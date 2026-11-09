"""Exercise compiled FormModel submissions against the Lean HTTP server."""
import json
import os
import pty
import threading
from pathlib import Path
import socket
import sys
import subprocess
import time
import tempfile
from contextlib import contextmanager
from urllib.error import HTTPError, URLError
from urllib.request import Request, urlopen

ROOT = Path(__file__).resolve().parents[1]
BINARY = ROOT / '.lake/build/bin/forms-web'


@contextmanager
def serve(example):
    """Runs forms-web for `example`; yields a request function, its descriptor, and the traffic log."""
    with socket.socket() as sock:
        sock.bind(('127.0.0.1', 0))
        port = sock.getsockname()[1]
    traffic_log = tempfile.TemporaryFile()
    process = subprocess.Popen([str(BINARY), example, '--port', str(port)], cwd=ROOT,
                               stdout=traffic_log, stderr=subprocess.PIPE)
    base = f'http://127.0.0.1:{port}'

    def request(path, value=None, raw=None, method=None):
        data = raw if raw is not None else json.dumps(value).encode() if value is not None else None
        req = Request(base + path, data=data, method=method,
                      headers={'Content-Type': 'application/json'} if data is not None else {})
        try:
            response = urlopen(req, timeout=5)
        except HTTPError as error:
            response = error
        with response:
            return response.status, response.headers, response.read().decode()

    try:
        for _ in range(100):
            if process.poll() is not None:
                raise AssertionError(process.stderr.read().decode())
            try:
                status, _, body = request('/api/compiled-form')
                break
            except URLError:
                time.sleep(.05)
        else:
            raise AssertionError('HTTP server did not start')
        assert status == 200
        descriptor = json.loads(body)
        assert set(descriptor) == {'form', 'fingerprint', 'value'}
        assert descriptor['form'] == example
        assert descriptor['fingerprint'].startswith('compiled-2-')
        yield request, descriptor, traffic_log
    finally:
        process.terminate()
        try:
            process.communicate(timeout=5)
        except subprocess.TimeoutExpired:
            process.kill()
            process.communicate()
        traffic_log.close()


def validation_error(request, submission, message, fields):
    status, _, body = request('/api/submit', submission)
    assert status == 422, (status, body)
    error = json.loads(body)['error']
    assert error['kind'] == 'validation' and error['message'] == message, error
    assert error['errors'] == [{'message': message, 'targets': {
        'kind': 'locations', 'locations': [[{'kind': 'field', 'name': f} for f in fields]]}}], error


def order_session():
    with serve('order') as (request, descriptor, _):
        initial = {'form': 'order', 'fingerprint': descriptor['fingerprint'], 'value': descriptor['value']}
        assert request('/api/submit', initial)[0] == 204
        value = descriptor['value']
        for changes, message, fields in [
            ({'customer': {**value['customer'], 'email': 'grace'}}, 'Enter a valid email address.',
             ['customer', 'email']),
            ({'quantity': 11, 'shipping': {**value['shipping'], 'express': True}},
             'Express shipping is limited to 10 items.', ['quantity']),
            ({'gift': True}, 'Enter a gift message.', ['giftMessage']),
        ]:
            validation_error(request, {**initial, 'value': {**value, **changes}}, message, fields)
        status, _, body = request('/api/submit', {**initial, 'form': 'person'})
        assert status == 422 and json.loads(body)['error']['kind'] == 'request'


def session(example):
    with serve(example) as (request, descriptor, traffic_log):
        for path, mime in [('/', 'text/html'), ('/app.js', 'text/javascript'),
                           ('/style.css', 'text/css')]:
            status, headers, body = request(path)
            assert status == 200 and headers['Content-Type'].startswith(mime), (path, status, headers)
            assert body and headers['Cache-Control'] == 'no-store'
        for retired in ['/wasm.js', '/validation.js', '/display.js', '/api/form', '/interpreter.js', '/wasm/json.mjs', '/wasm/json.wasm']:
            assert request(retired)[0] == 404
        for method in ['GET', 'POST', 'DELETE']:
            status, headers, _ = request('/missing', method=method)
            assert status == 404 and 'Allow' not in headers
        for path in ['/', '/app.js', '/style.css', '/api/compiled-form']:
            for method in ['POST', 'DELETE']:
                status, headers, _ = request(path, method=method)
                assert status == 405 and headers['Allow'] == 'GET', (path, method, status, headers)
        for method in ['GET', 'DELETE']:
            status, headers, _ = request('/api/submit', method=method)
            assert status == 405 and headers['Allow'] == 'POST', (method, status, headers)
        assert request('/api/submit', raw=b'{')[0] == 400
        assert request('/api/submit', raw=b'x' * (1024 * 1024 + 1))[0] == 413
        initial = {'form': example, 'fingerprint': descriptor['fingerprint'], 'value': descriptor['value']}
        status, headers, body = request('/api/submit', initial)
        assert status == 204 and body == ''
        assert 'Content-Type' not in headers
        script = """
import { openCompiledForm } from '@blp/lean-forms-react/runtime';
import { readFileSync } from 'node:fs';
import { pathToFileURL } from 'node:url';
const model = await openCompiledForm(JSON.parse(readFileSync(0, 'utf8')), pathToFileURL('web/dist/wasm/forms.mjs'));
const apply = (label, argument) => model.send({ apply: {
  key: model.snapshot().controls.find(c => c.label === label).key, argument } });
apply('Name', 'Grace');
apply('Request delivery', true);
apply('Street', 'Campus');
apply('Age', '25');
model.send({ event: { message: 'submit' } });
process.stdout.write(model.snapshot().effects[0].body);
model.dispose();
"""
        submission = json.loads(subprocess.check_output(
            ['node', '--input-type=module', '-e', script],
            input=json.dumps(descriptor).encode(), cwd=ROOT))
        assert submission['value']['name'] == 'Grace'
        assert submission['value']['address'] == {'street': 'Campus'}
        assert request('/api/submit', submission)[0] == 204
        assert submission['fingerprint'] == descriptor['fingerprint']
        for stale in [{'form': example, 'value': descriptor['value']}, {**initial, 'fingerprint': 'compiled-2-0'}]:
            status, _, body = request('/api/submit', stale)
            assert status == 422 and json.loads(body)['error'] == {
                'kind': 'request', 'message': 'This form is out of date. Reload the page.'}
        for invalid in [{}, {**initial, 'form': 'missing'}, {**initial, 'value': False},
                        {**initial, 'value': {**descriptor['value'], 'age': '20'}}]:
            status, _, body = request('/api/submit', invalid)
            assert status == 422 and json.loads(body)['error']['kind'] == 'request'
        for changes, message, fields in [
            ({'age': 150}, 'Age must be at most 120.', ['age']),
            ({'address': {'street': ''}}, 'Enter your delivery street.', ['address', 'street']),
            ({'age': 17, 'address': {'street': 'Campus'}}, 'Campus delivery requires an adult.', ['age']),
        ]:
            validation_error(request, {**initial, 'value': {**initial['value'], **changes}}, message, fields)
        assert request('/api/submit', initial)[0] == 204
        traffic_log.seek(0)
        traffic = traffic_log.read().decode()
        assert '\x1b[' not in traffic
        assert 'CLIENT → SERVER GET /api/compiled-form' in traffic
        assert 'SERVER → CLIENT 200 GET /api/compiled-form' in traffic
        assert 'CLIENT → SERVER POST /api/submit' in traffic
        assert 'SERVER → CLIENT 204 POST /api/submit\n' in traffic
        assert 'SERVER → CLIENT 422 POST /api/submit' in traffic
        assert '"Grace"' in traffic


def terminal_colors(no_color=False, term='xterm-256color'):
    with socket.socket() as sock:
        sock.bind(('127.0.0.1', 0))
        port = sock.getsockname()[1]
    master, slave = pty.openpty()
    environment = dict(os.environ, TERM=term)
    environment.pop('NO_COLOR', None)
    if no_color:
        environment['NO_COLOR'] = ''
    process = subprocess.Popen([str(BINARY), '--port', str(port)], cwd=ROOT,
                               stdout=slave, stderr=subprocess.PIPE, env=environment)
    os.close(slave)
    output = bytearray()

    def drain():
        try:
            while chunk := os.read(master, 65536):
                output.extend(chunk)
        except OSError:
            pass

    reader = threading.Thread(target=drain)
    reader.start()
    try:
        for _ in range(100):
            if process.poll() is not None:
                raise AssertionError(process.stderr.read().decode())
            try:
                with urlopen(f'http://127.0.0.1:{port}/api/compiled-form', timeout=5) as response:
                    assert response.status == 200
                    response.read()
                break
            except URLError:
                time.sleep(.05)
        else:
            raise AssertionError('HTTP server did not start')
    finally:
        process.terminate()
        try:
            process.communicate(timeout=5)
        except subprocess.TimeoutExpired:
            process.kill()
            process.communicate()
        reader.join(timeout=5)
        os.close(master)
    if no_color or term == 'dumb':
        assert b'\x1b[' not in output, output
    else:
        assert b'\x1b[36m' in output and b'\x1b[32m' in output, output
        assert b'\x1b[0m' in output, output
        assert b'\x1b[34m"value"\x1b[0m' in output, output
        assert b'\x1b[32m"Ada"\x1b[0m' in output, output


def browser_flag(exit_code):
    with socket.socket() as sock:
        sock.bind(('127.0.0.1', 0))
        port = sock.getsockname()[1]
    base = f'http://127.0.0.1:{port}'
    with tempfile.TemporaryDirectory() as directory:
        marker = Path(directory) / 'opened'
        opener = Path(directory) / ('open' if sys.platform == 'darwin' else 'xdg-open')
        opener.write_text(
            f'#!{sys.executable}\n'
            'import sys\n'
            'from pathlib import Path\n'
            'from urllib.request import urlopen\n'
            'with urlopen(sys.argv[1] + "/api/compiled-form", timeout=5) as response:\n'
            '    assert response.status == 200\n'
            f'Path({str(marker)!r}).write_text(sys.argv[1])\n'
            f'sys.exit({exit_code})\n')
        opener.chmod(0o755)
        environment = dict(os.environ, PATH=directory + os.pathsep + os.environ['PATH'])
        with tempfile.TemporaryFile() as traffic:
            process = subprocess.Popen(
                [str(BINARY), '--open', 'person', '--port', str(port)],
                cwd=ROOT, env=environment, stdout=traffic, stderr=subprocess.PIPE)
            try:
                for _ in range(100):
                    if marker.exists():
                        break
                    assert process.poll() is None, process.stderr.read().decode()
                    time.sleep(.05)
                else:
                    raise AssertionError('Browser opener was not called')
                assert marker.read_text() == base
                with urlopen(base + '/api/compiled-form', timeout=5) as response:
                    assert response.status == 200
                if exit_code:
                    assert b'Could not open browser' in process.stderr.readline()
                    assert process.poll() is None
            finally:
                process.terminate()
                process.communicate(timeout=5)


for arguments in [['--port'], ['--port', '0'], ['--port', '65536'], ['--port', 'abc'],
                  ['--unknown']]:
    assert subprocess.run([str(BINARY), *arguments], capture_output=True).returncode != 0
assert b'--open' in subprocess.check_output([str(BINARY), '--help'])
browser_flag(0)
browser_flag(1)


session('person')
order_session()
terminal_colors()
terminal_colors(no_color=True)
terminal_colors(term='dumb')
print('PASS: HTTP traffic, person and order validation, request errors, terminal colors, NO_COLOR, and --open')
