"""Exercise browser-generated histories against the Lean HTTP server."""
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
from urllib.error import HTTPError, URLError
from urllib.request import Request, urlopen

ROOT = Path(__file__).resolve().parents[1]
BINARY = ROOT / '.lake/build/bin/forms-web'


def session(example):
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
                status, _, body = request('/api/form')
                break
            except URLError:
                time.sleep(.05)
        else:
            raise AssertionError('HTTP server did not start')
        assert status == 200
        spec = json.loads(body)
        assert spec['version'] == 8
        for path, mime in [('/', 'text/html'), ('/app.js', 'text/javascript'),
                           ('/interpreter.js', 'text/javascript'), ('/validation.js', 'text/javascript'), ('/style.css', 'text/css')]:
            status, headers, body = request(path)
            assert status == 200 and headers['Content-Type'].startswith(mime), (path, status, headers)
            assert body and headers['Cache-Control'] == 'no-store'
        for method in ['GET', 'POST', 'DELETE']:
            status, headers, _ = request('/missing', method=method)
            assert status == 404 and 'Allow' not in headers
        for path in ['/', '/app.js', '/interpreter.js', '/validation.js', '/style.css', '/api/form']:
            for method in ['POST', 'DELETE']:
                status, headers, _ = request(path, method=method)
                assert status == 405 and headers['Allow'] == 'GET', (path, method, status, headers)
        for method in ['GET', 'DELETE']:
            status, headers, _ = request('/api/submit', method=method)
            assert status == 405 and headers['Allow'] == 'POST', (method, status, headers)
        assert request('/api/submit', raw=b'{')[0] == 400
        assert request('/api/submit', raw=b'x' * (1024 * 1024 + 1))[0] == 413
        initial = {'value': spec['value'], 'actions': []}
        status, headers, body = request('/api/submit', initial)
        assert status == 204 and body == ''
        assert 'Content-Type' not in headers
        script = '''
import { createModel } from './web/dist/interpreter.js';
import { readFileSync } from 'node:fs';
const model = createModel(JSON.parse(readFileSync(0, 'utf8')));
const edit = (widget, argument) => model.apply(model.controls().find(c => c.widget === widget).key, argument);
const apply = (label, argument) => model.apply(model.controls().find(c => c.label === label).key, argument);
const quantity = (index, argument) =>
  model.apply(model.controls().find(c => c.label === 'Quantity' && c.target[1] === index).key, argument);
switch (process.argv[1]) {
  case 'person':
    edit('textInput', 'Grace'); edit('checkbox', true); edit('select', 2); break;
  case 'booking': edit('dateInput', '2028-02-29'); break;
  case 'invoice':
    apply('Add item');
    quantity(1, '7');
    apply('Remove item');
    break;
  case 'invoice-invalid': apply('Add item'); quantity(1, '0'); break;
  case 'shapes-invalid': apply('Shape', 'rectangle'); apply('Width', '0'); break;
  case 'location': apply('Country', 'Japan'); apply('City', 2); break;
  case 'shapes':
    apply('Shape', 'rectangle'); apply('Width', '8');
    apply('Shape', 'dot'); apply('Shape', 'rectangle'); apply('Height', '7');
    break;
  case 'basket':
    apply('Search', 'pen'); apply('Sort', 1); apply('Product to add', 1);
    apply('Add selected product'); apply('Add selected product');
    break;
  case 'report': apply('Provider', 1); apply('Failures only', true); apply('Sort', 1); break;
  case 'thermostat': apply('Home temperature (C)', '23'); break;
  case 'counter':
  case 'counters': {
    const editor = model.controls().find(c => c.kind === 'editor');
    model.apply(editor.key, '123456789012345678901234567890');
    const button = model.controls().find(c => c.id === 'plusOne');
    model.apply(button.key); model.apply(button.key);
    break;
  }
  default: throw new Error('Missing example test');
}
model.view();
process.stdout.write(JSON.stringify(model.submission()));
'''

        def run_client(scenario):
            return json.loads(subprocess.check_output(['node', '--input-type=module', '-e', script, scenario],
                                                      input=json.dumps(spec).encode(), cwd=ROOT))
        submission = run_client(example)
        status, _, accepted = request('/api/submit', submission)
        assert status == 204 and accepted == '', (status, accepted)
        forged = {**submission, 'value': spec['value']}
        status, _, body = request('/api/submit', forged)
        assert status == 422 and json.loads(body)['error']['kind'] == 'replay'
        assert request('/api/submit', {'value': submission['value'], 'actions': []})[0] == 422
        unknown = {'value': spec['value'], 'actions': [{'target': [], 'action': 'unknown'}]}
        assert request('/api/submit', unknown)[0] == 422
        assert request('/api/submit', raw=json.dumps(spec['value']).encode())[0] == 422
        assert request('/api/submit', initial)[0] == 204
        if example == 'person':
            invalid = json.loads(json.dumps(initial))
            invalid['value']['age'] = '17'
            invalid['actions'] = [{'target': ['age'], 'action': 'replace', 'argument': '17'}]
            status, _, body = request('/api/submit', invalid)
            assert status == 422
            error = json.loads(body)['error']
            assert error['kind'] == 'validation'
            assert error['errors'] == [{'message': 'Attendees must be between 18 and 120 years old.', 'targets': {'kind': 'locations', 'locations': [[{'kind': 'field', 'name': 'age'}]]}}]
            assert error['message'] == 'Attendees must be between 18 and 120 years old.'
        for scenario, expected in [
                ('invoice-invalid', [{'message': 'Quantity and unit price must be at least 1.',
                                      'targets': {'kind': 'locations', 'locations': [[{'kind': 'item', 'index': '1'}, {'kind': 'field', 'name': 'quantity'}]]}}]),
                ('shapes-invalid', [{'message': 'Size must be at least 1.',
                                     'targets': {'kind': 'locations', 'locations': [[{'kind': 'constructor', 'tag': 'rectangle'}, {'kind': 'field', 'name': 'width'}]]}}])]:
            if example != scenario.removesuffix('-invalid'):
                continue
            invalid = run_client(scenario)
            status, _, body = request('/api/submit', invalid)
            assert status == 422, (status, body)
            error = json.loads(body)['error']
            assert error['kind'] == 'validation' and error['errors'] == expected, error
        if example == 'booking':
            invalid = json.loads(json.dumps(initial))
            invalid['value']['endDate'] = '2027-01-01'
            invalid['actions'] = [{'target': ['endDate'], 'action': 'replace', 'argument': '2027-01-01'}]
            status, _, body = request('/api/submit', invalid)
            assert status == 422
            assert json.loads(body)['error']['message'].splitlines() == [
                'Date must be between 2028-01-01 and 2028-12-31.',
                'End date must be on or after start date.']
            assert json.loads(body)['error']['errors'][1]['targets'] == {
                'kind': 'locations', 'locations': [[{'kind': 'field', 'name': 'startDate'}], [{'kind': 'field', 'name': 'endDate'}]]}
        traffic_log.seek(0)
        traffic = traffic_log.read().decode()
        assert '\x1b[' not in traffic
        assert 'CLIENT → SERVER GET /api/form' in traffic
        assert 'SERVER → CLIENT 200 GET /api/form' in traffic
        assert 'CLIENT → SERVER POST /api/submit' in traffic
        assert 'SERVER → CLIENT 204 POST /api/submit\n' in traffic
        assert 'SERVER → CLIENT 422 POST /api/submit' in traffic
        assert '"actions"' in traffic
        if example in ['counter', 'counters']:
            assert '123456789012345678901234567890' in traffic
    finally:
        process.terminate()
        try:
            process.communicate(timeout=5)
        except subprocess.TimeoutExpired:
            process.kill()
            process.communicate()
        traffic_log.close()


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
                with urlopen(f'http://127.0.0.1:{port}/api/form', timeout=5) as response:
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
        assert b'\x1b[32m"0"\x1b[0m' in output, output


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
            'with urlopen(sys.argv[1] + "/api/form", timeout=5) as response:\n'
            '    assert response.status == 200\n'
            f'Path({str(marker)!r}).write_text(sys.argv[1])\n'
            f'sys.exit({exit_code})\n')
        opener.chmod(0o755)
        environment = dict(os.environ, PATH=directory + os.pathsep + os.environ['PATH'])
        with tempfile.TemporaryFile() as traffic:
            process = subprocess.Popen(
                [str(BINARY), '--open', 'counters', '--port', str(port)],
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
                with urlopen(base + '/api/form', timeout=5) as response:
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


for example in ['counter', 'counters', 'person', 'booking', 'invoice', 'location', 'shapes', 'basket', 'report', 'thermostat']:
    session(example)
terminal_colors()
terminal_colors(no_color=True)
terminal_colors(term='dumb')
print('PASS: HTTP traffic, replay, request errors, terminal colors, NO_COLOR, and --open')
