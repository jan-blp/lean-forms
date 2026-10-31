"""Exercise the built Lean → C → Rust interpreter using a real pseudo-terminal."""
import errno
import fcntl
import json
import os
from pathlib import Path
import pty
import select
import signal
import struct
import subprocess
import termios
import time

ROOT = Path(__file__).resolve().parents[1]
BINARY = ROOT / '.lake/build/bin/forms'


def wire_value(schema, value):
    kind = schema['kind']
    if kind == 'natural':
        return str(value)
    if kind == 'enum':
        return schema['options'].index(value)
    if kind == 'record':
        return {field['name']: wire_value(field['type'], value[field['name']])
                for field in schema['fields']}
    if kind == 'list':
        return [wire_value(schema['element'], item) for item in value]
    return value


def session(keys, expected, interrupt=False, cancel=False, thermostat=False, theme=None, invoice=False, shapes=False, booking=False, report=False, basket=False, counter=False, counters=False, actions=None):
    master, slave = pty.openpty()
    fcntl.ioctl(slave, termios.TIOCSWINSZ, struct.pack('HHHH', 24, 100, 0, 0))
    before = termios.tcgetattr(slave)
    env = os.environ.copy()
    if theme:
        env.update(TERM='xterm-256color', COLORTERM='truecolor')
        env.pop('NO_COLOR', None)
    process = subprocess.Popen([str(BINARY)] + (["counters"] if counters else ["counter"] if counter else ["basket"] if basket else ["report"] if report else ["booking"] if booking else ["shapes"] if shapes else ["invoice"] if invoice else ["thermostat"] if thermostat else ["person"]) + (["--theme", theme] if theme else []), stdin=slave, stdout=slave, stderr=slave, env=env)
    output = bytearray()

    def read_until(predicate):
        deadline = time.monotonic() + 10
        while not predicate():
            if time.monotonic() > deadline:
                raise AssertionError(f'Terminal timeout: {bytes(output)!r}')
            if select.select([master], [], [], 0.1)[0]:
                try:
                    output.extend(os.read(master, 65536))
                except OSError as error:
                    if error.errno != errno.EIO:
                        raise
                    break

    try:
        read_until(lambda: (b'Counters' if counters else b'Counter' if counter else b'Basket total: EUR 16' if basket else b'Results' if report else b'Start date' if booking else b'Shape' if shapes else b'Description' if invoice else b'Home temperature (C)' if thermostat else b'Name') in output)
        os.write(master, keys)
        if cancel:
            read_until(lambda: b'Other' in output)
            start = len(output)
            os.write(master, b'\x1b')
            read_until(lambda: b'q submit' in output[start:])
            os.write(master, b'q')
        if interrupt:
            read_until(lambda: 'Ω▏'.encode() in output)
            process.send_signal(signal.SIGTERM)
        read_until(lambda: (b'Cancelled.' if expected is None else b'Final values') in output)
        process.wait(timeout=10)
        while select.select([master], [], [], 0)[0]:
            output.extend(os.read(master, 65536))
        assert process.returncode == 0, bytes(output)
        assert termios.tcgetattr(slave) == before, 'Terminal mode was not restored'
        assert b'\x1b[?1049l' in output, 'Alternate screen was not restored'
        if expected is None:
            assert b'Final values' not in output
        else:
            tail = output.split(b'Final values', 1)[1]
            result = json.loads(tail.split(b'------------', 1)[1].strip())
            if counter:
                assert result == {"value": str(expected), "actions": [
                    {"target": [], **({"action": action} if isinstance(action, str) else action)}
                    for action in actions]}, result
            elif not counters and isinstance(result, dict) and 'actions' in result:
                name = 'basket' if basket else 'invoice' if invoice else 'thermostat' if thermostat else 'booking' if booking else 'report' if report else 'person'
                spec = json.loads((ROOT / 'native/tui/tests' / f'{name}.json').read_text())
                assert result['value'] == wire_value(spec['schema'], expected), result
                assert isinstance(result['actions'], list), result
                if actions is not None:
                    assert result['actions'] == actions, result
            else:
                assert result == expected, result
        if theme:
            backgrounds = {
                'frappe': '48;2;48;52;70', 'macchiato': '48;2;36;39;58',
                'mocha': '48;2;30;30;46', 'latte': '48;2;239;241;245',
                'ayu-light': '48;2;248;249;250', 'ayu-dark': '48;2;13;16;23',
                'nord': '48;2;46;52;64',
            }
            assert backgrounds[theme].encode() in output, f'Wrong palette for {theme}'
        return bytes(output)
    finally:
        if process.poll() is None:
            process.kill()
            process.wait()
        os.close(master)
        os.close(slave)


initial = {'name': 'Ada', 'age': 28, 'subscribed': False, 'address': {'street': 'Lambda Lane', 'kind': 'Home'}}
output = session(b'j\r\x15-1\r\x1542\rj j\r\x15Elm Street\rk  q', {'name': 'Ada', 'age': 42, 'subscribed': True, 'address': {'street': 'Elm Street', 'kind': 'Home'}})
assert b'non-negative whole number' in output
session('i\x15Ω'.encode(), None, interrupt=True)
output = session(b'q', initial, actions=[])
assert b'Send me postal mail' in output
assert b'Address' not in output
for theme in ['frappe', 'macchiato', 'mocha', 'latte', 'ayu-light', 'ayu-dark', 'nord']:
    session(b'q', initial, theme=theme)
    session(b'q', {'home': 22, 'away': 18}, thermostat=True, theme=theme)
output = session(b'j\r\x1517\rq\r\x15121\rq\r\x1518\rq', {'name': 'Ada', 'age': 18, 'subscribed': False, 'address': {'street': 'Lambda Lane', 'kind': 'Home'}})
assert b'Attendees must be between 18 and 120' in output
session(b'jj jj\rj\rkk q', {'name': 'Ada', 'age': 28, 'subscribed': False, 'address': {'street': 'Lambda Lane', 'kind': 'Work'}})
session(b'jj jj\rj', {**initial, 'subscribed': True}, cancel=True)
output = session(b'\r\x1516\rqj\r\x1516\rq', {'home': 16, 'away': 16}, thermostat=True, actions=[
    {'target': ['home'], 'action': 'replace', 'argument': '16'},
    {'target': ['away'], 'action': 'replace', 'argument': '16'},
])
assert b'Away temperature must not exceed home temperature' in output
session(b'\r\x1516\rx', None, thermostat=True)
session(b'x', None)
result = subprocess.run([str(BINARY)], capture_output=True, text=True)
assert result.returncode != 0 and 'interactive terminal' in result.stderr + result.stdout

for args in [["--theme"], ["--theme", "unknown"], ["--theme", "dark"], ["--theme", "light"]]:
    result = subprocess.run([str(BINARY), *args], capture_output=True, text=True)
    assert result.returncode != 0 and "theme" in result.stderr

# Add a second item, remove the first, and submit through Lean validation.
session(b"jjjjj\rk\rq", [{"description": "New item", "quantity": 1, "unitPrice": 100}], invoice=True)

# A scalar payload, a record payload, and an empty constructor in the shapes demo.
session(b"q", {"tag": "circle", "value": 3}, shapes=True)
output = session(b"j\r\x150\rqk\rj\rj\r\x156\rq", {"tag": "rectangle", "value": {"width": 6, "height": 2}}, shapes=True)
assert b'Size must be at least 1' in output
session(b"\rk\rq", {"tag": "dot", "value": {}}, shapes=True)
# Return to the circle to recover its edited radius.
session(b"j\r\x155\rk\rj\r\rk\rq", {"tag": "circle", "value": 5}, shapes=True)

# An invalid cached circle does not block submission of the empty constructor.
session(b"j\r\x150\rqk\rk\rq", {"tag": "dot", "value": {}}, shapes=True)

output = session(b"j\r\x153\rjjjjj\ri q", [{"description": "New item", "quantity": 3, "unitPrice": 100}], invoice=True)
assert b"300 [computed]" in output

# Invalid calendar input stays in the editor; ordering errors block submission.
output = session(b"\ri\x152023-02-29\r\x152028-02-29\rj\ri\x152028-02-28\rq\ri\x152028-03-01\rq",
                 {"startDate": "2028-02-29", "endDate": "2028-03-01"}, booking=True)
assert b"Enter a valid date" in output
assert b"End date must be on or after start date" in output

# Calendar navigation updates the same date input before saving.
output = session(b"\rl\r\rq", {"startDate": "2028-02-29", "endDate": "2028-03-01"}, booking=True)
assert b"February 2028" in output
assert b"PgUp/PgDn month" in output

output = session(b"\rj\rj j\rj\rq", {
    "filters": {"provider": "Bedrock", "failuresOnly": True},
    "sort": "Name descending",
    "results": [
        {"name": "Zulu", "provider": "Bedrock", "passed": False},
        {"name": "Alpha", "provider": "Vertex", "passed": True},
        {"name": "Beta", "provider": "Bedrock", "passed": True},
        {"name": "Delta", "provider": "Vertex", "passed": False},
    ],
}, report=True)
assert b"Results" in output
assert b"PgUp/PgDn scroll results" in output

# Search only changes the catalogue view, not the stored basket.
basket_initial = {
    "page": "Catalogue",
    "filters": {"search": "", "category": "All categories", "budget": "Any price", "sort": "Name"},
    "selected": "Notebook",
    "items": [{"product": "Notebook", "quantity": 2}, {"product": "Pen", "quantity": 3}],
}
output = session(b"j\rpen\rq", {
    **basket_initial, "filters": {**basket_initial["filters"], "search": "pen"},
}, basket=True)
assert b'Basket total: EUR 16' in output

# Pick Mug, activate Add, switch to Basket, and change notebook quantity to 4.
output = session(b"jjjjj\rjj\rj\rkkkkkk\rj\rjj\r\x154\rq", {
    **basket_initial, "page": "Basket", "selected": "Mug",
    "items": [{"product": "Notebook", "quantity": 4}, {"product": "Pen", "quantity": 3},
              {"product": "Mug", "quantity": 1}],
}, basket=True)
assert b'Basket total: EUR 16' in output
print('PASS: FFI editing, validation, catalogue search, basket actions, typed result, interruption, and terminal restoration')

# Root-state typed actions, saturation, and ordinary input editing.
session(b"\rj\rj\r\x157\rj\rq", 6, counter=True,
        actions=["plusOne", "plusFive", {"action": "replace", "argument": "7"}, "minusOne"])
session(b"jjj\r\rq", 0, counter=True, actions=["minusOne", "minusOne"])
session(b"j\r\rq", 10, counter=True, actions=["plusFive", "plusFive"])

session(b"q", 0, counter=True, actions=[])
session(b"\rx", None, counter=True)

# Widget targets distinguish repeated action names within the stack.
session(b"\rjjjjj\rj\r\x1542\rq", {
    "value": {"left": "1", "right": "42"},
    "actions": [
        {"target": ["left"], "action": "plusOne"},
        {"target": ["right"], "action": "plusFive"},
        {"target": ["right"], "action": "replace", "argument": "42"},
    ],
}, counters=True)
