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


def session(keys, expected, interrupt=False):
    master, slave = pty.openpty()
    fcntl.ioctl(slave, termios.TIOCSWINSZ, struct.pack('HHHH', 24, 100, 0, 0))
    before = termios.tcgetattr(slave)
    process = subprocess.Popen([str(BINARY)], stdin=slave, stdout=slave, stderr=slave)
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
        read_until(lambda: b'Person.Name' in output)
        os.write(master, keys)
        if interrupt:
            read_until(lambda: 'Ω▏'.encode() in output)
            process.send_signal(signal.SIGTERM)
        read_until(lambda: b'Final values' in output)
        process.wait(timeout=10)
        while select.select([master], [], [], 0)[0]:
            output.extend(os.read(master, 65536))
        assert process.returncode == 0, bytes(output)
        assert termios.tcgetattr(slave) == before, 'Terminal mode was not restored'
        assert b'\x1b[?1049l' in output, 'Alternate screen was not restored'
        tail = output.split(b'Final values', 1)[1]
        result = json.loads(tail[tail.index(b'['):].decode())
        assert result == expected, result
        return bytes(output)
    finally:
        if process.poll() is None:
            process.kill()
            process.wait()
        os.close(master)
        os.close(slave)


initial = ['Ada', [False, ['Lambda Lane', 12]]]
output = session(b'j jj\r\x15-1\r\x1542\rkk  q', ['Ada', [True, ['Lambda Lane', 42]]])
assert b'non-negative whole number' in output
session('i\x15Ω'.encode(), initial, interrupt=True)
session(b'q', initial)
result = subprocess.run([str(BINARY)], capture_output=True, text=True)
assert result.returncode != 0 and '--plain' in result.stderr + result.stdout
result = subprocess.run([str(BINARY), '--plain'], input='q\n', capture_output=True, text=True)
assert result.returncode == 0 and 'Ada' in result.stdout
print('PASS: FFI editing, validation, visibility, typed result, interruption, terminal restoration, and plain mode')
