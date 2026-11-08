"""Check parsing and both shell adapters against the executable's completion endpoint."""
import os
from pathlib import Path
import shlex
import subprocess

ROOT = Path(__file__).resolve().parents[1]
BINARY = ROOT / '.lake/build/bin/forms-web'
ENV = dict(os.environ, PATH=str(BINARY.parent) + os.pathsep + os.environ['PATH'])


def invoke(args):
    return subprocess.run([str(BINARY), *args], capture_output=True, text=True)


def candidates(words):
    result = invoke(['--complete', *words])
    assert result.returncode == 0, result.stderr
    return result.stdout.splitlines()


def bash_candidates(words, lake=False, executable="forms-web"):
    prefix = ['lake', '-q', 'exe', executable] if lake else [executable]
    tokens = prefix + words
    script = 'source completions/forms.bash\n'
    script += 'COMP_WORDS=(' + ' '.join(map(shlex.quote, tokens)) + ')\n'
    script += f'COMP_CWORD={len(tokens) - 1}\n_forms_complete\n'
    script += 'for value in "${COMPREPLY[@]}"; do printf "%s\\n" "$value"; done\n'
    result = subprocess.run(['bash', '--noprofile', '--norc', '-c', script], cwd=ROOT,
                            env=ENV, capture_output=True, text=True)
    assert result.returncode == 0, result.stderr
    return result.stdout.splitlines()


def fish_candidates(words, lake=False, executable="forms-web"):
    prefix = ['lake', '-q', 'exe', executable] if lake else [executable]
    line = ' '.join(map(shlex.quote, prefix + words[:-1])) + ' ' + words[-1]
    script = 'source completions/forms.fish\ncomplete -C ' + shlex.quote(line)
    result = subprocess.run(['fish', '--no-config', '-c', script], cwd=ROOT,
                            env=ENV, capture_output=True, text=True)
    assert result.returncode == 0, result.stderr
    return [line.split('\t', 1)[0] for line in result.stdout.splitlines()]


all_candidates = candidates([''])
examples = [name for name in all_candidates if not name.startswith('-')]
# Sourcing twice must retain unrelated Lake completion and never recurse.
result = subprocess.run(['bash', '--noprofile', '--norc', '-c', '''
_previous_lake() { COMPREPLY=(preserved); }
complete -F _previous_lake lake
source completions/forms.bash
source completions/forms.bash
COMP_WORDS=(lake build '')
COMP_CWORD=2
_forms_complete
[[ ${COMPREPLY[0]} == preserved ]]
'''], cwd=ROOT, env=ENV)
assert result.returncode == 0
assert invoke(['not-an-example']).returncode != 0
for name in examples:
    assert name in invoke(['--help']).stdout
    assert candidates([name, '']) == ['--open', '--port', '--help']
    assert invoke([name, name]).returncode != 0
assert candidates(['t']) == ['typed-person']
assert candidates(['--port', '']) == []
assert candidates(['--port', 'invalid', '']) == []
assert candidates(['typed-person', '']) == ['--open', '--port', '--help']
assert '--open' not in candidates(['--open', ''])
assert candidates(['--help', '']) == []
for words in [[''], ['t'], ['--'], ['typed-person', ''], ['--port', ''],
              ['--port', '8081', ''], ['--open', 't'], ['typed-person', '--open', '']]:
    expected = sorted(candidates(words))
    for adapter in [bash_candidates, fish_candidates]:
        for lake in [False, True]:
            actual = sorted(adapter(words, lake=lake, executable='forms-web'))
            assert actual == expected, (adapter.__name__, words, lake, actual, expected)
print('PASS: web CLI completion, Bash and Fish (direct and lake exe forms-web)')
