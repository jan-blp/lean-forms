"""Check parsing and both shell adapters against the executable's completion endpoint."""
import os
from pathlib import Path
import shlex
import subprocess

ROOT = Path(__file__).resolve().parents[1]
BINARY = ROOT / '.lake/build/bin/forms'
ENV = dict(os.environ, PATH=str(BINARY.parent) + os.pathsep + os.environ['PATH'])


def invoke(args):
    return subprocess.run([str(BINARY), *args], capture_output=True, text=True)


def candidates(words):
    result = invoke(['--complete', *words])
    assert result.returncode == 0, result.stderr
    return result.stdout.splitlines()


def bash_candidates(words, lake=False, executable="forms"):
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


def fish_candidates(words, lake=False, executable="forms"):
    prefix = ['lake', '-q', 'exe', executable] if lake else [executable]
    line = ' '.join(map(shlex.quote, prefix + words[:-1])) + ' ' + words[-1]
    script = 'source completions/forms.fish\ncomplete -C ' + shlex.quote(line)
    result = subprocess.run(['fish', '--no-config', '-c', script], cwd=ROOT,
                            env=ENV, capture_output=True, text=True)
    assert result.returncode == 0, result.stderr
    return [line.split('\t', 1)[0] for line in result.stdout.splitlines()]


all_candidates = candidates([''])
examples = [name for name in all_candidates if not name.startswith('-')]
options = [name for name in all_candidates if name.startswith('-') and name != '--help']
assert examples and examples[0] == 'person'
assert len(set(all_candidates)) == len(all_candidates)
help_result = invoke(['--help'])
assert help_result.returncode == 0
for example in examples:
    assert example in help_result.stdout
    assert invoke([example, '--help']).returncode == 0
    assert invoke([example, example, '--help']).returncode != 0
assert invoke(['not-an-example', '--help']).returncode != 0
assert invoke(['--unknown', '--help']).returncode != 0
assert candidates(['not-an-example', '']) == []
assert candidates(['--help', '']) == []
contexts = [[''], ['p'], ['--'], [examples[0], ''], [examples[0], '--']]
for option in options:
    values = candidates([option, ''])
    assert values
    assert invoke([option]).returncode != 0
    assert invoke([option, 'not-a-value']).returncode != 0
    contexts += [[option, ''], [option, values[0][:1]], [option, values[0], '']]
    for value in values:
        for example in examples:
            assert invoke([option, value, example, '--help']).returncode == 0
            assert invoke([example, option, value, '--help']).returncode == 0
            assert value in help_result.stdout
    assert candidates([option, values[0], '']) == all_candidates
for words in contexts:
    expected = sorted(candidates(words))
    for adapter in [bash_candidates, fish_candidates]:
        assert sorted(adapter(words)) == expected, (adapter.__name__, words, expected, adapter(words))
for adapter in [bash_candidates, fish_candidates]:
    for words in [[''], ['p'], [examples[0], '--']]:
        assert sorted(adapter(words, lake=True)) == sorted(candidates(words)), (adapter.__name__, words)
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
print('PASS: CLI parsing, registry-derived completion, Bash and Fish (direct and lake exe forms)')

BINARY = ROOT / '.lake/build/bin/forms-web'
assert candidates(['b']) == ['booking']
assert candidates(['--port', '']) == []
assert candidates(['--port', 'invalid', '']) == []
assert candidates(['booking', '']) == ['--open', '--port', '--help']
assert '--open' not in candidates(['--open', ''])
assert candidates(['--help', '']) == []
for words in [[''], ['b'], ['--'], ['booking', ''], ['--port', ''],
              ['--port', '8081', ''], ['--open', 'b'], ['booking', '--open', '']]:
    expected = sorted(candidates(words))
    for adapter in [bash_candidates, fish_candidates]:
        for lake in [False, True]:
            actual = sorted(adapter(words, lake=lake, executable='forms-web'))
            assert actual == expected, (adapter.__name__, words, lake, actual, expected)
print('PASS: web CLI completion, Bash and Fish (direct and lake exe forms-web)')
