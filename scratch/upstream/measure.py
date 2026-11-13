"""measure.py <base.jsonl> <cand.jsonl> <tlc.jsonl>...: the startup report, candidate against a main baseline."""
import json, sys
from collections import Counter
from classify import load
base, cand = load(sys.argv[1]), load(sys.argv[2])
tlc = {}
for path in sys.argv[3:]:
    for line in open(path):
        r = json.loads(line); tlc[r['id']] = r
adj = '/home/user/work/adj'
ids = lambda f: [l for l in open(f'{adj}/{f}').read().split('\n') if l]
key = lambda r: (r['class'], r['exit'], r['transcript'])
print('classes base:', dict(Counter(r['class'] for r in base.values())))
print('classes cand:', dict(Counter(r['class'] for r in cand.values())))
changed = [i for i in sorted(cand) if key(base[i]) != key(cand[i]) or base[i]['reason'] != cand[i]['reason']]
print('changed runs:', len(changed))
print('transitions:', dict(Counter(f"{base[i]['class']}->{cand[i]['class']}" for i in changed)))
lost = [i for i in changed if base[i]['class'] == 'match' and cand[i]['class'] != 'match']
print('matches lost:', len(lost))
for i in lost: print('  LOST', i, cand[i]['class'], cand[i]['reason'])
new_wrong = [i for i in changed if cand[i]['class'] == 'wrong' and key(base[i]) != key(cand[i])]
need = [i for i in new_wrong if i not in tlc]
open(f'{adj}/measure-need-tlc.txt', 'w').write(''.join(i + '\n' for i in need))
print('wrong outputs that changed:', len(new_wrong), 'without a jar run:', len(need))
for i in new_wrong:
    if i in tlc:
        same = (tlc[i]['exit'], tlc[i]['transcript']) == (cand[i]['exit'], cand[i]['transcript'])
        print('  ', 'equals-jar' if same else 'WRONG', i, 'base', base[i]['class'])
nc = [i for i in cand if cand[i]['class'] == 'noncompletion']
print('noncompletions:', len(nc), [(i, cand[i]['verdict'], base[i]['class']) for i in nc])
for name, f in (('6,795', 'overreach.txt'), ('575', 'swc.txt'), ('8,671', 'startup-effects-8671.txt')):
    s = ids(f)
    print(f'subset {name}: cand', dict(Counter(cand[i]['class'] for i in s)), 'base', dict(Counter(base[i]['class'] for i in s)))
print('reasons of decline->match:', len([i for i in changed if base[i]['class'] == 'decline' and cand[i]['class'] == 'match']))
for i in changed:
    if 'cap_short_circuits_right' in i: print('  cap_short_circuits_right', i, base[i]['class'], '->', cand[i]['class'])
