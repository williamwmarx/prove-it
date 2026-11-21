"""vsmain.py <cand.jsonl> [jar.jsonl...]: classes, and each run whose output changed from main b7f832b9, against the jar."""
import sys, json, os
sys.path.insert(0, os.path.dirname(__file__))
from classify import load
from collections import Counter
W = '/home/user/work/'
b = load(W + 'main-b7f832b9.jsonl'); c = load(sys.argv[1])
jar = {}
for f in [W + 'jar-1.jsonl'] + sys.argv[2:]:
    for l in open(f): r = json.loads(l); jar[r['id']] = r
print(Counter(r['class'] for r in c.values()))
key = lambda r: (r['class'], r['exit'], r['transcript'], r['reason'])
ch = [i for i in c if key(b[i]) != key(c[i])]
print('changed', len(ch), Counter(f"{b[i]['class']}->{c[i]['class']}" for i in ch))
for i in ch:
    j = jar.get(i); eq = j and (j['exit'], j['transcript']) == (c[i]['exit'], c[i]['transcript'])
    print(' ', i, b[i]['class'], '->', c[i]['class'], 'equals-jar' if eq else ('no-jar' if not j else 'DIFF-jar'), c[i]['reason'][:100])
open(W + 'need-jar.txt', 'w').write(''.join(i + '\n' for i in ch if i not in jar))
