"""vs_jar.py <binary.jsonl> <jar.jsonl>: class of each binary run against the jar's."""
import json, sys
from collections import Counter
sys.path.insert(0, __import__('os').path.dirname(__file__))
from classify import MARKER
b = {json.loads(l)['id']: json.loads(l) for l in open(sys.argv[1])}
j = {json.loads(l)['id']: json.loads(l) for l in open(sys.argv[2])}
c = Counter(); out = []
for i in sorted(b):
    r, t = b[i], j.get(i)
    if MARKER in r['stderr'] + r['transcript']:
        k = 'decline'
    elif t is None: k = 'no-jar'
    elif t.get('exceeded'): k = 'jar-noncompletion'
    elif r.get('exceeded') or r['exit'] == -1: k = 'noncompletion'
    elif (r['exit'], r['transcript']) == (t['exit'], t['transcript']): k = 'match'
    else: k = 'wrong'
    c[k] += 1; out.append((i, k))
print(dict(c))
for i, k in out:
    if k in ('wrong', 'noncompletion', 'jar-noncompletion'): print(k, i)
