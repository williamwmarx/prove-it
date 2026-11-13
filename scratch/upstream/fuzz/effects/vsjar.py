"""vsjar.py <dir> <list> <tag>...: each tag's class vs tlc.out (match, decline, wrong) per fixture, and transitions between the first two tags."""
import sys, collections
d, lst, tags = sys.argv[1], sys.argv[2], sys.argv[3:]
def cls(z, t):
    o = open(f'{d}/{z}/out-{t}').read()
    if o.startswith('DECLINE'): return 'decline'
    return 'match' if o == open(f'{d}/{z}/tlc.out').read() else 'wrong'
rows = [l.strip() for l in open(lst) if l.strip()]
c = collections.Counter(); bad = []
for z in rows:
    k = tuple(cls(z, t) for t in tags); c[k] += 1
    if k[-1] == 'wrong' and k[0] != 'wrong' or (k[0] == 'match' and k[-1] != 'match'): bad.append((z, k))
for k, n in sorted(c.items()): print(n, ' -> '.join(k))
print('regressions (last tag wrong where first not, or first match and last not):', len(bad))
for z, k in bad: print(' ', z, k)
