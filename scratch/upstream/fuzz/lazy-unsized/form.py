"""form.py: group main->b2 transitions on the fuzz corpora by the consumer form of the generated expression."""
import re, sys, glob, collections
def form(expr):
    e = expr.strip()
    rules = [(r'^\(?UNION \{', 'UNION {S} = {}'), (r'^\(?DOMAIN \[k \|->', 'DOMAIN [k |-> S]'), (r'^\(?Cardinality\(\{', 'Cardinality({S})'),
             (r'^\(?\(CHOOSE t \\in \{', 'CHOOSE t \\in {S} = {}'), (r'^\(?ToString\(', 'ToString(S)'), (r'^\(?IsFiniteSet\(', 'IsFiniteSet(S)'),
             (r'^\(?\[t \\in .* \|-> 1\] = <<>>', '[t \\in S |-> 1] = <<>>'), (r'^\(?\{', '{S}'), (r'^\(?<<', '<<S>>'), (r'^\(?\[f \|->', '[f |-> S]'),
             (r'^\(?Cardinality\(', 'Cardinality(S)')]
    for pat, name in rules:
        if re.search(pat, e): return name
    return 'S itself'
rows = collections.defaultdict(collections.Counter); ex = collections.defaultdict(list)
for c in ['fz8', 'fz8b', 'fz8c']:
    for line in open(f'{c}.2way-' + (sys.argv[1] if len(sys.argv) > 1 else 'b2')):
        m = re.match(r'(\S+) base=(\S*) new=(\S*) \| (.*)', line)
        if not m: continue
        z, base, new, why = m.groups()
        if base == new: continue
        src = open(glob.glob(f'{c}/{z}/*.tla')[0]).read()
        hit = re.search(r"(?:y = |y' = |PrintT\()(.*?)(?:\)\s*/= 7|\n)", src.split('Init ==')[0] + src) 
        lines = [l for l in src.splitlines() if l.startswith(('Init', 'Next', 'Inv', 'ASSUME', 'Prop'))]
        expr = None
        for l in lines:
            mm = re.search(r"(?:y = |y' = |PrintT\()(.*)$", l)
            if mm and mm.group(1).strip() not in ('0', 'y'):
                expr = mm.group(1); where = l.split(' ')[0]; break
        k = f'{base}->{new}'
        f = form(expr or '') + (' [Inv/ASSUME print]' if where in ('Inv', 'ASSUME') else '')
        rows[f][k + ' ' + why[:60]] += 1
        ex[(f, k)].append(f'{c}/{z}')
for f, cnt in sorted(rows.items()):
    print(f)
    for k, n in cnt.most_common(): print(f'   {n:4} {k}')
if len(sys.argv) > 2:
    for (f, k), v in sorted(ex.items()): print(f, k, ' '.join(v))
