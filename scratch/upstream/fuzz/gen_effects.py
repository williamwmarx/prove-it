"""gen_effects.py <out> <seed> <count|all>: a part that fails or has an effect, inside a set TLC may keep lazy, as either operand of a set operator against an empty, singleton or lazy other operand, under each consumer."""
import itertools, os, random, sys
out, seed, count = sys.argv[1], int(sys.argv[2]), sys.argv[3]
random.seed(seed)
PARTS = {'div': '1 \\div 0', 'choose': 'CHOOSE c \\in {} : TRUE', 'assert': 'Assert(FALSE, "a")', 'apply': '<<1>>[2]', 'print': 'PrintT(5)', 'ok': '1'}
SHAPES = {
    'rcd': lambda p: f'[a : Int, b : {{{p}}}]', 'rcdl': lambda p: f'[a : {{{p}}}, b : Int]',
    'prod': lambda p: f'(Int \\X {{{p}}})', 'prodl': lambda p: f'({{{p}}} \\X Int)',
    'fdom': lambda p: f'[{{{p}}} -> Int]', 'fran': lambda p: f'[Int -> {{{p}}}]',
    'fin': lambda p: f'[a : {{1}}, b : {{{p}}}]', 'enum': lambda p: f'{{{p}}}',
    'sub': lambda p: f'SUBSET {{{p}}}', 'seq': lambda p: f'Seq({{{p}}})',
}
OTHERS = {'empty': '{}', 'one': '{1}', 'tup': '{<<1, 2>>}', 'rec': '{[a |-> 1, b |-> 2]}', 'nat': 'Nat', 'lazyempty': '[a : {}, b : Int]', 'str': '{"s"}'}
OPS = {
    'cap': lambda l, r: f'Cardinality({l} \\cap {r})', 'diff': lambda l, r: f'Cardinality({l} \\ {r})',
    'cup': lambda l, r: f'Cardinality({l} \\cup {r})', 'subeq': lambda l, r: f'({l} \\subseteq {r})',
    'eq': lambda l, r: f'({l} = {r})', 'capin': lambda l, r: f'(1 \\in ({l} \\cap {r}))',
    'diffin': lambda l, r: f'(<<1, 2>> \\in ({l} \\ {r}))', 'cupin': lambda l, r: f'("s" \\in ({l} \\cup {r}))',
    'exists': lambda l, r: f'(\\E t \\in ({l} \\cap {r}) : TRUE)', 'fcn': lambda l, r: f'([t \\in ({l} \\ {r}) |-> 1] = <<>>)',
    'finite': lambda l, r: f'IsFiniteSet({l} \\ {r})', 'union': lambda l, r: f'Cardinality(UNION {{{l}, {r}}})',
    'map': lambda l, r: f'Cardinality({{1 : t \\in ({l} \\cap {r})}})', 'choose': lambda l, r: f'((CHOOSE t \\in ({l} \\ {r}) : TRUE) = 1)',
    'cupsub': lambda l, r: f'(({l} \\cup {r}) \\subseteq {{}})', 'capeq': lambda l, r: f'(({l} \\cap {r}) = {{}})',
}
SINGLE = {  # one operand: the lazy set, the other the element
    'in': lambda s, o: f'({o} \\in {s})' if o not in ('Nat',) else f'(1 \\in {s})',
    'notin': lambda s, o: f'([a |-> 1, b |-> 2] \\notin {s})',
    'card': lambda s, o: f'Cardinality({s})', 'finite1': lambda s, o: f'IsFiniteSet({s})',
    'domain': lambda s, o: f'DOMAIN [k |-> {s}]',
}
CONSUMERS = {'init': 'Init == x = {e}\n', 'assume': 'ASSUME PrintT({e}) \\/ TRUE\nInit == x = 0\n', 'next': "Init == x = 0\nNext2 == x' = {e}\n"}
cells = []
for (pk, p), (sk, s), (ok, o), (opk, op), pos in itertools.product(PARTS.items(), SHAPES.items(), OTHERS.items(), OPS.items(), ('l', 'r')):
    lazy = s(p)
    e = op(lazy, o) if pos == 'l' else op(o, lazy)
    cells.append((f'{pk}-{sk}-{ok}-{opk}-{pos}', e))
for (pk, p), (sk, s), (opk, op) in itertools.product(PARTS.items(), SHAPES.items(), SINGLE.items()):
    cells.append((f'{pk}-{sk}-x-{opk}-s', op(s(p), '<<1, 2>>')))
if count != 'all':
    cells = random.sample(cells, int(count))
n = 0
for name, e in cells:
    ck = random.choice(list(CONSUMERS))
    d = f'{out}/{name}-{ck}'
    os.makedirs(d, exist_ok=True)
    body = CONSUMERS[ck].format(e=e)
    nxt = "Next == x' = x\n" if ck != 'next' else "Next == x' = x\n"
    if ck == 'next':
        body = f"Init == x = 0\nNext == x' = {e} /\\ x = 0 \\/ x' = x /\\ x # 0\n"
        nxt = ''
    open(f'{d}/M.tla', 'w').write(f"---- MODULE M ----\nEXTENDS Integers, FiniteSets, Sequences, TLC\nVARIABLE x\n{body}{nxt}====\n")
    open(f'{d}/M.cfg', 'w').write('INIT Init\nNEXT Next\n')
    n += 1
print(n, 'of', len(cells) if count == 'all' else 'sampled')
