"""gen_lazy.py <out> <seed> <count>: specs over sets TLC keeps lazy with a part it can't size."""
import os, random, sys
random.seed(int(sys.argv[2]))
out = sys.argv[1]
UNS = ['Int', 'Nat', 'STRING', 'Seq({1})', 'SUBSET Nat']
EMP = ['{}', '{x} \\ {x}', '(1..0)']
FIN = ['{1}', '{"a"}', '{<<1, 2>>}', '{[a |-> 1]}', '{<<>>}', '{{}}', 'BOOLEAN']
def lazy():
    u, e = random.choice(UNS), random.choice(EMP)
    return random.choice([f'({u} \\X {e})', f'({e} \\X {u})', f'({u} \\X {e} \\X {u})', f'[a : {u}, b : {e}]', f'[a : {e}, b : {u}]', f'[{u} -> {e}]', f'[{e} -> {u}]', f'[{u} -> [{u} -> {e}]]', f'({u} \\X [{e} -> {u}])'])
def setx(d=0):
    r = random.random()
    if d > 1 or r < 0.35: return lazy()
    if r < 0.55: return random.choice(FIN)
    op = random.choice(['\\cap', '\\', '\\cup'])
    a, b = setx(d + 1), setx(d + 1)
    return f'({a} {op} {b})'
def val():
    S, T = setx(), setx()
    e = random.choice(['"a"', '1', '<<1, 2>>', '<<>>', '[a |-> 1]', '{}', 'x'])
    return random.choice([
        f'Cardinality({S})', f'{S} = {T}', f'{S} # {T}', f'{e} \\in {S}', f'{e} \\notin {S}', f'{S} \\subseteq {T}',
        f'\\E t \\in {S} : TRUE', f'\\A t \\in {S} : FALSE', f'{{{S}}}', f'Cardinality({{{S}}})', f'<<{S}>>', f'[f |-> {S}]',
        f'DOMAIN [k |-> {S}]', f'IsFiniteSet({S})', f'{{t \\in {S} : TRUE}} = {{}}', f'{{1 : t \\in {S}}}', f'ToString({S})',
        f'LET L == {S} IN {e} \\in L', f'LET L == {S} IN L = {{}}', f'(CHOOSE t \\in {{{S}}} : TRUE) = {{}}', f'UNION {{{S}}} = {{}}',
        f'SUBSET {S} = {{{{}}}}', f'{S}', f'[t \\in {S} |-> 1] = <<>>', f'{e} \\in UNION {{{S}}}', f'{S} = {e}', f'{e} = {S}'])
for k in range(int(sys.argv[3])):
    d = f'{out}/z-{sys.argv[2]}-{k}'; os.makedirs(d, exist_ok=True)
    v = val()
    where = random.choice(['init', 'assume', 'inv', 'next'])
    init, nxt, inv, assume = 'x = 0', "x' = x", '', ''
    if where == 'init': init = f'x = 0 /\\ y = ({v})'
    elif where == 'assume': assume = f'ASSUME PrintT({v})'
    elif where == 'inv': inv = f'Inv == PrintT({v}) /= 7'
    else: nxt = f"x' = x /\\ y' = ({v})"
    yi = '' if where == 'init' else ' /\\ y = 0'
    yn = '' if where == 'next' else " /\\ y' = y"
    open(f'{d}/M.cfg', 'w').write('INIT Init\nNEXT Next\n' + ('INVARIANT Inv\n' if inv else ''))
    open(f'{d}/M.tla', 'w').write(f"---- MODULE M ----\nEXTENDS Integers, Sequences, FiniteSets, TLC\nVARIABLES x, y\n{assume}\n{inv}\nInit == {init}{yi}\nNext == {nxt}{yn}\n====\n")
