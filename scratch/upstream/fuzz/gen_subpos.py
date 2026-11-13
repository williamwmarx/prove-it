"""gen_subpos.py <out>: specs whose [][Next]_v subscript is each kind of expression, wrapped in LETs, INSTANCEs and operator arguments, with and without -nowarning."""
import os, sys
out = sys.argv[1]
INNER = "---- MODULE Inner ----\nVARIABLE v\nvars == <<v>>\n====\n"
HEAD = ("---- MODULE M ----\nEXTENDS Naturals\nVARIABLES x, y\n"
        "D1 == 1\nD2 == <<x, y>>\nK == x + 1\nOp(a) == <<a, y>>\nWrap(a) == a\nAp(F(_)) == F(0)\n"
        "f[i \\in {0}] == x\nJ == INSTANCE Inner WITH v <- x\n")
EXPRESSIONS = {
    'x': 'x', 'pair': '<<x, y>>', 'single': '<<x>>', 'num': '1', 'str': '"s"', 'plus': 'x + y',
    'set': '{x, y}', 'record': '[a |-> x, b |-> y]', 'mixed': '<<x, 1>>', 'if': 'IF TRUE THEN <<x, y>> ELSE x',
    'd2': 'D2', 'd1': 'D1', 'op': 'Op(x)', 'inst': 'J!vars', 'fun': 'f', 'funapp': 'f[0]', 'k': 'K',
    'nested': '<<<<x>>, y>>',
}
WRAPPERS = {
    'none': lambda e: e,
    'let': lambda e: f'LET L == {e} IN L',
    'lettuple': lambda e: f'LET L == {e} IN <<L, y>>',
    'letfun': lambda e: f'LET g[i \\in {{0}}] == i IN {e}',
    'letrecfun': lambda e: f'LET RECURSIVE h(_)\n                    h(n) == n IN {e}',
    'letop': lambda e: f'LET W(a) == a IN W({e})',
    'arg': lambda e: f'Wrap({e})',
    'lambda': lambda e: f'Ap(LAMBDA k : {e})',
    'letinst': lambda e: f'LET I == INSTANCE Inner WITH v <- {e} IN I!vars',
    'letinstparam': lambda e: f'LET P(z) == INSTANCE Inner WITH v <- z IN P({e})!vars',
    'nestedlet': lambda e: f'LET L == {e} IN LET M == L IN M',
    'topinst': None,
}
n = 0
for ek, e in EXPRESSIONS.items():
    for wk, wrap in WRAPPERS.items():
        for nowarning in (False, True):
            d = f'{out}/{wk}-{ek}' + ('-nw' if nowarning else '')
            os.makedirs(d, exist_ok=True)
            if wrap is None:
                extra, subscript = f'T == INSTANCE Inner WITH v <- {e}\n', 'T!vars'
            else:
                extra, subscript = '', wrap(e)
            open(f'{d}/M.tla', 'w').write(HEAD + extra + f"Spec == x = 0 /\\ y = 0 /\\ [][x' = x /\\ y' = y]_({subscript})\n====\n")
            open(f'{d}/M.cfg', 'w').write('SPECIFICATION Spec\n')
            open(f'{d}/Inner.tla', 'w').write(INNER)
            if nowarning:
                open(f'{d}/args', 'w').write('-nowarning\n')
            n += 1
print(n)
