"""gen_reach.py <out>: specs whose user TransitiveClosure.tla TLC's Java class replaces, reached or not from what TLC evaluates."""
import os, sys
out = sys.argv[1]
TC = '---- MODULE TransitiveClosure ----\nWarshall(R) == "stub"\nOther == 3\n====\n'
HELPER = '---- MODULE Helper ----\nEXTENDS TransitiveClosure\nH(r) == Warshall(r)\nH2(r) == H(r)\nHz == 1\n====\n'
R = '{<<1, 2>>, <<2, 3>>}'
imports = {
    'ext': ('EXTENDS TransitiveClosure, TLC, Naturals', 'Warshall'),
    'inst': ('EXTENDS TLC, Naturals\nI == INSTANCE TransitiveClosure', 'I!Warshall'),
    'local': ('EXTENDS TLC, Naturals\nLOCAL INSTANCE TransitiveClosure', 'Warshall'),
}


def shapes(W):
    # (name, definitions, assumption, extra configuration)
    return [
        ('unused1', f'U1(r) == {W}(r)', 'TRUE', ''),
        ('unused2', f'U1(r) == {W}(r)\nU2(r) == U1(r)', 'TRUE', ''),
        ('unused-chain-used-other', f'U1(r) == {W}(r)\nU2(r) == U1(r)\nV(r) == r', f'V({R}) = {R}', ''),
        ('oparg', f'U1(r) == {W}(r)\nAp(F(_), r) == F(r)', f'Ap(U1, {R}) = Ap(U1, {R})', ''),
        ('oparg-unused', f'U1(r) == {W}(r)\nAp(F(_), r) == F(r)\nUse == 1', 'TRUE', ''),
        ('cfg-invariant', f'U1(r) == {W}(r)\nInv == U1({R}) = U1({R})', 'TRUE', 'INVARIANT Inv\n'),
        ('cfg-substitute', f'CONSTANT G(_)\nU1(r) == {W}(r)\nUseG == G({R}) = G({R})', 'TRUE', 'CONSTANT G <- U1\nINVARIANT UseG\n'),
        ('cfg-substitute-unused', f'CONSTANT G(_)\nU1(r) == {W}(r)', 'TRUE', 'CONSTANT G <- U1\n'),
        ('assume', f'U1(r) == {W}(r)', f'U1({R}) = U1({R})', ''),
        ('let-unused', f'U1(r) == {W}(r)\nZ(k) == LET L(r) == U1(r) IN k', 'Z(1) = 1', ''),
        ('let-used', f'U1(r) == {W}(r)\nZ(k) == LET L(r) == U1(r) IN L(k)', f'Z({R}) = Z({R})', ''),
        ('zero-arity-unused', f'U1(r) == {W}(r)\nZ0 == U1({R})', 'TRUE', ''),
        ('recursive-unused', f'RECURSIVE U1(_)\nU1(r) == IF r = {{}} THEN {W}(r) ELSE U1({{}})', 'TRUE', ''),
        ('recursive-used', f'RECURSIVE U1(_)\nU1(r) == IF r = {{}} THEN {W}(r) ELSE U1({{}})', f'U1({R}) = U1({R})', ''),
    ]


n = 0
for imp, (header, W) in imports.items():
    for name, defs, assume, cfg in shapes(W):
        for printed in ('', 'print'):
            d = f'{out}/{imp}-{name}{"-" + printed if printed else ""}'
            os.makedirs(d, exist_ok=True)
            open(f'{d}/TransitiveClosure.tla', 'w').write(TC)
            a = f'PrintT({assume})' if printed else assume
            open(f'{d}/M.tla', 'w').write(f"---- MODULE M ----\n{header}\nVARIABLE x\n{defs}\nASSUME {a}\nInit == x = 0\nNext == x' = x\n====\n")
            open(f'{d}/M.cfg', 'w').write(f'INIT Init\nNEXT Next\n{cfg}')
            n += 1
# Through an INSTANCE's copy of a module of the user's that names the replaced operator.
for name, defs, assume in [
    ('copy-unused', 'J == INSTANCE Helper', 'TRUE'),
    ('copy-used', 'J == INSTANCE Helper', f'J!H({R}) = J!H({R})'),
    ('copy-used2', 'J == INSTANCE Helper', f'J!H2({R}) = J!H2({R})'),
    ('copy-zero', 'J == INSTANCE Helper', 'J!Hz = 1'),
    ('copy-param-unused', 'J(c) == INSTANCE Helper', 'TRUE'),
    ('copy-param-used', 'J(c) == INSTANCE Helper', f'J(1)!H({R}) = J(1)!H({R})'),
]:
    d = f'{out}/inst-{name}'
    os.makedirs(d, exist_ok=True)
    open(f'{d}/TransitiveClosure.tla', 'w').write(TC)
    open(f'{d}/Helper.tla', 'w').write(HELPER)
    open(f'{d}/M.tla', 'w').write(f"---- MODULE M ----\nEXTENDS TLC, Naturals\nVARIABLE x\n{defs}\nASSUME PrintT({assume})\nInit == x = 0\nNext == x' = x\n====\n")
    open(f'{d}/M.cfg', 'w').write('INIT Init\nNEXT Next\n')
    n += 1
print(n)
