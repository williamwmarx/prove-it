"""gen_sub.py <out>: specs whose [][Next]_v subscript reads an argument passed through operators, INSTANCEs, LETs and LAMBDAs, or a constant the configuration substitutes."""
import os, sys
out = sys.argv[1]
HEAD = "---- MODULE M ----\nEXTENDS Naturals\nVARIABLES x, y\nCONSTANT C, G\nD1 == y\nD2 == 1\nD3 == <<y>>\nD4 == C\nD5 == <<x, y>>\n"
INNER = "---- MODULE Inner ----\nVARIABLES a, b, p\nISpec == a = 0 /\\ b = 0 /\\ [][a' = a /\\ b' = b]_<<a, p>>\n====\n"
INIT = "x = 0 /\\ y = 0"
NEXT = "x' = x /\\ y' = y"
ARGS = {
    'letlit': ('L', 'LET L == 1 IN '),
    'letdef': ('L', 'LET L == y IN '),
    'letstr': ('L', 'LET L == "s" IN '),
    'lit': ('1', ''),
    'const': ('C', ''),
    'var': ('y', ''),
    'd1': ('D1', ''), 'd2': ('D2', ''), 'd3': ('D3', ''), 'd4': ('D4', ''), 'd5': ('D5', ''),
}


def write(name, body, cfg_extra='', inner=False):
    d = f'{out}/{name}'
    os.makedirs(d, exist_ok=True)
    open(f'{d}/M.tla', 'w').write(HEAD + body + "====\n")
    open(f'{d}/M.cfg', 'w').write('SPECIFICATION Spec\nCONSTANT C = 3\n' + (cfg_extra or 'CONSTANT G = 4\n'))
    if inner:
        open(f'{d}/Inner.tla', 'w').write(INNER)


n = 0
for key, (arg, wrap) in ARGS.items():
    sub = f"[][{NEXT}]_<<x, v>>"
    write(f'p1-{key}', f"S(v) == {INIT} /\\ {sub}\nSpec == {wrap}S({arg})\n")
    write(f'p2-{key}', f"S(v) == {INIT} /\\ {sub}\nS2(w) == S(w)\nSpec == {wrap}S2({arg})\n")
    write(f'p2let-{key}', f"S(v) == {INIT} /\\ {sub}\nS2(w) == LET K == w IN S(K)\nSpec == {wrap}S2({arg})\n")
    if wrap:
        write(f'inst-{key}', f"Spec == {wrap.rstrip(' IN ')}\n       I == INSTANCE Inner WITH a <- x, b <- y, p <- {arg} IN I!ISpec\n", inner=True)
    else:
        write(f'inst-{key}', f"I == INSTANCE Inner WITH a <- x, b <- y, p <- {arg}\nSpec == I!ISpec\n", inner=True)
    write(f'nestlet-{key}', f"Spec == {wrap}LET K == {arg} IN {INIT} /\\ [][{NEXT}]_<<x, K>>\n")
    write(f'lambda-{key}', f"Ap(F(_)) == {INIT} /\\ [][{NEXT}]_<<x, F(0)>>\nSpec == {wrap}Ap(LAMBDA k : {arg})\n")
    write(f'lambdaarg-{key}', f"Ap(F(_), v) == {INIT} /\\ [][{NEXT}]_<<x, F(v)>>\nSpec == {wrap}Ap(LAMBDA k : k, {arg})\n")
    n += 7
for target in ['D1', 'D2', 'D3', 'D4', 'D5']:
    cfg = f'CONSTANT G <- {target}\n'
    write(f'subst-direct-{target}', f"Spec == {INIT} /\\ [][{NEXT}]_<<x, G>>\n", cfg)
    write(f'subst-param-{target}', f"S(v) == {INIT} /\\ [][{NEXT}]_<<x, v>>\nSpec == S(G)\n", cfg)
    write(f'subst-only-{target}', f"Spec == {INIT} /\\ [][{NEXT}]_G\n", cfg)
    n += 3
print(n)
# Operators whose body is a literal, or isn't, named in the subscript.
EXTRA = {
    'op-lit-param': ("K(a) == 1\nSpec == {INIT} /\\ [][{NEXT}]_<<x, K(0)>>\n", ''),
    'op-str-param': ('K(a) == "s"\nSpec == {INIT} /\\ [][{NEXT}]_<<x, K(0)>>\n', ''),
    'op-var-param': ("K(a) == y\nSpec == {INIT} /\\ [][{NEXT}]_<<x, K(0)>>\n", ''),
    'op-arg-param': ("K(a) == a\nSpec == {INIT} /\\ [][{NEXT}]_<<x, K(1)>>\n", ''),
    'let-op-lit': ("Spec == LET K(a) == 1 IN {INIT} /\\ [][{NEXT}]_<<x, K(0)>>\n", ''),
    'let-op-var': ("Spec == LET K(a) == y IN {INIT} /\\ [][{NEXT}]_<<x, K(0)>>\n", ''),
    'lambda-var': ("Ap(F(_)) == {INIT} /\\ [][{NEXT}]_<<x, F(0)>>\nSpec == Ap(LAMBDA k : y)\n", ''),
    'lambda-lit-nested': ("Ap(F(_)) == {INIT} /\\ [][{NEXT}]_<<x, F(0)>>\nAp2(G(_)) == Ap(G)\nSpec == Ap2(LAMBDA k : 1)\n", ''),
    'opref-lit': ("K(a) == 1\nAp(F(_)) == {INIT} /\\ [][{NEXT}]_<<x, F(0)>>\nSpec == Ap(K)\n", ''),
    'opref-var': ("K(a) == y\nAp(F(_)) == {INIT} /\\ [][{NEXT}]_<<x, F(0)>>\nSpec == Ap(K)\n", ''),
    'letlit-two-lets': ("Spec == LET L == 1 IN LET M == L IN {INIT} /\\ [][{NEXT}]_<<x, M>>\n", ''),
    'letlit-param-let': ("S(v) == LET M == v IN {INIT} /\\ [][{NEXT}]_<<x, M>>\nSpec == LET L == 1 IN S(L)\n", ''),
    'letlit-twice': ("S(v) == {INIT} /\\ [][{NEXT}]_<<x, v>>\nS2(w) == S(w)\nS3(u) == S2(u)\nSpec == LET L == 1 IN S3(L)\n", ''),
    'letlit-lambda': ("Ap(F(_)) == {INIT} /\\ [][{NEXT}]_<<x, F(0)>>\nSpec == LET L == 1 IN Ap(LAMBDA k : L)\n", ''),
    'letvar-lambda': ("Ap(F(_)) == {INIT} /\\ [][{NEXT}]_<<x, F(0)>>\nSpec == LET L == y IN Ap(LAMBDA k : L)\n", ''),
    'inst-def-lit': ("I == INSTANCE Inner2 WITH a <- x, b <- y\nSpec == I!ISpec\n", 'inner2'),
}
INNER2 = "---- MODULE Inner2 ----\nVARIABLES a, b\nK == 1\nKp(z) == 1\nISpec == a = 0 /\\ b = 0 /\\ [][a' = a /\\ b' = b]_<<a, K, Kp(0)>>\n====\n"
for name, (body, kind) in EXTRA.items():
    write(f'x-{name}', body.replace('{INIT}', INIT).replace('{NEXT}', NEXT))
    if kind == 'inner2':
        open(f'{out}/x-{name}/Inner2.tla', 'w').write(INNER2)
    n += 1
print(n)
