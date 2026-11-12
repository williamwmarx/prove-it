import random, os, sys
random.seed(int(sys.argv[2]))
out=sys.argv[1]
DEFS={'C1':'1','C2':'PrintT(1)','C3':'<<1, 2>>','C4':'1 \\div 0','C5':'CHOOSE n \\in {1, 2} : TRUE','C6':'{1, 2}','C7':'"s"','C8':'<<PrintT("a"), 2>>','W':'<<x, y>>','Wx':'<<x>>','N':'TRUE'}
def sub(d):
    r=random.random()
    if d>2 or r<0.3: return random.choice(['x','y','x','y','1','"s"','C1','C2','C3','C4','C5','C6','C7','C8','W','Wx','N','V(x)','V(1)','x + 1'])
    if r<0.6: return '<<'+', '.join(sub(d+1) for _ in range(random.randint(0,3)))+'>>'
    if r<0.7: return '(IF TRUE THEN '+sub(d+1)+' ELSE '+sub(d+1)+')'
    if r<0.8: return '(LET L == '+sub(d+1)+' IN L)'
    if r<0.9: return 'V('+sub(d+1)+')'
    return '[a |-> '+sub(d+1)+']'
for k in range(int(sys.argv[3])):
    d=f'{out}/sub-{sys.argv[2]}-{k}'; os.makedirs(d,exist_ok=True)
    defs='\n'.join(f'{n} == {b}' for n,b in DEFS.items())
    open(f'{d}/M.cfg','w').write('SPECIFICATION Spec\n')
    open(f'{d}/M.tla','w').write(f"---- MODULE M ----\nEXTENDS Integers, TLC\nVARIABLES y, x\n{defs}\nV(v) == v\nSpec == x = 0 /\\ y = 0 /\\ [][x' = x /\\ y' = y]_{sub(0)}\n====\n")
# override shapes
TC='---- MODULE TransitiveClosure ----\nWarshall(R) == "stub"\nOther == 3\n====\n'
shapes=[]
for imp in ['EXTENDS TransitiveClosure, TLC','EXTENDS TLC\nI == INSTANCE TransitiveClosure','EXTENDS TLC\nLOCAL INSTANCE TransitiveClosure','EXTENDS TLC\nJ(c) == INSTANCE TransitiveClosure']:
    for root in ['', 'Warshall2(a) == a', 'Local(a) == a']:
        for use in ['1','Other','Warshall({<<1, 2>>})','I!Warshall({<<1, 2>>})','I!Other','J(1)!Warshall({<<1, 2>>})','Local(2)']:
            shapes.append((imp,root,use))
for k,(imp,root,use) in enumerate(shapes):
    d=f'{out}/ovr-{k}'; os.makedirs(d,exist_ok=True)
    open(f'{d}/TransitiveClosure.tla','w').write(TC)
    open(f'{d}/M.cfg','w').write('INIT Init\nNEXT Next\n')
    open(f'{d}/M.tla','w').write(f"---- MODULE M ----\n{imp}\nVARIABLE x\n{root}\nASSUME PrintT({use})\nInit == x = 0\nNext == x' = x\n====\n")
