from itertools import product

def alg(points,leq):
    els=[]
    for bits in product([0,1],repeat=len(points)):
        s=frozenset(p for p,b in zip(points,bits) if b)
        if all(not(x in s and leq(x,y) and y not in s) for x in points for y in points): els.append(s)
    top=frozenset(points); bot=frozenset()
    imp=lambda A,B: frozenset(p for p in points if all(not(leq(p,q) and q in A and q not in B) for q in points))
    return els,top,bot,imp

def report(name,points,leq):
    els,top,bot,imp=alg(points,leq); neg=lambda A: imp(A,bot)
    impor=lambda a,b: imp(imp(a,b), neg(a)|b)
    luk  =lambda a,b: imp(imp(neg(a),neg(b)), imp(b,a))
    dem  =lambda a,b: imp(neg(neg(a)&neg(b)), a|b)
    peir =lambda a,b: imp(imp(imp(a,b),a),a)
    f=lambda g: sum(1 for a,b in product(els,els) if g(a,b)!=top)
    em=sum(1 for a in els if (a|neg(a))!=top)
    wem=sum(1 for a in els if (neg(a)|neg(neg(a)))!=top)
    print(f"{name:14s}|H|={len(els):3d}  ImpOr∨Luk={f(lambda a,b:impor(a,b)|luk(a,b)):3d}  "
          f"DeM∨Luk={f(lambda a,b:dem(a,b)|luk(a,b)):3d}  Peirce∨Luk={f(lambda a,b:peir(a,b)|luk(a,b)):3d}  "
          f"ImpOr={f(impor):3d}  EMfails={em:2d} WEMfails={wem:2d}")

def chain(n): return (list(range(n)), lambda x,y:x<=y)
for n in (1,2,3,4,5):
    report(f"{n}-chain",*chain(n))
o={0:{0,1,2},1:{1},2:{2}};            report("fork(1,1)",[0,1,2],lambda x,y:y in o[x])
o3={0:{0,1,2,3},1:{1},2:{2},3:{3}};   report("fork(1,1,1)",[0,1,2,3],lambda x,y:y in o3[x])
o4={0:{0,1,2,3,4},1:{1,2},2:{2},3:{3,4},4:{4}}; report("fork(2,2)",[0,1,2,3,4],lambda x,y:y in o4[x])
o5={0:{0,1,2,3},1:{1,3},2:{2,3},3:{3}}; report("diamond",[0,1,2,3],lambda x,y:y in o5[x])
o6={0:{0,1,2},1:{1,2},2:{2}}
o7={0:{0,1,2,3},1:{1,2,3},2:{2},3:{3}}; report("chain2+fork",[0,1,2,3],lambda x,y:y in o7[x])
