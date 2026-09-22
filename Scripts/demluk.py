from itertools import product, combinations

def upset_algebra(points, leq):
    els=[]
    for bits in product([0,1],repeat=len(points)):
        s=frozenset(p for p,b in zip(points,bits) if b)
        if all(not(x in s and leq(x,y) and y not in s) for x in points for y in points):
            els.append(s)
    top=frozenset(points); bot=frozenset()
    imp=lambda A,B: frozenset(p for p in points if all(not(leq(p,q) and q in A and q not in B) for q in points))
    return els,top,bot,imp

def report(name,points,leq):
    els,top,bot,imp=upset_algebra(points,leq)
    neg=lambda A: imp(A,bot)
    dem=lambda a,b: imp(neg(neg(a)&neg(b)), a|b)
    luk=lambda a,b: imp(imp(neg(a),neg(b)), imp(b,a))
    peirce=lambda a,b: imp(imp(imp(a,b),a),a)
    bad_dl=[(a,b) for a,b in product(els,els) if (dem(a,b)|luk(a,b))!=top]
    bad_dem=[(a,b) for a,b in product(els,els) if dem(a,b)!=top]
    bad_luk=[(a,b) for a,b in product(els,els) if luk(a,b)!=top]
    em=[a for a in els if (a|neg(a))!=top]
    print(f"{name:12s} |H|={len(els):3d}  DeM∨Luk fails={len(bad_dl):3d}   "
          f"(DeM alone fails={len(bad_dem)}, Luk alone fails={len(bad_luk)})  EM fails={len(em)}")
    return len(bad_dl),len(em)

report("2-chain",[0,1],lambda x,y:x<=y)
report("3-chain",[0,1,2],lambda x,y:x<=y)
report("4-chain",[0,1,2,3],lambda x,y:x<=y)
report("fork(1,1)",[0,1,2],lambda x,y:x==y or x==0)
o={0:{0,1,2,3,4},1:{1,2},2:{2},3:{3,4},4:{4}}
report("fork(2,2)",[0,1,2,3,4],lambda x,y:y in o[x])
o3={0:{0,1,2,3},1:{1},2:{2},3:{3}}
report("fork(1,1,1)",[0,1,2,3],lambda x,y:y in o3[x])
