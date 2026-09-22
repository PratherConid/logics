from itertools import product, combinations

def upset_alg(points, leq):
    els=[]
    for bits in product([0,1],repeat=len(points)):
        s=frozenset(p for p,b in zip(points,bits) if b)
        if all(not(x in s and leq(x,y) and y not in s) for x in points for y in points): els.append(s)
    top=frozenset(points); bot=frozenset()
    imp=lambda A,B: frozenset(p for p in points if all(not(leq(p,q) and q in A and q not in B) for q in points))
    return els,top,bot,imp

def analyse(points,leq):
    els,top,bot,imp=upset_alg(points,leq); neg=lambda A: imp(A,bot)
    impor=lambda a,b: imp(imp(a,b), neg(a)|b)
    dem  =lambda a,b: imp(neg(neg(a)&neg(b)), a|b)
    luk  =lambda a,b: imp(imp(neg(a),neg(b)), imp(b,a))
    X=lambda a,b: impor(a,b)|luk(a,b)     # ImpOrOrLukasiewiczF
    Y=lambda a,b: dem(a,b)|luk(a,b)       # DeMOrLukasiewiczF
    Xvalid=all(X(a,b)==top for a,b in product(els,els))
    Yvalid=all(Y(a,b)==top for a,b in product(els,els))
    # pointwise order between the two left disjuncts
    dem_le_impor=all((dem(a,b)|impor(a,b))==impor(a,b) for a,b in product(els,els))
    impor_le_dem=all((dem(a,b)|impor(a,b))==dem(a,b) for a,b in product(els,els))
    return Xvalid,Yvalid,dem_le_impor,impor_le_dem,len(els)

# enumerate all posets on k points (as transitive reflexive antisymmetric relations)
def posets(k):
    pts=list(range(k)); pairs=[(i,j) for i in pts for j in pts if i!=j]
    seen=set()
    for bits in product([0,1],repeat=len(pairs)):
        rel={(i,i) for i in pts}|{p for p,b in zip(pairs,bits) if b}
        if any((i,j) in rel and (j,i) in rel for i,j in pairs): continue          # antisymmetry
        if any((i,j) in rel and (j,l) in rel and (i,l) not in rel
               for i in pts for j in pts for l in pts): continue                   # transitivity
        key=frozenset(rel)
        if key in seen: continue
        seen.add(key)
        yield (pts, lambda x,y,r=rel: (x,y) in r)

sep=[]; tot=0
for k in range(1,6):
    for pts,leq in posets(k):
        tot+=1
        Xv,Yv,dle,ile,n=analyse(pts,leq)
        if Xv!=Yv: sep.append((k,n,Xv,Yv))
        if not dle: print("  !! DeM NOT <= ImpOr pointwise on a", k, "point poset")
print(f"posets checked: {tot}")
print(f"algebras where validity of the two schemes differs: {len(sep)}")
for s in sep[:10]: print("   ",s)
