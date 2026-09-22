from itertools import product

def algebra_from_poset(points, leq):
    # elements = upsets of (points, leq)
    els = []
    for bits in product([0,1], repeat=len(points)):
        s = frozenset(p for p,b in zip(points,bits) if b)
        if all(not (x in s and leq(x,y) and y not in s) for x in points for y in points):
            els.append(s)
    top = frozenset(points); bot = frozenset()
    def imp(A,B):
        # largest upset C with C∩A ⊆ B
        return frozenset(p for p in points if all(not(leq(p,q) and q in A and q not in B) for q in points))
    return els, top, bot, imp

def check(name, points, leq):
    els, top, bot, imp = algebra_from_poset(points, leq)
    neg = lambda A: imp(A, bot)
    join = lambda A,B: A|B
    peirce = lambda a,b: imp(imp(imp(imp(a,b),a),a), top) if False else imp(imp(imp(a,b),a),a)
    luk    = lambda a,b: imp(imp(neg(a),neg(b)), imp(b,a))
    bad = [(a,b) for a,b in product(els,els) if join(peirce(a,b), luk(a,b)) != top]
    em  = [a for a in els if join(a, neg(a)) != top]
    wem = [a for a in els if join(neg(a), neg(neg(a))) != top]
    print(f"{name}: |H|={len(els)}  schema-counterexamples={len(bad)}  EM-fails={len(em)}  WEM-fails={len(wem)}")

# 1-point frame (classical, 2-element algebra)
check("point", [0], lambda x,y: x==y)
# 2-chain w0 < w1  -> 3-element chain algebra
check("2-chain", [0,1], lambda x,y: x<=y)
# 3-chain
check("3-chain", [0,1,2], lambda x,y: x<=y)
# fork: root 0 below incomparable 1,2 (depth 2)
check("fork(1,1)", [0,1,2], lambda x,y: x==y or x==0)
# fork of two 2-chains: root r=0; branch a: 1<2 ; branch b: 3<4
pts=[0,1,2,3,4]
def leq_deep(x,y):
    order={0:{0,1,2,3,4},1:{1,2},2:{2},3:{3,4},4:{4}}
    return y in order[x]
check("fork(2,2)", pts, leq_deep)
