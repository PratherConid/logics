from itertools import product
import sys
exec(open('compare.py').read().split('sep=[]')[0])

def check(points, leq):
    els,top,bot,imp=upset_alg(points,leq); neg=lambda A: imp(A,bot)
    peir=lambda a,b: imp(imp(imp(a,b),a),a)
    luk =lambda a,b: imp(imp(neg(a),neg(b)), imp(b,a))
    P=all((peir(a,b)|luk(a,b))==top for a,b in product(els,els))
    W=all((neg(a)|neg(neg(a)))==top for a in els)
    return P,W,len(els)

def frame(name, order):
    pts=sorted(order)
    P,W,n=check(pts, lambda x,y: y in order[x])
    print(f"{name:26s} |H|={n:3d}   PierceOrLuk valid={str(P):5s}   weakEM valid={W}", flush=True)

# root with two incomparable successors: PierceOrLuk holds, weak EM fails
frame("fork(1,1)", {0:{0,1,2},1:{1},2:{2}})
# fork of two 2-chains: PierceOrLuk fails
frame("fork(2,2)", {0:{0,1,2,3,4},1:{1,2},2:{2},3:{3,4},4:{4}})
# same, with a top point added -> directed frame, so weak EM should hold
frame("fork(2,2) + top", {0:{0,1,2,3,4,5},1:{1,2,5},2:{2,5},3:{3,4,5},4:{4,5},5:{5}})
# another directed frame: diamond with a tail
frame("diamond + top", {0:{0,1,2,3},1:{1,3},2:{2,3},3:{3}})
