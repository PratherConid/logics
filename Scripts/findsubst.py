from itertools import product
exec(open('compare.py').read().split('sep=[]')[0])

frames=[]
for k in range(1,5):
    for pts,leq in posets(k): frames.append((pts,leq))
# a few bigger ones too
o={0:{0,1,2,3,4},1:{1,2},2:{2},3:{3,4},4:{4}}
frames.append(([0,1,2,3,4], lambda x,y: y in o[x]))

def ctx(points,leq):
    els,top,bot,imp=upset_alg(points,leq); neg=lambda A: imp(A,bot)
    return els,top,bot,imp,neg

# candidate substitution terms, as functions of (a,b,imp,neg,bot,top)
TERMS={
 'a':        lambda a,b,I,N,B,T: a,
 'b':        lambda a,b,I,N,B,T: b,
 '~a':       lambda a,b,I,N,B,T: N(a),
 '~b':       lambda a,b,I,N,B,T: N(b),
 '~~a':      lambda a,b,I,N,B,T: N(N(a)),
 '~~b':      lambda a,b,I,N,B,T: N(N(b)),
 'a|b':      lambda a,b,I,N,B,T: a|b,
 'a&b':      lambda a,b,I,N,B,T: a&b,
 'a>b':      lambda a,b,I,N,B,T: I(a,b),
 'b>a':      lambda a,b,I,N,B,T: I(b,a),
 '~a|b':     lambda a,b,I,N,B,T: N(a)|b,
 'a|~b':     lambda a,b,I,N,B,T: a|N(b),
 '~a&b':     lambda a,b,I,N,B,T: N(a)&b,
 'bot':      lambda a,b,I,N,B,T: B,
 'top':      lambda a,b,I,N,B,T: T,
}

def scheme(name):
    if name=='impor': return lambda x,y,I,N: I(I(x,y), N(x)|y)
    if name=='dem':   return lambda x,y,I,N: I(N(N(x)&N(y)), x|y)
def luk(x,y,I,N): return I(I(N(x),N(y)), I(y,x))

def search(src, tgt):
    """instances (A,B) with  src(A,B) v luk(A,B)  <=  tgt(a,b) v luk(a,b)  in every test frame"""
    S=scheme(src); Tg=scheme(tgt); good=[]
    for na,fa in TERMS.items():
        for nb,fb in TERMS.items():
            ok=True
            for points,leq in frames:
                els,top,bot,I,N=ctx(points,leq)
                for a,b in product(els,els):
                    A=fa(a,b,I,N,bot,top); B=fb(a,b,I,N,bot,top)
                    lhs=S(A,B,I,N)|luk(A,B,I,N)
                    rhs=Tg(a,b,I,N)|luk(a,b,I,N)
                    if (lhs|rhs)!=rhs: ok=False; break
                if not ok: break
            if ok: good.append((na,nb))
    return good

print("DeMOrLuk(A,B)  ->  ImpOrOrLuk(a,b):", search('dem','impor'))
print("ImpOrOrLuk(A,B) ->  DeMOrLuk(a,b):", search('impor','dem'))
