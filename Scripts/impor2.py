from itertools import product
def show(n,names):
    imp=lambda x,y: n-1 if x<=y else y
    neg=lambda x: imp(x,0)
    io_=lambda a,b: imp(imp(a,b), max(neg(a),b))
    luk=lambda a,b: imp(imp(neg(a),neg(b)), imp(b,a))
    print(f"--- {n}-element chain ---")
    for a,b in product(range(n),repeat=2):
        i,l=io_(a,b),luk(a,b)
        mark="   <= FAILS" if max(i,l)!=n-1 else ""
        if n==3 or mark: print(f" a={names[a]} b={names[b]} | ImpOr={names[i]} Luk={names[l]} join={names[max(i,l)]}{mark}")
show(3,{0:'0',1:'m',2:'1'})
show(4,{0:'0',1:'p',2:'q',3:'1'})
