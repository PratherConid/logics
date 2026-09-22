from itertools import product
nm={0:'0',1:'m',2:'1'}                      # 3-element chain = upsets of the 2-chain frame
imp=lambda x,y: 2 if x<=y else y
neg=lambda x: imp(x,0)
dem=lambda a,b: imp(neg(min(neg(a),neg(b))), max(a,b))
luk=lambda a,b: imp(imp(neg(a),neg(b)), imp(b,a))
print("=== 3-element chain (frame = 2-chain) ===")
print(" a  b | DeM  Luk  join")
for a,b in product([0,1,2],repeat=2):
    d,l=dem(a,b),luk(a,b)
    print(f" {nm[a]}  {nm[b]} |  {nm[d]}    {nm[l]}    {nm[max(d,l)]}")
print("EM:", {nm[a]: nm[max(a,neg(a))] for a in [0,1,2]})

print("\n=== 4-element chain 0 < p < q < 1 (frame = 3-chain): counterexamples ===")
N={0:'0',1:'p',2:'q',3:'1'}
imp4=lambda x,y: 3 if x<=y else y
neg4=lambda x: imp4(x,0)
dem4=lambda a,b: imp4(neg4(min(neg4(a),neg4(b))), max(a,b))
luk4=lambda a,b: imp4(imp4(neg4(a),neg4(b)), imp4(b,a))
for a,b in product(range(4),repeat=2):
    d,l=dem4(a,b),luk4(a,b)
    if max(d,l)!=3: print(f" a={N[a]} b={N[b]}: DeM={N[d]} Luk={N[l]} join={N[max(d,l)]}")
