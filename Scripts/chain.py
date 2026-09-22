# Heyting algebra = 3-element chain 0 < m < 1  (= upsets of the 2-world Kripke chain)
els=[0,1,2]; nm={0:'0',1:'m',2:'1'}
imp=lambda x,y: 2 if x<=y else y
neg=lambda x: imp(x,0)
peirce=lambda a,b: imp(imp(imp(imp(a,b),a),a),2) if False else imp(imp(imp(a,b),a),a)
luk=lambda a,b: imp(imp(neg(a),neg(b)), imp(b,a))
print(" a  b | Peirce  Luk   join")
for a in els:
    for b in els:
        p,l=peirce(a,b),luk(a,b)
        print(f" {nm[a]}  {nm[b]} |   {nm[p]}      {nm[l]}     {nm[max(p,l)]}")
print("\nEM: ", {nm[a]: nm[max(a,neg(a))] for a in els})
