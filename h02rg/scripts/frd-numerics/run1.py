exec(open("checkP.py").read().replace("f0=mp.mpf(sys.argv[1]) if len(sys.argv)>1 else None",""))
setup(0.0000969866415335882327182094848949)
print("c0",float(c0),"cc",cc,"AA",AA)
for u in [1e-8,1e-4,1e-2,0.3,1,2]:
    print("norm G0(1,u)",u, G0(1.0000001,u))
print("tail ratio Psi1(2y)/Psi1(y):")
for y in [0.1,0.5,1,2,4,8,12,16,20,25,29]:
    print(y, Psi1(2*y)/Psi1(y), "Psi1(y)=",Psi1(y))
print("Psi1(60-)",PsiA[-2])
