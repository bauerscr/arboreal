exec(open("checkP.py").read())
setup(0.0000969866415335882327182094848949)
for u in [1e-10,1e-4,0.5,2]:
    T=1.0
    print(u,G(T,u),F(T,u),D(T,2,u), G(2,u),F(2,u))
