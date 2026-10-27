exec(open("checkP.py").read())
setup(0.0000969866415335882327182094848949)
us=list(np.logspace(-14,np.log10(2),57))
for L in [2,4,8,16]:
  for j in range(1,7):
    T=L**j/2
    best=(1e9,0,0,0,0,0)
    for u in us:
        g=G(T,u); fF=F(T,u); d=D(T,L,u)
        # consistency: G+F should be 1
        r=d/(g*fF) if g*fF>0 else float('inf')
        if r<best[0]: best=(r,u,g,fF,d,g+fF)
    print(L,j,"min r=%.4g at u=%.3g  G=%.3g F=%.3g D=%.3g G+F=%.6f"%best, flush=True)
