import numpy as np, pickle
A6,res = pickle.load(open('qvertex_sym.pkl','rb'))
def greens(N, m):
    k = 2*np.pi*np.fft.fftfreq(N)
    K = np.meshgrid(k,k,k, indexing='ij')
    lam = sum(2*(1-np.cos(ki)) for ki in K)
    G = np.real(np.fft.ifftn(1.0/(lam+m*m)))
    G2 = np.real(np.fft.ifftn(1.0/(lam+m*m)**2))
    return G, G2
def Gc(G, v):  return G[tuple(np.array(v))]
def evalpoly(poly, G):
    tot=0.0
    for keys,c in poly.items():
        arr=np.ones_like(G)
        for kind,v in keys:
            if kind=='c': arr=arr*Gc(G,v)
            else: arr=arr*np.roll(G, shift=tuple(-x for x in v), axis=(0,1,2))
        tot += c*arr.sum() if any(k[0]=='y' for k in keys) else c*arr.flat[0]
    return tot
for N,m in [(48,0.6),(64,0.45),(96,0.3)]:
    G,G2 = greens(N,m)
    A = evalpoly(A6,G); B = sum(evalpoly(p,G) for p in res.values())
    print(f"N={N} m={m}:  A={A:.10f}  pred -4(1-m^2 G0)={-4*(1-m*m*G[0,0,0]):.10f}   B={B:.10f}  pred 2-4m^2G0+2m^4G2_0={2-4*m*m*G[0,0,0]+2*m**4*G2[0,0,0]:.10f}")
    print(f"      Gamma_Q/eps^2 at h=0: 2 + A + B = {2+A+B:.3e}   (pred 2 m^4 G2(0) = {2*m**4*G2[0,0,0]:.3e})")
