import numpy as np
D=3
for N,m in [(64,0.4),(96,0.2),(160,0.1),(256,0.05)]:
    k=2*np.pi*np.fft.fftfreq(N).astype(np.float64)
    lam=sum(2*(1-np.cos(x)) for x in np.meshgrid(k,k,k,indexing='ij',sparse=True))
    gh=1/(lam+m*m); G=np.real(np.fft.ifftn(gh))
    G0=G.flat[0]; G2=np.sum(G**2); L=np.sum(G**3)
    print(f"m={m:5.3f} N={N}: G0={G0:.6f}  m*G2={m*G2:.5f} (1/8pi={1/(8*np.pi):.5f})  L={L:.5f}  L-log(1/m)/(16pi^2)={L-np.log(1/m)/(16*np.pi**2):.5f}",flush=True)
    del G,gh,lam
