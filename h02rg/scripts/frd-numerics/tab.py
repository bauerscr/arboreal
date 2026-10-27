import mpmath as mp, numpy as np, time
mp.mp.dps = 30
def g0(x):
    s = mp.mpf(1)/4 - x*x
    return mp.e**(-1/s) if s > 0 else mp.mpf(0)
def ghat(xi):
    xi = mp.mpf(xi)
    n = max(8, int(4*xi)+8)
    pts = [mp.mpf(-1)/2 + mp.mpf(k)/n for k in range(n+1)]
    return mp.quad(lambda x: g0(x)*mp.cos(2*mp.pi*xi*x), pts)
t=time.time()
h=0.05; xs=np.arange(0,60+h/2,h)
psi=[]
for xi in xs:
    v=ghat(xi); psi.append(v*v)
print("time",time.time()-t)
np.save("psi.npy", np.array([str(p) for p in psi]))
np.save("xs.npy", xs)
f0 = mp.quad(lambda x: g0(x)**2, [-0.5,0,0.5])
print("f0", f0)
