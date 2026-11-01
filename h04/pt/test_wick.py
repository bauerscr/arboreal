import numpy as np, random, itertools
import wick as W
import grassmann as Gr
# exact Gaussian on 3 vertices, 2 flavours: weight exp(sum_a sum_xy psibar^a_x A_xy psi^a_y)
rng = np.random.default_rng(1); n=3
A = rng.normal(size=(n,n)); A = A + A.T + 6*np.eye(n); Gm = np.linalg.inv(A)
# exact engine: xi(x,a) <-> psibar^a_x, eta(x,a) <-> psi^a_x
E = {}
for a in (0,1):
    for x in range(n):
        for y in range(n):
            E = Gr.add(E, Gr.scale(A[x,y], Gr.mul(Gr.gen(4*x+2*a), Gr.gen(4*y+2*a+1))))
Wt = Gr.exp_even(E, 12); top=(1<<12)-1; Z=Wt[top]
def exact(fs):  # fs: list of (x,a,bar)
    F={0:1.0}
    for (x,a,b) in fs: F = Gr.mul(F, Gr.gen(4*x+2*a+(0 if b else 1)))
    return Gr.mul(F,Wt).get(top,0.0)/Z
# engine with matrix covariance
W.cov_symbol = lambda s,t: ('m', s[1][0], t[1][0])
def eng(fs):
    fl=[('f',('0',(x,0,0,0)),a,b) for (x,a,b) in fs]
    r = W.wick(fl); return sum(c*np.prod([Gm[k[1],k[2]] for k in ks]) for ks,c in r.items())
maxerr=0
for trial in range(300):
    k = random.choice([2,4,6])
    fs=[(random.randrange(n),random.randrange(2),random.randrange(2)) for _ in range(k)]
    e1,e2=exact(fs),eng(fs); maxerr=max(maxerr,abs(e1-e2))
print("max |exact - wick| over 300 random products:", maxerr)
