# compare evalpoly4 with brute force on a tiny torus for random monomials
import numpy as np, itertools, random
from eval4 import evalpoly4
from qvertex3_num import greens
N=3; G,_,_ = greens(N, 1.1)
pts=list(itertools.product(range(N),repeat=4))
def Gv(v): return G[tuple(np.array(v)%N)]
def brute(keys,c):
    tot=0.0
    for y in pts:
        for w in pts:
            for u in pts:
                val=c
                for kind,v in keys:
                    if kind=='c': val*=G[tuple(np.array(v))]
                    else:
                        base={'y':np.array(y),'w':np.array(w),'u':np.array(u),
                              'yw':np.array(w)-np.array(y),'yu':np.array(u)-np.array(y),'wu':np.array(u)-np.array(w)}[kind]
                        val*=Gv(base+np.array(v))
                tot+=val
    return tot
random.seed(3)
for trial in range(3):
    keys=tuple(sorted([(random.choice(['y','w','u','yw','yu','wu']), tuple(random.choice([-1,0,1]) for _ in range(4))) for _ in range(5)]))
    print(evalpoly4({keys:1.0},G), brute(keys,1.0))
