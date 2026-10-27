import sympy as sp, itertools
I=sp.I
F=sp.Function('f')
def vec(n): return sp.Matrix(sp.symbols(n+'x '+n+'y',real=True))
p1,p2,q1=vec('p1'),vec('p2'),vec('q1'); q2=-(p1+p2+q1)
mom={('a',1):p1,('a',2):p2,('b',1):q1,('b',2):q2}
order={('a',1):0,('b',1):1,('a',2):2,('b',2):3}
def sgn(l):
    s=1
    for i in range(len(l)):
        for j in range(i+1,len(l)):
            if l[i]>l[j]: s=-s
    return s
def dfac(v,ders,sg=1):
    r=1
    for d in ders: r*=sg*I*v[d]
    return r
def Mslots(v,i): return [(v,False,()),(v,True,()),(v,False,(i,)),(v,True,(i,))]
mass=[(1,False,()),(1,True,())]   # nu psi psibar at vertex 1
bare=0
for i in range(2):
    sl=Mslots(2,i)
    ps=[0,2]; bs=[1,3]
    for pa in itertools.permutations([('a',1),('a',2)]):
        for pb in itertools.permutations([('b',1),('b',2)]):
            gen={ps[0]:pa[0],ps[1]:pa[1],bs[0]:pb[0],bs[1]:pb[1]}
            f=sgn([order[gen[n]] for n in range(4)])
            for n in range(4): f*=dfac(mom[gen[n]],sl[n][2])
            bare+=f
tot=0
for i in range(2):
    sl=mass+Mslots(2,i)
    for slow in itertools.combinations(range(6),4):
        fast=[n for n in range(6) if n not in slow]
        if len(fast)!=2: continue
        a,b=fast
        if sl[a][1]==sl[b][1] or sl[a][0]==sl[b][0]: continue
        sps=[n for n in slow if not sl[n][1]]; sbs=[n for n in slow if sl[n][1]]
        if len(sps)!=2: continue
        s=1
        for x in range(6):
            for y in range(x+1,6):
                if x in fast and y in slow: s=-s
        zb,z=(a,b) if sl[a][1] else (b,a)
        if z<zb: s=-s
        for pa in itertools.permutations([('a',1),('a',2)]):
          for pb in itertools.permutations([('b',1),('b',2)]):
            gen={sps[0]:pa[0],sps[1]:pa[1],sbs[0]:pb[0],sbs[1]:pb[1]}
            f=s*sgn([order[gen[n]] for n in slow])
            P1=sp.zeros(2,1)
            for n in slow:
                f*=dfac(mom[gen[n]],sl[n][2])
                if sl[n][0]==1: P1+=mom[gen[n]]
            o=1 if sl[zb][0]==1 else -1
            kl=-P1/o
            f*=dfac(kl,sl[zb][2],1)*dfac(kl,sl[z][2],-1)*sp.Symbol('C0')   # propagator at small momentum ~ Chat(0)
            tot+=f
cov=sp.expand(tot)      # Cov(psi psibar, M) quartic kernel (cross terms counted once)
print('Cov(mass,M)/bare =',sp.simplify(cov/bare))
