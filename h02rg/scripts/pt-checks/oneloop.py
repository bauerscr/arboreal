import sympy as sp, itertools
I=sp.I
kx,ky,eps,kap,t=sp.symbols('kx ky epsilon kappa t',real=True)
def vec(n): return sp.Matrix(sp.symbols(n+'x '+n+'y',real=True))
p1,p2,q1=vec('p1'),vec('p2'),vec('q1')
q2=-(p1+p2+q1)
k=sp.Matrix([kx,ky])
mom={('a',1):p1,('a',2):p2,('b',1):q1,('b',2):q2}
order={('a',1):0,('b',1):1,('a',2):2,('b',2):3}
def sgn_sort(gens):
    idx=[order[g] for g in gens]; s=1
    for i in range(len(idx)):
        for j in range(i+1,len(idx)):
            if idx[i]>idx[j]: s=-s
    return s
def vslots(v,i): return [(v,False,()),(v,True,()),(v,False,(i,)),(v,True,(i,))]
def dfac(vecm,ders,sign=1):
    r=1
    for d in ders: r*=sign*I*vecm[d]
    return r

def bare_kernel():
    tot=0
    for i in range(2):
        sl=vslots(1,i)
        psis=[n for n,s in enumerate(sl) if not s[1]]; bars=[n for n,s in enumerate(sl) if s[1]]
        for pa in itertools.permutations([('a',1),('a',2)]):
            for pb in itertools.permutations([('b',1),('b',2)]):
                gen={psis[0]:pa[0],psis[1]:pa[1],bars[0]:pb[0],bars[1]:pb[1]}
                gens=[gen[n] for n in range(4)]
                f=sgn_sort(gens)
                for n in range(4): f*=dfac(mom[gen[n]],sl[n][2])
                tot+=f
    return sp.expand(tot)

def bubble_kernel():
    tot=0
    for i in range(2):
      for j in range(2):
        sl=vslots(1,i)+vslots(2,j)
        for slow in itertools.combinations(range(8),4):
            fast=[n for n in range(8) if n not in slow]
            sps=[n for n in slow if not sl[n][1]]; sbs=[n for n in slow if sl[n][1]]
            if len(sps)!=2: continue
            fz=[n for n in fast if not sl[n][1]]; fzb=[n for n in fast if sl[n][1]]
            # cross pairings: each zbar paired with z at other vertex
            for perm in itertools.permutations(fz):
                pairs=list(zip(fzb,perm))
                if any(sl[a][0]==sl[b][0] for a,b in pairs): continue
                # sign: move fast to right preserving order
                s=1
                for a in range(8):
                    for b in range(a+1,8):
                        if a in fast and b in slow: s=-s
                # Wick sign for this matching on fast sequence (in order)
                seq=fast
                # build matching as list of index pairs in seq positions
                pos={n:m for m,n in enumerate(seq)}
                match=[(min(pos[a],pos[b]),max(pos[a],pos[b])) for a,b in pairs]
                # sign of matching = sign of permutation (m1a,m1b,m2a,m2b) in sorted pairs
                flat=[x for pr in sorted(match) for x in pr]
                ps=1
                for x in range(4):
                    for y in range(x+1,4):
                        if flat[x]>flat[y]: ps=-ps
                s*=ps
                # each pair value E[chi_first chi_second]; if z first -> minus
                for a,b in pairs:
                    if pos[b]<pos[a]: s=-s   # z (b) before zbar (a)
                for pa in itertools.permutations([('a',1),('a',2)]):
                  for pb in itertools.permutations([('b',1),('b',2)]):
                    gen={sps[0]:pa[0],sps[1]:pa[1],sbs[0]:pb[0],sbs[1]:pb[1]}
                    gens=[gen[n] for n in slow]
                    f=s*sgn_sort(gens)
                    P1=sp.zeros(2,1)
                    for n in slow:
                        f*=dfac(mom[gen[n]],sl[n][2])
                        if sl[n][0]==1: P1+=mom[gen[n]]
                    # lines: first pair momentum k, second determined by vertex-1 conservation
                    (a0,b0),(a1,b1)=pairs
                    # line l: exp(i k_l (x_u - x_w)), u=vertex of zbar
                    def orient(a): return 1 if sl[a][0]==1 else -1   # +1 if zbar at vertex1
                    o0,o1=orient(a0),orient(a1)
                    # vertex1: P1 + o0 k0 + o1 k1 = 0
                    k0=k; k1=-(P1+o0*k0)/o1
                    for (a,b),kl in (((a0,b0),k0),((a1,b1),k1)):
                        f*=dfac(kl,sl[a][2],1)*dfac(kl,sl[b][2],-1)
                        f/= (kl.dot(kl))
                    tot+=f
    return -sp.Rational(1,2)*tot

Kb=bare_kernel()
print('bare kernel:',sp.factor(Kb))
Kbub=bubble_kernel()
sub={}
for v in (p1,p2,q1):
    for c in v: sub[c]=eps*c
Ke=Kbub.subs(sub,simultaneous=True)
c2=sp.diff(Ke,eps,2).subs(eps,0)/2
c2=c2.subs({kx:kap*sp.cos(t),ky:kap*sp.sin(t)})
c2=sp.simplify(c2*kap**2)
A=sp.simplify(sp.integrate(sp.expand(sp.expand_trig(c2)),(t,0,2*sp.pi))/(2*sp.pi))
print('angular avg A:',sp.factor(A))
print('ratio A/Kb:',sp.simplify(A/Kb))
c0=sp.simplify(Ke.subs(eps,0))
print('eps^0 term:',c0)
