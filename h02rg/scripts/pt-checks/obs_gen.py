import sympy as sp, itertools
F=sp.Function("f")
I=sp.I
kx,ky,kap,t=sp.symbols('kx ky kappa t',real=True)
k=sp.Matrix([kx,ky])
p=sp.Matrix(sp.symbols('px py',real=True))
mom={'a':p,'b':-p}   # psi(p), psibar(-p) (momentum conservation with observable at 0 not needed at ext=0)
order={'a':0,'b':1}
def dfac(vecm,ders,sign=1):
    r=1
    for d in ders: r*=sign*I*vecm[d]
    return r
def sgn_perm(lst):
    s=1
    for i in range(len(lst)):
        for j in range(i+1,len(lst)):
            if lst[i]>lst[j]: s=-s
    return s
# observable O = psibar_0 psi_0 (coefficient -lambda sigma factored out), slots (vertex 0)
Oslots=[(0,True,()),(0,False,())]
def vsl(i): return [(1,False,()),(1,True,()),(1,False,(i,)),(1,True,(i,))]
# bare kernel of O in canonical gen order (a,b): psibar psi -> gens order [b,a]
bare=sgn_perm([order['b'],order['a']])
tot=0
for i in range(2):
    sl=Oslots+vsl(i)
    for slowV in itertools.combinations(range(2,6),2):
        slow=list(slowV); fast=[n for n in range(6) if n not in slow]
        if sorted(sl[n][1] for n in slow)!=[False,True]: continue
        fz=[n for n in fast if not sl[n][1]]; fzb=[n for n in fast if sl[n][1]]
        for perm in itertools.permutations(fz):
            pairs=list(zip(fzb,perm))
            if any(sl[a][0]==sl[b][0] for a,b in pairs): continue
            s=1
            for a in range(6):
                for b in range(a+1,6):
                    if a in fast and b in slow: s=-s
            pos={n:m for m,n in enumerate(fast)}
            match=sorted((min(pos[a],pos[b]),max(pos[a],pos[b])) for a,b in pairs)
            flat=[x for pr in match for x in pr]; s*=sgn_perm(flat)
            for a,b in pairs:
                if pos[b]<pos[a]: s=-s
            gen={n:('b' if sl[n][1] else 'a') for n in slow}
            f=s*sgn_perm([order[gen[n]] for n in slow])
            for n in slow: f*=dfac(mom[gen[n]],sl[n][2])
            # lines: zbar at u, z at w, exp(i k (x_u-x_w)); x_0 = 0. vertex-1 conservation fixes second line
            P1=sum((mom[gen[n]] for n in slow),sp.zeros(2,1))
            (a0,b0),(a1,b1)=pairs
            o0=1 if sl[a0][0]==1 else -1; o1=1 if sl[a1][0]==1 else -1
            k0=k; k1=-(P1+o0*k0)/o1
            for (a,b),kl in (((a0,b0),k0),((a1,b1),k1)):
                f*=dfac(kl,sl[a][2],1)*dfac(kl,sl[b][2],-1)*F(kl.dot(kl))
            tot+=f
# V_eff cross term: -Cov(O,V) ; O carries (-lambda sigma), V carries g.  kernel relative to bare O (-lambda sigma * bare)
K=(-1)*tot   # times (-lambda sigma) g
K0=sp.simplify(K.subs({p[0]:0,p[1]:0}))
c=sp.simplify(K0.subs({kx:kap*sp.cos(t),ky:kap*sp.sin(t)})*kap**2)
A=sp.integrate(sp.expand(c),(t,0,2*sp.pi))/(2*sp.pi)
print('A =',sp.simplify(A),' bare =',bare,' delta lambda/(lambda g) per (logL/2pi) =',sp.simplify(A/bare))
