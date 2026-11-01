import wick as W, pickle, time
D=W.D; Z0=W.ZERO
O=('0',Z0); Y=('y',Z0)
# term A: per site, sum over mu of E[-(grad_mu S)(grad_mu Q)] |_{Q(phi)}; by symmetry = D * (mu=0)
alg=W.Alg()
t=time.time()
A6 = W.mul(W.grad(W.S,alg,O,0), W.grad(W.Q,alg,O,0))
A6 = W.background_coeff(W.expect(alg, A6))   # coefficient +eps^2 of (grad S)(grad Q)
A6 = {k: D*c for k,c in A6.items()}
print("A (psi^6 tadpole) =", A6, f"({time.time()-t:.1f}s)")
# term B: (1/8) sum_y sum_{mu,nu} conn[(grad_mu S_0)^2 (grad_nu S_y)^2] |_{Q(phi)}
res={}
for (mu,nu,mult) in [(0,0,D),(0,1,D*(D-1))]:
    alg=W.Alg(); t=time.time()
    g0=W.grad(W.S,alg,O,mu); gy=W.grad(W.S,alg,Y,nu)
    B0=W.mul(g0,g0); By=W.mul(gy,gy)
    full=W.background_coeff(W.expect(alg, W.mul(B0,By)))
    disc=W.background_coeff(W.mul(W.expect(alg,B0), W.expect(alg,By)))
    conn=W.add(full, W.scale(-1.0,disc))
    conn={k: c*mult/8.0 for k,c in conn.items()}
    res[(mu,nu)]=conn
    print(f"B[mu={mu},nu={nu}]: {len(conn)} monomials ({time.time()-t:.1f}s)")
    for k,c in sorted(conn.items(), key=lambda kc: str(kc[0])): print("   ",c,k)
pickle.dump((A6,res),open('qvertex_sym.pkl','wb'))
