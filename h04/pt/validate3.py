"""Validate the perturbative pipeline on a small graph.

Exact: f(eps) = coefficient of Q(phi) in log E_C[exp V_eps(psi + phi)], with C = (-Delta_graph + m^2)^{-1},
computed by full Berezin integration (background phi as 4 extra Grassmann generators).
Engine: the same quantity at orders eps^2 and eps^3 from the diagram sums, with matrix covariance.
"""
import sys
import numpy as np
from math import factorial
import grassmann as Gr
import wick as W

edges = [(0, 1), (1, 2), (2, 0)]
n = 3
m2 = 0.49
cQ = 2.0
kappa = 0.7   # delta = kappa * eps
Lap = np.zeros((n, n))
for (i, j) in edges:
    Lap[i, i] += 1; Lap[j, j] += 1; Lap[i, j] -= 1; Lap[j, i] -= 1
Amat = Lap + m2 * np.eye(n)
Gm = np.linalg.inv(Amat)

# ---------------- exact ----------------
# generators: background 0..3 (phibar1, phi1, phibar2, phi2), then psibar^a_x, psi^a_x at 4 + 4x + 2a + t
NB = 4
def bg(a, bar): return Gr.gen(2 * a + (0 if bar else 1))
def fl(x, a, bar): return Gr.gen(NB + 4 * x + 2 * a + (0 if bar else 1))
def F(x, a, bar): return Gr.add(fl(x, a, bar), bg(a, bar))
def S(x): return Gr.add(*[Gr.mul(F(x, a, 1), F(x, a, 0)) for a in (0, 1)])
def Qf(x): return Gr.mul(Gr.mul(F(x, 0, 1), F(x, 0, 0)), Gr.mul(F(x, 1, 1), F(x, 1, 0)))
def Sfl(x): return Gr.add(*[Gr.mul(fl(x, a, 1), fl(x, a, 0)) for a in (0, 1)])
ntot = NB + 4 * n
flmask = ((1 << ntot) - 1) ^ ((1 << NB) - 1)

gauss = {}
for a in (0, 1):
    for x in range(n):
        for y in range(n):
            if Amat[x, y] != 0:
                gauss = Gr.add(gauss, Gr.scale(Amat[x, y], Gr.mul(fl(x, a, 1), fl(y, a, 0))))
Wg = Gr.exp_even(gauss, 2 * n)

def berezin_fl(X):
    """Integrate out fluctuations: keep coefficients of monomials whose fluct part is full."""
    out = {}
    for mk, c in X.items():
        if mk & flmask == flmask:
            out[mk & ((1 << NB) - 1)] = out.get(mk & ((1 << NB) - 1), 0.0) + c
    return out

Z0 = berezin_fl(Wg)[0]
gradS = {e: Gr.add(S(e[0]), Gr.scale(-1, S(e[1]))) for e in edges}
gradQ = {e: Gr.add(Qf(e[0]), Gr.scale(-1, Qf(e[1]))) for e in edges}

def exactQ(eps):
    V = {}
    for e in edges:
        V = Gr.add(V, Gr.scale(eps / 2, Gr.mul(gradS[e], gradS[e])),
                   Gr.scale(eps ** 2, Gr.mul(gradS[e], gradQ[e])),
                   Gr.scale(eps ** 3 / 2, Gr.mul(gradQ[e], gradQ[e])))
    for x in range(n):
        V = Gr.add(V, Gr.scale(cQ * eps ** 2, Qf(x)), Gr.scale(kappa * eps, S(x)))
    # exp of V (even; split off constant-free part)
    EV = Gr.exp_even(V, ntot)
    R = berezin_fl(Gr.mul(Wg, EV))
    R = {k: c / Z0 for k, c in R.items()}
    c0 = R.get(0, 0.0)
    # log: quartic part = R4/c0 - (R2)^2/(2 c0^2); R2 = quadratic part
    R2 = {k: c for k, c in R.items() if bin(k).count("1") == 2}
    R4 = R.get(15, 0.0)
    sq = Gr.mul(R2, R2).get(15, 0.0)
    return R4 / c0 - sq / (2 * c0 ** 2)

eps_list = np.linspace(0.002, 0.016, 8)
vals = np.array([exactQ(e) for e in eps_list])
# fit f = a2 eps^2 + a3 eps^3 + a4 eps^4 + a5 eps^5 + a6 eps^6
M = np.vstack([eps_list ** k for k in range(2, 7)]).T
coef = np.linalg.lstsq(M, vals, rcond=None)[0]
print("exact fit: a2 = %.8f  a3 = %.8f" % (coef[0], coef[1]))

# ---------------- engine (matrix covariance) ----------------
W.cov_symbol = lambda s, t: ('m', s[1][0], t[1][0])
def site(i): return ('g', (i,))
def evalp(p): return sum(c * np.prod([Gm[k[1], k[2]] for k in ks]) for ks, c in p.items())
def gS(alg, e): return W.add(W.S(alg, site(e[0])), W.scale(-1.0, W.S(alg, site(e[1]))))
def gQ(alg, e): return W.add(W.Q(alg, site(e[0])), W.scale(-1.0, W.Q(alg, site(e[1]))))
import qvertex3_lib as L
alg = W.Alg()
# order eps^2
a2 = cQ * n
for e in edges:
    a2 += evalp(L.Q15(L.E(alg, W.mul(gS(alg, e), gQ(alg, e)))))
for e in edges:
    for f in edges:
        b1 = L.trunc(W.mul(gS(alg, e), gS(alg, e)), 2); b2 = L.trunc(W.mul(gS(alg, f), gS(alg, f)), 2)
        a2 += 0.5 * 0.25 * evalp(L.cum2(alg, b1, b2))
# order eps^3
a3 = 0.0
for e in edges:
    a3 += 0.5 * evalp(L.Q15(L.E(alg, W.mul(gQ(alg, e), gQ(alg, e)))))
for e in edges:
    b1 = L.trunc(W.mul(gS(alg, e), gS(alg, e)), 2)
    for f in edges:
        a3 += 0.5 * evalp(L.cum2(alg, b1, L.trunc(W.mul(gS(alg, f), gQ(alg, f)), 4)))
    for x in range(n):
        a3 += 0.5 * cQ * evalp(L.cum2(alg, b1, W.Q(alg, site(x))))
bs = {e: L.trunc(W.mul(gS(alg, e), gS(alg, e)), 2) for e in edges}
for e1 in edges:
    for e2 in edges:
        for e3 in edges:
            a3 += evalp(L.cum3(alg, bs[e1], bs[e2], bs[e3])) / 48.0
# delta-vertex terms at eps^3
Ss = {x: W.S(alg, site(x)) for x in range(n)}
for x in range(n):
    for e in edges:
        a3 += kappa * evalp(L.cum2(alg, L.trunc(W.mul(gS(alg, e), gQ(alg, e)), 4), Ss[x]))
    for y in range(n):
        a3 += kappa * cQ * evalp(L.cum2(alg, W.Q(alg, site(y)), Ss[x]))
    for e in edges:
        for f in edges:
            a3 += kappa * evalp(L.cum3(alg, bs[e], bs[f], Ss[x])) / 8.0
print("engine:    a2 = %.8f  a3 = %.8f" % (a2, a3))
