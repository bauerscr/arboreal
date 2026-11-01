"""Symbolic O(eps^3) contributions to the zero-momentum Q-vertex (coefficient of Q(phi) in
log E[exp V(psi + phi)], per site), d = 4.

V = (eps/2) sum_edges (grad S)^2 + eps^2 sum_edges (grad S)(grad Q) + (eps^3/2) sum_edges (grad Q)^2
    + c_Q eps^2 sum_x Q_x   (+ mass terms, handled analytically by m^2 -> m^2 + delta).

Per site (first vertex at the origin, directions mu in 0..D-1, each edge once):
  T1 = (1/2) sum_mu E[(grad_mu Q)^2]
  T2 = (1/2) sum_y sum_{mu,nu} cum[(grad_mu S_0)^2, (grad_nu S grad_nu Q)_y]
  T3 = (1/2) sum_y sum_mu cum[(grad_mu S_0)^2, Q_y]                 (multiplies c_Q)
  T5 = (1/48) sum_{y,w} sum_{mu1,mu2,mu3} cum[(grad S_0)^2, (grad S_y)^2, (grad S_w)^2]
"""
import pickle, time
import wick as W

D = W.D
Z0 = W.ZERO
O, Y, Wt = ('0', Z0), ('y', Z0), ('w', Z0)


def bgdeg(m):
    return bin(m & 15).count("1")


def trunc(A, maxbg):
    return {k: c for k, c in A.items() if bgdeg(k[0]) <= maxbg}


def mulT(A, B, maxbg=4):
    return trunc(W.mul(A, B), maxbg)


def E(alg, A):
    return W.expect(alg, A)


def Q15(A):
    return W.background_coeff(A, 15)


def scale_poly(p, r):
    return {k: r * c for k, c in p.items()}


def addp(*ps):
    out = {}
    for p in ps:
        for k, c in p.items():
            out[k] = out.get(k, 0.0) + c
    return {k: c for k, c in out.items() if abs(c) > 1e-12}


def bS2(alg, site, mu):
    g = W.grad(W.S, alg, site, mu)
    return trunc(W.mul(g, g), 2)


def v6(alg, site, mu):
    return trunc(W.mul(W.grad(W.S, alg, site, mu), W.grad(W.Q, alg, site, mu)), 4)


def cum2(alg, a, b):
    full = Q15(E(alg, mulT(a, b)))
    disc = Q15(mulT(E(alg, a), E(alg, b)))
    return addp(full, scale_poly(disc, -1.0))


def cum3(alg, a, b, c):
    Ea, Eb, Ec = E(alg, a), E(alg, b), E(alg, c)
    Eab, Eac, Ebc = E(alg, mulT(a, b)), E(alg, mulT(a, c)), E(alg, mulT(b, c))
    full = Q15(E(alg, mulT(mulT(a, b), c)))
    t = [Q15(mulT(Eab, Ec)), Q15(mulT(Eac, Eb)), Q15(mulT(Ebc, Ea))]
    t3 = Q15(mulT(mulT(Ea, Eb), Ec))
    return addp(full, *[scale_poly(x, -1.0) for x in t], scale_poly(t3, 2.0))


