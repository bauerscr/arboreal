"""Exact Grassmann algebra / Berezin integration for the H^{0|4} model on small graphs.

Generators: index 4*x + 2*a + t, with site x, flavour a in {0,1}, t=0 for xi, t=1 for eta.
An element is a dict {mask: coeff}; a mask is the ordered (increasing index) monomial.
"""
from math import factorial
from itertools import combinations


def popcount(n):
    return bin(n).count("1")


def mono_mul(ma, mb):
    """Product of ordered monomials; returns (sign, mask) or (0, None)."""
    if ma & mb:
        return 0, None
    inv = 0
    m = mb
    while m:
        j = (m & -m).bit_length() - 1
        inv += popcount(ma >> (j + 1))
        m &= m - 1
    return (-1 if inv & 1 else 1), ma | mb


def mul(A, B):
    out = {}
    for ma, ca in A.items():
        for mb, cb in B.items():
            s, m = mono_mul(ma, mb)
            if s:
                out[m] = out.get(m, 0.0) + s * ca * cb
    return {m: c for m, c in out.items() if c != 0.0}


def add(*Xs):
    out = {}
    for X in Xs:
        for m, c in X.items():
            out[m] = out.get(m, 0.0) + c
    return {m: c for m, c in out.items() if c != 0.0}


def scale(r, A):
    return {m: r * c for m, c in A.items()} if r != 0 else {}


def const(r):
    return {0: float(r)} if r != 0 else {}


def gen(i):
    return {1 << i: 1.0}


def exp_even(E, maxdeg):
    """exp of an even element with zero constant term (nilpotent)."""
    assert E.get(0, 0.0) == 0.0
    out = const(1.0)
    P = const(1.0)
    for k in range(1, maxdeg + 1):
        P = mul(P, E)
        if not P:
            break
        out = add(out, scale(1.0 / factorial(k), P))
    return out


class H04:
    def __init__(self, nsites, edges, beta, h1, h2):
        self.N = nsites
        self.n = 4 * nsites
        self.edges = edges
        self.beta, self.h1, self.h2 = beta, h1, h2
        W = const(1.0)
        for (x, y) in edges:
            W = mul(W, exp_even(scale(beta, add(self.dot(x, y), const(1.0))), self.n))
        for x in range(nsites):
            zm1 = add(self.z(x), const(-1.0))
            loc = add(self.s(x), scale(2.0, self.q(x)),            # log(1/z)
                      scale(-h1, zm1), scale(-h2, mul(zm1, zm1)))   # -h1(z-1) - h2(z-1)^2
            W = mul(W, exp_even(loc, self.n))
        self.W = W
        self.top = (1 << self.n) - 1
        self.Z = W.get(self.top, 0.0)

    def xi(self, x, a):
        return gen(4 * x + 2 * a)

    def eta(self, x, a):
        return gen(4 * x + 2 * a + 1)

    def s(self, x):
        return add(*[mul(self.xi(x, a), self.eta(x, a)) for a in (0, 1)])

    def q(self, x):
        return mul(mul(self.xi(x, 0), self.eta(x, 0)), mul(self.xi(x, 1), self.eta(x, 1)))

    def z(self, x):
        return add(const(1.0), scale(-1.0, self.s(x)), scale(-1.0, self.q(x)))

    def dot(self, x, y):
        t = {}
        for a in (0, 1):
            t = add(t, mul(self.xi(x, a), self.eta(y, a)), mul(self.xi(y, a), self.eta(x, a)))
        return add(scale(-1.0, t), scale(-1.0, mul(self.z(x), self.z(y))))

    def avg(self, F):
        return mul(F, self.W).get(self.top, 0.0) / self.Z
