"""Symbolic Gaussian (Wick) engine with a constant Grassmann background, for H^{0|4} in psi-variables.

Fields: fluctuation psi^a_s, psibar^a_s at symbolic sites s = (label, offset) with label in {'0','y'}
and offset an integer vector; constant background phibar^a, phi^a (generators 0..3, ordered
phibar^1, phi^1, phibar^2, phi^2, so that the full background monomial is Q(phi)).

Covariance: <psibar^a_s psi^b_t> = delta_ab G(s - t), G symmetric (lattice-symmetric).
Coefficients are polynomials in symbols:  ('c', v)  = G(v) for a constant vector v (canonicalised by
hypercubic symmetry), and ('y', w) = G(y + w).
An element is a dict {(mask, keys): coeff} with keys a sorted tuple of symbols.
"""
from itertools import product

D = 3


def canon(v):
    return tuple(sorted(abs(c) for c in v))


def vsub(a, b):
    return tuple(x - y for x, y in zip(a, b))


def unit(mu):
    return tuple(1 if i == mu else 0 for i in range(D))


ZERO = tuple([0] * D)


class Alg:
    def __init__(self):
        self.gens = ['bgbar1', 'bg1', 'bgbar2', 'bg2']   # background first
        self.index = {g: i for i, g in enumerate(self.gens)}

    def g(self, key):
        if key not in self.index:
            self.index[key] = len(self.gens)
            self.gens.append(key)
        return {(1 << self.index[key], ()): 1.0}

    # fluctuation fields
    def psi(self, site, a):
        return self.g(('f', site, a, 0))

    def psibar(self, site, a):
        return self.g(('f', site, a, 1))

    def bg(self, a, bar):
        return {(1 << (2 * a + (0 if bar else 1)), ()): 1.0}


def popcount(n):
    return bin(n).count("1")


def mono_sign(ma, mb):
    if ma & mb:
        return 0
    inv = 0
    m = mb
    while m:
        j = (m & -m).bit_length() - 1
        inv += popcount(ma >> (j + 1))
        m &= m - 1
    return -1 if inv & 1 else 1


def mul(A, B):
    out = {}
    for (ma, ka), ca in A.items():
        for (mb, kb), cb in B.items():
            s = mono_sign(ma, mb)
            if s:
                k = (ma | mb, tuple(sorted(ka + kb)))
                out[k] = out.get(k, 0.0) + s * ca * cb
    return {k: c for k, c in out.items() if c != 0.0}


def add(*Xs):
    out = {}
    for X in Xs:
        for k, c in X.items():
            out[k] = out.get(k, 0.0) + c
    return {k: c for k, c in out.items() if c != 0.0}


def scale(r, A):
    return {k: r * c for k, c in A.items()}


LABEL_ORDER = {'0': 0, 'y': 1, 'w': 2, 'u': 3}


def cov_symbol(s, t):
    """Symbol for G(s - t) = G(t - s).  Sites are (label, offset) with label in '0','y','w'.
    ('c', v): constant G(v);  ('y', v): G(y + v);  ('w', v): G(w + v);  ('yw', v): G(w - y + v)."""
    (ls, vs), (lt, vt) = s, t
    if ls == lt:
        return ('c', canon(vsub(vs, vt)))
    if LABEL_ORDER[ls] > LABEL_ORDER[lt]:
        (ls, vs), (lt, vt) = (lt, vt), (ls, vs)
    kind = {('0', 'y'): 'y', ('0', 'w'): 'w', ('0', 'u'): 'u', ('y', 'w'): 'yw', ('y', 'u'): 'yu',
            ('w', 'u'): 'wu'}[(ls, lt)]
    return (kind, vsub(vt, vs))


def wick(fields):
    """<f_1 ... f_k> for an ordered list of fluctuation fields; returns {keys: coeff}."""
    if not fields:
        return {(): 1.0}
    if len(fields) % 2:
        return {}
    f1 = fields[0]
    out = {}
    for j in range(1, len(fields)):
        fj = fields[j]
        (_, s1, a1, b1), (_, sj, aj, bj) = f1, fj
        if a1 != aj or b1 == bj:
            continue
        sign = -1 if (j - 1) % 2 else 1        # move f_j next to f_1
        if b1 == 1:   # <psibar_s1 psi_sj> = G
            pair, ps = cov_symbol(s1, sj), 1.0
        else:         # <psi_s1 psibar_sj> = -G
            pair, ps = cov_symbol(sj, s1), -1.0
        rest = wick(fields[1:j] + fields[j + 1:])
        for k, c in rest.items():
            kk = tuple(sorted(k + (pair,)))
            out[kk] = out.get(kk, 0.0) + sign * ps * c
    return {k: c for k, c in out.items() if c != 0.0}


def expect(alg, A):
    """Gaussian expectation over fluctuations (background kept)."""
    out = {}
    for (m, keys), c in A.items():
        bgm = m & 15
        fl = [alg.gens[i] for i in range(4, len(alg.gens)) if (m >> i) & 1]
        for k2, c2 in wick(fl).items():
            kk = (bgm, tuple(sorted(keys + k2)))
            out[kk] = out.get(kk, 0.0) + c * c2
    return {k: c for k, c in out.items() if c != 0.0}


def background_coeff(A, mask=15):
    """Coefficient polynomial of a background monomial (default Q(phi))."""
    return {keys: c for (m, keys), c in A.items() if m == mask}


# ---- composite fields with psi -> psi + phi ----

def field(alg, site, a, bar):
    f = alg.psibar(site, a) if bar else alg.psi(site, a)
    return add(f, alg.bg(a, bar))


def S(alg, site):
    return add(*[mul(field(alg, site, a, 1), field(alg, site, a, 0)) for a in (0, 1)])


def Q(alg, site):
    return mul(mul(field(alg, site, 0, 1), field(alg, site, 0, 0)),
               mul(field(alg, site, 1, 1), field(alg, site, 1, 0)))


def grad(F, alg, site, mu):
    """F(site) - F(site + e_mu)."""
    lab, v = site
    w = tuple(x + y for x, y in zip(v, unit(mu)))
    return add(F(alg, site), scale(-1.0, F(alg, (lab, w))))
