"""One-loop Q-Q bubble for H^{0|4} in psi-variables (exact Grassmann/Wick, symbolic in the covariances).

Split psi = phi + zeta (phi: background, zeta: Gaussian fluctuation with <zetabar^a_u zeta^b_v> = delta_ab C_uv).
Weight exp(+g sum_x Q_x).  Second-order effective potential: (1/2) kappa(V,V) with V = g(Q_x + Q_y).
We extract the cross term g^2 E^T[Q_x Q_y] restricted to exactly two x-y lines, keep the c^2 = C_xy^2 coefficient,
and localise phi_y -> phi_x.  Output: coefficient K with  g^2 E^T[Q_x Q_y]|_{c^2, local} = K c^2 g^2 Q(phi_x).
Then the per-site increment of the Q-coupling is  dg = (K/2) * 2 * g^2 sum_y C(y)^2 / 2 ... (see print).
"""
import itertools
import numpy as np
from fractions import Fraction
class _SP:
    Integer=staticmethod(lambda n: Fraction(n))
    expand=staticmethod(lambda v: v)
sp=_SP()
import sys

c = Fraction(int(sys.argv[1])); c0 = Fraction(0)
SITES = ['x', 'y']
# generator: (kind, a, bar, site)   kind 'p' background, 'z' fluctuation
GENS = [(k, a, b, s) for k in ('p', 'z') for s in SITES for a in (1, 2) for b in (1, 0)]
IDX = {g: i for i, g in enumerate(GENS)}


def mono(*gs):
    """product of generators as a dict {sorted tuple: coeff} with sign from sorting."""
    lst = [IDX[g] for g in gs]
    if len(set(lst)) < len(lst):
        return {}
    sign = 1
    arr = lst[:]
    for i in range(len(arr)):
        for j in range(len(arr) - 1 - i):
            if arr[j] > arr[j + 1]:
                arr[j], arr[j + 1] = arr[j + 1], arr[j]
                sign = -sign
    return {tuple(arr): sp.Integer(sign)}


def mul(A, B):
    out = {}
    for ka, va in A.items():
        for kb, vb in B.items():
            if set(ka) & set(kb):
                continue
            m = mono(*[GENS[i] for i in ka + kb])
            for k, v in m.items():
                out[k] = sp.expand(out.get(k, 0) + v * va * vb)
    return {k: v for k, v in out.items() if v != 0}


def add(A, B, s=1):
    out = dict(A)
    for k, v in B.items():
        out[k] = sp.expand(out.get(k, 0) + s * v)
    return {k: v for k, v in out.items() if v != 0}


def field(a, bar, s):
    return add(mono(('p', a, bar, s)), mono(('z', a, bar, s)))


def Q(s):
    out = {(): sp.Integer(1)}
    for a in (1, 2):
        out = mul(out, mul(field(a, 1, s), field(a, 0, s)))
    return out


def cov(g1, g2):
    """<g1 g2> for fluctuation generators."""
    (_, a1, b1, s1), (_, a2, b2, s2) = g1, g2
    if a1 != a2 or b1 == b2:
        return 0
    C = c0 if s1 == s2 else c
    return C if b1 == 1 else -C


def wick(zs):
    if not zs:
        return sp.Integer(1)
    if len(zs) % 2:
        return 0
    tot = 0
    for k in range(1, len(zs)):
        w = cov(zs[0], zs[k])
        if w != 0:
            tot += (-1) ** (k - 1) * w * wick(zs[1:k] + zs[k + 1:])
    return tot


def expect(A):
    """Gaussian expectation over zeta: move zetas to the right (p's left), sign tracked."""
    out = {}
    for k, v in A.items():
        gs = [GENS[i] for i in k]
        ps = [g for g in gs if g[0] == 'p']
        zs = [g for g in gs if g[0] == 'z']
        # sign of reordering gs -> ps + zs
        order = [gs.index(g) for g in ps + zs]
        sign = 1
        for i in range(len(order)):
            for j in range(i + 1, len(order)):
                if order[i] > order[j]:
                    sign = -sign
        w = wick(zs)
        if w == 0:
            continue
        m = mono(*ps)
        for kk, vv in m.items():
            out[kk] = sp.expand(out.get(kk, 0) + sign * vv * w * v)
    return {k: v for k, v in out.items() if v != 0}


Qx, Qy = Q('x'), Q('y')
EQxQy = expect(mul(Qx, Qy))
T = add(EQxQy, mul(expect(Qx), expect(Qy)), -1)          # truncated
# keep c^2 coefficient, set c0 = 0 (tadpoles are mass/normal-ordering terms)
T2 = {}
for k, v in T.items():
    co = v
    if co != 0:
        T2[k] = co
# localise phi_y -> phi_x
loc = {}
for k, v in T2.items():
    gs = [GENS[i] for i in k]
    gs2 = [('p', a, b, 'x') for (_, a, b, s) in gs]
    m = mono(*gs2)
    for kk, vv in m.items():
        loc[kk] = sp.expand(loc.get(kk, 0) + vv * v)
loc = {k: v for k, v in loc.items() if v != 0}
Qphi = {k: v for k, v in Q('x').items() if all(GENS[i][0] == 'p' for i in k)}
print('Q(phi_x) =', {tuple(GENS[i] for i in k): v for k, v in Qphi.items()})
print('localised c^2 part of E^T[Q_x Q_y] =', {tuple(GENS[i] for i in k): v for k, v in loc.items()})
(kq, vq), = Qphi.items()
K = loc.get(kq, 0) / vq
print('K =', K, '  (E^T[Q_x Q_y] -> K c^2 Q_x after localisation)')
print('Effective potential: (1/2) g^2 sum_{x,y} E^T[Q_x Q_y] -> per-site Q coefficient increment  dg = (K/2)*2? :')
print('   sum over ordered pairs (x,y), x != y, counts each unordered pair twice; per site dg = (K/2) g^2 sum_y C(y)^2 * ... ')
print('   => dg = (K/2) g^2 * sum_{y != 0} C(0,y)^2  per site (ordered y)')
