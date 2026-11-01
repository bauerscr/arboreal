"""Perturbative cross-check of the two Ward identities for H^{0|4} in psi-variables, on a 4-torus.

Exponent: psibar(-Delta+m^2)psi + V, with
  V = eps*[ (1/2)sum (grad S)^2 + dh*S ] + eps^2*[ sum (grad S)(grad Q) + cQ*Q ] + eps^3*[(1/2) sum (grad Q)^2]
Model values: (1+h1) eps = m^2 + dh*eps,  cQ = 2 + h1 - 2 h2   =>  h1 = m^2/eps + dh - 1,
  2 eps^2 h2 = eps m^2 + eps^2 (1 + dh - cQ).
W1: 1 - eps<S> - eps^2<Q>          = (m^2 + eps(dh-1)) chi11 - (eps m^2 + eps^2(1+dh-cQ)) chi13
W2: eps<P> - eps^2<Q>              = eps (m^2 + eps(dh-1)) chi31 - eps (eps m^2 + eps^2(1+dh-cQ)) chi33
with S = sum_a psibar^a psi^a, P = psibar^2 psi^2, Q = psibar^1 psi^1 psibar^2 psi^2,
chi11 = sum_x <psibar^1_0 psi^1_x>, chi13 = sum_x <psibar^1_0 (psibar^2 psi^2 psi^1)_x>,
chi31 = sum_x <(psibar^1 psibar^2 psi^2)_0 psi^1_x>, chi33 = sum_x <(psibar^1 psibar^2 psi^2)_0 (psibar^2 psi^2 psi^1)_x>.
"""
import sys, itertools, time, pickle
from math import factorial
import numpy as np
import wick as W
from qvertex3_lib import mulT, trunc, addp, scale_poly
from qvertex3_num import greens, evalpoly

D = W.D
Z0 = W.ZERO
LAB = ['0', 'y', 'w', 'u']
from eval4 import evalpoly4

# ---- vertex builders (exponent coefficients, epsilon factored out) ----
ORDER = {'b': 1, 'd': 1, '6': 2, 'Q': 2, '8': 3}
DIRECTED = {'b', '6', '8'}


def vertex(alg, kind, site, mu, params, bgmax):
    dh, cQ = params
    if kind == 'b':
        g = W.grad(W.S, alg, site, mu); P = scale_poly(trunc(W.mul(g, g), bgmax), 0.5)
    elif kind == 'd':
        P = scale_poly(trunc(W.S(alg, site), bgmax), dh)
    elif kind == '6':
        P = trunc(W.mul(W.grad(W.S, alg, site, mu), W.grad(W.Q, alg, site, mu)), bgmax)
    elif kind == 'Q':
        P = scale_poly(trunc(W.Q(alg, site), bgmax), cQ)
    elif kind == '8':
        g = W.grad(W.Q, alg, site, mu); P = scale_poly(trunc(W.mul(g, g), bgmax), 0.5)
    return P


def set_partitions(items):
    if not items:
        yield []
        return
    first, rest = items[0], items[1:]
    for p in set_partitions(rest):
        for i in range(len(p)):
            yield p[:i] + [[first] + p[i]] + p[i + 1:]
        yield [[first]] + p


def joint_cumulant(alg, polys, bgmax):
    """kappa(p_1,...,p_n) = sum_pi (-1)^{|pi|-1} (|pi|-1)! prod_B E[prod_{i in B} p_i]  (blocks kept in order)."""
    n = len(polys)
    memo = {}

    def mom(block):
        key = tuple(block)
        if key not in memo:
            prod = {(0, ()): 1.0}
            for i in block:
                prod = mulT(prod, polys[i], bgmax)
            memo[key] = W.expect(alg, prod)
        return memo[key]

    out = {}
    for part in set_partitions(list(range(n))):
        k = len(part)
        coef = (-1) ** (k - 1) * factorial(k - 1)
        blocks = sorted([sorted(b) for b in part])
        prod = {(0, ()): 1.0}
        for b in blocks:
            prod = mulT(prod, mom(b), bgmax)
        out = addp(out, scale_poly(prod, coef))
    return out


def multisets(order):
    """multisets of vertex kinds with total epsilon-order == order."""
    kinds = list(ORDER)
    res = []
    def rec(start, rem, cur):
        if rem == 0:
            res.append(tuple(cur)); return
        for i in range(start, len(kinds)):
            k = kinds[i]
            if ORDER[k] <= rem:
                rec(i, rem - ORDER[k], cur + [k])
    rec(0, order, [])
    return res


def mult_factor(ms):
    f = 1
    for k in set(ms):
        f *= factorial(ms.count(k))
    return 1.0 / f


def series_obs(obs_builder, mask, maxorder, params, G, fixed_vertex=False, bgmax=4, extra=None):
    """Coefficients c_k (k=0..maxorder) of eps^k in  sum_n 1/n! kappa(obs, V,...,V)  (or, if obs_builder is None,
    the per-site vacuum log with one vertex fixed at the origin), restricted to background monomial `mask`.
    extra: optional (builder, label) for an additional summed source vertex (for chi33)."""
    coeffs = []
    t0 = time.time()
    for order in range(maxorder + 1):
        tot = 0.0
        for ms in multisets(order):
            nv = len(ms)
            if obs_builder is None and nv == 0:
                continue
            labels_needed = nv + (0 if obs_builder is None else 1) + (1 if extra else 0)
            if labels_needed > 4:
                raise ValueError(f'needs {labels_needed} positions: {ms}')
            ev = evalpoly4 if labels_needed == 4 else evalpoly
            fac = mult_factor(ms)
            # assign sites
            if obs_builder is None:
                vsites = LAB[:nv]
            else:
                vsites = LAB[1 + (1 if extra else 0):1 + (1 if extra else 0) + nv]
            # direction assignments: fix the first directed vertex's direction to 0 (times D) when allowed
            dirs_choices = []
            first_fixed = False
            for k in ms:
                if k in DIRECTED:
                    if not first_fixed:
                        dirs_choices.append([0]); first_fixed = True
                    else:
                        dirs_choices.append(list(range(D)))
                else:
                    dirs_choices.append([None])
            dfac = D if first_fixed else 1
            for dirs in itertools.product(*dirs_choices):
                alg = W.Alg()
                polys = []
                if obs_builder is not None:
                    polys.append(obs_builder(alg, ('0', Z0)))
                if extra:
                    polys.append(extra(alg, ('y', Z0)))
                for k, s, mu in zip(ms, vsites, dirs):
                    polys.append(vertex(alg, k, (s, Z0), mu, params, bgmax))
                kap = joint_cumulant(alg, polys, bgmax)
                p = W.background_coeff(kap, mask)
                tot += fac * dfac * ev(p, G)
        coeffs.append(tot)
        print(f'    order {order}: {tot:+.12f}  ({time.time()-t0:.0f}s)', flush=True)
    return np.array(coeffs)


def F(alg, site, a, bar):
    return W.field(alg, site, a, bar)


def obs_S(alg, s): return W.S(alg, s)
def obs_P(alg, s): return W.mul(F(alg, s, 1, 1), F(alg, s, 1, 0))
def obs_Q(alg, s): return W.Q(alg, s)
def obs_psibar1(alg, s): return F(alg, s, 0, 1)
def obs_O3(alg, s): return W.mul(W.mul(F(alg, s, 0, 1), F(alg, s, 1, 1)), F(alg, s, 1, 0))
def obs_O13(alg, s): return W.mul(W.mul(F(alg, s, 1, 1), F(alg, s, 1, 0)), F(alg, s, 0, 0))


def mul_series(a, b, n):
    c = np.zeros(n + 1)
    for i in range(min(len(a), n + 1)):
        for j in range(min(len(b), n + 1 - i)):
            c[i + j] += a[i] * b[j]
    return c


if __name__ == '__main__':
    N, m, dh, cQ, K = int(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3]), float(sys.argv[4]), int(sys.argv[5])
    params = (dh, cQ)
    G, _, _ = greens(N, m)
    m2 = m * m
    t0 = time.time()
    BGF2 = 0b0011     # phibar^1 phi^1
    BGbar1 = 0b0001   # phibar^1
    BG1 = 0b0010      # phi^1
    F2 = series_obs(None, BGF2, K, params, G, bgmax=2)
    print('F2', F2, f'{time.time()-t0:.0f}s', flush=True)
    S = series_obs(obs_S, 0, K - 1, params, G, bgmax=0)
    P = series_obs(obs_P, 0, K - 1, params, G, bgmax=0)
    Qv = series_obs(obs_Q, 0, K - 2, params, G, bgmax=0)
    print('S', S, 'P', P, 'Q', Qv, f'{time.time()-t0:.0f}s', flush=True)
    d31 = series_obs(obs_O3, BGbar1, K - 1, params, G, bgmax=1)
    d13 = series_obs(obs_O13, BG1, K - 1, params, G, bgmax=1)
    c33 = series_obs(obs_O3, 0, K - 2, params, G, bgmax=0, extra=obs_O13)
    print('d31', d31, 'd13', d13, 'c33', c33, f'{time.time()-t0:.0f}s', flush=True)
    # free-theory sign calibration of the background formulas
    G0 = G.flat[0]
    s31 = np.sign(d31[0] / G0); s13 = np.sign(d13[0] / G0)
    chi11 = np.zeros(K + 1); chi11[0] = 1 / m2; chi11 -= F2 / m2 ** 2   # chi11 = 1/m^2 - F2/m^4 (all orders, exact)
    chi31 = s31 * d31 / m2; chi13 = s13 * d13 / m2; chi33 = c33
    print('calibration signs', s31, s13, '  free chi31, chi13 =', chi31[0], chi13[0], ' (G0/m^2 =', G0 / m2, ')')
    # W1 through eps^K
    lhs1 = np.zeros(K + 1); lhs1[0] = 1.0
    lhs1[1:] -= S[:K]
    lhs1[2:] -= Qv[:K - 1]
    pre_a = np.array([m2, dh - 1.0]); pre_b = np.array([0.0, m2, 1 + dh - cQ])
    rhs1 = mul_series(pre_a, chi11, K) - mul_series(pre_b, np.concatenate([chi13, [0]]), K)
    # W2 through eps^K
    lhs2 = np.zeros(K + 1); lhs2[1:] += P[:K]; lhs2[2:] -= Qv[:K - 1]
    eps = np.array([0.0, 1.0])
    rhs2 = mul_series(eps, mul_series(pre_a, chi31, K), K) - mul_series(eps, mul_series(pre_b, np.concatenate([chi33, [0, 0]]), K), K)
    for k in range(K + 1):
        print(f"eps^{k}:  W1 lhs={lhs1[k]:+.10f} rhs={rhs1[k]:+.10f} diff={lhs1[k]-rhs1[k]:+.2e}   "
              f"W2 lhs={lhs2[k]:+.10f} rhs={rhs2[k]:+.10f} diff={lhs2[k]-rhs2[k]:+.2e}")
    print(f'total {time.time()-t0:.0f}s')
