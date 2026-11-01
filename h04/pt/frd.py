"""The finite range decomposition of h02rg (Appendix app:decomp) with the explicit polynomial family of the
Lean construction (FRD/PtFourier, FRD/PtPre, FRD/PtAverage):

  g0(x) = exp(-1/(1/4 - x^2)) on |x| < 1/2,   psi = (F g0)^2  (Fourier convention e^{-2 pi i x xi}),
  f = g0 * g0,  c0 = int_0^inf s psi(s) ds,  cc = 2 pi^2 c0,  AA = (2/3) f(0) / cc,
  Q_t(1 - cos 2 pi x) = sum_k t psi(t (x + k))            (Poisson identity, PtPre docstring),
  P0_t(u) = Q_t(u)/(cc t) + AA 1_{1 <= t <= 2}   (t >= 1),   P0_t = 0 (t < 1),
  P_t(u)  = sum_{j=0}^{floor t} a_j P0_{t/2^j}(u),   a_j = (1/j!)/(e 4^j).
  hat C_S(k) = (2d+m^2)^{-1} int_S t P_t(uhat) dt,   uhat = (lambda(k)+m^2)/(2d+m^2).
"""
import numpy as np
from math import factorial, e as E_CONST
from scipy.integrate import quad

def g0(x):
    s = 0.25 - x * x
    return np.exp(-1.0 / s) if s > 0 else 0.0

# tabulate ghat on a grid, psi = ghat^2
_XI = np.linspace(0, 60, 6001)
def _ghat(xi):
    return 2 * quad(lambda x: g0(x) * np.cos(2 * np.pi * x * xi), 0, 0.5, limit=400)[0]
_GH = np.array([_ghat(x) for x in _XI])
_PSI = _GH ** 2

def psi(xi):
    xi = np.abs(xi)
    return np.where(xi < _XI[-1], np.interp(xi, _XI, _PSI), 0.0)

C0 = quad(lambda s: s * float(psi(s)), 0, 60, limit=400)[0]
CC = 2 * np.pi ** 2 * C0
F0 = quad(lambda t: g0(t) ** 2, -0.5, 0.5)[0]          # f(0) = int g0(t) g0(-t) dt
AA = 2.0 / 3.0 * F0 / CC
W_TOT = E_CONST

def a_j(j):
    return (1.0 / factorial(j)) / (W_TOT * 4 ** j)

def Q(t, u):
    """Q_t(u) for u in [0,2] via x_u = arccos(1-u)/(2 pi)."""
    x = np.arccos(np.clip(1 - u, -1, 1)) / (2 * np.pi)
    out = np.zeros_like(x)
    for k in range(-2, 3):
        out = out + t * psi(t * (x + k))
    return out

def P0(t, u):
    if t < 1:
        return np.zeros_like(u)
    return Q(t, u) / (CC * t) + (AA if t <= 2 else 0.0)

def P(t, u):
    out = np.zeros_like(u)
    jmax = int(np.floor(np.log2(t))) if t >= 1 else -1     # P0_{t/2^j} = 0 when t/2^j < 1
    for j in range(jmax + 1):
        out = out + a_j(j) * P0(t / 2 ** j, u)
    return out

def Chat(lam, m2, d, tlo, thi, npts=120):
    """(2d+m^2)^{-1} int_{tlo}^{thi} t P_t(uhat) dt, vectorised over lam.  Gauss-Legendre in log t on each piece
    between the breakpoints t = 2^k (where P_t is discontinuous)."""
    u = (lam + m2) / (2 * d + m2)
    lo = max(tlo, 1.0)
    if thi <= lo:
        return np.zeros_like(lam)
    bps = [lo] + [2.0 ** k for k in range(0, 64) if lo < 2.0 ** k < thi] + [thi]
    xg, wg = np.polynomial.legendre.leggauss(npts)
    tot = np.zeros_like(lam)
    for a, b in zip(bps[:-1], bps[1:]):
        la, lb = np.log(a), np.log(b)
        for x, wq in zip(xg, wg):
            s = 0.5 * (lb - la) * x + 0.5 * (lb + la)
            tt = np.exp(s)
            tot = tot + 0.5 * (lb - la) * wq * tt * tt * P(tt, u)
    return tot / (2 * d + m2)

if __name__ == '__main__':
    print('c0 =', C0, ' cc =', CC, ' f(0) =', F0, ' AA =', AA)
    # normalisation check: int_0^inf t P_t(u) dt = 1/u
    for u in [0.05, 0.2, 0.7, 1.5]:
        val = Chat(np.array([u * 8 - 0.0]), 0.0, 2, 0.0, 1e5)[0] * 8   # d=2: (2d+m^2)=4... uhat=lam/4
        val = Chat(np.array([4 * u]), 0.0, 2, 0.0, 1e5)[0] * 4
        print(f'u={u}: int t P_t(u) dt = {val:.6f}   1/u = {1/u:.6f}')
