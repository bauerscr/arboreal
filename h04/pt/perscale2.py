"""Per-scale running couplings at O(eps) (mass) and O(eps^2) (Q-vertex) for d = 4, with h02rg's FRD.

With w_j = C_1 + ... + C_j (scales <= j integrated out), the constant-background vertices are
  a_j / eps   = (1 + h1) - int lambda w_j,
  g_j / eps^2 = (cQ - 2) + 2 int (1 - lambda w_j)^2,
int = int dk/(2pi)^4 = int rho(lambda) d lambda.   (At j = infinity: eps(h1 + m^2 G(0)) and eps^2(h1 - 2h2 + 2 m^4 G2(0)).)
"""
import sys
import numpy as np
import frd

d = 4
L = float(sys.argv[1]) if len(sys.argv) > 1 else 4.0
JMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 7

# ---- lattice density of states in d = 4 (masses on a fine grid, 4-fold convolution) ----
h = 2e-5
edges = np.arange(0, 4 + h, h)
cdf1 = (2 / np.pi) * np.arcsin(np.sqrt(np.clip(edges / 4, 0, 1)))
m1 = np.diff(cdf1)
n = 4 * len(m1)
fm = np.fft.rfft(m1, n)
m4 = np.fft.irfft(fm ** 4, n)[: 4 * len(m1) - 3]
lam_bins = (np.arange(len(m4)) + 2.0) * h          # centre of the sum of 4 bin-centres (approx)
# continuum asymptotics near 0: rho ~ lambda/(16 pi^2) (1 + c lambda); fit c on [0.02, 0.1]
dens = m4 / h
sel = (lam_bins > 0.02) & (lam_bins < 0.1)
c_fit = np.polyfit(lam_bins[sel], dens[sel] / (lam_bins[sel] / (16 * np.pi ** 2)) - 1, 1)
print('density check: rho/(lam/16pi^2) - 1 fit:', c_fit, '  total mass:', m4.sum())

# integration grid: log-spaced for small lambda (continuum form), histogram for lambda > 0.05
lam_small = np.geomspace(1e-14, 0.05, 1500)
rho_small = lam_small / (16 * np.pi ** 2) * (1 + np.polyval(c_fit, lam_small))
big = lam_bins > 0.05
lam_big, w_big = lam_bins[big][::10], m4[big].reshape(-1)[: (big.sum() // 10) * 10].reshape(-1, 10).sum(1)
lam_big = lam_big[: len(w_big)]

def integrate(Fs, Fb):
    return np.trapezoid(rho_small * Fs, lam_small) + np.sum(w_big * Fb)

m2 = 0.0
def scale_bounds(j):
    return (0.0 if j == 1 else L ** (j - 1) / 2, L ** j / 2)

ws, wb = np.zeros_like(lam_small), np.zeros_like(lam_big)
print(f"L = {L}, m = 0, h1 = h2 = 0   (d = 4)")
print(" j   int lam w_j     a_j/eps         g_j/eps^2        L^{4j} g_j/eps^2     Delta g_j/eps^2")
gprev = 2.0
for j in range(1, JMAX + 1):
    lo, hi = scale_bounds(j)
    ws = ws + frd.Chat(lam_small, m2, d, lo, hi)
    wb = wb + frd.Chat(lam_big, m2, d, lo, hi)
    I1 = integrate(lam_small * ws, lam_big * wb)
    a = 1 - I1
    g = 2 * integrate((1 - lam_small * ws) ** 2, (1 - lam_big * wb) ** 2)
    print(f"{j:2d}  {I1:.10f}  {a:+.6e}  {g:+.6e}  {g * L ** (4 * j):+.6e}  {g - gprev:+.6e}", flush=True)
    gprev = g
