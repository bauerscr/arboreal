"""Per-scale effective couplings with partial covariance w_j = C_1 + ... + C_j (h02rg FRD), d = 4, m = 0, h = 0.

g_j^(2)/eps^2 = cQ + A[w_j] + B[w_j]                       (cQ = 2)
g_j^(3)/eps^3 = T1 + T2 + cQ T3 + T5 + dh (T4 + T6 + cQ T7)  (dh = delta/eps = 1 at h = 0, m = 0)
evaluated on a torus with N >= 4 * range(w_j), so that there is no wrap-around (w_j has finite range L^j/2).
"""
import sys, pickle, time
import numpy as np
import frd
from qvertex3_num import evalpoly

D = 4
L = float(sys.argv[1]); N = int(sys.argv[2]); JS = [int(x) for x in sys.argv[3].split(',')]

# tabulate C_j(lambda) on a lambda grid
lg = np.concatenate([[0.0], np.geomspace(1e-8, 0.5, 1200), np.linspace(0.5, 4 * D, 3000)[1:]])
def Chat_tab(j):
    lo, hi = (0.0 if j == 1 else L ** (j - 1) / 2, L ** j / 2)
    return frd.Chat(lg, 0.0, D, lo, hi)

k = 2 * np.pi * np.fft.fftfreq(N)
K = np.meshgrid(*([k] * D), indexing='ij')
lam = sum(2 * (1 - np.cos(ki)) for ki in K)

A6, Bres = pickle.load(open('qvertex_sym.pkl', 'rb'))
P3 = pickle.load(open('qvertex3_sym.pkl', 'rb')); P3.update(pickle.load(open('qvertex3_delta.pkl', 'rb')))

lam_u, inv = np.unique(np.round(lam, 12), return_inverse=True)
print(f'{len(lam_u)} distinct lambda values on the {N}^4 torus', flush=True)
wtab = np.zeros_like(lam_u)
for j in range(1, max(JS) + 1):
    lo, hi = (0.0 if j == 1 else L ** (j - 1) / 2, L ** j / 2)
    wtab = wtab + frd.Chat(lam_u, 0.0, D, lo, hi)
    if j not in JS:
        continue
    t0 = time.time()
    what = wtab[inv].reshape(lam.shape)
    w = np.real(np.fft.ifftn(what))
    xs = np.abs(np.fft.fftfreq(N, 1 / N))
    dist = np.maximum.reduce(np.meshgrid(*([xs] * D), indexing='ij'))
    rng = dist[np.abs(w) > 1e-9 * np.abs(w).max()].max()
    g2 = 2.0 + evalpoly(A6, w) + sum(evalpoly(p, w) for p in Bres.values())
    T = {kk: evalpoly(v, w) for kk, v in P3.items()}
    g3 = T['T1'] + T['T2'] + 2 * T['T3'] + T['T5'] + 1.0 * (T['T4'] + T['T6'] + 2 * T['T7'])
    I1 = np.mean(lam * what)
    print(f"L={L} j={j} N={N} (support radius {rng:.0f}):  1-int lam w = {1-I1:+.4e}   g2/eps^2 = {g2:+.6e}   "
          f"g3/eps^3 = {g3:+.6e}   [{time.time()-t0:.0f}s]", flush=True)
    print("      " + " ".join(f"{kk}={v:+.5f}" for kk, v in sorted(T.items())), flush=True)
