"""O(eps) Schur complement of the Ward matrix for H^{0|4} in d = 3 (psi-variables, torus).
S = chi33 - chi31 chi13 / chi11, expanded to O(eps):  S0 + eps S1.
dh is fixed by mass renormalisation (F2 at O(eps) = 0) : linear in dh, solved from two runs."""
import sys, time, numpy as np
import ward_check as WC
from qvertex3_num import greens
N, m = int(sys.argv[1]), float(sys.argv[2])
G, _, _ = greens(N, m); m2 = m*m; G0 = G.flat[0]
t0 = time.time()
def run(dh):
    p = (dh, 2.0)
    F2 = WC.series_obs(None, 0b0011, 1, p, G, bgmax=2)
    d31 = WC.series_obs(WC.obs_O3, 0b0001, 1, p, G, bgmax=1)
    d13 = WC.series_obs(WC.obs_O13, 0b0010, 1, p, G, bgmax=1)
    c33 = WC.series_obs(WC.obs_O3, 0, 1, p, G, bgmax=0, extra=WC.obs_O13)
    return F2, d31, d13, c33
A = run(0.0); B = run(1.0)
# F2[1] linear in dh: choose dh with F2[1] = 0
dh = -A[0][1] / (B[0][1] - A[0][1])
F2, d31, d13, c33 = [a + dh*(b - a) for a, b in zip(A, B)]
s31 = np.sign(d31[0]/G0); s13 = np.sign(d13[0]/G0)
chi11 = np.array([1/m2, -F2[1]/m2**2]); chi31 = s31*d31/m2; chi13 = s13*d13/m2; chi33 = c33
S0 = chi33[0] - chi31[0]*chi13[0]/chi11[0]
S1 = chi33[1] - (chi31[1]*chi13[0] + chi31[0]*chi13[1])/chi11[0] + chi31[0]*chi13[0]*chi11[1]/chi11[0]**2
L = np.sum(G**3)
print(f"RESULT N={N} m={m}: dh={dh:+.8f} (1-m^2G0={1-m2*G0:+.8f})  F2_1={F2[1]:+.2e}  S0={S0:+.8f} L={L:.8f}  S1={S1:+.8f}"
      f"   chi: 11={chi11} 13={chi13} 31={chi31} 33={chi33}  [{time.time()-t0:.0f}s]", flush=True)
