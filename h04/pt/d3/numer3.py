"""Numerator N of the reduced Ward identity along (dh = 1 - m^2 G0, cQ = 2), d=3.
N_psi = <P> - eps<Q> - (chi31/chi11)(1 - eps<S> - eps^2<Q>),  and Ward predicts N_psi = -eps^2 * 2h2 * Sigma_psi,
2 eps^2 h2 = eps m^2 + eps^2 (1 + dh - cQ)  =>  N_psi = -(eps m^2 + eps^2(dh-1)) Sigma_psi."""
import sys, numpy as np, ward_check as WC
from qvertex3_num import greens
N, m = int(sys.argv[1]), float(sys.argv[2]); G,_,_ = greens(N, m); m2=m*m; G0=G.flat[0]
p = (1 - m2*G0, 2.0)
S = WC.series_obs(WC.obs_S, 0, 1, p, G, bgmax=0); P = WC.series_obs(WC.obs_P, 0, 1, p, G, bgmax=0)
Q = WC.series_obs(WC.obs_Q, 0, 0, p, G, bgmax=0)
F2 = WC.series_obs(None, 0b0011, 1, p, G, bgmax=2); d31 = WC.series_obs(WC.obs_O3, 0b0001, 1, p, G, bgmax=1)
d13 = WC.series_obs(WC.obs_O13, 0b0010, 1, p, G, bgmax=1); c33 = WC.series_obs(WC.obs_O3, 0, 1, p, G, bgmax=0, extra=WC.obs_O13)
s31=np.sign(d31[0]/G0); s13=np.sign(d13[0]/G0)
chi11=np.array([1/m2, -F2[1]/m2**2]); chi31=s31*d31/m2; chi13=s13*d13/m2
r = np.array([chi31[0]/chi11[0], chi31[1]/chi11[0] - chi31[0]*chi11[1]/chi11[0]**2])     # chi31/chi11
N0 = P[0] - r[0]; N1 = P[1] - Q[0] - r[1] + r[0]*S[0]
Sig0 = c33[0] - chi31[0]*chi13[0]/chi11[0]
print(f"m={m}: <P>0={P[0]:.6f} r0={r[0]:.6f}  N_psi^(0)={N0:+.2e}   N_psi^(1)={N1:+.8f}   predicted -m^2*Sigma0 = {-m2*Sig0:+.8f}   (Sigma0={Sig0:+.6f})")
