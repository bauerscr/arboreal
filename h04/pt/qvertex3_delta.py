"""O(eps^3) contributions with one mass-counterterm vertex  delta * S(psi+phi)  (per site, coefficient of delta):
  T4 = sum_y sum_mu cum[(gradS gradQ)_0, S_y]                          (x eps^2 delta)
  T7 = sum_y cum[Q_0, S_y]                                              (x c_Q eps^2 delta)
  T6 = (1/8) sum_{y,w} sum_{mu,nu} cum[(grad_mu S_0)^2, (grad_nu S_y)^2, S_w]   (x eps^2 delta)
"""
import pickle, time
import wick as W
from qvertex3_lib import *
out = {}
t0 = time.time()
alg = W.Alg()
out['T4'] = scale_poly(cum2(alg, v6(alg, O, 0), W.S(alg, Y)), D)
alg = W.Alg()
out['T7'] = cum2(alg, W.Q(alg, O), W.S(alg, Y))
T6 = {}
for (mu, nu, mult) in [(0, 0, D), (0, 1, D * (D - 1))]:
    alg = W.Alg()
    T6 = addp(T6, scale_poly(cum3(alg, bS2(alg, O, mu), bS2(alg, Y, nu), W.S(alg, Wt)), mult / 8.0))
out['T6'] = T6
print({k: len(v) for k, v in out.items()}, f'{time.time()-t0:.1f}s')
pickle.dump(out, open('qvertex3_delta.pkl', 'wb'))
