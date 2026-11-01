import sys, pickle
import numpy as np
from qvertex3_num import greens, evalpoly
P = pickle.load(open('qvertex3_sym.pkl', 'rb')); P.update(pickle.load(open('qvertex3_delta.pkl', 'rb')))
for N, m in [(int(a), float(b)) for a, b in (s.split(':') for s in sys.argv[1:])]:
    G, G2, G3 = greens(N, m)
    T = {k: evalpoly(v, G) for k, v in P.items()}
    dh = 1 - m * m * G.flat[0]          # delta/eps from mass renormalisation
    cQ = 2.0                            # h1 = h2 = 0 value of c_Q
    tot = T['T1'] + T['T2'] + T['T5'] + dh * (T['T4'] + T['T6']) + cQ * (T['T3'] + dh * T['T7'])
    print(f"N={N} m={m}: " + " ".join(f"{k}={v:+.6f}" for k, v in sorted(T.items())), flush=True)
    print(f"      Gamma_Q^(3)/eps^3 at h=0 = {tot:+.10f}    m^2 G2(0) = {m*m*G2.flat[0]:.4e}  m^4 G3(0) = {m**4*G3.flat[0]:.4e}", flush=True)
