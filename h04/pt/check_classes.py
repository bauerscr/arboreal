import itertools, pickle, time
import wick as W
from qvertex3_lib import *
from qvertex3_num import greens, evalpoly
G,_,_ = greens(8, 0.9)
P = pickle.load(open('qvertex3_sym.pkl','rb'))
t=time.time(); brute=0.0
for nu, rho in itertools.product(range(D), range(D)):   # first direction fixed to 0, times D
    alg = W.Alg()
    c = cum3(alg, bS2(alg, O, 0), bS2(alg, Y, nu), bS2(alg, Wt, rho))
    brute += D * evalpoly(c, G) / 48.0
print(f"T5 class formula = {evalpoly(P['T5'], G):+.12f}   brute-force directions = {brute:+.12f}   ({time.time()-t:.0f}s)")
# same for T2 (b x psi6) 
brute=0.0
for nu in range(D):
    alg=W.Alg(); brute += D*evalpoly(cum2(alg, bS2(alg,O,0), v6(alg,Y,nu)),G)/2.0
print(f"T2 class formula = {evalpoly(P['T2'], G):+.12f}   brute-force directions = {brute:+.12f}")
