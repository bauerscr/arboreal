import mpmath as mp
mp.mp.dps = 60
def g0(x):
    s = mp.mpf(1)/4 - x*x
    return mp.e**(-1/s) if s > 0 else mp.mpf(0)
def ghat(xi):
    xi = mp.mpf(xi)
    n = max(8, int(4*xi)+8)
    pts = [mp.mpf(-1)/2 + mp.mpf(k)/n for k in range(n+1)]
    return mp.quad(lambda x: g0(x)*mp.cos(2*mp.pi*xi*x), pts)
for xi in [0,1,2,5,10,20,40,80,120,160]:
    v = ghat(xi)
    print(xi, mp.nstr(v,8), mp.nstr(mp.log(abs(v))/mp.sqrt(xi) if xi>0 and v!=0 else 0,6))
