import mpmath as mp
mp.mp.dps=40
g=lambda x: mp.e**(-1/(mp.mpf(1)/4-x*x))
def gh(xi):
    f=lambda x: g(x)*mp.cos(2*mp.pi*x*xi)
    pts=[mp.mpf(-1)/2+k/(mp.mpf(4)*xi+8) for k in range(int(4*xi+8)+1)]
    return 2*mp.quad(f,[p for p in pts if p>=0] if False else [mp.mpf(k)/(2*(4*xi+8)) for k in range(int(4*xi+8)+1)])
c=mp.e**-1*mp.sqrt(mp.pi)*(2*mp.pi)**(-0.75)
for xi in [20,40,60,80,100,120,160]:
    v=gh(mp.mpf(xi))
    env=2*c*xi**(-0.75)*mp.e**(-2*mp.sqrt(mp.pi*xi))
    ph=mp.pi*xi-2*mp.sqrt(mp.pi*xi)
    print(xi, mp.nstr(v,6), mp.nstr(v/env,5), [mp.nstr(mp.cos(ph+t),5) for t in (3*mp.pi/8,-3*mp.pi/8,mp.pi/8,-mp.pi/8)])
