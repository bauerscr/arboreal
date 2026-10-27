import mpmath as mp, numpy as np, math, sys
mp.mp.dps=30
xs=np.load("xs.npy"); psi=[mp.mpf(s) for s in np.load("psi.npy")]
h=xs[1]-xs[0]; n=len(xs)
f=[mp.mpf(x)*p for x,p in zip(xs,psi)]      # sigma*psi
# cumulative trapezoid (Simpson would be better; h small)
Phi=[mp.mpf(0)]
for i in range(1,n): Phi.append(Phi[-1]+(f[i-1]+f[i])*h/2)
c0=Phi[-1]
Psi=[c0-p for p in Phi]
# right-cumulative directly for accuracy in tails
Psi=[mp.mpf(0)]*n
for i in range(n-2,-1,-1): Psi[i]=Psi[i+1]+(f[i]+f[i+1])*h/2
c0=Psi[0]
f0=mp.mpf(sys.argv[1]) if len(sys.argv)>1 else None
PhiA=np.array([float(p) for p in Phi]); PsiA=np.array([float(p) for p in Psi])
cc=2*math.pi**2*float(c0)
def interp(arr,y,logscale):
    if y>=xs[-1]: return 0.0 if logscale else arr[-1]
    k=int(y/h); t=(y-xs[k])/h
    a,b=arr[k],arr[k+1]
    if logscale and a>0 and b>0: return math.exp((1-t)*math.log(a)+t*math.log(b))
    return (1-t)*a+t*b
def Psi1(y): return interp(PsiA,y,True)
def Phi1(y): return interp(PhiA,y,False) if y<xs[-1] else float(c0)
return_A=None
def setup(f0v):
    global AA; AA=2/3*f0v/cc
def xu(u): return 2*math.asin(math.sqrt(u/2))/(2*math.pi)
def G0(S,u):
    if S<=1: return 1.0
    x=xu(u); s=0.0
    for k in range(-80,81):
        a=abs(x+k)
        if a*S>xs[-1]: continue
        s+=Psi1(S*a)/a**2
    val=u/cc*s
    if S<2: val+=u*AA*(4-S*S)/2
    return val
def dF0(S1,S2,u):  # F0(S2)-F0(S1) = u int_{S1}^{S2} tau P0, S1<S2
    S1=max(S1,1.0)
    if S2<=S1: return 0.0
    x=xu(u); s=0.0
    for k in range(-80,81):
        a=abs(x+k)
        lo,hi=S1*a,S2*a
        if lo>xs[-1]: continue
        if lo<1: s+=(Phi1(hi)-Phi1(lo))/a**2
        else: s+=(Psi1(lo)-Psi1(hi))/a**2
    val=u/cc*s
    lo,hi=S1,min(S2,2.0)
    if hi>lo: val+=u*AA*(hi*hi-lo*lo)/2
    return val
pi_=[math.exp(-1)/math.factorial(i) for i in range(80)]
def G(T,u): return sum(pi_[i]*G0(T/2**i,u) for i in range(80))
def F(T,u): return sum(pi_[i]*dF0(1.0,T/2**i,u) for i in range(80))
def D(T,L,u): return sum(pi_[i]*dF0(T/2**i,L*T/2**i,u) for i in range(80))
