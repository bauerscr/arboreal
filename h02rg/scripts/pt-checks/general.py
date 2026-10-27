exec(open('oneloop.py').read().split("Kb=bare_kernel()")[0])
import sympy as sp
f=sp.Function('f')
# redefine bubble with general propagator what(k)=f(k.k)
src=open('oneloop.py').read().split("Kb=bare_kernel()")[0]
src=src.replace("f/= (kl.dot(kl))","f*= f_(kl.dot(kl))")
f_=sp.Function('f')
exec(src)
Kb=bare_kernel()
Kbub=bubble_kernel()
sub={}
for v in (p1,p2,q1):
    for c in v: sub[c]=eps*c
Ke=Kbub.subs(sub,simultaneous=True)
c2=sp.diff(Ke,eps,2).subs(eps,0)/2
s=sp.Symbol('s',positive=True)
c2=c2.subs({kx:kap*sp.cos(t),ky:kap*sp.sin(t)})
c2=sp.expand(sp.expand_trig(c2.doit()))
c2=c2.subs({kap**2*sp.sin(t)**2+kap**2*sp.cos(t)**2:kap**2})
c2=sp.simplify(c2)
A=sp.integrate(sp.expand(sp.simplify(c2)),(t,0,2*sp.pi))/(2*sp.pi)
A=sp.simplify(A)
print('A =',A)
print('A/Kb =',sp.simplify(A/Kb))
