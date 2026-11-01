"""Per-scale one-loop beta coefficient for the Q coupling in d=4 with the h02rg FRD:
   g_{j+1} = g_j + beta_j g_j^2 + ...,  beta_j = 2 [ int w_{j+1}^2 - int w_j^2 ],   int = sum_y = int dk/(2pi)^4.
   Continuum prediction: beta_j -> 2 log(L)/(8 pi^2) = log(L)/(4 pi^2)."""
import sys, numpy as np, frd
exec(open('perscale2.py').read().split("m2 = 0.0")[0].split("\nd = 4\n")[1].replace("L = float","_L = float").replace("JMAX = int","_J = int"), globals())
d=4; L=float(sys.argv[1]); JMAX=int(sys.argv[2])
ws, wb = np.zeros_like(lam_small), np.zeros_like(lam_big); prev=0.0
print(f"L={L}: continuum log(L)/(4 pi^2) = {np.log(L)/(4*np.pi**2):.6f}")
for j in range(1, JMAX+1):
    lo, hi = (0.0 if j == 1 else L**(j-1)/2, L**j/2)
    ws = ws + frd.Chat(lam_small, 0.0, d, lo, hi); wb = wb + frd.Chat(lam_big, 0.0, d, lo, hi)
    I = integrate(ws**2, wb**2)
    print(f" j={j}: int w_j^2 = {I:.6f}   beta_(j-1) = 2*(increment) = {2*(I-prev):.6f}", flush=True); prev=I
