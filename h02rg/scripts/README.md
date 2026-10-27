# Checks for frd-redecompose.tex and h02uv-outline.tex

Run each script from its own directory.

## pt-checks/: one-loop Wick contractions in momentum space (sympy)

- `oneloop.py`: the bubble with two quartic vertices M = psi psibar (grad psi)(grad psibar),
  propagator 1/k^2. Prints the angular-averaged local coefficient divided by the bare
  vertex kernel. The result is 1, i.e. log L/(2 pi) per step.
- `general.py`: the same with a general radial propagator f(|k|^2). The coefficient
  density is -f (s^3 f')'.
- `obs.py`, `obs_gen.py`: the vertex of the observable sigma psibar psi with M. The
  coefficient is +1 (1/k^2 propagator); in general it is |k|^2 f^2, i.e. (w, -Delta w).
- `masscross.py`: Cov(psi psibar, M) = 4 Chat(0) M.

## frd-numerics/: Assumption 2.4 (non-degeneracy) for the Lean decomposition (mpmath)

- `tab.py`: tabulates psi = ghat^2 on [0,60]. Slow; it writes psi.npy and xs.npy.
- `checkP.py`: G^0, G, F and D.
- `run1.py`–`run4.py`: the normalisation check, the tail ratio, and min c_P.
- `asy.py`: compares ghat with its saddle-point asymptotics.
