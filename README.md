# Results for the arboreal gas and the $H^{0|2}$ nonlinear sigma model in Lean

Contributors: Roland Bauerschmidt, Nick Crawford, Tyler Helmuth

This repository contains Lean formalised results for the arboreal gas
and the corresponding $H^{0|2}$ nonlinear sigma model.
The results were obtained in different ways as discussed in the sections below.
We expect to add further results, and human-readable expositions, in the future.

## Repository layout

- `h02rg/`: the Lean formalisation of the first two results (Lean library and documents; see `h02rg/README.md`):
  - Percolation transition in $d \geq 3$ (`h02rg/h02rg-lean.tex`, Lean in `h02rg/H02RG/`), and
  - Asymptotic freedom in $d = 2$ (`h02rg/h02uv-lean.tex`, Lean in `h02rg/H02UV/`).
  - Both share the libraries at the top level of `h02rg/`.
- `h02expdec/`: the Lean formalisation of exponential decay in $d = 2$ (`h02expdec/h02expdec-lean.tex`, Lean in `h02expdec/ArborealDecay/`; see `h02expdec/README.md`).

Each directory is a separate Lake project. Build it and run its audit files from inside that directory, e.g. `cd h02rg && lake build && lake env lean Audit/H02RG.lean`.

## Percolation transition for random spanning forests in $d \geq 3$

The Lean formalisation verifies the results from the human-written paper `h02rg/src/h02rg.tex`, which is [arXiv:2107.01878](https://arxiv.org/abs/2107.01878). It was formalised by Claude with essentially zero input.
Small corrections found along the way are documented in `h02rg/summaries/h02rg-erratum.tex`.

### Sample result (Theorem 1.1 of the paper)
For the arboreal gas on the torus $\Lambda_N = (\mathbb{Z}/L^N\mathbb{Z})^d$ with $d \geq 3$ and $L$ odd and large,
there are $\beta_0 > 0$ and $\kappa \in (0,1]$ such that for all $\beta \geq \beta_0$, $N \geq 2$ and $x \in \Lambda_N \setminus \{0\}$,
```math
P^{\Lambda_N}_{\beta}[0\leftrightarrow x] = \theta(\beta)^2 + \frac{2c_1(\beta)}{\beta |x|^{d-2}} + O\Big(\frac{1}{\beta|x|^{d-2+\kappa}}\Big) + O\Big(\frac{1}{\beta L^{\kappa N}}\Big),
```
where: $\theta(\beta) = 1 + O(1/\beta)$ is the percolation probability, i.e., the limit of $P_{\beta,h}[0 \leftrightarrow \mathfrak{g}]$ as first $N \to \infty$, then $h \downarrow 0$, with a ghost vertex $\mathfrak{g}$;
$c_1(\beta) = c_d + O(1/\beta)$; and $c_d$ is the constant of the lattice Green function, $(-\Delta_{\mathbb{Z}^d})^{-1}(0,x) \sim c_d |x|^{2-d}$.

See `h02rg/h02rg-lean.tex` for the full statements, including those for the $H^{0|2}$ model and the truncated connection probabilities.

### Lean theorems

The theorems of `h02rg/h02rg-lean.tex`, all in `h02rg/H02RG/Main/Theorems.lean`:

- `H02RG.thm_forest_macro`: the connection probability on the torus at $h = 0$ (the sample result above).
- `H02RG.thm_h02`: the $H^{0|2}$ model, limits $N \to \infty$ then $h \downarrow 0$: magnetisation, two-point function, truncated $z$-$z$ and spin-spin correlations.
- `H02RG.thm_forests0`: existence of the percolation probability $\theta(\beta)$.
- `H02RG.thm_forests`: the truncated connection probabilities.
- `H02RG.thm_all`: all of the above with one shared set of constants, together with the identities $\zeta = \theta^2$, $c_2\theta^2/c_1^2 = 1$, $c_0 = 2c_1$ and $c_0 = 2c_d$.

Check with `lake env lean Audit/H02RG.lean` in `h02rg/` (statements, definitions used in them, and axioms: only `propext`, `Classical.choice`, `Quot.sound`).

## Asymptotic freedom for the arboreal gas in $d = 2$

The Lean formalisation constructs the continuum limit of the arboreal gas two-point function on the two-dimensional torus.
The Lean formalisation was obtained by starting from the formalisation of the $d \geq 3$ result discussed above, together with some additional input.

One of the main new ingredients of the renormalisation group analysis is a dressed finite-range decomposition which handles the infinite field strength renormalisation and the second-order renormalisation group flow.

In the future, we plan to post an exposition of these results, possibly along with further results that can be obtained from this method. These will refer to the Lean version, but with our understanding also being guided by more than a hundred pages of human-written notes on this problem which we wrote beforehand. We do not expect our prior work to be published in the originally anticipated way.

### Sample result

For the arboreal gas on the discretized unit torus $\mathbb{T}_\epsilon = (\epsilon \mathbb{Z}/\mathbb{Z})^2 \cong (\mathbb{Z}/L^N\mathbb{Z})^2$, $\epsilon = L^{-N}$ ($L$ fixed and large),
for any large $\beta_R > 0$ there is a choice of $\beta_\epsilon$ with
```math
\beta_\epsilon = \frac{3}{2\pi} \log \frac{1}{\epsilon} + O\Big(\log\log\frac{1}{\epsilon}\Big)
```
and a continuous function $G_{\beta_R}: \mathbb{T}^2 \setminus \{0\} \to \mathbb{R}$ such that, along a subsequence $\epsilon \to 0$,
```math
\Big(\frac{\beta_\epsilon}{\beta_R}\Big)^{2/3} \, P^{\mathbb{T}_\epsilon}_{\beta_\epsilon}[0\leftrightarrow x] \to G_{\beta_R}(x)
```
uniformly on compact subsets of $\mathbb{T}^2 \setminus \{0\}$ (with $x$ rounded to the nearest point of $\mathbb{T}_\epsilon$).
The limit $G_{\beta_R}$ satisfies, as $x \to 0$,
```math
G_{\beta_R}(x) = \Big(\frac{3}{2\pi\beta_R} \log \frac{1}{|x|}\Big)^{2/3} \Big(1 + O\Big(\frac{\log \log (1/|x|)}{\log (1/|x|)}\Big)\Big).
```
See `h02rg/h02uv-lean.tex` for the full statement.

### Lean theorems

The theorems of `h02rg/h02uv-lean.tex`, in `h02rg/H02UV/Main/Theorems.lean`:

- `H02UV.thm_arboreal_limit_fixed`: the continuum limit at fixed $\beta_R$ (the sample result above): the choice of $\beta_N=\beta_\epsilon$ with its asymptotics, equicontinuity, the subsequential limit $G$ and its short-distance behaviour.
- `H02UV.thm_arboreal_multiscale`: the statement for each fixed $N$: the bound on $\beta_\epsilon$, the multiscale formula for $P_{\beta_\epsilon}[0 \leftrightarrow x]$ and its short-distance bounds.

Check with `lake env lean Audit/H02UV.lean` in `h02rg/` (statements, definitions used in them, and axioms: only `propext`, `Classical.choice`, `Quot.sound`).

## Exponential decay for the arboreal gas in $d = 2$

It is proved that connection probabilities of the arboreal gas on $\mathbb{Z}^2$ decay exponentially. The proof was found by GPT-6
and the Lean formalisation was done using Claude. For the prompts, see `h02expdec/h02expdec.tex`.

### Main result

For every $\beta \geq 0$ there is $c > 0$ such that for every finite $\Lambda \subset \mathbb{Z}^2$, every symmetric nonnegative edge weight $w$ on $\Lambda$ with $w_{uv} \le \beta$ and $w_{uv} = 0$ unless $u, v$ are nearest neighbours, and all $x, y \in \Lambda$,
```math
P^\Lambda_{w}[x \leftrightarrow y] \leq 2e^{-c\|x-y\|_\infty}.
```
The same bound holds on the tori $(\mathbb{Z}/L\mathbb{Z})^2$, uniformly in $L \geq 1$, with the toroidal $\ell^\infty$ distance. In particular, for constant weight $\beta$ on the torus, $P_\beta[0 \leftrightarrow x] \leq C e^{-c|x|}$ with the toroidal Euclidean distance $|x|$.
See `h02expdec/h02expdec-lean.tex` for the full statements.

### Lean theorems

The theorems of `h02expdec/h02expdec-lean.tex` (namespace `ArborealDecay`):

- `expDecay_finite` (`h02expdec/ArborealDecay/Frozen/ExpDecayFinite.lean`): finite subsets of $\mathbb{Z}^2$ (the main result above).
- `expDecay_torus` (`h02expdec/ArborealDecay/Frozen/ExpDecayTorus.lean`): weighted tori, uniformly in $L$.
- `expDecay_torus_eucl` (`h02expdec/ArborealDecay/Frozen/ExpDecayTorusEucl.lean`): constant weight $\beta$ on the torus, Euclidean distance.

Check with `lake env lean Audit/ExpDecay.lean` in `h02expdec/` (statements, definitions used in them, and axioms: only `propext`, `Classical.choice`, `Quot.sound`).

