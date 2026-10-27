# h02-expdecay

Lean 4 / Mathlib formalisation of `h02expdec.tex` (exponential decay of connection probabilities
for the arboreal gas in `d = 2`, for every `β`). The proof is unconditional: the cited results of
BCHS, BHS, Borcea–Brändén and Borcea–Brändén–Liggett are proved in Lean or replaced by proved
elementary arguments. 

Lean `v4.34.1`, Mathlib `d13f23b`. Build with `lake build`.

## Layout

There is one `[[lean_lib]]`, `ArborealDecay`, with the umbrella `ArborealDecay.lean` and sources in
`ArborealDecay/`. Every file is a Lean module (`module`, `public import`). The library has three
layers:

- `ArborealDecay/Frozen/`: the author-approved statements, one public declaration per file
  (`FROZEN_MANIFEST.json` records them with their hashes). The main theorems are
  `ExpDecayFinite.lean`, `ExpDecayTorus.lean` and `ExpDecayTorusEucl.lean`; the other files are
  the definitions used in the statements and the frozen intermediate results.
- `ArborealDecay/Provider/`: the proofs of the frozen theorems, from the libraries below.
- The libraries, each with an umbrella `ArborealDecay/<Area>.lean`:
  - Foundations:
    - `H02`, `Grassmann`: the `ℍ^{0|2}` model and Grassmann algebra (ported from `h02-lean`).
    - `MatrixForest`: the weighted matrix-forest theorem.
    - `Forest`: spanning forests.
    - `Lattice`: geometry of `ℤ²` and `(ℤ/Lℤ)²`, boxes and shells, the logarithmic cutoff.
    - `Gaussian`: finite-dimensional Gaussian integrals.
    - `Conductance`: effective conductance, the Dirichlet principle.
  - Stability:
    - `Stability`: real stable multi-affine polynomials.
    - `ForestPoly`: the forest polynomial, the operator identity and its real stability.
    - `Separator`: the stable separator lemma.
    - `Wiring`: separator-wiring monotonicity.
  - Supersymmetry:
    - `Super`: superanalysis kernel, localisation (BCHS Thm 2.8).
    - `Horo`: horospherical coordinates (BCHS Prop 2.9).
    - `BCHS`: the identities (A) and (C).
    - `TLaw`: the pinned `t`-law and BCHS Lemma 4.1.
    - `Pinned`: the `ℍ^{0|2}` pinned Green-event identity.
    - `CondComb`: the combinatorial half of the conductance identity.
    - `Annulus`: the wired annulus bound.
  - Forest surgery:
    - `Surgery`: contraction and the related forest identities.
    - `SimonLieb`: incident-edge negative correlation, two rooted trees, the Simon–Lieb
      inequality.
  - Assembly:
    - `Superpoly`: the superpolynomial bound from nested separators.
    - `ExpDecay`: the exponential iteration.
    - `Bridge`: identifies the frozen definitions with the library definitions.
    - `Final`: the final assembly of the frozen theorems.

- `Audit/ExpDecay.lean`: the audit of `h02expdec-lean.tex`. It `#check`s the three main theorems,
  prints their axioms and the definitions used in their statements. It is not built as part of
  the library; run it with `lake env lean Audit/ExpDecay.lean` after `lake build`.
- `scripts/`: `check_lean_modules.py` (module discipline), `check_frozen_anchors.py` (frozen files
  against `FROZEN_MANIFEST.json`), `proof_depgraph.py` (the dependency graph).
- `h02expdec-lean.tex` (root): the human-readable statements of the three main theorems
  (`ArborealDecay.expDecay_finite`, `expDecay_torus`, `expDecay_torus_eucl`) and of the definitions
  in them, with the Lean names.
- `h02expdec.tex` (root, with `fig-nested-shells.tex`): the note.
- `refs/`: pinned sources of the cited papers (BB, BBL, BCHS, BHS).
- Compile the tex files from the root, e.g. `pdflatex -output-directory=<dir> h02expdec.tex` (twice;
  the bibliography is inline).

Expected axioms everywhere: `propext`, `Classical.choice`, `Quot.sound`.
