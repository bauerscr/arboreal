# h02-lean

Lean 4 / Mathlib formalisation of `src/h02rg.tex` (the arboreal gas and the `H^{0|2}` model in
`d ≥ 3`) and of `summaries/h02uv-outline.tex` (the ultraviolet problem in `d = 2`).

## Layout

Each library is a `[[lean_lib]]` in `lakefile.toml`, with an umbrella file `X.lean` and sources in `X/`.
The libraries are in three groups (`docs/moves.md` records the file moves):

- top level (shared foundations):
  - `H02`: the forest identity and the spin representations.
  - `Grassmann`: Grassmann integration and norms.
  - `Loc`: localisation.
  - `FRD`: the finite range decomposition.
  - `DressedFRD`: the dressed decomposition (used for `d = 2`).
  - `Cont`: continuum analysis, not specific to the model: the asymptotic Arzelà–Ascoli theorem,
    the heat kernel and Green function `G_𝕋` on the torus, and the scaling limit of the lattice
    Green function (used for `d = 2`).
- `H02RG/` (`src/h02rg.tex`, `d ≥ 3`):
  - `Step`: the renormalisation group step.
  - `Flow`: the bulk flow.
  - `Suscept`: the susceptibility.
  - `Obs`: the observable flow.
  - `PtCorr`: the pointwise correlations.
  - `Psi4`: Theorems `thm:psi4` and `thm:psi4-full`.
  - `Ward`: the Ward identities and the results of Section 1.
  - `Main/` (library `H02RGMain`, modules `H02RG.Main.*`): the main theorems of
    `h02rg-lean.tex` (`H02RG.thm_forest_macro`, `thm_h02`, `thm_forests0`, `thm_forests`,
    `thm_all`), in `Main/Theorems.lean`.
- `H02UV/` (`summaries/h02uv-outline.tex`, `d = 2`):
  - `Step2`, `Flow2`: the step and the flow.
  - `Obs2`, `PtCorr2`: the observable flow and the correlations.
  - `Spin2`: the spin observables and the results of Section 1.
  - `Main/` (library `H02UVMain`, modules `H02UV.Main.*`): the main theorems of
    `h02uv-lean.tex` (`H02UV.thm_arboreal_multiscale`, `H02UV.thm_arboreal_limit_fixed`), in
    `Main/Theorems.lean`.

The libraries in `H02RG/` and `H02UV/` have `srcDir = "H02RG"` resp. `srcDir = "H02UV"` in
`lakefile.toml`, so library, module and declaration names do not contain the group directory:
the module `Step2.Flow.FlowThm` is the file `H02UV/Step2/Flow/FlowThm.lean`, and
`import Step.ZVK` refers to `H02RG/Step/ZVK.lean`. The exception are the two `Main` libraries
`H02RGMain` and `H02UVMain`: they have the default `srcDir = "."` (and `globs = ["H02RG.Main.+"]`
resp. `["H02UV.Main.+"]`), so their module names contain the group directory, e.g.
`H02RG.Main.Theorems` is the file `H02RG/Main/Theorems.lean`. Nothing imports them except the
audit scripts.

The four large `d = 2` libraries have one level of thematic subdirectories:

- `H02UV/Step2/`: `Map/` (the one-step map and its estimates), `Coup/` (coupling coordinates, Wick
  evaluation, `prop:C4b`), `D2/` (`prop:d2`), `Flow/` (`thm:flow` and the sharp flow; `Flow/FlowMaster.lean`: the
  master theorem `flow_master`, of which the flow theorems of the chain are corollaries),
  `FlowCont/`
  (continuity and differentiability of the flow data), `Lip/` (the Lipschitz layer), `Last/` (the
  steps `N − 2`, `N − 1` and the zero mode).
- `H02UV/Obs2/`: `Map/` (the map with sources and exact identities), `Est/` (one-step bounds with
  sources), `Loc/` (localisation), `Flow/` (the observable coupling flows), `Pair/` (coalescence and
  the pair chain).
- `H02UV/PtCorr2/`: `Zero/` (zero-mode integration, susceptibility, Ward identity), `Obs/` (the
  observable history), `Pair/`, `Last/` (last step, top coalescence), `Restart/`, `Cont/`.
- `H02UV/Spin2/`: `Multiscale/` (`thm:multiscale`, `sec:spin`, `thm:beta`), `Case2/`, `Gam/`,
  `Master/`, `H0/` (route (a1), the `h = 0` window), `Pair/`, `Restart/`, `Final/` (the final
  theorems), `Cont/` (equicontinuity and the continuum limit), `Macro/` (`thm:macro0`).

- Audit scripts. They are not built as modules (no umbrella imports them); run them with
  `lake env lean <path>` after `lake build`.
  - `Audit/H02RG.lean`, `Audit/H02UV.lean`: the audits of `h02rg-lean.tex` and `h02uv-lean.tex`:
    `#check` and `#print axioms` for the theorems stated there, and `#print` for the definitions
    used in their statements.
  - `H02RG/Audit.lean`, `H02UV/Audit.lean`: all main statements of `src/h02rg.tex` resp. the
    Lean-proved statements of `summaries/h02uv-outline.tex`, with the paper labels.
  - `<Lib>/Audit.lean`: per-library audits, in the library's directory (e.g. `FRD/Audit.lean`,
    `H02RG/Ward/Audit.lean`, `H02UV/Spin2/Audit.lean`; `H02/Audit.lean` audits the forest identity).
- `docs/moves.md`: the file moves of the phase-3 reorganisation and of the `H02RG/`/`H02UV/`
  grouping (old path → new path).
- `scripts/`: numerical and symbolic checks (see `scripts/README.md`).
- `h02rg-lean.tex`, `h02uv-lean.tex` (root): the human-readable statements of the Lean theorems for
  `d ≥ 3` (`H02RG.thm_forest_macro`, `H02RG.thm_all`) and for `d = 2` (`H02UV.thm_arboreal_limit_fixed`
  for the arboreal gas without the auxiliary mass `m²`). Both use the same format: `amsart` with
  `mymacros.sty`, an abstract, the definitions and theorems in ordinary mathematical language with
  no Lean names, and a final section "Lean formalisation" that gives, per theorem, the Lean
  declaration, its file, and how each notion of the statement is represented, plus the axioms.
- `src/h02rg.tex`: the `d ≥ 3` paper (`BCH24`): R. Bauerschmidt, N. Crawford, T. Helmuth,
  *Percolation transition for random forests in d ≥ 3*, Invent. Math. 237 (2024), 445–540,
  arXiv:2107.01878.
- `src/h02.tex`: R. Bauerschmidt, N. Crawford, T. Helmuth, A. Swan, *Random spanning forests and
  hyperbolic symmetry*, Comm. Math. Phys. 381 (2021), 1223–1261, arXiv:1912.04854 (the forest
  identity and the spin representations of library `H02`).
- `summaries/h02rg-erratum.tex`: erratum for `src/h02rg.tex` (`BCH24`): the corrections found during
  the formalisation, as a list.
- `summaries/h02uv-outline.tex`: the outline of the `d = 2` continuum limit, with the "Lean status"
  paragraphs that relate each Lean statement to the paper statement.
- `all.bib`, `mymacros.sty`: in the root. Compile from the root, e.g.
  `pdflatex -output-directory=<dir> h02rg-lean.tex`, then
  `(cd <dir> && BIBINPUTS=<root>: bibtex h02rg-lean)` and `pdflatex` twice more; the other `.tex` files
  likewise (e.g. `pdflatex -output-directory=<dir> summaries/h02uv-outline.tex`).

Expected axioms everywhere: `propext`, `Classical.choice`, `Quot.sound`.
