# Duplication audit (2026-10-26, commit `35c5993`)

**Status (2026-10-26, later the same day).** Paths are now under `H02RG/` and `H02UV/` (see
`docs/moves.md`). C15: 47 of the 326 dead declarations deleted (the other 279 are named in the
per-library `<Lib>/Audit.lean` files or are `rfl` simp lemmas). C1: `flow_master`
(`H02UV/Step2/Flow/FlowMaster.lean`) with 10 of the 11 variants as corollaries (`flow_range_hyp`
kept). Details in `Log.md`. The figures below are those of the audit.

This audit is analysis only: no `.lean` file was changed. Its purpose is to find the duplicated code
in the `d = 2` libraries (`Step2`, `Obs2`, `PtCorr2`, `Flow2`, `Spin2`) and to propose
generalisations that would make the code base a better starting point for later work.

## 0. Method and reproducibility

All scratch files are in `/home/roland/.claude/jobs/f52f9c7e/tmp/dup_work/` and `.../tmp/dup_cl/`.
Every `lake env lean` call was serialised with `flock .../tmp/lean.lock`.

| Step | Tool | Output |
|---|---|---|
| Declaration dump (14 358 declarations in Step, Step2, Flow, Flow2, Obs, Obs2, PtCorr, PtCorr2, Spin2) | `dup_work/dump.lean` (MetaM): name, module, kind, source range, the project constants used in the value, a token sequence of the type, and the pretty-printed type (`pp.fullNames`) | `dump.tsv` |
| Cross-library statement similarity, each `X2` declaration against every declaration of the base library | `match.py`, `pairs.py`, `pairs2.py`: tokens normalised (`Step2.→Step.`, …, `Complex→Real`, name suffixes `2 C D X U Gen Z R E S N F T B K L ′ ₂` stripped, instances dropped); Jaccard prefilter, then `difflib` ratio; `twins*.py` keeps pairs with ratio ≥ 0.75 and proof-constant Jaccard ≥ 0.4 | `pairs.tsv`, `pairsX.tsv`, `twins.tsv`, `twinsX.tsv` |
| Statement similarity inside a library (across modules) | `intra.py`, `clus.py` (union-find at ratio ≥ 0.9 and proof-constant Jaccard ≥ 0.6) | `intra.tsv` |
| Text level (the main measure) | `textdup.py`, `textattr.py`, `fpairs.py`: comment-free code lines of at least 35 characters, normalised (whitespace, library prefix, the `O`/`OU`/`OAB` observable suffix); a line counts as *shared* if it occurs in 2–12 files | `text.pkl`, `textres.pkl` |
| Closure | `dup_cl/scan.lean` + `closure.py` (the pruning tool), roots = the names in `Audit/H02RG.lean` and `Audit/H02UV.lean` + every `\texttt{…}` token in `*.tex`, `src/`, `summaries/` (2 814 tokens, 24 tex files); a second run (`dup_cl/aud/`) uses only the 46 Audit names | `dup_cl/dead.tsv`, `dup_cl/aud/texonly.tsv`, `dup_cl/aud/texroots.tsv` |

How to read the numbers:
- **file lines**: `wc -l`.
- **code lines**: the filtered lines above. File lines are about 1.7–2 times the code lines.
- **decl lines**: the `l0..l1` range of the declaration, statement included.
- The base libraries have a background shared-line rate of 15–20% (repeated binder lines, `refine`
  boilerplate). The 2-libraries have 41–53%. "Removable" estimates below are corrected for this
  background.

## 1. Headline findings

1. **Almost all of the duplication is *inside* the 2-libraries, not between a 2-library and its base
   library.**

   Shared code lines, split by where the other copy lives:

   | Library | in the same subdirectory | in another subdirectory | in the base library | in another library |
   |---|---|---|---|---|
   | Step2 | 11 874 | 6 395 | 651 (`Step`) | 1 070 (`Obs2`), 486 (`Spin2`) |
   | Obs2 | 7 284 | 624 | 469 (`Obs`) | 1 291 (`Step2`) |
   | PtCorr2 | 5 452 | 2 086 | ≈0 | — |
   | Flow2 | 1 590 | — | 5 | — |
   | Spin2 | 24 221 | 3 955 | — | — |

   The internal copies are:
   - *versioned theorem chains*: a theorem proof copied to add one more ε-condition or one more
     export;
   - *hypothesis variants*: `ValidAt` changed to `ValidAtL`, `j + 2 < N` to `j + 1 < N`,
     `Admissible` to the `InD3` window, fixed weights to arbitrary weights, small transients to
     large ones;
   - *sector copies*: the observable sector `O` copied to `OU` and `OAB`.
2. **The base↔2 "mirror" is conceptual, not textual.**
   - `Step2` uses 331 `Step` constants, but mostly the infrastructure (`Step.Ev/EvR/Act/Knorm/bmap`).
     The step map itself was re-proved: `Step.Knext` (real `C`, concrete `e^{-V}`) and
     `Step2.gKnext` (complex `C`, generic block factors `Ib Ip J`) are parallel definitions with no
     bridge lemma.
   - `PtCorr2` uses 5 `PtCorr` constants (9 declarations).
   - `Flow2` uses **no** `Flow` constant: the finite horizon and the marginal coupling make it new
     content.
   - Direct lemma twins between a base library and its 2-library come to only about 1.3k decl
     lines. The best ones are listed in §5.
3. **Third copies.** The algebraic RG map exists three times:
   - `Step.Knext`;
   - `Obs.Gen.KnextG`, generic in the algebra (`RGAlg R R2`, `RGIngr`, with the bridge
     `H02RG/Obs/GenericBridge.lean`);
   - `Step2.gKnext`, generic in the block factors (`H02UV/Step2/Map/Gen.lean`, 359 lines, which re-proves
     `Ktil_union`, `sum_Sec_eq_sum_G0`, …).

   `H02UV/Obs2/Map/ExactStep.lean` adds a fourth set of `…W` copies of `Obs.Gen` (`KtermG_gjoinW`,
   `KnextG_unionW`, `SuppHypW`), because `SuppHyp` was too strong.

   The estimate layer exists twice: Log.md l.2383/2447 says `H02UV/Obs2/Est` is a copy of the `H02UV/Step2/Map`
   Cauchy chain (about 10k lines) "because the bulk proofs are not generic in the algebra".
4. **About 50k decl lines of the 2-libraries are reachable only from tex citations, not from the
   46 Audit statements.**

   | Library | tex-only decl lines |
   |---|---|
   | Spin2 | 21 722 |
   | Step2 | 14 813 |
   | Obs2 | 6 732 |
   | PtCorr2 | 5 391 |
   | Flow2 | 2 070 |

   Of the 585 tex-cited roots in this set, 527 are cited only from `summaries/h02uv-outline.tex`
   ("Lean status" paragraphs). These are the superseded chains. They are the main reason the
   copies cannot simply be deleted.
5. **Dead weight under the full root set (Audit + all tex): 326 declarations, 4 215 decl lines.**
   It is small because the earlier pruning already removed most of it. Details in §6.

## 2. Summary table: lines of each 2-library by cause

Causes:
- **(a)** a parameter that was fixed in the base became variable (complex covariance, `Z_j`/`ζ`
  dressing, generic block factors, finite horizon).
- **(b)** a hypothesis was strengthened or weakened (variant chains).
- **(c)** `d` was fixed to 2.
- **(d)** a proof was re-done because the base statement was not general enough (concrete algebra
  or hypothesis bundle, constants or ε chosen inside the proof).
- **(e)** genuinely new content.

The attribution is by module/file cluster. It uses the text measure and the "copy of" docstrings
(files that declare themselves copies: Step2 18 files/9.2k lines, Obs2 40/11.1k, PtCorr2 32/9.2k,
Spin2 47/16.0k).

| Library (file lines) | (a) | (b) | (c) | (d) | (e) | shared code lines (internal) | est. removable (raw / background-corrected) | tex-only decl lines | dead decl lines |
|---|---|---|---|---|---|---|---|---|---|
| **Step2** (80 619) | 21.1k: `Map` + `Coup` (mirror of `Step` with complex `C` and generic `Ib/Ip/J`) | 6.9k: `Last` copies of `Map`/`Lip`/`Flow` with `j+1<N`, `ValidAtL`, `L>68` (15 files) | ≈0 (646 declarations fix `d = 2`, but none duplicates a `d`-general one) | 10.0k: `Flow` theorem chain (22 files, 9.2k) + `Map/Gen` third copy (0.8k) | 42.6k: `D2` 15.8k, `Lip` 11.8k, `FlowCont` 2.7k, rest of `Flow` 7.4k, rest of `Last` 4.9k | 18.3k | 15.9k / ≈9.7k | 14 813 | 270 |
| **Obs2** (45 540) | 10.1k: `Loc` 4.0k, `Map` 6.1k (amended algebra with complex/dressed `C`) | 3.2k: `RestartRec`/`RestartRec2`, `MemGronwall`/`MemGronwall2`, `Coal`/`CoalR` | ≈0 (153 declarations) | 16.1k: `Est` = copy of the `H02UV/Step2/Map` chain on `OE` (≈9.2k) + sector copies `OU`/`OAB` (32 files, 6.9k) | 16.1k: `Flow`, `Pair` | 7.9k (+1.3k with Step2) | 8.7k / ≈5.2k | 6 732 | 136 |
| **PtCorr2** (38 283) | 4.9k: `Zero` (zero mode with complex `t`, Ward; mirrors `PtCorr.ZNN`/`Bridge` without reuse) | 8.3k: `ObsHist*`/`ProdBd*` family (14 files, 5.8k) + `Restart`/`Cont` top/wire variants (≈2.5k) | ≈0 (890 declarations fix `d = 2`) | — | 25.1k | 7.5k | 6.7k / ≈3.8k | 5 391 | 44 |
| **Flow2** (7 491) | (finite horizon: the whole library is (a)/(e) relative to `Flow`, with no reuse) | 4.3k: `FixedR*`/`Range*`/`Complete*` chain (17 files) | — | — | 3.2k | 1.6k | 1.6k / ≈1.0k | 2 070 | 683 |
| **Spin2** (90 908) | — | ≈45k in variant chains: `Pair` chains 15.2k (38 files), `Cont` chains 21.8k (89 files), `Final`/`Restart`/`Case2` ≈8k | (`d = 2` throughout; not a duplication cause) | — | ≈46k | 28.2k | 23.1k / ≈15.3k | 21 722 | 1 254 |
| **Total** (262 841) | ≈36k | ≈68k | ≈0 | ≈26k | ≈133k | 63.5k | ≈56k / ≈35k | 50 728 | 2 387 |

"Est. removable" is the text-level upper bound: half of the shared lines, converted to file lines.
The corrected column subtracts the 18% background. Reaching it requires the generalisations of §3.
It cannot be obtained by deletion alone, because the tex citations keep the old versions.

## 3. Duplicate clusters of type (a)/(b)/(d), with proposals

All size figures are from `fpairs.py`, the closure, and `wc`. "Tex-cited" counts the declarations
of the cluster that resolve from a `\texttt` token. "Audit" counts names in `Audit/H02*.lean`.

### C1. Step2 flow-theorem chain (d) — 22 files, 9 214 lines, 24 tex-cited, 0 audit

Files: `H02UV/Step2/Flow/` `FlowThm`, `FlowSharp1–3`, `FlowRange(Hyp)`, `FlowFinalZ(Hyp, Aux)`,
`ZetaSharpHypX`, `FlowComplete(Hyp, BandHyp, 2, 2Hyp, 2X, Band)`, `FlowMasterHypL(Z)`, `FlowHor2Thm`,
`FlowHor2Aux`, `FlowHorizon`.

Each file copies the proof of `thm_flow`, with:
- one more smallness condition on ε, `ρ` or `L₀`;
- or one more export (`ZeroTOk`, `MonoHyp`, `HDiff`, `ValidAtL`, …).

Log.md documents this at l.2031, 2097, 2159, 2249, 2284, 2489 and 2507. The pairwise overlap is
400–510 shared code lines, for example `FlowMasterHypL`/`FlowMasterHypLZ` (diff 196 lines out of
764/898) and `FlowCompleteHyp`/`FlowCompleteBandHyp`.

The cause is that the choice of `(ℓ, A, ρ, ε, …)` is made inside the proof, and the result is a
`∃ …, c₁ ∧ c₂ ∧ … ∧ ∀ N R Nh, …` conjunction.

Proposal (new file `H02UV/Step2/Flow/FlowMaster.lean`):

```lean
structure FlowConsts (L : ℕ) where ℓ A ρ ϑ κ cg cm cT ε Ke : ℝ  -- + positivity fields
structure FlowExport (L : ℕ) (k : FlowConsts L) (N : ℕ) (R : RGPar 2 L N) (Nh : ℕ) : Prop where
  hhyp : Hist.HHyp (rgData R) (L^2) (betaL L) (1/2) k.κ k.cg k.cm k.cT Nh _ _ k.ε
  valid : ∀ j < Nh, ValidAt R j
  mono : MonoHyp … ; monoCoef : MonoCoef … ; hdiff : HDiff … ; zeroT : ZeroTOk L k.ρ
  validL : Nh + 2 = N → ValidAtL R Nh ; f1 : SharpF1 … ; -- every current export
theorem flow_master (P : ℕ → FlowConsts L → Prop)       -- extra user conditions
    (hP : ∀ L ℓ A ρ, ∀ᶠ ε in 𝓝[>] 0, P L ⟨ℓ, A, ρ, …, ε, …⟩) :
    ∃ L₀, ∀ L ≥ L₀, ∃ k : FlowConsts L, P L k ∧ ∀ N R Nh, Std R k N Nh → FlowExport L k N R Nh
```

The tex-cited names (`thm_flow`, `thm_flow_sharp`, `thm_flow_range`, `flow_range_hyp`,
`thm_flow_hor2`, `thm_flow_complete_band`, `thm_flow_final`, `flow_finalZ_hyp`,
`thm_flow_final_Z`, …) keep their statements and become corollaries of 20–60 lines each.

| Lines saved | Effort | Risk |
|---|---|---|
| ≈6–6.5k | M | Statements unchanged; outline untouched. These files are among the slowest (Log: 7–11 min each), so the build time improves too. `h04rg-outline.tex` cites `thm_flow`. |

### C2. Obs2 sector copies `O` / `OU` / `OAB` (d) — 32 files, 6 902 lines (U/AB only), 25 tex-cited

Pairs: `BlockO2`/`BlockOU2`/`BlockOAB2`, `EstBlock(U, AB)`, `Step2OL(U, AB)`, `Step3OL(U, AB)`,
`StepKOW(U, AB)`, `KObs(U, AB)`, `WObs(U, AB)`, `LinBound(U, AB)`.

`diff BlockOU2 BlockOAB2` differs only in the structure name (`BHOU` vs `BHOAB`) and one field
access (`hO.hVm' hb` vs `hO.hVm b hb`). `Step3OL` vs `Step3OLU` differ in the weight hypothesis
(`w.ab = 0` vs `w.Sub ∧ w.ab ≠ ⊤`).

Proposal: one hypothesis bundle indexed by a sector, and the whole `Est` chain once.

```lean
inductive Sector | one | u | ab
structure BHOS (s : Sector) (P : ObsPts d L N) (j : ℕ) … : Prop   -- union of BHO/BHOU/BHOAB fields
def Sector.WtOK : Sector → Wt → Prop                              -- w.ab = 0 | w.Sub ∧ … | …
```

Alternatively, a class `ObsBlockHyp H` with the five accessors that the proofs actually use.
`BHO`, `BHOU` and `BHOAB` become `abbrev`s, and the old theorem names become 1-line instances.

| Lines saved | Effort | Risk |
|---|---|---|
| ≈4.5k | M | Low: 25 outline-cited names kept as abbrevs. |

### C3. Step2 `Last` copies of `Map`/`Lip`/`Flow` (b) — 15 files, 6 911 lines, 13 tex-cited

Copies:
- `LastSym` ↔ `Map/SymCov`: 50 differing lines. "`j + 2 < N` replaced by `j + 1 < N` and
  `L > 2^{d+4}+4`".
- `LastKCov` ↔ `Map/KCov`.
- `FlowLastLip1–6` ↔ `Lip/FlowLip*`/`FlowFade*`/`FlowZeta*`: verbatim (Log l.2486, ≈2.7k lines
  extracted by script, with the structures `SD.OK`, `DomH`, `Cmp`, `Run` shadowed).
- `FlowLastBand(2)` ↔ `g_step_bounds`.
- `FlowLastF1a/b` ↔ `Flow/FlowF1c/d`.

Proposal: replace the hard-wired gap and validity by parameters.

```lean
structure Gap (d L N j : ℕ) : Prop := (hj : j + 1 < N) (geo : j + 2 < N ∨ 2^(d+4)+4 < L)
-- SymHyp/KCovHyp take `Gap`; Lip structures take a validity predicate
structure DomH (Val : ℕ → Prop) … ; -- ValidAt R j  and  ValidAtL R j  both imply Val j
```

The `Map`/`Lip` versions are then the case `j + 2 < N`, and the `Last` versions the case
`L > 2^{d+4}+4`.

| Lines saved | Effort | Risk |
|---|---|---|
| ≈4k | M–H | The `Lip` layer is large and elaborate. Low statement risk: no audit names, 13 outline names. |

### C4. H02UV/Obs2/Est copy of the H02UV/Step2/Map Cauchy chain (d) — ≈9.2k lines (`O` sector)

Name-matched pairs (`onames.py`, 157 declarations, ≈3k lines; the rest is renamed):
`StepKO(W)`↔`StepFinal`, `SecondO`↔`Second`, `LinO`↔`Lin`, `Step2O`↔`Main`, `Step3OL`↔`Lambda`,
`BlockO5/6`↔`Block`/`Lambda`, `SplitO`↔`Split`, `LinBO`↔`LinB`, `ReblockO`↔`ReblockBound`,
`ExactStep`↔`Reblock`.

The cause is that the `Step2` estimates are stated on `N Λ` with `tNorm`.

Proposal: introduce a normed-RG-algebra interface and prove `H02UV/Step2/Map` once over it. `N Λ` (with
`tNorm`) and `OE c Λ` (with `oTj w`, which by C2 covers every sector) become instances.

```lean
class RGNormAlg (R R2 : Type*) [CommRing R] [CommRing R2] [Algebra ℂ R] [Algebra ℂ R2] where
  T : ℕ → ℝ → R → ℝ≥0∞            -- T_j(ℓ)
  mul_le : T j ℓ (f*g) ≤ T j ℓ f * T j ℓ g
  θ : R →ₐ[ℂ] R2 ; E : R2 →ₗ[ℂ] R ; E_θ_le : … ; cauchy : …; loc_contract : …
```

New shared library `RGCore` (with C6).

| Lines saved | Effort | Risk |
|---|---|---|
| ≈6–8k | H (weeks) | High: rewrites the `H02UV/Step2/Map` statements cited in the outline (`step2`, `step3L`, `stepK_tsW`, …) and touches every `H02UV/Obs2/Est` file. Do it only after C2 and C6. |

### C5. Spin2 Pair chains (b) — 38 files, 15 151 lines, 44 tex-cited

- `PairDef5e`/`5eD` and `PairDef6b`/`6bD`: "copies with `Admissible … b μ₀` replaced by
  `∀ j ≤ N_h, InD3 …`; same bodies".
- `PairDef5c`/`5D`, `PairLoop6D`/`6f`/`6a–g`, `PairESz2–8`, `PairFinal4/5/6`: successive
  generations.

Proposal: keep only the window (`…D`) form. Derive the `Admissible` form with a lemma
`InD3_of_admissible`, which already exists in effect (cf. `inDh_rg_of_D`). Re-derive the superseded
generations (`pairAbove_final4/5_MF'`, …), which the outline cites, as corollaries of
`PairFinal6`.

| Lines saved | Effort | Risk |
|---|---|---|
| ≈6k | M–H | 44 outline names. |

### C6. Algebraic RG map in triplicate (d) — `H02RG/Step/ZVK` 452, `H02RG/Obs/Generic*` 1 084, `H02UV/Step2/Map/Gen` + `Reblock` 779, `H02UV/Obs2/Map/ExactStep` W-copies ≈300

Twins: `Step.Ktil_union`/`Step2.gKtil_union` (53/52 lines), `Step.sum_Sec_eq_sum_G0`/
`Step2.gsum_Sec_eq_sum_G0` (64/62), `Step.Jprod_sum_R1`/`Step2.J2prod_sum`,
`Obs.Gen.KtermG_gjoin`/`Obs2.KtermG_gjoinW`, `KnextG_union`/`KnextG_unionW`,
`KnextG_eq_KextG`/`KnextG_eq_KextGW`.

Proposal:
- Move `Obs.Gen` (`RGAlg`, `RGIngr`, `KnextG`, `SuppHyp`, the factorisation lemmas) into a new
  low-level library `RGCore` that depends only on `Grassmann`, `Loc` and `FRD`.
- Weaken `SuppHyp` to the `W` form.
- Define `Step2.gKnext := KnextG (ECCAlg C) ⟨Ib, Ip, J, K⟩` and `Step.Knext` via
  `GenericBridge`.

| Lines saved | Effort | Risk |
|---|---|---|
| ≈1k | M | The enabling step for C4 and for any new model. `Step.Knext` is in the `d ≥ 3` audit closure, so prove the bridge as a lemma and do not change the definitions of `Step`. |

### C7. PtCorr2 observable-history variants (b) — 14 files, 5 832 lines, 32 tex-cited

`ObsHist`, `ObsHist2`, `ObsHistU`, `ObsHistRel`, `ObsHistRelE`, `ObsHistRelE2`, `ObsHistRelW`,
`ObsHistTop`, `ObsHistLast`, `ObsHistFrom`, `ProdBd(2)Hist/Top`, `Last/LastL1`. The variants are a
weight (`W`), an error term (`E`), and the top index versus an interior index.

Proposal: one `obs_hist_gen` with a weight parameter `w`, an error sequence `e`, and an end index
`n ≤ N_h + 1`.

| Lines saved | Effort |
|---|---|
| ≈2.5k | M |

### C8. Spin2 Cont chains (b) — 89 files, 21 775 lines, 132 tex-cited, 3 audit

Examples:
- `ContNa2`/`ContNb3`: `nb_lastA_le` is `na_lastA_le` with arbitrary weights (325 of 372 code lines
  shared).
- `ContEqS*`/`ContEqC*`/`ContEqF*`/`ContFx*`, `ContArt*`/`ContDiff*`, `ContWire*`/`ContTop*`.

Proposal: keep the most general member of each chain and re-derive the rest.

| Lines saved | Effort | Risk |
|---|---|---|
| ≈7k | H | High: 132 outline names, and the audited `Spin2.thm_limit_fixed_betaR`, `thm_limit_equi_r` and `thm_limit_equi_rAnn` sit here. |

### C9. Obs2 `RestartRec`/`RestartRec2`, `MemGronwall`/`MemGronwall2` (b) — 4 files, 2 525 lines, 8 tex-cited

`RestartRec2` (B3, T4′) generalises `RelRecK` to large transients `w₀ ≥ 0`, `k₀ ≥ 120 B r̄ w₀`.
`RelRecK` is the case `w₀ = 0`.

Proposal: derive `RestartRec` from `RestartRec2`, and the same for `MemGronwall`. In addition, give
`RelRecK`/`RelRecT` (30+ positional `ℕ → ℝ`/`ℝ` arguments) a `structure RecConsts`.

| Lines saved | Effort | Risk |
|---|---|---|
| ≈1.1k | L | Low. |

### C10. Flow2 internal chain (b)/(d) — 17 files, 4 276 lines, 16 tex-cited

`FixedR`, `FixedR2`, `FixedR3`, `FixedRParam`, `FixedRParamG1/G2/Z1/Z2/Z3`, `FixedRDiff(2)`,
`Range*`, `Complete(2)`, `Hor2Unique`. Examples: the `…K` copies of the `History` lemmas with
`hb : KeepD …` (Log l.2147), and `monoCoef_of_small_x`, a copy that returns explicit constants.

Proposal: state the `History` lemmas on an arbitrary set `S` with `KeepD`, which is already done
for some. Return constants through structures, not `∃`.

| Lines saved | Effort |
|---|---|
| ≈1.8k | M |

### C11. Grassmann real versus complex covariance (a) — `GaussianC`, `IBPC`, `GramC`, `HadamardC`, `TorusC`: 985 lines, 13 tex-cited

The bridges `Lop_eq_LopC`, `expL_eq_expLC`, `EC_eq_ECC` and `omega_eq` exist. The real versions
were kept only so that existing proofs that unfold them still work.

Proposal: `def Lop C := LopC (cplx C)` (and the same for `expL`, `EC`, `omega`), delete the
duplicated real proofs, and add `@[simp]` unfolding lemmas.

| Lines saved | Effort | Risk |
|---|---|---|
| ≈0.6–0.9k | L–M | Medium: `Step`, `Loc` and `Obs` (the `d ≥ 3` audit closure, `h02rg-lean.tex`) unfold `Lop`/`EC`. Do it only with a full `d ≥ 3` re-audit. |

### C12. H02UV/Step2/Flow `F1` family (b) — `FlowF1`, `F1b`, `F1c`, `F1d`, `F1S1–S3`, `Last/FlowLastF1a/b`

These are about 440 shared code lines per pair. The variants are band, sharp and top-index forms.

| Lines saved | Effort |
|---|---|
| ≈1.5k | M |

### C13. `Obs.LocObs` versus `H02UV/Obs2/Loc` (a)

Twins: `exists_core_bound`/`exists_core2_bound` (42/64), `exists_even_contract`/`…2` (79/49),
`exists_odd_contract`/`…2` (70/40), `locA_contract`/`exists_locA_contract2`/`exists_locB_contract2`.
These are the complex-covariance and dressed-weight versions.

Proposal: generalise `Obs.LocObs` to complex `C`, so that the `Obs2` versions become instances.

| Lines saved | Effort | Risk |
|---|---|---|
| ≈0.3k | M | Touches the `d ≥ 3` audit closure. |

### C14. `Step.StructureAux` versus `Step2` symmetry/covariance lemmas (a)

Twins: `AE_Inext`/`AE_J2`, `AE_kap` (in `CovHyp`, `SymHyp`, `Last.CovHyp`, `Last.SymHyp`: four
copies), `region_small`/`region_small_L`, `EC_mem_NX`/`ECC_mem_NX`, `EC_Jsym2`/`ECC_Jsym2`,
`EC_autAlg2`/`ECC_autAlg2`, `C_eq_zero_of_nbhd`/`C2_eq_zero_of_nbhd`.

Proposal: after C11, the `EC` lemmas are instances of the `ECC` ones. After C3, the two `Step2`
copies merge.

| Lines saved | Effort |
|---|---|
| ≈0.5k | M |

### C15. Dead declarations (§6) — 4 215 decl lines

Pure deletion, with no generalisation needed.

| Lines saved | Effort | Risk |
|---|---|---|
| ≈4.2k | L | Low; the root set is conservative (suffix-matched tex tokens). |

## 4. Top 15 consolidation opportunities (ranked by lines saved / effort)

Effort units: L = 1, M = 3, M–H = 4, H = 8 (roughly agent-days with a build).

| # | Opportunity | Lines saved | Effort | Ratio | Tex-cited / audit affected |
|---|---|---|---|---|---|
| 1 | C15 dead declarations | 4.2k | L | 4.2 | 0 / 0 |
| 2 | C1 Step2 flow master theorem | 6.3k | M | 2.1 | 24 (statements kept) / 0 |
| 3 | C2 Obs2 sector parameterisation | 4.5k | M | 1.5 | 25 / 0 |
| 4 | C5 Spin2 Pair window-form + generations | 6.0k | M–H | 1.5 | 44 / 0 |
| 5 | C9 RestartRec ⊂ RestartRec2, MemGronwall | 1.1k | L | 1.1 | 8 / 0 |
| 6 | C3 Step2 Last via `Gap`/validity parameters | 4.0k | M–H | 1.0 | 13 / 0 |
| 7 | C8 Spin2 Cont chains | 7.0k | H | 0.9 | 132 / 3 |
| 8 | C7 PtCorr2 ObsHist family | 2.5k | M | 0.8 | 32 / 0 |
| 9 | C4 generic normed RG algebra (H02UV/Obs2/Est ⊂ H02UV/Step2/Map) | 7.0k | H (+ after 3, 11) | 0.8 | ≈30 / 0 |
| 10 | C10 Flow2 chain | 1.8k | M | 0.6 | 16 / 0 |
| 11 | C11 Grassmann real := complex | 0.8k | L–M | 0.5 | 13 / `d ≥ 3` closure |
| 12 | C12 Step2 F1 family | 1.5k | M | 0.5 | ≈6 / 0 |
| 13 | C6 RGCore (single algebraic RG map) | 1.0k | M | 0.3 (strategic) | 3 / `d ≥ 3` closure (via bridge only) |
| 14 | C14 Step/Step2 symmetry lemmas | 0.5k | M | 0.17 | few / `d ≥ 3` closure |
| 15 | C13 LocObs complex | 0.3k | M | 0.1 | few / `d ≥ 3` closure |

The total of the 15 items is about 54k lines, which matches the raw text-level estimate of §2.
The realistic yield is the background-corrected ≈35k.

## 5. Mechanical cross-library twins (base ↔ 2), best matches

From `twins.tsv` and `twinsX.tsv`. Columns: 2-declaration (lines) ↔ base (lines), type ratio,
proof-constant Jaccard.

| 2-declaration | base declaration | type ratio | proof Jaccard |
|---|---|---|---|
| `Obs2.exists_core2_bound` (64) | `Obs.LocObs.exists_core_bound` (42) | .88 | .74 |
| `Step2.gsum_Sec_eq_sum_G0` (62) | `Step.sum_Sec_eq_sum_G0` (64) | .88 | .87 |
| `Step2.gKtil_union` (52) | `Step.Ktil_union` (53) | .94 | .56 |
| `Obs2.exists_even_contract2` (49) | `Obs.LocObs.exists_even_contract` (79) | .80 | .67 |
| `Step2.J2prod_sum` (44) | `Step.Jprod_sum_R1` (42) | 1.0 | .76 |
| `Obs2.exists_odd_contract2` (40) | `Obs.LocObs.exists_odd_contract` (70) | .80 | .66 |
| `Obs2.oNorm_mul_le'` (39) | `Obs.oT_mul_le` (38) | .78 | .64 |
| `Obs2.KtermG_gjoinW` (39) | `Obs.Gen.KtermG_gjoin` (40) | 1.0 | .81 |
| `Step2.card_G0W_le` (30) | `Step.card_Gset_le` (29) | .80 | .68 |
| `Obs2.oT_expU_sub_one_le` (30) | `Obs.oT_exp_oexp_sub_one_le` (32) | 1.0 | .81 |
| `Step2.region_small_L` (24) | `Step.region_small` (25) | .86 | .95 |
| `Step2.C2_eq_zero_of_nbhd` (24) | `Step.C_eq_zero_of_nbhd` (24) | 1.0 | .75 |
| `Step2.ECC_mem_NX` (23) | `Step.EC_mem_NX` (23) | 1.0 | .85 |
| `Step2.ECC_Jsym2` (21) | `Step.EC_Jsym2` (22) | 1.0 | .83 |

Totals:

| Library pair | twins | decl lines |
|---|---|---|
| Step2↔Step | 50 | 709 |
| Obs2↔Obs | 33 | 592 |
| PtCorr2↔PtCorr | 4 | 43 |
| Obs2↔Step2 | 22 | 847 |
| PtCorr2↔(Obs2, Step2) | 72 | 1 471 |
| Obs↔Step | 4 | 114 |

Reuse of the base library, as the fraction of 2-declarations that mention any base constant:

| Library | Fraction |
|---|---|
| Step2 | 38% (1 500/3 972) |
| Obs2 | 75% (the `Obs.SA`/`OE` algebra is reused) |
| PtCorr2 | 1% |
| Flow2 | 0% |

## 6. Dead-weight candidates (full root set: Audit + all tex)

326 top-level declarations, 4 215 decl lines; the list is in `dup_cl/dead.tsv`.

| Library | declarations | decl lines |
|---|---|---|
| Spin2 | 25 | 1 254 |
| Flow2 | 33 | 683 |
| Obs | 91 | 590 |
| Loc | 58 | 385 |
| Step2 | 4 | 270 |
| DressedFRD | 16 | 222 |
| Step | 23 | 160 |
| Obs2 | 19 | 136 |
| PtCorr | 6 | 127 |
| Grassmann | 7 | 114 |
| Flow | 9 | 97 |
| Cont | 18 | 84 |
| PtCorr2 | 9 | 44 |
| other | 8 | 49 |

Largest items:

| Declaration | Module | Lines |
|---|---|---|
| `Spin2.fw_pairAbove5_atD` | `Final.FinalNF` | 276 |
| `Spin2.fw_pairAbove_atD` | `Final.FinalWire` | 259 |
| `Step2.flow_rg_full` | `Lip.FlowLipMain` | 142 |
| `Flow2.Hist.monoCoef_of_small` | `Mono` | 114 |
| `Spin2.thm_multiscale_h0_beta` | `Final.FinalBeta` | 103 |
| `Step2.flow_rg_gen` | `Flow.FlowMain` | 90 |
| `Flow2.Hist.continuousOn_bsh` | | 86 |
| `Spin2.MasterFacts.fw_multiscale_traj5` | | 84 |
| `Spin2.thm_multiscale_h0_final` | | 83 |
| `DressedFRD.Data.Gplus_nonneg` | | 73 |
| `Spin2.eqs_ctMain` | | 69 |
| `Spin2.MasterFacts.fw_atG` | | 62 |
| `DressedFRD.zero_mode_le` | | 54 |
| `Obs.flowObs_of_thm_flow` | | 53 |
| `Flow.continuous_stableMap` | | 52 |

A separate and much larger category is *tex-only* declarations: live only because a tex file cites
them, not reachable from the 46 Audit statements.

- 50.7k decl lines in the 2-libraries (§1.4); the list is in `dup_cl/aud/texonly.tsv`.
- The roots, with reachable and exclusive line counts and the citing tex files, are in
  `dup_cl/aud/texroots.tsv`.
- Largest roots by reachable / exclusive lines:

  | Root | reachable | exclusive |
  |---|---|---|
  | `Spin2.pairAbove_final6_MF'` | 5 347 | 406 |
  | `Spin2.pairAbove_final5_MF'` | 4 685 | 324 |
  | `Step2.thm_flow_horizon` | 3 618 | 47 |
  | `Step2.thm_flow` | 3 571 | 0 |
  | `Step2.thm_flow_range` | 3 139 | 196 |
  | `Step2.thm_flow_complete_band` | 2 532 | 1 027 |

- 527 of the 585 roots are cited only by `summaries/h02uv-outline.tex`.

The consolidations C1, C3, C5, C7 and C8 make these citations cheap: the names stay, but their
proofs become corollaries.

## 7. Foundation-level generality gaps

| # | Gap | Where | Blocks |
|---|---|---|---|
| G1 | One `ψ, ψ̄` pair per site: `Sf Λ := Λ × ℤˣ` | `Grassmann/Coeff.lean` | `H^{0\|2n}`, `H^{0\|4}` (`summaries/h04rg-outline.tex`), O(n)-type models |
| G2 | Coupling space fixed to the four `H^{0\|2}` monomials: `structure Vcoup (z y a b : ℂ)` | `Loc/Stencil.lean`; also `Loc2`/`Loc4` | other local polynomials and models |
| G3 | Real covariance is primary (`Lop`/`EC`/`omega` on `Matrix I I ℝ`) with parallel `…C` copies | `Grassmann/Gaussian`, `IBP`, `Gram`, `Hadamard`, `Torus` | dressing, complex masses (cause of C11, C13, C14) |
| G4 | Geometry: `Lam d L N := Torus d (L^N)` (`Fin d → ZMod (L^N)`), blocks and polymers tied to it | `Loc/Polymer.lean` | other graphs, boxes with boundary conditions, anisotropic tori, non-hierarchical block systems |
| G5 | Observable algebra fixed to two observables: `Obs.SA c Λ` with components `e, a, b, ab`; `Case` is one or two | `H02RG/Obs/Algebra.lean` | n-point functions; cause of the C2 sector copies |
| G6 | Algebraic RG map not shared: `Step.Knext`, `Obs.Gen.KnextG` and `Step2.gKnext` are separate (C6) | | every new model or sector |
| G7 | No abstract norm interface: the estimate chain is proved for `N` with `tNorm` (C4) | | every new algebra |
| G8 | Flow theorems return long `∃ … ∧ …` conjunctions with the ε choice inside the proof, and hypothesis bundles are passed as 30+ positional reals (`Obs2.RelRecK`) | | additive variants: every new need costs a copy (C1, C9, C10) |
| G9 | Horizon and geometric constants hard-wired in hypotheses (`j + 2 < N`, `L > 68`, `L ≥ 69`, `L > 2^{d+4}+4`, `ValidAt` vs `ValidAtL`) | | cause of C3 |
| G10 | `d` fixed to 2 in 1 104 Spin2, 890 PtCorr2 and 646 Step2 declarations; the maps (`H02UV/Step2/Map`, `Obs2`) stay `d`-general | | Not a duplication cause. Several PtCorr2 statements could probably be `d`-general, which would allow reuse for `d ≥ 3` dressed problems. |

Recommended API changes:
1. **`RGCore` library** below `Step` and `Step2`: `RGAlg`, `RGIngr`, `KnextG`, `SuppHyp` (weak
   form), the factorisation and union lemmas, `GenericBridge` (G6). Then a
   `class RGNormAlg` (G7) with instances for `N Λ` and `OE c Λ`.
2. **Complex covariance as primary** (G3): `Lop C := LopC (cplx C)` and similar; keep `simp`
   lemmas so that unfolding proofs still work.
3. **Generator index type** (G1): `Sf Λ ι := Λ × ι × ℤˣ` with `ι = Unit` recovering the present
   `H^{0|2}`, or a typeclass `GrassmannSite`.
4. **Observable sectors as an index** (G5): `SA (S : Finset ObsLabel)` or `N Λ ⊗ ⋀(ℂ^k)` with a
   `Sector`/weight parameter. This removes C2 and makes n-point functions possible.
5. **Result structures plus eventual ε-conditions** for the flow theorems (G8): `FlowConsts`,
   `FlowExport`, `∀ᶠ ε in 𝓝[>] 0` extra conditions, and named constant structures instead of
   positional reals.
6. **Gap and validity predicates** (G9) in `H02UV/Step2/Lip` and `H02UV/Step2/Map/SymCov`, `KCov`.
7. **Block geometry interface** (G4): a structure with blocks at scale `j`, nesting, `Touch`,
   `IsConn` and a distance, instantiated by the torus. This is long-term, because `FRD` and
   `DressedFRD` are built on `Torus`.

## 8. Recommended first consolidation step

**C1: one `flow_master` theorem for `H02UV/Step2/Flow`, after deleting the dead declarations (C15) as a
warm-up.**

| Aspect | Expected effect |
|---|---|
| Scope | One new file, `H02UV/Step2/Flow/FlowMaster.lean` (≈1.5k lines), with the `FlowConsts`/`FlowExport` structures and an extra-condition parameter `P` with `∀ᶠ ε in 𝓝[>] 0, P …`. The 11 `…Hyp`/`…Thm` variants (`FlowThm`, `FlowSharp2`, `FlowRangeHyp`, `FlowFinalZHyp`, `ZetaSharpHypX`, `FlowCompleteHyp`, `FlowCompleteBandHyp`, `FlowComplete2Hyp`, `FlowMasterHypL`, `FlowMasterHypLZ`, `FlowHor2Thm`) are rewritten as corollaries under their current names and statements. |
| Lines | ≈ −6k lines in `Step2` (≈7.5% of the library); with C15, ≈ −10k lines in the project |
| Build time | Several of the slowest files go away (Log: `FlowFinalHyp` ≈11 min, `FlowDiffThm` and `thm_flow` ≈7 min each) |
| Paper and audit risk | Low: no Audit name is in the cluster, and the 24 tex-cited names keep their statements. Re-run `Audit/H02UV.lean` and `H02UV/Step2/Audit.lean` after the change. |
| Generality | Every future flow variant (for example the `H^{0|4}` outline, which cites `thm_flow`) becomes a choice of `P` plus a projection out of `FlowExport` instead of an 800-line copy. |

The same pattern then applies, in order, to C9 (L), C2, C3 and C5.
