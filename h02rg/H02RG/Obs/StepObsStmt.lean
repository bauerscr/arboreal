import Obs.Map
import Step.Theorem

/-!
# Theorem `thm:step-obs`: the statement (Section `sec:tyler-renorm-group`)

We state Theorem `thm:step-obs` for the observable renormalisation group map `KnextO` /
`nextObs` of `Obs.MapDef`, and the three component estimates into which its proof splits.

## Norms
All norms are the weighted norms `normj` (`e:Tphi-obs`) of `Obs.Norm` at scale `j`, with
`ℓ = ℓ_j = ellj d L ℓ₀ j` and coalescence scale `j_ab = coal L a b` (`E:coal`):
* `VnormObs … j Vo = ‖V^obs_j‖_j = sup_{B ∈ 𝓑_j} ‖V^obs_j(B)‖_{T_j(ℓ_j)}`, where
  `V^obs_j(B) = splitO c (toV Vo) a b B` is the (split) evaluation of the `V` part of `Vo`
  (so `u^obs_j = 0` automatically, as assumed in the theorem);
* `VnormFull … j Vb Vo = ‖V_j‖_j = sup_B ‖V^∅_j(B) + V^obs_j(B)‖_{T_j(ℓ_j)}`;
  the bulk norm `‖V^∅_j‖_j` is `Step.Vnorm j ℓ_j Vb`;
* `wnormO … j A U F = A^{(|𝓑_j(U)| - 2^d)_+} ‖F‖_{T_j(ℓ_j)}`,
  `KnormFull … j A K = ‖K_j‖_j = sup_{X ∈ 𝒞_j} wnormO j A X (K X)` (`e:K-norm` with `e:Tphi-obs`),
  `KnormObs … j A K = ‖K^obs_j‖_j` (the same for `π_obs K`); the bulk norm `‖K^∅_j‖_j` is
  `Step.Knorm j ℓ_j A (bulkK K)`.

## Hypotheses (`StepObsHyp`)
Those of Theorem `thm:step` for the bulk part (`GoodCov`, `InK` for `K^∅ = bulkK K`), and for
the observable part:
* `a ≠ b` (needed for `Q^obs` to be the evaluation of coupling constants, `QobsO_eq`);
* `ObsLoc c P j C Vo K a b` (Obs.MapSupp): `K^obs ∈` the support class `Supp c P a b j X`
  for connected `X` (`InKO`; `P = False`: the text's `𝒩^obs_sym(X^□)`, `P = True`:
  componentwise locality only) and the (Case 2) locality conditions `CoupLoc` of the coupling
  constants (`η = 0` or `NearS j a b`: `a, b` close at scale `j + 1`, which holds for
  `j ≥ j_ab`; only the output support `InKO … (j+1) K_{j+1}` depends on them); for `P = False`
  also `K^{ab}(Y) = 0` for all small `Y`;
* the ab-condition of the theorem: `K^{ab}_j(X) = 0` for `X ∈ 𝒮_j` if `j < j_ab`;
* `InKpt c a b j K`: the source fields of `K_j(X)` lie in `X`: `K_j(X)_a = 0` unless `a ∈ X`,
  `K_j(X)_b = 0` unless `b ∈ X`, `K_j(X)_{ab} = 0` unless `a ∈ X` or `b ∈ X`.
  **(Addition.)**  This is the convention of the text (`σ_a` occurs in `K(X)` only if `a ∈ X`),
  which is needed for the contraction `prop:Loc-obs` (ii) (`Obs.LocObs.locObs_contract`
  assumes `a ∈ X ∨ F_a = 0` etc.: if `a ∈ X^□ ∖ X` the component `K_a(X)` is not localised and
  is marginal).  It is weaker than `Supp` with `X` in place of `X^□` in the `ab` component,
  since `J(B, B)` can carry an `ab` component in a block containing only one of `a, b`.
  It holds at `j = 0` (`K_0 = 0`); its preservation by the map is proved in
  `Obs.StepObsCoupling` (`InKpt_KnextO`).

`C(a, b) = C(b, a)` follows from `GoodCov` (positive semidefinite, `symm_of_goodCov`).

## The statement (`StepObsStatement`)
`∃ C₀ η ν m L₀, ∀ L ≥ L₀, ∃ A₀, ∀ A ≥ A₀, ∃ ε > 0`, for `j < N`, `ℓ₀ > 0` and data satisfying
`StepObsHyp`, the separation hypothesis `blk (j+1) a ≠ blk (j+1) b → C(a, b) = 0`
(`SepHyp j C a b` of `Obs.StepObsFix`; **addition**: the text places `a` in the centre of its
blocks, and then this follows from `GoodCov.range`; for `j + 1 = N` it is vacuous, there is a
single `N`-block; it is needed for `e:K+obs-bd`, see `Obs.StepObsFix`), and
`‖V^∅‖_j + ‖K^∅‖_j ≤ ε`, `‖V^obs‖_j + ‖K^obs‖_j ≤ ε`:
* `e:V+obs-bd`, at the level of `Λ`:
  `‖(u^obs + V^obs)_{j+1}(Λ) - (𝔼 θ V^obs_j(Λ) - ½ 𝔼[θ V^obs_j(Λ); θ V^obs_j(Λ)])‖_{T_{j+1}(ℓ_{j+1})}
   ≤ C₀ L^{2(d-2)} ‖K^obs_j‖_j`, and per block
  `‖(u^obs + V^obs)_{j+1}(B) - (𝔼 θ V^obs_j(B) - ½ 𝔼[θ V^obs_j(B); θ V^obs_j(Λ)])‖ ≤ C₀ L^{2(d-2)} ‖K^obs_j‖_j`
  (for all `j < N`; for `j + 1 = N` the left sides vanish, `Q = 0`);
* `K_{j+1}` satisfies the support hypotheses at scale `j + 1` (`InKO`, `InKpt`);
* `e:K+obs-bd`: `‖K^obs_{j+1}‖_{j+1} ≤ C₀ (f + A^{-η}) ‖K^obs_j‖_j +
  C₀ A^ν (‖V^∅_j‖_j + ‖K_j‖_j)(‖V_j‖_j + ‖K_j‖_j)` with `f = L^{-d_+}` if `j + 1 < N` and
  `f = L^m` if `j + 1 = N` ("`Φ^obs_N` is bounded"; `m` depends only on `d`).

## The component estimates
With `K_{j+1} = 𝓛_{j+1,𝒮} + 𝓛_{j+1,𝒫∖𝒮} + (𝓡¹ + 𝓡² + 𝓡³)` (`Gen.KnextG_eq_decomp`, `LlinG_eq`),
for connected `(j+1)`-polymers `U`, with `vb = ‖V^∅‖`, `vo = ‖V^obs‖`, `kb = ‖K^∅‖`,
`ko = ‖K^obs‖` (all at scale `j`) and `Q = (vb + kb + ko)(vb + vo + kb + ko)`:
* `SmallObsStmt`: `A^{…} ‖π_obs 𝓛_{j+1,𝒮}(U)‖ ≤ C₀ f ko + C₀ L^m Q`
  (`f = L^{-d_+}` if `j + 1 < N`, `L^m` if `j + 1 = N`);
* `LargeObsStmt`: `A^{…} ‖π_obs 𝓛_{j+1,𝒫∖𝒮}(U)‖ ≤ C₀ L^m A^{-η} ko + C₀ L^m A^ν Q`;
* `NonlinObsStmt`: `A^{…} ‖π_obs (𝓡¹ + 𝓡² + 𝓡³)(U)‖ ≤ C₀ L^m A^ν Q` (proved in `Obs.StepObsNonlin`,
  `obs_nonlinear_bound_proof`).
**`SmallObsStmt` and `LargeObsStmt` are false as stated**; the corrected versions
`SmallObsStmt'`, `LargeObsStmt'` of `Obs.StepObsFix` (with `SepHyp`, and the two-block terms
`LpairG` moved from the large to the small sets) are used by the assembly
`Obs.stepObs_of_components` (`Obs.StepObs`); they are proved in `Obs.StepObsSmall` and
`Obs.StepObsLarge`.
The powers `L^m` are harmless (they are absorbed by `A ≥ A₀(L)`), and allow in particular for
the growth `L^{2(d-2)}` of the weights (`e:Tphi-obs-ub`).
-/

namespace Obs

noncomputable section

open Finset Grassmann SA Loc Step LocObs Gen

variable {d L N : ℕ} [NeZero L]

/-! ### Source points in the polymer -/

section PtSub

variable {c : Case} {Λ : Type*}

/-- The elements whose `a` component vanishes unless `pa`, whose `b` component vanishes unless
`pb`, and whose `ab` component vanishes unless `pa ∨ pb`. -/
def ptSub (pa pb : Prop) : Subalgebra ℂ (OE c Λ) where
  carrier := {F | (¬ pa → (F : SA c Λ).a = 0) ∧ (¬ pb → (F : SA c Λ).b = 0) ∧
    (¬ pa → ¬ pb → (F : SA c Λ).ab = 0)}
  mul_mem' := by
    rintro F G ⟨h1, h2, h3⟩ ⟨g1, g2, g3⟩
    refine ⟨fun h => ?_, fun h => ?_, fun ha hb => ?_⟩
    · rw [OE.mul_a, h1 h, g1 h]; simp
    · rw [OE.mul_b, h2 h, g2 h]; simp
    · rw [OE.mul_ab, h1 ha, g1 ha, h2 hb, g2 hb, h3 ha hb, g3 ha hb]; simp
  add_mem' := by
    rintro F G ⟨h1, h2, h3⟩ ⟨g1, g2, g3⟩
    refine ⟨fun h => ?_, fun h => ?_, fun ha hb => ?_⟩
    · show (F : SA c Λ).a + (G : SA c Λ).a = 0; rw [h1 h, g1 h, add_zero]
    · show (F : SA c Λ).b + (G : SA c Λ).b = 0; rw [h2 h, g2 h, add_zero]
    · show (F : SA c Λ).ab + (G : SA c Λ).ab = 0; rw [h3 ha hb, g3 ha hb, add_zero]
  algebraMap_mem' r :=
    ⟨fun _ => SA.algebraMap_a r, fun _ => SA.algebraMap_b r, fun _ _ => SA.algebraMap_ab r⟩

theorem ptSub_mono {pa pb pa' pb' : Prop} (ha : pa → pa') (hb : pb → pb') :
    (ptSub pa pb : Subalgebra ℂ (OE c Λ)) ≤ ptSub pa' pb' := by
  rintro F ⟨h1, h2, h3⟩
  exact ⟨fun h => h1 (fun h' => h (ha h')), fun h => h2 (fun h' => h (hb h')),
    fun h h' => h3 (fun h'' => h (ha h'')) (fun h'' => h' (hb h''))⟩

end PtSub

/-- The source fields of `K(X)` lie in `X` (see the module docstring). -/
def InKpt (c : Case) (a b : Lam d L N) (j : ℕ) (K : Finset (Lam d L N) → OE c (Lam d L N)) :
    Prop :=
  ∀ X, IsConn j X → K X ∈ (ptSub (a ∈ X) (b ∈ X) : Subalgebra ℂ (OE c (Lam d L N)))

/-! ### Norms -/

section Norms

variable (c : Case) (ℓ₀ : ℝ) (a b : Lam d L N)

/-- `‖F‖_{T_j(ℓ_j)}` with the weights of scale `j` and `j_ab = coal L a b`. -/
abbrev nrmj (j : ℕ) (F : OE c (Lam d L N)) : ENNReal :=
  normj d L c ℓ₀ (coal L a b : ℕ∞) j (F : SA c (Lam d L N))

/-- `‖V^obs_j‖_j = sup_{B ∈ 𝓑_j} ‖V^obs_j(B)‖_{T_j(ℓ_j)}` (`e:V-norm`). -/
def VnormObs (j : ℕ) (Vo : Coup c) : ENNReal :=
  ⨆ p ∈ blockIdx (L := L) (N := N) j,
    nrmj c ℓ₀ a b j (splitO c (Coup.toV c Vo) a b (blockSet j p))

/-- `‖V_j‖_j = sup_{B ∈ 𝓑_j} ‖V^∅_j(B) + V^obs_j(B)‖_{T_j(ℓ_j)}` (`e:V-norm`). -/
def VnormFull (j : ℕ) (Vb : Vcoup) (Vo : Coup c) : ENNReal :=
  ⨆ p ∈ blockIdx (L := L) (N := N) j, nrmj c ℓ₀ a b j (VfullX Vb Vo a b (blockSet j p))

/-- `A^{(|𝓑_j(U)| - 2^d)_+} ‖F‖_{T_j(ℓ_j)}`. -/
def wnormO (j : ℕ) (A : ℝ) (U : Finset (Lam d L N)) (F : OE c (Lam d L N)) : ENNReal :=
  ENNReal.ofReal (A ^ (nb j U - 2 ^ d)) * nrmj c ℓ₀ a b j F

/-- `‖K_j‖_j = sup_{X ∈ 𝒞_j} A^{(|𝓑_j(X)| - 2^d)_+} ‖K_j(X)‖_{T_j(ℓ_j)}` (`e:K-norm`). -/
def KnormFull (j : ℕ) (A : ℝ) (K : Finset (Lam d L N) → OE c (Lam d L N)) : ENNReal :=
  ⨆ X ∈ connSets (L := L) (N := N) j, wnormO c ℓ₀ a b j A X (K X)

/-- `‖K^obs_j‖_j = ‖π_obs K_j‖_j`. -/
def KnormObs (j : ℕ) (A : ℝ) (K : Finset (Lam d L N) → OE c (Lam d L N)) : ENNReal :=
  KnormFull c ℓ₀ a b j A (fun X => πobs (K X))

end Norms

/-! ### Hypotheses -/

/-- The hypotheses of Theorem `thm:step-obs` (besides the smallness of the norms). -/
structure StepObsHyp (c : Case) (P : Prop) (j : ℕ) (ℓ₀ : ℝ)
    (C : Matrix (Lam d L N) (Lam d L N) ℝ) (Vb : Vcoup) (Vo : Coup c)
    (K : Finset (Lam d L N) → OE c (Lam d L N)) (a b : Lam d L N) : Prop where
  /-- The covariance `C = C_{j+1}` (as in Theorem `thm:step`). -/
  cov : GoodCov j ℓ₀ C
  /-- `K^∅_j ∈ 𝒦^∅_j` (as in Theorem `thm:step`). -/
  bulk : InK j (bulkK K)
  /-- Two distinct source points. -/
  hab : a ≠ b
  /-- Supports and locality of the observable parts (`Obs.MapSupp`). -/
  loc : ObsLoc c P j C Vo K a b
  /-- The source fields of `K_j(X)` lie in `X`. -/
  pt : InKpt c a b j K
  /-- `K^{ab}_j(X) = 0` for `X ∈ 𝒮_j` if `j < j_ab`. -/
  abSmall : j < coal L a b → ∀ Y, IsSmall j Y → (K Y : SA c (Lam d L N)).ab = 0

/-! ### The component estimates -/

/-- The second-order factor `(vb + kb + ko)(vb + vo + kb + ko)` of the component estimates. -/
def quadO (vb vo kb ko : ENNReal) : ENNReal := (vb + kb + ko) * (vb + vo + kb + ko)

/-- **Nonlinear part**: the bound on `π_obs (𝓡¹ + 𝓡² + 𝓡³)(U)`. -/
def NonlinObsStmt (d : ℕ) : Prop :=
  ∃ (C₀ ν : ℝ) (m L₀ : ℕ), 0 ≤ C₀ ∧ 0 < ν ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ (N j : ℕ), j < N → ∀ (ℓ₀ : ℝ), 0 < ℓ₀ →
    ∀ (c : Case) (P : Prop) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (Vb : Vcoup) (Vo : Coup c)
      (K : Finset (Lam d L N) → OE c (Lam d L N)) (a b : Lam d L N),
      StepObsHyp c P j ℓ₀ C Vb Vo K a b →
      Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) Vb +
          Knorm j (ellj d L ℓ₀ j) A (bulkK K) ≤ ENNReal.ofReal ε₀ →
      VnormObs c ℓ₀ a b j Vo + KnormObs c ℓ₀ a b j A K ≤ ENNReal.ofReal ε₀ →
      ∀ U : Finset (Lam d L N), IsConn (j + 1) U →
        wnormO c ℓ₀ a b (j + 1) A U
            (πobs (R1G (obsA c C) j (obsI j C Vb Vo K a b) U +
              R2G (obsA c C) j (obsI j C Vb Vo K a b) U +
              R3G (obsA c C) j (obsI j C Vb Vo K a b) U)) ≤
          ENNReal.ofReal (C₀ * (L : ℝ) ^ m * A ^ ν) *
            quadO (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) Vb)
              (VnormObs c ℓ₀ a b j Vo) (Knorm j (ellj d L ℓ₀ j) A (bulkK K))
              (KnormObs c ℓ₀ a b j A K)

/-! ### Theorem `thm:step-obs` -/

/-- **Theorem `thm:step-obs`** (statement). -/
def StepObsStatement (d : ℕ) : Prop :=
  ∃ (C₀ η ν : ℝ) (m L₀ : ℕ), 0 ≤ C₀ ∧ 0 < η ∧ 0 < ν ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∃ ε : ℝ, 0 < ε ∧
    ∀ (N j : ℕ), j < N → ∀ (ℓ₀ : ℝ), 0 < ℓ₀ →
    ∀ (c : Case) (P : Prop) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (Vb : Vcoup) (Vo : Coup c)
      (K : Finset (Lam d L N) → OE c (Lam d L N)) (a b : Lam d L N),
      StepObsHyp c P j ℓ₀ C Vb Vo K a b →
      -- the separation hypothesis `SepHyp j C a b` of `Obs.StepObsFix`
      (blk (j + 1) a ≠ blk (j + 1) b → C a b = 0) →
      Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) Vb +
          Knorm j (ellj d L ℓ₀ j) A (bulkK K) ≤ ENNReal.ofReal ε →
      VnormObs c ℓ₀ a b j Vo + KnormObs c ℓ₀ a b j A K ≤ ENNReal.ofReal ε →
      -- `e:V+obs-bd` at the level of `Λ`
      nrmj c ℓ₀ a b (j + 1)
          (evalO c (nextObs C j Vo K a b) a b univ -
            freeStep C (evalO c (Coup.toV c Vo) a b univ)) ≤
        ENNReal.ofReal (C₀ * (L : ℝ) ^ (2 * ((d : ℝ) - 2))) * KnormObs c ℓ₀ a b j A K ∧
      -- `e:V+obs-bd` per block
      (∀ p ∈ blockIdx (L := L) (N := N) j,
        nrmj c ℓ₀ a b (j + 1)
          (splitO c (nextObs C j Vo K a b) a b (blockSet j p) -
            (ECO C (thetaO (Vobs j Vo a b p)) -
              (1 / 2 : ℂ) • ECT C (Vobs j Vo a b p) (evalO c (Coup.toV c Vo) a b univ))) ≤
        ENNReal.ofReal (C₀ * (L : ℝ) ^ (2 * ((d : ℝ) - 2))) * KnormObs c ℓ₀ a b j A K) ∧
      -- the support hypotheses at scale `j + 1`
      InKO c P a b (j + 1) (KnextO j C Vb Vo K a b) ∧
      InKpt c a b (j + 1) (KnextO j C Vb Vo K a b) ∧
      -- `e:K+obs-bd`, and boundedness for `j + 1 = N`
      KnormObs c ℓ₀ a b (j + 1) A (KnextO j C Vb Vo K a b) ≤
        ENNReal.ofReal (C₀ * ((if j + 1 < N then (L : ℝ) ^ (-dplus d) else (L : ℝ) ^ m) +
            A ^ (-η))) * KnormObs c ℓ₀ a b j A K +
          ENNReal.ofReal (C₀ * A ^ ν) *
            ((Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) Vb + KnormFull c ℓ₀ a b j A K) *
              (VnormFull c ℓ₀ a b j Vb Vo + KnormFull c ℓ₀ a b j A K))


end

end Obs
