import Obs2.Map.Ops
import Obs2.Loc.LocABt
import Obs.MapLoc
import Step2.Map.Hol
import Step2.Map.Lin

/-!
# The localisation with observables in `d = 2` (new route, `h02uv-outline.tex`,
Section `sec:obs-flow`)

`Loc_{X,Y}` on the algebra with sources is block diagonal:
`Loc_{X,Y} F = Loc_{X,Y} F_∅ + σ_a loc^a_{X,Y} F_a + σ_b loc^b_{X,Y} F_b + σ_aσ_b loc^{ab}_{X,Y} F_ab`
(`LocO2`), with
* the bulk part `Loc_{X,Y} = Step2.Loc2E X Y` (`Loc^{(2)} + Loc^{(4)}`), so that
  `bulk (LocO2 X Y F) = Loc2E X Y (bulk F)` (`bulk_LocO2`);
* `loc^a`, `loc^b` the **pointed** single-point operators (`locAp`, `locBp`): for `a ∈ X` the
  operator `locA` of `Obs.LocObsDef` (in `d = 2` its images, `ψ̄_a` in Case (1) and `1, ψ̄_aψ_a` in
  Case (2), are already all `U(1)`-compatible derivative-free monomials at one point), and for
  `a ∉ X` the point localisation at `a`, weighted by `|Y|/|X|`:
  `loc^a_{X,Y} F = (|Y|/|X|) locA a {a} {a} F` (`= (|Y|/|X|) m(F) ψ̄_a` in Case (1),
  `(|Y|/|X|)(ε(F) + m(F) ψ̄_aψ_a)` in Case (2)). This is the **repair of the support gap**
  (`Obs2.Est.EstLoc`): with the earlier choice `loc^a_{X,Y} = 0` for `a ∉ X`, the `σ_a` components of
  `K(X)`, `X ∌ a`, were never contracted. The pointed operator contracts for `a ∈ X^□`
  (`exists_odd_contract_pt`, `exists_even_contract_pt`); for `a ∉ X^□` the components vanish by the
  support analysis of `Obs2.Pair.Coal`, so the choice there is immaterial. `loc^a_{X,·}` is additive over
  the blocks of `X`, and `Loc_{X,X}` extracts the full mass of `F_a` for every `X`;
* `loc^{ab}` (`locABtXY`) **new in `d = 2`**: every `U(1)`-invariant derivative-free monomial in
  the fields at `a, b` is marginal, including `ψ̄_aψ_aψ̄_bψ_b` (the coupling `χ`) and
  `ψ̄_aψ_b, ψ̄_bψ_a` (the coupling `η`). We use the **barycentric** substitution
  `ψ_x ↦ ψ_a + t(x)(ψ_b - ψ_a)` of `Obs2.Loc.LocABt` (`locABt`), based at `a` if `a ∈ X` and at `b`
  otherwise (`locABtX`), and split the result over the blocks of `Y` meeting `{a, b}` as in
  `Obs.LocObsDef.locGen`: `loc^{ab}_{X,Y} F = (|Y ∩ {a,b}| / |X ∩ {a,b}|) loc^{ab,t}_X F`.
  It reproduces `1`, `ψ̄_uψ_v` (`u, v ∈ {a, b}`) and `ψ̄_aψ_aψ̄_bψ_b` (`Obs2.Loc.LocT`), is bounded and
  contracts with `C L^{-1}` uniformly in `|a - b|` (`exists_locABt_bound`,
  `exists_locABt_contract`).

**History (sharp region).** The first version used the sharp substitution `ψ_z ↦ ψ_{ρ(z)}`
(`ρ(z) = a` on a region `R_a`, `b` otherwise; `substN`, `proj0`, `locAB2`, kept below for
reference, not used). That operator is not bounded uniformly in `j` (`Obs2.Loc.LocABt`). The region
`ObsPts.Ra` is now unused.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step LocObs

variable {d L N : ℕ} [NeZero L]

/-- The observable points `a, b` and the region `R_a` of the fields localised at `a`. -/
structure ObsPts (d L N : ℕ) [NeZero L] where
  a : Lam d L N
  b : Lam d L N
  Ra : Finset (Lam d L N)

namespace ObsPts

variable (P : ObsPts d L N)

/-- `{a, b}`. -/
def pts : Finset (Lam d L N) := {P.a, P.b}

end ObsPts

/-! ### The substitution `ψ_z ↦ ψ_{ρ(z)}` -/

section Subst

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

end Subst

/-! ### The two-point projection -/

section Proj

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

/-- `ψ̄_u ψ_v`. -/
def m2 (u v : Λ) : Grassmann.N Λ := psibar u * psi v

/-- `ψ̄_a ψ_a ψ̄_b ψ_b`. -/
def m4 (a b : Λ) : Grassmann.N Λ := psibar a * psi a * (psibar b * psi b)

theorem inv'_m4 (a b : Λ) : inv' (m4 a b) = m4 a b := by
  rw [m4, map_mul, inv'_psibar_psi, inv'_psibar_psi]

/-- The part of `G` spanned by `1`, `ψ̄_uψ_v` (`u, v ∈ {a, b}`) and `ψ̄_aψ_aψ̄_bψ_b`. -/
def proj0 (a b : Λ) (G : Grassmann.N Λ) : Grassmann.N Λ :=
  algebraMap ℂ (Grassmann.N Λ) (ε G) +
    ∑ u ∈ ({a, b} : Finset Λ), ∑ v ∈ ({a, b} : Finset Λ), coeff G ![(u, -1), (v, 1)] • m2 u v +
    coeff G ![(a, -1), (a, 1), (b, -1), (b, 1)] • m4 a b

end Proj

/-! ### The single-point operators -/

section Single

variable {c : Obs.Case}

theorem locA_add (a : Lam d L N) (X Y : Finset (Lam d L N)) (F G : Alg d L N) :
    locA c.toObs a X Y (F + G) = locA c.toObs a X Y F + locA c.toObs a X Y G := by
  cases c
  · exact locOdd_add _ _ _ _ _ _
  · exact locEven_add _ _ _ _ _

theorem locA_smul (a : Lam d L N) (X Y : Finset (Lam d L N)) (r : ℂ) (F : Alg d L N) :
    locA c.toObs a X Y (r • F) = r • locA c.toObs a X Y F := by
  cases c
  · exact locOdd_smul _ _ _ _ _ _
  · exact locEven_smul _ _ _ _ _

theorem locB_add (b : Lam d L N) (X Y : Finset (Lam d L N)) (F G : Alg d L N) :
    locB c.toObs b X Y (F + G) = locB c.toObs b X Y F + locB c.toObs b X Y G := by
  cases c
  · exact locOdd_add _ _ _ _ _ _
  · exact locEven_add _ _ _ _ _

theorem locB_smul (b : Lam d L N) (X Y : Finset (Lam d L N)) (r : ℂ) (F : Alg d L N) :
    locB c.toObs b X Y (r • F) = r • locB c.toObs b X Y F := by
  cases c
  · exact locOdd_smul _ _ _ _ _ _
  · exact locEven_smul _ _ _ _ _

theorem inv'_locA (a : Lam d L N) (X Y : Finset (Lam d L N)) (F : Alg d L N) :
    inv' (locA c.toObs a X Y F) = c.s • locA c.toObs a X Y F := by
  cases c
  · show inv' (locOdd (-1) {a} X Y F) = (-1 : ℂ) • locOdd (-1) {a} X Y F
    rw [neg_one_smul]; exact inv'_locGen_odd _ _ _ _ _
  · show inv' (locEven {a} X Y F) = (1 : ℂ) • locEven {a} X Y F
    rw [one_smul]; exact inv'_locEven _ _ _ _

theorem inv'_locB (b : Lam d L N) (X Y : Finset (Lam d L N)) (F : Alg d L N) :
    inv' (locB c.toObs b X Y F) = c.s • locB c.toObs b X Y F := by
  cases c
  · show inv' (locOdd 1 {b} X Y F) = (-1 : ℂ) • locOdd 1 {b} X Y F
    rw [neg_one_smul]; exact inv'_locGen_odd _ _ _ _ _
  · show inv' (locEven {b} X Y F) = (1 : ℂ) • locEven {b} X Y F
    rw [one_smul]; exact inv'_locEven _ _ _ _

/-- **The pointed `loc^a_{X,Y}`** (repair of the support gap): `locA` for `a ∈ X`, and the
point localisation at `a` weighted by `|Y|/|X|` for `a ∉ X`. -/
def locAp (c : Obs.Case) (a : Lam d L N) (X Y : Finset (Lam d L N)) (F : Alg d L N) : Alg d L N :=
  if a ∈ X then locA c.toObs a X Y F
  else (((Y.card : ℂ) / (X.card : ℂ))) • locA c.toObs a {a} {a} F

/-- **The pointed `loc^b_{X,Y}`**. -/
def locBp (c : Obs.Case) (b : Lam d L N) (X Y : Finset (Lam d L N)) (F : Alg d L N) : Alg d L N :=
  if b ∈ X then locB c.toObs b X Y F
  else (((Y.card : ℂ) / (X.card : ℂ))) • locB c.toObs b {b} {b} F

theorem locAp_of_mem {a : Lam d L N} {X : Finset (Lam d L N)} (Y : Finset (Lam d L N))
    (ha : a ∈ X) (F : Alg d L N) : locAp c a X Y F = locA c.toObs a X Y F := if_pos ha

theorem locAp_of_not_mem {a : Lam d L N} {X : Finset (Lam d L N)} (Y : Finset (Lam d L N))
    (ha : a ∉ X) (F : Alg d L N) :
    locAp c a X Y F = (((Y.card : ℂ) / (X.card : ℂ))) • locA c.toObs a {a} {a} F := if_neg ha

theorem locBp_of_mem {b : Lam d L N} {X : Finset (Lam d L N)} (Y : Finset (Lam d L N))
    (hb : b ∈ X) (F : Alg d L N) : locBp c b X Y F = locB c.toObs b X Y F := if_pos hb

theorem locBp_of_not_mem {b : Lam d L N} {X : Finset (Lam d L N)} (Y : Finset (Lam d L N))
    (hb : b ∉ X) (F : Alg d L N) :
    locBp c b X Y F = (((Y.card : ℂ) / (X.card : ℂ))) • locB c.toObs b {b} {b} F := if_neg hb

theorem locAp_one_of_mem {a : Lam d L N} {X : Finset (Lam d L N)} (Y : Finset (Lam d L N))
    (ha : a ∈ X) (F : Alg d L N) : locAp Obs.Case.one a X Y F = locOdd (-1) {a} X Y F := if_pos ha

theorem locAp_two_of_mem {a : Lam d L N} {X : Finset (Lam d L N)} (Y : Finset (Lam d L N))
    (ha : a ∈ X) (F : Alg d L N) : locAp Obs.Case.two a X Y F = locEven {a} X Y F := if_pos ha

theorem locBp_two_of_mem {b : Lam d L N} {X : Finset (Lam d L N)} (Y : Finset (Lam d L N))
    (hb : b ∈ X) (F : Alg d L N) : locBp Obs.Case.two b X Y F = locEven {b} X Y F := if_pos hb

theorem locAp_one_of_not_mem {a : Lam d L N} {X : Finset (Lam d L N)} (Y : Finset (Lam d L N))
    (ha : a ∉ X) (F : Alg d L N) : locAp Obs.Case.one a X Y F =
      (((Y.card : ℂ) / (X.card : ℂ))) • locOdd (-1) {a} {a} {a} F := if_neg ha

theorem locAp_two_of_not_mem {a : Lam d L N} {X : Finset (Lam d L N)} (Y : Finset (Lam d L N))
    (ha : a ∉ X) (F : Alg d L N) : locAp Obs.Case.two a X Y F =
      (((Y.card : ℂ) / (X.card : ℂ))) • locEven {a} {a} {a} F := if_neg ha

theorem locAp_add (a : Lam d L N) (X Y : Finset (Lam d L N)) (F G : Alg d L N) :
    locAp c a X Y (F + G) = locAp c a X Y F + locAp c a X Y G := by
  unfold locAp; split_ifs
  · exact locA_add _ _ _ _ _
  · rw [locA_add, smul_add]

theorem locAp_smul (a : Lam d L N) (X Y : Finset (Lam d L N)) (r : ℂ) (F : Alg d L N) :
    locAp c a X Y (r • F) = r • locAp c a X Y F := by
  unfold locAp; split_ifs
  · exact locA_smul _ _ _ _ _
  · rw [locA_smul]; exact smul_comm _ _ _

theorem locBp_add (b : Lam d L N) (X Y : Finset (Lam d L N)) (F G : Alg d L N) :
    locBp c b X Y (F + G) = locBp c b X Y F + locBp c b X Y G := by
  unfold locBp; split_ifs
  · exact locB_add _ _ _ _ _
  · rw [locB_add, smul_add]

theorem locBp_smul (b : Lam d L N) (X Y : Finset (Lam d L N)) (r : ℂ) (F : Alg d L N) :
    locBp c b X Y (r • F) = r • locBp c b X Y F := by
  unfold locBp; split_ifs
  · exact locB_smul _ _ _ _ _
  · rw [locB_smul]; exact smul_comm _ _ _

theorem locAp_zero (a : Lam d L N) (X Y : Finset (Lam d L N)) :
    locAp c a X Y (0 : Alg d L N) = 0 := by
  simpa using locAp_smul (c := c) a X Y 0 0

theorem locBp_zero (b : Lam d L N) (X Y : Finset (Lam d L N)) :
    locBp c b X Y (0 : Alg d L N) = 0 := by
  simpa using locBp_smul (c := c) b X Y 0 0

theorem inv'_locAp (a : Lam d L N) (X Y : Finset (Lam d L N)) (F : Alg d L N) :
    inv' (locAp c a X Y F) = c.s • locAp c a X Y F := by
  unfold locAp; split_ifs
  · exact inv'_locA _ _ _ _
  · rw [map_smul, inv'_locA]; exact smul_comm _ _ _

theorem inv'_locBp (b : Lam d L N) (X Y : Finset (Lam d L N)) (F : Alg d L N) :
    inv' (locBp c b X Y F) = c.s • locBp c b X Y F := by
  unfold locBp; split_ifs
  · exact inv'_locB _ _ _ _
  · rw [map_smul, inv'_locB]; exact smul_comm _ _ _

end Single

/-! ### The barycentric two-point operator -/

section Bary

theorem Mw_add (X : Finset (Lam d L N)) (a b : Lam d L N) {n : ℕ} (σ : Fin n → ℤˣ)
    (w : Fin n → Bool) (F G : Alg d L N) :
    Mw X a b σ w (F + G) = Mw X a b σ w F + Mw X a b σ w G := by
  simp only [Mw, coeff_add, add_mul, sum_add_distrib]

theorem Mw_smul (X : Finset (Lam d L N)) (a b : Lam d L N) {n : ℕ} (σ : Fin n → ℤˣ)
    (w : Fin n → Bool) (r : ℂ) (F : Alg d L N) :
    Mw X a b σ w (r • F) = r * Mw X a b σ w F := by
  simp only [Mw, coeff_smul, mul_sum, mul_assoc]

theorem Dt_add (X : Finset (Lam d L N)) (a b : Lam d L N) (F G : Alg d L N) :
    Dt X a b (F + G) = Dt X a b F + Dt X a b G := by
  simp only [Dt, Mw_add, add_smul]; abel

theorem Dt_smul (X : Finset (Lam d L N)) (a b : Lam d L N) (r : ℂ) (F : Alg d L N) :
    Dt X a b (r • F) = r • Dt X a b F := by
  simp only [Dt, Mw_smul, mul_smul, smul_add]

theorem locABt_add (X : Finset (Lam d L N)) (a b : Lam d L N) (F G : Alg d L N) :
    locABt X a b (F + G) = locABt X a b F + locABt X a b G := by
  simp only [locABt, locEven_add, Dt_add]; abel

theorem locABt_smul (X : Finset (Lam d L N)) (a b : Lam d L N) (r : ℂ) (F : Alg d L N) :
    locABt X a b (r • F) = r • locABt X a b F := by
  simp only [locABt, locEven_smul, Dt_smul, smul_add]

theorem inv'_dbar (a b : Lam d L N) : inv' (dbar a b) = -dbar a b := by
  simp only [dbar, psibar, map_sub, inv'_ψ]; abel

theorem inv'_dlt (a b : Lam d L N) : inv' (dlt a b) = -dlt a b := by
  simp only [dlt, psi, map_sub, inv'_ψ]; abel

theorem inv'_Dt (X : Finset (Lam d L N)) (a b : Lam d L N) (F : Alg d L N) :
    inv' (Dt X a b F) = Dt X a b F := by
  have hp : inv' (psi a : Alg d L N) = -psi a := by simp [psi]
  have hpb : inv' (psibar a : Alg d L N) = -psibar a := by simp [psibar]
  simp only [Dt, map_add, map_smul, map_mul, inv'_dbar, inv'_dlt, hp, hpb, pbp,
    neg_mul_neg]

theorem inv'_locABt (X : Finset (Lam d L N)) (a b : Lam d L N) (F : Alg d L N) :
    inv' (locABt X a b F) = locABt X a b F := by
  rw [locABt, map_add, inv'_locEven, inv'_Dt]

/-- The barycentric `loc^{ab,t}_X`, based at `a` if `a ∈ X` and at `b` otherwise. -/
def locABtX (X : Finset (Lam d L N)) (a b : Lam d L N) (F : Alg d L N) : Alg d L N :=
  if a ∈ X then locABt X a b F else locABt X b a F

theorem locABtX_of_mem {X : Finset (Lam d L N)} {a : Lam d L N} (b : Lam d L N) (ha : a ∈ X)
    (F : Alg d L N) : locABtX X a b F = locABt X a b F := if_pos ha

theorem locABtX_of_not_mem {X : Finset (Lam d L N)} {a : Lam d L N} (b : Lam d L N)
    (ha : a ∉ X) (F : Alg d L N) : locABtX X a b F = locABt X b a F := if_neg ha

theorem locABtX_add (X : Finset (Lam d L N)) (a b : Lam d L N) (F G : Alg d L N) :
    locABtX X a b (F + G) = locABtX X a b F + locABtX X a b G := by
  unfold locABtX; split_ifs <;> exact locABt_add _ _ _ _ _

theorem locABtX_smul (X : Finset (Lam d L N)) (a b : Lam d L N) (r : ℂ) (F : Alg d L N) :
    locABtX X a b (r • F) = r • locABtX X a b F := by
  unfold locABtX; split_ifs <;> exact locABt_smul _ _ _ _ _

theorem inv'_locABtX (X : Finset (Lam d L N)) (a b : Lam d L N) (F : Alg d L N) :
    inv' (locABtX X a b F) = locABtX X a b F := by
  unfold locABtX; split_ifs <;> exact inv'_locABt _ _ _ _

/-- **`loc^{ab}_{X,Y}` in `d = 2`** (barycentric):
`(|Y ∩ {a,b}| / |X ∩ {a,b}|) loc^{ab,t}_X F`. -/
def locABtXY (P : ObsPts d L N) (X Y : Finset (Lam d L N)) (F : Alg d L N) : Alg d L N :=
  (((Y ∩ P.pts).card : ℂ) / ((X ∩ P.pts).card : ℂ)) • locABtX X P.a P.b F

theorem locABtXY_add (P : ObsPts d L N) (X Y : Finset (Lam d L N)) (F G : Alg d L N) :
    locABtXY P X Y (F + G) = locABtXY P X Y F + locABtXY P X Y G := by
  simp only [locABtXY, locABtX_add, smul_add]

theorem locABtXY_smul (P : ObsPts d L N) (X Y : Finset (Lam d L N)) (r : ℂ) (F : Alg d L N) :
    locABtXY P X Y (r • F) = r • locABtXY P X Y F := by
  simp only [locABtXY, locABtX_smul, smul_comm r]

theorem inv'_locABtXY (P : ObsPts d L N) (X Y : Finset (Lam d L N)) (F : Alg d L N) :
    inv' (locABtXY P X Y F) = locABtXY P X Y F := by
  rw [locABtXY, map_smul, inv'_locABtX]

theorem locABtXY_zero (P : ObsPts d L N) (X Y : Finset (Lam d L N)) :
    locABtXY P X Y 0 = 0 := by
  simpa using locABtXY_smul P X Y 0 0

/-- For `X` meeting `{a, b}`, `loc^{ab}_{X,X} = loc^{ab,t}_X`. -/
theorem locABtXY_self (P : ObsPts d L N) (X : Finset (Lam d L N))
    (h : (X ∩ P.pts).Nonempty) (F : Alg d L N) : locABtXY P X X F = locABtX X P.a P.b F := by
  rw [locABtXY, div_self (Nat.cast_ne_zero.2 (card_ne_zero.2 h)), one_smul]

end Bary

/-! ### `Loc` on the algebra with sources -/

section LocO

variable {c : Obs.Case} (P : ObsPts d L N)

/-- The underlying four-tuple of `Loc_{X,Y} F`. -/
def LocS2 (X Y : Finset (Lam d L N)) (F : OE c (Lam d L N)) : SA c (Lam d L N) :=
  ⟨(Step2.Loc2E X Y (bulk F) : Alg d L N), locAp c P.a X Y (F : SA c _).a,
    locBp c P.b X Y (F : SA c _).b, locABtXY P X Y (F : SA c _).ab⟩

theorem LocS2_mem (X Y : Finset (Lam d L N)) (F : OE c (Lam d L N)) :
    LocS2 P X Y F ∈ OEv c (Lam d L N) :=
  mem_OEv.2 ⟨mem_Ev.1 (Step2.Loc2E X Y (bulk F)).2, inv'_locAp _ _ _ _, inv'_locBp _ _ _ _,
    inv'_locABtXY _ _ _ _⟩

/-- **`Loc_{X,Y}` on even elements with sources** (`d = 2`, new route; pointed `loc^a`, `loc^b`,
barycentric `loc^{ab}`). -/
def LocO2 (X Y : Finset (Lam d L N)) : OE c (Lam d L N) →ₗ[ℂ] OE c (Lam d L N) where
  toFun F := ⟨LocS2 P X Y F, LocS2_mem P X Y F⟩
  map_add' F G := by
    refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_)
    · show ((Step2.Loc2E X Y (bulk (F + G)) : Alg d L N)) = _
      rw [map_add, Step2.Loc2E_add]; rfl
    · exact locAp_add _ _ _ _ _
    · exact locBp_add _ _ _ _ _
    · exact locABtXY_add _ _ _ _ _
  map_smul' r F := by
    refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_)
    · show ((Step2.Loc2E X Y (bulk (r • F)) : Alg d L N)) = _
      rw [map_smul, Step2.Loc2E_smul]; rfl
    · exact locAp_smul _ _ _ _ _
    · exact locBp_smul _ _ _ _ _
    · exact locABtXY_smul _ _ _ _ _

@[simp] theorem coe_LocO2 (X Y : Finset (Lam d L N)) (F : OE c (Lam d L N)) :
    (LocO2 P X Y F : SA c (Lam d L N)) = LocS2 P X Y F := rfl

/-- **The bulk part of `Loc` is Step2's `Loc`.** -/
theorem bulk_LocO2 (X Y : Finset (Lam d L N)) (F : OE c (Lam d L N)) :
    bulk (LocO2 P X Y F) = Step2.Loc2E X Y (bulk F) := rfl

end LocO

end

end Obs2
