module

public import ArborealDecay.Super.DimRedTransfer
public import ArborealDecay.Super.Localization

/-!
# Dimensional reduction `ℍ^{2|4} → ℍ^{0|2}` (BCHS Proposition 2.7)

BCHS Prop. 2.7 (`refs/BCHS/src/h02.tex` L1315–1325, proof L1361–1408): for observables `F` that
are functions of the inner products `(u_i · u_j)_{i,j}` and of the `z_i`,
`[F]^{ℍ^{0|2}}_{β,h} = [F]^{ℍ^{2|4}}_{β,h}`.

* Observables are the expressions `Obs Λ` built from the atoms `u_i · u_j`, `z_i` and real
  constants by sums, products and composition with smooth functions `g : ℝ → ℝ`.  They are
  interpreted in any Grassmann algebra (`Obs.eval`): in the `ℍ^{2|4}` model pointwise in
  `p ∈ ℝ^{2Λ}` (`obsH`), and in the `ℍ^{0|2}` model of `ArborealDecay.H02` (`obs0`).
* The `ℍ^{2|4}` action is `actionH β h = ¼ ∑_{i,j} β_{ij} (u_i - u_j)² + ∑_i h_i (z_i - 1)`
  (the same formula as `H02.action`), and the unnormalised expectation is
  `expectH β h F = ∫_{(ℍ^{2|4})^Λ} F e^{-H_{β,h}}` with the BCHS superintegral
  `intH G = ∫ ∏_i dx_i dy_i/(2π) ∂_{η¹_i}∂_{ξ¹_i} ∂_{η²_i}∂_{ξ²_i} (∏_i z_i⁻¹) G`.
* `expectH_eq_expect`: if the integrand `∏ z_i⁻¹ · F e^{-H}` is in `SDecay` (BCHS: "with enough
  decay that the integrals exist"), then `expectH β h (obsH o) = H02.expect β h (obs0 o)`.

Proof (BCHS): the integrand is `Q`-closed in the variables `(x, y, ξ², η²)`, so by the
localization theorem (`integral_dual_berezin_eq`) its `(x, y, ξ², η²)`-integral is its value at
`x = y = 0, ξ² = η² = 0`.  There `z_i ↦ √(1 - 2 ξ¹_i η¹_i) = 1 - ξ¹_i η¹_i` ("`z'` localises to
`z`"), `u'_i · u'_j ↦ u_i · u_j`, and the remaining parameter Berezin integral is the `ℍ^{0|2}`
integral (`tr`, `tr_B1`, `berezin_eq_bplain`).  All `Λ` vertices are treated at once.
-/

@[expose] public section

namespace ArborealDecay.Super

noncomputable section

open MeasureTheory CliffordAlgebra Grassmann Finset
open scoped ContDiff

set_option linter.unusedSectionVars false

/-! ### `Q`-closed differentiable families -/

section QC

variable {N P : Type*} [Fintype N] [DecidableEq N] [Fintype P] [DecidableEq P]

/-- `F` is differentiable and `Q F = 0`. -/
def QC (F : Pt N → SG N P) : Prop := SDiff F ∧ ∀ p, Q F p = 0

theorem QC.algebraMap (r : ℝ) : QC fun _ : Pt N => algebraMap ℝ (SG N P) r :=
  ⟨SDiff.const _, Q_algebraMap r⟩

theorem QC.one : QC fun _ : Pt N => (1 : SG N P) := by simpa using QC.algebraMap (N := N) (P := P) 1

theorem QC.add {F G : Pt N → SG N P} (hF : QC F) (hG : QC G) : QC fun p => F p + G p :=
  ⟨hF.1.add hG.1, fun p => by rw [Q_add hF.1 hG.1, hF.2, hG.2, add_zero]⟩

theorem QC.sub {F G : Pt N → SG N P} (hF : QC F) (hG : QC G) : QC fun p => F p - G p :=
  ⟨hF.1.sub hG.1, fun p => by rw [Q_sub hF.1 hG.1, hF.2, hG.2, sub_zero]⟩

theorem QC.neg {F : Pt N → SG N P} (hF : QC F) : QC fun p => -F p :=
  ⟨hF.1.neg, fun p => by rw [Q_neg hF.1, hF.2, neg_zero]⟩

theorem QC.smul {F : Pt N → SG N P} (hF : QC F) (c : ℝ) : QC fun p => c • F p :=
  ⟨SDiff.smul (differentiable_const c) hF.1, fun p => by rw [Q_smul c hF.1, hF.2, smul_zero]⟩

theorem QC.mul {F G : Pt N → SG N P} (hF : QC F) (hG : QC G) : QC fun p => F p * G p :=
  ⟨hF.1.mul hG.1, fun p => by rw [Q_mul hF.1 hG.1, hF.2, hG.2, zero_mul, mul_zero, add_zero]⟩

theorem QC.sum {ι : Type*} (s : Finset ι) {F : ι → Pt N → SG N P} (hF : ∀ i ∈ s, QC (F i)) :
    QC fun p => ∑ i ∈ s, F i p :=
  ⟨SDiff.sum s fun i hi => (hF i hi).1, fun p => by
    rw [Q_sum s (fun i hi => (hF i hi).1)]; exact sum_eq_zero fun i hi => (hF i hi).2 p⟩

theorem QC.list_prod {ι : Type*} (l : List ι) {F : ι → Pt N → SG N P} (hF : ∀ i ∈ l, QC (F i)) :
    QC fun p => (l.map fun i => F i p).prod := by
  induction l with
  | nil => simpa using QC.one
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (hF i List.mem_cons_self).mul (ih fun j hj => hF j (List.mem_cons_of_mem _ hj))

theorem QC.scomp {g : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    {S : Pt N → SG N P} (hS : QC S) (hE : ∀ p, IsEven (S p)) (hb : ∀ p, body (S p) ∈ U) :
    QC fun p => Super.scomp g (S p) :=
  ⟨SDiff.scomp hU hg hS.1 hE hb, fun p => by rw [Q_scomp hU hg hS.1 hE hb, hS.2, mul_zero]⟩

end QC

namespace H24

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ### Observables -/

/-- Observables built from the inner products `u_i · u_j` and the `z_i`: real constants, sums,
products and compositions with smooth functions. -/
inductive Obs (Λ : Type*) where
  /-- The inner product `u_i · u_j`. -/
  | dot (i j : Λ) : Obs Λ
  /-- The coordinate `z_i`. -/
  | z (i : Λ) : Obs Λ
  /-- A real constant. -/
  | const (c : ℝ) : Obs Λ
  /-- A sum. -/
  | add (a b : Obs Λ) : Obs Λ
  /-- A product. -/
  | mul (a b : Obs Λ) : Obs Λ
  /-- The composition `g(a)` with a smooth `g : ℝ → ℝ`. -/
  | comp (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (a : Obs Λ) : Obs Λ

namespace Obs

/-- The value of an observable, given values `d i j` of `u_i · u_j` and `zz i` of `z_i`. -/
def eval {O : Type*} (d : Λ → Λ → Gr O) (zz : Λ → Gr O) : Obs Λ → Gr O
  | dot i j => d i j
  | z i => zz i
  | const c => algebraMap ℝ (Gr O) c
  | add a b => eval d zz a + eval d zz b
  | mul a b => eval d zz a * eval d zz b
  | comp g _ a => Super.scomp g (eval d zz a)

theorem isEven_eval {O : Type*} {d : Λ → Λ → Gr O} {zz : Λ → Gr O}
    (hd : ∀ i j, IsEven (d i j)) (hz : ∀ i, IsEven (zz i)) (o : Obs Λ) : IsEven (o.eval d zz) := by
  induction o with
  | dot i j => exact hd i j
  | z i => exact hz i
  | const c => exact IsEven.algebraMap c
  | add a b ha hb => exact ha.add hb
  | mul a b ha hb => exact ha.mul hb
  | comp g _ a ha => exact ha.scomp g

theorem map_eval {O O' : Type*} [Fintype O] [DecidableEq O] (φ : Gr O →ₐ[ℝ] Gr O')
    (hφ : ∀ x, body (φ x) = body x) {d : Λ → Λ → Gr O} {zz : Λ → Gr O}
    (hd : ∀ i j, IsEven (d i j)) (hz : ∀ i, IsEven (zz i)) (o : Obs Λ) :
    φ (o.eval d zz) = o.eval (fun i j => φ (d i j)) (fun i => φ (zz i)) := by
  induction o with
  | dot i j => rfl
  | z i => rfl
  | const c => exact AlgHom.commutes φ c
  | add a b ha hb => simp only [eval, map_add, ha, hb]
  | mul a b ha hb => simp only [eval, map_mul, ha, hb]
  | comp g _ a ha =>
    simp only [eval]
    rw [map_scomp φ hφ g (isNilpotent_soul (isEven_eval hd hz a)), ha]

theorem qc_eval {N P : Type*} [Fintype N] [DecidableEq N] [Fintype P] [DecidableEq P]
    {D : Pt N → Λ → Λ → SG N P} {Z : Pt N → Λ → SG N P}
    (hD : ∀ i j, QC fun p => D p i j) (hZ : ∀ i, QC fun p => Z p i)
    (hDE : ∀ p i j, IsEven (D p i j)) (hZE : ∀ p i, IsEven (Z p i)) (o : Obs Λ) :
    QC fun p => o.eval (D p) (Z p) := by
  induction o with
  | dot i j => exact hD i j
  | z i => exact hZ i
  | const c => exact QC.algebraMap c
  | add a b ha hb => exact ha.add hb
  | mul a b ha hb => exact ha.mul hb
  | comp g hg a ha =>
    exact QC.scomp isOpen_univ hg.contDiffOn ha
      (fun p => isEven_eval (hDE p) (hZE p) a) (fun _ => Set.mem_univ _)

end Obs

/-! ### The `ℍ^{2|4}` model -/

/-- The action `H_{β,h} = ¼ ∑_{i,j} β_{ij} (u_i - u_j)² + ∑_i h_i (z_i - 1)` of the `ℍ^{2|4}`
model (BCHS (2.42); same formula as `H02.action`). -/
def actionH (β : Λ → Λ → ℝ) (h : Λ → ℝ) (p : Pt Λ) : A Λ :=
  (1 / 4 : ℝ) • ∑ i, ∑ j, β i j • (dotH i i p - dotH i j p - dotH j i p + dotH j j p) +
    ∑ i, h i • (zH i p - 1)

/-- `∏_i z_i⁻¹`. -/
def zinvProd (p : Pt Λ) : A Λ :=
  ((Finset.univ : Finset Λ).toList.map fun i => Ring.inverse (zH i p)).prod

/-- The `ℍ^{2|4}` superintegral (BCHS, display after (2.43), `n = m = 2`):
`∫_{(ℍ^{2|4})^Λ} G = ∫_{ℝ^{2Λ}} ∏_i (dx_i dy_i / 2π) ∂_{η¹_i}∂_{ξ¹_i} ∂_{η²_i}∂_{ξ²_i}
(∏_i z_i⁻¹) G`.  The pair operators `∂_η∂_ξ` are even and commute, so we apply first all
`∂_{η²_i}∂_{ξ²_i}` (`berezin`) and then all `∂_{η¹_i}∂_{ξ¹_i}` (`B1`); `body` reads off the
resulting real number. -/
def intH (G : Pt Λ → A Λ) : ℝ :=
  ((2 * Real.pi) ^ Fintype.card Λ)⁻¹ *
    ∫ p, body (B1 (Finset.univ : Finset Λ).toList (berezin (zinvProd p * G p)))

/-- The unnormalised `ℍ^{2|4}` expectation `[F]^{ℍ^{2|4}}_{β,h} = ∫ F e^{-H_{β,h}}`
(BCHS (2.43)). -/
def expectH (β : Λ → Λ → ℝ) (h : Λ → ℝ) (F : Pt Λ → A Λ) : ℝ :=
  intH fun p => F p * scomp Real.exp (-actionH β h p)

/-- An observable in the `ℍ^{2|4}` model. -/
def obsH (o : Obs Λ) (p : Pt Λ) : A Λ := o.eval (fun i j => dotH i j p) (fun i => zH i p)

/-- An observable in the `ℍ^{0|2}` model. -/
def obs0 (o : Obs Λ) : H02.Grassmann Λ := o.eval H02.dot H02.z

/-- The `ℍ^{2|4}` integrand `∏_i z_i⁻¹ · F e^{-H_{β,h}}` of a superfunction `F`, as a function on
`ℝ^{2Λ}`. -/
def integrandF (β : Λ → Λ → ℝ) (h : Λ → ℝ) (F : Pt Λ → A Λ) (p : Pt Λ) : A Λ :=
  zinvProd p * (F p * scomp Real.exp (-actionH β h p))

/-- The `ℍ^{2|4}` integrand of an observable. -/
def integrandH (β : Λ → Λ → ℝ) (h : Λ → ℝ) (o : Obs Λ) : Pt Λ → A Λ :=
  integrandF β h (obsH o)

theorem expectH_eq_intH (β : Λ → Λ → ℝ) (h : Λ → ℝ) (F : Pt Λ → A Λ) :
    expectH β h F = ((2 * Real.pi) ^ Fintype.card Λ)⁻¹ *
      ∫ p, body (B1 (Finset.univ : Finset Λ).toList (berezin (integrandF β h F p))) := by
  simp only [expectH, intH, integrandF]

/-! ### Parity and `Q`-closedness -/

theorem qc_zH (i : Λ) : QC (zH i) := ⟨sdiff_zH i, Q_zH i⟩

theorem qc_dotH (i j : Λ) : QC (dotH i j) := ⟨sdiff_dotH i j, Q_dotH i j⟩

theorem isEven_actionH (β : Λ → Λ → ℝ) (h : Λ → ℝ) (p : Pt Λ) : IsEven (actionH β h p) := by
  refine (IsEven.sum _ fun i _ => IsEven.sum _ fun j _ => ?_).smul _ |>.add
    (IsEven.sum _ fun i _ => ((isEven_zH i p).sub IsEven.one).smul _)
  exact ((((isEven_dotH i i p).sub (isEven_dotH i j p)).sub (isEven_dotH j i p)).add
    (isEven_dotH j j p)).smul _

theorem qc_actionH (β : Λ → Λ → ℝ) (h : Λ → ℝ) : QC (actionH β h) := by
  refine QC.add (QC.smul (QC.sum _ fun i _ => QC.sum _ fun j _ => ?_) _)
    (QC.sum _ fun i _ => QC.smul (QC.sub (qc_zH i) QC.one) _)
  exact QC.smul ((((qc_dotH i i).sub (qc_dotH i j)).sub (qc_dotH j i)).add (qc_dotH j j)) _

theorem inverse_zH (i : Λ) (p : Pt Λ) :
    Ring.inverse (zH i p) = scomp (fun t : ℝ => t⁻¹) (zH i p) :=
  inverse_eq_scomp_inv (isNilpotent_soul (isEven_zH i p)) (body_zH_pos i p).ne'

theorem qc_zinv (i : Λ) : QC fun p => Ring.inverse (zH i p) := by
  simp_rw [inverse_zH]
  exact QC.scomp isOpen_Ioi contDiffOn_inv (qc_zH i) (isEven_zH i) (body_zH_pos i)

theorem qc_zinvProd : QC (zinvProd : Pt Λ → A Λ) :=
  QC.list_prod _ fun i _ => qc_zinv i

theorem qc_integrandF (β : Λ → Λ → ℝ) (h : Λ → ℝ) {F : Pt Λ → A Λ} (hF : QC F) :
    QC (integrandF β h F) :=
  qc_zinvProd.mul (hF.mul
    (QC.scomp isOpen_univ Real.contDiff_exp.contDiffOn (qc_actionH β h).neg
      (fun p => (isEven_actionH β h p).neg) (fun _ => Set.mem_univ _)))

theorem qc_obsH (o : Obs Λ) : QC (obsH o) :=
  Obs.qc_eval (D := fun p i j => dotH i j p) (Z := fun p i => zH i p)
    (fun i j => qc_dotH i j) (fun i => qc_zH i) (fun p i j => isEven_dotH i j p)
    (fun p i => isEven_zH i p) o

theorem qc_integrandH (β : Λ → Λ → ℝ) (h : Λ → ℝ) (o : Obs Λ) : QC (integrandH β h o) :=
  qc_integrandF β h (qc_obsH o)

/-! ### Values at the origin under the transfer map -/

@[simp] theorem body_H02ξ (i : Λ) : body (H02.ξ i : H02.Grassmann Λ) = 0 := body_ι _
@[simp] theorem body_H02η (i : Λ) : body (H02.η i : H02.Grassmann Λ) = 0 := body_ι _

theorem tr_Rz_zero (i : Λ) :
    tr (Rz i 0) = 1 - (2 : ℝ) • (H02.ξ i * H02.η i : H02.Grassmann Λ) := by
  simp [Rz, map_sub, map_smul, map_mul]

/-- "`z'` localises to `z`": `√(1 - 2 ξ_i η_i) = 1 - ξ_i η_i`. -/
theorem tr_zH_zero (i : Λ) : tr (zH i 0) = H02.z i := by
  rw [zH, tr_scomp _ (isEven_Rz i 0), tr_Rz_zero]
  set a : H02.Grassmann Λ := 1 - (2 : ℝ) • (H02.ξ i * H02.η i)
  have hb : body a = 1 := by simp [a]
  have hs : soul a = -((2 : ℝ) • (H02.ξ i * H02.η i)) := by
    simp only [soul, hb, map_one, a]; abel
  have hsq : soul a * soul a = 0 := by
    rw [hs, neg_mul_neg, smul_mul_smul_comm, H02.ξη_sq, smul_zero]
  rw [scomp_of_soul_sq _ hsq, hb, hs, (Real.hasDerivAt_sqrt one_ne_zero).deriv, Real.sqrt_one,
    map_one, H02.z]
  rw [smul_neg, smul_smul]
  norm_num [sub_eq_add_neg]

theorem tr_dotH_zero (i j : Λ) : tr (dotH i j 0) = H02.dot i j := by
  rw [dotH, H02.dot]
  simp only [map_sub, map_add, map_mul, tr_ξ1, tr_η1, tr_ξ, tr_η, tr_zH_zero,
    Pi.zero_apply, mul_zero, add_zero, zero_smul, zero_add, sub_zero]
  rw [H02.η_anticomm_ξ]
  abel

theorem tr_obsH_zero (o : Obs Λ) : tr (obsH o 0) = obs0 o := by
  rw [obsH, Obs.map_eval tr body_tr (fun i j => isEven_dotH i j 0) (fun i => isEven_zH i 0)]
  simp only [tr_dotH_zero, tr_zH_zero]
  rfl

theorem tr_actionH_zero (β : Λ → Λ → ℝ) (h : Λ → ℝ) : tr (actionH β h 0) = H02.action β h := by
  simp only [actionH, H02.action, map_add, map_smul, map_sum, map_sub, map_one, tr_dotH_zero,
    tr_zH_zero]

theorem body_H02dot (i j : Λ) : body (H02.dot i j) = -1 := by
  simp [H02.dot, H02.z]

theorem body_H02action (β : Λ → Λ → ℝ) (h : Λ → ℝ) : body (H02.action β h) = 0 := by
  simp [H02.action, map_sum, body_H02dot, H02.z]

theorem tr_inverse_zH_zero (i : Λ) :
    tr (Ring.inverse (zH i 0)) = 1 + H02.ξ i * H02.η i := by
  have hE : IsEven (H02.z i : H02.Grassmann Λ) := by rw [← tr_zH_zero]; exact isEven_tr (isEven_zH i 0)
  rw [inverse_zH, tr_scomp _ (isEven_zH i 0), tr_zH_zero,
    ← inverse_eq_scomp_inv (isNilpotent_soul hE) (by simp [H02.z]), H02.inverse_z]

theorem tr_zinvProd_zero : tr (zinvProd (0 : Pt Λ)) = wprod (Finset.univ : Finset Λ).toList := by
  rw [zinvProd, map_list_prod, List.map_map, wprod]
  congr 1
  exact List.map_congr_left fun i _ => tr_inverse_zH_zero i

theorem tr_exp_zero (β : Λ → Λ → ℝ) (h : Λ → ℝ) :
    tr (scomp Real.exp (-actionH β h 0)) = IsNilpotent.exp (-H02.action β h) := by
  have hE : IsEven (-H02.action β h) := by
    rw [← tr_actionH_zero, ← map_neg]; exact isEven_tr (isEven_actionH β h 0).neg
  have hb : body (-H02.action β h) = 0 := by rw [map_neg, body_H02action, neg_zero]
  have hN : IsNilpotent (-H02.action β h) := by
    have := isNilpotent_soul hE; rwa [soul_of_body_eq_zero hb] at this
  rw [tr_scomp _ (isEven_actionH β h 0).neg, map_neg, tr_actionH_zero,
    scomp_exp_of_body_eq_zero hN hb]

theorem tr_integrandF_zero (β : Λ → Λ → ℝ) (h : Λ → ℝ) (F : Pt Λ → A Λ) :
    tr (integrandF β h F 0) = wprod (Finset.univ : Finset Λ).toList *
      (tr (F 0) * IsNilpotent.exp (-H02.action β h)) := by
  rw [integrandF, map_mul, map_mul, tr_zinvProd_zero, tr_exp_zero]

/-! ### Localization of `Q`-closed observables -/

/-- **Localization in `(x, y, ξ², η²)`**: for a `Q`-closed superfunction `F` whose integrand
decays, the `ℍ^{2|4}` expectation of `F` is the `ℍ^{0|2}` expectation of the transfer of
`F(0)`. -/
theorem expectH_eq_of_qc (β : Λ → Λ → ℝ) (h : Λ → ℝ) {F : Pt Λ → A Λ} (hF : QC F)
    (hdec : SDecay (integrandF β h F)) :
    expectH β h F = H02.expect β h (tr (F 0)) := by
  set l := (Finset.univ : Finset Λ).toList
  set ℓ : Module.Dual ℝ (A Λ) := body.toLinearMap ∘ₗ B1 l
  have hint : ∫ p, ℓ (berezin (integrandF β h F p)) =
      (2 * Real.pi) ^ Fintype.card Λ * ℓ (pi0 (integrandF β h F 0)) :=
    integral_dual_berezin_eq hdec (qc_integrandF β h hF).2 ℓ
  have hpi : (0 : ℝ) < (2 * Real.pi) ^ Fintype.card Λ := by positivity
  have e1 : expectH β h F =
      ((2 * Real.pi) ^ Fintype.card Λ)⁻¹ * ∫ p, ℓ (berezin (integrandF β h F p)) := by
    rw [expectH_eq_intH]; rfl
  rw [e1, hint, ← mul_assoc, inv_mul_cancel₀ hpi.ne', one_mul]
  simp only [ℓ, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply]
  rw [← body_tr, tr_B1, tr_pi0, tr_integrandF_zero, H02.expect, H02.int0,
    berezin_eq_bplain (Finset.nodup_toList _)]
  rfl

/-! ### Dimensional reduction -/

/-- **BCHS Proposition 2.7 (dimensional reduction).**  For every observable `o` built from the
inner products `u_i · u_j` and the `z_i` (by constants, sums, products and smooth functions),
if the `ℍ^{2|4}` integrand `∏_i z_i⁻¹ · o e^{-H_{β,h}}` is in `SDecay` ("enough decay that the
integrals exist"), then `[o]^{ℍ^{2|4}}_{β,h} = [o]^{ℍ^{0|2}}_{β,h}`. -/
theorem expectH_eq_expect (β : Λ → Λ → ℝ) (h : Λ → ℝ) (o : Obs Λ)
    (hdec : SDecay (integrandH β h o)) :
    expectH β h (obsH o) = H02.expect β h (obs0 o) := by
  rw [expectH_eq_of_qc β h (qc_obsH o) hdec, tr_obsH_zero]

end H24

end

end ArborealDecay.Super

end
