import Step.SymAlg
import Step.SymGeom
import Step.Polymers
import Loc.LocImage

/-!
# The coupling constants `(u_{j+1}, V_{j+1})` (Definition `def:V+`)

* Small sets satisfy the hypotheses of Proposition `prop:Loc` (iv) (`region_small`).
* `𝔼_C θ V(X) ∈ (ℂ ⊕ 𝒱^∅)(X)` for covariances invariant under the lattice automorphisms
  (`EC_theta_eval_mem`).
* `Q(B)` is equivariant (`Qb_img`) and lies in `(ℂ ⊕ 𝒱^∅)(B)` (`Qb_mem`, using
  Proposition `prop:Loc` (iv), (v)).
* Hence `𝔼_C θ (V_j(B) - Q(B)) = u_{j+1}|B| + V_{j+1}(B)` for *every* block `B`
  (`uVnext_spec`), with `(u_{j+1}, V_{j+1})` read off at one block.
-/

namespace Step

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

/-! ### Wick computations -/

namespace Coup

section Wick

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ] (C : Matrix Λ Λ ℝ)

local notation "ι" => ExteriorAlgebra.ι ℂ

/-- The pairing `(v, w) ↦ ℒ_C (v w)` of two elements of degree one. -/
def Bf (v w : V Λ) : ℂ := ∑ x, ∑ y, (C x y : ℂ) * (v (x, -1) * w (y, 1) - v (y, 1) * w (x, -1))

/-- The first order part of `ℒ_C (v F)`. -/
def Pd (v : V Λ) (F : Grassmann.N Λ) : Grassmann.N Λ :=
  ∑ x, ∑ y, (C x y : ℂ) • (v (x, -1) • D (y, 1) F - v (y, 1) • D (x, -1) F)

theorem D_ι_mul' (a : Sf Λ) (v : V Λ) (F : Grassmann.N Λ) : D a (ι v * F) = v a • F - ι v * D a F :=
  CliffordAlgebra.contractLeft_ι_mul _ _ _

theorem D_ι' (a : Sf Λ) (v : V Λ) : D a (ι v) = algebraMap ℂ (Grassmann.N Λ) (v a) :=
  CliffordAlgebra.contractLeft_ι _ _ _

theorem Lop_ι_mul (v : V Λ) (F : Grassmann.N Λ) : Lop C (ι v * F) = ι v * Lop C F + Pd C v F := by
  simp only [Lop_apply, Pd, D_ι_mul', map_sub, map_smul, mul_sum, mul_smul_comm, ← sum_add_distrib]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  rw [← smul_add]; congr 1; abel

theorem Pd_ι_mul (v w : V Λ) (F : Grassmann.N Λ) : Pd C v (ι w * F) = Bf C v w • F - ι w * Pd C v F := by
  simp only [Pd, Bf, D_ι_mul', smul_sub, mul_sum, mul_smul_comm, mul_sub, sum_smul, ← sum_sub_distrib,
    smul_smul, sub_smul]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  abel

theorem Pd_ι (v w : V Λ) : Pd C v (ι w) = algebraMap ℂ (Grassmann.N Λ) (Bf C v w) := by
  have := Pd_ι_mul C v w 1
  rw [mul_one] at this
  rw [this]
  have h0 : Pd C v 1 = 0 := by simp [Pd]
  rw [h0, mul_zero, sub_zero, Algebra.algebraMap_eq_smul_one]

theorem Lop_one' : Lop C (1 : Grassmann.N Λ) = 0 := by simp [Lop_apply]

theorem Lop_algebraMap (r : ℂ) : Lop C (algebraMap ℂ (Grassmann.N Λ) r) = 0 := by
  simp [Lop_apply, D_algebraMap]

theorem Lop_ι (w : V Λ) : Lop C (ι w) = 0 := by
  simp [Lop_apply, D_ι', D_algebraMap]

theorem Lop_ι2 (v w : V Λ) : Lop C (ι v * ι w) = Bf C v w • (1 : Grassmann.N Λ) := by
  rw [Lop_ι_mul, Lop_ι, mul_zero, zero_add, Pd_ι, Algebra.algebraMap_eq_smul_one]

theorem Lop_ι3 (a b c : V Λ) : Lop C (ι a * (ι b * ι c)) =
    Bf C b c • ι a + Bf C a b • ι c - Bf C a c • ι b := by
  rw [Lop_ι_mul, Lop_ι2, Pd_ι_mul, Pd_ι, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one,
    mul_smul_comm, mul_one]
  abel

theorem Lop_ι4 (a b c e : V Λ) : Lop C (ι a * (ι b * (ι c * ι e))) =
    Bf C c e • (ι a * ι b) + Bf C b c • (ι a * ι e) - Bf C b e • (ι a * ι c) +
    Bf C a b • (ι c * ι e) - Bf C a c • (ι b * ι e) + Bf C a e • (ι b * ι c) := by
  rw [Lop_ι_mul, Lop_ι3, Pd_ι_mul, Pd_ι_mul, Pd_ι, Algebra.algebraMap_eq_smul_one]
  simp only [mul_add, mul_sub, mul_smul_comm, mul_one]
  abel

end Wick

section Lat

local notation "ι" => ExteriorAlgebra.ι ℂ

theorem Bf_sub_left (C : Matrix (Lam d L N) (Lam d L N) ℝ) (v v' w : V (Lam d L N)) :
    Bf C (v - v') w = Bf C v w - Bf C v' w := by
  simp only [Bf, ← sum_sub_distrib]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  simp only [Pi.sub_apply]; ring

theorem Bf_sub_right (C : Matrix (Lam d L N) (Lam d L N) ℝ) (v w w' : V (Lam d L N)) :
    Bf C v (w - w') = Bf C v w - Bf C v w' := by
  simp only [Bf, ← sum_sub_distrib]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  simp only [Pi.sub_apply]; ring

theorem Bf_pq (C : Matrix (Lam d L N) (Lam d L N) ℝ) (u w : Lam d L N) :
    Bf C (ev (u, 1)) (ev (w, -1)) = -(C w u : ℂ) := by
  simp [Bf, ev, Pi.single_apply, Prod.ext_iff, units_ne.symm]

theorem Bf_qp (C : Matrix (Lam d L N) (Lam d L N) ℝ) (u w : Lam d L N) :
    Bf C (ev (u, -1)) (ev (w, 1)) = (C u w : ℂ) := by
  simp [Bf, ev, Pi.single_apply, Prod.ext_iff, units_ne.symm]

theorem Bf_pp (C : Matrix (Lam d L N) (Lam d L N) ℝ) (u w : Lam d L N) :
    Bf C (ev (u, 1)) (ev (w, 1)) = 0 := by
  simp [Bf, ev, Pi.single_apply, Prod.ext_iff, units_ne.symm]

theorem Bf_qq (C : Matrix (Lam d L N) (Lam d L N) ℝ) (u w : Lam d L N) :
    Bf C (ev (u, -1)) (ev (w, -1)) = 0 := by
  simp [Bf, ev, Pi.single_apply, Prod.ext_iff]

theorem card_dir : Fintype.card (Dir d) = 2 * d := by
  simp [Dir]; ring

theorem sum_dir_const {M : Type*} [AddCommGroup M] [Module ℂ M] (r : ℂ) (F : M) :
    ∑ _e : Dir d, r • F = (2 * d * r) • F := by
  rw [sum_const, card_univ, card_dir, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]; push_cast; ring_nf

theorem sum_dir_neg {M : Type*} [AddCommMonoid M] (f : Lam d L N → M) (x : Lam d L N) :
    ∑ e : Dir d, f (x - dirVec e) = ∑ e : Dir d, f (x + dirVec e) := by
  refine Fintype.sum_equiv (Equiv.sumComm _ _) _ _ fun e => ?_
  rw [Equiv.sumComm_apply, dirVec_swap, sub_eq_add_neg]

theorem lapPsi_eq_sum (x : Lam d L N) : lapPsi x = ∑ e, grad e x := by
  have h := sum_dir_neg (fun y => psi y) x
  simp only [lapPsi, grad, sub_add_cancel, sum_sub_distrib, h]
  simp only [sum_const, card_univ]
  module

theorem lapPsibar_eq_sum (x : Lam d L N) : lapPsibar x = ∑ e, gradbar e x := by
  have h := sum_dir_neg (fun y => psibar y) x
  simp only [lapPsibar, gradbar, sub_add_cancel, sum_sub_distrib, h]
  simp only [sum_const, card_univ]
  module

/-- The summand of `V(X)`. -/
def Vsum (V : Vcoup) (x : Lam d L N) : Alg d L N :=
  V.y • gradSq x + (V.z / 2) • ((-lapPsi x) * psibar x + psi x * (-lapPsibar x)) +
    V.a • (psi x * psibar x) + V.b • (psi x * psibar x * gradSq x)

theorem eval_eq_sum (V : Vcoup) (X : Finset (Lam d L N)) : V.eval X = ∑ x ∈ X, Vsum V x := rfl

/-- Linear combinations of coupling constants. -/
def Vlin (r s : ℂ) (V W : Vcoup) : Vcoup :=
  ⟨r * V.z + s * W.z, r * V.y + s * W.y, r * V.a + s * W.a, r * V.b + s * W.b⟩

theorem Vsum_lin (r s : ℂ) (V W : Vcoup) (x : Lam d L N) :
    Vsum (Vlin r s V W) x = r • Vsum V x + s • Vsum W x := by
  simp only [Vsum, Vlin, add_smul, smul_add, smul_smul, add_div, mul_div_assoc]
  abel

theorem eval_lin (r s : ℂ) (V W : Vcoup) (X : Finset (Lam d L N)) :
    (Vlin r s V W).eval X = r • V.eval X + s • W.eval X := by
  simp only [eval_eq_sum, Vsum_lin, sum_add_distrib, smul_sum]

theorem Vsum_zero (x : Lam d L N) : Vsum (d := d) (L := L) (N := N) ⟨0, 0, 0, 0⟩ x = 0 := by
  simp [Vsum]

theorem psi_eq (x : Lam d L N) : psi x = ι (ev (x, 1)) := rfl
theorem psibar_eq (x : Lam d L N) : psibar x = ι (ev (x, -1)) := rfl
theorem grad_eq (e : Dir d) (x : Lam d L N) :
    grad e x = ι (ev (x + dirVec e, 1) - ev (x, 1)) := by rw [map_sub]; rfl
theorem gradbar_eq (e : Dir d) (x : Lam d L N) :
    gradbar e x = ι (ev (x + dirVec e, -1) - ev (x, -1)) := by rw [map_sub]; rfl

section Comp

variable (C : Matrix (Lam d L N) (Lam d L N) ℝ) (c0 c1 : ℂ) (hc0 : ∀ x, (C x x : ℂ) = c0)
  (hc1 : ∀ x e, (C x (x + dirVec e) : ℂ) = c1) (hc1' : ∀ x e, (C (x + dirVec e) x : ℂ) = c1)
include hc0 hc1 hc1'


theorem Lop_grad_gradbar (e : Dir d) (x : Lam d L N) :
    Lop C (grad e x * gradbar e x) = (2 * (c1 - c0)) • (1 : Alg d L N) := by
  rw [grad_eq, gradbar_eq, Lop_ι2, Bf_sub_left, Bf_sub_right, Bf_sub_right, Bf_pq, Bf_pq, Bf_pq,
    Bf_pq, hc0, hc0, hc1, hc1']
  congr 1; ring

theorem Lop_gradSq (x : Lam d L N) : Lop C (gradSq x) = (2 * d * (c1 - c0)) • (1 : Alg d L N) := by
  rw [gradSq, map_smul, map_sum]
  simp only [Lop_grad_gradbar C c0 c1 hc0 hc1 hc1', sum_dir_const, smul_smul]
  congr 1; ring

theorem Lop_psi_psibar (x : Lam d L N) :
    Lop C (psi x * psibar x) = (-c0) • (1 : Alg d L N) := by
  rw [psi_eq, psibar_eq, Lop_ι2, Bf_pq, hc0]

theorem Lop_lap (x : Lam d L N) :
    Lop C ((-lapPsi x) * psibar x + psi x * (-lapPsibar x)) =
      (4 * d * (c1 - c0)) • (1 : Alg d L N) := by
  simp only [lapPsi_eq_sum, lapPsibar_eq_sum, neg_mul, mul_neg, sum_mul, mul_sum, map_add, map_neg,
    map_sum, grad_eq, gradbar_eq, psi_eq, psibar_eq, Lop_ι2, Bf_sub_left, Bf_sub_right,
    Bf_pq, hc0, hc1, hc1', sum_dir_const, ← neg_smul, ← add_smul]
  congr 1; ring

theorem Lop_quart (x : Lam d L N) :
    Lop C (psi x * psibar x * gradSq x) = (-c0) • gradSq x +
      ((c0 - c1) / 2) • ((-lapPsi x) * psibar x + psi x * (-lapPsibar x)) +
      (2 * d * (c1 - c0)) • (psi x * psibar x) := by
  have key : ∀ e : Dir d, Lop C (psi x * (psibar x * (grad e x * gradbar e x))) =
      (-c0) • (grad e x * gradbar e x) + (c0 - c1) • (-(grad e x * psibar x) +
        psi x * (-gradbar e x)) + (2 * (c1 - c0)) • (psi x * psibar x) := by
    intro e
    have hbc : psibar x * grad e x = -(grad e x * psibar x) := by
      rw [psibar_eq, grad_eq]; exact ι_anticomm _ _
    rw [psi_eq, psibar_eq, grad_eq, gradbar_eq, Lop_ι4]
    rw [← psi_eq, ← psibar_eq, ← grad_eq, ← gradbar_eq, hbc]
    simp only [Bf_sub_left, Bf_sub_right, Bf_pq, Bf_qp, Bf_pp, Bf_qq, hc0, hc1, hc1']
    simp only [mul_neg]
    module
  simp only [gradSq, mul_smul_comm, mul_sum, map_smul, map_sum, mul_assoc, key, sum_add_distrib,
    lapPsi_eq_sum, lapPsibar_eq_sum, neg_mul, mul_neg, sum_mul, ← smul_sum,
    sum_neg_distrib]
  rw [sum_const, card_univ, card_dir, ← Nat.cast_smul_eq_nsmul ℂ]
  push_cast
  module

/-- The constant produced by `ℒ_C` from `V(x)`. -/
def kf (d : ℕ) (c0 c1 : ℂ) (V : Vcoup) : ℂ :=
  2 * d * (c1 - c0) * V.y + 2 * d * (c1 - c0) * V.z - c0 * V.a

/-- The quadratic part produced by `ℒ_C` from `V(x)`. -/
def Wf (d : ℕ) (c0 c1 : ℂ) (V : Vcoup) : Vcoup :=
  ⟨V.b * (c0 - c1), -V.b * c0, V.b * (2 * d * (c1 - c0)), 0⟩

theorem Lop_Vsum (V : Vcoup) (x : Lam d L N) :
    Lop C (Vsum V x) = kf d c0 c1 V • (1 : Alg d L N) + Vsum (Wf d c0 c1 V) x := by
  simp only [Vsum, map_add, map_smul, Lop_gradSq C c0 c1 hc0 hc1 hc1', Lop_lap C c0 c1 hc0 hc1 hc1',
    Lop_psi_psibar C c0 c1 hc0 hc1 hc1', Lop_quart C c0 c1 hc0 hc1 hc1', kf, Wf]
  module

theorem Lop_eval (V : Vcoup) (X : Finset (Lam d L N)) :
    Lop C (V.eval X) = (kf d c0 c1 V * X.card) • (1 : Alg d L N) + (Wf d c0 c1 V).eval X := by
  rw [eval_eq_sum, map_sum]
  simp only [Lop_Vsum C c0 c1 hc0 hc1 hc1', sum_add_distrib, sum_const, ← Nat.cast_smul_eq_nsmul ℂ,
    smul_smul, eval_eq_sum]
  rw [mul_comm]

omit hc0 hc1 hc1' in
theorem expL_of_cube (F : Alg d L N) (h : Lop C (Lop C (Lop C F)) = 0) :
    expL C F = F + Lop C F + (1 / 2 : ℂ) • Lop C (Lop C F) := by
  have hk : (Lop C ^ 3) • F = 0 := by
    rw [Module.End.smul_def, pow_succ, pow_two, Module.End.mul_apply, Module.End.mul_apply]
    exact h
  have := IsNilpotent.exp_smul_eq_sum hk (Lop_isNilpotent C)
  rw [Module.End.smul_def] at this
  rw [expL, this]
  simp only [sum_range_succ, sum_range_zero, Module.End.smul_def, pow_zero, pow_one, pow_two,
    Module.End.mul_apply, Module.End.one_apply]
  rw [← Rat.cast_smul_eq_qsmul ℂ, ← Rat.cast_smul_eq_qsmul ℂ, ← Rat.cast_smul_eq_qsmul ℂ]
  norm_num

theorem Wf_Wf_eval (V : Vcoup) (X : Finset (Lam d L N)) :
    (Wf d c0 c1 (Wf d c0 c1 V)).eval X = 0 := by
  simp [eval_eq_sum, Vsum, Wf]

omit hc0 hc1 hc1' in
theorem Lop_const (r : ℂ) : Lop C (r • (1 : Alg d L N)) = 0 := by
  rw [map_smul, Lop_one', smul_zero]

theorem Lop2_eval (V : Vcoup) (X : Finset (Lam d L N)) :
    Lop C (Lop C (V.eval X)) = (kf d c0 c1 (Wf d c0 c1 V) * X.card) • (1 : Alg d L N) := by
  rw [Lop_eval C c0 c1 hc0 hc1 hc1', map_add, Lop_const, Lop_eval C c0 c1 hc0 hc1 hc1',
    Wf_Wf_eval C c0 c1 hc0 hc1 hc1', zero_add, add_zero]

/-- `𝔼_C θ V(X) = e^{ℒ_C} V(X) = u|X| + V'(X)`. -/
theorem expL_eval (V : Vcoup) (X : Finset (Lam d L N)) :
    expL C (V.eval X) = ((kf d c0 c1 V + kf d c0 c1 (Wf d c0 c1 V) / 2) * X.card) •
      (1 : Alg d L N) + (Vlin 1 1 V (Wf d c0 c1 V)).eval X := by
  have h1 := Lop_eval C c0 c1 hc0 hc1 hc1' V X
  have h2 := Lop2_eval C c0 c1 hc0 hc1 hc1' V X
  rw [expL_of_cube C _ (by rw [h2, Lop_const]), h2, h1, eval_lin, one_smul, one_smul]
  simp only [smul_smul]
  rw [show ((kf d c0 c1 V + kf d c0 c1 (Wf d c0 c1 V) / 2) * X.card) =
    kf d c0 c1 V * X.card + 1 / 2 * (kf d c0 c1 (Wf d c0 c1 V) * X.card) by ring, add_smul]
  abel

end Comp

theorem eval_ε0 (V : Vcoup) (X : Finset (Lam d L N)) : ε (V.eval X) = 0 := by
  simp [Vcoup.eval, gradSq, lapPsi, lapPsibar, grad, gradbar, psi, psibar, ψ]

/-- The coefficients of `V(X)` (for `V` with `b = 0`) in the monomial basis. -/
def cW (W : Vcoup) : Mono d → ℂ
  | .c => W.a
  | .a1 _ => 0
  | .b1 _ => 0
  | .a2 s => if s.IsDiag then -(W.z / 2) else 0
  | .b2 s => if s.IsDiag then -(W.z / 2) else 0
  | .m2 i k => if i = k then W.y else 0

theorem eval_eq_monoSet (W : Vcoup) (hW : W.b = 0) (X : Finset (Lam d L N)) :
    W.eval X = ∑ M, cW W M • monoSet M X := by
  classical
  rw [sum_mono]
  have h3 : ∑ s, cW W (.a2 s) • monoSet (.a2 s) X = ∑ i, (-(W.z / 2)) • monoSet (.a2 s(i, i)) X := by
    rw [sum_sym2_diag]
    · simp [cW]
    · intro s hs; simp [cW, hs]
  have h4 : ∑ s, cW W (.b2 s) • monoSet (.b2 s) X = ∑ i, (-(W.z / 2)) • monoSet (.b2 s(i, i)) X := by
    rw [sum_sym2_diag]
    · simp [cW]
    · intro s hs; simp [cW, hs]
  have h5 : ∑ i, ∑ k, cW W (.m2 i k) • monoSet (.m2 i k) X = ∑ i, W.y • monoSet (.m2 i i) X := by
    refine sum_congr rfl fun i _ => ?_
    rw [sum_eq_single i]
    · simp [cW]
    · intro k _ hik; simp [cW, Ne.symm hik]
    · simp
  rw [h3, h4, h5]
  simp only [cW, zero_smul, sum_const_zero, add_zero]
  simp only [← smul_sum, monoSet]
  rw [sum_comm (s := univ) (t := X), sum_comm (s := univ) (t := X), sum_comm (s := univ) (t := X)]
  simp only [sum_monoAt_a2, sum_monoAt_b2, sum_monoAt_m2, monoAt_c, Vcoup.eval, hW, zero_smul,
    add_zero, sum_add_distrib, ← smul_sum]
  simp only [neg_mul, mul_neg, sum_neg_distrib]
  module

end Lat

end Coup

open Coup

/-- Covariances invariant under the generated lattice automorphisms. -/
def CovInv (C : Matrix (Lam d L N) (Lam d L N) ℝ) : Prop :=
  ∀ T : AffAut d L N, IsGen T → ∀ x y, C (T.E x) (T.E y) = C x y

theorem GoodCov.covInv {j : ℕ} {ℓ₀ : ℝ} {C : Matrix (Lam d L N) (Lam d L N) ℝ}
    (hC : GoodCov j ℓ₀ C) : CovInv C := hC.inv

theorem GoodCov.symm' {j : ℕ} {ℓ₀ : ℝ} {C : Matrix (Lam d L N) (Lam d L N) ℝ}
    (hC : GoodCov j ℓ₀ C) (x y : Lam d L N) : C x y = C y x := by
  simpa using (hC.psd.1.apply x y).symm

/-- Small sets at scale `j` with `j + 1 < N` are regions for Proposition `prop:Loc` (iv). -/
theorem region_small (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {j : ℕ} (hj : j + 1 < N)
    {X : Finset (Lam d L N)} (hX : IsSmall j X) :
    Region X (nbhd j X : Set (Lam d L N)) := by
  refine ⟨fun x hx a ha => ?_, fun x hx y hy => ?_⟩
  · refine Finset.mem_coe.2 (mem_nbhd_of_near hd hX.1 hx ?_)
    rw [add_sub_cancel_left]
    exact (supNorm_prj_le a).trans ha
  · obtain ⟨x0, hx0⟩ := hX.2.1.1
    have h1 := supNorm_le_of_mem_nbhd hX hx0 (Finset.mem_coe.1 hx)
    have h2 := supNorm_le_of_mem_nbhd hX hx0 (Finset.mem_coe.1 hy)
    have h3 : supNorm (x - y) ≤ supNorm (x - x0) + supNorm (y - x0) := by
      have := supNorm_add_le (x - x0) (x0 - y)
      rw [sub_add_sub_cancel, supNorm_sub_comm x0 y] at this
      exact this
    have hP : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    have hQ : 1 ≤ L ^ j := Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ (NeZero.ne L))
    have hL8 : 8 * 2 ^ d ≤ L := by rw [pow_add] at hL; linarith
    have hLN : L ^ j * L * L ≤ L ^ N := by
      rw [← pow_succ, ← pow_succ]
      exact Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (by omega)
    have h4 : L ^ j * (8 * 2 ^ d) * 8 ≤ L ^ j * L * L :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hL8) (by linarith)
    rw [pow_succ] at h1 h2
    nlinarith

theorem patch_small (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {j : ℕ} (hj : j + 1 < N)
    {X : Finset (Lam d L N)} (hX : IsSmall j X) : Patch X :=
  (region_small hd hL hj hX).patch hX.2.1.1

/-- `𝔼_C θ V(X) ∈ (ℂ ⊕ 𝒱^∅)(X)`. -/
theorem CovInv.transl {C : Matrix (Lam d L N) (Lam d L N) ℝ} (hC : CovInv C) (x y t : Lam d L N) :
    C (x + t) (y + t) = C x y := hC _ (IsGen.transl t) x y

theorem CovInv.diag {C : Matrix (Lam d L N) (Lam d L N) ℝ} (hC : CovInv C) (x : Lam d L N) :
    C x x = C 0 0 := by
  simpa using hC.transl 0 0 x

theorem CovInv.shift {C : Matrix (Lam d L N) (Lam d L N) ℝ} (hC : CovInv C) (x v : Lam d L N) :
    C x (x + v) = C 0 v := by
  have := hC.transl 0 v x
  rwa [zero_add, add_comm v x] at this

theorem permT_single (σ : Equiv.Perm (Fin d)) (i : Fin d) :
    (permT (L := L) (N := N) σ) (dirVec (Sum.inl i)) = dirVec (Sum.inl (σ i)) := by
  funext m
  simp [permT, dirVec, co, Pi.single_apply, Equiv.symm_apply_eq]

theorem CovInv.dir {C : Matrix (Lam d L N) (Lam d L N) ℝ} (hC : CovInv C)
    (hCs : ∀ x y, C x y = C y x) (e e' : Dir d) :
    C 0 (dirVec e) = C 0 (dirVec e') := by
  have hinr : ∀ i, C 0 (dirVec (Sum.inr i)) = C 0 (dirVec (Sum.inl i)) := by
    intro i
    have := hC.transl 0 (dirVec (Sum.inr i)) (dirVec (Sum.inl i))
    rw [zero_add, dirVec_inr_eq, neg_add_cancel] at this
    rw [dirVec_inr_eq, ← this, hCs]
  have hinl : ∀ i k, C 0 (dirVec (Sum.inl i)) = C 0 (dirVec (Sum.inl k)) := by
    intro i k
    have := hC _ (IsGen.perm (Equiv.swap i k)) 0 (dirVec (Sum.inl i))
    have e1 : (AffAut.perm (L := L) (N := N) (Equiv.swap i k)).E 0 = 0 :=
      map_zero (permT (L := L) (N := N) (Equiv.swap i k))
    have e2 : (AffAut.perm (L := L) (N := N) (Equiv.swap i k)).E (dirVec (Sum.inl i)) =
        dirVec (Sum.inl k) := by
      rw [show (AffAut.perm (L := L) (N := N) (Equiv.swap i k)).E (dirVec (Sum.inl i)) =
        permT (Equiv.swap i k) (dirVec (Sum.inl i)) from rfl, permT_single, Equiv.swap_apply_left]
    rw [e1, e2] at this
    exact this.symm
  have h : ∀ e : Dir d, ∃ i, C 0 (dirVec e) = C 0 (dirVec (Sum.inl i)) := by
    rintro (i | i)
    · exact ⟨i, rfl⟩
    · exact ⟨i, hinr i⟩
  obtain ⟨i, hi⟩ := h e
  obtain ⟨k, hk⟩ := h e'
  rw [hi, hk, hinl]

theorem EC_one' (C : Matrix (Lam d L N) (Lam d L N) ℝ) : EC C (theta (1 : Alg d L N)) = 1 := by
  rw [map_one, EC_one]

/-- The explicit form of `𝔼_C θ V(X)`: with `c₀ = C(0,0)`, `c₁ = C(0,e)` (any unit vector `e`),
`𝔼_C θ V(X) = u|X| + V'(X)` with `u = kf c₀ c₁ V + kf c₀ c₁ (Wf c₀ c₁ V) / 2` and
`V' = V + Wf c₀ c₁ V`. -/
theorem EC_theta_eval_eq {C : Matrix (Lam d L N) (Lam d L N) ℝ} (hC : CovInv C)
    (hCs : ∀ x y, C x y = C y x) (c1 : ℝ) (hc1 : ∀ e : Dir d, C 0 (dirVec e) = c1) (V : Vcoup)
    (X : Finset (Lam d L N)) :
    EC C (theta (V.eval X)) = ((kf d (C 0 0 : ℂ) (c1 : ℂ) V +
      kf d (C 0 0 : ℂ) (c1 : ℂ) (Wf d (C 0 0 : ℂ) (c1 : ℂ) V) / 2) * X.card) • (1 : Alg d L N) +
        (Vlin 1 1 V (Wf d (C 0 0 : ℂ) (c1 : ℂ) V)).eval X := by
  rw [EC_theta]
  refine expL_eval C (C 0 0 : ℂ) (c1 : ℂ) (fun x => by rw [hC.diag]) (fun x e => by rw [hC.shift, hc1])
    (fun x e => by rw [hCs, hC.shift, hc1]) V X

theorem EC_theta_eval_mem {C : Matrix (Lam d L N) (Lam d L N) ℝ} (hC : CovInv C)
    (hCs : ∀ x y, C x y = C y x) (V : Vcoup) (X : Finset (Lam d L N)) :
    EC C (theta (V.eval X)) ∈ VXspace X := by
  rcases isEmpty_or_nonempty (Dir d) with hD | ⟨⟨e0⟩⟩
  · exact ⟨_, _, EC_theta_eval_eq hC hCs 0 (fun e => (IsEmpty.false e).elim) V X⟩
  · exact ⟨_, _, EC_theta_eval_eq hC hCs _ (fun e => hC.dir hCs e e0) V X⟩

theorem EC_theta_VXspace {C : Matrix (Lam d L N) (Lam d L N) ℝ} (hC : CovInv C)
    (hCs : ∀ x y, C x y = C y x) {X : Finset (Lam d L N)} {F : Alg d L N} (hF : F ∈ VXspace X) :
    EC C (theta F) ∈ VXspace X := by
  obtain ⟨u, W, rfl⟩ := hF
  obtain ⟨u', W', h⟩ := EC_theta_eval_mem hC hCs W X
  refine ⟨u + u', W', ?_⟩
  rw [map_add, map_smul, map_add, map_smul, EC_one', h, add_mul, add_smul, add_assoc]

theorem VXspace_sub {X : Finset (Lam d L N)} {F G : Alg d L N} (hF : F ∈ VXspace X)
    (hG : G ∈ VXspace X) : F - G ∈ VXspace X := by
  obtain ⟨u, V, rfl⟩ := hF
  obtain ⟨u', V', rfl⟩ := hG
  refine ⟨u - u', Vlin 1 (-1) V V', ?_⟩
  rw [eval_lin, one_smul, neg_one_smul, sub_mul, sub_smul]
  abel

theorem eval_mem_VXspace (V : Vcoup) (X : Finset (Lam d L N)) : V.eval X ∈ VXspace X :=
  ⟨0, V, by simp⟩

open Classical in
theorem Qb_coe {j : ℕ} (K : Act d L N) (b : Fin d → ℕ) :
    (Qb j K b : Alg d L N) = if j + 1 < N then
      ∑ X ∈ (smallSets j).filter (fun X => blockSet j b ⊆ X),
        LocXY X (blockSet j b) (K X : Alg d L N) else 0 := by
  unfold Qb
  split_ifs <;> simp

theorem mem_smallSets_filter {j : ℕ} {b : Fin d → ℕ} {X : Finset (Lam d L N)} :
    (open Classical in X ∈ (smallSets j).filter (fun X => blockSet j b ⊆ X)) ↔
      IsSmall j X ∧ blockSet j b ⊆ X := by
  simp [smallSets]

/-- `Q` is equivariant under block-preserving automorphisms. -/
theorem Qb_img (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {j : ℕ} {K : Act d L N} (hK : InK j K)
    {T : AffAut d L N} (hT : IsGen T) (hP : PresBlocks j T) {b b' : Fin d → ℕ}
    (hbb' : T.img (blockSet j b) = blockSet j b') :
    autAlg T.E (Qb j K b : Alg d L N) = Qb j K b' := by
  classical
  rw [Qb_coe, Qb_coe]
  split_ifs with hj
  · rw [map_sum]
    have hjN : j ≤ N := by omega
    refine Finset.sum_bij (fun X _ => T.img X) ?_ ?_ ?_ ?_
    · intro X hX
      rw [mem_smallSets_filter] at hX ⊢
      exact ⟨(hP.isSmall_img hT hjN).2 hX.1, hbb' ▸ img_mono T hX.2⟩
    · intro X₁ _ X₂ _ h
      exact img_injective T h
    · intro Y hY
      rw [mem_smallSets_filter] at hY
      obtain ⟨T', hT', hP', e, e'⟩ := hP.exists_inv hT hjN
      refine ⟨T'.img Y, ?_, e' Y⟩
      rw [mem_smallSets_filter]
      refine ⟨(hP'.isSmall_img hT' hjN).2 hY.1, ?_⟩
      rw [← e (blockSet j b), hbb']
      exact img_mono T' hY.2
    · intro X hX
      rw [mem_smallSets_filter] at hX
      have hc : IsConn j X := ⟨hX.1.1, hX.1.2.1⟩
      rw [T.LocXY_aut (region_small hd hL hj hX.1) hX.1.2.1.1 _ (hK.loc X hc), hbb',
        hK.aut T hT hP X hc]
  · simp

/-- `Q(B) ∈ (ℂ ⊕ 𝒱^∅)(B)` (by Proposition `prop:Loc` (iv), (v)). -/
theorem Qb_mem (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {j : ℕ} {K : Act d L N} (hK : InK j K)
    {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    (Qb j K b : Alg d L N) ∈ VXspace (blockSet (L := L) (N := N) j b) := by
  classical
  have key : ∀ T : AffAut d L N, IsGen T → PresBlocks j T →
      T.img (blockSet j b) = blockSet j b → j + 1 < N →
      autAlg T.E (∑ X ∈ (smallSets j).filter (fun X => blockSet j b ⊆ X),
        LocXY X (blockSet j b) (K X : Alg d L N)) =
      ∑ X ∈ (smallSets j).filter (fun X => blockSet j b ⊆ X),
        LocXY X (blockSet j b) (K X : Alg d L N) := by
    intro T hT hP hTB hj
    have := Qb_img hd hL hK hT hP hTB
    simp only [Qb_coe, if_pos hj] at this
    exact this
  rw [Qb_coe]
  split_ifs with hj
  · have hjN : j ≤ N := by omega
    have hne := mem_blockIdx.1 hb
    have h3 : 3 ≤ L := le_trans (by
      calc 3 ≤ 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (d + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)) hL
    refine Loc_image' hd (by omega) h3 hne _ (fun X => X) (fun X => (K X : Alg d L N))
      (fun X hX => patch_small hd hL hj (mem_smallSets_filter.1 hX).1)
      (fun X hX => (mem_smallSets_filter.1 hX).1.2.1.1)
      (fun X hX => hK.jinv X ⟨(mem_smallSets_filter.1 hX).1.1, (mem_smallSets_filter.1 hX).1.2.1⟩)
      (fun i => key _ (isGen_reflCenter j b i) (presBlocks_reflCenter hjN hb i)
        (reflCenter_img hjN b i) hj)
      (fun σ => key _ (isGen_permCorner j b σ) (presBlocks_permCorner hjN hb σ)
        (permCorner_img hjN b σ) hj)
  · refine ⟨0, ⟨0, 0, 0, 0⟩, ?_⟩
    rw [eval_eq_sum]
    simp [Vsum_zero]

theorem coupOf_spec {F : Alg d L N} {B : Finset (Lam d L N)} (h : F ∈ VXspace B) :
    F = ((coupOf F B).1 * B.card) • (1 : Alg d L N) + (coupOf F B).2.eval B := by
  have h' : ∃ (u : ℂ) (V' : Vcoup), F = (u * B.card) • (1 : Alg d L N) + V'.eval B := h
  unfold coupOf
  rw [dif_pos h']
  exact h'.choose_spec.choose_spec

/-- **Definition `def:V+`**: `𝔼_C θ (V_j(B) - Q(B)) = u_{j+1}|B| + V_{j+1}(B)` for every
`j`-block `B`. -/
theorem uVnext_spec (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {j : ℕ} (hj : j < N)
    {C : Matrix (Lam d L N) (Lam d L N) ℝ} (hC : CovInv C) (hCs : ∀ x y, C x y = C y x)
    (V : Vcoup) {K : Act d L N} (hK : InK j K) {b : Fin d → ℕ}
    (hb : b ∈ blockIdx (L := L) (N := N) j) :
    EC C (theta (V.eval (blockSet j b) - (Qb j K b : Alg d L N))) =
      ((uVnext j C V K).1 * (blockSet (L := L) (N := N) j b).card) • (1 : Alg d L N) +
        (uVnext j C V K).2.eval (blockSet j b) := by
  have hjN : j ≤ N := hj.le
  have hmem : EC C (theta (V.eval (blockSet j 0) - (Qb j K 0 : Alg d L N))) ∈
      VXspace (blockSet (L := L) (N := N) j 0) :=
    EC_theta_VXspace hC hCs (VXspace_sub (eval_mem_VXspace V _)
      (Qb_mem hd hL hK (zero_mem_blockIdx j)))
  have h0 : EC C (theta (V.eval (blockSet j 0) - (Qb j K 0 : Alg d L N))) =
      ((uVnext j C V K).1 * (blockSet (L := L) (N := N) j 0).card) • (1 : Alg d L N) +
        (uVnext j C V K).2.eval (blockSet j 0) := coupOf_spec hmem
  have hT : IsGen (AffAut.transl (corner (L := L) (N := N) j b)) := IsGen.transl _
  have hP := presBlocks_transl_corner (L := L) (N := N) hjN b
  have himg := transl_corner_img hjN hb
  have hcard : (blockSet (L := L) (N := N) j b).card =
      (blockSet (d := d) (L := L) (N := N) j 0).card := by
    rw [← himg, AffAut.card_img]
  have hE : ∀ G : Alg d L N, autAlg (AffAut.transl (corner (L := L) (N := N) j b)).E
      (EC C (theta G)) = EC C (theta (autAlg (AffAut.transl (corner (L := L) (N := N) j b)).E G)) := by
    intro G
    rw [theta_autAlg, EC_autAlg2 _ (hC _ hT)]
  have h1 := congrArg (autAlg (AffAut.transl (corner (L := L) (N := N) j b)).E) h0
  rw [hE, map_sub, hT.eval_img, himg, Qb_img hd hL hK hT hP himg, map_add, map_smul, map_one,
    hT.eval_img, himg] at h1
  rw [h1, hcard]

/-- The same for `j`-polymers `X`: `𝔼_C θ (V_j(X) - ∑_{B ⊆ X} Q(B)) = (u + V)_{j+1}(X)`. -/
theorem uVnext_spec_polymer (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {j : ℕ} (hj : j < N)
    {C : Matrix (Lam d L N) (Lam d L N) ℝ} (hC : CovInv C) (hCs : ∀ x y, C x y = C y x)
    (V : Vcoup) {K : Act d L N} (hK : InK j K) {X : Finset (Lam d L N)} (hX : IsPolymer j X) :
    EC C (theta (V.eval X - ∑ b ∈ blocks j X, (Qb j K b : Alg d L N))) =
      ((uVnext j C V K).1 * X.card) • (1 : Alg d L N) + (uVnext j C V K).2.eval X := by
  have hdisj : ((blocks j X : Finset (Fin d → ℕ)) : Set (Fin d → ℕ)).PairwiseDisjoint
      (blockSet (L := L) (N := N) j) := by
    intro b _ b' _ hbb'
    rw [Function.onFun, disjoint_left]
    intro x hx hx'
    exact hbb' ((mem_blockSet.1 hx).symm.trans (mem_blockSet.1 hx'))
  have hev : ∀ W : Vcoup, W.eval X = ∑ b ∈ blocks j X, W.eval (blockSet (L := L) (N := N) j b) := by
    intro W
    conv_lhs => rw [← biUnion_blocks hX]
    rw [Vcoup.eval, sum_biUnion hdisj]
    rfl
  have hcard : X.card = ∑ b ∈ blocks j X, (blockSet (L := L) (N := N) j b).card := by
    conv_lhs => rw [← biUnion_blocks hX]
    exact card_biUnion hdisj
  have hbi : ∀ b ∈ blocks j X, b ∈ blockIdx (L := L) (N := N) j := fun b hb =>
    image_subset_image (subset_univ X) hb
  rw [hev, hev, ← sum_sub_distrib, map_sum, map_sum, hcard]
  rw [sum_congr rfl fun b hb => uVnext_spec hd hL hj hC hCs V hK (hbi b hb)]
  rw [sum_add_distrib, Nat.cast_sum, mul_sum, sum_smul]

/-- The coupling constants are uniquely determined: `(u, V) ↦ u|X| + V(X)` is injective for
nonempty patches `X` (`d ≥ 1`, `L^N ≥ 3`); e.g. for blocks (`patch_blockSet`).  (For `X = Λ` it is
not injective: summation by parts identifies the `z`- and `y`-terms.) -/
theorem coup_injective (hd : 1 ≤ d) (hLN : 3 ≤ L ^ N) {X : Finset (Lam d L N)} (hX : X.Nonempty)
    (hXp : Patch X) {u u' : ℂ} {V V' : Vcoup}
    (h : (u * X.card) • (1 : Alg d L N) + V.eval X = (u' * X.card) • (1 : Alg d L N) + V'.eval X) :
    u = u' ∧ V = V' := by
  have hcard : (X.card : ℂ) ≠ 0 := by exact_mod_cast hX.card_pos.ne'
  have hε := congrArg ε h
  simp only [map_add, map_smul, map_one, eval_ε0, smul_eq_mul, mul_one, add_zero] at hε
  have hu : u = u' := mul_right_cancel₀ hcard hε
  subst hu
  have hV : V.eval X = V'.eval X := add_left_cancel h
  -- the quartic coefficient, via `ℒ_1²`
  have hne : ∀ (x : Lam d L N) (e : Dir d), x + dirVec e ≠ x := by
    haveI : Fact (1 < L ^ N) := ⟨by omega⟩
    intro x e hx
    have h0 : (dirVec e : Lam d L N) = 0 := by
      have := congrArg (fun v => v - x) hx
      simpa using this
    rcases e with i | i
    · have := congrFun (show (dirVec (Sum.inl i) : Fin d → ZMod (L ^ N)) = 0 from h0) i
      simp [dirVec] at this
      exact one_ne_zero (this.trans rfl)
    · have := congrFun (show (dirVec (Sum.inr i) : Fin d → ZMod (L ^ N)) = 0 from h0) i
      simp [dirVec] at this
      exact neg_ne_zero.2 one_ne_zero (this.trans rfl)
  have hc0 : ∀ x : Lam d L N, ((1 : Matrix (Lam d L N) (Lam d L N) ℝ) x x : ℂ) = 1 :=
    fun x => by rw [Matrix.one_apply_eq x, Complex.ofReal_one]
  have hc1 : ∀ (x : Lam d L N) (e : Dir d),
      ((1 : Matrix (Lam d L N) (Lam d L N) ℝ) x (x + dirVec e) : ℂ) = 0 :=
    fun x e => by rw [Matrix.one_apply_ne (hne x e).symm, Complex.ofReal_zero]
  have hc1' : ∀ (x : Lam d L N) (e : Dir d),
      ((1 : Matrix (Lam d L N) (Lam d L N) ℝ) (x + dirVec e) x : ℂ) = 0 :=
    fun x e => by rw [Matrix.one_apply_ne (hne x e), Complex.ofReal_zero]
  have hb := congrArg (fun F => ε (Lop 1 (Lop 1 F))) hV
  simp only [Lop2_eval 1 1 0 hc0 hc1 hc1', map_smul, map_one, smul_eq_mul, mul_one] at hb
  have hb' : V.b = V'.b := by
    have h2 : (2 * d * X.card : ℂ) * (V.b - V'.b) = 0 := by
      simp only [kf, Wf] at hb
      linear_combination hb
    rcases mul_eq_zero.1 h2 with h2 | h2
    · exfalso
      have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
      exact mul_ne_zero (mul_ne_zero two_ne_zero hd') hcard h2
    · exact sub_eq_zero.1 h2
  -- the quadratic coefficients, via the monomial basis
  set W := Vlin 1 (-1) V V' with hWdef
  have hW0 : W.eval X = 0 := by rw [eval_lin, hV]; simp
  have hWb : W.b = 0 := by simp [W, Vlin, hb']
  have hc := coef_unique hXp hX (c := cW W) (c' := 0) fun β => by
    rw [← eval_eq_monoSet W hWb X, hW0]
    simp only [Pi.zero_apply, zero_smul, sum_const_zero]
  set i₀ : Fin d := ⟨0, hd⟩
  have ha := congrFun hc .c
  have hy := congrFun hc (.m2 i₀ i₀)
  have hz := congrFun hc (.a2 s(i₀, i₀))
  simp only [cW, W, Vlin, Pi.zero_apply, if_true, Sym2.mk_isDiag_iff] at ha hy hz
  refine ⟨rfl, ?_⟩
  cases V
  cases V'
  simp only [Vcoup.mk.injEq] at hb' ha hy hz ⊢
  refine ⟨by linear_combination -2 * hz, by linear_combination hy, by linear_combination ha, hb'⟩

end

end Step
