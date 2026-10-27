import Obs2.Flow.GamRem
import Obs2.Flow.Tau2Bd

/-!
# The bulk one-loop factor `ε(F_C(ψ̄_aψ_a, V_κ(Λ)))` explicitly, and its bounds

* `eps_FC_pbp_pair`: `ε F_C(ψ̄_aψ_a, ψ_sψ̄_t) = C(a,s)C(t,a)`; `eps_FC_pbp_hom4`: the quartic part
  does not contribute;
* **`eps_FC_pbp_Vcoup`** (any matrix `C`, by summation by parts over the torus):
  `ε F_C(ψ̄_aψ_a, V_κ(Λ)) = ν∑_xC(a,x)C(x,a) + (y + z)𝔩_C(a)`; the gradient monomials contribute
  through the bubble `𝔩_C(a)` (`lfunC`), the two `y`-monomials after a summation by parts;
* bounds for `GoodCov2` covariances: `‖∑_xC(a,x)C(x,a)‖ ≤ 9L^{2(k+1)}ℓ_C⁴` (`norm_sumCC_le`), and,
  with an entry bound `|C(x,y)| ≤ c₀` (positive symbols), `‖∑_xC(a,x)C(x,a)‖ ≤ 9L^{2(k+1)}ℓ_C²c₀`,
  `‖𝔩_C(a)‖ ≤ 36L^{k+1}ℓ_C²c₀` (`norm_sumCC_le_c0`, `norm_lfunC_le_c0`).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Loc Step Step2 LocObs FRD

section Pure

variable {d L N : ℕ} [NeZero L] (C : Matrix (Lam d L N) (Lam d L N) ℂ)

theorem eps_DD_pair (s t x y : Lam d L N) :
    ε (D (x, -1) (D (y, 1) (psi s * psibar t))) = if y = s ∧ x = t then 1 else 0 := by
  have e : (psi s * psibar t : Alg d L N) = ExteriorAlgebra.ι ℂ (ev ((s, 1) : Sf (Lam d L N))) * ExteriorAlgebra.ι ℂ (ev (t, -1)) :=
    rfl
  rw [e, D_pair, D_ι]
  simp [ev, Pi.single_apply, Prod.ext_iff]
  split_ifs <;> simp_all

theorem eps_DD_pair' (s t x y : Lam d L N) :
    ε (D (y, 1) (D (x, -1) (psi s * psibar t))) = if y = s ∧ x = t then -1 else 0 := by
  have e : (psi s * psibar t : Alg d L N) = ExteriorAlgebra.ι ℂ (ev ((s, 1) : Sf (Lam d L N))) * ExteriorAlgebra.ι ℂ (ev (t, -1)) :=
    rfl
  rw [e, D_pair, D_ι]
  simp [ev, Pi.single_apply, Prod.ext_iff]
  split_ifs <;> simp_all

/-- `ε F_C(ψ̄_aψ_a, ψ_sψ̄_t) = C(a,s)C(t,a)`. -/
theorem eps_FC_pbp_pair (a s t : Lam d L N) :
    ε (FC C (pbp a) (psi s * psibar t)) = C a s * C t a := by
  rw [eps_FC_pbp]
  simp only [eps_DD_pair, eps_DD_pair']
  simp [mul_ite, ite_and, sum_ite_eq']
  ring

theorem eps_FC_pbp_hom4 (a : Lam d L N) {B : Alg d L N} (hB : Step2.IsHom 4 B) :
    ε (FC C (pbp a) B) = 0 := by
  rw [eps_FC_pbp]
  have h1 : ∀ x y : Lam d L N, ε (D (x, -1) (D (y, 1) B)) = 0 := fun x y => by
    rw [← coeff_two]; exact hB 2 _ (by norm_num)
  have h2 : ∀ x y : Lam d L N, ε (D (y, 1) (D (x, -1) B)) = 0 := fun x y => by
    rw [← coeff_two]; exact hB 2 _ (by norm_num)
  simp [h1, h2]

/-- `B ↦ ε F_C(ψ̄_aψ_a, B)` as a linear functional. -/
def epsFCL (a : Lam d L N) : Alg d L N →ₗ[ℂ] ℂ :=
  (ε : Alg d L N →ₐ[ℂ] ℂ).toLinearMap ∘ₗ FCr C (pbp a)

theorem epsFCL_apply (a : Lam d L N) (B : Alg d L N) : epsFCL C a B = ε (FC C (pbp a) B) := rfl

theorem dirVec_inl_inr (i : Fin d) (x : Lam d L N) :
    x + dirVec (Sum.inl i) + dirVec (Sum.inr i) = x := by
  simp only [dirVec]; abel

/-- Summation by parts: the two one-sided gradients combine into a gradient pair. -/
theorem sum_grad_pair (f g : Lam d L N → ℂ) (i : Fin d) :
    ∑ x, (f (x + dirVec (Sum.inl i)) - f x) * g x +
      ∑ x, (f (x + dirVec (Sum.inr i)) - f x) * g x =
    -∑ x, (f (x + dirVec (Sum.inl i)) - f x) * (g (x + dirVec (Sum.inl i)) - g x) := by
  have h := sum_add_right' (fun x => (f (x + dirVec (Sum.inr i)) - f x) * g x)
    (dirVec (Sum.inl i))
  simp only [dirVec_inl_inr] at h
  rw [← h, ← sum_add_distrib, ← sum_neg_distrib]
  exact sum_congr rfl fun x _ => by ring

theorem sum_gpC_inr (a : Lam d L N) (i : Fin d) :
    ∑ z, gpC C a (Sum.inr i) z = ∑ z, gpC C a (Sum.inl i) z := by
  have h := sum_add_right' (fun z => gpC C a (Sum.inr i) z) (dirVec (Sum.inl i))
  rw [← h]
  refine sum_congr rfl fun z _ => ?_
  simp only [gpC, dirVec_inl_inr]; ring

theorem epsFCL_monoSet_c (a : Lam d L N) :
    epsFCL C a (monoSet (Mono.c : Mono d) univ) = ∑ x, C a x * C x a := by
  rw [monoSet, map_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [Step2.monoAt_c, epsFCL_apply, eps_FC_pbp_pair]

theorem epsFCL_monoSet_a2 (a : Lam d L N) (i : Fin d) :
    epsFCL C a (monoSet (Mono.a2 s(i, i)) univ) = -∑ z, gpC C a (Sum.inl i) z := by
  rw [monoSet, map_sum]
  have e : ∀ x, epsFCL C a (monoAt (Mono.a2 s(i, i)) x) =
      (C a (x + dirVec (Sum.inl i)) - C a x) * C x a +
        (C a (x + dirVec (Sum.inr i)) - C a x) * C x a := fun x => by
    rw [monoAt_a2]
    simp only [sub_mul, map_add, map_sub, epsFCL_apply, eps_FC_pbp_pair]
  simp only [e, sum_add_distrib]
  rw [sum_grad_pair (fun x => C a x) (fun x => C x a) i]
  simp only [gpC]

theorem epsFCL_monoSet_b2 (a : Lam d L N) (i : Fin d) :
    epsFCL C a (monoSet (Mono.b2 s(i, i)) univ) = -∑ z, gpC C a (Sum.inl i) z := by
  rw [monoSet, map_sum]
  have e : ∀ x, epsFCL C a (monoAt (Mono.b2 s(i, i)) x) =
      (C (x + dirVec (Sum.inl i)) a - C x a) * C a x +
        (C (x + dirVec (Sum.inr i)) a - C x a) * C a x := fun x => by
    rw [monoAt_b2]
    simp only [mul_sub, map_add, map_sub, epsFCL_apply, eps_FC_pbp_pair]
    ring
  simp only [e, sum_add_distrib]
  rw [sum_grad_pair (fun x => C x a) (fun x => C a x) i]
  simp only [gpC]
  congr 1
  exact sum_congr rfl fun x _ => by ring

theorem epsFCL_monoSet_m2 (a : Lam d L N) (i : Fin d) :
    epsFCL C a (monoSet (Mono.m2 i i) univ) =
      ∑ z, (1 / 2 : ℂ) * (gpC C a (Sum.inl i) z + gpC C a (Sum.inr i) z) := by
  rw [monoSet, map_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [monoAt_m2]
  simp only [mul_sub, sub_mul, map_add, map_sub, map_smul, smul_eq_mul, epsFCL_apply,
    eps_FC_pbp_pair, gpC]

/-- **`ε F_C(ψ̄_aψ_a, V_κ(Λ)) = ν∑_xC(a,x)C(x,a) + (y + z)𝔩_C(a)`** (any matrix `C`). -/
theorem eps_FC_pbp_Vcoup (a : Lam d L N) (κ : Step2.Coup) :
    ε (FC C (pbp a) (Step2.Vcoup κ univ)) =
      κ.nu * ∑ x, C a x * C x a + (κ.y + κ.z) * lfunC C a := by
  rw [← epsFCL_apply, Step2.Vcoup, Step2.unif, map_add, map_add, map_smul, epsFCL_apply, FC_one_right,
    map_zero, smul_zero, zero_add, map_sum, map_sum]
  have hq : ∀ i k : Fin d, epsFCL C a (Step2.coupE κ i k • mono4sSet i k univ) = 0 := fun i k => by
    rw [map_smul, epsFCL_apply, eps_FC_pbp_hom4 C a
      (by unfold mono4sSet; exact Step2.IsHom.sum _ fun x _ => Step2.isHom_mono4s i k x),
      smul_zero]
  simp only [map_sum, hq, sum_const_zero, add_zero]
  rw [Step2.sum_mono]
  simp only [map_smul, smul_eq_mul, Step2.coupC, zero_mul, sum_const_zero, add_zero]
  have ha : ∀ s : Sym2 (Fin d), (if s.IsDiag then -κ.y / 2 else 0) * epsFCL C a (monoSet (Mono.a2 s) univ)
      = if s.IsDiag then -κ.y / 2 * epsFCL C a (monoSet (Mono.a2 s) univ) else 0 := fun s => by
    split_ifs <;> simp
  have hb : ∀ s : Sym2 (Fin d), (if s.IsDiag then -κ.y / 2 else 0) * epsFCL C a (monoSet (Mono.b2 s) univ)
      = if s.IsDiag then -κ.y / 2 * epsFCL C a (monoSet (Mono.b2 s) univ) else 0 := fun s => by
    split_ifs <;> simp
  have hm : ∀ i : Fin d, ∑ k : Fin d, (if i = k then κ.z else 0) * epsFCL C a (monoSet (Mono.m2 i k) univ)
      = κ.z * epsFCL C a (monoSet (Mono.m2 i i) univ) := fun i => by
    rw [Fintype.sum_eq_single i (fun k hk => by simp [Ne.symm hk])]; simp
  simp only [ha, hb, hm, Step2.sum_sym2_diag, epsFCL_monoSet_c, epsFCL_monoSet_a2,
    epsFCL_monoSet_b2, epsFCL_monoSet_m2]
  unfold lfunC
  have hg : ∀ i : Fin d, ∑ z, gpC C a (Sum.inl i) z =
      ∑ z, (1 / 2 : ℂ) * (gpC C a (Sum.inl i) z + gpC C a (Sum.inr i) z) := fun i => by
    rw [← mul_sum, sum_add_distrib, sum_gpC_inr]; ring
  simp only [← hg]
  rw [add_assoc, add_assoc]
  congr 1
  simp only [mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun z _ => ?_
  ring

end Pure

section Bounds

variable {L N : ℕ} [NeZero L] {k : ℕ} {ℓC : ℝ} {C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ}

/-- `‖∑_xC(a,x)C(x,a)‖ ≤ 9L^{2(k+1)}ℓ_C⁴`. -/
theorem norm_sumCC_le (hC : GoodCov2 k ℓC C) (hkN : k + 1 < N) (a : Lam 2 L N) :
    ‖∑ x, C a x * C x a‖ ≤ 9 * ((L : ℝ) ^ (k + 1)) ^ 2 * (ℓC ^ 2 * ℓC ^ 2) := by
  refine norm_sum_ball_le a k _ (fun z hz => ?_) (fun z => ?_)
  · obtain ⟨c1, -, -, -⟩ := cov_zero_far hC hkN a z hz (Sum.inl 0)
    rw [c1, zero_mul]
  · rw [norm_mul]
    exact mul_le_mul (good_entry hC a z) (good_entry hC z a) (norm_nonneg _) (by positivity)

/-- With an entry bound `‖C(x,y)‖ ≤ c₀`: `‖∑_xC(a,x)C(x,a)‖ ≤ 9L^{2(k+1)}ℓ_C²c₀`. -/
theorem norm_sumCC_le_c0 (hC : GoodCov2 k ℓC C) (hkN : k + 1 < N) {c₀ : ℝ}
    (hc : ∀ x y, ‖C x y‖ ≤ c₀) (a : Lam 2 L N) :
    ‖∑ x, C a x * C x a‖ ≤ 9 * ((L : ℝ) ^ (k + 1)) ^ 2 * (ℓC ^ 2 * c₀) := by
  refine norm_sum_ball_le a k _ (fun z hz => ?_) (fun z => ?_)
  · obtain ⟨c1, -, -, -⟩ := cov_zero_far hC hkN a z hz (Sum.inl 0)
    rw [c1, zero_mul]
  · rw [norm_mul]
    exact mul_le_mul (good_entry hC a z) (hc z a) (norm_nonneg _) (by positivity)

theorem norm_gpC_le_c0 (hC : GoodCov2 k ℓC C) {c₀ : ℝ} (hc : ∀ x y, ‖C x y‖ ≤ c₀)
    (a : Lam 2 L N) (e : Dir 2) (z : Lam 2 L N) :
    ‖gpC C a e z‖ ≤ ℓC ^ 2 / (L : ℝ) ^ (k + 1) * (2 * c₀) := by
  unfold gpC
  rw [norm_mul]
  have h1 := good_gradR hC e a z
  have h2 : ‖C (z + dirVec e) a - C z a‖ ≤ 2 * c₀ :=
    (norm_sub_le _ _).trans (by linarith [hc (z + dirVec e) a, hc z a])
  exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)

/-- With an entry bound `‖C(x,y)‖ ≤ c₀`: `‖𝔩_C(a)‖ ≤ 18L^{2(k+1)}(ℓ_C²/L^{k+1})(2c₀)`. -/
theorem norm_lfunC_le_c0 (hC : GoodCov2 k ℓC C) (hkN : k + 1 < N) {c₀ : ℝ}
    (hc : ∀ x y, ‖C x y‖ ≤ c₀) (a : Lam 2 L N) :
    ‖lfunC C a‖ ≤ 18 * ((L : ℝ) ^ (k + 1)) ^ 2 * (ℓC ^ 2 / (L : ℝ) ^ (k + 1) * (2 * c₀)) := by
  set M := ℓC ^ 2 / (L : ℝ) ^ (k + 1) * (2 * c₀) with hMd
  have hi : ∀ i : Fin 2, ‖∑ z, (1 / 2 : ℂ) * (gpC C a (Sum.inl i) z + gpC C a (Sum.inr i) z)‖ ≤
      9 * ((L : ℝ) ^ (k + 1)) ^ 2 * M := by
    intro i
    refine norm_sum_ball_le a k _ (fun z hz => ?_) (fun z => ?_)
    · obtain ⟨c1, c2, c3, c4⟩ := cov_zero_far hC hkN a z hz (Sum.inl i)
      obtain ⟨-, -, d3, d4⟩ := cov_zero_far hC hkN a z hz (Sum.inr i)
      simp only [gpC, c1, c2, c3, c4, d3, d4, sub_zero, mul_zero, add_zero]
    · rw [norm_mul]
      have e : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
      rw [e]
      have := (norm_add_le _ _).trans (add_le_add (norm_gpC_le_c0 hC hc a (Sum.inl i) z)
        (norm_gpC_le_c0 hC hc a (Sum.inr i) z))
      linarith
  unfold lfunC
  refine (norm_sum_le _ _).trans ?_
  rw [Fin.sum_univ_two]
  linarith [hi 0, hi 1]

end Bounds

end

end Obs2
