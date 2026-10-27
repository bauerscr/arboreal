import Step2.Coup.WickSum

/-!
# The quartic coefficients of the cross terms (`h02uv-outline.tex`, `prop:C4b`(c))

For a covariance with `CovH` and a set `X` near the base `b`:

* `mu4_mass_univ_X`, `mu4_mass_X_univ`: the cross contraction of `(ψψ̄)` with the quartic
  coupling monomial `∑_i M̂^{ii}` has quartic pairing `4 C⁽¹⁾ |X|`, in both summation orders;
* `mu4_m2_*`, `mu4_a2_*`, `mu4_b2_*`: the cross contractions of the gradient monomials with the
  quartic monomial have vanishing quartic pairing.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Matrix

section General

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

theorem Xc_add_left (C : Matrix Λ Λ ℂ) (A A' B : N Λ) :
    Xc C (A + A') B = Xc C A B + Xc C A' B := by
  simp only [Xc, map_add, add_mul, ← sum_add_distrib, ← smul_add]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  congr 1; abel

theorem Xc_add_right (C : Matrix Λ Λ ℂ) (A B B' : N Λ) :
    Xc C A (B + B') = Xc C A B + Xc C A B' := by
  simp only [Xc, map_add, mul_add, ← sum_add_distrib, ← smul_add]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  congr 1; abel

theorem Xc_smul_left (C : Matrix Λ Λ ℂ) (r : ℂ) (A B : N Λ) :
    Xc C (r • A) B = r • Xc C A B := by
  simp only [Xc, map_smul, smul_mul_assoc, ← smul_sub, smul_sum, smul_comm r]

theorem Xc_smul_right (C : Matrix Λ Λ ℂ) (r : ℂ) (A B : N Λ) :
    Xc C A (r • B) = r • Xc C A B := by
  simp only [Xc, map_smul, mul_smul_comm, ← smul_sub, smul_sum, smul_comm r]

/-- `Xc` as a bilinear map. -/
def XcL (C : Matrix Λ Λ ℂ) : N Λ →ₗ[ℂ] N Λ →ₗ[ℂ] N Λ :=
  LinearMap.mk₂ ℂ (Xc C) (Xc_add_left C) (Xc_smul_left C) (Xc_add_right C) (Xc_smul_right C)

theorem XcL_apply (C : Matrix Λ Λ ℂ) (A B : N Λ) : XcL C A B = Xc C A B := rfl

end General

variable {d L N : ℕ} [NeZero L]

theorem mu4_Xc_mono4s (C : Matrix (Lam d L N) (Lam d L N) ℂ) (b : Lam d L N) (κ : Fin d)
    (A : Alg d L N) (i : Fin d) (x : Lam d L N) :
    mu4 b κ κ (Xc C A (mono4s i i x)) = (1 / 2 : ℂ) *
      (mu4 b κ κ (Xc C A (gmono4 (Sum.inl i) (Sum.inl i) x)) +
        mu4 b κ κ (Xc C A (gmono4 (Sum.inr i) (Sum.inr i) x))) := by
  rw [mono4s, if_pos rfl, Xc_smul_right, Xc_add_right, mu4_smul, mu4_add]

theorem mu4_Xc_mono4sSet (C : Matrix (Lam d L N) (Lam d L N) ℂ) (b : Lam d L N) (κ : Fin d)
    (A : Alg d L N) (i : Fin d) (X : Finset (Lam d L N)) :
    mu4 b κ κ (Xc C A (mono4sSet i i X)) = ∑ x ∈ X, (1 / 2 : ℂ) *
      (mu4 b κ κ (Xc C A (gmono4 (Sum.inl i) (Sum.inl i) x)) +
        mu4 b κ κ (Xc C A (gmono4 (Sum.inr i) (Sum.inr i) x))) := by
  rw [mono4sSet, ← XcL_apply, map_sum, mu4_sum]
  exact sum_congr rfl fun x _ => mu4_Xc_mono4s C b κ A i x

theorem dirZ_sq (i κ : Fin d) :
    (1 / 2 : ℂ) * (4 * (dirZ (Sum.inl i) κ : ℂ) * (dirZ (Sum.inl i) κ : ℂ) +
      4 * (dirZ (Sum.inr i) κ : ℂ) * (dirZ (Sum.inr i) κ : ℂ)) = if i = κ then 4 else 0 := by
  by_cases h : i = κ
  · subst h; simp [dirZ, Pi.single_apply]; norm_num
  · simp [dirZ, Pi.single_apply, Ne.symm h, h]

namespace CovH

variable {C : Matrix (Lam d L N) (Lam d L N) ℂ} {r : ℕ} (H : CovH C r)
include H

/-- **The mass cross term, `ψψ̄` global.** -/
theorem mu4_mass_univ_X {b : Lam d L N} {X : Finset (Lam d L N)}
    (hX : ∀ x ∈ X, 2 * (supNorm (x - b) + 1 + r) < L ^ N) (κ i : Fin d) :
    mu4 b κ κ (Xc C (monoSet (Mono.c : Mono d) univ) (mono4sSet i i X)) =
      (∑ a, C a 0) * X.card * (if i = κ then 4 else 0) := by
  rw [mu4_Xc_mono4sSet]
  have hx : ∀ x ∈ X, (1 / 2 : ℂ) *
      (mu4 b κ κ (Xc C (monoSet (Mono.c : Mono d) univ) (gmono4 (Sum.inl i) (Sum.inl i) x)) +
        mu4 b κ κ (Xc C (monoSet (Mono.c : Mono d) univ) (gmono4 (Sum.inr i) (Sum.inr i) x))) =
      (∑ a, C a 0) * (if i = κ then 4 else 0) := by
    intro x hxX
    simp only [monoSet, monoAt_c, ← XcL_apply, map_sum, LinearMap.sum_apply, mu4_sum]
    simp only [XcL_apply, H.sum_mass_a (hX x hxX)]
    rw [← dirZ_sq i κ]; ring
  rw [sum_congr rfl hx, sum_const, nsmul_eq_mul]; ring

/-- **The mass cross term, quartic monomial global.** -/
theorem mu4_mass_X_univ {b : Lam d L N} {X : Finset (Lam d L N)}
    (hX : ∀ a ∈ X, 2 * (supNorm (a - b) + r + 2) < L ^ N) (κ i : Fin d) :
    mu4 b κ κ (Xc C (monoSet (Mono.c : Mono d) X) (mono4sSet i i univ)) =
      (∑ a, C a 0) * X.card * (if i = κ then 4 else 0) := by
  rw [mu4_Xc_mono4sSet]
  simp only [monoSet, monoAt_c, ← XcL_apply, map_sum, LinearMap.sum_apply, mu4_sum]
  simp only [XcL_apply, mul_add, mul_sum, sum_add_distrib]
  rw [sum_comm, sum_comm (s := univ) (t := X)]
  rw [← sum_add_distrib]
  have ha : ∀ a ∈ X, ∑ x, (1 / 2 : ℂ) *
        mu4 b κ κ (Xc C (psi a * psibar a) (gmono4 (Sum.inl i) (Sum.inl i) x)) +
      ∑ x, (1 / 2 : ℂ) *
        mu4 b κ κ (Xc C (psi a * psibar a) (gmono4 (Sum.inr i) (Sum.inr i) x)) =
      (∑ a, C a 0) * (if i = κ then 4 else 0) := by
    intro a haX
    rw [← mul_sum, ← mul_sum, H.sum_mass_x (hX a haX), H.sum_mass_x (hX a haX),
      ← dirZ_sq i κ]
    ring
  rw [sum_congr rfl ha, sum_const, nsmul_eq_mul]; ring

end CovH

/-! ### Expansions of the gradient monomials -/

section Expand

variable (C : Matrix (Lam d L N) (Lam d L N) ℂ) (b : Lam d L N) (κ : Fin d) (e : Dir d)
  (x : Lam d L N)

theorem mu4_Xc_dd (s s' t t' : Lam d L N) :
    mu4 b κ κ (Xc C ((psi s - psi s') * (psibar t - psibar t')) (gmono4 e e x)) =
      Phi C b κ κ e e x s t - Phi C b κ κ e e x s t' - Phi C b κ κ e e x s' t +
        Phi C b κ κ e e x s' t' := by
  rw [sub_mul, mul_sub, mul_sub, ← XcL_apply, map_sub, map_sub, map_sub, LinearMap.sub_apply,
    LinearMap.sub_apply, LinearMap.sub_apply, mu4_sub, mu4_sub, mu4_sub]
  simp only [XcL_apply, mu4_Xc_pair]; ring

theorem mu4_Xc_ds (s s' t : Lam d L N) :
    mu4 b κ κ (Xc C ((psi s - psi s') * psibar t) (gmono4 e e x)) =
      Phi C b κ κ e e x s t - Phi C b κ κ e e x s' t := by
  rw [sub_mul, ← XcL_apply, map_sub, LinearMap.sub_apply, mu4_sub]
  simp only [XcL_apply, mu4_Xc_pair]

theorem mu4_Xc_sd (s t t' : Lam d L N) :
    mu4 b κ κ (Xc C (psi s * (psibar t - psibar t')) (gmono4 e e x)) =
      Phi C b κ κ e e x s t - Phi C b κ κ e e x s t' := by
  rw [mul_sub, ← XcL_apply, map_sub, LinearMap.sub_apply, mu4_sub]
  simp only [XcL_apply, mu4_Xc_pair]

theorem mu4_Xc_m2 (i : Fin d) (y : Lam d L N) :
    mu4 b κ κ (Xc C (monoAt (Mono.m2 i i) y) (gmono4 e e x)) = (1 / 2 : ℂ) *
      ∑ f ∈ ({Sum.inl i, Sum.inr i} : Finset (Dir d)),
        (Phi C b κ κ e e x (y + dirVec f) (y + dirVec f) - Phi C b κ κ e e x (y + dirVec f) y -
          Phi C b κ κ e e x y (y + dirVec f) + Phi C b κ κ e e x y y) := by
  rw [monoAt_m2, Xc_smul_left, Xc_add_left, mu4_smul, mu4_add, mu4_Xc_dd, mu4_Xc_dd,
    sum_pair (by simp)]

theorem mu4_Xc_a2 (i : Fin d) (y : Lam d L N) :
    mu4 b κ κ (Xc C (monoAt (Mono.a2 s(i, i)) y) (gmono4 e e x)) =
      ∑ f ∈ ({Sum.inl i, Sum.inr i} : Finset (Dir d)),
        (Phi C b κ κ e e x (y + dirVec f) y - Phi C b κ κ e e x y y) := by
  rw [monoAt_a2, Xc_add_left, mu4_add, mu4_Xc_ds, mu4_Xc_ds, sum_pair (by simp)]

theorem mu4_Xc_b2 (i : Fin d) (y : Lam d L N) :
    mu4 b κ κ (Xc C (monoAt (Mono.b2 s(i, i)) y) (gmono4 e e x)) =
      ∑ f ∈ ({Sum.inl i, Sum.inr i} : Finset (Dir d)),
        (Phi C b κ κ e e x y (y + dirVec f) - Phi C b κ κ e e x y y) := by
  rw [monoAt_b2, Xc_add_left, mu4_add, mu4_Xc_sd, mu4_Xc_sd, sum_pair (by simp)]

theorem mu4_Xc_monoSet_mono4sSet (A : Lam d L N → Alg d L N) (Y X : Finset (Lam d L N))
    (i : Fin d) :
    mu4 b κ κ (Xc C (∑ y ∈ Y, A y) (mono4sSet i i X)) = ∑ x ∈ X, (1 / 2 : ℂ) *
      (∑ y ∈ Y, mu4 b κ κ (Xc C (A y) (gmono4 (Sum.inl i) (Sum.inl i) x)) +
        ∑ y ∈ Y, mu4 b κ κ (Xc C (A y) (gmono4 (Sum.inr i) (Sum.inr i) x))) := by
  rw [mu4_Xc_mono4sSet]
  refine sum_congr rfl fun x _ => ?_
  simp only [← XcL_apply, map_sum, LinearMap.sum_apply, mu4_sum]

end Expand

namespace CovH

variable {C : Matrix (Lam d L N) (Lam d L N) ℂ} {r : ℕ} (H : CovH C r)
include H

variable {b : Lam d L N} {X : Finset (Lam d L N)}
  (hX : ∀ x ∈ X, 2 * (supNorm (x - b) + r + 4) < L ^ N)
include hX

theorem mu4_m2_univ_X (κ i i' : Fin d) :
    mu4 b κ κ (Xc C (monoSet (Mono.m2 i' i') univ) (mono4sSet i i X)) = 0 := by
  rw [monoSet, mu4_Xc_monoSet_mono4sSet]
  refine sum_eq_zero fun x hx => ?_
  have h : ∀ e : Dir d, ∑ y, mu4 b κ κ (Xc C (monoAt (Mono.m2 i' i') y) (gmono4 e e x)) = 0 := by
    intro e
    simp only [mu4_Xc_m2, ← mul_sum]
    rw [sum_comm, sum_eq_zero fun f _ => H.sum_grad_y (by have := hX x hx; omega) κ κ e e f,
      mul_zero]
  rw [h, h]; ring

theorem mu4_m2_X_univ (κ i i' : Fin d) :
    mu4 b κ κ (Xc C (monoSet (Mono.m2 i' i') X) (mono4sSet i i univ)) = 0 := by
  rw [monoSet, mu4_Xc_monoSet_mono4sSet]
  have h : ∀ e : Dir d, ∑ x, ∑ y ∈ X,
      mu4 b κ κ (Xc C (monoAt (Mono.m2 i' i') y) (gmono4 e e x)) = 0 := by
    intro e
    rw [sum_comm]
    refine sum_eq_zero fun y hy => ?_
    simp only [mu4_Xc_m2, ← mul_sum]
    rw [sum_comm, sum_eq_zero fun f _ => H.sum_grad_x (hX y hy) κ κ e e f, mul_zero]
  simp only [mul_add, sum_add_distrib, ← mul_sum, h]; ring

theorem mu4_a2_univ_X (κ i i' : Fin d) :
    mu4 b κ κ (Xc C (monoSet (Mono.a2 s(i', i')) univ) (mono4sSet i i X)) = 0 := by
  rw [monoSet, mu4_Xc_monoSet_mono4sSet]
  refine sum_eq_zero fun x hx => ?_
  have h : ∀ e : Dir d, ∑ y, mu4 b κ κ (Xc C (monoAt (Mono.a2 s(i', i')) y) (gmono4 e e x)) = 0 := by
    intro e
    simp only [mu4_Xc_a2]
    rw [sum_comm]
    exact H.sum_a2_y (hX x hx) κ κ e e i'
  rw [h, h]; ring

theorem mu4_a2_X_univ (κ i i' : Fin d) :
    mu4 b κ κ (Xc C (monoSet (Mono.a2 s(i', i')) X) (mono4sSet i i univ)) = 0 := by
  rw [monoSet, mu4_Xc_monoSet_mono4sSet]
  have h : ∀ e : Dir d, ∑ x, ∑ y ∈ X,
      mu4 b κ κ (Xc C (monoAt (Mono.a2 s(i', i')) y) (gmono4 e e x)) = 0 := by
    intro e
    rw [sum_comm]
    refine sum_eq_zero fun y hy => ?_
    simp only [mu4_Xc_a2]
    rw [sum_comm]
    exact sum_eq_zero fun f _ => H.sum_a2_x (hX y hy) κ κ e e f
  simp only [mul_add, sum_add_distrib, ← mul_sum, h]; ring

theorem mu4_b2_univ_X (κ i i' : Fin d) :
    mu4 b κ κ (Xc C (monoSet (Mono.b2 s(i', i')) univ) (mono4sSet i i X)) = 0 := by
  rw [monoSet, mu4_Xc_monoSet_mono4sSet]
  refine sum_eq_zero fun x hx => ?_
  have h : ∀ e : Dir d, ∑ y, mu4 b κ κ (Xc C (monoAt (Mono.b2 s(i', i')) y) (gmono4 e e x)) = 0 := by
    intro e
    simp only [mu4_Xc_b2]
    rw [sum_comm]
    exact H.sum_b2_y (hX x hx) κ κ e e i'
  rw [h, h]; ring

theorem mu4_b2_X_univ (κ i i' : Fin d) :
    mu4 b κ κ (Xc C (monoSet (Mono.b2 s(i', i')) X) (mono4sSet i i univ)) = 0 := by
  rw [monoSet, mu4_Xc_monoSet_mono4sSet]
  have h : ∀ e : Dir d, ∑ x, ∑ y ∈ X,
      mu4 b κ κ (Xc C (monoAt (Mono.b2 s(i', i')) y) (gmono4 e e x)) = 0 := by
    intro e
    rw [sum_comm]
    refine sum_eq_zero fun y hy => ?_
    simp only [mu4_Xc_b2]
    rw [sum_comm]
    exact sum_eq_zero fun f _ => H.sum_b2_x (hX y hy) κ κ e e f
  simp only [mul_add, sum_add_distrib, ← mul_sum, h]; ring

end CovH

end

end Step2
