import Step2.Coup.Wick2

/-!
# The lattice sums in the Wick evaluation (`h02uv-outline.tex`, `prop:C4b`(c))

For a covariance `C` that is translation invariant, symmetric and of range `r` with `2r < L^N`:

* `first_moment`: `∑_a C(a, x) r(a - x) = 0` (reflection symmetry);
* `row_sum`: `∑_a C(a, x) = C⁽¹⁾ := ∑_a C(a, 0)`;
* `sum_E1`: `∑_a (C(a, x+e) - C(a, x)) (ℓ(a) - ℓ(x)) = C⁽¹⁾ (ℓ(x+e) - ℓ(x))`;
* `sum_E2`: `∑_x (C(a, x+e) - C(a, x)) Δ(x) (ℓ(a) - ℓ(x)) = C⁽¹⁾ (e·κ)(e'·κ')`;

where `ℓ = lift b · κ` is affine near the base `b`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Matrix

variable {d L N : ℕ} [NeZero L]

theorem rep_neg' {z : Lam d L N} (h : 2 * supNorm z < L ^ N) : rep (-z) = -rep z := by
  refine (eq_rep ?_ ?_).symm
  · rw [prj_neg, prj_rep]
  · rw [supNormZ_neg, supNormZ_rep_eq]; exact h

/-- `lift` is affine on small balls. -/
theorem lift_sub_eq {b x a : Lam d L N} (h : 2 * (supNorm (x - b) + supNorm (a - x)) < L ^ N)
    (κ : Fin d) : (lift b a κ : ℂ) = lift b x κ + (rep (a - x) κ : ℂ) := by
  have h' : 2 * (supNorm (x - b) + supNormZ (rep (a - x))) < L ^ N := by
    rwa [supNormZ_rep_eq]
  have := congrFun (lift_add (b := b) (x := x) h') κ
  rw [prj_rep, add_sub_cancel] at this
  rw [this, Pi.add_apply]; push_cast; rfl

theorem lift_dirVec_eq {b x : Lam d L N} (h : 2 * (supNorm (x - b) + 1) < L ^ N) (e : Dir d)
    (κ : Fin d) : (lift b (x + dirVec e) κ : ℂ) = lift b x κ + (dirZ e κ : ℂ) := by
  have h' : 2 * (supNorm (x - b) + supNormZ (dirZ e)) < L ^ N := by
    have := supNormZ_dirZ (d := d) e; omega
  have := congrFun (lift_add (b := b) (x := x) h') κ
  rw [prj_dirZ] at this
  rw [this, Pi.add_apply]; push_cast; rfl

theorem supNorm_tri (x y z : Lam d L N) : supNorm (x - z) ≤ supNorm (x - y) + supNorm (y - z) := by
  have := supNorm_add_le (x - y) (y - z)
  rwa [sub_add_sub_cancel] at this

theorem supNorm_shift (x b : Lam d L N) (e : Dir d) :
    supNorm (x + dirVec e - b) ≤ supNorm (x - b) + 1 := by
  have := supNorm_add_le (x - b) (dirVec e)
  have h1 := supNorm_dirVec_le (n := L ^ N) e
  rw [show x - b + dirVec e = x + dirVec e - b by abel] at this
  omega

theorem supNorm_shift' (x b : Lam d L N) (e : Dir d) :
    supNorm (x - dirVec e - b) ≤ supNorm (x - b) + 1 := by
  have := supNorm_add_le (x - b) (-dirVec e)
  have h1 := supNorm_dirVec_le (n := L ^ N) e
  rw [supNorm_neg, show x - b + -dirVec e = x - dirVec e - b by abel] at this
  omega

/-- The hypotheses on the covariance. -/
structure CovH (C : Matrix (Lam d L N) (Lam d L N) ℂ) (r : ℕ) : Prop where
  htr : ∀ x y t, C (x + t) (y + t) = C x y
  hsym : ∀ x y, C x y = C y x
  hr : ∀ x y, r < supNorm (x - y) → C x y = 0
  h2r : 2 * r < L ^ N

namespace CovH

variable {C : Matrix (Lam d L N) (Lam d L N) ℂ} {r : ℕ} (H : CovH C r)
include H

theorem near {x y : Lam d L N} (h : C x y ≠ 0) : supNorm (x - y) ≤ r := by
  by_contra hc; exact h (H.hr x y (by omega))

/-- `C⁽¹⁾ = ∑_a C(a, x)` does not depend on `x`. -/
theorem row_sum (x : Lam d L N) : ∑ a, C a x = ∑ a, C a 0 := by
  refine Fintype.sum_equiv (Equiv.addRight (-x)) _ _ fun a => ?_
  have := H.htr a x (-x)
  simp only [add_neg_cancel] at this
  simp [this]

theorem col_sum (a : Lam d L N) : ∑ x, C a x = ∑ x, C x 0 := by
  rw [← H.row_sum a]; exact sum_congr rfl fun x _ => H.hsym a x

/-- **The first moment vanishes** (reflection symmetry). -/
theorem first_moment (x : Lam d L N) (κ : Fin d) :
    ∑ a, C a x * (rep (a - x) κ : ℂ) = 0 := by
  have e1 : ∑ a, C a x * (rep (a - x) κ : ℂ) = ∑ z, C z 0 * (rep z κ : ℂ) := by
    refine Fintype.sum_equiv (Equiv.addRight (-x)) _ _ fun a => ?_
    have := H.htr a x (-x)
    simp only [add_neg_cancel] at this
    simp [this, sub_eq_add_neg]
  have e2 : ∑ z, C z 0 * (rep z κ : ℂ) = -∑ z, C z 0 * (rep z κ : ℂ) := by
    rw [← sum_neg_distrib]
    refine Fintype.sum_equiv (Equiv.neg _) _ _ fun z => ?_
    simp only [Equiv.neg_apply]
    by_cases hz : C z 0 = 0
    · have : C (-z) 0 = 0 := by
        have h1 := H.htr (-z) 0 z
        simp only [neg_add_cancel, zero_add] at h1
        rw [← h1, H.hsym, hz]
      rw [hz, this]; simp
    · have h1 := H.htr (-z) 0 z
      simp only [neg_add_cancel, zero_add] at h1
      have hz' : C (-z) 0 = C z 0 := by rw [← h1, H.hsym]
      have hn := H.near hz
      rw [sub_zero] at hn
      rw [hz', rep_neg' (by have := H.h2r; omega), Pi.neg_apply]
      push_cast; ring
  rw [e1]
  linear_combination e2 / 2

/-- The first moment, with the lift. -/
theorem moment_lift {b x : Lam d L N} (hx : 2 * (supNorm (x - b) + r) < L ^ N) (κ : Fin d) :
    ∑ a, C a x * ((lift b a κ : ℂ) - lift b x κ) = 0 := by
  rw [← H.first_moment x κ]
  refine sum_congr rfl fun a _ => ?_
  by_cases h : C a x = 0
  · simp [h]
  · have hn := H.near h
    rw [lift_sub_eq (b := b) (x := x) (a := a) (by omega), add_sub_cancel_left]

/-- **(E1)** `∑_a (C(a, x+e) - C(a, x)) (ℓ(a) - ℓ(x)) = C⁽¹⁾ (ℓ(x+e) - ℓ(x))`. -/
theorem sum_E1 {b x : Lam d L N} (hx : 2 * (supNorm (x - b) + 1 + r) < L ^ N) (f : Dir d)
    (κ : Fin d) :
    ∑ a, (C a (x + dirVec f) - C a x) * ((lift b a κ : ℂ) - lift b x κ) =
      (∑ a, C a 0) * ((lift b (x + dirVec f) κ : ℂ) - lift b x κ) := by
  have h1 := supNorm_shift x b f
  have m1 := H.moment_lift (x := x + dirVec f) (b := b) (by omega) κ
  have m0 := H.moment_lift (x := x) (b := b) (by omega) κ
  have hs := H.row_sum (x + dirVec f)
  have e : ∀ a, (C a (x + dirVec f) - C a x) * ((lift b a κ : ℂ) - lift b x κ) =
      C a (x + dirVec f) * ((lift b a κ : ℂ) - lift b (x + dirVec f) κ) +
        C a (x + dirVec f) * ((lift b (x + dirVec f) κ : ℂ) - lift b x κ) -
        C a x * ((lift b a κ : ℂ) - lift b x κ) := fun a => by ring
  simp only [e, sum_sub_distrib, sum_add_distrib, ← sum_mul, m1, m0, hs]
  ring

/-- **(E2)** `∑_x (C(a, x+e) - C(a, x)) (ℓ'(x+e') - ℓ'(x)) (ℓ(a) - ℓ(x)) = C⁽¹⁾ (e·κ)(e'·κ')`. -/
theorem sum_E2 {b a : Lam d L N} (ha : 2 * (supNorm (a - b) + r + 2) < L ^ N) (e e' : Dir d)
    (κ κ' : Fin d) :
    ∑ x, (C a (x + dirVec e) - C a x) * ((lift b (x + dirVec e') κ' : ℂ) - lift b x κ') *
      ((lift b a κ : ℂ) - lift b x κ) = (∑ x, C x 0) * (dirZ e κ : ℂ) * (dirZ e' κ' : ℂ) := by
  set g : Lam d L N → ℂ := fun x =>
    ((lift b (x + dirVec e') κ' : ℂ) - lift b x κ') * ((lift b a κ : ℂ) - lift b x κ)
  have hshift : ∑ x, C a (x + dirVec e) * g x = ∑ x, C a x * g (x - dirVec e) := by
    refine Fintype.sum_equiv (Equiv.addRight (dirVec e)) _ _ fun x => ?_
    simp
  have hterm : ∀ x, C a x * (g (x - dirVec e) - g x) =
      C a x * ((dirZ e κ : ℂ) * (dirZ e' κ' : ℂ)) := by
    intro x
    by_cases h : C a x = 0
    · simp [h]
    · have hn := H.near h
      have t1 := supNorm_tri x a b
      rw [supNorm_sub_comm] at hn
      have t2 := supNorm_shift' x b e
      have l1 := lift_dirVec_eq (b := b) (x := x) (by omega) e' κ'
      have l2 := lift_dirVec_eq (b := b) (x := x - dirVec e) (by omega) e' κ'
      have l3 := lift_dirVec_eq (b := b) (x := x - dirVec e) (by omega) e κ
      rw [sub_add_cancel] at l3
      simp only [g]
      rw [l1, l2, l3]
      ring
  calc ∑ x, (C a (x + dirVec e) - C a x) * ((lift b (x + dirVec e') κ' : ℂ) - lift b x κ') *
        ((lift b a κ : ℂ) - lift b x κ)
      = ∑ x, C a (x + dirVec e) * g x - ∑ x, C a x * g x := by
        rw [← sum_sub_distrib]; exact sum_congr rfl fun x _ => by simp only [g]; ring
    _ = ∑ x, C a x * (g (x - dirVec e) - g x) := by
        rw [hshift, ← sum_sub_distrib]; exact sum_congr rfl fun x _ => by ring
    _ = _ := by
        rw [sum_congr rfl fun x _ => hterm x, ← sum_mul, H.col_sum]; ring

end CovH

/-! ### The mass term -/

theorem pm_ev (a : Lam d L N) : PM (ev ((a, 1) : Sf (Lam d L N))) (ev (a, -1)) :=
  ⟨fun x => by simp [ev, Pi.single_apply, Prod.ext_iff], fun x => by
    simp [ev, Pi.single_apply, Prod.ext_iff]⟩

theorem pairC_v0_ev (C : Matrix (Lam d L N) (Lam d L N) ℂ) (e e' : Dir d) (x a : Lam d L N) :
    pairC C (v4g e e' x 0) (ev (a, -1)) = C a (x + dirVec e) - C a x := by
  show pairC C (ev (x + dirVec e, 1) - ev (x, 1)) (ev (a, -1)) = _
  simp [pairC, ev, Pi.single_apply, Prod.ext_iff, mul_sub, sub_mul, sum_sub_distrib]

theorem pairC_v2_ev (C : Matrix (Lam d L N) (Lam d L N) ℂ) (e e' : Dir d) (x a : Lam d L N) :
    pairC C (v4g e e' x 2) (ev (a, -1)) = C a x := by
  show pairC C (ev (x, 1)) (ev (a, -1)) = _
  simp [pairC, ev, Pi.single_apply, Prod.ext_iff]

theorem pairC_ev_v1 (C : Matrix (Lam d L N) (Lam d L N) ℂ) (e e' : Dir d) (x a : Lam d L N) :
    pairC C (ev (a, 1)) (v4g e e' x 1) = C (x + dirVec e') a - C x a := by
  show pairC C (ev (a, 1)) (ev (x + dirVec e', -1) - ev (x, -1)) = _
  simp [pairC, ev, Pi.single_apply, Prod.ext_iff, mul_sub, sub_mul, sum_sub_distrib]

theorem pairC_ev_v3 (C : Matrix (Lam d L N) (Lam d L N) ℂ) (e e' : Dir d) (x a : Lam d L N) :
    pairC C (ev (a, 1)) (v4g e e' x 3) = C x a := by
  show pairC C (ev (a, 1)) (ev (x, -1)) = _
  simp [pairC, ev, Pi.single_apply, Prod.ext_iff]

/-- `mu4` of the cross contraction of `ψ_a ψ̄_a` with `gmono4`. -/
theorem mu4_Xc_mass (C : Matrix (Lam d L N) (Lam d L N) ℂ) (b : Lam d L N) (κ κ' : Fin d)
    (e e' : Dir d) (x a : Lam d L N) :
    mu4 b κ κ' (Xc C (psi a * psibar a) (gmono4 e e' x)) =
      (C a (x + dirVec e) - C a x) * ((lift b (x + dirVec e') κ' : ℂ) - lift b x κ') *
          ((lift b a κ : ℂ) - lift b x κ) +
        (C (x + dirVec e') a - C x a) * ((lift b (x + dirVec e) κ : ℂ) - lift b x κ) *
          ((lift b a κ' : ℂ) - lift b x κ') +
        (C a x + C x a) * (((lift b (x + dirVec e) κ : ℂ) - lift b x κ) *
          ((lift b (x + dirVec e') κ' : ℂ) - lift b x κ')) := by
  have h := mu4_Xc_gmono4 C (pm_ev a) b κ κ' e e' x
  rw [show psi a * psibar a = ExteriorAlgebra.ι ℂ (ev ((a, 1) : Sf (Lam d L N))) *
    ExteriorAlgebra.ι ℂ (ev (a, -1)) from rfl, h, pairC_v0_ev, pairC_v2_ev, pairC_ev_v1,
    pairC_ev_v3, col_ev_pos, col_ev_neg]
  simp
  ring

/-! ### The general pair `ψ_s ψ̄_t` -/

/-- `mu4 Xc(ψ_s ψ̄_t, gmono4 e e' x)`. -/
def Phi (C : Matrix (Lam d L N) (Lam d L N) ℂ) (b : Lam d L N) (κ κ' : Fin d) (e e' : Dir d)
    (x s t : Lam d L N) : ℂ :=
  (C t (x + dirVec e) - C t x) * ((lift b (x + dirVec e') κ' : ℂ) - lift b x κ') *
      ((lift b s κ : ℂ) - lift b x κ) +
    (C (x + dirVec e') s - C x s) * ((lift b (x + dirVec e) κ : ℂ) - lift b x κ) *
      ((lift b t κ' : ℂ) - lift b x κ') +
    (C t x + C x s) * (((lift b (x + dirVec e) κ : ℂ) - lift b x κ) *
      ((lift b (x + dirVec e') κ' : ℂ) - lift b x κ'))

theorem pm_ev2 (s t : Lam d L N) : PM (ev ((s, 1) : Sf (Lam d L N))) (ev (t, -1)) :=
  ⟨fun x => by simp [ev, Pi.single_apply, Prod.ext_iff], fun x => by
    simp [ev, Pi.single_apply, Prod.ext_iff]⟩

theorem mu4_Xc_pair (C : Matrix (Lam d L N) (Lam d L N) ℂ) (b : Lam d L N) (κ κ' : Fin d)
    (e e' : Dir d) (x s t : Lam d L N) :
    mu4 b κ κ' (Xc C (psi s * psibar t) (gmono4 e e' x)) = Phi C b κ κ' e e' x s t := by
  have h := mu4_Xc_gmono4 C (pm_ev2 s t) b κ κ' e e' x
  rw [show psi s * psibar t = ExteriorAlgebra.ι ℂ (ev ((s, 1) : Sf (Lam d L N))) *
    ExteriorAlgebra.ι ℂ (ev (t, -1)) from rfl, h, pairC_v0_ev, pairC_v2_ev, pairC_ev_v1,
    pairC_ev_v3, col_ev_pos, col_ev_neg, Phi]
  simp
  ring

theorem sum_mul_near {F G : Lam d L N → ℂ} {c : ℂ} (h : ∀ y, F y ≠ 0 → G y = c) :
    ∑ y, F y * G y = c * ∑ y, F y := by
  rw [mul_sum]
  refine sum_congr rfl fun y _ => ?_
  by_cases hy : F y = 0
  · simp [hy]
  · rw [h y hy, mul_comm]

theorem sum_shift_eq (F : Lam d L N → ℂ) (v : Lam d L N) : ∑ y, F (y + v) = ∑ y, F y :=
  Fintype.sum_equiv (Equiv.addRight v) _ _ fun _ => rfl

namespace CovH

variable {C : Matrix (Lam d L N) (Lam d L N) ℂ} {r : ℕ} (H : CovH C r)
include H

/-- **The mass term, `ψψ̄` global**: `∑_a mu4 Xc(ψ_aψ̄_a, gmono4 e e' x) = 4 C⁽¹⁾ (e·κ)(e'·κ')`. -/
theorem sum_mass_a {b x : Lam d L N} (hx : 2 * (supNorm (x - b) + 1 + r) < L ^ N)
    (κ κ' : Fin d) (e e' : Dir d) :
    ∑ a, mu4 b κ κ' (Xc C (psi a * psibar a) (gmono4 e e' x)) =
      4 * (∑ a, C a 0) * (dirZ e κ : ℂ) * (dirZ e' κ' : ℂ) := by
  have l0 := lift_dirVec_eq (b := b) (x := x) (by omega) e κ
  have l1 := lift_dirVec_eq (b := b) (x := x) (by omega) e' κ'
  have E1 := H.sum_E1 hx e κ
  have E1' := H.sum_E1 hx e' κ'
  have hs := H.row_sum x
  have hs' : ∑ a, C x a = ∑ a, C a 0 := by rw [← hs]; exact sum_congr rfl fun a _ => H.hsym x a
  have hsym' : ∀ a, C (x + dirVec e') a - C x a = C a (x + dirVec e') - C a x := fun a => by
    rw [H.hsym (x + dirVec e'), H.hsym x]
  simp only [mu4_Xc_mass, hsym', sum_add_distrib]
  rw [show ∑ a, (C a (x + dirVec e) - C a x) * ((lift b (x + dirVec e') κ' : ℂ) - lift b x κ') *
      ((lift b a κ : ℂ) - lift b x κ) = ((lift b (x + dirVec e') κ' : ℂ) - lift b x κ') *
      ∑ a, (C a (x + dirVec e) - C a x) * ((lift b a κ : ℂ) - lift b x κ) by
        rw [mul_sum]; exact sum_congr rfl fun a _ => by ring,
    show ∑ a, (C a (x + dirVec e') - C a x) * ((lift b (x + dirVec e) κ : ℂ) - lift b x κ) *
      ((lift b a κ' : ℂ) - lift b x κ') = ((lift b (x + dirVec e) κ : ℂ) - lift b x κ) *
      ∑ a, (C a (x + dirVec e') - C a x) * ((lift b a κ' : ℂ) - lift b x κ') by
        rw [mul_sum]; exact sum_congr rfl fun a _ => by ring,
    E1, E1', ← sum_mul, sum_add_distrib, hs, hs', l0, l1]
  ring

/-- **The mass term, `gmono4` global**: `∑_x mu4 Xc(ψ_aψ̄_a, gmono4 e e' x) = 4 C⁽¹⁾ (e·κ)(e'·κ')`. -/
theorem sum_mass_x {b a : Lam d L N} (ha : 2 * (supNorm (a - b) + r + 2) < L ^ N)
    (κ κ' : Fin d) (e e' : Dir d) :
    ∑ x, mu4 b κ κ' (Xc C (psi a * psibar a) (gmono4 e e' x)) =
      4 * (∑ a, C a 0) * (dirZ e κ : ℂ) * (dirZ e' κ' : ℂ) := by
  have E2 := H.sum_E2 ha e e' κ κ'
  have E2' := H.sum_E2 ha e' e κ' κ
  have hc := H.col_sum a
  have hsym' : ∀ x, C (x + dirVec e') a - C x a = C a (x + dirVec e') - C a x := fun x => by
    rw [H.hsym (x + dirVec e'), H.hsym x]
  have h3 : ∀ x, (C a x + C x a) * (((lift b (x + dirVec e) κ : ℂ) - lift b x κ) *
      ((lift b (x + dirVec e') κ' : ℂ) - lift b x κ')) =
      (C a x + C x a) * ((dirZ e κ : ℂ) * (dirZ e' κ' : ℂ)) := by
    intro x
    by_cases h : C a x = 0
    · rw [h, H.hsym x a, h]; simp
    · have hn := H.near h
      rw [supNorm_sub_comm] at hn
      have t1 := supNorm_tri x a b
      rw [lift_dirVec_eq (b := b) (x := x) (by omega) e κ,
        lift_dirVec_eq (b := b) (x := x) (by omega) e' κ']
      ring
  simp only [mu4_Xc_mass, hsym', h3, sum_add_distrib, ← sum_mul]
  rw [E2, show ∑ x, (C a (x + dirVec e') - C a x) * ((lift b (x + dirVec e) κ : ℂ) - lift b x κ) *
      ((lift b a κ' : ℂ) - lift b x κ') = (∑ x, C x 0) * (dirZ e' κ' : ℂ) * (dirZ e κ : ℂ) from E2',
    hc, show ∑ x, C x a = ∑ x, C x 0 by rw [← hc]; exact sum_congr rfl fun x _ => H.hsym x a]
  have : ∑ x, C x 0 = ∑ a, C a 0 := rfl
  rw [this]
  ring

end CovH

theorem near_bound (y x b δ₁ δ₂ : Lam d L N) (h₁ : supNorm δ₁ ≤ 1) (h₂ : supNorm δ₂ ≤ 1) :
    supNorm (y - b) ≤ supNorm (y + δ₁ - (x + δ₂)) + supNorm (x - b) + 2 := by
  have e : y - b = (y + δ₁ - (x + δ₂)) + (x - b) + (δ₂ - δ₁) := by abel
  have a1 := supNorm_add_le (y + δ₁ - (x + δ₂) + (x - b)) (δ₂ - δ₁)
  have a2 := supNorm_add_le (y + δ₁ - (x + δ₂)) (x - b)
  have a3 := supNorm_add_le δ₂ (-δ₁)
  rw [supNorm_neg, ← sub_eq_add_neg] at a3
  rw [e]; omega

theorem supNorm_zero' : supNorm (0 : Lam d L N) ≤ 1 := by
  unfold supNorm
  refine Finset.sup_le fun i _ => ?_
  show zabs ((0 : Fin d → ZMod (L ^ N)) i) ≤ 1
  simp [zabs]

namespace CovH

variable {C : Matrix (Lam d L N) (Lam d L N) ℂ} {r : ℕ} (H : CovH C r)
include H

/-- If some `C(y + δ₁, x + δ₂)` with `|δᵢ| ≤ 1` is nonzero, then `y` is close to `b`. -/
theorem near_of_ne {y x b δ₁ δ₂ : Lam d L N} (h₁ : supNorm δ₁ ≤ 1) (h₂ : supNorm δ₂ ≤ 1)
    (h : C (y + δ₁) (x + δ₂) ≠ 0) : supNorm (y - b) ≤ r + supNorm (x - b) + 2 := by
  have := H.near h
  have := near_bound y x b δ₁ δ₂ h₁ h₂
  omega

theorem near_of_ne' {y x b δ₁ δ₂ : Lam d L N} (h₁ : supNorm δ₁ ≤ 1) (h₂ : supNorm δ₂ ≤ 1)
    (h : C (x + δ₂) (y + δ₁) ≠ 0) : supNorm (y - b) ≤ r + supNorm (x - b) + 2 :=
  H.near_of_ne h₁ h₂ (by rwa [H.hsym])

/-- **The `(∇ψ)(∇ψ̄)` cross term, summed over the gradient monomial**: zero. -/
theorem sum_grad_y {b x : Lam d L N} (hx : 2 * (supNorm (x - b) + r + 3) < L ^ N)
    (κ κ' : Fin d) (e e' f : Dir d) :
    ∑ y, (Phi C b κ κ' e e' x (y + dirVec f) (y + dirVec f) - Phi C b κ κ' e e' x (y + dirVec f) y -
      Phi C b κ κ' e e' x y (y + dirVec f) + Phi C b κ κ' e e' x y y) = 0 := by
  set A : Lam d L N → ℂ := fun t =>
    (C t (x + dirVec e) - C t x) * ((lift b (x + dirVec e') κ' : ℂ) - lift b x κ')
  set B : Lam d L N → ℂ := fun s =>
    (C (x + dirVec e') s - C x s) * ((lift b (x + dirVec e) κ : ℂ) - lift b x κ)
  have he : supNorm (dirVec e : Lam d L N) ≤ 1 := supNorm_dirVec_le e
  have he' : supNorm (dirVec e' : Lam d L N) ≤ 1 := supNorm_dirVec_le e'
  have hf : supNorm (dirVec f : Lam d L N) ≤ 1 := supNorm_dirVec_le f
  have h0 := supNorm_zero' (d := d) (L := L) (N := N)
  have e1 : ∀ y, Phi C b κ κ' e e' x (y + dirVec f) (y + dirVec f) - Phi C b κ κ' e e' x (y + dirVec f) y -
      Phi C b κ κ' e e' x y (y + dirVec f) + Phi C b κ κ' e e' x y y =
      (A (y + dirVec f) - A y) * ((lift b (y + dirVec f) κ : ℂ) - lift b y κ) +
      (B (y + dirVec f) - B y) * ((lift b (y + dirVec f) κ' : ℂ) - lift b y κ') := fun y => by
    simp only [Phi, A, B]; ring
  have hA : ∀ y, A (y + dirVec f) - A y ≠ 0 →
      (lift b (y + dirVec f) κ : ℂ) - lift b y κ = dirZ f κ := by
    intro y hy
    have : supNorm (y - b) ≤ r + supNorm (x - b) + 2 := by
      by_contra hc
      apply hy
      simp only [A]
      have z1 : C (y + dirVec f) (x + dirVec e) = 0 := by
        by_contra h; exact hc (H.near_of_ne hf he h)
      have z2 : C (y + dirVec f) x = 0 := by
        by_contra h; exact hc (H.near_of_ne hf h0 (by simpa using h))
      have z3 : C y (x + dirVec e) = 0 := by
        by_contra h; exact hc (H.near_of_ne h0 he (by simpa using h))
      have z4 : C y x = 0 := by
        by_contra h; exact hc (H.near_of_ne h0 h0 (by simpa using h))
      rw [z1, z2, z3, z4]; ring
    rw [lift_dirVec_eq (by omega)]; ring
  have hB : ∀ y, B (y + dirVec f) - B y ≠ 0 →
      (lift b (y + dirVec f) κ' : ℂ) - lift b y κ' = dirZ f κ' := by
    intro y hy
    have : supNorm (y - b) ≤ r + supNorm (x - b) + 2 := by
      by_contra hc
      apply hy
      simp only [B]
      have z1 : C (x + dirVec e') (y + dirVec f) = 0 := by
        by_contra h; exact hc (H.near_of_ne' hf he' h)
      have z2 : C x (y + dirVec f) = 0 := by
        by_contra h; exact hc (H.near_of_ne' hf h0 (by simpa using h))
      have z3 : C (x + dirVec e') y = 0 := by
        by_contra h; exact hc (H.near_of_ne' h0 he' (by simpa using h))
      have z4 : C x y = 0 := by
        by_contra h; exact hc (H.near_of_ne' h0 h0 (by simpa using h))
      rw [z1, z2, z3, z4]; ring
    rw [lift_dirVec_eq (by omega)]; ring
  simp only [e1, sum_add_distrib]
  rw [sum_mul_near hA, sum_mul_near hB, sum_sub_distrib, sum_sub_distrib,
    sum_shift_eq A, sum_shift_eq B]
  ring


/-- `∑_x (C(t, x+e) - C(t, x)) (ℓ'(x+e') - ℓ'(x)) = 0` for `t` near the base. -/
theorem sumA_x {b t : Lam d L N} (ht : 2 * (supNorm (t - b) + r + 3) < L ^ N)
    (κ' : Fin d) (e e' : Dir d) :
    ∑ x, (C t (x + dirVec e) - C t x) * ((lift b (x + dirVec e') κ' : ℂ) - lift b x κ') = 0 := by
  have he : supNorm (dirVec e : Lam d L N) ≤ 1 := supNorm_dirVec_le e
  have h0 := supNorm_zero' (d := d) (L := L) (N := N)
  have hn : ∀ x, C t (x + dirVec e) - C t x ≠ 0 →
      (lift b (x + dirVec e') κ' : ℂ) - lift b x κ' = dirZ e' κ' := by
    intro x hx
    have : supNorm (x - b) ≤ r + supNorm (t - b) + 2 := by
      by_contra hc
      apply hx
      have z1 : C t (x + dirVec e) = 0 := by
        by_contra h; exact hc (H.near_of_ne' (x := t) he h0 (by simpa using h))
      have z2 : C t x = 0 := by
        by_contra h; exact hc (H.near_of_ne' (x := t) h0 h0 (by simpa using h))
      rw [z1, z2, sub_zero]
    rw [lift_dirVec_eq (by omega)]; ring
  rw [sum_mul_near hn, sum_sub_distrib, sum_shift_eq (fun x => C t x), sub_self, mul_zero]

/-- `∑_x (C(x+e', s) - C(x, s)) (ℓ(x+e) - ℓ(x)) = 0` for `s` near the base. -/
theorem sumB_x {b s : Lam d L N} (hs : 2 * (supNorm (s - b) + r + 3) < L ^ N)
    (κ : Fin d) (e e' : Dir d) :
    ∑ x, (C (x + dirVec e') s - C x s) * ((lift b (x + dirVec e) κ : ℂ) - lift b x κ) = 0 := by
  rw [← H.sumA_x hs κ e' e]
  exact sum_congr rfl fun x _ => by rw [H.hsym (x + dirVec e'), H.hsym x]

/-- `∑_x (C(x, u) - C(x, v)) Δ₀(x) Δ₁(x) = 0` for `u`, `v` near the base. -/
theorem sumDD_x {b u v : Lam d L N} (hu : 2 * (supNorm (u - b) + r + 3) < L ^ N)
    (hv : 2 * (supNorm (v - b) + r + 3) < L ^ N) (κ κ' : Fin d) (e e' : Dir d) :
    ∑ x, (C x u - C x v) * (((lift b (x + dirVec e) κ : ℂ) - lift b x κ) *
      ((lift b (x + dirVec e') κ' : ℂ) - lift b x κ')) = 0 := by
  have h0 := supNorm_zero' (d := d) (L := L) (N := N)
  have hn : ∀ x, C x u - C x v ≠ 0 → ((lift b (x + dirVec e) κ : ℂ) - lift b x κ) *
      ((lift b (x + dirVec e') κ' : ℂ) - lift b x κ') = (dirZ e κ : ℂ) * dirZ e' κ' := by
    intro x hx
    have : supNorm (x - b) ≤ r + max (supNorm (u - b)) (supNorm (v - b)) + 2 := by
      by_contra hc
      apply hx
      have z1 : C x u = 0 := by
        by_contra h; have := H.near_of_ne (x := u) (b := b) h0 h0 (by simpa using h); omega
      have z2 : C x v = 0 := by
        by_contra h; have := H.near_of_ne (x := v) (b := b) h0 h0 (by simpa using h); omega
      rw [z1, z2, sub_zero]
    rw [lift_dirVec_eq (by omega), lift_dirVec_eq (by omega)]; ring
  rw [sum_mul_near hn, sum_sub_distrib, H.row_sum u, H.row_sum v, sub_self, mul_zero]

/-- **The `(∇ψ)(∇ψ̄)` cross term, summed over the quartic monomial**: zero. -/
theorem sum_grad_x {b y : Lam d L N} (hy : 2 * (supNorm (y - b) + r + 4) < L ^ N)
    (κ κ' : Fin d) (e e' f : Dir d) :
    ∑ x, (Phi C b κ κ' e e' x (y + dirVec f) (y + dirVec f) - Phi C b κ κ' e e' x (y + dirVec f) y -
      Phi C b κ κ' e e' x y (y + dirVec f) + Phi C b κ κ' e e' x y y) = 0 := by
  have h1 := supNorm_shift y b f
  have l := lift_dirVec_eq (b := b) (x := y) (by omega) f κ
  have l' := lift_dirVec_eq (b := b) (x := y) (by omega) f κ'
  have e1 : ∀ x, Phi C b κ κ' e e' x (y + dirVec f) (y + dirVec f) - Phi C b κ κ' e e' x (y + dirVec f) y -
      Phi C b κ κ' e e' x y (y + dirVec f) + Phi C b κ κ' e e' x y y =
      (dirZ f κ : ℂ) * ((C (y + dirVec f) (x + dirVec e) - C (y + dirVec f) x) *
          ((lift b (x + dirVec e') κ' : ℂ) - lift b x κ') -
        (C y (x + dirVec e) - C y x) * ((lift b (x + dirVec e') κ' : ℂ) - lift b x κ')) +
      (dirZ f κ' : ℂ) * ((C (x + dirVec e') (y + dirVec f) - C x (y + dirVec f)) *
          ((lift b (x + dirVec e) κ : ℂ) - lift b x κ) -
        (C (x + dirVec e') y - C x y) * ((lift b (x + dirVec e) κ : ℂ) - lift b x κ)) := by
    intro x; simp only [Phi, l, l']; ring
  simp only [e1, sum_add_distrib, ← mul_sum, sum_sub_distrib]
  rw [H.sumA_x (t := y + dirVec f) (by omega), H.sumA_x (t := y) (by omega),
    H.sumB_x (s := y + dirVec f) (by omega), H.sumB_x (s := y) (by omega)]
  ring

/-- **The `(Δψ)ψ̄` cross term, summed over the gradient monomial**: zero (after the sum over
`±e_i`). -/
theorem sum_a2_y {b x : Lam d L N} (hx : 2 * (supNorm (x - b) + r + 4) < L ^ N)
    (κ κ' : Fin d) (e e' : Dir d) (i : Fin d) :
    ∑ f ∈ ({Sum.inl i, Sum.inr i} : Finset (Dir d)), ∑ y,
      (Phi C b κ κ' e e' x (y + dirVec f) y - Phi C b κ κ' e e' x y y) = 0 := by
  set A : Lam d L N → ℂ := fun t =>
    (C t (x + dirVec e) - C t x) * ((lift b (x + dirVec e') κ' : ℂ) - lift b x κ')
  set B : Lam d L N → ℂ := fun s =>
    (C (x + dirVec e') s - C x s) * ((lift b (x + dirVec e) κ : ℂ) - lift b x κ)
  have he : supNorm (dirVec e : Lam d L N) ≤ 1 := supNorm_dirVec_le e
  have he' : supNorm (dirVec e' : Lam d L N) ≤ 1 := supNorm_dirVec_le e'
  have h0 := supNorm_zero' (d := d) (L := L) (N := N)
  have e1 : ∀ f y, Phi C b κ κ' e e' x (y + dirVec f) y - Phi C b κ κ' e e' x y y =
      A y * ((lift b (y + dirVec f) κ : ℂ) - lift b y κ) +
      (B (y + dirVec f) - B y) * ((lift b y κ' : ℂ) - lift b x κ') +
      (C x (y + dirVec f) - C x y) * (((lift b (x + dirVec e) κ : ℂ) - lift b x κ) *
        ((lift b (x + dirVec e') κ' : ℂ) - lift b x κ')) := fun f y => by
    simp only [Phi, A, B]; ring
  -- the near region
  have hnA : ∀ y, A y ≠ 0 → supNorm (y - b) ≤ r + supNorm (x - b) + 2 := by
    intro y hy
    by_contra hc
    apply hy
    simp only [A]
    have z1 : C y (x + dirVec e) = 0 := by
      by_contra h; exact hc (H.near_of_ne h0 he (by simpa using h))
    have z2 : C y x = 0 := by
      by_contra h; exact hc (H.near_of_ne h0 h0 (by simpa using h))
    rw [z1, z2]; ring
  have hnB : ∀ y, B y ≠ 0 → supNorm (y - b) ≤ r + supNorm (x - b) + 2 := by
    intro y hy
    by_contra hc
    apply hy
    simp only [B]
    have z1 : C (x + dirVec e') y = 0 := by
      by_contra h; exact hc (H.near_of_ne' h0 he' (by simpa using h))
    have z2 : C x y = 0 := by
      by_contra h; exact hc (H.near_of_ne' h0 h0 (by simpa using h))
    rw [z1, z2]; ring
  -- the three parts
  have p1 : ∑ f ∈ ({Sum.inl i, Sum.inr i} : Finset (Dir d)), ∑ y,
      A y * ((lift b (y + dirVec f) κ : ℂ) - lift b y κ) = 0 := by
    rw [sum_comm]
    refine sum_eq_zero fun y _ => ?_
    rw [← mul_sum]
    by_cases hy : A y = 0
    · rw [hy, zero_mul]
    · have := hnA y hy
      rw [sum_pair (by simp), lift_dirVec_eq (by omega), lift_dirVec_eq (by omega)]
      simp [dirZ, Pi.single_apply]
  have p2 : ∀ f : Dir d, ∑ y, (B (y + dirVec f) - B y) * ((lift b y κ' : ℂ) - lift b x κ') = 0 := by
    intro f
    have hs : ∑ y, B (y + dirVec f) * ((lift b y κ' : ℂ) - lift b x κ') =
        ∑ y, B y * ((lift b (y - dirVec f) κ' : ℂ) - lift b x κ') := by
      rw [← sum_shift_eq (fun y => B y * ((lift b (y - dirVec f) κ' : ℂ) - lift b x κ'))
        (dirVec f)]
      simp
    have hB0 : ∑ y, B y = 0 := by
      simp only [B, ← sum_mul, sum_sub_distrib, H.col_sum, sub_self, zero_mul]
    have hterm : ∀ y, B y * ((lift b (y - dirVec f) κ' : ℂ) - lift b y κ') =
        B y * (-(dirZ f κ' : ℂ)) := by
      intro y
      by_cases hy : B y = 0
      · simp [hy]
      · have := hnB y hy
        have t := supNorm_shift' y b f
        have l := lift_dirVec_eq (b := b) (x := y - dirVec f) (by omega) f κ'
        rw [sub_add_cancel] at l
        rw [l]; ring
    rw [show ∑ y, (B (y + dirVec f) - B y) * ((lift b y κ' : ℂ) - lift b x κ') =
        ∑ y, B y * ((lift b (y - dirVec f) κ' : ℂ) - lift b y κ') by
      rw [show ∑ y, B y * ((lift b (y - dirVec f) κ' : ℂ) - lift b y κ') =
          ∑ y, B y * ((lift b (y - dirVec f) κ' : ℂ) - lift b x κ') -
          ∑ y, B y * ((lift b y κ' : ℂ) - lift b x κ') by
        rw [← sum_sub_distrib]; exact sum_congr rfl fun y _ => by ring, ← hs, ← sum_sub_distrib]
      exact sum_congr rfl fun y _ => by ring]
    rw [sum_congr rfl fun y _ => hterm y, ← sum_mul, hB0, zero_mul]
  have p3 : ∀ f : Dir d, ∑ y, (C x (y + dirVec f) - C x y) *
      (((lift b (x + dirVec e) κ : ℂ) - lift b x κ) *
        ((lift b (x + dirVec e') κ' : ℂ) - lift b x κ')) = 0 := by
    intro f
    rw [← sum_mul, sum_sub_distrib, sum_shift_eq (fun y => C x y), sub_self, zero_mul]
  simp only [e1, sum_add_distrib, p2, p3, add_zero, sum_const_zero]
  exact p1


/-- `∑_x B_x(s) (ℓ'(y) - ℓ'(x)) = C⁽¹⁾ (e·κ)(e'·κ')` for `s` near the base. -/
theorem sumB_lift_x {b s y : Lam d L N} (hs : 2 * (supNorm (s - b) + r + 3) < L ^ N)
    (κ κ' : Fin d) (e e' : Dir d) :
    ∑ x, (C (x + dirVec e') s - C x s) * ((lift b (x + dirVec e) κ : ℂ) - lift b x κ) *
      ((lift b y κ' : ℂ) - lift b x κ') =
      (∑ x, C x 0) * (dirZ e' κ' : ℂ) * (dirZ e κ : ℂ) := by
  have E := H.sum_E2 (a := s) (b := b) (by omega) e' e κ' κ
  have B0 := H.sumB_x hs κ e e'
  rw [← E]
  have : ∀ x, (C (x + dirVec e') s - C x s) * ((lift b (x + dirVec e) κ : ℂ) - lift b x κ) *
      ((lift b y κ' : ℂ) - lift b x κ') =
      (C s (x + dirVec e') - C s x) * ((lift b (x + dirVec e) κ : ℂ) - lift b x κ) *
        ((lift b s κ' : ℂ) - lift b x κ') +
      ((lift b y κ' : ℂ) - lift b s κ') * ((C (x + dirVec e') s - C x s) *
        ((lift b (x + dirVec e) κ : ℂ) - lift b x κ)) := fun x => by
    rw [H.hsym s (x + dirVec e'), H.hsym s x]; ring
  rw [sum_congr rfl fun x _ => this x, sum_add_distrib, ← mul_sum, B0, mul_zero, add_zero]

/-- `∑_x A_x(t) (ℓ(y) - ℓ(x)) = C⁽¹⁾ (e·κ)(e'·κ')` for `t` near the base. -/
theorem sumA_lift_x {b t y : Lam d L N} (ht : 2 * (supNorm (t - b) + r + 3) < L ^ N)
    (κ κ' : Fin d) (e e' : Dir d) :
    ∑ x, (C t (x + dirVec e) - C t x) * ((lift b (x + dirVec e') κ' : ℂ) - lift b x κ') *
      ((lift b y κ : ℂ) - lift b x κ) =
      (∑ x, C x 0) * (dirZ e κ : ℂ) * (dirZ e' κ' : ℂ) := by
  have E := H.sum_E2 (a := t) (b := b) (by omega) e e' κ κ'
  have A0 := H.sumA_x ht κ' e e'
  rw [← E]
  have : ∀ x, (C t (x + dirVec e) - C t x) * ((lift b (x + dirVec e') κ' : ℂ) - lift b x κ') *
      ((lift b y κ : ℂ) - lift b x κ) =
      (C t (x + dirVec e) - C t x) * ((lift b (x + dirVec e') κ' : ℂ) - lift b x κ') *
        ((lift b t κ : ℂ) - lift b x κ) +
      ((lift b y κ : ℂ) - lift b t κ) * ((C t (x + dirVec e) - C t x) *
        ((lift b (x + dirVec e') κ' : ℂ) - lift b x κ')) := fun x => by ring
  rw [sum_congr rfl fun x _ => this x, sum_add_distrib, ← mul_sum, A0, mul_zero, add_zero]

/-- **The `(Δψ)ψ̄` cross term, summed over the quartic monomial**: zero. -/
theorem sum_a2_x {b y : Lam d L N} (hy : 2 * (supNorm (y - b) + r + 4) < L ^ N)
    (κ κ' : Fin d) (e e' f : Dir d) :
    ∑ x, (Phi C b κ κ' e e' x (y + dirVec f) y - Phi C b κ κ' e e' x y y) = 0 := by
  have h1 := supNorm_shift y b f
  have l := lift_dirVec_eq (b := b) (x := y) (by omega) f κ
  have e1 : ∀ x, Phi C b κ κ' e e' x (y + dirVec f) y - Phi C b κ κ' e e' x y y =
      (dirZ f κ : ℂ) * ((C y (x + dirVec e) - C y x) *
        ((lift b (x + dirVec e') κ' : ℂ) - lift b x κ')) +
      ((C (x + dirVec e') (y + dirVec f) - C x (y + dirVec f)) *
          ((lift b (x + dirVec e) κ : ℂ) - lift b x κ) * ((lift b y κ' : ℂ) - lift b x κ') -
        (C (x + dirVec e') y - C x y) * ((lift b (x + dirVec e) κ : ℂ) - lift b x κ) *
          ((lift b y κ' : ℂ) - lift b x κ')) +
      (C x (y + dirVec f) - C x y) * (((lift b (x + dirVec e) κ : ℂ) - lift b x κ) *
        ((lift b (x + dirVec e') κ' : ℂ) - lift b x κ')) := by
    intro x; simp only [Phi, l]; ring
  simp only [e1, sum_add_distrib, ← mul_sum, sum_sub_distrib]
  rw [H.sumA_x (t := y) (by omega), H.sumB_lift_x (s := y + dirVec f) (by omega),
    H.sumB_lift_x (s := y) (by omega), H.sumDD_x (u := y + dirVec f) (v := y) (by omega)
      (by omega)]
  ring

/-- **The `ψ(Δψ̄)` cross term, summed over the gradient monomial**: zero (after the sum over
`±e_i`). -/
theorem sum_b2_y {b x : Lam d L N} (hx : 2 * (supNorm (x - b) + r + 4) < L ^ N)
    (κ κ' : Fin d) (e e' : Dir d) (i : Fin d) :
    ∑ f ∈ ({Sum.inl i, Sum.inr i} : Finset (Dir d)), ∑ y,
      (Phi C b κ κ' e e' x y (y + dirVec f) - Phi C b κ κ' e e' x y y) = 0 := by
  set A : Lam d L N → ℂ := fun t =>
    (C t (x + dirVec e) - C t x) * ((lift b (x + dirVec e') κ' : ℂ) - lift b x κ')
  set B : Lam d L N → ℂ := fun s =>
    (C (x + dirVec e') s - C x s) * ((lift b (x + dirVec e) κ : ℂ) - lift b x κ)
  have he : supNorm (dirVec e : Lam d L N) ≤ 1 := supNorm_dirVec_le e
  have he' : supNorm (dirVec e' : Lam d L N) ≤ 1 := supNorm_dirVec_le e'
  have h0 := supNorm_zero' (d := d) (L := L) (N := N)
  have e1 : ∀ f y, Phi C b κ κ' e e' x y (y + dirVec f) - Phi C b κ κ' e e' x y y =
      B y * ((lift b (y + dirVec f) κ' : ℂ) - lift b y κ') +
      (A (y + dirVec f) - A y) * ((lift b y κ : ℂ) - lift b x κ) +
      (C (y + dirVec f) x - C y x) * (((lift b (x + dirVec e) κ : ℂ) - lift b x κ) *
        ((lift b (x + dirVec e') κ' : ℂ) - lift b x κ')) := fun f y => by
    simp only [Phi, A, B]; ring
  have hnA : ∀ y, A y ≠ 0 → supNorm (y - b) ≤ r + supNorm (x - b) + 2 := by
    intro y hy
    by_contra hc
    apply hy
    simp only [A]
    have z1 : C y (x + dirVec e) = 0 := by
      by_contra h; exact hc (H.near_of_ne h0 he (by simpa using h))
    have z2 : C y x = 0 := by
      by_contra h; exact hc (H.near_of_ne h0 h0 (by simpa using h))
    rw [z1, z2]; ring
  have hnB : ∀ y, B y ≠ 0 → supNorm (y - b) ≤ r + supNorm (x - b) + 2 := by
    intro y hy
    by_contra hc
    apply hy
    simp only [B]
    have z1 : C (x + dirVec e') y = 0 := by
      by_contra h; exact hc (H.near_of_ne' h0 he' (by simpa using h))
    have z2 : C x y = 0 := by
      by_contra h; exact hc (H.near_of_ne' h0 h0 (by simpa using h))
    rw [z1, z2]; ring
  have p1 : ∑ f ∈ ({Sum.inl i, Sum.inr i} : Finset (Dir d)), ∑ y,
      B y * ((lift b (y + dirVec f) κ' : ℂ) - lift b y κ') = 0 := by
    rw [sum_comm]
    refine sum_eq_zero fun y _ => ?_
    rw [← mul_sum]
    by_cases hy : B y = 0
    · rw [hy, zero_mul]
    · have := hnB y hy
      rw [sum_pair (by simp), lift_dirVec_eq (by omega), lift_dirVec_eq (by omega)]
      simp [dirZ, Pi.single_apply]
  have p2 : ∀ f : Dir d, ∑ y, (A (y + dirVec f) - A y) * ((lift b y κ : ℂ) - lift b x κ) = 0 := by
    intro f
    have hs : ∑ y, A (y + dirVec f) * ((lift b y κ : ℂ) - lift b x κ) =
        ∑ y, A y * ((lift b (y - dirVec f) κ : ℂ) - lift b x κ) := by
      rw [← sum_shift_eq (fun y => A y * ((lift b (y - dirVec f) κ : ℂ) - lift b x κ))
        (dirVec f)]
      simp
    have hA0 : ∑ y, A y = 0 := by
      simp only [A, ← sum_mul, sum_sub_distrib, H.row_sum, sub_self, zero_mul]
    have hterm : ∀ y, A y * ((lift b (y - dirVec f) κ : ℂ) - lift b y κ) =
        A y * (-(dirZ f κ : ℂ)) := by
      intro y
      by_cases hy : A y = 0
      · simp [hy]
      · have := hnA y hy
        have t := supNorm_shift' y b f
        have l := lift_dirVec_eq (b := b) (x := y - dirVec f) (by omega) f κ
        rw [sub_add_cancel] at l
        rw [l]; ring
    rw [show ∑ y, (A (y + dirVec f) - A y) * ((lift b y κ : ℂ) - lift b x κ) =
        ∑ y, A y * ((lift b (y - dirVec f) κ : ℂ) - lift b y κ) by
      rw [show ∑ y, A y * ((lift b (y - dirVec f) κ : ℂ) - lift b y κ) =
          ∑ y, A y * ((lift b (y - dirVec f) κ : ℂ) - lift b x κ) -
          ∑ y, A y * ((lift b y κ : ℂ) - lift b x κ) by
        rw [← sum_sub_distrib]; exact sum_congr rfl fun y _ => by ring, ← hs, ← sum_sub_distrib]
      exact sum_congr rfl fun y _ => by ring]
    rw [sum_congr rfl fun y _ => hterm y, ← sum_mul, hA0, zero_mul]
  have p3 : ∀ f : Dir d, ∑ y, (C (y + dirVec f) x - C y x) *
      (((lift b (x + dirVec e) κ : ℂ) - lift b x κ) *
        ((lift b (x + dirVec e') κ' : ℂ) - lift b x κ')) = 0 := by
    intro f
    rw [← sum_mul, sum_sub_distrib, sum_shift_eq (fun y => C y x), sub_self, zero_mul]
  simp only [e1, sum_add_distrib, p2, p3, add_zero, sum_const_zero]
  exact p1

/-- **The `ψ(Δψ̄)` cross term, summed over the quartic monomial**: zero. -/
theorem sum_b2_x {b y : Lam d L N} (hy : 2 * (supNorm (y - b) + r + 4) < L ^ N)
    (κ κ' : Fin d) (e e' f : Dir d) :
    ∑ x, (Phi C b κ κ' e e' x y (y + dirVec f) - Phi C b κ κ' e e' x y y) = 0 := by
  have h1 := supNorm_shift y b f
  have l := lift_dirVec_eq (b := b) (x := y) (by omega) f κ'
  have e1 : ∀ x, Phi C b κ κ' e e' x y (y + dirVec f) - Phi C b κ κ' e e' x y y =
      (dirZ f κ' : ℂ) * ((C (x + dirVec e') y - C x y) *
        ((lift b (x + dirVec e) κ : ℂ) - lift b x κ)) +
      ((C (y + dirVec f) (x + dirVec e) - C (y + dirVec f) x) *
          ((lift b (x + dirVec e') κ' : ℂ) - lift b x κ') * ((lift b y κ : ℂ) - lift b x κ) -
        (C y (x + dirVec e) - C y x) * ((lift b (x + dirVec e') κ' : ℂ) - lift b x κ') *
          ((lift b y κ : ℂ) - lift b x κ)) +
      (C x (y + dirVec f) - C x y) * (((lift b (x + dirVec e) κ : ℂ) - lift b x κ) *
        ((lift b (x + dirVec e') κ' : ℂ) - lift b x κ')) := by
    intro x; simp only [Phi, l, H.hsym (y + dirVec f) x, H.hsym y x]; ring
  simp only [e1, sum_add_distrib, ← mul_sum, sum_sub_distrib]
  rw [H.sumB_x (s := y) (by omega), H.sumA_lift_x (t := y + dirVec f) (by omega),
    H.sumA_lift_x (t := y) (by omega), H.sumDD_x (u := y + dirVec f) (v := y) (by omega)
      (by omega)]
  ring

end CovH

end

end Step2
