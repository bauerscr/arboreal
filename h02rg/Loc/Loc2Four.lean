import Loc.Loc4Est
import Loc.PauliOps

/-!
# The contraction bound on sequences of length `4` (`d = 2`, Lemma `lem:loc2`)

Let `G ∈ 𝒩(X^□)` be `U(1)`-invariant with vanishing quartic pairings `mu4 G = 0` (e.g.
`G = F - Loc2_X F`). Then `G` annihilates every polynomial of degree `≤ 2` in the lifted
coordinates of four points (`sum_coeff_poly2`):

* the constant and the linear terms, and the quadratic terms in two points of equal spin, by
  antisymmetry of the coefficients under exchanging the two points of equal spin;
* the mixed quadratic terms `ℓ(x_a)_i ℓ(x_b)_k` (`a` of spin `+`, `b` of spin `-`) are `± mu4`.

So the pairing of `G` with a test function only sees the Taylor remainder of order `3`, which
gains `L^{-3}` (`exists_four_bound`), as for sequences of length `2` (`exists_two_bound`).
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD Equiv

variable {d L N : ℕ} [NeZero L]

/-! ### Polynomials of degree `≤ 2` in four points -/

/-- Polynomials of degree `≤ 2` in the coordinates of four points of `ℤ^d`. -/
def Poly2 (f : (Fin 4 → Zd d) → ℂ) : Prop :=
  ∃ (a : ℂ) (c : Fin 4 → Fin d → ℂ) (B : Fin 4 → Fin d → Fin 4 → Fin d → ℂ),
    ∀ w, f w = a + linF c w + quadF B w

theorem linF_perm (c : Fin 4 → Fin d → ℂ) (π : Perm (Fin 4)) (w : Fin 4 → Zd d) :
    linF c (w ∘ π) = linF (fun k i => c (π.symm k) i) w := by
  unfold linF
  conv_rhs => rw [← Equiv.sum_comp π]
  simp

theorem quadF_perm (B : Fin 4 → Fin d → Fin 4 → Fin d → ℂ) (π : Perm (Fin 4))
    (w : Fin 4 → Zd d) :
    quadF B (w ∘ π) = quadF (fun k i k' i' => B (π.symm k) i (π.symm k') i') w := by
  unfold quadF
  conv_rhs => rw [← Equiv.sum_comp π]
  refine sum_congr rfl fun k _ => sum_congr rfl fun i _ => ?_
  conv_rhs => rw [← Equiv.sum_comp π]
  simp

theorem Poly2.perm {f : (Fin 4 → Zd d) → ℂ} (hf : Poly2 f) (π : Perm (Fin 4)) :
    Poly2 fun w => f (w ∘ π) := by
  obtain ⟨a, c, B, h⟩ := hf
  exact ⟨a, fun k i => c (π.symm k) i, fun k i k' i' => B (π.symm k) i (π.symm k') i',
    fun w => by show f (w ∘ π) = _; rw [h (w ∘ π), linF_perm, quadF_perm]⟩

theorem poly2_taylor2 (Φ : (Fin 4 → Zd d) → ℂ) : Poly2 (taylor2 Φ) := by
  refine ⟨Φ 0, fun k i => Dp k i Φ 0 - (1 / 2) * Dp k i (Dp k i Φ) 0,
    fun k i k' i' => (1 / 2) * Dp k' i' (Dp k i Φ) 0, fun w => ?_⟩
  rw [taylor2_eq]
  simp only [linF, quadF, sub_mul, sum_sub_distrib, mul_sum, mul_assoc]
  ring

/-! ### The functional `f ↦ ∑_x c(x) f(ℓ x)` -/

/-- Lifted coordinates of four points. -/
def w4 (b : Lam d L N) (x : Fin 4 → Lam d L N) : Fin 4 → Zd d := fun r => rep (x r - b)

/-- `f ↦ ∑_x c(x) f(ℓ x)`. -/
def om4 (b : Lam d L N) (c : (Fin 4 → Lam d L N) → ℂ) :
    ((Fin 4 → Zd d) → ℂ) →ₗ[ℂ] ℂ where
  toFun f := ∑ x, c x * f (w4 b x)
  map_add' f g := by simp only [Pi.add_apply, mul_add, sum_add_distrib]
  map_smul' r f := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_sum, RingHom.id_apply]
    exact sum_congr rfl fun _ _ => by ring

theorem om4_apply (b : Lam d L N) (c : (Fin 4 → Lam d L N) → ℂ) (f : (Fin 4 → Zd d) → ℂ) :
    om4 b c f = ∑ x, c x * f (w4 b x) := rfl

theorem om4_perm (b : Lam d L N) (c : (Fin 4 → Lam d L N) → ℂ) (τ : Perm (Fin 4))
    (f : (Fin 4 → Zd d) → ℂ) : om4 b c f = ∑ x, c (x ∘ τ) * f (w4 b x ∘ τ) := by
  rw [om4_apply]
  exact (Equiv.sum_comp (Equiv.arrowCongr τ.symm (Equiv.refl _))
    (fun x => c x * f (w4 b x))).symm

@[simp] theorem swap02_1 : swap (0 : Fin 4) 2 1 = 1 := by decide
@[simp] theorem swap02_3 : swap (0 : Fin 4) 2 3 = 3 := by decide
@[simp] theorem swap13_0 : swap (1 : Fin 4) 3 0 = 0 := by decide
@[simp] theorem swap13_2 : swap (1 : Fin 4) 3 2 = 2 := by decide

section Antisymm

variable {b : Lam d L N} {c : (Fin 4 → Lam d L N) → ℂ}

theorem om4_eq_neg {τ : Perm (Fin 4)} (hc : ∀ x, c (x ∘ τ) = -c x) {f g : (Fin 4 → Zd d) → ℂ}
    (hfg : ∀ w, f (w ∘ τ) = g w) : om4 b c f = -om4 b c g := by
  rw [om4_perm b c τ, om4_apply, ← sum_neg_distrib]
  refine sum_congr rfl fun x _ => ?_
  rw [hc, hfg]; ring

theorem om4_eq_zero {τ : Perm (Fin 4)} (hc : ∀ x, c (x ∘ τ) = -c x) {f : (Fin 4 → Zd d) → ℂ}
    (hf : ∀ w, f (w ∘ τ) = f w) : om4 b c f = 0 := by
  have := om4_eq_neg (b := b) hc hf
  linear_combination this / 2

/-- The coordinate function `w ↦ w_r i`. -/
def crd (r : Fin 4) (i : Fin d) (w : Fin 4 → Zd d) : ℂ := (w r i : ℂ)

variable (h02 : ∀ x, c (x ∘ swap 0 2) = -c x) (h13 : ∀ x, c (x ∘ swap 1 3) = -c x)
  (hmu : ∀ i k : Fin d, om4 b c (fun w => crd 0 i w * crd 1 k w) = 0)
include h02 h13

omit h13 in
theorem om4_one : om4 b c (fun _ => 1) = 0 := om4_eq_zero h02 fun _ => rfl

theorem om4_crd (r : Fin 4) (i : Fin d) : om4 b c (crd r i) = 0 := by
  fin_cases r
  · exact om4_eq_zero h13 fun w => by simp [crd]
  · exact om4_eq_zero h02 fun w => by simp [crd]
  · exact om4_eq_zero h13 fun w => by simp [crd]
  · exact om4_eq_zero h02 fun w => by simp [crd]

include hmu

theorem om4_crd2 (r : Fin 4) (i : Fin d) (r' : Fin 4) (i' : Fin d) :
    om4 b c (fun w => crd r i w * crd r' i' w) = 0 := by
  have hm : ∀ i k, om4 b c (fun w => crd 1 k w * crd 0 i w) = 0 := fun i k => by
    rw [← hmu i k]; congr 1; funext w; ring
  fin_cases r <;> fin_cases r'
  · exact om4_eq_zero h13 fun w => by simp [crd]
  · exact hmu i i'
  · exact om4_eq_zero h13 fun w => by simp [crd]
  · rw [om4_eq_neg h13 (g := fun w => crd 0 i w * crd 1 i' w) fun w => by simp [crd], hmu,
      neg_zero]
  · exact hm i' i
  · exact om4_eq_zero h02 fun w => by simp [crd]
  · rw [om4_eq_neg h02 (g := fun w => crd 1 i w * crd 0 i' w) fun w => by simp [crd], hm,
      neg_zero]
  · exact om4_eq_zero h02 fun w => by simp [crd]
  · exact om4_eq_zero h13 fun w => by simp [crd]
  · rw [om4_eq_neg h02 (g := fun w => crd 0 i w * crd 1 i' w) fun w => by simp [crd], hmu,
      neg_zero]
  · exact om4_eq_zero h13 fun w => by simp [crd]
  · rw [om4_eq_neg h02 (g := fun w => crd 0 i w * crd 3 i' w) fun w => by simp [crd],
      om4_eq_neg h13 (g := fun w => crd 0 i w * crd 1 i' w) fun w => by simp [crd], hmu,
      neg_zero, neg_zero]
  · rw [om4_eq_neg h13 (g := fun w => crd 1 i w * crd 0 i' w) fun w => by simp [crd], hm,
      neg_zero]
  · exact om4_eq_zero h02 fun w => by simp [crd]
  · rw [om4_eq_neg h02 (g := fun w => crd 3 i w * crd 0 i' w) fun w => by simp [crd],
      om4_eq_neg h13 (g := fun w => crd 1 i w * crd 0 i' w) fun w => by simp [crd], hm,
      neg_zero, neg_zero]
  · exact om4_eq_zero h02 fun w => by simp [crd]

theorem om4_poly2 {f : (Fin 4 → Zd d) → ℂ} (hf : Poly2 f) : om4 b c f = 0 := by
  obtain ⟨a, c', B, h⟩ := hf
  have e : f = a • (fun _ => (1 : ℂ)) + ∑ k, ∑ i, c' k i • crd k i +
      ∑ k, ∑ i, ∑ k', ∑ i', B k i k' i' • (fun w => crd k i w * crd k' i' w) := by
    funext w
    simp only [h, linF, quadF, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
      crd, mul_one]
    congr 1
    refine sum_congr rfl fun k _ => sum_congr rfl fun i _ => sum_congr rfl fun k' _ =>
      sum_congr rfl fun i' _ => by ring
  rw [e, map_add, map_add, map_smul, om4_one h02, smul_zero, zero_add, map_sum, map_sum]
  simp only [map_sum, map_smul, om4_crd h02 h13, om4_crd2 h02 h13 hmu, smul_zero,
    sum_const_zero, add_zero]

end Antisymm

/-! ### Application to the coefficients of `G` -/

theorem pat4_comp_swap02 : pat4 ∘ (swap (0 : Fin 4) 2) = pat4 := by
  funext r; fin_cases r <;> rfl

theorem pat4_comp_swap13 : pat4 ∘ (swap (1 : Fin 4) 3) = pat4 := by
  funext r; fin_cases r <;> rfl

theorem cf4_comp_swap (G : Alg d L N) {τ : Perm (Fin 4)} (hτ : pat4 ∘ τ = pat4)
    (hs : Perm.sign τ = -1) (x : Fin 4 → Lam d L N) : cf4 G (x ∘ τ) = -cf4 G x := by
  have e : (fun r => ((x ∘ τ) r, pat4 r)) = (fun r => (x r, pat4 r)) ∘ τ := by
    funext r; simp only [Function.comp_apply]
    exact congrArg _ (congrFun hτ r).symm
  rw [cf4, e, coeff_perm, hs]
  simp [cf4]

theorem om4_cf4_crd01 (b : Lam d L N) (G : Alg d L N) (i k : Fin d) :
    om4 b (cf4 G) (fun w => crd 0 i w * crd 1 k w) = mu4 b i k G := by
  rw [om4_apply, mu4]
  refine sum_congr rfl fun x _ => ?_
  simp [crd, w4, lift]

/-- `G` with `mu4 G = 0` annihilates polynomials of degree `≤ 2` on the pattern `(+,-,+,-)`. -/
theorem om4_cf4_poly2 {b : Lam d L N} {G : Alg d L N} (hμ : ∀ i k : Fin d, mu4 b i k G = 0)
    {f : (Fin 4 → Zd d) → ℂ} (hf : Poly2 f) : om4 b (cf4 G) f = 0 :=
  om4_poly2 (cf4_comp_swap G pat4_comp_swap02 (Perm.sign_swap (by decide)))
    (cf4_comp_swap G pat4_comp_swap13 (Perm.sign_swap (by decide)))
    (fun i k => (om4_cf4_crd01 b G i k).trans (hμ i k)) hf

/-- Every `U(1)`-invariant spin pattern of length four is a permutation of `(+,-,+,-)`. -/
theorem exists_perm_pat4 (s : Fin 4 → ℤˣ) (hs : U1 s) : ∃ σ : Perm (Fin 4), s ∘ σ = pat4 := by
  have e : s = ![s 0, s 1, s 2, s 3] := by funext r; fin_cases r <;> rfl
  rw [e] at hs ⊢
  rcases Int.units_eq_one_or (s 0) with h0 | h0 <;>
  rcases Int.units_eq_one_or (s 1) with h1 | h1 <;>
  rcases Int.units_eq_one_or (s 2) with h2 | h2 <;>
  rcases Int.units_eq_one_or (s 3) with h3 | h3 <;>
  rw [h0, h1, h2, h3] at hs ⊢ <;>
  first
  | (exfalso; revert hs; decide)
  | exact ⟨1, by decide⟩
  | exact ⟨swap 1 2, by decide⟩
  | exact ⟨swap 2 3, by decide⟩
  | exact ⟨swap 0 1, by decide⟩
  | exact ⟨swap 0 1 * swap 2 3, by decide⟩
  | exact ⟨swap 0 3, by decide⟩

/-- For every `U(1)`-invariant spin pattern `s`, the coefficients of `G` on `s` annihilate the
polynomials of degree `≤ 2`. -/
theorem sum_coeff_poly2 {b : Lam d L N} {G : Alg d L N} (hμ : ∀ i k : Fin d, mu4 b i k G = 0)
    {s : Fin 4 → ℤˣ} (hs : U1 s) {f : (Fin 4 → Zd d) → ℂ} (hf : Poly2 f) :
    ∑ x : Fin 4 → Lam d L N, coeff G (fun r => (x r, s r)) * f (w4 b x) = 0 := by
  obtain ⟨σ, hσ⟩ := exists_perm_pat4 s hs
  have hc : ∀ y : Fin 4 → Lam d L N,
      coeff G (fun r => ((y ∘ σ.symm) r, s r)) = (Perm.sign σ : ℂ) * cf4 G y := by
    intro y
    have e : (fun r => (y r, pat4 r)) = (fun r => ((y ∘ σ.symm) r, s r)) ∘ σ := by
      funext r
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
      exact congrArg _ (congrFun hσ r).symm
    have h := coeff_perm G (fun r => ((y ∘ σ.symm) r, s r)) σ
    rw [← e] at h
    rw [cf4, h, ← mul_assoc]
    rcases Int.units_eq_one_or (Perm.sign σ) with h1 | h1 <;> simp [h1]
  have := om4_perm b (fun x => coeff G (fun r => (x r, s r))) σ.symm f
  rw [om4_apply] at this
  rw [this]
  simp only [hc]
  have h2 := om4_cf4_poly2 hμ (hf.perm σ.symm)
  rw [om4_apply] at h2
  simp only [mul_assoc, ← mul_sum]
  have e2 : ∀ x : Fin 4 → Lam d L N, w4 b x ∘ σ.symm = w4 b (x ∘ σ.symm) := fun _ => rfl
  rw [show (∑ x : Fin 4 → Lam d L N, cf4 G x * f (w4 b x ∘ ⇑σ.symm)) = 0 from h2, mul_zero]

/-! ### The bound on sequences of length four -/

/-- Sums over sequences, split according to the spin pattern. -/
theorem sum_split_spins {X : Type*} [Fintype X] {n : ℕ} (f : (Fin n → Sf X) → ℂ) :
    ∑ z, f z = ∑ t : Fin n → ℤˣ, ∑ x : Fin n → X, f fun r => (x r, t r) := by
  let e : (Fin n → X) × (Fin n → ℤˣ) ≃ (Fin n → Sf X) :=
    { toFun := fun q r => (q.1 r, q.2 r)
      invFun := fun z => (fun r => (z r).1, fun r => (z r).2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← e.sum_comp, Fintype.sum_prod_type, sum_comm]
  rfl

/-- `g` at the points `ι_b(v_r)` with the spins `t`, as a function on `(ℤ^d)^4`. -/
def phiS (b : Lam d L N) (g : (Fin 4 → Sf (Lam d L N)) → ℂ) (t : Fin 4 → ℤˣ) :
    (Fin 4 → Zd d) → ℂ := fun v => g fun r => (ιZ b (v r), t r)

/-- The Taylor remainder of `phiS`, on the spin pattern of the argument. -/
def remS (b : Lam d L N) (g : (Fin 4 → Sf (Lam d L N)) → ℂ) : (Fin 4 → Sf (Zd d)) → ℂ :=
  fun w => phiS b g (spins w) (fun r => (w r).1) -
    taylor2 (phiS b g (spins w)) (fun r => (w r).1)

theorem exists_four_bound (d : ℕ) (hd : 2 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (L : ℕ) [NeZero L], 2 ^ (d + 3) + 8 * d < L → ∀ N j : ℕ, j < N →
    ∀ X : Finset (Lam d L N), IsSmall j X → ∀ G ∈ NX (nbhd j X : Set (Lam d L N)),
    (∀ z : Fin 4 → Sf (Lam d L N), ¬U1 (spins z) → coeff G z = 0) →
    (∀ i k : Fin d, mu4 (base X) i k G = 0) →
    ∀ ℓ ℓ' : ℝ, 0 < ℓ → 0 < ℓ' → ∀ g : (Fin 4 → Sf (Lam d L N)) → ℂ,
    (∀ (z : Fin 4 → Sf (Lam d L N)) (γ : Fin 4 → Dir d → ℕ), (∀ k, mabs (γ k) ≤ pPhi d) →
      ‖nab γ g z‖ ≤ ℓ' ^ 4 * (((L : ℝ) ^ (j + 1)) ^ ord γ)⁻¹) →
    ‖pair G (single 4 g)‖ ≤
      (Tj d (L : ℝ) j ℓ G).toReal * (C * ℓ' ^ 4 * ℓ⁻¹ ^ 4 / (L : ℝ) ^ 3) := by
  obtain ⟨Cl, hCl0, hCl⟩ := exists_localized_bound d
  set C4 : ℝ := 4 * d * (2 ^ (d + 2) + 4 * d + 2)
  refine ⟨Cl ^ 4 * (C4 + 1) ^ 3, by positivity, ?_⟩
  intro L _ hL N j hj X hX G hG hGs hGμ ℓ ℓ' hℓ hℓ' g hgb
  set b := base X
  set R : ℝ := (rad d L j : ℝ)
  set s : ℝ := (L : ℝ) ^ j
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hs1 : 1 ≤ s := one_le_pow₀ hL1
  have hs0 : 0 < s := by linarith
  have hh' : (L : ℝ) ^ (j + 1) = L * s := by rw [pow_succ, mul_comm]
  set U := remS b g
  -- the pairing
  have hpair : pair G (single 4 g) = pair G (single 4 (fun z => locH U1 U R (ρS b ∘ z))) := by
    rw [pair_single, pair_single]
    congr 1
    have hsplit : ∀ z : Fin 4 → Sf (Lam d L N), coeff G z * g z =
        coeff G z * locH U1 U R (ρS b ∘ z) +
          (if U1 (spins z) then coeff G z *
            taylor2 (phiS b g (spins z)) (w4 b (fun r => (z r).1)) else 0) := by
      intro z
      by_cases hU : U1 (spins z)
      · rw [if_pos hU]
        by_cases hz : ∀ r, (z r).1 ∈ nbhd j X
        · have e0 : phiS b g (spins z) (fun r => ((ρS b ∘ z) r).1) = g z := by
            simp only [phiS]
            congr 1
            funext r
            exact ιS_ρS b (z r)
          have e1 : locH U1 U R (ρS b ∘ z) =
              g z - taylor2 (phiS b g (spins z)) (w4 b (fun r => (z r).1)) := by
            simp only [locH]
            rw [if_pos (show U1 (spins (ρS b ∘ z)) from hU), cutS_ρS_eq_one hX z hz,
              Complex.ofReal_one, one_mul]
            simp only [U, remS]
            rw [show spins (ρS b ∘ z) = spins z from rfl, e0]
            rfl
          rw [e1]; ring
        · push Not at hz
          obtain ⟨r, hr⟩ := hz
          rw [coeff_eq_zero_of_mem_NX hG z r hr]; ring
      · rw [if_neg hU, hGs z hU]; ring
    simp only [hsplit, sum_add_distrib]
    have hT : ∑ z : Fin 4 → Sf (Lam d L N), (if U1 (spins z) then coeff G z *
        taylor2 (phiS b g (spins z)) (w4 b (fun r => (z r).1)) else 0) = 0 := by
      rw [sum_split_spins]
      refine sum_eq_zero fun t _ => ?_
      by_cases ht : U1 t
      · have e : ∀ x : Fin 4 → Lam d L N,
            (if U1 (spins (fun r => (x r, t r))) then coeff G (fun r => (x r, t r)) *
              taylor2 (phiS b g (spins (fun r => (x r, t r))))
                (w4 b (fun r => ((fun r => (x r, t r)) r).1)) else 0) =
            coeff G (fun r => (x r, t r)) * taylor2 (phiS b g t) (w4 b x) := fun x => if_pos ht
        rw [sum_congr rfl fun x _ => e x]
        exact sum_coeff_poly2 hGμ ht (poly2_taylor2 _)
      · exact sum_eq_zero fun x _ => if_neg ht
    rw [hT, add_zero]
  -- the bound on the remainder
  have hΦb : ∀ (t : Fin 4 → ℤˣ) (v : Fin 4 → Zd d) (γ : Fin 4 → Dir d → ℕ),
      (∀ k, mabs (γ k) ≤ pPhi d) →
      ‖nabla (fun b u => b +ᵥ u) γ (phiS b g t) v‖ ≤ ℓ' ^ 4 * (((L : ℝ) ^ (j + 1))⁻¹) ^ ord γ := by
    intro t v γ hγ
    have e := nabla_comp_pi (fun b u => b +ᵥ u) sh (fun k u => (ιZ b u, t k))
      (fun k β u => by simp [sh, ιZ_vadd]) γ g v
    show ‖nabla (fun b u => b +ᵥ u) γ (fun v => g fun r => (ιZ b (v r), t r)) v‖ ≤ _
    rw [e, inv_pow]
    exact hgb _ γ hγ
  have hUbound : ∀ w : Fin 4 → Sf (Zd d), U1 (spins w) →
      (∀ k, supNormZ (w k).1 ≤ 2 * rad d L j + 2 * pPhi d) →
      ∀ δ : Fin 4 → Dir d → ℕ, (∀ k, mabs (δ k) ≤ pPhi d) →
        ‖nab δ U w‖ * s ^ ord δ ≤ ℓ' ^ 4 * ((C4 + 1) ^ 3 / (L : ℝ) ^ 3) := by
    intro w _ hr δ hδ
    have eU : nab δ U w = nabla (fun (b : Dir d → ℕ) (u : Zd d) => b +ᵥ u) δ
        (fun v => phiS b g (spins w) v - taylor2 (phiS b g (spins w)) v)
          (fun k => (w k).1) := by
      rw [nabla_congr_range δ w (g := fun w' => phiS b g (spins w) (fun r => (w' r).1) -
        taylor2 (phiS b g (spins w)) (fun r => (w' r).1)) (fun _ _ => rfl)]
      exact nab_pos δ (fun v => phiS b g (spins w) v - taylor2 (phiS b g (spins w)) v) w
    have ht := taylor2_bound (K := ℓ' ^ 4) (ε := ((L : ℝ) ^ (j + 1))⁻¹) (P := pPhi d)
      (by positivity) (by positivity) (by simp [pPhi]; omega) (hΦb (spins w))
      (w := fun k => (w k).1) (r := 2 * rad d L j + 2 * pPhi d) hr δ hδ
    rw [hh'] at ht
    have hr' : ((4 * d * (2 * rad d L j + 2 * pPhi d + 2) : ℕ) : ℝ) ≤ C4 * s := by
      have := radius_le (d := d) (L := L) j
      push_cast at this ⊢
      simp only [C4, s]
      nlinarith
    have hsc := taylor_scale hL1 hs1 (Nat.cast_nonneg _) hr' (ord δ)
    rw [eU]
    calc ‖nabla (fun (b : Dir d → ℕ) (u : Zd d) => b +ᵥ u) δ
          (fun v => phiS b g (spins w) v - taylor2 (phiS b g (spins w)) v)
            (fun k => (w k).1)‖ * s ^ ord δ
        ≤ (ℓ' ^ 4 * ((4 * d * (2 * rad d L j + 2 * pPhi d + 2) : ℕ) : ℝ) ^
            (3 - min (ord δ) 3) * ((L * s)⁻¹) ^ max (ord δ) 3) * s ^ ord δ := by
          gcongr
      _ = ℓ' ^ 4 * (((4 * d * (2 * rad d L j + 2 * pPhi d + 2) : ℕ) : ℝ) ^
            (3 - min (ord δ) 3) * ((L * s)⁻¹) ^ max (ord δ) 3 * s ^ ord δ) := by ring
      _ ≤ ℓ' ^ 4 * ((C4 + 1) ^ 3 / (L : ℝ) ^ 3) := by gcongr
  have hnorm := hCl 4 L hL N j hj b U1 U _ (by positivity) hUbound ℓ hℓ
  rw [hpair]
  refine (abs_pair_le (by positivity) hℓ G (by positivity) hnorm).trans (le_of_eq ?_)
  simp only [Tj]
  field_simp

end

end Loc
