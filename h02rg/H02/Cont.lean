import H02.Ghost

/-!
# Regularity of the `ℍ^{0|2}` model in `(β, h)`

* `W_pow_eq_zero`: `(-H_{β,h})^K = 0` with `K = |E(K_Λ)| + |Λ| + 1` independent of `(β, h)`;
  hence `[F]_{β,h} = ∑_{k < K} (k!)⁻¹ [F (-H_{β,h})^k]_0` (`expect_eq_sum`) is a polynomial in the
  weights `(β_{ij}, h_i)`.
* `continuous_expect`: for continuous families `p ↦ (β(p), h(p))` of symmetric weights and
  fields, `p ↦ [F]_{β(p),h(p)}` is continuous.
* `expect_one_pos` (in `H02/Ghost.lean`): `Z_{β,h} = [1]_{β,h} > 0` for `β ≥ 0`, `h ≥ 0`.
* `continuousOn_avg`, `continuous_avg`: continuity of `⟨F⟩_{β,h}` where `Z_{β,h} > 0`.
-/

namespace H02

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

local notation "A" => Grassmann Λ

theorem sum_pow_card_succ {R : Type*} [CommRing R] {ι : Type*} (s : Finset ι) (f : ι → R)
    (hf : ∀ i ∈ s, f i * f i = 0) : (∑ i ∈ s, f i) ^ (s.card + 1) = 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
    refine (Commute.all _ _).add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero (m := 2)
      (n := s.card + 1) ?_ (ih fun i hi => hf i (mem_insert_of_mem hi)) (by omega)
    rw [pow_two]; exact hf a (mem_insert_self a s)

/-- The nilpotency degree of `-H_{β,h}`, independent of `β, h`. -/
def nilDeg (Λ : Type*) [DecidableEq Λ] [Fintype Λ] : ℕ :=
  (E (⊤ : SimpleGraph Λ)).card + Fintype.card Λ + 1

theorem W_pow_eq_zero (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) (h : Λ → ℝ) :
    W β hβ h ^ nilDeg Λ = 0 := by
  have h1 := sum_pow_card_succ (E (⊤ : SimpleGraph Λ)) (fun e => Sym2.lift ⟨β, hβ⟩ e • Xs e)
    (fun e _ => smul_mul_smul_self (Xs_sq e))
  have h2 := sum_pow_card_succ (univ : Finset Λ) (fun i => h i • pc i i)
    (fun i _ => smul_mul_smul_self (pc_sq i))
  rw [W, nilDeg]
  refine (Commute.all _ _).add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero h1 h2 ?_
  simp only [card_univ]; omega

/-- `[F]_0` as a linear map. -/
def int0L : A →ₗ[ℝ] ℝ :=
  ExteriorAlgebra.algebraMapInv.toLinearMap ∘ₗ berezin (univ : Finset Λ).toList

theorem int0_eq_L (F : A) : int0 F = int0L F := rfl

theorem cv_W (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) (h : Λ → ℝ) :
    cv (W β hβ h) = ∑ e ∈ E (⊤ : SimpleGraph Λ), Sym2.lift ⟨β, hβ⟩ e • cv (Xs e) +
      ∑ i, h i • (ξ i * η i) := by
  simp [W, map_sum, map_smul]

/-- `[F]_{β,h} = ∑_{k < K} (k!)⁻¹ [F (-H_{β,h})^k]_0`. -/
theorem expect_eq_sum (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) (h : Λ → ℝ) (F : A) :
    expect β h F = ∑ k ∈ range (nilDeg Λ),
      algebraMap ℚ ℝ (k.factorial : ℚ)⁻¹ * int0 (F * cv (W β hβ h) ^ k) := by
  rw [expect, action_eq β hβ h, neg_neg, ← IsNilpotent.map_exp (isNilpotent_W β hβ h),
    IsNilpotent.exp_eq_sum (W_pow_eq_zero β hβ h), map_sum, Finset.mul_sum, int0_sum]
  refine sum_congr rfl fun k _ => ?_
  have : cv ((k.factorial : ℚ)⁻¹ • W β hβ h ^ k) =
      algebraMap ℚ ℝ (k.factorial : ℚ)⁻¹ • cv (W β hβ h) ^ k := by
    rw [← map_pow]; exact map_smul cv (algebraMap ℚ ℝ (k.factorial : ℚ)⁻¹) _
  rw [this, mul_smul_comm, int0_smul]

/-- Continuity of `p ↦ ℓ(G (∑_i c_i(p) X_i + ∑_j c'_j(p) X'_j)^k)` for continuous `c, c'`. -/
theorem continuous_mul_pow {P : Type*} [TopologicalSpace P] {ι κ : Type*} (s : Finset ι)
    (t : Finset κ) (c : ι → P → ℝ) (c' : κ → P → ℝ) (hc : ∀ i, Continuous (c i))
    (hc' : ∀ j, Continuous (c' j)) (X : ι → A) (X' : κ → A) (k : ℕ) :
    ∀ (ℓ : A →ₗ[ℝ] ℝ) (G : A),
      Continuous fun p => ℓ (G * (∑ i ∈ s, c i p • X i + ∑ j ∈ t, c' j p • X' j) ^ k) := by
  induction k with
  | zero => intro ℓ G; simp only [pow_zero, mul_one]; exact continuous_const
  | succ k ih =>
    intro ℓ G
    have e : ∀ p, ℓ (G * (∑ i ∈ s, c i p • X i + ∑ j ∈ t, c' j p • X' j) ^ (k + 1)) =
        ∑ i ∈ s, c i p * (ℓ ∘ₗ LinearMap.mulRight ℝ (X i))
            (G * (∑ i ∈ s, c i p • X i + ∑ j ∈ t, c' j p • X' j) ^ k) +
        ∑ j ∈ t, c' j p * (ℓ ∘ₗ LinearMap.mulRight ℝ (X' j))
            (G * (∑ i ∈ s, c i p • X i + ∑ j ∈ t, c' j p • X' j) ^ k) := by
      intro p
      rw [pow_succ, ← mul_assoc, mul_add, Finset.mul_sum, Finset.mul_sum, map_add, map_sum,
        map_sum]
      simp only [mul_smul_comm, map_smul, smul_eq_mul, LinearMap.comp_apply,
        LinearMap.mulRight_apply]
    simp_rw [e]
    exact (continuous_finsetSum _ fun i _ => (hc i).mul (ih _ G)).add
      (continuous_finsetSum _ fun j _ => (hc' j).mul (ih _ G))

set_option maxHeartbeats 1000000 in
/-- **Continuity in `(β, h)`**: for continuous families of symmetric weights `β(p)` and fields
`h(p)`, `p ↦ [F]_{β(p),h(p)}` is continuous (it is a polynomial in `(β_{ij}, h_i)`). -/
theorem continuous_expect {P : Type*} [TopologicalSpace P] (β : P → Λ → Λ → ℝ)
    (hβ : ∀ p i j, β p i j = β p j i) (h : P → Λ → ℝ) (hβc : Continuous β) (hhc : Continuous h)
    (F : A) : Continuous fun p => expect (β p) (h p) F := by
  have e : ∀ p, expect (β p) (h p) F = ∑ k ∈ range (nilDeg Λ),
      algebraMap ℚ ℝ (k.factorial : ℚ)⁻¹ * int0L (F *
        (∑ e ∈ E (⊤ : SimpleGraph Λ), Sym2.lift ⟨β p, hβ p⟩ e • cv (Xs e) +
          ∑ i, h p i • (ξ i * η i)) ^ k) := by
    intro p; rw [expect_eq_sum (β p) (hβ p) (h p), cv_W]; simp only [int0_eq_L]
  simp_rw [e]
  refine continuous_finsetSum _ fun k _ => continuous_const.mul ?_
  refine continuous_mul_pow (E (⊤ : SimpleGraph Λ)) univ
    (fun e p => Sym2.lift ⟨β p, hβ p⟩ e) (fun i p => h p i) (fun e => ?_) (fun i => ?_) _ _ k _ F
  · induction e using Sym2.ind with
    | h a b => exact (continuous_apply b).comp ((continuous_apply a).comp hβc)
  · exact (continuous_apply i).comp hhc

end

end H02
