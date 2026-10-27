import H02.Spin

/-!
# The Ward identity `e:ward`

The Ward identity of `h02rg.tex` for the `ℍ^{0|2}` model with constant external field `h`:
`⟨z_0⟩_{β,h} = ⟨T ξ_0⟩_{β,h} = -∑_x h ⟨ξ_0 T z_x⟩_{β,h} = h ∑_x ⟨ξ_0 η_x⟩_{β,h}`,
where `T = ∑_x z_x ∂_{ξ_x}` is the symmetry generator `e:Tdef`.

The proof: `[T F]_0 = 0` for every form `F`, and `T` is an odd derivation with
`T e^{-H_{β,h}} = e^{-H_{β,h}} T(-H_{β,h})` and `T(-H_{β,h}) = ∑_x h_x η_x`.
-/

namespace H02

noncomputable section

set_option linter.unusedSectionVars false

open Finset

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

local notation "A" => Grassmann Λ

theorem T_pow {y : A} (hy : inv' y = y) (n : ℕ) :
    T univ (y ^ (n + 1)) = ((n + 1 : ℕ) : ℝ) • (y ^ n * T univ y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', T_mul, ih, hy, mul_smul_comm, ← mul_assoc, ← pow_succ',
      mul_comm_of_even (show inv' (y ^ (n + 1)) = y ^ (n + 1) by rw [map_pow, hy])]
    push_cast
    module

/-- `T` acts on the exponential of an even nilpotent form as a derivation. -/
theorem T_exp {y : A} (hy : inv' y = y) (hn : IsNilpotent y) :
    T univ (IsNilpotent.exp y) = IsNilpotent.exp y * T univ y := by
  obtain ⟨k, hk⟩ := hn
  have hk1 : y ^ (k + 1) = 0 := by rw [pow_succ, hk, zero_mul]
  conv_rhs => rw [IsNilpotent.exp_eq_sum hk]
  rw [IsNilpotent.exp_eq_sum hk1, map_sum, Finset.sum_mul, Finset.sum_range_succ', pow_zero,
    LinearMap.map_smul_of_tower, T_one, smul_zero, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.map_smul_of_tower, T_pow hy, smul_mul_assoc, Nat.cast_smul_eq_nsmul ℝ,
    ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, Nat.factorial_succ, Nat.cast_mul]
  congr 1
  field_simp

theorem T_dot (a b : Λ) : T univ (dot a b) = 0 := by
  have := T_Xc (s := univ) (mem_univ a) (mem_univ b)
  rwa [coe_Xc, map_add, T_one, zero_add] at this

theorem T_action (β : Λ → Λ → ℝ) (h : Λ → ℝ) :
    T univ (-action β h) = ∑ x, h x • η x := by
  simp [action, map_sum, T_dot, T_z, T_one]

theorem inv'_action (β : Λ → Λ → ℝ) (h : Λ → ℝ) : inv' (-action β h) = -action β h := by
  simp [action, map_sum, inv'_dot, inv'_z]

/-- Ward identity for a general external field: `[T F]_{β,h} = -[F̂ ∑_x h_x η_x]_{β,h}`, where
`F̂` is the grade involution of `F`. -/
theorem expect_T_field (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) (h : Λ → ℝ) (F : A) :
    expect β h (T univ F) = -expect β h (inv' F * ∑ x, h x • η x) := by
  have hn : IsNilpotent (-action β h) := by
    rw [action_eq β hβ h, neg_neg]
    exact (isNilpotent_W β hβ h).map cv
  have h0 : int0 (T univ (F * IsNilpotent.exp (-action β h))) = 0 := by
    rw [int0, berezin_T (fun i _ => Finset.mem_toList.2 (mem_univ i)), map_zero]
  rw [T_mul, T_exp (inv'_action β h) hn, T_action, int0, map_add, map_add] at h0
  rw [expect, expect, int0, int0, mul_assoc, ← mul_comm_of_even
    (show inv' (IsNilpotent.exp (-action β h)) = _ from ?_) (∑ x, h x • η x)]
  · linarith
  · rw [IsNilpotent.map_exp hn, inv'_action]

theorem avg_T_ξ (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) (h : ℝ) (a : Λ) :
    avg β (fun _ => h) (T univ (ξ a)) = h * ∑ x, avg β (fun _ => h) (ξ a * η x) := by
  have hinv : inv' (ξ a) = -ξ a := inv'_ι _
  rw [avg, expect_T_field β hβ, hinv, neg_mul, expect_neg, neg_neg, ← Finset.smul_sum,
    mul_smul_comm, expect_smul, Finset.mul_sum, expect_eq_L, map_sum, mul_div_assoc,
    Finset.sum_div]
  rfl

/-- **Ward identity `e:ward`** of `h02rg.tex`. For a constant external field `h`,
`⟨z_a⟩_{β,h} = ⟨T ξ_a⟩_{β,h} = -∑_x h ⟨ξ_a T z_x⟩_{β,h} = h ∑_x ⟨ξ_a η_x⟩_{β,h}`,
where `T = ∑_x z_x ∂_{ξ_x}` is the symmetry generator `e:Tdef`. -/
theorem ward (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) (h : ℝ) (a : Λ) :
    avg β (fun _ => h) (z a) = avg β (fun _ => h) (T univ (ξ a)) ∧
    avg β (fun _ => h) (T univ (ξ a)) = -∑ x, h * avg β (fun _ => h) (ξ a * T univ (z x)) ∧
    -∑ x, h * avg β (fun _ => h) (ξ a * T univ (z x)) =
      h * ∑ x, avg β (fun _ => h) (ξ a * η x) := by
  have h3 : -∑ x, h * avg β (fun _ => h) (ξ a * T univ (z x)) =
      h * ∑ x, avg β (fun _ => h) (ξ a * η x) := by
    simp only [T_z (mem_univ _), mul_neg, avg, expect_neg, neg_div, Finset.sum_neg_distrib,
      neg_neg, Finset.mul_sum]
  exact ⟨by rw [T_ξ (mem_univ a)], by rw [h3, avg_T_ξ β hβ], h3⟩

end

end H02
