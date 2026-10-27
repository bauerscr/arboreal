import Mathlib

/-!
# A linear recursion for the errors along two histories (Lipschitz bounds, part 20)

`err_rec`: three nonnegative error sequences `v` (couplings), `w` (`𝒲^lin`), `z` (zero mode),
vanishing at `0`, with
* `v_{k+1} ≤ a₀ M + a₁ w_k + η (v_k + z_k + V_k)`,
* `w_{k+1} ≤ q w_k + η (M + v_k + z_k + V_k)`,
* `z_{k+1} ≤ q z_k + b (v_k + V_k)`,
where `V_k = sup_{i ≤ k} v_i` (here: any bound valid for all `i ≤ k`), are bounded by
`v ≤ V M`, `w ≤ W M`, `z ≤ Z M` whenever the constants satisfy the closure inequalities.
-/

namespace Step2

theorem err_rec {M a₀ a₁ η q b V W Z : ℝ} (hM : 0 ≤ M) (ha₁ : 0 ≤ a₁) (hη : 0 ≤ η) (hq : 0 ≤ q)
    (hb : 0 ≤ b) (hV : 0 ≤ V) (hW : 0 ≤ W) (hZ : 0 ≤ Z)
    (c1 : a₀ + a₁ * W + η * (2 * V + Z) ≤ V) (c2 : q * W + η * (1 + 2 * V + Z) ≤ W)
    (c3 : q * Z + b * (2 * V) ≤ Z) {j : ℕ} (v w z : ℕ → ℝ)
    (h0 : v 0 = 0 ∧ w 0 = 0 ∧ z 0 = 0)
    (hstep : ∀ k < j, (∀ i ≤ k, v i ≤ V * M) →
      v (k + 1) ≤ a₀ * M + a₁ * w k + η * (v k + z k + V * M) ∧
      w (k + 1) ≤ q * w k + η * (M + v k + z k + V * M) ∧
      z (k + 1) ≤ q * z k + b * (v k + V * M)) :
    ∀ k ≤ j, (∀ i ≤ k, v i ≤ V * M) ∧ w k ≤ W * M ∧ z k ≤ Z * M := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨fun i hi => ?_, ?_, ?_⟩
    · rw [Nat.le_zero.1 hi, h0.1]; positivity
    · rw [h0.2.1]; positivity
    · rw [h0.2.2]; positivity
  | succ k ih =>
    intro hk
    obtain ⟨hv, hw, hz⟩ := ih (by omega)
    obtain ⟨s1, s2, s3⟩ := hstep k (by omega) hv
    have hvk := hv k le_rfl
    have e1 : v (k + 1) ≤ V * M := by
      refine s1.trans ?_
      have := mul_le_mul_of_nonneg_left hw ha₁
      have h2 : η * (v k + z k + V * M) ≤ η * ((2 * V + Z) * M) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hη
      have h3 := mul_le_mul_of_nonneg_right c1 hM
      nlinarith
    refine ⟨fun i hi => ?_, ?_, ?_⟩
    · rcases Nat.lt_or_ge i (k + 1) with h | h
      · exact hv i (by omega)
      · rw [show i = k + 1 by omega]; exact e1
    · refine s2.trans ?_
      have := mul_le_mul_of_nonneg_left hw hq
      have h2 : η * (M + v k + z k + V * M) ≤ η * ((1 + 2 * V + Z) * M) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hη
      have h3 := mul_le_mul_of_nonneg_right c2 hM
      nlinarith
    · refine s3.trans ?_
      have := mul_le_mul_of_nonneg_left hz hq
      have h2 : b * (v k + V * M) ≤ b * ((2 * V) * M) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hb
      have h3 := mul_le_mul_of_nonneg_right c3 hM
      nlinarith

/-- **Choice of the constants** in `err_rec`: for `q ≤ 1/2` and `η` small, `V = 2a₀ + 1`,
`Z = 4bV`, `W = 2η(1 + 2V + Z)` close. -/
theorem err_consts {a₀ a₁ η q b : ℝ} (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁) (hη : 0 ≤ η) (hq : 0 ≤ q)
    (hq2 : q ≤ 1 / 2) (hb : 0 ≤ b)
    (hsmall : η * (2 * a₁ * (1 + 2 * (2 * a₀ + 1) + 4 * b * (2 * a₀ + 1)) +
      (2 * (2 * a₀ + 1) + 4 * b * (2 * a₀ + 1))) ≤ 1 / 2) :
    let V := 2 * a₀ + 1
    let Z := 4 * b * V
    let W := 2 * η * (1 + 2 * V + Z)
    a₀ + a₁ * W + η * (2 * V + Z) ≤ V ∧ q * W + η * (1 + 2 * V + Z) ≤ W ∧
      q * Z + b * (2 * V) ≤ Z := by
  intro V Z W
  have hV : 0 ≤ V := by positivity
  have hZ : 0 ≤ Z := by positivity
  refine ⟨?_, ?_, ?_⟩
  · have e : a₁ * W + η * (2 * V + Z) = η * (2 * a₁ * (1 + 2 * V + Z) + (2 * V + Z)) := by
      simp only [W]; ring
    rw [add_assoc, e]
    simp only [V, Z] at hsmall ⊢
    nlinarith
  · have hW0 : 0 ≤ η * (1 + 2 * V + Z) := by positivity
    have : q * W ≤ 1 / 2 * W := mul_le_mul_of_nonneg_right hq2 (by positivity)
    simp only [W] at this ⊢
    nlinarith
  · have : q * Z ≤ 1 / 2 * Z := mul_le_mul_of_nonneg_right hq2 hZ
    simp only [Z] at this ⊢
    nlinarith

end Step2
