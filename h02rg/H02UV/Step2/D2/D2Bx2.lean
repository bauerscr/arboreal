import Step2.D2.D2Bx1

/-!
# The general bilinear bound for `𝔅x`

Lattice differences on `ℤ²`: `Δᵢ f(u) = f(u + eᵢ) - 2f(u) + f(u - eᵢ)`, `Λ = Δ₀ + Δ₁`,
`∂₀ f(u) = f(u + e₀) - f(u - e₀)`.

* `stK_kap0`: `K₀ = -2Δ₀ + 2Δ₁ - Δ₀Δ₀`; `stK_kap2`: `K₂ = ½ Λ²`;
* `LL_mom0`: `Λ²(u₀ f) = u₀ Λ² f + 2 ∂₀ Λ f`;
* `bubX_bound`: **if `a` has range `R` and `|a| ≤ M_A`, and `c` has
  `|Δᵢ c| ≤ B₂`, `|Δ₀Δ₀ c|, |Λ²c| ≤ B₄`, `|∂₀Λ c| ≤ B₃`, then**
  `|𝔅x(a, c)| ≤ (2R+1)² M_A (4B₂ + B₄ + R(R B₄ + 2B₃)/2)`.
  For `c` of scale `ρ` (`Bₖ = M_C ρ^{-k}`) and `R ≤ ρ` this is `≤ 9 · 7 M_A M_C (R+1)²/ρ²`.
-/

namespace Step2

open Finset MeasureTheory Step2.D2

noncomputable section

/-- `Δ₀ f(u) = f(u + e₀) - 2 f(u) + f(u - e₀)`. -/
def dd0 (f : ℤ × ℤ → ℂ) (u : ℤ × ℤ) : ℂ := f (u.1 + 1, u.2) - 2 * f u + f (u.1 - 1, u.2)

/-- `Δ₁ f(u) = f(u + e₁) - 2 f(u) + f(u - e₁)`. -/
def dd1 (f : ℤ × ℤ → ℂ) (u : ℤ × ℤ) : ℂ := f (u.1, u.2 + 1) - 2 * f u + f (u.1, u.2 - 1)

/-- `Λ = Δ₀ + Δ₁`. -/
def lapZ (f : ℤ × ℤ → ℂ) (u : ℤ × ℤ) : ℂ := dd0 f u + dd1 f u

/-- `∂₀ f(u) = f(u + e₀) - f(u - e₀)`. -/
def cd0 (f : ℤ × ℤ → ℂ) (u : ℤ × ℤ) : ℂ := f (u.1 + 1, u.2) - f (u.1 - 1, u.2)

theorem stK_kap0 (f : ℤ × ℤ → ℂ) (u : ℤ × ℤ) :
    stK kap0 f u = -2 * dd0 f u + 2 * dd1 f u - dd0 (dd0 f) u := by
  obtain ⟨u1, u2⟩ := u
  simp only [stK, kap0, dd0, dd1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring_nf

theorem stK_kap2 (f : ℤ × ℤ → ℂ) (u : ℤ × ℤ) :
    stK kap2 f u = (1 / 2 : ℂ) * lapZ (lapZ f) u := by
  obtain ⟨u1, u2⟩ := u
  simp only [stK, kap2, lapZ, dd0, dd1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring_nf

theorem LL_mom0 (f : ℤ × ℤ → ℂ) (u : ℤ × ℤ) :
    lapZ (lapZ (mom0 f)) u = (u.1 : ℂ) * lapZ (lapZ f) u + 2 * cd0 (lapZ f) u := by
  obtain ⟨u1, u2⟩ := u
  simp only [lapZ, dd0, dd1, cd0, mom0]
  push_cast
  ring_nf

/-- The box `[-R, R]²`. -/
def boxR (R : ℕ) : Finset (ℤ × ℤ) := Finset.Icc (-(R : ℤ)) R ×ˢ Finset.Icc (-(R : ℤ)) R

theorem card_boxR (R : ℕ) : ((boxR R).card : ℝ) = (2 * R + 1) ^ 2 := by
  rw [boxR, card_product, Int.card_Icc]
  push_cast
  have : ((R : ℤ) + 1 - -(R : ℤ)).toNat = 2 * R + 1 := by omega
  rw [this]; push_cast; ring

theorem mem_boxR {R : ℕ} {v : ℤ × ℤ} (h : nm v ≤ R) : v ∈ boxR R := by
  simp only [boxR, mem_product, Finset.mem_Icc]
  simp only [nm] at h
  omega

theorem finsum_norm_le {F : ℤ × ℤ → ℂ} {R : ℕ} (hF : ∀ v, R < nm v → F v = 0) {B : ℝ}
    (hB : ∀ v, nm v ≤ R → ‖F v‖ ≤ B) : ‖∑ᶠ v, F v‖ ≤ (2 * R + 1) ^ 2 * B := by
  rw [finsum_eq_sum_of_support_subset _ (s := boxR R) (fun v hv => by
    simp only [Function.mem_support] at hv
    rw [Finset.mem_coe]
    exact mem_boxR (by by_contra h; push Not at h; exact hv (hF v h)))]
  calc ‖∑ v ∈ boxR R, F v‖ ≤ ∑ v ∈ boxR R, ‖F v‖ := norm_sum_le _ _
    _ ≤ ∑ _v ∈ boxR R, B := sum_le_sum fun v hv => by
        refine hB v ?_
        simp only [boxR, mem_product, Finset.mem_Icc] at hv
        simp only [nm]; omega
    _ = (2 * R + 1) ^ 2 * B := by rw [sum_const, nsmul_eq_mul, card_boxR]

/-- **The general bilinear bound.** -/
theorem bubX_bound {a c : ℤ × ℤ → ℂ} {R : ℕ} (haR : ∀ v, R < nm v → a v = 0)
    (hc : Function.HasFiniteSupport c) {MA B2 B3 B4 : ℝ} (hMA : ∀ v, ‖a v‖ ≤ MA)
    (h0 : ∀ u, ‖dd0 c u‖ ≤ B2) (h1 : ∀ u, ‖dd1 c u‖ ≤ B2) (h00 : ∀ u, ‖dd0 (dd0 c) u‖ ≤ B4)
    (hLL : ∀ u, ‖lapZ (lapZ c) u‖ ≤ B4) (hcL : ∀ u, ‖cd0 (lapZ c) u‖ ≤ B3) :
    ‖bubX a c‖ ≤ (2 * R + 1) ^ 2 * (MA * (4 * B2 + B4)) +
      (2 * R + 1) ^ 2 * (R * MA * ((R * B4 + 2 * B3) / 2)) := by
  have ha : Function.HasFiniteSupport a := hfs_of_range a haR
  rw [bubX_pos a c ha hc]
  have hMA0 : 0 ≤ MA := (norm_nonneg _).trans (hMA 0)
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine finsum_norm_le (fun v hv => by rw [haR v hv, zero_mul]) fun v _ => ?_
    rw [norm_mul, stK_kap0]
    refine mul_le_mul (hMA v) ?_ (norm_nonneg _) hMA0
    calc ‖-2 * dd0 c (-v.1, -v.2) + 2 * dd1 c (-v.1, -v.2) - dd0 (dd0 c) (-v.1, -v.2)‖
        ≤ ‖-2 * dd0 c (-v.1, -v.2)‖ + ‖2 * dd1 c (-v.1, -v.2)‖ + ‖dd0 (dd0 c) (-v.1, -v.2)‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ 2 * B2 + 2 * B2 + B4 := by
          rw [norm_mul, norm_mul]
          simp only [norm_neg, Complex.norm_ofNat]
          gcongr
          · exact h0 _
          · exact h1 _
          · exact h00 _
      _ = 4 * B2 + B4 := by ring
  · refine finsum_norm_le (fun v hv => by rw [haR v hv, mul_zero, zero_mul]) fun v hv => ?_
    rw [stK_kap2, LL_mom0, norm_mul, norm_mul]
    have hv1 : ‖((v.1 : ℤ) : ℂ)‖ ≤ R := by
      rw [Complex.norm_intCast]
      have h1 : -(R : ℤ) ≤ v.1 ∧ v.1 ≤ R := by simp only [nm] at hv; omega
      rw [abs_le]; exact ⟨by exact_mod_cast h1.1, by exact_mod_cast h1.2⟩
    have hw : ‖(1 / 2 : ℂ) * ((((-v.1 : ℤ)) : ℂ) * lapZ (lapZ c) (-v.1, -v.2) +
        2 * cd0 (lapZ c) (-v.1, -v.2))‖ ≤ (R * B4 + 2 * B3) / 2 := by
      rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
      have : ‖(((-v.1 : ℤ)) : ℂ) * lapZ (lapZ c) (-v.1, -v.2) + 2 * cd0 (lapZ c) (-v.1, -v.2)‖ ≤
          R * B4 + 2 * B3 := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_mul]
          have h' : ‖(((-v.1 : ℤ)) : ℂ)‖ ≤ R := by
            rw [Int.cast_neg, norm_neg]; exact hv1
          exact mul_le_mul h' (hLL _) (norm_nonneg _) (Nat.cast_nonneg _)
        · rw [norm_mul, Complex.norm_ofNat]; gcongr; exact hcL _
      linarith
    have e : ((-v.1 : ℤ) : ℂ) = (((-v.1, -v.2) : ℤ × ℤ).1 : ℂ) := rfl
    rw [← e]
    calc ‖((v.1 : ℤ) : ℂ)‖ * ‖a v‖ * ‖(1 / 2 : ℂ) * ((((-v.1 : ℤ)) : ℂ) * lapZ (lapZ c) (-v.1, -v.2) +
          2 * cd0 (lapZ c) (-v.1, -v.2))‖ ≤ R * MA * ((R * B4 + 2 * B3) / 2) := by
          gcongr
          · exact hMA v
      _ = _ := rfl

end

end Step2
