import Step2.D2.D2Cov
import DressedFRD.FrdMain

/-!
# The dressed covariance `C'_{j+1}` (`prop:d2`, first line, (R6) for `C'`)

For the dressed decomposition built from the concrete family `Pc` (`DressedFRD.thm_main_frd`,
`d = 2`), `C'_{j+1} = Z_{j+1} Γ^int_{j+1}`, and `kern w x = w(x, 0)`.

* `kern_ofR_frdC`: `kern Ĉ_{j+1} x = C_{j+1}(x, 0)` for `j + 1 < N`;
* `abs_kern_sub_le`: in `d = 2` the weight of `‖·‖_{(j)}` at `α = 0` is `1`, so
  `|C'_{j+1}(x,0) - C_{j+1}(x,0)| ≤ ‖C'_{j+1} - C_{j+1}‖_{(j)} ≤ K |ζ|_{≤ j}` (`Concl.close`);
* `Cprime_values`: **`C'_{j+1}(0,0)` and `C'_{j+1}(e₁,0)` equal
  `(1/2π) log L + O(L^{-2j} + m²(L^{2j} + L^{2(j+1)}) + |ζ|_{≤ j})`**, uniformly in `N`, `m²`
  and `ζ`, for `1 ≤ j`, `j + 1 < N`, `L ≥ 7`.
-/

namespace Step2.D2

noncomputable section

open MeasureTheory Set Filter Real FRD DressedFRD DressedFRD.Data

variable {n : ℕ} [NeZero n]

theorem kern_ofR_frdC {msq : ℝ} {L N : ℕ} {k : ℕ} (hk : k < N) (x : Grassmann.Torus 2 n) :
    kern (ofR (frdC Pc msq L N k)) x = ((FRD.Cj Pc msq (L : ℝ) k x 0 : ℝ) : ℂ) := by
  rw [kern_ofR_eq_fmat (fun m => frdC_even Pc k m), frdC_of_lt Pc hk]
  rfl

theorem wgt_two_zero (L : ℝ) (s : ℕ) : wgt 2 L s 0 = 1 := by
  simp [wgt, Grassmann.mabs]

/-- In `d = 2`: `|k_w(x)| ≤ ‖w‖_{(s)}`. -/
theorem norm_kern_le_snorm {L : ℝ} (hL : 0 < L) (q s : ℕ) (w : Sym 2 n) (x : Grassmann.Torus 2 n) :
    ‖kern w x‖ ≤ snorm L q s w := by
  have := norm_kern_le (q := q) (s := s) hL w x
  rwa [wgt_two_zero, inv_one, one_mul] at this

theorem msq_le_one {L N : ℕ} (hL : 1 ≤ L) (hN : 1 ≤ N) {msq : ℝ}
    (h : msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) : msq ≤ 1 := by
  refine h.trans (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hL) ?_)
  have : (1 : ℝ) ≤ N := by exact_mod_cast hN
  linarith

theorem pow_half_lt {L N j : ℕ} (hL : 2 ≤ L) (hj : j + 1 < N) :
    (L : ℝ) ^ (j + 1) / 2 + 1 < ((L ^ N : ℕ) : ℝ) := by
  have h1 : L ^ (j + 1) * L ≤ L ^ N := by
    rw [← pow_succ]; exact Nat.pow_le_pow_right (by omega) hj
  have h2 : (L : ℝ) ^ (j + 1) * 2 ≤ (L : ℝ) ^ N := by
    have : ((L ^ (j + 1) * L : ℕ) : ℝ) ≤ ((L ^ N : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at this
    have hL' : (2 : ℝ) ≤ L := by exact_mod_cast hL
    nlinarith [pow_pos (show (0 : ℝ) < L by linarith) (j + 1)]
  have h3 : (1 : ℝ) ≤ (L : ℝ) ^ (j + 1) := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ L))
  push_cast
  linarith

theorem lift_e1 (n : ℕ) [NeZero n] (i : Fin 2) :
    (((![1, 0] : Fin 2 → ℤ) i : ℤ) : ZMod n) =
      ((unitT 0 - 0 : Grassmann.Torus 2 n) : Fin 2 → ZMod n) i := by
  fin_cases i <;> simp [unitT]

/-- **`prop:d2`, first line, for the dressed covariance.** There are `ζ̄ > 0` and `K` such that
for all `N ≥ 1`, `n = L^N`, `0 < m² ≤ L^{-2(N-1)}`, `|ζ_i| ≤ ζ̄`, `1 ≤ j`, `j + 1 < N`, with
`C'_{j+1}(x, 0) = kern (Z_{j+1} Γ^int_{j+1}) x`:
`|C'_{j+1}(0,0) - (1/2π) log L|`, `|C'_{j+1}(e₁,0) - (1/2π) log L|`
`≤ (2π)^{-2} (C L^{-2j} + B m² (L^{2j} + L^{2(j+1)})) + K |ζ|_{≤ j}`,
with `C = ErrC` (diagonal), `C = ErrC1` (`e₁`), `B = ErrB` absolute constants. -/
theorem Cprime_values {q L : ℕ} (hq : 2 ≤ q) (hL : 7 ≤ L) :
    ∃ ζbar : ℝ, 0 < ζbar ∧ ∃ K : ℝ, ∀ (n : ℕ) [NeZero n] (N : ℕ) (msq : ℝ) (ζ : ℕ → ℂ),
      1 ≤ N → n = L ^ N → 0 < msq → msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) →
      (∀ i, ‖ζ i‖ ≤ ζbar) → ∀ j, 1 ≤ j → j + 1 < N →
      let D : Data 2 n := ⟨L, N, msq, frdC Pc msq L N, ζ⟩
      ‖kern (D.Z (j + 1) • D.Gint j) 0 - (Real.log L / (2 * π) : ℝ)‖ ≤
          (2 * π)⁻¹ ^ 2 * (ErrC / ((L : ℝ) ^ j) ^ 2 +
            ErrB * msq * (((L : ℝ) ^ j) ^ 2 + ((L : ℝ) ^ (j + 1)) ^ 2)) + K * D.Mz (j + 1) ∧
      ‖kern (D.Z (j + 1) • D.Gint j) (unitT 0) - (Real.log L / (2 * π) : ℝ)‖ ≤
          (2 * π)⁻¹ ^ 2 * (ErrC1 / ((L : ℝ) ^ j) ^ 2 +
            ErrB * msq * (((L : ℝ) ^ j) ^ 2 + ((L : ℝ) ^ (j + 1)) ^ 2)) + K * D.Mz (j + 1) := by
  obtain ⟨ζbar, hζ, -, K, hK⟩ := thm_main_frd Pc (d := 2) le_rfl hq hL
  refine ⟨ζbar, hζ, K, fun n _ N msq ζ hN hn hmsq hmsq' hζb j hj hjN => ?_⟩
  intro D
  have hc : D.Concl q ζbar K j := (hK n N msq ζ hN hn hmsq hmsq').1 hζb j (by omega)
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hm1 := msq_le_one (by omega) hN hmsq'
  have hclose := hc.close hjN
  have hn' : (L : ℝ) ^ (j + 1) / 2 + 1 < (n : ℝ) := by
    rw [hn]; exact pow_half_lt (by omega) hjN
  have hdiff : ∀ x : Grassmann.Torus 2 n,
      ‖kern (D.Z (j + 1) • D.Gint j) x - ((FRD.Cj Pc msq (L : ℝ) (j + 1) x 0 : ℝ) : ℂ)‖ ≤
        K * D.Mz (j + 1) := by
    intro x
    rw [← kern_ofR_frdC hjN x, ← kern_sub]
    exact (norm_kern_le_snorm hL0 q j _ x).trans hclose
  have key : ∀ (x : Grassmann.Torus 2 n) (B : ℝ),
      |FRD.Cj Pc msq (L : ℝ) (j + 1) x 0 - Real.log L / (2 * π)| ≤ B →
      ‖kern (D.Z (j + 1) • D.Gint j) x - (Real.log L / (2 * π) : ℝ)‖ ≤ B + K * D.Mz (j + 1) := by
    intro x B hB
    have e : kern (D.Z (j + 1) • D.Gint j) x - ((Real.log L / (2 * π) : ℝ) : ℂ) =
        (kern (D.Z (j + 1) • D.Gint j) x - ((FRD.Cj Pc msq (L : ℝ) (j + 1) x 0 : ℝ) : ℂ)) +
          (((FRD.Cj Pc msq (L : ℝ) (j + 1) x 0 - Real.log L / (2 * π) : ℝ)) : ℂ) := by
      push_cast; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    linarith [hdiff x]
  constructor
  · refine key 0 _ ?_
    have := Cj_succ_diag_value hmsq.le hm1 hL1 hj (0 : Grassmann.Torus 2 n) (by linarith)
    exact this
  · refine key (unitT 0) _ ?_
    exact Cj_succ_e1_value hmsq.le hm1 hL1 hj (unitT 0) 0 (lift_e1 n) hn'

end

end Step2.D2
