import Spin2.Cont.ContEqF2

set_option autoImplicit false

/-!
# B3, `r`-dependent form, final assembly (III): helpers

* `eqfCd r = ⌈log_L(1/r)⌉₊ + 3` and `eqf_Cd_pow`: `2/r ≤ L^{eqfCd r}`.
* `eqf_scale`: `|ΔP|/ϑ_ε² ≤ 10·K·Q` from `|ΔP| ≤ 2KQϑ_{N_h}²` and `ǧ_{N_h} ≥ 1/(5β_R)`.
* `eqf_half_pow`: `(1/2)^n ≤ ε` eventually; `eqf_Lpow_inv_le`: `1/L^n ≤ (1/2)^n`.
-/

namespace Spin2

open Step Step2 PtCorr2 Filter Topology

noncomputable section

/-- `C_δ(r) = ⌈log_L(1/r)⌉₊ + 3`. -/
def eqfCd (L : ℕ) (r : ℝ) : ℕ := ⌈Real.logb L (1 / r)⌉₊ + 3

theorem eqf_Cd_pow {L : ℕ} (hL : 2 ≤ L) {r : ℝ} (hr : 0 < r) :
    2 / r ≤ (L : ℝ) ^ eqfCd L r ∧ 2 ≤ eqfCd L r := by
  refine ⟨?_, by unfold eqfCd; omega⟩
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
  have hL0 : (0 : ℝ) < L := by linarith
  have h1 : 1 / r ≤ (L : ℝ) ^ ⌈Real.logb L (1 / r)⌉₊ := by
    rw [← Real.rpow_natCast]
    calc 1 / r = (L : ℝ) ^ Real.logb L (1 / r) := (Real.rpow_logb hL0 hL1.ne' (by positivity)).symm
      _ ≤ (L : ℝ) ^ ((⌈Real.logb L (1 / r)⌉₊ : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL1.le (Nat.le_ceil _)
  have h2 : (8 : ℝ) ≤ (L : ℝ) ^ 3 := by
    have : (2 : ℝ) ^ 3 ≤ (L : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hL) 3
    norm_num at this ⊢; linarith
  unfold eqfCd
  rw [pow_add]
  have h3 : 0 < 1 / r := by positivity
  have := mul_le_mul h1 h2 (by norm_num) (by positivity)
  have e : 2 / r ≤ 1 / r * 8 := by rw [div_le_iff₀ hr]; field_simp; linarith
  linarith

/-- `1/L^n ≤ (1/2)^n`. -/
theorem eqf_Lpow_inv_le {L : ℕ} (hL : 2 ≤ L) (n : ℕ) : 1 / (L : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ n := by
  rw [one_div_pow, one_div_le_one_div (by positivity) (by positivity)]
  exact pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hL) n

theorem eqf_half_pow {ε : ℝ} (hε : 0 < ε) : ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → (1 / 2 : ℝ) ^ n ≤ ε := by
  obtain ⟨n₀, hn₀⟩ := exists_pow_lt_of_lt_one hε (show (1 / 2 : ℝ) < 1 by norm_num)
  exact ⟨n₀, fun n hn => (pow_le_pow_of_le_one (by norm_num) (by norm_num) hn).trans hn₀.le⟩

/-- **The `ϑ` normalisation**: `|ΔP|/(β_Rb)^{2/3} ≤ 10KQ`. -/
theorem eqf_scale {P K Q g βR b : ℝ} (hb : 0 < b) (hβ : 0 < βR) (hg : 0 < g)
    (hgl : 1 / βR / 5 ≤ g) (hK : 0 ≤ K) (hQ : 0 ≤ Q)
    (hP : |P| ≤ 2 * (K * Q * ((b / g) ^ (1 / 3 : ℝ)) ^ 2)) :
    |P| / (βR * b) ^ (2 / 3 : ℝ) ≤ 10 * (K * Q) := by
  have hθ : 0 < (βR * b) ^ (2 / 3 : ℝ) := by positivity
  rw [div_le_iff₀ hθ]
  have hv : ((b / g) ^ (1 / 3 : ℝ)) ^ 2 = (b / g) ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  have hbg : b / g ≤ 5 * (βR * b) := by
    rw [div_le_iff₀ hg]
    have : 1 / βR ≤ 5 * g := by linarith
    rw [div_le_iff₀ hβ] at this
    nlinarith
  have h1 : (b / g) ^ (2 / 3 : ℝ) ≤ (5 * (βR * b)) ^ (2 / 3 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hbg (by norm_num)
  have h2 : (5 * (βR * b)) ^ (2 / 3 : ℝ) = 5 ^ (2 / 3 : ℝ) * (βR * b) ^ (2 / 3 : ℝ) :=
    Real.mul_rpow (by norm_num) (by positivity)
  have h3 : (5 : ℝ) ^ (2 / 3 : ℝ) ≤ 5 := by
    have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 5 by norm_num)
      (show (2 / 3 : ℝ) ≤ 1 by norm_num)
    rwa [Real.rpow_one] at this
  rw [hv] at hP
  have hKQ : 0 ≤ K * Q := mul_nonneg hK hQ
  have h4 : (b / g) ^ (2 / 3 : ℝ) ≤ 5 * (βR * b) ^ (2 / 3 : ℝ) := by
    rw [h2] at h1; nlinarith
  have := mul_le_mul_of_nonneg_left h4 hKQ
  nlinarith

end

end Spin2
