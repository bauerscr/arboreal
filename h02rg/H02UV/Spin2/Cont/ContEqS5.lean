import Spin2.Cont.ContEqS4

set_option autoImplicit false

/-!
# B3, `r`-dependent form: pure waiting estimates

* **`eqs_wait_pure`**: the waiting hypothesis `hwait` of `fin_T6_mid`/`fin_conn_diff_top` for the
  explicit `Q₀ = (7/5)^n(τ_w/(cǧ) + τ_k/(8B(cǧ)²))` from `(3/4)^n·K_W ≤ ǧ_{ms}²`
  (`(8/15)(7/5) ≤ 3/4`, `(8/15)²(7/5)(81/56) ≤ 3/4`).
* `eqs_pow_mul_le`: `(a)^n(b)^n ≤ (3/4)^n` for `ab ≤ 3/4`.
-/

namespace Spin2

noncomputable section

theorem eqs_pow_mul_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a * b ≤ 3 / 4) (n : ℕ) :
    a ^ n * b ^ n ≤ (3 / 4 : ℝ) ^ n := by
  rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) h n

/-- **The waiting estimate** (pure). -/
theorem eqs_wait_pure {n : ℕ} {g c Bk cab Tw Tk τw τk Z Θ K₂ KW : ℝ} (hg : 0 < g) (hg1 : g ≤ 1)
    (hc : 1 ≤ c) (hBk : 0 < Bk) (hτw : 0 ≤ τw) (hτw' : τw ≤ Tw) (hτk : 0 ≤ τk)
    (hτk' : τk ≤ Tk) (hΘ : 0 ≤ Θ) (hK₂ : 0 ≤ K₂)
    (hZ : Z / (cab * (c * g)) ≤ (7 / 5) ^ n * (Θ * (81 / 56) ^ n) * K₂ / g ^ 2)
    (hKW : 2 * (Tw + Tk / (8 * Bk)) + 4 * (Θ * K₂) ≤ KW) (hW : (3 / 4) ^ n * KW ≤ g ^ 2) :
    (8 / 15) ^ n * ((7 / 5) ^ n * τw / (c * g) + (7 / 5) ^ n * τk / (8 * Bk * (c * g) ^ 2) +
      Real.sqrt (Z / (cab * (c * g)))) ≤ 1 := by
  have hq : (0 : ℝ) ≤ (3 / 4) ^ n := by positivity
  have hp : (8 / 15 : ℝ) ^ n * (7 / 5) ^ n ≤ (3 / 4) ^ n :=
    eqs_pow_mul_le (by norm_num) (by norm_num) (by norm_num) n
  have hg2 : 0 < g ^ 2 := by positivity
  have hcg : g ≤ c * g := le_mul_of_one_le_left hg.le hc
  have hgg : g ^ 2 ≤ g := by nlinarith
  have hcg2 : g ^ 2 ≤ (c * g) ^ 2 := pow_le_pow_left₀ hg.le hcg 2
  have hTw : 0 ≤ Tw := hτw.trans hτw'
  have hTk : 0 ≤ Tk := hτk.trans hτk'
  -- the `Q₀` part
  have t1 : (8 / 15 : ℝ) ^ n * ((7 / 5) ^ n * τw / (c * g)) ≤ (3 / 4) ^ n * Tw / g ^ 2 := by
    rw [← mul_div_assoc, ← mul_assoc, div_le_div_iff₀ (by positivity) hg2]
    have h1 : (8 / 15 : ℝ) ^ n * (7 / 5) ^ n * τw ≤ (3 / 4) ^ n * Tw :=
      mul_le_mul hp hτw' hτw hq
    have h2 := mul_le_mul h1 (hgg.trans hcg) hg2.le (by positivity)
    linarith
  have t2 : (8 / 15 : ℝ) ^ n * ((7 / 5) ^ n * τk / (8 * Bk * (c * g) ^ 2)) ≤
      (3 / 4) ^ n * (Tk / (8 * Bk)) / g ^ 2 := by
    rw [← mul_div_assoc, ← mul_assoc, div_le_div_iff₀ (by positivity) hg2]
    have h1 : (8 / 15 : ℝ) ^ n * (7 / 5) ^ n * τk ≤ (3 / 4) ^ n * Tk :=
      mul_le_mul hp hτk' hτk hq
    have e : (3 / 4 : ℝ) ^ n * (Tk / (8 * Bk)) * (8 * Bk * (c * g) ^ 2) =
        (3 / 4) ^ n * Tk * (c * g) ^ 2 := by field_simp
    rw [e]
    have := mul_le_mul h1 hcg2 hg2.le (by positivity)
    linarith
  have t12 : (3 / 4 : ℝ) ^ n * Tw / g ^ 2 + (3 / 4) ^ n * (Tk / (8 * Bk)) / g ^ 2 ≤ 1 / 2 := by
    rw [← add_div, div_le_iff₀ hg2]
    have : (3 / 4 : ℝ) ^ n * (2 * (Tw + Tk / (8 * Bk))) ≤ (3 / 4) ^ n * KW :=
      mul_le_mul_of_nonneg_left (by have : 0 ≤ 4 * (Θ * K₂) := by positivity
                                    linarith) hq
    nlinarith
  -- the square root part
  set a := (8 / 15 : ℝ) ^ n with had
  have ha : 0 ≤ a := by positivity
  have hsq : a * Real.sqrt (Z / (cab * (c * g))) ≤ 1 / 2 := by
    have e : a * Real.sqrt (Z / (cab * (c * g))) = Real.sqrt (a ^ 2 * (Z / (cab * (c * g)))) := by
      rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha]
    rw [e]
    have h4 : Real.sqrt (1 / 4) = 1 / 2 := by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h4]
    refine Real.sqrt_le_sqrt ?_
    have hb : a ^ 2 * (7 / 5) ^ n * (81 / 56) ^ n ≤ (3 / 4) ^ n := by
      rw [had, ← pow_mul, mul_comm (n) 2, pow_mul, ← mul_pow, ← mul_pow]
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) n
    have h5 := mul_le_mul_of_nonneg_left hZ (sq_nonneg a)
    refine h5.trans ?_
    rw [show a ^ 2 * ((7 / 5) ^ n * (Θ * (81 / 56) ^ n) * K₂ / g ^ 2) =
      a ^ 2 * (7 / 5) ^ n * (81 / 56) ^ n * (Θ * K₂) / g ^ 2 by ring, div_le_iff₀ hg2]
    have h6 := mul_le_mul_of_nonneg_right hb (show 0 ≤ Θ * K₂ by positivity)
    have : (3 / 4 : ℝ) ^ n * (4 * (Θ * K₂)) ≤ (3 / 4) ^ n * KW :=
      mul_le_mul_of_nonneg_left (by have : 0 ≤ 2 * (Tw + Tk / (8 * Bk)) := by positivity
                                    linarith) hq
    nlinarith
  rw [mul_add, mul_add]
  linarith

end

end Spin2
