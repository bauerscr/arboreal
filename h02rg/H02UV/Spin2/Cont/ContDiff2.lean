import Spin2.Cont.ContDiff
import PtCorr2.Restart.RerepK
import PtCorr2.Restart.RerepSym

/-!
# B3, T6: restart compatibility of the difference datum — the size bookkeeping (pure)

The hypotheses of `MasterCore.restartD` on a datum at scale `m` with field scale `s = s_m`,
`r = cǧ_m`, `c_W = D.cWo`, `B = D.Bk` are (besides the structural ones)
`|β^δ_m| + D_m ≤ M₀`, `‖𝒲^δ_m(B)‖ ≤ c_W r·2s²M₀`, `A^{(|𝓑|−4)_+}‖K^δ_m‖ ≤ k₀` and
`8k₀ ≤ 4B r²(c_W·2s²M₀)`. For the difference datum `δ = rrSt(o^P) − o^{P'}` the available sizes are
(`csm_K` for both positions, `rr_delta_KbHF`):
`‖𝒲^δ‖ ≤ c_W r 2s²(|β^P| + |β^{P'}|)`,
`k₀ = 16c_W B r²s²(|β^P| + |β^{P'}|) + E`, `E = β̄·4|a−a'|_∞s²L^{-m}·ι·A ≤ 4β̄ιA s²L^{-r}`.

* **`cd2_compat`**: `M₀ := 16(|β^P| + |β^{P'}|) + b₀ + E/(B c_W r² s²)` satisfies all size
  hypotheses (`8k₀ ≤ …` with equality up to `b₀`), and the `K` part of the transient coefficient is
  `8c_Nk₀/(s²M₀) ≤ 8c_N B c_W r²`.
* **`cd2_forced`**: conversely, the `K` condition with these `k₀` forces
  `M₀ ≥ 16(|β^P| + |β^{P'}|) + E/(B c_W r² s²)`: the restart envelope of the difference datum is
  **not** smaller than the couplings themselves (the triangle bound on `K^δ` loses the difference).
* `cd2_reloc_le`: `4|a−a'|_∞s²/L^m ≤ 4s²/L^r` for `|a−a'|_∞ ≤ L^{m−r}`, `r ≤ m`.
-/

namespace Spin2

theorem cd2_compat {B cW r s bP bP' b₀ E : ℝ} (hB : 0 < B) (hcW : 0 < cW) (hr : 0 < r)
    (hs : 0 < s) (hbP : 0 ≤ bP) (hbP' : 0 ≤ bP') (hb₀ : 0 ≤ b₀) (hE : 0 ≤ E) (cN : ℝ)
    (hcN : 0 ≤ cN) :
    let k₀ := 16 * cW * B * r ^ 2 * s ^ 2 * (bP + bP') + E
    let M₀ := 16 * (bP + bP') + b₀ + E / (B * cW * r ^ 2 * s ^ 2)
    b₀ ≤ M₀ ∧ cW * r * (2 * s ^ 2 * (bP + bP')) ≤ cW * r * (2 * s ^ 2 * M₀) ∧
      8 * k₀ ≤ 4 * B * r ^ 2 * (cW * (2 * s ^ 2 * M₀)) ∧
      (0 < M₀ → 8 * cN * k₀ / (s ^ 2 * M₀) ≤ 8 * cN * B * cW * r ^ 2) := by
  intro k₀ M₀
  have hD : 0 < B * cW * r ^ 2 * s ^ 2 := by positivity
  have hq : 0 ≤ E / (B * cW * r ^ 2 * s ^ 2) := div_nonneg hE hD.le
  have hEq : E = B * cW * r ^ 2 * s ^ 2 * (E / (B * cW * r ^ 2 * s ^ 2)) := by
    field_simp
  have hk : k₀ ≤ B * cW * r ^ 2 * s ^ 2 * M₀ := by
    show 16 * cW * B * r ^ 2 * s ^ 2 * (bP + bP') + E ≤
      B * cW * r ^ 2 * s ^ 2 * (16 * (bP + bP') + b₀ + E / (B * cW * r ^ 2 * s ^ 2))
    nth_rewrite 1 [hEq]
    nlinarith [mul_nonneg hD.le hb₀]
  refine ⟨by show b₀ ≤ 16 * (bP + bP') + b₀ + _; linarith, ?_, ?_, fun hM => ?_⟩
  · have : bP + bP' ≤ M₀ := by
      show bP + bP' ≤ 16 * (bP + bP') + b₀ + _; linarith
    gcongr
  · nlinarith
  · rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hk (by positivity : (0 : ℝ) ≤ 8 * cN)]

/-- **The envelope is forced to the size of the couplings.** -/
theorem cd2_forced {B cW r s bP bP' E M₀ : ℝ} (hB : 0 < B) (hcW : 0 < cW) (hr : 0 < r)
    (hs : 0 < s)
    (h8 : 8 * (16 * cW * B * r ^ 2 * s ^ 2 * (bP + bP') + E) ≤
      4 * B * r ^ 2 * (cW * (2 * s ^ 2 * M₀))) :
    16 * (bP + bP') + E / (B * cW * r ^ 2 * s ^ 2) ≤ M₀ := by
  have hD : 0 < B * cW * r ^ 2 * s ^ 2 := by positivity
  have : B * cW * r ^ 2 * s ^ 2 * (16 * (bP + bP') + E / (B * cW * r ^ 2 * s ^ 2)) ≤
      B * cW * r ^ 2 * s ^ 2 * M₀ := by
    rw [mul_add, mul_div_cancel₀ _ hD.ne']
    nlinarith
  exact le_of_mul_le_mul_left this hD

/-- **With a free `K`-step constant `c_k > 60B`** (the form of `PtCorr2.obs_hist_restartB`,
`8k₀ ≤ (c_k − 60B)r²c_W·2s²M₀`), the envelope `M₀ = 64B(b+b')/(c_k − 60B) + 4E/((c_k − 60B)r²c_Ws²)`
suffices (equality). With `c_k ≍ ε₀/(c_R ǧ_m)` this is `M₀ ≍ ǧ_m|β| + E/(ǧ_m s²)`. -/
theorem cd2_compat_ck {B cW r s bP bP' E ck : ℝ} (hck : 60 * B < ck) (hcW : 0 < cW) (hr : 0 < r)
    (hs : 0 < s) :
    8 * (16 * cW * B * r ^ 2 * s ^ 2 * (bP + bP') + E) =
      (ck - 60 * B) * r ^ 2 * cW * (2 * s ^ 2 *
        (64 * B * (bP + bP') / (ck - 60 * B) + 4 * E / ((ck - 60 * B) * r ^ 2 * cW * s ^ 2))) := by
  have h1 : ck - 60 * B ≠ 0 := by linarith
  generalize ck - 60 * B = u at h1 ⊢
  have : r ^ 2 * cW * s ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- The relocation factor for `|a − a'|_∞ ≤ L^{m−r}`. -/
theorem cd2_reloc_le {L : ℕ} (hL : 0 < L) {m r : ℕ} (hrm : r ≤ m) {w : ℕ} (hw : w ≤ L ^ (m - r))
    {s : ℝ} : 2 * ((2 : ℕ) : ℝ) * w * s ^ 2 / (L : ℝ) ^ m ≤ 4 * s ^ 2 / (L : ℝ) ^ r := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hw' : (w : ℝ) ≤ (L : ℝ) ^ (m - r) := by exact_mod_cast hw
  have hm : (L : ℝ) ^ m = (L : ℝ) ^ (m - r) * (L : ℝ) ^ r := by
    rw [← pow_add, Nat.sub_add_cancel hrm]
  rw [div_le_div_iff₀ (by positivity) (by positivity), hm]
  push_cast
  have : 0 ≤ s ^ 2 * (L : ℝ) ^ r := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hw' this]

end Spin2
