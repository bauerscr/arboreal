import Spin2.Multiscale.Multiscale

/-!
# (H_λ) from the per-step flow of the vertex (modulus and phase)

`lamHyp_of_log` needs the modulus `log‖λ̂_k‖` and a separate phase bound. Here both come from one
**complex** per-step hypothesis, summed by `LogSum` twice (real and imaginary part of
`∑ log(1 + x_i)`):

* `log_one_add_le`: `‖log(1+x) - x‖ ≤ ‖x‖²` for `‖x‖ ≤ 1/2`;
* `lam_exp_rep`: `λ̂_0 = 1`, `λ̂_{k+1} = λ̂_k(1 + x_k)`, `‖x_k‖ ≤ 1/2` give
  `λ̂_k = exp(∑_{i<k} log(1 + x_i))`;
* **`lamHat_near`** (abstract flow with `LogSum`): if moreover `‖x_k‖ ≤ B'ǧ_k`, `q_0 = 0`,
  `‖q_k‖ ≤ c_qǧ_k` (complex `q`) and
  `‖x_k - (β/3)ǧ_k + (q_{k+1} - q_k)‖ ≤ B(ǧ_k² + ǧ_ka_k)`, then
  `‖λ̂_n - (ǧ_n/b)^{1/3}‖ ≤ K(ǧ_n/b)^{1/3}ǧ_n` (`K = lamNearK`);
* **`lamHat_of_rel`**: the same for `λ̂_k = β_k/β_0` from the relative form of a one-loop flow
  `‖β_{k+1} - β_k(1 - 𝔫_k)‖ ≤ c_δǧ_k²‖β_k(1 - 𝔫_k)‖` (`c_δǧ_k² ≤ 1/8`, `‖𝔫_k‖ ≤ 1/8`,
  `‖𝔫_k‖ ≤ B'ǧ_k`) and the one-loop identification
  `‖-𝔫_k - (β/3)ǧ_k + (q_{k+1} - q_k)‖ ≤ B(ǧ_k² + ǧ_ka_k)`;
* `LamConcl`, **`lamConcl_of`** (from `SpinConcl`): the last statement along the admissible
  trajectories of the master construction, with conclusion `HLam` (`a_k = zA`).
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Step2.D2

theorem log_one_add_le {x : ℂ} (hx : ‖x‖ ≤ 1 / 2) : ‖Complex.log (1 + x) - x‖ ≤ ‖x‖ ^ 2 := by
  have h := Complex.norm_log_one_add_sub_self_le (z := x) (by linarith)
  have h1 : (1 - ‖x‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have h2 : ‖x‖ ^ 2 * (1 - ‖x‖)⁻¹ ≤ ‖x‖ ^ 2 * 2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  linarith

theorem one_add_ne_zero_of_le {x : ℂ} (hx : ‖x‖ ≤ 1 / 2) : 1 + x ≠ 0 := by
  intro h0
  have : x = -1 := by linear_combination h0
  rw [this, norm_neg, norm_one] at hx; norm_num at hx

theorem lam_exp_rep {lam x : ℕ → ℂ} {N : ℕ} (hl0 : lam 0 = 1)
    (hrec : ∀ k < N, lam (k + 1) = lam k * (1 + x k)) (hx : ∀ k < N, ‖x k‖ ≤ 1 / 2) :
    ∀ k ≤ N, lam k = Complex.exp (∑ i ∈ range k, Complex.log (1 + x i)) := by
  intro k hk
  induction k with
  | zero => rw [hl0, range_zero, sum_empty, Complex.exp_zero]
  | succ k ih =>
    rw [hrec k (by omega), ih (by omega), sum_range_succ, Complex.exp_add,
      Complex.exp_log (one_add_ne_zero_of_le (hx k (by omega)))]

variable {X : ℕ → Type*} [∀ j, NormedAddCommGroup (X j)] {F : HData X} {Λ β κ cg cm cT : ℝ}

/-- The `LogSum` conclusion at one trajectory `(b, μ₀)` (no domain hypothesis). -/
def LogSumAt (F : HData X) (Λ β cg : ℝ) (N : ℕ) (eR b μ₀ : ℝ) : Prop :=
  ∀ (y p a : ℕ → ℝ) (A σ : ℝ), 0 ≤ A → (∀ k, 0 ≤ a k) →
    (∀ k < N, |y (k + 1) - y k - (p (k + 1) - p k) + σ * (traj F Λ b μ₀ k).1| ≤
      A * (traj F Λ b μ₀ k).1 ^ 2 + A * (traj F Λ b μ₀ k).1 * a k) →
    ∀ n ≤ N, |y n - y 0 - (p n - p 0) + σ / β * Real.log ((traj F Λ b μ₀ n).1 / b)| ≤
      (logTrajK β cg A (|σ| / β) + A * ∑ k ∈ range n, a k + |σ| / β * (2 * (1 + β) * eR)) *
        (traj F Λ b μ₀ n).1

/-- The constant of `lamHat_near`. -/
def lamNearK (β cg B B' cq eR aS : ℝ) : ℝ :=
  ((logTrajK β cg (B + B' ^ 2) (1 / 3) + (B + B' ^ 2) * aS + 1 / 3 * (2 * (1 + β) * eR)) +
      (logTrajK β cg (B + B' ^ 2) 0 + (B + B' ^ 2) * aS) + 2 * cq) *
    Real.exp ((logTrajK β cg (B + B' ^ 2) (1 / 3) + (B + B' ^ 2) * aS +
      1 / 3 * (2 * (1 + β) * eR)) + (logTrajK β cg (B + B' ^ 2) 0 + (B + B' ^ 2) * aS) + 2 * cq)

set_option maxHeartbeats 1000000 in
/-- **The vertex along the flow, modulus and phase.** -/
theorem lamHat_nearD {N : ℕ} {ε eR : ℝ} {b μ₀ : ℝ} (LS : LogSumAt F Λ β cg N eR b μ₀) (hβ : 0 < β)
    (hε1 : ε ≤ 1) (hD : ∀ j ≤ N, InD3 Λ κ cm cT ε (traj F Λ b μ₀ j))
    {lam x q : ℕ → ℂ} {a : ℕ → ℝ} {B B' cq aS : ℝ} (hB : 0 ≤ B)
    (ha : ∀ k, 0 ≤ a k) (haS : ∑ k ∈ range N, a k ≤ aS)
    (hl0 : lam 0 = 1) (hrec : ∀ k < N, lam (k + 1) = lam k * (1 + x k))
    (hx2 : ∀ k < N, ‖x k‖ ≤ 1 / 2) (hxg : ∀ k < N, ‖x k‖ ≤ B' * (traj F Λ b μ₀ k).1)
    (hq0 : q 0 = 0) (hq : ∀ k ≤ N, ‖q k‖ ≤ cq * (traj F Λ b μ₀ k).1)
    (hx : ∀ k < N, ‖x k - ((β / 3 * (traj F Λ b μ₀ k).1 : ℝ) : ℂ) + (q (k + 1) - q k)‖ ≤
      B * (traj F Λ b μ₀ k).1 ^ 2 + B * (traj F Λ b μ₀ k).1 * a k) :
    ∀ n ≤ N, ‖lam n - ((((traj F Λ b μ₀ n).1 / b) ^ (1 / 3 : ℝ) : ℝ) : ℂ)‖ ≤
      lamNearK β cg B B' cq eR aS * ((traj F Λ b μ₀ n).1 / b) ^ (1 / 3 : ℝ) *
        (traj F Λ b μ₀ n).1 := by
  intro n hn
  set g : ℕ → ℝ := fun k => (traj F Λ b μ₀ k).1 with hgd
  have hg : ∀ k ≤ N, 0 < g k := fun k hk => (hD k hk).1
  have hg1 : ∀ k ≤ N, g k ≤ 1 := fun k hk => ((hD k hk).2.1).trans hε1
  have hb : 0 < b := by have := hg 0 (Nat.zero_le _); simpa [hgd, Hist.traj_zero] using this
  set A : ℝ := B + B' ^ 2 with hAd
  have hA : 0 ≤ A := by positivity
  set ℓ : ℕ → ℂ := fun k => ∑ i ∈ range k, Complex.log (1 + x i) with hℓd
  have hstep : ∀ k < N, ‖(Complex.log (1 + x k) - x k) +
      (x k - ((β / 3 * g k : ℝ) : ℂ) + (q (k + 1) - q k))‖ ≤ A * g k ^ 2 + A * g k * a k := by
    intro k hk
    refine (norm_add_le _ _).trans ?_
    have h1 := log_one_add_le (hx2 k hk)
    have h2 : ‖x k‖ ^ 2 ≤ (B' * g k) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hxg k hk) 2
    have h3 := hx k hk
    have h4 : 0 ≤ B' ^ 2 * g k * a k := by have := hg k hk.le; have := ha k; positivity
    have e : A * g k ^ 2 + A * g k * a k =
        (B' * g k) ^ 2 + (B * g k ^ 2 + B * g k * a k) + B' ^ 2 * g k * a k := by
      rw [hAd]; ring
    rw [e]
    simp only [hgd] at h2 h3 ⊢
    linarith
  have hsucc : ∀ k, ℓ (k + 1) - ℓ k = Complex.log (1 + x k) := fun k => by
    simp only [hℓd, sum_range_succ]; ring
  -- the real part
  have hre : ∀ k < N, |(ℓ (k + 1)).re - (ℓ k).re - ((-(q (k + 1)).re) - (-(q k).re)) +
      (-(β / 3)) * g k| ≤ A * g k ^ 2 + A * g k * a k := by
    intro k hk
    have e : (ℓ (k + 1)).re - (ℓ k).re - ((-(q (k + 1)).re) - (-(q k).re)) + (-(β / 3)) * g k =
        ((Complex.log (1 + x k) - x k) +
          (x k - ((β / 3 * g k : ℝ) : ℂ) + (q (k + 1) - q k))).re := by
      rw [← hsucc k]; simp; ring
    rw [e]; exact (Complex.abs_re_le_norm _).trans (hstep k hk)
  have him : ∀ k < N, |(ℓ (k + 1)).im - (ℓ k).im - ((-(q (k + 1)).im) - (-(q k).im)) +
      0 * g k| ≤ A * g k ^ 2 + A * g k * a k := by
    intro k hk
    have e : (ℓ (k + 1)).im - (ℓ k).im - ((-(q (k + 1)).im) - (-(q k).im)) + 0 * g k =
        ((Complex.log (1 + x k) - x k) +
          (x k - ((β / 3 * g k : ℝ) : ℂ) + (q (k + 1) - q k))).im := by
      rw [← hsucc k]; simp; ring
    rw [e]; exact (Complex.abs_im_le_norm _).trans (hstep k hk)
  have kre := LS (fun k => (ℓ k).re) (fun k => -(q k).re) a A (-(β / 3)) hA ha
    hre n hn
  have kim := LS (fun k => (ℓ k).im) (fun k => -(q k).im) a A 0 hA ha him n hn
  have hℓ0 : ℓ 0 = 0 := by simp [hℓd]
  have hsa : ∑ k ∈ range n, a k ≤ aS :=
    le_trans (sum_le_sum_of_subset_of_nonneg (range_subset_range.2 hn) (fun k _ _ => ha k)) haS
  have es : |(-(β / 3))| / β = 1 / 3 := by
    rw [abs_neg, abs_of_pos (by positivity)]; field_simp
  have es' : -(β / 3) / β = -(1 / 3) := by field_simp
  rw [es, es'] at kre
  simp only [hℓ0, hq0, Complex.zero_re, Complex.zero_im, neg_zero, sub_zero, abs_zero,
    zero_div, zero_mul, add_zero] at kre kim
  set K1 := logTrajK β cg A (1 / 3) + A * aS + 1 / 3 * (2 * (1 + β) * eR) with hK1
  set K2 := logTrajK β cg A 0 + A * aS with hK2
  have hgn := hg n hn
  have hAa : A * ∑ k ∈ range n, a k ≤ A * aS := mul_le_mul_of_nonneg_left hsa hA
  have kre' : |(ℓ n).re + (q n).re - 1 / 3 * Real.log (g n / b)| ≤ K1 * g n := by
    refine le_trans (le_of_eq ?_) (kre.trans (mul_le_mul_of_nonneg_right (by linarith) hgn.le))
    congr 1; simp only [hgd]; ring
  have kim' : |(ℓ n).im + (q n).im| ≤ K2 * g n := by
    have hlt : logTrajK β cg A 0 + A * ∑ k ∈ range n, a k ≤ K2 := by linarith
    refine le_trans (le_of_eq ?_) (kim.trans (mul_le_mul_of_nonneg_right hlt hgn.le))
    congr 1; ring
  -- the target
  set r : ℝ := (g n / b) ^ (1 / 3 : ℝ) with hrd
  have hr : 0 < r := Real.rpow_pos_of_pos (div_pos hgn hb) _
  have hlogr : Real.log r = 1 / 3 * Real.log (g n / b) := Real.log_rpow (div_pos hgn hb) _
  set w : ℂ := ℓ n - (Real.log r : ℂ) with hwd
  have hqn := hq n hn
  have hqre : |(q n).re| ≤ cq * g n := (Complex.abs_re_le_norm _).trans hqn
  have hqim : |(q n).im| ≤ cq * g n := (Complex.abs_im_le_norm _).trans hqn
  have hwre : |w.re| ≤ (K1 + cq) * g n := by
    have e : w.re = ((ℓ n).re + (q n).re - 1 / 3 * Real.log (g n / b)) - (q n).re := by
      rw [hwd, Complex.sub_re, Complex.ofReal_re, hlogr]; ring
    rw [e]; refine (abs_sub _ _).trans ?_; linarith
  have hwim : |w.im| ≤ (K2 + cq) * g n := by
    have e : w.im = ((ℓ n).im + (q n).im) - (q n).im := by
      rw [hwd, Complex.sub_im, Complex.ofReal_im]; ring
    rw [e]; refine (abs_sub _ _).trans ?_; linarith
  set Kw := K1 + K2 + 2 * cq with hKw
  have hw : ‖w‖ ≤ Kw * g n := by
    refine (Complex.norm_le_abs_re_add_abs_im w).trans ?_
    linarith
  have hKw0 : 0 ≤ Kw := by
    have := (norm_nonneg w).trans hw
    exact nonneg_of_mul_nonneg_left this hgn
  have hw1 : ‖w‖ ≤ Kw := hw.trans (mul_le_of_le_one_right hKw0 (hg1 n hn))
  have hlam : lam n = (r : ℂ) * Complex.exp w := by
    rw [lam_exp_rep hl0 hrec hx2 n hn]
    have : ∑ i ∈ range n, Complex.log (1 + x i) = w + (Real.log r : ℂ) := by
      rw [hwd]; simp only [hℓd]; ring
    rw [this, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hr, mul_comm]
  have hexp : ‖Complex.exp w - 1‖ ≤ ‖w‖ * Real.exp ‖w‖ := by
    have := Complex.norm_exp_sub_sum_le_norm_mul_exp w 1
    simpa using this
  rw [hlam]
  have e : (r : ℂ) * Complex.exp w - (r : ℂ) = (r : ℂ) * (Complex.exp w - 1) := by ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have h5 : ‖Complex.exp w - 1‖ ≤ Kw * g n * Real.exp Kw :=
    hexp.trans (mul_le_mul hw (Real.exp_le_exp.2 hw1) (Real.exp_pos _).le
      (mul_nonneg hKw0 hgn.le))
  have eK : lamNearK β cg B B' cq eR aS = Kw * Real.exp Kw := by
    rw [lamNearK, hKw, hK1, hK2, hAd]
  rw [eK]
  calc r * ‖Complex.exp w - 1‖ ≤ r * (Kw * g n * Real.exp Kw) :=
        mul_le_mul_of_nonneg_left h5 hr.le
    _ = Kw * Real.exp Kw * r * g n := by ring

/-- Corollary of `lamHat_nearD` (`Admissible` ⟹ the domain condition). -/
theorem lamHat_near {N : ℕ} {ε eR : ℝ} (LS : LogSum F Λ β κ cg cm cT N ε eR) (hβ : 0 < β)
    (hε1 : ε ≤ 1) {b μ₀ : ℝ} (hadm : Admissible F Λ κ cm cT N ε b μ₀)
    {lam x q : ℕ → ℂ} {a : ℕ → ℝ} {B B' cq aS : ℝ} (hB : 0 ≤ B)
    (ha : ∀ k, 0 ≤ a k) (haS : ∑ k ∈ range N, a k ≤ aS)
    (hl0 : lam 0 = 1) (hrec : ∀ k < N, lam (k + 1) = lam k * (1 + x k))
    (hx2 : ∀ k < N, ‖x k‖ ≤ 1 / 2) (hxg : ∀ k < N, ‖x k‖ ≤ B' * (traj F Λ b μ₀ k).1)
    (hq0 : q 0 = 0) (hq : ∀ k ≤ N, ‖q k‖ ≤ cq * (traj F Λ b μ₀ k).1)
    (hx : ∀ k < N, ‖x k - ((β / 3 * (traj F Λ b μ₀ k).1 : ℝ) : ℂ) + (q (k + 1) - q k)‖ ≤
      B * (traj F Λ b μ₀ k).1 ^ 2 + B * (traj F Λ b μ₀ k).1 * a k) :
    ∀ n ≤ N, ‖lam n - ((((traj F Λ b μ₀ n).1 / b) ^ (1 / 3 : ℝ) : ℝ) : ℂ)‖ ≤
      lamNearK β cg B B' cq eR aS * ((traj F Λ b μ₀ n).1 / b) ^ (1 / 3 : ℝ) *
        (traj F Λ b μ₀ n).1  :=
  lamHat_nearD (LS b μ₀ hadm) hβ hε1 hadm.1 hB ha haS hl0 hrec hx2 hxg hq0 hq hx

/-- The constant of `lamHat_of_rel`. -/
def lamRelK (β cg B B' cq cδ eR aS : ℝ) : ℝ := lamNearK β cg (B + 2 * cδ) (B' + 2 * cδ) cq eR aS

set_option maxHeartbeats 1000000 in
/-- **(H_λ)-type bound from the relative one-loop flow** of a coupling `β_k` and the one-loop
identification of `𝔫_k`. -/
theorem lamHat_of_relD {N : ℕ} {ε eR : ℝ} {b μ₀ : ℝ} (LS : LogSumAt F Λ β cg N eR b μ₀) (hβ : 0 < β)
    (hε1 : ε ≤ 1) (hD : ∀ j ≤ N, InD3 Λ κ cm cT ε (traj F Λ b μ₀ j))
    {bt nn q : ℕ → ℂ} {a : ℕ → ℝ} {B B' cq cδ aS : ℝ} (hB : 0 ≤ B) (hcδ : 0 ≤ cδ)
    (ha : ∀ k, 0 ≤ a k) (haS : ∑ k ∈ range N, a k ≤ aS)
    (hb0 : bt 0 ≠ 0)
    (hrel : ∀ k < N, ‖bt (k + 1) - bt k * (1 - nn k)‖ ≤
      cδ * (traj F Λ b μ₀ k).1 ^ 2 * ‖bt k * (1 - nn k)‖)
    (hsm : ∀ k < N, cδ * (traj F Λ b μ₀ k).1 ^ 2 ≤ 1 / 8)
    (hn8 : ∀ k < N, ‖nn k‖ ≤ 1 / 8) (hng : ∀ k < N, ‖nn k‖ ≤ B' * (traj F Λ b μ₀ k).1)
    (hq0 : q 0 = 0) (hq : ∀ k ≤ N, ‖q k‖ ≤ cq * (traj F Λ b μ₀ k).1)
    (hloop : ∀ k < N, ‖-nn k - ((β / 3 * (traj F Λ b μ₀ k).1 : ℝ) : ℂ) + (q (k + 1) - q k)‖ ≤
      B * (traj F Λ b μ₀ k).1 ^ 2 + B * (traj F Λ b μ₀ k).1 * a k) :
    ∀ n ≤ N, ‖bt n / bt 0 - ((((traj F Λ b μ₀ n).1 / b) ^ (1 / 3 : ℝ) : ℝ) : ℂ)‖ ≤
      lamRelK β cg B B' cq cδ eR aS * ((traj F Λ b μ₀ n).1 / b) ^ (1 / 3 : ℝ) *
        (traj F Λ b μ₀ n).1 := by
  set g : ℕ → ℝ := fun k => (traj F Λ b μ₀ k).1 with hgd
  have hg : ∀ k ≤ N, 0 < g k := fun k hk => (hD k hk).1
  have hg1 : ∀ k ≤ N, g k ≤ 1 := fun k hk => ((hD k hk).2.1).trans hε1
  -- one step: `β_{k+1} = β_k(1 - 𝔫_k)(1 + η_k)`, `‖η_k‖ ≤ c_δǧ_k²`
  have hstep : ∀ k < N, bt k ≠ 0 → bt (k + 1) ≠ 0 ∧
      ‖bt (k + 1) / bt k - 1 + nn k‖ ≤ 2 * cδ * g k ^ 2 := by
    intro k hk hbk
    have h1n : 1 - nn k ≠ 0 := by
      intro h0; have : nn k = 1 := by linear_combination -h0
      have := hn8 k hk; rw [‹nn k = 1›, norm_one] at this; norm_num at this
    have hu : bt k * (1 - nn k) ≠ 0 := mul_ne_zero hbk h1n
    have hr := hrel k hk
    have hs := hsm k hk
    refine ⟨fun h0 => ?_, ?_⟩
    · rw [h0, zero_sub, norm_neg] at hr
      have hpos : 0 < ‖bt k * (1 - nn k)‖ := norm_pos_iff.2 hu
      nlinarith
    · have e : bt (k + 1) / bt k - 1 + nn k = (bt (k + 1) - bt k * (1 - nn k)) / bt k := by
        field_simp; ring
      rw [e, norm_div]
      rw [div_le_iff₀ (norm_pos_iff.2 hbk)]
      refine hr.trans ?_
      rw [norm_mul]
      have h1 : ‖1 - nn k‖ ≤ 2 := by
        refine (norm_sub_le _ _).trans ?_; rw [norm_one]; linarith [hn8 k hk]
      have h2 : 0 ≤ cδ * g k ^ 2 := by positivity
      have := mul_le_mul_of_nonneg_left h1 (mul_nonneg h2 (norm_nonneg (bt k)))
      simp only [hgd] at this ⊢
      nlinarith [norm_nonneg (bt k)]
  have hne : ∀ k ≤ N, bt k ≠ 0 := by
    intro k hk
    induction k with
    | zero => exact hb0
    | succ k ih => exact (hstep k (by omega) (ih (by omega))).1
  set x : ℕ → ℂ := fun k => bt (k + 1) / bt k - 1 with hxd
  have hxn : ∀ k < N, ‖x k + nn k‖ ≤ 2 * cδ * g k ^ 2 := fun k hk =>
    (hstep k hk (hne k hk.le)).2
  have hx2 : ∀ k < N, ‖x k‖ ≤ 1 / 2 := by
    intro k hk
    have : x k = (x k + nn k) - nn k := by ring
    rw [this]; refine (norm_sub_le _ _).trans ?_
    have := hxn k hk; have := hn8 k hk; have := hsm k hk
    simp only [hgd] at *; linarith
  have hxg : ∀ k < N, ‖x k‖ ≤ (B' + 2 * cδ) * g k := by
    intro k hk
    have e : x k = (x k + nn k) - nn k := by ring
    rw [e]; refine (norm_sub_le _ _).trans ?_
    have h1 := hxn k hk; have h2 := hng k hk
    have hgk := hg k hk.le; have hgk1 := hg1 k hk.le
    have h3 : 2 * cδ * g k ^ 2 ≤ 2 * cδ * g k := by
      have : g k ^ 2 ≤ g k := by rw [sq]; exact mul_le_of_le_one_right hgk.le hgk1
      exact mul_le_mul_of_nonneg_left this (by positivity)
    simp only [hgd] at *; linarith
  have hrec : ∀ k < N, bt (k + 1) / bt 0 = bt k / bt 0 * (1 + x k) := by
    intro k hk
    simp only [hxd]; field_simp [hne k hk.le, hb0]; ring
  have hxl : ∀ k < N, ‖x k - ((β / 3 * g k : ℝ) : ℂ) + (q (k + 1) - q k)‖ ≤
      (B + 2 * cδ) * g k ^ 2 + (B + 2 * cδ) * g k * a k := by
    intro k hk
    have e : x k - ((β / 3 * g k : ℝ) : ℂ) + (q (k + 1) - q k) =
        (x k + nn k) + (-nn k - ((β / 3 * g k : ℝ) : ℂ) + (q (k + 1) - q k)) := by ring
    rw [e]; refine (norm_add_le _ _).trans ?_
    have h1 := hxn k hk; have h2 := hloop k hk
    have h3 : 0 ≤ 2 * cδ * g k * a k := by have := hg k hk.le; have := ha k; positivity
    simp only [hgd] at *; nlinarith
  exact lamHat_nearD LS hβ hε1 hD (lam := fun k => bt k / bt 0) (x := x) (q := q) (a := a)
    (by positivity) ha haS (div_self hb0) hrec hx2 hxg hq0 hq hxl

/-! ### Along the admissible trajectories of the master construction -/

/-- **(H_λ) from the relative one-loop flow**, for given constants: along every admissible
trajectory, every coupling sequence `β_k` with the relative flow and the one-loop identification of
`𝔫_k` gives `HLam` for `λ̂_k = β_k/β_0`. -/
def LamConcl (L : ℕ) [NeZero L] (ℓ A ρ κ cg cm cT ε Ke : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ → 1 ≤ N →
  ∀ Nh : ℕ, Nh + 2 ≤ N →
  ∀ m ∈ mRange L N, ∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
  ∀ (bt nn q : ℕ → ℂ) (B B' cq cδ : ℝ), 0 ≤ B → 0 ≤ cδ → bt 0 ≠ 0 →
    (∀ k < Nh, ‖bt (k + 1) - bt k * (1 - nn k)‖ ≤
      cδ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ^ 2 * ‖bt k * (1 - nn k)‖) →
    (∀ k < Nh, cδ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ^ 2 ≤ 1 / 8) →
    (∀ k < Nh, ‖nn k‖ ≤ 1 / 8) →
    (∀ k < Nh, ‖nn k‖ ≤ B' * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1) →
    q 0 = 0 → (∀ k ≤ Nh, ‖q k‖ ≤ cq * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1) →
    (∀ k < Nh, ‖-nn k - ((betaL L / 3 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 : ℝ) : ℂ) +
        (q (k + 1) - q k)‖ ≤ B * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ^ 2 +
          B * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 * zA L m k) →
    HLam R Nh m b μ₀ (fun k => bt k / bt 0)
      (lamRelK (betaL L) cg B B' cq cδ (eRange (betaL L) Ke 1) 4)

/-- The conclusion of `LamConcl` at one trajectory `(b, μ₀)`. -/
def LamConclAt (L : ℕ) [NeZero L] (cg Ke : ℝ) {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)]
    [Fact (0 < R.A)] (Nh : ℕ) (m b μ₀ : ℝ) : Prop :=
  ∀ (bt nn q : ℕ → ℂ) (B B' cq cδ : ℝ), 0 ≤ B → 0 ≤ cδ → bt 0 ≠ 0 →
    (∀ k < Nh, ‖bt (k + 1) - bt k * (1 - nn k)‖ ≤
      cδ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ^ 2 * ‖bt k * (1 - nn k)‖) →
    (∀ k < Nh, cδ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ^ 2 ≤ 1 / 8) →
    (∀ k < Nh, ‖nn k‖ ≤ 1 / 8) →
    (∀ k < Nh, ‖nn k‖ ≤ B' * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1) →
    q 0 = 0 → (∀ k ≤ Nh, ‖q k‖ ≤ cq * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1) →
    (∀ k < Nh, ‖-nn k - ((betaL L / 3 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 : ℝ) : ℂ) +
        (q (k + 1) - q k)‖ ≤ B * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ^ 2 +
          B * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 * zA L m k) →
    HLam R Nh m b μ₀ (fun k => bt k / bt 0)
      (lamRelK (betaL L) cg B B' cq cδ (eRange (betaL L) Ke 1) 4)

/-- **(H_λ) from the relative one-loop flow at one trajectory in `D_ε`** (the body of
`lamConcl_of`; only the domain condition and `LogSum` at this trajectory are used). -/
theorem lamConcl_at {L : ℕ} [NeZero L] {κ cg cm cT ε Ke : ℝ} (hL2 : (2 : ℝ) ≤ L) (hε1 : ε ≤ 1)
    {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {Nh : ℕ} (hNh : Nh + 2 ≤ N)
    {m : ℝ} (hm : m ∈ mRange L N) {b μ₀ : ℝ}
    (hLS : LogSumAt (rgDataM R m) ((L : ℝ) ^ 2) (betaL L) cg Nh (eRange (betaL L) Ke 1) b μ₀)
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) :
    LamConclAt L cg Ke R Nh m b μ₀ := by
  intro bt nn q B B' cq cδ hB hcδ hb0 hrel hsm hn8 hng hq0 hq hloop k hk
  have hmn : m * ((L : ℝ) ^ Nh) ^ 2 ≤ 1 := by
    have h1 := msq_horizon (L := (L : ℝ)) (by linarith only [hL2]) hm.2 (Nh := Nh) (k := 0)
      (by omega)
    simp only [pow_zero, one_pow, inv_one] at h1
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hm.1.le) h1
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by linarith only [hL2]) (by omega)) 2
  have hsa : ∑ k ∈ range Nh, zA L m k ≤ 4 := by
    have := sum_zA_le (Ln := L) rfl hL2 hm.1.le Nh
    linarith only [this, hmn]
  have hβ : 0 < betaL L := by
    unfold betaL
    have : 0 < Real.log L := Real.log_pos (by linarith only [hL2])
    have := Real.pi_pos
    positivity
  have key := lamHat_of_relD hLS hβ hε1 hD hB hcδ (zA_nonneg L hm.1.le) hsa hb0
    hrel hsm hn8 hng hq0 hq hloop k hk.le
  refine key.trans (mul_le_mul_of_nonneg_left ?_ ?_)
  · have := zA_nonneg L hm.1.le k; linarith
  · have hgk := (hD k hk.le).1
    have hb : 0 < b := by
      have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
    have h0 : 0 ≤ lamRelK (betaL L) cg B B' cq cδ (eRange (betaL L) Ke 1) 4 := by
      have := (norm_nonneg _).trans key
      have hr : 0 < ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 / b) ^ (1 / 3 : ℝ) *
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 :=
        mul_pos (Real.rpow_pos_of_pos (div_pos hgk hb) _) hgk
      rw [mul_assoc] at this
      exact nonneg_of_mul_nonneg_left this hr
    exact mul_nonneg h0 (Real.rpow_nonneg (div_pos hgk hb).le _)

/-- **`LamConcl` from `SpinConcl`** (the `LogSum` of the master construction). -/
theorem lamConcl_of {L : ℕ} [NeZero L] {ℓ A ρ κ cg cm cT ε Ke KZ KG : ℝ} (hL2 : (2 : ℝ) ≤ L)
    (hε1 : ε ≤ 1) (h : SpinConcl L ℓ A ρ κ cg cm cT ε Ke KZ KG) :
    LamConcl L ℓ A ρ κ cg cm cT ε Ke := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm
  obtain ⟨-, -, hLS, -⟩ := h N R hP hi0 hRℓ hRA hRρ hN Nh hNh
  exact lamConcl_at hL2 hε1 R hNh hm (hLS m hm b μ₀ hadm) hadm.1

/-- `LamConcl` along every trajectory in `D_ε` up to `N_h` (route (a1)). -/
def LamConclD (L : ℕ) [NeZero L] (ℓ A ρ κ cg cm cT ε Ke : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ → 1 ≤ N →
  ∀ Nh : ℕ, Nh + 2 ≤ N →
  ∀ m ∈ mRange L N, ∀ b μ₀,
    (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) →
    LamConclAt L cg Ke R Nh m b μ₀

end

end Spin2
