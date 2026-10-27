import Step2.Flow.ZetaSharp6
import Step2.Flow.ZetaSharp0

/-!
# `prop:gamma`: the observable vertices along the flow (abstract, conditional form)

The observable couplings in raw fields are the bare vertices `λ^{(1)}`, `λ^{(2)}` (the
observables are not rescaled by the field strength, `Obs2/Flow/Hist.lean`). Their flow equations
(`h02uv-outline.tex`, Section "Flow equations", from `Obs2/Flow/FlowMu.lean` and the Wick evaluation
of `m(S(B_+)_a)`) have the multiplicative form

  `λ_{k+1} = λ_k (1 + x_k)`,  `Re x_k = s (β/3) ǧ_k - (q_{k+1} - q_k) + O(ǧ_k² + ǧ_k a_k)`,

with `s = 0` (Case 1: `x = -𝔫_k + O(ḡ²)`, `q = n/4`) resp. `s = 1` (Case 2:
`x = g^♭𝔩_k - 2𝔫_k + O(ḡ²)`, `𝔩_k = log L/2π + O(a_k + ǧ_k)`, `q = n/2`), where `n_k = 4ν_k w⁽¹⁾_k`
is the telescoping coordinate change and the `O(ḡ²)` contains the `K^{obs}`, `𝒲^{obs}` remainders.
These remainders are bounded elsewhere (`Obs2/Est/`, `Obs2/ObsFlow*`); here the bound is a
hypothesis.

* `lam_step`: `log|λ_{k+1}| - log|λ_k| = Re x_k + O(|x_k|²)` (`|x_k| ≤ 1/4`);
* `lam_ratio`: given the summation principle `LogSum` of the bulk flow
  (`Step2.thm_flow_final_Z`) and the hypotheses above (`q_0 = 0`, `|q_k| ≤ c_q ǧ_k`,
  `|x_k| ≤ B' ǧ_k`),
  `|log(|λ_n|/|λ_0|) - (s/3) log(ǧ_n/b)| ≤ K ǧ_n`, i.e.
  `|λ_n/λ_0| = (β_ε/β_n)^{s/3} e^{O(β_n^{-1})}`;
* `theta_one`: the spin renormalisation of Case 1, `ϑ^{(1)} = (β_n/(β_ε |Z|))^{1/2} |λ^{(1)}_n/λ^{(1)}_0|`,
  is `(β_n/β_ε)^{1/3} e^{O(β_n^{-1})}` given `|Z| = (β_n/β_ε)^{1/3} e^{O(β_n^{-1})}` and
  `|λ^{(1)}_n/λ^{(1)}_0| = e^{O(β_n^{-1})}`.
-/

open Finset

namespace Obs2

/-- One multiplicative step: `|log|l'| - log|l| - Re x| ≤ 7|x|²`. -/
theorem lam_step {l l' x : ℂ} (hl : l ≠ 0) (h : l' = l * (1 + x)) (hx : ‖x‖ ≤ 1 / 4) :
    l' ≠ 0 ∧ |Real.log ‖l'‖ - Real.log ‖l‖ - x.re| ≤ 7 * ‖x‖ ^ 2 := by
  have h1 : 1 + x ≠ 0 := by
    intro h0
    have : x = -1 := by linear_combination h0
    rw [this, norm_neg, norm_one] at hx; norm_num at hx
  refine ⟨h ▸ mul_ne_zero hl h1, ?_⟩
  rw [h, norm_mul, Real.log_mul (norm_ne_zero_iff.2 hl) (norm_ne_zero_iff.2 h1)]
  have := Step2.log_norm_one_add hx
  have e : Real.log ‖l‖ + Real.log ‖1 + x‖ - Real.log ‖l‖ - x.re = Real.log ‖1 + x‖ - x.re := by
    ring
  rw [e]; exact this

theorem lam_ne_zero {lam x : ℕ → ℂ} {N : ℕ} (hl0 : lam 0 ≠ 0)
    (hrec : ∀ k < N, lam (k + 1) = lam k * (1 + x k)) (hx4 : ∀ k < N, ‖x k‖ ≤ 1 / 4) :
    ∀ k ≤ N, lam k ≠ 0 := by
  intro k hk
  induction k with
  | zero => exact hl0
  | succ k ih => exact (lam_step (ih (by omega)) (hrec k (by omega)) (hx4 k (by omega))).1

open Flow2.Hist in
/-- **The ratio of an observable vertex along the flow** (conditional on the per-step remainder
bound). -/
theorem lam_ratio {X : ℕ → Type*} [∀ j, NormedAddCommGroup (X j)] {F : HData X}
    {Λ β κ cg cm cT ε eR : ℝ} {N : ℕ} (LS : LogSum F Λ β κ cg cm cT N ε eR) (hβ : 0 < β)
    {b μ₀ : ℝ} (hadm : Admissible F Λ κ cm cT N ε b μ₀)
    {lam x : ℕ → ℂ} {q a : ℕ → ℝ} {s B B' cq : ℝ} (hB : 0 ≤ B) (ha : ∀ k, 0 ≤ a k)
    (hl0 : lam 0 ≠ 0) (hrec : ∀ k < N, lam (k + 1) = lam k * (1 + x k))
    (hx4 : ∀ k < N, ‖x k‖ ≤ 1 / 4) (hxg : ∀ k < N, ‖x k‖ ≤ B' * (traj F Λ b μ₀ k).1)
    (hq0 : q 0 = 0) (hq : ∀ k ≤ N, |q k| ≤ cq * (traj F Λ b μ₀ k).1)
    (hre : ∀ k < N, |(x k).re - s * (β / 3) * (traj F Λ b μ₀ k).1 + (q (k + 1) - q k)| ≤
      B * (traj F Λ b μ₀ k).1 ^ 2 + B * (traj F Λ b μ₀ k).1 * a k) :
    ∀ n ≤ N, |Real.log (‖lam n‖ / ‖lam 0‖) - s / 3 * Real.log ((traj F Λ b μ₀ n).1 / b)| ≤
      (logTrajK β cg (B + 7 * B' ^ 2) (|s| / 3) + (B + 7 * B' ^ 2) * ∑ k ∈ range n, a k +
        |s| / 3 * (2 * (1 + β) * eR) + cq) * (traj F Λ b μ₀ n).1 := by
  -- nonvanishing
  have hne := lam_ne_zero hl0 hrec hx4
  have hy : ∀ k < N, |Real.log ‖lam (k + 1)‖ - Real.log ‖lam k‖ - ((-q (k + 1)) - (-q k)) +
      (-(s * β / 3)) * (traj F Λ b μ₀ k).1| ≤ (B + 7 * B' ^ 2) * (traj F Λ b μ₀ k).1 ^ 2 + (B + 7 * B' ^ 2) * (traj F Λ b μ₀ k).1 * a k := by
    intro k hk
    have h1 := (lam_step (hne k hk.le) (hrec k hk) (hx4 k hk)).2
    have h2 := hre k hk
    have hx2 : ‖x k‖ ^ 2 ≤ (B' * (traj F Λ b μ₀ k).1) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hxg k hk) 2
    have e : Real.log ‖lam (k + 1)‖ - Real.log ‖lam k‖ - ((-q (k + 1)) - (-q k)) +
        (-(s * β / 3)) * (traj F Λ b μ₀ k).1 = (Real.log ‖lam (k + 1)‖ - Real.log ‖lam k‖ - (x k).re) +
          ((x k).re - s * (β / 3) * (traj F Λ b μ₀ k).1 + (q (k + 1) - q k)) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    have h3 : 0 ≤ 7 * B' ^ 2 * (traj F Λ b μ₀ k).1 * a k := by
      have : 0 < (traj F Λ b μ₀ k).1 := (hadm.1 k hk.le).1
      have := ha k
      positivity
    have e2 : (B + 7 * B' ^ 2) * (traj F Λ b μ₀ k).1 ^ 2 + (B + 7 * B' ^ 2) * (traj F Λ b μ₀ k).1 * a k =
        7 * (B' * (traj F Λ b μ₀ k).1) ^ 2 + (B * (traj F Λ b μ₀ k).1 ^ 2 + B * (traj F Λ b μ₀ k).1 * a k) + 7 * B' ^ 2 * (traj F Λ b μ₀ k).1 * a k := by ring
    rw [e2]
    linarith only [h1, h2, hx2, h3]
  have hA : 0 ≤ B + 7 * B' ^ 2 := by positivity
  intro n hn
  have key := LS b μ₀ hadm (fun k => Real.log ‖lam k‖) (fun k => -q k) a (B + 7 * B' ^ 2)
    (-(s * β / 3)) hA ha hy n hn
  have hβne : β ≠ 0 := hβ.ne'
  have es : |-(s * β / 3)| / β = |s| / 3 := by
    rw [abs_neg, abs_div, abs_mul, abs_of_pos hβ, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    field_simp
  have es' : -(s * β / 3) / β = -(s / 3) := by field_simp
  rw [es, es'] at key
  simp only [hq0, neg_zero, sub_zero] at key
  have hlog : Real.log (‖lam n‖ / ‖lam 0‖) = Real.log ‖lam n‖ - Real.log ‖lam 0‖ :=
    Real.log_div (norm_ne_zero_iff.2 (hne n hn)) (norm_ne_zero_iff.2 hl0)
  rw [hlog]
  have hqn := hq n hn
  have e : Real.log ‖lam n‖ - Real.log ‖lam 0‖ - s / 3 * Real.log ((traj F Λ b μ₀ n).1 / b) =
      (Real.log ‖lam n‖ - Real.log ‖lam 0‖ - -q n + -(s / 3) * Real.log ((traj F Λ b μ₀ n).1 / b)) - q n := by
    ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  have e2 : (logTrajK β cg (B + 7 * B' ^ 2) (|s| / 3) + (B + 7 * B' ^ 2) * ∑ k ∈ range n, a k +
        |s| / 3 * (2 * (1 + β) * eR) + cq) * (traj F Λ b μ₀ n).1 =
      (logTrajK β cg (B + 7 * B' ^ 2) (|s| / 3) + (B + 7 * B' ^ 2) * ∑ k ∈ range n, a k +
        |s| / 3 * (2 * (1 + β) * eR)) * (traj F Λ b μ₀ n).1 + cq * (traj F Λ b μ₀ n).1 := by ring
  rw [e2]
  exact add_le_add key hqn

/-- **The spin renormalisation of Case 1**: with `z = |Z|`, `ℓ₁ = |λ^{(1)}_n/λ^{(1)}_0|`,
`r = b/ǧ_n = β_n/β_ε`: if `|log z - (1/3) log r| ≤ K_Z ǧ` and `|log ℓ₁| ≤ K_1 ǧ`, then
`ϑ = (r/z)^{1/2} ℓ₁` satisfies `|log ϑ - (1/3) log r| ≤ (K_Z/2 + K_1) ǧ`. -/
theorem theta_one {z l r g KZ K1 : ℝ} (hz : 0 < z) (hl : 0 < l) (hr : 0 < r)
    (hZ : |Real.log z - 1 / 3 * Real.log r| ≤ KZ * g) (h1 : |Real.log l| ≤ K1 * g) :
    |Real.log (Real.sqrt (r / z) * l) - 1 / 3 * Real.log r| ≤ (KZ / 2 + K1) * g := by
  have hs : Real.log (Real.sqrt (r / z)) = (Real.log r - Real.log z) / 2 := by
    rw [Real.log_sqrt (div_pos hr hz).le, Real.log_div hr.ne' hz.ne']
  rw [Real.log_mul (Real.sqrt_pos.2 (div_pos hr hz)).ne' hl.ne', hs]
  have e : (Real.log r - Real.log z) / 2 + Real.log l - 1 / 3 * Real.log r =
      -((Real.log z - 1 / 3 * Real.log r) / 2) + Real.log l := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg, abs_div, abs_two]
  have e2 : (KZ / 2 + K1) * g = KZ * g / 2 + K1 * g := by ring
  rw [e2]
  linarith only [hZ, h1]

end Obs2
