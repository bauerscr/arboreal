import Obs2.Flow.MuHist
import Step2.Flow.FlowStep

/-!
# The fields `htau` and `hdrift` of `MuErr` along the history

* `sum_row_eq_zero_mode`: for a symmetric translation-invariant covariance,
  `∑_z C(a,z) = ∑_x C(x,0)`.
* **`norm_tauC_le`**: if `C` has `GoodCov2 k ℓ` (range `L^{k+1}/2`, `k + 1 < N`), is symmetric and
  translation invariant, and `Γ` has `GoodCov2 j ℓ` with the lattice symmetries
  (`Γ(x,x) = c₀`, `Γ(x ± e, x) = c₀ + δ`), then for `k ≤ j`
  `|τ(C, Γ)(a)| ≤ 18 ℓ⁴ (L^{-2})^{j-k}`. By `tauC_TI`, `τ = 2dδ ∑_z C(a,z)`, with
  `|δ| ≤ ℓ²/(2L^{2(j+1)})` (`cov_c0_delta_le`) and `|∑_z C(a,z)| ≤ 9 L^{2(k+1)} ℓ²`
  (`zero_mode_le`).
* **`histCovO_htau`**: the field `htau` of `MuErr` along every history, with `B = 18 ℓ_M⁴`,
  `q = L^{-2}` and `ℓ_M = ellM R n t` the common Gram scale of the steps `≤ n`.
* `drift_of_step`: the field `hdrift` from a per-step bound on `β_k g'_k`
  (`|β_{i+1}g'_{i+1} - β_i g'_i| ≤ A` for `k ≤ i < j` gives `|β_k g'_k - β_j g'_j| ≤ A(j-k)`).
* **`muErr_hist`**: `MuErr` along the history from `hK`, `hP` and the per-step drift bound.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 LocObs FRD Flow2

section Cov

variable {L N : ℕ} [NeZero L]

theorem sum_row_eq_zero_mode {C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ} (hT : TInv C)
    (hs : ∀ x y, C x y = C y x) (a : Lam 2 L N) : ∑ z, C a z = ∑ x, C x 0 := by
  rw [← Equiv.sum_comp (Equiv.addRight a)]
  refine sum_congr rfl fun x _ => ?_
  have h := hT a x 0
  rw [zero_add] at h
  simp only [Equiv.coe_addRight]
  rw [hs, h]

/-- **The tadpole between scales**: `|τ(C_k, Γ_j)(a)| ≤ 18 ℓ⁴ (L^{-2})^{j-k}`. -/
theorem norm_tauC_le {j k : ℕ} (hk : k ≤ j) (hkN : k + 1 < N) {ℓ : ℝ}
    {C Γ : Matrix (Lam 2 L N) (Lam 2 L N) ℂ} (hC : GoodCov2 k ℓ C) (hT : TInv C)
    (hs : ∀ x y, C x y = C y x) (hΓ : GoodCov2 j ℓ Γ) {c₀ δ : ℂ} (hc : ∀ x, Γ x x = c₀)
    (hδ : ∀ x e, Γ (x + dirVec e) x = c₀ + δ) (hδ' : ∀ x e, Γ x (x + dirVec e) = c₀ + δ)
    (a : Lam 2 L N) :
    ‖tauC C Γ a‖ ≤ 18 * ℓ ^ 4 * (((L : ℝ) ^ 2)⁻¹) ^ (j - k) := by
  rw [tauC_TI C Γ a c₀ δ hc hδ hδ', sum_row_eq_zero_mode hT hs]
  have hz := zero_mode_le hkN hC
  have hd := (cov_c0_delta_le hΓ hc hδ hδ').2
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_sub_cancel_left]
  have e4 : ‖(2 : ℂ) * ((2 : ℕ) : ℂ) * δ * ∑ x, C x 0‖ = 4 * ‖δ‖ * ‖∑ x, C x 0‖ := by
    rw [norm_mul, norm_mul, norm_mul]
    norm_num
  rw [e4]
  have hA : (0 : ℝ) < ((L : ℝ) ^ (k + m + 1)) ^ 2 := by positivity
  have hpow : ((L : ℝ) ^ (k + m + 1)) ^ 2 = ((L : ℝ) ^ (k + 1)) ^ 2 * ((L : ℝ) ^ 2) ^ m := by
    rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring
  have hq : (((L : ℝ) ^ 2)⁻¹) ^ m = ((L : ℝ) ^ (k + 1)) ^ 2 / ((L : ℝ) ^ (k + m + 1)) ^ 2 := by
    rw [hpow, inv_pow]
    field_simp
  rw [hq]
  calc 4 * ‖δ‖ * ‖∑ x, C x 0‖
      ≤ 4 * (ℓ ^ 2 / (2 * ((L : ℝ) ^ (k + m + 1)) ^ 2)) * (9 * ((L : ℝ) ^ (k + 1)) ^ 2 * ℓ ^ 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hd (by norm_num)) hz (norm_nonneg _)
          (by positivity)
    _ = 18 * ℓ ^ 4 * (((L : ℝ) ^ (k + 1)) ^ 2 / ((L : ℝ) ^ (k + m + 1)) ^ 2) := by
        field_simp; ring

end Cov

/-- **The drift from a per-step bound**: if `|x_{i+1} - x_i| ≤ A` for `k ≤ i < j`, then
`|x_k - x_j| ≤ A (j - k)`. -/
theorem drift_of_step {x : ℕ → ℂ} {A : ℝ} {k j : ℕ} (hkj : k ≤ j)
    (h : ∀ i, k ≤ i → i < j → ‖x (i + 1) - x i‖ ≤ A) : ‖x k - x j‖ ≤ A * (j - k : ℕ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkj
  rw [Nat.add_sub_cancel_left]
  induction m with
  | zero => simp
  | succ m ih =>
    have ih' := ih (by omega) fun i hi hi' => h i hi (by omega)
    have hs := h (k + m) (by omega) (by omega)
    calc ‖x k - x (k + (m + 1))‖ = ‖(x k - x (k + m)) - (x (k + m + 1) - x (k + m))‖ := by
          rw [← add_assoc]; congr 1; ring
      _ ≤ ‖x k - x (k + m)‖ + ‖x (k + m + 1) - x (k + m)‖ := norm_sub_le _ _
      _ ≤ A * (m : ℕ) + A := add_le_add ih' hs
      _ = A * ((m + 1 : ℕ) : ℝ) := by push_cast; ring

section Hist

variable {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  (P : ObsPts 2 L N) (o₀ : ObsSt .one L N) (t : Hist.Seq (Xs R)) {n : ℕ}

/-- The covariance properties of the step `i ≤ n` of the history, at the common scale
`ellM R n t`. -/
theorem histCovO_props (hV : ∀ i < n, ValidAt R i) (hVL : ValidAtL R n) {i : ℕ} (hi : i ≤ n) :
    GoodCov2 i (ellM R n t) (histCovO R t i) ∧ TInv (histCovO R t i) ∧
      CSym (histCovO R t i) ∧ ∀ x y, histCovO R t i x y = histCovO R t i y x := by
  have hG := histFS_goodU R hV hVL t i
  rw [histFS_C R t hi] at hG
  have H := rawInv_histU R hV hVL t i (by omega)
  obtain ⟨-, hT, hCs, hs⟩ := covU R hV hVL hi H
  exact ⟨hG, hT, hCs, hs⟩

/-- **The field `htau` of `MuErr` along the history**: for `k < j ≤ n < N`,
`|τ(C_k, C_j)(a)| ≤ 18 ℓ_M⁴ (L^{-2})^{j-k}`. -/
theorem histCovO_htau (hN : n < N) (hV : ∀ i < n, ValidAt R i) (hVL : ValidAtL R n) {j : ℕ}
    (hj : j ≤ n) : ∀ k < j, ‖tauC (histCovO R t k) (histCovO R t j) P.a‖ ≤
      18 * ellM R n t ^ 4 * (((L : ℝ) ^ 2)⁻¹) ^ (j - k) := by
  intro k hk
  obtain ⟨hCk, hTk, -, hsk⟩ := histCovO_props R t hV hVL (i := k) (by omega)
  obtain ⟨hCj, -, hCsj, hsj⟩ := histCovO_props R t hV hVL hj
  obtain ⟨c₀, δ, hc, hδ, hδ'⟩ := covProps (by norm_num) hCsj hsj
  exact norm_tauC_le hk.le (by omega) hCk hTk hsk hCj hc hδ hδ' P.a

/-- **`MuErr` along the history** from the activity bound `hK`, the product bound `hP` and a
per-step bound `A` on `β_k g'_k`; `B = 18 ℓ_M⁴`, `q = L^{-2}` (`L ≥ 2`). -/
theorem muErr_hist (hN : n < N) (hV : ∀ i < n, ValidAt R i) (hVL : ValidAtL R n) (hL : 2 ≤ L)
    (κ : ℕ → Step2.Coup) {j : ℕ} (hj : j ≤ n) {EK A EP : ℝ} (hA : 0 ≤ A)
    (hK : ‖∑ X ∈ smallSets (L := L) (N := N) j,
      mass1 (-1) (histKO R P o₀ t j X : SA .one (Lam 2 L N)).a‖ ≤ EK)
    (hstep : ∀ i < j, ‖betaTot (L := L) (N := N) (i + 1) (histVO R P o₀ t (i + 1)) * (κ (i + 1)).g -
      betaTot (L := L) (N := N) i (histVO R P o₀ t i) * (κ i).g‖ ≤ A)
    (hP : ‖wTad j (mass1L (-1)) (histWO R P o₀ t j) 0 +
      muProdInc P (histCovO R t) (histVO R P o₀ t) (histWO R P o₀ t) j‖ ≤ EP) :
    MuErr P (histCovO R t) (histVO R P o₀ t) (histWO R P o₀ t) (histKO R P o₀ t) κ j
      EK A (18 * ellM R n t ^ 4) (((L : ℝ) ^ 2)⁻¹) EP where
  hA := hA
  hB := by positivity
  hq0 := by positivity
  hq := by
    have : (1 : ℝ) < (L : ℝ) ^ 2 := by
      have : (2 : ℝ) ≤ L := by exact_mod_cast hL
      nlinarith
    exact inv_lt_one_of_one_lt₀ this
  hK := hK
  hdrift := fun k hk => drift_of_step (x := fun i => betaTot (L := L) (N := N) i (histVO R P o₀ t i) *
    (κ i).g) hk.le fun i _ hi => hstep i hi
  htau := histCovO_htau R P t hN hV hVL hj
  hP := hP

end Hist

end

end Obs2
