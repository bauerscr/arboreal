import DressedFRD.LipStep
import DressedFRD.MainFull

/-!
# Lipschitz dependence of `C'_{j+1}` on the couplings, with geometric decay

`C'_{j+1}(ζ) = Z_{j+1}(ζ) Γ^int_{j+1}(ζ)` is the normalised dressed covariance.

`lip_decay`: for every ratio `0 < ρ ≤ 1/2` there are `ζ̄ > 0` and `K` such that, for two coupling
sequences `ζ`, `ζ'` with `|ζ_i|, |ζ'_i| ≤ ζ̄/2` and `j + 1 < N`,
`‖C'_{j+1}(ζ) - C'_{j+1}(ζ')‖_{(j)} ≤ K ∑_{k ≤ j} ρ^{j-k} |ζ_k - ζ'_k|`.
`lip_decay_full` is the same under (S1)–(S5) (`StdFull`).

Consequences (`lip_decay_kern`): with `B_j = K ∑_{k ≤ j} ρ^{j-k} |ζ_k - ζ'_k|` and
`δC = C'_{j+1}(ζ) - C'_{j+1}(ζ')`,
* `|∇^α δC(x)| ≤ L^{-j(d-2+|α|)} B_j` for `|α| ≤ q` (kernel, with lattice derivatives);
* `2 rng δC < L^{j+1}` (finite range);
* `|δC^(p)| ≤ L^d L^{2j} B_j` for every momentum `p`; in particular the zero mode
  `∑_x δC(x) = δC^(0)`.

The proof (`DressedFRD/LipStep.lean`) controls `Δ_i = ∑_{r>i} W_{r-i} ‖W_i(r) - W'_i(r)‖_{(r-1)}`,
`W_i(r) = Z_i R_{i,r}`, by the recursion `Δ_{i+1} ≤ (θ^{6/256} + 4 C_ρ K₁ θ) Δ_i + 4 K₁ |ζ_i - ζ'_i|`
(`Dlt_succ_le`, `Elt_le`). The step bound uses the Schwarz lemma for the one-step map in the
variables `(ζ_i, W_i)` (`sum_lip_of_hol`).
-/

namespace DressedFRD

noncomputable section

open Finset Grassmann FRD

variable {d n : ℕ} [NeZero n]

namespace Data

variable {D : Data d n} {ζ' : ℕ → ℂ} {q : ℕ} {c₂ θ : ℝ}

/-- The contraction ratio `θ^{6/256} + 4 C_ρ K₁ θ`. -/
def rhoL (D : Data d n) (q : ℕ) (c₂ θ : ℝ) : ℝ :=
  θ ^ ((6 : ℝ) / 256) + 4 * (Crho d D.L * K1 D.L (cexp d q) c₂ θ * θ)

theorem rhoL_nonneg (h : D.LipHyp ζ' q c₂ θ) (hN : 0 < D.N) : 0 ≤ D.rhoL q c₂ θ := by
  have hθ := h.good.pos
  have hL0 : (0 : ℝ) < D.L := by exact_mod_cast (by have := h.hL; omega : 0 < D.L)
  have hc₂ : 0 ≤ c₂ := le_trans (snorm_nonneg hL0 _) (h.loc 0 hN)
  have := K1_nonneg (L := (D.L : ℝ)) (c := cexp d q) hL0.le hc₂ hθ.le
  have := Crho_nonneg d hL0.le
  have := Real.rpow_nonneg hθ.le ((6 : ℝ) / 256)
  unfold rhoL; positivity

/-- `Δ_i ≤ 4 K₁ ∑_{k < i} ρ^{i-1-k} |ζ_k - ζ'_k|`. -/
theorem Dlt_le (h : D.LipHyp ζ' q c₂ θ) :
    ∀ i, i ≤ D.N → D.Dlt ζ' q θ i ≤ 4 * K1 D.L (cexp d q) c₂ θ *
      ∑ k ∈ range i, D.rhoL q c₂ θ ^ (i - 1 - k) * ‖D.ζ k - ζ' k‖
  | 0, _ => by rw [Dlt_zero (by have := h.hL; omega)]; simp
  | i + 1, hi => by
    have ih := Dlt_le h i (by omega)
    have h1 := Dlt_succ_le h i
    have h2 := Elt_le h (i := i) (by omega)
    have hρ0 := rhoL_nonneg h (by omega)
    set ρ := D.rhoL q c₂ θ
    set K := K1 D.L (cexp d q) c₂ θ
    have hsum : ∑ k ∈ range (i + 1), ρ ^ (i + 1 - 1 - k) * ‖D.ζ k - ζ' k‖ =
        ρ * ∑ k ∈ range i, ρ ^ (i - 1 - k) * ‖D.ζ k - ζ' k‖ + ‖D.ζ i - ζ' i‖ := by
      rw [sum_range_succ, mul_sum, show i + 1 - 1 - i = 0 by omega, pow_zero, one_mul]
      congr 1
      refine sum_congr rfl fun k hk => ?_
      rw [mem_range] at hk
      rw [show i + 1 - 1 - k = (i - 1 - k) + 1 by omega, pow_succ]; ring
    rw [hsum]
    have hρ : D.Dlt ζ' q θ (i + 1) ≤ ρ * D.Dlt ζ' q θ i + 4 * K * ‖D.ζ i - ζ' i‖ := by
      simp only [ρ, rhoL]; linarith
    calc D.Dlt ζ' q θ (i + 1) ≤ ρ * D.Dlt ζ' q θ i + 4 * K * ‖D.ζ i - ζ' i‖ := hρ
      _ ≤ ρ * (4 * K * ∑ k ∈ range i, ρ ^ (i - 1 - k) * ‖D.ζ k - ζ' k‖) +
          4 * K * ‖D.ζ i - ζ' i‖ := by gcongr
      _ = _ := by ring

/-- The core estimate: `‖C'_{j+1}(ζ) - C'_{j+1}(ζ')‖_{(j)} ≤ 2 Δ_j + 4 K₁ |ζ_j - ζ'_j|`. -/
theorem snorm_Cdiff_le (h : D.LipHyp ζ' q c₂ θ) {j : ℕ} (hj : j + 1 < D.N) :
    snorm D.L q j (D.Z (j + 1) • D.Gint j - (D.withζ ζ').Z (j + 1) • (D.withζ ζ').Gint j) ≤
      2 * D.Dlt ζ' q θ j + 4 * K1 D.L (cexp d q) c₂ θ * ‖D.ζ j - ζ' j‖ := by
  have hθ := h.good.pos
  have hθ1 : θ ≤ 1 := by linarith [h.good.le8]
  have hL1 : 1 ≤ D.L := by have := h.hL; omega
  have hL0 : (0 : ℝ) < D.L := by exact_mod_cast (by omega : 0 < D.L)
  have h12 : ∀ k, ‖D.ζ k‖ ≤ 1 / 2 := fun k => by linarith [h.hζ k, h.good.le8]
  have h12' : ∀ k, ‖(D.withζ ζ').ζ k‖ ≤ 1 / 2 := fun k => by
    show ‖ζ' k‖ ≤ 1 / 2; linarith [h.hζ' k, h.good.le8]
  rw [Z_Gint_Wn h12 hj, Z_Gint_Wn (D := D.withζ ζ') h12' hj]
  have e : ofR (D.C (j + 1)) + D.Wn j (j + 1) + D.wSc j (D.tails j) (j + 1) -
      (ofR ((D.withζ ζ').C (j + 1)) + (D.withζ ζ').Wn j (j + 1) +
        (D.withζ ζ').wSc j ((D.withζ ζ').tails j) (j + 1)) =
      (D.Wn j (j + 1) - (D.withζ ζ').Wn j (j + 1)) +
      (D.wSc j (D.tails j) (j + 1) - (D.withζ ζ').wSc j ((D.withζ ζ').tails j) (j + 1)) := by
    show ofR (D.C (j + 1)) + D.Wn j (j + 1) + D.wSc j (D.tails j) (j + 1) -
      (ofR (D.C (j + 1)) + (D.withζ ζ').Wn j (j + 1) +
        (D.withζ ζ').wSc j ((D.withζ ζ').tails j) (j + 1)) = _
    abel
  rw [e]
  refine (snorm_add_le hL0 _ _).trans ?_
  -- the tail part
  have h1 : snorm D.L q j (D.Wn j (j + 1) - (D.withζ ζ').Wn j (j + 1)) ≤ D.Dlt ζ' q θ j := by
    have := single_le_sum (f := fun r => Wt θ D.L (r - j) *
      snorm D.L q (r - 1) (D.Wn j r - (D.withζ ζ').Wn j r))
      (fun r _ => mul_nonneg (Wt_pos hθ _ _).le (snorm_nonneg hL0 _))
      (show j + 1 ∈ Ioc j D.N by rw [mem_Ioc]; omega)
    simp only [show j + 1 - j = 1 by omega, show j + 1 - 1 = j by omega] at this
    have hW := one_le_Wt hθ hθ1 hL0.le 1
    have hs := snorm_nonneg hL0 (q := q) (s := j) (D.Wn j (j + 1) - (D.withζ ζ').Wn j (j + 1))
    unfold Dlt; nlinarith
  -- the word part
  have h2 : snorm D.L q j (D.wSc j (D.tails j) (j + 1) -
      (D.withζ ζ').wSc j ((D.withζ ζ').tails j) (j + 1)) ≤ D.Elt ζ' q θ j := by
    have := single_le_sum (f := fun s => Wt θ D.L (s - 1 - j) *
      snorm D.L q (s - 1) (D.wSc j (D.tails j) s - (D.withζ ζ').wSc j ((D.withζ ζ').tails j) s))
      (fun r _ => mul_nonneg (Wt_pos hθ _ _).le (snorm_nonneg hL0 _))
      (show j + 1 ∈ Icc (j + 1) D.N by rw [mem_Icc]; omega)
    simp only [show j + 1 - 1 = j by omega, Nat.sub_self] at this
    have hW := one_le_Wt hθ hθ1 hL0.le 0
    have hs := snorm_nonneg hL0 (q := q) (s := j)
      (D.wSc j (D.tails j) (j + 1) - (D.withζ ζ').wSc j ((D.withζ ζ').tails j) (j + 1))
    unfold Elt; nlinarith
  have h3 := Elt_le h (i := j) (by omega)
  have hsm : 4 * (Crho d D.L * K1 D.L (cexp d q) c₂ θ * θ) ≤ 1 := by linarith [h.small]
  have hΔ := Dlt_nonneg (ζ' := ζ') (q := q) hθ hL1 j
  nlinarith

/-- The core estimate with the decay: `‖δC'_{j+1}‖_{(j)} ≤ K₁ (8/ρ + 4) ∑_{k≤j} ρ^{j-k} |δζ_k|`
for any `ρ ≥ θ^{6/256} + 4 C_ρ K₁ θ`, `ρ > 0`. -/
theorem snorm_Cdiff_le_decay (h : D.LipHyp ζ' q c₂ θ) {ρ : ℝ} (hρ : 0 < ρ)
    (hρL : D.rhoL q c₂ θ ≤ ρ) {j : ℕ} (hj : j + 1 < D.N) :
    snorm D.L q j (D.Z (j + 1) • D.Gint j - (D.withζ ζ').Z (j + 1) • (D.withζ ζ').Gint j) ≤
      K1 D.L (cexp d q) c₂ θ * (8 / ρ + 4) *
        ∑ k ∈ range (j + 1), ρ ^ (j - k) * ‖D.ζ k - ζ' k‖ := by
  have hθ := h.good.pos
  have hL0 : (0 : ℝ) < D.L := by exact_mod_cast (by have := h.hL; omega : 0 < D.L)
  have hc₂ : 0 ≤ c₂ := le_trans (snorm_nonneg hL0 _) (h.loc 0 (by omega))
  have hK := K1_nonneg (L := (D.L : ℝ)) (c := cexp d q) hL0.le hc₂ hθ.le
  set K := K1 D.L (cexp d q) c₂ θ
  have h1 := snorm_Cdiff_le h hj
  have h2 := Dlt_le h j (by omega)
  have hρ0 := rhoL_nonneg h (by omega)
  -- replace the ratio by `ρ`
  have h3 : ∑ k ∈ range j, D.rhoL q c₂ θ ^ (j - 1 - k) * ‖D.ζ k - ζ' k‖ ≤
      ρ⁻¹ * ∑ k ∈ range j, ρ ^ (j - k) * ‖D.ζ k - ζ' k‖ := by
    rw [mul_sum]
    refine sum_le_sum fun k hk => ?_
    rw [mem_range] at hk
    have e : ρ⁻¹ * (ρ ^ ((j - 1 - k) + 1) * ‖D.ζ k - ζ' k‖) = ρ ^ (j - 1 - k) * ‖D.ζ k - ζ' k‖ := by
      rw [pow_succ]; field_simp
    rw [show j - k = (j - 1 - k) + 1 by omega, e]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hρ0 hρL _) (norm_nonneg _)
  have hsum : ∑ k ∈ range (j + 1), ρ ^ (j - k) * ‖D.ζ k - ζ' k‖ =
      ∑ k ∈ range j, ρ ^ (j - k) * ‖D.ζ k - ζ' k‖ + ‖D.ζ j - ζ' j‖ := by
    rw [sum_range_succ, Nat.sub_self, pow_zero, one_mul]
  rw [hsum]
  have hS0 : 0 ≤ ∑ k ∈ range j, ρ ^ (j - k) * ‖D.ζ k - ζ' k‖ :=
    sum_nonneg fun k _ => mul_nonneg (pow_nonneg hρ.le _) (norm_nonneg _)
  have hn0 := norm_nonneg (D.ζ j - ζ' j)
  have hρi : 0 ≤ ρ⁻¹ := inv_nonneg.2 hρ.le
  have h8 : 0 ≤ 8 / ρ := by positivity
  calc _ ≤ 2 * D.Dlt ζ' q θ j + 4 * K * ‖D.ζ j - ζ' j‖ := h1
    _ ≤ 2 * (4 * K * (ρ⁻¹ * ∑ k ∈ range j, ρ ^ (j - k) * ‖D.ζ k - ζ' k‖)) +
        4 * K * ‖D.ζ j - ζ' j‖ := by
        gcongr; exact h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity))
    _ = K * (8 / ρ) * ∑ k ∈ range j, ρ ^ (j - k) * ‖D.ζ k - ζ' k‖ +
        4 * K * ‖D.ζ j - ζ' j‖ := by rw [div_eq_mul_inv]; ring
    _ ≤ K * (8 / ρ + 4) * (∑ k ∈ range j, ρ ^ (j - k) * ‖D.ζ k - ζ' k‖ + ‖D.ζ j - ζ' j‖) := by
        have : 0 ≤ K * 4 * ∑ k ∈ range j, ρ ^ (j - k) * ‖D.ζ k - ζ' k‖ := by positivity
        have : 0 ≤ K * (8 / ρ) * ‖D.ζ j - ζ' j‖ := by positivity
        nlinarith

end Data

open Data

/-- **Lipschitz dependence with geometric decay** (`lip_decay`). For every ratio `0 < ρ ≤ 1/2`
there are `ζ̄ ∈ (0, 1/8]` and `K ≥ 0` such that: for every standard decomposition and every
two coupling sequences `ζ = D.ζ`, `ζ'` with `|ζ_i|, |ζ'_i| ≤ ζ̄/2`, and `j + 1 < N`,
`‖C'_{j+1}(ζ) - C'_{j+1}(ζ')‖_{(j)} ≤ K ∑_{k ≤ j} ρ^{j-k} |ζ_k - ζ'_k|`, where
`C'_{j+1} = Z_{j+1} Γ^int_{j+1}`. -/
theorem lip_decay {q L : ℕ} {c₂ ρ : ℝ} (hd : 2 ≤ d) (hq : 2 ≤ q) (hL : 7 ≤ L) (hc₂ : 0 ≤ c₂)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1 / 2) :
    ∃ ζbar : ℝ, 0 < ζbar ∧ ζbar ≤ 1 / 8 ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ (n : ℕ) [NeZero n] (D : Data d n) (ζ' : ℕ → ℂ), D.L = L → n = L ^ D.N →
      StdHyp L D.N D.msq D.C → StdLoc L D.N q D.msq c₂ D.C →
      D.msq ≤ (L : ℝ) ^ (-(2 * ((D.N : ℝ) - 1))) →
      (∀ i, ‖D.ζ i‖ ≤ ζbar / 2) → (∀ i, ‖ζ' i‖ ≤ ζbar / 2) → ∀ j, j + 1 < D.N →
      snorm L q j (D.Z (j + 1) • D.Gint j - (D.withζ ζ').Z (j + 1) • (D.withζ ζ').Gint j) ≤
        K * ∑ k ∈ range (j + 1), ρ ^ (j - k) * ‖D.ζ k - ζ' k‖ := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  obtain ⟨θ, hG, hθ6, hθK⟩ := exists_theta_lip (L : ℝ) (cexp d q) c₂ (Crho d L) ρ hL0 hc₂
    (Crho_nonneg d hL0.le) hρ hρ1
  have hK1 := K1_nonneg (L := (L : ℝ)) (c := cexp d q) hL0.le hc₂ hG.pos.le
  refine ⟨θ, hG.pos, hG.le8, K1 L (cexp d q) c₂ θ * (8 / ρ + 4), by positivity,
    fun n _ D ζ' hDL hn hstd hloc hmsq hζ hζ' j hj => ?_⟩
  subst hDL
  have h : D.LipHyp ζ' q c₂ θ := ⟨hG, by linarith, hstd, hloc, hL, hn, hq, hd, hmsq, hζ, hζ'⟩
  have hρL : D.rhoL q c₂ θ ≤ ρ := by unfold rhoL; linarith
  exact snorm_Cdiff_le_decay h hρ hρL hj

/-- `lip_decay` under (S1)–(S5), with `c₂ = c2val d L q M c_S` (`lem:std`(e)). -/
theorem lip_decay_full {q L M : ℕ} {cS ρ : ℝ} (hd : 2 ≤ d) (hq : 2 ≤ q) (hL : 7 ≤ L)
    (hM : q + d + 1 ≤ M) (hcS : 0 ≤ cS) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1 / 2) :
    ∃ ζbar : ℝ, 0 < ζbar ∧ ζbar ≤ 1 / 8 ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ (n : ℕ) [NeZero n] (D : Data d n) (ζ' : ℕ → ℂ), D.L = L → n = L ^ D.N →
      StdFull L D.N q M D.msq cS D.C →
      D.msq ≤ (L : ℝ) ^ (-(2 * ((D.N : ℝ) - 1))) →
      (∀ i, ‖D.ζ i‖ ≤ ζbar / 2) → (∀ i, ‖ζ' i‖ ≤ ζbar / 2) → ∀ j, j + 1 < D.N →
      snorm L q j (D.Z (j + 1) • D.Gint j - (D.withζ ζ').Z (j + 1) • (D.withζ ζ').Gint j) ≤
        K * ∑ k ∈ range (j + 1), ρ ^ (j - k) * ‖D.ζ k - ζ' k‖ := by
  obtain ⟨ζbar, hζ, hζ8, K, hK0, hK⟩ := lip_decay (c₂ := c2val d L q M cS) hd hq hL
    (c2val_nonneg (by omega) hM (by omega) hcS) hρ hρ1
  exact ⟨ζbar, hζ, hζ8, K, hK0, fun n _ D ζ' hDL hn hS hmsq hζi hζi' j hj =>
    hK n D ζ' hDL hn hS.base (std_e hS (by omega) hq hL hn) hmsq hζi hζi' j hj⟩

/-! ### Consequences for the kernel -/

section Kernel

variable {L : ℝ} {q s : ℕ}

end Kernel

namespace Data

/-- The range of the difference: `2 rng (C'_{j+1}(ζ) - C'_{j+1}(ζ')) < L^{j+1}`. -/
theorem two_rng_Cdiff_lt {D : Data d n} {ζ' : ℕ → ℂ} (h : StdHyp D.L D.N D.msq D.C)
    (hL : 1 ≤ D.L) (hn : n = D.L ^ D.N) {j : ℕ} (hj : j + 1 < D.N) :
    2 * rng (D.Z (j + 1) • D.Gint j - (D.withζ ζ').Z (j + 1) • (D.withζ ζ').Gint j) <
      D.L ^ (j + 1) := by
  have h1 := two_rng_Gint_lt h hL hn hj
  have h2 := two_rng_Gint_lt (D := D.withζ ζ') h hL hn hj
  have e1 := rng_smul_le (D.Z (j + 1)) (D.Gint j)
  have e2 := rng_smul_le ((D.withζ ζ').Z (j + 1)) ((D.withζ ζ').Gint j)
  have e3 := rng_sub_le (D.Z (j + 1) • D.Gint j) ((D.withζ ζ').Z (j + 1) • (D.withζ ζ').Gint j)
  have : 2 * max (rng (D.Z (j + 1) • D.Gint j)) (rng ((D.withζ ζ').Z (j + 1) • (D.withζ ζ').Gint j))
      < D.L ^ (j + 1) := by
    rcases le_total (rng (D.Z (j + 1) • D.Gint j))
      (rng ((D.withζ ζ').Z (j + 1) • (D.withζ ζ').Gint j)) with hh | hh
    · rw [max_eq_right hh]; exact lt_of_le_of_lt (by omega) h2
    · rw [max_eq_left hh]; exact lt_of_le_of_lt (by omega) h1
  omega

end Data

end

end DressedFRD
