import DressedFRD.MainFull

/-!
# The zero mode of `ε_j` (`d = 2`)

`eps_zero_bound`: under (S1)–(S5) with `0 < m² ≤ L^{-2(N-1)}`, there are `ζ̄ > 0` and `B ≥ 0`
such that for every history `|ζ_i| ≤ ζ̄` and every `j < N`
* `|ζ'_j ε_j(0)| ≤ 1/2` (`Data.norm_zp_eps_le`), so `|1 + ζ_j(1 - ε_j(0))| ≥ |1+ζ_j|/2`;
* `|ε_j(0)| ≤ B m² L^{2j}`.

Proof: `ε_j(0) = m² Ĉ_{≤j}(0) - Z_j m² ∑_{r>j} R̂_{j,r}(0)`. By `lem:std`(d), `Ĉ_k(0) ≤ c_d L^{2k}`.
For the tails, `|R̂_{j,r}(0)| ≤ ∑_x |R_{j,r}(x)| ≤ (2 rng + 1)² ‖R_{j,r}‖_{(r-1)} ≤ 4 L^{2r} ‖R_{j,r}‖_{(r-1)}`
(range invariant), and `L^{2(r-j)} ≤ 6·128³ W_{r-j}` (`sq_le_theta_rpow`), so the tail part is
`≤ 4·6·128³ m² L^{2j} 𝒮_j` with `𝒮_j ≤ 1` (induction (H_j) of `thm:main`).
-/

namespace DressedFRD

noncomputable section

open Finset FRD Data Grassmann

/-- `x² ≤ 6·128³ θ^{-x/256}` for `x ≥ 1`, `0 < θ ≤ 1/8`. -/
theorem sq_le_theta_rpow {θ x : ℝ} (hθ : 0 < θ) (hθ8 : θ ≤ 1 / 8) (hx : 1 ≤ x) :
    x ^ 2 ≤ 6 * 128 ^ 3 * θ ^ (-x / 256) := by
  have hx0 : 0 < x := by linarith
  have h1 : θ ^ (x / 256) ≤ Real.exp (-(x / 128)) := by
    calc θ ^ (x / 256) ≤ (1 / 8 : ℝ) ^ (x / 256) := Real.rpow_le_rpow hθ.le hθ8 (by positivity)
      _ = Real.exp (Real.log (1 / 8) * (x / 256)) := Real.rpow_def_of_pos (by norm_num) _
      _ ≤ Real.exp (-(x / 128)) := by
        apply Real.exp_le_exp.2
        have : Real.log (1 / 8 : ℝ) ≤ -2 := by
          rw [one_div, Real.log_inv, show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
          have := Real.log_two_gt_d9; push_cast; linarith
        nlinarith
  have h3 : x ^ 3 / (6 * 128 ^ 3) ≤ Real.exp (x / 128) := by
    have := Real.pow_div_factorial_le_exp (x := x / 128) (by positivity) 3
    have e : (x / 128) ^ 3 / (Nat.factorial 3 : ℝ) = x ^ 3 / (6 * 128 ^ 3) := by
      simp [Nat.factorial]; ring
    linarith
  rw [div_le_iff₀ (by norm_num)] at h3
  have hE : Real.exp (x / 128) * Real.exp (-(x / 128)) = 1 := by rw [← Real.exp_add]; simp
  have hp : θ ^ (x / 256) * θ ^ (-x / 256) = 1 := by
    rw [← Real.rpow_add hθ, show x / 256 + -x / 256 = 0 by ring, Real.rpow_zero]
  have hpos : 0 ≤ θ ^ (x / 256) := Real.rpow_nonneg hθ.le _
  have hq : x ^ 2 * θ ^ (x / 256) ≤ 6 * 128 ^ 3 := by
    have h4 : x ^ 3 * Real.exp (-(x / 128)) ≤ 6 * 128 ^ 3 := by
      calc x ^ 3 * Real.exp (-(x / 128))
          ≤ Real.exp (x / 128) * (6 * 128 ^ 3) * Real.exp (-(x / 128)) :=
            mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
        _ = 6 * 128 ^ 3 := by rw [mul_comm (Real.exp _), mul_assoc, hE, mul_one]
    have h23 : x ^ 2 ≤ x ^ 3 := by nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.2 hx)]
    exact (mul_le_mul h23 h1 hpos (by positivity)).trans h4
  calc x ^ 2 = x ^ 2 * (θ ^ (x / 256) * θ ^ (-x / 256)) := by rw [hp, mul_one]
    _ = x ^ 2 * θ ^ (x / 256) * θ ^ (-x / 256) := by ring
    _ ≤ 6 * 128 ^ 3 * θ ^ (-x / 256) :=
        mul_le_mul_of_nonneg_right hq (Real.rpow_nonneg hθ.le _)

/-- `∑_{k=1}^j x^k ≤ 2 x^j` for `x ≥ 2`. -/
theorem sum_Icc_two_pow_le {x : ℝ} (hx : 2 ≤ x) (j : ℕ) : ∑ k ∈ Icc 1 j, x ^ k ≤ 2 * x ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [sum_Icc_succ_top (by omega)]
    have : 0 ≤ x ^ j := pow_nonneg (by linarith) j
    rw [pow_succ]
    nlinarith

variable {n : ℕ} [NeZero n]

/-- **The zero mode of `ε_j`**: `|ζ'_jε_j(0)| ≤ 1/2` and `|ε_j(0)| ≤ B m² L^{2j}` (`d = 2`). -/
theorem eps_zero_bound {q L M : ℕ} {cS : ℝ} (hq : 2 ≤ q) (hL : 7 ≤ L) (hM : q + 2 + 1 ≤ M)
    (hcS : 0 ≤ cS) :
    ∃ ζbar : ℝ, 0 < ζbar ∧ ζbar ≤ 1 / 8 ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ (n : ℕ) [NeZero n] (D : Data 2 n), D.L = L → n = L ^ D.N →
      StdFull L D.N q M D.msq cS D.C → D.msq ≤ (L : ℝ) ^ (-(2 * ((D.N : ℝ) - 1))) →
      (∀ i, ‖D.ζ i‖ ≤ ζbar) → ∀ j, j < D.N →
        ‖D.zp j * D.eps j (D.tails j) 0‖ ≤ 1 / 2 ∧
        ‖D.eps j (D.tails j) 0‖ ≤ B * D.msq * (L : ℝ) ^ (2 * j) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hL1' : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hc₂ : 0 ≤ c2val 2 L q M cS := c2val_nonneg (by omega) hM (by omega) hcS
  obtain ⟨θ, hG⟩ := exists_theta (L : ℝ) (cexp 2 q) (c2val 2 L q M cS) (Crho 2 L) hL0 hc₂
    (Crho_nonneg 2 hL0.le)
  have hθ := hG.pos
  have hθ1 : θ ≤ 1 := by linarith [hG.le8]
  have hK1 : 0 ≤ K1 (L : ℝ) (cexp 2 q) (c2val 2 L q M cS) θ := K1_nonneg hL0.le hc₂ hθ.le
  have hcd : 0 ≤ 2 ^ M * (1 + 2 * M : ℝ) ^ 2 * cS := by positivity
  refine ⟨θ, hθ, hG.le8, 2 * (2 ^ M * (1 + 2 * M : ℝ) ^ 2 * cS) + 4 * (6 * 128 ^ 3),
    by positivity, fun n _ D hDL hn hS hmsq hζ j hj => ?_⟩
  subst hDL
  have hstd := hS.base
  have hloc := std_e hS (by norm_num) hq hL hn
  have hL1 : 1 ≤ D.L := by omega
  have H0 : D.StepHyp q (c2val 2 D.L q M cS) θ 0 := ⟨hstd, hloc, hL, hn, hq, le_rfl, hmsq,
    by omega, tailRange_zero hL1, hθ, hθ1⟩
  obtain ⟨H, hSj⟩ := induction hG hζ H0 j hj
  have hMz : D.Mz j ≤ θ := Mz_le hθ.le fun i _ => hζ i
  have hS1 : Crho 2 D.L * D.Sj q θ j ≤ 1 := by
    have := hG.small
    calc Crho 2 D.L * D.Sj q θ j
        ≤ Crho 2 D.L * (2 * K1 (D.L : ℝ) (cexp 2 q) (c2val 2 D.L q M cS) θ * θ) :=
          mul_le_mul_of_nonneg_left (hSj.trans (mul_le_mul_of_nonneg_left hMz (by positivity)))
            (Crho_nonneg 2 hL0.le)
      _ ≤ 1 := by simp only [K1]; linarith
  have hS0 := Sj_nonneg (D := D) (q := q) (j := j) hθ hL1
  have hSle : D.Sj q θ j ≤ 1 := by
    have := one_le_Crho 2 hL1'
    nlinarith
  refine ⟨norm_zp_eps_le H (hζ j) hG.le8 hS1 0, ?_⟩
  have hA0 : Asym D.msq (0 : Torus 2 n) = (D.msq : ℂ) := by simp [Asym, lam_zero']
  have hm0 := hstd.msq_pos
  set cd : ℝ := 2 ^ M * (1 + 2 * M : ℝ) ^ 2 * cS
  set c₀ : ℝ := 6 * 128 ^ 3
  have hL2 : (2 : ℝ) ≤ (D.L : ℝ) ^ 2 := by
    have : (7 : ℝ) ≤ D.L := by exact_mod_cast hL
    nlinarith
  -- the standard part
  have hE : ‖Ehat D.msq D.C j 0‖ ≤ 2 * cd * D.msq * (D.L : ℝ) ^ (2 * j) := by
    rw [Ehat_apply, Complex.norm_real, Real.norm_of_nonneg (ereal_nonneg hstd j 0), ereal,
      lam_zero', zero_add]
    have hC : ∑ k ∈ Icc 1 j, D.C k 0 ≤ cd * ∑ k ∈ Icc 1 j, ((D.L : ℝ) ^ 2) ^ k := by
      rw [mul_sum]
      refine sum_le_sum fun k hk => ?_
      rw [mem_Icc] at hk
      have := std_d hS (by norm_num) hL1 hk.1 (by omega) 0
      rw [pnorm_zero', mul_zero, add_zero, one_pow, mul_one] at this
      rw [← pow_mul, show 2 * k = 2 + 2 * (k - 1) by omega, pow_add]
      linarith
    have h2 := sum_Icc_two_pow_le hL2 j
    rw [← pow_mul] at h2
    calc D.msq * ∑ k ∈ Icc 1 j, D.C k 0 ≤ D.msq * (cd * (2 * (D.L : ℝ) ^ (2 * j))) := by
          refine mul_le_mul_of_nonneg_left (hC.trans ?_) hm0.le
          refine mul_le_mul_of_nonneg_left ?_ hcd
          simpa [← pow_mul] using h2
      _ = _ := by ring
  -- the tails
  have hT : ∀ r ∈ Ioc j D.N, ‖D.Z j‖ * ‖D.tails j r 0‖ ≤
      4 * c₀ * (D.L : ℝ) ^ (2 * j) * (Wt θ D.L (r - j) * D.tW q j r) := by
    intro r hr
    rw [mem_Ioc] at hr
    have hk : ∀ x, ‖kern (D.tails j r) x‖ ≤ snorm D.L q (r - 1) (D.tails j r) := fun x => by
      have := norm_kern_le (q := q) (s := r - 1) hL0 (D.tails j r) x
      rwa [wgt_zero, show ((2 : ℕ) : ℝ) - 2 = 0 by norm_num, mul_zero, Real.rpow_zero,
        inv_one, one_mul] at this
    have h1 := (norm_le_sum_kern (D.tails j r) 0).trans (sum_kern_le (D.tails j r) hk)
    have hcount : ((2 * rng (D.tails j r) + 1 : ℕ) : ℝ) ≤ 2 * (D.L : ℝ) ^ r := by
      have h2 : 2 * rng (D.tails j r) ≤ D.L ^ r := by
        by_cases hrN : r < D.N
        · have := H.tr r hr.1 hrN; omega
        · have : r = D.N := by omega
          rw [this, ← hn]; exact two_rng_le _
      have h3 : 1 ≤ D.L ^ r := Nat.one_le_pow _ _ (by omega)
      have : 2 * rng (D.tails j r) + 1 ≤ 2 * D.L ^ r := by omega
      exact_mod_cast this
    have hsn := snorm_nonneg hL0 (q := q) (s := r - 1) (D.tails j r)
    have h1' : ‖D.tails j r 0‖ ≤ 4 * ((D.L : ℝ) ^ r) ^ 2 * snorm D.L q (r - 1) (D.tails j r) := by
      refine h1.trans ?_
      have : ((2 * rng (D.tails j r) + 1 : ℕ) : ℝ) ^ 2 ≤ (2 * (D.L : ℝ) ^ r) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hcount 2
      push_cast at this ⊢
      nlinarith
    have hW : ((D.L : ℝ) ^ (r - j)) ^ 2 ≤ c₀ * Wt θ D.L (r - j) :=
      sq_le_theta_rpow hθ hG.le8 (one_le_pow₀ hL1')
    have hLr : ((D.L : ℝ) ^ r) ^ 2 = (D.L : ℝ) ^ (2 * j) * ((D.L : ℝ) ^ (r - j)) ^ 2 := by
      rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; omega
    have hZ := norm_nonneg (D.Z j)
    calc ‖D.Z j‖ * ‖D.tails j r 0‖
        ≤ ‖D.Z j‖ * (4 * ((D.L : ℝ) ^ r) ^ 2 * snorm D.L q (r - 1) (D.tails j r)) :=
          mul_le_mul_of_nonneg_left h1' hZ
      _ = 4 * (D.L : ℝ) ^ (2 * j) * ((D.L : ℝ) ^ (r - j)) ^ 2 * D.tW q j r := by
          rw [hLr, tW]; ring
      _ ≤ 4 * (D.L : ℝ) ^ (2 * j) * (c₀ * Wt θ D.L (r - j)) * D.tW q j r := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hW (by positivity))
            (tW_nonneg hL1 q j r)
      _ = _ := by ring
  have hTs : ‖D.Z j * (D.msq : ℂ) * (∑ r ∈ Ioc j D.N, D.tails j r) 0‖ ≤
      4 * c₀ * D.msq * (D.L : ℝ) ^ (2 * j) := by
    rw [Finset.sum_apply, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hm0.le]
    have := norm_sum_le (Ioc j D.N) fun r => D.tails j r 0
    calc ‖D.Z j‖ * D.msq * ‖∑ r ∈ Ioc j D.N, D.tails j r 0‖
        ≤ D.msq * ∑ r ∈ Ioc j D.N, ‖D.Z j‖ * ‖D.tails j r 0‖ := by
          rw [← mul_sum, mul_comm ‖D.Z j‖, mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left this (norm_nonneg _)) hm0.le
      _ ≤ D.msq * ∑ r ∈ Ioc j D.N,
            4 * c₀ * (D.L : ℝ) ^ (2 * j) * (Wt θ D.L (r - j) * D.tW q j r) :=
          mul_le_mul_of_nonneg_left (sum_le_sum hT) hm0.le
      _ = D.msq * (4 * c₀ * (D.L : ℝ) ^ (2 * j)) * D.Sj q θ j := by rw [← mul_sum, Sj]; ring
      _ ≤ D.msq * (4 * c₀ * (D.L : ℝ) ^ (2 * j)) * 1 :=
          mul_le_mul_of_nonneg_left hSle (by positivity)
      _ = _ := by ring
  rw [eps_apply, hA0]
  refine (norm_sub_le _ _).trans ?_
  linarith

end

end DressedFRD
