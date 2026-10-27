import DressedFRD.Step
import DressedFRD.Theta

/-!
# The main theorem (`thm:main`(i), (iii), (iv), (v))

`thm_main`: for `d ≥ 2`, `q ≥ 2`, `L ≥ 7` and `c₂ ≥ 0` there are `ζ̄ > 0` and `K` such that for
every standard decomposition (`StdHyp`, `StdLoc`) with `0 < m² ≤ L^{-2(N-1)}` and every sequence
`|ζ_i| ≤ ζ̄`, at every step `j < N`:
* (i) `1 + z_j A Γ_j` is invertible and `Γ_j (1 + z_j A Γ_j)^{-1} = Γ^int_{j+1} + Γ_{j+1}`;
* (iii) `rng Γ^int_{j+1} < L^{j+1}/2` if `j + 1 < N`;
* (iv) `‖Z_{j+1} Γ^int_{j+1} - C_{j+1}‖_{(j)} ≤ K |ζ|_{≤j}` if `j + 1 < N`;
* (v) `‖Z_{j+1} Γ^int_{j+1} - C_{j+1} - ζ_j C_{≤j}(1-E_j)‖_{(j)} ≤ K (|ζ_j|² + ζ̄^{L/256} |ζ|_{≤j})`.

The induction (H_j) is `induction_step`, with `𝒮_j ≤ 2 K₁ |ζ|_{<j}`.
-/

namespace DressedFRD

noncomputable section

open Finset Grassmann FRD

variable {d n : ℕ} [NeZero n]

namespace Data

variable {D : Data d n}

/-- `|ζ|_{<j} = max_{i<j} |ζ_i|`. -/
def Mz (D : Data d n) (j : ℕ) : ℝ := (((range j).sup fun i => ‖D.ζ i‖₊ : NNReal) : ℝ)

theorem Mz_nonneg (j : ℕ) : 0 ≤ D.Mz j := NNReal.coe_nonneg _

theorem norm_le_Mz {i j : ℕ} (h : i < j) : ‖D.ζ i‖ ≤ D.Mz j := by
  have : ‖D.ζ i‖₊ ≤ (range j).sup fun i => ‖D.ζ i‖₊ := Finset.le_sup (f := fun i => ‖D.ζ i‖₊)
    (mem_range.2 h)
  exact_mod_cast this

theorem Mz_le {j : ℕ} {B : ℝ} (hB : 0 ≤ B) (h : ∀ i < j, ‖D.ζ i‖ ≤ B) : D.Mz j ≤ B := by
  unfold Mz
  have : ((range j).sup fun i => ‖D.ζ i‖₊) ≤ ⟨B, hB⟩ :=
    Finset.sup_le fun i hi => by
      have := h i (mem_range.1 hi)
      exact_mod_cast this
  exact_mod_cast this

theorem Mz_mono {i j : ℕ} (h : i ≤ j) : D.Mz i ≤ D.Mz j :=
  Mz_le (Mz_nonneg j) fun k hk => norm_le_Mz (by omega)

/-- `K₁ = 2 L^c (2 c₂ θ^{-6/256} + 12 θ^{-5/256})`. -/
def K1 (L c c₂ θ : ℝ) : ℝ := 2 * L ^ c * (2 * c₂ * θ ^ (-(6 : ℝ) / 256) + 12 * θ ^ (-(5 : ℝ) / 256))

theorem K1_nonneg {L c c₂ θ : ℝ} (hL : 0 ≤ L) (hc₂ : 0 ≤ c₂) (hθ : 0 ≤ θ) : 0 ≤ K1 L c c₂ θ := by
  unfold K1
  have := Real.rpow_nonneg hL c
  have := Real.rpow_nonneg hθ (-(6 : ℝ) / 256)
  have := Real.rpow_nonneg hθ (-(5 : ℝ) / 256)
  positivity

theorem one_le_Crho (d : ℕ) {L : ℝ} (hL : 1 ≤ L) : 1 ≤ Crho d L := by
  unfold Crho
  have : (1 : ℝ) ≤ (2 * L) ^ d := one_le_pow₀ (by linarith)
  have : (1 : ℝ) ≤ (d : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) d; linarith
  nlinarith

/-- `∑_r tW r ≤ 𝒮_j`, since `W ≥ 1`. -/
theorem sum_tW_le_Sj {q : ℕ} {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hL : 1 ≤ D.L) (j : ℕ) :
    ∑ r ∈ Ioc j D.N, D.tW q j r ≤ D.Sj q θ j := by
  refine sum_le_sum fun r _ => ?_
  have := one_le_Wt hθ hθ1 (by positivity : (0 : ℝ) ≤ D.L) (r - j)
  have := tW_nonneg (D := D) hL q j r
  nlinarith

/-- The denominators `1 - ζ' ε_j` do not vanish, `|ζ' ε_j| ≤ 1/2`. -/
theorem norm_zp_eps_le {q : ℕ} {c₂ θ : ℝ} {j : ℕ} (H : D.StepHyp q c₂ θ j)
    (hζ : ‖D.ζ j‖ ≤ θ) (hθ8 : θ ≤ 1 / 8) (hS : Crho d D.L * D.Sj q θ j ≤ 1) (m : Torus d n) :
    ‖D.zp j * D.eps j (D.tails j) m‖ ≤ 1 / 2 := by
  have hL1 : 1 ≤ D.L := by have := H.hL; omega
  have h1 := norm_eps_le H.std H.hj.le (fun r h1 h2 m => rho_bound H ⟨h1, h2⟩ m) m
  have h2 : ∑ r ∈ Ioc j D.N, Crho d D.L * D.tW q j r ≤ 1 := by
    rw [← mul_sum]
    exact le_trans (mul_le_mul_of_nonneg_left (sum_tW_le_Sj H.hθ H.hθ1 hL1 j)
      (Crho_nonneg d (by positivity))) hS
  have h3 := norm_zp_le (D := D) (j := j) (by linarith)
  rw [norm_mul]
  have : ‖D.eps j (D.tails j) m‖ ≤ 2 := by linarith
  nlinarith [norm_nonneg (D.zp j), norm_nonneg (D.eps j (D.tails j) m)]

/-- `lem:sum` with the choice of `θ`: all words of scales `s ≥ j + 1` contribute `≤ K₁ |ζ_j|`. -/
theorem word_sum_le {q : ℕ} {c₂ θ : ℝ}
    (hG : Good D.L (cexp d q) c₂ (Crho d D.L) θ) (hζ : ∀ i, ‖D.ζ i‖ ≤ θ)
    (H : D.StepHyp q c₂ θ j)
    (hS : D.Sj q θ j ≤ 2 * K1 D.L (cexp d q) c₂ θ * D.Mz j) :
    ∑ s ∈ Icc (j + 1) D.N, Wt θ D.L (s - 1 - j) * snorm D.L q (s - 1) (D.wSc j (D.tails j) s) ≤
      K1 D.L (cexp d q) c₂ θ * ‖D.ζ j‖ := by
  have hL7 := H.hL
  have hL1 : 1 ≤ D.L := by omega
  have hL0 : (0 : ℝ) < D.L := by exact_mod_cast (by omega : 0 < D.L)
  have hθ := hG.pos
  have hθ1 : θ ≤ 1 := by linarith [hG.le8]
  have hc₂ : 0 ≤ c₂ := le_trans (snorm_nonneg hL0 _) (H.loc 0 (by have := H.hj; omega))
  have hK1 := K1_nonneg (L := (D.L : ℝ)) (c := cexp d q) hL0.le hc₂ hθ.le
  have hMz : D.Mz j ≤ θ := Mz_le hθ.le fun i _ => hζ i
  -- `C_ρ 𝒮_j ≤ 1`, hence `𝒮_j ≤ 1`
  have hS1 : Crho d D.L * D.Sj q θ j ≤ 1 := by
    have := hG.small
    have hCρ := Crho_nonneg d hL0.le
    calc Crho d D.L * D.Sj q θ j ≤ Crho d D.L * (2 * K1 D.L (cexp d q) c₂ θ * θ) :=
          mul_le_mul_of_nonneg_left (hS.trans (mul_le_mul_of_nonneg_left hMz (by positivity))) hCρ
      _ ≤ 1 := by unfold K1; linarith
  have hS0 := Sj_nonneg (D := D) (q := q) (j := j) hθ hL1
  have hS1' : D.Sj q θ j ≤ 1 := by
    have := one_le_Crho d (by exact_mod_cast hL1 : (1 : ℝ) ≤ D.L)
    nlinarith
  -- `σ₀ ≤ 2 θ^{-3/256}`
  have hb2a : θ ^ (-(2 : ℝ) / 256) ≤ θ ^ (-(3 : ℝ) / 256) :=
    Real.rpow_le_rpow_of_exponent_ge hθ hθ1 (by norm_num)
  have hσ : D.sig0 q θ j ≤ 2 * θ ^ (-(3 : ℝ) / 256) := by
    unfold sig0
    have : θ ^ (-(2 : ℝ) / 256) * Crho d D.L * D.Sj q θ j ≤ θ ^ (-(2 : ℝ) / 256) := by
      rw [mul_assoc]
      exact mul_le_of_le_one_right (Real.rpow_nonneg hθ.le _) hS1
    linarith
  -- `η = √|ζ'|`
  have hζj : ‖D.ζ j‖ ≤ 1 / 2 := by linarith [hζ j, hG.le8]
  have hzp := norm_zp_le (D := D) hζj
  set η := Real.sqrt ‖D.zp j‖
  have hη0 : 0 ≤ η := Real.sqrt_nonneg _
  have hη2 : η ^ 2 = ‖D.zp j‖ := Real.sq_sqrt (norm_nonneg _)
  have hη : η ≤ Real.sqrt (2 * θ) :=
    Real.sqrt_le_sqrt (by linarith [hζ j])
  have hηc : η ≤ (D.L : ℝ) ^ (-cexp d q) := hη.trans hG.absorb
  have hgeom := hG.geom
  have hsq0 : 0 ≤ Real.sqrt (2 * θ) := Real.sqrt_nonneg _
  have ha0 : 0 ≤ θ ^ (-(3 : ℝ) / 256) := Real.rpow_nonneg hθ.le _
  have hx : η * θ ^ (-(3 : ℝ) / 256) ≤ 1 / 2 := by nlinarith
  have hy : η * D.sig0 q θ j ≤ 1 / 2 := by
    have hσ0 : 0 ≤ D.sig0 q θ j := add_nonneg ha0 (mul_nonneg (mul_nonneg
      (Real.rpow_nonneg hθ.le _) (Crho_nonneg d hL0.le)) hS0)
    nlinarith
  have hden : ∀ m, ‖D.zp j * D.eps j (D.tails j) m‖ < 1 := fun m =>
    lt_of_le_of_lt (norm_zp_eps_le H (hζ j) hG.le8 hS1 m) (by norm_num)
  have hsc := scales_bound_all H hη0 hη2 hηc hx hy hden
  -- the word contribution is `≤ K₁ |ζ_j|`
  have hword : ‖D.zp j‖ * (D.L : ℝ) ^ cexp d q *
      (2 * (c₂ * (θ ^ (-(3 : ℝ) / 256)) ^ 2) +
        6 * (θ ^ (-(2 : ℝ) / 256) * D.Sj q θ j * D.sig0 q θ j)) ≤
      K1 D.L (cexp d q) c₂ θ * ‖D.ζ j‖ := by
    have hsq : (θ ^ (-(3 : ℝ) / 256)) ^ 2 = θ ^ (-(6 : ℝ) / 256) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hθ.le]; norm_num
    have hprod : θ ^ (-(2 : ℝ) / 256) * θ ^ (-(3 : ℝ) / 256) = θ ^ (-(5 : ℝ) / 256) := by
      rw [← Real.rpow_add hθ]; norm_num
    have hin : θ ^ (-(2 : ℝ) / 256) * D.Sj q θ j * D.sig0 q θ j ≤ 2 * θ ^ (-(5 : ℝ) / 256) := by
      rw [← hprod]
      have hb20 := Real.rpow_nonneg hθ.le (-(2 : ℝ) / 256)
      have hσ0 : 0 ≤ D.sig0 q θ j := add_nonneg ha0 (mul_nonneg (mul_nonneg
        (Real.rpow_nonneg hθ.le _) (Crho_nonneg d hL0.le)) hS0)
      calc θ ^ (-(2 : ℝ) / 256) * D.Sj q θ j * D.sig0 q θ j
          ≤ θ ^ (-(2 : ℝ) / 256) * 1 * (2 * θ ^ (-(3 : ℝ) / 256)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hS1' hb20) hσ hσ0 (mul_nonneg hb20 zero_le_one)
        _ = _ := by ring
    have hLc := Real.rpow_nonneg hL0.le (cexp d q)
    have hpos : 0 ≤ ‖D.zp j‖ * (D.L : ℝ) ^ cexp d q := by positivity
    calc ‖D.zp j‖ * (D.L : ℝ) ^ cexp d q *
          (2 * (c₂ * (θ ^ (-(3 : ℝ) / 256)) ^ 2) +
            6 * (θ ^ (-(2 : ℝ) / 256) * D.Sj q θ j * D.sig0 q θ j))
        ≤ (2 * ‖D.ζ j‖) * (D.L : ℝ) ^ cexp d q *
          (2 * (c₂ * θ ^ (-(6 : ℝ) / 256)) + 6 * (2 * θ ^ (-(5 : ℝ) / 256))) := by
          rw [hsq]
          have : 0 ≤ 2 * (c₂ * θ ^ (-(6 : ℝ) / 256)) +
              6 * (θ ^ (-(2 : ℝ) / 256) * D.Sj q θ j * D.sig0 q θ j) := by
            have := Real.rpow_nonneg hθ.le (-(6 : ℝ) / 256)
            have := Real.rpow_nonneg hθ.le (-(2 : ℝ) / 256)
            have hσ0 : 0 ≤ D.sig0 q θ j := add_nonneg ha0 (mul_nonneg (mul_nonneg
              (Real.rpow_nonneg hθ.le _) (Crho_nonneg d hL0.le)) hS0)
            positivity
          calc ‖D.zp j‖ * (D.L : ℝ) ^ cexp d q *
                (2 * (c₂ * θ ^ (-(6 : ℝ) / 256)) +
                  6 * (θ ^ (-(2 : ℝ) / 256) * D.Sj q θ j * D.sig0 q θ j))
              ≤ ‖D.zp j‖ * (D.L : ℝ) ^ cexp d q *
                (2 * (c₂ * θ ^ (-(6 : ℝ) / 256)) + 6 * (2 * θ ^ (-(5 : ℝ) / 256))) := by
                gcongr
            _ ≤ _ := by
                have : 0 ≤ 2 * (c₂ * θ ^ (-(6 : ℝ) / 256)) + 6 * (2 * θ ^ (-(5 : ℝ) / 256)) := by
                  have := Real.rpow_nonneg hθ.le (-(6 : ℝ) / 256)
                  have := Real.rpow_nonneg hθ.le (-(5 : ℝ) / 256)
                  positivity
                gcongr
      _ = K1 D.L (cexp d q) c₂ θ * ‖D.ζ j‖ := by unfold K1; ring
  exact hsc.trans hword

/-- The induction hypothesis (H_j): `𝒮_j ≤ 2 K₁ |ζ|_{<j}`, together with the standing
hypotheses at time `j`. -/
theorem induction_step {q : ℕ} {c₂ θ : ℝ}
    (hG : Good D.L (cexp d q) c₂ (Crho d D.L) θ) (hζ : ∀ i, ‖D.ζ i‖ ≤ θ)
    (H : D.StepHyp q c₂ θ j)
    (hS : D.Sj q θ j ≤ 2 * K1 D.L (cexp d q) c₂ θ * D.Mz j) (hjN : j + 1 < D.N) :
    D.StepHyp q c₂ θ (j + 1) ∧
      D.Sj q θ (j + 1) ≤ 2 * K1 D.L (cexp d q) c₂ θ * D.Mz (j + 1) := by
  have hL7 := H.hL
  have hL1 : 1 ≤ D.L := by omega
  have hL0 : (0 : ℝ) < D.L := by exact_mod_cast (by omega : 0 < D.L)
  have hθ := hG.pos
  have hc₂ : 0 ≤ c₂ := le_trans (snorm_nonneg hL0 _) (H.loc 0 (by have := H.hj; omega))
  have hK1 := K1_nonneg (L := (D.L : ℝ)) (c := cexp d q) hL0.le hc₂ hθ.le
  have hS0 := Sj_nonneg (D := D) (q := q) (j := j) hθ hL1
  have hstep := Sj_succ_le H fun i => by linarith [hζ i, hG.le8]
  have hsc : ∑ s ∈ Icc (j + 2) D.N, Wt θ D.L (s - 1 - j) *
      snorm D.L q (s - 1) (D.wSc j (D.tails j) s) ≤ K1 D.L (cexp d q) c₂ θ * ‖D.ζ j‖ :=
    le_trans (sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc (by omega) le_rfl)
      fun s _ _ => mul_nonneg (Wt_pos hθ _ _).le (snorm_nonneg hL0 _)) (word_sum_le hG hζ H hS)
  refine ⟨⟨H.std, H.loc, H.hL, H.hn, H.hq, H.hd, H.hmsq, hjN,
    tailRange_succ H.std hL1 H.hn H.hj H.tr, H.hθ, H.hθ1⟩, ?_⟩
  have hq4 := hG.quarter
  have hMz1 : D.Mz j ≤ D.Mz (j + 1) := Mz_mono (by omega)
  have hζMz : ‖D.ζ j‖ ≤ D.Mz (j + 1) := norm_le_Mz (by omega)
  have h6 : θ ^ ((6 : ℝ) / 256) * D.Sj q θ j ≤ 1 / 4 * (2 * K1 D.L (cexp d q) c₂ θ * D.Mz j) :=
    mul_le_mul hq4 hS hS0 (by norm_num)
  calc D.Sj q θ (j + 1) ≤ θ ^ ((6 : ℝ) / 256) * D.Sj q θ j + K1 D.L (cexp d q) c₂ θ * ‖D.ζ j‖ :=
        hstep.trans (add_le_add le_rfl hsc)
    _ ≤ 1 / 4 * (2 * K1 D.L (cexp d q) c₂ θ * D.Mz j) + K1 D.L (cexp d q) c₂ θ * D.Mz (j + 1) :=
        add_le_add h6 (mul_le_mul_of_nonneg_left hζMz hK1)
    _ ≤ 2 * K1 D.L (cexp d q) c₂ θ * D.Mz (j + 1) := by nlinarith

theorem Sj_zero {q : ℕ} {θ : ℝ} (hL : 1 ≤ D.L) : D.Sj q θ 0 = 0 := by
  have hL0 : (0 : ℝ) < D.L := by exact_mod_cast (by omega : 0 < D.L)
  unfold Sj tW
  refine sum_eq_zero fun r _ => ?_
  have h0 : D.tails 0 r = (0 : ℂ) • (0 : Sym d n) := by simp [tails]
  rw [h0, snorm_smul hL0]; simp

/-- The full induction: (H_j) for all `j < N`. -/
theorem induction {q : ℕ} {c₂ θ : ℝ} (hG : Good D.L (cexp d q) c₂ (Crho d D.L) θ)
    (hζ : ∀ i, ‖D.ζ i‖ ≤ θ) (H0 : D.StepHyp q c₂ θ 0) :
    ∀ j, j < D.N → D.StepHyp q c₂ θ j ∧
      D.Sj q θ j ≤ 2 * K1 D.L (cexp d q) c₂ θ * D.Mz j
  | 0, _ => ⟨H0, by
      rw [Sj_zero (by have := H0.hL; omega)]
      exact mul_nonneg (mul_nonneg (by norm_num) (K1_nonneg (by positivity)
        (le_trans (snorm_nonneg (by exact_mod_cast (by have := H0.hL; omega : 0 < D.L)) _)
          (H0.loc 0 (by have := H0.hj; omega))) hG.pos.le)) (Mz_nonneg 0)⟩
  | j + 1, hj => by
      obtain ⟨H, hS⟩ := induction hG hζ H0 j (by omega)
      exact induction_step hG hζ H hS hj

theorem den_ne_zero {q : ℕ} {c₂ θ : ℝ} {j : ℕ} (H : D.StepHyp q c₂ θ j)
    (hζ : ∀ i, ‖D.ζ i‖ ≤ 1 / 2) (m : Torus d n)
    (hden : 1 - D.zp j * D.eps j (D.tails j) m ≠ 0) :
    1 + D.ζ j * D.Z j * Asym D.msq m * D.Gam j m ≠ 0 := by
  have hG := Z_A_Gam H.std H.hj.le (Z_ne_zero hζ j) m
  have hζ1 := one_add_ne_zero (D := D) (j := j) (hζ j)
  have : 1 + D.ζ j * D.Z j * Asym D.msq m * D.Gam j m =
      (1 + D.ζ j) * (1 - D.zp j * D.eps j (D.tails j) m) := by
    rw [show D.ζ j * D.Z j * Asym D.msq m * D.Gam j m =
      D.ζ j * (D.Z j * Asym D.msq m * D.Gam j m) by ring, hG]
    unfold zp; field_simp; ring
  rw [this]; exact mul_ne_zero hζ1 hden

/-- `Z_{j+1} Γ^int_{j+1} = C_{j+1} + Z_j R_{j,j+1} + w_{j+1}` for `j + 1 < N`. -/
theorem Z_Gint (hζ : ∀ i, ‖D.ζ i‖ ≤ 1 / 2) {j : ℕ} (hjN : j + 1 < D.N) :
    D.Z (j + 1) • D.Gint j =
      ofR (D.C (j + 1)) + D.Z j • D.tails j (j + 1) + D.wLow j (D.tails j) (j + 1) := by
  simp only [Gint, if_pos hjN, smul_smul, mul_inv_cancel₀ (Z_ne_zero hζ (j + 1)), one_smul]
  simp [wSc, hjN]

theorem tW_le_Sj {q : ℕ} {θ : ℝ} (hθ : 0 < θ) (hL : 1 ≤ D.L) {j : ℕ} (hjN : j + 1 ≤ D.N) :
    D.tW q j (j + 1) ≤ θ ^ ((D.L : ℝ) / 256) * D.Sj q θ j := by
  have h1 : Wt θ D.L 1 * D.tW q j (j + 1) ≤ D.Sj q θ j := by
    have := single_le_sum (f := fun r => Wt θ D.L (r - j) * D.tW q j r)
      (fun r _ => mul_nonneg (Wt_pos hθ _ _).le (tW_nonneg hL q j r))
      (show j + 1 ∈ Ioc j D.N by rw [mem_Ioc]; omega)
    simp only [show j + 1 - j = 1 by omega] at this
    exact this
  have hW : Wt θ D.L 1 * θ ^ ((D.L : ℝ) / 256) = 1 := by
    rw [Wt, ← Real.rpow_add hθ, pow_one, show -(D.L : ℝ) / 256 + (D.L : ℝ) / 256 = 0 by ring,
      Real.rpow_zero]
  have := tW_nonneg (D := D) hL q j (j + 1)
  have hp := Real.rpow_nonneg hθ.le ((D.L : ℝ) / 256)
  calc D.tW q j (j + 1) = θ ^ ((D.L : ℝ) / 256) * (Wt θ D.L 1 * D.tW q j (j + 1)) := by
        rw [← mul_assoc, mul_comm (θ ^ _), hW, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 hp

/-- The conclusions of `thm:main` at step `j`. -/
structure Concl (D : Data d n) (q : ℕ) (ζbar K : ℝ) (j : ℕ) : Prop where
  den_eps : ∀ m, 1 - D.zp j * D.eps j (D.tails j) m ≠ 0
  den : ∀ m, 1 + D.ζ j * D.Z j * Asym D.msq m * D.Gam j m ≠ 0
  split : ∀ m, D.absorbed j m = D.Gint j m + D.Gam (j + 1) m
  range : j + 1 < D.N → 2 * rng (D.Gint j) < D.L ^ (j + 1)
  close : j + 1 < D.N →
    snorm D.L q j (D.Z (j + 1) • D.Gint j - ofR (D.C (j + 1))) ≤ K * D.Mz (j + 1)
  first : j + 1 < D.N →
    snorm D.L q j (D.Z (j + 1) • D.Gint j - ofR (D.C (j + 1)) -
        D.ζ j • (Cle D.C j * (1 - Ehat D.msq D.C j))) ≤
      K * (‖D.ζ j‖ ^ 2 + ζbar ^ ((D.L : ℝ) / 256) * D.Mz (j + 1))
  /-- (vii): the standard part `Γ^+_{j+1} - C_{j+1} = w_{j+1}`. -/
  plus : j + 1 < D.N → snorm D.L q j (D.wLow j (D.tails j) (j + 1)) ≤ K * ‖D.ζ j‖
  /-- (vii): the rest `Γ^-_{j+1} = Z_j R_{j,j+1}`. -/
  minus : j + 1 < D.N →
    snorm D.L q j (D.Z j • D.tails j (j + 1)) ≤ K * ζbar ^ ((D.L : ℝ) / 256) * D.Mz j
  /-- (vi): (iv) at the last scale, at all momenta. -/
  last : j + 1 = D.N →
    snorm D.L q j (D.Z (j + 1) • D.Gint j - ofR (D.C (j + 1))) ≤ 2 * K * D.Mz (j + 1)

end Data

open Data

/-- `thm:main`(i),(iii),(iv),(v). -/
theorem thm_main {d : ℕ} {q L : ℕ} {c₂ : ℝ} (hd : 2 ≤ d) (hq : 2 ≤ q) (hL : 7 ≤ L)
    (hc₂ : 0 ≤ c₂) :
    ∃ ζbar : ℝ, 0 < ζbar ∧ ζbar ≤ 1 / 8 ∧ ∃ K : ℝ, ∀ (n : ℕ) [NeZero n] (D : Data d n), D.L = L →
      n = L ^ D.N → StdHyp L D.N D.msq D.C → StdLoc L D.N q D.msq c₂ D.C →
      D.msq ≤ (L : ℝ) ^ (-(2 * ((D.N : ℝ) - 1))) → (∀ i, ‖D.ζ i‖ ≤ ζbar) →
      ∀ j, j < D.N → D.Concl q ζbar K j := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  obtain ⟨θ, hG⟩ := exists_theta (L : ℝ) (cexp d q) c₂ (Crho d L) hL0 hc₂ (Crho_nonneg d hL0.le)
  have hθ := hG.pos
  have hθ1 : θ ≤ 1 := by linarith [hG.le8]
  set K₁ := K1 (L : ℝ) (cexp d q) c₂ θ
  have hK1 : 0 ≤ K₁ := K1_nonneg hL0.le hc₂ hθ.le
  refine ⟨θ, hθ, hG.le8, 2 * K₁ + 10 * c₂, fun n _ D hDL hn hstd hloc hmsq hζ j hj => ?_⟩
  subst hDL
  have hζ2 : ∀ i, ‖D.ζ i‖ ≤ 1 / 2 := fun i => by linarith [hζ i, hG.le8]
  have hL1 : 1 ≤ D.L := by omega
  have H0 : D.StepHyp q c₂ θ 0 := ⟨hstd, hloc, hL, hn, hq, hd, hmsq, by omega,
    tailRange_zero hL1, hθ, hθ1⟩
  obtain ⟨H, hS⟩ := induction hG hζ H0 j hj
  -- `C_ρ 𝒮_j ≤ 1` and the denominators
  have hMz : D.Mz j ≤ θ := Mz_le hθ.le fun i _ => hζ i
  have hS1 : Crho d D.L * D.Sj q θ j ≤ 1 := by
    have := hG.small
    calc Crho d D.L * D.Sj q θ j ≤ Crho d D.L * (2 * K₁ * θ) :=
          mul_le_mul_of_nonneg_left (hS.trans (mul_le_mul_of_nonneg_left hMz (by positivity)))
            (Crho_nonneg d hL0.le)
      _ ≤ 1 := by simp only [K₁, K1]; linarith
  have hden : ∀ m, 1 - D.zp j * D.eps j (D.tails j) m ≠ 0 := fun m h => by
    have h1 := norm_zp_eps_le H (hζ j) hG.le8 hS1 m
    have : D.zp j * D.eps j (D.tails j) m = 1 := by linear_combination -h
    rw [this, norm_one] at h1; norm_num at h1
  have hS0 := Sj_nonneg (D := D) (q := q) (j := j) hθ hL1
  have hzp := norm_zp_le (D := D) (hζ2 j)
  have hzp2 : ‖D.zp j‖ ≤ 1 / 2 := by linarith [hζ j, hG.le8]
  have hθL : θ ^ ((D.L : ℝ) / 256) ≤ 1 := Real.rpow_le_one hθ.le hθ1 (by positivity)
  have hθL0 : 0 ≤ θ ^ ((D.L : ℝ) / 256) := Real.rpow_nonneg hθ.le _
  have hMz1 : D.Mz j ≤ D.Mz (j + 1) := Mz_mono (by omega)
  have hζMz : ‖D.ζ j‖ ≤ D.Mz (j + 1) := norm_le_Mz (by omega)
  refine ⟨hden, fun m => den_ne_zero H hζ2 m (hden m),
    fun m => split hstd (by omega) (Z_ne_zero hζ2 j) (one_add_ne_zero (hζ2 j)) m (hden m),
    fun hjN => two_rng_Gint_lt hstd hL1 hn hjN, fun hjN => ?_, fun hjN => ?_, fun hjN => ?_,
    fun hjN => ?_, fun hjN => ?_⟩
  · -- (iv)
    rw [Z_Gint hζ2 hjN, show ofR (D.C (j + 1)) + D.Z j • D.tails j (j + 1) +
      D.wLow j (D.tails j) (j + 1) - ofR (D.C (j + 1)) =
      D.Z j • D.tails j (j + 1) + D.wLow j (D.tails j) (j + 1) by abel]
    refine (snorm_add_le hL0 _ _).trans ?_
    rw [snorm_smul hL0]
    have h1 : ‖D.Z j‖ * snorm (D.L : ℝ) q j (D.tails j (j + 1)) ≤
        θ ^ ((D.L : ℝ) / 256) * D.Sj q θ j := by
      have := tW_le_Sj (D := D) (q := q) hθ hL1 (show j + 1 ≤ D.N by omega)
      simpa [tW] using this
    have h2 := snorm_wLow_succ_le H hjN hzp2
    calc ‖D.Z j‖ * snorm (D.L : ℝ) q j (D.tails j (j + 1)) +
          snorm (D.L : ℝ) q j (D.wLow j (D.tails j) (j + 1))
        ≤ θ ^ ((D.L : ℝ) / 256) * (2 * K₁ * D.Mz j) + 2 * c₂ * (2 * ‖D.ζ j‖) := by
          refine add_le_add (h1.trans (mul_le_mul_of_nonneg_left hS hθL0)) (h2.trans ?_)
          exact mul_le_mul_of_nonneg_left hzp (by positivity)
      _ ≤ 1 * (2 * K₁ * D.Mz (j + 1)) + 4 * c₂ * D.Mz (j + 1) := by
          have := Mz_nonneg (D := D) j
          have : 0 ≤ 2 * K₁ * D.Mz (j + 1) := by have := Mz_nonneg (D := D) (j + 1); positivity
          nlinarith
      _ ≤ (2 * K₁ + 10 * c₂) * D.Mz (j + 1) := by
          have := Mz_nonneg (D := D) (j + 1); nlinarith
  · -- (v)
    have hO := snorm_std_word_le hstd hloc hL1 hj (D.tails j) 0
    rw [wordVal_std] at hO
    simp only [pow_zero, mul_one] at hO
    rw [Z_Gint hζ2 hjN, show ofR (D.C (j + 1)) + D.Z j • D.tails j (j + 1) +
      D.wLow j (D.tails j) (j + 1) - ofR (D.C (j + 1)) -
        D.ζ j • (Cle D.C j * (1 - Ehat D.msq D.C j)) =
      D.Z j • D.tails j (j + 1) + ((D.wLow j (D.tails j) (j + 1) -
        D.zp j • (Cle D.C j * (1 - Ehat D.msq D.C j))) +
        (D.zp j - D.ζ j) • (Cle D.C j * (1 - Ehat D.msq D.C j))) by
      rw [sub_smul]; abel]
    refine (snorm_add_le hL0 _ _).trans ?_
    refine (add_le_add le_rfl (snorm_add_le hL0 _ _)).trans ?_
    rw [snorm_smul hL0, snorm_smul hL0]
    have h1 : ‖D.Z j‖ * snorm (D.L : ℝ) q j (D.tails j (j + 1)) ≤
        θ ^ ((D.L : ℝ) / 256) * D.Sj q θ j := by
      have := tW_le_Sj (D := D) (q := q) hθ hL1 (show j + 1 ≤ D.N by omega)
      simpa [tW] using this
    have h2 := snorm_wLow_succ_first_le H hjN hzp2
    have h3 := norm_zp_sub_le (D := D) (hζ2 j)
    have hzp' : ‖D.zp j‖ ^ 2 ≤ 4 * ‖D.ζ j‖ ^ 2 := by nlinarith [norm_nonneg (D.zp j)]
    have hOn := snorm_nonneg hL0 (q := q) (s := j) (Cle D.C j * (1 - Ehat D.msq D.C j))
    calc ‖D.Z j‖ * snorm (D.L : ℝ) q j (D.tails j (j + 1)) +
          (snorm (D.L : ℝ) q j (D.wLow j (D.tails j) (j + 1) -
            D.zp j • (Cle D.C j * (1 - Ehat D.msq D.C j))) +
          ‖D.zp j - D.ζ j‖ * snorm (D.L : ℝ) q j (Cle D.C j * (1 - Ehat D.msq D.C j)))
        ≤ θ ^ ((D.L : ℝ) / 256) * (2 * K₁ * D.Mz j) +
            (2 * c₂ * (4 * ‖D.ζ j‖ ^ 2) + 2 * ‖D.ζ j‖ ^ 2 * c₂) := by
          refine add_le_add (h1.trans (mul_le_mul_of_nonneg_left hS hθL0)) (add_le_add ?_ ?_)
          · exact h2.trans (mul_le_mul_of_nonneg_left hzp' (by positivity))
          · exact mul_le_mul h3 hO hOn (by positivity)
      _ ≤ (2 * K₁ + 10 * c₂) * (‖D.ζ j‖ ^ 2 + θ ^ ((D.L : ℝ) / 256) * D.Mz (j + 1)) := by
          have := Mz_nonneg (D := D) j
          have hm : θ ^ ((D.L : ℝ) / 256) * D.Mz j ≤ θ ^ ((D.L : ℝ) / 256) * D.Mz (j + 1) :=
            mul_le_mul_of_nonneg_left hMz1 hθL0
          have : 0 ≤ θ ^ ((D.L : ℝ) / 256) * D.Mz j := by positivity
          nlinarith [sq_nonneg ‖D.ζ j‖]
  · -- (vii), standard part
    have h2 := snorm_wLow_succ_le H hjN hzp2
    have := Mz_nonneg (D := D) j
    calc snorm (D.L : ℝ) q j (D.wLow j (D.tails j) (j + 1)) ≤ 2 * c₂ * (2 * ‖D.ζ j‖) :=
          h2.trans (mul_le_mul_of_nonneg_left hzp (by positivity))
      _ ≤ (2 * K₁ + 10 * c₂) * ‖D.ζ j‖ := by nlinarith [norm_nonneg (D.ζ j)]
  · -- (vii), the rest
    rw [snorm_smul hL0]
    have h1 : ‖D.Z j‖ * snorm (D.L : ℝ) q j (D.tails j (j + 1)) ≤
        θ ^ ((D.L : ℝ) / 256) * D.Sj q θ j := by
      have := tW_le_Sj (D := D) (q := q) hθ hL1 (show j + 1 ≤ D.N by omega)
      simpa [tW] using this
    have hM0 := Mz_nonneg (D := D) j
    calc ‖D.Z j‖ * snorm (D.L : ℝ) q j (D.tails j (j + 1))
        ≤ θ ^ ((D.L : ℝ) / 256) * (2 * K₁ * D.Mz j) :=
          h1.trans (mul_le_mul_of_nonneg_left hS hθL0)
      _ ≤ (2 * K₁ + 10 * c₂) * θ ^ ((D.L : ℝ) / 256) * D.Mz j := by
          have : 0 ≤ θ ^ ((D.L : ℝ) / 256) * D.Mz j := by positivity
          nlinarith
  · -- (vi)
    have hZ1 := Z_ne_zero hζ2 (j + 1)
    have hnot : ¬ j + 1 < D.N := by omega
    have hW : D.wSc j (D.tails j) (j + 1) = D.wTot j (D.tails j) := by
      have hI : Ico (j + 1) D.N = ∅ := by rw [← hjN]; exact Ico_self _
      simp [wSc, wTop, hnot, hI]
    have hid : D.Z (j + 1) • D.Gint j - ofR (D.C (j + 1)) =
        D.Z j • D.tails j (j + 1) + D.wSc j (D.tails j) (j + 1) := by
      funext m
      have hGi : D.Gint j m = D.absorbed j m := by simp [Gint, hnot]
      have hI : Ioc j D.N = {j + 1} := by ext k; simp only [mem_Ioc, mem_singleton]; omega
      rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hGi, absorbed_eq hstd (by omega)
        (Z_ne_zero hζ2 j) (one_add_ne_zero (hζ2 j)) m (hden m), hW]
      simp only [Cgt_apply, hI, sum_singleton, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ofR]
      rw [← mul_assoc, mul_inv_cancel₀ hZ1, one_mul]; ring
    rw [hid]
    refine (snorm_add_le hL0 _ _).trans ?_
    rw [snorm_smul hL0]
    have h1 : ‖D.Z j‖ * snorm (D.L : ℝ) q j (D.tails j (j + 1)) ≤
        θ ^ ((D.L : ℝ) / 256) * D.Sj q θ j := by
      have := tW_le_Sj (D := D) (q := q) hθ hL1 (show j + 1 ≤ D.N by omega)
      simpa [tW] using this
    have hws := word_sum_le hG hζ H hS
    have hIcc : Icc (j + 1) D.N = {j + 1} := by rw [← hjN]; exact Icc_self _
    rw [hIcc, sum_singleton, show j + 1 - 1 - j = 0 by omega, show j + 1 - 1 = j by omega] at hws
    have hW0 := one_le_Wt hθ hθ1 hL0.le 0
    have hsn := snorm_nonneg hL0 (q := q) (s := j) (D.wSc j (D.tails j) (j + 1))
    have h2 : snorm (D.L : ℝ) q j (D.wSc j (D.tails j) (j + 1)) ≤ K₁ * ‖D.ζ j‖ := by nlinarith
    have hM0 := Mz_nonneg (D := D) j
    have : 0 ≤ θ ^ ((D.L : ℝ) / 256) * D.Mz j := by positivity
    calc ‖D.Z j‖ * snorm (D.L : ℝ) q j (D.tails j (j + 1)) +
          snorm (D.L : ℝ) q j (D.wSc j (D.tails j) (j + 1))
        ≤ θ ^ ((D.L : ℝ) / 256) * (2 * K₁ * D.Mz j) + K₁ * ‖D.ζ j‖ :=
          add_le_add (h1.trans (mul_le_mul_of_nonneg_left hS hθL0)) h2
      _ ≤ 2 * (2 * K₁ + 10 * c₂) * D.Mz (j + 1) := by
          have := Mz_nonneg (D := D) (j + 1)
          have : θ ^ ((D.L : ℝ) / 256) * D.Mz j ≤ D.Mz (j + 1) := by nlinarith
          nlinarith

end

end DressedFRD
