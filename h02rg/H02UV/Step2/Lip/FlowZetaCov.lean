import Step2.Flow.FlowHV

/-!
# The dressed covariance at the origin, explicit in `L`

`frd_moment_unif`: `frd_moment` with the constant written as `c L²`, `c` independent of `L`.

`Zcov_hist`: along a history, `|Z_{j+1} Γ^int_j(x, y)| ≤ C₄ L² + K M_z`, with `C₄` independent of `L`
and of `ℓ` (the field scale). This replaces the field-scale bound `|Z_{j+1} C_j(x,x)| ≤ ℓ²/16`
(`GoodCov2`), which is of order `L⁸` for the admissible `ℓ`, in the size of the dressed gradient
coupling `ζ_{j+1} ≈ -ǧ_j Z_{j+1} C_j(e, 0)`.
-/

namespace Step2

open Step

noncomputable section

open Finset MeasureTheory Set FRD Grassmann DressedFRD DressedFRD.Data Step2.D2

theorem frd_moment_unif (P : PtFamily) {d : ℕ} (hd : 1 ≤ d) (M : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ {L : ℕ}, 7 ≤ L → ∀ (n : ℕ) [NeZero n] (N : ℕ) (msq : ℝ), n = L ^ N →
      0 < msq → ∀ k, 1 ≤ k → k < N → ∀ a ≤ 2 * M,
        avg (fun m : Torus d n => pnorm m ^ a * frdC P msq L N k m) ≤
          c * (L : ℝ) ^ 2 * (L : ℝ) ^ (-(((k - 1 : ℕ) : ℝ) * ((d : ℝ) - 2 + a))) := by
  set r := M + d + 1
  obtain ⟨B, hB0, hB⟩ := wt_Ioc_le P (d := d) hd r
  set E := 1 + (16 * (d : ℝ)) ^ r * (2 * 5 ^ d * (Real.pi / 2) ^ (2 * r : ℝ))
  have hE : 0 ≤ E := by positivity
  refine ⟨B / 4 * E, by positivity, fun {L} hL n _ N msq hn hmsq k hk1 hkN a ha => ?_⟩
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hL1 : 1 ≤ L := by omega
  set R : ℝ := (L : ℝ) ^ (k - 1)
  have hR : 0 < R := by positivity
  set Bk := B * ((L : ℝ) ^ k / 2) ^ 2
  have hBk : 0 ≤ Bk := by positivity
  have hw := frdC_of_lt P (d := d) (n := n) (msq := msq) (L := L) hkN
  have hlow0 := lowEnd_nonneg (show (0 : ℝ) ≤ L by positivity) k
  have hlowb : lowEnd L k ≤ (L : ℝ) ^ k / 2 := by
    have := lowEnd_le (show (1 : ℝ) ≤ L by exact_mod_cast hL1) k; linarith [this]
  have hpt : ∀ m : Torus d n, frdC P msq L N k m ≤
      Bk * ((1 + lowEnd L k ^ 2 * lam m / (4 * d)) ^ r)⁻¹ := fun m => by
    rw [hw]; exact hB n msq hmsq.le _ _ hlow0 hlowb m
  have hX1 : ∀ m : Torus d n, ((1 + lowEnd L k ^ 2 * lam m / (4 * d)) ^ r)⁻¹ ≤ 1 := fun m => by
    have := lam_nonneg m
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by
      have : 0 ≤ lowEnd L k ^ 2 * lam m / (4 * d) := by positivity
      linarith))
  have hnR : 7 * R ≤ n := by
    rw [hn]; push_cast
    have : (L : ℝ) ^ N = (L : ℝ) ^ 2 * R * (L : ℝ) ^ (N - k - 1) := by
      simp only [R]; rw [← pow_add, ← pow_add]; congr 1; omega
    rw [this]
    have h1 : (1 : ℝ) ≤ (L : ℝ) ^ (N - k - 1) := one_le_pow₀ (by exact_mod_cast hL1)
    have h7 : (7 : ℝ) ≤ L := by exact_mod_cast hL
    have : (7 : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
    have : 7 * R ≤ (L : ℝ) ^ 2 * R := by nlinarith
    nlinarith
  have hab : (d : ℝ) + a < 2 * r := by
    have : (a : ℝ) ≤ 2 * M := by exact_mod_cast ha
    simp only [r]; push_cast; linarith
  have hmain := avg_pnorm_pow_le (d := d) (n := n) hd (w := frdC P msq L N k) (B := Bk)
    (B' := Bk * (16 * d) ^ r) (R := R) a r hR hnR hab (frdC_nonneg P hmsq.le k)
    (fun m => (hpt m).trans (mul_le_of_le_one_right hBk (hX1 m))) (by positivity)
    (fun m _ => by
      calc frdC P msq L N k m * (R * pnorm m) ^ (2 * r)
          ≤ Bk * ((1 + lowEnd L k ^ 2 * lam m / (4 * d)) ^ r)⁻¹ * (R * pnorm m) ^ (2 * r) :=
            mul_le_mul_of_nonneg_right (hpt m) (pow_nonneg (mul_nonneg hR.le (pnorm_nonneg m)) _)
        _ = Bk * (((1 + lowEnd L k ^ 2 * lam m / (4 * d)) ^ r)⁻¹ * (R * pnorm m) ^ (2 * r)) := by
            ring
        _ ≤ Bk * (16 * d) ^ r :=
            mul_le_mul_of_nonneg_left (decay_factor hd hL1 r hk1 m) hBk)
  -- the constant
  have htail : tailC d (2 * r - a) ≤ 2 * 5 ^ d * (Real.pi / 2) ^ (2 * r : ℝ) := by
    have hda : (d : ℝ) + 1 ≤ 2 * r - a := by
      have : (a : ℝ) ≤ 2 * M := by exact_mod_cast ha
      simp only [r]; push_cast; linarith
    refine (tailC_le hda).trans ?_
    have : (Real.pi / 2) ^ ((2 * r : ℝ) - a) ≤ (Real.pi / 2) ^ (2 * r : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three])
        (by have := Nat.cast_nonneg (α := ℝ) a; linarith)
    have h5 : (0 : ℝ) ≤ 2 * 5 ^ d := by positivity
    simpa using mul_le_mul_of_nonneg_left this h5
  have hRpow : Bk * R ^ (-((a : ℝ) + d)) =
      B / 4 * (L : ℝ) ^ 2 * (L : ℝ) ^ (-(((k - 1 : ℕ) : ℝ) * ((d : ℝ) - 2 + a))) := by
    simp only [Bk, R]
    rw [← Real.rpow_natCast (L : ℝ) (k - 1), ← Real.rpow_mul hL0.le, div_pow, ← pow_mul,
      ← Real.rpow_natCast (L : ℝ) (k * 2), ← Real.rpow_natCast (L : ℝ) 2]
    have : (L : ℝ) ^ ((k * 2 : ℕ) : ℝ) * (L : ℝ) ^ (((k - 1 : ℕ) : ℝ) * -((a : ℝ) + d)) =
        (L : ℝ) ^ ((2 : ℕ) : ℝ) * (L : ℝ) ^ (-(((k - 1 : ℕ) : ℝ) * ((d : ℝ) - 2 + a))) := by
      rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]
      congr 1; push_cast [Nat.cast_sub hk1]; ring
    calc B * ((L : ℝ) ^ ((k * 2 : ℕ) : ℝ) / 2 ^ 2) * (L : ℝ) ^ (((k - 1 : ℕ) : ℝ) * -((a : ℝ) + d))
        = B / 4 * ((L : ℝ) ^ ((k * 2 : ℕ) : ℝ) *
            (L : ℝ) ^ (((k - 1 : ℕ) : ℝ) * -((a : ℝ) + d))) := by ring
      _ = _ := by rw [this]; ring
  have hRp : 0 ≤ R ^ (-((a : ℝ) + d)) := Real.rpow_nonneg hR.le _
  calc avg (fun m : Torus d n => pnorm m ^ a * frdC P msq L N k m)
      ≤ (Bk + Bk * (16 * d) ^ r * tailC d (2 * r - a)) * R ^ (-((a : ℝ) + d)) := hmain
    _ ≤ (Bk * E) * R ^ (-((a : ℝ) + d)) := by
        refine mul_le_mul_of_nonneg_right ?_ hRp
        simp only [E]
        have : Bk * (16 * d) ^ r * tailC d (2 * r - a) ≤
            Bk * (16 * d) ^ r * (2 * 5 ^ d * (Real.pi / 2) ^ (2 * r : ℝ)) :=
          mul_le_mul_of_nonneg_left htail (by positivity)
        nlinarith
    _ = E * (Bk * R ^ (-((a : ℝ) + d))) := by ring
    _ = _ := by rw [hRpow]; ring

/-- **The dressed covariance along a history, explicit in `L`.** -/
theorem Zcov_hist : ∃ C₄ : ℝ, 0 ≤ C₄ ∧ ∀ (L : ℕ) [NeZero L], 49 ≤ L →
    ∃ ζbar : ℝ, 0 < ζbar ∧ ∃ K : ℝ, 0 ≤ K ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → 1 ≤ N →
      0 < R.msq → R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) → R.ρ ≤ ζbar →
      ∀ j, j + 1 < N → (∀ i ≤ j, ValidAt R i) → ∀ t : Flow2.Hist.Seq (Xs R), ∀ x y,
        ‖stZ' R (rawHist R j t) * stCov R j (rawHist R j t) x y‖ ≤
          C₄ * (L : ℝ) ^ 2 + K * (dData L N R.msq (zh R j t)).Mz (j + 1) := by
  obtain ⟨c, hc, hmom⟩ := frd_moment_unif Pc (d := 2) (by norm_num) 0
  refine ⟨c, hc, fun L _ hL => ?_⟩
  obtain ⟨ζ₀, hζ₀, -, K, hK⟩ := thm_main_frd Pc (d := 2) le_rfl (q := 4) (by norm_num)
    (by omega : 7 ≤ L)
  refine ⟨ζ₀, hζ₀, max K 0, le_max_right _ _, fun N R _ _ hP hN hm0 hm hρ j hj hV t x y => ?_⟩
  obtain ⟨hz, -⟩ := hist_dData_hyps R hP hV t
  have hc' : (dData L N R.msq (zh R j t)).Concl 4 ζ₀ K j :=
    (hK (L ^ N) N R.msq (zh R j t) hN rfl hm0 hm).1 (fun i => (hz i).trans hρ) j (by omega)
  have hclose := hc'.close hj
  rw [stZ'_eq_dData R hV t, stCov_eq_dData R hP t le_rfl]
  set D := dData L N R.msq (zh R j t)
  show ‖D.Z (j + 1) * kern (D.Gint j) (x - y)‖ ≤ _
  rw [← kern_smul]
  have e : D.Z (j + 1) • D.Gint j = ofR (D.C (j + 1)) + (D.Z (j + 1) • D.Gint j - ofR (D.C (j + 1))) := by
    abel
  rw [e, kern_add]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_kern_le_avg _ _).trans ?_
    have h := hmom (L := L) (by omega) (L ^ N) N R.msq rfl hm0 (j + 1) (by omega) hj 0 (by norm_num)
    have e1 : (fun m => ‖ofR (D.C (j + 1)) m‖) =
        fun m => pnorm m ^ (0 : ℕ) * frdC Pc R.msq L N (j + 1) m := by
      funext m
      simp only [ofR, Complex.norm_real, Real.norm_eq_abs, pow_zero, one_mul]
      exact abs_of_nonneg (frdC_nonneg Pc hm0.le (j + 1) m)
    rw [e1]
    refine h.trans (le_of_eq ?_)
    have e2 : -((((j + 1 - 1 : ℕ) : ℝ)) * (((2 : ℕ) : ℝ) - 2 + ((0 : ℕ) : ℝ))) = 0 := by
      push_cast; ring
    rw [e2, Real.rpow_zero, mul_one]
  · refine (norm_kern_le_snorm (by positivity) 4 j _ _).trans (hclose.trans ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Mz_nonneg _)

end

end Step2
