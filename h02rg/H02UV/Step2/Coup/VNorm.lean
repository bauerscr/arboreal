import Step2.Lip.CdrHol

/-!
# The norm of a coupling polynomial

`‖V_κ(Y)‖_{T_j(ℓ)} ≤ |Y| (c_M ℓ² (|ν| + (|z| + |y|) h^{-2}) + d² |g| ℓ⁴ h^{-2})` with `h = L^j`
(`Tj_Vcoup_le`). For a `j`-block (`|Y| = h^d`) and `ℓ = ℓ₀ h^{-(d-2)/2}` this is
`c(ℓ₀) (|z| + |y| + L^{2j} |ν| + L^{-(d-2)j} |g|)`: the dimensionless couplings.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

theorem tn_sum' {ι : Type*} (j : ℕ) {ℓ : ℝ} (s : Finset ι) (F : ι → Alg d L N) (t : ι → ℝ)
    (ht : ∀ i ∈ s, 0 ≤ t i) (hF : ∀ i ∈ s, Tj d (L : ℝ) j ℓ (F i) ≤ ENNReal.ofReal (t i)) :
    Tj d (L : ℝ) j ℓ (∑ i ∈ s, F i) ≤ ENNReal.ofReal (∑ i ∈ s, t i) := by
  refine (Loc.tNorm_sum_le _ _).trans ((sum_le_sum hF).trans ?_)
  rw [ENNReal.ofReal_sum_of_nonneg ht]

theorem norm_coupC_le (κ : Coup) {h : ℝ} (hh : 0 < h) (M : Mono d) :
    ‖coupC κ M‖ * (h ^ M.deg)⁻¹ ≤ ‖κ.nu‖ + (‖κ.z‖ + ‖κ.y‖) * (h ^ 2)⁻¹ := by
  have h2 : 0 ≤ (h ^ 2)⁻¹ := by positivity
  have hy : ‖-κ.y / 2‖ ≤ ‖κ.y‖ := by
    rw [norm_div, norm_neg, RCLike.norm_ofNat]; linarith [norm_nonneg κ.y]
  have hn := norm_nonneg κ.nu
  have hz := norm_nonneg κ.z
  have hyy := norm_nonneg κ.y
  cases M with
  | c => simp [coupC, Mono.deg]; nlinarith
  | a1 i => simp [coupC]; positivity
  | b1 i => simp [coupC]; positivity
  | a2 s =>
    simp only [coupC, Mono.deg]
    split_ifs
    · nlinarith [mul_le_mul_of_nonneg_right hy h2]
    · simp; positivity
  | b2 s =>
    simp only [coupC, Mono.deg]
    split_ifs
    · nlinarith [mul_le_mul_of_nonneg_right hy h2]
    · simp; positivity
  | m2 i k =>
    simp only [coupC, Mono.deg]
    split_ifs
    · nlinarith
    · simp; positivity

/-- **The norm of `V_κ(Y)`.** -/
theorem Tj_Vcoup_le (hd : 1 ≤ d) (j : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) (κ : Coup) (Y : Finset (Lam d L N)) :
    Tj d (L : ℝ) j ℓ (Vcoup κ Y) ≤ ENNReal.ofReal ((Y.card : ℝ) *
      ((Fintype.card (Mono d) : ℝ) * ℓ ^ 2 * (‖κ.nu‖ + (‖κ.z‖ + ‖κ.y‖) * (((L : ℝ) ^ j) ^ 2)⁻¹) +
        (d : ℝ) ^ 2 * ‖κ.g‖ * ℓ ^ 4 * (((L : ℝ) ^ j) ^ 2)⁻¹)) := by
  have hh : (0 : ℝ) < (L : ℝ) ^ j := pow_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L))) j
  have hp2 : 2 ≤ pPhi d := by simp [pPhi]; omega
  set h := (L : ℝ) ^ j with hdef
  set A := ‖κ.nu‖ + (‖κ.z‖ + ‖κ.y‖) * (h ^ 2)⁻¹ with hA
  have hA0 : 0 ≤ A := by positivity
  unfold Vcoup unif
  simp only [zero_smul, zero_add]
  refine (Loc.tNorm_add_le _ _).trans ?_
  have h1 : Tj d (L : ℝ) j ℓ (∑ M, coupC κ M • monoSet M Y) ≤
      ENNReal.ofReal ((Y.card : ℝ) * ((Fintype.card (Mono d) : ℝ) * ℓ ^ 2 * A)) := by
    refine (tn_sum' j _ _ (fun _ => (Y.card : ℝ) * (ℓ ^ 2 * A)) (fun _ _ => by positivity)
      fun M _ => ?_).trans (le_of_eq ?_)
    · refine (Loc.tNorm_smul_le _ _).trans ?_
      have hm : Tj d (L : ℝ) j ℓ (monoSet M Y) ≤
          ENNReal.ofReal ((Y.card : ℝ) * (ℓ ^ 2 * (h ^ M.deg)⁻¹)) := by
        unfold monoSet
        refine (tn_sum' j _ _ (fun _ => ℓ ^ 2 * (h ^ M.deg)⁻¹) (fun _ _ => by positivity)
          fun x _ => tNorm_monoAt_le hp2 hh hℓ M x).trans (le_of_eq ?_)
        rw [sum_const, nsmul_eq_mul]
      refine (mul_le_mul_left' hm _).trans ?_
      rw [← ENNReal.ofReal_mul (norm_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      have := norm_coupC_le κ hh M
      calc ‖coupC κ M‖ * ((Y.card : ℝ) * (ℓ ^ 2 * (h ^ M.deg)⁻¹))
          = (Y.card : ℝ) * ℓ ^ 2 * (‖coupC κ M‖ * (h ^ M.deg)⁻¹) := by ring
        _ ≤ (Y.card : ℝ) * ℓ ^ 2 * A := mul_le_mul_of_nonneg_left this (by positivity)
        _ = (Y.card : ℝ) * (ℓ ^ 2 * A) := by ring
    · rw [sum_const, card_univ, nsmul_eq_mul]; ring
  have h2 : Tj d (L : ℝ) j ℓ (∑ i, ∑ k, coupE κ i k • mono4sSet i k Y) ≤
      ENNReal.ofReal ((Y.card : ℝ) * ((d : ℝ) ^ 2 * ‖κ.g‖ * ℓ ^ 4 * (h ^ 2)⁻¹)) := by
    refine (tn_sum' j _ _ (fun _ => (d : ℝ) * ((Y.card : ℝ) * (‖κ.g‖ * (ℓ ^ 4 * (h ^ 2)⁻¹))))
      (fun _ _ => by positivity) fun i _ => ?_).trans (le_of_eq ?_)
    · refine (tn_sum' j _ _ (fun _ => (Y.card : ℝ) * (‖κ.g‖ * (ℓ ^ 4 * (h ^ 2)⁻¹)))
        (fun _ _ => by positivity) fun k _ => ?_).trans (le_of_eq ?_)
      · refine (Loc.tNorm_smul_le _ _).trans ?_
        have hm : Tj d (L : ℝ) j ℓ (mono4sSet i k Y) ≤
            ENNReal.ofReal ((Y.card : ℝ) * (ℓ ^ 4 * (h ^ 2)⁻¹)) := by
          unfold mono4sSet
          refine (tn_sum' j _ _ (fun _ => ℓ ^ 4 * (h ^ 2)⁻¹) (fun _ _ => by positivity)
            fun x _ => tNorm_mono4s_le (by omega) hh hℓ i k x).trans (le_of_eq ?_)
          rw [sum_const, nsmul_eq_mul]
        refine (mul_le_mul_left' hm _).trans ?_
        rw [← ENNReal.ofReal_mul (norm_nonneg _)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hE : ‖coupE κ i k‖ ≤ ‖κ.g‖ := by
          unfold coupE; split_ifs
          · exact le_rfl
          · simp
        calc ‖coupE κ i k‖ * ((Y.card : ℝ) * (ℓ ^ 4 * (h ^ 2)⁻¹))
            ≤ ‖κ.g‖ * ((Y.card : ℝ) * (ℓ ^ 4 * (h ^ 2)⁻¹)) :=
              mul_le_mul_of_nonneg_right hE (by positivity)
          _ = (Y.card : ℝ) * (‖κ.g‖ * (ℓ ^ 4 * (h ^ 2)⁻¹)) := by ring
      · rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    · rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  refine (add_le_add h1 h2).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

/-! ### The activity `K♭` of the absorption step -/

/-- **`‖K♭‖_{j, A e^{-δ}} ≤ e^{2^d δ} ‖K‖_{j,A}`** for `K♭(X) = ∏_{B ⊆ X} e^{Δ(B)} K(X)` with
`‖Δ(B)‖_j ≤ δ`. -/
theorem Knorm_Kflat_le (j : ℕ) {ℓ A δ : ℝ} (hℓ : 0 < ℓ) (hA : 0 ≤ A) (hδ : 0 ≤ δ)
    (Δ : Fam d L N) (hΔ0 : ∀ b, ε (Δ b : Alg d L N) = 0)
    (hΔ : ∀ b ∈ blockIdx (L := L) (N := N) j, Tj d (L : ℝ) j ℓ (Δ b : Alg d L N) ≤ ENNReal.ofReal δ)
    (K : Act d L N) :
    Knorm j ℓ (A * Real.exp (-δ)) (fun Y => bpow j (fun b => gexp (Δ b)) Y * K Y) ≤
      ENNReal.ofReal (Real.exp (2 ^ d * δ)) * Knorm j ℓ A K := by
  have hh : (0 : ℝ) < (L : ℝ) ^ j := pow_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L))) j
  refine iSup₂_le fun X hX => ?_
  have hXc : IsConn j X := by simpa [connSets] using hX
  -- the product of exponentials
  have hP : Tj d (L : ℝ) j ℓ ((bpow j (fun b => gexp (Δ b)) X : EvR (Lam d L N)) : Alg d L N) ≤
      ENNReal.ofReal (Real.exp δ ^ nb j X) := by
    refine (tNorm_prod_le hh hℓ _ _).trans ?_
    calc ∏ b ∈ blocks j X, Tj d (L : ℝ) j ℓ ((gexp (Δ b) : EvR (Lam d L N)) : Alg d L N)
        ≤ ∏ b ∈ blocks j X, ENNReal.ofReal (Real.exp δ) :=
          prod_le_prod' fun b hb => tNorm_gexp_le hh hℓ (hΔ0 b) hδ
            (hΔ b (mem_blockIdx_of_mem_blocks hb))
      _ = ENNReal.ofReal (Real.exp δ ^ nb j X) := by
          rw [prod_const, ENNReal.ofReal_pow (Real.exp_pos _).le, nb]
  have hKX := wnorm_le_Knorm (K := K) (ℓ := ℓ) (A := A) hXc
  show ENNReal.ofReal ((A * Real.exp (-δ)) ^ (nb j X - 2 ^ d)) *
    Tj d (L : ℝ) j ℓ (((bpow j (fun b => gexp (Δ b)) X * K X : EvR (Lam d L N))) : Alg d L N) ≤ _
  set n := nb j X
  set m := n - 2 ^ d
  have hnm : (n : ℝ) ≤ m + 2 ^ d := by
    have : n ≤ m + 2 ^ d := by omega
    exact_mod_cast this
  calc ENNReal.ofReal ((A * Real.exp (-δ)) ^ m) *
        Tj d (L : ℝ) j ℓ (((bpow j (fun b => gexp (Δ b)) X * K X : EvR (Lam d L N))) : Alg d L N)
      ≤ ENNReal.ofReal ((A * Real.exp (-δ)) ^ m) *
        (ENNReal.ofReal (Real.exp δ ^ n) * Tj d (L : ℝ) j ℓ (K X : Alg d L N)) := by
        refine mul_le_mul_left' ?_ _
        rw [Subalgebra.coe_mul]
        exact (Grassmann.tNorm_mul_le hh hℓ _ _).trans (mul_le_mul_right' hP _)
    _ = ENNReal.ofReal (Real.exp (-δ) ^ m * Real.exp δ ^ n) *
        (ENNReal.ofReal (A ^ m) * Tj d (L : ℝ) j ℓ (K X : Alg d L N)) := by
        rw [mul_pow, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
        ring
    _ ≤ ENNReal.ofReal (Real.exp (2 ^ d * δ)) * Knorm j ℓ A K := by
        gcongr
        · rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
          refine Real.exp_le_exp.2 ?_
          nlinarith
        · exact hKX

end

end Step2
