import Step2.Map.Norm
import Step2.Map.ThetaScale

/-!
# The expectation bound with two field scales

`‖𝔼_C θ F‖_{T_{j+1}(ℓ')} ≤ q^{|𝓑_j(Y)|} ‖F‖_{T_j(ℓ)}` for a covariance with a Gram bound at the
field scale `ℓ_C` and `ℓ' + ℓ_C ≤ 2ℓ` (`EthE_succ_le2`). With `ℓ' = ℓ_C = ℓ` this is
`EthE_succ_le`. Proof: Gaussian rescaling `𝔼_C θ F = 𝔼_{λ^{-2}C} θ_λ F` with `λ = ℓ_C/ℓ'`
(`ECC_theta_scale`), the Gram bound for `λ^{-2}C` at `ℓ'`, `‖θ_λ F‖ ≤ ‖F‖_{T((1+λ)ℓ')}`
(`tNorm_thetaL_le`), monotonicity in `ℓ`, and `lem:pauli`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

section Gram

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {E : Type*} [Fintype E] [DecidableEq E] [AddAction (E → ℕ) Λ]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem gvec_smul (c : ℂ) (Fv : Λ → H) (f : Λ → ℝ) :
    gvec (fun x => c • Fv x) f = c • gvec Fv f := by
  simp only [gvec, smul_sum, smul_comm c]

theorem isGram_smul_real {C : Matrix Λ Λ ℂ} {Fv Gv : Λ → H} (hC : IsGram C Fv Gv) {c : ℝ}
    (hc : c ≠ 0) :
    IsGram (((c : ℂ) ^ 2)⁻¹ • C) (fun x => (c⁻¹ : ℂ) • Fv x) (fun x => (c⁻¹ : ℂ) • Gv x) := by
  intro x y
  rw [Matrix.smul_apply, hC x y, inner_smul_left, inner_smul_right, smul_eq_mul]
  simp only [map_inv₀, Complex.conj_ofReal]
  ring

theorem gramBound_smul_real {p : ℕ} {h ℓ : ℝ} {Fv Gv : Λ → H} (hB : GramBound E p h ℓ Fv Gv)
    {c : ℝ} (hc : 0 < c) :
    GramBound E p h (c⁻¹ * ℓ) (fun x => (c⁻¹ : ℂ) • Fv x) (fun x => (c⁻¹ : ℂ) • Gv x) := by
  intro a ha x
  have hn : ‖((c⁻¹ : ℝ) : ℂ)‖ = c⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hc)]
  have e : ((c : ℂ))⁻¹ = ((c⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  obtain ⟨h1, h2⟩ := hB a ha x
  rw [gvec_smul, gvec_smul, norm_smul, norm_smul, e, hn, mul_assoc]
  exact ⟨mul_le_mul_of_nonneg_left h1 (inv_pos.2 hc).le,
    mul_le_mul_of_nonneg_left h2 (inv_pos.2 hc).le⟩

end Gram

/-- **The two-scale expectation bound.** -/
theorem EthE_succ_le2 (hd : 1 ≤ d) (hL : pauliL0 d ≤ L) {j : ℕ} (hj : j < N) {ℓ ℓ' ℓC : ℝ}
    (hℓ' : 0 < ℓ') (hℓC : 0 < ℓC) (hsum : ℓ' + ℓC ≤ 2 * ℓ)
    {C : Matrix (Lam d L N) (Lam d L N) ℂ} (hC : GoodCov2 j ℓC C)
    {Y : Finset (Lam d L N)} {F : Alg d L N} (hF : F ∈ NX (↑Y : Set (Lam d L N))) :
    Tj d (L : ℝ) (j + 1) ℓ' (ECC C (theta F)) ≤
      ENNReal.ofReal (pq d ^ nb j Y) * Tj d (L : ℝ) j ℓ F := by
  obtain ⟨H, _, _, Fv, Gv, hG, hB⟩ := hC.gram
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hh : (0 : ℝ) < (L : ℝ) ^ (j + 1) := by positivity
  have hℓ : 0 < ℓ := by linarith
  set c : ℝ := ℓC / ℓ' with hc
  have hc0 : 0 < c := by positivity
  have hcℓ : c⁻¹ * ℓC = ℓ' := by rw [hc]; field_simp
  have hB' := gramBound_smul_real hB hc0
  rw [hcℓ] at hB'
  have hG' := isGram_smul_real hG hc0.ne'
  rw [ECC_theta_scale (c := (c : ℂ)) (by exact_mod_cast hc0.ne') C F]
  have e1 : (1 + c) * ℓ' = ℓ' + ℓC := by rw [hc]; field_simp
  calc Tj d (L : ℝ) (j + 1) ℓ' (ECC (((c : ℂ) ^ 2)⁻¹ • C) (thetaL (c : ℂ) F))
      ≤ tNorm (Dir d) (pPhi d) ((L : ℝ) ^ (j + 1)) ℓ' (thetaL (c : ℂ) F) :=
        tNorm_ECC_le hh hℓ' hG' hB' _
    _ ≤ tNorm (Dir d) (pPhi d) ((L : ℝ) ^ (j + 1)) ((1 + c) * ℓ') F :=
        tNorm_thetaL_le hh hℓ' hc0.le F
    _ ≤ Tj d (L : ℝ) (j + 1) (2 * ℓ) F := by
        rw [e1]; exact tNorm_mono hh.le le_rfl (by positivity) hsum F
    _ ≤ _ := Tj_succ_two_le hd hL hj hF hℓ

end

end Step2
