import Step2.Lip.FlowLipDom

/-!
# Lipschitz bounds for one normalised step (Lipschitz bounds, part 12)

`SD` collects the inputs of the normalised step `k` (`Step2.Lip.FlowLipNorm`): the normalised
covariance `C`, the couplings `ẑ, ŷ`, the coordinates `g, μ`, the zero mode `ŵ`, and the rescaled
`𝒲^lin, D, K`. `SD.OK` are the hypotheses on one datum (the domain), with input field scale `ℓ_i`
and weight `A`.

For two data `s, s'` the outputs `K̂_{k+1}`, `𝒲̂^lin_{k+1}`, `D̂_{k+1}` differ by at most the joint
Cauchy bounds (`nK_lip`, `nWl_lip`, `nD_lip`) in terms of the input differences
* `aV`: the difference of `V♭` (`nVec_sub_le`),
* `‖δ𝒲‖`, `‖δD‖`, and the difference `cKf` of `K♭` (`nKf_sub_le`),
* `ℓ_Δ`: the field scale of the difference of the covariances.
-/

namespace Step2

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD

variable {L N : ℕ} [NeZero L]

/-- The data of a normalised step. -/
structure SD (L N : ℕ) [NeZero L] where
  C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ
  zh : ℂ
  yh : ℂ
  g : ℝ
  μ : ℝ
  w : ℂ
  W : Fam 2 L N
  D : Fam 2 L N
  K : Act 2 L N

namespace SD

variable (R : RGPar 2 L N) (k : ℕ) (s : SD L N)

/-- `V♭`. -/
abbrev V : Fam 2 L N := VfamL k (nVec R k s.zh s.yh s.g s.μ s.w)

/-- `Δ`. -/
abbrev Dl : Fam 2 L N := VfamL k (nDel R s.zh s.yh)

/-- `K♭`. -/
abbrev Kf : Act 2 L N := nKf R k s.zh s.yh s.K

/-- The outputs. -/
abbrev kap : Fin 4 → ℂ := nKap R k s.C s.zh s.yh s.g s.μ s.w s.W s.D s.K
abbrev oW : Fam 2 L N := nWl R k s.C s.zh s.yh s.g s.μ s.w s.W
abbrev oD : Fam 2 L N := nD R k s.C s.zh s.yh s.g s.μ s.w s.W s.D
abbrev oK : Act 2 L N := nK R k s.C s.zh s.yh s.g s.μ s.w s.W s.D s.K

/-- **The hypotheses on one step datum.** -/
structure OK (ℓi ℓC A cz cw cx cmu : ℝ) : Prop where
  hk : k + 2 < N
  hC : GoodCov2 k ℓC s.C
  hCt : TInv s.C
  hCs : CSym s.C
  hCsym : ∀ x y, s.C x y = s.C y x
  hzy : ‖s.zh + s.yh‖ ≤ R.ρ
  hy : ‖s.yh‖ ≤ R.ρ
  hz' : ‖s.zh‖ ≤ cz * s.g
  hy' : ‖s.yh‖ ≤ cz * s.g
  hg : 0 < s.g
  hμ : |s.μ| ≤ cmu * s.g
  hW : s.W ∈ BSub (L := L) (N := N) k
  hD : s.D ∈ BSub (L := L) (N := N) k
  hK : s.K ∈ ASub (L := L) (N := N) k
  hWn : Fnorm k ℓi s.W ≤ ENNReal.ofReal (cw * s.g ^ 2)
  hDn : Fnorm k ℓi s.D ≤ ENNReal.ofReal (cx * s.g ^ 3)
  hKn : Knorm k ℓi A s.K ≤ ENNReal.ofReal (cx * s.g ^ 3)

end SD

/-- The constant of the bound on `V♭`. -/
def cVf (ℓi cz cmu : ℝ) : ℝ := cM * ℓi ^ 2 * (cmu + 4 * cz) + 5 * ℓi ^ 4

/-- The constant of the bound on `Δ`. -/
def cDl (ℓi cz : ℝ) : ℝ := cM * ℓi ^ 2 * (8 * cz)

/-- The bound on the difference of `V♭`. -/
def aVf (ℓi dμ dv dg dn : ℝ) : ℝ := cM * ℓi ^ 2 * (dμ + 2 * dv) + 4 * ℓi ^ 4 * (8 / 7 * dg + 2 * dn)

namespace SD.OK

variable {R : RGPar 2 L N} {k : ℕ} {s : SD L N} {ℓi ℓC A cz cw cx cmu : ℝ}
  (H : SD.OK R k s ℓi ℓC A cz cw cx cmu)
include H

theorem hz8 (hcz : 0 ≤ cz) (hsmall : cz * s.g ≤ 1 / 16) : ‖s.zh + s.yh‖ ≤ 1 / 8 :=
  (norm_add_le _ _).trans (by linarith [H.hz', H.hy'])

theorem hzy2 : ‖s.zh + s.yh‖ ≤ 2 * cz * s.g :=
  (norm_add_le _ _).trans (by linarith [H.hz', H.hy'])

theorem V_mem (hL8 : 2 ^ (2 + 3) + 8 * 2 < L) : SD.V R k s ∈ BSub (L := L) (N := N) k :=
  VfamL_mem (by norm_num) hL8 (by have := H.hk; omega) _

theorem Dl_mem (hL8 : 2 ^ (2 + 3) + 8 * 2 < L) : SD.Dl R k s ∈ BSub (L := L) (N := N) k :=
  VfamL_mem (by norm_num) hL8 (by have := H.hk; omega) _

theorem Kf_mem (hL8 : 2 ^ (2 + 3) + 8 * 2 < L) : SD.Kf R k s ∈ ASub (L := L) (N := N) k :=
  Kflat_mem (by have := H.hk; omega) (H.Dl_mem hL8) (eps_VfamL k _) H.hK

/-- `‖V♭‖ ≤ c_V g`. -/
theorem V_le (hℓi : 0 < ℓi) (hcz : 0 ≤ cz) (hsmall : cz * s.g ≤ 1 / 16)
    (hm : |R.msq| * ((L : ℝ) ^ k) ^ 2 ≤ 1) :
    Fnorm k ℓi (SD.V R k s) ≤ ENNReal.ofReal (cVf ℓi cz cmu * s.g) := by
  refine (Fnorm_nVec_le R k (by have := H.hk; omega) hℓi H.hzy H.hy (H.hz8 hcz hsmall) hm
    s.g s.μ s.w).trans (ENNReal.ofReal_le_ofReal ?_)
  unfold cVf
  have hg := H.hg
  rw [abs_of_pos hg]
  have h1 := H.hμ
  have h2 := H.hzy2
  have hM : 0 ≤ cM := Nat.cast_nonneg _
  have : |s.μ| + 2 * ‖s.zh + s.yh‖ ≤ (cmu + 4 * cz) * s.g := by nlinarith
  have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ cM * ℓi ^ 2)
  nlinarith [pow_pos hℓi 4]

/-- `‖Δ‖ ≤ c_Δ g`. -/
theorem Dl_le (hℓi : 0 < ℓi) (hcz : 0 ≤ cz) (hsmall : cz * s.g ≤ 1 / 16)
    (hm : |R.msq| * ((L : ℝ) ^ k) ^ 2 ≤ 1) :
    Fnorm k ℓi (SD.Dl R k s) ≤ ENNReal.ofReal (cDl ℓi cz * s.g) := by
  refine (Fnorm_nDel_le R k (by have := H.hk; omega) hℓi H.hzy H.hy (H.hz8 hcz hsmall) hm).trans
    (ENNReal.ofReal_le_ofReal ?_)
  unfold cDl
  have h1 := H.hz'
  have h2 := H.hy'
  have h3 := H.hzy2
  have hM : 0 ≤ cM := Nat.cast_nonneg _
  have : 2 * ‖s.zh + s.yh‖ + 2 * ‖s.zh‖ + 2 * ‖s.yh‖ ≤ 8 * cz * s.g := by linarith
  have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ cM * ℓi ^ 2)
  nlinarith

/-- `‖K♭‖ ≤ e c_x g³` at the weight `A e^{-1/2}`. -/
theorem Kf_le (hℓi : 0 < ℓi) (hA : 0 ≤ A) (hcz : 0 ≤ cz) (hsmall : cz * s.g ≤ 1 / 16)
    (hm : |R.msq| * ((L : ℝ) ^ k) ^ 2 ≤ 1) (hΔ : cDl ℓi cz * s.g ≤ 1 / 4) :
    Knorm k ℓi (A * Real.exp (-(1 / 4))) (SD.Kf R k s) ≤
      ENNReal.ofReal (Real.exp 1 * (cx * s.g ^ 3)) := by
  have hb : ∀ b ∈ blockIdx (L := L) (N := N) k,
      Tj 2 (L : ℝ) k ℓi (SD.Dl R k s b : Alg 2 L N) ≤ ENNReal.ofReal (1 / 4) := fun b hb =>
    (Tj_le_Fnorm _ hb).trans ((H.Dl_le hℓi hcz hsmall hm).trans (ENNReal.ofReal_le_ofReal hΔ))
  have h := Knorm_Kflat_le (d := 2) k hℓi hA (by norm_num : (0 : ℝ) ≤ 1 / 4) (SD.Dl R k s)
    (eps_VfamL k _) hb s.K
  refine h.trans ?_
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  refine mul_le_mul' (le_of_eq ?_) H.hKn
  norm_num

end SD.OK

/-! ### Differences of the inputs -/

section Diff

variable {R : RGPar 2 L N} {k : ℕ} {s s' : SD L N} {ℓi ℓC A cz cw cx cmu : ℝ}

/-- **The difference of `V♭`.** -/
theorem nVec_sub_le (H : SD.OK R k s ℓi ℓC A cz cw cx cmu) (H' : SD.OK R k s' ℓi ℓC A cz cw cx cmu)
    (hℓi : 0 < ℓi) (hcz : 0 ≤ cz) (hsmall : cz * s.g ≤ 1 / 16) (hsmall' : cz * s'.g ≤ 1 / 16)
    (hg1 : s'.g ≤ 1) (hm : |R.msq| * ((L : ℝ) ^ k) ^ 2 ≤ 1) :
    Fnorm k ℓi (SD.V R k s' - SD.V R k s) ≤ ENNReal.ofReal (aVf ℓi |s'.μ - s.μ|
      (‖s'.zh - s.zh‖ + ‖s'.yh - s.yh‖) |s'.g - s.g| ‖nCor (s'.μ : ℂ) s'.w - nCor (s.μ : ℂ) s.w‖) := by
  refine (Fnorm_nVec_sub_le R k (by have := H.hk; omega) hℓi H.hzy H.hy H'.hzy H'.hy
    (H.hz8 hcz hsmall) (H'.hz8 hcz hsmall') hm s.g s.μ s'.g s'.μ s.w s'.w
    (by rw [abs_of_pos H'.hg]; exact hg1)).trans (ENNReal.ofReal_le_ofReal ?_)
  unfold aVf
  have e : (s'.zh + s'.yh) - (s.zh + s.yh) = (s'.zh - s.zh) + (s'.yh - s.yh) := by ring
  have h1 : ‖(s'.zh + s'.yh) - (s.zh + s.yh)‖ ≤ ‖s'.zh - s.zh‖ + ‖s'.yh - s.yh‖ := by
    rw [e]; exact norm_add_le _ _
  have hM : 0 ≤ cM := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left (add_le_add_left (mul_le_mul_of_nonneg_left h1
    (by norm_num : (0 : ℝ) ≤ 2)) |s'.μ - s.μ|) (by positivity : (0 : ℝ) ≤ cM * ℓi ^ 2)
  linarith

/-- **The difference of `Δ`.** -/
theorem nDel_sub_le (H : SD.OK R k s ℓi ℓC A cz cw cx cmu) (H' : SD.OK R k s' ℓi ℓC A cz cw cx cmu)
    (hℓi : 0 < ℓi) (hcz : 0 ≤ cz) (hsmall : cz * s.g ≤ 1 / 16) (hsmall' : cz * s'.g ≤ 1 / 16)
    (hm : |R.msq| * ((L : ℝ) ^ k) ^ 2 ≤ 1) :
    Fnorm k ℓi (SD.Dl R k s' - SD.Dl R k s) ≤
      ENNReal.ofReal (cM * ℓi ^ 2 * (8 * (‖s'.zh - s.zh‖ + ‖s'.yh - s.yh‖))) := by
  have hz1 : ‖s.zh‖ ≤ 1 := H.hz'.trans (by linarith)
  have hy1 : ‖s.yh‖ ≤ 1 := H.hy'.trans (by linarith)
  refine (Fnorm_nDel_sub_le R k (by have := H.hk; omega) hℓi H.hzy H.hy H'.hzy H'.hy
    (H.hz8 hcz hsmall) (H'.hz8 hcz hsmall') hm hz1 hy1).trans (ENNReal.ofReal_le_ofReal ?_)
  have e : (s'.zh + s'.yh) - (s.zh + s.yh) = (s'.zh - s.zh) + (s'.yh - s.yh) := by ring
  have h1 : ‖(s'.zh + s'.yh) - (s.zh + s.yh)‖ ≤ ‖s'.zh - s.zh‖ + ‖s'.yh - s.yh‖ := by
    rw [e]; exact norm_add_le _ _
  have hM : 0 ≤ cM := Nat.cast_nonneg _
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  linarith

/-- **The difference of `K♭`**, at the weight `A e^{-1/2}`. -/
theorem nKf_sub_le (H : SD.OK R k s ℓi ℓC A cz cw cx cmu) (H' : SD.OK R k s' ℓi ℓC A cz cw cx cmu)
    (hℓi : 0 < ℓi) (hA : 0 < A) (hcz : 0 ≤ cz) (hsmall : cz * s.g ≤ 1 / 16)
    (hsmall' : cz * s'.g ≤ 1 / 16) (hm : |R.msq| * ((L : ℝ) ^ k) ^ 2 ≤ 1)
    (hΔ : cDl ℓi cz * s.g ≤ 1 / 4) (hΔ' : cDl ℓi cz * s'.g ≤ 1 / 4) {dK : ℝ} (hdK0 : 0 ≤ dK)
    (hdK : Knorm k ℓi A (s'.K - s.K) ≤ ENNReal.ofReal dK) (hcx : 0 ≤ cx) :
    Knorm k ℓi (A * Real.exp (-(1 / 4) * 2)) (SD.Kf R k s' - SD.Kf R k s) ≤
      ENNReal.ofReal (Real.exp 1 * dK + 4 * (Real.exp 2 * (cx * s.g ^ 3)) *
        (cM * ℓi ^ 2 * (8 * (‖s'.zh - s.zh‖ + ‖s'.yh - s.yh‖)) / (1 / 4))) := by
  have hΔn := (H.Dl_le hℓi hcz hsmall hm).trans (ENNReal.ofReal_le_ofReal hΔ)
  have hΔn' := (H'.Dl_le hℓi hcz hsmall' hm).trans (ENNReal.ofReal_le_ofReal hΔ')
  have hM : 0 ≤ cM := Nat.cast_nonneg _
  have h := Kflat_lip (d := 2) k hℓi hA (by norm_num : (0 : ℝ) < 1 / 4) (eps_VfamL k _)
    (eps_VfamL k _) hΔn hΔn' (k := cx * s.g ^ 3) (by have := H.hg; positivity) hdK0
    (by positivity) H.hKn hdK (nDel_sub_le H H' hℓi hcz hsmall hsmall' hm)
  have e1 : A * Real.exp (-(1 / 4) * 2) = A * Real.exp (-(2 * (1 / 4))) := by ring_nf
  rw [e1]
  refine h.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  norm_num

end Diff

end

end Step2
