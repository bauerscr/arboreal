import PtCorr2.Pair.SeedSplit
import PtCorr2.Pair.PairInitAB

/-!
# The linear-regime `ab` recursion with per-scale weights `wM(M_{a,k}, M_{b,k})`

`obs_histFromABL` runs with one fixed weight `w`. Along the reduced history the natural weights
are per scale, `wM(M_{a,k}, M_{b,k})` with `M_{•,k} = 2s_k²|β_{•,k}|`; with the fixed weights
`wM(j_x)` the `r'`-part of `V'_k` drifts relative to `M_aM_b` (`Log.md`, "the linear regime").
On the anchored reduced history every element lies in `abSub`, where the weights act by the scalar
`(wM M_a M_b).ab = (M_aM_b)^{-1}`; so a change of weights is a rescaling of the sizes:

* **`oTo_wM_rescale`**: on `abSub`, `‖F‖_{wM(M⁰)} = (M_aM_b/M⁰_aM⁰_b)‖F‖_{wM(M)}`.
* **`obs_histFromABL_wM`**: `obs_histFromABL` with per-scale weights. Inputs: `V`-sizes `m_j` in the
  weights of scale `j`, with `λ_jm_j ≤ 2λ_{j+1}m_{j+1}` (`λ_j = M_{a,j}M_{b,j}/M_{a,j₀}M_{b,j₀}`; with
  `λ_{j+1}/λ_j = 1 + O(ǧ_j)` this is the old condition up to `1 + O(ǧ)`). Outputs, in the weights of
  scale `j`: `‖𝒲_j(B)‖ ≤ c_Wr_jm_j` and `A^{(…)}‖K_j(X)‖ ≤ kseqF(8θ̄, B, r, c_Wλm)_j/λ_j`.
  Proof: `obs_histFromABL` with `w = wM(j₀)` and `m ↦ λm`, then `oTo_wM_rescale` at every scale.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

variable {L N : ℕ} [NeZero L]

/-- **Change of the `wM` weights on `abSub`.** -/
theorem oTo_wM_rescale {c : Obs.Case} {Ma0 Mb0 Ma Mb : ℝ} (hMa0 : 0 < Ma0) (hMb0 : 0 < Mb0)
    (hMa : 0 < Ma) (hMb : 0 < Mb) (j : ℕ) (ℓ : ℝ) {F : OE c (Lam 2 L N)}
    (hF : F ∈ (abSub : Subalgebra ℂ (OE c (Lam 2 L N)))) :
    oTo (wM Ma0 Mb0) j ℓ F = ENNReal.ofReal (Ma * Mb / (Ma0 * Mb0)) * oTo (wM Ma Mb) j ℓ F := by
  rw [oTo_of_ab _ _ _ hF, oTo_of_ab _ _ _ hF]
  have hw : ∀ {x y : ℝ}, 0 < x → (wM x y).ab = ENNReal.ofReal (x * y)⁻¹ := fun {x y} hx => by
    show ENNReal.ofReal x⁻¹ * ENNReal.ofReal y⁻¹ = _
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hx.le), mul_inv]
  rw [hw hMa0, hw hMa, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  field_simp

theorem wM_ne_top (Ma Mb : ℝ) : (wM Ma Mb).a ≠ ⊤ ∧ (wM Ma Mb).b ≠ ⊤ ∧ (wM Ma Mb).ab ≠ ⊤ :=
  ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩

/-- `kseqF` as a sum over absolute scales. -/
theorem kseqF_eq_sum_Ico (θ B : ℝ) (r m : ℕ → ℝ) (j₀ : ℕ) (k₀ : ℝ) {k : ℕ} (hk : j₀ ≤ k) :
    kseqF θ B r m j₀ k₀ k = θ ^ (k - j₀) * k₀ +
      ∑ i ∈ Finset.Ico j₀ k, θ ^ (k - 1 - i) * (B * r i ^ 2 * m i) := by
  obtain ⟨d, rfl⟩ : ∃ d, k = j₀ + d := ⟨k - j₀, by omega⟩
  rw [kseqF_eq_sum, Nat.add_sub_cancel_left, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  congr 1
  exact Finset.sum_congr rfl fun i hi => by
    have := Finset.mem_range.1 hi
    rw [show j₀ + d - 1 - (j₀ + i) = d - 1 - i by omega]

/-- **`kseqF` is linear in the `V`-sizes**: the seed and each part of `m` can be followed
separately (e.g. `m = c(|r'| + |M₄| + g)`; the `r'`-part then enters the error of the reduced
flow as `∑_iη_{ik}|r'_i|` with `η_{ik} ∝ θ^{k-1-i}Br_i²`, summable by
`Obs2.geom_kernel_weight_le`). -/
theorem kseqF_add_m (θ B : ℝ) (r m₁ m₂ : ℕ → ℝ) (j₀ : ℕ) (k₀ : ℝ) {k : ℕ} (hk : j₀ ≤ k) :
    kseqF θ B r (fun i => m₁ i + m₂ i) j₀ k₀ k =
      kseqF θ B r m₁ j₀ k₀ k + kseqF θ B r m₂ j₀ 0 k := by
  rw [kseqF_eq_sum_Ico _ _ _ _ _ _ hk, kseqF_eq_sum_Ico _ _ _ _ _ _ hk,
    kseqF_eq_sum_Ico _ _ _ _ _ _ hk, mul_zero, zero_add, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

section Hist

variable {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

/-- **The linear-regime `ab` recursion with per-scale weights.** -/
theorem obs_histFromABL_wM {C₀ η ε₀ C₁k : ℝ} (hKB : KObsBoundsABL L R.A C₀ η ε₀ C₁k) (hC₁k : 0 ≤ C₁k)
    (ck : ℝ) (hck : 0 ≤ ck)
    {Kw C₁ ε₁ : ℝ} (hWB : WObsBoundsAB L Kw C₁ ε₁) (hC₁ : 0 ≤ C₁)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    {c : Obs.Case} (P : ObsPts 2 L N) (Ma Mb : ℕ → ℝ) (hMa : ∀ j, 0 < Ma j) (hMb : ∀ j, 0 < Mb j)
    {j₀ : ℕ} (o₀ : ObsSt c L N) (h0 : o₀.IsObs) (hl0 : ObsLocInv P j₀ o₀)
    (hs0 : ObsSymInv j₀ o₀) (ha0 : ObsAnchInv P j₀ o₀)
    (t : Flow2.Hist.Seq (Xs R)) (n : ℕ) (hn : n ≤ Nh)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε n t)
    (hθ0 : 0 ≤ kθ0 L R.A C₀ η) (hθ : kθ0 L R.A C₀ η ≤ 1 / 72)
    (hsm : C₁k * (2 + 2 * (8 * cx κ cT) + ck) *
      (cR R Λ cm C₂ * ε) ≤ 1 / 72)
    (hε1 : cR R Λ cm C₂ * ε ≤ 1) (hεε : cR R Λ cm C₂ * ε ≤ ε₀)
    (hεk : (8 * cx κ cT + ck) * (cR R Λ cm C₂ * ε) ≤ ε₀)
    (hBr : 32 * kB (kθ0 L R.A C₀ η) C₁k (8 * cx κ cT) * (cR R Λ cm C₂ * ε) ^ 2 ≤ ck)
    (hLw : Kw / L ≤ 1 / 12) (hC₁ε : C₁ * (cR R Λ cm C₂ * ε) ≤ 1 / 12)
    (hε₁ : cR R Λ cm C₂ * ε ≤ ε₁)
    (m : ℕ → ℝ) (hm0 : ∀ j, 0 < m j)
    (hm' : ∀ j, j₀ ≤ j → j < n → Ma j * Mb j / (Ma j₀ * Mb j₀) * m j ≤
      2 * (Ma (j + 1) * Mb (j + 1) / (Ma j₀ * Mb j₀) * m (j + 1)))
    (hVo : ∀ j, j₀ ≤ j → j < n → ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo (wM (Ma j) (Mb j)) j (histS R j t) ((obsHistFrom R P j₀ o₀ j t).V b) ≤
        ENNReal.ofReal (m j))
    (hW0 : ∀ b ∈ blockIdx (L := L) (N := N) j₀, oTo (wM (Ma j₀) (Mb j₀)) j₀ (histS R j₀ t)
      (o₀.W b) ≤ ENNReal.ofReal ((4 * C₁ + 1) * (cR R Λ cm C₂ * (t j₀).1) * m j₀))
    (k₀ : ℝ) (hk₀ : 0 ≤ k₀)
    (hK0 : ∀ X, IsConn j₀ X → ENNReal.ofReal (R.A ^ (nb j₀ X - 2 ^ 2)) *
      oTo (wM (Ma j₀) (Mb j₀)) j₀ (histS R j₀ t) (o₀.K X) ≤ ENNReal.ofReal k₀)
    (h8 : 8 * k₀ ≤ ck * ((4 * C₁ + 1) * m j₀)) :
    let B := kB (kθ0 L R.A C₀ η) C₁k (8 * cx κ cT)
    let θb := kθ0 L R.A C₀ η + C₁k * (2 + 2 * (8 * cx κ cT) + ck) * (cR R Λ cm C₂ * ε)
    let r := fun j => cR R Λ cm C₂ * (t j).1
    let cWc := 4 * C₁ + 1
    let lamM := fun i => Ma i * Mb i / (Ma j₀ * Mb j₀)
    ∀ j, j₀ ≤ j → j ≤ n →
      8 * kseqF (8 * θb) B r (fun i => cWc * (lamM i * m i)) j₀ k₀ j ≤
        ck * (cWc * (lamM j * m j)) ∧
      (∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo (wM (Ma j) (Mb j)) j (histS R j t) ((obsHistFrom R P j₀ o₀ j t).W b) ≤
          ENNReal.ofReal (cWc * r j * m j)) ∧
      (∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
        oTo (wM (Ma j) (Mb j)) j (histS R j t) ((obsHistFrom R P j₀ o₀ j t).K X) ≤
          ENNReal.ofReal (kseqF (8 * θb) B r (fun i => cWc * (lamM i * m i)) j₀ k₀ j /
            lamM j)) := by
  intro B θb r cWc lamM
  have hl : ∀ i, 0 < lamM i := fun i => div_pos (mul_pos (hMa i) (hMb i)) (mul_pos (hMa j₀) (hMb j₀))
  have hlam0 : lamM j₀ = 1 := div_self (mul_pos (hMa j₀) (hMb j₀)).ne'
  have hab : ∀ j, j₀ ≤ j → ObsAnchInv P j (obsHistFrom R P j₀ o₀ j t) :=
    fun j hj => obsAnchInv_histFrom' R P ha0 t hj
  have hres : ∀ j {F : OE c (Lam 2 L N)}, F ∈ (abSub : Subalgebra ℂ (OE c (Lam 2 L N))) →
      oTo (wM (Ma j₀) (Mb j₀)) j (histS R j t) F =
        ENNReal.ofReal (lamM j) * oTo (wM (Ma j) (Mb j)) j (histS R j t) F := fun j F hF =>
    oTo_wM_rescale (hMa j₀) (hMb j₀) (hMa j) (hMb j) j _ hF
  have hm0' : ∀ j, 0 < lamM j * m j := fun j => mul_pos (hl j) (hm0 j)
  have hVo' : ∀ j, j₀ ≤ j → j < n → ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo (wM (Ma j₀) (Mb j₀)) j (histS R j t) ((obsHistFrom R P j₀ o₀ j t).V b) ≤
        ENNReal.ofReal (lamM j * m j) := by
    intro j hj hjn b hb
    rw [hres j (anchSub_ab ((hab j hj).V b)), ENNReal.ofReal_mul (hl j).le]
    exact mul_le_mul_right (hVo j hj hjn b hb) _
  have hW0' : ∀ b ∈ blockIdx (L := L) (N := N) j₀, oTo (wM (Ma j₀) (Mb j₀)) j₀ (histS R j₀ t)
      (o₀.W b) ≤ ENNReal.ofReal ((4 * C₁ + 1) * (cR R Λ cm C₂ * (t j₀).1) * (lamM j₀ * m j₀)) := by
    intro b hb; rw [hlam0, one_mul]; exact hW0 b hb
  have h8' : 8 * k₀ ≤ ck * ((4 * C₁ + 1) * (lamM j₀ * m j₀)) := by rw [hlam0, one_mul]; exact h8
  have hwt := wM_ne_top (Ma j₀) (Mb j₀)
  have hM := obs_histFromABL R hKB hC₁k ck hck hWB hC₁ hSB hV hm hβ hδ1 H P (wM (Ma j₀) (Mb j₀))
    (wM_sub _ _) hwt.1 hwt.2.1 hwt.2.2 o₀ h0 hl0 hs0 ha0 t n hn ht hθ0 hθ hsm hε1 hεε hεk hBr
    hLw hC₁ε hε₁ (fun i => lamM i * m i) hm0' hm' hVo' hW0' k₀ hk₀ hK0 h8'
  intro j hj hjn
  obtain ⟨h1, h2, h3⟩ := hM j hj hjn
  refine ⟨h1, fun b hb => ?_, fun X hX => ?_⟩
  · have h := h2 b hb
    rw [hres j (anchSub_ab ((hab j hj).W b))] at h
    have e : ENNReal.ofReal (cWc * r j * m j) =
        ENNReal.ofReal (lamM j)⁻¹ * ENNReal.ofReal (cWc * r j * (lamM j * m j)) := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.2 (hl j).le)]
      congr 1; field_simp [(hl j).ne']
    rw [e]
    calc oTo (wM (Ma j) (Mb j)) j (histS R j t) ((obsHistFrom R P j₀ o₀ j t).W b)
        = ENNReal.ofReal (lamM j)⁻¹ * (ENNReal.ofReal (lamM j) *
            oTo (wM (Ma j) (Mb j)) j (histS R j t) ((obsHistFrom R P j₀ o₀ j t).W b)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 (hl j).le),
            inv_mul_cancel₀ (hl j).ne', ENNReal.ofReal_one, one_mul]
      _ ≤ _ := mul_le_mul_right h _
  · have h := h3 X hX
    rw [hres j (anchSub_ab ((hab j hj).K X hX))] at h
    have e : ENNReal.ofReal (kseqF (8 * θb) B r (fun i => cWc * (lamM i * m i)) j₀ k₀ j / lamM j) =
        ENNReal.ofReal (lamM j)⁻¹ *
          ENNReal.ofReal (kseqF (8 * θb) B r (fun i => cWc * (lamM i * m i)) j₀ k₀ j) := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.2 (hl j).le), div_eq_inv_mul]
    rw [e]
    calc ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
          oTo (wM (Ma j) (Mb j)) j (histS R j t) ((obsHistFrom R P j₀ o₀ j t).K X)
        = ENNReal.ofReal (lamM j)⁻¹ * (ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
            (ENNReal.ofReal (lamM j) *
              oTo (wM (Ma j) (Mb j)) j (histS R j t) ((obsHistFrom R P j₀ o₀ j t).K X))) := by
          rw [mul_left_comm (ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2))), ← mul_assoc,
            ← ENNReal.ofReal_mul (inv_nonneg.2 (hl j).le), inv_mul_cancel₀ (hl j).ne',
            ENNReal.ofReal_one, one_mul]
      _ ≤ _ := mul_le_mul_right h _

end Hist

end

end PtCorr2
