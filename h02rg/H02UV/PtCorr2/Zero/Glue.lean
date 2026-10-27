import PtCorr2.Zero.Bounds
import Step2.Last.FlowGlueHist

/-!
# The zero-mode integration along the flow: from `GlueOut` to `ZeroModeOut`

`ZeroModeOut R N_h C t` collects, for the final-scale object `out = lastOut R N_h t` and the raw
zero mode `t_raw = zmRaw R (N_h+1) out.ζ` (complex), with `ǧ = ǧ_{N_h}`, `E = e^{L² C ǧ²}`:

* (`prop:ZNN`) `Rc Z̃_{N,N} = 1 + ũ_{N,N} - |Λ| ã_{N,N} ψψ̄` (`prop_ZNN2`);
* `Z_N ≠ 0`;
* `|k⁰| ≤ L² C ǧ² E + C ǧ³`;
* `|k^{2,𝒲}/Z_N| ≤ ℓ^{-2} L² C ǧ² E`, `|k^{2,K}/Z_N| ≤ ℓ^{-2} C ǧ³`;
* `||Λ| ã_{N,N}/Z_N - L^{2N} ν_N/Z_N| ≤ C ǧ · L² C ǧ² E + ℓ^{-2}(L² C ǧ² E + C ǧ³)`, and
  `|L^{2N} ν_N/Z_N| ≤ C ǧ`.

In normalised fields (`ψ = Z_N^{-1/2} ψ_raw`) the coefficient of `ψψ̄` is `-|Λ| ã/Z_N` and the
zero-mode variance is `t = Z_N t_raw`, so `ã t_raw = (|Λ| ã/Z_N)(t/|Λ|)`. Hence the leading
coefficient is `L^{2N} ν_N/Z_N = O(ǧ)` and all corrections (`k⁰`, `k^{2,𝒲}`, `k^{2,K}`, `P₀ - 1`) are
`O(ǧ²)`: relative errors `O(ǧ) = O(β_R^{-1})`.

`zeroModeOut_of_glue`: `GlueOut` and `Z_N ≠ 0` give `ZeroModeOut`.
-/

namespace PtCorr2

noncomputable section

open Finset Grassmann Suscept Step Loc Step2 Step2.LastN

set_option linter.unusedSectionVars false

variable {L N : ℕ} [NeZero L]

theorem card_lam_two_eq {Nh : ℕ} (hN : Nh + 2 = N) :
    (Fintype.card (Lam 2 L N) : ℂ) = (L : ℂ) ^ (2 * (Nh + 1 + 1)) := by
  rw [FRD.card_torus]
  subst hN
  push_cast
  rw [← pow_mul]; ring_nf

theorem inv_fscale_mul_sq (Z : ℂ) (ℓ : ℝ) :
    (fscale Z * ℓ)⁻¹ ^ 2 = ‖Z‖ * ℓ⁻¹ ^ 2 := by
  rw [mul_inv, mul_pow, inv_pow, fscale_sq, inv_inv]

/-- **The zero-mode integration of the final-scale object along a history**: the identity of
`prop:ZNN` and the bounds of its coefficients in terms of `ǧ = ǧ_{N_h}`. -/
def ZeroModeOut (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (Nh : ℕ) (C : ℝ)
    (t : Flow2.Hist.Seq (Xs R)) : Prop :=
  let out := lastOut R Nh t
  let g := (t Nh).1
  let E := (L : ℝ) ^ 2 * C * g ^ 2 * Real.exp ((L : ℝ) ^ 2 * C * g ^ 2)
  Rc (Lam 2 L N) (ZtFin (Nh + 1) out (zmRaw R (Nh + 1) out.ζ) : Alg 2 L N) =
      algebraMap ℂ (Alg 2 L N) (1 + uFin (Nh + 1) out (zmRaw R (Nh + 1) out.ζ)) -
        ((Fintype.card (Lam 2 L N) : ℂ) * aFin (Nh + 1) out) •
          (psiC (Lam 2 L N) * psibarC (Lam 2 L N)) ∧
    out.Z ≠ 0 ∧
    ‖P0Fin (Nh + 1) out - 1‖ ≤ E ∧
    ‖k0Fin (Nh + 1) out‖ ≤ E + C * g ^ 3 ∧
    ‖kW2Fin (Nh + 1) out / out.Z‖ ≤ R.ℓ⁻¹ ^ 2 * E ∧
    ‖kK2Fin out / out.Z‖ ≤ R.ℓ⁻¹ ^ 2 * (C * g ^ 3) ∧
    ‖(L : ℂ) ^ (2 * (Nh + 1 + 1)) * out.κ.nu / out.Z‖ ≤ C * g ∧
    ‖(Fintype.card (Lam 2 L N) : ℂ) * aFin (Nh + 1) out / out.Z -
        (L : ℂ) ^ (2 * (Nh + 1 + 1)) * out.κ.nu / out.Z‖ ≤
      C * g * E + R.ℓ⁻¹ ^ 2 * (E + C * g ^ 3)

/-- **`GlueOut` gives the zero-mode integration** (`N = N_h + 2`, `Z_N ≠ 0`). -/
theorem zeroModeOut_of_glue (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {Nh : ℕ}
    (hN : Nh + 2 = N) {C : ℝ} (hC : 0 ≤ C) (t : Flow2.Hist.Seq (Xs R)) (hg : 0 ≤ (t Nh).1)
    (hglue : GlueOut R Nh C t) (hZ : (lastOut R Nh t).Z ≠ 0) :
    ZeroModeOut R Nh C t := by
  obtain ⟨-, -, -, hnu, -, -, hB, hK⟩ := hglue
  set out := lastOut R Nh t with hout
  set g := (t Nh).1
  have hℓ : 0 < R.ℓ := Fact.out
  have hV : ∀ b ∈ blockIdx (L := L) (N := N) (Nh + 1),
      (out.V b : Alg 2 L N) = Vcoup out.κ (blockSet (Nh + 1) b) := fun b hb => (hB b hb).1
  have hh : 0 < fscale out.Z * R.ℓ := mul_pos (fscale_pos hZ) hℓ
  have hM : (blockIdx (L := L) (N := N) (Nh + 1)).card ≤ L ^ 2 :=
    card_blockIdx_last (by omega)
  have hw : 0 ≤ C * g ^ 2 := by positivity
  have hk : 0 ≤ C * g ^ 3 := by positivity
  obtain ⟨hP0, hk0, hkW, hkK, ha⟩ := fin_bounds (j := Nh + 1) (i := Nh + 1 + 1) (M := L ^ 2)
    hh hw hk hM (fun b hb => (hB b hb).2.2) hK
  have hMw : ((L ^ 2 : ℕ) : ℝ) * (C * g ^ 2) = (L : ℝ) ^ 2 * C * g ^ 2 := by push_cast; ring
  rw [hMw] at hP0 hk0 hkW ha
  set E := (L : ℝ) ^ 2 * C * g ^ 2 * Real.exp ((L : ℝ) ^ 2 * C * g ^ 2) with hE
  have hE0 : 0 ≤ E := by positivity
  rw [inv_fscale_mul_sq out.Z R.ℓ] at hkW hkK ha
  have hZn : 0 < ‖out.Z‖ := norm_pos_iff.2 hZ
  have hcard := card_lam_two_eq (L := L) hN
  refine ⟨prop_ZNN2 _ hV, hZ, hP0, hk0, ?_, ?_, hnu, ?_⟩
  · rw [norm_div, div_le_iff₀ hZn]
    calc _ ≤ _ := hkW
      _ = R.ℓ⁻¹ ^ 2 * E * ‖out.Z‖ := by ring
  · rw [norm_div, div_le_iff₀ hZn]
    calc _ ≤ _ := hkK
      _ = R.ℓ⁻¹ ^ 2 * (C * g ^ 3) * ‖out.Z‖ := by ring
  · rw [← sub_div, norm_div, div_le_iff₀ hZn, ← hcard]
    have hnu' : ‖(Fintype.card (Lam 2 L N) : ℂ) * out.κ.nu‖ ≤ C * g * ‖out.Z‖ := by
      rw [hcard]
      have := hnu
      rw [norm_div, div_le_iff₀ hZn] at this
      exact this
    calc _ ≤ _ := ha
      _ ≤ C * g * ‖out.Z‖ * E + ‖out.Z‖ * R.ℓ⁻¹ ^ 2 * (E + C * g ^ 3) := by
          gcongr
      _ = (C * g * E + R.ℓ⁻¹ ^ 2 * (E + C * g ^ 3)) * ‖out.Z‖ := by ring

end

end PtCorr2
