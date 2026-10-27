import Step2.Map.DCov
import DressedFRD.LipDecay

/-!
# Lipschitz dependence of `C'_{j+1}` on the couplings, with geometric decay (Gram form)

For two coupling sequences `ζ`, `ζ'` with `|ζ_i|, |ζ'_i| ≤ ζ̄/2` the difference
`C'_{j+1}(ζ) - C'_{j+1}(ζ')` of the dressed covariances `Cdr` satisfies `GoodCov2` at scale `j`
with field scale
`ℓ_Δ = (K ∑_{k≤j} ρ^{j-k} |ζ_k - ζ'_k|)^{1/2} L^{-j(d-2)/2} L^{p_Φ}`,
for any prescribed ratio `0 < ρ ≤ 1/2` (`prop_C5_lip`). This is `DressedFRD.lip_decay_full`
combined with the Gram representation of `goodCov2_dressed`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Matrix

variable {d L N : ℕ} [NeZero L]

/-- The difference of dressed covariances is the matrix of the difference of the symbols. -/
theorem Cdr_sub (D D' : DressedFRD.Data d (L ^ N)) (j : ℕ) :
    Cdr D j - Cdr D' j =
      DressedFRD.kmat (D.Z (j + 1) • D.Gint j - D'.Z (j + 1) • D'.Gint j) := by
  ext x y
  simp only [Matrix.sub_apply, DressedFRD.kmat, DressedFRD.kern_sub]

/-- `GoodCov2` at scale `j` for the matrix of a symbol with `‖w‖_{(j)} ≤ B` and
`2 rng w < L^{j+1}`, with `ℓ = B^{1/2} L^{-j(d-2)/2} L^{p_Φ}`. -/
theorem goodCov2_of_snorm {q : ℕ} (hL : 1 ≤ L) {j : ℕ} (hpq : 2 * pPhi d ≤ q)
    {w : DressedFRD.Sym d (L ^ N)} {B : ℝ} (hw : DressedFRD.snorm (L : ℝ) q j w ≤ B)
    (hr : 2 * DressedFRD.rng w < L ^ (j + 1)) :
    GoodCov2 (d := d) (L := L) (N := N) j
      (Real.sqrt B * (L : ℝ) ^ (-((j : ℝ) * ((d : ℝ) - 2)) / 2) * (L : ℝ) ^ pPhi d)
      (DressedFRD.kmat w) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  constructor
  · refine ⟨_, inferInstance, inferInstance, DressedFRD.gramF w, DressedFRD.gramG w,
      DressedFRD.kmat_isGram _, ?_⟩
    have hB := DressedFRD.kmat_gramBound (L := (L : ℝ)) (p := pPhi d) hL0 hpq hw
    have hB' := GramBound.rescale (c := (L : ℝ)) (by positivity) (by exact_mod_cast hL) hB
    rw [← pow_succ'] at hB'
    exact hB'
  · intro _ x y hxy
    refine DressedFRD.kern_eq_zero_of_rng_lt ?_
    have h2 : (2 * DressedFRD.rng w : ℝ) < (L : ℝ) ^ (j + 1) := by exact_mod_cast hr
    have h3 : ((DressedFRD.rng w : ℕ) : ℝ) < ((supNorm (x - y) : ℕ) : ℝ) := by
      linarith
    exact_mod_cast h3

/-- The field scale of the difference. -/
def ellLip (d L : ℕ) (B : ℝ) (j : ℕ) : ℝ :=
  Real.sqrt B * (L : ℝ) ^ (-((j : ℝ) * ((d : ℝ) - 2)) / 2) * (L : ℝ) ^ pPhi d

/-- **`prop:C5`, Lipschitz part with geometric decay**: for every ratio `0 < ρ ≤ 1/2` there are
`ζ̄` and `K` such that for `|ζ_i|, |ζ'_i| ≤ ζ̄/2` and `j + 1 < N`, the difference
`C'_{j+1}(ζ) - C'_{j+1}(ζ')` satisfies `GoodCov2` at scale `j` with
`ℓ_Δ² = K ∑_{k≤j} ρ^{j-k} |ζ_k - ζ'_k| · L^{-j(d-2)} L^{2 p_Φ}`. -/
theorem prop_C5_lip (P : PtFamily) (hd : 2 ≤ d) (hL7 : 7 ≤ L) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1 / 2) :
    ∃ ζbar : ℝ, 0 < ζbar ∧ ζbar ≤ 1 / 8 ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ) (msq : ℝ)
      (ζ ζ' : ℕ → ℂ), 1 ≤ N → 0 < msq → msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) →
      (∀ i, ‖ζ i‖ ≤ ζbar / 2) → (∀ i, ‖ζ' i‖ ≤ ζbar / 2) → ∀ j, j + 1 < N →
      let D : DressedFRD.Data d (L ^ N) := ⟨L, N, msq, DressedFRD.frdC P msq L N, ζ⟩
      let D' : DressedFRD.Data d (L ^ N) := ⟨L, N, msq, DressedFRD.frdC P msq L N, ζ'⟩
      GoodCov2 (d := d) (L := L) (N := N) j
        (ellLip d L (K * ∑ k ∈ range (j + 1), ρ ^ (j - k) * ‖ζ k - ζ' k‖) j)
        (Cdr D j - Cdr D' j) := by
  have hq : 2 ≤ 2 * pPhi d := by simp only [pPhi]; omega
  obtain ⟨cS, hcS, hS⟩ := DressedFRD.frd_stdFull P (d := d) hd hL7 (q := 2 * pPhi d)
    (M := 2 * pPhi d + d + 1) le_rfl
  obtain ⟨ζbar, hζ, hζ8, K, hK0, hK⟩ := DressedFRD.lip_decay_full (d := d) hd hq hL7
    (M := 2 * pPhi d + d + 1) le_rfl hcS hρ hρ1
  refine ⟨ζbar, hζ, hζ8, K, hK0, fun N msq ζ ζ' hN hmsq hmsq' hζi hζi' j hj => ?_⟩
  intro D D'
  have hS' := hS (L ^ N) N msq hN rfl hmsq
  have hw := hK (L ^ N) D ζ' rfl rfl hS' hmsq' hζi hζi' j hj
  have hr := DressedFRD.Data.two_rng_Cdiff_lt (D := D) (ζ' := ζ') hS'.base
    (show 1 ≤ D.L by show 1 ≤ L; omega) rfl hj
  rw [Cdr_sub]
  exact goodCov2_of_snorm (by omega) le_rfl hw hr

end

end Step2
