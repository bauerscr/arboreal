import Loc.Image

/-!
# Proposition `prop:Loc` (v) for block-preserving symmetries

`Loc_image` (in `Loc/Image.lean`) assumes invariance under all automorphisms fixing the block
`B`; its proof only uses the reflections about the centre of `B` and the permutations about its
corner.  `Loc_image'` assumes invariance under these only.
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD

variable {d L N : ℕ} [NeZero L]

/-- Symmetric coefficients from invariance under the reflections and permutations about `B`. -/
theorem symCoef_of_inv' {j : ℕ} (hj : j ≤ N) {b : Fin d → ℕ}
    (hB : Patch (blockSet (L := L) (N := N) j b)) (hne : (blockSet (L := L) (N := N) j b).Nonempty)
    (κ : ℂ) (C : Mono d → ℂ)
    (hR : ∀ i, autAlg (reflCenter (L := L) (N := N) j b i).E
      (κ • 1 + ∑ M, C M • monoSet M (blockSet j b)) =
        κ • 1 + ∑ M, C M • monoSet M (blockSet j b))
    (hP : ∀ σ, autAlg (permCorner (L := L) (N := N) j b σ).E
      (κ • 1 + ∑ M, C M • monoSet M (blockSet j b)) =
        κ • 1 + ∑ M, C M • monoSet M (blockSet j b))
    (hJ : Jsym (κ • 1 + ∑ M, C M • monoSet M (blockSet (L := L) (N := N) j b)) =
        κ • 1 + ∑ M, C M • monoSet M (blockSet j b)) : SymCoef C where
  refl i M := by
    have := coef_aut hB hne _ (reflCenter_img hj b i) κ C (hR i) M
    rwa [reflCenter_ρ, reflCenter_sgn] at this
  perm σ M := by
    have := coef_aut hB hne _ (permCorner_img hj b σ.symm) κ C (hP σ.symm) M
    rwa [permCorner_ρ, permCorner_sgn, mul_one, Equiv.symm_symm] at this
  swap M := coef_Jsym hB hne κ C hJ M

/-- **Proposition `prop:Loc` (v)**, assuming invariance only under the reflections about the
centre of `B` and the coordinate permutations about its corner. -/
theorem Loc_image' (hd : 1 ≤ d) {j : ℕ} (hj : j < N) (hL : 3 ≤ L) {b : Fin d → ℕ}
    (hne : (blockSet (L := L) (N := N) j b).Nonempty) {ι : Type*} (s : Finset ι)
    (X : ι → Finset (Lam d L N)) (F : ι → Alg d L N) (hX : ∀ i ∈ s, Patch (X i))
    (hXne : ∀ i ∈ s, (X i).Nonempty) (hFJ : ∀ i ∈ s, Jsym (F i) = F i)
    (hR : ∀ i, autAlg (reflCenter (L := L) (N := N) j b i).E
      (∑ k ∈ s, LocXY (X k) (blockSet j b) (F k)) = ∑ k ∈ s, LocXY (X k) (blockSet j b) (F k))
    (hP : ∀ σ, autAlg (permCorner (L := L) (N := N) j b σ).E
      (∑ k ∈ s, LocXY (X k) (blockSet j b) (F k)) = ∑ k ∈ s, LocXY (X k) (blockSet j b) (F k)) :
    ∑ i ∈ s, LocXY (X i) (blockSet j b) (F i) ∈ VXspace (blockSet (L := L) (N := N) j b) := by
  set B := blockSet (L := L) (N := N) j b
  have hG : ∑ i ∈ s, LocXY (X i) B (F i) =
      (∑ i ∈ s, ε (F i) * B.card / (X i).card) • (1 : Alg d L N) +
        ∑ M, (∑ i ∈ s, locCoef (X i) (F i) M) • monoSet M B := by
    simp only [LocXY, sum_add_distrib, sum_smul]
    rw [sum_comm]
  have hJ : Jsym (∑ i ∈ s, LocXY (X i) B (F i)) = ∑ i ∈ s, LocXY (X i) B (F i) := by
    rw [map_sum]
    refine sum_congr rfl fun i hi => ?_
    rw [← LocXY_Jsym (hX i hi) (hXne i hi), hFJ i hi]
  rw [hG] at hR hP hJ ⊢
  exact mem_VXspace_of_symCoef hd hne _
    (symCoef_of_inv' hj.le (patch_blockSet hj hL b) hne _ _ hR hP hJ)

end

end Loc
