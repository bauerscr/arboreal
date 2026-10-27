import Step2.Coup.CoupBound

/-!
# Symmetries of the coupling polynomials (`h02uv-outline.tex`, `prop:C1`, `prop:C2`)

* `autAlg_Vcoup`: `T V_κ(Y) = V_κ(T Y)` for every generated lattice automorphism `T`. The
  quadratic part is handled by induction on `IsGen` (`coupC_aut`), the quartic part with
  `SPerm.autAlg_mono4sSet`.
* `Jsym_Vcoup`: `J V_κ(Y) = V_κ(Y)`.
* `famSym_Vcoup`, `famJ_Vcoup`: a block family `V(B) = V_κ(B)`, in particular the initial `V_0`,
  satisfies `FamSym` and `FamJ`, the hypotheses of `prop:C1` and `prop:C2`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Matrix

variable {d L N : ℕ} [NeZero L]

/-- The coefficients of `V_κ` are invariant under the action of `T` on the monomial basis. -/
theorem coupC_aut {T : AffAut d L N} (hT : IsGen T) (κ : Coup) (M : Mono d) :
    coupC κ (T.ρ M) = T.sgn M * coupC κ M := by
  induction hT generalizing M with
  | transl t => simp [AffAut.transl]
  | refl i =>
    show coupC κ M = (-1 : ℂ) ^ cnt i M * coupC κ M
    cases M with
    | c => simp [cnt]
    | a1 k => simp [coupC]
    | b1 k => simp [coupC]
    | a2 s =>
      induction s using Sym2.ind with
      | h k l =>
        by_cases hkl : k = l
        · subst hkl; simp only [cnt, Sym2.lift_mk]
          rw [← two_mul, pow_mul]; simp
        · simp [coupC, hkl]
    | b2 s =>
      induction s using Sym2.ind with
      | h k l =>
        by_cases hkl : k = l
        · subst hkl; simp only [cnt, Sym2.lift_mk]
          rw [← two_mul, pow_mul]; simp
        · simp [coupC, hkl]
    | m2 k l =>
      by_cases hkl : k = l
      · subst hkl; simp only [cnt]
        rw [← two_mul, pow_mul]; simp
      · simp [coupC, hkl]
  | perm σ =>
    show coupC κ (permMono σ M) = 1 * coupC κ M
    rw [one_mul]
    cases M with
    | c => rfl
    | a1 k => rfl
    | b1 k => rfl
    | a2 s =>
      induction s using Sym2.ind with
      | h k l => simp [permMono, coupC, σ.injective.eq_iff]
    | b2 s =>
      induction s using Sym2.ind with
      | h k l => simp [permMono, coupC, σ.injective.eq_iff]
    | m2 k l => simp [permMono, coupC, σ.injective.eq_iff]
  | comp h₁ h₂ ih₁ ih₂ =>
    simp only [AffAut.comp, Equiv.trans_apply]
    rw [ih₂, ih₁]; ring

/-- **`T V_κ(Y) = V_κ(T Y)`.** -/
theorem autAlg_Vcoup {T : AffAut d L N} (hT : IsGen T) (κ : Coup) (Y : Finset (Lam d L N)) :
    autAlg T.E (Vcoup κ Y) = Vcoup κ (T.img Y) := by
  obtain ⟨π, s, h⟩ := isGen_sperm hT
  have hq : autAlg T.E (∑ M, coupC κ M • monoSet M Y) = ∑ M, coupC κ M • monoSet M (T.img Y) := by
    rw [map_sum]
    simp only [map_smul, T.autAlg_monoSet, smul_smul]
    refine Fintype.sum_equiv T.ρ _ _ fun M => ?_
    rw [coupC_aut hT, mul_comm]
  have hs2 : ∀ i, ((s i * s i : ℤ) : ℂ) = 1 := fun i => by
    rcases h.hs i with h1 | h1 <;> simp [h1]
  have h4 : autAlg T.E (∑ i, ∑ k, coupE κ i k • mono4sSet i k Y) =
      ∑ i, ∑ k, coupE κ i k • mono4sSet i k (T.img Y) := by
    have hd4 : ∀ Z : Finset (Lam d L N), ∑ i, ∑ k, coupE κ i k • mono4sSet i k Z =
        ∑ i, κ.g • mono4sSet i i Z := fun Z => by
      simp only [coupE, ite_smul, zero_smul, sum_ite_eq, mem_univ, if_true]
    rw [hd4, hd4, map_sum]
    simp only [map_smul, h.autAlg_mono4sSet, smul_smul, hs2, mul_one]
    exact Fintype.sum_equiv π _ _ fun i => rfl
  rw [Vcoup, Vcoup, unif, unif, map_add, map_add, map_smul, map_one, hq, h4]

/-- **`J V_κ(Y) = V_κ(Y)`.** -/
theorem Jsym_Vcoup (κ : Coup) (Y : Finset (Lam d L N)) : Jsym (Vcoup κ Y) = Vcoup κ Y := by
  rw [Vcoup, Jsym_unif]
  congr 1
  · funext M
    cases M with
    | c => rfl
    | a1 k => rfl
    | b1 k => rfl
    | a2 s => rfl
    | b2 s => rfl
    | m2 k l => simp only [swapM, coupC, eq_comm]
  · funext i k
    simp only [coupE, eq_comm]

/-- **`FamSym` for a coupling family**, in particular for `V_0`. -/
theorem famSym_Vcoup {j : ℕ} (hj : j ≤ N) {V : Fam d L N} (κ : Coup)
    (hV : ∀ b, (V b : Alg d L N) = Vcoup κ (blockSet (L := L) (N := N) j b)) : FamSym j V := by
  intro T hT hP b hb
  refine Subtype.ext ?_
  rw [coe_AE, hV, hV, autAlg_Vcoup hT, img_blockSet_bmap hT hj hP hb]

/-- **`FamJ` for a coupling family**, in particular for `V_0`. -/
theorem famJ_Vcoup {j : ℕ} {V : Fam d L N} (κ : Coup)
    (hV : ∀ b, (V b : Alg d L N) = Vcoup κ (blockSet (L := L) (N := N) j b)) : FamJ V := by
  intro b
  rw [mem_JS, hV, Jsym_Vcoup]

end

end Step2
