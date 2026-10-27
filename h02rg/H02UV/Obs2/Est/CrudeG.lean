import Obs.StepObsNonlinGen

/-!
# The crude bound for the generic polymer map over a submultiplicative norm

`Step2.GH.gKnext_le` (`Step2/Map/Crude.lean`) bounds the whole sum over `𝒢(U)` of the polymer map
`gKnext` on the bulk algebra. Its proof only uses the product property and the triangle
inequality of the norms, the contraction `‖𝔼 x‖ ≤ ‖x‖`, the block hypotheses of
`Obs.Gen.KHypG` and the combinatorics of `𝒢(U)`. This file proves it for the generic map
`Obs.Gen.KnextG` over any `SNorm` (`KHypG.KnextG_le`), so that it applies to the algebra with
sources (`Obs2.ExactStep.Knext2O_eq_KnextG`):

* `KHypG.integrand_le`: `‖Ǩ(X̌) ∏_{𝒳} θ J‖ ≤ β^m (2ρ)^{|𝓑_j(X̌)|}`, `ρ = A⁻¹`,
  `β = (1 + 2^d c_J) κ₀ + δ₁`, `m = |Comp(X̌)| + |𝒳|`;
* **`KHypG.KnextG_le`**: if the prefactors obey `‖e^{u(U)} e^{-(u+V)(U ∖ (X̌ ∪ X_𝒳))}‖ ≤
  2^{|𝓑_{j+1}(U)|}`, `|𝒢(U)| ≤ M^{|𝓑_{j+1}(U)|}`, the geometric inequality of `𝒢(U)` holds,
  `P = Q (2M)`, `4P ≤ A^{2η/(1+2η)}` and `(AP)^{2^d} β ≤ 1`, then
  `(A Q)^{|𝓑_{j+1}(U)|} ‖K_{j+1}(U)‖ ≤ 1`.
-/

namespace Obs.Gen

noncomputable section

open Finset Grassmann Loc FRD Step

variable {d L N : ℕ} [NeZero L]
variable {R R2 : Type*} [CommRing R] [CommRing R2] [Algebra ℂ R] [Algebra ℂ R2]

namespace KHypG

variable {Al : RGAlg R R2} {j : ℕ} {F : RGIngr d L N R} {n2 : SNorm R2}
  {A κ₀ δ₁ cJ : ℝ} (H : KHypG Al j F n2 A κ₀ δ₁ cJ)
include H

/-- The integrand of `K_{j+1}(U)`: `‖Ǩ(X̌) ∏_{𝒳} θ J‖ ≤ β^m (2ρ)^{|𝓑(X̌)|}`. -/
theorem integrand_le {g : GT d L N} (hg2 : IsPolymer j g.2)
    (hg1 : ∀ p ∈ g.1, p.1 ∈ blockIdx (L := L) (N := N) j) :
    n2.nrm (KchkG Al j F g.2 * JprodG Al F g.1) ≤
      ENNReal.ofReal (((1 + 2 ^ d * cJ) * κ₀ + δ₁) ^ ((Comp j g.2).card + g.1.card) *
        (2 * A⁻¹) ^ nb j g.2) := by
  have hρ := H.hρ0
  have hκ := H.hκ₀
  have hc := H.hcJ
  have hδ := H.hδ₁
  set β := (1 + 2 ^ d * cJ) * κ₀ + δ₁
  have hβ0 : 0 ≤ β := by positivity
  have hK1 : n2.nrm (KchkG Al j F g.2) ≤ ENNReal.ofReal (β ^ (Comp j g.2).card * (2 * A⁻¹) ^ nb j g.2) := by
    have := n2.prodR (Comp j g.2) (KchkCG Al j F)
      (fun Y => β * (2 * A⁻¹) ^ nb j Y) (fun _ _ => by positivity)
      (fun Y hY => (H.KchkC_bounds (isConn_of_mem_comp hg2 hY)).1)
    rwa [prod_mul_distrib, prod_const, prod_comp_pow hg2] at this
  have hJ : n2.nrm (JprodG Al F g.1) ≤ ENNReal.ofReal (β ^ g.1.card) := by
    have := n2.prodR g.1 (fun p => Al.θ (F.J p.1 p.2)) (fun _ => β) (fun _ _ => hβ0)
      (fun p hp => (H.thetaJ_le_kappa (hg1 p hp) p.2).trans (ENNReal.ofReal_le_ofReal (by
        have : 0 ≤ δ₁ := hδ
        simp only [β]; linarith)))
    rwa [prod_const] at this
  refine (n2.mulR (by positivity) hK1 hJ).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [pow_add]; ring_nf; rfl

/-- **The crude bound** for the generic map: `(A Q)^{|𝓑_{j+1}(U)|} ‖K_{j+1}(U)‖ ≤ 1`. -/
theorem KnextG_le (n : SNorm R) (hE : ∀ x : R2, n.nrm (Al.E x) ≤ n2.nrm x)
    {U : Finset (Lam d L N)} {Q η P : ℝ} {M : ℕ} (hQ : 1 ≤ Q) (hη : 0 ≤ η)
    (hpref : ∀ g ∈ Gset j U, n.nrm (PrefG j F U * ItPow j F (U \ (g.2 ∪ Xcal g.1))) ≤
      ENNReal.ofReal (2 ^ nb (j + 1) U))
    (hcount : (Gset j U).card ≤ M ^ nb (j + 1) U)
    (hgeom : ∀ g ∈ Gset j U, (1 + 2 * η) * (nb (j + 1) U : ℝ) ≤
      nb j g.2 + (1 + 2 * η) * 2 ^ d * ((Comp j g.2).card + g.1.card))
    (hP : P = Q * (2 * M)) (hM : 1 ≤ M) (hAP : 4 * P ≤ A ^ (2 * η / (1 + 2 * η)))
    (hDβ : (A * P) ^ 2 ^ d * ((1 + 2 ^ d * cJ) * κ₀ + δ₁) ≤ 1) :
    ENNReal.ofReal ((A * Q) ^ nb (j + 1) U) * n.nrm (KnextG Al j F U) ≤ ENNReal.ofReal 1 := by
  classical
  have hA := H.hA
  have hA0 : 0 < A := by linarith
  have hρ := H.hρ0
  have hκ := H.hκ₀
  have hc := H.hcJ
  have hδ := H.hδ₁
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hP1 : 1 ≤ P := by rw [hP]; nlinarith
  set x := nb (j + 1) U
  set β := (1 + 2 ^ d * cJ) * κ₀ + δ₁ with hβdef
  have hβ0 : 0 ≤ β := by positivity
  have e : KnextG Al j F U = ∑ g ∈ Gset j U,
      (PrefG j F U * ItPow j F (U \ (g.2 ∪ Xcal g.1))) *
        Al.E (KchkG Al j F g.2 * JprodG Al F g.1) := by
    rw [KnextG, mul_sum]
    exact sum_congr rfl fun g _ => by rw [KtermG, mul_assoc]
  rw [e]
  refine n.wsum_bound _ _ (M ^ x) hcount fun g hg => ?_
  obtain ⟨f1, -, -, f4⟩ := Gset_facts hg
  have hI := H.integrand_le f1 (fun p hp => (mem_pairsU.1 (f4 p hp).1).1)
  have hT := n.mulR (by positivity) (hpref g hg) ((hE _).trans hI)
  refine (mul_le_mul_left' hT _).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  set m := (Comp j g.2).card + g.1.card
  set t := nb j g.2
  have hgeo := geom_real (d := d) (x := x) (t := t) (m := m) (le_trans le_rfl hA) hP1 hη
    (by
      rw [show ((m : ℕ) : ℝ) = ((Comp j g.2).card : ℝ) + g.1.card by push_cast [m]; ring]
      exact hgeom g hg) hAP
  have h2 : (2 * A⁻¹) ^ t ≤ (4 * A⁻¹) ^ t := by gcongr; norm_num
  have hpm : ((A * P) ^ 2 ^ d) ^ m * β ^ m ≤ 1 := by
    rw [← mul_pow]; exact pow_le_one₀ (by positivity) hDβ
  calc ((M ^ x : ℕ) : ℝ) * (A * Q) ^ x * (2 ^ x * (β ^ m * (2 * A⁻¹) ^ t))
      ≤ ((M ^ x : ℕ) : ℝ) * (A * Q) ^ x * (2 ^ x * (β ^ m * (4 * A⁻¹) ^ t)) := by gcongr
    _ = (A ^ x * P ^ x * (4 * A⁻¹) ^ t) * β ^ m := by
        rw [hP, mul_pow, mul_pow, mul_pow]; push_cast; ring
    _ ≤ (A * P) ^ (2 ^ d * m) * β ^ m := by gcongr
    _ = ((A * P) ^ 2 ^ d) ^ m * β ^ m := by rw [pow_mul]
    _ ≤ 1 := hpm

end KHypG

end

end Obs.Gen
