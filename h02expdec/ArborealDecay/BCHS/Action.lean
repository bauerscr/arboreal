module

public import ArborealDecay.BCHS.HoroEval

/-!
# The horospherical action: bosonic part and fermionic quadratic form (R4)

In horospherical coordinates the `ℍ^{2|4}` action of the pinned model (`β = w|_{Λ}`,
`h_i = w_{ρ i}`, `Λ = V ∖ ρ`) is

  `H = (Φ_w(τ̂) + ½ sᵀ 𝓛 s) · 1 + ∑_γ ∑_{a,b} 𝓛_{ab} ψ̄^γ_a ψ^γ_b`

with `𝓛 = TLaw.Lmat w ρ τ̂` (`horoF_actionH_eq`), using `HData.neg_udot` (BCHS (2.73)).  Hence
`e^{−H} = e^{−Φ − ½ sᵀ𝓛 s} · exp(∑_{m,m'} M_{m m'} ξ_m η_{m'})` with `M = 𝓛ᵀ ⊕ 𝓛ᵀ`, whose Berezin
integral is `det 𝓛²` (`body_berezin_exp_neg_action`, BCHS (2.74)).
-/

@[expose] public section

namespace ArborealDecay.BCHS

noncomputable section

open Finset Real ArborealDecay.Super ArborealDecay.Super.H24 ArborealDecay.Horo Grassmann
open ArborealDecay.TLaw (Lmat Phi ext IsWGraph)

set_option linter.unusedSectionVars false

/-! ### A quadratic-form identity in a module -/

theorem quad_identity {N G : Type*} [Fintype N] [DecidableEq N] [AddCommGroup G] [Module ℝ G]
    (c : N → N → ℝ) (hc : ∀ i j, c i j = c j i) (d : N → ℝ) (q : N → N → G) :
    (1 / 2 : ℝ) • ∑ i, ∑ j, c i j • (q i i - q i j - q j i + q j j) + ∑ i, d i • q i i =
      ∑ a, ∑ b, ((if a = b then ∑ j, c a j + d a else 0) - c a b) • q a b := by
  have h1 : ∑ i, ∑ j, c i j • q j j = ∑ i, ∑ j, c i j • q i i := by
    rw [Finset.sum_comm]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [hc]
  have h2 : ∑ i, ∑ j, c i j • q j i = ∑ i, ∑ j, c i j • q i j := by
    rw [Finset.sum_comm]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [hc]
  have eL : ∑ i, ∑ j, c i j • (q i i - q i j - q j i + q j j) =
      ∑ i, ∑ j, c i j • q i i - ∑ i, ∑ j, c i j • q i j - ∑ i, ∑ j, c i j • q j i +
        ∑ i, ∑ j, c i j • q j j := by
    simp only [smul_add, smul_sub, sum_add_distrib, sum_sub_distrib]
  have eR : ∑ a, ∑ b, ((if a = b then ∑ j, c a j + d a else 0) - c a b) • q a b =
      ∑ i, ∑ j, c i j • q i i + ∑ i, d i • q i i - ∑ i, ∑ j, c i j • q i j := by
    simp only [sub_smul, sum_sub_distrib, ite_smul, zero_smul, sum_ite_eq, mem_univ, ite_true,
      add_smul, sum_add_distrib, sum_smul]
  rw [eL, eR, h1, h2]
  module

/-! ### Horospherical data: the inner products -/

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- `a_{ij} = cosh(t_i − t_j) + ½ e^{t_i+t_j}(s_i − s_j)²`. -/
def acoef (p : Pt Λ) (i j : Λ) : ℝ :=
  cosh (p (.inl i) - p (.inl j)) + exp (p (.inl i) + p (.inl j)) * (p (.inr i) - p (.inr j)) ^ 2 / 2

/-- `ψ̄^γ_a ψ^γ_b`. -/
def qq (γ : Bool) (a b : Λ) : B Λ := η (mf γ a) * ξ (mf γ b)

theorem udot_eq (p : Pt Λ) (i j : Λ) :
    (hd p).udot i j = -(acoef p i j • (1 : B Λ)) - exp (p (.inl i) + p (.inl j)) •
      ∑ γ, (qq γ i i - qq γ i j - qq γ j i + qq γ j j) := by
  have h := (hd p).neg_udot i j
  have e : ∑ γ, ((hd p).ψb γ i - (hd p).ψb γ j) * ((hd p).ψ γ i - (hd p).ψ γ j) =
      ∑ γ, (qq γ i i - qq γ i j - qq γ j i + qq γ j j) := by
    refine sum_congr rfl fun γ _ => ?_
    simp only [hd_ψ, hd_ψb, qq, sub_mul, mul_sub]; abel
  rw [e] at h
  rw [← neg_neg ((hd p).udot i j), h, neg_add, ← sub_eq_add_neg, acoef]
  rfl

theorem nn_eq (p : Pt Λ) (i : Λ) : (hd p).nn i = ∑ γ, qq γ i i := rfl

theorem acoef_self (p : Pt Λ) (i : Λ) : acoef p i i = 1 := by simp [acoef]

theorem acoef_symm (p : Pt Λ) (i j : Λ) : acoef p i j = acoef p j i := by
  simp only [acoef, add_comm (p (.inl i))]
  rw [← cosh_neg, neg_sub]; ring

/-- The action in horospherical coordinates, split into its body and its fermionic part. -/
theorem action_split (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) (h : Λ → ℝ) (p : Pt Λ) :
    (1 / 4 : ℝ) • ∑ i, ∑ j, β i j • ((hd p).udot i i - (hd p).udot i j -
        (hd p).udot j i + (hd p).udot j j) + ∑ i, h i • ((hd p).zS i - 1) =
      ((1 / 2) * ∑ i, ∑ j, β i j * (acoef p i j - 1) +
          ∑ i, h i * (hz (p (.inl i)) (p (.inr i)) - 1)) • (1 : B Λ) +
        ∑ γ, ∑ a, ∑ b, ((if a = b then ∑ j, β a j * exp (p (.inl a) + p (.inl j)) +
            h a * exp (p (.inl a)) else 0) - β a b * exp (p (.inl a) + p (.inl b))) • qq γ a b := by
  set e : Λ → Λ → ℝ := fun i j => exp (p (.inl i) + p (.inl j))
  set Ψ : Λ → Λ → B Λ := fun i j => ∑ γ, (qq γ i i - qq γ i j - qq γ j i + qq γ j j)
  have hΨ0 : ∀ i, Ψ i i = 0 := fun i => by simp [Ψ]
  have hΨs : ∀ i j, Ψ i j = Ψ j i := fun i j => sum_congr rfl fun γ _ => by abel
  have hes : ∀ i j, e i j = e j i := fun i j => by simp only [e, add_comm]
  have hbr : ∀ i j, (hd p).udot i i - (hd p).udot i j - (hd p).udot j i + (hd p).udot j j =
      (2 * (acoef p i j - 1)) • (1 : B Λ) + (2 * e i j) • Ψ i j := by
    intro i j
    simp only [udot_eq]
    change -(acoef p i i • (1 : B Λ)) - e i i • Ψ i i - (-(acoef p i j • 1) - e i j • Ψ i j) -
      (-(acoef p j i • 1) - e j i • Ψ j i) + (-(acoef p j j • 1) - e j j • Ψ j j) = _
    rw [hΨ0, hΨ0, acoef_self, acoef_self, acoef_symm p j i, hes j i, hΨs j i]
    module
  have hz1 : ∀ i, (hd p).zS i - 1 = (hz (p (.inl i)) (p (.inr i)) - 1) • (1 : B Λ) +
      exp (p (.inl i)) • ∑ γ, qq γ i i := fun i => by
    simp only [HData.zS, nn_eq]
    change hz (p (.inl i)) (p (.inr i)) • (1 : B Λ) + exp (p (.inl i)) • ∑ γ, qq γ i i - 1 = _
    module
  simp only [hbr, hz1]
  have hq : ∀ γ, (1 / 2 : ℝ) • ∑ i, ∑ j, (β i j * e i j) •
      (qq γ i i - qq γ i j - qq γ j i + qq γ j j) + ∑ i, (h i * exp (p (.inl i))) • qq γ i i =
      ∑ a, ∑ b, ((if a = b then ∑ j, β a j * e a j + h a * exp (p (.inl a)) else 0) -
        β a b * e a b) • qq γ a b := fun γ =>
    quad_identity (fun i j => β i j * e i j) (fun i j => by rw [hβ, hes])
      (fun i => h i * exp (p (.inl i))) (qq γ)
  have S1 : ∑ i, ∑ j, β i j • ((2 * (acoef p i j - 1)) • (1 : B Λ) + (2 * e i j) • Ψ i j) =
      (2 * ∑ i, ∑ j, β i j * (acoef p i j - 1)) • (1 : B Λ) +
        (2 : ℝ) • ∑ i, ∑ j, (β i j * e i j) • Ψ i j := by
    simp only [smul_add, sum_add_distrib, smul_smul, Finset.mul_sum, sum_smul, smul_sum]
    congr 1 <;> exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by congr 1; ring
  have S2 : ∑ i, h i • ((hz (p (.inl i)) (p (.inr i)) - 1) • (1 : B Λ) +
      exp (p (.inl i)) • ∑ γ, qq γ i i) =
      (∑ i, h i * (hz (p (.inl i)) (p (.inr i)) - 1)) • (1 : B Λ) +
        ∑ γ, ∑ i, (h i * exp (p (.inl i))) • qq γ i i := by
    simp only [smul_add, sum_add_distrib, smul_smul, sum_smul, smul_sum]
    congr 1
    rw [Finset.sum_comm]
  have S3 : ∑ i, ∑ j, (β i j * e i j) • Ψ i j =
      ∑ γ, ∑ i, ∑ j, (β i j * e i j) • (qq γ i i - qq γ i j - qq γ j i + qq γ j j) := by
    simp only [Ψ, smul_sum]
    rw [show (∑ i, ∑ j, ∑ γ, (β i j * e i j) • (qq γ i i - qq γ i j - qq γ j i + qq γ j j)) =
      ∑ i, ∑ γ, ∑ j, (β i j * e i j) • (qq γ i i - qq γ i j - qq γ j i + qq γ j j) from
      sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]
  rw [S1, S2, S3, ← sum_congr rfl fun γ _ => hq γ, sum_add_distrib, ← smul_sum]
  module

end

end ArborealDecay.BCHS

end
