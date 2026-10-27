import Mathlib

/-!
# The `ℍ^{0|2}` sigma model

Definitions from Section 2.1 ("`ℍ^{0|2}` model and arboreal gas") of `h02.tex`.

* The Grassmann algebra `Ω^{2Λ}` with generators `(ξ_i, η_i)_{i ∈ Λ}` is the exterior algebra
  over `ℝ` of the real vector space `Λ ⊕ Λ → ℝ`, where the basis vector at `Sum.inl i` is `ξ_i`
  and the basis vector at `Sum.inr i` is `η_i`.
* `z_i := 1 - ξ_i η_i` and `u_i · u_j := -ξ_i η_j - ξ_j η_i - z_i z_j`.
* The fermionic derivatives `∂_{ξ_i}`, `∂_{η_i}` are the odd derivations given by contraction
  (`CliffordAlgebra.contractLeft`) with the coordinate functionals of `ξ_i`, `η_i`; they satisfy
  `∂_{ξ_i}(ξ_i F) = F` and `∂_{ξ_i} F = 0` for forms `F` not containing `ξ_i`.
* The hyperbolic fermionic integral is
  `[F]_0 = ∂_{η_N} ∂_{ξ_N} ⋯ ∂_{η_1} ∂_{ξ_1} (z_1 ⋯ z_N)⁻¹ F`, where `1, …, N` is an
  enumeration of `Λ`.  We write it as the composition of the operators
  `F ↦ ∂_{η_i} ∂_{ξ_i} (z_i⁻¹ F)`, applied in the order of the list
  `(Finset.univ : Finset Λ).toList`, and read off the resulting element of `ℝ`.
* The action is
  `H_{β,h}(u) = 1/4 ∑_{i,j} β_{ij} (u_i - u_j)² + ∑_i h_i (z_i - 1)`, where
  `(u_i - u_j)² = u_i·u_i - u_i·u_j - u_j·u_i + u_j·u_j`, and `[F]_{β,h} = [F e^{-H_{β,h}}]_0`,
  where the exponential of the nilpotent element `-H_{β,h}` is its (terminating) power series.
-/

namespace H02

noncomputable section

/-- The real vector space spanned by the generators: `Sum.inl i ↦ ξ_i`, `Sum.inr i ↦ η_i`. -/
abbrev Gen (Λ : Type*) := Λ ⊕ Λ → ℝ

/-- The Grassmann algebra `Ω^{2Λ}` with generators `(ξ_i, η_i)_{i ∈ Λ}`. -/
abbrev Grassmann (Λ : Type*) := ExteriorAlgebra ℝ (Gen Λ)

variable {Λ : Type*} [DecidableEq Λ]

/-- The generator `ξ_i`. -/
def ξ (i : Λ) : Grassmann Λ := ExteriorAlgebra.ι ℝ (Pi.single (Sum.inl i) 1)

/-- The generator `η_i`. -/
def η (i : Λ) : Grassmann Λ := ExteriorAlgebra.ι ℝ (Pi.single (Sum.inr i) 1)

/-- `z_i = √(1 - 2 ξ_i η_i) := 1 - ξ_i η_i`. -/
def z (i : Λ) : Grassmann Λ := 1 - ξ i * η i

/-- The `ℍ^{0|2}` inner product `u_i · u_j = -ξ_i η_j - ξ_j η_i - z_i z_j`. -/
def dot (i j : Λ) : Grassmann Λ := -(ξ i * η j) - ξ j * η i - z i * z j

/-- The fermionic derivative `∂_{ξ_i}`. -/
def dξ (i : Λ) : Grassmann Λ →ₗ[ℝ] Grassmann Λ :=
  CliffordAlgebra.contractLeft (LinearMap.proj (R := ℝ) (φ := fun _ : Λ ⊕ Λ => ℝ) (Sum.inl i))

/-- The fermionic derivative `∂_{η_i}`. -/
def dη (i : Λ) : Grassmann Λ →ₗ[ℝ] Grassmann Λ :=
  CliffordAlgebra.contractLeft (LinearMap.proj (R := ℝ) (φ := fun _ : Λ ⊕ Λ => ℝ) (Sum.inr i))

/-- One factor `F ↦ ∂_{η_i} ∂_{ξ_i} (z_i⁻¹ F)` of the hyperbolic fermionic integral. -/
def intStep (i : Λ) : Grassmann Λ →ₗ[ℝ] Grassmann Λ :=
  dη i ∘ₗ dξ i ∘ₗ LinearMap.mulLeft ℝ (Ring.inverse (z i))

/-- `∏_{i ∈ l} (∂_{η_i} ∂_{ξ_i} z_i⁻¹)`, where the head of the list `l` is applied first. -/
def berezin (l : List Λ) : Grassmann Λ →ₗ[ℝ] Grassmann Λ :=
  l.foldl (fun L i => intStep i ∘ₗ L) LinearMap.id

variable [Fintype Λ]

/-- The hyperbolic fermionic integral `[F]_0 = ∫_{(ℍ^{0|2})^Λ} F ∈ ℝ`. -/
def int0 (F : Grassmann Λ) : ℝ :=
  ExteriorAlgebra.algebraMapInv (berezin (Finset.univ : Finset Λ).toList F)

/-- The action `H_{β,h}(u) = 1/4 ∑_{i,j} β_{ij} (u_i - u_j)² + ∑_i h_i (z_i - 1)`. -/
def action (β : Λ → Λ → ℝ) (h : Λ → ℝ) : Grassmann Λ :=
  (1 / 4 : ℝ) • ∑ i, ∑ j, β i j • (dot i i - dot i j - dot j i + dot j j) +
    ∑ i, h i • (z i - 1)

/-- The unnormalised expectation `[F]_{β,h} = [F e^{-H_{β,h}}]_0`. -/
def expect (β : Λ → Λ → ℝ) (h : Λ → ℝ) (F : Grassmann Λ) : ℝ :=
  int0 (F * IsNilpotent.exp (-action β h))

end

end H02
