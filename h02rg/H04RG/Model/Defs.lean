import H02.Integral

/-!
# The `ℍ^{0|4}` sigma model: definitions

Section 1 of `h04/h04-d5-outline.tex`.

We reuse the Grassmann algebra of `H02` on the doubled vertex set `Λ × Fin 2`: the generators
`ξ_{(x,a)}, η_{(x,a)}` (`a ∈ Fin 2`) are the two flavours `ξ^a_x, η^a_x` at the vertex `x`.

* `s_x = ∑_a ξ^a_x η^a_x`, `q_x = ξ^0_x η^0_x ξ^1_x η^1_x`, and
  `z_x = √(1 - 2 s_x) := 1 - s_x - q_x` (see `H04RG.z_sq` for `z_x² = 1 - 2 s_x`).
* `u_x · u_y = -∑_a (ξ^a_x η^a_y + ξ^a_y η^a_x) - z_x z_y`.
* The fermionic integral is `[F]_0 = ∏_x ∂_{η^1_x} ∂_{ξ^1_x} ∂_{η^0_x} ∂_{ξ^0_x} (z_x⁻¹ F)`.
  Since the pair derivations `∂_{η_i} ∂_{ξ_i}` are even, they commute with each other and with
  the factors `z_y⁻¹`, `y ≠ x`; hence `[F]_0` equals the flat Berezin integral (top coefficient)
  of `(∏_x z_x⁻¹) F`, taken with the pairs in the order of `Finset.univ.toList`. This is how we
  define it (`H04RG.int0`).
* The action is `H_{β,h} = 1/4 ∑_{x,y} β_{xy} (u_x - u_y)² + ∑_x h_x (z_x - 1)`, exactly as for
  `ℍ^{0|2}` in `H02.action`, and `[F]_{β,h} = [F e^{-H_{β,h}}]_0`.
-/

namespace H04RG

noncomputable section

open H02 (ξ η dξ dη C cv pc)

variable {Λ : Type*} [DecidableEq Λ]

/-- The Grassmann algebra with generators `ξ^a_x, η^a_x`, `x ∈ Λ`, `a ∈ Fin 2`. -/
abbrev A (Λ : Type*) := H02.Grassmann (Λ × Fin 2)

/-- `s_x = ∑_a ξ^a_x η^a_x`. -/
def s (x : Λ) : A Λ := ∑ a : Fin 2, ξ (x, a) * η (x, a)

/-- `q_x = ξ^0_x η^0_x ξ^1_x η^1_x`. -/
def q (x : Λ) : A Λ := ξ (x, 0) * η (x, 0) * (ξ (x, 1) * η (x, 1))

/-- `z_x = √(1 - 2 s_x) := 1 - s_x - q_x`. -/
def z (x : Λ) : A Λ := 1 - s x - q x

/-- The `ℍ^{0|4}` inner product `u_x · u_y = -∑_a (ξ^a_x η^a_y + ξ^a_y η^a_x) - z_x z_y`. -/
def dot (x y : Λ) : A Λ :=
  -(∑ a : Fin 2, (ξ (x, a) * η (y, a) + ξ (y, a) * η (x, a))) - z x * z y

/-! ### Central versions

`s_x, q_x, z_x` are even, hence central; their central versions live in the commutative ring
`H02.C (Λ × Fin 2)` (the center), where products over `Λ` make sense. -/

/-- `s_x` in the center. -/
def sC (x : Λ) : C (Λ × Fin 2) := ∑ a : Fin 2, pc (x, a) (x, a)

/-- `q_x` in the center. -/
def qC (x : Λ) : C (Λ × Fin 2) := pc (x, 0) (x, 0) * pc (x, 1) (x, 1)

/-- `z_x` in the center. -/
def zC (x : Λ) : C (Λ × Fin 2) := 1 - sC x - qC x

@[simp] theorem cv_sC (x : Λ) : cv (sC x) = s x := by simp [sC, s]
@[simp] theorem cv_qC (x : Λ) : cv (qC x) = q x := by simp [qC, q]
@[simp] theorem cv_zC (x : Λ) : cv (zC x) = z x := by simp [zC, z]

/-- The pair derivation `F ↦ ∂_{η_i} ∂_{ξ_i} F`. -/
def pairStep (i : Λ × Fin 2) : A Λ →ₗ[ℝ] A Λ := dη i ∘ₗ dξ i

/-- The flat Berezin operator `∏_{i ∈ l} ∂_{η_i} ∂_{ξ_i}`; the head of `l` is applied first. -/
def flat (l : List (Λ × Fin 2)) : A Λ →ₗ[ℝ] A Λ :=
  l.foldl (fun L i => pairStep i ∘ₗ L) LinearMap.id

variable [Fintype Λ]

/-- The `ℍ^{0|4}` fermionic integral `[F]_0 = ∫ ∏_x ∂_{η^1_x} ∂_{ξ^1_x} ∂_{η^0_x} ∂_{ξ^0_x} z_x⁻¹ F`.
The volume form `∏_x z_x⁻¹` is formed in the center (see `H04RG.cv_inverse_zC` for
`cv (Ring.inverse (zC x)) = Ring.inverse (z x)`). -/
def int0 (F : A Λ) : ℝ :=
  ExteriorAlgebra.algebraMapInv
    (flat (Finset.univ : Finset (Λ × Fin 2)).toList (cv (∏ x, Ring.inverse (zC x)) * F))

/-- The action `H_{β,h} = 1/4 ∑_{x,y} β_{xy} (u_x - u_y)² + ∑_x h_x (z_x - 1)`. -/
def action (β : Λ → Λ → ℝ) (h : Λ → ℝ) : A Λ :=
  (1 / 4 : ℝ) • ∑ x, ∑ y, β x y • (dot x x - dot x y - dot y x + dot y y) +
    ∑ x, h x • (z x - 1)

/-- The unnormalised expectation `[F]_{β,h} = [F e^{-H_{β,h}}]_0`. -/
def expect (β : Λ → Λ → ℝ) (h : Λ → ℝ) (F : A Λ) : ℝ :=
  int0 (F * IsNilpotent.exp (-action β h))

/-- The normalised expectation `⟨F⟩_{β,h} = [F]_{β,h} / [1]_{β,h}`. -/
def avg (β : Λ → Λ → ℝ) (h : Λ → ℝ) (F : A Λ) : ℝ := expect β h F / expect β h 1

end

end H04RG
