import Step.Structure

/-!
# The renormalisation group map over a general algebra (Section `sec:obs-flow`)

Section `sec:obs-flow` extends the renormalisation group map of Section `sec:step-def` to the
algebra with observables: `K_{j+1}` "is defined by the same formula as in Definition `def:K+`",
with `V` and `u` replaced by the extended ones.  Propositions `prop:ZVK` and `prop:consistency`
"also hold for this extended definition; the proofs are the same".

This file makes that construction generic.  The combinatorics (`Pj`, `Comp`, `clo`, `pairsU`,
`Xcal`, `Bbox`, `GCond`, `Gset`) is that of `Step`; only the algebra changes.

## The algebraic data (`RGAlg`)
* `R`: a commutative `ℂ`-algebra, the even elements of the algebra of fields at a point of the
  flow (in the bulk `EvR Λ`);
* `R2`: a commutative `ℂ`-algebra, the doubled algebra (in the bulk `EvR (Λ ⊔ Λ)`);
* `θ, ι : R →ₐ[ℂ] R2`: the doubling `θ` and the inclusion (functions of `ψ` only);
* `E : R2 →ₗ[ℂ] R`: the expectation `𝔼_{C_{j+1}}`.

## The ingredients (`RGIngr`)
For `j`-blocks `B` (given by their index `b`) and polymers `X`:
* `I0 b = e^{-V_j(B)}`;
* `eV b = e^{-V_{j+1}(B)}`, `eum b = e^{-u_{j+1}(B)}`, so that
  `It b = eum b * eV b = e^{-(u+V)_{j+1}(B)}` (`It`);
* `eu b = e^{u_{j+1}(B)}`, and the prefactor `e^{u_{j+1}(U)}` is `∏_{B ∈ 𝓑_j(U)} eu B` (`PrefG`);
* `J b X = J(B, X)`;
* `K X = K_j(X)` (used on connected polymers and extended by `KextG`).

## The map
`dIG`, `dIPowG`, `KtilG`, `KchkCG`, `KchkG`, `KnextG` are `δI(B)`, `(δI)^X`, `K̃(W)`, `Ǩ(W)`
(connected `W`), `Ǩ(X)` and `K_{j+1}(U)` (`e:K+-def`–`e:deltaI`); `ZjG` and `ZnextG` are
`∑_X e^{-V_j(Λ ∖ X)} K_j(X)` and `e^{-u_{j+1}(Λ)} ∑_U e^{-V_{j+1}(Λ ∖ U)} K_{j+1}(U)`.
-/

namespace Obs.Gen

noncomputable section

open Finset Grassmann Loc FRD Step

/-- The algebraic data of one renormalisation group step. -/
structure RGAlg (R R2 : Type*) [CommRing R] [CommRing R2] [Algebra ℂ R] [Algebra ℂ R2] where
  /-- The doubling `θ`. -/
  θ : R →ₐ[ℂ] R2
  /-- The inclusion of functions of `ψ` only. -/
  ι : R →ₐ[ℂ] R2
  /-- The expectation `𝔼_C`. -/
  E : R2 →ₗ[ℂ] R

variable {d L N : ℕ} [NeZero L]

/-- The ingredients of one renormalisation group step. -/
structure RGIngr (d L N : ℕ) [NeZero L] (R : Type*) where
  /-- `e^{-V_j(B)}`. -/
  I0 : (Fin d → ℕ) → R
  /-- `e^{-V_{j+1}(B)}`. -/
  eV : (Fin d → ℕ) → R
  /-- `e^{u_{j+1}(B)}`. -/
  eu : (Fin d → ℕ) → R
  /-- `e^{-u_{j+1}(B)}`. -/
  eum : (Fin d → ℕ) → R
  /-- `J(B, X)`. -/
  J : (Fin d → ℕ) → Finset (Lam d L N) → R
  /-- `K_j(X)`. -/
  K : Finset (Lam d L N) → R

/-- Applying a map to the ingredients. -/
def RGIngr.map {R S : Type*} (φ : R → S) (F : RGIngr d L N R) : RGIngr d L N S where
  I0 b := φ (F.I0 b)
  eV b := φ (F.eV b)
  eu b := φ (F.eu b)
  eum b := φ (F.eum b)
  J b X := φ (F.J b X)
  K X := φ (F.K X)

/-- A product over the `j`-blocks of `X`. -/
def bpow {M : Type*} [CommMonoid M] (j : ℕ) (f : (Fin d → ℕ) → M) (X : Finset (Lam d L N)) : M :=
  ∏ b ∈ blocks j X, f b

/-- The extension `K(X) = ∏_{Y ∈ Comp(X)} K(Y)` (`e:K-prod`). -/
def KextG {M : Type*} [CommMonoid M] (j : ℕ) (K : Finset (Lam d L N) → M)
    (X : Finset (Lam d L N)) : M :=
  ∏ Y ∈ Comp j X, K Y

section Map

variable {R R2 : Type*} [CommRing R] [CommRing R2] [Algebra ℂ R] [Algebra ℂ R2]
  (A : RGAlg R R2) (j : ℕ) (F : RGIngr d L N R)

/-- `e^{-(u+V)_{j+1}(B)} = e^{-u_{j+1}(B)} e^{-V_{j+1}(B)}`. -/
def It (b : Fin d → ℕ) : R := F.eum b * F.eV b

/-- `e^{-(u+V)_{j+1}(X)} = ∏_{B ∈ 𝓑_j(X)} e^{-(u+V)_{j+1}(B)}`. -/
def ItPow (X : Finset (Lam d L N)) : R := bpow j (It F) X

/-- The prefactor `e^{u_{j+1}(U)} = ∏_{B ∈ 𝓑_j(U)} e^{u_{j+1}(B)}`. -/
def PrefG (U : Finset (Lam d L N)) : R := bpow j F.eu U

/-- `δI(B) = θ e^{-V_j(B)} - e^{-(u+V)_{j+1}(B)}` (`e:deltaI`). -/
def dIG (b : Fin d → ℕ) : R2 := A.θ (F.I0 b) - A.ι (It F b)

/-- `(δI)^X = ∏_{B ∈ 𝓑_j(X)} δI(B)`. -/
def dIPowG (X : Finset (Lam d L N)) : R2 := bpow j (dIG A F) X

/-- `K̃(W) = ∑_{Y ∈ 𝒫_j(W)} θ K(W ∖ Y) (δI)^Y`. -/
def KtilG (W : Finset (Lam d L N)) : R2 :=
  ∑ Y ∈ Pj j W, A.θ (KextG j F.K (W \ Y)) * dIPowG A j F Y

/-- `Ǩ(W) = K̃(W) - ∑_{B ∈ 𝓑_j(W)} θ J(B, W)` for connected `W`. -/
def KchkCG (W : Finset (Lam d L N)) : R2 :=
  KtilG A j F W - ∑ b ∈ blocks j W, A.θ (F.J b W)

/-- `Ǩ(X) = ∏_{W ∈ Comp(X)} Ǩ(W)` (`e:K+-def2`). -/
def KchkG (X : Finset (Lam d L N)) : R2 := ∏ W ∈ Comp j X, KchkCG A j F W

/-- `∏_{(B,X) ∈ 𝒳} θ J(B, X)`. -/
def JprodG (𝒳 : Finset ((Fin d → ℕ) × Finset (Lam d L N))) : R2 :=
  ∏ p ∈ 𝒳, A.θ (F.J p.1 p.2)

/-- The summand of `K_{j+1}(U)`: `e^{-(u+V)_{j+1}(U ∖ (X̌ ∪ X_𝒳))} 𝔼[Ǩ(X̌) ∏ θ J]`. -/
def KtermG (U : Finset (Lam d L N)) (g : GT d L N) : R :=
  ItPow j F (U \ (g.2 ∪ Xcal g.1)) * A.E (KchkG A j F g.2 * JprodG A F g.1)

/-- `K_{j+1}(U)` (`e:K+-def`). -/
def KnextG (U : Finset (Lam d L N)) : R :=
  PrefG j F U * ∑ g ∈ Gset j U, KtermG A j F U g

/-- `Z_j = ∑_{X ∈ 𝒫_j} e^{-V_j(Λ ∖ X)} K_j(X)`. -/
def ZjG : R := ∑ X ∈ Pj j univ, bpow j F.I0 (univ \ X) * KextG j F.K X

/-- `e^{-u_{j+1}(Λ)} ∑_{U ∈ 𝒫_{j+1}} e^{-V_{j+1}(Λ ∖ U)} K_{j+1}(U)`. -/
def ZnextG : R :=
  bpow j F.eum (univ : Finset (Lam d L N)) *
    ∑ U ∈ Pj (j + 1) univ, bpow j F.eV (univ \ U) * KnextG A j F U

end Map

end

end Obs.Gen
