import Obs.StepObsStmt

/-!
# Corrections to the component statements of `thm:step-obs`

Two corrections to `SmallObsStmt` / `LargeObsStmt` of `Obs.StepObsStmt` (which are false as
stated):

1. **Separation (`SepHyp`).**  The text uses that `a` is positioned in the centre of all of its
   blocks, so that `a, b` in distinct `(j+1)`-blocks implies `|a - b|_∞ ≥ ½ L^{j+1}` and hence
   `C_{j+1}(a, b) = 0`.  In the formalisation blocks are aligned at the origin, so this is an
   extra hypothesis: `blk (j+1) a ≠ blk (j+1) b → C a b = 0`.  (It follows from `GoodCov.range`
   if `a` is centred in its blocks; for `j + 1 = N` it is vacuous since there is one block.)
   Without it, for `K = 0`, `V^∅ = 0` and `a, b` neighbours in adjacent `(j+1)`-blocks,
   `π_obs K_{j+1}(B̄_a) = ± ½ λ_a λ_b C(a, b) σ_a σ̄_b ≠ 0` violates `e:K+obs-bd`.

2. **The two-block terms (`LpairG`, `e:Kquad-obs`).**  The terms `(δI)^X` for disconnected
   `X = B ∪ B'` with `B' ⊂ B̄` (not small sets, hence in `LlinLG`) cancel the second-order
   `V^obs` terms of the single-block small set terms (`lem:smallset-Vobs`).  So they are moved
   from the large set sum to the small set sum: `SmallObsStmt'` bounds
   `π_obs (𝓛_{𝒮}(U) + 𝓛_{pair}(U))` and `LargeObsStmt'` bounds `π_obs (𝓛_{𝒫∖𝒮}(U) - 𝓛_{pair}(U))`.
-/

namespace Obs

noncomputable section

open Finset Grassmann SA Loc Step LocObs Gen

variable {d L N : ℕ} [NeZero L]

namespace Gen

variable {R R2 : Type*} [CommRing R] [CommRing R2] [Algebra ℂ R] [Algebra ℂ R2]
  (A : RGAlg R R2) (j : ℕ) (F : RGIngr d L N R)

/-- The disconnected two-block polymers `X = B ∪ B'` with `B' ⊂ B̄` and `X̄ = U`. -/
def pairSets (j : ℕ) (U : Finset (Lam d L N)) : Finset (Finset (Lam d L N)) :=
  open Classical in
  univ.filter fun X => IsPolymer j X ∧ clo j X = U ∧ nb j X = 2 ∧ nb (j + 1) X = 1 ∧
    ¬ IsConnected j X

/-- `𝓛_{pair}(U) = ∑_{X = B ∪ B' disconnected, B' ⊂ B̄, X̄ = U} e^{u(U)} e^{-(u+V)(U ∖ X)} 𝔼 (δI)^X`
(the two-block terms of `e:Kquad-obs`). -/
def LpairG (U : Finset (Lam d L N)) : R :=
  ∑ X ∈ pairSets j U, prefG j F U X * A.E (dIPowG A j F X)

end Gen

/-- The separation hypothesis: `C(a, b) = 0` if `a` and `b` lie in distinct `(j+1)`-blocks. -/
def SepHyp (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (a b : Lam d L N) : Prop :=
  blk (j + 1) a ≠ blk (j + 1) b → C a b = 0

/-- **Small sets** (corrected): the bound on `π_obs (𝓛_{j+1,𝒮}(U) + 𝓛_{pair}(U))`. -/
def SmallObsStmt' (d : ℕ) : Prop :=
  ∃ (C₀ : ℝ) (m L₀ : ℕ), 0 ≤ C₀ ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ (N j : ℕ), j < N → ∀ (ℓ₀ : ℝ), 0 < ℓ₀ →
    ∀ (c : Case) (P : Prop) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (Vb : Vcoup) (Vo : Coup c)
      (K : Finset (Lam d L N) → OE c (Lam d L N)) (a b : Lam d L N),
      StepObsHyp c P j ℓ₀ C Vb Vo K a b → SepHyp j C a b →
      Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) Vb +
          Knorm j (ellj d L ℓ₀ j) A (bulkK K) ≤ ENNReal.ofReal ε₀ →
      VnormObs c ℓ₀ a b j Vo + KnormObs c ℓ₀ a b j A K ≤ ENNReal.ofReal ε₀ →
      ∀ U : Finset (Lam d L N), IsConn (j + 1) U →
        wnormO c ℓ₀ a b (j + 1) A U
            (πobs (LlinSG (obsA c C) j (obsI j C Vb Vo K a b) U +
              LpairG (obsA c C) j (obsI j C Vb Vo K a b) U)) ≤
          ENNReal.ofReal (C₀ * (if j + 1 < N then (L : ℝ) ^ (-dplus d) else (L : ℝ) ^ m)) *
              KnormObs c ℓ₀ a b j A K +
            ENNReal.ofReal (C₀ * (L : ℝ) ^ m) *
              quadO (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) Vb)
                (VnormObs c ℓ₀ a b j Vo) (Knorm j (ellj d L ℓ₀ j) A (bulkK K))
                (KnormObs c ℓ₀ a b j A K)

/-- **Large sets** (corrected): the bound on `π_obs (𝓛_{j+1,𝒫∖𝒮}(U) - 𝓛_{pair}(U))`. -/
def LargeObsStmt' (d : ℕ) : Prop :=
  ∃ (C₀ η ν : ℝ) (m L₀ : ℕ), 0 ≤ C₀ ∧ 0 < η ∧ 0 < ν ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ (N j : ℕ), j < N → ∀ (ℓ₀ : ℝ), 0 < ℓ₀ →
    ∀ (c : Case) (P : Prop) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (Vb : Vcoup) (Vo : Coup c)
      (K : Finset (Lam d L N) → OE c (Lam d L N)) (a b : Lam d L N),
      StepObsHyp c P j ℓ₀ C Vb Vo K a b → SepHyp j C a b →
      Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) Vb +
          Knorm j (ellj d L ℓ₀ j) A (bulkK K) ≤ ENNReal.ofReal ε₀ →
      VnormObs c ℓ₀ a b j Vo + KnormObs c ℓ₀ a b j A K ≤ ENNReal.ofReal ε₀ →
      ∀ U : Finset (Lam d L N), IsConn (j + 1) U →
        wnormO c ℓ₀ a b (j + 1) A U
            (πobs (LlinLG (obsA c C) j (obsI j C Vb Vo K a b) U -
              LpairG (obsA c C) j (obsI j C Vb Vo K a b) U)) ≤
          ENNReal.ofReal (C₀ * (L : ℝ) ^ m * A ^ (-η)) * KnormObs c ℓ₀ a b j A K +
            ENNReal.ofReal (C₀ * (L : ℝ) ^ m * A ^ ν) *
              quadO (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) Vb)
                (VnormObs c ℓ₀ a b j Vo) (Knorm j (ellj d L ℓ₀ j) A (bulkK K))
                (KnormObs c ℓ₀ a b j A K)

/-- `π_obs 𝓛 = π_obs (𝓛_𝒮 + 𝓛_pair) + π_obs (𝓛_{𝒫∖𝒮} - 𝓛_pair)`. -/
theorem πobs_Llin_split {c : Case} (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (Vb : Vcoup)
    (Vo : Coup c) (K : Finset (Lam d L N) → OE c (Lam d L N)) (a b : Lam d L N)
    (U : Finset (Lam d L N)) :
    πobs (LlinSG (obsA c C) j (obsI j C Vb Vo K a b) U) +
        πobs (LlinLG (obsA c C) j (obsI j C Vb Vo K a b) U) =
      πobs (LlinSG (obsA c C) j (obsI j C Vb Vo K a b) U +
          LpairG (obsA c C) j (obsI j C Vb Vo K a b) U) +
        πobs (LlinLG (obsA c C) j (obsI j C Vb Vo K a b) U -
          LpairG (obsA c C) j (obsI j C Vb Vo K a b) U) := by
  rw [map_add, map_sub]; abel

end

end Obs
