import Obs.GenericStructure

/-!
# The bulk renormalisation group map as an instance of the generic one

With `R = EvR Λ`, `R2 = EvR (Λ ⊔ Λ)`, `θ = thetaE`, `ι = inclE`, `E = ECE C` (`bulkA`) and the
bulk ingredients (`bulkI`: `e^{-V_j(B)}`, `e^{-V_{j+1}(B)}`, `e^{±u_{j+1}|B|}`, `J = Jb`,
`K`), the generic map is `Step`'s:
* `dIG`, `dIPowG`, `KtilG`, `KchkG`, `ItPow` are `dI`, `dIPow`, `Ktil`, `Kchk`, `InextPow`;
* `KnextG U = Knext U` for `j`-polymers `U` (`KnextG_bulk`), `ZjG = Zj` (`ZjG_bulk`) and
  `ZnextG = Znext` (`ZnextG_bulk`).
The hypotheses of the generic theorems hold (`bulk_hE`, `bulk_hJ`, `bulk_hu`, `bulk_suppHyp`,
`bulk_sep`), and `Step.ZVK`, `Step.Knext_union`, `Step.ZVK'` are recovered (`ZVK_bulk`,
`Knext_union_bulk`, `ZVK'_bulk`).
-/

namespace Obs.Gen

noncomputable section

open Finset Grassmann Loc FRD Step

variable {d L N : ℕ} [NeZero L]

/-- The bulk algebraic data. -/
def bulkA (C : Matrix (Lam d L N) (Lam d L N) ℝ) :
    RGAlg (EvR (Lam d L N)) (EvR (Lam d L N ⊕ Lam d L N)) where
  θ := thetaE
  ι := inclE
  E := ECE C

/-- The bulk ingredients. -/
def bulkI (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (V : Vcoup) (K : Act d L N) :
    RGIngr d L N (EvR (Lam d L N)) where
  I0 b := gexp (-(VE V (blockSet j b) : EvR (Lam d L N)))
  eV b := gexp (-(VE (uVnext j C V K).2 (blockSet j b) : EvR (Lam d L N)))
  eu b := algebraMap ℂ _ (Complex.exp ((uVnext j C V K).1 * (blockSet (L := L) (N := N) j b).card))
  eum b := algebraMap ℂ _
    (Complex.exp (-((uVnext j C V K).1 * (blockSet (L := L) (N := N) j b).card)))
  J := Jb j K
  K := K

section

variable (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (V : Vcoup) (K : Act d L N)

theorem It_bulk (b : Fin d → ℕ) : It (bulkI j C V K) b = Inext j C V K b := by
  rw [It, Inext, Algebra.smul_def]; rfl

theorem ItPow_bulk (X : Finset (Lam d L N)) : ItPow j (bulkI j C V K) X = InextPow j C V K X := by
  rw [ItPow, bpow, InextPow]
  exact prod_congr rfl fun b _ => It_bulk j C V K b

theorem dIG_bulk (b : Fin d → ℕ) : dIG (bulkA C) (bulkI j C V K) b = dI j C V K b := by
  rw [dIG, dI, It_bulk]; rfl

theorem dIPowG_bulk (X : Finset (Lam d L N)) :
    dIPowG (bulkA C) j (bulkI j C V K) X = dIPow j C V K X := by
  rw [dIPowG, bpow, dIPow]
  exact prod_congr rfl fun b _ => dIG_bulk j C V K b

/-- `∏_{B ∈ 𝓑_j(S)} f(|B|) = f(|S|)` for exponentials. -/
theorem prod_exp_card (c : ℂ) {S : Finset (Lam d L N)} (hS : IsPolymer j S) :
    ∏ b ∈ blocks j S, algebraMap ℂ (EvR (Lam d L N))
        (Complex.exp (c * (blockSet (L := L) (N := N) j b).card)) =
      algebraMap ℂ (EvR (Lam d L N)) (Complex.exp (c * S.card)) := by
  rw [← map_prod, ← Complex.exp_sum, ← mul_sum]
  congr 3
  conv_rhs => rw [← biUnion_blocks hS]
  rw [card_biUnion fun b _ b' _ hne => blockSet_disjoint hne, Nat.cast_sum]

theorem PrefG_bulk {U : Finset (Lam d L N)} (hU : IsPolymer j U) :
    PrefG j (bulkI j C V K) U =
      algebraMap ℂ _ (Complex.exp ((uVnext j C V K).1 * U.card)) :=
  prod_exp_card j _ hU

/-- **Bridge**: the generic `K_{j+1}(U)` is `Step.Knext` for `j`-polymers `U`. -/
theorem KnextG_bulk {U : Finset (Lam d L N)} (hU : IsPolymer j U) :
    KnextG (bulkA C) j (bulkI j C V K) U = Knext j C V K U := by
  rw [KnextG, Knext, PrefG_bulk j C V K hU, Algebra.smul_def]
  congr 1

/-! ### The hypotheses of the generic theorems -/

end

end

end Obs.Gen
