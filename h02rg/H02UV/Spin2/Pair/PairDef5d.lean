import Spin2.Pair.PairVStep1
import Spin2.Pair.PairShareAB1

/-!
# The `V`-bounds of the joint induction up to `N_h + 1` from the region masses

**`pairVB_top_MF`**: the `V`-step (`pairVStep_MF`) and the region masses up to `N_h + 1`
(`PairRRelRX … c_r`, an output of `pairRRelR_of_jointSizesP3_MF`) give `PairVB … m̄ (N_h + 1)`
for every `x` (induction on the scale; `PairRRelRX` is `PairMassUpTo … (N_h + 1)`).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

set_option maxHeartbeats 2000000 in
/-- **`PairVB … m̄ (N_h + 1)` from `PairRRelRX`** (see the module docstring). -/
theorem pairVB_top_MF {L : ℕ} [NeZero L] (M : MasterFacts L) :
    ∃ C₁v : ℝ, 0 ≤ C₁v ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
    ∀ m ∈ mRange L N, ∀ b μ₀,
      Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μ₀ →
    ∀ (lam : ℕ → ℂ) (cu cr mbar : ℝ), PairUnitSeed R Nh m b μ₀ lam cu → 0 < mbar → cr ≤ mbar →
      8 * (cu * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) ≤
        vck C₁v * ((4 * C₁v + 1) * mbar) →
      PairRRelRX R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) cr →
    ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh → PairVB R m b μ₀ lam x mbar (Nh + 1) := by
  obtain ⟨C₁v, hC₁v, hVS⟩ := pairVStep_MF M
  refine ⟨C₁v, hC₁v, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam cu cr mbar hU hmbar hcr h8v hRX
    x hx h1 hj
  obtain ⟨hVB0, hVs⟩ := hVS N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam cu cr mbar hU
    hmbar hcr h8v x hx h1 hj
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  have hMs : ∀ n, n ≤ Nh + 1 → PairMassUpTo R m b μ₀ lam (oRed R m b μ₀ dxStd) cr x n :=
    fun n hn M' hM1 hM2 X hX k hk1 hk2 => hRX x hx h1 hj M' hM1 (hM2.trans hn) X hX k hk1 hk2
  have key : ∀ d, j + d ≤ Nh + 1 → PairVB R m b μ₀ lam x mbar (j + d) := by
    intro d
    induction d with
    | zero => intro _; simpa using hVB0
    | succ d ih =>
      intro hd
      have h := hVs (j + d) (by omega) (by omega) (ih (by omega)) (hMs (j + d) (by omega))
      simpa [Nat.add_assoc] using h
  have := key (Nh + 1 - j) (by omega)
  rwa [show j + (Nh + 1 - j) = Nh + 1 by omega] at this

end

end Spin2
