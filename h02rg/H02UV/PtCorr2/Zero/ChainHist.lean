import PtCorr2.Zero.Chain

/-!
# The partition function along a history of the flow (`Z_{N,N}`, conditional on exactness)

Along a history `t` with `N = N_h + 2`, the steps `j ≤ N_h` are `rawStep` with inputs
`hIn R j t` (raw state `rawHist R j t`, coordinates `(t j)`), and the last step is
`rawStepN` applied to the output of step `N_h` (`lastOut`). With the one-step identities
`rawStep_omega` and `lastStep_omega` (`PtCorr2/Zero/Chain.lean`):

**`hist_omega`**: `⟨Z_0⟩_{Γ_0} = ∏_{j ≤ N_h} [det(1 + a_j A Γ_j) e^{-u_{j+1}(Λ)}] ·
det(1 + a_{N-1} A Γ_{N-1}) e^{-u_N(Λ)} (1 + ũ_{N,N})`,

under
* the step hypotheses (`ValidCore`, `RawInv`, membership of the raw `D`, `K`) and the splitting
  hypotheses `SplitOK` of the dressed decomposition at every step;
* **exactness** (`ExactStep`): the output `Z_{j+1}` of step `j` is the input of step `j + 1`
  built from the history (the flow coordinates of `t (j+1)` reproduce the complex raw output),
  and `Γ_{j+1}` computed after step `j` is the `Γ_{j+1}` of step `j + 1`;
* `V_N(B) = V_{κ_N}(B)` (from `GlueOut`).
-/

namespace PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Step2 Step Step2.LastN

variable {L N : ℕ} [NeZero L]

/-- **Exactness of one step**: the output of step `j` at `(st, g, μ, D, K)` is the input of step
`j + 1` at `(st', g', μ', D', K')`, with the same `Γ_{j+1}`. -/
def ExactStep (R : RGPar 2 L N) (j : ℕ) (st : RawSt 2 L N) (g μ : ℝ) (D : Fam 2 L N)
    (K : Act 2 L N) (st' : RawSt 2 L N) (g' μ' : ℝ) (D' : Fam 2 L N) (K' : Act 2 L N) : Prop :=
  Zout R j st g μ D K = Zin R (j + 1) st' g' μ' D' K' ∧
    (stData R j st).Gam (j + 1) = (stData R (j + 1) st').Gam (j + 1)

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- `Γ_j` at step `j` along the history. -/
def Γh (j : ℕ) (t : Hist.Seq (Xs R)) : Matrix (Lam 2 L N) (Lam 2 L N) ℂ :=
  DressedFRD.kmat ((stData R j (rawHist R j t)).Gam j)

/-- The input `Z_j` of step `j` along the history. -/
def Zh (j : ℕ) (t : Hist.Seq (Xs R)) : EvR (Lam 2 L N) :=
  Zin R j (rawHist R j t) (t j).1 (t j).2.1 (rawD R (rawHist R j t).u (t j).2.2)
    (rawK R (rawHist R j t).u (t j).2.2)

/-- The factor `det(1 + a_j A Γ_j) e^{-u_{j+1}(Λ)}` of step `j` along the history. -/
def ch (j : ℕ) (t : Hist.Seq (Xs R)) : ℂ :=
  detStep R j (rawHist R j t) *
    Complex.exp (-uOut R j (rawHist R j t) (t j).1 (t j).2.1 (rawD R (rawHist R j t).u (t j).2.2)
      (rawK R (rawHist R j t).u (t j).2.2))

/-- **The partition function along a history** (conditional on exactness and the splittings). -/
theorem hist_omega {Nh : ℕ} (hN : Nh + 2 = N) (t : Hist.Seq (Xs R))
    (hV : ∀ j ≤ Nh, ValidCore R j) (hRI : ∀ j ≤ Nh + 1, RawInv R j (rawHist R j t))
    (hD : ∀ j ≤ Nh, rawD R (rawHist R j t).u (t j).2.2 ∈ BSub (L := L) (N := N) j)
    (hK : ∀ j ≤ Nh, rawK R (rawHist R j t).u (t j).2.2 ∈ ASub (L := L) (N := N) j)
    (hS : ∀ j ≤ Nh + 1, SplitOK R j (rawHist R j t))
    (hEx : ∀ j < Nh, ExactStep R j (rawHist R j t) (t j).1 (t j).2.1
      (rawD R (rawHist R j t).u (t j).2.2) (rawK R (rawHist R j t).u (t j).2.2)
      (rawHist R (j + 1) t) (t (j + 1)).1 (t (j + 1)).2.1
      (rawD R (rawHist R (j + 1) t).u (t (j + 1)).2.2) (rawK R (rawHist R (j + 1) t).u (t (j + 1)).2.2))
    (hExL : ExactStep R Nh (rawHist R Nh t) (t Nh).1 (t Nh).2.1
      (rawD R (rawHist R Nh t).u (t Nh).2.2) (rawK R (rawHist R Nh t).u (t Nh).2.2)
      (histOut R Nh t).st (histOut R Nh t).g.re (histOut R Nh t).nu.re (histOut R Nh t).D
      (histOut R Nh t).K)
    (hVL : ∀ b ∈ blockIdx (L := L) (N := N) (Nh + 1),
      ((lastOut R Nh t).V b : Alg 2 L N) = Vcoup (lastOut R Nh t).κ (blockSet (Nh + 1) b)) :
    omegaC (Γh R 0 t) (Zh R 0 t : Alg 2 L N) =
      (∏ j ∈ range (Nh + 1), ch R j t) *
        (detStep R (Nh + 1) (histOut R Nh t).st * Complex.exp (-(lastOut R Nh t).u) *
          (1 + uFin (Nh + 1) (lastOut R Nh t) (zmRaw R (Nh + 1) (lastOut R Nh t).ζ))) := by
  have hstep : ∀ j ≤ Nh, omegaC (Γh R j t) (Zh R j t : Alg 2 L N) =
      ch R j t * omegaC (DressedFRD.kmat ((stData R j (rawHist R j t)).Gam (j + 1)))
        (Zout R j (rawHist R j t) (t j).1 (t j).2.1 (rawD R (rawHist R j t).u (t j).2.2)
          (rawK R (rawHist R j t).u (t j).2.2) : Alg 2 L N) := fun j hj =>
    rawStep_omega (hV j hj) (hRI j (by omega)) (hD j hj) (hK j hj) (hS j (by omega))
  have h1 := chain_omega (Γ := fun j => Γh R j t) (Zs := fun j => Zh R j t) (c := fun j => ch R j t)
    Nh fun i hi => by
      show omegaC (Γh R i t) (Zh R i t : Alg 2 L N) =
        ch R i t * omegaC (Γh R (i + 1) t) (Zh R (i + 1) t : Alg 2 L N)
      rw [hstep i hi.le, (hEx i hi).1, (hEx i hi).2]
      rfl
  have h2 := hstep Nh le_rfl
  rw [hExL.1, hExL.2] at h2
  have h3 := lastStep_omega (R := R) (j := Nh + 1) (st := (histOut R Nh t).st)
    (g := (histOut R Nh t).g.re) (μ := (histOut R Nh t).nu.re) (D := (histOut R Nh t).D)
    (K := (histOut R Nh t).K) (by omega) (hRI (Nh + 1) le_rfl) (hS (Nh + 1) le_rfl) hVL
  rw [h1, h2, h3, prod_range_succ]
  simp only [lastOut]
  ring

end

end PtCorr2
