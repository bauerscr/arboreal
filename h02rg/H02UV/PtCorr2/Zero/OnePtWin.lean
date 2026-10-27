import PtCorr2.Pair.TwoPtZZ
import PtCorr2.Pair.PairReduce
import PtCorr2.Zero.WardNeg1

/-!
# The one-point function on windowed trajectories (route (a1), input (i))

Model part and exact RG part, at either sign of `h`:

* **`onept_real_of_re`**: `⟨Z_0⟩ ≠ 0`, `Re r ≥ 0` and `Re χ > 0` (`r = 1 − b⟨ψ̄_0ψ_0⟩`,
  `χ = ∑_x⟨ψ̄_0ψ_x⟩`) give `h ≥ 0` and `r` real `≥ 0`. The Ward identity `h'χ = r` (`h'` real)
  gives `h' Re χ = Re r ≥ 0`, hence `h' ≥ 0`, and positivity at `h ≥ 0` makes `r` real
  (`onept_avg0_mem`). So the RG never has to show that `r` is real: a lower bound on `Re r` is
  enough.
* **`onept_rg_ratioZ`**: the one-point part of `zz_rg_ratio` with `⟨Z_0⟩ ≠ 0` as hypothesis in
  place of `h ≥ 0`: `sE Π = ⟨Z_0⟩_{Γ_0}` and `⟨z_a⟩ = sA Π/sE Π` (`Π = rgProdO`).
* **`sE_rgProdO_eq`**: `sE Π = (∏_{j ≤ N_h} c_j)·(det_{N−1}·e^{−u^{obs,∅}_N(Λ)}·sE Ω)`, with
  `Ω = ω_{cQ}(F_N)` the zero-mode integral of the observable last step and `u^{obs,∅}_N = uXB` its
  bulk constant: the bulk normalisations of the observable chain are the `c_j` of the bulk chain.
-/

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD Obs2 Flow2 Flow2.Hist

variable {L N : ℕ} [NeZero L]

/-- **`r` real `≥ 0` from `Re r ≥ 0`** (any sign of `h`, given `⟨Z_0⟩ ≠ 0` and `Re χ > 0`). -/
theorem onept_real_of_re {b μ₀ msq : ℝ} (hb : 0 < b) (hm0 : 0 < msq)
    (hZ : Obs.Zb (Suscept.Cov 2 L N msq) (VE (V0c b μ₀) (univ : Finset (Lam 2 L N))) ≠ 0)
    (hr : 0 ≤ (1 - (b : ℂ) * avg0 L N msq b μ₀ (psibar 0 * psi 0)).re)
    (hχ : 0 < (∑ x : Lam 2 L N, avg0 L N msq b μ₀ (psibar 0 * psi x)).re) :
    b ≤ μ₀ + msq ∧ ∃ r : ℝ, 0 ≤ r ∧ 1 - (b : ℂ) * avg0 L N msq b μ₀ (psibar 0 * psi 0) = r := by
  have hw := ward_V0 (L := L) (N := N) hb hm0 hZ
  have h1 := congrArg Complex.re hw
  rw [Complex.re_ofReal_mul] at h1
  have hh : b ≤ μ₀ + msq := by
    by_contra hc
    push Not at hc
    have : (μ₀ + msq - b) * (∑ x : Lam 2 L N, avg0 L N msq b μ₀ (psibar 0 * psi x)).re < 0 :=
      mul_neg_of_neg_of_pos (by linarith) hχ
    linarith
  obtain ⟨r, hr0, -, hre⟩ := onept_avg0_mem (L := L) (N := N) hb hm0 hh
  exact ⟨hh, r, hr0, hre⟩

section Hist

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N)

set_option maxHeartbeats 1000000 in
/-- **The one-point function as a ratio of components of the RG product, at any sign of `h`**
(`zz_rg_ratio` with `⟨Z_0⟩ ≠ 0` in place of `b ≤ μ₀ + m²`). -/
theorem onept_rg_ratioZ {Nh : ℕ} (hN : Nh + 2 = N) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < R.msq)
    (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt R j)
    (hVL : ValidAtL R Nh) (hL7 : 7 ≤ L) (b μ₀ : ℝ) (V : OCoup2) :
    let Pr := rgProdO R P (obsInit .two V P) Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)
    sE Pr = omegaC (Γh R 0 (traj (rgData R) ((L : ℝ) ^ 2) b μ₀))
        (Zh R 0 (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) : Alg 2 L N) ∧
      (sE Pr ≠ 0 → avg0 L N R.msq b μ₀ (zObsA V P) = sA Pr / sE Pr) := by
  dsimp only
  set t := traj (rgData R) ((L : ℝ) ^ 2) b μ₀ with htd
  set Pr := rgProdO R P (obsInit .two V P) Nh t with hPr
  have ht : t 0 = (b, μ₀, 0) := Hist.traj_zero _ _
  have h := hist_omegaO_traj_loc R P (obsInit .two V P) hN hρ1 hspl hm0 hm hV hVL b μ₀
    (obsInit_isObs .two V P) (obsLocInv_init .two V P)
  rw [← htd, ← hPr] at h
  set Γ := Γh R 0 t
  have ke : sE Pr = omegaC Γ (Zh R 0 t : Alg 2 L N) := by
    rw [sE, ← h, omegaCO_ZhO_zero_e R P .two V t ht Γ]; exact ε.commutes _
  have ka : sA Pr = omegaC Γ ((Zh R 0 t : Alg 2 L N) * zObsA V P) := by
    rw [sA, ← h, omegaCO_ZhO_zero_two R P V t ht Γ]; exact ε.commutes _
  have hA := fun F => avg0_eq_omega_traj R hL7 hm0 (by omega) t ht F
  refine ⟨ke, fun _ => ?_⟩
  rw [hA, ka, ke]

/-- `sE chO_j = c_j`: the bulk normalisation of a step with sources is the bulk step constant. -/
theorem sE_chO (o₀ : ObsSt .two L N) (j : ℕ) (t : Hist.Seq (Xs R)) :
    sE (chO R P o₀ j t) = ch R j t := by
  unfold chO uOutO ch
  rw [sE_smul_expU]
  rw [map_neg, bulk_uObsTot, neg_zero]

/-- **The bulk normalisation of the RG product** (any history): `sE Π = (∏_{j≤N_h} c_j)·
(det_{N−1}·e^{−uXB}·sE Ω)`, `Ω` the zero-mode integral of the observable last step. -/
theorem sE_rgProdO_eq (o₀ : ObsSt .two L N) (Nh : ℕ) (t : Hist.Seq (Xs R)) :
    sE (rgProdO R P o₀ Nh t) = (∏ j ∈ range (Nh + 1), ch R j t) *
      (detStep R (Nh + 1) (histOut R Nh t).st *
        (Complex.exp (-uXB P (Nh + 1) (LastN.stCovN R (Nh + 1) (histOut R Nh t).st)
          (fullV R (Nh + 1) (histOut R Nh t).st (histOut R Nh t).g.re (histOut R Nh t).nu.re
            (obsHist R P o₀ (Nh + 1) t))
          (fullW (histOut R Nh t).st (histOut R Nh t).D (obsHist R P o₀ (Nh + 1) t))
          (fullK R (Nh + 1) (histOut R Nh t).st (histOut R Nh t).K (obsHist R P o₀ (Nh + 1) t))
          univ) *
        sE (omegaCO (cstC (Lam 2 L N) (zmRaw R (Nh + 1) (Function.update (histOut R Nh t).st.ζ
          (Nh + 1) (stZeta R (histOut R Nh t).st)) / Fintype.card (Lam 2 L N)))
          (finO R P (Nh + 1) (histOut R Nh t).st (histOut R Nh t).g.re (histOut R Nh t).nu.re
            (histOut R Nh t).D (histOut R Nh t).K (obsHist R P o₀ (Nh + 1) t))))) := by
  unfold rgProdO
  rw [sE_mul, sE_prod]
  congr 1
  · exact prod_congr rfl fun j _ => sE_chO R P o₀ j t
  · rw [show ∀ (r : ℂ) (F G : OE .two (Lam 2 L N)), sE (r • (F * G)) = r * (sE F * sE G) from
      fun r F G => by rw [← sE_mul]; simp only [sE, SetLike.val_smul, SA.smul_e, map_smul,
        smul_eq_mul]]
    congr 2
    unfold uOutNO
    have h := sE_smul_expU (Λ := Lam 2 L N) 1 (-uXB P (Nh + 1)
      (LastN.stCovN R (Nh + 1) (histOut R Nh t).st)
      (fullV R (Nh + 1) (histOut R Nh t).st (histOut R Nh t).g.re (histOut R Nh t).nu.re
        (obsHist R P o₀ (Nh + 1) t))
      (fullW (histOut R Nh t).st (histOut R Nh t).D (obsHist R P o₀ (Nh + 1) t))
      (fullK R (Nh + 1) (histOut R Nh t).st (histOut R Nh t).K (obsHist R P o₀ (Nh + 1) t)) univ)
      (F := -uXO P (Nh + 1) (LastN.stCovN R (Nh + 1) (histOut R Nh t).st)
      (fullV R (Nh + 1) (histOut R Nh t).st (histOut R Nh t).g.re (histOut R Nh t).nu.re
        (obsHist R P o₀ (Nh + 1) t))
      (fullW (histOut R Nh t).st (histOut R Nh t).D (obsHist R P o₀ (Nh + 1) t))
      (fullK R (Nh + 1) (histOut R Nh t).st (histOut R Nh t).K (obsHist R P o₀ (Nh + 1) t)) univ)
      (by rw [map_neg, bulk_uXO_gen, neg_zero])
    rw [one_smul, one_mul] at h
    exact h

end Hist

end

end PtCorr2
