import Spin2.Restart.RestartPairTop1
import PtCorr2.Cont.ContNa1

set_option autoImplicit false

/-!
# The one-point analogue of the `rpTopE` bound: `n_a` of the last factor of a general state

Pair `P = ptsX x` (**any** `x`, no coalescence condition), the `h = 0` trajectory, an arbitrary
observable state `o` at scale `N_h + 1` (local at `N_h + 1`), with sizes in the weights
`wM(M_a, M_b)` (`M_a = 2s_{N_h}²σ`) of `rp_top_traj`:
`‖V(B)‖ ≤ c_V`, `‖𝒲(B)‖ ≤ c_W`, `A^{(|𝓑(X)|-4)_+}‖K(X)‖_{wM1} ≤ c_K`.

* `na_wA_le` (pure): `‖F_a‖ ≤ M_a‖F‖_w` for `w_a = 1/M_a`.
* **`na_nA_lastOF_split`** (exact): `n_a(lastOF o) = −ε(u^{obs}_N(Λ))_a + n_a(ω_{cQ}F'_N)`.
* **`na_lastA_le`**: with the reference one-point items of the last step (`hone1`, `hone2`,
  `|γ_{a,N}| ≤ K₄|M_{N_h}|`, the reference zero-mode identity `n_aΩ = −γ_{a,N}` and `s_∅Ω ≠ 0`),
  the window `2·(81/16)c_J(c_ρ + 4/r₀²)c_Sℓ²·m²L^{2N} ≤ 1` (`c_S = c_V + c_W + 8c_K + 1`) and
  `2s_{N_h}²|β_{a,N_h}| ≤ c_u|M_{N_h}|ǧ`:

  `|n_a(lastOF_{N_h+1}(o))| ≤ (c_{Lab}c_Sc_u + 8(½ + (81/32)c_{Jab}c_S)K₄)·(σ/|β_{a,N_h}|)·|M_{N_h}|`,

  linear in the `a`-size `σ` of `o`. Proof: `na_eps_uXO_a_le` (constant of the last step),
  `na_finG_jets_a` (jets of `F'_N`), `rp_zero_abs` with the reference normaliser (`F'_∅ = F_∅`).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs.SA Obs.LocObs

variable {L N : ℕ} [NeZero L]

/-- `‖F_a‖ ≤ M_a·‖F‖_w` when `w_a = 1/M_a`. -/
theorem na_wA_le {c : Obs.Case} {w : Obs.Wt} {Ma : ℝ} (hMa : 0 < Ma) (hwa : w.a = ENNReal.ofReal Ma⁻¹)
    (j : ℕ) (ℓ : ℝ) (F : Obs.OE c (Lam 2 L N)) :
    Obs2.oTo Obs2.wA j ℓ F ≤ ENNReal.ofReal Ma * Obs2.oTo w j ℓ F := by
  rw [Obs2.oTo_wA]
  have h1 : w.a * Tj 2 (L : ℝ) j ℓ (F : SA c (Lam 2 L N)).a ≤ Obs2.oTo w j ℓ F := by
    refine le_trans ?_ (Obs2.oTo_one_le w j ℓ F)
    rw [Obs2.oTo_eq_comp (show (Obs2.wOne w).ab = 0 from rfl)]
    exact le_self_add
  have e : ENNReal.ofReal Ma * ENNReal.ofReal Ma⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul hMa.le, mul_inv_cancel₀ hMa.ne', ENNReal.ofReal_one]
  calc Tj 2 (L : ℝ) j ℓ (F : SA c (Lam 2 L N)).a
      = ENNReal.ofReal Ma * (w.a * Tj 2 (L : ℝ) j ℓ (F : SA c (Lam 2 L N)).a) := by
        rw [hwa, ← mul_assoc, e, one_mul]
    _ ≤ _ := mul_le_mul_right h1 _

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- **The split of `n_a` of the last factor** (exact, any observable state with `s_∅ ≠ 0` of
both factors): `n_a(lastOF j o) = −ε(u^{obs}_N(Λ))_a + n_a(zmOF j o)`. -/
theorem na_nA_lastOF_split (P : Obs2.ObsPts 2 L N) (j : ℕ) (o : Obs2.ObsSt .two L N)
    (Nh : ℕ) (t : Hist.Seq (Xs R))
    (hX : PtCorr2.sE (PtCorr2.lastCstOF R P j o Nh t) ≠ 0)
    (hΩ : PtCorr2.sE (PtCorr2.zmOF R P j o Nh t) ≠ 0) :
    PtCorr2.nA (PtCorr2.lastOF R P j o Nh t) =
      -ε (Obs2.uXO P (Nh + 1) (LastN.stCovN R (Nh + 1) (histOut R Nh t).st)
          (Obs2.fullV R (Nh + 1) (histOut R Nh t).st (histOut R Nh t).g.re (histOut R Nh t).nu.re
            (PtCorr2.obsHistFrom R P j o (Nh + 1) t))
          (Obs2.fullW (histOut R Nh t).st (histOut R Nh t).D (PtCorr2.obsHistFrom R P j o (Nh + 1) t))
          (Obs2.fullK R (Nh + 1) (histOut R Nh t).st (histOut R Nh t).K
            (PtCorr2.obsHistFrom R P j o (Nh + 1) t)) univ : SA .two (Lam 2 L N)).a +
        PtCorr2.nA (PtCorr2.zmOF R P j o Nh t) := by
  rw [PtCorr2.lastOF_eq_cst_zm R P j o Nh t, PtCorr2.nA_mul hX hΩ]
  congr 1
  have hU := PtCorr2.bulk_uXO_gen P (Nh + 1) (LastN.stCovN R (Nh + 1) (histOut R Nh t).st)
    (Obs2.fullV R (Nh + 1) (histOut R Nh t).st (histOut R Nh t).g.re (histOut R Nh t).nu.re
      (PtCorr2.obsHistFrom R P j o (Nh + 1) t))
    (Obs2.fullW (histOut R Nh t).st (histOut R Nh t).D (PtCorr2.obsHistFrom R P j o (Nh + 1) t))
    (Obs2.fullK R (Nh + 1) (histOut R Nh t).st (histOut R Nh t).K
      (PtCorr2.obsHistFrom R P j o (Nh + 1) t)) univ
  have hs := PtCorr2.na_sA_smul_expU_neg (detStep R (Nh + 1) (histOut R Nh t).st)
    (-Obs2.uXB P (Nh + 1) (LastN.stCovN R (Nh + 1) (histOut R Nh t).st)
      (Obs2.fullV R (Nh + 1) (histOut R Nh t).st (histOut R Nh t).g.re (histOut R Nh t).nu.re
        (PtCorr2.obsHistFrom R P j o (Nh + 1) t))
      (Obs2.fullW (histOut R Nh t).st (histOut R Nh t).D (PtCorr2.obsHistFrom R P j o (Nh + 1) t))
      (Obs2.fullK R (Nh + 1) (histOut R Nh t).st (histOut R Nh t).K
        (PtCorr2.obsHistFrom R P j o (Nh + 1) t)) univ) hU
  have e : PtCorr2.lastCstOF R P j o Nh t = detStep R (Nh + 1) (histOut R Nh t).st •
      Obs2.expU (-Obs2.uXB P (Nh + 1) (LastN.stCovN R (Nh + 1) (histOut R Nh t).st)
        (Obs2.fullV R (Nh + 1) (histOut R Nh t).st (histOut R Nh t).g.re (histOut R Nh t).nu.re
          (PtCorr2.obsHistFrom R P j o (Nh + 1) t))
        (Obs2.fullW (histOut R Nh t).st (histOut R Nh t).D (PtCorr2.obsHistFrom R P j o (Nh + 1) t))
        (Obs2.fullK R (Nh + 1) (histOut R Nh t).st (histOut R Nh t).K
          (PtCorr2.obsHistFrom R P j o (Nh + 1) t)) univ)
      (-Obs2.uXO P (Nh + 1) (LastN.stCovN R (Nh + 1) (histOut R Nh t).st)
        (Obs2.fullV R (Nh + 1) (histOut R Nh t).st (histOut R Nh t).g.re (histOut R Nh t).nu.re
          (PtCorr2.obsHistFrom R P j o (Nh + 1) t))
        (Obs2.fullW (histOut R Nh t).st (histOut R Nh t).D (PtCorr2.obsHistFrom R P j o (Nh + 1) t))
        (Obs2.fullK R (Nh + 1) (histOut R Nh t).st (histOut R Nh t).K
          (PtCorr2.obsHistFrom R P j o (Nh + 1) t)) univ) := rfl
  rw [← e] at hs
  unfold PtCorr2.nA
  rw [hs, mul_div_assoc, mul_comm, div_mul_cancel₀ _ hX]

end Traj

end

end Spin2
