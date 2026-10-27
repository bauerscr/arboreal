import Spin2.Gam.GamBulk
import Spin2.Gam.GamFormB
import PtCorr2.Restart.RestartPairGamB
import PtCorr2.Restart.RestartPairAB
import Spin2.Case2.Case2Top
import Spin2.Master.MasterAllFactsD
import Spin2.Case2.Case2Thm
import PtCorr2.Restart.RestartPairTopF1

-- Merged from `Spin2/RestartPairGamC.lean` (phase 3).
section

/-!
# T5: the bulk factor of the restarted `γ`-flow along a trajectory

`rpgC k = C_k(a,a) − ε(F_{C_k}(ψ̄_aψ_a, V'_k(Λ)_∅))` (`PtCorr2.rpgC`) along
`t = traj (rgDataM R m) (L²) b μ₀`:

* `rpg_C_eq`: `rpgC k = Γ^{int}_{k+1}(0,0) − gamBulkA R m b μ₀ P.a k` (`k < N_h`; translation
  invariance of the diagonal, `bulk2_hist`, `ε(F_C(ψ̄_aψ_a, 1)) = 0`).
* **`rpg_C_le`**: `GamBulkRelA R N_h m b μ₀ c_e ⇒ |rpgC k| ≤ (1 + c_e(ǧ_k + zA_k))|Γ^{int}_{k+1}(0,0)|`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs.SA Obs.LocObs

variable {L N : ℕ} [NeZero L]

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

theorem rpg_C_eq (hP : R.P = Pc) {Nh : ℕ} {m b μ₀ : ℝ}
    (hV : ∀ i < Nh, ValidAt (R.withMsq m) i) (P : Obs2.ObsPts 2 L N) (o₀ : Obs2.ObsSt .two L N)
    (ho₀ : o₀.IsObs) {k : ℕ} (hk : k < Nh) :
    rpgC (R.withMsq m) P (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) o₀ k =
      gamT R m b μ₀ k - gamBulkA R m b μ₀ P.a k := by
  unfold rpgC gamBulkA gamT
  rw [histCov_gamInt_at R hP]
  obtain ⟨r, hr⟩ := (Obs2.bulk2_hist (R.withMsq m) P o₀ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
    hV ho₀).he k hk
  rw [hr, FC_add_right, FC_smul_right, Obs2.FC_one_right, smul_zero, add_zero]

/-- **The bulk factor of the restarted `γ`-flow**: `|rpgC k| ≤ (1 + c_e(ǧ_k + zA_k))|Γ_{k+1}|`. -/
theorem rpg_C_le (hP : R.P = Pc) {Nh : ℕ} {m b μ₀ ce : ℝ}
    (hV : ∀ i < Nh, ValidAt (R.withMsq m) i) (hGB : GamBulkRelA R Nh m b μ₀ ce)
    (P : Obs2.ObsPts 2 L N) (o₀ : Obs2.ObsSt .two L N) (ho₀ : o₀.IsObs) {k : ℕ} (hk : k < Nh) :
    ‖rpgC (R.withMsq m) P (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) o₀ k‖ ≤
      (1 + ce * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k)) *
        ‖gamT R m b μ₀ k‖ := by
  rw [rpg_C_eq R hP hV P o₀ ho₀ hk]
  refine (norm_sub_le _ _).trans ?_
  have := hGB P.a k hk
  linarith
end Traj

end

end Spin2

end

/-!
# T5 (item 4′): the bulk factor of the restarted `γ`-flow at the top step `k = N_h`

`rpgC k = C_k(a,a) − ε(F_{C_k}(ψ̄_aψ_a, V'_k(Λ)_∅))` (`PtCorr2.rpgC`) along
`t = traj (rgDataM R m) (L²) b μ₀`:

* `rptf_C_eq_top`: `rpgC N_h = Γ^{int}_{N_h+1}(0,0) − gamBulkA R m b μ₀ P.a N_h` (`bulk2_histU`,
  `ValidAtL` at `N_h`);
* **`rptf_C_top_le`** (bulk context `C2Ctx`, `gamBulk_le_posU`):
  `|rpgC N_h| ≤ |Γ^{int}_{N_h+1}(0,0)| + K_bǧ_{N_h}/|Z_{N_h+1}|`;
* **`MasterFacts.rptf_C_topD`**: the same along every `D_ε` trajectory under the master constants
  (`c2ctx_master`; `K_b = gbKb L ℓ c_μ c_Z`);
* `rptfGam`, **`rptf_gam_top`**: `|ε(u^F_{N_h+1,a})| ≤ rptfGam` (the exact sum of `rpg_gam_le`
  from `ms` to `N_h`), and **`MasterFacts.rptf_gam_sizes`**: `rptfGam` bounded by the restart sizes
  `‖β^F_k‖ ≤ B_k`, `|gamWKF k| ≤ G_k` and the bulk factors (`GamBulkRelA` for `k < N_h`,
  `rptf_C_topD` at `k = N_h`).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs.SA Obs.LocObs

variable {L N : ℕ} [NeZero L]

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

theorem rptf_C_eq_top (hP : R.P = Pc) {Nh : ℕ} {m b μ₀ : ℝ}
    (hV : ∀ i < Nh, ValidAt (R.withMsq m) i) (hVL : ValidAtL (R.withMsq m) Nh)
    (P : Obs2.ObsPts 2 L N) (o₀ : Obs2.ObsSt .two L N) (ho₀ : o₀.IsObs) :
    rpgC (R.withMsq m) P (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) o₀ Nh =
      gamT R m b μ₀ Nh - gamBulkA R m b μ₀ P.a Nh := by
  unfold rpgC gamBulkA gamT
  rw [histCov_gamInt_at R hP]
  obtain ⟨r, hr⟩ := (bulk2_histU (R.withMsq m) P o₀ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
    hV hVL ho₀).he Nh (Nat.lt_succ_self Nh)
  rw [hr, FC_add_right, FC_smul_right, Obs2.FC_one_right, smul_zero, add_zero]

/-- **The bulk factor at the top step** (bulk context). -/
theorem rptf_C_top_le (hP : R.P = Pc) {Nh : ℕ} {m b μ₀ cmu' cz' cd c : ℝ}
    (X : C2Ctx (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) cmu' cz' cd c)
    (hzy : ‖(rawHist (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).z +
        (rawHist (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).y‖ ≤
      2 * cz' * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 *
        zH (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) Nh)
    (P : Obs2.ObsPts 2 L N) (o₀ : Obs2.ObsSt .two L N) (ho₀ : o₀.IsObs) :
    ‖rpgC (R.withMsq m) P (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) o₀ Nh‖ ≤
      ‖gamT R m b μ₀ Nh‖ + gbKb L (R.withMsq m).ℓ cmu' cz' *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 /
          zH (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Nh + 1) := by
  rw [rptf_C_eq_top R hP X.hV X.hVL P o₀ ho₀]
  refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
  exact X.gamBulk_le_posU (le_refl Nh) hzy P.a

end Traj

/-! ### The accumulated `a`-constant at `N_h + 1` -/

section Gam

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : Obs2.ObsPts 2 L N) (ms : ℕ)
  (o' : Obs2.ObsSt .two L N) (t : Hist.Seq (Xs R)) (o₀ : Obs2.ObsSt .two L N) (Nh : ℕ)

/-- The exact sum of `rpg_gam_le` from `ms` to `N_h` (the bound `γ_δ` of `rp_top_traj`). -/
def rptfGam : ℝ :=
  ‖gamF R P ms o' t ms‖ + ‖epsTotF R P ms o' t ms‖ +
    ∑ i ∈ range (Nh + 1 - ms), (‖Obs2.betaTot2 (ms + i) (histVF2 R P ms o' t (ms + i))‖ *
      ‖rpgC R P t o₀ (ms + i)‖ + ‖gamWKF R P ms o' t (ms + i)‖)

/-- **The accumulated `a`-constant of the restarted state at `N_h + 1`.** -/
theorem rptf_gam_top (h0 : o'.IsObs) (hf0 : ∀ b, Obs2.Loc2Form P.a (o'.V b : SA .two (Lam 2 L N)).a)
    (ho₀ : o₀.IsObs) (hms : ms ≤ Nh) :
    ‖ε ((obsHistFrom R P ms o' (Nh + 1) t).u : SA .two (Lam 2 L N)).a‖ ≤
      rptfGam R P ms o' t o₀ Nh := by
  have h := rpg_gam_le R P ms o' t h0 hf0 o₀ ho₀ (Nh + 1 - ms)
  rw [show ms + (Nh + 1 - ms) = Nh + 1 by omega, if_neg (by omega)] at h
  unfold gamF at h
  rw [norm_neg] at h
  exact h

end Gam

/-! ### Under the master constants -/

namespace MasterFacts

variable {L : ℕ} [NeZero L] (M : MasterFacts L)

set_option maxHeartbeats 4000000 in
/-- **The bulk factor at the top step along a `D_ε` trajectory** (master constants). -/
theorem rptf_C_topD {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) {b μ₀ : ℝ}
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    (P : Obs2.ObsPts 2 L N) (o₀ : Obs2.ObsSt .two L N) (ho₀ : o₀.IsObs) :
    ‖rpgC (R.withMsq m) P (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) o₀ Nh‖ ≤
      ‖gamT R m b μ₀ Nh‖ + gbKb L (R.withMsq m).ℓ (cmu ((L : ℝ) ^ 2) M.core.cm)
        (cZ (R.withMsq m)) * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 /
          zH (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Nh + 1) := by
  have hL49 : 49 ≤ L := M.core.hL49
  have hF := M.flow
  set R' := R.withMsq m with hR'
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  have hval : ∀ j < Nh, ValidAt R' j := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrest⟩ := hF
    exact ((hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm).1
  have hvalL : ValidAtL R' Nh := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrest⟩ := hF
    exact ((hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm).2
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8, -, -⟩ := hF
  have hρ0' : 0 ≤ R'.ρ := by rw [show R'.ρ = M.core.ρ from hRρ]; exact hρpos.le
  have hρ8' : R'.ρ ≤ 1 / 8 := by rw [show R'.ρ = M.core.ρ from hRρ]; exact hρ8
  obtain ⟨H, hm1, F1⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm
  have ht := inDh_rg_of_D R' F1 hD Nh le_rfl
  have hSB' : StepBounds L R'.A M.core.C₀x M.core.ηx M.core.εsx M.core.CKx M.core.C₂x M.core.CDx
      M.core.Cqx M.core.Clx M.core.cSx := by
    rw [show R'.A = M.core.A from hRA]; exact M.core.hSBx
  have X := c2ctx_master R' hNh hL49 hSB' H hm1 hval hvalL hρ0' hρ8' hm M.core.hβε ht
  have hβ2 := betaL_ge (by omega : 8 ≤ L)
  have hβ0 : 0 ≤ betaL L := by linarith
  have hzy : ‖(rawHist R' Nh t).z + (rawHist R' Nh t).y‖ ≤
      2 * cZ R' * (t Nh).1 * zH R' t Nh := by
    obtain ⟨hz, hy, -⟩ := apriori R' hSB' hval hm1 hβ0 (by norm_num) H Nh le_rfl t ht
    have hZ := zH_pos R' hρ0' hρ8' t Nh
    have hZne : (rawHist R' Nh t).Z ≠ 0 := norm_pos_iff.1 hZ
    have e : (rawHist R' Nh t).z + (rawHist R' Nh t).y =
        (rawHist R' Nh t).Z * ((rawHist R' Nh t).z / (rawHist R' Nh t).Z +
          (rawHist R' Nh t).y / (rawHist R' Nh t).Z) := by field_simp
    rw [e, norm_mul]
    have := (norm_add_le _ _).trans (add_le_add hz hy)
    have e2 : 2 * cZ R' * (t Nh).1 * zH R' t Nh =
        zH R' t Nh * (cZ R' * (t Nh).1 + cZ R' * (t Nh).1) := by ring
    rw [e2]
    exact mul_le_mul_of_nonneg_left this hZ.le
  exact rptf_C_top_le R hP X hzy P o₀ ho₀

set_option maxHeartbeats 2000000 in
/-- **`rptfGam` from the restart sizes**: with `‖β^F_k‖ ≤ B_k`, `|gamWKF k| ≤ G_k`
(`ms ≤ k ≤ N_h`), the bulk factors at `k < N_h` (`GamBulkRelA`, constant `c_e = M.core.cGB`) and
at `k = N_h` (`rptf_C_topD`). -/
theorem rptf_gam_sizes {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) {b μ₀ : ℝ}
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    (P : Obs2.ObsPts 2 L N) (o₀ : Obs2.ObsSt .two L N) (ho₀ : o₀.IsObs)
    {ms : ℕ} (hms : ms ≤ Nh) (o' : Obs2.ObsSt .two L N) (Bβ Gw : ℕ → ℝ)
    (hB : ∀ k, ms ≤ k → k ≤ Nh → ‖Obs2.betaTot2 (L := L) (N := N) k
      (histVF2 (R.withMsq m) P ms o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)‖ ≤ Bβ k)
    (hG : ∀ k, ms ≤ k → k ≤ Nh →
      ‖gamWKF (R.withMsq m) P ms o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k‖ ≤ Gw k) :
    rptfGam (R.withMsq m) P ms o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) o₀ Nh ≤
      ‖gamF (R.withMsq m) P ms o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ms‖ +
        ‖epsTotF (R.withMsq m) P ms o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ms‖ +
        ∑ i ∈ range (Nh - ms), (Bβ (ms + i) * ((1 + M.core.cGB *
            ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (ms + i)).1 + zA L m (ms + i))) *
              ‖gamT R m b μ₀ (ms + i)‖) + Gw (ms + i)) +
        (Bβ Nh * (‖gamT R m b μ₀ Nh‖ + gbKb L (R.withMsq m).ℓ (cmu ((L : ℝ) ^ 2) M.core.cm)
          (cZ (R.withMsq m)) * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 /
            zH (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Nh + 1)) + Gw Nh) := by
  have hF := M.flow
  have hval : ∀ j < Nh, ValidAt (R.withMsq m) j := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrest⟩ := hF
    exact ((hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm).1
  have hGB := M.gamBulkD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD
  have hCt := M.rptf_C_topD R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD P o₀ ho₀
  unfold rptfGam
  rw [show Nh + 1 - ms = (Nh - ms) + 1 by omega, sum_range_succ,
    show ms + (Nh - ms) = Nh by omega]
  have hsum : ∀ i ∈ range (Nh - ms),
      ‖Obs2.betaTot2 (L := L) (N := N) (ms + i)
          (histVF2 (R.withMsq m) P ms o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (ms + i))‖ *
        ‖rpgC (R.withMsq m) P (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) o₀ (ms + i)‖ +
      ‖gamWKF (R.withMsq m) P ms o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (ms + i)‖ ≤
      Bβ (ms + i) * ((1 + M.core.cGB *
            ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (ms + i)).1 + zA L m (ms + i))) *
              ‖gamT R m b μ₀ (ms + i)‖) + Gw (ms + i) := by
    intro i hi
    have hi' := mem_range.1 hi
    have hC := rpg_C_le R hP hval hGB P o₀ ho₀ (k := ms + i) (by omega)
    have hb := hB (ms + i) (by omega) (by omega)
    refine add_le_add (mul_le_mul hb hC (norm_nonneg _) ((norm_nonneg _).trans hb))
      (hG (ms + i) (by omega) (by omega))
  have htop := add_le_add (mul_le_mul (hB Nh hms le_rfl) hCt (norm_nonneg _)
    ((norm_nonneg _).trans (hB Nh hms le_rfl))) (hG Nh hms le_rfl)
  have := sum_le_sum hsum
  linarith

end MasterFacts

end

end Spin2
