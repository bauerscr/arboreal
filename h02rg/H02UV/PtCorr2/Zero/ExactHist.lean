import PtCorr2.Zero.ExactStep

/-!
# Reality and exactness along the trajectories of the flow

For a trajectory `t = traj (rgData R) L² b μ₀` (real initial data, `0 ≤ ρ < 1`):

* `traj_real`: every raw state `rawHist R j t` is real and the raw `(D_j, K_j)` rebuilt from
  `t j` are conjugation-invariant (no validity needed: `T_j` is either `σ_{u^{-1}}(D, K)` of a
  real output or `0`);
* `traj_exact`: for `j` with `ValidAt R i` for all `i ≤ j` and `ValidAtL R j`, the step `j` is
  exact (`ExactStep`): the coordinates `t (j+1) = (Re ǧ_{j+1}, Re ν_{j+1}, σ_{u^{-1}}(D, K)_{j+1})`
  rebuild the output exactly;
* `traj_exactL`: the step `N_h` (under `ValidAtL`) is exact with respect to the inputs of the last
  step (`lastOut`).
-/

namespace PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Step2 Step

local notation "cj" => starRingEnd ℂ

variable {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

theorem realSt_zero (t : Hist.Seq (Xs R)) : RealSt (rawHist R 0 t) :=
  ⟨by simp [rawHist], by simp [rawHist], by simp [rawHist], fun _ => by simp [rawHist],
    by simp [rawHist], by simp [rawHist], by funext b; simp [rawHist, conjF]⟩

theorem conjF_rawD {u : ℂ} (hu : cj u = u) {j : ℕ} (x : Xs R j)
    (hx : conjF (x.1.toFam) = x.1.toFam) : conjF (rawD R u x) = rawD R u x := by
  unfold rawD; rw [conjF_sigF hu, hx]

theorem conjA_rawK {u : ℂ} (hu : cj u = u) {j : ℕ} (x : Xs R j)
    (hx : conjA (x.2.toAct) = x.2.toAct) : conjA (rawK R u x) = rawK R u x := by
  unfold rawK; rw [conjA_sigK hu, hx]

/-- The coordinates `x_j` of a trajectory are conjugation-invariant, and the raw states real. -/
theorem traj_real (hρ0 : 0 ≤ R.ρ) (hρ1 : R.ρ < 1) (Λ b μ₀ : ℝ) :
    ∀ j, RealSt (rawHist R j (traj (rgData R) Λ b μ₀)) ∧
      conjF ((traj (rgData R) Λ b μ₀ j).2.2.1.toFam) = (traj (rgData R) Λ b μ₀ j).2.2.1.toFam ∧
      conjA ((traj (rgData R) Λ b μ₀ j).2.2.2.toAct) = (traj (rgData R) Λ b μ₀ j).2.2.2.toAct
  | 0 => ⟨realSt_zero R _, by funext b; simp [Hist.traj_zero, conjF], by funext X; simp [Hist.traj_zero]⟩
  | j + 1 => by
    set t := traj (rgData R) Λ b μ₀
    obtain ⟨H, hx1, hx2⟩ := traj_real hρ0 hρ1 Λ b μ₀ j
    have hD := conjF_rawD R H.u (t j).2.2 hx1
    have hK := conjA_rawK R H.u (t j).2.2 hx2
    obtain ⟨H', hD', hK', -, -⟩ := rawStep_real R j H (t j).1 (t j).2.1 hD hK hρ0 hρ1
    have hu' : cj (histOut R j t).st.u⁻¹ = (histOut R j t).st.u⁻¹ := by rw [map_inv₀]; exact congrArg _ H'.u
    have ht : t (j + 1) = Hist.stepS (rgData R) Λ j t := traj_succ_rg R Λ b μ₀ j
    refine ⟨H', ?_, ?_⟩
    · rw [ht]
      simp only [Hist.stepS, rgData, Tmap]
      split_ifs
      · show conjF (sigF (histOut R j t).st.u⁻¹ (histOut R j t).D) =
          sigF (histOut R j t).st.u⁻¹ (histOut R j t).D
        rw [conjF_sigF hu']; exact congrArg _ hD'
      · funext c; simp [conjF, BSp.toFam]
    · rw [ht]
      simp only [Hist.stepS, rgData, Tmap]
      split_ifs
      · show conjA (sigK (histOut R j t).st.u⁻¹ (histOut R j t).K) =
          sigK (histOut R j t).st.u⁻¹ (histOut R j t).K
        rw [conjA_sigK hu']; exact congrArg _ hK'
      · funext X; simp [ASp.toAct]

/-- The reality of the output couplings along a trajectory. -/
theorem traj_out_real (hρ0 : 0 ≤ R.ρ) (hρ1 : R.ρ < 1) (Λ b μ₀ : ℝ) (j : ℕ) :
    cj (histOut R j (traj (rgData R) Λ b μ₀)).nu = (histOut R j (traj (rgData R) Λ b μ₀)).nu ∧
      cj (histOut R j (traj (rgData R) Λ b μ₀)).g = (histOut R j (traj (rgData R) Λ b μ₀)).g := by
  set t := traj (rgData R) Λ b μ₀
  obtain ⟨H, hx1, hx2⟩ := traj_real R hρ0 hρ1 Λ b μ₀ j
  obtain ⟨-, -, -, hnu, hg⟩ := rawStep_real R j H (t j).1 (t j).2.1
    (conjF_rawD R H.u (t j).2.2 hx1) (conjA_rawK R H.u (t j).2.2 hx2) hρ0 hρ1
  exact ⟨hnu, hg⟩

/-- **Exactness of the step `j` along a trajectory** (`ValidAt` up to `j`). -/
theorem traj_exact (hρ1 : R.ρ < 1) (hLg : 2 ^ (2 + 4) + 4 < L) (b μ₀ : ℝ) {j : ℕ}
    (hV : ∀ i ≤ j, ValidAt R i) :
    let t := traj (rgData R) ((L : ℝ) ^ 2) b μ₀
    ExactStep R j (rawHist R j t) (t j).1 (t j).2.1 (rawD R (rawHist R j t).u (t j).2.2)
      (rawK R (rawHist R j t).u (t j).2.2) (rawHist R (j + 1) t) (t (j + 1)).1 (t (j + 1)).2.1
      (rawD R (rawHist R (j + 1) t).u (t (j + 1)).2.2)
      (rawK R (rawHist R (j + 1) t).u (t (j + 1)).2.2) := by
  intro t
  have hρ0 : 0 ≤ R.ρ := (hV j le_rfl).2.2.2.1
  have HI := rawInv_hist R hρ0 j (fun i hi => hV i hi.le) t
  have HI' := rawInv_hist R hρ0 (j + 1) (fun i hi => hV i (by omega)) t
  obtain ⟨hnu, hg⟩ := traj_out_real R hρ0 hρ1 ((L : ℝ) ^ 2) b μ₀ j
  have hE := exactStep_of R ((hV j le_rfl).toValidAtL hLg) HI (rawD_mem R _ _) (rawK_mem R _ _)
    hρ1 hnu hg
  have ht : t (j + 1) = Hist.stepS (rgData R) ((L : ℝ) ^ 2) j t := traj_succ_rg R _ b μ₀ j
  have hu0 : (rawHist R (j + 1) t).u ≠ 0 := by
    intro h
    have := HI'.hu
    rw [h, zero_pow two_ne_zero] at this
    exact HI'.Z_ne_zero hρ1 this.symm
  have e1 : (t (j + 1)).1 = (histOut R j t).g.re := by rw [ht]; rfl
  have e2 : (t (j + 1)).2.1 = (histOut R j t).nu.re := by
    rw [ht]; simp only [Hist.stepS, rgData]; ring
  have e3 : rawD R (rawHist R (j + 1) t).u (t (j + 1)).2.2 = (histOut R j t).D := by
    rw [ht]
    show rawD R (rawHist R (j + 1) t).u (Tmap R j t) = _
    unfold Tmap; rw [dif_pos hV]
    show sigF (rawHist R (j + 1) t).u (sigF (histOut R j t).st.u⁻¹ (histOut R j t).D) = _
    rw [sigF_sigF, show (rawHist R (j + 1) t).u * (histOut R j t).st.u⁻¹ = 1 from
      mul_inv_cancel₀ hu0, sigF_one]
  have e4 : rawK R (rawHist R (j + 1) t).u (t (j + 1)).2.2 = (histOut R j t).K := by
    rw [ht]
    show rawK R (rawHist R (j + 1) t).u (Tmap R j t) = _
    unfold Tmap; rw [dif_pos hV]
    show sigK (rawHist R (j + 1) t).u (sigK (histOut R j t).st.u⁻¹ (histOut R j t).K) = _
    rw [sigK_sigK, show (rawHist R (j + 1) t).u * (histOut R j t).st.u⁻¹ = 1 from
      mul_inv_cancel₀ hu0, sigK_one]
  rw [e1, e2, e3, e4]
  exact hE

/-- **Exactness of the step `N_h`** (under `ValidAtL`) with respect to the last step. -/
theorem traj_exactL (hρ1 : R.ρ < 1) (b μ₀ : ℝ) {Nh : ℕ} (hV : ∀ i < Nh, ValidAt R i)
    (hVL : ValidAtL R Nh) :
    let t := traj (rgData R) ((L : ℝ) ^ 2) b μ₀
    ExactStep R Nh (rawHist R Nh t) (t Nh).1 (t Nh).2.1 (rawD R (rawHist R Nh t).u (t Nh).2.2)
      (rawK R (rawHist R Nh t).u (t Nh).2.2) (histOut R Nh t).st (histOut R Nh t).g.re
      (histOut R Nh t).nu.re (histOut R Nh t).D (histOut R Nh t).K := by
  intro t
  have hρ0 : 0 ≤ R.ρ := hVL.2.2.2.2.1
  have HI := rawInv_hist R hρ0 Nh hV t
  obtain ⟨hnu, hg⟩ := traj_out_real R hρ0 hρ1 ((L : ℝ) ^ 2) b μ₀ Nh
  exact exactStep_of R hVL HI (rawD_mem R _ _) (rawK_mem R _ _) hρ1 hnu hg

end

end PtCorr2
