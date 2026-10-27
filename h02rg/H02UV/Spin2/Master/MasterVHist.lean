import Spin2.Master.MasterAllAbw
import Spin2.Pair.PairVReq
import PtCorr2.Pair.PairESz2

/-!
# `MasterCore`: the history `K`, `S`, bulk `V` and gradient sizes along admissible trajectories

The internal steps of `MasterCore.vstep` (`hK`, `hS`, the gradient bound), exported per scale
and for general weights (`D : MasterCore L`, the standard prelude). For every pair `P`, anchored
initial state `o₀` at `j₀` and weights `M_a, M_b > 0`, along every admissible trajectory:

* **`MasterCore.vhistK`** (`j₀ ≤ i ≤ N_h`, including `i = N_h` via `ValidAtL`,
  `PtCorr2.hist_smallK_leL`): a `K'` bound `k` in `wM(M_a, M_b)` gives
  `‖K_i(X)_{ab}‖_{T_i(s_i)} ≤ M_aM_b·8k` on small sets;
* **`MasterCore.vhistF`** (`i < N_h`): the step facts `hist_vstep_facts`;
* **`MasterCore.vhistS`** (`i < N_h`): `V`, `𝒲` bounds `m_V, m_W` in `wM` give
  `‖S_i(B_+)_{ab}‖_{T_{i+1}(s_{i+1})} ≤ M_aM_bL²s_O(cǧ_i, m_V, m_W)` (`sxo_hist_ab_le`) and
  `S_i(B_+)_{ab} = 0` off `{a, b}`;
* **`MasterCore.vhistE`** (`i ≤ N_h`, `c ≥ 1`): `‖V_i(B)_∅‖_{T_i(cs_i)} ≤ c⁴·cǧ_i` (bulk,
  `Fnorm_stVf_scale` and the `r`-bound of `hist_raw`/`hist_rawL`);
* **`MasterCore.vhistG`** (`j₀ ≤ n ≤ N_h`): per-scale small-set sizes `Q_i` and `S` sizes `S_i`
  give `gradM4Sz_{a}(V_n(B)_{ab}) ≤ gradRHS(…)` and `|M₄(V_n(B)_{ab})| ≤ m4RHS(…)`
  (`gradV_hist_leS`, constants `Ccut2`, `cSm2`, `cNb2`).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs2

set_option maxHeartbeats 4000000 in
/-- **The small-set `K` sizes along the history, up to `N_h`.** -/
theorem MasterCore.vhistK {L : ℕ} [NeZero L] (D : MasterCore L)
    (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0)
    (hRℓ : R.ℓ = D.ℓ) (hRA : R.A = D.A) (hRρ : R.ρ = D.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N)
    (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : Admissible (rgDataM R m) ((L : ℝ) ^ 2) D.κ D.cm D.cT Nh D.ε b μ₀)
    (P : Obs2.ObsPts 2 L N) {Ma Mb : ℝ} (hMa : 0 < Ma) (hMb : 0 < Mb)
    {j₀ : ℕ} (o₀ : ObsSt .two L N) (hl0 : ObsLocInv P j₀ o₀)
    (hs0 : ObsSymInv j₀ o₀) (ha0 : ObsAnchInv P j₀ o₀) (i : ℕ) (hji : j₀ ≤ i) (hi : i ≤ Nh)
    (k : ℝ)
    (hk : ∀ X, IsConn i X → ENNReal.ofReal ((R.withMsq m).A ^ (nb i X - 2 ^ 2)) *
        oTo (wM Ma Mb) i (histS (R.withMsq m) i (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          ((obsHistFrom (R.withMsq m) P j₀ o₀ i (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).K X) ≤
        ENNReal.ofReal k) :
    ∀ X, IsSmall i X →
      Tj 2 (L : ℝ) i (histS (R.withMsq m) i (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        (hKR (R.withMsq m) P j₀ o₀ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) i X :
          SA .two (Lam 2 L N)).ab ≤ ENNReal.ofReal (Ma * Mb * (8 * k)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hCN⟩ := id D.hC2
  set R' := R.withMsq m with hR'
  obtain ⟨H, hm1, F1⟩ := D.hXm N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm
  obtain ⟨hV, hVL⟩ := (hCN N R hP hi0 hRℓ hRA hRρ hN Nh hNh).2.2.2.2.2.2.2.2.2 m hm
  have hRA' : R'.A = D.A := hRA
  have hSB' : StepBounds L R'.A D.C₀x D.ηx D.εsx D.CKx D.C₂x D.CDx D.Cqx D.Clx D.cSx := by
    rw [hRA']; exact D.hSBx
  have hβ2 := betaL_ge (by have := D.hL49; omega : 8 ≤ L)
  have hβ0 : 0 ≤ betaL L := by linarith
  have ht := admissible_InDh_rg R' F1 hadm i hi
  intro X hX
  refine Tj_ab_le_of_oTo_wM' hMa hMb i _ _ ?_
  rcases Nat.lt_or_ge i Nh with hlt | hge
  · exact (hist_vstep_facts R' hSB' hV hm1 hβ0 (by norm_num : (1 / 2 : ℝ) ≤ 1) H P o₀ hl0 hs0 ha0
      _ i hji hlt ht).2.2.2.2.2.2.2 (wM Ma Mb) (wM_sub _ _) k hk X hX
  · obtain rfl : i = Nh := by omega
    have hmsq : R'.msq ∈ mRange L N := hm
    have hmN : |R'.msq| * ((L : ℝ) ^ i) ^ 2 ≤ 1 := by
      have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by have := D.hL49; omega)
      have h1 : R'.msq * ((L : ℝ) ^ (i + 1)) ^ 2 ≤ 1 := by
        have := msq_horizon (L := (L : ℝ)) hL1 hmsq.2 (Nh := i) (k := 0) (by omega)
        simpa using this
      have hm0 : 0 ≤ R'.msq := hmsq.1.le
      rw [abs_of_nonneg hm0]
      refine le_trans (mul_le_mul_of_nonneg_left ?_ hm0) h1
      exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ hL1 (by omega)) 2
    exact hist_smallK_leL R' hSB' hV hm1 hβ0 (by norm_num : (1 / 2 : ℝ) ≤ 1) H hVL hmN P o₀ _ ht
      (wM Ma Mb) (wM_sub _ _) k hk X hX

set_option maxHeartbeats 4000000 in
/-- **The step facts along the history below `N_h`.** -/
theorem MasterCore.vhistF {L : ℕ} [NeZero L] (D : MasterCore L)
    (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0)
    (hRℓ : R.ℓ = D.ℓ) (hRA : R.A = D.A) (hRρ : R.ρ = D.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N)
    (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : Admissible (rgDataM R m) ((L : ℝ) ^ 2) D.κ D.cm D.cT Nh D.ε b μ₀)
    (P : Obs2.ObsPts 2 L N) {j₀ : ℕ} (o₀ : ObsSt .two L N) (hl0 : ObsLocInv P j₀ o₀)
    (hs0 : ObsSymInv j₀ o₀) (ha0 : ObsAnchInv P j₀ o₀) (i : ℕ) (hji : j₀ ≤ i) (hi : i < Nh) :
    let R' := R.withMsq m
    let t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀
    GoodCov2 i (histS R' (i + 1) t / 4) (histCovO R' t i) ∧
    0 < histS R' i t ∧ 0 < histS R' (i + 1) t ∧
    ObsSymInv i (obsHistFrom R' P j₀ o₀ i t) ∧
    OAnchS P i (hVR R' P j₀ o₀ t i) (hWR R' P j₀ o₀ t i) (hKR R' P j₀ o₀ t i) ∧
    (∀ X, IsSmall i X →
      (hKR R' P j₀ o₀ t i X : SA .two (Lam 2 L N)).ab ∈ NX (nbhd i X : Set (Lam 2 L N))) ∧
    (∀ b ∈ blockIdx (L := L) (N := N) i,
      (SXO i (histCovO R' t i) (hVR R' P j₀ o₀ t i) (hWR R' P j₀ o₀ t i)
        (Step2.Bp (L := L) (N := N) i b) : SA .two (Lam 2 L N)).ab ∈
        NX (nbhd (i + 1) (Step2.Bp (L := L) (N := N) i b) : Set (Lam 2 L N))) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hCN⟩ := id D.hC2
  set R' := R.withMsq m with hR'
  obtain ⟨H, hm1, F1⟩ := D.hXm N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm
  obtain ⟨hV, -⟩ := (hCN N R hP hi0 hRℓ hRA hRρ hN Nh hNh).2.2.2.2.2.2.2.2.2 m hm
  have hRA' : R'.A = D.A := hRA
  have hSB' : StepBounds L R'.A D.C₀x D.ηx D.εsx D.CKx D.C₂x D.CDx D.Cqx D.Clx D.cSx := by
    rw [hRA']; exact D.hSBx
  have hβ2 := betaL_ge (by have := D.hL49; omega : 8 ≤ L)
  have hβ0 : 0 ≤ betaL L := by linarith
  have ht := admissible_InDh_rg R' F1 hadm i hi.le
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, -⟩ := hist_vstep_facts R' hSB' hV hm1 hβ0
    (by norm_num : (1 / 2 : ℝ) ≤ 1) H P o₀ hl0 hs0 ha0 _ i hji hi ht
  exact ⟨a1, a2, a3, a4, a5, a6, a7⟩

set_option maxHeartbeats 4000000 in
/-- **The `S` sizes along the history below `N_h`.** -/
theorem MasterCore.vhistS {L : ℕ} [NeZero L] (D : MasterCore L)
    (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0)
    (hRℓ : R.ℓ = D.ℓ) (hRA : R.A = D.A) (hRρ : R.ρ = D.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N)
    (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : Admissible (rgDataM R m) ((L : ℝ) ^ 2) D.κ D.cm D.cT Nh D.ε b μ₀)
    (P : Obs2.ObsPts 2 L N) {Ma Mb : ℝ} (hMa : 0 < Ma) (hMb : 0 < Mb)
    {j₀ : ℕ} (o₀ : ObsSt .two L N) (h0 : o₀.IsObs) (hl0 : ObsLocInv P j₀ o₀)
    (hs0 : ObsSymInv j₀ o₀) (ha0 : ObsAnchInv P j₀ o₀) (i : ℕ) (hji : j₀ ≤ i) (hi : i < Nh)
    (mV mW : ℝ) (hmV : 0 ≤ mV) (hmW : 0 ≤ mW)
    (hVo : ∀ b' ∈ blockIdx (L := L) (N := N) i,
      oTo (wM Ma Mb) i (histS (R.withMsq m) i (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((obsHistFrom (R.withMsq m) P j₀ o₀ i (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).V b') ≤
        ENNReal.ofReal mV)
    (hWo : ∀ b' ∈ blockIdx (L := L) (N := N) i,
      oTo (wM Ma Mb) i (histS (R.withMsq m) i (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((obsHistFrom (R.withMsq m) P j₀ o₀ i (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).W b') ≤
        ENNReal.ofReal mW) :
    let t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀
    ∀ b' ∈ blockIdx (L := L) (N := N) i,
      Tj 2 (L : ℝ) (i + 1) (histS (R.withMsq m) (i + 1) t)
          (SXO i (histCovO (R.withMsq m) t i) (hVR (R.withMsq m) P j₀ o₀ t i)
            (hWR (R.withMsq m) P j₀ o₀ t i) (Step2.Bp (L := L) (N := N) i b') :
            SA .two (Lam 2 L N)).ab ≤
        ENNReal.ofReal (Ma * Mb * ((L : ℝ) ^ 2 * sO 2 L (D.c * (t i).1) mV mW)) ∧
      (¬ (Step2.Bp (L := L) (N := N) i b' ∩ P.pts).Nonempty →
        (SXO i (histCovO (R.withMsq m) t i) (hVR (R.withMsq m) P j₀ o₀ t i)
          (hWR (R.withMsq m) P j₀ o₀ t i) (Step2.Bp (L := L) (N := N) i b') :
          SA .two (Lam 2 L N)).ab = 0) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hCN⟩ := id D.hC2
  set R' := R.withMsq m with hR'
  obtain ⟨H, hm1, F1⟩ := D.hXm N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm
  obtain ⟨hV, -⟩ := (hCN N R hP hi0 hRℓ hRA hRρ hN Nh hNh).2.2.2.2.2.2.2.2.2 m hm
  have hRA' : R'.A = D.A := hRA
  have hcR : cR R' ((L : ℝ) ^ 2) D.cm D.C₂x = D.c := by
    rw [D.hc]; exact cR_congr (show R.ℓ = D.ℓ from hRℓ) _ _ _
  have hSB' : StepBounds L R'.A D.C₀x D.ηx D.εsx D.CKx D.C₂x D.CDx D.Cqx D.Clx D.cSx := by
    rw [hRA']; exact D.hSBx
  have hβ2 := betaL_ge (by have := D.hL49; omega : 8 ≤ L)
  have hβ0 : 0 ≤ betaL L := by linarith
  have ht := admissible_InDh_rg R' F1 hadm i hi.le
  have H' := sxo_hist_ab_le R' D.hSX hSB' hV hm1 hβ0 (by norm_num : (1 / 2 : ℝ) ≤ 1) H P hMa hMb
    o₀ h0 hl0 hs0 ha0 _ i hji hi ht mV mW hmV hmW hVo hWo
  simp only [hcR] at H'
  exact H'

set_option maxHeartbeats 4000000 in
/-- **The bulk `V_i(B)_∅` at field scale `c·s_i`** (`i ≤ N_h`, `c ≥ 1`): `≤ c⁴·cǧ_i`. -/
theorem MasterCore.vhistE {L : ℕ} [NeZero L] (D : MasterCore L)
    (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0)
    (hRℓ : R.ℓ = D.ℓ) (hRA : R.A = D.A) (hRρ : R.ρ = D.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N)
    (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : Admissible (rgDataM R m) ((L : ℝ) ^ 2) D.κ D.cm D.cT Nh D.ε b μ₀)
    (P : Obs2.ObsPts 2 L N) {j₀ : ℕ} (o₀ : ObsSt .two L N) (h0 : o₀.IsObs)
    (i : ℕ) (hi : i ≤ Nh) {c : ℝ} (hc : 1 ≤ c) :
    ∀ b' ∈ blockIdx (L := L) (N := N) i,
      Tj 2 (L : ℝ) i (c * histS (R.withMsq m) i (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        (hVR (R.withMsq m) P j₀ o₀ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) i b' :
          SA .two (Lam 2 L N)).e ≤
        ENNReal.ofReal (c ^ 4 * (D.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ i).1)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hCN⟩ := id D.hC2
  set R' := R.withMsq m with hR'
  obtain ⟨H, hm1, F1⟩ := D.hXm N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm
  obtain ⟨hV, hVL⟩ := (hCN N R hP hi0 hRℓ hRA hRρ hN Nh hNh).2.2.2.2.2.2.2.2.2 m hm
  have hRA' : R'.A = D.A := hRA
  have hcR : cR R' ((L : ℝ) ^ 2) D.cm D.C₂x = D.c := by
    rw [D.hc]; exact cR_congr (show R.ℓ = D.ℓ from hRℓ) _ _ _
  have hSB' : StepBounds L R'.A D.C₀x D.ηx D.εsx D.CKx D.C₂x D.CDx D.Cqx D.Clx D.cSx := by
    rw [hRA']; exact D.hSBx
  have hβ2 := betaL_ge (by have := D.hL49; omega : 8 ≤ L)
  have hβ0 : 0 ≤ betaL L := by linarith
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  have ht := admissible_InDh_rg R' F1 hadm i hi
  have hmsq : R'.msq ∈ mRange L N := hm
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by have := D.hL49; omega)
  have hmi : |R'.msq| * ((L : ℝ) ^ i) ^ 2 ≤ 1 := by
    rcases Nat.lt_or_ge i Nh with hlt | hge
    · exact hm1 i hlt
    · have h1 : R'.msq * ((L : ℝ) ^ (Nh + 1)) ^ 2 ≤ 1 := by
        have := msq_horizon (L := (L : ℝ)) hL1 hmsq.2 (Nh := Nh) (k := 0) (by omega)
        simpa using this
      have hm0 : 0 ≤ R'.msq := hmsq.1.le
      rw [abs_of_nonneg hm0]
      refine le_trans (mul_le_mul_of_nonneg_left ?_ hm0) h1
      exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ hL1 (by omega)) 2
  -- the raw data at `i`
  have key : ValidCore R' i ∧ RawInv R' i (rawHist R' i t) ∧ 0 ≤ (t i).1 ∧
      ‖(rawHist R' i t).z / (rawHist R' i t).Z‖ ≤ cZ R' * (t i).1 ∧
      ‖(rawHist R' i t).y / (rawHist R' i t).Z‖ ≤ cZ R' * (t i).1 ∧
      2 * (cZ R' * (t i).1) ≤ R'.ρ ∧
      cM * R'.ℓ ^ 2 * (2 * |(t i).2.1| + 2 * (cZ R' * (t i).1)) + 8 * R'.ℓ ^ 4 * (t i).1 ≤
        cR R' ((L : ℝ) ^ 2) D.cm D.C₂x * (t i).1 := by
    rcases Nat.lt_or_ge i Nh with hlt | hge
    · obtain ⟨a1, a2, a3, -, a5, a6, a7, -, -, -, a11, -⟩ :=
        hist_raw R' hSB' hV hm1 hβ0 (by norm_num : (1 / 2 : ℝ) ≤ 1) H t i hlt ht
      exact ⟨a1, a2, a3, a5, a6, a7, a11⟩
    · obtain rfl : i = Nh := by omega
      obtain ⟨a1, a2, a3, -, a5, a6, a7, -, -, -, a11, -⟩ :=
        hist_rawL R' hSB' hV hm1 hβ0 (by norm_num : (1 / 2 : ℝ) ≤ 1) H hVL t ht
      exact ⟨a1, a2, a3, a5, a6, a7, a11⟩
  obtain ⟨hVc, HI, hg, hz, hy, hη, hr⟩ := key
  have hF := Fnorm_stVf_scale R' i hVc (rawHist R' i t) HI (t i).1 (t i).2.1 hmi hg _ hz hy hη hc
  intro b' hb'
  have he : (hVR R' P j₀ o₀ t i b' : SA .two (Lam 2 L N)).e =
      (stVf R' i (rawHist R' i t) (t i).1 (t i).2.1 b' : Alg 2 L N) := by
    show (((emb _ : OE .two (Lam 2 L N)) + (obsHistFrom R' P j₀ o₀ i t).V b' : OE .two (Lam 2 L N)) :
      SA .two (Lam 2 L N)).e = _
    rw [emb_add_e, e_eq_zero_of_bulk ((obsHistFrom_isObs (R := R') (P := P) h0 t i).V b'), add_zero]
  change Tj 2 (L : ℝ) i (c * histS R' i t) (hVR R' P j₀ o₀ t i b' : SA .two (Lam 2 L N)).e ≤ _
  rw [he, show c * histS R' i t = fscale (rawHist R' i t).Z * (c * R'.ℓ) by
    unfold histS; ring]
  refine (le_iSup₂_of_le b' hb' le_rfl : _ ≤ Fnorm i _ _).trans (hF.trans
    (ENNReal.ofReal_le_ofReal ?_))
  rw [hcR] at hr
  exact mul_le_mul_of_nonneg_left hr (by positivity)

set_option maxHeartbeats 4000000 in
/-- **The per-scale gradient/`M₄` sizes of `V_n(B)_{ab}`** (`gradV_hist_leS` under the master
constants). -/
theorem MasterCore.vhistG {L : ℕ} [NeZero L] (D : MasterCore L)
    (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0)
    (hRℓ : R.ℓ = D.ℓ) (hRA : R.A = D.A) (hRρ : R.ρ = D.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N)
    (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : Admissible (rgDataM R m) ((L : ℝ) ^ 2) D.κ D.cm D.cT Nh D.ε b μ₀)
    (P : Obs2.ObsPts 2 L N) (hab : P.a ≠ P.b) (w : List (Dir 2)) (hw : pathEnd P.a w = P.b)
    (hwl : (w.length : ℝ) ≤ 2 * ((supNorm (P.a - P.b) : ℕ) : ℝ))
    {j₀ : ℕ} (o₀ : ObsSt .two L N) (hl0 : ObsLocInv P j₀ o₀) (hs0 : ObsSymInv j₀ o₀)
    (ha0 : ObsAnchInv P j₀ o₀) (hvab : ObsVabInv P o₀)
    (hz : ∀ b, (o₀.V b : SA .two (Lam 2 L N)).ab = 0) {n : ℕ} (hjn : j₀ ≤ n) (hn : n ≤ Nh)
    (QK SS : ℕ → ℝ) (hQ0 : ∀ i, 0 ≤ QK i) (hS0 : ∀ i, 0 ≤ SS i)
    (hK : ∀ i, j₀ ≤ i → i < n → ∀ X, IsSmall i X →
      Tj 2 (L : ℝ) i (histS (R.withMsq m) i (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        (hKR (R.withMsq m) P j₀ o₀ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) i X :
          SA .two (Lam 2 L N)).ab ≤ ENNReal.ofReal (QK i))
    (hS : ∀ i, j₀ ≤ i → i < n → ∀ b' ∈ blockIdx (L := L) (N := N) i,
      Tj 2 (L : ℝ) (i + 1) (histS (R.withMsq m) (i + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        (SXO i (histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) i)
          (hVR (R.withMsq m) P j₀ o₀ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) i)
          (hWR (R.withMsq m) P j₀ o₀ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) i)
          (Step2.Bp (L := L) (N := N) i b') : SA .two (Lam 2 L N)).ab ≤
        ENNReal.ofReal (SS i)) :
    ∀ c ∈ blockIdx (L := L) (N := N) n,
      gradM4Sz {P.a} P.a P.b ((L : ℝ) ^ n)
          (histS (R.withMsq m) n (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          (hVR (R.withMsq m) P j₀ o₀ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) n c :
            SA .two (Lam 2 L N)).ab ≤
        gradRHS (L : ℝ) (Obs2.KG 2 Ccut2 4) (KM4 2 Ccut2) ((supNorm (P.a - P.b) : ℕ) : ℝ)
          (fun i => histS (R.withMsq m) i (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          (fun i => 2 * (cNb2 : ℝ) * (cSm2 : ℝ) * QK i) (fun i => 2 * (L : ℝ) ^ 2 * SS i) j₀ n ∧
      ‖cfAB4 P.a P.b (hVR (R.withMsq m) P j₀ o₀ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) n c :
          SA .two (Lam 2 L N)).ab‖ ≤
        m4RHS (L : ℝ) (KM4 2 Ccut2) ((supNorm (P.a - P.b) : ℕ) : ℝ)
          (fun i => histS (R.withMsq m) i (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          (fun i => 2 * (cNb2 : ℝ) * (cSm2 : ℝ) * QK i) (fun i => 2 * (L : ℝ) ^ 2 * SS i) j₀ n := by
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8, -, hCN⟩ := id D.hC2
  set R' := R.withMsq m with hR'
  obtain ⟨H, hm1, F1⟩ := D.hXm N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm
  obtain ⟨hV, -⟩ := (hCN N R hP hi0 hRℓ hRA hRρ hN Nh hNh).2.2.2.2.2.2.2.2.2 m hm
  have hRA' : R'.A = D.A := hRA
  have hSB' : StepBounds L R'.A D.C₀x D.ηx D.εsx D.CKx D.C₂x D.CDx D.Cqx D.Clx D.cSx := by
    rw [hRA']; exact D.hSBx
  have hβ2 := betaL_ge (by have := D.hL49; omega : 8 ≤ L)
  have hβ0 : 0 ≤ betaL L := by linarith
  have hti : ∀ i ≤ n, Flow2.Hist.InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) D.κ D.cg D.cm D.cT D.ε i
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) :=
    fun i hi => admissible_InDh_rg R' F1 hadm i (hi.trans hn)
  have hρ0' : 0 ≤ R'.ρ := by rw [show R'.ρ = D.ρ from hRρ]; linarith
  have hρ8' : R'.ρ ≤ 1 / 8 := by rw [show R'.ρ = D.ρ from hRρ]; linarith
  have hL8 : 2 ^ (2 + 3) + 8 * 2 < L := by have := D.hL49; omega
  exact gradV_hist_leS R' hSB' hV hm1 hβ0 (by norm_num : (1 / 2 : ℝ) ≤ 1) H (by omega) hρ0' hρ8'
    hL8 Ccut2_spec.1 Ccut2_spec.2 (cSn := (cSm2 : ℝ)) (cNn := (cNb2 : ℝ))
    (fun i b' hb' => by exact_mod_cast cSm2_spec L N i b' hb')
    (fun i x s hs => by exact_mod_cast cNb2_spec L N i x s hs)
    P hab w hw hwl o₀ hl0 hs0 ha0 hvab hz _ hjn hn hti QK SS hQ0 hS0 hK hS

end

end Spin2
