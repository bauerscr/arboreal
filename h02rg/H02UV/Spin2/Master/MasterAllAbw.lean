import Spin2.Master.MasterAllCore

/-!
# `MasterCore`: the reduced `ab` chain with per-scale weights and the `S_j(B_+)` bound

Under the consolidated master constants (with the requirements `abwAReq`, `abwEReq` of
`Spin2/Master/AbwReq`, now part of `allAReq`/`allEReq`), along every admissible trajectory:

* **`MasterCore.abwHist`**: `PtCorr2.obs_histFromABL_wM` (the `K'`, `𝒲'` sizes of the `ab` chain
  from `j₀` in the weights `wM(M_{a,j}, M_{b,j})`, `c_k = 1`) for every `n ≤ N_h`; the only inputs
  left are those of the chain itself (`V'` sizes `m_j` on `[j₀, n)`, the seed `k₀`, `𝒲'_{j₀}`).
  The constants `C₁k`, `C₁w` (of `KObsBoundsABL`, `WObsBoundsAB`) are exported;
  `cR(R_m) = c` (`= D.c`).
* **`MasterCore.sxoHist`**: `PtCorr2.sxo_hist_ab_le` (`‖S_j(B_+)_{ab}‖_{T_{j+1}(s_{j+1})} ≤
  M_aM_bL²s_O(cǧ_j, m_V, m_W)`, anchoring) for `j < N_h`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2 Obs Obs2

set_option maxHeartbeats 4000000 in
/-- **The reduced `ab` chain with per-scale weights under the master constants.** -/
theorem MasterCore.abwHist {L : ℕ} [NeZero L] (D : MasterCore L) :
    ∃ C₁k C₁w : ℝ, 0 ≤ C₁k ∧ 0 ≤ C₁w ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = D.ℓ → R.A = D.A → R.ρ = D.ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
    ∀ m ∈ mRange L N, ∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) D.κ D.cm D.cT Nh D.ε b μ₀ →
    cR (R.withMsq m) ((L : ℝ) ^ 2) D.cm D.C₂x = D.c ∧
    ∀ (P : Obs2.ObsPts 2 L N) (Ma Mb : ℕ → ℝ), (∀ j, 0 < Ma j) → (∀ j, 0 < Mb j) →
    ∀ (j₀ : ℕ) (o₀ : ObsSt .two L N), o₀.IsObs → ObsLocInv P j₀ o₀ → ObsSymInv j₀ o₀ →
      ObsAnchInv P j₀ o₀ →
    ∀ n ≤ Nh, ∀ mm : ℕ → ℝ, (∀ j, 0 < mm j) →
    (∀ j, j₀ ≤ j → j < n → Ma j * Mb j / (Ma j₀ * Mb j₀) * mm j ≤
      2 * (Ma (j + 1) * Mb (j + 1) / (Ma j₀ * Mb j₀) * mm (j + 1))) →
    (∀ j, j₀ ≤ j → j < n → ∀ b' ∈ blockIdx (L := L) (N := N) j,
      oTo (wM (Ma j) (Mb j)) j (histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((obsHistFrom (R.withMsq m) P j₀ o₀ j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).V b') ≤
        ENNReal.ofReal (mm j)) →
    (∀ b' ∈ blockIdx (L := L) (N := N) j₀, oTo (wM (Ma j₀) (Mb j₀)) j₀
      (histS (R.withMsq m) j₀ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) (o₀.W b') ≤
      ENNReal.ofReal ((4 * C₁w + 1) * (cR (R.withMsq m) ((L : ℝ) ^ 2) D.cm D.C₂x *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j₀).1) * mm j₀)) →
    ∀ k₀ : ℝ, 0 ≤ k₀ →
    (∀ X, IsConn j₀ X → ENNReal.ofReal ((R.withMsq m).A ^ (nb j₀ X - 2 ^ 2)) *
      oTo (wM (Ma j₀) (Mb j₀)) j₀
        (histS (R.withMsq m) j₀ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) (o₀.K X) ≤
        ENNReal.ofReal k₀) →
    8 * k₀ ≤ 1 * ((4 * C₁w + 1) * mm j₀) →
    let B := kB (kθ0 L (R.withMsq m).A D.C₀a D.ηa) C₁k (8 * cx D.κ D.cT)
    let θb := kθ0 L (R.withMsq m).A D.C₀a D.ηa + C₁k * (2 + 2 * (8 * cx D.κ D.cT) + 1) *
      (cR (R.withMsq m) ((L : ℝ) ^ 2) D.cm D.C₂x * D.ε)
    let r := fun j => cR (R.withMsq m) ((L : ℝ) ^ 2) D.cm D.C₂x *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1
    let cWc := 4 * C₁w + 1
    let lamM := fun i => Ma i * Mb i / (Ma j₀ * Mb j₀)
    ∀ j, j₀ ≤ j → j ≤ n →
      8 * kseqF (8 * θb) B r (fun i => cWc * (lamM i * mm i)) j₀ k₀ j ≤
        1 * (cWc * (lamM j * mm j)) ∧
      (∀ b' ∈ blockIdx (L := L) (N := N) j,
        oTo (wM (Ma j) (Mb j)) j (histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          ((obsHistFrom (R.withMsq m) P j₀ o₀ j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).W b') ≤
          ENNReal.ofReal (cWc * r j * mm j)) ∧
      (∀ X, IsConn j X → ENNReal.ofReal ((R.withMsq m).A ^ (nb j X - 2 ^ 2)) *
        oTo (wM (Ma j) (Mb j)) j (histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          ((obsHistFrom (R.withMsq m) P j₀ o₀ j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).K X) ≤
          ENNReal.ofReal (kseqF (8 * θb) B r (fun i => cWc * (lamM i * mm i)) j₀ k₀ j /
            lamM j)) := by
  obtain ⟨hθa0, hθa⟩ : 0 ≤ kθ0 L D.A D.C₀a D.ηa ∧ kθ0 L D.A D.C₀a D.ηa ≤ 1 / 72 := by
    refine ⟨?_, (D.hAa D.hLa).2⟩
    unfold kθ0
    have := D.hA2
    exact mul_nonneg D.hC₀a (add_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _))
  obtain ⟨ε₀, C₁k, hε₀, hC₁k, hKB, hsm, hεε, hεk, hBr, C₁w, ε₁, hC₁w, hε₁, hWB, hC₁ε, hε₁'⟩ :=
    D.hEa D.hLa D.hAa
  refine ⟨C₁k, C₁w, hC₁k, hC₁w, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8, -, hCN⟩ := id D.hC2
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
  refine ⟨hcR, ?_⟩
  intro P Ma Mb hMa hMb j₀ o₀ h0 hl0 hs0 ha0 n hn mm hm0 hm' hVo hW0 k₀ hk₀ hK0 h8
  have ht := admissible_InDh_rg R' F1 hadm n hn
  have hL0 : (0 : ℝ) < L := Nat.cast_pos.2 (by have := D.hL49; omega)
  have hKB' : KObsBoundsABL L R'.A D.C₀a D.ηa ε₀ C₁k := by rw [hRA']; exact hKB
  have hθa0' : 0 ≤ kθ0 L R'.A D.C₀a D.ηa := by rw [hRA']; exact hθa0
  have hθa' : kθ0 L R'.A D.C₀a D.ηa ≤ 1 / 72 := by rw [hRA']; exact hθa
  have hBr' : 32 * kB (kθ0 L R'.A D.C₀a D.ηa) C₁k (8 * cx D.κ D.cT) *
      (cR R' ((L : ℝ) ^ 2) D.cm D.C₂x * D.ε) ^ 2 ≤ 1 := by rw [hRA', hcR]; exact hBr
  exact obs_histFromABL_wM R' hKB' hC₁k 1 zero_le_one hWB hC₁w hSB' hV hm1 hβ0
    (by norm_num : (1 / 2 : ℝ) ≤ 1) H P Ma Mb hMa hMb o₀ h0 hl0 hs0 ha0
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) n hn ht hθa0' hθa' (by rw [hcR]; exact hsm)
    (by rw [hcR]; exact D.hcε) (by rw [hcR]; exact hεε) (by rw [hcR]; exact hεk) hBr' D.hLwa
    (by rw [hcR]; exact hC₁ε) (by rw [hcR]; exact hε₁') mm hm0 hm' hVo hW0 k₀ hk₀ hK0 h8


/-- The conclusion of `MasterCore.abwHist` at given constants `C₁k`, `C₁w`. -/
def MasterCore.AbwHistP {L : ℕ} [NeZero L] (D : MasterCore L) (C₁k C₁w : ℝ) : Prop :=
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = D.ℓ → R.A = D.A → R.ρ = D.ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
    ∀ m ∈ mRange L N, ∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) D.κ D.cm D.cT Nh D.ε b μ₀ →
    cR (R.withMsq m) ((L : ℝ) ^ 2) D.cm D.C₂x = D.c ∧
    ∀ (P : Obs2.ObsPts 2 L N) (Ma Mb : ℕ → ℝ), (∀ j, 0 < Ma j) → (∀ j, 0 < Mb j) →
    ∀ (j₀ : ℕ) (o₀ : ObsSt .two L N), o₀.IsObs → ObsLocInv P j₀ o₀ → ObsSymInv j₀ o₀ →
      ObsAnchInv P j₀ o₀ →
    ∀ n ≤ Nh, ∀ mm : ℕ → ℝ, (∀ j, 0 < mm j) →
    (∀ j, j₀ ≤ j → j < n → Ma j * Mb j / (Ma j₀ * Mb j₀) * mm j ≤
      2 * (Ma (j + 1) * Mb (j + 1) / (Ma j₀ * Mb j₀) * mm (j + 1))) →
    (∀ j, j₀ ≤ j → j < n → ∀ b' ∈ blockIdx (L := L) (N := N) j,
      oTo (wM (Ma j) (Mb j)) j (histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((obsHistFrom (R.withMsq m) P j₀ o₀ j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).V b') ≤
        ENNReal.ofReal (mm j)) →
    (∀ b' ∈ blockIdx (L := L) (N := N) j₀, oTo (wM (Ma j₀) (Mb j₀)) j₀
      (histS (R.withMsq m) j₀ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) (o₀.W b') ≤
      ENNReal.ofReal ((4 * C₁w + 1) * (cR (R.withMsq m) ((L : ℝ) ^ 2) D.cm D.C₂x *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j₀).1) * mm j₀)) →
    ∀ k₀ : ℝ, 0 ≤ k₀ →
    (∀ X, IsConn j₀ X → ENNReal.ofReal ((R.withMsq m).A ^ (nb j₀ X - 2 ^ 2)) *
      oTo (wM (Ma j₀) (Mb j₀)) j₀
        (histS (R.withMsq m) j₀ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) (o₀.K X) ≤
        ENNReal.ofReal k₀) →
    8 * k₀ ≤ 1 * ((4 * C₁w + 1) * mm j₀) →
    let B := kB (kθ0 L (R.withMsq m).A D.C₀a D.ηa) C₁k (8 * cx D.κ D.cT)
    let θb := kθ0 L (R.withMsq m).A D.C₀a D.ηa + C₁k * (2 + 2 * (8 * cx D.κ D.cT) + 1) *
      (cR (R.withMsq m) ((L : ℝ) ^ 2) D.cm D.C₂x * D.ε)
    let r := fun j => cR (R.withMsq m) ((L : ℝ) ^ 2) D.cm D.C₂x *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1
    let cWc := 4 * C₁w + 1
    let lamM := fun i => Ma i * Mb i / (Ma j₀ * Mb j₀)
    ∀ j, j₀ ≤ j → j ≤ n →
      8 * kseqF (8 * θb) B r (fun i => cWc * (lamM i * mm i)) j₀ k₀ j ≤
        1 * (cWc * (lamM j * mm j)) ∧
      (∀ b' ∈ blockIdx (L := L) (N := N) j,
        oTo (wM (Ma j) (Mb j)) j (histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          ((obsHistFrom (R.withMsq m) P j₀ o₀ j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).W b') ≤
          ENNReal.ofReal (cWc * r j * mm j)) ∧
      (∀ X, IsConn j X → ENNReal.ofReal ((R.withMsq m).A ^ (nb j X - 2 ^ 2)) *
        oTo (wM (Ma j) (Mb j)) j (histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          ((obsHistFrom (R.withMsq m) P j₀ o₀ j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).K X) ≤
          ENNReal.ofReal (kseqF (8 * θb) B r (fun i => cWc * (lamM i * mm i)) j₀ k₀ j /
            lamM j))

set_option maxHeartbeats 4000000 in
/-- **`MasterCore.abwHist` at the exported constants** `C₁k = D.C₁ka`, `C₁w = D.C₁wa` (the
witnesses of `pairEReq`; the smallness `C₁k(3 + 16c_x)cε ≤ 1/72` is `D.hEaB.2.2.2.1`). -/
theorem MasterCore.abwHistC {L : ℕ} [NeZero L] (D : MasterCore L) :
    D.AbwHistP D.C₁ka D.C₁wa := by
  obtain ⟨hθa0, hθa⟩ : 0 ≤ kθ0 L D.A D.C₀a D.ηa ∧ kθ0 L D.A D.C₀a D.ηa ≤ 1 / 72 := by
    refine ⟨?_, (D.hAa D.hLa).2⟩
    unfold kθ0
    have := D.hA2
    exact mul_nonneg D.hC₀a (add_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _))
  obtain ⟨hε₀, hC₁k, hKB, hsm, hεε, hεk, hBr, hC₁w, hε₁, hWB, hC₁ε, hε₁'⟩ := D.hEaB
  unfold MasterCore.AbwHistP
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8, -, hCN⟩ := id D.hC2
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
  refine ⟨hcR, ?_⟩
  intro P Ma Mb hMa hMb j₀ o₀ h0 hl0 hs0 ha0 n hn mm hm0 hm' hVo hW0 k₀ hk₀ hK0 h8
  have ht := admissible_InDh_rg R' F1 hadm n hn
  have hL0 : (0 : ℝ) < L := Nat.cast_pos.2 (by have := D.hL49; omega)
  have hKB' : KObsBoundsABL L R'.A D.C₀a D.ηa D.ε₀a D.C₁ka := by rw [hRA']; exact hKB
  have hθa0' : 0 ≤ kθ0 L R'.A D.C₀a D.ηa := by rw [hRA']; exact hθa0
  have hθa' : kθ0 L R'.A D.C₀a D.ηa ≤ 1 / 72 := by rw [hRA']; exact hθa
  have hBr' : 32 * kB (kθ0 L R'.A D.C₀a D.ηa) D.C₁ka (8 * cx D.κ D.cT) *
      (cR R' ((L : ℝ) ^ 2) D.cm D.C₂x * D.ε) ^ 2 ≤ 1 := by rw [hRA', hcR]; exact hBr
  exact obs_histFromABL_wM R' hKB' hC₁k 1 zero_le_one hWB hC₁w hSB' hV hm1 hβ0
    (by norm_num : (1 / 2 : ℝ) ≤ 1) H P Ma Mb hMa hMb o₀ h0 hl0 hs0 ha0
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) n hn ht hθa0' hθa' (by rw [hcR]; exact hsm)
    (by rw [hcR]; exact D.hcε) (by rw [hcR]; exact hεε) (by rw [hcR]; exact hεk) hBr' D.hLwa
    (by rw [hcR]; exact hC₁ε) (by rw [hcR]; exact hε₁') mm hm0 hm' hVo hW0 k₀ hk₀ hK0 h8

set_option maxHeartbeats 4000000 in
/-- **`κ^S_j(B)` under the master constants**: `PtCorr2.sxo_hist_ab_le` along every admissible
trajectory (`j₀ ≤ j < N_h`). -/
theorem MasterCore.sxoHist {L : ℕ} [NeZero L] (D : MasterCore L)
    (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0)
    (hRℓ : R.ℓ = D.ℓ) (hRA : R.A = D.A) (hRρ : R.ρ = D.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N)
    (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : Admissible (rgDataM R m) ((L : ℝ) ^ 2) D.κ D.cm D.cT Nh D.ε b μ₀)
    (P : Obs2.ObsPts 2 L N) {Ma Mb : ℝ} (hMa : 0 < Ma) (hMb : 0 < Mb)
    {j₀ : ℕ} (o₀ : ObsSt .two L N) (h0 : o₀.IsObs) (hl0 : ObsLocInv P j₀ o₀)
    (hs0 : ObsSymInv j₀ o₀) (ha0 : ObsAnchInv P j₀ o₀) (j : ℕ) (hjj : j₀ ≤ j) (hj : j < Nh)
    (mV mW : ℝ) (hmV : 0 ≤ mV) (hmW : 0 ≤ mW)
    (hVo : ∀ b' ∈ blockIdx (L := L) (N := N) j,
      oTo (wM Ma Mb) j (histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((obsHistFrom (R.withMsq m) P j₀ o₀ j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).V b') ≤
        ENNReal.ofReal mV)
    (hWo : ∀ b' ∈ blockIdx (L := L) (N := N) j,
      oTo (wM Ma Mb) j (histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((obsHistFrom (R.withMsq m) P j₀ o₀ j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).W b') ≤
        ENNReal.ofReal mW) :
    ∀ b' ∈ blockIdx (L := L) (N := N) j,
      Tj 2 (L : ℝ) (j + 1) (histS (R.withMsq m) (j + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          (SXO j (histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j)
            (hVR (R.withMsq m) P j₀ o₀ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j)
            (hWR (R.withMsq m) P j₀ o₀ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j)
            (Step2.Bp (L := L) (N := N) j b') : SA .two (Lam 2 L N)).ab ≤
        ENNReal.ofReal (Ma * Mb * ((L : ℝ) ^ 2 *
          sO 2 L (D.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1) mV mW)) ∧
      (¬ (Step2.Bp (L := L) (N := N) j b' ∩ P.pts).Nonempty →
        (SXO j (histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j)
            (hVR (R.withMsq m) P j₀ o₀ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j)
            (hWR (R.withMsq m) P j₀ o₀ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j)
            (Step2.Bp (L := L) (N := N) j b') : SA .two (Lam 2 L N)).ab = 0) := by
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
  have ht := admissible_InDh_rg R' F1 hadm j hj.le
  have H' := sxo_hist_ab_le R' D.hSX hSB' hV hm1 hβ0 (by norm_num : (1 / 2 : ℝ) ≤ 1) H P hMa hMb
    o₀ h0 hl0 hs0 ha0 (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j hjj hj ht mV mW hmV hmW hVo hWo
  rw [hcR] at H'
  exact H'

end

end Spin2
