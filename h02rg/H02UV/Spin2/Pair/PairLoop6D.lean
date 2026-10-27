import Spin2.Pair.PairFinal4

/-!
# The windowed (`D_ε`) forms of the `E`-step chain (route (a1))

Copies of `MasterCore.abwHist`, `sxoHist`, `vhistK/F/S/E/G`, `wpoHist`, `wpoOff`, `pairWSizes_MF`,
`pairKSSizes_MF`, `pairESizes3_MF`, `pairRedInv_MF`, `pairJointSizesP3_MF`,
`pairRRelR_of_jointSizesP3_MF`, `pairJointSizesP3_of_VS`, `pl6_item_le`, `pl6_sum_le` and
`pairJointSizesP3_closed` (suffix `D6`) with `Admissible … b μ₀` replaced by the domain condition
`∀ j ≤ N_h, InD3 … (t_j)` (`inDh_rg_of_D` and the `D` forms of `MasterFacts`, `Spin2/Master/MasterAllFactsD`).
Same bodies otherwise.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs2

set_option maxHeartbeats 4000000 in
/-- **The reduced `ab` chain with per-scale weights under the master constants.** -/
theorem MasterCore.abwHistD6 {L : ℕ} [NeZero L] (D : MasterCore L) :
    ∃ C₁k C₁w : ℝ, 0 ≤ C₁k ∧ 0 ≤ C₁w ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = D.ℓ → R.A = D.A → R.ρ = D.ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
    ∀ m ∈ mRange L N, ∀ b μ₀, (∀ jD ≤ Nh, InD3 ((L : ℝ) ^ 2) D.κ D.cm D.cT D.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ jD)) →
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
  have ht := inDh_rg_of_D R' F1 hadm n hn
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


/-- The conclusion of `MasterCore.abwHistD6` at given constants `C₁k`, `C₁w`. -/
def MasterCore.AbwHistPD6 {L : ℕ} [NeZero L] (D : MasterCore L) (C₁k C₁w : ℝ) : Prop :=
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = D.ℓ → R.A = D.A → R.ρ = D.ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
    ∀ m ∈ mRange L N, ∀ b μ₀, (∀ jD ≤ Nh, InD3 ((L : ℝ) ^ 2) D.κ D.cm D.cT D.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ jD)) →
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
/-- **`MasterCore.abwHistD6` at the exported constants** `C₁k = D.C₁ka`, `C₁w = D.C₁wa`. -/
theorem MasterCore.abwHistCD6 {L : ℕ} [NeZero L] (D : MasterCore L) :
    D.AbwHistPD6 D.C₁ka D.C₁wa := by
  obtain ⟨hθa0, hθa⟩ : 0 ≤ kθ0 L D.A D.C₀a D.ηa ∧ kθ0 L D.A D.C₀a D.ηa ≤ 1 / 72 := by
    refine ⟨?_, (D.hAa D.hLa).2⟩
    unfold kθ0
    have := D.hA2
    exact mul_nonneg D.hC₀a (add_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _))
  obtain ⟨hε₀, hC₁k, hKB, hsm, hεε, hεk, hBr, hC₁w, hε₁, hWB, hC₁ε, hε₁'⟩ := D.hEaB
  unfold MasterCore.AbwHistPD6
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
  have ht := inDh_rg_of_D R' F1 hadm n hn
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
/-- **The small-set `K` sizes along the history, up to `N_h`.** -/
theorem MasterCore.vhistKD6 {L : ℕ} [NeZero L] (D : MasterCore L)
    (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0)
    (hRℓ : R.ℓ = D.ℓ) (hRA : R.A = D.A) (hRρ : R.ρ = D.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N)
    (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : (∀ jD ≤ Nh, InD3 ((L : ℝ) ^ 2) D.κ D.cm D.cT D.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ jD)))
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
  have ht := inDh_rg_of_D R' F1 hadm i hi
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
theorem MasterCore.vhistFD6 {L : ℕ} [NeZero L] (D : MasterCore L)
    (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0)
    (hRℓ : R.ℓ = D.ℓ) (hRA : R.A = D.A) (hRρ : R.ρ = D.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N)
    (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : (∀ jD ≤ Nh, InD3 ((L : ℝ) ^ 2) D.κ D.cm D.cT D.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ jD)))
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
  have ht := inDh_rg_of_D R' F1 hadm i hi.le
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, -⟩ := hist_vstep_facts R' hSB' hV hm1 hβ0
    (by norm_num : (1 / 2 : ℝ) ≤ 1) H P o₀ hl0 hs0 ha0 _ i hji hi ht
  exact ⟨a1, a2, a3, a4, a5, a6, a7⟩


set_option maxHeartbeats 4000000 in
/-- **The `S` sizes along the history below `N_h`.** -/
theorem MasterCore.vhistSD6 {L : ℕ} [NeZero L] (D : MasterCore L)
    (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0)
    (hRℓ : R.ℓ = D.ℓ) (hRA : R.A = D.A) (hRρ : R.ρ = D.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N)
    (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : (∀ jD ≤ Nh, InD3 ((L : ℝ) ^ 2) D.κ D.cm D.cT D.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ jD)))
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
  have ht := inDh_rg_of_D R' F1 hadm i hi.le
  have H' := sxo_hist_ab_le R' D.hSX hSB' hV hm1 hβ0 (by norm_num : (1 / 2 : ℝ) ≤ 1) H P hMa hMb
    o₀ h0 hl0 hs0 ha0 _ i hji hi ht mV mW hmV hmW hVo hWo
  simp only [hcR] at H'
  exact H'


set_option maxHeartbeats 4000000 in
/-- **The bulk `V_i(B)_∅` at field scale `c·s_i`** (`i ≤ N_h`, `c ≥ 1`): `≤ c⁴·cǧ_i`. -/
theorem MasterCore.vhistED6 {L : ℕ} [NeZero L] (D : MasterCore L)
    (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0)
    (hRℓ : R.ℓ = D.ℓ) (hRA : R.A = D.A) (hRρ : R.ρ = D.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N)
    (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : (∀ jD ≤ Nh, InD3 ((L : ℝ) ^ 2) D.κ D.cm D.cT D.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ jD)))
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
  have ht := inDh_rg_of_D R' F1 hadm i hi
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
theorem MasterCore.vhistGD6 {L : ℕ} [NeZero L] (D : MasterCore L)
    (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0)
    (hRℓ : R.ℓ = D.ℓ) (hRA : R.A = D.A) (hRρ : R.ρ = D.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N)
    (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : (∀ jD ≤ Nh, InD3 ((L : ℝ) ^ 2) D.κ D.cm D.cT D.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ jD)))
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
    fun i hi => inDh_rg_of_D R' F1 hadm i (hi.trans hn)
  have hρ0' : 0 ≤ R'.ρ := by rw [show R'.ρ = D.ρ from hRρ]; linarith
  have hρ8' : R'.ρ ≤ 1 / 8 := by rw [show R'.ρ = D.ρ from hRρ]; linarith
  have hL8 : 2 ^ (2 + 3) + 8 * 2 < L := by have := D.hL49; omega
  exact gradV_hist_leS R' hSB' hV hm1 hβ0 (by norm_num : (1 / 2 : ℝ) ≤ 1) H (by omega) hρ0' hρ8'
    hL8 Ccut2_spec.1 Ccut2_spec.2 (cSn := (cSm2 : ℝ)) (cNn := (cNb2 : ℝ))
    (fun i b' hb' => by exact_mod_cast cSm2_spec L N i b' hb')
    (fun i x s hs => by exact_mod_cast cNb2_spec L N i x s hs)
    P hab w hw hwl o₀ hl0 hs0 ha0 hvab hz _ hjn hn hti QK SS hQ0 hS0 hK hS


set_option maxHeartbeats 4000000 in
/-- **`wpo_hist_ab_le` along admissible trajectories of the master construction.** -/
theorem MasterCore.wpoHistD6 {L : ℕ} [NeZero L] (D : MasterCore L) {Clo Clb : ℝ}
    (hWB : WpOBoundsAB L Clo Clb) (hClo : 0 ≤ Clo) (hClb : 0 ≤ Clb)
    (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0)
    (hRℓ : R.ℓ = D.ℓ) (hRA : R.A = D.A) (hRρ : R.ρ = D.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N)
    (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : (∀ jD ≤ Nh, InD3 ((L : ℝ) ^ 2) D.κ D.cm D.cT D.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ jD)))
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
    let t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀
    let r := D.c * (t j).1
    let oj := sO 2 L r mV mW + Clo * ((L : ℝ) ^ 2 * sO 2 L r mV mW)
    (∀ b' ∈ blockIdx (L := L) (N := N) j,
      Tj 2 (L : ℝ) (j + 1) (histS (R.withMsq m) (j + 1) t)
          (WpO P j (histCovO (R.withMsq m) t j) (hVR (R.withMsq m) P j₀ o₀ t j)
            (hWR (R.withMsq m) P j₀ o₀ t j) b' : SA .two (Lam 2 L N)).e ≤
        ENNReal.ofReal (cWblk 2 L Clb * r) ∧
      Tj 2 (L : ℝ) (j + 1) (histS (R.withMsq m) (j + 1) t)
          (WpO P j (histCovO (R.withMsq m) t j) (hVR (R.withMsq m) P j₀ o₀ t j)
            (hWR (R.withMsq m) P j₀ o₀ t j) b' : SA .two (Lam 2 L N)).ab ≤
        ENNReal.ofReal (Ma * Mb * oj) ∧
      Tj 2 (L : ℝ) (j + 1) (histS (R.withMsq m) (j + 1) t)
          (LSO P j (histCovO (R.withMsq m) t j) (hVR (R.withMsq m) P j₀ o₀ t j)
            (hWR (R.withMsq m) P j₀ o₀ t j) b' : SA .two (Lam 2 L N)).ab ≤
        ENNReal.ofReal (Ma * Mb * (Clo * ((L : ℝ) ^ 2 * sO 2 L r mV mW)))) ∧
    (∀ c' ∈ blockIdx (L := L) (N := N) (j + 1),
      Tj 2 (L : ℝ) (j + 1) (histS (R.withMsq m) (j + 1) t)
          ((Wnext2O P j (histCovO (R.withMsq m) t j) (hVR (R.withMsq m) P j₀ o₀ t j)
              (hWR (R.withMsq m) P j₀ o₀ t j) c' -
            ∑ b' ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
              WpO P j (histCovO (R.withMsq m) t j) (hVR (R.withMsq m) P j₀ o₀ t j)
                (hWR (R.withMsq m) P j₀ o₀ t j) b' : OE .two (Lam 2 L N)) :
              SA .two (Lam 2 L N)).ab ≤
        ENNReal.ofReal (Ma * Mb * ((L : ℝ) ^ 2 * oj * ((1 + cWblk 2 L Clb * r) ^ (L ^ 2) - 1)))) := by
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
  have ht := inDh_rg_of_D R' F1 hadm j hj.le
  have H' := wpo_hist_ab_le R' hWB hClo hClb hSB' hV hm1 hβ0 (by norm_num : (1 / 2 : ℝ) ≤ 1) H
    (by rw [hcR]; exact D.hcε) P hMa hMb o₀ h0 hl0 hs0 ha0 (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
    j hjj hj ht mV mW hmV hmW hVo hWo
  simp only [hcR] at H'
  exact H'


set_option maxHeartbeats 4000000 in
/-- **`wpo_hist_off` along admissible trajectories**: off the lattice blocks `𝒲'_{j+1}(B) = 0`. -/
theorem MasterCore.wpoOffD6 {L : ℕ} [NeZero L] (D : MasterCore L)
    (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0)
    (hRℓ : R.ℓ = D.ℓ) (hRA : R.A = D.A) (hRρ : R.ρ = D.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N)
    (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : (∀ jD ≤ Nh, InD3 ((L : ℝ) ^ 2) D.κ D.cm D.cT D.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ jD)))
    (P : Obs2.ObsPts 2 L N) {j₀ : ℕ} (o₀ : ObsSt .two L N) (h0 : o₀.IsObs)
    (ha0 : ObsAnchInv P j₀ o₀) (j : ℕ) (hjj : j₀ ≤ j) (hj : j < Nh)
    {b' : Fin 2 → ℕ} (hb' : b' ∉ blockIdx (L := L) (N := N) j) :
    (WpO P j (histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j)
        (hVR (R.withMsq m) P j₀ o₀ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j)
        (hWR (R.withMsq m) P j₀ o₀ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j) b' :
        SA .two (Lam 2 L N)).e = 0 ∧
    (WpO P j (histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j)
        (hVR (R.withMsq m) P j₀ o₀ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j)
        (hWR (R.withMsq m) P j₀ o₀ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j) b' :
        SA .two (Lam 2 L N)).ab = 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hCN⟩ := id D.hC2
  set R' := R.withMsq m with hR'
  obtain ⟨H, hm1, F1⟩ := D.hXm N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm
  obtain ⟨hV, -⟩ := (hCN N R hP hi0 hRℓ hRA hRρ hN Nh hNh).2.2.2.2.2.2.2.2.2 m hm
  have hRA' : R'.A = D.A := hRA
  have hSB' : StepBounds L R'.A D.C₀x D.ηx D.εsx D.CKx D.C₂x D.CDx D.Cqx D.Clx D.cSx := by
    rw [hRA']; exact D.hSBx
  have hβ2 := betaL_ge (by have := D.hL49; omega : 8 ≤ L)
  have hβ0 : 0 ≤ betaL L := by linarith
  have ht := inDh_rg_of_D R' F1 hadm j hj.le
  exact wpo_hist_off R' hSB' hV hm1 hβ0 (by norm_num : (1 / 2 : ℝ) ≤ 1) H P o₀ h0 ha0
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j hjj hj ht (by have := D.hL49; omega) hb'


set_option maxHeartbeats 4000000 in
/-- **`pairWSizes_MFD6` at given constants**. -/
theorem pairWSizes_MFatD6 {L : ℕ} [NeZero L] (M : MasterFacts L) {Clo Clb : ℝ}
    (hWB : WpOBoundsAB L Clo Clb) (hClo : 0 ≤ Clo) (hClb : 0 ≤ Clb) {C₁k C₁w : ℝ} (hC₁w : 0 ≤ C₁w)
    (hAH : M.core.AbwHistPD6 C₁k C₁w) :
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
    ∀ m ∈ mRange L N, ∀ b μ₀,
      (∀ jD ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ jD)) →
    ∀ (lam : ℕ → ℂ) (cu mbar : ℝ), PairUnitSeed R Nh m b μ₀ lam cu → 0 < mbar →
      8 * (cu * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) ≤ (4 * C₁w + 1) * mbar →
    ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∀ n, n ≤ Nh + 1 → PairVB R m b μ₀ lam x mbar n →
    ∀ i, Obs.coal L (0 : Lam 2 L N) x ≤ i → i < n → i < Nh →
      let t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀
      let C := histCovO (R.withMsq m) t
      let V := hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oRed R m b μ₀ dxStd x) t
      let W := hWR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oRed R m b μ₀ dxStd x) t
      let r := M.core.c * (t i).1
      let sOi := sO 2 L r mbar ((4 * C₁w + 1) * r * mbar)
      let oi := sOi + Clo * ((L : ℝ) ^ 2 * sOi)
      let Mab := vwA R m b μ₀ x i * vwB R m b μ₀ lam x
      (∀ b' ∈ blockIdx (L := L) (N := N) i,
        Tj 2 (L : ℝ) (i + 1) (histS (R.withMsq m) (i + 1) t)
            (WpO (ptsX x) i (C i) (V i) (W i) b' : SA .two (Lam 2 L N)).e ≤
          ENNReal.ofReal (cWblk 2 L Clb * r) ∧
        Tj 2 (L : ℝ) (i + 1) (histS (R.withMsq m) (i + 1) t)
            (WpO (ptsX x) i (C i) (V i) (W i) b' : SA .two (Lam 2 L N)).ab ≤
          ENNReal.ofReal (Mab * oi) ∧
        Tj 2 (L : ℝ) (i + 1) (histS (R.withMsq m) (i + 1) t)
            (LSO (ptsX x) i (C i) (V i) (W i) b' : SA .two (Lam 2 L N)).ab ≤
          ENNReal.ofReal (Mab * (Clo * ((L : ℝ) ^ 2 * sOi)))) ∧
      (∀ c' ∈ blockIdx (L := L) (N := N) (i + 1),
        Tj 2 (L : ℝ) (i + 1) (histS (R.withMsq m) (i + 1) t)
            ((Wnext2O (ptsX x) i (C i) (V i) (W i) c' -
              ∑ b' ∈ blocks i (blockSet (L := L) (N := N) (i + 1) c'),
                WpO (ptsX x) i (C i) (V i) (W i) b' : OE .two (Lam 2 L N)) :
                SA .two (Lam 2 L N)).ab ≤
          ENNReal.ofReal (Mab * ((L : ℝ) ^ 2 * oi * ((1 + cWblk 2 L Clb * r) ^ (L ^ 2) - 1)))) := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam cu mbar hU hmbar h8 x hx h1 hj
    n hn hVB i hi1 hin hiN
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  have hb : 0 < b := by
    have := (hadm 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  obtain ⟨hV, hVL, -, hRI⟩ := M.core.pairTrajD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  have hβr := pairBetaRatio_MFD M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm x
  have hβne : ∀ k ≤ Nh, hBeta R m b μ₀ x k ≠ 0 ∧ hBeta R m b μ₀ x (k + 1) ≠ 0 := by
    obtain ⟨q, -, -, hl⟩ :=
      (M.loopD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) (zV b)).2.2
    intro k hk
    obtain ⟨a1, a2, -, -⟩ := hBeta_rel_of R hNh hb x
      (M.relGD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) (zV b) (zV_mua_ne hb))
      (fun k hk => (hl k hk).1)
      (M.topD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x)).1 k hk
    exact ⟨a1, a2⟩
  have hρ0 : 0 ≤ (R.withMsq m).ρ := (hV 0 (by omega) |>.toValidCore).2.2.2.1
  have hρ8 : (R.withMsq m).ρ ≤ 1 / 8 := ((hRI 0 (by omega)).1).2.2.2.2.1
  have hs : ∀ k, 0 < histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) := fun k =>
    histS_pos' (R.withMsq m) hρ0 hρ8 (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k
  have hvwA : ∀ k ≤ Nh + 1, vwA R m b μ₀ x k = 2 * histS (R.withMsq m) k
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * ‖hBeta R m b μ₀ x k‖ := by
    intro k hk
    have hne : hBeta R m b μ₀ x k ≠ 0 := by
      rcases Nat.lt_or_ge k (Nh + 1) with h | h
      · exact (hβne k (by omega)).1
      · rw [show k = Nh + 1 by omega]
        exact (hβne Nh le_rfl).2
    unfold vwA; rw [if_neg hne]
  have hMa : ∀ k, 0 < vwA R m b μ₀ x k := fun k => by
    unfold vwA
    split_ifs with h
    · norm_num
    · have := hs k; have := norm_pos_iff.2 h; positivity
  -- the seed
  obtain ⟨hpa, hpb, hK⟩ := pairSeed_hK0D M.pairInitWD R hP hi0 hRℓ hRA hRρ hN2 hNh hm hadm x h1 hj
  have hU' := hU x hx h1 hj
  have hg0 : 0 ≤ ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j).1 := (hadm j hj).1.le
  have hwB0 : 0 ≤ vwB R m b μ₀ lam x := mul_nonneg (norm_nonneg _) hg0
  have hwB : 0 < vwB R m b μ₀ lam x := by
    rcases hwB0.lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hU'; linarith
  have hcu : 0 < cu := by
    by_contra hc
    push Not at hc
    have : cu * vwB R m b μ₀ lam x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc hwB0
    linarith
  have hpaE : pM (R.withMsq m) (ptsX x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j =
      vwA R m b μ₀ x j := by
    rw [hvwA j (by omega), hBeta_eq_zV0 R m b μ₀ x h1]; rfl
  set k₀ := cu * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2) with hk₀d
  have hιA : 0 ≤ (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2) := by
    have := M.ιW_ge; have := M.core.hA2; positivity
  have hk₀ : 0 ≤ k₀ := mul_nonneg hcu.le hιA
  have hK0 : ∀ X, IsConn j X → ENNReal.ofReal ((R.withMsq m).A ^ (nb j X - 2 ^ 2)) *
      oTo (wM (vwA R m b μ₀ x j) (vwB R m b μ₀ lam x)) j
        (histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((oRed R m b μ₀ (dxStd (L := L) (N := N)) x).K X) ≤ ENNReal.ofReal k₀ := by
    intro X hX
    have hab : (oRed R m b μ₀ (dxStd (L := L) (N := N)) x).K X ∈
        (abSub : Subalgebra ℂ (OE .two (Lam 2 L N))) :=
      (PtCorr2.obsAbInv_redSt _ _ _ _ _ _ _ _ _ _).K X hX
    rw [oTo_wM_rescale (hMa j) hwB hpa hpb j _ hab, hpaE, mul_left_comm]
    have hr : vwA R m b μ₀ x j * pM (R.withMsq m) (ptsS x) (zV0 b)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j /
        (vwA R m b μ₀ x j * vwB R m b μ₀ lam x) ≤ cu := by
      rw [mul_div_mul_left _ _ (hMa j).ne', div_le_iff₀ hwB]; linarith
    calc ENNReal.ofReal (vwA R m b μ₀ x j * pM (R.withMsq m) (ptsS x) (zV0 b)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j /
          (vwA R m b μ₀ x j * vwB R m b μ₀ lam x)) *
          (ENNReal.ofReal ((R.withMsq m).A ^ (nb j X - 2 ^ 2)) *
            oTo (wM (vwA R m b μ₀ x j) (pM (R.withMsq m) (ptsS x) (zV0 b)
              (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j)) j
              (histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
              ((oRed R m b μ₀ (dxStd (L := L) (N := N)) x).K X))
        ≤ ENNReal.ofReal cu * ENNReal.ofReal ((2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) := by
          gcongr
          rw [← hpaE]; exact hK X hX
      _ = ENNReal.ofReal k₀ := by rw [← ENNReal.ofReal_mul hcu.le]
  -- the initial state
  have hRd := pairSectRed_of R m hV hVL b μ₀ (pairDCov_std (L := L) (N := N) Nh)
  obtain ⟨hobs, hloc0, -, -⟩ := hRd x hx h1 hj
  have hanc := pairAnchR_oRed R Nh m b μ₀ x hx h1 hj
  have hsymj : PtCorr2.ObsSymInv j (oRed R m b μ₀ dxStd x) :=
    PtCorr2.obsSymInv_redSt (hRI j hj).1 (hRI j hj).2 (rawD_mem (R.withMsq m) _ _)
      (rawK_mem (R.withMsq m) _ _)
      (PtCorr2.obsSymInv_hist (R.withMsq m) (ptsX x) _ (PtCorr2.obsSymInv_init .two (zV b) (ptsX x))
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j fun i hi => (hRI i (by omega)))
  -- the doubling of the weights
  have hdbl : ∀ k, j ≤ k → k < n → vwA R m b μ₀ x k ≤ 2 * vwA R m b μ₀ x (k + 1) := by
    intro k hk hkn
    rw [hvwA k (by omega), hvwA (k + 1) (by omega)]
    have h1' := histS_sq_ratio (R.withMsq m) hρ0 hρ8 (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k
    have h2' := hβr k (by omega)
    have h3 := sq_nonneg (histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
    have h4 := norm_nonneg (hBeta R m b μ₀ x (k + 1))
    have h5 : histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
        ‖hBeta R m b μ₀ x k‖ ≤
        (6 / 5 * histS (R.withMsq m) (k + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2) *
          (64 / 49 * ‖hBeta R m b μ₀ x (k + 1)‖) :=
      mul_le_mul h1' h2' (norm_nonneg _) (by positivity)
    nlinarith [mul_nonneg (sq_nonneg (histS (R.withMsq m) (k + 1)
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))) h4]
  -- the `𝒲` chain up to `i`
  obtain ⟨hcR, hAH'⟩ := hAH N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  have hm' : ∀ k, j ≤ k → k < i → vwA R m b μ₀ x k * (fun _ : ℕ => vwB R m b μ₀ lam x) k /
      (vwA R m b μ₀ x j * (fun _ : ℕ => vwB R m b μ₀ lam x) j) * (fun _ : ℕ => mbar) k ≤
      2 * (vwA R m b μ₀ x (k + 1) * (fun _ : ℕ => vwB R m b μ₀ lam x) (k + 1) /
        (vwA R m b μ₀ x j * (fun _ : ℕ => vwB R m b μ₀ lam x) j) * (fun _ : ℕ => mbar) (k + 1)) := by
    intro k hk hki
    have h := hdbl k hk (by omega)
    have hpos : 0 ≤ vwB R m b μ₀ lam x * mbar / (vwA R m b μ₀ x j * vwB R m b μ₀ lam x) := by
      have := hMa j; positivity
    have e1 : vwA R m b μ₀ x k * vwB R m b μ₀ lam x / (vwA R m b μ₀ x j * vwB R m b μ₀ lam x) * mbar =
        vwA R m b μ₀ x k * (vwB R m b μ₀ lam x * mbar / (vwA R m b μ₀ x j * vwB R m b μ₀ lam x)) := by
      ring
    have e2 : 2 * (vwA R m b μ₀ x (k + 1) * vwB R m b μ₀ lam x /
        (vwA R m b μ₀ x j * vwB R m b μ₀ lam x) * mbar) =
        2 * vwA R m b μ₀ x (k + 1) * (vwB R m b μ₀ lam x * mbar /
          (vwA R m b μ₀ x j * vwB R m b μ₀ lam x)) := by ring
    show vwA R m b μ₀ x k * vwB R m b μ₀ lam x / (vwA R m b μ₀ x j * vwB R m b μ₀ lam x) * mbar ≤
      2 * (vwA R m b μ₀ x (k + 1) * vwB R m b μ₀ lam x /
        (vwA R m b μ₀ x j * vwB R m b μ₀ lam x) * mbar)
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right h hpos
  have hVo : ∀ k, j ≤ k → k < i → ∀ b' ∈ blockIdx (L := L) (N := N) k,
      oTo (wM (vwA R m b μ₀ x k) ((fun _ : ℕ => vwB R m b μ₀ lam x) k)) k
        (histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((obsHistFrom (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) k
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).V b') ≤ ENNReal.ofReal ((fun _ : ℕ => mbar) k) :=
    fun k hk hki b' hb' => hVB k hk (by omega) b' hb'
  have hW0 : ∀ b' ∈ blockIdx (L := L) (N := N) j,
      oTo (wM (vwA R m b μ₀ x j) ((fun _ : ℕ => vwB R m b μ₀ lam x) j)) j
        (histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((oRed R m b μ₀ dxStd x).W b') ≤
      ENNReal.ofReal ((4 * C₁w + 1) * (cR (R.withMsq m) ((L : ℝ) ^ 2) M.core.cm M.core.C₂x *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1) * (fun _ : ℕ => mbar) j) := fun b' _ => by
    show oTo _ _ _ (0 : OE .two (Lam 2 L N)) ≤ _
    rw [oTo_zero']; exact bot_le
  have hWi := (hAH' (ptsX x) (vwA R m b μ₀ x) (fun _ => vwB R m b μ₀ lam x) hMa (fun _ => hwB) j
    (oRed R m b μ₀ dxStd x) hobs hloc0 hsymj hanc i hiN.le (fun _ => mbar) (fun _ => hmbar) hm'
    hVo hW0 k₀ hk₀ hK0 (by rw [one_mul]; exact h8) i hi1 le_rfl).2.1
  have hWo : ∀ b' ∈ blockIdx (L := L) (N := N) i,
      oTo (wM (vwA R m b μ₀ x i) (vwB R m b μ₀ lam x)) i
        (histS (R.withMsq m) i (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((obsHistFrom (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) i
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).W b') ≤
      ENNReal.ofReal ((4 * C₁w + 1) * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ i).1) *
        mbar) := fun b' hb' => by
    have h := hWi b' hb'
    simp only [hcR] at h
    exact h
  have hr0 : 0 ≤ M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ i).1 := by
    have h1 := (hadm i hiN.le).1.le
    have h2 : 0 ≤ M.core.c := by
      rw [← hcR]; unfold cR cV cW cZ
      obtain ⟨H, -, -⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm
      have := H.hcmu; have := H.hC₂; positivity
    exact mul_nonneg h2 h1
  exact M.core.wpoHistD6 hWB hClo hClb N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x)
    (hMa i) hwB (oRed R m b μ₀ dxStd x) hobs hloc0 hsymj hanc i hi1 hiN mbar _ hmbar.le
    (by have := hC₁w; positivity) (fun b' hb' => hVB i hi1 hin b' hb') hWo


set_option maxHeartbeats 4000000 in
/-- **`pairKSSizes_MFD6` at given constants**. -/
theorem pairKSSizes_MFatD6 {L : ℕ} [NeZero L] (M : MasterFacts L) {C₁k C₁w : ℝ} (hC₁k : 0 ≤ C₁k)
    (hC₁w : 0 ≤ C₁w) (hAH : M.core.AbwHistPD6 C₁k C₁w) :
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
    ∀ m ∈ mRange L N, ∀ b μ₀,
      (∀ jD ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ jD)) →
    ∀ (lam : ℕ → ℂ) (cu mbar : ℝ), PairUnitSeed R Nh m b μ₀ lam cu → 0 < mbar →
      8 * (cu * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) ≤ (4 * C₁w + 1) * mbar →
    ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∀ n, n ≤ Nh + 1 → PairVB R m b μ₀ lam x mbar n →
    ∀ i, Obs.coal L (0 : Lam 2 L N) x ≤ i → i < n → i ≤ Nh →
      let t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀
      let C := histCovO (R.withMsq m) t
      let V := hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oRed R m b μ₀ dxStd x) t
      let W := hWR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oRed R m b μ₀ dxStd x) t
      let K := hKR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oRed R m b μ₀ dxStd x) t
      (∀ Y, IsSmall i Y → Tj 2 (L : ℝ) i (histS (R.withMsq m) i t) (K i Y : SA .two (Lam 2 L N)).ab ≤
          ENNReal.ofReal (kszQ R M C₁k C₁w mbar cu m b μ₀ lam x i)) ∧
      (i < Nh → ∀ b' ∈ blockIdx (L := L) (N := N) i,
        Tj 2 (L : ℝ) (i + 1) (histS (R.withMsq m) (i + 1) t)
            (SXO i (C i) (V i) (W i) (Step2.Bp (L := L) (N := N) i b') : SA .two (Lam 2 L N)).ab ≤
          ENNReal.ofReal (kszS R M C₁w mbar m b μ₀ lam x i) ∧
        (¬ (Step2.Bp (L := L) (N := N) i b' ∩ (ptsX x).pts).Nonempty →
          (SXO i (C i) (V i) (W i) (Step2.Bp (L := L) (N := N) i b') : SA .two (Lam 2 L N)).ab = 0)) := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam cu mbar hU hmbar h8 x hx h1 hj
    n hn hVB i hi1 hin hiN
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  have hb : 0 < b := by
    have := (hadm 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  obtain ⟨hV, hVL, -, hRI⟩ := M.core.pairTrajD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  have hβr := pairBetaRatio_MFD M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm x
  have hβne : ∀ k ≤ Nh, hBeta R m b μ₀ x k ≠ 0 ∧ hBeta R m b μ₀ x (k + 1) ≠ 0 := by
    obtain ⟨q, -, -, hl⟩ :=
      (M.loopD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) (zV b)).2.2
    intro k hk
    obtain ⟨a1, a2, -, -⟩ := hBeta_rel_of R hNh hb x
      (M.relGD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) (zV b) (zV_mua_ne hb))
      (fun k hk => (hl k hk).1)
      (M.topD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x)).1 k hk
    exact ⟨a1, a2⟩
  have hρ0 : 0 ≤ (R.withMsq m).ρ := (hV 0 (by omega) |>.toValidCore).2.2.2.1
  have hρ8 : (R.withMsq m).ρ ≤ 1 / 8 := ((hRI 0 (by omega)).1).2.2.2.2.1
  have hs : ∀ k, 0 < histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) := fun k =>
    histS_pos' (R.withMsq m) hρ0 hρ8 (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k
  have hvwA : ∀ k ≤ Nh + 1, vwA R m b μ₀ x k = 2 * histS (R.withMsq m) k
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * ‖hBeta R m b μ₀ x k‖ := by
    intro k hk
    have hne : hBeta R m b μ₀ x k ≠ 0 := by
      rcases Nat.lt_or_ge k (Nh + 1) with h | h
      · exact (hβne k (by omega)).1
      · rw [show k = Nh + 1 by omega]
        exact (hβne Nh le_rfl).2
    unfold vwA; rw [if_neg hne]
  have hMa : ∀ k, 0 < vwA R m b μ₀ x k := fun k => by
    unfold vwA
    split_ifs with h
    · norm_num
    · have := hs k; have := norm_pos_iff.2 h; positivity
  -- the seed
  obtain ⟨hpa, hpb, hK⟩ := pairSeed_hK0D M.pairInitWD R hP hi0 hRℓ hRA hRρ hN2 hNh hm hadm x h1 hj
  have hU' := hU x hx h1 hj
  have hg0 : 0 ≤ ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j).1 := (hadm j hj).1.le
  have hwB0 : 0 ≤ vwB R m b μ₀ lam x := mul_nonneg (norm_nonneg _) hg0
  have hwB : 0 < vwB R m b μ₀ lam x := by
    rcases hwB0.lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hU'; linarith
  have hcu : 0 < cu := by
    by_contra hc
    push Not at hc
    have : cu * vwB R m b μ₀ lam x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc hwB0
    linarith
  have hpaE : pM (R.withMsq m) (ptsX x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j =
      vwA R m b μ₀ x j := by
    rw [hvwA j (by omega), hBeta_eq_zV0 R m b μ₀ x h1]; rfl
  set k₀ := cu * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2) with hk₀d
  have hιA : 0 ≤ (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2) := by
    have := M.ιW_ge; have := M.core.hA2; positivity
  have hk₀ : 0 ≤ k₀ := mul_nonneg hcu.le hιA
  have hK0 : ∀ X, IsConn j X → ENNReal.ofReal ((R.withMsq m).A ^ (nb j X - 2 ^ 2)) *
      oTo (wM (vwA R m b μ₀ x j) (vwB R m b μ₀ lam x)) j
        (histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((oRed R m b μ₀ (dxStd (L := L) (N := N)) x).K X) ≤ ENNReal.ofReal k₀ := by
    intro X hX
    have hab : (oRed R m b μ₀ (dxStd (L := L) (N := N)) x).K X ∈
        (abSub : Subalgebra ℂ (OE .two (Lam 2 L N))) :=
      (PtCorr2.obsAbInv_redSt _ _ _ _ _ _ _ _ _ _).K X hX
    rw [oTo_wM_rescale (hMa j) hwB hpa hpb j _ hab, hpaE, mul_left_comm]
    have hr : vwA R m b μ₀ x j * pM (R.withMsq m) (ptsS x) (zV0 b)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j /
        (vwA R m b μ₀ x j * vwB R m b μ₀ lam x) ≤ cu := by
      rw [mul_div_mul_left _ _ (hMa j).ne', div_le_iff₀ hwB]; linarith
    calc ENNReal.ofReal (vwA R m b μ₀ x j * pM (R.withMsq m) (ptsS x) (zV0 b)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j /
          (vwA R m b μ₀ x j * vwB R m b μ₀ lam x)) *
          (ENNReal.ofReal ((R.withMsq m).A ^ (nb j X - 2 ^ 2)) *
            oTo (wM (vwA R m b μ₀ x j) (pM (R.withMsq m) (ptsS x) (zV0 b)
              (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j)) j
              (histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
              ((oRed R m b μ₀ (dxStd (L := L) (N := N)) x).K X))
        ≤ ENNReal.ofReal cu * ENNReal.ofReal ((2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) := by
          gcongr
          rw [← hpaE]; exact hK X hX
      _ = ENNReal.ofReal k₀ := by rw [← ENNReal.ofReal_mul hcu.le]
  -- the initial state
  have hRd := pairSectRed_of R m hV hVL b μ₀ (pairDCov_std (L := L) (N := N) Nh)
  obtain ⟨hobs, hloc0, -, -⟩ := hRd x hx h1 hj
  have hanc := pairAnchR_oRed R Nh m b μ₀ x hx h1 hj
  have hsymj : PtCorr2.ObsSymInv j (oRed R m b μ₀ dxStd x) :=
    PtCorr2.obsSymInv_redSt (hRI j hj).1 (hRI j hj).2 (rawD_mem (R.withMsq m) _ _)
      (rawK_mem (R.withMsq m) _ _)
      (PtCorr2.obsSymInv_hist (R.withMsq m) (ptsX x) _ (PtCorr2.obsSymInv_init .two (zV b) (ptsX x))
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j fun i hi => (hRI i (by omega)))
  -- the doubling of the weights
  have hdbl : ∀ k, j ≤ k → k < n → vwA R m b μ₀ x k ≤ 2 * vwA R m b μ₀ x (k + 1) := by
    intro k hk hkn
    rw [hvwA k (by omega), hvwA (k + 1) (by omega)]
    have h1' := histS_sq_ratio (R.withMsq m) hρ0 hρ8 (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k
    have h2' := hβr k (by omega)
    have h3 := sq_nonneg (histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
    have h4 := norm_nonneg (hBeta R m b μ₀ x (k + 1))
    have h5 : histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
        ‖hBeta R m b μ₀ x k‖ ≤
        (6 / 5 * histS (R.withMsq m) (k + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2) *
          (64 / 49 * ‖hBeta R m b μ₀ x (k + 1)‖) :=
      mul_le_mul h1' h2' (norm_nonneg _) (by positivity)
    nlinarith [mul_nonneg (sq_nonneg (histS (R.withMsq m) (k + 1)
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))) h4]
  -- the `𝒲` chain up to `i`
  obtain ⟨hcR, hAH'⟩ := hAH N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  have hm' : ∀ k, j ≤ k → k < i → vwA R m b μ₀ x k * (fun _ : ℕ => vwB R m b μ₀ lam x) k /
      (vwA R m b μ₀ x j * (fun _ : ℕ => vwB R m b μ₀ lam x) j) * (fun _ : ℕ => mbar) k ≤
      2 * (vwA R m b μ₀ x (k + 1) * (fun _ : ℕ => vwB R m b μ₀ lam x) (k + 1) /
        (vwA R m b μ₀ x j * (fun _ : ℕ => vwB R m b μ₀ lam x) j) * (fun _ : ℕ => mbar) (k + 1)) := by
    intro k hk hki
    have h := hdbl k hk (by omega)
    have hpos : 0 ≤ vwB R m b μ₀ lam x * mbar / (vwA R m b μ₀ x j * vwB R m b μ₀ lam x) := by
      have := hMa j; positivity
    have e1 : vwA R m b μ₀ x k * vwB R m b μ₀ lam x / (vwA R m b μ₀ x j * vwB R m b μ₀ lam x) * mbar =
        vwA R m b μ₀ x k * (vwB R m b μ₀ lam x * mbar / (vwA R m b μ₀ x j * vwB R m b μ₀ lam x)) := by
      ring
    have e2 : 2 * (vwA R m b μ₀ x (k + 1) * vwB R m b μ₀ lam x /
        (vwA R m b μ₀ x j * vwB R m b μ₀ lam x) * mbar) =
        2 * vwA R m b μ₀ x (k + 1) * (vwB R m b μ₀ lam x * mbar /
          (vwA R m b μ₀ x j * vwB R m b μ₀ lam x)) := by ring
    show vwA R m b μ₀ x k * vwB R m b μ₀ lam x / (vwA R m b μ₀ x j * vwB R m b μ₀ lam x) * mbar ≤
      2 * (vwA R m b μ₀ x (k + 1) * vwB R m b μ₀ lam x /
        (vwA R m b μ₀ x j * vwB R m b μ₀ lam x) * mbar)
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right h hpos
  have hVo : ∀ k, j ≤ k → k < i → ∀ b' ∈ blockIdx (L := L) (N := N) k,
      oTo (wM (vwA R m b μ₀ x k) ((fun _ : ℕ => vwB R m b μ₀ lam x) k)) k
        (histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((obsHistFrom (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) k
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).V b') ≤ ENNReal.ofReal ((fun _ : ℕ => mbar) k) :=
    fun k hk hki b' hb' => hVB k hk (by omega) b' hb'
  have hW0 : ∀ b' ∈ blockIdx (L := L) (N := N) j,
      oTo (wM (vwA R m b μ₀ x j) ((fun _ : ℕ => vwB R m b μ₀ lam x) j)) j
        (histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((oRed R m b μ₀ dxStd x).W b') ≤
      ENNReal.ofReal ((4 * C₁w + 1) * (cR (R.withMsq m) ((L : ℝ) ^ 2) M.core.cm M.core.C₂x *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1) * (fun _ : ℕ => mbar) j) := fun b' _ => by
    show oTo _ _ _ (0 : OE .two (Lam 2 L N)) ≤ _
    rw [oTo_zero']; exact bot_le
  have hWi := (hAH' (ptsX x) (vwA R m b μ₀ x) (fun _ => vwB R m b μ₀ lam x) hMa (fun _ => hwB) j
    (oRed R m b μ₀ dxStd x) hobs hloc0 hsymj hanc i hiN (fun _ => mbar) (fun _ => hmbar) hm'
    hVo hW0 k₀ hk₀ hK0 (by rw [one_mul]; exact h8) i hi1 le_rfl)
  obtain ⟨-, hWi', hKi'⟩ := hWi
  have hcR' := hcR
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  refine ⟨fun Y hY => ?_, fun hiN' b' hb' => ?_⟩
  · have hKs := M.core.vhistKD6 N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) (hMa i) hwB
      (oRed R m b μ₀ dxStd x) hloc0 hsymj hanc i hi1 hiN _ hKi' Y hY
    refine hKs.trans (ENNReal.ofReal_le_ofReal ?_)
    unfold kszQ kszK
    have hA : (R.withMsq m).A = M.core.A := hRA
    simp only [hA, hcR']
    have h1 := hMa i
    have h2 := hMa j
    set KK := kseqF (8 * (kθ0 L M.core.A M.core.C₀a M.core.ηa + C₁k * (2 + 2 * (8 * cx M.core.κ M.core.cT) + 1) *
      (M.core.c * M.core.ε)))
      (kB (kθ0 L M.core.A M.core.C₀a M.core.ηa) C₁k (8 * cx M.core.κ M.core.cT))
      (fun i => M.core.c * (t i).1)
      (fun i => (4 * C₁w + 1) * (vwA R m b μ₀ x i * vwB R m b μ₀ lam x /
        (vwA R m b μ₀ x j * vwB R m b μ₀ lam x) * mbar)) j
      (cu * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) i with hKK
    have e : vwA R m b μ₀ x i * vwB R m b μ₀ lam x * (8 * (KK / (vwA R m b μ₀ x i *
        vwB R m b μ₀ lam x / (vwA R m b μ₀ x j * vwB R m b μ₀ lam x)))) =
        vwA R m b μ₀ x j * vwB R m b μ₀ lam x * (8 * KK) := by
      field_simp
    rw [e]
    have hjB : 0 ≤ vwA R m b μ₀ x j * vwB R m b μ₀ lam x := mul_nonneg h2.le hwB.le
    exact mul_le_mul_of_nonneg_left (by linarith [le_max_left KK 0]) hjB
  · have hWo : ∀ b' ∈ blockIdx (L := L) (N := N) i,
        oTo (wM (vwA R m b μ₀ x i) (vwB R m b μ₀ lam x)) i (histS (R.withMsq m) i t)
          ((obsHistFrom (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) i t).W b') ≤
        ENNReal.ofReal ((4 * C₁w + 1) * (M.core.c * (t i).1) * mbar) := fun b' hb' => by
      have h := hWi' b' hb'
      simp only [hcR'] at h
      exact h
    have hr0 : 0 ≤ M.core.c * (t i).1 := by
      have h1 := (hadm i hiN).1.le
      have h2 : 0 ≤ M.core.c := by
        rw [← hcR']; unfold cR cV cW cZ
        obtain ⟨H, -, -⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm
        have := H.hcmu; have := H.hC₂; positivity
      exact mul_nonneg h2 h1
    obtain ⟨hS1, hS2⟩ := M.core.vhistSD6 N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x)
      (hMa i) hwB (oRed R m b μ₀ dxStd x) hobs hloc0 hsymj hanc i hi1 hiN' mbar _ hmbar.le
      (by have := hC₁w; positivity) (fun b' hb' => hVB i hi1 hin b' hb') hWo b' hb'
    exact ⟨hS1.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)), hS2⟩


set_option maxHeartbeats 8000000 in
/-- **`pairESizes3_MFD6` at given constants**. -/
theorem pairESizes3_MFatD6 {L : ℕ} [NeZero L] (M : MasterFacts L) {Clo Clb : ℝ}
    (hWB : WpOBoundsAB L Clo Clb) (hClo : 0 ≤ Clo) (hClb : 0 ≤ Clb) {C₁k C₁w C₁k' C₁w' : ℝ}
    (hC₁k : 0 ≤ C₁k) (hC₁w : 0 ≤ C₁w) (hC₁w' : 0 ≤ C₁w') (hAH : M.core.AbwHistPD6 C₁k C₁w)
    (hAH' : M.core.AbwHistPD6 C₁k' C₁w') :
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
    ∀ m ∈ mRange L N, ∀ b μ₀,
      (∀ jD ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ jD)) →
    ∀ (lam : ℕ → ℂ) (cu cr mbar : ℝ), PairUnitSeed R Nh m b μ₀ lam cu → 0 < mbar →
      8 * (cu * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) ≤ (4 * C₁w + 1) * mbar →
      8 * (cu * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) ≤ (4 * C₁w' + 1) * mbar →
    ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∀ w : List (Dir 2), Obs2.pathEnd (0 : Lam 2 L N) w = x → (w.length : ℝ) ≤ 2 * sXp x →
      PairESizes3 R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) cr x (PairVB R m b μ₀ lam x mbar)
        (e6KQ R M C₁k C₁w mbar cu m b μ₀ lam x)
        (eszSe R M.core.c Clb m b μ₀) (eszSo R M.core.c C₁w' mbar Clo m b μ₀ lam x)
        (eszSw R M.core.c C₁w' mbar Clo Clb m b μ₀ lam x) (fun _ => 0)
        (e6MQ R M C₁k C₁w mbar cu m b μ₀ lam x) (e6MS R M C₁w mbar m b μ₀ lam x) (fun _ => 3)
        (e6Nu R M Nh m b μ₀) (e6Del R M C₁k C₁w mbar cu m b μ₀ lam x w.length)
        (e6E R M m b μ₀) (pdSz R m b μ₀ w (e6M4X R M C₁k C₁w mbar cu m b μ₀ lam x))
        (e6F R M C₁k C₁w mbar cu m b μ₀ lam x w.length)
        (eszWp R M.core.c C₁w' mbar Clo Clb m b μ₀ lam x) (tauSz R m b μ₀ M.core.ce) := by
  have hKS := pairKSSizes_MFatD6 M hC₁k hC₁w hAH
  have hW := pairWSizes_MFatD6 M hWB hClo hClb hC₁w' hAH'
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam cu cr mbar hU hmbar h8 h8' x hx
    h1 hj w hw hwl
  have hb : 0 < b := by
    have := (hadm 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hL49 : 49 ≤ L := M.core.hL49
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
  have hL0 : (0 : ℝ) < L := by linarith
  have hL8 : 2 ^ (2 + 3) + 8 * 2 < L := by omega
  obtain ⟨hV, hVL, hG, hRI⟩ := M.core.pairTrajD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  have hRd := pairSectRed_of R m hV hVL b μ₀ (pairDCov_std (L := L) (N := N) Nh)
  obtain ⟨hobs, hloc0, -, -⟩ := hRd x hx h1 hj
  have hanc := pairAnchR_oRed R Nh m b μ₀ x hx h1 hj
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  set t : Flow2.Hist.Seq (Xs (R.withMsq m)) := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with ht
  have hVab : PtCorr2.ObsVabInv (ptsX x) (oRed R m b μ₀ dxStd x) :=
    PtCorr2.obsVabInv_redSt (R.withMsq m) (ptsX x)
  have hsymj : PtCorr2.ObsSymInv j (oRed R m b μ₀ dxStd x) :=
    PtCorr2.obsSymInv_redSt (hRI j hj).1 (hRI j hj).2 (rawD_mem (R.withMsq m) _ _)
      (rawK_mem (R.withMsq m) _ _)
      (PtCorr2.obsSymInv_hist (R.withMsq m) (ptsX x) _ (PtCorr2.obsSymInv_init .two (zV b) (ptsX x))
        t j fun i hi => (hRI i (by omega)))
  have hsym : ∀ k, j ≤ k → k ≤ Nh → PtCorr2.ObsSymInv k (PtCorr2.obsHistFrom (R.withMsq m)
      (ptsX x) j (oRed R m b μ₀ dxStd x) k t) := fun k hk hkN =>
    PtCorr2.obsSymInv_histFrom' (R.withMsq m) (ptsX x) hsymj t hk fun i _ hi => hRI i (by omega)
  obtain ⟨hct, htad, hcg⟩ := M.tadD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  obtain ⟨q, -, -, hl⟩ :=
    (M.loopD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) (zV b)).2.2
  have htop := (M.topD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x)).1
  have hnn : ∀ k ≤ Nh, ‖nn2 R (ptsX x) (zV b) m b μ₀ k‖ ≤ 1 / 8 := fun k hk => by
    rcases Nat.lt_or_ge k Nh with h | h
    · exact (hl k h).1
    · rw [show k = Nh by omega]; exact htop.1
  have htadR : ∀ i k, Obs2.tadInc2 (ptsX x) (Obs2.histCovO (R.withMsq m) t)
      (PtCorr2.hVR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t) i k = tadO R m b μ₀ x i k :=
    fun i k => PtCorr2.tadInc2_hR_eq hobs (Obs2.obsInit_isObs .two (zV b) (ptsX x)) i k
  have hL2' : (2 : ℝ) / L ≤ 1 / 2 := by
    have hL4 : (4 : ℝ) ≤ L := by exact_mod_cast (show 4 ≤ L by omega)
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hβne : ∀ k ≤ Nh, hBeta R m b μ₀ x (k + 1) ≠ 0 := fun k hk =>
    (hBeta_rel_of R hNh hb x
      (M.relGD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) (zV b) (zV_mua_ne hb))
      (fun k hk => (hl k hk).1) htop k hk).2.1
  have hβp : ∀ k ≤ Nh, 0 < ‖hBeta R m b μ₀ x (k + 1)‖ := fun k hk => norm_pos_iff.2 (hβne k hk)
  have hρ0 : 0 ≤ (R.withMsq m).ρ := hVL.2.2.2.2.1
  have hρ8 : (R.withMsq m).ρ ≤ 1 / 8 := hVL.2.2.2.2.2.1
  have hs : ∀ k, 0 < histS (R.withMsq m) k t := fun k => histS_pos' (R.withMsq m) hρ0 hρ8 t k
  have hsq : ∀ k, histS (R.withMsq m) (k + 1) t ≤ 9 / 8 * histS (R.withMsq m) k t :=
    fun k => histS_succ_le_q (R.withMsq m) hρ0 hρ8 t k
  have hz0 : ∀ b', ((oRed R m b μ₀ dxStd x).V b' : SA .two (Lam 2 L N)).ab = 0 :=
    fun b' => oRed_V_ab_zero R m b μ₀ dxStd x b'
  have hab : (ptsX x).a ≠ (ptsX x).b := fun h => hx h.symm
  have hpe : Obs2.pathEnd (ptsX x).a w = (ptsX x).b := hw
  have hsX0 : 0 ≤ sXp x := Nat.cast_nonneg _
  have hc0 : 0 ≤ M.core.c := by
    obtain ⟨_, _, _, _, hAH⟩ := M.core.abwHistD6
    obtain ⟨hcR, -⟩ := hAH N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
    rw [← hcR]; unfold cR cV cW cZ
    obtain ⟨H, -, -⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm
    have := H.hcmu; have := H.hC₂; positivity
  have hg0 : ∀ i ≤ Nh, 0 ≤ (t i).1 := fun i hi => (hadm i hi).1.le
  have hmono := M.gmonoD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  have hgm : ∀ i l, i ≤ l → l ≤ Nh → (t i).1 ≤ (t l).1 := by
    intro i l hil hl'
    have key : ∀ n, i + n ≤ Nh → (t i).1 ≤ (t (i + n)).1 := by
      intro n
      induction n with
      | zero => intro _; exact le_rfl
      | succ n ih => intro hn; exact (ih (by omega)).trans (hmono (i + n) (by omega))
    have := key (l - i) (by omega)
    rwa [show i + (l - i) = l by omega] at this
  -- the sizes of the history
  set QK := kszQ R M C₁k C₁w mbar cu m b μ₀ lam x with hQKd
  set SS := kszS R M C₁w mbar m b μ₀ lam x with hSSd
  have hvwA := vwA_nonneg R m b μ₀ x
  have hvwB : 0 ≤ vwB R m b μ₀ lam x := mul_nonneg (norm_nonneg _) (hg0 j hj)
  have hQ0 : ∀ i, 0 ≤ QK i := fun i => by
    rw [hQKd]; unfold kszQ
    exact mul_nonneg (mul_nonneg (hvwA _) hvwB) (mul_nonneg (by norm_num) (le_max_right _ _))
  have hS0 : ∀ i, 0 ≤ SS i := fun i => by rw [hSSd]; unfold kszS; exact le_max_right _ _
  have hcS : ∀ i, ∀ b' ∈ blockIdx (L := L) (N := N) i,
      (open Classical in ((smallSets (d := 2) (L := L) (N := N) i).filter
        (fun X => blockSet i b' ⊆ X)).card : ℝ) ≤ (cSm2 : ℝ) :=
    fun i b' hb' => by exact_mod_cast cSm2_spec L N i b' hb'
  have hcN : ∀ i (y : Lam 2 L N) (s : Finset (Fin 2 → ℕ)), s ⊆ blockIdx (L := L) (N := N) i →
      ((s.filter (fun b' => y ∈ nbhd i (blockSet (L := L) (N := N) i b'))).card : ℝ) ≤ (cNb2 : ℝ) :=
    fun i y s hs' => by exact_mod_cast cNb2_spec L N i y s hs'
  -- the sequences are nonnegative
  have hGr0 : ∀ k, 0 ≤ e6Gr R M C₁k C₁w mbar cu m b μ₀ lam x k := fun k =>
    gradRHS_nonneg hL0 (Obs2.KG_nonneg 2 (Cc := Ccut2) (by norm_num)) (KM4_nonneg 2 (Cc := Ccut2)) hsX0
      hs (fun i => by have := hQ0 i; positivity) (fun i => by have := hS0 i; positivity) _ _
  have hM40 : ∀ k, 0 ≤ e6M4 R M C₁k C₁w mbar cu m b μ₀ lam x k := fun k =>
    m4RHS_nonneg hL0 (KM4_nonneg 2 (Cc := Ccut2)) hsX0
      hs (fun i => by have := hQ0 i; positivity) (fun i => by have := hS0 i; positivity) _ _
  have hLop0 : ∀ k ℓ', 0 ≤ ℓ' → 0 ≤ e6Lop R m b μ₀ x w.length k ℓ' := fun k ℓ' hℓ' => by
    unfold e6Lop; positivity
  intro n hn1 hn2 hVB hMs k hk1 hk2
  have hkN : k ≤ Nh := by omega
  have hKSi := fun i (hi1 : j ≤ i) (hin : i < n) =>
    hKS N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam cu mbar hU hmbar h8 x hx h1 hj n hn2
      hVB i hi1 hin (by omega)
  have hFi := fun i (hi1 : j ≤ i) (hiN : i < Nh) =>
    M.core.vhistFD6 N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x)
      (oRed R m b μ₀ dxStd x) hloc0 hsymj hanc i hi1 hiN
  -- the per-scale gradient and `M₄` sizes of the blocks at `k' < n`
  have hGr : ∀ k', j ≤ k' → k' < n → ∀ c ∈ blockIdx (L := L) (N := N) k',
      gradM4Sz {(ptsX x).a} (ptsX x).a (ptsX x).b ((L : ℝ) ^ k') (histS (R.withMsq m) k' t)
          (hVR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t k' c :
            SA .two (Lam 2 L N)).ab ≤ e6Gr R M C₁k C₁w mbar cu m b μ₀ lam x k' ∧
      ‖cfAB4 (ptsX x).a (ptsX x).b (hVR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t k' c :
          SA .two (Lam 2 L N)).ab‖ ≤ e6M4 R M C₁k C₁w mbar cu m b μ₀ lam x k' := by
    intro k' hk1' hk' c hc
    exact M.core.vhistGD6 N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) hab w hpe hwl
      (oRed R m b μ₀ dxStd x) hloc0 hsymj hanc hVab hz0 hk1' (by omega) QK SS hQ0 hS0
      (fun i hi hik Y hY => (hKSi i hi (by omega)).1 Y hY)
      (fun i hi hik b' hb' => ((hKSi i hi (by omega)).2 (by omega) b' hb').1) c hc
  -- the per-block bounds for every block (off the lattice blocks the `ab` part vanishes)
  have hGrA : ∀ k', j ≤ k' → k' < n → ∀ c,
      gradM4Sz {(ptsX x).a} (ptsX x).a (ptsX x).b ((L : ℝ) ^ k') (histS (R.withMsq m) k' t)
          (hVR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t k' c :
            SA .two (Lam 2 L N)).ab ≤ e6Gr R M C₁k C₁w mbar cu m b μ₀ lam x k' ∧
      ‖cfAB4 (ptsX x).a (ptsX x).b (hVR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t k' c :
          SA .two (Lam 2 L N)).ab‖ ≤ e6M4 R M C₁k C₁w mbar cu m b μ₀ lam x k' := by
    intro k' hk1' hk' c
    by_cases hc : c = blk k' (ptsX x).a ∨ c = blk k' (ptsX x).b
    · have hcI : c ∈ blockIdx (L := L) (N := N) k' := by
        rcases hc with rfl | rfl <;> exact mem_image_of_mem _ (mem_univ _)
      exact hGr k' hk1' hk' c hcI
    · push Not at hc
      rw [hVR_ab_anch (R.withMsq m) (ptsX x) j _ t hanc hk1' c hc.1 hc.2]
      refine ⟨?_, ?_⟩
      · have : gradM4Sz {(ptsX x).a} (ptsX x).a (ptsX x).b ((L : ℝ) ^ k')
            (histS (R.withMsq m) k' t) (0 : Alg 2 L N) = 0 := by
          unfold gradM4Sz; simp [cfAB2, cfAB4, coeff_zero]
        rw [this]; exact hGr0 k'
      · rw [show cfAB4 (ptsX x).a (ptsX x).b (0 : Alg 2 L N) = 0 from coeff_zero _, norm_zero]
        exact hM40 k'
  -- the `LopM4` term
  have hLop : ∀ k', k' ≤ Nh → ∀ ℓ', 0 ≤ ℓ' →
      gradM4Sz {(ptsX x).a} (ptsX x).a (ptsX x).b ((L : ℝ) ^ (k' + 1)) ℓ'
          (LopM4 (histCovO (R.withMsq m) t k') (ptsX x).a (ptsX x).b) ≤
        e6Lop R m b μ₀ x w.length k' ℓ' := by
    intro k' hk' ℓ' hℓ'
    obtain ⟨hc1, hc2, hc3⟩ := covDiff_le_path (hG k' hk') (ptsX x).a w
    rw [hpe] at hc2 hc3
    refine (gradM4Sz_LopM4_le (by positivity) hℓ' _ hab hc1 hc2 hc3).trans ?_
    have hE : eN1 {(ptsX x).a} (ptsX x).a (ptsX x).b ≤ 2 * sXp x := by
      have := eN1_single_le (d := 2) (ptsX x).a (ptsX x).b
      unfold sXp; push_cast at this ⊢; linarith
    have hE0 := eN1_nonneg {(ptsX x).a} (ptsX x).a (ptsX x).b
    have hg : eN1 {(ptsX x).a} (ptsX x).a (ptsX x).b * ℓ' * ((L : ℝ) ^ (k' + 1))⁻¹ ≤
        2 * sXp x * ℓ' * ((L : ℝ) ^ (k' + 1))⁻¹ := by gcongr
    have hg0 : 0 ≤ eN1 {(ptsX x).a} (ptsX x).a (ptsX x).b * ℓ' * ((L : ℝ) ^ (k' + 1))⁻¹ := by
      positivity
    unfold e6Lop
    have hd0 : 0 ≤ (w.length : ℝ) * (histS (R.withMsq m) k' t ^ 2 / (L : ℝ) ^ (k' + 1)) := by
      positivity
    gcongr
  -- the near bulk `V'` at the field scale `4ℓ`, `ℓ ≥ s_{k'}/…`
  have hNear : ∀ k', k' ≤ Nh → ∀ (ℓ₀ ℓ' cc : ℝ), 0 < ℓ' → ℓ₀ ≤ ℓ' → 1 ≤ cc →
      GoodCov2 k' ℓ₀ (histCovO (R.withMsq m) t k') →
      2 * ℓ' ≤ cc * histS (R.withMsq m) k' t →
      Tj 2 (L : ℝ) (k' + 1) ℓ'
          (PtCorr2.gNear (0 : Lam 2 L N) x k' (blockIdx (L := L) (N := N) k') fun c =>
            (Obs2.VprO (Obs2.histCovO (R.withMsq m) t k')
              (PtCorr2.hVR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t k') c :
                Obs.SA .two (Lam 2 L N)).e) ≤
        ENNReal.ofReal (2 * ((L : ℝ) + 39) ^ 2 * (cc ^ 4 * (M.core.c * (t k').1))) := by
    classical
    intro k' hk' ℓ₀ ℓ' cc hℓ' hℓ₀ hcc hC hcs
    unfold PtCorr2.gNear
    have hcard := card_near_le (0 : Lam 2 L N) x (j := k') (by omega)
      (blockIdx (L := L) (N := N) k') subset_rfl
    have hu0 : 0 ≤ cc ^ 4 * (M.core.c * (t k').1) :=
      mul_nonneg (by positivity) (mul_nonneg hc0 (hg0 k' hk'))
    have hterm : ∀ c ∈ (blockIdx (L := L) (N := N) k').filter (PtCorr2.NearAB (0 : Lam 2 L N) x k'),
        Tj 2 (L : ℝ) (k' + 1) ℓ' (Obs2.VprO (Obs2.histCovO (R.withMsq m) t k')
          (PtCorr2.hVR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t k') c :
            Obs.SA .two (Lam 2 L N)).e ≤ ENNReal.ofReal (cc ^ 4 * (M.core.c * (t k').1)) := by
      intro c hc
      have hcI := (mem_filter.1 hc).1
      refine (Tj_VprO_e_le hℓ' hℓ₀ hC _ c).trans ?_
      refine (tNorm_mono (pow_pos hL0 k').le le_rfl (by linarith) hcs _).trans ?_
      exact M.core.vhistED6 N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x)
        (oRed R m b μ₀ dxStd x) hobs k' hk' hcc c hcI
    refine (tNorm_sum_le _ _).trans ?_
    refine (sum_le_sum hterm).trans ?_
    rw [sum_const, nsmul_eq_mul]
    have h2 : (((blockIdx (L := L) (N := N) k').filter
        (PtCorr2.NearAB (0 : Lam 2 L N) x k')).card : ENNReal) ≤
        ENNReal.ofReal (2 * ((L : ℝ) + 39) ^ 2) := by
      rw [← ENNReal.ofReal_natCast]; exact ENNReal.ofReal_le_ofReal hcard
    calc _ ≤ ENNReal.ofReal (2 * ((L : ℝ) + 39) ^ 2) *
          ENNReal.ofReal (cc ^ 4 * (M.core.c * (t k').1)) := mul_le_mul_right' h2 _
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]
  -- the gradient part of a region at `T_{k'+1}(ℓ')`
  have hDel : ∀ k', j ≤ k' → k' < n → ∀ (ℓ' qq : ℝ), 0 < ℓ' → 1 ≤ qq →
      ℓ' ≤ qq * histS (R.withMsq m) k' t → ∀ X : Finset (Lam 2 L N),
      Tj 2 (L : ℝ) (k' + 1) ℓ'
          (Obs2.dABX (ptsX x) k' (Obs2.histCovO (R.withMsq m) t k')
            (PtCorr2.hVR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t k') X) ≤
        ENNReal.ofReal (2 * (qq ^ 4 * (L : ℝ)⁻¹ * e6Gr R M C₁k C₁w mbar cu m b μ₀ lam x k' +
          e6M4 R M C₁k C₁w mbar cu m b μ₀ lam x k' * e6Lop R m b μ₀ x w.length k' ℓ')) := by
    intro k' hk1' hk' ℓ' qq hℓ' hqq hlq X
    refine Tj_dABX_le (ptsX x) hab k' _ _ X (hVR_ab_mem (R.withMsq m) (ptsX x) j _ t hVab k')
      (hVR_ab_sym (R.withMsq m) (ptsX x) j _ t (hsym k' hk1' (by omega)))
      (fun c h1' h2' => hVR_ab_anch (R.withMsq m) (ptsX x) j _ t hanc hk1' c h1' h2') hℓ'
      (mul_nonneg (by positivity) (hGr0 k')) (hM40 k') (hLop0 k' ℓ' hℓ'.le)
      (fun c => (gradM4Sz_scale_le hℓ'.le hqq hlq _ _ _).trans
        (mul_le_mul_of_nonneg_left (hGrA k' hk1' hk' c).1 (by positivity)))
      (fun c => (hGrA k' hk1' hk' c).2) (hLop k' (by omega) ℓ' hℓ'.le)
  refine ⟨fun Y hY => ?_, fun X => ?_, fun X i hi1 hi2 => ?_, fun X i hi1 hi2 => ?_, ?_, ?_,
    fun X => ?_, ?_, fun X i hi1 hi2 => ?_, fun i hi1 hi2 => ?_, fun X i hi1 hi2 => ?_,
    fun i hi1 hi2 c' hc' => ?_⟩
  · -- item 1: `κ^Q`
    refine ((hKSi k hk1 hk2).1 Y hY).trans (le_of_eq ?_)
    unfold e6KQ; rw [div_mul_cancel₀ _ (hβp k hkN).ne']
  · -- item 2: the `𝒲'_{k-1}` block
    dsimp only
    intro hjk
    obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
    have hiN : i < Nh := by omega
    obtain ⟨hblk, -⟩ := hW N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam cu mbar hU hmbar
      h8' x hx h1 hj n hn2 hVB i (by omega) (by omega) hiN
    have hrE : eszR R M.core.c m b μ₀ i = M.core.c * (t i).1 :=
      max_eq_left (mul_nonneg hc0 (hg0 i hiN.le))
    simp only [Nat.add_sub_cancel]
    refine ⟨fun B => ?_, fun B => ?_, ?_⟩
    · by_cases hB : B ∈ blockIdx (L := L) (N := N) i
      · refine (hblk B hB).1.trans (le_of_eq ?_)
        unfold eszSe; rw [Nat.add_sub_cancel, hrE]; rfl
      · refine le_trans (le_of_eq (congrArg (Tj 2 (L : ℝ) (i + 1) (histS (R.withMsq m) (i + 1) t))
          (M.core.wpoOffD6 N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) _ hobs hanc i
            (by omega) hiN hB).1)) ?_
        rw [Step.Tj_zero]; exact zero_le
    · by_cases hB : B ∈ blockIdx (L := L) (N := N) i
      · refine (hblk B hB).2.1.trans (le_of_eq ?_)
        unfold eszSo eszO eszSO; rw [Nat.add_sub_cancel, hrE]; rfl
      · refine le_trans (le_of_eq (congrArg (Tj 2 (L : ℝ) (i + 1) (histS (R.withMsq m) (i + 1) t))
          (M.core.wpoOffD6 N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) _ hobs hanc i
            (by omega) hiN hB).2)) ?_
        rw [Step.Tj_zero]; exact zero_le
    · have hβ := hβp (i + 1) (by omega)
      unfold eszSw
      rw [div_mul_cancel₀ _ hβ.ne', zero_mul, add_zero]
      exact le_rfl
  · -- item 3a: `μ^Q`
    have hiN : i < Nh := by omega
    have hF := hFi i hi1 hiN
    have hκ := kappaQ_le_count (ptsX x) (hKR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t i) X
      hF.2.2.2.2.1.hK (hQ0 i) ((hKSi i hi1 (by omega)).1) (hcS i) (hcN i)
    refine (norm_m4QX_le (R.withMsq m) (ptsX x) j _ t Ccut2_spec.1 Ccut2_spec.2 hL8 hab X (hs i)
      hF.2.2.2.2.2.1 hκ).trans (le_of_eq ?_)
    unfold e6MQ sXp
    rw [div_mul_cancel₀ _ (hβp i hiN.le).ne']
  · -- item 3b: `μ^S`
    have hiN : i < Nh := by omega
    have hF := hFi i hi1 hiN
    have hκ := kappaS_le_count (ptsX x) (i := i)
      (fun U => (SXO i (histCovO (R.withMsq m) t i)
        (hVR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t i)
        (hWR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t i) U : SA .two (Lam 2 L N)).ab) X
      (fun b' hb' hn' => ((hKSi i hi1 (by omega)).2 hiN b' hb').2 hn') (hS0 i)
      (fun b' hb' => ((hKSi i hi1 (by omega)).2 hiN b' hb').1)
    refine (norm_m4LSX_le (R.withMsq m) (ptsX x) j _ t Ccut2_spec.1 Ccut2_spec.2 hL8 hab
      (by omega) X (hs (i + 1)) hF.2.2.2.2.2.2 hκ).trans (le_of_eq ?_)
    unfold e6MS sXp
    rw [div_mul_cancel₀ _ (hβp i hiN.le).ne']
  · -- item 4: `|1 − n_a| ≤ 3`
    have e1 : Obs2.nA2 (ptsX x) k (Obs2.histCovO (R.withMsq m) t k)
        (PtCorr2.hVR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t k) =
        nn2 R (ptsX x) (zV b) m b μ₀ k - ∑ i ∈ Finset.range k, tadO R m b μ₀ x i k := by
      have e2 := PtCorr2.frakN2_hR_eq (R := R.withMsq m) (P := ptsX x) (j := j) (t := t) hobs
        (Obs2.obsInit_isObs .two (zV b) (ptsX x)) k
      have e3 : nn2 R (ptsX x) (zV b) m b μ₀ k = Obs2.frakN2 (ptsX x) (Obs2.histCovO (R.withMsq m) t)
          (PtCorr2.hVR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t) k := by
        rw [e2]; rfl
      rw [e3]
      unfold Obs2.frakN2
      simp only [htadR]
      show Obs2.nuBar2 _ _ _ k = _
      ring
    rw [e1]
    have hs' : ‖∑ i ∈ Finset.range k, tadO R m b μ₀ x i k‖ ≤ 1 := by
      refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i hi => ?_).trans
        (geom_tail_two_le (by positivity) hL2' k))
      have hik := Finset.mem_range.1 hi
      refine (htad (ptsX x) (zV b) i k hik hkN).trans ?_
      have hc := hcg i (by omega)
      have hp : 0 ≤ (2 / (L : ℝ)) ^ (k - i) := by positivity
      calc M.core.ce * (2 / (L : ℝ)) ^ (k - i) * (t i).1
          = (2 / (L : ℝ)) ^ (k - i) * (M.core.ce * (t i).1) := by ring
        _ ≤ (2 / (L : ℝ)) ^ (k - i) * 1 := mul_le_mul_of_nonneg_left hc hp
        _ = _ := mul_one _
    have hn := hnn k hkN
    calc ‖1 - (nn2 R (ptsX x) (zV b) m b μ₀ k - ∑ i ∈ Finset.range k, tadO R m b μ₀ x i k)‖
        ≤ ‖(1 : ℂ)‖ + ‖nn2 R (ptsX x) (zV b) m b μ₀ k‖ +
            ‖∑ i ∈ Finset.range k, tadO R m b μ₀ x i k‖ := by
          refine (norm_sub_le _ _).trans ?_
          have := norm_sub_le (nn2 R (ptsX x) (zV b) m b μ₀ k)
            (∑ i ∈ Finset.range k, tadO R m b μ₀ x i k)
          linarith
      _ ≤ 3 := by rw [norm_one]; linarith
  · -- the vertex factor `|n_k| ≤ c_{ν,k}`
    have e1 : Obs2.nA2 (ptsX x) k (Obs2.histCovO (R.withMsq m) t k)
        (PtCorr2.hVR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t k) =
        nn2 R (ptsX x) (zV b) m b μ₀ k - ∑ i ∈ Finset.range k, tadO R m b μ₀ x i k := by
      have e2 := PtCorr2.frakN2_hR_eq (R := R.withMsq m) (P := ptsX x) (j := j) (t := t) hobs
        (Obs2.obsInit_isObs .two (zV b) (ptsX x)) k
      have e3 : nn2 R (ptsX x) (zV b) m b μ₀ k = Obs2.frakN2 (ptsX x) (Obs2.histCovO (R.withMsq m) t)
          (PtCorr2.hVR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t) k := by
        rw [e2]; rfl
      rw [e3]
      unfold Obs2.frakN2
      simp only [htadR]
      show Obs2.nuBar2 _ _ _ k = _
      ring
    rw [e1]
    have hgk := hg0 k hkN
    have hmk : max (t k).1 0 = (t k).1 := max_eq_left hgk
    have hs' : ‖∑ i ∈ Finset.range k, tadO R m b μ₀ x i k‖ ≤ M.core.ce * (t k).1 := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ i ∈ Finset.range k, ‖tadO R m b μ₀ x i k‖
          ≤ ∑ i ∈ Finset.range k, (M.core.ce * (t k).1) * (2 / (L : ℝ)) ^ (k - i) := by
            refine Finset.sum_le_sum fun i hi => ?_
            have hik := Finset.mem_range.1 hi
            refine (htad (ptsX x) (zV b) i k hik hkN).trans ?_
            have hgi := hgm i k hik.le hkN
            have hp : 0 ≤ (2 / (L : ℝ)) ^ (k - i) := by positivity
            calc M.core.ce * (2 / (L : ℝ)) ^ (k - i) * (t i).1
                = (M.core.ce * (2 / (L : ℝ)) ^ (k - i)) * (t i).1 := rfl
              _ ≤ (M.core.ce * (2 / (L : ℝ)) ^ (k - i)) * (t k).1 :=
                  mul_le_mul_of_nonneg_left hgi (mul_nonneg hct hp)
              _ = _ := by ring
        _ = (M.core.ce * (t k).1) * ∑ i ∈ Finset.range k, (2 / (L : ℝ)) ^ (k - i) := by
            rw [Finset.mul_sum]
        _ ≤ (M.core.ce * (t k).1) * 1 :=
            mul_le_mul_of_nonneg_left (geom_tail_two_le (by positivity) hL2' k)
              (mul_nonneg hct hgk)
        _ = _ := mul_one _
    have hn : ‖nn2 R (ptsX x) (zV b) m b μ₀ k‖ ≤
        (if k < Nh then max M.core.B' 0 * max (t k).1 0 else 1 / 8) := by
      split_ifs with hkl
      · rw [hmk]
        exact (hl k hkl).2.1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hgk)
      · exact hnn k hkN
    show _ ≤ (if k < Nh then max M.core.B' 0 * max (t k).1 0 else 1 / 8) +
      M.core.ce * max (t k).1 0
    rw [hmk]
    rw [hmk] at hn
    refine (norm_sub_le _ _).trans ?_
    linarith
  · -- item 5: `δ_k`
    refine (hDel k hk1 hk2 (2 * (2 * histS (R.withMsq m) k t)) 4 (by have := hs k; positivity)
      (by norm_num) (by linarith [hs k]) X).trans (le_of_eq ?_)
    unfold e6Del
    rw [div_mul_cancel₀ _ (hβp k hkN).ne']
  · -- item 6: `e_k`
    have h := hNear k hkN (histS (R.withMsq m) k t) (2 * (2 * histS (R.withMsq m) k t)) 8
      (by have := hs k; positivity) (by linarith [hs k]) (by norm_num) (hG k hkN) (by linarith)
    refine h.trans (le_of_eq ?_)
    show _ = ENNReal.ofReal (2 * ((L : ℝ) + 39) ^ 2 * ((8 : ℝ) ^ 4 * (M.core.c * max (t k).1 0)))
    rw [max_eq_left (hg0 k hkN)]
  · -- item 7: the Pauli defects
    have hiN : i ≤ Nh := by omega
    have h := PtCorr2.pdefM2X_hVR_le (R.withMsq m) (ptsX x) t hVab (hsym i hi1 hiN) (hG i hiN) w hpe X
    have hm4 := norm_m4X_le_two (R.withMsq m) (ptsX x) j _ t hanc hi1 X (hM40 i)
      (fun c => (hGrA i hi1 (by omega) c).2)
    refine h.trans ?_
    unfold pdSz e6M4X
    have hsq' := sq_nonneg ((w.length : ℝ) * (histS (R.withMsq m) i t / (L : ℝ) ^ (i + 1)))
    set D := ((w.length : ℝ) * (histS (R.withMsq m) i t / (L : ℝ) ^ (i + 1))) ^ 2 with hD
    set μi := e6M4 R M C₁k C₁w mbar cu m b μ₀ lam x i with hμi
    have hβi := (hβp i hiN).ne'
    have e : 2 * μi / ‖hBeta R m b μ₀ x (i + 1)‖ * D * ‖hBeta R m b μ₀ x (i + 1)‖ = 2 * μi * D := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right hm4 hsq'
  · -- item 8: `tadInc₂`
    rw [htadR]
    have h := htad (ptsX x) (zV b) i k hi2 hkN
    show _ ≤ M.core.ce * (2 / (L : ℝ)) ^ (k - i) * max (t i).1 0
    rw [max_eq_left (hg0 i (by omega))]
    exact h
  · -- item 9: `F_C(dABX_i, V'^{near}_∅)`
    have hiN : i < Nh := by omega
    have hF := hFi i hi1 hiN
    have hC1 : GoodCov2 i (histS (R.withMsq m) (i + 1) t) (histCovO (R.withMsq m) t i) :=
      hF.1.mono (by
        show histS (R.withMsq m) (i + 1) t / 4 ≤ histS (R.withMsq m) (i + 1) t
        linarith [hs (i + 1)])
    have hA := hDel i hi1 (by omega) (2 * (2 * histS (R.withMsq m) (i + 1) t)) (9 / 2)
      (by have := hs (i + 1); positivity) (by norm_num) (by linarith [hsq i]) X
    have hB := hNear i hiN.le (histS (R.withMsq m) (i + 1) t / 4)
      (2 * (2 * histS (R.withMsq m) (i + 1) t)) 9 (by have := hs (i + 1); positivity)
      (by linarith [hs (i + 1)]) (by norm_num) hF.1 (by linarith [hsq i, hs (i + 1)])
    refine (tNorm_FC_gen_le (hs (i + 1)) hC1 _ _).trans ?_
    have hd0 : 0 ≤ e6DelF R M C₁k C₁w mbar cu m b μ₀ lam x w.length i := by
      unfold e6DelF
      exact mul_nonneg (by norm_num) (add_nonneg (mul_nonneg (by positivity) (hGr0 i))
        (mul_nonneg (hM40 i) (hLop0 i _ (by have := hs (i + 1); positivity))))
    have he0 : 0 ≤ 2 * ((L : ℝ) + 39) ^ 2 * ((9 : ℝ) ^ 4 * (M.core.c * (t i).1)) :=
      mul_nonneg (by positivity) (mul_nonneg (by positivity) (mul_nonneg hc0 (hg0 i hiN.le)))
    calc 2 * (Tj 2 (L : ℝ) (i + 1) (2 * (2 * histS (R.withMsq m) (i + 1) t)) _ *
          Tj 2 (L : ℝ) (i + 1) (2 * (2 * histS (R.withMsq m) (i + 1) t)) _)
        ≤ 2 * (ENNReal.ofReal (e6DelF R M C₁k C₁w mbar cu m b μ₀ lam x w.length i) *
          ENNReal.ofReal (2 * ((L : ℝ) + 39) ^ 2 * ((9 : ℝ) ^ 4 * (M.core.c * (t i).1)))) := by
          gcongr
          exact hA
      _ = ENNReal.ofReal (e6F R M C₁k C₁w mbar cu m b μ₀ lam x w.length i *
          ‖hBeta R m b μ₀ x (i + 1)‖) := by
          show _ = ENNReal.ofReal (2 * (e6DelF R M C₁k C₁w mbar cu m b μ₀ lam x w.length i *
            (2 * ((L : ℝ) + 39) ^ 2 * ((9 : ℝ) ^ 4 * (M.core.c * max (t i).1 0)))) /
            ‖hBeta R m b μ₀ x (i + 1)‖ * ‖hBeta R m b μ₀ x (i + 1)‖)
          rw [max_eq_left (hg0 i hiN.le), div_mul_cancel₀ _ (hβp i hiN.le).ne',
            ← ENNReal.ofReal_mul hd0, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
            ENNReal.ofReal_ofNat]
  · -- item 10: the product parts
    have hiN : i < Nh := by omega
    have hcI : c' ∈ blockIdx (L := L) (N := N) (i + 1) := by
      rcases hc' with rfl | rfl <;> exact mem_image_of_mem _ (mem_univ _)
    obtain ⟨-, hprod⟩ := hW N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam cu mbar hU hmbar
      h8' x hx h1 hj n hn2 hVB i hi1 (by omega) hiN
    have hrE : eszR R M.core.c m b μ₀ i = M.core.c * (t i).1 :=
      max_eq_left (mul_nonneg hc0 (hg0 i hiN.le))
    refine (hprod c' hcI).trans (le_of_eq ?_)
    unfold eszWp eszO eszSO
    rw [div_mul_cancel₀ _ (hβp i hiN.le).ne', hrE]
    rfl


set_option maxHeartbeats 4000000 in
/-- **The invariants of the reduced states `oRed … dxStd` under `MasterFacts`.** -/
theorem pairRedInv_MFD6 {L : ℕ} [NeZero L] (M : MasterFacts L)
    (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0)
    (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N)
    (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : (∀ jD ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ jD))) :
    PairRedInv R Nh m b μ₀ (oRed R m b μ₀ dxStd) := by
  obtain ⟨-, -, -, hRI⟩ := M.core.pairTrajD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  intro x hx h1 hj
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  set t : Flow2.Hist.Seq (Xs (R.withMsq m)) := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with ht
  have hsymj : PtCorr2.ObsSymInv j (oRed R m b μ₀ dxStd x) :=
    PtCorr2.obsSymInv_redSt (hRI j hj).1 (hRI j hj).2 (rawD_mem (R.withMsq m) _ _)
      (rawK_mem (R.withMsq m) _ _)
      (PtCorr2.obsSymInv_hist (R.withMsq m) (ptsX x) _ (PtCorr2.obsSymInv_init .two (zV b) (ptsX x))
        t j fun i hi => (hRI i (by omega)))
  exact ⟨PtCorr2.obsVabInv_redSt (R.withMsq m) (ptsX x), fun B => oRed_V_ab_zero R m b μ₀ dxStd x B,
    fun k hk hkN =>
      PtCorr2.obsSymInv_histFrom' (R.withMsq m) (ptsX x) hsymj t hk fun i _ hi => hRI i (by omega)⟩


set_option maxHeartbeats 4000000 in
/-- **`PairJointSizesP3` for the reduced states** from the `V`-step data and the reorganised
`E`-step sizes, along every admissible trajectory of `MasterFacts` (copy of
`pairJointSizesP_MF`). -/
theorem pairJointSizesP3_MFD6 {L : ℕ} [NeZero L] (M : MasterFacts L)
    (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0)
    (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N)
    (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : (∀ jD ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ jD)))
    (lam : ℕ → ℂ) (ce ca cr : ℝ)
    (hX : ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
      ∃ (VB : ℕ → Prop) (κQ se so sw ηw μQ μS cn cν δ e Pd F Wp : ℕ → ℝ) (τ : ℕ → ℕ → ℝ)
        (w : List (Dir 2)), Obs2.pathEnd (0 : Lam 2 L N) w = x ∧
        (∀ k, 0 ≤ κQ k ∧ 0 ≤ μQ k ∧ 0 ≤ μS k ∧ 0 ≤ cn k ∧ 0 ≤ cν k ∧ 0 ≤ δ k ∧ 0 ≤ e k ∧
          0 ≤ Pd k ∧ 0 ≤ F k ∧ 0 ≤ Wp k) ∧ (∀ i k, 0 ≤ τ i k) ∧
        (∀ k, 0 ≤ se k ∧ 0 ≤ so k ∧ 0 ≤ sw k ∧ 0 ≤ ηw k) ∧
        ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
            (2 * (Q1 2 * (cQab * κQ k) *
              (PtCorr2.histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))⁻¹ ^ 2) +
              sw k + spE3 (Obs.coal L (0 : Lam 2 L N) x) μQ μS cn cν (fun k => (w.length *
                (PtCorr2.histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) /
                  (L : ℝ) ^ (k + 1))) ^ 2) k +
              2 * δ k * e k * (PtCorr2.histS (R.withMsq m) k
                (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))⁻¹ ^ 2 +
              smE3 R m b μ₀ (Obs.coal L (0 : Lam 2 L N) x) Pd F Wp τ k) ≤
          ce * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 ∧
        ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1), (64 / 49 : ℝ) ^ 2 * ηw k ≤ ca ∧
        VB (Obs.coal L (0 : Lam 2 L N) x) ∧
        (∀ n, Obs.coal L (0 : Lam 2 L N) x ≤ n → n ≤ Nh → VB n →
          PairMassUpTo R m b μ₀ lam (oRed R m b μ₀ dxStd) cr x n → VB (n + 1)) ∧
        PairESizes3 R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) cr x VB κQ se so sw ηw μQ μS cn cν δ e
          Pd F Wp τ) :
    PairJointSizesP3 R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) ce ca cr := by
  have hL49 : 49 ≤ L := M.core.hL49
  have hLp : pauliL0 2 ≤ L := M.core.hLpl
  have hLb : PtCorr2.prodLb ≤ (L : ℝ) := M.core.hLb.trans (by exact_mod_cast M.core.hLo)
  obtain ⟨hV, hVL, hG, hRI⟩ := M.core.pairTrajD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  have hRd := pairSectRed_of R m hV hVL b μ₀ (pairDCov_std (L := L) (N := N) Nh)
  intro x hx h1 hj
  obtain ⟨VB, κQ, se, so, sw, ηw, μQ, μS, cn, cν, δ, e, Pd, F, Wp, τ, w, hw, h0, hτ0, h0', hsum,
    hηsum, hVB0, hVs, hS⟩ := hX x hx h1 hj
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  set t : Flow2.Hist.Seq (Xs (R.withMsq m)) := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with ht
  have hVab : PtCorr2.ObsVabInv (ptsX x) (oRed R m b μ₀ dxStd x) :=
    PtCorr2.obsVabInv_redSt (R.withMsq m) (ptsX x)
  have hloc0 := (hRd x hx h1 hj).2.1
  have hanc := pairAnchR_oRed R Nh m b μ₀ x hx h1 hj
  have hβr := pairBetaRatio_MFD M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm x
  have hρ0 : 0 ≤ (R.withMsq m).ρ := hVL.2.2.2.2.1
  have hρ8 : (R.withMsq m).ρ ≤ 1 / 8 := hVL.2.2.2.2.2.1
  refine ⟨VB, fun k => PtCorr2.histS (R.withMsq m) k t, fun k => cQab * κQ k, se, so, sw,
    spE3 j μQ μS cn cν (fun k => (w.length * (PtCorr2.histS (R.withMsq m) k t /
      (L : ℝ) ^ (k + 1))) ^ 2),
    fun k => 2 * δ k * e k * (PtCorr2.histS (R.withMsq m) k t)⁻¹ ^ 2,
    smE3 R m b μ₀ j Pd F Wp τ, ηw, fun _ _ => 0, fun k => ?_, fun _ _ => le_rfl, hsum, ?_,
    hVB0, hVs, pairEStep3_of_sizes R hNh hL49 hLb hLp m b μ₀ lam _ cr x hVab hloc0 hanc hV hVL hG
      hRI hβr w hw VB κQ se so sw ηw μQ μS cn cν δ e Pd F Wp τ h0 hτ0 hS⟩
  · obtain ⟨hκ0, -, -, -, -, hδ0, he0, -, -, -⟩ := h0 k
    obtain ⟨hse, hso, hsw, hηw⟩ := h0' k
    exact ⟨PtCorr2.histS_pos' (R.withMsq m) hρ0 hρ8 t k, mul_nonneg cQab_nonneg hκ0, hse, hso,
      hsw, spE3_nonneg j (fun i => (h0 i).2.1) (fun i => (h0 i).2.2.1) (fun i => (h0 i).2.2.2.1)
        (fun i => (h0 i).2.2.2.2.1) (fun i => sq_nonneg _) k,
      mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hδ0) he0) (sq_nonneg _),
      smE3_nonneg R m b μ₀ hρ0 hρ8 j (fun i => (h0 i).2.2.2.2.2.2.2.1)
        (fun i => (h0 i).2.2.2.2.2.2.2.2.1) (fun i => (h0 i).2.2.2.2.2.2.2.2.2) hτ0 k, hηw⟩
  · refine le_trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_)) hηsum
    simp


set_option maxHeartbeats 4000000 in
/-- **The joint route from `MasterFacts` with the reorganised items** (copy of
`pairRRelR_of_jointSizesP_MF`). -/
theorem pairRRelR_of_jointSizesP3_MFD6 {L : ℕ} [NeZero L] (M : MasterFacts L)
    (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0)
    (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N)
    (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : (∀ jD ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ jD)))
    (lam : ℕ → ℂ) {ce ca cr : ℝ} (hce : 0 ≤ ce)
    (hcr : crErr2 ce M.core.cRel (4 / betaL L) M.core.ce (max M.core.B' 0) ca ≤ cr)
    (hJ : PairJointSizesP3 R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) ce ca cr) :
    PairRRelR R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) cr ∧
      PairRRelRX R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) cr ∧
      PairErrRelRX R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) ce ca := by
  have hL49 : 49 ≤ L := M.core.hL49
  have hLp : pauliL0 2 ≤ L := M.core.hLpl
  have hb : 0 < b := by
    have := (hadm 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hg' : ∀ k ≤ Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1 := fun k hk =>
    ⟨(hadm k hk).1.le, ((hadm k hk).2.1).trans M.eps_le⟩
  have hβL : 0 < betaL L := lt_of_lt_of_le (by norm_num) (betaL_ge (by omega))
  have hG2 : ∑ k ∈ Finset.range Nh, (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ^ 2 ≤
      4 / betaL L :=
    sum_gsq_le_of_inc hβL (M.gincD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm)
      (hg' 0 (Nat.zero_le _)).1 (hg' Nh le_rfl).2
  have hmono := M.gmonoD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  have hgm : ∀ i l, i ≤ l → l ≤ Nh → (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ i).1 ≤
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ l).1 := by
    intro i l hil hl
    have key : ∀ n, i + n ≤ Nh → (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ i).1 ≤
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (i + n)).1 := by
      intro n
      induction n with
      | zero => intro _; exact le_rfl
      | succ n ih => intro hn; exact (ih (by omega)).trans (hmono (i + n) (by omega))
    have := key (l - i) (by omega)
    rwa [show i + (l - i) = l by omega] at this
  obtain ⟨hct, htad, hcg⟩ := M.tadD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  have hF := M.flow
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrest⟩ := hF
  have hval : ∀ j < Nh, ValidAt (R.withMsq m) j :=
    ((hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm).1
  have hvalL := ((hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm).2
  have hRd := pairSectRed_of R m hval hvalL b μ₀ (pairDCov_std Nh)
  have hloop := fun x : Lam 2 L N =>
    (M.loopD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) (zV b)).2.2
  refine pairRRelR_of_jointSizesP3 R hNh hLp m hb lam (oRed R m b μ₀ dxStd) hce M.cRel_nonneg hct
    (le_max_right _ _) hL49 (fun k hk => (hg' k hk).1) hG2 hgm hcg hRd
    (fun x B => oRed_V_ab_zero R m b μ₀ dxStd x B) (fun x B => oRed_W_ab_zero R m b μ₀ dxStd x B)
    (fun x _ => M.relGD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) (zV b)
      (zV_mua_ne hb))
    (fun x _ k hk => by
      obtain ⟨q, -, -, hl⟩ := hloop x
      exact (hl k hk).1)
    (fun x _ k hk => by
      obtain ⟨q, -, -, hl⟩ := hloop x
      exact (hl k hk).2.1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hg' k hk.le).1))
    (fun x _ _ _ => (M.topD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x)).1)
    (fun x _ i k hik hk => htad (ptsX x) (zV b) i k hik hk)
    (pairAnchR_oRed R Nh m b μ₀)
    (pairRedInv_MFD6 M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm) hcr hJ


set_option maxHeartbeats 8000000 in
/-- **`pairJointSizesP3_of_VSD6` at given constants**. -/
theorem pairJointSizesP3_of_VSatD6 {L : ℕ} [NeZero L] (M : MasterFacts L)
    {Clo Clb C₁k C₁w C₁k' C₁w' : ℝ} (hWB : WpOBoundsAB L Clo Clb) (hClo : 0 ≤ Clo) (hClb : 0 ≤ Clb)
    (hC₁k : 0 ≤ C₁k) (hC₁w : 0 ≤ C₁w) (hC₁w' : 0 ≤ C₁w') (hAH : M.core.AbwHistPD6 C₁k C₁w)
    (hAH' : M.core.AbwHistPD6 C₁k' C₁w') :
    ∃ C₁v : ℝ, 0 ≤ C₁v ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
    ∀ m ∈ mRange L N, ∀ b μ₀,
      (∀ jD ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ jD)) →
    ∀ (lam : ℕ → ℂ) (cu ce ca cr mbar : ℝ), PairUnitSeed R Nh m b μ₀ lam cu → 0 < mbar →
      cr ≤ mbar → 0 ≤ ca →
      8 * (cu * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) ≤
        vck C₁v * ((4 * C₁v + 1) * mbar) →
      8 * (cu * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) ≤ (4 * C₁w + 1) * mbar →
      8 * (cu * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) ≤ (4 * C₁w' + 1) * mbar →
    (∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
      ∀ w : List (Dir 2), Obs2.pathEnd (0 : Lam 2 L N) w = x → (w.length : ℝ) ≤ 2 * sXp x →
        ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
            (2 * (Q1 2 * (cQab * e6KQ R M C₁k C₁w mbar cu m b μ₀ lam x k) *
              (PtCorr2.histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))⁻¹ ^ 2) +
              eszSw R M.core.c C₁w' mbar Clo Clb m b μ₀ lam x k +
              spE3 (Obs.coal L (0 : Lam 2 L N) x) (e6MQ R M C₁k C₁w mbar cu m b μ₀ lam x)
                (e6MS R M C₁w mbar m b μ₀ lam x) (fun _ => 3) (e6Nu R M Nh m b μ₀)
                (fun k => (w.length * (PtCorr2.histS (R.withMsq m) k
                  (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) / (L : ℝ) ^ (k + 1))) ^ 2) k +
              2 * e6Del R M C₁k C₁w mbar cu m b μ₀ lam x w.length k * e6E R M m b μ₀ k *
                (PtCorr2.histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))⁻¹ ^ 2 +
              smE3 R m b μ₀ (Obs.coal L (0 : Lam 2 L N) x)
                (pdSz R m b μ₀ w (e6M4X R M C₁k C₁w mbar cu m b μ₀ lam x))
                (e6F R M C₁k C₁w mbar cu m b μ₀ lam x w.length)
                (eszWp R M.core.c C₁w' mbar Clo Clb m b μ₀ lam x) (tauSz R m b μ₀ M.core.ce) k) ≤
          ce * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1) →
    PairJointSizesP3 R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) ce ca cr := by
  obtain ⟨C₁v, hC₁v, hVS⟩ := pairVStep_MFD M
  have hES := pairESizes3_MFatD6 M hWB hClo hClb hC₁k hC₁w hC₁w' hAH hAH'
  refine ⟨C₁v, hC₁v, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam cu ce ca cr mbar hU hmbar hcr hca
    h8v h8 h8' hX
  have hc0 : 0 ≤ M.core.c := by
    obtain ⟨_, _, _, _, hAH⟩ := M.core.abwHistD6
    obtain ⟨hcR, -⟩ := hAH N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
    rw [← hcR]; unfold cR cV cW cZ
    obtain ⟨H, -, -⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm
    have := H.hcmu; have := H.hC₂; positivity
  obtain ⟨hct, -, -⟩ := M.tadD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  obtain ⟨-, hVL, -, -⟩ := M.core.pairTrajD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  have hρ0 : 0 ≤ (R.withMsq m).ρ := hVL.2.2.2.2.1
  have hρ8 : (R.withMsq m).ρ ≤ 1 / 8 := hVL.2.2.2.2.2.1
  have hs : ∀ k, 0 < histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) := fun k =>
    histS_pos' (R.withMsq m) hρ0 hρ8 _ k
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by have := M.core.hL49; omega)
  refine pairJointSizesP3_MFD6 M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam ce ca cr
    fun x hx h1 hj => ?_
  obtain ⟨hVB0, hVs⟩ := hVS N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam cu cr mbar hU
    hmbar hcr h8v x hx h1 hj
  -- the path from `0` to `x`
  obtain ⟨w, hwx, hwl⟩ := PtCorr2.exists_path_sum (n := L ^ N) (x : Lam 2 L N)
  have hpe : Obs2.pathEnd (0 : Lam 2 L N) w = x := by
    rw [Obs2.pathEnd, zero_add, hwx]
  have hwl' : (w.length : ℝ) ≤ 2 * sXp x := by
    unfold sXp
    have hsn : supNorm ((ptsX x).a - (ptsX x).b) = supNorm x := by
      show supNorm ((0 : Lam 2 L N) - x) = supNorm x
      rw [zero_sub, supNorm_neg]
    rw [hsn]; exact_mod_cast hwl
  have hg0 : 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 :=
    (hadm _ hj).1.le
  have hvwB : 0 ≤ vwB R m b μ₀ lam x := mul_nonneg (norm_nonneg _) hg0
  have hE := fun k => esz_nonneg R (c := M.core.c) (C₁w := C₁w') (mbar := mbar) (Clo := Clo)
    (Clb := Clb) (m := m) (b := b) (μ₀ := μ₀) (lam := lam) (x := x) hc0 hC₁w' hmbar.le hClo hClb
    hvwB k
  -- nonnegativity of the explicit sequences
  have hQ0 : ∀ i, 0 ≤ kszQ R M C₁k C₁w mbar cu m b μ₀ lam x i := fun i => by
    unfold kszQ
    exact mul_nonneg (mul_nonneg (vwA_nonneg R m b μ₀ x _) hvwB)
      (mul_nonneg (by norm_num) (le_max_right _ _))
  have hS0 : ∀ i, 0 ≤ kszS R M C₁w mbar m b μ₀ lam x i := fun i => by
    unfold kszS; exact le_max_right _ _
  have hsX0 : 0 ≤ sXp x := Nat.cast_nonneg _
  have hGr0 : ∀ k, 0 ≤ e6Gr R M C₁k C₁w mbar cu m b μ₀ lam x k := fun k =>
    gradRHS_nonneg hL0 (Obs2.KG_nonneg 2 (Cc := Ccut2) (by norm_num)) (KM4_nonneg 2 (Cc := Ccut2)) hsX0
      hs (fun i => by have := hQ0 i; positivity) (fun i => by have := hS0 i; positivity) _ _
  have hM40 : ∀ k, 0 ≤ e6M4 R M C₁k C₁w mbar cu m b μ₀ lam x k := fun k =>
    m4RHS_nonneg hL0 (KM4_nonneg 2 (Cc := Ccut2)) hsX0
      hs (fun i => by have := hQ0 i; positivity) (fun i => by have := hS0 i; positivity) _ _
  have hLop0 : ∀ k ℓ', 0 ≤ ℓ' → 0 ≤ e6Lop R m b μ₀ x w.length k ℓ' := fun k ℓ' hℓ' => by
    unfold e6Lop; positivity
  have hK4 := KM4_nonneg 2 (Cc := Ccut2)
  refine ⟨PairVB R m b μ₀ lam x mbar, e6KQ R M C₁k C₁w mbar cu m b μ₀ lam x,
    eszSe R M.core.c Clb m b μ₀, eszSo R M.core.c C₁w' mbar Clo m b μ₀ lam x,
    eszSw R M.core.c C₁w' mbar Clo Clb m b μ₀ lam x, fun _ => 0,
    e6MQ R M C₁k C₁w mbar cu m b μ₀ lam x, e6MS R M C₁w mbar m b μ₀ lam x, fun _ => 3,
    e6Nu R M Nh m b μ₀, e6Del R M C₁k C₁w mbar cu m b μ₀ lam x w.length, e6E R M m b μ₀,
    pdSz R m b μ₀ w (e6M4X R M C₁k C₁w mbar cu m b μ₀ lam x),
    e6F R M C₁k C₁w mbar cu m b μ₀ lam x w.length,
    eszWp R M.core.c C₁w' mbar Clo Clb m b μ₀ lam x, tauSz R m b μ₀ M.core.ce, w, hpe,
    fun k => ⟨?_, ?_, ?_, by norm_num, ?_, ?_, ?_, ?_, ?_, (hE k).2.2.2.2⟩, fun i k => ?_,
    fun k => ⟨(hE k).1, (hE k).2.1, (hE k).2.2.1, le_rfl⟩,
    hX x hx h1 hj w hpe hwl', ?_, hVB0, hVs,
    hES N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam cu cr mbar hU hmbar h8 h8' x hx h1 hj
      w hpe hwl'⟩
  · unfold e6KQ; exact div_nonneg (hQ0 k) (norm_nonneg _)
  · unfold e6MQ
    exact div_nonneg (mul_nonneg hK4 (mul_nonneg (by positivity)
      (mul_nonneg (by positivity) (hQ0 k)))) (norm_nonneg _)
  · unfold e6MS
    exact div_nonneg (mul_nonneg hK4 (mul_nonneg (by positivity)
      (mul_nonneg (by positivity) (hS0 k)))) (norm_nonneg _)
  · unfold e6Nu
    have h1' : 0 ≤ (if k < Nh then max M.core.B' 0 *
        max (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 0 else 1 / 8) := by
      split_ifs
      · exact mul_nonneg (le_max_right _ _) (le_max_right _ _)
      · norm_num
    exact add_nonneg h1' (mul_nonneg hct (le_max_right _ _))
  · unfold e6Del
    exact div_nonneg (mul_nonneg (by norm_num) (add_nonneg (mul_nonneg (by positivity) (hGr0 k))
      (mul_nonneg (hM40 k) (hLop0 k _ (by have := hs k; positivity))))) (norm_nonneg _)
  · unfold e6E
    exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (mul_nonneg hc0 (le_max_right _ _)))
  · unfold pdSz e6M4X
    exact mul_nonneg (div_nonneg (mul_nonneg (by norm_num) (hM40 k)) (norm_nonneg _)) (sq_nonneg _)
  · unfold e6F e6DelF e6EF
    refine div_nonneg (mul_nonneg (by norm_num) (mul_nonneg ?_ ?_)) (norm_nonneg _)
    · exact mul_nonneg (by norm_num) (add_nonneg (mul_nonneg (by positivity) (hGr0 k))
        (mul_nonneg (hM40 k) (hLop0 k _ (by have := hs (k + 1); positivity))))
    · exact mul_nonneg (by positivity) (mul_nonneg (by positivity)
        (mul_nonneg hc0 (le_max_right _ _)))
  · unfold tauSz
    exact mul_nonneg (mul_nonneg hct (pow_nonneg (by positivity) _)) (le_max_right _ _)
  · simp only [mul_zero, Finset.sum_const_zero]
    exact hca


set_option maxHeartbeats 16000000 in
/-- **The per-scale bound for the explicit sequences** (see `Spin2/Pair/PairLoop6e`). -/
theorem pl6_item_leD6 {L : ℕ} [NeZero L] (M : MasterFacts L) {C₁k C₁w C₁w' Clo Clb : ℝ}
    (hC₁k : 0 ≤ C₁k) (hC₁w : 0 ≤ C₁w) (hC₁w' : 0 ≤ C₁w') (hClo : 0 ≤ Clo) (hClb : 0 ≤ Clb)
    (hθ : C₁k * (2 + 2 * (8 * cx M.core.κ M.core.cT) + 1) * (M.core.c * M.core.ε) ≤ 1 / 72)
    (hpow : (1 + cWblk 2 L Clb * (M.core.c * M.core.ε)) ^ (L ^ 2) ≤ 2)
    (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0)
    (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N)
    (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : (∀ jD ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ jD)))
    (lam : ℕ → ℂ) {cu mbar : ℝ} (hcu : 0 ≤ cu) (hmbar : 0 ≤ mbar)
    (x : Lam 2 L N) (hx : x ≠ 0) (h1 : 1 ≤ Obs.coal L (0 : Lam 2 L N) x)
    (hj : Obs.coal L (0 : Lam 2 L N) x ≤ Nh) (w : List (Dir 2)) (hwl : (w.length : ℝ) ≤ 2 * sXp x)
    (k : ℕ) (hjk : Obs.coal L (0 : Lam 2 L N) x ≤ k) (hk : k ≤ Nh) :
    2 * (Q1 2 * (cQab * e6KQ R M C₁k C₁w mbar cu m b μ₀ lam x k) *
        (PtCorr2.histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))⁻¹ ^ 2) +
      eszSw R M.core.c C₁w' mbar Clo Clb m b μ₀ lam x k +
      spE3 (Obs.coal L (0 : Lam 2 L N) x) (e6MQ R M C₁k C₁w mbar cu m b μ₀ lam x)
        (e6MS R M C₁w mbar m b μ₀ lam x) (fun _ => 3) (e6Nu R M Nh m b μ₀)
        (fun k => (w.length * (PtCorr2.histS (R.withMsq m) k
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) / (L : ℝ) ^ (k + 1))) ^ 2) k +
      2 * e6Del R M C₁k C₁w mbar cu m b μ₀ lam x w.length k * e6E R M m b μ₀ k *
        (PtCorr2.histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))⁻¹ ^ 2 +
      smE3 R m b μ₀ (Obs.coal L (0 : Lam 2 L N) x)
        (pdSz R m b μ₀ w (e6M4X R M C₁k C₁w mbar cu m b μ₀ lam x))
        (e6F R M C₁k C₁w mbar cu m b μ₀ lam x w.length)
        (eszWp R M.core.c C₁w' mbar Clo Clb m b μ₀ lam x) (tauSz R m b μ₀ M.core.ce) k ≤
      vwB R m b μ₀ lam x * (pl6CEM M C₁k C₁w C₁w' Clo Clb *
        pl6NF (Obs.coal L (0 : Lam 2 L N) x) (pl6k0 M cu) mbar (pl6r R m b μ₀ M.core.c) k) +
      (if k < Nh then 0 else
        vwB R m b μ₀ lam x * (pl6CNM L C₁w * (mbar * (M.core.c * M.core.ε)))) := by
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  set t : Flow2.Hist.Seq (Xs (R.withMsq m)) := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with ht
  have hb : 0 < b := by
    have := (hadm 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hL49 : 49 ≤ L := M.core.hL49
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  obtain ⟨-, hVL, -, -⟩ := M.core.pairTrajD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  have hρ0 : 0 ≤ (R.withMsq m).ρ := hVL.2.2.2.2.1
  have hρ8 : (R.withMsq m).ρ ≤ 1 / 8 := hVL.2.2.2.2.2.1
  have hs : ∀ k, 0 < histS (R.withMsq m) k t := fun k => histS_pos' (R.withMsq m) hρ0 hρ8 t k
  obtain ⟨hct, -, hcg⟩ := M.tadD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  obtain ⟨q, -, -, hl⟩ :=
    (M.loopD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) (zV b)).2.2
  have htop := (M.topD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x)).1
  have hβne : ∀ k ≤ Nh, hBeta R m b μ₀ x k ≠ 0 ∧ hBeta R m b μ₀ x (k + 1) ≠ 0 := fun k hk => by
    obtain ⟨a1, a2, -, -⟩ := hBeta_rel_of R hNh hb x
      (M.relGD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) (zV b) (zV_mua_ne hb))
      (fun k hk => (hl k hk).1) htop k hk
    exact ⟨a1, a2⟩
  have hβr := pairBetaRatio_MFD M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm x
  obtain ⟨Hap, -, -⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm
  have hcR : cR (R.withMsq m) ((L : ℝ) ^ 2) M.core.cm M.core.C₂x = M.core.c := by
    obtain ⟨_, _, _, _, hAH⟩ := M.core.abwHistD6
    exact (hAH N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm).1
  have hc1 : 1 ≤ M.core.c := by
    rw [← hcR]
    have hcV : 0 ≤ cV (R.withMsq m) ((L : ℝ) ^ 2) M.core.cm := by
      unfold cV cZ; have := Hap.hcmu; positivity
    have hcW : 0 ≤ cW (R.withMsq m) ((L : ℝ) ^ 2) M.core.cm M.core.C₂x := by
      unfold cW; have := Hap.hC₂; positivity
    unfold cR; linarith
  have hc0 : 0 ≤ M.core.c := by linarith
  have hcx : 0 ≤ cx M.core.κ M.core.cT := Hap.hcx
  have hg : ∀ i ≤ Nh, 0 < (t i).1 ∧ (t i).1 ≤ M.core.ε := fun i hi =>
    ⟨(hadm i hi).1, (hadm i hi).2.1⟩
  have hε0 : 0 ≤ M.core.ε := ((hg 0 (Nat.zero_le _)).1.trans_le (hg 0 (Nat.zero_le _)).2).le
  have hcε : M.core.c * M.core.ε ≤ 1 := M.core.hcε
  have hmono := M.gmonoD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  -- the sequence `r`
  have hrE : ∀ i ≤ Nh, pl6r R m b μ₀ M.core.c i = M.core.c * (t i).1 := fun i hi => by
    show M.core.c * max (t i).1 0 = _; rw [max_eq_left (hg i hi).1.le]
  have hrε : ∀ i ≤ Nh, pl6r R m b μ₀ M.core.c i ≤ M.core.c * M.core.ε := fun i hi => by
    rw [hrE i hi]; exact mul_le_mul_of_nonneg_left (hg i hi).2 hc0
  have hr0 : ∀ i, 0 ≤ pl6r R m b μ₀ M.core.c i := fun i => mul_nonneg hc0 (le_max_right _ _)
  have hgr : ∀ i ≤ Nh, max (t i).1 0 ≤ pl6r R m b μ₀ M.core.c i := fun i hi => by
    show max (t i).1 0 ≤ M.core.c * max (t i).1 0
    have := le_max_right (t i).1 0; nlinarith
  have heszR : ∀ i ≤ Nh, eszR R M.core.c m b μ₀ i = pl6r R m b μ₀ M.core.c i := fun i hi => by
    show max (M.core.c * (t i).1) 0 = _
    rw [hrE i hi]; exact max_eq_left (mul_nonneg hc0 (hg i hi).1.le)
  -- the ratio facts
  have H : PL6H j Nh (L : ℝ) (sXp x) (fun i => histS (R.withMsq m) i t)
      (fun i => ‖hBeta R m b μ₀ x i‖) (pl6r R m b μ₀ M.core.c) :=
    { hL := by exact_mod_cast hL49
      hs0 := hs
      hs1 := fun i => histS_succ_le_q (R.withMsq m) hρ0 hρ8 t i
      hs2 := fun i => histS_sq_ratio (R.withMsq m) hρ0 hρ8 t i
      hβ0 := fun i => norm_nonneg _
      hβp := fun i hi => by
        rcases Nat.lt_or_ge i (Nh + 1) with h | h
        · exact norm_pos_iff.2 (hβne i (by omega)).1
        · rw [show i = Nh + 1 by omega]; exact norm_pos_iff.2 (hβne Nh le_rfl).2
      hβr := hβr
      hr0 := hr0
      hr1 := fun i hi => (hrε i hi).trans hcε
      hsx := Nat.cast_nonneg _
      hsxL := by
        have h2 := two_supNorm_lt_coal (by omega : 2 ≤ L) x
        have hsn : supNorm ((ptsX x).a - (ptsX x).b) = supNorm (x - 0) := by
          show supNorm ((0 : Lam 2 L N) - x) = supNorm (x - 0)
          rw [supNorm_sub_comm]
        unfold sXp; rw [hsn]
        have : ((2 * supNorm (x - 0) : ℕ) : ℝ) ≤ ((L ^ (j + 1) : ℕ) : ℝ) := by
          exact_mod_cast h2.le
        push_cast at this; exact this }
  have hβj : 0 < ‖hBeta R m b μ₀ x j‖ := H.hβp j (by omega)
  -- the master constants
  have hK4 : 0 ≤ KM4 2 Ccut2 := KM4_nonneg 2
  have hKG : 0 ≤ Obs2.KG 2 Ccut2 4 := Obs2.KG_nonneg 2 (by norm_num)
  have hcNS : 0 ≤ 2 * (cNb2 : ℝ) * (cSm2 : ℝ) := by positivity
  have hQ1 : 1 ≤ Q1 2 := one_le_Q1 (d := 2) one_le_two
  have hcN : 0 ≤ Step2.cNear 2 L := by unfold Step2.cNear; exact Nat.cast_nonneg _
  have hθa0 : 0 ≤ kθ0 L M.core.A M.core.C₀a M.core.ηa := by
    unfold kθ0
    have := M.core.hA2
    exact mul_nonneg M.core.hC₀a (add_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _))
  have hθa : kθ0 L M.core.A M.core.C₀a M.core.ηa ≤ 1 / 72 := (M.core.hAa M.core.hLa).2
  set Bk := kB (kθ0 L M.core.A M.core.C₀a M.core.ηa) C₁k (8 * cx M.core.κ M.core.cT) with hBkd
  have hBk : 0 ≤ Bk := by rw [hBkd]; unfold kB; positivity
  have hcWc : 0 ≤ 4 * C₁w + 1 := by linarith
  have hcWc' : 0 ≤ 4 * C₁w' + 1 := by linarith
  have hcW : 0 ≤ cWblk 2 L Clb := cWblk_nonneg' hClb
  have hcB : 0 ≤ max M.core.B' 0 + M.core.ce := add_nonneg (le_max_right _ _) hct
  have hAs : ∀ c', 0 ≤ c' → 0 ≤ pl6As L c' := fun c' hc' => pl6As_nonneg hc'
  have haQ : 0 ≤ pl6aQ Bk (4 * C₁w + 1) := by unfold pl6aQ pl6ρ; positivity
  have hcQ : 0 ≤ pl6cQ (2 * (cNb2 : ℝ) * (cSm2 : ℝ)) Bk (4 * C₁w + 1) := by
    unfold pl6cQ; exact mul_nonneg hcNS haQ
  have hcS : 0 ≤ pl6cS L (4 * C₁w + 1) := by unfold pl6cS; have := hAs _ hcWc; positivity
  have hcM : 0 ≤ pl6cM L (KM4 2 Ccut2) (2 * (cNb2 : ℝ) * (cSm2 : ℝ)) Bk (4 * C₁w + 1) := by
    unfold pl6cM; positivity
  have hcG : 0 ≤ pl6cG L (KM4 2 Ccut2) (Obs2.KG 2 Ccut2 4) (2 * (cNb2 : ℝ) * (cSm2 : ℝ)) Bk
      (4 * C₁w + 1) := by unfold pl6cG; positivity
  have hcO : 0 ≤ pl6cO L Clo (4 * C₁w' + 1) := by unfold pl6cO; have := hAs _ hcWc'; positivity
  set V := vwB R m b μ₀ lam x with hVd
  have hV : 0 ≤ V := mul_nonneg (norm_nonneg _) (hg j hj).1.le
  set k₀ := pl6k0 M cu with hk₀d
  have hk₀ : 0 ≤ k₀ := by
    rw [hk₀d]; unfold pl6k0
    have := M.ιW_ge; have := M.core.hA2
    exact mul_nonneg hcu (pow_nonneg (by positivity) _)
  -- `vwA = 2s²β` below `N_h + 1`
  have hvwA : ∀ i ≤ Nh, vwA R m b μ₀ x i = 2 * histS (R.withMsq m) i t ^ 2 * ‖hBeta R m b μ₀ x i‖ :=
    fun i hi => by unfold vwA; rw [if_neg (hβne i hi).1]
  -- the small-set sizes in profile form
  set θ := 8 * (kθ0 L M.core.A M.core.C₀a M.core.ηa + C₁k * (2 + 2 * (8 * cx M.core.κ M.core.cT) + 1) *
      (M.core.c * M.core.ε)) with hθd
  have hθ0 : 0 ≤ θ := by rw [hθd]; positivity
  have hθρ : θ * pl6ρ ≤ 1 / 2 := by
    have h29 : θ ≤ 2 / 9 := by rw [hθd]; linarith
    unfold pl6ρ; nlinarith
  have hK : ∀ i, j ≤ i → i ≤ Nh →
      2 * histS (R.withMsq m) j t ^ 2 * ‖hBeta R m b μ₀ x j‖ *
        kszK R M C₁k C₁w mbar cu m b μ₀ lam x i ≤
      histS (R.withMsq m) i t ^ 2 * ‖hBeta R m b μ₀ x (i + 1)‖ *
        (128 / 49 * pl6P j k₀ i + 4 * pl6ρ * (64 / 49) * Bk * (4 * C₁w + 1) *
          (mbar * pl6Q j (pl6r R m b μ₀ M.core.c) i)) := fun i hji hi =>
    pl6_kseq H (r' := fun i => M.core.c * (t i).1)
      (m' := fun i => (4 * C₁w + 1) * (vwA R m b μ₀ x i * V / (vwA R m b μ₀ x j * V) * mbar))
      hθ0 hθρ hBk hcWc hk₀ hmbar (fun i hi => (hrE i hi).symm)
      (fun i hji hi => by
        show 2 * histS (R.withMsq m) j t ^ 2 * ‖hBeta R m b μ₀ x j‖ * ((4 * C₁w + 1) *
          (vwA R m b μ₀ x i * V / (vwA R m b μ₀ x j * V) * mbar)) ≤
          (4 * C₁w + 1) * (2 * histS (R.withMsq m) i t ^ 2 * ‖hBeta R m b μ₀ x i‖) * mbar
        rw [hvwA i hi, hvwA j hj]
        rcases hV.eq_or_lt with h0 | hpos
        · rw [← h0]; simp only [mul_zero, div_zero, zero_mul]
          have := hs i; positivity
        · have hA : 0 < 2 * histS (R.withMsq m) j t ^ 2 * ‖hBeta R m b μ₀ x j‖ := by
            have := hs j; positivity
          rw [mul_div_mul_right _ _ hpos.ne']
          apply le_of_eq
          have := (hs j).ne'
          have := (H.hβp j (by omega)).ne'
          field_simp)
      hji hi
  have hkszQ : ∀ i, j ≤ i → i ≤ Nh → kszQ R M C₁k C₁w mbar cu m b μ₀ lam x i ≤
      V * (histS (R.withMsq m) i t ^ 2 * ‖hBeta R m b μ₀ x (i + 1)‖) *
        (pl6aQ Bk (4 * C₁w + 1) * pl6G0 j k₀ mbar (pl6r R m b μ₀ M.core.c) i) := by
    intro i hji hi
    have hA : 0 < 2 * histS (R.withMsq m) j t ^ 2 * ‖hBeta R m b μ₀ x j‖ := by
      have := hs j; positivity
    have hKi := hK i hji hi
    set X := 128 / 49 * pl6P j k₀ i + 4 * pl6ρ * (64 / 49) * Bk * (4 * C₁w + 1) *
      (mbar * pl6Q j (pl6r R m b μ₀ M.core.c) i) with hXd
    have hP0 := pl6P_nonneg (j := j) hk₀ i
    have hQ0 := pl6Q_nonneg (j := j) (r := pl6r R m b μ₀ M.core.c) i
    have hc₁ : 0 ≤ 4 * pl6ρ * (64 / 49) * Bk * (4 * C₁w + 1) := by unfold pl6ρ; positivity
    have hX0 : 0 ≤ X := by rw [hXd]; positivity
    have hT0 : 0 ≤ histS (R.withMsq m) i t ^ 2 * ‖hBeta R m b μ₀ x (i + 1)‖ := by positivity
    have hmax : 2 * histS (R.withMsq m) j t ^ 2 * ‖hBeta R m b μ₀ x j‖ *
        max (kszK R M C₁k C₁w mbar cu m b μ₀ lam x i) 0 ≤
        histS (R.withMsq m) i t ^ 2 * ‖hBeta R m b μ₀ x (i + 1)‖ * X := by
      rw [mul_max_of_nonneg _ _ hA.le, mul_zero]
      exact max_le hKi (mul_nonneg hT0 hX0)
    have h8 : 8 * X ≤ pl6aQ Bk (4 * C₁w + 1) * pl6G0 j k₀ mbar (pl6r R m b μ₀ M.core.c) i := by
      have e : pl6aQ Bk (4 * C₁w + 1) * pl6G0 j k₀ mbar (pl6r R m b μ₀ M.core.c) i =
          8 * X + 8 * (128 / 49 * (mbar * pl6Q j (pl6r R m b μ₀ M.core.c) i) +
            4 * pl6ρ * (64 / 49) * Bk * (4 * C₁w + 1) * pl6P j k₀ i) := by
        rw [hXd]; unfold pl6aQ pl6G0; ring
      rw [e]; have : 0 ≤ mbar * pl6Q j (pl6r R m b μ₀ M.core.c) i := mul_nonneg hmbar hQ0
      have : 0 ≤ 4 * pl6ρ * (64 / 49) * Bk * (4 * C₁w + 1) * pl6P j k₀ i := mul_nonneg hc₁ hP0
      linarith
    unfold kszQ
    rw [hvwA j hj]
    calc 2 * histS (R.withMsq m) j t ^ 2 * ‖hBeta R m b μ₀ x j‖ * V *
          (8 * max (kszK R M C₁k C₁w mbar cu m b μ₀ lam x i) 0) =
        8 * V * (2 * histS (R.withMsq m) j t ^ 2 * ‖hBeta R m b μ₀ x j‖ *
          max (kszK R M C₁k C₁w mbar cu m b μ₀ lam x i) 0) := by ring
      _ ≤ 8 * V * (histS (R.withMsq m) i t ^ 2 * ‖hBeta R m b μ₀ x (i + 1)‖ * X) := by gcongr
      _ = V * (histS (R.withMsq m) i t ^ 2 * ‖hBeta R m b μ₀ x (i + 1)‖) * (8 * X) := by ring
      _ ≤ _ := by gcongr
  have hkszS : ∀ i, j ≤ i → i ≤ Nh → kszS R M C₁w mbar m b μ₀ lam x i ≤
      V * (histS (R.withMsq m) i t ^ 2 * ‖hBeta R m b μ₀ x (i + 1)‖) *
        (128 / 49 * (L : ℝ) ^ 2 * pl6As L (4 * C₁w + 1) * (mbar * pl6r R m b μ₀ M.core.c i)) := by
    intro i hji hi
    have e : vwA R m b μ₀ x i * V * ((L : ℝ) ^ 2 * sO 2 L (M.core.c * (t i).1) mbar
        ((4 * C₁w + 1) * (M.core.c * (t i).1) * mbar)) =
        2 * (L : ℝ) ^ 2 * pl6As L (4 * C₁w + 1) * V * histS (R.withMsq m) i t ^ 2 *
          (mbar * pl6r R m b μ₀ M.core.c i) * ‖hBeta R m b μ₀ x i‖ := by
      rw [hvwA i hi, hrE i hi]; unfold sO pl6As; ring
    have hB := H.hβr i hi
    have hX0 : 0 ≤ 2 * (L : ℝ) ^ 2 * pl6As L (4 * C₁w + 1) * V * histS (R.withMsq m) i t ^ 2 *
        (mbar * pl6r R m b μ₀ M.core.c i) := by
      have := hAs _ hcWc; have := hr0 i; positivity
    show max (vwA R m b μ₀ x i * V * ((L : ℝ) ^ 2 * sO 2 L (M.core.c * (t i).1) mbar
        ((4 * C₁w + 1) * (M.core.c * (t i).1) * mbar))) 0 ≤ _
    rw [e]
    have := hAs _ hcWc; have := hr0 i
    refine max_le ?_ (by positivity)
    calc _ ≤ 2 * (L : ℝ) ^ 2 * pl6As L (4 * C₁w + 1) * V * histS (R.withMsq m) i t ^ 2 *
          (mbar * pl6r R m b μ₀ M.core.c i) * (64 / 49 * ‖hBeta R m b μ₀ x (i + 1)‖) :=
          mul_le_mul_of_nonneg_left hB hX0
      _ = _ := by ring
  -- the abstract sizes
  set κQ : ℕ → ℝ := fun i => 2 * (cNb2 : ℝ) * (cSm2 : ℝ) * kszQ R M C₁k C₁w mbar cu m b μ₀ lam x i
    with hκQd
  set κS : ℕ → ℝ := fun i => 2 * (L : ℝ) ^ 2 * kszS R M C₁w mbar m b μ₀ lam x i with hκSd
  have hQK0 : ∀ i, 0 ≤ kszQ R M C₁k C₁w mbar cu m b μ₀ lam x i := fun i => by
    unfold kszQ
    exact mul_nonneg (mul_nonneg (vwA_nonneg R m b μ₀ x _) hV)
      (mul_nonneg (by norm_num) (le_max_right _ _))
  have hSK0 : ∀ i, 0 ≤ kszS R M C₁w mbar m b μ₀ lam x i := fun i => by
    unfold kszS; exact le_max_right _ _
  have hκQ0 : ∀ i, 0 ≤ κQ i := fun i => mul_nonneg hcNS (hQK0 i)
  have hκS0 : ∀ i, 0 ≤ κS i := fun i => mul_nonneg (by positivity) (hSK0 i)
  have hκQ : ∀ i, j ≤ i → i ≤ Nh → κQ i ≤ V * (histS (R.withMsq m) i t ^ 2 *
      ‖hBeta R m b μ₀ x (i + 1)‖) * (pl6cQ (2 * (cNb2 : ℝ) * (cSm2 : ℝ)) Bk (4 * C₁w + 1) *
        pl6G0 j k₀ mbar (pl6r R m b μ₀ M.core.c) i) := fun i hji hi => by
    have := mul_le_mul_of_nonneg_left (hkszQ i hji hi) hcNS
    calc κQ i ≤ _ := this
      _ = _ := by unfold pl6cQ; ring
  have hκS : ∀ i, j ≤ i → i ≤ Nh → κS i ≤ V * (histS (R.withMsq m) i t ^ 2 *
      ‖hBeta R m b μ₀ x (i + 1)‖) * (pl6cS L (4 * C₁w + 1) *
        (mbar * pl6r R m b μ₀ M.core.c i)) := fun i hji hi => by
    have := mul_le_mul_of_nonneg_left (hkszS i hji hi) (by positivity : (0 : ℝ) ≤ 2 * (L : ℝ) ^ 2)
    calc κS i ≤ _ := this
      _ = _ := by unfold pl6cS; ring
  have hwl0 : (0 : ℝ) ≤ w.length := Nat.cast_nonneg _
  -- the profile constants
  set cQ := pl6cQ (2 * (cNb2 : ℝ) * (cSm2 : ℝ)) Bk (4 * C₁w + 1) with hcQd
  set cS := pl6cS L (4 * C₁w + 1) with hcSd
  set cM := pl6cM L (KM4 2 Ccut2) (2 * (cNb2 : ℝ) * (cSm2 : ℝ)) Bk (4 * C₁w + 1) with hcMd
  set cG := pl6cG L (KM4 2 Ccut2) (Obs2.KG 2 Ccut2 4) (2 * (cNb2 : ℝ) * (cSm2 : ℝ)) Bk
    (4 * C₁w + 1) with hcGd
  set r := pl6r R m b μ₀ M.core.c with hrd
  have hcMe : cM = KM4 2 Ccut2 * (cQ / (L : ℝ) ^ 2 + 6 / 5 * cS) := by rw [hcMd]; rfl
  have hcGe : cG = (L : ℝ) * (3 / 4 * (L : ℝ) ^ 2 * (KM4 2 Ccut2 * (cQ / (L : ℝ) ^ 2 + 6 / 5 * cS)) +
      (2 * Obs2.KG 2 Ccut2 4 / (L : ℝ) + 243 / 64) * cQ + (2 * Obs2.KG 2 Ccut2 4 + 3) * cS) := by
    rw [hcGd]; rfl
  -- the gradient and `M₄` sizes
  have hγ : ∀ i, i ≤ Nh → e6Gr R M C₁k C₁w mbar cu m b μ₀ lam x i ≤
      histS (R.withMsq m) i t ^ 2 * ‖hBeta R m b μ₀ x (i + 1)‖ * V *
        (cG * pl6FO j k₀ mbar r i) := fun i hi => by
    rw [hcGe]
    exact pl6_grad H hK4 hKG hV hk₀ hmbar hcQ hcS hκQ0 hκS0 hκQ hκS hi
  have hml : ∀ i, i ≤ Nh → ∀ ℓ', 0 ≤ ℓ' →
      e6M4 R M C₁k C₁w mbar cu m b μ₀ lam x i * e6Lop R m b μ₀ x w.length i ℓ' ≤
      12 * ℓ' ^ 2 * (‖hBeta R m b μ₀ x (i + 1)‖ * V * (cM * pl6FO j k₀ mbar r i)) :=
    fun i hi ℓ' hℓ' => by
      rw [hcMe]
      exact pl6_m4lop H hK4 hV hk₀ hmbar hcQ hcS hκQ0 hκS0 hκQ hκS hwl0 hwl hℓ' hi
  have hGr0 : ∀ k, 0 ≤ e6Gr R M C₁k C₁w mbar cu m b μ₀ lam x k := fun k =>
    gradRHS_nonneg hL0 hKG hK4 (Nat.cast_nonneg _) hs hκQ0 hκS0 _ _
  have hM40 : ∀ k, 0 ≤ e6M4 R M C₁k C₁w mbar cu m b μ₀ lam x k := fun k =>
    m4RHS_nonneg hL0 hK4 (Nat.cast_nonneg _) hs hκQ0 hκS0 _ _
  have hLop0 : ∀ k ℓ', 0 ≤ ℓ' → 0 ≤ e6Lop R m b μ₀ x w.length k ℓ' := fun k ℓ' hℓ' => by
    unfold e6Lop; have : (0 : ℝ) ≤ sXp x := Nat.cast_nonneg _; positivity
  -- group 1
  have g1 : 2 * (Q1 2 * (cQab * e6KQ R M C₁k C₁w mbar cu m b μ₀ lam x k) *
      (histS (R.withMsq m) k t)⁻¹ ^ 2) ≤
      V * (2 * Q1 2 * cQab * pl6aQ Bk (4 * C₁w + 1) * pl6NF j k₀ mbar r k) :=
    pl6_g1 H hk (by linarith) cQab_nonneg haQ hV hk₀ hmbar (hkszQ k hjk hk)
  -- group 2
  have g2 : eszSw R M.core.c C₁w' mbar Clo Clb m b μ₀ lam x k ≤
      V * (4 * (L : ℝ) ^ 4 * cWblk 2 L Clb * pl6cO L Clo (4 * C₁w' + 1) * (6 / 5) * (64 / 49) ^ 2 *
        pl6NF j k₀ mbar r k) := by
    have hk1 : 1 ≤ k := le_trans h1 hjk
    have hso : eszSo R M.core.c C₁w' mbar Clo m b μ₀ lam x k =
        V * (histS (R.withMsq m) (k - 1) t ^ 2 * ‖hBeta R m b μ₀ x (k - 1)‖) *
          (pl6cO L Clo (4 * C₁w' + 1) * (mbar * r (k - 1))) := by
      unfold eszSo eszO eszSO
      rw [hvwA (k - 1) (by omega), heszR (k - 1) (by omega)]
      unfold sO pl6cO pl6As; ring
    have hso0 : 0 ≤ eszSo R M.core.c C₁w' mbar Clo m b μ₀ lam x k := by
      rw [hso]; have := hr0 (k - 1); positivity
    have hse : eszSe R M.core.c Clb m b μ₀ k = cWblk 2 L Clb * r (k - 1) := by
      unfold eszSe; rw [heszR (k - 1) (by omega)]
    have hp : (1 + cWblk 2 L Clb * r (k - 1)) ^ (L ^ 2) ≤ 2 := by
      refine le_trans (pow_le_pow_left₀ (by have := hr0 (k - 1); positivity) ?_ _) hpow
      have := hrε (k - 1) (by omega)
      have := mul_le_mul_of_nonneg_left this hcW
      linarith
    have hmo : r (k - 1) ≤ r k := by
      rw [hrE (k - 1) (by omega), hrE k hk]
      refine mul_le_mul_of_nonneg_left ?_ hc0
      have := hmono (k - 1) (by omega)
      rwa [show k - 1 + 1 = k by omega] at this
    exact pl6_g2 H hjk hk1 hk hV hk₀ hmbar hcW hcO (by push_cast; ring) hso0 hso.le hse hp hmo
  -- group 3
  have g3 : spE3 j (e6MQ R M C₁k C₁w mbar cu m b μ₀ lam x)
        (e6MS R M C₁w mbar m b μ₀ lam x) (fun _ => 3) (e6Nu R M Nh m b μ₀)
        (fun k => (w.length * (histS (R.withMsq m) k t / (L : ℝ) ^ (k + 1))) ^ 2) k ≤
      V * ((12 * KM4 2 Ccut2 * cQ / (L : ℝ) ^ 2 + 24 / 5 * (max M.core.B' 0 + M.core.ce) *
        KM4 2 Ccut2 * cS) * pl6NF j k₀ mbar r k) +
      (if k < Nh then 0 else V * (27 / 5 * KM4 2 Ccut2 * cS * (mbar * (M.core.c * M.core.ε)))) :=
    pl6_g3 H (K₄ := KM4 2 Ccut2) (cQ := cQ) (cS := cS) (V := V) (k₀ := k₀) (mb := mbar)
    (wl := w.length) (cB := max M.core.B' 0 + M.core.ce) (cε := M.core.c * M.core.ε)
    (κQ := κQ) (κS := κS) (cν := e6Nu R M Nh m b μ₀) hK4 hV hk₀ hmbar hcQ hcS hcB hwl0 hwl
    hκQ0 hκS0 hκQ hκS hrε hk
    (by
      unfold e6Nu
      have h1' : 0 ≤ (if k < Nh then max M.core.B' 0 * max (t k).1 0 else 1 / 8) := by
        split_ifs
        · exact mul_nonneg (le_max_right _ _) (le_max_right _ _)
        · norm_num
      exact add_nonneg h1' (mul_nonneg hct (le_max_right _ _)))
    (fun hkN => by
      unfold e6Nu; rw [if_pos hkN]
      have := hgr k hk
      have : 0 ≤ max (t k).1 0 := le_max_right _ _
      calc max M.core.B' 0 * max (t k).1 0 + M.core.ce * max (t k).1 0 =
          (max M.core.B' 0 + M.core.ce) * max (t k).1 0 := by ring
        _ ≤ (max M.core.B' 0 + M.core.ce) * r k := by gcongr)
    (fun hkN => by
      change (if k < Nh then max M.core.B' 0 * max (t k).1 0 else 1 / 8) +
        M.core.ce * max (t k).1 0 ≤ 9 / 8
      rw [if_neg hkN, max_eq_left (hg k hk).1.le]
      have h' : M.core.ce * (t k).1 ≤ 1 := hcg k hk
      linarith)
  -- group 4
  have g4 : 2 * e6Del R M C₁k C₁w mbar cu m b μ₀ lam x w.length k * e6E R M m b μ₀ k *
      (histS (R.withMsq m) k t)⁻¹ ^ 2 ≤
      V * (8 * (2 * ((L : ℝ) + 39) ^ 2 * 8 ^ 4) * (256 * cG / (L : ℝ) + 192 * cM) *
        pl6NF j k₀ mbar r k) :=
    pl6_g4 H hk (hGr0 k) (mul_nonneg (hM40 k) (hLop0 k _ (by have := hs k; positivity)))
      (by unfold e6E; have := le_max_right (t k).1 0; positivity) (by positivity) hcG hcM hV
      hk₀ hmbar (hγ k hk) (hml k hk _ (by have := hs k; positivity))
      (by unfold e6E; rw [hrd]; unfold pl6r; apply le_of_eq; ring)
  -- group 5
  have g5 : smE3 R m b μ₀ j (pdSz R m b μ₀ w (e6M4X R M C₁k C₁w mbar cu m b μ₀ lam x))
      (e6F R M C₁k C₁w mbar cu m b μ₀ lam x w.length)
      (eszWp R M.core.c C₁w' mbar Clo Clb m b μ₀ lam x) (tauSz R m b μ₀ M.core.ce) k ≤
      V * ((16 * M.core.ce * cM + 2560 * locK 2 ^ 2 * (4 * (2 * ((L : ℝ) + 39) ^ 2 * 9 ^ 4) *
        ((9 / 2 : ℝ) ^ 4 * (6 / 5) * cG / (L : ℝ) + 192 * cM)) +
        2560 * locK 2 ^ 2 * (2 * (L : ℝ) ^ 4 * pl6cO L Clo (4 * C₁w' + 1) * cWblk 2 L Clb *
          (64 / 49) * (6 / 5))) * pl6NF j k₀ mbar r k) := by
    have hE := fun i => esz_nonneg R (c := M.core.c) (C₁w := C₁w') (mbar := mbar) (Clo := Clo)
      (Clb := Clb) (m := m) (b := b) (μ₀ := μ₀) (lam := lam) (x := x) hc0 hC₁w' hmbar hClo hClb
      hV i
    refine pl6_g5 H hk hct hcM (by positivity) (by positivity) hV hk₀ hmbar
      (fun i => by
        unfold pdSz e6M4X
        exact mul_nonneg (div_nonneg (mul_nonneg (by norm_num) (hM40 i)) (norm_nonneg _))
          (sq_nonneg _))
      (fun i => by
        show 0 ≤ M.core.ce * (2 / (L : ℝ)) ^ (k - i) * max (t i).1 0
        exact mul_nonneg (mul_nonneg hct (by positivity)) (le_max_right _ _))
      (fun i => by
        unfold e6F e6DelF e6EF
        refine div_nonneg (mul_nonneg (by norm_num) (mul_nonneg ?_ ?_)) (norm_nonneg _)
        · exact mul_nonneg (by norm_num) (add_nonneg (mul_nonneg (by positivity) (hGr0 i))
            (mul_nonneg (hM40 i) (hLop0 i _ (by have := hs (i + 1); positivity))))
        · exact mul_nonneg (by positivity) (mul_nonneg (by positivity)
            (mul_nonneg hc0 (le_max_right _ _))))
      (fun i => (hE i).2.2.2.2)
      (fun i hji hik => by
        rw [hcMe]
        exact pl6_Pd_le H hK4 hV hk₀ hmbar hcQ hcS hκQ0 hκS0 hκQ hκS hwl0 hwl (by omega))
      (fun i hji hik => by
        show M.core.ce * (2 / (L : ℝ)) ^ (k - i) * max (t i).1 0 ≤ _
        exact mul_le_mul_of_nonneg_left (hgr i (by omega)) (by positivity))
      (fun i hji hik =>
        pl6_F_le H (by omega) (hGr0 i)
          (mul_nonneg (hM40 i) (hLop0 i _ (by have := hs (i + 1); positivity)))
          (by unfold e6EF; have := le_max_right (t i).1 0; positivity) (by positivity) hcG hcM hV
          hk₀ hmbar (hγ i (by omega)) (hml i (by omega) _ (by have := hs (i + 1); positivity))
          (by unfold e6EF; rw [hrd]; unfold pl6r; apply le_of_eq; ring))
      (fun i hji hik => by
        have hiN : i ≤ Nh := by omega
        have hx0 : 0 ≤ cWblk 2 L Clb * r i := mul_nonneg hcW (hr0 i)
        have hpw : (1 + cWblk 2 L Clb * r i) ^ (L ^ 2) - 1 ≤ 2 * (L : ℝ) ^ 2 * (cWblk 2 L Clb * r i) := by
          have h := pl6_pow_sub_one_le hx0 (L ^ 2)
          have hp2 : (1 + cWblk 2 L Clb * r i) ^ (L ^ 2) ≤ 2 := by
            refine le_trans (pow_le_pow_left₀ (by positivity) ?_ _) hpow
            have := mul_le_mul_of_nonneg_left (hrε i hiN) hcW; linarith
          push_cast at h
          have : (L : ℝ) ^ 2 * (cWblk 2 L Clb * r i) * (1 + cWblk 2 L Clb * r i) ^ (L ^ 2) ≤
              (L : ℝ) ^ 2 * (cWblk 2 L Clb * r i) * 2 :=
            mul_le_mul_of_nonneg_left hp2 (by positivity)
          nlinarith
        have hpw0 : 0 ≤ (1 + cWblk 2 L Clb * r i) ^ (L ^ 2) - 1 := by
          have : 1 ≤ (1 + cWblk 2 L Clb * r i) ^ (L ^ 2) := one_le_pow₀ (by linarith)
          linarith
        have hβi := H.hβp (i + 1) (by omega)
        have hβr' := H.hβr i hiN
        have hs2 := H.hs2 i
        have hO : eszO R M.core.c C₁w' mbar Clo m b μ₀ i =
            pl6cO L Clo (4 * C₁w' + 1) / 2 * (mbar * r i) := by
          unfold eszO eszSO; rw [heszR i hiN]; unfold sO pl6cO pl6As; ring
        unfold eszWp
        rw [hvwA i hiN, hO, heszR i hiN, div_le_iff₀ hβi]
        have hA0 : 0 ≤ 2 * histS (R.withMsq m) i t ^ 2 * V *
            ((L : ℝ) ^ 2 * (pl6cO L Clo (4 * C₁w' + 1) / 2 * (mbar * r i))) := by
          have := hr0 i; positivity
        calc 2 * histS (R.withMsq m) i t ^ 2 * ‖hBeta R m b μ₀ x i‖ * V *
              ((L : ℝ) ^ 2 * (pl6cO L Clo (4 * C₁w' + 1) / 2 * (mbar * r i)) *
                ((1 + cWblk 2 L Clb * r i) ^ (L ^ 2) - 1)) =
            (2 * histS (R.withMsq m) i t ^ 2 * V *
              ((L : ℝ) ^ 2 * (pl6cO L Clo (4 * C₁w' + 1) / 2 * (mbar * r i)))) *
              ((1 + cWblk 2 L Clb * r i) ^ (L ^ 2) - 1) * ‖hBeta R m b μ₀ x i‖ := by ring
          _ ≤ (2 * histS (R.withMsq m) i t ^ 2 * V *
              ((L : ℝ) ^ 2 * (pl6cO L Clo (4 * C₁w' + 1) / 2 * (mbar * r i)))) *
              (2 * (L : ℝ) ^ 2 * (cWblk 2 L Clb * r i)) *
                (64 / 49 * ‖hBeta R m b μ₀ x (i + 1)‖) := by gcongr
          _ = 2 * (L : ℝ) ^ 4 * pl6cO L Clo (4 * C₁w' + 1) * cWblk 2 L Clb * (64 / 49) *
                (histS (R.withMsq m) i t ^ 2) * V * (mbar * r i ^ 2) *
                ‖hBeta R m b μ₀ x (i + 1)‖ := by ring
          _ ≤ 2 * (L : ℝ) ^ 4 * pl6cO L Clo (4 * C₁w' + 1) * cWblk 2 L Clb * (64 / 49) *
                (6 / 5 * histS (R.withMsq m) (i + 1) t ^ 2) * V * (mbar * r i ^ 2) *
                ‖hBeta R m b μ₀ x (i + 1)‖ := by
              have : 0 ≤ 2 * (L : ℝ) ^ 4 * pl6cO L Clo (4 * C₁w' + 1) * cWblk 2 L Clb *
                (64 / 49) := by positivity
              have : 0 ≤ mbar * r i ^ 2 := by positivity
              gcongr
          _ = _ := by ring)
  -- assemble
  have hsplit : V * (pl6CEM M C₁k C₁w C₁w' Clo Clb * pl6NF j k₀ mbar r k) =
      V * (2 * Q1 2 * cQab * pl6aQ Bk (4 * C₁w + 1) * pl6NF j k₀ mbar r k) +
      V * (4 * (L : ℝ) ^ 4 * cWblk 2 L Clb * pl6cO L Clo (4 * C₁w' + 1) * (6 / 5) * (64 / 49) ^ 2 *
        pl6NF j k₀ mbar r k) +
      V * ((12 * KM4 2 Ccut2 * cQ / (L : ℝ) ^ 2 + 24 / 5 * (max M.core.B' 0 + M.core.ce) *
        KM4 2 Ccut2 * cS) * pl6NF j k₀ mbar r k) +
      V * (8 * (2 * ((L : ℝ) + 39) ^ 2 * 8 ^ 4) * (256 * cG / (L : ℝ) + 192 * cM) *
        pl6NF j k₀ mbar r k) +
      V * ((16 * M.core.ce * cM + 2560 * locK 2 ^ 2 * (4 * (2 * ((L : ℝ) + 39) ^ 2 * 9 ^ 4) *
        ((9 / 2 : ℝ) ^ 4 * (6 / 5) * cG / (L : ℝ) + 192 * cM)) +
        2560 * locK 2 ^ 2 * (2 * (L : ℝ) ^ 4 * pl6cO L Clo (4 * C₁w' + 1) * cWblk 2 L Clb *
          (64 / 49) * (6 / 5))) * pl6NF j k₀ mbar r k) := by
    rw [hcQd, hcSd, hcMd, hcGd]
    unfold pl6CEM pl6CE
    ring
  have hN : (if k < Nh then (0 : ℝ) else V * (27 / 5 * KM4 2 Ccut2 * cS *
      (mbar * (M.core.c * M.core.ε)))) =
      (if k < Nh then 0 else V * (pl6CNM L C₁w * (mbar * (M.core.c * M.core.ε)))) := by
    rw [hcSd]; unfold pl6CNM pl6CN; split_ifs <;> ring
  rw [hsplit, ← hN]
  linarith


set_option maxHeartbeats 8000000 in
/-- **The first summability condition for the explicit sequences** (see the module docstring). -/
theorem pl6_sum_leD6 {L : ℕ} [NeZero L] (M : MasterFacts L) {C₁k C₁w C₁w' Clo Clb : ℝ}
    (hC₁k : 0 ≤ C₁k) (hC₁w : 0 ≤ C₁w) (hC₁w' : 0 ≤ C₁w') (hClo : 0 ≤ Clo) (hClb : 0 ≤ Clb)
    (hθ : C₁k * (2 + 2 * (8 * cx M.core.κ M.core.cT) + 1) * (M.core.c * M.core.ε) ≤ 1 / 72)
    (hpow : (1 + cWblk 2 L Clb * (M.core.c * M.core.ε)) ^ (L ^ 2) ≤ 2)
    (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0)
    (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N)
    (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : (∀ jD ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ jD)))
    (lam : ℕ → ℂ) {cu mbar : ℝ} (hcu : 0 ≤ cu) (hmbar : 0 ≤ mbar)
    (x : Lam 2 L N) (hx : x ≠ 0) (h1 : 1 ≤ Obs.coal L (0 : Lam 2 L N) x)
    (hj : Obs.coal L (0 : Lam 2 L N) x ≤ Nh) (w : List (Dir 2)) (hwl : (w.length : ℝ) ≤ 2 * sXp x) :
    ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
        (2 * (Q1 2 * (cQab * e6KQ R M C₁k C₁w mbar cu m b μ₀ lam x k) *
          (PtCorr2.histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))⁻¹ ^ 2) +
          eszSw R M.core.c C₁w' mbar Clo Clb m b μ₀ lam x k +
          spE3 (Obs.coal L (0 : Lam 2 L N) x) (e6MQ R M C₁k C₁w mbar cu m b μ₀ lam x)
            (e6MS R M C₁w mbar m b μ₀ lam x) (fun _ => 3) (e6Nu R M Nh m b μ₀)
            (fun k => (w.length * (PtCorr2.histS (R.withMsq m) k
              (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) / (L : ℝ) ^ (k + 1))) ^ 2) k +
          2 * e6Del R M C₁k C₁w mbar cu m b μ₀ lam x w.length k * e6E R M m b μ₀ k *
            (PtCorr2.histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))⁻¹ ^ 2 +
          smE3 R m b μ₀ (Obs.coal L (0 : Lam 2 L N) x)
            (pdSz R m b μ₀ w (e6M4X R M C₁k C₁w mbar cu m b μ₀ lam x))
            (e6F R M C₁k C₁w mbar cu m b μ₀ lam x w.length)
            (eszWp R M.core.c C₁w' mbar Clo Clb m b μ₀ lam x) (tauSz R m b μ₀ M.core.ce) k) ≤
      pl6ce M C₁k C₁w C₁w' Clo Clb cu mbar * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 := by
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  set t : Flow2.Hist.Seq (Xs (R.withMsq m)) := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with ht
  have hg : ∀ i ≤ Nh, 0 < (t i).1 ∧ (t i).1 ≤ M.core.ε := fun i hi =>
    ⟨(hadm i hi).1, (hadm i hi).2.1⟩
  have hε0 : 0 ≤ M.core.ε := ((hg 0 (Nat.zero_le _)).1.trans_le (hg 0 (Nat.zero_le _)).2).le
  have hc0 : 0 ≤ M.core.c := by
    obtain ⟨_, _, _, _, hAH⟩ := M.core.abwHistD6
    obtain ⟨hcR, -⟩ := hAH N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
    rw [← hcR]; unfold cR cV cW cZ
    obtain ⟨H, -, -⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm
    have := H.hcmu; have := H.hC₂; positivity
  obtain ⟨Hap, -, -⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm
  have hθa0 : 0 ≤ kθ0 L M.core.A M.core.C₀a M.core.ηa := by
    unfold kθ0
    have := M.core.hA2
    exact mul_nonneg M.core.hC₀a (add_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _))
  obtain ⟨hct, -, -⟩ := M.tadD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  have hCE := pl6CEM_nonneg M hC₁k hC₁w hC₁w' hClo hClb hθa0 Hap.hcx hct
  set CE := pl6CEM M C₁k C₁w C₁w' Clo Clb with hCEd
  set CN := pl6CNM L C₁w with hCNd
  set V := vwB R m b μ₀ lam x with hVd
  have hV : 0 ≤ V := mul_nonneg (norm_nonneg _) (hg j hj).1.le
  set k₀ := pl6k0 M cu with hk₀d
  have hk₀ : 0 ≤ k₀ := by
    rw [hk₀d]; unfold pl6k0
    have := M.ιW_ge; have := M.core.hA2
    exact mul_nonneg hcu (pow_nonneg (by positivity) _)
  set r := pl6r R m b μ₀ M.core.c with hrd
  set g' : ℕ → ℝ := fun i => max (min (t i).1 M.core.ε) 0 with hg'd
  have hrg : ∀ i ≤ Nh, r i = M.core.c * g' i := fun i hi => by
    show M.core.c * max (t i).1 0 = M.core.c * max (min (t i).1 M.core.ε) 0
    rw [min_eq_left (hg i hi).2]
  have hr0 : ∀ i, 0 ≤ r i := fun i => mul_nonneg hc0 (le_max_right _ _)
  -- per scale
  have hitem := fun k (hk : k ∈ Finset.Ico j (Nh + 1)) =>
    pl6_item_leD6 M hC₁k hC₁w hC₁w' hClo hClb hθ hpow N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀
      hadm lam hcu hmbar x hx h1 hj w hwl k (mem_Ico.1 hk).1 (by have := (mem_Ico.1 hk).2; omega)
  refine (sum_le_sum hitem).trans ?_
  simp only [← hVd, ← hjd, ← hk₀d, ← hrd, ← hCEd, ← hCNd, ← ht]
  rw [sum_add_distrib]
  -- the `k = N_h` term
  have hNt : ∑ k ∈ Finset.Ico j (Nh + 1), (if k < Nh then (0 : ℝ) else
      V * (CN * (mbar * (M.core.c * M.core.ε)))) = V * (CN * (mbar * (M.core.c * M.core.ε))) := by
    rw [sum_Ico_succ_top hj, if_neg (lt_irrefl _)]
    rw [sum_eq_zero fun k hk => if_pos (mem_Ico.1 hk).2, zero_add]
  rw [hNt]
  -- the normal forms, summed with `pairLoop2_sum_le`
  have hG2 : ∑ k ∈ Finset.Ico j (Nh + 1), g' k ^ 2 ≤ pl6G2 L M.core.ε := by
    have hβL : 0 < betaL L := lt_of_lt_of_le (by norm_num) (betaL_ge (by have := M.core.hL49; omega))
    have hinc := M.gincD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
    have hS := sum_gsq_Ico_le (g := fun i => (t i).1) hβL hj (fun k hk hkn => hinc k hkn)
    have e : ∑ k ∈ Finset.Ico j Nh, g' k ^ 2 = ∑ k ∈ Finset.Ico j Nh, ((t k).1) ^ 2 :=
      sum_congr rfl fun k hk => by
        rw [hg'd]; dsimp only
        rw [min_eq_left (hg k (by have := (mem_Ico.1 hk).2; omega)).2,
          max_eq_left (hg k (by have := (mem_Ico.1 hk).2; omega)).1.le]
    rw [sum_Ico_succ_top hj, e]
    have h2 : g' Nh ^ 2 ≤ M.core.ε ^ 2 := by
      rw [hg'd]; dsimp only
      exact pow_le_pow_left₀ (le_max_right _ _) (max_le (min_le_right _ _) hε0) 2
    have h3 : 4 / betaL L * ((t Nh).1 - (t j).1) ≤ 4 * M.core.ε / betaL L := by
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hβL.le
      have := (hg Nh le_rfl).2; have := (hg j hj).1; nlinarith
    unfold pl6G2; linarith
  have hs : ∀ k ∈ Finset.Ico j (Nh + 1), V * (CE * pl6NF j k₀ mbar r k) ≤
      V * CE * pl6P j k₀ k + CE * (V * mbar) * ((M.core.c * g' k) ^ 2 +
        ∑ i ∈ Finset.Ico j k, (1 / 2 : ℝ) ^ (k - i) * ((M.core.c * g' i) ^ 2 +
          (M.core.c * g' i) * (M.core.c * g' k)) + (1 / 2 : ℝ) ^ (k - j) * (M.core.c * g' k)) := by
    intro k hk
    have hkN : k ≤ Nh := by have := (mem_Ico.1 hk).2; omega
    have hQ : pl6Q j r k ≤ ∑ i ∈ Finset.Ico j k, (1 / 2 : ℝ) ^ (k - i) * ((M.core.c * g' i) ^ 2 +
        (M.core.c * g' i) * (M.core.c * g' k)) := by
      unfold pl6Q
      refine sum_le_sum fun i hi => ?_
      have hiN : i ≤ Nh := by have := (mem_Ico.1 hi).2; omega
      rw [hrg i hiN]
      have : 0 ≤ (M.core.c * g' i) * (M.core.c * g' k) := by
        rw [← hrg i hiN, ← hrg k hkN]; exact mul_nonneg (hr0 i) (hr0 k)
      have : 0 ≤ (1 / 2 : ℝ) ^ (k - i) := by positivity
      nlinarith
    have hlast : 0 ≤ (1 / 2 : ℝ) ^ (k - j) * (M.core.c * g' k) := by
      rw [← hrg k hkN]; exact mul_nonneg (by positivity) (hr0 k)
    have hCm : 0 ≤ CE * (V * mbar) := by positivity
    unfold pl6NF pl6G0
    rw [hrg k hkN]
    have e : V * (CE * (pl6P j k₀ k + mbar * pl6Q j r k + mbar * (M.core.c * g' k) ^ 2)) =
        V * CE * pl6P j k₀ k + CE * (V * mbar) * ((M.core.c * g' k) ^ 2 + pl6Q j r k) := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_left (add_le_add_left hQ ((M.core.c * g' k) ^ 2)) hCm
    nlinarith
  have hsum := pairLoop2_sum_le (q := 1 / 2) (by norm_num) le_rfl hc0 hCE (mul_nonneg hV hmbar)
    (g := g') (fun i => le_max_right _ _) (fun i => max_le (min_le_right _ _) hε0)
    (s := fun k => V * (CE * pl6NF j k₀ mbar r k)) (seed := fun k => V * CE * pl6P j k₀ k) hG2 hs
  have hseed : ∑ k ∈ Finset.Ico j (Nh + 1), V * CE * pl6P j k₀ k ≤ 2 * (V * CE * k₀) := by
    have h := geom_decay_le (q := 1 / 2) (by norm_num) le_rfl (g := fun _ => (1 : ℝ))
      (fun _ => zero_le_one) (fun _ => le_rfl) j (Nh + 1)
    unfold pl6P
    have e : ∑ k ∈ Finset.Ico j (Nh + 1), V * CE * ((1 / 2 : ℝ) ^ (k - j) * k₀) =
        V * CE * k₀ * ∑ k ∈ Finset.Ico j (Nh + 1), (1 / 2 : ℝ) ^ (k - j) * 1 := by
      rw [mul_sum]; exact sum_congr rfl fun k _ => by ring
    rw [e]
    have : 0 ≤ V * CE * k₀ := by positivity
    nlinarith
  have hfin : V * (pl6ce M C₁k C₁w C₁w' Clo Clb cu mbar) = 2 * (V * CE * k₀) +
      CE * (V * mbar) * (6 * M.core.c ^ 2 * pl6G2 L M.core.ε + 2 * M.core.c * M.core.ε) +
      V * (CN * (mbar * (M.core.c * M.core.ε))) := by
    unfold pl6ce pl6Θ; rw [← hCEd, ← hCNd, ← hk₀d]; ring
  have e2 : pl6ce M C₁k C₁w C₁w' Clo Clb cu mbar * ‖Mmag R m b μ₀ lam j‖ * (t j).1 =
      V * pl6ce M C₁k C₁w C₁w' Clo Clb cu mbar := by
    rw [hVd]; show _ = (‖Mmag R m b μ₀ lam j‖ * (t j).1) * _; ring
  refine le_trans ?_ (le_of_eq e2.symm)
  rw [hfin]
  linarith




/-- The conclusion of `pairJointSizesP3_closedD6` at given constants (after the requirements). -/
def PJClosedPD6 {L : ℕ} [NeZero L] (M : MasterFacts L) (C₁v C₁k C₁w C₁w' Clo Clb : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
  ∀ m ∈ mRange L N, ∀ b μ₀,
    (∀ jD ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ jD)) →
  ∀ (lam : ℕ → ℂ) (cu ca cr mbar : ℝ), PairUnitSeed R Nh m b μ₀ lam cu → 0 ≤ cu → 0 < mbar →
    cr ≤ mbar → 0 ≤ ca →
    8 * (cu * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) ≤
      vck C₁v * ((4 * C₁v + 1) * mbar) →
    8 * (cu * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) ≤ (4 * C₁w + 1) * mbar →
    8 * (cu * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) ≤ (4 * C₁w' + 1) * mbar →
    PairJointSizesP3 R Nh m b μ₀ lam (oRed R m b μ₀ dxStd)
      (pl6ce M C₁k C₁w C₁w' Clo Clb cu mbar) ca cr

set_option maxHeartbeats 8000000 in
/-- **`pairJointSizesP3_closedD6` at the exported constants, without requirements** (see
`pairJointSizesP3_closedC`). -/
theorem pairJointSizesP3_closedCD6 {L : ℕ} [NeZero L] (M : MasterFacts L) :
    ∃ C₁v : ℝ, 0 ≤ C₁v ∧ PJClosedPD6 M C₁v M.core.C₁ka M.core.C₁wa M.core.C₁wa cwClo cwClb := by
  obtain ⟨hClo, hClb, -⟩ := cw_wpo_spec
  obtain ⟨-, hC₁k, -, hθ, -, -, -, hC₁w, -⟩ := M.core.hEaB
  have hAH := M.core.abwHistCD6
  obtain ⟨C₁v, hC₁v, H⟩ :=
    pairJointSizesP3_of_VSatD6 M M.core.hWpo hClo hClb hC₁k hC₁w hC₁w hAH hAH
  refine ⟨C₁v, hC₁v, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam cu ca cr mbar hU hcu hmbar
    hcr hca h8v h8 h8'
  exact H N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam cu _ ca cr mbar hU hmbar hcr hca
    h8v h8 h8' fun x hx h1 hj w _ hwl =>
      pl6_sum_leD6 M hC₁k hC₁w hC₁w hClo hClb hθ M.core.hpowF N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀
        hadm lam hcu hmbar.le x hx h1 hj w hwl

end

end Spin2
