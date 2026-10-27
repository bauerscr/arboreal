import Spin2.Cont.ContZab1
import Spin2.Cont.ContK2c

set_option autoImplicit false

/-!
# B3, T6, route (c): the pair-history sizes at `ms` along `D_ε` (item (a) of `Z_{ab}`)

**`MasterFacts.zab_sizes`**: the `D_ε` version (no `Admissible`) of the pair-history bounds at a
scale `1 ≤ n ≤ N_h` below coalescence of any pair `P` (`zab_traj` under the master constants):
in the natural weights `wM(pM(P)_n, pM(ptsS P.b)_n)` and for the vertex `zV b`,
* `A^{(|𝓑(X)|−4)_+}w_{ab}‖K_n(X)_{ab}‖ ≤ c_{ab}r_n(2c_W)²` (`c_{ab} = M.k2cab`, the constant of
  `kabCond`, `r_n = cǧ_n`);
* `A^{(|𝓑(X)|−4)_+}‖K_n(X)‖_{wM1} ≤ 8B r_n²(2c_W)`, `‖V_n(B)‖_{wM} ≤ 2`, `‖𝒲_n(B)‖_{wM} ≤ 2c_Wr_n`.
Inputs from `M`: `cw2_relBaseD` (one-point sizes along `D_ε`), `bt2_ratio` with `relGD`/`loopD`,
`rpb_coalInv` (coalescence invariant up to `n`, `n < j_{ab}(P)`, no `j_{ab} ≤ N_h` needed).
-/

set_option linter.unusedSectionVars false

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs FRD Flow2 Flow2.Hist Obs2 ENNReal Step2.D2

variable {L : ℕ} [NeZero L]

namespace MasterFacts

variable (M : MasterFacts L)

set_option maxHeartbeats 8000000 in
/-- **The pair-history sizes at a scale `n` below coalescence, along `D_ε`.** -/
theorem zab_sizes (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN3 : 3 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ)
    (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    (P : ObsPts 2 L N) {n : ℕ} (hn1 : 1 ≤ n) (hnN : n ≤ Nh) (hnc : n < Obs.coal L P.a P.b) :
    0 < pM (R.withMsq m) P (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) n ∧
    0 < pM (R.withMsq m) (ptsS P.b) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) n ∧
    (∀ X, IsConn n X → ENNReal.ofReal ((R.withMsq m).A ^ (nb n X - 2 ^ 2)) *
      ((wM (pM (R.withMsq m) P (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) n)
          (pM (R.withMsq m) (ptsS P.b) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) n)).ab *
        Tj 2 (L : ℝ) n (histS (R.withMsq m) n (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          ((obsHist (R.withMsq m) P (obsInit .two (zV b) P) n
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).K X : SA .two (Lam 2 L N)).ab) ≤
      ENNReal.ofReal (M.k2cab * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ n).1) *
        (2 * M.core.cWo) ^ 2)) ∧
    (∀ X, IsConn n X → ENNReal.ofReal ((R.withMsq m).A ^ (nb n X - 2 ^ 2)) *
      oTo (wM1 (pM (R.withMsq m) P (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) n)
          (pM (R.withMsq m) (ptsS P.b) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) n)) n
        (histS (R.withMsq m) n (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((obsHist (R.withMsq m) P (obsInit .two (zV b) P) n
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).K X) ≤
      ENNReal.ofReal (8 * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ n).1) ^ 2 *
        (2 * M.core.cWo))) ∧
    (∀ q ∈ blockIdx (L := L) (N := N) n,
      oTo (wM (pM (R.withMsq m) P (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) n)
          (pM (R.withMsq m) (ptsS P.b) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) n)) n
        (histS (R.withMsq m) n (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((obsHist (R.withMsq m) P (obsInit .two (zV b) P) n
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).V q) ≤ ENNReal.ofReal 2) ∧
    (∀ q ∈ blockIdx (L := L) (N := N) n,
      oTo (wM (pM (R.withMsq m) P (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) n)
          (pM (R.withMsq m) (ptsS P.b) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) n)) n
        (histS (R.withMsq m) n (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((obsHist (R.withMsq m) P (obsInit .two (zV b) P) n
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).W q) ≤
        ENNReal.ofReal (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ n).1 *
          (2 * M.core.cWo))) := by
  have hN2 : 2 ≤ N := by omega
  have hNh0 : 0 < Nh := by omega
  have hb0 : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  set R' := R.withMsq m with hR'
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8, -, hCN⟩ := id M.core.hC2
  obtain ⟨H, hm1, F1⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm
  obtain ⟨hV, hVL⟩ := (hCN N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm
  have hRA' : R'.A = M.core.A := hRA
  have hρ0' : 0 ≤ R'.ρ := by rw [show R'.ρ = M.core.ρ from hRρ]; exact hρpos.le
  have hρ8' : R'.ρ ≤ 1 / 8 := by rw [show R'.ρ = M.core.ρ from hRρ]; exact hρ8
  have hcR : cR R' ((L : ℝ) ^ 2) M.core.cm M.core.C₂x = M.core.c := by
    rw [M.core.hc]; exact cR_congr (show R.ℓ = M.core.ℓ from hRℓ) _ _ _
  have hSB' : StepBounds L R'.A M.core.C₀x M.core.ηx M.core.εsx M.core.CKx M.core.C₂x M.core.CDx
      M.core.Cqx M.core.Clx M.core.cSx := by rw [hRA']; exact M.core.hSBx
  have ht := inDh_rg_of_D R' F1 hD Nh le_rfl
  have hβ2 := betaL_ge (show 8 ≤ L by have := M.core.hL49; omega)
  have hβ0 : 0 ≤ betaL L := by linarith
  have hL8 : 2 ^ (2 + 3) + 8 * 2 < L := by have := M.core.hL49; norm_num; omega
  have hmu : Obs2.OCoup2.mua (zV0 b) ≠ 0 := zV_mua_ne hb0
  have hcW : 1 ≤ M.core.cWo := M.core.consts_nonneg.2.2.2.2.2.1
  have hBk : 0 ≤ M.core.Bk := M.core.consts_nonneg.2.2.2.2.2.2.1
  obtain ⟨hε₀u, hC₁u, hKBu, h1u, h2u, h3u, h4u⟩ :=
    Classical.choose_spec (Classical.choose_spec M.k2_cab_spec)
  have hcab : M.k2cab = 10 * kB2 (kθ0 L M.core.A M.core.C₀u M.core.ηu) (Classical.choose
      (Classical.choose_spec M.k2_cab_spec)) (cx M.core.κ M.core.cT) (8 * M.core.Bk) := rfl
  -- one-point sizes
  have hOS : ∀ Q : ObsPts 2 L N, ∀ j ≤ Nh,
      OneSz R' Q (zV0 b) t j (cR R' ((L : ℝ) ^ 2) M.core.cm M.core.C₂x * (t j).1) M.core.cWo
        M.core.Bk := by
    intro Q j hj
    rw [hcR]
    obtain ⟨h1, h2, h3, h4⟩ := M.cw2_relBaseD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD Q
      (zV0 b) rfl hmu hNh0 j hj
    exact ⟨h1, h2, h3, h4⟩
  have hrat : ∀ Q : ObsPts 2 L N, ∀ j < Nh,
      ‖Obs2.betaTot2 (L := L) (N := N) j
        (Obs2.histVO2 R' Q (Obs2.obsInit .two (zV0 b) Q) t j)‖ ≤
      64 / 49 * ‖Obs2.betaTot2 (L := L) (N := N) (j + 1)
        (Obs2.histVO2 R' Q (Obs2.obsInit .two (zV0 b) Q) t (j + 1))‖ := fun Q j hj =>
    bt2_ratio R Q (zV0 b) (by omega)
      (M.relGD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD Q (zV0 b) hmu)
      (M.loopD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD Q (zV0 b)).2.2 hj
  -- the coalescence invariant up to `n`
  have hinv : ∀ j ≤ n, ObsCoalInv P j (obsHist R' P (obsInit .two (zV0 b) P) j t) := by
    intro j hj
    have h := rpb_coalInv R' P (m := 0) (obsInit_isObs .two (zV0 b) P)
      (coalInv_init .two (V := zV0 b) ⟨rfl, rfl, rfl, rfl⟩ P) hL8
      (n := min (Obs.coal L P.a P.b) (Nh + 1)) ((min_le_right _ _).trans (by omega)) t
      (fun k hk x y hxy => by
        have hkN : k ≤ Nh := by have := min_le_right (Obs.coal L P.a P.b) (Nh + 1); omega
        have HI := rawInv_histU R' hV hVL t k (by omega)
        exact (covU R' hV hVL hkN HI).1.range (by omega) x y hxy)
      j (Nat.zero_le _) (by omega) (le_min (by omega) (by omega))
    rw [obsHistFrom_zero] at h
    exact h
  have key := zab_traj R' (by rw [hRA']; exact hKBu) M.core.hC₀u hC₁u hSB' hV hm1 hβ0
    (by norm_num : (1 / 2 : ℝ) ≤ 1) H hρ0' hρ8' t (traj_zero_X R m b μ₀) ht b P hn1 hnN hinv
    hcW hBk (hOS P) (hOS (ptsS P.b)) (hrat P) (hrat (ptsS P.b))
    (by rw [hcR]; exact M.core.hcε) (by rw [hcR]; exact h1u) (by rw [hcR, hRA']; exact h2u)
    (by rw [hcR, hRA']; exact h3u) (by rw [hcR, hRA']; exact h4u)
  have hcab' : 10 * kB2 (kθ0 L R'.A M.core.C₀u M.core.ηu) (Classical.choose
      (Classical.choose_spec M.k2_cab_spec)) (cx M.core.κ M.core.cT) (8 * M.core.Bk) =
      M.k2cab := by rw [hcab, hRA']
  rw [hcR, hcab'] at key
  exact key

end MasterFacts

end

end Spin2
