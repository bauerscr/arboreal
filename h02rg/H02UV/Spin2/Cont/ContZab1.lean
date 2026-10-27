import Spin2.Pair.PairInitSizes

set_option autoImplicit false

/-!
# B3, T6, route (c): the pair-history `ab` activity at a scale `n` below coalescence

`pairInit_traj` runs `kab_hist` up to `j_x` with the weights at `j_x`. Here the same chain is run
up to any scale `1 ≤ n < j_{ab}(P)` for **any** pair of points `P`, with the natural weights at `n`:
`M_a = pM(P)_n = 2s_n²|β^P_n|`, `M_b = pM(ptsS P.b)_n` (the `σ_b` components along the history of
`P` are the `σ_a` components along the history of `(P.b, 0)`, `zab_mirror`).

**`zab_traj`**: from the one-point sizes `OneSz` at `P` and `(P.b, 0)` (vertex `zV0 b`), the two
`β` ratios, the coalescence invariant up to `n` and the constants of `kab_hist`, for the vertex
`zV b` at scale `n`:
* `A^{(|𝓑(X)|−4)_+}w_{ab}‖K_n(X)_{ab}‖ ≤ c₂r_n(2c_W)²` (`c₂ = 10B₂`);
* `A^{(|𝓑(X)|−4)_+}‖K_n(X)‖_{wM1} ≤ 8Br_n²(2c_W)`;
* `‖V_n(B)‖_{wM} ≤ 2`, `‖𝒲_n(B)‖_{wM} ≤ 2c_Wr_n`.
-/

set_option linter.unusedSectionVars false

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs FRD Flow2 Flow2.Hist Obs2 ENNReal Step2.D2

variable {L N : ℕ} [NeZero L]

/-- **The mirror for any pair of points**: the `σ_b` components along the history of `P` are the
`σ_a` components along the history of `(P.b, 0)`. -/
theorem zab_mirror (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (t : Hist.Seq (Xs R))
    (b : ℝ) (P : ObsPts 2 L N) (j : ℕ) :
    prjSt false (obsHist R P (obsInit .two (zV0 b) P) j t) =
      prjSt true (obsHist R (ptsS P.b) (obsInit .two (zV0 b) (ptsS P.b)) j t) := by
  rw [prj_obsHist R false (P := P) (P' := ptsS P.b) rfl,
    prj_obsHist R true (P := ptsS P.b) (P' := ptsS P.b) rfl,
    prjSt_obsInit_swap (zV0 b) rfl rfl (P := P) (P' := ptsS P.b) rfl]

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
variable {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

set_option maxHeartbeats 4000000 in
/-- **The pair-history sizes at a scale `n` below coalescence** (natural weights at `n`). -/
theorem zab_traj {C₀u ηu ε₀u C₁u : ℝ} (hKB : KObsBoundsU L R.A C₀u ηu ε₀u C₁u)
    (hC₀u : 0 ≤ C₀u) (hC₁u : 0 ≤ C₁u)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1) (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    (hρ0 : 0 ≤ R.ρ) (hρ8 : R.ρ ≤ 1 / 8)
    (t : Hist.Seq (Xs R)) (ht0 : (t 0).2.2 = 0) (ht : InDh Λ β δ κ cg cm cT ε Nh t)
    (b : ℝ) (P : ObsPts 2 L N) {n : ℕ} (hn1 : 1 ≤ n) (hnN : n ≤ Nh)
    (hinv : ∀ j ≤ n, ObsCoalInv P j (obsHist R P (obsInit .two (zV0 b) P) j t))
    {cW B : ℝ} (hcW : 1 ≤ cW) (hB : 0 ≤ B)
    (hX : ∀ j ≤ Nh, OneSz R P (zV0 b) t j (cR R Λ cm C₂ * (t j).1) cW B)
    (hS : ∀ j ≤ Nh, OneSz R (ptsS P.b) (zV0 b) t j (cR R Λ cm C₂ * (t j).1) cW B)
    (hrX : ∀ j < Nh,
      ‖betaTot2 (L := L) (N := N) j (histVO2 R P (obsInit .two (zV0 b) P) t j)‖ ≤
        64 / 49 * ‖betaTot2 (L := L) (N := N) (j + 1)
          (histVO2 R P (obsInit .two (zV0 b) P) t (j + 1))‖)
    (hrS : ∀ j < Nh,
      ‖betaTot2 (L := L) (N := N) j
        (histVO2 R (ptsS P.b) (obsInit .two (zV0 b) (ptsS P.b)) t j)‖ ≤
        64 / 49 * ‖betaTot2 (L := L) (N := N) (j + 1)
          (histVO2 R (ptsS P.b) (obsInit .two (zV0 b) (ptsS P.b)) t (j + 1))‖)
    (hε1 : cR R Λ cm C₂ * ε ≤ 1) (hεε : 2 * (cR R Λ cm C₂ * ε) ≤ ε₀u)
    (hkt1 : 8 * (cx κ cT + 8 * B + 10 * kB2 (kθ0 L R.A C₀u ηu) C₁u (cx κ cT) (8 * B)) *
      (cR R Λ cm C₂ * ε) ^ 3 ≤ 1)
    (hktε : 8 * (cx κ cT + 8 * B + 10 * kB2 (kθ0 L R.A C₀u ηu) C₁u (cx κ cT) (8 * B)) *
      (cR R Λ cm C₂ * ε) ^ 3 ≤ ε₀u)
    (hθ' : 8 * kθ0 L R.A C₀u ηu + 16 * C₁u * (cR R Λ cm C₂ * ε) +
      8 * C₁u * (8 * (cx κ cT + 8 * B + 10 * kB2 (kθ0 L R.A C₀u ηu) C₁u (cx κ cT) (8 * B)) *
        (cR R Λ cm C₂ * ε) ^ 3) ≤ 1 / 10) :
    0 < pM R P (zV0 b) t n ∧ 0 < pM R (ptsS P.b) (zV0 b) t n ∧
    (∀ X, IsConn n X → ENNReal.ofReal (R.A ^ (nb n X - 2 ^ 2)) *
      ((wM (pM R P (zV0 b) t n) (pM R (ptsS P.b) (zV0 b) t n)).ab *
        Tj 2 (L : ℝ) n (histS R n t)
          ((obsHist R P (obsInit .two (zV b) P) n t).K X : SA .two (Lam 2 L N)).ab) ≤
      ENNReal.ofReal (10 * kB2 (kθ0 L R.A C₀u ηu) C₁u (cx κ cT) (8 * B) *
        (cR R Λ cm C₂ * (t n).1) * (2 * cW) ^ 2)) ∧
    (∀ X, IsConn n X → ENNReal.ofReal (R.A ^ (nb n X - 2 ^ 2)) *
      oTo (wM1 (pM R P (zV0 b) t n) (pM R (ptsS P.b) (zV0 b) t n)) n (histS R n t)
        ((obsHist R P (obsInit .two (zV b) P) n t).K X) ≤
      ENNReal.ofReal (8 * B * (cR R Λ cm C₂ * (t n).1) ^ 2 * (2 * cW))) ∧
    (∀ q ∈ blockIdx (L := L) (N := N) n,
      oTo (wM (pM R P (zV0 b) t n) (pM R (ptsS P.b) (zV0 b) t n)) n (histS R n t)
        ((obsHist R P (obsInit .two (zV b) P) n t).V q) ≤ ENNReal.ofReal 2) ∧
    (∀ q ∈ blockIdx (L := L) (N := N) n,
      oTo (wM (pM R P (zV0 b) t n) (pM R (ptsS P.b) (zV0 b) t n)) n (histS R n t)
        ((obsHist R P (obsInit .two (zV b) P) n t).W q) ≤
        ENNReal.ofReal (cR R Λ cm C₂ * (t n).1 * (2 * cW))) := by
  set c := cR R Λ cm C₂ with hc
  set oX := obsInit .two (zV0 b) P with hoX
  set aX : ℕ → ℝ := fun j => pM R P (zV0 b) t j with haX
  set aS : ℕ → ℝ := fun j => pM R (ptsS P.b) (zV0 b) t j with haS
  set Ma := aX n with hMad
  set Mb := aS n with hMbd
  have hc2 : 2 ≤ c := two_le_cR R H.hcmu H.hC₂
  have hs : ∀ j, 0 < histS R j t := fun j => histS_pos' R hρ0 hρ8 t j
  have haX0 : ∀ j, 0 ≤ aX j := fun j => by
    show 0 ≤ 2 * histS R j t ^ 2 * _; positivity
  have haS0 : ∀ j, 0 ≤ aS j := fun j => by
    show 0 ≤ 2 * histS R j t ^ 2 * _; positivity
  have hMa : 0 < Ma := by
    have := (hX n hnN).1; have := hs n
    show 0 < 2 * histS R n t ^ 2 * _; positivity
  have hMb : 0 < Mb := by
    have := (hS n hnN).1; have := hs n
    show 0 < 2 * histS R n t ^ 2 * _; positivity
  set xx : ℕ → ℝ := fun j => aX j / Ma + aS j / Mb with hxx
  set mm : ℕ → ℝ := fun j => max (cW * xx j) 1 with hmmd
  set k1 : ℕ → ℝ := fun j => 8 * B * (c * (t j).1) ^ 2 * mm j with hk1d
  have hxx0 : ∀ j, 0 ≤ xx j := fun j => by
    have := haX0 j; have := haS0 j; show 0 ≤ aX j / Ma + aS j / Mb; positivity
  have hmm1 : ∀ j, 1 ≤ mm j := fun j => le_max_right _ _
  have hmm0 : ∀ j, 0 < mm j := fun j => lt_of_lt_of_le one_pos (hmm1 j)
  have hcxx : ∀ j, cW * xx j ≤ mm j := fun j => le_max_left _ _
  have hxxm : ∀ j, xx j ≤ mm j := fun j =>
    (le_mul_of_one_le_left (hxx0 j) hcW).trans (hcxx j)
  have hg0 : ∀ j ≤ Nh, 0 ≤ (t j).1 := fun j hj => (ht.1 j hj).1.le
  have hgε : ∀ j ≤ Nh, (t j).1 ≤ ε := fun j hj => (ht.1 j hj).2.1
  have hc0 : 0 ≤ c := by linarith
  have hr0 : ∀ j ≤ Nh, 0 ≤ c * (t j).1 := fun j hj => mul_nonneg hc0 (hg0 j hj)
  have hrε : ∀ j ≤ Nh, c * (t j).1 ≤ c * ε := fun j hj => mul_le_mul_of_nonneg_left (hgε j hj) hc0
  -- the mirror
  have hcmp : ∀ j, _ := fun j => prjSt_eq_cmp (zab_mirror R t b P j)
  -- the one-point components
  have hVa : ∀ j ≤ Nh, ∀ c' ∈ blockIdx (L := L) (N := N) j,
      Tj 2 (L : ℝ) j (histS R j t) ((obsHist R P oX j t).V c' : SA .two (Lam 2 L N)).a ≤
        ENNReal.ofReal (aX j) := fun j hj c' hc' => by
    rw [← oTo_wA]; exact vobs_le_of_shA2 R P (zV0 b) rfl t j (hs j) (hX j hj).2.1 c' hc'
  have hVb : ∀ j ≤ Nh, ∀ c' ∈ blockIdx (L := L) (N := N) j,
      Tj 2 (L : ℝ) j (histS R j t) ((obsHist R P oX j t).V c' : SA .two (Lam 2 L N)).b ≤
        ENNReal.ofReal (aS j) := fun j hj c' hc' => by
    rw [(hcmp j).1 c', ← oTo_wA]
    exact vobs_le_of_shA2 R (ptsS P.b) (zV0 b) rfl t j (hs j) (hS j hj).2.1 c' hc'
  have hWa : ∀ j ≤ Nh, ∀ c' ∈ blockIdx (L := L) (N := N) j,
      Tj 2 (L : ℝ) j (histS R j t) ((obsHist R P oX j t).W c' : SA .two (Lam 2 L N)).a ≤
        ENNReal.ofReal (cW * (c * (t j).1) * aX j) := fun j hj c' hc' => by
    rw [← oTo_wA]; exact (hX j hj).2.2.1 c' hc'
  have hWb : ∀ j ≤ Nh, ∀ c' ∈ blockIdx (L := L) (N := N) j,
      Tj 2 (L : ℝ) j (histS R j t) ((obsHist R P oX j t).W c' : SA .two (Lam 2 L N)).b ≤
        ENNReal.ofReal (cW * (c * (t j).1) * aS j) := fun j hj c' hc' => by
    rw [(hcmp j).2.1 c', ← oTo_wA]; exact (hS j hj).2.2.1 c' hc'
  have hKa : ∀ j ≤ Nh, ∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
      Tj 2 (L : ℝ) j (histS R j t) ((obsHist R P oX j t).K X : SA .two (Lam 2 L N)).a ≤
        ENNReal.ofReal (8 * cW * B * (c * (t j).1) ^ 2 * aX j) := fun j hj Z hZ => by
    rw [← oTo_wA]
    refine ((hX j hj).2.2.2 Z hZ).trans (le_of_eq (congrArg _ ?_))
    show _ = 8 * cW * B * (c * (t j).1) ^ 2 * (2 * histS R j t ^ 2 * _); ring
  have hKb' : ∀ j ≤ Nh, ∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
      Tj 2 (L : ℝ) j (histS R j t) ((obsHist R P oX j t).K X : SA .two (Lam 2 L N)).b ≤
        ENNReal.ofReal (8 * cW * B * (c * (t j).1) ^ 2 * aS j) := fun j hj X hX => by
    rw [(hcmp j).2.2 X, ← oTo_wA]
    refine ((hS j hj).2.2.2 X hX).trans (le_of_eq (congrArg _ ?_))
    show _ = 8 * cW * B * (c * (t j).1) ^ 2 * (2 * histS R j t ^ 2 * _); ring
  have hK1 : ∀ j ≤ Nh, ∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
      oTo (wM1 Ma Mb) j (histS R j t) ((obsHist R P oX j t).K X) ≤
        ENNReal.ofReal (8 * B * (c * (t j).1) ^ 2 * (cW * xx j)) := fun j hj X hX => by
    have hq : 0 ≤ 8 * cW * B * (c * (t j).1) ^ 2 := by
      have := hr0 j hj; positivity
    refine (reg_oTo_wM1_le hMa hMb j _ _ _ (mul_nonneg hq (haX0 j)) (mul_nonneg hq (haS0 j))
      (hKa j hj X hX) (hKb' j hj X hX)).trans (le_of_eq (congrArg _ ?_))
    show 8 * cW * B * (c * (t j).1) ^ 2 * aX j / Ma + 8 * cW * B * (c * (t j).1) ^ 2 * aS j / Mb =
      8 * B * (c * (t j).1) ^ 2 * (cW * (aX j / Ma + aS j / Mb))
    ring
  have hVo : ∀ j ≤ n, ∀ c' ∈ blockIdx (L := L) (N := N) j,
      oTo (wM Ma Mb) j (histS R j t) ((obsHist R P oX j t).V c') ≤
        ENNReal.ofReal (xx j) := fun j hj c' hc' =>
    oTo_wM_le_of_ab hMa hMb j _ _ ((hinv j hj).Vab c') (haX0 j) (haS0 j)
      (hVa j (by omega) c' hc') (hVb j (by omega) c' hc')
  have hWo : ∀ j ≤ n, ∀ c' ∈ blockIdx (L := L) (N := N) j,
      oTo (wM Ma Mb) j (histS R j t) ((obsHist R P oX j t).W c') ≤
        ENNReal.ofReal (c * (t j).1 * (cW * xx j)) := fun j hj c' hc' => by
    have hq : 0 ≤ cW * (c * (t j).1) := mul_nonneg (by linarith) (hr0 j (by omega))
    refine (oTo_wM_le_of_ab hMa hMb j _ _ ((hinv j hj).Wab c') (mul_nonneg hq (haX0 j))
      (mul_nonneg hq (haS0 j)) (hWa j (by omega) c' hc') (hWb j (by omega) c' hc')).trans
        (le_of_eq (congrArg _ ?_))
    show cW * (c * (t j).1) * aX j / Ma + cW * (c * (t j).1) * aS j / Mb =
      c * (t j).1 * (cW * (aX j / Ma + aS j / Mb))
    ring
  -- the ratio
  have haXr : ∀ j < Nh, aX j ≤ 2 * aX (j + 1) := fun j hj => by
    have h1 := histS_sq_ratio R hρ0 hρ8 t j
    have h2 := hrX j hj
    have h3 := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    have h4 : 0 ≤ histS R (j + 1) t ^ 2 * ‖betaTot2 (L := L) (N := N) (j + 1)
        (histVO2 R P (obsInit .two (zV0 b) P) t (j + 1))‖ := by positivity
    show 2 * histS R j t ^ 2 * _ ≤ 2 * (2 * histS R (j + 1) t ^ 2 * _)
    nlinarith
  have haSr : ∀ j < Nh, aS j ≤ 2 * aS (j + 1) := fun j hj => by
    have h1 := histS_sq_ratio R hρ0 hρ8 t j
    have h2 := hrS j hj
    have h3 := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    have h4 : 0 ≤ histS R (j + 1) t ^ 2 * ‖betaTot2 (L := L) (N := N) (j + 1)
        (histVO2 R (ptsS P.b) (obsInit .two (zV0 b) (ptsS P.b)) t (j + 1))‖ := by positivity
    show 2 * histS R j t ^ 2 * _ ≤ 2 * (2 * histS R (j + 1) t ^ 2 * _)
    nlinarith
  have hmm' : ∀ j < n, mm j ≤ 2 * mm (j + 1) := fun j hj => by
    have h1 : xx j ≤ 2 * xx (j + 1) := by
      have e1 := div_le_div_of_nonneg_right (haXr j (by omega)) hMa.le
      have e2 := div_le_div_of_nonneg_right (haSr j (by omega)) hMb.le
      show aX j / Ma + aS j / Mb ≤ 2 * (aX (j + 1) / Ma + aS (j + 1) / Mb)
      rw [mul_div_assoc] at e1 e2
      linarith
    refine max_le ?_ (by linarith [hmm1 (j + 1)])
    have := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ cW)
    linarith [hcxx (j + 1)]
  have hrm : ∀ j < n, c * (t j).1 ≤ mm j := fun j hj =>
    ((hrε j (by omega)).trans hε1).trans (hmm1 j)
  have hk10 : ∀ j, 0 ≤ k1 j := fun j => by
    have := hmm0 j; show 0 ≤ 8 * B * (c * (t j).1) ^ 2 * mm j; positivity
  -- the unreduced `ab` chain
  have hab := kab_hist R hKB hC₀u hC₁u hSB hV hm hβ hδ1 H P (wM Ma Mb) (wM_sub Ma Mb)
    ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) oX
    (obsInit_isObs .two _ _) (obsLocInv_init .two _ _) (obsSymInv_init .two _ _) t
    (fun X => by simp [hoX, obsInit]) n hnN
    ⟨fun i hi => ht.1 i (by omega), fun i hi => ht.2 i (by omega)⟩
    (fun j hj X hX => (hinv j hj.le).Kab X hX) mm k1 (8 * B) (by positivity) hmm0 hmm' hk10
    (fun j _ => le_rfl) hrm hε1 hεε hkt1 hktε hθ'
    (fun j hj c' hc' => (hVo j hj.le c' hc').trans (ENNReal.ofReal_le_ofReal (hxxm j)))
    (fun j hj c' hc' => (hWo j hj.le c' hc').trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (hcxx j) (hr0 j (by omega)))))
    (fun j hj X hX => by
      rw [wOne_wM]
      refine (hK1 j (by omega) X hX).trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_left (hcxx j) (by have := hr0 j (by omega); positivity))
    n le_rfl
  have hxxj : xx n = 2 := by
    show aX n / Ma + aS n / Mb = 2
    rw [← hMad, ← hMbd, div_self hMa.ne', div_self hMb.ne']; norm_num
  have hmj : mm n = 2 * cW := by
    show max (cW * xx n) 1 = 2 * cW
    rw [hxxj, mul_comm]; exact max_eq_left (by linarith)
  obtain ⟨hVeq, hWeq, hKeq⟩ := obsHist_zV0 R P t b ht0 n hn1
  refine ⟨hMa, hMb, fun X hX => ?_, fun X hX => ?_, fun q hq => ?_, fun q hq => ?_⟩
  · rw [hKeq]
    refine (hab X hX).trans (le_of_eq ?_)
    rw [hmj]
  · rw [hKeq]
    refine (hK1 n hnN X hX).trans (le_of_eq ?_)
    rw [hxxj, mul_comm cW 2]
  · rw [hVeq]
    exact (hVo n le_rfl q hq).trans (le_of_eq (by rw [hxxj]))
  · rw [hWeq]
    refine (hWo n le_rfl q hq).trans (le_of_eq ?_)
    rw [hxxj, mul_comm cW 2]

end Traj

end

end Spin2
