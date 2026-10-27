import Spin2.Master.MasterAllVStep
import PtCorr2.Last.LastAB4

/-!
# The top step `N_h → N_h + 1` of the `ab` chain under the master constants

**`MasterCore.vstepTopD`** (domain form; `MasterCore.vstepTop` along admissible trajectories): the
`V`-step `MasterCore.vstepD` at `n = N_h + 1` (the gradient sizes from `gradV_hist_leT`, the facts
at `N_h` from `hist_vstep_factsT`, the `S` sizes at `N_h` from `sxo_hist_ab_leL`), together with the
top `𝒲` and `K` steps (`wobs_hist_stepABT`, `kobs_hist_stepABLT` with the `wM` sizes at `N_h` of
`obs_histFromABL_wM`): for the same data as `vstepD`,

  `‖V_{N_h+1}(B)‖_{wM(M_{a,N_h+1}, M_b)} ≤ m̄`,
  `‖𝒲_{N_h+1}(B)‖_{wM(M_{a,N_h}, M_b)} ≤ (4C₁w+1)cǧ_{N_h}m̄`,
  `A^{(|𝓑(U)|-4)_+}‖K_{N_h+1}(U)‖_{wM(M_{a,N_h}, M_b)} ≤ (4C₁w+1)m̄`

(`K_w/L ≤ 1/12`, `C₁w cε ≤ 1/12`, `θ₀ ≤ 1/72`, `C₁(3 + 16c_x)cε ≤ 1/72`, `32Bc²ε² ≤ vck ≤ 1`).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2 Obs Obs2

set_option maxHeartbeats 8000000 in
/-- **The top step of the `ab` chain under the master constants** (domain form). -/
theorem MasterCore.vstepTopD {L : ℕ} [NeZero L] (D : MasterCore L) :
    ∃ C₁w : ℝ, 0 ≤ C₁w ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = D.ℓ → R.A = D.A → R.ρ = D.ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
    ∀ m ∈ mRange L N, ∀ b μ₀, (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) D.κ D.cm D.cT D.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) →
    ∀ (P : Obs2.ObsPts 2 L N), P.a ≠ P.b → ∀ w : List (Dir 2), pathEnd P.a w = P.b →
      (w.length : ℝ) ≤ 2 * ((supNorm (P.a - P.b) : ℕ) : ℝ) →
    ∀ (Ma : ℕ → ℝ) (Mb : ℝ), (∀ j, 0 < Ma j) → 0 < Mb →
    ∀ (j₀ : ℕ) (o₀ : ObsSt .two L N), o₀.IsObs → ObsLocInv P j₀ o₀ → ObsSymInv j₀ o₀ →
      ObsAnchInv P j₀ o₀ → ObsVabInv P o₀ → (∀ b', (o₀.V b' : SA .two (Lam 2 L N)).ab = 0) →
      2 * ((supNorm (P.a - P.b) : ℕ) : ℝ) ≤ (L : ℝ) ^ (j₀ + 1) →
    ∀ n, j₀ ≤ Nh → n = Nh + 1 → (∀ j, j₀ ≤ j → j < n → Ma j ≤ 2 * Ma (j + 1)) →
    ∀ mbar : ℝ, 0 < mbar →
    (∀ j, j₀ ≤ j → j < n → ∀ b' ∈ blockIdx (L := L) (N := N) j,
      oTo (wM (Ma j) Mb) j (histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((obsHistFrom (R.withMsq m) P j₀ o₀ j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).V b') ≤
        ENNReal.ofReal mbar) →
    (∀ b' ∈ blockIdx (L := L) (N := N) j₀, oTo (wM (Ma j₀) Mb) j₀
      (histS (R.withMsq m) j₀ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) (o₀.W b') ≤
      ENNReal.ofReal ((4 * C₁w + 1) * (D.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j₀).1) *
        mbar)) →
    ∀ k₀ : ℝ, 0 ≤ k₀ →
    (∀ X, IsConn j₀ X → ENNReal.ofReal ((R.withMsq m).A ^ (nb j₀ X - 2 ^ 2)) *
      oTo (wM (Ma j₀) Mb) j₀
        (histS (R.withMsq m) j₀ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) (o₀.K X) ≤
        ENNReal.ofReal k₀) →
    8 * k₀ ≤ vck C₁w * ((4 * C₁w + 1) * mbar) →
    ∀ ρ : ℝ, (∀ b' ∈ blockIdx (L := L) (N := N) n,
      ‖LocObs.mass2 ((obsHistFrom (R.withMsq m) P j₀ o₀ n
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).V b' : SA .two (Lam 2 L N)).ab‖ ≤ ρ) →
    (Ma n * Mb)⁻¹ * (ρ * (histS (R.withMsq m) n (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) *
      histS (R.withMsq m) n (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))) ≤ mbar / 2 →
    (∀ b' ∈ blockIdx (L := L) (N := N) n,
      oTo (wM (Ma n) Mb) n (histS (R.withMsq m) n (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((obsHistFrom (R.withMsq m) P j₀ o₀ n (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).V b') ≤
        ENNReal.ofReal mbar) ∧
    (∀ c' ∈ blockIdx (L := L) (N := N) n,
      oTo (wM (Ma Nh) Mb) n (histS (R.withMsq m) n (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((obsHistFrom (R.withMsq m) P j₀ o₀ n (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).W c') ≤
        ENNReal.ofReal ((4 * C₁w + 1) * (D.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) *
          mbar)) ∧
    (∀ U, IsConn n U → ENNReal.ofReal ((R.withMsq m).A ^ (nb n U - 2 ^ 2)) *
      oTo (wM (Ma Nh) Mb) n (histS (R.withMsq m) n (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((obsHistFrom (R.withMsq m) P j₀ o₀ n (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).K U) ≤
        ENNReal.ofReal ((4 * C₁w + 1) * mbar)) := by
  obtain ⟨hθa0, hθa⟩ : 0 ≤ kθ0 L D.A D.C₀a D.ηa ∧ kθ0 L D.A D.C₀a D.ηa ≤ 1 / 72 := by
    refine ⟨?_, (D.hAa D.hLa).2⟩
    unfold kθ0
    have := D.hA2
    exact mul_nonneg D.hC₀a (add_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _))
  obtain ⟨ε₀, C₁k, hε₀, hC₁k, hKB, hsm, hεε, hεk, hBr, C₁w, ε₁, hC₁w, hε₁, hWB, hC₁ε, hε₁',
    hA2v, hBrv⟩ := D.hEv D.hLa D.hAa
  refine ⟨C₁w, hC₁w, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hD P hab w hw hwl Ma Mb hMa hMb j₀ o₀
    h0 hl0 hs0 ha0 hvab hz hsL n hjNh hn hMa2 mbar hmbar hVo hW0 k₀ hk₀ hK0 h8 ρ hρ hρm
  subst hn
  have hjn : j₀ ≤ Nh + 1 := by omega
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8, -, hCN⟩ := id D.hC2
  set R' := R.withMsq m with hR'
  obtain ⟨H, hm1, F1⟩ := D.hXm N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm
  obtain ⟨hV, hVL⟩ := (hCN N R hP hi0 hRℓ hRA hRρ hN Nh hNh).2.2.2.2.2.2.2.2.2 m hm
  have hmN : |R'.msq| * ((L : ℝ) ^ Nh) ^ 2 ≤ 1 := by
    have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by have := D.hL49; omega)
    have h1 := msq_horizon (L := (L : ℝ)) (by linarith only [hL2]) hm.2 (Nh := Nh) (k := 0)
      (by omega)
    simp only [pow_zero, one_pow, inv_one] at h1
    show |m| * ((L : ℝ) ^ Nh) ^ 2 ≤ 1
    rw [abs_of_pos hm.1]
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hm.1.le) h1
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by linarith only [hL2]) (by omega)) 2
  have hRA' : R'.A = D.A := hRA
  have hcR : cR R' ((L : ℝ) ^ 2) D.cm D.C₂x = D.c := by
    rw [D.hc]; exact cR_congr (show R.ℓ = D.ℓ from hRℓ) _ _ _
  have hSB' : StepBounds L R'.A D.C₀x D.ηx D.εsx D.CKx D.C₂x D.CDx D.Cqx D.Clx D.cSx := by
    rw [hRA']; exact D.hSBx
  have hβ2 := betaL_ge (by have := D.hL49; omega : 8 ≤ L)
  have hβ0 : 0 ≤ betaL L := by linarith
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  have ht := inDh_rg_of_D R' F1 hD Nh le_rfl
  have hti : ∀ i ≤ Nh, Flow2.Hist.InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) D.κ D.cg D.cm D.cT D.ε i t :=
    fun i hi => inDh_rg_of_D R' F1 hD i hi
  have hL0 : (0 : ℝ) < L := Nat.cast_pos.2 (by have := D.hL49; omega)
  have hKB' : KObsBoundsABL L R'.A D.C₀a D.ηa ε₀ C₁k := by rw [hRA']; exact hKB
  have hθa0' : 0 ≤ kθ0 L R'.A D.C₀a D.ηa := by rw [hRA']; exact hθa0
  have hθa' : kθ0 L R'.A D.C₀a D.ηa ≤ 1 / 72 := by rw [hRA']; exact hθa
  have hBr' : 32 * kB (kθ0 L R'.A D.C₀a D.ηa) C₁k (8 * cx D.κ D.cT) *
      (cR R' ((L : ℝ) ^ 2) D.cm D.C₂x * D.ε) ^ 2 ≤ 1 := by rw [hRA', hcR]; exact hBr
  -- the weights
  have hMb' : ∀ j, 0 < (fun _ : ℕ => Mb) j := fun _ => hMb
  have hw0 : 0 < Ma j₀ * Mb := mul_pos (hMa j₀) hMb
  have hm' : ∀ j, j₀ ≤ j → j < Nh + 1 → Ma j * Mb / (Ma j₀ * Mb) * mbar ≤
      2 * (Ma (j + 1) * Mb / (Ma j₀ * Mb) * mbar) := by
    intro j hj hjn
    have h1 := hMa2 j hj hjn
    have e1 : Ma j * Mb / (Ma j₀ * Mb) * mbar = Ma j * (Mb * mbar / (Ma j₀ * Mb)) := by ring
    have e2 : 2 * (Ma (j + 1) * Mb / (Ma j₀ * Mb) * mbar) =
        2 * Ma (j + 1) * (Mb * mbar / (Ma j₀ * Mb)) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have hW0' : ∀ b' ∈ blockIdx (L := L) (N := N) j₀, oTo (wM (Ma j₀) ((fun _ : ℕ => Mb) j₀)) j₀
      (histS R' j₀ t) (o₀.W b') ≤ ENNReal.ofReal ((4 * C₁w + 1) *
        (cR R' ((L : ℝ) ^ 2) D.cm D.C₂x * (t j₀).1) * (fun _ : ℕ => mbar) j₀) := by
    rw [hcR]; exact hW0
  have hvck := vck_le_one hC₁w
  have hvck0 := vck_pos hC₁w
  have hcW0 : 0 < 4 * C₁w + 1 := by linarith
  have h8' : 8 * k₀ ≤ 1 * ((4 * C₁w + 1) * (fun _ : ℕ => mbar) j₀) := by
    have : vck C₁w * ((4 * C₁w + 1) * mbar) ≤ 1 * ((4 * C₁w + 1) * mbar) :=
      mul_le_mul_of_nonneg_right hvck (by positivity)
    exact h8.trans this
  have hM := obs_histFromABL_wM R' hKB' hC₁k 1 zero_le_one hWB hC₁w hSB' hV hm1 hβ0
    (by norm_num : (1 / 2 : ℝ) ≤ 1) H P Ma (fun _ => Mb) hMa hMb' o₀ h0 hl0 hs0 ha0
    t Nh le_rfl ht hθa0' hθa' (by rw [hcR]; exact hsm)
    (by rw [hcR]; exact D.hcε) (by rw [hcR]; exact hεε) (by rw [hcR]; exact hεk) hBr' D.hLwa
    (by rw [hcR]; exact hC₁ε) (by rw [hcR]; exact hε₁') (fun _ => mbar) (fun _ => hmbar)
    (fun j hj hjn => hm' j hj (by omega))
    (fun j hj hjn => hVo j hj (by omega)) hW0' k₀ hk₀ hK0 h8'
  -- notation of the chain
  set θb := kθ0 L R'.A D.C₀a D.ηa + C₁k * (2 + 2 * (8 * cx D.κ D.cT) + 1) *
    (cR R' ((L : ℝ) ^ 2) D.cm D.C₂x * D.ε) with hθbd
  set B := kB (kθ0 L R'.A D.C₀a D.ηa) C₁k (8 * cx D.κ D.cT) with hBd
  set r := fun j => cR R' ((L : ℝ) ^ 2) D.cm D.C₂x * (t j).1 with hrd
  set cWc := 4 * C₁w + 1 with hcWc
  set lamM := fun i => Ma i * (fun _ : ℕ => Mb) i / (Ma j₀ * (fun _ : ℕ => Mb) j₀) with hlamM
  have hcR0 : 0 ≤ cR R' ((L : ℝ) ^ 2) D.cm D.C₂x := by
    unfold cR cV cW cZ; have := H.hcmu; have := H.hC₂; positivity
  have hcε : 0 ≤ D.c * D.ε := by rw [← hcR]; exact mul_nonneg hcR0 H.hε.le
  have hr0 : ∀ i ≤ Nh, 0 ≤ r i := fun i hi => mul_nonneg hcR0 (ht.1 i hi).1.le
  have hrε : ∀ i ≤ Nh, r i ≤ D.c * D.ε := fun i hi => by
    rw [← hcR]; exact mul_le_mul_of_nonneg_left (ht.1 i hi).2.1 hcR0
  have hθb : 8 * θb ≤ 2 / 9 := by
    have h1 : C₁k * (2 + 2 * (8 * cx D.κ D.cT) + 1) * (cR R' ((L : ℝ) ^ 2) D.cm D.C₂x * D.ε) ≤
        1 / 72 := by rw [hcR]; exact hsm
    rw [hθbd]; linarith
  have hθb0 : 0 ≤ θb := by
    have : 0 ≤ C₁k * (2 + 2 * (8 * cx D.κ D.cT) + 1) * (cR R' ((L : ℝ) ^ 2) D.cm D.C₂x * D.ε) := by
      have := H.hcx; have := H.hε; positivity
    rw [hθbd]; linarith
  have hB0 : 0 ≤ B := by
    have hcb : 0 ≤ 8 * cx D.κ D.cT := by have := H.hcx; positivity
    have h1 := mul_nonneg hθa0' hcb
    have h2 := mul_nonneg hC₁k (by positivity : (0 : ℝ) ≤ 8 + 2 * (8 * cx D.κ D.cT) +
      (8 * cx D.κ D.cT) ^ 2)
    rw [hBd]; unfold kB; linarith
  have hBrv' : 32 * B * (D.c * D.ε) ^ 2 ≤ vck C₁w := by
    rw [hBd, hRA']; exact hBrv
  have hlam : ∀ i, 0 < lamM i := fun i =>
    div_pos (mul_pos (hMa i) hMb) (mul_pos (hMa j₀) hMb)
  have hlam0 : lamM j₀ = 1 := div_self (mul_pos (hMa j₀) hMb).ne'
  -- the `K'` sizes with `c_k = vck`
  have hkL := kseqF_leL (θ := 8 * θb) (B := B) (ck := vck C₁w) (r := r)
    (m := fun i => cWc * (lamM i * (fun _ : ℕ => mbar) i)) (j₀ := j₀) (k₀ := k₀) Nh
    (by positivity) hB0 hvck0.le (fun i => mul_nonneg hcW0.le (mul_nonneg (hlam i).le hmbar.le))
    (fun j hj hjn => by
      have h1 : 8 * θb * vck C₁w ≤ 2 / 9 * vck C₁w := mul_le_mul_of_nonneg_right hθb hvck0.le
      have hr2 : r j ^ 2 ≤ (D.c * D.ε) ^ 2 :=
        pow_le_pow_left₀ (hr0 j hjn.le) (hrε j hjn.le) 2
      have h2 : 8 * B * r j ^ 2 ≤ 8 * B * (D.c * D.ε) ^ 2 := mul_le_mul_of_nonneg_left hr2 (by positivity)
      linarith)
    (fun j hj hjn => by
      have := hm' j hj (by omega)
      show cWc * (lamM j * mbar) ≤ 2 * (cWc * (lamM (j + 1) * mbar))
      have e1 : lamM j * mbar = Ma j * Mb / (Ma j₀ * Mb) * mbar := rfl
      have e2 : lamM (j + 1) * mbar = Ma (j + 1) * Mb / (Ma j₀ * Mb) * mbar := rfl
      rw [e1, e2]
      nlinarith)
    (by
      show 8 * k₀ ≤ vck C₁w * (cWc * (lamM j₀ * mbar))
      rw [hlam0, one_mul]; exact h8)
  -- the per-scale source sizes
  set Q₀ := vck C₁w * (cWc * mbar) with hQ₀
  set S₀ := (L : ℝ) ^ 2 * sO 2 L (D.c * D.ε) mbar (cWc * (D.c * D.ε) * mbar) with hS₀
  have hQ₀0 : 0 ≤ Q₀ := by positivity
  have hcN0 : (0 : ℝ) ≤ Step2.cNear 2 L := by unfold Step2.cNear; exact Nat.cast_nonneg _
  have hQ10 : (0 : ℝ) ≤ Step2.Q1 2 := by have := Step2.one_le_Q1 (d := 2) one_le_two; linarith
  have hS₀0 : 0 ≤ S₀ := by
    rw [hS₀]; unfold sO
    generalize Step2.Q1 2 = q at *
    generalize Step2.cNear 2 L = cn at *
    positivity
  have hK : ∀ i, j₀ ≤ i → i < Nh + 1 → ∀ X, IsSmall i X →
      Tj 2 (L : ℝ) i (histS R' i t) (hKR R' P j₀ o₀ t i X : SA .two (Lam 2 L N)).ab ≤
        ENNReal.ofReal (Ma i * Mb * Q₀) := by
    intro i hi hin X hX
    have hF := if h : i < Nh then
      hist_vstep_facts R' hSB' hV hm1 hβ0 (by norm_num : (1 / 2 : ℝ) ≤ 1) H P o₀ hl0 hs0
        ha0 t i hi h (hti i (by omega))
    else
      hist_vstep_factsT R' hSB' hV hm1 hβ0 (by norm_num : (1 / 2 : ℝ) ≤ 1) H P o₀ hl0 hs0
        ha0 hVL hmN t i hi (by omega) (hti i (by omega))
    have hKi := hF.2.2.2.2.2.2.2 (wM (Ma i) Mb) (wM_sub _ _) _ (hM i hi (by omega)).2.2 X hX
    have hT := Tj_ab_le_of_oTo_wM' (hMa i) hMb i (histS R' i t) (hKR R' P j₀ o₀ t i X) hKi
    refine hT.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (mul_pos (hMa i) hMb).le))
    have h1 := hkL i hi (by omega)
    have hl := hlam i
    rw [mul_div_assoc', div_le_iff₀ hl]
    calc 8 * kseqF (8 * θb) B r (fun i => cWc * (lamM i * (fun _ : ℕ => mbar) i)) j₀ k₀ i
        ≤ vck C₁w * (cWc * (lamM i * mbar)) := h1
      _ = Q₀ * lamM i := by rw [hQ₀]; ring
  have hS : ∀ i, j₀ ≤ i → i < Nh + 1 → ∀ b' ∈ blockIdx (L := L) (N := N) i,
      Tj 2 (L : ℝ) (i + 1) (histS R' (i + 1) t)
        (SXO i (histCovO R' t i) (hVR R' P j₀ o₀ t i) (hWR R' P j₀ o₀ t i)
          (Step2.Bp (L := L) (N := N) i b') : SA .two (Lam 2 L N)).ab ≤
        ENNReal.ofReal (Ma i * Mb * S₀) := by
    intro i hi hin b' hb'
    have hWi := (hM i hi (by omega)).2.1
    have H' := if h : i < Nh then (sxo_hist_ab_le R' D.hSX hSB' hV hm1 hβ0 (by norm_num : (1 / 2 : ℝ) ≤ 1) H P
      (hMa i) hMb o₀ h0 hl0 hs0 ha0 t i hi h (hti i (by omega)) mbar (cWc * r i * mbar)
      hmbar.le (by have := hr0 i (by omega); positivity) (hVo i hi hin) hWi b' hb').1
    else by
      obtain rfl : i = Nh := by omega
      exact (sxo_hist_ab_leL R' D.hSX hSB' hV hm1 hβ0 (by norm_num : (1 / 2 : ℝ) ≤ 1) H hVL hmN P
        (hMa i) hMb o₀ h0 hl0 hs0 ha0 t hi (hti i le_rfl) mbar (cWc * r i * mbar)
        hmbar.le (by have := hr0 i le_rfl; positivity) (hVo i hi hin) hWi b' hb').1
    refine H'.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (mul_pos (hMa i) hMb).le))
    rw [hS₀]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    unfold sO
    have hri := hrε i (by omega)
    have hr0i := hr0 i (by omega)
    have h1 : cR R' ((L : ℝ) ^ 2) D.cm D.C₂x * (t i).1 * mbar ≤ D.c * D.ε * mbar :=
      mul_le_mul_of_nonneg_right hri hmbar.le
    have h2 : cWc * r i * mbar ≤ cWc * (D.c * D.ε) * mbar :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hri hcW0.le) hmbar.le
    have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * Step2.cNear 2 L * Step2.Q1 2 ^ 2)
    have h4 := mul_le_mul_of_nonneg_left h2 hQ10
    linarith
  -- the gradient bound
  have hρ0' : 0 ≤ R'.ρ := by rw [show R'.ρ = D.ρ from hRρ]; linarith
  have hρ8' : R'.ρ ≤ 1 / 8 := by rw [show R'.ρ = D.ρ from hRρ]; linarith
  have hL8 : 2 ^ (2 + 3) + 8 * 2 < L := by have := D.hL49; omega
  have hG := gradV_hist_leT R' hSB' hV hm1 hβ0 (by norm_num : (1 / 2 : ℝ) ≤ 1) H (by omega) hρ0' hρ8'
    hL8 Ccut2_spec.1 Ccut2_spec.2 (cSn := (cSm2 : ℝ)) (cNn := (cNb2 : ℝ))
    (fun i b' hb' => by exact_mod_cast cSm2_spec L N i b' hb')
    (fun i x s hs => by exact_mod_cast cNb2_spec L N i x s hs)
    P hab w hw hwl o₀ hl0 hs0 ha0 hvab hz hVL hmN t hjn le_rfl hti hsL (fun i => Ma i * Mb)
    (fun i => mul_pos (hMa i) hMb)
    (fun i hi hin => by
      have := hMa2 i hi hin
      show Ma i * Mb ≤ 2 * (Ma (i + 1) * Mb)
      nlinarith)
    hQ₀0 hS₀0 hK hS
  -- the final bound
  have hz' : ∀ b', Grassmann.ε (o₀.V b' : SA .two (Lam 2 L N)).ab = 0 := fun b' => by
    rw [hz b', map_zero]
  have hsn : ObsSymInv (Nh + 1) (obsHistFrom R' P j₀ o₀ (Nh + 1) t) :=
    obsSymInv_histFrom' R' P hs0 t hjn (fun i _ hi => hist_validL R' hV hVL t i (by omega))
  have hℓn := histS_pos' R' hρ0' hρ8' t (Nh + 1)
  set G := 4 * ((2 * Obs2.KG 2 Ccut2 4 + 3 * (9 / 8 : ℝ) ^ 2 + 2 * KM4 2 Ccut2) *
      (2 * (cNb2 : ℝ) * (cSm2 : ℝ) * Q₀) +
    (2 * Obs2.KG 2 Ccut2 4 + 3 + 2 * KM4 2 Ccut2) * (2 * (L : ℝ) ^ 2 * S₀)) with hGd
  have hGe : G = 4 * (vA1 C₁w * vck C₁w) * mbar + 4 * vA2 L C₁w * (D.c * D.ε) * mbar := by
    rw [hGd, hQ₀, hS₀]; unfold vA1 vA2 sO; rw [hcWc]; ring
  have hGle : G ≤ mbar / 2 := by
    rw [hGe]
    have h1 := mul_le_mul_of_nonneg_right (four_vA1_vck hC₁w) hmbar.le
    have h2 : 4 * vA2 L C₁w * (D.c * D.ε) ≤ 1 / 4 := by linarith
    have h3 := mul_le_mul_of_nonneg_right h2 hmbar.le
    linarith
  have hwn : 0 < Ma (Nh + 1) * Mb := mul_pos (hMa (Nh + 1)) hMb
  refine ⟨?_, ?_, ?_⟩
  · refine vbound_scale R' P hab o₀ hvab ha0 hz' t hjn hsn (hMa (Nh + 1)) hMb hℓn {P.a} hρ
      (fun b' hb' => Or.inl ?_) (?_ : (Ma (Nh + 1) * Mb)⁻¹ *
        (ρ * (histS R' (Nh + 1) t * histS R' (Nh + 1) t) + Ma (Nh + 1) * Mb * G) ≤ mbar)
    · rw [← hVR_ab R' P j₀ o₀ t (Nh + 1) b']; exact hG b' hb'
    · rw [mul_add, ← mul_assoc (Ma (Nh + 1) * Mb)⁻¹ (Ma (Nh + 1) * Mb) G, inv_mul_cancel₀ hwn.ne',
        one_mul]
      exact (add_le_add hρm hGle).trans (by linarith)
  · -- the top `𝒲` step
    have hWN := (hM Nh hjNh le_rfl).2.1
    have hrN0 := hr0 Nh le_rfl
    have hrNε := hrε Nh le_rfl
    have key := wobs_hist_stepABT R' hWB hSB' hV hm1 hβ0 (by norm_num : (1 / 2 : ℝ) ≤ 1) H P
      (wM (Ma Nh) Mb) (wM_sub _ _) o₀ h0 hl0 hs0 ha0 hVL hmN t Nh hjNh rfl ht
      (by rw [hcR]; exact hε₁') mbar (cWc * r Nh * mbar) hmbar.le (by positivity)
      (hVo Nh hjNh (by omega)) hWN
    intro c' hc'
    refine (key c' hc').trans (ENNReal.ofReal_le_ofReal ?_)
    have hC₁r : C₁w * r Nh ≤ 1 / 12 := (mul_le_mul_of_nonneg_left hrNε hC₁w).trans hC₁ε
    have hKw := D.hLwa
    have hcW1 : 1 ≤ cWc := by rw [hcWc]; linarith
    have e : (4 * C₁w + 1) * (D.c * (t Nh).1) * mbar = cWc * r Nh * mbar := by
      rw [hcWc, hrd]; dsimp only; rw [hcR]
    rw [e]
    have hX0 : 0 ≤ cWc * r Nh * mbar := by positivity
    have h1 : (D.Kwa / L + C₁w * r Nh) * (cWc * r Nh * mbar) ≤ 1 / 6 * (cWc * r Nh * mbar) :=
      mul_le_mul_of_nonneg_right (by linarith) hX0
    have h2 : C₁w * r Nh * mbar ≤ 1 / 4 * (cWc * r Nh * mbar) := by
      have hc4 : C₁w ≤ 1 / 4 * cWc := by rw [hcWc]; linarith
      have := mul_le_mul_of_nonneg_right hc4 (mul_nonneg hrN0 hmbar.le)
      calc C₁w * r Nh * mbar = C₁w * (r Nh * mbar) := by ring
        _ ≤ 1 / 4 * cWc * (r Nh * mbar) := this
        _ = 1 / 4 * (cWc * r Nh * mbar) := by ring
    linarith
  · -- the top `K` step
    have hWN := (hM Nh hjNh le_rfl).2.1
    have hKN := (hM Nh hjNh le_rfl).2.2
    have hrN0 := hr0 Nh le_rfl
    have hrNε := hrε Nh le_rfl
    have hcW1 : 1 ≤ cWc := by rw [hcWc]; linarith
    have hlN := hlam Nh
    have hk8N := hkL Nh hjNh le_rfl
    set kN := vck C₁w * (cWc * mbar) / 8 with hkNd
    have hKo' : ∀ X, IsConn Nh X → ENNReal.ofReal (R'.A ^ (nb Nh X - 2 ^ 2)) *
        oTo (wM (Ma Nh) Mb) Nh (histS R' Nh t) ((obsHistFrom R' P j₀ o₀ Nh t).K X) ≤
        ENNReal.ofReal kN := by
      intro X hX
      refine (hKN X hX).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [div_le_iff₀ hlN, hkNd]
      have : 8 * kseqF (8 * θb) B r (fun i => cWc * (lamM i * (fun _ : ℕ => mbar) i)) j₀ k₀ Nh ≤
          vck C₁w * (cWc * (lamM Nh * mbar)) := hk8N
      nlinarith
    have hεk' : (8 * cx D.κ D.cT + vck C₁w) * (cR R' ((L : ℝ) ^ 2) D.cm D.C₂x * D.ε) ≤ ε₀ := by
      rw [hcR]
      have := mul_le_mul_of_nonneg_right (add_le_add_left hvck (8 * cx D.κ D.cT)) hcε
      linarith
    have key := kobs_hist_stepABLT R' hKB' hSB' hV hm1 hβ0 (by norm_num : (1 / 2 : ℝ) ≤ 1) H P
      (wM (Ma Nh) Mb) (wM_sub _ _) ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) o₀ h0 hl0 hs0 ha0 hVL hmN
      t Nh hjNh rfl ht (vck C₁w) (cWc * mbar) kN hvck0.le (by positivity) (by positivity)
      (by rw [hcR]; exact D.hcε) (by rw [hcR]; exact hεε) hεk' (by rw [hkNd]; linarith)
      (fun b' hb' => (hVo Nh hjNh (by omega) b' hb').trans
        (ENNReal.ofReal_le_ofReal (le_mul_of_one_le_left hmbar.le hcW1)))
      (fun b' hb' => (hWN b' hb').trans (ENNReal.ofReal_le_ofReal (le_of_eq (by ring))))
      hKo'
    intro U hU
    refine (key U hU).trans (ENNReal.ofReal_le_ofReal ?_)
    have hθa'' : kθ0 L R'.A D.C₀a D.ηa ≤ 1 / 72 := hθa'
    have hsm' : C₁k * (2 + 2 * (8 * cx D.κ D.cT) + vck C₁w) * (cR R' ((L : ℝ) ^ 2) D.cm D.C₂x * (t Nh).1)
        ≤ 1 / 72 := by
      have h1 : C₁k * (2 + 2 * (8 * cx D.κ D.cT) + vck C₁w) ≤ C₁k * (2 + 2 * (8 * cx D.κ D.cT) + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hC₁k
      have h2 : cR R' ((L : ℝ) ^ 2) D.cm D.C₂x * (t Nh).1 ≤ D.c * D.ε := hrNε
      have h3 := mul_le_mul h1 h2 hrN0 (by have := H.hcx; positivity)
      rw [hcR] at h3 ⊢
      have := hsm
      linarith
    have hB2 : kB (kθ0 L R'.A D.C₀a D.ηa) C₁k (8 * cx D.κ D.cT) * (cR R' ((L : ℝ) ^ 2) D.cm D.C₂x *
        (t Nh).1) ^ 2 ≤ vck C₁w / 32 := by
      have hr2 : r Nh ^ 2 ≤ (D.c * D.ε) ^ 2 := pow_le_pow_left₀ hrN0 hrNε 2
      have := mul_le_mul_of_nonneg_left hr2 hB0
      have := hBrv'
      show B * r Nh ^ 2 ≤ _
      linarith
    have hm0 : 0 ≤ cWc * mbar := by positivity
    have hk0 : 0 ≤ 8 * kN := by positivity
    have e8 : 8 * kN = vck C₁w * (cWc * mbar) := by rw [hkNd]; ring
    have k1 : (kθ0 L R'.A D.C₀a D.ηa + C₁k * (2 + 2 * (8 * cx D.κ D.cT) + vck C₁w) *
        (cR R' ((L : ℝ) ^ 2) D.cm D.C₂x * (t Nh).1)) * (8 * kN) ≤ (1 / 36) * (8 * kN) :=
      mul_le_mul_of_nonneg_right (by linarith) hk0
    have k2 : kB (kθ0 L R'.A D.C₀a D.ηa) C₁k (8 * cx D.κ D.cT) * (cR R' ((L : ℝ) ^ 2) D.cm D.C₂x *
        (t Nh).1) ^ 2 * (cWc * mbar) ≤ vck C₁w / 32 * (cWc * mbar) :=
      mul_le_mul_of_nonneg_right hB2 hm0
    have k3 : vck C₁w * (cWc * mbar) ≤ cWc * mbar := by
      have := mul_le_mul_of_nonneg_right hvck hm0; linarith
    show _ ≤ cWc * mbar
    have k4 : vck C₁w / 32 * (cWc * mbar) ≤ 1 / 32 * (cWc * mbar) :=
      mul_le_mul_of_nonneg_right (by linarith) hm0
    have k5 : 1 / 36 * (vck C₁w * (cWc * mbar)) ≤ 1 / 36 * (cWc * mbar) :=
      mul_le_mul_of_nonneg_left k3 (by norm_num)
    linarith


end

end Spin2
