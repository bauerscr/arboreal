import Spin2.Master.Master
import PtCorr2.Obs.ObsHistRelW

/-!
# The relative `σ_a` flow under the master constants (Case (1))

**`Spin2.thm_obs_rel`**: for every choice `c_P(L, A, c_R, c_x) ≥ 0` of the constant of the
`ℓ¹` product bound, the constants of the master construction (`thm_flow_master`: `thm:flow`,
`sec:spin`, `thm:beta`) can be chosen such that, in addition, along every admissible trajectory
(`N ≥ 3`, `N_h = N − 2`, `m² ∈ mRange`) and for every observable initial state with
`𝒲_0 = K_0 = 0` and point shares `V_0(B)_a = β₀1_{a∈B}ψ̄_a`, `β₀ ≠ 0`: if the product parts satisfy
`ProdBd` with ratio `2L^{-2}` and constant `c_P(L, A, c_R, c_x)`, then for `j ≤ N_h`

  `|β_j − β₀∏_{k<j}(1 − 𝔫_k)| ≤ (e^{c_δ∑_{k<j} r_k²} − 1)|β₀∏_{k<j}(1 − 𝔫_k)|`,
  `c_δ∑_{k<N_h} r_k² ≤ 1/8`,

the relative one-step bound `|β_{j+1} − β_j(1−𝔫_j)| ≤ c_δr_j²|β_j(1−𝔫_j)|`, `|β_j| > 0` and phase
alignment `∑_B|c_j(B) − β_j1_{a∈B}| ≤ 6c_δ(∑_{k<j} r_k²)|β_j|`; `r_j = c_R ǧ_j`,
`𝔫_k = frakN` with the explicit couplings `kapH`. So `β_j = β₀∏_{k<j}(1−𝔫_k)(1 + O(∑_{k<j}ǧ_k²))`
with a uniform `O`. The only remaining input is `ProdBd`.

The bulk inputs of `obs_hist_rel_w` are discharged: `c_g = cgbF L c_R` (`cn_le_cR`,
`cd_le_cR`), `B_τ = 9ℓ⁴/128 ≤ 9c_R/1024`, `cg ε ≤ 1/6 ≤ β/4` (`betaL_ge`, `L ≥ 49`), and the
requirements on `ε` (`relEReq`) are passed to the master construction.
-/

set_option linter.unusedSectionVars false

namespace Spin2

open Step Step2 PtCorr2 Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs FRD Flow2 Flow2.Hist Filter Topology

/-! ### The constants -/

/-- The rescaled bulk constant `c_g`. -/
def cgbF (L : ℕ) (c : ℝ) : ℝ := ((L : ℝ) ^ 2 + 2) + (3 * betaL L + 7 + 9 * c) / c ^ 2

/-- The relative error constant `c_δ`. -/
def cdF (C₀ η : ℝ) (cPf : ℕ → ℝ → ℝ → ℝ → ℝ) (L : ℕ) (A c c' C₁ C₁w : ℝ) : ℝ :=
  3 * (16 * (8 * (csN 2 : ℝ)) * (3 * C₁w + 1) * kB (kθ0 L A C₀ η) C₁ (8 * c') +
    3 * cPf L A c c' * (3 * C₁w + 1) + 4 * (9 * c / 1024) * cgbF L c * (1 + cgbF L c))

/-- The requirement on `ε` (`c = c_R`, `c' = c_x`): the smallness conditions of
`obs_hist_rel_w` for the constants `cgbF`, `cdF`. -/
def relEReq (C₀ η Kw : ℝ) (Lo : ℕ) (cPf : ℕ → ℝ → ℝ → ℝ → ℝ) (L : ℕ) (A c c' ε : ℝ) : Prop :=
  ∀ [NeZero L], Lo ≤ L → obsAReq C₀ η Lo L A →
    ∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧ KObsBounds L A C₀ η ε₀ C₁ ∧
      C₁ * (2 + 2 * (8 * c') + 64 * kB (kθ0 L A C₀ η) C₁ (8 * c')) * (c * ε) ≤ 1 / 72 ∧
      c * ε ≤ 1 ∧ c * ε ≤ ε₀ ∧ (8 * c' + 64 * kB (kθ0 L A C₀ η) C₁ (8 * c')) * (c * ε) ≤ ε₀ ∧
      ∃ C₁w ε₁ : ℝ, 0 ≤ C₁w ∧ 0 < ε₁ ∧ WObsBounds L Kw C₁w ε₁ ∧ C₁w * (c * ε) ≤ 1 / 12 ∧
        c * ε ≤ ε₁ ∧ betaL L * ε ≤ 1 / 2 ∧ cgbF L c * c * ε ≤ 1 / 7 ∧
        4 * (9 * c / 1024) * cgbF L c * c * ε ≤ 1 / 2 ∧
        cdF C₀ η cPf L A c c' C₁ C₁w * c ^ 2 * (4 / betaL L) * ε ≤ 1 / 8

theorem relEReq_ev {C₀ η Kw : ℝ} {L₀ Lo : ℕ} (cPf : ℕ → ℝ → ℝ → ℝ → ℝ)
    (hw : ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ C₁ ε₁ : ℝ, 0 ≤ C₁ ∧ 0 < ε₁ ∧ WObsBounds L Kw C₁ ε₁)
    (hLo : L₀ ≤ Lo) (L : ℕ) (A c c' : ℝ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), relEReq C₀ η Kw Lo cPf L A c c' ε := by
  by_cases hL : L ≠ 0 ∧ Lo ≤ L
  · haveI : NeZero L := ⟨hL.1⟩
    by_cases hA : obsAReq C₀ η Lo L A
    · obtain ⟨⟨ε₀, C₁, hε₀, hC₁, hKB⟩, -⟩ := hA hL.2
      obtain ⟨C₁w, ε₁, hC₁w, hε₁, hWB⟩ := hw L (hLo.trans hL.2)
      filter_upwards [ev_lin (C₁ * (2 + 2 * (8 * c') + 64 * kB (kθ0 L A C₀ η) C₁ (8 * c')) * c)
          (by norm_num : (0 : ℝ) < 1 / 72), ev_lin c one_pos, ev_lin c hε₀,
        ev_lin ((8 * c' + 64 * kB (kθ0 L A C₀ η) C₁ (8 * c')) * c) hε₀,
        ev_lin (C₁w * c) (by norm_num : (0 : ℝ) < 1 / 12), ev_lin c hε₁,
        ev_lin (betaL L) (by norm_num : (0 : ℝ) < 1 / 2),
        ev_lin (cgbF L c * c) (by norm_num : (0 : ℝ) < 1 / 7),
        ev_lin (4 * (9 * c / 1024) * cgbF L c * c) (by norm_num : (0 : ℝ) < 1 / 2),
        ev_lin (cdF C₀ η cPf L A c c' C₁ C₁w * c ^ 2 * (4 / betaL L))
          (by norm_num : (0 : ℝ) < 1 / 8)]
        with ε h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
      intro _ _ _
      exact ⟨ε₀, C₁, hε₀, hC₁, hKB, by rw [← mul_assoc]; exact h1, h2, h3,
        by rw [← mul_assoc]; exact h4, C₁w, ε₁, hC₁w, hε₁, hWB, by rw [← mul_assoc]; exact h5,
        h6, h7, h8, h9, h10⟩
    · exact Eventually.of_forall fun _ _ _ hA' => absurd (fun (_ : NeZero L) => hA') hA
  · exact Eventually.of_forall fun _ inst hLL _ => absurd ⟨inst.out, hLL⟩ hL

theorem one_le_cM : (1 : ℝ) ≤ cM := by
  have : 0 < Fintype.card (Mono 2) := Fintype.card_pos_iff.2 ⟨Mono.c⟩
  exact_mod_cast this

section Consts

variable {L N : ℕ} [NeZero L] (R : RGPar 2 L N) {Λ cm C₂ : ℝ}

theorem cV_le_cR (hcmu : 0 ≤ cmu Λ cm) (hC₂ : 0 ≤ C₂) : cV R Λ cm + 3 ≤ cR R Λ cm C₂ := by
  unfold cR cW
  have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hC₂) (sq_nonneg (cV R Λ cm))
  linarith

theorem ell_parts (hcmu : 0 ≤ cmu Λ cm) :
    R.ℓ ^ 2 * cmu Λ cm ≤ cV R Λ cm / 2 ∧ R.ℓ ^ 4 ≤ cV R Λ cm / 8 ∧
      R.ℓ ^ 2 * cZ R ≤ 2 * cV R Λ cm / 49 ∧ cZ R ≤ 1 + cV R Λ cm := by
  have hM := one_le_cM
  have h2 : 0 ≤ R.ℓ ^ 2 := sq_nonneg _
  have hz : cZ R = 16 * R.ℓ ^ 2 / 49 := rfl
  have hzc : 0 ≤ cZ R := by rw [hz]; positivity
  have hV : cV R Λ cm = cM * R.ℓ ^ 2 * (2 * cmu Λ cm + 2 * cZ R) + 8 * R.ℓ ^ 4 := rfl
  have a1 : 0 ≤ R.ℓ ^ 2 * cmu Λ cm := mul_nonneg h2 hcmu
  have a2 : 0 ≤ R.ℓ ^ 2 * cZ R := mul_nonneg h2 hzc
  have b1 : R.ℓ ^ 2 * (2 * cmu Λ cm + 2 * cZ R) ≤ cM * R.ℓ ^ 2 * (2 * cmu Λ cm + 2 * cZ R) := by
    have : 0 ≤ R.ℓ ^ 2 * (2 * cmu Λ cm + 2 * cZ R) := by positivity
    nlinarith
  have h4 : 0 ≤ R.ℓ ^ 4 := by positivity
  have e4 : R.ℓ ^ 2 * cZ R = 16 / 49 * R.ℓ ^ 4 := by rw [hz]; ring
  refine ⟨by nlinarith, by nlinarith, by nlinarith, ?_⟩
  have : R.ℓ ^ 2 ≤ 1 + R.ℓ ^ 4 := by nlinarith [sq_nonneg (R.ℓ ^ 2 - 1)]
  rw [hz]; nlinarith

/-- `ℓ²L²(c_μ + 3c_z) + ℓ⁴ ≤ (L² + 1)c_R`. -/
theorem cn_le_cR (hcmu : 0 ≤ cmu Λ cm) (hC₂ : 0 ≤ C₂) :
    R.ℓ ^ 2 * (L : ℝ) ^ 2 * (cmu Λ cm + 3 * cZ R) + R.ℓ ^ 4 ≤ ((L : ℝ) ^ 2 + 1) * cR R Λ cm C₂ := by
  obtain ⟨a1, a2, a3, -⟩ := ell_parts R hcmu
  have hc := cV_le_cR R hcmu hC₂
  have hV0 : 0 ≤ cV R Λ cm := by
    have : 0 ≤ R.ℓ ^ 4 := by positivity
    linarith
  have hL2 : 0 ≤ (L : ℝ) ^ 2 := sq_nonneg _
  have e : R.ℓ ^ 2 * (L : ℝ) ^ 2 * (cmu Λ cm + 3 * cZ R) =
      (L : ℝ) ^ 2 * (R.ℓ ^ 2 * cmu Λ cm + 3 * (R.ℓ ^ 2 * cZ R)) := by ring
  rw [e]
  have h1 : R.ℓ ^ 2 * cmu Λ cm + 3 * (R.ℓ ^ 2 * cZ R) ≤ cV R Λ cm := by linarith
  have h2 := mul_le_mul_of_nonneg_left h1 hL2
  have h3 : cV R Λ cm ≤ cR R Λ cm C₂ := by linarith
  nlinarith

/-- `3β + 16c_μℓ² + 20c_z ≤ 3β + 7 + 9c_R`. -/
theorem cd_le_cR (hcmu : 0 ≤ cmu Λ cm) (hC₂ : 0 ≤ C₂) (β : ℝ) :
    3 * β + 16 * cmu Λ cm * R.ℓ ^ 2 + 20 * cZ R ≤ 3 * β + 7 + 9 * cR R Λ cm C₂ := by
  obtain ⟨a1, a2, -, -⟩ := ell_parts R hcmu
  have hc := cV_le_cR R hcmu hC₂
  have hz : cZ R = 16 * R.ℓ ^ 2 / 49 := rfl
  have h' : R.ℓ ^ 2 ≤ (1 + R.ℓ ^ 4) / 2 := by nlinarith [sq_nonneg (R.ℓ ^ 2 - 1)]
  have : 20 * cZ R ≤ 7 + cV R Λ cm := by rw [hz]; nlinarith
  nlinarith

theorem two_le_cR (hcmu : 0 ≤ cmu Λ cm) (hC₂ : 0 ≤ C₂) : 2 ≤ cR R Λ cm C₂ := by
  have hc := cV_le_cR R hcmu hC₂
  have : 0 ≤ cV R Λ cm := by
    have := (ell_parts R hcmu).2.1; have : 0 ≤ R.ℓ ^ 4 := by positivity
    linarith
  linarith

end Consts

/-- `β(L) ≥ 2/3` for `L ≥ 8`. -/
theorem betaL_ge {L : ℕ} (hL : 8 ≤ L) : 2 / 3 ≤ betaL L := by
  unfold betaL
  have h8 : Real.log 8 ≤ Real.log L := Real.log_le_log (by norm_num) (by exact_mod_cast hL)
  have e8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have h2 := Real.log_two_gt_d9
  have hπ := Real.pi_lt_d2
  have hπ0 := Real.pi_pos
  rw [mul_div_assoc', le_div_iff₀ (by positivity)]
  nlinarith

set_option maxHeartbeats 4000000 in
/-- **The relative `σ_a` flow under the master constants**, conditional only on the `ℓ¹`
product bound `ProdBd` (with any prescribed constant `c_P(L, A, c_R, c_x)`). -/
theorem thm_obs_rel (cPf : ℕ → ℝ → ℝ → ℝ → ℝ) (hcPf : ∀ L A c c', 0 ≤ cPf L A c c') :
    ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ κ cg cm cT ε Ke Cf Cb KZ KG : ℝ, FlowC2Concl L ℓ A ρ κ cg cm cT ε Ke Cf Cb ∧
      ε ≤ 1 ∧ SpinConcl L ℓ A ρ κ cg cm cT ε Ke KZ KG ∧
    ∃ cRc cδ : ℝ,
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Step2.D2.Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 3 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
    ∀ m ∈ mRange L N, ∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
    ∀ (P : ObsPts 2 L N) (o₀ : ObsSt .one L N), o₀.IsObs → ObsLocInv P 0 o₀ → ObsSymInv 0 o₀ →
      (∀ x, (o₀.V x : SA .one (Lam 2 L N)).a ∈ (ℂ ∙ psibar P.a)) → o₀.W = 0 → o₀.K = 0 →
    ∀ β₀ : ℂ, β₀ ≠ 0 → (∀ x ∈ blockIdx (L := L) (N := N) 0,
        mass1 (-1) (o₀.V x : SA .one (Lam 2 L N)).a =
          if P.a ∈ blockSet (L := L) (N := N) 0 x then β₀ else 0) →
      let R' := R.withMsq m
      let t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀
      let rr := fun j => cRc * (t j).1
      let nk := frakN (histCovO R' t) (kapH R' t) P.a
      let β := fun j => betaTot (L := L) (N := N) j (histVO R' P o₀ t j)
      ProdBd R' P o₀ t Nh rr (cPf L A cRc (cx κ cT)) (2 * ((L : ℝ) ^ 2)⁻¹) →
      cδ * ∑ k ∈ range Nh, rr k ^ 2 ≤ 1 / 8 ∧
      ∀ j ≤ Nh, 0 < ‖β j‖ ∧
        shareDev P.a j (histVO R' P o₀ t j) ≤ 6 * (cδ * ∑ k ∈ range j, rr k ^ 2) * ‖β j‖ ∧
        (j < Nh → ‖β (j + 1) - β j * (1 - nk j)‖ ≤ cδ * rr j ^ 2 * ‖β j * (1 - nk j)‖) ∧
        ‖β j - β₀ * ∏ k ∈ range j, (1 - nk k)‖ ≤
          (Real.exp (cδ * ∑ k ∈ range j, rr k ^ 2) - 1) * ‖β₀ * ∏ k ∈ range j, (1 - nk k)‖ := by
  obtain ⟨C₀o, ηo, L₀k, hC₀o, hηo, hk⟩ := kobs_bounds
  obtain ⟨Kw, L₀w, hKw, hw⟩ := wobs_bounds
  obtain ⟨Lo, hLod⟩ : ∃ Lo : ℕ, Lo = max (max L₀k L₀w) (⌈144 * C₀o + 12 * Kw⌉₊ + 8) := ⟨_, rfl⟩
  have hLk : L₀k ≤ Lo := hLod ▸ le_trans (le_max_left _ _) (le_max_left _ _)
  have hLw' : L₀w ≤ Lo := hLod ▸ le_trans (le_max_right _ _) (le_max_left _ _)
  have hLc : 144 * C₀o + 12 * Kw + 8 ≤ (Lo : ℝ) := by
    have h1 : ⌈144 * C₀o + 12 * Kw⌉₊ + 8 ≤ Lo := hLod ▸ le_max_right _ _
    have h2 := Nat.le_ceil (144 * C₀o + 12 * Kw)
    have h3 : ((⌈144 * C₀o + 12 * Kw⌉₊ + 8 : ℕ) : ℝ) ≤ Lo := by exact_mod_cast h1
    push_cast at h3
    linarith
  obtain ⟨L₀, hL₀⟩ := thm_flow_master (obsAReq C₀o ηo Lo)
    (obsAReq_ev hC₀o hηo hk hLk (by linarith)) (relEReq C₀o ηo Kw Lo cPf)
    (relEReq_ev cPf hw hLw')
  refine ⟨max L₀ Lo, fun L _ hL => ?_⟩
  have hLo : Lo ≤ L := le_trans (le_max_right _ _) hL
  have hLr : (Lo : ℝ) ≤ L := by exact_mod_cast hLo
  obtain ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, Cf, Cb, KZ, KG, hC, hε1', -, -, hSp, hAx, -, C₀x, ηx, εsx,
    CKx, C₂x, CDx, Cqx, Clx, cSx, hSBx, hEx, hXm⟩ := hL₀ L (le_trans (le_max_left _ _) hL)
  obtain ⟨-, hA0, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8, -, hCN⟩ := id hC
  let R₀ : RGPar 2 L 1 := ⟨Step2.D2.Pc, 0, ℓ, A, 0, ρ⟩
  obtain ⟨-, hθ⟩ := hAx hLo
  obtain ⟨ε₀, C₁k, hε₀, hC₁k, hKB, hsm, hε1, hεε, hεk, C₁w, ε₁, hC₁w, hε₁, hWB, hC₁ε, hε₁',
    hβε, hcgbε, hBτε, hcδε⟩ := hEx R₀ rfl hLo hAx
  have hθ0 : 0 ≤ kθ0 L A C₀o ηo := by
    unfold kθ0
    exact mul_nonneg hC₀o (add_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _))
  have hL0 : (0 : ℝ) < L := by linarith
  have hLwk : Kw / L ≤ 1 / 12 := by
    rw [div_le_iff₀ hL0]; linarith
  have hL8 : 8 ≤ L := by exact_mod_cast (show (8 : ℝ) ≤ L by linarith)
  have hβ2 := betaL_ge hL8
  set c := cR R₀ ((L : ℝ) ^ 2) cm C₂x with hc
  set cgb := cgbF L c
  set cδ := cdF C₀o ηo cPf L A c (cx κ cT) C₁k C₁w with hcδdef
  set B := kB (kθ0 L A C₀o ηo) C₁k (8 * cx κ cT)
  set X := 16 * (8 * (csN 2 : ℝ)) * (3 * C₁w + 1) * B +
    3 * cPf L A c (cx κ cT) * (3 * C₁w + 1) + 4 * (9 * c / 1024) * cgb * (1 + cgb) with hX
  have hcδX : cδ = 3 * X := rfl
  -- nonnegativity
  have hcx : 0 ≤ cx κ cT := by
    obtain ⟨-, -, -, -, hκ0, hκ1, -, -, hcT, -⟩ := id hC
    unfold cx; exact div_nonneg (by linarith) (by linarith)
  have hB : 0 ≤ B := by
    have h1 := mul_nonneg hθ0 (by positivity : (0 : ℝ) ≤ 8 * cx κ cT)
    have h2 := mul_nonneg hC₁k
      (by positivity : (0 : ℝ) ≤ 8 + 2 * (8 * cx κ cT) + (8 * cx κ cT) ^ 2)
    show 0 ≤ kθ0 L A C₀o ηo * (8 * cx κ cT) + C₁k * (8 + 2 * (8 * cx κ cT) + (8 * cx κ cT) ^ 2)
    linarith
  refine ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, Cf, Cb, KZ, KG, hC, hε1', hSp, c, cδ, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm P o₀ h0 hl0 hs0 hf0 hW0 hK0 β₀ hβ₀
    hpt R' t rr nk βs hPr
  obtain ⟨H, hm1, F1⟩ := hXm N R hP hi0 hRℓ hRA hRρ (by omega) Nh hNh m hm
  obtain ⟨hV, hVL⟩ := (hCN N R hP hi0 hRℓ hRA hRρ (by omega) Nh hNh).2.2.2.2.2.2.2.2.2 m hm
  have ht := admissible_InDh_rg R' F1 hadm Nh le_rfl
  have hRA' : R'.A = A := hRA
  have hcR : cR R' ((L : ℝ) ^ 2) cm C₂x = c := cR_congr (show R.ℓ = ℓ from hRℓ) _ _ _
  have hβ0 : (0 : ℝ) ≤ betaL L := by linarith
  have hβp : (0 : ℝ) < betaL L := by linarith
  have hcmu := H.hcmu
  have hC₂ := H.hC₂
  have hc2 : 2 ≤ c := hcR ▸ two_le_cR R' hcmu hC₂
  have hc0 : 0 < c := by linarith
  have hcgb0 : 0 ≤ cgb := by
    show 0 ≤ ((L : ℝ) ^ 2 + 2) + (3 * betaL L + 7 + 9 * c) / c ^ 2
    positivity
  have hX0 : 0 ≤ X := by
    have := hcPf L A c (cx κ cT); positivity
  have hcδ0 : 0 ≤ cδ := by rw [hcδX]; positivity
  have hW0' : ∀ x, oTo Obs2.wA 0 (histS R' 0 t) (o₀.W x) = 0 := fun x => by
    have : o₀.W x = 0 := by rw [hW0]; rfl
    rw [this]; exact oTo_zero' _ _ _
  have hK0' : ∀ X, oTo Obs2.wA 0 (histS R' 0 t) (o₀.K X) = 0 := fun X => by
    have : o₀.K X = 0 := by rw [hK0]; rfl
    rw [this]; exact oTo_zero' _ _ _
  have hW0a : ∀ x, (o₀.W x : SA .one (Lam 2 L N)).a = 0 := fun x => by
    have : o₀.W x = 0 := by rw [hW0]; rfl
    rw [this]; rfl
  have hcgε : cg * ε ≤ betaL L / 4 := by have := H.h6; linarith
  have key := obs_hist_rel_w R' (by rw [hRA']; exact hKB) hC₁k hWB hC₁w
    (by rw [hRA']; exact hSBx) hV hm1 hβ0 (by norm_num : (1 / 2 : ℝ) ≤ 1) H (by rw [show R'.ρ = ρ from hRρ]; linarith)
    (by rw [show R'.ρ = ρ from hRρ]; exact hρ8) P o₀ h0
    hl0 hs0 hf0 hW0a t hW0' hK0' Nh le_rfl (by omega) (by omega) hVL ht
    (by rw [hRA']; exact hθ0) (by rw [hRA']; exact hθ)
    (by rw [hRA', hcR]; exact hsm) (by rw [hcR]; exact hε1) (by rw [hcR]; exact hεε)
    (by rw [hRA', hcR]; exact hεk) hLwk (by rw [hcR]; exact hC₁ε) (by rw [hcR]; exact hε₁')
    hβp le_rfl hcgε hβε
  simp only [hRA', hcR] at key
  obtain ⟨r', -, hrest⟩ := key
  have hpt' : ∀ x ∈ blockIdx (L := L) (N := N) 0,
      mass1 (-1) (histVO R' P o₀ t 0 x : SA .one (Lam 2 L N)).a =
        if P.a ∈ blockSet (L := L) (N := N) 0 x then β₀ else 0 := fun x hx => by
    rw [histVO_a_mass]; exact hpt x hx
  obtain ⟨hb0, hD0⟩ := betaTot_shareDev_point P.a 0 (histVO R' P o₀ t 0) β₀ hpt'
  have hL2 : (64 : ℝ) ≤ (L : ℝ) ^ 2 := by
    have : (8 : ℝ) ≤ L := by exact_mod_cast hL8
    nlinarith
  have hcgb1 : (L : ℝ) ^ 2 + 2 ≤ cgb := by
    show _ ≤ ((L : ℝ) ^ 2 + 2) + (3 * betaL L + 7 + 9 * c) / c ^ 2
    have : 0 ≤ (3 * betaL L + 7 + 9 * c) / c ^ 2 := by positivity
    linarith
  have hℓ4 : 9 * R'.ℓ ^ 4 / 128 ≤ 9 * c / 1024 := by
    have h1 := (ell_parts R' hcmu).2.1
    have h2 := cV_le_cR R' hcmu hC₂
    rw [hcR] at h2
    linarith
  have hcδ' : 16 * (8 * (csN 2 : ℝ)) * (3 * C₁w + 1) * B + 3 * cPf L A c (cx κ cT) * (3 * C₁w + 1) +
      4 * (9 * R'.ℓ ^ 4 / 128) * cgb * (1 + cgb) +
      4 * (9 * R'.ℓ ^ 4 / 128) * cgb * cδ * (c * ε) ≤ 6 / 7 * cδ := by
    have hε0 : 0 ≤ ε := by have := H.hε; linarith
    have e1 : 4 * (9 * R'.ℓ ^ 4 / 128) * cgb * (1 + cgb) ≤ 4 * (9 * c / 1024) * cgb * (1 + cgb) := by
      gcongr
    have e2 : 4 * (9 * R'.ℓ ^ 4 / 128) * cgb * cδ * (c * ε) ≤
        (4 * (9 * c / 1024) * cgb * c * ε) * cδ := by
      have : 4 * (9 * R'.ℓ ^ 4 / 128) * cgb * cδ * (c * ε) =
          (4 * (9 * R'.ℓ ^ 4 / 128) * cgb * c * ε) * cδ := by ring
      rw [this]
      gcongr
    have e3 : (4 * (9 * c / 1024) * cgb * c * ε) * cδ ≤ 1 / 2 * cδ :=
      mul_le_mul_of_nonneg_right hBτε hcδ0
    have e4 : 16 * (8 * (csN 2 : ℝ)) * (3 * C₁w + 1) * B + 3 * cPf L A c (cx κ cT) * (3 * C₁w + 1) +
        4 * (9 * c / 1024) * cgb * (1 + cgb) = cδ / 3 := by rw [hcδX]; ring
    linarith
  have hcδε' : cδ * (c ^ 2 * (ε / (betaL L / 4))) ≤ 1 / 8 := by
    have e : cδ * (c ^ 2 * (ε / (betaL L / 4))) = cδ * c ^ 2 * (4 / betaL L) * ε := by
      field_simp
    rw [e]; exact hcδε
  obtain ⟨hsum, hall⟩ := hrest hcgb0 (hcPf L A c (cx κ cT)) hcδ0 le_rfl
    (by rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]; linarith)
    (by nlinarith)
    ((cn_le_cR R' hcmu hC₂).trans (by rw [hcR]; nlinarith))
    ((cd_le_cR R' hcmu hC₂ (betaL L)).trans (by
      rw [hcR]
      show 3 * betaL L + 7 + 9 * c ≤ (((L : ℝ) ^ 2 + 2) + (3 * betaL L + 7 + 9 * c) / c ^ 2) * c ^ 2
      rw [add_mul, div_mul_cancel₀ _ (by positivity)]
      nlinarith))
    (by linarith [show cgb * (c * ε) = cgb * c * ε by ring])
    hcδ' hcδε' hPr hD0 (by rw [hb0]; exact norm_pos_iff.2 hβ₀)
  refine ⟨hsum, fun j hj => ?_⟩
  obtain ⟨h1, h2, -, -, h5, h6⟩ := hall j hj
  rw [hb0] at h6
  exact ⟨h1, h2, h5, h6⟩

end

end Spin2
