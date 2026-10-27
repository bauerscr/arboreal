import Flow.Conj

/-!
# Theorem `thm:flow` (Section `sec:flow`)

* `thm_flow_body`: the proof of Theorem `thm:flow` (from the ingredients in `Flow/Theorem.lean`),
  with claims 0–8 packaged as `FlowBody`, together with the reality of `V₀^c` on the disc
  `|b₀| ≤ b̄` (`Vc_conj`, `Flow/Conj.lean`).
* `thm_flow`: **Theorem `thm:flow` and Corollary `cor:flow-finvol`**, the first part of
  `thm_flow_body`.
* `thm_flow_real`: `thm_flow` (same prefix and claims 0–8) together with the reality
  statement `V₀^c(m², b̄₀) = conj V₀^c(m², b₀)` for all `m², b₀`; in particular the couplings
  `z, y, a` of `V₀^c(m², b)` are real for real `b` (`Vcoup.im_eq_zero_of_conj`, `V0c_real`).
  For `|b₀| > b̄` the stable manifold map is junk, so `V₀^c` is redefined there as
  `(0, 0, 0, b₀)`, which does not affect claims 0–8 (`FlowBody.congr`).

The reality statement fills a gap of `h02rg.tex`, where the reality of `V₀^c` for real `b₀`
(needed for `β = (1+s₀)²/b₀` and `h` to be real parameters) is not proved.
-/

namespace Flow

noncomputable section

open Finset Grassmann Loc FRD Step Metric Filter Topology Coup

variable {d : ℕ}

/-- The body of `thm_flow` (claims 0–8) for given `b̄, C, κ, V₀^c`. -/
abbrev FlowBody (d L : ℕ) [NeZero L] (A ℓ₀ bbar C κ : ℝ) (V₀c : ℝ → ℂ → Vcoup) : Prop :=
      (∀ msq b₀, (V₀c msq b₀).b = b₀) ∧
      (∀ msq : ℝ, 0 ≤ msq → ∀ b₀ : ℂ, ‖b₀‖ ≤ bbar → ∀ N j : ℕ, j + 3 ≤ N →
        (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j)
            (flowN d L N msq (V₀c msq b₀) j).1).toReal ≤ C * ‖b₀‖ * (L : ℝ) ^ (-(κ * j)) ∧
        (Knorm j (ellj d L ℓ₀ j) A (flowN d L N msq (V₀c msq b₀) j).2).toReal ≤
          C * ‖b₀‖ ^ 2 * (L : ℝ) ^ (-(κ * j))) ∧
      (∀ msq : ℝ, 0 ≤ msq → ∀ b₀ : ℂ, ‖b₀‖ ≤ bbar → ∀ N M j : ℕ, j + 2 ≤ N → N ≤ M →
        (flowN d L N msq (V₀c msq b₀) j).1 = (flowN d L M msq (V₀c msq b₀) j).1) ∧
      (∀ msq : ℝ, 0 ≤ msq → ∀ b₀ : ℂ, ‖b₀‖ ≤ bbar →
        ‖(V₀c msq b₀).z‖ ≤ C * ‖b₀‖ ∧ ‖(V₀c msq b₀).y‖ ≤ C * ‖b₀‖ ∧
          ‖(V₀c msq b₀).a‖ ≤ C * ‖b₀‖) ∧
      (∀ b₀ : ℂ, ‖b₀‖ ≤ bbar → ContinuousOn (fun msq => (V₀c msq b₀).z) (Set.Ici 0) ∧
        ContinuousOn (fun msq => (V₀c msq b₀).y) (Set.Ici 0) ∧
        ContinuousOn (fun msq => (V₀c msq b₀).a) (Set.Ici 0)) ∧
      (∀ msq : ℝ, 0 ≤ msq →
        DifferentiableOn ℂ (fun b₀ => (V₀c msq b₀).z) (ball 0 bbar) ∧
        DifferentiableOn ℂ (fun b₀ => (V₀c msq b₀).y) (ball 0 bbar) ∧
        DifferentiableOn ℂ (fun b₀ => (V₀c msq b₀).a) (ball 0 bbar) ∧
        ∀ b₀ ∈ ball (0 : ℂ) bbar, ‖deriv (fun b => (V₀c msq b).z) b₀‖ ≤ C ∧
          ‖deriv (fun b => (V₀c msq b).y) b₀‖ ≤ C ∧ ‖deriv (fun b => (V₀c msq b).a) b₀‖ ≤ C) ∧
      (∀ msq : ℝ, 0 ≤ msq → ∀ b₀ : ℂ, ‖b₀‖ ≤ bbar → ∀ N j : ℕ, j ≤ N →
        (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j)
            (flowN d L N msq (V₀c msq b₀) j).1).toReal ≤ C * ‖b₀‖ * (L : ℝ) ^ (-(κ * j)) ∧
        (Knorm j (ellj d L ℓ₀ j) A (flowN d L N msq (V₀c msq b₀) j).2).toReal ≤
          C * ‖b₀‖ ^ 2 * (L : ℝ) ^ (-(κ * j))) ∧
      (∀ msq : ℝ, 0 ≤ msq → ∀ b₀ : ℂ, ‖b₀‖ ≤ bbar → ∀ N M j : ℕ, j + 3 ≤ N → N ≤ M →
        uflow d L N msq (V₀c msq b₀) j = uflow d L M msq (V₀c msq b₀) j) ∧
      (∀ msq : ℝ, 0 ≤ msq → ∀ b₀ : ℂ, ‖b₀‖ ≤ bbar → ∀ N : ℕ,
        ‖∑ j ∈ range N, uflow d L N msq (V₀c msq b₀) j‖ ≤ C * ‖b₀‖)

theorem FlowBody.congr {d L : ℕ} [NeZero L] {A ℓ₀ bbar C κ : ℝ} {V V' : ℝ → ℂ → Vcoup}
    (hV : FlowBody d L A ℓ₀ bbar C κ V) (hb : ∀ msq b₀, (V' msq b₀).b = b₀)
    (he : ∀ msq b₀, ‖b₀‖ ≤ bbar → V' msq b₀ = V msq b₀) : FlowBody d L A ℓ₀ bbar C κ V' := by
  obtain ⟨_, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hV
  refine ⟨hb, fun msq hm b₀ hb₀ => by rw [he msq b₀ hb₀]; exact h1 msq hm b₀ hb₀,
    fun msq hm b₀ hb₀ => by rw [he msq b₀ hb₀]; exact h2 msq hm b₀ hb₀,
    fun msq hm b₀ hb₀ => by rw [he msq b₀ hb₀]; exact h3 msq hm b₀ hb₀,
    fun b₀ hb₀ => by simp only [he _ b₀ hb₀]; exact h4 b₀ hb₀,
    fun msq hm => ?_,
    fun msq hm b₀ hb₀ => by rw [he msq b₀ hb₀]; exact h6 msq hm b₀ hb₀,
    fun msq hm b₀ hb₀ => by rw [he msq b₀ hb₀]; exact h7 msq hm b₀ hb₀,
    fun msq hm b₀ hb₀ => by rw [he msq b₀ hb₀]; exact h8 msq hm b₀ hb₀⟩
  obtain ⟨d1, d2, d3, d4⟩ := h5 msq hm
  have hEq : Set.EqOn (V' msq) (V msq) (ball 0 bbar) := fun b hb =>
    he msq b (mem_ball_zero_iff.1 hb).le
  have hev : ∀ b ∈ ball (0 : ℂ) bbar, V' msq =ᶠ[𝓝 b] V msq := fun b hb =>
    Filter.eventually_of_mem (isOpen_ball.mem_nhds hb) hEq
  refine ⟨d1.congr fun b hb => by simp only [hEq hb], d2.congr fun b hb => by simp only [hEq hb],
    d3.congr fun b hb => by simp only [hEq hb], fun b hb => ?_⟩
  have ez : (fun b => (V' msq b).z) =ᶠ[𝓝 b] fun b => (V msq b).z :=
    (hev b hb).mono fun x hx => by simp only [hx]
  have ey : (fun b => (V' msq b).y) =ᶠ[𝓝 b] fun b => (V msq b).y :=
    (hev b hb).mono fun x hx => by simp only [hx]
  have ea : (fun b => (V' msq b).a) =ᶠ[𝓝 b] fun b => (V msq b).a :=
    (hev b hb).mono fun x hx => by simp only [hx]
  rw [ez.deriv_eq, ey.deriv_eq, ea.deriv_eq]
  exact d4 b hb

set_option maxHeartbeats 4000000 in
/-- `thm_flow` with the reality of `V₀^c` on the disc `|b₀| ≤ b̄`, and the body packaged as
`FlowBody`. -/
theorem thm_flow_body (hd : 3 ≤ d) : ∃ (L₀ : ℕ) (Kℓ : ℝ), 0 ≤ Kℓ ∧ ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∀ ℓ₀ : ℝ, 0 < ℓ₀ →
    Kℓ * (L : ℝ) ^ ((d : ℝ) - 2 + 2 * pPhi d) ≤ ℓ₀ ^ 2 →
    ∃ (bbar C κ : ℝ) (V₀c : ℝ → ℂ → Vcoup), 0 < bbar ∧ 0 ≤ C ∧ 0 < κ ∧
      FlowBody d L A ℓ₀ bbar C κ V₀c ∧
      (∀ msq : ℝ, ∀ b₀ : ℂ, ‖b₀‖ ≤ bbar → V₀c msq (starRingEnd ℂ b₀) = (V₀c msq b₀).conj) := by
  obtain ⟨L₁, Kℓ₁, hKℓ₁, hhyp⟩ := exists_hyp hd
  obtain ⟨L₂, hsr⟩ := step_real hd
  obtain ⟨KgN, hKgN, hgoodN⟩ := goodCov_CfrdN hd
  refine ⟨max L₁ L₂, max Kℓ₁ KgN, le_trans hKℓ₁ (le_max_left _ _), fun L _ hL => ?_⟩
  obtain ⟨A₁, hA₁, hA₁'⟩ := hhyp L (le_trans (le_max_left _ _) hL)
  obtain ⟨A₂, hA₂, hA₂'⟩ := hsr L (le_trans (le_max_right _ _) hL)
  refine ⟨max A₁ A₂, le_trans hA₁ (le_max_left _ _), fun A hA ℓ₀ hℓ₀ hKℓ => ?_⟩
  have hLpos : (0 : ℝ) ≤ (L : ℝ) ^ ((d : ℝ) - 2 + 2 * pPhi d) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  obtain ⟨ε, C₁, δK, Kc, Cw, H, hδK⟩ := hA₁' A (le_trans (le_max_left _ _) hA) ℓ₀ hℓ₀
    ((mul_le_mul_of_nonneg_right (le_max_left _ _) hLpos).trans hKℓ)
  obtain ⟨ε', aK, Cu, hε', haK, hCu, hstep⟩ := hA₂' A (le_trans (le_max_right _ _) hA)
  have hgN : ∀ (M : ℕ) (msq : ℝ), 0 ≤ msq →
      GoodCov (d := d) (L := L) (N := M + 1) M ℓ₀ (CfrdN d L M msq) := fun M msq hmsq =>
    hgoodN L NeZero.one_le ℓ₀ hℓ₀ ((mul_le_mul_of_nonneg_right (le_max_right _ _) hLpos).trans hKℓ)
      M msq hmsq
  haveI : Fact (0 < ℓ₀) := ⟨hℓ₀⟩
  haveI : Fact (0 < A) := ⟨by linarith [H.hA]⟩
  have hS := RGsys_bounds H
  have hβ0 : 0 ≤ βB d L ℓ₀ Kc Cw := (hS 0).beta_nonneg
  have hδ0 : 0 ≤ δD d L δK := le_trans H.hδK (le_max_right _ _)
  have hδ : δD d L δK ≤ 1 / 2 := δD_le H.hd (by have := H.hL16; omega) hδK
  have hγ : 0 ≤ C₁ * cX d ℓ₀ ^ 2 := by have := H.hC₁; positivity
  obtain ⟨R, hR, hc⟩ := Admissible.exists hβ0 hδ0 hγ (by linarith : δD d L δK < 3 / 4)
    (by norm_num) (rad_pos H)
  set ρ := rho (βB d L ℓ₀ Kc Cw) (δD d L δK) (3 / 4) R with hρ
  have hρ0 : 0 < ρ := hc.rho_pos hR
  set c₃ := cc d L aK Cu (c0 d L ℓ₀ Kc Cw δK C₁) 3 with hc₃
  have hc₃0 : 0 ≤ c₃ := cc_nonneg aK Cu (c0_nonneg H hc) 3
  have hc03 : c0 d L ℓ₀ Kc Cw δK C₁ ≤ c₃ := cc_mono aK Cu _ (Nat.zero_le 3)
  set bbar := min ρ (min 1 (ε' / (2 * c₃ + 1))) with hbbar_def
  have hbbar : 0 < bbar := lt_min hρ0 (lt_min one_pos (by positivity))
  set Cs := Cst (βB d L ℓ₀ Kc Cw) (δD d L δK) with hCsdef
  have hCs := Cst_nonneg H hc
  set C := 4 * (1 + Cu) * c₃ + Cs with hCdef
  have hC0 : 0 ≤ C := by positivity
  have hc₃C : c₃ ≤ C := by nlinarith
  have hCsC : Cs ≤ C := by nlinarith
  have hL2 : 2 ≤ L := by have := H.hL16; omega
  set κ := Real.logb L (4 / 3) with hκdef
  have hκ : 0 < κ := Real.logb_pos (by exact_mod_cast (by omega : 1 < L)) (by norm_num)
  have hθ : ∀ j : ℕ, (L : ℝ) ^ (-(κ * j)) = (3 / 4) ^ j := fun j => (theta_pow_eq hL2 j).symm
  -- facts on `b₀`
  have hbρ : ∀ b₀ : ℂ, ‖b₀‖ ≤ bbar → ‖b₀‖ ≤ ρ := fun b₀ h => h.trans (min_le_left _ _)
  have hb1 : ∀ b₀ : ℂ, ‖b₀‖ ≤ bbar → ‖b₀‖ ≤ 1 := fun b₀ h =>
    h.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hbε : ∀ b₀ : ℂ, ‖b₀‖ ≤ bbar → 2 * c₃ * ‖b₀‖ ≤ ε' := by
    intro b₀ h
    have h1 : ‖b₀‖ ≤ ε' / (2 * c₃ + 1) := h.trans ((min_le_right _ _).trans (min_le_right _ _))
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith [norm_nonneg b₀]
  have hstep' : ∀ (N j : ℕ), j < N →
      ∀ (C' : Matrix (Lam d L N) (Lam d L N) ℝ), GoodCov j ℓ₀ C' →
      ∀ (V : Vcoup) (K : Act d L N), InK j K → _ :=
    fun N j hj C' hC' V K hK => hstep N j hj ℓ₀ hℓ₀ C' hC' V K hK
  have hfin := fun {msq : ℝ} (hmsq : 0 ≤ msq) {b₀ : ℂ} (hb : ‖b₀‖ ≤ bbar) =>
    flow_bounds_fin H hc haK hCu hstep' hgN hmsq (hbρ b₀ hb) (hb1 b₀ hb) (hbε b₀ hb)
  -- the norm of the stable manifold map
  have hsm : ∀ (m : ℝ) (b₀ : ℂ), ‖b₀‖ ≤ bbar →
      ‖(RGsys H m).stableMap (w0 d L ℓ₀ A b₀)‖ ≤ Cs * ‖b₀‖ := by
    intro m b₀ hb
    have h := orbit_decay H hc m (hbρ b₀ hb) 0
    simp only [pow_zero, mul_one] at h
    exact (le_add_of_nonneg_right (norm_nonneg _)).trans h
  refine ⟨bbar, C, κ, Vc H, hbbar, hC0, hκ, ⟨Vc_b H, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- (1) `e:flowVK`
    intro msq hmsq b₀ hb N j hN
    obtain ⟨hV, hK⟩ := flow_bounds_inf H hc hmsq (hbρ b₀ hb) hN
    rw [hθ j]
    have hcV := cV_nonneg d ℓ₀
    have hMk := Mk_nonneg H hc
    have h0 : 4 * cV d ℓ₀ * Cs + Mk (βB d L ℓ₀ Kc Cw) (δD d L δK) (C₁ * cX d ℓ₀ ^ 2) ≤ C := by
      have := hc03; unfold c0 at this; linarith
    have hθ0 : (0 : ℝ) ≤ (3 / 4) ^ j := by positivity
    have hb0 := norm_nonneg b₀
    constructor
    · refine hV.trans ?_
      have : 4 * cV d ℓ₀ * Cs ≤ C := by nlinarith
      calc 4 * cV d ℓ₀ * Cs * (3 / 4) ^ j * ‖b₀‖ = 4 * cV d ℓ₀ * Cs * (‖b₀‖ * (3 / 4) ^ j) := by
            ring
        _ ≤ C * (‖b₀‖ * (3 / 4) ^ j) := mul_le_mul_of_nonneg_right this (by positivity)
        _ = C * ‖b₀‖ * (3 / 4) ^ j := by ring
    · refine hK.trans ?_
      have : Mk (βB d L ℓ₀ Kc Cw) (δD d L δK) (C₁ * cX d ℓ₀ ^ 2) ≤ C := by nlinarith
      calc Mk (βB d L ℓ₀ Kc Cw) (δD d L δK) (C₁ * cX d ℓ₀ ^ 2) * ‖b₀‖ ^ 2 * (3 / 4) ^ j
          = Mk (βB d L ℓ₀ Kc Cw) (δD d L δK) (C₁ * cX d ℓ₀ ^ 2) * (‖b₀‖ ^ 2 * (3 / 4) ^ j) := by
            ring
        _ ≤ C * (‖b₀‖ ^ 2 * (3 / 4) ^ j) := mul_le_mul_of_nonneg_right this (by positivity)
        _ = C * ‖b₀‖ ^ 2 * (3 / 4) ^ j := by ring
  · -- (2) `V_j` does not depend on the torus
    intro msq hmsq b₀ hb N M j hN hNM
    rcases j with _ | j
    · rfl
    · have hr := orbit_le_rad H hc msq (hbρ b₀ hb)
      rw [Vc, flowN_orbit_V_succ H hmsq _ b₀ hr j N (by omega),
        flowN_orbit_V_succ H hmsq _ b₀ hr j M (by omega)]
  · -- (3) uniform bounds on `V_0^c`
    intro msq _ b₀ hb
    have h := hsm msq b₀ hb
    have hb0 := norm_nonneg b₀
    have hCC : Cs * ‖b₀‖ ≤ C * ‖b₀‖ := mul_le_mul_of_nonneg_right hCsC hb0
    rw [Vc_z, Vc_y, Vc_a]
    refine ⟨((norm_fst_le _).trans h).trans hCC,
      (((norm_fst_le _).trans (norm_snd_le _)).trans h).trans hCC,
      (((norm_snd_le _).trans (norm_snd_le _)).trans h).trans hCC⟩
  · -- (4) continuity in `m²`
    intro b₀ hb
    have hw : ∀ m : ℝ, ‖w0 d L ℓ₀ A b₀‖ ≤ ρ := fun m => by rw [norm_w0]; exact hbρ b₀ hb
    have hcont := continuous_stableMap_obs (V := Vsp) (W := WS d L ℓ₀ A)
      (ι := fun j => Idx j 3) (Y := fun j N => ℂ × KS d L j N.1 ℓ₀ A) (P := ℝ)
      (obs (d := d) (L := L) (ℓ₀ := ℓ₀) (A := A)) (fun m => RGsys H m) hS hc
      (fun x => by simp only [RGsys_E]; exact continuous_const)
      (fun j w hw _ => RGsys_contB H j w hw)
      (fun j w hw _ => RGsys_contD H j w hw) (fun j v w hv hw hr => RGsys_contg H j v w hv hw hr)
      (ObsCont.const obs (w0 d L ℓ₀ A b₀)) hw
    refine ⟨?_, ?_, ?_⟩
    · simp only [Vc_z]; exact (continuous_fst.comp hcont).continuousOn
    · simp only [Vc_y]; exact (continuous_fst.comp (continuous_snd.comp hcont)).continuousOn
    · simp only [Vc_a]; exact (continuous_snd.comp (continuous_snd.comp hcont)).continuousOn
  · -- (5) holomorphy in `b₀`
    intro msq _
    set ŵ : WS d L ℓ₀ A 0 := ((1 : ℂ), 0)
    have hŵ : ‖ŵ‖ = 1 := by simp [ŵ, Prod.norm_def]
    obtain ⟨hdiff, hder⟩ := (hS msq).differentiableOn_stableMap_smul hc (RGsys_analytic H msq) ŵ
      (R₀ := ρ) (by rw [hŵ, mul_one])
    have e : ∀ b : ℂ, b • ŵ = w0 d L ℓ₀ A b := fun b => by simp [ŵ, w0]
    set f := fun z : ℂ => (RGsys H msq).stableMap (z • ŵ) with hf
    have hsub : ball (0 : ℂ) bbar ⊆ ball 0 ρ := ball_subset_ball (min_le_left _ _)
    have hfz : (fun b => (Vc H msq b).z) = fun b => (f b).1 := funext fun b => by
      rw [Vc_z, hf]; simp only [e]
    have hfy : (fun b => (Vc H msq b).y) = fun b => (f b).2.1 := funext fun b => by
      rw [Vc_y, hf]; simp only [e]
    have hfa : (fun b => (Vc H msq b).a) = fun b => (f b).2.2 := funext fun b => by
      rw [Vc_a, hf]; simp only [e]
    have hd' := hdiff.mono hsub
    have hDer : ∀ b ∈ ball (0 : ℂ) bbar, HasDerivAt f (deriv f b) b := fun b hbb =>
      (hdiff.differentiableAt (isOpen_ball.mem_nhds (hsub hbb))).hasDerivAt
    have hbound : ∀ b ∈ ball (0 : ℂ) bbar, ‖deriv f b‖ ≤ C := by
      intro b hbb
      refine (hder b (hsub hbb)).trans ?_
      rw [hŵ, mul_one]
      refine le_trans ?_ hCsC
      rw [hCsdef, Cst]
      have : 0 ≤ 2 * (3 / 4 : ℝ) / (3 / 4 - δD d L δK) := by
        have : 0 < 3 / 4 - δD d L δK := by linarith
        positivity
      nlinarith
    rw [hfz, hfy, hfa]
    refine ⟨hd'.fst, hd'.snd.fst, hd'.snd.snd, fun b hbb => ⟨?_, ?_, ?_⟩⟩
    · have h1 := ((ContinuousLinearMap.fst ℂ ℂ (ℂ × ℂ)).hasFDerivAt.comp_hasDerivAt b
        (hDer b hbb)).deriv
      change ‖deriv (⇑(ContinuousLinearMap.fst ℂ ℂ (ℂ × ℂ)) ∘ f) b‖ ≤ C
      rw [h1]; exact (norm_fst_le _).trans (hbound b hbb)
    · have h1 := (((ContinuousLinearMap.fst ℂ ℂ ℂ).comp (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ))
        ).hasFDerivAt.comp_hasDerivAt b (hDer b hbb)).deriv
      change ‖deriv (⇑((ContinuousLinearMap.fst ℂ ℂ ℂ).comp
        (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ))) ∘ f) b‖ ≤ C
      rw [h1]
      exact ((norm_fst_le _).trans (norm_snd_le _)).trans (hbound b hbb)
    · have h1 := (((ContinuousLinearMap.snd ℂ ℂ ℂ).comp (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ))
        ).hasFDerivAt.comp_hasDerivAt b (hDer b hbb)).deriv
      change ‖deriv (⇑((ContinuousLinearMap.snd ℂ ℂ ℂ).comp
        (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ))) ∘ f) b‖ ≤ C
      rw [h1]
      exact ((norm_snd_le _).trans (norm_snd_le _)).trans (hbound b hbb)
  · -- (6) Corollary `cor:flow-finvol`
    intro msq hmsq b₀ hb N j hj
    obtain ⟨hV, hK, -⟩ := hfin hmsq hb N j hj
    have hcc : cc d L aK Cu (c0 d L ℓ₀ Kc Cw δK C₁) (j + 3 - N) ≤ C :=
      (cc_mono aK Cu _ (by omega : j + 3 - N ≤ 3)).trans hc₃C
    rw [hθ j]
    have hθ0 : (0 : ℝ) ≤ (3 / 4) ^ j := by positivity
    refine ⟨hV.trans ?_, hK.trans ?_⟩
    · calc cc d L aK Cu (c0 d L ℓ₀ Kc Cw δK C₁) (j + 3 - N) * ‖b₀‖ * (3 / 4) ^ j
          = cc d L aK Cu (c0 d L ℓ₀ Kc Cw δK C₁) (j + 3 - N) * (‖b₀‖ * (3 / 4) ^ j) := by ring
        _ ≤ C * (‖b₀‖ * (3 / 4) ^ j) := mul_le_mul_of_nonneg_right hcc (by positivity)
        _ = C * ‖b₀‖ * (3 / 4) ^ j := by ring
    · calc cc d L aK Cu (c0 d L ℓ₀ Kc Cw δK C₁) (j + 3 - N) * ‖b₀‖ ^ 2 * (3 / 4) ^ j
          = cc d L aK Cu (c0 d L ℓ₀ Kc Cw δK C₁) (j + 3 - N) * (‖b₀‖ ^ 2 * (3 / 4) ^ j) := by
            ring
        _ ≤ C * (‖b₀‖ ^ 2 * (3 / 4) ^ j) := mul_le_mul_of_nonneg_right hcc (by positivity)
        _ = C * ‖b₀‖ ^ 2 * (3 / 4) ^ j := by ring
  · -- (7) `u_{j+1}` does not depend on the torus
    intro msq hmsq b₀ hb N M j hN hNM
    exact uflow_indep H hmsq _ b₀ (orbit_le_rad H hc msq (hbρ b₀ hb)) hN hNM
  · -- (8) the total constant `u`
    intro msq hmsq b₀ hb N
    have hb0 := norm_nonneg b₀
    have hterm : ∀ j ∈ range N, ‖uflow d L N msq (Vc H msq b₀) j‖ ≤
        (1 + Cu) * c₃ * ‖b₀‖ * (3 / 4) ^ j := by
      intro j hj
      have hjN : j < N := mem_range.1 hj
      obtain ⟨hV, hK, hI⟩ := hfin hmsq hb N j hjN.le
      have hcc : cc d L aK Cu (c0 d L ℓ₀ Kc Cw δK C₁) (j + 3 - N) ≤ c₃ :=
        cc_mono aK Cu _ (by omega : j + 3 - N ≤ 3)
      set v := (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j)
        (flowN d L N msq (Vc H msq b₀) j).1).toReal with hv
      set k := (Knorm j (ellj d L ℓ₀ j) A (flowN d L N msq (Vc H msq b₀) j).2).toReal with hk
      have hθ0 : (0 : ℝ) ≤ (3 / 4) ^ j := by positivity
      have hθ1 : ((3 : ℝ) / 4) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have hv' : v ≤ c₃ * ‖b₀‖ * (3 / 4) ^ j := hV.trans (by gcongr)
      have hk' : k ≤ c₃ * ‖b₀‖ * (3 / 4) ^ j := by
        refine hK.trans ?_
        have hb2 : ‖b₀‖ ^ 2 ≤ ‖b₀‖ := by nlinarith [hb1 b₀ hb]
        have := cc_nonneg (d := d) (L := L) aK Cu (c0_nonneg H hc) (j + 3 - N)
        calc cc d L aK Cu (c0 d L ℓ₀ Kc Cw δK C₁) (j + 3 - N) * ‖b₀‖ ^ 2 * (3 / 4) ^ j
            ≤ c₃ * ‖b₀‖ * (3 / 4) ^ j := by gcongr
          _ = c₃ * ‖b₀‖ * (3 / 4) ^ j := rfl
      have hsmall : v + k ≤ ε' := by
        have h1 := mul_le_mul_of_nonneg_left hθ1 (mul_nonneg hc₃0 hb0)
        have := hbε b₀ hb
        linarith
      obtain ⟨-, -, hu⟩ := hstep' N j hjN _ (covAt_good H hgN hjN hmsq) _ _ (hI hjN) hsmall
      have hLj : (1 : ℝ) ≤ (L : ℝ) ^ (j * d) := one_le_pow₀ H.hL1
      unfold uflow
      calc ‖(uVnext j (covAt d L N msq j) (flowN d L N msq (Vc H msq b₀) j).1
            (flowN d L N msq (Vc H msq b₀) j).2).1‖
          ≤ ‖(uVnext j (covAt d L N msq j) (flowN d L N msq (Vc H msq b₀) j).1
            (flowN d L N msq (Vc H msq b₀) j).2).1‖ * (L : ℝ) ^ (j * d) :=
            le_mul_of_one_le_right (norm_nonneg _) hLj
        _ ≤ v + Cu * k := hu
        _ ≤ (1 + Cu) * c₃ * ‖b₀‖ * (3 / 4) ^ j := by
            have := mul_le_mul_of_nonneg_left hk' hCu
            linarith
    refine (norm_sum_le _ _).trans ((sum_le_sum hterm).trans ?_)
    rw [← mul_sum]
    have hgeom : ∑ j ∈ range N, ((3 : ℝ) / 4) ^ j ≤ 4 := by
      have h0 : (0 : ℝ) ≤ 3 / 4 := by norm_num
      have h1 : (3 : ℝ) / 4 < 1 := by norm_num
      refine ((summable_geometric_of_lt_one h0 h1).sum_le_tsum (range N)
        (fun i _ => pow_nonneg h0 i)).trans ?_
      rw [tsum_geometric_of_lt_one h0 h1]; norm_num
    have hc1 : 0 ≤ (1 + Cu) * c₃ * ‖b₀‖ := by positivity
    calc (1 + Cu) * c₃ * ‖b₀‖ * ∑ j ∈ range N, ((3 : ℝ) / 4) ^ j ≤ (1 + Cu) * c₃ * ‖b₀‖ * 4 :=
          mul_le_mul_of_nonneg_left hgeom hc1
      _ ≤ C * ‖b₀‖ := by
          rw [hCdef]; nlinarith [mul_nonneg hCs hb0]
  · -- reality
    intro msq b₀ hb
    exact Vc_conj H hc msq (hbρ b₀ hb)

/-- **Theorem `thm:flow` and Corollary `cor:flow-finvol`.**  Let `d ≥ 3`, `L ≥ L₀`,
`A ≥ A₀(L)` and `ℓ₀² ≥ K L^{d-2+2p_Φ}`.  There are `b̄ > 0`, `C ≥ 0`, `κ > 0` and initial coupling
constants `V_0^c(m², b₀)` with `b`-component `b₀` such that for `m² ≥ 0` and `|b₀| ≤ b̄` the
renormalisation group flow `(V_j, K_j) = flowN N m² V_0^c j` on every torus `Λ_N`
(started at `K_0 = 0`) satisfies:

1. (`e:flowVK`, infinite volume range) `‖V_j‖_j ≤ C |b₀| L^{-κj}` and
   `‖K_j‖_j ≤ C |b₀|² L^{-κj}` for `j + 3 ≤ N`;
2. `V_j` does not depend on `N` for `j + 2 ≤ N`;
3. the components `z, y, a` of `V_0^c(m², b₀)` are bounded by `C |b₀|` uniformly in `m² ≥ 0`,
4. continuous in `m² ≥ 0`,
5. holomorphic in `b₀` (`|b₀| < b̄`) with derivative bounded by `C`;
6. (Corollary `cor:flow-finvol`) the bounds of (1) hold for all `j ≤ N`;
7. `u_{j+1}` does not depend on `N` for `j + 3 ≤ N`;
8. the total constant `u_N^{tot} = ∑_{j < N} u_{j+1}` produced by the flow is bounded by
   `C |b₀|`, uniformly in `N` and `m² ≥ 0` (the remark after `cor:flow-finvol`). -/
theorem thm_flow (hd : 3 ≤ d) : ∃ (L₀ : ℕ) (Kℓ : ℝ), 0 ≤ Kℓ ∧ ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∀ ℓ₀ : ℝ, 0 < ℓ₀ →
    Kℓ * (L : ℝ) ^ ((d : ℝ) - 2 + 2 * pPhi d) ≤ ℓ₀ ^ 2 →
    ∃ (bbar C κ : ℝ) (V₀c : ℝ → ℂ → Vcoup), 0 < bbar ∧ 0 ≤ C ∧ 0 < κ ∧
      (∀ msq b₀, (V₀c msq b₀).b = b₀) ∧
      (∀ msq : ℝ, 0 ≤ msq → ∀ b₀ : ℂ, ‖b₀‖ ≤ bbar → ∀ N j : ℕ, j + 3 ≤ N →
        (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j)
            (flowN d L N msq (V₀c msq b₀) j).1).toReal ≤ C * ‖b₀‖ * (L : ℝ) ^ (-(κ * j)) ∧
        (Knorm j (ellj d L ℓ₀ j) A (flowN d L N msq (V₀c msq b₀) j).2).toReal ≤
          C * ‖b₀‖ ^ 2 * (L : ℝ) ^ (-(κ * j))) ∧
      (∀ msq : ℝ, 0 ≤ msq → ∀ b₀ : ℂ, ‖b₀‖ ≤ bbar → ∀ N M j : ℕ, j + 2 ≤ N → N ≤ M →
        (flowN d L N msq (V₀c msq b₀) j).1 = (flowN d L M msq (V₀c msq b₀) j).1) ∧
      (∀ msq : ℝ, 0 ≤ msq → ∀ b₀ : ℂ, ‖b₀‖ ≤ bbar →
        ‖(V₀c msq b₀).z‖ ≤ C * ‖b₀‖ ∧ ‖(V₀c msq b₀).y‖ ≤ C * ‖b₀‖ ∧
          ‖(V₀c msq b₀).a‖ ≤ C * ‖b₀‖) ∧
      (∀ b₀ : ℂ, ‖b₀‖ ≤ bbar → ContinuousOn (fun msq => (V₀c msq b₀).z) (Set.Ici 0) ∧
        ContinuousOn (fun msq => (V₀c msq b₀).y) (Set.Ici 0) ∧
        ContinuousOn (fun msq => (V₀c msq b₀).a) (Set.Ici 0)) ∧
      (∀ msq : ℝ, 0 ≤ msq →
        DifferentiableOn ℂ (fun b₀ => (V₀c msq b₀).z) (ball 0 bbar) ∧
        DifferentiableOn ℂ (fun b₀ => (V₀c msq b₀).y) (ball 0 bbar) ∧
        DifferentiableOn ℂ (fun b₀ => (V₀c msq b₀).a) (ball 0 bbar) ∧
        ∀ b₀ ∈ ball (0 : ℂ) bbar, ‖deriv (fun b => (V₀c msq b).z) b₀‖ ≤ C ∧
          ‖deriv (fun b => (V₀c msq b).y) b₀‖ ≤ C ∧ ‖deriv (fun b => (V₀c msq b).a) b₀‖ ≤ C) ∧
      (∀ msq : ℝ, 0 ≤ msq → ∀ b₀ : ℂ, ‖b₀‖ ≤ bbar → ∀ N j : ℕ, j ≤ N →
        (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j)
            (flowN d L N msq (V₀c msq b₀) j).1).toReal ≤ C * ‖b₀‖ * (L : ℝ) ^ (-(κ * j)) ∧
        (Knorm j (ellj d L ℓ₀ j) A (flowN d L N msq (V₀c msq b₀) j).2).toReal ≤
          C * ‖b₀‖ ^ 2 * (L : ℝ) ^ (-(κ * j))) ∧
      (∀ msq : ℝ, 0 ≤ msq → ∀ b₀ : ℂ, ‖b₀‖ ≤ bbar → ∀ N M j : ℕ, j + 3 ≤ N → N ≤ M →
        uflow d L N msq (V₀c msq b₀) j = uflow d L M msq (V₀c msq b₀) j) ∧
      (∀ msq : ℝ, 0 ≤ msq → ∀ b₀ : ℂ, ‖b₀‖ ≤ bbar → ∀ N : ℕ,
        ‖∑ j ∈ range N, uflow d L N msq (V₀c msq b₀) j‖ ≤ C * ‖b₀‖) := by
  obtain ⟨L₀, Kℓ, hKℓ, h⟩ := thm_flow_body (d := d) hd
  refine ⟨L₀, Kℓ, hKℓ, fun L _ hL => ?_⟩
  obtain ⟨A₀, hA₀, h⟩ := h L hL
  refine ⟨A₀, hA₀, fun A hA ℓ₀ hℓ₀ hK => ?_⟩
  obtain ⟨bbar, C, κ, V, hbbar, hC, hκ, hbody, -⟩ := h A hA ℓ₀ hℓ₀ hK
  exact ⟨bbar, C, κ, V, hbbar, hC, hκ, hbody⟩

/-- **Theorem `thm:flow` with reality.** The exact statement of `thm_flow`, together with
`V₀^c(m², b̄₀) = conj V₀^c(m², b₀)` for all `m², b₀`. -/
theorem thm_flow_real (hd : 3 ≤ d) : ∃ (L₀ : ℕ) (Kℓ : ℝ), 0 ≤ Kℓ ∧ ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∀ ℓ₀ : ℝ, 0 < ℓ₀ →
    Kℓ * (L : ℝ) ^ ((d : ℝ) - 2 + 2 * pPhi d) ≤ ℓ₀ ^ 2 →
    ∃ (bbar C κ : ℝ) (V₀c : ℝ → ℂ → Vcoup), 0 < bbar ∧ 0 ≤ C ∧ 0 < κ ∧
      (∀ msq b₀, (V₀c msq b₀).b = b₀) ∧
      (∀ msq : ℝ, 0 ≤ msq → ∀ b₀ : ℂ, ‖b₀‖ ≤ bbar → ∀ N j : ℕ, j + 3 ≤ N →
        (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j)
            (flowN d L N msq (V₀c msq b₀) j).1).toReal ≤ C * ‖b₀‖ * (L : ℝ) ^ (-(κ * j)) ∧
        (Knorm j (ellj d L ℓ₀ j) A (flowN d L N msq (V₀c msq b₀) j).2).toReal ≤
          C * ‖b₀‖ ^ 2 * (L : ℝ) ^ (-(κ * j))) ∧
      (∀ msq : ℝ, 0 ≤ msq → ∀ b₀ : ℂ, ‖b₀‖ ≤ bbar → ∀ N M j : ℕ, j + 2 ≤ N → N ≤ M →
        (flowN d L N msq (V₀c msq b₀) j).1 = (flowN d L M msq (V₀c msq b₀) j).1) ∧
      (∀ msq : ℝ, 0 ≤ msq → ∀ b₀ : ℂ, ‖b₀‖ ≤ bbar →
        ‖(V₀c msq b₀).z‖ ≤ C * ‖b₀‖ ∧ ‖(V₀c msq b₀).y‖ ≤ C * ‖b₀‖ ∧
          ‖(V₀c msq b₀).a‖ ≤ C * ‖b₀‖) ∧
      (∀ b₀ : ℂ, ‖b₀‖ ≤ bbar → ContinuousOn (fun msq => (V₀c msq b₀).z) (Set.Ici 0) ∧
        ContinuousOn (fun msq => (V₀c msq b₀).y) (Set.Ici 0) ∧
        ContinuousOn (fun msq => (V₀c msq b₀).a) (Set.Ici 0)) ∧
      (∀ msq : ℝ, 0 ≤ msq →
        DifferentiableOn ℂ (fun b₀ => (V₀c msq b₀).z) (ball 0 bbar) ∧
        DifferentiableOn ℂ (fun b₀ => (V₀c msq b₀).y) (ball 0 bbar) ∧
        DifferentiableOn ℂ (fun b₀ => (V₀c msq b₀).a) (ball 0 bbar) ∧
        ∀ b₀ ∈ ball (0 : ℂ) bbar, ‖deriv (fun b => (V₀c msq b).z) b₀‖ ≤ C ∧
          ‖deriv (fun b => (V₀c msq b).y) b₀‖ ≤ C ∧ ‖deriv (fun b => (V₀c msq b).a) b₀‖ ≤ C) ∧
      (∀ msq : ℝ, 0 ≤ msq → ∀ b₀ : ℂ, ‖b₀‖ ≤ bbar → ∀ N j : ℕ, j ≤ N →
        (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j)
            (flowN d L N msq (V₀c msq b₀) j).1).toReal ≤ C * ‖b₀‖ * (L : ℝ) ^ (-(κ * j)) ∧
        (Knorm j (ellj d L ℓ₀ j) A (flowN d L N msq (V₀c msq b₀) j).2).toReal ≤
          C * ‖b₀‖ ^ 2 * (L : ℝ) ^ (-(κ * j))) ∧
      (∀ msq : ℝ, 0 ≤ msq → ∀ b₀ : ℂ, ‖b₀‖ ≤ bbar → ∀ N M j : ℕ, j + 3 ≤ N → N ≤ M →
        uflow d L N msq (V₀c msq b₀) j = uflow d L M msq (V₀c msq b₀) j) ∧
      (∀ msq : ℝ, 0 ≤ msq → ∀ b₀ : ℂ, ‖b₀‖ ≤ bbar → ∀ N : ℕ,
        ‖∑ j ∈ range N, uflow d L N msq (V₀c msq b₀) j‖ ≤ C * ‖b₀‖) ∧
      (∀ msq b₀, V₀c msq (starRingEnd ℂ b₀) = (V₀c msq b₀).conj) := by
  obtain ⟨L₀, Kℓ, hKℓ, h⟩ := thm_flow_body (d := d) hd
  refine ⟨L₀, Kℓ, hKℓ, fun L _ hL => ?_⟩
  obtain ⟨A₀, hA₀, h⟩ := h L hL
  refine ⟨A₀, hA₀, fun A hA ℓ₀ hℓ₀ hK => ?_⟩
  obtain ⟨bbar, C, κ, V, hbbar, hC, hκ, hbody, hconj⟩ := h A hA ℓ₀ hℓ₀ hK
  classical
  let V' : ℝ → ℂ → Vcoup := fun msq b₀ => if ‖b₀‖ ≤ bbar then V msq b₀ else ⟨0, 0, 0, b₀⟩
  have he : ∀ msq b₀, ‖b₀‖ ≤ bbar → V' msq b₀ = V msq b₀ := fun msq b₀ hb => if_pos hb
  have hb' : ∀ msq b₀, (V' msq b₀).b = b₀ := fun msq b₀ => by
    by_cases hb : ‖b₀‖ ≤ bbar
    · rw [he msq b₀ hb]; exact hbody.1 msq b₀
    · simp only [V', if_neg hb]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := FlowBody.congr hbody hb' he
  refine ⟨bbar, C, κ, V', hbbar, hC, hκ, h0, h1, h2, h3, h4, h5, h6, h7, h8, fun msq b₀ => ?_⟩
  by_cases hb : ‖b₀‖ ≤ bbar
  · have hb2 : ‖starRingEnd ℂ b₀‖ ≤ bbar := by rwa [Complex.norm_conj]
    rw [he _ _ hb, he _ _ hb2, hconj msq b₀ hb]
  · have hb2 : ¬ ‖starRingEnd ℂ b₀‖ ≤ bbar := by rwa [Complex.norm_conj]
    have e1 : V' msq (starRingEnd ℂ b₀) = ⟨0, 0, 0, starRingEnd ℂ b₀⟩ := if_neg hb2
    have e2 : V' msq b₀ = ⟨0, 0, 0, b₀⟩ := if_neg hb
    rw [e1, e2]
    simp [Vcoup.conj]

/-! ### Corollaries for real `b₀` -/

theorem _root_.Loc.Vcoup.im_eq_zero_of_conj {V : Vcoup} (h : V.conj = V) :
    V.z.im = 0 ∧ V.y.im = 0 ∧ V.a.im = 0 ∧ V.b.im = 0 := by
  have hz := congrArg Vcoup.z h
  have hy := congrArg Vcoup.y h
  have ha := congrArg Vcoup.a h
  have hb := congrArg Vcoup.b h
  simp only [Vcoup.conj_z, Vcoup.conj_y, Vcoup.conj_a, Vcoup.conj_b] at hz hy ha hb
  exact ⟨Complex.conj_eq_iff_im.1 hz, Complex.conj_eq_iff_im.1 hy, Complex.conj_eq_iff_im.1 ha,
    Complex.conj_eq_iff_im.1 hb⟩

/-- For real `b`, `V₀^c(m², b)` is self-conjugate. -/
theorem conj_V0c_real {V₀c : ℝ → ℂ → Vcoup}
    (hconj : ∀ msq b₀, V₀c msq (starRingEnd ℂ b₀) = (V₀c msq b₀).conj) (msq b : ℝ) :
    (V₀c msq b).conj = V₀c msq b := by
  rw [← hconj, Complex.conj_ofReal]

/-- For real `b`, the couplings `z, y, a` of `V₀^c(m², b)` are real. -/
theorem V0c_real {V₀c : ℝ → ℂ → Vcoup}
    (hconj : ∀ msq b₀, V₀c msq (starRingEnd ℂ b₀) = (V₀c msq b₀).conj) (msq b : ℝ) :
    (V₀c msq b).z.im = 0 ∧ (V₀c msq b).y.im = 0 ∧ (V₀c msq b).a.im = 0 :=
  let h := Vcoup.im_eq_zero_of_conj (conj_V0c_real hconj msq b)
  ⟨h.1, h.2.1, h.2.2.1⟩

end

end Flow
