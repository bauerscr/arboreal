import Spin2.Case2.Case2Nu
import Spin2.Multiscale.ObsRel

/-!
# `Case2Bulk` discharged under the master constants; `thm:multiscale` (Case 2) without `Case2Bulk`

* `c2ctx_master`: the bulk context `C2Ctx` along every admissible trajectory of the master
  construction (constant `c = ceff L c_R = 3β + 7 + 9c_R`);
* `c2EReq`, `c2EReq_ev`: the requirement on `ε` (the dressed-bubble constants `(ζ̄, K, c_S)` of
  `prop:d2` (`LcProp`), `2cε ≤ ζ̄`, `c_Rε ≤ 1`, `8c_xε ≤ 1`, `βε ≤ 1/2` and the smallness
  `B'ε ≤ 1/8` of `Case2Loop`), passed to the master construction through `Eext`; `A ≥ 2` through
  `Aext`;
* `LoopConcl`: along every admissible trajectory (`N_h = N - 2`) and for every Case-(2) observable
  initial state, `Case2Bulk` with the fixed constants `B₁ = bubB`, `B₂ = nuB`, `B₃ = (9/64)c²`,
  `c_q = 7c`, and `Case2Loop`;
* **`thm_multiscale_case2C`**: one set of constants with `FlowC2Concl`, `ε ≤ 1`, `BetaConcl`,
  `LamConcl`, `LoopConcl`, `MultiConcl2C` — `thm:multiscale` for `λ̂ = μ_a/μ_{a,0}` conditional only
  on `RGInput` and `Case2Rel`.
-/

set_option linter.unusedSectionVars false

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Filter Topology Step2.D2

/-! ### The constants -/

/-- The bulk constant `c = 3β + 7 + 9c_R` of `C2Ctx`. -/
def ceff (L : ℕ) (c : ℝ) : ℝ := 3 * betaL L + 7 + 9 * c

/-- The requirement on `ε` (`c = c_R`, `c' = c_x`; `C_q, C_l, c_S` of `nu_sharp`). -/
def c2EReq (Cq Cl cS : ℝ) (L : ℕ) (_A c c' ε : ℝ) : Prop :=
  ∀ [NeZero L], 7 ≤ L → ∃ ζbar K cS2 : ℝ, 0 < ζbar ∧ 0 ≤ K ∧ 0 ≤ cS2 ∧ LcProp L ζbar K cS2 ∧
    2 * ceff L c * ε ≤ ζbar ∧ c * ε ≤ 1 ∧ 8 * c' * ε ≤ 1 ∧ betaL L * ε ≤ 1 / 2 ∧
    case2BK (betaL L) (bubB L (ceff L c) K cS2) (nuB L Cq Cl cS c' c (ceff L c))
      (9 / 64 * ceff L c ^ 2) (7 * ceff L c) 2 * ε ≤ 1 / 8

theorem c2EReq_ev (Cq Cl cS : ℝ) (L : ℕ) (A c c' : ℝ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), c2EReq Cq Cl cS L A c c' ε := by
  by_cases hL : L ≠ 0 ∧ 7 ≤ L
  · haveI : NeZero L := ⟨hL.1⟩
    obtain ⟨ζbar, hζ, K, cS2, hK, hcS2, hLc⟩ := lcProp_of (L := L) hL.2
    filter_upwards [ev_lin (2 * ceff L c) hζ, ev_lin c one_pos, ev_lin (8 * c') one_pos,
      ev_lin (betaL L) (by norm_num : (0 : ℝ) < 1 / 2),
      ev_lin (case2BK (betaL L) (bubB L (ceff L c) K cS2) (nuB L Cq Cl cS c' c (ceff L c))
        (9 / 64 * ceff L c ^ 2) (7 * ceff L c) 2) (by norm_num : (0 : ℝ) < 1 / 8)]
      with ε h1 h2 h3 h4 h5
    intro _ _
    exact ⟨ζbar, K, cS2, hζ, hK, hcS2, hLc, h1, h2, h3, h4, h5⟩
  · exact Eventually.of_forall fun _ inst hL7 => absurd ⟨inst.out, hL7⟩ hL

/-! ### The bulk context along the master trajectories -/

set_option maxHeartbeats 4000000 in
/-- **`C2Ctx` along a regular history** of the master construction. -/
theorem c2ctx_master {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    {Nh : ℕ} (hNh : Nh + 2 = N) (hL49 : 49 ≤ L)
    {C₀ η εs CK C₂ CD Cq Cl cS : ℝ} (hSB : StepBounds L R.A C₀ η εs CK C₂ CD Cq Cl cS)
    {κ cg cm cT ε : ℝ} (H : ApHyp R ((L : ℝ) ^ 2) κ cg cm cT ε εs C₀ C₂ Cq Cl cS)
    (hm1 : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hV : ∀ j < Nh, ValidAt R j) (hVL : ValidAtL R Nh) (hρ0 : 0 ≤ R.ρ) (hρ8 : R.ρ ≤ 1 / 8)
    (hmsq : R.msq ∈ mRange L N) (hβε : betaL L * ε ≤ 1 / 2) {t : Hist.Seq (Xs R)}
    (ht : InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT ε Nh t) :
    C2Ctx R Nh t (cmu ((L : ℝ) ^ 2) cm) (cZ R)
      (3 * betaL L + 16 * cmu ((L : ℝ) ^ 2) cm * R.ℓ ^ 2 + 20 * cZ R)
      (ceff L (cR R ((L : ℝ) ^ 2) cm C₂)) := by
  have hL8 : 8 ≤ L := by omega
  have hβ2 := betaL_ge hL8
  have hβ0 : 0 ≤ betaL L := by linarith
  have hcg0 : 0 ≤ cg := H.hcg
  have hcgε : cg * ε ≤ betaL L / 4 := by have := H.h6; linarith
  have hδ2 : (1 / 2 : ℝ) ≤ 1 / 2 := le_rfl
  -- the band along the history
  have hband : ∀ k < Nh, (t k).1 ≤ (t (k + 1)).1 ∧
      |(t (k + 1)).1 - (t k).1| ≤ 7 / 4 * betaL L * (t k).1 ^ 2 ∧ (t (k + 1)).1 ≤ 2 * (t k).1 := by
    intro k hk
    have hr := ht.2 k hk
    obtain ⟨hg, hgε, -, -⟩ := ht.1 k hk.le
    have h3 : cg * (t k).1 ^ 3 ≤ betaL L / 4 * (t k).1 ^ 2 := by
      have : cg * (t k).1 ≤ cg * ε := mul_le_mul_of_nonneg_left hgε hcg0
      have e : cg * (t k).1 ^ 3 = (cg * (t k).1) * (t k).1 ^ 2 := by ring
      rw [e]; exact mul_le_mul_of_nonneg_right (this.trans hcgε) (sq_nonneg _)
    rw [abs_le] at hr
    have hg2 : 0 ≤ betaL L * (t k).1 ^ 2 := by positivity
    refine ⟨by nlinarith [hr.1], ?_, ?_⟩
    · rw [abs_le]; constructor <;> nlinarith [hr.1, hr.2]
    · have h4 : 7 / 4 * betaL L * (t k).1 ^ 2 ≤ 7 / 8 * (t k).1 := by
        have : betaL L * (t k).1 ≤ betaL L * ε := mul_le_mul_of_nonneg_left hgε hβ0
        have e : 7 / 4 * betaL L * (t k).1 ^ 2 = 7 / 4 * (betaL L * (t k).1) * (t k).1 := by ring
        rw [e]; nlinarith
      nlinarith [hr.2]
  have hDh : ∀ j ≤ Nh, InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT ε j t := fun j hj =>
    ⟨fun i hi => ht.1 i (by omega), fun i hi => ht.2 i (by omega)⟩
  have hcmu := H.hcmu
  have hC₂ := H.hC₂
  have hcZ : 0 ≤ cZ R := by unfold cZ; positivity
  have hcR := cV_le_cR R hcmu hC₂ (Λ := (L : ℝ) ^ 2)
  obtain ⟨e1, e2, e3, e4⟩ := ell_parts R hcmu (Λ := (L : ℝ) ^ 2) (cm := cm)
  have hcV0 : 0 ≤ cV R ((L : ℝ) ^ 2) cm := by
    have : 0 ≤ R.ℓ ^ 4 := by positivity
    linarith
  have hce : cR R ((L : ℝ) ^ 2) cm C₂ ≤ ceff L (cR R ((L : ℝ) ^ 2) cm C₂) := by
    unfold ceff; linarith
  have hcR0 : 0 ≤ cR R ((L : ℝ) ^ 2) cm C₂ := by linarith
  have hmass : R.msq * ((L : ℝ) ^ (Nh + 1)) ^ 2 ≤ 1 := by
    have := msq_horizon (L := (L : ℝ)) (by exact_mod_cast (by omega : 1 ≤ L)) hmsq.2 (Nh := Nh)
      (k := 0) (by omega)
    simpa using this
  have hε1 : ε ≤ 1 := H.hε1
  exact {
    hN := by omega
    hL7 := by omega
    hρ0 := hρ0
    hρ8 := hρ8
    hV := hV
    hVL := hVL
    hg := fun j hj => ⟨(ht.1 j hj).1, (ht.1 j hj).2.1.trans hε1⟩
    hgm := fun j hj => (hband j hj).1
    hg2 := fun j hj => (hband j hj).2.2
    hμ := fun j hj => (ht.1 j hj).2.2.1
    hζ := fun j hj => norm_zetaH_le R hSB hV hm1 hβ0 (by norm_num) H hρ0 t hj (hDh j hj)
    hdg := fun i hi => by
      obtain ⟨hg, -, hμ, -⟩ := ht.1 i hi.le
      obtain ⟨hg1, -, hμ1, -⟩ := ht.1 (i + 1) hi
      obtain ⟨-, hΔ, hgg⟩ := hband i hi
      have h := hist_dg_w R hρ0 hρ8 t i hcmu hcZ hβ0 hg.le hg1.le hgg hΔ hμ hμ1
        (norm_zetaH_le R hSB hV hm1 hβ0 (by norm_num) H hρ0 t (by omega) (hDh (i + 1) hi))
        (norm_Zw1_le R hρ0 i (fun i' hi' => hV i' (by omega)) t)
        (norm_Zw1_succ_le R hρ0 i (fun i' hi' => hV i' (by omega)) t)
      have hz := zH_pos R hρ0 hρ8 t (i + 1)
      rw [div_le_iff₀ (by positivity)] at h
      exact h
    hZw := fun j hj => norm_Zw1_le R hρ0 j (fun i hi => hV i (by omega)) t
    hm0 := hmsq.1.le
    hm := hmass
    hcmu := hcmu
    hcz := hcZ
    hcd := by positivity
    hc4 := by linarith
    hcm := by linarith
    hcz1 := by linarith
    hcz2 := by
      have : 2 * cV R ((L : ℝ) ^ 2) cm / 49 ≤ cV R ((L : ℝ) ^ 2) cm := by linarith
      linarith
    hcd1 := by
      have := cd_le_cR R hcmu hC₂ (betaL L) (Λ := (L : ℝ) ^ 2) (cm := cm)
      unfold ceff; linarith }

/-! ### `Case2Bulk` and `Case2Loop` along the master trajectories -/

/-- `Case2Bulk` and `Case2Loop` along every admissible trajectory (`N_h = N - 2`), for every
Case-(2) observable initial state, with fixed constants. -/
def LoopConcl (L : ℕ) [NeZero L] (ℓ A ρ κ cm cT ε B₁ B₂ B₃ cq B' : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
  ∀ m ∈ mRange L N, ∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
  ∀ (P : Obs2.ObsPts 2 L N) (V : Obs2.OCoup .two), 0 ≤ B₁ + B₂ + B₃ ∧
    Case2Bulk R P Nh m b μ₀ B₁ B₂ B₃ cq ∧ Case2Loop R P V Nh m b μ₀ (B₁ + B₂ + B₃) B' cq

/-- **`thm:multiscale` for `λ̂ = μ_a/μ_{a,0}`**, conditional on `RGInput` and `Case2Rel` only. -/
def MultiConcl2C (L : ℕ) [NeZero L] (ℓ A ρ κ cg cm cT ε Ke KZ KG B B' cq : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
  ∀ m ∈ mRange L N, ∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
  ∀ (P : Obs2.ObsPts 2 L N) (V : Obs2.OCoup .two) (cδ KP : ℝ), 0 ≤ cδ → 0 ≤ KP →
    Obs2.OCoup2.mua V ≠ 0 → Case2Rel R P V Nh m b μ₀ cδ →
    RGInput R Nh m b μ₀ (lamHat2 R P V m b μ₀) KP →
  ∀ x : Lam 2 L N, x ≠ 0 → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∃ jp : ℕ, (jp : ℤ) = jPhys L N (eucl x / (L : ℝ) ^ N) ∧
      jp ≤ Obs.coal L (0 : Lam 2 L N) x ∧ Obs.coal L (0 : Lam 2 L N) x ≤ jp + 1 ∧
      |Pconn L N (1 / b) x - thetaSq R m b μ₀ jp| ≤
        multK L cg Ke KZ KG (max (lamRelK (betaL L) cg B B' cq cδ (eRange (betaL L) Ke 1) 4) 0)
          KP * thetaSq R m b μ₀ jp / betaJ R m b μ₀ jp

set_option maxHeartbeats 4000000 in
/-- **Expected result `thm:multiscale` for `λ̂ = μ_a/μ_{a,0}`, `Case2Bulk` discharged**: one set of
constants with `FlowC2Concl`, `ε ≤ 1`, `BetaConcl`, `LamConcl`, `LoopConcl` (`Case2Bulk` and
`Case2Loop` along every admissible trajectory, fixed constants) and `MultiConcl2C` (conditional on
`RGInput` and `Case2Rel` only). -/
theorem thm_multiscale_case2C : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ κ cg cm cT ε Ke Cf Cb KZ KG B₁ B₂ B₃ cq B' : ℝ,
      FlowC2Concl L ℓ A ρ κ cg cm cT ε Ke Cf Cb ∧ ε ≤ 1 ∧
      BetaConcl L ℓ A ρ κ cg cm cT ε Ke Cb ∧ LamConcl L ℓ A ρ κ cg cm cT ε Ke ∧
      LoopConcl L ℓ A ρ κ cm cT ε B₁ B₂ B₃ cq B' ∧
      MultiConcl2C L ℓ A ρ κ cg cm cT ε Ke KZ KG (B₁ + B₂ + B₃) B' cq := by
  obtain ⟨Cq, hCq, Cl, hCl, cS, hcS, hnu⟩ := nu_sharp
  obtain ⟨L₀, hL₀⟩ := thm_flow_master_all (fun _ A => 2 ≤ A) (fun _ => ⟨2, fun _ h => h⟩)
    (c2EReq Cq Cl cS) (c2EReq_ev Cq Cl cS)
  refine ⟨max L₀ (max 49 ⌈pauliL0 2⌉₊), fun L _ hL => ?_⟩
  obtain ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, Cf, Cb, KZ, KG, hC2, hε1, -, -, hSp, hMag, hB, hA2, -,
    C₀x, ηx, εsx, CKx, C₂x, CDx, Cqx, Clx, cSx, hSBx, hEx, hXm⟩ :=
    hL₀ L (le_trans (le_max_left _ _) hL)
  have hL49 : 49 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
  have hLp : pauliL0 2 ≤ L := (Nat.le_ceil _).trans (by
    exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL)
  have hL8 : 2 ^ (2 + 3) + 8 * 2 < L := by norm_num; omega
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (by omega : 2 ≤ L)
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8, -, hCN⟩ := id hC2
  let R₀ : RGPar 2 L 1 := ⟨Pc, 0, ℓ, A, 0, ρ⟩
  obtain ⟨ζbar, K, cS2, -, hK, hcS2, hLc, hζε, hcε, hc'ε, hβε, hsm⟩ := hEx R₀ rfl (by omega)
  set c := cR R₀ ((L : ℝ) ^ 2) cm C₂x with hc
  set ce := ceff L c with hce
  have hNu := hnu L hL8 hLp
  have hβ0 : 0 ≤ betaL L := by have := betaL_ge (by omega : 8 ≤ L); linarith
  -- the loop conclusion
  have hLoop : LoopConcl L ℓ A ρ κ cm cT ε (bubB L ce K cS2) (nuB L Cq Cl cS (cx κ cT) c ce)
      (9 / 64 * ce ^ 2) (7 * ce) (case2BK (betaL L) (bubB L ce K cS2) (nuB L Cq Cl cS (cx κ cT) c ce)
        (9 / 64 * ce ^ 2) (7 * ce) 2) := by
    intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm P V
    set R' := R.withMsq m with hR'
    obtain ⟨H, hm1, F1⟩ := hXm N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm
    obtain ⟨hV, hVL⟩ := (hCN N R hP hi0 hRℓ hRA hRρ hN Nh hNh).2.2.2.2.2.2.2.2.2 m hm
    have ht := admissible_InDh_rg R' F1 hadm Nh le_rfl
    have hRA' : R'.A = A := hRA
    have hρ0' : 0 ≤ R'.ρ := by rw [show R'.ρ = ρ from hRρ]; exact hρpos.le
    have hρ8' : R'.ρ ≤ 1 / 8 := by rw [show R'.ρ = ρ from hRρ]; exact hρ8
    have hcR : cR R' ((L : ℝ) ^ 2) cm C₂x = c := cR_congr (show R.ℓ = ℓ from hRℓ) _ _ _
    have hSB' : StepBounds L R'.A C₀x ηx εsx CKx C₂x CDx Cqx Clx cSx := by rw [hRA']; exact hSBx
    have hmsq : R'.msq ∈ mRange L N := hm
    have X := c2ctx_master R' hNh hL49 hSB' H hm1 hV hVL hρ0' hρ8' hmsq hβε ht
    rw [hcR] at X
    set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
    have hgε : ∀ j ≤ Nh, (t j).1 ≤ ε := fun j hj => (ht.1 j hj).2.1
    have hP' : R'.P = Pc := hP
    have hce0 : 0 ≤ ce := X.c_nonneg
    have hbulk : Case2Bulk R P Nh m b μ₀ (bubB L ce K cS2) (nuB L Cq Cl cS (cx κ cT) c ce)
        (9 / 64 * ce ^ 2) (7 * ce) := by
      refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
      · exact X.bubble_le hP' hLc hK hcS2 hm.1 hm.2 hgε hζε hk P.a
      · have h := X.nuflow_le hCq hCl hcS hNu hSB' hm1 hβ0 (by norm_num) H ht
          (by rw [hRA']; exact hA2) (by rw [hcR]; exact hcε) hc'ε hk P.a
        rw [hcR] at h
        exact h
      · exact X.drift_le hk P.a
      · exact X.q_le hk P.a
    have hB1 : 0 ≤ bubB L ce K cS2 := by
      unfold bubB; have := bubE_nonneg; have := bubF_nonneg (L := L) hce0 hK hcS2
      have : 0 ≤ betaL L / 3 := by linarith
      positivity
    have hB2 : 0 ≤ nuB L Cq Cl cS (cx κ cT) c ce := by
      have hQ1 : 1 ≤ Q1 2 := one_le_Q1 (by norm_num)
      have hN0 : 0 ≤ cNear 2 L := Nat.cast_nonneg _
      have hcx : 0 ≤ cx κ cT := H.hcx
      have hQc : 0 ≤ cNear 2 L * Q1 2 ^ 2 + Q1 2 :=
        add_nonneg (mul_nonneg hN0 (sq_nonneg _)) (by linarith)
      unfold nuB
      have : 0 ≤ 16 * (L : ℝ) ^ 2 * Cq * cS * Cl * cx κ cT :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hCq) (by linarith)) hCl) hcx
      have : 0 ≤ 2 * Cq * Cl * (L : ℝ) ^ 2 * (cNear 2 L * Q1 2 ^ 2 + Q1 2) * c ^ 2 :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCq) hCl)
          (sq_nonneg _)) hQc) (sq_nonneg _)
      linarith
    have hB3 : 0 ≤ 9 / 64 * ce ^ 2 := by positivity
    refine ⟨by linarith, hbulk,
      case2Loop_of (fun i hi => hV i hi) hB1 hB2 hB3 ?_ hβ0 ?_ ?_ ?_ ?_ hbulk⟩
    · positivity
    · exact fun k hk => ⟨(X.hg k hk.le).1.le, (X.hg k hk.le).2⟩
    · exact fun k hk => ⟨zA_nonneg L hm.1.le k, zA_le_two (by linarith) (le_trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
          (pow_le_pow_right₀ (by linarith) (by omega)) 2) hm.1.le) X.hm)⟩
    · exact fun k hk => X.hg2 k hk
    · intro k hk
      have h1 := hgε k hk.le
      have h0 := (X.hg k hk.le).1.le
      have hB0 : 0 ≤ case2BK (betaL L) (bubB L ce K cS2) (nuB L Cq Cl cS (cx κ cT) c ce)
          (9 / 64 * ce ^ 2) (7 * ce) 2 := by
        unfold case2BK
        have : 0 ≤ 7 * ce * (2 + 1) := by positivity
        have : 0 ≤ betaL L / 3 := by linarith
        linarith
      exact (mul_le_mul_of_nonneg_left h1 hB0).trans hsm
  refine ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, Cf, Cb, KZ, KG, bubB L ce K cS2,
    nuB L Cq Cl cS (cx κ cT) c ce, 9 / 64 * ce ^ 2, 7 * ce,
    case2BK (betaL L) (bubB L ce K cS2) (nuB L Cq Cl cS (cx κ cT) c ce) (9 / 64 * ce ^ 2)
      (7 * ce) 2, hC2, hε1, hB, lamConcl_of hL2 hε1 hSp, hLoop, ?_⟩
  have hM2 := multiConcl2_of hL2 hε1 hSp (multiConcl_of (by omega) hε1 hSp hMag)
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm P V cδ KP hcδ hKP hmu hrel hrg x hx hj
  obtain ⟨hB0, -, hloop⟩ := hLoop N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm P V
  exact hM2 N R hP hi0 hRℓ hRA hRρ Nh hNh.le m hm b μ₀ hadm P V _ _ (7 * ce) cδ KP
    hB0 hcδ hKP hmu hrel hloop hrg x hx hj

end

end Spin2
