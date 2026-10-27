import Ward.MainEst
import Ward.ObsLimitQ1Zero
import Ward.ObsLimitQ2Zero
import Ward.ObsLimitZero
import Ward.CorWardMain
import FRD.GreenAsymp
import FRD.GreenBd

/-!
# Theorems `thm:h02`, `thm:forests0` and `thm:forests` (h02rg.tex lines 316, 353, 511)

For `d ≥ 3` and odd `L ≥ L₀`, there are `β₀`, `κ > 0`, `K` and functions `θ, c₁, c₂` with
`θ(β) = 1 + O(1/β)`, `c₁(β) = c_d + O(1/β)`, `c₂(β) = c_d² + O(1/β)` (`c_d = FRD.cd d`, the
constant of `eq:LapZd`) such that for `β ≥ β₀` and `x ∈ ℤ^d ∖ {0}` (`|x|` the Euclidean norm,
`x` placed on `Λ_N` by `toT`):

* `lim_{h↓0} lim_N ⟨z_0⟩_{β,h} = θ(β)`;
* `lim_{h↓0} lim_N ⟨ξ_0 η_x⟩_{β,h} = c₁(β)/(β|x|^{d-2}) + O(1/(β|x|^{d-2+κ}))`;
* `lim_{h↓0} lim_N (⟨z_0z_x⟩ - ⟨z_0⟩⟨z_x⟩) = -c₂(β)/(β²|x|^{2d-4}) + O(1/(β²|x|^{2d-4+κ}))`;
* `lim_{h↓0} lim_N ⟨u_0·u_x⟩ = -θ(β)² - 2c₁(β)/(β|x|^{d-2}) + O(1/(β|x|^{d-2+κ}))`.

(`thm_h02`.)  By `H02.prop_h02_forest` the same limits give `thm:forests0` (existence of
`θ_d(β) = lim_{h↓0} lim_N P[0 ↔ g]` and `θ_d = 1 + O(1/β)`, `thm_forests0`) and
`thm:forests` (the asymptotics of `τ_β` and `σ_β`, `thm_forests`).  The identities
`θ_d² = ζ_d`, `c₂θ_d²/c₁² = 1` and `c₀ = 2c₁` involve the constants of `thm:forest-macro` and
`cor:aNlimit` and are not part of these statements (see `LOG_A3.md`).

The theorems `thm_h02`, `thm_forests0` and `thm_forests` themselves are in
`H02RG/Main/Theorems.lean`; this file has `H02Body` and `thm_h02_of`.
-/

namespace Ward

noncomputable section

open Finset Grassmann Loc Step Obs FRD PtCorr Psi4 Metric Filter Topology FRD.GreenAsymp

variable {d L : ℕ} [NeZero L] {A ℓ₀ lbar C κ : ℝ} {V₀c : ℝ → ℂ → Vcoup}

/-- The body of `thm:h02` for fixed `β`. -/
def H02Body (d L : ℕ) [NeZero L] (κ' K : ℝ) (θ c₁ c₂ : ℝ → ℝ) (β : ℝ) : Prop :=
  |θ β - 1| ≤ K / β ∧ |c₁ β - cd d| ≤ K / β ∧ |c₂ β - cd d ^ 2| ≤ K / β ∧
  (∀ h, 0 < h → ∀ N : ℕ, 1 ≤ N → ∀ y : Lam d L N,
    H02.avg (nnW d L N β) (fun _ => h) (H02.z y) = H02.avg (nnW d L N β) (fun _ => h) (H02.z 0)) ∧
  (∃ θh' : ℝ → ℝ, (∀ h, 0 < h → Tendsto (fun N => H02.avg (nnW d L N β) (fun _ => h)
      (H02.z (0 : Lam d L N))) atTop (𝓝 (θh' h))) ∧ Tendsto θh' (𝓝[>] 0) (𝓝 (θ β))) ∧
  (∀ x : Zd d, x ≠ 0 → ∃ (τh' : ℝ → ℝ) (τ₀ : ℝ),
    (∀ h, 0 < h → Tendsto (fun N => H02.avg (nnW d L N β) (fun _ => h)
      (H02.ξ (0 : Lam d L N) * H02.η (toT L N x))) atTop (𝓝 (τh' h))) ∧
    Tendsto τh' (𝓝[>] 0) (𝓝 τ₀) ∧
    |τ₀ - c₁ β * eNorm x ^ (-((d : ℝ) - 2)) / β| ≤ K * eNorm x ^ (-((d : ℝ) - 2 + κ')) / β) ∧
  (∀ x : Zd d, x ≠ 0 → ∃ (σh' : ℝ → ℝ) (σ₀ : ℝ),
    (∀ h, 0 < h → Tendsto (fun N => H02.avg (nnW d L N β) (fun _ => h)
        (H02.z (0 : Lam d L N) * H02.z (toT L N x)) -
      H02.avg (nnW d L N β) (fun _ => h) (H02.z (0 : Lam d L N)) *
        H02.avg (nnW d L N β) (fun _ => h) (H02.z (toT L N x))) atTop (𝓝 (σh' h))) ∧
    Tendsto σh' (𝓝[>] 0) (𝓝 σ₀) ∧
    |σ₀ + c₂ β * eNorm x ^ (-(2 * ((d : ℝ) - 2))) / β ^ 2| ≤
      K * eNorm x ^ (-(2 * ((d : ℝ) - 2) + κ')) / β ^ 2) ∧
  (∀ x : Zd d, x ≠ 0 → ∃ (υh' : ℝ → ℝ) (υ₀ : ℝ),
    (∀ h, 0 < h → Tendsto (fun N => H02.avg (nnW d L N β) (fun _ => h)
      (H02.dot (0 : Lam d L N) (toT L N x))) atTop (𝓝 (υh' h))) ∧
    Tendsto υh' (𝓝[>] 0) (𝓝 υ₀) ∧
    |υ₀ + θ β ^ 2 + 2 * c₁ β * eNorm x ^ (-((d : ℝ) - 2)) / β| ≤
      K * eNorm x ^ (-((d : ℝ) - 2 + κ')) / β)

theorem le_div_of {a K β : ℝ} (hβ : 0 < β) (h : a ≤ K) {X : ℝ} (hX : 0 ≤ X) :
    a * X / β ≤ K * X / β :=
  div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h hX) hβ.le

/-- `θ(β) = θh(β, 0)`. -/
abbrev θF (d L : ℕ) [NeZero L] (V₀c : ℝ → ℂ → Vcoup) (lbar : ℝ) (bt mt : ℝ → ℝ → ℝ) :
    ℝ → ℝ := fun β => θh d L V₀c lbar bt mt β 0

/-- `c₁(β) = (1 + s₀(b*, 0)) c_d`. -/
abbrev c1F (d : ℕ) (V₀c : ℝ → ℂ → Vcoup) (bt : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun β => (1 + s0R V₀c (bt β 0) 0) * cd d

/-- `c₂(β) = Re((1 + s₀)² Λ(0, b*)²) c_d²`. -/
abbrev c2Fc (d L : ℕ) [NeZero L] (V₀c : ℝ → ℂ → Vcoup) (lbar : ℝ) (bt : ℝ → ℝ → ℝ) :
    ℝ → ℝ :=
  fun β => ((1 + s0R V₀c (bt β 0) 0 : ℂ) ^ 2 * LamA d L V₀c lbar 0 (bt β 0) ^ 2).re * cd d ^ 2

set_option maxHeartbeats 4000000 in
/-- **`thm:h02`** for a given `V₀c` with `FlowDataW` (and `L` odd) and a given solution
`(bt, mt)` of `cor:ward` (ii). -/
theorem thm_h02_core (hd3 : 3 ≤ d) (HW : FlowDataW d L A ℓ₀ V₀c lbar C κ) (hLodd : Odd L)
    {bbar : ℝ} (hbpos : 0 < bbar) (hb2 : bbar ≤ lbar / 2) (h48 : 48 * C * bbar ≤ 1)
    {β₀ : ℝ} {bt mt : ℝ → ℝ → ℝ} (hsolall : ∀ β, β₀ ≤ β → SolAt V₀c bbar bt mt β) :
    ∃ (β₁ κ' K : ℝ), β₀ ≤ β₁ ∧ 1 ≤ β₁ ∧ κ' = min κ 1 ∧ 0 < κ' ∧ κ' ≤ 1 ∧ 0 ≤ K ∧
      ∀ β, β₁ ≤ β → H02Body d L κ' K (θF d L V₀c lbar bt mt) (c1F d V₀c bt)
        (c2Fc d L V₀c lbar bt) β := by
  have hd1 : 1 ≤ d := by omega
  have hd2' : (1 : ℝ) ≤ (d : ℝ) - 2 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd3
    linarith
  have H := ObsLimHyp.ofW HW hLodd
  have hL3 := three_le_L H
  have hL2 : 2 ≤ L := by omega
  have hl := HW.lbar_pos
  have hC := HW.C_nonneg
  have hκ := HW.κ_pos
  -- the flow constants
  obtain ⟨Cs, hCs, hSall⟩ := exists_stepBd d hd1
  have hS := hSall L A ℓ₀ V₀c lbar C κ H
  obtain ⟨Cs1, hCs1, hS1all⟩ := exists_stepBd1 d hd1
  have hS1 := hS1all L A ℓ₀ V₀c lbar C κ H
  obtain ⟨Cq, Cb, hCq, hCb, hPall⟩ := exists_pairHyp2 d hd3
  have hP := hPall L A ℓ₀ V₀c lbar C κ H
  -- the inputs at `m² = 0`
  have hθ1 := th_lt_one hL2 hκ (L := L)
  have hρ1 := rho_lt_one hd3 hL2 (L := L)
  set KΓ := Cs * C * ℓ₀ ^ 2 * (1 + 1 / (1 - th L κ)) / (1 - rho d L) with hKΓ
  have hKΓ0 : 0 ≤ KΓ := by
    have : 0 < 1 - th L κ := by linarith
    have : 0 < 1 - rho d L := by linarith
    rw [hKΓ]; positivity
  have hΓ : ∀ b₀ : ℂ, ‖b₀‖ ≤ lbar → ‖GamA d L V₀c lbar 0 b₀ - (greenZd d 0 : ℂ)‖ ≤ KΓ * ‖b₀‖ :=
    fun b₀ hb₀ => GamA_zero_sub_green H hd1 hCs hS hd3 hb₀
  obtain ⟨K1, hK1, hQ1⟩ := Qone_zero_sub_green H hd1 hCs1 hS1 hd3
  obtain ⟨K2, hK2, hQ2⟩ := Qtwo_zero_add_green H hd1 hCs hS hCq hCb hP hd3
  set KΛ := Cs * C / (1 - th L κ) with hKΛ
  have hKΛ0 : 0 ≤ KΛ := by
    have : 0 < 1 - th L κ := by linarith
    rw [hKΛ]; positivity
  have hΛ : ∀ b₀ : ℂ, ‖b₀‖ ≤ lbar → ‖LamA d L V₀c lbar 0 b₀ - 1‖ ≤ KΛ * ‖b₀‖ :=
    fun b₀ hb₀ => LamA_sub_one H hd1 hCs hS le_rfl hb₀
  set κg := min κ 1 with hκg
  have hκg0 : 0 < κg := lt_min hκ one_pos
  have hκgκ : κg ≤ κ := min_le_left _ _
  have hκg1 : κg ≤ 1 := min_le_right _ _
  obtain ⟨Cg, hCg, hg⟩ := greenZd_asymp_kappa hd3 hκg1
  obtain ⟨CG, hCG, hG⟩ := greenZd_bound_eNorm hd3
  have hcd : 0 ≤ cd d := by
    unfold cd
    have : 0 < (d : ℝ) / 2 - 1 := by
      have : (3 : ℝ) ≤ d := by exact_mod_cast hd3
      linarith
    exact div_nonneg (Real.Gamma_pos_of_pos this).le (by positivity)
  have hcd2 : 0 ≤ cd d ^ 2 := sq_nonneg _
  -- the constants
  set Kθ := 3 / 2 * (|greenZd d 0| + KΓ * lbar) with hKθ
  set Kc1 := 9 / 2 * C * cd d with hKc1
  set D := 2 * C * (1 + KΛ * lbar) + KΛ with hD
  set Kc2 := 9 / 4 * D * (9 / 4 * D + 2) * cd d ^ 2 with hKc2
  set Kτ := 3 / 2 * (K1 * lbar * Real.sqrt d ^ ((d : ℝ) - 2 + κ) + Cg) with hKτ
  set Kσ := 9 / 4 * (K2 * lbar * Real.sqrt d ^ (2 * ((d : ℝ) - 2) + κ) +
    (1 + KΛ * lbar) ^ 2 * (Cg * (CG + cd d))) with hKσ
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hKθ0 : 0 ≤ Kθ := by rw [hKθ]; positivity
  have hKc10 : 0 ≤ Kc1 := by rw [hKc1]; positivity
  have hKc20 : 0 ≤ Kc2 := by rw [hKc2]; positivity
  have hsq0 : 0 ≤ Real.sqrt d ^ ((d : ℝ) - 2 + κ) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hsq0' : 0 ≤ Real.sqrt d ^ (2 * ((d : ℝ) - 2) + κ) :=
    Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hKτ0 : 0 ≤ Kτ := by rw [hKτ]; positivity
  have hKσ0 : 0 ≤ Kσ := by rw [hKσ]; positivity
  set K := Kθ + Kc1 + Kc2 + 2 * Kτ + Kσ + (cd d ^ 2 + Kc2) with hK
  have hK0' : 0 ≤ K := by rw [hK]; positivity
  refine ⟨max β₀ 1, κg, K, le_max_left _ _, le_max_right _ _, hκg, hκg0, hκg1, hK0', fun β hβ => ?_⟩
  have hβ1 : 1 ≤ β := le_trans (le_max_right _ _) hβ
  have hβp : 0 < β := by linarith
  have hsol : SolAt V₀c bbar bt mt β := hsolall β (le_trans (le_max_left _ _) hβ)
  have hβinv : ∀ {X : ℝ}, 0 ≤ X → X / β ^ 2 ≤ X / β := fun hX =>
    div_le_div_of_nonneg_left hX hβp (by nlinarith)
  -- the pieces
  have eθ := est_θ HW hLodd hd3 hbpos hb2 h48 hsol hKΓ0 hΓ
  have ec1 := est_c1 HW hLodd hd3 hbpos hb2 h48 hsol hcd
  have ec2 := est_c2 HW hLodd hd3 hbpos hb2 h48 hsol hKΛ0 hΛ hβ1
  have hKle : ∀ {a : ℝ}, a ≤ K → ∀ {X : ℝ}, 0 ≤ X → a * X / β ≤ K * X / β :=
    fun {_} h {_} hX => le_div_of hβp h hX
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine eθ.trans (div_le_div_of_nonneg_right ?_ hβp.le)
    rw [hK]; linarith
  · refine ec1.trans (div_le_div_of_nonneg_right ?_ hβp.le)
    rw [hK]; linarith
  · refine ec2.trans (div_le_div_of_nonneg_right ?_ hβp.le)
    rw [hK]; linarith
  · intro h hh N hN y
    obtain ⟨hb, -, -, hs, -, -⟩ := sol_facts HW hLodd hd3 hbpos hb2 h48 hsol hh.le
    obtain ⟨-, -, -, hm, hβe, hhF, -⟩ := hsol h hh.le
    have := avgH_z_transl (N := N) HW.conj HW.hb hb hs (hm hh) (by rw [hhF]; exact hh.le) hN y
    rwa [hβe, hhF] at this
  · exact ⟨θh d L V₀c lbar bt mt β, fun h hh => lim_z HW hLodd hd3 hbpos hb2 h48 hsol hCs hS hh,
      cont_θh HW hLodd hd3 hbpos hb2 h48 hsol hCs hS⟩
  · intro x hx
    refine ⟨τh d L V₀c lbar bt mt β x, τh d L V₀c lbar bt mt β x 0,
      fun h hh => lim_ξη HW hLodd hd3 hbpos hb2 h48 hsol hCs1 hS1 hh hx,
      cont_τh HW hLodd hd3 hbpos hb2 h48 hsol hCs1 hS1 hx, ?_⟩
    have := est_τ HW hLodd hd3 hbpos hb2 h48 hsol hK1 hCg hκgκ hκg0.le hQ1 hg hx
    refine this.trans (hKle ?_ (eNorm_rpow_nonneg x _))
    rw [hK]; linarith
  · intro x hx
    refine ⟨σh d L V₀c lbar bt mt β x, σh d L V₀c lbar bt mt β x 0,
      fun h hh => lim_cov HW hLodd hd3 hbpos hb2 h48 hsol hCs hS hCq hCb hP hh hx,
      cont_σh HW hLodd hd3 hbpos hb2 h48 hsol hCs hS hCq hCb hP hx, ?_⟩
    have := est_σ HW hLodd hd3 hbpos hb2 h48 hsol hK2 hKΛ0 hCg hCG hκgκ hκg0.le hQ2 hΛ hg hG
      hcd hx
    refine this.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right ?_ (eNorm_rpow_nonneg x _)) (by positivity))
    rw [hK]; linarith
  · intro x hx
    refine ⟨fun h => -2 * τh d L V₀c lbar bt mt β x h - σh d L V₀c lbar bt mt β x h -
        θh d L V₀c lbar bt mt β h ^ 2,
      -2 * τh d L V₀c lbar bt mt β x 0 - σh d L V₀c lbar bt mt β x 0 -
        θh d L V₀c lbar bt mt β 0 ^ 2,
      fun h hh => lim_dot HW hLodd hd3 hbpos hb2 h48 hsol hCs hS hCs1 hS1 hCq hCb hP hh hx,
      (((cont_τh HW hLodd hd3 hbpos hb2 h48 hsol hCs1 hS1 hx).const_mul (-2)).sub
        (cont_σh HW hLodd hd3 hbpos hb2 h48 hsol hCs hS hCq hCb hP hx)).sub
        ((cont_θh HW hLodd hd3 hbpos hb2 h48 hsol hCs hS).pow 2), ?_⟩
    have eτ := est_τ HW hLodd hd3 hbpos hb2 h48 hsol hK1 hCg hκgκ hκg0.le hQ1 hg hx
    have eσ := est_σ HW hLodd hd3 hbpos hb2 h48 hsol hK2 hKΛ0 hCg hCG hκgκ hκg0.le hQ2 hΛ hg hG
      hcd hx
    rw [← hKτ] at eτ
    rw [← hKσ] at eσ
    set e1 := eNorm x ^ (-((d : ℝ) - 2 + κg))
    have he1 : 0 ≤ e1 := eNorm_rpow_nonneg x _
    have he2 : eNorm x ^ (-(2 * ((d : ℝ) - 2) + κg)) ≤ e1 := eNorm_rpow_anti hx (by linarith)
    have he3 : eNorm x ^ (-(2 * ((d : ℝ) - 2))) ≤ e1 := eNorm_rpow_anti hx (by linarith)
    have he30 : 0 ≤ eNorm x ^ (-(2 * ((d : ℝ) - 2))) := eNorm_rpow_nonneg x _
    have he20 : 0 ≤ eNorm x ^ (-(2 * ((d : ℝ) - 2) + κg)) := eNorm_rpow_nonneg x _
    set c₂' := ((1 + s0R V₀c (bt β 0) 0 : ℂ) ^ 2 * LamA d L V₀c lbar 0 (bt β 0) ^ 2).re * cd d ^ 2
    have hc₂ : |c₂'| ≤ cd d ^ 2 + Kc2 / β := by
      have := abs_sub_abs_le_abs_sub c₂' (cd d ^ 2)
      rw [abs_of_nonneg (sq_nonneg (cd d))] at this
      have := ec2; linarith
    have hc₂' : |c₂'| ≤ cd d ^ 2 + Kc2 := by
      have : Kc2 / β ≤ Kc2 := by rw [div_le_iff₀ hβp]; nlinarith
      linarith
    -- `|σ₀| ≤ (Kσ + |c₂|) e1 / β`
    have hσ0 : |σh d L V₀c lbar bt mt β x 0| ≤ (Kσ + (cd d ^ 2 + Kc2)) * e1 / β := by
      have h1 : |σh d L V₀c lbar bt mt β x 0| ≤
          Kσ * eNorm x ^ (-(2 * ((d : ℝ) - 2) + κg)) / β ^ 2 +
            |c₂'| * eNorm x ^ (-(2 * ((d : ℝ) - 2))) / β ^ 2 := by
        have := abs_sub_abs_le_abs_sub (σh d L V₀c lbar bt mt β x 0 +
          c₂' * eNorm x ^ (-(2 * ((d : ℝ) - 2))) / β ^ 2)
          (c₂' * eNorm x ^ (-(2 * ((d : ℝ) - 2))) / β ^ 2)
        rw [add_sub_cancel_right] at this
        have h2 : |c₂' * eNorm x ^ (-(2 * ((d : ℝ) - 2))) / β ^ 2| =
            |c₂'| * eNorm x ^ (-(2 * ((d : ℝ) - 2))) / β ^ 2 := by
          rw [abs_div, abs_mul, abs_of_nonneg he30, abs_of_nonneg (by positivity : (0 : ℝ) ≤ β ^ 2)]
        have h5 := abs_sub (σh d L V₀c lbar bt mt β x 0 +
          c₂' * eNorm x ^ (-(2 * ((d : ℝ) - 2))) / β ^ 2)
          (c₂' * eNorm x ^ (-(2 * ((d : ℝ) - 2))) / β ^ 2)
        rw [add_sub_cancel_right, h2] at h5
        have h6 := this
        linarith
      have h3 : Kσ * eNorm x ^ (-(2 * ((d : ℝ) - 2) + κg)) / β ^ 2 ≤ Kσ * e1 / β :=
        (hβinv (mul_nonneg hKσ0 he20)).trans (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left he2 hKσ0) hβp.le)
      have h4 : |c₂'| * eNorm x ^ (-(2 * ((d : ℝ) - 2))) / β ^ 2 ≤ (cd d ^ 2 + Kc2) * e1 / β :=
        (hβinv (mul_nonneg (abs_nonneg _) he30)).trans (div_le_div_of_nonneg_right
          (mul_le_mul hc₂' he3 he30 (by positivity)) hβp.le)
      have : (Kσ + (cd d ^ 2 + Kc2)) * e1 / β = Kσ * e1 / β + (cd d ^ 2 + Kc2) * e1 / β := by ring
      linarith
    have e : -2 * τh d L V₀c lbar bt mt β x 0 - σh d L V₀c lbar bt mt β x 0 -
          θh d L V₀c lbar bt mt β 0 ^ 2 + θh d L V₀c lbar bt mt β 0 ^ 2 +
          2 * ((1 + s0R V₀c (bt β 0) 0) * cd d) * eNorm x ^ (-((d : ℝ) - 2)) / β =
        -2 * (τh d L V₀c lbar bt mt β x 0 -
          (1 + s0R V₀c (bt β 0) 0) * cd d * eNorm x ^ (-((d : ℝ) - 2)) / β) -
          σh d L V₀c lbar bt mt β x 0 := by ring
    show |_| ≤ _
    rw [e]
    calc |-2 * (τh d L V₀c lbar bt mt β x 0 -
          (1 + s0R V₀c (bt β 0) 0) * cd d * eNorm x ^ (-((d : ℝ) - 2)) / β) -
          σh d L V₀c lbar bt mt β x 0|
        ≤ 2 * (Kτ * e1 / β) + (Kσ + (cd d ^ 2 + Kc2)) * e1 / β := by
          refine (abs_sub _ _).trans (add_le_add ?_ hσ0)
          rw [abs_mul, show |(-2 : ℝ)| = 2 by norm_num]
          exact mul_le_mul_of_nonneg_left eτ (by norm_num)
      _ = (2 * Kτ + Kσ + (cd d ^ 2 + Kc2)) * e1 / β := by ring
      _ ≤ K * e1 / β := hKle (by rw [hK]; linarith) he1

/-- **`thm:h02`** for a given `V₀c` with `FlowDataW` (and `L` odd). -/
theorem thm_h02_of (hd3 : 3 ≤ d) (HW : FlowDataW d L A ℓ₀ V₀c lbar C κ) (hLodd : Odd L) :
    ∃ (β₀ κ' K : ℝ) (θ c₁ c₂ : ℝ → ℝ), 0 < β₀ ∧ 0 < κ' ∧ 0 ≤ K ∧
      ∀ β, β₀ ≤ β → H02Body d L κ' K θ c₁ c₂ β := by
  obtain ⟨bbar, Kw, hbpos, hb2, -, hK0, hKb, h48, hall, hh0, -⟩ := cor_ward_i hd3 HW
  obtain ⟨β₀, bt, mt, -, hsolall⟩ := cor_ward_ii hd3 HW hbpos hb2 hK0 hKb h48 hall hh0
  obtain ⟨β₁, κ', K, -, hβ₁, -, hκ', -, hK, hmain⟩ :=
    thm_h02_core hd3 HW hLodd hbpos hb2 h48 hsolall
  exact ⟨β₁, κ', K, _, _, _, by linarith, hκ', hK, hmain⟩

/-! ### The ghost connection probability (for `thm:forests0`) -/

/-- `P_{β,h}[0 ↔ g]` on `Λ_N`. -/
abbrev Pg (d L N : ℕ) [NeZero L] (β h : ℝ) (hβ : 0 ≤ β) : ℝ :=
  H02.arborealProb (H02.ghostW (nnW d L N β) (fun _ => h))
    (H02.ghostW_symm (nnW_symm β) _) (fun F => F.Reachable (some (0 : Lam d L N)) none)

theorem Pg_eq {N : ℕ} {β h : ℝ} (hβ : 0 ≤ β) (hh : 0 ≤ h) :
    Pg d L N β h hβ = H02.avg (nnW d L N β) (fun _ => h) (H02.z 0) :=
  (H02.prop_h02_forest (nnW_symm β) (nnW_nonneg hβ) h hh 0 0).1

end

end Ward
