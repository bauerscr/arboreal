import Ward.Main
import Ward.ForestMacro

-- Merged from `Ward/FinVolMain.lean` (phase 3).
section

/-!
# `cor:anm0`, `cor:conn4pt`, `cor:aNlimit` with the full quantifier prefix

For `d ≥ 3` and odd `L ≥ L₀` there are `A, ℓ₀` and an initial coupling `V₀c` with `FlowDataW`
for which the statements of `cor_anm0_of`, `cor_conn4pt_of`, `cor_aNlimit_of` hold. (For a common
`V₀c`, use `exists_flowDataW` and the `_of` forms.)
-/

namespace Ward

noncomputable section

open Finset Grassmann Loc Step Obs FRD PtCorr Psi4 Filter Topology Metric

variable {d : ℕ}

/-- `cor_anm0_of` with the full quantifier prefix. -/
theorem cor_anm0 (hd : 3 ≤ d) : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → Odd L →
    ∃ (A ℓ₀ : ℝ) (V₀c : ℝ → ℂ → Vcoup) (lbar C κ : ℝ), FlowDataW d L A ℓ₀ V₀c lbar C κ ∧
    (∃ bbar Ca : ℝ, 0 < bbar ∧ bbar ≤ lbar / 2 ∧ bbar ≤ 1 ∧ 0 ≤ Ca ∧
      (∀ b, 0 < b → b ≤ bbar → hF V₀c b 0 = 0 ∧ (GamA d L V₀c lbar 0 b).im = 0 ∧
        (LamA d L V₀c lbar 0 b).im = 0 ∧ |lamInf d L V₀c lbar b - 1| ≤ 1 / 2) ∧
      ∀ N : ℕ, 2 ≤ N → ∀ b, 0 < b → b ≤ bbar →
        0 < atR d L V₀c N b ∧ Fintype.card (Lam d L N) * atR d L V₀c N b ≤ 8 * b ∧
        ∃ E : ℝ, |E| ≤ Ca * b * (L : ℝ) ^ (-(min κ 1 * N)) ∧
          1 = c2F V₀c b 0 * (gamInf d L V₀c lbar b + lamInf d L V₀c lbar b /
            (Fintype.card (Lam d L N) * atR d L V₀c N b) * (1 + E))) := by
  obtain ⟨L₀, H⟩ := exists_flowDataW hd
  exact ⟨L₀, fun L _ hL hLodd => by
    obtain ⟨A, ℓ₀, V₀c, lbar, C, κ, HW⟩ := H L hL hLodd
    exact ⟨A, ℓ₀, V₀c, lbar, C, κ, HW, cor_anm0_of hd HW hLodd⟩⟩

/-- `cor_conn4pt_of` with the full quantifier prefix. -/
theorem cor_conn4pt (hd : 3 ≤ d) : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → Odd L →
    ∃ (A ℓ₀ : ℝ) (V₀c : ℝ → ℂ → Vcoup) (lbar C κ : ℝ), FlowDataW d L A ℓ₀ V₀c lbar C κ ∧
    (∃ bbar Cc KΓ : ℝ, 0 < bbar ∧ bbar ≤ lbar / 2 ∧ bbar ≤ 1 ∧ 0 ≤ Cc ∧
      (∀ b, 0 < b → b ≤ bbar → hF V₀c b 0 = 0 ∧ (GamA d L V₀c lbar 0 b).im = 0 ∧
        (LamA d L V₀c lbar 0 b).im = 0 ∧ |lamInf d L V₀c lbar b - 1| ≤ 1 / 2) ∧
      ∀ N : ℕ, 2 ≤ N → ∀ b, 0 < b → b ≤ bbar → ∀ x : Lam d L N, x ≠ 0 →
        |gamInf d L V₀c lbar b| ≤ KΓ ∧
        |H02.arborealProb (nnW d L N (betaF V₀c b 0)) (nnW_symm _) (fun F => F.Reachable 0 x) -
          ((1 - c2F V₀c b 0 * gamInf d L V₀c lbar b) ^ 2 + 2 * c2F V₀c b 0 *
            lamInf d L V₀c lbar b * (1 - c2F V₀c b 0 * gamInf d L V₀c lbar b) *
              greenZd d (rep x))| ≤
          Cc * (b ^ 2 * (supNorm x : ℝ) ^ (-((d : ℝ) - 2 + min κ 1)) +
            b * (L : ℝ) ^ (-(((d : ℝ) - 2) * N)) + b ^ 2 * (L : ℝ) ^ (-(min κ 1 * N)))) := by
  obtain ⟨L₀, H⟩ := exists_flowDataW hd
  exact ⟨L₀, fun L _ hL hLodd => by
    obtain ⟨A, ℓ₀, V₀c, lbar, C, κ, HW⟩ := H L hL hLodd
    exact ⟨A, ℓ₀, V₀c, lbar, C, κ, HW, cor_conn4pt_of hd HW hLodd⟩⟩

/-- `cor_aNlimit_of` with the full quantifier prefix. -/
theorem cor_aNlimit (hd : 3 ≤ d) : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → Odd L →
    ∃ (A ℓ₀ : ℝ) (V₀c : ℝ → ℂ → Vcoup) (lbar C κ : ℝ), FlowDataW d L A ℓ₀ V₀c lbar C κ ∧
    (∃ bbar : ℝ, 0 < bbar ∧ ∀ b, 0 < b → b ≤ bbar →
      lamInf d L V₀c lbar b * (1 - c2F V₀c b 0 * gamInf d L V₀c lbar b) = 1) := by
  obtain ⟨L₀, H⟩ := exists_flowDataW hd
  exact ⟨L₀, fun L _ hL hLodd => by
    obtain ⟨A, ℓ₀, V₀c, lbar, C, κ, HW⟩ := H L hL hLodd
    exact ⟨A, ℓ₀, V₀c, lbar, C, κ, HW, cor_aNlimit_of hd HW hLodd⟩⟩

end

end Ward

end

/-!
# `thm:forest-macro`, `thm:h02`, `thm:forests0`, `thm:forests` with shared constants

`thm_all` (in `H02RG/Main/Theorems.lean`; here `thm_all_of` for a given `V₀c` with
`FlowDataW`): for `d ≥ 3`, odd `L ≥ L₀` there are a single initial coupling `V₀c`, a single `β₀`, `κ'` and constants
`ζ, c₀, θ, c₁, c₂ : ℝ → ℝ` such that for `β ≥ β₀`:

* `thm:forest-macro` (`FMBody`, final form, `𝖼₀ = 2 c_d`);
* `thm:h02` (`H02Body`);
* `thm:forests0` (`F0Body`) and `thm:forests` (`FBody`), with `P` the arboreal gas with ghost;
* the identities `θ(β)² = ζ(β)`, `c₂(β) θ(β)² / c₁(β)² = 1`, `c₀(β) = 2 c₁(β)`.

The identities: with `b* = bt β 0` (the solution of `cor:ward` (ii) at `h = 0`),
`θ = 1 - c²(b*,0) γ(b*)` (the `θ` of `cor:aNlimit` / `thm:forest-macro`, since
`γ = Re Γ(0, b*)`), `ζ = θ²` by definition, `c₀ = 2(1+s₀) c_d = 2 c₁`, and
`c₂ = (1+s₀)² λ² c_d²` (`Λ(0, b*) = λ` real, `cor_anm0_of`), so `c₂ θ²/c₁² = (λθ)² = 1`
(`cor_aNlimit_of`).
-/

namespace Ward

noncomputable section

open Finset Grassmann Loc Step Obs FRD PtCorr Psi4 Filter Topology Metric FRD.GreenAsymp

variable {d L : ℕ} [NeZero L] {A ℓ₀ lbar C κ : ℝ} {V₀c : ℝ → ℂ → Vcoup}

/-- The claims of `thm:forests0` at fixed `β`. -/
abbrev F0Body (d L : ℕ) [NeZero L] (θ : ℝ → ℝ) (β : ℝ) : Prop :=
  ∃ θh' : ℝ → ℝ, (∀ h, 0 < h → Tendsto (fun N =>
      H02.arborealProb (H02.ghostW (nnW d L N β) (fun _ => h))
        (H02.ghostW_symm (nnW_symm β) _) (fun F => F.Reachable (some (0 : Lam d L N)) none))
      atTop (𝓝 (θh' h))) ∧ Tendsto θh' (𝓝[>] 0) (𝓝 (θ β))

/-- The claims of `thm:forests` at fixed `β`. -/
abbrev FBody (d L : ℕ) [NeZero L] (κ' K : ℝ) (c₁ c₂ : ℝ → ℝ) (β : ℝ) : Prop :=
  ∀ x : Zd d, x ≠ 0 →
    (∃ (τh' : ℝ → ℝ) (τ₀ : ℝ),
      (∀ h, 0 < h → Tendsto (fun N =>
        H02.arborealProb (H02.ghostW (nnW d L N β) (fun _ => h))
          (H02.ghostW_symm (nnW_symm β) _) (fun F => (H02.base F).Reachable (0 : Lam d L N)
            (toT L N x) ∧ ¬F.Reachable (some (0 : Lam d L N)) none)) atTop (𝓝 (τh' h))) ∧
      Tendsto τh' (𝓝[>] 0) (𝓝 τ₀) ∧
      |τ₀ - c₁ β * eNorm x ^ (-((d : ℝ) - 2)) / β| ≤
        K * eNorm x ^ (-((d : ℝ) - 2 + κ')) / β) ∧
    (∃ (σh' : ℝ → ℝ) (σ₀ : ℝ),
      (∀ h, 0 < h → Tendsto (fun N =>
        H02.arborealProb (H02.ghostW (nnW d L N β) (fun _ => h))
            (H02.ghostW_symm (nnW_symm β) _)
            (fun F => ¬F.Reachable (some (0 : Lam d L N)) none) ^ 2 -
          H02.arborealProb (H02.ghostW (nnW d L N β) (fun _ => h))
            (H02.ghostW_symm (nnW_symm β) _) (fun F =>
              ¬F.Reachable (some (0 : Lam d L N)) none ∧
                ¬F.Reachable (some (toT L N x)) none ∧
                ¬F.Reachable (some (0 : Lam d L N)) (some (toT L N x)))) atTop
        (𝓝 (σh' h))) ∧
      Tendsto σh' (𝓝[>] 0) (𝓝 σ₀) ∧
      |σ₀ - c₂ β * eNorm x ^ (-(2 * ((d : ℝ) - 2))) / β ^ 2| ≤
        K * eNorm x ^ (-(2 * ((d : ℝ) - 2) + κ')) / β ^ 2)

theorem forests0_of_body {κ' K : ℝ} {θ c₁ c₂ : ℝ → ℝ} {β : ℝ} (hβ0 : 0 ≤ β)
    (Hb : H02Body d L κ' K θ c₁ c₂ β) : F0Body d L θ β := by
  obtain ⟨-, -, -, -, ⟨θh', hlim, hcont⟩, -⟩ := Hb
  refine ⟨θh', fun h hh => ?_, hcont⟩
  refine (hlim h hh).congr fun N => ?_
  exact (Pg_eq hβ0 hh.le).symm

theorem forests_of_body {κ' K : ℝ} {θ c₁ c₂ : ℝ → ℝ} {β : ℝ} (hβ0 : 0 ≤ β)
    (Hb : H02Body d L κ' K θ c₁ c₂ β) : FBody d L κ' K c₁ c₂ β := by
  obtain ⟨-, -, -, htr, -, hτ, hσ, -⟩ := Hb
  intro x hx
  refine ⟨?_, ?_⟩
  · obtain ⟨τh', τ₀, hlim, hcont, hest⟩ := hτ x hx
    refine ⟨τh', τ₀, fun h hh => (hlim h hh).congr fun N => ?_, hcont, hest⟩
    exact ((H02.prop_h02_forest (nnW_symm β) (nnW_nonneg hβ0) h hh.le 0 (toT L N x)).2.1).symm
  · obtain ⟨σh', σ₀, hlim, hcont, hest⟩ := hσ x hx
    refine ⟨fun h => -σh' h, -σ₀, fun h hh => ?_, hcont.neg, ?_⟩
    · refine (hlim h hh).neg.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with N hN
      obtain ⟨hz, -, -, -, hsig⟩ :=
        H02.prop_h02_forest (nnW_symm β) (nnW_nonneg hβ0) h hh.le (0 : Lam d L N) (toT L N x)
      obtain ⟨hzx, -⟩ :=
        H02.prop_h02_forest (nnW_symm β) (nnW_nonneg hβ0) h hh.le (toT L N x) (toT L N x)
      have hn := fun (a : Lam d L N) => H02.arborealProb_not
        (H02.ghostW_symm (nnW_symm β) (fun _ => h)) (H02.ghostW_nonneg (nnW_nonneg hβ0)
          (fun _ => hh.le)) (fun F => F.Reachable (some a) none)
      have hPx : H02.arborealProb (H02.ghostW (nnW d L N β) (fun _ => h))
            (H02.ghostW_symm (nnW_symm β) _) (fun F => ¬F.Reachable (some (toT L N x)) none) =
          H02.arborealProb (H02.ghostW (nnW d L N β) (fun _ => h))
            (H02.ghostW_symm (nnW_symm β) _)
            (fun F => ¬F.Reachable (some (0 : Lam d L N)) none) := by
        rw [hn, hn, hzx, hz, htr h hh N hN]
      rw [hsig, hPx]
      ring
    · rw [show -σ₀ - c₂ β * eNorm x ^ (-(2 * ((d : ℝ) - 2))) / β ^ 2 =
        -(σ₀ + c₂ β * eNorm x ^ (-(2 * ((d : ℝ) - 2))) / β ^ 2) by ring, abs_neg]
      exact hest

/-- The claims of all four theorems with shared constants, at fixed `β`. -/
abbrev AllBody (d L : ℕ) [NeZero L] (κ' K Cf c0 : ℝ) (ζ c₀ θ c₁ c₂ : ℝ → ℝ) (β : ℝ) : Prop :=
  FMBody d L κ' Cf c0 ζ c₀ β ∧ H02Body d L κ' K θ c₁ c₂ β ∧ F0Body d L θ β ∧
    FBody d L κ' K c₁ c₂ β ∧
    ζ β = θ β ^ 2 ∧ c₂ β * θ β ^ 2 / c₁ β ^ 2 = 1 ∧ c₀ β = 2 * c₁ β

set_option maxHeartbeats 4000000 in
/-- **`thm:forest-macro`, `thm:h02`, `thm:forests0`, `thm:forests`** for a given `V₀c` with
`FlowDataW` (`L` odd), with shared constants and the identities between them. -/
theorem thm_all_of (hd : 3 ≤ d) (HW : FlowDataW d L A ℓ₀ V₀c lbar C κ) (hLodd : Odd L) :
    ∃ (β₀ κ' K Cf c0 : ℝ) (ζ c₀ θ c₁ c₂ : ℝ → ℝ), 0 < β₀ ∧ 0 < κ' ∧ κ' ≤ 1 ∧ 0 ≤ K ∧
      0 ≤ Cf ∧ c0 = 2 * cd d ∧ 0 < c0 ∧
      ∀ β, β₀ ≤ β → AllBody d L κ' K Cf c0 ζ c₀ θ c₁ c₂ β := by
  have hl := HW.lbar_pos
  have hC := HW.C_nonneg
  have hcd := cd_pos hd
  -- one solution of `cor:ward`
  obtain ⟨bw, Kw, hbw0, hbw2, -, hK0, hKb, h48, hall, hh0, -⟩ := cor_ward_i hd HW
  obtain ⟨β₁, bt, mt, hβ₁, hsol⟩ := cor_ward_ii hd HW hbw0 hbw2 hK0 hKb h48 hall hh0
  -- `thm:h02`
  obtain ⟨βh, κh, K, hβh, hβh1, hκh, hκh0, hκh1, hK, hH⟩ :=
    thm_h02_core hd HW hLodd hbw0 hbw2 h48 hsol
  -- `thm:forest-macro`
  obtain ⟨βf, κf, Cf, hβf, hκf, -, -, hCf, hG⟩ :=
    forest_macro_G_core hd HW hLodd hbw0 hbw2 h48 hβ₁ hsol
  obtain ⟨βF, Cf2, hβF, hCf2, hF⟩ := fm_final_of_G hd (lt_of_lt_of_le hβ₁ hβf)
    (by rw [hκf]; exact lt_min HW.κ_pos one_pos) (by rw [hκf]; exact min_le_right _ _) hCf hG
  have hκeq : κf = κh := hκf.trans hκh.symm
  rw [hκeq] at hF
  -- `cor:aNlimit`, reality of `Λ`
  obtain ⟨bA, hbA, hlt⟩ := cor_aNlimit_of hd HW hLodd
  obtain ⟨ba, -, hba, -, -, -, hreal, -⟩ := cor_anm0_of hd HW hLodd
  set bm := min bA ba with hbm
  have hbm0 : 0 < bm := lt_min hbA hba
  set β₀ := max (max βh βF) (9 / (4 * bm)) with hβ₀
  refine ⟨β₀, κh, K, Cf2, 2 * cd d, ζF d L V₀c lbar bt, fun β => c0G V₀c bt β * cd d,
    θF d L V₀c lbar bt mt, c1F d V₀c bt, c2Fc d L V₀c lbar bt,
    lt_of_lt_of_le (by positivity : (0 : ℝ) < 9 / (4 * bm)) (le_max_right _ _), hκh0, hκh1, hK,
    hCf2, rfl, by positivity, fun β hβ => ?_⟩
  have hβh' : βh ≤ β := ((le_max_left _ _).trans (le_max_left _ _)).trans hβ
  have hβF' : βF ≤ β := ((le_max_right _ _).trans (le_max_left _ _)).trans hβ
  have hβm : 9 / (4 * bm) ≤ β := (le_max_right _ _).trans hβ
  have hβ1 : β₁ ≤ β := le_trans (le_trans hβf hβF) hβF'
  have hβp : 0 < β := lt_of_lt_of_le (by positivity) hβm
  have Hb := hH β hβh'
  obtain ⟨hm0, hb, hbl, hs2, -, -, -, hbe⟩ :=
    zero_facts HW hLodd hd hbw0 hbw2 h48 (hsol β hβ1)
  -- `b* ≤ bm`
  have hbβ : bt β 0 ≤ bm := by
    have h1 : bt β 0 ≤ 9 / 4 / β := by
      rw [hbe]
      refine div_le_div_of_nonneg_right ?_ hβp.le
      have := abs_le.1 hs2; nlinarith
    refine h1.trans ?_
    rw [div_le_iff₀ hβp]
    rw [div_le_iff₀ (by positivity)] at hβm
    linarith
  have hbA' : bt β 0 ≤ bA := hbβ.trans (min_le_left _ _)
  have hba' : bt β 0 ≤ ba := hbβ.trans (min_le_right _ _)
  -- `θ = 1 - c² γ`
  have hθ : θF d L V₀c lbar bt mt β =
      1 - c2F V₀c (bt β 0) 0 * gamInf d L V₀c lbar (bt β 0) := by
    show (1 - (c2F V₀c (bt β 0) (mt β 0) : ℂ) * GamA d L V₀c lbar (mt β 0) (bt β 0)).re = _
    rw [hm0, Complex.sub_re, Complex.one_re, Complex.re_ofReal_mul]
    rfl
  -- `Λ` real
  have hΛ : LamA d L V₀c lbar 0 (bt β 0) = (lamInf d L V₀c lbar (bt β 0) : ℂ) :=
    Complex.ext rfl (by rw [Complex.ofReal_im]; exact (hreal _ hb hba').2.2.1)
  have h1s : 0 < 1 + s0R V₀c (bt β 0) 0 := by linarith [(abs_le.1 hs2).1]
  have hlamθ := hlt (bt β 0) hb hbA'
  refine ⟨hF β hβF', Hb, forests0_of_body hβp.le Hb, forests_of_body hβp.le Hb, ?_, ?_, ?_⟩
  · -- `ζ = θ²`
    show (1 - c2F V₀c (bt β 0) 0 * gamInf d L V₀c lbar (bt β 0)) ^ 2 =
      θF d L V₀c lbar bt mt β ^ 2
    rw [hθ]
  · -- `c₂ θ² / c₁² = 1`
    show ((1 + s0R V₀c (bt β 0) 0 : ℂ) ^ 2 * LamA d L V₀c lbar 0 (bt β 0) ^ 2).re * cd d ^ 2 *
        θF d L V₀c lbar bt mt β ^ 2 / ((1 + s0R V₀c (bt β 0) 0) * cd d) ^ 2 = 1
    rw [hΛ, hθ, show ((1 + s0R V₀c (bt β 0) 0 : ℂ) ^ 2 *
        (lamInf d L V₀c lbar (bt β 0) : ℂ) ^ 2) =
        (((1 + s0R V₀c (bt β 0) 0) ^ 2 * lamInf d L V₀c lbar (bt β 0) ^ 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_re]
    have hne : (1 + s0R V₀c (bt β 0) 0) * cd d ≠ 0 := (mul_pos h1s hcd).ne'
    rw [div_eq_one_iff_eq (pow_ne_zero 2 hne)]
    calc (1 + s0R V₀c (bt β 0) 0) ^ 2 * lamInf d L V₀c lbar (bt β 0) ^ 2 * cd d ^ 2 *
          (1 - c2F V₀c (bt β 0) 0 * gamInf d L V₀c lbar (bt β 0)) ^ 2
        = ((1 + s0R V₀c (bt β 0) 0) * cd d) ^ 2 * (lamInf d L V₀c lbar (bt β 0) *
          (1 - c2F V₀c (bt β 0) 0 * gamInf d L V₀c lbar (bt β 0))) ^ 2 := by ring
      _ = _ := by rw [hlamθ]; ring
  · -- `c₀ = 2 c₁`
    show 2 * (1 + s0R V₀c (bt β 0) 0) * cd d = 2 * ((1 + s0R V₀c (bt β 0) 0) * cd d)
    ring

end

end Ward
