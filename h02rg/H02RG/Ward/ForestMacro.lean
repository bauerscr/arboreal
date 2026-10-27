import Ward.ANlimit
import Ward.CorWardMain
import FRD.GreenAsymp

/-!
# Theorem `thm:forest-macro`

For `d ≥ 3`, `L ≥ L₀` odd, there are `β₀, κ' ∈ (0, 1], C` and `ζ_d(β)`, `c₀(β)` with
`|ζ_d(β) - 1| ≤ C/β`, `|c₀(β) - 2| ≤ C/β` such that for `β ≥ β₀`, `N ≥ 2`, `x ∈ Λ_N ∖ {0}`:

* **G-form** (`thm_forest_macro_G`):
  `P^{Λ_N}_{β,0}[0 ↔ x] = ζ_d(β) + c₀(β) G(x)/β + O(β^{-1}|x|_∞^{-(d-2+κ')}) + O(β^{-1}L^{-κ'N})`,
  `G(x) = (-Δ_{ℤ^d})^{-1}(0, r(x))`;
* **final form** (`thm_forest_macro`, `h02rg.tex` line 231):
  `P^{Λ_N}_{β,0}[0 ↔ x] = ζ_d(β) + 𝖼₀(β)/(β|x|^{d-2}) + O(β^{-1}|x|^{-(d-2+κ')}) + O(β^{-1}L^{-κ'N})`
  with the Euclidean norm `|x| = |r(x)|` of the centred representative, `𝖼₀(β) = c₀(β) c_d`,
  `|𝖼₀(β) - 𝖼₀| ≤ C/β`, `𝖼₀ = 2 c_d > 0` (`c_d` of `FRD.GreenAsymp.cd`, eq:LapZd).

Here `ζ_d(β) = θ(b*)²`, `c₀(β) = 2(1 + s₀(b*, 0)) = 2(1 + s₀) λθ` (by `cor:aNlimit`), where
`b* = b*(β)` is the unique `b` with `β(b, 0) = β` (`cor_ward_ii`).

`forest_macro_G_core` proves the G-form for a given solution `(bt, mt)` of `cor:ward` (ii) with
the explicit `ζ = ζF`, `c₀ = c0G` (the claims at fixed `β`: `FMGBody`), and `fm_final_of_G`
passes from the G-form to the final form (`FMBody`) for any `ζ`, `c₀`.

The final theorem `thm_forest_macro` is in `H02RG/Main/Theorems.lean`; this file has
`thm_forest_macro_of` (for a given `V₀c`).

Deviations: `N ≥ 2` (the observable limits of `Ward.ObsLimit` are for `N ≥ 2`); `κ' = min(κ, 1)`.
-/

namespace Ward

noncomputable section

open Finset Grassmann Loc Step Obs FRD PtCorr Psi4 Filter Topology Metric

variable {d L : ℕ} [NeZero L] {A ℓ₀ lbar C κ : ℝ} {V₀c : ℝ → ℂ → Vcoup}

/-- The G-form claims of `thm:forest-macro` at fixed `β`. -/
abbrev FMGBody (d L : ℕ) [NeZero L] (κ' Cf : ℝ) (ζ c₀ : ℝ → ℝ) (β : ℝ) : Prop :=
  |ζ β - 1| ≤ Cf / β ∧ |c₀ β - 2| ≤ Cf / β ∧ 0 ≤ c₀ β ∧
    ∀ N : ℕ, 2 ≤ N → ∀ x : Lam d L N, x ≠ 0 →
      |H02.arborealProb (nnW d L N β) (nnW_symm _) (fun F => F.Reachable 0 x) - ζ β -
          c₀ β * greenZd d (rep x) / β| ≤
        Cf / β * (supNorm x : ℝ) ^ (-((d : ℝ) - 2 + κ')) + Cf / β * (L : ℝ) ^ (-(κ' * N))

/-- The final-form claims of `thm:forest-macro` at fixed `β`. -/
abbrev FMBody (d L : ℕ) [NeZero L] (κ' Cf c0 : ℝ) (ζ c₀ : ℝ → ℝ) (β : ℝ) : Prop :=
  |ζ β - 1| ≤ Cf / β ∧ |c₀ β - c0| ≤ Cf / β ∧
    ∀ N : ℕ, 2 ≤ N → ∀ x : Lam d L N, x ≠ 0 →
      |H02.arborealProb (nnW d L N β) (nnW_symm _) (fun F => F.Reachable 0 x) - ζ β -
          c₀ β / (β * eNorm (rep x) ^ ((d : ℝ) - 2))| ≤
        Cf / β * eNorm (rep x) ^ (-((d : ℝ) - 2 + κ')) + Cf / β * (L : ℝ) ^ (-(κ' * N))

/-- `ζ(β) = (1 - c²(b*, 0) γ(b*))²`. -/
abbrev ζF (d L : ℕ) [NeZero L] (V₀c : ℝ → ℂ → Vcoup) (lbar : ℝ) (bt : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun β => (1 - c2F V₀c (bt β 0) 0 * gamInf d L V₀c lbar (bt β 0)) ^ 2

/-- `c₀(β) = 2(1 + s₀(b*, 0))` (G-form). -/
abbrev c0G (V₀c : ℝ → ℂ → Vcoup) (bt : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun β => 2 * (1 + s0R V₀c (bt β 0) 0)

set_option maxHeartbeats 8000000 in
/-- `thm:forest-macro`, G-form, for a given solution `(bt, mt)` of `cor:ward` (ii), with the
explicit `ζ = θ(b*)²`, `c₀ = 2(1 + s₀(b*, 0))`. -/
theorem forest_macro_G_core (hd : 3 ≤ d) (HW : FlowDataW d L A ℓ₀ V₀c lbar C κ)
    (hLodd : Odd L) {bw : ℝ} (hbw0 : 0 < bw) (hbw2 : bw ≤ lbar / 2) (h48 : 48 * C * bw ≤ 1)
    {β₁ : ℝ} (hβ₁ : 0 < β₁) {bt mt : ℝ → ℝ → ℝ}
    (hsol : ∀ β, β₁ ≤ β → SolAt V₀c bw bt mt β) :
    ∃ (β₀ κ' Cf : ℝ), β₁ ≤ β₀ ∧ κ' = min κ 1 ∧ 0 < κ' ∧ κ' ≤ 1 ∧ 0 ≤ Cf ∧ ∀ β, β₀ ≤ β →
      FMGBody d L κ' Cf (ζF d L V₀c lbar bt) (c0G V₀c bt) β := by
  have HF := HW.toFlowData
  have hC := HF.C_nonneg
  have hκ := HF.κ_pos
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by have := HF.hL2; omega : 1 ≤ L)
  obtain ⟨bc, Cc, KΓ, hbc, -, hbc1, hCc, hper, hconn⟩ := cor_conn4pt_of hd HW hLodd
  obtain ⟨bA, hbA, hlt0⟩ := cor_aNlimit_of hd HW hLodd
  have hKΓ0 : 0 ≤ KΓ := by
    obtain ⟨x, hx⟩ := exists_ne_zero_lam (d := d) (L := L) (by omega) HF.hL2 (by norm_num : 1 ≤ 2)
    exact (abs_nonneg _).trans (hconn 2 le_rfl (bc / 2) (by positivity) (by linarith) x hx).1
  set b₁ := min bc (min bA bw) with hb₁
  have hb₁pos : 0 < b₁ := lt_min hbc (lt_min hbA hbw0)
  set β₀ := max (max β₁ (9 / (4 * b₁))) (9 * (KΓ + 1)) with hβ₀
  set κ' := min κ 1 with hκ'
  set Cf := 5 * Cc + 14 * (KΓ + 1) + 9 * C with hCf
  refine ⟨β₀, κ', Cf, (le_max_left _ _).trans (le_max_left _ _), hκ', lt_min hκ one_pos,
    min_le_right _ _, by positivity, fun β hβ => ?_⟩
  have hββ₁ : β₁ ≤ β := ((le_max_left _ _).trans (le_max_left _ _)).trans hβ
  have hβb : 9 / (4 * b₁) ≤ β := ((le_max_right _ _).trans (le_max_left _ _)).trans hβ
  have hβK : 9 * (KΓ + 1) ≤ β := (le_max_right _ _).trans hβ
  have hβ0 : 0 < β := lt_of_lt_of_le (by positivity) hβb
  obtain ⟨hbt0, hbtw, -, -, hbeta, -, hmt0, -⟩ := hsol β hββ₁ 0 le_rfl
  rw [hmt0] at hbeta
  set b := bt β 0 with hbdef
  -- `b ≤ 9/(4β)`
  have hs := abs_s0R_le HF hbt0.le (by linarith) le_rfl
  have hCb : 2 * C * b ≤ 1 / 2 := by nlinarith [mul_le_mul_of_nonneg_left hbtw hC]
  have hsb : -(1 / 2) ≤ s0R V₀c b 0 ∧ s0R V₀c b 0 ≤ 1 / 2 := by
    constructor <;> linarith [(abs_le.1 hs).1, (abs_le.1 hs).2]
  have hbβ : b ≤ 9 / (4 * β) := by
    have h1 : β = (1 + s0R V₀c b 0) ^ 2 / b := hbeta.symm
    have h2 : (1 + s0R V₀c b 0) ^ 2 ≤ 9 / 4 := by nlinarith [hsb.1, hsb.2]
    have h3 : β * b = (1 + s0R V₀c b 0) ^ 2 := by rw [h1]; field_simp
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hbb₁ : b ≤ b₁ := by
    refine hbβ.trans ?_
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hβb
    linarith
  have hbc' : b ≤ bc := hbb₁.trans (min_le_left _ _)
  have hbA' : b ≤ bA := hbb₁.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hb1 : b ≤ 1 := hbc'.trans hbc1
  have hbβ' : b ≤ 9 / 4 / β := by rw [div_div]; exact hbβ
  -- constants
  set c := c2F V₀c b 0 with hc
  set γ := gamInf d L V₀c lbar b
  set lam := lamInf d L V₀c lbar b
  set θ := 1 - c * γ with hθ
  have hc0 : 0 < c := c2F_pos hbt0 (by linarith [hsb.1])
  have hcb : c ≤ 2 * b := by
    rw [hc]; unfold c2F; rw [div_le_iff₀ (by linarith [hsb.1])]; nlinarith [hsb.1]
  have hcβ : c = (1 + s0R V₀c b 0) / β := by
    rw [← hbeta]; exact (c2F_eq hbt0 (by linarith [hsb.1])).symm
  have hlt := hlt0 b hbt0 hbA'
  obtain ⟨x0, hx0⟩ := exists_ne_zero_lam (d := d) (L := L) (by omega) HF.hL2 (by norm_num : 1 ≤ 2)
  have hγ : |γ| ≤ KΓ := (hconn 2 le_rfl b hbt0 hbc' x0 hx0).1
  have hbK : b * KΓ ≤ 1 / 4 := by
    have : b ≤ 9 / 4 / β := hbβ'
    have h2 : 9 / 4 / β * KΓ ≤ 1 / 4 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hβ0]; nlinarith
    nlinarith [mul_le_mul_of_nonneg_right this hKΓ0]
  have hcγ : |c * γ| ≤ 2 * b * KΓ := by
    rw [abs_mul, abs_of_pos hc0]; exact mul_le_mul hcb hγ (abs_nonneg _) (by linarith)
  have hbCf : ∀ X : ℝ, 0 ≤ X → b * X ≤ 9 / 4 / β * X := fun X hX =>
    mul_le_mul_of_nonneg_right hbβ' hX
  refine ⟨?_, ?_, ?_, fun N hN x hx => ?_⟩
  · -- `|ζ - 1| ≤ C/β`
    show |θ ^ 2 - 1| ≤ Cf / β
    have e : θ ^ 2 - 1 = (θ - 1) * (θ + 1) := by ring
    have h1 : |θ - 1| ≤ 2 * b * KΓ := by rw [hθ, sub_sub_cancel_left, abs_neg]; exact hcγ
    have h2 : |θ + 1| ≤ 3 := by
      rw [hθ]; have := abs_le.1 hcγ; rw [abs_le]; constructor <;> nlinarith
    rw [e, abs_mul]
    calc |θ - 1| * |θ + 1| ≤ 2 * b * KΓ * 3 := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = 6 * (b * KΓ) := by ring
      _ ≤ 6 * (9 / 4 / β * KΓ) := by nlinarith [hbCf KΓ hKΓ0]
      _ ≤ Cf / β := by
          rw [hCf]; field_simp
          nlinarith [hCc, hC]
  · -- `|c₀ - 2| ≤ C/β`
    show |2 * (1 + s0R V₀c b 0) - 2| ≤ Cf / β
    rw [show 2 * (1 + s0R V₀c b 0) - 2 = 2 * s0R V₀c b 0 by ring, abs_mul, abs_two]
    calc 2 * |s0R V₀c b 0| ≤ 2 * (2 * C * b) := by linarith
      _ = 4 * C * b := by ring
      _ ≤ 4 * C * (9 / 4 / β) := mul_le_mul_of_nonneg_left hbβ' (by positivity)
      _ ≤ Cf / β := by
          rw [hCf]; field_simp
          nlinarith [hCc, hKΓ0]
  · show 0 ≤ 2 * (1 + s0R V₀c b 0); linarith [hsb.1]
  -- the connection probability
  obtain ⟨-, hP⟩ := hconn N hN b hbt0 hbc' x hx
  rw [hbeta] at hP
  have e1 : 2 * c * lam * θ * greenZd d (rep x) =
      2 * (1 + s0R V₀c b 0) * greenZd d (rep x) / β := by
    rw [show 2 * c * lam * θ = 2 * c * (lam * θ) by ring, hlt, hcβ]; ring
  show |H02.arborealProb (nnW d L N β) (nnW_symm _) (fun F => F.Reachable 0 x) - θ ^ 2 -
      2 * (1 + s0R V₀c b 0) * greenZd d (rep x) / β| ≤ _
  have e2 : H02.arborealProb (nnW d L N β) (nnW_symm _) (fun F => F.Reachable 0 x) - θ ^ 2 -
      2 * (1 + s0R V₀c b 0) * greenZd d (rep x) / β =
      H02.arborealProb (nnW d L N β) (nnW_symm _) (fun F => F.Reachable 0 x) -
        (θ ^ 2 + 2 * c * lam * θ * greenZd d (rep x)) := by rw [e1]; ring
  rw [e2]
  refine hP.trans ?_
  -- errors
  have hρθ : (L : ℝ) ^ (-(((d : ℝ) - 2) * N)) ≤ (L : ℝ) ^ (-(κ' * N)) :=
    rpow_neg_mul_mono_one hL1 (by
      have : (3 : ℝ) ≤ d := by exact_mod_cast hd
      have := min_le_right κ 1; linarith) N
  have hs0 : 0 ≤ (supNorm x : ℝ) ^ (-((d : ℝ) - 2 + κ')) := by positivity
  have hθ0 : 0 ≤ (L : ℝ) ^ (-(κ' * N)) := by positivity
  have hb2 : b ^ 2 ≤ b := by nlinarith
  calc Cc * (b ^ 2 * (supNorm x : ℝ) ^ (-((d : ℝ) - 2 + κ')) +
        b * (L : ℝ) ^ (-(((d : ℝ) - 2) * N)) + b ^ 2 * (L : ℝ) ^ (-(κ' * N)))
      ≤ Cc * (b * (supNorm x : ℝ) ^ (-((d : ℝ) - 2 + κ')) + 2 * (b * (L : ℝ) ^ (-(κ' * N)))) := by
        refine mul_le_mul_of_nonneg_left ?_ hCc
        have h1 := mul_le_mul_of_nonneg_right hb2 hs0
        have h2 := mul_le_mul_of_nonneg_right hb2 hθ0
        have h3 := mul_le_mul_of_nonneg_left hρθ hbt0.le
        linarith
    _ ≤ Cc * (9 / 4 / β * (supNorm x : ℝ) ^ (-((d : ℝ) - 2 + κ')) +
          2 * (9 / 4 / β * (L : ℝ) ^ (-(κ' * N)))) := by
        gcongr
    _ ≤ Cf / β * (supNorm x : ℝ) ^ (-((d : ℝ) - 2 + κ')) + Cf / β * (L : ℝ) ^ (-(κ' * N)) := by
        have h1 : Cc * (9 / 4) ≤ Cf := by rw [hCf]; nlinarith [hKΓ0, hC]
        have h2 : Cc * (9 / 2) ≤ Cf := by rw [hCf]; nlinarith [hKΓ0, hC]
        have e : Cc * (9 / 4 / β * (supNorm x : ℝ) ^ (-((d : ℝ) - 2 + κ')) +
            2 * (9 / 4 / β * (L : ℝ) ^ (-(κ' * N)))) =
            Cc * (9 / 4) / β * (supNorm x : ℝ) ^ (-((d : ℝ) - 2 + κ')) +
              Cc * (9 / 2) / β * (L : ℝ) ^ (-(κ' * N)) := by ring
        rw [e]
        gcongr

/-- **`thm:forest-macro`, G-form**, for a given `V₀c` with `FlowDataW` (`L` odd). -/
theorem thm_forest_macro_G_of (hd : 3 ≤ d) (HW : FlowDataW d L A ℓ₀ V₀c lbar C κ)
    (hLodd : Odd L) :
    ∃ (β₀ κ' Cf : ℝ) (ζ c₀ : ℝ → ℝ), 0 < β₀ ∧ 0 < κ' ∧ κ' ≤ 1 ∧ 0 ≤ Cf ∧ ∀ β, β₀ ≤ β →
      |ζ β - 1| ≤ Cf / β ∧ |c₀ β - 2| ≤ Cf / β ∧ 0 ≤ c₀ β ∧
      ∀ N : ℕ, 2 ≤ N → ∀ x : Lam d L N, x ≠ 0 →
        |H02.arborealProb (nnW d L N β) (nnW_symm _) (fun F => F.Reachable 0 x) - ζ β -
            c₀ β * greenZd d (rep x) / β| ≤
          Cf / β * (supNorm x : ℝ) ^ (-((d : ℝ) - 2 + κ')) + Cf / β * (L : ℝ) ^ (-(κ' * N)) := by
  obtain ⟨bw, K, hbw0, hbw2, -, hK0, hKb, h48, hall, hh0, -⟩ := cor_ward_i hd HW
  obtain ⟨β₁, bt, mt, hβ₁, hsol⟩ := cor_ward_ii hd HW hbw0 hbw2 hK0 hKb h48 hall hh0
  obtain ⟨β₀, κ', Cf, hβ₁₀, -, hκ', hκ'1, hCf, hmain⟩ :=
    forest_macro_G_core hd HW hLodd hbw0 hbw2 h48 hβ₁ hsol
  exact ⟨β₀, κ', Cf, ζF d L V₀c lbar bt, c0G V₀c bt, lt_of_lt_of_le hβ₁ hβ₁₀, hκ', hκ'1, hCf,
    hmain⟩

theorem supNorm_rpow_le_eNorm (hd : 1 ≤ d) {n : ℕ} [NeZero n] {x : Torus d n} (hx : x ≠ 0) {a : ℝ}
    (ha : 0 ≤ a) (had : a ≤ d) :
    (supNorm x : ℝ) ^ (-a) ≤ Real.sqrt d ^ (d : ℝ) * eNorm (rep x) ^ (-a) := by
  have hrep : rep x ≠ 0 := fun h => hx (by
    rw [← prj_rep x, h]
    show (fun i => (((0 : Zd d) i : ℤ) : ZMod n)) = (0 : Fin d → ZMod n)
    funext i; simp)
  have hs1 : (1 : ℝ) ≤ supNorm x := by
    have : supNorm x ≠ 0 := fun h => hx ((supNorm_eq_zero_iff x).1 h)
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  have hsd : (1 : ℝ) ≤ Real.sqrt d := by
    rw [Real.one_le_sqrt]; exact_mod_cast hd
  have he := eNorm_le_supNormZ (rep x)
  rw [supNormZ_rep_eq_supNorm] at he
  have he0 : 0 < eNorm (rep x) := by
    have := supNormZ_le_eNorm (rep x)
    rw [supNormZ_rep_eq_supNorm] at this; linarith
  have h1 : eNorm (rep x) / Real.sqrt d ≤ supNorm x := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have h2 : (supNorm x : ℝ) ^ (-a) ≤ (eNorm (rep x) / Real.sqrt d) ^ (-a) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by linarith)
  refine h2.trans ?_
  rw [Real.div_rpow he0.le (by linarith), Real.rpow_neg (by linarith : (0 : ℝ) ≤ Real.sqrt d),
    div_inv_eq_mul, mul_comm]
  gcongr

set_option maxHeartbeats 8000000 in
/-- The final form of `thm:forest-macro` from the G-form, for any `ζ`, `c₀`: with
`𝖼₀(β) = c₀(β) c_d` and `𝖼₀ = 2 c_d`. -/
theorem fm_final_of_G (hd : 3 ≤ d) {β₀ κ' Cf : ℝ} {ζ c₀ : ℝ → ℝ} (hβ₀ : 0 < β₀)
    (hκ' : 0 < κ') (hκ'1 : κ' ≤ 1) (hCf : 0 ≤ Cf)
    (hmain : ∀ β, β₀ ≤ β → FMGBody d L κ' Cf ζ c₀ β) :
    ∃ (β₂ Cf2 : ℝ), β₀ ≤ β₂ ∧ 0 ≤ Cf2 ∧ ∀ β, β₂ ≤ β →
      FMBody d L κ' Cf2 (2 * FRD.GreenAsymp.cd d) ζ (fun β => c₀ β * FRD.GreenAsymp.cd d) β := by
  obtain ⟨Cga, hCga, hga⟩ := FRD.GreenAsymp.greenZd_asymp_kappa hd hκ'1
  have hcd := FRD.GreenAsymp.cd_pos hd
  have hd1 : 1 ≤ d := by omega
  set sd := Real.sqrt d ^ (d : ℝ) with hsd
  have hsd1 : 1 ≤ sd := Real.one_le_rpow (by rw [Real.one_le_sqrt]; exact_mod_cast hd1)
    (Nat.cast_nonneg _)
  set Cf2 := Cf * sd + 3 * Cga + Cf + Cf * FRD.GreenAsymp.cd d with hCf2
  refine ⟨max β₀ (Cf + 1), Cf2, le_max_left _ _, by positivity, fun β hβ => ?_⟩
  have hβ1 : β₀ ≤ β := (le_max_left _ _).trans hβ
  have hβ2 : Cf + 1 ≤ β := (le_max_right _ _).trans hβ
  have hβ0 : 0 < β := lt_of_lt_of_le hβ₀ hβ1
  obtain ⟨hζ, hc₀, hc₀0, hP⟩ := hmain β hβ1
  have hCfβ : Cf / β ≤ 1 := by rw [div_le_one hβ0]; linarith
  refine ⟨hζ.trans (div_le_div_of_nonneg_right (by nlinarith [hCga, hcd.le]) hβ0.le), ?_,
    fun N hN x hx => ?_⟩
  · rw [← sub_mul, abs_mul, abs_of_pos hcd]
    calc |c₀ β - 2| * FRD.GreenAsymp.cd d ≤ Cf / β * FRD.GreenAsymp.cd d := by gcongr
      _ = Cf * FRD.GreenAsymp.cd d / β := by ring
      _ ≤ Cf2 / β := by gcongr; rw [hCf2]; nlinarith [hCga]
  have hrep : rep x ≠ 0 := fun h => hx (by rw [← prj_rep x, h]; exact Loc.prj_zero)
  have he0 : 0 < eNorm (rep x) := by
    have := supNormZ_le_eNorm (rep x)
    rw [supNormZ_rep_eq_supNorm] at this
    have hs1 : (1 : ℝ) ≤ supNorm x := by
      have : supNorm x ≠ 0 := fun h => hx ((supNorm_eq_zero_iff x).1 h)
      exact_mod_cast Nat.one_le_iff_ne_zero.2 this
    linarith
  have hG := hga (rep x) hrep
  have hsN := supNorm_rpow_le_eNorm hd1 hx (a := (d : ℝ) - 2 + κ')
    (by have : (3 : ℝ) ≤ d := (by exact_mod_cast hd); linarith) (by linarith)
  have hP' := hP N hN x hx
  have hc₀3 : c₀ β ≤ 3 := by linarith [(abs_le.1 hc₀).2]
  have e1 : c₀ β * FRD.GreenAsymp.cd d / (β * eNorm (rep x) ^ ((d : ℝ) - 2)) =
      c₀ β * (FRD.GreenAsymp.cd d * eNorm (rep x) ^ (2 - (d : ℝ))) / β := by
    rw [show (2 : ℝ) - d = -((d : ℝ) - 2) by ring, Real.rpow_neg he0.le]
    field_simp
  rw [e1]
  have e2 : H02.arborealProb (nnW d L N β) (nnW_symm _) (fun F => F.Reachable 0 x) - ζ β -
      c₀ β * (FRD.GreenAsymp.cd d * eNorm (rep x) ^ (2 - (d : ℝ))) / β =
      (H02.arborealProb (nnW d L N β) (nnW_symm _) (fun F => F.Reachable 0 x) - ζ β -
        c₀ β * greenZd d (rep x) / β) +
      c₀ β / β * (greenZd d (rep x) - FRD.GreenAsymp.cd d * eNorm (rep x) ^ (2 - (d : ℝ))) := by
    ring
  rw [e2]
  refine (abs_add_le _ _).trans ?_
  have hx2 : eNorm (rep x) ^ (2 - (d : ℝ) - κ') = eNorm (rep x) ^ (-((d : ℝ) - 2 + κ')) := by
    congr 1; ring
  have h3 : |c₀ β / β * (greenZd d (rep x) - FRD.GreenAsymp.cd d * eNorm (rep x) ^ (2 - (d : ℝ)))|
      ≤ 3 * Cga / β * eNorm (rep x) ^ (-((d : ℝ) - 2 + κ')) := by
    rw [abs_mul, abs_div, abs_of_nonneg hc₀0, abs_of_pos hβ0, ← hx2]
    calc c₀ β / β * |greenZd d (rep x) - FRD.GreenAsymp.cd d * eNorm (rep x) ^ (2 - (d : ℝ))|
        ≤ 3 / β * (Cga * eNorm (rep x) ^ (2 - (d : ℝ) - κ')) := by
          gcongr
      _ = 3 * Cga / β * eNorm (rep x) ^ (2 - (d : ℝ) - κ') := by ring
  have h4 : Cf / β * (supNorm x : ℝ) ^ (-((d : ℝ) - 2 + κ')) ≤
      Cf * sd / β * eNorm (rep x) ^ (-((d : ℝ) - 2 + κ')) := by
    calc Cf / β * (supNorm x : ℝ) ^ (-((d : ℝ) - 2 + κ')) ≤
          Cf / β * (sd * eNorm (rep x) ^ (-((d : ℝ) - 2 + κ'))) := by gcongr
      _ = Cf * sd / β * eNorm (rep x) ^ (-((d : ℝ) - 2 + κ')) := by ring
  have hpos1 : 0 ≤ eNorm (rep x) ^ (-((d : ℝ) - 2 + κ')) := by positivity
  have hpos2 : 0 ≤ (L : ℝ) ^ (-(κ' * N)) := by positivity
  have h5 : Cf * sd / β + 3 * Cga / β ≤ Cf2 / β := by
    rw [← add_div]; gcongr; rw [hCf2]; nlinarith [hcd.le]
  have h6 : Cf / β ≤ Cf2 / β := by gcongr; rw [hCf2]; nlinarith [hcd.le, hCga]
  nlinarith [mul_le_mul_of_nonneg_right h5 hpos1, mul_le_mul_of_nonneg_right h6 hpos2]

/-- **`thm:forest-macro`** (final form, `h02rg.tex` line 231) for a given `V₀c` with
`FlowDataW` (`L` odd): the Euclidean norm `|x| = |r(x)|`, `𝖼₀(β) = c₀(β) c_d → 𝖼₀ = 2 c_d > 0`. -/
theorem thm_forest_macro_of (hd : 3 ≤ d) (HW : FlowDataW d L A ℓ₀ V₀c lbar C κ)
    (hLodd : Odd L) :
    ∃ (β₀ κ' Cf c0 : ℝ) (ζ c₀ : ℝ → ℝ), 0 < β₀ ∧ 0 < κ' ∧ κ' ≤ 1 ∧ 0 ≤ Cf ∧ 0 < c0 ∧
      ∀ β, β₀ ≤ β → |ζ β - 1| ≤ Cf / β ∧ |c₀ β - c0| ≤ Cf / β ∧
      ∀ N : ℕ, 2 ≤ N → ∀ x : Lam d L N, x ≠ 0 →
        |H02.arborealProb (nnW d L N β) (nnW_symm _) (fun F => F.Reachable 0 x) - ζ β -
            c₀ β / (β * eNorm (rep x) ^ ((d : ℝ) - 2))| ≤
          Cf / β * eNorm (rep x) ^ (-((d : ℝ) - 2 + κ')) + Cf / β * (L : ℝ) ^ (-(κ' * N)) := by
  obtain ⟨β₀, κ', Cf, ζ, c₀, hβ₀, hκ', hκ'1, hCf, hmain⟩ := thm_forest_macro_G_of hd HW hLodd
  obtain ⟨β₂, Cf2, hβ₀₂, hCf2, h⟩ := fm_final_of_G (L := L) hd hβ₀ hκ' hκ'1 hCf hmain
  have hcd := FRD.GreenAsymp.cd_pos hd
  exact ⟨β₂, κ', Cf2, 2 * FRD.GreenAsymp.cd d, ζ, fun β => c₀ β * FRD.GreenAsymp.cd d,
    lt_of_lt_of_le hβ₀ hβ₀₂, hκ', hκ'1, hCf2, by positivity, h⟩

end

end Ward
