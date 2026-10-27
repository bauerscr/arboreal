import Spin2.Multiscale.Multiscale

/-!
# `thm:rginput` at `h ≥ 0` and the limit `h ↓ 0`

The admissible trajectory `(b, μ₀ = μ₀^c(b))` at mass `m² > 0` carries the model with
`h = (μ₀ + m²)/b - 1` (`hPar`), in general `h ≠ 0`. This file separates the `h = 0` question
from the renormalisation-group analysis.

**Model level (no renormalisation group).**
* `ghostTwo L N β h x = P_{β,h}[0 ↔ x, 0 ↮ g]` (ghost arboreal gas, ghost weight `h`).
* `tendsto_ghostTwo`: `P_{β,h}[0 ↔ x, 0 ↮ g] → P_β[0 ↔ x]` as `h → 0` (finite sums of
  polynomials in `h`, `Z_{β,0} > 0`; `tendsto_arborealProb_ghost`).
* `avg0_two_eq_ghost`: `b⟨ψ̄_0ψ_x⟩ = P_{1/b,h}[0 ↔ x, 0 ↮ g]` for `h = hPar b μ₀ m² ≥ 0`.
* **`ward_r_bounds`** (Ward identity + positivity): with `r = 1 - b⟨ψ̄_0ψ_0⟩ = P_{β,h}[0 ↔ g]`,
  `r = h ∑_x P_{β,h}[0 ↔ x, 0 ↮ g]`, hence `h(1 - r) ≤ r ≤ h|Λ|`. At fixed `N`: `h → 0` iff
  `r → 0`. The Ward identity alone does not force `h → 0` as `m² ↓ 0`.

**Pure.** `multi_coreE`, `multi_shiftE`: `multi_core`, `multi_shift` with an additive error `δ`.

**Along the flow.**
* `MultiConclE`, `multiConclE_of`: `MultiConcl` for an arbitrary real target `P(x)` with
  `‖P(x) - M_{j_x}²‖ ≤ K_P‖M_{j_x}‖²ǧ_{j_x} + δ`; conclusion with `+ δ`.
* `TwoPtSq` (the named two-point input at `h ≥ 0`, the `d = 2` perfect square with the
  one-point deficit): `‖b⟨ψ̄_0ψ_x⟩ - M_{j_x}²‖ ≤ K_P‖M_{j_x}‖²ǧ_{j_x} + K_r‖1 - b⟨ψ̄_0ψ_0⟩‖`.
* `rgInput_of_twoPtSq_h0`: at `h = 0` (`b = μ₀ + m²`) `TwoPtSq` is `RGInput`.
* `MultiConclH`: `thm:multiscale` for `P_{1/b,h}[0 ↔ x, 0 ↮ g]` on the trajectory, error `+ K_r r`.
* `MultiConclH0`, `multiConclH0_of`: if, at fixed `b`, admissible data `(m_n², μ_n)` with
  `h_n ≥ 0`, (H_λ) and `TwoPtSq` (uniform constants) exist with `h_n → 0`, then for every
  `δ > 0` some `n` gives `|P_{1/b}[0 ↔ x] - ϑ_j(m_n²)²| ≤ K ϑ_j(m_n²)²/β_j(m_n²) + δ`.
* `contOn_hPar`: `h = (μ₀^c(b) + m²)/b - 1` is continuous on `UfixM` (`m² > 0`); the limit
  `m² ↓ 0` is not covered by `MsqConcl`.
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

/-! ## Model level -/

section Model

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

theorem continuous_forestWeight_ghost {w : Λ → Λ → ℝ} (hw : ∀ i j, w i j = w j i)
    (F : SimpleGraph (Option Λ)) :
    Continuous fun h : ℝ =>
      H02.forestWeight (H02.ghostW w (fun _ => h)) (H02.ghostW_symm hw _) F := by
  unfold H02.forestWeight
  refine continuous_finsetProd _ fun e _ => ?_
  induction e using Sym2.ind with
  | h i j =>
    simp only [Sym2.lift_mk]
    rcases i with _ | i <;> rcases j with _ | j <;>
      simp [continuous_const, continuous_id']

/-- The ghost arboreal-gas probabilities are continuous in the ghost weight at `h = 0`. -/
theorem tendsto_arborealProb_ghost {w : Λ → Λ → ℝ} (hw : ∀ i j, w i j = w j i)
    (hw0 : ∀ i j, 0 ≤ w i j) (P : SimpleGraph (Option Λ) → Prop) :
    Tendsto (fun h : ℝ => H02.arborealProb (H02.ghostW w (fun _ => h)) (H02.ghostW_symm hw _) P)
      (𝓝 0)
      (𝓝 (H02.arborealProb (H02.ghostW w (fun _ => (0 : ℝ))) (H02.ghostW_symm hw _) P)) := by
  have hZ0 : H02.Zforest (H02.ghostW w (fun _ => (0 : ℝ))) (H02.ghostW_symm hw _) ≠ 0 :=
    (H02.Zforest_pos _ (H02.ghostW_nonneg hw0 fun _ => le_rfl)).ne'
  unfold H02.arborealProb
  unfold H02.Zforest at hZ0 ⊢
  exact ((continuous_finsetSum _ fun F _ => continuous_forestWeight_ghost hw F).tendsto 0).div
    ((continuous_finsetSum _ fun F _ => continuous_forestWeight_ghost hw F).tendsto 0) hZ0

end Model

variable {L N : ℕ} [NeZero L]

/-- `h = (μ₀ + m²)/b - 1`, the external field of the model on the trajectory from `(b, μ₀)`. -/
def hPar (b μ₀ msq : ℝ) : ℝ := (μ₀ + msq) / b - 1

variable (L N) in
/-- **`P_{β,h}[0 ↔ x, 0 ↮ g]`** (ghost weight `h` on every vertex). -/
def ghostTwo (β h : ℝ) (x : Lam 2 L N) : ℝ :=
  H02.arborealProb (H02.ghostW (Ward.nnW 2 L N β) (fun _ => h))
    (H02.ghostW_symm (Ward.nnW_symm β) _)
    (fun F => (H02.base F).Reachable 0 x ∧ ¬F.Reachable (some 0) none)

theorem ghostTwo_mem {β h : ℝ} (hβ : 0 ≤ β) (hh : 0 ≤ h) (x : Lam 2 L N) :
    0 ≤ ghostTwo L N β h x ∧ ghostTwo L N β h x ≤ 1 :=
  ⟨H02.arborealProb_nonneg _ (H02.ghostW_nonneg (Ward.nnW_nonneg hβ) fun _ => hh) _,
    H02.arborealProb_le_one _ (H02.ghostW_nonneg (Ward.nnW_nonneg hβ) fun _ => hh) _⟩

/-- At `h = 0`: `P_{β,0}[0 ↔ x, 0 ↮ g] = P_β[0 ↔ x]`. -/
theorem ghostTwo_zero {β : ℝ} (hβ : 0 ≤ β) (x : Lam 2 L N) :
    ghostTwo L N β 0 x = Pconn L N β x := by
  rw [ghostTwo, H02.arborealProb_ghost_xieta (Ward.nnW_symm β) (Ward.nnW_nonneg hβ)
    (fun _ => le_rfl) 0 x, Pconn_eq_avg hβ]
  rfl

/-- **`h ↓ 0`**: `P_{β,h}[0 ↔ x, 0 ↮ g] → P_β[0 ↔ x]`. -/
theorem tendsto_ghostTwo {β : ℝ} (hβ : 0 ≤ β) (x : Lam 2 L N) :
    Tendsto (fun h => ghostTwo L N β h x) (𝓝 0) (𝓝 (Pconn L N β x)) := by
  rw [← ghostTwo_zero hβ x]
  exact tendsto_arborealProb_ghost (Ward.nnW_symm β) (Ward.nnW_nonneg hβ) _

theorem hPar_nonneg {b μ₀ msq : ℝ} (hb : 0 < b) (hh : b ≤ μ₀ + msq) : 0 ≤ hPar b μ₀ msq :=
  PtCorr2.onept_h_nonneg hb hh

/-- `b⟨ψ̄_0ψ_x⟩ = P_{1/b,h}[0 ↔ x, 0 ↮ g]`, `h = hPar b μ₀ m² ≥ 0`. -/
theorem avg0_two_eq_ghost {b μ₀ msq : ℝ} (hb : 0 < b) (hm0 : 0 < msq) (hh : b ≤ μ₀ + msq)
    (x : Lam 2 L N) :
    (b : ℂ) * PtCorr2.avg0 L N msq b μ₀ (psibar 0 * psi x) =
      ((ghostTwo L N (1 / b) (hPar b μ₀ msq) x : ℝ) : ℂ) := by
  have hV := PtCorr2.Vh_eq_V0 (μ₀ := μ₀) (msq := msq) hb
  rw [ghostTwo, H02.arborealProb_ghost_xieta (Ward.nnW_symm _) (Ward.nnW_nonneg (by positivity))
    (fun _ => hPar_nonneg hb hh) 0 x, hPar]
  simp only [PtCorr2.avg0, PtCorr2.V0c]
  rw [← hV, Ward.bridge_avg_ξη (s₀ := 0) (by positivity) (by norm_num) hm0,
    PtCorr2.onept_b_eq b]

/-- **The Ward identity as a constraint on `h`**: with `r = 1 - b⟨ψ̄_0ψ_0⟩ = P_{β,h}[0 ↔ g]`,
`r = h ∑_x P_{β,h}[0 ↔ x, 0 ↮ g]`, so `h(1 - r) ≤ r ≤ h|Λ|`. -/
theorem ward_r_bounds {b μ₀ msq : ℝ} (hb : 0 < b) (hm0 : 0 < msq) (hh : b ≤ μ₀ + msq) :
    ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧
      1 - (b : ℂ) * PtCorr2.avg0 L N msq b μ₀ (psibar 0 * psi 0) = r ∧
      r = hPar b μ₀ msq * ∑ x : Lam 2 L N, ghostTwo L N (1 / b) (hPar b μ₀ msq) x ∧
      hPar b μ₀ msq * (1 - r) ≤ r ∧ r ≤ hPar b μ₀ msq * Fintype.card (Lam 2 L N) := by
  set h := hPar b μ₀ msq with hhd
  set p := fun x : Lam 2 L N => ghostTwo L N (1 / b) h x with hpd
  have hh0 : 0 ≤ h := hPar_nonneg hb hh
  have hp := fun x => ghostTwo_mem (L := L) (N := N) (β := 1 / b) (by positivity) hh0 x
  have hw := PtCorr2.ward_V0 (L := L) (N := N) hb hm0 (PtCorr2.onept_Zb_ne hb hm0 hh)
  have e : μ₀ + msq - b = h * b := by rw [hhd, hPar]; field_simp
  have hsum : ((μ₀ + msq - b : ℝ) : ℂ) *
      ∑ x : Lam 2 L N, PtCorr2.avg0 L N msq b μ₀ (psibar 0 * psi x) =
      ((h * ∑ x : Lam 2 L N, p x : ℝ) : ℂ) := by
    rw [e]
    push_cast
    rw [mul_assoc, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [avg0_two_eq_ghost hb hm0 hh x]
  set r := h * ∑ x : Lam 2 L N, p x with hrd
  have hr : 1 - (b : ℂ) * PtCorr2.avg0 L N msq b μ₀ (psibar 0 * psi 0) = r := hw.trans hsum
  have hp0 : p 0 = 1 - r := by
    have h1 := avg0_two_eq_ghost (L := L) (N := N) hb hm0 hh 0
    have h2 : ((p 0 : ℝ) : ℂ) = ((1 - r : ℝ) : ℂ) := by
      rw [hpd]; push_cast; rw [← hr, ← h1]; ring
    exact_mod_cast h2
  have hS0 : p 0 ≤ ∑ x : Lam 2 L N, p x :=
    Finset.single_le_sum (f := p) (fun x _ => (hp x).1) (mem_univ 0)
  have hS1 : ∑ x : Lam 2 L N, p x ≤ Fintype.card (Lam 2 L N) := by
    calc ∑ x : Lam 2 L N, p x ≤ ∑ _x : Lam 2 L N, (1 : ℝ) :=
          Finset.sum_le_sum fun x _ => (hp x).2
      _ = Fintype.card (Lam 2 L N) := by simp
  have hr0 : 0 ≤ r := mul_nonneg hh0 (Finset.sum_nonneg fun x _ => (hp x).1)
  refine ⟨r, hr0, by linarith [(hp 0).1], hr, rfl, ?_, mul_le_mul_of_nonneg_left hS1 hh0⟩
  rw [← hp0]
  exact mul_le_mul_of_nonneg_left hS0 hh0

/-! ## Pure estimates with an additive error -/

/-- `multi_core` with an additive error `δ`. -/
theorem multi_coreE {M : ℂ} {P w g KM KP δ : ℝ} (hw : 0 < w) (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (hKM : 0 ≤ KM) (hKP : 0 ≤ KP) (hM : ‖M - (w : ℂ)‖ ≤ KM * w * g)
    (hP : ‖(P : ℂ) - M ^ 2‖ ≤ KP * ‖M‖ ^ 2 * g + δ) :
    |P - w ^ 2| ≤ (KP * (1 + KM) ^ 2 + KM * (2 + KM)) * w ^ 2 * g + δ := by
  have hwn : ‖(w : ℂ)‖ = w := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw]
  have hMn : ‖M‖ ≤ w * (1 + KM) := by
    have h1 := norm_le_norm_add_norm_sub' M (w : ℂ)
    rw [hwn] at h1
    have h2 : KM * w * g ≤ KM * w := by
      have := mul_le_mul_of_nonneg_left hg1 (mul_nonneg hKM hw.le); linarith
    linarith
  have hMp : ‖M + w‖ ≤ w * (2 + KM) := by
    have e : M + w = (M - w) + 2 * (w : ℂ) := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, hwn, Complex.norm_two]
    have h2 : KM * w * g ≤ KM * w := by
      have := mul_le_mul_of_nonneg_left hg1 (mul_nonneg hKM hw.le); linarith
    linarith
  have hsq : ‖M ^ 2 - (w : ℂ) ^ 2‖ ≤ KM * w * g * (w * (2 + KM)) := by
    rw [show M ^ 2 - (w : ℂ) ^ 2 = (M - w) * (M + w) by ring, norm_mul]
    exact mul_le_mul hM hMp (norm_nonneg _) (by positivity)
  have hM2 : ‖M‖ ^ 2 ≤ (w * (1 + KM)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hMn 2
  have hPn : |P - w ^ 2| = ‖(P : ℂ) - M ^ 2 + (M ^ 2 - (w : ℂ) ^ 2)‖ := by
    rw [show (P : ℂ) - M ^ 2 + (M ^ 2 - (w : ℂ) ^ 2) = ((P - w ^ 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
  rw [hPn]
  refine (norm_add_le _ _).trans ?_
  have h1 : KP * ‖M‖ ^ 2 * g ≤ KP * (w * (1 + KM)) ^ 2 * g :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM2 hKP) hg0
  have e2 : (KP * (1 + KM) ^ 2 + KM * (2 + KM)) * w ^ 2 * g =
      KP * (w * (1 + KM)) ^ 2 * g + KM * w * g * (w * (2 + KM)) := by ring
  rw [e2]
  linarith

/-- `multi_shift` with an additive error `δ`. -/
theorem multi_shiftE {P w w' g g' K1 c δ : ℝ} (hw : 0 < w) (hw' : 0 < w') (hg : 0 < g)
    (hg' : 0 < g') (hg1 : g ≤ 1) (hg'1 : g' ≤ 1) (hc : 0 ≤ c) (hK1 : 0 ≤ K1)
    (hb : w ^ 3 * g = w' ^ 3 * g') (hgap : |1 / g - 1 / g'| ≤ c)
    (h : |P - w ^ 2| ≤ K1 * w ^ 2 * g + δ) :
    |P - w' ^ 2| ≤ (K1 * (2 + c) + c * (3 + c)) * w' ^ 2 * g' + δ := by
  -- the `δ = 0` estimate for the target `w²`, and the comparison `K1 w²g ≤ K1(2+c)w'²g'`
  have h0 := multi_shift (P := w ^ 2) hw hw' hg hg' hg1 hg'1 hc (le_refl (0 : ℝ)) hb hgap
    (by rw [sub_self, abs_zero]; positivity)
  have h1 := multi_shift (P := w ^ 2 + w ^ 2 * g) hw hw' hg hg' hg1 hg'1 hc zero_le_one hb hgap
    (by rw [add_sub_cancel_left, one_mul, abs_of_nonneg (by positivity)])
  -- `w²g = (w/w')²(g/g') w'²g'` with `(w/w')³ = g'/g`: bound directly
  have hA : w ^ 2 * g ≤ (2 + c) * (w' ^ 2 * g') := by
    set u := w' / w with hud
    have hu0 : 0 < u := div_pos hw' hw
    have hwu : w' = u * w := by rw [hud, div_mul_cancel₀ _ hw.ne']
    have hu3 : u ^ 3 * g' = g := by
      have := hb; rw [hwu] at this
      have h3 : w ^ 3 ≠ 0 := by positivity
      exact mul_left_cancel₀ h3 (by linear_combination -this)
    have hgg : |g' - g| ≤ c * g * g' := by
      have e : g' - g = g * g' * (1 / g - 1 / g') := by field_simp
      rw [e, abs_mul, abs_of_pos (mul_pos hg hg')]
      calc g * g' * |1 / g - 1 / g'| ≤ g * g' * c :=
            mul_le_mul_of_nonneg_left hgap (by positivity)
        _ = c * g * g' := by ring
    have hu31 : u ^ 3 ≤ 1 + c := by
      have e : u ^ 3 - 1 = (g - g') / g' := by field_simp; linarith
      have : |u ^ 3 - 1| ≤ c * g := by
        rw [e, abs_div, abs_of_pos hg', div_le_iff₀ hg', abs_sub_comm]; linarith
      have hcg : c * g ≤ c := mul_le_of_le_one_right hc hg1
      linarith [le_abs_self (u ^ 3 - 1)]
    have hu2 : u ≤ 2 + c := (le_one_add_cube hu0.le).trans (by linarith)
    have e : w ^ 2 * g = u * (w' ^ 2 * g') := by rw [hwu, ← hu3]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hu2 (by positivity)
  have hB : |w ^ 2 - w' ^ 2| ≤ c * (3 + c) * w' ^ 2 * g' := by
    have := h0; rw [zero_mul, zero_add] at this; exact this
  calc |P - w' ^ 2| ≤ |P - w ^ 2| + |w ^ 2 - w' ^ 2| := abs_sub_le _ _ _
    _ ≤ K1 * w ^ 2 * g + δ + c * (3 + c) * w' ^ 2 * g' := add_le_add h hB
    _ ≤ K1 * ((2 + c) * (w' ^ 2 * g')) + δ + c * (3 + c) * w' ^ 2 * g' := by
        rw [mul_assoc K1]; gcongr
    _ = (K1 * (2 + c) + c * (3 + c)) * w' ^ 2 * g' + δ := by ring

/-! ## Along the flow -/

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- **The two-point input at `h ≥ 0`** (the `d = 2` perfect square with the one-point deficit
`r = 1 - b⟨ψ̄_0ψ_0⟩`): for `x ≠ 0` with `j_x ≤ N_h`,
`‖b⟨ψ̄_0ψ_x⟩ - M_{j_x}²‖ ≤ K_P‖M_{j_x}‖²ǧ_{j_x} + K_r‖r‖`. At `h = 0`, `r = 0` and this is
`RGInput` (`rgInput_of_twoPtSq_h0`). The `d ≥ 3` square (`lem:square` without its `h = 0`
input) gives the exact correction `2r(1 - M)` (`square_r`). -/
def TwoPtSq (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (KP Kr : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ‖(b : ℂ) * PtCorr2.avg0 L N m b μ₀ (psibar 0 * psi x) -
        Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x) ^ 2‖ ≤
      KP * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ ^ 2 *
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 +
        Kr * ‖1 - (b : ℂ) * PtCorr2.avg0 L N m b μ₀ (psibar 0 * psi 0)‖

/-- At `h = 0` (`b = μ₀ + m²`), `TwoPtSq` is `RGInput`. -/
theorem rgInput_of_twoPtSq_h0 {Nh : ℕ} {m b μ₀ : ℝ} {lam : ℕ → ℂ} {KP Kr : ℝ} (hb : 0 < b)
    (hm0 : 0 < m) (hh : b = μ₀ + m) (h : TwoPtSq R Nh m b μ₀ lam KP Kr) :
    RGInput R Nh m b μ₀ lam KP := by
  intro x hx hj
  have h1 := h x hx hj
  have hb' : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hb.ne'
  rw [PtCorr2.onept_avg0_h0 hb hm0 hh, mul_one_div_cancel hb', sub_self, norm_zero, mul_zero,
    add_zero, ← Pconn_eq_avg0 hb hm0 hh x] at h1
  exact h1

end Traj

/-- The `d ≥ 3` perfect square without the `h = 0` input: if `κ(γ + λτ) = 1 - r` (the Ward
identity `κ⟨ψ̄_0ψ_0⟩ = 1 - r`), then
`1 - κ²(γ² - λ²W² + 2λτ(γ - λW)) = (1 - κ(γ - λW))² + 2rκ(γ - λW)`, i.e. `P = M² + 2r(1 - M)`. -/
theorem square_r {κ γ lam W τ r : ℂ} (hW : κ * (γ + lam * τ) = 1 - r) :
    1 - κ ^ 2 * (γ ^ 2 - lam ^ 2 * W ^ 2 + 2 * lam * τ * (γ - lam * W)) =
      (1 - κ * (γ - lam * W)) ^ 2 + 2 * r * (κ * (γ - lam * W)) := by
  have e : κ * lam * τ = 1 - r - κ * γ := by linear_combination hW
  linear_combination (-2 * κ * (γ - lam * W)) * e

/-- **`thm:multiscale` for an arbitrary target with an additive error**: `MultiConcl` with
`P_{1/b}[0 ↔ x]` replaced by any real `P(x)` with
`‖P(x) - M_{j_x}²‖ ≤ K_P‖M_{j_x}‖²ǧ_{j_x} + δ`; conclusion `|P(x) - ϑ_j²| ≤ Kϑ_j²/β_j + δ`. -/
def MultiConclE (L : ℕ) [NeZero L] (ℓ A ρ κ cg cm cT ε Ke KZ KG : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ →
  ∀ Nh : ℕ, Nh + 2 ≤ N →
  ∀ m ∈ mRange L N, ∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
  ∀ (lam : ℕ → ℂ) (Kl KP : ℝ), 0 ≤ Kl → 0 ≤ KP → HLam R Nh m b μ₀ lam Kl →
  ∀ (Pf : Lam 2 L N → ℝ) (δ : ℝ) (x : Lam 2 L N), x ≠ 0 → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ‖((Pf x : ℝ) : ℂ) - Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x) ^ 2‖ ≤
      KP * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ ^ 2 *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 + δ →
    ∃ jp : ℕ, (jp : ℤ) = jPhys L N (eucl x / (L : ℝ) ^ N) ∧
      jp ≤ Obs.coal L (0 : Lam 2 L N) x ∧ Obs.coal L (0 : Lam 2 L N) x ≤ jp + 1 ∧
      |Pf x - thetaSq R m b μ₀ jp| ≤
        multK L cg Ke KZ KG Kl KP * thetaSq R m b μ₀ jp / betaJ R m b μ₀ jp + δ

set_option maxHeartbeats 1000000 in
/-- **`MultiConclE` from `SpinConcl` and `MagConcl`** (the proof of `multiConcl_of` with `δ`). -/
theorem multiConclE_of {L : ℕ} [NeZero L] {ℓ A ρ κ cg cm cT ε Ke KZ KG : ℝ} (hL2 : 2 ≤ L)
    (hε1 : ε ≤ 1) (hSp : SpinConcl L ℓ A ρ κ cg cm cT ε Ke KZ KG)
    (hMag : MagConcl L ℓ A ρ κ cg cm cT ε Ke KZ KG) :
    MultiConclE L ℓ A ρ κ cg cm cT ε Ke KZ KG := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ Nh hNh m hm b μ₀ hadm lam Kl KP hKl hKP hl Pf δ x hx hj hrg
  obtain ⟨jp, hjpd, hjp1, hjp2⟩ := coal_jPhys (N := N) hL2 hx
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  have hg : ∀ k ≤ Nh, 0 < (t k).1 := fun k hk => (hadm.1 k hk).1
  have hg1 : ∀ k ≤ Nh, (t k).1 ≤ 1 := fun k hk => ((hadm.1 k hk).2.1).trans hε1
  have hb : 0 < b := by have := hg 0 (Nat.zero_le _); rwa [htd, Hist.traj_zero] at this
  have hjpN : jp ≤ Nh := hjp1.trans hj
  set KM := spinMK L cg Ke KZ Kl KG 0 with hKMd
  set c := multC L cg Ke with hcd
  have hβ : 0 < betaL L := by
    have : 0 < Real.log L := Real.log_pos (by exact_mod_cast (by omega : 1 < L))
    unfold betaL; have := Real.pi_pos; positivity
  have hc : 0 ≤ c := by
    have : 0 ≤ max Ke (betaL L / 2) := le_trans (by linarith) (le_max_right _ _)
    rw [hcd, multC]; positivity
  have hmag := hMag N R hP hi0 hRℓ hRA hRρ (by omega) Nh hNh m hm b μ₀ hadm lam Kl hKl hl j hj
  have hwj : 0 < (b / (t j).1) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos (div_pos hb (hg j hj)) _
  have hKM : 0 ≤ KM := by
    have h0 : 0 ≤ KM * ((b / (t j).1) ^ (1 / 3 : ℝ) * (t j).1) := by
      rw [← mul_assoc]; exact (norm_nonneg _).trans hmag
    exact nonneg_of_mul_nonneg_left h0 (mul_pos hwj (hg j hj))
  have hcore := multi_coreE (P := Pf x) hwj (hg j hj).le (hg1 j hj) hKM hKP hmag hrg
  have hgap : |1 / (t j).1 - 1 / (t jp).1| ≤ c := by
    rcases (by omega : j = jp ∨ j = jp + 1) with e | e
    · rw [e, sub_self, abs_zero]; exact hc
    · obtain ⟨-, -, -, -, -, hband, -, -⟩ := hSp N R hP hi0 hRℓ hRA hRρ (by omega) Nh hNh
      have hk : jp < Nh := by omega
      have h1 := hband m hm b μ₀ hadm jp hk
      rw [← htd] at h1
      have hz : zA L m jp ≤ 2 := zA_le_two (by exact_mod_cast (by omega : 1 ≤ L))
        (multi_msq_le (by omega) (by omega) hm.1.le hm.2 (by omega))
      have hmx : 0 ≤ 2 * (1 + betaL L) * max Ke (betaL L / 2) := by
        have : 0 ≤ max Ke (betaL L / 2) := le_trans (by linarith) (le_max_right _ _)
        positivity
      have hz2 := mul_le_mul_of_nonneg_left hz hmx
      have hC : Cgu (betaL L) cg * (t jp).1 ≤ |Cgu (betaL L) cg| := by
        calc Cgu (betaL L) cg * (t jp).1 ≤ |Cgu (betaL L) cg| * (t jp).1 :=
              mul_le_mul_of_nonneg_right (le_abs_self _) (hg jp hjpN).le
          _ ≤ |Cgu (betaL L) cg| * 1 :=
              mul_le_mul_of_nonneg_left (hg1 jp hjpN) (abs_nonneg _)
          _ = _ := mul_one _
      rw [e]
      have h2 := abs_le.1 h1
      rw [abs_le, hcd, multC]
      constructor <;> linarith [h2.1, h2.2]
  have hwjp : 0 < (b / (t jp).1) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos (div_pos hb (hg jp hjpN)) _
  have hb3 : ((b / (t j).1) ^ (1 / 3 : ℝ)) ^ 3 * (t j).1 =
      ((b / (t jp).1) ^ (1 / 3 : ℝ)) ^ 3 * (t jp).1 := by
    rw [cube_rpow_third (div_pos hb (hg j hj)), cube_rpow_third (div_pos hb (hg jp hjpN)),
      div_mul_cancel₀ _ (hg j hj).ne', div_mul_cancel₀ _ (hg jp hjpN).ne']
  have hK1 : 0 ≤ KP * (1 + KM) ^ 2 + KM * (2 + KM) := by positivity
  have hsh := multi_shiftE hwj hwjp (hg j hj) (hg jp hjpN) (hg1 j hj) (hg1 jp hjpN) hc hK1 hb3
    hgap hcore
  refine ⟨jp, hjpd, hjp1, hjp2, ?_⟩
  have hth : thetaSq R m b μ₀ jp = ((b / (t jp).1) ^ (1 / 3 : ℝ)) ^ 2 := by
    rw [thetaSq, betaJ, ← htd, sq_rpow_third (div_pos hb (hg jp hjpN))]
    congr 1; field_simp
  have hbe : betaJ R m b μ₀ jp = 1 / (t jp).1 := by rw [betaJ, ← htd]
  rw [hth, hbe, div_div_eq_mul_div, div_one]
  convert hsh using 1

/-- **`thm:multiscale` at `h ≥ 0` on the trajectory**: for admissible `(b, μ₀)` at `m²` with
`b ≤ μ₀ + m²`, (H_λ) and `TwoPtSq` give, with `h = hPar b μ₀ m²` and `r = 1 - b⟨ψ̄_0ψ_0⟩ ∈ [0,1]`,
`|P_{1/b,h}[0 ↔ x, 0 ↮ g] - ϑ_j²| ≤ Kϑ_j²/β_j + K_r r`. -/
def MultiConclH (L : ℕ) [NeZero L] (ℓ A ρ κ cg cm cT ε Ke KZ KG : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ →
  ∀ Nh : ℕ, Nh + 2 ≤ N →
  ∀ m ∈ mRange L N, ∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
    b ≤ μ₀ + m →
  ∀ (lam : ℕ → ℂ) (Kl KP Kr : ℝ), 0 ≤ Kl → 0 ≤ KP → HLam R Nh m b μ₀ lam Kl →
    TwoPtSq R Nh m b μ₀ lam KP Kr →
  ∀ x : Lam 2 L N, x ≠ 0 → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∃ r : ℝ, 0 ≤ r ∧ r ≤ hPar b μ₀ m * Fintype.card (Lam 2 L N) ∧
      1 - (b : ℂ) * PtCorr2.avg0 L N m b μ₀ (psibar 0 * psi 0) = r ∧
    ∃ jp : ℕ, (jp : ℤ) = jPhys L N (eucl x / (L : ℝ) ^ N) ∧
      jp ≤ Obs.coal L (0 : Lam 2 L N) x ∧ Obs.coal L (0 : Lam 2 L N) x ≤ jp + 1 ∧
      |ghostTwo L N (1 / b) (hPar b μ₀ m) x - thetaSq R m b μ₀ jp| ≤
        multK L cg Ke KZ KG Kl KP * thetaSq R m b μ₀ jp / betaJ R m b μ₀ jp + Kr * r

theorem multiConclH_of {L : ℕ} [NeZero L] {ℓ A ρ κ cg cm cT ε Ke KZ KG : ℝ}
    (hE : MultiConclE L ℓ A ρ κ cg cm cT ε Ke KZ KG) :
    MultiConclH L ℓ A ρ κ cg cm cT ε Ke KZ KG := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ Nh hNh m hm b μ₀ hadm hh lam Kl KP Kr hKl hKP hl hsq x hx hj
  have hb : 0 < b := by
    have := (hadm.1 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  obtain ⟨r, hr0, -, hr, -, -, hrΛ⟩ := ward_r_bounds (L := L) (N := N) hb hm.1 hh
  refine ⟨r, hr0, hrΛ, hr, ?_⟩
  have h1 := hsq x hx hj
  rw [avg0_two_eq_ghost hb hm.1 hh x, hr, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr0] at h1
  exact hE N R hP hi0 hRℓ hRA hRρ Nh hNh m hm b μ₀ hadm lam Kl KP hKl hKP hl
    (fun y => ghostTwo L N (1 / b) (hPar b μ₀ m) y) (Kr * r) x hx hj h1

/-- **`thm:multiscale` at `h = 0` by `h ↓ 0`** (route (b)): at fixed `b`, if admissible data
`(m_n², μ_n)` with `h_n = hPar b μ_n m_n² ≥ 0`, (H_λ) and `TwoPtSq` (constants uniform in `n`)
exist with `h_n → 0`, then for every `x ≠ 0` with `j_x ≤ N_h` and every `δ > 0` there are `n`
and `j = j(|x|)` with `|P_{1/b}[0 ↔ x] - ϑ_j(m_n²)²| ≤ K ϑ_j(m_n²)²/β_j(m_n²) + δ`. -/
def MultiConclH0 (L : ℕ) [NeZero L] (ℓ A ρ κ cg cm cT ε Ke KZ KG : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ →
  ∀ Nh : ℕ, Nh + 2 ≤ N → ∀ (b : ℝ) (ms μs : ℕ → ℝ) (lams : ℕ → ℕ → ℂ) (Kl KP Kr : ℝ),
    0 ≤ Kl → 0 ≤ KP → 0 ≤ Kr →
    (∀ n, ms n ∈ mRange L N ∧
      Admissible (rgDataM R (ms n)) ((L : ℝ) ^ 2) κ cm cT Nh ε b (μs n) ∧ b ≤ μs n + ms n ∧
      HLam R Nh (ms n) b (μs n) (lams n) Kl ∧ TwoPtSq R Nh (ms n) b (μs n) (lams n) KP Kr) →
    Tendsto (fun n => hPar b (μs n) (ms n)) atTop (𝓝 0) →
  ∀ x : Lam 2 L N, x ≠ 0 → Obs.coal L (0 : Lam 2 L N) x ≤ Nh → ∀ δ : ℝ, 0 < δ →
    ∃ n jp : ℕ, (jp : ℤ) = jPhys L N (eucl x / (L : ℝ) ^ N) ∧
      jp ≤ Obs.coal L (0 : Lam 2 L N) x ∧ Obs.coal L (0 : Lam 2 L N) x ≤ jp + 1 ∧
      |Pconn L N (1 / b) x - thetaSq R (ms n) b (μs n) jp| ≤
        multK L cg Ke KZ KG Kl KP * thetaSq R (ms n) b (μs n) jp / betaJ R (ms n) b (μs n) jp + δ

theorem multiConclH0_of {L : ℕ} [NeZero L] {ℓ A ρ κ cg cm cT ε Ke KZ KG : ℝ}
    (hH : MultiConclH L ℓ A ρ κ cg cm cT ε Ke KZ KG) :
    MultiConclH0 L ℓ A ρ κ cg cm cT ε Ke KZ KG := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ Nh hNh b ms μs lams Kl KP Kr hKl hKP hKr hseq hlim x hx hj δ hδ
  have hb : 0 < b := by
    have := ((hseq 0).2.1.1 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  -- `P_{1/b,h_n}[0 ↔ x, 0 ↮ g] → P_{1/b}[0 ↔ x]` and `K_r h_n|Λ| → 0`
  have hP1 := (tendsto_ghostTwo (L := L) (N := N) (β := 1 / b) (by positivity) x).comp hlim
  have hP2 : Tendsto (fun n => Kr * (hPar b (μs n) (ms n) * Fintype.card (Lam 2 L N))) atTop
      (𝓝 0) := by
    have := (hlim.mul_const (Fintype.card (Lam 2 L N) : ℝ)).const_mul Kr
    simpa using this
  have hev1 := (Metric.tendsto_nhds.1 hP1) (δ / 2) (by linarith)
  have hev2 := (Metric.tendsto_nhds.1 hP2) (δ / 2) (by linarith)
  obtain ⟨n, h1, h2⟩ := (hev1.and hev2).exists
  obtain ⟨hmn, hadm, hh, hl, hsq⟩ := hseq n
  obtain ⟨r, hr0, hrΛ, -, jp, hjpd, hjp1, hjp2, hest⟩ :=
    hH N R hP hi0 hRℓ hRA hRρ Nh hNh (ms n) hmn b (μs n) hadm hh (lams n) Kl KP Kr hKl hKP hl hsq
      x hx hj
  refine ⟨n, jp, hjpd, hjp1, hjp2, ?_⟩
  rw [Real.dist_eq] at h1 h2
  simp only [Function.comp] at h1
  rw [sub_zero] at h2
  have hKr : Kr * r ≤ Kr * (hPar b (μs n) (ms n) * Fintype.card (Lam 2 L N)) :=
    mul_le_mul_of_nonneg_left hrΛ hKr
  have h2' := (le_abs_self _).trans h2.le
  rw [abs_sub_comm] at h1
  calc |Pconn L N (1 / b) x - thetaSq R (ms n) b (μs n) jp|
      ≤ |Pconn L N (1 / b) x - ghostTwo L N (1 / b) (hPar b (μs n) (ms n)) x| +
          |ghostTwo L N (1 / b) (hPar b (μs n) (ms n)) x - thetaSq R (ms n) b (μs n) jp| :=
        abs_sub_le _ _ _
    _ ≤ _ := by linarith

end

end Spin2
