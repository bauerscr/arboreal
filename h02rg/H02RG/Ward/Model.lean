import Psi4.Main
import PtCorr.ContJoint
import Ward.Bridge
import Ward.Defs
import H02.Cont
import Suscept.Real

-- Merged from `Ward/ModelFacts.lean` (phase 3).
section

/-!
# Regularity of the `ℍ^{0|2}` model with nearest-neighbour weights

Specialisations of `H02.continuous_expect`, `H02.expect_one_pos`, `H02.continuousOn_avg` to
`β_{xy} = nnW β` and a constant field `h`.
-/

namespace Ward

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]


/-- `(β, h) ↦ [F]_{β,h}` is continuous on `ℝ²` (nearest-neighbour weights, constant field). -/
theorem continuous_expect_nnW (F : H02.Grassmann (Lam d L N)) :
    Continuous fun q : ℝ × ℝ => H02.expect (nnW d L N q.1) (fun _ => q.2) F := by
  refine H02.continuous_expect (fun q : ℝ × ℝ => nnW d L N q.1) (fun q => nnW_symm q.1)
    (fun q _ => q.2) ?_ ?_ F
  · refine continuous_pi fun x => continuous_pi fun y => ?_
    simp only [nnW]
    exact continuous_fst.mul continuous_const
  · exact continuous_pi fun _ => continuous_snd

theorem expect_one_pos_nnW {β h : ℝ} (hβ : 0 ≤ β) (hh : 0 ≤ h) :
    0 < H02.expect (nnW d L N β) (fun _ => h) 1 :=
  H02.expect_one_pos (nnW_symm β) (nnW_nonneg hβ) fun _ => hh

/-- `(β, h) ↦ ⟨F⟩_{β,h}` is continuous on `[0,∞)²`. -/
theorem continuousOn_avg_nnW (F : H02.Grassmann (Lam d L N)) :
    ContinuousOn (fun q : ℝ × ℝ => H02.avg (nnW d L N q.1) (fun _ => q.2) F)
      {q | 0 ≤ q.1 ∧ 0 ≤ q.2} := by
  refine ((continuous_expect_nnW F).continuousOn).div (continuous_expect_nnW 1).continuousOn
    fun q hq => (expect_one_pos_nnW hq.1 hq.2).ne'

end

end Ward

end

/-!
# The model identification `(b₀, m²) ↦ (β, h)` (Section `sec:ward`)

For an initial coupling `V₀c` (with `b`-component `b₀`) and **real** `b > 0`, `m² ≥ 0`:

* `s0R V₀c b m = Re s₀^c(m², b)`, `a0R V₀c b m = Re a₀^c(m², b)`; by reality
  (`FlowDataW.conj`) these are `s₀^c`, `a₀^c` themselves (`s₀c_ofReal`, `a₀c_ofReal`);
* `betaF V₀c b m = (1 + s₀)²/b`, `hF V₀c b m = -1 + (a₀ + m²)(1 + s₀)/b`,
  `c2F V₀c b m = b/(1 + s₀) = (1 + s₀)/β` (`e:quartic-rescale`);
* `Vh (betaF) (hF) m² s₀ = V₀sp V₀c m² b` (`Vh_eq_V₀sp`), hence the bridge of `Ward.Bridge`
  identifies the `ℍ^{0|2}` model at `(β, h) = (betaF, hF)` with the `ψ`-model `avgM`
  (`avg_ξη_eq`, `avg_z_eq`, `expect_one_eq`).
-/

namespace Ward

noncomputable section

open Finset Grassmann Loc Step Obs FRD PtCorr Psi4

/-- `s₀ = Re s₀^c(m², b)`. -/
def s0R (V₀c : ℝ → ℂ → Vcoup) (b m : ℝ) : ℝ := (s₀c V₀c m b).re

/-- `a₀ = Re a₀^c(m², b)`. -/
def a0R (V₀c : ℝ → ℂ → Vcoup) (b m : ℝ) : ℝ := (a₀c V₀c m b).re

/-- `β(b, m²) = (1 + s₀)²/b`. -/
def betaF (V₀c : ℝ → ℂ → Vcoup) (b m : ℝ) : ℝ := (1 + s0R V₀c b m) ^ 2 / b

/-- `h(b, m²) = -1 + (a₀ + m²)(1 + s₀)/b`. -/
def hF (V₀c : ℝ → ℂ → Vcoup) (b m : ℝ) : ℝ := -1 + (a0R V₀c b m + m) * (1 + s0R V₀c b m) / b

/-- `c² = b/(1 + s₀) = (1 + s₀)/β`. -/
def c2F (V₀c : ℝ → ℂ → Vcoup) (b m : ℝ) : ℝ := b / (1 + s0R V₀c b m)

variable {V₀c : ℝ → ℂ → Vcoup}

section Real

variable (hconj : ∀ msq b₀, V₀c msq (starRingEnd ℂ b₀) = (V₀c msq b₀).conj)
include hconj

theorem s₀c_ofReal (b m : ℝ) : s₀c V₀c m b = (s0R V₀c b m : ℂ) := by
  obtain ⟨hz, hy, -⟩ := Flow.V0c_real hconj m b
  apply Complex.ext <;> simp [s0R, s₀c, hz, hy]

theorem a₀c_ofReal (b m : ℝ) : a₀c V₀c m b = (a0R V₀c b m : ℂ) := by
  obtain ⟨-, -, ha⟩ := Flow.V0c_real hconj m b
  apply Complex.ext <;> simp [a0R, a₀c, ha]

/-- **The model identification**: `Vh (β, h, m², s₀) = (0, s₀^c, a₀^c, b)`. -/
theorem Vh_eq_V₀sp {b m : ℝ} (hb : 0 < b) (hs : -1 < s0R V₀c b m) :
    Vh (betaF V₀c b m) (hF V₀c b m) m (s0R V₀c b m) = V₀sp V₀c m b := by
  have h1 : (1 + s0R V₀c b m) ≠ 0 := by linarith
  have hb0 : b ≠ 0 := hb.ne'
  unfold Vh V₀sp
  rw [s₀c_ofReal hconj, a₀c_ofReal hconj]
  congr 2
  · unfold betaF hF
    field_simp
    ring
  · unfold betaF
    field_simp

end Real

theorem c2F_eq {b m : ℝ} (hb : 0 < b) (hs : -1 < s0R V₀c b m) :
    (1 + s0R V₀c b m) / betaF V₀c b m = c2F V₀c b m := by
  have h1 : (1 + s0R V₀c b m) ≠ 0 := by linarith
  unfold betaF c2F
  field_simp

theorem betaF_pos {b m : ℝ} (hb : 0 < b) (hs : -1 < s0R V₀c b m) : 0 < betaF V₀c b m := by
  unfold betaF
  have : 0 < 1 + s0R V₀c b m := by linarith
  positivity

theorem c2F_pos {b m : ℝ} (hb : 0 < b) (hs : -1 < s0R V₀c b m) : 0 < c2F V₀c b m := by
  unfold c2F
  have : 0 < 1 + s0R V₀c b m := by linarith
  positivity

/-! ### The bridge in model form -/

section Bridge

variable {d L N : ℕ} [NeZero L]
  (hconj : ∀ msq b₀, V₀c msq (starRingEnd ℂ b₀) = (V₀c msq b₀).conj)
  {b m : ℝ} (hb : 0 < b) (hs : -1 < s0R V₀c b m) (hm : 0 < m)
include hconj hb hs hm

theorem avg_ξη_eq (a x : Lam d L N) :
    ((H02.avg (nnW d L N (betaF V₀c b m)) (fun _ => hF V₀c b m) (H02.ξ a * H02.η x) : ℝ) : ℂ) =
      (c2F V₀c b m : ℂ) * avgM d L N V₀c m b (psibar a * psi x) := by
  rw [bridge_avg_ξη (betaF_pos hb hs) hs hm, Vh_eq_V₀sp hconj hb hs, c2F_eq hb hs]
  rfl

theorem avg_z_eq (hZ : ZM d L N V₀c m b ≠ 0) (a : Lam d L N) :
    ((H02.avg (nnW d L N (betaF V₀c b m)) (fun _ => hF V₀c b m) (H02.z a) : ℝ) : ℂ) =
      1 - (c2F V₀c b m : ℂ) * avgM d L N V₀c m b (psibar a * psi a) := by
  have hZ' : Obs.Zb (Suscept.Cov d L N m)
      (VE (Vh (betaF V₀c b m) (hF V₀c b m) m (s0R V₀c b m)) (univ : Finset (Lam d L N))) ≠ 0 := by
    rw [Vh_eq_V₀sp hconj hb hs]; exact hZ
  rw [bridge_avg_z (betaF_pos hb hs) hs hm hZ', Vh_eq_V₀sp hconj hb hs, c2F_eq hb hs]
  rfl

theorem expect_one_eq :
    ((H02.expect (nnW d L N (betaF V₀c b m)) (fun _ => hF V₀c b m) 1 : ℝ) : ℂ) =
      (((betaF V₀c b m / (1 + s0R V₀c b m)) ^ Fintype.card (Lam d L N) *
          (FRD.negLap + m • 1 : Matrix (Lam d L N) (Lam d L N) ℝ).det : ℝ) : ℂ) *
        ZM d L N V₀c m b := by
  rw [bridge_Z (betaF_pos hb hs) hs hm, Vh_eq_V₀sp hconj hb hs]
  rfl

end Bridge

/-! ### Bounds and regularity from `FlowData` -/

section Flow

variable {d L : ℕ} [NeZero L] {A ℓ₀ lbar C κ : ℝ} (HF : FlowData d L A ℓ₀ V₀c lbar C κ)
include HF

theorem abs_s0R_le {b m : ℝ} (hb : 0 ≤ b) (hbl : b ≤ lbar) (hm : 0 ≤ m) :
    |s0R V₀c b m| ≤ 2 * C * b := by
  have h := ((s₀c_reg HF).1 m hm b (by rwa [Complex.norm_real, Real.norm_of_nonneg hb])).1
  rw [Complex.norm_real, Real.norm_of_nonneg hb] at h
  exact (Complex.abs_re_le_norm _).trans h

/-- `b ↦ s₀(b, m²)` is `2C`-Lipschitz on `[0, λ̄)`, uniformly in `m² ≥ 0`. -/
theorem s0R_lip {b b' m : ℝ} (hm : 0 ≤ m) (hb : 0 ≤ b) (hbl : b < lbar) (hb' : 0 ≤ b')
    (hbl' : b' < lbar) : |s0R V₀c b' m - s0R V₀c b m| ≤ 2 * C * |b' - b| := by
  obtain ⟨e1, e2, e3⟩ := (s₀c_reg HF).2.2 m hm
  have hmem : ∀ x : ℝ, 0 ≤ x → x < lbar → (x : ℂ) ∈ Metric.ball (0 : ℂ) lbar := fun x hx hxl => by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg hx]; exact hxl
  have h := lipschitz_of_deriv_le e1 (fun z hz => (e3 z hz).1) (hmem b hb hbl) (hmem b' hb' hbl')
  rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
  calc |s0R V₀c b' m - s0R V₀c b m| = |(s₀c V₀c m b' - s₀c V₀c m b).re| := by
        simp [s0R]
    _ ≤ ‖s₀c V₀c m b' - s₀c V₀c m b‖ := Complex.abs_re_le_norm _
    _ ≤ 2 * C * |b' - b| := h

/-- Joint continuity of `s₀`, `a₀` in `(b, m²)` on `[0, λ̄) × [0, ∞)`. -/
theorem s0R_a0R_cont :
    ContinuousOn (fun p : ℝ × ℝ => s0R V₀c p.1 p.2) (Set.Ico 0 lbar ×ˢ Set.Ici 0) ∧
    ContinuousOn (fun p : ℝ × ℝ => a0R V₀c p.1 p.2) (Set.Ico 0 lbar ×ˢ Set.Ici 0) := by
  obtain ⟨h1, h2, h3, -⟩ := HF.jointCont
  have hmap : Set.MapsTo (fun p : ℝ × ℝ => (p.2, (p.1 : ℂ))) (Set.Ico 0 lbar ×ˢ Set.Ici 0)
      (Set.Ici 0 ×ˢ Metric.ball (0 : ℂ) lbar) := by
    rintro ⟨x, y⟩ ⟨⟨hx0, hxl⟩, hy⟩
    refine ⟨hy, ?_⟩
    simp only [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg hx0]
    exact hxl
  have hc : ContinuousOn (fun p : ℝ × ℝ => (p.2, (p.1 : ℂ))) (Set.Ico 0 lbar ×ˢ Set.Ici 0) :=
    (continuous_snd.prodMk (Complex.continuous_ofReal.comp continuous_fst)).continuousOn
  refine ⟨?_, ?_⟩
  · exact Complex.continuous_re.comp_continuousOn ((h2.add h1).comp hc hmap)
  · exact Complex.continuous_re.comp_continuousOn (h3.comp hc hmap)

end Flow

end

end Ward
