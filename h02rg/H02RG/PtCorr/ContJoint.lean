import PtCorr.ContFlowData

/-!
# Joint continuity in `(m², b₀)` for the common flow `FlowData`

`FlowData` records, separately, continuity of `V₀c(·, b₀)` in `m² ≥ 0` (for `‖b₀‖ ≤ λ̄`) and
holomorphy of `V₀c(m², ·)` on `B(0, λ̄)` with `‖∂_{b₀} V₀c‖ ≤ C` uniformly in `m² ≥ 0`.  The
uniform derivative bound makes `V₀c(m², ·)` Lipschitz on the (convex) ball uniformly in `m²`,
hence (`jointCont_of_lipschitz`) `V₀c` is jointly continuous on `[0, ∞) × B(0, λ̄)`
(`FlowData.jointCont`), as needed in Section `sec:ward`.

Applying the generic results with the parameter space `T = ℝ × ℂ`, `μ = Prod.fst`
(`FlowData.regFlowJoint`), all quantities along the bulk and observable flows are jointly
continuous in `(m², b₀) ∈ [0, ∞) × B(0, λ̄)` (`FlowData.flowO_joint`, `FlowData.qN_joint`, …).
Composition with a continuous `b₀ = B(m²)` gives the families `m² ↦ V₀c(m², B(m²))`
(`FlowData.cv_comp`), to which `Obs.flowO_cont` etc. apply.
-/

namespace PtCorr

noncomputable section

open Finset Grassmann Loc Step Obs Metric

/-- Continuity in the first variable plus a Lipschitz bound in the second, uniform in the
first, give joint continuity. -/
theorem jointCont_of_lipschitz {X Y E : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [SeminormedAddCommGroup E] {f : X → Y → E} {S : Set X} {U : Set Y} {K : ℝ}
    (h1 : ∀ y ∈ U, ContinuousOn (fun x => f x y) S)
    (h2 : ∀ x ∈ S, ∀ y ∈ U, ∀ y' ∈ U, ‖f x y' - f x y‖ ≤ K * dist y' y) :
    ContinuousOn (fun p : X × Y => f p.1 p.2) (S ×ˢ U) := by
  rintro ⟨x₀, y₀⟩ ⟨hx₀, hy₀⟩
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ₁, hδ₁, h⟩ := Metric.continuousWithinAt_iff.1 (h1 y₀ hy₀ x₀ hx₀) (ε / 2) (by linarith)
  set K' := |K| + 1
  have hK' : 0 < K' := by positivity
  refine ⟨min δ₁ (ε / 2 / K'), lt_min hδ₁ (by positivity), ?_⟩
  rintro ⟨x, y⟩ ⟨hx, hy⟩ hd
  have hdx : dist x x₀ < δ₁ :=
    lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hd (min_le_left _ _))
  have hdy : dist y y₀ < ε / 2 / K' :=
    lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hd (min_le_right _ _))
  have e1 := h hx hdx
  have e2 := h2 x hx y₀ hy₀ y hy
  have e3 : K * dist y y₀ ≤ K' * dist y y₀ :=
    mul_le_mul_of_nonneg_right (by have := le_abs_self K; linarith) dist_nonneg
  have e4 : K' * dist y y₀ < ε / 2 := by
    have := mul_lt_mul_of_pos_left hdy hK'
    rwa [mul_div_cancel₀ _ hK'.ne'] at this
  rw [dist_eq_norm] at e1 ⊢
  calc ‖f x y - f x₀ y₀‖ = ‖(f x y - f x y₀) + (f x y₀ - f x₀ y₀)‖ := by
        congr 1; abel
    _ ≤ ‖f x y - f x y₀‖ + ‖f x y₀ - f x₀ y₀‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt (e2.trans (e3.trans e4.le)) e1
    _ = ε := by ring

/-- A holomorphic function on `B(0, r)` with `‖f'‖ ≤ C` is `C`-Lipschitz there. -/
theorem lipschitz_of_deriv_le {f : ℂ → ℂ} {r C : ℝ} (hf : DifferentiableOn ℂ f (ball 0 r))
    (hC : ∀ z ∈ ball (0 : ℂ) r, ‖deriv f z‖ ≤ C) {z w : ℂ} (hz : z ∈ ball (0 : ℂ) r)
    (hw : w ∈ ball (0 : ℂ) r) : ‖f w - f z‖ ≤ C * dist w z := by
  rw [dist_eq_norm]
  exact (convex_ball (0 : ℂ) r).norm_image_sub_le_of_norm_deriv_le
    (fun x hx => hf.differentiableAt (isOpen_ball.mem_nhds hx)) hC hz hw

namespace FlowData

variable {c : Case} {d L : ℕ} [NeZero L] {A ℓ₀ lbar C κ : ℝ} {V₀c : ℝ → ℂ → Vcoup}
  (H : FlowData d L A ℓ₀ V₀c lbar C κ)
include H

/-- **Joint continuity**: the initial coupling `V₀c` is jointly continuous on `[0, ∞) × B(0, λ̄)`. -/
theorem jointCont :
    ContinuousOn (fun p : ℝ × ℂ => (V₀c p.1 p.2).z) (Set.Ici 0 ×ˢ ball 0 lbar) ∧
    ContinuousOn (fun p : ℝ × ℂ => (V₀c p.1 p.2).y) (Set.Ici 0 ×ˢ ball 0 lbar) ∧
    ContinuousOn (fun p : ℝ × ℂ => (V₀c p.1 p.2).a) (Set.Ici 0 ×ˢ ball 0 lbar) ∧
    ContinuousOn (fun p : ℝ × ℂ => (V₀c p.1 p.2).b) (Set.Ici 0 ×ˢ ball 0 lbar) := by
  have hb : ∀ b ∈ ball (0 : ℂ) lbar, ‖b‖ ≤ lbar := fun b hb => by
    rw [mem_ball_zero_iff] at hb; exact hb.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact jointCont_of_lipschitz (fun b hb' => (H.cont b (hb b hb')).1)
      fun m hm z hz w hw => lipschitz_of_deriv_le (H.holo m hm).1
        (fun b hb' => ((H.holo m hm).2.2.2 b hb').1) hz hw
  · exact jointCont_of_lipschitz (fun b hb' => (H.cont b (hb b hb')).2.1)
      fun m hm z hz w hw => lipschitz_of_deriv_le (H.holo m hm).2.1
        (fun b hb' => ((H.holo m hm).2.2.2 b hb').2.1) hz hw
  · exact jointCont_of_lipschitz (fun b hb' => (H.cont b (hb b hb')).2.2)
      fun m hm z hz w hw => lipschitz_of_deriv_le (H.holo m hm).2.2.1
        (fun b hb' => ((H.holo m hm).2.2.2 b hb').2.2) hz hw
  · exact continuous_snd.continuousOn.congr fun p _ => H.hb p.1 p.2

/-- The hypotheses of the generic regularity results for joint continuity in `(m², b₀)`. -/
theorem regFlowJoint (hd : 1 ≤ d) (N : ℕ) :
    RegFlow (Reg.cont (Set.Ici (0 : ℝ) ×ˢ ball (0 : ℂ) lbar)) d L N ℓ₀ Prod.fst
      (fun p => V₀c p.1 p.2) := by
  obtain ⟨h1, h2, h3, h4⟩ := H.jointCont
  refine ⟨hd, H.hL8, ⟨h1, h2, h3, h4⟩, fun j hj x y => ?_, fun p hp => H.good N p.1 hp.1⟩
  exact Reg.cont_ofReal ((Flow.covAt_continuousOn hd hj x y).comp continuousOn_fst
    fun p hp => hp.1)

section Joint

variable (hd : 1 ≤ d) {N : ℕ}
include hd

theorem nextAt_joint (Vo₀ : Coup c) (a b : Lam d L N) {j : ℕ} (hj : j < N) :
    RegCp (Reg.cont (Set.Ici (0 : ℝ) ×ˢ ball (0 : ℂ) lbar))
      (fun p => nextAt d L c N p.1 (V₀c p.1 p.2) Vo₀ a b j) :=
  (H.regFlowJoint hd N).nextAt Vo₀ a b hj

theorem qN_joint (Vo₀ : Coup c) (a b : Lam d L N) :
    ContinuousOn (fun p : ℝ × ℂ => qN d L c N p.1 (V₀c p.1 p.2) Vo₀ a b)
      (Set.Ici 0 ×ˢ ball 0 lbar) :=
  (H.regFlowJoint hd N).qN Vo₀ a b

end Joint

end FlowData

end

end PtCorr
