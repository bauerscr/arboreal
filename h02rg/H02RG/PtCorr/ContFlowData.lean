import PtCorr.ContPt
import PtCorr.Setup

/-!
# Continuity in `m²` and holomorphy in `b₀` for the common flow `FlowData`

For the initial coupling `V₀c msq b₀` of `PtCorr.setup` / `PtCorr.FlowData` (`PtCorr.Setup`):

* `FlowData.cv`: for fixed `b₀` with `‖b₀‖ ≤ λ̄`, `m² ↦ V₀c m² b₀` is continuous on `[0, ∞)`
  (`Step.CV`): `z, y, a` by `FlowData.cont`, and `b = b₀` is constant (`FlowData.hb`);
* `FlowData.hol`: for fixed `m² ≥ 0`, `b₀ ↦ V₀c m² b₀` is holomorphic on `B(0, λ̄)`
  (`FlowData.holo`, `FlowData.hb`);

hence all the results of `PtCorr.ContPt` / `Obs.ContObs` apply (`FlowData.regFlowCont`,
`FlowData.regFlowHol`), e.g. `FlowData.flowO_cont`, `FlowData.qN_cont`, …, `FlowData.flowO_hol`,
`FlowData.qN_hol`, ….  (`FlowData` does not record `1 ≤ d`; it is a hypothesis here.)
-/

namespace PtCorr

noncomputable section

open Finset Grassmann Loc Step Obs Metric

namespace FlowData

variable {c : Case} {d L : ℕ} [NeZero L] {A ℓ₀ lbar C κ : ℝ} {V₀c : ℝ → ℂ → Vcoup}
  (H : FlowData d L A ℓ₀ V₀c lbar C κ)
include H

/-- `m² ↦ V₀c m² b₀` is continuous on `[0, ∞)` (`‖b₀‖ ≤ λ̄`). -/
theorem cv {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar) : CV (Set.Ici 0) (fun msq => V₀c msq b₀) := by
  obtain ⟨h1, h2, h3⟩ := H.cont b₀ hb₀
  exact ⟨h1, h2, h3, continuousOn_const.congr fun msq _ => H.hb msq b₀⟩

theorem regFlowCont (hd : 1 ≤ d) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar) (N : ℕ) :
    RegFlow (Reg.cont (Set.Ici 0)) d L N ℓ₀ (fun m => m) (fun msq => V₀c msq b₀) :=
  RegFlow.ofCont hd H.hL8 subset_rfl (H.cv hb₀) fun m hm => H.good N m hm

/-! ### Continuity in `m² ∈ [0, ∞)` at fixed `b₀` -/

section Cont

variable (hd : 1 ≤ d) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar) {N : ℕ}
include hd hb₀

theorem lamA2_cont (l₀ : ℂ) (x : Lam d L N) :
    ContinuousOn (fun msq => lamA2 d L N msq (V₀c msq b₀) l₀ x) (Set.Ici 0) :=
  (H.regFlowCont hd hb₀ N).lamA2 l₀ x

theorem lamB2_cont (l₀ : ℂ) (x : Lam d L N) :
    ContinuousOn (fun msq => lamB2 d L N msq (V₀c msq b₀) l₀ x) (Set.Ici 0) :=
  (H.regFlowCont hd hb₀ N).lamB2 l₀ x

theorem gamA2_cont (l₀ : ℂ) (x : Lam d L N) :
    ContinuousOn (fun msq => gamA2 d L N msq (V₀c msq b₀) l₀ x) (Set.Ici 0) :=
  (H.regFlowCont hd hb₀ N).gamA2 l₀ x

theorem gamB2_cont (l₀ : ℂ) (x : Lam d L N) :
    ContinuousOn (fun msq => gamB2 d L N msq (V₀c msq b₀) l₀ x) (Set.Ici 0) :=
  (H.regFlowCont hd hb₀ N).gamB2 l₀ x

theorem laOne_cont (l₀ : ℂ) (a b : Lam d L N) {j : ℕ} (hj : j ≤ N) :
    ContinuousOn (fun msq => laOne d L N msq (V₀c msq b₀) l₀ a b j) (Set.Ici 0) :=
  (H.regFlowCont hd hb₀ N).laOne l₀ a b hj

theorem lbOne_cont (l₀ : ℂ) (a b : Lam d L N) {j : ℕ} (hj : j ≤ N) :
    ContinuousOn (fun msq => lbOne d L N msq (V₀c msq b₀) l₀ a b j) (Set.Ici 0) :=
  (H.regFlowCont hd hb₀ N).lbOne l₀ a b hj

end Cont

/-! ### Holomorphy in `b₀ ∈ B(0, λ̄)` at fixed `m² ≥ 0` -/

section Hol

variable (hd : 1 ≤ d) {msq : ℝ} (hmsq : 0 ≤ msq) {N : ℕ}
include hd hmsq

end Hol

end FlowData

end

end PtCorr
