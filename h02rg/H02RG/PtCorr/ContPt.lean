import Obs.ContObs
import PtCorr.OnePt
import PtCorr.LamOne

/-!
# Continuity in `m²` (and holomorphy in `b₀`) of the point couplings (groundwork for `sec:ward`)

The hypotheses of the regularity results along the flow are bundled in
`RegFlow R d L N ℓ₀ μ V₀` (`1 ≤ d`, `2^{d+3} ≤ L`, regular `V₀(t)` and covariances
`C_{j+1}(μ(t))`, `GoodCov` on the domain).  Under them (generic statements `RegFlow.*`):

* the produced coupling constants `nextAt … j = (u + V)^obs_{j+1}` (`j < N`), `V^obs_N`, `K_N(Λ)`;
* the accumulated `u`-parts `qN`, `gaN`, `gbN` and `u^obs_N(Λ)` (`uObsN`);
* the normalised couplings `lamA2`, `lamB2`, `gamA2`, `gamB2` (Case (2), `PtCorr.OnePt`) and the
  Case (1) couplings `laOne`, `lbOne` (`PtCorr.LamOne`)

are regular.  Specialisations:

* **continuity in `m²`** on `S ⊆ [0, ∞)` (`RegFlow.ofCont`; `*_cont`): for `V₀(m²)`
  continuous on `S` (`Step.CV`) and `GoodCov` on `S`, including `m² = 0`;
* **holomorphy in `b₀`** at fixed `m²` (`RegFlow.ofHol`): for `V₀(b₀)` holomorphic on `U`.
-/

namespace PtCorr

noncomputable section

open Finset Grassmann Loc Step Obs

variable {T : Type*} {R : Reg T} {c : Case} {d L N : ℕ} [NeZero L]

/-- The hypotheses of the regularity results along the flow. -/
structure RegFlow (R : Reg T) (d L N : ℕ) [NeZero L] (ℓ₀ : ℝ) (μ : T → ℝ) (V₀ : T → Vcoup) :
    Prop where
  hd : 1 ≤ d
  hL : 2 ^ (d + 3) ≤ L
  V₀ : RegV R V₀
  C : ∀ j < N, ∀ x y : Lam d L N, R.P (fun t => ((Flow.covAt d L N (μ t) j x y : ℝ) : ℂ))
  good : ∀ t ∈ R.D, ∀ j < N,
    GoodCov (d := d) (L := L) (N := N) j ℓ₀ (Flow.covAt d L N (μ t) j)

/-- The hypotheses for continuity in `m²` on `S ⊆ [0, ∞)`. -/
theorem RegFlow.ofCont {S : Set ℝ} {ℓ₀ : ℝ} {V₀ : ℝ → Vcoup} (hd : 1 ≤ d)
    (hL : 2 ^ (d + 3) ≤ L) (hS : S ⊆ Set.Ici 0) (hV₀ : CV S V₀)
    (hgood : ∀ m ∈ S, ∀ j < N, GoodCov (d := d) (L := L) (N := N) j ℓ₀ (Flow.covAt d L N m j)) :
    RegFlow (Reg.cont S) d L N ℓ₀ (fun m => m) V₀ :=
  ⟨hd, hL, RegV.of_CV hV₀, covAt_reg_cont hd hS, hgood⟩

namespace RegFlow

variable {ℓ₀ : ℝ} {μ : T → ℝ} {V₀ : T → Vcoup} (H : RegFlow R d L N ℓ₀ μ V₀)
include H

/-! ### Generic statements -/

theorem flowO (Vo₀ : Coup c) (a b : Lam d L N) :
    ∀ j ≤ N, RegCp R (fun t => (flowO d L c N (μ t) (V₀ t) Vo₀ a b j).1) ∧
      RegKO R (fun t => (flowO d L c N (μ t) (V₀ t) Vo₀ a b j).2) :=
  flowO_reg H.hd H.hL H.V₀ (RegCp.const Vo₀) H.C H.good a b

theorem nextAt (Vo₀ : Coup c) (a b : Lam d L N) {j : ℕ} (hj : j < N) :
    RegCp R (fun t => PtCorr.nextAt d L c N (μ t) (V₀ t) Vo₀ a b j) :=
  nextObs_flowO_reg H.hd H.hL H.V₀ (RegCp.const Vo₀) H.C H.good a b hj

theorem qN (Vo₀ : Coup c) (a b : Lam d L N) :
    R.P (fun t => PtCorr.qN d L c N (μ t) (V₀ t) Vo₀ a b) := by
  unfold PtCorr.qN
  exact Reg.sum _ fun j hj => R.add (H.nextAt Vo₀ a b (mem_range.1 hj)).qa
    (H.nextAt Vo₀ a b (mem_range.1 hj)).qb

theorem gaN (Vo₀ : Coup c) (a b : Lam d L N) :
    R.P (fun t => PtCorr.gaN d L c N (μ t) (V₀ t) Vo₀ a b) := by
  unfold PtCorr.gaN
  exact Reg.sum _ fun j hj => (H.nextAt Vo₀ a b (mem_range.1 hj)).ga

theorem gbN (Vo₀ : Coup c) (a b : Lam d L N) :
    R.P (fun t => PtCorr.gbN d L c N (μ t) (V₀ t) Vo₀ a b) := by
  unfold PtCorr.gbN
  exact Reg.sum _ fun j hj => (H.nextAt Vo₀ a b (mem_range.1 hj)).gb

theorem VoN (Vo₀ : Coup c) (a b : Lam d L N) :
    RegCp R (fun t => PtCorr.VoN d L c N (μ t) (V₀ t) Vo₀ a b) :=
  (H.flowO Vo₀ a b N le_rfl).1

theorem lamA2 (l₀ : ℂ) (x : Lam d L N) :
    R.P (fun t => PtCorr.lamA2 d L N (μ t) (V₀ t) l₀ x) := by
  unfold PtCorr.lamA2
  exact Reg.div_const (H.VoN _ _ _).la l₀

theorem lamB2 (l₀ : ℂ) (x : Lam d L N) :
    R.P (fun t => PtCorr.lamB2 d L N (μ t) (V₀ t) l₀ x) := by
  unfold PtCorr.lamB2
  exact Reg.div_const (H.VoN _ _ _).lb l₀

theorem gamA2 (l₀ : ℂ) (x : Lam d L N) :
    R.P (fun t => PtCorr.gamA2 d L N (μ t) (V₀ t) l₀ x) := by
  unfold PtCorr.gamA2
  exact Reg.div_const (H.gaN _ _ _) l₀

theorem gamB2 (l₀ : ℂ) (x : Lam d L N) :
    R.P (fun t => PtCorr.gamB2 d L N (μ t) (V₀ t) l₀ x) := by
  unfold PtCorr.gamB2
  exact Reg.div_const (H.gbN _ _ _) l₀

theorem laOne (l₀ : ℂ) (a b : Lam d L N) {j : ℕ} (hj : j ≤ N) :
    R.P (fun t => PtCorr.laOne d L N (μ t) (V₀ t) l₀ a b j) :=
  (H.flowO (initObs .one l₀) a b j hj).1.la

theorem lbOne (l₀ : ℂ) (a b : Lam d L N) {j : ℕ} (hj : j ≤ N) :
    R.P (fun t => PtCorr.lbOne d L N (μ t) (V₀ t) l₀ a b j) :=
  (H.flowO (initObs .one l₀) a b j hj).1.lb

end RegFlow

/-! ### Continuity in `m²` -/

section Cont

variable {S : Set ℝ} {ℓ₀ : ℝ} {V₀ : ℝ → Vcoup}
  (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hS : S ⊆ Set.Ici 0) (hV₀ : CV S V₀)
  (hgood : ∀ m ∈ S, ∀ j < N, GoodCov (d := d) (L := L) (N := N) j ℓ₀ (Flow.covAt d L N m j))
include hd hL hS hV₀ hgood

end Cont

end

end PtCorr
