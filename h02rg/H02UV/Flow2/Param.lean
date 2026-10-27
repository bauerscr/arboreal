import Flow2.History

/-!
# Continuous dependence of the finite-horizon flow on a parameter

A family `F : P → HData X` of history-dependent flow data, indexed by a topological space `P`
(in the application `P` is an interval of masses `m²`), such that

* every `F p` satisfies the hypotheses `HHyp` of `prop:C6` with the *same* constants, and
* the maps `(p, t) ↦ G_j(p, t), m_j(p, t), T_j(p, t)` are jointly continuous.

Then the admissible initial value `μ₀^c(p, b)` (`muc`) is jointly continuous in `(p, b)` on
`P × (0, b_max]` (`continuousOn_muc_param`), and so is every coordinate of the admissible
trajectory (`continuousOn_traj_param`), in particular `ǧ_N` (`continuousOn_gN_param`).

The proof is that of `Flow2.Hist.continuousOn_muc`: uniqueness of the admissible `μ₀` for every
`p`, the sign of `μ_N` along the clamped flow on both sides of `μ₀^c`, and the joint continuity of
the clamped flow (`continuous_trajc_param`).
-/

open Set Filter Topology

noncomputable section

namespace Flow2

namespace Hist

variable {X : ℕ → Type*} [∀ j, NormedAddCommGroup (X j)]
variable {P : Type*} [TopologicalSpace P]

/-! ### Causal recursions with a parameter -/

lemma continuous_appr_param {s0 : P → Seq X} {st : P → ∀ j, Seq X → ℝ × ℝ × X (j + 1)}
    (hs0 : Continuous s0) {N : ℕ}
    (hst : ∀ j < N, Continuous fun q : P × Seq X => st q.1 j q.2) :
    ∀ k ≤ N, Continuous fun p => appr (s0 p) (st p) k := by
  intro k
  induction k with
  | zero => intro _; exact hs0
  | succ k ih =>
    intro hk
    have h := ih (by omega)
    exact h.update (k + 1) ((hst k (by omega)).comp (continuous_id.prodMk h))

lemma continuous_tr_param {s0 : P → Seq X} {st : P → ∀ j, Seq X → ℝ × ℝ × X (j + 1)}
    (hs0 : Continuous s0) {N : ℕ}
    (hst : ∀ j < N, Continuous fun q : P × Seq X => st q.1 j q.2) {k : ℕ} (hk : k ≤ N) :
    Continuous fun p => tr (s0 p) (st p) k :=
  (continuous_apply k).comp (continuous_appr_param hs0 hst k hk)

/-! ### The parametric clamped flow -/

variable (F : P → HData X) {Λ β δ κ cg cm cT : ℝ} {N : ℕ}

/-- Joint continuity of the flow data in the parameter and the history. -/
structure ParamCont (N : ℕ) : Prop where
  G : ∀ j < N, Continuous fun q : P × Seq X => (F q.1).G j q.2
  m : ∀ j < N, Continuous fun q : P × Seq X => (F q.1).m j q.2
  T : ∀ j < N, Continuous fun q : P × Seq X => (F q.1).T j q.2

variable {F}

lemma continuous_trajc_param (hc : ParamCont F N) {j : ℕ} (hj : j ≤ N) :
    Continuous (fun q : P × ℝ × ℝ => trajc (F q.1) Λ cm q.2.1 q.2.2 j) := by
  refine continuous_tr_param
    (s0 := fun q : P × ℝ × ℝ => fun _ => (q.2.1, clamp (cmu Λ cm * q.2.1) q.2.2, 0))
    (st := fun q => stepc (F q.1) Λ cm) ?_ (fun k hk => ?_) hj
  · refine continuous_pi fun i => (continuous_fst.comp continuous_snd).prodMk
      ((continuous_clamp.comp ((continuous_const.mul (continuous_fst.comp continuous_snd)).prodMk
        (continuous_snd.comp continuous_snd))).prodMk continuous_const)
  · have hG : Continuous fun q : (P × ℝ × ℝ) × Seq X => (F q.1.1).G k q.2 :=
      (hc.G k hk).comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
    have hm : Continuous fun q : (P × ℝ × ℝ) × Seq X => (F q.1.1).m k q.2 :=
      (hc.m k hk).comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
    have hT : Continuous fun q : (P × ℝ × ℝ) × Seq X => (F q.1.1).T k q.2 :=
      (hc.T k hk).comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
    exact hG.prodMk ((continuous_clamp.comp ((continuous_const.mul hG).prodMk
      ((continuous_const.mul (continuous_fst.comp (continuous_snd.comp
        ((continuous_apply k).comp continuous_snd)))).add hm))).prodMk hT)

lemma continuous_phi_param (hc : ParamCont F N) (μ : ℝ) :
    Continuous (fun q : P × ℝ => (trajc (F q.1) Λ cm q.2 μ N).2.1) :=
  (continuous_fst.comp (continuous_snd.comp (continuous_trajc_param hc le_rfl))).comp
    (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))

/-! ### Continuity of `μ₀^c` and of the trajectory -/

variable {A a ε : ℝ} (H : ∀ p, HHyp (F p) Λ β δ κ cg cm cT N A a ε)
  (he : ε ≤ eps0u Λ β δ κ cg cm) (hε : 0 < ε) (ha0 : a ≤ a0h Λ κ A) (hc : ParamCont F N)
include H he hε ha0 hc

/-- **Joint continuity of `μ₀^c` in the parameter and `b`.** -/
theorem continuousOn_muc_param :
    ContinuousOn (fun q : P × ℝ => muc (F q.1) Λ κ cm cT N ε q.2)
      (univ ×ˢ Ioc 0 (bmax β δ cg N ε)) := by
  rintro ⟨p, b⟩ ⟨-, hb⟩
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro η hη
  set μs := muc (F p) Λ κ cm cT N ε b
  have hp := phi_pos_of_gt (H p) he hε ha0 hb (show μs < μs + η / 2 by linarith)
  have hn := phi_neg_of_lt (H p) he hε ha0 hb (show μs - η / 2 < μs by linarith)
  have e1 : ∀ᶠ q in 𝓝 (p, b), 0 < (trajc (F q.1) Λ cm q.2 (μs + η / 2) N).2.1 :=
    (continuous_phi_param hc _).continuousAt.eventually (lt_mem_nhds hp)
  have e2 : ∀ᶠ q in 𝓝 (p, b), (trajc (F q.1) Λ cm q.2 (μs - η / 2) N).2.1 < 0 :=
    (continuous_phi_param hc _).continuousAt.eventually (gt_mem_nhds hn)
  filter_upwards [eventually_mem_nhdsWithin, (e1.and e2).filter_mono nhdsWithin_le_nhds]
    with q hq ⟨h1, h2⟩
  have hqb : q.2 ∈ Ioc 0 (bmax β δ cg N ε) := hq.2
  obtain ⟨μ'', hmem, hz⟩ := intermediate_value_Icc (by linarith : μs - η / 2 ≤ μs + η / 2)
    (continuous_phi (H q.1) q.2).continuousOn ⟨h2.le, h1.le⟩
  have := eq_muc (H q.1) he hε ha0 hqb (admissible_of_zero (H q.1) he hε hqb hz)
  rw [Real.dist_eq, ← this, abs_lt]
  constructor <;> linarith [hmem.1, hmem.2]

/-- **Joint continuity of the admissible trajectory** (all couplings `ǧ_j, μ_j, x_j`, `j ≤ N`). -/
theorem continuousOn_traj_param {j : ℕ} (hj : j ≤ N) :
    ContinuousOn (fun q : P × ℝ => traj (F q.1) Λ q.2 (muc (F q.1) Λ κ cm cT N ε q.2) j)
      (univ ×ˢ Ioc 0 (bmax β δ cg N ε)) := by
  have h : ContinuousOn (fun q : P × ℝ =>
      trajc (F q.1) Λ cm q.2 (muc (F q.1) Λ κ cm cT N ε q.2) j)
      (univ ×ˢ Ioc 0 (bmax β δ cg N ε)) :=
    (continuous_trajc_param hc hj).comp_continuousOn
      (continuousOn_fst.prodMk (continuousOn_snd.prodMk (continuousOn_muc_param H he hε ha0 hc)))
  refine h.congr fun q hq => ?_
  exact (trajc_eq_traj (H q.1) (muc_spec (H q.1) he hε hq.2) N le_rfl j hj).symm

end Hist

end Flow2
