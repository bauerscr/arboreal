import Step2.Flow.FlowThm
import Step2.FlowCont.FlowMsqStep
import Flow2.FixedRDiff2

/-!
# Continuity in `m²` at fixed `β_R`: the concrete form on `ℝ × ℝ`

The abstract parametric results (`Flow2.Hist.ParamConcl`) are stated for a family indexed by a
subtype `S` of masses. Here they are transferred to `ℝ × ℝ`:

* `UfixM R κ c_m c_T N_h ε S = {(m², b) : m² ∈ S, b ∈ Ufix(rgData (R.withMsq m²))}`;
* `isOpen_rel_of_subtype`: an open set of `S × ℝ` is the trace of an open set of `ℝ × ℝ`, so
  `UfixM` is relatively open in `S × ℝ`;
* `continuousOn_of_subtype2`: continuity on a subset of `S × ℝ` gives continuity on its image in
  `ℝ × ℝ` (a version of `continuousOn_of_subtype` for non-product sets);
* `MsqConcl`: the concrete conclusions (relative openness of `UfixM`, joint continuity of `μ₀`,
  `ǧ_{N_h}`, the trajectory on `UfixM`, joint continuity of the shooting solution
  `(m², y) ↦ b(m², y)` on `S × (0, ε)`, and continuity of `m² ↦ b(m², 1/β_R)` for `β_R > 1/ε`);
  `msqConcl_of`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

/-- An open subset of `S × ℝ` is the trace of an open subset of `ℝ × ℝ`. -/
theorem isOpen_rel_of_subtype {S : Set ℝ} {U : Set (S × ℝ)} (hU : IsOpen U) :
    ∃ O : Set (ℝ × ℝ), IsOpen O ∧
      O ∩ (S ×ˢ univ) = {q | ∃ hm : q.1 ∈ S, ((⟨q.1, hm⟩ : S), q.2) ∈ U} := by
  have hind : Topology.IsInducing (Prod.map ((↑) : S → ℝ) (id : ℝ → ℝ)) :=
    Topology.IsInducing.subtypeVal.prodMap Topology.IsInducing.id
  obtain ⟨O, hO, hpre⟩ := hind.isOpen_iff.1 hU
  refine ⟨O, hO, ?_⟩
  ext ⟨m, b⟩
  constructor
  · rintro ⟨hq, hm, -⟩
    refine ⟨hm, ?_⟩
    rw [← hpre]; exact hq
  · rintro ⟨hm, hq⟩
    rw [← hpre] at hq
    exact ⟨hq, hm, mem_univ _⟩

/-- Transfer of continuity from a subset of `S × ℝ` (subtype) to `ℝ × ℝ`. -/
theorem continuousOn_of_subtype2 {Y : Type*} [TopologicalSpace Y] {S : Set ℝ} {U : Set (S × ℝ)}
    {g : S × ℝ → Y} (hg : ContinuousOn g U) {f : ℝ × ℝ → Y}
    (hfg : ∀ (m : ℝ) (hm : m ∈ S) (b : ℝ), f (m, b) = g (⟨m, hm⟩, b)) {V : Set (ℝ × ℝ)}
    (hV : ∀ q ∈ V, ∃ hm : q.1 ∈ S, ((⟨q.1, hm⟩ : S), q.2) ∈ U) : ContinuousOn f V := by
  rw [continuousOn_iff_continuous_restrict]
  have h1 : Continuous fun x : V => (x : ℝ × ℝ) := continuous_subtype_val
  have hψ : Continuous fun x : V => ((⟨x.1.1, (hV x.1 x.2).1⟩ : S), x.1.2) :=
    (Continuous.subtype_mk h1.fst (fun x => (hV x.1 x.2).1)).prodMk h1.snd
  have h := hg.comp_continuous hψ (fun x => (hV x.1 x.2).2)
  refine h.congr fun x => ?_
  simp only [Function.comp_apply, restrict_apply]
  rw [← hfg x.1.1 (hV x.1 x.2).1 x.1.2]

variable {L : ℕ} [NeZero L]

/-- The masses and initial couplings with an admissible trajectory and `ǧ_{N_h} < ε`. -/
def UfixM {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (κ cm cT : ℝ) (Nh : ℕ)
    (ε : ℝ) (S : Set ℝ) : Set (ℝ × ℝ) :=
  {q | q.1 ∈ S ∧ q.2 ∈ Ufix (rgDataM R q.1) ((L : ℝ) ^ 2) κ cm cT Nh ε}

/-- **The conclusions of `thm:flow`(iii), continuity in `m²`, at fixed `β_R`.** -/
structure MsqConcl {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (κ cm cT : ℝ)
    (Nh : ℕ) (ε : ℝ) (S : Set ℝ) : Prop where
  /-- `UfixM` is relatively open in `S × ℝ` -/
  isOpen : ∃ O : Set (ℝ × ℝ), IsOpen O ∧ O ∩ (S ×ˢ univ) = UfixM R κ cm cT Nh ε S
  cont_muc : ContinuousOn (fun q : ℝ × ℝ => muc (rgDataM R q.1) ((L : ℝ) ^ 2) κ cm cT Nh ε q.2)
    (UfixM R κ cm cT Nh ε S)
  cont_gN : ContinuousOn (fun q : ℝ × ℝ => gN (rgDataM R q.1) ((L : ℝ) ^ 2) κ cm cT Nh ε q.2)
    (UfixM R κ cm cT Nh ε S)
  cont_traj : ∀ j ≤ Nh, ContinuousOn (fun q : ℝ × ℝ => traj (rgDataM R q.1) ((L : ℝ) ^ 2) q.2
      (muc (rgDataM R q.1) ((L : ℝ) ^ 2) κ cm cT Nh ε q.2) j) (UfixM R κ cm cT Nh ε S)
  /-- the shooting solution `b(m², y)` (`ǧ_{N_h} = y`) is jointly continuous -/
  cont_bsh : ContinuousOn (fun q : ℝ × ℝ => bsh (rgDataM R q.1) ((L : ℝ) ^ 2) κ cm cT Nh ε q.2)
    (S ×ˢ Ioo 0 ε)
  /-- `m² ↦ b(m², 1/β_R)` is continuous for every `β_R > 1/ε` -/
  cont_bsh_R : ∀ βR : ℝ, 1 / ε < βR →
    ContinuousOn (fun m => bsh (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε (1 / βR)) S

/-- `MsqConcl` from the abstract parametric conclusions on the subtype. -/
theorem msqConcl_of {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {κ cm cT : ℝ}
    {Nh : ℕ} {ε : ℝ} (hε : 0 < ε) {S : Set ℝ}
    (PC : ParamConcl (fun m : S => rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε) :
    MsqConcl R κ cm cT Nh ε S := by
  have hbsh : ContinuousOn (fun q : ℝ × ℝ => bsh (rgDataM R q.1) ((L : ℝ) ^ 2) κ cm cT Nh ε q.2)
      (S ×ˢ Ioo 0 ε) :=
    continuousOn_of_subtype2 PC.cont_bsh (fun _ _ _ => rfl) fun q hq => ⟨hq.1, mem_univ _, hq.2⟩
  refine ⟨?_, continuousOn_of_subtype2 PC.cont_muc (fun _ _ _ => rfl) fun q hq => ⟨hq.1, hq.2⟩,
    continuousOn_of_subtype2 PC.cont_gN (fun _ _ _ => rfl) fun q hq => ⟨hq.1, hq.2⟩,
    fun j hj => continuousOn_of_subtype2 (PC.cont_traj j hj) (fun _ _ _ => rfl)
      fun q hq => ⟨hq.1, hq.2⟩, hbsh, fun βR hβR => ?_⟩
  · obtain ⟨O, hO, hEq⟩ := isOpen_rel_of_subtype PC.isOpen
    refine ⟨O, hO, ?_⟩
    rw [hEq]
    ext ⟨m, b⟩
    exact ⟨fun ⟨hm, h⟩ => ⟨hm, h⟩, fun ⟨hm, h⟩ => ⟨hm, h⟩⟩
  · have h1 : 0 < 1 / ε := one_div_pos.2 hε
    have hy : 1 / βR ∈ Ioo 0 ε := by
      refine ⟨one_div_pos.2 (h1.trans hβR), ?_⟩
      have := one_div_lt_one_div_of_lt h1 hβR
      rwa [one_div_one_div] at this
    exact ContinuousOn.comp
      (g := fun q : ℝ × ℝ => bsh (rgDataM R q.1) ((L : ℝ) ^ 2) κ cm cT Nh ε q.2)
      (f := fun m : ℝ => ((m, 1 / βR) : ℝ × ℝ)) hbsh
      (continuous_id.prodMk continuous_const).continuousOn (fun m hm => ⟨hm, hy⟩)

end

end Step2
