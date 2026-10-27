import Flow2.FixedRDiff
import Flow2.FixedRParam
import Flow2.RangeFlow

/-!
# The consolidated abstract flow theorem at fixed `β_R`

`FixedConcl F …`: the conclusions of `thm:flow` for one flow datum `F`, on the fixed-`β_R` range
`Ufix` (no a priori range `(0, b_max]`):
* uniqueness of the admissible `μ₀`; existence and uniqueness of the shooting solution
  `b(y)` (`bsh`) for every `y ∈ (0, ε]`, with `b(y) ≤ y`;
* `Ufix` is open and order connected, `ǧ_N` is strictly increasing on all `b` with an admissible
  trajectory and maps `Ufix` onto `(0, ε)`;
* `μ₀(b)`, `ǧ_N(b)` are continuous and differentiable on `Ufix`, and so is every coordinate
  `s_j(b, μ₀(b))`, `j ≤ N`;
* the domain bounds along admissible trajectories (`InD3`: `0 < ǧ_j ≤ ε`, `|μ_j| ≤ c_μ ǧ_j`,
  `‖x_j‖ ≤ c_x ǧ_j³`; `b ≤ ǧ_j ≤ ǧ_N`), strict on `Ufix` (`ǧ_j < ε`, `|μ_j| < c_μ ǧ_j`);
* (i) in logarithmic form.

`fh_flow_final`: `FixedConcl` from `HHyp`, `MonoHyp`, `MonoCoef`, `HDiff`, `SharpHyp` and the
numerical conditions.

`ParamConcl F …`: for a family `F : P → HData X`, openness of `UfixP` and joint continuity of
`μ₀`, `ǧ_N`, the trajectory on it, and of the shooting solution `(p, y) ↦ b(p, y)` on
`P × (0, ε)`; `fh_flow_final_param`.
-/

open Set Filter Topology

noncomputable section

namespace Flow2

namespace Hist

variable {X : ℕ → Type*} [∀ j, NormedAddCommGroup (X j)] [∀ j, NormedSpace ℝ (X j)]

/-- **The conclusions of `thm:flow` at fixed `β_R`** for one flow datum. -/
structure FixedConcl (F : HData X) (Λ β κ cg cm cT : ℝ) (N : ℕ) (ε E : ℝ) : Prop where
  /-- the admissible `μ₀` is unique -/
  unique_mu : ∀ b μ μ', Admissible F Λ κ cm cT N ε b μ → Admissible F Λ κ cm cT N ε b μ' → μ = μ'
  /-- (ii): for every `y ∈ (0, ε]` there is a unique `b` with `ǧ_N(b) = y` -/
  shoot : ∀ y, 0 < y → y ≤ ε →
    ∃! b, (∃ μ, Admissible F Λ κ cm cT N ε b μ) ∧ gN F Λ κ cm cT N ε b = y
  /-- the shooting solution `bsh` solves it, and `0 < b(y) ≤ y` -/
  bsh_spec : ∀ y, 0 < y → y ≤ ε →
    (∃ μ, Admissible F Λ κ cm cT N ε (bsh F Λ κ cm cT N ε y) μ) ∧
      gN F Λ κ cm cT N ε (bsh F Λ κ cm cT N ε y) = y ∧ bsh F Λ κ cm cT N ε y ∈ Ioc 0 y
  /-- for `y < ε` the shooting solution lies in `Ufix` -/
  bsh_mem : ∀ y, 0 < y → y < ε → bsh F Λ κ cm cT N ε y ∈ Ufix F Λ κ cm cT N ε
  isOpen : IsOpen (Ufix F Λ κ cm cT N ε)
  ordConnected : (Ufix F Λ κ cm cT N ε).OrdConnected
  strictMono : StrictMonoOn (gN F Λ κ cm cT N ε) {b | ∃ μ, Admissible F Λ κ cm cT N ε b μ}
  image : gN F Λ κ cm cT N ε '' Ufix F Λ κ cm cT N ε = Ioo 0 ε
  cont_muc : ContinuousOn (muc F Λ κ cm cT N ε) (Ufix F Λ κ cm cT N ε)
  cont_gN : ContinuousOn (gN F Λ κ cm cT N ε) (Ufix F Λ κ cm cT N ε)
  diff_muc : DifferentiableOn ℝ (muc F Λ κ cm cT N ε) (Ufix F Λ κ cm cT N ε)
  diff_gN : DifferentiableOn ℝ (gN F Λ κ cm cT N ε) (Ufix F Λ κ cm cT N ε)
  diff_traj : ∀ j ≤ N, DifferentiableOn ℝ (fun b => traj F Λ b (muc F Λ κ cm cT N ε b) j)
    (Ufix F Λ κ cm cT N ε)
  /-- the domain bounds along admissible trajectories -/
  dom : ∀ b μ, Admissible F Λ κ cm cT N ε b μ → ∀ j ≤ N,
    InD3 Λ κ cm cT ε (traj F Λ b μ j) ∧ b ≤ (traj F Λ b μ j).1 ∧
      (traj F Λ b μ j).1 ≤ (traj F Λ b μ N).1
  /-- strict domain bounds on `Ufix` -/
  dom_strict : ∀ b ∈ Ufix F Λ κ cm cT N ε, ∀ j ≤ N,
    (traj F Λ b (muc F Λ κ cm cT N ε b) j).1 < ε ∧
      |(traj F Λ b (muc F Λ κ cm cT N ε b) j).2.1| <
        cmu Λ cm * (traj F Λ b (muc F Λ κ cm cT N ε b) j).1
  /-- (i), logarithmic form -/
  log : ∀ b μ, Admissible F Λ κ cm cT N ε b μ → ∀ n ≤ N,
    |1 / (traj F Λ b μ n).1 - 1 / b + β * n| ≤
      2 * (1 + β) * E + 5 * Cgu β cg / β * Real.log ((traj F Λ b μ n).1 / b)

section Final

variable {F : HData X} {Λ β δ κ cg cm cT : ℝ} {N : ℕ} {A a ε E w p q r p₂ q₂ r₂ : ℝ}
  {e : ℕ → ℝ}

/-- **The consolidated abstract flow theorem at fixed `β_R`.** -/
theorem fh_flow_final (H : HHyp F Λ β δ κ cg cm cT N A a ε)
    (HM : MonoHyp F Λ β δ κ cg cm cT N A a ε w) (hC : MonoCoef Λ κ A a w p q r p₂ q₂ r₂)
    (HD : HDiff F Λ β δ κ cg cm cT N ε) (S : SharpHyp F Λ β δ κ cg cm cT N ε cg E e)
    (he : ε ≤ eps0u Λ β δ κ cg cm) (hgβ : cg * ε ≤ (1 - δ) * β)
    (hgβ' : cg * ε ≤ (1 - δ) * β / 2) (ha0 : a ≤ a0h Λ κ A) (hε : 0 < ε) :
    FixedConcl F Λ β κ cg cm cT N ε E := by
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := fh_flow_fixedR H HM hC he hgβ ha0 hε
  obtain ⟨d1, d2, d3⟩ := fh_flow_fixedR_diff H he hgβ ha0 HD
  refine ⟨r1, r2, fun y hy0 hy => ?_, fun y hy0 hy => bsh_mem_Ufix H HM hC he hgβ ha0 hε hy0 hy,
    r4, r5, r8, r9, r6, r7, d1, d2, d3, fun b μ h j hj => ?_, fun b hb j hj => ?_,
    fun b μ h n hn => ginv_log H he hgβ' S h hn⟩
  · obtain ⟨h1, h2⟩ := bsh_spec H HM hC he hgβ ha0 hε hy0 hy
    exact ⟨h1, h2, r3 y hy0 hy _ h1 h2⟩
  · exact ⟨h.1 j hj, b_le_traj_fst H hgβ h j hj, traj_le_N H hgβ h j hj⟩
  · obtain ⟨μ₁, h₁, hg₁⟩ := hb
    have hadm := muc_spec_of H ha0 h₁
    have hg : (traj F Λ b (muc F Λ κ cm cT N ε b) N).1 < ε := by
      rw [muc_eq_of_adm H ha0 h₁]; exact hg₁
    exact ⟨traj_g_lt_fixed H hgβ hadm hg j hj, adm_strict H he hadm j hj⟩

end Final

/-! ### The parametric conclusions -/

variable {P : Type*} [TopologicalSpace P]

/-- **The parametric conclusions** (continuity in the parameter, e.g. `m²`). -/
structure ParamConcl (F : P → HData X) (Λ κ cm cT : ℝ) (N : ℕ) (ε : ℝ) : Prop where
  isOpen : IsOpen (UfixP F Λ κ cm cT N ε)
  cont_muc : ContinuousOn (fun x : P × ℝ => muc (F x.1) Λ κ cm cT N ε x.2) (UfixP F Λ κ cm cT N ε)
  cont_gN : ContinuousOn (fun x : P × ℝ => gN (F x.1) Λ κ cm cT N ε x.2) (UfixP F Λ κ cm cT N ε)
  cont_traj : ∀ j ≤ N, ContinuousOn
    (fun x : P × ℝ => traj (F x.1) Λ x.2 (muc (F x.1) Λ κ cm cT N ε x.2) j) (UfixP F Λ κ cm cT N ε)
  cont_bsh : ContinuousOn (fun x : P × ℝ => bsh (F x.1) Λ κ cm cT N ε x.2) (univ ×ˢ Ioo 0 ε)

variable {F : P → HData X} {Λ β δ κ cg cm cT : ℝ} {N : ℕ} {A a ε w p q r p₂ q₂ r₂ : ℝ}

omit [∀ j, NormedSpace ℝ (X j)] in
/-- **The parametric flow theorem at fixed `β_R`.** -/
theorem fh_flow_final_param (H : ∀ p, HHyp (F p) Λ β δ κ cg cm cT N A a ε)
    (HM : ∀ p, MonoHyp (F p) Λ β δ κ cg cm cT N A a ε w)
    (hC : MonoCoef Λ κ A a w p q r p₂ q₂ r₂)
    (he : ε ≤ eps0u Λ β δ κ cg cm) (hgβ : cg * ε ≤ (1 - δ) * β) (ha0 : a ≤ a0h Λ κ A)
    (hε : 0 < ε) (hc : ParamCont F N) : ParamConcl F Λ κ cm cT N ε :=
  ⟨isOpen_UfixP H he hgβ ha0 hc, continuousOn_muc_UfixP H he hgβ ha0 hc,
    continuousOn_gN_UfixP H he hgβ ha0 hc, fun _ hj => continuousOn_traj_UfixP H he hgβ ha0 hc hj,
    continuousOn_bsh H HM hC he hgβ ha0 hε hc⟩

end Hist

end Flow2
