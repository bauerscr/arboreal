import Loc.Stencil

/-!
# The space of test polynomials of degree `≤ 2`

`PolySp` is the span of the dual test polynomials `Q_β(u, v)`; it contains every polynomial of
degree `≤ 2` in `(u, v) ∈ ℝ^d × ℝ^d`, and is invariant under affine substitutions
`(u, v) ↦ (A u + τ, A v + τ)` (`Qfun_comp_mem`).
-/

namespace Loc

noncomputable section

open Finset

variable {d : ℕ}

/-- `Q_β` as a function of `(u, v)`. -/
def Qfun (β : Mono d) : (Fin d → ℝ) × (Fin d → ℝ) → ℝ := fun w => Qpoly β w.1 w.2

/-- The span of the test polynomials. -/
def PolySp (d : ℕ) : Submodule ℝ ((Fin d → ℝ) × (Fin d → ℝ) → ℝ) :=
  Submodule.span ℝ (Set.range (Qfun (d := d)))

/-- Affine functions of `(u, v)`. -/
def Aff (d : ℕ) : Submodule ℝ ((Fin d → ℝ) × (Fin d → ℝ) → ℝ) :=
  Submodule.span ℝ ({fun _ => 1} ∪ Set.range (fun i : Fin d => fun w => w.1 i) ∪
    Set.range (fun i : Fin d => fun w => w.2 i))

theorem Qfun_mem (β : Mono d) : Qfun β ∈ PolySp d := Submodule.subset_span ⟨β, rfl⟩

theorem one_mem_PolySp : (fun _ => (1 : ℝ)) ∈ PolySp d := Qfun_mem Mono.c

theorem uu_mem (i k : Fin d) : (fun w : (Fin d → ℝ) × (Fin d → ℝ) => w.1 i * w.1 k) ∈ PolySp d := by
  by_cases h : i = k
  · subst h
    have := Submodule.smul_mem _ (2 : ℝ) (Qfun_mem (Mono.a2 s(i, i)))
    convert this using 1
    funext w; simp [Qfun, Qpoly]; ring
  · convert Qfun_mem (Mono.a2 s(i, k)) using 1
    funext w; simp [Qfun, Qpoly, h]

theorem vv_mem (i k : Fin d) : (fun w : (Fin d → ℝ) × (Fin d → ℝ) => w.2 i * w.2 k) ∈ PolySp d := by
  by_cases h : i = k
  · subst h
    have := Submodule.smul_mem _ (2 : ℝ) (Qfun_mem (Mono.b2 s(i, i)))
    convert this using 1
    funext w; simp [Qfun, Qpoly]; ring
  · convert Qfun_mem (Mono.b2 s(i, k)) using 1
    funext w; simp [Qfun, Qpoly, h]

theorem uv_mem (i k : Fin d) : (fun w : (Fin d → ℝ) × (Fin d → ℝ) => w.1 i * w.2 k) ∈ PolySp d :=
  Qfun_mem (Mono.m2 i k)

theorem Aff_le : Aff d ≤ PolySp d := by
  refine Submodule.span_le.2 ?_
  rintro f ((rfl | ⟨i, rfl⟩) | ⟨i, rfl⟩)
  · exact one_mem_PolySp
  · exact Qfun_mem (Mono.a1 i)
  · exact Qfun_mem (Mono.b1 i)

theorem mul_mem_PolySp {f g : (Fin d → ℝ) × (Fin d → ℝ) → ℝ} (hf : f ∈ Aff d) (hg : g ∈ Aff d) :
    f * g ∈ PolySp d := by
  induction hf using Submodule.span_induction with
  | zero => simpa using (PolySp d).zero_mem
  | add f f' _ _ h h' => rw [add_mul]; exact add_mem h h'
  | smul r f _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r h
  | mem f hf =>
    induction hg using Submodule.span_induction with
    | zero => simpa using (PolySp d).zero_mem
    | add g g' _ _ h h' => rw [mul_add]; exact add_mem h h'
    | smul r g _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ r h
    | mem g hg =>
      rcases hf with (rfl | ⟨i, rfl⟩) | ⟨i, rfl⟩ <;> rcases hg with (rfl | ⟨k, rfl⟩) | ⟨k, rfl⟩
      · convert one_mem_PolySp (d := d) using 1; funext w; simp
      · convert Qfun_mem (Mono.a1 k) using 1; funext w; simp [Qfun, Qpoly]
      · convert Qfun_mem (Mono.b1 k) using 1; funext w; simp [Qfun, Qpoly]
      · convert Qfun_mem (Mono.a1 i) using 1; funext w; simp [Qfun, Qpoly]
      · exact uu_mem i k
      · exact uv_mem i k
      · convert Qfun_mem (Mono.b1 i) using 1; funext w; simp [Qfun, Qpoly]
      · convert uv_mem k i using 1; funext w; simp [mul_comm]
      · exact vv_mem i k

theorem coord_mem_Aff (A : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) (τ : Fin d → ℝ) (i : Fin d) :
    (fun w : (Fin d → ℝ) × (Fin d → ℝ) => (A w.1 + τ) i) ∈ Aff d ∧
      (fun w : (Fin d → ℝ) × (Fin d → ℝ) => (A w.2 + τ) i) ∈ Aff d := by
  have hsum : ∀ u : Fin d → ℝ, (A u) i = ∑ k, u k * A (Pi.single k 1) i := by
    intro u
    conv_lhs => rw [show u = ∑ k, u k • (Pi.single k 1 : Fin d → ℝ) by
      ext j; simp [Finset.sum_apply, Pi.single_apply]]
    simp [map_sum, Finset.sum_apply]
  have h1 : (fun _ : (Fin d → ℝ) × (Fin d → ℝ) => (1 : ℝ)) ∈ Aff d :=
    Submodule.subset_span (Or.inl (Or.inl rfl))
  constructor
  · have : (fun w : (Fin d → ℝ) × (Fin d → ℝ) => (A w.1 + τ) i) =
        τ i • (fun _ => 1) + ∑ k, A (Pi.single k 1) i • (fun w => w.1 k) := by
      funext w
      simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, mul_one]
      rw [hsum, add_comm]; congr 1; refine Finset.sum_congr rfl fun k _ => by ring
    rw [this]
    exact add_mem (Submodule.smul_mem _ _ h1) (Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl (Or.inr ⟨k, rfl⟩))))
  · have : (fun w : (Fin d → ℝ) × (Fin d → ℝ) => (A w.2 + τ) i) =
        τ i • (fun _ => 1) + ∑ k, A (Pi.single k 1) i • (fun w => w.2 k) := by
      funext w
      simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, mul_one]
      rw [hsum, add_comm]; congr 1; refine Finset.sum_congr rfl fun k _ => by ring
    rw [this]
    exact add_mem (Submodule.smul_mem _ _ h1) (Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨k, rfl⟩)))

/-- Invariance under affine substitutions. -/
theorem Qfun_comp_mem (A : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) (τ : Fin d → ℝ) (β : Mono d) :
    (fun w => Qfun β (A w.1 + τ, A w.2 + τ)) ∈ PolySp d := by
  cases β with
  | c => exact one_mem_PolySp
  | a1 i => exact Aff_le (coord_mem_Aff A τ i).1
  | b1 i => exact Aff_le (coord_mem_Aff A τ i).2
  | a2 s =>
    induction s using Sym2.ind with
    | h i k =>
      by_cases h : i = k
      · subst h
        have := Submodule.smul_mem _ (1 / 2 : ℝ)
          (mul_mem_PolySp (coord_mem_Aff A τ i).1 (coord_mem_Aff A τ i).1)
        convert this using 1
        funext w; simp [Qfun, Qpoly]; ring
      · convert mul_mem_PolySp (coord_mem_Aff A τ i).1 (coord_mem_Aff A τ k).1 using 1
        funext w; simp [Qfun, Qpoly, h]
  | b2 s =>
    induction s using Sym2.ind with
    | h i k =>
      by_cases h : i = k
      · subst h
        have := Submodule.smul_mem _ (1 / 2 : ℝ)
          (mul_mem_PolySp (coord_mem_Aff A τ i).2 (coord_mem_Aff A τ i).2)
        convert this using 1
        funext w; simp [Qfun, Qpoly]; ring
      · convert mul_mem_PolySp (coord_mem_Aff A τ i).2 (coord_mem_Aff A τ k).2 using 1
        funext w; simp [Qfun, Qpoly, h]
  | m2 i k => exact mul_mem_PolySp (coord_mem_Aff A τ i).1 (coord_mem_Aff A τ k).2

/-- The coefficients of `Q_β ∘ (affine map)` in the basis `Q_β'`. -/
theorem exists_Qfun_comp (A : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) (τ : Fin d → ℝ) (β : Mono d) :
    ∃ T : Mono d → ℝ, ∀ u v, Qpoly β (A u + τ) (A v + τ) = ∑ β', T β' * Qpoly β' u v := by
  obtain ⟨T, hT⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 (Qfun_comp_mem A τ β)
  refine ⟨T, fun u v => ?_⟩
  have := congrFun hT (u, v)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Qfun] at this
  exact this.symm

end

end Loc
