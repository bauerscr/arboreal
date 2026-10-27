import Loc.EstDefs

/-!
# Transfer of test functions from `ℤ^d` to the torus

A test function `H` on sequences in `ℤ^d` which vanishes unless all points lie in the box
`|u|_∞ ≤ S` defines the test function `z ↦ H(ρ_b z)` on the torus `Λ_N`, and for
`2(S + 2P) < L^N` the discrete derivatives of order `≤ P` (in each variable) are transferred:
`∇^α (H ∘ ρ_b) = (∇^α H) ∘ ρ_b`.
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD

variable {d L N : ℕ} [NeZero L]

theorem supNormZ_ρS (b : Lam d L N) (a : Sf (Lam d L N)) :
    supNormZ (ρS b a).1 = supNorm (a.1 - b) :=
  supNormZ_rep_eq _

theorem mabs_le_of_le {a c : Dir d → ℕ} (h : a ≤ c) : Grassmann.mabs a ≤ Grassmann.mabs c :=
  Finset.sum_le_sum fun e _ => h e

theorem supNorm_dirHom_le (β : Dir d → ℕ) :
    supNorm (dirHom β : Lam d L N) ≤ Grassmann.mabs β := by
  rw [← prj_dirHomZ]
  exact (supNorm_prj_le _).trans (supNormZ_dirHomZ_le β)

theorem rep_vadd_sub (b x : Lam d L N) (β : Dir d → ℕ) {S P : ℕ}
    (hSP : 2 * (S + 2 * P) < L ^ N) (hβ : Grassmann.mabs β ≤ P) (hx : supNorm (x - b) ≤ S + P) :
    rep ((β +ᵥ x) - b) = β +ᵥ rep (x - b) := by
  symm
  apply eq_rep
  · rw [vaddZ_def, prj_add, prj_dirHomZ, prj_rep, Grassmann.vadd_def]
    show dirHom β + (x - b) = dirHom β + x - b
    abel
  · have h1 := supNormZ_add_le (dirHomZ β) (rep (x - b))
    have h2 := supNormZ_dirHomZ_le β
    rw [supNormZ_rep_eq] at h1
    rw [vaddZ_def]
    omega

theorem lt_supNorm_vadd_sub (b x : Lam d L N) (β : Dir d → ℕ) {S P : ℕ}
    (hβ : Grassmann.mabs β ≤ P) (hx : S + P < supNorm (x - b)) :
    S < supNorm ((β +ᵥ x) - b) := by
  have e : x - b = ((β +ᵥ x) - b) + -(dirHom β) := by
    rw [Grassmann.vadd_def]
    show x - b = dirHom β + x - b + -dirHom β
    abel
  have h1 := supNorm_add_le ((β +ᵥ x) - b) (-(dirHom β : Lam d L N))
  rw [← e, supNorm_neg] at h1
  have h2 := supNorm_dirHom_le (L := L) (N := N) β
  omega

theorem lt_supNormZ_vadd (u : Zd d) (β : Dir d → ℕ) {S P : ℕ}
    (hβ : Grassmann.mabs β ≤ P) (hu : S + P < supNormZ u) :
    S < supNormZ (β +ᵥ u) := by
  have e : u = (β +ᵥ u) + -(dirHomZ β) := by rw [vaddZ_def]; abel
  have h1 := supNormZ_add_le (β +ᵥ u) (-(dirHomZ β))
  rw [← e, supNormZ_neg] at h1
  have h2 := supNormZ_dirHomZ_le β
  omega

/-- The transfer lemma. -/
theorem nab_comp_ρS {W : Type*} [AddCommGroup W] [Module ℝ W] (b : Lam d L N) {n : ℕ}
    (H : (Fin n → Sf (Zd d)) → W) {S P : ℕ}
    (hSP : 2 * (S + 2 * P) < L ^ N)
    (hH : ∀ w : Fin n → Sf (Zd d), (∃ k, S < supNormZ (w k).1) → H w = 0)
    (α : Fin n → Dir d → ℕ) (hα : ∀ k, mabs (α k) ≤ P) (z : Fin n → Sf (Lam d L N)) :
    nab α (fun z => H (ρS b ∘ z)) z = nab α H (ρS b ∘ z) := by
  simp only [nab, nabla_apply]
  refine sum_congr rfl fun β hβ => ?_
  have hβP : ∀ k, Grassmann.mabs (β k) ≤ P := fun k =>
    (mabs_le_of_le (Finset.mem_Iic.1 (Fintype.mem_piFinset.1 hβ k))).trans (hα k)
  congr 1
  by_cases hA : ∀ k, supNorm ((z k).1 - b) ≤ S + P
  · show H _ = H _
    congr 1
    funext k
    simp only [Function.comp, ρS, sh]
    rw [rep_vadd_sub b (z k).1 (β k) hSP (hβP k) (hA k)]
  · push Not at hA
    obtain ⟨k, hk⟩ := hA
    show H _ = H _
    rw [hH _ ⟨k, ?_⟩, hH _ ⟨k, ?_⟩]
    · simp only [Function.comp, ρS, sh]
      rw [← supNormZ_rep_eq] at hk
      exact lt_supNormZ_vadd _ (β k) (hβP k) hk
    · simp only [Function.comp, ρS, sh]
      rw [supNormZ_rep_eq]
      exact lt_supNorm_vadd_sub b (z k).1 (β k) (hβP k) hk

end

end Loc
