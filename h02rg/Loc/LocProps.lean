import Loc.LocDef

/-!
# Algebraic properties of the localisation

* `LocX_eq_sum` — Proposition `prop:Loc` (iii): if `X` is the disjoint union of `X_1, …, X_n`
  then `Loc_X = ∑_i Loc_{X,X_i}`;
* `LocXY_mem` — `Loc_{X,Y}` maps into `𝒩(Y^□)` (for `Y` a `j`-polymer);
* `IsSym` — `U(1)` invariance (`𝒩_sym`, Section `sec:symmetries`).
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD Matrix

variable {d L N : ℕ} [NeZero L]

theorem monoSet_biUnion {ι : Type*} (s : Finset ι) (P : ι → Finset (Lam d L N))
    (hP : (s : Set ι).PairwiseDisjoint P) (M : Mono d) :
    monoSet M (s.biUnion P) = ∑ i ∈ s, monoSet M (P i) := by
  rw [monoSet, sum_biUnion hP]; rfl

/-- Proposition `prop:Loc` (iii): `Loc_X = ∑_i Loc_{X,X_i}` for a disjoint union
`X = X_1 ∪ ⋯ ∪ X_n`. -/
theorem LocX_eq_sum {ι : Type*} (s : Finset ι) (P : ι → Finset (Lam d L N))
    (hP : (s : Set ι).PairwiseDisjoint P) (F : Alg d L N) :
    LocX (s.biUnion P) F = ∑ i ∈ s, LocXY (s.biUnion P) (P i) F := by
  rw [LocX, LocXY]
  simp only [LocXY]
  rw [sum_add_distrib, ← sum_smul]
  congr 1
  · congr 1
    rw [card_biUnion hP]; push_cast
    rw [mul_sum, sum_div]
  · simp only [monoSet_biUnion s P hP, smul_sum]
    rw [sum_comm]

/-- `U(1)` invariance: every monomial of `F` has as many factors `ψ̄` as `ψ`. -/
def IsSym (F : Alg d L N) : Prop :=
  ∀ (n : ℕ) (z : Fin n → Sf (Lam d L N)),
    (univ.filter fun i => (z i).2 = 1).card ≠ (univ.filter fun i => (z i).2 = -1).card →
      coeff F z = 0

theorem monoAt_mem {X : Set (Lam d L N)} {M : Mono d} {x : Lam d L N}
    (h : ∀ a : Zd d, supNormZ a ≤ 1 → x + prj a ∈ X) : monoAt M x ∈ NX X := by
  rw [monoAt]
  refine Subalgebra.list_sum_mem _ fun F hF => ?_
  rw [List.mem_map] at hF
  obtain ⟨p, hp, rfl⟩ := hF
  have hb := stencil_offsets M p hp
  exact Subalgebra.smul_mem _ (mul_mem (ψ_mem_NX (h _ hb.1)) (ψ_mem_NX (h _ hb.2))) _

theorem supNorm_prj_le {n : ℕ} [NeZero n] (a : Zd d) : supNorm (prj a : Torus d n) ≤ supNormZ a := by
  rw [supNorm_le_iff]
  intro i
  refine (zabs_le_natAbs (a i)).trans ?_
  exact natAbs_le_supNormZ a i

/-- `Loc_{X,Y}` maps into `𝒩(Y^□)`. -/
theorem LocXY_mem (hd : 1 ≤ d) {j : ℕ} {Y : Finset (Lam d L N)} (hY : IsPolymer j Y)
    (X : Finset (Lam d L N)) (F : Alg d L N) : LocXY X Y F ∈ NX (nbhd j Y : Set (Lam d L N)) := by
  refine add_mem (Subalgebra.smul_mem _ (one_mem _) _) (Subalgebra.sum_mem _ fun M _ =>
    Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun y hy => monoAt_mem fun a ha => ?_) _)
  refine mem_nbhd_of_near hd hY hy ?_
  rw [add_sub_cancel_left]
  exact (supNorm_prj_le a).trans ha

end

end Loc
