import Loc.EstPartI

/-!
# The coefficients of `Loc_{X,Y} F`

`Loc_{X,Y} F` is a constant plus a combination of the `ψ_u ψ̄_v`: its coefficients vanish on
sequences of length `∉ {0, 2}` and on sequences of length `2` with equal spins, and its constant
term is `F_∅ |Y|/|X|`.  Consequences for `F - Loc_X F` when `F` is `U(1)`-invariant.
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD

section General

variable {Λ : Type*} [DecidableEq Λ]

theorem psi_mul_psibar_eq (x y : Λ) : psi x * psibar y = psiPow ![(x, 1), (y, -1)] := by
  simp [psiPow, ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, psibar,
    psi, ψ, Matrix.vecTail]

theorem coeff_elim0 (F : Grassmann.N Λ) (z : Fin 0 → Sf Λ) : coeff F z = ε F := by
  simp [coeff, Dseq]

theorem coeff_one_of_ne {n : ℕ} (z : Fin n → Sf Λ) (hn : n ≠ 0) :
    coeff (1 : Grassmann.N Λ) z = 0 := by
  have : (1 : Grassmann.N Λ) = ExteriorAlgebra.ιMulti ℂ 0 (Fin.elim0 : Fin 0 → V Λ) := by
    simp [ExteriorAlgebra.ιMulti_zero_apply]
  rw [this]; exact coeff_ιMulti_of_ne _ _ hn

theorem coeff_psi_psibar_of_ne (u v : Λ) {n : ℕ} (z : Fin n → Sf Λ) (hn : n ≠ 2) :
    coeff (psi u * psibar v) z = 0 := by
  rw [psi_mul_psibar_eq, psiPow]; exact coeff_ιMulti_of_ne _ _ hn

theorem coeff_psi_psibar_same [Fintype Λ] (u v a a' : Λ) (σ : ℤˣ) :
    coeff (psi u * psibar v) ![(a, σ), (a', σ)] = 0 := by
  rw [psi_mul_psibar_eq, coeff_psiPow]
  refine sum_eq_zero fun τ _ => ?_
  rw [if_neg, mul_zero]
  intro h
  have hs : ∀ i : Fin 2, (![(a, σ), (a', σ)] i).2 = σ := by intro i; fin_cases i <;> rfl
  have e0 : (1 : ℤˣ) = σ := by
    have := congrArg Prod.snd (congrFun h 0)
    simpa [hs] using this
  have e1 : (-1 : ℤˣ) = σ := by
    have := congrArg Prod.snd (congrFun h 1)
    simpa [hs] using this
  exact absurd (e0.trans e1.symm) (by decide)

end General

variable {d L N : ℕ} [NeZero L]

theorem coeff_monoAt_eq_zero (M : Mono d) (x : Lam d L N) {n : ℕ} (z : Fin n → Sf (Lam d L N))
    (hz : ∀ u v : Lam d L N, coeff (psi u * psibar v) z = 0) : coeff (monoAt M x) z = 0 := by
  rw [monoAt, ← coeffL_apply, map_list_sum, List.map_map]
  refine List.sum_eq_zero fun a ha => ?_
  obtain ⟨p, _, rfl⟩ := List.mem_map.1 ha
  simp [coeffL_apply, hz]

theorem coeff_LocXY_eq_zero (X Y : Finset (Lam d L N)) (F : Alg d L N) {n : ℕ}
    (z : Fin n → Sf (Lam d L N)) (hn : n ≠ 0)
    (hz : ∀ u v : Lam d L N, coeff (psi u * psibar v) z = 0) : coeff (LocXY X Y F) z = 0 := by
  rw [LocXY, coeff_add, coeff_smul, coeff_one_of_ne z hn, mul_zero, zero_add, coeff_sum]
  refine sum_eq_zero fun M _ => ?_
  rw [coeff_smul, monoSet, coeff_sum, sum_eq_zero fun x _ => coeff_monoAt_eq_zero M x z hz,
    mul_zero]

theorem eps_monoAt (M : Mono d) (x : Lam d L N) : ε (monoAt M x) = 0 := by
  rw [← coeff_elim0 _ (Fin.elim0 : Fin 0 → Sf (Lam d L N))]
  exact coeff_monoAt_eq_zero M x _ fun u v => coeff_psi_psibar_of_ne u v _ (by decide)

theorem eps_LocXY (X Y : Finset (Lam d L N)) (F : Alg d L N) :
    ε (LocXY X Y F) = ε F * Y.card / X.card := by
  have h : ∀ M, ε (monoSet M Y) = 0 := fun M => by
    rw [monoSet, map_sum]; exact sum_eq_zero fun x _ => eps_monoAt M x
  rw [LocXY, map_add, map_sum]
  simp [h]

theorem eps_LocX {X : Finset (Lam d L N)} (hne : X.Nonempty) (F : Alg d L N) :
    ε (LocX X F) = ε F := by
  rw [LocX, eps_LocXY]
  have : (X.card : ℂ) ≠ 0 := by exact_mod_cast hne.card_pos.ne'
  field_simp

/-! ### `F - Loc_X F` -/

theorem coeff_sub_LocX_of_ne (X : Finset (Lam d L N)) (F : Alg d L N) {n : ℕ}
    (z : Fin n → Sf (Lam d L N)) (hn0 : n ≠ 0) (hn2 : n ≠ 2) :
    coeff (F - LocX X F) z = coeff F z := by
  rw [sub_eq_add_neg, coeff_add, show -LocX X F = (-1 : ℂ) • LocX X F by simp, coeff_smul, LocX,
    coeff_LocXY_eq_zero X X F z hn0 fun u v => coeff_psi_psibar_of_ne u v z hn2]
  ring

theorem card_spins_add {n : ℕ} (z : Fin n → Sf (Lam d L N)) :
    (univ.filter fun i => (z i).2 = 1).card + (univ.filter fun i => (z i).2 = -1).card = n := by
  rw [← card_union_of_disjoint]
  · have : (univ.filter fun i => (z i).2 = 1) ∪ (univ.filter fun i => (z i).2 = -1) = univ := by
      ext i
      simp only [mem_union, mem_filter, mem_univ, true_and, iff_true]
      exact Int.units_eq_one_or _
    rw [this, card_univ, Fintype.card_fin]
  · rw [disjoint_filter]
    intro i _ h1 h2
    exact absurd (h1.symm.trans h2) (by decide)

theorem coeff_eq_zero_of_odd {F : Alg d L N} (hF : IsSym F) {n : ℕ} (hn : Odd n)
    (z : Fin n → Sf (Lam d L N)) : coeff F z = 0 := by
  refine hF n z fun h => ?_
  have := card_spins_add z
  rw [h] at this
  obtain ⟨k, hk⟩ := hn
  omega

theorem coeff_same_spin_eq_zero {F : Alg d L N} (hF : IsSym F) (a a' : Lam d L N) (σ : ℤˣ) :
    coeff F ![(a, σ), (a', σ)] = 0 := by
  refine hF 2 _ fun h => ?_
  have hs : ∀ i : Fin 2, (![(a, σ), (a', σ)] i).2 = σ := by intro i; fin_cases i <;> rfl
  simp only [hs] at h
  rcases Int.units_eq_one_or σ with rfl | rfl
  · simp at h
  · simp at h

theorem coeff_sub_LocX_same (X : Finset (Lam d L N)) {F : Alg d L N} (hF : IsSym F)
    (a a' : Lam d L N) (σ : ℤˣ) : coeff (F - LocX X F) ![(a, σ), (a', σ)] = 0 := by
  rw [sub_eq_add_neg, coeff_add, show -LocX X F = (-1 : ℂ) • LocX X F by simp, coeff_smul, LocX,
    coeff_LocXY_eq_zero X X F _ (by decide) fun u v => coeff_psi_psibar_same u v a a' σ,
    coeff_same_spin_eq_zero hF]
  ring

theorem eps_sub_LocX {X : Finset (Lam d L N)} (hne : X.Nonempty) (F : Alg d L N) :
    ε (F - LocX X F) = 0 := by
  rw [map_sub, eps_LocX hne, sub_self]

theorem mu_sub_LocX {X : Finset (Lam d L N)} (hX : Patch X) (hne : X.Nonempty) (F : Alg d L N)
    (β : Mono d) : mu (base X) β (F - LocX X F) = 0 := by
  rw [sub_eq_add_neg, mu_add, show -LocX X F = (-1 : ℂ) • LocX X F by simp, mu_smul,
    mu_LocX hX hne]
  ring

end

end Loc
