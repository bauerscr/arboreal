import Obs2.Est.WObsAB
import Obs2.Loc.LocRepro
import Obs2.Map.SymO

/-!
# `loc^{ab}_X` reproduces every `U(1)`-invariant element of `𝒩({a,b})`

The range of the barycentric `loc^{ab,t}` (`Obs2.locABt`) is spanned by `1`, `ψ̄_uψ_v`
(`u, v ∈ {a, b}`) and `ψ̄_aψ_aψ̄_bψ_b`; these are **all** `U(1)`-invariant (charge `0`) elements of
`𝒩({a, b})` (`eq_proj0_of_ab`: `F = proj0 a b F` for `F ∈ 𝒩({a,b})`, `IsSym F`). In particular the
range does not depend on the base set: for every `X` meeting `{a, b}`,
`loc^{ab}_X F = F` for `U(1)`-invariant `F ∈ 𝒩({a,b})` (**`locABtX_repro`**), including `a = b`.

This is the "reproduction across base sets" needed for `EthSubLocAB` (`Obs2.Est.WObsAB2`): the
expectation `𝔼θ` maps `𝒩({a,b})` into itself and preserves `U(1)` invariance, so
`(1 - loc^{ab}_X)𝔼θ loc^{ab}_B G = 0` **exactly** (no `O(L^{-1})` remainder).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD

variable {d L N : ℕ} [NeZero L]

theorem abR_card_spin {n : ℕ} (z : Fin n → Sf (Lam d L N)) :
    (univ.filter fun i => (z i).2 = 1).card + (univ.filter fun i => (z i).2 = -1).card = n := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
    (fun i => (z i).2 = 1)
  rw [card_univ, Fintype.card_fin] at h
  have e : (univ.filter fun i => (z i).2 = -1) = univ.filter fun i => ¬(z i).2 = 1 := by
    ext i
    simp only [mem_filter, mem_univ, true_and]
    have hne : (-1 : ℤˣ) ≠ 1 := by decide
    rcases Int.units_eq_one_or (z i).2 with h1 | h1 <;> simp [h1, hne, hne.symm]
  rw [e]; exact h

/-- **Uniqueness on `𝒩({a,b})`**: a `U(1)`-invariant `H ∈ 𝒩({a,b})` with `ε(H) = 0`,
`H_{(u,-)(v,+)} = 0` (`u, v ∈ {a,b}`) and `H_{(a,-)(a,+)(b,-)(b,+)} = 0` vanishes. -/
theorem abR_eq_zero {a b : Lam d L N} {H : Alg d L N}
    (hN : H ∈ NX ({a, b} : Set (Lam d L N))) (hS : IsSym H) (h0 : ε H = 0)
    (h2 : ∀ u v : Lam d L N, (u = a ∨ u = b) → (v = a ∨ v = b) →
      coeff H ![(u, -1), (v, 1)] = 0)
    (h4 : coeff H ![(a, -1), (a, 1), (b, -1), (b, 1)] = 0) : H = 0 := by
  refine ext_coeff fun n z => ?_
  rw [coeff_zero]
  by_cases hinj : Function.Injective z
  swap
  · exact coeff_eq_zero_of_not_injective H hinj
  by_cases hout : ∃ i, (z i).1 ∉ ({a, b} : Set (Lam d L N))
  · obtain ⟨i, hi⟩ := hout
    exact coeff_eq_zero_of_mem_NX hN z i hi
  push Not at hout
  by_cases hc : (univ.filter fun i => (z i).2 = 1).card ≠
      (univ.filter fun i => (z i).2 = -1).card
  · exact hS n z hc
  push Not at hc
  have hn := abR_card_spin z
  set w4 : Fin 4 → Sf (Lam d L N) := ![(a, -1), (a, 1), (b, -1), (b, 1)] with hw4
  have hT : ∀ i, z i ∈ univ.image w4 := by
    intro i
    have h1 := hout i
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    rw [mem_image]
    rcases h1 with h1 | h1 <;> rcases Int.units_eq_one_or (z i).2 with h2 | h2
    · exact ⟨1, mem_univ _, Prod.ext (by simp [hw4, h1]) (by simp [hw4, h2])⟩
    · exact ⟨0, mem_univ _, Prod.ext (by simp [hw4, h1]) (by simp [hw4, h2])⟩
    · exact ⟨3, mem_univ _, Prod.ext (by simp [hw4, h1]) (by simp [hw4, h2])⟩
    · exact ⟨2, mem_univ _, Prod.ext (by simp [hw4, h1]) (by simp [hw4, h2])⟩
  have hcardT : (univ.image w4).card ≤ 4 := by
    refine card_image_le.trans ?_; simp
  have hnT : n ≤ (univ.image w4).card := by
    have := Finset.card_le_card_of_injOn z (s := (univ : Finset (Fin n)))
      (t := univ.image w4) (by intro i _; exact hT i) hinj.injOn
    simpa using this
  have hn4 : n ≤ 4 := hnT.trans hcardT
  interval_cases n
  · rw [coeff_fin_zero]; exact h0
  · omega
  · -- `n = 2`
    have hz : z = ![z 0, z 1] := by funext i; fin_cases i <;> rfl
    have hm := hout 0
    have hm' := hout 1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm hm'
    rcases Int.units_eq_one_or (z 0).2 with s0 | s0 <;>
      rcases Int.units_eq_one_or (z 1).2 with s1 | s1
    · exfalso
      have he : (univ.filter fun i => (z i).2 = -1) = ∅ := by
        rw [filter_eq_empty_iff]; intro i _
        fin_cases i
        · simp [s0]
        · simp [s1]
      rw [he, card_empty] at hc hn; omega
    · rw [hz]
      have e : (![z 0, z 1] : Fin 2 → Sf (Lam d L N)) = ![((z 0).1, 1), ((z 1).1, -1)] := by
        funext i; fin_cases i <;> simp [Prod.ext_iff, s0, s1]
      rw [e, coeff_swap_two, h2 _ _ hm' hm, neg_zero]
    · rw [hz]
      have e : (![z 0, z 1] : Fin 2 → Sf (Lam d L N)) = ![((z 0).1, -1), ((z 1).1, 1)] := by
        funext i; fin_cases i <;> simp [Prod.ext_iff, s0, s1]
      rw [e, h2 _ _ hm hm']
    · exfalso
      have he : (univ.filter fun i => (z i).2 = 1) = ∅ := by
        rw [filter_eq_empty_iff]; intro i _
        fin_cases i
        · simp [s0]
        · simp [s1]
      rw [he, card_empty] at hc hn; omega
  · omega
  · -- `n = 4`: `z` is a permutation of `w4`
    have hT4 : (univ.image w4).card = 4 := le_antisymm hcardT hnT
    have hwinj : Function.Injective w4 := by
      have h := (Finset.card_image_iff (s := (univ : Finset (Fin 4))) (f := w4)).1
        (by rw [hT4]; simp)
      intro x y hxy
      exact h (by simp) (by simp) hxy
    let T := {x // x ∈ univ.image w4}
    have hcT : Fintype.card T = 4 := by rw [Fintype.card_coe]; exact hT4
    let zf : Fin 4 → T := fun i => ⟨z i, hT i⟩
    let wf : Fin 4 → T := fun i => ⟨w4 i, mem_image_of_mem _ (mem_univ i)⟩
    have hzf : Function.Bijective zf :=
      (Fintype.bijective_iff_injective_and_card zf).2
        ⟨fun x y h => hinj (congrArg Subtype.val h), by rw [hcT]; simp⟩
    have hwf : Function.Bijective wf :=
      (Fintype.bijective_iff_injective_and_card wf).2
        ⟨fun x y h => hwinj (congrArg Subtype.val h), by rw [hcT]; simp⟩
    set σ : Equiv.Perm (Fin 4) :=
      (Equiv.ofBijective zf hzf).trans (Equiv.ofBijective wf hwf).symm with hσ
    have hcomp : w4 ∘ σ = z := by
      funext i
      have : wf (σ i) = zf i := by
        rw [hσ, Equiv.trans_apply]
        exact (Equiv.ofBijective wf hwf).apply_symm_apply _
      exact congrArg Subtype.val this
    rw [← hcomp, coeff_perm, h4, mul_zero]

/-! ### `proj0` on `𝒩({a,b})` -/

theorem abR_mem_pair {a b u : Lam d L N} (hu : u ∈ ({a, b} : Finset (Lam d L N))) :
    u ∈ ({a, b} : Set (Lam d L N)) := by
  rw [mem_insert, mem_singleton] at hu
  rcases hu with rfl | rfl <;> simp

theorem proj0_mem_NXab (a b : Lam d L N) (F : Alg d L N) :
    proj0 a b F ∈ NX ({a, b} : Set (Lam d L N)) := by
  unfold proj0 m4
  refine add_mem (add_mem (Subalgebra.algebraMap_mem _ _) (sum_mem fun u hu => sum_mem
    fun v hv => Subalgebra.smul_mem _ (mul_mem (psibar_mem_NX' (abR_mem_pair hu))
      (psi_mem_NX' (abR_mem_pair hv))) _)) (Subalgebra.smul_mem _ ?_ _)
  exact mul_mem (mul_mem (psibar_mem_NX' (by simp)) (psi_mem_NX' (by simp)))
    (mul_mem (psibar_mem_NX' (by simp)) (psi_mem_NX' (by simp)))

theorem proj0_mem_SymS (a b : Lam d L N) (F : Alg d L N) :
    proj0 a b F ∈ SymS (Lam d L N) := by
  unfold proj0 m4
  exact add_mem (add_mem (Subalgebra.algebraMap_mem _ _) (sum_mem fun u _ => sum_mem
    fun v _ => Subalgebra.smul_mem _ (pp_mem_SymS u v) _))
    (Subalgebra.smul_mem _ (mul_mem (pp_mem_SymS a a) (pp_mem_SymS b b)) _)

theorem eps_proj0 (a b : Lam d L N) (F : Alg d L N) : ε (proj0 a b F) = ε F := by
  simp only [proj0, map_add, map_sum, map_smul, AlgHom.commutes, m2, eps_m2, eps_m4,
    smul_zero, sum_const_zero, add_zero]
  rfl

theorem coeff_proj0_two (a b : Lam d L N) (F : Alg d L N) {x y : Lam d L N}
    (hx : x = a ∨ x = b) (hy : y = a ∨ y = b) :
    coeff (proj0 a b F) ![(x, -1), (y, 1)] = coeff F ![(x, -1), (y, 1)] := by
  have hx' : x ∈ ({a, b} : Finset (Lam d L N)) := by rcases hx with rfl | rfl <;> simp
  have hy' : y ∈ ({a, b} : Finset (Lam d L N)) := by rcases hy with rfl | rfl <;> simp
  have h4 : coeff (m4 a b) ![(x, -1), (y, 1)] = 0 := by
    rw [m4_eq_psiPow, psiPow]; exact coeff_ιMulti_of_ne _ _ (by decide)
  have h1 : coeff (algebraMap ℂ (Alg d L N) (ε F)) ![(x, -1), (y, 1)] = 0 := by
    rw [Algebra.algebraMap_eq_smul_one, coeff_smul, coeff_one_of_ne' _ (by decide), mul_zero]
  simp only [proj0, coeff_add, coeff_sum, coeff_smul, m2, coeff_psibar_psi_mp, h1, h4,
    mul_zero, add_zero, zero_add, mul_ite, mul_one]
  rw [sum_eq_single x, sum_eq_single y]
  · simp
  · intro v _ hv; simp [Ne.symm hv]
  · intro h; exact absurd hy' h
  · intro u _ hu
    refine sum_eq_zero fun v _ => ?_
    simp [Ne.symm hu]
  · intro h; exact absurd hx' h

theorem coeff_proj0_four (a b : Lam d L N) (F : Alg d L N) :
    coeff (proj0 a b F) ![(a, -1), (a, 1), (b, -1), (b, 1)] =
      coeff F ![(a, -1), (a, 1), (b, -1), (b, 1)] := by
  by_cases hab : a = b
  · subst hab
    have hni : ¬Function.Injective (![(a, -1), (a, 1), (a, -1), (a, 1)] : Fin 4 → Sf (Lam d L N)) :=
      fun hi => absurd (hi (a₁ := 0) (a₂ := 2) rfl) (by decide)
    rw [coeff_eq_zero_of_not_injective _ hni, coeff_eq_zero_of_not_injective _ hni]
  have h1 : coeff (algebraMap ℂ (Alg d L N) (ε F)) ![(a, -1), (a, 1), (b, -1), (b, 1)] = 0 := by
    rw [Algebra.algebraMap_eq_smul_one, coeff_smul, coeff_one_of_ne' _ (by decide), mul_zero]
  have h2 : ∀ u v : Lam d L N, coeff (m2 u v) ![(a, -1), (a, 1), (b, -1), (b, 1)] = 0 := by
    intro u v
    rw [m2, psibar_mul_psi_eq, psiPow]; exact coeff_ιMulti_of_ne _ _ (by decide)
  simp only [proj0, coeff_add, coeff_sum, coeff_smul, h1, h2, mul_zero, sum_const_zero,
    zero_add]
  rw [m4_eq_psiPow, coeff_psiPow_self _ (injective_m4 hab), mul_one]

theorem abR_coeff_sub (F G : Alg d L N) {n : ℕ} (z : Fin n → Sf (Lam d L N)) :
    coeff (F - G) z = coeff F z - coeff G z := by
  rw [sub_eq_add_neg, coeff_add, show -G = (-1 : ℂ) • G by simp, coeff_smul]; ring

/-- **The `U(1)`-invariant elements of `𝒩({a,b})` are spanned by `1`, `ψ̄_uψ_v`,
`ψ̄_aψ_aψ̄_bψ_b`**: `F = proj0 a b F`. -/
theorem eq_proj0_of_ab {a b : Lam d L N} {F : Alg d L N}
    (hN : F ∈ NX ({a, b} : Set (Lam d L N))) (hS : IsSym F) : F = proj0 a b F := by
  rw [← sub_eq_zero]
  refine abR_eq_zero (a := a) (b := b) (sub_mem hN (proj0_mem_NXab a b F)) ?_ ?_ ?_ ?_
  · rw [isSym_iff_mem_SymS]
    exact sub_mem ((isSym_iff_mem_SymS F).1 hS) (proj0_mem_SymS a b F)
  · rw [map_sub, eps_proj0, sub_self]
  · intro u v hu hv
    rw [abR_coeff_sub, coeff_proj0_two a b F hu hv, sub_self]
  · rw [abR_coeff_sub, coeff_proj0_four, sub_self]

/-! ### Reproduction -/

theorem locABtX_self_eq (X : Finset (Lam d L N)) (a : Lam d L N) (F : Alg d L N) :
    locABtX X a a F = locABt X a a F := by
  unfold locABtX; split_ifs <;> rfl

theorem locABtX_m2' {X : Finset (Lam d L N)} {a b : Lam d L N} (h : a ∈ X ∨ b ∈ X)
    {u v : Lam d L N} (hu : u = a ∨ u = b) (hv : v = a ∨ v = b) :
    locABtX X a b (m2 u v) = m2 u v := by
  by_cases hab : a = b
  · subst hab
    have ha : a ∈ X := h.elim id id
    have hu' : u = a := hu.elim id id
    have hv' : v = a := hv.elim id id
    subst hu' hv'
    rw [locABtX_self_eq, locABt, locEven_singleton_eq ha, m2, eps_m2, mass2_m2]
    simp [Dt, dbar, dlt, pbp]
  · rw [m2]; exact locABtX_m2 h hab hu hv

/-- **`loc^{ab}_X` reproduces the `U(1)`-invariant elements of `𝒩({a,b})`** (any `X` meeting
`{a,b}`; `a = b` allowed). -/
theorem locABtX_repro {X : Finset (Lam d L N)} {a b : Lam d L N} (h : a ∈ X ∨ b ∈ X)
    {F : Alg d L N} (hN : F ∈ NX ({a, b} : Set (Lam d L N))) (hS : IsSym F) :
    locABtX X a b F = F := by
  have e := eq_proj0_of_ab hN hS
  rw [e]
  have h4 : locABtX X a b (coeff F ![(a, -1), (a, 1), (b, -1), (b, 1)] • m4 a b) =
      coeff F ![(a, -1), (a, 1), (b, -1), (b, 1)] • m4 a b := by
    by_cases hab : a = b
    · subst hab
      have hni : ¬Function.Injective
          (![(a, -1), (a, 1), (a, -1), (a, 1)] : Fin 4 → Sf (Lam d L N)) :=
        fun hi => absurd (hi (a₁ := 0) (a₂ := 2) rfl) (by decide)
      rw [coeff_eq_zero_of_not_injective _ hni, zero_smul, ← zero_smul ℂ (0 : Alg d L N),
        locABtX_smul, zero_smul, zero_smul]
    · rw [locABtX_smul, locABtX_m4 h hab]
  have hsum : ∀ (s : Finset (Lam d L N)) (f : Lam d L N → Alg d L N),
      locABtX X a b (∑ u ∈ s, f u) = ∑ u ∈ s, locABtX X a b (f u) := by
    intro s f
    induction s using Finset.induction_on with
    | empty =>
      rw [sum_empty, sum_empty, ← zero_smul ℂ (0 : Alg d L N), locABtX_smul, zero_smul, zero_smul]
    | insert x s hx ih => rw [sum_insert hx, sum_insert hx, locABtX_add, ih]
  unfold proj0
  rw [locABtX_add, locABtX_add, h4, locABtX_algebraMap h, hsum]
  congr 2
  refine sum_congr rfl fun u hu => ?_
  rw [hsum]
  refine sum_congr rfl fun v hv => ?_
  rw [locABtX_smul, locABtX_m2' h (by simpa using hu) (by simpa using hv)]

end

end Obs2
