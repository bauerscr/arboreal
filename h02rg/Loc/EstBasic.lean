import Loc.EstDefs

/-!
# Basic properties of the pairing and of the `T` norm

* the `T` norm is a seminorm: `tNorm_add_le`, `tNorm_smul_le`, `tNorm_sum_le`, `tNorm_neg`;
* `‖1‖_T ≤ 1` and `‖F_∅‖ ≤ ‖F‖_T`;
* coefficients of `F ∈ 𝒩(A)` vanish on sequences leaving `A`;
* `⟨F, A g⟩ = ⟨F, g⟩` for the antisymmetrisation `A`;
* pairings with `single` and `restr`.
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD Equiv ENNReal

variable {X : Type*} [DecidableEq X] [Fintype X] {E : Type*} [Fintype E] [DecidableEq E]
  [AddAction (E → ℕ) X] {p : ℕ} {h ℓ : ℝ}

theorem pair_single' (F : N X) (m : ℕ) (f : (Fin m → Sf X) → ℂ) :
    pair F (single m f) = (m.factorial : ℂ)⁻¹ * ∑ z, coeff F z * f z := by
  unfold pair
  by_cases hm : m ≤ Nf X
  · rw [sum_eq_single_of_mem m (mem_range.2 (by omega)), single_self]
    intro n _ hn
    rw [single_ne f hn]
    simp
  · rw [sum_eq_zero fun n hn => by
      rw [single_ne f (by have := mem_range.1 hn; omega)]; simp]
    rw [sum_eq_zero fun z _ => by rw [coeff_eq_zero_of_lt F z (by omega), zero_mul], mul_zero]

theorem phiNorm_single_le' {m : ℕ} {f : (Fin m → Sf X) → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ (z : Fin m → Sf X) (α : Fin m → E → ℕ), (∀ i, Grassmann.mabs (α i) ≤ p) →
      ℓ⁻¹ ^ m * h ^ ord α * ‖nab α f z‖ ≤ M) :
    phiNorm E p h ℓ (single m f) ≤ ENNReal.ofReal M := by
  refine phiNorm_le fun n z α hα => ?_
  by_cases hn : n = m
  · subst hn
    unfold phiTerm
    rw [single_self]
    exact hf z α hα
  · unfold phiTerm
    rw [single_ne f hn, map_zero]
    simpa using hM

theorem tNorm_add_le (F G : N X) :
    tNorm E p h ℓ (F + G) ≤ tNorm E p h ℓ F + tNorm E p h ℓ G := by
  refine iSup₂_le fun g hg => ?_
  rw [pair_add]
  calc ENNReal.ofReal ‖pair F g + pair G g‖ ≤ ENNReal.ofReal (‖pair F g‖ + ‖pair G g‖) :=
        ENNReal.ofReal_le_ofReal (norm_add_le _ _)
    _ ≤ ENNReal.ofReal ‖pair F g‖ + ENNReal.ofReal ‖pair G g‖ := ENNReal.ofReal_add_le
    _ ≤ _ := add_le_add (le_tNorm F hg) (le_tNorm G hg)

theorem tNorm_smul_le (c : ℂ) (F : N X) :
    tNorm E p h ℓ (c • F) ≤ ENNReal.ofReal ‖c‖ * tNorm E p h ℓ F := by
  refine iSup₂_le fun g hg => ?_
  rw [pair_smul, norm_mul, ENNReal.ofReal_mul (norm_nonneg _)]
  gcongr
  exact le_tNorm F hg

theorem tNorm_neg (F : N X) : tNorm E p h ℓ (-F) = tNorm E p h ℓ F := by
  have key : ∀ G : N X, tNorm E p h ℓ (-G) ≤ tNorm E p h ℓ G := fun G => by
    simpa using tNorm_smul_le (E := E) (p := p) (h := h) (ℓ := ℓ) (-1) G
  exact le_antisymm (key F) (by simpa using key (-F))

theorem tNorm_sub_le (F G : N X) :
    tNorm E p h ℓ (F - G) ≤ tNorm E p h ℓ F + tNorm E p h ℓ G := by
  rw [sub_eq_add_neg]
  exact (tNorm_add_le F (-G)).trans (by rw [tNorm_neg])

theorem tNorm_sum_le {ι : Type*} (s : Finset ι) (F : ι → N X) :
    tNorm E p h ℓ (∑ i ∈ s, F i) ≤ ∑ i ∈ s, tNorm E p h ℓ (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [sum_empty, sum_empty]
    refine iSup₂_le fun g _ => ?_
    rw [show pair (0 : N X) g = 0 from map_zero (pairL g)]
    simp
  | insert i s hi ih =>
    rw [sum_insert hi, sum_insert hi]
    exact (tNorm_add_le _ _).trans (add_le_add le_rfl ih)

theorem tNorm_one_le (hh : 0 < h) (hℓ : 0 < ℓ) : tNorm E p h ℓ (1 : N X) ≤ 1 := by
  rw [← ENNReal.ofReal_one]
  refine tNorm_le fun g hg => ?_
  have h1 : (1 : N X) = psiPow (Fin.elim0 : Fin 0 → Sf X) := by
    simp [psiPow, ExteriorAlgebra.ιMulti_zero_apply]
  rw [h1, pair_psiPow]
  have h2 : asym g 0 (Fin.elim0 : Fin 0 → Sf X) = g 0 Fin.elim0 := by
    simp [asym]
  rw [h2]
  simpa using abs_le_of_phiNorm_le hh hℓ zero_le_one (by rwa [ENNReal.ofReal_one]) (g := g)
    (Fin.elim0 : Fin 0 → Sf X)

/-- `‖F_∅‖ ≤ ‖F‖_T`. -/
theorem abs_eps_le (hh : 0 < h) (hℓ : 0 < ℓ) (F : N X) : ‖ε F‖ ≤ (tNorm E p h ℓ F).toReal := by
  have hg : phiNorm E p h ℓ (single 0 (fun _ => (1 : ℂ)) : TestFn X) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    refine phiNorm_single_le' zero_le_one fun z α _ => ?_
    have hα : α = 0 := Subsingleton.elim _ _
    subst hα
    rw [nabla_zero _ (by simp)]
    simp [ord, Grassmann.mabs]
  have := le_tNorm (p := p) (h := h) (ℓ := ℓ) F hg
  rw [pair_single'] at this
  have e : (Nat.factorial 0 : ℂ)⁻¹ * ∑ z : Fin 0 → Sf X, coeff F z * 1 = ε F := by
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_mul, mul_one]
    rw [Fintype.sum_unique]
    rfl
  rw [e] at this
  exact (ENNReal.ofReal_le_iff_le_toReal (tNorm_ne_top hh hℓ F)).1 this

/-- The coefficients of `F ∈ 𝒩(A)` vanish on sequences with an entry outside `A`. -/
theorem coeff_eq_zero_of_mem_NX {A : Set X} {F : N X} (hF : F ∈ NX A) {n : ℕ}
    (z : Fin n → Sf X) (i : Fin n) (hi : (z i).1 ∉ A) : coeff F z = 0 := by
  have h0 : ∀ {k : ℕ} (w : Fin (k + 1) → Sf X), (w 0).1 ∉ A → coeff F w = 0 := by
    intro k w hw
    show ε (contr (fun i => coord (w i)) F) = 0
    rw [contr_succ]
    show ε (contr _ (D (w 0) F)) = 0
    rw [D_eq_zero_of_mem_NX hF hw, map_zero, map_zero]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by have := i.pos; omega⟩
  have hp := coeff_perm F z (Equiv.swap 0 i)
  rw [h0 _ (by simpa using hi)] at hp
  have hs : (Perm.sign (Equiv.swap (0 : Fin (k + 1)) i) : ℂ) ≠ 0 := by
    rcases Int.units_eq_one_or (Perm.sign (Equiv.swap (0 : Fin (k + 1)) i)) with hs | hs <;>
      simp [hs]
  exact (mul_eq_zero.1 hp.symm).resolve_left hs

theorem asym_perm (g : TestFn X) {n : ℕ} (z : Fin n → Sf X) (σ : Perm (Fin n)) :
    asym g n (z ∘ σ) = (Perm.sign σ : ℂ) * asym g n z := by
  have hs : (Perm.sign σ : ℂ) * Perm.sign σ = 1 := by
    rcases Int.units_eq_one_or (Perm.sign σ) with h | h <;> simp [h]
  simp only [asym]
  rw [mul_left_comm]
  congr 1
  rw [mul_sum]
  apply Fintype.sum_equiv (Equiv.mulLeft σ)
  intro τ
  simp only [Equiv.coe_mulLeft, Perm.sign_mul, Perm.coe_mul, Units.val_mul, Int.cast_mul]
  rw [Function.comp_assoc]
  linear_combination (-(Perm.sign τ : ℂ) * g n (z ∘ (σ ∘ τ))) * hs

theorem pair_asym (F : N X) (g : TestFn X) : pair F (asym g) = pair F g := by
  unfold pair
  refine sum_congr rfl fun n _ => congr_arg _ ?_
  simp only [asym, mul_sum]
  rw [sum_comm]
  have key : ∀ σ : Perm (Fin n), ∑ z : Fin n → Sf X,
      coeff F z * ((n.factorial : ℂ)⁻¹ * ((Perm.sign σ : ℂ) * g n (z ∘ σ))) =
      (n.factorial : ℂ)⁻¹ * ∑ z : Fin n → Sf X, coeff F z * g n z := by
    intro σ
    have hs : (Perm.sign σ : ℂ) * Perm.sign σ = 1 := by
      rcases Int.units_eq_one_or (Perm.sign σ) with h | h <;> simp [h]
    rw [mul_sum]
    let e : (Fin n → Sf X) ≃ (Fin n → Sf X) :=
      { toFun := fun z => z ∘ σ, invFun := fun w => w ∘ σ.symm,
        left_inv := fun z => by ext i <;> simp,
        right_inv := fun w => by ext i <;> simp }
    refine Fintype.sum_equiv e _ _ fun z => ?_
    simp only [e, Equiv.coe_fn_mk]
    rw [coeff_perm]
    ring
  rw [sum_congr rfl fun σ _ => key σ, sum_const, card_univ, Fintype.card_perm,
    Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)), one_mul]

theorem pair_single (F : N X) (m : ℕ) (f : (Fin m → Sf X) → ℂ) :
    pair F (single m f) = (m.factorial : ℂ)⁻¹ * ∑ z, coeff F z * f z := by
  exact pair_single' F m f

theorem phiNorm_single_le {m : ℕ} {f : (Fin m → Sf X) → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ (z : Fin m → Sf X) (α : Fin m → E → ℕ), (∀ i, mabs (α i) ≤ p) →
      ℓ⁻¹ ^ m * h ^ ord α * ‖nab α f z‖ ≤ M) :
    phiNorm E p h ℓ (single m f) ≤ ENNReal.ofReal M := by
  exact phiNorm_single_le' hM hf

theorem pair_restr_add (F : N X) (P : ℕ → Prop) [DecidablePred P] (g : TestFn X) :
    pair F g = pair F (restr P g) + pair F (restr (fun n => ¬ P n) g) := by
  have hg : g = restr P g + restr (fun n => ¬ P n) g := by
    funext n z
    simp only [restr, Pi.add_apply]
    split_ifs <;> simp
  conv_lhs => rw [hg]
  exact (pairR F).map_add _ _

theorem pair_restr_eq_single (F : N X) (m : ℕ) (g : TestFn X) :
    pair F (restr (fun n => n = m) g) = pair F (single m (g m)) := by
  congr 1
  funext n z
  simp only [restr, single]
  split_ifs with hn
  · subst hn; rfl
  · rfl

theorem phiNorm_restr_le (P : ℕ → Prop) [DecidablePred P] (g : TestFn X) :
    phiNorm E p h ℓ (restr P g) ≤ phiNorm E p h ℓ g := by
  refine iSup_le fun n => iSup_le fun z => iSup_le fun α => iSup_le fun hα => ?_
  by_cases hP : P n
  · have : restr P g n = g n := funext fun _ => if_pos hP
    unfold phiTerm; rw [this]
    exact phiTerm_le g z α hα
  · have : restr P g n = 0 := funext fun _ => if_neg hP
    unfold phiTerm; rw [this, map_zero]
    simp

end

end Loc
