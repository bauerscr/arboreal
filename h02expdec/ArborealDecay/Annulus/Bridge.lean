module

public import ArborealDecay.Annulus.Integr
public import ArborealDecay.Annulus.MMatrix
public import ArborealDecay.Annulus.MapW
public import ArborealDecay.Conductance
public import ArborealDecay.CondComb

/-!
# The split network of `Γ = G/(a=b)` (setting of `prop:conductance-identity`)

`G = (V, β)` with terminals `a ≠ b`; `Γ = gammaW β a b` on `GamV V a b = Option (V ∖ {a,b})`,
with `none = ρ`.  For a pinned field `τ` on `Γ`, `U_v = e^{t_{col v}}` (`col = collapse {a,b}`),
so that `U_a = U_b = 1`; `condK β a b τ` is the effective conductance between `a` and `b` in `G`
with conductances `β_{ij} U_i U_j` (variational definition `Conductance.effCond`).

* `condHmat_eq`: the note's `H` (`Conductance.Hmat`, rescaled) is the pinned `H^ρ_Γ(t)` of
  `TLaw` (reindexed by `eI : V ∖ {a,b} ≃ Γ ∖ ρ`).
* `condK_eq` (eq:K-Schur): `K = β_ab + ∑_{i,j ∈ I} β_ai (H^ρ_Γ)⁻¹_{ij} β_jb`.
* `condK_le`: `0 ≤ K ≤ ∑_v β_av U_v` (Dirichlet bound with the indicator of `a`).
-/

open Matrix Real MeasureTheory

set_option linter.unusedSectionVars false

@[expose] public section

namespace ArborealDecay.Annulus

open ArborealDecay.TLaw ArborealDecay.Surgery ArborealDecay.Wiring ArborealDecay.CondComb

variable {V : Type*} [Fintype V] [DecidableEq V] {a b : V}

/-- The collapse `V → Γ`, `a, b ↦ ρ = none`. -/
abbrev colAB (a b : V) : V → GamV V a b := collapse ({a, b} : Finset V)

theorem notMem_pair_of_interior (i : Conductance.Interior a b) :
    i.1 ∉ ({a, b} : Finset V) := by
  simp [i.2.1, i.2.2]

/-- `V ∖ {a,b} ≃ Γ ∖ {ρ}`. -/
def eI (a b : V) : Conductance.Interior a b ≃ {x : GamV V a b // x ≠ none} where
  toFun i := ⟨some ⟨i.1, notMem_pair_of_interior i⟩, Option.some_ne_none _⟩
  invFun x := ⟨(x.1.get (Option.ne_none_iff_isSome.1 x.2)).1, by
    have h := (x.1.get (Option.ne_none_iff_isSome.1 x.2)).2
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h
    exact h⟩
  left_inv i := by simp
  right_inv x := by
    obtain ⟨x, hx⟩ := x
    cases x with
    | none => exact absurd rfl hx
    | some u => simp

theorem colAB_interior (i : Conductance.Interior a b) : colAB a b i.1 = (eI a b i).1 :=
  collapse_of_notMem (notMem_pair_of_interior i)

theorem colAB_a : colAB a b a = none := collapse_of_mem (by simp)

theorem colAB_b : colAB a b b = none := collapse_of_mem (by simp)

/-- `U_v = e^{t_{col v}}` (so `U_a = U_b = 1`). -/
noncomputable def Ufield (τ : {x : GamV V a b // x ≠ none} → ℝ) (v : V) : ℝ :=
  exp (TLaw.ext none τ (colAB a b v))

/-- `U` on the interior vertices. -/
noncomputable def Uint (τ : {x : GamV V a b // x ≠ none} → ℝ) : Conductance.Interior a b → ℝ :=
  fun i => Ufield τ i.1

/-- The effective conductance `K(t)` between `a` and `b` with conductances `β_{ij} U_i U_j`. -/
noncomputable def condK (β : V → V → ℝ) (a b : V) (τ : {x : GamV V a b // x ≠ none} → ℝ) : ℝ :=
  Conductance.effCond (Conductance.rescaled β (Uint τ)) a b

theorem Ufield_pos (τ : {x : GamV V a b // x ≠ none} → ℝ) (v : V) : 0 < Ufield τ v := exp_pos _

theorem Ufield_a (τ : {x : GamV V a b // x ≠ none} → ℝ) : Ufield τ a = 1 := by
  simp [Ufield, colAB_a]

theorem Ufield_b (τ : {x : GamV V a b // x ≠ none} → ℝ) : Ufield τ b = 1 := by
  simp [Ufield, colAB_b]

theorem glue_Uint (τ : {x : GamV V a b // x ≠ none} → ℝ) (v : V) :
    Conductance.glue a b 1 1 (Uint τ) v = Ufield τ v := by
  unfold Conductance.glue
  split_ifs with h h'
  · rfl
  · rw [h', Ufield_a]
  · have : v = b := by tauto
    rw [this, Ufield_b]

theorem rescaled_Uint (β : V → V → ℝ) (τ : {x : GamV V a b // x ≠ none} → ℝ) :
    Conductance.rescaled β (Uint τ) = fun u v => β u v * Ufield τ u * Ufield τ v := by
  funext u v
  simp only [Conductance.rescaled, glue_Uint]

theorem isWGraph_gammaW {β : V → V → ℝ} (hβ : IsWGraph β) (a b : V) : IsWGraph (gammaW β a b) :=
  isWGraph_mapW hβ.symm hβ.nonneg _

theorem fib_colAB (i : Conductance.Interior a b) :
    (Finset.univ.filter fun u => colAB a b u = (eI a b i).1) = {i.1} := by
  ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h
    by_cases hu : u ∈ ({a, b} : Finset V)
    · rw [colAB, collapse_of_mem hu] at h; exact absurd h (by simp [eI])
    · rw [colAB, collapse_of_notMem hu] at h
      simp only [eI, Equiv.coe_fn_mk, Option.some.injEq] at h
      exact congrArg Subtype.val h
  · rintro rfl; exact colAB_interior i

theorem colAB_eq_iff (i : Conductance.Interior a b) (v : V) :
    colAB a b v = (eI a b i).1 ↔ v = i.1 := by
  have := fib_colAB i
  rw [Finset.ext_iff] at this
  simpa using this v

/-- The note's rescaled `H` (`Conductance.Hmat`) is the pinned `H^ρ_Γ(t)`. -/
theorem condHmat_eq (β : V → V → ℝ) (τ : {x : GamV V a b // x ≠ none} → ℝ) :
    Conductance.Hmat β a b (Uint τ) =
      (TLaw.Hmat (gammaW β a b) none (TLaw.ext none τ)).submatrix (eI a b) (eI a b) := by
  ext i j
  simp only [Conductance.Hmat, diagonal_mul, mul_diagonal, Conductance.lapII, submatrix_apply,
    TLaw.Hmat, of_apply, rescaled_Uint]
  by_cases hij : i = j
  · subst hij
    simp only [MatrixForest.lap_apply_self, ite_true]
    rw [gammaW, sum_mapW_row, fib_colAB, Finset.sum_singleton]
    have hUi : Uint τ i = exp (TLaw.ext none τ (eI a b i).1) := by
      simp [Uint, Ufield, colAB_interior]
    rw [hUi]
    have e1 : ∀ v, (if colAB a b v = (eI a b i).1 then (0 : ℝ) else
        β i.1 v * exp (TLaw.ext none τ (colAB a b v) - TLaw.ext none τ (eI a b i).1)) =
        if v = i.1 then 0 else β i.1 v * Ufield τ v * (exp (TLaw.ext none τ (eI a b i).1))⁻¹ := by
      intro v
      simp only [colAB_eq_iff i v]
      split_ifs
      · rfl
      · rw [exp_sub]; simp only [Ufield, div_eq_mul_inv]; ring_nf
    simp only [e1]
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.mul_sum, Finset.sum_mul]
    have hf : Finset.univ.filter (fun v => ¬ v = i.1) = Finset.univ.erase i.1 := by
      ext v; simp
    rw [hf]
    refine Finset.sum_congr rfl fun v _ => ?_
    have hU : Ufield τ i.1 = exp (TLaw.ext none τ (eI a b i).1) := by
      simp [Ufield, colAB_interior]
    rw [hU]
    have := (exp_pos (TLaw.ext none τ (eI a b i).1)).ne'
    field_simp
  · have hij' : eI a b i ≠ eI a b j := fun h => hij ((eI a b).injective h)
    simp only [hij', ite_false]
    rw [MatrixForest.lap_apply_of_ne _ (fun h => hij (Subtype.ext h))]
    have hs : (⟨i.1, notMem_pair_of_interior i⟩ : {v // v ∉ ({a, b} : Finset V)}) ≠
        ⟨j.1, notMem_pair_of_interior j⟩ := fun h => hij (Subtype.ext (Subtype.mk.inj h))
    have := mapW_some_some (β := β) _ _ hs
    simp only [gammaW, eI, Equiv.coe_fn_mk]
    rw [this]
    have h1 := (Ufield_pos τ i.1).ne'
    have h2 := (Ufield_pos τ j.1).ne'
    simp only [Uint]
    field_simp

theorem condHmat_posDef {β : V → V → ℝ} (hβ : IsWGraph β)
    (hconn : (supportGraph (gammaW β a b)).Connected) (τ : {x : GamV V a b // x ≠ none} → ℝ) :
    (Conductance.Hmat β a b (Uint τ)).PosDef := by
  rw [condHmat_eq β]
  exact (Hmat_posDef (isWGraph_gammaW hβ a b) hconn none _).submatrix (eI a b).injective

theorem lapII_posDef {β : V → V → ℝ} (hβ : IsWGraph β)
    (hconn : (supportGraph (gammaW β a b)).Connected) (τ : {x : GamV V a b // x ≠ none} → ℝ) :
    (Conductance.lapII (Conductance.rescaled β (Uint τ)) a b).PosDef := by
  have hU : ∀ i, Uint τ i ≠ 0 := fun i => (Ufield_pos τ i.1).ne'
  have e : Conductance.lapII (Conductance.rescaled β (Uint τ)) a b =
      (diagonal (Uint τ))ᴴ * Conductance.Hmat β a b (Uint τ) * diagonal (Uint τ) := by
    rw [diagonal_conjTranspose, star_trivial, Conductance.Hmat]
    simp only [← Matrix.mul_assoc, diagonal_mul_diagonal]
    rw [Matrix.mul_assoc, diagonal_mul_diagonal]
    have h1 : (fun i => Uint τ i * (Uint τ i)⁻¹) = fun _ => (1 : ℝ) := by
      funext i; exact mul_inv_cancel₀ (hU i)
    have h2 : (fun i => (Uint τ i)⁻¹ * Uint τ i) = fun _ => (1 : ℝ) := by
      funext i; exact inv_mul_cancel₀ (hU i)
    rw [h1, h2, diagonal_one, Matrix.one_mul, Matrix.mul_one]
  rw [e]
  refine (condHmat_posDef hβ hconn τ).conjTranspose_mul_mul_same ?_
  intro x y hxy
  funext i
  have := congr_fun hxy i
  simp only [mulVec_diagonal] at this
  exact mul_left_cancel₀ (hU i) this

/-- The pinned Green function `X_{pq}(τ) = (H^ρ_Γ(τ̂))⁻¹_{pq}`. -/
noncomputable def greenX (w : GamV V a b → GamV V a b → ℝ) (τ : {x : GamV V a b // x ≠ none} → ℝ)
    (p q : {x : GamV V a b // x ≠ none}) : ℝ :=
  (TLaw.Hmat w none (TLaw.ext none τ))⁻¹ p q

/-- **eq:K-Schur** for the pinned field: `K = β_ab + ∑_{i,j ∈ I} β_ai X_{ij} β_jb`. -/
theorem condK_eq {β : V → V → ℝ} (hβ : IsWGraph β) (hab : a ≠ b)
    (hconn : (supportGraph (gammaW β a b)).Connected) (τ : {x : GamV V a b // x ≠ none} → ℝ) :
    condK β a b τ = β a b + ∑ i : Conductance.Interior a b, ∑ j : Conductance.Interior a b,
      β a i.1 * greenX (gammaW β a b) τ (eI a b i) (eI a b j) * β j.1 b := by
  rw [condK, Conductance.effCond_rescaled hab hβ.symm hβ.nonneg
    (U := Uint τ) (fun i => Ufield_pos τ i.1) (lapII_posDef hβ hconn τ), condHmat_eq β,
    inv_submatrix_equiv]
  congr 1
  simp only [dotProduct, mulVec, Finset.mul_sum, submatrix_apply, Conductance.wFromA,
    Conductance.wToB, greenX]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem greenX_nonneg {w : GamV V a b → GamV V a b → ℝ} (hW : IsWGraph w)
    (hconn : (supportGraph w).Connected) (τ : {x : GamV V a b // x ≠ none} → ℝ)
    (p q : {x : GamV V a b // x ≠ none}) : 0 ≤ greenX w τ p q := by
  refine inv_apply_nonneg_of_posDef (Hmat_posDef hW hconn none _) (fun i j hij => ?_) p q
  simp only [TLaw.Hmat, of_apply, hij, ite_false]
  exact neg_nonpos.2 (hW.nonneg _ _)

theorem measurable_greenX (w : GamV V a b → GamV V a b → ℝ) (p q : {x : GamV V a b // x ≠ none}) :
    Measurable fun τ => greenX w τ p q := by
  have hH : Continuous fun τ : {x : GamV V a b // x ≠ none} → ℝ =>
      TLaw.Hmat w none (TLaw.ext none τ) := by
    refine continuous_matrix fun i k => ?_
    simp only [TLaw.Hmat, of_apply]
    split_ifs
    · exact continuous_finsetSum _ fun m _ => continuous_const.mul
        (continuous_exp.comp ((continuous_ext_apply none m).sub
          (continuous_ext_apply none (i : GamV V a b))))
    · exact continuous_const
  simp only [greenX, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact (hH.matrix_det.measurable.inv).mul
    (((continuous_apply q).comp ((continuous_apply p).comp hH.matrix_adjugate)).measurable)

/-- Dirichlet bound with the indicator of `a`: `0 ≤ K ≤ ∑_v β_av U_v`. -/
theorem condK_le {β : V → V → ℝ} (hβ : IsWGraph β) (hab : a ≠ b)
    (τ : {x : GamV V a b // x ≠ none} → ℝ) :
    0 ≤ condK β a b τ ∧ condK β a b τ ≤ ∑ v, β a v * Ufield τ v := by
  have hc : ∀ i j, 0 ≤ Conductance.rescaled β (Uint τ) i j := fun i j => by
    rw [rescaled_Uint]
    exact mul_nonneg (mul_nonneg (hβ.nonneg i j) (Ufield_pos τ i).le) (Ufield_pos τ j).le
  set δ : V → ℝ := fun v => if v = a then 1 else 0
  have hadm : Conductance.Admissible a b δ := ⟨by simp [δ], by simp [δ, hab.symm]⟩
  refine ⟨?_, (Conductance.effCond_le_energy hc hadm).trans ?_⟩
  · have : Nonempty {v // Conductance.Admissible a b v} := ⟨⟨δ, hadm⟩⟩
    unfold condK Conductance.effCond
    refine le_ciInf fun v => ?_
    rw [Conductance.energy_eq_form]; exact Conductance.energyForm_nonneg hc _
  · rw [rescaled_Uint] at hc ⊢
    unfold Conductance.energy
    have hpt : ∀ i j, β i j * Ufield τ i * Ufield τ j * (δ i - δ j) ^ 2 ≤
        (if i = a then β i j * Ufield τ i * Ufield τ j else 0) +
          (if j = a then β i j * Ufield τ i * Ufield τ j else 0) := by
      intro i j
      have h0 := hc i j
      simp only [δ]
      split_ifs <;> simp [h0]
    calc (1 / 2) * ∑ i, ∑ j, β i j * Ufield τ i * Ufield τ j * (δ i - δ j) ^ 2
        ≤ (1 / 2) * ∑ i, ∑ j, ((if i = a then β i j * Ufield τ i * Ufield τ j else 0) +
          (if j = a then β i j * Ufield τ i * Ufield τ j else 0)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
            hpt i j) (by norm_num)
      _ = ∑ v, β a v * Ufield τ v := by
          set X : V → V → ℝ := fun i j => β i j * Ufield τ i * Ufield τ j
          have hA : ∑ i, ∑ j, (if i = a then X i j else 0) = ∑ j, X a j := by
            rw [Fintype.sum_eq_single a (fun i hi => by simp [hi])]
            simp
          have hB : ∑ i, ∑ j, (if j = a then X i j else 0) = ∑ i, X i a := by
            simp
          simp only [Finset.sum_add_distrib]
          rw [hA, hB]
          have : ∀ v, X v a = X a v := fun v => by simp only [X]; rw [hβ.symm]; ring
          simp only [this, X, Ufield_a]
          ring_nf

end ArborealDecay.Annulus
