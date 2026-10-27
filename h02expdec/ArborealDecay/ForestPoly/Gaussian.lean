module

public import ArborealDecay.H02.Main
public import ArborealDecay.Grassmann.Algebra

/-!
# The fermionic Gaussian integral in the `H02` Grassmann algebra

This file proves the fermionic Gaussian identity `∫ d(ξ, η) exp(ξᵀ M η) = det M`
(BCHS, Lemma 2.11, (2.74)) for the Grassmann algebra of the ported `H02` library, and its
version for the hyperbolic fermionic integral `H02.int0`, which carries the extra factor
`∏ᵢ (1 + ξᵢ ηᵢ) = exp(∑ᵢ ξᵢ ηᵢ)`:
`[exp(ξᵀ M η)]_0 = det (M + 1)`.

The proof writes `exp(ξᵀ M η) = ∏ᵢ (1 + ξᵢ ι(vᵢ))` with `vᵢ = ∑ⱼ Mᵢⱼ ηⱼ`, expands the product,
and evaluates each term with `Grassmann.algebraMapInv_contr_ιMulti` (the constant term of an
iterated contraction of a product of generators is a determinant).
-/

@[expose] public section

namespace ArborealDecay.ForestPoly

noncomputable section

set_option linter.unusedSectionVars false

open H02 CliffordAlgebra Finset

variable {Λ : Type*} [DecidableEq Λ]

local notation "A" => H02.Grassmann Λ

/-! ### The plain Berezin integral -/

/-- One step `∂_{η_i} ∂_{ξ_i}` of the plain Berezin integral. -/
def pStep (i : Λ) : A →ₗ[ℝ] A := dη i ∘ₗ dξ i

/-- The plain Berezin integral `∏_{i ∈ l} ∂_{η_i} ∂_{ξ_i}` (head of `l` applied first). -/
def pBer : List Λ → A →ₗ[ℝ] A
  | [] => LinearMap.id
  | i :: l => pBer l ∘ₗ pStep i

/-- The weight `∏_{i ∈ l} (1 + ξ_i η_i)` of the hyperbolic integral. -/
def wProd (l : List Λ) : A := (l.map fun i => 1 + ξ i * η i).prod

theorem isFree_wProd {v : Λ} {l : List Λ} (hv : v ∉ l) : IsFree v (wProd l) := by
  induction l with
  | nil => simpa [wProd] using isFree_algebraMap v 1
  | cons a l ih =>
    rw [List.mem_cons, not_or] at hv
    simp only [wProd, List.map_cons, List.prod_cons]
    exact (isFree_w (Ne.symm hv.1)).mul (ih hv.2)

/-- The hyperbolic integral is the plain integral of `∏ᵢ (1 + ξᵢ ηᵢ) F`. -/
theorem berezin_eq_pBer {l : List Λ} (hl : l.Nodup) (F : A) :
    berezin l F = pBer l (wProd l * F) := by
  induction l generalizing F with
  | nil => simp [pBer, wProd]
  | cons i l ih =>
    rw [List.nodup_cons] at hl
    have hfree := isFree_wProd hl.1
    rw [berezin_cons, ih hl.2, intStep_apply, ← dη_free_mul hfree, ← dξ_free_mul hfree]
    simp only [pBer, pStep, wProd, List.map_cons, List.prod_cons, LinearMap.comp_apply]
    congr 3
    rw [← mul_assoc]
    exact congrArg (· * F) (mul_comm_of_even hfree.1 (1 + ξ i * η i))

/-! ### Interleaved functionals and vectors -/

/-- The functional `ξ_i^*` (coefficient of `ξ_i`). -/
def fξ (i : Λ) : Module.Dual ℝ (Gen Λ) := LinearMap.proj (R := ℝ) (φ := fun _ : Λ ⊕ Λ => ℝ) (Sum.inl i)

/-- The functional `η_i^*` (coefficient of `η_i`). -/
def fη (i : Λ) : Module.Dual ℝ (Gen Λ) := LinearMap.proj (R := ℝ) (φ := fun _ : Λ ⊕ Λ => ℝ) (Sum.inr i)

/-- The interleaved sequence `ξ_{l_0}^*, η_{l_0}^*, ξ_{l_1}^*, η_{l_1}^*, …`. -/
def φL (l : List Λ) (a : ℕ) : Module.Dual ℝ (Gen Λ) :=
  match l[a / 2]? with
  | none => 0
  | some i => if a % 2 = 0 then fξ i else fη i

theorem φL_cons_add_two (i : Λ) (l : List Λ) (a : ℕ) : φL (i :: l) (a + 2) = φL l a := by
  have h1 : (a + 2) / 2 = a / 2 + 1 := by omega
  have h2 : (a + 2) % 2 = a % 2 := by omega
  simp only [φL, h1, h2, List.getElem?_cons_succ]

theorem contr_add_two (f : ℕ → Module.Dual ℝ (Gen Λ)) (m : ℕ) (x : A) :
    Grassmann.contr (m := m + 2) (fun a => f a) x =
      Grassmann.contr (m := m) (fun a => f (a + 2)) (contractLeft (f 1) (contractLeft (f 0) x)) := by
  rw [Grassmann.contr_succ, Grassmann.contr_succ]
  rfl

/-- The plain Berezin integral is an iterated contraction. -/
theorem pBer_eq_contr (l : List Λ) (x : A) :
    pBer l x = Grassmann.contr (m := 2 * l.length) (fun a => φL l a) x := by
  induction l generalizing x with
  | nil => rfl
  | cons i l ih =>
    have e : 2 * (i :: l).length = 2 * l.length + 2 := by simp [List.length_cons]; ring
    change pBer l (dη i (dξ i x)) = _
    rw [ih]
    have := contr_add_two (fun a => φL (i :: l) a) (2 * l.length) x
    simp only [φL_cons_add_two] at this
    convert this.symm using 2
    rfl

/-- The vector `v_i = ∑_j M_ij η_j`. -/
def vv (M : Matrix Λ Λ ℝ) (i : Λ) : Gen Λ := fun x => Sum.elim (fun _ => 0) (fun j => M i j) x

/-- The interleaved sequence `ξ_{l_0}, v_{l_0}, ξ_{l_1}, v_{l_1}, …`. -/
def uL (M : Matrix Λ Λ ℝ) (l : List Λ) (a : ℕ) : Gen Λ :=
  match l[a / 2]? with
  | none => 0
  | some i => if a % 2 = 0 then Pi.single (Sum.inl i) 1 else vv M i

theorem uL_cons_add_two (M : Matrix Λ Λ ℝ) (i : Λ) (l : List Λ) (a : ℕ) :
    uL M (i :: l) (a + 2) = uL M l a := by
  have h1 : (a + 2) / 2 = a / 2 + 1 := by omega
  have h2 : (a + 2) % 2 = a % 2 := by omega
  simp only [uL, h1, h2, List.getElem?_cons_succ]

/-- The odd-odd product `ξ_i ι(v_i)`. -/
def cc (M : Matrix Λ Λ ℝ) (i : Λ) : A := ξ i * ExteriorAlgebra.ι ℝ (vv M i)

theorem list_prod_cc (M : Matrix Λ Λ ℝ) (l : List Λ) :
    (l.map (cc M)).prod = ExteriorAlgebra.ιMulti ℝ (2 * l.length) (fun a => uL M l a) := by
  induction l with
  | nil => simp [ExteriorAlgebra.ιMulti_zero_apply]
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons, ih]
    change _ = ExteriorAlgebra.ιMulti ℝ (2 * l.length + 1 + 1) _
    rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply, ← mul_assoc]
    have h0 : uL M (i :: l) 0 = Pi.single (Sum.inl i) 1 := by simp [uL]
    have h1 : uL M (i :: l) 1 = vv M i := by simp [uL]
    congr 1
    · simp only [Matrix.vecTail, Function.comp_apply, Fin.val_succ, Fin.val_zero, zero_add, h0,
        h1]
      rfl
    · congr 1
      funext a
      simp only [Matrix.vecTail, Function.comp_apply, Fin.val_succ]
      exact (uL_cons_add_two M i l a).symm

theorem inv'_cc (M : Matrix Λ Λ ℝ) (i : Λ) : inv' (cc M i) = cc M i := by
  simp [cc]

/-- `ξ_i ι(v_i)` in the center. -/
def ccC (M : Matrix Λ Λ ℝ) (i : Λ) : C Λ := mkC (cc M i) (mem_center_of_even (inv'_cc M i))

@[simp] theorem cv_ccC (M : Matrix Λ Λ ℝ) (i : Λ) : cv (ccC M i) = cc M i := rfl

theorem ccC_sq (M : Matrix Λ Λ ℝ) (i : Λ) : ccC M i * ccC M i = 0 := by
  apply cv_injective
  rw [map_mul, cv_ccC, map_zero, cc]
  have : ξ i * ExteriorAlgebra.ι ℝ (vv M i) * (ξ i * ExteriorAlgebra.ι ℝ (vv M i)) =
      -(ξ i * ξ i * (ExteriorAlgebra.ι ℝ (vv M i) * ExteriorAlgebra.ι ℝ (vv M i)) : A) := by
    have h := ι_anticomm (vv M i) (Pi.single (Sum.inl i) 1)
    change ExteriorAlgebra.ι ℝ (vv M i) * ξ i = -(ξ i * ExteriorAlgebra.ι ℝ (vv M i)) at h
    calc _ = ξ i * (ExteriorAlgebra.ι ℝ (vv M i) * ξ i) * ExteriorAlgebra.ι ℝ (vv M i) := by
          noncomm_ring
      _ = _ := by rw [h]; noncomm_ring
  rw [this, ξ_mul_ξ, zero_mul, neg_zero]

theorem vv_eq (M : Matrix Λ Λ ℝ) (i : Λ) [Fintype Λ] :
    vv M i = ∑ j, M i j • (Pi.single (Sum.inr j) 1 : Gen Λ) := by
  funext x
  rcases x with x | x
  · simp [vv]
  · simp [vv, Finset.sum_apply, Pi.single_apply]

theorem sum_ccC [Fintype Λ] (M : Matrix Λ Λ ℝ) :
    ∑ i, ccC M i = ∑ i, ∑ j, M i j • pc i j := by
  apply cv_injective
  simp only [map_sum, map_smul, cv_ccC, coe_pc, cc]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [vv_eq, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, mul_smul_comm]
  rfl

theorem exp_sum_ccC [Fintype Λ] (M : Matrix Λ Λ ℝ) :
    IsNilpotent.exp (∑ i, ccC M i) = ∏ i, (1 + ccC M i) := by
  have hn : ∀ i ∈ (univ : Finset Λ), IsNilpotent (ccC M i) :=
    fun i _ => isNilpotent_of_mul_self (ccC_sq M i)
  rw [exp_sum _ _ hn]
  exact Finset.prod_congr rfl fun i _ => exp_eq_one_add (ccC_sq M i)

theorem cv_prod_ccC (M : Matrix Λ Λ ℝ) {l : List Λ} (hl : l.Nodup) :
    cv (∏ i ∈ l.toFinset, ccC M i) = (l.map (cc M)).prod := by
  rw [List.prod_toFinset _ hl, map_list_prod, List.map_map]
  rfl

/-! ### The determinant -/

section Det

variable [Fintype Λ]

/-- The enumeration of `Λ` used for the Gaussian integral. -/
def enum (Λ : Type*) [Fintype Λ] : Fin (Fintype.card Λ) ≃ Λ := (Fintype.equivFin Λ).symm

/-- The list `l = (σ 0, …, σ (n-1))` of all vertices. -/
def lst (Λ : Type*) [Fintype Λ] : List Λ := List.ofFn (enum Λ)

theorem lst_nodup : (lst Λ).Nodup := List.nodup_ofFn.2 (enum Λ).injective

theorem lst_length : (lst Λ).length = Fintype.card Λ := List.length_ofFn

theorem lst_toFinset : (lst Λ).toFinset = univ := by
  ext i; simp only [lst, List.mem_toFinset, List.mem_ofFn, mem_univ, iff_true]
  exact ⟨(enum Λ).symm i, by simp⟩

/-- The index equivalence `(k, b) ↦ 2k + b`. -/
def ilv (n : ℕ) : Fin n × Fin 2 ≃ Fin (2 * n) := finProdFinEquiv.trans (finCongr (Nat.mul_comm n 2))

theorem ilv_val {n : ℕ} (x : Fin n × Fin 2) : (ilv n x : ℕ) = x.2 + 2 * x.1 := by
  simp [ilv, finProdFinEquiv_apply_val]

/-- `ilv` composed with the identification `2 * card Λ = 2 * length (lst Λ)`. -/
def ilv' (Λ : Type*) [DecidableEq Λ] [Fintype Λ] : Fin (Fintype.card Λ) × Fin 2 ≃ Fin (2 * (lst Λ).length) :=
  (ilv _).trans (finCongr (by rw [lst_length]))

theorem ilv'_val (x : Fin (Fintype.card Λ) × Fin 2) : (ilv' Λ x : ℕ) = x.2 + 2 * x.1 := by
  simp [ilv', ilv_val]

theorem det_interleaved (M : Matrix Λ Λ ℝ) :
    (Matrix.of fun a b : Fin (2 * (lst Λ).length) => φL (lst Λ) a (uL M (lst Λ) b)).det =
      M.det := by
  rw [← Matrix.det_submatrix_equiv_self (ilv' Λ)]
  have hget : ∀ (k : Fin (Fintype.card Λ)) (b : Fin 2),
      (lst Λ)[((ilv' Λ (k, b) : ℕ)) / 2]? = some (enum Λ k) ∧ (ilv' Λ (k, b) : ℕ) % 2 = b := by
    intro k b
    rw [ilv'_val]
    have h1 : ((b : ℕ) + 2 * k) / 2 = k := by omega
    have h2 : ((b : ℕ) + 2 * k) % 2 = b := by omega
    refine ⟨?_, h2⟩
    rw [h1]
    simp [lst, k.isLt]
  have hB : (Matrix.of fun a b : Fin (2 * (lst Λ).length) => φL (lst Λ) a (uL M (lst Λ) b)).submatrix
      (ilv' Λ) (ilv' Λ) = Matrix.blockDiagonal (fun b : Fin 2 =>
        if b = 0 then (1 : Matrix (Fin (Fintype.card Λ)) (Fin (Fintype.card Λ)) ℝ)
        else (M.submatrix (enum Λ) (enum Λ)).transpose) := by
    ext ⟨k, b⟩ ⟨m, c⟩
    obtain ⟨g1, g2⟩ := hget k b
    obtain ⟨g3, g4⟩ := hget m c
    simp only [Matrix.submatrix_apply, Matrix.of_apply, φL, uL, g1, g2, g3, g4,
      Matrix.blockDiagonal_apply]
    fin_cases b <;> fin_cases c
    · simp [fξ, Matrix.one_apply, Pi.single_apply, (enum Λ).injective.eq_iff]
    · simp [fξ, vv]
    · simp [fη]
    · simp [fη, vv]
  rw [hB, Matrix.det_blockDiagonal, Fin.prod_univ_two]
  simp [Matrix.det_transpose, Matrix.det_submatrix_equiv_self]

/-- **Fermionic Gaussian integral** (BCHS (2.74)):
`∫ d(ξ, η) exp(∑ᵢⱼ Mᵢⱼ ξᵢ ηⱼ) = det M` (plain Berezin integral). -/
theorem gaussian_pBer (M : Matrix Λ Λ ℝ) :
    ExteriorAlgebra.algebraMapInv
      (pBer (lst Λ) (cv (IsNilpotent.exp (∑ i, ∑ j, M i j • pc i j)))) = M.det := by
  rw [← sum_ccC, exp_sum_ccC, Finset.prod_one_add, map_sum, map_sum, map_sum,
    Finset.sum_eq_single (univ : Finset Λ)]
  · rw [← lst_toFinset, cv_prod_ccC M lst_nodup, list_prod_cc, pBer_eq_contr,
      Grassmann.algebraMapInv_contr_ιMulti, det_interleaved]
  · intro S _ hS
    rw [← S.toList_toFinset, cv_prod_ccC M S.nodup_toList, list_prod_cc, pBer_eq_contr]
    refine Grassmann.algebraMapInv_contr_ιMulti_of_ne _ _ ?_
    rw [lst_length, Finset.length_toList]
    intro h
    exact hS ((Finset.card_eq_iff_eq_univ S).1 (by omega))
  · intro h; exact absurd (Finset.mem_powerset.2 (Finset.subset_univ _)) h

theorem isNilpotent_quad (M : Matrix Λ Λ ℝ) : IsNilpotent (∑ i, ∑ j, M i j • pc i j : C Λ) :=
  isNilpotent_sum fun i _ => isNilpotent_sum fun j _ =>
    isNilpotent_of_mul_self (smul_mul_smul_self (pc_mul_pc_left i j j))

theorem wProd_lst : wProd (lst Λ) = cv (IsNilpotent.exp (∑ i, pc i i : C Λ)) := by
  rw [exp_sum _ _ (fun i _ => isNilpotent_of_mul_self (pc_sq i)),
    Finset.prod_congr rfl fun i _ => exp_eq_one_add (pc_sq i), ← lst_toFinset,
    List.prod_toFinset _ lst_nodup, map_list_prod, List.map_map]
  rfl

/-- **Fermionic Gaussian integral for the hyperbolic integral `H02.int0`**:
`[exp(∑ᵢⱼ Mᵢⱼ ξᵢ ηⱼ)]_0 = det (M + 1)`. -/
theorem int0_exp_quadratic (M : Matrix Λ Λ ℝ) :
    int0 (cv (IsNilpotent.exp (∑ i, ∑ j, M i j • pc i j))) = (M + 1).det := by
  have hQ := isNilpotent_quad M
  have hD : IsNilpotent (∑ i, pc i i : C Λ) :=
    isNilpotent_sum fun i _ => isNilpotent_of_mul_self (pc_sq i)
  have hperm : (univ : Finset Λ).toList.Perm (lst Λ) :=
    List.perm_of_nodup_nodup_toFinset_eq (Finset.nodup_toList _) lst_nodup
      (by rw [lst_toFinset, Finset.toList_toFinset])
  have hsum : (∑ i, pc i i + ∑ i, ∑ j, M i j • pc i j : C Λ) =
      ∑ i, ∑ j, (M + 1) i j • pc i j := by
    simp only [Matrix.add_apply, Matrix.one_apply, add_smul, Finset.sum_add_distrib, ite_smul,
      one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [add_comm]
  rw [int0, berezin_perm hperm, berezin_eq_pBer lst_nodup, wProd_lst, ← map_mul,
    ← IsNilpotent.exp_add_of_commute (Commute.all _ _) hD hQ, hsum, gaussian_pBer]

end Det

end

end ArborealDecay.ForestPoly

end
