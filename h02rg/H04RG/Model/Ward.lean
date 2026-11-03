import H04RG.Model.Algebra

/-!
# Ward identities for `ℍ^{0|4}` with two external fields

Lemma 3.1 of `h04/h04-d5-outline.tex`, for the two-field family
`H_{β,h,k} = 1/4 ∑_{x,y} β_{xy} (u_x - u_y)² + ∑_x h_x (z_x - 1) + ∑_x k_x (z_x - 1)²`
(`k ≡ 0` is the `ℍ^{0|4}` model; `(z - 1)² = 2q` couples to the local quartic term).

With the odd derivation `T_a = ∑_x z_x ∂_{ξ^a_x}`:
* `T_a z_y = -η^a_y` and `T_a (u_x · u_y) = 0`;
* `[T_a F]_0 = 0` for every `F` (`int0_T`): `z_x⁻¹ z_x = 1`, and `∏_{y ≠ x} z_y⁻¹` is even and free of
  `ξ^a_x`, so the integrand is a `∂_{ξ^a_x}`-derivative;
* `[T_a F]_{β,h,k} = -[F̂ ∑_x (h_x η^a_x + 2 k_x (z_x - 1) η^a_x)]_{β,h,k}` (`expect2_T`), `F̂` the grade
  involution of `F`.
Specialisations: `avg2_z` (`F = ξ^a_x`) and `avg2_ξηq` (`F = ξ^0_x ξ^1_x η^1_x`, `a = 0`).
-/

namespace H04RG

noncomputable section

open H02 (ξ η dξ dη C cv pc inv' mul_comm_of_even cv_injective)
open Finset

set_option linter.unusedSectionVars false

variable {Λ : Type*} [DecidableEq Λ]

/-! ### Evenness and invertibility of `z` -/

theorem inv'_s (x : Λ) : inv' (s x) = s x := by simp [s]

theorem inv'_q (x : Λ) : inv' (q x) = q x := by simp [q]

theorem inv'_z (x : Λ) : inv' (z x) = z x := by simp [z, inv'_s, inv'_q]

/-- `z_x² = 1 - 2 s_x` in the Grassmann algebra. -/
theorem z_mul_z (x : Λ) : z x * z x = 1 - (2 : ℝ) • s x := by
  have h := congrArg cv (zC_sq x)
  simp only [map_mul, map_sub, map_one, cv_zC, cv_sC] at h
  rw [h, map_ofNat, two_smul, two_mul]

theorem z_mul_cv_inverse (x : Λ) : z x * cv (Ring.inverse (zC x)) = 1 := by
  rw [← cv_zC, ← map_mul, Ring.mul_inverse_cancel _ (isUnit_zC x), map_one]

theorem cv_inverse_mul_z (x : Λ) : cv (Ring.inverse (zC x)) * z x = 1 := by
  rw [← cv_zC, ← map_mul, inverse_zC_mul_zC, map_one]

/-- `cv (zC x)⁻¹ = (z x)⁻¹`: the volume form of `int0` is `∏_x z_x⁻¹`. -/
theorem cv_inverse_zC (x : Λ) : cv (Ring.inverse (zC x)) = Ring.inverse (z x) := by
  let u : (A Λ)ˣ := ⟨z x, cv (Ring.inverse (zC x)), z_mul_cv_inverse x, cv_inverse_mul_z x⟩
  exact ((Ring.inverse_unit u).trans rfl).symm

/-! ### The generator `T_a` -/

variable [Fintype Λ]

/-- `T_a = ∑_x z_x ∂_{ξ^a_x}`. -/
def T (a : Fin 2) : A Λ →ₗ[ℝ] A Λ := ∑ x, LinearMap.mulLeft ℝ (z x) ∘ₗ dξ (x, a)

theorem T_apply (a : Fin 2) (F : A Λ) : T a F = ∑ x, z x * dξ (x, a) F := by simp [T]

theorem T_mul (a : Fin 2) (F G : A Λ) : T a (F * G) = T a F * G + inv' F * T a G := by
  simp only [T_apply, H02.dξ_mul, mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  congr 1
  · simp only [mul_assoc]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc, ← mul_assoc, mul_comm_of_even (inv'_z i)]

theorem T_one (a : Fin 2) : T a (1 : A Λ) = 0 := by simp [T_apply]

theorem T_ξ (a : Fin 2) (y : Λ) (b : Fin 2) : T a (ξ (y, b)) = if b = a then z y else 0 := by
  rw [T_apply]
  simp only [H02.dξ_ξ, mul_ite, mul_one, mul_zero, Prod.mk.injEq]
  by_cases hb : b = a
  · subst hb; simp [eq_comm]
  · simp [Ne.symm hb, hb]

theorem T_η (a : Fin 2) (i : Λ × Fin 2) : T a (η i) = 0 := by simp [T_apply, H02.dξ_η]

theorem T_ξη (a : Fin 2) (y : Λ) (b : Fin 2) (j : Λ × Fin 2) :
    T a (ξ (y, b) * η j) = if b = a then z y * η j else 0 := by
  rw [T_mul, T_ξ, T_η, mul_zero, add_zero]
  split_ifs <;> simp

theorem T_s (a : Fin 2) (y : Λ) : T a (s y) = z y * η (y, a) := by
  rw [s, map_sum]
  simp only [T_ξη]
  rw [Finset.sum_ite_eq']; simp

/-- `T_a z_y = -η^a_y`. -/
theorem T_z (a : Fin 2) (y : Λ) : T a (z y) = -η (y, a) := by
  have h1 : T a (z y * z y) = (2 : ℝ) • (z y * T a (z y)) := by
    rw [T_mul, inv'_z, ← mul_comm_of_even (inv'_z y) (T a (z y)), two_smul]
  have h2 : T a (z y * z y) = -((2 : ℝ) • (z y * η (y, a))) := by
    rw [z_mul_z, map_sub, T_one, LinearMap.map_smul_of_tower, T_s, zero_sub]
  have h3 : z y * (T a (z y) + η (y, a)) = 0 := by
    have := h1.symm.trans h2
    rw [mul_add]
    have h2' : (2 : ℝ) • (z y * T a (z y) + z y * η (y, a)) = 0 := by
      rw [smul_add, this, neg_add_cancel]
    exact (smul_eq_zero.mp h2').resolve_left two_ne_zero
  have h4 : cv (Ring.inverse (zC y)) * (z y * (T a (z y) + η (y, a))) = 0 := by rw [h3, mul_zero]
  rw [← mul_assoc, cv_inverse_mul_z, one_mul] at h4
  exact eq_neg_of_add_eq_zero_left h4

/-- `T_a (u_x · u_y) = 0`. -/
theorem T_dot (a : Fin 2) (x y : Λ) : T a (dot x y) = 0 := by
  rw [dot, map_sub, map_neg, map_sum, T_mul, T_z, T_z, inv'_z]
  simp only [map_add, T_ξη, Fin.sum_univ_two]
  fin_cases a <;> simp <;>
    rw [← mul_comm_of_even (inv'_z y) (η (x, _))] <;> abel

theorem T_zsub (a : Fin 2) (y : Λ) : T a (z y - 1) = -η (y, a) := by
  rw [map_sub, T_z, T_one, sub_zero]

theorem T_zsub_sq (a : Fin 2) (y : Λ) :
    T a ((z y - 1) * (z y - 1)) = -((2 : ℝ) • ((z y - 1) * η (y, a))) := by
  have he : inv' (z y - 1) = z y - 1 := by simp [inv'_z]
  rw [T_mul, T_zsub, he, ← mul_comm_of_even he (-η (y, a))]
  simp only [mul_neg, two_smul, neg_add_rev]

/-! ### The flat Berezin integral of a derivative vanishes -/

theorem flat_foldl (l : List (Λ × Fin 2)) (L : A Λ →ₗ[ℝ] A Λ) :
    l.foldl (fun L i => pairStep i ∘ₗ L) L = flat l ∘ₗ L := by
  induction l generalizing L with
  | nil => rfl
  | cons a l ih =>
    simp only [flat, List.foldl_cons]
    rw [ih, ih (pairStep a ∘ₗ LinearMap.id)]
    rfl

theorem flat_cons (i : Λ × Fin 2) (l : List (Λ × Fin 2)) (F : A Λ) :
    flat (i :: l) F = flat l (pairStep i F) := by
  simp only [flat, List.foldl_cons]
  rw [flat_foldl]; rfl

theorem pairStep_comm (i j : Λ × Fin 2) (F : A Λ) :
    pairStep i (pairStep j F) = pairStep j (pairStep i F) := by
  simp only [pairStep, LinearMap.comp_apply]
  exact H02.dd_comm i j F

instance : RightCommutative (fun (L : A Λ →ₗ[ℝ] A Λ) (i : Λ × Fin 2) => pairStep i ∘ₗ L) :=
  ⟨fun L i j => LinearMap.ext fun F => pairStep_comm j i (L F)⟩

theorem flat_perm {l l' : List (Λ × Fin 2)} (h : l.Perm l') : flat l = flat l' :=
  h.foldl_eq _

theorem flat_dξ {l : List (Λ × Fin 2)} {i : Λ × Fin 2} (hi : i ∈ l) (G : A Λ) :
    flat l (dξ i G) = 0 := by
  rw [flat_perm (List.perm_cons_erase hi), flat_cons, pairStep, LinearMap.comp_apply,
    H02.dξ_dξ, map_zero, map_zero]

/-- `(zC y)⁻¹` is free of the generators at `(x, a)` when `y ≠ x`. -/
theorem inverse_zC_mem_freeSub {x y : Λ} (hxy : y ≠ x) (a : Fin 2) :
    Ring.inverse (zC y) ∈ H02.freeSub (x, a) := by
  have hP : ∀ b : Fin 2, pc (y, b) (y, b) ∈ H02.freeSub (x, a) := fun b =>
    H02.pc_mem_freeSub (by simp [hxy]) (by simp [hxy])
  have hs : sC y ∈ H02.freeSub (x, a) := Subalgebra.sum_mem _ fun b _ => hP b
  have hq : qC y ∈ H02.freeSub (x, a) := Subalgebra.mul_mem _ (hP 0) (hP 1)
  rw [inverse_zC]
  refine Subalgebra.add_mem _ (Subalgebra.add_mem _ (Subalgebra.one_mem _) hs) ?_
  exact Subalgebra.mul_mem _ (by simp) hq

theorem int0_z_mul_dξ (x : Λ) (a : Fin 2) (G : A Λ) : int0 (z x * dξ (x, a) G) = 0 := by
  have hmem : ∏ y ∈ univ.erase x, Ring.inverse (zC y) ∈ H02.freeSub (x, a) :=
    Subalgebra.prod_mem _ fun y hy => inverse_zC_mem_freeSub (Finset.ne_of_mem_erase hy) a
  have hfree : H02.IsFree (x, a) (cv (∏ y ∈ univ.erase x, Ring.inverse (zC y))) := hmem
  have hW : cv (∏ y, Ring.inverse (zC y)) * (z x * dξ (x, a) G) =
      dξ (x, a) (cv (∏ y ∈ univ.erase x, Ring.inverse (zC y)) * G) := by
    rw [H02.dξ_free_mul hfree, ← Finset.mul_prod_erase univ _ (mem_univ x),
      mul_comm (Ring.inverse (zC x)), map_mul, mul_assoc, ← mul_assoc (cv (Ring.inverse (zC x))),
      cv_inverse_mul_z, one_mul]
  rw [int0, hW, flat_dξ (Finset.mem_toList.2 (mem_univ _)), map_zero]

/-- `[T_a F]_0 = 0`. -/
theorem int0_T (a : Fin 2) (F : A Λ) : int0 (T a F) = 0 := by
  have hlin : ∀ G H : A Λ, int0 (G + H) = int0 G + int0 H := by
    intro G H; simp [int0, mul_add, map_add]
  rw [T_apply]
  induction (univ : Finset Λ) using Finset.induction_on with
  | empty => simp [int0]
  | insert x t hx ih => rw [Finset.sum_insert hx, hlin, int0_z_mul_dξ, ih, zero_add]

/-! ### The two-field action -/

/-- `H_{β,h,k} = 1/4 ∑_{x,y} β_{xy} (u_x - u_y)² + ∑_x h_x (z_x - 1) + ∑_x k_x (z_x - 1)²`. -/
def action2 (β : Λ → Λ → ℝ) (h k : Λ → ℝ) : A Λ :=
  action β h + ∑ x, k x • ((z x - 1) * (z x - 1))

/-- `[F]_{β,h,k} = [F e^{-H_{β,h,k}}]_0`. -/
def expect2 (β : Λ → Λ → ℝ) (h k : Λ → ℝ) (F : A Λ) : ℝ :=
  int0 (F * IsNilpotent.exp (-action2 β h k))

/-- `⟨F⟩_{β,h,k}`. -/
def avg2 (β : Λ → Λ → ℝ) (h k : Λ → ℝ) (F : A Λ) : ℝ := expect2 β h k F / expect2 β h k 1

theorem action2_zero (β : Λ → Λ → ℝ) (h : Λ → ℝ) : action2 β h 0 = action β h := by
  simp [action2]

/-- The action in the center. -/
def actionC (β : Λ → Λ → ℝ) (h k : Λ → ℝ) : C (Λ × Fin 2) :=
  (1 / 4 : ℝ) • ∑ x, ∑ y, β x y • (dotC x x - dotC x y - dotC y x + dotC y y) +
    ∑ x, h x • (zC x - 1) + ∑ x, k x • ((zC x - 1) * (zC x - 1))

theorem cv_actionC (β : Λ → Λ → ℝ) (h k : Λ → ℝ) : cv (actionC β h k) = action2 β h k := by
  simp [actionC, action2, action, map_sum]

/-- The ideal of the center generated by the pairs `ξ_i η_j`. -/
def pairIdeal : Ideal (C (Λ × Fin 2)) :=
  Ideal.span (Set.range fun p : (Λ × Fin 2) × (Λ × Fin 2) => pc p.1 p.2)

theorem pc_mem_pairIdeal (i j : Λ × Fin 2) : pc i j ∈ (pairIdeal : Ideal (C (Λ × Fin 2))) :=
  Ideal.subset_span ⟨(i, j), rfl⟩

theorem pairIdeal_le_nilradical : (pairIdeal : Ideal (C (Λ × Fin 2))) ≤ nilradical _ := by
  rw [pairIdeal, Ideal.span_le]
  rintro _ ⟨⟨i, j⟩, rfl⟩
  exact mem_nilradical.2 ⟨2, by rw [pow_two]; exact H02.pc_mul_pc_left i j j⟩

theorem smul_mem_pairIdeal (r : ℝ) {c : C (Λ × Fin 2)} (hc : c ∈ (pairIdeal : Ideal _)) :
    r • c ∈ (pairIdeal : Ideal (C (Λ × Fin 2))) := by
  rw [Algebra.smul_def]; exact Ideal.mul_mem_left _ _ hc

theorem zC_sub_one_mem (x : Λ) : zC x - 1 ∈ (pairIdeal : Ideal (C (Λ × Fin 2))) := by
  have : zC x - 1 = -(sC x + qC x) := by unfold zC; ring
  rw [this]
  refine neg_mem (add_mem (Ideal.sum_mem _ fun b _ => pc_mem_pairIdeal _ _) ?_)
  exact Ideal.mul_mem_left _ _ (pc_mem_pairIdeal _ _)

theorem dotC_add_one_mem (x y : Λ) : dotC x y + 1 ∈ (pairIdeal : Ideal (C (Λ × Fin 2))) := by
  have : dotC x y + 1 = -(∑ a : Fin 2, (pc (x, a) (y, a) + pc (y, a) (x, a))) -
      ((zC x - 1) * (zC y - 1) + (zC x - 1) + (zC y - 1)) := by unfold dotC; ring
  rw [this]
  refine sub_mem (neg_mem (Ideal.sum_mem _ fun a _ =>
    add_mem (pc_mem_pairIdeal _ _) (pc_mem_pairIdeal _ _))) ?_
  exact add_mem (add_mem (Ideal.mul_mem_right _ _ (zC_sub_one_mem x)) (zC_sub_one_mem x))
    (zC_sub_one_mem y)

theorem actionC_mem (β : Λ → Λ → ℝ) (h k : Λ → ℝ) :
    actionC β h k ∈ (pairIdeal : Ideal (C (Λ × Fin 2))) := by
  have hd : ∀ x y : Λ, dotC x x - dotC x y - dotC y x + dotC y y =
      (dotC x x + 1) - (dotC x y + 1) - (dotC y x + 1) + (dotC y y + 1) := fun x y => by ring
  refine add_mem (add_mem ?_ ?_) ?_
  · refine smul_mem_pairIdeal _ (Ideal.sum_mem _ fun x _ => Ideal.sum_mem _ fun y _ => ?_)
    rw [hd]
    exact smul_mem_pairIdeal _ (add_mem (sub_mem (sub_mem (dotC_add_one_mem x x)
      (dotC_add_one_mem x y)) (dotC_add_one_mem y x)) (dotC_add_one_mem y y))
  · exact Ideal.sum_mem _ fun x _ => smul_mem_pairIdeal _ (zC_sub_one_mem x)
  · exact Ideal.sum_mem _ fun x _ =>
      smul_mem_pairIdeal _ (Ideal.mul_mem_right _ _ (zC_sub_one_mem x))

theorem isNilpotent_neg_action2 (β : Λ → Λ → ℝ) (h k : Λ → ℝ) :
    IsNilpotent (-action2 β h k) := by
  rw [← cv_actionC, ← map_neg]
  exact (mem_nilradical.1 (pairIdeal_le_nilradical (neg_mem (actionC_mem β h k)))).map cv

theorem inv'_action2 (β : Λ → Λ → ℝ) (h k : Λ → ℝ) :
    inv' (action2 β h k) = action2 β h k := by
  simp [action2, action, dot, inv'_z, map_sum]

/-! ### `T_a` on the Boltzmann factor -/

theorem T_pow (a : Fin 2) {y : A Λ} (hy : inv' y = y) (n : ℕ) :
    T a (y ^ (n + 1)) = ((n + 1 : ℕ) : ℝ) • (y ^ n * T a y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', T_mul, ih, hy, mul_smul_comm, ← mul_assoc, ← pow_succ',
      mul_comm_of_even (show inv' (y ^ (n + 1)) = y ^ (n + 1) by rw [map_pow, hy])]
    push_cast
    module

theorem T_exp (a : Fin 2) {y : A Λ} (hy : inv' y = y) (hn : IsNilpotent y) :
    T a (IsNilpotent.exp y) = IsNilpotent.exp y * T a y := by
  obtain ⟨k, hk⟩ := hn
  have hk1 : y ^ (k + 1) = 0 := by rw [pow_succ, hk, zero_mul]
  conv_rhs => rw [IsNilpotent.exp_eq_sum hk]
  rw [IsNilpotent.exp_eq_sum hk1, map_sum, Finset.sum_mul, Finset.sum_range_succ', pow_zero,
    LinearMap.map_smul_of_tower, T_one, smul_zero, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.map_smul_of_tower, T_pow a hy, smul_mul_assoc, Nat.cast_smul_eq_nsmul ℝ,
    ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, Nat.factorial_succ, Nat.cast_mul]
  congr 1
  field_simp

/-- The source term `T_a(-H_{β,h,k}) = ∑_x (h_x η^a_x + 2 k_x (z_x - 1) η^a_x)`. -/
def src (h k : Λ → ℝ) (a : Fin 2) : A Λ :=
  ∑ x, (h x • η (x, a) + (2 * k x) • ((z x - 1) * η (x, a)))

theorem T_neg_action2 (β : Λ → Λ → ℝ) (h k : Λ → ℝ) (a : Fin 2) :
    T a (-action2 β h k) = src h k a := by
  simp only [action2, action, src, map_neg, map_add, map_sub, map_sum, LinearMap.map_smul_of_tower,
    T_dot, T_zsub_sq, T_z, T_one, sub_zero, add_zero, smul_zero, Finset.sum_const_zero, neg_zero,
    Finset.sum_add_distrib, neg_add_rev, smul_neg, Finset.sum_neg_distrib, neg_neg, smul_smul]
  simp [add_comm, mul_comm]

/-! ### The Ward identity -/

/-- `[·]_0` as a linear map. -/
def int0L : A Λ →ₗ[ℝ] ℝ :=
  (ExteriorAlgebra.algebraMapInv (R := ℝ) (M := (Λ × Fin 2) ⊕ (Λ × Fin 2) → ℝ)).toLinearMap ∘ₗ
    flat (Finset.univ : Finset (Λ × Fin 2)).toList ∘ₗ
    LinearMap.mulLeft ℝ (cv (∏ x, Ring.inverse (zC x)))

theorem int0_eq_L (F : A Λ) : int0 F = int0L F := rfl

/-- `[·]_{β,h,k}` as a linear map. -/
def expect2L (β : Λ → Λ → ℝ) (h k : Λ → ℝ) : A Λ →ₗ[ℝ] ℝ :=
  int0L ∘ₗ LinearMap.mulRight ℝ (IsNilpotent.exp (-action2 β h k))

theorem expect2_eq_L (β : Λ → Λ → ℝ) (h k : Λ → ℝ) (F : A Λ) :
    expect2 β h k F = expect2L β h k F := rfl

/-- Ward identity: `[T_a F]_{β,h,k} = -[F̂ ∑_x (h_x η^a_x + 2 k_x (z_x - 1) η^a_x)]_{β,h,k}`. -/
theorem expect2_T (β : Λ → Λ → ℝ) (h k : Λ → ℝ) (a : Fin 2) (F : A Λ) :
    expect2 β h k (T a F) = -expect2 β h k (inv' F * src h k a) := by
  have hn := isNilpotent_neg_action2 β h k
  have hy : inv' (-action2 β h k) = -action2 β h k := by rw [map_neg, inv'_action2]
  have hE : inv' (IsNilpotent.exp (-action2 β h k)) = IsNilpotent.exp (-action2 β h k) := by
    rw [IsNilpotent.map_exp hn, hy]
  have h0 : int0 (T a (F * IsNilpotent.exp (-action2 β h k))) = 0 := int0_T a _
  rw [T_mul, T_exp a hy hn, T_neg_action2, int0_eq_L, map_add] at h0
  rw [expect2_eq_L, expect2_eq_L, expect2L, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.mulRight_apply, LinearMap.mulRight_apply, mul_assoc,
    ← mul_comm_of_even hE (src h k a)]
  linarith

/-- First Ward identity (`F = ξ^a_{x₀}`):
`[z_{x₀}] = ∑_y (h_y [ξ^a_{x₀} η^a_y] + 2 k_y [ξ^a_{x₀} (z_y - 1) η^a_y])`. -/
theorem expect2_z (β : Λ → Λ → ℝ) (h k : Λ → ℝ) (a : Fin 2) (x₀ : Λ) :
    expect2 β h k (z x₀) = ∑ y, (h y * expect2 β h k (ξ (x₀, a) * η (y, a)) +
      2 * k y * expect2 β h k (ξ (x₀, a) * ((z y - 1) * η (y, a)))) := by
  have hW := expect2_T β h k a (ξ (x₀, a))
  rw [T_ξ, if_pos rfl, H02.inv'_ξ, neg_mul, expect2_eq_L, expect2_eq_L, map_neg, neg_neg] at hW
  rw [expect2_eq_L, hW, src, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [mul_add, map_add, mul_smul_comm, mul_smul_comm, LinearMap.map_smul_of_tower,
    LinearMap.map_smul_of_tower, smul_eq_mul, smul_eq_mul, expect2_eq_L, expect2_eq_L]

/-- `z_x ξ^1_x η^1_x = ξ^1_x η^1_x - q_x`. -/
theorem z_mul_ξη1 (x : Λ) : z x * (ξ (x, 1) * η (x, 1)) = ξ (x, 1) * η (x, 1) - q x := by
  have h : zC x * P x 1 = P x 1 - qC x := by
    rw [zC, sC_eq, qC_eq]
    linear_combination (-(1 + P x 0)) * P_sq x 1
  have := congrArg cv h
  simpa using this

/-- Second Ward identity (`F = ξ^0_{x₀} ξ^1_{x₀} η^1_{x₀}`, `a = 0`):
`[ξ^1_{x₀} η^1_{x₀} - q_{x₀}] = ∑_y (h_y [F η^0_y] + 2 k_y [F (z_y - 1) η^0_y])`. -/
theorem expect2_ξηq (β : Λ → Λ → ℝ) (h k : Λ → ℝ) (x₀ : Λ) :
    expect2 β h k (ξ (x₀, 1) * η (x₀, 1) - q x₀) =
      ∑ y, (h y * expect2 β h k (ξ (x₀, 0) * (ξ (x₀, 1) * η (x₀, 1)) * η (y, 0)) +
        2 * k y * expect2 β h k (ξ (x₀, 0) * (ξ (x₀, 1) * η (x₀, 1)) * ((z y - 1) * η (y, 0)))) := by
  set F : A Λ := ξ (x₀, 0) * (ξ (x₀, 1) * η (x₀, 1)) with hF
  have hT : T 0 F = ξ (x₀, 1) * η (x₀, 1) - q x₀ := by
    rw [hF, T_mul, T_ξ, if_pos rfl, T_ξη, if_neg (by decide), mul_zero, add_zero, z_mul_ξη1]
  have hinv : inv' F = -F := by simp [hF]
  have hW := expect2_T β h k 0 F
  rw [hT, hinv, neg_mul, expect2_eq_L, expect2_eq_L, map_neg, neg_neg] at hW
  rw [expect2_eq_L, hW, src, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [mul_add, map_add, mul_smul_comm, mul_smul_comm, LinearMap.map_smul_of_tower,
    LinearMap.map_smul_of_tower, smul_eq_mul, smul_eq_mul, expect2_eq_L, expect2_eq_L, mul_assoc,
    mul_assoc]

end

end H04RG
