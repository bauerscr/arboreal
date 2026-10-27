import H02.Algebra

/-!
# The fermionic integral: basic computations, order independence, Ward identity
-/

namespace H02

noncomputable section

set_option linter.unusedSectionVars false

open CliffordAlgebra

variable {Λ : Type*} [DecidableEq Λ]

local notation "A" => Grassmann Λ

/-- The center of the Grassmann algebra, a commutative ring containing all even forms. -/
def C (Λ : Type*) : Type _ := Subalgebra.center ℝ (Grassmann Λ)

instance : CommRing (C Λ) := inferInstanceAs (CommRing (Subalgebra.center ℝ (Grassmann Λ)))

instance : Algebra ℝ (C Λ) := inferInstanceAs (Algebra ℝ (Subalgebra.center ℝ (Grassmann Λ)))

instance : Module ℚ (C Λ) := Module.compHom (C Λ) (algebraMap ℚ ℝ)

/-- The inclusion of the center. -/
def cv : C Λ →ₐ[ℝ] Grassmann Λ := (Subalgebra.center ℝ (Grassmann Λ)).val

theorem cv_injective : Function.Injective (cv : C Λ → Grassmann Λ) := Subtype.val_injective

/-- An element of the center. -/
def mkC (x : Grassmann Λ) (hx : x ∈ Subalgebra.center ℝ (Grassmann Λ)) : C Λ := ⟨x, hx⟩

@[simp] theorem cv_mkC (x : Grassmann Λ) (hx) : cv (mkC x hx) = x := rfl

/-! ### Even quadratic elements `ξ_i η_j` in the center -/

/-- `ξ_i η_j` as an element of the center. -/
def pc (i j : Λ) : C Λ := mkC (ξ i * η j) (mem_center_of_even (inv'_ξη i j))

@[simp] theorem coe_pc (i j : Λ) : cv (pc i j) = ξ i * η j := rfl

theorem pc_rel (i j k l : Λ) : pc i j * pc k l = -(pc i l * pc k j) := by
  apply cv_injective
  simp only [map_mul, map_neg, coe_pc]
  exact ξη_rel i j k l

theorem eq_zero_of_eq_neg' {x : C Λ} (h : x = -x) : x = 0 := by
  have h2 : (2 : ℝ) • x = 0 := by
    rw [two_smul]; nth_rewrite 2 [h]; exact add_neg_cancel x
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

theorem pc_mul_pc_left (i j l : Λ) : pc i j * pc i l = 0 := by
  apply eq_zero_of_eq_neg'
  have := pc_rel i j i l
  rwa [mul_comm (pc i l)] at this

theorem pc_mul_pc_right (i j k : Λ) : pc i j * pc k j = 0 :=
  eq_zero_of_eq_neg' (pc_rel i j k j)

/-- `z_i` in the center. -/
def zc (i : Λ) : C Λ := 1 - pc i i

/-- `1 + u_i · u_j` in the center. -/
def Xc (i j : Λ) : C Λ := 1 + (-(pc i j) - pc j i - zc i * zc j)

@[simp] theorem coe_zc (i : Λ) : cv (zc i) = z i := by simp [zc, z]

@[simp] theorem coe_Xc (i j : Λ) : cv (Xc i j) = 1 + dot i j := by
  simp [Xc, dot]

theorem Xc_eq (i j : Λ) : Xc i j = pc i i + pc j j - pc i i * pc j j - pc i j - pc j i := by
  unfold Xc zc; ring

theorem Xc_comm (i j : Λ) : Xc i j = Xc j i := by
  rw [Xc_eq, Xc_eq]; ring

theorem Xc_self (i : Λ) : Xc i i = 0 := by
  rw [Xc_eq]; linear_combination (-1 : C Λ) * pc_mul_pc_left i i i

theorem Xc_sq (a b : Λ) : Xc a b * Xc a b = 0 := by
  rw [Xc_eq]
  have hAA := pc_mul_pc_left a a a
  have hBB := pc_mul_pc_left b b b
  have hPP := pc_mul_pc_left a b b
  have hQQ := pc_mul_pc_left b a a
  have hAP := pc_mul_pc_left a a b
  have hAQ := pc_mul_pc_right a a b
  have hBP := pc_mul_pc_right b b a
  have hBQ := pc_mul_pc_left b b a
  have hPQ := pc_rel a b b a
  linear_combination (1 - 2 * pc b b + pc b b ^ 2) * hAA + (1 - 2 * pc a a) * hBB + hPP + hQQ +
    (2 * pc b b - 2) * hAP + (2 * pc b b - 2) * hAQ + (-2 : C Λ) * hBP + (-2 : C Λ) * hBQ +
    2 * hPQ

theorem pc_mul_Xc (v w : Λ) : pc v v * Xc v w = pc v v * pc w w := by
  rw [Xc_eq]
  linear_combination (1 - pc w w) * pc_mul_pc_left v v v - pc_mul_pc_left v v w -
    pc_mul_pc_right v v w

theorem pc_sq (i : Λ) : pc i i * pc i i = 0 := pc_mul_pc_left i i i

theorem ξη_sq (i : Λ) : ξ i * η i * (ξ i * η i) = (0 : A) := by
  simpa using congrArg cv (pc_sq i)

/-! ### `z_i` and its inverse -/

theorem inv'_z (i : Λ) : inv' (z i) = z i := by simp [z]

theorem inverse_z (i : Λ) : Ring.inverse (z i) = 1 + ξ i * η i := by
  have hQ := ξη_sq i
  let u : Aˣ := ⟨z i, 1 + ξ i * η i,
    by simp only [z]; rw [sub_mul, one_mul, mul_add, mul_one, hQ]; abel,
    by simp only [z]; rw [mul_sub, mul_one, add_mul, one_mul, hQ]; abel⟩
  exact Ring.inverse_unit u

theorem z_mul_η (i : Λ) : z i * η i = η i := by
  simp only [z]; rw [sub_mul, one_mul, mul_assoc, η_mul_η, mul_zero, sub_zero]

theorem inverse_z_mul_z (i : Λ) : Ring.inverse (z i) * z i = 1 := by
  rw [inverse_z]; simp only [z]; rw [mul_sub, mul_one, add_mul, one_mul, ξη_sq i]; abel

theorem intStep_apply (i : Λ) (F : A) :
    intStep i F = dη i (dξ i ((1 + ξ i * η i) * F)) := by
  simp [intStep, inverse_z]

/-! ### Forms not involving a vertex -/

/-- `x` is even and does not involve the generators `ξ_v`, `η_v`. -/
def IsFree (v : Λ) (x : A) : Prop := inv' x = x ∧ dξ v x = 0 ∧ dη v x = 0

theorem IsFree.mul {v : Λ} {x y : A} (hx : IsFree v x) (hy : IsFree v y) : IsFree v (x * y) :=
  ⟨by rw [map_mul, hx.1, hy.1], by rw [dξ_mul, hx.2.1, hy.2.1]; simp,
    by rw [dη_mul, hx.2.2, hy.2.2]; simp⟩

theorem IsFree.add {v : Λ} {x y : A} (hx : IsFree v x) (hy : IsFree v y) : IsFree v (x + y) :=
  ⟨by rw [map_add, hx.1, hy.1], by rw [map_add, hx.2.1, hy.2.1, add_zero],
    by rw [map_add, hx.2.2, hy.2.2, add_zero]⟩

theorem isFree_algebraMap (v : Λ) (r : ℝ) : IsFree v (algebraMap ℝ A r) :=
  ⟨AlgHom.commutes _ r, by simp [dξ], by simp [dη]⟩

theorem isFree_ξη {v i j : Λ} (hi : i ≠ v) (hj : j ≠ v) : IsFree v (ξ i * η j) := by
  refine ⟨inv'_ξη i j, ?_, ?_⟩
  · rw [dξ_mul, dξ_ξ, dξ_η, if_neg (Ne.symm hi)]; simp
  · rw [dη_mul, dη_ξ, dη_η, if_neg (Ne.symm hj)]; simp

/-- The central elements free of `v`, as a subalgebra of the center. -/
def freeSub (v : Λ) : Subalgebra ℝ (C Λ) where
  carrier := {x | IsFree v (cv x)}
  mul_mem' hx hy := by simpa [map_mul] using IsFree.mul hx hy
  add_mem' hx hy := by simpa [map_add] using IsFree.add hx hy
  algebraMap_mem' r := by simpa using isFree_algebraMap v r

theorem pc_mem_freeSub {v i j : Λ} (hi : i ≠ v) (hj : j ≠ v) : pc i j ∈ freeSub v :=
  isFree_ξη hi hj

theorem Xc_mem_freeSub {v a b : Λ} (ha : a ≠ v) (hb : b ≠ v) : Xc a b ∈ freeSub v := by
  rw [Xc_eq]
  have := pc_mem_freeSub (v := v) ha ha
  have := pc_mem_freeSub (v := v) hb hb
  have := pc_mem_freeSub (v := v) ha hb
  have := pc_mem_freeSub (v := v) hb ha
  refine Subalgebra.sub_mem _ (Subalgebra.sub_mem _ (Subalgebra.sub_mem _
    (Subalgebra.add_mem _ ?_ ?_) (Subalgebra.mul_mem _ ?_ ?_)) ?_) ?_ <;> assumption

theorem dξ_free_mul {v : Λ} {x : A} (hx : IsFree v x) (b : A) : dξ v (x * b) = x * dξ v b := by
  rw [dξ_mul, hx.2.1, hx.1, zero_mul, zero_add]

theorem dη_free_mul {v : Λ} {x : A} (hx : IsFree v x) (b : A) : dη v (x * b) = x * dη v b := by
  rw [dη_mul, hx.2.2, hx.1, zero_mul, zero_add]

theorem intStep_free_mul {v : Λ} {x : A} (hx : IsFree v x) (F : A) :
    intStep v (x * F) = x * intStep v F := by
  rw [intStep_apply, intStep_apply]
  have hc : (1 + ξ v * η v) * (x * F) = x * ((1 + ξ v * η v) * F) := by
    rw [← mul_assoc, ← mul_assoc, mul_comm_of_even hx.1 (1 + ξ v * η v)]
  rw [hc, dξ_free_mul hx, dη_free_mul hx]

theorem intStep_ξη (v : Λ) : intStep v (ξ v * η v) = 1 := by
  rw [intStep_apply, add_mul, one_mul, ξη_sq, add_zero, dξ_mul, dξ_ξ, dξ_η, if_pos rfl]
  simp [dη_η]

theorem intStep_free_mul_ξη {v : Λ} {x : A} (hx : IsFree v x) :
    intStep v (x * (ξ v * η v)) = x := by
  rw [intStep_free_mul hx, intStep_ξη, mul_one]

/-! ### Order independence of the integral -/

theorem isFree_w {i j : Λ} (h : i ≠ j) : IsFree j (1 + ξ i * η i) := by
  have := (isFree_algebraMap j 1).add (isFree_ξη h h)
  simpa using this

theorem dd_comm (i j : Λ) (x : A) :
    dη i (dξ i (dη j (dξ j x))) = dη j (dξ j (dη i (dξ i x))) := by
  calc _ = dη i (dη j (dξ j (dξ i x))) := by
        rw [dξ_comm_dη i j, dξ_comm_dξ i j]; simp only [map_neg, neg_neg]
    _ = _ := by rw [dη_comm_dη i j, dη_comm_dξ i j]; simp only [map_neg, neg_neg]

theorem intStep_comm (i j : Λ) (F : A) : intStep i (intStep j F) = intStep j (intStep i F) := by
  by_cases h : i = j
  · rw [h]
  have key : ∀ i j : Λ, i ≠ j → intStep i (intStep j F) =
      dη i (dξ i (dη j (dξ j ((1 + ξ i * η i) * ((1 + ξ j * η j) * F))))) := by
    intro i j h
    have hw := isFree_w h
    rw [intStep_apply, intStep_apply, ← dη_free_mul hw, ← dξ_free_mul hw]
  rw [key i j h, key j i (Ne.symm h), dd_comm, ← mul_assoc, ← mul_assoc,
    mul_comm_of_even (isFree_w h).1]

theorem berezin_foldl (l : List Λ) (L : A →ₗ[ℝ] A) :
    l.foldl (fun L i => intStep i ∘ₗ L) L = berezin l ∘ₗ L := by
  induction l generalizing L with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldl_cons, berezin]
    rw [ih, ih (intStep a ∘ₗ LinearMap.id)]
    rfl

@[simp] theorem berezin_nil : berezin ([] : List Λ) = LinearMap.id := rfl

theorem berezin_cons (i : Λ) (l : List Λ) (F : A) :
    berezin (i :: l) F = berezin l (intStep i F) := by
  simp only [berezin, List.foldl_cons]
  rw [berezin_foldl]; rfl

instance : RightCommutative (fun (L : A →ₗ[ℝ] A) (i : Λ) => intStep i ∘ₗ L) :=
  ⟨fun L i j => LinearMap.ext fun x => (intStep_comm j i (L x))⟩

theorem berezin_perm {l l' : List Λ} (h : l.Perm l') : berezin l = berezin l' :=
  h.foldl_eq _

theorem berezin_eq_cons_erase {l : List Λ} {i : Λ} (hi : i ∈ l) (F : A) :
    berezin l F = berezin (l.erase i) (intStep i F) := by
  rw [berezin_perm (List.perm_cons_erase hi), berezin_cons]

/-! ### Ward identity -/

/-- The supersymmetry generator `T_s = ∑_{i ∈ s} z_i ∂_{ξ_i}`. -/
def T (s : Finset Λ) : A →ₗ[ℝ] A := ∑ i ∈ s, LinearMap.mulLeft ℝ (z i) ∘ₗ dξ i

theorem T_apply (s : Finset Λ) (x : A) : T s x = ∑ i ∈ s, z i * dξ i x := by
  simp [T]

theorem T_mul (s : Finset Λ) (a b : A) : T s (a * b) = T s a * b + inv' a * T s b := by
  simp only [T_apply, dξ_mul, mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  congr 1
  · simp only [mul_assoc]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc, ← mul_assoc, mul_comm_of_even (inv'_z i)]

theorem T_ξ {s : Finset Λ} {v : Λ} (hv : v ∈ s) : T s (ξ v) = z v := by
  simp [T_apply, dξ_ξ, hv]

theorem T_η (s : Finset Λ) (v : Λ) : T s (η v) = 0 := by
  simp [T_apply, dξ_η]

theorem T_one (s : Finset Λ) : T s (1 : A) = 0 := by
  simp [T_apply]

theorem T_ξη {s : Finset Λ} {a b : Λ} (ha : a ∈ s) : T s (ξ a * η b) = z a * η b := by
  rw [T_mul, T_ξ ha, T_η]; simp

theorem T_z {s : Finset Λ} {a : Λ} (ha : a ∈ s) : T s (z a) = -η a := by
  rw [z, map_sub, T_one, T_ξη ha, z_mul_η]; simp

theorem T_Xc {s : Finset Λ} {a b : Λ} (ha : a ∈ s) (hb : b ∈ s) : T s (cv (Xc a b)) = 0 := by
  rw [coe_Xc, dot, map_add, map_sub, map_sub, map_neg, T_one, T_ξη ha, T_ξη hb, T_mul,
    T_z ha, T_z hb, inv'_z]
  simp only [neg_mul, mul_neg]
  rw [← mul_comm_of_even (inv'_z b) (η a)]
  abel

theorem inv'_Xc (a b : Λ) : inv' (cv (Xc a b)) = cv (Xc a b) := by
  simp [coe_Xc, dot, z]

theorem T_prod {ι : Type*} (s : Finset Λ) (t : Finset ι) (f : ι → C Λ)
    (hT : ∀ k ∈ t, T s (cv (f k)) = 0) (hf : ∀ k ∈ t, inv' (cv (f k)) = cv (f k)) :
    T s (cv (∏ k ∈ t, f k)) = 0 := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [T_one]
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, map_mul, T_mul, hT a (Finset.mem_insert_self a t),
      ih (fun k hk => hT k (Finset.mem_insert_of_mem hk))
        (fun k hk => hf k (Finset.mem_insert_of_mem hk))]
    simp

theorem berezin_z_mul_dξ {l : List Λ} {i : Λ} (hi : i ∈ l) (y : A) :
    berezin l (z i * dξ i y) = 0 := by
  rw [berezin_eq_cons_erase hi, intStep, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.mulLeft_apply, ← mul_assoc, inverse_z_mul_z, one_mul, dξ_dξ, map_zero, map_zero]

theorem berezin_T {l : List Λ} {s : Finset Λ} (hs : ∀ i ∈ s, i ∈ l) (y : A) :
    berezin l (T s y) = 0 := by
  rw [T_apply, map_sum]
  exact Finset.sum_eq_zero fun i hi => berezin_z_mul_dξ (hs i hi) y

/-- Ward identity: inserting `z_v` into a `T`-invariant even form gives zero. -/
theorem berezin_z_mul {l : List Λ} {s : Finset Λ} (hs : ∀ i ∈ s, i ∈ l) {v : Λ} (hv : v ∈ s)
    {G : A} (hTG : T s G = 0) : berezin l (z v * G) = 0 := by
  have : z v * G = T s (ξ v * G) := by rw [T_mul, T_ξ hv, hTG, mul_zero, add_zero]
  rw [this, berezin_T hs]

/-- Pinning: for `T`-invariant even forms, one may insert `ξ_v η_v = 1 - z_v`. -/
theorem berezin_pin {l : List Λ} {s : Finset Λ} (hs : ∀ i ∈ s, i ∈ l) {v : Λ} (hv : v ∈ s)
    {G : A} (hTG : T s G = 0) :
    berezin l G = berezin l (ξ v * η v * G) := by
  have : G = z v * G + ξ v * η v * G := by rw [← add_mul, z, sub_add_cancel, one_mul]
  conv_lhs => rw [this]
  rw [map_add, berezin_z_mul hs hv hTG, zero_add]

end

end H02
