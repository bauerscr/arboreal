module

public import Mathlib
public import ArborealDecay.Grassmann.Algebra

/-!
# Grassmann algebras with finitely many generators

For a finite type `O` of odd generators, `Gr O` is the exterior algebra over `ℝ` of `O → ℝ`;
the generator `θ_o` is `gen o = ι (Pi.single o 1)` and the fermionic derivative `∂_{θ_o}` is the
left contraction `dgen o` with the coordinate functional at `o`.  It is an odd derivation:
`∂(ab) = (∂a) b + inv' a ∂b`, where `inv'` is the grade involution.

We also define, for a set `S` of generators, the algebra homomorphism `killA S` which sends the
generators in `S` to `0` and fixes the others.  For instance the degree-zero part (in the
generators of `S`) of `F` is `killA S F`.

Finally `Gr O` is finite-dimensional, which lets us treat `Gr O`-valued functions through their
coordinates in a fixed basis (see `ArborealDecay.Super.Calculus`).
-/

@[expose] public section

namespace ArborealDecay.Super

noncomputable section

open CliffordAlgebra Grassmann

/-- The Grassmann algebra with odd generators indexed by `O`. -/
abbrev Gr (O : Type*) := ExteriorAlgebra ℝ (O → ℝ)

variable {O : Type*}

/-- The generator `θ_o`. -/
def gen [DecidableEq O] (o : O) : Gr O := ExteriorAlgebra.ι ℝ (Pi.single o 1)

/-- The fermionic derivative `∂_{θ_o}` (left contraction). -/
def dgen (o : O) : Gr O →ₗ[ℝ] Gr O :=
  contractLeft (LinearMap.proj (R := ℝ) (φ := fun _ : O => ℝ) o)

/-! ### Finite-dimensionality -/

instance instModuleFiniteGr [Finite O] : Module.Finite ℝ (Gr O) := by
  have := Fintype.ofFinite O
  let b : Module.Basis (Fin (Fintype.card O)) ℝ (O → ℝ) :=
    (Pi.basisFun ℝ O).reindex (Fintype.equivFin O)
  exact Module.Finite.of_basis (Module.Basis.ExteriorAlgebra b)

/-! ### Generators and derivatives -/

section Gen

variable [DecidableEq O]

@[simp] theorem inv'_gen (o : O) : inv' (gen o) = -gen o := inv'_ι _

theorem gen_mul_gen_self (o : O) : gen o * gen o = 0 := ExteriorAlgebra.ι_sq_zero _

theorem gen_anticomm (o o' : O) : gen o * gen o' = -(gen o' * gen o) := ι_anticomm _ _

theorem gen_mul_eq (o : O) (x : Gr O) : gen o * x = inv' x * gen o := ι_mul_eq _ _

theorem dgen_gen (o o' : O) : dgen o (gen o') = if o = o' then 1 else 0 := by
  simp only [dgen, gen, ExteriorAlgebra.ι, contractLeft_ι, LinearMap.proj_apply]
  by_cases h : o = o'
  · subst h; simp
  · simp [h]

@[simp] theorem dgen_gen_self (o : O) : dgen o (gen o) = 1 := by simp [dgen_gen]

theorem dgen_gen_of_ne {o o' : O} (h : o ≠ o') : dgen o (gen o') = 0 := by simp [dgen_gen, h]

end Gen

theorem dgen_mul (o : O) (a b : Gr O) : dgen o (a * b) = dgen o a * b + inv' a * dgen o b :=
  Grassmann.contractLeft_mul _ a b

@[simp] theorem dgen_one (o : O) : dgen o (1 : Gr O) = 0 := by simp [dgen]

@[simp] theorem dgen_algebraMap (o : O) (r : ℝ) : dgen o (algebraMap ℝ (Gr O) r) = 0 := by
  simp [dgen]

theorem dgen_dgen (o : O) (x : Gr O) : dgen o (dgen o x) = 0 := contractLeft_contractLeft _ _

theorem dgen_comm (o o' : O) (x : Gr O) : dgen o (dgen o' x) = -dgen o' (dgen o x) :=
  contractLeft_comm _ _ _

theorem dgen_inv' (o : O) (x : Gr O) : dgen o (inv' x) = -inv' (dgen o x) :=
  Grassmann.contractLeft_inv' _ x

/-- Even elements are central. -/
theorem mul_comm_of_even' {x : Gr O} (hx : inv' x = x) (y : Gr O) : x * y = y * x :=
  Grassmann.mul_comm_of_even hx y

/-! ### Killing generators -/

/-- The linear map `O → ℝ` zeroing the coordinates in `S`. -/
def killV (S : Set O) : (O → ℝ) →ₗ[ℝ] (O → ℝ) where
  toFun v := Sᶜ.indicator v
  map_add' v w := Set.indicator_add _ v w
  map_smul' c v := Set.indicator_const_smul _ c v

theorem killV_apply (S : Set O) (v : O → ℝ) (o : O) : killV S v o = Sᶜ.indicator v o := rfl

/-- The algebra homomorphism killing the generators in `S`. -/
def killA (S : Set O) : Gr O →ₐ[ℝ] Gr O := ExteriorAlgebra.map (killV S)

theorem killA_killA (S T : Set O) (x : Gr O) : killA S (killA T x) = killA (S ∪ T) x := by
  have : (killV S).comp (killV T) = killV (S ∪ T) := by
    ext v o
    show Sᶜ.indicator (Tᶜ.indicator v) o = _
    rw [killV_apply, Set.indicator_indicator, Set.compl_union, Set.inter_comm]
  change ((killA S).comp (killA T)) x = _
  rw [killA, killA, ExteriorAlgebra.map_comp_map, this]; rfl

theorem killA_comm (S T : Set O) (x : Gr O) : killA S (killA T x) = killA T (killA S x) := by
  rw [killA_killA, killA_killA, Set.union_comm]

@[simp] theorem killA_empty (x : Gr O) : killA ∅ x = x := by
  have : killV (∅ : Set O) = LinearMap.id := by
    ext v o; rw [killV_apply, Set.compl_empty, Set.indicator_univ]; rfl
  rw [killA, this, ExteriorAlgebra.map_id]; rfl

theorem inv'_killA (S : Set O) (x : Gr O) : inv' (killA S x) = killA S (inv' x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι v => simp [killA, ExteriorAlgebra.ι]
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb, map_mul, map_mul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

section Kill

variable [DecidableEq O]

theorem killA_gen_of_mem {S : Set O} {o : O} (h : o ∈ S) : killA S (gen o) = 0 := by
  simp only [killA, gen, ExteriorAlgebra.map_apply_ι]
  rw [← map_zero (ExteriorAlgebra.ι ℝ (M := O → ℝ))]
  congr 1; ext o'
  rw [killV_apply, Pi.zero_apply]
  by_cases h' : o' = o
  · subst h'; exact Set.indicator_of_notMem (Set.notMem_compl_iff.2 h) _
  · rw [Set.indicator_apply_eq_zero]; intro; simp [h']

theorem killA_gen_of_notMem {S : Set O} {o : O} (h : o ∉ S) : killA S (gen o) = gen o := by
  simp only [killA, gen, ExteriorAlgebra.map_apply_ι]
  congr 1; ext o'
  rw [killV_apply]
  by_cases h' : o' = o
  · subst h'; exact Set.indicator_of_mem (Set.mem_compl h) _
  · rw [Set.indicator_apply_eq_zero.2]; · simp [h']
    intro; simp [h']

end Kill

/-- A derivative in a killed generator vanishes on the image of `killA`. -/
theorem dgen_killA {S : Set O} {o : O} (h : o ∈ S) (x : Gr O) : dgen o (killA S x) = 0 := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι v =>
    simp only [killA, ExteriorAlgebra.map_apply_ι, dgen, ExteriorAlgebra.ι, contractLeft_ι,
      LinearMap.proj_apply, killV_apply, Set.indicator_of_notMem (Set.notMem_compl_iff.2 h),
      map_zero]
  | mul a b ha hb => rw [map_mul, dgen_mul, ha, hb, mul_zero, zero_mul, add_zero]
  | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]

/-- `killA S` commutes with the derivative in a generator not in `S`. -/
theorem dgen_killA_of_notMem {S : Set O} {o : O} (h : o ∉ S) (x : Gr O) :
    dgen o (killA S x) = killA S (dgen o x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι v =>
    simp only [killA, ExteriorAlgebra.map_apply_ι, dgen, ExteriorAlgebra.ι, contractLeft_ι,
      LinearMap.proj_apply, killV_apply, Set.indicator_of_mem (Set.mem_compl h), AlgHom.commutes]
  | mul a b ha hb =>
    rw [map_mul, dgen_mul, ha, hb, dgen_mul, map_add, map_mul, map_mul, inv'_killA]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

end

end ArborealDecay.Super

end
