module

public import ArborealDecay.Super.Calculus

/-!
# Invariance of the Lebesgue integral under nilpotent shifts

Let `A` be a finite-dimensional `ℝ`-algebra (in applications a Grassmann algebra `SG N P`), `F`
an `A`-valued function on `E → ℝ`, `v` a direction, `g` a scalar function and `n ∈ A` with
`n ^ K = 0`.  The composition `F(x + g(x) n v)` is the finite Taylor sum (BHS App. A, (A.12))

  `shiftT v g n K F x = ∑_{m < K} (g(x)^m / m!) • (∂_v^m F(x) · n^m)`.

**Main result** (`integral_shiftT_mul`): the change of generators `x ↦ x + g(x) n` along `v` has
Berezinian `1 + ∂_v g · n` (BHS Example A.6 (`ex:chvarmixed`), `refs/BHS/src/isomorphisms.tex`
L3791–3840), i.e. coefficientwise

  `∫ ℓ (F(x + g(x) n) · (1 + ∂_v g(x) n)) dx = ∫ ℓ (F(x)) dx`.

The proof is the BHS one: pointwise,
`F(x + g n)(1 + g' n) = F(x) + ∑_{m < K} ∂_v (g^{m+1}/(m+1)! · ∂_v^m F · n^{m+1})` (`shiftT_mul_eq`),
and `∫ ∂_v f = 0` for `f` in `Decay`.  `n` need not be even or central: it always multiplies from
the right.

The special case `g ≡ 1` is the translation invariance `∫ F(x + n v) dx = ∫ F(x) dx`
(`integral_shiftT_const`).

**Use in the horospherical step.** After the bosonic change of variables `(t, s) ↦ (x, y)`, the
remaining super-change is `x ↦ x − e^{−t(x,y)} n` (`n = ∑_γ ξ^γ η^γ`-type even element), whose
Berezinian `1 + e^{−t} n / z` is exactly `1 + ∂_x g · n` for `g = −1/(x + z)`.
-/

@[expose] public section

namespace ArborealDecay.Horo

noncomputable section

open MeasureTheory Finset ArborealDecay.Super

set_option linter.unusedSectionVars false

variable {E : Type*} [Fintype E]
variable {A : Type*} [Ring A] [Algebra ℝ A] [FiniteDimensional ℝ A]

local notation "X" => E → ℝ

/-- The iterated partial derivative `∂_v^m F`. -/
def pdn (v : X) : ℕ → (X → A) → X → A
  | 0, F => F
  | m + 1, F => pd v (pdn v m F)

@[simp] theorem pdn_zero (v : X) (F : X → A) : pdn v 0 F = F := rfl

theorem pdn_succ (v : X) (m : ℕ) (F : X → A) : pdn v (m + 1) F = pd v (pdn v m F) := rfl

/-- `F(x + g(x) n v)`, defined as the Taylor sum `∑_{m < K} (g(x)^m / m!) • (∂_v^m F(x) · n^m)`. -/
def shiftT (v : X) (g : X → ℝ) (n : A) (K : ℕ) (F : X → A) (x : X) : A :=
  ∑ m ∈ range K, (g x ^ m / m.factorial) • (pdn v m F x * n ^ m)

/-- The primitive whose `∂_v` produces the order-`(m+1)` correction. -/
def shiftPrim (v : X) (g : X → ℝ) (n : A) (F : X → A) (m : ℕ) (x : X) : A :=
  (g x ^ (m + 1) / (m + 1).factorial) • (pdn v m F x * n ^ (m + 1))

/-- A scalar telescoping identity. -/
theorem telescope (K : ℕ) (c a b : ℕ → ℝ) (d : ℝ) (hc : c 0 = 1) (ha : a K = 0) :
    ∑ m ∈ range K, c m * a m + d * ∑ m ∈ range K, c m * b m =
      a 0 + ∑ m ∈ range K, (c m * d * b m + c (m + 1) * a (m + 1)) := by
  have h1 : ∑ m ∈ range K, c (m + 1) * a (m + 1) = ∑ m ∈ range K, c m * a m - c 0 * a 0 := by
    have := Finset.sum_range_succ' (fun m => c m * a m) K
    rw [Finset.sum_range_succ, ha, mul_zero, add_zero] at this
    linarith
  rw [Finset.sum_add_distrib, h1, hc, Finset.mul_sum]
  have : ∑ m ∈ range K, c m * d * b m = ∑ m ∈ range K, d * (c m * b m) :=
    Finset.sum_congr rfl fun m _ => by ring
  rw [this]; ring

/-- The derivative of the primitive, coefficientwise. -/
theorem fderiv_dual_shiftPrim (v : X) {g : X → ℝ} (hg : Differentiable ℝ g) (n : A) {F : X → A}
    {m : ℕ} (hd : SDiff (pdn v m F)) (ℓ : Module.Dual ℝ A) (x : X) :
    fderiv ℝ (fun y => ℓ (shiftPrim v g n F m y)) x v =
      (g x ^ m / m.factorial) * fderiv ℝ g x v * ℓ (pdn v m F x * n ^ (m + 1)) +
        (g x ^ (m + 1) / (m + 1).factorial) * ℓ (pdn v (m + 1) F x * n ^ (m + 1)) := by
  set L : Module.Dual ℝ A := ℓ ∘ₗ LinearMap.mulRight ℝ (n ^ (m + 1))
  have hb : HasFDerivAt (fun y => L (pdn v m F y)) (fderiv ℝ (fun y => L (pdn v m F y)) x) x :=
    (hd L x).hasFDerivAt
  have hc : HasFDerivAt (fun y => ((m + 1).factorial : ℝ)⁻¹ * (g y ^ (m + 1) * L (pdn v m F y)))
      _ x := (((hg x).hasFDerivAt.pow (m + 1)).mul hb).const_mul (((m + 1).factorial : ℝ)⁻¹)
  have e : (fun y => ℓ (shiftPrim v g n F m y)) =
      fun y => ((m + 1).factorial : ℝ)⁻¹ * (g y ^ (m + 1) * L (pdn v m F y)) := by
    funext y
    simp only [shiftPrim, map_smul, smul_eq_mul, L, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.mulRight_apply]
    ring
  rw [e, hc.fderiv]
  have hdp : fderiv ℝ (fun y => L (pdn v m F y)) x v = ℓ (pdn v (m + 1) F x * n ^ (m + 1)) := by
    rw [← dual_pd hd L v x, pdn_succ]; rfl
  simp only [FunLike.coe_smul, FunLike.coe_add, Pi.smul_apply, Pi.add_apply, smul_eq_mul, hdp,
    Nat.add_sub_cancel]
  simp only [L, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulRight_apply]
  rw [Nat.factorial_succ]
  push_cast
  have : (m.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- **Pointwise identity**: `F(x + g n)(1 + ∂_v g · n) = F + ∑_{m<K} ∂_v (shiftPrim m)`,
coefficientwise. -/
theorem dual_shiftT_mul_eq (v : X) {g : X → ℝ} (hg : Differentiable ℝ g) {n : A} {K : ℕ}
    (hn : n ^ K = 0) {F : X → A} (hd : ∀ m < K, SDiff (pdn v m F)) (ℓ : Module.Dual ℝ A)
    (x : X) :
    ℓ (shiftT v g n K F x * (1 + fderiv ℝ g x v • n)) =
      ℓ (F x) + ∑ m ∈ range K, fderiv ℝ (fun y => ℓ (shiftPrim v g n F m y)) x v := by
  rw [Finset.sum_congr rfl fun m hm =>
    fderiv_dual_shiftPrim v hg n (hd m (Finset.mem_range.1 hm)) ℓ x]
  have e1 : shiftT v g n K F x * (1 + fderiv ℝ g x v • n) =
      shiftT v g n K F x + fderiv ℝ g x v •
        ∑ m ∈ range K, (g x ^ m / m.factorial) • (pdn v m F x * n ^ (m + 1)) := by
    rw [mul_add, mul_one, shiftT, mul_smul_comm, Finset.sum_mul]
    congr 2
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_mul_assoc, mul_assoc, pow_succ]
  rw [e1, map_add, map_smul, shiftT, map_sum, map_sum, smul_eq_mul]
  simp only [map_smul, smul_eq_mul]
  have := telescope K (fun m => g x ^ m / m.factorial) (fun m => ℓ (pdn v m F x * n ^ m))
    (fun m => ℓ (pdn v m F x * n ^ (m + 1))) (fderiv ℝ g x v) (by simp) (by simp [hn])
  simp only [pow_zero, mul_one] at this
  rw [this]; rfl

/-- **Nilpotent change of generators** `x ↦ x + g(x) n` along `v`, with Berezinian
`1 + ∂_v g · n` (BHS Example A.6), coefficientwise. -/
theorem integral_dual_shiftT_mul (v : X) {g : X → ℝ} (hg : Differentiable ℝ g) {n : A} {K : ℕ}
    (hn : n ^ K = 0) {F : X → A} (hd : ∀ m < K, SDiff (pdn v m F)) (hF : SInt F volume)
    (hdec : ∀ m < K, SDecay (shiftPrim v g n F m)) (ℓ : Module.Dual ℝ A) :
    ∫ x, ℓ (shiftT v g n K F x * (1 + fderiv ℝ g x v • n)) = ∫ x, ℓ (F x) := by
  simp_rw [dual_shiftT_mul_eq v hg hn hd ℓ]
  rw [integral_add (hF ℓ), integral_finsetSum]
  · rw [Finset.sum_eq_zero fun m hm =>
      (hdec m (Finset.mem_range.1 hm) ℓ).integral_fderiv_eq_zero v, add_zero]
  · exact fun m hm => (hdec m (Finset.mem_range.1 hm) ℓ).integrable_fderiv v
  · exact integrable_finsetSum _ fun m hm => (hdec m (Finset.mem_range.1 hm) ℓ).integrable_fderiv v

theorem sint_shiftT_mul_aux (v : X) {g : X → ℝ} (hg : Differentiable ℝ g) {n : A} {K : ℕ}
    (hn : n ^ K = 0) {F : X → A} (hd : ∀ m < K, SDiff (pdn v m F)) (hF : SInt F volume)
    (hdec : ∀ m < K, SDecay (shiftPrim v g n F m)) :
    SInt (fun x => shiftT v g n K F x * (1 + fderiv ℝ g x v • n)) volume := fun ℓ => by
  simp_rw [dual_shiftT_mul_eq v hg hn hd ℓ]
  exact (hF ℓ).add
    (integrable_finsetSum _ fun m hm => (hdec m (Finset.mem_range.1 hm) ℓ).integrable_fderiv v)

/-- `sint` form of `integral_dual_shiftT_mul`. -/
theorem integral_shiftT_mul (v : X) {g : X → ℝ} (hg : Differentiable ℝ g) {n : A} {K : ℕ}
    (hn : n ^ K = 0) {F : X → A} (hd : ∀ m < K, SDiff (pdn v m F)) (hF : SInt F volume)
    (hdec : ∀ m < K, SDecay (shiftPrim v g n F m)) :
    sint (fun x => shiftT v g n K F x * (1 + fderiv ℝ g x v • n)) volume = sint F volume := by
  refine ext_dual fun ℓ => ?_
  rw [dual_sint (sint_shiftT_mul_aux v hg hn hd hF hdec), dual_sint hF,
    integral_dual_shiftT_mul v hg hn hd hF hdec]

/-- **Translation by a nilpotent** (`g ≡ 1`): `∫ F(x + n v) dx = ∫ F(x) dx`, provided
`∂_v^m F` decays for `m < K`. -/
theorem integral_shiftT_const (v : X) {n : A} {K : ℕ} (hn : n ^ K = 0) {F : X → A}
    (hdec : ∀ m < K, SDecay (pdn v m F)) (hF : SInt F volume) :
    sint (shiftT v (fun _ => 1) n K F) volume = sint F volume := by
  have hdec' : ∀ m < K, SDecay (shiftPrim v (fun _ => 1) n F m) := fun m hm => by
    have := ((hdec m hm).map (LinearMap.mulRight ℝ (n ^ (m + 1)))).smul
      (Temp.const (((m + 1).factorial : ℝ)⁻¹))
    refine fun ℓ => ?_
    convert this ℓ using 2 with x
    simp [shiftPrim, div_eq_inv_mul]
  have h := integral_shiftT_mul v (differentiable_const 1) hn (fun m hm => (hdec m hm).sdiff) hF
    hdec'
  simpa using h

end

end ArborealDecay.Horo

end
