module

public import ArborealDecay.Super.ComposeDiff

/-!
# The `ℍ^{2|4}` coordinates

BCHS §2.3 (`refs/BCHS/src/h02.tex` L1201–1300) with `n = 2`, `m = 2`.  At each vertex `i ∈ Λ` we
have two even coordinates `x_i, y_i` and two pairs of odd generators `(ξ¹_i, η¹_i)`,
`(ξ²_i, η²_i)`.  We use the carrier `SG Λ (Λ ⊕ Λ)` of `ArborealDecay.Super.Berezin`: the second
pair is the integrated pair `(ξ_i, η_i)` of `SG`, on which `Q` acts, and the first pair consists of
the parameter generators `ξ¹_i = θ_{inr (inl i)}`, `η¹_i = θ_{inr (inr i)}` (BCHS proof of
Prop. 2.7: "applying the localisation theorem to the variables `(x, y, ξ², η²)`").

* `Rz i p = 1 + x_i² + y_i² - 2 ξ¹_i η¹_i - 2 ξ²_i η²_i` and `zH i p = √(Rz i p)`
  (BCHS (2.39), composition `scomp`);
* `dotH i j p = x_i x_j + y_i y_j + (η¹_i ξ¹_j - ξ¹_i η¹_j) + (η²_i ξ²_j - ξ²_i η²_j) - z_i z_j`
  (BCHS (2.40));
* `Q_zH`, `Q_dotH`: `Q z_i = 0` and `Q (u_i · u_j) = 0`.
-/

@[expose] public section

namespace ArborealDecay.Super

noncomputable section

open CliffordAlgebra Grassmann Finset
open scoped ContDiff

set_option linter.unusedSectionVars false

namespace H24

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- The algebra of the `ℍ^{2|4}` model: the integrated pairs are `(ξ²_i, η²_i) = (ξ_i, η_i)`, the
parameters are `(ξ¹_i, η¹_i)`. -/
abbrev A (Λ : Type*) := SG Λ (Λ ⊕ Λ)

/-- The parameter generator `ξ¹_i`. -/
def ξ1 (i : Λ) : A Λ := gen (.inr (.inl i))

/-- The parameter generator `η¹_i`. -/
def η1 (i : Λ) : A Λ := gen (.inr (.inr i))

/-- `R_i = 1 + x_i² + y_i² - 2 ξ¹_i η¹_i - 2 ξ²_i η²_i`, so that `z_i = √R_i` (BCHS (2.39)). -/
def Rz (i : Λ) (p : Pt Λ) : A Λ :=
  (1 + p (.inl i) ^ 2 + p (.inr i) ^ 2) • (1 : A Λ) - (2 : ℝ) • (ξ1 i * η1 i) -
    (2 : ℝ) • (ξ i * η i)

/-- `z_i = √(1 + x_i² + y_i² - 2 ξ¹_i η¹_i - 2 ξ²_i η²_i)` (BCHS (2.39)). -/
def zH (i : Λ) (p : Pt Λ) : A Λ := scomp Real.sqrt (Rz i p)

/-- The bosonic and `(ξ², η²)` part of the inner product:
`x_i x_j + y_i y_j + η²_i ξ²_j - ξ²_i η²_j`. -/
def σ (i j : Λ) (p : Pt Λ) : A Λ :=
  (p (.inl i) * p (.inl j) + p (.inr i) * p (.inr j)) • (1 : A Λ) + (η i * ξ j - ξ i * η j)

/-- The parameter part of the inner product: `η¹_i ξ¹_j - ξ¹_i η¹_j`. -/
def τ (i j : Λ) : A Λ := η1 i * ξ1 j - ξ1 i * η1 j

/-- The inner product `u_i · u_j = x_i x_j + y_i y_j + ∑_ℓ (η^ℓ_i ξ^ℓ_j - ξ^ℓ_i η^ℓ_j) - z_i z_j`
(BCHS (2.40)). -/
def dotH (i j : Λ) (p : Pt Λ) : A Λ :=
  (p (.inl i) * p (.inl j) + p (.inr i) * p (.inr j)) • (1 : A Λ) +
    (η1 i * ξ1 j - ξ1 i * η1 j) + (η i * ξ j - ξ i * η j) - zH i p * zH j p

theorem dotH_eq (i j : Λ) (p : Pt Λ) : dotH i j p = σ i j p + τ i j - zH i p * zH j p := by
  rw [dotH, σ, τ]; abel

/-! ### Parity and bodies -/

theorem isEven_gen_mul_gen (o o' : (Λ ⊕ Λ) ⊕ (Λ ⊕ Λ)) : IsEven (gen o * gen o' : A Λ) := by
  unfold IsEven; rw [map_mul, inv'_gen, inv'_gen, neg_mul_neg]

theorem isEven_σ (i j : Λ) (p : Pt Λ) : IsEven (σ i j p) :=
  (IsEven.one.smul _).add ((isEven_gen_mul_gen _ _).sub (isEven_gen_mul_gen _ _))

theorem isEven_τ (i j : Λ) : IsEven (τ i j) := (isEven_gen_mul_gen _ _).sub (isEven_gen_mul_gen _ _)

theorem isEven_Rz (i : Λ) (p : Pt Λ) : IsEven (Rz i p) :=
  ((IsEven.one.smul _).sub ((isEven_gen_mul_gen _ _).smul _)).sub ((isEven_gen_mul_gen _ _).smul _)

theorem isEven_zH (i : Λ) (p : Pt Λ) : IsEven (zH i p) := (isEven_Rz i p).scomp _

theorem isEven_dotH (i j : Λ) (p : Pt Λ) : IsEven (dotH i j p) := by
  rw [dotH_eq]
  exact ((isEven_σ i j p).add (isEven_τ i j)).sub ((isEven_zH i p).mul (isEven_zH j p))

theorem body_gen_mul_gen (o o' : (Λ ⊕ Λ) ⊕ (Λ ⊕ Λ)) : body (gen o * gen o' : A Λ) = 0 := by
  rw [map_mul, body_gen, zero_mul]

theorem body_Rz (i : Λ) (p : Pt Λ) : body (Rz i p) = 1 + p (.inl i) ^ 2 + p (.inr i) ^ 2 := by
  simp only [Rz, ξ1, η1, ξ, η, map_sub, map_smul, body_gen_mul_gen, body_one, smul_eq_mul,
    mul_one, mul_zero, sub_zero]

theorem body_Rz_pos (i : Λ) (p : Pt Λ) : 0 < body (Rz i p) := by
  rw [body_Rz]; positivity

theorem body_zH (i : Λ) (p : Pt Λ) : body (zH i p) = √(1 + p (.inl i) ^ 2 + p (.inr i) ^ 2) := by
  rw [zH, body_scomp _ (isNilpotent_soul (isEven_Rz i p)), body_Rz]

theorem body_zH_pos (i : Λ) (p : Pt Λ) : 0 < body (zH i p) := by
  rw [body_zH]; exact Real.sqrt_pos.2 (by positivity)

/-! ### Differentiability -/

theorem contDiffOn_sqrt : ContDiffOn ℝ ∞ Real.sqrt (Set.Ioi 0) := fun _ hx =>
  (Real.contDiffAt_sqrt (ne_of_gt hx)).contDiffWithinAt

theorem contDiffOn_inv : ContDiffOn ℝ ∞ (fun t : ℝ => t⁻¹) (Set.Ioi 0) := fun _ hx =>
  (contDiffAt_inv ℝ (ne_of_gt hx)).contDiffWithinAt

theorem differentiable_quad (a b c d : Λ ⊕ Λ) :
    Differentiable ℝ fun q : Pt Λ => q a * q b + q c * q d := by fun_prop

theorem sdiff_σ (i j : Λ) : SDiff (σ i j) :=
  (SDiff.smul (differentiable_quad _ _ _ _) (SDiff.const _)).add (SDiff.const _)

theorem sdiff_Rz (i : Λ) : SDiff (Rz i) :=
  ((SDiff.smul (by fun_prop) (SDiff.const _)).sub (SDiff.const _)).sub (SDiff.const _)

theorem sdiff_zH (i : Λ) : SDiff (zH i) :=
  SDiff.scomp isOpen_Ioi contDiffOn_sqrt (sdiff_Rz i) (isEven_Rz i) (body_Rz_pos i)

theorem sdiff_dotH (i j : Λ) : SDiff (dotH i j) := by
  have e : dotH i j = fun p => σ i j p + τ i j - zH i p * zH j p := funext (dotH_eq i j)
  rw [e]
  exact ((sdiff_σ i j).add (SDiff.const _)).sub ((sdiff_zH i).mul (sdiff_zH j))

/-! ### `Q`-closedness -/

theorem Q_smul_one {f : Pt Λ → ℝ} (hf : Differentiable ℝ f) (p : Pt Λ) :
    Q (fun q => f q • (1 : A Λ)) p =
      ∑ k, (fderiv ℝ f p (ex k) • ξ k + fderiv ℝ f p (ey k) • η k) := by
  refine sum_congr rfl fun k _ => ?_
  rw [pd_smul_const hf, pd_smul_const hf]
  simp

theorem Q_const_apply (c : A Λ) (p : Pt Λ) :
    Q (fun _ => c) p = ∑ k, (-(p (.inl k) • dη k c) + p (.inr k) • dξ k c) := by
  refine sum_congr rfl fun k _ => ?_
  simp only [pd_const, mul_zero, zero_add]; abel

theorem fderiv_quad (a b c d : Λ ⊕ Λ) (p v : Pt Λ) :
    fderiv ℝ (fun q : Pt Λ => q a * q b + q c * q d) p v = v a * p b + p a * v b + (v c * p d +
      p c * v d) := by
  have ha := hasFDerivAt_apply (𝕜 := ℝ) a p
  have hb := hasFDerivAt_apply (𝕜 := ℝ) b p
  have hc := hasFDerivAt_apply (𝕜 := ℝ) c p
  have hd := hasFDerivAt_apply (𝕜 := ℝ) d p
  have h : HasFDerivAt (fun q : Pt Λ => q a * q b + q c * q d) _ p :=
    (ha.mul hb).add (hc.mul hd)
  rw [h.fderiv]
  simp
  ring

theorem ex_apply (k : Λ) (a : Λ ⊕ Λ) : ex k a = if a = .inl k then 1 else 0 := by
  simp [ex, Pi.single_apply]

theorem ey_apply (k : Λ) (a : Λ ⊕ Λ) : ey k a = if a = .inr k then 1 else 0 := by
  simp [ey, Pi.single_apply]

theorem dη_gen_param (k : Λ) (o : Λ ⊕ Λ) : dη k (gen (.inr o) : A Λ) = 0 := by
  simp [dη, dgen_gen]

theorem dξ_gen_param (k : Λ) (o : Λ ⊕ Λ) : dξ k (gen (.inr o) : A Λ) = 0 := by
  simp [dξ, dgen_gen]

theorem Q_σ (i j : Λ) (p : Pt Λ) : Q (σ i j) p = 0 := by
  have e : σ i j = fun q => (q (.inl i) * q (.inl j) + q (.inr i) * q (.inr j)) • (1 : A Λ) +
      (η i * ξ j - ξ i * η j) := rfl
  rw [e, Q_add (SDiff.smul (differentiable_quad _ _ _ _) (SDiff.const _)) (SDiff.const _),
    Q_smul_one (differentiable_quad _ _ _ _), Q_const_apply]
  have hA : ∀ k, fderiv ℝ (fun q : Pt Λ => q (.inl i) * q (.inl j) + q (.inr i) * q (.inr j)) p
      (ex k) • (ξ k : A Λ) + fderiv ℝ (fun q : Pt Λ => q (.inl i) * q (.inl j) +
        q (.inr i) * q (.inr j)) p (ey k) • η k =
      (if k = i then p (.inl j) else 0) • ξ k + (if k = j then p (.inl i) else 0) • ξ k +
      ((if k = i then p (.inr j) else 0) • η k + (if k = j then p (.inr i) else 0) • η k) := by
    intro k
    simp only [fderiv_quad, ex_apply, ey_apply, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
      ite_false, eq_comm (a := i), eq_comm (a := j)]
    rcases eq_or_ne k i with rfl | hi <;> rcases eq_or_ne k j with rfl | hj <;>
      (simp [*, Ne.symm]; try module)
  have hB : ∀ k, -(p (.inl k) • dη k (η i * ξ j - ξ i * η j : A Λ)) +
      p (.inr k) • dξ k (η i * ξ j - ξ i * η j : A Λ) =
      -((if k = i then p (.inl i) else 0) • ξ j + (if k = j then p (.inl j) else 0) • ξ i +
      ((if k = j then p (.inr j) else 0) • η i + (if k = i then p (.inr i) else 0) • η j)) := by
    intro k
    simp only [map_sub, dη_mul, dξ_mul, dη_η, dη_ξ, dξ_ξ, dξ_η, inv'_η, inv'_ξ]
    rcases eq_or_ne k i with rfl | hi <;> rcases eq_or_ne k j with rfl | hj <;>
      (simp [*, Ne.symm]; try module)
  simp only [hA, hB, sum_add_distrib, sum_neg_distrib, ite_smul, zero_smul, sum_ite_eq',
    mem_univ, ite_true]
  abel

theorem Q_τ (i j : Λ) (p : Pt Λ) : Q (fun _ => τ i j) p = 0 := by
  refine Q_const (fun k => ⟨?_, ?_⟩) p
  · simp [τ, ξ1, η1, dξ_mul, dξ_gen_param]
  · simp [τ, ξ1, η1, dη_mul, dη_gen_param]

theorem Rz_eq (i : Λ) (p : Pt Λ) : Rz i p = 1 + σ i i p + τ i i := by
  have h1 : (η i * ξ i : A Λ) = -(ξ i * η i) := gen_anticomm _ _
  have h2 : (η1 i * ξ1 i : A Λ) = -(ξ1 i * η1 i) := gen_anticomm _ _
  rw [Rz, σ, τ, h1, h2, add_smul, add_smul, one_smul]
  have : p (.inl i) * p (.inl i) + p (.inr i) * p (.inr i) = p (.inl i) ^ 2 + p (.inr i) ^ 2 := by
    ring
  rw [this, add_smul]
  module

theorem Q_Rz (i : Λ) (p : Pt Λ) : Q (Rz i) p = 0 := by
  have e : Rz i = fun q => (1 : A Λ) + σ i i q + τ i i := funext (Rz_eq i)
  rw [e, Q_add ((SDiff.const 1).add (sdiff_σ i i)) (SDiff.const _),
    Q_add (SDiff.const 1) (sdiff_σ i i), Q_τ, Q_σ]
  simpa using Q_algebraMap (N := Λ) (P := Λ ⊕ Λ) 1 p

/-- `Q z_i = 0`. -/
theorem Q_zH (i : Λ) (p : Pt Λ) : Q (zH i) p = 0 := by
  rw [show zH i = fun q => scomp Real.sqrt (Rz i q) from rfl,
    Q_scomp isOpen_Ioi contDiffOn_sqrt (sdiff_Rz i) (isEven_Rz i) (body_Rz_pos i), Q_Rz, mul_zero]

/-- `Q (u_i · u_j) = 0`. -/
theorem Q_dotH (i j : Λ) (p : Pt Λ) : Q (dotH i j) p = 0 := by
  have e : dotH i j = fun p => σ i j p + τ i j - zH i p * zH j p := funext (dotH_eq i j)
  rw [e, Q_sub ((sdiff_σ i j).add (SDiff.const _)) ((sdiff_zH i).mul (sdiff_zH j)),
    Q_add (sdiff_σ i j) (SDiff.const _), Q_mul (sdiff_zH i) (sdiff_zH j), Q_σ, Q_τ, Q_zH, Q_zH]
  simp

end H24

end

end ArborealDecay.Super

end
