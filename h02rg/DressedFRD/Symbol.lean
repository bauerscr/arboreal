import FRD.BoundsFourier
import FRD.LatticeSum

/-!
# Symbols of translation invariant operators on the torus

Translation invariant operators on `ℂ^Λ`, `Λ = (ℤ/nℤ)^d`, are identified with their Fourier
symbols `w : Torus d n → ℂ` (`Sym d n`). Products of operators are products of symbols.

* `kern w` is the convolution kernel `k(x) = |Λ|^{-1} ∑_m w(m) e^{ik·x}`, and `kern_mul` shows
  that products of symbols are convolutions of kernels.
* `rng w` is the range `max{|x|_∞ : k(x) ≠ 0}`; it is subadditive under products
  (`rng_mul_le`), and `-Δ` has range `≤ 1` (`rng_lam_le`).
* `sigma α` is the symbol `σ_α(p) = ∏_e (e^{ip·e} - 1)^{α(e)}` of `∇^α`, and
  `dop α (kern w) = kern (σ_α w)` (`dop_kern`).
* `norm_le_sum_kern`: `|w(m)| ≤ ∑_x |k(x)|`.
-/

namespace DressedFRD

noncomputable section

open Finset Complex FRD Grassmann ComplexConjugate

variable {d n : ℕ} [NeZero n]

/-- Fourier symbols on the torus `Torus d n`. -/
abbrev Sym (d n : ℕ) := Torus d n → ℂ

/-- The convolution kernel of a symbol. -/
def kern (w : Sym d n) (x : Torus d n) : ℂ := ((n : ℂ) ^ d)⁻¹ * ∑ m, w m * char m x

theorem npow_ne_zero : ((n : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne n))

/-- `∑_x e^{ik·x} \overline{e^{ik'·x}} = |Λ| δ_{k,k'}`. -/
theorem sum_char_mul_conj (m m' : Torus d n) :
    ∑ x, char m x * conj (char m' x) = if m = m' then (n : ℂ) ^ d else 0 := by
  have : ∀ x, char m x * conj (char m' x) = char (m - m') x := by
    intro x; rw [sub_eq_add_neg, char_add_left, char_neg_left]
  simp only [this, sum_char, sub_eq_zero]

/-- Fourier inversion: the symbol is recovered from the kernel. -/
theorem sum_kern_mul_conj (w : Sym d n) (m : Torus d n) :
    ∑ x, kern w x * conj (char m x) = w m := by
  simp only [kern, mul_assoc, ← mul_sum, sum_mul]
  rw [sum_comm]
  simp only [← mul_sum, sum_char_mul_conj, mul_ite, mul_zero, sum_ite_eq',
    mem_univ, if_true]
  rw [mul_comm (w m), ← mul_assoc, inv_mul_cancel₀ npow_ne_zero, one_mul]

theorem kern_add (w w' : Sym d n) (x : Torus d n) : kern (w + w') x = kern w x + kern w' x := by
  simp [kern, add_mul, sum_add_distrib, mul_add]

theorem kern_smul (c : ℂ) (w : Sym d n) (x : Torus d n) : kern (c • w) x = c * kern w x := by
  simp only [kern, Pi.smul_apply, smul_eq_mul, mul_assoc, ← mul_sum]; ring

theorem kern_sum {ι : Type*} (s : Finset ι) (w : ι → Sym d n) (x : Torus d n) :
    kern (∑ i ∈ s, w i) x = ∑ i ∈ s, kern (w i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [kern]
  | insert i s hi ih => rw [sum_insert hi, kern_add, ih, sum_insert hi]

theorem kern_neg (w : Sym d n) (x : Torus d n) : kern (-w) x = -kern w x := by
  have := kern_smul (-1) w x; simpa using this

theorem kern_sub (w w' : Sym d n) (x : Torus d n) : kern (w - w') x = kern w x - kern w' x := by
  rw [sub_eq_add_neg, kern_add, kern_neg, ← sub_eq_add_neg]

/-- Products of symbols are convolutions of kernels. -/
theorem kern_mul (w w' : Sym d n) (x : Torus d n) :
    kern (w * w') x = ∑ y, kern w y * kern w' (x - y) := by
  set c : ℂ := ((n : ℂ) ^ d)⁻¹
  have hc : c * (n : ℂ) ^ d = 1 := inv_mul_cancel₀ npow_ne_zero
  symm
  calc ∑ y, kern w y * kern w' (x - y)
      = ∑ y, ∑ m, ∑ m', (c * c * (w m * w' m' * char m' x)) * (char m y * conj (char m' y)) := by
        refine sum_congr rfl fun y _ => ?_
        simp only [kern]
        rw [mul_mul_mul_comm, sum_mul_sum, mul_sum]
        refine sum_congr rfl fun m _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun m' _ => ?_
        rw [char_sub_right]; ring
    _ = ∑ m, ∑ m', ∑ y, (c * c * (w m * w' m' * char m' x)) * (char m y * conj (char m' y)) := by
        rw [sum_comm]; exact sum_congr rfl fun m _ => sum_comm
    _ = ∑ m, ∑ m', (c * c * (w m * w' m' * char m' x)) * (if m = m' then (n : ℂ) ^ d else 0) := by
        simp only [← mul_sum, sum_char_mul_conj]
    _ = ∑ m, c * c * (w m * w' m * char m x) * (n : ℂ) ^ d := by
        simp only [mul_ite, mul_zero, sum_ite_eq, mem_univ, if_true]
    _ = kern (w * w') x := by
        simp only [kern, Pi.mul_apply, mul_sum]
        refine sum_congr rfl fun m _ => ?_
        rw [show c * c * (w m * w' m * char m x) * (n : ℂ) ^ d =
          c * (w m * w' m * char m x) * (c * (n : ℂ) ^ d) by ring, hc, mul_one]

/-! ### Range -/

/-- The range `max{|x|_∞ : k(x) ≠ 0}` of a symbol. -/
def rng (w : Sym d n) : ℕ := (univ.filter fun x => kern w x ≠ 0).sup supNorm

theorem supNorm_le_rng {w : Sym d n} {x : Torus d n} (hx : kern w x ≠ 0) : supNorm x ≤ rng w :=
  Finset.le_sup (f := supNorm) (by simpa using hx)

theorem kern_eq_zero_of_rng_lt {w : Sym d n} {x : Torus d n} (hx : rng w < supNorm x) :
    kern w x = 0 := by
  by_contra h; exact absurd (supNorm_le_rng h) (by omega)

theorem rng_le_iff {w : Sym d n} {R : ℕ} : rng w ≤ R ↔ ∀ x, R < supNorm x → kern w x = 0 := by
  constructor
  · intro h x hx; exact kern_eq_zero_of_rng_lt (lt_of_le_of_lt h hx)
  · intro h
    refine Finset.sup_le fun x hx => ?_
    simp only [mem_filter, mem_univ, true_and] at hx
    by_contra hlt; exact hx (h x (by omega))

theorem rng_add_le (w w' : Sym d n) : rng (w + w') ≤ max (rng w) (rng w') := by
  refine rng_le_iff.2 fun x hx => ?_
  rw [kern_add, kern_eq_zero_of_rng_lt (by omega), kern_eq_zero_of_rng_lt (by omega), add_zero]

theorem rng_smul_le (c : ℂ) (w : Sym d n) : rng (c • w) ≤ rng w := by
  refine rng_le_iff.2 fun x hx => ?_
  rw [kern_smul, kern_eq_zero_of_rng_lt hx, mul_zero]

theorem rng_neg (w : Sym d n) : rng (-w) ≤ rng w := by
  refine rng_le_iff.2 fun x hx => ?_
  rw [kern_neg, kern_eq_zero_of_rng_lt hx, neg_zero]

theorem rng_sub_le (w w' : Sym d n) : rng (w - w') ≤ max (rng w) (rng w') := by
  refine rng_le_iff.2 fun x hx => ?_
  rw [kern_sub, kern_eq_zero_of_rng_lt (by omega), kern_eq_zero_of_rng_lt (by omega), sub_zero]

theorem rng_sum_le {ι : Type*} (s : Finset ι) (w : ι → Sym d n) {R : ℕ}
    (h : ∀ i ∈ s, rng (w i) ≤ R) : rng (∑ i ∈ s, w i) ≤ R := by
  refine rng_le_iff.2 fun x hx => ?_
  rw [kern_sum]
  exact sum_eq_zero fun i hi => kern_eq_zero_of_rng_lt (lt_of_le_of_lt (h i hi) hx)

/-- The range is subadditive under products. -/
theorem rng_mul_le (w w' : Sym d n) : rng (w * w') ≤ rng w + rng w' := by
  refine rng_le_iff.2 fun x hx => ?_
  rw [kern_mul]
  refine sum_eq_zero fun y _ => ?_
  by_cases hy : kern w y = 0
  · rw [hy, zero_mul]
  · have h1 := supNorm_le_rng hy
    have h2 : rng w' < supNorm (x - y) := by
      have := supNorm_add_le y (x - y)
      rw [add_sub_cancel] at this
      omega
    rw [kern_eq_zero_of_rng_lt h2, mul_zero]

theorem rng_prod_le {ι : Type*} (s : Finset ι) (w : ι → Sym d n) :
    rng (∏ i ∈ s, w i) ≤ ∑ i ∈ s, rng (w i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine rng_le_iff.2 fun x hx => ?_
    have hx0 : x ≠ 0 := by rintro rfl; rw [supNorm_zero] at hx; omega
    simp only [prod_empty, kern, Pi.one_apply, one_mul, sum_char_left, if_neg hx0, mul_zero]
  | insert i s hi ih =>
    rw [prod_insert hi, sum_insert hi]
    exact (rng_mul_le _ _).trans (by omega)

theorem rng_pow_le (w : Sym d n) (k : ℕ) : rng (w ^ k) ≤ k * rng w := by
  have := rng_prod_le (range k) (fun _ => w)
  simpa [prod_const, sum_const, card_range] using this

/-- Constant symbols have range `0`. -/
theorem rng_const (c : ℂ) : rng (fun _ : Torus d n => c) = 0 := by
  refine Nat.le_zero.1 (rng_le_iff.2 fun x hx => ?_)
  have hx0 : x ≠ 0 := by rintro rfl; rw [supNorm_zero] at hx; omega
  simp only [kern, ← mul_sum, sum_char_left, if_neg hx0, mul_zero]

/-- The kernel of `-Δ` is the matrix `negLap`. -/
theorem kern_lam (x : Torus d n) : kern (fun m => (lam m : ℂ)) x = (negLap x 0 : ℂ) := by
  rw [negLap_eq_fmat, fmat_complex lam_even, sub_zero]; rfl

/-- `-Δ` has range at most `1`. -/
theorem rng_lam_le : rng (fun m : Torus d n => (lam m : ℂ)) ≤ 1 := by
  refine rng_le_iff.2 fun x hx => ?_
  rw [kern_lam]
  have hx0 : x ≠ 0 := by rintro rfl; rw [supNorm_zero] at hx; omega
  have he : ∀ e : Dir d, (0 : Torus d n) ≠ x + dirVec e := by
    intro e h
    have : x = -dirVec e := by rw [eq_neg_iff_add_eq_zero, h]
    rw [this, supNorm_neg] at hx
    exact absurd (supNorm_dirVec_le e) (by omega)
  simp [negLap, hx0, he]

/-! ### Derivatives -/

/-- The symbol of `∇^α`: `σ_α(p) = ∏_e (e^{ip·e} - 1)^{α(e)}`. -/
def sigma (α : Dir d → ℕ) (m : Torus d n) : ℂ := ∏ e, (char m (dirVec e) - 1) ^ α e

theorem dop_kern (α : Dir d → ℕ) (w : Sym d n) (x : Torus d n) :
    dop α (kern w) x = kern (fun m => sigma α m * w m) x := by
  unfold dop kern sigma
  simp only [mul_sum, Complex.real_smul]
  rw [sum_comm]
  refine sum_congr rfl fun m _ => ?_
  have := dop_char α m x
  unfold dop at this
  simp only [Complex.real_smul] at this
  calc ∑ b ∈ Iic α, (cf α b : ℂ) * (((n : ℂ) ^ d)⁻¹ * (w m * char m (b +ᵥ x)))
      = ((n : ℂ) ^ d)⁻¹ * w m * ∑ b ∈ Iic α, (cf α b : ℂ) * char m (b +ᵥ x) := by
        rw [mul_sum]; refine sum_congr rfl fun b _ => by ring
    _ = _ := by rw [this]; ring

theorem sigma_zero (m : Torus d n) : sigma (0 : Dir d → ℕ) m = 1 := by simp [sigma]

/-! ### Sup bounds -/

/-- `|w(m)| ≤ ∑_x |k(x)|`. -/
theorem norm_le_sum_kern (w : Sym d n) (m : Torus d n) : ‖w m‖ ≤ ∑ x, ‖kern w x‖ := by
  rw [← sum_kern_mul_conj w m]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  refine sum_congr rfl fun x _ => ?_
  rw [norm_mul, Complex.norm_conj, norm_char, mul_one]

/-- `∑_x |k(x)| ≤ (2 rng + 1)^d sup_x |k(x)|`. -/
theorem sum_kern_le (w : Sym d n) {B : ℝ} (hB : ∀ x, ‖kern w x‖ ≤ B) :
    ∑ x, ‖kern w x‖ ≤ (2 * rng w + 1) ^ d * B := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  rw [← sum_filter_add_sum_filter_not univ (fun x => supNorm x ≤ rng w)]
  have h2 : ∑ x ∈ univ.filter (fun x => ¬ supNorm x ≤ rng w), ‖kern w x‖ = 0 :=
    sum_eq_zero fun x hx => by
      simp only [mem_filter, mem_univ, true_and, not_le] at hx
      rw [kern_eq_zero_of_rng_lt hx, norm_zero]
  rw [h2, add_zero]
  calc ∑ x ∈ univ.filter (fun x => supNorm x ≤ rng w), ‖kern w x‖
      ≤ ∑ x ∈ univ.filter (fun x => supNorm x ≤ rng w), B := sum_le_sum fun x _ => hB x
    _ = (univ.filter (fun x : Torus d n => supNorm x ≤ rng w)).card * B := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (2 * rng w + 1) ^ d * B := by
        refine mul_le_mul_of_nonneg_right ?_ hB0
        exact_mod_cast card_supNorm_le (rng w)

end

end DressedFRD
