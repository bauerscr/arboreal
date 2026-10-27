import Grassmann.Doubled

/-!
# Gaussian expectation as a Berezin integral

For invertible `C`, `𝔼_C F = (det C) ∫ ∂_ζ ∂_ζ̄ e^{-(ζ, C^{-1} ζ̄)} F` (`EC_eq_berezin`), in
particular for positive definite `C` (`EC_eq_berezin_of_posDef`).
-/

namespace Grassmann

noncomputable section

open CliffordAlgebra ExteriorAlgebra Finset Matrix

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

/-- The Berezin integral `∫ ∂_ζ ∂_ζ̄ = ∏_x ∂_{ζ_x} ∂_{ζ̄_x}` over the ζ variables
(for each `x`, `∂_{ζ̄_x}` is applied first; the pairs commute, so the order of `x` is irrelevant). -/
def berezinζ : N (Λ ⊕ Λ) →ₗ[ℂ] N (Λ ⊕ Λ) :=
  (Finset.univ : Finset Λ).toList.foldr (fun x T => D (Sum.inr x, 1) ∘ₗ D (Sum.inr x, -1) ∘ₗ T) LinearMap.id

/-- `(ζ, A ζ̄) = ∑_{x,y} ζ_x A_{xy} ζ̄_y`. -/
def quadζ (A : Matrix Λ Λ ℝ) : N (Λ ⊕ Λ) := ∑ x, ∑ y, (A x y : ℂ) • (ζ (x, 1) * ζ (y, -1))

/-! ### The Berezin integral over a list of sites -/

/-- `∂_{ζ_x} ∂_{ζ̄_x}`. -/
abbrev Pζ (x : Λ) : N (Λ ⊕ Λ) →ₗ[ℂ] N (Λ ⊕ Λ) := D (Sum.inr x, 1) ∘ₗ D (Sum.inr x, -1)

/-- `∏_{x ∈ l} ∂_{ζ_x} ∂_{ζ̄_x}`. -/
def berL (l : List Λ) : N (Λ ⊕ Λ) →ₗ[ℂ] N (Λ ⊕ Λ) :=
  l.foldr (fun x T => D (Sum.inr x, 1) ∘ₗ D (Sum.inr x, -1) ∘ₗ T) LinearMap.id

theorem berezinζ_eq : (berezinζ : N (Λ ⊕ Λ) →ₗ[ℂ] _) = berL (Finset.univ : Finset Λ).toList := rfl

theorem berL_cons (x : Λ) (l : List Λ) (F : N (Λ ⊕ Λ)) : berL (x :: l) F = Pζ x (berL l F) := rfl

theorem berL_nil (F : N (Λ ⊕ Λ)) : berL ([] : List Λ) F = F := rfl

theorem D_berL (a : Sf (Λ ⊕ Λ)) (l : List Λ) (F : N (Λ ⊕ Λ)) :
    D a (berL l F) = berL l (D a F) := by
  induction l generalizing F with
  | nil => rfl
  | cons x l ih =>
    rw [berL_cons, berL_cons, LinearMap.comp_apply, DD_comm, ih, LinearMap.comp_apply]

theorem units_cases (σ : ℤˣ) : σ = 1 ∨ σ = -1 := Int.units_eq_one_or σ

theorem Pζ_D_self (x : Λ) (σ : ℤˣ) (G : N (Λ ⊕ Λ)) : Pζ x (D (Sum.inr x, σ) G) = 0 := by
  rcases units_cases σ with rfl | rfl
  · rw [LinearMap.comp_apply, D_comm (Sum.inr x, -1) (Sum.inr x, 1), map_neg, D_D, neg_zero]
  · rw [LinearMap.comp_apply, D_D, map_zero]

theorem berL_D {l : List Λ} {x : Λ} (hx : x ∈ l) (σ : ℤˣ) (G : N (Λ ⊕ Λ)) :
    berL l (D (Sum.inr x, σ) G) = 0 := by
  induction l generalizing G with
  | nil => simp at hx
  | cons y l ih =>
    rw [berL_cons]
    by_cases h : x = y
    · subst h; rw [← D_berL, Pζ_D_self]
    · rw [ih (List.mem_of_ne_of_mem h hx), map_zero]

theorem Pζ_mul_of (x : Λ) {X : N (Λ ⊕ Λ)} (hX : ∀ σ : ℤˣ, D (Sum.inr x, σ) X = 0)
    (G : N (Λ ⊕ Λ)) : Pζ x (X * G) = X * Pζ x G := by
  rw [LinearMap.comp_apply, LinearMap.comp_apply, D_mul, hX, zero_mul, zero_add, D_mul, D_inv',
    hX, map_zero, neg_zero, zero_mul, zero_add, inv'_inv']

theorem berL_mul_of (l : List Λ) {X : N (Λ ⊕ Λ)} (hX : ∀ x ∈ l, ∀ σ : ℤˣ, D (Sum.inr x, σ) X = 0)
    (G : N (Λ ⊕ Λ)) : berL l (X * G) = X * berL l G := by
  induction l generalizing G with
  | nil => rfl
  | cons y l ih =>
    rw [berL_cons, berL_cons, ih (fun x hx => hX x (List.mem_cons_of_mem _ hx)),
      Pζ_mul_of y (hX y List.mem_cons_self)]

/-! ### The Gaussian weight -/

theorem D_pow (a : Sf (Λ ⊕ Λ)) {y : N (Λ ⊕ Λ)} (hy : inv' y = y) (n : ℕ) :
    D a (y ^ (n + 1)) = ((n + 1 : ℕ) : ℂ) • (y ^ n * D a y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', D_mul, ih, hy, mul_smul_comm, ← mul_assoc, ← pow_succ',
      mul_comm_of_even (show inv' (y ^ (n + 1)) = y ^ (n + 1) by rw [map_pow, hy])]
    push_cast
    module

theorem D_exp (a : Sf (Λ ⊕ Λ)) {y : N (Λ ⊕ Λ)} (hy : inv' y = y) (hn : IsNilpotent y) :
    D a (IsNilpotent.exp y) = IsNilpotent.exp y * D a y := by
  obtain ⟨k, hk⟩ := hn
  have hk1 : y ^ (k + 1) = 0 := by rw [pow_succ, hk, zero_mul]
  conv_rhs => rw [IsNilpotent.exp_eq_sum hk]
  rw [IsNilpotent.exp_eq_sum hk1, map_sum, Finset.sum_mul, Finset.sum_range_succ', pow_zero,
    LinearMap.map_smul_of_tower, D_one, smul_zero, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.map_smul_of_tower, D_pow a hy, smul_mul_assoc, Nat.cast_smul_eq_nsmul ℂ,
    ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, Nat.factorial_succ, Nat.cast_mul]
  congr 1
  field_simp

theorem inv'_quadζ (A : Matrix Λ Λ ℝ) : inv' (quadζ A) = quadζ A := by
  simp [quadζ, map_sum, AlgHom.map_smul_of_tower]

theorem ιι_sq {M : Type*} [AddCommGroup M] [Module ℂ M] (u w : M) :
    (ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ w) * (ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ w)
      = 0 := by
  rw [mul_assoc, ← mul_assoc (ExteriorAlgebra.ι ℂ w), ι_anticomm w u]
  simp only [neg_mul, mul_neg, ← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul, neg_zero]

theorem zz_sq (a b : Sf Λ) (c : ℂ) : (c • (ζ a * ζ b)) * (c • (ζ a * ζ b)) = 0 := by
  rw [smul_mul_smul, ζ, ζ, ψ, ψ, ιι_sq, smul_zero]

theorem quadζ_isNilpotent (A : Matrix Λ Λ ℝ) : IsNilpotent (quadζ A) := by
  have hev : ∀ (a b : Sf Λ) (c : ℂ), inv' (c • (ζ a * ζ b)) = c • (ζ a * ζ b) := by simp
  refine Commute.isNilpotent_sum (fun x _ => ?_) fun x x' _ _ => ?_
  · refine Commute.isNilpotent_sum (fun y _ => ?_) fun y y' _ _ => ?_
    · exact ⟨2, by rw [pow_two]; exact zz_sq _ _ _⟩
    · exact mul_comm_of_even (hev _ _ _) _
  · exact mul_comm_of_even (by simp [map_sum, AlgHom.map_smul_of_tower]) _

theorem inv'_expQ (A : Matrix Λ Λ ℝ) :
    inv' (IsNilpotent.exp (-quadζ A)) = IsNilpotent.exp (-quadζ A) := by
  rw [IsNilpotent.map_exp (quadζ_isNilpotent A).neg, map_neg, inv'_quadζ]


theorem one_ne_neg_one_units : (1 : ℤˣ) ≠ -1 := by decide

theorem D_zeta_quadζ (A : Matrix Λ Λ ℝ) (y : Λ) :
    D (Sum.inr y, 1) (quadζ A) = ∑ y', (A y y' : ℂ) • ζ (y', -1) := by
  simp [quadζ, map_sum, D_mul, D_ψ, Prod.ext_iff]

theorem D_zetabar_quadζ (A : Matrix Λ Λ ℝ) (x : Λ) :
    D (Sum.inr x, -1) (quadζ A) = -∑ x', (A x' x : ℂ) • ζ (x', 1) := by
  simp [quadζ, map_sum, D_mul, D_ψ, Prod.ext_iff, one_ne_neg_one_units.symm]


/-- `F ↦ ∫ ∂_ζ ∂_ζ̄ e^{-(ζ, A ζ̄)} F`, followed by `ζ = 0`. -/
def Jb (A : Matrix Λ Λ ℝ) : N (Λ ⊕ Λ) →ₗ[ℂ] N Λ :=
  proj.toLinearMap ∘ₗ berezinζ ∘ₗ LinearMap.mulLeft ℂ (IsNilpotent.exp (-quadζ A))

theorem Jb_apply (A : Matrix Λ Λ ℝ) (F : N (Λ ⊕ Λ)) :
    Jb A F = proj (berezinζ (IsNilpotent.exp (-quadζ A) * F)) := rfl

theorem Jb_ψ₁_mul (A : Matrix Λ Λ ℝ) (a : Sf Λ) (G : N (Λ ⊕ Λ)) :
    Jb A (ψ₁ a * G) = ψ a * Jb A G := by
  rw [Jb_apply, Jb_apply, ← mul_assoc, mul_comm_of_even (inv'_expQ A), mul_assoc, berezinζ_eq,
    berL_mul_of _ (fun x _ σ => by simp [D_ψ]), map_mul, proj_ψ₁]

theorem berezinζ_D (x : Λ) (σ : ℤˣ) (G : N (Λ ⊕ Λ)) : berezinζ (D (Sum.inr x, σ) G) = 0 :=
  berL_D (Finset.mem_toList.2 (mem_univ x)) σ G

theorem Jb_D_zeta (A : Matrix Λ Λ ℝ) (y : Λ) (G : N (Λ ⊕ Λ)) :
    Jb A (D (Sum.inr y, 1) G) = ∑ y', (A y y' : ℂ) • Jb A (ζ (y', -1) * G) := by
  have h0 := berezinζ_D y 1 (IsNilpotent.exp (-quadζ A) * G)
  rw [D_mul, D_exp _ (by rw [map_neg, inv'_quadζ]) (quadζ_isNilpotent A).neg, inv'_expQ,
    map_neg, D_zeta_quadζ, mul_neg, neg_mul, map_add, map_neg, neg_add_eq_zero] at h0
  rw [Jb_apply, ← h0, mul_sum, sum_mul, map_sum, map_sum]
  refine sum_congr rfl fun y' _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, mul_assoc, map_smul, map_smul, Jb_apply]

theorem Jb_D_zetabar (A : Matrix Λ Λ ℝ) (x : Λ) (G : N (Λ ⊕ Λ)) :
    Jb A (D (Sum.inr x, -1) G) = -∑ x', (A x' x : ℂ) • Jb A (ζ (x', 1) * G) := by
  have h0 := berezinζ_D x (-1) (IsNilpotent.exp (-quadζ A) * G)
  rw [D_mul, D_exp _ (by rw [map_neg, inv'_quadζ]) (quadζ_isNilpotent A).neg, inv'_expQ,
    map_neg, D_zetabar_quadζ, neg_neg, map_add, add_eq_zero_iff_neg_eq] at h0
  rw [Jb_apply, ← h0, mul_sum, sum_mul, map_sum, map_neg, map_sum]
  congr 1
  refine sum_congr rfl fun y' _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, mul_assoc, map_smul, map_smul, Jb_apply]

theorem sum_smul_sum_mul {M : Type*} [AddCommGroup M] [Module ℂ M] (C A : Matrix Λ Λ ℝ) (x : Λ)
    (v : Λ → M) :
    ∑ y, (C x y : ℂ) • ∑ y', (A y y' : ℂ) • v y' = ∑ y', ((C * A) x y' : ℂ) • v y' := by
  simp only [Matrix.mul_apply, Complex.ofReal_sum, Complex.ofReal_mul, Finset.smul_sum, smul_smul,
    Finset.sum_smul]
  exact Finset.sum_comm

theorem Jb_zetabar_mul (C : Matrix Λ Λ ℝ) (hC : IsUnit C.det) (x : Λ) (G : N (Λ ⊕ Λ)) :
    Jb C⁻¹ (ζ (x, -1) * G) = ∑ y, (C x y : ℂ) • Jb C⁻¹ (D (Sum.inr y, 1) G) := by
  simp_rw [Jb_D_zeta]
  rw [sum_smul_sum_mul, Matrix.mul_nonsing_inv C hC]
  simp [Matrix.one_apply, apply_ite ((↑) : ℝ → ℂ)]

theorem Jb_zeta_mul (C : Matrix Λ Λ ℝ) (hC : IsUnit C.det) (y : Λ) (G : N (Λ ⊕ Λ)) :
    Jb C⁻¹ (ζ (y, 1) * G) = -∑ x, (C x y : ℂ) • Jb C⁻¹ (D (Sum.inr x, -1) G) := by
  simp_rw [Jb_D_zetabar, smul_neg, Finset.sum_neg_distrib, neg_neg, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  have : ∀ x', ∑ x, (C x y : ℂ) * (C⁻¹ x' x : ℂ) = ((C⁻¹ * C) x' y : ℂ) := fun x' => by
    rw [Matrix.mul_apply]; push_cast; exact sum_congr rfl fun _ _ => mul_comm _ _
  simp_rw [this, Matrix.nonsing_inv_mul C hC]
  simp [Matrix.one_apply, apply_ite ((↑) : ℝ → ℂ)]


/-! ### Uniqueness -/

theorem ι_eq_sum (w : V (Λ ⊕ Λ)) : ExteriorAlgebra.ι ℂ w = ∑ a, w a • ψ a := by
  have hw : w = ∑ a, w a • ev a := by
    ext b; simp [ev, Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hw]
  rw [map_sum]; simp_rw [map_smul]; rfl

/-- A linear map satisfying the integration by parts rules of `𝔼_C` is determined by its
value at `1`. -/
theorem ext_of_rules (C : Matrix Λ Λ ℝ) (K₁ K₂ : N (Λ ⊕ Λ) →ₗ[ℂ] N Λ)
    (h1a : ∀ a G, K₁ (ψ₁ a * G) = ψ a * K₁ G) (h2a : ∀ a G, K₂ (ψ₁ a * G) = ψ a * K₂ G)
    (h1b : ∀ x G, K₁ (ζ (x, -1) * G) = ∑ y, (C x y : ℂ) • K₁ (D (Sum.inr y, 1) G))
    (h2b : ∀ x G, K₂ (ζ (x, -1) * G) = ∑ y, (C x y : ℂ) • K₂ (D (Sum.inr y, 1) G))
    (h1c : ∀ y G, K₁ (ζ (y, 1) * G) = -∑ x, (C x y : ℂ) • K₁ (D (Sum.inr x, -1) G))
    (h2c : ∀ y G, K₂ (ζ (y, 1) * G) = -∑ x, (C x y : ℂ) • K₂ (D (Sum.inr x, -1) G))
    (h1 : K₁ 1 = K₂ 1) : K₁ = K₂ := by
  suffices h : ∀ n (v : Fin n → V (Λ ⊕ Λ)), K₁ (ιMulti ℂ n v) = K₂ (ιMulti ℂ n v) by
    refine LinearMap.ext fun F => ?_
    induction F using induction_ιMulti with
    | hzero => simp
    | hadd F G hF hG => rw [map_add, map_add, hF, hG]
    | hsmul r F hF => rw [map_smul, map_smul, hF]
    | hι n v => exact h n v
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro v
  rcases n with _ | m
  · rw [ιMulti_zero_apply, h1]
  · rw [ιMulti_succ_apply]
    set G := ιMulti ℂ m (Matrix.vecTail v)
    have hG : K₁ G = K₂ G := ih m (Nat.lt_succ_self m) _
    have hDG : ∀ a, K₁ (D a G) = K₂ (D a G) := by
      intro a
      rcases m with _ | k
      · simp [G, ιMulti_zero_apply]
      · simp only [G, D]
        rw [contractLeft_ιMulti, map_sum, map_sum]
        refine sum_congr rfl fun j _ => ?_
        rw [map_smul, map_smul, ih k (by omega)]
    rw [ι_eq_sum, sum_mul, map_sum, map_sum]
    refine sum_congr rfl fun ⟨b, σ⟩ _ => ?_
    rw [smul_mul_assoc, map_smul, map_smul]
    congr 1
    rcases b with x | x
    · exact (h1a (x, σ) G).trans ((congrArg _ hG).trans (h2a (x, σ) G).symm)
    · rcases units_cases σ with rfl | rfl
      · rw [show ψ (Sum.inr x, (1 : ℤˣ)) = ζ (x, 1) from rfl, h1c, h2c]
        simp_rw [hDG]
      · rw [show ψ (Sum.inr x, (-1 : ℤˣ)) = ζ (x, -1) from rfl, h1b, h2b]
        simp_rw [hDG]

/-! ### `Jb A 1` is a scalar -/

theorem D_inclζ (x : Λ) (σ : ℤˣ) (F : N Λ) : D (Sum.inr x, σ) (inclζ F) = inclζ (D (x, σ) F) := by
  rw [D, inclζ, contractLeft_map, coord_inr_inrV]; rfl

theorem berL_inclζ (l : List Λ) (F : N Λ) : ∃ G, berL l (inclζ F) = inclζ G := by
  induction l generalizing F with
  | nil => exact ⟨F, rfl⟩
  | cons x l ih =>
    obtain ⟨G, hG⟩ := ih F
    exact ⟨D (x, 1) (D (x, -1) G), by rw [berL_cons, hG, LinearMap.comp_apply, D_inclζ, D_inclζ]⟩

/-- `(ψ, A ψ̄)` in `𝒩(Λ)`. -/
def quad (A : Matrix Λ Λ ℝ) : N Λ := ∑ x, ∑ y, (A x y : ℂ) • (ψ (x, 1) * ψ (y, -1))

theorem inclζ_quad (A : Matrix Λ Λ ℝ) : inclζ (quad A) = quadζ A := by
  simp [quad, quadζ, map_sum, inclζ_psi, AlgHom.map_smul_of_tower]

theorem Jb_one (A : Matrix Λ Λ ℝ) : ∃ r : ℂ, Jb A 1 = algebraMap ℂ (N Λ) r := by
  have hn : IsNilpotent (-quad A) := by
    have hev : ∀ (a b : Sf Λ) (c : ℂ), inv' (c • (ψ a * ψ b)) = c • (ψ a * ψ b) := by simp
    refine (Commute.isNilpotent_sum (fun x _ => ?_) fun x x' _ _ => ?_).neg
    · refine Commute.isNilpotent_sum (fun y _ => ?_) fun y y' _ _ => ?_
      · exact ⟨2, by rw [pow_two, smul_mul_smul, ψ, ψ, ιι_sq, smul_zero]⟩
      · exact mul_comm_of_even (hev _ _ _) _
    · exact mul_comm_of_even (by simp [map_sum, AlgHom.map_smul_of_tower]) _
  obtain ⟨G, hG⟩ := berL_inclζ (Finset.univ : Finset Λ).toList (IsNilpotent.exp (-quad A))
  refine ⟨ε G, ?_⟩
  rw [Jb_apply, mul_one, ← inclζ_quad, ← map_neg, ← IsNilpotent.map_exp hn, berezinζ_eq, hG,
    proj_inclζ]


/-! ### Normalization -/

/-- `∏_i ψ̄_{f i} ψ_{f i}`. -/
def pairs {n : ℕ} (f : Fin n → Λ) : N Λ := (List.ofFn fun i => ψ (f i, -1) * ψ (f i, 1)).prod

theorem pairs_succ {n : ℕ} (f : Fin (n + 1) → Λ) :
    pairs f = (ψ (f 0, -1) * ψ (f 0, 1)) * pairs (fun i => f i.succ) := by
  simp [pairs, List.ofFn_succ]

theorem exp_succ (n : ℕ) : n * (n - 1) / 2 + n = (n + 1) * (n + 1 - 1) / 2 := by
  rcases n with _ | k
  · rfl
  · rw [show k + 1 + 1 - 1 = k + 1 by omega, show k + 1 - 1 = k by omega,
      show (k + 1 + 1) * (k + 1) = (k + 1) * k + 2 * (k + 1) by ring,
      Nat.add_mul_div_left _ _ two_pos]

theorem pairs_eq {n : ℕ} (f : Fin n → Λ) :
    pairs f = ((-1 : ℂ) ^ (n * (n - 1) / 2)) •
      (ιMulti ℂ n (fun i => ev (f i, -1)) * ιMulti ℂ n (fun i => ev (f i, 1))) := by
  induction n with
  | zero => simp [pairs, ιMulti_zero_apply]
  | succ n ih =>
    rw [pairs_succ, ih, ιMulti_succ_apply, ιMulti_succ_apply]
    simp only [Matrix.vecTail, Function.comp_def]
    set U := ιMulti ℂ n (fun i => ev (f i.succ, -1))
    set W := ιMulti ℂ n (fun i => ev (f i.succ, 1))
    have hc : ψ (f 0, 1) * U = (-1 : ℂ) ^ n • (U * ψ (f 0, 1)) := by
      rw [ψ, ι_mul_eq, inv'_ιMulti, smul_mul_assoc]
    rw [mul_smul_comm, show (ψ (f 0, -1) * ψ (f 0, 1)) * (U * W) =
      ψ (f 0, -1) * (ψ (f 0, 1) * U) * W by simp only [mul_assoc], hc, mul_smul_comm,
      smul_mul_assoc, smul_smul, ← pow_add, exp_succ]
    simp only [mul_assoc]; rfl

theorem vbar_single (x : Λ) : vbar (Pi.single x (1 : ℝ)) = ev (x, -1) := by
  ext ⟨y, σ⟩
  rcases units_cases σ with rfl | rfl <;> simp [vbar, ev, Pi.single_apply, apply_ite ((↑) : ℝ → ℂ)]

theorem vpsi_single (x : Λ) : vpsi (Pi.single x (1 : ℝ)) = ev (x, 1) := by
  ext ⟨y, σ⟩
  rcases units_cases σ with rfl | rfl <;> simp [vpsi, ev, Pi.single_apply, apply_ite ((↑) : ℝ → ℂ)]

theorem omega_pairs (C : Matrix Λ Λ ℝ) {n : ℕ} (f : Fin n → Λ) :
    omega C (pairs f) = ((Matrix.of fun i j => C (f i) (f j)).det : ℂ) := by
  have := omega_moment C (fun i => Pi.single (f i) (1 : ℝ)) (fun i => Pi.single (f i) (1 : ℝ))
  simp only [vbar_single, vpsi_single] at this
  rw [pairs_eq, omega_smul, this, ← mul_assoc, ← mul_pow]
  norm_num


theorem inclζ_pairs_succ {n : ℕ} (f : Fin (n + 1) → Λ) :
    inclζ (pairs f) = (ζ (f 0, -1) * ζ (f 0, 1)) * inclζ (pairs (fun i => f i.succ)) := by
  rw [pairs_succ, map_mul, map_mul, inclζ_psi, inclζ_psi]

theorem inv'_pair (x : Λ) : inv' (ζ (x, -1) * ζ (x, 1)) = ζ (x, -1) * ζ (x, 1) := by simp

theorem D_pair_of_ne {x y : Λ} (h : x ≠ y) (σ : ℤˣ) :
    D (Sum.inr y, σ) (ζ (x, -1) * ζ (x, 1)) = 0 := by
  simp [D_mul, D_ψ, Prod.ext_iff, Ne.symm h]

theorem Pζ_pair (x : Λ) : Pζ x (ζ (x, -1) * ζ (x, 1)) = 1 := by
  simp [D_mul, D_ψ, Prod.ext_iff]

theorem berL_pairs {n : ℕ} (f : Fin n → Λ) (hf : Function.Injective f) :
    berL (List.ofFn f) (inclζ (pairs f)) = 1 := by
  induction n with
  | zero => simp [pairs, berL_nil]
  | succ n ih =>
    rw [List.ofFn_succ, berL_cons, inclζ_pairs_succ, berL_mul_of, ih (fun i => f i.succ) (hf.comp (Fin.succ_injective _)),
      mul_one, Pζ_pair]
    intro x hx σ
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact D_pair_of_ne (fun h => Fin.succ_ne_zero i (hf h.symm)) σ

theorem zeta_mul_pair (x : Λ) (σ : ℤˣ) : ζ (x, σ) * (ζ (x, -1) * ζ (x, 1)) = 0 := by
  simp only [ζ, ψ]
  rcases units_cases σ with rfl | rfl
  · rw [← mul_assoc, ι_anticomm, neg_mul, mul_assoc, ExteriorAlgebra.ι_sq_zero, mul_zero, neg_zero]
  · rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]

theorem zeta_mul_pairs {n : ℕ} (f : Fin n → Λ) (i : Fin n) (σ : ℤˣ) :
    ζ (f i, σ) * inclζ (pairs f) = 0 := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    rw [inclζ_pairs_succ]
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [← mul_assoc, zeta_mul_pair, zero_mul]
    · rw [← mul_assoc, mul_comm_of_even (inv'_pair _) (ζ _) |>.symm, mul_assoc,
        ih (fun i => f i.succ) j, mul_zero]

theorem expQ_mul_pairs (A : Matrix Λ Λ ℝ) {n : ℕ} (f : Fin n → Λ) (hf : Function.Surjective f) :
    IsNilpotent.exp (-quadζ A) * inclζ (pairs f) = inclζ (pairs f) := by
  have hQ : quadζ A * inclζ (pairs f) = 0 := by
    rw [quadζ, sum_mul]
    refine sum_eq_zero fun x _ => ?_
    rw [sum_mul]
    refine sum_eq_zero fun y _ => ?_
    obtain ⟨i, rfl⟩ := hf y
    rw [smul_mul_assoc, mul_assoc, zeta_mul_pairs, mul_zero, smul_zero]
  obtain ⟨k, hk⟩ := (quadζ_isNilpotent A).neg
  have hk1 : (-quadζ A) ^ (k + 1) = 0 := by rw [pow_succ, hk, zero_mul]
  rw [IsNilpotent.exp_eq_sum hk1, sum_mul, sum_range_succ', pow_zero, Nat.factorial_zero,
    Nat.cast_one, inv_one, one_smul, one_mul, add_eq_right]
  refine sum_eq_zero fun i _ => ?_
  rw [smul_mul_assoc, pow_succ, mul_assoc, neg_mul, hQ, neg_zero, mul_zero, smul_zero]


/-! ### The main theorem -/

/-- For invertible `C`, `𝔼_C F = (det C) ∫ ∂_ζ ∂_ζ̄ e^{-(ζ, C^{-1} ζ̄)} F`. -/
theorem EC_eq_berezin (C : Matrix Λ Λ ℝ) (hC : IsUnit C.det) (F : N (Λ ⊕ Λ)) :
    EC C F = (C.det : ℂ) • proj (berezinζ (IsNilpotent.exp (-quadζ C⁻¹) * F)) := by
  set l := (Finset.univ : Finset Λ).toList
  let f : Fin l.length → Λ := l.get
  have hinj : Function.Injective f := List.nodup_iff_injective_get.1 (Finset.nodup_toList _)
  have hsurj : Function.Surjective f := fun x =>
    List.mem_iff_get.1 (Finset.mem_toList.2 (mem_univ x))
  let e : Fin l.length ≃ Λ := Equiv.ofBijective f ⟨hinj, hsurj⟩
  obtain ⟨r, hr⟩ := Jb_one C⁻¹
  have hJ : Jb C⁻¹ = r • EC C := by
    refine ext_of_rules C _ _ (Jb_ψ₁_mul _) (fun a G => ?_) (Jb_zetabar_mul C hC)
      (fun x G => ?_) (Jb_zeta_mul C hC) (fun y G => ?_) ?_
    · rw [LinearMap.smul_apply, LinearMap.smul_apply, EC_ψ₁_mul, mul_smul_comm]
    · simp only [LinearMap.smul_apply, EC_zetabar_mul, Finset.smul_sum]
      exact sum_congr rfl fun _ _ => smul_comm _ _ _
    · simp only [LinearMap.smul_apply, EC_zeta_mul, Finset.smul_sum, smul_neg]
      exact congrArg _ (sum_congr rfl fun _ _ => smul_comm _ _ _)
    · rw [hr, LinearMap.smul_apply, EC_one, Algebra.algebraMap_eq_smul_one]
  have hl : berL l = berL (List.ofFn f) := by rw [List.ofFn_get]
  have hM1 : Jb C⁻¹ (inclζ (pairs f)) = 1 := by
    rw [Jb_apply, expQ_mul_pairs _ f hsurj, berezinζ_eq, hl, berL_pairs f hinj, map_one]
  have hM2 : EC C (inclζ (pairs f)) = algebraMap ℂ (N Λ) (C.det : ℂ) := by
    rw [EC_inclζ, omega_pairs]
    exact congrArg _ (congrArg Complex.ofReal (Matrix.det_submatrix_equiv_self e C))
  have hrd : r * C.det = 1 := by
    have h := congrArg ε (hM1.symm.trans (LinearMap.congr_fun hJ _))
    rw [LinearMap.smul_apply, hM2, map_one, map_smul, AlgHom.commutes] at h
    simpa using h.symm
  rw [← Jb_apply, hJ, LinearMap.smul_apply, smul_smul, mul_comm, hrd, one_smul]

/-- For positive definite `C`, `𝔼_C F = (det C) ∫ ∂_ζ ∂_ζ̄ e^{-(ζ, C^{-1} ζ̄)} F`. -/
theorem EC_eq_berezin_of_posDef (C : Matrix Λ Λ ℝ) (hC : C.PosDef) (F : N (Λ ⊕ Λ)) :
    EC C F = (C.det : ℂ) • proj (berezinζ (IsNilpotent.exp (-quadζ C⁻¹) * F)) :=
  EC_eq_berezin C hC.det_pos.ne'.isUnit F

end

end Grassmann
