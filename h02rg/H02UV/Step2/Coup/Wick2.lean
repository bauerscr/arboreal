import Step2.Coup.CoupPast

/-!
# Wick evaluation of the quartic coefficients (`h02uv-outline.tex`, Proposition `prop:C4b`(c))

* `ι_mul_D_ιMulti`: `ι e · ∂_a (ι v₀ ⋯ ι v_{n-1}) = ∑_r ι v₀ ⋯ ι (v_r(a) e) ⋯ ι v_{n-1}`.
  Multiplying by `ι e` after a contraction acts as the derivation of the rank-one map
  `v ↦ v(a) e`.
* `Xc`: the single cross contraction `Σ C(x,y) [(∂_{y+} A)(∂_{x-} B) - (∂_{x-} A)(∂_{y+} B)]`;
  `mu4_FC_eq_Xc`: for `A` of degree `≤ 2` and `B` of degree `≤ 4`, `F_C(A, B)` and `Xc(A, B)` have
  the same quartic pairing.
* `Xc_pm_ιMulti`: for `A = ι p ι q` (spins `+`, `-`), `Xc(A, ι v₀ ⋯ ι v₃)` is the derivation of
  `T u = ⟨p, u⟩_C q + ⟨u, q⟩_C p`.
* `mu4_ιMulti`: `mu4` of a product of four vectors is the determinant of their columns
  `col u = (∑ ℓ_κ u₊, ∑ ℓ_κ' u₋, ∑ u₊, ∑ u₋)`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Matrix

section General

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

local notation "ι" => (ExteriorAlgebra.ι ℂ : V Λ →ₗ[ℂ] N Λ)

theorem vecTail_update_zero {n : ℕ} (v : Fin (n + 1) → V Λ) (x : V Λ) :
    Matrix.vecTail (Function.update v 0 x) = Matrix.vecTail v := by
  funext r
  simp [Matrix.vecTail, Function.update_of_ne (Fin.succ_ne_zero r)]

theorem vecTail_update_succ {n : ℕ} (v : Fin (n + 1) → V Λ) (r : Fin n) (x : V Λ) :
    Matrix.vecTail (Function.update v r.succ x) = Function.update (Matrix.vecTail v) r x := by
  funext r'
  simp only [Matrix.vecTail, Function.comp_apply]
  by_cases h : r' = r
  · subst h; simp
  · rw [Function.update_of_ne (fun e => h (Fin.succ_injective _ e)), Function.update_of_ne h]
    rfl

/-- **The derivation identity.** -/
theorem ι_mul_D_ιMulti (e : V Λ) (a : Sf Λ) :
    ∀ (n : ℕ) (v : Fin n → V Λ), ι e * D a (ExteriorAlgebra.ιMulti ℂ n v) =
      ∑ r, ExteriorAlgebra.ιMulti ℂ n (Function.update v r (v r a • e))
  | 0, v => by simp [D, CliffordAlgebra.contractLeft_one]
  | n + 1, v => by
    rw [ExteriorAlgebra.ιMulti_succ_apply, D_ι_mul, mul_sub, mul_smul_comm, ← mul_assoc,
      ι_anticomm e (v 0), neg_mul, sub_neg_eq_add, mul_assoc,
      ι_mul_D_ιMulti e a n (Matrix.vecTail v), Fin.sum_univ_succ]
    congr 1
    · rw [ExteriorAlgebra.ιMulti_succ_apply, vecTail_update_zero, Function.update_self, map_smul,
        smul_mul_assoc]
    · rw [mul_sum]
      refine sum_congr rfl fun r _ => ?_
      rw [ExteriorAlgebra.ιMulti_succ_apply, vecTail_update_succ,
        Function.update_of_ne (Fin.succ_ne_zero r).symm]
      rfl

/-- The single cross contraction. -/
def Xc (C : Matrix Λ Λ ℂ) (A B : N Λ) : N Λ :=
  ∑ x, ∑ y, C x y • (D (y, 1) A * D (x, -1) B - D (x, -1) A * D (y, 1) B)

theorem inv'_D_of_even {A : N Λ} (hA : inv' A = A) (a : Sf Λ) : inv' (D a A) = -D a A := by
  have h := Grassmann.D_inv' a A
  rw [hA] at h
  calc inv' (D a A) = -(-inv' (D a A)) := by rw [neg_neg]
    _ = -D a A := by rw [← h]

/-- **Leibniz rule**: `𝓛(AB) = (𝓛A)B + A(𝓛B) + Xc(A, B)` for even `A`. -/
theorem LopC_mul_even (C : Matrix Λ Λ ℂ) {A : N Λ} (hA : inv' A = A) (B : N Λ) :
    LopC C (A * B) = LopC C A * B + A * LopC C B + Xc C A B := by
  simp only [LopC_apply, Xc, sum_mul, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  rw [D_mul, map_add, D_mul, D_mul]
  simp only [hA, inv'_D_of_even hA]
  rw [smul_mul_assoc, mul_smul_comm, ← smul_add, ← smul_add]
  congr 1
  noncomm_ring

theorem LopC_neg (C : Matrix Λ Λ ℂ) : LopC (-C) = -LopC C := by
  refine LinearMap.ext fun F => ?_
  simp only [LinearMap.neg_apply, LopC_apply, Matrix.neg_apply, neg_smul, sum_neg_distrib]

theorem LopC_eq_zero_of_degLe {x : N Λ} (hx : DegLe 1 x) (C : Matrix Λ Λ ℂ) : LopC C x = 0 := by
  rw [LopC_apply]
  refine sum_eq_zero fun a _ => sum_eq_zero fun b _ => ?_
  have : D (b, 1) (D (a, -1) x) = 0 := ext_coeff fun n z => by
    rw [coeff_D, coeff_D, coeff_zero]; exact hx _ _ (by omega)
  rw [this, smul_zero]

/-- `e^{𝓛} P - P - 𝓛 P` has degree `≤ n` if `P` has degree `≤ n + 4`. -/
theorem _root_.Grassmann.DegLe.exp_sub2 (C : Matrix Λ Λ ℂ) {n : ℕ} {P : N Λ}
    (hP : DegLe (n + 4) P) : DegLe n (expLC C P - P - LopC C P) := by
  obtain ⟨k, hk⟩ := LopC_isNilpotent C
  have hk' : LopC C ^ (k + 2) = 0 := pow_eq_zero_of_le (by omega) hk
  rw [expLC, IsNilpotent.exp_eq_sum hk', LinearMap.sum_apply, sum_range_succ', sum_range_succ']
  have h0 : (((Nat.factorial 0 : ℕ) : ℚ)⁻¹ • LopC C ^ 0) P = P := by simp
  have h1 : (((Nat.factorial (0 + 1) : ℕ) : ℚ)⁻¹ • LopC C ^ (0 + 1)) P = LopC C P := by simp
  rw [h0, h1, show ∀ X Y Z : N Λ, X + Y + Z - Z - Y = X by intros; abel]
  refine DegLe.sum _ fun i _ => ?_
  rw [LinearMap.smul_apply, ← Rat.cast_smul_eq_qsmul ℂ, pow_succ, pow_succ, Module.End.mul_apply,
    Module.End.mul_apply]
  exact (((hP.lop C).lop C).lopPow C i).smul _

/-- **`F_C(A, B)` and the single cross contraction have the same quartic content.** -/
theorem FC_sub_Xc_degLe (C : Matrix Λ Λ ℂ) {A B : N Λ} (hA : inv' A = A) (hA2 : DegLe 2 A)
    (hB4 : DegLe 4 B) : DegLe 2 (FC C A B - Xc C A B) := by
  have hLA : DegLe 0 (LopC C A) := hA2.lop C
  have hLLA : LopC C (LopC C A) = 0 := LopC_eq_zero_of_degLe (hLA.mono (by norm_num)) C
  have hLB : DegLe 2 (LopC C B) := hB4.lop C
  have hLLB : DegLe 0 (LopC C (LopC C B)) := hLB.lop C
  have hLLLB : LopC C (LopC C (LopC C B)) = 0 := LopC_eq_zero_of_degLe (hLLB.mono (by norm_num)) C
  have eA : expLC (-C) A = A - LopC C A := by
    rw [expLC_of_cube (-C) (by simp [LopC_neg, hLLA]), LopC_neg]
    simp [hLLA]; abel
  have eB : expLC (-C) B = B - LopC C B + (1 / 2 : ℂ) • LopC C (LopC C B) := by
    rw [expLC_of_cube (-C) (by simp [LopC_neg, hLLLB]), LopC_neg]
    simp; abel
  set a := LopC C A
  set b := LopC C B
  set c := (1 / 2 : ℂ) • LopC C (LopC C B)
  have hc : DegLe 0 c := hLLB.smul _
  have hXc : Xc C A B = LopC C (A * B) - a * B - A * b := by
    rw [LopC_mul_even C hA]; abel
  set P := (A - a) * (B - b + c)
  have hP : DegLe 6 P := ((hA2.sub (hLA.mono (by norm_num))).mul
    ((hB4.sub (hLB.mono (by norm_num))).add (hc.mono (by norm_num))))
  have hPAB : P - A * B = -(A * b) + A * c - a * B + a * b - a * c := by
    simp only [P]; noncomm_ring
  have hPAB4 : DegLe 4 (P - A * B) := by
    rw [hPAB]
    refine ((((DegLe.smul ((hA2.mul hLB).mono (by norm_num)) (-1)).add ?_).sub ?_).add ?_).sub ?_
    · exact (hA2.mul hc).mono (by norm_num)
    · exact (hLA.mul hB4).mono (by norm_num)
    · exact (hLA.mul hLB).mono (by norm_num)
    · exact (hLA.mul hc).mono (by norm_num)
  have hP' : P = A * B + (-(A * b) + A * c - a * B + a * b - a * c) := by rw [← hPAB]; abel
  have e : FC C A B - Xc C A B = (expLC C P - P - LopC C P) +
      (A * c + a * b - a * c) + LopC C (P - A * B) := by
    rw [FC, eA, eB, hXc, map_sub]
    change expLC C P - A * B - (LopC C (A * B) - a * B - A * b) =
      expLC C P - P - LopC C P + (A * c + a * b - a * c) + (LopC C P - LopC C (A * B))
    generalize expLC C P = E
    generalize LopC C P = LP
    generalize LopC C (A * B) = LAB
    rw [hP']
    noncomm_ring
  rw [e]
  refine ((hP.exp_sub2 C (n := 2)).add ?_).add (hPAB4.lop C)
  exact (((hA2.mul hc).mono (by norm_num)).add ((hLA.mul hLB).mono (by norm_num))).sub
    ((hLA.mul hc).mono (by norm_num))

/-- `ι v₀ ⋯ ι v_{n-1}` is linear in the slot `r`. -/
def slotL (n : ℕ) (v : Fin n → V Λ) (r : Fin n) : V Λ →ₗ[ℂ] N Λ :=
  (ExteriorAlgebra.ιMulti ℂ n).toMultilinearMap.toLinearMap v r

theorem slotL_apply (n : ℕ) (v : Fin n → V Λ) (r : Fin n) (u : V Λ) :
    slotL n v r u = ExteriorAlgebra.ιMulti ℂ n (Function.update v r u) := rfl

theorem sum_comm3 {α β γ M : Type*} [AddCommMonoid M] [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → M) : ∑ x, ∑ y, ∑ r, f x y r = ∑ r, ∑ x, ∑ y, f x y r := by
  calc ∑ x, ∑ y, ∑ r, f x y r = ∑ x, ∑ r, ∑ y, f x y r := sum_congr rfl fun x _ => sum_comm
    _ = _ := sum_comm

/-- **The cross contraction of `ι p ι q` with a product of vectors** is the derivation of
`T u = ⟨p, u⟩_C q + ⟨u, q⟩_C p`. -/
theorem Xc_pm_ιMulti (C : Matrix Λ Λ ℂ) {p q : V Λ} (h : PM p q) (n : ℕ) (v : Fin n → V Λ) :
    Xc C (ι p * ι q) (ExteriorAlgebra.ιMulti ℂ n v) =
      ∑ r, ExteriorAlgebra.ιMulti ℂ n
        (Function.update v r (pairC C p (v r) • q + pairC C (v r) q • p)) := by
  have hy : ∀ y, D (y, 1) (ι p * ι q) = p (y, 1) • ι q := fun y => by
    rw [D_ι_mul, D_ι, h.hv, map_zero, mul_zero, sub_zero]
  have hx : ∀ x, D (x, -1) (ι p * ι q) = -(q (x, -1) • ι p) := fun x => by
    rw [D_ι_mul, D_ι, h.hu, zero_smul, zero_sub, Algebra.algebraMap_eq_smul_one, mul_smul_comm,
      mul_one]
  simp only [Xc, hy, hx, smul_mul_assoc, neg_mul, sub_neg_eq_add, ι_mul_D_ιMulti, smul_add,
    smul_sum, sum_add_distrib]
  simp only [← slotL_apply, map_smul, map_add, smul_smul, pairC, sum_smul, sum_add_distrib]
  simp only [map_sum, map_smul]
  congr 1
  all_goals
    rw [sum_comm3]
    try (refine sum_congr rfl fun r _ => sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
         congr 1; ring)

end General

variable {d L N : ℕ} [NeZero L]

/-- **The quartic content of `F_C(A, B)`** is that of the single cross contraction. -/
theorem mu4_FC_eq_Xc (C : Matrix (Lam d L N) (Lam d L N) ℂ) {A B : Alg d L N} (hA : inv' A = A)
    (hA2 : DegLe 2 A) (hB4 : DegLe 4 B) (b : Lam d L N) (κ κ' : Fin d) :
    mu4 b κ κ' (FC C A B) = mu4 b κ κ' (Xc C A B) := by
  have h := mu4_of_degLe ((FC_sub_Xc_degLe C hA hA2 hB4).mono (by norm_num)) b κ κ'
  rwa [mu4_sub, sub_eq_zero] at h

/-- The column of a vector in the determinant formula for `mu4`. -/
def col (b : Lam d L N) (κ κ' : Fin d) (u : V (Lam d L N)) : Fin 4 → ℂ :=
  ![∑ y, (lift b y κ : ℂ) * u (y, 1), ∑ y, (lift b y κ' : ℂ) * u (y, -1), ∑ y, u (y, 1),
    ∑ y, u (y, -1)]

/-- **`mu4` of a product of four vectors is the determinant of their columns.** -/
theorem mu4_ιMulti (b : Lam d L N) (κ κ' : Fin d) (v : Fin 4 → V (Lam d L N)) :
    mu4 b κ κ' (ExteriorAlgebra.ιMulti ℂ 4 v) = (Matrix.of fun a c => col b κ κ' (v c) a).det := by
  set φ : Fin 4 → Lam d L N → ℂ :=
    ![fun y => (lift b y κ : ℂ), fun y => (lift b y κ' : ℂ), fun _ => 1, fun _ => 1]
  have hφ : ∀ x' : Fin 4 → Lam d L N,
      ((lift b (x' 0) κ * lift b (x' 1) κ' : ℝ) : ℂ) = ∏ r, φ r (x' r) := by
    intro x'
    simp [φ, Fin.prod_univ_four]
  simp only [mu4, cf4, coeff_ιMulti, hφ]
  rw [sum_det_rows φ v]
  congr 1
  ext a c
  fin_cases a <;> simp [col, φ, pat4]

theorem col_add (b : Lam d L N) (κ κ' : Fin d) (u w : V (Lam d L N)) :
    col b κ κ' (u + w) = col b κ κ' u + col b κ κ' w := by
  funext a; fin_cases a <;> simp [col, mul_add, sum_add_distrib]

theorem col_smul (b : Lam d L N) (κ κ' : Fin d) (r : ℂ) (u : V (Lam d L N)) :
    col b κ κ' (r • u) = r • col b κ κ' u := by
  funext a; fin_cases a <;> simp [col, mul_sum, mul_left_comm]

theorem det4 (m : Matrix (Fin 4) (Fin 4) ℂ) :
    m.det = m 0 0 * (m 1 1 * (m 2 2 * m 3 3 - m 2 3 * m 3 2) - m 1 2 * (m 2 1 * m 3 3 - m 2 3 * m 3 1)
        + m 1 3 * (m 2 1 * m 3 2 - m 2 2 * m 3 1))
      - m 0 1 * (m 1 0 * (m 2 2 * m 3 3 - m 2 3 * m 3 2) - m 1 2 * (m 2 0 * m 3 3 - m 2 3 * m 3 0)
        + m 1 3 * (m 2 0 * m 3 2 - m 2 2 * m 3 0))
      + m 0 2 * (m 1 0 * (m 2 1 * m 3 3 - m 2 3 * m 3 1) - m 1 1 * (m 2 0 * m 3 3 - m 2 3 * m 3 0)
        + m 1 3 * (m 2 0 * m 3 1 - m 2 1 * m 3 0))
      - m 0 3 * (m 1 0 * (m 2 1 * m 3 2 - m 2 2 * m 3 1) - m 1 1 * (m 2 0 * m 3 2 - m 2 2 * m 3 0)
        + m 1 2 * (m 2 0 * m 3 1 - m 2 1 * m 3 0)) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.det_fin_three, Matrix.submatrix_apply,
    Fin.succAbove, Fin.castSucc, Fin.succ]
  simp [Fin.lt_def]
  ring

theorem col_sub (b : Lam d L N) (κ κ' : Fin d) (u w : V (Lam d L N)) :
    col b κ κ' (u - w) = col b κ κ' u - col b κ κ' w := by
  rw [sub_eq_add_neg, col_add, ← neg_one_smul ℂ w, col_smul, neg_one_smul, sub_eq_add_neg]

theorem col_ev_pos (b : Lam d L N) (κ κ' : Fin d) (z : Lam d L N) :
    col b κ κ' (ev (z, 1)) = ![(lift b z κ : ℂ), 0, 1, 0] := by
  funext a; fin_cases a <;> simp [col, ev, Pi.single_apply, Prod.ext_iff]

theorem col_ev_neg (b : Lam d L N) (κ κ' : Fin d) (z : Lam d L N) :
    col b κ κ' (ev (z, -1)) = ![0, (lift b z κ' : ℂ), 0, 1] := by
  funext a; fin_cases a <;> simp [col, ev, Pi.single_apply, Prod.ext_iff]

theorem pairC_eq_zero_right (C : Matrix (Lam d L N) (Lam d L N) ℂ) (p : V (Lam d L N))
    {u : V (Lam d L N)} (hu : ∀ x, u (x, -1) = 0) : pairC C p u = 0 := by
  simp [pairC, hu]

theorem pairC_eq_zero_left (C : Matrix (Lam d L N) (Lam d L N) ℂ) (q : V (Lam d L N))
    {u : V (Lam d L N)} (hu : ∀ x, u (x, 1) = 0) : pairC C u q = 0 := by
  simp [pairC, hu]

theorem v4g_pos0 (e e' : Dir d) (x y : Lam d L N) : v4g e e' x 0 (y, -1) = 0 := by
  simp [v4g, ev, Pi.single_apply, Prod.ext_iff]

theorem v4g_pos2 (e e' : Dir d) (x y : Lam d L N) : v4g e e' x 2 (y, -1) = 0 := by
  simp [v4g, ev, Pi.single_apply, Prod.ext_iff]

theorem v4g_neg1 (e e' : Dir d) (x y : Lam d L N) : v4g e e' x 1 (y, 1) = 0 := by
  simp [v4g, ev, Pi.single_apply, Prod.ext_iff]

theorem v4g_neg3 (e e' : Dir d) (x y : Lam d L N) : v4g e e' x 3 (y, 1) = 0 := by
  simp [v4g, ev, Pi.single_apply, Prod.ext_iff]

theorem col_update (b : Lam d L N) (κ κ' : Fin d) (v : Fin 4 → V (Lam d L N)) (r : Fin 4)
    (w : V (Lam d L N)) (a c : Fin 4) :
    col b κ κ' (Function.update v r w c) a = Function.update (fun c => col b κ κ' (v c)) r
      (col b κ κ' w) c a := by
  by_cases h : c = r
  · subst h; simp
  · simp [Function.update_of_ne h]

/-- **`mu4` of the cross contraction of `ι p ι q` with `gmono4`.** -/
theorem mu4_Xc_gmono4 (C : Matrix (Lam d L N) (Lam d L N) ℂ) {p q : V (Lam d L N)} (h : PM p q)
    (b : Lam d L N) (κ κ' : Fin d) (e e' : Dir d) (x : Lam d L N) :
    mu4 b κ κ' (Xc C (ExteriorAlgebra.ι ℂ p * ExteriorAlgebra.ι ℂ q) (gmono4 e e' x)) =
      pairC C (v4g e e' x 0) q * ((lift b (x + dirVec e') κ' : ℂ) - lift b x κ') *
          (col b κ κ' p 0 - (lift b x κ : ℂ) * col b κ κ' p 2) +
        pairC C p (v4g e e' x 1) * ((lift b (x + dirVec e) κ : ℂ) - lift b x κ) *
          (col b κ κ' q 1 - (lift b x κ' : ℂ) * col b κ κ' q 3) +
        pairC C (v4g e e' x 2) q * (((lift b (x + dirVec e) κ : ℂ) - lift b x κ) *
          ((lift b (x + dirVec e') κ' : ℂ) - lift b x κ') * col b κ κ' p 2) +
        pairC C p (v4g e e' x 3) * (((lift b (x + dirVec e) κ : ℂ) - lift b x κ) *
          ((lift b (x + dirVec e') κ' : ℂ) - lift b x κ') * col b κ κ' q 3) := by
  have hp1 : col b κ κ' p 1 = 0 := by simp [col, h.hu]
  have hp3 : col b κ κ' p 3 = 0 := by simp [col, h.hu]
  have hq0 : col b κ κ' q 0 = 0 := by simp [col, h.hv]
  have hq2 : col b κ κ' q 2 = 0 := by simp [col, h.hv]
  have z0 := pairC_eq_zero_right C p (v4g_pos0 e e' x)
  have z2 := pairC_eq_zero_right C p (v4g_pos2 e e' x)
  have z1 := pairC_eq_zero_left C q (v4g_neg1 e e' x)
  have z3 := pairC_eq_zero_left C q (v4g_neg3 e e' x)
  have c0 : col b κ κ' (v4g e e' x 0) =
      ![(lift b (x + dirVec e) κ : ℂ) - lift b x κ, 0, 0, 0] := by
    show col b κ κ' (ev (x + dirVec e, 1) - ev (x, 1)) = _
    rw [col_sub, col_ev_pos, col_ev_pos]
    funext a; fin_cases a <;> simp
  have c1 : col b κ κ' (v4g e e' x 1) =
      ![0, (lift b (x + dirVec e') κ' : ℂ) - lift b x κ', 0, 0] := by
    show col b κ κ' (ev (x + dirVec e', -1) - ev (x, -1)) = _
    rw [col_sub, col_ev_neg, col_ev_neg]
    funext a; fin_cases a <;> simp
  have c2 : col b κ κ' (v4g e e' x 2) = ![(lift b x κ : ℂ), 0, 1, 0] := col_ev_pos b κ κ' x
  have c3 : col b κ κ' (v4g e e' x 3) = ![0, (lift b x κ' : ℂ), 0, 1] := col_ev_neg b κ κ' x
  rw [gmono4, Xc_pm_ιMulti C h, mu4_sum, Fin.sum_univ_four]
  simp only [mu4_ιMulti]
  simp only [col_update, col_add, col_smul, z0, z1, z2, z3, zero_smul, add_zero, zero_add]
  simp only [det4, Matrix.of_apply, Function.update_apply, Fin.isValue]
  simp [c0, c1, c2, c3, hp1, hp3, hq0, hq2]
  ring

end

end Step2
