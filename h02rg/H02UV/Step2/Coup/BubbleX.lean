import Step2.Coup.Bubble

/-!
# Explicit evaluation of the double contraction

* `D_ιMulti`: `∂_a(ι v₀ ⋯ ι v_n) = ∑_r (-1)^r v_r(a) ι v₀ ⋯ ι̂ v_r ⋯ ι v_n`;
* `Xc_ιMulti`: the single cross contraction of two products of vectors,
  `X(ι^p, ι^q) = ∑_{r,s} (-1)^{r+s} K(p_r, q_s) ι^{p∖r} ι^{q∖s}` with the antisymmetric kernel
  `K(u, w) = ⟨u, w⟩_C - ⟨w, u⟩_C`;
* `X2_ιMulti`: `X₂(ι^p, ι^q) = -∑_{r,s} (-1)^{r+s} K(p_r, q_s) X(ι^{p∖r}, ι^{q∖s})`;
* `mu4_X2_ιMulti`: for four vectors on each side, `μ₄ X₂` is an explicit sum of products of two
  kernels times `4 × 4` determinants of columns.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

section General

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

local notation "ι" => (ExteriorAlgebra.ι ℂ : V Λ →ₗ[ℂ] N Λ)

/-- **The derivative of a product of vectors.** -/
theorem D_ιMulti (a : Sf Λ) : ∀ (n : ℕ) (v : Fin (n + 1) → V Λ),
    Grassmann.D a (ExteriorAlgebra.ιMulti ℂ (n + 1) v) =
      ∑ r : Fin (n + 1), ((-1 : ℂ) ^ (r : ℕ) * v r a) • ExteriorAlgebra.ιMulti ℂ n (v ∘ r.succAbove)
  | 0, v => by
    rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one, D_ι]
    simp [Algebra.algebraMap_eq_smul_one, ExteriorAlgebra.ιMulti_zero_apply]
  | n + 1, v => by
    rw [ExteriorAlgebra.ιMulti_succ_apply, D_ι_mul, D_ιMulti a n (Matrix.vecTail v), mul_sum]
    conv_rhs => rw [Fin.sum_univ_succ]
    rw [sub_eq_add_neg, ← sum_neg_distrib]
    congr 1
    · simp only [Fin.val_zero, pow_zero, one_mul]
      congr 2
    · refine sum_congr rfl fun r _ => ?_
      rw [ExteriorAlgebra.ιMulti_succ_apply, mul_smul_comm, ← neg_smul, Fin.val_succ, pow_succ]
      congr 1
      · simp [Matrix.vecTail]
      · congr 2
        funext i
        simp [Matrix.vecTail, Fin.succ_succAbove_succ]

theorem sum_comm4 {α β γ δ M : Type*} [AddCommMonoid M] [Fintype α] [Fintype β] [Fintype γ]
    [Fintype δ] (f : α → β → γ → δ → M) :
    ∑ x, ∑ y, ∑ r, ∑ s, f x y r s = ∑ r, ∑ s, ∑ x, ∑ y, f x y r s := by
  calc ∑ x, ∑ y, ∑ r, ∑ s, f x y r s = ∑ x, ∑ r, ∑ y, ∑ s, f x y r s :=
        sum_congr rfl fun x _ => sum_comm
    _ = ∑ r, ∑ x, ∑ y, ∑ s, f x y r s := sum_comm
    _ = ∑ r, ∑ x, ∑ s, ∑ y, f x y r s :=
        sum_congr rfl fun r _ => sum_congr rfl fun x _ => sum_comm
    _ = ∑ r, ∑ s, ∑ x, ∑ y, f x y r s := sum_congr rfl fun r _ => sum_comm

/-- The antisymmetric contraction kernel `K(u, w) = ⟨u, w⟩_C - ⟨w, u⟩_C`. -/
def Kc (C : Matrix Λ Λ ℂ) (u w : V Λ) : ℂ := pairC C u w - pairC C w u

/-- **The single cross contraction of two products of vectors.** -/
theorem Xc_ιMulti (C : Matrix Λ Λ ℂ) (n m : ℕ) (p : Fin (n + 1) → V Λ) (q : Fin (m + 1) → V Λ) :
    Xc C (ExteriorAlgebra.ιMulti ℂ (n + 1) p) (ExteriorAlgebra.ιMulti ℂ (m + 1) q) =
      ∑ r : Fin (n + 1), ∑ s : Fin (m + 1),
        ((-1 : ℂ) ^ (r : ℕ) * (-1 : ℂ) ^ (s : ℕ) * Kc C (p r) (q s)) •
        (ExteriorAlgebra.ιMulti ℂ n (p ∘ r.succAbove) *
          ExteriorAlgebra.ιMulti ℂ m (q ∘ s.succAbove)) := by
  simp only [Xc, D_ιMulti, sum_mul, mul_sum, smul_mul_smul_comm, smul_sum, ← sum_sub_distrib]
  rw [sum_comm4 (M := N Λ), sum_comm]
  refine sum_congr rfl fun r _ => sum_congr rfl fun s _ => ?_
  simp only [← sub_smul, smul_smul, ← sum_smul]
  congr 1
  simp only [Kc, pairC, mul_sub, sum_sub_distrib, mul_sum]
  congr 1 <;> refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => by ring

/-- **The double cross contraction of two products of vectors.** -/
theorem X2_ιMulti (C : Matrix Λ Λ ℂ) (n m : ℕ) (p : Fin (n + 1) → V Λ) (q : Fin (m + 1) → V Λ) :
    X2 C (ExteriorAlgebra.ιMulti ℂ (n + 1) p) (ExteriorAlgebra.ιMulti ℂ (m + 1) q) =
      ∑ r : Fin (n + 1), ∑ s : Fin (m + 1),
        (-((-1 : ℂ) ^ (r : ℕ) * (-1 : ℂ) ^ (s : ℕ) * Kc C (p r) (q s))) •
        Xc C (ExteriorAlgebra.ιMulti ℂ n (p ∘ r.succAbove))
          (ExteriorAlgebra.ιMulti ℂ m (q ∘ s.succAbove)) := by
  simp only [X2, D_ιMulti, ← XcL_apply, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_sum, ← sum_sub_distrib, smul_smul]
  rw [sum_comm4 (M := N Λ), sum_comm]
  refine sum_congr rfl fun r _ => sum_congr rfl fun s _ => ?_
  simp only [← sub_smul, smul_smul, ← sum_smul]
  congr 1
  simp only [Kc, pairC, mul_sub, sum_sub_distrib, mul_sum, neg_sub]
  congr 1 <;> refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => by ring

theorem X2_add_left (C : Matrix Λ Λ ℂ) (A A' B : N Λ) : X2 C (A + A') B = X2 C A B + X2 C A' B := by
  simp only [X2, map_add, Xc_add_left, ← sum_add_distrib, ← smul_add]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  congr 1; abel

theorem X2_add_right (C : Matrix Λ Λ ℂ) (A B B' : N Λ) : X2 C A (B + B') = X2 C A B + X2 C A B' := by
  simp only [X2, map_add, Xc_add_right, ← sum_add_distrib, ← smul_add]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  congr 1; abel

theorem X2_smul_left (C : Matrix Λ Λ ℂ) (r : ℂ) (A B : N Λ) : X2 C (r • A) B = r • X2 C A B := by
  simp only [X2, map_smul, Xc_smul_left, ← smul_sub, smul_sum, smul_comm r]

theorem X2_smul_right (C : Matrix Λ Λ ℂ) (r : ℂ) (A B : N Λ) : X2 C A (r • B) = r • X2 C A B := by
  simp only [X2, map_smul, Xc_smul_right, ← smul_sub, smul_sum, smul_comm r]

/-- `X₂` as a bilinear map. -/
def X2L (C : Matrix Λ Λ ℂ) : N Λ →ₗ[ℂ] N Λ →ₗ[ℂ] N Λ :=
  LinearMap.mk₂ ℂ (X2 C) (X2_add_left C) (X2_smul_left C) (X2_add_right C) (X2_smul_right C)

theorem X2L_apply (C : Matrix Λ Λ ℂ) (A B : N Λ) : X2L C A B = X2 C A B := rfl

end General

variable {d L N : ℕ} [NeZero L]

/-- **`μ₄` of the double contraction of two products of four vectors.** -/
theorem mu4_X2_ιMulti (C : Matrix (Lam d L N) (Lam d L N) ℂ) (b : Lam d L N) (κ κ' : Fin d)
    (p q : Fin 4 → V (Lam d L N)) :
    mu4 b κ κ' (X2 C (ExteriorAlgebra.ιMulti ℂ 4 p) (ExteriorAlgebra.ιMulti ℂ 4 q)) =
      ∑ r : Fin 4, ∑ s : Fin 4, ∑ r' : Fin 3, ∑ s' : Fin 3,
        -((-1 : ℂ) ^ (r : ℕ) * (-1 : ℂ) ^ (s : ℕ) * Kc C (p r) (q s)) *
          ((-1 : ℂ) ^ (r' : ℕ) * (-1 : ℂ) ^ (s' : ℕ) *
            Kc C ((p ∘ r.succAbove) r') ((q ∘ s.succAbove) s')) *
          (Matrix.of fun a c => col b κ κ'
            (Fin.append ((p ∘ r.succAbove) ∘ r'.succAbove) ((q ∘ s.succAbove) ∘ s'.succAbove) c)
              a).det := by
  rw [X2_ιMulti C 3 3 p q, mu4_sum]
  refine sum_congr rfl fun r _ => ?_
  rw [mu4_sum]
  refine sum_congr rfl fun s _ => ?_
  rw [mu4_smul, Xc_ιMulti C 2 2, mu4_sum, mul_sum]
  refine sum_congr rfl fun r' _ => ?_
  rw [mu4_sum, mul_sum]
  refine sum_congr rfl fun s' _ => ?_
  rw [mu4_smul, ExteriorAlgebra.ιMulti_mul_ιMulti, mu4_ιMulti]
  ring

/-- The two directions of the diagonal quartic monomial `M̂^{ii}`. -/
def pmdir (i : Fin d) : Fin 2 → Dir d := ![Sum.inl i, Sum.inr i]

theorem mono4s_diag (i : Fin d) (x : Lam d L N) :
    mono4s i i x = (1 / 2 : ℂ) • ∑ t : Fin 2, gmono4 (pmdir i t) (pmdir i t) x := by
  simp [mono4s, pmdir, Fin.sum_univ_two]

/-- **The explicit bubble coefficient.**
`-𝔅(C') = q_{j,j}(e_g)_g = (16 |B_+|)⁻¹ ∑_{x ∈ B_+} ∑_{y ∈ Λ} ∑_{i, i'} ∑_{t, t'}
μ₄ X₂(M^{e e}_x, M^{f f}_y)` with `e = ±e_i`, `f = ±e_{i'}`, and each term given by
`mu4_X2_ιMulti` for the legs `v4g e e x`, `v4g f f y`. -/
theorem FlowSeq.bubble_explicit (D : FlowSeq d L N) (hL : 2 ^ (d + 3) + 8 * d < L) {j : ℕ}
    (hj : j < N) {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) (i₀ : Fin d) :
    D.betaQ j j b i₀ (eC 3) (eC 3) 3 =
      (∑ i' : Fin d, ∑ y : Lam d L N, ∑ t' : Fin 2, ∑ i : Fin d, ∑ x ∈ Bp (L := L) (N := N) j b,
        ∑ t : Fin 2,
          mu4 (base (Bp (L := L) (N := N) j b)) i₀ i₀
            (X2 (D.C j) (ExteriorAlgebra.ιMulti ℂ 4 (v4g (pmdir i t) (pmdir i t) x))
              (ExteriorAlgebra.ιMulti ℂ 4 (v4g (pmdir i' t') (pmdir i' t') y)))) /
        (16 * (Bp (L := L) (N := N) j b).card) := by
  rw [D.bubble_eq hL hj hb, VcoupL_eg, VcoupL_eg]
  simp only [mono4sSet, mono4s_diag, ← X2L_apply, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, mu4_sum, mu4_smul]
  simp only [X2L_apply, gmono4]
  have hc : ((Bp (L := L) (N := N) j b).card : ℂ) ≠ 0 := by
    have := (isSmall_clo (isSmall_blockSet_of_mem hb)).2.1.1.card_pos
    exact_mod_cast this.ne'
  rw [div_eq_div_iff (mul_ne_zero (by norm_num) hc) (mul_ne_zero (by norm_num) hc)]
  simp only [mul_sum, sum_mul]
  refine sum_congr rfl fun i' _ => sum_congr rfl fun y _ => sum_congr rfl fun t' _ =>
    sum_congr rfl fun i _ => sum_congr rfl fun x _ => sum_congr rfl fun t _ => ?_
  ring

end

end Step2
