import Step2.D2.D2Bub1

/-!
# The bubble functional `𝔅` for translation-invariant covariances (`prop:d2`, (R4))

* `negBub C X κ`: the explicit sum of `FlowSeq.bubble_explicit`, i.e.
  `-𝔅_X(C) = (16|X|)^{-1} ∑_{x ∈ X} ∑_y ∑_{e = ±e_i} ∑_{f = ±e_{i'}} μ₄ X₂(M^{ee}_x, M^{ff}_y)`;
  `FlowSeq.betaQ_eq_negBub`: `q_{j,j}(e_g)_g = negBub (D.C j) (B_+) i₀` (this is `bubble_explicit`).
* `bubF cC κ z`: the translation-invariant density (in the displacement `z = y - x`);
* `negBub_transl`: if `C(a, b) = c(a - b)` with `c` of range `R`, and every `x ∈ X` is at distance
  `< n/2 - R - 3` from the base point, then `-𝔅_X(C) = ⅛ ∑_z bubF c κ z`, independent of `X`.
-/

namespace Step2

open Step Finset Grassmann Loc FRD

noncomputable section

variable {d L N : ℕ} [NeZero L]

/-! ### Elementary properties of `bubPoly` -/

theorem bubPoly_congr {Λ Λ' : Type*} (C : Matrix Λ Λ ℂ) (C' : Matrix Λ' Λ' ℂ) {x xe y yf : Λ}
    {x' xe' y' yf' : Λ'} (lx lxe ly lyf : ℂ)
    (h1 : C x y = C' x' y') (h2 : C x yf = C' x' yf') (h3 : C xe y = C' xe' y')
    (h4 : C xe yf = C' xe' yf') (h5 : C y x = C' y' x') (h6 : C y xe = C' y' xe')
    (h7 : C yf x = C' yf' x') (h8 : C yf xe = C' yf' xe') :
    bubPoly C x xe y yf lx lxe ly lyf = bubPoly C' x' xe' y' yf' lx lxe ly lyf := by
  unfold bubPoly; rw [h1, h2, h3, h4, h5, h6, h7, h8]

theorem bubPoly_shift {Λ : Type*} (C : Matrix Λ Λ ℂ) (x xe y yf : Λ) (lx lxe ly lyf : ℂ) :
    bubPoly C x xe y yf lx lxe ly lyf = bubPoly C x xe y yf 0 (lxe - lx) (ly - lx) (lyf - lx) := by
  unfold bubPoly; ring

theorem bubPoly_eq_zero {Λ : Type*} (C : Matrix Λ Λ ℂ) {x xe y yf : Λ} (lx lxe ly lyf : ℂ)
    (h1 : C x y = 0) (h2 : C x yf = 0) (h3 : C xe y = 0)
    (h4 : C xe yf = 0) (h5 : C y x = 0) (h6 : C y xe = 0)
    (h7 : C yf x = 0) (h8 : C yf xe = 0) : bubPoly C x xe y yf lx lxe ly lyf = 0 := by
  unfold bubPoly; rw [h1, h2, h3, h4, h5, h6, h7, h8]; ring

/-! ### The functional -/

/-- `-𝔅_X(C)`: the sum of `FlowSeq.bubble_explicit`. -/
def negBub (C : Matrix (Lam d L N) (Lam d L N) ℂ) (X : Finset (Lam d L N)) (κ : Fin d) : ℂ :=
  (∑ i' : Fin d, ∑ y : Lam d L N, ∑ t' : Fin 2, ∑ i : Fin d, ∑ x ∈ X, ∑ t : Fin 2,
    mu4 (base X) κ κ
      (X2 C (ExteriorAlgebra.ιMulti ℂ 4 (v4g (pmdir i t) (pmdir i t) x))
        (ExteriorAlgebra.ιMulti ℂ 4 (v4g (pmdir i' t') (pmdir i' t') y)))) / (16 * X.card)

/-- **`q_{j,j}(e_g)_g = -𝔅(C')`** in the form `negBub`. -/
theorem FlowSeq.betaQ_eq_negBub (D : FlowSeq d L N) (hL : 2 ^ (d + 3) + 8 * d < L) {j : ℕ}
    (hj : j < N) {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) (i₀ : Fin d) :
    D.betaQ j j b i₀ (eC 3) (eC 3) 3 = negBub (D.C j) (Bp (L := L) (N := N) j b) i₀ :=
  D.bubble_explicit hL hj hb i₀

/-- The translation-invariant density in the displacement `z`. -/
def bubF (cC : Lam d L N → ℂ) (κ : Fin d) (z : Lam d L N) : ℂ :=
  ∑ i' : Fin d, ∑ t' : Fin 2, ∑ i : Fin d, ∑ t : Fin 2,
    bubPoly (fun a b : Lam d L N => cC (a - b)) 0 (dirVec (pmdir i t)) z (z + dirVec (pmdir i' t'))
      0 (dirZ (pmdir i t) κ) (rep z κ) (rep z κ + dirZ (pmdir i' t') κ)

theorem supNorm_add_dir_ge (z : Lam d L N) (e : Dir d) :
    supNorm z ≤ supNorm (z + dirVec e) + 1 := by
  have h := supNorm_add_le (z + dirVec e) (-dirVec e)
  rw [add_neg_cancel_right, supNorm_neg] at h
  have := supNorm_dirVec_le (n := L ^ N) e
  omega

theorem supNorm_le_of_sub (z w : Lam d L N) : supNorm z ≤ supNorm w + supNorm (z - w) := by
  have h := supNorm_add_le w (z - w)
  rw [add_sub_cancel] at h
  exact h

/-- The term of `negBub` at `(x, x + z)` is the density at `z`. -/
theorem term_transl {C : Matrix (Lam d L N) (Lam d L N) ℂ} {cC : Lam d L N → ℂ} {R : ℕ}
    (hC : ∀ a b, C a b = cC (a - b)) (hR : ∀ z, R < supNorm z → cC z = 0)
    {b x : Lam d L N} (hx : 2 * (supNorm (x - b) + R + 3) < L ^ N) (κ : Fin d) (e f : Dir d)
    (z : Lam d L N) :
    bubPoly C x (x + dirVec e) (x + z) (x + z + dirVec f) (lift b x κ) (lift b (x + dirVec e) κ)
        (lift b (x + z) κ) (lift b (x + z + dirVec f) κ) =
      bubPoly (fun a b : Lam d L N => cC (a - b)) 0 (dirVec e) z (z + dirVec f)
        0 (dirZ e κ) (rep z κ) (rep z κ + dirZ f κ) := by
  have he := supNorm_dirVec_le (n := L ^ N) e
  have hf := supNorm_dirVec_le (n := L ^ N) f
  by_cases hz : supNorm z ≤ R + 2
  · -- lifts are honest
    rw [bubPoly_shift]
    have l1 : lift b (x + dirVec e) = lift b x + fun i => (dirZ e i : ℝ) := by
      rw [← prj_dirZ e, lift_add]
      have := supNormZ_dirZ e; omega
    have l2 : lift b (x + z) = lift b x + fun i => (rep z i : ℝ) := by
      conv_lhs => rw [← prj_rep z]
      rw [lift_add]
      rw [supNormZ_rep_eq]; omega
    have l3 : lift b (x + z + dirVec f) = lift b x + fun i => ((rep z + dirZ f) i : ℝ) := by
      rw [← prj_dirZ f, ← prj_rep z, add_assoc, ← prj_add, lift_add, prj_rep]
      have := supNormZ_add_le (rep z) (dirZ f)
      have := supNormZ_dirZ f
      rw [supNormZ_rep_eq] at *
      omega
    have m1 : ((lift b (x + dirVec e) κ : ℝ) : ℂ) - (lift b x κ : ℂ) = (dirZ e κ : ℂ) := by
      rw [l1]; simp
    have m2 : ((lift b (x + z) κ : ℝ) : ℂ) - (lift b x κ : ℂ) = (rep z κ : ℂ) := by
      rw [l2]; simp
    have m3 : ((lift b (x + z + dirVec f) κ : ℝ) : ℂ) - (lift b x κ : ℂ) =
        (rep z κ : ℂ) + (dirZ f κ : ℂ) := by
      rw [l3]; simp
    rw [m1, m2, m3]
    refine bubPoly_congr _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (rw [hC]; exact congrArg cC (by abel))
  · -- all entries vanish
    push_neg at hz
    have hzf := supNorm_add_dir_ge z f
    have e1 : ∀ a : Lam d L N, supNorm z ≤ supNorm a + 2 → cC a = 0 := fun a ha => hR a (by omega)
    have n1 : supNorm z ≤ supNorm (-z) + 2 := by rw [supNorm_neg]; omega
    have n2 : supNorm z ≤ supNorm (-(z + dirVec f)) + 2 := by rw [supNorm_neg]; omega
    have n3 : supNorm z ≤ supNorm (dirVec e - z) + 2 := by
      have := supNorm_le_of_sub z (z - dirVec e); rw [sub_sub_cancel] at this
      have h' : supNorm (dirVec e - z) = supNorm (z - dirVec e) := by rw [← supNorm_neg, neg_sub]
      omega
    have n4 : supNorm z ≤ supNorm (dirVec e - (z + dirVec f)) + 2 := by
      have := supNorm_le_of_sub (z + dirVec f) (z + dirVec f - dirVec e)
      rw [sub_sub_cancel] at this
      have h' : supNorm (dirVec e - (z + dirVec f)) = supNorm (z + dirVec f - dirVec e) := by
        rw [← supNorm_neg, neg_sub]
      omega
    have n5 : supNorm z ≤ supNorm z + 2 := by omega
    have n6 : supNorm z ≤ supNorm (z - dirVec e) + 2 := by
      have := supNorm_le_of_sub z (z - dirVec e); rw [sub_sub_cancel] at this; omega
    have n7 : supNorm z ≤ supNorm (z + dirVec f) + 2 := by omega
    have n8 : supNorm z ≤ supNorm (z + dirVec f - dirVec e) + 2 := by
      have := supNorm_le_of_sub (z + dirVec f) (z + dirVec f - dirVec e)
      rw [sub_sub_cancel] at this; omega
    have z1 : cC (-z) = 0 := e1 _ n1
    have z2 : cC (-(z + dirVec f)) = 0 := e1 _ n2
    have z3 : cC (dirVec e - z) = 0 := e1 _ n3
    have z4 : cC (dirVec e - (z + dirVec f)) = 0 := e1 _ n4
    have z5 : cC z = 0 := e1 _ n5
    have z6 : cC (z - dirVec e) = 0 := e1 _ n6
    have z7 : cC (z + dirVec f) = 0 := e1 _ n7
    have z8 : cC (z + dirVec f - dirVec e) = 0 := e1 _ n8
    rw [bubPoly_eq_zero, bubPoly_eq_zero]
    · show cC (0 - z) = 0; rw [zero_sub]; exact z1
    · show cC (0 - (z + dirVec f)) = 0; rw [zero_sub]; exact z2
    · show cC (dirVec e - z) = 0; exact z3
    · show cC (dirVec e - (z + dirVec f)) = 0; exact z4
    · show cC (z - 0) = 0; rw [sub_zero]; exact z5
    · show cC (z - dirVec e) = 0; exact z6
    · show cC (z + dirVec f - 0) = 0; rw [sub_zero]; exact z7
    · show cC (z + dirVec f - dirVec e) = 0; exact z8
    · rw [hC, show x - (x + z) = -z by abel]; exact z1
    · rw [hC, show x - (x + z + dirVec f) = -(z + dirVec f) by abel]; exact z2
    · rw [hC, show x + dirVec e - (x + z) = dirVec e - z by abel]; exact z3
    · rw [hC, show x + dirVec e - (x + z + dirVec f) = dirVec e - (z + dirVec f) by abel]; exact z4
    · rw [hC, show x + z - x = z by abel]; exact z5
    · rw [hC, show x + z - (x + dirVec e) = z - dirVec e by abel]; exact z6
    · rw [hC, show x + z + dirVec f - x = z + dirVec f by abel]; exact z7
    · rw [hC, show x + z + dirVec f - (x + dirVec e) = z + dirVec f - dirVec e by abel]; exact z8

/-- **`-𝔅` for a translation-invariant covariance of finite range.** If `C(a, b) = c(a - b)`,
`c(z) = 0` for `|z|_∞ > R`, and `2(|x - b_X|_∞ + R + 3) < L^N` on `X ≠ ∅`, then
`-𝔅_X(C) = ⅛ ∑_z bubF c κ z`. -/
theorem negBub_transl {C : Matrix (Lam d L N) (Lam d L N) ℂ} {cC : Lam d L N → ℂ} {R : ℕ}
    (hC : ∀ a b, C a b = cC (a - b)) (hR : ∀ z, R < supNorm z → cC z = 0)
    {X : Finset (Lam d L N)} (hne : X.Nonempty)
    (hX : ∀ x ∈ X, 2 * (supNorm (x - base X) + R + 3) < L ^ N) (κ : Fin d) :
    negBub C X κ = (∑ z, bubF cC κ z) / 8 := by
  set T : Fin d → Lam d L N → Fin 2 → Fin d → Lam d L N → Fin 2 → ℂ := fun i' y t' i x t =>
    mu4 (base X) κ κ
      (X2 C (ExteriorAlgebra.ιMulti ℂ 4 (v4g (pmdir i t) (pmdir i t) x))
        (ExteriorAlgebra.ιMulti ℂ 4 (v4g (pmdir i' t') (pmdir i' t') y)))
  have hS : (∑ i' : Fin d, ∑ y : Lam d L N, ∑ t' : Fin 2, ∑ i : Fin d, ∑ x ∈ X, ∑ t : Fin 2,
      T i' y t' i x t) = ∑ x ∈ X, ∑ y : Lam d L N, ∑ i' : Fin d, ∑ t' : Fin 2, ∑ i : Fin d,
        ∑ t : Fin 2, T i' y t' i x t := by
    calc _ = ∑ i' : Fin d, ∑ y : Lam d L N, ∑ t' : Fin 2, ∑ x ∈ X, ∑ i : Fin d, ∑ t : Fin 2,
          T i' y t' i x t :=
          sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_comm
      _ = ∑ i' : Fin d, ∑ y : Lam d L N, ∑ x ∈ X, ∑ t' : Fin 2, ∑ i : Fin d, ∑ t : Fin 2,
          T i' y t' i x t := sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_comm
      _ = ∑ i' : Fin d, ∑ x ∈ X, ∑ y : Lam d L N, ∑ t' : Fin 2, ∑ i : Fin d, ∑ t : Fin 2,
          T i' y t' i x t := sum_congr rfl fun _ _ => sum_comm
      _ = ∑ x ∈ X, ∑ i' : Fin d, ∑ y : Lam d L N, ∑ t' : Fin 2, ∑ i : Fin d, ∑ t : Fin 2,
          T i' y t' i x t := sum_comm
      _ = _ := sum_congr rfl fun _ _ => sum_comm
  have hx : ∀ x ∈ X, (∑ y : Lam d L N, ∑ i' : Fin d, ∑ t' : Fin 2, ∑ i : Fin d,
      ∑ t : Fin 2, T i' y t' i x t) = 2 * ∑ z, bubF cC κ z := by
    intro x hxX
    rw [← Equiv.sum_comp (Equiv.addLeft x), mul_sum]
    refine sum_congr rfl fun z _ => ?_
    simp only [Equiv.coe_addLeft, T, bubF, mul_sum]
    refine sum_congr rfl fun i' _ => sum_congr rfl fun t' _ => sum_congr rfl fun i _ =>
      sum_congr rfl fun t _ => ?_
    rw [mu4_X2_v4g, term_transl hC hR (hX x hxX)]
  rw [negBub, hS, sum_congr rfl hx, sum_const, nsmul_eq_mul]
  have hc : (X.card : ℂ) ≠ 0 := by exact_mod_cast hne.card_pos.ne'
  field_simp
  ring

end

end Step2
