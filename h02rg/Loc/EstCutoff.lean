import Loc.EstDefs

/-!
# Smooth cut-off functions on `ℤ^d`

`cut m R t` is a smooth cut-off version (at scale `R`) of `t ↦ t^m` on `ℤ`: it equals `t^m` for
`|t| ≤ R`, vanishes for `|t| ≥ 2R`, and its discrete derivatives of order `k` are bounded by
`C R^{m - k}`.  `cutP m R u = ∏_i cut (m i) R (u i)` is the corresponding function on `ℤ^d`,
whose discrete derivatives factorise over the coordinates.
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD
open scoped ContDiff

/-- The 1-d difference `f(t + k) - f(t)`. -/
def dz (k : ℤ) (f : ℤ → ℝ) : ℤ → ℝ := fun t => f (t + k) - f t

/-- The real difference `F(x + h) - F(x)`. -/
def dr (h : ℝ) (F : ℝ → ℝ) : ℝ → ℝ := fun x => F (x + h) - F x

/-- The bump function equal to `1` on `[-1, 1]` and supported in `(-2, 2)`. -/
def bump0 : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- `τ ↦ τ^m φ(τ)`. -/
def cutθ (m : ℕ) (τ : ℝ) : ℝ := τ ^ m * bump0 τ

/-- A smooth cut-off version of `t ↦ t^m` at scale `R`: `R^m θ_m(t/R)` with
`θ_m(τ) = τ^m φ(τ)`, i.e. `t^m φ(t/R)` for `R ≠ 0`. -/
def cut (m : ℕ) (R : ℝ) : ℤ → ℝ := fun t => R ^ m * cutθ m (R⁻¹ * t)

theorem cutθ_contDiff (m : ℕ) : ContDiff ℝ ∞ (cutθ m) :=
  (contDiff_id.pow m).mul bump0.contDiff

theorem cutθ_hasCompactSupport (m : ℕ) : HasCompactSupport (cutθ m) :=
  show HasCompactSupport ((fun τ : ℝ => τ ^ m) * ⇑bump0) from bump0.hasCompactSupport.mul_left

theorem cut_eq {m : ℕ} {R : ℝ} (hR : 0 < R) {t : ℤ} (ht : |(t : ℝ)| ≤ R) :
    cut m R t = (t : ℝ) ^ m := by
  have h1 : bump0 (R⁻¹ * t) = 1 := by
    apply bump0.one_of_mem_closedBall
    rw [mem_closedBall_zero_iff, Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hR]
    show R⁻¹ * |(t:ℝ)| ≤ 1
    rw [inv_mul_le_iff₀ hR]; linarith
  simp only [cut, cutθ, h1, mul_one, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hR.ne', one_mul]

theorem cut_eq_zero {m : ℕ} {R : ℝ} (hR : 0 < R) {t : ℤ} (ht : 2 * R ≤ |(t : ℝ)|) :
    cut m R t = 0 := by
  have h1 : bump0 (R⁻¹ * t) = 0 := by
    apply bump0.zero_of_le_dist
    rw [Real.dist_0_eq_abs, abs_mul, abs_inv, abs_of_pos hR]
    show 2 ≤ R⁻¹ * |(t:ℝ)|
    rw [le_inv_mul_iff₀ hR]; linarith
  simp [cut, cutθ, h1]

theorem dr_contDiff (h : ℝ) {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (dr h F) :=
  (hF.comp (contDiff_id.add contDiff_const)).sub hF

theorem dr_iter_contDiff (h : ℝ) (k : ℕ) {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ ((dr h)^[k] F) := by
  induction k generalizing F with
  | zero => exact hF
  | succ k ih => rw [Function.iterate_succ_apply]; exact ih (dr_contDiff h hF)

theorem deriv_dr (h : ℝ) {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) : deriv (dr h F) = dr h (deriv F) := by
  funext x
  have hd : Differentiable ℝ F := hF.differentiable (by simp)
  have hd' : Differentiable ℝ (fun x => F (x + h)) := hd.comp (differentiable_id.add_const h)
  show deriv (fun x => F (x + h) - F x) x = _
  rw [deriv_fun_sub (hd' x) (hd x), deriv_comp_add_const]; rfl

theorem iterate_deriv_dr (h : ℝ) (n : ℕ) {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) :
    deriv^[n] (dr h F) = dr h (deriv^[n] F) := by
  induction n generalizing F with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, deriv_dr h hF]
    exact ih (ContDiff.iterate_deriv 1 hF)

theorem iterate_deriv_dr_iter (h : ℝ) (n k : ℕ) {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) :
    deriv^[n] ((dr h)^[k] F) = (dr h)^[k] (deriv^[n] F) := by
  induction k generalizing F with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih (dr_contDiff h hF),
      iterate_deriv_dr h n hF]

theorem abs_dr_le {h : ℝ} {F : ℝ → ℝ} (hF : Differentiable ℝ F) {M : ℝ}
    (hM : ∀ y, |deriv F y| ≤ M) (x : ℝ) : |dr h F x| ≤ M * |h| := by
  have := Convex.norm_image_sub_le_of_norm_deriv_le (fun y _ => hF y) (fun y _ => hM y)
    convex_univ (Set.mem_univ x) (Set.mem_univ (x + h))
  simpa [dr] using this

theorem abs_dr_iter_le (h : ℝ) (k : ℕ) {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {M : ℝ}
    (hM : ∀ y, |deriv^[k] F y| ≤ M) (x : ℝ) : |(dr h)^[k] F x| ≤ M * |h| ^ k := by
  induction k generalizing F M with
  | zero => simpa using hM x
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    have := ih (dr_contDiff h hF) (M := M * |h|) (fun y => by
      rw [iterate_deriv_dr h k hF]
      refine abs_dr_le ((ContDiff.iterate_deriv k hF).differentiable (by simp)) (fun y => ?_) y
      rw [← Function.iterate_succ_apply' deriv]; exact hM y)
    rw [pow_succ]; linarith [this]

theorem abs_dr_iter2_le (h₁ h₂ : ℝ) (k₁ k₂ : ℕ) {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {M : ℝ}
    (hM : ∀ y, |deriv^[k₁ + k₂] F y| ≤ M) (x : ℝ) :
    |(dr h₁)^[k₁] ((dr h₂)^[k₂] F) x| ≤ M * |h₂| ^ k₂ * |h₁| ^ k₁ := by
  refine abs_dr_iter_le h₁ k₁ (dr_iter_contDiff h₂ k₂ hF) (fun y => ?_) x
  rw [iterate_deriv_dr_iter h₂ k₁ k₂ hF]
  refine abs_dr_iter_le h₂ k₂ (ContDiff.iterate_deriv k₁ hF) (fun y => ?_) y
  rw [← Function.iterate_add_apply, add_comm]; exact hM y

theorem dz_comp_cast (h : ℤ) (G : ℝ → ℝ) : dz h (G ∘ Int.cast) = dr h G ∘ Int.cast := by
  funext t; simp [dz, dr]

theorem dz_iter_comp_cast (h : ℤ) (k : ℕ) (G : ℝ → ℝ) :
    (dz h)^[k] (G ∘ Int.cast) = (dr h)^[k] G ∘ Int.cast := by
  induction k generalizing G with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, dz_comp_cast, ih]

theorem iterate_deriv_hasCompactSupport (n : ℕ) {F : ℝ → ℝ} (hF : HasCompactSupport F) :
    HasCompactSupport (deriv^[n] F) := by
  induction n generalizing F with
  | zero => exact hF
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih hF.deriv

theorem iterate_deriv_scale (m n : ℕ) (R : ℝ) (y : ℝ) :
    deriv^[n] (fun x => R ^ m * cutθ m (R⁻¹ * x)) y =
      R ^ m * ((R⁻¹) ^ n * deriv^[n] (cutθ m) (R⁻¹ * y)) := by
  rw [← iteratedDeriv_eq_iterate, iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_const_mul (contDiff_infty.1 (cutθ_contDiff m) n), iteratedDeriv_eq_iterate]

theorem exists_cut_bound (m K : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R → ∀ k₁ k₂ : ℕ,
    k₁ + k₂ ≤ K → ∀ t : ℤ,
      |(dz 1)^[k₁] ((dz (-1))^[k₂] (cut m R)) t| ≤ C * R ^ m / R ^ (k₁ + k₂) := by
  have hB : ∀ k : ℕ, ∃ B : ℝ, ∀ x, ‖deriv^[k] (cutθ m) x‖ ≤ B := fun k =>
    ((ContDiff.iterate_deriv k (cutθ_contDiff m)).continuous).bounded_above_of_compact_support
      (iterate_deriv_hasCompactSupport k (cutθ_hasCompactSupport m))
  choose B hB using hB
  refine ⟨∑ k ∈ range (K + 1), max (B k) 0, sum_nonneg fun _ _ => le_max_right _ _, ?_⟩
  intro R hR k₁ k₂ hk t
  have hR0 : 0 < R := by linarith
  set C := ∑ k ∈ range (K + 1), max (B k) 0
  have hBC : B (k₁ + k₂) ≤ C := (le_max_left _ _).trans
    (single_le_sum (f := fun k => max (B k) 0) (fun _ _ => le_max_right _ _)
      (mem_range.2 (by omega)))
  have hcut : cut m R = (fun x => R ^ m * cutθ m (R⁻¹ * x)) ∘ Int.cast := rfl
  rw [hcut, dz_iter_comp_cast, dz_iter_comp_cast]
  have := abs_dr_iter2_le ((1 : ℤ) : ℝ) ((-1 : ℤ) : ℝ) k₁ k₂
    (F := fun x => R ^ m * cutθ m (R⁻¹ * x))
    (contDiff_const.mul ((cutθ_contDiff m).comp (contDiff_const.mul contDiff_id)))
    (M := R ^ m * ((R⁻¹) ^ (k₁ + k₂) * C)) (fun y => by
      rw [iterate_deriv_scale, abs_mul, abs_mul, abs_of_pos (by positivity),
        abs_of_pos (by positivity)]
      gcongr
      exact (hB _ _).trans hBC) (t : ℝ)
  simp only [Function.comp_apply]
  refine this.trans (le_of_eq ?_)
  simp only [Int.cast_one, Int.cast_neg, abs_neg, abs_one, one_pow, mul_one, inv_pow]
  field_simp

variable {d : ℕ}

/-- `u ↦ ∏_i cut (m i) R (u i)` on `ℤ^d`. -/
def cutP (m : Fin d → ℕ) (R : ℝ) (u : Zd d) : ℝ := ∏ i, cut (m i) R (u i)

theorem dz_comm : Function.Commute (dz 1) (dz (-1)) := by
  intro f; funext t; simp only [dz]
  rw [show t + (-1) + 1 = t + 1 + (-1) by ring]; ring

/-- The factor of the derivative of a coordinate product. -/
def dzT (a : Dir d → ℕ) (ψ : Fin d → ℤ → ℝ) (i : Fin d) : ℤ → ℝ :=
  (dz 1)^[a (Sum.inl i)] ((dz (-1))^[a (Sum.inr i)] (ψ i))

theorem prod_update_apply (ψ : Fin d → ℤ → ℝ) (j : Fin d) (χ : ℤ → ℝ) (y : Zd d) :
    ∏ i, Function.update ψ j χ i (y i) = χ (y j) * ∏ i ∈ univ.erase j, ψ i (y i) := by
  rw [← mul_prod_erase univ _ (mem_univ j)]
  simp only [Function.update_self]
  congr 1
  refine prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (ne_of_mem_erase hi)]

theorem prod_shift (ψ : Fin d → ℤ → ℝ) (j : Fin d) (c : ℤ) (y : Zd d) :
    ∏ i, ψ i ((y + (Pi.single j c : Zd d)) i) - ∏ i, ψ i (y i) =
      ∏ i, Function.update ψ j (dz c (ψ j)) i (y i) := by
  rw [prod_update_apply, ← mul_prod_erase univ _ (mem_univ j),
    ← mul_prod_erase univ (fun i => ψ i (y i)) (mem_univ j)]
  have : ∀ i ∈ univ.erase j, ψ i ((y + (Pi.single j c : Zd d)) i) = ψ i (y i) := fun i hi => by
    simp [ne_of_mem_erase hi]
  rw [prod_congr rfl this]
  simp [dz, sub_mul]

theorem D1_prod (a : Dir d → ℕ) (ψ : Fin d → ℤ → ℝ) (u : Zd d) :
    D1 (fun b v => b +ᵥ v) a (fun v => ∏ i, ψ i (v i)) u = ∏ i, dzT a ψ i (u i) := by
  obtain ⟨n, hn⟩ : ∃ n, Grassmann.mabs a = n := ⟨_, rfl⟩
  induction n generalizing a ψ with
  | zero =>
    rw [mabs_eq_zero hn, D1_zero _ (fun y => zero_vadd _ y)]
    rfl
  | succ n ih =>
    obtain ⟨e, he⟩ : ∃ e, a e ≠ 0 := by
      by_contra h; push Not at h
      have : a = 0 := funext h
      rw [this] at hn; simp [Grassmann.mabs] at hn
    set a' := a - Pi.single e 1
    have ha : a = a' + Pi.single e 1 := by
      funext e'; by_cases h : e' = e
      · subst h; simp [a']; omega
      · simp [a', h]
    have hn' : Grassmann.mabs a' = n := by
      rw [ha, mabs_add, mabs_single] at hn; omega
    rw [ha, D1_succ _ (fun b b' y => add_vadd b b' y)]
    simp only [single_vaddZ]
    rcases e with j | j
    · simp only [dirZ]
      simp_rw [prod_shift ψ j 1]
      rw [ih a' _ hn']
      refine prod_congr rfl fun i _ => ?_
      simp only [dzT]
      by_cases hij : i = j
      · subst hij
        simp only [Function.update_self, Pi.add_apply, Pi.single_eq_same, Pi.single_apply,
          reduceCtorEq, if_false, add_zero]
        rw [Function.iterate_succ_apply, (dz_comm.iterate_right _) (ψ i)]
      · simp [hij]
    · simp only [dirZ]
      have : ∀ y : Zd d, y + -Pi.single j (1 : ℤ) = y + Pi.single j (-1) := fun y => by
        rw [Pi.single_neg]
      simp_rw [this, prod_shift ψ j (-1)]
      rw [ih a' _ hn']
      refine prod_congr rfl fun i _ => ?_
      simp only [dzT]
      by_cases hij : i = j
      · subst hij
        simp only [Function.update_self, Pi.add_apply, Pi.single_eq_same, Pi.single_apply,
          reduceCtorEq, if_false, add_zero]
        rw [Function.iterate_succ_apply]
      · simp [hij]

/-- The derivatives of `cutP` factorise over the coordinates. -/
theorem D1_cutP (m : Fin d → ℕ) (R : ℝ) (a : Dir d → ℕ) (u : Zd d) :
    D1 (fun b v => b +ᵥ v) a (cutP m R) u =
      ∏ i, (dz 1)^[a (Sum.inl i)] ((dz (-1))^[a (Sum.inr i)] (cut (m i) R)) (u i) :=
  D1_prod a (fun i => cut (m i) R) u

theorem mabs_eq_sum_dir (a : Dir d → ℕ) :
    Grassmann.mabs a = ∑ i, (a (Sum.inl i) + a (Sum.inr i)) := by
  rw [Grassmann.mabs, Fintype.sum_sum_type, sum_add_distrib]

theorem exists_D1_cutP_bound (d K Mx : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ m : Fin d → ℕ, (∀ i, m i ≤ Mx) →
    ∀ R : ℝ, 1 ≤ R → ∀ a : Dir d → ℕ, mabs a ≤ K → ∀ u : Zd d,
      |D1 (fun b v => b +ᵥ v) a (cutP m R) u| ≤ C * R ^ (∑ i, m i) / R ^ mabs a := by
  have h := fun m' : ℕ => exists_cut_bound m' K
  choose B hB0 hB using h
  set C0 : ℝ := 1 + ∑ m' ∈ range (Mx + 1), B m'
  have hC0 : 0 ≤ C0 := add_nonneg zero_le_one (sum_nonneg fun k _ => hB0 k)
  have hBC : ∀ m' ≤ Mx, B m' ≤ C0 := fun m' hm' => by
    have := single_le_sum (f := B) (fun k _ => hB0 k) (mem_range.2 (Nat.lt_succ_of_le hm'))
    simp only [C0]; linarith
  refine ⟨C0 ^ d, by positivity, ?_⟩
  intro m hm R hR a ha u
  have hR0 : 0 < R := by linarith
  rw [D1_cutP, abs_prod]
  have hk : ∀ i, a (Sum.inl i) + a (Sum.inr i) ≤ K := fun i => by
    refine le_trans ?_ ha
    rw [mabs_eq_sum_dir]
    exact single_le_sum (f := fun i => a (Sum.inl i) + a (Sum.inr i)) (fun _ _ => by positivity)
      (mem_univ i)
  calc ∏ i, |(dz 1)^[a (Sum.inl i)] ((dz (-1))^[a (Sum.inr i)] (cut (m i) R)) (u i)|
      ≤ ∏ i, (C0 * R ^ (m i) / R ^ (a (Sum.inl i) + a (Sum.inr i))) := by
        refine prod_le_prod (fun _ _ => abs_nonneg _) fun i _ => ?_
        refine (hB (m i) R hR _ _ (hk i) (u i)).trans ?_
        gcongr
        exact hBC _ (hm i)
    _ = C0 ^ d * R ^ (∑ i, m i) / R ^ mabs a := by
        rw [prod_div_distrib, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin,
          prod_pow_eq_pow_sum, prod_pow_eq_pow_sum, mabs_eq_sum_dir]

theorem cutP_eq (m : Fin d → ℕ) {R : ℝ} (hR : 0 < R) {u : Zd d} (hu : (supNormZ u : ℝ) ≤ R) :
    cutP m R u = ∏ i, (u i : ℝ) ^ (m i) := by
  refine prod_congr rfl fun i _ => cut_eq hR ?_
  have := natAbs_le_supNormZ u i
  have h2 : ((u i).natAbs : ℝ) ≤ supNormZ u := by exact_mod_cast this
  rw [Nat.cast_natAbs, Int.cast_abs] at h2
  linarith

theorem cutP_eq_zero (m : Fin d → ℕ) {R : ℝ} (hR : 0 < R) {u : Zd d}
    (hu : 2 * R ≤ (supNormZ u : ℝ)) : cutP m R u = 0 := by
  have hne : (univ : Finset (Fin d)).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    have : supNormZ u = 0 := by simp [supNormZ, h]
    rw [this] at hu; simp at hu; linarith
  obtain ⟨i, -, hi⟩ := exists_mem_eq_sup univ hne (fun i => (u i).natAbs)
  refine prod_eq_zero (mem_univ i) (cut_eq_zero hR ?_)
  have h2 : ((u i).natAbs : ℝ) = supNormZ u := by rw [supNormZ, hi]
  rw [Nat.cast_natAbs, Int.cast_abs] at h2
  linarith

/-- The derivatives of `cutP` vanish far from the support. -/
theorem D1_cutP_eq_zero (m : Fin d → ℕ) {R : ℝ} (hR : 0 < R) (a : Dir d → ℕ) {u : Zd d}
    (hu : 2 * R + mabs a ≤ (supNormZ u : ℝ)) : D1 (fun b v => b +ᵥ v) a (cutP m R) u = 0 := by
  rw [D1_eq_sum]
  refine sum_eq_zero fun b hb => ?_
  rw [cutP_eq_zero m hR, mul_zero]
  have hba : Grassmann.mabs b ≤ Grassmann.mabs a :=
    sum_le_sum fun e _ => (mem_Iic.1 hb) e
  have h1 : supNormZ u ≤ supNormZ (b +ᵥ u) + Grassmann.mabs a := by
    have := supNormZ_add_le (b +ᵥ u) (-dirHomZ b)
    rw [vaddZ_def, add_neg_cancel_comm, supNormZ_neg] at this
    rw [vaddZ_def]
    have := supNormZ_dirHomZ_le b
    omega
  have h2 : (supNormZ u : ℝ) ≤ supNormZ (b +ᵥ u) + Grassmann.mabs a := by exact_mod_cast h1
  linarith

end

end Loc
