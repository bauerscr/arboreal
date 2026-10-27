import FRD.Decomp

/-!
# Lattice sums

* Jordan's inequality gives `λ(k) ≥ 16 |v|^2 / n^2`, `v_i = |m_i|` (`lam_ge`);
* `|Λ|^{-1} ∑_k (1 + t^2 λ(k)/(4d))^{-d} ≤ C t^{-d}` for `1 ≤ t ≤ n` (`latt_small`), and the
  same for `t ≥ n` when the zero mode is removed (`latt_large`).
-/

namespace FRD

noncomputable section

open Finset Grassmann

variable {d n : ℕ} [NeZero n]

theorem zabs_le_val (z : ZMod n) : zabs z ≤ z.val := min_le_left _ _
theorem zabs_le_sub_val (z : ZMod n) : zabs z ≤ n - z.val := min_le_right _ _

theorem zabs_eq_zero_iff (z : ZMod n) : zabs z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have hlt := ZMod.val_lt z
    unfold zabs at h
    have : z.val = 0 := by omega
    exact (ZMod.val_eq_zero z).1 this
  · rintro rfl; simp [zabs]

/-- Jordan's inequality on the torus: `16 |z|^2 / n^2 ≤ 2 - 2 cos (2π z / n)`. -/
theorem zabs_sq_le (z : ZMod n) :
    16 * (zabs z : ℝ) ^ 2 / (n : ℝ) ^ 2 ≤ 2 - 2 * Real.cos (2 * Real.pi * z.val / n) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (NeZero.pos n)
  set y := Real.pi * z.val / n with hy
  have hc : 2 - 2 * Real.cos (2 * Real.pi * z.val / n) = 4 * Real.sin y ^ 2 := by
    rw [show 2 * Real.pi * z.val / n = 2 * y by rw [hy]; ring, Real.cos_two_mul, Real.cos_sq']
    ring
  rw [hc]
  have hlt := ZMod.val_lt z
  -- `2 |z| / n ≤ sin y`
  have key : 2 * (zabs z : ℝ) / n ≤ Real.sin y := by
    by_cases h : z.val ≤ n - z.val
    · have h1 : (2 * z.val : ℝ) ≤ n := by
        have : 2 * z.val ≤ n := by omega
        exact_mod_cast this
      have hy0 : 0 ≤ y := by positivity
      have hy1 : y ≤ Real.pi / 2 := by
        rw [hy, div_le_iff₀ hn]; nlinarith [Real.pi_pos]
      have := Real.mul_le_sin hy0 hy1
      calc 2 * (zabs z : ℝ) / n ≤ 2 * z.val / n := by
            gcongr; exact_mod_cast zabs_le_val z
        _ = 2 / Real.pi * y := by rw [hy]; field_simp
        _ ≤ _ := this
    · have h1 : (2 * (n - z.val : ℕ) : ℝ) ≤ n := by
        have : 2 * (n - z.val) ≤ n := by omega
        exact_mod_cast this
      set y' := Real.pi * ((n - z.val : ℕ) : ℝ) / n with hy'
      have hyy : Real.sin y = Real.sin y' := by
        rw [← Real.sin_pi_sub, hy, hy', Nat.cast_sub hlt.le]; congr 1; field_simp
      have hy0 : 0 ≤ y' := by positivity
      have hy1 : y' ≤ Real.pi / 2 := by
        rw [hy', div_le_iff₀ hn]; nlinarith [Real.pi_pos]
      have := Real.mul_le_sin hy0 hy1
      rw [hyy]
      calc 2 * (zabs z : ℝ) / n ≤ 2 * ((n - z.val : ℕ) : ℝ) / n := by
            gcongr; exact_mod_cast zabs_le_sub_val z
        _ = 2 / Real.pi * y' := by rw [hy']; field_simp
        _ ≤ _ := this
  have h0 : 0 ≤ 2 * (zabs z : ℝ) / n := by positivity
  have := pow_le_pow_left₀ h0 key 2
  calc 16 * (zabs z : ℝ) ^ 2 / (n : ℝ) ^ 2 = 4 * (2 * (zabs z : ℝ) / n) ^ 2 := by
        field_simp; ring
    _ ≤ 4 * Real.sin y ^ 2 := by linarith

/-- `λ(k) ≥ 16 |v|^2 / n^2`. -/
theorem lam_ge (m : Torus d n) :
    16 / (n : ℝ) ^ 2 * ∑ i, (zabs (co m i) : ℝ) ^ 2 ≤ lam m := by
  rw [mul_sum]
  refine sum_le_sum fun i _ => ?_
  have := zabs_sq_le (co m i)
  rw [cosk]
  calc 16 / (n : ℝ) ^ 2 * (zabs (co m i) : ℝ) ^ 2 = 16 * (zabs (co m i) : ℝ) ^ 2 / (n : ℝ) ^ 2 := by
        ring
    _ ≤ _ := this

theorem one_le_sum_zabs_sq {m : Torus d n} (hm : m ≠ 0) :
    (1 : ℝ) ≤ ∑ i, (zabs (co m i) : ℝ) ^ 2 := by
  obtain ⟨i, hi⟩ : ∃ i, co m i ≠ 0 := by
    by_contra h; push Not at h; exact hm (funext h)
  have h1 : 1 ≤ zabs (co m i) := Nat.one_le_iff_ne_zero.2 ((zabs_eq_zero_iff _).not.2 hi)
  have h2 : (1 : ℝ) ≤ (zabs (co m i) : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ zabs (co m i) := by exact_mod_cast h1
    nlinarith
  exact h2.trans (single_le_sum (f := fun i => (zabs (co m i) : ℝ) ^ 2)
    (fun _ _ => by positivity) (mem_univ i))

/-! ### One-dimensional sums -/

theorem sum_zmod_val (f : ℕ → ℝ) : ∑ z : ZMod n, f z.val = ∑ v ∈ range n, f v := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos (NeZero.pos n)).symm⟩
  exact Fin.sum_univ_eq_sum_range f (k + 1)

theorem integral_inv_one_add_sq_mul_le {τ : ℝ} (hτ : 0 < τ) (b : ℝ) :
    ∫ x in (0 : ℝ)..b, (1 + (τ * x) ^ 2)⁻¹ ≤ Real.pi / 2 / τ := by
  rw [intervalIntegral.integral_comp_mul_left (fun x => (1 + x ^ 2)⁻¹) hτ.ne',
    integral_inv_one_add_sq, mul_zero, Real.arctan_zero, sub_zero, smul_eq_mul]
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (Real.arctan_lt_pi_div_two _).le (inv_nonneg.2 hτ.le)

/-- `∑_{z ∈ ℤ/nℤ} (1 + τ^2 |z|^2)^{-1} ≤ 1 + π/τ`. -/
theorem sum_zmod_le {τ : ℝ} (hτ : 0 < τ) :
    ∑ z : ZMod n, (1 + (τ * zabs z) ^ 2)⁻¹ ≤ 1 + Real.pi / τ := by
  set g : ℝ → ℝ := fun x => (1 + (τ * x) ^ 2)⁻¹ with hg
  have hg0 : ∀ x, 0 ≤ g x := fun x => by positivity
  have hanti : AntitoneOn g (Set.Ici 0) := by
    intro a ha b hb hab
    simp only [hg]
    refine inv_anti₀ (by positivity) ?_
    have : τ * a ≤ τ * b := mul_le_mul_of_nonneg_left hab hτ.le
    nlinarith [mul_nonneg hτ.le (show (0 : ℝ) ≤ a from ha)]
  have h1 : ∀ z : ZMod n, g (zabs z) ≤ g z.val + g (n - z.val : ℕ) := by
    intro z
    unfold zabs
    rcases min_choice z.val (n - z.val) with h | h <;> rw [h]
    · linarith [hg0 ((n - z.val : ℕ) : ℝ)]
    · linarith [hg0 (z.val : ℝ)]
  have hsum1 : ∑ z : ZMod n, g z.val = ∑ v ∈ range n, g v := sum_zmod_val (fun v => g v)
  have hsum2 : ∑ z : ZMod n, g (n - z.val : ℕ) = ∑ v ∈ range n, g (v + 1 : ℕ) := by
    rw [sum_zmod_val (fun v => g (n - v : ℕ)), ← sum_range_reflect]
    refine sum_congr rfl fun v hv => ?_
    rw [mem_range] at hv
    congr 2; omega
  have hsum3 : ∑ v ∈ range n, g v ≤ 1 + ∑ v ∈ range n, g (v + 1 : ℕ) := by
    obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos (NeZero.pos n)).symm⟩
    rw [hk, sum_range_succ', sum_range_succ]
    have : g ((0 : ℕ) : ℝ) = 1 := by simp [hg]
    rw [this]
    have : ∀ v : ℕ, g ((v + 1 : ℕ) : ℝ) = g (((v + 1 : ℕ) : ℕ) : ℝ) := fun _ => rfl
    linarith [hg0 (((k + 1 : ℕ) : ℕ) : ℝ)]
  have hint : ∑ v ∈ range n, g (v + 1 : ℕ) ≤ Real.pi / 2 / τ := by
    have := AntitoneOn.sum_le_integral (f := g) (x₀ := 0) (a := n)
      (hanti.mono fun x hx => hx.1)
    simp only [zero_add] at this
    exact this.trans (integral_inv_one_add_sq_mul_le hτ _)
  calc ∑ z : ZMod n, (1 + (τ * zabs z) ^ 2)⁻¹ = ∑ z : ZMod n, g (zabs z) := rfl
    _ ≤ ∑ z : ZMod n, (g z.val + g (n - z.val : ℕ)) := sum_le_sum fun z _ => h1 z
    _ = ∑ v ∈ range n, g v + ∑ v ∈ range n, g (v + 1 : ℕ) := by
        rw [sum_add_distrib, hsum1, hsum2]
    _ ≤ 1 + 2 * (Real.pi / 2 / τ) := by linarith
    _ = 1 + Real.pi / τ := by ring

/-! ### `d`-dimensional sums -/

/-- The factorised lower bound: `1 + t^2 λ/(4d) ≥ 1 + (τ |m_i|)^2` with `τ = t/(dn)`. -/
theorem one_add_lam_ge (hd : 1 ≤ d) {t : ℝ} (m : Torus d n) (i : Fin d) :
    1 + (t / (d * n) * zabs (co m i)) ^ 2 ≤ 1 + t ^ 2 * lam m / (4 * d) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (NeZero.pos n)
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 := lam_ge m
  have h2 : (zabs (co m i) : ℝ) ^ 2 ≤ ∑ i, (zabs (co m i) : ℝ) ^ 2 :=
    single_le_sum (f := fun i => (zabs (co m i) : ℝ) ^ 2) (fun _ _ => by positivity) (mem_univ i)
  have h3 : (t / (d * n) * zabs (co m i)) ^ 2 ≤ t ^ 2 / (4 * d) * (16 / (n : ℝ) ^ 2 *
      ∑ i, (zabs (co m i) : ℝ) ^ 2) := by
    have e : (t / (d * n) * zabs (co m i)) ^ 2 = t ^ 2 / (4 * d) * (16 / (n : ℝ) ^ 2 *
        (zabs (co m i) : ℝ) ^ 2) * (1 / (4 * d)) := by
      field_simp; ring
    rw [e]
    have h4 : t ^ 2 / (4 * d) * (16 / (n : ℝ) ^ 2 * (zabs (co m i) : ℝ) ^ 2) ≤
        t ^ 2 / (4 * d) * (16 / (n : ℝ) ^ 2 * ∑ i, (zabs (co m i) : ℝ) ^ 2) := by
      gcongr
    have h5 : 1 / (4 * (d : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have h6 : 0 ≤ t ^ 2 / (4 * d) * (16 / (n : ℝ) ^ 2 * (zabs (co m i) : ℝ) ^ 2) := by positivity
    nlinarith
  have h7 : t ^ 2 / (4 * d) * (16 / (n : ℝ) ^ 2 * ∑ i, (zabs (co m i) : ℝ) ^ 2) ≤
      t ^ 2 * lam m / (4 * d) := by
    rw [mul_div_right_comm]; gcongr
  linarith

theorem inv_pow_le_prod (hd : 1 ≤ d) {t : ℝ} (m : Torus d n) :
    ((1 + t ^ 2 * lam m / (4 * d)) ^ d)⁻¹ ≤
      ∏ i, (1 + (t / (d * n) * zabs (co m i)) ^ 2)⁻¹ := by
  rw [prod_inv_distrib]
  refine inv_anti₀ (prod_pos fun i _ => by positivity) ?_
  calc ∏ i, (1 + (t / (d * n) * zabs (co m i)) ^ 2) ≤ ∏ _i : Fin d, (1 + t ^ 2 * lam m / (4 * d)) :=
        prod_le_prod (fun i _ => by positivity) fun i _ => one_add_lam_ge hd m i
    _ = _ := by rw [prod_const, card_univ, Fintype.card_fin]

theorem sum_prod_eq (f : ZMod n → ℝ) :
    ∑ m : Torus d n, ∏ i, f (co m i) = (∑ z : ZMod n, f z) ^ d := by
  rw [← Fin.prod_const, Finset.prod_univ_sum (fun _ => (univ : Finset (ZMod n))) (fun _ z => f z),
    Fintype.piFinset_univ]
  rfl

/-- `|Λ|^{-1} ∑_k (1 + t^2 λ(k)/(4d))^{-d} ≤ (1 + π d)^d t^{-d}` for `1 ≤ t ≤ n`. -/
theorem latt_small (hd : 1 ≤ d) {t : ℝ} (ht : 1 ≤ t) (htn : t ≤ n) :
    ((n : ℝ) ^ d)⁻¹ * ∑ m : Torus d n, ((1 + t ^ 2 * lam m / (4 * d)) ^ d)⁻¹ ≤
      (1 + Real.pi * d) ^ d / t ^ d := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (NeZero.pos n)
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have ht0 : 0 < t := by linarith
  set τ := t / (d * n) with hτ
  have hτ0 : 0 < τ := by positivity
  have h1 : ∑ m : Torus d n, ((1 + t ^ 2 * lam m / (4 * d)) ^ d)⁻¹ ≤
      (∑ z : ZMod n, (1 + (τ * zabs z) ^ 2)⁻¹) ^ d := by
    rw [← sum_prod_eq (fun z => (1 + (τ * zabs z) ^ 2)⁻¹)]
    exact sum_le_sum fun m _ => inv_pow_le_prod hd m
  have h2 : ∑ z : ZMod n, (1 + (τ * zabs z) ^ 2)⁻¹ ≤ (1 + Real.pi * d) * (n / t) := by
    refine (sum_zmod_le hτ0).trans ?_
    have e : Real.pi / τ = Real.pi * d * (n / t) := by rw [hτ]; field_simp
    rw [e]
    have : 1 ≤ (n : ℝ) / t := by rw [le_div_iff₀ ht0]; linarith
    nlinarith [Real.pi_pos]
  have h3 : (∑ z : ZMod n, (1 + (τ * zabs z) ^ 2)⁻¹) ^ d ≤ ((1 + Real.pi * d) * (n / t)) ^ d :=
    pow_le_pow_left₀ (sum_nonneg fun _ _ => by positivity) h2 d
  calc ((n : ℝ) ^ d)⁻¹ * ∑ m : Torus d n, ((1 + t ^ 2 * lam m / (4 * d)) ^ d)⁻¹
      ≤ ((n : ℝ) ^ d)⁻¹ * ((1 + Real.pi * d) * (n / t)) ^ d := by
        gcongr; exact h1.trans h3
    _ = (1 + Real.pi * d) ^ d / t ^ d := by
        rw [mul_pow, div_pow]; field_simp

/-- For `t ≥ n`, without the zero mode:
`|Λ|^{-1} ∑_{k ≠ 0} (1 + t^2 λ(k)/(4d))^{-d} ≤ ((d+4)/4)^d (1 + π d)^d t^{-d}`. -/
theorem latt_large (hd : 1 ≤ d) {t : ℝ} (htn : (n : ℝ) ≤ t) :
    ((n : ℝ) ^ d)⁻¹ * ∑ m ∈ univ.erase (0 : Torus d n), ((1 + t ^ 2 * lam m / (4 * d)) ^ d)⁻¹ ≤
      ((d + 4) / 4 : ℝ) ^ d * (1 + Real.pi * d) ^ d / t ^ d := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (NeZero.pos n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast NeZero.one_le
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have ht0 : 0 < t := by linarith
  set θ := (t / n) ^ 2 with hθ
  have hθ1 : 1 ≤ θ := by
    rw [hθ]; exact one_le_pow₀ (by rw [le_div_iff₀ hn]; linarith)
  set c : ℝ := 4 / (d + 4)
  have hc : 0 < c := by positivity
  have key : ∀ m ∈ univ.erase (0 : Torus d n), ((1 + t ^ 2 * lam m / (4 * d)) ^ d)⁻¹ ≤
      ((θ * c) ^ d)⁻¹ * ((1 + (n : ℝ) ^ 2 * lam m / (4 * d)) ^ d)⁻¹ := by
    intro m hm
    have hm0 : m ≠ 0 := (mem_erase.1 hm).1
    have hl := lam_ge m
    have hs := one_le_sum_zabs_sq hm0
    set X := (n : ℝ) ^ 2 * lam m / (4 * d)
    have hX : 4 / d ≤ X := by
      have : 16 / (n : ℝ) ^ 2 ≤ lam m := by
        calc 16 / (n : ℝ) ^ 2 = 16 / (n : ℝ) ^ 2 * 1 := by ring
          _ ≤ 16 / (n : ℝ) ^ 2 * ∑ i, (zabs (co m i) : ℝ) ^ 2 := by gcongr
          _ ≤ lam m := hl
      simp only [X]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h16 : 16 ≤ (n : ℝ) ^ 2 * lam m := by
        rw [div_le_iff₀ (by positivity)] at this; linarith
      nlinarith
    have hX0 : 0 ≤ X := by have := lam_nonneg m; positivity
    have h1 : c * (1 + X) ≤ X := by
      simp only [c]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ (by positivity)] at hX
      nlinarith
    have h2 : θ * c * (1 + X) ≤ 1 + t ^ 2 * lam m / (4 * d) := by
      have e : t ^ 2 * lam m / (4 * d) = θ * X := by
        simp only [θ, X]; field_simp
      rw [e, mul_assoc]
      nlinarith
    rw [← mul_inv, ← mul_pow]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) h2 d)
  have hsmall := latt_small (d := d) (n := n) hd hn1 le_rfl
  calc ((n : ℝ) ^ d)⁻¹ * ∑ m ∈ univ.erase (0 : Torus d n), ((1 + t ^ 2 * lam m / (4 * d)) ^ d)⁻¹
      ≤ ((n : ℝ) ^ d)⁻¹ * ∑ m ∈ univ.erase (0 : Torus d n),
          ((θ * c) ^ d)⁻¹ * ((1 + (n : ℝ) ^ 2 * lam m / (4 * d)) ^ d)⁻¹ := by
        gcongr with m hm; exact key m hm
    _ ≤ ((n : ℝ) ^ d)⁻¹ * ∑ m : Torus d n,
          ((θ * c) ^ d)⁻¹ * ((1 + (n : ℝ) ^ 2 * lam m / (4 * d)) ^ d)⁻¹ := by
        gcongr
        · intro i _ _
          have := lam_nonneg i
          positivity
        · exact erase_subset _ _
    _ = ((θ * c) ^ d)⁻¹ * (((n : ℝ) ^ d)⁻¹ *
          ∑ m : Torus d n, ((1 + (n : ℝ) ^ 2 * lam m / (4 * d)) ^ d)⁻¹) := by
        rw [← mul_sum]; ring
    _ ≤ ((θ * c) ^ d)⁻¹ * ((1 + Real.pi * d) ^ d / (n : ℝ) ^ d) := by gcongr
    _ = ((d + 4) / 4 : ℝ) ^ d * (1 + Real.pi * d) ^ d * ((θ * (n : ℝ)) ^ d)⁻¹ := by
        simp only [c]; rw [mul_pow, mul_pow, div_pow, div_pow]; field_simp
    _ ≤ ((d + 4) / 4 : ℝ) ^ d * (1 + Real.pi * d) ^ d * (t ^ d)⁻¹ := by
        gcongr
        simp only [θ]
        have e : (t / n) ^ 2 * (n : ℝ) = t * (t / n) := by field_simp
        rw [e]
        have : 1 ≤ t / n := by rw [le_div_iff₀ hn]; linarith
        nlinarith
    _ = _ := by ring

end

end FRD
