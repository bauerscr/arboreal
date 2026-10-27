import DressedFRD.Norm

/-!
# Lattice sums on the dual torus

`pnorm m = |p|_σ = max_i |e^{ip_i} - 1| = max_i 2 sin(π |m_i| / n)`.
* `pnorm_ge`, `pnorm_le`: `4 |m|_∞ / n ≤ |p|_σ ≤ 2π |m|_∞ / n`.
* `norm_sigma_le_pnorm`: `|σ_α| ≤ |p|_σ^{|α|}`.
* `card_pnorm_le`: `#{|p|_σ ≤ r} ≤ (n r/2 + 1)^d`.
* `sum_supNorm_rpow_tail`: `∑_{|m|_∞ ≥ K} |m|_∞^{-b} ≤ 5^d (1 - 2^{d-b})^{-1} K^{d-b}` for `b > d`.
-/

namespace DressedFRD

noncomputable section

open Finset Complex FRD Grassmann ComplexConjugate

variable {d n : ℕ} [NeZero n]

/-- `|p|_σ = max_i |e^{ip_i} - 1|`. -/
def pnorm (m : Torus d n) : ℝ := ((univ.sup fun i : Fin d => ‖char m (unitT i) - 1‖₊ : NNReal) : ℝ)

theorem pnorm_nonneg (m : Torus d n) : 0 ≤ pnorm m := NNReal.coe_nonneg _

theorem norm_char_unitT_le_pnorm (m : Torus d n) (i : Fin d) :
    ‖char m (unitT i) - 1‖ ≤ pnorm m := by
  have : ‖char m (unitT i) - 1‖₊ ≤ univ.sup fun i : Fin d => ‖char m (unitT i) - 1‖₊ :=
    Finset.le_sup (f := fun i : Fin d => ‖char m (unitT i) - 1‖₊) (mem_univ i)
  exact_mod_cast this

theorem exists_pnorm_eq (hd : 1 ≤ d) (m : Torus d n) :
    ∃ i : Fin d, pnorm m = ‖char m (unitT i) - 1‖ := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup (univ : Finset (Fin d)) ⟨⟨0, by omega⟩, mem_univ _⟩
    (fun i : Fin d => ‖char m (unitT i) - 1‖₊)
  exact ⟨i, by unfold pnorm; rw [hi]; rfl⟩

theorem two_zabs_le' (a : ZMod n) : 2 * zabs a ≤ n := by
  unfold zabs; have := ZMod.val_lt a; omega

theorem two_supNorm_le' (x : Torus d n) : 2 * supNorm x ≤ n := by
  have : supNorm x ≤ n / 2 := Finset.sup_le fun i _ => by
    have := two_zabs_le' ((x : Fin d → ZMod n) i); omega
  omega

/-- `|e^{2πia/n} - 1| = 2 sin(π|a|/n)`. -/
theorem norm_stdAddChar_sub_one (a : ZMod n) :
    ‖(ZMod.stdAddChar a : ℂ) - 1‖ = 2 * Real.sin (Real.pi * zabs a / n) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hsq := norm_stdAddChar_sub_one_sq a
  have hv := ZMod.val_lt a
  -- `sin(π v/n) = sin(π |a|/n)`
  have hsin : Real.sin (Real.pi * a.val / n) = Real.sin (Real.pi * zabs a / n) := by
    unfold zabs
    rcases le_total a.val (n - a.val) with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h, Nat.cast_sub hv.le]
      rw [show Real.pi * ((n : ℝ) - a.val) / n = Real.pi - Real.pi * a.val / n by field_simp]
      rw [Real.sin_pi_sub]
  have hz : (zabs a : ℝ) ≤ n / 2 := by
    have := two_zabs_le' a
    have : (2 * zabs a : ℝ) ≤ n := by exact_mod_cast this
    linarith
  have hs0 : 0 ≤ Real.sin (Real.pi * zabs a / n) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · positivity
    · rw [div_le_iff₀ hn]; nlinarith [Real.pi_pos]
  have hcos : 2 - 2 * Real.cos (2 * Real.pi * a.val / n) =
      (2 * Real.sin (Real.pi * a.val / n)) ^ 2 := by
    rw [show 2 * Real.pi * a.val / n = 2 * (Real.pi * a.val / n) by ring, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * a.val / n)]
  rw [hcos, hsin] at hsq
  have := (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 hsq
  exact this

/-- `|e^{2πia/n} - 1| ≥ 4|a|/n`. -/
theorem norm_stdAddChar_sub_one_ge (a : ZMod n) :
    4 * (zabs a : ℝ) / n ≤ ‖(ZMod.stdAddChar a : ℂ) - 1‖ := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  rw [norm_stdAddChar_sub_one]
  have hz : (2 * zabs a : ℝ) ≤ n := by exact_mod_cast two_zabs_le' a
  have h1 : 0 ≤ Real.pi * zabs a / n := by positivity
  have h2 : Real.pi * zabs a / n ≤ Real.pi / 2 := by
    rw [div_le_iff₀ hn]; nlinarith [Real.pi_pos]
  have := Real.mul_le_sin h1 h2
  have e : 2 / Real.pi * (Real.pi * zabs a / n) = 2 * zabs a / n := by
    field_simp
  rw [e] at this
  have : 4 * (zabs a : ℝ) / n = 2 * (2 * zabs a / n) := by ring
  linarith

/-- `|e^{2πia/n} - 1| ≤ 2π|a|/n`. -/
theorem norm_stdAddChar_sub_one_le (a : ZMod n) :
    ‖(ZMod.stdAddChar a : ℂ) - 1‖ ≤ 2 * Real.pi * zabs a / n := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  rw [norm_stdAddChar_sub_one]
  have := Real.sin_le (show 0 ≤ Real.pi * zabs a / n by positivity)
  have e : 2 * (Real.pi * zabs a / n) = 2 * Real.pi * zabs a / n := by ring
  linarith

theorem zabs_le_supNorm (m : Torus d n) (i : Fin d) : zabs (co m i) ≤ supNorm m :=
  Finset.le_sup (f := fun i => zabs ((m : Fin d → ZMod n) i)) (mem_univ i)

theorem exists_supNorm_eq (hd : 1 ≤ d) (m : Torus d n) : ∃ i : Fin d, supNorm m = zabs (co m i) := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup (univ : Finset (Fin d)) ⟨⟨0, by omega⟩, mem_univ _⟩
    (fun i => zabs ((m : Fin d → ZMod n) i))
  exact ⟨i, hi⟩

/-- `|p|_σ ≥ 4 |m|_∞ / n`. -/
theorem pnorm_ge (hd : 1 ≤ d) (m : Torus d n) : 4 * (supNorm m : ℝ) / n ≤ pnorm m := by
  obtain ⟨i, hi⟩ := exists_supNorm_eq hd m
  rw [hi]
  refine le_trans ?_ (norm_char_unitT_le_pnorm m i)
  rw [char_unitT]; exact norm_stdAddChar_sub_one_ge _

/-- `|p|_σ ≤ 2π |m|_∞ / n`. -/
theorem pnorm_le (hd : 1 ≤ d) (m : Torus d n) : pnorm m ≤ 2 * Real.pi * supNorm m / n := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  obtain ⟨i, hi⟩ := exists_pnorm_eq hd m
  rw [hi, char_unitT]
  refine (norm_stdAddChar_sub_one_le _).trans ?_
  have : (zabs (co m i) : ℝ) ≤ supNorm m := by exact_mod_cast zabs_le_supNorm m i
  rw [div_le_div_iff_of_pos_right hn]; nlinarith [Real.pi_pos]

/-- `|σ_α(p)| ≤ |p|_σ^{|α|}`. -/
theorem norm_sigma_le_pnorm (α : Dir d → ℕ) (m : Torus d n) :
    ‖sigma α m‖ ≤ pnorm m ^ Grassmann.mabs α := by
  unfold sigma Grassmann.mabs
  rw [norm_prod, ← prod_pow_eq_pow_sum]
  refine prod_le_prod (fun e _ => by positivity) fun e _ => ?_
  rw [norm_pow]
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
  rcases e with i | i
  · rw [dirVec_inl]; exact norm_char_unitT_le_pnorm m i
  · rw [dirVec_inr, char_neg_right, show conj (char m (unitT i)) - 1 = conj (char m (unitT i) - 1) by
      simp, Complex.norm_conj]
    exact norm_char_unitT_le_pnorm m i

/-- `#{m : |p|_σ ≤ r} ≤ (n r / 2 + 1)^d`. -/
theorem card_pnorm_le (hd : 1 ≤ d) {r : ℝ} (hr : 0 ≤ r) :
    ((univ.filter fun m : Torus d n => pnorm m ≤ r).card : ℝ) ≤ (n * r / 2 + 1) ^ d := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  set K := ⌊(n : ℝ) * r / 4⌋₊
  have hsub : (univ.filter fun m : Torus d n => pnorm m ≤ r) ⊆
      univ.filter fun m : Torus d n => supNorm m ≤ K := by
    intro m hm
    simp only [mem_filter, mem_univ, true_and] at hm ⊢
    have h1 := pnorm_ge hd m
    have h2 : (supNorm m : ℝ) ≤ n * r / 4 := by
      rw [div_le_iff₀ hn] at h1
      nlinarith
    exact Nat.le_floor h2
  calc ((univ.filter fun m : Torus d n => pnorm m ≤ r).card : ℝ)
      ≤ ((univ.filter fun m : Torus d n => supNorm m ≤ K).card : ℝ) := by
        exact_mod_cast card_le_card hsub
    _ ≤ ((2 * K + 1) ^ d : ℕ) := by exact_mod_cast card_supNorm_le K
    _ ≤ (n * r / 2 + 1) ^ d := by
        push_cast
        refine pow_le_pow_left₀ (by positivity) ?_ d
        have := Nat.floor_le (show 0 ≤ (n : ℝ) * r / 4 by positivity)
        linarith

/-- The dyadic tail sum: `∑_{|m|_∞ ≥ K} |m|_∞^{-b} ≤ 5^d (1 - 2^{d-b})^{-1} K^{d-b}`. -/
theorem sum_supNorm_rpow_tail {b : ℝ} (hb : (d : ℝ) < b) {K : ℕ} (hK : 1 ≤ K) :
    ∑ m ∈ univ.filter (fun m : Torus d n => K ≤ supNorm m), ((supNorm m : ℝ) ^ (-b)) ≤
      5 ^ d * (1 - (2 : ℝ) ^ ((d : ℝ) - b))⁻¹ * (K : ℝ) ^ ((d : ℝ) - b) := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  set S := univ.filter (fun m : Torus d n => K ≤ supNorm m)
  have hq : (2 : ℝ) ^ ((d : ℝ) - b) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hq0 : 0 ≤ (2 : ℝ) ^ ((d : ℝ) - b) := by positivity
  -- each `m` lies in the dyadic shell `K 2^i ≤ |m|_∞ < K 2^{i+1}`, `i = log₂(|m|_∞/K)`
  have hshell : ∀ m ∈ S, K * 2 ^ Nat.log 2 (supNorm m / K) ≤ supNorm m ∧
      supNorm m < K * 2 ^ (Nat.log 2 (supNorm m / K) + 1) := by
    intro m hm
    rw [mem_filter] at hm
    have hpos : supNorm m / K ≠ 0 := by
      have := Nat.div_pos hm.2 (by omega); omega
    constructor
    · have := Nat.pow_log_le_self 2 hpos
      calc K * 2 ^ Nat.log 2 (supNorm m / K) ≤ K * (supNorm m / K) := Nat.mul_le_mul_left K this
        _ ≤ supNorm m := Nat.mul_div_le _ _
    · have h1 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (supNorm m / K)
      have h2 := Nat.lt_mul_div_succ (supNorm m) (show 0 < K by omega)
      calc supNorm m < K * (supNorm m / K + 1) := h2
        _ ≤ K * 2 ^ (Nat.log 2 (supNorm m / K) + 1) := Nat.mul_le_mul_left K h1
  have hmaps : ∀ m ∈ S, Nat.log 2 (supNorm m / K) ∈ range (n + 1) := by
    intro m hm
    rw [mem_range]
    have h1 := (hshell m hm).1
    have h2 : 2 ^ Nat.log 2 (supNorm m / K) ≤ supNorm m :=
      le_trans (Nat.le_mul_of_pos_left _ (by omega)) h1
    have h3 : Nat.log 2 (supNorm m / K) < 2 ^ Nat.log 2 (supNorm m / K) := Nat.lt_two_pow_self
    have h4 := two_supNorm_le' m
    omega
  rw [← sum_fiberwise_of_maps_to hmaps]
  -- bound each shell
  have hshellsum : ∀ i ∈ range (n + 1),
      ∑ m ∈ S.filter (fun m => Nat.log 2 (supNorm m / K) = i), ((supNorm m : ℝ) ^ (-b)) ≤
        5 ^ d * (K : ℝ) ^ ((d : ℝ) - b) * ((2 : ℝ) ^ ((d : ℝ) - b)) ^ i := by
    intro i _
    set T := S.filter (fun m => Nat.log 2 (supNorm m / K) = i)
    have hT : T ⊆ univ.filter fun m : Torus d n => supNorm m ≤ K * 2 ^ (i + 1) := by
      intro m hm
      rw [mem_filter] at hm
      have := (hshell m hm.1).2
      rw [hm.2] at this
      simp only [mem_filter, mem_univ, true_and]; omega
    have hKi : (1 : ℝ) ≤ K * 2 ^ i := by
      have : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
      have : (1 : ℝ) ≤ K := by exact_mod_cast hK
      nlinarith
    have hterm : ∀ m ∈ T, (supNorm m : ℝ) ^ (-b) ≤ ((K : ℝ) * 2 ^ i) ^ (-b) := by
      intro m hm
      rw [mem_filter] at hm
      have := (hshell m hm.1).1
      rw [hm.2] at this
      have h' : (K : ℝ) * 2 ^ i ≤ supNorm m := by exact_mod_cast this
      exact Real.rpow_le_rpow_of_nonpos (by linarith) h' (by linarith)
    have hcard : (T.card : ℝ) ≤ (5 * ((K : ℝ) * 2 ^ i)) ^ d := by
      have h1 : (T.card : ℝ) ≤ ((2 * (K * 2 ^ (i + 1)) + 1) ^ d : ℕ) := by
        exact_mod_cast (card_le_card hT).trans (card_supNorm_le _)
      refine h1.trans ?_
      push_cast
      refine pow_le_pow_left₀ (by positivity) ?_ d
      rw [pow_succ]; nlinarith
    calc ∑ m ∈ T, (supNorm m : ℝ) ^ (-b) ≤ ∑ _m ∈ T, ((K : ℝ) * 2 ^ i) ^ (-b) :=
          sum_le_sum hterm
      _ = T.card * ((K : ℝ) * 2 ^ i) ^ (-b) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (5 * ((K : ℝ) * 2 ^ i)) ^ d * ((K : ℝ) * 2 ^ i) ^ (-b) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 5 ^ d * ((K : ℝ) * 2 ^ i) ^ ((d : ℝ) - b) := by
          rw [mul_pow, mul_assoc, ← Real.rpow_natCast ((K : ℝ) * 2 ^ i) d,
            ← Real.rpow_add (by positivity), sub_eq_add_neg]
      _ = 5 ^ d * (K : ℝ) ^ ((d : ℝ) - b) * ((2 : ℝ) ^ ((d : ℝ) - b)) ^ i := by
          rw [Real.mul_rpow (by positivity) (by positivity)]
          have e : ((2 : ℝ) ^ i) ^ ((d : ℝ) - b) = ((2 : ℝ) ^ ((d : ℝ) - b)) ^ i := by
            rw [← Real.rpow_natCast (2 : ℝ) i, ← Real.rpow_natCast ((2 : ℝ) ^ ((d : ℝ) - b)) i,
              ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), mul_comm]
          rw [e]; ring
  calc ∑ i ∈ range (n + 1), ∑ m ∈ S.filter (fun m => Nat.log 2 (supNorm m / K) = i),
        ((supNorm m : ℝ) ^ (-b))
      ≤ ∑ i ∈ range (n + 1), 5 ^ d * (K : ℝ) ^ ((d : ℝ) - b) * ((2 : ℝ) ^ ((d : ℝ) - b)) ^ i :=
        sum_le_sum hshellsum
    _ = 5 ^ d * (K : ℝ) ^ ((d : ℝ) - b) * ∑ i ∈ range (n + 1), ((2 : ℝ) ^ ((d : ℝ) - b)) ^ i := by
        rw [mul_sum]
    _ ≤ 5 ^ d * (K : ℝ) ^ ((d : ℝ) - b) * (1 - (2 : ℝ) ^ ((d : ℝ) - b))⁻¹ := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← tsum_geometric_of_lt_one hq0 hq]
        exact Summable.sum_le_tsum _ (fun i _ => pow_nonneg hq0 i)
          (summable_geometric_of_lt_one hq0 hq)
    _ = _ := by ring

end

end DressedFRD
