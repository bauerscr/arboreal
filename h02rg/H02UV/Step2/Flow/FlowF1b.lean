import Step2.Flow.FlowF1
import Step2.Flow.FlowF1Alg

/-!
# Auxiliary facts along regular histories for (F1)

* `g_mono`, `g_diff_le`: along a regular history `g` is nondecreasing and
  `g_j - g_k ≤ (j - k)(2β + 1) g_j²`;
* `stZ'_ratio`: `Z_{j+1} = Z_{k+1} ∏_{k<i≤j} (1 + ζ_i)`;
* `prod_sub_one_le`: `|∏ f_i - 1| ≤ |s| x M^{|s|}`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2

/-! ### Regular histories -/

section Reg

variable {X : ℕ → Type*} [∀ j, NormedAddCommGroup (X j)] {Λ β δ κ cg cm cT ε : ℝ}

/-- One regular step: `g ≤ g' ≤ g + (2β+1) g²`. -/
theorem reg_step {g g' : ℝ} (hg : 0 < g) (hgε : g ≤ ε) (hβ : 0 ≤ β) (hδ1 : δ ≤ 1 / 2)
    (hcg : 0 ≤ cg) (hcgβ : cg * ε ≤ β / 2) (hcg1 : cg * ε ≤ 1)
    (h : |g' - g - β * g ^ 2| ≤ δ * β * g ^ 2 + cg * g ^ 3) :
    g ≤ g' ∧ g' - g ≤ (2 * β + 1) * g ^ 2 := by
  have hr := abs_le.1 h
  have h3 : cg * g ^ 3 ≤ cg * ε * g ^ 2 := by
    have : g ^ 3 ≤ ε * g ^ 2 := by
      rw [pow_succ]; nlinarith [sq_nonneg g, mul_le_mul_of_nonneg_left hgε (sq_nonneg g)]
    nlinarith
  have hg2 : 0 ≤ g ^ 2 := sq_nonneg g
  have hδ0 : δ * β * g ^ 2 ≤ β / 2 * g ^ 2 := by
    have : δ * β ≤ β / 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right this hg2
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right hcgβ hg2]
  · nlinarith [mul_le_mul_of_nonneg_right hcg1 hg2]

theorem g_mono {j : ℕ} {t : Hist.Seq X} (ht : Hist.InDh Λ β δ κ cg cm cT ε j t) (hβ : 0 ≤ β)
    (hδ1 : δ ≤ 1 / 2) (hcg : 0 ≤ cg) (hcgβ : cg * ε ≤ β / 2) (hcg1 : cg * ε ≤ 1) (k : ℕ) :
    ∀ m, k + m ≤ j → (t k).1 ≤ (t (k + m)).1 ∧
      (t (k + m)).1 - (t k).1 ≤ m * (2 * β + 1) * (t (k + m)).1 ^ 2
  | 0, _ => by simp
  | m + 1, hm => by
    have ih := g_mono ht hβ hδ1 hcg hcgβ hcg1 k m (by omega)
    obtain ⟨hg, hgε, -, -⟩ := ht.1 (k + m) (by omega)
    obtain ⟨hs1, hs2⟩ := reg_step hg hgε hβ hδ1 hcg hcgβ hcg1 (ht.2 (k + m) (by omega))
    rw [← add_assoc]
    refine ⟨ih.1.trans hs1, ?_⟩
    have hsq : (t (k + m)).1 ^ 2 ≤ (t (k + m + 1)).1 ^ 2 := pow_le_pow_left₀ hg.le hs1 2
    have hc : (0 : ℝ) ≤ 2 * β + 1 := by linarith
    have h1 := mul_le_mul_of_nonneg_left hsq (mul_nonneg (Nat.cast_nonneg (α := ℝ) m) hc)
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hsq hc]

end Reg

/-! ### Products -/

theorem prod_sub_one_le {ι : Type*} (s : Finset ι) (f : ι → ℂ) {x M : ℝ} (hM : 1 ≤ M)
    (hx : ∀ i ∈ s, ‖f i - 1‖ ≤ x) (hfM : ∀ i ∈ s, ‖f i‖ ≤ M) :
    ‖∏ i ∈ s, f i - 1‖ ≤ s.card * x * M ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, card_insert_of_notMem ha]
    have ih' := ih (fun i hi => hx i (mem_insert_of_mem hi)) (fun i hi => hfM i (mem_insert_of_mem hi))
    have hxa := hx a (mem_insert_self a s)
    have hfa := hfM a (mem_insert_self a s)
    have hx0 : 0 ≤ x := (norm_nonneg _).trans hxa
    have e : f a * ∏ i ∈ s, f i - 1 = f a * (∏ i ∈ s, f i - 1) + (f a - 1) := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    have hMs : 1 ≤ M ^ s.card := one_le_pow₀ hM
    have h1 : ‖f a‖ * ‖∏ i ∈ s, f i - 1‖ ≤ M * (s.card * x * M ^ s.card) :=
      mul_le_mul hfa ih' (norm_nonneg _) (by linarith)
    push_cast
    have : x ≤ x * M ^ (s.card + 1) := le_mul_of_one_le_right hx0 (one_le_pow₀ hM)
    have e2 : M * (s.card * x * M ^ s.card) = s.card * x * M ^ (s.card + 1) := by ring
    nlinarith

/-! ### The past couplings -/

theorem pow4_sub_one_le {ζ : ℂ} (h : ‖ζ‖ ≤ 1 / 8) :
    ‖((1 + ζ) ^ 4)⁻¹ - 1‖ ≤ 12 * ‖ζ‖ ∧ ‖((1 + ζ) ^ 4)⁻¹‖ ≤ 2 := by
  have h1 : 7 / 8 ≤ ‖1 + ζ‖ := by
    have := norm_sub_le (1 + ζ) ζ
    simp only [add_sub_cancel_right, norm_one] at this
    linarith
  have h9 : ‖1 + ζ‖ ≤ 9 / 8 := by
    refine (norm_add_le _ _).trans ?_; rw [norm_one]; linarith
  have h4 : (7 / 8) ^ 4 ≤ ‖1 + ζ‖ ^ 4 := pow_le_pow_left₀ (by norm_num) h1 4
  have h0 : (1 + ζ) ^ 4 ≠ 0 := pow_ne_zero 4 (by
    intro h; rw [h, norm_zero] at h1; norm_num at h1)
  have hinv : ‖((1 + ζ) ^ 4)⁻¹‖ ≤ 2 := by
    rw [norm_inv, norm_pow]
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    nlinarith
  refine ⟨?_, hinv⟩
  have e : ((1 + ζ) ^ 4)⁻¹ - 1 = -(ζ * (4 + 6 * ζ + 4 * ζ ^ 2 + ζ ^ 3)) * ((1 + ζ) ^ 4)⁻¹ := by
    rw [show -(ζ * (4 + 6 * ζ + 4 * ζ ^ 2 + ζ ^ 3)) = 1 - (1 + ζ) ^ 4 by ring, sub_mul, one_mul,
      mul_inv_cancel₀ h0]
  rw [e, norm_mul, norm_neg, norm_mul]
  have hp : ‖4 + 6 * ζ + 4 * ζ ^ 2 + ζ ^ 3‖ ≤ 6 := by
    have hz0 := norm_nonneg ζ
    have := norm_add_le (4 + 6 * ζ + 4 * ζ ^ 2) (ζ ^ 3)
    have := norm_add_le (4 + 6 * ζ) (4 * ζ ^ 2)
    have := norm_add_le (4 : ℂ) (6 * ζ)
    simp only [norm_mul, norm_pow, Complex.norm_ofNat] at *
    have : ‖ζ‖ ^ 2 ≤ 1 / 64 := by nlinarith
    have : ‖ζ‖ ^ 3 ≤ 1 / 512 := by nlinarith
    linarith
  calc ‖ζ‖ * ‖4 + 6 * ζ + 4 * ζ ^ 2 + ζ ^ 3‖ * ‖((1 + ζ) ^ 4)⁻¹‖ ≤ ‖ζ‖ * 6 * 2 := by
        gcongr
    _ = 12 * ‖ζ‖ := by ring

set_option maxHeartbeats 2000000 in
/-- **The past couplings**: `|g_{r,k}² (Z_{k+1}/Z_{j+1})⁴ - g_j²| ≤ c (j-k+1) 2^{j-k} g_j³`. -/
theorem past_coef_le {j k : ℕ} (hkj : k ≤ j) {g gk β cZ cn : ℝ} {grk nk zk zj : ℂ}
    (ζ : ℕ → ℂ) (hg : 0 ≤ g) (hg1 : g ≤ 1) (hgk : 0 ≤ gk) (hgkg : gk ≤ g)
    (hdiff : g - gk ≤ (j - k) * (2 * β + 1) * g ^ 2) (hβ : 0 ≤ β) (hcZ : 0 ≤ cZ) (hcn : 0 ≤ cn)
    (hgr : grk = gk / (1 + nk)) (hn : ‖nk‖ ≤ cn * g) (hn8 : ‖nk‖ ≤ 1 / 8)
    (hzk : zk ≠ 0) (hz : zj = zk * ∏ i ∈ Ioc k j, (1 + ζ i))
    (hζ : ∀ i ∈ Ioc k j, ‖ζ i‖ ≤ cZ * g) (hζ8 : ∀ i ∈ Ioc k j, ‖ζ i‖ ≤ 1 / 8) :
    ‖grk ^ 2 * (zk / zj) ^ 4 - (g : ℂ) ^ 2‖ ≤
      (j - k + 1) * 2 ^ (j - k) * (24 * cZ + 3 * cn + 2 * (2 * β + 1)) * g ^ 3 := by
  set m := j - k with hm
  have hcard : (Ioc k j).card = m := by simp [hm]
  -- the ratio
  have hP0 : ∏ i ∈ Ioc k j, (1 + ζ i) ≠ 0 := prod_ne_zero_iff.2 fun i hi => by
    intro h; have h8 := hζ8 i hi; have h2 := norm_sub_le (1 + ζ i) (ζ i)
    simp only [add_sub_cancel_right, norm_one] at h2
    rw [h, norm_zero] at h2; linarith
  have hr : (zk / zj) ^ 4 = ∏ i ∈ Ioc k j, ((1 + ζ i) ^ 4)⁻¹ := by
    rw [hz, prod_inv_distrib, prod_pow]; field_simp
  have hr1 : ‖(zk / zj) ^ 4 - 1‖ ≤ m * (12 * (cZ * g)) * 2 ^ m := by
    rw [hr, ← hcard]
    exact prod_sub_one_le _ _ (by norm_num)
      (fun i hi => (pow4_sub_one_le (hζ8 i hi)).1.trans (by have := hζ i hi; linarith))
      (fun i hi => (pow4_sub_one_le (hζ8 i hi)).2)
  have hr2 : ‖(zk / zj) ^ 4‖ ≤ 2 ^ m := by
    rw [hr, norm_prod, ← hcard]
    calc ∏ i ∈ Ioc k j, ‖((1 + ζ i) ^ 4)⁻¹‖ ≤ ∏ i ∈ Ioc k j, (2 : ℝ) :=
          prod_le_prod (fun _ _ => norm_nonneg _) fun i hi => (pow4_sub_one_le (hζ8 i hi)).2
      _ = 2 ^ (Ioc k j).card := by rw [prod_const]
  -- the coupling
  have h1n : 7 / 8 ≤ ‖1 + nk‖ := by
    have := norm_sub_le (1 + nk) nk
    simp only [add_sub_cancel_right, norm_one] at this
    linarith
  have h1n0 : 1 + nk ≠ 0 := by intro h; rw [h, norm_zero] at h1n; norm_num at h1n
  have hgr2 : ‖grk ^ 2 - (gk : ℂ) ^ 2‖ ≤ 3 * cn * g ^ 3 := by
    have e : grk ^ 2 - (gk : ℂ) ^ 2 = -((gk : ℂ) ^ 2 * (nk * (2 + nk)) / (1 + nk) ^ 2) := by
      rw [hgr]; field_simp; ring
    rw [e, norm_neg, norm_div, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hgk]
    have h2 : ‖2 + nk‖ ≤ 17 / 8 := by
      refine (norm_add_le _ _).trans ?_; simp only [Complex.norm_ofNat]; linarith
    have h3 : (49 / 64 : ℝ) ≤ ‖1 + nk‖ ^ 2 := by nlinarith
    rw [div_le_iff₀ (by linarith)]
    have hgk2 : gk ^ 2 ≤ g ^ 2 := pow_le_pow_left₀ hgk hgkg 2
    have : ‖nk‖ * ‖2 + nk‖ ≤ cn * g * (17 / 8) := mul_le_mul hn h2 (norm_nonneg _) (by positivity)
    have hA : gk ^ 2 * (‖nk‖ * ‖2 + nk‖) ≤ g ^ 2 * (cn * g * (17 / 8)) :=
      mul_le_mul hgk2 this (by positivity) (by positivity)
    have hB : 3 * cn * g ^ 3 * (49 / 64) ≤ 3 * cn * g ^ 3 * ‖1 + nk‖ ^ 2 :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have : 0 ≤ cn * g ^ 3 := by positivity
    nlinarith
  have hgg : ‖(gk : ℂ) ^ 2 - (g : ℂ) ^ 2‖ ≤ 2 * m * (2 * β + 1) * g ^ 3 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_sub_comm]
    have e : g ^ 2 - gk ^ 2 = (g - gk) * (g + gk) := by ring
    rw [e, abs_of_nonneg (mul_nonneg (by linarith) (by linarith))]
    have hm' : ((j : ℝ) - k) = m := by rw [hm]; push_cast [Nat.cast_sub hkj]; ring
    rw [hm'] at hdiff
    have : g + gk ≤ 2 * g := by linarith
    calc (g - gk) * (g + gk) ≤ (m * (2 * β + 1) * g ^ 2) * (2 * g) :=
          mul_le_mul hdiff this (by linarith) (by positivity)
      _ = _ := by ring
  -- combine
  have e : grk ^ 2 * (zk / zj) ^ 4 - (g : ℂ) ^ 2 =
      grk ^ 2 * ((zk / zj) ^ 4 - 1) + (grk ^ 2 - (gk : ℂ) ^ 2) + ((gk : ℂ) ^ 2 - (g : ℂ) ^ 2) := by
    ring
  rw [e]
  have hgrn : ‖grk‖ ^ 2 ≤ 2 * g ^ 2 := by
    have : ‖grk‖ ≤ 8 / 7 * g := by
      rw [hgr, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hgk,
        div_le_iff₀ (by linarith)]
      nlinarith
    have h0 := norm_nonneg grk
    nlinarith
  have t1 : ‖grk ^ 2 * ((zk / zj) ^ 4 - 1)‖ ≤ 2 * g ^ 2 * (m * (12 * (cZ * g)) * 2 ^ m) := by
    rw [norm_mul, norm_pow]; exact mul_le_mul hgrn hr1 (norm_nonneg _) (by positivity)
  have hm1 : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  have hj : ((j : ℝ) - k + 1) = m + 1 := by rw [hm]; push_cast [Nat.cast_sub hkj]; ring
  rw [hj]
  have hsum := (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add t1 hgr2)) hgg)
  refine hsum.trans ?_
  have hg3 : 0 ≤ g ^ 3 := by positivity
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have a1 : 2 * g ^ 2 * (m * (12 * (cZ * g)) * 2 ^ m) ≤ (m + 1) * 2 ^ m * (24 * cZ) * g ^ 3 := by
    have : 2 * g ^ 2 * (m * (12 * (cZ * g)) * 2 ^ m) = m * 2 ^ m * (24 * cZ) * g ^ 3 := by ring
    rw [this]
    have : (0 : ℝ) ≤ 2 ^ m * (24 * cZ) * g ^ 3 := by positivity
    nlinarith
  have a2 : 3 * cn * g ^ 3 ≤ (m + 1) * 2 ^ m * (3 * cn) * g ^ 3 := by
    have : (1 : ℝ) ≤ (m + 1) * 2 ^ m := by nlinarith
    have h0 : 0 ≤ 3 * cn * g ^ 3 := by positivity
    nlinarith
  have a3 : 2 * m * (2 * β + 1) * g ^ 3 ≤ (m + 1) * 2 ^ m * (2 * (2 * β + 1)) * g ^ 3 := by
    have : (m : ℝ) ≤ (m + 1) * 2 ^ m := by nlinarith
    have h0 : 0 ≤ 2 * (2 * β + 1) * g ^ 3 := by positivity
    nlinarith
  nlinarith

/-! ### The normalisation along a history -/

variable {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

theorem stZ'_succ (j : ℕ) (t : Hist.Seq (Xs R)) :
    stZ' R (rawHist R (j + 1) t) = stZ' R (rawHist R j t) * (1 + stZeta R (rawHist R (j + 1) t)) :=
  rfl

/-- `Z_{j+1} = Z_{k+1} ∏_{k<i≤j} (1 + ζ_i)`. -/
theorem stZ'_ratio (t : Hist.Seq (Xs R)) (k : ℕ) :
    ∀ j, k ≤ j → stZ' R (rawHist R j t) =
      stZ' R (rawHist R k t) * ∏ i ∈ Ioc k j, (1 + stZeta R (rawHist R i t))
  | j, hkj => by
    obtain ⟨m, rfl⟩ : ∃ m, j = k + m := ⟨j - k, by omega⟩
    induction m with
    | zero => simp
    | succ m ih =>
      have e : Ioc k (k + m + 1) = insert (k + m + 1) (Ioc k (k + m)) := by
        ext i; simp only [mem_Ioc, mem_insert]; omega
      rw [← add_assoc, stZ'_succ, ih (by omega), e, prod_insert (by simp), mul_assoc,
        mul_comm (1 + _) _]

end

end Step2
