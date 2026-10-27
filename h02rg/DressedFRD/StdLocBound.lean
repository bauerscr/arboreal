import DressedFRD.StdBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# `lem:std`(e): the localisation bound

`std_e`: under (S1)–(S5), `‖C_{≤j}(1 - ê_j)‖_{(j)} ≤ c₂` for all `j < N`, with
`c₂ = c_d L^d (1 + 5^d Q (π/2)^M / (1 - L^{2-M}))`, `c_d = 2^M (1+2M)^d c_S` and
`Q = (1 - 2^{d-(M-q)})^{-1}`. This is `StdLoc`.

The proof splits the momenta at `|p|_σ = r = L^{-j}`:
* small momenta, by `lem:std`(d) and `card_pnorm_le`;
* large momenta, by `C_{≤j}(1-ê_j) = ê_j C_{>j} ≤ C_{>j}`, (S5) and `sum_supNorm_rpow_tail`.
-/

namespace DressedFRD

noncomputable section

open Finset Complex FRD Grassmann ComplexConjugate

variable {d n : ℕ} [NeZero n]

variable {L N q M : ℕ} {msq cS : ℝ} {C : ℕ → Torus d n → ℝ}

/-- `∑_{|p|_σ > r} |p|_σ^{-b} ≤ n^d · 5^d (1 - 2^{d-b})^{-1} 4^{-b} (2π)^{b-d} r^{d-b}`. -/
theorem sum_pnorm_rpow_tail (hd : 1 ≤ d) {b : ℝ} (hb : (d : ℝ) < b) {r : ℝ} (hr : 0 < r)
    (hnr : 2 * Real.pi ≤ n * r) :
    ∑ m ∈ univ.filter (fun m : Torus d n => r < pnorm m), pnorm m ^ (-b) ≤
      (n : ℝ) ^ d * (5 ^ d * (1 - (2 : ℝ) ^ ((d : ℝ) - b))⁻¹ * (4 : ℝ) ^ (-b) *
        (2 * Real.pi) ^ (b - d) * r ^ ((d : ℝ) - b)) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  set K := ⌈(n : ℝ) * r / (2 * Real.pi)⌉₊
  have hK1 : 1 ≤ K := by
    apply Nat.one_le_iff_ne_zero.2
    intro h
    rw [Nat.ceil_eq_zero] at h
    have : 0 < (n : ℝ) * r / (2 * Real.pi) := by positivity
    linarith
  have hKr : (n : ℝ) * r / (2 * Real.pi) ≤ K := Nat.le_ceil _
  -- `|p|_σ > r` implies `|m|_∞ ≥ K`
  have hsub : ∀ m ∈ univ.filter (fun m : Torus d n => r < pnorm m), K ≤ supNorm m := by
    intro m hm
    simp only [mem_filter, mem_univ, true_and] at hm
    have h1 := pnorm_le hd m
    have h2 : (n : ℝ) * r / (2 * Real.pi) < supNorm m := by
      rw [div_lt_iff₀ (by positivity)]
      rw [le_div_iff₀ hn] at h1
      nlinarith
    exact Nat.ceil_le.2 h2.le
  have hterm : ∀ m ∈ univ.filter (fun m : Torus d n => r < pnorm m),
      pnorm m ^ (-b) ≤ ((n : ℝ) / 4) ^ b * (supNorm m : ℝ) ^ (-b) := by
    intro m hm
    simp only [mem_filter, mem_univ, true_and] at hm
    have hs : (0 : ℝ) < supNorm m := by
      have := hsub m (by simp [hm]); exact_mod_cast (show 0 < supNorm m by omega)
    have h1 := pnorm_ge hd m
    have h4 : 4 * (supNorm m : ℝ) / n ≤ pnorm m := h1
    calc pnorm m ^ (-b) ≤ (4 * (supNorm m : ℝ) / n) ^ (-b) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) h4 (by linarith)
      _ = ((n : ℝ) / 4) ^ b * (supNorm m : ℝ) ^ (-b) := by
          rw [show 4 * (supNorm m : ℝ) / n = (supNorm m : ℝ) / ((n : ℝ) / 4) by field_simp,
            Real.div_rpow hs.le (by positivity), Real.rpow_neg (by positivity : (0 : ℝ) ≤ n / 4),
            div_inv_eq_mul, mul_comm]
  have htail := sum_supNorm_rpow_tail (d := d) (n := n) hb hK1
  have hb0 : 0 < b := by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
  have hKpow : (K : ℝ) ^ ((d : ℝ) - b) ≤ ((n : ℝ) * r / (2 * Real.pi)) ^ ((d : ℝ) - b) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hKr (by linarith)
  have hq : 0 < 1 - (2 : ℝ) ^ ((d : ℝ) - b) := by
    have := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2) (by linarith : (d : ℝ) - b < 0)
    linarith
  calc ∑ m ∈ univ.filter (fun m : Torus d n => r < pnorm m), pnorm m ^ (-b)
      ≤ ∑ m ∈ univ.filter (fun m : Torus d n => K ≤ supNorm m), ((n : ℝ) / 4) ^ b * (supNorm m : ℝ) ^ (-b) :=
        (sum_le_sum hterm).trans (sum_le_sum_of_subset_of_nonneg
          (fun m hm => by simp only [mem_filter, mem_univ, true_and]; exact hsub m hm)
          fun m _ _ => by positivity)
    _ = ((n : ℝ) / 4) ^ b * ∑ m ∈ univ.filter (fun m : Torus d n => K ≤ supNorm m),
          (supNorm m : ℝ) ^ (-b) := by rw [mul_sum]
    _ ≤ ((n : ℝ) / 4) ^ b * (5 ^ d * (1 - (2 : ℝ) ^ ((d : ℝ) - b))⁻¹ *
          ((n : ℝ) * r / (2 * Real.pi)) ^ ((d : ℝ) - b)) := by
        refine mul_le_mul_of_nonneg_left (htail.trans ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left hKpow (by positivity)
    _ = _ := by
        rw [Real.div_rpow hn.le (by norm_num), Real.div_rpow (by positivity) (by positivity),
          Real.mul_rpow hn.le hr.le]
        have hnpow : (n : ℝ) ^ b * (n : ℝ) ^ ((d : ℝ) - b) = (n : ℝ) ^ d := by
          rw [← Real.rpow_add hn]; simp
        have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
        rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4), Real.rpow_sub hπ (d : ℝ) b,
          Real.rpow_sub hπ b (d : ℝ), ← hnpow]
        field_simp

theorem sum_range_pow_le {x : ℝ} (hx : 2 ≤ x) (j : ℕ) : ∑ k ∈ range j, x ^ k ≤ x ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [sum_range_succ, pow_succ]
    have : (0 : ℝ) ≤ x ^ j := pow_nonneg (by linarith) j
    nlinarith

/-- `∑_{k=j+1}^N L^{(k-1)(2-M)} ≤ L^{j(2-M)} / (1 - L^{2-M})`. -/
theorem sum_Ioc_geom_le {ℓ : ℝ} (hℓ : 1 < ℓ) {M : ℕ} (hM : 3 ≤ M) (j N : ℕ) :
    ∑ k ∈ Ioc j N, ℓ ^ ((((k - 1 : ℕ) : ℝ)) * (2 - (M : ℝ))) ≤
      ℓ ^ ((j : ℝ) * (2 - (M : ℝ))) * (1 - ℓ ^ (2 - (M : ℝ)))⁻¹ := by
  have hℓ0 : 0 < ℓ := by linarith
  set x := ℓ ^ (2 - (M : ℝ))
  have hx0 : 0 ≤ x := Real.rpow_nonneg hℓ0.le _
  have hx1 : x < 1 := Real.rpow_lt_one_of_one_lt_of_neg hℓ (by
    have : (3 : ℝ) ≤ M := by exact_mod_cast hM
    linarith)
  have hterm : ∀ k ∈ Ioc j N, ℓ ^ ((((k - 1 : ℕ) : ℝ)) * (2 - (M : ℝ))) =
      ℓ ^ ((j : ℝ) * (2 - (M : ℝ))) * x ^ (k - 1 - j) := by
    intro k hk
    rw [mem_Ioc] at hk
    simp only [x]
    rw [← Real.rpow_natCast (ℓ ^ (2 - (M : ℝ))), ← Real.rpow_mul hℓ0.le, ← Real.rpow_add hℓ0]
    congr 1
    rw [Nat.cast_sub (by omega : j ≤ k - 1), Nat.cast_sub (by omega : 1 ≤ k)]
    push_cast; ring
  rw [sum_congr rfl hterm, ← mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hℓ0.le _)
  rw [← tsum_geometric_of_lt_one hx0 hx1]
  calc ∑ k ∈ Ioc j N, x ^ (k - 1 - j) = ∑ i ∈ range (N - j), x ^ i := by
        refine sum_nbij' (fun k => k - 1 - j) (fun i => i + j + 1) ?_ ?_ ?_ ?_ ?_
        · intro k hk; simp only [mem_Ioc, mem_range] at hk ⊢; omega
        · intro i hi; simp only [mem_Ioc, mem_range] at hi ⊢; omega
        · intro k hk; simp only [mem_Ioc] at hk; omega
        · intro i _; omega
        · intro k _; rfl
    _ ≤ ∑' i, x ^ i := Summable.sum_le_tsum _ (fun i _ => pow_nonneg hx0 i)
        (summable_geometric_of_lt_one hx0 hx1)

/-- The constant `c₂` of `lem:std`(e). -/
def c2val (d L q M : ℕ) (cS : ℝ) : ℝ :=
  2 ^ M * (1 + 2 * M : ℝ) ^ d * cS * (L : ℝ) ^ d *
    (1 + 5 ^ d * (1 - (2 : ℝ) ^ ((d : ℝ) - ((M : ℝ) - q)))⁻¹ * (Real.pi / 2) ^ M *
      (1 - (L : ℝ) ^ (2 - (M : ℝ)))⁻¹)

/-- `lem:std`(e). -/
theorem std_e (h : StdFull L N q M msq cS C) (hd : 1 ≤ d) (hq : 2 ≤ q) (hL : 7 ≤ L)
    (hn : n = L ^ N) :
    StdLoc L N q msq (c2val d L q M cS) C := by
  intro j hjN
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  have hM := h.hM
  have hM3 : 3 ≤ M := by omega
  have hL7 : (7 : ℝ) ≤ L := by exact_mod_cast hL
  set ℓ := (L : ℝ)
  set cd := 2 ^ M * (1 + 2 * M : ℝ) ^ d * cS
  have hcd0 : 0 ≤ cd := by have := h.hcS; positivity
  have hcS_le : cS ≤ cd := by
    have h1 : (1 : ℝ) ≤ 2 ^ M := one_le_pow₀ (by norm_num)
    have h2 : (1 : ℝ) ≤ (1 + 2 * M : ℝ) ^ d :=
      one_le_pow₀ (by linarith [show (0 : ℝ) ≤ M from Nat.cast_nonneg M])
    have := h.hcS
    have h3 : (1 : ℝ) ≤ 2 ^ M * (1 + 2 * M : ℝ) ^ d := by nlinarith
    calc cS = 1 * cS := by ring
      _ ≤ 2 ^ M * (1 + 2 * M : ℝ) ^ d * cS := mul_le_mul_of_nonneg_right h3 h.hcS
  set r := ℓ ^ (-(j : ℝ))
  have hr0 : 0 < r := Real.rpow_pos_of_pos hL0 _
  have hnr : (L : ℝ) ≤ n * r := by
    rw [hn]; push_cast
    simp only [r, ℓ]
    rw [← Real.rpow_natCast (L : ℝ) N, ← Real.rpow_add hL0]
    have : (1 : ℝ) ≤ (N : ℝ) + -(j : ℝ) := by
      have : (j : ℝ) + 1 ≤ N := by exact_mod_cast hjN
      linarith
    calc (L : ℝ) = (L : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL1.le this
  refine snorm_le_iff.2 fun α hα => ?_
  set a := Grassmann.mabs α
  set b : ℝ := (M : ℝ) - a
  have hb : (d : ℝ) < b := by
    have : (a : ℝ) ≤ q := by exact_mod_cast hα
    have : ((q + d + 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast hM
    push_cast at this; simp only [b]; linarith
  set G := ∑ k ∈ Ioc j N, ℓ ^ ((((k - 1 : ℕ) : ℝ)) * (2 - (M : ℝ)))
  -- the pointwise bounds
  have hu : ∀ m, ‖(Cle C j * (1 - Ehat msq C j)) m‖ =
      (∑ k ∈ Icc 1 j, C k m) * (1 - ereal msq C j m) := by
    intro m
    rw [Pi.mul_apply, Cle_apply, Pi.sub_apply, Pi.one_apply, Ehat_apply, ← Complex.ofReal_one,
      ← Complex.ofReal_sub, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_of_nonneg]
    exact mul_nonneg (sum_nonneg fun k _ => h.base.nonneg k m)
      (by linarith [ereal_le_one h.base hjN.le m])
  have hsmall : ∀ m, pnorm m ≤ r → ‖sigma α m‖ * ‖(Cle C j * (1 - Ehat msq C j)) m‖ ≤
      r ^ a * (cd * ℓ ^ d * ℓ ^ (2 * j)) := by
    intro m hm
    rw [hu m]
    have h1 : ‖sigma α m‖ ≤ r ^ a :=
      (norm_sigma_le_pnorm α m).trans (pow_le_pow_left₀ (pnorm_nonneg m) hm a)
    have h2 : (∑ k ∈ Icc 1 j, C k m) * (1 - ereal msq C j m) ≤ cd * ℓ ^ d * ℓ ^ (2 * j) := by
      have he := ereal_nonneg h.base j m
      have hs0 : 0 ≤ ∑ k ∈ Icc 1 j, C k m := sum_nonneg fun k _ => h.base.nonneg k m
      calc (∑ k ∈ Icc 1 j, C k m) * (1 - ereal msq C j m) ≤ ∑ k ∈ Icc 1 j, C k m := by
            nlinarith
        _ ≤ ∑ k ∈ Icc 1 j, cd * ℓ ^ d * ℓ ^ (2 * (k - 1)) := by
            refine sum_le_sum fun k hk => ?_
            rw [mem_Icc] at hk
            have := std_d h hd (by omega) hk.1 (by omega) m
            have hy : 1 ≤ (1 + ℓ ^ (k - 1) * pnorm m) ^ M :=
              one_le_pow₀ (by have := pnorm_nonneg m; have : 0 ≤ ℓ ^ (k - 1) := by positivity
                              nlinarith)
            nlinarith [h.base.nonneg k m]
        _ = cd * ℓ ^ d * ∑ k ∈ range j, (ℓ ^ 2) ^ k := by
            rw [mul_sum]
            refine sum_nbij' (fun k => k - 1) (fun i => i + 1) ?_ ?_ ?_ ?_ ?_
            · intro k hk; simp only [mem_Icc, mem_range] at hk ⊢; omega
            · intro i hi; simp only [mem_Icc, mem_range] at hi ⊢; omega
            · intro k hk; simp only [mem_Icc] at hk; omega
            · intro i _; omega
            · intro k _; rw [← pow_mul]
        _ ≤ cd * ℓ ^ d * (ℓ ^ 2) ^ j :=
            mul_le_mul_of_nonneg_left (sum_range_pow_le (by
              nlinarith) j) (by positivity)
        _ = cd * ℓ ^ d * ℓ ^ (2 * j) := by rw [← pow_mul]
    exact mul_le_mul h1 h2 (by rw [← hu m]; positivity) (pow_nonneg hr0.le a)
  have hlarge : ∀ m, r < pnorm m → ‖sigma α m‖ * ‖(Cle C j * (1 - Ehat msq C j)) m‖ ≤
      cd * ℓ ^ d * G * pnorm m ^ (-b) := by
    intro m hm
    have hp0 : 0 < pnorm m := lt_trans hr0 hm
    have hm0 : m ≠ 0 := by
      rintro rfl
      have : pnorm (0 : Torus d n) = 0 := by
        unfold pnorm
        simp [char_zero_left]
      linarith
    rw [hu m]
    -- `C_{≤j}(1-ê_j) = ê_j C_{>j} ≤ C_{>j}`
    have hCgt : (∑ k ∈ Icc 1 j, C k m) * (1 - ereal msq C j m) ≤ ∑ k ∈ Ioc j N, C k m := by
      have hsum : ∑ k ∈ Icc 1 j, C k m + ∑ k ∈ Ioc j N, C k m = (lam m + msq)⁻¹ := by
        rw [← h.base.sum_eq m]
        have hU : Icc 1 N = Icc 1 j ∪ Ioc j N := by
          ext k; simp only [mem_Icc, mem_union, mem_Ioc]; omega
        rw [hU, sum_union (disjoint_left.2 fun k h1 h2 => by
          simp only [mem_Icc, mem_Ioc] at h1 h2; omega)]
      have hp := lam_add_pos h.base m
      have he := ereal_nonneg h.base j m
      have he1 := ereal_le_one h.base hjN.le m
      have h1e : 1 - ereal msq C j m = (lam m + msq) * ∑ k ∈ Ioc j N, C k m := by
        unfold ereal
        have : (lam m + msq) * ((lam m + msq)⁻¹) = 1 := mul_inv_cancel₀ hp.ne'
        rw [← hsum] at this
        linarith [this]
      rw [h1e]
      have : (∑ k ∈ Icc 1 j, C k m) * ((lam m + msq) * ∑ k ∈ Ioc j N, C k m) =
          ereal msq C j m * ∑ k ∈ Ioc j N, C k m := by unfold ereal; ring
      rw [this]
      have hg0 : 0 ≤ ∑ k ∈ Ioc j N, C k m := sum_nonneg fun k _ => h.base.nonneg k m
      nlinarith
    have hCk : ∀ k ∈ Ioc j N, C k m ≤ cd * ℓ ^ d * ℓ ^ ((((k - 1 : ℕ) : ℝ)) * (2 - (M : ℝ))) *
        pnorm m ^ (-(M : ℝ)) := by
      intro k hk
      rw [mem_Ioc] at hk
      have hbd : C k m * (1 + ℓ ^ (k - 1) * pnorm m) ^ M ≤ cd * ℓ ^ d * ℓ ^ (2 * (k - 1)) := by
        by_cases hkN : k < N
        · exact std_d h hd (by omega) (by omega) hkN m
        · have : k = N := by omega
          subst this
          have := h.S5 m hm0
          calc C k m * (1 + ℓ ^ (k - 1) * pnorm m) ^ M ≤ cS * ℓ ^ d * ℓ ^ (2 * (k - 1)) := this
            _ ≤ cd * ℓ ^ d * ℓ ^ (2 * (k - 1)) := by gcongr
      have hy : 0 < ℓ ^ (k - 1) * pnorm m := mul_pos (by positivity) hp0
      have hyM : (ℓ ^ (k - 1) * pnorm m) ^ M ≤ (1 + ℓ ^ (k - 1) * pnorm m) ^ M :=
        pow_le_pow_left₀ hy.le (by linarith) M
      have hC0 := h.base.nonneg k m
      have hCy : C k m * (ℓ ^ (k - 1) * pnorm m) ^ M ≤ cd * ℓ ^ d * ℓ ^ (2 * (k - 1)) :=
        le_trans (mul_le_mul_of_nonneg_left hyM hC0) hbd
      have hyMpos : 0 < (ℓ ^ (k - 1) * pnorm m) ^ M := pow_pos hy M
      rw [← le_div_iff₀ hyMpos] at hCy
      refine hCy.trans (le_of_eq ?_)
      rw [mul_pow, ← pow_mul]
      rw [show cd * ℓ ^ d * ℓ ^ (2 * (k - 1)) / (ℓ ^ ((k - 1) * M) * pnorm m ^ M) =
        cd * ℓ ^ d * (ℓ ^ (2 * (k - 1)) / ℓ ^ ((k - 1) * M)) * (pnorm m ^ M)⁻¹ by
          field_simp]
      congr 1
      · congr 1
        rw [← Real.rpow_natCast ℓ (2 * (k - 1)), ← Real.rpow_natCast ℓ ((k - 1) * M),
          ← Real.rpow_sub hL0]
        congr 1; push_cast; ring
      · rw [Real.rpow_neg hp0.le, Real.rpow_natCast]
    have hσ : ‖sigma α m‖ ≤ pnorm m ^ (a : ℝ) := by
      rw [Real.rpow_natCast]; exact norm_sigma_le_pnorm α m
    calc ‖sigma α m‖ * ((∑ k ∈ Icc 1 j, C k m) * (1 - ereal msq C j m))
        ≤ pnorm m ^ (a : ℝ) * ∑ k ∈ Ioc j N, cd * ℓ ^ d *
            ℓ ^ ((((k - 1 : ℕ) : ℝ)) * (2 - (M : ℝ))) * pnorm m ^ (-(M : ℝ)) := by
          refine mul_le_mul hσ (hCgt.trans (sum_le_sum hCk)) ?_ (by positivity)
          rw [← hu m]; positivity
      _ = cd * ℓ ^ d * G * (pnorm m ^ (a : ℝ) * pnorm m ^ (-(M : ℝ))) := by
          simp only [G, mul_sum, sum_mul]
          refine sum_congr rfl fun k _ => by ring
      _ = cd * ℓ ^ d * G * pnorm m ^ (-b) := by
          rw [← Real.rpow_add hp0]; congr 2; simp only [b]; ring
  -- assembly
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hnd : (0 : ℝ) < (n : ℝ) ^ d := pow_pos hn0 d
  have hnr2 : 2 * Real.pi ≤ n * r := by have := Real.pi_lt_d2; linarith
  have hX : 0 ≤ cd * ℓ ^ d * ℓ ^ (2 * j) :=
    mul_nonneg (mul_nonneg hcd0 (pow_nonneg hL0.le _)) (pow_nonneg hL0.le _)
  have hG0 : 0 ≤ G := sum_nonneg fun k _ => Real.rpow_nonneg hL0.le _
  have hcdl : 0 ≤ cd * ℓ ^ d := mul_nonneg hcd0 (pow_nonneg hL0.le _)
  set S := ∑ m ∈ univ.filter (fun m : Torus d n => r < pnorm m), pnorm m ^ (-b)
  have hS0 : 0 ≤ S := sum_nonneg fun m _ => Real.rpow_nonneg (pnorm_nonneg m) _
  have hsplit : mom α (Cle C j * (1 - Ehat msq C j)) ≤
      ((n : ℝ) ^ d)⁻¹ * (((n : ℝ) * r) ^ d * (r ^ a * (cd * ℓ ^ d * ℓ ^ (2 * j)))) +
        ((n : ℝ) ^ d)⁻¹ * (cd * ℓ ^ d * G * S) := by
    unfold mom avg
    rw [← sum_filter_add_sum_filter_not univ (fun m => pnorm m ≤ r), mul_add]
    have h1 : ∑ m ∈ univ.filter (fun m : Torus d n => pnorm m ≤ r),
        ‖sigma α m‖ * ‖(Cle C j * (1 - Ehat msq C j)) m‖ ≤
          ((n : ℝ) * r) ^ d * (r ^ a * (cd * ℓ ^ d * ℓ ^ (2 * j))) := by
      calc _ ≤ ∑ m ∈ univ.filter (fun m : Torus d n => pnorm m ≤ r),
            r ^ a * (cd * ℓ ^ d * ℓ ^ (2 * j)) :=
            sum_le_sum fun m hm => hsmall m (mem_filter.1 hm).2
        _ = ((univ.filter fun m : Torus d n => pnorm m ≤ r).card : ℝ) *
            (r ^ a * (cd * ℓ ^ d * ℓ ^ (2 * j))) := by rw [sum_const, nsmul_eq_mul]
        _ ≤ _ := by
            refine mul_le_mul_of_nonneg_right ((card_pnorm_le hd hr0.le).trans
              (pow_le_pow_left₀ (by positivity) (by linarith) d)) ?_
            exact mul_nonneg (pow_nonneg hr0.le a) hX
    have h2 : ∑ m ∈ univ.filter (fun m : Torus d n => ¬ pnorm m ≤ r),
        ‖sigma α m‖ * ‖(Cle C j * (1 - Ehat msq C j)) m‖ ≤ cd * ℓ ^ d * G * S := by
      have : univ.filter (fun m : Torus d n => ¬ pnorm m ≤ r) =
          univ.filter (fun m : Torus d n => r < pnorm m) := by ext; simp
      rw [this]; simp only [S]; rw [mul_sum]
      exact sum_le_sum fun m hm => hlarge m (mem_filter.1 hm).2
    have hi : (0 : ℝ) ≤ ((n : ℝ) ^ d)⁻¹ := inv_nonneg.2 hnd.le
    exact add_le_add (mul_le_mul_of_nonneg_left h1 hi) (mul_le_mul_of_nonneg_left h2 hi)
  have hw0 : 0 < wgt d ℓ j α := wgt_pos hL0 j α
  have hE1 : wgt d ℓ j α * (r ^ d * r ^ a * ℓ ^ (2 * j)) = 1 := by
    unfold wgt; simp only [r]
    rw [← Real.rpow_natCast (ℓ ^ (-(j : ℝ))) d, ← Real.rpow_natCast (ℓ ^ (-(j : ℝ))) a,
      ← Real.rpow_natCast ℓ (2 * j), ← Real.rpow_mul hL0.le, ← Real.rpow_mul hL0.le,
      ← Real.rpow_add hL0, ← Real.rpow_add hL0, ← Real.rpow_add hL0]
    convert Real.rpow_zero ℓ using 2
    simp only [a]; push_cast; ring
  have hE2 : wgt d ℓ j α * (r ^ ((d : ℝ) - b) * ℓ ^ ((j : ℝ) * (2 - (M : ℝ)))) = 1 := by
    unfold wgt; simp only [r, b]
    rw [← Real.rpow_mul hL0.le, ← Real.rpow_add hL0, ← Real.rpow_add hL0]
    convert Real.rpow_zero ℓ using 2
    simp only [a]; ring
  have htail := sum_pnorm_rpow_tail (n := n) hd hb hr0 hnr2
  set Q' := (1 - (2 : ℝ) ^ ((d : ℝ) - b))⁻¹
  set Q := (1 - (2 : ℝ) ^ ((d : ℝ) - ((M : ℝ) - q)))⁻¹
  set P := (1 - ℓ ^ (2 - (M : ℝ)))⁻¹
  have hbq : (M : ℝ) - q ≤ b := by
    have : (a : ℝ) ≤ q := by exact_mod_cast hα
    simp only [b]; linarith
  have hbM : b ≤ M := by simp only [b]; have := Nat.cast_nonneg (α := ℝ) a; linarith
  have hMq : (d : ℝ) < (M : ℝ) - q := by
    have : ((q + d + 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast hM
    push_cast at this; linarith
  have hQ'0 : 0 < 1 - (2 : ℝ) ^ ((d : ℝ) - b) := by
    have := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2)
      (by linarith : (d : ℝ) - b < 0)
    linarith
  have hQ0 : 0 < 1 - (2 : ℝ) ^ ((d : ℝ) - ((M : ℝ) - q)) := by
    have := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2)
      (by linarith : (d : ℝ) - ((M : ℝ) - q) < 0)
    linarith
  have hQ'Q : Q' ≤ Q := by
    simp only [Q', Q]
    refine inv_anti₀ hQ0 ?_
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by linarith : (d : ℝ) - b ≤ (d : ℝ) - ((M : ℝ) - q))
    linarith
  have hP0 : 0 ≤ P := by
    simp only [P]
    have := Real.rpow_lt_one_of_one_lt_of_neg hL1 (by
      have : (3 : ℝ) ≤ M := by exact_mod_cast hM3
      linarith : 2 - (M : ℝ) < 0)
    exact inv_nonneg.2 (by linarith)
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hT : (4 : ℝ) ^ (-b) * (2 * Real.pi) ^ (b - d) ≤ (Real.pi / 2) ^ M := by
    have hb0 : 0 ≤ b := by have := Nat.cast_nonneg (α := ℝ) d; linarith
    have heq : (4 : ℝ) ^ (-b) * (2 * Real.pi) ^ (b - d) =
        (Real.pi / 2) ^ b * ((2 * Real.pi) ^ (d : ℝ))⁻¹ := by
      rw [Real.rpow_sub hπ, Real.rpow_neg (by norm_num), Real.div_rpow Real.pi_pos.le
        (by norm_num), Real.mul_rpow (by norm_num) Real.pi_pos.le,
        show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      rw [show (2 : ℝ) * b = b + b by ring, Real.rpow_add (by norm_num)]
      have : (0 : ℝ) < 2 ^ b := by positivity
      have : (0 : ℝ) < Real.pi ^ b := by positivity
      have : (0 : ℝ) < (2 * Real.pi) ^ (d : ℝ) := by positivity
      field_simp
    rw [heq]
    have h1 : (Real.pi / 2) ^ b ≤ (Real.pi / 2) ^ M := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) hbM
    have h2 : ((2 * Real.pi) ^ (d : ℝ))⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (Real.one_le_rpow (by linarith [Real.pi_gt_three])
        (Nat.cast_nonneg d))
    have : 0 ≤ (Real.pi / 2) ^ M := by positivity
    calc _ ≤ (Real.pi / 2) ^ M * 1 := mul_le_mul h1 h2 (by positivity) this
      _ = _ := mul_one _
  have hGle : G ≤ ℓ ^ ((j : ℝ) * (2 - (M : ℝ))) * P := sum_Ioc_geom_le hL1 hM3 j N
  have hSle : ((n : ℝ) ^ d)⁻¹ * S ≤
      5 ^ d * Q' * ((4 : ℝ) ^ (-b) * (2 * Real.pi) ^ (b - d)) * r ^ ((d : ℝ) - b) := by
    rw [inv_mul_le_iff₀ hnd]; refine htail.trans (le_of_eq ?_); simp only [Q']; ring
  have hQ'nn : 0 ≤ Q' := inv_nonneg.2 hQ'0.le
  have hTnn : 0 ≤ (4 : ℝ) ^ (-b) * (2 * Real.pi) ^ (b - d) := by positivity
  have hrb : 0 ≤ r ^ ((d : ℝ) - b) := Real.rpow_nonneg hr0.le _
  have hlg : 0 ≤ ℓ ^ ((j : ℝ) * (2 - (M : ℝ))) := Real.rpow_nonneg hL0.le _
  calc wgt d ℓ j α * mom α (Cle C j * (1 - Ehat msq C j))
      ≤ wgt d ℓ j α * (((n : ℝ) ^ d)⁻¹ * (((n : ℝ) * r) ^ d *
          (r ^ a * (cd * ℓ ^ d * ℓ ^ (2 * j)))) + ((n : ℝ) ^ d)⁻¹ * (cd * ℓ ^ d * G * S)) :=
        mul_le_mul_of_nonneg_left hsplit hw0.le
    _ = cd * ℓ ^ d * (wgt d ℓ j α * (r ^ d * r ^ a * ℓ ^ (2 * j))) +
          wgt d ℓ j α * (cd * ℓ ^ d) * G * (((n : ℝ) ^ d)⁻¹ * S) := by
        rw [mul_pow]
        have : ((n : ℝ) ^ d)⁻¹ * ((n : ℝ) ^ d * r ^ d * (r ^ a * (cd * ℓ ^ d * ℓ ^ (2 * j)))) =
            r ^ d * (r ^ a * (cd * ℓ ^ d * ℓ ^ (2 * j))) := by
          rw [mul_assoc, ← mul_assoc ((n : ℝ) ^ d)⁻¹, inv_mul_cancel₀ hnd.ne', one_mul]
        rw [this]; ring
    _ ≤ cd * ℓ ^ d * 1 + wgt d ℓ j α * (cd * ℓ ^ d) * (ℓ ^ ((j : ℝ) * (2 - (M : ℝ))) * P) *
          (5 ^ d * Q' * ((4 : ℝ) ^ (-b) * (2 * Real.pi) ^ (b - d)) * r ^ ((d : ℝ) - b)) := by
        rw [hE1]
        refine add_le_add_right (mul_le_mul (mul_le_mul_of_nonneg_left hGle
          (mul_nonneg hw0.le hcdl)) hSle (mul_nonneg (inv_nonneg.2 hnd.le) hS0)
          (mul_nonneg (mul_nonneg hw0.le hcdl) (mul_nonneg hlg hP0))) _
    _ = cd * ℓ ^ d + cd * ℓ ^ d * (5 ^ d * Q' * ((4 : ℝ) ^ (-b) * (2 * Real.pi) ^ (b - d)) * P) *
          (wgt d ℓ j α * (r ^ ((d : ℝ) - b) * ℓ ^ ((j : ℝ) * (2 - (M : ℝ))))) := by ring
    _ = cd * ℓ ^ d + cd * ℓ ^ d * (5 ^ d * Q' * ((4 : ℝ) ^ (-b) * (2 * Real.pi) ^ (b - d)) * P) := by
        rw [hE2, mul_one]
    _ ≤ cd * ℓ ^ d + cd * ℓ ^ d * (5 ^ d * Q * (Real.pi / 2) ^ M * P) := by
        refine add_le_add_right (mul_le_mul_of_nonneg_left ?_ hcdl) _
        refine mul_le_mul_of_nonneg_right ?_ hP0
        exact mul_le_mul (mul_le_mul_of_nonneg_left hQ'Q (by positivity)) hT hTnn
          (mul_nonneg (by positivity) (hQ'nn.trans hQ'Q))
    _ = c2val d L q M cS := by simp only [c2val, cd, Q, P, ℓ]; ring

end

end DressedFRD

