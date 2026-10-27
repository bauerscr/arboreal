import Obs2.Est.LinComp

/-!
# The contraction of the linear part for one component, output regulator `λA`

**`lin_comp_boundL`**: `Obs2.lin_comp_bound` with the output measured with the regulator `λA`
(`λ ≥ 1` fixed), as `Step2.Llin2_boundL`: `λ^{|𝓑_{j+1}(U)|} ≤ λ^{|𝓑_j(X)|}` is absorbed in the
Pauli factor `Q ↦ λQ` of the large-set estimate (`A ≥ A₀(L, λ)`).
-/

namespace Obs2

noncomputable section

open Finset Grassmann Loc FRD Step Step2

variable {d L N : ℕ} [NeZero L]

open Classical in
/-- **The contraction of the linear part, one component.** -/
theorem lin_comp_boundL (d : ℕ) (hd : 2 ≤ d) : ∃ (cn η : ℝ) (L₀ : ℕ), 0 ≤ cn ∧ 0 < η ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∀ lam : ℝ, 1 ≤ lam → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓC C →
    ∀ (a : Lam d L N) (Cl : ℝ), 0 ≤ Cl →
    ∀ (G H : Finset (Lam d L N) → Alg d L N) (m k : ENNReal),
      (∀ X, IsSmall j X → Tj d (L : ℝ) (j + 1) (2 * ℓ) (H X) ≤
        ENNReal.ofReal (Cl / L) * Tj d (L : ℝ) j ℓ (G X)) →
      (∀ X, IsSmall j X → a ∉ nbhd j X → H X = 0) →
      (∀ X, IsConn j X → ¬ IsSmall j X → G X ∈ NX (nbhd j X : Set (Lam d L N))) →
      (∀ X, IsConn j X → ENNReal.ofReal (A ^ (nb j X - 2 ^ d)) * (m * Tj d (L : ℝ) j ℓ (G X)) ≤ k) →
      ∀ U : Finset (Lam d L N), IsConn (j + 1) U →
        ENNReal.ofReal ((lam * A) ^ (nb (j + 1) U - 2 ^ d)) * (m * Tj d (L : ℝ) (j + 1) ℓ'
          ((∑ X ∈ (Pj j univ).filter (fun X => IsSmall j X ∧ clo j X = U), ECC C (theta (H X))) +
            ∑ X ∈ (Pj j univ).filter (fun X => IsConn j X ∧ ¬ IsSmall j X ∧ clo j X = U),
              ECC C (theta (G X)))) ≤
          ENNReal.ofReal (cn * Cl / L + A ^ (-η)) * k := by
  obtain ⟨cs, hcs⟩ := card_small_near d
  obtain ⟨η, hη0, hη1, hcomb⟩ := comb1 d
  set s := min (2 * η / (1 + 2 * η)) (1 / (2 ^ d + 1)) with hsdef
  have hs0 : 0 < s := lt_min (by positivity) (by positivity)
  refine ⟨cs, s / 2, max (2 ^ (d + 3) + 8 * d + 1) ⌈pauliL0 d⌉₊, by positivity, by positivity, ?_⟩
  intro L _ hL lam hlam
  have hL8 : 2 ^ (d + 3) + 8 * d < L :=
    lt_of_lt_of_le (Nat.lt_succ_self _) (le_trans (le_max_left _ _) hL)
  have hLp : pauliL0 d ≤ L := (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hL)
  have hd1 : 1 ≤ d := by omega
  set M := (2 ^ (d + 1) + 3) ^ d
  set Q : ℝ := pq d ^ M
  have hQ : 1 ≤ Q := one_le_pow₀ (one_le_pq hd1)
  set P : ℝ := ((L ^ d : ℕ) : ℝ)
  have hP : 0 ≤ P := Nat.cast_nonneg _
  have hlQ : 1 ≤ lam * Q := by nlinarith
  set A₁ : ℝ := ((2 ^ P * (lam * Q)) ^ 2) ^ (1 / s)
  refine ⟨max 1 A₁, le_max_left _ _, ?_⟩
  intro A hA
  have hA1 : 1 ≤ A := le_trans (le_max_left _ _) hA
  have hA0 : 0 < A := by linarith
  have hAQ : (2 ^ P * (lam * Q)) ^ 2 ≤ A ^ s := by
    have h0 : 0 ≤ (2 ^ P * (lam * Q)) ^ 2 := by positivity
    calc (2 ^ P * (lam * Q)) ^ 2 = A₁ ^ s := by
          rw [← Real.rpow_mul h0, one_div_mul_cancel hs0.ne', Real.rpow_one]
      _ ≤ A ^ s := Real.rpow_le_rpow (by positivity) (le_trans (le_max_right _ _) hA) hs0.le
  intro N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC a Cl hCl G H m k hH hz hG hk U hU
  have hj : j < N := by omega
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set w := ENNReal.ofReal ((lam * A) ^ (nb (j + 1) U - 2 ^ d))
  -- the small sets
  have hS : w * (m * Tj d (L : ℝ) (j + 1) ℓ'
      (∑ X ∈ (Pj j univ).filter (fun X => IsSmall j X ∧ clo j X = U), ECC C (theta (H X)))) ≤
        ENNReal.ofReal (cs * Cl / L) * k := by
    by_cases hUs : IsSmall (j + 1) U
    · have hw : w = 1 := by
        have h0 : nb (j + 1) U - 2 ^ d = 0 := Nat.sub_eq_zero_of_le hUs.2.2
        rw [show w = ENNReal.ofReal ((lam * A) ^ (nb (j + 1) U - 2 ^ d)) from rfl, h0, pow_zero,
          ENNReal.ofReal_one]
      rw [hw, one_mul]
      set T := (Pj j univ).filter (fun X => IsSmall j X ∧ clo j X = U)
      set T' := T.filter (fun X => a ∈ nbhd j X)
      have hsplit : ∑ X ∈ T, ECC C (theta (H X)) = ∑ X ∈ T', ECC C (theta (H X)) :=
        (sum_subset (filter_subset _ T) fun X hX hX' => by
          rw [hz X (mem_filter.1 hX).2.1 (fun h => hX' (mem_filter.2 ⟨hX, h⟩)), map_zero,
            map_zero]).symm
      rw [hsplit]
      have hcard : T'.card ≤ cs := by
        refine le_trans (card_le_card fun X hX => ?_) (hcs L N j a)
        obtain ⟨hXT, haX⟩ := mem_filter.1 hX
        exact mem_filter.2 ⟨mem_smallSets.2 (mem_filter.1 hXT).2.1, haX⟩
      have hterm : ∀ X ∈ T', m * Tj d (L : ℝ) (j + 1) ℓ' (ECC C (theta (H X))) ≤
          ENNReal.ofReal (Cl / L) * k := by
        intro X hX
        have hs : IsSmall j X := (mem_filter.1 (mem_filter.1 hX).1).2.1
        have hc : IsConn j X := ⟨hs.1, hs.2.1⟩
        have h1 := (EthE_succ_le2' hℓ' hℓC hsum hC (H X)).trans (hH X hs)
        have hkX := hk X hc
        have h0 : nb j X - 2 ^ d = 0 := Nat.sub_eq_zero_of_le hs.2.2
        rw [h0, pow_zero, ENNReal.ofReal_one, one_mul] at hkX
        calc m * Tj d (L : ℝ) (j + 1) ℓ' (ECC C (theta (H X)))
            ≤ m * (ENNReal.ofReal (Cl / L) * Tj d (L : ℝ) j ℓ (G X)) := by gcongr
          _ = ENNReal.ofReal (Cl / L) * (m * Tj d (L : ℝ) j ℓ (G X)) := by ring
          _ ≤ ENNReal.ofReal (Cl / L) * k := by gcongr
      calc m * Tj d (L : ℝ) (j + 1) ℓ' (∑ X ∈ T', ECC C (theta (H X)))
          ≤ m * ∑ X ∈ T', Tj d (L : ℝ) (j + 1) ℓ' (ECC C (theta (H X))) := by
            gcongr; exact tNorm_sum_le _ _
        _ = ∑ X ∈ T', m * Tj d (L : ℝ) (j + 1) ℓ' (ECC C (theta (H X))) := mul_sum _ _ _
        _ ≤ (cs : ENNReal) * (ENNReal.ofReal (Cl / L) * k) :=
            sum_le_card_mul_ennreal _ _ _ _ hcard hterm
        _ = ENNReal.ofReal (cs * Cl / L) * k := by
            rw [← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
            congr 2; ring
    · have he : (Pj j univ).filter (fun X => IsSmall j X ∧ clo j X = U) = ∅ := by
        refine filter_eq_empty_iff.2 fun X _ h => hUs ?_
        rw [← h.2]; exact isSmall_clo h.1
      rw [he, sum_empty, Step.Tj_zero (d := d) (L : ℝ) (j + 1) ℓ', mul_zero, mul_zero]
      exact zero_le
  -- the large sets
  have hB : w * (m * Tj d (L : ℝ) (j + 1) ℓ' (∑ X ∈ (Pj j univ).filter
      (fun X => IsConn j X ∧ ¬ IsSmall j X ∧ clo j X = U), ECC C (theta (G X)))) ≤
        ENNReal.ofReal (A ^ (-(s / 2))) * k := by
    set T := (Pj j univ).filter (fun X => IsConn j X ∧ ¬ IsSmall j X ∧ clo j X = U)
    set Mc : ℕ := 2 ^ (L ^ d * nb (j + 1) U)
    have hcard : T.card ≤ Mc := by
      refine le_trans (card_le_card ?_) (card_clo_eq_le hU.1)
      intro X hX
      obtain ⟨h1, -, -, h4⟩ := mem_filter.1 hX
      exact mem_filter.2 ⟨h1, h4⟩
    have hterm : ∀ X ∈ T, w * (m * Tj d (L : ℝ) (j + 1) ℓ' (ECC C (theta (G X)))) ≤
        ENNReal.ofReal (A ^ (-(s / 2)) / 2 ^ (L ^ d * nb (j + 1) U)) * k := by
      intro X hX
      obtain ⟨-, hc, hns, hcl⟩ := mem_filter.1 hX
      set x := nb (j + 1) U
      set t := nb j X
      have ht : 2 ^ d < t := by
        by_contra h; push Not at h; exact hns ⟨hc.1, hc.2, h⟩
      have h2d : 2 ^ d ≤ 2 ^ (d + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hcb := hcomb L (by omega) N j X hj hc hns
      rw [hcl] at hcb
      have hE : Tj d (L : ℝ) (j + 1) ℓ' (ECC C (theta (G X))) ≤
          ENNReal.ofReal (Q ^ t) * Tj d (L : ℝ) j ℓ (G X) := by
        refine (EthE_succ_le2 hd1 hLp hj hℓ' hℓC hsum hC (hG X hc hns)).trans
          (mul_le_mul_left ?_ _)
        refine ENNReal.ofReal_le_ofReal ?_
        rw [show Q ^ t = pq d ^ (M * t) by simp only [Q, ← pow_mul]]
        exact pow_le_pow_right₀ (one_le_pq hd1) (nb_nbhd_le hj.le X)
      have hKX := hk X hc
      have hreal := large_real (x := x) (t := t) hA1 hη0 hlQ hcb ht hAQ hP
      have hxt : x ≤ t := by
        have : (x : ℝ) ≤ t := by nlinarith [Nat.cast_nonneg (α := ℝ) x]
        exact_mod_cast this
      have hlam' : (lam * A) ^ (x - 2 ^ d) * Q ^ t ≤ A ^ (x - 2 ^ d) * (lam * Q) ^ t := by
        rw [mul_pow, mul_pow]
        have : lam ^ (x - 2 ^ d) ≤ lam ^ t := pow_le_pow_right₀ hlam ((Nat.sub_le _ _).trans hxt)
        have h0 : 0 ≤ A ^ (x - 2 ^ d) * Q ^ t := by positivity
        nlinarith
      have hpos : (0 : ℝ) < A ^ (t - 2 ^ d) := by positivity
      have h2 : (2 : ℝ) ^ (L ^ d * x) = (2 ^ P) ^ x := by
        rw [← Real.rpow_natCast (2 : ℝ) (L ^ d * x), ← Real.rpow_natCast ((2 : ℝ) ^ P) x,
          ← Real.rpow_mul (by norm_num)]
        congr 1; push_cast [P]; ring
      set Z := m * Tj d (L : ℝ) j ℓ (G X)
      calc w * (m * Tj d (L : ℝ) (j + 1) ℓ' (ECC C (theta (G X))))
          ≤ w * (m * (ENNReal.ofReal (Q ^ t) * Tj d (L : ℝ) j ℓ (G X))) := by gcongr
        _ = ENNReal.ofReal ((lam * A) ^ (x - 2 ^ d)) * (ENNReal.ofReal (Q ^ t) * Z) := by
            rw [mul_left_comm m]
        _ = ENNReal.ofReal ((lam * A) ^ (x - 2 ^ d) * Q ^ t / A ^ (t - 2 ^ d)) *
              (ENNReal.ofReal (A ^ (t - 2 ^ d)) * Z) :=
            ofReal_reweight (by positivity) (by positivity) hpos Z
        _ ≤ ENNReal.ofReal (A ^ (-(s / 2)) / 2 ^ (L ^ d * x)) * k := by
            refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) hKX
            rw [h2, div_le_div_iff₀ hpos (by positivity)]
            calc (lam * A) ^ (x - 2 ^ d) * Q ^ t * (2 ^ P) ^ x
                ≤ A ^ (x - 2 ^ d) * (lam * Q) ^ t * (2 ^ P) ^ x := by gcongr
              _ ≤ A ^ (-(s / 2)) * A ^ (t - 2 ^ d) := hreal
              _ = _ := rfl
    calc w * (m * Tj d (L : ℝ) (j + 1) ℓ' (∑ X ∈ T, ECC C (theta (G X))))
        ≤ w * (m * ∑ X ∈ T, Tj d (L : ℝ) (j + 1) ℓ' (ECC C (theta (G X)))) := by
          gcongr; exact tNorm_sum_le _ _
      _ = ∑ X ∈ T, w * (m * Tj d (L : ℝ) (j + 1) ℓ' (ECC C (theta (G X)))) := by
          rw [mul_sum, mul_sum]
      _ ≤ (Mc : ENNReal) * (ENNReal.ofReal (A ^ (-(s / 2)) / 2 ^ (L ^ d * nb (j + 1) U)) * k) :=
          sum_le_card_mul_ennreal _ _ _ _ hcard hterm
      _ = ENNReal.ofReal (A ^ (-(s / 2))) * k := by
          rw [← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          congr 2
          have : (0 : ℝ) < Mc := by positivity
          simp only [Mc, Nat.cast_pow, Nat.cast_ofNat]
          field_simp
  calc w * (m * Tj d (L : ℝ) (j + 1) ℓ' (_ + _))
      ≤ w * (m * (Tj d (L : ℝ) (j + 1) ℓ'
          (∑ X ∈ (Pj j univ).filter (fun X => IsSmall j X ∧ clo j X = U), ECC C (theta (H X))) +
        Tj d (L : ℝ) (j + 1) ℓ' (∑ X ∈ (Pj j univ).filter
          (fun X => IsConn j X ∧ ¬ IsSmall j X ∧ clo j X = U), ECC C (theta (G X))))) := by
        gcongr; exact tNorm_add_le _ _
    _ = w * (m * Tj d (L : ℝ) (j + 1) ℓ'
          (∑ X ∈ (Pj j univ).filter (fun X => IsSmall j X ∧ clo j X = U), ECC C (theta (H X)))) +
        w * (m * Tj d (L : ℝ) (j + 1) ℓ' (∑ X ∈ (Pj j univ).filter
          (fun X => IsConn j X ∧ ¬ IsSmall j X ∧ clo j X = U), ECC C (theta (G X)))) := by ring
    _ ≤ ENNReal.ofReal (cs * Cl / L) * k + ENNReal.ofReal (A ^ (-(s / 2))) * k := add_le_add hS hB
    _ = ENNReal.ofReal (cs * Cl / L + A ^ (-(s / 2))) * k := by
        rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]

end

end Obs2
