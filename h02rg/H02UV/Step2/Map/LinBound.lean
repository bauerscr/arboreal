import Step2.Map.Geom
import Step.EstLarge
import Step2.Map.TNorm2

/-!
# The contraction of the linear part (`h02uv-outline.tex`, `thm:step`)

`Llin2_bound`: for `j + 1 < N` and connected `U`,
`A^{(|𝓑_{j+1}(U)| - 2^d)_+} ‖𝓛(K)(U)‖_{T_{j+1}(ℓ)} ≤ C₀ (L^d L^{-3} + A^{-η}) ‖K‖_j`.

* Small sets (`X ∈ 𝒮_j`, `\bar X = U`): `‖𝔼θ (1 - Loc_X) K(X)‖_{T_{j+1}(ℓ)} ≤
  ‖(1 - Loc_X) K(X)‖_{T_{j+1}(2ℓ)} ≤ C L^{-3} ‖K(X)‖_{T_j(ℓ)}` (Lemma `lem:loc2`), and there are
  `O(L^d)` of them. In `d = 2` this is `O(L^{-1})`.
* Large sets: `‖𝔼θ K(X)‖_{T_{j+1}(ℓ)} ≤ q^{|𝓑_j(X^□)|} ‖K(X)‖_{T_j(ℓ)}` (Lemma `lem:pauli`), and
  the combinatorial Lemma `lem:comb1` with `A ≥ A₀(L)` absorbs the entropy and `q^{O(|𝓑_j(X)|)}`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

theorem wnorm_add_le' (j : ℕ) (ℓ A : ℝ) (U : Finset (Lam d L N)) (F G : EvR (Lam d L N)) :
    wnorm j ℓ A U (F + G) ≤ wnorm j ℓ A U F + wnorm j ℓ A U G := by
  unfold wnorm
  rw [← mul_add]
  gcongr
  exact tNorm_add_le _ _

/-- The real inequality for the large sets. -/
theorem large_real {d x t : ℕ} {A η Q P : ℝ} (hA : 1 ≤ A) (hη : 0 < η) (hQ : 1 ≤ Q)
    (hcomb : (1 + 2 * η) * (x : ℝ) ≤ t) (ht : 2 ^ d < t)
    (hAQ : (2 ^ P * Q) ^ 2 ≤ A ^ (min (2 * η / (1 + 2 * η)) (1 / (2 ^ d + 1)))) (hP : 0 ≤ P) :
    A ^ (x - 2 ^ d) * Q ^ t * (2 ^ P) ^ x ≤
      A ^ (-(min (2 * η / (1 + 2 * η)) (1 / (2 ^ d + 1)) / 2)) * A ^ (t - 2 ^ d) := by
  have hA0 : 0 < A := by linarith
  set s := min (2 * η / (1 + 2 * η)) (1 / (2 ^ d + 1)) with hs
  have hs0 : 0 < s := lt_min (by positivity) (by positivity)
  have h2P : (1 : ℝ) ≤ 2 ^ P := Real.one_le_rpow (by norm_num) hP
  have hxt : x ≤ t := by
    have : (x : ℝ) ≤ t := by nlinarith [Nat.cast_nonneg (α := ℝ) x]
    exact_mod_cast this
  -- `(2^P Q)^t ≤ A^{s t / 2}`
  have h1 : Q ^ t * (2 ^ P) ^ x ≤ (2 ^ P * Q) ^ t := by
    rw [mul_pow, mul_comm]
    gcongr
  have hsq : 2 ^ P * Q ≤ A ^ (s / 2) := by
    have h0 : 0 ≤ 2 ^ P * Q := by positivity
    have := Real.sqrt_le_sqrt hAQ
    rw [Real.sqrt_sq h0, Real.sqrt_eq_rpow, ← Real.rpow_mul hA0.le] at this
    calc 2 ^ P * Q ≤ A ^ (s * (1 / 2)) := this
      _ = A ^ (s / 2) := by ring_nf
  have h2 : (2 ^ P * Q) ^ t ≤ A ^ (s / 2 * t) := by
    rw [Real.rpow_mul hA0.le, Real.rpow_natCast]
    exact pow_le_pow_left₀ (by positivity) hsq t
  -- exponents
  have hexp : ((x - 2 ^ d : ℕ) : ℝ) + s / 2 * t ≤ -(s / 2) + ((t - 2 ^ d : ℕ) : ℝ) := by
    have ht' : ((t - 2 ^ d : ℕ) : ℝ) = t - 2 ^ d := by
      rw [Nat.cast_sub ht.le]; push_cast; ring
    rw [ht']
    have htR : (2 : ℝ) ^ d + 1 ≤ t := by exact_mod_cast ht
    have hs1 : s ≤ 2 * η / (1 + 2 * η) := min_le_left _ _
    have hs2 : s ≤ 1 / (2 ^ d + 1) := min_le_right _ _
    have h1η : 0 < 1 + 2 * η := by linarith
    by_cases hx : 2 ^ d ≤ x
    · rw [Nat.cast_sub hx]; push_cast
      -- `t - x ≥ (2η/(1+2η)) t ≥ s t ≥ s (t + 1) / 2`
      have : (2 * η / (1 + 2 * η)) * t ≤ t - x := by
        rw [div_mul_eq_mul_div, div_le_iff₀ h1η]; nlinarith
      have h3 : s * t ≤ t - x := (mul_le_mul_of_nonneg_right hs1 (by positivity)).trans this
      have ht1 : (1 : ℝ) ≤ t := by linarith [one_le_pow₀ (M₀ := ℝ) (n := d) (by norm_num : (1:ℝ) ≤ 2)]
      nlinarith
    · push Not at hx
      rw [Nat.sub_eq_zero_of_le hx.le, Nat.cast_zero, zero_add]
      have h2d : (0 : ℝ) < 2 ^ d + 1 := by positivity
      have : (1 / ((2 : ℝ) ^ d + 1)) * (t : ℝ) ≤ t - 2 ^ d := by
        rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ h2d]
        have : (0 : ℝ) ≤ 2 ^ d * (t - (2 ^ d + 1)) := mul_nonneg (by positivity) (by linarith)
        nlinarith
      have h3 : s * t ≤ t - 2 ^ d :=
        (mul_le_mul_of_nonneg_right hs2 (by positivity)).trans this
      have ht1 : (1 : ℝ) ≤ t := by linarith [one_le_pow₀ (M₀ := ℝ) (n := d) (by norm_num : (1:ℝ) ≤ 2)]
      nlinarith
  calc A ^ (x - 2 ^ d) * Q ^ t * (2 ^ P) ^ x = A ^ (x - 2 ^ d) * (Q ^ t * (2 ^ P) ^ x) := by ring
    _ ≤ A ^ (((x - 2 ^ d : ℕ) : ℝ)) * A ^ (s / 2 * t) := by
        rw [Real.rpow_natCast]; gcongr; exact h1.trans h2
    _ = A ^ (((x - 2 ^ d : ℕ) : ℝ) + s / 2 * t) := (Real.rpow_add hA0 _ _).symm
    _ ≤ A ^ (-(s / 2) + ((t - 2 ^ d : ℕ) : ℝ)) := Real.rpow_le_rpow_of_exponent_le hA hexp
    _ = A ^ (-(s / 2)) * A ^ (t - 2 ^ d) := by rw [Real.rpow_add hA0, Real.rpow_natCast]

open Classical in
/-- **The contraction of the linear part**, with input field scale `ℓ`, output field scale `ℓ'`
and covariance field scale `ℓ_C`, `ℓ' + ℓ_C ≤ 2ℓ`. -/
theorem Llin2_bound_ts (d : ℕ) (hd : 2 ≤ d) : ∃ (C₀ η : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧ 0 < η ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓC C →
    ∀ K : Act d L N, InK2 j K → ∀ U : Finset (Lam d L N), IsConn (j + 1) U →
      wnorm (j + 1) ℓ' A U (Llin2 j C K U) ≤
        ENNReal.ofReal (C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3 + A ^ (-η))) * Knorm j ℓ A K := by
  obtain ⟨Cl, hCl0, Ll, hloc⟩ := loc2s_contract d hd
  obtain ⟨cs, hcs⟩ := card_small_clo_le d
  obtain ⟨η, hη0, hη1, hcomb⟩ := comb1 d
  set s := min (2 * η / (1 + 2 * η)) (1 / (2 ^ d + 1)) with hsdef
  have hs0 : 0 < s := lt_min (by positivity) (by positivity)
  refine ⟨cs * Cl + 1, s / 2, max (max Ll (2 ^ (d + 3) + 8 * d + 1)) ⌈pauliL0 d⌉₊,
    by positivity, by positivity, ?_⟩
  intro L _ hL
  have hLl : Ll ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hL8 : 2 ^ (d + 3) + 8 * d < L :=
    lt_of_lt_of_le (Nat.lt_succ_self _) (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL)
  have hLp : pauliL0 d ≤ L := (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hL)
  have hd1 : 1 ≤ d := by omega
  set M := (2 ^ (d + 1) + 3) ^ d
  set Q : ℝ := pq d ^ M
  have hQ : 1 ≤ Q := one_le_pow₀ (one_le_pq hd1)
  set P : ℝ := ((L ^ d : ℕ) : ℝ)
  have hP : 0 ≤ P := Nat.cast_nonneg _
  set A₁ : ℝ := ((2 ^ P * Q) ^ 2) ^ (1 / s)
  refine ⟨max 1 A₁, le_max_left _ _, ?_⟩
  intro A hA
  have hA1 : 1 ≤ A := le_trans (le_max_left _ _) hA
  have hA0 : 0 < A := by linarith
  have hAQ : (2 ^ P * Q) ^ 2 ≤ A ^ s := by
    have h0 : 0 ≤ (2 ^ P * Q) ^ 2 := by positivity
    calc (2 ^ P * Q) ^ 2 = A₁ ^ s := by
          rw [← Real.rpow_mul h0, one_div_mul_cancel hs0.ne', Real.rpow_one]
      _ ≤ A ^ s := Real.rpow_le_rpow (by positivity) (le_trans (le_max_right _ _) hA) hs0.le
  intro N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC K hK U hU
  have hj : j < N := by omega
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set k := Knorm j ℓ A K
  rw [Llin2_eq j C K hjN U]
  refine (wnorm_add_le' _ _ _ _ _ _).trans ?_
  -- the small sets
  have hS : wnorm (j + 1) ℓ' A U (∑ X ∈ (Pj j univ).filter (fun X => IsSmall j X ∧ clo j X = U),
      EthE C (K X - Loc2E X X (K X))) ≤
        ENNReal.ofReal (cs * Cl * ((L : ℝ) ^ d / (L : ℝ) ^ 3)) * k := by
    by_cases hUs : IsSmall (j + 1) U
    · have hw : A ^ (nb (j + 1) U - 2 ^ d) = 1 := by
        have h0 : nb (j + 1) U - 2 ^ d = 0 := Nat.sub_eq_zero_of_le hUs.2.2
        rw [h0, pow_zero]
      unfold wnorm
      rw [hw, ENNReal.ofReal_one, one_mul, AddSubmonoidClass.coe_finsetSum]
      refine (tNorm_sum_le _ _).trans ?_
      have hcard : ((Pj j univ).filter (fun X => IsSmall j X ∧ clo j X = U)).card ≤ cs * L ^ d := by
        refine le_trans (card_le_card fun X hX => ?_) (hcs L N j U hUs)
        obtain ⟨-, hs, hcl⟩ := mem_filter.1 hX
        exact mem_filter.2 ⟨mem_smallSets.2 hs, hcl⟩
      have hterm : ∀ X ∈ (Pj j univ).filter (fun X => IsSmall j X ∧ clo j X = U),
          Tj d (L : ℝ) (j + 1) ℓ' (EthE C (K X - Loc2E X X (K X)) : Alg d L N) ≤
            ENNReal.ofReal (Cl / (L : ℝ) ^ 3) * k := by
        intro X hX
        obtain ⟨-, hs, -⟩ := mem_filter.1 hX
        have hc : IsConn j X := ⟨hs.1, hs.2.1⟩
        rw [coe_EthE, ← ECC_theta]
        refine (EthE_succ_le2' hℓ' hℓC hsum hC _).trans ?_
        have := hloc L hL8 hLl N j hj ℓ (2 * ℓ) hℓ (by positivity) le_rfl X hs (K X)
          (hK.loc X hc) (hK.sym X hc)
        refine le_trans (le_of_eq ?_) (this.trans (mul_le_mul_left' (Tj_le_Knorm hA1 hc) _))
        rfl
      calc ∑ X ∈ (Pj j univ).filter (fun X => IsSmall j X ∧ clo j X = U),
            Tj d (L : ℝ) (j + 1) ℓ' (EthE C (K X - Loc2E X X (K X)) : Alg d L N)
          ≤ ∑ _X ∈ (Pj j univ).filter (fun X => IsSmall j X ∧ clo j X = U),
              ENNReal.ofReal (Cl / (L : ℝ) ^ 3) * k := sum_le_sum hterm
        _ ≤ ((cs * L ^ d : ℕ) : ENNReal) * (ENNReal.ofReal (Cl / (L : ℝ) ^ 3) * k) := by
            rw [sum_const, nsmul_eq_mul]; gcongr
        _ = ENNReal.ofReal (cs * Cl * ((L : ℝ) ^ d / (L : ℝ) ^ 3)) * k := by
            rw [← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
            congr 2
            simp only [Nat.cast_mul, Nat.cast_pow]
            ring
    · have he : (Pj j univ).filter (fun X => IsSmall j X ∧ clo j X = U) = ∅ := by
        refine filter_eq_empty_iff.2 fun X _ h => hUs ?_
        rw [← h.2]; exact isSmall_clo h.1
      rw [he, sum_empty]
      unfold wnorm
      rw [ZeroMemClass.coe_zero, Step.Tj_zero (d := d) (L : ℝ) (j + 1) ℓ', mul_zero]
      exact zero_le
  -- the large sets
  have hB : wnorm (j + 1) ℓ' A U (∑ X ∈ (Pj j univ).filter
      (fun X => IsConn j X ∧ ¬ IsSmall j X ∧ clo j X = U), EthE C (K X)) ≤
        ENNReal.ofReal (A ^ (-(s / 2))) * k := by
    refine wsum_le hU.1 (Real.rpow_nonneg hA0.le _) k _ _
      (fun X hX => ⟨(mem_Pj.1 (mem_filter.1 hX).1).2, (mem_filter.1 hX).2.2.2⟩) ?_
    intro X hX
    obtain ⟨-, hc, hns, hcl⟩ := mem_filter.1 hX
    set x := nb (j + 1) U
    set t := nb j X
    have ht : 2 ^ d < t := by
      by_contra h; push Not at h; exact hns ⟨hc.1, hc.2, h⟩
    have h2d : 2 ^ d ≤ 2 ^ (d + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hcb := hcomb L (by omega) N j X hj hc hns
    rw [hcl] at hcb
    -- Pauli
    have hE : Tj d (L : ℝ) (j + 1) ℓ' (EthE C (K X) : Alg d L N) ≤
        ENNReal.ofReal (Q ^ t) * Tj d (L : ℝ) j ℓ (K X : Alg d L N) := by
      rw [coe_EthE, ← ECC_theta]
      refine (EthE_succ_le2 hd1 hLp hj hℓ' hℓC hsum hC (hK.loc X hc)).trans (mul_le_mul_left ?_ _)
      refine ENNReal.ofReal_le_ofReal ?_
      rw [show Q ^ t = pq d ^ (M * t) by simp only [Q, ← pow_mul]]
      exact pow_le_pow_right₀ (one_le_pq hd1) (nb_nbhd_le hj.le X)
    have hKX : ENNReal.ofReal (A ^ (t - 2 ^ d)) * Tj d (L : ℝ) j ℓ (K X : Alg d L N) ≤ k :=
      wnorm_le_Knorm hc
    have hreal := large_real (x := x) (t := t) hA1 hη0 hQ hcb ht hAQ hP
    have hpos : (0 : ℝ) < A ^ (t - 2 ^ d) := by positivity
    have h2 : (2 : ℝ) ^ (L ^ d * x) = (2 ^ P) ^ x := by
      rw [← Real.rpow_natCast (2 : ℝ) (L ^ d * x), ← Real.rpow_natCast ((2 : ℝ) ^ P) x,
        ← Real.rpow_mul (by norm_num)]
      congr 1; push_cast [P]; ring
    calc ENNReal.ofReal (A ^ (x - 2 ^ d)) * Tj d (L : ℝ) (j + 1) ℓ' (EthE C (K X) : Alg d L N)
        ≤ ENNReal.ofReal (A ^ (x - 2 ^ d)) * (ENNReal.ofReal (Q ^ t) *
            Tj d (L : ℝ) j ℓ (K X : Alg d L N)) := by gcongr
      _ = ENNReal.ofReal (A ^ (x - 2 ^ d) * Q ^ t / A ^ (t - 2 ^ d)) *
            (ENNReal.ofReal (A ^ (t - 2 ^ d)) * Tj d (L : ℝ) j ℓ (K X : Alg d L N)) := by
          rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity), div_mul_cancel₀ _ hpos.ne']
      _ ≤ ENNReal.ofReal (A ^ (-(s / 2)) / 2 ^ (L ^ d * x)) * k := by
          refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) hKX
          rw [h2, div_le_div_iff₀ hpos (by positivity)]
          calc A ^ (x - 2 ^ d) * Q ^ t * (2 ^ P) ^ x ≤ A ^ (-(s / 2)) * A ^ (t - 2 ^ d) := hreal
            _ = _ := rfl
  refine (add_le_add hS hB).trans ?_
  rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  gcongr
  have hLd : (0 : ℝ) ≤ (L : ℝ) ^ d / (L : ℝ) ^ 3 := by positivity
  have hAs : 0 ≤ A ^ (-(s / 2)) := by positivity
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ cs * Cl by positivity) hAs, hLd]


/-- **The contraction of the linear part** at a single field scale. -/
theorem Llin2_bound (d : ℕ) (hd : 2 ≤ d) : ∃ (C₀ η : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧ 0 < η ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ : ℝ, 0 < ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓ C →
    ∀ K : Act d L N, InK2 j K → ∀ U : Finset (Lam d L N), IsConn (j + 1) U →
      wnorm (j + 1) ℓ A U (Llin2 j C K U) ≤
        ENNReal.ofReal (C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3 + A ^ (-η))) * Knorm j ℓ A K := by
  obtain ⟨C₀, η, L₀, hC₀, hη, h⟩ := Llin2_bound_ts d hd
  refine ⟨C₀, η, L₀, hC₀, hη, fun L _ hL => ?_⟩
  obtain ⟨A₀, hA₀, h'⟩ := h L hL
  exact ⟨A₀, hA₀, fun A hA N j hj ℓ hℓ C hC =>
    h' A hA N j hj ℓ ℓ ℓ hℓ hℓ hℓ (by linarith) C hC⟩

end

end Step2
