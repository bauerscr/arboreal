import Step2.Map.Fact
import Step2.Map.Reapp

/-!
# Output regulator `λA`

Versions of `Llin2_bound`, `Knext2_crude`, `step2` and `step3` (with input field scale `ℓ`, output
field scale `ℓ'` and covariance field scale `ℓ_C`, `ℓ' + ℓ_C ≤ 2ℓ`) in which the output is measured
with the large-set regulator `λA` (`λ ≥ 1` fixed) while the input is measured with `A`. The
slack in Lemma `lem:comb1` absorbs `λ^{|𝓑_{j+1}(U)|}` for `A ≥ A₀(L, λ)`. The reapportionment
(Brydges–Slade Map 4) loses a factor in the regulator, which this compensates
(Brydges–Slade: `a_out < a_in` in Proposition 4.1).
-/

namespace Step2

noncomputable section

open Finset Grassmann Loc FRD Step

variable {d L N : ℕ} [NeZero L]

open Classical in
/-- **The contraction of the linear part**, with output regulator `λA`. -/
theorem Llin2_boundL (d : ℕ) (hd : 2 ≤ d) : ∃ (C₀ η : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧ 0 < η ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∀ lam : ℝ, 1 ≤ lam → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓC C →
    ∀ K : Act d L N, InK2 j K → ∀ U : Finset (Lam d L N), IsConn (j + 1) U →
      wnorm (j + 1) ℓ' (lam * A) U (Llin2 j C K U) ≤
        ENNReal.ofReal (C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3 + A ^ (-η))) * Knorm j ℓ A K := by
  obtain ⟨Cl, hCl0, Ll, hloc⟩ := loc2s_contract d hd
  obtain ⟨cs, hcs⟩ := card_small_clo_le d
  obtain ⟨η, hη0, hη1, hcomb⟩ := comb1 d
  set s := min (2 * η / (1 + 2 * η)) (1 / (2 ^ d + 1)) with hsdef
  have hs0 : 0 < s := lt_min (by positivity) (by positivity)
  refine ⟨cs * Cl + 1, s / 2, max (max Ll (2 ^ (d + 3) + 8 * d + 1)) ⌈pauliL0 d⌉₊,
    by positivity, by positivity, ?_⟩
  intro L _ hL lam hlam
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
  intro N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC K hK U hU
  have hj : j < N := by omega
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set k := Knorm j ℓ A K
  rw [Llin2_eq j C K hjN U]
  refine (wnorm_add_le' _ _ _ _ _ _).trans ?_
  -- the small sets
  have hS : wnorm (j + 1) ℓ' (lam * A) U (∑ X ∈ (Pj j univ).filter (fun X => IsSmall j X ∧ clo j X = U),
      EthE C (K X - Loc2E X X (K X))) ≤
        ENNReal.ofReal (cs * Cl * ((L : ℝ) ^ d / (L : ℝ) ^ 3)) * k := by
    by_cases hUs : IsSmall (j + 1) U
    · have hw : (lam * A) ^ (nb (j + 1) U - 2 ^ d) = 1 := by
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
  have hB : wnorm (j + 1) ℓ' (lam * A) U (∑ X ∈ (Pj j univ).filter
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
    have hreal := large_real (x := x) (t := t) hA1 hη0 hlQ hcb ht hAQ hP
    have hxt : x ≤ t := by
      have : (x : ℝ) ≤ t := by nlinarith [Nat.cast_nonneg (α := ℝ) x]
      exact_mod_cast this
    have hlam : (lam * A) ^ (x - 2 ^ d) * Q ^ t ≤ A ^ (x - 2 ^ d) * (lam * Q) ^ t := by
      rw [mul_pow, mul_pow]
      have : lam ^ (x - 2 ^ d) ≤ lam ^ t := pow_le_pow_right₀ hlam ((Nat.sub_le _ _).trans hxt)
      have h0 : 0 ≤ A ^ (x - 2 ^ d) * Q ^ t := by positivity
      nlinarith
    have hpos : (0 : ℝ) < A ^ (t - 2 ^ d) := by positivity
    have h2 : (2 : ℝ) ^ (L ^ d * x) = (2 ^ P) ^ x := by
      rw [← Real.rpow_natCast (2 : ℝ) (L ^ d * x), ← Real.rpow_natCast ((2 : ℝ) ^ P) x,
        ← Real.rpow_mul (by norm_num)]
      congr 1; push_cast [P]; ring
    calc ENNReal.ofReal ((lam * A) ^ (x - 2 ^ d)) * Tj d (L : ℝ) (j + 1) ℓ' (EthE C (K X) : Alg d L N)
        ≤ ENNReal.ofReal ((lam * A) ^ (x - 2 ^ d)) * (ENNReal.ofReal (Q ^ t) *
            Tj d (L : ℝ) j ℓ (K X : Alg d L N)) := by gcongr
      _ = ENNReal.ofReal ((lam * A) ^ (x - 2 ^ d) * Q ^ t / A ^ (t - 2 ^ d)) *
            (ENNReal.ofReal (A ^ (t - 2 ^ d)) * Tj d (L : ℝ) j ℓ (K X : Alg d L N)) := by
          rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity), div_mul_cancel₀ _ hpos.ne']
      _ ≤ ENNReal.ofReal (A ^ (-(s / 2)) / 2 ^ (L ^ d * x)) * k := by
          refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) hKX
          rw [h2, div_le_div_iff₀ hpos (by positivity)]
          calc (lam * A) ^ (x - 2 ^ d) * Q ^ t * (2 ^ P) ^ x
              ≤ A ^ (x - 2 ^ d) * (lam * Q) ^ t * (2 ^ P) ^ x := by gcongr
            _ ≤ A ^ (-(s / 2)) * A ^ (t - 2 ^ d) := hreal
  refine (add_le_add hS hB).trans ?_
  rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  gcongr
  have hLd : (0 : ℝ) ≤ (L : ℝ) ^ d / (L : ℝ) ^ 3 := by positivity
  have hAs : 0 ≤ A ^ (-(s / 2)) := by positivity
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ cs * Cl by positivity) hAs, hLd]


set_option maxHeartbeats 4000000 in
/-- **The crude bound** with output regulator `λA`. -/
theorem Knext2_crudeL (d : ℕ) (hd : 1 ≤ d) : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∀ lam : ℝ, 1 ≤ lam → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∃ r₀ : ℝ, 0 < r₀ ∧
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓC C →
    ∀ (V W : Fam d L N) (K : Act d L N), InF j V → InF j W → (∀ b, ε (V b : Alg d L N) = 0) →
      InK2 j K → Fnorm j ℓ V ≤ ENNReal.ofReal r₀ → Fnorm j ℓ W ≤ ENNReal.ofReal r₀ →
      Knorm j ℓ A K ≤ ENNReal.ofReal r₀ →
      ∀ U : Finset (Lam d L N), IsConn (j + 1) U →
        wnorm (j + 1) ℓ' (lam * A) U (Knext2 j C V W K U) ≤ ENNReal.ofReal 1 := by
  classical
  obtain ⟨Cl, hCl0, hloc⟩ := exists_Loc2sXY_bound d hd
  obtain ⟨c, hc⟩ := card_small_containing d
  obtain ⟨η, hη0, -, hcomb⟩ := comb2 d
  refine ⟨max (2 ^ (d + 3) + 8 * d + 1) ⌈pauliL0 d⌉₊, ?_⟩
  intro L _ hL lam hlam
  have hL8 : 2 ^ (d + 3) + 8 * d < L := lt_of_lt_of_le (Nat.lt_succ_self _) (le_trans (le_max_left _ _) hL)
  have hLp : pauliL0 d ≤ L := (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hL)
  have hd8 : 2 ^ (d + 3) = 2 ^ d * 8 := by ring
  have hd4 : 2 ^ (d + 2) = 2 ^ d * 4 := by ring
  have hL2 : 2 ^ (d + 2) ≤ L := by
    rw [hd8] at hL8; rw [hd4]; generalize 2 ^ d = t at hL8 ⊢; omega
  have hL1 : 2 ^ d + 1 ≤ L := by
    rw [hd8] at hL8; generalize 2 ^ d = t at hL8 ⊢; omega
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set Q := Q1 d with hQdef
  have hQ : 1 ≤ Q := one_le_Q1 hd
  have hQ0 : 0 < Q := by linarith
  set M : ℕ := 2 ^ ((1 + c) * L ^ d) with hMdef
  have hM1 : 1 ≤ M := Nat.one_le_two_pow
  have hM1' : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  set Qw : ℝ := lam * Q with hQw
  have hQw1 : 1 ≤ Qw := by rw [hQw]; nlinarith
  set P : ℝ := Qw * (2 * M) with hPdef
  have hP1 : 1 ≤ P := by rw [hPdef]; nlinarith
  have hη' : 0 < 2 * η / (1 + 2 * η) := by positivity
  set A₀ : ℝ := Q * max 1 ((4 * P) ^ ((1 + 2 * η) / (2 * η))) with hA₀
  have hA₀1 : 1 ≤ A₀ := by
    rw [hA₀]; nlinarith [le_max_left (1 : ℝ) ((4 * P) ^ ((1 + 2 * η) / (2 * η)))]
  refine ⟨A₀, hA₀1, ?_⟩
  intro A hA
  have hA1 : 1 ≤ A := hA₀1.trans hA
  have hA0 : 0 < A := by linarith
  set Ar : ℝ := A / Q with hArdef
  have hArQ : Ar * Qw = lam * A := by rw [hArdef, hQw]; field_simp
  have hArQ1 : Ar * Q = A := by rw [hArdef]; field_simp
  have hAr : max 1 ((4 * P) ^ ((1 + 2 * η) / (2 * η))) ≤ Ar := by
    rw [hArdef, le_div_iff₀ hQ0, mul_comm]; exact hA
  have hAr1 : 1 ≤ Ar := (le_max_left _ _).trans hAr
  have hAP : 4 * P ≤ Ar ^ (2 * η / (1 + 2 * η)) := by
    calc 4 * P = ((4 * P) ^ ((1 + 2 * η) / (2 * η))) ^ (2 * η / (1 + 2 * η)) := by
          rw [← Real.rpow_mul (by positivity)]
          rw [show (1 + 2 * η) / (2 * η) * (2 * η / (1 + 2 * η)) = 1 by field_simp]
          rw [Real.rpow_one]
      _ ≤ Ar ^ (2 * η / (1 + 2 * η)) :=
          Real.rpow_le_rpow (by positivity) ((le_max_right _ _).trans hAr) hη'.le
  set cS : ℝ := c + 1 with hcSdef
  have hcS1 : 1 ≤ cS := by rw [hcSdef]; linarith [Nat.cast_nonneg (α := ℝ) c]
  set cJ : ℝ := Q * cS * Cl with hcJdef
  have hcJ : 0 ≤ cJ := by positivity
  set cu := cUblk d L Cl cS
  set cw := cWblk d L Cl
  set ci := cIblk d L Cl cS
  have hcu : 0 ≤ cu := by
    have := Nat.cast_nonneg (α := ℝ) ((L + 2 ^ (d + 3) + 7) ^ d)
    simp only [cu, cUblk, cSblk, cNear]; positivity
  have hcw : 0 ≤ cw := by
    have := Nat.cast_nonneg (α := ℝ) ((L + 2 ^ (d + 3) + 7) ^ d)
    simp only [cw, cWblk, cSblk, cNear]; positivity
  have hci : 0 ≤ ci := by simp only [ci, cIblk]; positivity
  set Bc : ℝ := (1 + 2 ^ d * cJ) * A ^ 2 ^ d + (5 * Q + ci) * Ar with hBc
  have hBc0 : 0 ≤ Bc := by positivity
  set D : ℝ := 1 + 4 * cu + cw + 2 * (cu + ci) * (L : ℝ) ^ d + A ^ 2 ^ d + (5 * Q + ci) * Ar +
    (Ar * P) ^ 2 ^ d * Bc with hD
  have hD0 : 0 < D := by positivity
  refine ⟨1 / D, by positivity, ?_⟩
  intro N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC V W K hV hW hV0 hK hVr hWr hKr U hU
  set r := 1 / D with hrdef
  have hr0 : 0 ≤ r := by positivity
  have hrle : r ≤ 1 / D := le_rfl
  have item : ∀ x : ℝ, 0 ≤ x → x ≤ D → x * r ≤ 1 := fun x hx hxD =>
    le_one_of_le_div hx hD0 hrle hxD
  have t1 : 0 ≤ 4 * cu := by positivity
  have t2 : 0 ≤ 2 * (cu + ci) * (L : ℝ) ^ d := by positivity
  have t3 : 0 ≤ A ^ 2 ^ d := by positivity
  have t4 : 0 ≤ (5 * Q + ci) * Ar := by positivity
  have t5 : 0 ≤ (Ar * P) ^ 2 ^ d * Bc := by positivity
  have hr1 : r ≤ 1 := by
    simpa using item 1 zero_le_one (by rw [hD]; linarith)
  have hj : j < N := by omega
  have H : BH j ℓ ℓ' ℓC C V W K A r Cl cS :=
    { hd := hd, hLp := hLp, hL8 := hL8, hjN := hjN, hℓ := hℓ, hℓ' := hℓ', hℓC := hℓC, hsum := hsum, hC := hC, hV := hV, hW := hW,
      hV0 := hV0, hK := hK, hA := hA1, hr := hr0, hr1 := hr1
      hVr := fun b hb => (le_iSup₂ (f := fun b (_ : b ∈ blockIdx (L := L) (N := N) j) =>
        Tj d (L : ℝ) j ℓ (V b : Alg d L N)) b hb).trans hVr
      hWr := fun b hb => (le_iSup₂ (f := fun b (_ : b ∈ blockIdx (L := L) (N := N) j) =>
        Tj d (L : ℝ) j ℓ (W b : Alg d L N)) b hb).trans hWr
      hKr := hKr, hCl := hCl0
      hloc := fun k hk ℓ₀ hℓ₀ X Y hX hYX F hF => hloc L hL8 N k hk X Y hX hYX F hF ℓ₀ hℓ₀
      hcS := hcS1
      hcount := fun b hb => by
        have h1 : ((smallSets (d := d) (L := L) (N := N) j).filter
            (fun X => blockSet j b ⊆ X)).card ≤ c := by convert hc L N j b hb
        have h2 := Nat.cast_le (α := ℝ) |>.2 h1
        linarith }
  have hu : cu * r ≤ 1 / 4 := by
    have := item (4 * cu) (by positivity) (by rw [hD]; linarith)
    linarith
  have hw : cw * r ≤ 1 := item cw hcw (by rw [hD]; linarith)
  have hpr : (cu + ci) * r * (L : ℝ) ^ d ≤ 1 / 2 := by
    have := item (2 * (cu + ci) * (L : ℝ) ^ d) (by positivity) (by rw [hD]; linarith)
    nlinarith
  have hκ1 : r * A ^ 2 ^ d ≤ 1 := by
    have := item (A ^ 2 ^ d) t3 (by rw [hD]; linarith)
    linarith [mul_comm r (A ^ 2 ^ d)]
  have hδ1 : (5 * Q + ci) * r * Ar ≤ 1 := by
    have := item ((5 * Q + ci) * Ar) t4 (by rw [hD]; linarith)
    have e : (5 * Q + ci) * r * Ar = (5 * Q + ci) * Ar * r := by ring
    linarith
  have hDβ : (Ar * P) ^ 2 ^ d * ((1 + 2 ^ d * cJ) * (r * A ^ 2 ^ d) + (5 * Q + ci) * r * Ar) ≤ 1 := by
    have e : (Ar * P) ^ 2 ^ d * ((1 + 2 ^ d * cJ) * (r * A ^ 2 ^ d) + (5 * Q + ci) * r * Ar) =
        ((Ar * P) ^ 2 ^ d * Bc) * r := by rw [hBc]; ring
    rw [e]; exact item _ (by positivity) (by rw [hD]; linarith)
  have hρ : Q / A = Ar⁻¹ := by rw [hArdef, inv_div]
  have G : GH j (Ib V W) (Ip j C V W K) K (J2 j K) ((L : ℝ) ^ (j + 1)) ℓ' ℓC (Q / A)
      (r * A ^ 2 ^ d) ((5 * Q + ci) * r * Ar) cJ :=
    { hh' := H.hh', hℓ' := hℓ', hρ := by positivity
      hρ1 := by rw [div_le_one hA0]; exact (le_mul_of_one_le_left hQ0.le hAr1).trans hArQ1.le
      hκ₀ := by positivity, hκ₀1 := hκ1, hδ₁ := by positivity, hδ₁1 := hδ1, hcJ := hcJ
      hK := fun W hW => H.thetaK_le hW
      hdI := fun b hb => (H.gdI_le hu hw hb).trans (ENNReal.ofReal_le_ofReal (le_of_eq (by
        rw [hArdef]; field_simp; show _ = r * (5 * Q1 d + cIblk d L Cl cS); ring)))
      hJ := fun b hb X => (H.thetaJ_le hb X).trans (ENNReal.ofReal_le_ofReal (by
        have e : cJ * (r * A ^ 2 ^ d) * (Q / A) ^ 2 ^ d = Q * (cS * (Cl * r)) * Q ^ 2 ^ d := by
          rw [hcJdef, div_pow]; field_simp
        rw [e]
        have : 1 ≤ Q ^ 2 ^ d := one_le_pow₀ hQ
        have : 0 ≤ Q * (cS * (Cl * r)) := by positivity
        nlinarith))
      hJs := fun b X hX => J2_of_not_small j K b X hX }
  have hUj : IsPolymer j U := IsPolymer.of_succ hU.1
  have key := G.gKnext_le C (Complex.exp (uX j C V W K U)) hAr1 hρ hQw1 hη0.le
    (fun F => ECC_succ_le2 hℓ' hℓC hC F)
    (fun g _ => by
      refine (H.pref_le hu hw U _).trans (ENNReal.ofReal_le_ofReal ?_)
      have hnb : (nb j U : ℝ) ≤ (L : ℝ) ^ d * nb (j + 1) U := by
        exact_mod_cast nb_le_of_succ hU.1
      have hx : (cu + ci) * r * nb j U ≤ (nb (j + 1) U : ℝ) * (1 / 2) := by
        have : (cu + ci) * r * nb j U ≤ (cu + ci) * r * ((L : ℝ) ^ d * nb (j + 1) U) := by
          gcongr
        nlinarith [mul_le_mul_of_nonneg_right hpr (Nat.cast_nonneg (α := ℝ) (nb (j + 1) U))]
      have he : Real.exp (1 / 2) ≤ 2 := by
        have := (abs_le.1 (Real.abs_exp_sub_one_le (x := 1 / 2) (by norm_num))).2
        norm_num at this ⊢; linarith
      calc Real.exp ((cu + ci) * r * nb j U) ≤ Real.exp ((nb (j + 1) U : ℝ) * (1 / 2)) :=
            Real.exp_le_exp.2 hx
        _ = Real.exp (1 / 2) ^ nb (j + 1) U := Real.exp_nat_mul _ _
        _ ≤ 2 ^ nb (j + 1) U := pow_le_pow_left₀ (Real.exp_pos _).le he _)
    (by
      refine (card_Gset_le (fun b hb => hc L N j b hb) hUj).trans ?_
      rw [hMdef, ← pow_mul]
      exact Nat.pow_le_pow_right (by norm_num) (by
        rw [mul_assoc]; exact Nat.mul_le_mul_left _ (nb_le_of_succ hU.1)))
    (fun g hg => nU_bound (fun X hX => (hcomb L hL1 N j X hj hX).1)
      (fun b hb => (isSmall_clo_nbhd hd hL2 hj b hb).2.2) hη0.le hg)
    hPdef hM1 hAP hDβ
  rw [hArQ] at key
  refine le_trans ?_ key
  unfold wnorm
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (pow_le_pow_right₀ (by nlinarith) (Nat.sub_le _ _)))
    le_rfl


set_option maxHeartbeats 1000000 in
/-- **Theorem `step2`** with output regulator `λA`. -/
theorem step2L (d : ℕ) (hd : 2 ≤ d) : ∃ (C₀ η : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧ 0 < η ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∀ lam : ℝ, 1 ≤ lam → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓC C →
    ∀ (V W : Fam d L N) (K : Act d L N), InF j V → InF j W → (∀ b, ε (V b : Alg d L N) = 0) →
      InK2 j K → ∀ g : ℝ, 0 ≤ g → g ≤ ε₀ →
      Fnorm j ℓ V ≤ ENNReal.ofReal g → Fnorm j ℓ W ≤ ENNReal.ofReal (g ^ 2) →
      Knorm j ℓ A K ≤ ENNReal.ofReal ε₀ →
      ∀ U : Finset (Lam d L N), IsConn (j + 1) U →
        wnorm (j + 1) ℓ' (lam * A) U (Knext2 j C V W K U - K2 j C V U) ≤
          ENNReal.ofReal (C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3 + A ^ (-η))) * Knorm j ℓ A K +
          ENNReal.ofReal C₁ * (ENNReal.ofReal (g ^ 3) + ENNReal.ofReal g * Knorm j ℓ A K +
            Knorm j ℓ A K ^ 2) := by
  obtain ⟨C₀, η, Ll, hC₀, hη, hLl⟩ := Llin2_boundL d hd
  obtain ⟨Lc, hLc⟩ := Knext2_crudeL d (by omega)
  refine ⟨C₀, η, max Ll Lc, hC₀, hη, ?_⟩
  intro L _ hL lam hlam
  obtain ⟨A₁, hA₁, hA₁'⟩ := hLl L (le_trans (le_max_left _ _) hL) lam hlam
  obtain ⟨A₂, hA₂, hA₂'⟩ := hLc L (le_trans (le_max_right _ _) hL) lam hlam
  refine ⟨max A₁ A₂, le_trans hA₁ (le_max_left _ _), ?_⟩
  intro A hA
  have hA1 : 1 ≤ A := le_trans hA₁ (le_trans (le_max_left _ _) hA)
  have hA0 : 0 < A := by linarith
  have hlA0 : 0 < lam * A := by nlinarith
  obtain ⟨r₀, hr₀, hcr⟩ := hA₂' A (le_trans (le_max_right _ _) hA)
  set ρ := min r₀ 1 with hρdef
  have hρ0 : 0 < ρ := lt_min hr₀ one_pos
  have hρ1 : ρ ≤ 1 := min_le_right _ _
  have hρr : ρ ≤ r₀ := min_le_left _ _
  refine ⟨ρ, 4 / ρ ^ 3, hρ0, by positivity, ?_⟩
  intro N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC V W K hV hW hV0 hK g hg0 hgρ hVg hWg hKρ U hU
  have hUne : U.Nonempty := hU.2.1
  set k := (Knorm j ℓ A K).toReal with hkdef
  have hKfin : Knorm j ℓ A K ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hKρ
  have hKk : Knorm j ℓ A K = ENNReal.ofReal k := (ENNReal.ofReal_toReal hKfin).symm
  have hk0 : 0 ≤ k := ENNReal.toReal_nonneg
  have hkρ : k ≤ ρ := by
    rw [hKk] at hKρ; exact (ENNReal.ofReal_le_ofReal_iff hρ0.le).1 hKρ
  -- the two-parameter family
  set F : ℂ → ℂ → EvR (Lam d L N) := fun t s => Knext2 j C (Vt V t) (Wt W t) (s • K) U with hF
  have hVt0 : ∀ t b, ε (Vt V t b : Alg d L N) = 0 := fun t b => by
    rw [Vt, Subalgebra.coe_smul, map_smul, hV0, smul_zero]
  -- holomorphy
  have hVf : ∀ b, HolE (fun t : ℂ => Vt V t b) := fun b =>
    HolE.smul differentiable_id (HolE.const _)
  have hWf : ∀ b, HolE (fun t : ℂ => Wt W t b) := fun b =>
    HolE.smul (differentiable_id.pow 2) (HolE.const _)
  have hF1 : ∀ s, HolE (fun t => F t s) := fun s =>
    Knext2_hol (E := ℂ) j C hVf hWf (Kf := fun _ => s • K) (fun X => HolE.const _) hVt0 U
  have hF2 : ∀ t, HolE (fun s => F t s) := fun t =>
    Knext2_hol (E := ℂ) j C (Vf := fun _ => Vt V t) (Wf := fun _ => Wt W t) (Kf := fun s => s • K)
      (fun b => HolE.const _) (fun b => HolE.const _)
      (fun X => HolE.smul differentiable_id (HolE.const _)) (fun _ b => hVt0 t b) U
  -- the crude bound on the polydisc
  have hball : ∀ R₁ : ℝ, 1 ≤ R₁ → R₁ * g ≤ ρ → ∀ R₂ : ℝ, 1 ≤ R₂ → R₂ * k ≤ ρ →
      ∀ t s : ℂ, ‖t‖ ≤ R₁ → ‖s‖ ≤ R₂ → wnorm (j + 1) ℓ' (lam * A) U (F t s) ≤ ENNReal.ofReal 1 := by
    intro R₁ hR₁ hR₁g R₂ hR₂ hR₂k t s ht hs
    have h1 : Fnorm j ℓ (Vt V t) ≤ ENNReal.ofReal r₀ := by
      show Fnorm j ℓ (fun b => t • V b) ≤ _
      rw [Fnorm_smul]
      calc ENNReal.ofReal ‖t‖ * Fnorm j ℓ V ≤ ENNReal.ofReal R₁ * ENNReal.ofReal g := by
            gcongr
        _ = ENNReal.ofReal (R₁ * g) := (ENNReal.ofReal_mul (by linarith)).symm
        _ ≤ ENNReal.ofReal r₀ := ENNReal.ofReal_le_ofReal (hR₁g.trans hρr)
    have h2 : Fnorm j ℓ (Wt W t) ≤ ENNReal.ofReal r₀ := by
      show Fnorm j ℓ (fun b => t ^ 2 • W b) ≤ _
      rw [Fnorm_smul, norm_pow]
      have hRg : (R₁ * g) ^ 2 ≤ ρ := by
        have : 0 ≤ R₁ * g := by positivity
        nlinarith
      calc ENNReal.ofReal (‖t‖ ^ 2) * Fnorm j ℓ W ≤ ENNReal.ofReal (R₁ ^ 2) *
            ENNReal.ofReal (g ^ 2) := by gcongr
        _ = ENNReal.ofReal ((R₁ * g) ^ 2) := by
            rw [← ENNReal.ofReal_mul (by positivity)]; ring_nf
        _ ≤ ENNReal.ofReal r₀ := ENNReal.ofReal_le_ofReal (hRg.trans hρr)
    have h3 : Knorm j ℓ A (s • K) ≤ ENNReal.ofReal r₀ := by
      rw [Knorm_smul, hKk]
      calc ENNReal.ofReal ‖s‖ * ENNReal.ofReal k ≤ ENNReal.ofReal R₂ * ENNReal.ofReal k := by
            gcongr
        _ = ENNReal.ofReal (R₂ * k) := (ENNReal.ofReal_mul (by linarith)).symm
        _ ≤ ENNReal.ofReal r₀ := ENNReal.ofReal_le_ofReal (hR₂k.trans hρr)
    exact hcr N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC (Vt V t) (Wt W t) (s • K) (hV.smul t) (hW.smul (t ^ 2))
      (hVt0 t) (hK.smul s) h1 h2 h3 U hU
  -- the weighted pairings
  have hw : 0 ≤ wt (j + 1) (lam * A) U := pow_nonneg hlA0.le _
  have hrem : wnorm (j + 1) ℓ' (lam * A) U (Knext2 j C V W K U - K2 j C V U - Llin2 j C K U) ≤
      ENNReal.ofReal (4 / ρ ^ 3 * (g ^ 3 + g * k + k ^ 2)) := by
    refine wnorm_le_of_wpair hlA0 U _ fun g' hg' => ?_
    set Λw := wpairL (wt (j + 1) (lam * A) U) g' with hΛw
    have hB : ∀ R₁ : ℝ, 1 ≤ R₁ → R₁ * g ≤ ρ → ∀ R₂ : ℝ, 1 ≤ R₂ → R₂ * k ≤ ρ →
        ∀ t s : ℂ, ‖t‖ ≤ R₁ → ‖s‖ ≤ R₂ → ‖Λw (F t s : Alg d L N)‖ ≤ 1 := by
      intro R₁ hR₁ hR₁g R₂ hR₂ hR₂k t s ht hs
      rw [hΛw, norm_wpairL hw]
      refine (wpair_le_wnorm hℓ' hlA0.le U _ hg').trans ?_
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (hball R₁ hR₁ hR₁g R₂ hR₂ hR₂k t s ht hs)
    have hR0g : (1 : ℝ) * g ≤ ρ := by linarith
    have hR0k : (1 : ℝ) * k ≤ ρ := by linarith
    -- `F(0,0) = 0`
    have hF00 : F 0 0 = 0 := by
      have h := Knext2_lin j C (K := K) hUne
      obtain ⟨q, -, e⟩ := h
      have := e 0
      simp only [zero_smul, zero_add, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow] at this
      simp only [hF, Vt_zero, Wt_zero, zero_smul]
      exact this
    -- the mixed term
    have X1 : ‖Λw (F 1 1 : Alg d L N) - Λw (F 1 0 : Alg d L N) - Λw (F 0 1 : Alg d L N) +
        Λw (F 0 0 : Alg d L N)‖ ≤ 4 * (g / ρ) * (k / ρ) := by
      refine rad2 (by norm_num) hρ0 hg0 hgρ hk0 hkρ fun R₁ hR₁ hR₁g R₂ hR₂ hR₂k => ?_
      have := mixed_le hF1 hF2 Λw hR₁ hR₂ (B := 1) (hB R₁ hR₁ hR₁g R₂ hR₂ hR₂k)
      simpa using this
    -- the third-order remainder at `K = 0`
    have X2 : ‖Λw (F 1 0 : Alg d L N) - Λw (K2 j C V U : Alg d L N)‖ ≤ 2 * (g / ρ) ^ 3 := by
      have hexp := Knext2_expansion j C (V := V) (W := W) hV0 hUne
      have hexp' : ExpE2 (fun t => F t 0) 0 0 (K2 j C V U) := by
        refine OrdE.congr hexp fun t => ?_
        simp only [hF, zero_smul]
      refine rad1 (n := 3) (by norm_num) (by norm_num) hρ0 hg0 hgρ fun R hR hRg => ?_
      have := rem3_le hexp' Λw hR (B := 1) fun ζ hζ =>
        hB R hR hRg 1 le_rfl hR0k ζ 0 hζ.le (by simp)
      simpa using this
    -- the second-order remainder at `V = 𝒲 = 0`
    have X3 : ‖Λw (F 0 1 : Alg d L N) - Λw (Llin2 j C K U : Alg d L N)‖ ≤ 2 * (k / ρ) ^ 2 := by
      have hlin := Knext2_lin j C (K := K) hUne
      have hlin' : ExpE1 (fun s => F 0 s) 0 (Llin2 j C K U) := by
        refine ExpE1.congr hlin fun s => ?_
        simp only [hF, Vt_zero, Wt_zero]
      refine rad1 (n := 2) (by norm_num) (by norm_num) hρ0 hk0 hkρ fun R hR hRk => ?_
      have := rem2_le hlin' Λw hR (B := 1) fun ζ hζ =>
        hB 1 le_rfl hR0g R hR hRk 0 ζ (by simp) hζ.le
      simpa using this
    have e11 : F 1 1 = Knext2 j C V W K U := by simp only [hF, Vt_one, Wt_one, one_smul]
    have hsplit : Λw ((Knext2 j C V W K U - K2 j C V U - Llin2 j C K U : EvR (Lam d L N)) :
        Alg d L N) = (Λw (F 1 1 : Alg d L N) - Λw (F 1 0 : Alg d L N) -
          Λw (F 0 1 : Alg d L N) + Λw (F 0 0 : Alg d L N)) +
        (Λw (F 1 0 : Alg d L N) - Λw (K2 j C V U : Alg d L N)) +
        (Λw (F 0 1 : Alg d L N) - Λw (Llin2 j C K U : Alg d L N)) := by
      rw [hF00, e11]
      simp only [AddSubgroupClass.coe_sub, map_sub, ZeroMemClass.coe_zero, map_zero]
      ring
    rw [← norm_wpairL hw, ← hΛw, hsplit]
    refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
    have hρ3 : 0 < ρ ^ 3 := by positivity
    have hgk : g / ρ * (k / ρ) ≤ g * k / ρ ^ 3 := by
      rw [div_mul_div_comm, ← sq]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (by nlinarith [pow_le_pow_of_le_one hρ0.le hρ1 (show 2 ≤ 3 by norm_num)])
    have hkk : (k / ρ) ^ 2 ≤ k ^ 2 / ρ ^ 3 := by
      rw [div_pow]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_of_le_one hρ0.le hρ1 (by norm_num))
    have hg3 : (g / ρ) ^ 3 = g ^ 3 / ρ ^ 3 := div_pow _ _ _
    have : 4 / ρ ^ 3 * (g ^ 3 + g * k + k ^ 2) =
        4 * (g ^ 3 / ρ ^ 3) + 4 * (g * k / ρ ^ 3) + 4 * (k ^ 2 / ρ ^ 3) := by ring
    rw [this]
    nlinarith [X1, X2, X3, show 0 ≤ g ^ 3 / ρ ^ 3 by positivity,
      show 0 ≤ k ^ 2 / ρ ^ 3 by positivity]
  -- assemble
  have hdec : Knext2 j C V W K U - K2 j C V U =
      Llin2 j C K U + (Knext2 j C V W K U - K2 j C V U - Llin2 j C K U) := by abel
  rw [hdec]
  refine (wnorm_add_le' _ _ _ _ _ _).trans (add_le_add
    (hA₁' A (le_trans (le_max_left _ _) hA) N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC K hK U hU) (hrem.trans (le_of_eq ?_)))
  rw [hKk, ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hg0,
    ← ENNReal.ofReal_pow hk0, ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]



set_option maxHeartbeats 1000000 in
/-- **Theorem `step3`** with output regulator `λA`. -/
theorem step3L (d : ℕ) (hd : 2 ≤ d) : ∃ (C₀ η : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧ 0 < η ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∀ lam : ℝ, 1 ≤ lam → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓC C →
    ∀ (V W : Fam d L N) (K : Act d L N), InF j V → InF j W → (∀ b, ε (V b : Alg d L N) = 0) →
      InK2 j K → ∀ g : ℝ, 0 ≤ g → g ≤ ε₀ →
      Fnorm j ℓ V ≤ ENNReal.ofReal g → Fnorm j ℓ W ≤ ENNReal.ofReal (g ^ 2) →
      Knorm j ℓ A K ≤ ENNReal.ofReal ε₀ →
      ∀ U : Finset (Lam d L N), IsConn (j + 1) U →
        wnorm (j + 1) ℓ' (lam * A) U (Knew j C V W K U) ≤
          ENNReal.ofReal (C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3 + A ^ (-η))) * Knorm j ℓ A K +
          ENNReal.ofReal C₁ * (ENNReal.ofReal (g ^ 3) + ENNReal.ofReal g * Knorm j ℓ A K +
            Knorm j ℓ A K ^ 2) := by
  classical
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C₀, η, L₂, hC₀, hη, h2⟩ := step2L d hd
  obtain ⟨Cl, hCl0, hloc⟩ := exists_Loc2sXY_bound d hd1
  obtain ⟨c, hc⟩ := card_small_containing d
  refine ⟨C₀, η, max L₂ (max (2 ^ (d + 3) + 8 * d + 1) ⌈pauliL0 d⌉₊), hC₀, hη, ?_⟩
  intro L _ hL lam hlam
  have hL2 : L₂ ≤ L := le_trans (le_max_left _ _) hL
  have hL8 : 2 ^ (d + 3) + 8 * d < L :=
    lt_of_lt_of_le (Nat.lt_succ_self _) (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL)
  have hLp : pauliL0 d ≤ L := (Nat.le_ceil _).trans
    (by exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL)
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  obtain ⟨A₀, hA₀, h2'⟩ := h2 L hL2 lam hlam
  refine ⟨A₀, hA₀, fun A hA => ?_⟩
  have hA1 : 1 ≤ A := hA₀.trans hA
  have hA0 : 0 < A := by linarith
  obtain ⟨ε₂, C₂, hε₂, hC₂, h2''⟩ := h2' A hA
  set cS : ℝ := c + 1 with hcSdef
  have hcS1 : 1 ≤ cS := by rw [hcSdef]; linarith [Nat.cast_nonneg (α := ℝ) c]
  set cu := cUblk d L Cl cS
  set cw := cWblk d L Cl
  have hcu : 0 ≤ cu := by
    have := Nat.cast_nonneg (α := ℝ) ((L + 2 ^ (d + 3) + 7) ^ d)
    have := one_le_Q1 hd1
    simp only [cu, cUblk, cSblk, cNear]; positivity
  have hcw : 0 ≤ cw := by
    have := Nat.cast_nonneg (α := ℝ) ((L + 2 ^ (d + 3) + 7) ^ d)
    have := one_le_Q1 hd1
    simp only [cw, cWblk, cSblk, cNear]; positivity
  set δc : ℝ := 8 * cu + cw with hδc
  have hδc0 : 0 ≤ δc := by positivity
  set n₀ : ℝ := 2 * (L : ℝ) ^ d with hn₀
  have hn₀0 : 0 ≤ n₀ := by positivity
  set Ck : ℝ := (cNear d L + 2) * (2 * Q1 d ^ 2) with hCk
  have hCk0 : 0 ≤ Ck := by
    have := Nat.cast_nonneg (α := ℝ) ((L + 2 ^ (d + 3) + 7) ^ d)
    rw [hCk]; unfold cNear; positivity
  set Cs : ℝ := 2 * n₀ * δc * (2 : ℝ) ^ (2 * L ^ d) * Ck with hCs
  have hCs0 : 0 ≤ Cs := by positivity
  set ε₀ : ℝ := min ε₂ (min 1 (min (1 / (4 * cu + 1)) (min (1 / (cw + 1)) (1 / (n₀ * δc + 1)))))
    with hε₀
  have hε₀0 : 0 < ε₀ := lt_min hε₂ (lt_min one_pos (lt_min (by positivity)
    (lt_min (by positivity) (by positivity))))
  refine ⟨ε₀, C₂ + Cs, hε₀0, by positivity, ?_⟩
  intro N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC V W K hV hW hV0 hK g hg0 hgε hVg hWg hKε U hU
  have e1 : ε₀ ≤ ε₂ := min_le_left _ _
  have e2 : ε₀ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have e3 : ε₀ ≤ 1 / (4 * cu + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have e4 : ε₀ ≤ 1 / (cw + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have e5 : ε₀ ≤ 1 / (n₀ * δc + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_right _ _)))
  -- the step2 bound
  have hS2 := h2'' N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC V W K hV hW hV0 hK g hg0 (hgε.trans e1) hVg hWg
    (hKε.trans (ENNReal.ofReal_le_ofReal e1)) U hU
  -- the radius
  set k := (Knorm j ℓ A K).toReal with hkdef
  have hKfin : Knorm j ℓ A K ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hKε
  have hKk : Knorm j ℓ A K = ENNReal.ofReal k := (ENNReal.ofReal_toReal hKfin).symm
  have hk0 : 0 ≤ k := ENNReal.toReal_nonneg
  have hkε : k ≤ ε₀ := by
    rw [hKk] at hKε; exact (ENNReal.ofReal_le_ofReal_iff hε₀0.le).1 hKε
  set r := max g k with hrdef
  have hr0 : 0 ≤ r := le_max_of_le_left hg0
  have hrε : r ≤ ε₀ := max_le hgε hkε
  have hr1 : r ≤ 1 := hrε.trans e2
  have hg1 : g ≤ 1 := hgε.trans e2
  have hgr : g ≤ r := le_max_left _ _
  have hkr : k ≤ r := le_max_right _ _
  have H : BH j ℓ ℓ' ℓC C V W K A r Cl cS :=
    { hd := hd1, hLp := hLp, hL8 := hL8, hjN := hjN, hℓ := hℓ, hℓ' := hℓ', hℓC := hℓC, hsum := hsum, hC := hC, hV := hV, hW := hW,
      hV0 := hV0, hK := hK, hA := hA1, hr := hr0, hr1 := hr1
      hVr := fun b hb => ((le_iSup₂ (f := fun b (_ : b ∈ blockIdx (L := L) (N := N) j) =>
        Tj d (L : ℝ) j ℓ (V b : Alg d L N)) b hb).trans hVg).trans (ENNReal.ofReal_le_ofReal hgr)
      hWr := fun b hb => ((le_iSup₂ (f := fun b (_ : b ∈ blockIdx (L := L) (N := N) j) =>
        Tj d (L : ℝ) j ℓ (W b : Alg d L N)) b hb).trans hWg).trans (ENNReal.ofReal_le_ofReal
          (by nlinarith))
      hKr := by rw [hKk]; exact ENNReal.ofReal_le_ofReal hkr
      hCl := hCl0
      hloc := fun k hk ℓ₀ hℓ₀ X Y hX hYX F hF => hloc L hL8 N k hk X Y hX hYX F hF ℓ₀ hℓ₀
      hcS := hcS1
      hcount := fun b hb => by
        have h1 : ((smallSets (d := d) (L := L) (N := N) j).filter
            (fun X => blockSet j b ⊆ X)).card ≤ c := by convert hc L N j b hb
        have h2 := Nat.cast_le (α := ℝ) |>.2 h1
        linarith }
  have hu : cu * r ≤ 1 / 4 := by
    have := le_one_of_le_div (x := 4 * cu) (by positivity) (by positivity) (hrε.trans e3)
      (by linarith)
    linarith
  have hw : cw * r ≤ 1 :=
    le_one_of_le_div hcw (by positivity) (hrε.trans e4) (by linarith)
  have hnδ : n₀ * δc * r ≤ 1 :=
    le_one_of_le_div (by positivity) (by positivity) (hrε.trans e5) (by linarith)
  -- the reapportionment term
  have hsplit : Knew j C V W K U = (Knext2 j C V W K U - K2 j C V U) +
      -((bpow j (Gp j C V W K) U - 1) * K2 j C V U) := by rw [Knew]; ring
  have hT : wnorm (j + 1) ℓ' (lam * A) U ((bpow j (Gp j C V W K) U - 1) * K2 j C V U) ≤
      ENNReal.ofReal (Cs * r ^ 3) := by
    by_cases hU2 : 2 < nb (j + 1) U
    · rw [K2_eq_zero j C V hU2, mul_zero]
      unfold wnorm
      rw [ZeroMemClass.coe_zero, Step.Tj_zero (d := d) (L : ℝ) (j + 1) ℓ', mul_zero]
      exact zero_le
    · push Not at hU2
      have hw1 : (lam * A) ^ (nb (j + 1) U - 2 ^ d) = 1 := by
        have : nb (j + 1) U - 2 ^ d = 0 := by
          have : 2 ≤ 2 ^ d := by
            calc 2 = 2 ^ 1 := rfl
              _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd1
          omega
        rw [this, pow_zero]
      unfold wnorm
      rw [hw1, ENNReal.ofReal_one, one_mul]
      have hnbU : (nb j U : ℝ) ≤ n₀ := by
        have := nb_le_of_succ hU.1
        have h' : (nb j U : ℝ) ≤ (L : ℝ) ^ d * nb (j + 1) U := by exact_mod_cast this
        have h'' : (nb (j + 1) U : ℝ) ≤ 2 := by exact_mod_cast hU2
        rw [hn₀]; nlinarith [pow_pos hL0 d]
      -- `‖Ĩ^U - 1‖ ≤ 2 n₀ δc r`
      have hP : Tj d (L : ℝ) (j + 1) ℓ' ((bpow j (Gp j C V W K) U - 1 : EvR (Lam d L N)) :
          Alg d L N) ≤ ENNReal.ofReal (2 * n₀ * δc * r) := by
        refine (tn_prod_sub_one H.hh' hℓ' (blocks j U) _ (by positivity)
          (fun b hb => H.Gp_sub_one_le hu hw (mem_blockIdx_of_mem_blocks hb))).trans
          (ENNReal.ofReal_le_ofReal ?_)
        have hn : ((blocks j U).card : ℝ) ≤ n₀ := hnbU
        have h1 : (1 + δc * r) ^ (blocks j U).card ≤ Real.exp ((blocks j U).card * (δc * r)) := by
          calc (1 + δc * r) ^ (blocks j U).card ≤ Real.exp (δc * r) ^ (blocks j U).card := by
                gcongr; linarith [Real.add_one_le_exp (δc * r)]
            _ = Real.exp ((blocks j U).card * (δc * r)) := (Real.exp_nat_mul _ _).symm
        have hx : ((blocks j U).card : ℝ) * (δc * r) ≤ n₀ * δc * r := by
          have := mul_le_mul_of_nonneg_right hn (by positivity : 0 ≤ δc * r); linarith
        have h2 := exp_sub_one_le (r := ((blocks j U).card : ℝ) * (δc * r))
          (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hδc0 hr0)) (hx.trans hnδ)
        nlinarith
      -- `‖K^{(2)}(U)‖ ≤ 2^{n₀} Ck r²`
      have hK2 : Tj d (L : ℝ) (j + 1) ℓ' (K2 j C V U : Alg d L N) ≤
          ENNReal.ofReal ((2 : ℝ) ^ (2 * L ^ d) * (Ck * r ^ 2)) := by
        unfold K2
        refine (tn_sum_const (E := Dir d) (p := pPhi d) _ _ (r := Ck * r ^ 2) (by positivity)
          fun X _ => (H.k2_le X).trans (ENNReal.ofReal_le_ofReal (le_of_eq (by ring)))).trans
          (ENNReal.ofReal_le_ofReal ?_)
        refine mul_le_mul_of_nonneg_right ((card_K2_filter_le j hU.1).trans ?_) (by positivity)
        have : nb j U ≤ 2 * L ^ d :=
          calc nb j U ≤ L ^ d * nb (j + 1) U := nb_le_of_succ hU.1
            _ ≤ L ^ d * 2 := Nat.mul_le_mul_left _ hU2
            _ = 2 * L ^ d := mul_comm _ _
        calc (2 : ℝ) ^ nb j U ≤ 2 ^ (2 * L ^ d) := pow_le_pow_right₀ (by norm_num) this
          _ = _ := rfl
      refine (tn_mulE H.hh' hℓ' (by positivity) hP hK2).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [hCs]; nlinarith [sq_nonneg r]
  rw [hsplit]
  refine (wnorm_add_le' _ _ _ _ _ _).trans ?_
  rw [wnorm_neg]
  refine (add_le_add hS2 hT).trans ?_
  -- `r³ ≤ g³ + k²`
  have hr3 : r ^ 3 ≤ g ^ 3 + k ^ 2 := by
    rcases le_total g k with h | h
    · have : r = k := max_eq_right h
      rw [this]
      have : k ^ 3 ≤ k ^ 2 := pow_le_pow_of_le_one hk0 (hkr.trans hr1) (by norm_num)
      nlinarith [pow_nonneg hg0 3]
    · have : r = g := max_eq_left h
      rw [this]; nlinarith [sq_nonneg k]
  rw [hKk, add_assoc]
  have hY : ENNReal.ofReal (g ^ 3) + ENNReal.ofReal g * ENNReal.ofReal k + ENNReal.ofReal k ^ 2 =
      ENNReal.ofReal (g ^ 3 + g * k + k ^ 2) := by
    rw [← ENNReal.ofReal_mul hg0, ← ENNReal.ofReal_pow hk0,
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
  rw [hY]
  refine add_le_add le_rfl ?_
  rw [← ENNReal.ofReal_mul hC₂, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have : Cs * r ^ 3 ≤ Cs * (g ^ 3 + g * k + k ^ 2) := by
    have : 0 ≤ g * k := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) hCs0
  nlinarith



end

end Step2
