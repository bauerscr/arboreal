import Step.EstCoupling

/-!
# Large sets (Section `sec:K-largeset`)

The consequences `e:Achoice`, `e:Achoice-conn` of Lemma `lem:comb1`, and
Proposition `prop:LargeSetLin`:
`‖𝓛_{j+1,𝒫∖𝒮}‖_{j+1} = O(A^{-η} ‖K_j‖_j + A^ν (‖V_j‖_j + ‖K_j‖_j)^2)`.

The combinatorial sums are estimated crudely: the number of `X ∈ 𝒫_j` with `X̄ = U` is at
most `2^{L^d |𝓑_{j+1}(U)|}` (`card_clo_eq_le`), and this entropy is absorbed by
`A^{-η |𝓑_{j+1}(U)| / 2^d}` (`e:Achoice`, `largeK_real`) in the `K`-part, and by the smallness
of `‖V‖_j + ‖K‖_j ≤ ε₀(L, A)` in the `δI`-part (`largeD_real`).  We obtain `ν = 1`.
-/

namespace Step

noncomputable section

open Finset Grassmann Loc FRD

/-- The real inequality behind the `K`-part of `prop:LargeSetLin`. -/
theorem largeK_real {d n m P : ℕ} {A η : ℝ} (hA : 1 ≤ A) (hη0 : 0 < η) (hη1 : η ≤ 1 / 4)
    (hcomb : (1 + 2 * η) * (n : ℝ) ≤ m) (hm : 2 ^ d < m) (hmP : m ≤ P * n)
    (hAP : (4 : ℝ) ^ P ≤ A ^ (η / 2 ^ d)) :
    A ^ (n - 2 ^ d) * 2 ^ m * 2 ^ (P * n) ≤ A ^ (-η) * A ^ (m - 2 ^ d) := by
  have hA0 : 0 < A := by linarith
  have h2d : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
  have h1 : (2 : ℝ) ^ m * 2 ^ (P * n) ≤ A ^ (η / 2 ^ d * n) := by
    calc (2 : ℝ) ^ m * 2 ^ (P * n) ≤ 2 ^ (P * n) * 2 ^ (P * n) := by
          gcongr; norm_num
      _ = ((4 : ℝ) ^ P) ^ n := by rw [← pow_mul, ← mul_pow]; norm_num
      _ ≤ (A ^ (η / 2 ^ d)) ^ n := by gcongr
      _ = A ^ (η / 2 ^ d * n) := by rw [← Real.rpow_mul_natCast hA0.le]
  have hexp : ((n - 2 ^ d : ℕ) : ℝ) + η / 2 ^ d * n ≤ -η + ((m - 2 ^ d : ℕ) : ℝ) := by
    have hm' : ((m - 2 ^ d : ℕ) : ℝ) = m - 2 ^ d := by
      rw [Nat.cast_sub hm.le]; push_cast; ring
    rw [hm']
    have hmR : (2 : ℝ) ^ d + 1 ≤ m := by exact_mod_cast hm
    by_cases hn : n ≤ 2 ^ d
    · rw [Nat.sub_eq_zero_of_le hn, Nat.cast_zero, zero_add]
      have hnR : (n : ℝ) ≤ 2 ^ d := by exact_mod_cast hn
      have : η / 2 ^ d * n ≤ η := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        exact mul_le_mul_of_nonneg_left hnR hη0.le
      linarith
    · push Not at hn
      rw [Nat.cast_sub hn.le]; push_cast
      have hn1 : (1 : ℝ) ≤ n := by
        have : 1 ≤ n := le_trans Nat.one_le_two_pow hn.le
        exact_mod_cast this
      have : η / 2 ^ d * n ≤ η * n := by
        gcongr
        exact div_le_self hη0.le h2d
      nlinarith
  calc A ^ (n - 2 ^ d) * 2 ^ m * 2 ^ (P * n) = A ^ (n - 2 ^ d) * (2 ^ m * 2 ^ (P * n)) := by ring
    _ ≤ A ^ (((n - 2 ^ d : ℕ) : ℝ)) * A ^ (η / 2 ^ d * n) := by
      rw [Real.rpow_natCast]; gcongr
    _ = A ^ (((n - 2 ^ d : ℕ) : ℝ) + η / 2 ^ d * n) := (Real.rpow_add hA0 _ _).symm
    _ ≤ A ^ (-η + ((m - 2 ^ d : ℕ) : ℝ)) := Real.rpow_le_rpow_of_exponent_le hA hexp
    _ = A ^ (-η) * A ^ (m - 2 ^ d) := by rw [Real.rpow_add hA0, Real.rpow_natCast]

/-- The real inequality behind the `δI`-part of `prop:LargeSetLin`. -/
theorem largeD_real {d n m P : ℕ} {A q r : ℝ} (hd : 2 ≤ d) (hA : 1 ≤ A) (hq : 0 ≤ q)
    (hr : r = 1 / (A * 2 ^ P)) (hqr : q ≤ r ^ 2) (hm2 : 2 ≤ m) (hnm : n ≤ m)
    (hAP : (2 : ℝ) ^ (P * 2 ^ d) ≤ A) :
    A ^ (n - 2 ^ d) * q ^ m * 2 ^ (P * n) ≤ A * q ^ 2 := by
  have hA0 : 0 < A := by linarith
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr1 : r ≤ 1 := by
    rw [hr, div_le_one (by positivity)]
    exact one_le_mul_of_one_le_of_one_le hA (one_le_pow₀ (by norm_num))
  have hq1 : q ≤ 1 := hqr.trans (pow_le_one₀ hr0.le hr1)
  have hqm : q ^ m = q ^ 2 * q ^ (m - 2) := by rw [← pow_add]; congr 1; omega
  rw [hqm]
  by_cases hn : n ≤ 2 ^ d
  · rw [Nat.sub_eq_zero_of_le hn, pow_zero, one_mul]
    have h1 : q ^ (m - 2) ≤ 1 := pow_le_one₀ hq hq1
    have h2 : (2 : ℝ) ^ (P * n) ≤ A :=
      le_trans (pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left P hn)) hAP
    calc q ^ 2 * q ^ (m - 2) * 2 ^ (P * n) ≤ q ^ 2 * 1 * A := by gcongr
      _ = A * q ^ 2 := by ring
  · push Not at hn
    have h4 : 4 ≤ 2 ^ d := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
    have h1 : q ^ (m - 2) ≤ r ^ n := by
      calc q ^ (m - 2) ≤ (r ^ 2) ^ (m - 2) := by gcongr
        _ = r ^ (2 * (m - 2)) := by rw [← pow_mul]
        _ ≤ r ^ n := pow_le_pow_of_le_one hr0.le hr1 (by omega)
    have h2 : A ^ (n - 2 ^ d) ≤ A ^ n := pow_le_pow_right₀ hA (Nat.sub_le _ _)
    have h3 : A ^ n * r ^ n * 2 ^ (P * n) = 1 := by
      rw [pow_mul, ← mul_pow, ← mul_pow, hr]
      rw [show A * (1 / (A * 2 ^ P)) * 2 ^ P = 1 by field_simp, one_pow]
    calc A ^ (n - 2 ^ d) * (q ^ 2 * q ^ (m - 2)) * 2 ^ (P * n)
        ≤ A ^ n * (q ^ 2 * r ^ n) * 2 ^ (P * n) := by gcongr
      _ = q ^ 2 * (A ^ n * r ^ n * 2 ^ (P * n)) := by ring
      _ = q ^ 2 := by rw [h3, mul_one]
      _ ≤ A * q ^ 2 := le_mul_of_one_le_left (by positivity) hA

theorem sum_le_card_mul_ennreal {ι : Type*} (s : Finset ι) (f : ι → ENNReal) (c : ENNReal)
    (M : ℕ) (hs : s.card ≤ M) (hf : ∀ i ∈ s, f i ≤ c) : ∑ i ∈ s, f i ≤ (M : ENNReal) * c := by
  refine (sum_le_card_nsmul s f c hf).trans ?_
  rw [nsmul_eq_mul]; gcongr

section

variable {d L N : ℕ} [NeZero L]

/-- Summing a bound over `X ∈ 𝒫_j` with `X̄ = U`, using `card_clo_eq_le`. -/
theorem wsum_le {j : ℕ} {U : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U) {h ℓ w c : ℝ}
    (_hc : 0 ≤ c) (Z : ENNReal) (s : Finset (Finset (Lam d L N))) (F : Finset (Lam d L N) → EvR (Lam d L N))
    (hs : ∀ X ∈ s, IsPolymer j X ∧ clo j X = U)
    (hF : ∀ X ∈ s, ENNReal.ofReal w * tNorm (Dir d) (pPhi d) h ℓ (F X : Alg d L N) ≤
      ENNReal.ofReal (c / 2 ^ (L ^ d * nb (j + 1) U)) * Z) :
    ENNReal.ofReal w * tNorm (Dir d) (pPhi d) h ℓ ((∑ X ∈ s, F X : EvR (Lam d L N)) : Alg d L N) ≤
      ENNReal.ofReal c * Z := by
  set M : ℕ := 2 ^ (L ^ d * nb (j + 1) U)
  have hcard : s.card ≤ M := by
    refine le_trans (card_le_card ?_) (card_clo_eq_le hU)
    intro X hX
    exact mem_filter.2 ⟨mem_Pj.2 ⟨subset_univ _, (hs X hX).1⟩, (hs X hX).2⟩
  rw [AddSubmonoidClass.coe_finsetSum]
  calc ENNReal.ofReal w * tNorm (Dir d) (pPhi d) h ℓ (∑ X ∈ s, (F X : Alg d L N))
      ≤ ENNReal.ofReal w * ∑ X ∈ s, tNorm (Dir d) (pPhi d) h ℓ (F X : Alg d L N) := by
        gcongr; exact tNorm_sum_le _ _
    _ = ∑ X ∈ s, ENNReal.ofReal w * tNorm (Dir d) (pPhi d) h ℓ (F X : Alg d L N) := mul_sum _ _ _
    _ ≤ (M : ENNReal) * (ENNReal.ofReal (c / 2 ^ (L ^ d * nb (j + 1) U)) * Z) :=
        sum_le_card_mul_ennreal _ _ _ _ hcard hF
    _ = ENNReal.ofReal c * Z := by
        rw [← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 2
        have : (0 : ℝ) < M := by positivity
        simp only [M, Nat.cast_pow, Nat.cast_ofNat] at this ⊢
        field_simp

end

/-- **Proposition `prop:LargeSetLin`.** Here `η` and `ν` depend only on `d`. -/
theorem largeset_bound {d : ℕ} (hd : 3 ≤ d) : ∃ (C₀ η ν : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧ 0 < η ∧ 0 < ν ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ (N j : ℕ), j < N → ∀ (ℓ₀ : ℝ), 0 < ℓ₀ →
    ∀ (C : Matrix (Lam d L N) (Lam d L N) ℝ), GoodCov j ℓ₀ C →
    ∀ (V : Vcoup) (K : Act d L N), InK j K →
      Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V + Knorm j (ellj d L ℓ₀ j) A K ≤
        ENNReal.ofReal ε₀ →
      ∀ U : Finset (Lam d L N), IsConn (j + 1) U →
        wnorm (j + 1) (ellj d L ℓ₀ (j + 1)) A U (LlinL j C V K U) ≤
          ENNReal.ofReal (C₀ * A ^ (-η)) * Knorm j (ellj d L ℓ₀ j) A K +
            ENNReal.ofReal (C₀ * A ^ ν) *
              (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V +
                Knorm j (ellj d L ℓ₀ j) A K) ^ 2 := by
  obtain ⟨c₀, Lp, hc₀, hLp, hpert⟩ := pert12 hd
  obtain ⟨C₁, ε₁, Ld, hC₁, hε₁, -, hdI⟩ := dI_bounds hd
  obtain ⟨η, hη0, hη1, hcomb⟩ := comb1 d
  refine ⟨1 + 4 * C₁ ^ 2, η, 1, max Lp Ld, by positivity, hη0, one_pos, ?_⟩
  intro L _ hL
  have hLp' : Lp ≤ L := le_trans (le_max_left _ _) hL
  have hLd' : Ld ≤ L := le_trans (le_max_right _ _) hL
  have hL4 : (4 : ℝ) ≤ L := four_le_of_L₀ (hLp.trans hLp')
  have hL0 : (0 : ℝ) < L := by linarith
  have hL2d : 2 ^ d + 1 ≤ L := by
    have : 2 ^ d ≤ 2 ^ (d + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  set P : ℕ := L ^ d with hP
  set A₁ : ℝ := (4 : ℝ) ^ ((P : ℝ) * 2 ^ d / η) with hA₁
  refine ⟨max 1 A₁, le_max_left _ _, ?_⟩
  intro A hA
  have hA1 : 1 ≤ A := le_trans (le_max_left _ _) hA
  have hA0 : 0 < A := by linarith
  have hAA₁ : A₁ ≤ A := le_trans (le_max_right _ _) hA
  have hA₁0 : 0 ≤ A₁ := by positivity
  have h2d : (0 : ℝ) < 2 ^ d := by positivity
  have hAP1 : (4 : ℝ) ^ P ≤ A ^ (η / 2 ^ d) := by
    calc (4 : ℝ) ^ P = A₁ ^ (η / 2 ^ d) := by
          rw [hA₁, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast]
          congr 1
          field_simp
      _ ≤ A ^ (η / 2 ^ d) := Real.rpow_le_rpow hA₁0 hAA₁ (by positivity)
  have hAP2 : (2 : ℝ) ^ (P * 2 ^ d) ≤ A := by
    calc (2 : ℝ) ^ (P * 2 ^ d) ≤ 4 ^ (P * 2 ^ d) := by gcongr; norm_num
      _ = (4 : ℝ) ^ ((P : ℝ) * 2 ^ d) := by rw [← Real.rpow_natCast]; push_cast; rfl
      _ ≤ A₁ := by
          rw [hA₁]
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          exact le_div_self (by positivity) hη0 (by linarith)
      _ ≤ A := hAA₁
  set r : ℝ := 1 / (A * 2 ^ P) with hr
  have hr0 : 0 < r := by positivity
  set ε₀ : ℝ := min ε₁ (min (c₀ / (L : ℝ) ^ d) (r ^ 2 / (2 * C₁ + 1))) with hε₀
  have hε₀0 : 0 < ε₀ := lt_min hε₁ (lt_min (by positivity) (by positivity))
  refine ⟨ε₀, hε₀0, ?_⟩
  intro N j hj ℓ₀ hℓ₀ C hC V K hK hvk U hU
  classical
  set ℓ := ellj d L ℓ₀ j
  set ℓ' := ellj d L ℓ₀ (j + 1)
  set v := Vnorm (d := d) (L := L) (N := N) j ℓ V
  set k := Knorm j ℓ A K
  set n := nb (j + 1) U
  have hh : (0 : ℝ) < (L : ℝ) ^ (j + 1) := by positivity
  have hℓ' : 0 < ℓ' := ellj_pos hL0 hℓ₀ _
  have hvk1 : v + k ≤ ENNReal.ofReal ε₁ := hvk.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _))
  have hvk2 : v + k ≤ ENNReal.ofReal (c₀ / (L : ℝ) ^ d) :=
    hvk.trans (ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans (min_le_left _ _)))
  have hvkt : v + k ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvk
  set sr := (v + k).toReal with hsr
  have hs : v + k = ENNReal.ofReal sr := (ENNReal.ofReal_toReal hvkt).symm
  have hsr0 : 0 ≤ sr := ENNReal.toReal_nonneg
  have hsrε : sr ≤ ε₀ := ENNReal.toReal_le_of_le_ofReal hε₀0.le hvk
  have hq : 2 * C₁ * sr ≤ r ^ 2 := by
    have h1 : sr ≤ r ^ 2 / (2 * C₁ + 1) := hsrε.trans ((min_le_right _ _).trans (min_le_right _ _))
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  have hpert' := hpert L hLp' N j hj ℓ₀ hℓ₀ C hC V K A hA1 hK hvk2
  have hdI' := hdI L hLd' N j hj ℓ₀ hℓ₀ C hC V K A hA1 hK hvk1
  -- the two parts
  have key : ∀ s1 s2 : Finset (Finset (Lam d L N)),
      (∀ X ∈ s1, X ∉ smallSets j ∧ IsConn j X ∧ clo j X = U) →
      (∀ X ∈ s2, X ∉ smallSets j ∧ IsPolymer j X ∧ clo j X = U) →
      ENNReal.ofReal (A ^ (n - 2 ^ d)) * Tj d (L : ℝ) (j + 1) ℓ'
        (((∑ X ∈ s1, pref j C V K U X *
            ECE C (thetaE (K X) - ∑ b ∈ blocks j X, thetaE (Jb j K b X))) +
          ∑ X ∈ s2, pref j C V K U X * ECE C (dIPow j C V K X) : EvR (Lam d L N)) :
            Alg d L N) ≤
        ENNReal.ofReal ((1 + 4 * C₁ ^ 2) * A ^ (-η)) * k +
          ENNReal.ofReal ((1 + 4 * C₁ ^ 2) * A ^ (1 : ℝ)) * (v + k) ^ 2 := by
    intro s1 s2 h1 h2
    -- the `K`-part
    have hK1 : ENNReal.ofReal (A ^ (n - 2 ^ d)) * Tj d (L : ℝ) (j + 1) ℓ'
        ((∑ X ∈ s1, pref j C V K U X *
            ECE C (thetaE (K X) - ∑ b ∈ blocks j X, thetaE (Jb j K b X)) : EvR (Lam d L N)) :
          Alg d L N) ≤ ENNReal.ofReal (A ^ (-η)) * k := by
      refine wsum_le hU.1 (Real.rpow_nonneg hA0.le _) k s1 _ (fun X hX => ⟨(h1 X hX).2.1.1, (h1 X hX).2.2⟩) ?_
      intro X hX'
      obtain ⟨hns, hX, hXU⟩ := h1 X hX'
      have hns' : ¬ IsSmall j X := fun h => hns (mem_filter.2 ⟨mem_univ _, h⟩)
      have hJ : ∑ b ∈ blocks j X, thetaE (Jb j K b X) = 0 :=
        sum_eq_zero fun b _ => by simp [Jb, hns']
      rw [hJ, sub_zero]
      have hm : 2 ^ d < nb j X := by
        by_contra h; push Not at h; exact hns' ⟨hX.1, hX.2, h⟩
      have hc := hcomb L hL2d N j X hj hX hns'
      rw [hXU] at hc
      have hmP : nb j X ≤ P * n :=
        (card_le_card (image_subset_image (hXU ▸ subset_clo j X))).trans (nb_le_of_succ hU.1)
      have hT : Tj d (L : ℝ) (j + 1) ℓ'
          ((pref j C V K U X * ECE C (thetaE (K X)) : EvR (Lam d L N)) : Alg d L N) ≤
          2 ^ nb j X * Tj d (L : ℝ) j ℓ (K X : Alg d L N) :=
        (tNorm_mul_le' hh hℓ' _ _).trans (mul_le_mul' (hpert' X U hX.1 hXU)
          (Tj_EC_theta_le hd hL4 hℓ₀ j hC.psd hC.norm _))
      have hKX : ENNReal.ofReal (A ^ (nb j X - 2 ^ d)) * Tj d (L : ℝ) j ℓ (K X : Alg d L N) ≤ k :=
        wnorm_le_Knorm hX
      have hreal := largeK_real hA1 hη0 hη1 hc hm hmP hAP1
      have hpos : (0 : ℝ) < A ^ (nb j X - 2 ^ d) := by positivity
      have e : ENNReal.ofReal (A ^ (n - 2 ^ d) * 2 ^ nb j X / A ^ (nb j X - 2 ^ d)) *
          ENNReal.ofReal (A ^ (nb j X - 2 ^ d)) = ENNReal.ofReal (A ^ (n - 2 ^ d)) * 2 ^ nb j X := by
        rw [← ENNReal.ofReal_mul (div_nonneg (mul_nonneg (pow_nonneg hA0.le _) (by positivity))
            hpos.le), div_mul_cancel₀ _ hpos.ne',
          ENNReal.ofReal_mul (p := A ^ (n - 2 ^ d)) (pow_nonneg hA0.le _),
          ENNReal.ofReal_pow (p := (2 : ℝ)) (by norm_num), ENNReal.ofReal_ofNat]
      calc ENNReal.ofReal (A ^ (n - 2 ^ d)) * Tj d (L : ℝ) (j + 1) ℓ'
            ((pref j C V K U X * ECE C (thetaE (K X)) : EvR (Lam d L N)) : Alg d L N)
          ≤ ENNReal.ofReal (A ^ (n - 2 ^ d)) *
              (2 ^ nb j X * Tj d (L : ℝ) j ℓ (K X : Alg d L N)) := by gcongr
        _ = ENNReal.ofReal (A ^ (n - 2 ^ d) * 2 ^ nb j X / A ^ (nb j X - 2 ^ d)) *
              (ENNReal.ofReal (A ^ (nb j X - 2 ^ d)) * Tj d (L : ℝ) j ℓ (K X : Alg d L N)) := by
            rw [← mul_assoc, ← mul_assoc, e]
        _ ≤ ENNReal.ofReal (A ^ (-η) / 2 ^ (L ^ d * n)) * k := by
            refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) hKX
            rw [div_le_div_iff₀ hpos (by positivity)]
            linarith
    -- the `δI`-part
    have hK2 : ENNReal.ofReal (A ^ (n - 2 ^ d)) * Tj d (L : ℝ) (j + 1) ℓ'
        ((∑ X ∈ s2, pref j C V K U X * ECE C (dIPow j C V K X) : EvR (Lam d L N)) :
          Alg d L N) ≤ ENNReal.ofReal (A * (2 * C₁ * sr) ^ 2) * 1 := by
      refine wsum_le hU.1 (mul_nonneg hA0.le (sq_nonneg _)) 1 s2 _ (fun X hX => ⟨(h2 X hX).2.1, (h2 X hX).2.2⟩) ?_
      intro X hX'
      obtain ⟨hns, hX, hXU⟩ := h2 X hX'
      have hns' : ¬ IsSmall j X := fun h => hns (mem_filter.2 ⟨mem_univ _, h⟩)
      have hnm : n ≤ nb j X := by have := nb_clo_le j X; rw [hXU] at this; exact this
      have hm2 : 2 ≤ nb j X := by
        have hne : X ≠ ∅ := by
          rintro rfl
          rw [clo_empty] at hXU
          obtain ⟨x, hx⟩ := hU.2.1
          rw [← hXU] at hx
          exact notMem_empty x hx
        by_cases hc' : IsConnected j X
        · have : 2 ^ d < nb j X := by
            by_contra h; push Not at h; exact hns' ⟨hX, hc', h⟩
          have : 2 ≤ 2 ^ d := by
            calc 2 = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        · have h0 := (comp_card_eq_zero_iff hX).not.2 hne
          have h1' := (comp_card_eq_one_iff hX).not.2 (fun h => hc' h.2)
          have := card_comp_le (j := j) (X := X)
          omega
      have hT : Tj d (L : ℝ) (j + 1) ℓ'
          ((pref j C V K U X * ECE C (dIPow j C V K X) : EvR (Lam d L N)) : Alg d L N) ≤
          2 ^ nb j X * (ENNReal.ofReal C₁ * ENNReal.ofReal sr) ^ nb j X := by
        refine (tNorm_mul_le' hh hℓ' _ _).trans (mul_le_mul' (hpert' X U hX hXU) ?_)
        refine (tNorm_EC_le hh hℓ' hC.psd hC.norm _).trans ((tNorm_prod_le hh hℓ' _ _).trans ?_)
        refine (prod_le_prod' fun b hb => ?_).trans (by rw [prod_const]; rfl)
        rw [← hs]
        exact (hdI' b (mem_blockIdx_of_mem_blocks hb)).1
      have hreal := largeD_real (d := d) (n := n) (m := nb j X) (P := P) (by omega) hA1
        (by positivity) hr hq hm2 hnm hAP2
      calc ENNReal.ofReal (A ^ (n - 2 ^ d)) * Tj d (L : ℝ) (j + 1) ℓ'
            ((pref j C V K U X * ECE C (dIPow j C V K X) : EvR (Lam d L N)) : Alg d L N)
          ≤ ENNReal.ofReal (A ^ (n - 2 ^ d)) *
              (2 ^ nb j X * (ENNReal.ofReal C₁ * ENNReal.ofReal sr) ^ nb j X) := by gcongr
        _ = ENNReal.ofReal (A ^ (n - 2 ^ d) * (2 * C₁ * sr) ^ nb j X) := by
            rw [ENNReal.ofReal_mul (p := A ^ (n - 2 ^ d)) (pow_nonneg hA0.le _),
              ENNReal.ofReal_pow (p := 2 * C₁ * sr) (by positivity),
              ENNReal.ofReal_mul (p := 2 * C₁) (by positivity),
              ENNReal.ofReal_mul (p := 2) (by norm_num), ENNReal.ofReal_ofNat]
            ring
        _ ≤ ENNReal.ofReal (A * (2 * C₁ * sr) ^ 2 / 2 ^ (L ^ d * n)) * 1 := by
            rw [mul_one]
            refine ENNReal.ofReal_le_ofReal ?_
            rw [le_div_iff₀ (by positivity)]
            exact hreal
    calc _ ≤ ENNReal.ofReal (A ^ (n - 2 ^ d)) * (Tj d (L : ℝ) (j + 1) ℓ'
            ((∑ X ∈ s1, pref j C V K U X *
              ECE C (thetaE (K X) - ∑ b ∈ blocks j X, thetaE (Jb j K b X)) : EvR (Lam d L N)) :
                Alg d L N) +
          Tj d (L : ℝ) (j + 1) ℓ'
            ((∑ X ∈ s2, pref j C V K U X * ECE C (dIPow j C V K X) : EvR (Lam d L N)) :
              Alg d L N)) := by
          gcongr; exact tNorm_add_le _ _
      _ ≤ ENNReal.ofReal (A ^ (-η)) * k + ENNReal.ofReal (A * (2 * C₁ * sr) ^ 2) * 1 := by
          rw [mul_add]; exact add_le_add hK1 hK2
      _ ≤ _ := by
          refine add_le_add (mul_le_mul' (ENNReal.ofReal_le_ofReal
            (le_mul_of_one_le_left (Real.rpow_nonneg hA0.le _) (by nlinarith))) le_rfl) ?_
          · rw [mul_one, hs, ← ENNReal.ofReal_pow hsr0, ← ENNReal.ofReal_mul (by positivity)]
            refine ENNReal.ofReal_le_ofReal ?_
            rw [Real.rpow_one]
            nlinarith [sq_nonneg sr, sq_nonneg C₁]
  unfold wnorm LlinL Lsum
  refine key _ _ ?_ ?_
  · intro X hX
    obtain ⟨h1, h2, h3⟩ := mem_filter.1 hX
    exact ⟨(mem_sdiff.1 h1).2, h2, h3⟩
  · intro X hX
    obtain ⟨h1, h2, h3⟩ := mem_filter.1 hX
    exact ⟨(mem_sdiff.1 h1).2, h2, h3⟩

end

end Step
