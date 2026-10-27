import Obs.StepObsLargeProd
import Obs.StepObsLargeReal

/-!
# The large set contribution of `π_obs 𝓛_{j+1}` (`e:Kquad-obs`)

`obs_largeset_bound_proof'` proves `LargeObsStmt'` (`Obs.StepObsFix`): the bound on
`π_obs (𝓛_{j+1,𝒫∖𝒮}(U) - 𝓛_{pair}(U))`, following the text below `e:Kquad-obs`
(Section `sec:tyler-renorm-group`):

* the `K`-part `∑_{X ∈ 𝒞_j ∖ 𝒮_j, X̄ = U} e^{u(U)} e^{-(u+V)(U∖X)} 𝔼 θ K(X)`: by
  `e:norm-obs-nonmon`, `π_obs (P F) = P π_obs F + π_obs P F_∅`, where `‖P‖ ≤ 2^{|𝓑_j(X)|}`,
  `‖π_obs P‖ ≤ ‖P - 1‖ = O(‖V‖ + ‖K‖) 4^{|𝓑_j(X)|}` and `‖𝔼 θ π_obs K(X)‖_{j+1} ≤ L^{2(d-2)}
  ‖π_obs K(X)‖_j` (`e:Tphi-obs-ub`); the sum over `X` is as in Section `sec:K-largeset`
  (`comb1`, `card_clo_eq_le`), giving `O(A^{-η} ‖K^obs‖) + O(‖V‖ + ‖K‖) ‖K^∅‖`;
* the `δI`-part `∑_{X ∈ 𝒫_j ∖ 𝒮_j, X̄ = U, X ∉ pairs} …`: at most two blocks of `X`
  (those containing `a` or `b`) carry an observable part of `δI`
  (`n1_πobs_ECO_dIPow_le`); if `|𝓑_j(X)| ≥ 3` or only one block carries an observable
  part, a bulk factor `O(‖V^∅‖ + ‖K^∅‖)` remains; the remaining case is `X = B_a ∪ B_b`
  with `B_a, B_b` in distinct `(j+1)`-blocks (the pairs in one `(j+1)`-block are in
  `𝓛_pair`), where `C(a, b) = 0` (`SepHyp`) and `e:deltaI-obs-4`
  (`n1_ECO_πobs_dIo_mul_le`) applies.

The constants: `η` from `comb1`, `ν = 1`, `m = 9 d`.
-/

namespace Obs

noncomputable section

open Finset Grassmann SA Loc Step LocObs Gen

variable {d L N : ℕ} [NeZero L]

theorem le_ofReal_div_of_mul {x : ENNReal} {a k : ℝ} (ha : 0 < a)
    (h : ENNReal.ofReal a * x ≤ ENNReal.ofReal k) : x ≤ ENNReal.ofReal (k / a) := by
  rw [ENNReal.ofReal_div_of_pos ha, ENNReal.le_div_iff_mul_le (Or.inl (by simpa using ha))
    (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  exact h

/-- Summing a bound over `X ∈ 𝒫_j` with `X̄ = U` (the analogue of `Step.wsum_le`). -/
theorem wsumO_le {c : Case} {ℓ₀ : ℝ} {a b : Lam d L N} {j k : ℕ} {U : Finset (Lam d L N)}
    (hU : IsPolymer (j + 1) U) {w c' : ℝ} (hc : 0 ≤ c') (s : Finset (Finset (Lam d L N)))
    (F : Finset (Lam d L N) → OE c (Lam d L N)) (hs : ∀ X ∈ s, IsPolymer j X ∧ clo j X = U)
    (hF : ∀ X ∈ s, ENNReal.ofReal w * nrmj c ℓ₀ a b k (F X) ≤
      ENNReal.ofReal (c' / 2 ^ (L ^ d * nb (j + 1) U))) :
    ENNReal.ofReal w * nrmj c ℓ₀ a b k (∑ X ∈ s, F X) ≤ ENNReal.ofReal c' := by
  classical
  set M : ℕ := 2 ^ (L ^ d * nb (j + 1) U)
  have hcard : s.card ≤ M := by
    refine le_trans (card_le_card ?_) (card_clo_eq_le hU)
    intro X hX
    exact mem_filter.2 ⟨mem_Pj.2 ⟨subset_univ _, (hs X hX).1⟩, (hs X hX).2⟩
  calc ENNReal.ofReal w * nrmj c ℓ₀ a b k (∑ X ∈ s, F X)
      ≤ ENNReal.ofReal w * ∑ X ∈ s, nrmj c ℓ₀ a b k (F X) := by
        gcongr; exact nrmj_sum_le k s F
    _ = ∑ X ∈ s, ENNReal.ofReal w * nrmj c ℓ₀ a b k (F X) := mul_sum _ _ _
    _ ≤ (M : ENNReal) * ENNReal.ofReal (c' / 2 ^ (L ^ d * nb (j + 1) U)) :=
        sum_le_card_mul_ennreal _ _ _ _ hcard hF
    _ = ENNReal.ofReal c' := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1
        have : (0 : ℝ) < M := by positivity
        simp only [M, Nat.cast_pow, Nat.cast_ofNat] at this ⊢
        field_simp

theorem exp_le_two_pow {x : ℝ} {m : ℕ} (hx : x ≤ m / 8) : Real.exp x ≤ 2 ^ m := by
  have he : Real.exp (1 / 8) ≤ 2 := by
    have := (abs_le.1 (Real.abs_exp_sub_one_le (x := 1 / 8) (by norm_num))).2
    norm_num at this ⊢; linarith
  calc Real.exp x ≤ Real.exp (m * (1 / 8)) := Real.exp_le_exp.2 (by linarith)
    _ = Real.exp (1 / 8) ^ m := by rw [← Real.exp_nat_mul]
    _ ≤ 2 ^ m := pow_le_pow_left₀ (Real.exp_pos _).le he m


theorem exp_sub_one_le_mul_exp {y : ℝ} (hy : 0 ≤ y) : Real.exp y - 1 ≤ y * Real.exp y := by
  have h1 := Real.add_one_le_exp (-y)
  have h2 : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  nlinarith [Real.exp_pos y]

section PerX

variable {c : Case} {ℓ₀ : ℝ} {a b : Lam d L N} {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℝ}
  {Vb : Vcoup} {Vo : Coup c} {K : Finset (Lam d L N) → OE c (Lam d L N)}

/-- The prefactor: `‖P‖ ≤ 2^{|𝓑_j(X)|}` and `‖π_obs P‖ ≤ 3 t L^d 4^{|𝓑_j(X)|}`. -/
theorem prefG_bounds (hd : 2 ≤ d) (hℓ₀ : 0 < ℓ₀) {t : ℝ} (ht : 0 ≤ t)
    (hκ : 3 * t * (L : ℝ) ^ d ≤ 1 / 8)
    (hf : ∀ p ∈ blockIdx (L := L) (N := N) j,
      nrmj c ℓ₀ a b (j + 1) ((obsI j C Vb Vo K a b).eu p - 1) ≤ ENNReal.ofReal (Real.exp t - 1) ∧
      nrmj c ℓ₀ a b (j + 1) ((obsI j C Vb Vo K a b).eum p - 1) ≤ ENNReal.ofReal (Real.exp t - 1) ∧
      nrmj c ℓ₀ a b (j + 1) ((obsI j C Vb Vo K a b).eV p - 1) ≤ ENNReal.ofReal (Real.exp t - 1))
    {U X : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U) (hXU : clo j X = U) :
    nrmj c ℓ₀ a b (j + 1) (prefG j (obsI j C Vb Vo K a b) U X) ≤ ENNReal.ofReal (2 ^ nb j X) ∧
      nrmj c ℓ₀ a b (j + 1) (πobs (prefG j (obsI j C Vb Vo K a b) U X)) ≤
        ENNReal.ofReal (3 * t * (L : ℝ) ^ d * 4 ^ nb j X) := by
  have h1 := n1_prefG_sub_one_le j C Vb Vo K hd hℓ₀ ht hf U X
  set y : ℝ := t * nb j U + 2 * t * nb j (U \ X) with hy
  have hnbY : (nb j (U \ X) : ℝ) ≤ nb j U := by
    exact_mod_cast card_le_card (image_subset_image sdiff_subset)
  have hnbU : (nb j U : ℝ) ≤ (L : ℝ) ^ d * nb j X := by
    have := (nb_le_of_succ hU).trans (Nat.mul_le_mul_left (L ^ d) (hXU ▸ nb_clo_le j X))
    exact_mod_cast this
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y ≤ 3 * t * (L : ℝ) ^ d * nb j X := by
    have : y ≤ 3 * t * nb j U := by rw [hy]; nlinarith
    nlinarith
  have hy2 : y ≤ (nb j X : ℝ) / 8 := by
    have := mul_le_mul_of_nonneg_right hκ (Nat.cast_nonneg (α := ℝ) (nb j X)); linarith
  have hexp : Real.exp y ≤ 2 ^ nb j X := exp_le_two_pow hy2
  have hm : (nb j X : ℝ) ≤ 2 ^ nb j X := by exact_mod_cast (Nat.lt_two_pow_self).le
  constructor
  · have e : prefG j (obsI j C Vb Vo K a b) U X =
        (prefG j (obsI j C Vb Vo K a b) U X - 1) + 1 := by ring
    rw [e]
    refine (nrmj_add_le _ _ _).trans ((add_le_add h1
      (oT_one_le (hpow_pos _) (Grassmann.ellj_pos (d := d) (L_pos (L := L)) hℓ₀ _))).trans ?_)
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by linarith [Real.add_one_le_exp y])
      zero_le_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · have e : πobs (prefG j (obsI j C Vb Vo K a b) U X) =
        πobs (prefG j (obsI j C Vb Vo K a b) U X - 1) := by
      rw [map_sub, show (1 : OE c (Lam d L N)) = emb 1 from (map_one _).symm, πobs_emb, sub_zero]
    rw [e]
    refine (nrmj_πobs_le _ _).trans (h1.trans (ENNReal.ofReal_le_ofReal ?_))
    have h3 := exp_sub_one_le_mul_exp hy0
    have h4 : y * Real.exp y ≤ 3 * t * (L : ℝ) ^ d * nb j X * 2 ^ nb j X :=
      mul_le_mul hy1 hexp (Real.exp_pos _).le (by positivity)
    have h5 : (4 : ℝ) ^ nb j X = 2 ^ nb j X * 2 ^ nb j X := by rw [← mul_pow]; norm_num
    rw [h5]
    have : 3 * t * (L : ℝ) ^ d * nb j X * 2 ^ nb j X ≤
        3 * t * (L : ℝ) ^ d * (2 ^ nb j X * 2 ^ nb j X) := by
      rw [← mul_assoc]; gcongr
    linarith


set_option maxHeartbeats 4000000 in
/-- The `K`-part, one polymer. -/
theorem Kpart_X (hd : 3 ≤ d) (hL4 : (4 : ℝ) ≤ L) (hL2d : 2 ^ d + 1 ≤ L) (hℓ₀ : 0 < ℓ₀)
    (hjN : j < N) (hC : GoodCov j ℓ₀ C) {t : ℝ} (ht : 0 ≤ t)
    (hκ : 3 * t * (L : ℝ) ^ d ≤ 1 / 8)
    (hf : ∀ p ∈ blockIdx (L := L) (N := N) j,
      nrmj c ℓ₀ a b (j + 1) ((obsI j C Vb Vo K a b).eu p - 1) ≤ ENNReal.ofReal (Real.exp t - 1) ∧
      nrmj c ℓ₀ a b (j + 1) ((obsI j C Vb Vo K a b).eum p - 1) ≤ ENNReal.ofReal (Real.exp t - 1) ∧
      nrmj c ℓ₀ a b (j + 1) ((obsI j C Vb Vo K a b).eV p - 1) ≤ ENNReal.ofReal (Real.exp t - 1))
    {A η kor kbr : ℝ} (hA1 : 1 ≤ A) (hη0 : 0 < η) (hη1 : η ≤ 1 / 4)
    (hcomb : ∀ X : Finset (Lam d L N), IsConn j X → ¬ IsSmall j X →
      (1 + 2 * η) * (nb (j + 1) (clo j X) : ℝ) ≤ nb j X)
    (hAP : ((4 : ℝ) ^ 2) ^ (L ^ d) ≤ A ^ (η / 2 ^ d)) (hkor : 0 ≤ kor) (hkbr : 0 ≤ kbr)
    (hko : KnormObs c ℓ₀ a b j A K = ENNReal.ofReal kor)
    (hkb : Knorm j (ellj d L ℓ₀ j) A (bulkK K) = ENNReal.ofReal kbr)
    {U X : Finset (Lam d L N)} (hU : IsConn (j + 1) U) (hX : IsConn j X) (hns : ¬ IsSmall j X)
    (hXU : clo j X = U) :
    ENNReal.ofReal (A ^ (nb (j + 1) U - 2 ^ d)) *
        nrmj c ℓ₀ a b (j + 1) (πobs (prefG j (obsI j C Vb Vo K a b) U X *
          (obsA c C).E ((obsA c C).θ ((obsI j C Vb Vo K a b).K X) -
            ∑ p ∈ blocks j X, (obsA c C).θ ((obsI j C Vb Vo K a b).J p X)))) ≤
      ENNReal.ofReal (A ^ (-η) * ((L : ℝ) ^ (2 * ((d : ℝ) - 2)) * kor +
        3 * t * (L : ℝ) ^ d * kbr) / 2 ^ (L ^ d * nb (j + 1) U)) := by
  have hL0 : (0 : ℝ) < L := L_pos
  have hh := hpow_pos (L := L) (j + 1)
  have hℓ := Grassmann.ellj_pos (d := d) (L_pos (L := L)) hℓ₀ (j + 1)
  have hw := wj_sub (d := d) (L := L) (by omega) c hℓ₀ (coal L a b : ℕ∞) (j + 1)
  have hA0 : 0 < A := by linarith
  set m := nb j X
  set n := nb (j + 1) U
  set k := m - 2 ^ d
  set K₂ : ℝ := (L : ℝ) ^ (2 * ((d : ℝ) - 2))
  have hK₂ : 0 ≤ K₂ := by positivity
  have hJ : ∑ p ∈ blocks j X, (obsA c C).θ ((obsI j C Vb Vo K a b).J p X) = 0 :=
    sum_eq_zero fun p _ => by rw [obsI_hJ j C Vb Vo K a b p X hns, map_zero]
  rw [hJ, sub_zero]
  obtain ⟨hP1, hP2⟩ := prefG_bounds (by omega) hℓ₀ ht hκ hf hU.1 hXU
  have hAk : 0 < A ^ k := pow_pos hA0 k
  -- the observable part of `K(X)`
  have hKo : nrmj c ℓ₀ a b (j + 1) (πobs (ECO C (thetaO (K X)))) ≤
      ENNReal.ofReal (K₂ * (kor / A ^ k)) := by
    rw [πobs_ECOL, πobs_thetaOL]
    refine (nrmj_ECO_le hd hL4 hℓ₀ hC _).trans ?_
    rw [ENNReal.ofReal_mul hK₂]
    gcongr
    refine le_ofReal_div_of_mul hAk ?_
    have := wnormO_le_KnormFull (c := c) (ℓ₀ := ℓ₀) (a := a) (b := b) (A := A)
      (K := fun X => πobs (K X)) hX
    rw [← hko]; exact this
  have hKb : Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1))
      ((bulk (ECO C (thetaO (K X))) : EvR (Lam d L N)) : Alg d L N) ≤
      ENNReal.ofReal (kbr / A ^ k) := by
    rw [bulk_ECO, bulk_thetaO, coe_ECE, coe_thetaE]
    refine (Tj_EC_theta_le hd hL4 hℓ₀ j hC.psd hC.norm _).trans ?_
    refine le_ofReal_div_of_mul hAk ?_
    have := wnorm_le_Knorm (ℓ := ellj d L ℓ₀ j) (A := A) (K := bulkK K) hX
    rw [← hkb]; exact this
  have hmain : nrmj c ℓ₀ a b (j + 1) (πobs (prefG j (obsI j C Vb Vo K a b) U X *
        ECO C (thetaO (K X)))) ≤
      ENNReal.ofReal (4 ^ m * (K₂ * kor + 3 * t * (L : ℝ) ^ d * kbr) / A ^ k) := by
    refine (oT_πobs_mul_le' hh hℓ hw _ _).trans ?_
    refine (add_le_add (mul_le_mul' hP1 hKo) (mul_le_mul' hP2 hKb)).trans (le_of_eq_of_le
      (by rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]) (ENNReal.ofReal_le_ofReal ?_))
    have h2 : (2 : ℝ) ^ m ≤ 4 ^ m := pow_le_pow_left₀ (by norm_num) (by norm_num) m
    have e : 4 ^ m * (K₂ * kor + 3 * t * (L : ℝ) ^ d * kbr) / A ^ k =
        4 ^ m * (K₂ * (kor / A ^ k)) + 3 * t * (L : ℝ) ^ d * 4 ^ m * (kbr / A ^ k) := by
      field_simp
    rw [e]
    have : 0 ≤ K₂ * (kor / A ^ k) := by positivity
    nlinarith
  -- combinatorics
  have hm : 2 ^ d < m := by
    by_contra hc; push Not at hc; exact hns ⟨hX.1, hX.2, hc⟩
  have hc := hcomb X hX hns
  rw [hXU] at hc
  have hmP : m ≤ L ^ d * n :=
    (card_le_card (image_subset_image (hXU ▸ subset_clo j X))).trans (nb_le_of_succ hU.1)
  have hreal := largeK_real' (P := L ^ d) hA1 hη0 hη1 (by norm_num : (1 : ℝ) ≤ 4) hc hm hmP hAP
  refine (mul_le_mul_left' hmain _).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  set W := K₂ * kor + 3 * t * (L : ℝ) ^ d * kbr
  have hW : 0 ≤ W := by positivity
  have h24 : (2 : ℝ) ^ (L ^ d * n) ≤ 4 ^ (L ^ d * n) :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  rw [le_div_iff₀ (by positivity)]
  calc A ^ (n - 2 ^ d) * (4 ^ m * W / A ^ k) * 2 ^ (L ^ d * n)
      ≤ A ^ (n - 2 ^ d) * (4 ^ m * W / A ^ k) * 4 ^ (L ^ d * n) := by gcongr
    _ = (A ^ (n - 2 ^ d) * 4 ^ m * 4 ^ (L ^ d * n)) * W / A ^ k := by ring
    _ ≤ (A ^ (-η) * A ^ k) * W / A ^ k := by gcongr
    _ = A ^ (-η) * W := by field_simp

set_option maxHeartbeats 4000000 in
/-- The `δI`-part, one polymer. -/
theorem Dpart_X (hd : 3 ≤ d) (hℓ₀ : 0 < ℓ₀) (hC : GoodCov j ℓ₀ C) {t : ℝ} (ht : 0 ≤ t)
    (hκ : 3 * t * (L : ℝ) ^ d ≤ 1 / 8)
    (hf : ∀ p ∈ blockIdx (L := L) (N := N) j,
      nrmj c ℓ₀ a b (j + 1) ((obsI j C Vb Vo K a b).eu p - 1) ≤ ENNReal.ofReal (Real.exp t - 1) ∧
      nrmj c ℓ₀ a b (j + 1) ((obsI j C Vb Vo K a b).eum p - 1) ≤ ENNReal.ofReal (Real.exp t - 1) ∧
      nrmj c ℓ₀ a b (j + 1) ((obsI j C Vb Vo K a b).eV p - 1) ≤ ENNReal.ofReal (Real.exp t - 1))
    {A q σ Γ r : ℝ} (hA1 : 1 ≤ A) (hq : 0 ≤ q) (hσ : 0 ≤ σ) (hΓ : 0 ≤ Γ)
    (hr : r = 1 / (A * 2 ^ (L ^ d))) (hρr : 2 * (q + σ) ≤ r ^ 2)
    (hAP : (2 : ℝ) ^ (L ^ d * 2 ^ d) ≤ A)
    (hbq : ∀ p ∈ blockIdx (L := L) (N := N) j,
      Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1))
        ((bulk (dIoL j C Vb Vo K a b p) : EvR (Lam d L N ⊕ Lam d L N)) :
          Grassmann.N (Lam d L N ⊕ Lam d L N)) ≤ ENNReal.ofReal q)
    (hbσ : ∀ p ∈ blockIdx (L := L) (N := N) j,
      n2 c ℓ₀ a b j (πobs (dIoL j C Vb Vo K a b p)) ≤ ENNReal.ofReal σ)
    {U X : Finset (Lam d L N)} (hU : IsConn (j + 1) U) (hX : IsPolymer j X) (hns : ¬ IsSmall j X)
    (hXU : clo j X = U)
    (hpair : blk j a ∈ blocks j X → blk j b ∈ blocks j X → blk j a ≠ blk j b →
      nb j X = 2 →
      nrmj c ℓ₀ a b (j + 1)
        (ECO C (πobs (dIoL j C Vb Vo K a b (blk j a)) * πobs (dIoL j C Vb Vo K a b (blk j b)))) ≤
        ENNReal.ofReal Γ) :
    ENNReal.ofReal (A ^ (nb (j + 1) U - 2 ^ d)) *
        nrmj c ℓ₀ a b (j + 1) (πobs (prefG j (obsI j C Vb Vo K a b) U X *
          (obsA c C).E (dIPowG (obsA c C) j (obsI j C Vb Vo K a b) X))) ≤
      ENNReal.ofReal (4 * (Γ + 2 * σ * q + q ^ 2) * A / 2 ^ (L ^ d * nb (j + 1) U)) := by
  have hL0 : (0 : ℝ) < L := L_pos
  have hh := hpow_pos (L := L) (j + 1)
  have hℓ := Grassmann.ellj_pos (d := d) (L_pos (L := L)) hℓ₀ (j + 1)
  have hw := wj_sub (d := d) (L := L) (by omega) c hℓ₀ (coal L a b : ℕ∞) (j + 1)
  have hA0 : 0 < A := by linarith
  set m := nb j X
  set n := nb (j + 1) U
  set ρ := q + σ
  have hρ : 0 ≤ ρ := by positivity
  obtain ⟨hP1, hP2⟩ := prefG_bounds (by omega) hℓ₀ ht hκ hf hU.1 hXU
  have hnm : n ≤ m := by have := nb_clo_le j X; rw [hXU] at this; exact this
  have hm2 : 2 ≤ m := by
    have hne : X ≠ ∅ := by
      rintro rfl
      rw [clo_empty] at hXU
      obtain ⟨x, hx⟩ := hU.2.1
      rw [← hXU] at hx
      exact notMem_empty x hx
    by_cases hc' : IsConnected j X
    · have : 2 ^ d < m := by
        by_contra h; push Not at h; exact hns ⟨hX, hc', h⟩
      have : 2 ≤ 2 ^ d := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · have h0 := (comp_card_eq_zero_iff hX).not.2 hne
      have h1' := (comp_card_eq_one_iff hX).not.2 (fun h => hc' h.2)
      have := card_comp_le (j := j) (X := X)
      omega
  have hobs := n1_πobs_ECO_dIPow_le j C Vb Vo K (by omega) hℓ₀ hC hm2 hq hσ hΓ hbq hbσ hpair
  have hbulk : Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1))
      ((bulk (ECO C (dIPowG (obsA c C) j (obsI j C Vb Vo K a b) X)) : EvR (Lam d L N)) :
        Alg d L N) ≤ ENNReal.ofReal (q ^ m) := by
    rw [bulk_ECO, coe_ECE]
    refine (tNorm_EC_le hh hℓ hC.psd hC.norm _).trans ?_
    rw [dIPowG, bpow, map_prod]
    refine (tNorm_prod_le hh hℓ _ _).trans ((prod_le_prod' fun p hp => hbq p
      (mem_blockIdx_of_mem_blocks hp)).trans ?_)
    rw [prod_const, ENNReal.ofReal_pow hq]
    exact le_rfl
  have hmain : nrmj c ℓ₀ a b (j + 1) (πobs (prefG j (obsI j C Vb Vo K a b) U X *
        ECO C (dIPowG (obsA c C) j (obsI j C Vb Vo K a b) X))) ≤
      ENNReal.ofReal (4 * (Γ + 2 * σ * q + q ^ 2) * (2 * ρ) ^ (m - 2)) := by
    refine (oT_πobs_mul_le' hh hℓ hw _ _).trans ?_
    refine (add_le_add (mul_le_mul' hP1 hobs) (mul_le_mul' ((nrmj_πobs_le _ _).trans hP1)
      hbulk)).trans (le_of_eq_of_le
      (by rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]) (ENNReal.ofReal_le_ofReal ?_))
    have e1 : (2 : ℝ) ^ m = 4 * 2 ^ (m - 2) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
    have e2 : q ^ m = q ^ 2 * q ^ (m - 2) := by rw [← pow_add]; congr 1; omega
    have e3 : q ^ (m - 2) ≤ ρ ^ (m - 2) := pow_le_pow_left₀ hq (le_add_of_nonneg_right hσ) _
    rw [e1, e2, mul_pow]
    have : 0 ≤ (2 : ℝ) ^ (m - 2) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left e3 (mul_nonneg this (sq_nonneg q)),
      pow_nonneg hρ (m - 2), mul_nonneg hΓ (pow_nonneg hρ (m - 2))]
  have hreal := largeD_real' (d := d) (n := n) (m := m) (P := L ^ d) (by omega) hA1
    (by positivity) hr hρr hm2 hnm hAP
  refine (mul_le_mul_left' hmain _).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [le_div_iff₀ (by positivity)]
  have hΨ : 0 ≤ 4 * (Γ + 2 * σ * q + q ^ 2) := by positivity
  calc A ^ (n - 2 ^ d) * (4 * (Γ + 2 * σ * q + q ^ 2) * (2 * ρ) ^ (m - 2)) * 2 ^ (L ^ d * n)
      = 4 * (Γ + 2 * σ * q + q ^ 2) * (A ^ (n - 2 ^ d) * (2 * ρ) ^ (m - 2) * 2 ^ (L ^ d * n)) := by
        ring
    _ ≤ 4 * (Γ + 2 * σ * q + q ^ 2) * A := by gcongr

end PerX

set_option maxHeartbeats 8000000 in
/-- **The large set estimate** (`e:Kquad-obs`): `LargeObsStmt'` with `ν = 1`, `m = 9 d`. -/
theorem obs_largeset_bound_proof' {d : ℕ} (hd : 3 ≤ d) : LargeObsStmt' d := by
  obtain ⟨CB, LB, hCB, hLB, hbr⟩ := block_real hd
  obtain ⟨C₁, ε₁, Ld, hC₁, hε₁, hLd, hdI⟩ := dI_bounds hd
  obtain ⟨CV, LV, hCV, hLV, hVn⟩ := Vobs_next_bounds hd
  obtain ⟨η, hη0, hη1, hcomb⟩ := comb1 d
  set Cst : ℝ := 1 + CB + C₁ + CV with hCst
  have hCst1 : 1 ≤ Cst := by linarith
  refine ⟨1400 * Cst ^ 4, η, 1, 9 * d, max LB (max Ld LV), by positivity, hη0, one_pos, ?_⟩
  intro L _ hL
  have hLB' : LB ≤ L := le_trans (le_max_left _ _) hL
  have hLd' : Ld ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
  have hLV' : LV ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
  have hL4 : (4 : ℝ) ≤ L := four_le_of_L₀ (hLB.trans hLB')
  have hL0 : (0 : ℝ) < L := by linarith
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hL2d : 2 ^ d + 1 ≤ L := by
    have : 2 ^ d ≤ 2 ^ (d + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := hLB.trans hLB'
    omega
  set P : ℕ := L ^ d with hP
  set K₂ : ℝ := (L : ℝ) ^ (2 * ((d : ℝ) - 2)) with hK₂
  have hK₂1 : 1 ≤ K₂ := one_le_K₂ hd
  set G : ℝ := Cst * (L : ℝ) ^ (2 * d) with hG
  have hLd1 : (1 : ℝ) ≤ (L : ℝ) ^ d := one_le_pow₀ hL1
  have hL2d1 : (1 : ℝ) ≤ (L : ℝ) ^ (2 * d) := one_le_pow₀ hL1
  have hK₂G : K₂ ≤ (L : ℝ) ^ (2 * d) := by
    rw [hK₂, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by push_cast; linarith)
  have hG1 : 1 ≤ G := one_le_mul_of_one_le_of_one_le hCst1 hL2d1
  have hG0 : 0 < G := by linarith
  have hCVK : CV * K₂ ≤ G := by
    rw [hG]; exact mul_le_mul (by linarith) hK₂G (by linarith) (by linarith)
  have hK₂G' : K₂ ≤ G := hK₂G.trans (le_mul_of_one_le_left (by positivity) hCst1)
  have hC₁G : C₁ ≤ G := (show C₁ ≤ Cst by linarith).trans (le_mul_of_one_le_right (by linarith) hL2d1)
  have hCBG : 1 + CB ≤ G := (show 1 + CB ≤ Cst by linarith).trans
    (le_mul_of_one_le_right (by linarith) hL2d1)
  set A₁ : ℝ := (16 : ℝ) ^ ((P : ℝ) * 2 ^ d / η) with hA₁
  refine ⟨max 1 A₁, le_max_left _ _, ?_⟩
  intro A hA
  have hA1 : 1 ≤ A := le_trans (le_max_left _ _) hA
  have hA0 : 0 < A := by linarith
  have hAA₁ : A₁ ≤ A := le_trans (le_max_right _ _) hA
  have hA₁0 : 0 ≤ A₁ := by positivity
  have h2d : (0 : ℝ) < 2 ^ d := by positivity
  have hAP1 : ((4 : ℝ) ^ 2) ^ P ≤ A ^ (η / 2 ^ d) := by
    have e : (P : ℝ) * 2 ^ d / η * (η / 2 ^ d) = P := by field_simp
    calc ((4 : ℝ) ^ 2) ^ P = (16 : ℝ) ^ (P : ℝ) := by rw [Real.rpow_natCast]; norm_num
      _ = A₁ ^ (η / 2 ^ d) := by rw [hA₁, ← Real.rpow_mul (by norm_num), e]
      _ ≤ A ^ (η / 2 ^ d) := Real.rpow_le_rpow hA₁0 hAA₁ (by positivity)
  have hAP2 : (2 : ℝ) ^ (P * 2 ^ d) ≤ A := by
    calc (2 : ℝ) ^ (P * 2 ^ d) ≤ 16 ^ (P * 2 ^ d) := by gcongr; norm_num
      _ = (16 : ℝ) ^ ((P : ℝ) * 2 ^ d) := by rw [← Real.rpow_natCast]; push_cast; rfl
      _ ≤ A₁ := by
          rw [hA₁]
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          exact le_div_self (by positivity) hη0 (by linarith)
      _ ≤ A := hAA₁
  set r : ℝ := 1 / (A * 2 ^ P) with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r ≤ 1 := by
    rw [hr, div_le_one (by positivity)]
    exact one_le_mul_of_one_le_of_one_le hA1 (one_le_pow₀ (by norm_num))
  set ε₀ : ℝ := min ε₁ (r ^ 2 / (144 * G * (L : ℝ) ^ d)) with hε₀
  have hε₀0 : 0 < ε₀ := lt_min hε₁ (by positivity)
  refine ⟨ε₀, hε₀0, ?_⟩
  intro N j hj ℓ₀ hℓ₀ c P' C Vb Vo K a b h hsep hvb hvo U hU
  classical
  have hC := h.cov
  have hCs := symm_of_goodCov hC a b
  set vb := Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) Vb with hvb_def
  set kb := Knorm j (ellj d L ℓ₀ j) A (bulkK K) with hkb_def
  set vo := VnormObs c ℓ₀ a b j Vo with hvo_def
  set ko := KnormObs c ℓ₀ a b j A K with hko_def
  have hvbt : vb ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_self_add.trans hvb)
  have hkbt : kb ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_add_self.trans hvb)
  have hvot : vo ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_self_add.trans hvo)
  have hkot : ko ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_add_self.trans hvo)
  set vbr := vb.toReal with hvbr
  set kbr := kb.toReal with hkbr
  set vor := vo.toReal with hvor
  set kor := ko.toReal with hkor
  have evb : vb = ENNReal.ofReal vbr := (ENNReal.ofReal_toReal hvbt).symm
  have ekb : kb = ENNReal.ofReal kbr := (ENNReal.ofReal_toReal hkbt).symm
  have evo : vo = ENNReal.ofReal vor := (ENNReal.ofReal_toReal hvot).symm
  have eko : ko = ENNReal.ofReal kor := (ENNReal.ofReal_toReal hkot).symm
  have hvbr0 : 0 ≤ vbr := ENNReal.toReal_nonneg
  have hkbr0 : 0 ≤ kbr := ENNReal.toReal_nonneg
  have hvor0 : 0 ≤ vor := ENNReal.toReal_nonneg
  have hkor0 : 0 ≤ kor := ENNReal.toReal_nonneg
  have hBε : vbr + kbr ≤ ε₀ := by
    have := hvb
    rw [evb, ekb, ← ENNReal.ofReal_add hvbr0 hkbr0] at this
    exact (ENNReal.ofReal_le_ofReal_iff hε₀0.le).1 this
  have hOε : vor + kor ≤ ε₀ := by
    have := hvo
    rw [evo, eko, ← ENNReal.ofReal_add hvor0 hkor0] at this
    exact (ENNReal.ofReal_le_ofReal_iff hε₀0.le).1 this
  have hε₀r : ε₀ * (144 * G * (L : ℝ) ^ d) ≤ r ^ 2 :=
    (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
  have hε₀1 : ε₀ ≤ ε₁ := min_le_left _ _
  have hGSL : 72 * (G * (vbr + kbr + (vor + kor)) * (L : ℝ) ^ d) ≤ r ^ 2 := by
    have hS2 : vbr + kbr + (vor + kor) ≤ 2 * ε₀ := by linarith
    have h1 := mul_le_mul_of_nonneg_left hS2 (by positivity : (0 : ℝ) ≤ 72 * G * (L : ℝ) ^ d)
    have e1 : 72 * G * (L : ℝ) ^ d * (2 * ε₀) = ε₀ * (144 * G * (L : ℝ) ^ d) := by ring
    have e2 : 72 * (G * (vbr + kbr + (vor + kor)) * (L : ℝ) ^ d) =
        72 * G * (L : ℝ) ^ d * (vbr + kbr + (vor + kor)) := by ring
    linarith
  -- the real parameters
  obtain ⟨α, hα⟩ : ∃ x : ℝ, x = vbr + CB * kbr := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ x : ℝ, x = K₂ * vor := ⟨_, rfl⟩
  obtain ⟨s', hs'⟩ : ∃ x : ℝ, x = CV * K₂ * (vor + kor) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ x : ℝ, x = C₁ * (vbr + kbr) := ⟨_, rfl⟩
  obtain ⟨σ, hσ⟩ : ∃ x : ℝ,
      x = Real.exp vbr * (s + s ^ 2 / 2) + Real.exp (α + 2 * α) * (s' + s' ^ 2 / 2) := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ x : ℝ, x = (Real.exp vbr - 1) * (s + s ^ 2 / 2) +
      (Real.exp (α + 2 * α) - 1) * (s' + s' ^ 2 / 2) := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ x : ℝ, x = CV * K₂ * kor := ⟨_, rfl⟩
  obtain ⟨mM, hmM⟩ : ∃ x : ℝ, x = s + s' := ⟨_, rfl⟩
  obtain ⟨Γ, hΓ⟩ : ∃ x : ℝ, x = δ ^ 2 + 2 * mM * z + z ^ 2 := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ x : ℝ, x = α + s' + (2 * α + s') := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ x : ℝ, x = (vbr + kbr + kor) * (vbr + vor + kbr + kor) := ⟨_, rfl⟩
  obtain ⟨hKO, hρr, hκ, hΨle, hW1, hz0, hσ0, hΓ0, ht0⟩ :=
    large_real hvbr0 hkbr0 hvor0 hkor0 hCB hC₁ (by linarith) hK₂1 hG1 hCBG hC₁G hCVK hK₂G' hLd1
      hr0 hr1 hGSL hα hs hs' hq hσ hz hδ hmM hΓ ht hQ
  have hα0 : 0 ≤ α := by rw [hα]; positivity
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  have hs'0 : 0 ≤ s' := by rw [hs']; positivity
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hmM0 : 0 ≤ mM := by rw [hmM]; linarith
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  have hsm : ENNReal.ofReal K₂ * (vo + ko) ≤ 1 := by
    rw [evo, eko, ← ENNReal.ofReal_add hvor0 hkor0, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hKO
  -- the external bounds
  obtain ⟨-, -, -, -, -, hblk⟩ :=
    hbr L hLB' N j hj ℓ₀ hℓ₀ C hC Vb (bulkK K) A hA1 h.bulk _ hε₀0.le hvb
  have hdI' := fun p hp => (hdI L hLd' N j hj ℓ₀ hℓ₀ C hC Vb (bulkK K) A hA1 h.bulk
    (hvb.trans (ENNReal.ofReal_le_ofReal hε₀1)) p hp).1
  obtain ⟨-, -, -, h4, h5⟩ := hVn L hLV' N j hj ℓ₀ hℓ₀ c P' C Vb Vo K a b A hA1 h hsm
  -- block bounds
  have hx : ∀ p ∈ blockIdx (L := L) (N := N) j, Tj d (L : ℝ) (j + 1) (2 * ellj d L ℓ₀ (j + 1))
      ((VE Vb (blockSet j p) : EvR (Lam d L N)) : Alg d L N) ≤ ENNReal.ofReal vbr := fun p hp => by
    rw [coe_VE]; exact (Tj_succ_le hd hL4 hℓ₀ j _).2.trans (hblk p hp).1
  have hGv : ∀ p ∈ blockIdx (L := L) (N := N) j, n1' c ℓ₀ a b j (Gv j Vo a b p) ≤
      ENNReal.ofReal s := fun p hp => by
    refine (normj_succ_le hd hL4 c hℓ₀ _ j _).2.trans ?_
    rw [hs, ENNReal.ofReal_mul (by positivity)]
    gcongr
    exact (nrmj_Vobs_le Vo hp).trans evo.le
  have hzb : ∀ p ∈ blockIdx (L := L) (N := N) j,
      ‖(uVb j C Vb K).1 * (blockSet (L := L) (N := N) j p).card‖ ≤ α := fun p hp => by
    rw [hα]; exact (hblk p hp).2.1
  have hx' : ∀ p ∈ blockIdx (L := L) (N := N) j, Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1))
      ((VE (uVb j C Vb K).2 (blockSet j p) : EvR (Lam d L N)) : Alg d L N) ≤
        ENNReal.ofReal (2 * α) := fun p hp => by
    rw [coe_VE, hα]; exact (hblk p hp).2.2
  have eO : ENNReal.ofReal (CV * K₂) * (vo + ko) = ENNReal.ofReal s' := by
    rw [hs', evo, eko, ← ENNReal.ofReal_add hvor0 hkor0, ← ENNReal.ofReal_mul (by positivity)]
  have hGn : ∀ p ∈ blockIdx (L := L) (N := N) j,
      nrmj c ℓ₀ a b (j + 1) (Gn j C Vo K a b p) ≤ ENNReal.ofReal s' := fun p _ =>
    ((h5 _ (isPolymer_blockSet j p)).1).trans eO.le
  have huO : ∀ p ∈ blockIdx (L := L) (N := N) j,
      nrmj c ℓ₀ a b (j + 1) (uObsX j C Vo K a b (blockSet j p)) ≤ ENNReal.ofReal s' := fun p _ =>
    ((h5 _ (isPolymer_blockSet j p)).2.1).trans eO.le
  have hVf : ∀ p ∈ blockIdx (L := L) (N := N) j,
      nrmj c ℓ₀ a b (j + 1) (VfullX (uVb j C Vb K).2 (nextObs C j Vo K a b) a b (blockSet j p)) ≤
        ENNReal.ofReal (2 * α + s') := fun p hp => by
    refine (n1_VfullX_le _ _ _ _).trans ?_
    rw [ENNReal.ofReal_add (by positivity) hs'0, hα]
    exact add_le_add (hblk p hp).2.2 (((h5 _ (isPolymer_blockSet j p)).2.2).trans eO.le)
  have hfac0 := fun p hp => n1_factor_le j C Vb Vo K (by omega) hℓ₀ p hs'0 (by positivity)
    (hzb p hp) (huO p hp) (hVf p hp)
  have hfac : ∀ p ∈ blockIdx (L := L) (N := N) j,
      nrmj c ℓ₀ a b (j + 1) ((obsI j C Vb Vo K a b).eu p - 1) ≤ ENNReal.ofReal (Real.exp t - 1) ∧
      nrmj c ℓ₀ a b (j + 1) ((obsI j C Vb Vo K a b).eum p - 1) ≤ ENNReal.ofReal (Real.exp t - 1) ∧
      nrmj c ℓ₀ a b (j + 1) ((obsI j C Vb Vo K a b).eV p - 1) ≤ ENNReal.ofReal (Real.exp t - 1) :=
    fun p hp => by rw [ht]; exact hfac0 p hp
  have hbq : ∀ p ∈ blockIdx (L := L) (N := N) j,
      Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1))
        ((bulk (dIoL j C Vb Vo K a b p) : EvR (Lam d L N ⊕ Lam d L N)) :
          Grassmann.N (Lam d L N ⊕ Lam d L N)) ≤ ENNReal.ofReal q := fun p hp => by
    rw [bulk_dIoL]
    refine (hdI' p hp).trans (le_of_eq ?_)
    change ENNReal.ofReal C₁ * (vb + kb) = _
    rw [hq, evb, ekb, ← ENNReal.ofReal_add hvbr0 hkbr0, ← ENNReal.ofReal_mul hC₁]
  have hbσ : ∀ p ∈ blockIdx (L := L) (N := N) j,
      n2 c ℓ₀ a b j (πobs (dIoL j C Vb Vo K a b p)) ≤ ENNReal.ofReal σ := fun p hp => by
    rw [hσ]; exact n2_πobs_dIo_le j C Vb Vo K (by omega) hℓ₀ p hvbr0 hs0 (by positivity) hs'0 (hx p hp)
      (hGv p hp) (hzb p hp) (hx' p hp) (hGn p hp)
  have hMo : ∀ p ∈ blockIdx (L := L) (N := N) j,
      n2 c ℓ₀ a b j (Mo j C Vo K a b p) ≤ ENNReal.ofReal mM := fun p hp => by
    rw [hmM]; exact n2_Mo_le j C Vo K hℓ₀ p hs0 hs'0 (hGv p hp) (hGn p hp)
  have hZo : ∀ p ∈ blockIdx (L := L) (N := N) j,
      n2 c ℓ₀ a b j (Zo j C Vb Vo K a b p) ≤ ENNReal.ofReal z := fun p hp => by
    rw [hz]; exact n2_Zo_le j C Vb Vo K (by omega) hℓ₀ p hvbr0 hs0 (by positivity) hs'0 (hx p hp)
      (hGv p hp) (hzb p hp) (hx' p hp) (hGn p hp)
  have hDl : ∀ p ∈ blockIdx (L := L) (N := N) j,
      nrmj c ℓ₀ a b (j + 1) (Dl j C Vo K a b p) ≤ ENNReal.ofReal δ := fun p hp => by
    refine (h4 p hp).trans (le_of_eq ?_)
    change ENNReal.ofReal (CV * K₂) * ko = _
    rw [hδ, eko, ← ENNReal.ofReal_mul (by positivity)]
  -- the decomposition
  set F := obsI j C Vb Vo K a b with hF
  set S1 := (univ \ smallSets (L := L) (N := N) j).filter
    (fun X => IsConn j X ∧ clo j X = U) with hS1
  set S2 := (univ \ smallSets (L := L) (N := N) j).filter
    (fun X => IsPolymer j X ∧ clo j X = U) with hS2
  have hsub : pairSets j U ⊆ S2 := by
    intro X hX
    obtain ⟨-, hXp, hXU, -, -, hnc⟩ := mem_filter.1 hX
    refine mem_filter.2 ⟨mem_sdiff.2 ⟨mem_univ _, fun hs => hnc ?_⟩, hXp, hXU⟩
    exact (mem_filter.1 hs).2.2.1
  have hdec : LlinLG (obsA c C) j F U - LpairG (obsA c C) j F U =
      (∑ X ∈ S1, prefG j F U X * (obsA c C).E ((obsA c C).θ (F.K X) -
        ∑ p ∈ blocks j X, (obsA c C).θ (F.J p X))) +
      ∑ X ∈ S2 \ pairSets j U, prefG j F U X * (obsA c C).E (dIPowG (obsA c C) j F X) := by
    simp only [LlinLG, LsumG, LpairG]
    rw [← sum_sdiff hsub]
    ring
  rw [hdec, map_add, map_sum, map_sum]
  unfold wnormO
  refine (mul_le_mul_left' (nrmj_add_le _ _ _) _).trans ?_
  rw [mul_add]
  obtain ⟨W, hW⟩ : ∃ x : ℝ, x = K₂ * kor + 3 * t * (L : ℝ) ^ d * kbr := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by rw [hW]; positivity
  have hK : ENNReal.ofReal (A ^ (nb (j + 1) U - 2 ^ d)) * nrmj c ℓ₀ a b (j + 1)
      (∑ X ∈ S1, πobs (prefG j F U X * (obsA c C).E ((obsA c C).θ (F.K X) -
        ∑ p ∈ blocks j X, (obsA c C).θ (F.J p X)))) ≤ ENNReal.ofReal (A ^ (-η) * W) := by
    refine wsumO_le hU.1 (by positivity) S1 _ (fun X hX => ?_) (fun X hX => ?_)
    · obtain ⟨-, hX1, hX2⟩ := mem_filter.1 hX; exact ⟨hX1.1, hX2⟩
    · obtain ⟨hX0, hX1, hX2⟩ := mem_filter.1 hX
      have hns : ¬ IsSmall j X := fun hs => (mem_sdiff.1 hX0).2 (mem_filter.2 ⟨mem_univ _, hs⟩)
      rw [hW]
      exact Kpart_X hd hL4 hL2d hℓ₀ hj hC ht0 hκ hfac hA1 hη0 hη1
        (fun X hX hns => hcomb L hL2d N j X hj hX hns) hAP1 hkor0 hkbr0 eko ekb hU hX1 hns hX2
  have hD : ENNReal.ofReal (A ^ (nb (j + 1) U - 2 ^ d)) * nrmj c ℓ₀ a b (j + 1)
      (∑ X ∈ S2 \ pairSets j U, πobs (prefG j F U X * (obsA c C).E (dIPowG (obsA c C) j F X))) ≤
      ENNReal.ofReal (4 * (Γ + 2 * σ * q + q ^ 2) * A) := by
    refine wsumO_le hU.1 (by positivity) _ _ (fun X hX => ?_) (fun X hX => ?_)
    · obtain ⟨-, hX1, hX2⟩ := mem_filter.1 (mem_sdiff.1 hX).1; exact ⟨hX1, hX2⟩
    · obtain ⟨hX0, hX1, hX2⟩ := mem_filter.1 (mem_sdiff.1 hX).1
      have hnp := (mem_sdiff.1 hX).2
      have hns : ¬ IsSmall j X := fun hs => (mem_sdiff.1 hX0).2 (mem_filter.2 ⟨mem_univ _, hs⟩)
      refine Dpart_X hd hℓ₀ hC ht0 hκ hfac hA1 hq0 hσ0 hΓ0 hr hρr hAP2 hbq hbσ hU hX1 hns hX2 ?_
      intro ha hb hne hnb2
      have hpa := mem_blockIdx_of_mem_blocks ha
      have hpb := mem_blockIdx_of_mem_blocks hb
      -- `C(a, b) = 0`: otherwise `X` is a pair in one `(j+1)`-block
      have hCab : C a b = 0 := by
        refine hsep fun hsame => hnp ?_
        have hbl : blocks j X = {blk j a, blk j b} := by
          symm
          refine eq_of_subset_of_card_le (insert_subset ha (singleton_subset_iff.2 hb)) ?_
          rw [card_pair hne]; exact hnb2.le
        have hn1 : nb (j + 1) X = 1 := by
          rw [nb, blocks_succ, hbl, image_insert, image_singleton, ← blk_succ, ← blk_succ,
            hsame, insert_eq_of_mem (mem_singleton_self _), card_singleton]
        have h2d' : 2 ≤ 2 ^ d := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) (by omega)
        have hnc : ¬ IsConnected j X := fun hc => hns ⟨hX1, hc, show nb j X ≤ 2 ^ d by omega⟩
        exact mem_filter.2 ⟨mem_univ _, hX1, hX2, hnb2, hn1, hnc⟩
      have hba : blk j b ≠ blk j a := fun h => hne h.symm
      refine (n1_ECO_πobs_dIo_mul_le j C Vb Vo K (by omega) hℓ₀ h.hab hCab (hCs ▸ hCab) hC
        (mem_blockSet_blk j a) (fun h => hba (Loc.mem_blockSet.1 h))
        (fun h => hne (Loc.mem_blockSet.1 h)) (mem_blockSet_blk j b) hδ0 hmM0 hz0
        (fun p hp => ?_) (fun p hp => ?_) (fun p hp => ?_)).trans (le_of_eq (by rw [hΓ]))
      · rcases mem_insert.1 hp with rfl | hp
        · exact hDl _ hpa
        · rw [mem_singleton.1 hp]; exact hDl _ hpb
      · rcases mem_insert.1 hp with rfl | hp
        · exact hMo _ hpa
        · rw [mem_singleton.1 hp]; exact hMo _ hpb
      · rcases mem_insert.1 hp with rfl | hp
        · exact hZo _ hpa
        · rw [mem_singleton.1 hp]; exact hZo _ hpb
  refine (add_le_add hK hD).trans ?_
  -- the final real inequality
  have hquad : quadO vb vo kb ko = ENNReal.ofReal Q := by
    rw [hQ, quadO, evb, evo, ekb, eko, ← ENNReal.ofReal_add hvbr0 hkbr0,
      ← ENNReal.ofReal_add (by positivity) hkor0, ← ENNReal.ofReal_add hvbr0 hvor0,
      ← ENNReal.ofReal_add (by positivity) hkbr0, ← ENNReal.ofReal_add (by positivity) hkor0,
      ← ENNReal.ofReal_mul (by positivity)]
  have hAη0 : 0 ≤ A ^ (-η) := Real.rpow_nonneg hA0.le _
  have hAη1 : A ^ (-η) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hA1 (by linarith)
  have hLm : 0 ≤ (L : ℝ) ^ (9 * d) := by positivity
  rw [hquad, eko, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity), Real.rpow_one]
  refine ENNReal.ofReal_le_ofReal ?_
  have hC4 : Cst ≤ Cst ^ 4 := le_self_pow₀ hCst1 (by norm_num)
  have hL29 : (L : ℝ) ^ (2 * d) ≤ (L : ℝ) ^ (9 * d) := pow_le_pow_right₀ hL1 (by omega)
  have hL39 : (L : ℝ) ^ (2 * d) * (L : ℝ) ^ d ≤ (L : ℝ) ^ (9 * d) := by
    rw [← pow_add]; exact pow_le_pow_right₀ hL1 (by omega)
  have hG4 : G ^ 4 = Cst ^ 4 * (L : ℝ) ^ (8 * d) := by rw [hG, mul_pow, ← pow_mul]; ring_nf
  have hL89 : (L : ℝ) ^ (8 * d) ≤ (L : ℝ) ^ (9 * d) := pow_le_pow_right₀ hL1 (by omega)
  obtain ⟨M, hM⟩ : ∃ x : ℝ, x = Cst ^ 4 * (L : ℝ) ^ (9 * d) := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hGM : G ≤ M := by rw [hG, hM]; exact mul_le_mul hC4 hL29 (by positivity) (by positivity)
  have hGLM : G * (L : ℝ) ^ d ≤ M := by
    rw [hG, hM, mul_assoc]; exact mul_le_mul hC4 hL39 (by positivity) (by positivity)
  have hG4M : G ^ 4 ≤ M := by
    rw [hG4, hM]; exact mul_le_mul_of_nonneg_left hL89 (by positivity)
  have hW2 : K₂ * kor ≤ M * kor := mul_le_mul_of_nonneg_right (hK₂G'.trans hGM) hkor0
  have hW3 : 9 * (G * (L : ℝ) ^ d) * Q ≤ 9 * M * Q := by
    have := mul_le_mul_of_nonneg_right hGLM hQ0; linarith
  have hWle : W ≤ M * kor + 9 * M * Q := by rw [hW]; linarith
  have hΨ : 4 * (Γ + 2 * σ * q + q ^ 2) ≤ 1352 * M * Q := by
    have := mul_le_mul_of_nonneg_right hG4M hQ0; linarith
  have key := large_final_real hAη0 hAη1 hA1 hkor0 hQ0 hM0 hWle hΨ
  have e3 : 1400 * Cst ^ 4 * (L : ℝ) ^ (9 * d) * A ^ (-η) * kor =
      1400 * (A ^ (-η) * (M * kor)) := by rw [hM]; ring
  have e4 : 1400 * Cst ^ 4 * (L : ℝ) ^ (9 * d) * A * Q = 1400 * (M * Q * A) := by rw [hM]; ring
  rw [e3, e4]
  linarith

end

end Obs
