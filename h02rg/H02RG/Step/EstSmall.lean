import Step.EstCoupling

/-!
# Small sets (Section `sec:K-smallset`)

Lemmas `lem:smallset-K`, `lem:smallset-V`, `lem:smallset-V1`, `lem:pert12` and
Proposition `prop:SmallSetLin`:
`‖𝓛_{j+1,𝒮}‖_{j+1} = O(L^{-d_+} ‖K_j‖_j + L^d (‖V_j‖_j^2 + ‖K_j‖_j^2))`.
For the last step `j + 1 = N` (where `Q = J = 0`) the factor `L^{-d_+}` becomes `L^d`.

* `term_eq_nonblock`, `term_eq_block`: the identities `e:Ksmallset` and `e:Kblock` for the
  summands of `𝓛_{j+1,𝒮}(U)` (using Proposition `prop:Loc` (iii) and the definitions of `J`, `Q`);
* `term_bound`: the bound on one summand (Lemmas `lem:smallset-K`, `lem:smallset-V`,
  `lem:smallset-V1`);
* `smallset_bound`: Proposition `prop:SmallSetLin`.
-/

namespace Step

noncomputable section

open Finset Grassmann Loc FRD

section Terms

variable {d L N : ℕ} [NeZero L]

/-! ### Algebraic identities for the summands (`e:Ksmallset`, `e:Kblock`) -/

theorem blocks_blockSet_eq {j : ℕ} {b : Fin d → ℕ}
    (hne : (blockSet (L := L) (N := N) j b).Nonempty) :
    blocks j (blockSet (L := L) (N := N) j b) = {b} := by
  ext c
  rw [mem_blocks, mem_singleton]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact mem_blockSet.1 hx
  · rintro rfl
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, hx, mem_blockSet.1 hx⟩

theorem nb_blockSet_le (j : ℕ) (b : Fin d → ℕ) : nb j (blockSet (L := L) (N := N) j b) ≤ 1 := by
  refine (card_le_card (s := blocks j (blockSet (L := L) (N := N) j b)) (t := {b}) ?_).trans
    (by simp)
  intro c hc
  obtain ⟨x, hx, rfl⟩ := mem_blocks.1 hc
  exact mem_singleton.2 (mem_blockSet.1 hx)

/-- `Loc_X F` if `j + 1 < N`, and `0` for the last step. -/
def LocC (j : ℕ) (X : Finset (Lam d L N)) (F : Alg d L N) : Alg d L N :=
  if j + 1 < N then LocX X F else 0

/-- `e:Ksmallset`: for `X ∈ 𝒮_j ∖ 𝓑_j`, the summand is `θ (1 - Loc_X) K(X) + (δI)^X`. -/
theorem term_eq_nonblock {j : ℕ} (C : Matrix (Lam d L N) (Lam d L N) ℝ) (V : Vcoup)
    (K : Act d L N) {X : Finset (Lam d L N)} (hX : IsSmall j X)
    (hnb : ∀ b, X ≠ blockSet j b) :
    ((thetaE (K X) - ∑ b ∈ blocks j X, thetaE (Jb j K b X) + dIPow j C V K X :
        EvR (Lam d L N ⊕ Lam d L N)) : Grassmann.N (Lam d L N ⊕ Lam d L N)) =
      theta ((K X : Alg d L N) - LocC j X (K X)) + (dIPow j C V K X : Grassmann.N _) := by
  classical
  have hJ : ∀ b ∈ blocks j X, (Jb j K b X : Alg d L N) =
      if j + 1 < N then LocXY X (blockSet j b) (K X) else 0 := by
    intro b hb
    have hsub := blockSet_subset hX.1 hb
    by_cases hj : j + 1 < N
    · rw [Jb, if_pos ⟨hj, hX, hsub⟩, if_neg (hnb b), if_pos hj, coe_LocE]
    · rw [Jb, if_neg (fun h => hj h.1), if_neg hj, ZeroMemClass.coe_zero]
  have hLoc : LocC j X (K X) = ∑ b ∈ blocks j X, (Jb j K b X : Alg d L N) := by
    rw [sum_congr rfl hJ, LocC]
    by_cases hj : j + 1 < N
    · simp only [hj, if_true]
      have := LocX_eq_sum (blocks j X) (blockSet j) (pairwiseDisjoint_blockSet j _)
        (K X : Alg d L N)
      rwa [biUnion_blocks hX.1] at this
    · simp [hj]
  rw [hLoc]
  simp only [AddSubgroupClass.coe_sub, AddMemClass.coe_add, coe_thetaE,
    AddSubmonoidClass.coe_finsetSum, map_sub, map_sum]

/-- `e:Kblock`: for `X = B ∈ 𝓑_j`, the summand is `θ (1 - Loc_B) K(B) + δI(B) + θ Q(B)`. -/
theorem term_eq_block {j : ℕ} (C : Matrix (Lam d L N) (Lam d L N) ℝ) (V : Vcoup)
    (K : Act d L N) {b : Fin d → ℕ} (hb : b ∈ blockIdx (d := d) (L := L) (N := N) j) :
    ((thetaE (K (blockSet j b)) -
        ∑ c ∈ blocks j (blockSet (L := L) (N := N) j b), thetaE (Jb j K c (blockSet j b)) +
        dIPow j C V K (blockSet j b) : EvR (Lam d L N ⊕ Lam d L N)) :
          Grassmann.N (Lam d L N ⊕ Lam d L N)) =
      theta ((K (blockSet j b) : Alg d L N) - LocC j (blockSet j b) (K (blockSet j b))) +
        ((dI j C V K b : Grassmann.N _) + theta (Qb j K b : Alg d L N)) := by
  classical
  set B := blockSet (L := L) (N := N) j b with hB
  have hne : B.Nonempty := by
    obtain ⟨x, _, hx⟩ := mem_image.1 hb
    exact ⟨x, mem_blockSet.2 hx⟩
  have hS : IsSmall j B := isSmall_blockSet_of_mem hb
  have hbl : blocks j B = {b} := blocks_blockSet_eq hne
  have hJQ : (Jb j K b B : Alg d L N) = LocC j B (K B) - (Qb j K b : Alg d L N) := by
    by_cases hj : j + 1 < N
    · have hsplit := sum_filter_add_sum_filter_not ((smallSets j).filter (fun Y => B ⊆ Y))
        (fun Y => Y = B) (fun Y => LocE Y B (K Y))
      rw [filter_filter, filter_filter] at hsplit
      have hmem : B ∈ (smallSets j).filter (fun Y => B ⊆ Y ∧ Y = B) :=
        mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, hS⟩, subset_rfl, rfl⟩
      rw [sum_eq_single_of_mem B hmem (fun Y hY hYB => absurd (mem_filter.1 hY).2.2 hYB)]
        at hsplit
      have hQ : Qb j K b = ∑ Y ∈ (smallSets j).filter (fun Y => B ⊆ Y), LocE Y B (K Y) := by
        rw [Qb, if_pos hj]
      have hJ : Jb j K b B = -∑ Y ∈ (smallSets j).filter (fun Y => B ⊆ Y ∧ Y ≠ B),
          LocE Y B (K Y) := by
        rw [Jb, if_pos ⟨hj, hS, subset_rfl⟩, if_pos rfl]
      rw [hQ, hJ, ← hsplit, LocC, if_pos hj, LocX]
      simp only [NegMemClass.coe_neg, AddMemClass.coe_add, coe_LocE,
        AddSubmonoidClass.coe_finsetSum]
      abel
    · simp [Jb, Qb, LocC, hj]
  rw [hbl, sum_singleton, dIPow, hbl, prod_singleton]
  simp only [AddSubgroupClass.coe_sub, AddMemClass.coe_add, coe_thetaE, hJQ, map_sub]
  abel

/-! ### The bound on one summand -/

/-- The bound on `𝔼 [θ K(X) - ∑_B θ J(B, X) + (δI)^X]` for `X ∈ 𝒮_j`: Lemmas `lem:smallset-K`
(per summand), `lem:smallset-V` for `X ∈ 𝓑_j` and `lem:smallset-V1` for `X ∈ 𝒮_j ∖ 𝓑_j`. -/
theorem term_bound (hd : 3 ≤ d) : ∃ (C₂ ε₁ : ℝ) (L₀ : ℕ), 0 ≤ C₂ ∧ 0 < ε₁ ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∀ (N j : ℕ), j < N → ∀ (ℓ₀ : ℝ), 0 < ℓ₀ →
    ∀ (C : Matrix (Lam d L N) (Lam d L N) ℝ), GoodCov j ℓ₀ C →
    ∀ (V : Vcoup) (K : Act d L N) (A : ℝ), 1 ≤ A → InK j K →
      Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V + Knorm j (ellj d L ℓ₀ j) A K ≤
        ENNReal.ofReal ε₁ →
      ∀ X : Finset (Lam d L N), IsSmall j X →
        Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1))
            (EC C ((thetaE (K X) - ∑ b ∈ blocks j X, thetaE (Jb j K b X) + dIPow j C V K X :
              EvR (Lam d L N ⊕ Lam d L N)) : Grassmann.N (Lam d L N ⊕ Lam d L N))) ≤
          ENNReal.ofReal (C₂ * (if j + 1 < N then (L : ℝ) ^ (-(d : ℝ)) * (L : ℝ) ^ (-dplus d)
              else 1)) * Knorm j (ellj d L ℓ₀ j) A K +
            ENNReal.ofReal C₂ *
              (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V ^ 2 +
                Knorm j (ellj d L ℓ₀ j) A K ^ 2) := by
  obtain ⟨C₁, εd, Ld, hC₁, hεd, hLd, hdI⟩ := dI_bounds hd
  obtain ⟨Cbar, Lc, hLoc⟩ := Loc_contract hd
  set Cm := max Cbar 0 + 1 with hCm
  have hCm1 : 1 ≤ Cm := by rw [hCm]; linarith [le_max_right Cbar 0]
  have hCmb : Cbar ≤ Cm := by rw [hCm]; linarith [le_max_left Cbar 0]
  refine ⟨Cm + (C₁ + 2 * C₁ ^ 2), min εd (1 / (C₁ + 1)), max Ld Lc, by positivity,
    lt_min hεd (by positivity), ?_⟩
  intro L _ hL N j hj ℓ₀ hℓ₀ C hC V K A hA hK hvk X hX
  have hvk' := hvk.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _))
  obtain ⟨hv, hk, hv0, hk0, hvkr⟩ := real_of_le (by positivity) hvk
  set vr := (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V).toReal
  set kr := (Knorm j (ellj d L ℓ₀ j) A K).toReal
  have hL4 : (4 : ℝ) ≤ L := four_le_of_L₀ (hLd.trans ((le_max_left _ _).trans hL))
  have hL0 : (0 : ℝ) < L := by linarith
  have hh : (0 : ℝ) < (L : ℝ) ^ (j + 1) := by positivity
  have hℓ := ellj_pos (d := d) hL0 hℓ₀ (j + 1)
  have hconn : IsConn j X := ⟨hX.1, hX.2.1⟩
  have hKX : Tj d (L : ℝ) j (ellj d L ℓ₀ j) (K X : Alg d L N) ≤ ENNReal.ofReal kr :=
    (Tj_le_Knorm hA hconn).trans hk.le
  set f : ℝ := if j + 1 < N then (L : ℝ) ^ (-(d : ℝ)) * (L : ℝ) ^ (-dplus d) else 1 with hf
  have hf0 : 0 ≤ f := by rw [hf]; split_ifs <;> positivity
  -- `lem:smallset-K`, one summand
  have h1 : Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1))
      (EC C (theta ((K X : Alg d L N) - LocC j X (K X)))) ≤
      ENNReal.ofReal (Cm * f) * ENNReal.ofReal kr := by
    refine (tNorm_EC_theta_le hh hℓ hC.psd hC.norm _).trans ?_
    by_cases hjN : j + 1 < N
    · rw [LocC, if_pos hjN, hf, if_pos hjN]
      refine (hLoc L ((le_max_right _ _).trans hL) N j hj ℓ₀ hℓ₀ X hX _ (hK.loc X hconn)
        (hK.sym X hconn)).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) hKX)
      rw [mul_assoc, dplus]
      exact mul_le_mul_of_nonneg_right hCmb (by positivity)
    · rw [LocC, if_neg hjN, hf, if_neg hjN, sub_zero, mul_one]
      refine (Tj_succ_le hd hL4 hℓ₀ j _).2.trans (hKX.trans ?_)
      exact le_mul_of_one_le_left zero_le (ENNReal.one_le_ofReal.2 hCm1)
  -- `lem:smallset-V` and `lem:smallset-V1`
  have h2 : ∀ R : Grassmann.N (Lam d L N ⊕ Lam d L N),
      Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1)) (EC C R) ≤
        ENNReal.ofReal ((C₁ + 2 * C₁ ^ 2) * (vr ^ 2 + kr ^ 2)) →
      Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1))
          (EC C (theta ((K X : Alg d L N) - LocC j X (K X)) + R)) ≤
        ENNReal.ofReal ((Cm + (C₁ + 2 * C₁ ^ 2)) * f) * Knorm j (ellj d L ℓ₀ j) A K +
          ENNReal.ofReal (Cm + (C₁ + 2 * C₁ ^ 2)) *
            (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V ^ 2 +
              Knorm j (ellj d L ℓ₀ j) A K ^ 2) := by
    intro R hR
    rw [map_add]
    refine (tNorm_add_le _ _).trans (add_le_add (h1.trans ?_) (hR.trans ?_))
    · rw [hk]
      exact mul_le_mul_left (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (by nlinarith) hf0)) _
    · rw [hv, hk, ← ENNReal.ofReal_pow hv0, ← ENNReal.ofReal_pow hk0,
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_mul (by nlinarith [le_max_right Cbar 0])]
      exact ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have hsq : (vr + kr) ^ 2 ≤ 2 * (vr ^ 2 + kr ^ 2) := by nlinarith [sq_nonneg (vr - kr)]
  by_cases hn : nb j X = 1
  · rw [nb] at hn
    obtain ⟨b, hb⟩ := card_eq_one.1 hn
    have hXb : X = blockSet j b := by
      rw [← biUnion_blocks hX.1, hb, singleton_biUnion]
    have hbI : b ∈ blockIdx (d := d) (L := L) (N := N) j :=
      mem_blockIdx_of_mem_blocks (hb ▸ mem_singleton_self b)
    subst hXb
    rw [term_eq_block C V K hbI]
    refine h2 _ ((hdI L ((le_max_left _ _).trans hL) N j hj ℓ₀ hℓ₀ C hC V K A hA hK hvk' b
      hbI).2.trans ?_)
    rw [hv, hk, ← ENNReal.ofReal_pow hv0, ← ENNReal.ofReal_pow hk0,
      ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul hC₁]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by nlinarith) (by positivity))
  · have hn1 : 1 ≤ nb j X := card_pos.2 (hX.2.1.1.image _)
    have hn2 : 2 ≤ nb j X := by omega
    have hnb : ∀ b, X ≠ blockSet j b := fun b h => by
      have := nb_blockSet_le (L := L) (N := N) j b
      rw [← h] at this; omega
    rw [term_eq_nonblock C V K hX hnb]
    refine h2 _ ((tNorm_EC_le hh hℓ hC.psd hC.norm _).trans ((tNorm_prod_le hh hℓ _ _).trans ?_))
    have hx0 : 0 ≤ C₁ * (vr + kr) := by positivity
    have hx1 : C₁ * (vr + kr) ≤ 1 := by
      have h3 : vr + kr ≤ 1 / (C₁ + 1) := hvkr.trans (min_le_right _ _)
      have h4 : (C₁ + 1) * (vr + kr) ≤ 1 := by
        rw [le_div_iff₀ (by positivity)] at h3; linarith
      nlinarith
    calc ∏ b ∈ blocks j X, Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1))
          (dI j C V K b : Grassmann.N (Lam d L N ⊕ Lam d L N))
        ≤ ∏ _b ∈ blocks j X, ENNReal.ofReal (C₁ * (vr + kr)) := by
          refine prod_le_prod' fun b hb => ?_
          refine ((hdI L ((le_max_left _ _).trans hL) N j hj ℓ₀ hℓ₀ C hC V K A hA hK hvk' b
            (mem_blockIdx_of_mem_blocks hb)).1).trans (le_of_eq ?_)
          rw [hv, hk, ← ENNReal.ofReal_add hv0 hk0, ← ENNReal.ofReal_mul hC₁]
      _ = ENNReal.ofReal ((C₁ * (vr + kr)) ^ nb j X) := by
          rw [prod_const, ENNReal.ofReal_pow hx0, nb]
      _ ≤ ENNReal.ofReal ((C₁ + 2 * C₁ ^ 2) * (vr ^ 2 + kr ^ 2)) := by
          refine ENNReal.ofReal_le_ofReal ((pow_le_pow_of_le_one hx0 hx1 hn2).trans ?_)
          rw [mul_pow]
          nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg C₁), sq_nonneg vr, sq_nonneg kr]

end Terms

/-! ### Proposition `prop:SmallSetLin` -/

/-- **Proposition `prop:SmallSetLin`** (and its version for `j + 1 = N`). -/
theorem smallset_bound {d : ℕ} (hd : 3 ≤ d) : ∃ (C₀ : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ (N j : ℕ), j < N → ∀ (ℓ₀ : ℝ), 0 < ℓ₀ →
    ∀ (C : Matrix (Lam d L N) (Lam d L N) ℝ), GoodCov j ℓ₀ C →
    ∀ (V : Vcoup) (K : Act d L N) (A : ℝ), 1 ≤ A → InK j K →
      Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V + Knorm j (ellj d L ℓ₀ j) A K ≤
        ENNReal.ofReal ε₀ →
      ∀ U : Finset (Lam d L N), IsConn (j + 1) U →
        wnorm (j + 1) (ellj d L ℓ₀ (j + 1)) A U (LlinS j C V K U) ≤
          ENNReal.ofReal (C₀ * (if j + 1 < N then (L : ℝ) ^ (-dplus d) else (L : ℝ) ^ d)) *
              Knorm j (ellj d L ℓ₀ j) A K +
            ENNReal.ofReal (C₀ * (L : ℝ) ^ d) *
              (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V ^ 2 +
                Knorm j (ellj d L ℓ₀ j) A K ^ 2) := by
  obtain ⟨C₂, ε₁, L₁, hC₂, hε₁, htb⟩ := term_bound hd
  obtain ⟨c₀, Lp, hc₀, hLp, hpert⟩ := pert12 hd
  obtain ⟨c, hc⟩ := card_small_clo_le d
  refine ⟨c * 2 ^ (2 ^ d) * C₂, max L₁ Lp, by positivity, ?_⟩
  intro L _ hL
  have hL4 : (4 : ℝ) ≤ L := four_le_of_L₀ (hLp.trans ((le_max_right _ _).trans hL))
  have hL0 : (0 : ℝ) < L := by linarith
  refine ⟨min ε₁ (c₀ / (L : ℝ) ^ d), lt_min hε₁ (by positivity), ?_⟩
  intro N j hj ℓ₀ hℓ₀ C hC V K A hA hK hvk U _
  classical
  have hh : (0 : ℝ) < (L : ℝ) ^ (j + 1) := by positivity
  have hℓ := ellj_pos (d := d) hL0 hℓ₀ (j + 1)
  set v := Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V
  set k := Knorm j (ellj d L ℓ₀ j) A K
  set F : Finset (Lam d L N) → EvR (Lam d L N ⊕ Lam d L N) := fun X =>
    thetaE (K X) - ∑ b ∈ blocks j X, thetaE (Jb j K b X) + dIPow j C V K X with hF
  have hLS : LlinS j C V K U = ∑ X ∈ smallSets j,
      if clo j X = U then pref j C V K U X * ECE C (F X) else 0 := by
    rw [LlinS, Lsum, sum_filter, sum_filter, ← sum_add_distrib]
    refine sum_congr rfl fun X hX => ?_
    have hXs : IsSmall j X := (mem_filter.1 hX).2
    by_cases h : clo j X = U
    · rw [if_pos ⟨⟨hXs.1, hXs.2.1⟩, h⟩, if_pos ⟨hXs.1, h⟩, if_pos h, ← mul_add, ← map_add]
    · rw [if_neg (fun h' => h h'.2), if_neg (fun h' => h h'.2), if_neg h, add_zero]
  by_cases hUs : IsSmall (j + 1) U
  swap
  · have h0 : LlinS j C V K U = 0 := by
      rw [hLS]
      refine sum_eq_zero fun X hX => if_neg fun h => hUs ?_
      exact h ▸ isSmall_clo (mem_filter.1 hX).2
    rw [wnorm, h0, ZeroMemClass.coe_zero, Tj_zero, mul_zero]
    exact zero_le
  have hw : nb (j + 1) U - 2 ^ d = 0 := Nat.sub_eq_zero_of_le hUs.2.2
  rw [wnorm, hw, pow_zero, ENNReal.ofReal_one, one_mul, hLS, ← sum_filter]
  set f : ℝ := if j + 1 < N then (L : ℝ) ^ (-(d : ℝ)) * (L : ℝ) ^ (-dplus d) else 1 with hf
  set T := ENNReal.ofReal (C₂ * f) * k + ENNReal.ofReal C₂ * (v ^ 2 + k ^ 2) with hT
  have hsum : ∀ X ∈ (smallSets j).filter (fun X => clo j X = U),
      Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1))
        ((pref j C V K U X * ECE C (F X) : EvR (Lam d L N)) : Alg d L N) ≤ 2 ^ (2 ^ d) * T := by
    intro X hX
    obtain ⟨hXm, hXU⟩ := mem_filter.1 hX
    have hXs : IsSmall j X := (mem_filter.1 hXm).2
    refine (tNorm_mul_le' hh hℓ _ _).trans (mul_le_mul' ?_ ?_)
    · refine (hpert L ((le_max_right _ _).trans hL) N j hj ℓ₀ hℓ₀ C hC V K A hA hK
        (hvk.trans (ENNReal.ofReal_le_ofReal (min_le_right _ _))) X U hXs.1 hXU).trans ?_
      exact pow_le_pow_right₀ one_le_two hXs.2.2
    · exact htb L ((le_max_left _ _).trans hL) N j hj ℓ₀ hℓ₀ C hC V K A hA hK
        (hvk.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _))) X hXs
  have hM : ((c * L ^ d : ℕ) : ENNReal) * 2 ^ (2 ^ d) =
      ENNReal.ofReal ((c : ℝ) * (L : ℝ) ^ d * 2 ^ (2 ^ d)) := by
    rw [ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_natCast]
    push_cast
    rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  have e1 : (c : ℝ) * (L : ℝ) ^ d * 2 ^ (2 ^ d) * (C₂ * f) =
      c * 2 ^ (2 ^ d) * C₂ * (if j + 1 < N then (L : ℝ) ^ (-dplus d) else (L : ℝ) ^ d) := by
    rw [hf]
    split_ifs
    · have : (L : ℝ) ^ d * (L : ℝ) ^ (-(d : ℝ)) = 1 := by
        rw [Real.rpow_neg hL0.le, Real.rpow_natCast, mul_inv_cancel₀ (by positivity)]
      linear_combination (c : ℝ) * 2 ^ (2 ^ d) * C₂ * (L : ℝ) ^ (-dplus d) * this
    · ring
  calc Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1))
        ((∑ X ∈ (smallSets j).filter (fun X => clo j X = U),
          pref j C V K U X * ECE C (F X) : EvR (Lam d L N)) : Alg d L N)
      ≤ ∑ X ∈ (smallSets j).filter (fun X => clo j X = U), Tj d (L : ℝ) (j + 1)
          (ellj d L ℓ₀ (j + 1)) ((pref j C V K U X * ECE C (F X) : EvR (Lam d L N)) :
            Alg d L N) := by
        rw [AddSubmonoidClass.coe_finsetSum]; exact tNorm_sum_le _ _
    _ ≤ ∑ _X ∈ (smallSets j).filter (fun X => clo j X = U), 2 ^ (2 ^ d) * T := sum_le_sum hsum
    _ = ((smallSets j).filter (fun X => clo j X = U)).card * (2 ^ (2 ^ d) * T) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ ((c * L ^ d : ℕ) : ENNReal) * (2 ^ (2 ^ d) * T) :=
        mul_le_mul_left (Nat.cast_le.2 (hc L N j U hUs)) _
    _ = _ := by
        rw [← mul_assoc, hM, hT, mul_add, ← mul_assoc, ← mul_assoc,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), e1]
        congr 3
        ring

end

end Step
