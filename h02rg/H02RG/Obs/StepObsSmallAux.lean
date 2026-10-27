import Obs.StepObsSmallComb

/-!
# Small sets for `thm:step-obs`: counting and prefactor bounds

* `card_Iset`: `|I(U)| ≤ c L^d + (2^d L^d)^2`;
* `nb_Iset`: `|𝓑_j(X)| ≤ 2^d` and `|𝓑_{j+1}(U)| ≤ 2^d` for `X ∈ I(U)`;
* `πobs_pref_bound`: `‖π_obs e^{u(U)} e^{-(u+V)(U∖X)}‖ ≤ 2^{|𝓑_j(X)|} (e^{w} - 1)`;
* `bulkT_bound`: the bulk part of the summands.
-/

namespace Obs

noncomputable section

open Finset Grassmann SA Loc Step LocObs Gen

variable {d L N : ℕ} [NeZero L]

section Aux

variable {c : Case} {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℝ} {Vb : Vcoup} {Vo : Coup c}
  {K : Finset (Lam d L N) → OE c (Lam d L N)} {a b : Lam d L N} {ℓ₀ : ℝ}

theorem nb_Iset (hd : 1 ≤ d) {U X : Finset (Lam d L N)} (hX : X ∈ Iset j U) :
    nb j X ≤ 2 ^ d ∧ nb (j + 1) U ≤ 2 ^ d := by
  obtain ⟨hcl, -, -, hs⟩ := mem_Iset hX
  have h1 : nb j X ≤ 2 ^ d := by
    rcases hs with hs | hs
    · exact hs.2.2
    · rw [hs.1]
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
  exact ⟨h1, hcl ▸ (nb_clo_le j X).trans h1⟩

theorem card_Iset (d : ℕ) (hd : 1 ≤ d) : ∃ c₁ : ℕ, ∀ (L : ℕ) [NeZero L] (N j : ℕ)
    (U : Finset (Lam d L N)), IsPolymer (j + 1) U →
      (Iset j U).card ≤ c₁ * L ^ d + (L ^ d) ^ 2 := by
  classical
  obtain ⟨cc, hcc⟩ := card_small_clo_le d
  refine ⟨cc, fun L _ N j U hU => ?_⟩
  refine (card_union_le _ _).trans (add_le_add ?_ ?_)
  · by_cases h : (smU j U).Nonempty
    · obtain ⟨X₀, hX₀⟩ := h
      have hX₀' : IsSmall j X₀ ∧ clo j X₀ = U := by
        simp only [smU, mem_filter, mem_smallSets] at hX₀; exact hX₀
      exact hcc L N j U (hX₀'.2 ▸ isSmall_clo hX₀'.1)
    · rw [not_nonempty_iff_eq_empty.1 h]; simp
  · by_cases h : (pairSets j U).Nonempty
    · obtain ⟨X₀, hX₀⟩ := h
      simp only [pairSets, mem_filter, mem_univ, true_and] at hX₀
      have hnbU : nb (j + 1) U = 1 := by rw [← hX₀.2.1, nb, blocks_clo]; exact hX₀.2.2.2.1
      have hnbj : nb j U ≤ L ^ d := by
        have := nb_le_of_succ hU
        rw [hnbU, mul_one] at this; exact this
      have hsub : pairSets j U ⊆ (blocks j U ×ˢ blocks j U).image
          (fun pq => blockSet (L := L) (N := N) j pq.1 ∪ blockSet j pq.2) := by
        intro X hX
        simp only [pairSets, mem_filter, mem_univ, true_and] at hX
        obtain ⟨p, q, -, hpq⟩ := card_eq_two.1 hX.2.2.1
        have hXU : X ⊆ U := hX.2.1 ▸ subset_clo j X
        have hp : p ∈ blocks j U := blocks_mono hXU (hpq ▸ by simp)
        have hq : q ∈ blocks j U := blocks_mono hXU (hpq ▸ by simp)
        refine mem_image.2 ⟨(p, q), mem_product.2 ⟨hp, hq⟩, ?_⟩
        rw [← biUnion_blocks hX.1, hpq]; simp
      refine (card_le_card hsub).trans (card_image_le.trans ?_)
      rw [card_product, ← sq]
      exact Nat.pow_le_pow_left hnbj 2
    · rw [not_nonempty_iff_eq_empty.1 h]; simp

/-- `‖π_obs (e^{u(U)} e^{-(u+V)(U ∖ X)})‖ ≤ 2^{|𝓑_j(X)|} (e^w - 1)` if `‖W‖ ≤ w`. -/
theorem πobs_pref_bound (hd : 2 ≤ d) (hℓ₀ : 0 < ℓ₀) {U X : Finset (Lam d L N)}
    (hU : IsPolymer j U) (hX : IsPolymer j X) {w : ℝ} (hw : 0 ≤ w)
    (hβ : Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1))
      ((pref j C Vb (bulkK K) U X : EvR (Lam d L N)) : Alg d L N) ≤ 2 ^ nb j X)
    (hW : nrmj c ℓ₀ a b (j + 1) (uObsX j C Vo K a b U -
      splitO c (nextObs C j Vo K a b) a b (U \ X)) ≤ ENNReal.ofReal w) :
    nrmj c ℓ₀ a b (j + 1) (πobs (prefG j (obsI j C Vb Vo K a b) U X)) ≤
      2 ^ nb j X * ENNReal.ofReal (Real.exp w - 1) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hh : (0 : ℝ) < (L : ℝ) ^ (j + 1) := by positivity
  rw [πobs_prefG j C Vb Vo K a b hU (IsPolymer.sdiff hU hX)]
  refine (nrmj_mul_le hd hℓ₀ _ _ _).trans (mul_le_mul' ?_ ?_)
  · rw [nrmj_emb, bulk_prefG j C Vb Vo K a b U X hU]; exact hβ
  · have hWb : bulk (uObsX j C Vo K a b U - splitO c (nextObs C j Vo K a b) a b (U \ X)) = 0 := by
      rw [map_sub, bulk_uObsX, bulk_splitO, sub_zero]
    exact oT_oexp_sub_one_le hh (ellj_pos hL0 hℓ₀ _) (wj_sub hd c hℓ₀ _ _)
      (ε_bulk_eq_zero_of_obs hWb) hw hW

/-- The bulk part of a small-set summand is Step's summand. -/
theorem bulk_TX_small {X : Finset (Lam d L N)} (hX : IsConn j X) :
    ((bulk (TX j C Vb Vo K a b X) : EvR (Lam d L N)) : Alg d L N) =
      EC C ((thetaE (bulkK K X) - ∑ p ∈ blocks j X, thetaE (Jb j (bulkK K) p X) +
        dIPow j C Vb (bulkK K) X : EvR (Lam d L N ⊕ Lam d L N)) :
          Grassmann.N (Lam d L N ⊕ Lam d L N)) := by
  rw [TX, if_pos hX, bulk_ECO, coe_ECE]
  congr 2
  rw [map_add, map_sub, map_sum, bulk_thetaO, bulk_dIPowG]
  simp only [bulk_thetaO, bulk_JO]
  rfl

theorem bulk_TX_pair {X : Finset (Lam d L N)} (hX : ¬ IsConn j X) :
    ((bulk (TX j C Vb Vo K a b X) : EvR (Lam d L N)) : Alg d L N) =
      EC C ((dIPow j C Vb (bulkK K) X : EvR (Lam d L N ⊕ Lam d L N)) :
          Grassmann.N (Lam d L N ⊕ Lam d L N)) := by
  rw [TX, if_neg hX, bulk_ECO, coe_ECE, bulk_dIPowG]

end Aux

/-- The real bookkeeping of the remainder. -/

theorem real_R {W M K₂ t s ko vo : ℝ} (n : ℕ) (hW1 : 1 ≤ W) (hM1 : 1 ≤ M) (hK1 : 1 ≤ K₂)
    (hMK : M * K₂ = W) (ht : 0 ≤ t) (hko0 : 0 ≤ ko) (hvo0 : 0 ≤ vo)
    (hvo : vo ≤ s) (hko : ko ≤ s) :
    K₂ * (M * ko * (2 * vo + M * ko)) + W * s * t +
      ((M * t) * (5 * W * s) + (5 * W * s) * (M * t) + (3 * W * s) * (W * (ko + t)) +
        (W * (ko + t)) * (3 * W * s) + (W * (ko + t)) * (W * (ko + t))) +
      (M * t) * (2 ^ n * (5 * W * s)) ≤ 30 * 2 ^ n * W ^ 3 * ((ko + t) * (t + s)) := by
  have hs0 : 0 ≤ s := hko0.trans hko
  have hK0 : 0 ≤ K₂ := by linarith
  set Q := (ko + t) * (t + s) with hQ
  have hP1 : ko * (t + s) ≤ Q := by rw [hQ]; gcongr; linarith
  have hP2 : t * s ≤ Q := by rw [hQ]; gcongr <;> linarith
  have hP3 : s * (ko + t) ≤ Q := by rw [hQ, mul_comm]; gcongr; linarith
  have hP4 : (ko + t) * (ko + t) ≤ Q := by
    rw [hQ]; exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hQ0 : 0 ≤ Q := by positivity
  have hW0 : 0 ≤ W := by linarith
  have hMW : M ≤ W := by
    rw [← hMK]; nlinarith
  have hKW : K₂ ≤ W := by rw [← hMK]; nlinarith [mul_le_mul_of_nonneg_right hM1 hK0]
  have hW2 : W ≤ W ^ 2 := by nlinarith
  have hW3 : W ^ 2 ≤ W ^ 3 := by nlinarith
  have hn : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have e1 : K₂ * (M * ko * (2 * vo + M * ko)) ≤ 3 * W ^ 3 * Q := by
    have h1 : 2 * vo + M * ko ≤ 3 * M * (t + s) := by nlinarith
    have h2 : K₂ * M * M ≤ W ^ 3 := by
      rw [show K₂ * M * M = W * M by rw [← hMK]; ring]; nlinarith
    calc K₂ * (M * ko * (2 * vo + M * ko)) ≤ K₂ * (M * ko * (3 * M * (t + s))) := by gcongr
      _ = 3 * (K₂ * M * M) * (ko * (t + s)) := by ring
      _ ≤ 3 * W ^ 3 * Q := by gcongr
  have e2 : W * s * t ≤ W ^ 3 * Q := by
    calc W * s * t = W * (t * s) := by ring
      _ ≤ W * Q := by gcongr
      _ ≤ W ^ 3 * Q := by gcongr; linarith
  have e3 : (M * t) * (5 * W * s) + (5 * W * s) * (M * t) ≤ 10 * W ^ 3 * Q := by
    calc (M * t) * (5 * W * s) + (5 * W * s) * (M * t) = 10 * (M * W) * (t * s) := by ring
      _ ≤ 10 * (W * W) * Q := by gcongr
      _ ≤ 10 * W ^ 3 * Q := by gcongr; nlinarith
  have e4 : (3 * W * s) * (W * (ko + t)) + (W * (ko + t)) * (3 * W * s) ≤ 6 * W ^ 3 * Q := by
    calc (3 * W * s) * (W * (ko + t)) + (W * (ko + t)) * (3 * W * s) =
        6 * W ^ 2 * (s * (ko + t)) := by ring
      _ ≤ 6 * W ^ 3 * Q := by gcongr
  have e5 : (W * (ko + t)) * (W * (ko + t)) ≤ W ^ 3 * Q := by
    calc (W * (ko + t)) * (W * (ko + t)) = W ^ 2 * ((ko + t) * (ko + t)) := by ring
      _ ≤ W ^ 3 * Q := by gcongr
  have e6 : (M * t) * (2 ^ n * (5 * W * s)) ≤ 5 * 2 ^ n * W ^ 3 * Q := by
    calc (M * t) * (2 ^ n * (5 * W * s)) = 5 * 2 ^ n * (M * W) * (t * s) := by ring
      _ ≤ 5 * 2 ^ n * (W * W) * Q := by gcongr
      _ ≤ 5 * 2 ^ n * W ^ 3 * Q := by gcongr; nlinarith
  have hWQ : 0 ≤ W ^ 3 * Q := by positivity
  nlinarith


/-- The final real bookkeeping. -/

theorem final_real {G Cl C₂ M W K₂ LL c₁ cs n f f' t s ko vo π Q : ℝ} (dd : ℕ)
    (hG1 : 1 ≤ G) (hCl : 0 ≤ Cl) (hC₂ : 0 ≤ C₂) (hM1 : 1 ≤ M) (hK1 : 1 ≤ K₂) (hW : W = M * K₂)
    (hLL1 : 1 ≤ LL) (hKLL : K₂ ≤ LL ^ 2) (hc₁ : 0 ≤ c₁) (hcs : 0 ≤ cs) (hn0 : 0 ≤ n)
    (hn : n ≤ (c₁ + 1) * LL ^ 2) (hf : f' ≤ f) (hf'0 : 0 ≤ f') (ht0 : 0 ≤ t) (hko0 : 0 ≤ ko)
    (hvo0 : 0 ≤ vo) (hvo : vo ≤ s) (hko : ko ≤ s) (hsv : vo + ko ≤ s) (hs1 : s ≤ 1)
    (hπ : π = 2 * K₂ ^ 2 * (vo + M * ko) * (vo + M * ko)) (hQ : Q = (ko + t) * (t + s)) :
    2 * cs * (G * (Cl * f' * ko)) + n * (G * (30 * 2 ^ dd * W ^ 3 * Q)) +
        2 * (4 * (M * t) * π) + n * (G * (4 * (W * s)) * ((3 * C₂ + M ^ 2) * t)) ≤
      (2 * cs * G * (max Cl 0 + 1) +
          ((c₁ + 1) * (G * (30 * 2 ^ dd) + G * 4 * (3 * C₂ + M ^ 2)) + 16) * M ^ 5) * f * ko +
        (2 * cs * G * (max Cl 0 + 1) +
          ((c₁ + 1) * (G * (30 * 2 ^ dd) + G * 4 * (3 * C₂ + M ^ 2)) + 16) * M ^ 5) *
          LL ^ 12 * Q := by
  have hs0 : 0 ≤ s := hko0.trans hko
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  have hts : t * s ≤ Q := by rw [hQ]; nlinarith [mul_nonneg hko0 ht0, mul_nonneg hko0 hs0, sq_nonneg t]
  have hM0 : 0 ≤ M := by linarith
  have hK0 : 0 ≤ K₂ := by linarith
  have hW1 : 1 ≤ W := by rw [hW]; nlinarith
  have hW0 : 0 ≤ W := by linarith
  have hMW : M ≤ W := by rw [hW]; nlinarith
  have hf0 : 0 ≤ f := hf'0.trans hf
  -- the `f` part
  have e1 : 2 * cs * (G * (Cl * f' * ko)) ≤ 2 * cs * G * (max Cl 0 + 1) * f * ko := by
    have : Cl ≤ max Cl 0 + 1 := by linarith [le_max_left Cl 0]
    have h1 : Cl * f' ≤ (max Cl 0 + 1) * f := mul_le_mul this hf hf'0 (by positivity)
    have h2 : 0 ≤ 2 * cs * G := by positivity
    calc 2 * cs * (G * (Cl * f' * ko)) = (2 * cs * G) * (Cl * f') * ko := by ring
      _ ≤ (2 * cs * G) * ((max Cl 0 + 1) * f) * ko := by gcongr
      _ = _ := by ring
  -- the `Q` part
  have hWs : W * s * t ≤ W ^ 3 * Q := by
    have : W ≤ W ^ 3 := by nlinarith [mul_nonneg hW0 (by nlinarith : (0:ℝ) ≤ W ^ 2 - 1)]
    calc W * s * t = W * (t * s) := by ring
      _ ≤ W * Q := by gcongr
      _ ≤ W ^ 3 * Q := by gcongr
  have hπ' : π ≤ 2 * W ^ 2 * s ^ 2 := by
    have h1 : vo + M * ko ≤ M * s := by
      nlinarith [mul_le_mul_of_nonneg_right hM1 hvo0, mul_le_mul_of_nonneg_left hsv hM0]
    have h0 : 0 ≤ vo + M * ko := by positivity
    rw [hπ, hW]
    have : (vo + M * ko) * (vo + M * ko) ≤ (M * s) * (M * s) := mul_le_mul h1 h1 h0 (by positivity)
    have hK2 : 0 ≤ 2 * K₂ ^ 2 := by positivity
    calc 2 * K₂ ^ 2 * (vo + M * ko) * (vo + M * ko) = 2 * K₂ ^ 2 * ((vo + M * ko) * (vo + M * ko)) := by
          ring
      _ ≤ 2 * K₂ ^ 2 * ((M * s) * (M * s)) := by gcongr
      _ = 2 * (M * K₂) ^ 2 * s ^ 2 := by ring
  have e2 : 2 * (4 * (M * t) * π) ≤ 16 * W ^ 3 * Q := by
    have h1 : 2 * (4 * (M * t) * π) ≤ 2 * (4 * (M * t) * (2 * W ^ 2 * s ^ 2)) := by gcongr
    have h2 : M * t * (W ^ 2 * s ^ 2) ≤ W ^ 3 * (t * s) := by
      have hs2 : s ^ 2 ≤ s := pow_le_of_le_one hs0 hs1 (by norm_num)
      calc M * t * (W ^ 2 * s ^ 2) ≤ W * t * (W ^ 2 * s) := by gcongr
        _ = W ^ 3 * (t * s) := by ring
    have h3 : W ^ 3 * (t * s) ≤ W ^ 3 * Q := by gcongr
    have h4 : 2 * (4 * (M * t) * (2 * W ^ 2 * s ^ 2)) = 16 * (M * t * (W ^ 2 * s ^ 2)) := by ring
    linarith
  have e3 : G * (4 * (W * s)) * ((3 * C₂ + M ^ 2) * t) ≤ G * 4 * (3 * C₂ + M ^ 2) * (W ^ 3 * Q) := by
    calc G * (4 * (W * s)) * ((3 * C₂ + M ^ 2) * t) = G * 4 * (3 * C₂ + M ^ 2) * (W * s * t) := by
          ring
      _ ≤ _ := by gcongr
  set B : ℝ := G * (30 * 2 ^ dd) + G * 4 * (3 * C₂ + M ^ 2) with hB
  have hB0 : 0 ≤ B := by positivity
  have e4 : n * (G * (30 * 2 ^ dd * W ^ 3 * Q)) +
      n * (G * (4 * (W * s)) * ((3 * C₂ + M ^ 2) * t)) ≤ n * B * (W ^ 3 * Q) := by
    have : n * (G * (4 * (W * s)) * ((3 * C₂ + M ^ 2) * t)) ≤
        n * (G * 4 * (3 * C₂ + M ^ 2) * (W ^ 3 * Q)) := by gcongr
    have e : n * B * (W ^ 3 * Q) = n * (G * (30 * 2 ^ dd * W ^ 3 * Q)) +
        n * (G * 4 * (3 * C₂ + M ^ 2) * (W ^ 3 * Q)) := by rw [hB]; ring
    linarith
  -- powers of `LL`
  have hW3 : W ^ 3 ≤ M ^ 3 * LL ^ 6 := by
    have : W ≤ M * LL ^ 2 := by rw [hW]; gcongr
    calc W ^ 3 ≤ (M * LL ^ 2) ^ 3 := by gcongr
      _ = M ^ 3 * LL ^ 6 := by ring
  have hM35 : M ^ 3 ≤ M ^ 5 := pow_le_pow_right₀ hM1 (by norm_num)
  have hL6 : LL ^ 6 ≤ LL ^ 12 := pow_le_pow_right₀ hLL1 (by norm_num)
  have hL8 : LL ^ 8 ≤ LL ^ 12 := pow_le_pow_right₀ hLL1 (by norm_num)
  have e5 : n * B * (W ^ 3 * Q) ≤ (c₁ + 1) * B * M ^ 5 * LL ^ 12 * Q := by
    have h1 : n * W ^ 3 ≤ (c₁ + 1) * M ^ 5 * LL ^ 12 := by
      calc n * W ^ 3 ≤ ((c₁ + 1) * LL ^ 2) * (M ^ 3 * LL ^ 6) := by gcongr
        _ = (c₁ + 1) * M ^ 3 * LL ^ 8 := by ring
        _ ≤ (c₁ + 1) * M ^ 5 * LL ^ 12 := by gcongr
    calc n * B * (W ^ 3 * Q) = B * Q * (n * W ^ 3) := by ring
      _ ≤ B * Q * ((c₁ + 1) * M ^ 5 * LL ^ 12) := by gcongr
      _ = _ := by ring
  have e6 : 16 * W ^ 3 * Q ≤ 16 * M ^ 5 * LL ^ 12 * Q := by
    have : W ^ 3 ≤ M ^ 5 * LL ^ 12 :=
      hW3.trans (mul_le_mul hM35 hL6 (by positivity) (by positivity))
    have e : 16 * M ^ 5 * LL ^ 12 * Q = 16 * (M ^ 5 * LL ^ 12) * Q := by ring
    rw [e]; gcongr
  have e7 : 0 ≤ 2 * cs * G * (max Cl 0 + 1) * LL ^ 12 * Q := by positivity
  have e8 : 0 ≤ ((c₁ + 1) * B + 16) * M ^ 5 * f * ko := by positivity
  have e9 : (2 * cs * G * (max Cl 0 + 1) + ((c₁ + 1) * B + 16) * M ^ 5) * f * ko =
      2 * cs * G * (max Cl 0 + 1) * f * ko + ((c₁ + 1) * B + 16) * M ^ 5 * f * ko := by ring
  have e10 : (2 * cs * G * (max Cl 0 + 1) + ((c₁ + 1) * B + 16) * M ^ 5) * LL ^ 12 * Q =
      2 * cs * G * (max Cl 0 + 1) * LL ^ 12 * Q + (c₁ + 1) * B * M ^ 5 * LL ^ 12 * Q +
        16 * M ^ 5 * LL ^ 12 * Q := by ring
  rw [e9, e10]
  linarith

end

end Obs
