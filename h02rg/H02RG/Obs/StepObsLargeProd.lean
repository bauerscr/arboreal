import Obs.StepObsLargeBlock

/-!
# The observable part of `𝔼 (δI)^X` (products over blocks)
-/

namespace Obs

noncomputable section

open Finset Grassmann SA Loc Step LocObs Gen

variable {d L N : ℕ} [NeZero L]

/-! ### The observable part of `𝔼 (δI)^X` -/

section Prod

variable {c : Case} {ℓ₀ : ℝ} {a b : Lam d L N} (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℝ)
  (Vb : Vcoup) (Vo : Coup c) (K : Finset (Lam d L N) → OE c (Lam d L N))

theorem card_filter_ab_le (s : Finset (Fin d → ℕ)) :
    (s.filter (fun p => a ∈ blockSet (L := L) (N := N) j p ∨ b ∈ blockSet (L := L) (N := N) j p)).card
      ≤ 2 := by
  refine (card_le_card (t := {blk j a, blk j b}) fun p hp => ?_).trans card_le_two
  rcases (mem_filter.1 hp).2 with h | h <;> rw [Loc.mem_blockSet] at h <;> simp [h]

theorem real_pow_aux {q ρ σ : ℝ} (hq : 0 ≤ q) (hqρ : q ≤ ρ) (hσ : 0 ≤ σ) (t k : ℕ) (ht : t ≤ 2)
    (hk : 1 ≤ k) :
    (t : ℝ) * (σ * ρ ^ (t - 1)) * q ^ k ≤ 2 * σ * q * ρ ^ (t + k - 2) := by
  have hρ : 0 ≤ ρ := hq.trans hqρ
  rcases Nat.eq_zero_or_pos t with h0 | h0
  · subst h0; simp; positivity
  · have e1 : q ^ k = q * q ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
    have e2 : t + k - 2 = (t - 1) + (k - 1) := by omega
    have h3 : q ^ (k - 1) ≤ ρ ^ (k - 1) := pow_le_pow_left₀ hq hqρ _
    have ht' : (t : ℝ) ≤ 2 := by exact_mod_cast ht
    rw [e1, e2, pow_add]
    have : 0 ≤ σ * ρ ^ (t - 1) := by positivity
    calc (t : ℝ) * (σ * ρ ^ (t - 1)) * (q * q ^ (k - 1))
        ≤ 2 * (σ * ρ ^ (t - 1)) * (q * ρ ^ (k - 1)) := by gcongr
      _ = 2 * σ * q * (ρ ^ (t - 1) * ρ ^ (k - 1)) := by ring

set_option maxHeartbeats 4000000 in
/-- The observable part of `𝔼 (δI)^X` for `X ∈ 𝒫_j` with `|𝓑_j(X)| ≥ 2`: the blocks without
`a, b` contribute bulk factors, and if `X` consists of the two blocks of `a` and `b` the bound
`Γ` of `e:deltaI-obs-4` is used. -/
theorem n1_πobs_ECO_dIPow_le (hd : 2 ≤ d) (hℓ₀ : 0 < ℓ₀) (hC : GoodCov j ℓ₀ C)
    {X : Finset (Lam d L N)} (hnb : 2 ≤ nb j X) {q σ Γ : ℝ} (hq : 0 ≤ q) (hσ : 0 ≤ σ) (hΓ : 0 ≤ Γ)
    (hbq : ∀ p ∈ blockIdx (L := L) (N := N) j,
      Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1))
        ((bulk (dIoL j C Vb Vo K a b p) : EvR (Lam d L N ⊕ Lam d L N)) :
          Grassmann.N (Lam d L N ⊕ Lam d L N)) ≤ ENNReal.ofReal q)
    (hbσ : ∀ p ∈ blockIdx (L := L) (N := N) j,
      n2 c ℓ₀ a b j (πobs (dIoL j C Vb Vo K a b p)) ≤ ENNReal.ofReal σ)
    (hpair : blk j a ∈ blocks j X → blk j b ∈ blocks j X → blk j a ≠ blk j b →
      nb j X = 2 →
      nrmj c ℓ₀ a b (j + 1)
        (ECO C (πobs (dIoL j C Vb Vo K a b (blk j a)) * πobs (dIoL j C Vb Vo K a b (blk j b)))) ≤
        ENNReal.ofReal Γ) :
    nrmj c ℓ₀ a b (j + 1) (πobs (ECO C (dIPowG (obsA c C) j (obsI j C Vb Vo K a b) X))) ≤
      ENNReal.ofReal ((Γ + 2 * σ * q) * (q + σ) ^ (nb j X - 2)) := by
  classical
  have hh := hpow_pos (L := L) (j + 1)
  have hℓ := Grassmann.ellj_pos (d := d) (L_pos (L := L)) hℓ₀ (j + 1)
  have hw := wj_sub (L := L) hd c hℓ₀ (coal L a b : ℕ∞) (j + 1)
  set f := dIoL j C Vb Vo K a b with hf
  set s := blocks j X with hs
  set pr : (Fin d → ℕ) → Prop :=
    fun p => a ∈ blockSet (L := L) (N := N) j p ∨ b ∈ blockSet (L := L) (N := N) j p with hpr
  set T := s.filter pr with hT
  set Tc := s.filter (fun p => ¬ pr p) with hTc
  have hTcard : T.card ≤ 2 := card_filter_ab_le j s
  have hsplit : T.card + Tc.card = nb j X := by
    rw [hT, hTc, card_filter_add_card_filter_not]; rfl
  have hD : dIPowG (obsA c C) j (obsI j C Vb Vo K a b) X = (∏ p ∈ T, f p) * ∏ p ∈ Tc, f p := by
    rw [dIPowG, bpow, hT, hTc, prod_filter_mul_prod_filter_not]
  -- the factors without observables
  have hemb : ∀ p ∈ Tc, f p = emb (bulk (f p)) := by
    intro p hp
    have hn := (mem_filter.1 hp).2
    simp only [hpr, not_or] at hn
    have h0 := πobs_dIo_eq_zero j C Vb Vo K a b p hn.1 hn.2
    conv_lhs => rw [eq_emb_add_πobs (f p)]
    rw [show πobs (f p) = 0 from h0, add_zero]
  have hY : ∏ p ∈ Tc, f p = emb (∏ p ∈ Tc, bulk (f p)) := by
    rw [map_prod]; exact prod_congr rfl hemb
  have hbY : Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1))
      ((∏ p ∈ Tc, bulk (f p) : EvR (Lam d L N ⊕ Lam d L N)) : Grassmann.N (Lam d L N ⊕ Lam d L N))
      ≤ ENNReal.ofReal (q ^ Tc.card) := by
    refine (tNorm_prod_le hh hℓ _ _).trans ((prod_le_prod' fun p hp => hbq p
      (mem_blockIdx_of_mem_blocks (mem_filter.1 hp).1)).trans ?_)
    rw [prod_const, ENNReal.ofReal_pow hq]
  have hπ : πobs ((∏ p ∈ T, f p) * ∏ p ∈ Tc, f p) =
      πobs (∏ p ∈ T, f p) * emb (∏ p ∈ Tc, bulk (f p)) := by
    rw [πobs_mul_eq, hY, πobs_emb, mul_zero, zero_add, bulk_emb]
  have hρ : ∀ p ∈ T, n2 c ℓ₀ a b j (f p) ≤ ENNReal.ofReal (q + σ) := by
    intro p hp
    have hp' := mem_blockIdx_of_mem_blocks (mem_filter.1 hp).1
    refine (le_of_eq (oT_split (f p))).trans ?_
    rw [ENNReal.ofReal_add hq hσ]
    exact add_le_add (hbq p hp') (hbσ p hp')
  have hZ : n2 c ℓ₀ a b j (πobs (∏ p ∈ T, f p)) ≤
      ENNReal.ofReal (T.card * (σ * (q + σ) ^ (T.card - 1))) := by
    refine (oT_πobs_prod_le hh hℓ hw T f (fun _ => ENNReal.ofReal (q + σ)) (fun _ => ENNReal.ofReal σ)
      hρ (fun p hp => hbσ p (mem_blockIdx_of_mem_blocks (mem_filter.1 hp).1))).trans (le_of_eq ?_)
    rw [sum_congr rfl fun i hi => by rw [prod_const, card_erase_of_mem hi], sum_const,
      nsmul_eq_mul, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul hσ,
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  rw [hD, πobs_ECOL]
  by_cases hk : 1 ≤ Tc.card
  · refine (n1_ECO_le hℓ₀ hC _).trans ?_
    rw [hπ]
    refine (oT_mul_le hh hℓ hw _ _).trans ?_
    rw [oT_emb]
    refine (mul_le_mul' hZ hbY).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := real_pow_aux hq (le_add_of_nonneg_right hσ) hσ T.card Tc.card hTcard hk
    rw [hsplit] at this
    nlinarith [pow_nonneg (add_nonneg hq hσ) (nb j X - 2)]
  · -- `X` consists of the blocks of `a` and `b`
    have hTc0 : Tc.card = 0 := by omega
    have hT2 : T.card = 2 := by omega
    have hnb2 : nb j X = 2 := by omega
    have hTsub : T ⊆ {blk j a, blk j b} := fun p hp => by
      rcases (mem_filter.1 hp).2 with h | h <;> rw [Loc.mem_blockSet] at h <;> simp [h]
    have hTeq : T = {blk j a, blk j b} :=
      eq_of_subset_of_card_le hTsub (card_le_two.trans hT2.ge)
    have hne : blk j a ≠ blk j b := by
      intro h
      have := card_le_card hTsub
      rw [h] at this
      simp at this
      omega
    have hTc' : Tc = ∅ := card_eq_zero.1 hTc0
    have hsT : s = T := by
      have := filter_union_filter_not_eq pr s
      rw [← hT, ← hTc, hTc', union_empty] at this
      exact this.symm
    have ha : blk j a ∈ blocks j X := by rw [← hs, hsT, hTeq]; exact mem_insert_self _ _
    have hb : blk j b ∈ blocks j X := by
      rw [← hs, hsT, hTeq]; exact mem_insert_of_mem (mem_singleton_self _)
    rw [hTc', prod_empty, mul_one, hTeq, prod_pair hne, πobs_mul, map_add, map_add]
    have hpa := mem_blockIdx_of_mem_blocks ha
    have hpb := mem_blockIdx_of_mem_blocks hb
    have t1 : nrmj c ℓ₀ a b (j + 1) (ECO C (emb (bulk (f (blk j a))) * πobs (f (blk j b)))) ≤
        ENNReal.ofReal (q * σ) := by
      refine (n1_ECO_le hℓ₀ hC _).trans ((oT_mul_le hh hℓ hw _ _).trans ?_)
      rw [oT_emb, ENNReal.ofReal_mul hq]
      exact mul_le_mul' (hbq _ hpa) (hbσ _ hpb)
    have t3 : nrmj c ℓ₀ a b (j + 1) (ECO C (πobs (f (blk j a)) * emb (bulk (f (blk j b))))) ≤
        ENNReal.ofReal (σ * q) := by
      refine (n1_ECO_le hℓ₀ hC _).trans ((oT_mul_le hh hℓ hw _ _).trans ?_)
      rw [oT_emb, ENNReal.ofReal_mul hσ]
      exact mul_le_mul' (hbσ _ hpa) (hbq _ hpb)
    refine (nrmj_add_le _ _ _).trans ((add_le_add ((nrmj_add_le _ _ _).trans
      (add_le_add t1 t3)) (hpair ha hb hne hnb2)).trans (le_of_eq ?_))
    rw [hnb2, Nat.sub_self, pow_zero, mul_one, ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) hΓ]
    congr 1; ring

end Prod

end

end Obs
