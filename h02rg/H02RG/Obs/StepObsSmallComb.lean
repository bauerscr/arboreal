import Obs.StepObsSmallEst

/-!
# Small sets for `thm:step-obs`: the combined sum and its decomposition

`π_obs (𝓛_𝒮(U) + 𝓛_pair(U)) = ∑_{X ∈ I(U)} π_obs (e^{u(U)} e^{-(u+V)(U∖X)} T(X))` with
`I(U) = {X ∈ 𝒮_j : X̄ = U} ∪ pairSets j U` (`sumS_eq`), and for each summand
`π_obs (pre T) = pre (Lt + r) + e^{…^∅} m + π_obs(pre) T_∅` (`term_decomp`), where
`Lt = 𝔼 θ π_obs (1 - Loc) K(X)`, `m` is the `P^obs` part (`e:Kblock-obs`, `lem:Pjj+1`) and `r` is
the remainder.
-/

namespace Obs

noncomputable section

open Finset Grassmann SA Loc Step LocObs Gen

variable {d L N : ℕ} [NeZero L]

section Comb

variable {c : Case} (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (Vb : Vcoup) (Vo : Coup c)
  (K : Finset (Lam d L N) → OE c (Lam d L N)) (a b : Lam d L N)

/-- The small sets with closure `U`. -/
def smU (U : Finset (Lam d L N)) : Finset (Finset (Lam d L N)) :=
  open Classical in (smallSets j).filter (fun X => clo j X = U)

/-- The index set `I(U)`. -/
def Iset (U : Finset (Lam d L N)) : Finset (Finset (Lam d L N)) := smU j U ∪ pairSets j U

/-- The summand `T(X)`. -/
def TX (X : Finset (Lam d L N)) : OE c (Lam d L N) :=
  open Classical in
  if IsConn j X then
    ECO C (thetaO (K X) - ∑ p ∈ blocks j X, thetaO (JO a b j K p X) +
      dIPowG (obsA c C) j (obsI j C Vb Vo K a b) X)
  else ECO C (dIPowG (obsA c C) j (obsI j C Vb Vo K a b) X)

/-- The `(1 - Loc) K` part. -/
def LtX (X : Finset (Lam d L N)) : OE c (Lam d L N) :=
  open Classical in
  if IsConn j X then ECO C (thetaO (πobs (K X - LocCO j a b X (K X)))) else 0

/-- The `P^obs` part. -/
def mX (X : Finset (Lam d L N)) : OE c (Lam d L N) :=
  if nb j X = 1 then
    -∑ q ∈ blocks j X, ∑ q' ∈ (blockIdx (L := L) (N := N) j).erase q, PobsBB C j Vo K a b q q'
  else if nb j X = 2 then
    ∑ q ∈ blocks j X, ∑ q' ∈ (blocks j X).erase q, PobsBB C j Vo K a b q q'
  else 0

theorem isAB_PobsBB (p p' : Fin d → ℕ) : IsAB (PobsBB C j Vo K a b p p') :=
  (isAB_ECT C (bulk_Vhat j Vo K a b p) (bulk_Vhat j Vo K a b p')).smul _

theorem isAB_sum {ι : Type*} (s : Finset ι) (f : ι → OE c (Lam d L N)) (h : ∀ i ∈ s, IsAB (f i)) :
    IsAB (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simp, by simp, by simp⟩
  | insert i s hi ih =>
    rw [sum_insert hi]
    exact (h i (mem_insert_self i s)).add (ih fun k hk => h k (mem_insert_of_mem hk))

theorem isAB_mX (X : Finset (Lam d L N)) : IsAB (mX j C Vo K a b X) := by
  unfold mX
  split_ifs
  · have := isAB_sum (blocks j X) (fun q => ∑ q' ∈ (blockIdx (L := L) (N := N) j).erase q,
      PobsBB C j Vo K a b q q') fun q _ => isAB_sum _ _ fun q' _ => isAB_PobsBB j C Vo K a b q q'
    rw [← zero_sub]
    have h0 : IsAB (0 : OE c (Lam d L N)) := ⟨by simp, by simp, by simp⟩
    exact IsAB.sub h0 this
  · exact isAB_sum (blocks j X) (fun q => ∑ q' ∈ (blocks j X).erase q,
      PobsBB C j Vo K a b q q') fun q _ => isAB_sum _ _ fun q' _ => isAB_PobsBB j C Vo K a b q q'
  · exact ⟨by simp, by simp, by simp⟩

theorem disjoint_smU_pair (U : Finset (Lam d L N)) : Disjoint (smU j U) (pairSets j U) := by
  classical
  rw [Finset.disjoint_left]
  intro X h1 h2
  simp only [smU, mem_filter, mem_smallSets] at h1
  simp only [pairSets, mem_filter, mem_univ, true_and] at h2
  exact h2.2.2.2.2 h1.1.2.1

theorem sumS_eq (U : Finset (Lam d L N)) :
    LlinSG (obsA c C) j (obsI j C Vb Vo K a b) U + LpairG (obsA c C) j (obsI j C Vb Vo K a b) U =
      ∑ X ∈ Iset j U, prefG j (obsI j C Vb Vo K a b) U X * TX j C Vb Vo K a b X := by
  classical
  rw [Iset, sum_union (disjoint_smU_pair j U)]
  congr 1
  · rw [LlinSG, LsumG]
    have h1 : (smallSets (L := L) (N := N) j).filter (fun X => IsConn j X ∧ clo j X = U) =
        smU j U := by
      unfold smU
      refine filter_congr fun X hX => ?_
      have := mem_smallSets.1 hX
      exact ⟨fun h => h.2, fun h => ⟨⟨this.1, this.2.1⟩, h⟩⟩
    have h2 : (smallSets (L := L) (N := N) j).filter (fun X => IsPolymer j X ∧ clo j X = U) =
        smU j U := by
      unfold smU
      refine filter_congr fun X hX => ?_
      have := mem_smallSets.1 hX
      exact ⟨fun h => h.2, fun h => ⟨this.1, h⟩⟩
    rw [h1, h2, ← sum_add_distrib]
    refine sum_congr rfl fun X hX => ?_
    have hX' : IsConn j X := by
      simp only [smU, mem_filter, mem_smallSets] at hX
      exact ⟨hX.1.1, hX.1.2.1⟩
    rw [← mul_add, TX, if_pos hX', map_add]
    rfl
  · rw [LpairG]
    refine sum_congr rfl fun X hX => ?_
    have hX' : ¬ IsConn j X := by
      simp only [pairSets, mem_filter, mem_univ, true_and] at hX
      exact fun h => hX.2.2.2.2 h.2
    rw [TX, if_neg hX']
    rfl

/-- The decomposition of one summand. -/
theorem term_decomp (U X : Finset (Lam d L N)) :
    πobs (prefG j (obsI j C Vb Vo K a b) U X * TX j C Vb Vo K a b X) =
      prefG j (obsI j C Vb Vo K a b) U X * (LtX j C K a b X +
          (πobs (TX j C Vb Vo K a b X) - LtX j C K a b X - mX j C Vo K a b X)) +
        emb (bulk (prefG j (obsI j C Vb Vo K a b) U X)) * mX j C Vo K a b X +
        πobs (prefG j (obsI j C Vb Vo K a b) U X) * emb (bulk (TX j C Vb Vo K a b X)) := by
  rw [πobs_mul', ← (isAB_mX j C Vo K a b X).mul_eq_emb]
  ring

end Comb

/-! ### The remainder of one summand -/

section RBound

variable {c : Case} {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℝ} {Vb : Vcoup} {Vo : Coup c}
  {K : Finset (Lam d L N) → OE c (Lam d L N)} {a b : Lam d L N} {ℓ₀ : ℝ}

theorem mem_Iset {U X : Finset (Lam d L N)} (hX : X ∈ Iset j U) :
    clo j X = U ∧ IsPolymer j X ∧ X.Nonempty ∧
      (IsSmall j X ∨ (nb j X = 2 ∧ ¬ IsConnected j X)) := by
  classical
  rcases mem_union.1 hX with h | h
  · simp only [smU, mem_filter, mem_smallSets] at h
    exact ⟨h.2, h.1.1, h.1.2.1.1, Or.inl h.1⟩
  · simp only [pairSets, mem_filter, mem_univ, true_and] at h
    refine ⟨h.2.1, h.1, ?_, Or.inr ⟨h.2.2.1, h.2.2.2.2⟩⟩
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    have := h.2.2.1
    simp [nb, blocks] at this

theorem eq_blockSet_of_nb_one {X : Finset (Lam d L N)} (hX : IsPolymer j X) (h : nb j X = 1) :
    ∃ q, blocks j X = {q} ∧ X = blockSet j q ∧ q ∈ blockIdx (L := L) (N := N) j := by
  obtain ⟨q, hq⟩ := card_eq_one.1 h
  have hXq : X = blockSet j q := by rw [← biUnion_blocks hX, hq, singleton_biUnion]
  exact ⟨q, hq, hXq, mem_blockIdx_of_mem_blocks (hq ▸ mem_singleton_self q)⟩

set_option maxHeartbeats 4000000 in
/-- **The remainder bound** for one summand, given block bounds. -/
theorem r_bound (hd : 3 ≤ d) (hL : (4 : ℝ) ≤ L) (hℓ₀ : 0 < ℓ₀) {P : Prop}
    (h : StepObsHyp c P j ℓ₀ C Vb Vo K a b)
    {e o α y vo q ρ : ℝ} (he0 : 0 ≤ e) (ho0 : 0 ≤ o) (hα0 : 0 ≤ α) (hy0 : 0 ≤ y) (hvo : 0 ≤ vo)
    (hq0 : 0 ≤ q) (hρ0 : 0 ≤ ρ)
    (hbl : ∀ p ∈ blockIdx (L := L) (N := N) j,
      nrmD c ℓ₀ a b j (emb (bulk (dIo j C Vb Vo K a b p))) ≤ ENNReal.ofReal e ∧
      nrmD c ℓ₀ a b j (πobs (dIo j C Vb Vo K a b p)) ≤ ENNReal.ofReal o ∧
      nrmD c ℓ₀ a b j (Aq j C Vo K a b p) ≤ ENNReal.ofReal α ∧
      nrmD c ℓ₀ a b j (Yq j C Vb Vo K a b p) ≤ ENNReal.ofReal y ∧
      nrmD c ℓ₀ a b j (dIo j C Vb Vo K a b p) ≤ 1 ∧
      nrmj c ℓ₀ a b j (Vobs j Vo a b p) ≤ ENNReal.ofReal vo ∧
      nrmj c ℓ₀ a b j (QobsO a b j K p) ≤ ENNReal.ofReal q ∧
      nrmD c ℓ₀ a b j (rhoO j C Vb Vo K a b p) ≤ ENNReal.ofReal ρ)
    {U X : Finset (Lam d L N)} (hX : X ∈ Iset j U) :
    nrmj c ℓ₀ a b (j + 1)
        (πobs (TX j C Vb Vo K a b X) - LtX j C K a b X - mX j C Vo K a b X) ≤
      ENNReal.ofReal (((L : ℝ) ^ (2 * ((d : ℝ) - 2)) * (q * (2 * vo + q)) + ρ) +
        (e * o + o * e + α * y + y * α + y * y) + e * (2 ^ d * o)) := by
  classical
  have hab := h.hab
  have hCs := symm_of_goodCov h.cov a b
  have hC := h.cov
  obtain ⟨-, hXp, hXne, hXs⟩ := mem_Iset hX
  have hK0 : 0 ≤ (L : ℝ) ^ (2 * ((d : ℝ) - 2)) := by positivity
  have hR1 : 0 ≤ (L : ℝ) ^ (2 * ((d : ℝ) - 2)) * (q * (2 * vo + q)) + ρ := by positivity
  have hR2 : 0 ≤ e * o + o * e + α * y + y * α + y * y := by positivity
  have hR3 : 0 ≤ e * (2 ^ d * o) := by positivity
  -- blocks of `X` are in `blockIdx`
  have hbI : ∀ p ∈ blocks j X, p ∈ blockIdx (L := L) (N := N) j :=
    fun p hp => mem_blockIdx_of_mem_blocks hp
  -- the term `πobs (TX)` for connected `X`
  have hTc : ∀ (hc : IsConn j X), (∀ p, X ≠ blockSet j p) →
      πobs (TX j C Vb Vo K a b X) = LtX j C K a b X +
        πobs (ECO C (dIPowG (obsA c C) j (obsI j C Vb Vo K a b) X)) := by
    intro hc hnb
    have hsm : IsSmall j X := by
      rcases hXs with h1 | h1
      · exact h1
      · exact absurd hc.2 h1.2
    rw [TX, if_pos hc, termS_nonblock j K a b hsm hnb, map_add, map_add, πobs_ECO, πobs_thetaO,
      LtX, if_pos hc]
  have hnb1 : ∀ p, nb j X ≠ 1 → X ≠ blockSet j p := by
    intro p h1 h2
    have := nb_blockSet_le (L := L) (N := N) j p
    rw [← h2] at this
    have : 1 ≤ nb j X := card_pos.2 (hXne.image _)
    omega
  have hsum_le : ∀ R : ℝ, R = (L : ℝ) ^ (2 * ((d : ℝ) - 2)) * (q * (2 * vo + q)) + ρ ∨
      R = e * o + o * e + α * y + y * α + y * y ∨ R = e * (2 ^ d * o) →
      ENNReal.ofReal R ≤ ENNReal.ofReal (((L : ℝ) ^ (2 * ((d : ℝ) - 2)) * (q * (2 * vo + q)) + ρ) +
        (e * o + o * e + α * y + y * α + y * y) + e * (2 ^ d * o)) := by
    rintro R (rfl | rfl | rfl) <;> exact ENNReal.ofReal_le_ofReal (by linarith)
  by_cases h1 : nb j X = 1
  · -- a single block
    obtain ⟨q₀, hq, hXq, hqI⟩ := eq_blockSet_of_nb_one hXp h1
    have hc : IsConn j X := by
      rcases hXs with h2 | h2
      · exact ⟨h2.1, h2.2.1⟩
      · omega
    obtain ⟨-, -, -, -, -, hv, hqb, hρ⟩ := hbl q₀ hqI
    have hm : mX j C Vo K a b X =
        -∑ q' ∈ (blockIdx (L := L) (N := N) j).erase q₀, PobsBB C j Vo K a b q₀ q' := by
      rw [mX, if_pos h1, hq, sum_singleton]
    subst hXq
    have hT : πobs (TX j C Vb Vo K a b (blockSet j q₀)) = LtX j C K a b (blockSet j q₀) +
        πobs (ECO C (dIo j C Vb Vo K a b q₀ + thetaO (QO a b j K q₀))) := by
      rw [TX, if_pos hc, LtX, if_pos hc, termS_block j K a b hqI, dIPowG, bpow, hq,
        prod_singleton]
      simp only [map_add, map_sub, πobs_ECO, πobs_thetaO]
      abel
    rw [hT, hm, Mb_eq hab hCs hqI]
    refine le_trans (le_of_eq ?_) ((rem_block_bound hd hL hℓ₀ hC hvo hq0 hρ0 hv hqb hρ).trans
      (hsum_le _ (Or.inl rfl)))
    congr 1; abel
  by_cases h2 : nb j X = 2
  · obtain ⟨q, q', hqq, hbq⟩ := card_eq_two.1 h2
    have hqI := hbI q (by rw [hbq]; simp)
    have hqI' := hbI q' (by rw [hbq]; simp)
    obtain ⟨he, ho, hA, hY, -, -, -, -⟩ := hbl q hqI
    obtain ⟨he', ho', hA', hY', -, -, -, -⟩ := hbl q' hqI'
    have hm : mX j C Vo K a b X = (2 : ℂ) • PobsBB C j Vo K a b q q' := by
      rw [mX, if_neg h1, if_pos h2, hbq, sum_pair hqq]
      have e1 : ({q, q'} : Finset (Fin d → ℕ)).erase q = {q'} := by
        ext r; simp only [mem_erase, mem_insert, mem_singleton]
        constructor
        · rintro ⟨h, h' | h'⟩; exacts [absurd h' h, h']
        · rintro rfl; exact ⟨fun h => hqq h.symm, Or.inr rfl⟩
      have e2 : ({q, q'} : Finset (Fin d → ℕ)).erase q' = {q} := by
        ext r; simp only [mem_erase, mem_insert, mem_singleton]
        constructor
        · rintro ⟨h, h' | h'⟩; exacts [h', absurd h' h]
        · rintro rfl; exact ⟨hqq, Or.inl rfl⟩
      rw [e1, e2, sum_singleton, sum_singleton, two_smul]
      congr 1
      rw [PobsBB, PobsBB, ECT_comm]
    have hP : dIPowG (obsA c C) j (obsI j C Vb Vo K a b) X =
        dIo j C Vb Vo K a b q * dIo j C Vb Vo K a b q' := by
      rw [dIPowG, bpow, hbq, prod_pair hqq]
    have hT : πobs (TX j C Vb Vo K a b X) = LtX j C K a b X +
        πobs (ECO C (dIPowG (obsA c C) j (obsI j C Vb Vo K a b) X)) := by
      by_cases hc : IsConn j X
      · exact hTc hc (fun p => hnb1 p h1)
      · rw [TX, if_neg hc, LtX, if_neg hc, zero_add]
    rw [hT, hm, hP, pair_eq hab hCs]
    refine le_trans (le_of_eq ?_) ((rem_pair_bound hd hL hℓ₀ hC he0 ho0 hα0 hy0 he he' ho ho'
      hA hA' hY hY').trans (hsum_le _ (Or.inr (Or.inl rfl))))
    congr 1; abel
  · -- at least three blocks
    have hsm : IsSmall j X := by
      rcases hXs with h3 | h3
      · exact h3
      · exact absurd h3.1 h2
    have hc : IsConn j X := ⟨hsm.1, hsm.2.1⟩
    have h0 : 1 ≤ nb j X := card_pos.2 (hXne.image _)
    have h3 : 3 ≤ nb j X := by omega
    have hm : mX j C Vo K a b X = 0 := by rw [mX, if_neg h1, if_neg h2]
    obtain ⟨p₀, hp₀⟩ : (((blocks j X).erase (blk j a)).erase (blk j b)).Nonempty := by
      rw [← card_pos]
      have h4 := pred_card_le_card_erase (s := blocks j X) (a := blk j a)
      have h5 := pred_card_le_card_erase (s := (blocks j X).erase (blk j a)) (a := blk j b)
      rw [nb] at h3
      omega
    have hpb : p₀ ≠ blk j b := (mem_erase.1 hp₀).1
    have hpa : p₀ ≠ blk j a := (mem_erase.1 (mem_erase.1 hp₀).2).1
    have hpX : p₀ ∈ blocks j X := (mem_erase.1 (mem_erase.1 hp₀).2).2
    have ha : a ∉ blockSet (L := L) (N := N) j p₀ := fun h => hpa (Loc.mem_blockSet.1 h).symm
    have hb : b ∉ blockSet (L := L) (N := N) j p₀ := fun h => hpb (Loc.mem_blockSet.1 h).symm
    obtain ⟨he, -, -, -, -, -, -, -⟩ := hbl p₀ (hbI p₀ hpX)
    rw [hTc hc (fun p => hnb1 p h1), hm, add_sub_cancel_left, sub_zero]
    refine (rem_many_bound hd hL hℓ₀ hC hpX ha hb he0 ho0 he
      (fun p hp => (hbl p (hbI p hp)).2.2.2.2.1) (fun p hp => (hbl p (hbI p hp)).2.1)).trans
      ((ENNReal.ofReal_le_ofReal ?_).trans (hsum_le _ (Or.inr (Or.inr rfl))))
    gcongr
    exact_mod_cast hsm.2.2

end RBound

/-! ### The cancellation of the `P^obs` parts (`lem:smallset-Vobs`, two-block terms) -/

section Cancel

variable {c : Case} {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℝ} {Vb : Vcoup} {Vo : Coup c}
  {K : Finset (Lam d L N) → OE c (Lam d L N)} {a b : Lam d L N} {ℓ₀ : ℝ}

theorem blocks_blockSet_of_mem {q : Fin d → ℕ} {x : Lam d L N} (hx : x ∈ blockSet j q) :
    blocks j (blockSet (L := L) (N := N) j q) = {q} :=
  blocks_blockSet_eq ⟨x, hx⟩

theorem clo_blockSet_eq {q : Fin d → ℕ} {x : Lam d L N} (hx : x ∈ blockSet j q) :
    blocks (j + 1) (blockSet (L := L) (N := N) j q) = {blk (j + 1) x} := by
  rw [blocks_succ, blocks_blockSet_of_mem hx, image_singleton, blk_succ, Loc.mem_blockSet.1 hx]

theorem clo_congr {X Y : Finset (Lam d L N)} (h : blocks (j + 1) X = blocks (j + 1) Y) :
    clo j X = clo j Y := by
  ext x; rw [mem_clo, mem_clo, h]

/-- The vanishing of `P^obs(B, B')` in terms of block indices. -/
theorem PobsBB_zero' (hab : a ≠ b) (hsep : SepHyp j C a b) (hsym : C b a = C a b)
    {q q' : Fin d → ℕ} (hne : q ≠ q')
    (h : ¬ (blk (j + 1) a = blk (j + 1) b ∧
      ((q = blk j a ∧ q' = blk j b) ∨ (q = blk j b ∧ q' = blk j a)))) :
    PobsBB C j Vo K a b q q' = 0 := by
  refine PobsBB_eq_zero hab hsep hsym hne ?_
  rintro ⟨hs, h1 | h1⟩
  · exact h ⟨hs, Or.inl ⟨(Loc.mem_blockSet.1 h1.1).symm, (Loc.mem_blockSet.1 h1.2).symm⟩⟩
  · exact h ⟨hs, Or.inr ⟨(Loc.mem_blockSet.1 h1.1).symm, (Loc.mem_blockSet.1 h1.2).symm⟩⟩

set_option maxHeartbeats 4000000 in
/-- **The cancellation**: `‖∑_X e^{…^∅}(U, X) m(X)‖ ≤ 2 δ π` where `π` bounds `P^obs` and `δ`
bounds the differences of the bulk prefactors of `B_a, B_b` and `B_a ∪ B_b`. -/
theorem cancel_bound (hd : 3 ≤ d) (hℓ₀ : 0 < ℓ₀) (hab : a ≠ b) (hsep : SepHyp j C a b) (hsym : C b a = C a b)
    {U : Finset (Lam d L N)} {δ π : ℝ} (hδ0 : 0 ≤ δ) (hπ0 : 0 ≤ π)
    (hπ : nrmj c ℓ₀ a b (j + 1) (PobsBB C j Vo K a b (blk j a) (blk j b)) ≤ ENNReal.ofReal π)
    (hδ : blk (j + 1) a = blk (j + 1) b → blk j a ≠ blk j b →
      clo j (blockSet (L := L) (N := N) j (blk j a)) = U →
      ∀ q ∈ ({blk j a, blk j b} : Finset (Fin d → ℕ)),
      nrmj c ℓ₀ a b (j + 1) (emb (bulk (prefG j (obsI j C Vb Vo K a b) U (blockSet j q))) -
        emb (bulk (prefG j (obsI j C Vb Vo K a b) U
          (blockSet j (blk j a) ∪ blockSet j (blk j b))))) ≤ ENNReal.ofReal δ) :
    nrmj c ℓ₀ a b (j + 1) (∑ X ∈ Iset j U,
        emb (bulk (prefG j (obsI j C Vb Vo K a b) U X)) * mX j C Vo K a b X) ≤
      ENNReal.ofReal (2 * (δ * π)) := by
  classical
  set pa := blk j a
  set pb := blk j b
  set Ba := blockSet (L := L) (N := N) j pa
  set Bb := blockSet (L := L) (N := N) j pb
  set β : Finset (Lam d L N) → OE c (Lam d L N) :=
    fun X => emb (bulk (prefG j (obsI j C Vb Vo K a b) U X))
  have hpaI : pa ∈ blockIdx (L := L) (N := N) j := mem_image.2 ⟨a, mem_univ _, rfl⟩
  have hpbI : pb ∈ blockIdx (L := L) (N := N) j := mem_image.2 ⟨b, mem_univ _, rfl⟩
  have haBa : a ∈ Ba := Loc.mem_blockSet.2 rfl
  have hbBb : b ∈ Bb := Loc.mem_blockSet.2 rfl
  -- the vanishing
  have hvan : ∀ q q', q ≠ q' → ¬ (blk (j + 1) a = blk (j + 1) b ∧
      ((q = pa ∧ q' = pb) ∨ (q = pb ∧ q' = pa))) → PobsBB C j Vo K a b q q' = 0 :=
    fun q q' hne h => PobsBB_zero' hab hsep hsym hne h
  have hsym' : PobsBB C j Vo K a b pb pa = PobsBB C j Vo K a b pa pb := by
    rw [PobsBB, PobsBB, ECT_comm]
  by_cases hs : blk (j + 1) a = blk (j + 1) b ∧ pa ≠ pb
  swap
  · -- all `m(X)` vanish
    have hz : ∀ q q', q ≠ q' → PobsBB C j Vo K a b q q' = 0 := by
      intro q q' hne
      refine hvan q q' hne ?_
      rintro ⟨h1, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
      · exact hs ⟨h1, hne⟩
      · exact hs ⟨h1, fun h => hne h.symm⟩
    have hm : ∀ X, mX j C Vo K a b X = 0 := by
      intro X
      unfold mX
      split_ifs
      · rw [sum_eq_zero fun q _ => sum_eq_zero fun q' hq' => hz q q' (mem_erase.1 hq').1.symm,
          neg_zero]
      · exact sum_eq_zero fun q _ => sum_eq_zero fun q' hq' => hz q q' (mem_erase.1 hq').1.symm
      · rfl
    rw [sum_eq_zero fun X _ => by rw [hm X, mul_zero], nrmj_zero]
    exact zero_le
  obtain ⟨hs1, hpab⟩ := hs
  set P := PobsBB C j Vo K a b pa pb
  have hdisj : Disjoint Ba Bb := blockSet_disjoint hpab
  have hbBa : b ∉ Ba := fun h => Finset.disjoint_left.1 hdisj h hbBb
  have haBb : a ∉ Bb := fun h => Finset.disjoint_left.1 hdisj haBa h
  have hbla : blocks j Ba = {pa} := blocks_blockSet_of_mem haBa
  have hblb : blocks j Bb = {pb} := blocks_blockSet_of_mem hbBb
  have hblab : blocks j (Ba ∪ Bb) = {pa, pb} := by
    rw [blocks_union, hbla, hblb]; rfl
  -- values of `m`
  have hma : mX j C Vo K a b Ba = -P := by
    rw [mX, if_pos (by rw [nb, hbla]; rfl), hbla, sum_singleton,
      sum_eq_single_of_mem pb (mem_erase.2 ⟨fun h => hpab h.symm, hpbI⟩)]
    intro q' hq' hne
    exact hvan pa q' (mem_erase.1 hq').1.symm (by
      rintro ⟨-, ⟨-, h⟩ | ⟨h, -⟩⟩; exacts [hne h, hpab h])
  have hmb : mX j C Vo K a b Bb = -P := by
    rw [mX, if_pos (by rw [nb, hblb]; rfl), hblb, sum_singleton,
      sum_eq_single_of_mem pa (mem_erase.2 ⟨hpab, hpaI⟩), hsym']
    intro q' hq' hne
    exact hvan pb q' (mem_erase.1 hq').1.symm (by
      rintro ⟨-, ⟨h, -⟩ | ⟨-, h⟩⟩; exacts [hpab h.symm, hne h])
  have hnb2 : nb j (Ba ∪ Bb) = 2 := by rw [nb, hblab, card_pair hpab]
  have hmab : mX j C Vo K a b (Ba ∪ Bb) = P + P := by
    rw [mX, if_neg (by rw [hnb2]; norm_num), if_pos hnb2, hblab, sum_pair hpab]
    have e1 : ({pa, pb} : Finset (Fin d → ℕ)).erase pa = {pb} := by
      rw [erase_insert (by simpa using hpab)]
    have e2 : ({pa, pb} : Finset (Fin d → ℕ)).erase pb = {pa} := by
      rw [pair_comm, erase_insert (by simpa using hpab.symm)]
    rw [e1, e2, sum_singleton, sum_singleton, hsym']
  -- `m` vanishes elsewhere
  have hzero : ∀ X ∈ Iset j U, X ≠ Ba → X ≠ Bb → X ≠ Ba ∪ Bb → mX j C Vo K a b X = 0 := by
    intro X hX h1 h2 h3
    obtain ⟨-, hXp, -, -⟩ := mem_Iset hX
    unfold mX
    split_ifs with hn1 hn2
    · obtain ⟨q, hq, hXq, -⟩ := eq_blockSet_of_nb_one hXp hn1
      rw [hq, sum_singleton]
      rw [sum_eq_zero fun q' hq' => hvan q q' (mem_erase.1 hq').1.symm ?_, neg_zero]
      rintro ⟨-, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩
      · exact h1 hXq
      · exact h2 hXq
    · refine sum_eq_zero fun r hr => sum_eq_zero fun r' hr' => ?_
      have hrr : r' ≠ r := (mem_erase.1 hr').1
      have hr2 : r' ∈ blocks j X := (mem_erase.1 hr').2
      have hbl : blocks j X = {r, r'} := by
        refine (eq_of_subset_of_card_le ?_ ?_).symm
        · intro x hx
          simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hr
          · exact hr2
        · rw [card_pair hrr.symm]; exact hn2.le
      have hX' : X = blockSet j r ∪ blockSet j r' := by
        rw [← biUnion_blocks hXp, hbl]; simp
      refine hvan r r' hrr.symm ?_
      rintro ⟨-, ⟨h1', h2'⟩ | ⟨h1', h2'⟩⟩
      · exact h3 (by rw [hX', h1', h2'])
      · exact h3 (by rw [hX', h1', h2', union_comm])
    · rfl
  -- closures
  have hca : blocks (j + 1) Ba = {blk (j + 1) a} := clo_blockSet_eq haBa
  have hcb : blocks (j + 1) Bb = {blk (j + 1) a} := by rw [clo_blockSet_eq hbBb, hs1]
  have hcab : blocks (j + 1) (Ba ∪ Bb) = {blk (j + 1) a} := by
    rw [blocks_union, hca, hcb, union_self]
  by_cases hU : clo j Ba = U
  swap
  · have : ∀ X ∈ Iset j U, β X * mX j C Vo K a b X = 0 := by
      intro X hX
      obtain ⟨hcl, -⟩ := mem_Iset hX
      rw [hzero X hX (fun h => hU (h ▸ hcl)) (fun h => hU (by
          rw [clo_congr (hca.trans hcb.symm)]; exact h ▸ hcl))
        (fun h => hU (by rw [clo_congr (hca.trans hcab.symm)]; exact h ▸ hcl)), mul_zero]
    rw [sum_eq_zero this, nrmj_zero]
    exact zero_le
  -- the three sets lie in `I(U)`
  have hBaI : Ba ∈ Iset j U := mem_union_left _ (by
    simp only [smU, mem_filter, mem_smallSets]
    exact ⟨isSmall_blockSet_of_mem hpaI, hU⟩)
  have hBbI : Bb ∈ Iset j U := mem_union_left _ (by
    simp only [smU, mem_filter, mem_smallSets]
    exact ⟨isSmall_blockSet_of_mem hpbI, by rw [clo_congr (hcb.trans hca.symm)]; exact hU⟩)
  have hpol : IsPolymer j (Ba ∪ Bb) := IsPolymer.union (isPolymer_blockSet j pa) (isPolymer_blockSet j pb)
  have hcloab : clo j (Ba ∪ Bb) = U := by rw [clo_congr (hcab.trans hca.symm)]; exact hU
  have hBabI : Ba ∪ Bb ∈ Iset j U := by
    by_cases hcn : IsConnected j (Ba ∪ Bb)
    · refine mem_union_left _ ?_
      simp only [smU, mem_filter, mem_smallSets]
      refine ⟨⟨hpol, hcn, ?_⟩, hcloab⟩
      rw [show (blocks j (Ba ∪ Bb)).card = nb j (Ba ∪ Bb) from rfl, hnb2]
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) (by omega)
    · refine mem_union_right _ ?_
      simp only [pairSets, mem_filter, mem_univ, true_and]
      exact ⟨hpol, hcloab, hnb2, by rw [nb, hcab]; rfl, hcn⟩
  have hne1 : Ba ≠ Bb := fun h => hbBa (h ▸ hbBb)
  have hne2 : Ba ≠ Ba ∪ Bb := fun h => hbBa (h ▸ mem_union_right _ hbBb)
  have hne3 : Bb ≠ Ba ∪ Bb := fun h => haBb (h ▸ mem_union_left _ haBa)
  have hsub : ({Ba, Bb, Ba ∪ Bb} : Finset (Finset (Lam d L N))) ⊆ Iset j U := by
    intro X hX
    simp only [mem_insert, mem_singleton] at hX
    rcases hX with rfl | rfl | rfl <;> assumption
  rw [← sum_subset hsub (fun X hX hX' => by
    simp only [mem_insert, mem_singleton, not_or] at hX'
    rw [hzero X hX hX'.1 hX'.2.1 hX'.2.2, mul_zero])]
  rw [sum_insert (by simp [hne1, hne2]), sum_insert (by simp [hne3]), sum_singleton, hma, hmb,
    hmab]
  have e : β Ba * -P + (β Bb * -P + β (Ba ∪ Bb) * (P + P)) =
      -((β Ba - β (Ba ∪ Bb)) * P) - (β Bb - β (Ba ∪ Bb)) * P := by ring
  rw [e]
  refine (nrmj_sub_le _ _ _).trans ?_
  rw [nrmj_neg, two_mul, ENNReal.ofReal_add (by positivity) (by positivity)]
  have hd2 : 2 ≤ d := by omega
  exact add_le_add (nn_mul hd2 hℓ₀ hδ0 (hδ hs1 hpab hU pa (by simp)) hπ)
    (nn_mul hd2 hℓ₀ hδ0 (hδ hs1 hpab hU pb (by simp)) hπ)

/-- The difference of bulk prefactors: `pref(U, B) - pref(U, B ∪ B') = pref(U, B ∪ B') (e^{-(u+V)(B')} - 1)`. -/
theorem pref_diff {U : Finset (Lam d L N)} {q q' : Fin d → ℕ} (hqq : q ≠ q') (hU : IsPolymer j U)
    (hsub : blockSet (L := L) (N := N) j q' ⊆ U) (hne : (blockSet (L := L) (N := N) j q').Nonempty)
    (Kb : Act d L N) :
    pref j C Vb Kb U (blockSet j q) - pref j C Vb Kb U (blockSet j q ∪ blockSet j q') =
      pref j C Vb Kb U (blockSet j q ∪ blockSet j q') * (Inext j C Vb Kb q' - 1) := by
  classical
  have hdisj : Disjoint (blockSet (L := L) (N := N) j q) (blockSet j q') := blockSet_disjoint hqq
  have hset : U \ blockSet j q = (U \ (blockSet j q ∪ blockSet j q')) ∪ blockSet j q' := by
    ext x
    simp only [mem_sdiff, mem_union, not_or]
    constructor
    · rintro ⟨hx, hxq⟩
      by_cases h : x ∈ blockSet (L := L) (N := N) j q'
      · exact Or.inr h
      · exact Or.inl ⟨hx, hxq, h⟩
    · rintro (⟨hx, hxq, -⟩ | h)
      · exact ⟨hx, hxq⟩
      · exact ⟨hsub h, fun h' => Finset.disjoint_left.1 hdisj h' h⟩
  have hpol : IsPolymer j (blockSet (L := L) (N := N) j q ∪ blockSet j q') :=
    IsPolymer.union (isPolymer_blockSet j q) (isPolymer_blockSet j q')
  have h1 : InextPow j C Vb Kb (U \ blockSet j q) =
      InextPow j C Vb Kb (U \ (blockSet j q ∪ blockSet j q')) * Inext j C Vb Kb q' := by
    rw [hset, InextPow_union j C Vb Kb (IsPolymer.sdiff hU hpol) (isPolymer_blockSet j q')
      (Finset.disjoint_left.2 fun x hx hx' => (mem_sdiff.1 hx).2 (mem_union_right _ hx'))]
    congr 1
    rw [InextPow, blocks_blockSet_eq hne, prod_singleton]
  rw [pref, pref, h1, smul_mul_assoc, mul_sub, mul_one, smul_sub]

end Cancel

end

end Obs
