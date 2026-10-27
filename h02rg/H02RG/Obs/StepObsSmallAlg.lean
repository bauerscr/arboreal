import Obs.StepObsFix

/-!
# Small sets for `thm:step-obs`: algebraic identities

Algebraic identities used in the proof of `SmallObsStmt'` (`Obs.StepObsSmall`):
* `πobs_mul'`: `π_obs (F G) = F π_obs G + π_obs F · F_∅(G)`;
* `prefG_obs_eq`: the prefactor `e^{u_{j+1}(U)} e^{-(u+V)_{j+1}(U ∖ X)}` is
  `e^{(…)^∅} e^{W}` with `W = u^obs_{j+1}(U) - (u+V)^obs_{j+1}(U ∖ X)`;
* the identities `e:Kblock-obs`, `e:Ksmallset-obs` for the summands (`termS_block`,
  `termS_nonblock`);
* `Mb_eq` (the single-block terms, proof of `lem:smallset-Vobs`), `pair_eq` (the two-block terms,
  `lem:Pjj+1`), `PobsBB_eq_zero` (`P^obs(B, B') = 0` unless `a, b` are in `B, B'` in the same
  `(j+1)`-block).
-/

namespace Obs

noncomputable section

open Finset Grassmann SA Loc Step LocObs Gen

variable {d L N : ℕ} [NeZero L]

/-! ### Generic facts -/

section Generic

variable {c : Case} {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

theorem πobs_mul' (F G : OE c Λ) : πobs (F * G) = F * πobs G + πobs F * emb (bulk G) := by
  rw [πobs_mul, add_right_comm, ← add_mul, ← eq_emb_add_πobs F]

theorem IsAB.mul_eq_emb {F G : OE c Λ} (hG : IsAB G) : F * G = (emb (bulk F) : OE c Λ) * G := by
  have h0 : πobs F * G = 0 := by rw [mul_comm]; exact hG.mul_eq_zero (bulk_πobs F)
  calc F * G = ((emb (bulk F) : OE c Λ) + πobs F) * G := by rw [← eq_emb_add_πobs F]
    _ = _ := by rw [add_mul, h0, add_zero]

theorem πobs_thetaO (F : OE c Λ) : πobs (thetaO F) = thetaO (πobs F) := by
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;> simp [piobs_apply]

theorem πobs_inclO (F : OE c Λ) : πobs (inclO F) = inclO (πobs F) := by
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;> simp [piobs_apply]

theorem πobs_ECO (C : Matrix Λ Λ ℝ) (F : OE c (Λ ⊕ Λ)) : πobs (ECO C F) = ECO C (πobs F) := by
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;> simp [piobs_apply]

/-- A product of factors `e^{x_i} e^{w_i}` with observable `w_i`. -/
theorem prod_emb_mul_oexp {ι : Type*} (s : Finset ι) (x : ι → EvR Λ) (w : ι → OE c Λ)
    (hw : ∀ i ∈ s, bulk (w i) = 0) :
    ∏ i ∈ s, (emb (x i) * oexp (w i)) = emb (∏ i ∈ s, x i) * oexp (∑ i ∈ s, w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [oexp_zero]
  | insert i s hi ih =>
    have hs : ∀ k ∈ s, bulk (w k) = 0 := fun k hk => hw k (mem_insert_of_mem hk)
    have hs' : bulk (∑ k ∈ s, w k) = 0 := by
      rw [map_sum]; exact sum_eq_zero hs
    rw [prod_insert hi, prod_insert hi, sum_insert hi, ih hs, map_mul,
      oexp_add (isNilpotent_of_obs (hw i (mem_insert_self i s))) (isNilpotent_of_obs hs'),
      mul_mul_mul_comm]

end Generic

theorem splitO_eq_sum_blocks' {c : Case} (W : Coup c) (a b : Lam d L N) {j : ℕ}
    {X : Finset (Lam d L N)} (hX : IsPolymer j X) :
    splitO c W a b X = ∑ p ∈ blocks j X, splitO c W a b (blockSet j p) := by
  have hd : ((blocks j X : Finset (Fin d → ℕ)) : Set (Fin d → ℕ)).PairwiseDisjoint
      (blockSet (L := L) (N := N) j) := fun _ _ _ _ hne => blockSet_disjoint hne
  conv_lhs => rw [← biUnion_blocks hX]
  exact splitO_biUnion c _ a b _ _ hd

/-! ### The prefactor -/

section Pref

variable {c : Case} (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (Vb : Vcoup) (Vo : Coup c)
  (K : Finset (Lam d L N) → OE c (Lam d L N)) (a b : Lam d L N)

theorem eu_fac (p : Fin d → ℕ) :
    (obsI j C Vb Vo K a b).eu p =
      emb (algebraMap ℂ (EvR (Lam d L N))
        (Complex.exp ((uVb j C Vb K).1 * (blockSet (L := L) (N := N) j p).card))) *
        oexp (uObsX j C Vo K a b (blockSet j p)) := by
  simp only [obsI]
  rw [AlgHom.commutes]

theorem It_fac (p : Fin d → ℕ) :
    It (obsI j C Vb Vo K a b) p =
      emb (algebraMap ℂ (EvR (Lam d L N))
          (Complex.exp (-((uVb j C Vb K).1 * (blockSet (L := L) (N := N) j p).card))) *
        gexp (-(VE (uVb j C Vb K).2 (blockSet j p) : EvR (Lam d L N)))) *
        oexp (-splitO c (nextObs C j Vo K a b) a b (blockSet j p)) := by
  simp only [It, obsI]
  have hx : ε (((-VE (uVb j C Vb K).2 (blockSet (L := L) (N := N) j p) : EvR (Lam d L N))) :
      Alg d L N) = 0 := by
    rw [NegMemClass.coe_neg, map_neg, ε_VE, neg_zero]
  have h1 : oexp (-VfullX (uVb j C Vb K).2 (nextObs C j Vo K a b) a b (blockSet j p)) =
      emb (gexp (-(VE (uVb j C Vb K).2 (blockSet j p) : EvR (Lam d L N)))) *
        oexp (-splitO c (Coup.toV c (nextObs C j Vo K a b)) a b (blockSet j p)) := by
    rw [VfullX, neg_add, oexp_add (isNilpotent_of_ε (F := -emb _) ?_)
      (isNilpotent_of_obs (by rw [map_neg, bulk_splitO, neg_zero])), ← map_neg, oexp_emb hx]
    rw [NegMemClass.coe_neg, SA.neg_e, coe_emb, map_neg, neg_eq_zero]
    exact ε_VE _ _
  have h2 : oexp (-uObsX j C Vo K a b (blockSet j p)) *
      oexp (-splitO c (Coup.toV c (nextObs C j Vo K a b)) a b (blockSet j p)) =
      oexp (-splitO c (nextObs C j Vo K a b) a b (blockSet j p)) := by
    rw [← oexp_add (isNilpotent_of_obs (by rw [map_neg, bulk_uObsX, neg_zero]))
      (isNilpotent_of_obs (by rw [map_neg, bulk_splitO, neg_zero])), ← neg_add, uObsX,
      splitO_toU_add_toV]
  rw [h1, ← AlgHom.commutes (emb (c := c) (Λ := Lam d L N)), map_mul, ← h2]
  ring

/-- The prefactor `e^{u_{j+1}(U)} e^{-(u+V)_{j+1}(U ∖ X)}` as `e^{…^∅} e^{W}`. -/
theorem prefG_obs_eq {U X : Finset (Lam d L N)} (hU : IsPolymer j U)
    (hUX : IsPolymer j (U \ X)) :
    prefG j (obsI j C Vb Vo K a b) U X =
      emb (bulk (prefG j (obsI j C Vb Vo K a b) U X)) *
        oexp (uObsX j C Vo K a b U - splitO c (nextObs C j Vo K a b) a b (U \ X)) := by
  set β₁ := ∏ p ∈ blocks j U, algebraMap ℂ (EvR (Lam d L N))
    (Complex.exp ((uVb j C Vb K).1 * (blockSet (L := L) (N := N) j p).card)) with hβ₁
  set β₂ := ∏ p ∈ blocks j (U \ X), algebraMap ℂ (EvR (Lam d L N))
      (Complex.exp (-((uVb j C Vb K).1 * (blockSet (L := L) (N := N) j p).card))) *
    gexp (-(VE (uVb j C Vb K).2 (blockSet (L := L) (N := N) j p) : EvR (Lam d L N))) with hβ₂
  have e1 : PrefG j (obsI j C Vb Vo K a b) U = emb β₁ * oexp (uObsX j C Vo K a b U) := by
    rw [PrefG, bpow, prod_congr rfl fun p _ => eu_fac j C Vb Vo K a b p,
      prod_emb_mul_oexp _ _ _ fun p _ => bulk_uObsX j C Vo K a b _, uObsX,
      splitO_eq_sum_blocks' _ a b hU]
    rfl
  have e2 : ItPow j (obsI j C Vb Vo K a b) (U \ X) =
      emb β₂ * oexp (-splitO c (nextObs C j Vo K a b) a b (U \ X)) := by
    rw [ItPow, bpow, prod_congr rfl fun p _ => It_fac j C Vb Vo K a b p,
      prod_emb_mul_oexp _ _ _ fun p _ => by rw [map_neg, bulk_splitO, neg_zero],
      splitO_eq_sum_blocks' _ a b hUX, ← sum_neg_distrib]
  have hβ : prefG j (obsI j C Vb Vo K a b) U X =
      emb (β₁ * β₂) * oexp (uObsX j C Vo K a b U - splitO c (nextObs C j Vo K a b) a b (U \ X)) := by
    rw [prefG, e1, e2, sub_eq_add_neg, oexp_add (isNilpotent_of_obs (bulk_uObsX j C Vo K a b _))
      (isNilpotent_of_obs (by rw [map_neg, bulk_splitO, neg_zero])), map_mul]
    ring
  have hb : bulk (prefG j (obsI j C Vb Vo K a b) U X) = β₁ * β₂ := by
    rw [hβ, map_mul, bulk_emb, bulk_oexp_obs, mul_one]
    rw [map_sub, bulk_uObsX, bulk_splitO, sub_zero]
  rw [hb]; exact hβ

theorem πobs_prefG {U X : Finset (Lam d L N)} (hU : IsPolymer j U) (hUX : IsPolymer j (U \ X)) :
    πobs (prefG j (obsI j C Vb Vo K a b) U X) =
      emb (bulk (prefG j (obsI j C Vb Vo K a b) U X)) *
        (oexp (uObsX j C Vo K a b U - splitO c (nextObs C j Vo K a b) a b (U \ X)) - 1) := by
  set W := uObsX j C Vo K a b U - splitO c (nextObs C j Vo K a b) a b (U \ X)
  have hW : bulk W = 0 := by rw [map_sub, bulk_uObsX, bulk_splitO, sub_zero]
  have h1 : bulk (oexp W - 1) = 0 := by rw [map_sub, bulk_oexp_obs hW, map_one, sub_self]
  set β := bulk (prefG j (obsI j C Vb Vo K a b) U X)
  have e : prefG j (obsI j C Vb Vo K a b) U X = emb β * oexp W := prefG_obs_eq j C Vb Vo K a b hU hUX
  rw [e, show (emb β : OE c (Lam d L N)) * oexp W = emb β + emb β * (oexp W - 1) by ring,
    map_add, πobs_emb, zero_add, πobs_emb_mul h1]

/-- The bulk prefactor is Step's `pref`. -/
theorem bulk_prefG (U X : Finset (Lam d L N)) (hU : IsPolymer j U) :
    bulk (prefG j (obsI j C Vb Vo K a b) U X) = pref j C Vb (bulkK K) U X := by
  have h1 := map_PrefG (bulk (c := c) (Λ := Lam d L N)) j (obsI j C Vb Vo K a b) U
  have h2 := map_ItPow (bulk (c := c) (Λ := Lam d L N)) j (obsI j C Vb Vo K a b) (U \ X)
  have hm : (obsI j C Vb Vo K a b).map (bulk (c := c) (Λ := Lam d L N)) =
      bulkI j C Vb (bulkK K) := map_bulk_obsI j C Vb Vo K a b
  rw [hm] at h1 h2
  rw [prefG, map_mul, h1, h2]
  rw [PrefG_bulk j C Vb (bulkK K) hU, ItPow_bulk, pref, Algebra.smul_def]

end Pref

/-! ### The summands: `e:Kblock-obs`, `e:Ksmallset-obs` -/

section Terms

variable {c : Case} (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (Vb : Vcoup) (Vo : Coup c)
  (K : Finset (Lam d L N) → OE c (Lam d L N)) (a b : Lam d L N)

/-- `Loc_X F` if `j + 1 < N`, and `0` for the last step (extended `Loc`). -/
def LocCO (X : Finset (Lam d L N)) (F : OE c (Lam d L N)) : OE c (Lam d L N) :=
  if j + 1 < N then LocO a b X X F else 0

/-- `Loc_X = ∑_{B ∈ 𝓑_j(X)} Loc_{X,B}` (Proposition `prop:Loc-obs` (iii)). -/
theorem LocO_eq_sum {X : Finset (Lam d L N)} (hX : IsPolymer j X) (F : OE c (Lam d L N)) :
    LocO a b X X F = ∑ p ∈ blocks j X, LocO a b X (blockSet j p) F := by
  have hd : ((blocks j X : Finset (Fin d → ℕ)) : Set (Fin d → ℕ)).PairwiseDisjoint
      (blockSet (L := L) (N := N) j) := fun _ _ _ _ hne => blockSet_disjoint hne
  have he := LocX_eq_sum (blocks j X) (blockSet j) hd (F : SA c (Lam d L N)).e
  have ha := locA_eq_sum c.toObs a (blocks j X) (blockSet j) hd (F : SA c (Lam d L N)).a
  have hb := locB_eq_sum c.toObs b (blocks j X) (blockSet j) hd (F : SA c (Lam d L N)).b
  have hab := locAB_eq_sum a b (blocks j X) (blockSet j) hd (F : SA c (Lam d L N)).ab
  rw [biUnion_blocks hX] at he ha hb hab
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_)
  · rw [AddSubmonoidClass.coe_finsetSum, SA.sum_e, coe_LocO, LocS_e]
    simp only [coe_LocO, LocS_e]; rw [← he]; rfl
  · rw [AddSubmonoidClass.coe_finsetSum, SA.sum_a, coe_LocO, LocS_a]
    simp only [coe_LocO, LocS_a]; exact ha
  · rw [AddSubmonoidClass.coe_finsetSum, SA.sum_b, coe_LocO, LocS_b]
    simp only [coe_LocO, LocS_b]; exact hb
  · rw [AddSubmonoidClass.coe_finsetSum, SA.sum_ab, coe_LocO, LocS_ab]
    simp only [coe_LocO, LocS_ab]; exact hab

/-- `e:Ksmallset-obs`: for `X ∈ 𝒮_j ∖ 𝓑_j`,
`θ K(X) - ∑_B θ J(B, X) = θ (1 - Loc_X) K(X)`. -/
theorem termS_nonblock {X : Finset (Lam d L N)} (hX : IsSmall j X)
    (hnb : ∀ p, X ≠ blockSet j p) :
    thetaO (K X) - ∑ p ∈ blocks j X, thetaO (JO a b j K p X) =
      thetaO (K X - LocCO j a b X (K X)) := by
  classical
  have hJ : ∀ p ∈ blocks j X, JO a b j K p X =
      if j + 1 < N then LocO a b X (blockSet j p) (K X) else 0 := by
    intro p hp
    have hsub := blockSet_subset hX.1 hp
    by_cases hj : j + 1 < N
    · rw [JO, if_pos ⟨hj, hX, hsub⟩, if_neg (hnb p), if_pos hj]
    · rw [JO, if_neg (fun h => hj h.1), if_neg hj]
  have hLoc : LocCO j a b X (K X) = ∑ p ∈ blocks j X, JO a b j K p X := by
    rw [sum_congr rfl hJ, LocCO]
    by_cases hj : j + 1 < N
    · simp only [hj, if_true]; exact LocO_eq_sum j a b hX.1 _
    · simp [hj]
  rw [hLoc, map_sub, map_sum]

/-- `e:Kblock-obs`: for `X = B ∈ 𝓑_j`,
`θ K(B) - θ J(B, B) = θ (1 - Loc_B) K(B) + θ Q(B)`. -/
theorem termS_block {p : Fin d → ℕ} (hp : p ∈ blockIdx (d := d) (L := L) (N := N) j) :
    thetaO (K (blockSet j p)) -
        ∑ q ∈ blocks j (blockSet (L := L) (N := N) j p), thetaO (JO a b j K q (blockSet j p)) =
      thetaO (K (blockSet j p) - LocCO j a b (blockSet j p) (K (blockSet j p))) +
        thetaO (QO a b j K p) := by
  classical
  set B := blockSet (L := L) (N := N) j p with hB
  have hne : B.Nonempty := by
    obtain ⟨x, _, hx⟩ := mem_image.1 hp
    exact ⟨x, Loc.mem_blockSet.2 hx⟩
  have hS : IsSmall j B := isSmall_blockSet_of_mem hp
  have hbl : blocks j B = {p} := blocks_blockSet_eq hne
  have hJQ : JO a b j K p B = LocCO j a b B (K B) - QO a b j K p := by
    by_cases hj : j + 1 < N
    · have hsplit := sum_filter_add_sum_filter_not ((smallSets j).filter (fun Y => B ⊆ Y))
        (fun Y => Y = B) (fun Y => LocO a b Y B (K Y))
      rw [filter_filter, filter_filter] at hsplit
      have hmem : B ∈ (smallSets j).filter (fun Y => B ⊆ Y ∧ Y = B) :=
        mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, hS⟩, subset_rfl, rfl⟩
      rw [sum_eq_single_of_mem B hmem (fun Y hY hYB => absurd (mem_filter.1 hY).2.2 hYB)]
        at hsplit
      have hQ : QO a b j K p = ∑ Y ∈ (smallSets j).filter (fun Y => B ⊆ Y), LocO a b Y B (K Y) := by
        rw [QO, if_pos hj]
      have hJ : JO a b j K p B = -∑ Y ∈ (smallSets j).filter (fun Y => B ⊆ Y ∧ Y ≠ B),
          LocO a b Y B (K Y) := by
        rw [JO, if_pos ⟨hj, hS, subset_rfl⟩, if_pos rfl]
      rw [hQ, hJ, ← hsplit, LocCO, if_pos hj]
      abel
    · simp [JO, QO, LocCO, hj]
  rw [hbl, sum_singleton, hJQ, map_sub, map_sub]
  abel

end Terms

/-! ### The block quantities -/

section Block

variable {c : Case} (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (Vb : Vcoup) (Vo : Coup c)
  (K : Finset (Lam d L N) → OE c (Lam d L N)) (a b : Lam d L N)

/-- `δI(B)` of the observable map. -/
abbrev dIo (p : Fin d → ℕ) : OE c (Lam d L N ⊕ Lam d L N) :=
  dIG (obsA c C) (obsI j C Vb Vo K a b) p

/-- `Ṽ^obs_{j+1}(B) = (u^obs + V^obs)_{j+1}(B)`. -/
abbrev vt (p : Fin d → ℕ) : OE c (Lam d L N) :=
  splitO c (nextObs C j Vo K a b) a b (blockSet j p)

/-- The remainder of `e:expVobs2-expansion` for `δI(B)`:
`π_obs δI(B) = θ(-V + ½V²) - ι(-Ṽ + ½Ṽ²) + ρ(B)`. -/
def rhoO (p : Fin d → ℕ) : OE c (Lam d L N ⊕ Lam d L N) :=
  thetaO (πobs ((obsI j C Vb Vo K a b).I0 p) -
      (-Vobs j Vo a b p + (1 / 2 : ℂ) • Vobs j Vo a b p ^ 2)) -
    inclO (πobs (It (obsI j C Vb Vo K a b) p) -
      (-vt j C Vo K a b p + (1 / 2 : ℂ) • vt j C Vo K a b p ^ 2))

theorem πobs_dIo (p : Fin d → ℕ) :
    πobs (dIo j C Vb Vo K a b p) =
      thetaO (-Vobs j Vo a b p + (1 / 2 : ℂ) • Vobs j Vo a b p ^ 2) -
        inclO (-vt j C Vo K a b p + (1 / 2 : ℂ) • vt j C Vo K a b p ^ 2) +
        rhoO j C Vb Vo K a b p := by
  simp only [dIo, dIG, obsA, rhoO, map_sub, πobs_thetaO, πobs_inclO]
  abel

theorem bulk_dIo (p : Fin d → ℕ) : bulk (dIo j C Vb Vo K a b p) = dI j C Vb (bulkK K) p := by
  have e1 : bulk (dIo j C Vb Vo K a b p) = dIG (bulkA C) ((obsI j C Vb Vo K a b).map
      (bulk (c := c) (Λ := Lam d L N))) p := by
    simp only [dIo, dIG, obsA, bulkA, RGIngr.map, It, map_sub, map_mul, bulk_thetaO, bulk_inclO]
  rw [e1, map_bulk_obsI, dIG_bulk]

theorem bulk_dIPowG (X : Finset (Lam d L N)) :
    bulk (dIPowG (obsA c C) j (obsI j C Vb Vo K a b) X) = dIPow j C Vb (bulkK K) X := by
  have h := map_dIPowG (A := obsA c C) (A' := bulkA C) (bulk (c := c) (Λ := Lam d L N))
    (bulk (c := c) (Λ := Lam d L N ⊕ Lam d L N))
    (fun x => bulk_thetaO x) (fun x => bulk_inclO x) j (obsI j C Vb Vo K a b) X
  rw [map_bulk_obsI, dIPowG_bulk] at h
  exact h

theorem bulk_rhoO (p : Fin d → ℕ) : bulk (rhoO j C Vb Vo K a b p) = 0 := by
  have hv : bulk (Vobs j Vo a b p) = 0 := bulk_splitO _ _ _ _ _
  have hvt : bulk (vt j C Vo K a b p) = 0 := bulk_splitO _ _ _ _ _
  simp only [rhoO, map_sub, map_add, map_neg, map_smul, map_pow, bulk_thetaO, bulk_inclO,
    bulk_πobs, hv, hvt]
  simp

variable {j C Vb Vo K a b}

set_option maxHeartbeats 1000000 in
/-- **The single-block terms** (proof of `lem:smallset-Vobs`, one-block part):
`π_obs 𝔼[δI(B) + θ Q(B)] = -∑_{B' ≠ B} P^obs(B, B') + ½ 𝔼 θ(V(B)² - V̂(B)²) + 𝔼 ρ(B)`. -/
theorem Mb_eq (hab : a ≠ b) (hCs : C a b = C b a) {p : Fin d → ℕ}
    (hp : p ∈ blockIdx (L := L) (N := N) j) :
    πobs (ECO C (dIo j C Vb Vo K a b p + thetaO (QO a b j K p))) =
      -∑ p' ∈ (blockIdx (L := L) (N := N) j).erase p, PobsBB C j Vo K a b p p' +
        (1 / 2 : ℂ) • ECO C (thetaO (Vobs j Vo a b p ^ 2 - Vhat j Vo K a b p ^ 2)) +
        ECO C (rhoO j C Vb Vo K a b p) := by
  set v := Vobs j Vo a b p
  set vh := Vhat j Vo K a b p
  set q := QobsO a b j K p
  set E := ECO C (thetaO vh)
  set P := Pobs C j Vo K a b p
  have hvq : v = vh + q := by rw [show vh = v - q from rfl]; abel
  have hR : vt j C Vo K a b p = E - P := by
    rw [vt, ← RHS_eq C hab hCs p]; rfl
  have hPd : P = PobsBB C j Vo K a b p p +
      ∑ p' ∈ (blockIdx (L := L) (N := N) j).erase p, PobsBB C j Vo K a b p p' := by
    exact (add_sum_erase (blockIdx (L := L) (N := N) j) (fun p' => PobsBB C j Vo K a b p p') hp).symm
  have hPP : PobsBB C j Vo K a b p p = (1 / 2 : ℂ) • (ECO C (thetaO vh * thetaO vh) - E * E) := by
    rw [PobsBB, ECT]
  have hE0 : bulk E = 0 := bulk_ECO_thetaO (bulk_Vhat j Vo K a b p) C
  have hPab : IsAB P := Pobs_isAB C j Vo K a b p
  have hsq : (E - P) ^ 2 = E * E := by
    have h1 : E * P = 0 := by rw [mul_comm]; exact hPab.mul_eq_zero hE0
    have h2 : P * E = 0 := hPab.mul_eq_zero hE0
    rw [sq, sub_mul, mul_sub, mul_sub, h1, h2, hPab.mul_eq_zero hPab.bulk_eq_zero]
    simp
  have hL : πobs (ECO C (dIo j C Vb Vo K a b p + thetaO (QO a b j K p))) =
      -ECO C (thetaO v) + (1 / 2 : ℂ) • ECO C (thetaO (v ^ 2)) -
        (-vt j C Vo K a b p + (1 / 2 : ℂ) • vt j C Vo K a b p ^ 2) +
        ECO C (rhoO j C Vb Vo K a b p) + ECO C (thetaO q) := by
    rw [πobs_ECO, map_add, πobs_dIo, πobs_thetaO]
    simp only [map_add, map_sub, map_neg, map_smul, ECO_inclO]
    rfl
  have hv : ECO C (thetaO v) = E + ECO C (thetaO q) := by rw [hvq, map_add, map_add]
  have hY : ECO C (thetaO (v ^ 2 - vh ^ 2)) =
      ECO C (thetaO (v ^ 2)) - ECO C (thetaO vh * thetaO vh) := by
    rw [map_sub, map_sub, sq vh, map_mul]
  rw [hL, hv, hY, hR, hsq, hPd, hPP]
  module

end Block

/-! ### The two-block terms -/

section Pair

variable {c : Case} (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (Vb : Vcoup) (Vo : Coup c)
  (K : Finset (Lam d L N) → OE c (Lam d L N)) (a b : Lam d L N)

/-- `δV̂(B) = θ V̂(B) - Ṽ(B)`. -/
def Aq (p : Fin d → ℕ) : OE c (Lam d L N ⊕ Lam d L N) :=
  thetaO (Vhat j Vo K a b p) - inclO (vt j C Vo K a b p)

/-- The `K`-part and the remainder of `π_obs δI(B)`. -/
def Yq (p : Fin d → ℕ) : OE c (Lam d L N ⊕ Lam d L N) :=
  -thetaO (QobsO a b j K p) + rhoO j C Vb Vo K a b p

/-- The quadratic (`ab`) part of `π_obs δI(B)`. -/
def Zq (p : Fin d → ℕ) : OE c (Lam d L N ⊕ Lam d L N) :=
  (1 / 2 : ℂ) • thetaO (Vobs j Vo a b p ^ 2) - (1 / 2 : ℂ) • inclO (vt j C Vo K a b p ^ 2)

theorem πobs_dIo_eq (p : Fin d → ℕ) :
    πobs (dIo j C Vb Vo K a b p) = -Aq j C Vo K a b p + Yq j C Vb Vo K a b p +
      Zq j C Vo K a b p := by
  rw [πobs_dIo, Aq, Yq, Zq]
  have hv : thetaO (Vobs j Vo a b p) = thetaO (Vhat j Vo K a b p) + thetaO (QobsO a b j K p) := by
    rw [← map_add, Vhat, sub_add_cancel]
  simp only [map_add, map_neg, map_smul]
  rw [hv]
  abel

theorem bulk_Aq (p : Fin d → ℕ) : bulk (Aq j C Vo K a b p) = 0 := by
  rw [Aq, map_sub, bulk_thetaO, bulk_inclO, bulk_Vhat, bulk_splitO]; simp

theorem bulk_Yq (p : Fin d → ℕ) : bulk (Yq j C Vb Vo K a b p) = 0 := by
  rw [Yq, map_add, map_neg, bulk_thetaO, QobsO, bulk_πobs, bulk_rhoO]; simp

theorem isAB_Zq (p : Fin d → ℕ) : IsAB (Zq j C Vo K a b p) := by
  have hv : bulk (thetaO (Vobs j Vo a b p)) = 0 := by
    rw [bulk_thetaO, Vobs, bulk_splitO, map_zero]
  have hvt : bulk (inclO (vt j C Vo K a b p)) = 0 := by
    rw [bulk_inclO, vt, bulk_splitO, map_zero]
  rw [Zq, map_pow, map_pow, sq, sq]
  exact ((isAB_mul hv hv).smul _).sub ((isAB_mul hvt hvt).smul _)

variable {j C Vb Vo K a b}

set_option maxHeartbeats 2000000 in
/-- **The two-block terms** (`lem:Pjj+1` and the proof of `lem:smallset-Vobs`):
`π_obs 𝔼[δI(B) δI(B')] = 2 P^obs(B, B') + 𝔼[(remainder)]` where the remainder consists of
products with a bulk factor, a factor `Q^obs` or a factor `ρ`. -/
theorem pair_eq (hab : a ≠ b) (hCs : C a b = C b a) (p p' : Fin d → ℕ) :
    πobs (ECO C (dIo j C Vb Vo K a b p * dIo j C Vb Vo K a b p')) =
      (2 : ℂ) • PobsBB C j Vo K a b p p' +
        ECO C (emb (bulk (dIo j C Vb Vo K a b p)) * πobs (dIo j C Vb Vo K a b p') +
          πobs (dIo j C Vb Vo K a b p) * emb (bulk (dIo j C Vb Vo K a b p')) -
          Aq j C Vo K a b p * Yq j C Vb Vo K a b p' - Yq j C Vb Vo K a b p * Aq j C Vo K a b p' +
          Yq j C Vb Vo K a b p * Yq j C Vb Vo K a b p') := by
  set A := Aq j C Vo K a b p
  set A' := Aq j C Vo K a b p'
  set Y := Yq j C Vb Vo K a b p
  set Y' := Yq j C Vb Vo K a b p'
  set Z := Zq j C Vo K a b p
  set Z' := Zq j C Vo K a b p'
  have hA := bulk_Aq j C Vo K a b p
  have hA' := bulk_Aq j C Vo K a b p'
  have hY := bulk_Yq j C Vb Vo K a b p
  have hY' := bulk_Yq j C Vb Vo K a b p'
  have hZ := isAB_Zq j C Vo K a b p
  have hZ' := isAB_Zq j C Vo K a b p'
  have hG : bulk (-A' + Y' + Z') = 0 := by
    rw [map_add, map_add, map_neg, hA', hY', hZ'.bulk_eq_zero]; simp
  have hG' : bulk (-A + Y) = 0 := by rw [map_add, map_neg, hA, hY]; simp
  have hoo : πobs (dIo j C Vb Vo K a b p) * πobs (dIo j C Vb Vo K a b p') =
      A * A' - A * Y' - Y * A' + Y * Y' := by
    rw [πobs_dIo_eq, πobs_dIo_eq]
    have h1 : Z * (-A' + Y' + Z') = 0 := hZ.mul_eq_zero hG
    have h2 : (-A + Y) * Z' = 0 := by rw [mul_comm]; exact hZ'.mul_eq_zero hG'
    have e : (-A + Y + Z) * (-A' + Y' + Z') =
        (-A + Y) * (-A' + Y') + Z * (-A' + Y' + Z') + (-A + Y) * Z' := by ring
    rw [e, h1, h2]; ring
  -- `𝔼[A A'] = 2 P(B, B')`
  set E := ECO C (thetaO (Vhat j Vo K a b p))
  set E' := ECO C (thetaO (Vhat j Vo K a b p'))
  set P := Pobs C j Vo K a b p
  set P' := Pobs C j Vo K a b p'
  have hR : vt j C Vo K a b p = E - P := by rw [vt, ← RHS_eq C hab hCs p]; rfl
  have hR' : vt j C Vo K a b p' = E' - P' := by rw [vt, ← RHS_eq C hab hCs p']; rfl
  have hPP : P * P' = 0 := (Pobs_isAB C j Vo K a b p).mul_eq_zero
    (Pobs_isAB C j Vo K a b p').bulk_eq_zero
  have hAA : ECO C (A * A') = (2 : ℂ) • PobsBB C j Vo K a b p p' := by
    have e : A * A' = thetaO (Vhat j Vo K a b p) * thetaO (Vhat j Vo K a b p') -
        inclO (vt j C Vo K a b p') * thetaO (Vhat j Vo K a b p) -
        inclO (vt j C Vo K a b p) * thetaO (Vhat j Vo K a b p') +
        inclO (vt j C Vo K a b p * vt j C Vo K a b p') := by
      rw [map_mul]; simp only [A, A', Aq]; ring
    rw [e, map_add, map_sub, map_sub, ECO_inclO_mul, ECO_inclO_mul, ECO_inclO, PobsBB, ECT,
      smul_smul, hR, hR']
    norm_num
    rw [show (E - P) * (E' - P') = E * E' - P * E' - E * P' + P * P' by ring, hPP]
    ring
  rw [πobs_ECO, πobs_mul, hoo, ← hAA]
  simp only [map_add, map_sub]
  abel

/-! ### Blocks without source points -/

theorem splitO_of_not_mem {V : Coup c} {X : Finset (Lam d L N)} (ha : a ∉ X) (hb : b ∉ X) :
    splitO c V a b X = 0 := by
  simp [splitO, ha, hb]

theorem πobs_dIo_of_not_mem {p : Fin d → ℕ} (ha : a ∉ blockSet (L := L) (N := N) j p)
    (hb : b ∉ blockSet (L := L) (N := N) j p) : πobs (dIo j C Vb Vo K a b p) = 0 := by
  have h1 : πobs ((obsI j C Vb Vo K a b).I0 p) = 0 := by
    simp only [obsI, VfullX, splitO_of_not_mem ha hb, add_zero]
    rw [← map_neg, oexp_emb, πobs_emb]
    rw [NegMemClass.coe_neg, map_neg, ε_VE, neg_zero]
  have h2 : πobs (It (obsI j C Vb Vo K a b) p) = 0 := by
    rw [It_fac, splitO_of_not_mem ha hb, neg_zero, oexp_zero, mul_one, πobs_emb]
  simp only [dIo, dIG, obsA, map_sub, πobs_thetaO, πobs_inclO, h1, h2, map_zero, sub_zero]

/-- `π_obs (δI)^X = δI(B₀) π_obs ∏_{B ≠ B₀} δI(B)` if `B₀ ∈ 𝓑_j(X)` has no source point. -/
theorem πobs_dIPowG_of_block {X : Finset (Lam d L N)} {p₀ : Fin d → ℕ} (hp₀ : p₀ ∈ blocks j X)
    (h0 : πobs (dIo j C Vb Vo K a b p₀) = 0) :
    πobs (dIPowG (obsA c C) j (obsI j C Vb Vo K a b) X) =
      emb (bulk (dIo j C Vb Vo K a b p₀)) *
        πobs (∏ p ∈ (blocks j X).erase p₀, dIo j C Vb Vo K a b p) := by
  have e : dIo j C Vb Vo K a b p₀ = emb (bulk (dIo j C Vb Vo K a b p₀)) := by
    have := eq_emb_add_πobs (dIo j C Vb Vo K a b p₀)
    rw [h0, add_zero] at this; exact this
  rw [dIPowG, bpow, ← mul_prod_erase _ _ hp₀, πobs_mul', ← e, h0, zero_mul, add_zero]

/-! ### `P^obs(B, B') = 0` unless `a, b` lie in `B, B'` in the same `(j+1)`-block -/

theorem ECT_zero_left' (F : OE c (Lam d L N)) : ECT C 0 F = 0 := by simp [ECT]

theorem ECT_zero_right' (F : OE c (Lam d L N)) : ECT C F 0 = 0 := by simp [ECT]

theorem ECT_isAB_left {F G : OE c (Lam d L N)} (hF : IsAB F) (hG : bulk G = 0) :
    ECT C F G = 0 := by
  have h1 : IsAB (thetaO F) := ⟨by simp [hF.1], by simp [hF.2.1], by simp [hF.2.2]⟩
  have h2 : bulk (thetaO G) = 0 := by rw [bulk_thetaO, hG, map_zero]
  rw [ECT, h1.mul_eq_zero h2, (hF.ECO_thetaO C).mul_eq_zero (bulk_ECO_thetaO hG C), map_zero,
    sub_zero]

theorem halfA_a_mem (W : Coup c) : (halfA c W a b).a ∈ NX ({a} : Set (Lam d L N)) := by
  have hψ : ∀ s : ℤˣ, ψ (a, s) ∈ NX ({a} : Set (Lam d L N)) := fun s => ψ_mem_NX rfl
  cases c
  · exact Subalgebra.smul_mem _ (hψ _) _
  · exact sub_mem (Subalgebra.algebraMap_mem _ _)
      (Subalgebra.smul_mem _ (mul_mem (hψ _) (hψ _)) _)

theorem halfB_b_mem (W : Coup c) : (halfB c W a b).b ∈ NX ({b} : Set (Lam d L N)) := by
  have hψ : ∀ s : ℤˣ, ψ (b, s) ∈ NX ({b} : Set (Lam d L N)) := fun s => ψ_mem_NX rfl
  cases c
  · exact Subalgebra.smul_mem _ (hψ _) _
  · exact sub_mem (Subalgebra.algebraMap_mem _ _)
      (Subalgebra.smul_mem _ (mul_mem (hψ _) (hψ _)) _)

set_option maxHeartbeats 2000000 in
/-- `𝔼[θ H_a; θ H_b] = 0` if `C(a, b) = C(b, a) = 0`. -/
theorem ECT_half_sep (W : Coup c) (hab : a ≠ b) (h1 : C a b = 0) (h2 : C b a = 0) :
    ECT C (halfAO c W a b) (halfBO c W a b) = 0 := by
  set F := halfAO c W a b
  set G := halfBO c W a b
  have hFe : (F : SA c (Lam d L N)).e = 0 := by cases c <;> rfl
  have hFb : (F : SA c (Lam d L N)).b = 0 := by cases c <;> rfl
  have hGe : (G : SA c (Lam d L N)).e = 0 := by cases c <;> rfl
  have hGa : (G : SA c (Lam d L N)).a = 0 := by cases c <;> rfl
  have eF : F = πa F + πab F := by
    refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;> simp [pia_apply, piab_apply, hFe, hFb]
  have eG : G = πb G + πab G := by
    refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;> simp [pib_apply, piab_apply, hGe, hGa]
  have habF : IsAB (πab F) := ⟨by simp [piab_apply], by simp [piab_apply], by simp [piab_apply]⟩
  have habG : IsAB (πab G) := ⟨by simp [piab_apply], by simp [piab_apply], by simp [piab_apply]⟩
  have hbaF : bulk (πa F) = 0 := Subtype.ext (by simp [pia_apply])
  have hbbG : bulk (πb G) = 0 := Subtype.ext (by simp [pib_apply])
  have hbG : bulk G = 0 := bulk_halfBO c W a b
  -- the separated part
  have hsep : ECT C (πa F) (πb G) = 0 := by
    have hX : ∀ x ∈ ({a} : Set (Lam d L N)), ∀ y ∈ ({b} : Set (Lam d L N)),
        x ≠ y ∧ C x y = 0 ∧ C y x = 0 := by
      rintro x rfl y rfl; exact ⟨hab, h1, h2⟩
    have hmF : thetaO (πa F) ∈ (compSub (NX2 ({a} : Set (Lam d L N))) True True :
        Subalgebra ℂ (OE c (Lam d L N ⊕ Lam d L N))) := by
      refine ⟨?_, ?_, ?_, ?_, fun h => absurd trivial h, fun h => absurd trivial h⟩
      · simp [pia_apply]
      · simp only [coe_thetaO, thetaS_a, coe_πa, pia_apply]
        exact theta_mem_NX2 (halfA_a_mem W)
      · simp [pia_apply]
      · simp [pia_apply]
    have hmG : thetaO (πb G) ∈ (compSub (NX2 ({b} : Set (Lam d L N))) True True :
        Subalgebra ℂ (OE c (Lam d L N ⊕ Lam d L N))) := by
      refine ⟨?_, ?_, ?_, ?_, fun h => absurd trivial h, fun h => absurd trivial h⟩
      · simp [pib_apply]
      · simp [pib_apply]
      · simp only [coe_thetaO, thetaS_b, coe_πb, pib_apply]
        exact theta_mem_NX2 (halfB_b_mem W)
      · simp [pib_apply]
    rw [ECT, ECO_mul_of_sep hX hmF hmG, sub_self]
  rw [eF, eG, ECT_add_left, ECT_isAB_left habF (by rw [← eG]; exact hbG), add_zero, ECT_comm,
    ECT_add_left, ECT_isAB_left habG hbaF, add_zero, ECT_comm, hsep]

/-- **`P^obs(B, B') = 0`** for `B ≠ B'` unless one of them contains `a`, the other `b`, and
`a, b` lie in the same `(j+1)`-block (using `SepHyp`). -/
theorem PobsBB_eq_zero (hab : a ≠ b) (hsep : SepHyp j C a b) (hsym : C b a = C a b)
    {p p' : Fin d → ℕ} (hne : p ≠ p')
    (h : ¬ (blk (j + 1) a = blk (j + 1) b ∧
      (a ∈ blockSet (L := L) (N := N) j p ∧ b ∈ blockSet (L := L) (N := N) j p' ∨
        b ∈ blockSet (L := L) (N := N) j p ∧ a ∈ blockSet (L := L) (N := N) j p'))) :
    PobsBB C j Vo K a b p p' = 0 := by
  rw [PobsBB, Vhat_eq hab, Vhat_eq hab]
  set W := Wcoup j Vo K a b
  have hd : Disjoint (blockSet (L := L) (N := N) j p) (blockSet j p') := blockSet_disjoint hne
  by_cases ha : a ∈ blockSet (L := L) (N := N) j p
  · have ha' : a ∉ blockSet (L := L) (N := N) j p' := Finset.disjoint_left.1 hd ha
    by_cases hb' : b ∈ blockSet (L := L) (N := N) j p'
    · have hb : b ∉ blockSet (L := L) (N := N) j p := fun hb => Finset.disjoint_left.1 hd hb hb'
      have hblk : blk (j + 1) a ≠ blk (j + 1) b := fun e => h ⟨e, Or.inl ⟨ha, hb'⟩⟩
      rw [splitO_of_mem_not_mem c W a b ha hb, splitO_of_not_mem_mem c W a b ha' hb',
        ECT_half_sep W hab (hsep hblk) (hsym.trans (hsep hblk)), smul_zero]
    · rw [splitO_of_not_mem ha' hb', ECT_zero_right', smul_zero]
  · by_cases hb : b ∈ blockSet (L := L) (N := N) j p
    · have hb' : b ∉ blockSet (L := L) (N := N) j p' := Finset.disjoint_left.1 hd hb
      by_cases ha' : a ∈ blockSet (L := L) (N := N) j p'
      · have hblk : blk (j + 1) a ≠ blk (j + 1) b := fun e => h ⟨e, Or.inr ⟨hb, ha'⟩⟩
        rw [splitO_of_not_mem_mem c W a b ha hb, splitO_of_mem_not_mem c W a b ha' hb', ECT_comm,
          ECT_half_sep W hab (hsep hblk) (hsym.trans (hsep hblk)), smul_zero]
      · rw [splitO_of_not_mem ha' hb', ECT_zero_right', smul_zero]
    · rw [splitO_of_not_mem ha hb, ECT_zero_left', smul_zero]

end Pair

end

end Obs
