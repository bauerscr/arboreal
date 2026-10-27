import Obs.StepObsStmt

/-!
# Theorem `thm:step-obs`: the coupling constants (subsection "Coupling constants")

Norm estimates for the observable coupling constants, in the norms `nrmj` of
`Obs.StepObsStmt` (`‖·‖_{T_k(ℓ_k)}` with the weights of scale `k`, `j_ab = coal L a b`).
Throughout `K₂ = L^{2(d-2)}` is the constant of `e:Tphi-obs-ub` (`normj_succ_le`).

## Basic norm facts
`nrmj_split` (`‖F‖ = ‖F_∅‖ + ‖π_obs F‖`), `nrmj_add_le`, `nrmj_mul_le` (product property),
`nrmj_ECO_le` (`‖𝔼 θ F‖_{j+1} ≤ K₂ ‖F‖_j`), `nrmj_ECT_le`
(`‖𝔼[θF; θG]‖_{j+1} ≤ 2 K₂² ‖F‖_j ‖G‖_j`).
-/

namespace Obs

noncomputable section

open Finset Grassmann SA Loc Step LocObs Gen

variable {d L N : ℕ} [NeZero L]

/-! ### Basic norm facts -/

section Basic

variable {c : Case} {ℓ₀ : ℝ} {a b : Lam d L N}

theorem πobs_of_bulk {F : OE c (Lam d L N)} (hF : bulk F = 0) : πobs F = F := by
  have h := eq_emb_add_πobs F
  rw [hF, map_zero, zero_add] at h
  exact h.symm

theorem nrmj_split (j : ℕ) (F : OE c (Lam d L N)) :
    nrmj c ℓ₀ a b j F = Tj d (L : ℝ) j (ellj d L ℓ₀ j) ((bulk F : EvR (Lam d L N)) : Alg d L N) +
      nrmj c ℓ₀ a b j (πobs F) := by
  simp only [nrmj, normj, oTj, oNorm, coe_πobs, piobs_apply, coe_bulk]
  rw [Tj_zero]; ring

theorem Tj_bulk_le_nrmj (j : ℕ) (F : OE c (Lam d L N)) :
    Tj d (L : ℝ) j (ellj d L ℓ₀ j) ((bulk F : EvR (Lam d L N)) : Alg d L N) ≤
      nrmj c ℓ₀ a b j F := by
  rw [nrmj_split]; exact le_self_add

theorem nrmj_πobs_le (j : ℕ) (F : OE c (Lam d L N)) :
    nrmj c ℓ₀ a b j (πobs F) ≤ nrmj c ℓ₀ a b j F := by
  rw [nrmj_split (F := F)]; exact le_add_self

theorem nrmj_emb (j : ℕ) (x : EvR (Lam d L N)) :
    nrmj c ℓ₀ a b j (emb x) = Tj d (L : ℝ) j (ellj d L ℓ₀ j) (x : Alg d L N) := by
  rw [nrmj_split, πobs_emb, bulk_emb]
  simp only [nrmj, normj, oTj, oNorm]
  simp [Tj_zero]

theorem nrmj_zero (j : ℕ) : nrmj c ℓ₀ a b j (0 : OE c (Lam d L N)) = 0 := by
  have := nrmj_emb (c := c) (ℓ₀ := ℓ₀) (a := a) (b := b) j 0
  rw [map_zero] at this
  rw [this]
  exact Tj_zero _ _ _

theorem nrmj_add_le (j : ℕ) (F G : OE c (Lam d L N)) :
    nrmj c ℓ₀ a b j (F + G) ≤ nrmj c ℓ₀ a b j F + nrmj c ℓ₀ a b j G :=
  oT_add_le (E := Dir d) (p := pPhi d) (h := (L : ℝ) ^ j) (ℓ := ellj d L ℓ₀ j) _ _

theorem nrmj_neg (j : ℕ) (F : OE c (Lam d L N)) :
    nrmj c ℓ₀ a b j (-F) = nrmj c ℓ₀ a b j F :=
  oT_neg (E := Dir d) (p := pPhi d) (h := (L : ℝ) ^ j) (ℓ := ellj d L ℓ₀ j) _

theorem nrmj_sub_le (j : ℕ) (F G : OE c (Lam d L N)) :
    nrmj c ℓ₀ a b j (F - G) ≤ nrmj c ℓ₀ a b j F + nrmj c ℓ₀ a b j G :=
  oT_sub_le (E := Dir d) (p := pPhi d) (h := (L : ℝ) ^ j) (ℓ := ellj d L ℓ₀ j) _ _

theorem nrmj_smul (j : ℕ) (r : ℂ) (F : OE c (Lam d L N)) :
    nrmj c ℓ₀ a b j (r • F) = ENNReal.ofReal ‖r‖ * nrmj c ℓ₀ a b j F :=
  oT_smul (E := Dir d) (p := pPhi d) (h := (L : ℝ) ^ j) (ℓ := ellj d L ℓ₀ j) r _

theorem nrmj_sum_le (j : ℕ) {ι : Type*} (s : Finset ι) (F : ι → OE c (Lam d L N)) :
    nrmj c ℓ₀ a b j (∑ i ∈ s, F i) ≤ ∑ i ∈ s, nrmj c ℓ₀ a b j (F i) := by
  have := oT_sum_le (E := Dir d) (p := pPhi d) (h := (L : ℝ) ^ j) (ℓ := ellj d L ℓ₀ j)
    (w := wj d L c ℓ₀ (coal L a b : ℕ∞) j) s (fun i => (F i : SA c (Lam d L N)))
  simpa [nrmj, normj, oTj, AddSubmonoidClass.coe_finsetSum] using this

theorem nrmj_half_smul (j : ℕ) (F : OE c (Lam d L N)) :
    nrmj c ℓ₀ a b j ((1 / 2 : ℂ) • F) ≤ nrmj c ℓ₀ a b j F := by
  rw [nrmj_smul]
  refine mul_le_of_le_one_left bot_le ?_
  rw [← ENNReal.ofReal_one]; refine ENNReal.ofReal_le_ofReal ?_
  norm_num

/-- The product property (`e:T-product` with observables). -/
theorem nrmj_mul_le (hd : 2 ≤ d) (hℓ₀ : 0 < ℓ₀) (j : ℕ) (F G : OE c (Lam d L N)) :
    nrmj c ℓ₀ a b j (F * G) ≤ nrmj c ℓ₀ a b j F * nrmj c ℓ₀ a b j G := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  exact oT_mul_le (by positivity) (ellj_pos hL0 hℓ₀ j) (wj_sub hd c hℓ₀ _ j) F G

/-- `‖𝔼_{C_{j+1}} θ F‖_{j+1} ≤ L^{2(d-2)} ‖F‖_j`. -/
theorem nrmj_ECO_le (hd : 3 ≤ d) (hL : (4 : ℝ) ≤ L) (hℓ₀ : 0 < ℓ₀) {j : ℕ}
    {C : Matrix (Lam d L N) (Lam d L N) ℝ} (hC : GoodCov j ℓ₀ C) (F : OE c (Lam d L N)) :
    nrmj c ℓ₀ a b (j + 1) (ECO C (thetaO F)) ≤
      ENNReal.ofReal ((L : ℝ) ^ (2 * ((d : ℝ) - 2))) * nrmj c ℓ₀ a b j F :=
  normj_EC_theta_le hd hL c hℓ₀ _ j hC.psd hC.norm _

/-- `‖𝔼_{C_{j+1}}[θ F; θ G]‖_{j+1} ≤ 2 L^{4(d-2)} ‖F‖_j ‖G‖_j` (product property, contraction
of `𝔼 θ`, `e:Tphi-obs-ub`). -/
theorem nrmj_ECT_le (hd : 3 ≤ d) (hL : (4 : ℝ) ≤ L) (hℓ₀ : 0 < ℓ₀) {j : ℕ}
    {C : Matrix (Lam d L N) (Lam d L N) ℝ} (hC : GoodCov j ℓ₀ C) (F G : OE c (Lam d L N)) :
    nrmj c ℓ₀ a b (j + 1) (ECT C F G) ≤
      ENNReal.ofReal (2 * ((L : ℝ) ^ (2 * ((d : ℝ) - 2))) ^ 2) *
        (nrmj c ℓ₀ a b j F * nrmj c ℓ₀ a b j G) := by
  have hL0 : (0 : ℝ) < L := by linarith
  set K₂ := (L : ℝ) ^ (2 * ((d : ℝ) - 2)) with hK₂
  have hK0 : 0 ≤ K₂ := by positivity
  have hh : (0 : ℝ) < (L : ℝ) ^ (j + 1) := by positivity
  have hℓ := ellj_pos (d := d) hL0 hℓ₀ (j + 1)
  have hw := wj_sub (d := d) (L := L) (by omega) c hℓ₀ (coal L a b : ℕ∞) (j + 1)
  have h2 : ∀ H : OE c (Lam d L N),
      oTj d L (wj d L c ℓ₀ (coal L a b : ℕ∞) (j + 1)) (j + 1) (2 * ellj d L ℓ₀ (j + 1))
        (H : SA c (Lam d L N)) ≤ ENNReal.ofReal K₂ * nrmj c ℓ₀ a b j H :=
    fun H => (normj_succ_le hd hL c hℓ₀ _ j _).2
  -- the first term
  have e1 : nrmj c ℓ₀ a b (j + 1) (ECO C (thetaO F * thetaO G)) ≤
      ENNReal.ofReal K₂ * nrmj c ℓ₀ a b j F * (ENNReal.ofReal K₂ * nrmj c ℓ₀ a b j G) := by
    refine (oT_EC_le (E := Dir d) (p := pPhi d) hh hℓ hC.psd hC.norm _).trans ?_
    refine (oT_mul_le hh hℓ hw (thetaO F) (thetaO G)).trans ?_
    gcongr
    · exact (oT_theta_le hh hℓ _).trans (h2 F)
    · exact (oT_theta_le hh hℓ _).trans (h2 G)
  have e2 : nrmj c ℓ₀ a b (j + 1) (ECO C (thetaO F) * ECO C (thetaO G)) ≤
      ENNReal.ofReal K₂ * nrmj c ℓ₀ a b j F * (ENNReal.ofReal K₂ * nrmj c ℓ₀ a b j G) := by
    refine (nrmj_mul_le (by omega) hℓ₀ _ _ _).trans ?_
    gcongr
    · exact nrmj_ECO_le hd hL hℓ₀ hC F
    · exact nrmj_ECO_le hd hL hℓ₀ hC G
  have e3 : ENNReal.ofReal K₂ * nrmj c ℓ₀ a b j F * (ENNReal.ofReal K₂ * nrmj c ℓ₀ a b j G) =
      ENNReal.ofReal (K₂ ^ 2) * (nrmj c ℓ₀ a b j F * nrmj c ℓ₀ a b j G) := by
    rw [sq, ENNReal.ofReal_mul hK0]; ring
  refine (nrmj_sub_le _ _ _).trans ((add_le_add e1 e2).trans (le_of_eq ?_))
  rw [e3, ← two_mul, ← mul_assoc, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_ofNat]

end Basic

/-! ### Split evaluations on polymers -/

section Split

variable {c : Case} {a b : Lam d L N}

theorem sum_le_of_subadd {ι : Type*} (n : OE c (Lam d L N) → ENNReal) (hn0 : n 0 = 0)
    (hadd : ∀ F G, n (F + G) ≤ n F + n G) (s : Finset ι) (F : ι → OE c (Lam d L N)) :
    n (∑ i ∈ s, F i) ≤ ∑ i ∈ s, n (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hn0]
  | insert i s hi ih =>
    rw [sum_insert hi, sum_insert hi]
    exact (hadd _ _).trans (add_le_add le_rfl ih)

/-- `W(X) = ∑_{B ∈ 𝓑_j(X)} W(B)` for the split evaluation on polymers. -/
theorem splitO_eq_sum_blocks (W : Coup c) {j : ℕ} {X : Finset (Lam d L N)} (hX : IsPolymer j X) :
    splitO c W a b X = ∑ p ∈ blocks j X, splitO c W a b (blockSet j p) := by
  have hd : ((blocks j X : Finset (Fin d → ℕ)) : Set (Fin d → ℕ)).PairwiseDisjoint
      (blockSet (L := L) (N := N) j) := fun _ _ _ _ hne => blockSet_disjoint hne
  conv_lhs => rw [← biUnion_blocks hX]
  exact splitO_biUnion c _ a b _ _ hd

/-- Only the (at most two) blocks containing `a` or `b` contribute to a split evaluation: for a
subadditive `n` with `n 0 = 0` and `X ∈ 𝒫_j`, `n(W(X)) ≤ 2 sup_{B ∈ 𝓑_j} n(W(B))`. -/
theorem splitO_polymer_le (n : OE c (Lam d L N) → ENNReal) (hn0 : n 0 = 0)
    (hadd : ∀ F G, n (F + G) ≤ n F + n G) (W : Coup c) {j : ℕ} {X : Finset (Lam d L N)}
    (hX : IsPolymer j X) :
    n (splitO c W a b X) ≤
      2 * ⨆ p ∈ blockIdx (L := L) (N := N) j, n (splitO c W a b (blockSet j p)) := by
  classical
  set M := ⨆ p ∈ blockIdx (L := L) (N := N) j, n (splitO c W a b (blockSet j p))
  rw [splitO_eq_sum_blocks W hX]
  have hfil : ∑ p ∈ blocks j X, splitO c W a b (blockSet j p) =
      ∑ p ∈ (blocks j X).filter (fun p => p = blk j a ∨ p = blk j b),
        splitO c W a b (blockSet j p) := by
    refine (sum_filter_of_ne fun p _ hp => ?_).symm
    by_contra hne
    push Not at hne
    apply hp
    rw [splitO_congr c W a b (Y := ∅)
      (by simp only [Finset.notMem_empty, iff_false, Loc.mem_blockSet]; exact fun h => hne.1 h.symm)
      (by simp only [Finset.notMem_empty, iff_false, Loc.mem_blockSet]; exact fun h => hne.2 h.symm),
      splitO_empty]
  rw [hfil]
  refine (sum_le_of_subadd n hn0 hadd _ _).trans ?_
  have hcard : ((blocks j X).filter (fun p => p = blk j a ∨ p = blk j b)).card ≤ 2 := by
    refine (card_le_card (s := _) (t := {blk j a, blk j b}) fun p hp => ?_).trans card_le_two
    rcases (mem_filter.1 hp).2 with h | h <;> simp [h]
  calc ∑ p ∈ (blocks j X).filter (fun p => p = blk j a ∨ p = blk j b),
        n (splitO c W a b (blockSet j p))
      ≤ ((blocks j X).filter (fun p => p = blk j a ∨ p = blk j b)).card • M :=
        sum_le_card_nsmul _ _ _ fun p hp =>
          le_iSup₂_of_le (f := fun p _ => n (splitO c W a b (blockSet j p))) p
            (mem_blockIdx_of_mem_blocks (mem_filter.1 hp).1) le_rfl
    _ ≤ 2 • M := nsmul_le_nsmul_left zero_le hcard
    _ = 2 * M := by rw [nsmul_eq_mul]; rfl

variable {ℓ₀ : ℝ}

/-- `‖W(X)‖ ≤ 2 sup_B ‖W(B)‖` for `X ∈ 𝒫_j`, in the norm of any scale `k`. -/
theorem nrmj_splitO_polymer_le (k : ℕ) (W : Coup c) {j : ℕ} {X : Finset (Lam d L N)}
    (hX : IsPolymer j X) :
    nrmj c ℓ₀ a b k (splitO c W a b X) ≤
      2 * ⨆ p ∈ blockIdx (L := L) (N := N) j, nrmj c ℓ₀ a b k (splitO c W a b (blockSet j p)) :=
  splitO_polymer_le _ (nrmj_zero k) (nrmj_add_le k) W hX

/-- `‖V^obs_j(B)‖ ≤ ‖V^obs_j‖_j`. -/
theorem nrmj_Vobs_le {j : ℕ} (Vo : Coup c) {p : Fin d → ℕ}
    (hp : p ∈ blockIdx (L := L) (N := N) j) :
    nrmj c ℓ₀ a b j (Vobs j Vo a b p) ≤ VnormObs c ℓ₀ a b j Vo :=
  le_iSup₂_of_le (f := fun p _ => nrmj c ℓ₀ a b j (splitO c (Coup.toV c Vo) a b (blockSet j p)))
    p hp le_rfl

/-- `‖V^obs_j(X)‖ ≤ 2 ‖V^obs_j‖_j` for `X ∈ 𝒫_j`, in particular for `X = Λ`. -/
theorem nrmj_VobsX_le {j : ℕ} (Vo : Coup c) {X : Finset (Lam d L N)} (hX : IsPolymer j X) :
    nrmj c ℓ₀ a b j (splitO c (Coup.toV c Vo) a b X) ≤ 2 * VnormObs c ℓ₀ a b j Vo :=
  nrmj_splitO_polymer_le j _ hX

theorem nrmj_VobsL_le {j : ℕ} (Vo : Coup c) :
    nrmj c ℓ₀ a b j (evalO c (Coup.toV c Vo) a b univ) ≤ 2 * VnormObs c ℓ₀ a b j Vo := by
  rw [← splitO_univ]; exact nrmj_VobsX_le Vo (isPolymer_univ j)

end Split

/-! ### Norms of `K` -/

section KNorm

variable {c : Case} {ℓ₀ : ℝ} {a b : Lam d L N}

theorem nrmj_le_wnormO {j : ℕ} {A : ℝ} (hA : 1 ≤ A) (U : Finset (Lam d L N))
    (F : OE c (Lam d L N)) : nrmj c ℓ₀ a b j F ≤ wnormO c ℓ₀ a b j A U F :=
  le_mul_of_one_le_left zero_le (one_le_ofReal_pow hA _)

theorem wnormO_le_KnormFull {j : ℕ} {A : ℝ} {K : Finset (Lam d L N) → OE c (Lam d L N)}
    {X : Finset (Lam d L N)} (hX : IsConn j X) :
    wnormO c ℓ₀ a b j A X (K X) ≤ KnormFull c ℓ₀ a b j A K := by
  classical
  exact le_iSup₂_of_le (f := fun X _ => wnormO c ℓ₀ a b j A X (K X)) X (by simp [connSets, hX])
    le_rfl

/-- `‖K(X)‖_{T_j(ℓ_j)} ≤ ‖K‖_j` for connected `X`. -/
theorem nrmj_le_KnormFull {j : ℕ} {A : ℝ} (hA : 1 ≤ A) {K : Finset (Lam d L N) → OE c (Lam d L N)}
    {X : Finset (Lam d L N)} (hX : IsConn j X) :
    nrmj c ℓ₀ a b j (K X) ≤ KnormFull c ℓ₀ a b j A K :=
  (nrmj_le_wnormO hA X _).trans (wnormO_le_KnormFull hX)

/-- `‖π_obs K(X)‖_{T_j(ℓ_j)} ≤ ‖K^obs‖_j` for connected `X`. -/
theorem nrmj_le_KnormObs {j : ℕ} {A : ℝ} (hA : 1 ≤ A) {K : Finset (Lam d L N) → OE c (Lam d L N)}
    {X : Finset (Lam d L N)} (hX : IsConn j X) :
    nrmj c ℓ₀ a b j (πobs (K X)) ≤ KnormObs c ℓ₀ a b j A K :=
  nrmj_le_KnormFull (K := fun X => πobs (K X)) hA hX

/-- `‖K^obs‖_j ≤ ‖K‖_j`. -/
theorem KnormObs_le_KnormFull (j : ℕ) (A : ℝ) (K : Finset (Lam d L N) → OE c (Lam d L N)) :
    KnormObs c ℓ₀ a b j A K ≤ KnormFull c ℓ₀ a b j A K :=
  iSup₂_mono fun _ _ => by rw [wnormO, wnormO]; gcongr; exact nrmj_πobs_le j _

/-- `‖K^∅‖_j ≤ ‖K‖_j`. -/
theorem Knorm_bulk_le_KnormFull (j : ℕ) (A : ℝ) (K : Finset (Lam d L N) → OE c (Lam d L N)) :
    Knorm j (ellj d L ℓ₀ j) A (bulkK K) ≤ KnormFull c ℓ₀ a b j A K :=
  iSup₂_mono fun X _ => by rw [wnormO]; gcongr; exact Tj_bulk_le_nrmj j (K X)

/-- `‖K‖_j ≤ ‖K^∅‖_j + ‖K^obs‖_j`. -/
theorem KnormFull_le (j : ℕ) (A : ℝ) (K : Finset (Lam d L N) → OE c (Lam d L N)) :
    KnormFull c ℓ₀ a b j A K ≤
      Knorm j (ellj d L ℓ₀ j) A (bulkK K) + KnormObs c ℓ₀ a b j A K := by
  refine iSup₂_le fun X hX => ?_
  rw [wnormO, nrmj_split, mul_add]
  exact add_le_add (le_iSup₂_of_le (f := fun X _ => ENNReal.ofReal (A ^ (nb j X - 2 ^ d)) *
      Tj d (L : ℝ) j (ellj d L ℓ₀ j) ((bulkK K X : EvR (Lam d L N)) : Alg d L N)) X hX le_rfl)
    (le_iSup₂_of_le (f := fun X _ => wnormO c ℓ₀ a b j A X (πobs (K X))) X hX le_rfl)

/-- `‖V^∅‖_j ≤ ‖V‖_j` and `‖V^obs‖_j ≤ ‖V‖_j`. -/
theorem Vnorm_le_VnormFull (j : ℕ) (Vb : Vcoup) (Vo : Coup c) :
    Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) Vb ≤ VnormFull c ℓ₀ a b j Vb Vo ∧
      VnormObs c ℓ₀ a b j Vo ≤ VnormFull c ℓ₀ a b j Vb Vo := by
  constructor
  · refine iSup₂_mono fun p _ => ?_
    have := Tj_bulk_le_nrmj (c := c) (ℓ₀ := ℓ₀) (a := a) (b := b) j (VfullX Vb Vo a b (blockSet j p))
    rwa [bulk_VfullX, coe_VE] at this
  · refine iSup₂_mono fun p _ => ?_
    have := nrmj_πobs_le (c := c) (ℓ₀ := ℓ₀) (a := a) (b := b) j (VfullX Vb Vo a b (blockSet j p))
    rwa [VfullX, map_add, πobs_emb, zero_add, πobs_of_bulk (bulk_splitO _ _ _ _ _)] at this

end KNorm

/-! ### `e:Qobsbd`: the bounds on `Q^obs` and `J^obs` -/

section QJ

variable {c : Case} {ℓ₀ : ℝ} {a b : Lam d L N}

theorem nrmj_πobs_eq (j : ℕ) (F : OE c (Lam d L N)) :
    nrmj c ℓ₀ a b j (πobs F) =
      (wj d L c ℓ₀ (coal L a b : ℕ∞) j).a * Tj d (L : ℝ) j (ellj d L ℓ₀ j) (F : SA c (Lam d L N)).a +
      (wj d L c ℓ₀ (coal L a b : ℕ∞) j).b * Tj d (L : ℝ) j (ellj d L ℓ₀ j) (F : SA c (Lam d L N)).b +
      (wj d L c ℓ₀ (coal L a b : ℕ∞) j).ab *
        Tj d (L : ℝ) j (ellj d L ℓ₀ j) (F : SA c (Lam d L N)).ab := by
  simp only [nrmj, normj, oTj, oNorm, coe_πobs, piobs_apply]
  rw [Tj_zero, zero_add]

theorem nrmj_sum_card_le (k : ℕ) {ι : Type*} (s : Finset ι) (F : ι → OE c (Lam d L N))
    (M : ENNReal) (h : ∀ i ∈ s, nrmj c ℓ₀ a b k (F i) ≤ M) (n : ℕ) (hs : s.card ≤ n) :
    nrmj c ℓ₀ a b k (∑ i ∈ s, F i) ≤ n * M :=
  (nrmj_sum_le k s F).trans ((sum_le_card_nsmul _ _ _ h).trans (by
    rw [nsmul_eq_mul]; gcongr))

/-- **`e:Qobsbd`** and the bound on `J^obs`: `‖Q^obs(B)‖_{T_j(ℓ_j)} ≤ C_Q ‖K^obs‖_j`,
`‖π_obs J(B, X)‖_{T_j(ℓ_j)} ≤ C_Q ‖K^obs‖_j`, and (for `a ≠ b`)
`‖Q^obs(Λ)‖_{T_j(ℓ_j)} ≤ 2 C_Q ‖K^obs‖_j`, where `C_Q` depends only on `d`.  (Proposition
`prop:Loc-obs` (i) and the number of small sets containing a block; at the level of `Λ` only
the blocks containing `a` or `b` contribute.) -/
theorem Qobs_bounds (d : ℕ) : ∃ Cq : ℝ, 0 ≤ Cq ∧ ∀ (L : ℕ) [NeZero L], 2 ^ (d + 3) + 8 * d < L →
    ∀ (N j : ℕ), j < N → ∀ (ℓ₀ : ℝ), 0 < ℓ₀ →
    ∀ (c : Case) (P : Prop) (K : Finset (Lam d L N) → OE c (Lam d L N)) (a b : Lam d L N)
      (A : ℝ), 1 ≤ A → InKO c P a b j K →
      (∀ p ∈ blockIdx (L := L) (N := N) j,
        nrmj c ℓ₀ a b j (QobsO a b j K p) ≤ ENNReal.ofReal Cq * KnormObs c ℓ₀ a b j A K) ∧
      (∀ p ∈ blockIdx (L := L) (N := N) j, ∀ X : Finset (Lam d L N),
        nrmj c ℓ₀ a b j (πobs (JO a b j K p X)) ≤ ENNReal.ofReal Cq * KnormObs c ℓ₀ a b j A K) ∧
      (a ≠ b → nrmj c ℓ₀ a b j (∑ p ∈ blockIdx (L := L) (N := N) j, QobsO a b j K p) ≤
        ENNReal.ofReal (2 * Cq) * KnormObs c ℓ₀ a b j A K) := by
  classical
  obtain ⟨Cb, hCb, hloc⟩ := locObs_bound_comp d
  obtain ⟨cs, hcs⟩ := card_small_containing d
  refine ⟨(cs + 1) * Cb, by positivity, ?_⟩
  intro L _ hL N j hj ℓ₀ hℓ₀ c P K a b A hA hK
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hℓ := ellj_pos (d := d) hL0 hℓ₀ j
  set ko := KnormObs c ℓ₀ a b j A K
  -- one small set
  have key : ∀ X B : Finset (Lam d L N), IsSmall j X → B ⊆ X →
      nrmj c ℓ₀ a b j (πobs (LocO a b X B (K X))) ≤ ENNReal.ofReal Cb * ko := by
    intro X B hX hBX
    have hXc : IsConn j X := ⟨hX.1, hX.2.1⟩
    obtain ⟨-, ha, hb, hab', -, -⟩ := mem_compSub.1 (Algebra.mem_inf.1 (hK X hXc)).1
    obtain ⟨h1, -, -⟩ := hloc L hL N j hj X B hX hBX c.toObs a b _ ha _ hℓ
    obtain ⟨-, h2, -⟩ := hloc L hL N j hj X B hX hBX c.toObs a b _ hb _ hℓ
    obtain ⟨-, -, h3⟩ := hloc L hL N j hj X B hX hBX c.toObs a b _ hab' _ hℓ
    have hk : nrmj c ℓ₀ a b j (πobs (K X)) ≤ ko := nrmj_le_KnormObs hA hXc
    refine le_trans ?_ (mul_le_mul' (le_refl (ENNReal.ofReal Cb)) hk)
    rw [nrmj_πobs_eq, nrmj_πobs_eq, coe_LocO, LocS_a, LocS_b, LocS_ab, mul_add, mul_add]
    refine add_le_add (add_le_add ?_ ?_) ?_
    · calc _ ≤ (wj d L c ℓ₀ (coal L a b : ℕ∞) j).a *
            (ENNReal.ofReal Cb * Tj d (L : ℝ) j (ellj d L ℓ₀ j) (K X : SA c (Lam d L N)).a) := by
            gcongr
        _ = _ := by ring
    · calc _ ≤ (wj d L c ℓ₀ (coal L a b : ℕ∞) j).b *
            (ENNReal.ofReal Cb * Tj d (L : ℝ) j (ellj d L ℓ₀ j) (K X : SA c (Lam d L N)).b) := by
            gcongr
        _ = _ := by ring
    · calc _ ≤ (wj d L c ℓ₀ (coal L a b : ℕ∞) j).ab *
            (ENNReal.ofReal Cb * Tj d (L : ℝ) j (ellj d L ℓ₀ j) (K X : SA c (Lam d L N)).ab) := by
            gcongr
        _ = _ := by ring
  -- sums over small sets containing a block
  have hsum : ∀ p ∈ blockIdx (L := L) (N := N) j,
      ∀ S ⊆ (smallSets (L := L) (N := N) j).filter (fun X => blockSet j p ⊆ X),
      nrmj c ℓ₀ a b j (∑ X ∈ S, πobs (LocO a b X (blockSet j p) (K X))) ≤
        ENNReal.ofReal ((cs + 1) * Cb) * ko := by
    intro p hp S hS
    refine (nrmj_sum_card_le j S _ _ (fun X hX => key X _ (mem_smallSets.1
      (mem_filter.1 (hS hX)).1) (mem_filter.1 (hS hX)).2) cs
      ((card_le_card hS).trans (hcs L N j p hp))).trans ?_
    rw [← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    gcongr
    nlinarith
  have hQ : ∀ p ∈ blockIdx (L := L) (N := N) j,
      nrmj c ℓ₀ a b j (QobsO a b j K p) ≤ ENNReal.ofReal ((cs + 1) * Cb) * ko := by
    intro p hp
    unfold QobsO QO
    split_ifs
    · rw [map_sum]; exact hsum p hp _ subset_rfl
    · rw [map_zero, nrmj_zero]; exact zero_le
  refine ⟨hQ, fun p hp X => ?_, fun hab => ?_⟩
  · unfold JO
    split_ifs with h1 h2
    · rw [map_neg, nrmj_neg, map_sum]
      exact hsum p hp _ (fun Y hY => mem_filter.2 ⟨(mem_filter.1 hY).1, (mem_filter.1 hY).2.1⟩)
    · have := key X _ h1.2.1 h1.2.2
      refine this.trans (by gcongr; nlinarith)
    · rw [map_zero, nrmj_zero]; exact zero_le
  · have e : ∑ p ∈ blockIdx (L := L) (N := N) j, QobsO a b j K p =
        splitO c (Qcoup c j K a b) a b univ := by
      rw [sum_congr rfl fun p _ => QobsO_eq hab p, sum_splitO_blocks, splitO_univ]
    rw [e]
    refine (nrmj_splitO_polymer_le j _ (isPolymer_univ j)).trans ?_
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, mul_assoc]
    gcongr
    refine iSup₂_le fun p hp => ?_
    rw [← QobsO_eq hab p]
    exact hQ p hp

end QJ

/-! ### The `u` part of observable coupling constants -/

section UPart

variable {c : Case} {Λ : Type*} [DecidableEq Λ]

theorem eps_psibar (x : Λ) : ε (psibar x) = 0 := by simp [psibar, ψ]
theorem eps_psi (x : Λ) : ε (psi x) = 0 := by simp [psi, ψ]

/-- The constant parts of the observable components: `u`-part of `(u + V)^obs`. -/
def uprojS (F : SA c Λ) : SA c Λ :=
  ⟨0, algebraMap ℂ (Grassmann.N Λ) (ε F.a), algebraMap ℂ (Grassmann.N Λ) (ε F.b),
    algebraMap ℂ (Grassmann.N Λ) (ε F.ab)⟩

theorem uprojS_add (F G : SA c Λ) : uprojS (F + G) = uprojS F + uprojS G := by
  ext <;> simp [uprojS]

theorem uprojS_smul (r : ℂ) (F : SA c Λ) : uprojS (r • F) = r • uprojS F := by
  ext <;> simp [uprojS, Algebra.algebraMap_eq_smul_one, smul_smul]

theorem halfA_toU (W : Coup c) (a b : Λ) :
    halfA c (Coup.toU c W) a b = uprojS (halfA c W a b) := by
  cases c <;> ext <;> simp [halfA, Coup.toU, uprojS, eps_psibar, eps_psi, nx]

theorem halfB_toU (W : Coup c) (a b : Λ) :
    halfB c (Coup.toU c W) a b = uprojS (halfB c W a b) := by
  cases c <;> ext <;> simp [halfB, Coup.toU, uprojS, eps_psibar, eps_psi, nx]

/-- `u^obs(X)` is the constant part of `(u + V)^obs(X)`. -/
theorem splitS_toU (W : Coup c) (a b : Λ) (X : Finset Λ) :
    splitS c (Coup.toU c W) a b X = uprojS (splitS c W a b X) := by
  rw [splitS, splitS, uprojS_add, uprojS_smul, uprojS_smul, halfA_toU, halfB_toU]

end UPart

section UNorm

variable {c : Case} {ℓ₀ : ℝ} {a b : Lam d L N}

theorem nrmj_uprojS_le (hℓ₀ : 0 < ℓ₀) (k : ℕ) (F : OE c (Lam d L N)) (G : OE c (Lam d L N))
    (hG : (G : SA c (Lam d L N)) = uprojS (F : SA c (Lam d L N))) :
    nrmj c ℓ₀ a b k G ≤ nrmj c ℓ₀ a b k F := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hh : (0 : ℝ) < (L : ℝ) ^ k := by positivity
  have hℓ := ellj_pos (d := d) hL0 hℓ₀ k
  have hx : ∀ x : Alg d L N, Tj d (L : ℝ) k (ellj d L ℓ₀ k) (algebraMap ℂ (Alg d L N) (ε x)) ≤
      Tj d (L : ℝ) k (ellj d L ℓ₀ k) x := fun x =>
    (tNorm_algebraMap_le hh hℓ _).trans (abs_ε_le hh hℓ x)
  simp only [nrmj, normj, oTj, oNorm, hG, uprojS]
  rw [Tj_zero]
  gcongr
  · exact zero_le
  · exact hx _
  · exact hx _
  · exact hx _

/-- `‖u^obs(X)‖ ≤ ‖(u + V)^obs(X)‖` (in the norm of any scale). -/
theorem nrmj_splitO_toU_le (hℓ₀ : 0 < ℓ₀) (k : ℕ) (W : Coup c) (X : Finset (Lam d L N)) :
    nrmj c ℓ₀ a b k (splitO c (Coup.toU c W) a b X) ≤ nrmj c ℓ₀ a b k (splitO c W a b X) :=
  nrmj_uprojS_le hℓ₀ k _ _ (by rw [coe_splitO, coe_splitO, splitS_toU])

/-- `‖V^obs(X)‖ ≤ 2 ‖(u + V)^obs(X)‖`. -/
theorem nrmj_splitO_toV_le (hℓ₀ : 0 < ℓ₀) (k : ℕ) (W : Coup c) (X : Finset (Lam d L N)) :
    nrmj c ℓ₀ a b k (splitO c (Coup.toV c W) a b X) ≤ 2 * nrmj c ℓ₀ a b k (splitO c W a b X) := by
  have e : splitO c (Coup.toV c W) a b X = splitO c W a b X - splitO c (Coup.toU c W) a b X := by
    rw [← splitO_toU_add_toV c W a b X]; abel
  rw [e, two_mul]
  exact (nrmj_sub_le k _ _).trans (add_le_add le_rfl (nrmj_splitO_toU_le hℓ₀ k W X))

end UNorm

/-! ### Real-valued bookkeeping -/

section Real

variable {c : Case} {ℓ₀ : ℝ} {a b : Lam d L N}

theorem nn_add {k : ℕ} {F G : OE c (Lam d L N)} {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hF : nrmj c ℓ₀ a b k F ≤ ENNReal.ofReal s) (hG : nrmj c ℓ₀ a b k G ≤ ENNReal.ofReal t) :
    nrmj c ℓ₀ a b k (F + G) ≤ ENNReal.ofReal (s + t) :=
  (nrmj_add_le k F G).trans ((add_le_add hF hG).trans_eq (ENNReal.ofReal_add hs ht).symm)

theorem nn_sub {k : ℕ} {F G : OE c (Lam d L N)} {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hF : nrmj c ℓ₀ a b k F ≤ ENNReal.ofReal s) (hG : nrmj c ℓ₀ a b k G ≤ ENNReal.ofReal t) :
    nrmj c ℓ₀ a b k (F - G) ≤ ENNReal.ofReal (s + t) :=
  (nrmj_sub_le k F G).trans ((add_le_add hF hG).trans_eq (ENNReal.ofReal_add hs ht).symm)

theorem nn_half {k : ℕ} {F : OE c (Lam d L N)} {s : ℝ}
    (hF : nrmj c ℓ₀ a b k F ≤ ENNReal.ofReal s) :
    nrmj c ℓ₀ a b k ((1 / 2 : ℂ) • F) ≤ ENNReal.ofReal s :=
  (nrmj_half_smul k F).trans hF

theorem nn_ECO (hd : 3 ≤ d) (hL : (4 : ℝ) ≤ L) (hℓ₀ : 0 < ℓ₀) {j : ℕ}
    {C : Matrix (Lam d L N) (Lam d L N) ℝ} (hC : GoodCov j ℓ₀ C) {F : OE c (Lam d L N)} {s : ℝ}
    (hF : nrmj c ℓ₀ a b j F ≤ ENNReal.ofReal s) :
    nrmj c ℓ₀ a b (j + 1) (ECO C (thetaO F)) ≤
      ENNReal.ofReal ((L : ℝ) ^ (2 * ((d : ℝ) - 2)) * s) := by
  refine (nrmj_ECO_le hd hL hℓ₀ hC F).trans ?_
  rw [ENNReal.ofReal_mul (by positivity)]
  gcongr

theorem nn_ECT (hd : 3 ≤ d) (hL : (4 : ℝ) ≤ L) (hℓ₀ : 0 < ℓ₀) {j : ℕ}
    {C : Matrix (Lam d L N) (Lam d L N) ℝ} (hC : GoodCov j ℓ₀ C) {F G : OE c (Lam d L N)}
    {s t : ℝ} (hs : 0 ≤ s) (hF : nrmj c ℓ₀ a b j F ≤ ENNReal.ofReal s)
    (hG : nrmj c ℓ₀ a b j G ≤ ENNReal.ofReal t) :
    nrmj c ℓ₀ a b (j + 1) (ECT C F G) ≤
      ENNReal.ofReal (2 * ((L : ℝ) ^ (2 * ((d : ℝ) - 2))) ^ 2 * s * t) := by
  refine (nrmj_ECT_le hd hL hℓ₀ hC F G).trans
    (le_of_le_of_eq (mul_le_mul' le_rfl (mul_le_mul' hF hG)) ?_)
  rw [← ENNReal.ofReal_mul hs, ← ENNReal.ofReal_mul (by positivity)]
  congr 1; ring

theorem ECT_sub_sub {Λ : Type*} [DecidableEq Λ] [Fintype Λ] (C : Matrix Λ Λ ℝ)
    (F F' G G' : OE c Λ) :
    ECT C (F - F') (G - G') = ECT C F G - ECT C G' F - ECT C F' (G - G') := by
  rw [ECT_sub_left, ECT_comm C F (G - G'), ECT_sub_left, ECT_comm C G F]

theorem symm_of_goodCov {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℝ} (hC : GoodCov j ℓ₀ C)
    (x y : Lam d L N) : C x y = C y x := by
  have := hC.psd.isHermitian.apply y x
  simpa using this

theorem finite_of_small {K₂ : ℝ} (hK : 1 ≤ K₂) {v k : ENNReal}
    (h : ENNReal.ofReal K₂ * (v + k) ≤ 1) :
    v = ENNReal.ofReal v.toReal ∧ k = ENNReal.ofReal k.toReal ∧ K₂ * (v.toReal + k.toReal) ≤ 1 := by
  have h1 : v + k ≤ 1 := by
    refine le_trans ?_ h
    exact le_mul_of_one_le_left zero_le (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hK)
  have hv : v ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (le_self_add.trans h1)
  have hk : k ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (le_add_self.trans h1)
  refine ⟨(ENNReal.ofReal_toReal hv).symm, (ENNReal.ofReal_toReal hk).symm, ?_⟩
  have := ENNReal.toReal_mono ENNReal.one_ne_top h
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_add hv hk,
    ENNReal.toReal_one] at this

end Real

/-! ### `P^obs`, `e:V+obs-bd`, `e:uobs+`, `e:vobs+` -/

section Next

theorem one_le_K₂ (hd : 3 ≤ d) : (1 : ℝ) ≤ (L : ℝ) ^ (2 * ((d : ℝ) - 2)) := by
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast NeZero.one_le
  refine Real.one_le_rpow hL ?_
  have : (3 : ℝ) ≤ d := by exact_mod_cast hd
  linarith

set_option maxHeartbeats 4000000 in
/-- **The coupling constants** (subsection "Coupling constants" of `sec:tyler-renorm-group`).
Let `K₂ = L^{2(d-2)}`, `v = ‖V^obs_j‖_j`, `k = ‖K^obs_j‖_j`, `V^obs_j(Λ) = evalO (toV Vo) univ`,
and assume `K₂ (v + k) ≤ 1`.  Then, with `C₀` depending only on `d`:
1. `P^obs(B) = ½ 𝔼[θV^obs_j(B); θV^obs_j(Λ)] + O(K₂² k (v + k))` (per block);
2. `P^obs(Λ) = ½ 𝔼[θV^obs_j(Λ); θV^obs_j(Λ)] + O(K₂² k (v + k))`;
3. **`e:V+obs-bd`**: `(u^obs + V^obs)_{j+1}(Λ) = 𝔼 θ V^obs_j(Λ) - ½ 𝔼[θV^obs_j(Λ); θV^obs_j(Λ)] + O(K₂ k)`;
4. `e:V+obs-bd` per block: `(u^obs + V^obs)_{j+1}(B) = 𝔼 θ V^obs_j(B) - ½ 𝔼[θV^obs_j(B); θV^obs_j(Λ)] + O(K₂ k)`;
5. **`e:uobs+`, `e:vobs+`** for every `X ∈ 𝒫_j` (in particular `X = Λ`):
   `‖(u^obs + V^obs)_{j+1}(X)‖, ‖u^obs_{j+1}(X)‖, ‖V^obs_{j+1}(X)‖ ≤ C₀ K₂ (v + k)`.

All norms of the left sides are `‖·‖_{T_{j+1}(ℓ_{j+1})}`.

**Deviation.**  In 5 the text has `O(‖V^obs_j‖_j + L^{2(d-2)} ‖K^obs_j‖_j)`; we prove the bound
with `L^{2(d-2)}` also in front of `‖V^obs_j‖_j`, which is what the general estimate
`‖𝔼 θ F‖_{j+1} ≤ L^{2(d-2)} ‖F‖_j` (`e:Tphi-obs-ub`) gives (the text's sharper bound would use
that `V^obs_j` consists of the marginal monomials only).  This only changes `L`-dependent
constants in front of terms that are at least quadratic. -/
theorem Vobs_next_bounds (hd : 3 ≤ d) : ∃ (C₀ : ℝ) (L₀ : ℕ), 1 ≤ C₀ ∧
    2 ^ (d + 3) + 8 * d + 1 ≤ L₀ ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∀ (N j : ℕ), j < N → ∀ (ℓ₀ : ℝ), 0 < ℓ₀ →
    ∀ (c : Case) (P : Prop) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (Vb : Vcoup) (Vo : Coup c)
      (K : Finset (Lam d L N) → OE c (Lam d L N)) (a b : Lam d L N) (A : ℝ), 1 ≤ A →
      StepObsHyp c P j ℓ₀ C Vb Vo K a b →
      ENNReal.ofReal ((L : ℝ) ^ (2 * ((d : ℝ) - 2))) *
          (VnormObs c ℓ₀ a b j Vo + KnormObs c ℓ₀ a b j A K) ≤ 1 →
      (∀ p ∈ blockIdx (L := L) (N := N) j,
        nrmj c ℓ₀ a b (j + 1) (Pobs C j Vo K a b p -
            (1 / 2 : ℂ) • ECT C (Vobs j Vo a b p) (evalO c (Coup.toV c Vo) a b univ)) ≤
          ENNReal.ofReal (C₀ * ((L : ℝ) ^ (2 * ((d : ℝ) - 2))) ^ 2) *
            (KnormObs c ℓ₀ a b j A K * (VnormObs c ℓ₀ a b j Vo + KnormObs c ℓ₀ a b j A K))) ∧
      nrmj c ℓ₀ a b (j + 1) (∑ p ∈ blockIdx (L := L) (N := N) j, Pobs C j Vo K a b p -
          (1 / 2 : ℂ) • ECT C (evalO c (Coup.toV c Vo) a b univ)
            (evalO c (Coup.toV c Vo) a b univ)) ≤
        ENNReal.ofReal (C₀ * ((L : ℝ) ^ (2 * ((d : ℝ) - 2))) ^ 2) *
          (KnormObs c ℓ₀ a b j A K * (VnormObs c ℓ₀ a b j Vo + KnormObs c ℓ₀ a b j A K)) ∧
      nrmj c ℓ₀ a b (j + 1) (evalO c (nextObs C j Vo K a b) a b univ -
          freeStep C (evalO c (Coup.toV c Vo) a b univ)) ≤
        ENNReal.ofReal (C₀ * (L : ℝ) ^ (2 * ((d : ℝ) - 2))) * KnormObs c ℓ₀ a b j A K ∧
      (∀ p ∈ blockIdx (L := L) (N := N) j,
        nrmj c ℓ₀ a b (j + 1) (splitO c (nextObs C j Vo K a b) a b (blockSet j p) -
            (ECO C (thetaO (Vobs j Vo a b p)) -
              (1 / 2 : ℂ) • ECT C (Vobs j Vo a b p) (evalO c (Coup.toV c Vo) a b univ))) ≤
          ENNReal.ofReal (C₀ * (L : ℝ) ^ (2 * ((d : ℝ) - 2))) * KnormObs c ℓ₀ a b j A K) ∧
      (∀ X : Finset (Lam d L N), IsPolymer j X →
        nrmj c ℓ₀ a b (j + 1) (splitO c (nextObs C j Vo K a b) a b X) ≤
            ENNReal.ofReal (C₀ * (L : ℝ) ^ (2 * ((d : ℝ) - 2))) *
              (VnormObs c ℓ₀ a b j Vo + KnormObs c ℓ₀ a b j A K) ∧
          nrmj c ℓ₀ a b (j + 1) (splitO c (Coup.toU c (nextObs C j Vo K a b)) a b X) ≤
            ENNReal.ofReal (C₀ * (L : ℝ) ^ (2 * ((d : ℝ) - 2))) *
              (VnormObs c ℓ₀ a b j Vo + KnormObs c ℓ₀ a b j A K) ∧
          nrmj c ℓ₀ a b (j + 1) (splitO c (Coup.toV c (nextObs C j Vo K a b)) a b X) ≤
            ENNReal.ofReal (C₀ * (L : ℝ) ^ (2 * ((d : ℝ) - 2))) *
              (VnormObs c ℓ₀ a b j Vo + KnormObs c ℓ₀ a b j A K)) := by
  obtain ⟨Cq, hCq, hQb⟩ := Qobs_bounds d
  refine ⟨20 + 68 * Cq + 32 * Cq ^ 2, 2 ^ (d + 3) + 8 * d + 1, by nlinarith, le_rfl, ?_⟩
  intro L _ hL N j hj ℓ₀ hℓ₀ c P C Vb Vo K a b A hA h hsm
  have hL4 : (4 : ℝ) ≤ L := four_le_of_L₀ hL
  have hC := h.cov
  have hCs := symm_of_goodCov hC a b
  set C₀ : ℝ := 20 + 68 * Cq + 32 * Cq ^ 2 with hC₀
  set C₂ : ℝ := 16 * Cq + 8 * Cq ^ 2 with hC₂
  obtain ⟨hQp, -, hQL⟩ := hQb L (by omega) N j hj ℓ₀ hℓ₀ c P K a b A hA h.loc.hK
  have hQL := hQL h.hab
  set K₂ : ℝ := (L : ℝ) ^ (2 * ((d : ℝ) - 2)) with hK₂
  have hK1 : 1 ≤ K₂ := one_le_K₂ hd
  set v := VnormObs c ℓ₀ a b j Vo with hvdef
  set k := KnormObs c ℓ₀ a b j A K with hkdef
  obtain ⟨hv, hk, hsr⟩ := finite_of_small hK1 hsm
  set vr := v.toReal
  set kr := k.toReal
  have hv0 : 0 ≤ vr := ENNReal.toReal_nonneg
  have hk0 : 0 ≤ kr := ENNReal.toReal_nonneg
  set VL := evalO c (Coup.toV c Vo) a b univ with hVLdef
  set QL := ∑ p ∈ blockIdx (L := L) (N := N) j, QobsO a b j K p with hQLdef
  -- the basic bounds
  have hV : ∀ p ∈ blockIdx (L := L) (N := N) j,
      nrmj c ℓ₀ a b j (Vobs j Vo a b p) ≤ ENNReal.ofReal vr := fun p hp =>
    (nrmj_Vobs_le Vo hp).trans_eq hv
  have hVL : nrmj c ℓ₀ a b j VL ≤ ENNReal.ofReal (2 * vr) := by
    refine (nrmj_VobsL_le Vo).trans (le_of_eq ?_)
    rw [← hvdef, hv, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  have hQ : ∀ p ∈ blockIdx (L := L) (N := N) j,
      nrmj c ℓ₀ a b j (QobsO a b j K p) ≤ ENNReal.ofReal (Cq * kr) := fun p hp =>
    (hQp p hp).trans (le_of_eq (by rw [hk, ← ENNReal.ofReal_mul hCq]))
  have hQL' : nrmj c ℓ₀ a b j QL ≤ ENNReal.ofReal (2 * Cq * kr) :=
    hQL.trans (le_of_eq (by rw [hk, ← ENNReal.ofReal_mul (by positivity)]))
  have eVL : ∑ p ∈ blockIdx (L := L) (N := N) j, Vobs j Vo a b p = VL :=
    sum_splitO_blocks j a b _
  have eVhL : VhatL j Vo K a b = VL - QL := by
    rw [VhatL]; simp only [Vhat]; rw [sum_sub_distrib, eVL]
  have hVhL : nrmj c ℓ₀ a b j (VhatL j Vo K a b) ≤ ENNReal.ofReal (2 * vr + 2 * Cq * kr) := by
    rw [eVhL]; exact nn_sub (by positivity) (by positivity) hVL hQL'
  -- (1) `P^obs(B)`
  have eP1 : ∀ p, Pobs C j Vo K a b p - (1 / 2 : ℂ) • ECT C (Vobs j Vo a b p) VL =
      -((1 / 2 : ℂ) • ECT C QL (Vobs j Vo a b p)) -
        (1 / 2 : ℂ) • ECT C (QobsO a b j K p) (VhatL j Vo K a b) := by
    intro p
    rw [Pobs_eq C j Vo K a b p, Vhat, eVhL, ECT_sub_sub, smul_sub, smul_sub]; abel
  have hB1 : ∀ p ∈ blockIdx (L := L) (N := N) j,
      nrmj c ℓ₀ a b (j + 1) (Pobs C j Vo K a b p - (1 / 2 : ℂ) • ECT C (Vobs j Vo a b p) VL) ≤
        ENNReal.ofReal (C₂ * K₂ ^ 2 * (kr * (vr + kr))) := by
    intro p hp
    rw [eP1]
    have a1 : nrmj c ℓ₀ a b (j + 1) (-((1 / 2 : ℂ) • ECT C QL (Vobs j Vo a b p))) ≤
        ENNReal.ofReal (2 * K₂ ^ 2 * (2 * Cq * kr) * vr) := by
      rw [nrmj_neg]; exact nn_half (nn_ECT hd hL4 hℓ₀ hC (by positivity) hQL' (hV p hp))
    have a2 : nrmj c ℓ₀ a b (j + 1) ((1 / 2 : ℂ) • ECT C (QobsO a b j K p) (VhatL j Vo K a b)) ≤
        ENNReal.ofReal (2 * K₂ ^ 2 * (Cq * kr) * (2 * vr + 2 * Cq * kr)) :=
      nn_half (nn_ECT hd hL4 hℓ₀ hC (by positivity) (hQ p hp) hVhL)
    refine (nn_sub (by positivity) (by positivity) a1 a2).trans (ENNReal.ofReal_le_ofReal ?_)
    have e1 : 8 * Cq * vr + 4 * Cq ^ 2 * kr ≤ C₂ * (vr + kr) := by nlinarith
    calc 2 * K₂ ^ 2 * (2 * Cq * kr) * vr + 2 * K₂ ^ 2 * (Cq * kr) * (2 * vr + 2 * Cq * kr)
        = K₂ ^ 2 * kr * (8 * Cq * vr + 4 * Cq ^ 2 * kr) := by ring
      _ ≤ K₂ ^ 2 * kr * (C₂ * (vr + kr)) := by gcongr
      _ = _ := by ring
  -- (2) `P^obs(Λ)`
  have ePL : ∑ p ∈ blockIdx (L := L) (N := N) j, Pobs C j Vo K a b p =
      (1 / 2 : ℂ) • ECT C (VhatL j Vo K a b) (VhatL j Vo K a b) := by
    rw [sum_congr rfl fun p _ => Pobs_eq C j Vo K a b p, ← smul_sum, ← ECT_sum_left]; rfl
  have eP2 : ∑ p ∈ blockIdx (L := L) (N := N) j, Pobs C j Vo K a b p -
      (1 / 2 : ℂ) • ECT C VL VL =
      -((1 / 2 : ℂ) • ECT C QL VL) - (1 / 2 : ℂ) • ECT C QL (VhatL j Vo K a b) := by
    rw [ePL, eVhL, ECT_sub_sub, smul_sub, smul_sub]; abel
  have hB2 : nrmj c ℓ₀ a b (j + 1) (∑ p ∈ blockIdx (L := L) (N := N) j, Pobs C j Vo K a b p -
      (1 / 2 : ℂ) • ECT C VL VL) ≤ ENNReal.ofReal (C₂ * K₂ ^ 2 * (kr * (vr + kr))) := by
    rw [eP2]
    have a1 : nrmj c ℓ₀ a b (j + 1) (-((1 / 2 : ℂ) • ECT C QL VL)) ≤
        ENNReal.ofReal (2 * K₂ ^ 2 * (2 * Cq * kr) * (2 * vr)) := by
      rw [nrmj_neg]; exact nn_half (nn_ECT hd hL4 hℓ₀ hC (by positivity) hQL' hVL)
    have a2 : nrmj c ℓ₀ a b (j + 1) ((1 / 2 : ℂ) • ECT C QL (VhatL j Vo K a b)) ≤
        ENNReal.ofReal (2 * K₂ ^ 2 * (2 * Cq * kr) * (2 * vr + 2 * Cq * kr)) :=
      nn_half (nn_ECT hd hL4 hℓ₀ hC (by positivity) hQL' hVhL)
    refine (nn_sub (by positivity) (by positivity) a1 a2).trans (ENNReal.ofReal_le_ofReal ?_)
    have e1 : 16 * Cq * vr + 8 * Cq ^ 2 * kr ≤ C₂ * (vr + kr) := by nlinarith
    calc 2 * K₂ ^ 2 * (2 * Cq * kr) * (2 * vr) + 2 * K₂ ^ 2 * (2 * Cq * kr) * (2 * vr + 2 * Cq * kr)
        = K₂ ^ 2 * kr * (16 * Cq * vr + 8 * Cq ^ 2 * kr) := by ring
      _ ≤ K₂ ^ 2 * kr * (C₂ * (vr + kr)) := by gcongr
      _ = _ := by ring
  have hsq : C₂ * K₂ ^ 2 * (kr * (vr + kr)) ≤ C₂ * K₂ * kr := by
    have h1 : K₂ * (vr + kr) ≤ 1 := hsr
    calc C₂ * K₂ ^ 2 * (kr * (vr + kr)) = C₂ * K₂ * kr * (K₂ * (vr + kr)) := by ring
      _ ≤ C₂ * K₂ * kr * 1 := by gcongr
      _ = _ := by ring
  have hK0 : 0 ≤ K₂ := by linarith
  -- (3) `e:V+obs-bd` at `Λ`
  have eN : evalO c (nextObs C j Vo K a b) a b univ = freeStep C (VhatL j Vo K a b) :=
    (sum_RHS_eq C h.hab hCs).symm.trans (sum_RHS C j Vo K a b)
  have e3 : evalO c (nextObs C j Vo K a b) a b univ - freeStep C VL =
      -ECO C (thetaO QL) - (∑ p ∈ blockIdx (L := L) (N := N) j, Pobs C j Vo K a b p -
        (1 / 2 : ℂ) • ECT C VL VL) := by
    rw [eN, ePL, freeStep, freeStep, eVhL, map_sub, map_sub]; abel
  have hB3 : nrmj c ℓ₀ a b (j + 1) (evalO c (nextObs C j Vo K a b) a b univ - freeStep C VL) ≤
      ENNReal.ofReal (C₀ * K₂ * kr) := by
    rw [e3]
    have a1 : nrmj c ℓ₀ a b (j + 1) (-ECO C (thetaO QL)) ≤ ENNReal.ofReal (K₂ * (2 * Cq * kr)) := by
      rw [nrmj_neg]; exact nn_ECO (F := QL) (s := 2 * Cq * kr) hd hL4 hℓ₀ hC hQL'
    refine (nn_sub (by positivity) (by positivity) a1 hB2).trans (ENNReal.ofReal_le_ofReal ?_)
    nlinarith [mul_nonneg hK0 hk0]
  -- (4) per block
  have e4 : ∀ p, splitO c (nextObs C j Vo K a b) a b (blockSet j p) -
      (ECO C (thetaO (Vobs j Vo a b p)) - (1 / 2 : ℂ) • ECT C (Vobs j Vo a b p) VL) =
      -ECO C (thetaO (QobsO a b j K p)) -
        (Pobs C j Vo K a b p - (1 / 2 : ℂ) • ECT C (Vobs j Vo a b p) VL) := by
    intro p
    rw [← RHS_eq C h.hab hCs p, RHS, Vhat, map_sub, map_sub]; abel
  have hB4 : ∀ p ∈ blockIdx (L := L) (N := N) j,
      nrmj c ℓ₀ a b (j + 1) (splitO c (nextObs C j Vo K a b) a b (blockSet j p) -
        (ECO C (thetaO (Vobs j Vo a b p)) - (1 / 2 : ℂ) • ECT C (Vobs j Vo a b p) VL)) ≤
      ENNReal.ofReal ((17 * Cq + 8 * Cq ^ 2) * K₂ * kr) := by
    intro p hp
    rw [e4]
    have a1 : nrmj c ℓ₀ a b (j + 1) (-ECO C (thetaO (QobsO a b j K p))) ≤
        ENNReal.ofReal (K₂ * (Cq * kr)) := by
      rw [nrmj_neg]; exact nn_ECO hd hL4 hℓ₀ hC (hQ p hp)
    refine (nn_sub (by positivity) (by positivity) a1 (hB1 p hp)).trans
      (ENNReal.ofReal_le_ofReal ?_)
    nlinarith [mul_nonneg hK0 hk0]
  -- (5) `e:uobs+`, `e:vobs+`
  set C₁ : ℝ := 5 + 17 * Cq + 8 * Cq ^ 2 with hC₁
  have hB5 : ∀ p ∈ blockIdx (L := L) (N := N) j,
      nrmj c ℓ₀ a b (j + 1) (splitO c (nextObs C j Vo K a b) a b (blockSet j p)) ≤
        ENNReal.ofReal (C₁ * K₂ * (vr + kr)) := by
    intro p hp
    have hlead : nrmj c ℓ₀ a b (j + 1) (ECO C (thetaO (Vobs j Vo a b p)) -
        (1 / 2 : ℂ) • ECT C (Vobs j Vo a b p) VL) ≤
        ENNReal.ofReal (K₂ * vr + 2 * K₂ ^ 2 * vr * (2 * vr)) :=
      nn_sub (by positivity) (by positivity) (nn_ECO hd hL4 hℓ₀ hC (hV p hp))
        (nn_half (nn_ECT hd hL4 hℓ₀ hC hv0 (hV p hp) hVL))
    have e : splitO c (nextObs C j Vo K a b) a b (blockSet j p) =
        (splitO c (nextObs C j Vo K a b) a b (blockSet j p) -
          (ECO C (thetaO (Vobs j Vo a b p)) - (1 / 2 : ℂ) • ECT C (Vobs j Vo a b p) VL)) +
        (ECO C (thetaO (Vobs j Vo a b p)) - (1 / 2 : ℂ) • ECT C (Vobs j Vo a b p) VL) := by abel
    rw [e]
    refine (nn_add (by positivity) (by positivity) (hB4 p hp) hlead).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have h1 : K₂ * vr ≤ 1 := by nlinarith
    have h2 : 2 * K₂ ^ 2 * vr * (2 * vr) ≤ 4 * (K₂ * vr) := by nlinarith [mul_nonneg hK0 hv0]
    nlinarith [mul_nonneg hK0 hk0, mul_nonneg hK0 hv0]
  have hB5X : ∀ X : Finset (Lam d L N), IsPolymer j X →
      nrmj c ℓ₀ a b (j + 1) (splitO c (nextObs C j Vo K a b) a b X) ≤
        ENNReal.ofReal (2 * C₁ * K₂ * (vr + kr)) := by
    intro X hX
    refine (nrmj_splitO_polymer_le (j + 1) _ hX).trans ?_
    rw [show 2 * C₁ * K₂ * (vr + kr) = 2 * (C₁ * K₂ * (vr + kr)) by ring,
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    gcongr
    exact iSup₂_le hB5
  -- conversions
  have cv1 : ∀ α : ℝ, 0 ≤ α → ENNReal.ofReal α * (k * (v + k)) =
      ENNReal.ofReal (α * (kr * (vr + kr))) := by
    intro α hα
    rw [hk, hv, ← ENNReal.ofReal_add hv0 hk0, ← ENNReal.ofReal_mul hk0, ← ENNReal.ofReal_mul hα]
  have cv2 : ∀ α : ℝ, 0 ≤ α → ENNReal.ofReal α * k = ENNReal.ofReal (α * kr) := by
    intro α hα
    rw [hk, ← ENNReal.ofReal_mul hα]
  have cv3 : ∀ α : ℝ, 0 ≤ α → ENNReal.ofReal α * (v + k) = ENNReal.ofReal (α * (vr + kr)) := by
    intro α hα
    rw [hk, hv, ← ENNReal.ofReal_add hv0 hk0, ← ENNReal.ofReal_mul hα]
  have hC₂₀ : C₂ ≤ C₀ := by nlinarith
  refine ⟨fun p hp => ?_, ?_, ?_, fun p hp => ?_, fun X hX => ⟨?_, ?_, ?_⟩⟩
  · rw [cv1 _ (by positivity)]
    exact (hB1 p hp).trans (ENNReal.ofReal_le_ofReal (by gcongr))
  · rw [cv1 _ (by positivity)]
    exact hB2.trans (ENNReal.ofReal_le_ofReal (by gcongr))
  · rw [cv2 _ (by positivity)]
    exact hB3.trans (ENNReal.ofReal_le_ofReal (by gcongr))
  · rw [cv2 _ (by positivity)]
    exact (hB4 p hp).trans (ENNReal.ofReal_le_ofReal (by gcongr; nlinarith))
  · rw [cv3 _ (by positivity)]
    exact (hB5X X hX).trans (ENNReal.ofReal_le_ofReal (by nlinarith [mul_nonneg hK0 (add_nonneg hv0 hk0)]))
  · rw [cv3 _ (by positivity)]
    exact (nrmj_splitO_toU_le hℓ₀ _ _ X).trans
      ((hB5X X hX).trans (ENNReal.ofReal_le_ofReal (by nlinarith [mul_nonneg hK0 (add_nonneg hv0 hk0)])))
  · rw [cv3 _ (by positivity)]
    refine (nrmj_splitO_toV_le hℓ₀ _ _ X).trans ?_
    rw [show C₀ * K₂ * (vr + kr) = 2 * (C₀ / 2 * K₂ * (vr + kr)) by ring,
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    gcongr
    exact (hB5X X hX).trans (ENNReal.ofReal_le_ofReal (by nlinarith [mul_nonneg hK0 (add_nonneg hv0 hk0)]))

end Next


/-! ### Preservation of `InKpt` (the source fields of `K_{j+1}(U)` lie in `U`) -/

section Pt

variable {c : Case}

theorem thetaO_mem_ptSub {Λ : Type*} [DecidableEq Λ] {pa pb : Prop} {F : OE c Λ}
    (hF : F ∈ (ptSub pa pb : Subalgebra ℂ (OE c Λ))) :
    thetaO F ∈ (ptSub pa pb : Subalgebra ℂ (OE c (Λ ⊕ Λ))) := by
  obtain ⟨h1, h2, h3⟩ := hF
  refine ⟨fun h => ?_, fun h => ?_, fun ha hb => ?_⟩ <;>
    simp only [coe_thetaO, thetaS_a, thetaS_b, thetaS_ab]
  · rw [h1 h, map_zero]
  · rw [h2 h, map_zero]
  · rw [h3 ha hb, map_zero]

theorem inclO_mem_ptSub {Λ : Type*} [DecidableEq Λ] {pa pb : Prop} {F : OE c Λ}
    (hF : F ∈ (ptSub pa pb : Subalgebra ℂ (OE c Λ))) :
    inclO F ∈ (ptSub pa pb : Subalgebra ℂ (OE c (Λ ⊕ Λ))) := by
  obtain ⟨h1, h2, h3⟩ := hF
  refine ⟨fun h => ?_, fun h => ?_, fun ha hb => ?_⟩ <;>
    simp only [coe_inclO, inclS_a, inclS_b, inclS_ab]
  · rw [h1 h, map_zero]
  · rw [h2 h, map_zero]
  · rw [h3 ha hb, map_zero]

theorem ECO_mem_ptSub {Λ : Type*} [DecidableEq Λ] [Fintype Λ] (C : Matrix Λ Λ ℝ) {pa pb : Prop}
    {F : OE c (Λ ⊕ Λ)} (hF : F ∈ (ptSub pa pb : Subalgebra ℂ (OE c (Λ ⊕ Λ)))) :
    ECO C F ∈ (ptSub pa pb : Subalgebra ℂ (OE c Λ)) := by
  obtain ⟨h1, h2, h3⟩ := hF
  refine ⟨fun h => ?_, fun h => ?_, fun ha hb => ?_⟩ <;>
    simp only [coe_ECO, ECS_a, ECS_b, ECS_ab]
  · rw [h1 h, map_zero]
  · rw [h2 h, map_zero]
  · rw [h3 ha hb, map_zero]

theorem emb_mem_ptSub {Λ : Type*} {pa pb : Prop} (x : EvR Λ) :
    (emb x : OE c Λ) ∈ (ptSub pa pb : Subalgebra ℂ (OE c Λ)) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem splitO_mem_ptSub {Λ : Type*} [DecidableEq Λ] (W : Coup c) (a b : Λ) (B : Finset Λ) :
    splitO c W a b B ∈ (ptSub (a ∈ B) (b ∈ B) : Subalgebra ℂ (OE c Λ)) := by
  refine ⟨fun h => ?_, fun h => ?_, fun ha hb => ?_⟩ <;>
    simp only [coe_splitO, splitS, SA.add_a, SA.add_b, SA.add_ab, SA.smul_a, SA.smul_b,
      SA.smul_ab]
  · rw [ind_neg h, zero_smul, zero_add]; cases c <;> simp [halfB]
  · rw [ind_neg h, zero_smul, add_zero]; cases c <;> simp [halfA]
  · rw [ind_neg ha, ind_neg hb, zero_smul, zero_smul, add_zero]

theorem LocO_mem_ptSub {a b : Lam d L N} (hab : a ≠ b) {X B : Finset (Lam d L N)} (hBX : B ⊆ X)
    (F : OE c (Lam d L N)) :
    LocO a b X B F ∈ (ptSub (a ∈ B) (b ∈ B) : Subalgebra ℂ (OE c (Lam d L N))) := by
  refine ⟨fun h => ?_, fun h => ?_, fun ha hb => ?_⟩ <;>
    simp only [coe_LocO, LocS_a, LocS_b, LocS_ab]
  · cases c
    · show locOdd (-1) {a} X B _ = 0
      rw [locOdd_single _ _ hBX, ind_neg h, zero_smul]
    · show locEven {a} X B _ = 0
      rw [locEven_single _ hBX, ind_neg h, zero_smul]
  · cases c
    · show locOdd 1 {b} X B _ = 0
      rw [locOdd_single _ _ hBX, ind_neg h, zero_smul]
    · show locEven {b} X B _ = 0
      rw [locEven_single _ hBX, ind_neg h, zero_smul]
  · rw [locAB_eq_ind hab, ind_neg ha, ind_neg hb, zero_smul, zero_smul, add_zero]

theorem JO_mem_ptSub {a b : Lam d L N} (hab : a ≠ b) (j : ℕ)
    (K : Finset (Lam d L N) → OE c (Lam d L N)) (p : Fin d → ℕ) (Y : Finset (Lam d L N)) :
    JO a b j K p Y ∈
      (ptSub (a ∈ blockSet j p) (b ∈ blockSet j p) : Subalgebra ℂ (OE c (Lam d L N))) := by
  classical
  unfold JO
  split_ifs with h1 h2
  · exact neg_mem (Subalgebra.sum_mem _ fun Y' hY' => LocO_mem_ptSub hab (mem_filter.1 hY').2.1 _)
  · exact LocO_mem_ptSub hab h1.2.2 _
  · exact zero_mem _

/-- **Preservation of `InKpt`**: if the source fields of `K_j(X)` lie in `X`, then those of
`K_{j+1}(U)` lie in `U` (for every `(j+1)`-polymer `U`).  No other hypotheses are needed. -/
theorem KnextO_mem_ptSub {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℝ} {Vb : Vcoup}
    {Vo : Coup c} {K : Finset (Lam d L N) → OE c (Lam d L N)} {a b : Lam d L N} (hab : a ≠ b)
    (hK : InKpt c a b j K) {U : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U) :
    KnextO j C Vb Vo K a b U ∈ (ptSub (a ∈ U) (b ∈ U) : Subalgebra ℂ (OE c (Lam d L N))) := by
  have mono : ∀ {B U : Finset (Lam d L N)} {F : OE c (Lam d L N)}, B ⊆ U →
      F ∈ (ptSub (a ∈ B) (b ∈ B) : Subalgebra ℂ (OE c (Lam d L N))) →
      F ∈ (ptSub (a ∈ U) (b ∈ U) : Subalgebra ℂ (OE c (Lam d L N))) :=
    fun hBU hF => ptSub_mono (fun h => hBU h) (fun h => hBU h) hF
  have hV : ∀ (V : Vcoup) (W : Coup c) {U : Finset (Lam d L N)} (p : Fin d → ℕ),
      blockSet j p ⊆ U → oexp (-VfullX V W a b (blockSet j p)) ∈
        (ptSub (a ∈ U) (b ∈ U) : Subalgebra ℂ (OE c (Lam d L N))) := fun V W U p hp =>
    oexp_mem _ (neg_mem (add_mem (emb_mem_ptSub _)
      (mono hp (splitO_mem_ptSub _ a b _)))) (isNilpotent_VfullX a b _ _ _).neg
  have hS : SuppHyp (obsA c C) j (obsI j C Vb Vo K a b)
      (fun U => (ptSub (a ∈ U) (b ∈ U) : Subalgebra ℂ (OE c (Lam d L N))))
      (fun U => (ptSub (a ∈ U) (b ∈ U) : Subalgebra ℂ (OE c (Lam d L N ⊕ Lam d L N)))) :=
    { hθ := fun _ _ hF => thetaO_mem_ptSub hF
      hι := fun _ _ hF => inclO_mem_ptSub hF
      hK := fun _ Y hY hYU => mono hYU (hK Y hY)
      hJ := fun _ p Y hb hYU => mono (hb.trans hYU) (JO_mem_ptSub hab j K p Y)
      hI0 := fun _ p hb => hV _ _ p hb
      heV := fun _ p hb => hV _ _ p hb
      heum := fun _ p hb => mul_mem (Subalgebra.algebraMap_mem _ _)
        (oexp_mem _ (neg_mem (mono hb (splitO_mem_ptSub _ a b _)))
          (isNilpotent_of_obs (bulk_uObsX j C Vo K a b _)).neg) }
  exact hS.KnextG_mem hU (fun _ hf => ECO_mem_ptSub C hf) fun p hb =>
    mul_mem (Subalgebra.algebraMap_mem _ _)
      (oexp_mem _ (mono hb (splitO_mem_ptSub _ a b _))
        (isNilpotent_of_obs (bulk_uObsX j C Vo K a b _)))

theorem InKpt_KnextO {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℝ} {Vb : Vcoup}
    {Vo : Coup c} {K : Finset (Lam d L N) → OE c (Lam d L N)} {a b : Lam d L N} (hab : a ≠ b)
    (hK : InKpt c a b j K) : InKpt c a b (j + 1) (KnextO j C Vb Vo K a b) :=
  fun _ hU => KnextO_mem_ptSub hab hK hU.1

end Pt


/-! ### `e:expVobs2-expansion` -/

section Expansion

variable {c : Case} {X : Type*} [DecidableEq X] [Fintype X] {E : Type*} [Fintype E]
  [DecidableEq E] [AddAction (E → ℕ) X] {p : ℕ} {h ℓ : ℝ} {w : Wt}

theorem πobs_of_bulk' {F : OE c X} (hF : bulk F = 0) : πobs F = F := by
  have h := eq_emb_add_πobs F
  rw [hF, map_zero, zero_add] at h
  exact h.symm

set_option maxHeartbeats 2000000 in
/-- **`e:expVobs2-expansion`** (in any norm `T(h, ℓ)` with weights satisfying the product
property): for a bulk part `x` (`ε(x) = 0`), an observable part `G` and a constant `z`
(the bulk `u`),
`‖π_obs (e^{z} e^{-(x + G)}) - (-G + ½ G²)‖ ≤ (e^{|z| + r} - 1)(s + s²/2)`
if `‖x‖ ≤ r`, `‖G‖ ≤ s`.  In particular (`z = 0`) `π_obs e^{-V(B)} = -V^obs(B) + ½ V^obs(B)²
+ O(‖V^∅(B)‖ ‖V^obs(B)‖)` for `‖V^∅(B)‖, ‖V^obs(B)‖ ≤ 1`.  Exact identity:
`π_obs (e^z e^{-(x+G)}) - (-G + ½G²) = (e^z e^{-x} - 1)(-G + ½G²)` (`G³ = 0`). -/
theorem πobs_oexp_expansion_le (hh : 0 < h) (hℓ : 0 < ℓ) (hw : w.Sub) (z : ℂ)
    {x : EvR X} (hx : ε (x : Grassmann.N X) = 0) {G : OE c X} (hG : bulk G = 0) {r s : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hxr : tNorm E p h ℓ (x : Grassmann.N X) ≤ ENNReal.ofReal r)
    (hGs : oT E p h ℓ w (G : SA c X) ≤ ENNReal.ofReal s) :
    oT E p h ℓ w ((πobs (algebraMap ℂ (OE c X) (Complex.exp z) * oexp (-(emb x + G))) -
        (-G + (1 / 2 : ℂ) • G ^ 2) : OE c X) : SA c X) ≤
      ENNReal.ofReal ((Real.exp (‖z‖ + r) - 1) * (s + s ^ 2 / 2)) := by
  set H : OE c X := -G + (1 / 2 : ℂ) • G ^ 2 with hHdef
  have hGe : (G : SA c X).e = 0 := by rw [← coe_bulk, hG]; rfl
  have hF : ε ((-(emb x + G) : OE c X) : SA c X).e = 0 := by
    rw [← coe_bulk, map_neg, map_add, bulk_emb, hG, add_zero]
    simp [hx]
  have hbF : bulk (-(emb x + G)) = -x := by rw [map_neg, map_add, bulk_emb, hG, add_zero]
  have hpF : πobs (-(emb x + G)) = -G := by
    rw [map_neg, map_add, πobs_emb, zero_add, πobs_of_bulk' hG]
  have hbH : bulk H = 0 := by
    rw [hHdef, map_add, map_neg, hG, map_smul, map_pow, hG]; simp
  have e1 : oexp (-(emb x + G)) = emb (gexp (-x)) * (1 + H) := by
    rw [oexp_eq_mul hF, hbF, hpF, hHdef, neg_sq, add_assoc]
  set Y : EvR X := algebraMap ℂ (EvR X) (Complex.exp z) * gexp (-x) with hY
  have e2 : algebraMap ℂ (OE c X) (Complex.exp z) * oexp (-(emb x + G)) = emb Y * (1 + H) := by
    rw [e1, ← mul_assoc, hY, map_mul, AlgHom.commutes]
  have e3 : πobs (algebraMap ℂ (OE c X) (Complex.exp z) * oexp (-(emb x + G))) - H =
      emb (Y - 1) * H := by
    rw [e2, mul_add, mul_one, map_add, πobs_emb, zero_add, πobs_emb_mul hbH, map_sub, map_one,
      sub_mul, one_mul]
  rw [e3]
  have hx' : ε ((-x : EvR X) : Grassmann.N X) = 0 := by simp [hx]
  have hxr' : tNorm E p h ℓ ((-x : EvR X) : Grassmann.N X) ≤ ENNReal.ofReal r := by
    rw [NegMemClass.coe_neg, Loc.tNorm_neg]; exact hxr
  -- the bulk factor
  have hYn : tNorm E p h ℓ (((Y - 1 : EvR X)) : Grassmann.N X) ≤
      ENNReal.ofReal (Real.exp (‖z‖ + r) - 1) := by
    have eY : ((Y - 1 : EvR X) : Grassmann.N X) =
        Complex.exp z • ((gexp (-x) - 1 : EvR X) : Grassmann.N X) +
          (Complex.exp z - 1) • (1 : Grassmann.N X) := by
      rw [hY, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
      simp only [AddSubgroupClass.coe_sub, SetLike.val_smul, OneMemClass.coe_one, smul_sub,
        sub_smul, one_smul]
      abel
    rw [eY]
    have h1 := tn_smul (Complex.exp z) (tNorm_gexp_sub_one_le hh hℓ hx' hr hxr')
    have h2 := tn_smul (Complex.exp z - 1) (tn_one (E := E) (p := p) (X := X) hh hℓ)
    have hr1 : 0 ≤ Real.exp r - 1 := by linarith [Real.add_one_le_exp r]
    refine (tn_add (mul_nonneg (norm_nonneg _) hr1) (by positivity) h1 h2).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have hz1 : ‖Complex.exp z‖ ≤ Real.exp ‖z‖ := Complex.norm_exp_le_exp_norm z
    have hz2 : ‖Complex.exp z - 1‖ ≤ Real.exp ‖z‖ - 1 := by
      simpa using Complex.norm_exp_sub_sum_le_exp_norm_sub_sum z 1
    rw [Real.exp_add]
    nlinarith [norm_nonneg (Complex.exp z)]
  -- the observable factor
  have hHn : oT E p h ℓ w (H : SA c X) ≤ ENNReal.ofReal (s + s ^ 2 / 2) := by
    rw [hHdef]
    refine (oT_add_le _ _).trans ?_
    rw [show (((1 / 2 : ℂ) • G ^ 2 : OE c X) : SA c X) = (1 / 2 : ℂ) • ((G ^ 2 : OE c X) : SA c X)
      from rfl, oT_smul, NegMemClass.coe_neg, oT_neg,
      ENNReal.ofReal_add hs (by positivity)]
    gcongr
    have h2 := (oT_pow_le hh hℓ hw G 2).trans (pow_le_pow_left' hGs 2)
    rw [← ENNReal.ofReal_pow hs] at h2
    calc ENNReal.ofReal ‖(1 / 2 : ℂ)‖ * oT E p h ℓ w ((G ^ 2 : OE c X) : SA c X)
        ≤ ENNReal.ofReal (1 / 2) * ENNReal.ofReal (s ^ 2) := by
          gcongr; norm_num
      _ = ENNReal.ofReal (s ^ 2 / 2) := by
          rw [← ENNReal.ofReal_mul (by norm_num)]; congr 1; ring
  calc oT E p h ℓ w ((emb (Y - 1) * H : OE c X) : SA c X)
      ≤ oT E p h ℓ w ((emb (Y - 1) : OE c X) : SA c X) * oT E p h ℓ w (H : SA c X) :=
        oT_mul_le hh hℓ hw _ _
    _ ≤ ENNReal.ofReal (Real.exp (‖z‖ + r) - 1) * ENNReal.ofReal (s + s ^ 2 / 2) := by
        rw [coe_emb, oT_ofN]; gcongr
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by linarith [Real.add_one_le_exp (‖z‖ + r), norm_nonneg z])]

end Expansion


/-! ### `E:vj` with observables and Lemma `lem:pert12` for the full prefactors -/

section Vj

set_option maxHeartbeats 4000000 in
/-- **`E:vj` with observables**, in real form (the analogue of `Step.block_real`).  With
`vb = ‖V^∅‖_j`, `kb = ‖K^∅‖_j`, `vo = ‖V^obs‖_j`, `ko = ‖K^obs‖_j` (real versions `vbr`, …),
`K₂ = L^{2(d-2)}`, `a = vbr + C₀ kbr` and `s = C₀ K₂ (vor + kor)`, for every `B ∈ 𝓑_j`:
* `|u^∅_{j+1}| |B| ≤ a`;
* `‖V_{j+1}(B)‖_{T_{j+1}(ℓ_{j+1})} ≤ 2a + s` (bulk and observable part, `V^obs_{j+1} = toV nextObs`);
* `‖u^obs_{j+1}(B)‖_{T_{j+1}(ℓ_{j+1})} ≤ s`;
* `‖V_j(B)‖_{T_{j+1}(2ℓ_{j+1})}, ‖V_j(B)‖_{T_{j+1}(ℓ_{j+1})} ≤ vbr + K₂ vor` (weights of scale `j + 1`).
Assumes `‖V^∅‖_j + ‖K^∅‖_j ≤ ε` (any `ε ≥ 0`) and `K₂ (‖V^obs‖_j + ‖K^obs‖_j) ≤ 1`. -/
theorem obs_block_real (hd : 3 ≤ d) : ∃ (C₀ : ℝ) (L₀ : ℕ), 1 ≤ C₀ ∧
    2 ^ (d + 3) + 8 * d + 1 ≤ L₀ ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∀ (N j : ℕ), j < N → ∀ (ℓ₀ : ℝ), 0 < ℓ₀ →
    ∀ (c : Case) (P : Prop) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (Vb : Vcoup) (Vo : Coup c)
      (K : Finset (Lam d L N) → OE c (Lam d L N)) (a b : Lam d L N) (A : ℝ), 1 ≤ A →
      StepObsHyp c P j ℓ₀ C Vb Vo K a b → ∀ ε : ℝ, 0 ≤ ε →
      Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) Vb +
          Knorm j (ellj d L ℓ₀ j) A (bulkK K) ≤ ENNReal.ofReal ε →
      ENNReal.ofReal ((L : ℝ) ^ (2 * ((d : ℝ) - 2))) *
          (VnormObs c ℓ₀ a b j Vo + KnormObs c ℓ₀ a b j A K) ≤ 1 →
      let vbr := (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) Vb).toReal
      let kbr := (Knorm j (ellj d L ℓ₀ j) A (bulkK K)).toReal
      let vor := (VnormObs c ℓ₀ a b j Vo).toReal
      let kor := (KnormObs c ℓ₀ a b j A K).toReal
      let K₂ := (L : ℝ) ^ (2 * ((d : ℝ) - 2))
      Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) Vb = ENNReal.ofReal vbr ∧
      Knorm j (ellj d L ℓ₀ j) A (bulkK K) = ENNReal.ofReal kbr ∧
      VnormObs c ℓ₀ a b j Vo = ENNReal.ofReal vor ∧ KnormObs c ℓ₀ a b j A K = ENNReal.ofReal kor ∧
      0 ≤ vbr ∧ 0 ≤ kbr ∧ 0 ≤ vor ∧ 0 ≤ kor ∧ vbr + kbr ≤ ε ∧ K₂ * (vor + kor) ≤ 1 ∧
      ∀ p ∈ blockIdx (L := L) (N := N) j,
        ‖(uVb j C Vb K).1 * (blockSet (L := L) (N := N) j p).card‖ ≤ vbr + C₀ * kbr ∧
        nrmj c ℓ₀ a b (j + 1)
            (VfullX (uVb j C Vb K).2 (nextObs C j Vo K a b) a b (blockSet j p)) ≤
          ENNReal.ofReal (2 * (vbr + C₀ * kbr) + C₀ * K₂ * (vor + kor)) ∧
        nrmj c ℓ₀ a b (j + 1) (uObsX j C Vo K a b (blockSet j p)) ≤
          ENNReal.ofReal (C₀ * K₂ * (vor + kor)) ∧
        oTj d L (wj d L c ℓ₀ (coal L a b : ℕ∞) (j + 1)) (j + 1) (2 * ellj d L ℓ₀ (j + 1))
            (VfullX Vb Vo a b (blockSet j p) : SA c (Lam d L N)) ≤
          ENNReal.ofReal (vbr + K₂ * vor) ∧
        nrmj c ℓ₀ a b (j + 1) (VfullX Vb Vo a b (blockSet j p)) ≤
          ENNReal.ofReal (vbr + K₂ * vor) := by
  obtain ⟨CU, LU, hCU, hLU, hbr⟩ := block_real hd
  obtain ⟨CV, LV, hCV, hLV, hVn⟩ := Vobs_next_bounds hd
  refine ⟨CU + CV + 1, max LU LV, by linarith, hLU.trans (le_max_left _ _), ?_⟩
  intro L _ hL N j hj ℓ₀ hℓ₀ c P C Vb Vo K a b A hA h ε hε hvkb hsm vbr kbr vor kor K₂
  have hL4 : (4 : ℝ) ≤ L := four_le_of_L₀ (hLU.trans ((le_max_left _ _).trans hL))
  have hL0 : (0 : ℝ) < L := by linarith
  have hK1 : 1 ≤ K₂ := one_le_K₂ hd
  obtain ⟨hvb, hkb, hvb0, hkb0, hvkr, hblk⟩ :=
    hbr L ((le_max_left _ _).trans hL) N j hj ℓ₀ hℓ₀ C h.cov Vb (bulkK K) A hA h.bulk ε hε hvkb
  obtain ⟨hvo, hko, hsr⟩ := finite_of_small hK1 hsm
  have hvo0 : 0 ≤ vor := ENNReal.toReal_nonneg
  have hko0 : 0 ≤ kor := ENNReal.toReal_nonneg
  obtain ⟨-, -, -, -, h5⟩ := hVn L ((le_max_right _ _).trans hL) N j hj ℓ₀ hℓ₀ c P C Vb Vo K a b A hA h hsm
  have cv : ∀ α : ℝ, 0 ≤ α → ENNReal.ofReal α *
      (VnormObs c ℓ₀ a b j Vo + KnormObs c ℓ₀ a b j A K) = ENNReal.ofReal (α * (vor + kor)) := by
    intro α hα
    rw [hvo, hko, ← ENNReal.ofReal_add hvo0 hko0, ← ENNReal.ofReal_mul hα]
  have hK0 : 0 ≤ K₂ := by linarith
  have hsCV : CV * K₂ * (vor + kor) ≤ (CU + CV + 1) * K₂ * (vor + kor) := by
    gcongr; linarith
  refine ⟨hvb, hkb, hvo, hko, hvb0, hkb0, hvo0, hko0, hvkr, hsr, fun p hp => ?_⟩
  obtain ⟨hVB, hu, hV'⟩ := hblk p hp
  obtain ⟨-, hU5, hV5⟩ := h5 _ (isPolymer_blockSet j p)
  rw [cv _ (by positivity)] at hU5 hV5
  have hCU' : CU * kbr ≤ (CU + CV + 1) * kbr := by gcongr; linarith
  refine ⟨hu.trans (by linarith), ?_, ?_, ?_, ?_⟩
  · rw [VfullX]
    refine (nn_add (s := 2 * (vbr + CU * kbr)) (t := CV * K₂ * (vor + kor)) (by positivity)
      (by positivity) ?_ hV5).trans (ENNReal.ofReal_le_ofReal (by linarith))
    rw [nrmj_emb, coe_VE]; exact hV'
  · exact hU5.trans (ENNReal.ofReal_le_ofReal hsCV)
  · have hw := (normj_succ_le hd hL4 c hℓ₀ (coal L a b : ℕ∞) j
      (splitO c (Coup.toV c Vo) a b (blockSet j p) : SA c (Lam d L N))).2
    have hb2 : Tj d (L : ℝ) (j + 1) (2 * ellj d L ℓ₀ (j + 1)) (Vb.eval (blockSet j p)) ≤
        ENNReal.ofReal vbr := (Tj_succ_le hd hL4 hℓ₀ j _).2.trans hVB
    have ho2 : oTj d L (wj d L c ℓ₀ (coal L a b : ℕ∞) (j + 1)) (j + 1) (2 * ellj d L ℓ₀ (j + 1))
        (splitO c (Coup.toV c Vo) a b (blockSet j p) : SA c (Lam d L N)) ≤
        ENNReal.ofReal (K₂ * vor) := by
      refine hw.trans ?_
      rw [ENNReal.ofReal_mul hK0, ← hvo]
      gcongr
      exact nrmj_Vobs_le Vo hp
    rw [VfullX]
    refine (oT_add_le (E := Dir d) (p := pPhi d) (h := (L : ℝ) ^ (j + 1))
      (ℓ := 2 * ellj d L ℓ₀ (j + 1)) _ _).trans ?_
    rw [ENNReal.ofReal_add hvb0 (by positivity)]
    refine add_le_add ?_ ho2
    rw [coe_emb, oT_ofN, coe_VE]; exact hb2
  · have hw := (normj_succ_le hd hL4 c hℓ₀ (coal L a b : ℕ∞) j
      (splitO c (Coup.toV c Vo) a b (blockSet j p) : SA c (Lam d L N)))
    have hb2 : Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1)) (Vb.eval (blockSet j p)) ≤
        ENNReal.ofReal vbr :=
      (Tj_succ_le hd hL4 hℓ₀ j _).1.trans ((Tj_succ_le hd hL4 hℓ₀ j _).2.trans hVB)
    have ho2 : nrmj c ℓ₀ a b (j + 1) (splitO c (Coup.toV c Vo) a b (blockSet j p)) ≤
        ENNReal.ofReal (K₂ * vor) := by
      refine hw.1.trans (hw.2.trans ?_)
      rw [ENNReal.ofReal_mul hK0, ← hvo]
      gcongr
      exact nrmj_Vobs_le Vo hp
    rw [VfullX]
    refine (nn_add hvb0 (by positivity) ?_ ho2)
    rw [nrmj_emb, coe_VE]; exact hb2

end Vj


section Pert

set_option maxHeartbeats 4000000 in
/-- **Lemma `lem:pert12` for the full prefactors**: for `X ∈ 𝒫_j` with `X̄ = U`,
`‖e^{u_{j+1}(U)} e^{-(u+V)_{j+1}(U ∖ X)}‖_{T_{j+1}(ℓ_{j+1})} ≤ 2^{|𝓑_j(X)|}` (with the bulk and
observable parts of `u_{j+1}, V_{j+1}`, i.e. `prefG` of the observable map), provided
`‖V^∅‖_j + ‖K^∅‖_j ≤ c₀ / L^d` and `L^{2(d-2)} (‖V^obs‖_j + ‖K^obs‖_j) ≤ c₀ / L^d`, with `c₀`
depending only on `d`.  (We do not use the cancellation between `e^{u(U)}` and `e^{-u(U ∖ X)}`;
every block factor is bounded by `e^{O(c₀ / L^d)}`.) -/
theorem pert12_obs (hd : 3 ≤ d) : ∃ (c₀ : ℝ) (L₀ : ℕ), 0 < c₀ ∧ c₀ ≤ 1 ∧
    2 ^ (d + 3) + 8 * d + 1 ≤ L₀ ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∀ (N j : ℕ), j < N → ∀ (ℓ₀ : ℝ), 0 < ℓ₀ →
    ∀ (c : Case) (P : Prop) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (Vb : Vcoup) (Vo : Coup c)
      (K : Finset (Lam d L N) → OE c (Lam d L N)) (a b : Lam d L N) (A : ℝ), 1 ≤ A →
      StepObsHyp c P j ℓ₀ C Vb Vo K a b →
      Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) Vb +
          Knorm j (ellj d L ℓ₀ j) A (bulkK K) ≤ ENNReal.ofReal (c₀ / (L : ℝ) ^ d) →
      ENNReal.ofReal ((L : ℝ) ^ (2 * ((d : ℝ) - 2))) *
          (VnormObs c ℓ₀ a b j Vo + KnormObs c ℓ₀ a b j A K) ≤
        ENNReal.ofReal (c₀ / (L : ℝ) ^ d) →
      ∀ X U : Finset (Lam d L N), IsPolymer j X → clo j X = U →
        nrmj c ℓ₀ a b (j + 1) (prefG j (obsI j C Vb Vo K a b) U X) ≤ 2 ^ nb j X := by
  obtain ⟨C₁, L₁, hC₁, hL₁, hbr⟩ := obs_block_real hd
  refine ⟨1 / (14 * (1 + C₁)), L₁, by positivity,
    by rw [div_le_one (by positivity)]; linarith, hL₁, ?_⟩
  intro L _ hL N j hj ℓ₀ hℓ₀ c P C Vb Vo K a b A hA h hvkb hvko X U hX hU
  have hL4 : (4 : ℝ) ≤ L := four_le_of_L₀ (hL₁.trans hL)
  have hL0 : (0 : ℝ) < L := by linarith
  have hLd : (0 : ℝ) < (L : ℝ) ^ d := by positivity
  have hLd1 : (1 : ℝ) ≤ (L : ℝ) ^ d := one_le_pow₀ (by linarith)
  set c₀ : ℝ := 1 / (14 * (1 + C₁)) with hc₀
  have hc₀1 : c₀ / (L : ℝ) ^ d ≤ 1 := by
    rw [div_le_one hLd]
    exact le_trans (by rw [hc₀, div_le_one (by positivity)]; linarith) hLd1
  have hsm : ENNReal.ofReal ((L : ℝ) ^ (2 * ((d : ℝ) - 2))) *
      (VnormObs c ℓ₀ a b j Vo + KnormObs c ℓ₀ a b j A K) ≤ 1 :=
    hvko.trans (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hc₀1)
  obtain ⟨-, -, hvo, hko, hvb0, hkb0, hvo0, hko0, hvkr, -, hblk⟩ :=
    hbr L hL N j hj ℓ₀ hℓ₀ c P C Vb Vo K a b A hA h _ (by positivity) hvkb hsm
  set vbr := (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) Vb).toReal
  set kbr := (Knorm j (ellj d L ℓ₀ j) A (bulkK K)).toReal
  set vor := (VnormObs c ℓ₀ a b j Vo).toReal
  set kor := (KnormObs c ℓ₀ a b j A K).toReal
  set K₂ := (L : ℝ) ^ (2 * ((d : ℝ) - 2))
  have hK0 : 0 ≤ K₂ := by positivity
  have hsor : K₂ * (vor + kor) ≤ c₀ / (L : ℝ) ^ d := by
    rw [hvo, hko, ← ENNReal.ofReal_add hvo0 hko0, ← ENNReal.ofReal_mul hK0] at hvko
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hvko
  set α : ℝ := vbr + C₁ * kbr with hα
  set σ : ℝ := C₁ * K₂ * (vor + kor) with hσ
  have hα0 : 0 ≤ α := by positivity
  have hσ0 : 0 ≤ σ := by positivity
  -- smallness: `(4α + 3σ) L^d ≤ 1/2`
  have hsmall : (4 * α + 3 * σ) * (L : ℝ) ^ d ≤ 1 / 2 := by
    have h1 : α ≤ (1 + C₁) * (c₀ / (L : ℝ) ^ d) := by
      have : vbr + kbr ≤ c₀ / (L : ℝ) ^ d := hvkr
      nlinarith
    have h2 : σ ≤ C₁ * (c₀ / (L : ℝ) ^ d) := by
      rw [hσ, mul_assoc]; gcongr
    have h3 : (4 * α + 3 * σ) ≤ 7 * (1 + C₁) * (c₀ / (L : ℝ) ^ d) := by nlinarith
    calc (4 * α + 3 * σ) * (L : ℝ) ^ d ≤ 7 * (1 + C₁) * (c₀ / (L : ℝ) ^ d) * (L : ℝ) ^ d := by
          gcongr
      _ = 7 * (1 + C₁) * c₀ := by field_simp
      _ = 1 / 2 := by rw [hc₀]; field_simp; ring
  have hh : (0 : ℝ) < (L : ℝ) ^ (j + 1) := by positivity
  have hℓ := ellj_pos (d := d) hL0 hℓ₀ (j + 1)
  have hw := wj_sub (d := d) (L := L) (by omega) c hℓ₀ (coal L a b : ℕ∞) (j + 1)
  -- the block factors
  have hsmul : ∀ (z : ℂ) (F : OE c (Lam d L N)),
      nrmj c ℓ₀ a b (j + 1) (algebraMap ℂ (OE c (Lam d L N)) (Complex.exp z) * F) =
        ENNReal.ofReal (Real.exp z.re) * nrmj c ℓ₀ a b (j + 1) F := by
    intro z F
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, nrmj_smul, Complex.norm_exp]
  have hre : ∀ p ∈ blockIdx (L := L) (N := N) j,
      |((uVb j C Vb K).1 * (blockSet (L := L) (N := N) j p).card).re| ≤ α := fun p hp =>
    (Complex.abs_re_le_norm _).trans (hblk p hp).1
  have heu : ∀ p ∈ blockIdx (L := L) (N := N) j,
      nrmj c ℓ₀ a b (j + 1) ((obsI j C Vb Vo K a b).eu p) ≤ ENNReal.ofReal (Real.exp (α + σ)) := by
    intro p hp
    obtain ⟨-, -, hu, -, -⟩ := hblk p hp
    simp only [obsI]
    rw [hsmul, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
    gcongr
    · exact (le_abs_self _).trans (hre p hp)
    · exact oT_oexp_le hh hℓ hw (by rw [← coe_bulk, bulk_uObsX]; simp) hσ0 hu
  have hIt : ∀ p ∈ blockIdx (L := L) (N := N) j,
      nrmj c ℓ₀ a b (j + 1) (It (obsI j C Vb Vo K a b) p) ≤
        ENNReal.ofReal (Real.exp (3 * α + 2 * σ)) := by
    intro p hp
    obtain ⟨-, hV, hu, -, -⟩ := hblk p hp
    refine (nrmj_mul_le (by omega) hℓ₀ _ _ _).trans ?_
    simp only [obsI]
    rw [hsmul, show 3 * α + 2 * σ = (α + σ) + (2 * α + σ) by ring, Real.exp_add, Real.exp_add,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (Real.exp_pos _).le]
    gcongr
    · rw [Complex.neg_re]
      exact (neg_le_abs _).trans (hre p hp)
    · refine oT_oexp_le hh hℓ hw (by rw [← coe_bulk, map_neg, bulk_uObsX]; simp) hσ0 ?_
      rw [NegMemClass.coe_neg, oT_neg]; exact hu
    · refine oT_oexp_le hh hℓ hw (ε_neg_VfullX a b _ _ _) (by positivity) ?_
      rw [NegMemClass.coe_neg, oT_neg]
      exact hV.trans (ENNReal.ofReal_le_ofReal (by linarith))
  -- the product
  have hUp : IsPolymer (j + 1) U := hU ▸ isPolymer_clo j X
  have hUj : IsPolymer j U := IsPolymer.of_succ hUp
  have hnbU : (nb j U : ℝ) ≤ (L : ℝ) ^ d * nb j X := by
    rw [← hU]
    exact_mod_cast (nb_le_of_succ (isPolymer_clo j X)).trans
      (Nat.mul_le_mul_left _ (nb_clo_le j X))
  have hnbY : (nb j (U \ X) : ℝ) ≤ nb j U := by
    exact_mod_cast card_le_card (image_subset_image sdiff_subset)
  have hP1 : nrmj c ℓ₀ a b (j + 1) (PrefG j (obsI j C Vb Vo K a b) U) ≤
      ENNReal.ofReal (Real.exp (α + σ)) ^ nb j U := by
    refine (oT_prod_le hh hℓ hw _ _).trans ?_
    rw [nb, ← prod_const]
    exact prod_le_prod' fun p hp => heu p (mem_blockIdx_of_mem_blocks hp)
  have hP2 : nrmj c ℓ₀ a b (j + 1) (ItPow j (obsI j C Vb Vo K a b) (U \ X)) ≤
      ENNReal.ofReal (Real.exp (3 * α + 2 * σ)) ^ nb j (U \ X) := by
    refine (oT_prod_le hh hℓ hw _ _).trans ?_
    rw [nb, ← prod_const]
    exact prod_le_prod' fun p hp => hIt p (mem_blockIdx_of_mem_blocks hp)
  have he : Real.exp (1 / 2) ≤ 2 := by
    have := (abs_le.1 (Real.abs_exp_sub_one_le (x := 1 / 2) (by norm_num))).2
    norm_num at this ⊢; linarith
  refine (nrmj_mul_le (by omega) hℓ₀ _ _ _).trans ((mul_le_mul' hP1 hP2).trans ?_)
  rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← ENNReal.ofReal_pow (Real.exp_pos _).le,
    ← ENNReal.ofReal_mul (by positivity), ← Real.exp_nat_mul, ← Real.exp_nat_mul,
    ← Real.exp_add, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_pow (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc Real.exp (nb j U * (α + σ) + nb j (U \ X) * (3 * α + 2 * σ))
      ≤ Real.exp ((nb j X : ℝ) * (1 / 2)) := by
        refine Real.exp_le_exp.2 ?_
        have s1 : (nb j U : ℝ) * (α + σ) + nb j (U \ X) * (3 * α + 2 * σ) ≤
            nb j U * (4 * α + 3 * σ) := by nlinarith
        have s2 : (nb j U : ℝ) * (4 * α + 3 * σ) ≤ (L : ℝ) ^ d * nb j X * (4 * α + 3 * σ) :=
          mul_le_mul_of_nonneg_right hnbU (by positivity)
        nlinarith [mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg (α := ℝ) (nb j X))]
    _ = Real.exp (1 / 2) ^ nb j X := by rw [Real.exp_nat_mul]
    _ ≤ 2 ^ nb j X := pow_le_pow_left₀ (Real.exp_pos _).le he _

end Pert

end

end Obs
