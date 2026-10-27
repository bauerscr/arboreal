import Step2.Map.LocTr
import Step2.Map.Coord

/-!
# Contraction of the remainder `𝒲` (`h02uv-outline.tex`, Proposition `prop:W-contract`)

For translation-covariant `𝒲` (`FamCov`) and a translation-invariant covariance (`TInv`),
the part of `𝒲_{j+1}` linear in `𝒲` contracts:

  `‖𝒲_{j+1}‖_{j+1} ≤ C₀ L^d L^{-3} w + C(L) (v² + w²)` (`W_contract`).

With `𝒲(B) = A_B + P_B`, `P_B = Loc_B 𝒲(B)`, `R_B = 𝔼θ P_B`:

  `∑_{B ⊆ B_+} 𝒲_{j+1}(B) = (1 - Loc_{B_+}) (S_V + X₁) + (1 - Loc_{B_+}) U`,

where `S_V = ∑_B ½ F(V'_B, V'(Λ))`, `X₁ = ∑_B (𝔼θ A_B + (1 - Loc_B) R_B)` and
`U = ∑_B Loc_B R_B`. The last term vanishes: by covariance all `Loc_B R_B` are translates of one
uniform polynomial (`locR_eq_unif`), so `U` is uniform on `B_+` and `Loc_{B_+} U = U`
(`Loc2X_unif`). The terms of `X₁` gain `L^{-3}` by Lemma `lem:loc2`; for `R_B` this uses
`‖P_B‖_{T_j(2ℓ)} ≤ 16 ‖P_B‖_{T_j(ℓ)}` (`P_B` has degree `≤ 4`).
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Matrix

variable {d L N : ℕ} [NeZero L]

/-! ### Translation covariance -/

/-- Translation covariance of a block family at scale `j`: `F(B_b) = τ_{corner b} F(B_0)`. -/
def FamCov (j : ℕ) (F : Fam d L N) : Prop :=
  ∀ b ∈ blockIdx (L := L) (N := N) j,
    (F b : Alg d L N) = autAlg (Equiv.addRight (corner (L := L) (N := N) j b)) (F 0 : Alg d L N)

/-- Translation invariance of a covariance. -/
def TInv (C : Matrix (Lam d L N) (Lam d L N) ℂ) : Prop := ∀ t x y, C (x + t) (y + t) = C x y

theorem unif_transl (t : Lam d L N) (κ : ℂ) (c : Mono d → ℂ) (e : Fin d → Fin d → ℂ)
    (Y : Finset (Lam d L N)) :
    autAlg (Equiv.addRight t) (unif κ c e Y) = unif κ c e ((AffAut.transl t).img Y) := by
  have h1 : autAlg (Equiv.addRight t) (∑ M, c M • monoSet M Y) =
      ∑ M, (c M * 1) • monoSet M ((AffAut.transl t).img Y) :=
    (AffAut.transl t).autAlg_sum_monoSet c Y
  simp only [mul_one] at h1
  rw [unif, map_add, map_add, map_smul, map_one, h1, unif]
  simp only [map_sum, map_smul, autAlg_mono4Set]

theorem Loc2E_sub (X Y : Finset (Lam d L N)) (F G : EvR (Lam d L N)) :
    Loc2E X Y (F - G) = Loc2E X Y F - Loc2E X Y G := by
  have := Loc2E_add X Y (F - G) G
  rw [sub_add_cancel] at this
  rw [this, add_sub_cancel_right]

section Cov

variable {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℂ} {W : Fam d L N}

/-- `R_B = 𝔼θ Loc_B 𝒲(B)`. -/
def Rw (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (W : Fam d L N) (b : Fin d → ℕ) :
    EvR (Lam d L N) :=
  EthE C (Loc2E (blockSet (L := L) (N := N) j b) (blockSet j b) (W b))

/-- `A_B = 𝒲(B) - Loc_B 𝒲(B)`. -/
def Aw (j : ℕ) (W : Fam d L N) (b : Fin d → ℕ) : EvR (Lam d L N) :=
  W b - Loc2E (blockSet (L := L) (N := N) j b) (blockSet j b) (W b)

theorem Loc2XY_mem_nbhd (hd : 1 ≤ d) (j : ℕ) (b : Fin d → ℕ) (X : Finset (Lam d L N))
    (F : Alg d L N) :
    Loc2sXY X (blockSet (L := L) (N := N) j b) F ∈
      NX (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N)) :=
  add_mem (LocXY_mem hd (isPolymer_blockSet j b) X F) (Loc4sXY_mem hd (isPolymer_blockSet j b) X F)

/-- **Covariance**: `Loc_B R_B = τ_{corner b} Loc_{B_0} R_{B_0}`. -/
theorem locR_transl (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hjN : j + 1 < N) (hC : TInv C)
    (hW : InF j W) (hWc : FamCov j W) {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    (Loc2E (blockSet (L := L) (N := N) j b) (blockSet j b) (Rw j C W b) : Alg d L N) =
      autAlg (Equiv.addRight (corner (L := L) (N := N) j b))
        (Loc2E (blockSet (L := L) (N := N) j 0) (blockSet j 0) (Rw j C W 0) : Alg d L N) := by
  have h0 := zero_mem_blockIdx (d := d) (L := L) (N := N) j
  have himg : (AffAut.transl (corner (L := L) (N := N) j b)).img
      (blockSet (L := L) (N := N) j 0) = blockSet j b :=
    transl_corner_img (by omega) hb
  have hs0 := isSmall_blockSet_of_mem h0
  have hR := region_small hd hL hjN hs0
  have hne := hs0.2.1.1
  have hW0 := hW.loc 0
  have hP0 := Loc2XY_mem_nbhd (L := L) (N := N) hd j 0 (blockSet j 0) (W 0 : Alg d L N)
  have hR0 := expLC_mem_NX C hP0
  have hCt : ∀ x y, C ((Equiv.addRight (corner (L := L) (N := N) j b)) x)
      ((Equiv.addRight (corner (L := L) (N := N) j b)) y) = C x y :=
    fun x y => hC _ x y
  have hRb : ∀ b' : Fin d → ℕ,
      (Loc2E (blockSet (L := L) (N := N) j b') (blockSet j b') (Rw j C W b') : Alg d L N) =
        Loc2sXY (blockSet j b') (blockSet j b')
          (expLC C (Loc2sXY (blockSet j b') (blockSet j b') (W b' : Alg d L N))) := by
    intro b'; rw [coe_Loc2E, Rw, coe_EthE, coe_Loc2E]
  have e2 : Loc2sXY (blockSet (L := L) (N := N) j b) (blockSet j b)
      (autAlg (Equiv.addRight (corner (L := L) (N := N) j b)) (W 0 : Alg d L N)) =
      autAlg (Equiv.addRight (corner (L := L) (N := N) j b))
        (Loc2sXY (blockSet j 0) (blockSet j 0) (W 0 : Alg d L N)) := by
    rw [← himg]; exact (Loc2XY_transl hR hne _ _ hW0).symm
  have e4 : Loc2sXY (blockSet (L := L) (N := N) j b) (blockSet j b)
      (autAlg (Equiv.addRight (corner (L := L) (N := N) j b))
        (expLC C (Loc2sXY (blockSet j 0) (blockSet j 0) (W 0 : Alg d L N)))) =
      autAlg (Equiv.addRight (corner (L := L) (N := N) j b))
        (Loc2sXY (blockSet j 0) (blockSet j 0)
          (expLC C (Loc2sXY (blockSet j 0) (blockSet j 0) (W 0 : Alg d L N)))) := by
    rw [← himg]; exact (Loc2XY_transl hR hne _ _ hR0).symm
  rw [hRb, hRb, hWc b hb, e2, expLC_autAlg _ hCt, e4]

/-- All `Loc_B R_B` are the same uniform polynomial, placed on `B`. -/
theorem locR_eq_unif (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hjN : j + 1 < N) (hC : TInv C)
    (hW : InF j W) (hWc : FamCov j W) :
    ∃ (κ : ℂ) (c : Mono d → ℂ) (e : Fin d → Fin d → ℂ), ∀ b ∈ blockIdx (L := L) (N := N) j,
      (Loc2E (blockSet (L := L) (N := N) j b) (blockSet j b) (Rw j C W b) : Alg d L N) =
        unif κ c e (blockSet j b) := by
  have h0 := zero_mem_blockIdx (d := d) (L := L) (N := N) j
  have hne := (isSmall_blockSet_of_mem h0).2.1.1
  set F0 := (Rw j C W 0 : Alg d L N)
  refine ⟨ε F0, locCoef (blockSet (L := L) (N := N) j 0) F0,
    fun i k => mu4 (base (blockSet (L := L) (N := N) j 0)) i k F0 /
      ((blockSet (d := d) (L := L) (N := N) j 0).card : ℂ),
    fun b hb => ?_⟩
  rw [locR_transl hd hL hjN hC hW hWc hb, coe_Loc2E,
    show Loc2sXY (blockSet (L := L) (N := N) j 0) (blockSet j 0) F0 = Loc2sX (blockSet j 0) F0
      from rfl, Loc2X_eq_unif hne, unif_transl, transl_corner_img (by omega) hb]

/-- **`Loc_{B_+} U = U`** for `U = ∑_{B ⊆ B_+} Loc_B R_B`. -/
theorem loc_U (hd : 1 ≤ d) (hL : 2 ^ (d + 3) + 8 * d < L) (hjN : j + 1 < N) (hC : TInv C)
    (hW : InF j W) (hWc : FamCov j W) {c' : Fin d → ℕ}
    (hc' : c' ∈ blockIdx (L := L) (N := N) (j + 1)) :
    Loc2E (blockSet (L := L) (N := N) (j + 1) c') (blockSet (j + 1) c')
      (∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
        Loc2E (blockSet (L := L) (N := N) j b) (blockSet j b) (Rw j C W b)) =
      ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
        Loc2E (blockSet (L := L) (N := N) j b) (blockSet j b) (Rw j C W b) := by
  obtain ⟨κ, c, e, he⟩ := locR_eq_unif hd (by omega) hjN hC hW hWc
  have hsm := isSmall_blockSet_of_mem hc'
  have hpatch := patch_of_small hL hjN hsm
  refine Subtype.ext ?_
  have hsum : ((∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
      Loc2E (blockSet (L := L) (N := N) j b) (blockSet j b) (Rw j C W b) : EvR (Lam d L N)) :
        Alg d L N) =
      unif ((blocks j (blockSet (L := L) (N := N) (j + 1) c')).card * κ) c e
        (blockSet (j + 1) c') := by
    rw [AddSubmonoidClass.coe_finsetSum,
      sum_congr rfl fun b hb => he b (mem_blockIdx_of_mem_blocks hb),
      unif_sum _ κ c e _ (pairwiseDisjoint_blockSet j _),
      biUnion_blocks (IsPolymer.of_succ (isPolymer_blockSet (j + 1) c'))]
  rw [coe_Loc2E, hsum]
  exact Loc2X_unif hpatch hsm.2.1.1 _ c e

end Cov

/-! ### Norm lemmas -/

theorem GramBound_mono {Λ : Type*} [DecidableEq Λ] [Fintype Λ] {E : Type*} [Fintype E] [DecidableEq E] [AddAction (E → ℕ) Λ]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {p : ℕ} {h h' ℓ : ℝ}
    (hh' : 0 < h') (hle : h' ≤ h) (hℓ : 0 ≤ ℓ) {Fv Gv : Λ → H}
    (hB : GramBound E p h ℓ Fv Gv) : GramBound E p h' ℓ Fv Gv := by
  intro a ha x
  obtain ⟨h1, h2⟩ := hB a ha x
  have hinv : (h ^ mabs a)⁻¹ ≤ (h' ^ mabs a)⁻¹ :=
    inv_anti₀ (pow_pos hh' _) (pow_le_pow_left₀ hh'.le hle _)
  exact ⟨h1.trans (mul_le_mul_of_nonneg_left hinv hℓ),
    h2.trans (mul_le_mul_of_nonneg_left hinv hℓ)⟩

/-- `‖𝔼θ F‖_{T_j(ℓ)} ≤ ‖F‖_{T_j(2ℓ)}` for a covariance with the Gram bound at scale `j + 1`. -/
theorem expLC_same_le {j : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {C : Matrix (Lam d L N) (Lam d L N) ℂ}
    (hC : GoodCov2 j ℓ C) (F : Alg d L N) :
    Tj d (L : ℝ) j ℓ (expLC C F) ≤ Tj d (L : ℝ) j (2 * ℓ) F := by
  obtain ⟨H, _, _, Fv, Gv, hG, hB⟩ := hC.gram
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hL0 : (0 : ℝ) < L := by linarith
  have hB' : GramBound (Dir d) (pPhi d) ((L : ℝ) ^ j) ℓ Fv Gv :=
    GramBound_mono (pow_pos hL0 _) (pow_le_pow_right₀ hL1 (Nat.le_succ j)) hℓ.le hB
  rw [← ECC_theta]
  exact tNorm_ECC_theta_le (pow_pos hL0 _) hℓ hG hB' F

/-- `‖∏ (1 + x_i) - 1 - ∑ x_i‖ ≤ (1+δ)^n - 1 - nδ`. -/
theorem tn_prod_sub_one_sub {X : Type*} [DecidableEq X] [Fintype X] {E : Type*} [Fintype E]
    [DecidableEq E] [AddAction (E → ℕ) X] {p : ℕ} {h ℓ : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → EvR X) {δ : ℝ} (hδ : 0 ≤ δ)
    (hx : ∀ i ∈ s, tNorm E p h ℓ (x i : Grassmann.N X) ≤ ENNReal.ofReal δ) :
    tNorm E p h ℓ ((∏ i ∈ s, (1 + x i) - 1 - ∑ i ∈ s, x i : EvR X) : Grassmann.N X) ≤
      ENNReal.ofReal ((1 + δ) ^ s.card - 1 - s.card * δ) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [prod_empty, sub_self, sum_empty, card_empty, pow_zero, ZeroMemClass.coe_zero,
      CharP.cast_eq_zero, zero_mul]
    rw [tn_zero']; exact zero_le
  | insert a s ha ih =>
    have ih' := ih fun i hi => hx i (mem_insert_of_mem hi)
    have hxa := hx a (mem_insert_self a s)
    have hP := tn_prod_sub_one (E := E) (p := p) hh hℓ s (fun i => 1 + x i) hδ (fun i hi => by
      simp only [add_sub_cancel_left]; exact hx i (mem_insert_of_mem hi))
    have e : ∏ i ∈ insert a s, (1 + x i) - 1 - ∑ i ∈ insert a s, x i =
        (∏ i ∈ s, (1 + x i) - 1 - ∑ i ∈ s, x i) + x a * (∏ i ∈ s, (1 + x i) - 1) := by
      rw [prod_insert ha, sum_insert ha]; ring
    have h1 : 0 ≤ (1 + δ) ^ s.card - 1 := by
      have := one_le_pow₀ (M₀ := ℝ) (n := s.card) (by linarith : (1 : ℝ) ≤ 1 + δ); linarith
    have h2 : 0 ≤ (1 + δ) ^ s.card - 1 - s.card * δ := by
      have := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ δ) s.card; linarith
    rw [e]
    refine (tn_addE h2 (by positivity) ih' (tn_mulE hh hℓ hδ hxa hP)).trans
      (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    rw [card_insert_of_notMem ha, pow_succ]; push_cast; ring

theorem pow_sub_one_sub_le {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) :
    (1 + δ) ^ n - 1 - n * δ ≤ n ^ 2 * δ ^ 2 * (1 + δ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : 1 ≤ (1 + δ) ^ n := one_le_pow₀ (by linarith)
    have e : (1 + δ) ^ (n + 1) - 1 - ((n + 1 : ℕ) : ℝ) * δ =
        (1 + δ) * ((1 + δ) ^ n - 1 - n * δ) + n * δ ^ 2 := by push_cast; ring
    rw [e]
    have h2 : (1 + δ) * ((1 + δ) ^ n - 1 - n * δ) ≤ (1 + δ) * (n ^ 2 * δ ^ 2 * (1 + δ) ^ n) :=
      mul_le_mul_of_nonneg_left ih (by linarith)
    have h3 : (n : ℝ) * δ ^ 2 ≤ (2 * n + 1) * δ ^ 2 * (1 + δ) ^ (n + 1) := by
      have : (1 : ℝ) ≤ (1 + δ) ^ (n + 1) := one_le_pow₀ (by linarith)
      have h4 : (0 : ℝ) ≤ δ ^ 2 := sq_nonneg δ
      have h5 : (n : ℝ) ≤ 2 * n + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
      calc (n : ℝ) * δ ^ 2 ≤ (2 * n + 1) * δ ^ 2 := by nlinarith
        _ ≤ _ := le_mul_of_one_le_right (by positivity) this
    calc (1 + δ) * ((1 + δ) ^ n - 1 - n * δ) + n * δ ^ 2
        ≤ (1 + δ) * (n ^ 2 * δ ^ 2 * (1 + δ) ^ n) + (2 * n + 1) * δ ^ 2 * (1 + δ) ^ (n + 1) :=
          add_le_add h2 h3
      _ = ((n + 1 : ℕ) : ℝ) ^ 2 * δ ^ 2 * (1 + δ) ^ (n + 1) := by push_cast; ring

/-! ### The bound for one `(j+1)`-block -/

namespace BH

variable {j : ℕ} {ℓ ℓ' ℓC : ℝ} {C : Matrix (Lam d L N) (Lam d L N) ℂ} {V W : Fam d L N}
  {K : Act d L N} {A r Cl cS : ℝ} (H : BH j ℓ ℓ' ℓC C V W K A r Cl cS) {v w : ℝ}
  (hv0 : 0 ≤ v) (hw0 : 0 ≤ w)
  (hv : ∀ b ∈ blockIdx (L := L) (N := N) j, Tj d (L : ℝ) j ℓ (V b : Alg d L N) ≤ ENNReal.ofReal v)
  (hw : ∀ b ∈ blockIdx (L := L) (N := N) j, Tj d (L : ℝ) j ℓ (W b : Alg d L N) ≤ ENNReal.ofReal w)
  {Cc : ℝ} (hCc : 0 ≤ Cc)
  (hcon : ∀ ℓ₀ ℓ₁ : ℝ, 0 < ℓ₀ → 0 < ℓ₁ → ℓ₁ ≤ 2 * ℓ₀ → ∀ X : Finset (Lam d L N), IsSmall j X →
    ∀ F ∈ NX (nbhd j X : Set (Lam d L N)), IsSym F →
      Tj d (L : ℝ) (j + 1) ℓ₁ (F - Loc2sX X F) ≤
        ENNReal.ofReal (Cc / (L : ℝ) ^ 3) * Tj d (L : ℝ) j ℓ₀ F)
  (hCℓ : ℓC ≤ ℓ)
include H

/-- `S_V(B) = ½ F(V'_B, V'(Λ))`. -/
def SV (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V : Fam d L N) (b : Fin d → ℕ) :
    EvR (Lam d L N) :=
  (1 / 2 : ℂ) • FCE C (Vpr C V b) (VprL j C V)

include hv hv0 in
theorem SV_le {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    Tj d (L : ℝ) (j + 1) ℓ' (SV j C V b : Alg d L N) ≤
      ENNReal.ofReal (cNear d L * Q1 d ^ 2 * v ^ 2) := by
  rw [SV, FCE_VprL_eq H.hjN H.hC H.hV b]
  have h1 := tn_sum_const (E := Dir d) (p := pPhi d) (h := (L : ℝ) ^ (j + 1)) (ℓ := ℓ')
    (nearSet (L := L) (N := N) j b) (fun b' => FCE C (Vpr C V b) (Vpr C V b'))
    (r := 2 * (Q1 d * v) ^ 2) (by positivity)
    (fun b' hb' => H.FCE_pair_le' hv0 hv hb (mem_filter.1 hb').1)
  have hn : ((nearSet (L := L) (N := N) j b).card : ℝ) ≤ cNear d L := by
    unfold cNear; exact_mod_cast card_nearSet_le H.hj.le b hb
  rw [Subalgebra.coe_smul, Tj_smul']
  refine (mul_le_mul_left' h1 _).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [this]
  have := H.hcNear
  calc 1 / 2 * (((nearSet (L := L) (N := N) j b).card : ℝ) * (2 * (Q1 d * v) ^ 2))
      = ((nearSet (L := L) (N := N) j b).card : ℝ) * (Q1 d ^ 2 * v ^ 2) := by ring
    _ ≤ cNear d L * (Q1 d ^ 2 * v ^ 2) := by gcongr
    _ = _ := by ring

include hw hcon hCc in
theorem EthAw_le {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    Tj d (L : ℝ) (j + 1) ℓ' (EthE C (Aw j W b) : Alg d L N) ≤
      ENNReal.ofReal (Cc / (L : ℝ) ^ 3 * w) := by
  have hL0 := H.hL0
  rw [coe_EthE, ← ECC_theta]
  refine (EthE_succ_le2' H.hℓ' H.hℓC H.hsum H.hC _).trans ?_
  have h := hcon ℓ (2 * ℓ) H.hℓ (by linarith [H.hℓ]) le_rfl _ (isSmall_blockSet_of_mem hb)
    _ (H.hW.loc b) (H.hW.sym b)
  rw [Aw, AddSubgroupClass.coe_sub, coe_Loc2E]
  exact tj_of (by positivity) h (hw b hb)

include hw hcon hCc hCℓ in
theorem Rw_le {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    Tj d (L : ℝ) (j + 1) ℓ' ((Rw j C W b - Loc2E (blockSet (L := L) (N := N) j b) (blockSet j b)
      (Rw j C W b) : EvR (Lam d L N)) : Alg d L N) ≤
      ENNReal.ofReal (Cc / (L : ℝ) ^ 3 * (16 * (Cl * w))) := by
  have hL0 := H.hL0
  have hCl := H.hCl
  have hsm := isSmall_blockSet_of_mem hb
  have hP := Loc2XY_mem_nbhd H.hd j b (blockSet (L := L) (N := N) j b) (W b : Alg d L N)
  have hRmem : (Rw j C W b : Alg d L N) ∈ NX (nbhd j (blockSet (L := L) (N := N) j b) : Set _) :=
    by rw [Rw, coe_EthE]; exact expLC_mem_NX C hP
  have hRsym : IsSym (Rw j C W b : Alg d L N) := by
    rw [isSym_iff_mem_SymS]; exact EthE_sym (Loc2E_sym _ _ _)
  have h1 := hcon ℓ ℓ' H.hℓ H.hℓ' (by linarith [H.hsum, H.hℓC]) _ hsm _ hRmem hRsym
  rw [AddSubgroupClass.coe_sub, coe_Loc2E,
    ENNReal.ofReal_mul (div_nonneg hCc (pow_nonneg hL0.le 3))]
  refine h1.trans (mul_le_mul_left' ?_ _)
  -- `‖R_B‖_{T_j(ℓ)} ≤ 16 Cl w`
  rw [Rw, coe_EthE, coe_Loc2E]
  refine (expLC_same_le H.hℓ (H.hC.mono hCℓ) _).trans ?_
  refine (tNorm_two_le_of_deg (E := Dir d) (pPhi d) (pow_pos hL0 _).le H.hℓ
    fun n z hn => coeff_Loc2XY_of_lt _ _ _ z hn).trans ?_
  have h2 := H.hloc j H.hj ℓ H.hℓ _ _ hsm subset_rfl _ (H.hW.loc b)
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul hCl, ENNReal.ofReal_ofNat]
  exact mul_le_mul_left' (h2.trans (mul_le_mul_left' (hw b hb) _)) _

include hv hw hv0 hw0 hcon hCc hCℓ in
/-- **The bound on one `(j+1)`-block**: `‖∑_{B ⊆ B_+} 𝒲_{j+1}(B)‖ ≤ (1 + C_l) n (C v² + C L^{-3} w)`. -/
theorem sumWp_le (hT : TInv C) (hWc : FamCov j W) {c' : Fin d → ℕ}
    (hc' : c' ∈ blockIdx (L := L) (N := N) (j + 1)) :
    Tj d (L : ℝ) (j + 1) ℓ' ((∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
      Wp j C V W b : EvR (Lam d L N)) : Alg d L N) ≤
      ENNReal.ofReal ((1 + Cl) * ((L : ℝ) ^ d * (cNear d L * Q1 d ^ 2 * v ^ 2 +
        Cc / (L : ℝ) ^ 3 * w + Cc / (L : ℝ) ^ 3 * (16 * (Cl * w))))) := by
  have hL0 := H.hL0
  have hCl := H.hCl
  have hQ := H.hQ1
  have hcN := H.hcNear
  set Bc := blockSet (L := L) (N := N) (j + 1) c' with hBc
  set s := blocks j Bc with hs
  have hBp : ∀ b ∈ s, Bp (L := L) (N := N) j b = Bc := fun b hb => by
    obtain ⟨hb1, hb2⟩ := mem_blocks_blockSet_succ.1 hb
    rw [Bp, clo_blockSet hb1, hb2]
  set T : (Fin d → ℕ) → EvR (Lam d L N) := fun b => SV j C V b + EthE C (Aw j W b) +
    (Rw j C W b - Loc2E (blockSet (L := L) (N := N) j b) (blockSet j b) (Rw j C W b)) with hT'
  set Y : EvR (Lam d L N) := ∑ b ∈ s, T b with hY
  set U : EvR (Lam d L N) :=
    ∑ b ∈ s, Loc2E (blockSet (L := L) (N := N) j b) (blockSet j b) (Rw j C W b) with hUdef
  have hSb : ∀ b, Sb j C V W b = T b +
      Loc2E (blockSet (L := L) (N := N) j b) (blockSet j b) (Rw j C W b) := by
    intro b
    have e : EthE C (W b) = EthE C (Aw j W b) +
        EthE C (Loc2E (blockSet (L := L) (N := N) j b) (blockSet j b) (W b)) := by
      rw [← EthE_add, Aw, sub_add_cancel]
    simp only [hT', Sb, SV, Rw, e]
    abel
  have hSX : SX j C V W Bc = Y + U := by
    rw [SX, hY, hUdef, ← sum_add_distrib]
    exact sum_congr rfl fun b _ => hSb b
  have hsum : ∑ b ∈ s, Wp j C V W b = (Y + U) - Loc2E Bc Bc (Y + U) := by
    have e1 : ∑ b ∈ s, Wp j C V W b =
        ∑ b ∈ s, Sb j C V W b - ∑ b ∈ s, Loc2E Bc (blockSet j b) (SX j C V W Bc) := by
      rw [← sum_sub_distrib]
      refine sum_congr rfl fun b hb => ?_
      rw [Wp, LS, hBp b hb]
    rw [e1, Loc2E_sum_blocks (j := j) (IsPolymer.of_succ (isPolymer_blockSet (j + 1) c')), ← hSX]
    rfl
  have hU : Loc2E Bc Bc U = U := loc_U H.hd H.hL8 H.hjN hT H.hW hWc hc'
  have hYU : (Y + U) - Loc2E Bc Bc (Y + U) = Y - Loc2E Bc Bc Y := by
    rw [Loc2E_add, hU]; abel
  rw [hsum, hYU]
  -- the bound on `Y`
  set r := cNear d L * Q1 d ^ 2 * v ^ 2 + Cc / (L : ℝ) ^ 3 * w + Cc / (L : ℝ) ^ 3 * (16 * (Cl * w))
  have hr0 : 0 ≤ r := by positivity
  have hTb : ∀ b ∈ s, Tj d (L : ℝ) (j + 1) ℓ' (T b : Alg d L N) ≤ ENNReal.ofReal r := by
    intro b hb
    have hb' := mem_blockIdx_of_mem_blocks hb
    exact tn_addE (by positivity) (by positivity)
      (tn_addE (by positivity) (by positivity) (H.SV_le hv0 hv hb')
        (H.EthAw_le hw hCc hcon hb')) (H.Rw_le hw hCc hcon hCℓ hb')
  have hYb : Tj d (L : ℝ) (j + 1) ℓ' (Y : Alg d L N) ≤ ENNReal.ofReal ((L : ℝ) ^ d * r) := by
    refine (tn_sum_const (E := Dir d) (p := pPhi d) _ _ hr0 hTb).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have : (s.card : ℝ) ≤ (L : ℝ) ^ d := by
      have := nb_blockSet_succ_le (L := L) (N := N) j c'
      unfold nb at this; exact_mod_cast this
    exact mul_le_mul_of_nonneg_right this hr0
  -- membership of `Y`
  have hYmem : (Y : Alg d L N) ∈ NX (nbhd (j + 1) Bc : Set (Lam d L N)) := by
    rw [hY, AddSubmonoidClass.coe_finsetSum]
    refine Subalgebra.sum_mem _ fun b hb => NBp_le_block hb ?_
    have hb' := mem_blockIdx_of_mem_blocks hb
    have hWb : (W b : Alg d L N) ∈ NB (L := L) (N := N) j b := H.hW.loc b
    have hLW := Loc2E_mem_NB (j := j) H.hd hb'
      (blockSet j b) (W b)
    have hRb : (Rw j C W b : Alg d L N) ∈ NB (L := L) (N := N) j b := by
      rw [Rw]; exact EthE_mem_NB hLW
    have hSVb : (SV j C V b : Alg d L N) ∈ NBp (L := L) (N := N) j b := by
      have e : SV j C V b = Sb j C V W b - EthE C (W b) := by rw [Sb, SV, add_sub_cancel_right]
      rw [e, AddSubgroupClass.coe_sub]
      exact sub_mem (Sb_mem' H.hd (by have := H.hL8; omega) H.hjN H.hC H.hV H.hW hb')
        (NB_le_NBp j b (EthE_mem_NB hWb))
    simp only [hT', AddMemClass.coe_add, AddSubgroupClass.coe_sub]
    refine add_mem (add_mem hSVb (NB_le_NBp j b (EthE_mem_NB ?_)))
      (NB_le_NBp j b (sub_mem hRb (Loc2E_mem_NB (j := j) H.hd hb' _ _)))
    rw [Aw, AddSubgroupClass.coe_sub]
    exact sub_mem hWb hLW
  have hLoc := H.hloc (j + 1) H.hjN ℓ' H.hℓ' Bc Bc (isSmall_blockSet_of_mem hc') subset_rfl _ hYmem
  rw [← coe_Loc2E] at hLoc
  refine (tn_subE (by positivity) (by positivity) hYb ((hLoc.trans
    (mul_le_mul_left' hYb _)).trans_eq (ENNReal.ofReal_mul hCl).symm)).trans ?_
  exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))

end BH

/-! ### The theorem -/

set_option maxHeartbeats 1000000 in
/-- **Proposition `prop:W-contract`** (for `d ≥ 2`, with `L^d L^{-3}`): for translation-covariant
`𝒲` and a translation-invariant covariance,
`‖𝒲_{j+1}‖_{j+1} ≤ C₀ L^d L^{-3} w + C(L) (v² + w²)`, with `C₀` independent of `L`. -/
theorem W_contract_ts (d : ℕ) (hd : 2 ≤ d) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ L₀ : ℕ,
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ C₁ : ℝ, 0 ≤ C₁ ∧
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ → ℓC ≤ ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓC C → TInv C →
    ∀ V W : Fam d L N, InF j V → InF j W → (∀ b, ε (V b : Alg d L N) = 0) → FamCov j W →
    ∀ v w : ℝ, 0 ≤ v → 0 ≤ w → v ≤ 1 → w ≤ 1 →
      Fnorm j ℓ V ≤ ENNReal.ofReal v → Fnorm j ℓ W ≤ ENNReal.ofReal w →
      Fnorm (j + 1) ℓ' (Wnext2 j C V W) ≤
        ENNReal.ofReal (C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3) * w + C₁ * (v ^ 2 + w ^ 2)) := by
  classical
  obtain ⟨Cl, hCl0, hloc⟩ := exists_Loc2sXY_bound d (by omega)
  obtain ⟨Cc, hCc0, L₁, hcon⟩ := loc2s_contract d hd
  obtain ⟨cc, hcc⟩ := card_small_containing d
  refine ⟨(1 + Cl) * (1 + 16 * Cl) * Cc, by positivity,
    max (max (2 ^ (d + 3) + 8 * d + 1) ⌈pauliL0 d⌉₊) L₁, ?_⟩
  intro L _ hL
  have hL8 : 2 ^ (d + 3) + 8 * d < L :=
    lt_of_lt_of_le (Nat.lt_succ_self _) ((le_max_left _ _).trans ((le_max_left _ _).trans hL))
  have hLp : pauliL0 d ≤ L := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right _ _).trans ((le_max_left _ _).trans hL))
  have hL₁ : L₁ ≤ L := (le_max_right _ _).trans hL
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hQ := one_le_Q1 (by omega : 1 ≤ d)
  have hN0 : 0 ≤ cNear d L := Nat.cast_nonneg _
  set n : ℝ := (L : ℝ) ^ d with hn
  have hn0 : 0 ≤ n := by positivity
  set Cσ : ℝ := (1 + Cl * n) * (cNear d L * Q1 d ^ 2 + Q1 d) with hCσ
  have hCσ0 : 0 ≤ Cσ := by positivity
  set C₁ : ℝ := (1 + Cl) * n * (cNear d L * Q1 d ^ 2) + n ^ 2 * (2 * Cσ ^ 2) * (1 + Cσ) ^ (L ^ d)
    with hC₁
  refine ⟨C₁, by positivity, ?_⟩
  intro N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum hCℓ C hC hT V W hV hW hV0 hWc v w hv0 hw0 hv1 hw1 hVv hWw
  have hvb : ∀ b ∈ blockIdx (L := L) (N := N) j, Tj d (L : ℝ) j ℓ (V b : Alg d L N) ≤
      ENNReal.ofReal v := fun b hb => (le_iSup₂ (f := fun b (_ : b ∈ blockIdx (L := L) (N := N) j) =>
        Tj d (L : ℝ) j ℓ (V b : Alg d L N)) b hb).trans hVv
  have hwb : ∀ b ∈ blockIdx (L := L) (N := N) j, Tj d (L : ℝ) j ℓ (W b : Alg d L N) ≤
      ENNReal.ofReal w := fun b hb => (le_iSup₂ (f := fun b (_ : b ∈ blockIdx (L := L) (N := N) j) =>
        Tj d (L : ℝ) j ℓ (W b : Alg d L N)) b hb).trans hWw
  have hK0 : InK2 j (0 : Act d L N) :=
    { loc := fun _ _ => zero_mem _, sym := fun _ _ => (isSym_iff_mem_SymS _).2 (zero_mem _) }
  have H : BH j ℓ ℓ' ℓC C V W (0 : Act d L N) 1 1 Cl (cc + 1) :=
    { hd := by omega, hLp := hLp, hL8 := hL8, hjN := hjN, hℓ := hℓ, hℓ' := hℓ', hℓC := hℓC, hsum := hsum, hC := hC, hV := hV,
      hW := hW, hV0 := hV0, hK := hK0, hA := le_rfl, hr := zero_le_one, hr1 := le_rfl
      hVr := fun b hb => (hvb b hb).trans (ENNReal.ofReal_le_ofReal hv1)
      hWr := fun b hb => (hwb b hb).trans (ENNReal.ofReal_le_ofReal hw1)
      hKr := by rw [Knorm_zero]; exact zero_le
      hCl := hCl0
      hloc := fun k hk ℓ₀ hℓ₀ X Y hX hYX F hF => hloc L hL8 N k hk X Y hX hYX F hF ℓ₀ hℓ₀
      hcS := by linarith [Nat.cast_nonneg (α := ℝ) cc]
      hcount := fun b hb => by
        have h1 : ((smallSets (d := d) (L := L) (N := N) j).filter
            (fun X => blockSet j b ⊆ X)).card ≤ cc := by convert hcc L N j b hb
        have h2 := Nat.cast_le (α := ℝ) |>.2 h1
        push_cast; linarith }
  have hcon' : ∀ ℓ₀ ℓ₁ : ℝ, 0 < ℓ₀ → 0 < ℓ₁ → ℓ₁ ≤ 2 * ℓ₀ → ∀ X : Finset (Lam d L N), IsSmall j X →
      ∀ F ∈ NX (nbhd j X : Set (Lam d L N)), IsSym F →
        Tj d (L : ℝ) (j + 1) ℓ₁ (F - Loc2sX X F) ≤
          ENNReal.ofReal (Cc / (L : ℝ) ^ 3) * Tj d (L : ℝ) j ℓ₀ F :=
    fun ℓ₀ ℓ₁ h0 h1 h2 X hX F hF hs => hcon L hL8 hL₁ N j (by omega) ℓ₀ ℓ₁ h0 h1 h2 X hX F hF hs
  have hsig : BH.sig d L v w ≤ (cNear d L * Q1 d ^ 2 + Q1 d) * (v ^ 2 + w) := by
    unfold BH.sig
    have h1 : 0 ≤ cNear d L * Q1 d ^ 2 * w := mul_nonneg (mul_nonneg hN0 (sq_nonneg _)) hw0
    have h2 : 0 ≤ Q1 d * v ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    nlinarith
  have hsig1 : BH.sig d L v w ≤ cNear d L * Q1 d ^ 2 + Q1 d := by
    unfold BH.sig
    have : v ^ 2 ≤ 1 := by nlinarith
    have h1 : cNear d L * Q1 d ^ 2 * v ^ 2 ≤ cNear d L * Q1 d ^ 2 :=
      mul_le_of_le_one_right (mul_nonneg hN0 (sq_nonneg _)) this
    have h2 : Q1 d * w ≤ Q1 d := mul_le_of_le_one_right (by linarith) hw1
    linarith
  refine iSup₂_le fun c' hc' => ?_
  rw [Wnext2]
  set s := blocks j (blockSet (L := L) (N := N) (j + 1) c')
  set δ := (1 + Cl * (L : ℝ) ^ d) * BH.sig d L v w with hδdef
  have hδ0 : 0 ≤ δ := mul_nonneg (by positivity) (BH.sig_nonneg (L := L) (by omega) v w hw0)
  have hR := tn_prod_sub_one_sub (E := Dir d) (p := pPhi d) H.hh' hℓ' s (Wp j C V W) hδ0
    (fun b hb => H.Wp_le' hv0 hw0 hv1 hvb hwb (mem_blockIdx_of_mem_blocks hb))
  have hS := H.sumWp_le hv0 hw0 hvb hwb hCc0 hcon' hCℓ hT hWc hc'
  have e : ∏ b ∈ s, (1 + Wp j C V W b) - 1 =
      (∏ b ∈ s, (1 + Wp j C V W b) - 1 - ∑ b ∈ s, Wp j C V W b) + ∑ b ∈ s, Wp j C V W b := by
    abel
  rw [e]
  refine (tn_addE (by
    have := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ δ) s.card; linarith) (by positivity)
    hR hS).trans (ENNReal.ofReal_le_ofReal ?_)
  -- the real inequality
  have hsn : s.card ≤ L ^ d := nb_blockSet_succ_le j c'
  have hs : (s.card : ℝ) ≤ n := by rw [hn]; exact_mod_cast hsn
  have hδ : δ ≤ Cσ * (v ^ 2 + w) := by
    rw [hδdef, hCσ, mul_assoc]; exact mul_le_mul_of_nonneg_left hsig (by positivity)
  have hδ1 : δ ≤ Cσ := by
    rw [hδdef, hCσ]; exact mul_le_mul_of_nonneg_left hsig1 (by positivity)
  have hP1 := pow_sub_one_sub_le hδ0 s.card
  have hP2 : (1 + δ) ^ s.card ≤ (1 + Cσ) ^ (L ^ d) :=
    (pow_le_pow_left₀ (by linarith) (by linarith) _).trans
      (pow_le_pow_right₀ (by linarith) hsn)
  have hδ2 : δ ^ 2 ≤ 2 * Cσ ^ 2 * (v ^ 2 + w ^ 2) := by
    have h1 : δ ^ 2 ≤ (Cσ * (v ^ 2 + w)) ^ 2 := pow_le_pow_left₀ hδ0 hδ 2
    have h2 : (v ^ 2 + w) ^ 2 ≤ 2 * (v ^ 2 + w ^ 2) := by
      have hv2 : v ^ 2 ≤ 1 := by nlinarith
      have : v ^ 4 ≤ v ^ 2 := by
        calc v ^ 4 = v ^ 2 * v ^ 2 := by ring
          _ ≤ v ^ 2 * 1 := mul_le_mul_of_nonneg_left hv2 (sq_nonneg v)
          _ = v ^ 2 := by ring
      nlinarith [sq_nonneg (v ^ 2 - w)]
    calc δ ^ 2 ≤ (Cσ * (v ^ 2 + w)) ^ 2 := h1
      _ = Cσ ^ 2 * (v ^ 2 + w) ^ 2 := by ring
      _ ≤ Cσ ^ 2 * (2 * (v ^ 2 + w ^ 2)) := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = _ := by ring
  have hrem : (1 + δ) ^ s.card - 1 - s.card * δ ≤
      n ^ 2 * (2 * Cσ ^ 2) * (1 + Cσ) ^ (L ^ d) * (v ^ 2 + w ^ 2) := by
    refine hP1.trans ?_
    have h1 : (s.card : ℝ) ^ 2 ≤ n ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hs 2
    calc (s.card : ℝ) ^ 2 * δ ^ 2 * (1 + δ) ^ s.card
        ≤ n ^ 2 * (2 * Cσ ^ 2 * (v ^ 2 + w ^ 2)) * (1 + Cσ) ^ (L ^ d) := by gcongr
      _ = _ := by ring
  have hmain : (1 + Cl) * ((L : ℝ) ^ d * (cNear d L * Q1 d ^ 2 * v ^ 2 +
      Cc / (L : ℝ) ^ 3 * w + Cc / (L : ℝ) ^ 3 * (16 * (Cl * w)))) =
      (1 + Cl) * (1 + 16 * Cl) * Cc * ((L : ℝ) ^ d / (L : ℝ) ^ 3) * w +
        (1 + Cl) * n * (cNear d L * Q1 d ^ 2) * v ^ 2 := by
    rw [hn]; field_simp; ring
  rw [hmain, hC₁]
  have hw2 : 0 ≤ w ^ 2 := sq_nonneg w
  have hA : 0 ≤ (1 + Cl) * n * (cNear d L * Q1 d ^ 2) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hw2 : v ^ 2 ≤ v ^ 2 + w ^ 2) hA]

set_option maxHeartbeats 1000000 in
/-- **Proposition `prop:W-contract`** (for `d ≥ 2`, with `L^d L^{-3}`): for translation-covariant
`𝒲` and a translation-invariant covariance,
`‖𝒲_{j+1}‖_{j+1} ≤ C₀ L^d L^{-3} w + C(L) (v² + w²)`, with `C₀` independent of `L`. -/
theorem W_contract (d : ℕ) (hd : 2 ≤ d) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ L₀ : ℕ,
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ C₁ : ℝ, 0 ≤ C₁ ∧
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ : ℝ, 0 < ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓ C → TInv C →
    ∀ V W : Fam d L N, InF j V → InF j W → (∀ b, ε (V b : Alg d L N) = 0) → FamCov j W →
    ∀ v w : ℝ, 0 ≤ v → 0 ≤ w → v ≤ 1 → w ≤ 1 →
      Fnorm j ℓ V ≤ ENNReal.ofReal v → Fnorm j ℓ W ≤ ENNReal.ofReal w →
      Fnorm (j + 1) ℓ (Wnext2 j C V W) ≤
        ENNReal.ofReal (C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3) * w + C₁ * (v ^ 2 + w ^ 2)) := by
  obtain ⟨C₀, hC₀, L₀, h⟩ := W_contract_ts d hd
  refine ⟨C₀, hC₀, L₀, fun L _ hL => ?_⟩
  obtain ⟨C₁, hC₁, h'⟩ := h L hL
  exact ⟨C₁, hC₁, fun N j hj ℓ hℓ C hC =>
    h' N j hj ℓ ℓ ℓ hℓ hℓ hℓ (by linarith) le_rfl C hC⟩

/-- **Proposition `prop:W-contract`** in `d = 2`: `‖𝒲_{j+1}‖ ≤ C₀ L^{-1} w + C(L)(v² + w²)`. -/
theorem W_contract_d2 : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ L₀ : ℕ,
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ C₁ : ℝ, 0 ≤ C₁ ∧
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ : ℝ, 0 < ℓ →
    ∀ C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ, GoodCov2 j ℓ C → TInv C →
    ∀ V W : Fam 2 L N, InF j V → InF j W → (∀ b, ε (V b : Alg 2 L N) = 0) → FamCov j W →
    ∀ v w : ℝ, 0 ≤ v → 0 ≤ w → v ≤ 1 → w ≤ 1 →
      Fnorm j ℓ V ≤ ENNReal.ofReal v → Fnorm j ℓ W ≤ ENNReal.ofReal w →
      Fnorm (j + 1) ℓ (Wnext2 j C V W) ≤
        ENNReal.ofReal (C₀ / L * w + C₁ * (v ^ 2 + w ^ 2)) := by
  obtain ⟨C₀, hC₀, L₀, h⟩ := W_contract 2 le_rfl
  refine ⟨C₀, hC₀, L₀, fun L _ hL => ?_⟩
  obtain ⟨C₁, hC₁, h'⟩ := h L hL
  refine ⟨C₁, hC₁, fun N j hj ℓ hℓ C hC hT V W hV hW hV0 hWc v w hv0 hw0 hv1 hw1 hVv hWw => ?_⟩
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have e : C₀ * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3) = C₀ / L := by field_simp
  rw [← e]
  exact h' N j hj ℓ hℓ C hC hT V W hV hW hV0 hWc v w hv0 hw0 hv1 hw1 hVv hWw

end

end Step2
