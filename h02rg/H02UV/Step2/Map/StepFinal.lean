import Step2.Map.Split

/-!
# The activity `K_{j+1}` after the change of variables (Expected result `thm:closure`(d))

`Kplus j C V W K = K_out` of Brydges–Slade (D.13) (`Step2.Kout`), at scale `j + 1`, with
`I = Ĩ_{j+1}` (`It`), `K_in = K^{pf}_{j+1}` (`Knext2`), `M = K^♯_{j+1}` (`Knew`) and
`J = Jh`. Then:

* `Kplus_union`: `K_{j+1}` factorises over non-touching polymers;
* `stepK_ZVK`: `𝔼_C θ Z_j = ∑_U I_{j+1}^{Λ∖U} e^{-u_{j+1}(U)} ∏_{Y ∈ Comp(U)} K_{j+1}(Y)`;
* `Kplus_split`: for connected `U`, `K_{j+1}(U) = K^♯_{j+1}(U) + E(U)` with `E` the sum over
  `Rset` (`Step2.Kout_sub_le` bounds it).
-/

namespace Step2

noncomputable section

open Finset Grassmann Loc FRD Step PolyAux

variable {d L N : ℕ} [NeZero L]

section Map

variable (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V W : Fam d L N) (K : Act d L N)

/-- **`K_{j+1}`**: the output of the change of variables (D.13). -/
def Kplus : Act d L N := Kout (j + 1) (It j C V W K) (Knew j C V W K) (Jh j C V)

theorem Knext2_empty : Knext2 j C V W K ∅ = 1 := by
  rw [Knext2, gKnext, Gset_empty, sum_singleton]
  simp only [uX, blocks, image_empty, sum_empty, Complex.exp_zero, one_smul, Xcal, biUnion_empty,
    union_empty, empty_sdiff, bpow, prod_empty, one_mul, gKchk, comp_empty, mul_one]
  exact Subtype.ext (by simp [ECCE, ECC_one])

theorem Kout_empty (k : ℕ) (I : (Fin d → ℕ) → EvR (Lam d L N)) (M : Act d L N)
    (J : (Fin d → ℕ) → Finset (Lam d L N) → EvR (Lam d L N)) : Kout k I M J ∅ = 1 := by
  classical
  have hF : (G0 (d := d) (L := L) (N := N) k).filter (fun g => g.2 ∪ Bbox k g.1 = ∅) = {(∅, ∅)} := by
    ext g
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hg, hgW⟩
      obtain ⟨-, h2, -, -, -⟩ := (mem_G0 k).1 hg
      have h2' := union_eq_empty.1 hgW
      refine Prod.ext ?_ h2'.1
      refine eq_empty_of_forall_notMem fun p hp => ?_
      obtain ⟨hb, -, -⟩ := mem_pairsU.1 (h2 hp)
      obtain ⟨x, hx⟩ := mem_blockIdx.1 hb
      have : x ∈ Bbox k g.1 := mem_biUnion.2 ⟨p, hp,
        subset_nbhd (isPolymer_blockSet k p.1) hx⟩
      rw [h2'.2] at this; exact notMem_empty x this
    · rintro rfl
      refine ⟨(mem_G0 k).2 ⟨isPolymer_empty k, empty_subset _, by simp, by simp, ?_⟩, ?_⟩
      · rintro ⟨x, hx, -⟩; simp [Xcal] at hx
      · show ∅ ∪ Bbox k ∅ = ∅; simp [Bbox]
  rw [Kout, hF, sum_singleton, Rterm]
  simp [Xcal, bpow, blocks, Kext_empty]

theorem Kext_eq_of_union (k : ℕ) (F : Act d L N) (h0 : F ∅ = 1)
    (hmul : ∀ A B, IsPolymer k A → IsPolymer k B → ¬ Touch A B → F (A ∪ B) = F A * F B)
    {U : Finset (Lam d L N)} (hU : IsPolymer k U) : Kext k F U = F U :=
  (eq_prod_comp_of_mul F h0 hmul hU).symm

theorem uX_union' {A B : Finset (Lam d L N)} (hA : IsPolymer j A) (hB : IsPolymer j B)
    (hD : Disjoint A B) : uX j C V W K (A ∪ B) = uX j C V W K A + uX j C V W K B := by
  rw [uX, uX, uX, blocks_union, sum_union (disjoint_blocks hA hB hD)]

end Map

section Props

variable {j : ℕ} {ℓ : ℝ} {C : Matrix (Lam d L N) (Lam d L N) ℂ} {V W : Fam d L N}
  {K : Act d L N}

theorem Kplus_union {U₁ U₂ : Finset (Lam d L N)} (hU₁ : IsPolymer (j + 1) U₁)
    (hU₂ : IsPolymer (j + 1) U₂) (h : ¬ Touch U₁ U₂) :
    Kplus j C V W K (U₁ ∪ U₂) = Kplus j C V W K U₁ * Kplus j C V W K U₂ :=
  Kout_union hU₁ hU₂ h _ _ _

theorem hKin (hd : 1 ≤ d) {c : Finset (Lam d L N)} (hc : IsConn (j + 1) c) :
    Knext2 j C V W K c = Knew j C V W K c +
      ∑ b ∈ blocks (j + 1) c, Jbar (j + 1) (It j C V W K) (Jh j C V) b c := by
  simp only [Jbar, bpow_It j C V W K hc.1, ← mul_sum, Jh_sum j C V hd hc, Knew]
  abel

/-- **`𝔼_C θ Z_j = Z_{j+1}` with the factorised activity `K_{j+1}`.** -/
theorem stepK_ZVK (hd : 1 ≤ d) (hL : 2 ^ (d + 2) ≤ L) (hjN : j + 1 < N) (hC : GoodCov2 j ℓ C)
    (hV : InF j V) (hW : InF j W) (hV0 : ∀ b, ε (V b : Alg d L N) = 0) (hK : InK2 j K) :
    ECCE C (thetaE (gZ j (Ib V W) K)) = ∑ U ∈ Pj (j + 1) univ,
      bpow j (Ip j C V W K) (univ \ U) *
        (Complex.exp (-uX j C V W K U) • Kext (j + 1) (Kplus j C V W K) U) := by
  classical
  have hJs : ∀ b c, ¬ IsSmall (j + 1) c → Jh j C V b c = 0 := fun b c hc => Jh_of_not_small j C V b hc
  have hfac : ∀ (F : Finset (Lam d L N) → EvR (Lam d L N)), ∀ U ∈ Pj (L := L) (N := N) (j + 1) univ,
      bpow j (Ip j C V W K) (univ \ U) * (Complex.exp (-uX j C V W K U) • F U) =
      Complex.exp (-uX j C V W K univ) • (bpow (j + 1) (It j C V W K) (univ \ U) * F U) := by
    intro F U hU
    have hUp := (mem_Pj.1 hU).2
    have hc : IsPolymer (j + 1) (univ \ U) := IsPolymer.sdiff (isPolymer_univ _) hUp
    rw [bpow_It j C V W K hc, bpow_Ip, smul_mul_assoc, mul_smul_comm, smul_smul,
      ← Complex.exp_add, ← neg_add, ← uX_union' j C V W K (IsPolymer.of_succ hc)
        (IsPolymer.of_succ hUp) sdiff_disjoint, sdiff_union_of_subset (subset_univ _)]
  rw [step2_ZVK]
  rw [sum_congr rfl fun U hU => hfac _ U hU, ← smul_sum]
  conv_rhs => rw [sum_congr rfl fun U hU => hfac _ U hU, ← smul_sum]
  congr 1
  have h1 : ∀ U ∈ Pj (L := L) (N := N) (j + 1) univ,
      Knext2 j C V W K U = Kext (j + 1) (Knext2 j C V W K) U := fun U hU =>
    (Kext_eq_of_union (j + 1) _ (Knext2_empty j C V W K)
      (fun A B hA hB h => Knext2_union hd hL hjN.le hA hB h hC hV hW hV0 hK)
      (mem_Pj.1 hU).2).symm
  have h2 : ∀ U ∈ Pj (L := L) (N := N) (j + 1) univ,
      Kext (j + 1) (Kplus j C V W K) U = Kplus j C V W K U := fun U hU =>
    Kext_eq_of_union (j + 1) _ (Kout_empty _ _ _ _)
      (fun A B hA hB h => Kplus_union hA hB h) (mem_Pj.1 hU).2
  calc ∑ U ∈ Pj (j + 1) univ, bpow (j + 1) (It j C V W K) (univ \ U) * Knext2 j C V W K U
      = ∑ U ∈ Pj (j + 1) univ, bpow (j + 1) (It j C V W K) (univ \ U) *
          Kext (j + 1) (Knext2 j C V W K) U := sum_congr rfl fun U hU => by rw [← h1 U hU]
    _ = ∑ U ∈ Pj (j + 1) univ, bpow (j + 1) (It j C V W K) (univ \ U) *
          Kout (j + 1) (It j C V W K) (Knew j C V W K) (Jh j C V) U :=
        reblock_ZVK hJs _ fun c hc => hKin hd hc
    _ = _ := sum_congr rfl fun U hU => by rw [h2 U hU]; rfl

end Props

/-! ### Bounds on the data of the change of variables -/

namespace BH

variable {j : ℕ} {ℓ ℓ' ℓC : ℝ} {C : Matrix (Lam d L N) (Lam d L N) ℂ} {V W : Fam d L N}
  {K : Act d L N} {A r Cl cS : ℝ} (H : BH j ℓ ℓ' ℓC C V W K A r Cl cS) {v : ℝ} (hv0 : 0 ≤ v)
  (hv : ∀ b ∈ blockIdx (L := L) (N := N) j, Tj d (L : ℝ) j ℓ (V b : Alg d L N) ≤ ENNReal.ofReal v)
include H hv0 hv

theorem kap_le (X : Finset (Lam d L N)) (c : Fin d → ℕ) :
    Tj d (L : ℝ) (j + 1) ℓ' (kap j C V X c : Alg d L N) ≤
      ENNReal.ofReal ((cNear d L + 2) * (2 * (Q1 d * v) ^ 2)) := by
  classical
  have hq : 0 ≤ 2 * (Q1 d * v) ^ 2 := by positivity
  have hN := H.hcNear
  have hb : ∀ b ∈ blocks j X, b ∈ blockIdx (L := L) (N := N) j :=
    fun b hb => mem_blockIdx_of_mem_blocks hb
  unfold kap
  split_ifs with h1 h2
  · refine (tn_sum_const (E := Dir d) (p := pPhi d) _ _
      (r := (cNear d L + 1) * (2 * (Q1 d * v) ^ 2)) (by positivity) fun b hbX => ?_).trans
      (ENNReal.ofReal_le_ofReal ?_)
    · have hbX' := (mem_filter.1 hbX).1
      rw [Subalgebra.coe_smul, tNorm_smul, FCE_sub_right, FCE_VprL_eq H.hjN H.hC H.hV b]
      have hs := tn_sum_const (E := Dir d) (p := pPhi d) (h := (L : ℝ) ^ (j + 1)) (ℓ := ℓ')
        (nearSet (L := L) (N := N) j b) (fun b' => FCE C (Vpr C V b) (Vpr C V b'))
        (r := 2 * (Q1 d * v) ^ 2) hq
        (fun b' hb' => H.FCE_pair_le' hv0 hv (hb b hbX') (mem_filter.1 hb').1)
      have hn : ((nearSet (L := L) (N := N) j b).card : ℝ) ≤ cNear d L := by
        unfold cNear; exact_mod_cast card_nearSet_le H.hj.le b (hb b hbX')
      have hsub := tn_subE (by positivity) hq hs (H.FCE_pair_le' hv0 hv (hb b hbX') (hb b hbX'))
      refine (mul_le_mul_left' hsub _).trans ?_
      rw [← ENNReal.ofReal_mul (norm_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      have : ‖-(1 / 2 : ℂ)‖ = 1 / 2 := by simp
      rw [this]
      nlinarith
    · have hc1 : (((blocks j X).filter (fun b => par L b = c)).card : ℝ) ≤ 1 := by
        have := card_le_card (filter_subset (fun b => par L b = c) (blocks j X))
        have h1' : (blocks j X).card = 1 := h1
        exact_mod_cast this.trans h1'.le
      have h0 : 0 ≤ (cNear d L + 1) * (2 * (Q1 d * v) ^ 2) := by positivity
      nlinarith
  · rw [Subalgebra.coe_smul, Tj_smul']
    have hs : Tj d (L : ℝ) (j + 1) ℓ' ((∑ b ∈ (blocks j X).filter (fun b => par L b = c),
        ∑ b' ∈ (blocks j X).erase b, FCE C (Vpr C V b) (Vpr C V b') : EvR (Lam d L N)) :
          Alg d L N) ≤
        ENNReal.ofReal (((blocks j X).filter (fun b => par L b = c)).card *
          (((blocks j X).card - 1 : ℕ) * (2 * (Q1 d * v) ^ 2))) := by
      refine tn_sum_const (E := Dir d) (p := pPhi d) _ _ (by positivity) fun b hbX => ?_
      have hbX' := (mem_filter.1 hbX).1
      have := tn_sum_const (E := Dir d) (p := pPhi d) (h := (L : ℝ) ^ (j + 1)) (ℓ := ℓ')
        ((blocks j X).erase b) (fun b' => FCE C (Vpr C V b) (Vpr C V b')) hq
        (fun b' hb' => H.FCE_pair_le' hv0 hv (hb b hbX') (hb b' (mem_of_mem_erase hb')))
      rwa [card_erase_of_mem hbX'] at this
    refine (mul_le_mul_left' hs _).trans ?_
    rw [← ENNReal.ofReal_mul (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    have h2' : (blocks j X).card = 2 := h2
    have hc2 : (((blocks j X).filter (fun b => par L b = c)).card : ℝ) ≤ 2 := by
      have := card_le_card (filter_subset (fun b => par L b = c) (blocks j X))
      exact_mod_cast this.trans h2'.le
    rw [this, h2']
    norm_num
    nlinarith
  · rw [ZeroMemClass.coe_zero, Step.Tj_zero (d := d) (L : ℝ) (j + 1) ℓ']; exact zero_le

theorem Jh_le (c : Fin d → ℕ) {U : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U) :
    Tj d (L : ℝ) (j + 1) ℓ' (Jh j C V c U : Alg d L N) ≤
      ENNReal.ofReal (2 ^ nb j U * ((cNear d L + 2) * (2 * (Q1 d * v) ^ 2))) := by
  classical
  have hN := H.hcNear
  unfold Jh
  split_ifs
  · refine (tn_sum_const (E := Dir d) (p := pPhi d) _ _ (by positivity)
      fun X _ => H.kap_le hv0 hv X c).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (card_K2_filter_le j hU) (by positivity)
  · rw [ZeroMemClass.coe_zero, Step.Tj_zero (d := d) (L : ℝ) (j + 1) ℓ']; exact zero_le

end BH

/-- `‖Ĩ_{j+1}(B_+)‖ ≤ 2`. -/
theorem BH.It_le {j : ℕ} {ℓ ℓ' ℓC : ℝ} {C : Matrix (Lam d L N) (Lam d L N) ℂ} {V W : Fam d L N}
    {K : Act d L N} {A r Cl cS : ℝ} (H : BH j ℓ ℓ' ℓC C V W K A r Cl cS)
    (hu : cUblk d L Cl cS * r ≤ 1 / 4) (hw : cWblk d L Cl * r ≤ 1)
    (hsmall : (L : ℝ) ^ d * ((8 * cUblk d L Cl cS + cWblk d L Cl) * r) * 2 ^ (L ^ d) ≤ 1)
    (c : Fin d → ℕ) :
    Tj d (L : ℝ) (j + 1) ℓ' (It j C V W K c : Alg d L N) ≤ ENNReal.ofReal 2 := by
  have hr := H.hr
  set δ := (8 * cUblk d L Cl cS + cWblk d L Cl) * r with hδ
  have hδ0 : 0 ≤ δ := by have := H.hcU; have := H.hcW; positivity
  have hδ1 : δ ≤ 1 := by
    have h1 : (1 : ℝ) ≤ (L : ℝ) ^ d := one_le_pow₀ (by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
    have h2 : (1 : ℝ) ≤ 2 ^ (L ^ d) := one_le_pow₀ (by norm_num)
    nlinarith [mul_le_mul h1 h2 zero_le_one (by positivity)]
  have hP := tn_prod_sub_one (E := Dir d) (p := pPhi d) H.hh' H.hℓ'
    (blocks j (blockSet (L := L) (N := N) (j + 1) c)) (Gp j C V W K) hδ0
    (fun b hb => H.Gp_sub_one_le hu hw (mem_blockIdx_of_mem_blocks hb))
  have hn : (blocks j (blockSet (L := L) (N := N) (j + 1) c)).card ≤ L ^ d :=
    nb_blockSet_succ_le j c
  have h1 := one_add_pow_sub_one_le hδ0 (blocks j (blockSet (L := L) (N := N) (j + 1) c)).card
  have h2 : (1 + δ) ^ (blocks j (blockSet (L := L) (N := N) (j + 1) c)).card ≤ 2 ^ (L ^ d) :=
    (pow_le_pow_left₀ (by linarith) (by linarith) _).trans (pow_le_pow_right₀ (by norm_num) hn)
  have hn' : ((blocks j (blockSet (L := L) (N := N) (j + 1) c)).card : ℝ) ≤ (L : ℝ) ^ d := by
    exact_mod_cast hn
  have h3 : (1 + δ) ^ (blocks j (blockSet (L := L) (N := N) (j + 1) c)).card - 1 ≤ 1 := by
    refine h1.trans ?_
    calc ((blocks j (blockSet (L := L) (N := N) (j + 1) c)).card : ℝ) * δ *
          (1 + δ) ^ (blocks j (blockSet (L := L) (N := N) (j + 1) c)).card
        ≤ (L : ℝ) ^ d * δ * 2 ^ (L ^ d) := by gcongr
      _ ≤ 1 := hsmall
  have e : It j C V W K c = 1 + (bpow j (Gp j C V W K) (blockSet (j + 1) c) - 1) := by
    rw [It]; abel
  rw [e]
  have h4 : 0 ≤ (1 + δ) ^ (blocks j (blockSet (L := L) (N := N) (j + 1) c)).card - 1 := by
    have := one_le_pow₀ (M₀ := ℝ) (n := (blocks j (blockSet (L := L) (N := N) (j + 1) c)).card)
      (by linarith : (1 : ℝ) ≤ 1 + δ)
    linarith
  refine (tn_addE zero_le_one h4 (by
    rw [OneMemClass.coe_one, ENNReal.ofReal_one]; exact tNorm_one_le H.hh' H.hℓ') hP).trans
    (ENNReal.ofReal_le_ofReal (by linarith))

/-! ### The step estimate for the factorised activity -/

theorem wnorm_mono_A {k : ℕ} {ℓ A lam : ℝ} (hA : 0 ≤ A) (hlam : 1 ≤ lam) (U : Finset (Lam d L N))
    (F : EvR (Lam d L N)) : wnorm k ℓ A U F ≤ wnorm k ℓ (lam * A) U F := by
  unfold wnorm
  gcongr
  nlinarith

set_option maxHeartbeats 2000000 in
/-- **Theorem `stepK`** with input weight `A` and output weight `μA`, `μ ≥ 1` (the slack for
`K♭`), and two field scales. -/
theorem stepK_tsW (d : ℕ) (hd : 2 ≤ d) : ∃ (C₀ η : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧ 0 < η ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∀ μ : ℝ, 1 ≤ μ → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓC C →
    ∀ (V W : Fam d L N) (K : Act d L N), InF j V → InF j W → (∀ b, ε (V b : Alg d L N) = 0) →
      InK2 j K → ∀ g : ℝ, 0 ≤ g → g ≤ ε₀ →
      Fnorm j ℓ V ≤ ENNReal.ofReal g → Fnorm j ℓ W ≤ ENNReal.ofReal (g ^ 2) →
      Knorm j ℓ A K ≤ ENNReal.ofReal ε₀ →
      ∀ U : Finset (Lam d L N), IsConn (j + 1) U →
        wnorm (j + 1) ℓ' (μ * A) U (Kplus j C V W K U) ≤
          ENNReal.ofReal (C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3 + A ^ (-η))) * Knorm j ℓ A K +
          ENNReal.ofReal C₁ * (ENNReal.ofReal (g ^ 3) + ENNReal.ofReal g * Knorm j ℓ A K +
            Knorm j ℓ A K ^ 2) := by
  classical
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Cl, hCl0, hloc⟩ := exists_Loc2sXY_bound d hd1
  obtain ⟨c, hc⟩ := card_small_containing d
  set lam : ℝ := 2 * (2 : ℝ) ^ (1 + c) with hlamdef
  have hlam1 : 1 ≤ lam := by
    have : (1 : ℝ) ≤ 2 ^ (1 + c) := one_le_pow₀ (by norm_num)
    rw [hlamdef]; linarith
  obtain ⟨C₀, η, L₃, hC₀, hη, h3⟩ := step3L d hd
  refine ⟨C₀, η, max L₃ (max (2 ^ (d + 3) + 8 * d + 1) ⌈pauliL0 d⌉₊), hC₀, hη, ?_⟩
  intro L _ hL μ hμ1'
  have hL3 : L₃ ≤ L := le_trans (le_max_left _ _) hL
  have hL8 : 2 ^ (d + 3) + 8 * d < L :=
    lt_of_lt_of_le (Nat.lt_succ_self _) (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL)
  have hLp : pauliL0 d ≤ L := (Nat.le_ceil _).trans
    (by exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL)
  have hL2 : 2 ^ (d + 2) ≤ L := by
    have : 2 ^ (d + 2) ≤ 2 ^ (d + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  obtain ⟨A₀, hA₀, h3'⟩ := h3 L hL3 (lam * μ) (by nlinarith)
  refine ⟨A₀, hA₀, fun A hA => ?_⟩
  have hA1 : 1 ≤ A := hA₀.trans hA
  have hA0 : 0 < A := by linarith
  have hμA1 : 1 ≤ μ * A := by nlinarith
  have hμA0 : 0 < μ * A := by linarith
  obtain ⟨ε₃, C₃, hε₃, hC₃, h3''⟩ := h3' A hA
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
  set n₀ : ℝ := (L : ℝ) ^ d with hn₀
  have hn₀0 : 0 ≤ n₀ := by positivity
  set cB : ℕ := (2 ^ (d + 1) + 3) ^ d
  set a : ℝ := 2 * (2 : ℝ) ^ (1 + c) * (μ * A) with ha
  have ha0 : 0 ≤ a := by positivity
  set X1 : ℝ := a ^ cB with hX1
  have hX10 : 0 ≤ X1 := by positivity
  have hN0 : 0 ≤ cNear d L := Nat.cast_nonneg _
  have hQ := one_le_Q1 hd1
  set Cδ : ℝ := (2 : ℝ) ^ (2 ^ d) * (2 : ℝ) ^ (L ^ d * 2 ^ d) * ((cNear d L + 2) * (2 * Q1 d ^ 2))
    with hCδ
  have hCδ0 : 0 ≤ Cδ := by positivity
  set C0' : ℝ := C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3 + A ^ (-η)) with hC0'
  have hC0'0 : 0 ≤ C0' := by positivity
  set Λ2 : ℝ := (lam * (μ * A)) ^ 2 ^ d with hΛ2
  have hΛ20 : 0 ≤ Λ2 := by positivity
  set Cμ : ℝ := C0' + 3 * C₃ with hCμ
  have hCμ0 : 0 ≤ Cμ := by positivity
  set Cx : ℝ := X1 ^ 2 * Cδ ^ 2 + X1 * Cδ * Λ2 * (C0' + C₃) with hCx
  have hCx0 : 0 ≤ Cx := by positivity
  set ε₀ : ℝ := min ε₃ (min 1 (min (1 / (4 * cu + 1)) (min (1 / (cw + 1))
    (min (1 / (n₀ * δc * 2 ^ (L ^ d) + 1)) (min (1 / (X1 * Cδ + 1)) (1 / (Cμ * Λ2 + 1)))))))
    with hε₀
  have hε₀0 : 0 < ε₀ := lt_min hε₃ (lt_min one_pos (lt_min (by positivity)
    (lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity) (by positivity))))))
  refine ⟨ε₀, C₃ + Cx, hε₀0, by positivity, ?_⟩
  intro N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC V W K hV hW hV0 hK g hg0 hgε hVg hWg hKε U hU
  have e1 : ε₀ ≤ ε₃ := min_le_left _ _
  have e2 : ε₀ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have e3 : ε₀ ≤ 1 / (4 * cu + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have e4 : ε₀ ≤ 1 / (cw + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have e5 : ε₀ ≤ 1 / (n₀ * δc * 2 ^ (L ^ d) + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have e6 : ε₀ ≤ 1 / (X1 * Cδ + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have e7 : ε₀ ≤ 1 / (Cμ * Λ2 + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
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
  have hk1 : k ≤ 1 := hkε.trans e2
  have hgr : g ≤ r := le_max_left _ _
  have hkr : k ≤ r := le_max_right _ _
  have hVb : ∀ b ∈ blockIdx (L := L) (N := N) j, Tj d (L : ℝ) j ℓ (V b : Alg d L N) ≤
      ENNReal.ofReal g := fun b hb => (le_iSup₂ (f := fun b (_ : b ∈ blockIdx (L := L) (N := N) j) =>
        Tj d (L : ℝ) j ℓ (V b : Alg d L N)) b hb).trans hVg
  have H : BH j ℓ ℓ' ℓC C V W K A r Cl cS :=
    { hd := hd1, hLp := hLp, hL8 := hL8, hjN := hjN, hℓ := hℓ, hℓ' := hℓ', hℓC := hℓC, hsum := hsum, hC := hC, hV := hV, hW := hW,
      hV0 := hV0, hK := hK, hA := hA1, hr := hr0, hr1 := hr1
      hVr := fun b hb => (hVb b hb).trans (ENNReal.ofReal_le_ofReal hgr)
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
  have hIt : ∀ c' : Fin d → ℕ, Tj d (L : ℝ) (j + 1) ℓ' (It j C V W K c' : Alg d L N) ≤
      ENNReal.ofReal 2 := fun c' => H.It_le hu hw (by
    have := le_one_of_le_div (x := n₀ * δc * 2 ^ (L ^ d)) (by positivity) (by positivity)
      (hrε.trans e5) (by linarith)
    calc (L : ℝ) ^ d * (δc * r) * 2 ^ (L ^ d) = n₀ * δc * 2 ^ (L ^ d) * r := by ring
      _ ≤ 1 := this) c'
  -- the second-order data
  set δ : ℝ := Cδ * g ^ 2 with hδdef
  have hδ0 : 0 ≤ δ := by positivity
  have hJb : ∀ p ∈ pairsU (L := L) (N := N) (j + 1),
      Tj d (L : ℝ) (j + 1) ℓ' (Jbar (j + 1) (It j C V W K) (Jh j C V) p.1 p.2 : Alg d L N) ≤
        ENNReal.ofReal δ := by
    intro p hp
    obtain ⟨-, hs, -⟩ := mem_pairsU.1 hp
    have hb1 : Tj d (L : ℝ) (j + 1) ℓ' (bpow (j + 1) (It j C V W K) p.2 : Alg d L N) ≤
        ENNReal.ofReal (2 ^ (2 ^ d)) := by
      have := tn_prodE (E := Dir d) (p := pPhi d) H.hh' hℓ' (blocks (j + 1) p.2) (It j C V W K)
        (fun _ => 2) (fun _ _ => by norm_num) (fun c' _ => hIt c')
      rw [prod_const] at this
      exact this.trans (ENNReal.ofReal_le_ofReal (pow_le_pow_right₀ (by norm_num) hs.2.2))
    have hnb : nb j p.2 ≤ L ^ d * 2 ^ d :=
      (nb_le_of_succ hs.1).trans (Nat.mul_le_mul_left _ hs.2.2)
    have hb2 := H.Jh_le hg0 hVb p.1 hs.1
    have hb2' : Tj d (L : ℝ) (j + 1) ℓ' (Jh j C V p.1 p.2 : Alg d L N) ≤
        ENNReal.ofReal ((2 : ℝ) ^ (L ^ d * 2 ^ d) * ((cNear d L + 2) * (2 * (Q1 d * g) ^ 2))) :=
      hb2.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hnb) (by positivity)))
    refine (tn_mulE H.hh' hℓ' (by positivity) hb1 hb2').trans (ENNReal.ofReal_le_ofReal
      (le_of_eq ?_))
    rw [hδdef, hCδ]; ring
  -- the bound on `M = K^♯`
  set μ' : ℝ := C0' * k + C₃ * (g ^ 3 + g * k + k ^ 2) with hμdef
  have hμ0 : 0 ≤ μ' := by positivity
  have hM : ∀ Y, IsConn (j + 1) Y → ENNReal.ofReal ((lam * (μ * A)) ^ (nb (j + 1) Y - 2 ^ d)) *
      Tj d (L : ℝ) (j + 1) ℓ' (Knew j C V W K Y : Alg d L N) ≤ ENNReal.ofReal μ' := by
    intro Y hY
    have := h3'' N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC V W K hV hW hV0 hK g hg0 (hgε.trans e1) hVg hWg
      (hKε.trans (ENNReal.ofReal_le_ofReal e1)) Y hY
    rw [show lam * (μ * A) = lam * μ * A by ring]
    refine this.trans (le_of_eq ?_)
    rw [hKk, hμdef, ← ENNReal.ofReal_mul hC0'0, ← ENNReal.ofReal_mul hg0, ← ENNReal.ofReal_pow hk0,
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul hC₃,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
  -- smallness
  have hδ1 : (2 * (2 : ℝ) ^ (1 + c) * (μ * A)) ^ ((2 ^ (d + 1) + 3) ^ d) * δ ≤ 1 := by
    have h := le_one_of_le_div (x := X1 * Cδ) (by positivity) (by positivity) (hgε.trans e6)
      (by linarith)
    have hg2 : g ^ 2 ≤ g := by nlinarith
    calc (2 * (2 : ℝ) ^ (1 + c) * (μ * A)) ^ ((2 ^ (d + 1) + 3) ^ d) * δ = X1 * Cδ * g ^ 2 := by
          rw [hX1, ha, hδdef]; ring
      _ ≤ X1 * Cδ * g := by gcongr
      _ ≤ 1 := h
  have hμ1 : μ' * (lam * (μ * A)) ^ 2 ^ d ≤ 1 := by
    have h := le_one_of_le_div (x := Cμ * Λ2) (by positivity) (by positivity) (hrε.trans e7)
      (by linarith)
    have hμr : μ' ≤ Cμ * r := by
      have h1 : k ≤ r := hkr
      have h2 : g ^ 3 + g * k + k ^ 2 ≤ 3 * r := by
        have i1 : g ^ 3 ≤ r := (pow_le_of_le_one hg0 hg1 (by norm_num)).trans hgr
        have i2 : g * k ≤ r := (mul_le_of_le_one_left hk0 hg1).trans hkr
        have i3 : k ^ 2 ≤ r := (pow_le_of_le_one hk0 hk1 (by norm_num)).trans hkr
        linarith
      calc μ' = C0' * k + C₃ * (g ^ 3 + g * k + k ^ 2) := rfl
        _ ≤ C0' * r + C₃ * (3 * r) := by gcongr
        _ = Cμ * r := by rw [hCμ]; ring
    calc μ' * (lam * (μ * A)) ^ 2 ^ d = μ' * Λ2 := rfl
      _ ≤ Cμ * r * Λ2 := by gcongr
      _ = Cμ * Λ2 * r := by ring
      _ ≤ 1 := h
  -- the decomposition
  have hJ0 : ∀ b ∈ blockIdx (L := L) (N := N) (j + 1),
      ∑ U ∈ (smallSets (d := d) (L := L) (N := N) (j + 1)).filter
        (fun U => blockSet (j + 1) b ⊆ U), Jh j C V b U = 0 :=
    fun b _ => Jh_sum_U hd1 hL2 hjN hC hV b
  have hsplit := Kout_split (I := It j C V W K) (M := Knew j C V W K) hJ0 hU
  have hE := Kout_sub_le (k := j + 1) (I := It j C V W K) (M := Knew j C V W K)
    (J := Jh j C V) hjN.le H.hh' hℓ' hμA1 hlam1 hδ0 hμ0
    (fun b hb => by convert hc L N (j + 1) b hb) le_rfl (fun b _ => hIt b) hJb hM hδ1 hμ1 hU.1
  have hKplus : Kplus j C V W K U = Knew j C V W K U +
      ∑ g ∈ Rset (j + 1) U, Rterm (j + 1) (It j C V W K) (Knew j C V W K) (Jh j C V) U g := hsplit
  rw [hKplus]
  refine (wnorm_add_le' _ _ _ _ _ _).trans ?_
  have hS3 := h3'' N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC V W K hV hW hV0 hK g hg0 (hgε.trans e1) hVg hWg
    (hKε.trans (ENNReal.ofReal_le_ofReal e1)) U hU
  have hmono := wnorm_mono_A (k := j + 1) (ℓ := ℓ') hμA0.le hlam1 U (Knew j C V W K U)
  rw [show lam * (μ * A) = lam * μ * A by ring] at hmono
  refine (add_le_add (hmono.trans hS3) hE).trans ?_
  -- the real inequality for the correction
  have hX1' : (2 * (2 : ℝ) ^ (1 + c) * (μ * A)) ^ ((2 ^ (d + 1) + 3) ^ d) = X1 := by rw [hX1, ha]
  rw [hX1']
  have hcorr : X1 * δ * (X1 * δ + μ' * (lam * (μ * A)) ^ 2 ^ d) ≤ Cx * (g ^ 3 + g * k + k ^ 2) := by
    have hg4 : g ^ 4 ≤ g ^ 3 := pow_le_pow_of_le_one hg0 hg1 (by norm_num)
    have hg2 : g ^ 2 ≤ g := pow_le_of_le_one hg0 hg1 (by norm_num)
    have hg21 : g ^ 2 ≤ 1 := hg2.trans hg1
    have hy : 0 ≤ g ^ 3 + g * k + k ^ 2 := by positivity
    have hgk0 : 0 ≤ g * k := mul_nonneg hg0 hk0
    have hk20 : 0 ≤ k ^ 2 := sq_nonneg k
    have hg30 : 0 ≤ g ^ 3 := pow_nonneg hg0 3
    have hgμ : g ^ 2 * μ' ≤ C0' * (g * k) + C₃ * (g ^ 3 + g * k + k ^ 2) := by
      have h1 : g ^ 2 * (C0' * k) ≤ C0' * (g * k) :=
        calc g ^ 2 * (C0' * k) ≤ g * (C0' * k) :=
              mul_le_mul_of_nonneg_right hg2 (by positivity)
          _ = C0' * (g * k) := by ring
      have h2 : g ^ 2 * (C₃ * (g ^ 3 + g * k + k ^ 2)) ≤ C₃ * (g ^ 3 + g * k + k ^ 2) :=
        mul_le_of_le_one_left (by positivity) hg21
      have e : g ^ 2 * μ' = g ^ 2 * (C0' * k) + g ^ 2 * (C₃ * (g ^ 3 + g * k + k ^ 2)) := by
        rw [hμdef]; ring
      rw [e]; linarith
    have e : X1 * δ * (X1 * δ + μ' * (lam * (μ * A)) ^ 2 ^ d) =
        X1 ^ 2 * Cδ ^ 2 * g ^ 4 + X1 * Cδ * Λ2 * (g ^ 2 * μ') := by
      rw [hδdef, hΛ2]; ring
    rw [e, hCx]
    have h1 : X1 ^ 2 * Cδ ^ 2 * g ^ 4 ≤ X1 ^ 2 * Cδ ^ 2 * (g ^ 3 + g * k + k ^ 2) := by
      have : g ^ 4 ≤ g ^ 3 + g * k + k ^ 2 := by linarith
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have h2 : X1 * Cδ * Λ2 * (g ^ 2 * μ') ≤
        X1 * Cδ * Λ2 * ((C0' + C₃) * (g ^ 3 + g * k + k ^ 2)) := by
      have hgk : C0' * (g * k) ≤ C0' * (g ^ 3 + g * k + k ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hC0'0
      have : g ^ 2 * μ' ≤ (C0' + C₃) * (g ^ 3 + g * k + k ^ 2) := by
        have e2 : (C0' + C₃) * (g ^ 3 + g * k + k ^ 2) =
            C0' * (g ^ 3 + g * k + k ^ 2) + C₃ * (g ^ 3 + g * k + k ^ 2) := by ring
        rw [e2]; linarith
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have e3 : (X1 ^ 2 * Cδ ^ 2 + X1 * Cδ * Λ2 * (C0' + C₃)) * (g ^ 3 + g * k + k ^ 2) =
        X1 ^ 2 * Cδ ^ 2 * (g ^ 3 + g * k + k ^ 2) +
          X1 * Cδ * Λ2 * ((C0' + C₃) * (g ^ 3 + g * k + k ^ 2)) := by ring
    rw [e3]; linarith
  rw [hKk]
  have hY : ENNReal.ofReal (g ^ 3) + ENNReal.ofReal g * ENNReal.ofReal k + ENNReal.ofReal k ^ 2 =
      ENNReal.ofReal (g ^ 3 + g * k + k ^ 2) := by
    rw [← ENNReal.ofReal_mul hg0, ← ENNReal.ofReal_pow hk0,
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
  rw [hY, add_assoc]
  refine add_le_add le_rfl ?_
  rw [← ENNReal.ofReal_mul hC₃, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have e4 : (C₃ + Cx) * (g ^ 3 + g * k + k ^ 2) =
      C₃ * (g ^ 3 + g * k + k ^ 2) + Cx * (g ^ 3 + g * k + k ^ 2) := by ring
  rw [e4]; linarith

set_option maxHeartbeats 2000000 in
/-- **Theorem `stepK`**: the third-order estimate for the factorised `K_{j+1}`. -/
theorem stepK_ts (d : ℕ) (hd : 2 ≤ d) : ∃ (C₀ η : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧ 0 < η ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓC C →
    ∀ (V W : Fam d L N) (K : Act d L N), InF j V → InF j W → (∀ b, ε (V b : Alg d L N) = 0) →
      InK2 j K → ∀ g : ℝ, 0 ≤ g → g ≤ ε₀ →
      Fnorm j ℓ V ≤ ENNReal.ofReal g → Fnorm j ℓ W ≤ ENNReal.ofReal (g ^ 2) →
      Knorm j ℓ A K ≤ ENNReal.ofReal ε₀ →
      ∀ U : Finset (Lam d L N), IsConn (j + 1) U →
        wnorm (j + 1) ℓ' A U (Kplus j C V W K U) ≤
          ENNReal.ofReal (C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3 + A ^ (-η))) * Knorm j ℓ A K +
          ENNReal.ofReal C₁ * (ENNReal.ofReal (g ^ 3) + ENNReal.ofReal g * Knorm j ℓ A K +
            Knorm j ℓ A K ^ 2) := by
  classical
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Cl, hCl0, hloc⟩ := exists_Loc2sXY_bound d hd1
  obtain ⟨c, hc⟩ := card_small_containing d
  set lam : ℝ := 2 * (2 : ℝ) ^ (1 + c) with hlamdef
  have hlam1 : 1 ≤ lam := by
    have : (1 : ℝ) ≤ 2 ^ (1 + c) := one_le_pow₀ (by norm_num)
    rw [hlamdef]; linarith
  obtain ⟨C₀, η, L₃, hC₀, hη, h3⟩ := step3L d hd
  refine ⟨C₀, η, max L₃ (max (2 ^ (d + 3) + 8 * d + 1) ⌈pauliL0 d⌉₊), hC₀, hη, ?_⟩
  intro L _ hL
  have hL3 : L₃ ≤ L := le_trans (le_max_left _ _) hL
  have hL8 : 2 ^ (d + 3) + 8 * d < L :=
    lt_of_lt_of_le (Nat.lt_succ_self _) (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL)
  have hLp : pauliL0 d ≤ L := (Nat.le_ceil _).trans
    (by exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL)
  have hL2 : 2 ^ (d + 2) ≤ L := by
    have : 2 ^ (d + 2) ≤ 2 ^ (d + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  obtain ⟨A₀, hA₀, h3'⟩ := h3 L hL3 lam hlam1
  refine ⟨A₀, hA₀, fun A hA => ?_⟩
  have hA1 : 1 ≤ A := hA₀.trans hA
  have hA0 : 0 < A := by linarith
  obtain ⟨ε₃, C₃, hε₃, hC₃, h3''⟩ := h3' A hA
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
  set n₀ : ℝ := (L : ℝ) ^ d with hn₀
  have hn₀0 : 0 ≤ n₀ := by positivity
  set cB : ℕ := (2 ^ (d + 1) + 3) ^ d
  set a : ℝ := 2 * (2 : ℝ) ^ (1 + c) * A with ha
  have ha0 : 0 ≤ a := by positivity
  set X1 : ℝ := a ^ cB with hX1
  have hX10 : 0 ≤ X1 := by positivity
  have hN0 : 0 ≤ cNear d L := Nat.cast_nonneg _
  have hQ := one_le_Q1 hd1
  set Cδ : ℝ := (2 : ℝ) ^ (2 ^ d) * (2 : ℝ) ^ (L ^ d * 2 ^ d) * ((cNear d L + 2) * (2 * Q1 d ^ 2))
    with hCδ
  have hCδ0 : 0 ≤ Cδ := by positivity
  set C0' : ℝ := C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3 + A ^ (-η)) with hC0'
  have hC0'0 : 0 ≤ C0' := by positivity
  set Λ2 : ℝ := (lam * A) ^ 2 ^ d with hΛ2
  have hΛ20 : 0 ≤ Λ2 := by positivity
  set Cμ : ℝ := C0' + 3 * C₃ with hCμ
  have hCμ0 : 0 ≤ Cμ := by positivity
  set Cx : ℝ := X1 ^ 2 * Cδ ^ 2 + X1 * Cδ * Λ2 * (C0' + C₃) with hCx
  have hCx0 : 0 ≤ Cx := by positivity
  set ε₀ : ℝ := min ε₃ (min 1 (min (1 / (4 * cu + 1)) (min (1 / (cw + 1))
    (min (1 / (n₀ * δc * 2 ^ (L ^ d) + 1)) (min (1 / (X1 * Cδ + 1)) (1 / (Cμ * Λ2 + 1)))))))
    with hε₀
  have hε₀0 : 0 < ε₀ := lt_min hε₃ (lt_min one_pos (lt_min (by positivity)
    (lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity) (by positivity))))))
  refine ⟨ε₀, C₃ + Cx, hε₀0, by positivity, ?_⟩
  intro N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC V W K hV hW hV0 hK g hg0 hgε hVg hWg hKε U hU
  have e1 : ε₀ ≤ ε₃ := min_le_left _ _
  have e2 : ε₀ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have e3 : ε₀ ≤ 1 / (4 * cu + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have e4 : ε₀ ≤ 1 / (cw + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have e5 : ε₀ ≤ 1 / (n₀ * δc * 2 ^ (L ^ d) + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have e6 : ε₀ ≤ 1 / (X1 * Cδ + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have e7 : ε₀ ≤ 1 / (Cμ * Λ2 + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
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
  have hk1 : k ≤ 1 := hkε.trans e2
  have hgr : g ≤ r := le_max_left _ _
  have hkr : k ≤ r := le_max_right _ _
  have hVb : ∀ b ∈ blockIdx (L := L) (N := N) j, Tj d (L : ℝ) j ℓ (V b : Alg d L N) ≤
      ENNReal.ofReal g := fun b hb => (le_iSup₂ (f := fun b (_ : b ∈ blockIdx (L := L) (N := N) j) =>
        Tj d (L : ℝ) j ℓ (V b : Alg d L N)) b hb).trans hVg
  have H : BH j ℓ ℓ' ℓC C V W K A r Cl cS :=
    { hd := hd1, hLp := hLp, hL8 := hL8, hjN := hjN, hℓ := hℓ, hℓ' := hℓ', hℓC := hℓC, hsum := hsum, hC := hC, hV := hV, hW := hW,
      hV0 := hV0, hK := hK, hA := hA1, hr := hr0, hr1 := hr1
      hVr := fun b hb => (hVb b hb).trans (ENNReal.ofReal_le_ofReal hgr)
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
  have hIt : ∀ c' : Fin d → ℕ, Tj d (L : ℝ) (j + 1) ℓ' (It j C V W K c' : Alg d L N) ≤
      ENNReal.ofReal 2 := fun c' => H.It_le hu hw (by
    have := le_one_of_le_div (x := n₀ * δc * 2 ^ (L ^ d)) (by positivity) (by positivity)
      (hrε.trans e5) (by linarith)
    calc (L : ℝ) ^ d * (δc * r) * 2 ^ (L ^ d) = n₀ * δc * 2 ^ (L ^ d) * r := by ring
      _ ≤ 1 := this) c'
  -- the second-order data
  set δ : ℝ := Cδ * g ^ 2 with hδdef
  have hδ0 : 0 ≤ δ := by positivity
  have hJb : ∀ p ∈ pairsU (L := L) (N := N) (j + 1),
      Tj d (L : ℝ) (j + 1) ℓ' (Jbar (j + 1) (It j C V W K) (Jh j C V) p.1 p.2 : Alg d L N) ≤
        ENNReal.ofReal δ := by
    intro p hp
    obtain ⟨-, hs, -⟩ := mem_pairsU.1 hp
    have hb1 : Tj d (L : ℝ) (j + 1) ℓ' (bpow (j + 1) (It j C V W K) p.2 : Alg d L N) ≤
        ENNReal.ofReal (2 ^ (2 ^ d)) := by
      have := tn_prodE (E := Dir d) (p := pPhi d) H.hh' hℓ' (blocks (j + 1) p.2) (It j C V W K)
        (fun _ => 2) (fun _ _ => by norm_num) (fun c' _ => hIt c')
      rw [prod_const] at this
      exact this.trans (ENNReal.ofReal_le_ofReal (pow_le_pow_right₀ (by norm_num) hs.2.2))
    have hnb : nb j p.2 ≤ L ^ d * 2 ^ d :=
      (nb_le_of_succ hs.1).trans (Nat.mul_le_mul_left _ hs.2.2)
    have hb2 := H.Jh_le hg0 hVb p.1 hs.1
    have hb2' : Tj d (L : ℝ) (j + 1) ℓ' (Jh j C V p.1 p.2 : Alg d L N) ≤
        ENNReal.ofReal ((2 : ℝ) ^ (L ^ d * 2 ^ d) * ((cNear d L + 2) * (2 * (Q1 d * g) ^ 2))) :=
      hb2.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hnb) (by positivity)))
    refine (tn_mulE H.hh' hℓ' (by positivity) hb1 hb2').trans (ENNReal.ofReal_le_ofReal
      (le_of_eq ?_))
    rw [hδdef, hCδ]; ring
  -- the bound on `M = K^♯`
  set μ : ℝ := C0' * k + C₃ * (g ^ 3 + g * k + k ^ 2) with hμdef
  have hμ0 : 0 ≤ μ := by positivity
  have hM : ∀ Y, IsConn (j + 1) Y → ENNReal.ofReal ((lam * A) ^ (nb (j + 1) Y - 2 ^ d)) *
      Tj d (L : ℝ) (j + 1) ℓ' (Knew j C V W K Y : Alg d L N) ≤ ENNReal.ofReal μ := by
    intro Y hY
    have := h3'' N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC V W K hV hW hV0 hK g hg0 (hgε.trans e1) hVg hWg
      (hKε.trans (ENNReal.ofReal_le_ofReal e1)) Y hY
    refine this.trans (le_of_eq ?_)
    rw [hKk, hμdef, ← ENNReal.ofReal_mul hC0'0, ← ENNReal.ofReal_mul hg0, ← ENNReal.ofReal_pow hk0,
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul hC₃,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
  -- smallness
  have hδ1 : (2 * (2 : ℝ) ^ (1 + c) * A) ^ ((2 ^ (d + 1) + 3) ^ d) * δ ≤ 1 := by
    have h := le_one_of_le_div (x := X1 * Cδ) (by positivity) (by positivity) (hgε.trans e6)
      (by linarith)
    have hg2 : g ^ 2 ≤ g := by nlinarith
    calc (2 * (2 : ℝ) ^ (1 + c) * A) ^ ((2 ^ (d + 1) + 3) ^ d) * δ = X1 * Cδ * g ^ 2 := by
          rw [hX1, ha, hδdef]; ring
      _ ≤ X1 * Cδ * g := by gcongr
      _ ≤ 1 := h
  have hμ1 : μ * (lam * A) ^ 2 ^ d ≤ 1 := by
    have h := le_one_of_le_div (x := Cμ * Λ2) (by positivity) (by positivity) (hrε.trans e7)
      (by linarith)
    have hμr : μ ≤ Cμ * r := by
      have h1 : k ≤ r := hkr
      have h2 : g ^ 3 + g * k + k ^ 2 ≤ 3 * r := by
        have i1 : g ^ 3 ≤ r := (pow_le_of_le_one hg0 hg1 (by norm_num)).trans hgr
        have i2 : g * k ≤ r := (mul_le_of_le_one_left hk0 hg1).trans hkr
        have i3 : k ^ 2 ≤ r := (pow_le_of_le_one hk0 hk1 (by norm_num)).trans hkr
        linarith
      calc μ = C0' * k + C₃ * (g ^ 3 + g * k + k ^ 2) := rfl
        _ ≤ C0' * r + C₃ * (3 * r) := by gcongr
        _ = Cμ * r := by rw [hCμ]; ring
    calc μ * (lam * A) ^ 2 ^ d = μ * Λ2 := rfl
      _ ≤ Cμ * r * Λ2 := by gcongr
      _ = Cμ * Λ2 * r := by ring
      _ ≤ 1 := h
  -- the decomposition
  have hJ0 : ∀ b ∈ blockIdx (L := L) (N := N) (j + 1),
      ∑ U ∈ (smallSets (d := d) (L := L) (N := N) (j + 1)).filter
        (fun U => blockSet (j + 1) b ⊆ U), Jh j C V b U = 0 :=
    fun b _ => Jh_sum_U hd1 hL2 hjN hC hV b
  have hsplit := Kout_split (I := It j C V W K) (M := Knew j C V W K) hJ0 hU
  have hE := Kout_sub_le (k := j + 1) (I := It j C V W K) (M := Knew j C V W K)
    (J := Jh j C V) hjN.le H.hh' hℓ' hA1 hlam1 hδ0 hμ0
    (fun b hb => by convert hc L N (j + 1) b hb) le_rfl (fun b _ => hIt b) hJb hM hδ1 hμ1 hU.1
  have hKplus : Kplus j C V W K U = Knew j C V W K U +
      ∑ g ∈ Rset (j + 1) U, Rterm (j + 1) (It j C V W K) (Knew j C V W K) (Jh j C V) U g := hsplit
  rw [hKplus]
  refine (wnorm_add_le' _ _ _ _ _ _).trans ?_
  have hS3 := h3'' N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC V W K hV hW hV0 hK g hg0 (hgε.trans e1) hVg hWg
    (hKε.trans (ENNReal.ofReal_le_ofReal e1)) U hU
  refine (add_le_add ((wnorm_mono_A hA0.le hlam1 U _).trans hS3) hE).trans ?_
  -- the real inequality for the correction
  have hX1' : (2 * (2 : ℝ) ^ (1 + c) * A) ^ ((2 ^ (d + 1) + 3) ^ d) = X1 := by rw [hX1, ha]
  rw [hX1']
  have hcorr : X1 * δ * (X1 * δ + μ * (lam * A) ^ 2 ^ d) ≤ Cx * (g ^ 3 + g * k + k ^ 2) := by
    have hg4 : g ^ 4 ≤ g ^ 3 := pow_le_pow_of_le_one hg0 hg1 (by norm_num)
    have hg2 : g ^ 2 ≤ g := pow_le_of_le_one hg0 hg1 (by norm_num)
    have hg21 : g ^ 2 ≤ 1 := hg2.trans hg1
    have hy : 0 ≤ g ^ 3 + g * k + k ^ 2 := by positivity
    have hgk0 : 0 ≤ g * k := mul_nonneg hg0 hk0
    have hk20 : 0 ≤ k ^ 2 := sq_nonneg k
    have hg30 : 0 ≤ g ^ 3 := pow_nonneg hg0 3
    have hgμ : g ^ 2 * μ ≤ C0' * (g * k) + C₃ * (g ^ 3 + g * k + k ^ 2) := by
      have h1 : g ^ 2 * (C0' * k) ≤ C0' * (g * k) :=
        calc g ^ 2 * (C0' * k) ≤ g * (C0' * k) :=
              mul_le_mul_of_nonneg_right hg2 (by positivity)
          _ = C0' * (g * k) := by ring
      have h2 : g ^ 2 * (C₃ * (g ^ 3 + g * k + k ^ 2)) ≤ C₃ * (g ^ 3 + g * k + k ^ 2) :=
        mul_le_of_le_one_left (by positivity) hg21
      have e : g ^ 2 * μ = g ^ 2 * (C0' * k) + g ^ 2 * (C₃ * (g ^ 3 + g * k + k ^ 2)) := by
        rw [hμdef]; ring
      rw [e]; linarith
    have e : X1 * δ * (X1 * δ + μ * (lam * A) ^ 2 ^ d) =
        X1 ^ 2 * Cδ ^ 2 * g ^ 4 + X1 * Cδ * Λ2 * (g ^ 2 * μ) := by
      rw [hδdef, hΛ2]; ring
    rw [e, hCx]
    have h1 : X1 ^ 2 * Cδ ^ 2 * g ^ 4 ≤ X1 ^ 2 * Cδ ^ 2 * (g ^ 3 + g * k + k ^ 2) := by
      have : g ^ 4 ≤ g ^ 3 + g * k + k ^ 2 := by linarith
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have h2 : X1 * Cδ * Λ2 * (g ^ 2 * μ) ≤
        X1 * Cδ * Λ2 * ((C0' + C₃) * (g ^ 3 + g * k + k ^ 2)) := by
      have hgk : C0' * (g * k) ≤ C0' * (g ^ 3 + g * k + k ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hC0'0
      have : g ^ 2 * μ ≤ (C0' + C₃) * (g ^ 3 + g * k + k ^ 2) := by
        have e2 : (C0' + C₃) * (g ^ 3 + g * k + k ^ 2) =
            C0' * (g ^ 3 + g * k + k ^ 2) + C₃ * (g ^ 3 + g * k + k ^ 2) := by ring
        rw [e2]; linarith
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have e3 : (X1 ^ 2 * Cδ ^ 2 + X1 * Cδ * Λ2 * (C0' + C₃)) * (g ^ 3 + g * k + k ^ 2) =
        X1 ^ 2 * Cδ ^ 2 * (g ^ 3 + g * k + k ^ 2) +
          X1 * Cδ * Λ2 * ((C0' + C₃) * (g ^ 3 + g * k + k ^ 2)) := by ring
    rw [e3]; linarith
  rw [hKk]
  have hY : ENNReal.ofReal (g ^ 3) + ENNReal.ofReal g * ENNReal.ofReal k + ENNReal.ofReal k ^ 2 =
      ENNReal.ofReal (g ^ 3 + g * k + k ^ 2) := by
    rw [← ENNReal.ofReal_mul hg0, ← ENNReal.ofReal_pow hk0,
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
  rw [hY, add_assoc]
  refine add_le_add le_rfl ?_
  rw [← ENNReal.ofReal_mul hC₃, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have e4 : (C₃ + Cx) * (g ^ 3 + g * k + k ^ 2) =
      C₃ * (g ^ 3 + g * k + k ^ 2) + Cx * (g ^ 3 + g * k + k ^ 2) := by ring
  rw [e4]; linarith

set_option maxHeartbeats 2000000 in
/-- **Theorem `stepK`**: the third-order estimate for the factorised `K_{j+1}`. -/
theorem stepK (d : ℕ) (hd : 2 ≤ d) : ∃ (C₀ η : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧ 0 < η ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ : ℝ, 0 < ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓ C →
    ∀ (V W : Fam d L N) (K : Act d L N), InF j V → InF j W → (∀ b, ε (V b : Alg d L N) = 0) →
      InK2 j K → ∀ g : ℝ, 0 ≤ g → g ≤ ε₀ →
      Fnorm j ℓ V ≤ ENNReal.ofReal g → Fnorm j ℓ W ≤ ENNReal.ofReal (g ^ 2) →
      Knorm j ℓ A K ≤ ENNReal.ofReal ε₀ →
      ∀ U : Finset (Lam d L N), IsConn (j + 1) U →
        wnorm (j + 1) ℓ A U (Kplus j C V W K U) ≤
          ENNReal.ofReal (C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3 + A ^ (-η))) * Knorm j ℓ A K +
          ENNReal.ofReal C₁ * (ENNReal.ofReal (g ^ 3) + ENNReal.ofReal g * Knorm j ℓ A K +
            Knorm j ℓ A K ^ 2) := by
  obtain ⟨C₀, η, L₀, hC₀, hη, h⟩ := stepK_ts d hd
  refine ⟨C₀, η, L₀, hC₀, hη, fun L _ hL => ?_⟩
  obtain ⟨A₀, hA₀, h'⟩ := h L hL
  refine ⟨A₀, hA₀, fun A hA => ?_⟩
  obtain ⟨ε₀, C₁, hε, hC₁, h''⟩ := h' A hA
  exact ⟨ε₀, C₁, hε, hC₁, fun N j hj ℓ hℓ C hC =>
    h'' N j hj ℓ ℓ ℓ hℓ hℓ hℓ (by linarith) C hC⟩

/-! ### Locality and symmetry of `K_{j+1}` -/

section Mem

variable {k : ℕ} {I : (Fin d → ℕ) → EvR (Lam d L N)} {M : Act d L N}
  {J : (Fin d → ℕ) → Finset (Lam d L N) → EvR (Lam d L N)} {W : Finset (Lam d L N)}
  {S : Subalgebra ℂ (Alg d L N)}

/-- **Membership principle for `K_out`.** -/
theorem Kout_mem (hI : ∀ X, IsPolymer k X → X ⊆ W → bpow k I X ∈ SE S)
    (hM : ∀ Y, IsConn k Y → Y ⊆ W → M Y ∈ SE S)
    (hJ : ∀ p ∈ pairsU (L := L) (N := N) k, p.2 ⊆ W → J p.1 p.2 ∈ SE S) :
    Kout k I M J W ∈ SE S := by
  refine Subalgebra.sum_mem _ fun g hg => ?_
  obtain ⟨f2, f3, f4⟩ := G0W_facts hg
  obtain ⟨h1, h2, -, -, -⟩ := (mem_G0 k).1 (mem_filter.1 hg).1
  have hW : IsPolymer k W := by
    rw [← (mem_filter.1 hg).2]; exact IsPolymer.union h1 (isPolymer_Bbox k _)
  refine mul_mem (hI _ (IsPolymer.sdiff hW (IsPolymer.union h1 (isPolymer_Xcal h2))) sdiff_subset)
    (mul_mem (prod_mem fun Y hY => hM Y (isConn_of_mem_comp h1 hY)
      ((subset_of_mem_comp hY).trans f2)) (prod_mem fun p hp => ?_))
  have hp2 := (mem_pairsU.1 (h2 hp)).2.1
  exact mul_mem (hI _ hp2.1 (f4 p hp).2) (hJ p (h2 hp) (f4 p hp).2)

end Mem

section Concrete

variable {j : ℕ} {ℓ : ℝ} {C : Matrix (Lam d L N) (Lam d L N) ℂ} {V W : Fam d L N}
  {K : Act d L N}

theorem kap_loc (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hjN : j + 1 < N) (hC : GoodCov2 j ℓ C)
    (hV : InF j V) {U X : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U) (hXU : clo j X = U)
    (c : Fin d → ℕ) :
    (kap j C V X c : Alg d L N) ∈ NX (nbhd (j + 1) U : Set (Lam d L N)) := by
  have hbU : ∀ b ∈ blocks j X, blockSet (L := L) (N := N) j b ⊆ U := fun b hb =>
    (blockSet_subset (IsPolymer.of_succ (isPolymer_clo j X)) (blocks_mono (subset_clo j X) hb)).trans
      (hXU ▸ subset_rfl)
  have hsub : ∀ b ∈ blocks j X, ∀ b' ∈ nearSet (L := L) (N := N) j b,
      (nbhd j (blockSet (L := L) (N := N) j b') : Set (Lam d L N)) ⊆
        (nbhd (j + 1) U : Set (Lam d L N)) := fun b hb b' hb' _ hy =>
    nbhd_mono (clo_subset hU (hbU b hb)) (mem_nbhd_succ_of_near hd hL hjN.le hb' hy)
  have hself : ∀ b ∈ blocks j X, (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N)) ⊆
      (nbhd (j + 1) U : Set (Lam d L N)) := fun b hb =>
    hsub b hb b (mem_nearSet_self (mem_blockIdx_of_mem_blocks hb))
  unfold kap; split_ifs with h1 h2
  · rw [AddSubmonoidClass.coe_finsetSum]
    refine Subalgebra.sum_mem _ fun b hb => ?_
    replace hb := (mem_filter.1 hb).1
    rw [Subalgebra.coe_smul, FCE_sub_right, AddSubgroupClass.coe_sub, FCE_VprL_eq hjN hC hV b,
      AddSubmonoidClass.coe_finsetSum]
    refine Subalgebra.smul_mem _ (sub_mem (Subalgebra.sum_mem _ fun b' hb' => ?_) ?_) _
    · rw [coe_FCE]
      exact FC_mem_NX C (NX_mono (hself b hb) (Vpr_mem hV b))
        (NX_mono (hsub b hb b' hb') (Vpr_mem hV b'))
    · rw [coe_FCE]
      exact FC_mem_NX C (NX_mono (hself b hb) (Vpr_mem hV b)) (NX_mono (hself b hb) (Vpr_mem hV b))
  · rw [Subalgebra.coe_smul, AddSubmonoidClass.coe_finsetSum]
    refine Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun b hb => ?_) _
    replace hb := (mem_filter.1 hb).1
    rw [AddSubmonoidClass.coe_finsetSum]
    refine Subalgebra.sum_mem _ fun b' hb' => ?_
    rw [coe_FCE]
    exact FC_mem_NX C (NX_mono (hself b hb) (Vpr_mem hV b))
      (NX_mono (hself b' (mem_of_mem_erase hb')) (Vpr_mem hV b'))
  · exact zero_mem _

theorem kap_sym (hV : InF j V) (X : Finset (Lam d L N)) (c : Fin d → ℕ) :
    (kap j C V X c : Alg d L N) ∈ SymS (Lam d L N) := by
  unfold kap; split_ifs
  · rw [AddSubmonoidClass.coe_finsetSum]
    refine Subalgebra.sum_mem _ fun b _ => ?_
    rw [Subalgebra.coe_smul]
    refine Subalgebra.smul_mem _ (FCE_sym (Vpr_sym hV b) ?_) _
    rw [AddSubgroupClass.coe_sub]; exact sub_mem (VprL_sym hV) (Vpr_sym hV b)
  · rw [Subalgebra.coe_smul, AddSubmonoidClass.coe_finsetSum]
    refine Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun b _ => ?_) _
    rw [AddSubmonoidClass.coe_finsetSum]
    exact Subalgebra.sum_mem _ fun b' _ => FCE_sym (Vpr_sym hV b) (Vpr_sym hV b')
  · exact zero_mem _

theorem Jh_loc (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hjN : j + 1 < N) (hC : GoodCov2 j ℓ C)
    (hV : InF j V) (c : Fin d → ℕ) {U : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U) :
    (Jh j C V c U : Alg d L N) ∈ NX (nbhd (j + 1) U : Set (Lam d L N)) := by
  classical
  unfold Jh; split_ifs
  · rw [AddSubmonoidClass.coe_finsetSum]
    exact Subalgebra.sum_mem _ fun X hX => kap_loc hd hL hjN hC hV hU (mem_filter.1 hX).2 c
  · exact zero_mem _

theorem Jh_sym (hV : InF j V) (c : Fin d → ℕ) (U : Finset (Lam d L N)) :
    (Jh j C V c U : Alg d L N) ∈ SymS (Lam d L N) := by
  classical
  unfold Jh; split_ifs
  · rw [AddSubmonoidClass.coe_finsetSum]
    exact Subalgebra.sum_mem _ fun X _ => kap_sym hV X c
  · exact zero_mem _

/-- **Locality of `K_{j+1}`.** -/
theorem Kplus_loc (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hjN : j + 1 < N) (hC : GoodCov2 j ℓ C)
    (hV : InF j V) (hW : InF j W) (hV0 : ∀ b, ε (V b : Alg d L N) = 0) (hK : InK2 j K)
    {U : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U) :
    (Kplus j C V W K U : Alg d L N) ∈ NX (nbhd (j + 1) U : Set (Lam d L N)) := by
  refine mem_SE.1 (Kout_mem (S := NX (nbhd (j + 1) U : Set (Lam d L N))) ?_ ?_ ?_)
  · intro X hX hXU
    rw [bpow_It j C V W K hX]
    exact prod_mem fun b hb => NX_mono (coe_subset.2 (nbhd_mono ((clo_subset hU
      ((blockSet_subset (IsPolymer.of_succ hX) hb).trans hXU)))))
      (Gp_mem hd hL hjN hC hV hW (mem_blockIdx_of_mem_blocks hb))
  · intro Y hY hYU
    exact NX_mono (coe_subset.2 (nbhd_mono hYU)) (Knew_loc hd hL hjN hC hV hW hV0 hK hY.1)
  · intro p hp hpU
    exact NX_mono (coe_subset.2 (nbhd_mono hpU))
      (Jh_loc hd hL hjN hC hV p.1 (mem_pairsU.1 hp).2.1.1)

/-- **`U(1)` invariance of `K_{j+1}`.** -/
theorem Kplus_sym (hV : InF j V) (hW : InF j W) (hK : InK2 j K) (U : Finset (Lam d L N)) :
    IsSym (Kplus j C V W K U : Alg d L N) := by
  rw [isSym_iff_mem_SymS]
  refine mem_SE.1 (Kout_mem (S := SymS (Lam d L N)) ?_ ?_ ?_)
  · intro X hX _
    rw [bpow_It j C V W K hX]
    exact prod_mem fun b _ => Gp_sym hV hW b
  · intro Y hY _
    exact (isSym_iff_mem_SymS _).1 (Knew_sym hV hW hK hY.1)
  · intro p _ _
    exact Jh_sym hV p.1 p.2

/-- **`K_{j+1} ∈ 𝒦_{j+1}`.** -/
theorem InK2_Kplus (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hjN : j + 1 < N) (hC : GoodCov2 j ℓ C)
    (hV : InF j V) (hW : InF j W) (hV0 : ∀ b, ε (V b : Alg d L N) = 0) (hK : InK2 j K) :
    InK2 (j + 1) (Kplus j C V W K) :=
  ⟨fun X hX => Kplus_loc hd hL hjN hC hV hW hV0 hK hX.1, fun X _ => Kplus_sym hV hW hK X⟩

end Concrete

/-- **Theorem `stepK` in `d = 2`.** -/
theorem stepK_d2 : ∃ (C₀ η : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧ 0 < η ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ : ℝ, 0 < ℓ →
    ∀ C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ, GoodCov2 j ℓ C →
    ∀ (V W : Fam 2 L N) (K : Act 2 L N), InF j V → InF j W → (∀ b, ε (V b : Alg 2 L N) = 0) →
      InK2 j K → ∀ g : ℝ, 0 ≤ g → g ≤ ε₀ →
      Fnorm j ℓ V ≤ ENNReal.ofReal g → Fnorm j ℓ W ≤ ENNReal.ofReal (g ^ 2) →
      Knorm j ℓ A K ≤ ENNReal.ofReal ε₀ →
      ∀ U : Finset (Lam 2 L N), IsConn (j + 1) U →
        wnorm (j + 1) ℓ A U (Kplus j C V W K U) ≤
          ENNReal.ofReal (C₀ * ((L : ℝ)⁻¹ + A ^ (-η))) * Knorm j ℓ A K +
          ENNReal.ofReal C₁ * (ENNReal.ofReal (g ^ 3) + ENNReal.ofReal g * Knorm j ℓ A K +
            Knorm j ℓ A K ^ 2) := by
  obtain ⟨C₀, η, L₀, hC₀, hη, h⟩ := stepK 2 le_rfl
  refine ⟨C₀, η, L₀, hC₀, hη, fun L _ hL => ?_⟩
  obtain ⟨A₀, hA₀, h'⟩ := h L hL
  refine ⟨A₀, hA₀, fun A hA => ?_⟩
  obtain ⟨ε', C₁, hε, hC₁, h''⟩ := h' A hA
  refine ⟨ε', C₁, hε, hC₁, fun N j hj ℓ hℓ C hC V W K hV hW hV0 hK g hg hgε hVg hWg hKε U hU => ?_⟩
  have e : (L : ℝ) ^ 2 / (L : ℝ) ^ 3 = (L : ℝ)⁻¹ := by
    have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
    field_simp
  have := h'' N j hj ℓ hℓ C hC V W K hV hW hV0 hK g hg hgε hVg hWg hKε U hU
  rwa [e] at this

end

end Step2
