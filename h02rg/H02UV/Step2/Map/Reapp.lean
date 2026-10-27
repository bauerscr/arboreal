import Step2.Map.Main

/-!
# Reapportionment of the second-order part (Brydges–Slade, *A single RG step*, Map 4)

The polymer activity `K_{j+1}` of `Step2.Knext2` has the nonzero second-order part
`K^{(2)} = K2` (BS: `h_lead`, (5.18)). As in Map 4 of Brydges–Slade, it is reapportioned
using `∑_U K^{(2)}(U) = 0` (BS (5.19)):

  `K_{j+1}^♯(U) = K_{j+1}(U) - Ĩ_{j+1}^U K^{(2)}(U)`,    `Ĩ_{j+1}(B) = e^{-V_{j+1}(B)}(1 + 𝒲_{j+1}(B))`,

(`Knew`). Then (`step3_ZVK`)

  `𝔼θ Z_j = ∑_U I_{j+1}^{Λ∖U} e^{-u_{j+1}(U)} K^♯_{j+1}(U)`

exactly, and (`step3`, `step3_d2`) the **original third-order estimate** holds:

  `A^{(|𝓑_{j+1}(U)|-2^d)_+} ‖K^♯_{j+1}(U)‖ ≤ C₀(L^{d-3} + A^{-η}) ‖K‖_j + C₁ (ḡ³ + ḡ‖K‖_j + ‖K‖_j²)`.

BS use the change of variables of their Proposition 4.1 / (D.13), whose output is
`K^♯ + E` with a higher-order correction `E` that restores the factorisation of the activity
over connected components. Here `K_{j+1}` itself is not shown to factorise, and `E` is omitted.
-/

namespace Step2

noncomputable section

open Finset Grassmann Loc FRD Step

variable {d L N : ℕ} [NeZero L]

/-! ### `∑_U K^{(2)}(U) = 0` -/

section Sum

variable {ι M : Type*} [DecidableEq ι] [AddCommMonoid M]

theorem sum_powersetCard_one (T : Finset ι) (f : ι → M) :
    ∑ S ∈ T.powersetCard 1, ∑ b ∈ S, f b = ∑ b ∈ T, f b := by
  rw [powersetCard_one, sum_map]
  simp

theorem sum_powersetCard_two (T : Finset ι) (g : ι → ι → M) :
    ∑ S ∈ T.powersetCard 2, ∑ b ∈ S, ∑ b' ∈ S.erase b, g b b' =
      ∑ b ∈ T, ∑ b' ∈ T.erase b, g b b' := by
  simp only [sum_sigma']
  refine sum_bij' (fun x _ => (⟨x.2.1, x.2.2⟩ : Σ _ : ι, ι))
    (fun y _ => (⟨{y.1, y.2}, ⟨y.1, y.2⟩⟩ : Σ _ : Finset ι, Σ _ : ι, ι)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨S, b, b'⟩ h
    simp only [mem_sigma, mem_powersetCard, mem_erase] at h ⊢
    exact ⟨h.1.1 h.2.1, h.2.2.1, h.1.1 h.2.2.2⟩
  · rintro ⟨b, b'⟩ h
    simp only [mem_sigma, mem_erase] at h ⊢
    refine ⟨mem_powersetCard.2 ⟨?_, card_pair (Ne.symm h.2.1)⟩, mem_insert_self _ _,
      h.2.1, ?_⟩
    · intro x hx
      rcases mem_insert.1 hx with rfl | hx
      · exact h.1
      · rw [mem_singleton.1 hx]; exact h.2.2
    · simp
  · rintro ⟨S, b, b'⟩ h
    simp only [mem_sigma, mem_powersetCard, mem_erase] at h
    obtain ⟨⟨-, hS⟩, hb, hbb', hb'⟩ := h
    obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.1 hS
    have : ({b, b'} : Finset ι) = {x, y} := by
      refine eq_of_subset_of_card_le ?_ (by rw [card_pair hxy, card_pair (Ne.symm hbb')])
      intro z hz
      rcases mem_insert.1 hz with rfl | hz
      · exact hb
      · rw [mem_singleton.1 hz]; exact hb'
    simp only [this]
  · rintro ⟨b, b'⟩ _; rfl
  · rintro ⟨S, b, b'⟩ _; rfl

end Sum

section K2sum

variable (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V : Fam d L N)

/-- The `j`-polymers are in bijection with the sets of `j`-blocks. -/
theorem sum_Pj_eq_sum_powerset {M : Type*} [AddCommMonoid M] (φ : Finset (Fin d → ℕ) → M) :
    ∑ X ∈ Pj (d := d) (L := L) (N := N) j univ, φ (blocks j X) =
      ∑ S ∈ (blockIdx (d := d) (L := L) (N := N) j).powerset, φ S := by
  classical
  refine sum_bij' (fun X _ => blocks j X) (fun S _ => S.biUnion (blockSet j)) ?_ ?_ ?_ ?_ ?_
  · intro X _
    exact mem_powerset.2 fun b hb => mem_blockIdx_of_mem_blocks hb
  · intro S hS
    refine mem_Pj.2 ⟨subset_univ _, ?_⟩
    intro x y hxy hx
    obtain ⟨b, hb, hxb⟩ := mem_biUnion.1 hx
    exact mem_biUnion.2 ⟨b, hb, mem_blockSet.2 (hxy ▸ mem_blockSet.1 hxb)⟩
  · intro X hX
    exact biUnion_blocks (mem_Pj.1 hX).2
  · intro S hS
    ext b
    constructor
    · intro hb
      obtain ⟨x, hx, rfl⟩ := mem_blocks.1 hb
      obtain ⟨b', hb', hxb'⟩ := mem_biUnion.1 hx
      rw [mem_blockSet.1 hxb']; exact hb'
    · intro hb
      obtain ⟨x, -, rfl⟩ := mem_image.1 (mem_powerset.1 hS hb)
      exact mem_blocks.2 ⟨x, mem_biUnion.2 ⟨blk j x, hb, mem_blockSet.2 rfl⟩, rfl⟩
  · intro X _; rfl

/-- `∑_X k^{(2)}(X) = 0` over all `j`-polymers. -/
theorem k2_sum_zero : ∑ X ∈ Pj (d := d) (L := L) (N := N) j univ, k2 j C V X = 0 := by
  classical
  set T := blockIdx (L := L) (N := N) j
  set φ : Finset (Fin d → ℕ) → EvR (Lam d L N) := fun S =>
    if S.card = 1 then ∑ b ∈ S, (-(1 / 2 : ℂ)) • FCE C (Vpr C V b) (VprL j C V - Vpr C V b)
    else if S.card = 2 then
      (1 / 2 : ℂ) • ∑ b ∈ S, ∑ b' ∈ S.erase b, FCE C (Vpr C V b) (Vpr C V b')
    else 0
  have e1 : ∑ X ∈ Pj (L := L) (N := N) j univ, k2 j C V X =
      ∑ X ∈ Pj (L := L) (N := N) j univ, φ (blocks j X) := rfl
  rw [e1, sum_Pj_eq_sum_powerset j φ]
  have e2 : ∑ S ∈ T.powerset, φ S = ∑ S ∈ T.powersetCard 1, φ S + ∑ S ∈ T.powersetCard 2, φ S := by
    rw [← sum_union (disjoint_left.2 fun S h1 h2 => by
      have := (mem_powersetCard.1 h1).2; have := (mem_powersetCard.1 h2).2; omega)]
    symm
    refine sum_subset (fun S hS => ?_) fun S hS hS' => ?_
    · rcases mem_union.1 hS with h | h <;> exact mem_powerset.2 (mem_powersetCard.1 h).1
    · have h1 : S.card ≠ 1 := fun h => hS' (mem_union_left _ (mem_powersetCard.2
        ⟨mem_powerset.1 hS, h⟩))
      have h2 : S.card ≠ 2 := fun h => hS' (mem_union_right _ (mem_powersetCard.2
        ⟨mem_powerset.1 hS, h⟩))
      simp [φ, h1, h2]
  rw [e2]
  have e3 : ∑ S ∈ T.powersetCard 1, φ S = ∑ b ∈ T, (-(1 / 2 : ℂ)) •
      FCE C (Vpr C V b) (VprL j C V - Vpr C V b) := by
    rw [← sum_powersetCard_one T]
    refine sum_congr rfl fun S hS => ?_
    simp [φ, (mem_powersetCard.1 hS).2]
  have e4 : ∑ S ∈ T.powersetCard 2, φ S = (1 / 2 : ℂ) • ∑ b ∈ T, ∑ b' ∈ T.erase b,
      FCE C (Vpr C V b) (Vpr C V b') := by
    rw [← sum_powersetCard_two T, smul_sum]
    refine sum_congr rfl fun S hS => ?_
    simp [φ, (mem_powersetCard.1 hS).2]
  rw [e3, e4, smul_sum, ← sum_add_distrib]
  refine sum_eq_zero fun b hb => ?_
  rw [← FCE_sum_right, sum_erase_eq_sub hb, neg_smul]
  exact neg_add_cancel _

/-- **`∑_U K^{(2)}(U) = 0`** (BS (5.19)). -/
theorem K2_sum_zero : ∑ U ∈ Pj (L := L) (N := N) (j + 1) univ, K2 j C V U = 0 := by
  classical
  rw [← k2_sum_zero j C V]
  unfold K2
  exact sum_fiberwise_of_maps_to (fun X _ => mem_Pj.2 ⟨subset_univ _, isPolymer_clo j X⟩)
    (k2 j C V)

end K2sum

/-! ### The reapportioned activity -/

section Map

variable (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V W : Fam d L N) (K : Act d L N)

/-- `Ĩ_{j+1}(B) = e^{-V_{j+1}(B)}(1 + 𝒲_{j+1}(B))` (BS `Ĩ_pt`). -/
def Gp (b : Fin d → ℕ) : EvR (Lam d L N) := gexp (-Vp j C V W K b) * (1 + Wp j C V W b)

/-- **`K^♯_{j+1}(U) = K_{j+1}(U) - Ĩ_{j+1}^U K^{(2)}(U)`.** -/
def Knew (U : Finset (Lam d L N)) : EvR (Lam d L N) :=
  Knext2 j C V W K U - bpow j (Gp j C V W K) U * K2 j C V U

theorem bpow_Ip (X : Finset (Lam d L N)) :
    bpow j (Ip j C V W K) X = Complex.exp (-uX j C V W K X) • bpow j (Gp j C V W K) X := by
  classical
  unfold bpow uX
  induction blocks j X using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha, sum_insert ha, ih, neg_add, Complex.exp_add, Ip,
      smul_mul_smul_comm]
    rfl

end Map

/-! ### Bounds -/

section Bounds

variable {X : Type*} [DecidableEq X] [Fintype X] {E : Type*} [Fintype E] [DecidableEq E]
  [AddAction (E → ℕ) X] {p : ℕ} {h ℓ : ℝ}

/-- `‖∏ F_i - 1‖ ≤ (1+δ)^n - 1` if `‖F_i - 1‖ ≤ δ`. -/
theorem tn_prod_sub_one (hh : 0 < h) (hℓ : 0 < ℓ) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (F : ι → EvR X) {δ : ℝ} (hδ : 0 ≤ δ)
    (hF : ∀ i ∈ s, tNorm E p h ℓ ((F i - 1 : EvR X) : Grassmann.N X) ≤ ENNReal.ofReal δ) :
    tNorm E p h ℓ ((∏ i ∈ s, F i - 1 : EvR X) : Grassmann.N X) ≤
      ENNReal.ofReal ((1 + δ) ^ s.card - 1) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [prod_empty, sub_self, card_empty, pow_zero, ZeroMemClass.coe_zero]
    rw [tn_zero']; exact zero_le
  | insert a s ha ih =>
    have ih' := ih fun i hi => hF i (mem_insert_of_mem hi)
    have hFa := hF a (mem_insert_self a s)
    have hFa' : tNorm E p h ℓ (F a : Grassmann.N X) ≤ ENNReal.ofReal (1 + δ) := by
      have e : F a = 1 + (F a - 1) := by abel
      rw [e]
      exact tn_addE zero_le_one hδ (by
        rw [OneMemClass.coe_one, ENNReal.ofReal_one]; exact tNorm_one_le hh hℓ) hFa
    have e : ∏ i ∈ insert a s, F i - 1 = F a * (∏ i ∈ s, F i - 1) + (F a - 1) := by
      rw [prod_insert ha]; ring
    have h1 : 0 ≤ (1 + δ) ^ s.card - 1 := by
      have := one_le_pow₀ (M₀ := ℝ) (n := s.card) (by linarith : (1 : ℝ) ≤ 1 + δ); linarith
    rw [e]
    refine (tn_addE (by positivity) hδ (tn_mulE hh hℓ (by linarith) hFa' ih') hFa).trans
      (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    rw [card_insert_of_notMem ha, pow_succ]; ring

end Bounds

namespace BH

variable {j : ℕ} {ℓ ℓ' ℓC : ℝ} {C : Matrix (Lam d L N) (Lam d L N) ℂ} {V W : Fam d L N}
  {K : Act d L N} {A r Cl cS : ℝ} (H : BH j ℓ ℓ' ℓC C V W K A r Cl cS)
include H

theorem Gp_sub_one_le (hu : cUblk d L Cl cS * r ≤ 1 / 4) (hw : cWblk d L Cl * r ≤ 1)
    {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    Tj d (L : ℝ) (j + 1) ℓ' ((Gp j C V W K b - 1 : EvR (Lam d L N)) : Alg d L N) ≤
      ENNReal.ofReal ((8 * cUblk d L Cl cS + cWblk d L Cl) * r) := by
  have hr := H.hr
  have hU0 : 0 ≤ cUblk d L Cl cS * r := mul_nonneg H.hcU hr
  have hW0 : 0 ≤ cWblk d L Cl * r := mul_nonneg H.hcW hr
  have e : Gp j C V W K b - 1 =
      (gexp (-Vp j C V W K b) - 1) * (1 + Wp j C V W b) + Wp j C V W b := by
    rw [Gp]; ring
  have hε : ε ((-Vp j C V W K b : EvR (Lam d L N)) : Alg d L N) = 0 := by
    rw [NegMemClass.coe_neg, map_neg, ε_Vp, neg_zero]
  have hg : Tj d (L : ℝ) (j + 1) ℓ' ((gexp (-Vp j C V W K b) - 1 : EvR (Lam d L N)) : Alg d L N) ≤
      ENNReal.ofReal (2 * (2 * (cUblk d L Cl cS * r))) := by
    refine (tNorm_gexp_sub_one_le H.hh' H.hℓ' hε (by positivity) ?_).trans
      (ENNReal.ofReal_le_ofReal (exp_sub_one_le (by positivity) (by linarith)))
    rw [NegMemClass.coe_neg, tNorm_neg]; exact H.Vp_le hb
  have h1W : Tj d (L : ℝ) (j + 1) ℓ' ((1 + Wp j C V W b : EvR (Lam d L N)) : Alg d L N) ≤
      ENNReal.ofReal (1 + cWblk d L Cl * r) :=
    tn_addE zero_le_one hW0 (by
      rw [OneMemClass.coe_one, ENNReal.ofReal_one]; exact tNorm_one_le H.hh' H.hℓ') (H.Wp_le hb)
  rw [e]
  refine (tn_addE (by positivity) hW0 (tn_mulE H.hh' H.hℓ' (by positivity) hg h1W)
    (H.Wp_le hb)).trans (ENNReal.ofReal_le_ofReal ?_)
  nlinarith

theorem k2_le (X : Finset (Lam d L N)) :
    Tj d (L : ℝ) (j + 1) ℓ' (k2 j C V X : Alg d L N) ≤
      ENNReal.ofReal ((cNear d L + 2) * (2 * (Q1 d * r) ^ 2)) := by
  classical
  have hq : 0 ≤ 2 * (Q1 d * r) ^ 2 := by positivity
  have hN := H.hcNear
  have hb : ∀ b ∈ blocks j X, b ∈ blockIdx (L := L) (N := N) j :=
    fun b hb => mem_blockIdx_of_mem_blocks hb
  unfold k2
  split_ifs with h1 h2
  · refine (tn_sum_const (E := Dir d) (p := pPhi d) _ _
      (r := (cNear d L + 1) * (2 * (Q1 d * r) ^ 2)) (by positivity) fun b hbX => ?_).trans
      (ENNReal.ofReal_le_ofReal ?_)
    · rw [Subalgebra.coe_smul, tNorm_smul, FCE_sub_right, FCE_VprL_eq H.hjN H.hC H.hV b]
      have hs := tn_sum_const (E := Dir d) (p := pPhi d) (h := (L : ℝ) ^ (j + 1)) (ℓ := ℓ')
        (nearSet (L := L) (N := N) j b) (fun b' => FCE C (Vpr C V b) (Vpr C V b'))
        (r := 2 * (Q1 d * r) ^ 2) hq (fun b' hb' => H.FCE_pair_le (hb b hbX) (mem_filter.1 hb').1)
      have hn : ((nearSet (L := L) (N := N) j b).card : ℝ) ≤ cNear d L := by
        unfold cNear; exact_mod_cast card_nearSet_le H.hj.le b (hb b hbX)
      have hsub := tn_subE (by positivity) hq hs (H.FCE_pair_le (hb b hbX) (hb b hbX))
      refine (mul_le_mul_left' hsub _).trans ?_
      rw [← ENNReal.ofReal_mul (norm_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      have : ‖-(1 / 2 : ℂ)‖ = 1 / 2 := by simp
      rw [this]
      nlinarith
    · rw [show (blocks j X).card = 1 from h1]; push_cast; nlinarith
  · rw [Subalgebra.coe_smul, Tj_smul']
    have hs : Tj d (L : ℝ) (j + 1) ℓ' ((∑ b ∈ blocks j X, ∑ b' ∈ (blocks j X).erase b,
        FCE C (Vpr C V b) (Vpr C V b') : EvR (Lam d L N)) : Alg d L N) ≤
        ENNReal.ofReal ((blocks j X).card * (((blocks j X).card - 1 : ℕ) *
          (2 * (Q1 d * r) ^ 2))) := by
      refine tn_sum_const (E := Dir d) (p := pPhi d) _ _ (by positivity) fun b hbX => ?_
      have := tn_sum_const (E := Dir d) (p := pPhi d) (h := (L : ℝ) ^ (j + 1)) (ℓ := ℓ')
        ((blocks j X).erase b) (fun b' => FCE C (Vpr C V b) (Vpr C V b')) hq
        (fun b' hb' => H.FCE_pair_le (hb b hbX) (hb b' (mem_of_mem_erase hb')))
      rwa [card_erase_of_mem hbX] at this
    refine (mul_le_mul_left' hs _).trans ?_
    rw [← ENNReal.ofReal_mul (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [this, show (blocks j X).card = 2 from h2]
    norm_num
    nlinarith
  · rw [ZeroMemClass.coe_zero, Step.Tj_zero (d := d) (L : ℝ) (j + 1) ℓ']; exact zero_le

end BH

/-- `K^{(2)}(U) = 0` unless `U` has at most two `(j+1)`-blocks. -/
theorem K2_eq_zero (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V : Fam d L N)
    {U : Finset (Lam d L N)} (hU : 2 < nb (j + 1) U) : K2 j C V U = 0 := by
  classical
  unfold K2
  refine sum_eq_zero fun X hX => ?_
  have hcl := (mem_filter.1 hX).2
  have h3 : 2 < nb j X := by
    have := nb_clo_le (L := L) (N := N) j X
    rw [hcl] at this; omega
  unfold k2
  rw [if_neg (by intro h; rw [h] at h3; omega), if_neg (by intro h; rw [h] at h3; omega)]


theorem card_K2_filter_le (j : ℕ) {U : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U) :
    (((Pj (d := d) (L := L) (N := N) j univ).filter (fun X => clo j X = U)).card : ℝ) ≤
      2 ^ nb j U := by
  classical
  have h1 : (Pj (d := d) (L := L) (N := N) j univ).filter (fun X => clo j X = U) ⊆ Pj j U :=
    fun X hX => by
      obtain ⟨hX1, hX2⟩ := mem_filter.1 hX
      exact mem_Pj.2 ⟨hX2 ▸ subset_clo j X, (mem_Pj.1 hX1).2⟩
  have := (card_le_card h1).trans (card_Pj (IsPolymer.of_succ hU)).le
  exact_mod_cast this

theorem wnorm_neg (j : ℕ) (ℓ A : ℝ) (U : Finset (Lam d L N)) (F : EvR (Lam d L N)) :
    wnorm j ℓ A U (-F) = wnorm j ℓ A U F := by
  unfold wnorm; rw [NegMemClass.coe_neg]; exact congrArg _ (tNorm_neg _)

set_option maxHeartbeats 1000000 in
/-- **Theorem `step3`**: the original third-order estimate (Expected result 7.1) for the
reapportioned activity `K^♯_{j+1}`. -/
theorem step3_ts (d : ℕ) (hd : 2 ≤ d) : ∃ (C₀ η : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧ 0 < η ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓC C →
    ∀ (V W : Fam d L N) (K : Act d L N), InF j V → InF j W → (∀ b, ε (V b : Alg d L N) = 0) →
      InK2 j K → ∀ g : ℝ, 0 ≤ g → g ≤ ε₀ →
      Fnorm j ℓ V ≤ ENNReal.ofReal g → Fnorm j ℓ W ≤ ENNReal.ofReal (g ^ 2) →
      Knorm j ℓ A K ≤ ENNReal.ofReal ε₀ →
      ∀ U : Finset (Lam d L N), IsConn (j + 1) U →
        wnorm (j + 1) ℓ' A U (Knew j C V W K U) ≤
          ENNReal.ofReal (C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3 + A ^ (-η))) * Knorm j ℓ A K +
          ENNReal.ofReal C₁ * (ENNReal.ofReal (g ^ 3) + ENNReal.ofReal g * Knorm j ℓ A K +
            Knorm j ℓ A K ^ 2) := by
  classical
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C₀, η, L₂, hC₀, hη, h2⟩ := step2_ts d hd
  obtain ⟨Cl, hCl0, hloc⟩ := exists_Loc2sXY_bound d hd1
  obtain ⟨c, hc⟩ := card_small_containing d
  refine ⟨C₀, η, max L₂ (max (2 ^ (d + 3) + 8 * d + 1) ⌈pauliL0 d⌉₊), hC₀, hη, ?_⟩
  intro L _ hL
  have hL2 : L₂ ≤ L := le_trans (le_max_left _ _) hL
  have hL8 : 2 ^ (d + 3) + 8 * d < L :=
    lt_of_lt_of_le (Nat.lt_succ_self _) (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL)
  have hLp : pauliL0 d ≤ L := (Nat.le_ceil _).trans
    (by exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL)
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  obtain ⟨A₀, hA₀, h2'⟩ := h2 L hL2
  refine ⟨A₀, hA₀, fun A hA => ?_⟩
  have hA1 : 1 ≤ A := hA₀.trans hA
  have hA0 : 0 < A := by linarith
  obtain ⟨ε₂, C₂, hε₂, hC₂, h2''⟩ := h2' A hA
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
  set n₀ : ℝ := 2 * (L : ℝ) ^ d with hn₀
  have hn₀0 : 0 ≤ n₀ := by positivity
  set Ck : ℝ := (cNear d L + 2) * (2 * Q1 d ^ 2) with hCk
  have hCk0 : 0 ≤ Ck := by
    have := Nat.cast_nonneg (α := ℝ) ((L + 2 ^ (d + 3) + 7) ^ d)
    rw [hCk]; unfold cNear; positivity
  set Cs : ℝ := 2 * n₀ * δc * (2 : ℝ) ^ (2 * L ^ d) * Ck with hCs
  have hCs0 : 0 ≤ Cs := by positivity
  set ε₀ : ℝ := min ε₂ (min 1 (min (1 / (4 * cu + 1)) (min (1 / (cw + 1)) (1 / (n₀ * δc + 1)))))
    with hε₀
  have hε₀0 : 0 < ε₀ := lt_min hε₂ (lt_min one_pos (lt_min (by positivity)
    (lt_min (by positivity) (by positivity))))
  refine ⟨ε₀, C₂ + Cs, hε₀0, by positivity, ?_⟩
  intro N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC V W K hV hW hV0 hK g hg0 hgε hVg hWg hKε U hU
  have e1 : ε₀ ≤ ε₂ := min_le_left _ _
  have e2 : ε₀ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have e3 : ε₀ ≤ 1 / (4 * cu + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have e4 : ε₀ ≤ 1 / (cw + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have e5 : ε₀ ≤ 1 / (n₀ * δc + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_right _ _)))
  -- the step2 bound
  have hS2 := h2'' N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC V W K hV hW hV0 hK g hg0 (hgε.trans e1) hVg hWg
    (hKε.trans (ENNReal.ofReal_le_ofReal e1)) U hU
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
  have hgr : g ≤ r := le_max_left _ _
  have hkr : k ≤ r := le_max_right _ _
  have H : BH j ℓ ℓ' ℓC C V W K A r Cl cS :=
    { hd := hd1, hLp := hLp, hL8 := hL8, hjN := hjN, hℓ := hℓ, hℓ' := hℓ', hℓC := hℓC, hsum := hsum, hC := hC, hV := hV, hW := hW,
      hV0 := hV0, hK := hK, hA := hA1, hr := hr0, hr1 := hr1
      hVr := fun b hb => ((le_iSup₂ (f := fun b (_ : b ∈ blockIdx (L := L) (N := N) j) =>
        Tj d (L : ℝ) j ℓ (V b : Alg d L N)) b hb).trans hVg).trans (ENNReal.ofReal_le_ofReal hgr)
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
  have hnδ : n₀ * δc * r ≤ 1 :=
    le_one_of_le_div (by positivity) (by positivity) (hrε.trans e5) (by linarith)
  -- the reapportionment term
  have hsplit : Knew j C V W K U = (Knext2 j C V W K U - K2 j C V U) +
      -((bpow j (Gp j C V W K) U - 1) * K2 j C V U) := by rw [Knew]; ring
  have hT : wnorm (j + 1) ℓ' A U ((bpow j (Gp j C V W K) U - 1) * K2 j C V U) ≤
      ENNReal.ofReal (Cs * r ^ 3) := by
    by_cases hU2 : 2 < nb (j + 1) U
    · rw [K2_eq_zero j C V hU2, mul_zero]
      unfold wnorm
      rw [ZeroMemClass.coe_zero, Step.Tj_zero (d := d) (L : ℝ) (j + 1) ℓ', mul_zero]
      exact zero_le
    · push Not at hU2
      have hw1 : A ^ (nb (j + 1) U - 2 ^ d) = 1 := by
        have : nb (j + 1) U - 2 ^ d = 0 := by
          have : 2 ≤ 2 ^ d := by
            calc 2 = 2 ^ 1 := rfl
              _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd1
          omega
        rw [this, pow_zero]
      unfold wnorm
      rw [hw1, ENNReal.ofReal_one, one_mul]
      have hnbU : (nb j U : ℝ) ≤ n₀ := by
        have := nb_le_of_succ hU.1
        have h' : (nb j U : ℝ) ≤ (L : ℝ) ^ d * nb (j + 1) U := by exact_mod_cast this
        have h'' : (nb (j + 1) U : ℝ) ≤ 2 := by exact_mod_cast hU2
        rw [hn₀]; nlinarith [pow_pos hL0 d]
      -- `‖Ĩ^U - 1‖ ≤ 2 n₀ δc r`
      have hP : Tj d (L : ℝ) (j + 1) ℓ' ((bpow j (Gp j C V W K) U - 1 : EvR (Lam d L N)) :
          Alg d L N) ≤ ENNReal.ofReal (2 * n₀ * δc * r) := by
        refine (tn_prod_sub_one H.hh' hℓ' (blocks j U) _ (by positivity)
          (fun b hb => H.Gp_sub_one_le hu hw (mem_blockIdx_of_mem_blocks hb))).trans
          (ENNReal.ofReal_le_ofReal ?_)
        have hn : ((blocks j U).card : ℝ) ≤ n₀ := hnbU
        have h1 : (1 + δc * r) ^ (blocks j U).card ≤ Real.exp ((blocks j U).card * (δc * r)) := by
          calc (1 + δc * r) ^ (blocks j U).card ≤ Real.exp (δc * r) ^ (blocks j U).card := by
                gcongr; linarith [Real.add_one_le_exp (δc * r)]
            _ = Real.exp ((blocks j U).card * (δc * r)) := (Real.exp_nat_mul _ _).symm
        have hx : ((blocks j U).card : ℝ) * (δc * r) ≤ n₀ * δc * r := by
          have := mul_le_mul_of_nonneg_right hn (by positivity : 0 ≤ δc * r); linarith
        have h2 := exp_sub_one_le (r := ((blocks j U).card : ℝ) * (δc * r))
          (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hδc0 hr0)) (hx.trans hnδ)
        nlinarith
      -- `‖K^{(2)}(U)‖ ≤ 2^{n₀} Ck r²`
      have hK2 : Tj d (L : ℝ) (j + 1) ℓ' (K2 j C V U : Alg d L N) ≤
          ENNReal.ofReal ((2 : ℝ) ^ (2 * L ^ d) * (Ck * r ^ 2)) := by
        unfold K2
        refine (tn_sum_const (E := Dir d) (p := pPhi d) _ _ (r := Ck * r ^ 2) (by positivity)
          fun X _ => (H.k2_le X).trans (ENNReal.ofReal_le_ofReal (le_of_eq (by ring)))).trans
          (ENNReal.ofReal_le_ofReal ?_)
        refine mul_le_mul_of_nonneg_right ((card_K2_filter_le j hU.1).trans ?_) (by positivity)
        have : nb j U ≤ 2 * L ^ d :=
          calc nb j U ≤ L ^ d * nb (j + 1) U := nb_le_of_succ hU.1
            _ ≤ L ^ d * 2 := Nat.mul_le_mul_left _ hU2
            _ = 2 * L ^ d := mul_comm _ _
        calc (2 : ℝ) ^ nb j U ≤ 2 ^ (2 * L ^ d) := pow_le_pow_right₀ (by norm_num) this
          _ = _ := rfl
      refine (tn_mulE H.hh' hℓ' (by positivity) hP hK2).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [hCs]; nlinarith [sq_nonneg r]
  rw [hsplit]
  refine (wnorm_add_le' _ _ _ _ _ _).trans ?_
  rw [wnorm_neg]
  refine (add_le_add hS2 hT).trans ?_
  -- `r³ ≤ g³ + k²`
  have hr3 : r ^ 3 ≤ g ^ 3 + k ^ 2 := by
    rcases le_total g k with h | h
    · have : r = k := max_eq_right h
      rw [this]
      have : k ^ 3 ≤ k ^ 2 := pow_le_pow_of_le_one hk0 (hkr.trans hr1) (by norm_num)
      nlinarith [pow_nonneg hg0 3]
    · have : r = g := max_eq_left h
      rw [this]; nlinarith [sq_nonneg k]
  rw [hKk, add_assoc]
  have hY : ENNReal.ofReal (g ^ 3) + ENNReal.ofReal g * ENNReal.ofReal k + ENNReal.ofReal k ^ 2 =
      ENNReal.ofReal (g ^ 3 + g * k + k ^ 2) := by
    rw [← ENNReal.ofReal_mul hg0, ← ENNReal.ofReal_pow hk0,
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
  rw [hY]
  refine add_le_add le_rfl ?_
  rw [← ENNReal.ofReal_mul hC₂, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have : Cs * r ^ 3 ≤ Cs * (g ^ 3 + g * k + k ^ 2) := by
    have : 0 ≤ g * k := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) hCs0
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **Theorem `step3`**: the original third-order estimate (Expected result 7.1) for the
reapportioned activity `K^♯_{j+1}`. -/
theorem step3 (d : ℕ) (hd : 2 ≤ d) : ∃ (C₀ η : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧ 0 < η ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ : ℝ, 0 < ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓ C →
    ∀ (V W : Fam d L N) (K : Act d L N), InF j V → InF j W → (∀ b, ε (V b : Alg d L N) = 0) →
      InK2 j K → ∀ g : ℝ, 0 ≤ g → g ≤ ε₀ →
      Fnorm j ℓ V ≤ ENNReal.ofReal g → Fnorm j ℓ W ≤ ENNReal.ofReal (g ^ 2) →
      Knorm j ℓ A K ≤ ENNReal.ofReal ε₀ →
      ∀ U : Finset (Lam d L N), IsConn (j + 1) U →
        wnorm (j + 1) ℓ A U (Knew j C V W K U) ≤
          ENNReal.ofReal (C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3 + A ^ (-η))) * Knorm j ℓ A K +
          ENNReal.ofReal C₁ * (ENNReal.ofReal (g ^ 3) + ENNReal.ofReal g * Knorm j ℓ A K +
            Knorm j ℓ A K ^ 2) := by
  obtain ⟨C₀, η, L₀, hC₀, hη, h⟩ := step3_ts d hd
  refine ⟨C₀, η, L₀, hC₀, hη, fun L _ hL => ?_⟩
  obtain ⟨A₀, hA₀, h'⟩ := h L hL
  refine ⟨A₀, hA₀, fun A hA => ?_⟩
  obtain ⟨ε₀, C₁, hε, hC₁, h''⟩ := h' A hA
  exact ⟨ε₀, C₁, hε, hC₁, fun N j hj ℓ hℓ C hC =>
    h'' N j hj ℓ ℓ ℓ hℓ hℓ hℓ (by linarith) C hC⟩

end

end Step2
