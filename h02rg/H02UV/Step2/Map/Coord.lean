import Step2.Map.Mem

/-!
# The coordinates at scale `j + 1` (Expected result `thm:closure`(a))

For a `(j+1)`-block `B_+ = B(c)`,

  `V_{j+1}(B_+) = ∑_{B ⊆ B_+} V_{j+1}(B)` (`Vnext2`),
  `𝒲_{j+1}(B_+) = ∏_{B ⊆ B_+} (1 + 𝒲_{j+1}(B)) - 1` (`Wnext2`).

* `Vnext2_inF`, `Wnext2_inF`: both are block families at scale `j + 1` (`InF (j+1)`), and
  `ε(V_{j+1}(B_+)) = 0` (`ε_Vnext2`).
* `Vnext2_le`, `Wnext2_le`: with `‖V‖_j ≤ v`, `‖𝒲‖_j ≤ w`, `‖K‖_j ≤ k` (all `≤ 1`),
  `‖V_{j+1}‖_{j+1} ≤ C(L) (v + w + k)` and `‖𝒲_{j+1}‖_{j+1} ≤ C(L) (v² + w)`.
-/

namespace Step2

noncomputable section

open Finset Grassmann Loc FRD Step

variable {d L N : ℕ} [NeZero L] {j : ℕ} {ℓ : ℝ} {C : Matrix (Lam d L N) (Lam d L N) ℂ}
  {V W : Fam d L N} {K : Act d L N}

/-! ### Membership -/

theorem Bp_sub_block {c b : Fin d → ℕ}
    (hb : b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c)) :
    Bp (L := L) (N := N) j b ⊆ blockSet (L := L) (N := N) (j + 1) c :=
  clo_subset (isPolymer_blockSet (j + 1) c)
    (blockSet_subset (IsPolymer.of_succ (isPolymer_blockSet (j + 1) c)) hb)

theorem NBp_le_block {c b : Fin d → ℕ}
    (hb : b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c)) :
    NBp (L := L) (N := N) j b ≤
      NX (nbhd (j + 1) (blockSet (L := L) (N := N) (j + 1) c) : Set (Lam d L N)) :=
  NX_mono (coe_subset.2 (nbhd_mono (Bp_sub_block hb)))

theorem Vnext2_inF (hd : 1 ≤ d) (hV : InF j V) : InF (j + 1) (Vnext2 j C V W K) where
  loc c := by
    rw [Vnext2, AddSubmonoidClass.coe_finsetSum]
    exact Subalgebra.sum_mem _ fun b hb => NBp_le_block hb
      (NB_le_NBp j b (Vp_mem hd hV (mem_blockIdx_of_mem_blocks hb)))
  sym c := by
    rw [isSym_iff_mem_SymS, Vnext2, AddSubmonoidClass.coe_finsetSum]
    exact Subalgebra.sum_mem _ fun b _ => Vp_sym hV b

theorem Wnext2_inF (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hjN : j + 1 < N) (hC : GoodCov2 j ℓ C)
    (hV : InF j V) (hW : InF j W) : InF (j + 1) (Wnext2 j C V W) where
  loc c := by
    refine mem_SE.1 ?_
    rw [Wnext2]
    exact sub_mem (prod_mem fun b hb => add_mem (one_mem _) (NBp_le_block hb
      (Wp_mem hd hL hjN hC hV hW (mem_blockIdx_of_mem_blocks hb)))) (one_mem _)
  sym c := by
    rw [isSym_iff_mem_SymS]
    refine mem_SE.1 ?_
    rw [Wnext2]
    exact sub_mem (prod_mem fun b _ => add_mem (one_mem _) (Wp_sym hV hW b)) (one_mem _)

/-! ### Bounds with separate radii -/

namespace BH

variable {ℓ' ℓC A r Cl cS : ℝ} (H : BH j ℓ ℓ' ℓC C V W K A r Cl cS) {v w k : ℝ}
  (hv0 : 0 ≤ v) (hw0 : 0 ≤ w) (hk0 : 0 ≤ k) (hv1 : v ≤ 1)
  (hv : ∀ b ∈ blockIdx (L := L) (N := N) j, Tj d (L : ℝ) j ℓ (V b : Alg d L N) ≤ ENNReal.ofReal v)
  (hw : ∀ b ∈ blockIdx (L := L) (N := N) j, Tj d (L : ℝ) j ℓ (W b : Alg d L N) ≤ ENNReal.ofReal w)
  (hk : Knorm j ℓ A K ≤ ENNReal.ofReal k)
include H

include hv in
theorem Vpr_le' {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    Tj d (L : ℝ) (j + 1) ℓ' (Vpr C V b : Alg d L N) ≤ ENNReal.ofReal (Q1 d * v) := by
  rw [Vpr]
  exact tj_of (by linarith [H.hQ1]) (EthE_block_le2 H.hd H.hLp H.hj H.hℓ' H.hℓC H.hsum H.hC (H.hV.loc b))
    (hv b hb)

include hv hv0 in
theorem FCE_pair_le' {b b' : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j)
    (hb' : b' ∈ blockIdx (L := L) (N := N) j) :
    Tj d (L : ℝ) (j + 1) ℓ' (FCE C (Vpr C V b) (Vpr C V b') : Alg d L N) ≤
      ENNReal.ofReal (2 * (Q1 d * v) ^ 2) := by
  have e : ∀ b, (Vpr C V b : Alg d L N) = ECC C (theta (V b : Alg d L N)) := fun b => by
    rw [Vpr, coe_EthE, ECC_theta]
  have hq : 0 ≤ Q1 d * v := mul_nonneg (by linarith [H.hQ1]) hv0
  have h2 : ∀ b ∈ blockIdx (L := L) (N := N) j,
      Tj d (L : ℝ) (j + 1) (2 * ℓ) (V b : Alg d L N) ≤ ENNReal.ofReal (Q1 d * v) := by
    intro b hb
    rw [ENNReal.ofReal_mul (by linarith [H.hQ1])]
    exact (Tj2_block_le H.hd H.hLp H.hj H.hℓ (H.hV.loc b)).trans (mul_le_mul_left' (hv b hb) _)
  rw [coe_FCE, e, e]
  refine (FC_succ_le2 H.hℓ' H.hℓC H.hsum H.hC _ _).trans ?_
  rw [sq, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul hq, ENNReal.ofReal_ofNat]
  gcongr
  · exact h2 b hb
  · exact h2 b' hb'

include hv hw hv0 hw0 hv1 in
theorem Sb_le' {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    Tj d (L : ℝ) (j + 1) ℓ' (Sb j C V W b : Alg d L N) ≤
      ENNReal.ofReal (cNear d L * Q1 d ^ 2 * v ^ 2 + Q1 d * w) := by
  have hQ := H.hQ1
  rw [Sb, FCE_VprL_eq H.hjN H.hC H.hV b]
  have h1 := tn_sum_const (E := Dir d) (p := pPhi d) (h := (L : ℝ) ^ (j + 1)) (ℓ := ℓ')
    (nearSet (L := L) (N := N) j b) (fun b' => FCE C (Vpr C V b) (Vpr C V b'))
    (r := 2 * (Q1 d * v) ^ 2) (by positivity)
    (fun b' hb' => H.FCE_pair_le' hv0 hv hb (mem_filter.1 hb').1)
  have hn : ((nearSet (L := L) (N := N) j b).card : ℝ) ≤ cNear d L := by
    unfold cNear; exact_mod_cast card_nearSet_le H.hj.le b hb
  have h2 : Tj d (L : ℝ) (j + 1) ℓ' (((1 / 2 : ℂ) • ∑ b' ∈ nearSet (L := L) (N := N) j b,
      FCE C (Vpr C V b) (Vpr C V b') : EvR (Lam d L N)) : Alg d L N) ≤
      ENNReal.ofReal (cNear d L * Q1 d ^ 2 * v ^ 2) := by
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
  have h3 : Tj d (L : ℝ) (j + 1) ℓ' (EthE C (W b) : Alg d L N) ≤ ENNReal.ofReal (Q1 d * w) :=
    tj_of (by linarith) (EthE_block_le2 H.hd H.hLp H.hj H.hℓ' H.hℓC H.hsum H.hC (H.hW.loc b)) (hw b hb)
  exact tn_addE (mul_nonneg (mul_nonneg H.hcNear (sq_nonneg _)) (sq_nonneg _))
    (mul_nonneg (by linarith) hw0) h2 h3

/-- The quadratic radius `σ = n Q₁² v² + Q₁ w` of `S(B)`. -/
def sig (d L : ℕ) (v w : ℝ) : ℝ := cNear d L * Q1 d ^ 2 * v ^ 2 + Q1 d * w

omit H in
theorem sig_nonneg (hd : 1 ≤ d) (x y : ℝ) (hy : 0 ≤ y) : 0 ≤ sig d L x y :=
  add_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) (sq_nonneg _))
    (mul_nonneg (by linarith [one_le_Q1 hd]) hy)

include hv hw hv0 hw0 hv1 in
theorem SX_le' (b : Fin d → ℕ) :
    Tj d (L : ℝ) (j + 1) ℓ' (SX j C V W (Bp (L := L) (N := N) j b) : Alg d L N) ≤
      ENNReal.ofReal ((L : ℝ) ^ d * sig d L v w) := by
  have := H.hcNear
  have hs0 : 0 ≤ sig d L v w := sig_nonneg H.hd v w hw0
  rw [SX]
  refine (tn_sum_const (E := Dir d) (p := pPhi d) _ _ hs0 fun b'' hb'' =>
    H.Sb_le' hv0 hw0 hv1 hv hw (mem_blockIdx_of_mem_blocks hb'')).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have : ((blocks j (Bp (L := L) (N := N) j b)).card : ℝ) ≤ (L : ℝ) ^ d := by
    exact_mod_cast H.nb_Bp_le b
  gcongr

include hv hw hv0 hw0 hv1 in
theorem LS_le' {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    Tj d (L : ℝ) (j + 1) ℓ' (LS j C V W b : Alg d L N) ≤
      ENNReal.ofReal (Cl * (L : ℝ) ^ d * sig d L v w) := by
  have := H.hcNear
  have hs0 : 0 ≤ sig d L v w := sig_nonneg H.hd v w hw0
  rw [LS, coe_Loc2E]
  refine (H.hloc (j + 1) H.hjN ℓ' H.hℓ' _ _ (isSmall_clo (isSmall_blockSet_of_mem hb))
    (subset_clo j _) _ (SX_mem' H.hd H.hL8' H.hjN H.hC H.hV H.hW b)).trans ?_
  have hSX : Tj d (L : ℝ) (j + 1) ℓ' (SX j C V W (Bp (L := L) (N := N) j b) : Alg d L N) ≤
      ENNReal.ofReal ((L : ℝ) ^ d * sig d L v w) := by
    rw [SX]
    refine (tn_sum_const (E := Dir d) (p := pPhi d) _ _ hs0 fun b'' hb'' =>
      H.Sb_le' hv0 hw0 hv1 hv hw (mem_blockIdx_of_mem_blocks hb'')).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have : ((blocks j (Bp (L := L) (N := N) j b)).card : ℝ) ≤ (L : ℝ) ^ d := by
      exact_mod_cast H.nb_Bp_le b
    gcongr
  refine (mul_le_mul_left' hSX _).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul H.hCl]; congr 1; ring

include hk hk0 in
theorem Q2_le' {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    Tj d (L : ℝ) (j + 1) ℓ' (EthE C (Q2 j K b) : Alg d L N) ≤
      ENNReal.ofReal (Q1 d * (cS * (Cl * k))) := by
  classical
  have hCl := H.hCl
  refine tj_of (by linarith [H.hQ1]) (EthE_block_le2 H.hd H.hLp H.hj H.hℓ' H.hℓC H.hsum H.hC
    (Q2_mem_NB H.hd hb)) ?_
  rw [Q2, if_pos H.hjN]
  refine (tn_sum_const (E := Dir d) (p := pPhi d) _ _ (r := Cl * k) (by positivity)
    fun X hX => ?_).trans (ENNReal.ofReal_le_ofReal ?_)
  · obtain ⟨hs, hbX⟩ := mem_smallSets_filter.1 hX
    have hc : IsConn j X := ⟨hs.1, hs.2.1⟩
    rw [coe_Loc2E]
    refine (H.hloc j H.hj ℓ H.hℓ X _ hs hbX _ (H.hK.loc X hc)).trans ?_
    rw [ENNReal.ofReal_mul hCl]
    exact mul_le_mul_left' ((Tj_le_Knorm H.hA hc).trans hk) _
  · exact mul_le_mul_of_nonneg_right (H.hcount b hb) (by positivity)

/-- The linear radius of `V_{j+1}(B)`. -/
def rho (d L : ℕ) (Cl cS v w k : ℝ) : ℝ :=
  Q1 d * v + Q1 d * (cS * (Cl * k)) + Cl * (L : ℝ) ^ d * sig d L v w

include hv hw hk hv0 hw0 hk0 hv1 in
theorem Vp_le' {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    Tj d (L : ℝ) (j + 1) ℓ' (Vp j C V W K b : Alg d L N) ≤
      ENNReal.ofReal (2 * rho d L Cl cS v w k) := by
  have := H.hQ1; have := H.hcNear; have := H.hCl; have := H.hcS0
  have hs0 : 0 ≤ sig d L v w := sig_nonneg H.hd v w hw0
  have hρ0 : 0 ≤ rho d L Cl cS v w k := by
    unfold rho
    have := mul_nonneg (mul_nonneg H.hCl (pow_nonneg H.hL0.le d)) hs0
    have h2 : 0 ≤ Q1 d * v := mul_nonneg (by linarith) hv0
    have h3 : 0 ≤ Q1 d * (cS * (Cl * k)) := mul_nonneg (by linarith) (mul_nonneg H.hcS0 (mul_nonneg H.hCl hk0))
    linarith
  have hu : Tj d (L : ℝ) (j + 1) ℓ' (uVp j C V W K b : Alg d L N) ≤
      ENNReal.ofReal (rho d L Cl cS v w k) := by
    rw [uVp]
    exact (tn_subE (by positivity) (by positivity) (tn_subE (by positivity) (by positivity)
      (H.Vpr_le' hv hb) (H.Q2_le' hk0 hk hb)) (H.LS_le' hv0 hw0 hv1 hv hw hb)).trans
      (ENNReal.ofReal_le_ofReal (le_of_eq (by unfold rho; ring)))
  rw [Vp]
  refine (tn_subE hρ0 hρ0 hu ?_).trans (ENNReal.ofReal_le_ofReal (by linarith))
  rw [Subalgebra.coe_algebraMap]
  refine (tNorm_algebraMap_le H.hh' H.hℓ' _).trans (ENNReal.ofReal_le_ofReal ?_)
  have h := (abs_ε_le (E := Dir d) (p := pPhi d) H.hh' H.hℓ' _).trans hu
  exact (ENNReal.ofReal_le_ofReal_iff hρ0).1 h

include hv hw hv0 hw0 hv1 in
theorem Wp_le' {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    Tj d (L : ℝ) (j + 1) ℓ' (Wp j C V W b : Alg d L N) ≤
      ENNReal.ofReal ((1 + Cl * (L : ℝ) ^ d) * sig d L v w) := by
  have := H.hQ1; have := H.hcNear; have := H.hCl; have := H.hL0
  have hs0 : 0 ≤ sig d L v w := sig_nonneg H.hd v w hw0
  rw [Wp]
  exact (tn_subE hs0 (by positivity) (H.Sb_le' hv0 hw0 hv1 hv hw hb)
    (H.LS_le' hv0 hw0 hv1 hv hw hb)).trans (ENNReal.ofReal_le_ofReal (le_of_eq (by ring)))

end BH

theorem one_add_pow_sub_one_le {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) :
    (1 + δ) ^ n - 1 ≤ n * δ * (1 + δ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : 1 ≤ (1 + δ) ^ n := one_le_pow₀ (by linarith)
    have h1' : 1 ≤ (1 + δ) ^ n * (1 + δ) := by nlinarith
    push_cast
    rw [pow_succ]
    have e : (1 + δ) ^ n * (1 + δ) - 1 = (1 + δ) * ((1 + δ) ^ n - 1) + δ := by ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left ih (by linarith : (0 : ℝ) ≤ 1 + δ),
      mul_le_mul_of_nonneg_left h1' hδ]

/-! ### The bounds -/

set_option maxHeartbeats 1000000 in
/-- **`thm:closure`(a), bounds.** -/
theorem coords_bound_ts (d : ℕ) (hd : 1 ≤ d) : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓC C →
    ∀ (V W : Fam d L N) (K : Act d L N), InF j V → InF j W → (∀ b, ε (V b : Alg d L N) = 0) →
      InK2 j K → ∀ A : ℝ, 1 ≤ A → ∀ v w k : ℝ, 0 ≤ v → 0 ≤ w → 0 ≤ k → v ≤ 1 → w ≤ 1 → k ≤ 1 →
      Fnorm j ℓ V ≤ ENNReal.ofReal v → Fnorm j ℓ W ≤ ENNReal.ofReal w →
      Knorm j ℓ A K ≤ ENNReal.ofReal k →
      Fnorm (j + 1) ℓ' (Vnext2 j C V W K) ≤ ENNReal.ofReal (C₁ * (v + w + k)) ∧
      Fnorm (j + 1) ℓ' (Wnext2 j C V W) ≤ ENNReal.ofReal (C₁ * (v ^ 2 + w)) := by
  classical
  obtain ⟨Cl, hCl0, hloc⟩ := exists_Loc2sXY_bound d hd
  obtain ⟨c, hc⟩ := card_small_containing d
  refine ⟨max (2 ^ (d + 3) + 8 * d + 1) ⌈pauliL0 d⌉₊, ?_⟩
  intro L _ hL
  have hL8 : 2 ^ (d + 3) + 8 * d < L :=
    lt_of_lt_of_le (Nat.lt_succ_self _) (le_trans (le_max_left _ _) hL)
  have hLp : pauliL0 d ≤ L := (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hL)
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set cS : ℝ := c + 1 with hcSdef
  have hcS1 : 1 ≤ cS := by rw [hcSdef]; linarith [Nat.cast_nonneg (α := ℝ) c]
  have hQ := one_le_Q1 hd
  have hN0 : 0 ≤ cNear d L := Nat.cast_nonneg _
  set n : ℝ := (L : ℝ) ^ d with hn
  have hn0 : 0 ≤ n := by positivity
  -- the `V` constant
  set Cv : ℝ := 2 * n * (Q1 d + Q1 d * (cS * Cl) + Cl * n * (cNear d L * Q1 d ^ 2 + Q1 d))
    with hCv
  -- the `W` constant
  set Cσ : ℝ := (1 + Cl * n) * (cNear d L * Q1 d ^ 2 + Q1 d) with hCσ
  have hCσ0 : 0 ≤ Cσ := by positivity
  set Cw : ℝ := n * Cσ * (1 + Cσ) ^ (L ^ d) with hCw
  refine ⟨Cv + Cw, by positivity, ?_⟩
  intro N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC V W K hV hW hV0 hK A hA v w k hv0 hw0 hk0 hv1 hw1 hk1 hVv hWw hKk
  have hvb : ∀ b ∈ blockIdx (L := L) (N := N) j, Tj d (L : ℝ) j ℓ (V b : Alg d L N) ≤
      ENNReal.ofReal v := fun b hb => (le_iSup₂ (f := fun b (_ : b ∈ blockIdx (L := L) (N := N) j) =>
        Tj d (L : ℝ) j ℓ (V b : Alg d L N)) b hb).trans hVv
  have hwb : ∀ b ∈ blockIdx (L := L) (N := N) j, Tj d (L : ℝ) j ℓ (W b : Alg d L N) ≤
      ENNReal.ofReal w := fun b hb => (le_iSup₂ (f := fun b (_ : b ∈ blockIdx (L := L) (N := N) j) =>
        Tj d (L : ℝ) j ℓ (W b : Alg d L N)) b hb).trans hWw
  have H : BH j ℓ ℓ' ℓC C V W K A 1 Cl cS :=
    { hd := hd, hLp := hLp, hL8 := hL8, hjN := hjN, hℓ := hℓ, hℓ' := hℓ', hℓC := hℓC, hsum := hsum, hC := hC, hV := hV, hW := hW,
      hV0 := hV0, hK := hK, hA := hA, hr := zero_le_one, hr1 := le_rfl
      hVr := fun b hb => (hvb b hb).trans (ENNReal.ofReal_le_ofReal hv1)
      hWr := fun b hb => (hwb b hb).trans (ENNReal.ofReal_le_ofReal hw1)
      hKr := hKk.trans (ENNReal.ofReal_le_ofReal hk1)
      hCl := hCl0
      hloc := fun k hk ℓ₀ hℓ₀ X Y hX hYX F hF => hloc L hL8 N k hk X Y hX hYX F hF ℓ₀ hℓ₀
      hcS := hcS1
      hcount := fun b hb => by
        have h1 : ((smallSets (d := d) (L := L) (N := N) j).filter
            (fun X => blockSet j b ⊆ X)).card ≤ c := by convert hc L N j b hb
        have h2 := Nat.cast_le (α := ℝ) |>.2 h1
        linarith }
  have hcard : ∀ c' : Fin d → ℕ, ((blocks j (blockSet (L := L) (N := N) (j + 1) c')).card : ℝ) ≤ n :=
    fun c' => by
      have := nb_blockSet_succ_le (L := L) (N := N) j c'
      unfold nb at this; rw [hn]; exact_mod_cast this
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
  refine ⟨iSup₂_le fun c' _ => ?_, iSup₂_le fun c' _ => ?_⟩
  · -- `V_{j+1}`
    rw [Vnext2]
    have hρ : ∀ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
        Tj d (L : ℝ) (j + 1) ℓ' (Vp j C V W K b : Alg d L N) ≤
          ENNReal.ofReal (2 * BH.rho d L Cl cS v w k) := fun b hb =>
      H.Vp_le' hv0 hw0 hk0 hv1 hvb hwb hKk (mem_blockIdx_of_mem_blocks hb)
    have hρ0 : 0 ≤ BH.rho d L Cl cS v w k := by
      unfold BH.rho
      have := mul_nonneg (mul_nonneg hCl0 (pow_nonneg hL0.le d)) (BH.sig_nonneg (L := L) hd v w hw0)
      have h2 : 0 ≤ Q1 d * v := mul_nonneg (by linarith) hv0
      have h3 : 0 ≤ Q1 d * (cS * (Cl * k)) :=
        mul_nonneg (by linarith) (mul_nonneg (by linarith) (mul_nonneg hCl0 hk0))
      linarith
    refine (tn_sum_const (E := Dir d) (p := pPhi d) _ _ (by positivity) hρ).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have hrho : BH.rho d L Cl cS v w k ≤
        (Q1 d + Q1 d * (cS * Cl) + Cl * n * (cNear d L * Q1 d ^ 2 + Q1 d)) * (v + w + k) := by
      unfold BH.rho
      have h1 : BH.sig d L v w ≤ (cNear d L * Q1 d ^ 2 + Q1 d) * (v + w + k) := by
        refine hsig.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
        nlinarith
      have h2 : Cl * n * BH.sig d L v w ≤ Cl * n * ((cNear d L * Q1 d ^ 2 + Q1 d) * (v + w + k)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have h3 : Q1 d * (cS * (Cl * k)) ≤ Q1 d * (cS * Cl) * (v + w + k) := by
        have : 0 ≤ Q1 d * (cS * Cl) := by positivity
        nlinarith
      have h4 : Q1 d * v ≤ Q1 d * (v + w + k) := by nlinarith
      nlinarith
    have hCw0 : 0 ≤ Cw := by positivity
    calc ((blocks j (blockSet (L := L) (N := N) (j + 1) c')).card : ℝ) *
          (2 * BH.rho d L Cl cS v w k)
        ≤ n * (2 * ((Q1 d + Q1 d * (cS * Cl) + Cl * n * (cNear d L * Q1 d ^ 2 + Q1 d)) *
            (v + w + k))) := by gcongr; exact hcard c'
      _ = Cv * (v + w + k) := by rw [hCv]; ring
      _ ≤ (Cv + Cw) * (v + w + k) := by nlinarith
  · -- `𝒲_{j+1}`
    rw [Wnext2]
    set s := blocks j (blockSet (L := L) (N := N) (j + 1) c')
    have hδ0 : 0 ≤ (1 + Cl * (L : ℝ) ^ d) * BH.sig d L v w :=
      mul_nonneg (by positivity) (BH.sig_nonneg (L := L) hd v w hw0)
    have hP := tn_prod_sub_one (E := Dir d) (p := pPhi d) H.hh' hℓ' s
      (fun b => 1 + Wp j C V W b) hδ0 (fun b hb => by
        simp only [add_sub_cancel_left]
        exact H.Wp_le' hv0 hw0 hv1 hvb hwb (mem_blockIdx_of_mem_blocks hb))
    refine hP.trans (ENNReal.ofReal_le_ofReal ?_)
    set δ := (1 + Cl * (L : ℝ) ^ d) * BH.sig d L v w
    have hδ : δ ≤ Cσ * (v ^ 2 + w) := by
      rw [hCσ, mul_assoc]; exact mul_le_mul_of_nonneg_left hsig (by positivity)
    have hδ1 : δ ≤ Cσ := by
      rw [hCσ]; exact mul_le_mul_of_nonneg_left hsig1 (by positivity)
    have h1 := one_add_pow_sub_one_le hδ0 s.card
    have hs : (s.card : ℝ) ≤ n := hcard c'
    have hsn : s.card ≤ L ^ d := nb_blockSet_succ_le j c'
    have h2 : (1 + δ) ^ s.card ≤ (1 + Cσ) ^ (L ^ d) :=
      (pow_le_pow_left₀ (by linarith) (by linarith) _).trans
        (pow_le_pow_right₀ (by linarith) hsn)
    have hCv0 : 0 ≤ Cv := by positivity
    have hvw : 0 ≤ v ^ 2 + w := by positivity
    calc (1 + δ) ^ s.card - 1 ≤ s.card * δ * (1 + δ) ^ s.card := h1
      _ ≤ n * (Cσ * (v ^ 2 + w)) * (1 + Cσ) ^ (L ^ d) := by gcongr
      _ = Cw * (v ^ 2 + w) := by rw [hCw]; ring
      _ ≤ (Cv + Cw) * (v ^ 2 + w) := by nlinarith

set_option maxHeartbeats 1000000 in
/-- **`thm:closure`(a), bounds.** -/
theorem coords_bound (d : ℕ) (hd : 1 ≤ d) : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ : ℝ, 0 < ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓ C →
    ∀ (V W : Fam d L N) (K : Act d L N), InF j V → InF j W → (∀ b, ε (V b : Alg d L N) = 0) →
      InK2 j K → ∀ A : ℝ, 1 ≤ A → ∀ v w k : ℝ, 0 ≤ v → 0 ≤ w → 0 ≤ k → v ≤ 1 → w ≤ 1 → k ≤ 1 →
      Fnorm j ℓ V ≤ ENNReal.ofReal v → Fnorm j ℓ W ≤ ENNReal.ofReal w →
      Knorm j ℓ A K ≤ ENNReal.ofReal k →
      Fnorm (j + 1) ℓ (Vnext2 j C V W K) ≤ ENNReal.ofReal (C₁ * (v + w + k)) ∧
      Fnorm (j + 1) ℓ (Wnext2 j C V W) ≤ ENNReal.ofReal (C₁ * (v ^ 2 + w)) := by
  obtain ⟨L₀, h⟩ := coords_bound_ts d hd
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨C₁, hC₁, h'⟩ := h L hL
  exact ⟨C₁, hC₁, fun N j hj ℓ hℓ C hC => h' N j hj ℓ ℓ ℓ hℓ hℓ hℓ (by linarith) C hC⟩

end

end Step2
