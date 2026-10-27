import Step2.Last.LastSym

/-!
# The step at `j = N - 2`: the coupling vector of `V_{j+1}`

Copies of `CoupHyp` (`Step2.Coup.CoupStep`, Proposition `prop:C2`(ii)) and of `coupP_bound`
(`Step2.Coup.CoupFlow`) with `j + 2 < N` replaced by `j + 1 < N` and `L > 2^{d+4} + 4` (namespace
`Step2.Last`). The only change in the proofs: the localisation of `S` over a `(j+1)`-block uses
`region_small_L` at scale `j + 1 < N`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Matrix PolyAux

variable {d L N : ℕ} [NeZero L]

namespace Last

/-! ### The hypotheses -/

/-- The hypotheses of Proposition `prop:C2`(ii). -/
structure CoupHyp (j : ℕ) (ℓ : ℝ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V W : Fam d L N)
    (K : Act d L N) (κ : Coup) (c₀ δ : ℂ) : Prop where
  hd : 1 ≤ d
  hL8 : 2 ^ (d + 3) + 8 * d < L
  hj2 : j + 1 < N
  hLg : 2 ^ (d + 4) + 4 < L
  hC : GoodCov2 j ℓ C
  hCs : CSym C
  hCsym : ∀ x y, C x y = C y x
  hc₀ : ∀ x, C x x = c₀
  hδ : ∀ x e, C (x + dirVec e) x = c₀ + δ
  hδ' : ∀ x e, C x (x + dirVec e) = c₀ + δ
  hV : InF j V
  hW : InF j W
  hK : InK2 j K
  hVs : FamSym j V
  hWs : FamSym j W
  hKs : KSym j K
  hVJ : FamJ V
  hWJ : FamJ W
  hKJ : KJ j K
  hVκ : ∀ b, (V b : Alg d L N) = Vcoup κ (blockSet j b)

namespace CoupHyp

variable {j : ℕ} {ℓ : ℝ} {C : Matrix (Lam d L N) (Lam d L N) ℂ} {V W : Fam d L N}
  {K : Act d L N} {κ : Coup} {c₀ δ : ℂ} (H : CoupHyp j ℓ C V W K κ c₀ δ)
include H

theorem hL : 2 ^ (d + 3) ≤ L := by have := H.hL8; omega
theorem hjN : j + 1 < N := by have := H.hj2; omega
theorem hV0 : ∀ b, ε (V b : Alg d L N) = 0 := fun b => by rw [H.hVκ]; exact eps_Vcoup _ _

theorem symHyp {T : AffAut d L N} (hT : IsGen T) (hP1 : PresBlocks (j + 1) T) :
    SymHyp j ℓ C V W K T :=
  ⟨H.hd, H.hL, H.hj2, H.hLg, H.hC, H.hCs, H.hV, H.hW, H.hV0, H.hK, H.hVs, H.hWs, H.hKs, hT, hP1⟩

/-- The coefficients of `Q` are those of a coupling polynomial, the same on every block. -/
theorem Q2_coup : ∃ (r : ℂ) (κQ : Coup), ∀ b ∈ blockIdx (L := L) (N := N) j,
    (Q2 j K b : Alg d L N) = unif r (coupC κQ) (coupE κQ) (blockSet j b) := by
  have hj : j ≤ N := by have := H.hj2; omega
  have h0 := zero_mem_blockIdx (d := d) (L := L) (N := N) j
  obtain ⟨r, c, e, hQ0⟩ := Q2_unif K H.hjN (L := L) (N := N) (0 : Fin d → ℕ)
  -- the symmetries of the block `0`
  have hRm : ∀ m, autAlg (reflCenter (L := L) (N := N) j 0 m).E (unif r c e (blockSet j 0)) =
      unif r c e (blockSet j 0) := by
    intro m
    have hT := isGen_reflCenter (L := L) (N := N) j 0 m
    have hP := presBlocks_reflCenter (L := L) (N := N) hj h0 m
    have := AE_Q2_j H.hd H.hL H.hjN H.hK H.hKs hT hP h0
    rw [bmap_fix hT hj hP h0 (reflCenter_img hj 0 m)] at this
    have := congrArg Subtype.val this
    rwa [coe_AE, hQ0] at this
  have hPσ : ∀ σ, autAlg (permCorner (L := L) (N := N) j 0 σ).E (unif r c e (blockSet j 0)) =
      unif r c e (blockSet j 0) := by
    intro σ
    have hT := isGen_permCorner (L := L) (N := N) j 0 σ
    have hP := presBlocks_permCorner (L := L) (N := N) hj h0 σ
    have := AE_Q2_j H.hd H.hL H.hjN H.hK H.hKs hT hP h0
    rw [bmap_fix hT hj hP h0 (permCorner_img hj 0 σ)] at this
    have := congrArg Subtype.val this
    rwa [coe_AE, hQ0] at this
  have hJ : Jsym (unif r c e (blockSet (L := L) (N := N) j 0)) = unif r c e (blockSet j 0) := by
    rw [← hQ0]; exact mem_JS.1 (Q2_J H.hL8 H.hKJ 0)
  obtain ⟨κQ, hc, he⟩ := unif_sym_coeff hj H.hL8 (by have := H.hj2; omega) h0 ⟨0, H.hd⟩ hRm hPσ hJ
  refine ⟨r, κQ, fun b hb => ?_⟩
  -- transport from the block `0`
  have hT := IsGen.transl (d := d) (L := L) (N := N) (corner (L := L) (N := N) j b)
  have hP := presBlocks_transl_corner (L := L) (N := N) hj b
  have := AE_Q2_j H.hd H.hL H.hjN H.hK H.hKs hT hP h0
  rw [bmap_corner_zero hj hb] at this
  have := congrArg Subtype.val this
  rw [coe_AE, hQ0] at this
  rw [← this, hc, he]
  exact (unif_transl _ _ _ _ _).trans (by rw [transl_corner_img hj hb])

/-- The coefficients of `Loc_{B_+} S(B_+)` are those of a coupling polynomial, the same on every
`(j+1)`-block. -/
theorem LS_coup : ∃ κL : Coup, ∀ c ∈ blockIdx (L := L) (N := N) (j + 1),
    locCoef (blockSet (j + 1) c) (SX j C V W (blockSet (L := L) (N := N) (j + 1) c) : Alg d L N) =
      coupC κL ∧
    (fun i k => mu4 (base (blockSet (L := L) (N := N) (j + 1) c)) i k
      (SX j C V W (blockSet (j + 1) c) : Alg d L N) / (blockSet (L := L) (N := N) (j + 1) c).card) =
      coupE κL := by
  have hj1 : j + 1 ≤ N := by have := H.hj2; omega
  have h0 := zero_mem_blockIdx (d := d) (L := L) (N := N) (j + 1)
  have hF0mem' : (SX j C V W (blockSet (d := d) (L := L) (N := N) (j + 1) 0) : Alg d L N) ∈
      NX ((nbhd (j + 1) (blockSet (d := d) (L := L) (N := N) (j + 1) 0) : Finset (Lam d L N)) :
        Set (Lam d L N)) := by
    have e : blockSet (d := d) (L := L) (N := N) (j + 1) 0 = Bp (L := L) (N := N) j (0 : Fin d → ℕ) := by
      rw [Bp, clo_blockSet (zero_mem_blockIdx j)]
      congr 1; funext i; simp [par]
    rw [e]
    exact SX_mem' H.hd H.hL H.hjN H.hC H.hV H.hW (0 : Fin d → ℕ)
  set B0 := blockSet (L := L) (N := N) (j + 1) 0
  set F0 := (SX j C V W B0 : Alg d L N)
  have hsm0 := isSmall_blockSet_of_mem h0
  have hR0 := region_small_L H.hd H.hLg H.hj2 hsm0
  have hne0 := hsm0.2.1.1
  have hF0mem : F0 ∈ NX (nbhd (j + 1) B0 : Set (Lam d L N)) := hF0mem'
  -- invariance of `Loc_{B₀} F₀` under the stabiliser of `B₀`
  have hinv : ∀ {T : AffAut d L N}, IsGen T → PresBlocks (j + 1) T → T.img B0 = B0 →
      autAlg T.E (Loc2sX B0 F0) = Loc2sX B0 F0 := by
    intro T hT hP1 himg
    have HS := H.symHyp hT hP1
    rw [Loc2sX, Loc2sXY_aut hT hR0 hne0 B0 hF0mem, himg]
    have := HS.AE_SX B0
    rw [himg] at this
    have := congrArg Subtype.val this
    rw [coe_AE] at this
    rw [this]
  rw [Loc2X_eq_unif hne0] at hinv
  have hRm := fun m => hinv (isGen_reflCenter (L := L) (N := N) (j + 1) 0 m)
    (presBlocks_reflCenter hj1 h0 m) (reflCenter_img hj1 0 m)
  have hPσ := fun σ => hinv (isGen_permCorner (L := L) (N := N) (j + 1) 0 σ)
    (presBlocks_permCorner hj1 h0 σ) (permCorner_img hj1 0 σ)
  have hJ : Jsym (unif (ε F0) (locCoef B0 F0) (fun i k => mu4 (base B0) i k F0 / B0.card) B0) =
      unif (ε F0) (locCoef B0 F0) (fun i k => mu4 (base B0) i k F0 / B0.card) B0 := by
    rw [← Loc2X_eq_unif hne0]
    exact mem_JS.1 (Loc2E_J (Y := B0) (patch_of_small H.hL8 (by have := H.hj2; omega) hsm0) hne0
      (SX_J H.hCsym H.hVJ H.hWJ B0))
  obtain ⟨κL, hc, he⟩ := unif_sym_coeff hj1 H.hL8 (by have := H.hj2; omega) h0 ⟨0, H.hd⟩
    hRm hPσ hJ
  refine ⟨κL, fun c hc' => ?_⟩
  -- transport from the block `0`
  have hT := IsGen.transl (d := d) (L := L) (N := N) (corner (L := L) (N := N) (j + 1) c)
  have hP1 := presBlocks_transl_corner (L := L) (N := N) hj1 c
  have himg := transl_corner_img (L := L) (N := N) hj1 hc'
  have HS := H.symHyp hT hP1
  have hsmc := isSmall_blockSet_of_mem hc'
  have hpc := patch_of_small H.hL8 (by have := H.hj2; omega) hsmc
  have hnec := hsmc.2.1.1
  have hF := congrArg Subtype.val (HS.AE_SX B0)
  rw [coe_AE, himg] at hF
  have key : Loc2sX (blockSet (L := L) (N := N) (j + 1) c)
      (SX j C V W (blockSet (j + 1) c) : Alg d L N) =
      unif (ε F0) (coupC κL) (coupE κL) (blockSet (j + 1) c) := by
    rw [← hF, Loc2sX, ← himg, ← Loc2sXY_aut hT hR0 hne0 B0 hF0mem, ← Loc2sX,
      Loc2X_eq_unif hne0, hc, he, himg]
    exact (unif_transl _ _ _ _ _).trans (by rw [himg])
  rw [Loc2X_eq_unif hnec] at key
  have := unif_coeff hpc hnec key
  exact ⟨this.2.1, this.2.2⟩

/-- **`V_{j+1}(B) = V_{κp}(B)`, explicitly**: `κp = κ' - κ_Q' - κ_L`, where `κ_Q` is the
coupling vector of `Q` and `κ_L` that of `Loc S`. -/
theorem Vp_coup_explicit : ∃ (r : ℂ) (κQ κL : Coup),
    (∀ b ∈ blockIdx (L := L) (N := N) j,
      (Q2 j K b : Alg d L N) = unif r (coupC κQ) (coupE κQ) (blockSet j b)) ∧
    (∀ c ∈ blockIdx (L := L) (N := N) (j + 1),
      locCoef (blockSet (j + 1) c) (SX j C V W (blockSet (L := L) (N := N) (j + 1) c) :
        Alg d L N) = coupC κL ∧
      (fun i k => mu4 (base (blockSet (L := L) (N := N) (j + 1) c)) i k
        (SX j C V W (blockSet (j + 1) c) : Alg d L N) /
          (blockSet (L := L) (N := N) (j + 1) c).card) = coupE κL) ∧
    ∀ b ∈ blockIdx (L := L) (N := N) j,
      (Vp j C V W K b : Alg d L N) = Vcoup (κ.shift d c₀ δ - κQ.shift d c₀ δ - κL)
        (blockSet j b) := by
  obtain ⟨r, κQ, hQ⟩ := H.Q2_coup
  obtain ⟨κL, hLS⟩ := H.LS_coup
  refine ⟨r, κQ, κL, hQ, hLS, fun b hb => ?_⟩
  set B := blockSet (L := L) (N := N) j b
  obtain ⟨r₁, h₁⟩ := expLC_Vcoup H.hc₀ H.hδ H.hδ' κ B
  obtain ⟨r₂, h₂⟩ := expLC_Vcoup H.hc₀ H.hδ H.hδ' κQ B
  have hVpr : (Vpr C V b : Alg d L N) = Vcoup (κ.shift d c₀ δ) B + r₁ • 1 := by
    rw [Vpr, coe_EthE, H.hVκ, h₁]
  have hEQ : (EthE C (Q2 j K b) : Alg d L N) = r • 1 + Vcoup (κQ.shift d c₀ δ) B + r₂ • 1 := by
    rw [coe_EthE, hQ b hb, unif_eq_add_Vcoup, map_add, map_smul, expLC_one, h₂, add_assoc]
  have hpar : par L b ∈ blockIdx (L := L) (N := N) (j + 1) := CovHyp.par_mem hb
  have hBp : Bp (L := L) (N := N) j b = blockSet (j + 1) (par L b) := by
    rw [Bp, clo_blockSet hb]
  obtain ⟨hc, he⟩ := hLS _ hpar
  have hLSb : (LS j C V W b : Alg d L N) =
      ((ε (SX j C V W (Bp (L := L) (N := N) j b) : Alg d L N)) * B.card /
        (Bp (L := L) (N := N) j b).card) • 1 + Vcoup κL B := by
    rw [LS, coe_Loc2E, Loc2sXY_eq_unif, hBp, hc, he, unif_eq_add_Vcoup]
  set r₃ := (ε (SX j C V W (Bp (L := L) (N := N) j b) : Alg d L N)) * B.card /
    (Bp (L := L) (N := N) j b).card
  have hu : (uVp j C V W K b : Alg d L N) =
      Vcoup (κ.shift d c₀ δ - κQ.shift d c₀ δ - κL) B + (r₁ - r - r₂ - r₃) • 1 := by
    rw [uVp, AddSubgroupClass.coe_sub, AddSubgroupClass.coe_sub, hVpr, hEQ, hLSb, Vcoup_sub,
      Vcoup_sub]
    module
  have hup : up j C V W K b = r₁ - r - r₂ - r₃ := by
    rw [up, hu, map_add, eps_Vcoup, map_smul, map_one, smul_eq_mul, mul_one, zero_add]
  rw [Vp, AddSubgroupClass.coe_sub, Subalgebra.coe_algebraMap, hu, hup,
    Algebra.algebraMap_eq_smul_one, add_sub_cancel_right]

/-- **`V_{j+1}(B) = V_{κp}(B)` on every `j`-block**, with `κp` independent of `B`. -/
theorem Vp_coup : ∃ κp : Coup, ∀ b ∈ blockIdx (L := L) (N := N) j,
    (Vp j C V W K b : Alg d L N) = Vcoup κp (blockSet j b) := by
  obtain ⟨r, κQ, κL, -, -, h⟩ := H.Vp_coup_explicit
  exact ⟨_, h⟩

/-- **Proposition `prop:C2`(ii)**: `V_{j+1}(B_+) = V_{κp}(B_+)` on every `(j+1)`-block. -/
theorem Vnext2_coup : ∃ κp : Coup, ∀ c ∈ blockIdx (L := L) (N := N) (j + 1),
    (Vnext2 j C V W K c : Alg d L N) = Vcoup κp (blockSet (j + 1) c) := by
  obtain ⟨κp, h⟩ := H.Vp_coup
  refine ⟨κp, fun c hc => ?_⟩
  rw [Vnext2, AddSubmonoidClass.coe_finsetSum,
    sum_congr rfl fun b hb => h b (mem_blockIdx_of_mem_blocks hb)]
  simp only [Vcoup]
  rw [unif_sum _ 0 _ _ _ (pairwiseDisjoint_blockSet j _), mul_zero,
    biUnion_blocks (IsPolymer.of_succ (isPolymer_blockSet (j + 1) c))]

end CoupHyp


/-- **`V_{j+1} = V_{κp}` with `κp = κ' - κ_Q' - κ_L` and bounds on `κ_Q`, `κ_L`** (`d = 2`). The
input `V` is the coupling polynomial of `κ`; `κ_Q` is bounded by `‖K‖_j ≤ k`, `κ_L` by
`v² + w` with `‖V‖_j ≤ v`, `‖W‖_j ≤ w`. -/
theorem coupP_bound : ∃ Cq : ℝ, 0 ≤ Cq ∧ ∃ Cl : ℝ, 0 ≤ Cl ∧ ∃ cS : ℝ, 1 ≤ cS ∧
    ∀ (L : ℕ) [NeZero L], 2 ^ (2 + 3) + 8 * 2 < L → pauliL0 2 ≤ L →
    ∀ (N j : ℕ), j + 1 < N → 2 ^ (2 + 4) + 4 < L → ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ →
    ∀ C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ, GoodCov2 j ℓC C → CSym C →
      (∀ x y, C x y = C y x) →
    ∀ (κ : Coup) (W : Fam 2 L N) (K : Act 2 L N), W ∈ BSub (L := L) (N := N) j →
      K ∈ ASub (L := L) (N := N) j → ∀ A : ℝ, 1 ≤ A → ∀ v w k : ℝ, 0 ≤ v → 0 ≤ w → 0 ≤ k →
      v ≤ 1 → w ≤ 1 → k ≤ 1 →
      Fnorm j ℓ (VfamL (d := 2) (L := L) (N := N) j κ.toVec) ≤ ENNReal.ofReal v →
      Fnorm j ℓ W ≤ ENNReal.ofReal w → Knorm j ℓ A K ≤ ENNReal.ofReal k →
    ∃ (c₀ δ : ℂ) (κQ κL : Coup), (∀ x, C x x = c₀) ∧ (∀ x e, C (x + dirVec e) x = c₀ + δ) ∧
      (∀ c ∈ blockIdx (L := L) (N := N) (j + 1),
        (Vnext2 j C (VfamL j κ.toVec) W K c : Alg 2 L N) =
          Vcoup (κ.shift 2 c₀ δ - κQ.shift 2 c₀ δ - κL) (blockSet (j + 1) c)) ∧
      ‖κQ.z‖ ≤ Cq * (ℓ ^ 2)⁻¹ * (cS * (Cl * k)) ∧ ‖κQ.y‖ ≤ Cq * (ℓ ^ 2)⁻¹ * (cS * (Cl * k)) ∧
      ‖κQ.nu‖ ≤ Cq * (ℓ ^ 2)⁻¹ * (cS * (Cl * k)) / ((L : ℝ) ^ j) ^ 2 ∧
      ‖κQ.g‖ ≤ Cq * (ℓ ^ 4)⁻¹ * (cS * (Cl * k)) ∧
      ‖κL.z‖ ≤ Cq * (ℓ' ^ 2)⁻¹ * (Cl * ((L : ℝ) ^ 2 * BH.sig 2 L v w)) ∧
      ‖κL.y‖ ≤ Cq * (ℓ' ^ 2)⁻¹ * (Cl * ((L : ℝ) ^ 2 * BH.sig 2 L v w)) ∧
      ‖κL.nu‖ ≤ Cq * (ℓ' ^ 2)⁻¹ * (Cl * ((L : ℝ) ^ 2 * BH.sig 2 L v w)) /
        ((L : ℝ) ^ (j + 1)) ^ 2 ∧
      ‖κL.g‖ ≤ Cq * (ℓ' ^ 4)⁻¹ * (Cl * ((L : ℝ) ^ 2 * BH.sig 2 L v w)) ∧
      ∀ b ∈ blockIdx (L := L) (N := N) j, ∀ i₀ : Fin 2,
        cvec4 (blockSet (L := L) (N := N) j b) i₀
          (LS j C (VfamL j κ.toVec) W b : Alg 2 L N) = κL.toVec := by
  classical
  obtain ⟨Cq, hCq0, hCq⟩ := exists_coup_bound 2 (by norm_num)
  obtain ⟨Cl, hCl0, hloc⟩ := exists_Loc2sXY_bound 2 (by norm_num)
  obtain ⟨c, hc⟩ := card_small_containing 2
  refine ⟨Cq, hCq0, Cl, hCl0, c + 1, by linarith [Nat.cast_nonneg (α := ℝ) c], ?_⟩
  intro L _ hL8 hLp N j hj2 hLg ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC hCs hCsym κ W K hW hK A hA v w k hv0 hw0
    hk0 hv1 hw1 hk1 hVv hWw hKk
  have hjN : j + 1 < N := by omega
  have hj : j < N := by omega
  set V : Fam 2 L N := VfamL (d := 2) (L := L) (N := N) j κ.toVec
  have hVmem : V ∈ BSub (L := L) (N := N) j := VfamL_mem (by norm_num) hL8 hj _
  obtain ⟨c₀, δ, hc₀, hδ, hδ'⟩ := covProps (by norm_num) hCs hCsym
  have H' : CoupHyp j ℓC C V W K κ c₀ δ :=
    ⟨by norm_num, hL8, hj2, hLg, hC, hCs, hCsym, hc₀, hδ, hδ', hVmem.1, hW.1, hK.1, hVmem.2.2.1,
      hW.2.2.1, hK.2.2.1, hVmem.2.2.2.1, hW.2.2.2.1, hK.2.2.2.1, fun b => rfl⟩
  obtain ⟨rQ, κQ, κL, hQ, hLS, hVp⟩ := H'.Vp_coup_explicit
  have hLcv : ∀ b ∈ blockIdx (L := L) (N := N) j, ∀ i₀ : Fin 2,
      cvec4 (blockSet (L := L) (N := N) j b) i₀ (LS j C V W b : Alg 2 L N) = κL.toVec := by
    intro b hb i₀
    have hpar : PolyAux.par L b ∈ blockIdx (L := L) (N := N) (j + 1) := CovHyp.par_mem hb
    have hBp : Bp (L := L) (N := N) j b = blockSet (j + 1) (PolyAux.par L b) := by
      rw [Bp, clo_blockSet hb]
    obtain ⟨hc, he⟩ := hLS _ hpar
    have hsm := isSmall_blockSet_of_mem hb
    rw [LS, coe_Loc2E, Loc2sXY_eq_unif, hBp, hc, he]
    exact cvec4_unif (patch_of_small hL8 hj hsm) hsm.2.1.1 i₀ _ κL
  refine ⟨c₀, δ, κQ, κL, hc₀, hδ, fun c' hc' => ?_, ?_⟩
  · rw [Vnext2, AddSubmonoidClass.coe_finsetSum,
      sum_congr rfl fun b hb => hVp b (mem_blockIdx_of_mem_blocks hb)]
    simp only [Vcoup]
    rw [unif_sum _ 0 _ _ _ (pairwiseDisjoint_blockSet j _), mul_zero,
      biUnion_blocks (IsPolymer.of_succ (isPolymer_blockSet (j + 1) c'))]
  -- the bound on `κ_Q`: a `BH` for `(C, 0, 0, K)` with radius `k`
  have hT0 : ∀ i (ℓ₀ : ℝ), Tj 2 (L : ℝ) i ℓ₀ (0 : Alg 2 L N) = 0 := fun i ℓ₀ => Tj_zero _ _ _
  have hcount : ∀ b ∈ blockIdx (d := 2) (L := L) (N := N) j,
      (((smallSets (d := 2) (L := L) (N := N) j).filter (fun X => blockSet j b ⊆ X)).card : ℝ) ≤
        (c : ℝ) + 1 := fun b hb => by
    have h1 : ((smallSets (d := 2) (L := L) (N := N) j).filter
        (fun X => blockSet j b ⊆ X)).card ≤ c := by convert hc L N j b hb
    have h2 := Nat.cast_le (α := ℝ) |>.2 h1
    linarith
  have HQ : BH j ℓ ℓ' ℓC C 0 0 K A k Cl ((c : ℝ) + 1) :=
    { hd := by norm_num, hLp := hLp, hL8 := hL8, hjN := hjN, hℓ := hℓ, hℓ' := hℓ', hℓC := hℓC,
      hsum := hsum, hC := hC, hV := inF_zero j, hW := inF_zero j, hV0 := fun _ => by simp,
      hK := hK.1, hA := hA, hr := hk0, hr1 := hk1
      hVr := fun b hb => by simp [hT0]
      hWr := fun b hb => by simp [hT0]
      hKr := hKk, hCl := hCl0
      hloc := fun k' hk ℓ₀ hℓ₀ X Y hX hYX G hG => hloc L hL8 N k' hk X Y hX hYX G hG ℓ₀ hℓ₀
      hcS := by linarith [Nat.cast_nonneg (α := ℝ) c]
      hcount := hcount }
  have hQb := HQ.coupQ_le hCq (κQ := κQ) (rQ := rQ) hQ
  -- the bound on `κ_L`: a `BH` for `(C, V, W, 0)` with radius `1`
  have hK0 : InK2 j (0 : Act 2 L N) :=
    { loc := fun _ _ => zero_mem _, sym := fun _ _ => (isSym_iff_mem_SymS _).2 (zero_mem _) }
  have hvb : ∀ b ∈ blockIdx (L := L) (N := N) j, Tj 2 (L : ℝ) j ℓ (V b : Alg 2 L N) ≤
      ENNReal.ofReal v := fun b hb => (Tj_le_Fnorm V hb).trans hVv
  have hwb : ∀ b ∈ blockIdx (L := L) (N := N) j, Tj 2 (L : ℝ) j ℓ (W b : Alg 2 L N) ≤
      ENNReal.ofReal w := fun b hb => (Tj_le_Fnorm W hb).trans hWw
  have HL : BH j ℓ ℓ' ℓC C V W (0 : Act 2 L N) 1 1 Cl ((c : ℝ) + 1) :=
    { hd := by norm_num, hLp := hLp, hL8 := hL8, hjN := hjN, hℓ := hℓ, hℓ' := hℓ', hℓC := hℓC,
      hsum := hsum, hC := hC, hV := hVmem.1, hW := hW.1, hV0 := fun b => eps_VfamL j _ b,
      hK := hK0, hA := le_rfl, hr := zero_le_one, hr1 := le_rfl
      hVr := fun b hb => (hvb b hb).trans (ENNReal.ofReal_le_ofReal hv1)
      hWr := fun b hb => (hwb b hb).trans (ENNReal.ofReal_le_ofReal hw1)
      hKr := by rw [Knorm_zero]; exact zero_le
      hCl := hCl0
      hloc := fun k' hk ℓ₀ hℓ₀ X Y hX hYX G hG => hloc L hL8 N k' hk X Y hX hYX G hG ℓ₀ hℓ₀
      hcS := by linarith [Nat.cast_nonneg (α := ℝ) c]
      hcount := hcount }
  have hLb := HL.coupL_le hv0 hw0 hv1 hvb hwb hCq (κL := κL)
    (hLS 0 (zero_mem_blockIdx (j + 1)))
  -- the block sizes
  have hcard : ∀ i, i ≤ N → ((blockSet (L := L) (N := N) i (0 : Fin 2 → ℕ)).card : ℝ) =
      ((L : ℝ) ^ i) ^ 2 := fun i hi => by
    rw [card_blockSet hi (zero_mem_blockIdx i)]; push_cast; ring
  have hh : ∀ i, (0 : ℝ) < ((L : ℝ) ^ i) ^ 2 := fun i => by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  simp only at hQb hLb
  rw [hcard j hj.le] at hQb
  rw [hcard (j + 1) hjN.le] at hLb
  obtain ⟨q1, q2, q3, q4⟩ := hQb
  obtain ⟨l1, l2, l3, l4⟩ := hLb
  have hcanc : ∀ (a X : ℝ), 0 < X → a * X / X = a := fun a X hX => by field_simp
  have hh0 := hh j
  have hh1 := hh (j + 1)
  refine ⟨q1.trans (le_of_eq ?_), q2.trans (le_of_eq ?_), q3, q4.trans (le_of_eq ?_),
    l1.trans (le_of_eq ?_), l2.trans (le_of_eq ?_), l3, l4.trans (le_of_eq ?_), hLcv⟩ <;>
    field_simp


end Last

end

end Step2
