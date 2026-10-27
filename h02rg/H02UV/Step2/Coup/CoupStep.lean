import Step2.Coup.CoupClass

/-!
# The coupling space is closed under the step (`h02uv-outline.tex`, Proposition `prop:C2`(ii))

If `V(B) = V_κ(B)` on every `j`-block, `C` is symmetric, invariant under all lattice symmetries
and `C(x,x) = c₀`, `C(x+e,x) = C(x,x+e) = c₀ + δ`, and `𝒲`, `K` are covariant under lattice
symmetries and `J`-invariant, then `V_{j+1}(B_+) = V_{κp}(B_+)` on every `(j+1)`-block, for one
`κp` (`Vnext2_coup`).
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Matrix PolyAux

variable {d L N : ℕ} [NeZero L]

/-! ### Arithmetic of coupling vectors -/

instance : Sub Coup := ⟨fun a b => ⟨a.z - b.z, a.y - b.y, a.nu - b.nu, a.g - b.g⟩⟩

@[simp] theorem Coup.sub_z (κ κ' : Coup) : (κ - κ').z = κ.z - κ'.z := rfl
@[simp] theorem Coup.sub_y (κ κ' : Coup) : (κ - κ').y = κ.y - κ'.y := rfl
@[simp] theorem Coup.sub_nu (κ κ' : Coup) : (κ - κ').nu = κ.nu - κ'.nu := rfl
@[simp] theorem Coup.sub_g (κ κ' : Coup) : (κ - κ').g = κ.g - κ'.g := rfl

theorem coupC_sub (κ κ' : Coup) :
    coupC (d := d) (κ - κ') = fun M => coupC κ M - coupC κ' M := by
  funext M
  cases M with
  | c => simp [coupC]
  | a1 => simp [coupC]
  | b1 => simp [coupC]
  | a2 s => by_cases h : s.IsDiag <;> simp [coupC, h] <;> ring
  | b2 s => by_cases h : s.IsDiag <;> simp [coupC, h] <;> ring
  | m2 i k => by_cases h : i = k <;> simp [coupC, h]

theorem coupE_sub (κ κ' : Coup) :
    coupE (d := d) (κ - κ') = fun i k => coupE κ i k - coupE κ' i k := by
  funext i k
  by_cases h : i = k <;> simp [coupE, h]

theorem unif_sub (κ κ' : ℂ) (c c' : Mono d → ℂ) (e e' : Fin d → Fin d → ℂ)
    (Y : Finset (Lam d L N)) :
    unif κ c e Y - unif κ' c' e' Y =
      unif (κ - κ') (fun M => c M - c' M) (fun i k => e i k - e' i k) Y := by
  simp only [unif, sub_smul, sum_sub_distrib]
  abel

theorem unif_add (κ κ' : ℂ) (c c' : Mono d → ℂ) (e e' : Fin d → Fin d → ℂ)
    (Y : Finset (Lam d L N)) :
    unif κ c e Y + unif κ' c' e' Y =
      unif (κ + κ') (fun M => c M + c' M) (fun i k => e i k + e' i k) Y := by
  simp only [unif, add_smul, sum_add_distrib]
  abel

theorem unif_finset_sum {ι : Type*} (s : Finset ι) (κ : ι → ℂ) (c : ι → Mono d → ℂ)
    (e : ι → Fin d → Fin d → ℂ) (Y : Finset (Lam d L N)) :
    ∑ a ∈ s, unif (κ a) (c a) (e a) Y =
      unif (∑ a ∈ s, κ a) (fun M => ∑ a ∈ s, c a M) (fun i k => ∑ a ∈ s, e a i k) Y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [unif]
  | insert a s ha ih =>
    rw [sum_insert ha, ih, unif_add]
    simp only [sum_insert ha]

theorem Vcoup_sub (κ κ' : Coup) (Y : Finset (Lam d L N)) :
    Vcoup (κ - κ') Y = Vcoup κ Y - Vcoup κ' Y := by
  rw [Vcoup, Vcoup, Vcoup, unif_sub, coupC_sub, coupE_sub, sub_zero]

theorem eps_Vcoup (κ : Coup) (Y : Finset (Lam d L N)) : ε (Vcoup κ Y) = 0 := eps_unif _ _ _ _

theorem unif_eq_add_Vcoup (r : ℂ) (κ : Coup) (Y : Finset (Lam d L N)) :
    unif r (coupC κ) (coupE κ) Y = r • (1 : Alg d L N) + Vcoup κ Y := by
  rw [Vcoup, unif, unif, zero_smul, zero_add, add_assoc]

theorem expLC_one (C : Matrix (Lam d L N) (Lam d L N) ℂ) : expLC C (1 : Alg d L N) = 1 := by
  rw [expLC_of_cube C (by rw [LopC_one, map_zero, map_zero]), LopC_one, map_zero, smul_zero,
    add_zero, add_zero]

/-! ### The covariance hypotheses -/

/-- For a symmetric covariance invariant under the lattice symmetries, `C(x,x) = c₀` and
`C(x+e,x) = C(x,x+e) = c₀ + δ` for all unit directions `e`. -/
theorem covProps (hd : 1 ≤ d) {C : Matrix (Lam d L N) (Lam d L N) ℂ} (hCs : CSym C)
    (hCsym : ∀ x y, C x y = C y x) :
    ∃ c₀ δ : ℂ, (∀ x, C x x = c₀) ∧ (∀ x e, C (x + dirVec e) x = c₀ + δ) ∧
      (∀ x e, C x (x + dirVec e) = c₀ + δ) := by
  set i₀ : Fin d := ⟨0, hd⟩
  have hperm : ∀ i : Fin d, C (dirVec (Sum.inl i)) 0 = C (dirVec (Sum.inl i₀)) 0 := by
    intro i
    have h2 := hCs (AffAut.perm (Equiv.swap i₀ i)) (IsGen.perm _) (dirVec (Sum.inl i₀)) 0
    have e1 : (AffAut.perm (L := L) (N := N) (Equiv.swap i₀ i)).E (dirVec (Sum.inl i₀)) =
        dirVec (Sum.inl i) := by
      funext k
      show co (dirVec (Sum.inl i₀) : Lam d L N) ((Equiv.swap i₀ i).symm k) = _
      simp only [co, dirVec, Pi.single_apply, Equiv.symm_swap]
      by_cases hk : k = i
      · subst hk; simp
      · rw [if_neg hk, if_neg]; intro h; apply hk
        have := congrArg (Equiv.swap i₀ i) h
        simpa using this
    have e0 : (AffAut.perm (L := L) (N := N) (Equiv.swap i₀ i)).E 0 = 0 :=
      map_zero (permT (L := L) (N := N) (Equiv.swap i₀ i))
    rw [e1, e0] at h2; exact h2
  have key : ∀ x e, C (x + dirVec e) x = C (dirVec (Sum.inl i₀)) 0 := by
    intro x e
    have h1 := hCs (AffAut.transl x) (IsGen.transl x) (dirVec e) 0
    simp only [AffAut.transl, Equiv.coe_addRight, zero_add] at h1
    rw [add_comm, h1]
    rcases e with i | i
    · exact hperm i
    · have h3 := hCs (AffAut.refl i) (IsGen.refl i) (dirVec (Sum.inl i)) 0
      have e1 : (AffAut.refl (L := L) (N := N) i).E (dirVec (Sum.inl i)) = dirVec (Sum.inr i) := by
        funext k
        show (if k = i then -co (dirVec (Sum.inl i) : Lam d L N) k
          else co (dirVec (Sum.inl i) : Lam d L N) k) = _
        by_cases hk : k = i <;> simp [hk, co, dirVec, Pi.single_apply]
      have e0 : (AffAut.refl (L := L) (N := N) i).E 0 = 0 := map_zero (reflT (L := L) (N := N) i)
      rw [e1, e0] at h3
      rw [h3, hperm i]
  refine ⟨C 0 0, C (dirVec (Sum.inl i₀)) 0 - C 0 0, fun x => ?_, fun x e => ?_, fun x e => ?_⟩
  · have := hCs (AffAut.transl x) (IsGen.transl x) 0 0
    simpa [AffAut.transl] using this
  · rw [key]; ring
  · rw [hCsym, key]; ring

/-! ### `Q` at the level of `j`-blocks -/

theorem bmap_fix {T : AffAut d L N} (hT : IsGen T) {j : ℕ} (hj : j ≤ N) (hP : PresBlocks j T)
    {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j)
    (himg : T.img (blockSet (L := L) (N := N) j b) = blockSet j b) : bmap j T b = b := by
  have e1 := img_blockSet_bmap hT hj hP hb
  rw [himg] at e1
  have e2 := congrArg (blocks j) e1
  rw [blocks_blockSet_eq hb, blocks_blockSet_eq (bmap_mem_blockIdx hT hj hP hb)] at e2
  exact (Finset.singleton_injective e2).symm

/-- `T Q(B) = Q(T B)` for lattice maps preserving `j`-blocks. -/
theorem AE_Q2_j {j : ℕ} {K : Act d L N} (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hjN : j + 1 < N)
    (hK : InK2 j K) (hKs : KSym j K) {T : AffAut d L N} (hT : IsGen T) (hP : PresBlocks j T)
    {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    AE T (Q2 j K b) = Q2 j K (bmap j T b) := by
  classical
  have hj : j ≤ N := by omega
  have hB := img_blockSet_bmap hT hj hP hb
  obtain ⟨T', hT', hP', e, e'⟩ := hP.exists_inv hT hj
  have hS : ((smallSets j).filter fun Y => blockSet j (bmap j T b) ⊆ Y) =
      ((smallSets j).filter fun Y => blockSet (L := L) (N := N) j b ⊆ Y).image T.img := by
    ext Y
    simp only [mem_filter, mem_image, mem_smallSets]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨T'.img Y, ⟨(hP'.isSmall_img hT' hj).2 h1, ?_⟩, e' Y⟩
      have := img_mono T' h2
      rwa [← hB, e] at this
    · rintro ⟨Y', ⟨h1, h2⟩, rfl⟩
      exact ⟨(hP.isSmall_img hT hj).2 h1, by rw [← hB]; exact img_mono T h2⟩
  rw [Q2, Q2, if_pos hjN, if_pos hjN, hS, sum_image fun Y _ Y' _ e => img_injective T e, map_sum]
  refine sum_congr rfl fun X hX => ?_
  have hs := mem_smallSets.1 (mem_filter.1 hX).1
  refine Subtype.ext ?_
  rw [coe_AE, coe_Loc2E, coe_Loc2E, ← hB, Loc2sXY_aut hT (region_small hd hL hjN hs) hs.2.1.1 _
    (hK.loc X ⟨hs.1, hs.2.1⟩), ← coe_AE, hKs T hT hP X]

/-- `Q(B)` is uniform on `B`. -/
theorem Q2_unif {j : ℕ} (K : Act d L N) (hjN : j + 1 < N) (b : Fin d → ℕ) :
    ∃ (κ : ℂ) (c : Mono d → ℂ) (e : Fin d → Fin d → ℂ),
      (Q2 j K b : Alg d L N) = unif κ c e (blockSet (L := L) (N := N) j b) := by
  classical
  rw [Q2, if_pos hjN, AddSubmonoidClass.coe_finsetSum]
  simp only [coe_Loc2E, Loc2sXY_eq_unif]
  exact ⟨_, _, _, unif_finset_sum _ _ _ _ _⟩

/-! ### The hypotheses -/

/-- The hypotheses of Proposition `prop:C2`(ii). -/
structure CoupHyp (j : ℕ) (ℓ : ℝ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V W : Fam d L N)
    (K : Act d L N) (κ : Coup) (c₀ δ : ℂ) : Prop where
  hd : 1 ≤ d
  hL8 : 2 ^ (d + 3) + 8 * d < L
  hj2 : j + 2 < N
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
  ⟨H.hd, H.hL, H.hj2, H.hC, H.hCs, H.hV, H.hW, H.hV0, H.hK, H.hVs, H.hWs, H.hKs, hT, hP1⟩

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
  have hR0 := region_small H.hd H.hL (by have := H.hj2; omega : (j + 1) + 1 < N) hsm0
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

end

end Step2
