import Step2.Flow.FlowBounds

/-!
# Bounds on the coupling vector of `V_{j+1}` (`h02uv-outline.tex`, Section `sec:reduction`)

By `CoupHyp.Vp_coup_explicit`, `V_{j+1}(B) = V_{κp}(B)` with `κp = κ' - κ_Q' - κ_L`:
`κ'` is the first-order shift of the input couplings, `κ_Q` the coupling vector of `Q(B)`
(bounded by `‖K‖`, `BH.coupQ_le`) and `κ_L` that of `Loc S` on the `(j+1)`-block (bounded by
`v² + w`, `BH.coupL_le`).
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

theorem Bp_zero (j : ℕ) :
    Bp (L := L) (N := N) j (0 : Fin d → ℕ) = blockSet (j + 1) (0 : Fin d → ℕ) := by
  rw [Bp, clo_blockSet (zero_mem_blockIdx j)]
  congr 1; funext i; simp [PolyAux.par]

/-! ### Covariance entries from the Gram bound -/

section CovEntries

variable {n : ℕ} [NeZero n] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem gvec_single (Fv : Torus d n → H) (x : Torus d n) : gvec Fv (Pi.single x 1) = Fv x := by
  unfold gvec
  rw [sum_eq_single x (fun y _ hy => by simp [Pi.single_apply, hy]) (by simp)]
  simp

theorem Iic_zero_dir : Finset.Iic (0 : Dir d → ℕ) = {0} := by
  ext b; simp only [Finset.mem_Iic, Finset.mem_singleton]
  constructor
  · intro h; funext e; exact Nat.le_zero.1 (h e)
  · rintro rfl; exact le_rfl

theorem dprof_zero (x : Torus d n) : dprof (0 : Dir d → ℕ) x = Pi.single x 1 := by
  unfold dprof
  rw [Iic_zero_dir, sum_singleton]
  simp [cf, zero_vadd]

theorem Iic_single_dir (e : Dir d) :
    Finset.Iic (Pi.single e 1 : Dir d → ℕ) = {0, Pi.single e 1} := by
  ext b; simp only [Finset.mem_Iic, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    by_cases hb : b e = 0
    · left; funext e'
      by_cases he : e' = e
      · subst he; exact hb
      · have := h e'; simp [Pi.single_apply, he] at this; simp [this]
    · right; funext e'
      by_cases he : e' = e
      · subst he; have := h e'; simp at this; simp; omega
      · have := h e'; simp [Pi.single_apply, he] at this; simp [Pi.single_apply, he, this]
  · rintro (rfl | rfl)
    · exact fun _ => Nat.zero_le _
    · exact le_rfl

theorem dprof_single (e : Dir d) (x : Torus d n) :
    dprof (Pi.single e 1 : Dir d → ℕ) x = Pi.single (dirVec e + x) 1 - Pi.single x 1 := by
  unfold dprof
  have hne : (0 : Dir d → ℕ) ≠ Pi.single e 1 := by
    intro h; have := congrFun h e; simp at this
  rw [Iic_single_dir, sum_insert (by simpa using hne), sum_singleton]
  have h1 : cf (Pi.single e 1 : Dir d → ℕ) 0 = -1 := by
    unfold cf
    rw [Finset.prod_eq_single e (fun e' _ he' => by simp [Pi.single_apply, he'])
      (by simp)]
    simp
  have h2 : cf (Pi.single e 1 : Dir d → ℕ) (Pi.single e 1) = 1 := by
    unfold cf; simp
  have h3 : (Pi.single e 1 : Dir d → ℕ) +ᵥ x = dirVec e + x := by
    rw [vadd_def]
    congr 1
    rw [sum_eq_single e (fun e' _ he' => by simp [Pi.single_apply, he']) (by simp)]
    simp
  rw [h1, h2, h3, zero_vadd]
  simp only [neg_smul, one_smul]
  abel

theorem bil_sub_sub (C : Matrix (Torus d n) (Torus d n) ℂ) (a b : Torus d n) :
    bil C (Pi.single a 1 - Pi.single b 1) (Pi.single a 1 - Pi.single b 1) =
      C a a - C a b - C b a + C b b := by
  simp only [bil, Pi.sub_apply, Pi.single_apply]
  have key : ∀ u v : Torus d n, ∑ x, ∑ y, (((if x = u then (1 : ℝ) else 0) : ℝ) : ℂ) * C x y *
      (((if y = v then (1 : ℝ) else 0) : ℝ) : ℂ) = C u v := by
    intro u v
    rw [Finset.sum_eq_single u (fun x _ hx => by
      refine Finset.sum_eq_zero fun y _ => ?_
      rw [if_neg hx]; push_cast; ring) (by simp)]
    rw [Finset.sum_eq_single v (fun y _ hy => by rw [if_neg hy]; push_cast; ring) (by simp)]
    simp
  have e : ∀ x y : Torus d n, ((((if x = a then (1 : ℝ) else 0) - if x = b then 1 else 0 : ℝ)) : ℂ) *
      C x y * ((((if y = a then (1 : ℝ) else 0) - if y = b then 1 else 0 : ℝ)) : ℂ) =
      (((if x = a then (1 : ℝ) else 0) : ℝ) : ℂ) * C x y * (((if y = a then (1 : ℝ) else 0) : ℝ) : ℂ)
      - (((if x = a then (1 : ℝ) else 0) : ℝ) : ℂ) * C x y * (((if y = b then (1 : ℝ) else 0) : ℝ) : ℂ)
      - (((if x = b then (1 : ℝ) else 0) : ℝ) : ℂ) * C x y * (((if y = a then (1 : ℝ) else 0) : ℝ) : ℂ)
      + (((if x = b then (1 : ℝ) else 0) : ℝ) : ℂ) * C x y *
        (((if y = b then (1 : ℝ) else 0) : ℝ) : ℂ) := by
    intro x y; push_cast; ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, key]

theorem norm_cov_le {C : Matrix (Torus d n) (Torus d n) ℂ} {Fv Gv : Torus d n → H}
    (hC : IsGram C Fv Gv) {p : ℕ} {h ℓ : ℝ} (hB : GramBound (Dir d) p h ℓ Fv Gv)
    (x y : Torus d n) : ‖C x y‖ ≤ ℓ ^ 2 := by
  obtain ⟨h1, -⟩ := hB 0 (by simp [Grassmann.mabs]) x
  obtain ⟨-, h2⟩ := hB 0 (by simp [Grassmann.mabs]) y
  rw [dprof_zero, gvec_single] at h1 h2
  simp only [Grassmann.mabs, Pi.zero_apply, sum_const_zero, pow_zero, inv_one, mul_one] at h1 h2
  rw [hC x y]
  calc ‖inner ℂ (Fv x) (Gv y)‖ ≤ ‖Fv x‖ * ‖Gv y‖ := norm_inner_le_norm _ _
    _ ≤ ℓ * ℓ := mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
    _ = ℓ ^ 2 := by ring

/-- **The first difference**: `|C(x+e,x+e) - C(x+e,x) - C(x,x+e) + C(x,x)| ≤ ℓ²/h²`. -/
theorem norm_cov_diff_le {C : Matrix (Torus d n) (Torus d n) ℂ} {Fv Gv : Torus d n → H}
    (hC : IsGram C Fv Gv) {p : ℕ} (hp : 1 ≤ p) {h ℓ : ℝ} (hB : GramBound (Dir d) p h ℓ Fv Gv)
    (e : Dir d) (x : Torus d n) :
    ‖C (dirVec e + x) (dirVec e + x) - C (dirVec e + x) x - C x (dirVec e + x) + C x x‖ ≤
      ℓ ^ 2 * ((h ^ 2)⁻¹) := by
  have hm : Grassmann.mabs (Pi.single e 1 : Dir d → ℕ) = 1 := by
    unfold Grassmann.mabs; rw [sum_eq_single e (fun e' _ he' => by simp [Pi.single_apply, he']) (by simp)]
    simp
  obtain ⟨h1, h2⟩ := hB (Pi.single e 1) (by rw [hm]; exact hp) x
  rw [hm, pow_one] at h1 h2
  have hbil := bil_eq_inner hC (dprof (Pi.single e 1) x) (dprof (Pi.single e 1) x)
  have e1 : bil C (dprof (Pi.single e 1 : Dir d → ℕ) x) (dprof (Pi.single e 1) x) =
      C (dirVec e + x) (dirVec e + x) - C (dirVec e + x) x - C x (dirVec e + x) + C x x := by
    rw [dprof_single, bil_sub_sub]
  rw [← e1, hbil]
  calc ‖inner ℂ (gvec Fv (dprof (Pi.single e 1) x)) (gvec Gv (dprof (Pi.single e 1) x))‖
      ≤ ‖gvec Fv (dprof (Pi.single e 1) x)‖ * ‖gvec Gv (dprof (Pi.single e 1) x)‖ :=
        norm_inner_le_norm _ _
    _ ≤ (ℓ * h⁻¹) * (ℓ * h⁻¹) := mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
    _ = ℓ ^ 2 * ((h ^ 2)⁻¹) := by rw [sq h, mul_inv]; ring

end CovEntries

namespace BH

variable {j : ℕ} {ℓ ℓ' ℓC : ℝ} {C : Matrix (Lam d L N) (Lam d L N) ℂ} {V W : Fam d L N}
  {K : Act d L N} {A r Cl cS : ℝ} (H : BH j ℓ ℓ' ℓC C V W K A r Cl cS) {v w : ℝ}
  (hv0 : 0 ≤ v) (hw0 : 0 ≤ w) (hv1 : v ≤ 1)
  (hv : ∀ b ∈ blockIdx (L := L) (N := N) j, Tj d (L : ℝ) j ℓ (V b : Alg d L N) ≤ ENNReal.ofReal v)
  (hw : ∀ b ∈ blockIdx (L := L) (N := N) j, Tj d (L : ℝ) j ℓ (W b : Alg d L N) ≤ ENNReal.ofReal w)
include H

include hv hw hv0 hw0 hv1 in
/-- **The coupling vector of `Loc S` on the `(j+1)`-block is bounded by `v² + w`**. -/
theorem coupL_le {Cq : ℝ}
    (hCq : ∀ (L : ℕ) [NeZero L], 2 ^ (d + 3) + 8 * d < L → ∀ N j : ℕ, j < N →
      ∀ X : Finset (Lam d L N), IsSmall j X →
      ∀ (r : ℂ) (κ : Coup), unif r (coupC κ) (coupE κ) X ∈ NX (nbhd j X : Set (Lam d L N)) →
      ∀ ℓ R : ℝ, 0 < ℓ → 0 ≤ R →
        Tj d (L : ℝ) j ℓ (unif r (coupC κ) (coupE κ) X) ≤ ENNReal.ofReal R →
        ‖κ.z‖ ≤ Cq * (ℓ ^ 2)⁻¹ * ((L : ℝ) ^ j) ^ 2 * R / X.card ∧
        ‖κ.y‖ ≤ Cq * (ℓ ^ 2)⁻¹ * ((L : ℝ) ^ j) ^ 2 * R / X.card ∧
        ‖κ.nu‖ ≤ Cq * (ℓ ^ 2)⁻¹ * R / X.card ∧
        ‖κ.g‖ ≤ Cq * (ℓ ^ 4)⁻¹ * ((L : ℝ) ^ j) ^ 2 * R / X.card)
    {κL : Coup}
    (hLS : locCoef (blockSet (j + 1) 0)
        (SX j C V W (blockSet (L := L) (N := N) (j + 1) (0 : Fin d → ℕ)) : Alg d L N) =
          coupC κL ∧
      (fun i k => mu4 (base (blockSet (L := L) (N := N) (j + 1) (0 : Fin d → ℕ))) i k
        (SX j C V W (blockSet (j + 1) 0) : Alg d L N) /
          (blockSet (L := L) (N := N) (j + 1) (0 : Fin d → ℕ)).card) = coupE κL) :
    let X := blockSet (L := L) (N := N) (j + 1) (0 : Fin d → ℕ)
    let R := Cl * ((L : ℝ) ^ d * sig d L v w)
    ‖κL.z‖ ≤ Cq * (ℓ' ^ 2)⁻¹ * ((L : ℝ) ^ (j + 1)) ^ 2 * R / X.card ∧
      ‖κL.y‖ ≤ Cq * (ℓ' ^ 2)⁻¹ * ((L : ℝ) ^ (j + 1)) ^ 2 * R / X.card ∧
      ‖κL.nu‖ ≤ Cq * (ℓ' ^ 2)⁻¹ * R / X.card ∧
      ‖κL.g‖ ≤ Cq * (ℓ' ^ 4)⁻¹ * ((L : ℝ) ^ (j + 1)) ^ 2 * R / X.card := by
  intro X R
  have h0 := zero_mem_blockIdx (d := d) (L := L) (N := N) (j + 1)
  have hX := isSmall_blockSet_of_mem h0
  have hne : X.Nonempty := hX.2.1.1
  set F := (SX j C V W X : Alg d L N)
  have hF : F ∈ NX (nbhd (j + 1) X : Set (Lam d L N)) := by
    have := SX_mem' H.hd H.hL8' H.hjN H.hC H.hV H.hW (0 : Fin d → ℕ)
    simp only [NBp, Bp_zero] at this
    exact this
  have hu : Loc2sX X F = unif (ε F) (coupC κL) (coupE κL) X := by
    rw [Loc2X_eq_unif hne, hLS.1, hLS.2]
  have hT : Tj d (L : ℝ) (j + 1) ℓ' (Loc2sX X F) ≤ ENNReal.ofReal R := by
    have hs0 : 0 ≤ sig d L v w := sig_nonneg H.hd v w hw0
    refine (H.hloc (j + 1) H.hjN ℓ' H.hℓ' X X hX subset_rfl F hF).trans ?_
    have hSX := H.SX_le' hv0 hw0 hv1 hv hw (0 : Fin d → ℕ)
    rw [Bp_zero] at hSX
    rw [ENNReal.ofReal_mul H.hCl]
    exact mul_le_mul_left' hSX _
  have hmem : unif (ε F) (coupC κL) (coupE κL) X ∈ NX (nbhd (j + 1) X : Set (Lam d L N)) := by
    rw [← hu]; exact Loc2XY_mem' H.hd hX.1 X F
  rw [hu] at hT
  have hs0 : 0 ≤ sig d L v w := sig_nonneg H.hd v w hw0
  exact hCq L H.hL8 N (j + 1) H.hjN X hX (ε F) κL hmem ℓ' R H.hℓ' (by have := H.hCl; positivity) hT

end BH

/-! ### The coupling vector of `V_{j+1}` in `d = 2` -/

/-- **`V_{j+1} = V_{κp}` with `κp = κ' - κ_Q' - κ_L` and bounds on `κ_Q`, `κ_L`** (`d = 2`). The
input `V` is the coupling polynomial of `κ`; `κ_Q` is bounded by `‖K‖_j ≤ k`, `κ_L` by
`v² + w` with `‖V‖_j ≤ v`, `‖W‖_j ≤ w`. -/
theorem coupP_bound : ∃ Cq : ℝ, 0 ≤ Cq ∧ ∃ Cl : ℝ, 0 ≤ Cl ∧ ∃ cS : ℝ, 1 ≤ cS ∧
    ∀ (L : ℕ) [NeZero L], 2 ^ (2 + 3) + 8 * 2 < L → pauliL0 2 ≤ L →
    ∀ (N j : ℕ), j + 2 < N → ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ →
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
  intro L _ hL8 hLp N j hj2 ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC hCs hCsym κ W K hW hK A hA v w k hv0 hw0
    hk0 hv1 hw1 hk1 hVv hWw hKk
  have hjN : j + 1 < N := by omega
  have hj : j < N := by omega
  set V : Fam 2 L N := VfamL (d := 2) (L := L) (N := N) j κ.toVec
  have hVmem : V ∈ BSub (L := L) (N := N) j := VfamL_mem (by norm_num) hL8 hj _
  obtain ⟨c₀, δ, hc₀, hδ, hδ'⟩ := covProps (by norm_num) hCs hCsym
  have H' : CoupHyp j ℓC C V W K κ c₀ δ :=
    ⟨by norm_num, hL8, hj2, hC, hCs, hCsym, hc₀, hδ, hδ', hVmem.1, hW.1, hK.1, hVmem.2.2.1,
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

end

end Step2
