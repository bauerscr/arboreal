import Step2.Flow.FlowRG

/-!
# The step at `j = N - 2`: geometry (`h02uv-outline.tex`, Section `sec:corr`, the last scales)

At `j + 2 = N` the outputs of the step live at scale `N - 1`, where the `(N-1)`-blocks are only
`L` per direction. The Step2 covariance lemmas (`LS_transl`, `Wnext2_cov`, …) assume `j + 2 < N`
only to apply `Step.region_small` at scale `j + 1`, whose crude bound `L^{k+2} ≤ L^N` fails at
`k = N - 1`. The sharp bound only needs `k < N` and `L > 2^{d+4} + 4`
(`region_small_L`): the small set neighbourhood of a small `k`-set has diameter
`≤ 2^{d+2} L^k`, which is `< L^N / 4` as soon as `L > 2^{d+4} + 4`.

This file proves the translation covariance of the outputs at scale `j + 1` for all `j + 1 < N`
under `L > 2^{d+4} + 4` (namespace `Step2.Last`, same names as the `j + 2 < N` versions).
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Matrix

variable {d L N : ℕ} [NeZero L]

/-- **Small sets at every scale `k < N` are regions**, for `L > 2^{d+4} + 4`. (The old
`region_small` needs `k + 1 < N`.) -/
theorem region_small_L (hd : 1 ≤ d) (hLg : 2 ^ (d + 4) + 4 < L) {k : ℕ} (hk : k < N)
    {X : Finset (Lam d L N)} (hX : IsSmall k X) :
    Region X (nbhd k X : Set (Lam d L N)) := by
  refine ⟨fun x hx a ha => ?_, fun x hx y hy => ?_⟩
  · refine Finset.mem_coe.2 (mem_nbhd_of_near hd hX.1 hx ?_)
    rw [add_sub_cancel_left]
    exact (supNorm_prj_le a).trans ha
  · obtain ⟨x0, hx0⟩ := hX.2.1.1
    have h1 := supNorm_le_of_mem_nbhd hX hx0 (Finset.mem_coe.1 hx)
    have h2 := supNorm_le_of_mem_nbhd hX hx0 (Finset.mem_coe.1 hy)
    have h3 : supNorm (x - y) ≤ supNorm (x - x0) + supNorm (y - x0) := by
      have := supNorm_add_le (x - x0) (x0 - y)
      rw [sub_add_sub_cancel, supNorm_sub_comm x0 y] at this
      exact this
    have hQ : 1 ≤ L ^ k := Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ (NeZero.ne L))
    have hLN : L ^ k * L ≤ L ^ N := by
      rw [← pow_succ]
      exact Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) hk
    have e : 2 ^ (d + 4) = 2 ^ (d + 1) * 8 := by ring
    have h4 : L ^ k * (2 ^ (d + 4) + 5) ≤ L ^ k * L := Nat.mul_le_mul_left _ hLg
    rw [e] at h4
    nlinarith

namespace Last

variable {t : Lam d L N} {ℓ : ℝ}
variable {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℂ} {V W : Fam d L N} {K : Act d L N}

theorem LS_transl (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hj2 : j + 1 < N) (hLg : 2 ^ (d + 4) + 4 < L) (hC : GoodCov2 j ℓ C)
    (hCt : TInv C) (hV : InF j V) (hW : InF j W) (hVc : FamCovG j V) (hWc : FamCovG j W)
    (ht : ∀ i, L ^ (j + 1) ∣ (co t i).val) {b : Fin d → ℕ}
    (hb : b ∈ blockIdx (L := L) (N := N) j) :
    (LS j C V W (bmap j (AffAut.transl t) b) : Alg d L N) =
      autAlg (Equiv.addRight t) (LS j C V W b) := by
  have ht' : ∀ i, L ^ j ∣ (co t i).val := fun i => (pow_dvd_pow L (Nat.le_succ j)).trans (ht i)
  have hP := Flow.presBlocks_transl' (by omega) t ht'
  have hsm : IsSmall (j + 1) (Bp (L := L) (N := N) j b) :=
    isSmall_clo (isSmall_blockSet_of_mem hb)
  have hR := region_small_L hd hLg hj2 hsm
  have hF := SX_mem' hd hL (by omega) hC hV hW b
  rw [LS, LS, coe_Loc2E, coe_Loc2E, Loc2XY_transl hR hsm.2.1.1 t _ hF,
    Bp_transl (by omega) ht hb, img_blockSet_bmap (IsGen.transl t) (by omega) hP hb,
    ← SX_transl (by omega) hCt hVc hWc ht', Bp_transl (by omega) ht hb]

theorem Wp_transl (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hj2 : j + 1 < N) (hLg : 2 ^ (d + 4) + 4 < L) (hC : GoodCov2 j ℓ C)
    (hCt : TInv C) (hV : InF j V) (hW : InF j W) (hVc : FamCovG j V) (hWc : FamCovG j W)
    (ht : ∀ i, L ^ (j + 1) ∣ (co t i).val) {b : Fin d → ℕ}
    (hb : b ∈ blockIdx (L := L) (N := N) j) :
    (Wp j C V W (bmap j (AffAut.transl t) b) : Alg d L N) =
      autAlg (Equiv.addRight t) (Wp j C V W b) := by
  have ht' : ∀ i, L ^ j ∣ (co t i).val := fun i => (pow_dvd_pow L (Nat.le_succ j)).trans (ht i)
  rw [Wp, Wp, AddSubgroupClass.coe_sub, AddSubgroupClass.coe_sub, map_sub,
    Sb_transl (by omega) hCt hVc hWc ht' hb, LS_transl hd hL hj2 hLg hC hCt hV hW hVc hWc ht hb]

/-- **Covariance of `𝒲_{j+1}`** at scale `j + 1`. -/
theorem Wnext2_cov (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hj2 : j + 1 < N) (hLg : 2 ^ (d + 4) + 4 < L)
    (hC : GoodCov2 j ℓ C) (hCt : TInv C) (hV : InF j V) (hW : InF j W) (hVc : FamCovG j V)
    (hWc : FamCovG j W) : FamCovG (j + 1) (Wnext2 j C V W) := by
  intro t ht c hc
  have ht' : ∀ i, L ^ j ∣ (co t i).val := fun i => (pow_dvd_pow L (Nat.le_succ j)).trans (ht i)
  have hP := Flow.presBlocks_transl' (by omega) t ht'
  have hP1 := Flow.presBlocks_transl' (by omega) t ht
  have hWp : ∀ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c),
      Wp j C V W (bmap j (AffAut.transl t) b) = AE (AffAut.transl t) (Wp j C V W b) :=
    fun b hb => Subtype.ext (by
      rw [coe_AE]; exact Wp_transl hd hL hj2 hLg hC hCt hV hW hVc hWc ht (mem_blockIdx_of_mem_blocks hb))
  have e : Wnext2 j C V W (bmap (j + 1) (AffAut.transl t) c) =
      AE (AffAut.transl t) (Wnext2 j C V W c) := by
    rw [Wnext2, Wnext2, ← img_blockSet_bmap (IsGen.transl t) (by omega) hP1 hc,
      blocks_img_bmap hP, map_sub, map_prod, map_one,
      prod_image fun b hb b' hb' e => bmap_injOn (IsGen.transl t) (by omega) hP
        (mem_blockIdx_of_mem_blocks hb) (mem_blockIdx_of_mem_blocks hb') e]
    congr 1
    refine prod_congr rfl fun b hb => ?_
    rw [map_add, map_one, hWp b hb]
  rw [e, coe_AE]; rfl

theorem uVp_transl (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hj2 : j + 1 < N) (hLg : 2 ^ (d + 4) + 4 < L) (hC : GoodCov2 j ℓ C)
    (hCt : TInv C) (hV : InF j V) (hW : InF j W) (hK : InK2 j K) (hVc : FamCovG j V)
    (hWc : FamCovG j W) (hKc : KCov j K) (ht : ∀ i, L ^ (j + 1) ∣ (co t i).val)
    {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    (uVp j C V W K (bmap j (AffAut.transl t) b) : Alg d L N) =
      autAlg (Equiv.addRight t) (uVp j C V W K b) := by
  have ht' : ∀ i, L ^ j ∣ (co t i).val := fun i => (pow_dvd_pow L (Nat.le_succ j)).trans (ht i)
  have h1 : ∀ x y, C ((Equiv.addRight t) x) ((Equiv.addRight t) y) = C x y :=
    fun x y => hCt t x y
  rw [uVp, uVp, AddSubgroupClass.coe_sub, AddSubgroupClass.coe_sub, AddSubgroupClass.coe_sub,
    AddSubgroupClass.coe_sub, map_sub, map_sub, Vpr_transl hCt hVc ht' hb, coe_EthE, coe_EthE,
    Q2_transl hd hL (by omega) hK hKc ht' hb, expLC_autAlg _ h1,
    LS_transl hd hL hj2 hLg hC hCt hV hW hVc hWc ht hb]

theorem Vp_transl (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hj2 : j + 1 < N) (hLg : 2 ^ (d + 4) + 4 < L) (hC : GoodCov2 j ℓ C)
    (hCt : TInv C) (hV : InF j V) (hW : InF j W) (hK : InK2 j K) (hVc : FamCovG j V)
    (hWc : FamCovG j W) (hKc : KCov j K) (ht : ∀ i, L ^ (j + 1) ∣ (co t i).val)
    {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    (Vp j C V W K (bmap j (AffAut.transl t) b) : Alg d L N) =
      autAlg (Equiv.addRight t) (Vp j C V W K b) := by
  have e := uVp_transl hd hL hj2 hLg hC hCt hV hW hK hVc hWc hKc ht hb
  have hu : up j C V W K (bmap j (AffAut.transl t) b) = up j C V W K b := by
    rw [up, up, e, ε_autAlg]
  rw [Vp, Vp, AddSubgroupClass.coe_sub, AddSubgroupClass.coe_sub, e, hu, map_sub,
    Subalgebra.coe_algebraMap, AlgHom.commutes]

/-- **Covariance of `V_{j+1}`** at scale `j + 1`. -/
theorem Vnext2_cov (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hj2 : j + 1 < N) (hLg : 2 ^ (d + 4) + 4 < L)
    (hC : GoodCov2 j ℓ C) (hCt : TInv C) (hV : InF j V) (hW : InF j W) (hK : InK2 j K)
    (hVc : FamCovG j V) (hWc : FamCovG j W) (hKc : KCov j K) :
    FamCovG (j + 1) (Vnext2 j C V W K) := by
  intro t ht c hc
  have ht' : ∀ i, L ^ j ∣ (co t i).val := fun i => (pow_dvd_pow L (Nat.le_succ j)).trans (ht i)
  have hP := Flow.presBlocks_transl' (by omega) t ht'
  have hP1 := Flow.presBlocks_transl' (by omega) t ht
  rw [Vnext2, Vnext2, ← img_blockSet_bmap (IsGen.transl t) (by omega) hP1 hc, blocks_img_bmap hP,
    sum_image fun b hb b' hb' e => bmap_injOn (IsGen.transl t) (by omega) hP
      (mem_blockIdx_of_mem_blocks hb) (mem_blockIdx_of_mem_blocks hb') e,
    AddSubmonoidClass.coe_finsetSum, AddSubmonoidClass.coe_finsetSum, map_sum]
  exact sum_congr rfl fun b hb =>
    Vp_transl hd hL hj2 hLg hC hCt hV hW hK hVc hWc hKc ht (mem_blockIdx_of_mem_blocks hb)

theorem sumWp_cov
    (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hj2 : j + 1 < N) (hLg : 2 ^ (d + 4) + 4 < L)
    (hC : GoodCov2 j ℓ C) (hCt : TInv C) (hV : InF j V) (hW : InF j W) (hVc : FamCovG j V)
    (hWc : FamCovG j W) :
    FamCovG (j + 1) (fun c => ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c),
      Wp j C V W b) := by
  intro t ht c hc
  have ht' : ∀ i, L ^ j ∣ (co t i).val := fun i => (pow_dvd_pow L (Nat.le_succ j)).trans (ht i)
  have hP := Flow.presBlocks_transl' (by omega) t ht'
  have hP1 := Flow.presBlocks_transl' (by omega) t ht
  have hWp : ∀ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c),
      Wp j C V W (bmap j (AffAut.transl t) b) = AE (AffAut.transl t) (Wp j C V W b) :=
    fun b hb => Subtype.ext (by
      rw [coe_AE]; exact Wp_transl hd hL hj2 hLg hC hCt hV hW hVc hWc ht (mem_blockIdx_of_mem_blocks hb))
  have e : (∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) (bmap (j + 1) (AffAut.transl t) c)),
      Wp j C V W b) = AE (AffAut.transl t) (∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c),
        Wp j C V W b) := by
    rw [← img_blockSet_bmap (IsGen.transl t) (by omega) hP1 hc, blocks_img_bmap hP, map_sum,
      sum_image fun b hb b' hb' e => bmap_injOn (IsGen.transl t) (by omega) hP
        (mem_blockIdx_of_mem_blocks hb) (mem_blockIdx_of_mem_blocks hb') e]
    exact sum_congr rfl fun b hb => hWp b hb
  show ((∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) (bmap (j + 1) (AffAut.transl t) c)),
      Wp j C V W b : EvR (Lam d L N)) : Alg d L N) = _
  rw [e, coe_AE]
  rfl


end Last

end

end Step2
