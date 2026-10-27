import Flow.ConsistTransl

/-!
# Proposition `prop:consistency`: independence of the torus

For `N ≤ M` the torus `Λ_N` is identified near the origin with `Λ_M` by `emb x = rep(x) mod L^M`
(`rep` is the centred representative in `ℤ^d`).  Activities `K` on `Λ_N` and `K'` on `Λ_M` are
*compatible up to diameter `D`* (`Compat`) if `K'(emb X) = emb K(X)` for all connected polymers
`X ⊆ Λ_N` of diameter `≤ D` in the central region `|x|_∞ ≤ L^N/4`.  For compatible activities in
`𝒦_j` and the covariances of `sec:frd` (which agree near the origin, `Cfrd_emb`):

* the coupling constants agree: `uVnext_consist`;
* the next activities are compatible (up to a smaller diameter): `Knext_consist`.

This is the second part of Proposition `prop:consistency`; it is used to define the infinite
volume flow as a compatible family of torus flows.

The definitions (`emb`, `embA`, `embE`, `diam`, `Compat`) are in `Flow.Embed`.  The proof:

* `Flow.Embed`, `Flow.EmbGeom`: near the origin `emb` preserves differences, distances, blocks,
  polymers, touching, connectedness, small sets, components, closures and neighbourhoods;
* `Flow.EmbAlg`, `Flow.EmbLoc`: `embA` commutes with `θ`, `ζ ↦ 0`, `V(X)`, `Loc` (for supports
  near the origin) and `𝔼_C` (for covariances agreeing on the support);
* `Flow.ConsistStep`: the ingredients of `K_{j+1}(U)` and the index sets `𝒢(U)`, `𝒢(emb U)`
  correspond, so `emb K_{j+1}(U) = K'_{j+1}(emb U)` (`E_Knext`);
* `Flow.ConsistTransl`: compatibility extends from the central region to polymers near `U` by
  translation invariance (`compat_ext`).
-/

namespace Flow

noncomputable section

open Finset Grassmann Loc FRD Step

variable {d L : ℕ} [NeZero L]

/-- The covariances of the finite range decomposition agree near the origin. -/
theorem Cfrd_emb {N M : ℕ} (hNM : N ≤ M) {j : ℕ} (hj : j + 1 < N) {msq : ℝ} (hmsq : 0 ≤ msq)
    (hd : 1 ≤ d) (x y : Lam d L N) (hx : 4 * supNorm x < L ^ N) (hy : 4 * supNorm y < L ^ N) :
    Cfrd d L M msq j (emb N M x) (emb N M y) = Cfrd d L N msq j x y := by
  refine Cfrd_emb_of hNM hj hmsq hd ?_
  have := supNorm_add_le x (-y)
  rw [← sub_eq_add_neg, supNorm_neg] at this
  omega

/-! ### Auxiliary facts -/

theorem blk_zero (j N : ℕ) : blk j (0 : Lam d L N) = 0 := by
  funext i
  show ((0 : Fin d → ZMod (L ^ N)) i).val / L ^ j = 0
  simp

theorem emb_zero (N M : ℕ) : emb N M (0 : Lam d L N) = 0 := by
  have h : rep (0 : Lam d L N) = 0 :=
    (eq_rep (Loc.prj_zero (d := d) (L := L) (N := N)) (by rw [supNormZ_zero, mul_zero]; exact Nat.pos_of_ne_zero (NeZero.ne _))).symm
  rw [emb, h, Loc.prj_zero]

theorem supNorm_lt_of_mem_blockSet_zero {j N : ℕ} {x : Lam d L N}
    (hx : x ∈ blockSet j (0 : Fin d → ℕ)) : supNorm x < L ^ j := by
  have := supNorm_lt_of_blk_eq ((Loc.mem_blockSet.1 hx).trans (blk_zero j N).symm)
  rwa [sub_zero] at this

theorem Compat.mono {N M j D D' : ℕ} {K : Act d L N} {K' : Act d L M} (h : Compat j D K K')
    (hD : D' ≤ D) : Compat j D' K K' := fun X h1 h2 h3 => h X h1 h2 (h3.trans hD)

theorem covInv_Cfrd (N : ℕ) (msq : ℝ) (j : ℕ) : CovInv (Cfrd d L N msq j) :=
  fun T hT x y => Cfrd_inv msq j T hT x y

theorem symm_Cfrd (N : ℕ) {msq : ℝ} (hmsq : 0 ≤ msq) (j : ℕ) (x y : Lam d L N) :
    Cfrd d L N msq j x y = Cfrd d L N msq j y x := by
  simpa using ((Cj_posSemidef stdPt hmsq (Nat.cast_nonneg L) (j + 1)
    (d := d) (n := L ^ N)).1.apply x y).symm

/-- **Proposition `prop:consistency`** (coupling constants): compatible activities give the same
`(u_{j+1}, V_{j+1})`. -/
theorem uVnext_consist (hd : 3 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {N M j : ℕ} (hNM : N ≤ M)
    (hj : j + 2 ≤ N) {msq : ℝ} (hmsq : 0 ≤ msq) (V : Vcoup) {K : Act d L N} {K' : Act d L M}
    (hK : InK j K) (hK' : InK j K') (hc : Compat j (2 ^ (d + 2) * L ^ j) K K') :
    uVnext j (Cfrd d L N msq j) V K = uVnext j (Cfrd d L M msq j) V K' := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨-, h2, h3, h16⟩ := num_facts hd1 hL hj
  have hjN : j + 1 < N := by omega
  have hjM : j + 1 < M := by omega
  have hP1 : 1 ≤ L ^ j := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j
  have h64 : 64 * (2 ^ d * L ^ j) ≤ L ^ N := by
    calc 64 * (2 ^ d * L ^ j) = 2 ^ (d + 6) * L ^ j := by ring
      _ ≤ L ^ N := h2
  have h4 : 2 ^ (d + 2) * L ^ j = 4 * (2 ^ d * L ^ j) := by ring
  have hdP : L ^ j ≤ 2 ^ d * L ^ j := Nat.le_mul_of_pos_left _ (by positivity)
  set B0 := blockSet (L := L) (N := N) j (0 : Fin d → ℕ) with hB0def
  have hU0 : ∀ x ∈ B0, supNorm x < L ^ j := fun x hx => supNorm_lt_of_mem_blockSet_zero hx
  have hUc : ∀ x ∈ B0, 4 * supNorm x ≤ L ^ N := fun x hx => by have := hU0 x hx; omega
  have hUd : ∀ x ∈ B0, ∀ y ∈ B0, 8 * supNorm (x - y) ≤ L ^ N := fun x hx y hy => by
    have := supNorm_lt_of_blk_eq ((Loc.mem_blockSet.1 hx).trans (Loc.mem_blockSet.1 hy).symm)
    omega
  have h0 : (0 : Lam d L N) ∈ B0 := Loc.mem_blockSet.2 (blk_zero j N)
  have hb0 : bemb L N M j (blk j (0 : Lam d L N)) = 0 := by
    rw [bemb_blk hNM (hPj hj) h3 (by rw [supNorm_zero]; positivity), emb_zero, blk_zero]
  have hB0 : blockSet (L := L) (N := M) j (0 : Fin d → ℕ) = B0.image (emb N M) := by
    have := blockSet_bemb' hNM hd1 hL hj hUc hUd (M := M) h0
    rwa [hb0, blk_zero] at this
  have hBt : ∀ y ∈ B0, 2 * supNorm y + 2 < L ^ N := by
    have := block_two hNM hd1 hL hj hUc hUd (M := M) h0
    rwa [blk_zero] at this
  -- compatibility for the small sets containing `B_0`
  have hKK : ∀ X : Finset (Lam d L N), IsConn j X → (∀ x ∈ X, InB B0 (2 ^ d * L ^ j) x) →
      embE N M (K X) = K' (X.image (emb N M)) := by
    intro X hX hXU
    refine hc X hX (fun x hx => ?_) (diam_le fun x hx y hy => ?_)
    · obtain ⟨u, hu, h⟩ := hXU x hx
      have := hU0 u hu
      have := supNorm_add_le (x - u) u
      rw [sub_add_cancel] at this
      omega
    · obtain ⟨u, hu, hxu⟩ := hXU x hx
      obtain ⟨v, hv, hyv⟩ := hXU y hy
      have huv := supNorm_lt_of_blk_eq ((Loc.mem_blockSet.1 hu).trans (Loc.mem_blockSet.1 hv).symm)
      have e : x - y = (x - u) + ((u - v) + (v - y)) := by abel
      have h6 := supNorm_add_le (x - u) ((u - v) + (v - y))
      have h7 := supNorm_add_le (u - v) (v - y)
      rw [supNorm_sub_comm v y] at h7
      rw [← e] at h6
      omega
  have hr : 0 + 2 ^ d * L ^ j ≤ 2 ^ (d + 2) * L ^ j := by omega
  have hCC : ∀ x ∈ (nbhd j B0 : Set (Lam d L N)), ∀ y ∈ (nbhd j B0 : Set (Lam d L N)),
      Cfrd d L M msq j (emb N M x) (emb N M y) = Cfrd d L N msq j x y := fun x hx y hy =>
    Cfrd_emb_of hNM hjN hmsq hd1 (inB_near hd1 hL hj hUc hUd hr
      (InB.nbhd (fun z hz => inB_of_mem hz 0) (mem_coe.1 hx))
      (InB.nbhd (fun z hz => inB_of_mem hz 0) (mem_coe.1 hy)))
  -- `emb Q(B_0) = Q'(B_0)`
  have hQ : embA N M (Qb j K 0 : Alg d L N) = (Qb j K' 0 : Alg d L M) := by
    rw [Qb_coe, Qb_coe, if_pos hjN, if_pos hjM, _root_.map_sum]
    have hS := smallSets_image hNM hd1 hL hj hUc hUd (M := M) h0
    rw [hb0, blk_zero] at hS
    rw [hS, sum_image fun Y _ Y' _ e => image_emb_injective hNM e]
    refine sum_congr rfl fun Y hY => ?_
    obtain ⟨hY1, hY2⟩ := mem_filter.1 hY
    have hYs := mem_smallSets.1 hY1
    have hYU : ∀ y ∈ Y, InB B0 (2 ^ d * L ^ j) y := fun y hy =>
      ⟨0, h0, supNorm_le_of_isSmall hYs hy (hY2 h0)⟩
    have := congrArg Subtype.val
      (E_LocE hNM hd1 hL hj hUc hUd hK hYs hYU (hKK Y ⟨hYs.1, hYs.2.1⟩ hYU) hBt)
    simp only [coe_embE, coe_LocE] at this
    rw [this, ← hB0]
  have hQmem : (Qb j K 0 : Alg d L N) ∈ NX (nbhd j B0 : Set (Lam d L N)) := by
    rw [Qb_coe, if_pos hjN]
    exact Subalgebra.sum_mem _ fun X _ => LocXY_mem hd1 (isPolymer_blockSet j 0) X _
  have hG : V.eval B0 - (Qb j K 0 : Alg d L N) ∈ NX (nbhd j B0 : Set (Lam d L N)) :=
    sub_mem (eval_mem_NX hd1 (isPolymer_blockSet j 0) V) hQmem
  have hkey : embA N M (EC (Cfrd d L N msq j) (theta (V.eval B0 - (Qb j K 0 : Alg d L N)))) =
      EC (Cfrd d L M msq j) (theta (V.eval (blockSet (L := L) (N := M) j (0 : Fin d → ℕ)) -
        (Qb j K' 0 : Alg d L M))) := by
    rw [← EC_emb hNM hCC (theta_mem_NX2 hG), ← theta_pushA (emb_injective' hNM), ← embA_eq,
      _root_.map_sub, embA_eval hNM V hBt, hQ, ← hB0]
  have sN := uVnext_spec hd1 hL (by omega : j < N) (covInv_Cfrd N msq j) (symm_Cfrd N hmsq j) V hK
    (zero_mem_blockIdx j)
  have sM := uVnext_spec hd1 hL (by omega : j < M) (covInv_Cfrd M msq j) (symm_Cfrd M hmsq j) V hK'
    (zero_mem_blockIdx j)
  have e1 : EC (Cfrd d L M msq j) (theta (V.eval (blockSet (L := L) (N := M) j (0 : Fin d → ℕ)) -
        (Qb j K' 0 : Alg d L M))) =
      ((uVnext j (Cfrd d L N msq j) V K).1 *
        (blockSet (L := L) (N := M) j (0 : Fin d → ℕ)).card) • (1 : Alg d L M) +
        (uVnext j (Cfrd d L N msq j) V K).2.eval (blockSet (L := L) (N := M) j (0 : Fin d → ℕ)) := by
    rw [← hkey, sN, _root_.map_add, _root_.map_smul, _root_.map_one, embA_eval hNM _ hBt, hB0,
      card_image_emb hNM]
  rw [sM] at e1
  have hLM : 3 ≤ L ^ M := by
    have := pow_le_pow_NM (L := L) hNM
    omega
  have hne : (blockSet (L := L) (N := M) j (0 : Fin d → ℕ)).Nonempty :=
    ⟨0, Loc.mem_blockSet.2 (blk_zero j M)⟩
  have hpatch : Patch (blockSet (L := L) (N := M) j (0 : Fin d → ℕ)) := by
    have := patch_small hd1 hL hjM (isSmall_blockSet j (0 : Lam d L M))
    rwa [blk_zero] at this
  obtain ⟨u1, u2⟩ := coup_injective hd1 hLM hne hpatch e1
  exact Prod.ext u1.symm u2.symm

/-- **Proposition `prop:consistency`** (activities): activities compatible up to diameter `D`
give next activities compatible up to diameter `D - 2^{d+3} L^{j+1}` (the loss comes from the
neighbourhoods `X^□` of the polymers contributing to `K_{j+1}(U)`). -/
theorem Knext_consist (hd : 3 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {N M j : ℕ} (hNM : N ≤ M)
    (hj : j + 2 ≤ N) {msq : ℝ} (hmsq : 0 ≤ msq) (V : Vcoup) {K : Act d L N} {K' : Act d L M}
    (hK : InK j K) (hK' : InK j K') {D : ℕ} (hD : 8 * D ≤ L ^ N)
    (hD' : 2 ^ (d + 3) * L ^ (j + 1) ≤ D) (hc : Compat j D K K') :
    Compat (j + 1) (D - 2 ^ (d + 3) * L ^ (j + 1))
      (Knext j (Cfrd d L N msq j) V K) (Knext j (Cfrd d L M msq j) V K') := by
  have hd1 : 1 ≤ d := by omega
  have hjN : j + 1 < N := by omega
  have hLj : L ^ j ≤ L ^ (j + 1) :=
    Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (by omega)
  have h2d : 2 ^ (d + 2) ≤ 2 ^ (d + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hA : 2 ^ (d + 2) * L ^ j ≤ 2 ^ (d + 3) * L ^ (j + 1) := Nat.mul_le_mul h2d hLj
  have h4 : 2 ^ (d + 2) * L ^ j = 4 * (2 ^ d * L ^ j) := by ring
  have huV := (uVnext_consist hd hL hNM hj hmsq V hK hK' (hc.mono (hA.trans hD'))).symm
  intro U hU hUc hUdiam
  have hUd : ∀ x ∈ U, ∀ y ∈ U, 8 * supNorm (x - y) ≤ L ^ N := fun x hx y hy => by
    have := le_diam hx hy
    omega
  have hr : 0 + 2 ^ d * L ^ j ≤ 2 ^ (d + 2) * L ^ j := by omega
  have hr' : 2 ^ d * L ^ j ≤ 2 ^ (d + 2) * L ^ j := by omega
  have hKK : ∀ X : Finset (Lam d L N), IsConn j X → (∀ x ∈ X, InB U (2 ^ d * L ^ j) x) →
      embE N M (K X) = K' (X.image (emb N M)) := by
    intro X hX hXU
    refine compat_ext hNM hd1 hL hj hK hK' hD hc hX
      (fun x hx => inB_pt hd1 hL hj hUc hUd hr' (hXU x hx)) (diam_le fun x hx y hy => ?_)
    obtain ⟨u, hu, hxu⟩ := hXU x hx
    obtain ⟨v, hv, hyv⟩ := hXU y hy
    have huv := le_diam hu hv
    have e : x - y = (x - u) + ((u - v) + (v - y)) := by abel
    have h6 := supNorm_add_le (x - u) ((u - v) + (v - y))
    have h7 := supNorm_add_le (u - v) (v - y)
    rw [supNorm_sub_comm v y] at h7
    rw [← e] at h6
    omega
  have hCC : ∀ x ∈ (nbhd j U : Set (Lam d L N)), ∀ y ∈ (nbhd j U : Set (Lam d L N)),
      Cfrd d L M msq j (emb N M x) (emb N M y) = Cfrd d L N msq j x y := fun x hx y hy =>
    Cfrd_emb_of hNM hjN hmsq hd1 (inB_near hd1 hL hj hUc hUd hr
      (InB.nbhd (fun z hz => inB_of_mem hz 0) (mem_coe.1 hx))
      (InB.nbhd (fun z hz => inB_of_mem hz 0) (mem_coe.1 hy)))
  exact E_Knext hNM hd1 hL hj hUc hUd huV hK hKK hCC hU.1

end

end Flow
