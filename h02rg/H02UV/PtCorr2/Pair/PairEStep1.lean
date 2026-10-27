import PtCorr2.Pair.MemAB2
import PtCorr2.Pair.PairSizesAB
import PtCorr2.Pair.VObsStepAB1
import PtCorr2.Pair.KObsHistAB
import Obs2.Est.ErrABX
import Obs2.Flow.VObsAB2
import Obs2.Flow.VObsAB4X

/-!
# The `E`-step of the joint induction: trajectory-level pieces

* **The `Q'` item with the pair locality.** `PairErrItemsX` asks for
  `Q'_k(B)_{ab} ∈ 𝒩(B^□)`. This holds above coalescence, but at `k = j_x` the point `b` may lie
  outside `B_a^□` (the natural locality of `Q'_k(B)` from `OLocS` is `B^{□□}`, `Obs2.Q2O_mem`).
  The only use of that locality is the expectation bound `|m₂(e^{ℒ_C}F)| ≤ Q₁ℓ^{-2}‖F‖`; it holds
  as well for `F ∈ 𝒩({a,b})` (**`norm_mass2_expLC_le_pair`**: `|𝓑({a,b})| ≤ 2`), and
  `Q'_k(B)_{ab} ∈ 𝒩({a,b})` always (`Obs2.Q2O_ab_mem_pair`). So **`norm_qABX_leP`** is
  `Obs2.norm_qABX_le` without the locality hypothesis.
* **`Tj_Q2O_ab_le`**: `‖Q'_k(B)_{ab}‖_{T_k(ℓ)} ≤ C_Q κ` from `‖K_k(X)_{ab}‖_{T_k(ℓ)} ≤ κ` on small
  sets (`K(X)_{ab} ∈ 𝒩(X^□)`, anchored `K`): the `T`-norm copy of `exists_Q2O_ab_bound`.
* **`olocS_hR`**: the inputs of every step of the reduced history are local (`OLocS`).
* **`pdefM2X_eq_m4X`**, **`pdefM2X_hVR_le`**: region copy of `pdefM2_hist_le`:
  `|𝔡₂_k(X)| ≤ |M₄_k(X)|(nℓ_k/L^{k+1})²`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

section Pure

variable {d L N : ℕ} [NeZero L]

/-- `|m₂(e^{ℒ_C}F)| ≤ Q₁ℓ^{-2}‖F‖_{T_j(ℓ)}` for `F ∈ 𝒩({a,b})`. -/
theorem norm_mass2_expLC_le_pair (hd : 1 ≤ d) (hL : pauliL0 d ≤ L) {j : ℕ} (hj : j < N)
    {ℓ : ℝ} (hℓ : 0 < ℓ) {C : Matrix (Lam d L N) (Lam d L N) ℂ} (hC : GoodCov2 j ℓ C)
    (a b : Lam d L N) {F : Alg d L N} (hF : F ∈ NX ({a, b} : Set (Lam d L N))) :
    ‖mass2 (expLC C F)‖ ≤ Q1 d * (Tj d (L : ℝ) j ℓ F).toReal * ℓ⁻¹ ^ 2 := by
  have hF' : F ∈ NX (↑({a, b} : Finset (Lam d L N)) : Set (Lam d L N)) := by
    rw [Finset.coe_pair]; exact hF
  have h1 := norm_mass2_le hℓ (j + 1) (expLC C F)
  have h2 := EthE_succ_le hd hL hj hℓ hC hF'
  rw [ECC_theta] at h2
  have hnb : nb j ({a, b} : Finset (Lam d L N)) ≤ (2 ^ (d + 1) + 3) ^ d := by
    unfold nb blocks
    refine (card_image_le).trans ((card_le_two).trans ?_)
    calc 2 ≤ 2 ^ (d + 1) + 3 := by have := Nat.one_le_two_pow (n := d + 1); omega
      _ ≤ (2 ^ (d + 1) + 3) ^ d := Nat.le_self_pow (by omega) _
  have h3 : ENNReal.ofReal (pq d ^ nb j ({a, b} : Finset (Lam d L N))) *
      Tj d (L : ℝ) j ℓ F ≤ ENNReal.ofReal (Q1 d) * Tj d (L : ℝ) j ℓ F :=
    mul_le_mul_left (ENNReal.ofReal_le_ofReal (pow_le_pow_right₀ (one_le_pq hd) hnb)) _
  have h4 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (tNorm_ne_top (pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) j) hℓ F))
    (h2.trans h3)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by have := one_le_Q1 hd; linarith)] at h4
  exact h1.trans (mul_le_mul_of_nonneg_right h4 (by positivity))

/-- **`|qABX| ≤ 2Q₁ℓ^{-2}q̄`** on anchored `K` (no locality hypothesis: `Q'(B)_{ab} ∈ 𝒩({a,b})`). -/
theorem norm_qABX_leP (hd : 1 ≤ d) (hL : pauliL0 d ≤ L) (P : ObsPts d L N) {j : ℕ} (hj : j < N)
    {C : Matrix (Lam d L N) (Lam d L N) ℂ} {ℓ q : ℝ} (hℓ : 0 < ℓ) (hq : 0 ≤ q)
    (hC : GoodCov2 j ℓ C) {V W : OFam .two d L N} {K : OAct .two d L N} (H : OAnchS P j V W K)
    (hQ : ∀ b, Tj d (L : ℝ) j ℓ (Q2O P j K b : SA .two (Lam d L N)).ab ≤ ENNReal.ofReal q)
    (X : Finset (Lam d L N)) :
    ‖qABX P j C K X‖ ≤ 2 * (Q1 d * q * ℓ⁻¹ ^ 2) := by
  unfold qABX
  have hQ1 := one_le_Q1 hd
  refine norm_sum_two_le _ _ (blk j P.a) (blk j P.b) (by positivity)
    (fun b _ h1 h2 => by
      rw [ab_eq_zero_of_anch P (H.Q2O_anch b) h1 h2, map_zero, mass2_zero])
    fun b _ => ?_
  refine (norm_mass2_expLC_le_pair hd hL hj hℓ hC P.a P.b (Q2O_ab_mem_pair P j K b)).trans ?_
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hQ b)
  rw [ENNReal.toReal_ofReal hq] at this
  gcongr

/-- **The `T`-norm of `Q'(B)_{ab}` from the `ab` sizes of `K` on small sets.** -/
theorem Tj_Q2O_ab_le (hd : 1 ≤ d) : ∃ CQ : ℝ, 0 ≤ CQ ∧ ∀ (L : ℕ) [NeZero L],
    2 ^ (d + 3) + 8 * d < L → ∀ (N : ℕ) (P : ObsPts d L N) (k : ℕ), k < N → ∀ ℓ : ℝ, 0 < ℓ →
    ∀ (V W : OFam .two d L N) (K : OAct .two d L N), OAnchS P k V W K →
    ∀ κ : ℝ, 0 ≤ κ →
      (∀ X, IsSmall k X → (K X : SA .two (Lam d L N)).ab ∈ NX (nbhd k X : Set (Lam d L N))) →
      (∀ X, IsSmall k X → Tj d (L : ℝ) k ℓ (K X : SA .two (Lam d L N)).ab ≤ ENNReal.ofReal κ) →
      ∀ b, Tj d (L : ℝ) k ℓ (Q2O P k K b : SA .two (Lam d L N)).ab ≤ ENNReal.ofReal (CQ * κ) := by
  classical
  obtain ⟨Cl, hCl, hloc⟩ := exists_locABt_bound d hd
  obtain ⟨cN, hcN⟩ := card_small_containing d
  refine ⟨cN * Cl, by positivity, fun L _ hL N P k hk ℓ hℓ V W K H κ hκ hnx hK b => ?_⟩
  have hCκ : 0 ≤ cN * Cl * κ := by positivity
  by_cases hb : b = blk k P.a ∨ b = blk k P.b
  swap
  · rw [not_or] at hb
    rw [ab_eq_zero_of_anch P (H.Q2O_anch b) hb.1 hb.2, Step.Tj_zero]; exact zero_le
  have hbI : b ∈ blockIdx (L := L) (N := N) k := by
    rw [mem_blockIdx]
    rcases hb with rfl | rfl
    · exact ⟨P.a, mem_blockSet_blk k P.a⟩
    · exact ⟨P.b, mem_blockSet_blk k P.b⟩
  by_cases hN : k + 1 < N
  · rw [Q2O, if_pos hN, AddSubmonoidClass.coe_finsetSum, SA.sum_ab]
    have hX : ∀ X ∈ (smallSets (L := L) (N := N) k).filter (fun X => blockSet k b ⊆ X),
        Tj d (L : ℝ) k ℓ (LocO2 P X (blockSet k b) (K X) : SA .two (Lam d L N)).ab ≤
          ENNReal.ofReal (Cl * κ) := fun X hX' => by
      obtain ⟨hs, hbX⟩ := mem_smallSets_filter.1 hX'
      rw [LocO2_ab, locABtXY]
      by_cases hne : (X ∩ P.pts).Nonempty
      · refine (tNorm_smul_le _ _).trans ?_
        have hr := ENNReal.ofReal_le_ofReal (norm_ratio_le (P := P) hbX)
        rw [ENNReal.ofReal_one] at hr
        refine (mul_le_mul' hr le_rfl).trans ?_
        rw [one_mul, locABtX]
        have key : ∀ (u v : Lam d L N), u ∈ X →
            Tj d (L : ℝ) k ℓ (locABt X u v (K X : SA .two (Lam d L N)).ab) ≤
              ENNReal.ofReal (Cl * κ) := fun u v hu =>
          (hloc L hL N k hk ℓ hℓ X hs u v hu _ (hnx X hs)).trans
            (le_ofReal_mul hCl le_rfl (hK X hs))
        split_ifs with ha
        · exact key _ _ ha
        · exact key _ _ (mem_b_of_inter hne ha)
      · have h0 : (((blockSet k b ∩ P.pts).card : ℂ) / ((X ∩ P.pts).card : ℂ)) = 0 := by
          simp [Finset.not_nonempty_iff_eq_empty.1 hne]
        rw [h0, zero_smul, Step.Tj_zero]
        exact zero_le
    refine (tNorm_sum_le _ _).trans ((le_ofReal_sum_const _ (mul_nonneg hCl hκ) hX).trans
      (ENNReal.ofReal_le_ofReal ?_))
    have := hcN L N k b hbI
    have h2 : ((((smallSets (L := L) (N := N) k).filter
        (fun X => blockSet k b ⊆ X)).card : ℕ) : ℝ) ≤ cN := by exact_mod_cast this
    calc _ ≤ (cN : ℝ) * (Cl * κ) := mul_le_mul_of_nonneg_right h2 (mul_nonneg hCl hκ)
      _ = _ := by ring
  · rw [Q2O, if_neg hN]
    show Tj d (L : ℝ) k ℓ ((0 : OE .two (Lam d L N)) : SA .two (Lam d L N)).ab ≤ _
    rw [show ((0 : OE .two (Lam d L N)) : SA .two (Lam d L N)).ab = 0 from rfl, Step.Tj_zero]
    exact zero_le

/-- The `m₂` Pauli defect of a region is the region quartic coefficient times the gradient
defect. -/
theorem pdefM2X_eq_m4X (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
    (V : OFam .two d L N) (X : Finset (Lam d L N))
    (hV : ∀ b, (V b : SA .two (Lam d L N)).ab ∈ NX ({P.a, P.b} : Set (Lam d L N)))
    (hS : ∀ b, IsSym (V b : SA .two (Lam d L N)).ab) :
    pdefM2X j C V X = m4X P j V X * (C P.a P.a + C P.b P.b - C P.a P.b - C P.b P.a) := by
  rw [pdefM2X, m4X, sum_mul]
  exact sum_congr rfl fun b _ => pauliDef2_of_ab C (hV b) (hS b)

end Pure

section Hist

variable {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  (P : ObsPts 2 L N) {j : ℕ} {o' : ObsSt .two L N} (t : Flow2.Hist.Seq (Xs R))

/-- **The inputs of every step of the reduced history are local.** -/
theorem olocS_hR (h0 : ObsLocInv P j o') {k : ℕ} (hjk : j ≤ k)
    (hv : ∀ i, j ≤ i → i ≤ k → ValidCore R i ∧ RawInv R i (rawHist R i t)) :
    OLocS P k (hVR R P j o' t k) (hWR R P j o' t k) (hKR R P j o' t k) :=
  olocS_full R P (t k).1 (t k).2.1 (hv k hjk le_rfl).1 (hv k hjk le_rfl).2 (rawD_mem R _ _)
    (rawK_mem R _ _)
    (obsLocInv_histFrom' R P h0 t hjk fun i h1 h2 => hv i h1 h2.le)

/-- **Region copy of `pdefM2_hist_le`**: `|𝔡₂_k(X)| ≤ |M₄_k(X)|(nℓ_k/L^{k+1})²` for `b = a + w`. -/
theorem pdefM2X_hVR_le (h0 : ObsVabInv P o') {k : ℕ}
    (hs : ObsSymInv k (obsHistFrom R P j o' k t)) {ℓk : ℝ}
    {C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ} (hC : GoodCov2 k ℓk C)
    (w : List (Dir 2)) (hw : pathEnd P.a w = P.b) (X : Finset (Lam 2 L N)) :
    ‖pdefM2X k C (hVR R P j o' t k) X‖ ≤
      ‖m4X P k (hVR R P j o' t k) X‖ * (w.length * (ℓk / (L : ℝ) ^ (k + 1))) ^ 2 := by
  rw [pdefM2X_eq_m4X P k C _ X (hVR_ab_mem R P j o' t h0 k) (hVR_ab_sym R P j o' t hs), norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have h := norm_m2Def_le2 hC P.a w
  rw [hw] at h
  exact h

end Hist

end

end PtCorr2
