import Obs2.Pair.ShareAB1

/-!
# Region copies of the `errAB2` size lemmas

For a region `X` the error `errABX2` of the region `r'` flow (`Obs2.Pair.ShareAB1`) consists of the
same pieces as `errAB2`, with all block sums restricted to `𝓑(X)`. On anchored inputs only the
blocks of `a` and `b` carry `ab` parts, so the per-block bounds of `Obs2.Est.ErrAB` and
`Obs2.Flow.MuChainAB2` hold verbatim for the region sums:

* `farABmX_eq_zero_of_anch`, **`norm_qABX_le`**, **`norm_wProdABX0_le`**;
* **`norm_errABX2_le`**: the triangle inequality for `errABX2`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 LocObs Flow2

variable {d L N : ℕ} [NeZero L]

/-- **`farABmX = 0` on anchored inputs.** -/
theorem farABmX_eq_zero_of_anch {P : ObsPts d L N} {j : ℕ}
    {C : Matrix (Lam d L N) (Lam d L N) ℂ} {V W : OFam .two d L N} {K : OAct .two d L N}
    (H : OAnchS P j V W K) (X : Finset (Lam d L N)) : farABmX P j C V W X = 0 := by
  unfold farABmX
  refine sum_eq_zero fun c' _ => ?_
  split_ifs with h
  · rfl
  · rw [SXO, AddSubmonoidClass.coe_finsetSum, SA.sum_ab, mass2_sum]
    refine sum_eq_zero fun b hb => ?_
    have hsub : blockSet (L := L) (N := N) j b ⊆ blockSet (L := L) (N := N) (j + 1) c' :=
      blockSet_subset_of_mem_blocks (IsPolymer.of_succ (isPolymer_blockSet (j + 1) c')) hb
    rw [(H.Sb_anch (C := C) b).2.2 fun hne => h (hne.mono (inter_subset_inter_right hsub)),
      mass2_zero]

/-- **`|qAB(X)| ≤ 2Q₁ℓ^{-2}q̄`** on anchored `K`. -/
theorem norm_qABX_le (hd : 1 ≤ d) (hL : pauliL0 d ≤ L) (P : ObsPts d L N) {j : ℕ} (hj : j < N)
    {C : Matrix (Lam d L N) (Lam d L N) ℂ} {ℓ q : ℝ} (hℓ : 0 < ℓ) (hq : 0 ≤ q)
    (hC : GoodCov2 j ℓ C) {V W : OFam .two d L N} {K : OAct .two d L N} (H : OAnchS P j V W K)
    (hloc : ∀ b, (Q2O P j K b : SA .two (Lam d L N)).ab ∈
      NX (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N)))
    (hQ : ∀ b, Tj d (L : ℝ) j ℓ (Q2O P j K b : SA .two (Lam d L N)).ab ≤ ENNReal.ofReal q)
    (X : Finset (Lam d L N)) :
    ‖qABX P j C K X‖ ≤ 2 * (Q1 d * q * ℓ⁻¹ ^ 2) := by
  unfold qABX
  have hQ1 := one_le_Q1 hd
  refine norm_sum_two_le _ _ (blk j P.a) (blk j P.b) (by positivity)
    (fun b _ h1 h2 => by
      rw [ab_eq_zero_of_anch P (H.Q2O_anch b) h1 h2, map_zero, mass2_zero])
    fun b _ => ?_
  refine (norm_mass2_expLC_le hd hL hj hℓ hC (hloc b)).trans ?_
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hQ b)
  rw [ENNReal.toReal_ofReal hq] at this
  gcongr

/-- **The `m₂` of the product part of a region on anchored inputs** (copy of
`norm_wProdAB0_le`). -/
theorem norm_wProdABX0_le {P : ObsPts d L N} {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℂ}
    {V W : OFam .two d L N} {K : OAct .two d L N} (H : OAnchS P j V W K) (k : ℕ)
    {ℓ e o : ℝ} (hℓ : 0 < ℓ) (he : 0 ≤ e) (ho : 0 ≤ o)
    (hWe : ∀ b, Tj d (L : ℝ) k ℓ (WpO P j C V W b : SA .two (Lam d L N)).e ≤ ENNReal.ofReal e)
    (hWo : ∀ b, Tj d (L : ℝ) k ℓ (WpO P j C V W b : SA .two (Lam d L N)).ab ≤
      ENNReal.ofReal o) (X : Finset (Lam d L N)) :
    ‖wProdABX P j C V W X 0‖ ≤
      2 * ((L : ℝ) ^ d * o * ((1 + e) ^ (L ^ d) - 1) * ℓ⁻¹ ^ 2) := by
  have hh : (0 : ℝ) < (L : ℝ) ^ k := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) k
  have hq0 : (0 : ℝ) ≤ (1 + e) ^ (L ^ d) - 1 := by
    have := one_le_pow₀ (n := L ^ d) (show (1 : ℝ) ≤ 1 + e by linarith); linarith
  unfold wProdABX
  simp only [expLC_zero]
  refine norm_sum_two_le _ _ (blk (j + 1) P.a) (blk (j + 1) P.b) (by positivity)
    (fun c' _ h1 h2 => ?_) fun c' _ => ?_
  · have hm : (Wnext2O P j C V W c' - ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
        WpO P j C V W b : OE .two (Lam d L N)) ∈
        (anc P (blockSet (L := L) (N := N) (j + 1) c') : Subalgebra ℂ (OE .two (Lam d L N))) :=
      sub_mem (H.Wnext_anch (C := C) c') (Subalgebra.sum_mem _ fun b hb => anc_mono
        (blockSet_subset (IsPolymer.of_succ (isPolymer_blockSet (j + 1) c')) hb)
        (H.Wp_anch (C := C) b))
    rw [ab_eq_zero_of_anch P hm h1 h2, mass2_zero]
  · set s := blocks j (blockSet (L := L) (N := N) (j + 1) c') with hs
    have hab : ∀ b ∈ s, WpO P j C V W b ∈ (abSub : Subalgebra ℂ (OE .two (Lam d L N))) :=
      fun b _ => anchSub_ab (H.Wp_anch (C := C) b)
    have hP := (oTo_prod_sub_leAB (w := wAB1) hh hℓ s (fun b => WpO P j C V W b) he ho
      (fun b _ => hWe b) (fun b hb => by rw [oTo_wAB1 k ℓ (hab b hb)]; exact hWo b) hab).2
    have hmem : (∏ b ∈ s, (1 + WpO P j C V W b) - 1 - ∑ b ∈ s, WpO P j C V W b :
        OE .two (Lam d L N)) ∈ (abSub : Subalgebra ℂ (OE .two (Lam d L N))) :=
      sub_mem (sub_mem (prod_mem fun b hb => add_mem (one_mem _) (hab b hb)) (one_mem _))
        (Subalgebra.sum_mem _ hab)
    rw [oTo_wAB1 k ℓ hmem] at hP
    have hn : (s.card : ℝ) ≤ (L : ℝ) ^ d := by
      have := nb_blockSet_succ_le (L := L) (N := N) j c'
      unfold nb at this; exact_mod_cast this
    have hn' : s.card ≤ L ^ d := by exact_mod_cast hn
    have hpow : (1 + e) ^ s.card ≤ (1 + e) ^ (L ^ d) :=
      pow_le_pow_right₀ (by linarith) hn'
    have hB : (s.card : ℝ) * o * ((1 + e) ^ s.card - 1) ≤
        (L : ℝ) ^ d * o * ((1 + e) ^ (L ^ d) - 1) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hn ho) (by linarith) (by
        have := one_le_pow₀ (n := s.card) (show (1 : ℝ) ≤ 1 + e by linarith); linarith)
        (by positivity)
    refine (norm_mass2_le hℓ k _).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have e1 : ((Wnext2O P j C V W c' - ∑ b ∈ s, WpO P j C V W b : OE .two (Lam d L N)) :
        SA .two (Lam d L N)).ab = ((∏ b ∈ s, (1 + WpO P j C V W b) - 1 -
          ∑ b ∈ s, WpO P j C V W b : OE .two (Lam d L N)) : SA .two (Lam d L N)).ab := by
      rw [Wnext2O]
    rw [e1]
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hP
    rw [ENNReal.toReal_ofReal (by
      have := one_le_pow₀ (n := s.card) (show (1 : ℝ) ≤ 1 + e by linarith); positivity)] at this
    exact this.trans hB

/-- **The triangle inequality for `errABX2`** when `farABmX_k = 0`. -/
theorem norm_errABX2_le (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : ℕ → OFam .two d L N) (K : ℕ → OAct .two d L N) (X : Finset (Lam d L N)) (j0 k : ℕ)
    (hf : farABmX P k (C k) (V k) (W k) X = 0) :
    ‖errABX2 P C V W K X j0 k‖ ≤ ‖qABX P k (C k) (K k) X‖ + ‖wMassABX P C V W X j0 k‖ +
      ‖pdefM2X k (C k) (V k) X‖ * ‖1 - nA2 P k (C k) (V k)‖ +
      ‖mass2 (FC (C k) (dABX P k (C k) (V k) X) (VprLO k (C k) (V k) : SA .two (Lam d L N)).e)‖ +
      ∑ i ∈ Ico j0 k, ‖memABX P C V W X i k‖ := by
  unfold errABX2
  rw [hf, sub_zero]
  refine (norm_add_le _ _).trans (add_le_add ?_ (norm_sum_le _ _))
  refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
  refine (norm_sub_le _ _).trans (add_le_add ?_ (norm_mul _ _).le)
  exact norm_add_le _ _

end

end Obs2
