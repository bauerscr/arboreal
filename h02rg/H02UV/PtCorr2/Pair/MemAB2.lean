import PtCorr2.Pair.MemAB1
import Step2.Coup.WickSum

/-!
# The memory terms of the reduced `r'` flow, II: top scale, locality, sizes

Continuation of `PtCorr2.Pair.MemAB1` (the `E`-step items of the joint induction, memory part).

* **Validity up to the top scale.** `memABX_hist_le` needs `k < n` with `ValidAtL R n`; the items of
  the joint induction run up to `k = N_h` and the bulk flow only gives `ValidAt` below `N_h` and
  `ValidAtL R N_h`. The proof of `delta_histY_le2` only uses the covariances of the steps `≤ j`, so it
  holds for `j ≤ n` (with `k + 3 ≤ N`): **`delta_histY_le2L`**, `delta_locSz_leL`,
  `norm_memCore_leL`, `norm_memABX_leL`, **`memABX_hist_leL`** (`k ≤ n`, `k + 2 ≤ N`).
* **Locality of the three memory arguments** (the `LocSz` fields of `MemSz`):
  - `Loc S_i(B)_{ab} ∈ 𝒩({a,b})` (**`LSO_ab_mem_pair`**), so **`locSz_of_pair`** applies;
  - the product part of `𝒲'_{i+1}(B_+)` lies in `𝒩((B_+)^□)` (**`prodPart_ab_mem`**, from `OLocS`),
    which is within `5L^{i+1}` of `a` for the block of `a` and within `6L^{i+1}` for the block of
    `b` (**`locSz_prodPart`**);
  - the range of `F_C`: for `D ∈ 𝒩({a,b})` and `G = ∑_{B'}G(B')` with `G(B') ∈ 𝒩(B'^□)` and
    `C` of range `L^{i+1}/2`, **`FC_pair_eq_near`**: `F_C(D, G) = F_C(D, G^{near})`
    (`G^{near}` = the blocks whose neighbourhood comes within `L^{i+1}/2` of `a` or `b`), and
    **`locSz_FC_near`**: `F_C(D, G)` is localised near `a` with the size of `F_C(D, G^{near})`.
  - **`memSz_of_sizes`**: `MemSz` from the three `T_{i+1}(s_{i+1})` sizes.
* **Conversion** (**`mem_conv_le`**, pure): per-scale sizes proportional to `|β_{i+1}|` and the ratio
  `|β_{i+1}| ≤ ρ^{k-i}|β_{k+1}|` give the memory item in the form `s^m_k|β_{k+1}|`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

variable {L N : ℕ} [NeZero L]

section Hist

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

set_option maxHeartbeats 1000000 in
/-- **`delta_histY_le2` up to the top scale**: the same bound for `k < j ≤ n` (`ValidAtL R n`
covers the covariance of step `n` itself), with `k + 3 ≤ N`. For `F ∈ 𝒩(Y)` with `Y` in the box of radius `10L^{k+1}` around `x₀` and
`‖F‖_{T_{k+1}(s_{k+1})} ≤ B`:
`|m₂(e^{ℒ_{C_j + S_{k,j}}}F) − m₂(e^{ℒ_{S_{k,j}}}F)| ≤ 1280K²(8/(7L))^{j−k}B/s_{k+1}²`. -/
theorem delta_histY_le2L (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8) {n : ℕ} (hnN : n < N)
    (hVn : ∀ i < n, ValidAt R i) (hVL : ValidAtL R n) (t : Flow2.Hist.Seq (Xs R))
    (x₀ : Lam 2 L N) {k j : ℕ} (hkj : k < j) (hjn : j ≤ n) (hkN3 : k + 3 ≤ N) (hL : prodLb ≤ L)
    {Y : Set (Lam 2 L N)} (hY : ∀ y ∈ Y, (supNorm (y - x₀) : ℝ) ≤ 10 * (L : ℝ) ^ (k + 1))
    {F : Alg 2 L N} (hF : F ∈ NX Y)
    {B : ℝ} (hB0 : 0 ≤ B) (hFB : Tj 2 (L : ℝ) (k + 1) (histS R (k + 1) t) F ≤ ENNReal.ofReal B) :
    ‖mass2 (expLC (histCovO R t j + cumBetween (histCovO R t) k j) F) -
        mass2 (expLC (cumBetween (histCovO R t) k j) F)‖ ≤
      1280 * locK 2 ^ 2 * (8 / (7 * L) : ℝ) ^ (j - k) * B / histS R (k + 1) t ^ 2 := by
  set s := histS R (k + 1) t with hsdef
  have hs : 0 < s := histS_pos' R hρ0 hρ t (k + 1)
  set K := locK 2
  have hK := one_le_locK 2
  have hLK : 1000 * K ^ 2 + 10 ≤ (L : ℝ) := hL
  have hL10 : (10 : ℝ) ≤ L := by nlinarith [sq_nonneg K]
  have hL0 : (0 : ℝ) < L := by linarith
  set x : ℝ := 8 / (7 * L) with hx
  have hx0 : 0 ≤ x := by positivity
  have hxK : 640 * K ^ 2 * x ≤ 1 := by
    have e : 640 * K ^ 2 * x = 5120 * K ^ 2 / (7 * L) := by rw [hx]; ring
    rw [e, div_le_one (by positivity)]; nlinarith [sq_nonneg K]
  have hK2 : 640 ≤ 640 * K ^ 2 := by nlinarith
  have hx2 : x ≤ 1 / 2 := by
    have : 640 * x ≤ 640 * K ^ 2 * x := mul_le_mul_of_nonneg_right hK2 hx0
    linarith
  set σ : ℝ := s / 4 with hσdef
  have hσ : 0 < σ := by positivity
  set R₀ : ℝ := 10 * (L : ℝ) ^ (k + 1) with hR₀
  have hLk : (1 : ℝ) ≤ (L : ℝ) ^ (k + 1) := one_le_pow₀ (by linarith)
  have hkN : k + 1 + 2 ≤ N := by omega
  have hhR : (L : ℝ) ^ (k + 1) ≤ R₀ := by rw [hR₀]; linarith
  have hR : 2 * ((pPhi 2 : ℕ) : ℝ) + 1 ≤ R₀ := by
    rw [hR₀]; norm_num [pPhi]; linarith
  have hN : 2 * (⌈2 * R₀⌉₊ + 2 * pPhi 2) < L ^ N := by
    have e : ⌈2 * R₀⌉₊ = 20 * L ^ (k + 1) := by
      rw [hR₀, show 2 * (10 * (L : ℝ) ^ (k + 1)) = ((20 * L ^ (k + 1) : ℕ) : ℝ) by push_cast; ring,
        Nat.ceil_natCast]
    rw [e]
    have hL10' : 10 ≤ L := by exact_mod_cast hL10
    have h1 : L ^ N = L ^ (N - (k + 1)) * L ^ (k + 1) := by rw [← pow_add]; congr 1; omega
    have h2 : 100 ≤ L ^ (N - (k + 1)) := by
      calc 100 ≤ L ^ 2 := by nlinarith
        _ ≤ L ^ (N - (k + 1)) := Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : 1 ≤ L ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
    simp only [pPhi]
    nlinarith
  have hrep : ∀ i ∈ Ioo k j, ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (Fv Gv : Lam 2 L N → H), IsGram (histCovO R t i) Fv Gv ∧
        GramBound (Dir 2) (pPhi 2) ((L : ℝ) ^ (i + 1))
          (fscale (stZ' R (rawHist R i t)) * R.ℓ / 4) Fv Gv := fun i hi =>
    (histCovO_props_i R hVn hVL t (i := i) (by have := (mem_Ioo.1 hi).2; omega)).1.gram
  have hrep₁ := (histCovO_props_i R hVn hVL t (i := j) hjn).1.gram
  have hRs : ∀ i ∈ Ioo k j, R₀ ≤ (L : ℝ) ^ (i + 1) := by
    intro i hi
    have hi' := (mem_Ioo.1 hi).1
    calc R₀ ≤ (L : ℝ) * (L : ℝ) ^ (k + 1) := by
          rw [hR₀]; exact mul_le_mul_of_nonneg_right hL10 (by positivity)
      _ = (L : ℝ) ^ (k + 2) := by ring
      _ ≤ (L : ℝ) ^ (i + 1) := pow_le_pow_right₀ (by linarith) (by omega)
  have hR₁ : R₀ ≤ (L : ℝ) ^ (j + 1) := by
    calc R₀ ≤ (L : ℝ) * (L : ℝ) ^ (k + 1) := by
          rw [hR₀]; exact mul_le_mul_of_nonneg_right hL10 (by positivity)
      _ = (L : ℝ) ^ (k + 2) := by ring
      _ ≤ (L : ℝ) ^ (j + 1) := pow_le_pow_right₀ (by linarith) (by omega)
  have hsumS : ∑ i ∈ Ioo k j, locC 2 R₀ (fscale (stZ' R (rawHist R i t)) * R.ℓ / 4)
      ((L : ℝ) ^ (i + 1)) ≤ σ ^ 2 := by
    calc ∑ i ∈ Ioo k j, locC 2 R₀ (fscale (stZ' R (rawHist R i t)) * R.ℓ / 4) ((L : ℝ) ^ (i + 1))
        ≤ ∑ i ∈ Ioo k j, 20 * K ^ 2 * x ^ (i - k) * s ^ 2 :=
          sum_le_sum fun i hi => locC_hist_le R hρ0 hρ t (mem_Ioo.1 hi).1
      _ = 20 * K ^ 2 * s ^ 2 * ∑ i ∈ Ioo k j, x ^ (i - k) := by
          rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
      _ ≤ 20 * K ^ 2 * s ^ 2 * (2 * x) :=
          mul_le_mul_of_nonneg_left (geom_Ioo_le hx0 hx2 k j) (by positivity)
      _ ≤ σ ^ 2 := by
          rw [hσdef]
          have : 0 ≤ s ^ 2 := sq_nonneg s
          nlinarith
  have hxj : x ^ (j - k) ≤ x := by
    have : 1 ≤ j - k := by omega
    calc x ^ (j - k) ≤ x ^ 1 := pow_le_pow_of_le_one hx0 (by linarith) this
      _ = x := pow_one x
  have hCj := locC_hist_le R hρ0 hρ t hkj
  have hsumC : locC 2 R₀ (fscale (stZ' R (rawHist R j t)) * R.ℓ / 4) ((L : ℝ) ^ (j + 1)) ≤
      (2 * σ) ^ 2 := by
    refine hCj.trans ?_
    rw [hσdef]
    have h1 : 20 * K ^ 2 * x ^ (j - k) ≤ 20 * K ^ 2 * x :=
      mul_le_mul_of_nonneg_left hxj (by positivity)
    have : 0 ≤ s ^ 2 := sq_nonneg s
    nlinarith
  have hM : (0 : ℝ) ≤ σ⁻¹ ^ 2 := by positivity
  have key := pauli_lip_loc (d := 2) one_le_two (pauliInv_mass2 (d := 2) (L := L) (N := N))
    (k := k + 1) hσ hM
    (fun G => (norm_mass2_le hσ (k + 1) G).trans_eq (mul_comm _ _)) hhR hR hN x₀ hY hF
    (Ioo k j) (histCovO R t) (fun i => (L : ℝ) ^ (i + 1))
    (fun i => fscale (stZ' R (rawHist R i t)) * R.ℓ / 4)
    (fun i _ => ellI_pos R hρ0 hρ t i) hRs hrep (histCovO R t j) (ellI_pos R hρ0 hρ t j) hR₁
    hrep₁ hsumS hsumC
  have e1 : histCovO R t j + cumBetween (histCovO R t) k j =
      ∑ i ∈ Ioo k j, histCovO R t i + histCovO R t j := by rw [cumBetween, add_comm]
  rw [e1, cumBetween]
  refine key.trans ?_
  rw [show 4 * σ = s by rw [hσdef]; ring]
  have hT : (Tj 2 (L : ℝ) (k + 1) s F).toReal ≤ B := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hFB
    rwa [ENNReal.toReal_ofReal hB0] at this
  have hlc : locC 2 R₀ (fscale (stZ' R (rawHist R j t)) * R.ℓ / 4) ((L : ℝ) ^ (j + 1)) /
      (2 * σ) ^ 2 ≤ 80 * K ^ 2 * x ^ (j - k) := by
    rw [div_le_iff₀ (by positivity)]
    refine hCj.trans (le_of_eq ?_)
    rw [hσdef]; ring
  have hT0 : 0 ≤ (Tj 2 (L : ℝ) (k + 1) s F).toReal := ENNReal.toReal_nonneg
  have hl0 : 0 ≤ locC 2 R₀ (fscale (stZ' R (rawHist R j t)) * R.ℓ / 4) ((L : ℝ) ^ (j + 1)) /
      (2 * σ) ^ 2 := div_nonneg (locC_nonneg (by positivity) (by positivity)) (by positivity)
  calc σ⁻¹ ^ 2 * (locC 2 R₀ (fscale (stZ' R (rawHist R j t)) * R.ℓ / 4) ((L : ℝ) ^ (j + 1)) /
        (2 * σ) ^ 2) * (Tj 2 (L : ℝ) (k + 1) s F).toReal
      ≤ σ⁻¹ ^ 2 * (80 * K ^ 2 * x ^ (j - k)) * B :=
        mul_le_mul (mul_le_mul_of_nonneg_left hlc hM) hT hT0 (by positivity)
    _ = _ := by rw [hσdef]; field_simp; ring


/-- `delta_histY_le2L` with `LocSz`. -/
theorem delta_locSz_leL (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8) {n : ℕ} (hnN : n < N)
    (hVn : ∀ i < n, ValidAt R i) (hVL : ValidAtL R n) (t : Flow2.Hist.Seq (Xs R))
    (x₀ : Lam 2 L N) {i k : ℕ} (hik : i < k) (hkn : k ≤ n) (hiN : i + 3 ≤ N) (hL : prodLb ≤ L)
    {F : Alg 2 L N} {B : ℝ} (hB0 : 0 ≤ B) (hF : LocSz R t x₀ i F B) :
    ‖mass2 (expLC (histCovO R t k + cumBetween (histCovO R t) i k) F) -
        mass2 (expLC (cumBetween (histCovO R t) i k) F)‖ ≤ memKer R t i k * B := by
  obtain ⟨Y, hY, hFY, hFB⟩ := hF
  refine (delta_histY_le2L R hρ0 hρ hnN hVn hVL t x₀ hik hkn hiN hL hY hFY hB0 hFB).trans
    (le_of_eq ?_)
  unfold memKer; ring



/-- `norm_memCore_le` up to the top scale (`k ≤ n`): the three tadpole differences of a memory term, for any block sets `sL ⊆` (scale `i`) and
`sP` (scale `i + 1`) and gradient element `DF`. -/
theorem norm_memCore_leL (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8) {n : ℕ} (hnN : n < N)
    (hVn : ∀ i < n, ValidAt R i) (hVL : ValidAtL R n) (t : Flow2.Hist.Seq (Xs R))
    (P : ObsPts 2 L N) {i k : ℕ} (hik : i < k) (hkn : k ≤ n) (hiN : i + 3 ≤ N) (hL : prodLb ≤ L)
    {V W : OFam .two 2 L N} {K : OAct .two 2 L N} (H : OAnchS P i V W K)
    (sL sP : Finset (Fin 2 → ℕ)) {DF : Alg 2 L N} {f lam w : ℝ} (hf : 0 ≤ f) (hl : 0 ≤ lam)
    (hw : 0 ≤ w) (hS : MemSz R t P i DF V W f lam w) :
    let Γ₁ := histCovO R t k + cumBetween (histCovO R t) i k
    let Γ₀ := cumBetween (histCovO R t) i k
    ‖((mass2 (expLC Γ₁ DF) - mass2 DF) - (mass2 (expLC Γ₀ DF) - mass2 DF)) -
        (∑ b ∈ sL, (mass2 (expLC Γ₁ (LSO P i (histCovO R t i) V W b : SA .two (Lam 2 L N)).ab) -
            mass2 (LSO P i (histCovO R t i) V W b : SA .two (Lam 2 L N)).ab) -
          ∑ b ∈ sL, (mass2 (expLC Γ₀ (LSO P i (histCovO R t i) V W b : SA .two (Lam 2 L N)).ab) -
            mass2 (LSO P i (histCovO R t i) V W b : SA .two (Lam 2 L N)).ab)) +
        (∑ c' ∈ sP, mass2 (expLC Γ₁ ((Wnext2O P i (histCovO R t i) V W c' -
            ∑ b ∈ blocks i (blockSet (L := L) (N := N) (i + 1) c'),
              WpO P i (histCovO R t i) V W b : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).ab) -
          ∑ c' ∈ sP, mass2 (expLC Γ₀ ((Wnext2O P i (histCovO R t i) V W c' -
            ∑ b ∈ blocks i (blockSet (L := L) (N := N) (i + 1) c'),
              WpO P i (histCovO R t i) V W b : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).ab))‖ ≤
      memKer R t i k * (f + 2 * lam + 2 * w) := by
  intro Γ₁ Γ₀
  have hK := memKer_nonneg R hρ0 hρ t i k
  have h1 : ‖(mass2 (expLC Γ₁ DF) - mass2 DF) - (mass2 (expLC Γ₀ DF) - mass2 DF)‖ ≤
      memKer R t i k * f := by
    rw [sub_sub_sub_cancel_right]
    exact delta_locSz_leL R hρ0 hρ hnN hVn hVL t P.a hik hkn hiN hL hf hS.hD
  have h2 := norm_sum_tad_diff_le sL
    (fun b => (LSO P i (histCovO R t i) V W b : SA .two (Lam 2 L N)).ab) Γ₁ Γ₀
    (blk i P.a) (blk i P.b) (mul_nonneg hK hl)
    (fun b _ h1 h2 => LSO_ab_zero H h1 h2)
    (fun b _ hb => delta_locSz_leL R hρ0 hρ hnN hVn hVL t P.a hik hkn hiN hL hl (hS.hLS b hb))
  have h3 := norm_sum_tad_diff_le' sP
    (fun c' => ((Wnext2O P i (histCovO R t i) V W c' -
      ∑ b ∈ blocks i (blockSet (L := L) (N := N) (i + 1) c'),
        WpO P i (histCovO R t i) V W b : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).ab) Γ₁ Γ₀
    (blk (i + 1) P.a) (blk (i + 1) P.b) (mul_nonneg hK hw)
    (fun c' _ h1 h2 => prodPart_ab_zero H h1 h2)
    (fun c' _ hc => delta_locSz_leL R hρ0 hρ hnN hVn hVL t P.a hik hkn hiN hL hw (hS.hPr c' hc))
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add ((norm_sub_le _ _).trans (add_le_add h1 h2)) h3).trans (le_of_eq ?_)
  ring


/-- **One memory term of a region** `memABX i k` for `i < k ≤ n` (`ValidAtL R n`). -/
theorem norm_memABX_leL (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8) {n : ℕ} (hnN : n < N)
    (hVn : ∀ i < n, ValidAt R i) (hVL : ValidAtL R n) (t : Flow2.Hist.Seq (Xs R))
    (P : ObsPts 2 L N) {i k : ℕ} (hik : i < k) (hkn : k ≤ n) (hiN : i + 3 ≤ N) (hL : prodLb ≤ L)
    (V W : ℕ → OFam .two 2 L N) {K : OAct .two 2 L N} (H : OAnchS P i (V i) (W i) K)
    (X : Finset (Lam 2 L N)) {p τ f lam w : ℝ} (hf : 0 ≤ f) (hl : 0 ≤ lam) (hw : 0 ≤ w)
    (hp : ‖pdefM2X i (histCovO R t i) (V i) X‖ ≤ p)
    (hτ : ‖tadInc2 P (histCovO R t) V i k‖ ≤ τ)
    (hS : MemSz R t P i (FC (histCovO R t i) (dABX P i (histCovO R t i) (V i) X)
      (VprLO i (histCovO R t i) (V i) : SA .two (Lam 2 L N)).e) (V i) (W i) f lam w) :
    ‖memABX P (histCovO R t) V W X i k‖ ≤ p * τ + memKer R t i k * (f + 2 * lam + 2 * w) := by
  have hc := norm_memCore_leL R hρ0 hρ hnN hVn hVL t P hik hkn hiN hL H
    (blocks i X) (blocks (i + 1) X) hf hl hw hS
  simp only at hc
  have hpt : ‖pdefM2X i (histCovO R t i) (V i) X * tadInc2 P (histCovO R t) V i k‖ ≤ p * τ := by
    rw [norm_mul]
    exact mul_le_mul hp hτ (norm_nonneg _) ((norm_nonneg _).trans hp)
  refine le_trans (le_of_eq ?_) ((norm_add_le _ _).trans (add_le_add hpt hc))
  unfold memABX dTauABX pdefLSX wProdABX
  congr 1; ring

/-! ### The summed bounds -/

/-- **The memory sum of a region up to the top scale** (`k ≤ n`, `ValidAtL R n`). -/
theorem memABX_hist_leL (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8) {n : ℕ} (hnN : n < N)
    (hVn : ∀ i < n, ValidAt R i) (hVL : ValidAtL R n) (t : Flow2.Hist.Seq (Xs R))
    (P : ObsPts 2 L N) (hL : prodLb ≤ L) (V W : ℕ → OFam .two 2 L N) (K : ℕ → OAct .two 2 L N)
    (X : Finset (Lam 2 L N))
    {j k : ℕ} (hkn : k ≤ n) (hkN : k + 2 ≤ N) (H : ∀ i, j ≤ i → i < k → OAnchS P i (V i) (W i) (K i))
    (p f lam w : ℕ → ℝ) (τ : ℕ → ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) (hl : ∀ i, 0 ≤ lam i)
    (hw : ∀ i, 0 ≤ w i)
    (hp : ∀ i, j ≤ i → i < k → ‖pdefM2X i (histCovO R t i) (V i) X‖ ≤ p i)
    (hτ : ∀ i, j ≤ i → i < k → ‖tadInc2 P (histCovO R t) V i k‖ ≤ τ i k)
    (hS : ∀ i, j ≤ i → i < k → MemSz R t P i (FC (histCovO R t i)
      (dABX P i (histCovO R t i) (V i) X) (VprLO i (histCovO R t i) (V i) : SA .two (Lam 2 L N)).e)
      (V i) (W i) (f i) (lam i) (w i)) :
    ∑ i ∈ Ico j k, ‖memABX P (histCovO R t) V W X i k‖ ≤
      ∑ i ∈ Ico j k, (p i * τ i k + memKer R t i k * (f i + 2 * lam i + 2 * w i)) :=
  sum_le_sum fun i hi => by
    obtain ⟨h1, h2⟩ := mem_Ico.1 hi
    exact norm_memABX_leL R hρ0 hρ hnN hVn hVL t P h2 hkn (by omega) hL V W (H i h1 h2) X (hf i) (hl i)
      (hw i) (hp i h1 h2) (hτ i h1 h2) (hS i h1 h2)

end Hist

/-! ### Geometry of block neighbourhoods -/

section Geom

theorem supNorm_le_of_mem_nbhd_blk {j : ℕ} {p y : Lam 2 L N}
    (hy : y ∈ nbhd j (blockSet (L := L) (N := N) j (blk j p))) :
    (supNorm (y - p) : ℝ) ≤ 5 * (L : ℝ) ^ j := by
  obtain ⟨z, hz, hyz⟩ := exists_near_of_mem_nbhd hy
  have hzp : supNorm (z - p) < L ^ j := supNorm_lt_of_blk_eq (mem_blockSet.1 hz)
  have h := supNorm_tri y z p
  have h1 : (supNorm (y - p) : ℝ) ≤ (supNorm (y - z) : ℝ) + (supNorm (z - p) : ℝ) := by
    exact_mod_cast h
  have h2 : (supNorm (y - z) : ℝ) ≤ 4 * (L : ℝ) ^ j := by
    have : ((supNorm (y - z) : ℕ) : ℝ) ≤ ((2 ^ 2 * L ^ j : ℕ) : ℝ) := by exact_mod_cast hyz
    push_cast at this; linarith
  have h3 : (supNorm (z - p) : ℝ) ≤ (L : ℝ) ^ j := by
    have : ((supNorm (z - p) : ℕ) : ℝ) ≤ ((L ^ j : ℕ) : ℝ) := by exact_mod_cast hzp.le
    push_cast at this; exact this
  linarith

theorem supNorm_le_of_mem_nbhd_same {j : ℕ} {c : Fin 2 → ℕ} {y z : Lam 2 L N}
    (hy : y ∈ nbhd j (blockSet (L := L) (N := N) j c))
    (hz : z ∈ nbhd j (blockSet (L := L) (N := N) j c)) :
    (supNorm (y - z) : ℝ) ≤ 9 * (L : ℝ) ^ j := by
  obtain ⟨w₁, hw₁, h1⟩ := exists_near_of_mem_nbhd hy
  obtain ⟨w₂, hw₂, h2⟩ := exists_near_of_mem_nbhd hz
  have hw : supNorm (w₁ - w₂) < L ^ j :=
    supNorm_lt_of_blk_eq ((mem_blockSet.1 hw₁).trans (mem_blockSet.1 hw₂).symm)
  have t1 := supNorm_tri y w₁ z
  have t2 := supNorm_tri w₁ w₂ z
  have e : supNorm (w₂ - z) = supNorm (z - w₂) := supNorm_sub_comm _ _
  have h1' : ((supNorm (y - w₁) : ℕ) : ℝ) ≤ 4 * (L : ℝ) ^ j := by
    have : ((supNorm (y - w₁) : ℕ) : ℝ) ≤ ((2 ^ 2 * L ^ j : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at this; linarith
  have h2' : ((supNorm (z - w₂) : ℕ) : ℝ) ≤ 4 * (L : ℝ) ^ j := by
    have : ((supNorm (z - w₂) : ℕ) : ℝ) ≤ ((2 ^ 2 * L ^ j : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at this; linarith
  have hw' : ((supNorm (w₁ - w₂) : ℕ) : ℝ) ≤ (L : ℝ) ^ j := by
    have : ((supNorm (w₁ - w₂) : ℕ) : ℝ) ≤ ((L ^ j : ℕ) : ℝ) := by exact_mod_cast hw.le
    push_cast at this; exact this
  have t1' : ((supNorm (y - z) : ℕ) : ℝ) ≤ (supNorm (y - w₁) : ℝ) + (supNorm (w₁ - z) : ℝ) := by
    exact_mod_cast t1
  have t2' : ((supNorm (w₁ - z) : ℕ) : ℝ) ≤ (supNorm (w₁ - w₂) : ℝ) + (supNorm (z - w₂) : ℝ) := by
    rw [← e]; exact_mod_cast t2
  linarith

end Geom

/-! ### Locality of the memory arguments -/

section Loc

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- An element of `𝒩({a,b})` is localised near `a` (`|b − a|_∞ ≤ L^{i+1}`). -/
theorem locSz_of_pair (t : Flow2.Hist.Seq (Xs R)) {a b : Lam 2 L N} {i : ℕ}
    (hab : (supNorm (b - a) : ℝ) ≤ (L : ℝ) ^ (i + 1)) {F : Alg 2 L N}
    (hF : F ∈ NX ({a, b} : Set (Lam 2 L N))) {B : ℝ}
    (hB : Tj 2 (L : ℝ) (i + 1) (histS R (i + 1) t) F ≤ ENNReal.ofReal B) :
    LocSz R t a i F B := by
  refine ⟨{a, b}, fun y hy => ?_, hF, hB⟩
  have hL : (0 : ℝ) ≤ (L : ℝ) ^ (i + 1) := by positivity
  rcases hy with rfl | hy
  · rw [sub_self, supNorm_zero]; push_cast; linarith
  · rw [Set.mem_singleton_iff.1 hy]; linarith

/-- `Loc S_i(B)_{ab} ∈ 𝒩({a,b})`. -/
theorem LSO_ab_mem_pair (P : ObsPts 2 L N) (i : ℕ) (C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ)
    (V W : OFam .two 2 L N) (b : Fin 2 → ℕ) :
    (LSO P i C V W b : SA .two (Lam 2 L N)).ab ∈ NX ({P.a, P.b} : Set (Lam 2 L N)) := by
  rw [LSO, LocO2_ab]; exact locABtXY_mem P _ _ _

/-- **The product part of `𝒲'_{i+1}(B_+)` is supported in `(B_+)^□`.** -/
theorem prodPart_ab_mem {P : ObsPts 2 L N} {i : ℕ} {C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ}
    {V W : OFam .two 2 L N} {K : OAct .two 2 L N} (H : OLocS P i V W K)
    (hL : 2 ^ (2 + 3) ≤ L) (hiN : i + 1 < N) (hC : CovRange i C) (c' : Fin 2 → ℕ) :
    ((Wnext2O P i C V W c' - ∑ b ∈ blocks i (blockSet (L := L) (N := N) (i + 1) c'),
      WpO P i C V W b : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).ab ∈
      NX (nbhd (i + 1) (blockSet (L := L) (N := N) (i + 1) c') : Set (Lam 2 L N)) := by
  have hm : (Wnext2O P i C V W c' - ∑ b ∈ blocks i (blockSet (L := L) (N := N) (i + 1) c'),
      WpO P i C V W b : OE .two (Lam 2 L N)) ∈
      osub P (nbhd (i + 1) (blockSet (L := L) (N := N) (i + 1) c')) :=
    sub_mem (H.Wnext_mem one_le_two hL hiN hC c') (Subalgebra.sum_mem _ fun b hb =>
      osub_mono (nbhd_mono (Bp_subset_block hb))
        (H.Wp_mem one_le_two hL hiN hC (mem_blockIdx_of_mem_blocks hb)))
  exact hm.2.2.2.1

/-- **Locality of the product part** for the `(i+1)`-blocks of `a` and `b`. -/
theorem locSz_prodPart (t : Flow2.Hist.Seq (Xs R)) {P : ObsPts 2 L N} {i : ℕ}
    {C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ} {V W : OFam .two 2 L N} {K : OAct .two 2 L N}
    (H : OLocS P i V W K) (hL : 2 ^ (2 + 3) ≤ L) (hiN : i + 1 < N) (hC : CovRange i C)
    (hab : (supNorm (P.b - P.a) : ℝ) ≤ (L : ℝ) ^ (i + 1)) {c' : Fin 2 → ℕ}
    (hc : c' = blk (i + 1) P.a ∨ c' = blk (i + 1) P.b) {w : ℝ}
    (hw : Tj 2 (L : ℝ) (i + 1) (histS R (i + 1) t)
      ((Wnext2O P i C V W c' - ∑ b ∈ blocks i (blockSet (L := L) (N := N) (i + 1) c'),
        WpO P i C V W b : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).ab ≤ ENNReal.ofReal w) :
    LocSz R t P.a i
      ((Wnext2O P i C V W c' - ∑ b ∈ blocks i (blockSet (L := L) (N := N) (i + 1) c'),
        WpO P i C V W b : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).ab w := by
  refine ⟨_, fun y hy => ?_, prodPart_ab_mem H hL hiN hC c', hw⟩
  have hL0 : (0 : ℝ) ≤ (L : ℝ) ^ (i + 1) := by positivity
  rcases hc with rfl | rfl
  · have := supNorm_le_of_mem_nbhd_blk (L := L) (N := N) (Finset.mem_coe.1 hy); linarith
  · have h1 := supNorm_le_of_mem_nbhd_blk (L := L) (N := N) (Finset.mem_coe.1 hy)
    have h2 := supNorm_tri y P.b P.a
    have h2' : (supNorm (y - P.a) : ℝ) ≤ (supNorm (y - P.b) : ℝ) + (supNorm (P.b - P.a) : ℝ) := by
      exact_mod_cast h2
    linarith

/-- **`Loc S_i(B)_{ab}` is localised near `a`.** -/
theorem locSz_LSO (t : Flow2.Hist.Seq (Xs R)) (P : ObsPts 2 L N) {i : ℕ}
    (C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ) (V W : OFam .two 2 L N) (b : Fin 2 → ℕ)
    (hab : (supNorm (P.b - P.a) : ℝ) ≤ (L : ℝ) ^ (i + 1)) {lam : ℝ}
    (hl : Tj 2 (L : ℝ) (i + 1) (histS R (i + 1) t) (LSO P i C V W b : SA .two (Lam 2 L N)).ab ≤
      ENNReal.ofReal lam) :
    LocSz R t P.a i (LSO P i C V W b : SA .two (Lam 2 L N)).ab lam :=
  locSz_of_pair R t hab (LSO_ab_mem_pair P i C V W b) hl

/-! #### The range of `F_C` -/

/-- The `j`-blocks whose neighbourhood comes within `L^{j+1}/2` of `a` or `b`. -/
def NearAB (a b : Lam 2 L N) (j : ℕ) (c : Fin 2 → ℕ) : Prop :=
  ∃ y ∈ nbhd j (blockSet (L := L) (N := N) j c),
    2 * supNorm (y - a) < L ^ (j + 1) ∨ 2 * supNorm (y - b) < L ^ (j + 1)

open Classical in
/-- The near part `∑_{B' near a, b} G(B')`. -/
def gNear (a b : Lam 2 L N) (j : ℕ) (s : Finset (Fin 2 → ℕ)) (G : (Fin 2 → ℕ) → Alg 2 L N) :
    Alg 2 L N :=
  ∑ c ∈ s.filter (NearAB a b j), G c

/-- **Finite range of `F_C`**: `F_C(D, ∑_{B'}G(B')) = F_C(D, G^{near})` for `D ∈ 𝒩({a,b})`,
`G(B') ∈ 𝒩(B'^□)`, `C` of range `L^{j+1}/2`. -/
theorem FC_pair_eq_near {j : ℕ} {C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ} (hC : CovRange j C)
    {a b : Lam 2 L N} {D : Alg 2 L N} (hD : D ∈ NX ({a, b} : Set (Lam 2 L N)))
    (G : (Fin 2 → ℕ) → Alg 2 L N)
    (hG : ∀ c, G c ∈ NX (nbhd j (blockSet (L := L) (N := N) j c) : Set (Lam 2 L N)))
    (s : Finset (Fin 2 → ℕ)) :
    FC C D (∑ c ∈ s, G c) = FC C D (gNear a b j s G) := by
  classical
  unfold gNear
  rw [← sum_filter_add_sum_filter_not s (NearAB a b j), FC_add_right,
    FC_sum_right (s.filter fun c => ¬ NearAB a b j c)]
  rw [sum_eq_zero (s := s.filter fun c => ¬ NearAB a b j c) (fun c hc => ?_), add_zero]
  have hnc := (mem_filter.1 hc).2
  have hfar : ∀ y ∈ nbhd j (blockSet (L := L) (N := N) j c),
      L ^ (j + 1) ≤ 2 * supNorm (y - a) ∧ L ^ (j + 1) ≤ 2 * supNorm (y - b) := by
    intro y hy
    by_contra h
    rw [not_and_or, not_le, not_le] at h
    exact hnc ⟨y, hy, h⟩
  have hpos : 0 < L ^ (j + 1) := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
  have hreal : ∀ x y : Lam 2 L N, L ^ (j + 1) ≤ 2 * supNorm (y - x) →
      C x y = 0 ∧ C y x = 0 := by
    intro x y h
    have h' : ((L : ℝ) ^ (j + 1)) / 2 ≤ (supNorm (y - x) : ℝ) := by
      have h4 : ((L ^ (j + 1) : ℕ) : ℝ) ≤ ((2 * supNorm (y - x) : ℕ) : ℝ) := Nat.cast_le.2 h
      push_cast at h4; linarith
    have e : supNorm (x - y) = supNorm (y - x) := supNorm_sub_comm _ _
    exact ⟨hC x y (by rw [e]; exact h'), hC y x h'⟩
  refine FC_eq_zero_of_disjoint C (X := ({a, b} : Set (Lam 2 L N)))
    (Y := (nbhd j (blockSet (L := L) (N := N) j c) : Set (Lam 2 L N))) ?_ ?_ hD (hG c)
  · rw [Set.disjoint_left]
    intro z hz hz'
    have h3 := hfar z (Finset.mem_coe.1 hz')
    rcases hz with rfl | hz
    · have := h3.1; rw [sub_self, supNorm_zero, mul_zero] at this; omega
    · rw [Set.mem_singleton_iff.1 hz] at h3
      have := h3.2; rw [sub_self, supNorm_zero, mul_zero] at this; omega
  · intro x hx y hy
    have h3 := hfar y (Finset.mem_coe.1 hy)
    rcases hx with rfl | hx
    · exact hreal x y h3.1
    · rw [Set.mem_singleton_iff.1 hx]; exact hreal b y h3.2

/-- The near part lies in the box of radius `10L^{j+1}` around `a`. -/
theorem gNear_mem {j : ℕ} {a b : Lam 2 L N} (hL : 9 ≤ L)
    (hab : (supNorm (b - a) : ℝ) ≤ (L : ℝ) ^ (j + 1)) (G : (Fin 2 → ℕ) → Alg 2 L N)
    (hG : ∀ c, G c ∈ NX (nbhd j (blockSet (L := L) (N := N) j c) : Set (Lam 2 L N)))
    (s : Finset (Fin 2 → ℕ)) :
    ∃ Y : Set (Lam 2 L N), (∀ y ∈ Y, (supNorm (y - a) : ℝ) ≤ 10 * (L : ℝ) ^ (j + 1)) ∧
      ({a, b} : Set (Lam 2 L N)) ⊆ Y ∧ gNear a b j s G ∈ NX Y := by
  classical
  set Y : Set (Lam 2 L N) := {a, b} ∪
    {y | ∃ c, NearAB a b j c ∧ y ∈ nbhd j (blockSet (L := L) (N := N) j c)} with hY
  have hL0 : (0 : ℝ) ≤ (L : ℝ) ^ j := by positivity
  have hLj : 9 * (L : ℝ) ^ j ≤ (L : ℝ) ^ (j + 1) := by
    rw [pow_succ, mul_comm ((L : ℝ) ^ j)]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hL) hL0
  refine ⟨Y, fun y hy => ?_, Set.subset_union_left, ?_⟩
  · rcases hy with hy | ⟨c, ⟨y₀, hy₀, hnear⟩, hy⟩
    · rcases hy with rfl | hy
      · rw [sub_self, supNorm_zero]; push_cast; positivity
      · rw [Set.mem_singleton_iff.1 hy]; linarith
    · have hd := supNorm_le_of_mem_nbhd_same (L := L) (N := N) hy hy₀
      rcases hnear with h | h
      · have h' : (2 * supNorm (y₀ - a) : ℝ) ≤ (L : ℝ) ^ (j + 1) := by
          have : ((2 * supNorm (y₀ - a) : ℕ) : ℝ) ≤ ((L ^ (j + 1) : ℕ) : ℝ) :=
            Nat.cast_le.2 h.le
          push_cast at this; exact this
        have t := supNorm_tri y y₀ a
        have t' : (supNorm (y - a) : ℝ) ≤ (supNorm (y - y₀) : ℝ) + (supNorm (y₀ - a) : ℝ) := by
          exact_mod_cast t
        linarith
      · have h' : (2 * supNorm (y₀ - b) : ℝ) ≤ (L : ℝ) ^ (j + 1) := by
          have : ((2 * supNorm (y₀ - b) : ℕ) : ℝ) ≤ ((L ^ (j + 1) : ℕ) : ℝ) :=
            Nat.cast_le.2 h.le
          push_cast at this; exact this
        have t := supNorm_tri y y₀ a
        have t2 := supNorm_tri y₀ b a
        have t' : (supNorm (y - a) : ℝ) ≤ (supNorm (y - y₀) : ℝ) + (supNorm (y₀ - a) : ℝ) := by
          exact_mod_cast t
        have t2' : (supNorm (y₀ - a) : ℝ) ≤ (supNorm (y₀ - b) : ℝ) + (supNorm (b - a) : ℝ) := by
          exact_mod_cast t2
        linarith
  · unfold gNear
    refine Subalgebra.sum_mem _ fun c hc => NX_mono ?_ (hG c)
    intro y hy
    exact Or.inr ⟨c, (mem_filter.1 hc).2, Finset.mem_coe.1 hy⟩

/-- **Locality of `F_C(D, G)`** with the size of `F_C(D, G^{near})`. -/
theorem locSz_FC_near (t : Flow2.Hist.Seq (Xs R)) {i : ℕ} {C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ}
    (hC : CovRange i C) {a b : Lam 2 L N} (hL : 9 ≤ L)
    (hab : (supNorm (b - a) : ℝ) ≤ (L : ℝ) ^ (i + 1)) {D : Alg 2 L N}
    (hD : D ∈ NX ({a, b} : Set (Lam 2 L N))) (G : (Fin 2 → ℕ) → Alg 2 L N)
    (hG : ∀ c, G c ∈ NX (nbhd i (blockSet (L := L) (N := N) i c) : Set (Lam 2 L N)))
    (s : Finset (Fin 2 → ℕ)) {f : ℝ}
    (hf : Tj 2 (L : ℝ) (i + 1) (histS R (i + 1) t) (FC C D (gNear a b i s G)) ≤
      ENNReal.ofReal f) :
    LocSz R t a i (FC C D (∑ c ∈ s, G c)) f := by
  rw [FC_pair_eq_near hC hD G hG s]
  obtain ⟨Y, hY, hsub, hmem⟩ := gNear_mem hL hab G hG s
  exact ⟨Y, hY, FC_mem_NX C (NX_mono hsub hD) hmem, hf⟩

/-! #### `MemSz` from the three sizes -/

theorem VprLO_e_eq (j : ℕ) (C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ) (V : OFam .two 2 L N) :
    (VprLO j C V : SA .two (Lam 2 L N)).e =
      ∑ c ∈ blockIdx (L := L) (N := N) j, (VprO C V c : SA .two (Lam 2 L N)).e := by
  rw [VprLO, AddSubmonoidClass.coe_finsetSum, SA.sum_e]

/-- The gradient part of a region lies in `𝒩({a,b})`. -/
theorem dABX_mem_pair (P : ObsPts 2 L N) (j : ℕ) (C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ)
    (V : OFam .two 2 L N) (X : Finset (Lam 2 L N))
    (hV : ∀ b, (V b : SA .two (Lam 2 L N)).ab ∈ NX ({P.a, P.b} : Set (Lam 2 L N))) :
    dABX P j C V X ∈ NX ({P.a, P.b} : Set (Lam 2 L N)) := by
  have hX : (VprXO j C V X : SA .two (Lam 2 L N)).ab ∈ NX ({P.a, P.b} : Set (Lam 2 L N)) := by
    rw [VprXO, AddSubmonoidClass.coe_finsetSum, SA.sum_ab]
    exact Subalgebra.sum_mem _ fun b _ => by
      rw [VprO, (EthO_comp C (V b)).2.2]; exact expLC_mem_NX C (hV b)
  unfold dABX
  refine sub_mem hX (add_mem (Subalgebra.smul_mem _ (one_mem _) _)
    (Subalgebra.smul_mem _ (NX_mono (by simp) (pbp_mem_NX P.a)) _))

/-- **`MemSz` from the sizes** of `F_C(D, V'^{near}_∅)`, of `Loc S_i(B)_{ab}` and of the product
parts, for `D ∈ 𝒩({a,b})` (locality from `OLocS` and the finite range of `C_i`). -/
theorem memSz_of_sizes (t : Flow2.Hist.Seq (Xs R)) (P : ObsPts 2 L N) {i : ℕ}
    {V W : OFam .two 2 L N} {K : OAct .two 2 L N} (H : OLocS P i V W K)
    (hL : 2 ^ (2 + 3) ≤ L) (hiN : i + 1 < N) (hC : CovRange i (histCovO R t i))
    (hab : (supNorm (P.b - P.a) : ℝ) ≤ (L : ℝ) ^ (i + 1)) {D : Alg 2 L N}
    (hD : D ∈ NX ({P.a, P.b} : Set (Lam 2 L N))) {f lam w : ℝ}
    (hf : Tj 2 (L : ℝ) (i + 1) (histS R (i + 1) t) (FC (histCovO R t i) D
      (gNear P.a P.b i (blockIdx (L := L) (N := N) i)
        fun c => (VprO (histCovO R t i) V c : SA .two (Lam 2 L N)).e)) ≤ ENNReal.ofReal f)
    (hl : ∀ b, (b = blk i P.a ∨ b = blk i P.b) → Tj 2 (L : ℝ) (i + 1) (histS R (i + 1) t)
      (LSO P i (histCovO R t i) V W b : SA .two (Lam 2 L N)).ab ≤ ENNReal.ofReal lam)
    (hw : ∀ c', (c' = blk (i + 1) P.a ∨ c' = blk (i + 1) P.b) →
      Tj 2 (L : ℝ) (i + 1) (histS R (i + 1) t)
        ((Wnext2O P i (histCovO R t i) V W c' -
          ∑ b ∈ blocks i (blockSet (L := L) (N := N) (i + 1) c'),
            WpO P i (histCovO R t i) V W b : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).ab ≤
        ENNReal.ofReal w) :
    MemSz R t P i (FC (histCovO R t i) D (VprLO i (histCovO R t i) V : SA .two (Lam 2 L N)).e)
      V W f lam w := by
  have hL9 : 9 ≤ L := le_trans (by norm_num) hL
  refine ⟨?_, fun b hb => locSz_LSO R t P _ V W b hab (hl b hb),
    fun c' hc => locSz_prodPart R t H hL hiN hC hab hc (hw c' hc)⟩
  rw [VprLO_e_eq]
  exact locSz_FC_near R t hC hL9 hab hD _ (fun c => (H.Vpr_mem c).1) _ hf

end Loc

/-! ### Conversion of the memory bounds (pure) -/

/-- Iterating a one-step ratio `β_i ≤ ρβ_{i+1}` (`i < K`): `β_{i+1} ≤ ρ^{k-i}β_{k+1}` for
`i < k ≤ K`… stated as `β_i ≤ ρ^{k-i}β_k` for `i ≤ k ≤ K`. -/
theorem ratio_pow_le {β : ℕ → ℝ} {ρ : ℝ} (hρ : 1 ≤ ρ) {K : ℕ}
    (h : ∀ i < K, β i ≤ ρ * β (i + 1)) (hβ : ∀ i, 0 ≤ β i) :
    ∀ i k, i ≤ k → k ≤ K → β i ≤ ρ ^ (k - i) * β k := by
  intro i k hik hkK
  induction k, hik using Nat.le_induction with
  | base => simp
  | succ k hik ih =>
    have h1 := ih (by omega)
    have h2 := h k (by omega)
    rw [show k + 1 - i = (k - i) + 1 by omega, pow_succ, mul_assoc]
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (pow_nonneg (by linarith) _))

/-- **The memory item in `s^m_k|β_{k+1}|` form**: if the summand at scale `i` is at most
`U_i·β_{i+1}` and `β_{i+1} ≤ ρ^{k-i}β_{k+1}`, then the sum is at most
`(∑_iU_iρ^{k-i})·β_{k+1}`. -/
theorem mem_conv_le {j k : ℕ} (a U β : ℕ → ℝ) (ρ : ℝ) (hU : ∀ i, 0 ≤ U i)
    (ha : ∀ i ∈ Finset.Ico j k, a i ≤ U i * β (i + 1))
    (hβ : ∀ i ∈ Finset.Ico j k, β (i + 1) ≤ ρ ^ (k - i) * β (k + 1)) :
    ∑ i ∈ Finset.Ico j k, a i ≤ (∑ i ∈ Finset.Ico j k, U i * ρ ^ (k - i)) * β (k + 1) := by
  rw [sum_mul]
  refine sum_le_sum fun i hi => (ha i hi).trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hβ i hi) (hU i)

end
end PtCorr2
