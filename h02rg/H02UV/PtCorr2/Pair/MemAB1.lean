import PtCorr2.Obs.ProdBdHist
import Obs2.Pair.ShareAB1

/-!
# The memory terms of the reduced `r'` flow: `memAB`, `memABX`

`Obs2.memAB P C V W i k` (and its region copy `Obs2.memABX`) is
`𝔡₂_i·tadInc₂(i,k) + Δ_{ik}(dTau) − Δ_{ik}(pdefLS) + Δ_{ik}(wProd)`, where each `Δ_{ik}` is the
difference of a tadpole functional at `Γ = C_k + S_{i,k}` and at `Γ = S_{i,k}`
(`S_{i,k} = ∑_{i<l<k}C_l`). Each such difference is of the form of the localised Lipschitz bound
`Obs2.pauli_lip_loc` (Pauli invariance of `m₂`), exactly as in `PtCorr2.Obs.ProdBdHist`:

* **`delta_histY_le2`**: the `m₂` increment for any `F ∈ 𝒩(Y)`, `Y` in the box of radius
  `10L^{i+1}` around `a`: `≤ 1280K²(8/(7L))^{k−i}‖F‖_{T_{i+1}(s_{i+1})}/s_{i+1}²` (copy of
  `delta_hist_le_gen` with the locality given by a set `Y` instead of a block neighbourhood);
* **`norm_memAB_le`** / **`norm_memABX_le`**: one memory term, from the sizes at scale `i`
  (`|𝔡₂_i| ≤ p`, `|tadInc₂(i,k)| ≤ τ`, the `T_{i+1}(s_{i+1})` sizes `f`, `λ`, `w` of
  `F_C(D_i, V'_∅)`, of `Loc S_i(B)_{ab}` and of the product part of `𝒲'`, with their localities);
  by anchoring only the blocks of `a` and `b` contribute (factor `2`);
* **`memAB_hist_le`** / **`memABX_hist_le`**: the summed bound
  `∑_{j≤i<k}|memAB i k| ≤ ∑_{j≤i<k}(p_iτ_{ik} + 1280K²(8/(7L))^{k−i}(f_i + 2λ_i + 2w_i)/s_{i+1}²)`
  with all per-scale sizes as real sequences (the form fed to the joint induction).
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
/-- **The `m₂` Lipschitz increment for a set-localised `F`** (copy of `delta_hist_le_gen`, `m = m₂`):
for `k < j < n`, `F ∈ 𝒩(Y)` with `Y` in the box of radius `10L^{k+1}` around `x₀` and
`‖F‖_{T_{k+1}(s_{k+1})} ≤ B`:
`|m₂(e^{ℒ_{C_j + S_{k,j}}}F) − m₂(e^{ℒ_{S_{k,j}}}F)| ≤ 1280K²(8/(7L))^{j−k}B/s_{k+1}²`. -/
theorem delta_histY_le2 (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8) {n : ℕ} (hnN : n < N)
    (hVn : ∀ i < n, ValidAt R i) (hVL : ValidAtL R n) (t : Flow2.Hist.Seq (Xs R))
    (x₀ : Lam 2 L N) {k j : ℕ} (hkj : k < j) (hjn : j < n) (hL : prodLb ≤ L)
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
  have hrep₁ := (histCovO_props_i R hVn hVL t (i := j) hjn.le).1.gram
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

/-- The kernel of `delta_histY_le2`: `1280K²(8/(7L))^{k−i}/s_{i+1}²`. -/
def memKer (t : Flow2.Hist.Seq (Xs R)) (i k : ℕ) : ℝ :=
  1280 * locK 2 ^ 2 * (8 / (7 * L) : ℝ) ^ (k - i) / histS R (i + 1) t ^ 2

theorem memKer_nonneg (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8) (t : Flow2.Hist.Seq (Xs R)) (i k : ℕ) :
    0 ≤ memKer R t i k := by
  unfold memKer
  have := histS_pos' R hρ0 hρ t (i + 1)
  positivity

/-- A set-localised element of size `B` at scale `i + 1`, near `a`. -/
def LocSz (t : Flow2.Hist.Seq (Xs R)) (x₀ : Lam 2 L N) (i : ℕ) (F : Alg 2 L N) (B : ℝ) : Prop :=
  ∃ Y : Set (Lam 2 L N), (∀ y ∈ Y, (supNorm (y - x₀) : ℝ) ≤ 10 * (L : ℝ) ^ (i + 1)) ∧
    F ∈ NX Y ∧ Tj 2 (L : ℝ) (i + 1) (histS R (i + 1) t) F ≤ ENNReal.ofReal B

/-- `delta_histY_le2` with `LocSz`. -/
theorem delta_locSz_le (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8) {n : ℕ} (hnN : n < N)
    (hVn : ∀ i < n, ValidAt R i) (hVL : ValidAtL R n) (t : Flow2.Hist.Seq (Xs R))
    (x₀ : Lam 2 L N) {i k : ℕ} (hik : i < k) (hkn : k < n) (hL : prodLb ≤ L)
    {F : Alg 2 L N} {B : ℝ} (hB0 : 0 ≤ B) (hF : LocSz R t x₀ i F B) :
    ‖mass2 (expLC (histCovO R t k + cumBetween (histCovO R t) i k) F) -
        mass2 (expLC (cumBetween (histCovO R t) i k) F)‖ ≤ memKer R t i k * B := by
  obtain ⟨Y, hY, hFY, hFB⟩ := hF
  refine (delta_histY_le2 R hρ0 hρ hnN hVn hVL t x₀ hik hkn hL hY hFY hB0 hFB).trans
    (le_of_eq ?_)
  unfold memKer; ring

/-- The difference of a block-summed tadpole functional (only two blocks contribute). -/
theorem norm_sum_tad_diff_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (G : ι → Alg 2 L N)
    (Γ₁ Γ₀ : Matrix (Lam 2 L N) (Lam 2 L N) ℂ) (x y : ι) {M : ℝ} (hM : 0 ≤ M)
    (hz : ∀ i ∈ s, i ≠ x → i ≠ y → G i = 0)
    (hb : ∀ i ∈ s, (i = x ∨ i = y) →
      ‖mass2 (expLC Γ₁ (G i)) - mass2 (expLC Γ₀ (G i))‖ ≤ M) :
    ‖∑ i ∈ s, (mass2 (expLC Γ₁ (G i)) - mass2 (G i)) -
        ∑ i ∈ s, (mass2 (expLC Γ₀ (G i)) - mass2 (G i))‖ ≤ 2 * M := by
  rw [← sum_sub_distrib]
  refine norm_sum_two_le _ _ x y hM (fun i hi h1 h2 => ?_) fun i hi => ?_
  · rw [hz i hi h1 h2]; simp
  · by_cases h : i = x ∨ i = y
    · refine le_trans (le_of_eq ?_) (hb i hi h)
      congr 1; ring
    · push_neg at h
      rw [hz i hi h.1 h.2]; simpa using hM

/-- The same for a sum of `m₂(e^{ℒ_Γ}·)` alone. -/
theorem norm_sum_tad_diff_le' {ι : Type*} [DecidableEq ι] (s : Finset ι) (G : ι → Alg 2 L N)
    (Γ₁ Γ₀ : Matrix (Lam 2 L N) (Lam 2 L N) ℂ) (x y : ι) {M : ℝ} (hM : 0 ≤ M)
    (hz : ∀ i ∈ s, i ≠ x → i ≠ y → G i = 0)
    (hb : ∀ i ∈ s, (i = x ∨ i = y) →
      ‖mass2 (expLC Γ₁ (G i)) - mass2 (expLC Γ₀ (G i))‖ ≤ M) :
    ‖∑ i ∈ s, mass2 (expLC Γ₁ (G i)) - ∑ i ∈ s, mass2 (expLC Γ₀ (G i))‖ ≤ 2 * M := by
  have := norm_sum_tad_diff_le s G Γ₁ Γ₀ x y hM hz hb
  rwa [sum_sub_distrib, sum_sub_distrib, sub_sub_sub_cancel_right] at this

/-! ### One memory term -/

/-- The per-scale inputs of a memory term at scale `i`: the localised sizes of
`F_C(D_i, V'_∅)` (`f`), of the `ab` parts of `Loc S_i(B)` for the blocks of `a` and `b` (`λ`), and
of the `ab` parts of the product part of `𝒲'` for the `(i+1)`-blocks of `a` and `b` (`w`). -/
structure MemSz (t : Flow2.Hist.Seq (Xs R)) (P : ObsPts 2 L N) (i : ℕ) (DF : Alg 2 L N)
    (V W : OFam .two 2 L N) (f lam w : ℝ) : Prop where
  hD : LocSz R t P.a i DF f
  hLS : ∀ b, (b = blk i P.a ∨ b = blk i P.b) →
    LocSz R t P.a i (LSO P i (histCovO R t i) V W b : SA .two (Lam 2 L N)).ab lam
  hPr : ∀ c', (c' = blk (i + 1) P.a ∨ c' = blk (i + 1) P.b) →
    LocSz R t P.a i ((Wnext2O P i (histCovO R t i) V W c' -
      ∑ b ∈ blocks i (blockSet (L := L) (N := N) (i + 1) c'),
        WpO P i (histCovO R t i) V W b : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).ab w

theorem prodPart_ab_zero {P : ObsPts 2 L N} {i : ℕ} {C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ}
    {V W : OFam .two 2 L N} {K : OAct .two 2 L N} (H : OAnchS P i V W K) {c' : Fin 2 → ℕ}
    (h1 : c' ≠ blk (i + 1) P.a) (h2 : c' ≠ blk (i + 1) P.b) :
    ((Wnext2O P i C V W c' - ∑ b ∈ blocks i (blockSet (L := L) (N := N) (i + 1) c'),
      WpO P i C V W b : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).ab = 0 := by
  have hm : (Wnext2O P i C V W c' - ∑ b ∈ blocks i (blockSet (L := L) (N := N) (i + 1) c'),
      WpO P i C V W b : OE .two (Lam 2 L N)) ∈
      (anc P (blockSet (L := L) (N := N) (i + 1) c') : Subalgebra ℂ (OE .two (Lam 2 L N))) :=
    sub_mem (H.Wnext_anch (C := C) c') (Subalgebra.sum_mem _ fun b hb => anc_mono
      (blockSet_subset (IsPolymer.of_succ (isPolymer_blockSet (i + 1) c')) hb)
      (H.Wp_anch (C := C) b))
  exact ab_eq_zero_of_anch P hm h1 h2

theorem LSO_ab_zero {P : ObsPts 2 L N} {i : ℕ} {C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ}
    {V W : OFam .two 2 L N} {K : OAct .two 2 L N} (H : OAnchS P i V W K) {b : Fin 2 → ℕ}
    (h1 : b ≠ blk i P.a) (h2 : b ≠ blk i P.b) :
    (LSO P i C V W b : SA .two (Lam 2 L N)).ab = 0 :=
  ab_eq_zero_of_anch P (H.LS_anch (C := C) b) h1 h2

/-- The three tadpole differences of a memory term, for any block sets `sL ⊆` (scale `i`) and
`sP` (scale `i + 1`) and gradient element `DF`. -/
theorem norm_memCore_le (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8) {n : ℕ} (hnN : n < N)
    (hVn : ∀ i < n, ValidAt R i) (hVL : ValidAtL R n) (t : Flow2.Hist.Seq (Xs R))
    (P : ObsPts 2 L N) {i k : ℕ} (hik : i < k) (hkn : k < n) (hL : prodLb ≤ L)
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
    exact delta_locSz_le R hρ0 hρ hnN hVn hVL t P.a hik hkn hL hf hS.hD
  have h2 := norm_sum_tad_diff_le sL
    (fun b => (LSO P i (histCovO R t i) V W b : SA .two (Lam 2 L N)).ab) Γ₁ Γ₀
    (blk i P.a) (blk i P.b) (mul_nonneg hK hl)
    (fun b _ h1 h2 => LSO_ab_zero H h1 h2)
    (fun b _ hb => delta_locSz_le R hρ0 hρ hnN hVn hVL t P.a hik hkn hL hl (hS.hLS b hb))
  have h3 := norm_sum_tad_diff_le' sP
    (fun c' => ((Wnext2O P i (histCovO R t i) V W c' -
      ∑ b ∈ blocks i (blockSet (L := L) (N := N) (i + 1) c'),
        WpO P i (histCovO R t i) V W b : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).ab) Γ₁ Γ₀
    (blk (i + 1) P.a) (blk (i + 1) P.b) (mul_nonneg hK hw)
    (fun c' _ h1 h2 => prodPart_ab_zero H h1 h2)
    (fun c' _ hc => delta_locSz_le R hρ0 hρ hnN hVn hVL t P.a hik hkn hL hw (hS.hPr c' hc))
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add ((norm_sub_le _ _).trans (add_le_add h1 h2)) h3).trans (le_of_eq ?_)
  ring

/-- **One memory term** `memAB i k` (`i < k < n`). -/
theorem norm_memAB_le (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8) {n : ℕ} (hnN : n < N)
    (hVn : ∀ i < n, ValidAt R i) (hVL : ValidAtL R n) (t : Flow2.Hist.Seq (Xs R))
    (P : ObsPts 2 L N) {i k : ℕ} (hik : i < k) (hkn : k < n) (hL : prodLb ≤ L)
    (V W : ℕ → OFam .two 2 L N) {K : OAct .two 2 L N} (H : OAnchS P i (V i) (W i) K)
    {p τ f lam w : ℝ} (hf : 0 ≤ f) (hl : 0 ≤ lam) (hw : 0 ≤ w)
    (hp : ‖pdefM2 i (histCovO R t i) (V i)‖ ≤ p)
    (hτ : ‖tadInc2 P (histCovO R t) V i k‖ ≤ τ)
    (hS : MemSz R t P i (FC (histCovO R t i) (dAB P i (histCovO R t i) (V i))
      (VprLO i (histCovO R t i) (V i) : SA .two (Lam 2 L N)).e) (V i) (W i) f lam w) :
    ‖memAB P (histCovO R t) V W i k‖ ≤ p * τ + memKer R t i k * (f + 2 * lam + 2 * w) := by
  have hc := norm_memCore_le R hρ0 hρ hnN hVn hVL t P hik hkn hL H
    (blockIdx (L := L) (N := N) i) (blockIdx (L := L) (N := N) (i + 1)) hf hl hw hS
  simp only at hc
  have hpt : ‖pdefM2 i (histCovO R t i) (V i) * tadInc2 P (histCovO R t) V i k‖ ≤ p * τ := by
    rw [norm_mul]
    exact mul_le_mul hp hτ (norm_nonneg _) ((norm_nonneg _).trans hp)
  refine le_trans (le_of_eq ?_) ((norm_add_le _ _).trans (add_le_add hpt hc))
  unfold memAB dTauAB pdefLS wProdAB
  congr 1; ring

/-- **One memory term of a region** `memABX i k` (`i < k < n`). -/
theorem norm_memABX_le (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8) {n : ℕ} (hnN : n < N)
    (hVn : ∀ i < n, ValidAt R i) (hVL : ValidAtL R n) (t : Flow2.Hist.Seq (Xs R))
    (P : ObsPts 2 L N) {i k : ℕ} (hik : i < k) (hkn : k < n) (hL : prodLb ≤ L)
    (V W : ℕ → OFam .two 2 L N) {K : OAct .two 2 L N} (H : OAnchS P i (V i) (W i) K)
    (X : Finset (Lam 2 L N)) {p τ f lam w : ℝ} (hf : 0 ≤ f) (hl : 0 ≤ lam) (hw : 0 ≤ w)
    (hp : ‖pdefM2X i (histCovO R t i) (V i) X‖ ≤ p)
    (hτ : ‖tadInc2 P (histCovO R t) V i k‖ ≤ τ)
    (hS : MemSz R t P i (FC (histCovO R t i) (dABX P i (histCovO R t i) (V i) X)
      (VprLO i (histCovO R t i) (V i) : SA .two (Lam 2 L N)).e) (V i) (W i) f lam w) :
    ‖memABX P (histCovO R t) V W X i k‖ ≤ p * τ + memKer R t i k * (f + 2 * lam + 2 * w) := by
  have hc := norm_memCore_le R hρ0 hρ hnN hVn hVL t P hik hkn hL H
    (blocks i X) (blocks (i + 1) X) hf hl hw hS
  simp only at hc
  have hpt : ‖pdefM2X i (histCovO R t i) (V i) X * tadInc2 P (histCovO R t) V i k‖ ≤ p * τ := by
    rw [norm_mul]
    exact mul_le_mul hp hτ (norm_nonneg _) ((norm_nonneg _).trans hp)
  refine le_trans (le_of_eq ?_) ((norm_add_le _ _).trans (add_le_add hpt hc))
  unfold memABX dTauABX pdefLSX wProdABX
  congr 1; ring

/-! ### The summed bounds -/

/-- **The memory sum along a history**: for `j ≤ k < n`,
`∑_{j≤i<k}|memAB i k| ≤ ∑_{j≤i<k}(p_iτ_{ik} + ker_{ik}(f_i + 2λ_i + 2w_i))`. -/
theorem memAB_hist_le (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8) {n : ℕ} (hnN : n < N)
    (hVn : ∀ i < n, ValidAt R i) (hVL : ValidAtL R n) (t : Flow2.Hist.Seq (Xs R))
    (P : ObsPts 2 L N) (hL : prodLb ≤ L) (V W : ℕ → OFam .two 2 L N) (K : ℕ → OAct .two 2 L N)
    {j k : ℕ} (hkn : k < n) (H : ∀ i, j ≤ i → i < k → OAnchS P i (V i) (W i) (K i))
    (p f lam w : ℕ → ℝ) (τ : ℕ → ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) (hl : ∀ i, 0 ≤ lam i)
    (hw : ∀ i, 0 ≤ w i)
    (hp : ∀ i, j ≤ i → i < k → ‖pdefM2 i (histCovO R t i) (V i)‖ ≤ p i)
    (hτ : ∀ i, j ≤ i → i < k → ‖tadInc2 P (histCovO R t) V i k‖ ≤ τ i k)
    (hS : ∀ i, j ≤ i → i < k → MemSz R t P i (FC (histCovO R t i)
      (dAB P i (histCovO R t i) (V i)) (VprLO i (histCovO R t i) (V i) : SA .two (Lam 2 L N)).e)
      (V i) (W i) (f i) (lam i) (w i)) :
    ∑ i ∈ Ico j k, ‖memAB P (histCovO R t) V W i k‖ ≤
      ∑ i ∈ Ico j k, (p i * τ i k + memKer R t i k * (f i + 2 * lam i + 2 * w i)) :=
  sum_le_sum fun i hi => by
    obtain ⟨h1, h2⟩ := mem_Ico.1 hi
    exact norm_memAB_le R hρ0 hρ hnN hVn hVL t P h2 hkn hL V W (H i h1 h2) (hf i) (hl i) (hw i)
      (hp i h1 h2) (hτ i h1 h2) (hS i h1 h2)

/-- **The memory sum of a region along a history.** -/
theorem memABX_hist_le (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8) {n : ℕ} (hnN : n < N)
    (hVn : ∀ i < n, ValidAt R i) (hVL : ValidAtL R n) (t : Flow2.Hist.Seq (Xs R))
    (P : ObsPts 2 L N) (hL : prodLb ≤ L) (V W : ℕ → OFam .two 2 L N) (K : ℕ → OAct .two 2 L N)
    (X : Finset (Lam 2 L N))
    {j k : ℕ} (hkn : k < n) (H : ∀ i, j ≤ i → i < k → OAnchS P i (V i) (W i) (K i))
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
    exact norm_memABX_le R hρ0 hρ hnN hVn hVL t P h2 hkn hL V W (H i h1 h2) X (hf i) (hl i)
      (hw i) (hp i h1 h2) (hτ i h1 h2) (hS i h1 h2)

end Hist

end

end PtCorr2
