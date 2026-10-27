import PtCorr2.Obs.ProdStep
import PtCorr2.Obs.ObsHistRelW
import Obs2.Loc.PauliLip

/-!
# The `ℓ¹` product bound `ProdBd` along the history (Case (1))

The product parts `G_j(B_+; 0)` and `prodInc_j(B_+)` of the per-block `μ^{(1)}` flow:

* `G_j(B_+; 0) = P_j(B_+; 0)` (`MuChain.wTadX_succ` at `Γ = 0`) is bounded by the observable
  norm of the product part of step `j − 1` (`prod_hist_step`, `|m₁(F)| ≤ s^{-1}‖F‖_{T(s)}`);
* every increment `P_{k+1}(B_+; C_j + S_{k,j}) − P_{k+1}(B_+; S_{k,j})` is bounded by the localised
  Lipschitz bound `Obs2.pauli_lip_loc` (Pauli invariance of `m₁` + locality of `e^{ℒ_Γ}` +
  the gradient bound of `C_i` in the box of radius `R = 10L^{k+1}` around `a`): the constant part
  `C_j(a,a)` of `C_j` does not contribute, the rest is `O(ℓ_j² L^{-(j-k)})`, i.e. with the weights
  of the field scales `O((8/(7L))^{j−k})` relative to `s_{k+1}`;
* only the `O(1)` blocks `B` with `a ∈ 𝒩_{k+1}(B)` carry an `a`-component.

**`prodBd_hist`**: `ProdBd R P o₀ t n r c_P (2/L)` with `c_P = c_bn C_P(L) ((15/14) L + 686 K²)`
(`K = locK 2`, `c_bn` the block count of `card_blocks_near`) for `L ≥ 1000 K² + 10`, under the
hypotheses of `obs_hist_rel_w` and `c_R ε ≤ ε_P(L)`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

variable {L N : ℕ} [NeZero L]

/-- The number of blocks whose neighbourhood contains a given point (`card_blocks_near 2`). -/
def cbnC : ℕ := Classical.choose (card_blocks_near 2)

theorem card_filter_near_le {j : ℕ} (a : Lam 2 L N) :
    ((blockIdx (L := L) (N := N) j).filter
      (fun b => a ∈ nbhd j (blockSet (L := L) (N := N) j b))).card ≤ cbnC :=
  Classical.choose_spec (card_blocks_near 2) L N j a _ subset_rfl

/-- `∑_{k<i<j} x^{i−k} ≤ 2x` for `0 ≤ x ≤ 1/2`. -/
theorem geom_Ioo_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (k j : ℕ) :
    ∑ i ∈ Ioo k j, x ^ (i - k) ≤ 2 * x := by
  rw [← Finset.Ico_add_one_left_eq_Ioo, sum_Ico_eq_sum_range]
  have e : ∀ m ∈ range (j - (k + 1)), x ^ (k + 1 + m - k) = x * x ^ m := fun m _ => by
    rw [show k + 1 + m - k = m + 1 by omega, pow_succ, mul_comm]
  rw [sum_congr rfl e, ← mul_sum]
  have h1 : ∑ m ∈ range (j - (k + 1)), x ^ m ≤ 1 / (1 - x) := by
    have := geom_sum_Ico_le_of_lt_one (m := 0) (n := j - (k + 1)) hx0 (by linarith)
    rwa [pow_zero, ← range_eq_Ico] at this
  have h2 : 1 / (1 - x) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  exact (mul_le_mul_of_nonneg_left (h1.trans h2) hx0).trans_eq (mul_comm _ _)

/-- The lower bound on `L` of `prodBd_hist`. -/
def prodLb : ℝ := 1000 * locK 2 ^ 2 + 10

/-- The constant `c_P` of `prodBd_hist`. -/
def prodCP (L : ℕ) (Cp : ℝ) : ℝ := cbnC * Cp * (15 / 14 * L + 686 * locK 2 ^ 2)

section Hist

variable {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

/-- The Gram constant `ℓ_i` of `C_i` and the field scale: `ℓ_i²/s_{k+1}² ≤ (8/7)^{i−k}/16`. -/
theorem ell_sq_le_histS (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8) (t : Flow2.Hist.Seq (Xs R))
    {k i : ℕ} (hki : k ≤ i) :
    (fscale (stZ' R (rawHist R i t)) * R.ℓ / 4) ^ 2 ≤
      (8 / 7 : ℝ) ^ (i - k) / 16 * histS R (k + 1) t ^ 2 := by
  rw [ellI_sq]
  have hs : histS R (k + 1) t ^ 2 = R.ℓ ^ 2 / zH R t (k + 1) := by
    unfold histS; rw [mul_pow, fscale_sq, div_eq_mul_inv, mul_comm]
  rw [hs]
  have h1 := zH_ratio_down R hρ0 hρ t (l := k + 1) (m := i + 1) (by omega)
  have hz1 := zH_pos R hρ0 hρ t (k + 1)
  have hz2 := zH_pos R hρ0 hρ t (i + 1)
  rw [show i + 1 - (k + 1) = i - k by omega] at h1
  have hℓ : 0 ≤ R.ℓ ^ 2 := sq_nonneg _
  rw [div_le_iff₀ (by positivity)]
  calc R.ℓ ^ 2 = R.ℓ ^ 2 / zH R t (k + 1) * zH R t (k + 1) := by field_simp
    _ ≤ R.ℓ ^ 2 / zH R t (k + 1) * ((8 / 7 : ℝ) ^ (i - k) * zH R t (i + 1)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by ring


theorem histS_pos' (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8) (t : Flow2.Hist.Seq (Xs R)) (i : ℕ) :
    0 < histS R i t := by
  have hz := zH_pos R hρ0 hρ t i
  exact mul_pos (fscale_pos (norm_pos_iff.1 hz)) (Fact.out)

theorem ellI_pos (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8) (t : Flow2.Hist.Seq (Xs R)) (i : ℕ) :
    0 < fscale (stZ' R (rawHist R i t)) * R.ℓ / 4 := by
  have hz := zH_pos R hρ0 hρ t (i + 1)
  have e : stZ' R (rawHist R i t) = (rawHist R (i + 1) t).Z := rfl
  rw [e]
  exact div_pos (mul_pos (fscale_pos (norm_pos_iff.1 hz)) Fact.out) (by norm_num)

/-- The localised squared Gram constant of `C_i` relative to `s_{k+1}`. -/
theorem locC_hist_le (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8) (t : Flow2.Hist.Seq (Xs R))
    {k i : ℕ} (hki : k < i) :
    locC 2 (10 * (L : ℝ) ^ (k + 1)) (fscale (stZ' R (rawHist R i t)) * R.ℓ / 4)
        ((L : ℝ) ^ (i + 1)) ≤
      20 * locK 2 ^ 2 * (8 / (7 * L) : ℝ) ^ (i - k) * histS R (k + 1) t ^ 2 := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have h1 := ell_sq_le_histS R hρ0 hρ t hki.le
  have e : (L : ℝ) ^ (i + 1) = (L : ℝ) ^ (k + 1) * (L : ℝ) ^ (i - k) := by
    rw [← pow_add]; congr 1; omega
  have hK := one_le_locK 2
  unfold locC
  rw [e]
  have hp : (0 : ℝ) < (L : ℝ) ^ (k + 1) := by positivity
  have hq : (0 : ℝ) < (L : ℝ) ^ (i - k) := by positivity
  have e2 : (8 / (7 * L) : ℝ) ^ (i - k) = (8 / 7 : ℝ) ^ (i - k) / (L : ℝ) ^ (i - k) := by
    rw [div_mul_eq_div_div, div_pow]
  rw [e2]
  have : 16 * ((2 : ℕ) : ℝ) * locK 2 ^ 2 * (10 * (L : ℝ) ^ (k + 1)) *
      (fscale (stZ' R (rawHist R i t)) * R.ℓ / 4) ^ 2 / ((L : ℝ) ^ (k + 1) * (L : ℝ) ^ (i - k)) =
      320 * locK 2 ^ 2 * (fscale (stZ' R (rawHist R i t)) * R.ℓ / 4) ^ 2 / (L : ℝ) ^ (i - k) := by
    field_simp; push_cast; ring
  rw [this]
  have h2 : 320 * locK 2 ^ 2 * (fscale (stZ' R (rawHist R i t)) * R.ℓ / 4) ^ 2 ≤
      320 * locK 2 ^ 2 * ((8 / 7 : ℝ) ^ (i - k) / 16 * histS R (k + 1) t ^ 2) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  calc 320 * locK 2 ^ 2 * (fscale (stZ' R (rawHist R i t)) * R.ℓ / 4) ^ 2 / (L : ℝ) ^ (i - k)
      ≤ 320 * locK 2 ^ 2 * ((8 / 7 : ℝ) ^ (i - k) / 16 * histS R (k + 1) t ^ 2) /
          (L : ℝ) ^ (i - k) := div_le_div_of_nonneg_right h2 hq.le
    _ = _ := by field_simp; ring

/-- **The Lipschitz increment of one product part, generic functional.** For any `m` with the
Pauli invariance (`m₁^{(±)}`, `m₂`) and `|m(G)| ≤ M ‖G‖_{T_{k+1}(s_{k+1}/4)}`, `k < j < n`, a
`(k+1)`-block `B` with `a ∈ 𝒩_{k+1}(B)` and `F ∈ 𝒩(𝒩_{k+1}(B))`, `‖F‖_{T_{k+1}(s_{k+1})} ≤ B`:
`|m(e^{ℒ_{C_j + S_{k,j}}}F) − m(e^{ℒ_{S_{k,j}}}F)| ≤ 80 M K² (8/(7L))^{j−k} B`. -/
theorem delta_hist_le_gen (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8) {n : ℕ} (hnN : n < N)
    (hVn : ∀ i < n, ValidAt R i) (hVL : ValidAtL R n) (t : Flow2.Hist.Seq (Xs R))
    (P : ObsPts 2 L N) {m : Alg 2 L N →ₗ[ℂ] ℂ} (hmP : PauliInv m) {M : ℝ} (hM : 0 ≤ M)
    {k j : ℕ} (hkj : k < j) (hjn : j < n) (hL : prodLb ≤ L)
    (hmb : ∀ G : Alg 2 L N, ‖m G‖ ≤ M * (Tj 2 (L : ℝ) (k + 1) (histS R (k + 1) t / 4) G).toReal)
    {c'' : Fin 2 → ℕ} (hc'' : c'' ∈ blockIdx (L := L) (N := N) (k + 1)) {F : Alg 2 L N}
    (hF : F ∈ NX (nbhd (k + 1) (blockSet (L := L) (N := N) (k + 1) c'') : Set (Lam 2 L N)))
    (ha : P.a ∈ nbhd (k + 1) (blockSet (L := L) (N := N) (k + 1) c''))
    {B : ℝ} (hB0 : 0 ≤ B) (hFB : Tj 2 (L : ℝ) (k + 1) (histS R (k + 1) t) F ≤ ENNReal.ofReal B) :
    ‖m (expLC (histCovO R t j + cumBetween (histCovO R t) k j) F) -
        m (expLC (cumBetween (histCovO R t) k j) F)‖ ≤
      M * (80 * locK 2 ^ 2 * (8 / (7 * L) : ℝ) ^ (j - k)) * B := by
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
  -- the hypotheses of `pauli_lip_loc`
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
  have hY : ∀ y ∈ (nbhd (k + 1) (blockSet (L := L) (N := N) (k + 1) c'') : Set (Lam 2 L N)),
      (supNorm (y - P.a) : ℝ) ≤ R₀ := by
    intro y hy
    obtain ⟨z, hz⟩ := mem_blockIdx.1 hc''
    have h1 := supNorm_le_of_mem_nbhd_blockSet (L := L) (N := N) hy hz
    have h2 := supNorm_le_of_mem_nbhd_blockSet (L := L) (N := N) ha hz
    have h3 := supNorm_add_le (y - z) (z - P.a)
    rw [sub_add_sub_cancel, supNorm_sub_comm z] at h3
    have h4 : supNorm (y - P.a) ≤ 10 * L ^ (k + 1) := by norm_num at h1 h2; omega
    rw [hR₀]; exact_mod_cast h4
  have hrep : ∀ i ∈ Ioo k j, ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (Fv Gv : Lam 2 L N → H), IsGram (histCovO R t i) Fv Gv ∧
        GramBound (Dir 2) (pPhi 2) ((L : ℝ) ^ (i + 1))
          (fscale (stZ' R (rawHist R i t)) * R.ℓ / 4) Fv Gv := fun i hi =>
    (histCovO_props_i R hVn hVL t (i := i) (by have := (mem_Ioo.1 hi).2; omega)).1.gram
  have hrep₁ := (histCovO_props_i R hVn hVL t (i := j) hjn.le).1.gram
  have hRs : ∀ i ∈ Ioo k j, R₀ ≤ (L : ℝ) ^ (i + 1) := by
    intro i hi
    have hi' := (mem_Ioo.1 hi).1
    calc R₀ ≤ (L : ℝ) * (L : ℝ) ^ (k + 1) := by rw [hR₀]; exact mul_le_mul_of_nonneg_right hL10 (by positivity)
      _ = (L : ℝ) ^ (k + 2) := by ring
      _ ≤ (L : ℝ) ^ (i + 1) := pow_le_pow_right₀ (by linarith) (by omega)
  have hR₁ : R₀ ≤ (L : ℝ) ^ (j + 1) := by
    calc R₀ ≤ (L : ℝ) * (L : ℝ) ^ (k + 1) := by rw [hR₀]; exact mul_le_mul_of_nonneg_right hL10 (by positivity)
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
  have key := pauli_lip_loc (d := 2) one_le_two hmP (k := k + 1) hσ hM
    hmb hhR hR hN P.a hY hF (Ioo k j) (histCovO R t) (fun i => (L : ℝ) ^ (i + 1))
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
  exact mul_le_mul (mul_le_mul_of_nonneg_left hlc hM) hT hT0 (by positivity)


/-- **The Lipschitz increment of one product part** (`m₁`): for `k < j < n`, a `(k+1)`-block `B`
with `a ∈ 𝒩_{k+1}(B)` and `F ∈ 𝒩(𝒩_{k+1}(B))`, `‖F‖_{T_{k+1}(s_{k+1})} ≤ B`:
`|m₁(e^{ℒ_{C_j + S_{k,j}}}F) − m₁(e^{ℒ_{S_{k,j}}}F)| ≤ 320 K² (8/(7L))^{j−k} B / s_{k+1}`. -/
theorem delta_hist_le (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8) {n : ℕ} (hnN : n < N)
    (hVn : ∀ i < n, ValidAt R i) (hVL : ValidAtL R n) (t : Flow2.Hist.Seq (Xs R))
    (P : ObsPts 2 L N) {k j : ℕ} (hkj : k < j) (hjn : j < n) (hL : prodLb ≤ L)
    {c'' : Fin 2 → ℕ} (hc'' : c'' ∈ blockIdx (L := L) (N := N) (k + 1)) {F : Alg 2 L N}
    (hF : F ∈ NX (nbhd (k + 1) (blockSet (L := L) (N := N) (k + 1) c'') : Set (Lam 2 L N)))
    (ha : P.a ∈ nbhd (k + 1) (blockSet (L := L) (N := N) (k + 1) c''))
    {B : ℝ} (hB0 : 0 ≤ B) (hFB : Tj 2 (L : ℝ) (k + 1) (histS R (k + 1) t) F ≤ ENNReal.ofReal B) :
    ‖mass1L (-1) (expLC (histCovO R t j + cumBetween (histCovO R t) k j) F) -
        mass1L (-1) (expLC (cumBetween (histCovO R t) k j) F)‖ ≤
      320 * locK 2 ^ 2 * (8 / (7 * L) : ℝ) ^ (j - k) * B / histS R (k + 1) t := by
  have hs := histS_pos' R hρ0 hρ t (k + 1)
  have hσ : 0 < histS R (k + 1) t / 4 := by positivity
  refine (delta_hist_le_gen R hρ0 hρ hnN hVn hVL t P pauliInv_mass1
    (M := (histS R (k + 1) t / 4)⁻¹) (by positivity) hkj hjn hL
    (fun G => (norm_mass1_le hσ (k + 1) (-1) G).trans_eq (mul_comm _ _)) hc'' hF ha hB0 hFB).trans
    (le_of_eq ?_)
  field_simp; ring

/-- **The Case (2) analogue** (`m₂ = ε ∘ D D̄`, also Pauli invariant, `mass2_expLC_add_J`):
`|m₂(e^{ℒ_{C_j + S_{k,j}}}F) − m₂(e^{ℒ_{S_{k,j}}}F)| ≤ 1280 K² (8/(7L))^{j−k} B / s_{k+1}²`. -/
theorem delta_hist_le2 (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8) {n : ℕ} (hnN : n < N)
    (hVn : ∀ i < n, ValidAt R i) (hVL : ValidAtL R n) (t : Flow2.Hist.Seq (Xs R))
    (P : ObsPts 2 L N) {k j : ℕ} (hkj : k < j) (hjn : j < n) (hL : prodLb ≤ L)
    {c'' : Fin 2 → ℕ} (hc'' : c'' ∈ blockIdx (L := L) (N := N) (k + 1)) {F : Alg 2 L N}
    (hF : F ∈ NX (nbhd (k + 1) (blockSet (L := L) (N := N) (k + 1) c'') : Set (Lam 2 L N)))
    (ha : P.a ∈ nbhd (k + 1) (blockSet (L := L) (N := N) (k + 1) c''))
    {B : ℝ} (hB0 : 0 ≤ B) (hFB : Tj 2 (L : ℝ) (k + 1) (histS R (k + 1) t) F ≤ ENNReal.ofReal B) :
    ‖mass2L (expLC (histCovO R t j + cumBetween (histCovO R t) k j) F) -
        mass2L (expLC (cumBetween (histCovO R t) k j) F)‖ ≤
      1280 * locK 2 ^ 2 * (8 / (7 * L) : ℝ) ^ (j - k) * B / histS R (k + 1) t ^ 2 := by
  have hs := histS_pos' R hρ0 hρ t (k + 1)
  have hσ : 0 < histS R (k + 1) t / 4 := by positivity
  refine (delta_hist_le_gen R hρ0 hρ hnN hVn hVL t P pauliInv_mass2
    (M := ((histS R (k + 1) t / 4)⁻¹) ^ 2) (by positivity) hkj hjn hL
    (fun G => (norm_mass2_le hσ (k + 1) G).trans_eq (mul_comm _ _)) hc'' hF ha hB0 hFB).trans
    (le_of_eq ?_)
  field_simp; ring

theorem wProdX_eq_prodO {c : Obs.Case} (P : ObsPts 2 L N) (k : ℕ)
    (C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ) (V W : OFam c 2 L N) (m : Alg 2 L N →ₗ[ℂ] ℂ)
    (X : Finset (Lam 2 L N)) (Γ : Matrix (Lam 2 L N) (Lam 2 L N) ℂ) :
    wProdX P k C V W m X Γ =
      ∑ c'' ∈ blocks (k + 1) X, m (expLC Γ (prodO P k C V W c'' : SA c (Lam 2 L N)).a) := rfl

/-- `∑_{b ∈ S} (if p b then v else 0) ≤ c_bn v` for the blocks near `a`. -/
theorem sum_ite_near_le {j : ℕ} (a : Lam 2 L N) {v : ℝ} (hv : 0 ≤ v) :
    ∑ b ∈ blockIdx (L := L) (N := N) j,
        (if a ∈ nbhd j (blockSet (L := L) (N := N) j b) then v else 0) ≤ cbnC * v := by
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_filter_near_le a) hv


/-- The final real inequality of `prodBd_hist`. -/
theorem prodBd_real {L : ℕ} (hL0 : (0 : ℝ) < L) {K cb Cp x : ℝ} (hcb : 0 ≤ cb) (hCp : 0 ≤ Cp)
    (hK : 0 ≤ K) (hx0 : 0 ≤ x) (hx : x ≤ 2 / L) (j : ℕ) (a s : ℕ → ℝ) (ha : ∀ k ≤ j, 0 ≤ a k)
    (hs : ∀ k, 0 < s k) (hss : ∀ k, (s (k + 1))⁻¹ ≤ 15 / 14 * (s k)⁻¹) :
    (if j = 0 then 0 else cb * (2 * Cp * a (j - 1)) / s j) +
        ∑ k ∈ range j, cb * (320 * K ^ 2 * x ^ (j - k) * (2 * Cp * a k) / s (k + 1)) ≤
      cb * Cp * (15 / 14 * L + 686 * K ^ 2) *
        ∑ i ∈ range (j + 1), (2 / L : ℝ) ^ (j - i) * (a i / s i) := by
  set q : ℝ := 2 / L with hq
  have hq0 : 0 ≤ q := by positivity
  have hX : ∀ k ≤ j, 0 ≤ a k / s k := fun k hk => div_nonneg (ha k hk) (hs k).le
  have h1 : ∑ k ∈ range j, cb * (320 * K ^ 2 * x ^ (j - k) * (2 * Cp * a k) / s (k + 1)) ≤
      ∑ k ∈ range j, cb * Cp * (686 * K ^ 2) * (q ^ (j - k) * (a k / s k)) := by
    refine sum_le_sum fun k hkr => ?_
    have hkj : k ≤ j := (mem_range.1 hkr).le
    have hxq : x ^ (j - k) ≤ q ^ (j - k) := pow_le_pow_left₀ hx0 hx _
    have hsk := hss k
    have e1 : cb * (320 * K ^ 2 * x ^ (j - k) * (2 * Cp * a k) / s (k + 1)) =
        (cb * Cp * K ^ 2 * a k) * (640 * x ^ (j - k)) * (s (k + 1))⁻¹ := by ring
    have e2 : cb * Cp * (686 * K ^ 2) * (q ^ (j - k) * (a k / s k)) =
        (cb * Cp * K ^ 2 * a k) * (686 * q ^ (j - k)) * (s k)⁻¹ := by ring
    rw [e1, e2]
    have hA : 0 ≤ cb * Cp * K ^ 2 * a k := by have := ha k hkj; positivity
    have hB : 0 ≤ 640 * x ^ (j - k) := by positivity
    calc (cb * Cp * K ^ 2 * a k) * (640 * x ^ (j - k)) * (s (k + 1))⁻¹
        ≤ (cb * Cp * K ^ 2 * a k) * (640 * x ^ (j - k)) * (15 / 14 * (s k)⁻¹) :=
          mul_le_mul_of_nonneg_left hsk (mul_nonneg hA hB)
      _ = (cb * Cp * K ^ 2 * a k) * (4800 / 7 * x ^ (j - k)) * (s k)⁻¹ := by ring
      _ ≤ (cb * Cp * K ^ 2 * a k) * (686 * q ^ (j - k)) * (s k)⁻¹ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hA)
            (inv_nonneg.2 (hs k).le)
          have : 0 ≤ q ^ (j - k) := pow_nonneg hq0 _
          nlinarith
  have h2 : (if j = 0 then 0 else cb * (2 * Cp * a (j - 1)) / s j) ≤
      ∑ k ∈ range j, cb * Cp * (15 / 14 * L) * (q ^ (j - k) * (a k / s k)) := by
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · rw [if_neg (by omega)]
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hmem : j' ∈ range (j' + 1) := mem_range.2 (by omega)
      refine le_trans ?_ (single_le_sum (f := fun k => cb * Cp * (15 / 14 * L) *
        (q ^ (j' + 1 - k) * (a k / s k))) (fun k hk => by
          have := hX k (mem_range.1 hk).le; have : 0 ≤ q ^ (j' + 1 - k) := pow_nonneg hq0 _
          positivity) hmem)
      simp only [show j' + 1 - 1 = j' by omega, show j' + 1 - j' = 1 by omega, pow_one]
      have hsj := hss j'
      have e1 : cb * Cp * (15 / 14 * L) * (q * (a j' / s j')) = cb * Cp * (15 / 7) * a j' * (s j')⁻¹ := by
        rw [hq]; field_simp; ring
      rw [e1]
      have e2 : cb * (2 * Cp * a j') / s (j' + 1) = cb * Cp * 2 * a j' * (s (j' + 1))⁻¹ := by ring
      rw [e2]
      have hA : 0 ≤ cb * Cp * 2 * a j' := by have := ha j' (by omega); positivity
      calc cb * Cp * 2 * a j' * (s (j' + 1))⁻¹ ≤ cb * Cp * 2 * a j' * (15 / 14 * (s j')⁻¹) :=
            mul_le_mul_of_nonneg_left hsj hA
        _ = _ := by ring
  have h3 : ∑ k ∈ range j, cb * Cp * (15 / 14 * L) * (q ^ (j - k) * (a k / s k)) +
      ∑ k ∈ range j, cb * Cp * (686 * K ^ 2) * (q ^ (j - k) * (a k / s k)) ≤
      cb * Cp * (15 / 14 * L + 686 * K ^ 2) * ∑ i ∈ range (j + 1), q ^ (j - i) * (a i / s i) := by
    rw [← sum_add_distrib, mul_sum]
    have e : ∀ k ∈ range j, cb * Cp * (15 / 14 * L) * (q ^ (j - k) * (a k / s k)) +
        cb * Cp * (686 * K ^ 2) * (q ^ (j - k) * (a k / s k)) =
        cb * Cp * (15 / 14 * L + 686 * K ^ 2) * (q ^ (j - k) * (a k / s k)) := fun k _ => by ring
    rw [sum_congr rfl e]
    refine sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega)) fun i hi _ => ?_
    have := hX i (Nat.lt_succ_iff.1 (mem_range.1 hi)); have : 0 ≤ q ^ (j - i) := pow_nonneg hq0 _
    have : 0 ≤ (L : ℝ) := hL0.le
    positivity
  linarith

set_option maxHeartbeats 2000000 in
/-- **`ProdBd` along the history** (ratio `2/L`, constant `prodCP L C_P`). -/
theorem prodBd_hist {Cp εp : ℝ} (hPB : PObsBounds L Cp εp) (hCp : 0 ≤ Cp)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1) (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8)
    (P : ObsPts 2 L N) (o₀ : ObsSt .one L N) (h0 : o₀.IsObs) (hl0 : ObsLocInv P 0 o₀)
    (hs0 : ObsSymInv 0 o₀) (hf0 : ∀ b, (o₀.V b : SA .one (Lam 2 L N)).a ∈ (ℂ ∙ psibar P.a))
    (hW0a : ∀ b, (o₀.W b : SA .one (Lam 2 L N)).a = 0)
    (t : Flow2.Hist.Seq (Xs R)) (n : ℕ) (hn : n ≤ Nh) (hnN : n < N) (hVL : ValidAtL R n)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε n t)
    (hεp : cR R Λ cm C₂ * ε ≤ εp) (hL : prodLb ≤ L) :
    ProdBd R P o₀ t n (fun j => cR R Λ cm C₂ * (t j).1) (prodCP L Cp) (2 / L) := by
  intro j hj mm hmm
  set rr : ℕ → ℝ := fun j => cR R Λ cm C₂ * (t j).1 with hrr
  set K := locK 2
  have hK := one_le_locK 2
  have hLK : 1000 * K ^ 2 + 10 ≤ (L : ℝ) := hL
  have hL10 : (10 : ℝ) ≤ L := by nlinarith [sq_nonneg K]
  have hL0 : (0 : ℝ) < L := by linarith
  have hVn : ∀ i < n, ValidAt R i := fun i hi => hV i (by omega)
  obtain ⟨r', HC⟩ := muChain_obsHist_kap R P o₀ t hnN hVn hVL h0 hW0a hf0
  have hDh : ∀ k ≤ n, Flow2.Hist.InDh Λ β δ κ cg cm cT ε k t := fun k hk =>
    ⟨fun i hi => ht.1 i (by omega), fun i hi => ht.2 i (by omega)⟩
  have hcR : 0 ≤ cR R Λ cm C₂ := by
    unfold cR cV cW cZ; have := H.hcmu; have := H.hC₂; positivity
  have hr0 : ∀ k ≤ n, 0 ≤ rr k := fun k hk => mul_nonneg hcR (ht.1 k hk).1.le
  have hs : ∀ i, 0 < histS R i t := histS_pos' R hρ0 hρ t
  have hform : ∀ k b, ((obsHist R P o₀ k t).V b : SA .one (Lam 2 L N)).a ∈ (ℂ ∙ psibar P.a) :=
    fun k b => by rw [← histVO_a]; exact obsHist_hform R P o₀ t hf0 k b
  have hm0 : ∀ k ≤ j, 0 ≤ mm k := fun k hk => (hmm k hk).1
  -- the block bound of `V^{obs}_k`
  have hVo : ∀ k ≤ j, ∀ b ∈ blockIdx (L := L) (N := N) k,
      oTo Obs2.wA k (histS R k t) ((obsHist R P o₀ k t).V b) ≤ ENNReal.ofReal (mm k) := by
    intro k hk b hb'
    have hsm := (hmm k hk).2.1
    rw [Obs2.oTo_wA, eq_mass1_smul_of_span (hform k b), Tj_smul_psibar k (hs k)]
    refine ENNReal.ofReal_le_ofReal (le_trans ?_ hsm)
    have h1 : ‖mass1 (-1) ((obsHist R P o₀ k t).V b : SA .one (Lam 2 L N)).a‖ ≤
        MuChain.shA (histVO R P o₀ t) k := by
      rw [← histVO_a_mass R P o₀ t k b]
      exact single_le_sum (f := fun b => ‖mass1 (-1)
        (histVO R P o₀ t k b : SA .one (Lam 2 L N)).a‖) (fun _ _ => norm_nonneg _) hb'
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left h1 (hs k).le
  -- the product parts of the steps `k < j`
  have hPk : ∀ k < j, ∀ c'' ∈ blockIdx (L := L) (N := N) (k + 1),
      Tj 2 (L : ℝ) (k + 1) (histS R (k + 1) t)
        ((prodO P k (histCovO R t k) (histVO R P o₀ t k) (histWO R P o₀ t k) c'' :
          SA .one (Lam 2 L N)).a) ≤ ENNReal.ofReal (2 * Cp * rr k ^ 2 * mm k) ∧
      prodO P k (histCovO R t k) (histVO R P o₀ t k) (histWO R P o₀ t k) c'' ∈
        osub P (nbhd (k + 1) (blockSet (L := L) (N := N) (k + 1) c'')) := by
    intro k hk c'' hc''
    have hkn : k < n := by omega
    have hrk := hr0 k hkn.le
    obtain ⟨h1, h2⟩ := prod_hist_step R hPB hSB hV hm hβ hδ1 H P Obs2.wA Obs2.wA_ab o₀ h0 hl0 hs0 t k
      (by omega) (hDh k hkn.le) hεp (mm k) (rr k * mm k) (hm0 k hk.le)
      (mul_nonneg hrk (hm0 k hk.le)) (hVo k hk.le) (hmm k hk.le).2.2 c'' hc''
    refine ⟨?_, h2⟩
    rw [← Obs2.oTo_wA]
    refine h1.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    simp only [hrr]; ring
  set x : ℝ := 8 / (7 * L) with hx
  have hx0 : 0 ≤ x := by positivity
  have hx2 : x ≤ 2 / L := by
    rw [hx, div_le_div_iff₀ (by positivity) hL0]; nlinarith
  have hss : ∀ k, (histS R (k + 1) t)⁻¹ ≤ 15 / 14 * (histS R k t)⁻¹ := by
    intro k
    have e : histS R (k + 1) t = histS R k t * fscale (1 + zetaH R k t) := by
      unfold histS; rw [rawHist_succ_Z, fscale_mul]; ring
    have hz : ‖zetaH R k t‖ ≤ 1 / 8 := (absorb_le R hρ0 _ _).trans hρ
    have h1 := fscale_one_add_ge hz
    have hf : 0 < fscale (1 + zetaH R k t) := by linarith
    have hfi : (fscale (1 + zetaH R k t))⁻¹ ≤ 15 / 14 := by
      rw [inv_le_iff_one_le_mul₀ hf]; nlinarith
    rw [e, mul_inv]
    calc (histS R k t)⁻¹ * (fscale (1 + zetaH R k t))⁻¹ ≤ (histS R k t)⁻¹ * (15 / 14) :=
          mul_le_mul_of_nonneg_left hfi (inv_nonneg.2 (hs k).le)
      _ = _ := by ring
  set gterm : (Fin 2 → ℕ) → ℝ := fun c'' => if j = 0 then 0 else
    if P.a ∈ nbhd j (blockSet (L := L) (N := N) j c'') then
      2 * Cp * rr (j - 1) ^ 2 * mm (j - 1) / histS R j t else 0 with hgterm
  set dterm : ℕ → (Fin 2 → ℕ) → ℝ := fun k c'' =>
    if P.a ∈ nbhd (k + 1) (blockSet (L := L) (N := N) (k + 1) c'') then
      320 * K ^ 2 * x ^ (j - k) * (2 * Cp * rr k ^ 2 * mm k) / histS R (k + 1) t else 0 with hdterm
  -- the term `G_j(B_+; 0)`
  have hG : ∀ c' ∈ blockIdx (L := L) (N := N) (j + 1),
      ‖wTadX j (mass1L (-1)) (histWO R P o₀ t j) (blockSet (L := L) (N := N) (j + 1) c') 0‖ ≤
        ∑ c'' ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'), gterm c'' := by
    intro c' hc'
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · have : wTadX 0 (mass1L (-1)) (histWO R P o₀ t 0) (blockSet (L := L) (N := N) (0 + 1) c') 0
          = 0 := by
        unfold wTadX
        refine sum_eq_zero fun b _ => ?_
        rw [HC.hW0 b, map_zero, map_zero]
      rw [this, norm_zero]
      exact sum_nonneg fun c'' _ => by simp [hgterm]
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hX : IsPolymer (j' + 1) (blockSet (L := L) (N := N) (j' + 1 + 1) c') :=
        IsPolymer.of_succ (isPolymer_blockSet _ c')
      rw [HC.wTadX_succ (by omega) hX 0, tauC_zero_right, mul_zero, mul_zero, zero_add, zero_add,
        sub_self, add_zero, wProdX_eq_prodO]
      refine (norm_sum_le _ _).trans (sum_le_sum fun c'' hc'' => ?_)
      rw [expLC_zero]
      have hc''I := mem_blockIdx_of_mem_blocks hc''
      obtain ⟨hT, hmem⟩ := hPk j' (by omega) c'' hc''I
      simp only [hgterm, if_neg (Nat.succ_ne_zero j'), Nat.add_sub_cancel]
      split_ifs with ha
      · show ‖mass1 (-1) _‖ ≤ _
        refine (norm_mass1_le (hs (j' + 1)) (j' + 1) (-1) _).trans ?_
        have hB : 0 ≤ 2 * Cp * rr j' ^ 2 * mm j' := by
          have := hm0 j' (by omega); positivity
        have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hT
        rw [ENNReal.toReal_ofReal hB] at this
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right this (inv_nonneg.2 (hs _).le)
      · rw [osub_a_zero hmem ha, map_zero, norm_zero]
  -- the increments
  have hD : ∀ c' ∈ blockIdx (L := L) (N := N) (j + 1),
      ‖muProdIncX P (histCovO R t) (histVO R P o₀ t) (histWO R P o₀ t) j
          (blockSet (L := L) (N := N) (j + 1) c')‖ ≤
        ∑ k ∈ range j, ∑ c'' ∈ blocks (k + 1) (blockSet (L := L) (N := N) (j + 1) c'),
          dterm k c'' := by
    intro c' hc'
    unfold muProdIncX
    refine (norm_sum_le _ _).trans (sum_le_sum fun k hk => ?_)
    rw [wProdX_eq_prodO, wProdX_eq_prodO, ← sum_sub_distrib]
    refine (norm_sum_le _ _).trans (sum_le_sum fun c'' hc'' => ?_)
    have hk' : k < j := mem_range.1 hk
    have hc''I := mem_blockIdx_of_mem_blocks hc''
    obtain ⟨hT, hmem⟩ := hPk k hk' c'' hc''I
    simp only [hdterm]
    split_ifs with ha
    · have hB : 0 ≤ 2 * Cp * rr k ^ 2 * mm k := by
        have := hm0 k hk'.le; have := hr0 k (by omega); positivity
      exact delta_hist_le R hρ0 hρ hnN hVn hVL t P hk' hj hL hc''I hmem.2.1 ha hB hT
    · rw [osub_a_zero hmem ha]; simp
  -- the sum over the `(j+1)`-blocks
  show ∑ c' ∈ blockIdx (L := L) (N := N) (j + 1),
      ‖wTadX j (mass1L (-1)) (histWO R P o₀ t j) (blockSet (L := L) (N := N) (j + 1) c') 0 +
        muProdIncX P (histCovO R t) (histVO R P o₀ t) (histWO R P o₀ t) j
          (blockSet (L := L) (N := N) (j + 1) c')‖ ≤ _
  have hS1 : ∑ c' ∈ blockIdx (L := L) (N := N) (j + 1),
      ‖wTadX j (mass1L (-1)) (histWO R P o₀ t j) (blockSet (L := L) (N := N) (j + 1) c') 0 +
        muProdIncX P (histCovO R t) (histVO R P o₀ t) (histWO R P o₀ t) j
          (blockSet (L := L) (N := N) (j + 1) c')‖ ≤
      ∑ c'' ∈ blockIdx (L := L) (N := N) j, gterm c'' +
        ∑ k ∈ range j, ∑ c'' ∈ blockIdx (L := L) (N := N) (k + 1), dterm k c'' := by
    refine (sum_le_sum fun c' hc' => (norm_add_le _ _).trans
      (add_le_add (hG c' hc') (hD c' hc'))).trans (le_of_eq ?_)
    rw [sum_add_distrib, sum_blockIdx_le gterm (by omega : j ≤ j + 1), sum_comm]
    congr 1
    exact sum_congr rfl fun k hk => sum_blockIdx_le (dterm k) (by have := mem_range.1 hk; omega)
  have hS2 : ∑ c'' ∈ blockIdx (L := L) (N := N) j, gterm c'' ≤
      (if j = 0 then 0 else cbnC * (2 * Cp * (rr (j - 1) ^ 2 * mm (j - 1))) / histS R j t) := by
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp [hgterm]
    · simp only [hgterm, if_neg (by omega : j ≠ 0)]
      have hv : 0 ≤ 2 * Cp * rr (j - 1) ^ 2 * mm (j - 1) / histS R j t := by
        have := hm0 (j - 1) (by omega); have := hs j; positivity
      refine (sum_ite_near_le P.a hv).trans (le_of_eq ?_)
      ring
  have hS3 : ∑ k ∈ range j, ∑ c'' ∈ blockIdx (L := L) (N := N) (k + 1), dterm k c'' ≤
      ∑ k ∈ range j, cbnC * (320 * K ^ 2 * x ^ (j - k) * (2 * Cp * (rr k ^ 2 * mm k)) /
        histS R (k + 1) t) := by
    refine sum_le_sum fun k hk => ?_
    have hk' := mem_range.1 hk
    have hv : 0 ≤ 320 * K ^ 2 * x ^ (j - k) * (2 * Cp * rr k ^ 2 * mm k) / histS R (k + 1) t := by
      have := hm0 k hk'.le; have := hs (k + 1); positivity
    refine (sum_ite_near_le P.a hv).trans (le_of_eq ?_)
    ring
  have hfin := prodBd_real (K := K) hL0 (Nat.cast_nonneg cbnC) hCp (by positivity) hx0 hx2 j
    (fun k => rr k ^ 2 * mm k) (fun k => histS R k t)
    (fun k hk => mul_nonneg (sq_nonneg _) (hm0 k hk)) hs hss
  refine hS1.trans ((add_le_add hS2 hS3).trans (hfin.trans (le_of_eq ?_)))
  rw [prodCP]

end Hist

end

end PtCorr2
