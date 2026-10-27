import PtCorr2.Pair.GradABHist2
import Obs2.Flow.GradAB4

/-!
# The gradient coefficients of `V'_{ab}` along the history with the true field scale

`PtCorr2.gSzE_gX_flow_le` needs a nonincreasing field-scale sequence `ℓ_{i+1} ≤ ℓ_i`; the field scale
`s_j = histS R j t` of the history is not monotone (`s_{j+1} = s_j·fscale(1 + ζ_j)`), only
`s_{j+1} ≤ q s_j` with `q = 1 + ρ` (`histS_ratio_le`). Here the flow is redone with a ratio `q ≥ 1`
(contraction `q⁴/L` per step, `Obs2.gSzE_scale_le_q`), and the sources are bounded by the per-scale
sizes of `K` and `S` restricted to the block, the `M₄` coefficients included:

* **`gSzE_gX_flow_leq`**, **`gSzE_hVR_block_leq`**: `Γ_k ≤ ∑_{j≤i<k}(q⁴/L)^{k-1-i}σ_i`;
* **`m4SrcX_le_sizes`**: the `M₄` sources of one step of a region from `κ^Q_i`, `κ^S_i`;
* **`m4X_hVR_sizes`**: `|M₄_i(X)|` of a region (the `μ` of the gradient sources);
* **`gradM4Sz_hVR_block_sizes`**: the `γ_k` input of `hVo_of_coeffsP` (base point `a`,
  `X = {a}`, `E = 2|a−b|_∞`) for a `k`-block from the sizes `μ_i`, `κ^Q_i`, `κ^S_i` and a uniform
  bound `|C_i(x,y)| ≤ c_i` (`= s_i²` for `GoodCov2`).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD Obs2 Flow2 Flow2.Hist LocObs

variable {L N : ℕ} [NeZero L]

section Hist

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N) (j : ℕ)
  (o' : ObsSt .two L N) (t : Hist.Seq (Xs R))

/-- **The gradient coefficients of a region with a field-scale ratio `q`.** -/
theorem gSzE_gX_flow_leq (h0 : ObsVabInv P o') (hz : ∀ b, (o'.V b : SA .two (Lam 2 L N)).ab = 0)
    {k : ℕ} (hs : ∀ i, j ≤ i → i < k → ObsSymInv i (obsHistFrom R P j o' i t))
    {X : Finset (Lam 2 L N)} (hX : ∀ i, j ≤ i → i < k → IsPolymer (i + 1) X) (hjk : j ≤ k)
    {E q : ℝ} (hE : 0 ≤ E) (hq : 1 ≤ q) (ℓ : ℕ → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (hℓq : ∀ i, j ≤ i → i < k → ℓ (i + 1) ≤ q * ℓ i) :
    gSzE E P.a P.b ((L : ℝ) ^ k) (ℓ k) (gX R P j o' t k X) ≤
      ∑ i ∈ Finset.Ico j k, (q ^ 4 * (L : ℝ)⁻¹) ^ (k - 1 - i) *
        gSrcX R P j o' t E ((L : ℝ) ^ (i + 1)) (ℓ (i + 1)) i X := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hL0 : (0 : ℝ) < L := by linarith
  have hq0 : 0 ≤ q ^ 4 * (L : ℝ)⁻¹ := by positivity
  set x : ℕ → ℝ := fun i => if i ≤ k then
    gSzE E P.a P.b ((L : ℝ) ^ i) (ℓ i) (gX R P j o' t i X) else 0 with hx
  set σ : ℕ → ℝ := fun i => if i < k then
    gSrcX R P j o' t E ((L : ℝ) ^ (i + 1)) (ℓ (i + 1)) i X else 0 with hσ
  have hrec := geom_rec_le (x := x) (σ := σ) (q := q ^ 4 * (L : ℝ)⁻¹) hq0 (j := j)
    (by simp only [hx, if_pos hjk, gX_start R P j o' t hz, gSzE_zero, le_refl])
    (fun i hi => by
      rcases Nat.lt_or_ge i k with hik | hik
      · simp only [hx, hσ, if_pos hik, if_pos hik.le, if_pos (show i + 1 ≤ k by omega)]
        have hh : (0 : ℝ) < (L : ℝ) ^ i := pow_pos hL0 i
        have step := gSzE_gX_succ_le R P j o' t h0 hi (hs i hi hik) (hX i hi hik) hE
          (by positivity : (0 : ℝ) ≤ (L : ℝ) ^ (i + 1)) (hℓ (i + 1)).le
        have sc := gSzE_scale_le_q hE hh (pow_le_pow_right₀ hL1 (Nat.le_succ i))
          (hℓ (i + 1)).le hq (hℓq i hi hik) P.a P.b (gX R P j o' t i X)
        have e : (L : ℝ) ^ i * ((L : ℝ) ^ (i + 1))⁻¹ = (L : ℝ)⁻¹ := by
          rw [pow_succ, mul_inv, ← mul_assoc, mul_inv_cancel₀ hh.ne', one_mul]
        simp only [Nat.succ_eq_add_one] at sc
        rw [e] at sc
        linarith
      · have h1 : ¬ i + 1 ≤ k := by omega
        simp only [hx, hσ, if_neg h1, if_neg (show ¬ i < k by omega)]
        rcases Nat.lt_or_ge k i with hki | hki
        · simp only [if_neg (show ¬ i ≤ k by omega), mul_zero, add_zero, le_refl]
        · obtain rfl : i = k := by omega
          simp only [le_refl, if_true, add_zero]
          exact mul_nonneg hq0 (gSzE_nonneg hE (by positivity) (hℓ _).le _ _ _))
    k hjk
  simp only [hx, le_refl, if_true] at hrec
  refine hrec.trans (le_of_eq (sum_congr rfl fun i hi => ?_))
  simp only [hσ, if_pos (Finset.mem_Ico.1 hi).2]

/-- **The gradient coefficients of a `k`-block with a field-scale ratio `q`.** -/
theorem gSzE_hVR_block_leq (h0 : ObsVabInv P o') (hz : ∀ b, (o'.V b : SA .two (Lam 2 L N)).ab = 0)
    {k : ℕ} (hs : ∀ i, j ≤ i → i < k → ObsSymInv i (obsHistFrom R P j o' i t)) (hjk : j ≤ k)
    {c : Fin 2 → ℕ} (hne : (blockSet (L := L) (N := N) k c).Nonempty)
    {E q : ℝ} (hE : 0 ≤ E) (hq : 1 ≤ q) (ℓ : ℕ → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (hℓq : ∀ i, j ≤ i → i < k → ℓ (i + 1) ≤ q * ℓ i) :
    gSzE E P.a P.b ((L : ℝ) ^ k) (ℓ k) (hVR R P j o' t k c : SA .two (Lam 2 L N)).ab ≤
      ∑ i ∈ Finset.Ico j k, (q ^ 4 * (L : ℝ)⁻¹) ^ (k - 1 - i) *
        gSrcX R P j o' t E ((L : ℝ) ^ (i + 1)) (ℓ (i + 1)) i (blockSet (L := L) (N := N) k c) := by
  rw [← gX_blockSet R P j o' t k hne]
  exact gSzE_gX_flow_leq R P j o' t h0 hz hs
    (fun i _ hik => isPolymer_of_le (isPolymer_blockSet k c) (i + 1) (by omega)) hjk hE hq ℓ hℓ hℓq

section Sizes

variable {Cc : ℝ} (hCc0 : 0 ≤ Cc)
  (hCc : ∀ m : Fin 2 → ℕ, (∀ i, m i ≤ 1) → ∀ R : ℝ, 1 ≤ R → ∀ α : Dir 2 → ℕ,
    Grassmann.mabs α ≤ pPhi 2 → ∀ u : Zd 2,
    |D1 (fun b v => b +ᵥ v) α (cutP m R) u| ≤ Cc * R ^ (∑ i, m i) / R ^ Grassmann.mabs α)
  (hL : 2 ^ (2 + 3) + 8 * 2 < L) (hab : P.a ≠ P.b)

include hCc0 hCc hL hab

/-- **The `M₄` sources of one step of a region from the sizes of `K` and `S`.** -/
theorem m4SrcX_le_sizes {i : ℕ} (hiN : i + 1 < N) (X : Finset (Lam 2 L N)) {ℓi ℓi1 : ℝ}
    (hℓi : 0 < ℓi) (hℓi1 : 0 < ℓi1)
    (hKl : ∀ X', IsSmall i X' →
      (hKR R P j o' t i X' : SA .two (Lam 2 L N)).ab ∈ NX (nbhd i X' : Set (Lam 2 L N)))
    (hSl : ∀ b ∈ blockIdx (L := L) (N := N) i,
      (SXO i (histCovO R t i) (hVR R P j o' t i) (hWR R P j o' t i)
        (Step2.Bp (L := L) (N := N) i b) : SA .two (Lam 2 L N)).ab ∈
        NX (nbhd (i + 1) (Step2.Bp (L := L) (N := N) i b) : Set (Lam 2 L N)))
    {κQ κS : ℝ}
    (hκQ : (open Classical in ∑ b ∈ blocks i X,
        ∑ X' ∈ (smallSets i).filter (fun X' => blockSet i b ⊆ X'),
          (Tj 2 (L : ℝ) i ℓi (hKR R P j o' t i X' : SA .two (Lam 2 L N)).ab).toReal) ≤ κQ)
    (hκS : ∑ b ∈ blocks i X,
        (Tj 2 (L : ℝ) (i + 1) ℓi1
          (SXO i (histCovO R t i) (hVR R P j o' t i) (hWR R P j o' t i)
            (Step2.Bp (L := L) (N := N) i b) : SA .two (Lam 2 L N)).ab).toReal ≤ κS) :
    m4SrcX R P j o' t i X ≤
      KM4 2 Cc * (ℓi⁻¹ ^ 4 * (((L : ℝ) ^ i) ^ 2 / ((supNorm (P.a - P.b) : ℕ) : ℝ) ^ 2) * κQ +
        ℓi1⁻¹ ^ 4 * (((L : ℝ) ^ (i + 1)) ^ 2 / ((supNorm (P.a - P.b) : ℕ) : ℝ) ^ 2) * κS) := by
  classical
  have hK := KM4_nonneg 2 (Cc := Cc)
  set s : ℝ := ((supNorm (P.a - P.b) : ℕ) : ℝ)
  have hbI : ∀ b ∈ blocks i X, b ∈ blockIdx (L := L) (N := N) i :=
    fun b hb => mem_blockIdx_of_mem_blocks hb
  have hQ : ∑ b ∈ blocks i X,
      ‖cfAB4 P.a P.b (Q2O P i (hKR R P j o' t i) b : SA .two (Lam 2 L N)).ab‖ ≤
        KM4 2 Cc * (ℓi⁻¹ ^ 4 * (((L : ℝ) ^ i) ^ 2 / s ^ 2) * κQ) := by
    refine (sum_le_sum fun b _ => norm_cfAB4_Q2O_le hCc0 hCc hL P hab i (hKR R P j o' t i)
      hKl b hℓi).trans ?_
    rw [← mul_sum]
    have hu : 0 ≤ KM4 2 Cc * ℓi⁻¹ ^ 4 * (((L : ℝ) ^ i) ^ 2 / s ^ 2) := by positivity
    calc _ ≤ KM4 2 Cc * ℓi⁻¹ ^ 4 * (((L : ℝ) ^ i) ^ 2 / s ^ 2) * κQ :=
          mul_le_mul_of_nonneg_left hκQ hu
      _ = _ := by ring
  have hS : ∑ b ∈ blocks i X,
      ‖cfAB4 P.a P.b (LSO P i (histCovO R t i) (hVR R P j o' t i) (hWR R P j o' t i) b :
        SA .two (Lam 2 L N)).ab‖ ≤
        KM4 2 Cc * (ℓi1⁻¹ ^ 4 * (((L : ℝ) ^ (i + 1)) ^ 2 / s ^ 2) * κS) := by
    refine (sum_le_sum fun b hb => norm_cfAB4_LSO_le hCc0 hCc hL P hab hiN _ _ _ (hbI b hb)
      (hSl b (hbI b hb)) hℓi1).trans ?_
    rw [← mul_sum]
    have hu : 0 ≤ KM4 2 Cc * ℓi1⁻¹ ^ 4 * (((L : ℝ) ^ (i + 1)) ^ 2 / s ^ 2) := by positivity
    calc _ ≤ KM4 2 Cc * ℓi1⁻¹ ^ 4 * (((L : ℝ) ^ (i + 1)) ^ 2 / s ^ 2) * κS :=
          mul_le_mul_of_nonneg_left hκS hu
      _ = _ := by ring
  unfold m4SrcX
  calc _ ≤ KM4 2 Cc * (ℓi⁻¹ ^ 4 * (((L : ℝ) ^ i) ^ 2 / s ^ 2) * κQ) +
        KM4 2 Cc * (ℓi1⁻¹ ^ 4 * (((L : ℝ) ^ (i + 1)) ^ 2 / s ^ 2) * κS) := add_le_add hQ hS
    _ = _ := by ring

omit hCc0 hCc hL hab in
/-- The `M₄` part of the `Q`-source is part of the `M₄` source. -/
theorem norm_sum_cfAB4_Q2O_le_m4SrcX (i : ℕ) (X : Finset (Lam 2 L N)) :
    ‖∑ b ∈ blocks i X, cfAB4 P.a P.b (Q2O P i (hKR R P j o' t i) b : SA .two (Lam 2 L N)).ab‖ ≤
      m4SrcX R P j o' t i X := by
  unfold m4SrcX
  have := norm_sum_le (blocks i X)
    (fun b => cfAB4 P.a P.b (Q2O P i (hKR R P j o' t i) b : SA .two (Lam 2 L N)).ab)
  have := sum_nonneg fun b (_ : b ∈ blocks i X) => norm_nonneg
    (cfAB4 P.a P.b (LSO P i (histCovO R t i) (hVR R P j o' t i) (hWR R P j o' t i) b :
      SA .two (Lam 2 L N)).ab)
  linarith

end Sizes

/-- **The `μ` of the gradient sources of a region**: `|M₄_i(X)| + |∑M₄(Q_i)| ≤ ∑_{j≤i'≤i}` (the
`M₄` sources of step `i'` in `X`). -/
theorem m4X_hVR_mu_le (h0 : ObsVabInv P o') (hz : ∀ b, (o'.V b : SA .two (Lam 2 L N)).ab = 0)
    {i : ℕ} (hs : ∀ i', j ≤ i' → i' < i → ObsSymInv i' (obsHistFrom R P j o' i' t))
    {X : Finset (Lam 2 L N)} (hX : ∀ i', j ≤ i' → i' < i → IsPolymer (i' + 1) X) (hji : j ≤ i) :
    ‖m4X P i (hVR R P j o' t i) X‖ +
        ‖∑ b ∈ blocks i X, cfAB4 P.a P.b (Q2O P i (hKR R P j o' t i) b : SA .two (Lam 2 L N)).ab‖ ≤
      ∑ i' ∈ Finset.Ico j (i + 1), m4SrcX R P j o' t i' X := by
  rw [Finset.sum_Ico_succ_top hji]
  exact add_le_add (m4X_hVR_le R P j o' t h0 hz hs hX hji)
    (norm_sum_cfAB4_Q2O_le_m4SrcX R P j o' t i X)

/-- **The `γ_k` input of `hVo_of_coeffsP` for a `k`-block** (base point `a`, `X = {a}`,
`E = 2|a − b|_∞`): with `g_i = Eℓ_{i+1}/L^{i+1}`, `|C_i(x,y)| ≤ c_i`, `μ_i ≥ |M₄_i(B)| + |∑M₄(Q_i)|`,
`η_i ≥ E/L^{i+1}`,
`gradM4Sz ≤ ∑_{j≤i<k}(q⁴/L)^{k-1-i}(μ_ic_i(4ℓ_{i+1}g_i + g_i²) + B^Q_iκ^Q_i + B^S_iκ^S_i)`. -/
theorem gradM4Sz_hVR_block_sizes {Cc : ℝ} (hCc0 : 0 ≤ Cc)
    (hCc : ∀ m : Fin 2 → ℕ, (∀ i, m i ≤ 1) → ∀ R : ℝ, 1 ≤ R → ∀ α : Dir 2 → ℕ,
      Grassmann.mabs α ≤ pPhi 2 → ∀ u : Zd 2,
      |D1 (fun b v => b +ᵥ v) α (cutP m R) u| ≤ Cc * R ^ (∑ i, m i) / R ^ Grassmann.mabs α)
    (hL : 2 ^ (2 + 3) + 8 * 2 < L) (hab : P.a ≠ P.b) (h0 : ObsVabInv P o')
    (hz : ∀ b, (o'.V b : SA .two (Lam 2 L N)).ab = 0)
    {k : ℕ} (hkN : k + 1 ≤ N) (hs : ∀ i, j ≤ i → i < k → ObsSymInv i (obsHistFrom R P j o' i t))
    (hjk : j ≤ k) {c : Fin 2 → ℕ} (hne : (blockSet (L := L) (N := N) k c).Nonempty)
    {q : ℝ} (hq : 1 ≤ q) (ℓ : ℕ → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (hℓq : ∀ i, j ≤ i → i < k → ℓ (i + 1) ≤ q * ℓ i)
    (hℓ2 : ∀ i, j ≤ i → i < k → ℓ (i + 1) ≤ 2 * ℓ i)
    (cC η μ κQ κS : ℕ → ℝ)
    (hC : ∀ i, j ≤ i → i < k → ∀ x y, ‖histCovO R t i x y‖ ≤ cC i)
    (hη : ∀ i, j ≤ i → i < k →
      2 * ((supNorm (P.a - P.b) : ℕ) : ℝ) * ((L : ℝ) ^ (i + 1))⁻¹ ≤ η i)
    (hμ : ∀ i, j ≤ i → i < k →
      ‖m4X P i (hVR R P j o' t i) (blockSet (L := L) (N := N) k c)‖ +
        ‖∑ b ∈ blocks i (blockSet (L := L) (N := N) k c),
          cfAB4 P.a P.b (Q2O P i (hKR R P j o' t i) b : SA .two (Lam 2 L N)).ab‖ ≤ μ i)
    (hKl : ∀ i, j ≤ i → i < k → ∀ X, IsSmall i X →
      (hKR R P j o' t i X : SA .two (Lam 2 L N)).ab ∈ NX (nbhd i X : Set (Lam 2 L N)))
    (hSl : ∀ i, j ≤ i → i < k → ∀ b ∈ blockIdx (L := L) (N := N) i,
      (SXO i (histCovO R t i) (hVR R P j o' t i) (hWR R P j o' t i)
        (Step2.Bp (L := L) (N := N) i b) : SA .two (Lam 2 L N)).ab ∈
        NX (nbhd (i + 1) (Step2.Bp (L := L) (N := N) i b) : Set (Lam 2 L N)))
    (hκQ : ∀ i, j ≤ i → i < k →
      (open Classical in ∑ b ∈ blocks i (blockSet (L := L) (N := N) k c),
        ∑ X ∈ (smallSets i).filter (fun X => blockSet i b ⊆ X),
          (Tj 2 (L : ℝ) i (ℓ i) (hKR R P j o' t i X : SA .two (Lam 2 L N)).ab).toReal) ≤ κQ i)
    (hκS : ∀ i, j ≤ i → i < k →
      ∑ b ∈ blocks i (blockSet (L := L) (N := N) k c),
        (Tj 2 (L : ℝ) (i + 1) (ℓ (i + 1))
          (SXO i (histCovO R t i) (hVR R P j o' t i) (hWR R P j o' t i)
            (Step2.Bp (L := L) (N := N) i b) : SA .two (Lam 2 L N)).ab).toReal ≤ κS i) :
    let E := 2 * ((supNorm (P.a - P.b) : ℕ) : ℝ)
    let g := fun i => E * ℓ (i + 1) * ((L : ℝ) ^ (i + 1))⁻¹
    gradM4Sz {P.a} P.a P.b ((L : ℝ) ^ k) (ℓ k) (hVR R P j o' t k c : SA .two (Lam 2 L N)).ab ≤
      ∑ i ∈ Finset.Ico j k, (q ^ 4 * (L : ℝ)⁻¹) ^ (k - 1 - i) *
        (μ i * (cC i * (4 * (ℓ (i + 1) * g i) + g i * g i)) +
          ((1 + η i) * (KG 2 Cc 4 * ((L : ℝ) ^ i * ((L : ℝ) ^ (i + 1))⁻¹)) +
            (ℓ i)⁻¹ ^ 2 * (2 * (ℓ (i + 1) * g i) + g i * g i)) * κQ i +
          ((1 + η i) * (KG 2 Cc 4 * ((L : ℝ) ^ (i + 1) * ((L : ℝ) ^ (i + 1))⁻¹)) +
            (ℓ (i + 1))⁻¹ ^ 2 * (2 * (ℓ (i + 1) * g i) + g i * g i)) * κS i) := by
  intro E g
  have hE : 0 ≤ E := by positivity
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hXE : eN1 ({P.a} : Finset (Lam 2 L N)) P.a P.b ≤ E := by
    have := eN1_single_le P.a P.b
    simpa [E] using this
  refine (gradM4Sz_le_gSzE {P.a} P.a P.b hXE (by positivity) (hℓ k).le _).trans
    ((gSzE_hVR_block_leq R P j o' t h0 hz hs hjk hne hE hq ℓ hℓ hℓq).trans
      (sum_le_sum fun i hi => ?_))
  obtain ⟨hji, hik⟩ := Finset.mem_Ico.1 hi
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hEκ : ∀ X : Finset (Lam 2 L N), E * eN1 X P.a P.b ≤ 4 * eN2 X P.a P.b := by
    intro X
    have := eN1_mul_supNorm_le (d := 2) one_le_two X P.a P.b
    simp only [E]
    push_cast at this
    nlinarith [eN1_nonneg X P.a P.b]
  have hh : (0 : ℝ) < (L : ℝ) ^ (i + 1) := pow_pos (by linarith) _
  have hS := gSrcX_le R P j o' t hCc0 hCc hL hab hE (by norm_num : (0 : ℝ) ≤ 4) hEκ
    (show i + 1 < N by omega) (blockSet (L := L) (N := N) k c) (hℓ i) (hℓ (i + 1)) (hℓ (i + 1)).le
    (hℓ2 i hji hik) (by linarith [hℓ (i + 1)]) (hη i hji hik) (hKl i hji hik) (hSl i hji hik)
    (hκQ i hji hik) (hκS i hji hik)
  have hg0 : 0 ≤ g i := mul_nonneg (mul_nonneg hE (hℓ (i + 1)).le) (inv_nonneg.2 hh.le)
  have hM := gSzE_LopM4_le hE hh.le (hℓ (i + 1)).le (histCovO R t i) hab (hC i hji hik)
  have hMn := gSzE_nonneg hE hh.le (hℓ (i + 1)).le P.a P.b (LopM4 (histCovO R t i) P.a P.b)
  have hμ' := hμ i hji hik
  have h1 : (‖m4X P i (hVR R P j o' t i) (blockSet (L := L) (N := N) k c)‖ +
        ‖∑ b ∈ blocks i (blockSet (L := L) (N := N) k c),
          cfAB4 P.a P.b (Q2O P i (hKR R P j o' t i) b : SA .two (Lam 2 L N)).ab‖) *
        gSzE E P.a P.b ((L : ℝ) ^ (i + 1)) (ℓ (i + 1)) (LopM4 (histCovO R t i) P.a P.b) ≤
      μ i * (cC i * (4 * (ℓ (i + 1) * g i) + g i * g i)) :=
    mul_le_mul hμ' hM hMn ((by positivity : (0 : ℝ) ≤ _).trans hμ')
  have e1 : E * ℓ (i + 1) * ((L : ℝ) ^ (i + 1))⁻¹ = g i := rfl
  rw [e1] at hS
  linarith

end Hist

end

end PtCorr2
