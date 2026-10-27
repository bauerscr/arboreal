import PtCorr2.Pair.GradABHist3
import PtCorr2.Pair.SXOStepAB
import Obs2.Pair.PairRed

/-!
# The `V`-step of the joint induction (1): the gradient of `ℒ_C m₄` with covariance differences

`PtCorr2.gradM4Sz_hVR_block_sizes` bounds the `M₄` part of the gradient sources with the uniform
bound `|C_i(x, y)| ≤ c_i` only (`Obs2.gSzE_LopM4_le`). Its first-order term is then
`μ_i·c_i·4ℓ_{i+1}g_i` with `g_i = 2|a−b|_∞ℓ_{i+1}/L^{i+1}` and `μ_i ≲ ℓ^{-4}(L^i/|a−b|)²κ_i`, i.e.
`≈ κ_iL^{i-1}/|a−b|`: it **grows** like `L^{i−j_x}` above coalescence, and the gradient flow (contraction
`q⁴/L` per step) does not compensate it. The first-order coefficients of `ℒ_C m₄` are the
covariance **differences** `C(a,a) − C(b,a)`, `C(a,a) − C(a,b)`, which are `≤ |w|ℓ_C²/L^{i+1}` for a
lattice path `w` from `a` to `b` (`GoodCov2`). With them the first-order term is of the size of the
second-order one, `≲ κ_iL^{2(i'−i−1)}`, and the gradient flow closes.

* **`gSzE_LopM4_leD`**: `gSzE(ℒ_C m₄) ≤ 2d·ℓg + c·g²` from `|C(a,a)| ≤ c` and the two differences
  `≤ d`;
* **`covDiff_le_path`**: the differences from `GoodCov2` and a path;
* **`gradM4Sz_hVR_block_sizesD`**: `gradM4Sz_hVR_block_sizes` with `μ_i(2d_iℓ_{i+1}g_i + c_ig_i²)` in
  place of `μ_ic_i(4ℓ_{i+1}g_i + g_i²)`.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD Obs2 Flow2 Flow2.Hist LocObs

variable {L N : ℕ} [NeZero L]

/-- **The gradient size of `ℒ_C m₄` from covariance differences.** -/
theorem gSzE_LopM4_leD {E h ℓ c dc : ℝ} (hE : 0 ≤ E) (hh : 0 ≤ h) (hℓ : 0 ≤ ℓ)
    (C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ) {a b : Lam 2 L N} (hab : a ≠ b)
    (hC : ‖C a a‖ ≤ c) (hD1 : ‖C a a - C b a‖ ≤ dc) (hD2 : ‖C a a - C a b‖ ≤ dc) :
    gSzE E a b h ℓ (LopM4 C a b) ≤
      2 * dc * (ℓ * (E * ℓ * h⁻¹)) + c * ((E * ℓ * h⁻¹) * (E * ℓ * h⁻¹)) := by
  rw [gSzE_LopM4_eq C hab]
  have hg : 0 ≤ E * ℓ * h⁻¹ := by positivity
  have hu : 0 ≤ ℓ * (E * ℓ * h⁻¹) := mul_nonneg hℓ hg
  have hv : 0 ≤ (E * ℓ * h⁻¹) * (E * ℓ * h⁻¹) := mul_nonneg hg hg
  have h1 : (‖C a a - C b a‖ + ‖C a a - C a b‖) * (ℓ * (E * ℓ * h⁻¹)) ≤
      2 * dc * (ℓ * (E * ℓ * h⁻¹)) :=
    mul_le_mul_of_nonneg_right (by linarith) hu
  have h2 := mul_le_mul_of_nonneg_right hC hv
  linarith

/-- **Covariance differences along a path**: for `b = a + w`,
`|C(a,a) − C(b,a)|, |C(a,a) − C(a,b)| ≤ |w|ℓ_C²/L^{k+1}` and `|C(a,a)| ≤ ℓ_C²`. -/
theorem covDiff_le_path {k : ℕ} {ℓC : ℝ} {C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ}
    (hC : GoodCov2 k ℓC C) (a : Lam 2 L N) (w : List (Dir 2)) :
    ‖C a a‖ ≤ ℓC ^ 2 ∧
    ‖C a a - C (pathEnd a w) a‖ ≤ w.length * (ℓC ^ 2 / (L : ℝ) ^ (k + 1)) ∧
    ‖C a a - C a (pathEnd a w)‖ ≤ w.length * (ℓC ^ 2 / (L : ℝ) ^ (k + 1)) := by
  refine ⟨good_entry hC a a, ?_, ?_⟩
  · rw [← norm_neg, neg_sub]; exact norm_cov_path_L hC a a w
  · rw [← norm_neg, neg_sub]; exact norm_cov_path_R hC a a w

section Hist

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N) (j : ℕ)
  (o' : ObsSt .two L N) (t : Hist.Seq (Xs R))

/-- **The `γ_k` input of `hVo_of_coeffsP` for a `k`-block with covariance differences**
(`gradM4Sz_hVR_block_sizes` with `|C_i(a,a)| ≤ c_i` and `|C_i(a,a) − C_i(b,a)|`,
`|C_i(a,a) − C_i(a,b)| ≤ d_i`). -/
theorem gradM4Sz_hVR_block_sizesD {Cc : ℝ} (hCc0 : 0 ≤ Cc)
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
    (cC dC η μ κQ κS : ℕ → ℝ)
    (hC : ∀ i, j ≤ i → i < k → ‖histCovO R t i P.a P.a‖ ≤ cC i)
    (hD : ∀ i, j ≤ i → i < k → ‖histCovO R t i P.a P.a - histCovO R t i P.b P.a‖ ≤ dC i ∧
      ‖histCovO R t i P.a P.a - histCovO R t i P.a P.b‖ ≤ dC i)
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
        (μ i * (2 * dC i * (ℓ (i + 1) * g i) + cC i * (g i * g i)) +
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
  have hM := gSzE_LopM4_leD hE hh.le (hℓ (i + 1)).le (histCovO R t i) hab (hC i hji hik)
    (hD i hji hik).1 (hD i hji hik).2
  have hMn := gSzE_nonneg hE hh.le (hℓ (i + 1)).le P.a P.b (LopM4 (histCovO R t i) P.a P.b)
  have hμ' := hμ i hji hik
  have h1 : (‖m4X P i (hVR R P j o' t i) (blockSet (L := L) (N := N) k c)‖ +
        ‖∑ b ∈ blocks i (blockSet (L := L) (N := N) k c),
          cfAB4 P.a P.b (Q2O P i (hKR R P j o' t i) b : SA .two (Lam 2 L N)).ab‖) *
        gSzE E P.a P.b ((L : ℝ) ^ (i + 1)) (ℓ (i + 1)) (LopM4 (histCovO R t i) P.a P.b) ≤
      μ i * (2 * dC i * (ℓ (i + 1) * g i) + cC i * (g i * g i)) :=
    mul_le_mul hμ' hM hMn ((by positivity : (0 : ℝ) ≤ _).trans hμ')
  have e1 : E * ℓ (i + 1) * ((L : ℝ) ^ (i + 1))⁻¹ = g i := rfl
  rw [e1] at hS
  linarith

end Hist

end

end PtCorr2
