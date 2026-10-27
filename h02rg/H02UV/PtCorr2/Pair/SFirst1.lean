import PtCorr2.Pair.VObsStepAB2
import PtCorr2.Pair.MemAB2
import Obs2.Pair.SFirst1

/-!
# The cancellation of the first-order `S`-contribution along the reduced history

Along `hVR` (the reduced history from `j`, `V'_{j,ab} = 0`):

* **`m4X_hVR_eq_sum`**: `M₄_k(X) = −∑_{j≤i<k}(M₄(Q_i)(X) + M₄(Loc S_i)(X))` (summed
  `m4X_hVR_succ`);
* **`errABX2_eq3_hR`**: the region error `errABX2` of `rABX_flow` equals the reorganised
  `errABX3` (`Obs2.errABX2_eq3`: the `Loc S` parts of the Pauli defect of `V'_k` and of the memory
  cancel; what is left is `n_k·(∑_iM₄(Loc S_i))·m2D(C_k)`);
* **`norm_memABX3_leL`**, **`memABX3_hist_leL`**: the memory term without the `Loc S` tadpole,
  `|mem₃(i,k)| ≤ |𝔡₂_i|τ_{ik} + ker_{ik}(f_i + 2w_i)` (no `Λ_i`).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2 Flow2.Hist

variable {L N : ℕ} [NeZero L]

section Hist

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N) (j : ℕ)
  (o' : ObsSt .two L N) (t : Hist.Seq (Xs R))

/-- **The summed `M₄` recursion of a region along the reduced history.** -/
theorem m4X_hVR_eq_sum (h0 : ObsVabInv P o') (hz : ∀ b, (o'.V b : SA .two (Lam 2 L N)).ab = 0)
    {k : ℕ} (hs : ∀ i, j ≤ i → i < k → ObsSymInv i (obsHistFrom R P j o' i t))
    {X : Finset (Lam 2 L N)} (hX : ∀ i, j ≤ i → i < k → IsPolymer (i + 1) X) (hjk : j ≤ k) :
    m4X P k (hVR R P j o' t k) X = -∑ i ∈ Finset.Ico j k,
      (m4QX P i (hKR R P j o' t i) X +
        m4LSX P i (histCovO R t i) (hVR R P j o' t i) (hWR R P j o' t i) X) :=
  m4_eq_neg_sum (M := fun i => m4X P i (hVR R P j o' t i) X) (n := k)
    (m4X_hVR_start R P j o' t hz X)
    (fun i hi hik => m4X_hVR_succ R P j o' t h0 hi (hs i hi hik) (hX i hi hik)) k hjk le_rfl

/-- **The cancellation along the reduced history**: `errABX2 = errABX3` for a `k`-polymer `X`. -/
theorem errABX2_eq3_hR (h0 : ObsVabInv P o') (hz : ∀ b, (o'.V b : SA .two (Lam 2 L N)).ab = 0)
    {k : ℕ} (hs : ∀ i, j ≤ i → i ≤ k → ObsSymInv i (obsHistFrom R P j o' i t))
    {X : Finset (Lam 2 L N)} (hX : IsPolymer k X) (hjk : j ≤ k) :
    errABX2 P (histCovO R t) (hVR R P j o' t) (hWR R P j o' t) (hKR R P j o' t) X j k =
      errABX3 P (histCovO R t) (hVR R P j o' t) (hWR R P j o' t) (hKR R P j o' t) X j k :=
  errABX2_eq3 P _ _ _ _ X j k
    (m4X_hVR_eq_sum R P j o' t h0 hz (fun i hi hik => hs i hi hik.le)
      (fun i _ hik => Step2.isPolymer_of_le hX (i + 1) (by omega)) hjk)
    (hVR_ab_mem R P j o' t h0 k) (hVR_ab_sym R P j o' t (hs k hjk le_rfl))

end Hist

section Mem

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- **One memory term without the `Loc S` tadpole** (`i < k ≤ n`, `ValidAtL R n`):
`|mem₃(i,k)| ≤ pτ + ker_{ik}(f + 2w)`. -/
theorem norm_memABX3_leL (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8) {n : ℕ} (hnN : n < N)
    (hVn : ∀ i < n, ValidAt R i) (hVL : ValidAtL R n) (t : Flow2.Hist.Seq (Xs R))
    (P : ObsPts 2 L N) {i k : ℕ} (hik : i < k) (hkn : k ≤ n) (hiN : i + 3 ≤ N) (hL : prodLb ≤ L)
    (V W : ℕ → OFam .two 2 L N) {K : OAct .two 2 L N} (H : OAnchS P i (V i) (W i) K)
    (X : Finset (Lam 2 L N)) {p τ f w : ℝ} (hf : 0 ≤ f) (hw : 0 ≤ w)
    (hp : ‖pdefM2X i (histCovO R t i) (V i) X‖ ≤ p)
    (hτ : ‖tadInc2 P (histCovO R t) V i k‖ ≤ τ)
    (hD : LocSz R t P.a i (FC (histCovO R t i) (dABX P i (histCovO R t i) (V i) X)
      (VprLO i (histCovO R t i) (V i) : SA .two (Lam 2 L N)).e) f)
    (hPr : ∀ c', (c' = blk (i + 1) P.a ∨ c' = blk (i + 1) P.b) →
      LocSz R t P.a i ((Wnext2O P i (histCovO R t i) (V i) (W i) c' -
        ∑ b ∈ blocks i (blockSet (L := L) (N := N) (i + 1) c'),
          WpO P i (histCovO R t i) (V i) (W i) b : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).ab w) :
    ‖memABX3 P (histCovO R t) V W X i k‖ ≤ p * τ + memKer R t i k * (f + 2 * w) := by
  have hK := memKer_nonneg R hρ0 hρ t i k
  have h1 : ‖dTauABX P i (histCovO R t i) (V i) X (histCovO R t k + cumBetween (histCovO R t) i k) -
      dTauABX P i (histCovO R t i) (V i) X (cumBetween (histCovO R t) i k)‖ ≤
      memKer R t i k * f := by
    unfold dTauABX
    rw [sub_sub_sub_cancel_right]
    exact delta_locSz_leL R hρ0 hρ hnN hVn hVL t P.a hik hkn hiN hL hf hD
  have h3 := norm_sum_tad_diff_le' (blocks (i + 1) X)
    (fun c' => ((Wnext2O P i (histCovO R t i) (V i) (W i) c' -
      ∑ b ∈ blocks i (blockSet (L := L) (N := N) (i + 1) c'),
        WpO P i (histCovO R t i) (V i) (W i) b : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).ab)
    (histCovO R t k + cumBetween (histCovO R t) i k) (cumBetween (histCovO R t) i k)
    (blk (i + 1) P.a) (blk (i + 1) P.b) (mul_nonneg hK hw)
    (fun c' _ h1 h2 => prodPart_ab_zero H h1 h2)
    (fun c' _ hc => delta_locSz_leL R hρ0 hρ hnN hVn hVL t P.a hik hkn hiN hL hw (hPr c' hc))
  have hpt : ‖pdefM2X i (histCovO R t i) (V i) X * tadInc2 P (histCovO R t) V i k‖ ≤ p * τ := by
    rw [norm_mul]
    exact mul_le_mul hp hτ (norm_nonneg _) ((norm_nonneg _).trans hp)
  have e : memABX3 P (histCovO R t) V W X i k =
      pdefM2X i (histCovO R t i) (V i) X * tadInc2 P (histCovO R t) V i k +
      (dTauABX P i (histCovO R t i) (V i) X (histCovO R t k + cumBetween (histCovO R t) i k) -
        dTauABX P i (histCovO R t i) (V i) X (cumBetween (histCovO R t) i k)) +
      (∑ c' ∈ blocks (i + 1) X, mass2 (expLC (histCovO R t k + cumBetween (histCovO R t) i k)
          ((Wnext2O P i (histCovO R t i) (V i) (W i) c' -
            ∑ b ∈ blocks i (blockSet (L := L) (N := N) (i + 1) c'),
              WpO P i (histCovO R t i) (V i) (W i) b : OE .two (Lam 2 L N)) :
                SA .two (Lam 2 L N)).ab) -
        ∑ c' ∈ blocks (i + 1) X, mass2 (expLC (cumBetween (histCovO R t) i k)
          ((Wnext2O P i (histCovO R t i) (V i) (W i) c' -
            ∑ b ∈ blocks i (blockSet (L := L) (N := N) (i + 1) c'),
              WpO P i (histCovO R t i) (V i) (W i) b : OE .two (Lam 2 L N)) :
                SA .two (Lam 2 L N)).ab)) := rfl
  rw [e]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add ((norm_add_le _ _).trans (add_le_add hpt h1)) h3).trans (le_of_eq ?_)
  ring

/-- **The memory sum without `Loc S`** (`k ≤ n`, `ValidAtL R n`). -/
theorem memABX3_hist_leL (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8) {n : ℕ} (hnN : n < N)
    (hVn : ∀ i < n, ValidAt R i) (hVL : ValidAtL R n) (t : Flow2.Hist.Seq (Xs R))
    (P : ObsPts 2 L N) (hL : prodLb ≤ L) (V W : ℕ → OFam .two 2 L N) (K : ℕ → OAct .two 2 L N)
    (X : Finset (Lam 2 L N))
    {j k : ℕ} (hkn : k ≤ n) (hkN : k + 2 ≤ N) (H : ∀ i, j ≤ i → i < k → OAnchS P i (V i) (W i) (K i))
    (p f w : ℕ → ℝ) (τ : ℕ → ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) (hw : ∀ i, 0 ≤ w i)
    (hp : ∀ i, j ≤ i → i < k → ‖pdefM2X i (histCovO R t i) (V i) X‖ ≤ p i)
    (hτ : ∀ i, j ≤ i → i < k → ‖tadInc2 P (histCovO R t) V i k‖ ≤ τ i k)
    (hD : ∀ i, j ≤ i → i < k → LocSz R t P.a i (FC (histCovO R t i)
      (dABX P i (histCovO R t i) (V i) X) (VprLO i (histCovO R t i) (V i) : SA .two (Lam 2 L N)).e)
      (f i))
    (hPr : ∀ i, j ≤ i → i < k → ∀ c', (c' = blk (i + 1) P.a ∨ c' = blk (i + 1) P.b) →
      LocSz R t P.a i ((Wnext2O P i (histCovO R t i) (V i) (W i) c' -
        ∑ b ∈ blocks i (blockSet (L := L) (N := N) (i + 1) c'),
          WpO P i (histCovO R t i) (V i) (W i) b : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).ab
        (w i)) :
    ∑ i ∈ Ico j k, ‖memABX3 P (histCovO R t) V W X i k‖ ≤
      ∑ i ∈ Ico j k, (p i * τ i k + memKer R t i k * (f i + 2 * w i)) :=
  sum_le_sum fun i hi => by
    obtain ⟨h1, h2⟩ := mem_Ico.1 hi
    exact norm_memABX3_leL R hρ0 hρ hnN hVn hVL t P h2 hkn (by omega) hL V W (H i h1 h2) X (hf i)
      (hw i) (hp i h1 h2) (hτ i h1 h2) (hD i h1 h2) (hPr i h1 h2)

end Mem

end

end PtCorr2
