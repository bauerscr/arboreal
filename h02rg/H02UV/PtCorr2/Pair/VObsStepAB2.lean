import PtCorr2.Pair.VObsStepAB1
import Obs2.Flow.VObsAB4X

/-!
# The `M₄` flow and the gradient flow of `V'_{ab}` along the reduced history

Along `hVR` (the history from `j`, `V' = V'^{obs}`):

* **`m4Tot_hVR_succ`**: `M₄_{k+1} = M₄_k − ∑_BM₄(Q_k(B)_{ab}) − ∑_BM₄(Loc S_k(B)_{ab})`
  (`Obs2.m4Tot_succ`), and `M₄_j = 0` if `V'_{j,ab} = 0` (`m4Tot_hVR_start`);
* **`m4_hist_weighted_le`**: with source bounds `σ_k`, the second-order seed weights of
  `PairDefSizesR3` are summable, `∑_k|M₄_k|·2ℓ_k²(L^{j+1}ℓ_k/L^{k+1})² ≤ 16∑_kσ_k`;
* **`m4_hist_weighted_sizes`**: the same with `σ_k = K_{M4}(κ^Q_k + κ^S_k)` from the norms
  `∑_B∑_{X⊇B}‖K_k(X)_{ab}‖_{T_k(ℓ_k)} ≤ κ^Q_k` and `∑_B‖S_k(B_+)_{ab}‖_{T_{k+1}(ℓ_{k+1})} ≤ κ^S_k`
  (`Obs2.norm_cfAB4_Q2O_le`, `Obs2.norm_cfAB4_LSO_le`), for `L^j ≤ 2|a − b|_∞`;
* **`gradAB_hVR_VpO`**: the one-step flow of the gradient part (`Obs2.gradAB_VpO`);
* per region / per block (`Obs2.m4X`): **`m4X_hVR_le`** (`|M₄_k(X)| ≤ ∑_{j≤i<k}` region sources,
  `X` an `(i+1)`-polymer for `i < k`), **`cfAB4_hVR_block_le`** (per `k`-block, sources in the
  fixed region `B`), **`cfAB4_hVR_block_sizes`** (from the norms of the region sources: the `M₄`
  part of the per-block input `γ_k` of `hVo_of_coeffs`).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD Obs2 Flow2 Flow2.Hist

variable {L N : ℕ} [NeZero L]

/-- `L^{j_{ab}} ≤ 2|a − b|_∞` (`j_{ab} = coal`), for `a ≠ b`. -/
theorem pow_coal_le_two_supNorm {d : ℕ} {a b : Lam d L N} (hab : a ≠ b) :
    (L : ℝ) ^ Obs.coal L a b ≤ 2 * ((supNorm (a - b) : ℕ) : ℝ) := by
  have hne : 2 * supNorm (a - b) ≠ 0 := by
    intro h0
    have : supNorm (a - b) = 0 := by omega
    exact hab (sub_eq_zero.1 ((supNorm_eq_zero_iff _).1 this))
  have h := Nat.pow_log_le_self L hne
  have : ((L ^ Obs.coal L a b : ℕ) : ℝ) ≤ ((2 * supNorm (a - b) : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at this
  exact this

section Hist

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N) (j : ℕ)
  (o' : ObsSt .two L N) (t : Hist.Seq (Xs R))

/-- **The `M₄` step along the reduced history.** -/
theorem m4Tot_hVR_succ (h0 : ObsVabInv P o') {k : ℕ} (hk : j ≤ k)
    (hs : ObsSymInv k (obsHistFrom R P j o' k t)) :
    m4Tot P (k + 1) (hVR R P j o' t (k + 1)) = m4Tot P k (hVR R P j o' t k) -
      ∑ b ∈ blockIdx (L := L) (N := N) k,
        cfAB4 P.a P.b (Q2O P k (hKR R P j o' t k) b : SA .two (Lam 2 L N)).ab -
      ∑ b ∈ blockIdx (L := L) (N := N) k,
        cfAB4 P.a P.b (LSO P k (histCovO R t k) (hVR R P j o' t k) (hWR R P j o' t k) b :
          SA .two (Lam 2 L N)).ab := by
  have e : m4Tot P (k + 1) (hVR R P j o' t (k + 1)) =
      m4Tot P (k + 1) (Vnext2O P k (histCovO R t k) (hVR R P j o' t k) (hWR R P j o' t k)
        (hKR R P j o' t k)) := by
    unfold m4Tot
    exact sum_congr rfl fun c _ => by rw [hVR_succ_ab hk]
  rw [e, m4Tot_succ P k _ _ _ _ (hVR_ab_mem R P j o' t h0 k) (hVR_ab_sym R P j o' t hs)]

/-- `M₄_j = 0` if the seed has no `ab` coupling. -/
theorem m4Tot_hVR_start (hz : ∀ b, (o'.V b : SA .two (Lam 2 L N)).ab = 0) :
    m4Tot P j (hVR R P j o' t j) = 0 := by
  unfold m4Tot
  refine sum_eq_zero fun b _ => ?_
  rw [hVR_ab, obsHistFrom_self, hz]
  exact coeff_zero _

/-- **The norm-weighted `M₄` sizes along the reduced history are summable** (from per-step source
bounds). -/
theorem m4_hist_weighted_le (hL : (2 : ℝ) ≤ L) (h0 : ObsVabInv P o')
    (hz : ∀ b, (o'.V b : SA .two (Lam 2 L N)).ab = 0) {n : ℕ}
    (hs : ∀ k, j ≤ k → k < n → ObsSymInv k (obsHistFrom R P j o' k t))
    {s : ℝ} (hs0 : 0 < s) (hsj : (L : ℝ) ^ j ≤ 2 * s) (ℓ : ℕ → ℝ) (hℓ : ∀ k, 0 < ℓ k)
    (hℓm : ∀ i k, i ≤ k → ℓ k ≤ ℓ i) (σ : ℕ → ℝ) (hσ : ∀ k, 0 ≤ σ k)
    (hsrc : ∀ k, j ≤ k → k < n →
      ∑ b ∈ blockIdx (L := L) (N := N) k,
          ‖cfAB4 P.a P.b (Q2O P k (hKR R P j o' t k) b : SA .two (Lam 2 L N)).ab‖ +
        ∑ b ∈ blockIdx (L := L) (N := N) k,
          ‖cfAB4 P.a P.b (LSO P k (histCovO R t k) (hVR R P j o' t k) (hWR R P j o' t k) b :
            SA .two (Lam 2 L N)).ab‖ ≤
        (ℓ (k + 1))⁻¹ ^ 4 * (((L : ℝ) ^ (k + 1)) ^ 2 / s ^ 2) * σ k) :
    ∑ k ∈ Finset.Ico j n, ‖m4Tot P k (hVR R P j o' t k)‖ *
        (2 * ℓ k ^ 2 * ((L : ℝ) ^ (j + 1) * (ℓ k / (L : ℝ) ^ (k + 1))) ^ 2) ≤
      16 * ∑ k ∈ Finset.Ico j n, σ k := by
  refine m4_weighted_sum_le hL hs0 hsj ℓ hℓ hℓm (m4Tot_hVR_start R P j o' t hz) σ hσ n
    fun k hk hkn => ?_
  rw [m4Tot_hVR_succ R P j o' t h0 hk (hs k hk hkn)]
  have e : ∀ x y z : ℂ, x - y - z - x = -(y + z) := fun x y z => by ring
  rw [e, norm_neg]
  exact (norm_add_le _ _).trans
    (le_trans (add_le_add (norm_sum_le _ _) (norm_sum_le _ _)) (hsrc k hk hkn))

/-- **`m4_hist_weighted_le` from the norms of the sources**: `σ_k = K_{M4}(κ^Q_k + κ^S_k)`. -/
theorem m4_hist_weighted_sizes (hL2 : (2 : ℝ) ≤ L) {Cc : ℝ} (hCc0 : 0 ≤ Cc)
    (hCc : ∀ m : Fin 2 → ℕ, (∀ i, m i ≤ 1) → ∀ R : ℝ, 1 ≤ R → ∀ α : Dir 2 → ℕ,
      Grassmann.mabs α ≤ pPhi 2 → ∀ u : Zd 2,
      |D1 (fun b v => b +ᵥ v) α (cutP m R) u| ≤ Cc * R ^ (∑ i, m i) / R ^ Grassmann.mabs α)
    (hL : 2 ^ (2 + 3) + 8 * 2 < L) (hab : P.a ≠ P.b) (h0 : ObsVabInv P o')
    (hz : ∀ b, (o'.V b : SA .two (Lam 2 L N)).ab = 0) {n : ℕ} (hnN : n + 1 ≤ N)
    (hs : ∀ k, j ≤ k → k < n → ObsSymInv k (obsHistFrom R P j o' k t))
    (hsj : (L : ℝ) ^ j ≤ 2 * ((supNorm (P.a - P.b) : ℕ) : ℝ))
    (ℓ : ℕ → ℝ) (hℓ : ∀ k, 0 < ℓ k) (hℓm : ∀ i k, i ≤ k → ℓ k ≤ ℓ i)
    (hKl : ∀ k, j ≤ k → k < n → ∀ X, IsSmall k X →
      (hKR R P j o' t k X : SA .two (Lam 2 L N)).ab ∈ NX (nbhd k X : Set (Lam 2 L N)))
    (hSl : ∀ k, j ≤ k → k < n → ∀ b ∈ blockIdx (L := L) (N := N) k,
      (SXO k (histCovO R t k) (hVR R P j o' t k) (hWR R P j o' t k)
        (Step2.Bp (L := L) (N := N) k b) : SA .two (Lam 2 L N)).ab ∈
        NX (nbhd (k + 1) (Step2.Bp (L := L) (N := N) k b) : Set (Lam 2 L N)))
    (κQ κS : ℕ → ℝ) (hκQ0 : ∀ k, 0 ≤ κQ k) (hκS0 : ∀ k, 0 ≤ κS k)
    (hκQ : ∀ k, j ≤ k → k < n →
      (open Classical in ∑ b ∈ blockIdx (L := L) (N := N) k,
        ∑ X ∈ (smallSets k).filter (fun X => blockSet k b ⊆ X),
          (Tj 2 (L : ℝ) k (ℓ k) (hKR R P j o' t k X : SA .two (Lam 2 L N)).ab).toReal) ≤ κQ k)
    (hκS : ∀ k, j ≤ k → k < n →
      ∑ b ∈ blockIdx (L := L) (N := N) k,
        (Tj 2 (L : ℝ) (k + 1) (ℓ (k + 1))
          (SXO k (histCovO R t k) (hVR R P j o' t k) (hWR R P j o' t k)
            (Step2.Bp (L := L) (N := N) k b) : SA .two (Lam 2 L N)).ab).toReal ≤ κS k) :
    ∑ k ∈ Finset.Ico j n, ‖m4Tot P k (hVR R P j o' t k)‖ *
        (2 * ℓ k ^ 2 * ((L : ℝ) ^ (j + 1) * (ℓ k / (L : ℝ) ^ (k + 1))) ^ 2) ≤
      16 * ∑ k ∈ Finset.Ico j n, KM4 2 Cc * (κQ k + κS k) := by
  classical
  set s : ℝ := ((supNorm (P.a - P.b) : ℕ) : ℝ)
  have hs0 : 0 < s := by
    have : supNorm (P.a - P.b) ≠ 0 := fun h0 =>
      hab (sub_eq_zero.1 ((supNorm_eq_zero_iff _).1 h0))
    show (0 : ℝ) < ((supNorm (P.a - P.b) : ℕ) : ℝ)
    exact_mod_cast Nat.pos_of_ne_zero this
  have hK := KM4_nonneg 2 (Cc := Cc)
  have hL0 : (0 : ℝ) < L := by linarith
  refine m4_hist_weighted_le R P j o' t hL2 h0 hz hs hs0 hsj ℓ hℓ hℓm _
    (fun k => mul_nonneg hK (add_nonneg (hκQ0 k) (hκS0 k))) fun k hk hkn => ?_
  set u : ℝ := (ℓ (k + 1))⁻¹ ^ 4 * (((L : ℝ) ^ (k + 1)) ^ 2 / s ^ 2) with hu
  have hu0 : 0 ≤ u := by have := hℓ (k + 1); positivity
  have hQu : (ℓ k)⁻¹ ^ 4 * (((L : ℝ) ^ k) ^ 2 / s ^ 2) ≤ u := by
    have h1 : (ℓ k)⁻¹ ^ 4 ≤ (ℓ (k + 1))⁻¹ ^ 4 :=
      pow_le_pow_left₀ (inv_nonneg.2 (hℓ k).le)
        (inv_anti₀ (hℓ (k + 1)) (hℓm k (k + 1) (by omega))) 4
    have h2 : ((L : ℝ) ^ k) ^ 2 / s ^ 2 ≤ ((L : ℝ) ^ (k + 1)) ^ 2 / s ^ 2 := by
      have : (L : ℝ) ^ k ≤ (L : ℝ) ^ (k + 1) := pow_le_pow_right₀ (by linarith) (by omega)
      have h3 : 0 ≤ (L : ℝ) ^ k := by positivity
      gcongr
    exact mul_le_mul h1 h2 (by positivity) (by have := hℓ (k + 1); positivity)
  have hQ : ∑ b ∈ blockIdx (L := L) (N := N) k,
      ‖cfAB4 P.a P.b (Q2O P k (hKR R P j o' t k) b : SA .two (Lam 2 L N)).ab‖ ≤
        u * (KM4 2 Cc * κQ k) := by
    refine (sum_le_sum fun b _ => norm_cfAB4_Q2O_le hCc0 hCc hL P hab k (hKR R P j o' t k)
      (hKl k hk hkn) b (hℓ k)).trans ?_
    rw [← mul_sum]
    set S := ∑ b ∈ blockIdx (L := L) (N := N) k,
        ∑ X ∈ (smallSets k).filter (fun X => blockSet k b ⊆ X),
          (Tj 2 (L : ℝ) k (ℓ k) (hKR R P j o' t k X : SA .two (Lam 2 L N)).ab).toReal with hSd
    have hsum0 : 0 ≤ S := sum_nonneg fun _ _ => sum_nonneg fun _ _ => ENNReal.toReal_nonneg
    have e2 : KM4 2 Cc * (ℓ k)⁻¹ ^ 4 * (((L : ℝ) ^ k) ^ 2 / s ^ 2) * S =
        KM4 2 Cc * ((ℓ k)⁻¹ ^ 4 * (((L : ℝ) ^ k) ^ 2 / s ^ 2)) * S := by ring
    rw [e2]
    calc KM4 2 Cc * ((ℓ k)⁻¹ ^ 4 * (((L : ℝ) ^ k) ^ 2 / s ^ 2)) * S
        ≤ KM4 2 Cc * u * κQ k :=
          mul_le_mul (mul_le_mul_of_nonneg_left hQu hK) (hκQ k hk hkn) hsum0
            (mul_nonneg hK hu0)
      _ = u * (KM4 2 Cc * κQ k) := by ring
  have hS : ∑ b ∈ blockIdx (L := L) (N := N) k,
      ‖cfAB4 P.a P.b (LSO P k (histCovO R t k) (hVR R P j o' t k) (hWR R P j o' t k) b :
        SA .two (Lam 2 L N)).ab‖ ≤ u * (KM4 2 Cc * κS k) := by
    refine (sum_le_sum fun b hb => norm_cfAB4_LSO_le hCc0 hCc hL P hab (by omega) _ _ _ hb
      (hSl k hk hkn b hb) (hℓ (k + 1))).trans ?_
    rw [← mul_sum]
    have e3 : ∀ T : ℝ, KM4 2 Cc * (ℓ (k + 1))⁻¹ ^ 4 * (((L : ℝ) ^ (k + 1)) ^ 2 / s ^ 2) * T =
        KM4 2 Cc * u * T := fun T => by rw [hu]; ring
    rw [e3]
    calc KM4 2 Cc * u * _ ≤ KM4 2 Cc * u * κS k :=
          mul_le_mul_of_nonneg_left (hκS k hk hkn) (mul_nonneg hK hu0)
      _ = u * (KM4 2 Cc * κS k) := by ring
  calc _ ≤ u * (KM4 2 Cc * κQ k) + u * (KM4 2 Cc * κS k) := add_le_add hQ hS
    _ = u * (KM4 2 Cc * (κQ k + κS k)) := by ring

/-! ### Regions and blocks -/

/-- **The `M₄` step of a region along the reduced history.** -/
theorem m4X_hVR_succ (h0 : ObsVabInv P o') {k : ℕ} (hk : j ≤ k)
    (hs : ObsSymInv k (obsHistFrom R P j o' k t)) {X : Finset (Lam 2 L N)}
    (hX : IsPolymer (k + 1) X) :
    m4X P (k + 1) (hVR R P j o' t (k + 1)) X = m4X P k (hVR R P j o' t k) X -
      ∑ b ∈ blocks k X, cfAB4 P.a P.b (Q2O P k (hKR R P j o' t k) b : SA .two (Lam 2 L N)).ab -
      ∑ b ∈ blocks k X,
        cfAB4 P.a P.b (LSO P k (histCovO R t k) (hVR R P j o' t k) (hWR R P j o' t k) b :
          SA .two (Lam 2 L N)).ab := by
  have e : m4X P (k + 1) (hVR R P j o' t (k + 1)) X =
      m4X P (k + 1) (Vnext2O P k (histCovO R t k) (hVR R P j o' t k) (hWR R P j o' t k)
        (hKR R P j o' t k)) X := by
    unfold m4X
    exact sum_congr rfl fun c _ => by rw [hVR_succ_ab hk]
  rw [e, m4X_succ P k _ _ _ _ hX (hVR_ab_mem R P j o' t h0 k) (hVR_ab_sym R P j o' t hs)]

theorem m4X_hVR_start (hz : ∀ b, (o'.V b : SA .two (Lam 2 L N)).ab = 0) (X : Finset (Lam 2 L N)) :
    m4X P j (hVR R P j o' t j) X = 0 := by
  unfold m4X
  refine sum_eq_zero fun b _ => ?_
  rw [hVR_ab, obsHistFrom_self, hz]
  exact coeff_zero _

/-- The region sources of step `i`. -/
def m4SrcX (i : ℕ) (X : Finset (Lam 2 L N)) : ℝ :=
  ∑ b ∈ blocks i X, ‖cfAB4 P.a P.b (Q2O P i (hKR R P j o' t i) b : SA .two (Lam 2 L N)).ab‖ +
    ∑ b ∈ blocks i X,
      ‖cfAB4 P.a P.b (LSO P i (histCovO R t i) (hVR R P j o' t i) (hWR R P j o' t i) b :
        SA .two (Lam 2 L N)).ab‖

/-- **`|M₄_k(X)| ≤ ∑_{j≤i<k}` (region sources of step `i`)**. -/
theorem m4X_hVR_le (h0 : ObsVabInv P o') (hz : ∀ b, (o'.V b : SA .two (Lam 2 L N)).ab = 0)
    {k : ℕ} (hs : ∀ i, j ≤ i → i < k → ObsSymInv i (obsHistFrom R P j o' i t))
    {X : Finset (Lam 2 L N)} (hX : ∀ i, j ≤ i → i < k → IsPolymer (i + 1) X) (hjk : j ≤ k) :
    ‖m4X P k (hVR R P j o' t k) X‖ ≤ ∑ i ∈ Finset.Ico j k, m4SrcX R P j o' t i X := by
  refine m4_norm_le_sum (M := fun i => m4X P i (hVR R P j o' t i) X) (n := k)
    (m4X_hVR_start R P j o' t hz X) _ (fun i hi hik => ?_) k hjk le_rfl
  show ‖m4X P (i + 1) (hVR R P j o' t (i + 1)) X - m4X P i (hVR R P j o' t i) X‖ ≤ _
  rw [m4X_hVR_succ R P j o' t h0 hi (hs i hi hik) (hX i hi hik)]
  have e : ∀ x y z : ℂ, x - y - z - x = -(y + z) := fun x y z => by ring
  rw [e, norm_neg]
  exact (norm_add_le _ _).trans (add_le_add (norm_sum_le _ _) (norm_sum_le _ _))

/-- **The per-block quartic coefficient**: for a `k`-block `B`, `|M₄(V'_k(B)_{ab})|` is bounded by
the sources of the steps `j ≤ i < k` in the fixed region `B`. -/
theorem cfAB4_hVR_block_le (h0 : ObsVabInv P o') (hz : ∀ b, (o'.V b : SA .two (Lam 2 L N)).ab = 0)
    {k : ℕ} (hs : ∀ i, j ≤ i → i < k → ObsSymInv i (obsHistFrom R P j o' i t)) (hjk : j ≤ k)
    {c : Fin 2 → ℕ} (hne : (blockSet (L := L) (N := N) k c).Nonempty) :
    ‖cfAB4 P.a P.b (hVR R P j o' t k c : SA .two (Lam 2 L N)).ab‖ ≤
      ∑ i ∈ Finset.Ico j k, m4SrcX R P j o' t i (blockSet (L := L) (N := N) k c) := by
  rw [← m4X_blockSet P k _ hne]
  exact m4X_hVR_le R P j o' t h0 hz hs
    (fun i _ hik => isPolymer_of_le (isPolymer_blockSet k c) (i + 1) (by omega)) hjk

/-- **The per-block quartic coefficient from the norms of the region sources**:
`|M₄(V'_k(B))| ≤ K_{M4}∑_{j≤i<k}(ℓ_i^{-4}(L^i/s)²κ^Q_i + ℓ_{i+1}^{-4}(L^{i+1}/s)²κ^S_i)`,
`s = |a − b|_∞`, `κ^Q_i ≥ ∑_{B'∈𝓑_i(B)}∑_{X⊇B'}‖K_i(X)_{ab}‖`, `κ^S_i ≥ ∑_{B'∈𝓑_i(B)}‖S_i(B'_+)_{ab}‖`. -/
theorem cfAB4_hVR_block_sizes {Cc : ℝ} (hCc0 : 0 ≤ Cc)
    (hCc : ∀ m : Fin 2 → ℕ, (∀ i, m i ≤ 1) → ∀ R : ℝ, 1 ≤ R → ∀ α : Dir 2 → ℕ,
      Grassmann.mabs α ≤ pPhi 2 → ∀ u : Zd 2,
      |D1 (fun b v => b +ᵥ v) α (cutP m R) u| ≤ Cc * R ^ (∑ i, m i) / R ^ Grassmann.mabs α)
    (hL : 2 ^ (2 + 3) + 8 * 2 < L) (hab : P.a ≠ P.b) (h0 : ObsVabInv P o')
    (hz : ∀ b, (o'.V b : SA .two (Lam 2 L N)).ab = 0)
    {k : ℕ} (hkN : k + 1 ≤ N) (hs : ∀ i, j ≤ i → i < k → ObsSymInv i (obsHistFrom R P j o' i t))
    (hjk : j ≤ k) {c : Fin 2 → ℕ} (hne : (blockSet (L := L) (N := N) k c).Nonempty)
    (ℓ : ℕ → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (hKl : ∀ i, j ≤ i → i < k → ∀ X, IsSmall i X →
      (hKR R P j o' t i X : SA .two (Lam 2 L N)).ab ∈ NX (nbhd i X : Set (Lam 2 L N)))
    (hSl : ∀ i, j ≤ i → i < k → ∀ b ∈ blockIdx (L := L) (N := N) i,
      (SXO i (histCovO R t i) (hVR R P j o' t i) (hWR R P j o' t i)
        (Step2.Bp (L := L) (N := N) i b) : SA .two (Lam 2 L N)).ab ∈
        NX (nbhd (i + 1) (Step2.Bp (L := L) (N := N) i b) : Set (Lam 2 L N)))
    (κQ κS : ℕ → ℝ)
    (hκQ : ∀ i, j ≤ i → i < k →
      (open Classical in ∑ b ∈ blocks i (blockSet (L := L) (N := N) k c),
        ∑ X ∈ (smallSets i).filter (fun X => blockSet i b ⊆ X),
          (Tj 2 (L : ℝ) i (ℓ i) (hKR R P j o' t i X : SA .two (Lam 2 L N)).ab).toReal) ≤ κQ i)
    (hκS : ∀ i, j ≤ i → i < k →
      ∑ b ∈ blocks i (blockSet (L := L) (N := N) k c),
        (Tj 2 (L : ℝ) (i + 1) (ℓ (i + 1))
          (SXO i (histCovO R t i) (hVR R P j o' t i) (hWR R P j o' t i)
            (Step2.Bp (L := L) (N := N) i b) : SA .two (Lam 2 L N)).ab).toReal ≤ κS i) :
    ‖cfAB4 P.a P.b (hVR R P j o' t k c : SA .two (Lam 2 L N)).ab‖ ≤
      ∑ i ∈ Finset.Ico j k, KM4 2 Cc *
        ((ℓ i)⁻¹ ^ 4 * (((L : ℝ) ^ i) ^ 2 / ((supNorm (P.a - P.b) : ℕ) : ℝ) ^ 2) * κQ i +
          (ℓ (i + 1))⁻¹ ^ 4 * (((L : ℝ) ^ (i + 1)) ^ 2 / ((supNorm (P.a - P.b) : ℕ) : ℝ) ^ 2) *
            κS i) := by
  classical
  refine (cfAB4_hVR_block_le R P j o' t h0 hz hs hjk hne).trans
    (sum_le_sum fun i hi => ?_)
  obtain ⟨hji, hik⟩ := Finset.mem_Ico.1 hi
  have hK := KM4_nonneg 2 (Cc := Cc)
  set s : ℝ := ((supNorm (P.a - P.b) : ℕ) : ℝ)
  have hbI : ∀ b ∈ blocks i (blockSet (L := L) (N := N) k c), b ∈ blockIdx (L := L) (N := N) i :=
    fun b hb => mem_blockIdx_of_mem_blocks hb
  have hQ : ∑ b ∈ blocks i (blockSet (L := L) (N := N) k c),
      ‖cfAB4 P.a P.b (Q2O P i (hKR R P j o' t i) b : SA .two (Lam 2 L N)).ab‖ ≤
        KM4 2 Cc * ((ℓ i)⁻¹ ^ 4 * (((L : ℝ) ^ i) ^ 2 / s ^ 2) * κQ i) := by
    refine (sum_le_sum fun b _ => norm_cfAB4_Q2O_le hCc0 hCc hL P hab i (hKR R P j o' t i)
      (hKl i hji hik) b (hℓ i)).trans ?_
    rw [← mul_sum]
    have hu : 0 ≤ KM4 2 Cc * (ℓ i)⁻¹ ^ 4 * (((L : ℝ) ^ i) ^ 2 / s ^ 2) := by
      have := hℓ i; positivity
    calc _ ≤ KM4 2 Cc * (ℓ i)⁻¹ ^ 4 * (((L : ℝ) ^ i) ^ 2 / s ^ 2) * κQ i :=
          mul_le_mul_of_nonneg_left (hκQ i hji hik) hu
      _ = _ := by ring
  have hS : ∑ b ∈ blocks i (blockSet (L := L) (N := N) k c),
      ‖cfAB4 P.a P.b (LSO P i (histCovO R t i) (hVR R P j o' t i) (hWR R P j o' t i) b :
        SA .two (Lam 2 L N)).ab‖ ≤
        KM4 2 Cc * ((ℓ (i + 1))⁻¹ ^ 4 * (((L : ℝ) ^ (i + 1)) ^ 2 / s ^ 2) * κS i) := by
    refine (sum_le_sum fun b hb => norm_cfAB4_LSO_le hCc0 hCc hL P hab (by omega) _ _ _ (hbI b hb)
      (hSl i hji hik b (hbI b hb)) (hℓ (i + 1))).trans ?_
    rw [← mul_sum]
    have hu : 0 ≤ KM4 2 Cc * (ℓ (i + 1))⁻¹ ^ 4 * (((L : ℝ) ^ (i + 1)) ^ 2 / s ^ 2) := by
      have := hℓ (i + 1); positivity
    calc _ ≤ KM4 2 Cc * (ℓ (i + 1))⁻¹ ^ 4 * (((L : ℝ) ^ (i + 1)) ^ 2 / s ^ 2) * κS i :=
          mul_le_mul_of_nonneg_left (hκS i hji hik) hu
      _ = _ := by ring
  unfold m4SrcX
  calc _ ≤ KM4 2 Cc * ((ℓ i)⁻¹ ^ 4 * (((L : ℝ) ^ i) ^ 2 / s ^ 2) * κQ i) +
        KM4 2 Cc * ((ℓ (i + 1))⁻¹ ^ 4 * (((L : ℝ) ^ (i + 1)) ^ 2 / s ^ 2) * κS i) :=
        add_le_add hQ hS
    _ = _ := by ring

end Hist

end

end PtCorr2
