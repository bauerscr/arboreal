import PtCorr2.Pair.VObsStepAB2
import PtCorr2.Pair.GradABHist1
import Obs2.Flow.GradAB3

/-!
# The gradient coefficients of `V'_{ab}` along the reduced history: regions and blocks

The gradient part of `V'_k(B)_{ab}` (seen from `a`) is followed through the region sums over a fixed
region `X` (as `m4X` for `M₄`): for an `(i+1)`-polymer `X` the coefficients of
`∑_{B∈𝓑_{i+1}(X)}V'_{i+1}(B)` are those of `∑_{B∈𝓑_i(X)}V'^{next}_i(B)` (`cf2X_succ`, `m4X_succ`).
A `k`-block is an `(i+1)`-polymer for all `i < k`, so its gradient size is bounded by the sources of
all earlier steps restricted to the block, each contracted by `L^{-1}` per step (`gSzE_scale_le`).
Mergers need no bookkeeping: a localisation based at `b` enters with its mass seen from `a`
(`Obs2.gSzE_locABtX_le`).

* `gX` (the region sum), **`gSzE_gX_succ_le`** (one step of a region, fixed `(h, ℓ)`);
* **`gSzE_gX_flow_le`**: with `Γ_i = gSzE_{L^i,ℓ_i}(gX_i(X))`, `Γ_j = 0`, `ℓ_{i+1} ≤ ℓ_i`:
  `Γ_k ≤ ∑_{j≤i<k}L^{-(k-1-i)}σ_i`, `σ_i` the step-`i` sources measured at scale `i+1`;
* **`gSzE_hVR_block_le`**: the same for a `k`-block (`gX_k(B) = V'_k(B)_{ab}`);
* `gradM4Sz_le_gSzE` (for the `hγ` input of `hVo_of_coeffs`).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD Obs2 Flow2 Flow2.Hist LocObs

variable {L N : ℕ} [NeZero L]

/-- **A linear recursion with contraction** (pure): `x_j = 0`, `x_{i+1} ≤ qx_i + σ_i` give
`x_k ≤ ∑_{j≤i<k}q^{k-1-i}σ_i`. -/
theorem geom_rec_le {x σ : ℕ → ℝ} {q : ℝ} (hq : 0 ≤ q) {j : ℕ} (h0 : x j ≤ 0)
    (hs : ∀ i, j ≤ i → x (i + 1) ≤ q * x i + σ i) :
    ∀ k, j ≤ k → x k ≤ ∑ i ∈ Finset.Ico j k, q ^ (k - 1 - i) * σ i := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => simpa using h0
  | succ k hk ih =>
    refine (hs k hk).trans ?_
    rw [Finset.sum_Ico_succ_top hk]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
    refine add_le_add ((mul_le_mul_of_nonneg_left ih hq).trans (le_of_eq ?_)) le_rfl
    rw [mul_sum]
    refine sum_congr rfl fun i hi => ?_
    have := (Finset.mem_Ico.1 hi).2
    rw [← mul_assoc, ← pow_succ', show k - 1 - i + 1 = k - i by omega]

/-- `gradM4Sz` is `gSzE` with `E = |e_X|₁`; monotone in `E`. -/
theorem gradM4Sz_le_gSzE (X : Finset (Lam 2 L N)) (a b : Lam 2 L N) {E h ℓ : ℝ}
    (hXE : eN1 X a b ≤ E) (hh : 0 ≤ h) (hℓ : 0 ≤ ℓ) (F : Alg 2 L N) :
    gradM4Sz X a b h ℓ F ≤ gSzE E a b h ℓ F :=
  gSzE_mono_E (eN1_nonneg X a b) hXE hh hℓ a b F

section Hist

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N) (j : ℕ)
  (o' : ObsSt .two L N) (t : Hist.Seq (Xs R))

/-- The `ab` part of `V'_k` summed over the `k`-blocks of a region. -/
def gX (k : ℕ) (X : Finset (Lam 2 L N)) : Alg 2 L N :=
  ∑ b ∈ blocks k X, (hVR R P j o' t k b : SA .two (Lam 2 L N)).ab

theorem gX_blockSet (k : ℕ) {c : Fin 2 → ℕ} (hne : (blockSet (L := L) (N := N) k c).Nonempty) :
    gX R P j o' t k (blockSet (L := L) (N := N) k c) = (hVR R P j o' t k c : SA .two (Lam 2 L N)).ab := by
  rw [gX, blocks_blockSet_self hne, sum_singleton]

theorem gX_start (hz : ∀ b, (o'.V b : SA .two (Lam 2 L N)).ab = 0) (X : Finset (Lam 2 L N)) :
    gX R P j o' t j X = 0 := by
  unfold gX
  refine sum_eq_zero fun b _ => ?_
  rw [hVR_ab, obsHistFrom_self, hz]

/-- The sources of step `k` in the region `X`, measured with `(h, ℓ)`. -/
def gSrcX (E h ℓ : ℝ) (k : ℕ) (X : Finset (Lam 2 L N)) : ℝ :=
  (‖m4X P k (hVR R P j o' t k) X‖ +
      ‖∑ b ∈ blocks k X, cfAB4 P.a P.b (Q2O P k (hKR R P j o' t k) b : SA .two (Lam 2 L N)).ab‖) *
      gSzE E P.a P.b h ℓ (LopM4 (histCovO R t k) P.a P.b) +
    ∑ b ∈ blocks k X, gSzE E P.a P.b h ℓ (Q2O P k (hKR R P j o' t k) b : SA .two (Lam 2 L N)).ab +
    ∑ b ∈ blocks k X, gSzE E P.a P.b h ℓ
      (LSO P k (histCovO R t k) (hVR R P j o' t k) (hWR R P j o' t k) b : SA .two (Lam 2 L N)).ab

/-- **One step of the gradient coefficients of a region** (`X` a `(k+1)`-polymer). -/
theorem gSzE_gX_succ_le (h0 : ObsVabInv P o') {k : ℕ} (hk : j ≤ k)
    (hs : ObsSymInv k (obsHistFrom R P j o' k t)) {X : Finset (Lam 2 L N)}
    (hX : IsPolymer (k + 1) X) {E h ℓ : ℝ} (hE : 0 ≤ E) (hh : 0 ≤ h) (hℓ : 0 ≤ ℓ) :
    gSzE E P.a P.b h ℓ (gX R P j o' t (k + 1) X) ≤
      gSzE E P.a P.b h ℓ (gX R P j o' t k X) + gSrcX R P j o' t E h ℓ k X := by
  set C := histCovO R t k
  set G := LopM4 C P.a P.b
  set SQ : Alg 2 L N := ∑ b ∈ blocks k X, (Q2O P k (hKR R P j o' t k) b : SA .two (Lam 2 L N)).ab
  set SS : Alg 2 L N := ∑ b ∈ blocks k X,
    (LSO P k C (hVR R P j o' t k) (hWR R P j o' t k) b : SA .two (Lam 2 L N)).ab
  set H : Alg 2 L N := gX R P j o' t k X + m4X P k (hVR R P j o' t k) X • G -
    (SQ + (∑ b ∈ blocks k X, cfAB4 P.a P.b (Q2O P k (hKR R P j o' t k) b :
      SA .two (Lam 2 L N)).ab) • G) - SS
  have hmem := hVR_ab_mem R P j o' t h0 k
  have hsym := hVR_ab_sym R P j o' t hs
  have eV : ∀ c', (hVR R P j o' t (k + 1) c' : SA .two (Lam 2 L N)).ab =
      (Vnext2O P k C (hVR R P j o' t k) (hWR R P j o' t k) (hKR R P j o' t k) c' :
        SA .two (Lam 2 L N)).ab := fun c' => hVR_succ_ab hk c'
  have hc : ∀ {u v : Lam 2 L N}, (u = P.a ∨ u = P.b) → (v = P.a ∨ v = P.b) →
      cfAB2 u v (gX R P j o' t (k + 1) X) = cfAB2 u v H := by
    intro u v hu hv
    have e1 : cfAB2 u v (gX R P j o' t (k + 1) X) =
        cf2X u v (k + 1) (Vnext2O P k C (hVR R P j o' t k) (hWR R P j o' t k)
          (hKR R P j o' t k)) X := by
      rw [gX, cfAB2_sum_eq, cf2X]
      exact sum_congr rfl fun c' _ => by rw [eV c']
    rw [e1, cf2X_succ P k _ _ _ _ hX hmem hsym hu hv]
    simp only [H, SQ, SS, G, gX, cf2X, cfAB2_sub, cfAB2_add, cfAB2_smul, cfAB2_sum_eq]
  have h4 : cfAB4 P.a P.b (gX R P j o' t (k + 1) X) = cfAB4 P.a P.b H := by
    have e1 : cfAB4 P.a P.b (gX R P j o' t (k + 1) X) =
        m4X P (k + 1) (Vnext2O P k C (hVR R P j o' t k) (hWR R P j o' t k)
          (hKR R P j o' t k)) X := by
      rw [gX, cfAB4_sum_eq, m4X]
      exact sum_congr rfl fun c' _ => by rw [eV c']
    rw [e1, m4X_succ P k _ _ _ _ hX hmem hsym]
    simp only [H, SQ, SS, G, gX, m4X, cfAB4_sub, cfAB4_add, cfAB4_smul, cfAB4_sum_eq,
      cfAB4_LopM4, mul_zero, add_zero]
  rw [gSzE_congr (hc (Or.inl rfl) (Or.inr rfl)) (hc (Or.inr rfl) (Or.inl rfl))
    (hc (Or.inr rfl) (Or.inr rfl)) h4]
  have s1 := gSzE_sub_le hE hh hℓ P.a P.b (gX R P j o' t k X + m4X P k (hVR R P j o' t k) X • G -
    (SQ + (∑ b ∈ blocks k X, cfAB4 P.a P.b (Q2O P k (hKR R P j o' t k) b :
      SA .two (Lam 2 L N)).ab) • G)) SS
  have s2 := gSzE_sub_le hE hh hℓ P.a P.b (gX R P j o' t k X + m4X P k (hVR R P j o' t k) X • G)
    (SQ + (∑ b ∈ blocks k X, cfAB4 P.a P.b (Q2O P k (hKR R P j o' t k) b :
      SA .two (Lam 2 L N)).ab) • G)
  have s3 := gSzE_add_le hE hh hℓ P.a P.b (gX R P j o' t k X) (m4X P k (hVR R P j o' t k) X • G)
  have s4 := gSzE_add_le hE hh hℓ P.a P.b SQ ((∑ b ∈ blocks k X, cfAB4 P.a P.b
    (Q2O P k (hKR R P j o' t k) b : SA .two (Lam 2 L N)).ab) • G)
  have s5 := gSzE_sum_le hE hh hℓ (blocks k X)
    (fun b => (Q2O P k (hKR R P j o' t k) b : SA .two (Lam 2 L N)).ab) P.a P.b
  have s6 := gSzE_sum_le hE hh hℓ (blocks k X)
    (fun b => (LSO P k C (hVR R P j o' t k) (hWR R P j o' t k) b : SA .two (Lam 2 L N)).ab) P.a P.b
  rw [gSzE_smul hE hh hℓ] at s3 s4
  unfold gSrcX
  simp only [SQ, SS] at s4 s5 s6 s1 s2
  linarith

/-- **The gradient coefficients of a region along the history**: with the scale-`(i+1)` sources
`σ_i`, `Γ_k = gSzE_{L^k,ℓ_k}(gX_k(X)) ≤ ∑_{j≤i<k}L^{-(k-1-i)}σ_i`. -/
theorem gSzE_gX_flow_le (h0 : ObsVabInv P o') (hz : ∀ b, (o'.V b : SA .two (Lam 2 L N)).ab = 0)
    {k : ℕ} (hs : ∀ i, j ≤ i → i < k → ObsSymInv i (obsHistFrom R P j o' i t))
    {X : Finset (Lam 2 L N)} (hX : ∀ i, j ≤ i → i < k → IsPolymer (i + 1) X) (hjk : j ≤ k)
    {E : ℝ} (hE : 0 ≤ E) (ℓ : ℕ → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (hℓm : ∀ i, j ≤ i → i < k → ℓ (i + 1) ≤ ℓ i) :
    gSzE E P.a P.b ((L : ℝ) ^ k) (ℓ k) (gX R P j o' t k X) ≤
      ∑ i ∈ Finset.Ico j k, ((L : ℝ)⁻¹) ^ (k - 1 - i) *
        gSrcX R P j o' t E ((L : ℝ) ^ (i + 1)) (ℓ (i + 1)) i X := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hL0 : (0 : ℝ) < L := by linarith
  -- truncate the recursion at `k`
  set x : ℕ → ℝ := fun i => if i ≤ k then
    gSzE E P.a P.b ((L : ℝ) ^ i) (ℓ i) (gX R P j o' t i X) else 0 with hx
  set σ : ℕ → ℝ := fun i => if i < k then
    gSrcX R P j o' t E ((L : ℝ) ^ (i + 1)) (ℓ (i + 1)) i X else 0 with hσ
  have hσ0 : ∀ i, j ≤ i → i < k → 0 ≤ gSrcX R P j o' t E ((L : ℝ) ^ (i + 1)) (ℓ (i + 1)) i X := by
    intro i _ _
    have hh : (0 : ℝ) ≤ (L : ℝ) ^ (i + 1) := by positivity
    have hl : 0 ≤ ℓ (i + 1) := (hℓ _).le
    unfold gSrcX
    have := mul_nonneg (add_nonneg (norm_nonneg (m4X P i (hVR R P j o' t i) X))
      (norm_nonneg (∑ b ∈ blocks i X, cfAB4 P.a P.b (Q2O P i (hKR R P j o' t i) b :
        SA .two (Lam 2 L N)).ab))) (gSzE_nonneg hE hh hl P.a P.b (LopM4 (histCovO R t i) P.a P.b))
    have := sum_nonneg fun b (_ : b ∈ blocks i X) => gSzE_nonneg hE hh hl P.a P.b
      (Q2O P i (hKR R P j o' t i) b : SA .two (Lam 2 L N)).ab
    have := sum_nonneg fun b (_ : b ∈ blocks i X) => gSzE_nonneg hE hh hl P.a P.b
      (LSO P i (histCovO R t i) (hVR R P j o' t i) (hWR R P j o' t i) b : SA .two (Lam 2 L N)).ab
    linarith
  have hrec := geom_rec_le (x := x) (σ := σ) (q := (L : ℝ)⁻¹) (by positivity) (j := j)
    (by simp only [hx, if_pos hjk, gX_start R P j o' t hz, gSzE_zero, le_refl])
    (fun i hi => by
      rcases Nat.lt_or_ge i k with hik | hik
      · simp only [hx, hσ, if_pos hik, if_pos hik.le, if_pos (show i + 1 ≤ k by omega)]
        have hh : (0 : ℝ) < (L : ℝ) ^ i := pow_pos hL0 i
        have step := gSzE_gX_succ_le R P j o' t h0 hi (hs i hi hik) (hX i hi hik) hE
          (by positivity : (0 : ℝ) ≤ (L : ℝ) ^ (i + 1)) (hℓ (i + 1)).le
        have sc := gSzE_scale_le hE hh (pow_le_pow_right₀ hL1 (Nat.le_succ i))
          (hℓ (i + 1)).le (hℓm i hi hik) P.a P.b (gX R P j o' t i X)
        have e : (L : ℝ) ^ i * ((L : ℝ) ^ (i + 1))⁻¹ = (L : ℝ)⁻¹ := by
          rw [pow_succ, mul_inv, ← mul_assoc, mul_inv_cancel₀ hh.ne', one_mul]
        rw [e] at sc
        linarith
      · have h1 : ¬ i + 1 ≤ k := by omega
        simp only [hx, hσ, if_neg h1, if_neg (show ¬ i < k by omega)]
        rcases Nat.lt_or_ge k i with hki | hki
        · simp only [if_neg (show ¬ i ≤ k by omega), mul_zero, add_zero, le_refl]
        · obtain rfl : i = k := by omega
          simp only [le_refl, if_true, add_zero]
          exact mul_nonneg (by positivity) (gSzE_nonneg hE (by positivity) (hℓ _).le _ _ _))
    k hjk
  simp only [hx, le_refl, if_true] at hrec
  refine hrec.trans (le_of_eq (sum_congr rfl fun i hi => ?_))
  simp only [hσ, if_pos (Finset.mem_Ico.1 hi).2]

/-- **The gradient coefficients of a `k`-block along the history.** -/
theorem gSzE_hVR_block_le (h0 : ObsVabInv P o') (hz : ∀ b, (o'.V b : SA .two (Lam 2 L N)).ab = 0)
    {k : ℕ} (hs : ∀ i, j ≤ i → i < k → ObsSymInv i (obsHistFrom R P j o' i t)) (hjk : j ≤ k)
    {c : Fin 2 → ℕ} (hne : (blockSet (L := L) (N := N) k c).Nonempty)
    {E : ℝ} (hE : 0 ≤ E) (ℓ : ℕ → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (hℓm : ∀ i, j ≤ i → i < k → ℓ (i + 1) ≤ ℓ i) :
    gSzE E P.a P.b ((L : ℝ) ^ k) (ℓ k) (hVR R P j o' t k c : SA .two (Lam 2 L N)).ab ≤
      ∑ i ∈ Finset.Ico j k, ((L : ℝ)⁻¹) ^ (k - 1 - i) *
        gSrcX R P j o' t E ((L : ℝ) ^ (i + 1)) (ℓ (i + 1)) i (blockSet (L := L) (N := N) k c) := by
  rw [← gX_blockSet R P j o' t k hne]
  exact gSzE_gX_flow_le R P j o' t h0 hz hs
    (fun i _ hik => isPolymer_of_le (isPolymer_blockSet k c) (i + 1) (by omega)) hjk hE ℓ hℓ hℓm

/-- **The sources of one step from the norms of `K` and `S`** (scale-`(i+1)` weights
`h = L^{i+1}`, `ℓ' ≤ 2ℓ_i`, `ℓ' ≤ 2ℓ_{i+1}`): with `g = Eℓ'/L^{i+1}`,
`σ_i ≤ (|M₄(X)| + |∑M₄(Q)|)gSzE(ℒ_Cm₄) + B^Q_iκ^Q_i + B^S_iκ^S_i`,
`B^Q_i = (1+η)K_G/L + ℓ_i^{-2}(2ℓ'g + g²)`, `B^S_i = (1+η)K_G + ℓ_{i+1}^{-2}(2ℓ'g + g²)`. -/
theorem gSrcX_le {Cc : ℝ} (hCc0 : 0 ≤ Cc)
    (hCc : ∀ m : Fin 2 → ℕ, (∀ i, m i ≤ 1) → ∀ R : ℝ, 1 ≤ R → ∀ α : Dir 2 → ℕ,
      Grassmann.mabs α ≤ pPhi 2 → ∀ u : Zd 2,
      |D1 (fun b v => b +ᵥ v) α (cutP m R) u| ≤ Cc * R ^ (∑ i, m i) / R ^ Grassmann.mabs α)
    (hL : 2 ^ (2 + 3) + 8 * 2 < L) (hab : P.a ≠ P.b) {E κ η : ℝ} (hE : 0 ≤ E) (hκ : 0 ≤ κ)
    (hEκ : ∀ X : Finset (Lam 2 L N), E * eN1 X P.a P.b ≤ κ * eN2 X P.a P.b)
    {i : ℕ} (hiN : i + 1 < N) (X : Finset (Lam 2 L N)) {ℓi ℓi1 ℓ' : ℝ} (hℓi : 0 < ℓi)
    (hℓi1 : 0 < ℓi1) (hℓ' : 0 ≤ ℓ') (hℓ'i : ℓ' ≤ 2 * ℓi) (hℓ'i1 : ℓ' ≤ 2 * ℓi1)
    (hη : E * ((L : ℝ) ^ (i + 1))⁻¹ ≤ η)
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
    gSrcX R P j o' t E ((L : ℝ) ^ (i + 1)) ℓ' i X ≤
      (‖m4X P i (hVR R P j o' t i) X‖ +
          ‖∑ b ∈ blocks i X, cfAB4 P.a P.b (Q2O P i (hKR R P j o' t i) b :
            SA .two (Lam 2 L N)).ab‖) *
          gSzE E P.a P.b ((L : ℝ) ^ (i + 1)) ℓ' (LopM4 (histCovO R t i) P.a P.b) +
        ((1 + η) * (KG 2 Cc κ * ((L : ℝ) ^ i * ((L : ℝ) ^ (i + 1))⁻¹)) +
          ℓi⁻¹ ^ 2 * (2 * (ℓ' * (E * ℓ' * ((L : ℝ) ^ (i + 1))⁻¹)) +
            (E * ℓ' * ((L : ℝ) ^ (i + 1))⁻¹) * (E * ℓ' * ((L : ℝ) ^ (i + 1))⁻¹))) * κQ +
        ((1 + η) * (KG 2 Cc κ * ((L : ℝ) ^ (i + 1) * ((L : ℝ) ^ (i + 1))⁻¹)) +
          ℓi1⁻¹ ^ 2 * (2 * (ℓ' * (E * ℓ' * ((L : ℝ) ^ (i + 1))⁻¹)) +
            (E * ℓ' * ((L : ℝ) ^ (i + 1))⁻¹) * (E * ℓ' * ((L : ℝ) ^ (i + 1))⁻¹))) * κS := by
  classical
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hh : (0 : ℝ) < (L : ℝ) ^ (i + 1) := pow_pos (by linarith) _
  have hsh : (L : ℝ) ^ i ≤ (L : ℝ) ^ (i + 1) := pow_le_pow_right₀ hL1 (Nat.le_succ i)
  have hη0 : 0 ≤ η := (by positivity : (0 : ℝ) ≤ E * ((L : ℝ) ^ (i + 1))⁻¹).trans hη
  have hg0 : 0 ≤ E * ℓ' * ((L : ℝ) ^ (i + 1))⁻¹ := by positivity
  have hP0 : 0 ≤ 2 * (ℓ' * (E * ℓ' * ((L : ℝ) ^ (i + 1))⁻¹)) +
      (E * ℓ' * ((L : ℝ) ^ (i + 1))⁻¹) * (E * ℓ' * ((L : ℝ) ^ (i + 1))⁻¹) := by
    have := mul_nonneg hℓ' hg0; have := mul_nonneg hg0 hg0; linarith
  have hKG := KG_nonneg 2 (Cc := Cc) hκ
  have hbI : ∀ b ∈ blocks i X, b ∈ blockIdx (L := L) (N := N) i :=
    fun b hb => mem_blockIdx_of_mem_blocks hb
  set BQ := (1 + η) * (KG 2 Cc κ * ((L : ℝ) ^ i * ((L : ℝ) ^ (i + 1))⁻¹)) +
          ℓi⁻¹ ^ 2 * (2 * (ℓ' * (E * ℓ' * ((L : ℝ) ^ (i + 1))⁻¹)) +
            (E * ℓ' * ((L : ℝ) ^ (i + 1))⁻¹) * (E * ℓ' * ((L : ℝ) ^ (i + 1))⁻¹)) with hBQ
  set BS := (1 + η) * (KG 2 Cc κ * ((L : ℝ) ^ (i + 1) * ((L : ℝ) ^ (i + 1))⁻¹)) +
          ℓi1⁻¹ ^ 2 * (2 * (ℓ' * (E * ℓ' * ((L : ℝ) ^ (i + 1))⁻¹)) +
            (E * ℓ' * ((L : ℝ) ^ (i + 1))⁻¹) * (E * ℓ' * ((L : ℝ) ^ (i + 1))⁻¹)) with hBS
  have hBQ0 : 0 ≤ BQ := by
    have : 0 ≤ (L : ℝ) ^ i * ((L : ℝ) ^ (i + 1))⁻¹ := by positivity
    have : 0 ≤ ℓi⁻¹ ^ 2 := by positivity
    positivity
  have hBS0 : 0 ≤ BS := by
    have : 0 ≤ (L : ℝ) ^ (i + 1) * ((L : ℝ) ^ (i + 1))⁻¹ := by positivity
    have : 0 ≤ ℓi1⁻¹ ^ 2 := by positivity
    positivity
  have hQ : ∑ b ∈ blocks i X, gSzE E P.a P.b ((L : ℝ) ^ (i + 1)) ℓ'
      (Q2O P i (hKR R P j o' t i) b : SA .two (Lam 2 L N)).ab ≤ BQ * κQ := by
    refine (sum_le_sum fun b _ => gSzE_Q2O_le hCc0 hCc hL P hab hE hκ hEκ i (hKR R P j o' t i)
      hKl b hℓi hℓ' hℓ'i hh hsh hη).trans ?_
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left hκQ hBQ0
  have hS : ∑ b ∈ blocks i X, gSzE E P.a P.b ((L : ℝ) ^ (i + 1)) ℓ'
      (LSO P i (histCovO R t i) (hVR R P j o' t i) (hWR R P j o' t i) b :
        SA .two (Lam 2 L N)).ab ≤ BS * κS := by
    refine (sum_le_sum fun b hb => gSzE_LSO_le hCc0 hCc hL P hab hE hκ hEκ hiN _ _ _ (hbI b hb)
      (hSl b (hbI b hb)) hℓi1 hℓ' hℓ'i1 hh le_rfl hη).trans ?_
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left hκS hBS0
  unfold gSrcX
  linarith

end Hist

end

end PtCorr2
