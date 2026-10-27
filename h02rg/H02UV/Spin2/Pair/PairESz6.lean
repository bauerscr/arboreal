import Spin2.Pair.PairESz5
import Spin2.Pair.PairLoop4

/-!
# The `E`-step sizes (6): the explicit per-scale sequences of `PairESizes3`

For the reduced states `oRed … dxStd` along an admissible trajectory of `MasterFacts`, with
`β_k = |β_{a,k}|`, `s_k = histS k`, `ǧ_k`, `r_k = cǧ_k`, `|a − b|_∞ = s_x`, a path of length `|w|`,
and the history sizes `kszQ` (small-set `K`) and `kszS` (`S(B_+)`) of `pairKSSizes_MF`:

* `κ^Q_k = kszQ_k/β_{k+1}` (item 1);
* `μ^Q_i = K_{M4}s_i^{-4}(L^i/s_x)²·2c_Nc_S·kszQ_i/β_{i+1}`,
  `μ^S_i = K_{M4}s_{i+1}^{-4}(L^{i+1}/s_x)²·2L²·kszS_i/β_{i+1}` (the `Q` and `Loc S` halves of
  `m4SrcX_le_sizes`);
* `c_{ν,k} = max(B',0)ǧ_k + c_tǧ_k` (`k < N_h`; `1/8 + c_tǧ_{N_h}` at `N_h`);
* `γ_k = gradRHS(…)_k`, `μ_k = m4RHS(…)_k` (the per-scale gradient and `M₄` sizes of the blocks,
  `MasterCore.vhistG`), `λ_k(ℓ') = 2|w|s_k²L^{-(k+1)}ℓ'(2s_xℓ'L^{-(k+1)}) + s_k²(2s_xℓ'L^{-(k+1)})²`
  (the `LopM4` term);
* `δ_k = 2(4⁴L^{-1}γ_k + μ_kλ_k(4s_k))/β_{k+1}` (item 5, the scale change `T_k(s_k) → T_{k+1}(4s_k)`);
* `e_k = 2(L+39)²·8⁴·r_k` (item 6, the near bulk `V'`);
* `P_i = 2μ_i/β_{i+1}·(|w|s_i/L^{i+1})²`;
* `F_i = 2·δ'_ie'_i/β_{i+1}` with `δ'_i = 2((9/2)⁴L^{-1}γ_i + μ_iλ_i(4s_{i+1}))`,
  `e'_i = 2(L+39)²·9⁴·r_i` (item 9, the bilinear `F_C` bound at `T_{i+1}(4s_{i+1})`).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs2

variable {L N : ℕ} [NeZero L]

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- `|a − b|_∞` of the pair `(0, x)`. -/
def sXp (x : Lam 2 L N) : ℝ := ((supNorm ((ptsX x).a - (ptsX x).b) : ℕ) : ℝ)

/-- Item 1: `κ^Q_k = kszQ_k/β_{k+1}`. -/
def e6KQ (M : MasterFacts L) (C₁k C₁w mbar cu m b μ₀ : ℝ) (lam : ℕ → ℂ) (x : Lam 2 L N)
    (k : ℕ) : ℝ :=
  kszQ R M C₁k C₁w mbar cu m b μ₀ lam x k / ‖hBeta R m b μ₀ x (k + 1)‖

/-- `μ^Q_i`. -/
def e6MQ (M : MasterFacts L) (C₁k C₁w mbar cu m b μ₀ : ℝ) (lam : ℕ → ℂ) (x : Lam 2 L N)
    (i : ℕ) : ℝ :=
  KM4 2 Ccut2 * ((histS (R.withMsq m) i (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))⁻¹ ^ 4 *
    (((L : ℝ) ^ i) ^ 2 / sXp x ^ 2) *
      (2 * (cNb2 : ℝ) * (cSm2 : ℝ) * kszQ R M C₁k C₁w mbar cu m b μ₀ lam x i)) /
    ‖hBeta R m b μ₀ x (i + 1)‖

/-- `μ^S_i`. -/
def e6MS (M : MasterFacts L) (C₁w mbar m b μ₀ : ℝ) (lam : ℕ → ℂ) (x : Lam 2 L N) (i : ℕ) : ℝ :=
  KM4 2 Ccut2 * ((histS (R.withMsq m) (i + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))⁻¹ ^ 4 *
    (((L : ℝ) ^ (i + 1)) ^ 2 / sXp x ^ 2) *
      (2 * (L : ℝ) ^ 2 * kszS R M C₁w mbar m b μ₀ lam x i)) /
    ‖hBeta R m b μ₀ x (i + 1)‖

/-- `c_{ν,k}`. -/
def e6Nu (M : MasterFacts L) (Nh : ℕ) (m b μ₀ : ℝ) (k : ℕ) : ℝ :=
  (if k < Nh then max M.core.B' 0 * max (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 0
    else 1 / 8) + M.core.ce * max (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 0

/-- `γ_k`: the per-scale gradient size of the blocks. -/
def e6Gr (M : MasterFacts L) (C₁k C₁w mbar cu m b μ₀ : ℝ) (lam : ℕ → ℂ) (x : Lam 2 L N)
    (k : ℕ) : ℝ :=
  gradRHS (L : ℝ) (Obs2.KG 2 Ccut2 4) (KM4 2 Ccut2) (sXp x)
    (fun i => histS (R.withMsq m) i (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
    (fun i => 2 * (cNb2 : ℝ) * (cSm2 : ℝ) * kszQ R M C₁k C₁w mbar cu m b μ₀ lam x i)
    (fun i => 2 * (L : ℝ) ^ 2 * kszS R M C₁w mbar m b μ₀ lam x i) (Obs.coal L (0 : Lam 2 L N) x) k

/-- `μ_k`: the per-scale `M₄` size of the blocks. -/
def e6M4 (M : MasterFacts L) (C₁k C₁w mbar cu m b μ₀ : ℝ) (lam : ℕ → ℂ) (x : Lam 2 L N)
    (k : ℕ) : ℝ :=
  m4RHS (L : ℝ) (KM4 2 Ccut2) (sXp x)
    (fun i => histS (R.withMsq m) i (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
    (fun i => 2 * (cNb2 : ℝ) * (cSm2 : ℝ) * kszQ R M C₁k C₁w mbar cu m b μ₀ lam x i)
    (fun i => 2 * (L : ℝ) ^ 2 * kszS R M C₁w mbar m b μ₀ lam x i) (Obs.coal L (0 : Lam 2 L N) x) k

/-- `λ_k(ℓ')`: the `LopM4` gradient size at `(L^{k+1}, ℓ')`. -/
def e6Lop (m b μ₀ : ℝ) (x : Lam 2 L N) (wl : ℝ) (k : ℕ) (ℓ' : ℝ) : ℝ :=
  2 * (wl * (histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 /
      (L : ℝ) ^ (k + 1))) * (ℓ' * (2 * sXp x * ℓ' * ((L : ℝ) ^ (k + 1))⁻¹)) +
    histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
      ((2 * sXp x * ℓ' * ((L : ℝ) ^ (k + 1))⁻¹) * (2 * sXp x * ℓ' * ((L : ℝ) ^ (k + 1))⁻¹))

/-- Item 5: `δ_k`. -/
def e6Del (M : MasterFacts L) (C₁k C₁w mbar cu m b μ₀ : ℝ) (lam : ℕ → ℂ) (x : Lam 2 L N)
    (wl : ℝ) (k : ℕ) : ℝ :=
  2 * ((4 : ℝ) ^ 4 * (L : ℝ)⁻¹ * e6Gr R M C₁k C₁w mbar cu m b μ₀ lam x k +
    e6M4 R M C₁k C₁w mbar cu m b μ₀ lam x k * e6Lop R m b μ₀ x wl k
      (2 * (2 * histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))) /
    ‖hBeta R m b μ₀ x (k + 1)‖

/-- Item 6: `e_k = 2(L+39)²·8⁴·r_k`. -/
def e6E (M : MasterFacts L) (m b μ₀ : ℝ) (k : ℕ) : ℝ :=
  2 * ((L : ℝ) + 39) ^ 2 *
    ((8 : ℝ) ^ 4 * (M.core.c * max (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 0))

/-- `δ'_i` (absolute, at `T_{i+1}(4s_{i+1})`). -/
def e6DelF (M : MasterFacts L) (C₁k C₁w mbar cu m b μ₀ : ℝ) (lam : ℕ → ℂ) (x : Lam 2 L N)
    (wl : ℝ) (i : ℕ) : ℝ :=
  2 * ((9 / 2 : ℝ) ^ 4 * (L : ℝ)⁻¹ * e6Gr R M C₁k C₁w mbar cu m b μ₀ lam x i +
    e6M4 R M C₁k C₁w mbar cu m b μ₀ lam x i * e6Lop R m b μ₀ x wl i
      (2 * (2 * histS (R.withMsq m) (i + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))))

/-- `e'_i = 2(L+39)²·9⁴·r_i`. -/
def e6EF (M : MasterFacts L) (m b μ₀ : ℝ) (i : ℕ) : ℝ :=
  2 * ((L : ℝ) + 39) ^ 2 *
    ((9 : ℝ) ^ 4 * (M.core.c * max (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ i).1 0))

/-- Item 9: `F_i = 2δ'_ie'_i/β_{i+1}`. -/
def e6F (M : MasterFacts L) (C₁k C₁w mbar cu m b μ₀ : ℝ) (lam : ℕ → ℂ) (x : Lam 2 L N)
    (wl : ℝ) (i : ℕ) : ℝ :=
  2 * (e6DelF R M C₁k C₁w mbar cu m b μ₀ lam x wl i * e6EF R M m b μ₀ i) /
    ‖hBeta R m b μ₀ x (i + 1)‖

/-- The region `M₄` size `2μ_i/β_{i+1}` (for the Pauli defects `P_i = pdSz`). -/
def e6M4X (M : MasterFacts L) (C₁k C₁w mbar cu m b μ₀ : ℝ) (lam : ℕ → ℂ) (x : Lam 2 L N)
    (i : ℕ) : ℝ :=
  2 * e6M4 R M C₁k C₁w mbar cu m b μ₀ lam x i / ‖hBeta R m b μ₀ x (i + 1)‖

end Traj

/-! ### Nonnegativity -/

theorem gradRHS_nonneg {Lr KG KM s : ℝ} (hL : 0 < Lr) (hKG : 0 ≤ KG) (hKM : 0 ≤ KM) (hs : 0 ≤ s)
    {ℓ κQ κS : ℕ → ℝ} (hℓ : ∀ i, 0 < ℓ i) (hQ : ∀ i, 0 ≤ κQ i) (hS : ∀ i, 0 ≤ κS i) (j k : ℕ) :
    0 ≤ gradRHS Lr KG KM s ℓ κQ κS j k := by
  unfold gradRHS
  refine sum_nonneg fun i _ => mul_nonneg (pow_nonneg (by positivity) _) ?_
  have hm : 0 ≤ ∑ i' ∈ Ico j (i + 1), KM * ((ℓ i')⁻¹ ^ 4 * ((Lr ^ i') ^ 2 / s ^ 2) * κQ i' +
      (ℓ (i' + 1))⁻¹ ^ 4 * ((Lr ^ (i' + 1)) ^ 2 / s ^ 2) * κS i') :=
    sum_nonneg fun i' _ => mul_nonneg hKM (add_nonneg
      (mul_nonneg (by have := hℓ i'; positivity) (hQ i'))
      (mul_nonneg (by have := hℓ (i' + 1); positivity) (hS i')))
  have h1 := hℓ (i + 1)
  have h2 := hℓ i
  have hA : 0 ≤ 2 * (2 * s * (ℓ (i + 1) / 4) ^ 2 / Lr ^ (i + 1)) *
          (ℓ (i + 1) * (2 * s * ℓ (i + 1) * (Lr ^ (i + 1))⁻¹)) +
        (ℓ (i + 1) / 4) ^ 2 * ((2 * s * ℓ (i + 1) * (Lr ^ (i + 1))⁻¹) *
          (2 * s * ℓ (i + 1) * (Lr ^ (i + 1))⁻¹)) := by positivity
  have hB : 0 ≤ (1 + 2 * s * (Lr ^ (i + 1))⁻¹) * (KG * (Lr ^ i * (Lr ^ (i + 1))⁻¹)) +
        (ℓ i)⁻¹ ^ 2 * (2 * (ℓ (i + 1) * (2 * s * ℓ (i + 1) * (Lr ^ (i + 1))⁻¹)) +
          (2 * s * ℓ (i + 1) * (Lr ^ (i + 1))⁻¹) * (2 * s * ℓ (i + 1) * (Lr ^ (i + 1))⁻¹)) := by
    positivity
  have hC : 0 ≤ (1 + 2 * s * (Lr ^ (i + 1))⁻¹) * (KG * (Lr ^ (i + 1) * (Lr ^ (i + 1))⁻¹)) +
        (ℓ (i + 1))⁻¹ ^ 2 * (2 * (ℓ (i + 1) * (2 * s * ℓ (i + 1) * (Lr ^ (i + 1))⁻¹)) +
          (2 * s * ℓ (i + 1) * (Lr ^ (i + 1))⁻¹) * (2 * s * ℓ (i + 1) * (Lr ^ (i + 1))⁻¹)) := by
    positivity
  exact add_nonneg (add_nonneg (mul_nonneg hm hA) (mul_nonneg hB (hQ i))) (mul_nonneg hC (hS i))

theorem m4RHS_nonneg {Lr KM s : ℝ} (hL : 0 < Lr) (hKM : 0 ≤ KM) (hs : 0 ≤ s)
    {ℓ κQ κS : ℕ → ℝ} (hℓ : ∀ i, 0 < ℓ i) (hQ : ∀ i, 0 ≤ κQ i) (hS : ∀ i, 0 ≤ κS i) (j k : ℕ) :
    0 ≤ m4RHS Lr KM s ℓ κQ κS j k := by
  unfold m4RHS
  exact sum_nonneg fun i' _ => mul_nonneg hKM (add_nonneg
    (mul_nonneg (by have := hℓ i'; positivity) (hQ i'))
    (mul_nonneg (by have := hℓ (i' + 1); positivity) (hS i')))

end

end Spin2
