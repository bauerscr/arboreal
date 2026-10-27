import Spin2.Multiscale.RGInH
import PtCorr2.Pair.TwoPtZZ
import PtCorr2.Zero.TwoPtGhost

/-!
# `TwoPtSq` from the Case-(2) pair observable: the `d = 2` square

`TwoPtSq` (`Spin2/Multiscale/RGInH.lean`) is reduced to two estimates on the Case-(2) RG product of the pair
observable `z̃_0z̃_x`, `z̃_y = 1 - bψ̄_yψ_y` (sources `σ_0, σ_x`, `γ = 1`, `μ = -b`: `zV b`, points
`ptsX x = (0, x)`), split at the coalescence scale `j_x`:

* model level (`PtCorr2.twopt_eq_neg_zz`): `b⟨ψ̄_0ψ_x⟩ = -⟨z̃_0z̃_x⟩ + p`, `0 ≤ p ≤ r`,
  `r = 1 - b⟨ψ̄_0ψ_0⟩ = ⟨z̃_0⟩ = ⟨z̃_x⟩`;
* exact RG identity (`PtCorr2.zz_square_split`): with `X = Π^{<j_x}` (rank one by coalescence),
  `Y = Π^{≥j_x}`, `A = sA X/sE X`, `B = sB X/sE X`, `E = sAB Y/sE Y`:
  `⟨z̃_0z̃_x⟩ = -AB + rA + rB + E`. Hence **`b⟨ψ̄_0ψ_x⟩ = AB - r(A + B) - E + p`** (`twopt_zz_eq`).

Named inputs (open analysis), exactly:
* **`ZBelow R N_h m² b μ₀ λ̂ K_M`** (the one-point part below coalescence is `M`): for `x ≠ 0`,
  `j_x ≤ N_h`: `‖A - M_{j_x}‖ ≤ K_M‖M_{j_x}‖ǧ_{j_x}` and `‖B - M_{j_x}‖ ≤ K_M‖M_{j_x}‖ǧ_{j_x}`
  (the `γ`-flow of Case (2): `γ_{j+1} = γ_j + μ^{(2),♭}C'_{j+1}(0,0) + O(ǧ²)`, `μ^{(2)}_k = -bλ̂_k`);
* **`PairAbove R N_h m² b μ₀ K_E K_R`** (the pair part above coalescence is small, Pauli):
  `‖E‖ ≤ K_E‖M_{j_x}‖²ǧ_{j_x} + K_R r`.

**`twoPtSq_of_zz`**: `ZBelow`, `PairAbove`, `‖M_j‖ ≤ M_b` (`j ≤ N_h`), `0 ≤ ǧ ≤ 1` and the
hypotheses of the observable chain give `TwoPtSq` with `K_P = K_M(2 + K_M) + K_E`,
`K_r = 1 + 2(1 + K_M)M_b + K_R`. **`twoPtSq_of_zz_flow`**: the same with the chain hypotheses taken
from `FlowC2Concl` (admissible trajectories, `m² ∈ mRange`, `b ≤ μ₀ + m²`, `L > 48`).
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

/-! ## Pure estimate -/

/-- `‖(AB - rA - rB - E + p) - M²‖ ≤ (K_M(2+K_M) + K_E)‖M‖²g + (1 + 2(1+K_M)M_b + K_R)r`. -/
theorem twoPt_sq_pure {A B M E : ℂ} {r p g KM Mb KE KR : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (hKM : 0 ≤ KM) (hr0 : 0 ≤ r) (hp0 : 0 ≤ p) (hpr : p ≤ r)
    (hA : ‖A - M‖ ≤ KM * ‖M‖ * g) (hB : ‖B - M‖ ≤ KM * ‖M‖ * g) (hMb : ‖M‖ ≤ Mb)
    (hE : ‖E‖ ≤ KE * ‖M‖ ^ 2 * g + KR * r) :
    ‖(A * B - (r : ℂ) * A - (r : ℂ) * B - E + (p : ℂ)) - M ^ 2‖ ≤
      (KM * (2 + KM) + KE) * ‖M‖ ^ 2 * g + (1 + 2 * (1 + KM) * Mb + KR) * r := by
  have hM0 := norm_nonneg M
  have hg' : KM * ‖M‖ * g ≤ KM * ‖M‖ := mul_le_of_le_one_right (by positivity) hg1
  have hAn : ‖A‖ ≤ (1 + KM) * ‖M‖ := by
    have := norm_le_norm_add_norm_sub' A M; nlinarith
  have hBn : ‖B‖ ≤ (1 + KM) * ‖M‖ := by
    have := norm_le_norm_add_norm_sub' B M; nlinarith
  have h1 : ‖A * B - M ^ 2‖ ≤ KM * (2 + KM) * ‖M‖ ^ 2 * g := by
    have e : A * B - M ^ 2 = (A - M) * B + M * (B - M) := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have i1 : ‖A - M‖ * ‖B‖ ≤ (KM * ‖M‖ * g) * ((1 + KM) * ‖M‖) :=
      mul_le_mul hA hBn (norm_nonneg _) (by positivity)
    have i2 : ‖M‖ * ‖B - M‖ ≤ ‖M‖ * (KM * ‖M‖ * g) := mul_le_mul_of_nonneg_left hB hM0
    have e2 : KM * (2 + KM) * ‖M‖ ^ 2 * g =
        (KM * ‖M‖ * g) * ((1 + KM) * ‖M‖) + ‖M‖ * (KM * ‖M‖ * g) := by ring
    rw [e2]; exact add_le_add i1 i2
  have hrA : ‖(r : ℂ) * A‖ ≤ r * ((1 + KM) * Mb) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
    exact mul_le_mul_of_nonneg_left (hAn.trans (mul_le_mul_of_nonneg_left hMb (by positivity)))
      hr0
  have hrB : ‖(r : ℂ) * B‖ ≤ r * ((1 + KM) * Mb) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
    exact mul_le_mul_of_nonneg_left (hBn.trans (mul_le_mul_of_nonneg_left hMb (by positivity)))
      hr0
  have hp : ‖(p : ℂ)‖ = p := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp0]
  have e : (A * B - (r : ℂ) * A - (r : ℂ) * B - E + (p : ℂ)) - M ^ 2 =
      (A * B - M ^ 2) + (-((r : ℂ) * A)) + (-((r : ℂ) * B)) + (-E) + (p : ℂ) := by ring
  rw [e]
  have t1 := norm_add_le ((A * B - M ^ 2) + (-((r : ℂ) * A)) + (-((r : ℂ) * B)) + (-E)) (p : ℂ)
  have t2 := norm_add_le ((A * B - M ^ 2) + (-((r : ℂ) * A)) + (-((r : ℂ) * B))) (-E)
  have t3 := norm_add_le ((A * B - M ^ 2) + (-((r : ℂ) * A))) (-((r : ℂ) * B))
  have t4 := norm_add_le (A * B - M ^ 2) (-((r : ℂ) * A))
  rw [norm_neg] at t2 t3 t4
  rw [hp] at t1
  nlinarith

variable {L N : ℕ} [NeZero L]

/-! ## The pair observable `z̃_0z̃_x` -/

/-- The points `a = 0`, `b = x`. -/
def ptsX (x : Lam 2 L N) : Obs2.ObsPts 2 L N := ⟨0, x, ∅⟩

/-- The Case-(2) couplings of `z̃_0z̃_x`: `γ_a = γ_b = 1`, `μ_a = μ_b = -b`, no `ab` couplings. -/
def zV (b : ℝ) : Obs2.OCoup2 := ⟨-(b : ℂ), -(b : ℂ), 1, 1, 0, 0, 0, 0⟩

theorem zV_abFree (b : ℝ) : Obs2.AbFree .two (zV b) := ⟨rfl, rfl, rfl, rfl⟩

theorem zObsA_zV (b : ℝ) (x : Lam 2 L N) :
    PtCorr2.zObsA (zV b) (ptsX x) = 1 - (b : ℂ) • (psibar 0 * psi 0) := by
  simp [PtCorr2.zObsA, zV, ptsX, sub_eq_add_neg, neg_smul]

theorem zObsB_zV (b : ℝ) (x : Lam 2 L N) :
    PtCorr2.zObsB (zV b) (ptsX x) = 1 - (b : ℂ) • (psibar x * psi x) := by
  simp [PtCorr2.zObsB, zV, ptsX, sub_eq_add_neg, neg_smul]

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- `Π^{<j_x}` for the pair observable `z̃_0z̃_x` along the trajectory at mass `m²`. -/
def zLo (m b μ₀ : ℝ) (x : Lam 2 L N) : Obs.OE .two (Lam 2 L N) :=
  PtCorr2.prodLo (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x))
    (Obs.coal L (0 : Lam 2 L N) x) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)

/-- `Π^{≥j_x}` for the pair observable `z̃_0z̃_x` along the trajectory at mass `m²`. -/
def zHi (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) : Obs.OE .two (Lam 2 L N) :=
  PtCorr2.prodHi (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) Nh
    (Obs.coal L (0 : Lam 2 L N) x) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)

/-- **Named input: the one-point parts below coalescence are `M_{j_x}`.** -/
def ZBelow (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (KM : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ‖PtCorr2.sA (zLo R m b μ₀ x) / PtCorr2.sE (zLo R m b μ₀ x) -
        Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ ≤
      KM * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 ∧
    ‖PtCorr2.sB (zLo R m b μ₀ x) / PtCorr2.sE (zLo R m b μ₀ x) -
        Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ ≤
      KM * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1

/-- **Named input: the pair part above coalescence is small.** -/
def PairAbove (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (KE KR : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ‖PtCorr2.sAB (zHi R Nh m b μ₀ x) / PtCorr2.sE (zHi R Nh m b μ₀ x)‖ ≤
      KE * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ ^ 2 *
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 +
        KR * ‖1 - (b : ℂ) * PtCorr2.avg0 L N m b μ₀ (psibar 0 * psi 0)‖

set_option maxHeartbeats 1000000 in
/-- **The exact `d = 2` square for the two-point function**: along the trajectory (hypotheses of
the observable chain, `h ≥ 0`, `L > 48`, `j_x ≤ N_h`), with `A, B, E` as above and
`r = 1 - b⟨ψ̄_0ψ_0⟩`: `b⟨ψ̄_0ψ_x⟩ = AB - rA - rB - E + p`, `0 ≤ p ≤ r ≤ 1`. -/
theorem twopt_zz_eq {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < m)
    (hm : m ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt (R.withMsq m) j)
    (hVL : ValidAtL (R.withMsq m) Nh) (hL : 2 ^ (2 + 3) + 8 * 2 < L) {b μ₀ : ℝ} (hb : 0 < b)
    (hh : b ≤ μ₀ + m) (x : Lam 2 L N) (hj : Obs.coal L (0 : Lam 2 L N) x ≤ Nh) :
    ∃ p r : ℝ, 0 ≤ p ∧ p ≤ r ∧ r ≤ 1 ∧
      1 - (b : ℂ) * PtCorr2.avg0 L N m b μ₀ (psibar 0 * psi 0) = r ∧
      (b : ℂ) * PtCorr2.avg0 L N m b μ₀ (psibar 0 * psi x) =
        PtCorr2.sA (zLo R m b μ₀ x) / PtCorr2.sE (zLo R m b μ₀ x) *
            (PtCorr2.sB (zLo R m b μ₀ x) / PtCorr2.sE (zLo R m b μ₀ x)) -
          (r : ℂ) * (PtCorr2.sA (zLo R m b μ₀ x) / PtCorr2.sE (zLo R m b μ₀ x)) -
          (r : ℂ) * (PtCorr2.sB (zLo R m b μ₀ x) / PtCorr2.sE (zLo R m b μ₀ x)) -
          PtCorr2.sAB (zHi R Nh m b μ₀ x) / PtCorr2.sE (zHi R Nh m b μ₀ x) + (p : ℂ) := by
  obtain ⟨p, r, hp0, hpr, hr1, hr, hP⟩ := PtCorr2.twopt_eq_neg_zz (L := L) (N := N) hb hm0 hh x
  refine ⟨p, r, hp0, hpr, hr1, hr, ?_⟩
  obtain ⟨-, -, -, -, hzz⟩ := PtCorr2.zz_square_split (R.withMsq m) (ptsX x) hN hρ1 hspl hm0 hm
    hV hVL hL hj hb hh (zV b) (zV_abFree b)
  have hra : PtCorr2.avg0 L N m b μ₀ (PtCorr2.zObsA (zV b) (ptsX x)) = r := by
    rw [zObsA_zV, ← hr]
    exact Ward.avg_one_sub_smul _ _ (PtCorr2.onept_Zb_ne hb hm0 hh) _ _
  have hrb : PtCorr2.avg0 L N m b μ₀ (PtCorr2.zObsB (zV b) (ptsX x)) = r := by
    rw [zObsB_zV, ← hr, ← PtCorr2.avg0_diag_transl hm0 (by omega) x]
    exact Ward.avg_one_sub_smul _ _ (PtCorr2.onept_Zb_ne hb hm0 hh) _ _
  have hzz' := hzz
  rw [show (R.withMsq m).msq = m from rfl, hra, hrb, zObsA_zV, zObsB_zV] at hzz'
  have hco : Obs.coal L (ptsX x).a (ptsX x).b = Obs.coal L (0 : Lam 2 L N) x := rfl
  rw [hco] at hzz'
  unfold zLo zHi
  rw [hP, hzz']
  ring

set_option maxHeartbeats 1000000 in
/-- **`TwoPtSq` from `ZBelow` and `PairAbove`** (trajectory level). -/
theorem twoPtSq_of_zz {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < m)
    (hm : m ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt (R.withMsq m) j)
    (hVL : ValidAtL (R.withMsq m) Nh) (hL : 2 ^ (2 + 3) + 8 * 2 < L) {b μ₀ : ℝ} (hb : 0 < b)
    (hh : b ≤ μ₀ + m) (lam : ℕ → ℂ) {KM Mb KE KR : ℝ} (hKM : 0 ≤ KM)
    (hg : ∀ k ≤ Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1)
    (hMb : ∀ k ≤ Nh, ‖Mmag R m b μ₀ lam k‖ ≤ Mb)
    (hZ : ZBelow R Nh m b μ₀ lam KM) (hE : PairAbove R Nh m b μ₀ lam KE KR) :
    TwoPtSq R Nh m b μ₀ lam (KM * (2 + KM) + KE) (1 + 2 * (1 + KM) * Mb + KR) := by
  intro x hx hj
  obtain ⟨p, r, hp0, hpr, -, hr, hP⟩ :=
    twopt_zz_eq R hN m hρ1 hspl hm0 hm hV hVL hL hb hh x hj
  obtain ⟨hA, hB⟩ := hZ x hx hj
  have hE' := hE x hx hj
  rw [hr, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp0.trans hpr)] at hE' ⊢
  rw [hP]
  exact twoPt_sq_pure (hg _ hj).1 (hg _ hj).2 hKM (hp0.trans hpr) hp0 hpr hA hB (hMb _ hj) hE'

/-! ### The refined inputs: the `γ` couplings below coalescence and the state at coalescence -/

/-- `γ_{0,k} = -ε(u^{obs}_{k,a})`: the accumulated observable constant at `a = 0`, scale `k`. -/
def uA (m b μ₀ : ℝ) (x : Lam 2 L N) (k : ℕ) : ℂ :=
  -ε ((Obs2.obsHist (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) k
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).u : Obs.SA .two (Lam 2 L N)).a

/-- `γ_{x,k} = -ε(u^{obs}_{k,b})`. -/
def uB (m b μ₀ : ℝ) (x : Lam 2 L N) (k : ℕ) : ℂ :=
  -ε ((Obs2.obsHist (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) k
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).u : Obs.SA .two (Lam 2 L N)).b

/-- The Gaussian integral `ω_{Γ_k}(Z_k)` of the state with sources at scale `k`. -/
def zOm (m b μ₀ : ℝ) (x : Lam 2 L N) (k : ℕ) : Obs.OE .two (Lam 2 L N) :=
  PtCorr2.omegaCO (PtCorr2.Γh (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
    (PtCorr2.ZhO (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) k
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))

/-- **Named input (refined `ZBelow`): the `γ` couplings at the coalescence scale are `M_{j_x}`.** -/
def ZBelowU (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (KM : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ‖uA R m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x) -
        Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ ≤
      KM * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 ∧
    ‖uB R m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x) -
        Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ ≤
      KM * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1

/-- **Named input (refined `PairAbove`): at the coalescence scale, the normalised `σ_0σ_x` part of
the Gaussian integral of the state is small.** -/
def PairAboveW (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (KE KR : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ‖PtCorr2.sAB (zOm R m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x)) /
        PtCorr2.sE (zOm R m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x))‖ ≤
      KE * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ ^ 2 *
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 +
        KR * ‖1 - (b : ℂ) * PtCorr2.avg0 L N m b μ₀ (psibar 0 * psi 0)‖

set_option maxHeartbeats 1000000 in
/-- **`TwoPtSq` from `ZBelowU` and `PairAboveW`** (trajectory level). -/
theorem twoPtSq_of_zzU {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < m)
    (hm : m ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt (R.withMsq m) j)
    (hVL : ValidAtL (R.withMsq m) Nh) (hL : 2 ^ (2 + 3) + 8 * 2 < L) {b μ₀ : ℝ} (hb : 0 < b)
    (hh : b ≤ μ₀ + m) (lam : ℕ → ℂ) {KM Mb KE KR : ℝ} (hKM : 0 ≤ KM)
    (hg : ∀ k ≤ Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1)
    (hMb : ∀ k ≤ Nh, ‖Mmag R m b μ₀ lam k‖ ≤ Mb)
    (hZ : ZBelowU R Nh m b μ₀ lam KM) (hE : PairAboveW R Nh m b μ₀ lam KE KR) :
    TwoPtSq R Nh m b μ₀ lam (KM * (2 + KM) + KE) (1 + 2 * (1 + KM) * Mb + KR) := by
  refine twoPtSq_of_zz R hN m hρ1 hspl hm0 hm hV hVL hL hb hh lam hKM hg hMb ?_ ?_
  · intro x hx hj
    obtain ⟨hX0, -⟩ := PtCorr2.zz_square_split (R.withMsq m) (ptsX x) hN hρ1 hspl hm0 hm
      hV hVL hL hj hb hh (zV b) (zV_abFree b)
    obtain ⟨ea, eb⟩ := PtCorr2.prodLo_sA_sB (R.withMsq m) (ptsX x)
      (Obs2.obsInit .two (zV b) (ptsX x)) rfl (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
      (Obs.coal L (0 : Lam 2 L N) x)
    have hX0' : PtCorr2.sE (zLo R m b μ₀ x) ≠ 0 := hX0
    have ha : PtCorr2.sA (zLo R m b μ₀ x) / PtCorr2.sE (zLo R m b μ₀ x) =
        uA R m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x) := by
      have ea' : PtCorr2.sA (zLo R m b μ₀ x) =
          PtCorr2.sE (zLo R m b μ₀ x) * uA R m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x) := ea
      rw [ea', mul_div_cancel_left₀ _ hX0']
    have hb' : PtCorr2.sB (zLo R m b μ₀ x) / PtCorr2.sE (zLo R m b μ₀ x) =
        uB R m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x) := by
      have eb' : PtCorr2.sB (zLo R m b μ₀ x) =
          PtCorr2.sE (zLo R m b μ₀ x) * uB R m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x) := eb
      rw [eb', mul_div_cancel_left₀ _ hX0']
    rw [ha, hb']
    exact hZ x hx hj
  · intro x hx hj
    have hw := PtCorr2.hist_omegaO_from (R.withMsq m) (ptsX x)
      (Obs2.obsInit .two (zV b) (ptsX x)) hN hρ1 hspl hm0 hm hV hVL b μ₀
      (Obs2.obsInit_isObs .two (zV b) (ptsX x)) (PtCorr2.obsLocInv_init .two (zV b) (ptsX x)) hj
    have e : zHi R Nh m b μ₀ x = zOm R m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x) := hw.symm
    rw [e]
    exact hE x hx hj

end Traj

/-- **`TwoPtSq` along the admissible trajectories of `thm:flow`**: for constants with
`FlowC2Concl` and `ε ≤ 1`, `L > 48`, every `N`, `R` (`R.P = Pc`, `i₀ = 0`, `ℓ, A, ρ`), `N_h = N - 2`,
`m² ∈ mRange`, admissible `(b, μ₀)` with `b ≤ μ₀ + m²` and every `λ̂`: `ZBelow`, `PairAbove` and
`‖M_j‖ ≤ M_b` imply `TwoPtSq` with `K_P = K_M(2+K_M) + K_E`, `K_r = 1 + 2(1+K_M)M_b + K_R`. -/
theorem twoPtSq_of_zz_flow {L : ℕ} [NeZero L] {ℓ A ρ κ cg cm cT ε Ke Cf Cb : ℝ}
    (hF : FlowC2Concl L ℓ A ρ κ cg cm cT ε Ke Cf Cb) (hε1 : ε ≤ 1)
    (hL : 2 ^ (2 + 3) + 8 * 2 < L) :
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N →
    ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, ∀ b μ₀,
      Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ → b ≤ μ₀ + m →
    ∀ (lam : ℕ → ℂ) (KM Mb KE KR : ℝ), 0 ≤ KM → (∀ k ≤ Nh, ‖Mmag R m b μ₀ lam k‖ ≤ Mb) →
      ZBelowU R Nh m b μ₀ lam KM → PairAboveW R Nh m b μ₀ lam KE KR →
      TwoPtSq R Nh m b μ₀ lam (KM * (2 + KM) + KE) (1 + 2 * (1 + KM) * Mb + KR) := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm hh lam KM Mb KE KR hKM hMb hZ hE
  obtain ⟨-, -, hρ0, -, -, -, -, -, -, -, -, -, -, hρ8, hspl, hrest⟩ := hF
  have hval := (hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm
  have hb : 0 < b := by
    have := (hadm.1 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hg : ∀ k ≤ Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1 := fun k hk =>
    ⟨(hadm.1 k hk).1.le, ((hadm.1 k hk).2.1).trans hε1⟩
  exact twoPtSq_of_zzU R hNh m (by rw [hRρ]; linarith) (by rw [hP, hRρ]; exact hspl)
    hm.1 hm.2 hval.1 hval.2 hL hb hh lam hKM hg hMb hZ hE

end

end Spin2
