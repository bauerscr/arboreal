import Spin2.Cont.ContEqC4
import Spin2.Cont.ContFin2

set_option autoImplicit false

/-!
# B3, `r`-dependent form, item (d): scalar packages; both cases as `C·cddRel·ϑ_{N_h}²`

The scalar hypotheses of the two pair bounds are collected, per pair `(x, y)`, in two named
`Prop`s (for every admissible transient pair `kk, ww` of the restart, which the bounds produce
existentially):

* **`MasterFacts.EqcMidPkg C₁w C₁t C₁v C₁m Λ₁ Λ₂ R m b N_h r₀ x y ms r C_δ K_A K_R`**: the `∀` block
  of `fin_T6_mid` (`hvT … hmAa` without `C_δ`, `hδ`) and `naKA(…) ≤ K_A`, `rpc11K(…, C_δ) ≤ K_R`;
* **`MasterFacts.EqcTopPkg R m b N_h r₀ x y ms r K_A K_E`**: the arrows of `fin_conn_diff_top`
  and `naKA(…) ≤ K_A`, `rpKE(…) ≤ K_E`.

* **`MasterFacts.eqc_mid_pkg (hcab)`** (`ms < j_y ≤ N_h`, `N ≤ j_y + C_δ`):
  `|P(x) − P(y)| ≤ eqcCmid(K_A, K_R, C_δ)·cddRel·ϑ_{N_h}²`;
* **`MasterFacts.eqc_top_pkg … (hcab)`** (`N_h + 1 ≤ j_y`):
  `|P(x) − P(y)| ≤ eqcCtop(K_A, K_E)·cddRel·ϑ_{N_h}²`,
  `eqcCtop K_A K_E = (9/4)(max(1 + K_O, 0)max(K_A, 0) + max(K_E, 0))·cw4Cmp(0)`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs FRD Flow2 Flow2.Hist Obs2 Step2.D2

variable {L : ℕ} [NeZero L]

namespace MasterFacts

variable (M : MasterFacts L)

/-- **The constant of the top case.** -/
def eqcCtop (KA KE : ℝ) : ℝ :=
  9 / 4 * (max (1 + M.fwKO) 0 * max KA 0 + max KE 0) * cw4Cmp M 0

theorem eqcCmid_mono (hc0 : 0 ≤ M.core.c) {KA KA' KR KR' : ℝ} {n n' : ℕ} (hKA : KA ≤ KA')
    (hKR : KR ≤ KR') (hn : n ≤ n') : M.eqcCmid KA KR n ≤ M.eqcCmid KA' KR' n' := by
  unfold eqcCmid
  have hK := M.eqcK_nonneg hc0
  have hEc : 0 ≤ M.eqcEc := by unfold eqcEc; positivity
  have hK11 := M.rpc11KM_nonneg M.Kp
  have hKg := M.eqcKg_one_le
  have hn' : (n : ℝ) ≤ n' := by exact_mod_cast hn
  have a1 : max KA 0 ≤ max KA' 0 := max_le_max hKA le_rfl
  have a2 : max KR 0 ≤ max KR' 0 := max_le_max hKR le_rfl
  have a3 : M.eqcKg ^ n ≤ M.eqcKg ^ n' := pow_le_pow_right₀ hKg hn
  have a4 := cw4Cmp_mono M hn
  have a5 : 0 ≤ cw4Cmp M n := (cw4Cmp_pos M n).le
  have hA0 : 0 ≤ max KA 0 := le_max_right _ _
  have hR0 : 0 ≤ max KR 0 := le_max_right _ _
  have b1 : max KA 0 * M.eqcEc * (3 / 2) + ((n : ℝ) + 1) * M.eqcK ≤
      max KA' 0 * M.eqcEc * (3 / 2) + ((n' : ℝ) + 1) * M.eqcK := by
    have := mul_le_mul_of_nonneg_right a1 hEc
    have := mul_le_mul_of_nonneg_right (show (n : ℝ) + 1 ≤ n' + 1 by linarith) hK
    linarith
  have b0 : 0 ≤ max KA 0 * M.eqcEc * (3 / 2) + ((n : ℝ) + 1) * M.eqcK := by positivity
  have b2 : 3 / 2 * (1 + M.rpc11KM M.Kp) * M.eqcKg ^ n ≤ 3 / 2 * (1 + M.rpc11KM M.Kp) * M.eqcKg ^ n' :=
    mul_le_mul_of_nonneg_left a3 (by positivity)
  have b3 := mul_le_mul b1 b2 (by positivity) (by positivity)
  have b4 : max KR 0 * cw4Cmp M n ≤ max KR' 0 * cw4Cmp M n' := mul_le_mul a2 a4 a5 (by positivity)
  have e1 : ∀ a k : ℝ, ∀ j : ℕ, (a * M.eqcEc * (3 / 2) + ((j : ℝ) + 1) * M.eqcK) *
      (3 / 2 * (1 + M.rpc11KM M.Kp)) * k = (a * M.eqcEc * (3 / 2) + ((j : ℝ) + 1) * M.eqcK) *
      (3 / 2 * (1 + M.rpc11KM M.Kp) * k) := fun _ _ _ => by ring
  rw [e1, e1]
  linarith

/-- **The scalar package of the intermediate case** for one pair (the `∀` block of
`fin_T6_mid` for every admissible transient pair `kk, ww`, with fixed `C_δ`, together with the
constant bounds `K_A`, `K_R`). -/
def EqcMidPkg (C₁w C₁t C₁v C₁m Λ₁ Λ₂ : ℝ) {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)]
    [Fact (0 < R.A)] (m b : ℝ) (Nh : ℕ) (r₀ : ℝ) (x y : Lam 2 L N) (ms r Cδ : ℕ)
    (KA KR : ℝ) : Prop :=
  ∀ kk ww : ℝ, 0 ≤ kk → 0 ≤ ww →
    1344 * (8 * (PtCorr2.csN 2 : ℝ) * kk + M.core.rdtΓ * ww) ≤ histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r) →
    ∃ vT wT kxT w2 k2 m0 Q₀ mm k₁ c₁ : ℝ,
      (1 + (cw2Thb M Nh (Obs.coal L (0 : Lam 2 L N) y)) ≤ vT) ∧
      (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) y)).1) + (7 / 30) ^ (Obs.coal L (0 : Lam 2 L N) y - ms) * (ww / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) + (cw2Thb M Nh (Obs.coal L (0 : Lam 2 L N) y)) * (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) y)).1)) + w2 ≤ wT) ∧
      ((56 / 75) ^ (Obs.coal L (0 : Lam 2 L N) y - ms) * ((kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) + 8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) y)).1) ^ 2 + (cw2Thb M Nh (Obs.coal L (0 : Lam 2 L N) y)) * (8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) y)).1) ^ 2) ≤ kxT) ∧
      (0 ≤ w2) ∧
      (0 ≤ k2) ∧
      (0 ≤ Q₀) ∧
      ((7 / 5) ^ ((Obs.coal L (0 : Lam 2 L N) y) - ms) * (ww / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) ≤ M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 * Q₀) ∧
      ((7 / 5) ^ ((Obs.coal L (0 : Lam 2 L N) y) - ms) * ((kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) ≤ 8 * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1) ^ 2 * Q₀) ∧
      ((8 / 15) ^ ((Obs.coal L (0 : Lam 2 L N) y) - ms) * zabQ M R m b (b - m) x y ms (M.pl5M0 R m b x y ms r) (Obs.coal L (0 : Lam 2 L N) y) Nh Q₀ ≤ 1) ∧
      (Real.exp ((L : ℝ) ^ 2 * (M.core.Cw * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ((Obs.coal L (0 : Lam 2 L N) y) - 1)).1 + (2 * k2mbar M Nh (Obs.coal L (0 : Lam 2 L N) y)) ^ 2))) - 1 ≤ w2) ∧
      (M.k2cab * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) y)).1) * k2mbar M Nh (Obs.coal L (0 : Lam 2 L N) y) ^ 2 ≤ k2) ∧
      (M.core.A ^ 4 * (cx M.core.κ M.core.cT * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) y)).1 ^ 3 + kxT + k2) ≤ 1) ∧
      (0 < m0) ∧
      (8 * (2 * rpIota vT wT * M.core.A) ^ ((L + 18) ^ 2) ≤ vck C₁w * ((4 * C₁w + 1) * m0)) ∧
      (8 * (2 * rpIota vT wT * M.core.A) ^ ((L + 18) ^ 2) ≤ vck C₁t * ((4 * C₁t + 1) * m0)) ∧
      (8 * (2 * rpIota vT wT * M.core.A) ^ ((L + 18) ^ 2) ≤ vck C₁v * ((4 * C₁v + 1) * m0)) ∧
      (8 * (2 * rpIota vT wT * M.core.A) ^ ((L + 18) ^ 2) ≤ vck C₁m * ((4 * C₁m + 1) * m0)) ∧
      (2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) * ((rpc9Mb Λ₁ m0 Cδ) + (4 * C₁t + 1) * M.core.c * (rpc9Mb Λ₁ m0 Cδ) + 8 * ((4 * C₁t + 1) * (rpc9Mb Λ₁ m0 Cδ)) + 1) * M.core.ℓ ^ 2) * m * (L : ℝ) ^ (2 * N) ≤ 1) ∧
      (0 ≤ c₁) ∧
      (1 ≤ mm) ∧
      (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) + (7 / 30) ^ (Nh - ms) * (ww / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) ≤ (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) * mm) ∧
      ((M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ≤ mm) ∧
      ((56 / 75) ^ (Nh - ms) * ((kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) + 8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2 ≤ k₁) ∧
      (k₁ ≤ c₁ * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2 * mm) ∧
      (8 * (cx M.core.κ M.core.cT + c₁) * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 3 ≤ M.core.ε₀) ∧
      (2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) * (M.ctVT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) + M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm + 8 * M.rptfKx c₁ (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm k₁ + 1) * M.core.ℓ ^ 2) * m * (L : ℝ) ^ (2 * N) ≤ 1) ∧
      M.naKA (M.ctVT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)) (M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm) (M.rptfKx c₁ (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm k₁) r₀ ≤ KA ∧
      M.rpc11K r₀ C₁t Λ₁ Λ₂ (rpc9Mb Λ₁ m0 Cδ) Cδ ≤ KR

/-- **The scalar package of the top case** for one pair (the arrows of `fin_conn_diff_top` for
every admissible transient pair `kk, ww`, together with the constant bounds `K_A`, `K_E`). -/
def EqcTopPkg {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (m b : ℝ) (Nh : ℕ)
    (r₀ : ℝ) (x y : Lam 2 L N) (ms r : ℕ) (KA KE : ℝ) : Prop :=
  ∀ kk ww : ℝ, 0 ≤ kk → 0 ≤ ww →
    1344 * (8 * (PtCorr2.csN 2 : ℝ) * kk + M.core.rdtΓ * ww) ≤ histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r) →
    ∃ mm k₁ c₁ k2 Q₀ : ℝ,
      (0 ≤ c₁) ∧
      (0 ≤ k2) ∧
      (1 + cw2Thb M Nh Nh ≤ mm) ∧
      (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) + (7 / 30) ^ (Nh - ms) * (ww / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) + cw2Thb M Nh Nh * (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)) ≤ M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 * mm) ∧
      (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ mm) ∧
      ((56 / 75) ^ (Nh - ms) * ((kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) + 8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2 + cw2Thb M Nh Nh * (8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2) ≤ k₁) ∧
      (k₁ ≤ c₁ * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2 * mm) ∧
      (8 * (cx M.core.κ M.core.cT + c₁) * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 3 ≤ M.core.ε₀) ∧
      (0 ≤ Q₀) ∧
      ((7 / 5) ^ (Nh - ms) * (ww / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) ≤ M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 * Q₀) ∧
      ((7 / 5) ^ (Nh - ms) * ((kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) ≤ 8 * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1) ^ 2 * Q₀) ∧
      ((8 / 15) ^ (Nh - ms) * zabQ M R m b (b - m) x y ms (M.pl5M0 R m b x y ms r) Nh Nh Q₀ ≤ 1) ∧
      (M.k2cab / 5 * ((M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) * k2mbar M Nh Nh ^ 2) ≤ k2) ∧
      (M.core.A ^ 4 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ^ 3 + M.rptfKx c₁ (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm k₁ + k2) ≤ 1) ∧
      (2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) * (8 * (2 * rpIota (M.ctVT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)) (M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm) * M.core.A) ^ (L ^ 2) + 1) * M.core.ℓ ^ 2) * m * (L : ℝ) ^ (2 * N) ≤ 1) ∧
      (2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) * (M.ctVT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) + M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm + 8 * M.rptfKx c₁ (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm k₁ + 1) * M.core.ℓ ^ 2) * m * (L : ℝ) ^ (2 * N) ≤ 1) ∧
      M.naKA (M.ctVT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)) (M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm) (M.rptfKx c₁ (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm k₁) r₀ ≤ KA ∧
      M.rpKE ((2 * rpIota (M.ctVT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)) (M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm) * M.core.A) ^ (L ^ 2)) r₀ ≤ KE

set_option linter.unusedVariables false in
set_option maxHeartbeats 16000000 in
/-- **The intermediate case from the scalar package.** -/
theorem eqc_mid_pkg (hcab : 0 < M.k2cab) : ∃ C₁w C₁t C₁v C₁m Λ₁ Λ₂ : ℝ, 0 ≤ C₁w ∧ 0 ≤ C₁t ∧ 0 ≤ C₁v ∧ 0 ≤ C₁m ∧
    ∀ {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN3 : 3 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) {b : ℝ}
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j))
    {r₀ : ℝ} (hr₀ : 0 < r₀) (hr₀1 : r₀ ≤ 1) (hJ : LastJetBd L (M.core.A / 2) r₀)
    {Kt : ℝ}
    (hK : ‖(m : ℂ) * ((lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).Z *
        zmRaw (R.withMsq m) (Nh + 1)
          (lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).ζ) - 1‖ ≤
      Kt * m * (L : ℝ) ^ (2 * N))
    (hmT : Kt * m * (L : ℝ) ^ (2 * N) ≤ 1 / 2)
    (hmA : 8 * cKAL L M.core.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3 * m * (L : ℝ) ^ (2 * N) ≤ 1)
    (hsmA : (M.core.Cf * (M.core.ℓ ^ 2 / 8 + M.core.ℓ ^ 4 / 128) +
        9 / 4 * ((PtCorr2.cBn : ℝ) * Q1 2 * M.core.cWL) +
        cKAL L M.core.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3) *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ 1 / 2)
    (hs1 : 2 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ≤ M.core.ρ)
    (hs2 : 8 * cM * M.core.ℓ ^ 2 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)
      ≤ 1 / 2)
    (hs3 : PtCorr2.cRho L * (cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ≤ 1)
    (hs4 : 4 * (cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ≤ r₀ ^ 2)
    (hs5 : cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ r₀)
    (hsmall : ∀ j ≤ Nh, max (spinMK L M.core.cg M.core.Ke M.core.KZ M.Kp M.core.KG 0) 0 *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j).1 ≤ 1 / 2)
    (hspl : SplitSmall R.P L R.ρ) (hm0' : 0 < m) (hmL : m ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))))
    (x y : Lam 2 L N) (hx : y ≠ 0) (h1 : 1 ≤ Obs.coal L (0 : Lam 2 L N) y)
    (hj : Obs.coal L (0 : Lam 2 L N) y ≤ Nh)
    {ms r : ℕ} (hk0 : 0 < ms) (hmx : ms < Obs.coal L (0 : Lam 2 L N) x)
    (hmy : ms < Obs.coal L (0 : Lam 2 L N) y)
    (hrk : r ≤ ms) (hblk : blk ms (y - x) = blk ms (0 : Lam 2 L N))
    (hdist : supNorm (y - x) ≤ L ^ (ms - r))
    (hs0 : 0 ≤ M.Kp * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 + zA L m ms))
    (hs : M.Kp * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 + zA L m ms) ≤ 1 / 2)
    (hreg : M.core.A ^ 4 * (cx M.core.κ M.core.cT *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 ^ 3) ≤ 1)
    (hg : M.core.rdtC * (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1) *
      2) ≤ 1 / 1344),
    ∀ (Cδ : ℕ), N ≤ Obs.coal L (0 : Lam 2 L N) y + Cδ → ∀ {KA KR : ℝ},
      M.EqcMidPkg C₁w C₁t C₁v C₁m Λ₁ Λ₂ R m b Nh r₀ x y ms r Cδ KA KR →
    |Pconn L N (1 / b) x - Pconn L N (1 / b) y| ≤
      M.eqcCmid KA KR Cδ *
        M.cddRel M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms) (rpIota 0 0)
          (R.withMsq m).A r * varthJ R m b (b - m) Nh ^ 2 := by
  obtain ⟨C₁w, C₁t, C₁v, C₁m, Λ₁, Λ₂, hC₁w, hC₁t, hC₁v, hC₁m, hT⟩ := M.eqc_mid hcab
  refine ⟨C₁w, C₁t, C₁v, C₁m, Λ₁, Λ₂, hC₁w, hC₁t, hC₁v, hC₁m, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm b hD r₀ hr₀ hr₀1 hJ Kt hK hmT hmA hsmA hs1 hs2
    hs3 hs4 hs5 hsmall hspl hm0' hmL x y hx h1 hj ms r hk0 hmx hmy hrk hblk hdist hs0 hs hreg hg
    Cδ hδ KA KR hpkg
  obtain ⟨kk, ww, hkk, hww, hMR, hrest⟩ := hT R hP hi0 hRℓ hRA hRρ hN3 hNh hm hD hr₀ hr₀1 hJ hK
    hmT hmA hsmA hs1 hs2 hs3 hs4 hs5 hsmall hspl hm0' hmL x y hx h1 hj hk0 hmx hmy hrk hblk hdist
    hs0 hs hreg hg
  obtain ⟨vT, wT, kxT, w2, k2, m0, Q₀, mm, k₁, c₁, hvT, hwT, hkxT, hw2, hk2, hQ0, hQw, hQk, hwait, hw2e, hk2e, hsmT, hm0, h8w, h8t, h8v, h8m, hmAB, hc₁, hmm1, hmmW, hrm, hk1, hk₁, hkt, hmAa, hKA, hKR⟩ :=
    hpkg kk ww hkk hww hMR
  have hmain := hrest hvT hwT hkxT hw2 hk2 hQ0 hQw hQk hwait hw2e hk2e hsmT hm0 h8w h8t h8v h8m Cδ hδ hmAB hc₁ hmm1 hmmW hrm hk1 hk₁ hkt hmAa
  have hN2 : 2 ≤ N := by omega
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hc0 : 0 ≤ M.core.c := by linarith [M.eqc_c_ge R hP hi0 hRℓ hRA hRρ hN2 hNh hm]
  have hε : 0 ≤ M.core.ε := (hD 0 (Nat.zero_le _)).1.le.trans (hD 0 (Nat.zero_le _)).2.1
  have hA0 : 0 ≤ (R.withMsq m).A := (Fact.out : 0 < R.A).le
  have hι : 0 ≤ rpIota 0 0 := by unfold rpIota; positivity
  have hQ0 := M.eqc_cddRel_nonneg r hc0 hε (hD ms (by omega)).1.le (zA_nonneg L hm.1.le ms) hι hA0
  have hV0 : 0 ≤ varthJ R m b (b - m) Nh := Real.rpow_nonneg (div_pos hb (hD Nh le_rfl).1).le _
  have hmono := M.eqcCmid_mono hc0 hKA hKR (show Nh - Obs.coal L (0 : Lam 2 L N) y ≤ Cδ by omega)
  refine hmain.trans ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmono hQ0) (by positivity)

set_option linter.unusedVariables false in
set_option maxHeartbeats 16000000 in
/-- **The top case from the scalar package.** -/
theorem eqc_top_pkg {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN3 : 3 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) {b : ℝ}
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j))
    {r₀ : ℝ} (hr₀ : 0 < r₀) (hr₀1 : r₀ ≤ 1) (hJ : LastJetBd L (M.core.A / 2) r₀)
    {cK0 Kt : ℝ} (hseed : TopSeedAt R Nh m b (b - m) cK0)
    (hK : ‖(m : ℂ) * ((lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).Z *
        zmRaw (R.withMsq m) (Nh + 1)
          (lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).ζ) - 1‖ ≤
      Kt * m * (L : ℝ) ^ (2 * N))
    (hmT : Kt * m * (L : ℝ) ^ (2 * N) ≤ 1 / 2)
    (hmA : 8 * cKAL L M.core.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3 * m * (L : ℝ) ^ (2 * N) ≤ 1)
    (hsmA : (M.core.Cf * (M.core.ℓ ^ 2 / 8 + M.core.ℓ ^ 4 / 128) +
        9 / 4 * ((PtCorr2.cBn : ℝ) * Q1 2 * M.core.cWL) +
        cKAL L M.core.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3) *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ 1 / 2)
    (hs1 : 2 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ≤ M.core.ρ)
    (hs2 : 8 * cM * M.core.ℓ ^ 2 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)
      ≤ 1 / 2)
    (hs3 : PtCorr2.cRho L * (cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ≤ 1)
    (hs4 : 4 * (cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ≤ r₀ ^ 2)
    (hs5 : cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ r₀)
    (hvb : cM * M.core.ℓ ^ 2 * (4 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)) +
      8 * M.core.ℓ ^ 4 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ≤ 1)
    (hwb : 2 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ^ 2) ≤ 1)
    (hsmall : ∀ j ≤ Nh, max (spinMK L M.core.cg M.core.Ke M.core.KZ M.Kp M.core.KG 0) 0 *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j).1 ≤ 1 / 2)
    (y : Lam 2 L N) (hy : y ≠ 0) (hj : Nh + 1 ≤ Obs.coal L (0 : Lam 2 L N) y)
    -- the pair-difference datum
    (hspl : SplitSmall R.P L R.ρ) (x : Lam 2 L N) {ms r : ℕ} (hk0 : 0 < ms) (hkN : ms < Nh)
    (hmx : ms < Obs.coal L (0 : Lam 2 L N) x)
    (hrk : r ≤ ms) (hblk : blk ms (y - x) = blk ms (0 : Lam 2 L N))
    (hdist : supNorm (y - x) ≤ L ^ (ms - r))
    (hsc0 : 0 ≤ M.Kp * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 + zA L m ms))
    (hsc : M.Kp * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 + zA L m ms) ≤ 1 / 2)
    (hreg : M.core.A ^ 4 * (cx M.core.κ M.core.cT * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 ^ 3) ≤ 1)
    (hgms : M.core.rdtC * (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1) * 2) ≤ 1 / 1344) (hcab : 0 < M.k2cab) :
    ∀ {KA KE : ℝ}, M.EqcTopPkg R m b Nh r₀ x y ms r KA KE →
    |Pconn L N (1 / b) x - Pconn L N (1 / b) y| ≤
      M.eqcCtop KA KE *
        M.cddRel M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms) (rpIota 0 0)
          (R.withMsq m).A r * varthJ R m b (b - m) Nh ^ 2 := by
  intro KA KE hpkg
  obtain ⟨kk, ww, hkk, hww, hMR, hrest⟩ := M.fin_conn_diff_top R hP hi0 hRℓ hRA hRρ hN3 hNh hm hD
    hr₀ hr₀1 hJ hseed hK hmT hmA hsmA hs1 hs2 hs3 hs4 hs5 hvb hwb hsmall y hy hj hspl x hk0 hkN hmx
    hrk hblk hdist hsc0 hsc hreg hgms hcab
  obtain ⟨mm, k₁, c₁, k2, Q₀, hc₁, hk2, hmmV, hmmW, hrm, hk1, hk₁, hkt, hQ0, hQw, hQk, hwait, hk2e,
    hsmT, hmAB, hmAa, hKA, hKE⟩ := hpkg kk ww hkk hww hMR
  have hmain := hrest hc₁ hk2 hmmV hmmW hrm hk1 hk₁ hkt hQ0 hQw hQk hwait hk2e hsmT hmAB hmAa
  have hN2 : 2 ≤ N := by omega
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hc0 : 0 ≤ M.core.c := by linarith [M.eqc_c_ge R hP hi0 hRℓ hRA hRρ hN2 hNh hm]
  have hε : 0 ≤ M.core.ε := (hD 0 (Nat.zero_le _)).1.le.trans (hD 0 (Nat.zero_le _)).2.1
  have hA0 : 0 ≤ (R.withMsq m).A := (Fact.out : 0 < R.A).le
  have hι : 0 ≤ rpIota 0 0 := by unfold rpIota; positivity
  have hQ0 := M.eqc_cddRel_nonneg r hc0 hε (hD ms (by omega)).1.le (zA_nonneg L hm.1.le ms) hι hA0
  have hV0 : 0 ≤ varthJ R m b (b - m) Nh := Real.rpow_nonneg (div_pos hb (hD Nh le_rfl).1).le _
  have hg0 := (hD Nh le_rfl).1
  have hg1 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ 1 :=
    (hD Nh le_rfl).2.1.trans M.eps_le
  have e : ‖((Pconn L N (1 / b) x : ℝ) : ℂ) - ((Pconn L N (1 / b) y : ℝ) : ℂ)‖ =
      |Pconn L N (1 / b) x - Pconn L N (1 / b) y| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [e] at hmain
  refine hmain.trans ?_
  have hC0 : 0 ≤ cw4Cmp M 0 := (cw4Cmp_pos M 0).le
  have hX : 0 ≤ cw4Cmp M 0 * M.cddRel M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1
      (zA L m ms) (rpIota 0 0) (R.withMsq m).A r * varthJ R m b (b - m) Nh ^ 2 := by positivity
  set KA0 := M.naKA (M.ctVT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)) (M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm) (M.rptfKx c₁ (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm k₁) r₀ with hKA0
  set KE0 := M.rpKE ((2 * rpIota (M.ctVT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)) (M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm) * M.core.A) ^ (L ^ 2)) r₀ with hKE0
  have h1 : (1 + M.fwKO) * max KA0 0 ≤ max (1 + M.fwKO) 0 * max KA 0 :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (le_max_right _ _)).trans
      (mul_le_mul_of_nonneg_left (max_le_max hKA le_rfl) (le_max_right _ _))
  have h2 : max KE0 0 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ max KE 0 :=
    (mul_le_of_le_one_right (le_max_right _ _) hg1).trans (max_le_max hKE le_rfl)
  have h3 : 9 / 4 * ((1 + M.fwKO) * max KA0 0 + max KE0 0 *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ≤
      9 / 4 * (max (1 + M.fwKO) 0 * max KA 0 + max KE 0) := by linarith
  have := mul_le_mul_of_nonneg_right h3 hX
  refine (le_of_eq (by ring)).trans (this.trans (le_of_eq ?_))
  unfold eqcCtop; ring

end MasterFacts

end

end Spin2
