import Spin2.Cont.ContEqC2

set_option autoImplicit false

/-!
# B3, `r`-dependent form, item (d): the ratio `ϑ_{j}/ϑ_{N_h}` and signs

* **`MasterFacts.eqc_g_succ_le`**: `ǧ_{k+1} ≤ K_g·ǧ_k` (`k < N_h`), `K_g = max(2, 2K₁)`,
  `K₁ = β_L + 4(1 + β_L)max(K_e, β_L/2) + |C_{gu}|` (from the `1/ǧ` recursion of `spinD`);
* **`MasterFacts.eqc_varth_ratio`**: `ϑ_j ≤ K_g^{N_h−j}ϑ_{N_h}` (`j ≤ N_h`);
* `eqc_cddRel_nonneg`, `cw4Cmp_mono`, `eqcKg_one_le`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs.SA Obs.LocObs

variable {L : ℕ} [NeZero L]

theorem cw4Cmp_mono (M : MasterFacts L) {n n' : ℕ} (h : n ≤ n') : cw4Cmp M n ≤ cw4Cmp M n' := by
  unfold cw4Cmp
  have h1 : (15 / 14 : ℝ) ^ (2 * n) ≤ (15 / 14 : ℝ) ^ (2 * n') :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : (8 / 7 : ℝ) ^ n ≤ (8 / 7 : ℝ) ^ n' := pow_le_pow_right₀ (by norm_num) h
  have := Real.exp_pos (8 / 7 * (8 / 3 * (2 / (L : ℝ))))
  have := Real.exp_pos (2 * (M.core.cRel * (4 / betaL L) * M.core.ε))
  gcongr

namespace MasterFacts

variable (M : MasterFacts L)

/-- `K₁ = β_L + 4(1 + β_L)max(K_e, β_L/2) + |C_{gu}|`. -/
def eqcK1 : ℝ :=
  betaL L + 4 * (1 + betaL L) * max M.core.Ke (betaL L / 2) + |Cgu (betaL L) M.core.cg|

/-- `K_g = max(2, 2K₁)`. -/
def eqcKg : ℝ := max 2 (2 * M.eqcK1)

theorem eqcKg_one_le : 1 ≤ M.eqcKg := le_trans (by norm_num) (le_max_left _ _)

theorem eqc_cddRel_nonneg {g z ι A : ℝ} (r : ℕ) (hc : 0 ≤ M.core.c) (hε : 0 ≤ M.core.ε)
    (hg : 0 ≤ g) (hz : 0 ≤ z) (hι : 0 ≤ ι) (hA : 0 ≤ A) :
    0 ≤ M.cddRel M.Kp g z ι A r := by
  obtain ⟨-, -, -, -, -, hcWo, hBk, hcδ, -, -⟩ := M.core.consts_nonneg
  have hβ2 := betaL_ge (show 8 ≤ L by have := M.core.hL49; omega)
  have hβ : 0 ≤ betaL L := by linarith
  have hΓ := M.core.rdtΓ_nonneg hc hε
  have hKp := M.Kp_nonneg
  have : (0 : ℝ) ≤ PtCorr2.csN 2 := Nat.cast_nonneg _
  have : 0 ≤ M.core.cWo := by linarith
  unfold cddRel
  positivity

/-- **`ǧ_{k+1} ≤ K_gǧ_k`** along `D_ε`. -/
theorem eqc_g_succ_le {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) {b μ₀ : ℝ}
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) {k : ℕ} (hk : k < Nh) :
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (k + 1)).1 ≤
      M.eqcKg * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 := by
  have h := (M.spinD N R hP hi0 hRℓ hRA hRρ (by omega) Nh (by omega)).2.2.2.1 m hm b μ₀ hD k hk
  set g := (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 with hgd
  set g' := (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (k + 1)).1 with hg'd
  have hg0 : 0 < g := (hD k hk.le).1
  have hg1 : g ≤ 1 := (hD k hk.le).2.1.trans M.eps_le
  have hg'0 : 0 < g' := (hD (k + 1) hk).1
  have hg'1 : g' ≤ 1 := (hD (k + 1) hk).2.1.trans M.eps_le
  have hβ2 := betaL_ge (show 8 ≤ L by have := M.core.hL49; omega)
  have hβ : 0 ≤ betaL L := by linarith
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by have := M.core.hL49; omega)
  have hmn : m * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1 := by
    have h1 := msq_horizon (L := (L : ℝ)) (by linarith only [hL2]) hm.2 (Nh := Nh) (k := 0)
      (by omega)
    simp only [pow_zero, one_pow, inv_one] at h1
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hm.1.le) h1
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by linarith only [hL2]) (by omega)) 2
  have hz := zA_le_two (by linarith only [hL2]) hmn
  have hz0 := zA_nonneg L hm.1.le k
  set Km := max M.core.Ke (betaL L / 2) with hKmd
  have hKm : 0 ≤ Km := le_trans (by linarith) (le_max_right _ _)
  have hE : 2 * (1 + betaL L) * Km * zA L m k + Cgu (betaL L) M.core.cg * g ≤
      4 * (1 + betaL L) * Km + |Cgu (betaL L) M.core.cg| := by
    have a1 : 2 * (1 + betaL L) * Km * zA L m k ≤ 2 * (1 + betaL L) * Km * 2 :=
      mul_le_mul_of_nonneg_left hz (by positivity)
    have a2 : Cgu (betaL L) M.core.cg * g ≤ |Cgu (betaL L) M.core.cg| := by
      calc Cgu (betaL L) M.core.cg * g ≤ |Cgu (betaL L) M.core.cg| * g :=
            mul_le_mul_of_nonneg_right (le_abs_self _) hg0.le
        _ ≤ |Cgu (betaL L) M.core.cg| * 1 := mul_le_mul_of_nonneg_left hg1 (abs_nonneg _)
        _ = _ := mul_one _
    linarith
  have hlow : 1 / g - M.eqcK1 ≤ 1 / g' := by
    have := (abs_le.1 (h.trans hE)).1
    unfold eqcK1; linarith
  have hK1 : 0 ≤ M.eqcK1 := by unfold eqcK1; positivity
  by_cases hs : M.eqcK1 * g ≤ 1 / 2
  · -- `1/g' ≥ 1/(2g)`
    have h2 : 1 / (2 * g) ≤ 1 / g' := by
      have e : 1 / (2 * g) = 1 / g - 1 / (2 * g) := by field_simp; ring_nf
      have h3 : M.eqcK1 ≤ 1 / (2 * g) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      linarith
    have h4 : g' ≤ 2 * g := by
      rw [div_le_div_iff₀ (by positivity) hg'0] at h2; linarith
    exact h4.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hg0.le)
  · push Not at hs
    have : g' ≤ 2 * M.eqcK1 * g := by linarith
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hg0.le)

/-- `ǧ_n ≤ K_g^{n−k}ǧ_k` for `k ≤ n ≤ N_h`. -/
theorem eqc_g_pow_le {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) {b μ₀ : ℝ}
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) {k : ℕ} :
    ∀ d : ℕ, k + d ≤ Nh → (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (k + d)).1 ≤
      M.eqcKg ^ d * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1
  | 0, _ => by simp
  | d + 1, h => by
    have ih := eqc_g_pow_le R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD (k := k) d (by omega)
    have hs := M.eqc_g_succ_le R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD (k := k + d) (by omega)
    have hK := M.eqcKg_one_le
    rw [show k + (d + 1) = k + d + 1 by omega, pow_succ]
    calc _ ≤ M.eqcKg * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (k + d)).1 := hs
      _ ≤ M.eqcKg * (M.eqcKg ^ d * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1) :=
          mul_le_mul_of_nonneg_left ih (by linarith)
      _ = _ := by ring_nf

/-- **`ϑ_j ≤ K_g^{N_h−j}ϑ_{N_h}`** (`j ≤ N_h`). -/
theorem eqc_varth_ratio {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) {b μ₀ : ℝ}
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) {j : ℕ} (hj : j ≤ Nh) :
    varthJ R m b μ₀ j ≤ M.eqcKg ^ (Nh - j) * varthJ R m b μ₀ Nh := by
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have h := M.eqc_g_pow_le R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD (k := j) (Nh - j) (by omega)
  rw [show j + (Nh - j) = Nh by omega] at h
  set g := (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1
  set gN := (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1
  have hg0 : 0 < g := (hD j hj).1
  have hgN : 0 < gN := (hD Nh le_rfl).1
  have hK := M.eqcKg_one_le
  set Kd := M.eqcKg ^ (Nh - j) with hKd
  have hKd1 : 1 ≤ Kd := one_le_pow₀ hK
  have h1 : b / g ≤ Kd * (b / gN) := by
    rw [div_le_iff₀ hg0]
    have : Kd * (b / gN) * g = b * (Kd * g) / gN := by ring
    rw [this, le_div_iff₀ hgN]
    nlinarith
  unfold varthJ
  calc (b / g) ^ (1 / 3 : ℝ) ≤ (Kd * (b / gN)) ^ (1 / 3 : ℝ) :=
        Real.rpow_le_rpow (div_pos hb hg0).le h1 (by norm_num)
    _ = Kd ^ (1 / 3 : ℝ) * (b / gN) ^ (1 / 3 : ℝ) :=
        Real.mul_rpow (by linarith) (div_pos hb hgN).le
    _ ≤ Kd * (b / gN) ^ (1 / 3 : ℝ) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (div_pos hb hgN).le _)
        calc Kd ^ (1 / 3 : ℝ) ≤ Kd ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hKd1 (by norm_num)
          _ = Kd := Real.rpow_one _

end MasterFacts

end

end Spin2
