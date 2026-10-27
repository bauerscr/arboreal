import Psi4.Alg

/-!
# Definitions and basic facts for `thm:psi4-full` and `thm:psi4`

For an initial coupling `V₀c : ℝ → ℂ → Vcoup` (the `V₀^c(b₀, m²)` of `thm:flow`):

* `s₀c V₀c m² b₀ = y₀^c + z₀^c`, `a₀c V₀c m² b₀ = a₀^c` (`e:thm-psi4-y0a0`);
* `V₀sp V₀c m² b₀ = (0, s₀, a₀, b₀)`, the coupling after summation by parts;
* `avgM d L N V₀c m² b₀ F = ⟨F⟩_{m², s₀, a₀, b₀}` (`Obs.avg` with `C = (-Δ + m²)^{-1}` and
  `V = V₀sp(Λ)`), and `ZM … = Z_{m², b₀}` (`Obs.Zb`).

By summation by parts (`Psi4.VE_univ_sumParts'`), `V₀sp(Λ) = V₀^c(Λ)` (`VE_V₀sp`), so
`avgM` is the expectation used in `PtCorr` (`avgM_eq`) and `ZM = 𝔼_C[Z_0]` (`ZM_eq`).

Also: the regularity of `s₀c`, `a₀c` (`s₀c_reg`), the bulk bounds at scale `N`
(`bulkN`), `ũ - t_N ã`, `ã`, `ũ` (`utN_sub_le`, `atN_le`, `utN_le_of_mass`), continuity in `m²`
(`cont_bulk`), and `W_N(x) = (-Δ+m²)^{-1}(0,x) - t_N/|Λ|` (`WN_eq_Cov`).
-/

namespace Psi4

noncomputable section

open Finset Grassmann Loc Step Obs FRD PtCorr

/-- `s₀^c = y₀^c + z₀^c`. -/
def s₀c (V₀c : ℝ → ℂ → Vcoup) (msq : ℝ) (b₀ : ℂ) : ℂ := (V₀c msq b₀).y + (V₀c msq b₀).z

/-- `a₀^c`. -/
def a₀c (V₀c : ℝ → ℂ → Vcoup) (msq : ℝ) (b₀ : ℂ) : ℂ := (V₀c msq b₀).a

/-- The coupling `(z, y, a, b) = (0, s₀^c, a₀^c, b₀)` of `e:psi4`. -/
def V₀sp (V₀c : ℝ → ℂ → Vcoup) (msq : ℝ) (b₀ : ℂ) : Vcoup :=
  ⟨0, s₀c V₀c msq b₀, a₀c V₀c msq b₀, b₀⟩

/-- `⟨F⟩_{m², s₀, a₀, b₀}`: the expectation of `e:psi4` with `(s₀, a₀) = (s₀^c, a₀^c)(b₀, m²)`,
i.e. `𝔼_C[e^{-V(Λ)} F]/𝔼_C[e^{-V(Λ)}]`, `C = (-Δ+m²)^{-1}`,
`V(Λ) = ∑_x (s₀ (∇ψ)_x(∇ψ̄)_x + a₀ ψ_xψ̄_x + b₀ …)`. -/
def avgM (d L : ℕ) [NeZero L] (N : ℕ) (V₀c : ℝ → ℂ → Vcoup) (msq : ℝ) (b₀ : ℂ)
    (F : Alg d L N) : ℂ :=
  avg (Suscept.Cov d L N msq) (VE (V₀sp V₀c msq b₀) (univ : Finset (Lam d L N))) F

/-- The partition function `Z_{m², b₀} = 𝔼_C[e^{-V(Λ)}]`. -/
def ZM (d L : ℕ) [NeZero L] (N : ℕ) (V₀c : ℝ → ℂ → Vcoup) (msq : ℝ) (b₀ : ℂ) : ℂ :=
  Zb (Suscept.Cov d L N msq) (VE (V₀sp V₀c msq b₀) (univ : Finset (Lam d L N)))

variable {d L : ℕ} [NeZero L] {N : ℕ} {V₀c : ℝ → ℂ → Vcoup} {msq : ℝ} {b₀ : ℂ}

/-- **Summation by parts** (`thm:psi4-full` (ii)): `V₀^c(Λ) = (0, s₀^c, a₀^c, b₀)(Λ)`. -/
theorem VE_V₀sp (hb : (V₀c msq b₀).b = b₀) :
    VE (V₀c msq b₀) (univ : Finset (Lam d L N)) = VE (V₀sp V₀c msq b₀) univ := by
  rw [VE_univ_sumParts']
  simp only [V₀sp, s₀c, a₀c, hb]

theorem avgM_eq (hb : (V₀c msq b₀).b = b₀) (F : Alg d L N) :
    avgM d L N V₀c msq b₀ F = avg (Suscept.Cov d L N msq) (VE (V₀c msq b₀) univ) F := by
  rw [avgM, ← VE_V₀sp hb]

theorem ZM_eq (hb : (V₀c msq b₀).b = b₀) :
    ZM d L N V₀c msq b₀ = omega (Suscept.Cov d L N msq) (Suscept.Z0 d L N (V₀c msq b₀)) := by
  rw [ZM, ← VE_V₀sp hb]; rfl

/-- `W_N(x) = (-Δ+m²)^{-1}(0,x) - t_N/|Λ|` (`e:WN-def`), with `τ = t_N/|Λ|`. -/
theorem WN_eq_Cov (hmsq : 0 < msq) (hN : 1 ≤ N) (x : Lam d L N) :
    (WN (d := d) (n := L ^ N) stdPt msq (L : ℝ) N x : ℂ) =
      (Suscept.Cov d L N msq 0 x : ℂ) - PtCorr.tau d L N msq := by
  have h1 := sum_covAt_eq hmsq hN (0 : Lam d L N) x
  have h2 := sum_covAt_eq_WN hmsq hN (0 : Lam d L N) x
  rw [sub_zero] at h2
  rw [← h2, h1, PtCorr.tau]
  push_cast; ring

section Flow

variable {A ℓ₀ lbar C κ : ℝ}

/-- Regularity and bounds of `s₀^c`, `a₀^c` (from `thm:flow`): `|s₀|, |a₀| = O(b₀)` uniformly
in `m² ≥ 0`; continuous in `m² ≥ 0` for fixed `b₀`; holomorphic in `b₀` with bounded derivative
for fixed `m² ≥ 0`. -/
theorem s₀c_reg (HF : FlowData d L A ℓ₀ V₀c lbar C κ) :
    (∀ msq : ℝ, 0 ≤ msq → ∀ b₀ : ℂ, ‖b₀‖ ≤ lbar →
      ‖s₀c V₀c msq b₀‖ ≤ 2 * C * ‖b₀‖ ∧ ‖a₀c V₀c msq b₀‖ ≤ C * ‖b₀‖) ∧
    (∀ b₀ : ℂ, ‖b₀‖ ≤ lbar → ContinuousOn (fun msq => s₀c V₀c msq b₀) (Set.Ici 0) ∧
      ContinuousOn (fun msq => a₀c V₀c msq b₀) (Set.Ici 0)) ∧
    (∀ msq : ℝ, 0 ≤ msq →
      DifferentiableOn ℂ (fun b₀ => s₀c V₀c msq b₀) (Metric.ball 0 lbar) ∧
      DifferentiableOn ℂ (fun b₀ => a₀c V₀c msq b₀) (Metric.ball 0 lbar) ∧
      ∀ b₀ ∈ Metric.ball (0 : ℂ) lbar, ‖deriv (fun b => s₀c V₀c msq b) b₀‖ ≤ 2 * C ∧
        ‖deriv (fun b => a₀c V₀c msq b) b₀‖ ≤ C) := by
  refine ⟨fun msq hmsq b₀ hb₀ => ?_, fun b₀ hb₀ => ?_, fun msq hmsq => ?_⟩
  · obtain ⟨e1, e2, e3⟩ := HF.coup_le msq hmsq b₀ hb₀
    refine ⟨(norm_add_le _ _).trans (by linarith), e3⟩
  · obtain ⟨e1, e2, e3⟩ := HF.cont b₀ hb₀
    exact ⟨e2.add e1, e3⟩
  · obtain ⟨e1, e2, e3, e4⟩ := HF.holo msq hmsq
    refine ⟨e2.add e1, e3, fun b₀ hb₀ => ?_⟩
    obtain ⟨f1, f2, f3⟩ := e4 b₀ hb₀
    have hn : Metric.ball (0 : ℂ) lbar ∈ nhds b₀ := Metric.isOpen_ball.mem_nhds hb₀
    have hs : (fun b => s₀c V₀c msq b) = fun b => (V₀c msq b).y + (V₀c msq b).z := rfl
    refine ⟨?_, f3⟩
    rw [hs, show (fun b => (V₀c msq b).y + (V₀c msq b).z) =
      (fun b => (V₀c msq b).y) + (fun b => (V₀c msq b).z) from rfl,
      deriv_add (e2.differentiableAt hn) (e1.differentiableAt hn)]
    exact (norm_add_le _ _).trans (by linarith)

/-- The bulk bounds at the last scale: `‖V_N‖_N ≤ C|b₀|L^{-κN}`, `‖K_N‖_N ≤ C λ̄ |b₀| L^{-κN}`. -/
theorem bulkN (HF : FlowData d L A ℓ₀ V₀c lbar C κ) (hmsq : 0 ≤ msq) (hb₀ : ‖b₀‖ ≤ lbar) :
    (Vnorm (d := d) (L := L) (N := N) N (ellj d L ℓ₀ N)
        (Suscept.VN d L N msq (V₀c msq b₀))).toReal ≤ C * ‖b₀‖ * (L : ℝ) ^ (-(κ * N)) ∧
    (Suscept.KNnorm d L N msq (V₀c msq b₀) (ellj d L ℓ₀ N) A).toReal ≤
      C * lbar * ‖b₀‖ * (L : ℝ) ^ (-(κ * N)) := by
  obtain ⟨hV, hK⟩ := HF.bulk N msq b₀ hmsq hb₀ N le_rfl
  refine ⟨hV, hK.trans ?_⟩
  have : ‖b₀‖ ^ 2 ≤ lbar * ‖b₀‖ := by
    rw [sq]; exact mul_le_mul_of_nonneg_right hb₀ (norm_nonneg _)
  have h0 : 0 ≤ C * (L : ℝ) ^ (-(κ * N)) := mul_nonneg HF.C_nonneg (by positivity)
  nlinarith

/-- **`e:tildeu`**: `|ũ_{N,N} - t_N ã_{N,N}| ≤ C λ̄ |b₀| L^{-κN}`. -/
theorem utN_sub_le (HF : FlowData d L A ℓ₀ V₀c lbar C κ) (hmsq : 0 ≤ msq) (hb₀ : ‖b₀‖ ≤ lbar) :
    ‖Suscept.utN d L N msq (V₀c msq b₀) -
        Suscept.atN d L N msq (V₀c msq b₀) * (Suscept.tNN d L N msq : ℂ)‖ ≤
      C * lbar * ‖b₀‖ * (L : ℝ) ^ (-(κ * N)) :=
  (norm_utN_sub_le HF.hℓ₀ A msq (V₀c msq b₀)).trans (bulkN HF hmsq hb₀).2

/-- `|ã_{N,N}| ≤ ℓ₀^{-2} C (1 + λ̄) |b₀| L^{-(2+κ)N}` (remark after `thm:psi4-full`). -/
theorem atN_le (HF : FlowData d L A ℓ₀ V₀c lbar C κ) (hmsq : 0 ≤ msq) (hb₀ : ‖b₀‖ ≤ lbar) :
    ‖Suscept.atN d L N msq (V₀c msq b₀)‖ ≤
      (ℓ₀ ^ 2)⁻¹ * C * (1 + lbar) * ‖b₀‖ * (L : ℝ) ^ (-((2 + κ) * N)) := by
  have hL0 : (0 : ℝ) < L := Lr_pos
  obtain ⟨hV, hK⟩ := bulkN (N := N) HF hmsq hb₀
  refine (norm_atN_le HF.hℓ₀ A msq (V₀c msq b₀)).trans ?_
  rw [mul_inv, inv_pow_two_mul hL0, rpow_neg_add_mul hL0]
  have hs : (Vnorm (d := d) (L := L) (N := N) N (ellj d L ℓ₀ N)
        (Suscept.VN d L N msq (V₀c msq b₀))).toReal +
      (Suscept.KNnorm d L N msq (V₀c msq b₀) (ellj d L ℓ₀ N) A).toReal ≤
      C * (1 + lbar) * ‖b₀‖ * (L : ℝ) ^ (-(κ * N)) := by linarith
  have hp : 0 ≤ (ℓ₀ ^ 2)⁻¹ * (L : ℝ) ^ (-((2 : ℝ) * N)) := by positivity
  calc (ℓ₀ ^ 2)⁻¹ * (L : ℝ) ^ (-((2 : ℝ) * N)) *
        ((Vnorm (d := d) (L := L) (N := N) N (ellj d L ℓ₀ N)
          (Suscept.VN d L N msq (V₀c msq b₀))).toReal +
        (Suscept.KNnorm d L N msq (V₀c msq b₀) (ellj d L ℓ₀ N) A).toReal)
      ≤ (ℓ₀ ^ 2)⁻¹ * (L : ℝ) ^ (-((2 : ℝ) * N)) *
        (C * (1 + lbar) * ‖b₀‖ * (L : ℝ) ^ (-(κ * N))) := mul_le_mul_of_nonneg_left hs hp
    _ = _ := by ring

/-- `|ũ_{N,N}| ≤ (C λ̄ + ℓ₀^{-2} C (1 + λ̄)) |b₀| L^{-κN}` if `m² L^{2N} ≥ 1`. -/
theorem utN_le_of_mass (hd : 1 ≤ d) (HF : FlowData d L A ℓ₀ V₀c lbar C κ) (hmsq : 0 < msq)
    (hm : 1 ≤ msq * (L : ℝ) ^ (2 * N)) (hb₀ : ‖b₀‖ ≤ lbar) :
    ‖Suscept.utN d L N msq (V₀c msq b₀)‖ ≤
      (C * lbar + (ℓ₀ ^ 2)⁻¹ * (C * (1 + lbar))) * ‖b₀‖ * (L : ℝ) ^ (-(κ * N)) := by
  obtain ⟨hV, hK⟩ := bulkN (N := N) HF hmsq.le hb₀
  refine (norm_utN_le_of_mass hd HF.hℓ₀ A hmsq hm (V₀c msq b₀)).trans ?_
  have hs : (Vnorm (d := d) (L := L) (N := N) N (ellj d L ℓ₀ N)
        (Suscept.VN d L N msq (V₀c msq b₀))).toReal +
      (Suscept.KNnorm d L N msq (V₀c msq b₀) (ellj d L ℓ₀ N) A).toReal ≤
      C * (1 + lbar) * ‖b₀‖ * (L : ℝ) ^ (-(κ * N)) := by linarith
  have hp : 0 ≤ (ℓ₀ ^ 2)⁻¹ := by positivity
  have := mul_le_mul_of_nonneg_left hs hp
  nlinarith

/-- Continuity in `m²` (`thm:psi4-full`): `ã_{N,N}`, `u_N` on `m² ≥ 0`, `ũ_{N,N}` on `m² > 0`,
for fixed `b₀` (from `Suscept.prop_ZNN_cont` and the continuity of `V₀^c` in `m²`). -/
theorem cont_bulk (hd : 1 ≤ d) (HF : FlowData d L A ℓ₀ V₀c lbar C κ) (N : ℕ) (b₀ : ℂ)
    (hb₀ : ‖b₀‖ ≤ lbar) :
    ContinuousOn (fun msq => Suscept.atN d L N msq (V₀c msq b₀)) (Set.Ici 0) ∧
    ContinuousOn (fun msq => Suscept.uN d L N msq (V₀c msq b₀)) (Set.Ici 0) ∧
    ContinuousOn (fun msq => Suscept.utN d L N msq (V₀c msq b₀)) (Set.Ioi 0) := by
  obtain ⟨cz, cy, ca⟩ := HF.cont b₀ hb₀
  have hCV : CV (Set.Ici 0) (fun m => V₀c m b₀) :=
    ⟨cz, cy, ca, by simp only [HF.hb]; exact continuousOn_const⟩
  obtain ⟨-, hu, -, -, hat, hut⟩ := Suscept.prop_ZNN_cont (N := N) hd HF.hL8 (ℓ₀ := ℓ₀)
    (subset_refl _) hCV (fun m hm j hj => HF.good N m hm j hj)
  refine ⟨hat, hu, hut.mono fun m hm => ⟨Set.mem_Ici.2 (le_of_lt hm), hm⟩⟩

end Flow

/-- `1/(m²|Λ|) ≤ L^{-(d-2)N}` if `m² L^{2N} ≥ 1`. -/
theorem T_le_of_mass (hmsq : 0 < msq) (hm : 1 ≤ msq * (L : ℝ) ^ (2 * N)) :
    1 / (msq * Fintype.card (Lam d L N)) ≤ (L : ℝ) ^ (-(((d : ℝ) - 2) * N)) := by
  have hL0 : (0 : ℝ) < L := Lr_pos
  have hc := Suscept.card_lam_pos (d := d) (L := L) N
  rw [div_le_iff₀ (mul_pos hmsq hc), Suscept.card_lam]
  have e1 : (((L ^ N : ℕ) : ℝ)) ^ d = (L : ℝ) ^ (((N * d : ℕ) : ℝ)) := by
    rw [Real.rpow_natCast]; push_cast; ring
  have e2 : (L : ℝ) ^ (2 * N) = (L : ℝ) ^ (((2 * N : ℕ) : ℝ)) := by rw [Real.rpow_natCast]
  have key : (L : ℝ) ^ (-(((d : ℝ) - 2) * N)) * (L : ℝ) ^ (((N * d : ℕ) : ℝ)) =
      (L : ℝ) ^ (((2 * N : ℕ) : ℝ)) := by
    rw [← Real.rpow_add hL0]; congr 1; push_cast; ring
  rw [e1, show (L : ℝ) ^ (-(((d : ℝ) - 2) * N)) * (msq * (L : ℝ) ^ (((N * d : ℕ) : ℝ))) =
    msq * ((L : ℝ) ^ (-(((d : ℝ) - 2) * N)) * (L : ℝ) ^ (((N * d : ℕ) : ℝ))) by ring, key, ← e2]
  exact hm

end

end Psi4
