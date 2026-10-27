import Psi4.Defs
import PtCorr.TwoPtTwo

/-!
# Theorem `thm:psi4-full` (Tier 1: finite `N`, `m² > 0`, couplings of scale `N`)

With `V₀^c` of `thm:flow` (the common flow of `PtCorr.setup`), `s₀^c = y₀^c + z₀^c`,
`a₀^c` (`Psi4.s₀c`, `Psi4.a₀c`) and `⟨·⟩_{m², b₀} = ⟨·⟩_{m², s₀^c, a₀^c, b₀}` (`Psi4.avgM`),
`thm_psi4_full` states:

* **(i)** `|s₀^c|, |a₀^c| ≤ C|b₀|` uniformly in `m² ≥ 0`; continuity in `m² ≥ 0` (fixed `b₀`);
  holomorphy in `b₀ ∈ B(0, b̄)` with derivatives bounded by `C` (fixed `m² ≥ 0`);
* **(ii)** summation by parts `V₀^c(Λ) = (0, s₀^c, a₀^c, b₀)(Λ)`;
* continuity of `ã_{N,N}`, `u_N` on `m² ≥ 0` and of `ũ_{N,N}` on `m² > 0` (fixed `b₀`);
* **`e:tildeu`** `|ũ_{N,N} - t_N ã_{N,N}| ≤ C|b₀|L^{-κN}`, and `|ã_{N,N}| ≤ C|b₀|L^{-(2+κ)N}`;
* for `N ≥ 1`, `m² > 0`, `|b₀| ≤ b̄`:
  **`e:ZuNNaNN`** `Z_{m²,b₀} = e^{-u_N|Λ|}(1 + ũ_{N,N})`, and if `1 + ũ_{N,N} ≠ 0`:
  **`e:suscept-atilde-thm`** `∑_x ⟨ψ̄_0ψ_x⟩ = 1/m² - (1/m⁴) ã/(1+ũ)`;
  for every `x ≠ 0`, with the scale-`N` couplings `λ_a = lamA2 … x`, `λ_b = lamB2 … x`,
  `γ_a = gamA2 … x`, `γ_b = gamB2 … x` of the observable pair `(ctr, ctr + x)`:
  **`e:1pt-b-thm`** `⟨ψ̄_0ψ_0⟩ = γ + (λ t_N/|Λ| + E)/(1+ũ)` (both for `(λ_a, γ_a)` and
  `(λ_b, γ_b)`), `|λ - 1|, |γ - W_N(0)| ≤ C|b₀|`,
  `|E| ≤ C|b₀|(L^{-(d-2+κ)N} + L^{-κN}/(m²|Λ|))`;
  **`e:2pt-b-thm`** `⟨ψ̄_0ψ_0ψ̄_xψ_x⟩ = -λ_aλ_b W_N(x)² + γ_aγ_b
  + (-2λ_aλ_b W_N(x) + λ_aγ_b + λ_bγ_a) (t_N/|Λ|)/(1+ũ) + E₁ + E₂/(1+ũ)`,
  `|E₁| ≤ C|b₀| |x|^{-(2(d-2)+κ)}`,
  `|E₂| ≤ C|b₀|(L^{-(d-2+κ)N} + (L^{-κN} + |x|^{-(d-2+κ)})/(m²|Λ|))`.

## Deviations from the paper
* **Tier 1.** `λ, γ` are the couplings at scale `N` at the points (`PtCorr.lamA2` …), not
  `N`-independent functions; hence `γ ≈ W_N(0)` (torus) instead of `(-Δ_{ℤ^d}+m²)^{-1}(0,0)`,
  and `λ², γ², 2λγ` in `e:2pt-b-thm` become `λ_aλ_b, γ_aγ_b, λ_aγ_b + λ_bγ_a`
  (point-dependent couplings).  Their continuity in `m²`, `b₀` is not proved (not available for the
  observable flow).
* `m² > 0` for all correlation statements (the covariance `(-Δ+m²)^{-1}` needs it), and
  `1 + ũ ≠ 0` is a hypothesis (as in `prop:suscept`).
* Regularity is separate, not joint: continuity in `m²` for fixed `b₀`, holomorphy in `b₀` for
  fixed `m²` (this is what `thm:flow` gives).  For `ã, u_N, ũ` only continuity in `m²` is proved.
* In `e:2pt-b-thm` the error `O(b₀L^{-(d-2+κ)N})` (which contains the constant term `ε(K^{ab}_N)`
  omitted in the paper) comes with the factor `1/(1+ũ)`.
* `|x|` is the sup norm `supNorm x` on the torus.
-/

namespace Psi4

noncomputable section

open Finset Grassmann Loc Step Obs FRD PtCorr

variable {d : ℕ}

theorem up3 {a C1 Ct β X : ℝ} (h : a ≤ C1 * β * X) (hC : C1 ≤ Ct) (hβ : 0 ≤ β) (hX : 0 ≤ X) :
    a ≤ Ct * β * X :=
  h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hβ) hX)

theorem up2 {a C1 Ct β : ℝ} (h : a ≤ C1 * β) (hC : C1 ≤ Ct) (hβ : 0 ≤ β) : a ≤ Ct * β :=
  h.trans (mul_le_mul_of_nonneg_right hC hβ)

/-- The conclusion of `thm_psi4_full` for given `V₀c, b̄, C, κ`. -/
abbrev Psi4FullBody (d L : ℕ) [NeZero L] (V₀c : ℝ → ℂ → Vcoup) (bbar C κ : ℝ) : Prop :=
      (∀ msq b₀, (V₀c msq b₀).b = b₀) ∧
      -- (i) `s₀^c`, `a₀^c`
      (∀ msq : ℝ, 0 ≤ msq → ∀ b₀ : ℂ, ‖b₀‖ ≤ bbar →
        ‖s₀c V₀c msq b₀‖ ≤ C * ‖b₀‖ ∧ ‖a₀c V₀c msq b₀‖ ≤ C * ‖b₀‖) ∧
      (∀ b₀ : ℂ, ‖b₀‖ ≤ bbar → ContinuousOn (fun msq => s₀c V₀c msq b₀) (Set.Ici 0) ∧
        ContinuousOn (fun msq => a₀c V₀c msq b₀) (Set.Ici 0)) ∧
      (∀ msq : ℝ, 0 ≤ msq →
        DifferentiableOn ℂ (fun b₀ => s₀c V₀c msq b₀) (Metric.ball 0 bbar) ∧
        DifferentiableOn ℂ (fun b₀ => a₀c V₀c msq b₀) (Metric.ball 0 bbar) ∧
        ∀ b₀ ∈ Metric.ball (0 : ℂ) bbar, ‖deriv (fun b => s₀c V₀c msq b) b₀‖ ≤ C ∧
          ‖deriv (fun b => a₀c V₀c msq b) b₀‖ ≤ C) ∧
      -- (ii) summation by parts
      (∀ (N : ℕ) (msq : ℝ) (b₀ : ℂ),
        VE (V₀c msq b₀) (univ : Finset (Lam d L N)) = VE (V₀sp V₀c msq b₀) univ) ∧
      -- continuity of `ã_{N,N}`, `u_N`, `ũ_{N,N}` in `m²`
      (∀ (N : ℕ) (b₀ : ℂ), ‖b₀‖ ≤ bbar →
        ContinuousOn (fun msq => Suscept.atN d L N msq (V₀c msq b₀)) (Set.Ici 0) ∧
        ContinuousOn (fun msq => Suscept.uN d L N msq (V₀c msq b₀)) (Set.Ici 0) ∧
        ContinuousOn (fun msq => Suscept.utN d L N msq (V₀c msq b₀)) (Set.Ioi 0)) ∧
      -- `e:tildeu` and the bound on `ã_{N,N}`
      (∀ (N : ℕ) (msq : ℝ) (b₀ : ℂ), 0 ≤ msq → ‖b₀‖ ≤ bbar →
        ‖Suscept.utN d L N msq (V₀c msq b₀) -
            Suscept.atN d L N msq (V₀c msq b₀) * (Suscept.tNN d L N msq : ℂ)‖ ≤
          C * ‖b₀‖ * (L : ℝ) ^ (-(κ * N)) ∧
        ‖Suscept.atN d L N msq (V₀c msq b₀)‖ ≤ C * ‖b₀‖ * (L : ℝ) ^ (-((2 + κ) * N))) ∧
      -- the partition function and the correlation functions
      ∀ (N : ℕ) (msq : ℝ) (b₀ : ℂ), 1 ≤ N → 0 < msq → ‖b₀‖ ≤ bbar →
        ZM d L N V₀c msq b₀ =
          Complex.exp (-(Suscept.uN d L N msq (V₀c msq b₀) * Fintype.card (Lam d L N))) *
            (1 + Suscept.utN d L N msq (V₀c msq b₀)) ∧
        (1 + Suscept.utN d L N msq (V₀c msq b₀) ≠ 0 →
          ∑ x : Lam d L N, avgM d L N V₀c msq b₀ (psibar 0 * psi x) =
            1 / (msq : ℂ) - 1 / (msq : ℂ) ^ 2 *
              (Suscept.atN d L N msq (V₀c msq b₀) / (1 + Suscept.utN d L N msq (V₀c msq b₀))) ∧
          ∀ x : Lam d L N, x ≠ 0 →
            (‖lamA2 d L N msq (V₀c msq b₀) bbar x - 1‖ ≤ C * ‖b₀‖ ∧
              ‖gamA2 d L N msq (V₀c msq b₀) bbar x -
                (WN (d := d) (n := L ^ N) stdPt msq (L : ℝ) N (0 : Lam d L N) : ℂ)‖ ≤
                  C * ‖b₀‖ ∧
              ∃ E : ℂ, ‖E‖ ≤ C * ‖b₀‖ * ((L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N)) +
                  (L : ℝ) ^ (-(κ * N)) / (msq * Fintype.card (Lam d L N))) ∧
                avgM d L N V₀c msq b₀ (psibar (0 : Lam d L N) * psi (0 : Lam d L N)) =
                  gamA2 d L N msq (V₀c msq b₀) bbar x +
                    (lamA2 d L N msq (V₀c msq b₀) bbar x * PtCorr.tau d L N msq + E) /
                      (1 + Suscept.utN d L N msq (V₀c msq b₀))) ∧
            (‖lamB2 d L N msq (V₀c msq b₀) bbar x - 1‖ ≤ C * ‖b₀‖ ∧
              ‖gamB2 d L N msq (V₀c msq b₀) bbar x -
                (WN (d := d) (n := L ^ N) stdPt msq (L : ℝ) N (0 : Lam d L N) : ℂ)‖ ≤
                  C * ‖b₀‖ ∧
              ∃ E : ℂ, ‖E‖ ≤ C * ‖b₀‖ * ((L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N)) +
                  (L : ℝ) ^ (-(κ * N)) / (msq * Fintype.card (Lam d L N))) ∧
                avgM d L N V₀c msq b₀ (psibar (0 : Lam d L N) * psi (0 : Lam d L N)) =
                  gamB2 d L N msq (V₀c msq b₀) bbar x +
                    (lamB2 d L N msq (V₀c msq b₀) bbar x * PtCorr.tau d L N msq + E) /
                      (1 + Suscept.utN d L N msq (V₀c msq b₀))) ∧
            ∃ E₁ E₂ : ℂ,
              ‖E₁‖ ≤ C * ‖b₀‖ * (supNorm x : ℝ) ^ (-(2 * ((d : ℝ) - 2) + κ)) ∧
              ‖E₂‖ ≤ C * ‖b₀‖ * ((L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N)) +
                ((L : ℝ) ^ (-(κ * N)) + (supNorm x : ℝ) ^ (-((d : ℝ) - 2 + κ))) /
                  (msq * Fintype.card (Lam d L N))) ∧
              avgM d L N V₀c msq b₀
                  (psibar (0 : Lam d L N) * psi (0 : Lam d L N) * (psibar x * psi x)) =
                -lamA2 d L N msq (V₀c msq b₀) bbar x * lamB2 d L N msq (V₀c msq b₀) bbar x *
                    (WN (d := d) (n := L ^ N) stdPt msq (L : ℝ) N x : ℂ) ^ 2 +
                  gamA2 d L N msq (V₀c msq b₀) bbar x * gamB2 d L N msq (V₀c msq b₀) bbar x +
                  (-2 * lamA2 d L N msq (V₀c msq b₀) bbar x *
                      lamB2 d L N msq (V₀c msq b₀) bbar x *
                      (WN (d := d) (n := L ^ N) stdPt msq (L : ℝ) N x : ℂ) +
                    lamA2 d L N msq (V₀c msq b₀) bbar x * gamB2 d L N msq (V₀c msq b₀) bbar x +
                    lamB2 d L N msq (V₀c msq b₀) bbar x * gamA2 d L N msq (V₀c msq b₀) bbar x) *
                    PtCorr.tau d L N msq / (1 + Suscept.utN d L N msq (V₀c msq b₀)) +
                  E₁ + E₂ / (1 + Suscept.utN d L N msq (V₀c msq b₀)))

set_option maxHeartbeats 1000000 in
/-- **`thm:psi4-full` for a given `V₀c`** with `FlowData` (`b̄ = λ̄`). -/
theorem thm_psi4_full_of (hd : 3 ≤ d) {L : ℕ} [NeZero L] {A ℓ₀ lbar C κ : ℝ}
    {V₀c : ℝ → ℂ → Vcoup} (HF : FlowData d L A ℓ₀ V₀c lbar C κ) :
    ∃ Ct : ℝ, 0 ≤ Ct ∧ Psi4FullBody d L V₀c lbar Ct κ := by
  obtain ⟨C1, hC1, h1pt⟩ := prop_1pt_of hd HF
  obtain ⟨C2, hC2, h2pt⟩ := lem_2pt_two_of hd HF
  have hC := HF.C_nonneg
  have hlbar := HF.lbar_pos
  have hd1 : 1 ≤ d := by omega
  set Ct : ℝ := 2 * C + C1 + C2 + C * lbar + (ℓ₀ ^ 2)⁻¹ * C * (1 + lbar) with hCt
  have hq : 0 ≤ (ℓ₀ ^ 2)⁻¹ * C * (1 + lbar) := by positivity
  have hCl : 0 ≤ C * lbar := by positivity
  have hC0 : C ≤ Ct := by rw [hCt]; linarith
  have h2C : 2 * C ≤ Ct := by rw [hCt]; linarith
  have hC1t : C1 ≤ Ct := by rw [hCt]; linarith
  have hC2t : C2 ≤ Ct := by rw [hCt]; linarith
  have hClt : C * lbar ≤ Ct := by rw [hCt]; linarith
  have hqt : (ℓ₀ ^ 2)⁻¹ * C * (1 + lbar) ≤ Ct := by rw [hCt]; linarith
  obtain ⟨r1, r2, r3⟩ := s₀c_reg HF
  refine ⟨Ct, by positivity, HF.hb, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro msq hmsq b₀ hb₀
    obtain ⟨e1, e2⟩ := r1 msq hmsq b₀ hb₀
    exact ⟨up2 e1 h2C (norm_nonneg _), up2 e2 hC0 (norm_nonneg _)⟩
  · exact r2
  · intro msq hmsq
    obtain ⟨e1, e2, e3⟩ := r3 msq hmsq
    exact ⟨e1, e2, fun b₀ hb₀ => ⟨(e3 b₀ hb₀).1.trans h2C, (e3 b₀ hb₀).2.trans hC0⟩⟩
  · intro N msq b₀
    exact VE_V₀sp (HF.hb msq b₀)
  · intro N b₀ hb₀
    exact cont_bulk hd1 HF N b₀ hb₀
  · intro N msq b₀ hmsq hb₀
    have hX : 0 ≤ (L : ℝ) ^ (-(κ * N)) := by positivity
    have hX' : 0 ≤ (L : ℝ) ^ (-((2 + κ) * N)) := by positivity
    refine ⟨?_, ?_⟩
    · have := utN_sub_le (N := N) HF hmsq hb₀
      exact up3 this hClt (norm_nonneg _) hX
    · exact up3 (atN_le (N := N) HF hmsq hb₀) hqt (norm_nonneg _) hX'
  · intro N msq b₀ hN hmsq hb₀
    have hgood := HF.good N msq hmsq.le
    refine ⟨?_, fun hu => ?_⟩
    · rw [ZM_eq (HF.hb msq b₀)]
      exact Suscept.EC_Z0 hd1 HF.hL8 hN hmsq hgood (V₀c msq b₀)
    refine ⟨?_, fun x hx => ?_⟩
    · simp only [avgM_eq (HF.hb msq b₀)]
      exact Suscept.prop_suscept hd1 HF.hL8 hN hmsq hgood (V₀c msq b₀) hu
    obtain ⟨⟨a1, a2, Ea, hEa, hEqa⟩, ⟨b1, b2, Eb, hEb, hEqb⟩⟩ :=
      h1pt N msq b₀ x hN hmsq hb₀ hx hu
    obtain ⟨E₁, E₂, hE₁, hE₂, hEq⟩ := h2pt N msq b₀ x hN hmsq hb₀ hx hu
    have hβ := norm_nonneg b₀
    refine ⟨⟨up2 a1 hC1t hβ, up2 a2 hC1t hβ, Ea, up3 hEa hC1t hβ (by positivity), ?_⟩,
      ⟨up2 b1 hC1t hβ, up2 b2 hC1t hβ, Eb, up3 hEb hC1t hβ (by positivity), ?_⟩,
      E₁, E₂, up3 hE₁ hC2t hβ (by positivity), up3 hE₂ hC2t hβ (by positivity), ?_⟩
    · rw [avgM_eq (HF.hb msq b₀)]; exact hEqa
    · rw [avgM_eq (HF.hb msq b₀)]; exact hEqb
    · rw [avgM_eq (HF.hb msq b₀)]; exact hEq

/-- **Theorem `thm:psi4-full`** (Tier 1, see the module docstring). -/
theorem thm_psi4_full (hd : 3 ≤ d) : ∃ (L₀ : ℕ) (Kℓ : ℝ), 0 ≤ Kℓ ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → Odd L →
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∀ ℓ₀ : ℝ, 0 < ℓ₀ →
    Kℓ * (L : ℝ) ^ ((d : ℝ) - 2 + 2 * pPhi d) ≤ ℓ₀ ^ 2 →
    ∃ (V₀c : ℝ → ℂ → Vcoup) (bbar C κ : ℝ), 0 < bbar ∧ 0 ≤ C ∧ 0 < κ ∧
      (∀ msq b₀, (V₀c msq b₀).b = b₀) ∧
      -- (i) `s₀^c`, `a₀^c`
      (∀ msq : ℝ, 0 ≤ msq → ∀ b₀ : ℂ, ‖b₀‖ ≤ bbar →
        ‖s₀c V₀c msq b₀‖ ≤ C * ‖b₀‖ ∧ ‖a₀c V₀c msq b₀‖ ≤ C * ‖b₀‖) ∧
      (∀ b₀ : ℂ, ‖b₀‖ ≤ bbar → ContinuousOn (fun msq => s₀c V₀c msq b₀) (Set.Ici 0) ∧
        ContinuousOn (fun msq => a₀c V₀c msq b₀) (Set.Ici 0)) ∧
      (∀ msq : ℝ, 0 ≤ msq →
        DifferentiableOn ℂ (fun b₀ => s₀c V₀c msq b₀) (Metric.ball 0 bbar) ∧
        DifferentiableOn ℂ (fun b₀ => a₀c V₀c msq b₀) (Metric.ball 0 bbar) ∧
        ∀ b₀ ∈ Metric.ball (0 : ℂ) bbar, ‖deriv (fun b => s₀c V₀c msq b) b₀‖ ≤ C ∧
          ‖deriv (fun b => a₀c V₀c msq b) b₀‖ ≤ C) ∧
      -- (ii) summation by parts
      (∀ (N : ℕ) (msq : ℝ) (b₀ : ℂ),
        VE (V₀c msq b₀) (univ : Finset (Lam d L N)) = VE (V₀sp V₀c msq b₀) univ) ∧
      -- continuity of `ã_{N,N}`, `u_N`, `ũ_{N,N}` in `m²`
      (∀ (N : ℕ) (b₀ : ℂ), ‖b₀‖ ≤ bbar →
        ContinuousOn (fun msq => Suscept.atN d L N msq (V₀c msq b₀)) (Set.Ici 0) ∧
        ContinuousOn (fun msq => Suscept.uN d L N msq (V₀c msq b₀)) (Set.Ici 0) ∧
        ContinuousOn (fun msq => Suscept.utN d L N msq (V₀c msq b₀)) (Set.Ioi 0)) ∧
      -- `e:tildeu` and the bound on `ã_{N,N}`
      (∀ (N : ℕ) (msq : ℝ) (b₀ : ℂ), 0 ≤ msq → ‖b₀‖ ≤ bbar →
        ‖Suscept.utN d L N msq (V₀c msq b₀) -
            Suscept.atN d L N msq (V₀c msq b₀) * (Suscept.tNN d L N msq : ℂ)‖ ≤
          C * ‖b₀‖ * (L : ℝ) ^ (-(κ * N)) ∧
        ‖Suscept.atN d L N msq (V₀c msq b₀)‖ ≤ C * ‖b₀‖ * (L : ℝ) ^ (-((2 + κ) * N))) ∧
      -- the partition function and the correlation functions
      ∀ (N : ℕ) (msq : ℝ) (b₀ : ℂ), 1 ≤ N → 0 < msq → ‖b₀‖ ≤ bbar →
        ZM d L N V₀c msq b₀ =
          Complex.exp (-(Suscept.uN d L N msq (V₀c msq b₀) * Fintype.card (Lam d L N))) *
            (1 + Suscept.utN d L N msq (V₀c msq b₀)) ∧
        (1 + Suscept.utN d L N msq (V₀c msq b₀) ≠ 0 →
          ∑ x : Lam d L N, avgM d L N V₀c msq b₀ (psibar 0 * psi x) =
            1 / (msq : ℂ) - 1 / (msq : ℂ) ^ 2 *
              (Suscept.atN d L N msq (V₀c msq b₀) / (1 + Suscept.utN d L N msq (V₀c msq b₀))) ∧
          ∀ x : Lam d L N, x ≠ 0 →
            (‖lamA2 d L N msq (V₀c msq b₀) bbar x - 1‖ ≤ C * ‖b₀‖ ∧
              ‖gamA2 d L N msq (V₀c msq b₀) bbar x -
                (WN (d := d) (n := L ^ N) stdPt msq (L : ℝ) N (0 : Lam d L N) : ℂ)‖ ≤
                  C * ‖b₀‖ ∧
              ∃ E : ℂ, ‖E‖ ≤ C * ‖b₀‖ * ((L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N)) +
                  (L : ℝ) ^ (-(κ * N)) / (msq * Fintype.card (Lam d L N))) ∧
                avgM d L N V₀c msq b₀ (psibar (0 : Lam d L N) * psi (0 : Lam d L N)) =
                  gamA2 d L N msq (V₀c msq b₀) bbar x +
                    (lamA2 d L N msq (V₀c msq b₀) bbar x * PtCorr.tau d L N msq + E) /
                      (1 + Suscept.utN d L N msq (V₀c msq b₀))) ∧
            (‖lamB2 d L N msq (V₀c msq b₀) bbar x - 1‖ ≤ C * ‖b₀‖ ∧
              ‖gamB2 d L N msq (V₀c msq b₀) bbar x -
                (WN (d := d) (n := L ^ N) stdPt msq (L : ℝ) N (0 : Lam d L N) : ℂ)‖ ≤
                  C * ‖b₀‖ ∧
              ∃ E : ℂ, ‖E‖ ≤ C * ‖b₀‖ * ((L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N)) +
                  (L : ℝ) ^ (-(κ * N)) / (msq * Fintype.card (Lam d L N))) ∧
                avgM d L N V₀c msq b₀ (psibar (0 : Lam d L N) * psi (0 : Lam d L N)) =
                  gamB2 d L N msq (V₀c msq b₀) bbar x +
                    (lamB2 d L N msq (V₀c msq b₀) bbar x * PtCorr.tau d L N msq + E) /
                      (1 + Suscept.utN d L N msq (V₀c msq b₀))) ∧
            ∃ E₁ E₂ : ℂ,
              ‖E₁‖ ≤ C * ‖b₀‖ * (supNorm x : ℝ) ^ (-(2 * ((d : ℝ) - 2) + κ)) ∧
              ‖E₂‖ ≤ C * ‖b₀‖ * ((L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N)) +
                ((L : ℝ) ^ (-(κ * N)) + (supNorm x : ℝ) ^ (-((d : ℝ) - 2 + κ))) /
                  (msq * Fintype.card (Lam d L N))) ∧
              avgM d L N V₀c msq b₀
                  (psibar (0 : Lam d L N) * psi (0 : Lam d L N) * (psibar x * psi x)) =
                -lamA2 d L N msq (V₀c msq b₀) bbar x * lamB2 d L N msq (V₀c msq b₀) bbar x *
                    (WN (d := d) (n := L ^ N) stdPt msq (L : ℝ) N x : ℂ) ^ 2 +
                  gamA2 d L N msq (V₀c msq b₀) bbar x * gamB2 d L N msq (V₀c msq b₀) bbar x +
                  (-2 * lamA2 d L N msq (V₀c msq b₀) bbar x *
                      lamB2 d L N msq (V₀c msq b₀) bbar x *
                      (WN (d := d) (n := L ^ N) stdPt msq (L : ℝ) N x : ℂ) +
                    lamA2 d L N msq (V₀c msq b₀) bbar x * gamB2 d L N msq (V₀c msq b₀) bbar x +
                    lamB2 d L N msq (V₀c msq b₀) bbar x * gamA2 d L N msq (V₀c msq b₀) bbar x) *
                    PtCorr.tau d L N msq / (1 + Suscept.utN d L N msq (V₀c msq b₀)) +
                  E₁ + E₂ / (1 + Suscept.utN d L N msq (V₀c msq b₀))) := by
  obtain ⟨L₀, Kℓ, hKℓ, H⟩ := setup hd
  refine ⟨L₀, Kℓ, hKℓ, fun L _ hL hLodd => ?_⟩
  obtain ⟨A₀, hA₀, H⟩ := H L hL hLodd
  refine ⟨A₀, hA₀, fun A hA ℓ₀ hℓ₀ hKℓ' => ?_⟩
  obtain ⟨V₀c, lbar, C, κ, HF⟩ := H A hA ℓ₀ hℓ₀ hKℓ'
  obtain ⟨Ct, hCt, hB⟩ := thm_psi4_full_of hd HF
  exact ⟨V₀c, lbar, Ct, κ, HF.lbar_pos, hCt, HF.κ_pos, hB⟩

end

end Psi4
