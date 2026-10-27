import Psi4.Full
import PtCorr.TwoPtOne

/-!
# Theorem `thm:psi4` (Tier 1) and the proof of Section `sec:proofs`

`thm_psi4`: the statement of `thm_psi4_full` specialised to `L^{-N} ≤ m`, i.e.
`1 ≤ m² L^{2N}`.  Then (`|x|` = `supNorm x`, `θ_N = L^{-κN}`):

* `|ũ_{N,N}| ≤ C|b₀|θ_N`, hence (for `|b₀| ≤ b̄`, `b̄` small) `|ũ| ≤ 1/2` and `1 + ũ ≠ 0`;
* **`e:psi4-suscept`** `∑_x ⟨ψ̄_0ψ_x⟩ = 1/m² + E/m⁴`, `|E| ≤ C|b₀|L^{-(2+κ)N}`;
* for every `x ≠ 0`, with the scale-`N` couplings `λ_a, λ_b, γ_a, γ_b` of the pair
  `(ctr, ctr + x)` (`PtCorr.lamA2` …): `|λ_{a,b} - 1|, |γ_{a,b} - W_N(0)| ≤ C|b₀|`;
* **`e:psi4-00`** `⟨ψ̄_0ψ_0⟩ = γ_a + E`, `|E| ≤ C(L^{-(d-2)N} + |b₀|θ_N)`;
* **`e:psi4-0x`** `⟨ψ̄_0ψ_x⟩ = (-Δ+m²)^{-1}(0,x) + E`, `|E| ≤ C|b₀|(|x|^{-(d-2+κ)} + θ_N)`;
* **`e:psi4-00xx`** `⟨ψ̄_0ψ_0; ψ̄_xψ_x⟩ = -λ_aλ_b (-Δ+m²)^{-1}(0,x)² + E`,
  `|E| ≤ C|b₀|(|x|^{-(2(d-2)+κ)} + θ_N)`.

## Deviations from the paper
* **`e:psi4-00` is false as stated** (`γ + O(b₀L^{-κN})`): at `b₀ = 0`,
  `⟨ψ̄_0ψ_0⟩ = (-Δ+m²)^{-1}(0,0) = W_N(0) + t_N/|Λ|` and the zero-mode term
  `λ t_N/|Λ|/(1+ũ) ≈ (m²|Λ|)^{-1}` carries no factor `b₀`.  We prove the error
  `O(L^{-(d-2)N}) + O(b₀L^{-κN})`, which is `O(L^{-κN})` (no `b₀`) as `κ ≤ d - 2` may be
  assumed (`κ` can always be decreased).
* **Tier 1**: `λ, γ` are the couplings of scale `N` at the points; `λ²` in `e:psi4-00xx` is
  `λ(0)λ(x) = λ_aλ_b`; `γ ≈ W_N(0)` instead of `(-Δ_{ℤ^d}+m²)^{-1}(0,0)`.  No
  continuity of `λ, γ` in `(m², b₀)` is proved.
* `m² > 0` (the paper allows `m² ≥ 0` with `L^{-N} ≤ m`, which forces `m > 0` anyway).
* `b̄` is additionally shrunk (`b̄ ≤ λ̄`, `C_u b̄ ≤ 1/2`) so that `|ũ| ≤ 1/2`.
* Regularity of `s₀^c, a₀^c` as in `thm_psi4_full` (separate, not joint).
-/

namespace Psi4

noncomputable section

open Finset Grassmann Loc Step Obs FRD PtCorr

variable {d : ℕ}

/-! ### Real bookkeeping under `1 ≤ m² L^{2N}` -/

theorem mass_facts (hd : 3 ≤ d) {L N : ℕ} [NeZero L] {msq κ : ℝ} (hκ : 0 < κ)
    (hmsq : 0 < msq) (hm : 1 ≤ msq * (L : ℝ) ^ (2 * N)) {x : Lam d L N} (hx : x ≠ 0) :
    0 ≤ 1 / (msq * Fintype.card (Lam d L N)) ∧
    1 / (msq * Fintype.card (Lam d L N)) ≤ (L : ℝ) ^ (-(((d : ℝ) - 2) * N)) ∧
    (L : ℝ) ^ (-(((d : ℝ) - 2) * N)) ≤ 1 ∧
    (L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N)) ≤ (L : ℝ) ^ (-(κ * N)) ∧
    (L : ℝ) ^ (-(κ * N)) ≤ 1 ∧
    (supNorm x : ℝ) ^ (-κ) * (1 / (msq * Fintype.card (Lam d L N))) ≤
      (supNorm x : ℝ) ^ (-((d : ℝ) - 2 + κ)) ∧
    (supNorm x : ℝ) ^ (-((d : ℝ) - 2 + κ)) * (1 / (msq * Fintype.card (Lam d L N))) ≤
      (supNorm x : ℝ) ^ (-(2 * ((d : ℝ) - 2) + κ)) := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast NeZero.one_le
  have hd2 : (0 : ℝ) ≤ (d : ℝ) - 2 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hc := Suscept.card_lam_pos (d := d) (L := L) N
  have hT0 : 0 ≤ 1 / (msq * Fintype.card (Lam d L N)) := by positivity
  have hTP := T_le_of_mass (d := d) (L := L) (N := N) hmsq hm
  have hr1 : (1 : ℝ) ≤ (supNorm x : ℝ) := by
    have := one_le_supNorm_sub (a := x) (b := 0) hx
    rw [sub_zero] at this
    exact_mod_cast this
  have hr0 : (0 : ℝ) < (supNorm x : ℝ) := by linarith
  have hPr : (L : ℝ) ^ (-(((d : ℝ) - 2) * N)) ≤ (supNorm x : ℝ) ^ (-((d : ℝ) - 2)) := by
    have := pow_N_le (L := L) (N := N) hd2 (a := x) (b := 0) hx
    rw [sub_zero] at this
    rwa [rpow_neg_mul_nat (Nat.cast_nonneg _)]
  have hTr : 1 / (msq * Fintype.card (Lam d L N)) ≤ (supNorm x : ℝ) ^ (-((d : ℝ) - 2)) :=
    hTP.trans hPr
  refine ⟨hT0, hTP, rpow_neg_mul_le_one hL1 hd2 N,
    rpow_neg_mul_mono_one hL1 (by linarith) N, rpow_neg_mul_le_one hL1 hκ.le N, ?_, ?_⟩
  · calc (supNorm x : ℝ) ^ (-κ) * (1 / (msq * Fintype.card (Lam d L N)))
        ≤ (supNorm x : ℝ) ^ (-κ) * (supNorm x : ℝ) ^ (-((d : ℝ) - 2)) :=
          mul_le_mul_of_nonneg_left hTr (by positivity)
      _ = _ := by rw [← Real.rpow_add hr0]; congr 1; ring
  · calc (supNorm x : ℝ) ^ (-((d : ℝ) - 2 + κ)) * (1 / (msq * Fintype.card (Lam d L N)))
        ≤ (supNorm x : ℝ) ^ (-((d : ℝ) - 2 + κ)) * (supNorm x : ℝ) ^ (-((d : ℝ) - 2)) :=
          mul_le_mul_of_nonneg_left hTr (by positivity)
      _ = _ := by rw [← Real.rpow_add hr0]; congr 1; ring

/-! ### Abstract bounds -/

theorem onePt_bound {u τ la E : ℂ} {β θ T P Λ Ce : ℝ} (hβ : 0 ≤ β) (hθ : 0 ≤ θ)
    (hCe : 0 ≤ Ce) (hv : ‖(1 + u)⁻¹‖ ≤ 2)
    (hτ : ‖τ‖ ≤ T) (hTP : T ≤ P) (hla : ‖la‖ ≤ Λ) (hE : ‖E‖ ≤ Ce * β * θ) :
    ‖(la * τ + E) * (1 + u)⁻¹‖ ≤ (2 * Λ + 2 * Ce) * (P + β * θ) := by
  have hΛ : 0 ≤ Λ := (norm_nonneg _).trans hla
  have hP : 0 ≤ P := ((norm_nonneg _).trans hτ).trans hTP
  rw [norm_mul]
  have h1 : ‖la * τ + E‖ ≤ Λ * P + Ce * β * θ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    gcongr
    exact hτ.trans hTP
  have hX : 0 ≤ β * θ := mul_nonneg hβ hθ
  calc ‖la * τ + E‖ * ‖(1 + u)⁻¹‖ ≤ (Λ * P + Ce * β * θ) * 2 := by gcongr
    _ ≤ (2 * Λ + 2 * Ce) * (P + β * θ) := by
      nlinarith [mul_nonneg hΛ hX, mul_nonneg hCe hP]

theorem twoPt_one_bound {u τ E1 E2 : ℂ} {β θ ρ Cu C3 : ℝ} (hβ : 0 ≤ β) (hθ : 0 ≤ θ)
    (hρ : 0 ≤ ρ) (hCu : 0 ≤ Cu) (hC3 : 0 ≤ C3) (hv : ‖(1 + u)⁻¹‖ ≤ 2) (hτ : ‖τ‖ ≤ 1)
    (hu : ‖u‖ ≤ Cu * β * θ) (hE1 : ‖E1‖ ≤ C3 * β * ρ) (hE2 : ‖E2‖ ≤ C3 * β * (ρ + θ)) :
    ‖E1 + (E2 * (1 + u)⁻¹ - τ * u * (1 + u)⁻¹)‖ ≤ (3 * C3 + 2 * Cu) * β * (ρ + θ) := by
  have t2 : ‖E2 * (1 + u)⁻¹‖ ≤ C3 * β * (ρ + θ) * 2 := by
    rw [norm_mul]; gcongr
  have t3 : ‖τ * u * (1 + u)⁻¹‖ ≤ 1 * (Cu * β * θ) * 2 := by
    rw [norm_mul, norm_mul]; gcongr
  have := (norm_add_le _ _).trans (add_le_add hE1 ((norm_sub_le _ _).trans (add_le_add t2 t3)))
  refine this.trans ?_
  have a1 : C3 * β * ρ ≤ C3 * β * (ρ + θ) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC3 hβ)
  have a2 : Cu * β * θ ≤ Cu * β * (ρ + θ) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hCu hβ)
  nlinarith

/-- The conclusion of `thm_psi4` for given `V₀c, λ̄, b̄, C, κ`. -/
abbrev Psi4Body (d L : ℕ) [NeZero L] (V₀c : ℝ → ℂ → Vcoup) (lbar bbar C κ : ℝ) : Prop :=
      (∀ msq b₀, (V₀c msq b₀).b = b₀) ∧
      -- regularity of `s₀^c`, `a₀^c`
      (∀ msq : ℝ, 0 ≤ msq → ∀ b₀ : ℂ, ‖b₀‖ ≤ bbar →
        ‖s₀c V₀c msq b₀‖ ≤ C * ‖b₀‖ ∧ ‖a₀c V₀c msq b₀‖ ≤ C * ‖b₀‖) ∧
      (∀ b₀ : ℂ, ‖b₀‖ ≤ bbar → ContinuousOn (fun msq => s₀c V₀c msq b₀) (Set.Ici 0) ∧
        ContinuousOn (fun msq => a₀c V₀c msq b₀) (Set.Ici 0)) ∧
      (∀ msq : ℝ, 0 ≤ msq →
        DifferentiableOn ℂ (fun b₀ => s₀c V₀c msq b₀) (Metric.ball 0 bbar) ∧
        DifferentiableOn ℂ (fun b₀ => a₀c V₀c msq b₀) (Metric.ball 0 bbar) ∧
        ∀ b₀ ∈ Metric.ball (0 : ℂ) bbar, ‖deriv (fun b => s₀c V₀c msq b) b₀‖ ≤ C ∧
          ‖deriv (fun b => a₀c V₀c msq b) b₀‖ ≤ C) ∧
      ∀ (N : ℕ) (msq : ℝ) (b₀ : ℂ), 1 ≤ N → 0 < msq → 1 ≤ msq * (L : ℝ) ^ (2 * N) →
        ‖b₀‖ ≤ bbar →
        ‖Suscept.utN d L N msq (V₀c msq b₀)‖ ≤ C * ‖b₀‖ * (L : ℝ) ^ (-(κ * N)) ∧
        ‖Suscept.utN d L N msq (V₀c msq b₀)‖ ≤ 1 / 2 ∧
        1 + Suscept.utN d L N msq (V₀c msq b₀) ≠ 0 ∧
        -- `e:psi4-suscept`
        (∃ E : ℂ, ‖E‖ ≤ C * ‖b₀‖ * (L : ℝ) ^ (-((2 + κ) * N)) ∧
          ∑ x : Lam d L N, avgM d L N V₀c msq b₀ (psibar 0 * psi x) =
            1 / (msq : ℂ) + E / (msq : ℂ) ^ 2) ∧
        ∀ x : Lam d L N, x ≠ 0 →
          (‖lamA2 d L N msq (V₀c msq b₀) lbar x - 1‖ ≤ C * ‖b₀‖ ∧
            ‖lamB2 d L N msq (V₀c msq b₀) lbar x - 1‖ ≤ C * ‖b₀‖ ∧
            ‖gamA2 d L N msq (V₀c msq b₀) lbar x -
              (WN (d := d) (n := L ^ N) stdPt msq (L : ℝ) N (0 : Lam d L N) : ℂ)‖ ≤ C * ‖b₀‖ ∧
            ‖gamB2 d L N msq (V₀c msq b₀) lbar x -
              (WN (d := d) (n := L ^ N) stdPt msq (L : ℝ) N (0 : Lam d L N) : ℂ)‖ ≤
                C * ‖b₀‖) ∧
          -- `e:psi4-00` (corrected error)
          (∃ E : ℂ, ‖E‖ ≤ C * ((L : ℝ) ^ (-(((d : ℝ) - 2) * N)) +
              ‖b₀‖ * (L : ℝ) ^ (-(κ * N))) ∧
            avgM d L N V₀c msq b₀ (psibar (0 : Lam d L N) * psi (0 : Lam d L N)) =
              gamA2 d L N msq (V₀c msq b₀) lbar x + E) ∧
          -- `e:psi4-0x`
          (∃ E : ℂ, ‖E‖ ≤ C * ‖b₀‖ * ((supNorm x : ℝ) ^ (-((d : ℝ) - 2 + κ)) +
              (L : ℝ) ^ (-(κ * N))) ∧
            avgM d L N V₀c msq b₀ (psibar (0 : Lam d L N) * psi x) =
              (Suscept.Cov d L N msq 0 x : ℂ) + E) ∧
          -- `e:psi4-00xx`
          (∃ E : ℂ, ‖E‖ ≤ C * ‖b₀‖ * ((supNorm x : ℝ) ^ (-(2 * ((d : ℝ) - 2) + κ)) +
              (L : ℝ) ^ (-(κ * N))) ∧
            avgM d L N V₀c msq b₀
                (psibar (0 : Lam d L N) * psi (0 : Lam d L N) * (psibar x * psi x)) -
              avgM d L N V₀c msq b₀ (psibar (0 : Lam d L N) * psi (0 : Lam d L N)) *
                avgM d L N V₀c msq b₀ (psibar x * psi x) =
              -lamA2 d L N msq (V₀c msq b₀) lbar x * lamB2 d L N msq (V₀c msq b₀) lbar x *
                (Suscept.Cov d L N msq 0 x : ℂ) ^ 2 + E)

set_option maxHeartbeats 4000000 in
/-- **`thm:psi4` for a given `V₀c`** with `FlowData`. -/
theorem thm_psi4_of (hd : 3 ≤ d) {L : ℕ} [NeZero L] {A ℓ₀ lbar C κ : ℝ} {V₀c : ℝ → ℂ → Vcoup}
    (HF : FlowData d L A ℓ₀ V₀c lbar C κ) :
    ∃ bbar Ct : ℝ, 0 < bbar ∧ bbar ≤ lbar ∧ 0 ≤ Ct ∧ Psi4Body d L V₀c lbar bbar Ct κ := by
  obtain ⟨C1, hC1, h1pt⟩ := prop_1pt_of hd HF
  obtain ⟨C2, hC2, h2pt⟩ := lem_2pt_two_of hd HF
  obtain ⟨C3, hC3, h2a⟩ := lem_2pt_one_of hd HF
  have hC := HF.C_nonneg
  have hlbar := HF.lbar_pos
  have hκ := HF.κ_pos
  have hd1 : 1 ≤ d := by omega
  have hL2 := HF.hL2
  have hL0 : (0 : ℝ) < L := Lr_pos
  -- constants
  set Cu : ℝ := C * lbar + (ℓ₀ ^ 2)⁻¹ * (C * (1 + lbar)) with hCu
  have hCu0 : 0 ≤ Cu := by positivity
  set q : ℝ := (ℓ₀ ^ 2)⁻¹ * C * (1 + lbar) with hq
  have hq0 : 0 ≤ q := by positivity
  set Λ : ℝ := 1 + C1 * lbar with hΛ
  set G : ℝ := 2 * ℓ₀ ^ 2 + C1 * lbar with hG
  set K0 : ℝ := 2 * ℓ₀ ^ 2 + 1 with hK0
  set Ce : ℝ := 2 * C1 with hCe
  set B : ℝ := 2 * C1 * lbar with hB
  have hΛ0 : 0 ≤ Λ := by positivity
  have hG0 : 0 ≤ G := by positivity
  have hK00 : 0 ≤ K0 := by positivity
  have hCe0 : 0 ≤ Ce := by positivity
  have hB0 : 0 ≤ B := by positivity
  set Mo : ℝ := 2 * Λ + 2 * Ce with hMo
  set Mx : ℝ := 3 * C3 + 2 * Cu with hMx
  set M : ℝ := Λ * Λ * (2 * Cu) * (2 * K0 + 1) + 4 * C2 + 4 * G * Ce +
    4 * (2 * Λ * Ce + B * Ce) with hM
  set Mt : ℝ := C2 + M with hMt
  have hMo0 : 0 ≤ Mo := by positivity
  have hMx0 : 0 ≤ Mx := by positivity
  have hM0 : 0 ≤ M := by positivity
  have hMt0 : 0 ≤ Mt := by positivity
  set Ct : ℝ := 2 * C + Cu + 2 * q + C1 + Mo + Mx + Mt with hCt
  have h2C : 2 * C ≤ Ct := by rw [hCt]; linarith
  have hC0 : C ≤ Ct := by rw [hCt]; linarith
  have hCut : Cu ≤ Ct := by rw [hCt]; linarith
  have hqt : 2 * q ≤ Ct := by rw [hCt]; linarith
  have hC1t : C1 ≤ Ct := by rw [hCt]; linarith
  have hMot : Mo ≤ Ct := by rw [hCt]; linarith
  have hMxt : Mx ≤ Ct := by rw [hCt]; linarith
  have hMtt : Mt ≤ Ct := by rw [hCt]; linarith
  set bbar : ℝ := min lbar (1 / (2 * Cu + 2)) with hbbar
  have hbbar0 : 0 < bbar := lt_min hlbar (by positivity)
  have hbl : bbar ≤ lbar := min_le_left _ _
  have hbCu : Cu * bbar ≤ 1 / 2 := by
    have h1 : bbar ≤ 1 / (2 * Cu + 2) := min_le_right _ _
    have h2 : Cu * bbar ≤ Cu * (1 / (2 * Cu + 2)) := mul_le_mul_of_nonneg_left h1 hCu0
    refine h2.trans ?_
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    linarith
  obtain ⟨r1, r2, r3⟩ := s₀c_reg HF
  have hball : Metric.ball (0 : ℂ) bbar ⊆ Metric.ball 0 lbar := Metric.ball_subset_ball hbl
  refine ⟨bbar, Ct, hbbar0, hbl, by positivity, HF.hb, ?_, ?_, ?_, ?_⟩
  · intro msq hmsq b₀ hb₀
    obtain ⟨e1, e2⟩ := r1 msq hmsq b₀ (hb₀.trans hbl)
    exact ⟨up2 e1 h2C (norm_nonneg _), up2 e2 hC0 (norm_nonneg _)⟩
  · exact fun b₀ hb₀ => r2 b₀ (hb₀.trans hbl)
  · intro msq hmsq
    obtain ⟨e1, e2, e3⟩ := r3 msq hmsq
    exact ⟨e1.mono hball, e2.mono hball, fun b₀ hb₀ =>
      ⟨(e3 b₀ (hball hb₀)).1.trans h2C, (e3 b₀ (hball hb₀)).2.trans hC0⟩⟩
  intro N msq b₀ hN hmsq hm hb₀
  have hb₀l : ‖b₀‖ ≤ lbar := hb₀.trans hbl
  have hβ := norm_nonneg b₀
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = (L : ℝ) ^ (-(κ * N)) := ⟨_, rfl⟩
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  have hθ1 : θ ≤ 1 := by
    rw [hθ]; exact rpow_neg_mul_le_one (by exact_mod_cast NeZero.one_le) hκ.le N
  have hu : ‖Suscept.utN d L N msq (V₀c msq b₀)‖ ≤ Cu * ‖b₀‖ * θ := by
    rw [hθ]; exact utN_le_of_mass hd1 HF hmsq hm hb₀l
  have hu2 : ‖Suscept.utN d L N msq (V₀c msq b₀)‖ ≤ 1 / 2 := by
    refine hu.trans ?_
    have : Cu * ‖b₀‖ * θ ≤ Cu * bbar * 1 := by gcongr
    linarith
  obtain ⟨hune, hv⟩ := one_add_ne_zero_of_norm_le hu2
  have hgood := HF.good N msq hmsq.le
  refine ⟨by rw [← hθ]; exact up3 hu hCut hβ hθ0, hu2, hune, ?_, fun x hx => ?_⟩
  · -- `e:psi4-suscept`
    refine ⟨-(Suscept.atN d L N msq (V₀c msq b₀) *
      (1 + Suscept.utN d L N msq (V₀c msq b₀))⁻¹), ?_, ?_⟩
    · rw [norm_neg, norm_mul]
      have ha := atN_le (N := N) HF hmsq.le hb₀l
      have hX : 0 ≤ (L : ℝ) ^ (-((2 + κ) * N)) := by positivity
      calc ‖Suscept.atN d L N msq (V₀c msq b₀)‖ * ‖(1 + Suscept.utN d L N msq (V₀c msq b₀))⁻¹‖ ≤
          (ℓ₀ ^ 2)⁻¹ * C * (1 + lbar) * ‖b₀‖ * (L : ℝ) ^ (-((2 + κ) * N)) * 2 := by gcongr
        _ = 2 * q * ‖b₀‖ * (L : ℝ) ^ (-((2 + κ) * N)) := by rw [hq]; ring
        _ ≤ _ := up3 le_rfl hqt hβ hX
    · simp only [avgM_eq (HF.hb msq b₀)]
      have hs : ∑ x : Lam d L N, avg (Suscept.Cov d L N msq) (VE (V₀c msq b₀) univ)
          (psibar 0 * psi x) = 1 / (msq : ℂ) - 1 / (msq : ℂ) ^ 2 *
            (Suscept.atN d L N msq (V₀c msq b₀) / (1 + Suscept.utN d L N msq (V₀c msq b₀))) :=
        Suscept.prop_suscept hd1 HF.hL8 hN hmsq hgood (V₀c msq b₀) hune
      rw [hs]
      have hm0 : (msq : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hmsq.ne'
      field_simp
      ring
  -- the pointwise statements
  obtain ⟨⟨a1, a2, Ea, hEa, hEqa⟩, ⟨b1, b2, Eb, hEb, hEqb⟩⟩ :=
    h1pt N msq b₀ x hN hmsq hb₀l hx hune
  obtain ⟨E₁, E₂, hE₁, hE₂, hEq4⟩ := h2pt N msq b₀ x hN hmsq hb₀l hx hune
  obtain ⟨F₁, F₂, hF₁, hF₂, -, hEq2⟩ := h2a N hN msq hmsq b₀ hb₀l x hx hune
  obtain ⟨hT0, hTP, hP1, hLθ, -, hrT, hrT2⟩ := mass_facts hd hκ hmsq hm hx
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = 1 / (msq * Fintype.card (Lam d L N)) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = (L : ℝ) ^ (-(((d : ℝ) - 2) * N)) := ⟨_, rfl⟩
  obtain ⟨ρ1, hρ1⟩ : ∃ ρ : ℝ, ρ = (supNorm x : ℝ) ^ (-((d : ℝ) - 2 + κ)) := ⟨_, rfl⟩
  obtain ⟨ρ2, hρ2⟩ : ∃ ρ : ℝ, ρ = (supNorm x : ℝ) ^ (-(2 * ((d : ℝ) - 2) + κ)) := ⟨_, rfl⟩
  have hdivT : ∀ y : ℝ, y / (msq * Fintype.card (Lam d L N)) = y * T := fun y => by
    rw [hT, mul_one_div]
  rw [← hT, ← hP] at hTP
  rw [← hP] at hP1
  rw [← hT] at hT0 hrT hrT2
  rw [← hρ1] at hrT hrT2
  rw [← hρ2] at hrT2
  rw [← hθ] at hLθ
  rw [hdivT, ← hθ] at hEa hEb
  rw [hdivT, ← hθ, ← hρ1] at hE₂
  rw [← hρ2] at hE₁
  rw [← hρ1] at hF₁
  rw [hdivT] at hF₂
  have hρ10 : 0 ≤ ρ1 := by rw [hρ1]; positivity
  have hρ20 : 0 ≤ ρ2 := by rw [hρ2]; positivity
  have hτT : ‖PtCorr.tau d L N msq‖ ≤ T := by rw [hT]; exact norm_tau_le hd1 hmsq
  have hτ1 : ‖PtCorr.tau d L N msq‖ ≤ 1 := hτT.trans (hTP.trans hP1)
  have hθT : θ * T ≤ θ := by
    have := mul_le_mul_of_nonneg_left (hTP.trans hP1) hθ0; linarith
  -- `‖W_N(y)‖ ≤ 2 ℓ₀²`
  have hWn : ∀ y : Lam d L N, ‖(WN (d := d) (n := L ^ N) stdPt msq (L : ℝ) N y : ℂ)‖ ≤
      2 * ℓ₀ ^ 2 := by
    intro y
    have h := norm_sum_covAt_le hd hL2 HF.hℓ₀ hgood (0 : Lam d L N) y
    rwa [sum_covAt_ofReal, sum_covAt_eq_WN hmsq hN, sub_zero] at h
  have hWC := WN_eq_Cov hmsq hN x
  have hCvn : ‖(Suscept.Cov d L N msq 0 x : ℂ)‖ ≤ K0 := by
    have : (Suscept.Cov d L N msq 0 x : ℂ) =
        (WN (d := d) (n := L ^ N) stdPt msq (L : ℝ) N x : ℂ) + PtCorr.tau d L N msq := by
      rw [hWC]; ring
    rw [this, hK0]
    exact (norm_add_le _ _).trans (add_le_add (hWn x) hτ1)
  -- couplings
  have hC1b : C1 * ‖b₀‖ ≤ C1 * lbar := mul_le_mul_of_nonneg_left hb₀l hC1
  have hla : ‖lamA2 d L N msq (V₀c msq b₀) lbar x‖ ≤ Λ := by
    have := norm_sub_norm_le (lamA2 d L N msq (V₀c msq b₀) lbar x) 1
    rw [norm_one] at this
    rw [hΛ]; linarith
  have hlb : ‖lamB2 d L N msq (V₀c msq b₀) lbar x‖ ≤ Λ := by
    have := norm_sub_norm_le (lamB2 d L N msq (V₀c msq b₀) lbar x) 1
    rw [norm_one] at this
    rw [hΛ]; linarith
  have hga : ‖gamA2 d L N msq (V₀c msq b₀) lbar x‖ ≤ G := by
    have := norm_sub_norm_le (gamA2 d L N msq (V₀c msq b₀) lbar x)
      (WN (d := d) (n := L ^ N) stdPt msq (L : ℝ) N (0 : Lam d L N) : ℂ)
    have := hWn 0
    rw [hG]; linarith
  have hgb : ‖gamB2 d L N msq (V₀c msq b₀) lbar x‖ ≤ G := by
    have := norm_sub_norm_le (gamB2 d L N msq (V₀c msq b₀) lbar x)
      (WN (d := d) (n := L ^ N) stdPt msq (L : ℝ) N (0 : Lam d L N) : ℂ)
    have := hWn 0
    rw [hG]; linarith
  -- the 1-point errors
  have hEθ : ∀ E : ℂ, ‖E‖ ≤ C1 * ‖b₀‖ * ((L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N)) + θ * T) →
      ‖E‖ ≤ Ce * ‖b₀‖ * θ := by
    intro E hE
    refine hE.trans ?_
    calc C1 * ‖b₀‖ * ((L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N)) + θ * T) ≤ C1 * ‖b₀‖ * (θ + θ) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = Ce * ‖b₀‖ * θ := by rw [hCe]; ring
  have hEa' := hEθ Ea hEa
  have hEb' := hEθ Eb hEb
  refine ⟨⟨up2 a1 hC1t hβ, up2 b1 hC1t hβ, up2 a2 hC1t hβ, up2 b2 hC1t hβ⟩, ?_, ?_, ?_⟩
  · -- `e:psi4-00`
    rw [← hP, ← hθ]
    refine ⟨(lamA2 d L N msq (V₀c msq b₀) lbar x * PtCorr.tau d L N msq + Ea) *
      (1 + Suscept.utN d L N msq (V₀c msq b₀))⁻¹, ?_, ?_⟩
    · have := onePt_bound hβ hθ0 hCe0 hv hτT hTP hla hEa'
      refine this.trans ?_
      have : 0 ≤ P + ‖b₀‖ * θ := by
        have : 0 ≤ P := hT0.trans hTP
        positivity
      exact mul_le_mul_of_nonneg_right hMot this
    · rw [avgM_eq (HF.hb msq b₀), hEqa, div_eq_mul_inv]
  · -- `e:psi4-0x`
    rw [← hρ1, ← hθ]
    have hEq := twoPt_one_eq hune hEq2 hWC
    refine ⟨F₁ + (F₂ * (1 + Suscept.utN d L N msq (V₀c msq b₀))⁻¹ -
      PtCorr.tau d L N msq * Suscept.utN d L N msq (V₀c msq b₀) *
        (1 + Suscept.utN d L N msq (V₀c msq b₀))⁻¹), ?_, ?_⟩
    · have hF2 : ‖F₂‖ ≤ C3 * ‖b₀‖ * (ρ1 + θ) := by
        refine hF₂.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
        linarith
      have := twoPt_one_bound hβ hθ0 hρ10 hCu0 hC3 hv hτ1 hu hF₁ hF2
      refine this.trans ?_
      rw [← hMx]
      exact up3 le_rfl hMxt hβ (by positivity)
    · rw [avgM_eq (HF.hb msq b₀), hEq, add_assoc]
  · -- `e:psi4-00xx`
    rw [← hρ2, ← hθ]
    have htr : avg (Suscept.Cov d L N msq) (VE (V₀c msq b₀) univ) (psibar x * psi x) =
        avg (Suscept.Cov d L N msq) (VE (V₀c msq b₀) univ)
          (psibar (0 : Lam d L N) * psi (0 : Lam d L N)) := by
      have := avg_psibar_psi_diag_transl hmsq hN (V₀c msq b₀) x (0 : Lam d L N)
      rwa [zero_add] at this
    have hEq := trunc_eq hune hEq4 hEqa (htr.trans hEqb) hWC
    simp only [avgM_eq (HF.hb msq b₀)]
    refine ⟨_, ?_, hEq.trans (add_assoc _ _ _)⟩
    have hEBb : ‖Eb‖ ≤ B := by
      refine hEb'.trans ?_
      have : Ce * ‖b₀‖ * θ ≤ Ce * lbar * 1 := by gcongr
      rw [hB]; linarith
    have hE2' : ‖E₂‖ ≤ C2 * ‖b₀‖ * (2 * θ + ρ2) := by
      refine hE₂.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      have : (θ + ρ1) * T = θ * T + ρ1 * T := add_mul _ _ _
      linarith
    have hR := trunc_bound hβ hθ0 hρ20 hCu0 hCe0 hC2 hu hu2 hv hτ1 hla hlb hga hgb hCvn
      hEa' hEb' hEBb hE2'
    rw [← hM] at hR
    refine (norm_add_le _ _).trans ?_
    have e1 : ‖E₁‖ ≤ C2 * ‖b₀‖ * (ρ2 + θ) :=
      hE₁.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
    have e2 : M * ‖b₀‖ * (θ + ρ2) = M * ‖b₀‖ * (ρ2 + θ) := by ring
    rw [e2] at hR
    refine (add_le_add e1 hR).trans ?_
    calc C2 * ‖b₀‖ * (ρ2 + θ) + M * ‖b₀‖ * (ρ2 + θ) = Mt * ‖b₀‖ * (ρ2 + θ) := by
          rw [hMt]; ring
      _ ≤ Ct * ‖b₀‖ * (ρ2 + θ) := up3 le_rfl hMtt hβ (by positivity)

/-- **Theorem `thm:psi4`** (Tier 1, see the module docstring). -/
theorem thm_psi4 (hd : 3 ≤ d) : ∃ (L₀ : ℕ) (Kℓ : ℝ), 0 ≤ Kℓ ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → Odd L →
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∀ ℓ₀ : ℝ, 0 < ℓ₀ →
    Kℓ * (L : ℝ) ^ ((d : ℝ) - 2 + 2 * pPhi d) ≤ ℓ₀ ^ 2 →
    ∃ (V₀c : ℝ → ℂ → Vcoup) (lbar bbar C κ : ℝ), 0 < bbar ∧ bbar ≤ lbar ∧ 0 ≤ C ∧ 0 < κ ∧
      (∀ msq b₀, (V₀c msq b₀).b = b₀) ∧
      -- regularity of `s₀^c`, `a₀^c`
      (∀ msq : ℝ, 0 ≤ msq → ∀ b₀ : ℂ, ‖b₀‖ ≤ bbar →
        ‖s₀c V₀c msq b₀‖ ≤ C * ‖b₀‖ ∧ ‖a₀c V₀c msq b₀‖ ≤ C * ‖b₀‖) ∧
      (∀ b₀ : ℂ, ‖b₀‖ ≤ bbar → ContinuousOn (fun msq => s₀c V₀c msq b₀) (Set.Ici 0) ∧
        ContinuousOn (fun msq => a₀c V₀c msq b₀) (Set.Ici 0)) ∧
      (∀ msq : ℝ, 0 ≤ msq →
        DifferentiableOn ℂ (fun b₀ => s₀c V₀c msq b₀) (Metric.ball 0 bbar) ∧
        DifferentiableOn ℂ (fun b₀ => a₀c V₀c msq b₀) (Metric.ball 0 bbar) ∧
        ∀ b₀ ∈ Metric.ball (0 : ℂ) bbar, ‖deriv (fun b => s₀c V₀c msq b) b₀‖ ≤ C ∧
          ‖deriv (fun b => a₀c V₀c msq b) b₀‖ ≤ C) ∧
      ∀ (N : ℕ) (msq : ℝ) (b₀ : ℂ), 1 ≤ N → 0 < msq → 1 ≤ msq * (L : ℝ) ^ (2 * N) →
        ‖b₀‖ ≤ bbar →
        ‖Suscept.utN d L N msq (V₀c msq b₀)‖ ≤ C * ‖b₀‖ * (L : ℝ) ^ (-(κ * N)) ∧
        ‖Suscept.utN d L N msq (V₀c msq b₀)‖ ≤ 1 / 2 ∧
        1 + Suscept.utN d L N msq (V₀c msq b₀) ≠ 0 ∧
        -- `e:psi4-suscept`
        (∃ E : ℂ, ‖E‖ ≤ C * ‖b₀‖ * (L : ℝ) ^ (-((2 + κ) * N)) ∧
          ∑ x : Lam d L N, avgM d L N V₀c msq b₀ (psibar 0 * psi x) =
            1 / (msq : ℂ) + E / (msq : ℂ) ^ 2) ∧
        ∀ x : Lam d L N, x ≠ 0 →
          (‖lamA2 d L N msq (V₀c msq b₀) lbar x - 1‖ ≤ C * ‖b₀‖ ∧
            ‖lamB2 d L N msq (V₀c msq b₀) lbar x - 1‖ ≤ C * ‖b₀‖ ∧
            ‖gamA2 d L N msq (V₀c msq b₀) lbar x -
              (WN (d := d) (n := L ^ N) stdPt msq (L : ℝ) N (0 : Lam d L N) : ℂ)‖ ≤ C * ‖b₀‖ ∧
            ‖gamB2 d L N msq (V₀c msq b₀) lbar x -
              (WN (d := d) (n := L ^ N) stdPt msq (L : ℝ) N (0 : Lam d L N) : ℂ)‖ ≤
                C * ‖b₀‖) ∧
          -- `e:psi4-00` (corrected error)
          (∃ E : ℂ, ‖E‖ ≤ C * ((L : ℝ) ^ (-(((d : ℝ) - 2) * N)) +
              ‖b₀‖ * (L : ℝ) ^ (-(κ * N))) ∧
            avgM d L N V₀c msq b₀ (psibar (0 : Lam d L N) * psi (0 : Lam d L N)) =
              gamA2 d L N msq (V₀c msq b₀) lbar x + E) ∧
          -- `e:psi4-0x`
          (∃ E : ℂ, ‖E‖ ≤ C * ‖b₀‖ * ((supNorm x : ℝ) ^ (-((d : ℝ) - 2 + κ)) +
              (L : ℝ) ^ (-(κ * N))) ∧
            avgM d L N V₀c msq b₀ (psibar (0 : Lam d L N) * psi x) =
              (Suscept.Cov d L N msq 0 x : ℂ) + E) ∧
          -- `e:psi4-00xx`
          (∃ E : ℂ, ‖E‖ ≤ C * ‖b₀‖ * ((supNorm x : ℝ) ^ (-(2 * ((d : ℝ) - 2) + κ)) +
              (L : ℝ) ^ (-(κ * N))) ∧
            avgM d L N V₀c msq b₀
                (psibar (0 : Lam d L N) * psi (0 : Lam d L N) * (psibar x * psi x)) -
              avgM d L N V₀c msq b₀ (psibar (0 : Lam d L N) * psi (0 : Lam d L N)) *
                avgM d L N V₀c msq b₀ (psibar x * psi x) =
              -lamA2 d L N msq (V₀c msq b₀) lbar x * lamB2 d L N msq (V₀c msq b₀) lbar x *
                (Suscept.Cov d L N msq 0 x : ℂ) ^ 2 + E) := by
  obtain ⟨L₀, Kℓ, hKℓ, H⟩ := setup hd
  refine ⟨L₀, Kℓ, hKℓ, fun L _ hL hLodd => ?_⟩
  obtain ⟨A₀, hA₀, H⟩ := H L hL hLodd
  refine ⟨A₀, hA₀, fun A hA ℓ₀ hℓ₀ hKℓ' => ?_⟩
  obtain ⟨V₀c, lbar, C, κ, HF⟩ := H A hA ℓ₀ hℓ₀ hKℓ'
  obtain ⟨bbar, Ct, hbbar, hbl, hCt, hB⟩ := thm_psi4_of hd HF
  exact ⟨V₀c, lbar, bbar, Ct, κ, hbbar, hbl, hCt, HF.κ_pos, hB⟩

end

end Psi4
