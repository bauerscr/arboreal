import Step2.D2.D2HD

/-!
# (S0), (S1) with `L`-independent constants

For `|ζ_i| ≤ ζ̄(L)` (small enough):

* (S0) `‖z ∑_{k<j} ∑_x Γ^int_k(x, 0)‖ ≤ (M₀ + 1) L^{2j}`;
* (S1) `‖z (Γ^int_j(e₀, 0) - Γ^int_j(0, 0))‖ ≤ (M₂ + 1) L^{-2j}`,

with `M₀`, `M₂` independent of `L`, `N`, `m²`, `j`, `ζ`.
-/

namespace Step2

open Step

noncomputable section

open Finset MeasureTheory Step2.D2 Loc FRD Grassmann DressedFRD DressedFRD.Data

theorem S0S1 : ∃ M₀ M₂ : ℝ, 0 ≤ M₀ ∧ 0 ≤ M₂ ∧ ∀ (L : ℕ) [NeZero L], 49 ≤ L →
    ∃ ζbar : ℝ, 0 < ζbar ∧ ∀ (N : ℕ) (msq : ℝ) (ζ : ℕ → ℂ), 1 ≤ N → 0 < msq →
      msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) → (∀ i, ‖ζ i‖ ≤ ζbar) → ∀ j : ℕ, j + 1 < N →
      ‖(dData L N msq ζ).Z (j + 1) *
          ∑ k ∈ range j, ∑ x : Lam 2 L N, DressedFRD.kern ((dData L N msq ζ).Gint k) x‖ ≤
          (M₀ + 1) * ((L : ℝ) ^ j) ^ 2 ∧
        ‖(dData L N msq ζ).Z (j + 1) *
          (DressedFRD.kern ((dData L N msq ζ).Gint j) (unitT 0 : Lam 2 L N) -
            DressedFRD.kern ((dData L N msq ζ).Gint j) 0)‖ ≤ (M₂ + 1) / ((L : ℝ) ^ j) ^ 2 := by
  obtain ⟨M₂, hM₂0, hS1⟩ := first_diff_le
  obtain ⟨M₀, hM₀0, hS0⟩ := zmode_le
  refine ⟨M₀, M₂, hM₀0, hM₂0, fun L _ hL => ?_⟩
  obtain ⟨ζ₀, hζ₀, hζ8, K, hK⟩ := thm_main_frd Pc (d := 2) le_rfl (q := 4) (by norm_num)
    (by omega : 7 ≤ L)
  obtain ⟨cS, hcS, hS⟩ := frd_stdFull Pc (d := 2) le_rfl (by omega : 7 ≤ L) (q := 4)
    (M := 4 + 2 + 1) le_rfl
  set K' := max K 0
  have hK'0 : 0 ≤ K' := le_max_right _ _
  have hKK : K ≤ K' := le_max_left _ _
  set A := 1 + 3 * (K' + M₀) + K'
  have hA : 1 ≤ A := by
    have : 0 ≤ K' + M₀ := by positivity
    simp only [A]; linarith
  refine ⟨min ζ₀ (1 / A), lt_min hζ₀ (by positivity),
    fun N msq ζ hN hm hmN hζb j hjN => ?_⟩
  set D := dData L N msq ζ
  have hζ0 : ∀ i, ‖ζ i‖ ≤ ζ₀ := fun i => (hζb i).trans (min_le_left _ _)
  have hc : ∀ i < N, D.Concl 4 ζ₀ K i := (hK (L ^ N) N msq ζ hN rfl hm hmN).1 hζ0
  have hclose : ∀ i, i + 1 < N →
      snorm (L : ℝ) 4 i (D.Z (i + 1) • D.Gint i - ofR (D.C (i + 1))) ≤ K' * D.Mz (i + 1) :=
    fun i hi => ((hc i (by omega)).close hi).trans
      (mul_le_mul_of_nonneg_right hKK (Mz_nonneg _))
  have hrange : ∀ i, i + 1 < N → 2 * rng (D.Gint i) < L ^ (i + 1) := fun i hi =>
    (hc i (by omega)).range hi
  have hS' : StdFull L N 4 (4 + 2 + 1) D.msq cS D.C := hS (L ^ N) N msq hN rfl hm
  have hCs : ∀ k π s m, D.C k (symmDual π s m) = D.C k m :=
    fun k π s m => frdC_symm Pc msq L N k π s m
  have hζ8' : ∀ i, ‖D.ζ i‖ ≤ 1 / 8 := fun i => (hζ0 i).trans hζ8
  have hZ : ∀ i, D.Z i ≠ 0 := Z_ne_zero (fun i => (hζ8' i).trans (by norm_num))
  set Mz := D.Mz (j + 1)
  have hMz0 : 0 ≤ Mz := Mz_nonneg _
  have hMzA : Mz ≤ 1 / A := Mz_le (by positivity) fun i _ => (hζb i).trans (min_le_right _ _)
  have hAM : A * Mz ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hMzA; linarith
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  constructor
  · have h := S0_dressed D hS' le_rfl (by omega) hζ8' hK'0 hclose hrange hjN hM₀0
      (fun k hk m => hS0 L N (by omega) msq hm k (by omega) m)
    have e : D.Z (j + 1) * ∑ k ∈ range j, ∑ x : Lam 2 L N, DressedFRD.kern (D.Gint k) x =
        wp D j 0 := by
      rw [wp_eq_smul D hZ j, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
      congr 1
      exact sum_congr rfl fun k _ => sum_kern_eq _
    rw [e]
    refine h.trans ?_
    have : 18 / 7 * (K' + M₀) * Mz ≤ 1 := by
      have : 18 / 7 * (K' + M₀) * Mz ≤ A * Mz := by
        apply mul_le_mul_of_nonneg_right _ hMz0
        simp only [A]; linarith
      linarith
    rw [mul_comm (M₀ + 1)]
    gcongr
  · have h := S1_dressed D le_rfl hK'0 hCs hclose hjN (hS1 L N (by omega) msq hm j hjN)
    have e : D.Z (j + 1) * (DressedFRD.kern (D.Gint j) (unitT 0 : Lam 2 L N) -
        DressedFRD.kern (D.Gint j) 0) =
        DressedFRD.kern (Cp D (j + 1)) (dirVec (Sum.inl 0) : Lam 2 L N) -
          DressedFRD.kern (Cp D (j + 1)) 0 := by
      simp only [Cp, show j + 1 - 1 = j by omega, DressedFRD.kern_smul]; rw [mul_sub]; rfl
    rw [e]
    refine h.trans ?_
    have : K' * Mz / 2 ≤ 1 := by
      have : K' * Mz ≤ A * Mz := by
        apply mul_le_mul_of_nonneg_right _ hMz0
        simp only [A]; have : 0 ≤ K' + M₀ := by positivity
        linarith
      linarith
    gcongr

end

end Step2
