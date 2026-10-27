import Step2.D2.D2HV5

/-!
# Inputs for the dressing of the bubble: derivative bounds and kernel sums

* `dopB w M ρ`: `|∇^α kern w| ≤ M ρ^{-|α|}` for `|α| ≤ 4`;
* `dopB_of_snorm`, `dopB_of_S4a`, `dopB_add`, `dopB_smul`;
* `cKer_zero_of_rng`, `sum_box_le`: the `ℓ¹` norm of `cKer` over its box;
* `kern_sum_le`: `∑_x |kern w x| ≤ (L^k)² M` if `2 rng w < L^k` and `|kern w| ≤ M`.
-/

namespace Step2

open Step

noncomputable section

open Finset MeasureTheory Step2.D2 Loc FRD Grassmann DressedFRD

variable {L N : ℕ} [NeZero L]

local notation "Λ2" => Lam 2 L N

/-- Derivative bounds at scale `ρ` up to order `4`. -/
def dopB (w : DressedFRD.Sym 2 (L ^ N)) (M ρ : ℝ) : Prop :=
  ∀ α : Dir 2 → ℕ, Grassmann.mabs α ≤ 4 → ∀ x : Λ2,
    ‖dop α (DressedFRD.kern w) x‖ ≤ M / ρ ^ Grassmann.mabs α

theorem dopB_of_snorm {w : DressedFRD.Sym 2 (L ^ N)} {q s : ℕ} (hq : 4 ≤ q) {B : ℝ}
    (hw : snorm (L : ℝ) q s w ≤ B) : dopB w B ((L : ℝ) ^ s) := by
  intro α hα x
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  refine (norm_dop_kern_le (q := q) (s := s) hL0 (by omega) w x).trans ?_
  have hw' : (wgt 2 (L : ℝ) s α)⁻¹ * snorm (L : ℝ) q s w ≤ (wgt 2 (L : ℝ) s α)⁻¹ * B :=
    mul_le_mul_of_nonneg_left hw (inv_nonneg.2 (wgt_pos hL0 s α).le)
  refine hw'.trans (le_of_eq ?_)
  have e1 : wgt 2 (L : ℝ) s α = ((L : ℝ) ^ s) ^ (Grassmann.mabs α) := by
    unfold wgt
    rw [← Real.rpow_natCast ((L : ℝ) ^ s), ← Real.rpow_natCast (L : ℝ) s,
      ← Real.rpow_mul hL0.le]
    congr 1
    simp
  rw [e1, div_eq_inv_mul]

theorem dopB_add {w w' : DressedFRD.Sym 2 (L ^ N)} {M M' ρ : ℝ} (h : dopB w M ρ)
    (h' : dopB w' M' ρ) : dopB (w + w') (M + M') ρ := by
  intro α hα x
  have e : dop α (DressedFRD.kern (w + w')) x =
      dop α (DressedFRD.kern w) x + dop α (DressedFRD.kern w') x := by
    rw [DressedFRD.dop_kern, DressedFRD.dop_kern, DressedFRD.dop_kern, ← DressedFRD.kern_add]
    congr 1; funext m; simp [mul_add]
  rw [e, add_div]
  exact (norm_add_le _ _).trans (add_le_add (h α hα x) (h' α hα x))

theorem dopB_mono {w : DressedFRD.Sym 2 (L ^ N)} {M M' ρ : ℝ} (h : dopB w M ρ) (hMM : M ≤ M')
    (hρ : 0 < ρ) : dopB w M' ρ := fun α hα x =>
  (h α hα x).trans (div_le_div_of_nonneg_right hMM (by positivity))

theorem cKer_zero_of_rng {R : ℕ} {w : DressedFRD.Sym 2 (L ^ N)} (hn : 2 * R < L ^ N) {v : ℤ × ℤ}
    (hv : DressedFRD.rng w < nm v) : cKer R w v = 0 := by
  unfold cKer
  split_ifs with h
  · exact DressedFRD.kern_eq_zero_of_rng_lt (by rw [supNorm_prj_zd (by omega)]; exact hv)
  · rfl

/-- `∑_x |kern w x| ≤ (L^k)² M` if `2 rng w < L^k` and `|kern w| ≤ M`. -/
theorem kern_sum_le {w : DressedFRD.Sym 2 (L ^ N)} {k : ℕ} (hr : 2 * DressedFRD.rng w < L ^ k)
    {M : ℝ} (hM : ∀ x, ‖DressedFRD.kern w x‖ ≤ M) :
    ∑ x : Λ2, ‖DressedFRD.kern w x‖ ≤ ((L : ℝ) ^ k) ^ 2 * M := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  refine (sum_norm_ball_le (d := 2) (R := DressedFRD.rng w)
    (fun x hx => DressedFRD.kern_eq_zero_of_rng_lt hx) hM).trans ?_
  have h1 : ((2 * DressedFRD.rng w + 1 : ℕ) : ℝ) ≤ (L : ℝ) ^ k := by exact_mod_cast hr
  have h2 : ((2 * DressedFRD.rng w + 1 : ℕ) : ℝ) ^ 2 ≤ ((L : ℝ) ^ k) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  push_cast at h2
  exact mul_le_mul_of_nonneg_right h2 hM0

/-- The `ℓ¹` norm of the truncated kernel over its box. -/
theorem sum_box_le {R R' : ℕ} {w : DressedFRD.Sym 2 (L ^ N)} (hn : 2 * R < L ^ N)
    (hR' : R' ≤ R) :
    ∑ v ∈ boxR R', ‖cKer R w v‖ ≤ ∑ x : Λ2, ‖DressedFRD.kern w x‖ := by
  have hmem : ∀ v ∈ boxR R', nm v ≤ R' := fun v hv => by
    simp only [boxR, mem_product, Finset.mem_Icc] at hv
    simp only [nm]; omega
  have e : ∑ v ∈ boxR R', ‖cKer R w v‖ =
      ∑ v ∈ boxR R', ‖DressedFRD.kern w (prj (zd v) : Λ2)‖ :=
    sum_congr rfl fun v hv => by unfold cKer; rw [if_pos ((hmem v hv).trans hR')]
  rw [e, ← sum_image (f := fun x : Λ2 => ‖DressedFRD.kern w x‖)
    (g := fun v => (prj (zd v) : Λ2)) (fun v hv v' hv' h => by
      have h1 := rep_prj_zd (L := L) (N := N) v (by have := hmem v hv; omega)
      have h2 := rep_prj_zd (L := L) (N := N) v' (by have := hmem v' hv'; omega)
      simp only at h
      rw [← h1, ← h2, h])]
  exact sum_le_univ_sum_of_nonneg fun x => norm_nonneg _

/-- **The bilinear bound in the form used for the dressing.** If `2 rng a < L^{k}` with
`R' = L^k ≤ R`, and `c` has derivative bounds `M` at scale `ρ`, then
`|𝔅x(cKer a, cKer c)| ≤ (∑_x |kern a|) (M/ρ²)(4 + 4/ρ² + 2(R'/ρ)² + 4R'/ρ)`. -/
theorem bubX_dop {R : ℕ} {a c : DressedFRD.Sym 2 (L ^ N)} (hn : 2 * (R + 4) < L ^ N)
    (hcR : DressedFRD.rng c ≤ R) {R' : ℕ} (haR : DressedFRD.rng a ≤ R') (hR' : R' ≤ R)
    {M ρ : ℝ} (hρ : 0 < ρ) (hc : dopB c M ρ) :
    ‖bubX (cKer R a) (cKer R c)‖ ≤ (∑ x : Λ2, ‖DressedFRD.kern a x‖) *
      (4 * (M / ρ ^ 2) + 4 * M / ρ ^ 4 + R' * (R' * (4 * M / ρ ^ 4) + 2 * (4 * M / ρ ^ 3)) / 2) := by
  have hops := cKer_opsB hcR hn hρ hc
  have hb := bubX_bound1' (a := cKer R a) (R := R') (fun v hv => cKer_zero_of_rng (by omega)
    (by omega)) (cKer_hfs R c) hops
  refine hb.trans ?_
  have hM0 : 0 ≤ M := by
    have := hc 0 (by simp [Grassmann.mabs]) 0
    simp [Grassmann.mabs] at this
    exact (norm_nonneg _).trans this
  have hbr : 0 ≤ 4 * (M / ρ ^ 2) + 4 * M / ρ ^ 4 + R' * (R' * (4 * M / ρ ^ 4) + 2 * (4 * M / ρ ^ 3)) / 2 :=
    by positivity
  exact mul_le_mul_of_nonneg_right (sum_box_le (by omega) hR') hbr

end

end Step2
