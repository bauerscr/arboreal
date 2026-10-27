import Step2.D2.D2HV1
import Step2.D2.D2Tad

/-!
# Homogeneity and the `ℓ¹` form of the bilinear bound

* `bubX_smul_left`, `bubX_smul_right`;
* `bubX_bound1`: `|𝔅x(a, c)| ≤ (∑_{|v|_∞ ≤ R} |a(v)|) (4B₂ + B₄ + R(R B₄ + 2B₃)/2)`;
* `sum_cKer_le`: `∑_{|v|_∞ ≤ R} |cKer R w v| ≤ ∑_x |kern w x|`.
-/

namespace Step2

open Step

noncomputable section

open Finset MeasureTheory Step2.D2 Loc FRD Grassmann

theorem symb_smul (r : ℂ) (a : ℤ × ℤ → ℂ) (j : ℕ) (p : ℂ) :
    symb (r • a) j p = r * symb a j p := by
  unfold symb
  rw [mul_finsum]
  refine finsum_congr fun v => ?_
  simp only [Pi.smul_apply, smul_eq_mul]; ring

theorem bubX_smul_left (r : ℂ) (a c : ℤ × ℤ → ℂ) : bubX (r • a) c = r * bubX a c := by
  unfold bubX
  simp only [symb_smul]
  have e : ∀ (l : List KCoef) (j : ℕ), ∫ p in BZ, trigK l p * (r * symb a j p * symb c j p) =
      r * ∫ p in BZ, trigK l p * (symb a j p * symb c j p) := by
    intro l j
    rw [← integral_const_mul]; congr 1; funext p; ring
  rw [e, e]; ring

theorem bubX_smul_right (r : ℂ) (a c : ℤ × ℤ → ℂ) : bubX a (r • c) = r * bubX a c := by
  rw [bubX_comm, bubX_smul_left, bubX_comm]

theorem bubX_sub_left {a a' c : ℤ × ℤ → ℂ} (ha : Function.HasFiniteSupport a)
    (ha' : Function.HasFiniteSupport a') (hc : Function.HasFiniteSupport c) :
    bubX (a - a') c = bubX a c - bubX a' c := by
  have hn : Function.HasFiniteSupport (-a') := by
    refine Set.Finite.subset ha' (fun v hv => ?_)
    simp only [Function.mem_support, Pi.neg_apply, ne_eq, neg_eq_zero] at hv ⊢; exact hv
  rw [sub_eq_add_neg, bubX_add_left ha hn hc, show -a' = (-1 : ℂ) • a' by simp,
    bubX_smul_left]; ring

theorem bubX_sum_left {ι : Type*} (s : Finset ι) {a : ι → ℤ × ℤ → ℂ}
    (ha : ∀ i, Function.HasFiniteSupport (a i)) {c : ℤ × ℤ → ℂ}
    (hc : Function.HasFiniteSupport c) :
    bubX (∑ i ∈ s, a i) c = ∑ i ∈ s, bubX (a i) c := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [sum_empty]
    have := bubX_smul_left 0 (0 : ℤ × ℤ → ℂ) c
    simpa using this
  | insert i s hi ih =>
    have hs : Function.HasFiniteSupport (∑ i ∈ s, a i) := by
      refine Set.Finite.subset (s.finite_toSet.biUnion fun i _ => ha i) ?_
      intro v hv
      simp only [Function.mem_support, ne_eq, Finset.sum_apply] at hv
      obtain ⟨k, hk, hk'⟩ := exists_ne_zero_of_sum_ne_zero hv
      exact Set.mem_biUnion hk hk'
    rw [sum_insert hi, sum_insert hi, bubX_add_left (ha i) hs hc, ih]

/-- **The `ℓ¹` form of the bilinear bound.** -/
theorem bubX_bound1 {a c : ℤ × ℤ → ℂ} {R : ℕ} (haR : ∀ v, R < nm v → a v = 0)
    (hc : Function.HasFiniteSupport c) {B2 B3 B4 : ℝ}
    (h0 : ∀ u, ‖dd0 c u‖ ≤ B2) (h1 : ∀ u, ‖dd1 c u‖ ≤ B2) (h00 : ∀ u, ‖dd0 (dd0 c) u‖ ≤ B4)
    (hLL : ∀ u, ‖lapZ (lapZ c) u‖ ≤ B4) (hcL : ∀ u, ‖cd0 (lapZ c) u‖ ≤ B3) :
    ‖bubX a c‖ ≤ (∑ v ∈ boxR R, ‖a v‖) * (4 * B2 + B4 + R * (R * B4 + 2 * B3) / 2) := by
  have ha : Function.HasFiniteSupport a := hfs_of_range a haR
  have hB2 : 0 ≤ B2 := (norm_nonneg _).trans (h0 0)
  have hB3 : 0 ≤ B3 := (norm_nonneg _).trans (hcL 0)
  have hB4 : 0 ≤ B4 := (norm_nonneg _).trans (hLL 0)
  rw [bubX_pos a c ha hc]
  have hsupp : ∀ (F : ℤ × ℤ → ℂ), (∀ v, R < nm v → F v = 0) → ∑ᶠ v, F v = ∑ v ∈ boxR R, F v :=
    fun F hF => finsum_eq_sum_of_support_subset _ (fun v hv => by
      simp only [Function.mem_support] at hv
      rw [Finset.mem_coe]
      exact mem_boxR (by by_contra h; push Not at h; exact hv (hF v h)))
  have hmem : ∀ v ∈ boxR R, nm v ≤ R := fun v hv => by
    simp only [boxR, mem_product, Finset.mem_Icc] at hv
    simp only [nm]; omega
  rw [hsupp _ (fun v hv => by rw [haR v hv, zero_mul]),
    hsupp _ (fun v hv => by rw [haR v hv, mul_zero, zero_mul])]
  have t1 : ∀ v : ℤ × ℤ, ‖stK kap0 c (-v.1, -v.2)‖ ≤ 4 * B2 + B4 := by
    intro v
    rw [stK_kap0]
    calc ‖-2 * dd0 c (-v.1, -v.2) + 2 * dd1 c (-v.1, -v.2) - dd0 (dd0 c) (-v.1, -v.2)‖
        ≤ ‖-2 * dd0 c (-v.1, -v.2)‖ + ‖2 * dd1 c (-v.1, -v.2)‖ + ‖dd0 (dd0 c) (-v.1, -v.2)‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ 2 * B2 + 2 * B2 + B4 := by
          rw [norm_mul, norm_mul]
          simp only [norm_neg, Complex.norm_ofNat]
          gcongr
          · exact h0 _
          · exact h1 _
          · exact h00 _
      _ = 4 * B2 + B4 := by ring
  have t2 : ∀ v ∈ boxR R, ‖(v.1 : ℂ) * stK kap2 (mom0 c) (-v.1, -v.2)‖ ≤
      R * (R * B4 + 2 * B3) / 2 := by
    intro v hv
    have hv' := hmem v hv
    have hv1 : ‖((v.1 : ℤ) : ℂ)‖ ≤ R := by
      rw [Complex.norm_intCast]
      have h1 : -(R : ℤ) ≤ v.1 ∧ v.1 ≤ R := by simp only [nm] at hv'; omega
      rw [abs_le]; exact ⟨by exact_mod_cast h1.1, by exact_mod_cast h1.2⟩
    rw [stK_kap2, LL_mom0, norm_mul, norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
    have hw : ‖(((-v.1, -v.2) : ℤ × ℤ).1 : ℂ) * lapZ (lapZ c) (-v.1, -v.2) +
        2 * cd0 (lapZ c) (-v.1, -v.2)‖ ≤ R * B4 + 2 * B3 := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul]
        have h' : ‖(((-v.1, -v.2) : ℤ × ℤ).1 : ℂ)‖ ≤ R := by
          show ‖(((-v.1 : ℤ)) : ℂ)‖ ≤ R
          rw [Int.cast_neg, norm_neg]; exact hv1
        exact mul_le_mul h' (hLL _) (norm_nonneg _) (Nat.cast_nonneg _)
      · rw [norm_mul, Complex.norm_ofNat]; gcongr; exact hcL _
    calc ‖((v.1 : ℤ) : ℂ)‖ * (1 / 2 * ‖(((-v.1, -v.2) : ℤ × ℤ).1 : ℂ) * lapZ (lapZ c) (-v.1, -v.2) +
          2 * cd0 (lapZ c) (-v.1, -v.2)‖) ≤ R * (1 / 2 * (R * B4 + 2 * B3)) := by gcongr
      _ = R * (R * B4 + 2 * B3) / 2 := by ring
  have hT : 0 ≤ (R : ℝ) * (R * B4 + 2 * B3) / 2 := by positivity
  calc ‖∑ v ∈ boxR R, a v * stK kap0 c (-v.1, -v.2) +
        ∑ v ∈ boxR R, (v.1 : ℂ) * a v * stK kap2 (mom0 c) (-v.1, -v.2)‖
      ≤ ∑ v ∈ boxR R, ‖a v‖ * (4 * B2 + B4) +
          ∑ v ∈ boxR R, ‖a v‖ * (R * (R * B4 + 2 * B3) / 2) := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · refine (norm_sum_le _ _).trans (sum_le_sum fun v _ => ?_)
          rw [norm_mul]; exact mul_le_mul_of_nonneg_left (t1 v) (norm_nonneg _)
        · refine (norm_sum_le _ _).trans (sum_le_sum fun v hv => ?_)
          rw [show (v.1 : ℂ) * a v * stK kap2 (mom0 c) (-v.1, -v.2) =
            a v * ((v.1 : ℂ) * stK kap2 (mom0 c) (-v.1, -v.2)) by ring, norm_mul]
          exact mul_le_mul_of_nonneg_left (t2 v hv) (norm_nonneg _)
    _ = (∑ v ∈ boxR R, ‖a v‖) * (4 * B2 + B4 + R * (R * B4 + 2 * B3) / 2) := by
        rw [← sum_mul, ← sum_mul, ← mul_add]

/-! ### Kernel sums -/

variable {L N : ℕ} [NeZero L]

end

end Step2
