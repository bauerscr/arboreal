import Step2.Lip.FlowLipCoup

/-!
# Complex field rescalings (Lipschitz bounds, part 7)

* `tNorm_sig_unit`: `‖σ_ω F‖ = ‖F‖` for `|ω| = 1` (phase invariance);
* `tNorm_sig_cscale`: `‖σ_a F‖_{T(ℓ)} = ‖F‖_{T(|a| ℓ)}` for `a ≠ 0`;
* `tNorm_sig_csub_le`: `‖σ_a F - σ_b F‖ ≤ (|a - b|/τ) ‖F‖` for `|a|, |b| ≤ 1 - τ`;

and the versions for block families (`Fnorm`) and activities (`Knorm`).
-/

namespace Step2

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD

section Gen

variable {X : Type*} [DecidableEq X] [Fintype X] {E : Type*} [Fintype E] [DecidableEq E]
  [AddAction (E → ℕ) X] {p : ℕ} {h ℓ : ℝ}

/-- `‖aⁿ - bⁿ‖ ≤ ‖a - b‖/τ` for `‖a‖, ‖b‖ ≤ 1 - τ`. -/
theorem norm_pow_sub_pow_le {a b : ℂ} {τ : ℝ} (hτ : 0 < τ) (ha1 : ‖a‖ ≤ 1 - τ)
    (hb1 : ‖b‖ ≤ 1 - τ) (n : ℕ) : ‖a ^ n - b ^ n‖ ≤ ‖a - b‖ / τ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp; positivity
  set x := 1 - τ with hx
  have hx0 : 0 ≤ x := (norm_nonneg a).trans ha1
  have hx1 : x ≤ 1 := by linarith
  have hsum : ‖∑ i ∈ range n, a ^ i * b ^ (n - 1 - i)‖ ≤ n * x ^ (n - 1) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i ∈ range n, ‖a ^ i * b ^ (n - 1 - i)‖ ≤ ∑ _i ∈ range n, x ^ (n - 1) := by
          refine sum_le_sum fun i hi => ?_
          have hi' := mem_range.1 hi
          rw [norm_mul, norm_pow, norm_pow]
          calc ‖a‖ ^ i * ‖b‖ ^ (n - 1 - i) ≤ x ^ i * x ^ (n - 1 - i) := by
                gcongr
            _ = x ^ (n - 1) := by rw [← pow_add]; congr 1; omega
      _ = n * x ^ (n - 1) := by rw [sum_const, card_range, nsmul_eq_mul]
  have hkey : (n : ℝ) * x ^ (n - 1) * τ ≤ 1 := by
    have h := pow_mul_one_sub_le hx0 hx1 (n - 1)
    have hn1 : ((n - 1 : ℕ) : ℝ) + 1 = n := by rw [Nat.cast_sub hn]; push_cast; ring
    have hτx : τ = 1 - x := by rw [hx]; ring
    rw [hτx, ← hn1]
    have := pow_nonneg hx0 (n - 1 + 1)
    linarith
  have e := (Commute.all a b).geom_sum₂_mul n
  rw [← e, norm_mul, le_div_iff₀ hτ]
  calc ‖∑ i ∈ range n, a ^ i * b ^ (n - 1 - i)‖ * ‖a - b‖ * τ
      ≤ (n * x ^ (n - 1)) * ‖a - b‖ * τ := by gcongr
    _ = (n * x ^ (n - 1) * τ) * ‖a - b‖ := by ring
    _ ≤ 1 * ‖a - b‖ := by gcongr
    _ = ‖a - b‖ := one_mul _

/-- **Lipschitz dependence on a complex scale.** -/
theorem tNorm_sig_csub_le (hh : 0 < h) (hℓ : 0 < ℓ) {a b : ℂ} {τ : ℝ} (hτ : 0 < τ)
    (ha1 : ‖a‖ ≤ 1 - τ) (hb1 : ‖b‖ ≤ 1 - τ) (F : Grassmann.N X) :
    tNorm E p h ℓ (sig a F - sig b F) ≤ ENNReal.ofReal (‖a - b‖ / τ) * tNorm E p h ℓ F := by
  rw [← ENNReal.ofReal_toReal (tNorm_ne_top hh hℓ F), ← ENNReal.ofReal_mul (by positivity)]
  refine tNorm_le fun g hg => ?_
  set g' : TestFn X := fun n z => (a ^ n - b ^ n) * g n z
  have hpair : pair (sig a F - sig b F) g = pair F g' := by
    unfold pair
    refine sum_congr rfl fun n _ => ?_
    congr 1
    refine sum_congr rfl fun z _ => ?_
    rw [coeff_sub', coeff_sig, coeff_sig]; simp only [g']; ring
  have hg' : phiNorm E p h ℓ g' ≤ ENNReal.ofReal (‖a - b‖ / τ) := by
    refine phiNorm_le fun n z α hα => ?_
    unfold phiTerm
    have e : nab α (g' n) z = (a ^ n - b ^ n) * nab α (g n) z := nab_const_mul α _ (g n) z
    have hc : ‖a ^ n - b ^ n‖ ≤ ‖a - b‖ / τ := norm_pow_sub_pow_le hτ ha1 hb1 n
    have h1 : phiTerm h ℓ g z α ≤ 1 :=
      phiTerm_le_of_phiNorm_le hh.le hℓ zero_le_one (by rwa [ENNReal.ofReal_one]) z α hα
    unfold phiTerm at h1
    rw [e, norm_mul]
    calc ℓ⁻¹ ^ n * h ^ ord α * (‖a ^ n - b ^ n‖ * ‖nab α (g n) z‖)
        = ‖a ^ n - b ^ n‖ * (ℓ⁻¹ ^ n * h ^ ord α * ‖nab α (g n) z‖) := by ring
      _ ≤ ‖a - b‖ / τ * 1 := by gcongr
      _ = ‖a - b‖ / τ := mul_one _
  rw [hpair]
  have := abs_pair_le hh hℓ F (by positivity) hg'
  linarith [mul_comm (‖a - b‖ / τ) (tNorm E p h ℓ F).toReal]

end Gen

variable {d L N : ℕ} [NeZero L]

theorem Tj_sig_csub_le {j : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {a b : ℂ} {τ : ℝ} (hτ : 0 < τ)
    (ha1 : ‖a‖ ≤ 1 - τ) (hb1 : ‖b‖ ≤ 1 - τ) (F : Alg d L N) :
    Tj d (L : ℝ) j ℓ (sig a F - sig b F) ≤ ENNReal.ofReal (‖a - b‖ / τ) * Tj d (L : ℝ) j ℓ F := by
  have hh : (0 : ℝ) < (L : ℝ) ^ j := pow_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L))) j
  exact tNorm_sig_csub_le hh hℓ hτ ha1 hb1 F

theorem Fnorm_sigF_csub_le {j : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {a b : ℂ} {τ : ℝ} (hτ : 0 < τ)
    (ha1 : ‖a‖ ≤ 1 - τ) (hb1 : ‖b‖ ≤ 1 - τ) (F : Fam d L N) :
    Fnorm j ℓ (sigF a F - sigF b F) ≤ ENNReal.ofReal (‖a - b‖ / τ) * Fnorm j ℓ F := by
  refine iSup₂_le fun c hc => ?_
  have h := Tj_sig_csub_le (j := j) hℓ hτ ha1 hb1 (F c : Alg d L N)
  refine le_trans (le_of_eq ?_) (h.trans (mul_le_mul_right (Tj_le_Fnorm F hc) _))
  rfl

theorem Knorm_sigK_csub_le {j : ℕ} {ℓ A : ℝ} (hℓ : 0 < ℓ) {a b : ℂ} {τ : ℝ} (hτ : 0 < τ)
    (ha1 : ‖a‖ ≤ 1 - τ) (hb1 : ‖b‖ ≤ 1 - τ) (K : Act d L N) :
    Knorm j ℓ A (sigK a K - sigK b K) ≤ ENNReal.ofReal (‖a - b‖ / τ) * Knorm j ℓ A K := by
  refine iSup₂_le fun X hX => ?_
  have h := Tj_sig_csub_le (j := j) hℓ hτ ha1 hb1 (K X : Alg d L N)
  have h2 : ENNReal.ofReal (A ^ (nb j X - 2 ^ d)) * Tj d (L : ℝ) j ℓ (K X : Alg d L N) ≤
      Knorm j ℓ A K :=
    le_iSup₂ (f := fun X (_ : X ∈ connSets (L := L) (N := N) j) =>
      ENNReal.ofReal (A ^ (nb j X - 2 ^ d)) * Tj d (L : ℝ) j ℓ (K X : Alg d L N)) X hX
  calc ENNReal.ofReal (A ^ (nb j X - 2 ^ d)) *
        Tj d (L : ℝ) j ℓ (((sigK a K - sigK b K) X : EvR (Lam d L N)) : Alg d L N)
      ≤ ENNReal.ofReal (A ^ (nb j X - 2 ^ d)) *
        (ENNReal.ofReal (‖a - b‖ / τ) * Tj d (L : ℝ) j ℓ (K X : Alg d L N)) :=
        mul_le_mul_right (le_trans (le_of_eq rfl) h) _
    _ = ENNReal.ofReal (‖a - b‖ / τ) *
        (ENNReal.ofReal (A ^ (nb j X - 2 ^ d)) * Tj d (L : ℝ) j ℓ (K X : Alg d L N)) := by ring
    _ ≤ _ := mul_le_mul_right h2 _

end

end Step2
