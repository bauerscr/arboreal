import Loc.EstCoef

/-!
# Proposition `prop:Loc` (i): boundedness of `Loc_{X,Y}`

`‖Loc_{X,Y} F‖_{T_j(ℓ)} ≤ C ‖F‖_{T_j(ℓ)}` for small `Y ⊆ X`, `F ∈ 𝒩(X^□)`, any `ℓ > 0`,
with `C` depending only on `d` (for `L > 2^{d+3} + 8d`).
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD

variable {d L N : ℕ} [NeZero L]

theorem abs_pair_le_of_le {X : Type*} [DecidableEq X] [Fintype X] {E : Type*} [Fintype E]
    [DecidableEq E] [AddAction (E → ℕ) X] {p : ℕ} {h ℓ : ℝ} {F : Grassmann.N X} {c : ℝ}
    (hc : 0 ≤ c) (hF : tNorm E p h ℓ F ≤ ENNReal.ofReal c) {g : TestFn X}
    (hg : phiNorm E p h ℓ g ≤ 1) : ‖pair F g‖ ≤ c :=
  (ENNReal.ofReal_le_ofReal_iff hc).1 ((le_tNorm F hg).trans hF)

theorem pair_LocXY (X Y : Finset (Lam d L N)) (F : Alg d L N) (g : TestFn (Lam d L N)) :
    pair (LocXY X Y F) g = (ε F * Y.card / X.card) * pair 1 g +
      ∑ M, locCoef X F M * pair (monoSet M Y) g := by
  rw [LocXY, pair_add, pair_smul, pair_sum]
  simp only [pair_smul]

theorem exists_LocXY_bound (d : ℕ) (hd : 1 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℕ) [NeZero L],
    2 ^ (d + 3) + 8 * d < L → ∀ N j : ℕ, j < N → ∀ X Y : Finset (Lam d L N), IsSmall j X →
    Y ⊆ X → ∀ F ∈ NX (nbhd j X : Set (Lam d L N)), ∀ ℓ : ℝ, 0 < ℓ →
      Tj d (L : ℝ) j ℓ (LocXY X Y F) ≤ ENNReal.ofReal C * Tj d (L : ℝ) j ℓ F := by
  obtain ⟨Kc, hKc0, hKc⟩ := exists_locCoef_bound d hd
  set n : ℝ := (Fintype.card (Mono d) : ℝ)
  refine ⟨1 + n * Kc, by positivity, ?_⟩
  intro L _ hL N j hj X Y hX hYX F hF ℓ hℓ
  have hne : X.Nonempty := hX.2.1.1
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set s : ℝ := (L : ℝ) ^ j
  have hs : 0 < s := by positivity
  set T : ℝ := (Tj d (L : ℝ) j ℓ F).toReal
  have hT : 0 ≤ T := ENNReal.toReal_nonneg
  have hX0 : (0 : ℝ) < X.card := by exact_mod_cast hne.card_pos
  have hYX' : (Y.card : ℝ) ≤ X.card := by exact_mod_cast card_le_card hYX
  have hp : 2 ≤ pPhi d := by simp [pPhi]; omega
  have hTF : Tj d (L : ℝ) j ℓ F = ENNReal.ofReal T :=
    (ENNReal.ofReal_toReal (tNorm_ne_top hs hℓ F)).symm
  rw [hTF, ← ENNReal.ofReal_mul (by positivity)]
  refine tNorm_le fun g hg => ?_
  rw [pair_LocXY]
  have h1 : ‖pair (1 : Alg d L N) g‖ ≤ 1 :=
    abs_pair_le_of_le zero_le_one (by rw [ENNReal.ofReal_one]; exact tNorm_one_le hs hℓ) hg
  have h2 : ∀ M : Mono d, ‖pair (monoSet M Y) g‖ ≤ Y.card * (ℓ ^ 2 * (s ^ M.deg)⁻¹) :=
    fun M => abs_pair_le_of_le (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (sq_nonneg _)
      (inv_nonneg.2 (pow_nonneg hs.le _)))) (tNorm_monoSet_le hp hs hℓ M Y) hg
  have h3 : ‖ε F‖ ≤ T := abs_eps_le hs hℓ F
  have hcM : ∀ M : Mono d, ‖locCoef X F M‖ ≤ Kc * (ℓ ^ 2)⁻¹ * s ^ M.deg * T / X.card :=
    fun M => hKc L hL N j hj X hX F hF ℓ hℓ M
  clear_value s T
  have h4 : ∀ M : Mono d, ‖locCoef X F M * pair (monoSet M Y) g‖ ≤ Kc * T := by
    intro M
    rw [norm_mul]
    have hsM : 0 < s ^ M.deg := pow_pos hs _
    have e1 : (Kc * (ℓ ^ 2)⁻¹ * s ^ M.deg * T / X.card) * (Y.card * (ℓ ^ 2 * (s ^ M.deg)⁻¹)) =
        Kc * T * (Y.card / X.card) := by
      field_simp
    have e2 : Y.card / (X.card : ℝ) ≤ 1 := (div_le_one hX0).2 hYX'
    have e3 : 0 ≤ Kc * T := mul_nonneg hKc0 hT
    calc ‖locCoef X F M‖ * ‖pair (monoSet M Y) g‖
        ≤ (Kc * (ℓ ^ 2)⁻¹ * s ^ M.deg * T / X.card) * (Y.card * (ℓ ^ 2 * (s ^ M.deg)⁻¹)) :=
          mul_le_mul (hcM M) (h2 M) (norm_nonneg _) ((norm_nonneg _).trans (hcM M))
      _ = Kc * T * (Y.card / X.card) := e1
      _ ≤ Kc * T * 1 := mul_le_mul_of_nonneg_left e2 e3
      _ = Kc * T := mul_one _
  have h5 : ‖ε F * Y.card / X.card * pair 1 g‖ ≤ T := by
    rw [norm_mul, norm_div, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
    have e1 : ‖ε F‖ * Y.card / X.card ≤ T := by
      rw [div_le_iff₀ hX0]
      calc ‖ε F‖ * Y.card ≤ T * X.card :=
            mul_le_mul h3 hYX' (Nat.cast_nonneg _) hT
        _ = T * X.card := rfl
    calc ‖ε F‖ * Y.card / X.card * ‖pair 1 g‖ ≤ T * 1 :=
          mul_le_mul e1 h1 (norm_nonneg _) hT
      _ = T := mul_one T
  calc ‖ε F * Y.card / X.card * pair 1 g + ∑ M, locCoef X F M * pair (monoSet M Y) g‖
      ≤ ‖ε F * Y.card / X.card * pair 1 g‖ + ∑ M, ‖locCoef X F M * pair (monoSet M Y) g‖ :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ T + ∑ _M : Mono d, Kc * T := add_le_add h5 (sum_le_sum fun M _ => h4 M)
    _ = (1 + n * Kc) * T := by
        rw [sum_const, card_univ, nsmul_eq_mul]; ring

end

end Loc
