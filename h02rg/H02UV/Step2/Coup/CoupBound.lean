import Step2.Map.DCov

/-!
# The coupling vector of `Q(B)` and the second-order part of `𝒲`
(`h02uv-outline.tex`, `prop:C2`(iii) and `prop:C4`)

* `exists_coup_bound`: the coupling vector of a polynomial `unif r (coupC κ) (coupE κ) X` on a
  small set `X` is bounded by its `T_j(ℓ)` norm `R`:
  `|z|, |y| ≤ C ℓ^{-2} L^{2j} R/|X|`, `|ν| ≤ C ℓ^{-2} R/|X|`, `|g| ≤ C ℓ^{-4} L^{2j} R/|X|`
  (from `exists_locCoef_bound` and `exists_mu4_bound`).
* `BH.Q2_tj_le`: `‖Q(B)‖_{T_j(ℓ)} ≤ c_S C_l r` when `‖K‖ ≤ r`. Together these give `prop:C2`(iii),
  `|κ_Q| ≤ C(L) ‖K_j‖`, in the scaled form above (`BH.coupQ_le`).
* `Wp_split` (`prop:C4`): `𝒲_{j+1}(B) = 𝒲_{j+1}^{src}(B) + 𝔼_C θ 𝒲(B) - Loc_{B_+,B} 𝔼_C θ 𝒲(B_+)`,
  where the source `𝒲^{src} = Wp j C V 0` is quadratic in `V`. `Wp` does not depend on `K`, so
  the `𝒲`-coordinate of the flow is exactly the explicit recursion `𝒲^{(2)}` of `prop:C4`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Matrix

/-! ### Coefficients of coupling polynomials -/

theorem toReal_le_of_le {x : ENNReal} {R : ℝ} (hR : 0 ≤ R) (h : x ≤ ENNReal.ofReal R) :
    x.toReal ≤ R :=
  ENNReal.toReal_le_of_le_ofReal hR h

/-- **The coupling vector is bounded by the norm.** -/
theorem exists_coup_bound (d : ℕ) (hd : 1 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℕ) [NeZero L],
    2 ^ (d + 3) + 8 * d < L → ∀ N j : ℕ, j < N → ∀ X : Finset (Lam d L N), IsSmall j X →
    ∀ (r : ℂ) (κ : Coup), unif r (coupC κ) (coupE κ) X ∈ NX (nbhd j X : Set (Lam d L N)) →
    ∀ ℓ R : ℝ, 0 < ℓ → 0 ≤ R → Tj d (L : ℝ) j ℓ (unif r (coupC κ) (coupE κ) X) ≤ ENNReal.ofReal R →
      ‖κ.z‖ ≤ C * (ℓ ^ 2)⁻¹ * ((L : ℝ) ^ j) ^ 2 * R / X.card ∧
      ‖κ.y‖ ≤ C * (ℓ ^ 2)⁻¹ * ((L : ℝ) ^ j) ^ 2 * R / X.card ∧
      ‖κ.nu‖ ≤ C * (ℓ ^ 2)⁻¹ * R / X.card ∧
      ‖κ.g‖ ≤ C * (ℓ ^ 4)⁻¹ * ((L : ℝ) ^ j) ^ 2 * R / X.card := by
  obtain ⟨Cc, hCc0, hCc⟩ := exists_locCoef_bound d hd
  obtain ⟨Cm, hCm0, hCm⟩ := exists_mu4_bound d
  refine ⟨2 * (Cc + Cm), by positivity, ?_⟩
  intro L _ hL N j hj X hX r κ hF ℓ R hℓ hR hT
  set i₀ : Fin d := ⟨0, hd⟩
  have hp := patch_of_small hL hj hX
  have hne : X.Nonempty := hX.2.1.1
  have hX0 : (0 : ℝ) < X.card := by exact_mod_cast hne.card_pos
  have hTR := toReal_le_of_le hR hT
  have hc : ∀ M : Mono d, ‖coupC κ M‖ ≤ Cc * (ℓ ^ 2)⁻¹ * ((L : ℝ) ^ j) ^ M.deg * R / X.card := by
    intro M
    have h := hCc L hL N j hj X hX _ hF ℓ hℓ M
    rw [locCoef_unif hp hne] at h
    refine h.trans (div_le_div_of_nonneg_right ?_ hX0.le)
    exact mul_le_mul_of_nonneg_left hTR (by positivity)
  have hcC : Cc ≤ 2 * (Cc + Cm) := by linarith
  have hcm : Cm ≤ 2 * (Cc + Cm) := by linarith
  have hmono : ∀ {a b : ℝ} (u : ℝ), 0 ≤ u → a ≤ b → a * u ≤ b * u :=
    fun u hu h => mul_le_mul_of_nonneg_right h hu
  have hfac : 0 ≤ (ℓ ^ 2)⁻¹ * ((L : ℝ) ^ j) ^ 2 * R / X.card := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := hc (.m2 i₀ i₀)
    simp only [coupC, if_pos rfl, Mono.deg] at h
    calc ‖κ.z‖ ≤ Cc * ((ℓ ^ 2)⁻¹ * ((L : ℝ) ^ j) ^ 2 * R / X.card) := by
          refine h.trans_eq ?_; ring
      _ ≤ 2 * (Cc + Cm) * ((ℓ ^ 2)⁻¹ * ((L : ℝ) ^ j) ^ 2 * R / X.card) := hmono _ hfac hcC
      _ = _ := by ring
  · have h := hc (.a2 s(i₀, i₀))
    simp only [coupC, Sym2.mk_isDiag_iff, if_true, Mono.deg, norm_div, norm_neg] at h
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)] at h
    calc ‖κ.y‖ ≤ 2 * Cc * ((ℓ ^ 2)⁻¹ * ((L : ℝ) ^ j) ^ 2 * R / X.card) := by
          refine h.trans_eq ?_; ring
      _ ≤ 2 * (Cc + Cm) * ((ℓ ^ 2)⁻¹ * ((L : ℝ) ^ j) ^ 2 * R / X.card) :=
          hmono _ hfac (by linarith)
      _ = _ := by ring
  · have h := hc .c
    simp only [coupC, Mono.deg, pow_zero, mul_one] at h
    calc ‖κ.nu‖ ≤ Cc * ((ℓ ^ 2)⁻¹ * R / X.card) := by refine h.trans_eq ?_; ring
      _ ≤ 2 * (Cc + Cm) * ((ℓ ^ 2)⁻¹ * R / X.card) := hmono _ (by positivity) hcC
      _ = _ := by ring
  · have h := hCm L hL N j hj X hX _ hF i₀ i₀ ℓ hℓ
    rw [mu4_unif hp, coupE, if_pos rfl, norm_mul, Complex.norm_natCast] at h
    rw [← le_div_iff₀ hX0] at h
    calc ‖κ.g‖ ≤ Cm * (ℓ ^ 4)⁻¹ * ((L : ℝ) ^ j) ^ 2 * (Tj d (L : ℝ) j ℓ
          (unif r (coupC κ) (coupE κ) X)).toReal / X.card := h
      _ ≤ Cm * ((ℓ ^ 4)⁻¹ * ((L : ℝ) ^ j) ^ 2 * R / X.card) := by
          rw [mul_div_assoc, mul_div_assoc]
          refine (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hTR hX0.le)
            (by positivity)).trans_eq ?_
          ring
      _ ≤ 2 * (Cc + Cm) * ((ℓ ^ 4)⁻¹ * ((L : ℝ) ^ j) ^ 2 * R / X.card) :=
          hmono _ (by positivity) hcm
      _ = _ := by ring

variable {d L N : ℕ} [NeZero L]

/-! ### The norm of `Q(B)` -/

namespace BH

variable {j : ℕ} {ℓ ℓ' ℓC : ℝ} {C : Matrix (Lam d L N) (Lam d L N) ℂ} {V W : Fam d L N}
  {K : Act d L N} {A r Cl cS : ℝ} (H : BH j ℓ ℓ' ℓC C V W K A r Cl cS)
include H

/-- `‖Q(B)‖_{T_j(ℓ)} ≤ c_S C_l r`. -/
theorem Q2_tj_le {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    Tj d (L : ℝ) j ℓ (Q2 j K b : Alg d L N) ≤ ENNReal.ofReal (cS * (Cl * r)) := by
  classical
  have hr := H.hr
  have hCl := H.hCl
  rw [Q2, if_pos H.hjN]
  refine (tn_sum_const (E := Dir d) (p := pPhi d) _ _ (r := Cl * r) (by positivity)
    fun X hX => ?_).trans (ENNReal.ofReal_le_ofReal ?_)
  · obtain ⟨hs, hbX⟩ := mem_smallSets_filter.1 hX
    exact H.loc_term_le hs hbX
  · exact mul_le_mul_of_nonneg_right (H.hcount b hb) (by positivity)

/-- **`prop:C2`(iii)**: the coupling vector `κ_Q` of `Q(B)` is bounded by `‖K_j‖`. -/
theorem coupQ_le {Cq : ℝ}
    (hCq : ∀ (L : ℕ) [NeZero L], 2 ^ (d + 3) + 8 * d < L → ∀ N j : ℕ, j < N →
      ∀ X : Finset (Lam d L N), IsSmall j X →
      ∀ (r : ℂ) (κ : Coup), unif r (coupC κ) (coupE κ) X ∈ NX (nbhd j X : Set (Lam d L N)) →
      ∀ ℓ R : ℝ, 0 < ℓ → 0 ≤ R →
        Tj d (L : ℝ) j ℓ (unif r (coupC κ) (coupE κ) X) ≤ ENNReal.ofReal R →
        ‖κ.z‖ ≤ Cq * (ℓ ^ 2)⁻¹ * ((L : ℝ) ^ j) ^ 2 * R / X.card ∧
        ‖κ.y‖ ≤ Cq * (ℓ ^ 2)⁻¹ * ((L : ℝ) ^ j) ^ 2 * R / X.card ∧
        ‖κ.nu‖ ≤ Cq * (ℓ ^ 2)⁻¹ * R / X.card ∧
        ‖κ.g‖ ≤ Cq * (ℓ ^ 4)⁻¹ * ((L : ℝ) ^ j) ^ 2 * R / X.card)
    {rQ : ℂ} {κQ : Coup}
    (hQ : ∀ b ∈ blockIdx (L := L) (N := N) j,
      (Q2 j K b : Alg d L N) = unif rQ (coupC κQ) (coupE κQ) (blockSet j b)) :
    let X := blockSet (L := L) (N := N) j (0 : Fin d → ℕ)
    let R := cS * (Cl * r)
    ‖κQ.z‖ ≤ Cq * (ℓ ^ 2)⁻¹ * ((L : ℝ) ^ j) ^ 2 * R / X.card ∧
      ‖κQ.y‖ ≤ Cq * (ℓ ^ 2)⁻¹ * ((L : ℝ) ^ j) ^ 2 * R / X.card ∧
      ‖κQ.nu‖ ≤ Cq * (ℓ ^ 2)⁻¹ * R / X.card ∧
      ‖κQ.g‖ ≤ Cq * (ℓ ^ 4)⁻¹ * ((L : ℝ) ^ j) ^ 2 * R / X.card := by
  intro X R
  have h0 := zero_mem_blockIdx (d := d) (L := L) (N := N) j
  have hX := isSmall_blockSet_of_mem h0
  have hmem : unif rQ (coupC κQ) (coupE κQ) X ∈ NX (nbhd j X : Set (Lam d L N)) := by
    rw [← hQ 0 h0]; exact Q2_mem_NB H.hd h0
  have hT : Tj d (L : ℝ) j ℓ (unif rQ (coupC κQ) (coupE κQ) X) ≤ ENNReal.ofReal R := by
    rw [← hQ 0 h0]; exact H.Q2_tj_le h0
  have hr := H.hr; have hCl := H.hCl
  have hcS : 0 ≤ cS := by linarith [H.hcS]
  exact hCq L H.hL8 N j H.hj X hX rQ κQ hmem ℓ R H.hℓ (by positivity) hT

end BH

/-! ### The `𝒲`-recursion (`prop:C4`) -/

variable (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V W : Fam d L N)

/-- **`𝒲_{j+1}` is the explicit recursion**: the quadratic source `Wp j C V 0` plus the linear
transport `(1 - Loc_{B_+,B}) 𝔼_C θ 𝒲`. There is no `K` dependence. -/
theorem Wp_split (b : Fin d → ℕ) :
    Wp j C V W b = Wp j C V 0 b + (EthE C (W b) -
      Loc2E (Bp (L := L) (N := N) j b) (blockSet j b)
        (∑ b' ∈ blocks j (Bp (L := L) (N := N) j b), EthE C (W b'))) := by
  have hS : ∀ X, SX j C V W X = SX j C V 0 X + ∑ b' ∈ blocks j X, EthE C (W b') := by
    intro X
    simp only [SX, Sb, Pi.zero_apply, EthE_zero, add_zero, ← sum_add_distrib]
  simp only [Wp, LS, hS, Loc2E_add, Sb, Pi.zero_apply, EthE_zero, add_zero]
  abel

end

end Step2
