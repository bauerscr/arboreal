import Obs2.Flow.GradAB2

/-!
# The gradient coefficients of `V'_{ab}`: the sources of one step and the one-step bound

* **`gSzE_Q2O_le`**: the activity source, `gSzE(Q(B)_{ab}) ≤ B_j∑_{X⊇B}‖K(X)_{ab}‖_{T_j(ℓ)}`;
* **`gSzE_LSO_le`**: the localisation source at scale `j+1`,
  `gSzE(Loc_{B_+,B}S(B_+)_{ab}) ≤ B_{j+1}‖S(B_+)_{ab}‖_{T_{j+1}(ℓ)}`;
  here `B_i = (1+η)K_G L^i/h + ℓ^{-2}(2ℓ'g + g²)` (`gSzE_locABtXY_le`);
* `gSzE_LopM4_eq`: the gradient size of `ℒ_C(ψ̄_aψ_aψ̄_bψ_b)` (`M₄` under `e^{ℒ_C}`);
* **`gSzE_VpO_le`**: one step of one block,
  `gSzE(V_{j+1}(B)) ≤ gSzE(V(B)) + |M₄(V(B))|gSzE(ℒ_Cm₄) + gSzE(Q(B)) + |M₄(Q(B))|gSzE(ℒ_Cm₄) +
  gSzE(Loc S(B))` (from the exact coefficient flows `cfAB2_VpO`, `cfAB4_VpO`);
* **`gSzE_Vnext2O_le`**: the block `B_+` of scale `j+1` collects the blocks `B ⊆ B_+`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD

variable {d L N : ℕ} [NeZero L]

theorem gSzE_zero {E h ℓ : ℝ} (a b : Lam d L N) : gSzE E a b h ℓ (0 : Alg d L N) = 0 := by
  unfold gSzE
  simp only [show cfAB2 a b (0 : Alg d L N) = 0 from coeff_zero _,
    show cfAB2 b a (0 : Alg d L N) = 0 from coeff_zero _,
    show cfAB2 b b (0 : Alg d L N) = 0 from coeff_zero _,
    show cfAB4 a b (0 : Alg d L N) = 0 from coeff_zero _]
  simp

section Sources

variable {Cc : ℝ} (hCc0 : 0 ≤ Cc)
  (hCc : ∀ m : Fin d → ℕ, (∀ i, m i ≤ 1) → ∀ R : ℝ, 1 ≤ R → ∀ α : Dir d → ℕ,
    Grassmann.mabs α ≤ pPhi d → ∀ u : Zd d,
    |D1 (fun b v => b +ᵥ v) α (cutP m R) u| ≤ Cc * R ^ (∑ i, m i) / R ^ Grassmann.mabs α)
  (hL : 2 ^ (d + 3) + 8 * d < L) (P : ObsPts d L N) (hab : P.a ≠ P.b)
  {E κ η : ℝ} (hE : 0 ≤ E) (hκ : 0 ≤ κ)
  (hEκ : ∀ X : Finset (Lam d L N), E * eN1 X P.a P.b ≤ κ * eN2 X P.a P.b)

include hCc0 hCc hL hab hE hκ hEκ

/-- **The activity source of the gradient coefficients.** -/
theorem gSzE_Q2O_le {c : Obs.Case} (j : ℕ) (K : OAct c d L N)
    (hK : ∀ X, IsSmall j X → (K X : SA c (Lam d L N)).ab ∈ NX (nbhd j X : Set (Lam d L N)))
    (b : Fin d → ℕ) {ℓ ℓ' h : ℝ} (hℓ : 0 < ℓ) (hℓ' : 0 ≤ ℓ') (hℓℓ : ℓ' ≤ 2 * ℓ) (hh : 0 < h)
    (hsh : (L : ℝ) ^ j ≤ h) (hη : E * h⁻¹ ≤ η) :
    gSzE E P.a P.b h ℓ' (Q2O P j K b : SA c (Lam d L N)).ab ≤
      ((1 + η) * (KG d Cc κ * ((L : ℝ) ^ j * h⁻¹)) +
        ℓ⁻¹ ^ 2 * (2 * (ℓ' * (E * ℓ' * h⁻¹)) + (E * ℓ' * h⁻¹) * (E * ℓ' * h⁻¹))) *
        (open Classical in ∑ X ∈ (smallSets j).filter (fun X => blockSet j b ⊆ X),
          (Tj d (L : ℝ) j ℓ (K X : SA c (Lam d L N)).ab).toReal) := by
  classical
  have hη0 : 0 ≤ η := (by positivity : (0 : ℝ) ≤ E * h⁻¹).trans hη
  have hB0 : 0 ≤ (1 + η) * (KG d Cc κ * ((L : ℝ) ^ j * h⁻¹)) +
        ℓ⁻¹ ^ 2 * (2 * (ℓ' * (E * ℓ' * h⁻¹)) + (E * ℓ' * h⁻¹) * (E * ℓ' * h⁻¹)) := by
    have hg0 : 0 ≤ E * ℓ' * h⁻¹ := by positivity
    have : 0 ≤ KG d Cc κ := KG_nonneg d hκ
    have h2 : 0 ≤ 2 * (ℓ' * (E * ℓ' * h⁻¹)) + (E * ℓ' * h⁻¹) * (E * ℓ' * h⁻¹) := by
      have := mul_nonneg hℓ' hg0; have := mul_nonneg hg0 hg0; linarith
    have : 0 ≤ (L : ℝ) ^ j * h⁻¹ := by positivity
    positivity
  unfold Q2O
  split_ifs with hjN
  · rw [AddSubmonoidClass.coe_finsetSum, SA.sum_ab]
    refine (gSzE_sum_le hE hh.le hℓ' _ _ _ _).trans ?_
    rw [mul_sum]
    refine sum_le_sum fun X hX => ?_
    obtain ⟨hs, hbX⟩ := mem_smallSets_filter.1 hX
    rw [LocO2_ab]
    exact gSzE_locABtXY_le hCc0 hCc hL (by omega) P hab hs hbX (hK X hs) hℓ hℓ' hℓℓ hh hsh hE hκ
      (hEκ X) hη
  · rw [show ((0 : OE c (Lam d L N)) : SA c (Lam d L N)).ab = 0 from rfl, gSzE_zero]
    exact mul_nonneg hB0 (sum_nonneg fun _ _ => ENNReal.toReal_nonneg)

/-- **The localisation source of the gradient coefficients** (scale `j + 1`). -/
theorem gSzE_LSO_le {c : Obs.Case} {j : ℕ} (hj : j + 1 < N)
    (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V W : OFam c d L N) {b : Fin d → ℕ}
    (hb : b ∈ blockIdx (L := L) (N := N) j)
    (hS : (SXO j C V W (Step2.Bp (L := L) (N := N) j b) : SA c (Lam d L N)).ab ∈
      NX (nbhd (j + 1) (Step2.Bp (L := L) (N := N) j b) : Set (Lam d L N)))
    {ℓ ℓ' h : ℝ} (hℓ : 0 < ℓ) (hℓ' : 0 ≤ ℓ') (hℓℓ : ℓ' ≤ 2 * ℓ) (hh : 0 < h)
    (hsh : (L : ℝ) ^ (j + 1) ≤ h) (hη : E * h⁻¹ ≤ η) :
    gSzE E P.a P.b h ℓ' (LSO P j C V W b : SA c (Lam d L N)).ab ≤
      ((1 + η) * (KG d Cc κ * ((L : ℝ) ^ (j + 1) * h⁻¹)) +
        ℓ⁻¹ ^ 2 * (2 * (ℓ' * (E * ℓ' * h⁻¹)) + (E * ℓ' * h⁻¹) * (E * ℓ' * h⁻¹))) *
        (Tj d (L : ℝ) (j + 1) ℓ
          (SXO j C V W (Step2.Bp (L := L) (N := N) j b) : SA c (Lam d L N)).ab).toReal := by
  rw [LSO, LocO2_ab]
  exact gSzE_locABtXY_le hCc0 hCc hL hj P hab (isSmall_clo (isSmall_blockSet_of_mem hb))
    (subset_clo j _) hS hℓ hℓ' hℓℓ hh hsh hE hκ (hEκ _) hη

end Sources

/-- The gradient size of `ℒ_C(ψ̄_aψ_aψ̄_bψ_b)`. -/
theorem gSzE_LopM4_eq {E h ℓ : ℝ} (C : Matrix (Lam d L N) (Lam d L N) ℂ) {a b : Lam d L N}
    (hab : a ≠ b) :
    gSzE E a b h ℓ (LopM4 C a b) =
      (‖C a a - C b a‖ + ‖C a a - C a b‖) * (ℓ * (E * ℓ * h⁻¹)) +
        ‖C a a‖ * ((E * ℓ * h⁻¹) * (E * ℓ * h⁻¹)) := by
  obtain ⟨-, h2, h3, h4⟩ := cfAB2_LopM4 C hab
  unfold gSzE
  rw [h2, h3, h4, cfAB4_LopM4, norm_zero, zero_mul, add_zero,
    show -C b a + C a a = C a a - C b a by ring, show -C a b + C a a = C a a - C a b by ring]

section Step

variable (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
  (V W : OFam .two d L N) (K : OAct .two d L N)

/-- **One step of the gradient coefficients of one block.** -/
theorem gSzE_VpO_le {E h ℓ : ℝ} (hE : 0 ≤ E) (hh : 0 ≤ h) (hℓ : 0 ≤ ℓ)
    (hV : ∀ b, (V b : SA .two (Lam d L N)).ab ∈ NX ({P.a, P.b} : Set (Lam d L N)))
    (hS : ∀ b, IsSym (V b : SA .two (Lam d L N)).ab) (b : Fin d → ℕ) :
    gSzE E P.a P.b h ℓ (VpO P j C V W K b : SA .two (Lam d L N)).ab ≤
      gSzE E P.a P.b h ℓ (V b : SA .two (Lam d L N)).ab +
        ‖cfAB4 P.a P.b (V b : SA .two (Lam d L N)).ab‖ * gSzE E P.a P.b h ℓ (LopM4 C P.a P.b) +
        gSzE E P.a P.b h ℓ (Q2O P j K b : SA .two (Lam d L N)).ab +
        ‖cfAB4 P.a P.b (Q2O P j K b : SA .two (Lam d L N)).ab‖ *
          gSzE E P.a P.b h ℓ (LopM4 C P.a P.b) +
        gSzE E P.a P.b h ℓ (LSO P j C V W b : SA .two (Lam d L N)).ab := by
  set Fv := (V b : SA .two (Lam d L N)).ab
  set Fq := (Q2O P j K b : SA .two (Lam d L N)).ab
  set Fs := (LSO P j C V W b : SA .two (Lam d L N)).ab
  set G := LopM4 C P.a P.b
  set H : Alg d L N := Fv + cfAB4 P.a P.b Fv • G - (Fq + cfAB4 P.a P.b Fq • G) - Fs
  have hc : ∀ {u v : Lam d L N}, (u = P.a ∨ u = P.b) → (v = P.a ∨ v = P.b) →
      cfAB2 u v (VpO P j C V W K b : SA .two (Lam d L N)).ab = cfAB2 u v H := by
    intro u v hu hv
    rw [cfAB2_VpO P j C V W K hV hS hu hv b]
    simp only [H, Fv, Fq, Fs, G, cfAB2_sub, cfAB2_add, cfAB2_smul]
  have h4 : cfAB4 P.a P.b (VpO P j C V W K b : SA .two (Lam d L N)).ab = cfAB4 P.a P.b H := by
    rw [cfAB4_VpO P j C V W K hV hS b]
    simp only [H, Fv, Fq, Fs, G, cfAB4_sub, cfAB4_add, cfAB4_smul, cfAB4_LopM4, mul_zero, add_zero]
  rw [gSzE_congr (hc (Or.inl rfl) (Or.inr rfl)) (hc (Or.inr rfl) (Or.inl rfl))
    (hc (Or.inr rfl) (Or.inr rfl)) h4]
  have s1 := gSzE_sub_le hE hh hℓ P.a P.b (Fv + cfAB4 P.a P.b Fv • G - (Fq + cfAB4 P.a P.b Fq • G)) Fs
  have s2 := gSzE_sub_le hE hh hℓ P.a P.b (Fv + cfAB4 P.a P.b Fv • G) (Fq + cfAB4 P.a P.b Fq • G)
  have s3 := gSzE_add_le hE hh hℓ P.a P.b Fv (cfAB4 P.a P.b Fv • G)
  have s4 := gSzE_add_le hE hh hℓ P.a P.b Fq (cfAB4 P.a P.b Fq • G)
  rw [gSzE_smul hE hh hℓ] at s3 s4
  linarith

end Step

end

end Obs2
