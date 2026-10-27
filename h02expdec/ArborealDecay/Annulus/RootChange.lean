module

public import ArborealDecay.TLaw
public import ArborealDecay.H02

/-!
# Change of root (supplement `prop:root-change`) and (B) (`thm:B`)

* `lintegral_root_change`: `Z^k_{w,a} = ∫ e^{2a τ_k} e^{-Φ} D^ρ(τ̂)^a dμ_ρ` in `[0,∞]`
  (supplement `prop:root-change`), via the linear map `ψ(τ)_i = τ̂_i - τ̂_k`, which preserves
  Lebesgue measure (`|det| = 1`), together with `D_root_change`.
* `B_of_inputs` (`thm:B`): `E^ρ_{w,3/2} e^{3 t_k} = 1`, from (A) at the two roots `ρ`, `k`.
* `Zmono_of_inputs` (`cor:Zmon`): monotonicity of `Z_{w,3/2}` in the weights, from (A).
-/

open Matrix Real MeasureTheory

set_option linter.unusedSectionVars false

@[expose] public section

namespace ArborealDecay.Annulus

open ArborealDecay.TLaw

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Shift invariance -/

theorem Phi_sub_const (w : V → V → ℝ) (t : V → ℝ) (c : ℝ) :
    Phi w (fun v => t v - c) = Phi w t := by
  unfold Phi
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  congr 3; ring

theorem Hmat_sub_const (w : V → V → ℝ) (ρ : V) (t : V → ℝ) (c : ℝ) :
    Hmat w ρ (fun v => t v - c) = Hmat w ρ t := by
  ext i k
  simp only [Hmat, of_apply]
  split_ifs
  · refine Finset.sum_congr rfl fun m _ => ?_
    congr 2; ring
  · rfl

theorem D_sub_const (w : V → V → ℝ) (ρ : V) (t : V → ℝ) (c : ℝ) :
    D w ρ (fun v => t v - c) = D w ρ t := by
  rw [D, D, Hmat_sub_const]

/-! ### The change-of-root map -/

/-- The relabelling `Λ_k ≃ Λ_ρ` induced by the transposition `(ρ k)`. -/
def rootSwap (ρ k : V) : {i // i ≠ k} ≃ {i // i ≠ ρ} :=
  Equiv.subtypeEquiv (Equiv.swap ρ k) fun i => by
    constructor
    · intro hi h
      rcases eq_or_ne i ρ with rfl | hiρ
      · rw [Equiv.swap_apply_left] at h
        exact hi (h ▸ rfl)
      · rw [Equiv.swap_apply_of_ne_of_ne hiρ hi] at h
        exact hiρ h
    · intro h hi
      subst hi
      exact h (Equiv.swap_apply_right ρ i)

theorem card_ne_eq (ρ k : V) :
    Fintype.card {i // i ≠ k} = Fintype.card {i // i ≠ ρ} :=
  Fintype.card_congr (rootSwap ρ k)

theorem normC_eq (ρ k : V) : normC k = normC ρ := by
  simp only [normC, card_ne_eq ρ k]

/-- The shear matrix `1 + u vᵀ` with `v = e_{k'}`, `u = -(1 + e_{k'})`:
`(M τ)_i = τ_i - τ_{k'}` for `i ≠ k'` and `(M τ)_{k'} = -τ_{k'}`. -/
noncomputable def shearMat {ρ : V} (k' : {i // i ≠ ρ}) : Matrix {i // i ≠ ρ} {i // i ≠ ρ} ℝ :=
  1 + replicateCol Unit (fun i => -1 - (Pi.single k' (1 : ℝ) : {i // i ≠ ρ} → ℝ) i) *
    replicateRow Unit (Pi.single k' (1 : ℝ) : {i // i ≠ ρ} → ℝ)

theorem det_shearMat {ρ : V} (k' : {i // i ≠ ρ}) : (shearMat k').det = -1 := by
  rw [shearMat, det_one_add_replicateCol_mul_replicateRow]
  simp [dotProduct, Pi.single_apply]

theorem shearMat_mulVec {ρ : V} (k' : {i // i ≠ ρ}) (τ : {i // i ≠ ρ} → ℝ) (i : {i // i ≠ ρ}) :
    (shearMat k' *ᵥ τ) i = if i = k' then -τ k' else τ i - τ k' := by
  simp only [shearMat, add_mulVec, one_mulVec, Pi.add_apply]
  rw [← mulVec_mulVec]
  simp [mulVec, dotProduct, Pi.single_apply]
  split_ifs with h
  · subst h; ring
  · ring

theorem measurePreserving_shear {ρ : V} (k' : {i // i ≠ ρ}) :
    MeasurePreserving (fun τ : {i // i ≠ ρ} → ℝ => shearMat k' *ᵥ τ) volume volume := by
  have hdet : LinearMap.det (Matrix.toLin' (shearMat k')) ≠ 0 := by
    rw [LinearMap.det_toLin', det_shearMat]; norm_num
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure ({i // i ≠ ρ} → ℝ)) hdet
  rw [LinearMap.det_toLin', det_shearMat] at hmap
  have hc : Continuous (Matrix.toLin' (shearMat k')) :=
    LinearMap.continuous_of_finiteDimensional _
  refine ⟨hc.measurable, ?_⟩
  have e : (fun τ : {i // i ≠ ρ} → ℝ => shearMat k' *ᵥ τ) = Matrix.toLin' (shearMat k') := by
    funext τ; rw [Matrix.toLin'_apply]
  rw [e, hmap]
  norm_num

/-- The change-of-root map `ψ(τ)_j = τ̂_j - τ̂_k` from `ℝ^{Λ_ρ}` to `ℝ^{Λ_k}`. -/
noncomputable def psiMap (ρ k : V) (hk : k ≠ ρ) (τ : {i // i ≠ ρ} → ℝ) : {i // i ≠ k} → ℝ :=
  fun j => (shearMat (⟨k, hk⟩ : {i // i ≠ ρ}) *ᵥ τ) (rootSwap ρ k j)

theorem measurePreserving_psiMap (ρ k : V) (hk : k ≠ ρ) :
    MeasurePreserving (psiMap ρ k hk) volume volume := by
  have h2 := volume_preserving_arrowCongr' (α₁ := {i // i ≠ ρ}) (α₂ := {i // i ≠ k})
    (rootSwap ρ k).symm (MeasurableEquiv.refl ℝ) (MeasurePreserving.id _)
  have := h2.comp (measurePreserving_shear (⟨k, hk⟩ : {i // i ≠ ρ}))
  convert this using 1
  funext τ j
  simp [psiMap, MeasurableEquiv.arrowCongr', Equiv.arrowCongr']

theorem ext_psiMap (ρ k : V) (hk : k ≠ ρ) (τ : {i // i ≠ ρ} → ℝ) :
    TLaw.ext k (psiMap ρ k hk τ) = fun v => TLaw.ext ρ τ v - TLaw.ext ρ τ k := by
  funext v
  by_cases hvk : v = k
  · subst hvk; simp
  · simp only [TLaw.ext, hvk, dite_false, psiMap, shearMat_mulVec]
    by_cases hvρ : v = ρ
    · subst hvρ
      have : rootSwap v k ⟨v, hvk⟩ = ⟨k, hk⟩ := by
        apply Subtype.ext; simp [rootSwap]
      rw [this]; simp [hk]
    · have : rootSwap ρ k ⟨v, hvk⟩ = ⟨v, hvρ⟩ := by
        apply Subtype.ext; simp [rootSwap, Equiv.swap_apply_of_ne_of_ne hvρ hvk]
      rw [this]
      simp [hvρ, hvk, hk]

theorem density_psiMap {w : V → V → ℝ} (hW : IsWGraph w) (ρ k : V) (hk : k ≠ ρ) (a : ℝ)
    (τ : {i // i ≠ ρ} → ℝ) :
    density w k a (psiMap ρ k hk τ) = exp (2 * a * TLaw.ext ρ τ k) * density w ρ a τ := by
  unfold density
  rw [ext_psiMap, Phi_sub_const, D_sub_const, D_root_change hW ρ k, ext_root, sub_zero,
    mul_rpow (D_nonneg hW ρ _) (exp_pos _).le, ← exp_mul]
  have : normC k = normC ρ := normC_eq ρ k
  simp only [normC] at this
  rw [this]
  have e : exp (2 * TLaw.ext ρ τ k * a) = exp (2 * a * TLaw.ext ρ τ k) := by ring_nf
  rw [e]; ring

theorem measurable_density (w : V → V → ℝ) (ρ : V) (a : ℝ) : Measurable (density w ρ a) := by
  have h1 : Continuous fun τ => D w ρ (TLaw.ext ρ τ) := (continuous_D w ρ).comp (continuous_ext ρ)
  have h2 : Continuous fun τ => Phi w (TLaw.ext ρ τ) := (continuous_Phi w).comp (continuous_ext ρ)
  unfold density
  exact ((continuous_exp.comp h2.neg).measurable.mul (h1.measurable.pow_const a)).mul
    measurable_const

/-- **Change of root** (supplement `prop:root-change`), in `[0, ∞]`. -/
theorem lintegral_root_change {w : V → V → ℝ} (hW : IsWGraph w) (ρ k : V) (a : ℝ) :
    Z w k a = ∫⁻ τ, ENNReal.ofReal (exp (2 * a * TLaw.ext ρ τ k) * density w ρ a τ) := by
  by_cases hk : k = ρ
  · subst hk; simp [Z]
  · rw [Z, ← (measurePreserving_psiMap ρ k hk).lintegral_comp
      (measurable_density w k a).ennreal_ofReal]
    simp only [density_psiMap hW ρ k hk]

/-! ### (B) and monotonicity from (A) -/

universe u

/-- `E^ρ_{w,a} e^{2a t_k} = Z^k_{w,a} / Z^ρ_{w,a}` (supplement `prop:root-change`, second part). -/
theorem expect_exp_root_change {w : V → V → ℝ} (hW : IsWGraph w)
    (hconn : (supportGraph w).Connected) (ρ k : V) (a : ℝ) :
    expect w ρ a (fun τ => exp (2 * a * TLaw.ext ρ τ k)) = (Z w k a).toReal / (Z w ρ a).toReal := by
  unfold expect
  have hnn : 0 ≤ᵐ[volume] fun τ => exp (2 * a * TLaw.ext ρ τ k) * density w ρ a τ :=
    Filter.Eventually.of_forall fun τ => mul_nonneg (exp_pos _).le (density_pos hW hconn ρ a τ).le
  have hm : AEStronglyMeasurable (fun τ => exp (2 * a * TLaw.ext ρ τ k) * density w ρ a τ) :=
    (((continuous_exp.comp (continuous_const.mul ((continuous_apply k).comp
      (continuous_ext ρ))))).measurable.mul (measurable_density w ρ a)).aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae hnn hm, ← lintegral_root_change hW ρ k a]
  ring

/-- **(B)** (supplement `thm:B`), from (A) at the roots `ρ` and `k`:
`E^ρ_{w,3/2} e^{3 t_k} = 1`. -/
theorem B_of_inputs
    (hA : ∀ (V : Type u) [Fintype V] [DecidableEq V] (w : V → V → ℝ) (hW : IsWGraph w),
      (supportGraph w).Connected → ∀ ρ : V,
        Z w ρ (3 / 2) = ENNReal.ofReal (H02.Zforest w hW.symm))
    {V : Type u} [Fintype V] [DecidableEq V] {w : V → V → ℝ} (hW : IsWGraph w)
    (hconn : (supportGraph w).Connected) (ρ k : V) :
    expect w ρ (3 / 2) (fun τ => exp (3 * TLaw.ext ρ τ k)) = 1 := by
  have h := expect_exp_root_change hW hconn ρ k (3 / 2)
  have e : (fun τ : {i // i ≠ ρ} → ℝ => exp (2 * (3 / 2 : ℝ) * TLaw.ext ρ τ k)) =
      fun τ => exp (3 * TLaw.ext ρ τ k) := by funext τ; norm_num
  rw [e, hA V w hW hconn k, ← hA V w hW hconn ρ] at h
  rw [h]
  exact div_self (ENNReal.toReal_pos (Z_pos hW hconn ρ _).ne'
    (Z_lt_top hW hconn ρ (by norm_num)).ne).ne'

theorem Zforest_mono {w w' : V → V → ℝ} (hW' : IsWGraph w') (hle : ∀ i k, w' i k ≤ w i k)
    (hs : ∀ i k, w i k = w k i) :
    H02.Zforest w' hW'.symm ≤ H02.Zforest w hs := by
  unfold H02.Zforest
  refine Finset.sum_le_sum fun F _ => ?_
  unfold H02.forestWeight
  refine Finset.prod_le_prod₀ (fun e _ => ?_) (fun e _ => ?_)
  · induction e using Sym2.ind with | h i k => exact hW'.nonneg i k
  · induction e using Sym2.ind with | h i k => exact hle i k

/-- **Monotonicity** (supplement `cor:Zmon`), from (A): for `w'` with the same support and
`w' ≤ w`, `Z^ρ_{w',3/2} ≤ Z^ρ_{w,3/2}`. -/
theorem Zmono_of_inputs
    (hA : ∀ (V : Type u) [Fintype V] [DecidableEq V] (w : V → V → ℝ) (hW : IsWGraph w),
      (supportGraph w).Connected → ∀ ρ : V,
        Z w ρ (3 / 2) = ENNReal.ofReal (H02.Zforest w hW.symm))
    {V : Type u} [Fintype V] [DecidableEq V] {w : V → V → ℝ} (hW : IsWGraph w)
    (hconn : (supportGraph w).Connected) (ρ : V) (w' : V → V → ℝ) (hW' : IsWGraph w')
    (hsupp : ∀ i k, 0 < w' i k ↔ 0 < w i k) (hle : ∀ i k, w' i k ≤ w i k) :
    Z w' ρ (3 / 2) ≤ Z w ρ (3 / 2) := by
  have hG : supportGraph w' = supportGraph w := by
    ext i k; simp only [supportGraph, SimpleGraph.fromRel_adj, hsupp]
  rw [hA V w hW hconn ρ, hA V w' hW' (hG ▸ hconn) ρ]
  exact ENNReal.ofReal_le_ofReal (Zforest_mono hW' hle hW.symm)

/-- (H1) of `sabot_two_thirds`, from (A). -/
theorem H1_of_inputs
    (hA : ∀ (V : Type u) [Fintype V] [DecidableEq V] (w : V → V → ℝ) (hW : IsWGraph w),
      (supportGraph w).Connected → ∀ ρ : V,
        Z w ρ (3 / 2) = ENNReal.ofReal (H02.Zforest w hW.symm))
    {V : Type u} [Fintype V] [DecidableEq V] {w : V → V → ℝ} (hW : IsWGraph w)
    (hconn : (supportGraph w).Connected) (ρ : V) :
    ∀ w' : V → V → ℝ, IsWGraph w' → (∀ i k, 0 < w' i k ↔ 0 < w i k) →
      (∀ i k, w' i k ≤ w i k) → Z w' ρ (3 / 2) < ⊤ ∧ Z w' ρ (3 / 2) ≤ Z w ρ (3 / 2) := by
  intro w' hW' hsupp hle
  have hG : supportGraph w' = supportGraph w := by
    ext i k; simp only [supportGraph, SimpleGraph.fromRel_adj, hsupp]
  exact ⟨Z_lt_top hW' (hG ▸ hconn) ρ (by norm_num),
    Zmono_of_inputs hA hW hconn ρ w' hW' hsupp hle⟩

end ArborealDecay.Annulus
