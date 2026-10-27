module

public import ArborealDecay.BCHS.Rooted

/-!
# BCHS Proposition 2.9: the horospherical integrand (R5, pointwise part)

* `integrable_berezin_horo`: integrability of the horospherical integrand
  `p ↦ e^{∑ t − 2∑_m t_{vtx m}} ℓ(B(horoF F p · ∏ z_super))` for Schwartz `F` (the integrability
  companion of `ArborealDecay.Horo.integral_berezin_horo`, same proof).
* `horo_integrand_eq`: for the pinned `ℍ^{2|4}` integrand `∏ z⁻¹ F e^{−H}` with `F` a scalar after
  the substitution (`F ∈ {1, y_i y_j}`), the horospherical integrand is
  `f(τ, s) e^{−H̃(τ, s)}` with `H̃` the supplement's (`TSide.Htil`, BCHS (2.59) corrected):
  `e^{−3∑τ} body B(horoF(∏z⁻¹ F e^{−H}) ∏ z) = f · e^{−H̃}`.  This is BCHS (2.61) before the
  `(τ, s)`-integration.
-/

@[expose] public section

namespace ArborealDecay.BCHS

noncomputable section

open Finset Real Matrix MeasureTheory ArborealDecay.Super ArborealDecay.Super.H24
  ArborealDecay.Horo Grassmann
open ArborealDecay.TLaw (Lmat Phi ext IsWGraph ext_root ext_val supportGraph Lmat_posDef)
open scoped ContDiff

set_option linter.unusedSectionVars false

/-! ### Integrability of the horospherical integrand -/

section Integrable

variable {Λ M P : Type*} [Fintype Λ] [DecidableEq Λ] [Fintype M] [DecidableEq M]
  [Fintype P] [DecidableEq P]
variable (vtx : M → Λ)

theorem horo_pointwise (F : (Λ ⊕ Λ → ℝ) → SG M P) (ℓ : Module.Dual ℝ (SG M P))
    (p : Λ ⊕ Λ → ℝ) :
    horoDens p • ℓ (berezin (ArborealDecay.Horo.shiftL exV gS (nV vtx) (Kord M P)
        (Finset.univ : Finset Λ).toList F (horo p) *
        berL exV gS (nV vtx) (Finset.univ : Finset Λ).toList (horo p))) =
      exp (∑ i, p (.inl i) - 2 * ∑ m, p (.inl (vtx m))) *
        ℓ (berezin (horoF vtx F p * zL vtx p (Finset.univ : Finset Λ).toList)) := by
  set l := (Finset.univ : Finset Λ).toList
  simp only [smul_eq_mul]
  set c := cS (P := P) vtx fun i => p (.inl i)
  have hc : ∀ q, c (.inr q) = 1 := fun _ => rfl
  have hB := berezin_scaleA_of_param hc
    (ArborealDecay.Horo.shiftL exV gS (nV vtx) (Kord M P) l F (horo p) *
      berL exV gS (nV vtx) l (horo p))
  rw [map_mul, scaleA_berL, mul_smul_comm, map_smul] at hB
  have hps : 0 < ∏ m, pairScale c m := Finset.prod_pos fun m _ => by
    simp only [pairScale, c, cS, expScale]; positivity
  have hY : berezin (ArborealDecay.Horo.shiftL exV gS (nV vtx) (Kord M P) l F (horo p) *
      berL exV gS (nV vtx) l (horo p)) =
      (∏ m, pairScale c m)⁻¹ • ((l.map fun k => (hz (p (.inl k)) (p (.inr k)))⁻¹).prod •
        berezin (horoF vtx F p * zL vtx p l)) := by
    rw [show horoF vtx F p = scaleA c (ArborealDecay.Horo.shiftL exV gS (nV vtx) (Kord M P) l F
      (horo p)) from rfl, hB, smul_smul, inv_mul_cancel₀ hps.ne', one_smul]
  rw [hY, map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_assoc, horo_weight]

theorem integrable_berezin_horo {F : (Λ ⊕ Λ → ℝ) → SG M P} (hF : SSchwartz F)
    (ℓ : Module.Dual ℝ (SG M P)) :
    Integrable fun p => exp (∑ i, p (.inl i) - 2 * ∑ m, p (.inl (vtx m))) *
      ℓ (berezin (horoF vtx F p * zL vtx p (Finset.univ : Finset Λ).toList)) := by
  set l := (Finset.univ : Finset Λ).toList
  have hgd : ∀ k, (gdir exV gS k : (Λ ⊕ Λ → ℝ) → ℝ).HasTemperateGrowth := fun k => by
    convert hasTemperateGrowth_gdS k using 1; funext q; exact gdir_exV_gS_apply k q
  have hS := (hF.shiftL (v := exV) (n := nV vtx) (K := Kord M P) hasTemperateGrowth_gS l).mul_berL
    (n := nV vtx) hgd l
  have hI := ((hS.map (berezin : SG M P →ₗ[ℝ] SG M P)).sdecay ℓ).integrable
  rw [integrable_horo_iff] at hI
  exact hI.congr (ae_of_all _ fun p => horo_pointwise vtx F ℓ p)

end Integrable

theorem weight_H24 {Λ : Type*} [Fintype Λ] (p : Λ ⊕ Λ → ℝ) :
    ∑ i, p (.inl i) - 2 * ∑ m : Λ ⊕ Λ, p (.inl (vt Λ m)) = -3 * ∑ i, p (.inl i) := by
  rw [Fintype.sum_sum_type]
  simp only [vt, Sum.elim_inl, Sum.elim_inr, id]
  ring

/-! ### The pointwise identity -/

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

theorem inverse_mul_self_zS (p : Pt Λ) (i : Λ) : Ring.inverse ((hd p).zS i) * (hd p).zS i = 1 := by
  have hb : body ((hd p).zS i) ≠ 0 := by rw [body_zS]; exact (hz_pos _ _).ne'
  rw [inverse_eq_scomp_inv (isNilpotent_soul (isEven_zS p i)) hb,
    ← (isEven_zS p i).comm, mul_scomp_inv (isNilpotent_soul (isEven_zS p i)) hb]

theorem prod_inverse_mul_zL (p : Pt Λ) (l : List Λ) :
    (l.map fun i => Ring.inverse ((hd p).zS i)).prod * zL (vt Λ) p l = 1 := by
  induction l with
  | nil => simp [zL]
  | cons k l ih =>
    simp only [List.map_cons, List.prod_cons, zL, zSup_eq]
    calc Ring.inverse ((hd p).zS k) * (l.map fun i => Ring.inverse ((hd p).zS i)).prod *
          (zL (vt Λ) p l * (hd p).zS k)
        = Ring.inverse ((hd p).zS k) * ((l.map fun i => Ring.inverse ((hd p).zS i)).prod *
          zL (vt Λ) p l) * (hd p).zS k := by noncomm_ring
      _ = 1 := by rw [ih, mul_one, inverse_mul_self_zS]

theorem isEven_zL (p : Pt Λ) (l : List Λ) : IsEven (zL (vt Λ) p l : B Λ) := by
  induction l with
  | nil => exact IsEven.one
  | cons k l ih => rw [zL, zSup_eq]; exact ih.mul (isEven_zS p k)

variable {V : Type*} [Fintype V] [DecidableEq V] {w : V → V → ℝ} {ρ : V}

/-- The pinned couplings `β = w|_Λ`. -/
abbrev βr (w : V → V → ℝ) (ρ : V) : {i // i ≠ ρ} → {i // i ≠ ρ} → ℝ := fun a b => w a b
/-- The pinning field `h_i = w_{ρ i}`. -/
abbrev hr (w : V → V → ℝ) (ρ : V) : {i // i ≠ ρ} → ℝ := fun a => w ρ a

theorem T_integrandF (F : Pt {i // i ≠ ρ} → H24.A {i // i ≠ ρ}) (q : Pt {i // i ≠ ρ}) :
    T (integrandF (βr w ρ) (hr w ρ) F q) =
      ((Finset.univ : Finset {i // i ≠ ρ}).toList.map fun i => T (Ring.inverse (zH i q))).prod *
        (T (F q) * scomp Real.exp (-T (actionH (βr w ρ) (hr w ρ) q))) := by
  rw [integrandF, map_mul, map_mul, T_scomp _ (isEven_actionH _ _ q).neg, map_neg, zinvProd,
    map_list_prod, List.map_map]
  rfl

theorem horoF_integrand (hW : IsWGraph w) {F : Pt {i // i ≠ ρ} → H24.A {i // i ≠ ρ}}
    (hF : STG F) (hE : ∀ q, IsEven (F q)) (f : Pt {i // i ≠ ρ} → ℝ)
    (hf : ∀ p, horoF (vt _) (fun q => T (F q)) p = f p • (1 : B {i // i ≠ ρ}))
    (p : Pt {i // i ≠ ρ}) :
    horoF (vt _) (fun q => T (integrandF (βr w ρ) (hr w ρ) F q)) p *
        zL (vt _) p (Finset.univ : Finset {i // i ≠ ρ}).toList =
      (f p * exp (-Hb w ρ p)) • IsNilpotent.exp (-Qf w ρ p) := by
  set l := (Finset.univ : Finset {i // i ≠ ρ}).toList
  have hZ : ∀ i ∈ l, SSmooth fun q => T (Ring.inverse (zH i q)) :=
    fun i _ => (stg_zinv i).sSmooth.mapT
  have hA : SSmooth fun q => -T (actionH (βr w ρ) (hr w ρ) q) :=
    (stg_actionH _ _).sSmooth.mapT.neg
  have hAE : ∀ q, IsEven (-T (actionH (βr w ρ) (hr w ρ) q)) :=
    fun q => (isEven_T (isEven_actionH _ _ q)).neg
  have hEx : SSmooth fun q => scomp Real.exp (-T (actionH (βr w ρ) (hr w ρ) q)) :=
    hA.scomp isOpen_univ Real.contDiff_exp.contDiffOn hAE fun _ => Set.mem_univ _
  rw [funext (T_integrandF (w := w) F), horoF_mul _ (SSmooth.list_prod l hZ)
      ((hF.sSmooth.mapT).mul hEx), horoF_mul _ hF.sSmooth.mapT hEx, horoF_list_prod _ l (F := fun i q => T (Ring.inverse (zH i q))) hZ,
    horoF_scomp _ isOpen_univ Real.contDiff_exp.contDiffOn hA hAE (fun _ => Set.mem_univ _),
    horoF_neg _ (stg_actionH _ _).sSmooth.mapT, horoF_actionH_eq hW,
    scomp_exp_neg _ (isEven_Qf p) (body_Qf p), hf]
  simp only [horoF_zinv]
  set Y := (f p * exp (-Hb w ρ p)) • IsNilpotent.exp (-Qf w ρ p)
  have hY : f p • (1 : B {i // i ≠ ρ}) * (exp (-Hb w ρ p) • IsNilpotent.exp (-Qf w ρ p)) = Y := by
    rw [smul_mul_smul, one_mul]
  rw [hY, mul_assoc, ← (isEven_zL p l).comm Y, ← mul_assoc, prod_inverse_mul_zL, one_mul]

/-- **The horospherical integrand** (BCHS (2.61) before integration):
`e^{−3∑τ} body B(horoF(∏ z⁻¹ F e^{−H}) ∏ z_super) = f(τ, s) e^{−H̃(τ, s)}`. -/
theorem horo_integrand_eq (hW : IsWGraph w) (hconn : (supportGraph w).Connected)
    {F : Pt {i // i ≠ ρ} → H24.A {i // i ≠ ρ}} (hF : STG F) (hE : ∀ q, IsEven (F q))
    (f : Pt {i // i ≠ ρ} → ℝ)
    (hf : ∀ p, horoF (vt _) (fun q => T (F q)) p = f p • (1 : B {i // i ≠ ρ}))
    (p : Pt {i // i ≠ ρ}) :
    exp (-3 * ∑ i, p (.inl i)) * body (berezin
        (horoF (vt _) (fun q => T (integrandF (βr w ρ) (hr w ρ) F q)) p *
          zL (vt _) p (Finset.univ : Finset {i // i ≠ ρ}).toList)) =
      f p * exp (-ArborealDecay.Horo.Htil w ρ (tauP p) (sP p)) := by
  rw [horoF_integrand hW hF hE f hf p, map_smul, map_smul, body_berezin_exp_neg_Qf,
    exp_neg_Htil w ρ _ _ (Lmat_posDef hW hconn ρ _).det_pos, smul_eq_mul, Hb]
  simp only [tauP]
  rw [neg_add, exp_add, show -(3 * ∑ i, p (.inl i)) = -3 * ∑ i, p (.inl i) by ring, neg_mul]
  ring

end

end ArborealDecay.BCHS

end
