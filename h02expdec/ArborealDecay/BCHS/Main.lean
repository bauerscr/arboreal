module

public import ArborealDecay.BCHS.Assembly
public import ArborealDecay.Pinned.Main
public import ArborealDecay.TLaw

/-!
# BCHS Proposition 2.9 and the identities (A), (C)

Supplement `inp:A-BCHS`, `inp:C-BCHS`, `prop:A`, `thm:pinned-green` (ruling R8): for a finite
connected weighted graph `Γ = (V, w)` and any root `ρ` (cut vertices allowed, supplement
`rem:conn-hyp`),

* **(A)** `Z_eq_Zforest`: `Z^ρ_{w,3/2} = Z_Γ`;
* **(C)** `expect_Hinv_eq`: `E^ρ_w (H^{-1})_{ij} = P_Γ(i ↔ j, i ↮ ρ)` for `i, j ≠ ρ`.

Route (BCHS §2.4): the pinned `ℍ^{2|4}` model on `Λ = V ∖ ρ` with `β = w|_Λ`, `h_i = w_{ρ i}`
(`Pinned` holds by connectivity, `pinned_of_connected`).

* `ℍ^{0|2}` side: dimensional reduction (`H24.expectH_eq_expect_of_pinned`, `H24.expectH_yy`)
  and the pinned `ℍ^{0|2}` identities (`Pinned.thm_H02_pinned_denominator`,
  `Pinned.thm_H02_pinned_numerator`).
* horospherical side (`expectH_eq_integral`, BCHS Prop 2.9 (2.61)/(2.62)): transport to the
  two-flavour algebra, horospherical change of generators (`Horo.integral_berezin_horo_H24`),
  the substituted integrand (`horo_integrand_eq`), Fubini, and the `s`-Gaussians
  (`Horo.integral_exp_neg_Htil`, `Horo.integral_ss_exp_neg_Htil`).
-/

@[expose] public section

namespace ArborealDecay.BCHS

noncomputable section

open Finset Real Matrix MeasureTheory ArborealDecay.Super ArborealDecay.Super.H24
  ArborealDecay.Horo Grassmann
open ArborealDecay.TLaw (Lmat Hmat Phi ext IsWGraph ext_root ext_val supportGraph Lmat_posDef
  density Z expect supportGraph_adj)
open scoped ContDiff

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V] {w : V → V → ℝ} {ρ : V}

/-! ### Pinning -/

theorem pinned_of_connected (hW : IsWGraph w) (hconn : (supportGraph w).Connected) :
    Pinned (βr w ρ) (hr w ρ) := by
  have key : ∀ (u v : V) (W : (supportGraph w).Walk u v), v = ρ → ∀ hu : u ≠ ρ,
      ∃ k : {i // i ≠ ρ}, 0 < hr w ρ k ∧
        Relation.ReflTransGen (fun a b => 0 < βr w ρ a b) ⟨u, hu⟩ k := by
    intro u v W
    induction W with
    | nil => intro h hu; exact absurd h hu
    | @cons a b c hab W ih =>
      intro hc ha
      have hab' := (supportGraph_adj hW.symm).1 hab
      by_cases hb : b = ρ
      · subst hb
        exact ⟨⟨a, ha⟩, by simpa [hr, hW.symm] using hab'.2, Relation.ReflTransGen.refl⟩
      · obtain ⟨k, hk, hpath⟩ := ih hc hb
        exact ⟨k, hk, Relation.ReflTransGen.head (b := ⟨b, hb⟩) hab'.2 hpath⟩
  intro i
  obtain ⟨W⟩ := hconn.preconnected (i : V) ρ
  exact key _ _ W rfl i.2

/-! ### The horospherical side of Proposition 2.9 -/

theorem toA_T (x : H24.A {i // i ≠ ρ}) : toA (T x) = x := toA.apply_symm_apply x

theorem vt_eq : (vt {i // i ≠ ρ}) = Sum.elim id id := rfl

/-- **BCHS Proposition 2.9** ((2.61), unnormalized, for superfunctions that become scalars in
horospherical coordinates): `[F]^{ℍ^{2|4}}_{β,h} = (2π)^{-|Λ|} ∫ dτ ∫ ds g(τ, s) e^{−H̃(τ, s)}`,
with the integrand integrable on `ℝ^Λ × ℝ^Λ`. -/
theorem expectH_eq_integral (hW : IsWGraph w) (hconn : (supportGraph w).Connected)
    {F : Pt {i // i ≠ ρ} → H24.A {i // i ≠ ρ}} (hF : STG F) (hE : ∀ q, IsEven (F q))
    (g : ({i // i ≠ ρ} → ℝ) → ({i // i ≠ ρ} → ℝ) → ℝ)
    (hg : ∀ p, horoF (vt _) (fun q => T (F q)) p = g (tauP p) (sP p) • (1 : B {i // i ≠ ρ})) :
    Integrable (fun x : ({i // i ≠ ρ} → ℝ) × ({i // i ≠ ρ} → ℝ) =>
        g x.1 x.2 * exp (-ArborealDecay.Horo.Htil w ρ x.1 x.2)) ∧
      expectH (βr w ρ) (hr w ρ) F = ((2 * π) ^ Fintype.card {i // i ≠ ρ})⁻¹ *
        ∫ τ, ∫ s, g τ s * exp (-ArborealDecay.Horo.Htil w ρ τ s) := by
  set G : ({i // i ≠ ρ} → ℝ) × ({i // i ≠ ρ} → ℝ) → ℝ :=
    fun x => g x.1 x.2 * exp (-ArborealDecay.Horo.Htil w ρ x.1 x.2)
  have hP := pinned_of_connected (ρ := ρ) hW hconn
  have hS : SSchwartz fun q => T (integrandF (βr w ρ) (hr w ρ) F q) :=
    (sschwartz_integrandF (fun i j => hW.nonneg _ _) (fun i => hW.nonneg _ _) hP hF).map
      (T (Λ := {i // i ≠ ρ})).toAlgHom.toLinearMap
  set ℓ : Module.Dual ℝ (B {i // i ≠ ρ}) := (body : B {i // i ≠ ρ} →ₐ[ℝ] ℝ).toLinearMap
  have hpt : ∀ p : Pt {i // i ≠ ρ}, exp (-3 * ∑ i, p (.inl i)) *
      ℓ (berezin (horoF (Sum.elim id id) (fun q => T (integrandF (βr w ρ) (hr w ρ) F q)) p *
        zL (Sum.elim id id) p (Finset.univ : Finset {i // i ≠ ρ}).toList)) = G (tauP p, sP p) :=
    fun p => horo_integrand_eq hW hconn hF hE (fun p => g (tauP p) (sP p)) hg p
  -- integrability on `ℝ^{Λ ⊕ Λ}`
  have hI := integrable_berezin_horo (vt {i // i ≠ ρ}) hS ℓ
  have hI' : Integrable fun p : Pt {i // i ≠ ρ} => G (tauP p, sP p) :=
    hI.congr (ae_of_all _ fun p => by
      simp only
      rw [weight_H24]
      exact hpt p)
  set e := MeasurableEquiv.sumPiEquivProdPi (fun _ : {i // i ≠ ρ} ⊕ {i // i ≠ ρ} => ℝ)
  have hmp : MeasurePreserving e volume volume :=
    volume_measurePreserving_sumPiEquivProdPi _
  have he : ∀ p : Pt {i // i ≠ ρ}, e p = (tauP p, sP p) := fun p => rfl
  have hGint : Integrable G := by
    rw [← hmp.integrable_comp_emb e.measurableEmbedding]
    exact hI'.congr (ae_of_all _ fun p => by simp only [Function.comp_apply, he])
  refine ⟨hGint, ?_⟩
  -- the integral
  rw [expectH_eq_intH]
  congr 1
  have h1 : ∀ p, body (B1 (Finset.univ : Finset {i // i ≠ ρ}).toList
      (berezin (integrandF (βr w ρ) (hr w ρ) F p))) =
      ℓ (berezin (T (integrandF (βr w ρ) (hr w ρ) F p))) := fun p => by
    conv_lhs => rw [← toA_T (integrandF (βr w ρ) (hr w ρ) F p)]
    rw [body_B1_berezin_toA]; rfl
  simp_rw [h1]
  rw [integral_berezin_horo_H24 hS ℓ, integral_congr_ae (ae_of_all _ hpt)]
  have h2 : ∫ p : Pt {i // i ≠ ρ}, G (tauP p, sP p) = ∫ x, G x := by
    rw [← hmp.integral_comp' G]; rfl
  rw [h2, ← integral_prod G hGint]
  rfl

/-! ### `F ≡ 1`: identity (A) -/

theorem horoF_T_one (p : Pt {i // i ≠ ρ}) :
    horoF (vt _) (fun q => T ((fun _ : Pt {i // i ≠ ρ} => (1 : H24.A {i // i ≠ ρ})) q)) p =
      (fun _ _ => (1 : ℝ)) (tauP p) (sP p) • (1 : B {i // i ≠ ρ}) := by
  simp only [map_one, one_smul]
  rw [horoF_const, map_one]

theorem integral_density_eq_expectH (hW : IsWGraph w) (hconn : (supportGraph w).Connected) :
    ∫ τ, density w ρ (3 / 2) τ = expectH (βr w ρ) (hr w ρ) fun _ => 1 := by
  obtain ⟨-, h⟩ := expectH_eq_integral hW hconn (ρ := ρ) stg_one (fun _ => IsEven.one)
    (fun _ _ => 1) horoF_T_one
  rw [h]
  simp only [one_mul]
  simp_rw [ArborealDecay.Horo.integral_exp_neg_Htil hW hconn]
  rw [integral_const_mul, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

theorem expectH_one_eq_Zforest (hW : IsWGraph w) (hconn : (supportGraph w).Connected) :
    expectH (βr w ρ) (hr w ρ) (fun _ => 1) = H02.Zforest w hW.symm := by
  have hP := pinned_of_connected (ρ := ρ) hW hconn
  have e : (fun _ : Pt {i // i ≠ ρ} => (1 : H24.A {i // i ≠ ρ})) = obsH (Obs.const 1) := by
    funext p; simp [obsH, Obs.eval]
  rw [e, expectH_eq_expect_of_pinned (fun i j => hW.nonneg _ _) (fun i => hW.nonneg _ _) hP
    (Obs.const 1) trivial]
  have : obs0 (Λ := {i // i ≠ ρ}) (Obs.const 1) = 1 := by simp [obs0, Obs.eval]
  rw [this]
  exact Pinned.thm_H02_pinned_denominator hW.symm ρ

theorem integral_density_eq_toReal_Z (hW : IsWGraph w) (hconn : (supportGraph w).Connected) :
    ∫ τ, density w ρ (3 / 2) τ = (Z w ρ (3 / 2)).toReal := by
  rw [Z, integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun τ => (ArborealDecay.TLaw.density_pos hW hconn ρ _ τ).le)
    (ArborealDecay.TLaw.continuous_density hW hconn ρ _).aestronglyMeasurable]

/-- **Identity (A)** (supplement `prop:A`, via `inp:A-BCHS`): for a finite connected weighted
graph and any root, `Z^ρ_{w,3/2} = Z_Γ`. -/
theorem Z_eq_Zforest (w : V → V → ℝ) (hW : IsWGraph w) (hconn : (supportGraph w).Connected)
    (ρ : V) : Z w ρ (3 / 2) = ENNReal.ofReal (H02.Zforest w hW.symm) := by
  rw [← expectH_one_eq_Zforest (ρ := ρ) hW hconn, ← integral_density_eq_expectH hW hconn,
    integral_density_eq_toReal_Z hW hconn,
    ENNReal.ofReal_toReal (ArborealDecay.TLaw.Z_lt_top hW hconn ρ (by norm_num)).ne]

/-! ### `F = y_i y_j`: identity (C) -/

theorem Hmat_inv_apply (hW : IsWGraph w) (hconn : (supportGraph w).Connected) (t : V → ℝ)
    (i j : {i // i ≠ ρ}) :
    (Hmat w ρ t)⁻¹ i j = exp (t i) * (Lmat w ρ t)⁻¹ i j * exp (t j) := by
  set L := Lmat w ρ t
  set D : Matrix {i // i ≠ ρ} {i // i ≠ ρ} ℝ := diagonal fun i => exp (-t i)
  set E : Matrix {i // i ≠ ρ} {i // i ≠ ρ} ℝ := diagonal fun i => exp (t i)
  have hED : E * D = 1 := by
    show diagonal (fun i : {i // i ≠ ρ} => exp (t i)) *
      diagonal (fun i : {i // i ≠ ρ} => exp (-t i)) = 1
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i; rw [← exp_add, add_neg_cancel, exp_zero]
  have hL : L⁻¹ * L = 1 :=
    nonsing_inv_mul L ((isUnit_iff_ne_zero).2 (Lmat_posDef hW hconn ρ t).det_pos.ne')
  have hinv : (Hmat w ρ t)⁻¹ = E * L⁻¹ * E := by
    refine inv_eq_left_inv ?_
    rw [ArborealDecay.TLaw.Hmat_eq]
    change E * L⁻¹ * E * (D * L * D) = 1
    calc E * L⁻¹ * E * (D * L * D) = E * L⁻¹ * (E * D) * L * D := by noncomm_ring
      _ = 1 := by rw [hED, Matrix.mul_one, Matrix.mul_assoc E, hL, Matrix.mul_one, hED]
  rw [hinv, mul_diagonal, diagonal_mul]

theorem T_Fyy (i j : {i // i ≠ ρ}) (q : Pt {i // i ≠ ρ}) :
    T (Fyy i j q) = Yc i q * Yc j q := by
  rw [Fyy, map_smul, map_one, Yc, Yc, smul_mul_smul, one_mul]

theorem horoF_T_Fyy (i j : {i // i ≠ ρ}) (p : Pt {i // i ≠ ρ}) :
    horoF (vt _) (fun q => T (Fyy i j q)) p =
      (fun (τ s : {i // i ≠ ρ} → ℝ) => exp (τ i) * s i * (exp (τ j) * s j)) (tauP p) (sP p) •
        (1 : B {i // i ≠ ρ}) := by
  rw [funext (T_Fyy (ρ := ρ) i j), horoF_mul _ (sSmooth_Yc i) (sSmooth_Yc j), horoF_Yc, horoF_Yc,
    HData.yS, HData.yS, smul_mul_smul, one_mul]
  rfl

theorem isEven_Fyy (i j : {i // i ≠ ρ}) (q : Pt {i // i ≠ ρ}) : IsEven (Fyy i j q) :=
  IsEven.one.smul _

theorem integral_Hinv_density (hW : IsWGraph w) (hconn : (supportGraph w).Connected)
    (i j : {i // i ≠ ρ}) :
    ∫ τ, (Hmat w ρ (ext ρ τ))⁻¹ i j * density w ρ (3 / 2) τ =
      expectH (βr w ρ) (hr w ρ) (Fyy i j) := by
  obtain ⟨-, h⟩ := expectH_eq_integral hW hconn (ρ := ρ) (stg_Fyy i j) (isEven_Fyy i j)
    (fun τ s => exp (τ i) * s i * (exp (τ j) * s j)) (horoF_T_Fyy i j)
  rw [h]
  have hs : ∀ τ : {i // i ≠ ρ} → ℝ, ∫ s, exp (τ i) * s i * (exp (τ j) * s j) *
      exp (-ArborealDecay.Horo.Htil w ρ τ s) =
      (2 * π) ^ Fintype.card {i // i ≠ ρ} *
        ((Hmat w ρ (ext ρ τ))⁻¹ i j * density w ρ (3 / 2) τ) := fun τ => by
    have e : ∀ s : {i // i ≠ ρ} → ℝ, exp (τ i) * s i * (exp (τ j) * s j) *
        exp (-ArborealDecay.Horo.Htil w ρ τ s) =
        s i * s j * exp (τ i + τ j) * exp (-ArborealDecay.Horo.Htil w ρ τ s) := fun s => by
      rw [exp_add]; ring
    simp_rw [e]
    rw [ArborealDecay.Horo.integral_ss_exp_neg_Htil hW hconn,
      ArborealDecay.Horo.integral_exp_neg_Htil hW hconn, Hmat_inv_apply hW hconn, ext_val,
      ext_val, exp_add]
    ring
  simp_rw [hs]
  rw [integral_const_mul, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

theorem reach_event_symm (F : SimpleGraph V) (i j : {i // i ≠ ρ}) :
    (F.Reachable i j ∧ ¬F.Reachable i ρ) ↔ (F.Reachable j i ∧ ¬F.Reachable j ρ) := by
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1.symm, fun h => h2 (h1.trans h)⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1.symm, fun h => h2 (h1.trans h)⟩

open Classical in
theorem expectH_Fyy_eq (hW : IsWGraph w) (hconn : (supportGraph w).Connected)
    (i j : {i // i ≠ ρ}) :
    expectH (βr w ρ) (hr w ρ) (Fyy i j) =
      ∑ F : SimpleGraph V with F.IsAcyclic ∧ F.Reachable i j ∧ ¬F.Reachable i ρ,
        H02.forestWeight w hW.symm F := by
  have hP := pinned_of_connected (ρ := ρ) hW hconn
  rw [expectH_yy (fun i j => hW.nonneg _ _) (fun i => hW.nonneg _ _) hP i j, H02.expect_add,
    Pinned.thm_H02_pinned_numerator hW.symm ρ i j, Pinned.thm_H02_pinned_numerator hW.symm ρ j i]
  have : (∑ F : SimpleGraph V with F.IsAcyclic ∧ F.Reachable j i ∧ ¬F.Reachable j ρ,
      H02.forestWeight w hW.symm F) =
      ∑ F : SimpleGraph V with F.IsAcyclic ∧ F.Reachable i j ∧ ¬F.Reachable i ρ,
        H02.forestWeight w hW.symm F := by
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext F; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [reach_event_symm F j i]
  rw [this]; ring

/-- **Identity (C)** (supplement `thm:pinned-green`, via `inp:C-BCHS`): for a finite connected
weighted graph, any root `ρ` and `i, j ≠ ρ`, `E^ρ_w (H^{-1})_{ij} = P_Γ(i ↔ j, i ↮ ρ)`. -/
theorem expect_Hinv_eq (w : V → V → ℝ) (hW : IsWGraph w) (hconn : (supportGraph w).Connected)
    (ρ : V) (i j : {x // x ≠ ρ}) :
    expect w ρ (3 / 2) (fun τ => (Hmat w ρ (ext ρ τ))⁻¹ i j) =
      H02.arborealProb w hW.symm (fun F => F.Reachable i j ∧ ¬ F.Reachable i ρ) := by
  have hZ : (Z w ρ (3 / 2)).toReal = H02.Zforest w hW.symm := by
    rw [← integral_density_eq_toReal_Z hW hconn, integral_density_eq_expectH hW hconn,
      expectH_one_eq_Zforest hW hconn]
  rw [ArborealDecay.TLaw.expect, hZ, integral_Hinv_density hW hconn, expectH_Fyy_eq hW hconn, H02.arborealProb,
    div_eq_inv_mul]
  exact congrArg _ (Finset.sum_congr (by ext F; simp) fun _ _ => rfl)

end

end ArborealDecay.BCHS

end
