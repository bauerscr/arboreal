import Obs2.Loc.PauliMass
import Obs2.Loc.LocGram

/-!
# The Lipschitz bound of the mass functionals in the covariance (Pauli + locality)

For a functional `m` with `m(e^{ℒ_{Γ+cJ}}F) = m(e^{ℒ_Γ}F)` (`PauliInv`; `m₁^{(±)}`, `m₂`,
`Obs2.Loc.PauliMass`) and `F ∈ 𝒩(Y)`:

* **`pauli_lip_abs`**: if `S, C` agree on `Y × Y` with `Ŝ + c_S`, `Ĉ + c_C` and `Ŝ`, `Ĉ` have
  Gram representations with constants `≤ σ`, `γ ≤ 2σ` at the norm scale, then
  `|m(e^{ℒ_{S+C}}F) − m(e^{ℒ_S}F)| ≤ M_σ (γ/2σ)² ‖F‖_{T(4σ)}` (`|m(G)| ≤ M_σ‖G‖_{T(σ)}`).
* **`pauli_lip_loc`**: the same with `S = ∑_{i∈I} C_i` for covariances `C_i`, `C` with Gram
  representations at their own scales `h_i ≥ R` and `Y` in the box of radius `R`: the constants
  are the localised ones `locC d R γ_i h_i = 16 d K² R γ_i²/h_i` (`gram_loc`, `gram_finsum`), so
  the bound is `M_σ (locC d R γ h)/(4σ²) ‖F‖_{T(4σ)}` once `∑_i locC d R γ_i h_i ≤ σ²` and
  `locC d R γ h ≤ 4σ²`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Obs2

noncomputable section

open Finset Grassmann Loc FRD Step2

variable {d L N : ℕ} [NeZero L]

/-- The Pauli invariance of a functional. -/
def PauliInv (m : Alg d L N →ₗ[ℂ] ℂ) : Prop :=
  ∀ (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) (c : ℂ) (F : Alg d L N),
    m (expLC (Γ + c • Jmat _) F) = m (expLC Γ F)

theorem pauliInv_mass1 : PauliInv (mass1L (d := d) (L := L) (N := N) (-1)) :=
  fun Γ c F => mass1_expLC_add_J Γ c F

theorem pauliInv_mass2 : PauliInv (mass2L (d := d) (L := L) (N := N)) :=
  fun Γ c F => mass2_expLC_add_J Γ c F

theorem gramBound_mono {Λ : Type*} [DecidableEq Λ] [Fintype Λ] {E : Type*} [Fintype E]
    [DecidableEq E] [AddAction (E → ℕ) Λ] {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {p : ℕ} {h c c' : ℝ} (hh : 0 < h) {F G : Λ → H}
    (hB : GramBound E p h c F G) (hc : c ≤ c') : GramBound E p h c' F G := by
  intro a ha x
  have hX : 0 ≤ (h ^ mabs a)⁻¹ := by positivity
  exact ⟨(hB a ha x).1.trans (mul_le_mul_of_nonneg_right hc hX),
    (hB a ha x).2.trans (mul_le_mul_of_nonneg_right hc hX)⟩

/-- **The abstract Lipschitz bound.** -/
theorem pauli_lip_abs {m : Alg d L N →ₗ[ℂ] ℂ} (hm : PauliInv m) {k : ℕ} {M σ : ℝ}
    (hσ : 0 < σ) (hM : 0 ≤ M)
    (hmb : ∀ G : Alg d L N, ‖m G‖ ≤ M * (Tj d (L : ℝ) k σ G).toReal)
    {Y : Set (Lam d L N)} {F : Alg d L N} (hF : F ∈ NX Y)
    {S C Sh Ch : Matrix (Lam d L N) (Lam d L N) ℂ} {cS cC : ℂ}
    (hS : ∀ x ∈ Y, ∀ y ∈ Y, S x y = Sh x y + cS) (hC : ∀ x ∈ Y, ∀ y ∈ Y, C x y = Ch x y + cC)
    {H₁ H₂ : Type} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [NormedAddCommGroup H₂]
    [InnerProductSpace ℂ H₂] {F₁ G₁ : Lam d L N → H₁} {F₂ G₂ : Lam d L N → H₂}
    (hSg : IsGram Sh F₁ G₁) (hSb : GramBound (Dir d) (pPhi d) ((L : ℝ) ^ k) σ F₁ G₁)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ ≤ 2 * σ)
    (hCg : IsGram Ch F₂ G₂) (hCb : GramBound (Dir d) (pPhi d) ((L : ℝ) ^ k) γ F₂ G₂) :
    ‖m (expLC (S + C) F) - m (expLC S F)‖ ≤
      M * (γ / (2 * σ)) ^ 2 * (Tj d (L : ℝ) k (4 * σ) F).toReal := by
  have hL0 : (0 : ℝ) < (L : ℝ) ^ k := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) _
  have e1 : expLC (S + C) F = expLC ((Sh + Ch) + (cS + cC) • Jmat _) F := by
    refine expLC_congr_NX hF fun x hx y hy => ?_
    simp only [Matrix.add_apply, Matrix.smul_apply, Jmat, smul_eq_mul, mul_one, hS x hx y hy,
      hC x hx y hy]
    ring
  have e2 : expLC S F = expLC (Sh + cS • Jmat _) F := by
    refine expLC_congr_NX hF fun x hx y hy => ?_
    simp only [Matrix.add_apply, Matrix.smul_apply, Jmat, smul_eq_mul, mul_one, hS x hx y hy]
  rw [e1, e2, hm, hm, expLC_add Sh Ch, ← map_sub m, ← map_sub (expLC Sh)]
  refine (hmb _).trans ?_
  have h1 : Tj d (L : ℝ) k σ (expLC Sh (expLC Ch F - F)) ≤
      Tj d (L : ℝ) k (2 * σ) (expLC Ch F - F) := by
    rw [← ECC_theta]
    exact tNorm_ECC_theta_le hL0 hσ hSg hSb _
  have h2 : Tj d (L : ℝ) k (2 * σ) (expLC Ch F - F) ≤
      ENNReal.ofReal ((γ / (2 * σ)) ^ 2) * Tj d (L : ℝ) k (2 * (2 * σ)) F :=
    tNorm_expLC_sub_le hL0 (by positivity) hγ0 hγ hCg hCb F
  have h3 := h1.trans h2
  have hfin : Tj d (L : ℝ) k (2 * (2 * σ)) F ≠ ⊤ := tNorm_ne_top hL0 (by positivity) F
  have h4 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) h3
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    show 2 * (2 * σ) = 4 * σ by ring] at h4
  calc M * (Tj d (L : ℝ) k σ (expLC Sh (expLC Ch F - F))).toReal
      ≤ M * ((γ / (2 * σ)) ^ 2 * (Tj d (L : ℝ) k (4 * σ) F).toReal) :=
        mul_le_mul_of_nonneg_left h4 hM
    _ = _ := by ring

/-- The squared localised Gram constant `16 d K² R γ²/h`. -/
def locC (d : ℕ) (R γ h : ℝ) : ℝ := 16 * d * locK d ^ 2 * R * γ ^ 2 / h

theorem locC_nonneg {R γ h : ℝ} (hR : 0 ≤ R) (hh : 0 ≤ h) : 0 ≤ locC d R γ h := by
  unfold locC; positivity

/-- `gram_loc` with the optimal `μ`: a Gram constant `g` with `g² = locC d R γ₁ h₁`. -/
theorem gram_loc' (hd : 1 ≤ d) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {C : Matrix (Lam d L N) (Lam d L N) ℂ} {Fv Gv : Lam d L N → H}
    (hC : IsGram C Fv Gv) {h₁ γ₁ : ℝ} (hγ₁ : 0 < γ₁)
    (hB : GramBound (Dir d) (pPhi d) h₁ γ₁ Fv Gv) {R h : ℝ} (hh : 0 < h) (hhR : h ≤ R)
    (hRh : R ≤ h₁) (hR : 2 * (pPhi d : ℝ) + 1 ≤ R)
    (hN : 2 * (⌈2 * R⌉₊ + 2 * pPhi d) < L ^ N) (x₀ : Lam d L N) :
    ∃ (Ch : Matrix (Lam d L N) (Lam d L N) ℂ) (F' G' : Lam d L N → WithLp 2 (H × H)),
      IsGram Ch F' G' ∧
      GramBound (Dir d) (pPhi d) h (Real.sqrt (locC d R γ₁ h₁)) F' G' ∧
      ∀ x y, (supNorm (x - x₀) : ℝ) ≤ R → (supNorm (y - x₀) : ℝ) ≤ R →
        C x y = Ch x y + C x₀ x₀ := by
  have hR0 : 0 < R := by have : (0 : ℝ) ≤ pPhi d := Nat.cast_nonneg _; linarith
  have hh₁ : 0 < h₁ := hR0.trans_le hRh
  set δ : ℝ := 4 * d * R * γ₁ / h₁ with hδ
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hδ0 : 0 < δ := by positivity
  set μ : ℝ := Real.sqrt δ / Real.sqrt γ₁
  have hsδ : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ0
  have hsγ : 0 < Real.sqrt γ₁ := Real.sqrt_pos.2 hγ₁
  have hμ : 0 < μ := div_pos hsδ hsγ
  obtain ⟨F', G', hB', hagree⟩ := gram_loc hd hC hγ₁.le hB hh hhR hRh hR hN x₀ hμ
  refine ⟨fun x y => inner ℂ (F' x) (G' y), F', G', fun _ _ => rfl, ?_, ?_⟩
  · refine gramBound_mono hh hB' (le_of_eq ?_)
    have e1 : μ⁻¹ * δ = Real.sqrt δ * Real.sqrt γ₁ := by
      simp only [μ, inv_div]
      rw [div_mul_eq_mul_div, mul_div_assoc, Real.div_sqrt]; ring
    have e2 : μ * γ₁ = Real.sqrt δ * Real.sqrt γ₁ := by
      simp only [μ]
      rw [div_mul_eq_mul_div, mul_div_assoc, Real.div_sqrt]
    rw [e1, e2]
    have hK := one_le_locK d
    have hsq : (Real.sqrt δ * Real.sqrt γ₁) ^ 2 = δ * γ₁ := by
      rw [mul_pow, Real.sq_sqrt hδ0.le, Real.sq_sqrt hγ₁.le]
    have hlc : locC d R γ₁ h₁ = (2 * locK d * (Real.sqrt δ * Real.sqrt γ₁)) ^ 2 := by
      rw [show (2 * locK d * (Real.sqrt δ * Real.sqrt γ₁)) ^ 2 =
        4 * locK d ^ 2 * (Real.sqrt δ * Real.sqrt γ₁) ^ 2 by ring, hsq, hδ, locC]
      field_simp
      ring
    rw [hlc, Real.sqrt_sq (by positivity)]
    ring
  · intro x y hx hy
    show C x y = inner ℂ (F' x) (G' y) + C x₀ x₀
    rw [hagree x y hx hy]; ring

/-- **The localised Lipschitz bound.** -/
theorem pauli_lip_loc (hd : 1 ≤ d) {m : Alg d L N →ₗ[ℂ] ℂ} (hm : PauliInv m) {k : ℕ}
    {M σ : ℝ} (hσ : 0 < σ) (hM : 0 ≤ M)
    (hmb : ∀ G : Alg d L N, ‖m G‖ ≤ M * (Tj d (L : ℝ) k σ G).toReal)
    {R : ℝ} (hhR : (L : ℝ) ^ k ≤ R) (hR : 2 * (pPhi d : ℝ) + 1 ≤ R)
    (hN : 2 * (⌈2 * R⌉₊ + 2 * pPhi d) < L ^ N) (x₀ : Lam d L N)
    {Y : Set (Lam d L N)} (hY : ∀ y ∈ Y, (supNorm (y - x₀) : ℝ) ≤ R)
    {F : Alg d L N} (hF : F ∈ NX Y)
    {ι : Type*} [DecidableEq ι] (I : Finset ι) (Cs : ι → Matrix (Lam d L N) (Lam d L N) ℂ)
    (hs γs : ι → ℝ) (hγs : ∀ i ∈ I, 0 < γs i) (hRs : ∀ i ∈ I, R ≤ hs i)
    (hrep : ∀ i ∈ I, ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (Fv Gv : Lam d L N → H), IsGram (Cs i) Fv Gv ∧ GramBound (Dir d) (pPhi d) (hs i) (γs i) Fv Gv)
    (C : Matrix (Lam d L N) (Lam d L N) ℂ) {h₁ γ₁ : ℝ} (hγ₁ : 0 < γ₁) (hR₁ : R ≤ h₁)
    (hrep₁ : ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (Fv Gv : Lam d L N → H), IsGram C Fv Gv ∧ GramBound (Dir d) (pPhi d) h₁ γ₁ Fv Gv)
    (hsumS : ∑ i ∈ I, locC d R (γs i) (hs i) ≤ σ ^ 2) (hsumC : locC d R γ₁ h₁ ≤ (2 * σ) ^ 2) :
    ‖m (expLC (∑ i ∈ I, Cs i + C) F) - m (expLC (∑ i ∈ I, Cs i) F)‖ ≤
      M * (locC d R γ₁ h₁ / (2 * σ) ^ 2) * (Tj d (L : ℝ) k (4 * σ) F).toReal := by
  have hL0 : (0 : ℝ) < (L : ℝ) ^ k := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) _
  have hR0 : 0 < R := hL0.trans_le hhR
  -- localise every `C_i`
  have hloc : ∀ i ∈ I, ∃ (Ch : Matrix (Lam d L N) (Lam d L N) ℂ),
      (∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
        (Fv Gv : Lam d L N → H), IsGram Ch Fv Gv ∧
          GramBound (Dir d) (pPhi d) ((L : ℝ) ^ k) (Real.sqrt (locC d R (γs i) (hs i))) Fv Gv) ∧
      ∀ x y, (supNorm (x - x₀) : ℝ) ≤ R → (supNorm (y - x₀) : ℝ) ≤ R →
        Cs i x y = Ch x y + Cs i x₀ x₀ := by
    intro i hi
    obtain ⟨H, i1, i2, Fv, Gv, hG, hB⟩ := hrep i hi
    obtain ⟨Ch, F', G', hG', hB', hag⟩ :=
      gram_loc' hd hG (hγs i hi) hB hL0 hhR (hRs i hi) hR hN x₀
    exact ⟨Ch, ⟨_, inferInstance, inferInstance, F', G', hG', hB'⟩, hag⟩
  choose! Chs hChs hags using hloc
  obtain ⟨HS, iS1, iS2, FS, GS, hSg, hSb⟩ := gram_finsum (E := Dir d) (p := pPhi d) I Chs
    (fun i => Real.sqrt (locC d R (γs i) (hs i))) (fun i => Real.sqrt_nonneg _) hL0
    (fun i hi => hChs i hi)
  obtain ⟨H, i1, i2, Fv, Gv, hG, hB⟩ := hrep₁
  obtain ⟨Ch, F', G', hG', hB', hag⟩ := gram_loc' hd hG hγ₁ hB hL0 hhR hR₁ hR hN x₀
  have hsq : ∑ i ∈ I, Real.sqrt (locC d R (γs i) (hs i)) ^ 2 = ∑ i ∈ I, locC d R (γs i) (hs i) :=
    sum_congr rfl fun i hi => Real.sq_sqrt (locC_nonneg hR0.le (hR0.le.trans (hRs i hi)))
  have hSb' : GramBound (Dir d) (pPhi d) ((L : ℝ) ^ k) σ FS GS := by
    refine gramBound_mono hL0 hSb ?_
    rw [hsq]
    exact (Real.sqrt_le_sqrt hsumS).trans_eq (Real.sqrt_sq hσ.le)
  have hγC : Real.sqrt (locC d R γ₁ h₁) ≤ 2 * σ :=
    (Real.sqrt_le_sqrt hsumC).trans_eq (Real.sqrt_sq (by positivity))
  have key := pauli_lip_abs hm hσ hM hmb hF (S := ∑ i ∈ I, Cs i) (C := C)
    (Sh := ∑ i ∈ I, Chs i) (Ch := Ch) (cS := ∑ i ∈ I, Cs i x₀ x₀) (cC := C x₀ x₀)
    (fun x hx y hy => by
      rw [Matrix.sum_apply, Matrix.sum_apply, ← sum_add_distrib]
      exact sum_congr rfl fun i hi => hags i hi x y (hY x hx) (hY y hy))
    (fun x hx y hy => hag x y (hY x hx) (hY y hy)) hSg hSb' (Real.sqrt_nonneg _) hγC hG' hB'
  refine key.trans (le_of_eq ?_)
  rw [div_pow, Real.sq_sqrt (locC_nonneg hR0.le (hR0.le.trans hR₁))]

end

end Obs2
