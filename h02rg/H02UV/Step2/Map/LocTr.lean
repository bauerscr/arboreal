import Step2.Map.StepFinal
import Step.SymAlg
import Step.Coupling
import Loc.AutGen
import Loc.Loc2

/-!
# Localisation and translations (`h02uv-outline.tex`, Lemma `lem:loc-tr`)

* `expLC_autAlg`, `autAlg_EthE`: `𝔼_C θ` commutes with lattice maps preserving `C`.
* `tNorm_two_le_of_deg`: for `F` without coefficients of length `> 4`,
  `‖F‖_{T(2ℓ)} ≤ 16 ‖F‖_{T(ℓ)}`; this applies to `Loc_X F` (`coeff_Loc2XY_of_lt`).
* `mu4_base_indep`: the quartic pairing `μ⁽⁴⁾` does not depend on the base point (the
  lower-order terms of a shift vanish by antisymmetry of the coefficients); `mu4_transl`:
  it is translation invariant. Hence `Loc4XY_transl` and `Loc2X_transl`:
  `τ_t Loc_X F = Loc_{X + t} τ_t F` (Lemma `lem:loc-tr`(i)).
* `Loc2X_uniform`: `Loc_X` is the identity on `κ + ∑ c_M M(X) + ∑ e_{ik} M⁽⁴⁾_{ik}(X)`
  (Lemma `lem:loc-tr`(iii)), and `Loc2X_form`: `Loc_X F` has this form.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Matrix

variable {d L N : ℕ} [NeZero L]

/-! ### `𝔼θ` and lattice maps -/

theorem D_autAlg (E : Lam d L N ≃ Lam d L N) (a : Sf (Lam d L N)) (H : Alg d L N) :
    D a (autAlg E H) = autAlg E (D (E.symm a.1, a.2) H) := by
  rw [autAlg, D_map]; rfl

theorem LopC_autAlg (E : Lam d L N ≃ Lam d L N) {C : Matrix (Lam d L N) (Lam d L N) ℂ}
    (hC : ∀ x y, C (E x) (E y) = C x y) (G : Alg d L N) :
    LopC C (autAlg E G) = autAlg E (LopC C G) := by
  simp only [LopC_apply, D_autAlg, map_sum, map_smul]
  rw [← Equiv.sum_comp E]
  refine sum_congr rfl fun x _ => ?_
  rw [← Equiv.sum_comp E]
  refine sum_congr rfl fun y _ => ?_
  simp [hC]

theorem expLC_autAlg (E : Lam d L N ≃ Lam d L N) {C : Matrix (Lam d L N) (Lam d L N) ℂ}
    (hC : ∀ x y, C (E x) (E y) = C x y) (G : Alg d L N) :
    expLC C (autAlg E G) = autAlg E (expLC C G) := by
  have hc : LopC C ∘ₗ (autAlg E).toLinearMap = (autAlg E).toLinearMap ∘ₗ LopC C :=
    LinearMap.ext fun G => LopC_autAlg E hC G
  have h := Module.End.commute_exp_left_of_commute (LopC_isNilpotent C) (LopC_isNilpotent C) hc
  exact LinearMap.congr_fun h G

/-! ### Elements of degree at most `4` -/

section Deg

variable {X : Type*} [DecidableEq X] [Fintype X] {E : Type*} [Fintype E] [DecidableEq E]
  [AddAction (E → ℕ) X]

/-- For `F` without coefficients of length `> 4`, `‖F‖_{T(2ℓ)} ≤ 16 ‖F‖_{T(ℓ)}`. -/
theorem tNorm_two_le_of_deg (p : ℕ) {h ℓ : ℝ} (hh : 0 ≤ h) (hℓ : 0 < ℓ) {F : Grassmann.N X}
    (hF : ∀ (n : ℕ) (z : Fin n → Sf X), 4 < n → coeff F z = 0) :
    tNorm E p h (2 * ℓ) F ≤ 16 * tNorm E p h ℓ F := by
  unfold tNorm
  refine iSup₂_le fun g hg => ?_
  set g' : TestFn X := fun n z => if n ≤ 4 then ((1 / 16 : ℝ) : ℂ) * g n z else 0 with hg'def
  have hpair : pair F g = 16 * pair F g' := by
    simp only [pair, Finset.mul_sum]
    refine sum_congr rfl fun n _ => sum_congr rfl fun z _ => ?_
    by_cases hn : n ≤ 4
    · simp only [hg'def, if_pos hn]; push_cast; ring
    · rw [hF n z (by omega)]; simp
  have hphi : phiNorm E p h ℓ g' ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    refine phiNorm_le fun n z α hα => ?_
    have h2 : phiTerm h (2 * ℓ) g z α ≤ 1 :=
      phiTerm_le_of_phiNorm_le hh (by positivity) zero_le_one
        (by rwa [ENNReal.ofReal_one]) z α hα
    by_cases hn : n ≤ 4
    · have e : g' n = (1 / 16 : ℝ) • g n := by
        funext w; simp only [hg'def, if_pos hn, Pi.smul_apply, Complex.real_smul]
      have h3 : phiTerm h ℓ g' z α = 2 ^ n / 16 * phiTerm h (2 * ℓ) g z α := by
        simp only [phiTerm, e, map_smul, Pi.smul_apply, norm_smul, Real.norm_eq_abs]
        rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 16), mul_inv, mul_pow, inv_pow, inv_pow]
        field_simp
      have h4 : (2 : ℝ) ^ n / 16 ≤ 1 := by
        rw [div_le_one (by norm_num)]
        calc (2 : ℝ) ^ n ≤ 2 ^ 4 := pow_le_pow_right₀ (by norm_num) hn
          _ = 16 := by norm_num
      rw [h3]
      have := phiTerm_nonneg hh (by positivity : 0 < 2 * ℓ) g z α
      nlinarith
    · have e : g' n = 0 := by funext w; simp only [hg'def, if_neg hn, Pi.zero_apply]
      simp [phiTerm, e]
  rw [hpair, norm_mul, ENNReal.ofReal_mul (by norm_num)]
  simp only [Complex.norm_ofNat, ENNReal.ofReal_ofNat]
  exact mul_le_mul_left' (le_iSup₂ (f := fun g _ => ENNReal.ofReal ‖pair F g‖) g' hphi) _

end Deg

theorem coeff_Loc2XY_of_lt (X Y : Finset (Lam d L N)) (F : Alg d L N) {n : ℕ}
    (z : Fin n → Sf (Lam d L N)) (hn : 4 < n) : coeff (Loc2sXY X Y F) z = 0 := by
  rw [Loc2sXY, coeff_add, coeff_LocXY_eq_zero X Y F z (by omega)
    (fun u v => coeff_psi_psibar_of_ne u v z (by omega)), coeff_Loc4sXY_of_ne X Y F z (by omega),
    add_zero]

/-! ### Antisymmetry and the quartic pairing -/

/-- The transposition `σ` of two positions of equal spin in the pattern `(+,-,+,-)`. -/
theorem cf4_swap (F : Alg d L N) (x : Fin 4 → Lam d L N) (a b : Fin 4) (hab : a ≠ b)
    (hp : pat4 a = pat4 b) :
    cf4 F (x ∘ Equiv.swap a b) = -cf4 F x := by
  have e : (fun r => ((x ∘ Equiv.swap a b) r, pat4 r)) =
      (fun r => (x r, pat4 r)) ∘ Equiv.swap a b := by
    funext r
    simp only [Function.comp_apply, Prod.mk.injEq, true_and]
    rcases eq_or_ne r a with rfl | hra
    · rw [Equiv.swap_apply_left, hp]
    rcases eq_or_ne r b with rfl | hrb
    · rw [Equiv.swap_apply_right, hp]
    · rw [Equiv.swap_apply_of_ne_of_ne hra hrb]
  rw [cf4, e, coeff_perm, Equiv.Perm.sign_swap hab]
  simp [cf4]

/-- If `f` does not depend on the positions `a, b` of equal spin, `∑_x F_x f(x) = 0`. -/
theorem sum_cf4_eq_zero (F : Alg d L N) (a b : Fin 4) (hab : a ≠ b) (hp : pat4 a = pat4 b)
    (f : (Fin 4 → Lam d L N) → ℂ) (hf : ∀ x, f (x ∘ Equiv.swap a b) = f x) :
    ∑ x, cf4 F x * f x = 0 := by
  set S := ∑ x, cf4 F x * f x with hS
  have e1 : ∑ x, cf4 F (x ∘ Equiv.swap a b) * f (x ∘ Equiv.swap a b) = S :=
    Fintype.sum_equiv (Equiv.arrowCongr (Equiv.swap a b) (Equiv.refl _)) _ _
      fun x => by
        have : (Equiv.arrowCongr (Equiv.swap a b) (Equiv.refl _)) x = x ∘ Equiv.swap a b := by
          funext r; simp [Equiv.arrowCongr_apply, Equiv.symm_swap]
        rw [this]
  have e2 : ∑ x, cf4 F (x ∘ Equiv.swap a b) * f (x ∘ Equiv.swap a b) = -S := by
    simp only [cf4_swap F _ a b hab hp, hf, neg_mul, sum_neg_distrib, hS]
  have e : S = -S := e1.symm.trans e2
  have : (2 : ℂ) * S = 0 := by linear_combination e
  exact (mul_eq_zero.1 this).resolve_left two_ne_zero

theorem lift_shift {b b' x : Lam d L N}
    (h : 2 * (supNorm (x - b) + supNorm (b - b')) < L ^ N) :
    lift b' x = lift b x + lift b' b := by
  have := (AffAut.transl (0 : Lam d L N)).lift_E (b := b) (b' := b') (x := x)
    (by simpa [AffAut.transl] using h)
  simpa [AffAut.transl] using this

theorem cf4_eq_zero_of_mem_NX {R : Set (Lam d L N)} {F : Alg d L N} (hF : F ∈ NX R)
    (x : Fin 4 → Lam d L N) (r : Fin 4) (hr : x r ∉ R) : cf4 F x = 0 :=
  coeff_eq_zero_of_mem_NX hF _ r hr

/-- **The quartic pairing does not depend on the base point.** -/
theorem mu4_base_indep {R : Set (Lam d L N)} {F : Alg d L N} (hF : F ∈ NX R) {b b' : Lam d L N}
    (hR : ∀ x ∈ R, 2 * (supNorm (x - b) + supNorm (b - b')) < L ^ N) (i k : Fin d) :
    mu4 b' i k F = mu4 b i k F := by
  set δ := lift b' b
  have hterm : ∀ x : Fin 4 → Lam d L N,
      cf4 F x * ((lift b' (x 0) i * lift b' (x 1) k : ℝ) : ℂ) =
        cf4 F x * ((lift b (x 0) i * lift b (x 1) k : ℝ) : ℂ) +
        cf4 F x * ((δ i * lift b (x 1) k : ℝ) : ℂ) +
        cf4 F x * ((lift b (x 0) i * δ k : ℝ) : ℂ) + cf4 F x * ((δ i * δ k : ℝ) : ℂ) := by
    intro x
    by_cases hx : ∀ r, x r ∈ R
    · rw [lift_shift (hR _ (hx 0)), lift_shift (hR _ (hx 1))]
      simp only [Pi.add_apply]; push_cast; ring
    · push_neg at hx
      obtain ⟨r, hr⟩ := hx
      simp [cf4_eq_zero_of_mem_NX hF x r hr]
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  have h13 : (1 : Fin 4) ≠ 3 := by decide
  have p02 : pat4 0 = pat4 2 := by decide
  have p13 : pat4 1 = pat4 3 := by decide
  have s1 := sum_cf4_eq_zero F 0 2 h02 p02 (fun x => ((δ i * lift b (x 1) k : ℝ) : ℂ))
    fun x => by simp [Equiv.swap_apply_of_ne_of_ne (show (1 : Fin 4) ≠ 0 by decide)
      (show (1 : Fin 4) ≠ 2 by decide)]
  have s2 := sum_cf4_eq_zero F 1 3 h13 p13 (fun x => ((lift b (x 0) i * δ k : ℝ) : ℂ))
    fun x => by simp [Equiv.swap_apply_of_ne_of_ne (show (0 : Fin 4) ≠ 1 by decide)
      (show (0 : Fin 4) ≠ 3 by decide)]
  have s3 := sum_cf4_eq_zero F 0 2 h02 p02 (fun _ => ((δ i * δ k : ℝ) : ℂ)) fun _ => rfl
  simp only [mu4, hterm, sum_add_distrib, s1, s2, s3, add_zero]

/-- **The quartic pairing is translation invariant.** -/
theorem mu4_transl (t b : Lam d L N) (i k : Fin d) (F : Alg d L N) :
    mu4 (b + t) i k (autAlg (Equiv.addRight t) F) = mu4 b i k F := by
  have hl : ∀ y : Lam d L N, lift (b + t) (y + t) = lift b y := by
    intro y; unfold lift; rw [add_sub_add_right_eq_sub]
  have hc : ∀ y : Fin 4 → Lam d L N,
      cf4 (autAlg (Equiv.addRight t) F) (fun r => y r + t) = cf4 F y := by
    intro y
    simp only [cf4, coeff_autAlg, Equiv.addRight_symm, Equiv.coe_addRight, add_neg_cancel_right]
  simp only [mu4]
  refine (Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl _) (Equiv.addRight t)) _ _
    fun y => ?_).symm
  rw [show (Equiv.arrowCongr (Equiv.refl _) (Equiv.addRight t)) y = fun r => y r + t from rfl,
    hc, hl, hl]

/-! ### Translations of the localisation -/

theorem autAlg_ψ (E : Lam d L N ≃ Lam d L N) (a : Sf (Lam d L N)) :
    autAlg E (ψ a) = ψ (E a.1, a.2) := by
  rw [autAlg, ψ, ExteriorAlgebra.map_apply_ι, autV_ev, ← ψ]

theorem autAlg_mono4 (t : Lam d L N) (i k : Fin d) (x : Lam d L N) :
    autAlg (Equiv.addRight t) (mono4s i k x) = mono4s i k (x + t) := by
  have hg : ∀ e e' : Dir d, autAlg (Equiv.addRight t) (gmono4 e e' x) = gmono4 e e' (x + t) := by
    intro e e'
    rw [gmono4_eq, gmono4_eq]
    simp only [map_mul, map_sub, autAlg_ψ, Equiv.coe_addRight, add_right_comm]
  unfold mono4s
  split_ifs <;> simp only [map_smul, map_add, map_sub, hg]

theorem autAlg_mono4Set (t : Lam d L N) (i k : Fin d) (Y : Finset (Lam d L N)) :
    autAlg (Equiv.addRight t) (mono4sSet i k Y) =
      mono4sSet i k ((AffAut.transl t).img Y) := by
  rw [mono4sSet, map_sum, mono4sSet, AffAut.img, sum_map]
  refine sum_congr rfl fun x _ => ?_
  rw [autAlg_mono4]; rfl

/-- The region condition for the base point of a translate. -/
theorem _root_.Loc.Region.base_cond {X : Finset (Lam d L N)} {R : Set (Lam d L N)} (hR : Region X R)
    (hne : X.Nonempty) (t : Lam d L N) :
    ∀ x ∈ (Equiv.addRight t) '' R,
      2 * (supNorm (x - (base X + t)) + supNorm (base X + t - base ((AffAut.transl t).img X)))
        < L ^ N := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hy'⟩ := Finset.mem_map.1 (base_mem ((AffAut.transl t).img_nonempty hne))
  have hy'' : y + t = base ((AffAut.transl t).img X) := hy'
  rw [← hy'']
  simp only [Equiv.coe_addRight, add_sub_add_right_eq_sub]
  have h1 := hR.diam x hx _ (hR.mem (base_mem hne))
  have h2 := hR.diam _ (hR.mem (base_mem hne)) y (hR.mem hy)
  omega

theorem autAlg_mem_NX_image (E : Lam d L N ≃ Lam d L N) {R : Set (Lam d L N)} {F : Alg d L N}
    (hF : F ∈ NX R) : autAlg E F ∈ NX (E '' R) := by
  refine algHom_mem_of_mem_NX _ (fun a ha => ?_) hF
  rw [autAlg_ψ]
  exact ψ_mem_NX ⟨a.1, ha, rfl⟩

/-- `τ_t Loc⁽⁴⁾_X F = Loc⁽⁴⁾_{X+t} τ_t F`. -/
theorem Loc4XY_transl {X : Finset (Lam d L N)} {R : Set (Lam d L N)} (hR : Region X R)
    (hne : X.Nonempty) (t : Lam d L N) (Y : Finset (Lam d L N)) {F : Alg d L N}
    (hF : F ∈ NX R) :
    autAlg (Equiv.addRight t) (Loc4sXY X Y F) =
      Loc4sXY ((AffAut.transl t).img X) ((AffAut.transl t).img Y)
        (autAlg (Equiv.addRight t) F) := by
  have hmu : ∀ i k, mu4 (base ((AffAut.transl t).img X)) i k (autAlg (Equiv.addRight t) F) =
      mu4 (base X) i k F := by
    intro i k
    rw [mu4_base_indep (autAlg_mem_NX_image _ hF) (hR.base_cond hne t), mu4_transl]
  simp only [Loc4sXY, map_sum, map_smul, autAlg_mono4Set, hmu, AffAut.card_img]

/-- **`τ_t Loc_X F = Loc_{X+t} τ_t F`** (Lemma `lem:loc-tr`(i)). -/
theorem Loc2XY_transl {X : Finset (Lam d L N)} {R : Set (Lam d L N)} (hR : Region X R)
    (hne : X.Nonempty) (t : Lam d L N) (Y : Finset (Lam d L N)) {F : Alg d L N}
    (hF : F ∈ NX R) :
    autAlg (Equiv.addRight t) (Loc2sXY X Y F) =
      Loc2sXY ((AffAut.transl t).img X) ((AffAut.transl t).img Y)
        (autAlg (Equiv.addRight t) F) := by
  rw [Loc2sXY, map_add, Loc4XY_transl hR hne t Y hF, Loc2sXY]
  congr 1
  exact (AffAut.transl t).LocXY_aut hR hne F hF

/-! ### `Loc_X` on uniform local polynomials -/

/-- A uniform local polynomial on `Y`: `κ + ∑_M c_M M(Y) + ∑_{i,k} e_{ik} M⁽⁴⁾_{ik}(Y)`. -/
def unif (κ : ℂ) (c : Mono d → ℂ) (e : Fin d → Fin d → ℂ) (Y : Finset (Lam d L N)) :
    Alg d L N :=
  κ • 1 + ∑ M, c M • monoSet M Y + ∑ i, ∑ k, e i k • mono4sSet i k Y

theorem coeff_mono4Set_of_ne (i k : Fin d) (Y : Finset (Lam d L N)) {n : ℕ}
    (z : Fin n → Sf (Lam d L N)) (hn : n ≠ 4) : coeff (mono4sSet i k Y) z = 0 := by
  rw [mono4sSet, coeff_sum]; exact sum_eq_zero fun x _ => coeff_mono4s_of_ne i k x z hn

theorem coeff_monoSet_of_ne (M : Mono d) (Y : Finset (Lam d L N)) {n : ℕ}
    (z : Fin n → Sf (Lam d L N)) (hn : n ≠ 2) : coeff (monoSet M Y) z = 0 := by
  rw [monoSet, coeff_sum]
  exact sum_eq_zero fun x _ => coeff_monoAt_eq_zero M x z fun u v =>
    coeff_psi_psibar_of_ne u v z hn

theorem mu_mono4Set (b : Lam d L N) (β : Mono d) (i k : Fin d) (Y : Finset (Lam d L N)) :
    mu b β (mono4sSet i k Y) = 0 := by
  refine sum_eq_zero fun x _ => sum_eq_zero fun y _ => ?_
  rw [cf2, coeff_mono4Set_of_ne i k Y _ (by decide), zero_mul]

theorem mu4_monoSet (b : Lam d L N) (i k : Fin d) (M : Mono d) (Y : Finset (Lam d L N)) :
    mu4 b i k (monoSet M Y) = 0 := by
  refine sum_eq_zero fun x _ => ?_
  rw [cf4, coeff_monoSet_of_ne M Y _ (by decide), zero_mul]

theorem mu4_one (b : Lam d L N) (i k : Fin d) : mu4 b i k (1 : Alg d L N) = 0 := by
  refine sum_eq_zero fun x _ => ?_
  rw [cf4, coeff_one_of_ne _ (by decide), zero_mul]

theorem eps_mono4Set (i k : Fin d) (Y : Finset (Lam d L N)) : ε (mono4sSet i k Y) = 0 := by
  rw [← coeff_elim0 _ (Fin.elim0 : Fin 0 → Sf (Lam d L N))]
  exact coeff_mono4Set_of_ne i k Y _ (by decide)

theorem eps_monoSet (M : Mono d) (Y : Finset (Lam d L N)) : ε (monoSet M Y) = 0 := by
  rw [monoSet, map_sum]; exact sum_eq_zero fun x _ => eps_monoAt M x

theorem mu4_mono4Set {X : Finset (Lam d L N)} (hX : Patch X) (i k κ κ' : Fin d) :
    mu4 (base X) κ κ' (mono4sSet i k X) =
      (if κ = i then 1 else 0) * (if κ' = k then 1 else 0) * X.card := by
  rw [mono4sSet, mu4_sum, sum_congr rfl fun x hx => mu4_mono4s_patch hX hx i k κ κ', sum_const,
    nsmul_eq_mul]
  ring

/-- **`Loc_X` is the identity on uniform local polynomials** (Lemma `lem:loc-tr`(iii)). -/
theorem Loc2X_unif {X : Finset (Lam d L N)} (hX : Patch X) (hne : X.Nonempty) (κ : ℂ)
    (c : Mono d → ℂ) (e : Fin d → Fin d → ℂ) : Loc2sX X (unif κ c e X) = unif κ c e X := by
  have hX0 : (X.card : ℂ) ≠ 0 := by exact_mod_cast hne.card_pos.ne'
  set G := unif κ c e X with hG
  have hε : ε G = κ := by
    simp only [hG, unif, map_add, map_smul, map_one, map_sum, eps_monoSet, eps_mono4Set,
      smul_eq_mul, mul_zero, sum_const_zero, add_zero, mul_one]
  have hmu : ∀ β, mu (base X) β G = (c ᵥ* Amat X) β := by
    intro β
    simp only [hG, unif, mu_add, mu_smul, mu_one, mu_sum, mu_mono4Set, mul_zero, sum_const_zero,
      add_zero, zero_add]
    rfl
  have hc : locCoef X G = c := by
    rw [locCoef]
    have : (fun β => mu (base X) β G) = c ᵥ* Amat X := funext hmu
    rw [this, vecMul_vecMul,
      mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (Amat_isUnit hX hne)), vecMul_one]
  have hmu4 : ∀ i k, mu4 (base X) i k G = e i k * X.card := by
    intro i k
    simp only [hG, unif, mu4_add, mu4_smul, mu4_one, mu4_sum, mu4_monoSet, mu4_mono4Set hX,
      mul_zero, sum_const_zero, zero_add]
    simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, sum_ite_eq,
      mem_univ, if_true]
    ring
  rw [Loc2sX, Loc2sXY, LocXY, hε, hc, Loc4sXY]
  simp only [hmu4, mul_div_assoc, div_self hX0, mul_one]
  simp only [hG, unif]

/-- `Loc_X F` is uniform, with coefficients `(ε F, locCoef X F, μ⁽⁴⁾(F)/|X|)`. -/
theorem Loc2X_eq_unif {X : Finset (Lam d L N)} (hne : X.Nonempty) (F : Alg d L N) :
    Loc2sX X F = unif (ε F) (locCoef X F) (fun i k => mu4 (base X) i k F / X.card) X := by
  have hX0 : (X.card : ℂ) ≠ 0 := by exact_mod_cast hne.card_pos.ne'
  rw [Loc2sX, Loc2sXY, LocXY, Loc4sXY, unif, mul_div_assoc, div_self hX0, mul_one]

theorem unif_sum {ι : Type*} (s : Finset ι) (κ : ℂ) (c : Mono d → ℂ) (e : Fin d → Fin d → ℂ)
    (Y : ι → Finset (Lam d L N)) (hY : (s : Set ι).PairwiseDisjoint Y) :
    ∑ a ∈ s, unif κ c e (Y a) = unif (s.card * κ) c e (s.biUnion Y) := by
  have h1 : ∀ M, monoSet M (s.biUnion Y) = ∑ a ∈ s, monoSet M (Y a) := fun M => by
    rw [monoSet, sum_biUnion hY]; rfl
  have h2 : ∀ i k, mono4sSet i k (s.biUnion Y) = ∑ a ∈ s, mono4sSet i k (Y a) := fun i k => by
    rw [mono4sSet, sum_biUnion hY]; rfl
  simp only [unif, h1, h2, smul_sum, sum_add_distrib, sum_const, nsmul_eq_mul]
  rw [mul_smul, Finset.sum_comm (s := s) (t := univ)]
  congr 1
  · simp only [Algebra.smul_def]
    rw [Finset.sum_comm (s := s) (t := univ)]
    refine sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]

end

end Step2
