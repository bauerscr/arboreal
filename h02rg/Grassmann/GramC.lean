import Grassmann.Gram
import Grassmann.IBPC
import Grassmann.HadamardC

/-!
# The Gram inequality for covariances with a Gram representation

A complex covariance `C` has a *Gram representation* `C_{xy} = ⟪F_x, G_y⟫` in a complex inner
product space (`IsGram`). It need not be positive semidefinite, symmetric or real.

* `abs_omegaC_pure_le`: `‖⟨∏_j (∑_x f_j(x) ψ_{x, σ_j})⟩_C‖ ≤ ∏_j ‖∑_x f_j(x) H^{σ_j}_x‖`, with
  `H^- = F` and `H^+ = G` (Gram–Hadamard, `norm_det_inner_le`).
* `GramBound E p h ℓ F G`: the derivative profiles `∇^a δ_x`, `|a| ≤ p`, have
  `‖∑_y (∇^a δ_x)(y) F_y‖, ‖∑_y (∇^a δ_x)(y) G_y‖ ≤ ℓ h^{-|a|}`. This replaces
  `C.PosSemidef` together with `covNorm E p h ℓ C ≤ 1`.
* `tNorm_ECC_le`, `tNorm_ECC_theta_le`: `e:E-contract2` and `e:E-contract` under `GramBound`.
* `gram_of_psd`: a positive semidefinite real `C` with `covNorm ≤ 1` has such a representation,
  so `tNorm_EC_le` is a special case.
-/

namespace Grassmann

noncomputable section

open CliffordAlgebra ExteriorAlgebra Finset Matrix

section GramRep

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ] {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]

/-- `C_{xy} = ⟪F_x, G_y⟫`. -/
def IsGram (C : Matrix Λ Λ ℂ) (Fv Gv : Λ → H) : Prop := ∀ x y, C x y = inner ℂ (Fv x) (Gv y)

/-- `∑_x f(x) F_x`. -/
def gvec (Fv : Λ → H) (f : Λ → ℝ) : H := ∑ x, (f x : ℂ) • Fv x

theorem bil_eq_inner {C : Matrix Λ Λ ℂ} {Fv Gv : Λ → H} (hC : IsGram C Fv Gv) (b a : Λ → ℝ) :
    bil C b a = inner ℂ (gvec Fv b) (gvec Gv a) := by
  simp only [bil, gvec, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, mul_sum]
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => by rw [hC]; ring

/-- The Gram norm of the profile `f` for a field of type `σ`. -/
def gnorm (Fv Gv : Λ → H) (σ : ℤˣ) (f : Λ → ℝ) : ℝ := if σ = 1 then ‖gvec Gv f‖ else ‖gvec Fv f‖

theorem gnorm_nonneg (Fv Gv : Λ → H) (σ : ℤˣ) (f : Λ → ℝ) : 0 ≤ gnorm Fv Gv σ f := by
  unfold gnorm; split_ifs <;> exact norm_nonneg _

/-- Gram's inequality for a covariance with a Gram representation. -/
theorem abs_omegaC_pure_le {C : Matrix Λ Λ ℂ} {Fv Gv : Λ → H} (hC : IsGram C Fv Gv) {m : ℕ}
    (σ : Fin m → ℤˣ) (f : Fin m → Λ → ℝ) :
    ‖omegaC C (ιMulti ℂ m fun j => pureV (σ j) (f j))‖ ≤ ∏ j, gnorm Fv Gv (σ j) (f j) := by
  obtain ⟨a, b, e, s, hs, hP, hnP, heq⟩ :=
    ιMulti_split (fun j => pureV (σ j) (f j)) (fun j => σ j = -1)
  have hbar : (fun j => pureV (σ j) (f j)) ∘ e ∘ Sum.inl = fun j => vbar (f (e (Sum.inl j))) := by
    funext j
    simp only [Function.comp_apply, pureV, hP j]
    rw [if_neg (by decide)]
  have hpsi : (fun j => pureV (σ j) (f j)) ∘ e ∘ Sum.inr = fun j => vpsi (f (e (Sum.inr j))) := by
    funext j
    have : σ (e (Sum.inr j)) = 1 := (Int.units_eq_one_or _).resolve_right (hnP j)
    simp only [Function.comp_apply, pureV, this, if_true]
  rw [heq, omegaC_smul, hbar, hpsi, norm_mul, hs, one_mul]
  have hprod : ∏ j, gnorm Fv Gv (σ j) (f j) =
      (∏ j : Fin a, ‖gvec Fv (f (e (Sum.inl j)))‖) * ∏ j : Fin b, ‖gvec Gv (f (e (Sum.inr j)))‖ := by
    rw [← Fintype.prod_equiv e (fun j => gnorm Fv Gv (σ (e j)) (f (e j))) _ (fun _ => rfl),
      Fintype.prod_sum_type]
    congr 1
    · refine prod_congr rfl fun j _ => ?_
      simp only [gnorm, hP j]; rw [if_neg (by decide)]
    · refine prod_congr rfl fun j _ => ?_
      have : σ (e (Sum.inr j)) = 1 := (Int.units_eq_one_or _).resolve_right (hnP j)
      simp only [gnorm, this, if_true]
  by_cases hab : a = b
  · subst hab
    rw [omegaC_moment, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, hprod,
      ← prod_mul_distrib]
    have : (Matrix.of fun i j => bil C (f (e (Sum.inl i))) (f (e (Sum.inr j)))) =
        Matrix.of fun i j => inner ℂ (gvec Fv (f (e (Sum.inl i)))) (gvec Gv (f (e (Sum.inr j)))) := by
      ext i j; simp [bil_eq_inner hC]
    rw [this]
    exact norm_det_inner_le _ _
  · rw [omegaC_moment_of_ne _ _ _ hab, norm_zero]
    exact prod_nonneg fun j _ => gnorm_nonneg _ _ _ _

end GramRep

section Contract

variable {E : Type*} [Fintype E] [DecidableEq E]
variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ] [AddAction (E → ℕ) Λ]
variable {p : ℕ} {h ℓ : ℝ}

variable (E) in
/-- The Gram bound on the derivative profiles: it replaces `C.PosSemidef` and
`covNorm E p h ℓ C ≤ 1`. -/
def GramBound {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (p : ℕ) (h ℓ : ℝ)
    (Fv Gv : Λ → H) : Prop :=
  ∀ a : E → ℕ, mabs a ≤ p → ∀ x : Λ,
    ‖gvec Fv (dprof a x)‖ ≤ ℓ * (h ^ mabs a)⁻¹ ∧ ‖gvec Gv (dprof a x)‖ ≤ ℓ * (h ^ mabs a)⁻¹

theorem gnorm_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {Fv Gv : Λ → H}
    (hB : GramBound E p h ℓ Fv Gv) {a : E → ℕ} (ha : mabs a ≤ p) (σ : ℤˣ) (x : Λ) :
    gnorm Fv Gv σ (dprof a x) ≤ ℓ * (h ^ mabs a)⁻¹ := by
  unfold gnorm; split_ifs
  · exact (hB a ha x).2
  · exact (hB a ha x).1

/-- `e:E-contract2` for a covariance with a Gram representation:
`‖𝔼_C F‖_{T(ℓ)} ≤ ‖F‖_{T(ℓ ⊔ ℓ)}`. -/
theorem tNorm_ECC_le (hh : 0 < h) (hℓ : 0 < ℓ) {C : Matrix Λ Λ ℂ} {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] {Fv Gv : Λ → H} (hC : IsGram C Fv Gv)
    (hB : GramBound E p h ℓ Fv Gv) (F : N (Λ ⊕ Λ)) :
    tNorm E p h ℓ (ECC C F) ≤ tNorm E p h ℓ F := by
  rw [← ENNReal.ofReal_toReal (tNorm_ne_top hh hℓ F)]
  refine tNorm_le fun g hg => ?_
  -- the test function `g̃_w = ⟨𝔼_C ψ^w, g⟩` on the doubled sequences
  set gT : TestFn (Λ ⊕ Λ) := fun n w => pair (ECC C (psiPow w)) g
  have hpair : pair (ECC C F) g = pair F gT := by
    conv_lhs => rw [sum_coeff F]
    simp only [map_sum, map_smul, pair_sum, pair_smul]
    conv_rhs => rw [pair]
    simp only [gT, mul_sum]
    refine sum_congr rfl fun n _ => sum_congr rfl fun w _ => by ring
  have hg1 : phiNorm E p h ℓ g ≤ ENNReal.ofReal 1 := by rwa [ENNReal.ofReal_one]
  have hAg : phiNorm E p h ℓ (asym g) ≤ ENNReal.ofReal 1 := (phiNorm_asym_le hh.le hℓ g).trans hg1
  have hgT : phiNorm E p h ℓ gT ≤ ENNReal.ofReal 1 := by
    refine phiNorm_le fun n w α hα => ?_
    have h1 : nab α (gT n) w = pair (ECC C (ιMulti ℂ n fun i => dvec (α i) (w i))) g :=
      nab_psiPow ((pairL g) ∘ₗ ECC C) α w
    obtain ⟨a, b, e, s, hs, hP, hnP, heq⟩ :=
      ιMulti_split (fun i => dvec (α i) (w i)) (fun i => (w i).1.isLeft)
    set αψ : Fin a → E → ℕ := α ∘ e ∘ Sum.inl
    set αζ : Fin b → E → ℕ := α ∘ e ∘ Sum.inr
    set zψ : Fin a → Sf Λ := fun j => prf (w (e (Sum.inl j)))
    set zζ : Fin b → Sf Λ := fun j => prf (w (e (Sum.inr j)))
    have hψ : (fun i => dvec (α i) (w i)) ∘ e ∘ Sum.inl = inlV ∘ fun j => dvec (αψ j) (zψ j) := by
      funext j
      have := hP j
      simp only [Function.comp_apply, zψ, αψ]
      rcases hw : w (e (Sum.inl j)) with ⟨x | x, σ⟩
      · exact dvec_inl _ (x, σ)
      · rw [hw] at this; simp at this
    have hζ : (fun i => dvec (α i) (w i)) ∘ e ∘ Sum.inr = inrV ∘ fun j => dvec (αζ j) (zζ j) := by
      funext j
      have := hnP j
      simp only [Function.comp_apply, zζ, αζ]
      rcases hw : w (e (Sum.inr j)) with ⟨x | x, σ⟩
      · rw [hw] at this; simp at this
      · exact dvec_inr _ (x, σ)
    rw [hψ, hζ, ← ExteriorAlgebra.map_apply_ιMulti, ← ExteriorAlgebra.map_apply_ιMulti] at heq
    unfold phiTerm
    rw [h1, heq, map_smul, ← incl, ← inclζ, ECC_incl_mul_inclζ, pair_smul, pair_smul]
    -- the `ψ` part
    have hA : pair (ιMulti ℂ a fun j => dvec (αψ j) (zψ j)) g = nab αψ (asym g a) zψ := by
      rw [show pair (ιMulti ℂ a fun j => dvec (αψ j) (zψ j)) g =
        pairL g (ιMulti ℂ a fun j => dvec (αψ j) (zψ j)) from rfl, ← nab_psiPow (pairL g) αψ zψ]
      have hfun : (fun w : Fin a → Sf Λ => pairL g (psiPow w)) = asym g a :=
        funext fun z => pair_psiPow z g
      rw [hfun]
    have hAb := abs_nab_le hh hℓ zero_le_one hAg zψ αψ (fun j => hα _)
    -- the `ζ` part (Gram)
    have hB : ‖omegaC C (ιMulti ℂ b fun j => dvec (αζ j) (zζ j))‖ ≤ ℓ ^ b * (h ^ ord αζ)⁻¹ := by
      simp_rw [dvec_eq_pureV]
      refine (abs_omegaC_pure_le hC _ _).trans ?_
      calc ∏ j, gnorm Fv Gv (zζ j).2 (dprof (αζ j) (zζ j).1)
          ≤ ∏ j : Fin b, ℓ * (h ^ mabs (αζ j))⁻¹ :=
            prod_le_prod (fun _ _ => gnorm_nonneg _ _ _ _)
              fun j _ => gnorm_le hB (hα _) _ _
        _ = ℓ ^ b * (h ^ ord αζ)⁻¹ := by
            rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, prod_inv_distrib,
              prod_pow_eq_pow_sum, ord]
    have hn : a + b = n := by simpa using Fintype.card_congr e
    have hord := ord_equiv e α
    rw [norm_mul, norm_mul, hs, one_mul, hA]
    calc ℓ⁻¹ ^ n * h ^ ord α * (‖omegaC C (ιMulti ℂ b fun j => dvec (αζ j) (zζ j))‖ *
          ‖nab αψ (asym g a) zψ‖)
        ≤ ℓ⁻¹ ^ n * h ^ ord α * ((ℓ ^ b * (h ^ ord αζ)⁻¹) * (1 * ℓ ^ a * (h ^ ord αψ)⁻¹)) := by
          gcongr
      _ = 1 := by
          rw [hord, pow_add, show ℓ⁻¹ ^ n = ℓ⁻¹ ^ (a + b) by rw [hn], pow_add, inv_pow, inv_pow]
          field_simp
          exact mul_comm _ _
  rw [hpair]
  have := abs_pair_le hh hℓ F zero_le_one hgT
  rwa [mul_one] at this

/-- `e:E-contract` for a covariance with a Gram representation:
`‖𝔼_C θ F‖_{T(ℓ)} ≤ ‖F‖_{T(2ℓ)}`. -/
theorem tNorm_ECC_theta_le (hh : 0 < h) (hℓ : 0 < ℓ) {C : Matrix Λ Λ ℂ} {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] {Fv Gv : Λ → H} (hC : IsGram C Fv Gv)
    (hB : GramBound E p h ℓ Fv Gv) (F : N Λ) :
    tNorm E p h ℓ (ECC C (theta F)) ≤ tNorm E p h (2 * ℓ) F :=
  (tNorm_ECC_le hh hℓ hC hB _).trans (tNorm_theta_le hh hℓ F)

/-! ### Positive semidefinite covariances have a Gram representation -/

open scoped MatrixOrder in
/-- A positive semidefinite real covariance with `‖C‖_Φ ≤ 1` satisfies `GramBound`, with
`F = G`. So `tNorm_EC_le` is the special case of `tNorm_ECC_le`. -/
theorem gram_of_psd (hh : 0 < h) (hℓ : 0 < ℓ) {C : Matrix Λ Λ ℝ} (hC : C.PosSemidef)
    (hCn : covNorm E p h ℓ C ≤ 1) :
    ∃ Fv : Λ → EuclideanSpace ℂ Λ, IsGram (cplx C) Fv Fv ∧ GramBound E p h ℓ Fv Fv := by
  obtain ⟨D, hD⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hC.nonneg
  set Fv : Λ → EuclideanSpace ℂ Λ := fun x => WithLp.toLp 2 (fun i => (D i x : ℂ))
  have hG : IsGram (cplx C) Fv Fv := by
    intro x y
    simp only [Fv, cplx, Matrix.map_apply, hD, PiLp.inner_apply, RCLike.inner_apply,
      Complex.conj_ofReal, mul_apply, star_eq_conjTranspose, conjTranspose_apply, star_trivial]
    push_cast
    exact sum_congr rfl fun i _ => by ring
  have hnorm : ∀ f : Λ → ℝ, ‖gvec Fv f‖ = Real.sqrt (f ⬝ᵥ (C *ᵥ f)) := by
    intro f
    have h1 : (‖gvec Fv f‖ ^ 2 : ℝ) = f ⬝ᵥ (C *ᵥ f) := by
      rw [@norm_sq_eq_re_inner ℂ, ← bil_eq_inner hG, bil_cplx]; simp
    rw [← h1, Real.sqrt_sq (norm_nonneg _)]
  refine ⟨Fv, hG, fun a ha x => ?_⟩
  have := sqrt_dprof_quad_le hh hℓ hCn ha x
  rw [hnorm]
  exact ⟨this, this⟩

/-- `tNorm_EC_le` recovered from `tNorm_ECC_le`. -/
theorem tNorm_EC_le_of_gram (hh : 0 < h) (hℓ : 0 < ℓ) {C : Matrix Λ Λ ℝ} (hC : C.PosSemidef)
    (hCn : covNorm E p h ℓ C ≤ 1) (F : N (Λ ⊕ Λ)) :
    tNorm E p h ℓ (EC C F) ≤ tNorm E p h ℓ F := by
  obtain ⟨Fv, hG, hB⟩ := gram_of_psd hh hℓ hC hCn
  rw [EC_eq_ECC]
  exact tNorm_ECC_le hh hℓ hG hB F

end Contract

end

end Grassmann
