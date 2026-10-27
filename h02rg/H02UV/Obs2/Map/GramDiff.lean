import Grassmann.GramC

/-!
# The quadratic gain of `e^{ℒ_R} − 1` for a small covariance

* **`tNorm_ECC_sub_le`**: if `R` has a Gram representation with `GramBound` constant `γ ≤ ℓ`,
  then `‖(𝔼_R − 𝔼_0) F‖_{T(ℓ)} ≤ (γ/ℓ)² ‖F‖_{T(ℓ ⊔ ℓ)}` (the terms with no or one `ζ` cancel or
  vanish, every further `ζ` gains `γ/ℓ`);
* `tNorm_expLC_sub_le`: `‖e^{ℒ_R}F − F‖_{T(ℓ)} ≤ (γ/ℓ)² ‖F‖_{T(2ℓ)}`.
-/

set_option linter.unusedSectionVars false

namespace Grassmann

noncomputable section

open CliffordAlgebra ExteriorAlgebra Finset Matrix

variable {E : Type*} [Fintype E] [DecidableEq E]
variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ] [AddAction (E → ℕ) Λ]
variable {p : ℕ} {h ℓ : ℝ}

theorem omegaC_zero_ιMulti_succ {n : ℕ} (v : Fin (n + 1) → V Λ) :
    omegaC (0 : Matrix Λ Λ ℂ) (ιMulti ℂ (n + 1) v) = 0 := by
  have h0 : LopC (0 : Matrix Λ Λ ℂ) (ιMulti ℂ (n + 1) v) = 0 := by
    rw [LopC_apply]; simp
  rw [omegaC, expLC_eq_self _ h0]
  exact algebraMapInv_ιMulti_succ v

theorem omegaC_ιMulti_one (C : Matrix Λ Λ ℂ) (v : Fin 1 → V Λ) :
    omegaC C (ιMulti ℂ 1 v) = 0 := by
  have e1 : ιMulti ℂ 1 v = ι ℂ (v 0) := by simp [ιMulti_apply]
  have hD : ∀ a b : Sf Λ, D b (D a (ιMulti ℂ 1 v)) = 0 := by
    intro a b
    rw [e1]
    simp only [D]
    rw [contractLeft_ι]
    exact D_algebraMap b _
  have h0 : LopC C (ιMulti ℂ 1 v) = 0 := by
    rw [LopC_apply]
    exact sum_eq_zero fun x _ => sum_eq_zero fun y _ => by rw [hD, smul_zero]
  rw [omegaC, expLC_eq_self _ h0]
  exact algebraMapInv_ιMulti_succ v

theorem omegaC_one' (C : Matrix Λ Λ ℂ) : omegaC C 1 = 1 := by
  have h0 : LopC C (1 : N Λ) = 0 := by
    rw [LopC_apply]
    refine sum_eq_zero fun x _ => sum_eq_zero fun y _ => ?_
    rw [show (1 : N Λ) = algebraMap ℂ (N Λ) 1 from (map_one _).symm, D_algebraMap, map_zero,
      smul_zero]
  rw [omegaC, expLC_eq_self _ h0, map_one]

theorem omegaC_sub_zero_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {C : Matrix Λ Λ ℂ} {Fv Gv : Λ → H} (hC : IsGram C Fv Gv) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ : γ ≤ ℓ) (hℓ : 0 < ℓ) {b : ℕ} (σ : Fin b → ℤˣ) (f : Fin b → Λ → ℝ) {M : ℝ}
    (hM : ∏ j, gnorm Fv Gv (σ j) (f j) ≤ γ ^ b * M) (hM0 : 0 ≤ M) :
    ‖omegaC C (ιMulti ℂ b fun j => pureV (σ j) (f j)) -
        omegaC (0 : Matrix Λ Λ ℂ) (ιMulti ℂ b fun j => pureV (σ j) (f j))‖ ≤
      (γ / ℓ) ^ 2 * ℓ ^ b * M := by
  rcases b with _ | _ | b
  · rw [ιMulti_zero_apply, omegaC_one', omegaC_one', sub_self, norm_zero]
    positivity
  · rw [omegaC_ιMulti_one, omegaC_ιMulti_one, sub_self, norm_zero]
    positivity
  · rw [omegaC_zero_ιMulti_succ, sub_zero]
    refine (abs_omegaC_pure_le hC σ f).trans (hM.trans ?_)
    have hγℓ : γ / ℓ ≤ 1 := (div_le_one hℓ).2 hγ
    have hγℓ0 : 0 ≤ γ / ℓ := div_nonneg hγ0 hℓ.le
    have e : γ ^ (b + 2) = (γ / ℓ) ^ 2 * ((γ / ℓ) ^ b * ℓ ^ (b + 2)) := by
      have hℓ0 : ℓ ≠ 0 := hℓ.ne'
      rw [div_pow, div_pow, pow_add ℓ b 2]
      field_simp
      ring
    rw [e]
    have : (γ / ℓ) ^ b ≤ 1 := pow_le_one₀ hγℓ0 hγℓ
    have h1 : (γ / ℓ) ^ b * ℓ ^ (b + 2) ≤ ℓ ^ (b + 1 + 1) := by
      calc (γ / ℓ) ^ b * ℓ ^ (b + 2) ≤ 1 * ℓ ^ (b + 2) :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = ℓ ^ (b + 1 + 1) := by rw [one_mul]
    calc (γ / ℓ) ^ 2 * ((γ / ℓ) ^ b * ℓ ^ (b + 2)) * M ≤ (γ / ℓ) ^ 2 * ℓ ^ (b + 1 + 1) * M := by
          gcongr
      _ = _ := rfl

/-- **`‖(𝔼_R − 𝔼_0) F‖_{T(ℓ)} ≤ (γ/ℓ)² ‖F‖_{T(ℓ ⊔ ℓ)}`** for a covariance with a Gram
representation with constant `γ ≤ ℓ`. -/
theorem tNorm_ECC_sub_le (hh : 0 < h) (hℓ : 0 < ℓ) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ ≤ ℓ)
    {C : Matrix Λ Λ ℂ} {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] {Fv Gv : Λ → H} (hC : IsGram C Fv Gv)
    (hB : GramBound E p h γ Fv Gv) (F : N (Λ ⊕ Λ)) :
    tNorm E p h ℓ (ECC C F - ECC 0 F) ≤ ENNReal.ofReal ((γ / ℓ) ^ 2) * tNorm E p h ℓ F := by
  set M : ℝ := (γ / ℓ) ^ 2 with hMdef
  have hM0 : 0 ≤ M := by positivity
  rw [← ENNReal.ofReal_toReal (tNorm_ne_top hh hℓ F), ← ENNReal.ofReal_mul hM0]
  refine tNorm_le fun g hg => ?_
  set T : N (Λ ⊕ Λ) →ₗ[ℂ] N Λ := ECC C - ECC 0 with hT
  set gT : TestFn (Λ ⊕ Λ) := fun n w => pair (T (psiPow w)) g
  have hpair : pair (T F) g = pair F gT := by
    conv_lhs => rw [sum_coeff F]
    simp only [map_sum, map_smul, pair_sum, pair_smul]
    conv_rhs => rw [pair]
    simp only [gT, mul_sum]
    refine sum_congr rfl fun n _ => sum_congr rfl fun w _ => by ring
  have hg1 : phiNorm E p h ℓ g ≤ ENNReal.ofReal 1 := by rwa [ENNReal.ofReal_one]
  have hAg : phiNorm E p h ℓ (asym g) ≤ ENNReal.ofReal 1 := (phiNorm_asym_le hh.le hℓ g).trans hg1
  have hgT : phiNorm E p h ℓ gT ≤ ENNReal.ofReal M := by
    refine phiNorm_le fun n w α hα => ?_
    have h1 : nab α (gT n) w = pair (T (ιMulti ℂ n fun i => dvec (α i) (w i))) g :=
      nab_psiPow ((pairL g) ∘ₗ T) α w
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
    have hTe : T (ιMulti ℂ n fun i => dvec (α i) (w i)) =
        (s * (omegaC C (ιMulti ℂ b fun j => dvec (αζ j) (zζ j)) -
          omegaC 0 (ιMulti ℂ b fun j => dvec (αζ j) (zζ j)))) •
          ιMulti ℂ a fun j => dvec (αψ j) (zψ j) := by
      rw [heq, map_smul, ← incl, ← inclζ, hT, LinearMap.sub_apply, ECC_incl_mul_inclζ,
        ECC_incl_mul_inclζ, ← sub_smul, smul_smul]
    rw [h1, hTe, pair_smul]
    -- the `ψ` part
    have hA : pair (ιMulti ℂ a fun j => dvec (αψ j) (zψ j)) g = nab αψ (asym g a) zψ := by
      rw [show pair (ιMulti ℂ a fun j => dvec (αψ j) (zψ j)) g =
        pairL g (ιMulti ℂ a fun j => dvec (αψ j) (zψ j)) from rfl, ← nab_psiPow (pairL g) αψ zψ]
      have hfun : (fun w : Fin a → Sf Λ => pairL g (psiPow w)) = asym g a :=
        funext fun z => pair_psiPow z g
      rw [hfun]
    have hAb := abs_nab_le hh hℓ zero_le_one hAg zψ αψ (fun j => hα _)
    -- the `ζ` part (Gram)
    have hB' : ‖omegaC C (ιMulti ℂ b fun j => dvec (αζ j) (zζ j)) -
        omegaC 0 (ιMulti ℂ b fun j => dvec (αζ j) (zζ j))‖ ≤
        M * ℓ ^ b * (h ^ ord αζ)⁻¹ := by
      simp_rw [dvec_eq_pureV]
      refine omegaC_sub_zero_le hC hγ0 hγ hℓ _ _ ?_ (by positivity)
      calc ∏ j, gnorm Fv Gv (zζ j).2 (dprof (αζ j) (zζ j).1)
          ≤ ∏ j : Fin b, γ * (h ^ mabs (αζ j))⁻¹ :=
            prod_le_prod (fun _ _ => gnorm_nonneg _ _ _ _)
              fun j _ => gnorm_le hB (hα _) _ _
        _ = γ ^ b * (h ^ ord αζ)⁻¹ := by
            rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, prod_inv_distrib,
              prod_pow_eq_pow_sum, ord]
    have hn : a + b = n := by simpa using Fintype.card_congr e
    have hord := ord_equiv e α
    rw [norm_mul, norm_mul, hs, one_mul, hA]
    calc ℓ⁻¹ ^ n * h ^ ord α * (‖omegaC C (ιMulti ℂ b fun j => dvec (αζ j) (zζ j)) -
          omegaC 0 (ιMulti ℂ b fun j => dvec (αζ j) (zζ j))‖ * ‖nab αψ (asym g a) zψ‖)
        ≤ ℓ⁻¹ ^ n * h ^ ord α * ((M * ℓ ^ b * (h ^ ord αζ)⁻¹) *
            (1 * ℓ ^ a * (h ^ ord αψ)⁻¹)) := by
          gcongr
      _ = M := by
          rw [hord, pow_add, show ℓ⁻¹ ^ n = ℓ⁻¹ ^ (a + b) by rw [hn], pow_add, inv_pow, inv_pow]
          field_simp
          ring
  show ‖pair (T F) g‖ ≤ _
  rw [hpair]
  have := abs_pair_le hh hℓ F hM0 hgT
  rwa [mul_comm] at this

theorem ECC_zero_theta (F : N Λ) : ECC (0 : Matrix Λ Λ ℂ) (theta F) = F := by
  rw [ECC_theta]
  exact expLC_eq_self _ (by rw [LopC_apply]; simp)

/-- **`‖e^{ℒ_R}F − F‖_{T(ℓ)} ≤ (γ/ℓ)² ‖F‖_{T(2ℓ)}`** under a Gram representation of `R` with
constant `γ ≤ ℓ`. -/
theorem tNorm_expLC_sub_le (hh : 0 < h) (hℓ : 0 < ℓ) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ ≤ ℓ)
    {C : Matrix Λ Λ ℂ} {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] {Fv Gv : Λ → H} (hC : IsGram C Fv Gv)
    (hB : GramBound E p h γ Fv Gv) (F : N Λ) :
    tNorm E p h ℓ (expLC C F - F) ≤ ENNReal.ofReal ((γ / ℓ) ^ 2) * tNorm E p h (2 * ℓ) F := by
  have := tNorm_ECC_sub_le hh hℓ hγ0 hγ hC hB (theta F)
  rw [ECC_theta, ECC_zero_theta] at this
  exact this.trans (mul_le_mul_right (tNorm_theta_le hh hℓ F) _)

end

end Grassmann
