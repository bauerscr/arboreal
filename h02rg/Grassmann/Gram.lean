import Grassmann.Doubled
import Grassmann.Doubling
import Grassmann.Hadamard

/-!
# The Gram inequality (`e:E-contract2`, `e:E-contract`)

For a positive semidefinite covariance `C` with `‖C‖_{Φ_j(ℓ)} ≤ 1` and `F ∈ 𝒩(Λ ⊔ Λ)`,
`‖𝔼_C F‖_{T_j(ℓ)} ≤ ‖F‖_{T_j(ℓ ⊔ ℓ)}`; with `e:theta-bd` this gives
`‖𝔼_C θ F‖_{T_j(ℓ)} ≤ ‖F‖_{T_j(2ℓ)}`.

The covariance is measured by the `Φ` norm of the coefficients of
`∑_{x,y} C_{xy} ψ̄_x ψ_y` (`covNorm`), as in the paragraph before `e:Cleq1`.
-/

namespace Grassmann

noncomputable section

open CliffordAlgebra ExteriorAlgebra Finset Matrix

/-! ### Sorting a product of vectors -/

theorem ιMulti_cast {M : Type*} [AddCommGroup M] [Module ℂ M] {m n : ℕ} (h : m = n)
    (v : Fin m → M) : ιMulti ℂ n (v ∘ Fin.cast h.symm) = ιMulti ℂ m v := by
  subst h; rfl

/-- Any product `ι u_1 ⋯ ι u_n` equals `±` the product of the factors with `P` followed by the
factors without `P`. -/
theorem ιMulti_split {M : Type*} [AddCommGroup M] [Module ℂ M] {n : ℕ} (u : Fin n → M)
    (P : Fin n → Prop) [DecidablePred P] :
    ∃ (a b : ℕ) (e : Fin a ⊕ Fin b ≃ Fin n) (s : ℂ), ‖s‖ = 1 ∧ (∀ j, P (e (Sum.inl j))) ∧
      (∀ j, ¬P (e (Sum.inr j))) ∧
      ιMulti ℂ n u = s • (ιMulti ℂ a (u ∘ e ∘ Sum.inl) * ιMulti ℂ b (u ∘ e ∘ Sum.inr)) := by
  set S := univ.filter P
  let e : Fin S.card ⊕ Fin Sᶜ.card ≃ Fin n := finSumEquivOfFinset rfl rfl
  have hab : S.card + Sᶜ.card = n := by rw [card_add_card_compl, Fintype.card_fin]
  let π : Equiv.Perm (Fin n) := (finCongr hab.symm).trans (finSumFinEquiv.symm.trans e)
  refine ⟨S.card, Sᶜ.card, e, (Equiv.Perm.sign π : ℂ), ?_, fun j => ?_, fun j => ?_, ?_⟩
  · rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
  · have hm := orderEmbOfFin_mem S rfl j
    simp only [S, mem_filter, mem_univ, true_and] at hm
    simp only [e, finSumEquivOfFinset_inl]
    exact hm
  · have hm := Finset.mem_compl.1 (orderEmbOfFin_mem Sᶜ rfl j)
    simp only [S, mem_filter, mem_univ, true_and] at hm
    simp only [e, finSumEquivOfFinset_inr]
    exact hm
  · have hperm := AlternatingMap.map_perm (ιMulti ℂ n) u π
    have hcomp : u ∘ π = Fin.append (u ∘ e ∘ Sum.inl) (u ∘ e ∘ Sum.inr) ∘ Fin.cast hab.symm := by
      ext i
      simp only [Function.comp_apply, π, Equiv.trans_apply, finCongr_apply]
      rw [append_eq_sumElim]
      simp only [Function.comp_apply]
      rcases h : finSumFinEquiv.symm (Fin.cast hab.symm i) with j | j <;> simp
    rw [hcomp, ιMulti_cast hab, ← ιMulti_mul_ιMulti] at hperm
    rw [hperm, Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ, smul_smul, ← Int.cast_mul,
      ← Units.val_mul, Int.units_mul_self]
    simp

/-! ### Gram's inequality for Gaussian moments -/

section Moment

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

/-- The vector `∑_x f(x) ψ_{(x, σ)}`. -/
def pureV (σ : ℤˣ) (f : Λ → ℝ) : V Λ := if σ = 1 then vpsi f else vbar f

/-- Gram's inequality: `‖⟨∏_j (∑_x f_j(x) ψ_{x, σ_j})⟩_C‖ ≤ ∏_j (f_j · C f_j)^{1/2}`. -/
theorem abs_omega_pure_le {C : Matrix Λ Λ ℝ} (hC : C.PosSemidef) {m : ℕ} (σ : Fin m → ℤˣ)
    (f : Fin m → Λ → ℝ) :
    ‖omega C (ιMulti ℂ m fun j => pureV (σ j) (f j))‖ ≤
      ∏ j, Real.sqrt (f j ⬝ᵥ (C *ᵥ f j)) := by
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
  rw [heq, omega_smul, hbar, hpsi, norm_mul, hs, one_mul]
  have hprod : ∏ j, Real.sqrt (f j ⬝ᵥ (C *ᵥ f j)) =
      (∏ j : Fin a, Real.sqrt (f (e (Sum.inl j)) ⬝ᵥ (C *ᵥ f (e (Sum.inl j))))) *
        ∏ j : Fin b, Real.sqrt (f (e (Sum.inr j)) ⬝ᵥ (C *ᵥ f (e (Sum.inr j)))) := by
    rw [← Fintype.prod_sum_type (fun j => Real.sqrt (f (e j) ⬝ᵥ (C *ᵥ f (e j))))]
    exact (Fintype.prod_equiv e _ _ fun _ => rfl).symm
  by_cases hab : a = b
  · subst hab
    rw [omega_moment, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_real,
      Real.norm_eq_abs, hprod, ← prod_mul_distrib]
    exact abs_det_psd_le hC _ _
  · rw [omega_moment_of_ne _ _ _ hab, norm_zero]; positivity

end Moment

/-! ### The norm of the covariance -/

section Cov

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ] {E : Type*} [Fintype E] [DecidableEq E]
  [AddAction (E → ℕ) Λ]

/-- `∑_{x,y} C_{xy} ψ̄_x ψ_y`. -/
def covForm (C : Matrix Λ Λ ℝ) : N Λ := ∑ x, ∑ y, (C x y : ℂ) • (psibar x * psi y)

/-- The covariance as a test function: the coefficients of `∑_{x,y} C_{xy} ψ̄_x ψ_y`. -/
def covTest (C : Matrix Λ Λ ℝ) : TestFn Λ := fun _ z => coeff (covForm C) z

variable (E) in
/-- `‖C‖_{Φ}`: the `Φ` norm of the covariance, regarded as the coefficient function of
`∑_{x,y} C_{xy} ψ̄_x ψ_y` (see before `e:Cleq1`). -/
def covNorm (p : ℕ) (h ℓ : ℝ) (C : Matrix Λ Λ ℝ) : ENNReal := phiNorm E p h ℓ (covTest C)

theorem coeff_two (F : N Λ) (a b : Sf Λ) : coeff F ![a, b] = ε (D b (D a F)) := by
  simp only [coeff, Dseq, contr_succ, contr_zero]
  rfl

theorem D_psibar_mul_psi (x y a : Λ) :
    D (a, -1) (psibar x * psi y) = if a = x then psi y else 0 := by
  have hne : ((a, -1) : Sf Λ) ≠ (y, 1) := by simp [Prod.ext_iff]
  rw [D_mul, psibar, psi, D_ψ, D_ψ, if_neg hne, mul_zero, add_zero]
  by_cases h : a = x
  · subst h; simp
  · rw [if_neg (by simp [Prod.ext_iff, h]), if_neg h, zero_mul]

theorem coeff_covForm (C : Matrix Λ Λ ℝ) (y y' : Λ) :
    coeff (covForm C) ![(y, -1), (y', 1)] = (C y y' : ℂ) := by
  rw [coeff_two, covForm]
  simp only [map_sum, map_smul, D_psibar_mul_psi, apply_ite (D _), map_zero, smul_ite,
    smul_zero]
  simp [psi, D_ψ, Prod.ext_iff, apply_ite ε, Finset.sum_ite_eq, AlgHom.map_smul_of_tower,
    Complex.real_smul]

/-- The spatial profile `∇^a δ_x = ∑_{b ≤ a} c_{a,b} δ_{x + b}`. -/
def dprof (a : E → ℕ) (x : Λ) : Λ → ℝ := ∑ b ∈ Iic a, cf a b • Pi.single (b +ᵥ x) 1

theorem dprof_quad (C : Matrix Λ Λ ℝ) (a : E → ℕ) (x : Λ) :
    ((dprof a x ⬝ᵥ (C *ᵥ dprof a x) : ℝ) : ℂ) =
      nab (X := Λ) ![a, a] (covTest C 2) ![(x, -1), (x, 1)] := by
  rw [nabla_apply]
  have hbij : ∑ β ∈ Fintype.piFinset (fun i => Iic ((![a, a] : Fin 2 → E → ℕ) i)),
      (∏ i, cf ((![a, a] : Fin 2 → E → ℕ) i) (β i)) •
        covTest C 2 (fun i => sh (β i) ((![(x, -1), (x, 1)] : Fin 2 → Sf Λ) i)) =
      ∑ p ∈ Iic a ×ˢ Iic a, ((cf a p.1 * cf a p.2 * C (p.1 +ᵥ x) (p.2 +ᵥ x) : ℝ) : ℂ) := by
    refine Finset.sum_nbij' (fun β => (β 0, β 1)) (fun p => ![p.1, p.2]) ?_ ?_ ?_ ?_ ?_
    · intro β hβ
      rw [Fintype.mem_piFinset] at hβ
      exact mem_product.2 ⟨hβ 0, hβ 1⟩
    · intro q hq
      rw [mem_product] at hq
      rw [Fintype.mem_piFinset]
      intro i; fin_cases i
      exacts [hq.1, hq.2]
    · intro β _; funext i; fin_cases i <;> rfl
    · intro q _; rfl
    · intro β _
      have : (fun i => sh (β i) ((![(x, -1), (x, 1)] : Fin 2 → Sf Λ) i)) =
          ![(β 0 +ᵥ x, -1), (β 1 +ᵥ x, 1)] := by
        funext i; fin_cases i <;> rfl
      rw [this, covTest, coeff_covForm, Fin.prod_univ_two, Complex.real_smul]
      push_cast; rfl
  rw [hbij, ← Complex.ofReal_sum]
  congr 1
  rw [sum_product]
  simp only [dprof, sum_dotProduct, dotProduct_sum, mulVec_sum, smul_dotProduct, mulVec_smul,
    dotProduct_smul, single_one_dotProduct, mulVec_single_one, smul_eq_mul]
  rw [sum_comm]
  refine sum_congr rfl fun b _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun b' _ => ?_
  simp only [Matrix.col_apply]
  ring

end Cov

/-! ### The contraction estimate -/

section Contract

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- `∇^a` applied to the generator `ψ_y`: `∑_{b ≤ a} c_{a,b} ψ_{y + b}` (as a vector). -/
def dvec {Y : Type*} [DecidableEq Y] [AddAction (E → ℕ) Y] (a : E → ℕ) (y : Sf Y) : V Y :=
  ∑ b ∈ Iic a, cf a b • ev (sh b y)

/-- `∇^α_w T(ψ^w) = T(∏_i ∇^{α_i} ψ_{w_i})` for linear `T`. -/
theorem nab_psiPow {Y : Type*} [DecidableEq Y] [AddAction (E → ℕ) Y] {W : Type*}
    [AddCommGroup W] [Module ℂ W] (T : N Y →ₗ[ℂ] W) {n : ℕ} (α : Fin n → E → ℕ)
    (w : Fin n → Sf Y) :
    nab α (fun w => T (psiPow w)) w = T (ιMulti ℂ n fun i => dvec (α i) (w i)) := by
  have := nabla_multilinear (sh (X := Y)) α
    ((T.compMultilinearMap (ιMulti ℂ n).toMultilinearMap).restrictScalars ℝ) (fun _ => ev) w
  simpa [psiPow, dvec] using this

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ] [AddAction (E → ℕ) Λ]

theorem ev_inl (y : Sf Λ) : ev ((Sum.inl y.1, y.2) : Sf (Λ ⊕ Λ)) = inlV (ev y) := by
  ext ⟨c, τ⟩; cases c <;> simp [inlV, ev, Pi.single_apply, Prod.ext_iff]

theorem ev_inr (y : Sf Λ) : ev ((Sum.inr y.1, y.2) : Sf (Λ ⊕ Λ)) = inrV (ev y) := by
  ext ⟨c, τ⟩; cases c <;> simp [inrV, ev, Pi.single_apply, Prod.ext_iff]

theorem dvec_inl (a : E → ℕ) (y : Sf Λ) :
    dvec a ((Sum.inl y.1, y.2) : Sf (Λ ⊕ Λ)) = inlV (dvec a y) := by
  simp only [dvec, map_sum, LinearMap.map_smul_of_tower]
  refine sum_congr rfl fun b _ => ?_
  rw [← ev_inl]; rfl

theorem dvec_inr (a : E → ℕ) (y : Sf Λ) :
    dvec a ((Sum.inr y.1, y.2) : Sf (Λ ⊕ Λ)) = inrV (dvec a y) := by
  simp only [dvec, map_sum, LinearMap.map_smul_of_tower]
  refine sum_congr rfl fun b _ => ?_
  rw [← ev_inr]; rfl

theorem dvec_eq_pureV (a : E → ℕ) (y : Sf Λ) : dvec a y = pureV y.2 (dprof a y.1) := by
  ext ⟨c, τ⟩
  simp only [dvec, dprof, pureV, Finset.sum_apply, Pi.smul_apply, Complex.real_smul,
    ev, sh, Pi.single_apply, Prod.ext_iff]
  rcases Int.units_eq_one_or y.2 with h | h <;> rcases Int.units_eq_one_or τ with h' | h' <;>
    simp [h, h', vpsi, vbar, Finset.sum_apply, Pi.single_apply, eq_comm, apply_ite ((↑) : ℝ → ℂ)]

theorem ord_equiv {a b n : ℕ} (e : Fin a ⊕ Fin b ≃ Fin n) (α : Fin n → E → ℕ) :
    ord α = ord (α ∘ e ∘ Sum.inl) + ord (α ∘ e ∘ Sum.inr) := by
  simp only [ord, Function.comp_apply]
  rw [← Fintype.sum_sum_type (fun j => mabs (α (e j)))]
  exact (Fintype.sum_equiv e _ _ fun _ => rfl).symm

variable {p : ℕ} {h ℓ : ℝ}

theorem sqrt_dprof_quad_le (hh : 0 < h) (hℓ : 0 < ℓ) {C : Matrix Λ Λ ℝ}
    (hCn : covNorm E p h ℓ C ≤ 1) {a : E → ℕ} (ha : mabs a ≤ p) (x : Λ) :
    Real.sqrt (dprof a x ⬝ᵥ (C *ᵥ dprof a x)) ≤ ℓ * (h ^ mabs a)⁻¹ := by
  have hb := abs_nab_le hh hℓ zero_le_one (by rwa [ENNReal.ofReal_one]) (g := covTest C)
    ![(x, -1), (x, 1)] ![a, a] (fun i => by fin_cases i <;> simpa)
  rw [← dprof_quad] at hb
  have hord : ord (![a, a] : Fin 2 → E → ℕ) = mabs a + mabs a := by
    simp [ord, Fin.sum_univ_two]
  rw [hord, one_mul, pow_add, mul_inv, show ℓ ^ 2 * ((h ^ mabs a)⁻¹ * (h ^ mabs a)⁻¹) =
    (ℓ * (h ^ mabs a)⁻¹) ^ 2 by ring] at hb
  rw [Complex.norm_real, Real.norm_eq_abs] at hb
  calc Real.sqrt (dprof a x ⬝ᵥ (C *ᵥ dprof a x)) ≤ Real.sqrt ((ℓ * (h ^ mabs a)⁻¹) ^ 2) :=
        Real.sqrt_le_sqrt ((le_abs_self _).trans hb)
    _ = ℓ * (h ^ mabs a)⁻¹ := Real.sqrt_sq (by positivity)

/-- The Gram inequality `e:E-contract2`: if `C` is positive semidefinite with
`‖C‖_{Φ_j(ℓ)} ≤ 1`, then `‖𝔼_C F‖_{T_j(ℓ)} ≤ ‖F‖_{T_j(ℓ ⊔ ℓ)}` for `F ∈ 𝒩(Λ ⊔ Λ)`. -/
theorem tNorm_EC_le (hh : 0 < h) (hℓ : 0 < ℓ) {C : Matrix Λ Λ ℝ} (hC : C.PosSemidef)
    (hCn : covNorm E p h ℓ C ≤ 1) (F : N (Λ ⊕ Λ)) :
    tNorm E p h ℓ (EC C F) ≤ tNorm E p h ℓ F := by
  rw [← ENNReal.ofReal_toReal (tNorm_ne_top hh hℓ F)]
  refine tNorm_le fun g hg => ?_
  -- the test function `g̃_w = ⟨𝔼_C ψ^w, g⟩` on the doubled sequences
  set gT : TestFn (Λ ⊕ Λ) := fun n w => pair (EC C (psiPow w)) g
  have hpair : pair (EC C F) g = pair F gT := by
    conv_lhs => rw [sum_coeff F]
    simp only [map_sum, map_smul, pair_sum, pair_smul]
    conv_rhs => rw [pair]
    simp only [gT, mul_sum]
    refine sum_congr rfl fun n _ => sum_congr rfl fun w _ => by ring
  have hg1 : phiNorm E p h ℓ g ≤ ENNReal.ofReal 1 := by rwa [ENNReal.ofReal_one]
  have hAg : phiNorm E p h ℓ (asym g) ≤ ENNReal.ofReal 1 := (phiNorm_asym_le hh.le hℓ g).trans hg1
  have hgT : phiNorm E p h ℓ gT ≤ ENNReal.ofReal 1 := by
    refine phiNorm_le fun n w α hα => ?_
    have h1 : nab α (gT n) w = pair (EC C (ιMulti ℂ n fun i => dvec (α i) (w i))) g :=
      nab_psiPow ((pairL g) ∘ₗ EC C) α w
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
    rw [h1, heq, map_smul, ← incl, ← inclζ, EC_incl_mul_inclζ, pair_smul, pair_smul]
    -- the `ψ` part
    have hA : pair (ιMulti ℂ a fun j => dvec (αψ j) (zψ j)) g = nab αψ (asym g a) zψ := by
      rw [show pair (ιMulti ℂ a fun j => dvec (αψ j) (zψ j)) g =
        pairL g (ιMulti ℂ a fun j => dvec (αψ j) (zψ j)) from rfl, ← nab_psiPow (pairL g) αψ zψ]
      have hfun : (fun w : Fin a → Sf Λ => pairL g (psiPow w)) = asym g a :=
        funext fun z => pair_psiPow z g
      rw [hfun]
    have hAb := abs_nab_le hh hℓ zero_le_one hAg zψ αψ (fun j => hα _)
    -- the `ζ` part (Gram)
    have hB : ‖omega C (ιMulti ℂ b fun j => dvec (αζ j) (zζ j))‖ ≤ ℓ ^ b * (h ^ ord αζ)⁻¹ := by
      simp_rw [dvec_eq_pureV]
      refine (abs_omega_pure_le hC _ _).trans ?_
      calc ∏ j, Real.sqrt (dprof (αζ j) (zζ j).1 ⬝ᵥ (C *ᵥ dprof (αζ j) (zζ j).1))
          ≤ ∏ j : Fin b, ℓ * (h ^ mabs (αζ j))⁻¹ :=
            prod_le_prod (fun _ _ => Real.sqrt_nonneg _)
              fun j _ => sqrt_dprof_quad_le hh hℓ hCn (hα _) _
        _ = ℓ ^ b * (h ^ ord αζ)⁻¹ := by
            rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, prod_inv_distrib,
              prod_pow_eq_pow_sum, ord]
    have hn : a + b = n := by simpa using Fintype.card_congr e
    have hord := ord_equiv e α
    rw [norm_mul, norm_mul, hs, one_mul, hA]
    calc ℓ⁻¹ ^ n * h ^ ord α * (‖omega C (ιMulti ℂ b fun j => dvec (αζ j) (zζ j))‖ *
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

/-- `e:E-contract`: `‖𝔼_C θ F‖_{T_j(ℓ)} ≤ ‖F‖_{T_j(2ℓ)}`. -/
theorem tNorm_EC_theta_le (hh : 0 < h) (hℓ : 0 < ℓ) {C : Matrix Λ Λ ℝ} (hC : C.PosSemidef)
    (hCn : covNorm E p h ℓ C ≤ 1) (F : N Λ) :
    tNorm E p h ℓ (EC C (theta F)) ≤ tNorm E p h (2 * ℓ) F :=
  (tNorm_EC_le hh hℓ hC hCn _).trans (tNorm_theta_le hh hℓ F)

end Contract

end

end Grassmann
