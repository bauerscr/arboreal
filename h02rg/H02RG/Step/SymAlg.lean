import Step.Defs

/-!
# Symmetries of `θ` and `𝔼_C` (Section `sec:symmetries`)

* Bijections `E` of `Λ` act on `𝒩(Λ ⊔ Λ)` (`autAlg2`), and `𝔼_C θ` commutes with them if
  `C(Ex, Ey) = C(x, y)` (`theta_autAlg`, `EC_autAlg2`).
* The symplectic symmetry `J` commutes with `θ` and, for symmetric `C`, with `𝔼_C`.
* `U(1)` invariance is invariance under the scaling `ψ ↦ t ψ`, `ψ̄ ↦ t⁻¹ ψ̄` (`isSym_iff_scal`);
  it is preserved by `θ`, `𝔼_C`, products, and `Loc`.
* Locality: `θ 𝒩(X) ⊆ 𝒩(X ⊔ X)` and `𝔼_C 𝒩(X ⊔ X) ⊆ 𝒩(X)`.
-/

namespace Step

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

/-- The doubled algebra `𝒩(Λ ⊔ Λ)`. -/
abbrev Alg2 (d L N : ℕ) [NeZero L] := Grassmann.N (Lam d L N ⊕ Lam d L N)

theorem map_map_apply {Λ₁ Λ₂ Λ₃ : Type*} (f : V Λ₂ →ₗ[ℂ] V Λ₃) (g : V Λ₁ →ₗ[ℂ] V Λ₂)
    (x : Grassmann.N Λ₁) :
    ExteriorAlgebra.map f (ExteriorAlgebra.map g x) = ExteriorAlgebra.map (f ∘ₗ g) x := by
  rw [← ExteriorAlgebra.map_comp_map]; rfl

theorem map_congr_apply {Λ₁ Λ₂ : Type*} {f g : V Λ₁ →ₗ[ℂ] V Λ₂} (h : ∀ v b, f v b = g v b)
    (x : Grassmann.N Λ₁) : ExteriorAlgebra.map f x = ExteriorAlgebra.map g x := by
  have : f = g := LinearMap.ext fun v => funext fun b => h v b
  rw [this]

/-- The chain rule for `D` and `ExteriorAlgebra.map`. -/
theorem D_map {Λ₁ Λ₂ : Type*} [DecidableEq Λ₂] (f : V Λ₁ →ₗ[ℂ] V Λ₂) (a : Sf Λ₂)
    (x : Grassmann.N Λ₁) :
    D a (ExteriorAlgebra.map f x) = ExteriorAlgebra.map f (CliffordAlgebra.contractLeft (coord a ∘ₗ f) x) :=
  contractLeft_map f _ x

/-- `𝔼_C` commutes with algebra maps intertwining `ℒ_C^ζ` and setting `ζ = 0`. -/
theorem EC_comm_of {C : Matrix (Lam d L N) (Lam d L N) ℝ} (g : Alg2 d L N →ₐ[ℂ] Alg2 d L N)
    (g' : Alg d L N →ₐ[ℂ] Alg d L N)
    (hL : ∀ G, Lζ C (g G) = g (Lζ C G)) (hp : ∀ G, proj (g G) = g' (proj G)) (F : Alg2 d L N) :
    EC C (g F) = g' (EC C F) := by
  have hc : Lζ C ∘ₗ g.toLinearMap = g.toLinearMap ∘ₗ Lζ C := LinearMap.ext fun G => hL G
  have h := Module.End.commute_exp_left_of_commute (Lζ_isNilpotent C) (Lζ_isNilpotent C) hc
  have h2 := LinearMap.congr_fun h F
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply] at h2
  rw [EC, LinearMap.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, h2,
    AlgHom.toLinearMap_apply, hp]

/-! ### Automorphisms on the doubled algebra -/

/-- The action of a bijection `E` of `Λ` on the generators of `𝒩(Λ ⊔ Λ)`. -/
def autV2 (E : Lam d L N ≃ Lam d L N) :
    V (Lam d L N ⊕ Lam d L N) →ₗ[ℂ] V (Lam d L N ⊕ Lam d L N) :=
  LinearMap.funLeft ℂ ℂ fun a : Sf (Lam d L N ⊕ Lam d L N) => (Sum.map E.symm E.symm a.1, a.2)

/-- `E ψ_x = ψ_{Ex}`, `E ζ_x = ζ_{Ex}` (and likewise for `ψ̄`, `ζ̄`). -/
def autAlg2 (E : Lam d L N ≃ Lam d L N) : Alg2 d L N →ₐ[ℂ] Alg2 d L N :=
  ExteriorAlgebra.map (autV2 E)

theorem theta_autAlg (E : Lam d L N ≃ Lam d L N) (F : Alg d L N) :
    theta (autAlg E F) = autAlg2 E (theta F) := by
  simp only [theta, autAlg, autAlg2, map_map_apply]
  refine map_congr_apply (fun v b => ?_) F
  rcases b with ⟨b | b, σ⟩ <;> rfl

theorem incl_autAlg (E : Lam d L N ≃ Lam d L N) (F : Alg d L N) :
    incl (autAlg E F) = autAlg2 E (incl F) := by
  simp only [incl, autAlg, autAlg2, map_map_apply]
  refine map_congr_apply (fun v b => ?_) F
  rcases b with ⟨b | b, σ⟩ <;> rfl

/-- `𝔼_C` commutes with lattice maps preserving `C`. -/
theorem EC_autAlg2 (E : Lam d L N ≃ Lam d L N) {C : Matrix (Lam d L N) (Lam d L N) ℝ}
    (hC : ∀ x y, C (E x) (E y) = C x y) (F : Alg2 d L N) :
    EC C (autAlg2 E F) = autAlg E (EC C F) := by
  refine EC_comm_of _ _ (fun G => ?_) (fun G => ?_) F
  · have hD : ∀ (b : Lam d L N ⊕ Lam d L N) (σ : ℤˣ) (H : Alg2 d L N),
        D (b, σ) (autAlg2 E H) = autAlg2 E (D (Sum.map E.symm E.symm b, σ) H) := by
      intro b σ H
      rw [autAlg2, D_map]; rfl
    simp only [Lζ_apply, hD, map_sum, map_smul, Sum.map_inr]
    rw [← Equiv.sum_comp E]
    refine sum_congr rfl fun x _ => ?_
    rw [← Equiv.sum_comp E]
    refine sum_congr rfl fun y _ => ?_
    simp [hC]
  · simp only [proj, autAlg2, autAlg, map_map_apply]
    exact map_congr_apply (fun v b => rfl) G

theorem autAlg_symm_apply (E : Lam d L N ≃ Lam d L N) (F : Alg d L N) :
    autAlg E.symm (autAlg E F) = F := by
  simp only [autAlg, map_map_apply]
  rw [map_congr_apply (g := LinearMap.id) (fun v b => by simp [autV]) F, ExteriorAlgebra.map_id]
  rfl

/-- An algebra map sending the generators of `𝒩(X)` into a subalgebra `S` maps `𝒩(X)` into `S`. -/
theorem algHom_mem_of_mem_NX {Λ₁ Λ₂ : Type*} [DecidableEq Λ₁] (g : Grassmann.N Λ₁ →ₐ[ℂ] Grassmann.N Λ₂)
    {X : Set Λ₁} {S : Subalgebra ℂ (Grassmann.N Λ₂)} (h : ∀ a : Sf Λ₁, a.1 ∈ X → g (ψ a) ∈ S)
    {F : Grassmann.N Λ₁} (hF : F ∈ NX X) : g F ∈ S := by
  induction hF using Algebra.adjoin_induction with
  | mem x hx => obtain ⟨⟨a, ha⟩, rfl⟩ := hx; exact h a ha
  | algebraMap r => rw [AlgHom.commutes]; exact Subalgebra.algebraMap_mem _ r
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

/-! ### The symplectic symmetry on the doubled algebra -/

/-- `J` on the generators of `𝒩(Λ ⊔ Λ)`. -/
def JV2 : V (Lam d L N ⊕ Lam d L N) →ₗ[ℂ] V (Lam d L N ⊕ Lam d L N) where
  toFun v a := if a.2 = -1 then v (a.1, 1) else -v (a.1, -1)
  map_add' v w := by ext a; by_cases h : a.2 = -1 <;> simp [h]; ring
  map_smul' c v := by ext a; by_cases h : a.2 = -1 <;> simp [h]

/-- `J ψ = ψ̄, J ψ̄ = -ψ, J ζ = ζ̄, J ζ̄ = -ζ`. -/
def Jsym2 : Alg2 d L N →ₐ[ℂ] Alg2 d L N := ExteriorAlgebra.map JV2

theorem theta_Jsym (F : Alg d L N) : theta (Jsym F) = Jsym2 (theta F) := by
  simp only [theta, Jsym, Jsym2, map_map_apply]
  refine map_congr_apply (fun v b => ?_) F
  rcases b with ⟨b | b, σ⟩ <;> rfl

theorem incl_Jsym (F : Alg d L N) : incl (Jsym F) = Jsym2 (incl F) := by
  simp only [incl, Jsym, Jsym2, map_map_apply]
  refine map_congr_apply (fun v b => ?_) F
  rcases b with ⟨b | b, σ⟩ <;> by_cases h : σ = -1 <;> simp [inlV, JV, JV2, h]

/-- `𝔼_C` commutes with `J` for symmetric `C`. -/
theorem EC_Jsym2 {C : Matrix (Lam d L N) (Lam d L N) ℝ} (hC : ∀ x y, C x y = C y x)
    (F : Alg2 d L N) : EC C (Jsym2 F) = Jsym (EC C F) := by
  refine EC_comm_of _ _ (fun G => ?_) (fun G => ?_) F
  · have h1 : ∀ (b : Lam d L N ⊕ Lam d L N) (H : Alg2 d L N),
        D (b, -1) (Jsym2 H) = Jsym2 (D (b, 1) H) := by
      intro b H
      rw [Jsym2, D_map]; rfl
    have h2 : ∀ (b : Lam d L N ⊕ Lam d L N) (H : Alg2 d L N),
        D (b, 1) (Jsym2 H) = -Jsym2 (D (b, -1) H) := by
      intro b H
      rw [Jsym2, D_map, ← map_neg]
      have : coord ((b, 1) : Sf (Lam d L N ⊕ Lam d L N)) ∘ₗ JV2 = -coord (b, -1) := by
        refine LinearMap.ext fun v => ?_
        simp [JV2]
      rw [this, map_neg, LinearMap.neg_apply]; rfl
    simp only [Lζ_apply, h1, h2, map_sum, map_smul, smul_neg]
    rw [sum_comm]
    refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
    rw [hC, D_comm, map_neg, smul_neg, neg_neg]
  · simp only [proj, Jsym2, Jsym, map_map_apply]
    exact map_congr_apply (fun v b => rfl) G

theorem Jsym_LocXY_of_patch {X : Finset (Lam d L N)} (hX : Patch X) (hne : X.Nonempty)
    (Y : Finset (Lam d L N)) {F : Alg d L N} (hF : Jsym F = F) :
    Jsym (LocXY X Y F) = LocXY X Y F := by
  rw [← LocXY_Jsym hX hne, hF]

/-- Elements of degree one anticommute. -/
theorem anticomm_of_mem_range {Λ : Type*} {a b : Grassmann.N Λ}
    (ha : a ∈ LinearMap.range (ExteriorAlgebra.ι ℂ : V Λ →ₗ[ℂ] Grassmann.N Λ))
    (hb : b ∈ LinearMap.range (ExteriorAlgebra.ι ℂ : V Λ →ₗ[ℂ] Grassmann.N Λ)) :
    a * b = -(b * a) := by
  obtain ⟨m, rfl⟩ := ha
  obtain ⟨n, rfl⟩ := hb
  exact ι_anticomm m n

theorem ψ_mem_range {Λ : Type*} [DecidableEq Λ] (a : Sf Λ) :
    ψ a ∈ LinearMap.range (ExteriorAlgebra.ι ℂ : V Λ →ₗ[ℂ] Grassmann.N Λ) :=
  LinearMap.mem_range_self _ _

theorem grad_mem_range (e : Dir d) (x : Lam d L N) :
    grad e x ∈ LinearMap.range (ExteriorAlgebra.ι ℂ : V _ →ₗ[ℂ] Alg d L N) :=
  sub_mem (ψ_mem_range _) (ψ_mem_range _)

theorem gradbar_mem_range (e : Dir d) (x : Lam d L N) :
    gradbar e x ∈ LinearMap.range (ExteriorAlgebra.ι ℂ : V _ →ₗ[ℂ] Alg d L N) :=
  sub_mem (ψ_mem_range _) (ψ_mem_range _)

theorem lapPsi_mem_range (x : Lam d L N) :
    lapPsi x ∈ LinearMap.range (ExteriorAlgebra.ι ℂ : V _ →ₗ[ℂ] Alg d L N) :=
  Submodule.smul_mem _ _ (Submodule.sum_mem _ fun e _ =>
    sub_mem (grad_mem_range e _) (grad_mem_range e _))

theorem lapPsibar_mem_range (x : Lam d L N) :
    lapPsibar x ∈ LinearMap.range (ExteriorAlgebra.ι ℂ : V _ →ₗ[ℂ] Alg d L N) :=
  Submodule.smul_mem _ _ (Submodule.sum_mem _ fun e _ =>
    sub_mem (gradbar_mem_range e _) (gradbar_mem_range e _))

theorem Jsym_grad (e : Dir d) (x : Lam d L N) : Jsym (grad e x) = gradbar e x := by
  rw [grad, map_sub, Jsym_psi, Jsym_psi, gradbar]

theorem Jsym_gradbar (e : Dir d) (x : Lam d L N) : Jsym (gradbar e x) = -grad e x := by
  rw [gradbar, map_sub, Jsym_psibar, Jsym_psibar, grad, neg_sub_neg, neg_sub]

theorem Jsym_lapPsi (x : Lam d L N) : Jsym (lapPsi x) = lapPsibar x := by
  simp only [lapPsi, lapPsibar, map_smul, map_sum, map_sub, Jsym_grad]

theorem Jsym_lapPsibar (x : Lam d L N) : Jsym (lapPsibar x) = -lapPsi x := by
  rw [lapPsibar, lapPsi, map_smul, map_sum, ← smul_neg, ← sum_neg_distrib]
  congr 1
  refine sum_congr rfl fun e _ => ?_
  rw [map_sub, Jsym_gradbar, Jsym_gradbar, neg_sub_neg, neg_sub]

theorem Jsym_gradSq (x : Lam d L N) : Jsym (gradSq x) = gradSq x := by
  rw [gradSq, map_smul, map_sum]
  congr 1
  refine sum_congr rfl fun e _ => ?_
  rw [map_mul, Jsym_grad, Jsym_gradbar, mul_neg,
    anticomm_of_mem_range (gradbar_mem_range e x) (grad_mem_range e x), neg_neg]

theorem Jsym_eval (V : Vcoup) (X : Finset (Lam d L N)) : Jsym (V.eval X) = V.eval X := by
  rw [Vcoup.eval, map_sum]
  refine sum_congr rfl fun x _ => ?_
  have h1 : psibar x * -psi x = psi x * psibar x := by
    rw [mul_neg, anticomm_of_mem_range (a := psibar x) (b := psi x) (ψ_mem_range _) (ψ_mem_range _),
      neg_neg]
  have h2 : lapPsibar x * psi x = psi x * -lapPsibar x := by
    rw [mul_neg, anticomm_of_mem_range (b := psi x) (lapPsibar_mem_range x) (ψ_mem_range _)]
  have h3 : psibar x * lapPsi x = -lapPsi x * psibar x := by
    rw [neg_mul, anticomm_of_mem_range (a := psibar x) (ψ_mem_range _) (lapPsi_mem_range x)]
  simp only [map_add, map_smul, map_mul, map_neg, Jsym_gradSq, Jsym_lapPsi, Jsym_lapPsibar,
    Jsym_psi, Jsym_psibar, neg_neg, neg_mul_neg, h1, h2, h3]
  abel_nf

/-! ### `U(1)` symmetry -/

/-- The scaling `ψ ↦ t ψ`, `ψ̄ ↦ t⁻¹ ψ̄` on the generators. -/
def scalV (Λ : Type*) (t : ℂ) : V Λ →ₗ[ℂ] V Λ where
  toFun v a := if a.2 = 1 then t * v a else t⁻¹ * v a
  map_add' v w := by ext a; by_cases h : a.2 = 1 <;> simp [h] <;> ring
  map_smul' c v := by ext a; by_cases h : a.2 = 1 <;> simp [h] <;> ring

/-- The `U(1)` scaling on `𝒩(Λ)`. -/
def scal (Λ : Type*) (t : ℂ) : Grassmann.N Λ →ₐ[ℂ] Grassmann.N Λ := ExteriorAlgebra.map (scalV Λ t)

/-- `U(1)` invariance on a general `𝒩(Λ)`: every monomial has as many `ψ̄` as `ψ`. -/
def IsSymG {Λ : Type*} [DecidableEq Λ] (F : Grassmann.N Λ) : Prop :=
  ∀ (n : ℕ) (z : Fin n → Sf Λ),
    (univ.filter fun i => (z i).2 = 1).card ≠ (univ.filter fun i => (z i).2 = -1).card →
      coeff F z = 0

theorem isSym_iff_isSymG (F : Alg d L N) : IsSym F ↔ IsSymG F := Iff.rfl

theorem contr_smul {Λ : Type*} {m : ℕ} (c : Fin m → ℂ) (φ : Fin m → Module.Dual ℂ (V Λ))
    (x : Grassmann.N Λ) : contr (fun i => c i • φ i) x = (∏ i, c i) • contr φ x := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    rw [contr_succ, contr_succ, map_smul, LinearMap.smul_apply, map_smul,
      show Fin.tail (fun i => c i • φ i) = fun i => Fin.tail c i • Fin.tail φ i from rfl, ih,
      smul_smul, Fin.prod_univ_succ]
    rfl

/-- The coefficients of `scal t F`. -/
theorem coeff_scal {Λ : Type*} [DecidableEq Λ] (t : ℂ) (F : Grassmann.N Λ) {n : ℕ}
    (z : Fin n → Sf Λ) :
    coeff (scal Λ t F) z = (∏ i, if (z i).2 = 1 then t else t⁻¹) * coeff F z := by
  rw [coeff, Dseq, scal, contr_map, algebraMapInv_map]
  have : (fun i => coord (z i) ∘ₗ scalV Λ t) =
      fun i => (if (z i).2 = 1 then t else t⁻¹) • coord (z i) := by
    funext i
    refine LinearMap.ext fun v => ?_
    by_cases h : (z i).2 = 1 <;> simp [scalV, h]
  rw [this, contr_smul, map_smul, smul_eq_mul]; rfl

theorem prod_scal_factor {Λ : Type*} (t : ℂ) {n : ℕ} (z : Fin n → Sf Λ) :
    (∏ i, if (z i).2 = 1 then t else t⁻¹) =
      t ^ (univ.filter fun i => (z i).2 = 1).card *
        t⁻¹ ^ (univ.filter fun i => (z i).2 = -1).card := by
  have hf : (univ.filter fun i => ¬(z i).2 = 1) = univ.filter fun i => (z i).2 = -1 := by
    refine filter_congr fun i _ => ?_
    rcases Int.units_eq_one_or (z i).2 with h | h <;> simp [h, units_ne.symm]
  rw [Finset.prod_ite, prod_const, prod_const, hf]

theorem isSymG_iff_scal {Λ : Type*} [DecidableEq Λ] [Fintype Λ] (F : Grassmann.N Λ) :
    IsSymG F ↔ scal Λ 2 F = F := by
  constructor
  · intro h
    refine ext_coeff fun n z => ?_
    rw [coeff_scal, prod_scal_factor]
    by_cases hk : (univ.filter fun i => (z i).2 = 1).card =
        (univ.filter fun i => (z i).2 = -1).card
    · rw [hk, ← mul_pow, mul_inv_cancel₀ (two_ne_zero), one_pow, one_mul]
    · rw [h n z hk, mul_zero]
  · intro h n z hk
    have h1 := congrArg (fun G => coeff G z) h
    simp only [coeff_scal, prod_scal_factor] at h1
    by_contra hc
    have h2 : (2 : ℂ) ^ (univ.filter fun i => (z i).2 = 1).card *
        2⁻¹ ^ (univ.filter fun i => (z i).2 = -1).card = 1 := by
      have := mul_right_cancel₀ hc (h1.trans (one_mul _).symm)
      exact this
    rw [inv_pow, mul_inv_eq_one₀ (pow_ne_zero _ two_ne_zero)] at h2
    exact hk (Nat.pow_right_injective (le_refl 2) (by exact_mod_cast h2))

/-- The `U(1)`-invariant elements form a subalgebra. -/
def SymS (Λ : Type*) : Subalgebra ℂ (Grassmann.N Λ) := AlgHom.equalizer (scal Λ 2) (AlgHom.id ℂ _)

theorem mem_SymS {Λ : Type*} {F : Grassmann.N Λ} : F ∈ SymS Λ ↔ scal Λ 2 F = F := by
  simp [SymS, AlgHom.mem_equalizer]

/-- The eigenspace of `scal 2` with eigenvalue `c`. -/
def eigS (Λ : Type*) (c : ℂ) : Submodule ℂ (Grassmann.N Λ) :=
  LinearMap.ker ((scal Λ 2).toLinearMap - c • LinearMap.id)

theorem mem_eigS {Λ : Type*} {c : ℂ} {F : Grassmann.N Λ} : F ∈ eigS Λ c ↔ scal Λ 2 F = c • F := by
  simp [eigS, sub_eq_zero]

theorem scal_ψ {Λ : Type*} [DecidableEq Λ] (t : ℂ) (a : Sf Λ) :
    scal Λ t (ψ a) = (if a.2 = 1 then t else t⁻¹) • ψ a := by
  rw [scal, ψ, ExteriorAlgebra.map_apply_ι, ← map_smul]
  congr 1
  funext b
  by_cases h : a.2 = 1 <;> by_cases hb : b = a <;> simp [scalV, ev, h, hb]

theorem psi_mem_eigS (x : Lam d L N) : psi x ∈ eigS (Lam d L N) 2 := by
  rw [mem_eigS, psi, scal_ψ, if_pos rfl]

theorem psibar_mem_eigS (x : Lam d L N) : psibar x ∈ eigS (Lam d L N) 2⁻¹ := by
  rw [mem_eigS, psibar, scal_ψ, if_neg units_ne.symm]

theorem mul_mem_SymS {Λ : Type*} {a b : Grassmann.N Λ} (ha : a ∈ eigS Λ 2) (hb : b ∈ eigS Λ 2⁻¹) :
    a * b ∈ SymS Λ := by
  rw [mem_eigS] at ha hb
  rw [mem_SymS, map_mul, ha, hb, smul_mul_smul_comm, mul_inv_cancel₀ two_ne_zero, one_smul]

theorem isSym_iff_mem_SymS (F : Alg d L N) : IsSym F ↔ F ∈ SymS (Lam d L N) := by
  rw [isSym_iff_isSymG, isSymG_iff_scal, mem_SymS]

theorem grad_mem_eigS (e : Dir d) (x : Lam d L N) : grad e x ∈ eigS (Lam d L N) 2 :=
  sub_mem (psi_mem_eigS _) (psi_mem_eigS _)

theorem gradbar_mem_eigS (e : Dir d) (x : Lam d L N) : gradbar e x ∈ eigS (Lam d L N) 2⁻¹ :=
  sub_mem (psibar_mem_eigS _) (psibar_mem_eigS _)

theorem lapPsi_mem_eigS (x : Lam d L N) : lapPsi x ∈ eigS (Lam d L N) 2 :=
  Submodule.smul_mem _ _ (Submodule.sum_mem _ fun e _ =>
    sub_mem (grad_mem_eigS e _) (grad_mem_eigS e _))

theorem lapPsibar_mem_eigS (x : Lam d L N) : lapPsibar x ∈ eigS (Lam d L N) 2⁻¹ :=
  Submodule.smul_mem _ _ (Submodule.sum_mem _ fun e _ =>
    sub_mem (gradbar_mem_eigS e _) (gradbar_mem_eigS e _))

theorem gradSq_mem_SymS (x : Lam d L N) : gradSq x ∈ SymS (Lam d L N) :=
  Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun e _ =>
    mul_mem_SymS (grad_mem_eigS e x) (gradbar_mem_eigS e x)) _

theorem theta_scal (t : ℂ) (F : Alg d L N) :
    theta (scal _ t F) = scal _ t (theta F) := by
  simp only [theta, scal, map_map_apply]
  refine map_congr_apply (fun v b => ?_) F
  rcases b with ⟨b | b, σ⟩ <;> rfl

theorem incl_scal (t : ℂ) (F : Alg d L N) :
    incl (scal _ t F) = scal _ t (incl F) := by
  simp only [incl, scal, map_map_apply]
  refine map_congr_apply (fun v b => ?_) F
  rcases b with ⟨b | b, σ⟩ <;> by_cases h : σ = 1 <;> simp [inlV, scalV, h]

theorem EC_scal (C : Matrix (Lam d L N) (Lam d L N) ℝ) {t : ℂ} (ht : t ≠ 0) (F : Alg2 d L N) :
    EC C (scal _ t F) = scal _ t (EC C F) := by
  refine EC_comm_of _ _ (fun G => ?_) (fun G => ?_) F
  · have hD : ∀ (a : Sf (Lam d L N ⊕ Lam d L N)) (H : Alg2 d L N),
        D a (scal _ t H) = (if a.2 = 1 then t else t⁻¹) • scal _ t (D a H) := by
      intro a H
      rw [scal, D_map, ← map_smul]
      have : coord a ∘ₗ scalV _ t = (if a.2 = 1 then t else t⁻¹) • coord a := by
        refine LinearMap.ext fun v => ?_
        by_cases h : a.2 = 1 <;> simp [scalV, h]
      rw [this, map_smul, LinearMap.smul_apply]; rfl
    simp only [Lζ_apply, hD, map_sum, map_smul, smul_smul]
    refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
    simp [units_ne.symm, ht]
  · simp only [proj, scal, map_map_apply]
    exact map_congr_apply (fun v b => rfl) G

theorem isSym_LocXY (X Y : Finset (Lam d L N)) (F : Alg d L N) : IsSym (LocXY X Y F) := by
  rw [isSym_iff_mem_SymS]
  refine add_mem (Subalgebra.smul_mem _ (one_mem _) _) (Subalgebra.sum_mem _ fun M _ =>
    Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun x _ => ?_) _)
  rw [monoAt]
  refine Subalgebra.list_sum_mem _ fun F hF => ?_
  obtain ⟨p, _, rfl⟩ := List.mem_map.1 hF
  exact Subalgebra.smul_mem _ (mul_mem_SymS (psi_mem_eigS _) (psibar_mem_eigS _)) _

theorem isSym_eval (V : Vcoup) (X : Finset (Lam d L N)) : IsSym (V.eval X) := by
  rw [isSym_iff_mem_SymS]
  refine Subalgebra.sum_mem _ fun x _ => ?_
  refine add_mem (add_mem (add_mem (Subalgebra.smul_mem _ (gradSq_mem_SymS x) _) ?_) ?_) ?_
  · exact Subalgebra.smul_mem _ (add_mem
      (mul_mem_SymS (neg_mem (lapPsi_mem_eigS x)) (psibar_mem_eigS x))
      (mul_mem_SymS (psi_mem_eigS x) (neg_mem (lapPsibar_mem_eigS x)))) _
  · exact Subalgebra.smul_mem _ (mul_mem_SymS (psi_mem_eigS x) (psibar_mem_eigS x)) _
  · exact Subalgebra.smul_mem _ (mul_mem
      (mul_mem_SymS (psi_mem_eigS x) (psibar_mem_eigS x)) (gradSq_mem_SymS x)) _

/-! ### Locality -/

/-- `𝒩(X ⊔ X) ⊆ 𝒩(Λ ⊔ Λ)`. -/
def NX2 (X : Set (Lam d L N)) : Subalgebra ℂ (Alg2 d L N) := NX (Sum.inl '' X ∪ Sum.inr '' X)

theorem theta_mem_NX2 {X : Set (Lam d L N)} {F : Alg d L N} (hF : F ∈ NX X) :
    theta F ∈ NX2 X := by
  refine algHom_mem_of_mem_NX _ (fun a ha => ?_) hF
  rw [theta_psi]
  exact add_mem (ψ_mem_NX (Or.inl ⟨_, ha, rfl⟩)) (ψ_mem_NX (Or.inr ⟨_, ha, rfl⟩))

theorem incl_mem_NX2 {X : Set (Lam d L N)} {F : Alg d L N} (hF : F ∈ NX X) :
    incl F ∈ NX2 X := by
  refine algHom_mem_of_mem_NX _ (fun a ha => ?_) hF
  rw [incl_psi]
  exact ψ_mem_NX (Or.inl ⟨_, ha, rfl⟩)

theorem EC_mem_NX (C : Matrix (Lam d L N) (Lam d L N) ℝ) {X : Set (Lam d L N)}
    {F : Alg2 d L N} (hF : F ∈ NX2 X) : EC C F ∈ NX X := by
  have hL : ∀ G ∈ NX2 X, Lζ C G ∈ NX2 X := fun G hG => by
    rw [Lζ_apply]
    exact Subalgebra.sum_mem _ fun x _ => Subalgebra.sum_mem _ fun y _ =>
      Subalgebra.smul_mem _ (D_mem_NX (D_mem_NX hG _) _) _
  have hLk : ∀ k, ∀ G ∈ NX2 X, (Lζ C ^ k) G ∈ NX2 X := by
    intro k
    induction k with
    | zero => exact fun G hG => hG
    | succ k ih => intro G hG; rw [pow_succ', Module.End.mul_apply]; exact hL _ (ih G hG)
  obtain ⟨n, hn⟩ := Lζ_isNilpotent C
  have hexp : IsNilpotent.exp (Lζ C) F ∈ NX2 X := by
    rw [IsNilpotent.exp_eq_sum hn, LinearMap.sum_apply]
    refine Subalgebra.sum_mem _ fun k _ => ?_
    rw [LinearMap.smul_apply, ← Rat.cast_smul_eq_qsmul ℂ]
    exact Subalgebra.smul_mem _ (hLk k F hF) _
  rw [EC, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  refine algHom_mem_of_mem_NX _ (fun a ha => ?_) hexp
  rcases a with ⟨b | b, σ⟩
  · have hb : b ∈ X := by simpa using ha
    exact (proj_ψ₁ (b, σ)).symm ▸ ψ_mem_NX hb
  · exact (proj_ζ (b, σ)).symm ▸ zero_mem _

theorem eval_mem_NX (hd : 1 ≤ d) {j : ℕ} {X : Finset (Lam d L N)} (hX : IsPolymer j X)
    (V : Vcoup) : V.eval X ∈ NX (nbhd j X : Set (Lam d L N)) := by
  refine Subalgebra.sum_mem _ fun x hx => ?_
  have hψ : ∀ (y : Lam d L N) (σ : ℤˣ), supNorm (y - x) ≤ 1 →
      ψ (y, σ) ∈ NX (nbhd j X : Set (Lam d L N)) := fun y σ h =>
    ψ_mem_NX (Finset.mem_coe.2 (mem_nbhd_of_near hd hX hx h))
  have h0 : ∀ σ : ℤˣ, ψ (x, σ) ∈ NX (nbhd j X : Set (Lam d L N)) := fun σ =>
    hψ x σ (by rw [sub_self, supNorm_zero]; omega)
  have hp : ∀ (e : Dir d) (σ : ℤˣ), ψ (x + dirVec e, σ) ∈ NX (nbhd j X : Set (Lam d L N)) :=
    fun e σ => hψ _ σ (by rw [add_sub_cancel_left]; exact supNorm_dirVec_le e)
  have hm : ∀ (e : Dir d) (σ : ℤˣ), ψ (x - dirVec e, σ) ∈ NX (nbhd j X : Set (Lam d L N)) :=
    fun e σ => hψ _ σ (by rw [supNorm_sub_comm, sub_sub_cancel]; exact supNorm_dirVec_le e)
  have hg : ∀ e, grad e x ∈ NX (nbhd j X : Set (Lam d L N)) := fun e => sub_mem (hp e 1) (h0 1)
  have hgb : ∀ e, gradbar e x ∈ NX (nbhd j X : Set (Lam d L N)) := fun e =>
    sub_mem (hp e (-1)) (h0 (-1))
  have hg' : ∀ e, grad e (x - dirVec e) ∈ NX (nbhd j X : Set (Lam d L N)) := fun e => by
    rw [grad, sub_add_cancel]; exact sub_mem (h0 1) (hm e 1)
  have hgb' : ∀ e, gradbar e (x - dirVec e) ∈ NX (nbhd j X : Set (Lam d L N)) := fun e => by
    rw [gradbar, sub_add_cancel]; exact sub_mem (h0 (-1)) (hm e (-1))
  have hl : lapPsi x ∈ NX (nbhd j X : Set (Lam d L N)) :=
    Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun e _ => sub_mem (hg' e) (hg e)) _
  have hlb : lapPsibar x ∈ NX (nbhd j X : Set (Lam d L N)) :=
    Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun e _ => sub_mem (hgb' e) (hgb e)) _
  have hs : gradSq x ∈ NX (nbhd j X : Set (Lam d L N)) :=
    Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun e _ => mul_mem (hg e) (hgb e)) _
  have hpp : psi x * psibar x ∈ NX (nbhd j X : Set (Lam d L N)) := mul_mem (h0 1) (h0 (-1))
  refine add_mem (add_mem (add_mem (Subalgebra.smul_mem _ hs _) ?_) ?_) ?_
  · exact Subalgebra.smul_mem _ (add_mem (mul_mem (neg_mem hl) (h0 (-1)))
      (mul_mem (h0 1) (neg_mem hlb))) _
  · exact Subalgebra.smul_mem _ hpp _
  · exact Subalgebra.smul_mem _ (mul_mem hpp hs) _

end

end Step
