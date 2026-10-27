import Flow.Embed

/-!
# Grassmann algebra maps induced by injections of the index sets

For an injective map `f : α → β`, `pushA f : 𝒩(α) → 𝒩(β)`, `ψ_a ↦ ψ_{f a}`.  It commutes with
`θ`, the inclusion, `ζ ↦ 0` and derivatives, preserves coefficients, and intertwines `𝔼_C` with
`𝔼_{C'}` for a covariance `C'` which is `C` transported by `f` (`EC_pushA`).  Moreover `𝔼_C`
only depends on `C` restricted to the support (`EC_restr`).  `embA = pushA emb`.
-/

namespace Flow

noncomputable section

open Finset Grassmann Loc FRD Step

section Push

variable {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β] (f : α → β)

/-- The map on generators induced by `f`. -/
def pushV : V α →ₗ[ℂ] V β where
  toFun v b := ∑ a : Sf α, if (f a.1, a.2) = b then v a else 0
  map_add' v w := by ext b; simp [← sum_add_distrib, ite_add_zero]
  map_smul' c v := by ext b; simp [mul_sum]

/-- The algebra map induced by `f`. -/
def pushA : N α →ₐ[ℂ] N β := ExteriorAlgebra.map (pushV f)

variable {f}

theorem pushV_apply (v : V α) (b : Sf β) :
    pushV f v b = ∑ a : Sf α, if (f a.1, a.2) = b then v a else 0 := rfl

theorem pushV_ev' (a : Sf α) : pushV f (ev a) = ev (f a.1, a.2) := by
  ext b
  rw [pushV_apply, Finset.sum_eq_single a]
  · simp only [ev, Pi.single_apply]
    by_cases h : (f a.1, a.2) = b
    · simp [h]
    · simp [h, Ne.symm h]
  · intro a' _ ha'
    simp [ev, ha']
  · simp

theorem pushV_ev (_hf : Function.Injective f) (a : Sf α) : pushV f (ev a) = ev (f a.1, a.2) :=
  pushV_ev' a

theorem pushA_ψ (hf : Function.Injective f) (a : Sf α) : pushA f (ψ a) = ψ (f a.1, a.2) := by
  rw [pushA, ψ, ExteriorAlgebra.map_apply_ι, pushV_ev hf]; rfl

theorem coord_pushV (hf : Function.Injective f) (a : Sf α) :
    coord (f a.1, a.2) ∘ₗ pushV f = coord a := by
  ext v
  simp only [LinearMap.comp_apply, LinearMap.coe_proj, Function.eval, pushV_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro a' _ ha'
    rw [if_neg]
    intro h
    apply ha'
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    exact Prod.ext (hf h1) h2
  · simp

theorem coord_pushV_of_not {b : Sf β} (hb : ∀ x, f x ≠ b.1) : coord b ∘ₗ pushV f = 0 := by
  ext v
  simp only [LinearMap.comp_apply, LinearMap.coe_proj, Function.eval, pushV_apply,
    LinearMap.zero_apply]
  refine Finset.sum_eq_zero fun a _ => if_neg fun h => hb a.1 (congrArg Prod.fst h)

theorem D_pushA (hf : Function.Injective f) (a : Sf α) (G : N α) :
    D (f a.1, a.2) (pushA f G) = pushA f (D a G) := by
  rw [D, pushA, contractLeft_map]
  have := coord_pushV hf a
  simp only [coord] at this
  rw [this]; rfl

theorem D_pushA_of_not {b : Sf β} (hb : ∀ x, f x ≠ b.1) (G : N α) : D b (pushA f G) = 0 := by
  rw [D, pushA, contractLeft_map]
  have := coord_pushV_of_not (f := f) hb
  simp only [coord] at this
  rw [this]; simp

theorem ε_pushA (G : N α) : ε (pushA f G) = ε G := algebraMapInv_map _ G

theorem coeff_pushA (hf : Function.Injective f) (G : N α) {n : ℕ} (z : Fin n → Sf α) :
    coeff (pushA f G) (fun i => (f (z i).1, (z i).2)) = coeff G z := by
  rw [coeff, Dseq, pushA, contr_map, algebraMapInv_map]
  simp only [coord_pushV hf]; rfl

theorem pushA_mem_NX (hf : Function.Injective f) {X : Set α} {G : N α} (hG : G ∈ NX X) :
    pushA f G ∈ NX (f '' X) := by
  refine algHom_mem_of_mem_NX _ (fun a ha => ?_) hG
  rw [pushA_ψ hf]
  exact ψ_mem_NX ⟨a.1, ha, rfl⟩

end Push

/-- Algebra maps out of `𝒩(α)` agreeing on the generators are equal. -/
theorem algHom_ext_ψ {α : Type*} [Fintype α] [DecidableEq α] {A : Type*} [Semiring A]
    [Algebra ℂ A] {Φ Ψ : N α →ₐ[ℂ] A} (h : ∀ a, Φ (ψ a) = Ψ (ψ a)) : Φ = Ψ := by
  apply ExteriorAlgebra.hom_ext
  refine LinearMap.pi_ext fun a c => ?_
  have e : (Pi.single a c : V α) = c • ev a := by
    ext b; simp [ev, Pi.single_apply]
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, e, map_smul]
  exact congrArg (c • ·) (h a)

/-- Algebra maps agreeing on the generators of `𝒩(X)` agree on `𝒩(X)`. -/
theorem algHom_eqOn_NX {α : Type*} [DecidableEq α] {A : Type*} [Semiring A] [Algebra ℂ A]
    {Φ Ψ : N α →ₐ[ℂ] A} {X : Set α} (h : ∀ a : Sf α, a.1 ∈ X → Φ (ψ a) = Ψ (ψ a)) {F : N α}
    (hF : F ∈ NX X) : Φ F = Ψ F := by
  induction hF using Algebra.adjoin_induction with
  | mem x hx => obtain ⟨⟨a, ha⟩, rfl⟩ := hx; exact h a ha
  | algebraMap r => rw [AlgHom.commutes, AlgHom.commutes]
  | add x y _ _ hx hy => rw [_root_.map_add, _root_.map_add, hx, hy]
  | mul x y _ _ hx hy => rw [_root_.map_mul, _root_.map_mul, hx, hy]

section PushDoubled

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {f : α → β}
  (hf : Function.Injective f)
include hf

theorem sumMap_injective : Function.Injective (Sum.map f f) := Sum.map_injective.2 ⟨hf, hf⟩

theorem theta_pushA (F : N α) : theta (pushA f F) = pushA (Sum.map f f) (theta F) := by
  have : theta.comp (pushA f) = (pushA (Sum.map f f)).comp (theta : N α →ₐ[ℂ] N (α ⊕ α)) := by
    refine algHom_ext_ψ fun a => ?_
    simp only [AlgHom.comp_apply, pushA_ψ hf, theta_psi, _root_.map_add]
    rw [show (ψ₁ a : N (α ⊕ α)) = ψ (Sum.inl a.1, a.2) from rfl,
      show (ζ a : N (α ⊕ α)) = ψ (Sum.inr a.1, a.2) from rfl,
      pushA_ψ (sumMap_injective hf), pushA_ψ (sumMap_injective hf)]
    rfl
  exact congrArg (fun Φ : N α →ₐ[ℂ] N (β ⊕ β) => Φ F) this

theorem incl_pushA (F : N α) : incl (pushA f F) = pushA (Sum.map f f) (incl F) := by
  have : incl.comp (pushA f) = (pushA (Sum.map f f)).comp (incl : N α →ₐ[ℂ] N (α ⊕ α)) := by
    refine algHom_ext_ψ fun a => ?_
    simp only [AlgHom.comp_apply, pushA_ψ hf, incl_psi]
    rw [show (ψ₁ a : N (α ⊕ α)) = ψ (Sum.inl a.1, a.2) from rfl, pushA_ψ (sumMap_injective hf)]
    rfl
  exact congrArg (fun Φ : N α →ₐ[ℂ] N (β ⊕ β) => Φ F) this

theorem proj_pushA (G : N (α ⊕ α)) : proj (pushA (Sum.map f f) G) = pushA f (proj G) := by
  have : proj.comp (pushA (Sum.map f f)) = (pushA f).comp (proj : N (α ⊕ α) →ₐ[ℂ] N α) := by
    refine algHom_ext_ψ fun a => ?_
    obtain ⟨x | x, σ⟩ := a
    · simp only [AlgHom.comp_apply, pushA_ψ (sumMap_injective hf), Sum.map_inl]
      rw [show (ψ (Sum.inl (f x), σ) : N (β ⊕ β)) = ψ₁ (f x, σ) from rfl, proj_ψ₁,
        show (ψ (Sum.inl x, σ) : N (α ⊕ α)) = ψ₁ (x, σ) from rfl, proj_ψ₁, pushA_ψ hf]
    · simp only [AlgHom.comp_apply, pushA_ψ (sumMap_injective hf), Sum.map_inr]
      rw [show (ψ (Sum.inr (f x), σ) : N (β ⊕ β)) = ζ (f x, σ) from rfl, proj_ζ,
        show (ψ (Sum.inr x, σ) : N (α ⊕ α)) = ζ (x, σ) from rfl, proj_ζ, _root_.map_zero]
  exact congrArg (fun Φ : N (α ⊕ α) →ₐ[ℂ] N β => Φ G) this

/-- `𝔼_{C'} ∘ f = f ∘ 𝔼_C` if `C'` is `C` transported by `f` (and vanishes off the image). -/
theorem EC_pushA {C : Matrix α α ℝ} {C' : Matrix β β ℝ} (hC : ∀ x y, C' (f x) (f y) = C x y)
    (hC0 : ∀ x' y', (∀ x, f x ≠ x') ∨ (∀ y, f y ≠ y') → C' x' y' = 0) (G : N (α ⊕ α)) :
    EC C' (pushA (Sum.map f f) G) = pushA f (EC C G) := by
  have hf2 := sumMap_injective hf
  set g : N (α ⊕ α) →ₗ[ℂ] N (β ⊕ β) := (pushA (Sum.map f f)).toLinearMap
  have hc : Lζ C' ∘ₗ g = g ∘ₗ Lζ C := by
    refine LinearMap.ext fun H => ?_
    simp only [LinearMap.comp_apply, g, AlgHom.toLinearMap_apply, Lζ_apply, map_sum, map_smul]
    refine Eq.symm (Fintype.sum_of_injective f hf _ _ (fun x' hx' => ?_) (fun x => ?_))
    · refine Finset.sum_eq_zero fun y' _ => ?_
      rw [hC0 x' y' (Or.inl fun x hx => hx' ⟨x, hx⟩), Complex.ofReal_zero, zero_smul]
    · refine Fintype.sum_of_injective f hf _ _ (fun y' hy' => ?_) (fun y => ?_)
      · rw [hC0 _ y' (Or.inr fun y hy => hy' ⟨y, hy⟩), Complex.ofReal_zero, zero_smul]
      · rw [hC x y]
        congr 1
        rw [show ((Sum.inr (f x), (-1 : ℤˣ)) : Sf (β ⊕ β)) =
            (Sum.map f f (Sum.inr x, (-1 : ℤˣ)).1, (Sum.inr x, (-1 : ℤˣ)).2) from rfl,
          D_pushA hf2,
          show ((Sum.inr (f y), (1 : ℤˣ)) : Sf (β ⊕ β)) =
            (Sum.map f f (Sum.inr y, (1 : ℤˣ)).1, (Sum.inr y, (1 : ℤˣ)).2) from rfl,
          D_pushA hf2]
  have h := Module.End.commute_exp_left_of_commute (Lζ_isNilpotent C) (Lζ_isNilpotent C') hc
  have h2 := LinearMap.congr_fun h G
  simp only [LinearMap.comp_apply, g, AlgHom.toLinearMap_apply] at h2
  rw [EC, EC]
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [h2, proj_pushA hf]

end PushDoubled

/-! ### `𝔼_C` depends only on `C` restricted to the support -/

section Restr

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- `𝒩(X ⊔ X)`. -/
abbrev NXd (X : Set Λ) : Subalgebra ℂ (N (Λ ⊕ Λ)) :=
  NX (Sum.inl '' X ∪ Sum.inr '' X : Set (Λ ⊕ Λ))

theorem Lζ_restr (C : Matrix Λ Λ ℝ) {X : Set Λ} {G : N (Λ ⊕ Λ)} (hG : G ∈ NXd X) :
    Lζ C G = Lζ (restr C X) G := by
  classical
  rw [Lζ_apply, Lζ_apply]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  by_cases hx : x ∈ X
  · by_cases hy : y ∈ X
    · simp [restr, hx, hy]
    · rw [D_eq_zero_of_mem_NX (D_mem_NX hG _) (a := (Sum.inr y, 1)) (by
        rintro (⟨z, -, hz⟩ | ⟨z, hz, e⟩)
        · exact Sum.inl_ne_inr hz
        · exact hy (Sum.inr_injective e ▸ hz)), smul_zero, smul_zero]
  · rw [D_eq_zero_of_mem_NX hG (a := (Sum.inr x, -1)) (by
      rintro (⟨z, -, hz⟩ | ⟨z, hz, e⟩)
      · exact Sum.inl_ne_inr hz
      · exact hx (Sum.inr_injective e ▸ hz)), _root_.map_zero, smul_zero, smul_zero]

theorem Lζ_mem (C : Matrix Λ Λ ℝ) {X : Set Λ} {G : N (Λ ⊕ Λ)} (hG : G ∈ NXd X) :
    Lζ C G ∈ NXd X := by
  rw [Lζ_apply]
  exact Subalgebra.sum_mem _ fun x _ => Subalgebra.sum_mem _ fun y _ =>
    Subalgebra.smul_mem _ (D_mem_NX (D_mem_NX hG _) _) _

theorem EC_restr (C : Matrix Λ Λ ℝ) {X : Set Λ} {G : N (Λ ⊕ Λ)} (hG : G ∈ NXd X) :
    EC C G = EC (restr C X) G := by
  have hk : ∀ k, (Lζ C ^ k) G = (Lζ (restr C X) ^ k) G ∧ (Lζ C ^ k) G ∈ NXd X := by
    intro k
    induction k with
    | zero => exact ⟨rfl, hG⟩
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih.1]
      exact ⟨Lζ_restr C ih.2, Lζ_mem C ih.2⟩
  obtain ⟨n, hn⟩ := Lζ_isNilpotent C
  obtain ⟨n', hn'⟩ := Lζ_isNilpotent (restr C X)
  rw [EC, EC, LinearMap.comp_apply, LinearMap.comp_apply,
    IsNilpotent.exp_eq_sum (k := max n n') (pow_eq_zero_of_le (le_max_left _ _) hn),
    IsNilpotent.exp_eq_sum (k := max n n') (pow_eq_zero_of_le (le_max_right _ _) hn')]
  congr 1
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, (hk _).1]

end Restr

end

end Flow
