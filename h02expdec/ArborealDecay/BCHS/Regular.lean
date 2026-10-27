module

public import ArborealDecay.Super.DimRedSymm
public import ArborealDecay.Horo.Schwartz
public import ArborealDecay.Horo.ShiftFun
public import ArborealDecay.Super.ComposeComp

/-!
# Schwartz regularity of the `ℍ^{2|4}` integrand

For the horospherical change of variables (`ArborealDecay.Horo.integral_berezin_horo_H24`) the
`ℍ^{2|4}` integrand `∏ z_i⁻¹ · F e^{-H_{β,h}}` must be Schwartz (every coefficient a Mathlib
Schwartz function).  We prove this when `β ≥ 0`, `h ≥ 0`, `Pinned β h`, and every coefficient of
`F` has temperate growth (`STG F`; e.g. `F = 1`, `F = y_i y_j`).

* `STG F`: every coordinate `ℓ ∘ F` has temperate growth (Mathlib `Function.HasTemperateGrowth`).
  Closed under sums, products, constants, multiplication by temperate scalars, and composition
  with `g` whose Taylor coefficients `p ↦ g^{(k)}(body (S p))` have temperate growth.
* `zH`, `Ring.inverse zH`, `dotH`, `actionH`, `exp (soul (-actionH))` are `STG`.
* `exists_schwartz_exp_neg`: `e^{-Φ}` is a Schwartz function if `Φ ≥ 0` has temperate growth and
  `1 + ‖p‖ ≤ C (1 + Φ p)^M` (pointwise Faà di Bruno bound `norm_iteratedFDeriv_comp_le`).
* `sschwartz_integrandF`: the integrand is `SSchwartz`.

Also: square-root uniqueness for even elements with positive body (`eq_of_sq_eq_of_body_pos`) and
`zH_mul_self : z_i z_i = R_i`.
-/

@[expose] public section

namespace ArborealDecay.BCHS

noncomputable section

open MeasureTheory Finset Real ArborealDecay.Super ArborealDecay.Super.H24 SchwartzMap Function
open scoped ContDiff Nat

set_option linter.unusedSectionVars false

/-! ### Square roots of even elements -/

section Sqrt

variable {O : Type*} [Fintype O] [DecidableEq O]

/-- **Square-root uniqueness**: even elements with positive body and equal squares are equal. -/
theorem eq_of_sq_eq_of_body_pos {a b : Gr O} (ha : IsEven a) (hb : IsEven b) (hpa : 0 < body a)
    (hpb : 0 < body b) (h : a * a = b * b) : a = b := by
  have hab : IsEven (a + b) := ha.add hb
  have hbody : body (a + b) ≠ 0 := by rw [map_add]; linarith
  have hinv := mul_scomp_inv (isNilpotent_soul hab) hbody
  have h0 : (a - b) * (a + b) = 0 := by
    have hc : a * b = b * a := ha.comm b
    rw [sub_mul, mul_add, mul_add, h, hc]; abel
  have e : a - b = 0 := by
    calc a - b = (a - b) * ((a + b) * scomp (fun t : ℝ => t⁻¹) (a + b)) := by
          rw [hinv, mul_one]
      _ = 0 := by rw [← mul_assoc, h0, zero_mul]
  exact sub_eq_zero.1 e

theorem iteratedDeriv_id_add_two (k : ℕ) (s : ℝ) :
    iteratedDeriv (k + 2) (fun t : ℝ => t) s = 0 := by
  rw [iteratedDeriv_succ', iteratedDeriv_succ']
  have h1 : deriv (fun t : ℝ => t) = fun _ => 1 := deriv_id''
  have h2 : deriv (fun _ : ℝ => (1 : ℝ)) = fun _ => 0 := funext fun _ => deriv_const _ _
  rw [h1, h2]
  simp

/-- `id(a) = a`. -/
theorem scomp_id {a : Gr O} (ha : IsEven a) : scomp (fun t : ℝ => t) a = a := by
  rw [scomp_eq_jet_card _ ha (Nat.le_succ _ : Fintype.card O + 1 ≤
    Fintype.card O + 2), jet, Finset.sum_range_succ', Finset.sum_range_succ']
  rw [Finset.sum_eq_zero fun k _ => by rw [iteratedDeriv_id_add_two, zero_div, zero_smul]]
  simp [iteratedDeriv_one, deriv_id'', soul, Algebra.algebraMap_eq_smul_one]

end Sqrt

/-- `z_i z_i = R_i`. -/
theorem zH_mul_self {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (i : Λ) (p : Pt Λ) :
    zH i p * zH i p = Rz i p := by
  have hpos := body_Rz_pos i p
  have hN := isNilpotent_soul (isEven_Rz i p)
  have hs : ContDiffAt ℝ (⊤ : ℕ∞) Real.sqrt (body (Rz i p)) :=
    (Real.contDiffAt_sqrt hpos.ne').of_le le_top
  rw [zH, ← scomp_mul_fun hN hs hs]
  have he : (fun t => Real.sqrt t * Real.sqrt t) =ᶠ[nhds (body (Rz i p))] fun t => t := by
    filter_upwards [lt_mem_nhds hpos] with t ht
    exact Real.mul_self_sqrt ht.le
  rw [scomp_congr he, scomp_id (isEven_Rz i p)]

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ### Temperate-growth superfunctions -/

/-- Every coordinate has temperate growth. -/
def STG {A : Type*} [AddCommGroup A] [Module ℝ A] (F : Pt Λ → A) : Prop :=
  ∀ ℓ : Module.Dual ℝ A, (fun p => ℓ (F p)).HasTemperateGrowth

section Module

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

theorem STG.const (c : A) : STG (Λ := Λ) fun _ => c := fun _ => HasTemperateGrowth.const _

theorem STG.add {F G : Pt Λ → A} (hF : STG F) (hG : STG G) : STG fun p => F p + G p :=
  fun ℓ => by
    have := (hF ℓ).add (hG ℓ)
    convert this using 1; funext p; simp

theorem STG.neg {F : Pt Λ → A} (hF : STG F) : STG fun p => -F p := fun ℓ => by
  have := (hF ℓ).neg
  convert this using 1; funext p; simp

theorem STG.sub {F G : Pt Λ → A} (hF : STG F) (hG : STG G) : STG fun p => F p - G p := by
  simpa [sub_eq_add_neg] using hF.add hG.neg

theorem STG.smul {F : Pt Λ → A} (hF : STG F) {g : Pt Λ → ℝ} (hg : g.HasTemperateGrowth) :
    STG fun p => g p • F p := fun ℓ => by
  have := hg.mul (hF ℓ)
  convert this using 1; funext p; simp

theorem STG.const_smul {F : Pt Λ → A} (hF : STG F) (c : ℝ) : STG fun p => c • F p :=
  hF.smul (HasTemperateGrowth.const c)

theorem STG.sum {ι : Type*} (s : Finset ι) {F : ι → Pt Λ → A} (hF : ∀ i ∈ s, STG (F i)) :
    STG fun p => ∑ i ∈ s, F i p := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using STG.const (Λ := Λ) (0 : A)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hF a (mem_insert_self a s)).add (ih fun i hi => hF i (mem_insert_of_mem hi))

theorem STG.map {B : Type*} [AddCommGroup B] [Module ℝ B] {F : Pt Λ → A} (hF : STG F)
    (L : A →ₗ[ℝ] B) : STG fun p => L (F p) := fun ℓ => hF (ℓ ∘ₗ L)

end Module

section Alg

variable {A : Type*} [Ring A] [Algebra ℝ A] [FiniteDimensional ℝ A]

theorem STG.mul {F G : Pt Λ → A} (hF : STG F) (hG : STG G) : STG fun p => F p * G p :=
  fun ℓ => by
    have e : (fun p => ℓ (F p * G p)) =
        fun p => ∑ m, crd m (F p) * (ℓ ∘ₗ LinearMap.mulLeft ℝ (fb A m)) (G p) := by
      funext p; rw [dual_mul_eq_sum]; rfl
    rw [e]
    have := HasTemperateGrowth.sum (s := Finset.univ)
      (f := fun m p => crd m (F p) * (ℓ ∘ₗ LinearMap.mulLeft ℝ (fb A m)) (G p))
      fun m _ => (hF (crd m)).mul (hG _)
    convert this using 1

theorem STG.pow {F : Pt Λ → A} (hF : STG F) (k : ℕ) : STG fun p => F p ^ k := by
  induction k with
  | zero => simpa using STG.const (Λ := Λ) (1 : A)
  | succ k ih => simpa [pow_succ] using ih.mul hF

theorem STG.list_prod {ι : Type*} (l : List ι) {F : ι → Pt Λ → A} (hF : ∀ i ∈ l, STG (F i)) :
    STG fun p => (l.map fun i => F i p).prod := by
  induction l with
  | nil => simpa using STG.const (Λ := Λ) (1 : A)
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (hF i List.mem_cons_self).mul (ih fun j hj => hF j (List.mem_cons_of_mem _ hj))

end Alg

section Comp

variable {O : Type*} [Fintype O] [DecidableEq O]

theorem STG.body {S : Pt Λ → Gr O} (hS : STG S) :
    (fun p => Super.body (S p)).HasTemperateGrowth :=
  hS Super.body.toLinearMap

theorem STG.soulF {S : Pt Λ → Gr O} (hS : STG S) : STG (Super.soulF S) :=
  hS.sub ((STG.const 1).smul hS.body)

/-- Composition preserves `STG`, given temperate Taylor coefficients. -/
theorem STG.scomp {g : ℝ → ℝ} {S : Pt Λ → Gr O} (hS : STG S) (hE : ∀ p, IsEven (S p))
    (hg : ∀ k, (fun p => iteratedDeriv k g (Super.body (S p))).HasTemperateGrowth) :
    STG fun p => Super.scomp g (S p) := by
  rw [scomp_fun_eq hE le_rfl]
  refine STG.sum _ fun k _ => (hS.soulF.pow k).smul ?_
  have := (hg k).mul (HasTemperateGrowth.const ((k.factorial : ℝ)⁻¹))
  convert this using 1; funext p; simp [bodyF, div_eq_mul_inv]

theorem STG.scomp_exp_soul {S : Pt Λ → Gr O} (hS : STG S) (hE : ∀ p, IsEven (S p)) :
    STG fun p => Super.scomp Real.exp (soul (S p)) := by
  have e : (fun p => soul (S p)) = Super.soulF S := funext fun p => (soulF_eq S p).symm
  rw [show (fun p => Super.scomp Real.exp (soul (S p))) =
    fun p => Super.scomp Real.exp (Super.soulF S p) from by rw [← e]]
  refine hS.soulF.scomp (fun p => by rw [soulF_eq]; exact (hE p).soul) fun k => ?_
  simp only [soulF_eq, body_soul, iteratedDeriv_exp, Real.exp_zero]
  exact HasTemperateGrowth.const 1

end Comp

/-! ### The `ℍ^{2|4}` building blocks -/

theorem rr_eq_norm (i : Λ) (p : Pt Λ) : rr i p = 1 + ‖Horo.pairL i p‖ ^ 2 := by
  rw [Horo.norm_pairL_sq, rr, add_assoc]

theorem hasTemperateGrowth_rr_rpow (i : Λ) (r : ℝ) :
    (fun p : Pt Λ => rr i p ^ r).HasTemperateGrowth := by
  have := (hasTemperateGrowth_one_add_norm_sq_rpow (EuclideanSpace ℝ (Fin 2)) r).comp
    (Horo.pairL i).hasTemperateGrowth
  convert this using 1; funext p; simp [rr_eq_norm]

theorem hasTemperateGrowth_rr (i : Λ) : (rr i : Pt Λ → ℝ).HasTemperateGrowth := by
  convert hasTemperateGrowth_rr_rpow i 1 using 1; funext p; simp

theorem stg_Rz (i : Λ) : STG (Rz i) := by
  have := ((STG.const (Λ := Λ) (1 : A Λ)).smul (hasTemperateGrowth_rr i)).sub
    (STG.const (Λ := Λ) ((2 : ℝ) • (ξ1 i * η1 i))) |>.sub
    (STG.const (Λ := Λ) ((2 : ℝ) • (ξ i * η i)))
  convert this using 1; funext p; rfl

theorem stg_zH (i : Λ) : STG (zH i) :=
  (stg_Rz i).scomp (isEven_Rz i) fun k => by
    simp only [body_Rz]
    have := (HasTemperateGrowth.const ((descPochhammer ℝ k).eval (1 / 2 : ℝ))).mul
      (hasTemperateGrowth_rr_rpow i ((1 / 2 : ℝ) - k))
    convert this using 1; funext p; rw [iteratedDeriv_sqrt]; rfl

theorem stg_zinv (i : Λ) : STG fun p => Ring.inverse (zH i p) := by
  simp_rw [inverse_zH]
  refine (stg_zH i).scomp (isEven_zH i) fun k => ?_
  have := (HasTemperateGrowth.const ((-1 : ℝ) ^ k * k.factorial)).mul
    ((Horo.hasTemperateGrowth_zOf_inv i).pow (k + 1))
  convert this using 1; funext p
  simp only [body_zH, iteratedDeriv_inv, Pi.mul_apply, Pi.pow_apply, inv_pow]
  rfl

theorem stg_zinvProd : STG (zinvProd : Pt Λ → A Λ) :=
  STG.list_prod _ fun i _ => stg_zinv i

theorem hasTemperateGrowth_quad (a b c d : Λ ⊕ Λ) :
    (fun p : Pt Λ => p a * p b + p c * p d).HasTemperateGrowth := by
  have := ((Horo.hasTemperateGrowth_coord a).mul (Horo.hasTemperateGrowth_coord b)).add
    ((Horo.hasTemperateGrowth_coord c).mul (Horo.hasTemperateGrowth_coord d))
  convert this using 1

theorem stg_dotH (i j : Λ) : STG (dotH i j) := by
  have := ((((STG.const (Λ := Λ) (1 : A Λ)).smul (hasTemperateGrowth_quad (.inl i) (.inl j)
    (.inr i) (.inr j))).add (STG.const (η1 i * ξ1 j - ξ1 i * η1 j))).add
    (STG.const (η i * ξ j - ξ i * η j))).sub ((stg_zH i).mul (stg_zH j))
  convert this using 1; funext p; rfl

theorem stg_actionH (β : Λ → Λ → ℝ) (h : Λ → ℝ) : STG (actionH β h) := by
  refine (STG.const_smul (STG.sum _ fun i _ => STG.sum _ fun j _ => ?_) _).add
    (STG.sum _ fun i _ => ((stg_zH i).sub (STG.const 1)).const_smul _)
  exact ((((stg_dotH i i).sub (stg_dotH i j)).sub (stg_dotH j i)).add
    (stg_dotH j j)).const_smul _

theorem stg_one : STG (fun _ : Pt Λ => (1 : A Λ)) := STG.const 1

theorem stg_Fyy (i j : Λ) : STG (Fyy i j : Pt Λ → A Λ) := by
  have := (STG.const (Λ := Λ) (1 : A Λ)).smul
    ((Horo.hasTemperateGrowth_coord (.inr i)).mul (Horo.hasTemperateGrowth_coord (.inr j)))
  convert this using 1; funext p; rfl

/-! ### `e^{-Φ}` is a Schwartz function -/

section Schwartz

variable {E : Type*} [Fintype E]

theorem norm_iteratedFDeriv_exp (i : ℕ) (u : ℝ) : ‖iteratedFDeriv ℝ i Real.exp u‖ = Real.exp u := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_exp, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos u)]

/-- `e^{-Φ}` is a Schwartz function if `Φ ≥ 0` has temperate growth and `1 + ‖x‖` is dominated by
a power of `1 + Φ`. -/
theorem exists_schwartz_exp_neg {Φ : (E → ℝ) → ℝ} (hΦ : Φ.HasTemperateGrowth)
    (h0 : ∀ x, 0 ≤ Φ x) {C : ℝ} {M : ℕ} (hdom : ∀ x, 1 + ‖x‖ ≤ C * (1 + Φ x) ^ M) :
    ∃ f : 𝓢(E → ℝ, ℝ), ∀ x, f x = Real.exp (-Φ x) := by
  have hC : 0 ≤ C := by
    have h := hdom 0
    have : 0 < (1 + Φ 0) ^ M := pow_pos (by linarith [h0 0]) M
    by_contra hneg
    have hneg' : C < 0 := not_le.mp hneg
    nlinarith [norm_nonneg (0 : E → ℝ)]
  have hneg : (fun x => -Φ x).HasTemperateGrowth := hΦ.neg
  refine ⟨{ toFun := fun x => Real.exp (-Φ x)
            smooth' := Real.contDiff_exp.comp hneg.1
            decay' := fun k n => ?_ }, fun _ => rfl⟩
  obtain ⟨kΦ, CΦ, hCΦ, hb⟩ := hneg.norm_iteratedFDeriv_le_uniform n
  set L := k + kΦ * n
  refine ⟨n ! * (1 + CΦ) ^ n * (C ^ L * ((M * L).factorial * Real.exp 1)), fun x => ?_⟩
  set D := (1 + CΦ) * (1 + ‖x‖) ^ kΦ
  have hx1 : (1 : ℝ) ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  have hD1 : 1 ≤ D := one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ hx1)
  have hderiv : ‖iteratedFDeriv ℝ n (Real.exp ∘ fun x => -Φ x) x‖ ≤
      n ! * Real.exp (-Φ x) * D ^ n := by
    refine norm_iteratedFDeriv_comp_le Real.contDiff_exp hneg.1 (by exact_mod_cast le_top) x
      (fun i _ => (norm_iteratedFDeriv_exp i _).le) fun i hi hin => ?_
    calc ‖iteratedFDeriv ℝ i (fun x => -Φ x) x‖ ≤ CΦ * (1 + ‖x‖) ^ kΦ := hb i hin x
      _ ≤ D := by
          have hy : 0 ≤ (1 + ‖x‖) ^ kΦ := by positivity
          simp only [D]; nlinarith
      _ ≤ D ^ i := le_self_pow₀ hD1 (by omega)
  have hΦx := h0 x
  have hf : (0 : ℝ) < (M * L).factorial := by exact_mod_cast Nat.factorial_pos _
  have h1 : (1 + Φ x) ^ (M * L) / (M * L).factorial ≤ Real.exp (1 + Φ x) :=
    Real.pow_div_factorial_le_exp _ (by linarith) _
  rw [div_le_iff₀ hf] at h1
  have h2 : (1 + ‖x‖) ^ L ≤ C ^ L * (1 + Φ x) ^ (M * L) := by
    calc (1 + ‖x‖) ^ L ≤ (C * (1 + Φ x) ^ M) ^ L :=
          pow_le_pow_left₀ (by positivity) (hdom x) L
      _ = C ^ L * (1 + Φ x) ^ (M * L) := by rw [mul_pow, ← pow_mul]
  have h3 : (1 + ‖x‖) ^ L * Real.exp (-Φ x) ≤ C ^ L * ((M * L).factorial * Real.exp 1) := by
    calc (1 + ‖x‖) ^ L * Real.exp (-Φ x)
        ≤ (C ^ L * (1 + Φ x) ^ (M * L)) * Real.exp (-Φ x) := by gcongr
      _ ≤ (C ^ L * (Real.exp (1 + Φ x) * (M * L).factorial)) * Real.exp (-Φ x) := by gcongr
      _ = C ^ L * ((M * L).factorial * Real.exp 1) := by
          rw [show Real.exp (1 + Φ x) = Real.exp 1 * Real.exp (Φ x) from Real.exp_add _ _]
          have := Real.exp_neg (Φ x)
          field_simp
          rw [this]; field_simp
  have hxk : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := pow_le_pow_left₀ (norm_nonneg x) (by linarith) k
  have hDn : D ^ n = (1 + CΦ) ^ n * (1 + ‖x‖) ^ (kΦ * n) := by rw [mul_pow, ← pow_mul]
  change ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (Real.exp ∘ fun x => -Φ x) x‖ ≤ _
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (Real.exp ∘ fun x => -Φ x) x‖
      ≤ (1 + ‖x‖) ^ k * (n ! * Real.exp (-Φ x) * D ^ n) := by gcongr
    _ = n ! * (1 + CΦ) ^ n * ((1 + ‖x‖) ^ L * Real.exp (-Φ x)) := by
        rw [hDn, pow_add]; ring
    _ ≤ _ := by gcongr

end Schwartz

/-! ### The integrand -/

/-- **Schwartz regularity of the `ℍ^{2|4}` integrand** under `Pinned`, for `F` with temperate
coefficients. -/
theorem sschwartz_integrandF {β : Λ → Λ → ℝ} (hβ : ∀ i j, 0 ≤ β i j) {h : Λ → ℝ}
    (hh : ∀ i, 0 ≤ h i) (hP : Pinned β h) {F : Pt Λ → A Λ} (hF : STG F) :
    ArborealDecay.Horo.SSchwartz (integrandF β h F) := by
  obtain ⟨C, M, hdom⟩ := norm_dom hβ hh hP
  obtain ⟨ψ, hψ⟩ := exists_schwartz_exp_neg (stg_actionH β h).body
    (body_actionH_nonneg hβ hh) hdom
  have hG : STG fun p => zinvProd p * (F p * Super.scomp Real.exp (soul (-actionH β h p))) :=
    stg_zinvProd.mul (hF.mul ((stg_actionH β h).neg.scomp_exp_soul
      fun p => (isEven_actionH β h p).neg))
  intro ℓ
  refine ⟨smulLeftCLM ℝ (fun p => ℓ (zinvProd p *
    (F p * Super.scomp Real.exp (soul (-actionH β h p))))) ψ, fun p => ?_⟩
  rw [smulLeftCLM_apply_apply (hG ℓ), hψ, integrandF_eq, map_smul, smul_eq_mul, smul_eq_mul,
    mul_comm]

end

end ArborealDecay.BCHS

end
