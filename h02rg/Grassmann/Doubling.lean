import Grassmann.TNorm
import Grassmann.Gaussian

/-!
# The doubling map (`e:theta-bd`)

`‖θ F‖_{T_j(ℓ ⊔ ℓ)} ≤ ‖F‖_{T_j(2ℓ)}`, where the norm on the doubled algebra `𝒩(Λ ⊔ Λ)` is the
`T` norm for the sites `Λ ⊕ Λ` (with the translations acting on both copies).
-/

namespace Grassmann

noncomputable section

open CliffordAlgebra ExteriorAlgebra Finset

section Map

variable {M M' : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M']

theorem contr_map (f : M →ₗ[ℂ] M') {m : ℕ} (φ : Fin m → Module.Dual ℂ M')
    (x : ExteriorAlgebra ℂ M) :
    contr φ (ExteriorAlgebra.map f x) = ExteriorAlgebra.map f (contr (fun i => φ i ∘ₗ f) x) := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih => rw [contr_succ, contractLeft_map, ih, contr_succ]; rfl

theorem algebraMapInv_map (f : M →ₗ[ℂ] M') (x : ExteriorAlgebra ℂ M) :
    algebraMapInv (ExteriorAlgebra.map f x) = algebraMapInv x := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι m => simp [ExteriorAlgebra.map_apply_ι]
  | mul a b ha hb => rw [map_mul, map_mul, map_mul, ha, hb]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

end Map

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ] {E : Type*} [Fintype E] [DecidableEq E]
  [AddAction (E → ℕ) Λ]

/-- Forgetting the copy: `Λ_f ⊔ Λ_f → Λ_f`. -/
def prf (a : Sf (Λ ⊕ Λ)) : Sf Λ := (Sum.elim id id a.1, a.2)

/-- `(x, σ) ↦ (x, σ)` in the first (`false`) or second (`true`) copy. -/
def liftf (c : Bool) (a : Sf Λ) : Sf (Λ ⊕ Λ) := (if c then Sum.inr a.1 else Sum.inl a.1, a.2)

@[simp] theorem prf_liftf (c : Bool) (a : Sf Λ) : prf (liftf c a) = a := by
  cases c <;> rfl

theorem coord_thetaV (b : Sf (Λ ⊕ Λ)) : coord b ∘ₗ thetaV = coord (prf b) := by
  ext v; simp [thetaV, prf]

/-- `(θ F)_w = F_{w'}`, where `w'` forgets the copies. -/
theorem coeff_theta (F : N Λ) {n : ℕ} (w : Fin n → Sf (Λ ⊕ Λ)) :
    coeff (theta F) w = coeff F (fun i => prf (w i)) := by
  rw [coeff, Dseq, theta, contr_map, algebraMapInv_map]
  simp only [coord_thetaV]; rfl

theorem sh_liftf (c : Bool) (b : E → ℕ) (a : Sf Λ) : sh b (liftf c a) = liftf c (sh b a) := by
  cases c <;> simp [sh, liftf]

/-- The test function `g'_z = ∑_{w ↦ z} g_w` on `Λ_f^*`. -/
def liftT (g : TestFn (Λ ⊕ Λ)) : TestFn Λ := fun n z =>
  ∑ c : Fin n → Bool, g n fun i => liftf (c i) (z i)

/-- `(z, c) ↦ w` is a bijection `Λ_f^n × Bool^n ≃ (Λ_f ⊔ Λ_f)^n`. -/
def liftEquiv (n : ℕ) : (Fin n → Sf Λ) × (Fin n → Bool) ≃ (Fin n → Sf (Λ ⊕ Λ)) where
  toFun p i := liftf (p.2 i) (p.1 i)
  invFun w := (fun i => prf (w i), fun i => (w i).1.isRight)
  left_inv p := by
    refine Prod.ext (funext fun i => prf_liftf _ _) (funext fun i => ?_)
    cases h : p.2 i <;> simp [liftf, h]
  right_inv w := by
    ext i
    · rcases hw : w i with ⟨x | x, σ⟩ <;> simp [liftf, prf, hw]
    · rfl

theorem pair_theta (F : N Λ) (g : TestFn (Λ ⊕ Λ)) : pair (theta F) g = pair F (liftT g) := by
  unfold pair
  have hsub : range (Nf Λ + 1) ⊆ range (Nf (Λ ⊕ Λ) + 1) := by
    intro n hn
    simp only [mem_range] at hn ⊢
    have : Nf Λ ≤ Nf (Λ ⊕ Λ) := by simp [Nf, Fintype.card_sum]
    omega
  rw [← sum_subset hsub]
  · refine sum_congr rfl fun n _ => ?_
    congr 1
    simp_rw [coeff_theta]
    rw [← Fintype.sum_equiv (liftEquiv n) (fun p => coeff F (fun i => prf (liftEquiv n p i)) *
      g n (liftEquiv n p)) _ (fun _ => rfl), Fintype.sum_prod_type]
    simp only [liftEquiv, Equiv.coe_fn_mk, prf_liftf, liftT, mul_sum]
  · intro n _ hn
    simp only [mem_range, not_lt] at hn
    rw [sum_eq_zero fun w _ => by rw [coeff_theta, coeff_eq_zero_of_lt _ _ (by omega), zero_mul],
      mul_zero]

variable {p : ℕ} {h ℓ : ℝ}

theorem phiNorm_liftT_le (hh : 0 < h) (hℓ : 0 < ℓ) (g : TestFn (Λ ⊕ Λ)) {M : ℝ} (hM : 0 ≤ M)
    (hg : phiNorm E p h ℓ g ≤ ENNReal.ofReal M) :
    phiNorm E p h (2 * ℓ) (liftT g) ≤ ENNReal.ofReal M := by
  refine phiNorm_le fun n z α hα => ?_
  have hnab : nab α (liftT g n) z =
      ∑ c : Fin n → Bool, nab α (g n) (fun i => liftf (c i) (z i)) := by
    unfold liftT
    rw [nabla_sum]
    refine sum_congr rfl fun c _ => ?_
    exact nabla_comp_pi (sh (X := Λ) (E := E)) (sh (X := Λ ⊕ Λ) (E := E)) (fun i => liftf (c i))
      (fun i b a => (sh_liftf (c i) b a).symm) α (g n) z
  unfold phiTerm
  rw [hnab]
  calc (2 * ℓ)⁻¹ ^ n * h ^ ord α * ‖∑ c : Fin n → Bool, nab α (g n) fun i => liftf (c i) (z i)‖
      ≤ (2 * ℓ)⁻¹ ^ n * h ^ ord α * ∑ _c : Fin n → Bool, M * ℓ ^ n * (h ^ ord α)⁻¹ := by
        gcongr
        refine (norm_sum_le _ _).trans (sum_le_sum fun c _ => ?_)
        exact abs_nab_le hh hℓ hM hg _ α hα
    _ = M := by
        rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
          nsmul_eq_mul]
        have hl : ℓ ^ n ≠ 0 := by positivity
        have hh' : h ^ ord α ≠ 0 := by positivity
        have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
        rw [inv_pow, mul_pow]
        push_cast
        field_simp

/-- `e:theta-bd`: `‖θ F‖_{T(ℓ ⊔ ℓ)} ≤ ‖F‖_{T(2ℓ)}`. -/
theorem tNorm_theta_le (hh : 0 < h) (hℓ : 0 < ℓ) (F : N Λ) :
    tNorm E p h ℓ (theta F) ≤ tNorm E p h (2 * ℓ) F := by
  rw [← ENNReal.ofReal_toReal (tNorm_ne_top hh (by positivity) F)]
  refine tNorm_le fun g hg => ?_
  rw [pair_theta]
  have := abs_pair_le hh (by positivity) F zero_le_one
    (phiNorm_liftT_le hh hℓ g zero_le_one (by rwa [ENNReal.ofReal_one]))
  rwa [mul_one] at this

end

end Grassmann
