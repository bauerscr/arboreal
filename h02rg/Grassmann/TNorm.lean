import Grassmann.Norms

/-!
# Properties of the `T_j(ℓ)` norm

* `tNorm_ne_top`: the norm is finite;
* `abs_pair_le`: `‖⟨F, g⟩‖ ≤ ‖F‖_T ‖g‖_Φ`;
* `tNorm_mono` (`e:T-monotone`): `‖F‖_{T(h', ℓ)} ≤ ‖F‖_{T(h, ℓ')}` for `h ≤ h'`, `ℓ ≤ ℓ'`;
* `tNorm_mul_le` (`e:T-product`): `‖F_1 F_2‖_T ≤ ‖F_1‖_T ‖F_2‖_T`.
-/

namespace Grassmann

noncomputable section

open Finset Equiv ENNReal

variable {X : Type*} [DecidableEq X] [Fintype X] {E : Type*} [Fintype E] [DecidableEq E]
  [AddAction (E → ℕ) X] {p : ℕ} {h ℓ : ℝ}

theorem le_tNorm (F : N X) {g : TestFn X} (hg : phiNorm E p h ℓ g ≤ 1) :
    ENNReal.ofReal ‖pair F g‖ ≤ tNorm E p h ℓ F :=
  le_iSup₂_of_le g hg le_rfl

theorem tNorm_le {F : N X} {A : ℝ} (hF : ∀ g : TestFn X, phiNorm E p h ℓ g ≤ 1 → ‖pair F g‖ ≤ A) :
    tNorm E p h ℓ F ≤ ENNReal.ofReal A :=
  iSup₂_le fun g hg => ENNReal.ofReal_le_ofReal (hF g hg)

/-- The `T` norm is finite. -/
theorem tNorm_ne_top (hh : 0 < h) (hℓ : 0 < ℓ) (F : N X) : tNorm E p h ℓ F ≠ ⊤ := by
  refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top (tNorm_le (A := ∑ n ∈ range (Nf X + 1),
    (n.factorial : ℝ)⁻¹ * ∑ z : Fin n → Sf X, ‖coeff F z‖ * ℓ ^ n) fun g hg => ?_)
  refine (norm_sum_le _ _).trans (sum_le_sum fun n _ => ?_)
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  gcongr
  refine (norm_sum_le _ _).trans (sum_le_sum fun z _ => ?_)
  rw [norm_mul]
  gcongr
  simpa using abs_le_of_phiNorm_le hh hℓ zero_le_one (by rwa [ENNReal.ofReal_one]) (g := g) z

/-- `‖⟨F, g⟩‖ ≤ ‖F‖_T M` whenever `‖g‖_Φ ≤ M`. -/
theorem abs_pair_le (hh : 0 < h) (hℓ : 0 < ℓ) (F : N X) {g : TestFn X} {M : ℝ} (hM : 0 ≤ M)
    (hg : phiNorm E p h ℓ g ≤ ENNReal.ofReal M) :
    ‖pair F g‖ ≤ (tNorm E p h ℓ F).toReal * M := by
  rcases hM.eq_or_lt with hM0 | hM0
  · subst hM0
    have hg0 : g = 0 := by
      ext n z
      exact phiNorm_eq_zero hh hℓ (le_antisymm (by simpa using hg) bot_le) n z
    simp [hg0, pair]
  · have hg' : phiNorm E p h ℓ (((M⁻¹ : ℝ) : ℂ) • g) ≤ 1 := by
      rw [phiNorm_smul hh.le hℓ, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hM0]
      calc ENNReal.ofReal M⁻¹ * phiNorm E p h ℓ g ≤ ENNReal.ofReal M⁻¹ * ENNReal.ofReal M := by
            gcongr
        _ = 1 := by rw [← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ hM0.ne',
            ENNReal.ofReal_one]
    have := le_tNorm F hg'
    rw [← ENNReal.ofReal_toReal (tNorm_ne_top hh hℓ F), ENNReal.ofReal_le_ofReal_iff
      ENNReal.toReal_nonneg, pair_smul_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_inv, abs_of_pos hM0] at this
    rwa [inv_mul_le_iff₀ hM0, mul_comm] at this

/-- Monotonicity `e:T-monotone`: for `h ≤ h'` and `ℓ ≤ ℓ'`,
`‖F‖_{T(h', ℓ)} ≤ ‖F‖_{T(h, ℓ')}`.  With `h = L^j`, `h' = L^{j+1}` this gives both
`‖F‖_{T_j(ℓ)} ≤ ‖F‖_{T_j(ℓ')}` and `‖F‖_{T_{j+1}(ℓ)} ≤ ‖F‖_{T_j(ℓ')}`. -/
theorem tNorm_mono {h' ℓ' : ℝ} (hh : 0 ≤ h) (hhh : h ≤ h') (hℓ : 0 < ℓ) (hℓℓ : ℓ ≤ ℓ')
    (F : N X) : tNorm E p h' ℓ F ≤ tNorm E p h ℓ' F := by
  refine iSup₂_le fun g hg => le_iSup₂_of_le g (le_trans ?_ hg) le_rfl
  refine iSup_le fun n => iSup_le fun z => iSup_le fun α => iSup_le fun hα => ?_
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (phiTerm_le g z α hα)
  have hℓ' : 0 < ℓ' := hℓ.trans_le hℓℓ
  unfold phiTerm
  gcongr

/-! ### The product property -/

theorem psiPow_mul_psiPow {m n : ℕ} (z : Fin m → Sf X) (w : Fin n → Sf X) :
    psiPow z * psiPow w = psiPow (Fin.append z w) := by
  rw [psiPow, psiPow, ExteriorAlgebra.ιMulti_mul_ιMulti, psiPow]
  congr 1; ext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp

theorem append_eq_sumElim {α : Type*} {m n : ℕ} (a : Fin m → α) (b : Fin n → α) :
    Fin.append a b = Sum.elim a b ∘ finSumFinEquiv.symm := by
  ext i; refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp

/-- `∇^{α_2}_{z_2} ∇^{α_1}_{z_1} f(z_1 z_2) = ∇^{α_1 α_2} f (z_1 z_2)` for concatenations. -/
theorem nab_append {W : Type*} [AddCommGroup W] [Module ℝ W] {n₁ n₂ : ℕ}
    (α₁ : Fin n₁ → E → ℕ) (α₂ : Fin n₂ → E → ℕ) (f : (Fin (n₁ + n₂) → Sf X) → W)
    (z₁ : Fin n₁ → Sf X) (z₂ : Fin n₂ → Sf X) :
    nab α₂ (fun w₂ => nab α₁ (fun w₁ => f (Fin.append w₁ w₂)) z₁) z₂ =
      nab (Fin.append α₁ α₂) f (Fin.append z₁ z₂) := by
  have h1 := nabla_reindex (sh (X := X)) finSumFinEquiv (Fin.append α₁ α₂) f (Fin.append z₁ z₂)
  rw [← h1, nabla_sumElim]
  have hα : Fin.append α₁ α₂ ∘ finSumFinEquiv = Sum.elim α₁ α₂ := by
    rw [append_eq_sumElim, Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]
  have hz : Fin.append z₁ z₂ ∘ finSumFinEquiv = Sum.elim z₁ z₂ := by
    rw [append_eq_sumElim, Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]
  simp only [hα, hz, Sum.elim_comp_inl, Sum.elim_comp_inr]
  simp only [append_eq_sumElim]

theorem ord_append {n₁ n₂ : ℕ} (α₁ : Fin n₁ → E → ℕ) (α₂ : Fin n₂ → E → ℕ) :
    ord (Fin.append α₁ α₂) = ord α₁ + ord α₂ := by
  simp [ord, Fin.sum_univ_add]

/-- The product property `e:T-product`: `‖F_1 F_2‖_{T} ≤ ‖F_1‖_{T} ‖F_2‖_{T}`. -/
theorem tNorm_mul_le (hh : 0 < h) (hℓ : 0 < ℓ) (F₁ F₂ : N X) :
    tNorm E p h ℓ (F₁ * F₂) ≤ tNorm E p h ℓ F₁ * tNorm E p h ℓ F₂ := by
  set A₁ := (tNorm E p h ℓ F₁).toReal
  set A₂ := (tNorm E p h ℓ F₂).toReal
  rw [← ENNReal.ofReal_toReal (tNorm_ne_top hh hℓ F₁),
    ← ENNReal.ofReal_toReal (tNorm_ne_top hh hℓ F₂), ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  refine tNorm_le fun g hg => ?_
  set R := range (Nf X + 1)
  have hAg : phiNorm E p h ℓ (asym g) ≤ ENNReal.ofReal 1 := by
    rw [ENNReal.ofReal_one]; exact (phiNorm_asym_le hh.le hℓ g).trans hg
  -- the test functions `z_2 ↦ (A g)(z_1 z_2)`
  let Gs : ∀ {n₁ : ℕ}, (Fin n₁ → Sf X) → TestFn X := fun {n₁} z₁ n₂ z₂ =>
    asym g (n₁ + n₂) (Fin.append z₁ z₂)
  let G : TestFn X := fun n₁ z₁ => pair F₂ (Gs z₁)
  have hpair : pair (F₁ * F₂) g = pair F₁ G := by
    conv_lhs => rw [sum_coeff F₁, sum_coeff F₂]
    simp_rw [sum_mul]
    simp_rw [mul_sum]
    simp only [smul_mul_smul, psiPow_mul_psiPow, pair_sum, pair_smul, pair_psiPow]
    simp only [pair, G, Gs, mul_sum]
    refine sum_congr rfl fun n₁ _ => sum_congr rfl fun z₁ _ => sum_congr rfl fun n₂ _ =>
      sum_congr rfl fun z₂ _ => ?_
    ring
  -- `‖G‖_Φ ≤ ‖F_2‖_T`
  have hG : phiNorm E p h ℓ G ≤ ENNReal.ofReal A₂ := by
    refine phiNorm_le fun n₁ z₁ α₁ hα₁ => ?_
    let K : TestFn X := fun n₂ z₂ => nab α₁ (fun w₁ => Gs w₁ n₂ z₂) z₁
    have hK : nab α₁ (G n₁) z₁ = pair F₂ K := by
      have e1 := nabla_comp_linear (sh (X := X)) α₁ ((pairR F₂).restrictScalars ℝ)
        (fun w₁ => Gs w₁) z₁
      have e2 : nab α₁ (fun w₁ => Gs w₁) z₁ = K := by
        ext n₂ z₂
        have := nabla_comp_linear (sh (X := X)) α₁
          ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin n₂ → Sf X => ℂ) z₂) ∘ₗ
            (LinearMap.proj (R := ℝ) (φ := fun n : ℕ => (Fin n → Sf X) → ℂ) n₂))
          (fun w₁ => Gs w₁) z₁
        exact this.symm
      rw [e2] at e1
      exact e1
    have hKb : phiNorm E p h ℓ K ≤ ENNReal.ofReal (ℓ ^ n₁ * (h ^ ord α₁)⁻¹) := by
      refine phiNorm_le fun n₂ z₂ α₂ hα₂ => ?_
      have hnab : nab α₂ (K n₂) z₂ =
          nab (Fin.append α₁ α₂) (asym g (n₁ + n₂)) (Fin.append z₁ z₂) :=
        nab_append α₁ α₂ (asym g (n₁ + n₂)) z₁ z₂
      have hb := abs_nab_le hh hℓ zero_le_one hAg (Fin.append z₁ z₂) (Fin.append α₁ α₂)
        (fun i => Fin.addCases (fun i => by simpa using hα₁ i) (fun i => by simpa using hα₂ i) i)
      unfold phiTerm
      rw [hnab]
      rw [ord_append, one_mul] at hb
      calc ℓ⁻¹ ^ n₂ * h ^ ord α₂ * ‖nab (Fin.append α₁ α₂) (asym g (n₁ + n₂)) (Fin.append z₁ z₂)‖
          ≤ ℓ⁻¹ ^ n₂ * h ^ ord α₂ * (ℓ ^ (n₁ + n₂) * (h ^ (ord α₁ + ord α₂))⁻¹) := by gcongr
        _ = ℓ ^ n₁ * (h ^ ord α₁)⁻¹ := by
            rw [pow_add, pow_add, inv_pow]
            field_simp
    have := abs_pair_le hh hℓ F₂ (by positivity) hKb
    unfold phiTerm
    rw [hK]
    calc ℓ⁻¹ ^ n₁ * h ^ ord α₁ * ‖pair F₂ K‖ ≤ ℓ⁻¹ ^ n₁ * h ^ ord α₁ *
          (A₂ * (ℓ ^ n₁ * (h ^ ord α₁)⁻¹)) := by gcongr
      _ = A₂ := by
          rw [inv_pow]
          field_simp
  rw [hpair]
  exact abs_pair_le hh hℓ F₁ ENNReal.toReal_nonneg hG

end

end Grassmann
