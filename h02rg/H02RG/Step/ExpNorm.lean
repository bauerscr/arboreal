import Step.Defs
import Loc.EstBasic

/-!
# Norm estimates for exponentials and products

For the `T` norms (on `𝒩(Λ)` and on the doubled algebra `𝒩(Λ ⊔ Λ)`):

* elements with vanishing constant term are nilpotent (`isNilpotent_of_ε`), so `e^F` is the
  terminating exponential series;
* `‖e^F‖ ≤ e^{‖F‖}`, `‖e^F - 1‖ ≤ e^{‖F‖} - 1`, `‖e^F - 1 - F‖ ≤ e^{‖F‖} - 1 - ‖F‖` (from the
  product property `e:T-product`);
* `‖∏_i F_i‖ ≤ ∏_i ‖F_i‖`, `‖ι F‖ ≤ ‖F‖` for the inclusion `ι : 𝒩(Λ) → 𝒩(Λ ⊔ Λ)`.
-/

namespace Step

noncomputable section

open Finset Grassmann Loc FRD ENNReal

variable {X : Type*} [DecidableEq X] [Fintype X] {E : Type*} [Fintype E] [DecidableEq E]
  [AddAction (E → ℕ) X] {p : ℕ} {h ℓ : ℝ}

/-! ### Nilpotency -/

/-- The span of the products `ι v_1 ⋯ ι v_n` with `n ≥ m`. -/
def SpanGe (X : Type*) (m : ℕ) : Submodule ℂ (Grassmann.N X) :=
  Submodule.span ℂ {x | ∃ n, m ≤ n ∧ ∃ v : Fin n → V X, x = ExteriorAlgebra.ιMulti ℂ n v}

theorem SpanGe_mul (a b : ℕ) : SpanGe X a * SpanGe X b ≤ SpanGe X (a + b) := by
  rw [SpanGe, SpanGe, Submodule.span_mul_span]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, ⟨n, hn, v, rfl⟩, y, ⟨n', hn', w, rfl⟩, rfl⟩
  exact Submodule.subset_span ⟨n + n', by omega, _, ExteriorAlgebra.ιMulti_mul_ιMulti v w⟩

theorem SpanGe_eq_bot {m : ℕ} (hm : Nf X < m) : SpanGe X m = ⊥ := by
  refine Submodule.span_eq_bot.2 ?_
  rintro _ ⟨n, hn, v, rfl⟩
  exact ιMulti_eq_zero_of_lt v (by omega)

theorem coeff_fin_zero (F : Grassmann.N X) (z : Fin 0 → Sf X) : coeff F z = ε F := by
  simp [coeff, Dseq]

theorem mem_SpanGe_one {F : Grassmann.N X} (hF : ε F = 0) : F ∈ SpanGe X 1 := by
  rw [sum_coeff F]
  refine Submodule.sum_mem _ fun n _ => Submodule.sum_mem _ fun z _ => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [coeff_fin_zero, hF, mul_zero, zero_smul]; exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, hn, _, rfl⟩)

theorem pow_mem_SpanGe {F : Grassmann.N X} (hF : F ∈ SpanGe X 1) (k : ℕ) :
    F ^ k ∈ SpanGe X k := by
  induction k with
  | zero =>
    rw [pow_zero]
    exact Submodule.subset_span ⟨0, le_rfl, Fin.elim0,
      (ExteriorAlgebra.ιMulti_zero_apply _).symm⟩
  | succ k ih =>
    rw [pow_succ]
    exact SpanGe_mul k 1 (Submodule.mul_mem_mul ih hF)

theorem pow_eq_zero_of_ε {F : Grassmann.N X} (hF : ε F = 0) {k : ℕ} (hk : Nf X < k) :
    F ^ k = 0 := by
  have := pow_mem_SpanGe (mem_SpanGe_one hF) k
  rwa [SpanGe_eq_bot hk, Submodule.mem_bot] at this

theorem pow_eq_zero_of_ε' {F : EvR X} (hF : ε (F : Grassmann.N X) = 0) {k : ℕ}
    (hk : Nf X < k) : F ^ k = 0 :=
  Subtype.ext (by rw [SubmonoidClass.coe_pow, pow_eq_zero_of_ε hF hk]; rfl)

theorem isNilpotent_of_ε' {F : EvR X} (hF : ε (F : Grassmann.N X) = 0) : IsNilpotent F :=
  ⟨_, pow_eq_zero_of_ε' hF (Nat.lt_succ_self _)⟩

theorem coe_gexp {F : EvR X} {k : ℕ} (hk : F ^ k = 0) :
    (gexp F : Grassmann.N X) = ∑ i ∈ range k, ((i.factorial : ℂ)⁻¹) • (F : Grassmann.N X) ^ i := by
  rw [gexp, IsNilpotent.exp_eq_sum hk, AddSubmonoidClass.coe_finsetSum]
  refine sum_congr rfl fun i _ => ?_
  rw [← SubmonoidClass.coe_pow]
  show ((algebraMap ℚ ℂ (i.factorial : ℚ)⁻¹ • F ^ i : EvR X) : Grassmann.N X) = _
  rw [map_inv₀, map_natCast]
  rfl

theorem ε_gexp {F : EvR X} (hF : ε (F : Grassmann.N X) = 0) :
    ε (gexp F : Grassmann.N X) = 1 := by
  rw [coe_gexp (pow_eq_zero_of_ε' hF (Nat.lt_succ_self _)), map_sum, sum_range_succ']
  simp [hF]

theorem gexp_add {F G : EvR X} (hF : ε (F : Grassmann.N X) = 0) (hG : ε (G : Grassmann.N X) = 0) :
    gexp (F + G) = gexp F * gexp G :=
  IsNilpotent.exp_add_of_commute (Commute.all _ _) (isNilpotent_of_ε' hF) (isNilpotent_of_ε' hG)

theorem gexp_sum_of_ε {ι : Type*} (s : Finset ι) (F : ι → EvR X)
    (hF : ∀ i ∈ s, ε (F i : Grassmann.N X) = 0) : gexp (∑ i ∈ s, F i) = ∏ i ∈ s, gexp (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [gexp, IsNilpotent.exp_zero]
  | insert a s ha ih =>
    rw [sum_insert ha, prod_insert ha, gexp, IsNilpotent.exp_add_of_commute (Commute.all _ _)
      (isNilpotent_of_ε' (hF a (mem_insert_self a s)))
      (isNilpotent_sum fun i hi => isNilpotent_of_ε' (hF i (mem_insert_of_mem hi))),
      ← gexp, ← gexp, ih fun i hi => hF i (mem_insert_of_mem hi)]

theorem gexp_zero : gexp (0 : EvR X) = 1 := IsNilpotent.exp_zero

/-! ### Products -/

theorem tNorm_mul_le' (hh : 0 < h) (hℓ : 0 < ℓ) (F G : EvR X) :
    tNorm E p h ℓ ((F * G : EvR X) : Grassmann.N X) ≤
      tNorm E p h ℓ (F : Grassmann.N X) * tNorm E p h ℓ (G : Grassmann.N X) :=
  tNorm_mul_le hh hℓ _ _

theorem tNorm_prod_le (hh : 0 < h) (hℓ : 0 < ℓ) {ι : Type*} (s : Finset ι) (F : ι → EvR X) :
    tNorm E p h ℓ ((∏ i ∈ s, F i : EvR X) : Grassmann.N X) ≤
      ∏ i ∈ s, tNorm E p h ℓ (F i : Grassmann.N X) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using tNorm_one_le (E := E) (p := p) (X := X) hh hℓ
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha]
    exact (tNorm_mul_le' hh hℓ _ _).trans (mul_le_mul_right ih _)

theorem tNorm_pow_le (hh : 0 < h) (hℓ : 0 < ℓ) (F : Grassmann.N X) (n : ℕ) :
    tNorm E p h ℓ (F ^ n) ≤ tNorm E p h ℓ F ^ n := by
  induction n with
  | zero => simpa using tNorm_one_le (E := E) (p := p) (X := X) hh hℓ
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (tNorm_mul_le hh hℓ _ _).trans (mul_le_mul_left ih _)

theorem tNorm_smul (c : ℂ) (F : Grassmann.N X) :
    tNorm E p h ℓ (c • F) = ENNReal.ofReal ‖c‖ * tNorm E p h ℓ F := by
  refine le_antisymm (tNorm_smul_le c F) ?_
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · have h1 := tNorm_smul_le (E := E) (p := p) (h := h) (ℓ := ℓ) c⁻¹ (c • F)
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul] at h1
    calc ENNReal.ofReal ‖c‖ * tNorm E p h ℓ F
        ≤ ENNReal.ofReal ‖c‖ * (ENNReal.ofReal ‖c⁻¹‖ * tNorm E p h ℓ (c • F)) := by gcongr
      _ = tNorm E p h ℓ (c • F) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (norm_nonneg _), ← norm_mul, mul_inv_cancel₀ hc,
          norm_one, ENNReal.ofReal_one, one_mul]

theorem tNorm_algebraMap_le (hh : 0 < h) (hℓ : 0 < ℓ) (c : ℂ) :
    tNorm E p h ℓ (algebraMap ℂ (Grassmann.N X) c) ≤ ENNReal.ofReal ‖c‖ := by
  rw [Algebra.algebraMap_eq_smul_one, tNorm_smul]
  calc ENNReal.ofReal ‖c‖ * tNorm E p h ℓ (1 : Grassmann.N X) ≤ ENNReal.ofReal ‖c‖ * 1 := by
        gcongr; exact tNorm_one_le hh hℓ
    _ = _ := mul_one _

/-- `|F_∅| ≤ ‖F‖`. -/
theorem abs_ε_le (hh : 0 < h) (hℓ : 0 < ℓ) (F : Grassmann.N X) :
    ENNReal.ofReal ‖ε F‖ ≤ tNorm E p h ℓ F :=
  ENNReal.ofReal_le_of_le_toReal (abs_eps_le hh hℓ F)

/-! ### Exponentials -/

theorem tNorm_sum_smul_pow_le (hh : 0 < h) (hℓ : 0 < ℓ) (G : Grassmann.N X) {r : ℝ} (hr : 0 ≤ r)
    (hG : tNorm E p h ℓ G ≤ ENNReal.ofReal r) (s : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i)
    (f : ℕ → ℕ) :
    tNorm E p h ℓ (∑ i ∈ s, (a i : ℂ) • G ^ f i) ≤ ENNReal.ofReal (∑ i ∈ s, a i * r ^ f i) := by
  refine (tNorm_sum_le _ _).trans ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun i _ => mul_nonneg (ha i) (pow_nonneg hr _)]
  refine sum_le_sum fun i _ => ?_
  refine (tNorm_smul_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_of_nonneg (ha i), ENNReal.ofReal_mul (ha i), ENNReal.ofReal_pow hr]
  gcongr
  exact (tNorm_pow_le hh hℓ G _).trans (by gcongr)

/-- `‖e^F‖ ≤ e^{‖F‖}`. -/
theorem tNorm_gexp_le (hh : 0 < h) (hℓ : 0 < ℓ) {F : EvR X} (hF : ε (F : Grassmann.N X) = 0)
    {r : ℝ} (hr : 0 ≤ r) (hFr : tNorm E p h ℓ (F : Grassmann.N X) ≤ ENNReal.ofReal r) :
    tNorm E p h ℓ (gexp F : Grassmann.N X) ≤ ENNReal.ofReal (Real.exp r) := by
  rw [coe_gexp (pow_eq_zero_of_ε' hF (Nat.lt_succ_self _))]
  have e : ∑ i ∈ range (Nf X + 1), ((i.factorial : ℂ)⁻¹) • (F : Grassmann.N X) ^ i =
      ∑ i ∈ range (Nf X + 1), (((i.factorial : ℝ)⁻¹ : ℝ) : ℂ) • (F : Grassmann.N X) ^ id i := by
    push_cast; rfl
  rw [e]
  refine (tNorm_sum_smul_pow_le hh hℓ _ hr hFr _ (fun i => (i.factorial : ℝ)⁻¹)
    (fun i => by positivity) id).trans ?_
  refine ENNReal.ofReal_le_ofReal ((le_of_eq ?_).trans (Real.sum_le_exp_of_nonneg hr (Nf X + 1)))
  refine sum_congr rfl fun i _ => ?_
  simp [div_eq_inv_mul]

/-- `‖e^F - 1‖ ≤ e^{‖F‖} - 1`. -/
theorem tNorm_gexp_sub_one_le (hh : 0 < h) (hℓ : 0 < ℓ) {F : EvR X}
    (hF : ε (F : Grassmann.N X) = 0) {r : ℝ} (hr : 0 ≤ r)
    (hFr : tNorm E p h ℓ (F : Grassmann.N X) ≤ ENNReal.ofReal r) :
    tNorm E p h ℓ ((gexp F - 1 : EvR X) : Grassmann.N X) ≤ ENNReal.ofReal (Real.exp r - 1) := by
  have e : ((gexp F - 1 : EvR X) : Grassmann.N X) =
      ∑ i ∈ range (Nf X + 1), ((((i + 1).factorial : ℝ)⁻¹ : ℝ) : ℂ) • (F : Grassmann.N X) ^ (i + 1) := by
    rw [AddSubgroupClass.coe_sub, coe_gexp (pow_eq_zero_of_ε' hF (by omega : Nf X < Nf X + 2)),
      sum_range_succ']
    simp
  rw [e]
  refine (tNorm_sum_smul_pow_le hh hℓ _ hr hFr _ _ (fun i => by positivity) _).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hs := Real.sum_le_exp_of_nonneg hr (Nf X + 2)
  rw [sum_range_succ'] at hs
  simp only [div_eq_inv_mul, pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one,
    mul_one] at hs
  linarith

/-- `‖e^F - 1 - F‖ ≤ e^{‖F‖} - 1 - ‖F‖`. -/
theorem tNorm_gexp_sub_one_sub_le (hh : 0 < h) (hℓ : 0 < ℓ) {F : EvR X}
    (hF : ε (F : Grassmann.N X) = 0) {r : ℝ} (hr : 0 ≤ r)
    (hFr : tNorm E p h ℓ (F : Grassmann.N X) ≤ ENNReal.ofReal r) :
    tNorm E p h ℓ ((gexp F - 1 - F : EvR X) : Grassmann.N X) ≤
      ENNReal.ofReal (Real.exp r - 1 - r) := by
  have e : ((gexp F - 1 - F : EvR X) : Grassmann.N X) =
      ∑ i ∈ range (Nf X), ((((i + 2).factorial : ℝ)⁻¹ : ℝ) : ℂ) • (F : Grassmann.N X) ^ (i + 2) := by
    rw [AddSubgroupClass.coe_sub, AddSubgroupClass.coe_sub,
      coe_gexp (pow_eq_zero_of_ε' hF (by omega : Nf X < Nf X + 2)), sum_range_succ',
      sum_range_succ']
    simp
  rw [e]
  refine (tNorm_sum_smul_pow_le hh hℓ _ hr hFr _ _ (fun i => by positivity) _).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hs := Real.sum_le_exp_of_nonneg hr (Nf X + 2)
  rw [sum_range_succ', sum_range_succ'] at hs
  simp only [div_eq_inv_mul, pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one,
    mul_one, zero_add, pow_one, Nat.factorial_one] at hs
  linarith

/-- The elementary bounds used with the previous lemmas. -/
theorem exp_sub_one_sub_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : Real.exp r - 1 - r ≤ r ^ 2 :=
  (le_abs_self _).trans (Real.abs_exp_sub_one_sub_id_le (by rwa [abs_of_nonneg hr0]))

theorem exp_sub_one_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : Real.exp r - 1 ≤ 2 * r := by
  have := exp_sub_one_sub_le hr0 hr1
  nlinarith

/-! ### The inclusion -/

/-- `(x, σ) ↦ (x, σ)` in the first copy. -/
def inlS (a : Sf X) : Sf (X ⊕ X) := (Sum.inl a.1, a.2)

theorem inlS_injective : Function.Injective (inlS (X := X)) := by
  rintro ⟨x, σ⟩ ⟨y, τ⟩ hxy
  simp only [inlS, Prod.mk.injEq, Sum.inl.injEq] at hxy
  rw [hxy.1, hxy.2]

theorem coeff_incl (F : Grassmann.N X) {n : ℕ} (w : Fin n → Sf X) :
    coeff (incl F) (inlS ∘ w) = coeff F w := by
  induction F using induction_ιMulti with
  | hzero => simp
  | hadd F G hF hG => rw [map_add, coeff_add, coeff_add, hF, hG]
  | hsmul r F hF => rw [map_smul, coeff_smul, coeff_smul, hF]
  | hι m v =>
    rw [incl, ExteriorAlgebra.map_apply_ιMulti]
    by_cases hm : n = m
    · subst hm
      rw [coeff_ιMulti, coeff_ιMulti]
      rfl
    · rw [coeff_ιMulti_of_ne _ _ hm, coeff_ιMulti_of_ne _ _ hm]

theorem coeff_incl_of_inr (F : Grassmann.N X) {n : ℕ} (z : Fin n → Sf (X ⊕ X)) {i : Fin n}
    {y : X} (hy : (z i).1 = Sum.inr y) : coeff (incl F) z = 0 := by
  induction F using induction_ιMulti with
  | hzero => simp
  | hadd F G hF hG => rw [map_add, coeff_add, hF, hG, add_zero]
  | hsmul r F hF => rw [map_smul, coeff_smul, hF, mul_zero]
  | hι m v =>
    rw [incl, ExteriorAlgebra.map_apply_ιMulti]
    by_cases hm : n = m
    · subst hm
      rw [coeff_ιMulti]
      refine Matrix.det_eq_zero_of_row_eq_zero i fun j => ?_
      simp [inlV, hy]
    · rw [coeff_ιMulti_of_ne _ _ hm]

theorem pair_eq_sum_range (F : Grassmann.N X) (g : TestFn X) {K : ℕ} (hK : Nf X ≤ K) :
    pair F g = ∑ n ∈ range (K + 1), (n.factorial : ℂ)⁻¹ *
      ∑ z : Fin n → Sf X, coeff F z * g n z := by
  unfold pair
  refine sum_subset (range_subset_range.2 (by omega)) fun n _ hn => ?_
  rw [mem_range, not_lt] at hn
  rw [sum_eq_zero fun z _ => by rw [coeff_eq_zero_of_lt F z (by omega), zero_mul], mul_zero]

theorem pair_incl (F : Grassmann.N X) (g : TestFn (X ⊕ X)) :
    pair (incl F) g = pair F (fun n w => g n (inlS ∘ w)) := by
  have hK : Nf X ≤ Nf (X ⊕ X) := by
    simp only [Nf, Fintype.card_prod, Fintype.card_sum]
    exact Nat.mul_le_mul_right _ (by omega)
  rw [pair_eq_sum_range F _ hK, pair]
  refine sum_congr rfl fun n _ => ?_
  congr 1
  symm
  refine Fintype.sum_of_injective (fun w => inlS ∘ w) ?_ _ _ ?_ fun w => by rw [coeff_incl]
  · intro w w' hw
    funext i
    exact inlS_injective (congrFun hw i)
  · intro z hz
    have : ∃ i, ∃ y, (z i).1 = Sum.inr y := by
      by_contra hc
      push Not at hc
      refine hz ⟨fun i => ((z i).1.elim id id, (z i).2), funext fun i => ?_⟩
      show inlS _ = z i
      rcases hzi : z i with ⟨x | y, σ⟩
      · simp [inlS, hzi]
      · exact absurd (by rw [hzi]) (hc i y)
    obtain ⟨i, y, hy⟩ := this
    rw [coeff_incl_of_inr F z hy, zero_mul]

theorem phiNorm_comp_inlS_le (g : TestFn (X ⊕ X)) :
    phiNorm E p h ℓ (fun n w => g n (inlS ∘ w)) ≤ phiNorm E p h ℓ g := by
  refine iSup_le fun n => iSup_le fun z => iSup_le fun α => iSup_le fun hα => ?_
  refine le_trans (le_of_eq ?_) (phiTerm_le g (inlS ∘ z) α hα)
  unfold phiTerm
  rw [nabla_comp_equivariant (sh (X := X)) (sh (X := X ⊕ X)) inlS
    (fun b y => by simp [inlS, sh]) α (g n) z]

/-- The inclusion `𝒩(Λ) ⊆ 𝒩(Λ ⊔ Λ)` does not increase the norm (for the doubled `T` norm with
the action of `E → ℕ` on both copies). -/
theorem tNorm_incl_le (hh : 0 < h) (hℓ : 0 < ℓ) (F : Grassmann.N X) :
    tNorm E p h ℓ (incl F) ≤ tNorm E p h ℓ F := by
  refine iSup₂_le fun g hg => ?_
  rw [pair_incl]
  exact le_tNorm F ((phiNorm_comp_inlS_le g).trans hg)

end

end Step
