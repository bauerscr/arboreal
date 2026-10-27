import Obs.Ops

/-!
# Norms with observables (`e:Tphi-obs`, `e:ellsigma`)

For weights `w = (ℓ_a, ℓ_b, ℓ_ab)` (`Wt`) and a bulk norm `‖·‖` on `𝒩(X)`,
`oNorm ‖·‖ w F = ‖F_∅‖ + ℓ_a ‖F_a‖ + ℓ_b ‖F_b‖ + ℓ_ab ‖F_ab‖` (`e:Tphi-obs`).  `oT E p h ℓ w`
is this with the `T(h, ℓ)` norm; `oTj d L j ℓ w` with the `T_j(ℓ)` norm.

## The weights (`e:ellsigma`)
`obsWt c ℓ ℓ'` has `ℓ_a = ℓ_b = ℓ^{-p}` (`p = 1, 2`) and `ℓ_ab = ℓ^{-2}` (Case (1)) resp.
`ℓ^{-2} ℓ'^{-2}` (Case (2)).  The extra parameter `ℓ'` is `ℓ_{j ∧ j_ab}`: `wj c d L ℓ₀ jab j` is
`obsWt c ℓ_j ℓ_{j ∧ j_ab}` with `ℓ_j = ellj d L ℓ₀ j` and `j ∧ j_ab = jwedge j jab`, where the
coalescence scale `jab : ℕ∞` is `coal L a b = ⌊log_L (2 |a - b|_∞)⌋` (`E:coal`, `Nat.log`) for
two source points, and `⊤` (the convention `j_ab = ∞`) if only one source field is present.
`normj c ℓ₀ jab j F = ‖F‖_{T_j(ℓ_j)}` is the norm of the text.

**Convention (deviation).**  The weights `ℓ_{a,j}, ℓ_{b,j}, ℓ_{ab,j}` are attached to the
*scale* `j`, not to the parameter `ℓ` of `T_j(ℓ)`: `‖F‖_{T_{j+1}(2ℓ_{j+1})}` means
`‖F_∅‖_{T_{j+1}(2ℓ_{j+1})} + ℓ_{a,j+1} ‖F_a‖_{T_{j+1}(2ℓ_{j+1})} + …`.  This is the reading
under which the first inequality of `e:Tphi-obs-ub` holds.

## Properties
* `oT_add_le`, `oT_smul`, `oT_neg`, `oT_sum_le`, `oT_one_le`, `oT_ofN`, `oT_sa_mul_ofN`, …;
* the product property `oT_mul_le` for even elements, under `ℓ_ab ≤ ℓ_a ℓ_b` (`Wt.Sub`); for
  `obsWt` this is automatic in Case (1) and needs `ℓ ≤ ℓ'` in Case (2) (`obsWt_sub`), which
  holds for `wj` (`wj_sub`, as `ℓ_j ≤ ℓ_{j ∧ j_ab}`);
* `oT_theta_le` (`‖θF‖_{T(ℓ)} ≤ ‖F‖_{T(2ℓ)}`), `oT_incl_le`, `oT_EC_le` (`𝔼_C` is a
  contraction), `oT_EC_theta_le`, `oT_mono`;
* `normj_succ_le` (`e:Tphi-obs-ub`):
  `‖F‖_{T_{j+1}(ℓ_{j+1})} ≤ ‖F‖_{T_{j+1}(2ℓ_{j+1})} ≤ L^{2(d-2)} ‖F‖_{T_j(ℓ_j)}`, which
  is sharper than the constant `16 L^{2(d-2)}` of the text (`normj_succ_le_16`).
  **What fails:** the monotonicity `‖F‖_{T_{j+1}(2ℓ_{j+1})} ≤ ‖F‖_{T_j(ℓ_j)}` of the bulk
  (`Tj_succ_le`) fails as soon as `F^obs ≠ 0`, because the weights grow:
  `ℓ_{a,j+1} = L^{p(d-2)/2} ℓ_{a,j}` (`wj_succ_a`), and `ℓ_{ab,j+1} = L^{d-2} ℓ_{ab,j}`
  (Case (1), and Case (2) for `j ≥ j_ab`) resp. `L^{2(d-2)} ℓ_{ab,j}` (Case (2), `j + 1 ≤ j_ab`)
  (`wj_succ_ab_*`); e.g. `‖σ_a‖_{T_{j+1}} = ℓ_{a,j+1} > ℓ_{a,j} = ‖σ_a‖_{T_j}`.
* the marginal monomials (`e:a-marginal`, `e:ab-marginal`): `‖σ_a ψ̄_a‖ = ℓ_a ℓ = 1`
  (Case (1)), `‖σ_a ψ̄_a ψ_a‖ ≤ ℓ_a ℓ² = 1` (Case (2)), `‖σ_a σ̄_b ψ̄_x ψ_x‖ ≤ ℓ_ab ℓ² = 1`
  (Case (1)) and `‖σ_a σ_b ψ̄_x ψ_x‖ ≤ ℓ_ab ℓ² = ℓ'^{-2}` (Case (2)); only the upper bounds for
  the quadratic monomials are proved (the product property);
* exponentials: `oT_oexp_le` (`‖e^F‖ ≤ e^{‖F‖}`), `oT_oexp_sub_one_le`,
  `oT_oexp_sub_one_sub_le`, for even `F` with `ε(F_∅) = 0`.
-/

namespace Obs

noncomputable section

open Finset Grassmann ENNReal SA

/-- Weights `(ℓ_a, ℓ_b, ℓ_ab)`. -/
structure Wt where
  /-- `ℓ_a`. -/
  a : ℝ≥0∞
  /-- `ℓ_b`. -/
  b : ℝ≥0∞
  /-- `ℓ_ab`. -/
  ab : ℝ≥0∞

/-- The submultiplicativity condition `ℓ_ab ≤ ℓ_a ℓ_b` for the product property. -/
def Wt.Sub (w : Wt) : Prop := w.ab ≤ w.a * w.b

variable {c : Case} {Λ : Type*}

/-- `‖F‖ = ‖F_∅‖ + ℓ_a ‖F_a‖ + ℓ_b ‖F_b‖ + ℓ_ab ‖F_ab‖` (`e:Tphi-obs`). -/
def oNorm (nrm : N Λ → ℝ≥0∞) (w : Wt) (F : SA c Λ) : ℝ≥0∞ :=
  nrm F.e + w.a * nrm F.a + w.b * nrm F.b + w.ab * nrm F.ab

theorem oNorm_mono {nrm nrm' : N Λ → ℝ≥0∞} (hn : ∀ x, nrm x ≤ nrm' x) {w w' : Wt}
    (ha : w.a ≤ w'.a) (hb : w.b ≤ w'.b) (hab : w.ab ≤ w'.ab) (F : SA c Λ) :
    oNorm nrm w F ≤ oNorm nrm' w' F := by
  unfold oNorm; gcongr <;> exact hn _

/-- Comparison of norms and weights with a common factor `K ≥ 1`. -/
theorem oNorm_le_mul {nrm nrm' : N Λ → ℝ≥0∞} (hn : ∀ x, nrm x ≤ nrm' x) {w w' : Wt} {K : ℝ≥0∞}
    (hK : 1 ≤ K) (ha : w.a ≤ K * w'.a) (hb : w.b ≤ K * w'.b) (hab : w.ab ≤ K * w'.ab)
    (F : SA c Λ) : oNorm nrm w F ≤ K * oNorm nrm' w' F := by
  calc oNorm nrm w F ≤ K * nrm' F.e + (K * w'.a) * nrm' F.a + (K * w'.b) * nrm' F.b +
        (K * w'.ab) * nrm' F.ab := by
        unfold oNorm
        gcongr ?_ + ?_ * ?_ + ?_ * ?_ + ?_ * ?_ <;> try exact hn _
        exact (hn _).trans (le_mul_of_one_le_left (by positivity) hK)
    _ = K * oNorm nrm' w' F := by unfold oNorm; ring

section T

variable {X : Type*} [DecidableEq X] [Fintype X] {E : Type*} [Fintype E] [DecidableEq E]
  [AddAction (E → ℕ) X] {p : ℕ} {h ℓ : ℝ}

variable (E) in
/-- The `T(h, ℓ)` norm with observables. -/
abbrev oT (p : ℕ) (h ℓ : ℝ) (w : Wt) (F : SA c X) : ℝ≥0∞ := oNorm (tNorm E p h ℓ) w F

variable {w : Wt}

theorem oT_def (F : SA c X) : oT E p h ℓ w F = tNorm E p h ℓ F.e + w.a * tNorm E p h ℓ F.a +
    w.b * tNorm E p h ℓ F.b + w.ab * tNorm E p h ℓ F.ab := rfl

theorem oT_add_le (F G : SA c X) : oT E p h ℓ w (F + G) ≤ oT E p h ℓ w F + oT E p h ℓ w G := by
  simp only [oT_def, add_e, add_a, add_b, add_ab]
  calc _ ≤ (tNorm E p h ℓ F.e + tNorm E p h ℓ G.e) + w.a * (tNorm E p h ℓ F.a + tNorm E p h ℓ G.a)
        + w.b * (tNorm E p h ℓ F.b + tNorm E p h ℓ G.b)
        + w.ab * (tNorm E p h ℓ F.ab + tNorm E p h ℓ G.ab) := by
        gcongr <;> exact Loc.tNorm_add_le _ _
    _ = _ := by ring

theorem oT_smul (r : ℂ) (F : SA c X) : oT E p h ℓ w (r • F) = ENNReal.ofReal ‖r‖ * oT E p h ℓ w F := by
  simp only [oT_def, smul_e, smul_a, smul_b, smul_ab, Step.tNorm_smul]; ring

theorem oT_neg (F : SA c X) : oT E p h ℓ w (-F) = oT E p h ℓ w F := by
  simp only [oT_def, neg_e, neg_a, neg_b, neg_ab, Loc.tNorm_neg]

theorem oT_sub_le (F G : SA c X) : oT E p h ℓ w (F - G) ≤ oT E p h ℓ w F + oT E p h ℓ w G := by
  rw [sub_eq_add_neg]; exact (oT_add_le _ _).trans (by rw [oT_neg])

theorem oT_zero : oT E p h ℓ w (0 : SA c X) = 0 := by
  have := oT_smul (E := E) (p := p) (h := h) (ℓ := ℓ) (w := w) (0 : ℂ) (0 : SA c X)
  rw [zero_smul] at this; rw [this]; simp

theorem oT_sum_le {ι : Type*} (s : Finset ι) (F : ι → SA c X) :
    oT E p h ℓ w (∑ i ∈ s, F i) ≤ ∑ i ∈ s, oT E p h ℓ w (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [oT_zero]
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (oT_add_le _ _).trans (add_le_add le_rfl ih)

theorem tNorm_zero' : tNorm E p h ℓ (0 : N X) = 0 := by
  have := Step.tNorm_smul (E := E) (p := p) (h := h) (ℓ := ℓ) (0 : ℂ) (0 : N X)
  rw [zero_smul] at this; rw [this]; simp

theorem oT_ofN (x : N X) : oT E p h ℓ w (ofN x : SA c X) = tNorm E p h ℓ x := by
  simp [oT_def, tNorm_zero']

theorem oT_one_le (hh : 0 < h) (hℓ : 0 < ℓ) : oT E p h ℓ w (1 : SA c X) ≤ 1 := by
  simp only [oT_def, one_e, one_a, one_b, one_ab]
  rw [tNorm_zero']; simpa using Loc.tNorm_one_le hh hℓ

theorem tNorm_smul_s (x : N X) : tNorm E p h ℓ (c.s • x) = tNorm E p h ℓ x := by
  rw [Step.tNorm_smul, Case.norm_s]; simp

/-- The product property for even elements, assuming `ℓ_ab ≤ ℓ_a ℓ_b`. -/
theorem oT_mul_le (hh : 0 < h) (hℓ : 0 < ℓ) (hw : w.Sub) (F G : OE c X) :
    oT E p h ℓ w ((F * G : OE c X) : SA c X) ≤ oT E p h ℓ w (F : SA c X) * oT E p h ℓ w (G : SA c X) := by
  set n := tNorm E p h ℓ (X := X)
  rw [oT_def, OE.mul_e, OE.mul_a, OE.mul_b, OE.mul_ab]
  have hm : ∀ x y : N X, n (x * y) ≤ n x * n y := fun x y => tNorm_mul_le hh hℓ x y
  have ha : ∀ x y : N X, n (x + y) ≤ n x + n y := fun x y => Loc.tNorm_add_le x y
  set fe := n (F : SA c X).e; set fa := n (F : SA c X).a; set fb := n (F : SA c X).b
  set fab := n (F : SA c X).ab; set ge := n (G : SA c X).e; set ga := n (G : SA c X).a
  set gb := n (G : SA c X).b; set gab := n (G : SA c X).ab
  have h1 : n ((F : SA c X).e * (G : SA c X).a + (F : SA c X).a * (G : SA c X).e) ≤
      fe * ga + fa * ge := (ha _ _).trans (add_le_add (hm _ _) (hm _ _))
  have h2 : n ((F : SA c X).e * (G : SA c X).b + (F : SA c X).b * (G : SA c X).e) ≤
      fe * gb + fb * ge := (ha _ _).trans (add_le_add (hm _ _) (hm _ _))
  have h3 : n ((F : SA c X).e * (G : SA c X).ab + c.s • ((F : SA c X).a * (G : SA c X).b) +
      (F : SA c X).b * (G : SA c X).a + (F : SA c X).ab * (G : SA c X).e) ≤
      fe * gab + fa * gb + fb * ga + fab * ge := by
    refine (ha _ _).trans (add_le_add ((ha _ _).trans (add_le_add ((ha _ _).trans
      (add_le_add (hm _ _) ?_)) (hm _ _))) (hm _ _))
    exact (tNorm_smul_s _).trans_le (hm _ _)
  have hw' : w.ab ≤ w.a * w.b := hw
  calc n ((F : SA c X).e * (G : SA c X).e) + w.a * n _ + w.b * n _ + w.ab * n _
      ≤ fe * ge + w.a * (fe * ga + fa * ge) + w.b * (fe * gb + fb * ge) +
        w.ab * (fe * gab + fa * gb + fb * ga + fab * ge) := by
        gcongr
        exact hm _ _
    _ ≤ fe * ge + w.a * (fe * ga + fa * ge) + w.b * (fe * gb + fb * ge) +
        (w.ab * (fe * gab) + (w.a * w.b) * (fa * gb) + (w.a * w.b) * (fb * ga) +
          w.ab * (fab * ge)) := by
        rw [mul_add w.ab, mul_add w.ab, mul_add w.ab]
        gcongr
    _ ≤ (fe * ge + w.a * (fe * ga + fa * ge) + w.b * (fe * gb + fb * ge) +
        (w.ab * (fe * gab) + (w.a * w.b) * (fa * gb) + (w.a * w.b) * (fb * ga) +
          w.ab * (fab * ge))) + (w.a * fa * (w.a * ga) + w.a * fa * (w.ab * gab) +
          w.b * fb * (w.b * gb) + w.b * fb * (w.ab * gab) + w.ab * fab * (w.a * ga) +
          w.ab * fab * (w.b * gb) + w.ab * fab * (w.ab * gab)) := le_self_add
    _ = (fe + w.a * fa + w.b * fb + w.ab * fab) * (ge + w.a * ga + w.b * gb + w.ab * gab) := by
        ring

theorem oT_pow_le (hh : 0 < h) (hℓ : 0 < ℓ) (hw : w.Sub) (F : OE c X) (k : ℕ) :
    oT E p h ℓ w ((F ^ k : OE c X) : SA c X) ≤ oT E p h ℓ w (F : SA c X) ^ k := by
  induction k with
  | zero => simpa using oT_one_le (E := E) (p := p) (w := w) (c := c) (X := X) hh hℓ
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact (oT_mul_le hh hℓ hw _ _).trans (mul_le_mul_left ih _)

theorem oT_prod_le (hh : 0 < h) (hℓ : 0 < ℓ) (hw : w.Sub) {ι : Type*} (s : Finset ι)
    (F : ι → OE c X) :
    oT E p h ℓ w ((∏ i ∈ s, F i : OE c X) : SA c X) ≤ ∏ i ∈ s, oT E p h ℓ w (F i : SA c X) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using oT_one_le (E := E) (p := p) (w := w) (c := c) (X := X) hh hℓ
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha]
    exact (oT_mul_le hh hℓ hw _ _).trans (mul_le_mul_right ih _)

/-- `‖θ F‖_{T(ℓ)} ≤ ‖F‖_{T(2ℓ)}` (same weights). -/
theorem oT_theta_le (hh : 0 < h) (hℓ : 0 < ℓ) (F : SA c X) :
    oT E p h ℓ w (thetaS F) ≤ oT E p h (2 * ℓ) w F := by
  simp only [oT_def, thetaS_e, thetaS_a, thetaS_b, thetaS_ab]
  gcongr <;> exact tNorm_theta_le hh hℓ _

/-- `‖ι F‖ ≤ ‖F‖` for the inclusion `𝒩(X) ⊆ 𝒩(X ⊔ X)`. -/
theorem oT_incl_le (hh : 0 < h) (hℓ : 0 < ℓ) (F : SA c X) :
    oT E p h ℓ w (inclS F) ≤ oT E p h ℓ w F := by
  simp only [oT_def, inclS_e, inclS_a, inclS_b, inclS_ab]
  gcongr <;> exact Step.tNorm_incl_le hh hℓ _

/-- `𝔼_C` is a contraction (`e:normcontract`-type bound). -/
theorem oT_EC_le (hh : 0 < h) (hℓ : 0 < ℓ) {C : Matrix X X ℝ} (hC : C.PosSemidef)
    (hCn : covNorm E p h ℓ C ≤ 1) (F : SA c (X ⊕ X)) :
    oT E p h ℓ w (ECS C F) ≤ oT E p h ℓ w F := by
  simp only [oT_def, ECS_e, ECS_a, ECS_b, ECS_ab]
  gcongr <;> exact tNorm_EC_le hh hℓ hC hCn _

theorem oT_EC_theta_le (hh : 0 < h) (hℓ : 0 < ℓ) {C : Matrix X X ℝ} (hC : C.PosSemidef)
    (hCn : covNorm E p h ℓ C ≤ 1) (F : SA c X) :
    oT E p h ℓ w (ECS C (thetaS F)) ≤ oT E p h (2 * ℓ) w F :=
  (oT_EC_le hh hℓ hC hCn _).trans (oT_theta_le hh hℓ F)

/-! #### Exponentials -/

theorem oT_sum_smul_pow_le (hh : 0 < h) (hℓ : 0 < ℓ) (hw : w.Sub) (G : OE c X) {r : ℝ}
    (hr : 0 ≤ r) (hG : oT E p h ℓ w (G : SA c X) ≤ ENNReal.ofReal r) (s : Finset ℕ)
    (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (f : ℕ → ℕ) :
    oT E p h ℓ w ((∑ i ∈ s, (a i : ℂ) • G ^ f i : OE c X) : SA c X) ≤
      ENNReal.ofReal (∑ i ∈ s, a i * r ^ f i) := by
  rw [AddSubmonoidClass.coe_finsetSum]
  refine (oT_sum_le _ _).trans ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun i _ => mul_nonneg (ha i) (pow_nonneg hr _)]
  refine sum_le_sum fun i _ => ?_
  rw [show (((a i : ℂ) • G ^ f i : OE c X) : SA c X) = (a i : ℂ) • ((G ^ f i : OE c X) : SA c X)
    from rfl, oT_smul, Complex.norm_real, Real.norm_of_nonneg (ha i),
    ENNReal.ofReal_mul (ha i), ENNReal.ofReal_pow hr]
  gcongr
  exact (oT_pow_le hh hℓ hw G _).trans (by gcongr)

variable [DecidableEq X]

/-- `‖e^F‖ ≤ e^{‖F‖}`. -/
theorem oT_oexp_le (hh : 0 < h) (hℓ : 0 < ℓ) (hw : w.Sub) {F : OE c X}
    (hF : ε ((F : SA c X).e) = 0) {r : ℝ} (hr : 0 ≤ r)
    (hFr : oT E p h ℓ w (F : SA c X) ≤ ENNReal.ofReal r) :
    oT E p h ℓ w (oexp F : SA c X) ≤ ENNReal.ofReal (Real.exp r) := by
  rw [coe_oexp (pow_eq_zero_of_ε hF)]
  have e : ∑ i ∈ range (Nf X + 3), ((i.factorial : ℂ)⁻¹) • F ^ i =
      ∑ i ∈ range (Nf X + 3), (((i.factorial : ℝ)⁻¹ : ℝ) : ℂ) • F ^ id i := by
    push_cast; rfl
  rw [e]
  refine (oT_sum_smul_pow_le hh hℓ hw _ hr hFr _ (fun i => (i.factorial : ℝ)⁻¹)
    (fun i => by positivity) id).trans ?_
  refine ENNReal.ofReal_le_ofReal ((le_of_eq ?_).trans (Real.sum_le_exp_of_nonneg hr (Nf X + 3)))
  refine sum_congr rfl fun i _ => ?_
  simp [div_eq_inv_mul]

/-- `‖e^F - 1‖ ≤ e^{‖F‖} - 1`. -/
theorem oT_oexp_sub_one_le (hh : 0 < h) (hℓ : 0 < ℓ) (hw : w.Sub) {F : OE c X}
    (hF : ε ((F : SA c X).e) = 0) {r : ℝ} (hr : 0 ≤ r)
    (hFr : oT E p h ℓ w (F : SA c X) ≤ ENNReal.ofReal r) :
    oT E p h ℓ w ((oexp F - 1 : OE c X) : SA c X) ≤ ENNReal.ofReal (Real.exp r - 1) := by
  have e : oexp F - 1 =
      ∑ i ∈ range (Nf X + 3), ((((i + 1).factorial : ℝ)⁻¹ : ℝ) : ℂ) • F ^ (i + 1) := by
    rw [coe_oexp (k := Nf X + 3 + 1) (by rw [pow_succ, pow_eq_zero_of_ε hF, zero_mul]),
      sum_range_succ']
    simp
  rw [e]
  refine (oT_sum_smul_pow_le hh hℓ hw _ hr hFr _ _ (fun i => by positivity) _).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hs := Real.sum_le_exp_of_nonneg hr (Nf X + 3 + 1)
  rw [sum_range_succ'] at hs
  simp only [div_eq_inv_mul, pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one,
    mul_one] at hs
  linarith

end T

/-! ### The weights `e:ellsigma` -/

/-- `ℓ_a = ℓ_b = ℓ^{-p}`. -/
def ella (c : Case) (ℓ : ℝ) : ℝ := ℓ⁻¹ ^ c.p

/-- `ℓ_ab = ℓ^{-2}` (Case (1)), `ℓ^{-2} ℓ'^{-2}` (Case (2)). -/
def ellab (c : Case) (ℓ ℓ' : ℝ) : ℝ := match c with
  | .one => ℓ⁻¹ ^ 2
  | .two => ℓ⁻¹ ^ 2 * ℓ'⁻¹ ^ 2

/-- The weights `e:ellsigma`. -/
def obsWt (c : Case) (ℓ ℓ' : ℝ) : Wt :=
  ⟨ENNReal.ofReal (ella c ℓ), ENNReal.ofReal (ella c ℓ), ENNReal.ofReal (ellab c ℓ ℓ')⟩

theorem ella_nonneg (c : Case) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) : 0 ≤ ella c ℓ := by
  unfold ella; positivity

/-- `ℓ_ab ≤ ℓ_a ℓ_b` (for Case (2) this needs `ℓ ≤ ℓ'`). -/
theorem obsWt_sub (c : Case) {ℓ ℓ' : ℝ} (hℓ : 0 < ℓ) (hℓ' : c = .two → ℓ ≤ ℓ') :
    (obsWt c ℓ ℓ').Sub := by
  unfold Wt.Sub obsWt
  simp only
  rw [← ENNReal.ofReal_mul (ella_nonneg c hℓ.le)]
  refine ENNReal.ofReal_le_ofReal ?_
  cases c
  · simp [ella, ellab, Case.p]; ring_nf; rfl
  · have h := hℓ' rfl
    simp only [ella, ellab, Case.p]
    have : ℓ'⁻¹ ≤ ℓ⁻¹ := inv_anti₀ hℓ h
    have h0 : 0 ≤ ℓ'⁻¹ := (inv_pos.2 (hℓ.trans_le h)).le
    calc ℓ⁻¹ ^ 2 * ℓ'⁻¹ ^ 2 ≤ ℓ⁻¹ ^ 2 * ℓ⁻¹ ^ 2 := by gcongr
      _ = _ := by ring

/-! ### Scale-dependent weights on the torus -/

section Torus

variable {d L N : ℕ} [NeZero L]

/-- `j ∧ j_ab`, for `j_ab ∈ ℕ ∪ {∞}`. -/
def jwedge (j : ℕ) (jab : ℕ∞) : ℕ := (min (j : ℕ∞) jab).toNat

theorem jwedge_top (j : ℕ) : jwedge j ⊤ = j := by simp [jwedge]

theorem jwedge_coe (j k : ℕ) : jwedge j k = min j k := by
  rcases le_total j k with h | h <;> simp [jwedge, h]

theorem jwedge_le (j : ℕ) (jab : ℕ∞) : jwedge j jab ≤ j := by
  unfold jwedge
  rcases le_total (j : ℕ∞) jab with h | h
  · rw [min_eq_left h]; simp
  · rw [min_eq_right h]
    lift jab to ℕ using ne_top_of_le_ne_top (ENat.coe_ne_top j) h
    simpa using h

theorem jwedge_eq_of_ge {j k : ℕ} (h : k ≤ j) : jwedge j k = k := by
  rw [jwedge_coe, min_eq_right h]

theorem jwedge_succ (j : ℕ) (jab : ℕ∞) :
    jwedge (j + 1) jab = jwedge j jab ∨ jwedge (j + 1) jab = jwedge j jab + 1 := by
  induction jab using ENat.recTopCoe with
  | top => right; simp [jwedge_top]
  | coe k =>
    rw [jwedge_coe, jwedge_coe]
    omega

variable (L) in
/-- The coalescence scale `j_ab = ⌊log_L (2 |a - b|_∞)⌋` (`E:coal`). -/
def coal (a b : Loc.Lam d L N) : ℕ := Nat.log L (2 * supNorm (a - b))

/-- For `k < j_ab`: `L^{k+1} ≤ 2 |a - b|_∞`, so that `C_{k+1}(a, b) = 0` by the finite range
property (`e:C-range`, `GoodCov.range`). -/
theorem pow_le_of_lt_coal {a b : Loc.Lam d L N} {k : ℕ} (hk : k < coal L a b) :
    (L : ℝ) ^ (k + 1) / 2 ≤ supNorm (a - b) := by
  have hne : 2 * supNorm (a - b) ≠ 0 := by
    intro h0
    rw [coal, h0, Nat.log_zero_right] at hk
    exact Nat.not_lt_zero _ hk
  have h1 : L ^ (k + 1) ≤ L ^ coal L a b := by
    rcases Nat.lt_or_ge L 2 with hL | hL
    · have : Nat.log L (2 * supNorm (a - b)) = 0 := Nat.log_of_left_le_one (by omega) _
      rw [coal, this] at hk; omega
    · exact Nat.pow_le_pow_right (by omega) hk
  have h2 : L ^ coal L a b ≤ 2 * supNorm (a - b) := Nat.pow_log_le_self L hne
  have : ((L ^ (k + 1) : ℕ) : ℝ) ≤ ((2 * supNorm (a - b) : ℕ) : ℝ) := by exact_mod_cast h1.trans h2
  push_cast at this
  linarith

variable (d L) in
/-- The weights at scale `j` (`e:ellsigma`): `obsWt c ℓ_j ℓ_{j ∧ j_ab}`. -/
def wj (c : Case) (ℓ₀ : ℝ) (jab : ℕ∞) (j : ℕ) : Wt :=
  obsWt c (ellj d L ℓ₀ j) (ellj d L ℓ₀ (jwedge j jab))

variable (d L) in
/-- The norm `‖F‖_{T_j(ℓ)}` with the weights of scale `j`. -/
abbrev oTj (w : Wt) (j : ℕ) (ℓ : ℝ) (F : SA c (Loc.Lam d L N)) : ℝ≥0∞ :=
  oNorm (Tj d (L : ℝ) j ℓ) w F

variable (d L) in
/-- `‖F‖_{T_j(ℓ_j)}`, the norm `e:Tphi-obs` at scale `j`. -/
abbrev normj (c : Case) (ℓ₀ : ℝ) (jab : ℕ∞) (j : ℕ) (F : SA c (Loc.Lam d L N)) : ℝ≥0∞ :=
  oTj d L (wj d L c ℓ₀ jab j) j (ellj d L ℓ₀ j) F

theorem ellj_anti (hd : 2 ≤ d) {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) {j k : ℕ} (hjk : j ≤ k) :
    ellj d (L : ℝ) ℓ₀ k ≤ ellj d (L : ℝ) ℓ₀ j := by
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast NeZero.one_le
  unfold ellj
  refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL ?_) hℓ₀.le
  have h0 : (0 : ℝ) ≤ (d : ℝ) - 2 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hjk' : (j : ℝ) ≤ k := by exact_mod_cast hjk
  have : -((d : ℝ) - 2) * k ≤ -((d : ℝ) - 2) * j := by nlinarith
  linarith

/-- The product property holds for the weights of scale `j` (`ℓ_j ≤ ℓ_{j ∧ j_ab}`). -/
theorem wj_sub (hd : 2 ≤ d) (c : Case) {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) (jab : ℕ∞) (j : ℕ) :
    (wj d L c ℓ₀ jab j).Sub :=
  obsWt_sub c (ellj_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) hℓ₀ j)
    fun _ => ellj_anti hd hℓ₀ (jwedge_le j jab)

/-- `ℓ_j / ℓ_{j+1} = L^{(d-2)/2}`. -/
theorem ellj_div_succ {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) (j : ℕ) :
    (ellj d (L : ℝ) ℓ₀ (j + 1))⁻¹ = (ellj d (L : ℝ) ℓ₀ j)⁻¹ * (L : ℝ) ^ (((d : ℝ) - 2) / 2) := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  rw [ellj_succ hL, mul_inv, ← Real.rpow_neg hL.le]
  congr 2; ring

/-- `ℓ_{a,j+1} = L^{p(d-2)/2} ℓ_{a,j}`. -/
theorem wj_succ_a (c : Case) {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) (jab : ℕ∞) (j : ℕ) :
    ella c (ellj d (L : ℝ) ℓ₀ (j + 1)) =
      ((L : ℝ) ^ (((d : ℝ) - 2) / 2)) ^ c.p * ella c (ellj d (L : ℝ) ℓ₀ j) := by
  rw [ella, ella, ellj_div_succ hℓ₀, mul_pow, mul_comm]

/-- `ℓ_{ab,j+1} = L^{d-2} ℓ_{ab,j}` (Case (1)). -/
theorem wj_succ_ab_one {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) (j : ℕ) (ℓ' ℓ'' : ℝ) :
    ellab .one (ellj d (L : ℝ) ℓ₀ (j + 1)) ℓ' =
      ((L : ℝ) ^ (((d : ℝ) - 2) / 2)) ^ 2 * ellab .one (ellj d (L : ℝ) ℓ₀ j) ℓ'' := by
  simp only [ellab]; rw [ellj_div_succ hℓ₀, mul_pow, mul_comm]

theorem one_le_rL (hd : 2 ≤ d) : (1 : ℝ) ≤ (L : ℝ) ^ (((d : ℝ) - 2) / 2) := by
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast NeZero.one_le
  refine Real.one_le_rpow hL ?_
  have : (2 : ℝ) ≤ d := by exact_mod_cast hd
  linarith

/-- `ℓ' = ℓ_{j ∧ j_ab}` at scale `j + 1` versus scale `j`. -/
theorem ellP_succ (hd : 2 ≤ d) {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) (j : ℕ) (jab : ℕ∞) :
    (ellj d (L : ℝ) ℓ₀ (jwedge (j + 1) jab))⁻¹ ≤
      (ellj d (L : ℝ) ℓ₀ (jwedge j jab))⁻¹ * (L : ℝ) ^ (((d : ℝ) - 2) / 2) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  rcases jwedge_succ j jab with h | h
  · rw [h]
    exact le_mul_of_one_le_right (inv_pos.2 (ellj_pos hL0 hℓ₀ _)).le (one_le_rL hd)
  · rw [h, ellj_div_succ hℓ₀]

/-- The weight ratio `ℓ_{x,j+1} ≤ L^{2(d-2)} ℓ_{x,j}`. -/
theorem wj_succ_le (hd : 2 ≤ d) (c : Case) {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) (jab : ℕ∞) (j : ℕ) :
    ella c (ellj d (L : ℝ) ℓ₀ (j + 1)) ≤
        ((L : ℝ) ^ (((d : ℝ) - 2) / 2)) ^ 4 * ella c (ellj d (L : ℝ) ℓ₀ j) ∧
      ellab c (ellj d (L : ℝ) ℓ₀ (j + 1)) (ellj d (L : ℝ) ℓ₀ (jwedge (j + 1) jab)) ≤
        ((L : ℝ) ^ (((d : ℝ) - 2) / 2)) ^ 4 *
          ellab c (ellj d (L : ℝ) ℓ₀ j) (ellj d (L : ℝ) ℓ₀ (jwedge j jab)) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set r := (L : ℝ) ^ (((d : ℝ) - 2) / 2)
  have hr : 1 ≤ r := one_le_rL hd
  have hℓ := ellj_pos (d := d) hL0 hℓ₀ j
  have hpow : ∀ k ≤ 4, r ^ k ≤ r ^ 4 := fun k hk => pow_le_pow_right₀ hr hk
  constructor
  · rw [wj_succ_a c hℓ₀ jab j]
    gcongr
    · exact ella_nonneg c hℓ.le
    · cases c <;> norm_num [Case.p]
  · cases c
    · rw [wj_succ_ab_one (d := d) (L := L) hℓ₀ j _ (ellj d (L : ℝ) ℓ₀ (jwedge j jab))]
      gcongr
      · simp only [ellab]; positivity
      · norm_num
    · simp only [ellab]
      have h1 := ellP_succ (d := d) (L := L) hd hℓ₀ j jab
      have h0 : 0 ≤ (ellj d (L : ℝ) ℓ₀ (jwedge (j + 1) jab))⁻¹ :=
        (inv_pos.2 (ellj_pos hL0 hℓ₀ _)).le
      rw [ellj_div_succ hℓ₀]
      calc ((ellj d (L : ℝ) ℓ₀ j)⁻¹ * r) ^ 2 * (ellj d (L : ℝ) ℓ₀ (jwedge (j + 1) jab))⁻¹ ^ 2
          ≤ ((ellj d (L : ℝ) ℓ₀ j)⁻¹ * r) ^ 2 * ((ellj d (L : ℝ) ℓ₀ (jwedge j jab))⁻¹ * r) ^ 2 := by
            gcongr
        _ = r ^ 4 * ((ellj d (L : ℝ) ℓ₀ j)⁻¹ ^ 2 * (ellj d (L : ℝ) ℓ₀ (jwedge j jab))⁻¹ ^ 2) := by
            ring

theorem rL_pow_four : ((L : ℝ) ^ (((d : ℝ) - 2) / 2)) ^ 4 = (L : ℝ) ^ (2 * ((d : ℝ) - 2)) := by
  have hL0 : (0 : ℝ) ≤ L := by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul hL0]; congr 1; push_cast; ring

/-- `e:Tphi-obs-ub`: `‖F‖_{T_{j+1}(ℓ_{j+1})} ≤ ‖F‖_{T_{j+1}(2ℓ_{j+1})} ≤ L^{2(d-2)} ‖F‖_{T_j(ℓ_j)}`
(with the weights of scale `j + 1` on the left, see the module docstring). -/
theorem normj_succ_le (hd : 3 ≤ d) (hL : (4 : ℝ) ≤ L) (c : Case) {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀)
    (jab : ℕ∞) (j : ℕ) (F : SA c (Loc.Lam d L N)) :
    normj d L c ℓ₀ jab (j + 1) F ≤
        oTj d L (wj d L c ℓ₀ jab (j + 1)) (j + 1) (2 * ellj d (L : ℝ) ℓ₀ (j + 1)) F ∧
      oTj d L (wj d L c ℓ₀ jab (j + 1)) (j + 1) (2 * ellj d (L : ℝ) ℓ₀ (j + 1)) F ≤
        ENNReal.ofReal ((L : ℝ) ^ (2 * ((d : ℝ) - 2))) * normj d L c ℓ₀ jab j F := by
  constructor
  · exact oNorm_mono (fun x => (Tj_succ_le hd hL hℓ₀ j x).1) le_rfl le_rfl le_rfl F
  · have hw := wj_succ_le (d := d) (L := L) (by omega) c hℓ₀ jab j
    rw [rL_pow_four] at hw
    have hK : (1 : ℝ) ≤ (L : ℝ) ^ (2 * ((d : ℝ) - 2)) := by
      rw [← rL_pow_four]; exact one_le_pow₀ (one_le_rL (by omega))
    refine oNorm_le_mul (fun x => (Tj_succ_le hd hL hℓ₀ j x).2) (by simpa using hK) ?_ ?_ ?_ F
    · simp only [wj, obsWt]
      rw [← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal hw.1
    · simp only [wj, obsWt]
      rw [← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal hw.1
    · simp only [wj, obsWt]
      rw [← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal hw.2

/-- `‖𝔼_{C_{j+1}} θ F‖_{j+1} ≤ L^{2(d-2)} ‖F‖_j` (for `C_{j+1}` as in `GoodCov`). -/
theorem normj_EC_theta_le (hd : 3 ≤ d) (hL : (4 : ℝ) ≤ L) (c : Case) {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀)
    (jab : ℕ∞) (j : ℕ) {C : Matrix (Loc.Lam d L N) (Loc.Lam d L N) ℝ} (hC : C.PosSemidef)
    (hCn : covNormj (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1)) C ≤ 1) (F : SA c (Loc.Lam d L N)) :
    normj d L c ℓ₀ jab (j + 1) (ECS C (thetaS F)) ≤
      ENNReal.ofReal ((L : ℝ) ^ (2 * ((d : ℝ) - 2))) * normj d L c ℓ₀ jab j F := by
  have hL0 : (0 : ℝ) < L := by linarith
  exact (oT_EC_theta_le (by positivity) (ellj_pos hL0 hℓ₀ _) hC hCn F).trans
    (normj_succ_le hd hL c hℓ₀ jab j F).2

end Torus

end

end Obs
