module

public import ArborealDecay.TLaw.Defs

/-!
# Elementary inequalities (supplement `lem:elem`) and log-convexity of `D`

* `cosh_add_le`: `cosh (u + h) ≤ e^{|h|} cosh u` (`lem:elem`(i)).
* `cosh_combo_ge`: `q cosh x - (q-1) cosh (x + γ d) ≥ (1 - (q-1) q² γ² d²) cosh (x + y*)` for
  `|q γ d| ≤ 1`, `y* = -(q-1) γ d`. This is the form of `lem:elem`(ii) used in `thm:sabot`:
  the supplement's `κ = ½ (q-1) q² γ² d² e^{q γ |d|}` is only ever used through
  `κ ≤ (q-1) q² γ² d²`, which we take as the definition of `κ`.
* `sum_exp_logconvex`: Hölder log-convexity of `c ↦ ∑ α_T e^{c λ_T}` (`lem:elem`(iii)).
* `inv_one_sub_le_exp`: `(1-κ)⁻¹ ≤ e^{2κ}` for `0 ≤ κ ≤ ½` (`lem:elem`(iv)).
* `D_logconvex`: `D(t + (θ c₁ + (1-θ) c₂) v) ≤ D(t + c₁ v)^θ D(t + c₂ v)^{1-θ}`.
* `edgeSum_eq_sum_edgeFinset`: `edgeSum w g = ∑_{e ∈ E(w)} g_e`.
-/

open Finset Matrix Real

set_option linter.unusedSectionVars false

public section

namespace ArborealDecay.TLaw

/-- `lem:elem`(i): `cosh (u + h) ≤ e^{|h|} cosh u`. -/
theorem cosh_add_le (u h : ℝ) : cosh (u + h) ≤ exp |h| * cosh u := by
  have hs : |sinh u| ≤ cosh u := by
    rw [abs_le, sinh_eq, cosh_eq]
    constructor <;> nlinarith [exp_pos u, exp_pos (-u)]
  have hc : 0 ≤ cosh u := (cosh_pos u).le
  rw [cosh_add, ← cosh_abs h, ← cosh_add_sinh |h|]
  have : sinh u * sinh h ≤ cosh u * sinh |h| := by
    calc sinh u * sinh h ≤ |sinh u * sinh h| := le_abs_self _
      _ = |sinh u| * |sinh h| := abs_mul _ _
      _ ≤ cosh u * |sinh h| := mul_le_mul_of_nonneg_right hs (abs_nonneg _)
      _ = cosh u * sinh |h| := by rw [abs_sinh]
  rw [cosh_abs]
  nlinarith

theorem abs_sinh_le_cosh (u : ℝ) : |sinh u| ≤ cosh u := by
  rw [abs_le, sinh_eq, cosh_eq]
  constructor <;> nlinarith [exp_pos u, exp_pos (-u)]

/-- `|sinh h - h| ≤ cosh h - 1`. -/
theorem abs_sinh_sub_le (h : ℝ) : |sinh h - h| ≤ cosh h - 1 := by
  rw [abs_le, sinh_eq, cosh_eq]
  have h1 := add_one_le_exp h
  have h2 := add_one_le_exp (-h)
  constructor <;> linarith

/-- `cosh h - 1 + |sinh h - h| ≤ h²` for `|h| ≤ 1`. -/
theorem cosh_sub_one_add_abs_le (h : ℝ) (hh : |h| ≤ 1) :
    cosh h - 1 + |sinh h - h| ≤ h ^ 2 := by
  rw [sinh_eq, cosh_eq]
  have e1 := abs_exp_sub_one_sub_id_le hh
  have e2 := abs_exp_sub_one_sub_id_le (x := -h) (by rwa [abs_neg])
  rcases le_total 0 ((exp h - exp (-h)) / 2 - h) with hpos | hneg
  · rw [abs_of_nonneg hpos]
    have := (abs_le.1 e1).2
    nlinarith
  · rw [abs_of_nonpos hneg]
    have := (abs_le.1 e2).2
    nlinarith

/-- The tangent-line remainder `R(h) = cosh(u+h) - cosh u - sinh u · h`. -/
theorem cosh_add_eq (u h : ℝ) :
    cosh (u + h) = cosh u + sinh u * h + (cosh u * (cosh h - 1) + sinh u * (sinh h - h)) := by
  rw [cosh_add]; ring

theorem remainder_nonneg (u h : ℝ) : 0 ≤ cosh u * (cosh h - 1) + sinh u * (sinh h - h) := by
  have h1 := abs_sinh_le_cosh u
  have h2 := abs_sinh_sub_le h
  have h3 : -(sinh u * (sinh h - h)) ≤ cosh u * (cosh h - 1) := by
    calc -(sinh u * (sinh h - h)) ≤ |sinh u * (sinh h - h)| := neg_le_abs _
      _ = |sinh u| * |sinh h - h| := abs_mul _ _
      _ ≤ cosh u * (cosh h - 1) :=
        mul_le_mul h1 h2 (abs_nonneg _) (cosh_pos u).le
  linarith

theorem remainder_le (u h : ℝ) (hh : |h| ≤ 1) :
    cosh u * (cosh h - 1) + sinh u * (sinh h - h) ≤ h ^ 2 * cosh u := by
  have h1 := abs_sinh_le_cosh u
  have h2 := cosh_sub_one_add_abs_le h hh
  have h3 : sinh u * (sinh h - h) ≤ cosh u * |sinh h - h| := by
    calc sinh u * (sinh h - h) ≤ |sinh u * (sinh h - h)| := le_abs_self _
      _ = |sinh u| * |sinh h - h| := abs_mul _ _
      _ ≤ cosh u * |sinh h - h| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  have hc := (cosh_pos u).le
  nlinarith

/-- `lem:elem`(ii), in the form used: for `q ≥ 1` and `|q γ d| ≤ 1`, with `y* = -(q-1) γ d`,
`q cosh x - (q-1) cosh (x + γ d) ≥ (1 - (q-1) q² γ² d²) cosh (x + y*)`. -/
theorem cosh_combo_ge {q γ d : ℝ} (hq : 1 ≤ q) (hqd : |q * γ * d| ≤ 1) (x : ℝ) :
    (1 - (q - 1) * q ^ 2 * γ ^ 2 * d ^ 2) * cosh (x - (q - 1) * γ * d) ≤
      q * cosh x - (q - 1) * cosh (x + γ * d) := by
  set u := x - (q - 1) * γ * d
  have hx : x = u + (q - 1) * γ * d := by simp [u]
  have hx' : x + γ * d = u + q * γ * d := by simp [u]; ring
  rw [hx', hx, cosh_add_eq u, cosh_add_eq u]
  have h0 := remainder_nonneg u ((q - 1) * γ * d)
  have h1 := remainder_le u (q * γ * d) hqd
  have : (q * γ * d) ^ 2 = q ^ 2 * γ ^ 2 * d ^ 2 := by ring
  rw [this] at h1
  have hq0 : 0 ≤ q - 1 := by linarith
  nlinarith [mul_le_mul_of_nonneg_left h1 hq0, mul_nonneg (by linarith : (0:ℝ) ≤ q) h0]

/-- `lem:elem`(iv): `(1-κ)⁻¹ ≤ e^{2κ}` for `0 ≤ κ ≤ ½`. -/
theorem inv_one_sub_le_exp {κ : ℝ} (h0 : 0 ≤ κ) (h1 : κ ≤ 1 / 2) : (1 - κ)⁻¹ ≤ exp (2 * κ) := by
  have hpos : 0 < 1 - κ := by linarith
  rw [inv_le_iff_one_le_mul₀ hpos]
  have := add_one_le_exp (2 * κ)
  nlinarith

/-- `lem:elem`(iii): `φ(c) = ∑ α_T e^{c λ_T}` with `α_T ≥ 0` is log-convex. -/
theorem sum_exp_logconvex {ι : Type*} (s : Finset ι) (α lam : ι → ℝ) (hα : ∀ i ∈ s, 0 ≤ α i)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (c₁ c₂ : ℝ) :
    ∑ i ∈ s, α i * exp ((θ * c₁ + (1 - θ) * c₂) * lam i) ≤
      (∑ i ∈ s, α i * exp (c₁ * lam i)) ^ θ * (∑ i ∈ s, α i * exp (c₂ * lam i)) ^ (1 - θ) := by
  have hpq : (1 / θ).HolderConjugate (1 / (1 - θ)) := by
    rw [Real.holderConjugate_iff]
    refine ⟨by rw [lt_div_iff₀ hθ0]; linarith, by field_simp; ring⟩
  have key := inner_le_Lp_mul_Lq_of_nonneg s hpq
    (f := fun i => (α i * exp (c₁ * lam i)) ^ θ) (g := fun i => (α i * exp (c₂ * lam i)) ^ (1 - θ))
    (fun i hi => rpow_nonneg (mul_nonneg (hα i hi) (exp_pos _).le) _)
    (fun i hi => rpow_nonneg (mul_nonneg (hα i hi) (exp_pos _).le) _)
  have hne1 : θ ≠ 0 := hθ0.ne'
  have hne2 : 1 - θ ≠ 0 := by linarith
  simp only [one_div, inv_inv] at key
  have e1 : ∀ i ∈ s, ((α i * exp (c₁ * lam i)) ^ θ) ^ θ⁻¹ = α i * exp (c₁ * lam i) :=
    fun i hi => by
      rw [← rpow_mul (mul_nonneg (hα i hi) (exp_pos _).le), mul_inv_cancel₀ hne1, rpow_one]
  have e2 : ∀ i ∈ s, ((α i * exp (c₂ * lam i)) ^ (1 - θ)) ^ (1 - θ)⁻¹ =
      α i * exp (c₂ * lam i) := fun i hi => by
    rw [← rpow_mul (mul_nonneg (hα i hi) (exp_pos _).le), mul_inv_cancel₀ hne2, rpow_one]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2] at key
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun i hi => ?_)) key
  rw [mul_rpow (hα i hi) (exp_pos _).le, mul_rpow (hα i hi) (exp_pos _).le, ← exp_mul,
    ← exp_mul]
  have : α i = α i ^ θ * α i ^ (1 - θ) := by
    rw [← rpow_add' (hα i hi) (by simp)]; simp
  rw [show α i * exp ((θ * c₁ + (1 - θ) * c₂) * lam i) =
      (α i ^ θ * α i ^ (1 - θ)) * (exp (c₁ * lam i * θ) * exp (c₂ * lam i * (1 - θ))) by
    rw [← this, ← exp_add]; ring_nf]
  ring

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Log-convexity of `c ↦ D(t + c v)` (from the tree expansion and `lem:elem`(iii)). -/
theorem D_logconvex {w : V → V → ℝ} (hW : IsWGraph w) (ρ : V) (t v : V → ℝ)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (c₁ c₂ : ℝ) :
    D w ρ (t + (θ * c₁ + (1 - θ) * c₂) • v) ≤
      D w ρ (t + c₁ • v) ^ θ * D w ρ (t + c₂ • v) ^ (1 - θ) := by
  classical
  simp only [D_eq_treeSum w hW.symm hW.diag, treeExp_add_smul, exp_add]
  have hα : ∀ T ∈ (univ.filter fun T : SimpleGraph V => T.IsTree),
      0 ≤ (∏ e ∈ T.edgeFinset, Sym2.lift ⟨w, hW.symm⟩ e) * exp (treeExp ρ T t) := by
    intro T _
    refine mul_nonneg (Finset.prod_nonneg fun e _ => ?_) (exp_pos _).le
    induction e using Sym2.ind with
    | h i k => exact hW.nonneg i k
  have := sum_exp_logconvex _ _ (fun T => treeExp ρ T v) hα hθ0 hθ1 c₁ c₂
  simpa only [mul_assoc] using this

open Classical in
/-- `edgeSum w g` is the sum of `g` over the unordered support edges `E(w)`. -/
theorem edgeSum_eq_sum_edgeFinset {w : V → V → ℝ} (hW : IsWGraph w) (g : V → V → ℝ)
    (hg : ∀ i k, g i k = g k i) :
    edgeSum w g = ∑ e ∈ (supportGraph w).edgeFinset, Sym2.lift ⟨g, hg⟩ e := by
  set G := supportGraph w
  have hadj : ∀ i k, G.Adj i k ↔ 0 < w i k := fun i k => by
    rw [supportGraph_adj hW.symm]
    constructor
    · exact fun h => h.2
    · intro h; refine ⟨fun hik => ?_, h⟩; subst hik; rw [hW.diag] at h; exact lt_irrefl _ h
  -- ordered sum = dart sum
  have h1 : ∑ i, ∑ k, (if 0 < w i k then g i k else 0) =
      ∑ d : G.Dart, Sym2.lift ⟨g, hg⟩ d.edge := by
    rw [← Finset.sum_product', ← Finset.sum_filter]
    refine (Finset.sum_bij (fun d _ => d.toProd) ?_ ?_ ?_ ?_).symm
    · intro d _
      simpa [hadj] using d.adj
    · intro d _ d' _ h; exact (SimpleGraph.Dart.ext_iff _ _).2 h
    · intro p hp
      exact ⟨⟨p, (hadj _ _).2 (Finset.mem_filter.1 hp).2⟩, Finset.mem_univ _, rfl⟩
    · intro d _
      simp [SimpleGraph.Dart.edge]
  have h2 : ∑ d : G.Dart, Sym2.lift ⟨g, hg⟩ d.edge =
      2 * ∑ e ∈ G.edgeFinset, Sym2.lift ⟨g, hg⟩ e := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := SimpleGraph.Dart.edge) (t := G.edgeFinset)
      (fun d _ => by simp [d.edge_mem]), Finset.mul_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [Finset.sum_congr rfl (fun d hd => by rw [(Finset.mem_filter.1 hd).2]), Finset.sum_const,
      G.dart_edge_fiber_card e (by simpa using he), nsmul_eq_mul]
    norm_num
  rw [edgeSum, h1, h2]
  ring

/-- `e^y - 1 - y ≤ ½ y² e^y` for `y ≥ 0`. -/
theorem exp_sub_one_sub_le (y : ℝ) (hy : 0 ≤ y) : exp y - 1 - y ≤ y ^ 2 / 2 * exp y := by
  -- `φ(y) = (1 + y) e^{-y} + y²/2` is nondecreasing on `[0, ∞)` with `φ 0 = 1`.
  set φ : ℝ → ℝ := fun y => (1 + y) * exp (-y) + y ^ 2 / 2
  have hd : ∀ y, HasDerivAt φ (y * (1 - exp (-y))) y := fun y => by
    have h1 := ((hasDerivAt_id y).const_add 1).mul ((hasDerivAt_neg y).exp)
    have h2 := (hasDerivAt_pow 2 y).div_const 2
    convert h1.add h2 using 1
    · funext z; simp only [φ, Pi.add_apply, Pi.mul_apply, id]
    · simp only [id]; norm_num; ring
  have hmono : MonotoneOn φ (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (fun y _ => (hd y).continuousAt.continuousWithinAt)
      (fun y _ => (hd y).differentiableAt.differentiableWithinAt) fun y hy' => ?_
    rw [interior_Ici] at hy'
    rw [(hd y).deriv]
    have : exp (-y) ≤ 1 := exp_le_one_iff.2 (by linarith [Set.mem_Ioi.1 hy'])
    exact mul_nonneg (le_of_lt hy') (by linarith)
  have h := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hy) hy
  simp only [φ, neg_zero, exp_zero, add_zero, mul_one, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, zero_div] at h
  have he := exp_pos y
  have : (1 + y) * exp (-y) * exp y = 1 + y := by rw [mul_assoc, ← exp_add]; simp
  nlinarith

/-- `R(h) ≤ ½ h² e^{|h|} cosh u` for the tangent-line remainder of `cosh` at `u`. -/
theorem remainder_le_exact (u h : ℝ) :
    cosh u * (cosh h - 1) + sinh u * (sinh h - h) ≤ h ^ 2 / 2 * exp |h| * cosh u := by
  have h1 := abs_sinh_le_cosh u
  have hc := (cosh_pos u).le
  have h3 : sinh u * (sinh h - h) ≤ cosh u * |sinh h - h| := by
    calc sinh u * (sinh h - h) ≤ |sinh u * (sinh h - h)| := le_abs_self _
      _ = |sinh u| * |sinh h - h| := abs_mul _ _
      _ ≤ cosh u * |sinh h - h| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  have h4 : cosh h - 1 + |sinh h - h| ≤ exp |h| - 1 - |h| := by
    rw [sinh_eq, cosh_eq]
    rcases le_total 0 h with hh | hh
    · rw [abs_of_nonneg hh]
      have : 0 ≤ (exp h - exp (-h)) / 2 - h := by
        have := self_le_sinh_iff.2 hh; rw [sinh_eq] at this; linarith
      rw [abs_of_nonneg this]; linarith
    · rw [abs_of_nonpos hh]
      have : (exp h - exp (-h)) / 2 - h ≤ 0 := by
        have := (self_le_sinh_iff (x := -h)).2 (by linarith)
        rw [sinh_eq, neg_neg] at this; linarith
      rw [abs_of_nonpos this]; linarith
  have h5 := exp_sub_one_sub_le |h| (abs_nonneg h)
  rw [sq_abs] at h5
  nlinarith

/-- **`lem:elem`(ii)** exactly as stated in the supplement: for `q > 1`, `γ ≥ 0`,
`y* = -(q-1) γ d` and `κ = ½ (q-1) q² γ² d² e^{q γ |d|}`,
`q cosh x - (q-1) cosh (x + γ d) ≥ (1 - κ) cosh (x + y*)`. -/
theorem cosh_combo_ge_exact {q γ : ℝ} (hq : 1 < q) (hγ : 0 ≤ γ) (x d : ℝ) :
    (1 - 1 / 2 * (q - 1) * q ^ 2 * γ ^ 2 * d ^ 2 * exp (q * γ * |d|)) *
        cosh (x + -((q - 1) * γ * d)) ≤
      q * cosh x - (q - 1) * cosh (x + γ * d) := by
  set u := x + -((q - 1) * γ * d)
  have hx : x = u + (q - 1) * γ * d := by simp [u]
  have hx' : x + γ * d = u + q * γ * d := by simp [u]; ring
  rw [hx', hx, cosh_add_eq u, cosh_add_eq u]
  have h0 := remainder_nonneg u ((q - 1) * γ * d)
  have h1 := remainder_le_exact u (q * γ * d)
  have habs : |q * γ * d| = q * γ * |d| := by
    rw [abs_mul, abs_mul, abs_of_pos (by linarith : (0:ℝ) < q), abs_of_nonneg hγ]
  rw [habs] at h1
  have : (q * γ * d) ^ 2 = q ^ 2 * γ ^ 2 * d ^ 2 := by ring
  rw [this] at h1
  have hq0 : 0 ≤ q - 1 := by linarith
  nlinarith [mul_le_mul_of_nonneg_left h1 hq0, mul_nonneg (by linarith : (0:ℝ) ≤ q) h0]

end ArborealDecay.TLaw
