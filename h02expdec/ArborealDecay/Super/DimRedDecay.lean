module

public import ArborealDecay.Super.DimRed
public import ArborealDecay.Super.ComposeTemp

/-!
# Decay of the `ℍ^{2|4}` integrand, and unconditional dimensional reduction

We discharge the decay hypothesis of `expectH_eq_expect` when `β ≥ 0` and every `h_i > 0`, for
*tame* observables: those whose smooth functions `g` have all derivatives polynomially bounded
(`Obs.Tame`; e.g. all polynomials in the `u_i · u_j` and `z_i`).

With `r_i = 1 + x_i² + y_i²`, the body of the action is
`Φ = ¼ ∑ β_{ij} (b_{ii} - b_{ij} - b_{ji} + b_{jj}) + ∑ h_i (√r_i - 1)` where
`b_{ij} = x_i x_j + y_i y_j - √r_i √r_j ≤ -1` and `b_{ii} = -1` (`body_dotH_le`,
`body_dotH_self`), so `Φ ≥ c ‖p‖ - C` with `c = min h_i` (`body_actionH_ge`).  Writing
`e^{-H} = e^{-Φ} · exp(soul(-H))` (`scomp_exp_eq_smul`), the integrand is
`e^{-Φ}` (in `Decay`) times a tempered superfunction (`STemp`), hence in `SDecay`
(`sdecay_integrandH`).
-/

@[expose] public section

namespace ArborealDecay.Super

noncomputable section

open MeasureTheory Finset
open scoped ContDiff

set_option linter.unusedSectionVars false

namespace H24

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ### Scalar estimates -/

/-- `r_i = 1 + x_i² + y_i²`. -/
def rr (i : Λ) (p : Pt Λ) : ℝ := 1 + p (.inl i) ^ 2 + p (.inr i) ^ 2

theorem one_le_rr (i : Λ) (p : Pt Λ) : 1 ≤ rr i p := by
  unfold rr; nlinarith [sq_nonneg (p (.inl i)), sq_nonneg (p (.inr i))]

theorem temp_rr (i : Λ) : Temp (rr i : Pt Λ → ℝ) :=
  ((Temp.const 1).add ((Temp.coord _).pow 2)).add ((Temp.coord _).pow 2)

theorem temp_quad (a b c d : Λ ⊕ Λ) : Temp fun p : Pt Λ => p a * p b + p c * p d :=
  ((Temp.coord a).mul (Temp.coord b)).add ((Temp.coord c).mul (Temp.coord d))

theorem iteratedDeriv_sqrt (k : ℕ) (t : ℝ) :
    iteratedDeriv k Real.sqrt t = (descPochhammer ℝ k).eval (1 / 2 : ℝ) * t ^ ((1 / 2 : ℝ) - k) := by
  have e : Real.sqrt = fun x : ℝ => x ^ (1 / 2 : ℝ) := funext Real.sqrt_eq_rpow
  rw [e, iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const]

theorem sqrt_deriv_bound (k : ℕ) :
    ∃ C : ℝ, ∃ m : ℕ, ∀ t ∈ Set.Ici (1 : ℝ), |iteratedDeriv k Real.sqrt t| ≤ C * (1 + |t|) ^ m := by
  refine ⟨|(descPochhammer ℝ k).eval (1 / 2 : ℝ)|, 1, fun t ht => ?_⟩
  have ht1 : (1 : ℝ) ≤ t := ht
  rw [iteratedDeriv_sqrt, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (by linarith) _), pow_one]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have h1 : t ^ ((1 / 2 : ℝ) - k) ≤ t ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le ht1 (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
  rw [Real.rpow_one] at h1
  rw [abs_of_pos (by linarith : (0 : ℝ) < t)]
  linarith

theorem inv_deriv_bound (k : ℕ) :
    ∃ C : ℝ, ∃ m : ℕ, ∀ t ∈ Set.Ici (1 : ℝ),
      |iteratedDeriv k (fun t : ℝ => t⁻¹) t| ≤ C * (1 + |t|) ^ m := by
  refine ⟨k.factorial, 0, fun t ht => ?_⟩
  have ht1 : (1 : ℝ) ≤ t := ht
  rw [iteratedDeriv_inv, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, pow_zero,
    mul_one, Nat.abs_cast, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < t ^ (k + 1))]
  have : 1 ≤ t ^ (k + 1) := one_le_pow₀ ht1
  have hf : (0 : ℝ) ≤ k.factorial := Nat.cast_nonneg _
  calc (k.factorial : ℝ) * (t ^ (k + 1))⁻¹ ≤ k.factorial * 1 :=
        mul_le_mul_of_nonneg_left (inv_le_one_of_one_le₀ this) hf
    _ = k.factorial := mul_one _

theorem temp_sqrt_rr (i : Λ) (k : ℕ) :
    Temp fun p : Pt Λ => iteratedDeriv k Real.sqrt (rr i p) :=
  temp_iteratedDeriv_comp isOpen_Ioi (fun _ ht => lt_of_lt_of_le one_pos ht) contDiffOn_sqrt
    sqrt_deriv_bound (temp_rr i) (one_le_rr i) k

/-! ### Tempered building blocks -/

theorem stemp_Rz (i : Λ) : STemp (Rz i) :=
  (((STemp.const 1).smul (temp_rr i)).sub (STemp.const _)).sub (STemp.const _)

theorem stemp_zH (i : Λ) : STemp (zH i) :=
  (stemp_Rz i).scomp (isEven_Rz i) fun k => by
    simp only [body_Rz]; exact temp_sqrt_rr i k

theorem one_le_body_zH (i : Λ) (p : Pt Λ) : 1 ≤ body (zH i p) := by
  rw [body_zH]; exact Real.one_le_sqrt.2 (one_le_rr i p)

theorem stemp_zinv (i : Λ) : STemp fun p => Ring.inverse (zH i p) := by
  simp_rw [inverse_zH]
  exact (stemp_zH i).scomp (isEven_zH i) fun k =>
    temp_iteratedDeriv_comp isOpen_Ioi (fun _ ht => lt_of_lt_of_le one_pos ht) contDiffOn_inv
      inv_deriv_bound (stemp_zH i).temp_body (one_le_body_zH i) k

theorem stemp_zinvProd : STemp (zinvProd : Pt Λ → A Λ) :=
  STemp.list_prod _ fun i _ => stemp_zinv i

theorem stemp_dotH (i j : Λ) : STemp (dotH i j) :=
  ((((STemp.const 1).smul (temp_quad _ _ _ _)).add (STemp.const _)).add (STemp.const _)).sub
    ((stemp_zH i).mul (stemp_zH j))

/-- Tame observables: every smooth function used has polynomially bounded derivatives. -/
def Obs.Tame : Obs Λ → Prop
  | .dot _ _ => True
  | .z _ => True
  | .const _ => True
  | .add a b => a.Tame ∧ b.Tame
  | .mul a b => a.Tame ∧ b.Tame
  | .comp g _ a =>
    (∀ k, ∃ C : ℝ, ∃ m : ℕ, ∀ t : ℝ, |iteratedDeriv k g t| ≤ C * (1 + |t|) ^ m) ∧ a.Tame

theorem stemp_obsH (o : Obs Λ) (ho : o.Tame) : STemp (obsH o) := by
  induction o with
  | dot i j => exact stemp_dotH i j
  | z i => exact stemp_zH i
  | const c => exact STemp.const _
  | add a b ha hb => exact (ha ho.1).add (hb ho.2)
  | mul a b ha hb => exact (ha ho.1).mul (hb ho.2)
  | comp g hg a ha =>
    have hbd : ∀ k, ∃ C : ℝ, ∃ m : ℕ, ∀ t ∈ (Set.univ : Set ℝ),
        |iteratedDeriv k g t| ≤ C * (1 + |t|) ^ m := fun k => by
      obtain ⟨C, m, h⟩ := ho.1 k; exact ⟨C, m, fun t _ => h t⟩
    exact (ha ho.2).scomp (fun p => Obs.isEven_eval (fun i j => isEven_dotH i j p)
      (fun i => isEven_zH i p) a) fun k =>
        temp_iteratedDeriv_comp isOpen_univ subset_rfl hg.contDiffOn hbd (ha ho.2).temp_body
          (fun _ => Set.mem_univ _) k

theorem stemp_actionH (β : Λ → Λ → ℝ) (h : Λ → ℝ) : STemp (actionH β h) := by
  refine (STemp.const_smul (STemp.sum _ fun i _ => STemp.sum _ fun j _ => ?_) _).add
    (STemp.sum _ fun i _ => ((stemp_zH i).sub (STemp.const 1)).const_smul _)
  exact ((((stemp_dotH i i).sub (stemp_dotH i j)).sub (stemp_dotH j i)).add
    (stemp_dotH j j)).const_smul _

/-! ### The body of the action -/

theorem body_dotH (i j : Λ) (p : Pt Λ) :
    body (dotH i j p) = p (.inl i) * p (.inl j) + p (.inr i) * p (.inr j) -
      √(rr i p) * √(rr j p) := by
  simp only [dotH, ξ1, η1, ξ, η, map_sub, map_add, map_smul, map_mul, body_gen, body_one,
    smul_eq_mul, mul_one, mul_zero, sub_zero, add_zero, body_zH, rr]

theorem body_dotH_self (i : Λ) (p : Pt Λ) : body (dotH i i p) = -1 := by
  rw [body_dotH, Real.mul_self_sqrt (by linarith [one_le_rr i p]), rr]; ring

theorem body_dotH_le (i j : Λ) (p : Pt Λ) : body (dotH i j p) ≤ -1 := by
  rw [body_dotH]
  have h1 : (1 + p (.inl i) * p (.inl j) + p (.inr i) * p (.inr j)) ^ 2 ≤ rr i p * rr j p := by
    unfold rr
    nlinarith [sq_nonneg (p (.inl i) - p (.inl j)), sq_nonneg (p (.inr i) - p (.inr j)),
      sq_nonneg (p (.inl i) * p (.inr j) - p (.inr i) * p (.inl j))]
  have h2 := Real.abs_le_sqrt h1
  rw [Real.sqrt_mul (by linarith [one_le_rr i p])] at h2
  linarith [le_abs_self (1 + p (.inl i) * p (.inl j) + p (.inr i) * p (.inr j))]

theorem body_actionH (β : Λ → Λ → ℝ) (h : Λ → ℝ) (p : Pt Λ) :
    body (actionH β h p) = (1 / 4 : ℝ) * ∑ i, ∑ j, β i j * (body (dotH i i p) -
      body (dotH i j p) - body (dotH j i p) + body (dotH j j p)) +
      ∑ i, h i * (√(rr i p) - 1) := by
  simp only [actionH, map_add, map_smul, map_sum, map_sub, smul_eq_mul, body_zH, body_one, rr]

theorem norm_le_sum_sqrt (p : Pt Λ) : ‖p‖ ≤ ∑ i, √(rr i p) := by
  have hnn : ∀ i, 0 ≤ √(rr i p) := fun i => Real.sqrt_nonneg _
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => hnn i)).2 fun k => ?_
  rw [Real.norm_eq_abs]
  have hle : ∀ i, √(rr i p) ≤ ∑ j, √(rr j p) := fun i =>
    Finset.single_le_sum (f := fun j => √(rr j p)) (fun j _ => hnn j) (mem_univ i)
  rcases k with i | i
  · exact (Real.abs_le_sqrt (by unfold rr; nlinarith [sq_nonneg (p (.inr i))])).trans (hle i)
  · exact (Real.abs_le_sqrt (by unfold rr; nlinarith [sq_nonneg (p (.inl i))])).trans (hle i)

theorem q_symm (i j : Λ) (p : Pt Λ) : body (dotH j i p) = body (dotH i j p) := by
  rw [body_dotH, body_dotH]; ring

/-- Weak triangle inequality on the hyperboloid: `z_i ≤ 2 (-u_i · u_j) z_j`. -/
theorem sqrt_rr_le (i j : Λ) (p : Pt Λ) :
    √(rr i p) ≤ 2 * -body (dotH i j p) * √(rr j p) := by
  rw [body_dotH]
  set xi := p (.inl i); set yi := p (.inr i); set xj := p (.inl j); set yj := p (.inr j)
  set zi := √(rr i p); set zj := √(rr j p)
  set t := √(xi ^ 2 + yi ^ 2); set s := √(xj ^ 2 + yj ^ 2)
  have hzi : zi ^ 2 = 1 + t ^ 2 := by
    simp only [zi, t, rr]; rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]; ring
  have hzj : zj ^ 2 = 1 + s ^ 2 := by
    simp only [zj, s, rr]; rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]; ring
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hzi0 : 0 ≤ zi := Real.sqrt_nonneg _
  have hzj0 : 0 ≤ zj := Real.sqrt_nonneg _
  have hts : xi * xj + yi * yj ≤ t * s := by
    have h1 : (xi * xj + yi * yj) ^ 2 ≤ (t * s) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
      nlinarith [sq_nonneg (xi * yj - yi * xj)]
    exact abs_le_of_sq_le_sq' h1 (by positivity) |>.2
  have htz : t ≤ zi := by nlinarith
  have key : 0 ≤ zi * (zj - s) ^ 2 := by positivity
  nlinarith [mul_nonneg hzj0 (sub_nonneg.2 htz), mul_nonneg hzj0 hs0]

theorem summand_nonneg {β : Λ → Λ → ℝ} (hβ : ∀ i j, 0 ≤ β i j) (i j : Λ) (p : Pt Λ) :
    0 ≤ β i j * (body (dotH i i p) - body (dotH i j p) - body (dotH j i p) + body (dotH j j p)) := by
  refine mul_nonneg (hβ i j) ?_
  rw [body_dotH_self, body_dotH_self]
  linarith [body_dotH_le i j p, body_dotH_le j i p]

theorem hsummand_nonneg {h : Λ → ℝ} (hh : ∀ i, 0 ≤ h i) (i : Λ) (p : Pt Λ) :
    0 ≤ h i * (√(rr i p) - 1) :=
  mul_nonneg (hh i) (by linarith [Real.one_le_sqrt.2 (one_le_rr i p)])

theorem body_actionH_nonneg {β : Λ → Λ → ℝ} (hβ : ∀ i j, 0 ≤ β i j) {h : Λ → ℝ}
    (hh : ∀ i, 0 ≤ h i) (p : Pt Λ) : 0 ≤ body (actionH β h p) := by
  rw [body_actionH]
  have := Finset.sum_nonneg fun i (_ : i ∈ univ) =>
    Finset.sum_nonneg fun j (_ : j ∈ univ) => summand_nonneg hβ i j p
  have := Finset.sum_nonneg fun i (_ : i ∈ univ) => hsummand_nonneg hh i p
  positivity

theorem edge_le_body_actionH {β : Λ → Λ → ℝ} (hβ : ∀ i j, 0 ≤ β i j) {h : Λ → ℝ}
    (hh : ∀ i, 0 ≤ h i) (i j : Λ) (p : Pt Λ) :
    β i j / 2 * (-body (dotH i j p) - 1) ≤ body (actionH β h p) := by
  rw [body_actionH]
  have h1 := Finset.single_le_sum (f := fun j => β i j * (body (dotH i i p) - body (dotH i j p) -
    body (dotH j i p) + body (dotH j j p))) (fun j _ => summand_nonneg hβ i j p) (mem_univ j)
  have h2 := Finset.single_le_sum (f := fun i => ∑ j, β i j * (body (dotH i i p) -
    body (dotH i j p) - body (dotH j i p) + body (dotH j j p)))
    (fun i _ => Finset.sum_nonneg fun j _ => summand_nonneg hβ i j p) (mem_univ i)
  have h3 := Finset.sum_nonneg fun i (_ : i ∈ univ) => hsummand_nonneg hh i p
  have e : body (dotH i i p) - body (dotH i j p) - body (dotH j i p) + body (dotH j j p) =
      2 * (-body (dotH i j p) - 1) := by
    rw [body_dotH_self, body_dotH_self, q_symm i j]; ring
  rw [e] at h1
  nlinarith

theorem field_le_body_actionH {β : Λ → Λ → ℝ} (hβ : ∀ i j, 0 ≤ β i j) {h : Λ → ℝ}
    (hh : ∀ i, 0 ≤ h i) (i : Λ) (p : Pt Λ) :
    h i * (√(rr i p) - 1) ≤ body (actionH β h p) := by
  rw [body_actionH]
  have h1 := Finset.single_le_sum (f := fun i => h i * (√(rr i p) - 1))
    (fun i _ => hsummand_nonneg hh i p) (mem_univ i)
  have := Finset.sum_nonneg fun i (_ : i ∈ univ) =>
    Finset.sum_nonneg fun j (_ : j ∈ univ) => summand_nonneg hβ i j p
  nlinarith

/-- Every vertex is joined by a path of positive couplings to a vertex with positive field.
This is the irreducibility condition of BCHS (2.42) ff.: `β ≥ 0` irreducible and `h ≥ 0`,
`h ≠ 0` (it also holds when every `h_i > 0`). -/
def Pinned (β : Λ → Λ → ℝ) (h : Λ → ℝ) : Prop :=
  ∀ i, ∃ k, 0 < h k ∧ Relation.ReflTransGen (fun a b => 0 < β a b) i k

theorem pinned_of_pos {β : Λ → Λ → ℝ} {h : Λ → ℝ} (hh : ∀ i, 0 < h i) : Pinned β h :=
  fun i => ⟨i, hh i, Relation.ReflTransGen.refl⟩

/-- `z_i` is dominated by a power of `1 + Φ`. -/
theorem sqrt_rr_dom {β : Λ → Λ → ℝ} (hβ : ∀ i j, 0 ≤ β i j) {h : Λ → ℝ} (hh : ∀ i, 0 ≤ h i)
    (hP : Pinned β h) (i : Λ) :
    ∃ C : ℝ, ∃ M : ℕ, ∀ p, √(rr i p) ≤ C * (1 + body (actionH β h p)) ^ M := by
  obtain ⟨k, hk, hpath⟩ := hP i
  induction hpath using Relation.ReflTransGen.head_induction_on with
  | refl =>
    refine ⟨1 + 1 / h k, 1, fun p => ?_⟩
    have h1 := field_le_body_actionH hβ hh k p
    have h0 := body_actionH_nonneg hβ hh p
    rw [pow_one]
    have h3 : √(rr k p) - 1 ≤ body (actionH β h p) / h k := by rw [le_div_iff₀ hk]; linarith
    have h4 : body (actionH β h p) / h k = (1 / h k) * body (actionH β h p) := by ring
    have h5 : 0 ≤ 1 / h k := by positivity
    nlinarith
  | @head a b hab _ ih =>
    obtain ⟨C, M, hCM⟩ := ih
    refine ⟨2 * (1 + 2 / β a b) * C, M + 1, fun p => ?_⟩
    have hβab : 0 < β a b := hab
    have h0 := body_actionH_nonneg hβ hh p
    have he := edge_le_body_actionH hβ hh a b p
    have hq : -body (dotH a b p) ≤ (1 + 2 / β a b) * (1 + body (actionH β h p)) := by
      have : -body (dotH a b p) - 1 ≤ 2 / β a b * body (actionH β h p) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hβab]; linarith
      nlinarith [div_pos two_pos hβab]
    have hq1 : 1 ≤ -body (dotH a b p) := by linarith [body_dotH_le a b p]
    have hz := sqrt_rr_le a b p
    have hzb := hCM p
    have hzb0 : 0 ≤ √(rr b p) := Real.sqrt_nonneg _
    calc √(rr a p) ≤ 2 * -body (dotH a b p) * √(rr b p) := hz
      _ ≤ 2 * ((1 + 2 / β a b) * (1 + body (actionH β h p))) *
          (C * (1 + body (actionH β h p)) ^ M) := by gcongr
      _ = 2 * (1 + 2 / β a b) * C * (1 + body (actionH β h p)) ^ (M + 1) := by ring

theorem norm_dom {β : Λ → Λ → ℝ} (hβ : ∀ i j, 0 ≤ β i j) {h : Λ → ℝ} (hh : ∀ i, 0 ≤ h i)
    (hP : Pinned β h) :
    ∃ C : ℝ, ∃ M : ℕ, ∀ p : Pt Λ, 1 + ‖p‖ ≤ C * (1 + body (actionH β h p)) ^ M := by
  choose C M hCM using sqrt_rr_dom hβ hh hP
  refine ⟨1 + ∑ i, |C i|, ∑ i, M i, fun p => ?_⟩
  set Y := 1 + body (actionH β h p)
  have hY : 1 ≤ Y := by linarith [body_actionH_nonneg hβ hh p]
  have hYM : ∀ i, Y ^ M i ≤ Y ^ ∑ j, M j := fun i =>
    pow_le_pow_right₀ hY (Finset.single_le_sum (f := M) (fun _ _ => Nat.zero_le _) (mem_univ i))
  have hYpos : 1 ≤ Y ^ ∑ j, M j := one_le_pow₀ hY
  have h1 : ∀ i, √(rr i p) ≤ |C i| * Y ^ ∑ j, M j := fun i =>
    (hCM i p).trans ((mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)).trans
      (mul_le_mul_of_nonneg_left (hYM i) (abs_nonneg _)))
  calc 1 + ‖p‖ ≤ 1 + ∑ i, √(rr i p) := by linarith [norm_le_sum_sqrt p]
    _ ≤ Y ^ ∑ j, M j + ∑ i, |C i| * Y ^ ∑ j, M j := add_le_add hYpos (Finset.sum_le_sum
        fun i _ => h1 i)
    _ = (1 + ∑ i, |C i|) * Y ^ ∑ j, M j := by rw [← Finset.sum_mul]; ring

/-! ### Decay of the integrand -/

theorem integrandF_eq (β : Λ → Λ → ℝ) (h : Λ → ℝ) (F : Pt Λ → A Λ) (p : Pt Λ) :
    integrandF β h F p = Real.exp (-body (actionH β h p)) •
      (zinvProd p * (F p * scomp Real.exp (soul (-actionH β h p)))) := by
  rw [integrandF, scomp_exp_eq_smul (isEven_actionH β h p).neg, map_neg, mul_smul_comm,
    mul_smul_comm]

/-- The `ℍ^{2|4}` integrand of a tempered superfunction decays when `β ≥ 0`, `h ≥ 0` and every
vertex is joined by positive couplings to a vertex with positive field (`Pinned`). -/
theorem sdecay_integrandF {β : Λ → Λ → ℝ} (hβ : ∀ i j, 0 ≤ β i j) {h : Λ → ℝ}
    (hh : ∀ i, 0 ≤ h i) (hP : Pinned β h) {F : Pt Λ → A Λ} (hF : STemp F) :
    SDecay (integrandF β h F) := by
  obtain ⟨C, M, hdom⟩ := norm_dom hβ hh hP
  rw [show integrandF β h F = fun p => Real.exp (-body (actionH β h p)) •
    (zinvProd p * (F p * scomp Real.exp (soul (-actionH β h p)))) from
    funext (integrandF_eq β h F)]
  refine SDecay.of_decay_smul (decay_exp_neg (stemp_actionH β h).temp_body
    (body_actionH_nonneg hβ hh) hdom) ?_
  exact stemp_zinvProd.mul (hF.mul
    ((stemp_actionH β h).neg.scomp_exp_soul fun p => (isEven_actionH β h p).neg))

/-- The `ℍ^{2|4}` integrand of a tame observable decays under `Pinned`. -/
theorem sdecay_integrandH {β : Λ → Λ → ℝ} (hβ : ∀ i j, 0 ≤ β i j) {h : Λ → ℝ}
    (hh : ∀ i, 0 ≤ h i) (hP : Pinned β h) (o : Obs Λ) (ho : o.Tame) :
    SDecay (integrandH β h o) :=
  sdecay_integrandF hβ hh hP (stemp_obsH o ho)

/-- **BCHS Proposition 2.7 (dimensional reduction), unconditional form.**  Let `β ≥ 0`, `h ≥ 0`,
and suppose every vertex is joined by a path of positive couplings `β` to a vertex with positive
field (`Pinned`; e.g. `β` irreducible and `h ≠ 0`, or all `h_i > 0`).  Then for every tame
observable `o` (in particular every polynomial in the `u_i · u_j` and `z_i`),
`[o]^{ℍ^{2|4}}_{β,h} = [o]^{ℍ^{0|2}}_{β,h}`. -/
theorem expectH_eq_expect_of_pinned {β : Λ → Λ → ℝ} (hβ : ∀ i j, 0 ≤ β i j) {h : Λ → ℝ}
    (hh : ∀ i, 0 ≤ h i) (hP : Pinned β h) (o : Obs Λ) (ho : o.Tame) :
    expectH β h (obsH o) = H02.expect β h (obs0 o) :=
  expectH_eq_expect β h o (sdecay_integrandH hβ hh hP o ho)

end H24

end

end ArborealDecay.Super

end
