module

public import ArborealDecay.TLaw.Integral

/-!
# Finiteness and positivity of `Z` (supplement `lem:C-integrable`, exponential moments)

For a connected weighted graph and `a ≥ 0`:

* `lintegral_exp_mul_density_lt_top`: `∫ e^{λ·τ} e^{-Φ(τ̂)} D(τ̂)^a dμ_ρ < ∞` for every
  `λ ∈ ℝ^{V∖ρ}` (the part of `eq:expmom` without the `‖𝓛⁻¹‖` factor);
* `Z_lt_top`, `Z_pos`: `0 < Z^ρ_{w,a} < ∞`.

Proof as in `lem:C-integrable`: choose for every `i ≠ ρ` a support neighbour `p(i)` closer to
`ρ` (graph distance), pass to the coordinates `d_i = τ̂_i - τ̂_{p(i)}` (an injective linear map,
so Lebesgue measure is mapped to a multiple of itself), bound
`Φ ≥ ½ ∑_i w_{i p(i)} (cosh d_i - 1)`, `|τ̂_i| ≤ N ∑_k |d_k|` and `D ≤ W e^{K₀ N ∑|d_k|}`,
and integrate a product of one-dimensional Gaussian-dominated functions.
-/

open Finset Matrix Real MeasureTheory

set_option linter.unusedSectionVars false

@[expose] public section

namespace ArborealDecay.TLaw

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_parent {G : SimpleGraph V} (hconn : G.Connected) {ρ i : V} (hi : i ≠ ρ) :
    ∃ j, G.Adj i j ∧ G.dist j ρ < G.dist i ρ := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist i ρ
  cases p with
  | nil => exact absurd rfl hi
  | cons h p' =>
    refine ⟨_, h, ?_⟩
    have := SimpleGraph.dist_le p'
    rw [SimpleGraph.Walk.length_cons] at hp
    omega

/-- The tree coordinates `d_i = τ̂_i - τ̂_{p(i)}`. -/
noncomputable def diffMap (ρ : V) (par : {i // i ≠ ρ} → V) :
    ({i // i ≠ ρ} → ℝ) →ₗ[ℝ] ({i // i ≠ ρ} → ℝ) where
  toFun τ i := ext ρ τ i - ext ρ τ (par i)
  map_add' τ σ := by
    funext i
    simp only [ext, Pi.add_apply]
    split_ifs <;> ring
  map_smul' c τ := by
    funext i
    simp only [ext, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem diffMap_apply (ρ : V) (par : {i // i ≠ ρ} → V) (τ : {i // i ≠ ρ} → ℝ)
    (i : {i // i ≠ ρ}) : diffMap ρ par τ i = ext ρ τ i - ext ρ τ (par i) := rfl

theorem abs_ext_le {G : SimpleGraph V} {ρ : V} {par : {i // i ≠ ρ} → V}
    (hpar : ∀ i : {i // i ≠ ρ}, G.dist (par i) ρ < G.dist (i : V) ρ) (τ : {i // i ≠ ρ} → ℝ)
    (i : V) : |ext ρ τ i| ≤ G.dist i ρ * ∑ k, |diffMap ρ par τ k| := by
  set S := ∑ k, |diffMap ρ par τ k|
  have hS : 0 ≤ S := Finset.sum_nonneg fun k _ => abs_nonneg _
  induction hn : G.dist i ρ using Nat.strong_induction_on generalizing i with
  | _ n ih =>
    by_cases hi : i = ρ
    · subst hi; simp only [ext_root, abs_zero]; positivity
    · have hd := hpar ⟨i, hi⟩
      have e : ext ρ τ i = diffMap ρ par τ ⟨i, hi⟩ + ext ρ τ (par ⟨i, hi⟩) := by
        rw [diffMap_apply]; ring
      have h1 := ih _ (hn ▸ hd) (par ⟨i, hi⟩) rfl
      have h2 : |diffMap ρ par τ ⟨i, hi⟩| ≤ S :=
        Finset.single_le_sum (f := fun k => |diffMap ρ par τ k|) (fun k _ => abs_nonneg _)
          (mem_univ _)
      have hn' : ((G.dist (par ⟨i, hi⟩) ρ : ℕ) : ℝ) + 1 ≤ n := by
        rw [← hn]; exact_mod_cast hd
      rw [e]
      calc |diffMap ρ par τ ⟨i, hi⟩ + ext ρ τ (par ⟨i, hi⟩)|
          ≤ |diffMap ρ par τ ⟨i, hi⟩| + |ext ρ τ (par ⟨i, hi⟩)| := abs_add_le _ _
        _ ≤ S + G.dist (par ⟨i, hi⟩) ρ * S := add_le_add h2 h1
        _ = ((G.dist (par ⟨i, hi⟩) ρ : ℕ) + 1 : ℝ) * S := by ring
        _ ≤ n * S := mul_le_mul_of_nonneg_right hn' hS

theorem diffMap_injective {G : SimpleGraph V} {ρ : V} {par : {i // i ≠ ρ} → V}
    (hpar : ∀ i : {i // i ≠ ρ}, G.dist (par i) ρ < G.dist (i : V) ρ) :
    Function.Injective (diffMap ρ par) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro τ hτ
  funext k
  have h := abs_ext_le hpar τ k
  simp only [hτ, Pi.zero_apply, abs_zero, Finset.sum_const_zero, mul_zero] at h
  show τ k = 0
  rw [← ext_val ρ τ k]
  exact abs_nonpos_iff.1 h

/-- `Φ_w(t) ≥ ½ ∑_{i ≠ ρ} w_{i p(i)} (cosh (t_i - t_{p(i)}) - 1)`. -/
theorem Phi_ge {w : V → V → ℝ} (hW : IsWGraph w) {ρ : V} (par : {i // i ≠ ρ} → V)
    (t : V → ℝ) :
    (1 / 2) * ∑ i : {i // i ≠ ρ}, w i (par i) * (cosh (t i - t (par i)) - 1) ≤ Phi w t := by
  have hnn : ∀ i k, 0 ≤ w i k * (cosh (t i - t k) - 1) := fun i k =>
    mul_nonneg (hW.nonneg i k) (by linarith [one_le_cosh (t i - t k)])
  unfold Phi
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  calc ∑ i : {i // i ≠ ρ}, w i (par i) * (cosh (t i - t (par i)) - 1)
      ≤ ∑ i : {i // i ≠ ρ}, ∑ k, w i k * (cosh (t i - t k) - 1) :=
        Finset.sum_le_sum fun i _ => Finset.single_le_sum
          (f := fun k => w i k * (cosh (t i - t k) - 1)) (fun k _ => hnn i k) (mem_univ _)
    _ = ∑ i ∈ univ.erase ρ, ∑ k, w i k * (cosh (t i - t k) - 1) :=
        (Finset.sum_subtype (univ.erase ρ) (p := fun i => i ≠ ρ) (fun x => by simp)
          (fun i => ∑ k, w i k * (cosh (t i - t k) - 1))).symm
    _ ≤ ∑ i, ∑ k, w i k * (cosh (t i - t k) - 1) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          fun i _ _ => Finset.sum_nonneg fun k _ => hnn i k

open Classical in
/-- `D(t) ≤ W e^{K₀ B}` when `|t_i| ≤ B` for all `i`, with `W = ∑_T w(T)` and
`K₀ = 2 (|Sym2 V| + |V ∖ ρ|)`. -/
theorem D_le_of_abs_le {w : V → V → ℝ} (hW : IsWGraph w) (ρ : V) (t : V → ℝ) {B : ℝ}
    (hB : ∀ i, |t i| ≤ B) :
    D w ρ t ≤ (∑ T : SimpleGraph V with T.IsTree, ∏ e ∈ T.edgeFinset, Sym2.lift ⟨w, hW.symm⟩ e) *
      exp (2 * (Fintype.card (Sym2 V) + Fintype.card {i // i ≠ ρ}) * B) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB ρ)
  rw [D_eq_treeSum w hW.symm hW.diag, Finset.sum_mul]
  refine Finset.sum_le_sum fun T _ => mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_)
    (Finset.prod_nonneg fun e _ => by
      induction e using Sym2.ind with
      | h i k => exact hW.nonneg i k)
  unfold treeExp
  have h1 : ∑ e ∈ T.edgeFinset, Sym2.lift ⟨fun i k => t i + t k, fun _ _ => add_comm _ _⟩ e ≤
      Fintype.card (Sym2 V) * (2 * B) := by
    calc ∑ e ∈ T.edgeFinset, Sym2.lift ⟨fun i k => t i + t k, fun _ _ => add_comm _ _⟩ e
        ≤ ∑ e ∈ T.edgeFinset, 2 * B := Finset.sum_le_sum fun e _ => by
          induction e using Sym2.ind with
          | h i k =>
            simp only [Sym2.lift_mk]
            linarith [(abs_le.1 (hB i)).2, (abs_le.1 (hB k)).2]
      _ = T.edgeFinset.card * (2 * B) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Fintype.card (Sym2 V) * (2 * B) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact_mod_cast Finset.card_le_univ _
  have h2 : -(2 * ∑ i : {i // i ≠ ρ}, t i) ≤ 2 * (Fintype.card {i // i ≠ ρ} * B) := by
    have : -∑ i : {i // i ≠ ρ}, t i ≤ ∑ i : {i // i ≠ ρ}, B := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum fun i _ => by linarith [(abs_le.1 (hB i)).1]
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at this
    linarith
  linarith

/-- One-dimensional integrability: `x ↦ e^{K|x| - c(cosh x - 1)}` is integrable for `c > 0`. -/
theorem integrable_exp_abs_sub_cosh {K c : ℝ} (hc : 0 < c) :
    Integrable fun x : ℝ => exp (K * |x| - c * (cosh x - 1)) := by
  have hint := (integrable_exp_neg_mul_sq (b := c / 8) (by positivity)).const_mul
    (exp (2 * K ^ 2 / c + 2 * c))
  refine hint.mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), ← exp_add]
  refine exp_le_exp.2 ?_
  have hcosh : (1 + |x| + |x| ^ 2 / 2) / 2 ≤ cosh x := by
    rw [← cosh_abs, cosh_eq]
    have := quadratic_le_exp_of_nonneg (abs_nonneg x)
    linarith [exp_pos (-|x|)]
  have hx2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  have hamgm : K * |x| ≤ 2 * K ^ 2 / c + c * |x| ^ 2 / 8 := by
    have h := sq_nonneg (4 * K - c * |x|)
    have : 2 * K ^ 2 / c + c * |x| ^ 2 / 8 - K * |x| = (4 * K - c * |x|) ^ 2 / (8 * c) := by
      field_simp; ring
    have : 0 ≤ (4 * K - c * |x|) ^ 2 / (8 * c) := by positivity
    linarith
  rw [hx2]
  nlinarith [abs_nonneg x]

theorem continuous_exp_abs_sub_cosh (K c : ℝ) :
    Continuous fun x : ℝ => exp (K * |x| - c * (cosh x - 1)) := by fun_prop

/-- **Exponential moments** (`lem:C-integrable`, without the `‖𝓛⁻¹‖` factor): for a connected
weighted graph, `a ≥ 0` and any `λ`, `∫ e^{λ·τ} density < ∞`. -/
theorem lintegral_exp_mul_density_lt_top {w : V → V → ℝ} (hW : IsWGraph w)
    (hconn : (supportGraph w).Connected) (ρ : V) {a : ℝ} (ha : 0 ≤ a)
    (lam : {i // i ≠ ρ} → ℝ) :
    ∫⁻ τ, ENNReal.ofReal (exp (∑ i, lam i * τ i) * density w ρ a τ) < ⊤ := by
  classical
  set G := supportGraph w
  choose par hpar using fun i : {i // i ≠ ρ} => exists_parent hconn i.2
  have hpar' : ∀ i : {i // i ≠ ρ}, G.dist (par i) ρ < G.dist (i : V) ρ := fun i => (hpar i).2
  have hc : ∀ i : {i // i ≠ ρ}, 0 < w i (par i) := fun i =>
    ((supportGraph_adj hW.symm).1 (hpar i).1).2
  set L := diffMap ρ par
  have hinj : Function.Injective L := diffMap_injective hpar'
  -- constants
  set N : ℝ := ∑ i, (G.dist i ρ : ℝ)
  have hN : ∀ i, (G.dist i ρ : ℝ) ≤ N := fun i =>
    Finset.single_le_sum (f := fun i => (G.dist i ρ : ℝ)) (fun _ _ => by positivity) (mem_univ i)
  set W := ∑ T : SimpleGraph V with T.IsTree, ∏ e ∈ T.edgeFinset, Sym2.lift ⟨w, hW.symm⟩ e
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun T _ => Finset.prod_nonneg fun e _ => by
    induction e using Sym2.ind with
    | h i k => exact hW.nonneg i k
  set K₀ : ℝ := 2 * (Fintype.card (Sym2 V) + Fintype.card {i // i ≠ ρ})
  set Λ₁ : ℝ := ∑ i, |lam i|
  set K : ℝ := Λ₁ * N + a * (K₀ * N)
  set C : ℝ := normC ρ * W ^ a
  set g : {i // i ≠ ρ} → ℝ → ℝ := fun i x => exp (K * |x| - (1 / 2 * w i (par i)) * (cosh x - 1))
  set F : ({i // i ≠ ρ} → ℝ) → ℝ := fun d => ∏ i, g i (d i)
  -- pointwise bound
  have hpt : ∀ τ, exp (∑ i, lam i * τ i) * density w ρ a τ ≤ C * F (L τ) := by
    intro τ
    set S := ∑ k, |L τ k|
    have hS : 0 ≤ S := Finset.sum_nonneg fun k _ => abs_nonneg _
    have hext : ∀ i, |ext ρ τ i| ≤ N * S := fun i =>
      (abs_ext_le hpar' τ i).trans (mul_le_mul_of_nonneg_right (hN i) hS)
    -- the three factors
    have hlam : ∑ i, lam i * τ i ≤ Λ₁ * N * S := by
      calc ∑ i, lam i * τ i ≤ ∑ i, |lam i| * (N * S) := Finset.sum_le_sum fun i _ => by
            have h := hext i
            rw [ext_val] at h
            calc lam i * τ i ≤ |lam i * τ i| := le_abs_self _
              _ = |lam i| * |τ i| := abs_mul _ _
              _ ≤ |lam i| * (N * S) := mul_le_mul_of_nonneg_left h (abs_nonneg _)
        _ = Λ₁ * N * S := by rw [← Finset.sum_mul]; ring
    have hD := D_le_of_abs_le hW ρ (ext ρ τ) hext
    have hDa : D w ρ (ext ρ τ) ^ a ≤ W ^ a * exp (a * (K₀ * N * S)) := by
      calc D w ρ (ext ρ τ) ^ a ≤ (W * exp (K₀ * (N * S))) ^ a :=
            rpow_le_rpow (D_nonneg hW ρ _) hD ha
        _ = W ^ a * exp (a * (K₀ * N * S)) := by
            rw [mul_rpow hW0 (exp_pos _).le, ← exp_mul]; ring_nf
    have hPhi := Phi_ge hW par (ext ρ τ)
    have hF : exp (K * S - (1 / 2) * ∑ i : {i // i ≠ ρ},
        w i (par i) * (cosh (ext ρ τ i - ext ρ τ (par i)) - 1)) = F (L τ) := by
      simp only [F, g, ← exp_sum]
      congr 1
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [diffMap_apply]; ring
    rw [← hF]
    unfold density
    simp only [C]
    have hC0 : 0 ≤ normC ρ := (normC_pos ρ).le
    calc exp (∑ i, lam i * τ i) * (exp (-Phi w (ext ρ τ)) * D w ρ (ext ρ τ) ^ a * normC ρ)
        ≤ exp (Λ₁ * N * S) * (exp (-((1 / 2) * ∑ i : {i // i ≠ ρ},
            w i (par i) * (cosh (ext ρ τ i - ext ρ τ (par i)) - 1))) *
              (W ^ a * exp (a * (K₀ * N * S))) * normC ρ) := by
          have hDn : 0 ≤ D w ρ (ext ρ τ) ^ a := rpow_nonneg (D_nonneg hW ρ _) _
          gcongr
      _ = normC ρ * W ^ a * exp (K * S - (1 / 2) * ∑ i : {i // i ≠ ρ},
            w i (par i) * (cosh (ext ρ τ i - ext ρ τ (par i)) - 1)) := by
          rw [show K * S - (1 / 2) * ∑ i : {i // i ≠ ρ},
              w i (par i) * (cosh (ext ρ τ i - ext ρ τ (par i)) - 1) =
              Λ₁ * N * S + (-((1 / 2) * ∑ i : {i // i ≠ ρ},
                w i (par i) * (cosh (ext ρ τ i - ext ρ τ (par i)) - 1)) + a * (K₀ * N * S)) by
            simp only [K]; ring]
          rw [exp_add, exp_add]; ring
  -- integrability of `F`
  have hFint : Integrable F := by
    have := Integrable.fintype_prod (μ := fun _ : {i // i ≠ ρ} => (volume : Measure ℝ))
      (f := g) fun i => by
        simp only [g]
        exact integrable_exp_abs_sub_cosh (by have := hc i; positivity)
    simpa [F, volume_pi] using this
  have hFc : Continuous F := by
    simp only [F, g]
    exact continuous_finsetProd _ fun i _ =>
      (continuous_exp_abs_sub_cosh _ _).comp (continuous_apply i)
  have hFnn : ∀ d, 0 ≤ F d := fun d => Finset.prod_nonneg fun i _ => (exp_pos _).le
  -- change of variables
  have hdet : LinearMap.det L ≠ 0 := by
    have h := (LinearEquiv.ofInjectiveEndo L hinj).isUnit_det'
    have he : ((LinearEquiv.ofInjectiveEndo L hinj : _ ≃ₗ[ℝ] _) : _ →ₗ[ℝ] _) = L := by
      ext x; simp [LinearEquiv.coe_ofInjectiveEndo]
    rw [he] at h
    exact h.ne_zero
  have hLc : Continuous L := LinearMap.continuous_of_finiteDimensional L
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure ({i // i ≠ ρ} → ℝ)) hdet
  have hcomp : ∫⁻ τ, ENNReal.ofReal (F (L τ)) =
      ENNReal.ofReal |(LinearMap.det L)⁻¹| * ∫⁻ d, ENNReal.ofReal (F d) := by
    rw [← lintegral_map (f := fun d => ENNReal.ofReal (F d)) hFc.measurable.ennreal_ofReal
      hLc.measurable, hmap, lintegral_smul_measure, smul_eq_mul]
  calc ∫⁻ τ, ENNReal.ofReal (exp (∑ i, lam i * τ i) * density w ρ a τ)
      ≤ ∫⁻ τ, ENNReal.ofReal C * ENNReal.ofReal (F (L τ)) := lintegral_mono fun τ => by
        rw [← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal (hpt τ)
    _ = ENNReal.ofReal C * (ENNReal.ofReal |(LinearMap.det L)⁻¹| *
          ∫⁻ d, ENNReal.ofReal (F d)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hcomp]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hFint.lintegral_lt_top)

/-- `Z^ρ_{w,a} < ∞` for a connected weighted graph and `a ≥ 0`. -/
theorem Z_lt_top {w : V → V → ℝ} (hW : IsWGraph w) (hconn : (supportGraph w).Connected)
    (ρ : V) {a : ℝ} (ha : 0 ≤ a) : Z w ρ a < ⊤ := by
  have := lintegral_exp_mul_density_lt_top hW hconn ρ ha 0
  simpa [Z] using this

/-- `Z^ρ_{w,a} > 0` for a connected weighted graph. -/
theorem Z_pos {w : V → V → ℝ} (hW : IsWGraph w) (hconn : (supportGraph w).Connected)
    (ρ : V) (a : ℝ) : 0 < Z w ρ a := by
  rw [pos_iff_ne_zero]
  intro h
  rw [Z, lintegral_eq_zero_iff (continuous_density hW hconn ρ a).measurable.ennreal_ofReal] at h
  have hae : ∀ᵐ τ ∂(volume : Measure ({i // i ≠ ρ} → ℝ)), False := by
    filter_upwards [h] with τ hτ
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hτ
    exact absurd (density_pos hW hconn ρ a τ) (not_lt.2 hτ)
  rw [MeasureTheory.ae_iff] at hae
  simp only [not_false_eq_true, Set.ofPred_true, Measure.measure_univ_eq_zero] at hae
  exact (NeZero.ne (volume : Measure ({i // i ≠ ρ} → ℝ))) hae

end ArborealDecay.TLaw
