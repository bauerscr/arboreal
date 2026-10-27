module

public import ArborealDecay.Annulus.Moment

/-!
# The separately wired annulus (note `prop:annulus`, supplement `thm:annulus`), from (A), (C)

`annulus_of_inputs`: for every `β ≥ 0` there are `C, κ > 0` such that for all `r ≥ 2`, every
`Λ ⊆ {r ≤ ‖z‖∞ ≤ 2r}` and every nearest-neighbour `w` with `0 ≤ w ≤ β`, the wired graph
`G_r = mapW w (annulusCollapse r Λ)` has `μ_{G_r}(a ↔ b) ≤ C r^{-κ}`.

Route (supplement `thm:annulus`): restrict to the component of the terminals (`rem:conn-hyp`);
identify `a = b` to `ρ`; `τ ≤ E^ρ K` (conductance identity, from (C)); Dirichlet bound
`K ≤ ½ ∑_{u,u'} w_{uu'} U_u U_{u'} (f_u - f_{u'})²` with the Lipschitz cutoff `f`;
`E(U_u U_{u'}) ≤ ½ (E U_u² + E U_{u'}²)`; `E U_u² ≤ (r/8)^{-κ}` (`second_moment_of_inputs`, from
(A)); at most `170 r²` ordered active edges, `w ≤ β`, `(∇f)² ≤ 4/r²`.  Constants:
`κ = 1/(6 C₁ (β+3))`, `C = 340 β 8^κ + 32^κ`.
-/

open Matrix Real MeasureTheory

set_option linter.unusedSectionVars false

@[expose] public section

namespace ArborealDecay.Annulus

open ArborealDecay.TLaw ArborealDecay.Surgery ArborealDecay.Wiring ArborealDecay.CondComb
  ArborealDecay.Lattice

variable {r : ℕ} {Λ : Finset (ℤ × ℤ)}

theorem expect_zero {V : Type*} [Fintype V] [DecidableEq V] (w : V → V → ℝ) (ρ : V) (a : ℝ) :
    expect w ρ a (fun _ => 0) = 0 := by
  simp [expect]

theorem expect_nonneg {V : Type*} [Fintype V] [DecidableEq V] {w : V → V → ℝ} {ρ : V} {a : ℝ}
    (hd : ∀ τ, 0 ≤ density w ρ a τ) {f : ({i // i ≠ ρ} → ℝ) → ℝ} (hf : ∀ τ, 0 ≤ f τ) :
    0 ≤ expect w ρ a f := by
  unfold expect
  exact mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
    (integral_nonneg fun τ => mul_nonneg (hf τ) (hd τ))

/-! ### The field `U` on the wired vertex set -/

/-- The terminal `b` in the component. -/
noncomputable def bW {w : Λ → Λ → ℝ} (hb : (Sum.inl true : Bool ⊕ Λ) ∈ compW r Λ w) :
    compW r Λ w :=
  ⟨Sum.inl true, hb⟩

/-- `U_y = e^{t_y}` on the component, `0` off it. -/
noncomputable def Uhat {w : Λ → Λ → ℝ} {hb : (Sum.inl true : Bool ⊕ Λ) ∈ compW r Λ w}
    (τ : {x : GamV (compW r Λ w) (aW r Λ w) (bW hb) // x ≠ none} → ℝ) (y : Bool ⊕ Λ) : ℝ :=
  if h : y ∈ compW r Λ w then Ufield τ ⟨y, h⟩ else 0

section Field

variable {w : Λ → Λ → ℝ} {hb : (Sum.inl true : Bool ⊕ Λ) ∈ compW r Λ w}

theorem Uhat_nonneg (τ : {x : GamV (compW r Λ w) (aW r Λ w) (bW hb) // x ≠ none} → ℝ)
    (y : Bool ⊕ Λ) : 0 ≤ Uhat τ y := by
  unfold Uhat; split_ifs
  · exact (Ufield_pos τ _).le
  · rfl

theorem Uhat_val (τ : {x : GamV (compW r Λ w) (aW r Λ w) (bW hb) // x ≠ none} → ℝ)
    (x : compW r Λ w) : Uhat τ x.1 = Ufield τ x := by
  simp [Uhat, x.2]

theorem integrable_Uhat_pair (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hconn : (supportGraph (gammaW (resW r Λ w) (aW r Λ w) (bW hb))).Connected)
    (y y' : Bool ⊕ Λ) :
    Integrable (fun τ => (Uhat τ y * Uhat τ y') *
      density (gammaW (resW r Λ w) (aW r Λ w) (bW hb)) none (3 / 2) τ) := by
  have hΓ := isWGraph_gammaW (isWGraph_resW hw hw0) (aW r Λ w) (bW hb)
  by_cases hy : y ∈ compW r Λ w
  · by_cases hy' : y' ∈ compW r Λ w
    · refine (integrable_exp_pair hΓ hconn none (a := 3 / 2) (by norm_num)
        (colAB (aW r Λ w) (bW hb) ⟨y, hy⟩) (colAB (aW r Λ w) (bW hb) ⟨y', hy'⟩)).congr
        (Filter.Eventually.of_forall fun τ => ?_)
      simp only [Uhat, hy, hy', dite_true, Ufield, exp_add]
    · refine (integrable_zero _ _ _).congr (Filter.Eventually.of_forall fun τ => ?_)
      simp [Uhat, hy']
  · refine (integrable_zero _ _ _).congr (Filter.Eventually.of_forall fun τ => ?_)
    simp [Uhat, hy]

/-- **Dirichlet bound** (note `eq:Dirichlet-K`) with the Lipschitz cutoff `f`:
`K ≤ ½ ∑_{u,u' ∈ Λ} w_{uu'} (f_u - f_{u'})² U_u U_{u'}` (`U = 0` off the component). -/
theorem condK_le_cutoff (hr : 0 < r) (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (τ : {x : GamV (compW r Λ w) (aW r Λ w) (bW hb) // x ≠ none} → ℝ) :
    condK (resW r Λ w) (aW r Λ w) (bW hb) τ ≤
      (1 / 2) * ∑ u, ∑ u', w u u' * (lipCutoff r u - lipCutoff r u') ^ 2 *
        (Uhat τ (annulusCollapse r Λ u) * Uhat τ (annulusCollapse r Λ u')) := by
  have hβ' := isWGraph_resW (r := r) hw hw0
  have hc : ∀ i j, 0 ≤ Conductance.rescaled (resW r Λ w) (Uint τ) i j := fun i j => by
    rw [rescaled_Uint]
    exact mul_nonneg (mul_nonneg (hβ'.nonneg i j) (Ufield_pos τ i).le) (Ufield_pos τ j).le
  set f : compW r Λ w → ℝ := fun x => fWire r Λ x.1 with hf
  have hadm : Conductance.Admissible (aW r Λ w) (bW hb) f :=
    ⟨by simp [f, aW, fWire], by simp [f, bW, fWire]⟩
  refine (Conductance.effCond_le_energy hc hadm).trans ?_
  unfold Conductance.energy
  rw [rescaled_Uint]
  set F : Bool ⊕ Λ → Bool ⊕ Λ → ℝ := fun y y' =>
    wiredW r Λ w y y' * (Uhat τ y * Uhat τ y' * (fWire r Λ y - fWire r Λ y') ^ 2) with hF
  have hF0 : ∀ y y', 0 ≤ F y y' := fun y y' =>
    mul_nonneg (mapW_nonneg hw0 _ y y') (mul_nonneg (mul_nonneg (Uhat_nonneg τ y)
      (Uhat_nonneg τ y')) (sq_nonneg _))
  have e1 : ∑ x, ∑ x', resW r Λ w x x' * Ufield τ x * Ufield τ x' * (f x - f x') ^ 2 =
      ∑ x : compW r Λ w, ∑ x' : compW r Λ w, F x.1 x'.1 := by
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
    simp only [hF, Uhat_val, resW, f]; ring
  have e2 : ∑ y, ∑ y', F y y' = ∑ u, ∑ u', w u u' * (lipCutoff r u - lipCutoff r u') ^ 2 *
      (Uhat τ (annulusCollapse r Λ u) * Uhat τ (annulusCollapse r Λ u')) := by
    have := sum_mapW_mul w (annulusCollapse r Λ)
      (fun y y' => Uhat τ y * Uhat τ y' * (fWire r Λ y - fWire r Λ y') ^ 2) (fun y => by simp)
    simp only [hF, wiredW]
    rw [this]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun u' _ => ?_
    rw [fWire_coll hr, fWire_coll hr]; ring
  rw [e1, ← e2]
  exact mul_le_mul_of_nonneg_left (sum_coe_le _ F hF0) (by norm_num)

theorem exp_mul_exp_le (x y : ℝ) :
    exp x * exp y ≤ 1 / 2 * exp (2 * x) + 1 / 2 * exp (2 * y) := by
  rw [show 2 * x = x + x by ring, show 2 * y = y + y by ring, exp_add, exp_add]
  nlinarith [sq_nonneg (exp x - exp y)]

/-- `E(U_u U_{u'}) ≤ ½ (E U_u² + E U_{u'}²) ≤ (r/8)^{-κ}` for band vertices. -/
theorem expect_Uhat_pair_le
    (hA : ∀ (V : Type) [Fintype V] [DecidableEq V] (w : V → V → ℝ) (hW : IsWGraph w),
      (supportGraph w).Connected → ∀ ρ : V,
        Z w ρ (3 / 2) = ENNReal.ofReal (H02.Zforest w hW.symm))
    {β : ℝ} (hβ : 0 ≤ β) (hr : 32 ≤ r) (hw : ∀ i j, w i j = w j i)
    (hw0 : ∀ i j, 0 ≤ w i j) (hnn : ∀ i j, w i j ≠ 0 → IsNN (i : ℤ × ℤ) j)
    (hB : ∀ i j, w i j ≤ β)
    (hconn : (supportGraph (gammaW (resW r Λ w) (aW r Λ w) (bW hb))).Connected)
    (u u' : Λ) (hband : 5 * (r : ℝ) / 4 - 1 ≤ supNorm (u : ℤ × ℤ) ∧
      (supNorm (u : ℤ × ℤ) : ℝ) ≤ 7 * r / 4 + 1)
    (hband' : 5 * (r : ℝ) / 4 - 1 ≤ supNorm (u' : ℤ × ℤ) ∧
      (supNorm (u' : ℤ × ℤ) : ℝ) ≤ 7 * r / 4 + 1) :
    expect (gammaW (resW r Λ w) (aW r Λ w) (bW hb)) none (3 / 2)
      (fun τ => Uhat τ (Sum.inr u) * Uhat τ (Sum.inr u')) ≤ ((r : ℝ) / 8) ^ (-kappaB β) := by
  have hΓ := isWGraph_gammaW (isWGraph_resW (r := r) hw hw0) (aW r Λ w) (bW hb)
  have hd : ∀ τ, 0 ≤ density (gammaW (resW r Λ w) (aW r Λ w) (bW hb)) none (3 / 2) τ :=
    fun τ => (density_pos hΓ hconn none _ τ).le
  have hM : 0 ≤ ((r : ℝ) / 8) ^ (-kappaB β) := by positivity
  by_cases hu : (Sum.inr u : Bool ⊕ Λ) ∈ compW r Λ w
  · by_cases hu' : (Sum.inr u' : Bool ⊕ Λ) ∈ compW r Λ w
    · set p := colAB (aW r Λ w) (bW hb) ⟨Sum.inr u, hu⟩
      set q := colAB (aW r Λ w) (bW hb) ⟨Sum.inr u', hu'⟩
      have i1 := (integrable_exp_single hΓ hconn none (a := 3 / 2) (by norm_num) 2 p).const_mul
        (1 / 2 : ℝ)
      have i2 := (integrable_exp_single hΓ hconn none (a := 3 / 2) (by norm_num) 2 q).const_mul
        (1 / 2 : ℝ)
      have i1' : Integrable (fun τ => (1 / 2 * exp (2 * TLaw.ext none τ p)) *
          density (gammaW (resW r Λ w) (aW r Λ w) (bW hb)) none (3 / 2) τ) :=
        i1.congr (Filter.Eventually.of_forall fun τ => by simp only; ring)
      have i2' : Integrable (fun τ => (1 / 2 * exp (2 * TLaw.ext none τ q)) *
          density (gammaW (resW r Λ w) (aW r Λ w) (bW hb)) none (3 / 2) τ) :=
        i2.congr (Filter.Eventually.of_forall fun τ => by simp only; ring)
      have hmono := expect_mono hd (integrable_Uhat_pair hw hw0 hconn (Sum.inr u) (Sum.inr u'))
        ((i1'.add i2').congr (Filter.Eventually.of_forall fun τ => by
          simp only [Pi.add_apply]; ring))
        (g := fun τ => 1 / 2 * exp (2 * TLaw.ext none τ p) +
          1 / 2 * exp (2 * TLaw.ext none τ q)) (fun τ => by
          simp only [Uhat, hu, hu', dite_true, Ufield]
          exact exp_mul_exp_le _ _)
      refine hmono.trans ?_
      rw [expect_add i1' i2', expect_const_mul, expect_const_mul]
      have m1 := second_moment_of_inputs hA hβ hr hw hw0 hnn hB (bW := bW hb) rfl hconn u hband hu
      have m2 := second_moment_of_inputs hA hβ hr hw hw0 hnn hB (bW := bW hb) rfl hconn u' hband'
        hu'
      linarith
    · have : (fun τ : {x : GamV (compW r Λ w) (aW r Λ w) (bW hb) // x ≠ none} → ℝ =>
          Uhat τ (Sum.inr u) * Uhat τ (Sum.inr u')) = fun _ => 0 := by
        funext τ; simp [Uhat, hu']
      rw [this, expect_zero]; exact hM
  · have : (fun τ : {x : GamV (compW r Λ w) (aW r Λ w) (bW hb) // x ≠ none} → ℝ =>
        Uhat τ (Sum.inr u) * Uhat τ (Sum.inr u')) = fun _ => 0 := by
      funext τ; simp [Uhat, hu]
    rw [this, expect_zero]; exact hM

end Field

theorem surjective_colAB {V : Type*} [Fintype V] [DecidableEq V] (a b : V) :
    Function.Surjective (colAB a b) := by
  intro p
  cases p with
  | none => exact ⟨a, colAB_a⟩
  | some x => exact ⟨x.1, collapse_of_notMem x.2⟩

/-- **The annulus bound for `r ≥ 32`**: `μ_{G_r}(a ↔ b) ≤ 340 β (r/8)^{-κ_β}`, from (A), (C). -/
theorem annulus_main_of_inputs
    (hA : ∀ (V : Type) [Fintype V] [DecidableEq V] (w : V → V → ℝ) (hW : IsWGraph w),
      (supportGraph w).Connected → ∀ ρ : V,
        Z w ρ (3 / 2) = ENNReal.ofReal (H02.Zforest w hW.symm))
    (hC : ∀ (V : Type) [Fintype V] [DecidableEq V] (w : V → V → ℝ) (hW : IsWGraph w),
      (supportGraph w).Connected → ∀ (ρ : V) (i j : {x // x ≠ ρ}),
        expect w ρ (3 / 2) (fun τ => (TLaw.Hmat w ρ (TLaw.ext ρ τ))⁻¹ i j) =
          H02.arborealProb w hW.symm (fun F => F.Reachable i j ∧ ¬ F.Reachable i ρ))
    {β : ℝ} (hβ : 0 ≤ β) (hr : 32 ≤ r) {w : Λ → Λ → ℝ} (hw : ∀ i j, w i j = w j i)
    (hw0 : ∀ i j, 0 ≤ w i j) (hnn : ∀ i j, w i j ≠ 0 → IsNN (i : ℤ × ℤ) j)
    (hB : ∀ i j, w i j ≤ β) :
    H02.arborealProb (wiredW r Λ w) (mapW_symm hw _)
        (fun F => F.Reachable (Sum.inl false) (Sum.inl true)) ≤
      340 * β * ((r : ℝ) / 8) ^ (-kappaB β) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
  set M := ((r : ℝ) / 8) ^ (-kappaB β) with hMdef
  have hM : 0 ≤ M := by positivity
  by_cases hreach : (supportGraph (wiredW r Λ w)).Reachable (Sum.inl false) (Sum.inl true)
  swap
  · rw [tau_eq_zero_of_not_reachable (mapW_symm hw _) (mapW_nonneg hw0 _) hreach]
    positivity
  have hb : (Sum.inl true : Bool ⊕ Λ) ∈ compW r Λ w := mem_compOf.2 hreach
  rw [tau_restrict (mapW_symm hw _) (mapW_nonneg hw0 _) hb]
  have hβ' := isWGraph_resW (r := r) hw hw0
  have hab : aW r Λ w ≠ bW hb := fun h => by
    have := congrArg Subtype.val h
    simp [aW, bW] at this
  have hconnC : (supportGraph (resW r Λ w)).Connected :=
    connected_restrict (mapW_symm hw _) (Sum.inl false)
  have hconnΓ : (supportGraph (gammaW (resW r Λ w) (aW r Λ w) (bW hb))).Connected :=
    connected_mapW hβ'.nonneg (surjective_colAB _ _) hconnC
  have hΓ := isWGraph_gammaW hβ' (aW r Λ w) (bW hb)
  have hd : ∀ τ, 0 ≤ density (gammaW (resW r Λ w) (aW r Λ w) (bW hb)) none (3 / 2) τ :=
    fun τ => (density_pos hΓ hconnΓ none _ τ).le
  have CI := conductance_identity_of_inputs hC hβ' hab hconnΓ
  refine le_trans (le_of_eq rfl) (CI.2.2.trans ?_)
  -- the Dirichlet bound and its expectation
  set c : Λ → Λ → ℝ := fun u u' => w u u' * (lipCutoff r u - lipCutoff r u') ^ 2 with hc
  set P : Λ → Λ → ({x : GamV (compW r Λ w) (aW r Λ w) (bW hb) // x ≠ none} → ℝ) → ℝ :=
    fun u u' τ => Uhat τ (annulusCollapse r Λ u) * Uhat τ (annulusCollapse r Λ u') with hP
  have hPint : ∀ u u', Integrable (fun τ => (c u u' * P u u' τ) *
      density (gammaW (resW r Λ w) (aW r Λ w) (bW hb)) none (3 / 2) τ) := fun u u' =>
    ((integrable_Uhat_pair hw hw0 hconnΓ (annulusCollapse r Λ u)
      (annulusCollapse r Λ u')).const_mul (c u u')).congr
      (Filter.Eventually.of_forall fun τ => by simp only [hP]; ring)
  have hRint : ∀ u, Integrable (fun τ => (∑ u', c u u' * P u u' τ) *
      density (gammaW (resW r Λ w) (aW r Λ w) (bW hb)) none (3 / 2) τ) := fun u =>
    (integrable_finsetSum Finset.univ fun u' _ => hPint u u').congr
      (Filter.Eventually.of_forall fun τ => by simp only [Finset.sum_mul])
  have hSint : Integrable (fun τ => ((1 / 2) * ∑ u, ∑ u', c u u' * P u u' τ) *
      density (gammaW (resW r Λ w) (aW r Λ w) (bW hb)) none (3 / 2) τ) :=
    ((integrable_finsetSum Finset.univ fun u _ => hRint u).const_mul (1 / 2)).congr
      (Filter.Eventually.of_forall fun τ => by
        simp only [mul_assoc, Finset.sum_mul])
  have hKB := expect_mono hd CI.1 hSint (fun τ => by
    have := condK_le_cutoff (hb := hb) (show 0 < r by omega) hw hw0 τ
    simpa only [hc, hP] using this)
  refine hKB.trans ?_
  rw [expect_const_mul, expect_sum _ fun u _ => hRint u]
  simp_rw [expect_sum _ fun u' _ => hPint _ u']
  simp_rw [expect_const_mul]
  -- counting
  have hcount : ∑ u, ∑ u', c u u' *
      expect (gammaW (resW r Λ w) (aW r Λ w) (bW hb)) none (3 / 2) (P u u') ≤ 680 * β * M := by
    rw [← Fintype.sum_prod_type' (f := fun u u' => c u u' *
      expect (gammaW (resW r Λ w) (aW r Λ w) (bW hb)) none (3 / 2) (P u u'))]
    have hsum := sum_le_of_injective (fun q : Λ × Λ => ((q.1 : ℤ × ℤ), (q.2 : ℤ × ℤ)))
      (fun q q' h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)) (gradEdges r)
      (fun q => c q.1 q.2 * expect (gammaW (resW r Λ w) (aW r Λ w) (bW hb)) none (3 / 2)
        (P q.1 q.2)) (fun _ => β * (2 / r) ^ 2 * M) (fun _ _ => by positivity) (fun q hq => by
        have hc0 : c q.1 q.2 ≠ 0 := fun h => hq (by rw [h, zero_mul])
        have hwq : w q.1 q.2 ≠ 0 := fun h => hc0 (by simp only [hc, h, zero_mul])
        have hne : lipCutoff r q.1 ≠ lipCutoff r q.2 := fun h => hc0 (by
          simp only [hc, h, sub_self]; ring)
        have hnnq := hnn q.1 q.2 hwq
        have b1 := band_of_ne (show 0 < r by omega) hnnq hne
        have b2 := band_of_ne (show 0 < r by omega) hnnq.symm (Ne.symm hne)
        refine ⟨mem_gradEdges_of_ne hr0 hnnq hne, ?_⟩
        have hE : expect (gammaW (resW r Λ w) (aW r Λ w) (bW hb)) none (3 / 2) (P q.1 q.2) ≤ M := by
          simp only [hP, coll_of_band (show 8 ≤ r by omega) b1,
            coll_of_band (show 8 ≤ r by omega) b2]
          exact expect_Uhat_pair_le hA hβ hr hw hw0 hnn hB hconnΓ q.1 q.2 b1 b2
        have hE0 : 0 ≤ expect (gammaW (resW r Λ w) (aW r Λ w) (bW hb)) none (3 / 2)
            (P q.1 q.2) :=
          expect_nonneg hd fun τ => mul_nonneg (Uhat_nonneg τ _) (Uhat_nonneg τ _)
        have hgr := abs_lipCutoff_sub_le hr0 hnnq
        have hsq : (lipCutoff r q.1 - lipCutoff r q.2) ^ 2 ≤ (2 / r) ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) hgr 2
        have hcle : c q.1 q.2 ≤ β * (2 / r) ^ 2 := by
          simp only [hc]
          exact mul_le_mul (hB _ _) hsq (sq_nonneg _) hβ
        exact mul_le_mul hcle hE hE0 (by positivity))
    refine hsum.trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard := card_gradEdges_le hr1
    have : ((gradEdges r).card : ℝ) * (β * (2 / r) ^ 2 * M) ≤
        170 * (r : ℝ) ^ 2 * (β * (2 / r) ^ 2 * M) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    refine this.trans (le_of_eq ?_)
    field_simp
    ring
  linarith

/-- **Separately wired annulus** (note `prop:annulus`, supplement `thm:annulus`), from (A), (C):
for every `β ≥ 0` there are `C, κ > 0` with `μ_{G_r}(a ↔ b) ≤ C r^{-κ}` for all `r ≥ 2`, all
`Λ ⊆ {r ≤ ‖z‖∞ ≤ 2r}` and all nearest-neighbour weights `0 ≤ w ≤ β` (uniformly in the deleted
edges and the boundary multiplicities). One may take `κ = 1/(6 C₁ (β+3))`. -/
theorem annulus_of_inputs
    (hA : ∀ (V : Type) [Fintype V] [DecidableEq V] (w : V → V → ℝ) (hW : IsWGraph w),
      (supportGraph w).Connected → ∀ ρ : V,
        Z w ρ (3 / 2) = ENNReal.ofReal (H02.Zforest w hW.symm))
    (hC : ∀ (V : Type) [Fintype V] [DecidableEq V] (w : V → V → ℝ) (hW : IsWGraph w),
      (supportGraph w).Connected → ∀ (ρ : V) (i j : {x // x ≠ ρ}),
        expect w ρ (3 / 2) (fun τ => (TLaw.Hmat w ρ (TLaw.ext ρ τ))⁻¹ i j) =
          H02.arborealProb w hW.symm (fun F => F.Reachable i j ∧ ¬ F.Reachable i ρ))
    (β : ℝ) (hβ : 0 ≤ β) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧
      ∀ (r : ℕ), 2 ≤ r → ∀ (Λ : Finset (ℤ × ℤ)),
        (∀ z ∈ Λ, (r : ℤ) ≤ supNorm z ∧ supNorm z ≤ 2 * (r : ℤ)) →
        ∀ (w : Λ → Λ → ℝ) (hw : ∀ i j, w i j = w j i), (∀ i j, 0 ≤ w i j) →
          (∀ i j, w i j ≠ 0 → IsNN (i : ℤ × ℤ) j) → (∀ i j, w i j ≤ β) →
          H02.arborealProb (mapW w (annulusCollapse r Λ)) (mapW_symm hw _)
            (fun F => F.Reachable (Sum.inl false) (Sum.inl true)) ≤ C * (r : ℝ) ^ (-κ) := by
  set κ := kappaB β with hκdef
  have hκ : 0 < κ := kappaB_pos hβ
  have h8 : (0 : ℝ) < 8 ^ κ := by positivity
  have h32 : (0 : ℝ) < 32 ^ κ := by positivity
  refine ⟨340 * β * 8 ^ κ + 32 ^ κ, κ, by positivity, hκ, ?_⟩
  intro r hr Λ _ w hw hw0 hnn hB
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hrk : 0 ≤ (r : ℝ) ^ (-κ) := by positivity
  by_cases hbig : 32 ≤ r
  · have hmain := annulus_main_of_inputs hA hC hβ hbig hw hw0 hnn hB
    have e : ((r : ℝ) / 8) ^ (-κ) = (r : ℝ) ^ (-κ) * 8 ^ κ := by
      rw [div_rpow hr0.le (by norm_num), rpow_neg (by norm_num : (0 : ℝ) ≤ 8), div_inv_eq_mul]
    rw [← hκdef, e] at hmain
    refine hmain.trans ?_
    nlinarith [mul_nonneg h32.le hrk]
  · have hle1 := H02.arborealProb_le_one (mapW_symm hw (annulusCollapse r Λ))
      (mapW_nonneg hw0 _) (fun F => F.Reachable (Sum.inl false) (Sum.inl true))
    refine hle1.trans ?_
    have hr32 : (r : ℝ) ≤ 32 := by exact_mod_cast (show r ≤ 32 by omega)
    have hpow : (r : ℝ) ^ κ ≤ 32 ^ κ := rpow_le_rpow hr0.le hr32 hκ.le
    have hrκ : 0 < (r : ℝ) ^ κ := by positivity
    have h1 : 1 ≤ 32 ^ κ * (r : ℝ) ^ (-κ) := by
      rw [rpow_neg hr0.le, ← div_eq_mul_inv, le_div_iff₀ hrκ, one_mul]
      exact hpow
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 340) hβ) h8.le) hrk]

end ArborealDecay.Annulus
