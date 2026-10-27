module

public import ArborealDecay.Annulus.Bridge

/-!
# The effective-conductance identity (note `prop:conductance-identity`), from (C)

For `G = (V, β)` with terminals `a ≠ b` and `Γ = G/(a=b)` connected:
`E^ρ_Γ K = τ_G(a,b) / (1 - τ_G(a,b))` and `τ_G(a,b) ≤ E^ρ_Γ K` (`eq:conductance-odds`,
`eq:tau-le-EK`), where `K = condK β a b` is the effective conductance of the split network
with conductances `β_{ij} U_i U_j`, `U = e^t`, `U_a = U_b = 1`.

Only identity (C) (the pinned Green-function event, supplement `thm:pinned-green`) is assumed.
Integrability of `K` is proved: `0 ≤ K ≤ ∑_v β_av U_v`, and each term `β_ai X_ij β_jb` of the
Schur formula lies in `[0, K]` because `X = (H^ρ_Γ)⁻¹ ≥ 0` entrywise (`MMatrix`).
-/

open Matrix Real MeasureTheory

set_option linter.unusedSectionVars false

@[expose] public section

namespace ArborealDecay.Annulus

open ArborealDecay.TLaw ArborealDecay.Surgery ArborealDecay.Wiring ArborealDecay.CondComb

universe u

variable {V : Type u} [Fintype V] [DecidableEq V] {a b : V}

/-- `V ∖ {a,b}` as `Interior a b` and as the `Finset` complement. -/
def eIS (a b : V) : Conductance.Interior a b ≃ {v : V // v ∉ ({a, b} : Finset V)} :=
  Equiv.subtypeEquivRight fun v => by simp

theorem integrable_condK_bound {β : V → V → ℝ} (hβ : IsWGraph β)
    (hconn : (supportGraph (gammaW β a b)).Connected) :
    Integrable (fun τ => (∑ v, β a v * Ufield τ v) * density (gammaW β a b) none (3 / 2) τ) := by
  have h := integrable_finsetSum (Finset.univ : Finset V) fun v _ =>
    (integrable_exp_single (isWGraph_gammaW hβ a b) hconn none (a := 3 / 2) (by norm_num) 1
      (colAB a b v)).const_mul (β a v)
  refine h.congr (Filter.Eventually.of_forall fun τ => ?_)
  simp only [Finset.sum_mul, Ufield, one_mul]
  refine Finset.sum_congr rfl fun v _ => by ring

theorem measurable_condK {β : V → V → ℝ} (hβ : IsWGraph β) (hab : a ≠ b)
    (hconn : (supportGraph (gammaW β a b)).Connected) : Measurable (condK β a b) := by
  have e : condK β a b = fun τ => β a b + ∑ i : Conductance.Interior a b,
      ∑ j : Conductance.Interior a b,
        β a i.1 * greenX (gammaW β a b) τ (eI a b i) (eI a b j) * β j.1 b := by
    funext τ; exact condK_eq hβ hab hconn τ
  rw [e]
  refine measurable_const.add (Finset.measurable_sum _ fun i _ =>
    Finset.measurable_sum _ fun j _ => ?_)
  exact (measurable_const.mul (measurable_greenX _ _ _)).mul measurable_const

/-- **Effective-conductance identity** (note `prop:conductance-identity`), from (C):
`K` is integrable, `E^ρ_Γ K = τ_G(a,b)/(1 - τ_G(a,b))`, and `τ_G(a,b) ≤ E^ρ_Γ K`. -/
theorem conductance_identity_of_inputs
    (hC : ∀ (V : Type u) [Fintype V] [DecidableEq V] (w : V → V → ℝ) (hW : IsWGraph w),
      (supportGraph w).Connected → ∀ (ρ : V) (i j : {x // x ≠ ρ}),
        expect w ρ (3 / 2) (fun τ => (TLaw.Hmat w ρ (TLaw.ext ρ τ))⁻¹ i j) =
          H02.arborealProb w hW.symm (fun F => F.Reachable i j ∧ ¬ F.Reachable i ρ))
    {β : V → V → ℝ} (hβ : IsWGraph β) (hab : a ≠ b)
    (hconn : (supportGraph (gammaW β a b)).Connected) :
    Integrable (fun τ => condK β a b τ * density (gammaW β a b) none (3 / 2) τ) ∧
      expect (gammaW β a b) none (3 / 2) (condK β a b) =
        H02.arborealProb β hβ.symm (fun F => F.Reachable a b) /
          (1 - H02.arborealProb β hβ.symm (fun F => F.Reachable a b)) ∧
      H02.arborealProb β hβ.symm (fun F => F.Reachable a b) ≤
        expect (gammaW β a b) none (3 / 2) (condK β a b) := by
  set Γ := gammaW β a b with hΓdef
  have hΓ : IsWGraph Γ := isWGraph_gammaW hβ a b
  have hd : ∀ τ, 0 ≤ density Γ none (3 / 2) τ := fun τ => (density_pos hΓ hconn none _ τ).le
  set T : Conductance.Interior a b → Conductance.Interior a b →
      ({x : GamV V a b // x ≠ none} → ℝ) → ℝ :=
    fun i j τ => β a i.1 * greenX Γ τ (eI a b i) (eI a b j) * β j.1 b with hT
  have hT0 : ∀ i j τ, 0 ≤ T i j τ := fun i j τ =>
    mul_nonneg (mul_nonneg (hβ.nonneg _ _) (greenX_nonneg hΓ hconn τ _ _)) (hβ.nonneg _ _)
  have hK : ∀ τ, condK β a b τ = β a b + ∑ i, ∑ j, T i j τ := fun τ => condK_eq hβ hab hconn τ
  have hKint : Integrable (fun τ => condK β a b τ * density Γ none (3 / 2) τ) :=
    integrable_of_le hd (measurable_condK hβ hab hconn) (integrable_condK_bound hβ hconn)
      (fun τ => (condK_le hβ hab τ).1) (fun τ => (condK_le hβ hab τ).2)
  have hTm : ∀ i j, Measurable (T i j) := fun i j =>
    (measurable_const.mul (measurable_greenX _ _ _)).mul measurable_const
  have hrow_le : ∀ i τ, ∑ j, T i j τ ≤ condK β a b τ := fun i τ => by
    rw [hK]
    have h1 : ∑ j, T i j τ ≤ ∑ i, ∑ j, T i j τ :=
      Finset.single_le_sum (f := fun i => ∑ j, T i j τ)
        (fun i _ => Finset.sum_nonneg fun j _ => hT0 i j τ) (Finset.mem_univ i)
    linarith [hβ.nonneg a b]
  have hTint : ∀ i j, Integrable (fun τ => T i j τ * density Γ none (3 / 2) τ) := fun i j =>
    integrable_of_le hd (hTm i j) hKint (hT0 i j) fun τ =>
      (Finset.single_le_sum (f := fun j => T i j τ) (fun j _ => hT0 i j τ)
        (Finset.mem_univ j)).trans (hrow_le i τ)
  have hRint : ∀ i, Integrable (fun τ => (∑ j, T i j τ) * density Γ none (3 / 2) τ) := fun i =>
    integrable_of_le hd (Finset.measurable_sum _ fun j _ => hTm i j) hKint
      (fun τ => Finset.sum_nonneg fun j _ => hT0 i j τ) (hrow_le i)
  have hEK : expect Γ none (3 / 2) (condK β a b) = β a b + ∑ i, ∑ j,
      β a i.1 * β j.1 b * expect Γ none (3 / 2) (fun τ => greenX Γ τ (eI a b i) (eI a b j)) := by
    have e : condK β a b = fun τ => β a b + ∑ i, ∑ j, T i j τ := funext hK
    have hSint : Integrable (fun τ => (∑ i, ∑ j, T i j τ) * density Γ none (3 / 2) τ) :=
      integrable_of_le hd (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
        hTm i j) hKint (fun τ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
          hT0 i j τ) (fun τ => by rw [hK]; linarith [hβ.nonneg a b])
    rw [e, expect_add ((integrable_density hΓ hconn none (by norm_num)).const_mul (β a b)) hSint,
      expect_const hΓ hconn none (by norm_num), expect_sum _ fun i _ => hRint i]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [expect_sum _ fun j _ => hTint i j]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : T i j = fun τ => (β a i.1 * β j.1 b) * greenX Γ τ (eI a b i) (eI a b j) := by
      funext τ; simp only [hT]; ring
    rw [this, expect_const_mul]
  have hCij : ∀ i j, expect Γ none (3 / 2) (fun τ => greenX Γ τ (eI a b i) (eI a b j)) =
      H02.arborealProb Γ (gammaW_symm hβ.symm a b) (EvIJ a b (eIS a b i) (eIS a b j)) := by
    intro i j
    exact hC (GamV V a b) Γ hΓ hconn none (eI a b i) (eI a b j)
  have hsum : ∑ i : Conductance.Interior a b, ∑ j : Conductance.Interior a b,
      β a i.1 * β j.1 b * H02.arborealProb Γ (gammaW_symm hβ.symm a b)
        (EvIJ a b (eIS a b i) (eIS a b j)) =
      ∑ i : {v : V // v ∉ ({a, b} : Finset V)}, ∑ j : {v : V // v ∉ ({a, b} : Finset V)},
        β a i.1 * β j.1 b * H02.arborealProb Γ (gammaW_symm hβ.symm a b) (EvIJ a b i j) := by
    rw [← (eIS a b).sum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← (eIS a b).sum_comp]
    rfl
  have hval : expect Γ none (3 / 2) (condK β a b) =
      Zc β hβ.symm a b / Zd β hβ.symm a b := by
    rw [hEK]
    simp only [hCij]
    rw [hsum, Zd_eq_ZGamma hβ.symm hab, Zc_div_ZGamma hβ.symm hβ.nonneg hab]
  refine ⟨hKint, ?_, ?_⟩
  · rw [hval, Zc_div_Zd hβ.symm hβ.nonneg hab]
  · rw [hval]; exact tau_le_Zc_div_Zd hβ.symm hβ.nonneg hab

end ArborealDecay.Annulus
