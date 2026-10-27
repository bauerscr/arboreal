import Obs2.Est.LinBoundAB
import Obs2.Est.EstLocU

/-!
# The contraction of the linear part for unreduced activities (all four components)

**`Llin2O_U_boundL`**: for `K(X)` with all four components local in `X^□`, `U(1)`-invariant, the
single-source components supported as in `Llin2O_obs_boundL`, and **no `ab` part on small sets**
(`K(X)_{ab} = 0` for `X` small, as below coalescence, `ObsCoalInv`), the observable part of `𝓛(K)`
is contracted in the norm with any weights. Split `‖·‖_w = ‖·‖_{(w_a,w_b,0)} + w_{ab}‖(·)_{ab}‖`
(`oTo_split_ab`): the first part is `Llin2O_obs_boundL`; the `ab` part of `𝓛(K)` is
`∑_{X large}𝔼θ K(X)_{ab}` (`Llin2O_ab_eq`; the `(1-loc^{ab})` term vanishes), contracted by the
large-set regulator (`lin_comp_bound2L` with `H = 0`). No anchoring is needed.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD PolyAux ENNReal

variable {d L N : ℕ} [NeZero L]

open Classical in
/-- **The contraction of the linear part, unreduced activities, output regulator `λA`.** -/
theorem Llin2O_U_boundL (d : ℕ) (hd : 2 ≤ d) : ∃ (C₀ η : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧ 0 < η ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∀ lam : ℝ, 1 ≤ lam → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓC C →
    ∀ (c : Obs.Case) (P : ObsPts d L N) (w : Wt) (K : OAct c d L N),
      (∀ X, IsConn j X → CmpInA (nbhd j X : Set (Lam d L N)) (K X : SA c (Lam d L N))) →
      (∀ X, IsConn j X → IsSymS (K X : SA c (Lam d L N))) →
      (∀ X, IsConn j X → P.a ∉ nbhd j X → (K X : SA c (Lam d L N)).a = 0) →
      (∀ X, IsConn j X → P.b ∉ nbhd j X → (K X : SA c (Lam d L N)).b = 0) →
      (∀ X, IsSmall j X → (K X : SA c (Lam d L N)).ab = 0) →
      ∀ k : ℝ≥0∞, (∀ X, IsConn j X → ENNReal.ofReal (A ^ (nb j X - 2 ^ d)) * oTo w j ℓ (K X) ≤ k) →
      ∀ U : Finset (Lam d L N), IsConn (j + 1) U →
        ENNReal.ofReal ((lam * A) ^ (nb (j + 1) U - 2 ^ d)) * oTo w (j + 1) ℓ' (Llin2O P j C K U) ≤
          ENNReal.ofReal (C₀ * ((L : ℝ)⁻¹ + A ^ (-η))) * k := by
  obtain ⟨C₁, η₁, L₁, hC₁, hη₁, h1⟩ := Llin2O_obs_boundL d hd
  obtain ⟨cn, η₂, L₂, hcn, hη₂, h2⟩ := lin_comp_bound2L d hd
  refine ⟨C₁ + 2, min η₁ η₂, max L₁ (max L₂ 1), by positivity, lt_min hη₁ hη₂, ?_⟩
  intro L _ hL lam hlam
  obtain ⟨A₁, hA₁, h1'⟩ := h1 L (le_trans (le_max_left _ _) hL) lam hlam
  obtain ⟨A₂, hA₂, h2'⟩ := h2 L (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL) lam hlam
  refine ⟨max A₁ A₂, le_trans hA₁ (le_max_left _ _), fun A hA => ?_⟩
  intro N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC c P w K hloc hsym hza hzb hzab k hk U hU
  have hA1 : 1 ≤ A := le_trans hA₁ (le_trans (le_max_left _ _) hA)
  have hL1 : (1 : ℝ) ≤ L := by
    exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
  have e1 := h1' A (le_trans (le_max_left _ _) hA) N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC c P (wOne w)
    rfl K (fun X hX => (hloc X hX).toCmpIn) hsym hza hzb k
    (fun X hX => (mul_le_mul_left' (oTo_one_le w j ℓ (K X)) _).trans (hk X hX)) U hU
  have e2 := h2' A (le_trans (le_max_right _ _) hA) N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC P.a P.b 0
    le_rfl (fun X => (K X : SA c (Lam d L N)).ab) (fun _ => 0) w.ab k
    (fun X _ => by rw [Step.Tj_zero]; exact zero_le) (fun _ _ _ _ => rfl)
    (fun X hX _ => (hloc X hX).ab)
    (fun X hX => (mul_le_mul_left' (ab_le_oTo w j ℓ (K X)) _).trans (hk X hX))
    U hU
  have eab : (Llin2O P j C K U : SA c (Lam d L N)).ab =
      (∑ X ∈ (Pj j univ).filter (fun X => IsSmall j X ∧ clo j X = U), ECC C (theta (0 : Alg d L N))) +
      ∑ X ∈ (Pj j univ).filter (fun X => IsConn j X ∧ ¬ IsSmall j X ∧ clo j X = U),
        ECC C (theta (K X : SA c (Lam d L N)).ab) := by
    rw [Llin2O_ab_eq P hjN C K U]
    congr 1
    refine sum_congr rfl fun X hX => ?_
    rw [hzab X (mem_filter.1 hX).2.1, locABtXY_zero, sub_zero]
  rw [← eab] at e2
  rw [oTo_split_ab w (j + 1) ℓ' (Llin2O P j C K U), mul_add]
  refine (add_le_add e1 e2).trans ?_
  rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine mul_le_mul_right' (ENNReal.ofReal_le_ofReal ?_) _
  have hb1 : A ^ (-η₁) ≤ A ^ (-min η₁ η₂) :=
    Real.rpow_le_rpow_of_exponent_le hA1 (neg_le_neg (min_le_left _ _))
  have hb2 : A ^ (-η₂) ≤ A ^ (-min η₁ η₂) :=
    Real.rpow_le_rpow_of_exponent_le hA1 (neg_le_neg (min_le_right _ _))
  have hLi : 0 ≤ (L : ℝ)⁻¹ := by positivity
  have hAp : 0 ≤ A ^ (-η₂) := Real.rpow_nonneg (by linarith) _
  have e0 : cn * 0 / (L : ℝ) = 0 := by simp
  rw [e0, zero_add]
  nlinarith
