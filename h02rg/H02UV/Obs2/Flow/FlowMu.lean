import Obs2.Pair.CoalHist
import Obs2.Map.Second
import Obs.LocObsEst

/-!
# The flow of the single-point couplings `μ^{(1)}, μ^{(2)}`: exact recursion and the `K` error

At the block `B ∋ a`, the `σ_a` component of `V_j(B)` is localised:
`V_j(B)_a = -μ^{(1)}_a ψ̄_a` (Case (1)) resp. `α + β ψ̄_aψ_a`, `β = -μ^{(2)}_a` (Case (2)). One step of
the map with sources (`Obs2.Map.Map`) gives **exactly** (`mass1_VpO_a`, `mass2_VpO_a`)

`β_{j+1}(B) = β_j - ∑_{X ∈ 𝒮_j, X ⊇ B} m(K_j(X)_a) - m(S(B_+)_a)`,

where `m = mass1(-1)` (Case (1), the coefficient sum `∑_x F_{x̄}`) resp. `m = mass2` (Case (2),
`∑_{x,y} F_{x̄y}`), and `S(B_+) = ∑_{B' ⊆ B_+} (½ F_C(V'_{B'}, V'(Λ)) + 𝔼_Cθ 𝒲(B'))` is the
second-order term (it contains the one-loop corrections `−𝔫_j`, `g^♭𝔩_j` of the flow equations and
the `𝒲^{obs}` remainder). The `σ_a` component keeps its localised form (`VpO_a_form_one/two`).

The error from the activity is bounded by the norm of `K^{obs}` (`K_term_bound_one/two`):
`|∑_{X ⊇ B} m(K(X)_a)| ≤ c C ℓ^{-p} sup_X ‖K(X)_a‖_{T_j(ℓ)}` (`p = 1, 2`), with `c` the number of
small sets containing a block (independent of `L`).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 LocObs FRD

variable {d L N : ℕ} [NeZero L]

/-! ### Linear coefficient functionals -/

/-- `mass2` as a linear map. -/
def mass2L : Alg d L N →ₗ[ℂ] ℂ where
  toFun := mass2
  map_add' := mass2_add
  map_smul' r F := mass2_smul r F

theorem mass2_sub (F G : Alg d L N) : mass2 (F - G) = mass2 F - mass2 G :=
  map_sub (mass2L (d := d) (L := L) (N := N)) F G

theorem mass2_sum {ι : Type*} (s : Finset ι) (F : ι → Alg d L N) :
    mass2 (∑ i ∈ s, F i) = ∑ i ∈ s, mass2 (F i) :=
  map_sum (mass2L (d := d) (L := L) (N := N)) F s

theorem mass2_algebraMap (r : ℂ) : mass2 (algebraMap ℂ (Alg d L N) r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, mass2_smul, mass2_one, mul_zero]

theorem mass1_sum (s : ℤˣ) {ι : Type*} (t : Finset ι) (F : ι → Alg d L N) :
    mass1 s (∑ i ∈ t, F i) = ∑ i ∈ t, mass1 s (F i) :=
  map_sum (mass1L (d := d) (L := L) (N := N) s) F t

theorem mass1_algebraMap (s : ℤˣ) (r : ℂ) : mass1 s (algebraMap ℂ (Alg d L N) r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, mass1_smul, mass1_one, mul_zero]

/-! ### `e^{ℒ_C}` on the localised monomials -/

theorem expLC_one' (C : Matrix (Lam d L N) (Lam d L N) ℂ) : expLC C (1 : Alg d L N) = 1 := by
  rw [expLC_of_cube C (by rw [LopC_one, map_zero, map_zero]), LopC_one, map_zero, smul_zero,
    add_zero, add_zero]

theorem expLC_pbp (C : Matrix (Lam d L N) (Lam d L N) ℂ) (a : Lam d L N) :
    ∃ r : ℂ, expLC C (pbp a) = pbp a + r • (1 : Alg d L N) := by
  have h : PM (ev ((a, 1) : Sf (Lam d L N))) (ev (a, -1)) :=
    ⟨fun y => by simp [ev, Prod.ext_iff], fun y => by simp [ev, Prod.ext_iff]⟩
  have e : pbp a = -(ψ (a, 1) * ψ (a, -1) : Alg d L N) := by
    unfold pbp psibar psi; exact ψ_anticomm _ _
  refine ⟨pairC C (ev (a, 1)) (ev (a, -1)), ?_⟩
  rw [e, map_neg]
  have := expLC_two C h
  simp only [ψ] at this ⊢
  rw [this, neg_add, neg_smul, neg_neg]

theorem expLC_psibar (C : Matrix (Lam d L N) (Lam d L N) ℂ) (a : Lam d L N) :
    expLC C (psibar a) = psibar a :=
  expLC_lin C (ev (a, -1))

/-- `m(e^{ℒ_C}(α + β ψ̄_aψ_a)) = β`. -/
theorem mass2_expLC_loc (C : Matrix (Lam d L N) (Lam d L N) ℂ) (α β : ℂ) (a : Lam d L N) :
    mass2 (expLC C (α • (1 : Alg d L N) + β • pbp a)) = β := by
  obtain ⟨r, hr⟩ := expLC_pbp C a
  rw [map_add, map_smul, map_smul, expLC_one', hr, mass2_add, mass2_smul, mass2_smul, mass2_add,
    mass2_smul, mass2_one, mass2_pbp]
  ring

theorem mass2_loc (α β : ℂ) (a : Lam d L N) : mass2 (α • (1 : Alg d L N) + β • pbp a) = β := by
  rw [mass2_add, mass2_smul, mass2_smul, mass2_one, mass2_pbp]; ring

/-- The single-point localisations for `a ∈ Y ⊆ X`. -/
theorem locEven_single_eq' {a : Lam d L N} {X Y : Finset (Lam d L N)} (haY : a ∈ Y)
    (hYX : Y ⊆ X) (F : Alg d L N) :
    locEven {a} X Y F = ε F • (1 : Alg d L N) + mass2 F • pbp a := by
  have h1 : X ∩ {a} = {a} := by
    ext x; simp only [mem_inter, mem_singleton]
    exact ⟨fun h => h.2, by rintro rfl; exact ⟨hYX haY, rfl⟩⟩
  have h2 : Y ∩ {a} = {a} := by
    ext x; simp only [mem_inter, mem_singleton]
    exact ⟨fun h => h.2, by rintro rfl; exact ⟨haY, rfl⟩⟩
  simp only [locEven, locGen, h1, h2, card_singleton, Nat.cast_one, div_one, sum_singleton]

theorem locOdd_single_eq' {a : Lam d L N} {X Y : Finset (Lam d L N)} (haY : a ∈ Y)
    (hYX : Y ⊆ X) (F : Alg d L N) :
    locOdd (-1) {a} X Y F = mass1 (-1) F • psibar a := by
  have h1 : X ∩ {a} = {a} := by
    ext x; simp only [mem_inter, mem_singleton]
    exact ⟨fun h => h.2, by rintro rfl; exact ⟨hYX haY, rfl⟩⟩
  have h2 : Y ∩ {a} = {a} := by
    ext x; simp only [mem_inter, mem_singleton]
    exact ⟨fun h => h.2, by rintro rfl; exact ⟨haY, rfl⟩⟩
  simp only [locOdd, locGen, h1, h2, card_singleton, Nat.cast_one, div_one, sum_singleton]
  rfl

/-! ### Case (2): `μ^{(2)}` -/

section Two

variable (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
  (V W : OFam .two d L N) (K : OAct .two d L N)

/-- The `σ_a` part of `Q(B)` for `a ∈ B`: `∑_{X ⊇ B} (ε(K(X)_a) + m(K(X)_a) ψ̄_aψ_a)`. -/
theorem Q2O_a_two (hjN : j + 1 < N) {b : Fin d → ℕ}
    (ha : P.a ∈ blockSet (L := L) (N := N) j b) :
    (Q2O P j K b : SA .two (Lam d L N)).a =
      (∑ X ∈ (smallSets (L := L) (N := N) j).filter (fun X => blockSet j b ⊆ X),
        ε (K X : SA .two (Lam d L N)).a) • (1 : Alg d L N) +
      (∑ X ∈ (smallSets (L := L) (N := N) j).filter (fun X => blockSet j b ⊆ X),
        mass2 (K X : SA .two (Lam d L N)).a) • pbp P.a := by
  classical
  unfold Q2O
  rw [if_pos hjN, AddSubmonoidClass.coe_finset_sum, sum_a, sum_smul, sum_smul,
    ← sum_add_distrib]
  refine sum_congr (by congr) fun X hX => ?_
  exact (locAp_two_of_mem _ ((mem_filter.1 hX).2 ha) _).trans
    (locEven_single_eq' ha (mem_filter.1 hX).2 _)

/-- **The exact recursion of `μ^{(2)}`** at the block `B ∋ a`: if `V_j(B)_a = α + β ψ̄_aψ_a`, then
`m(V_{j+1}(B)_a) = β - ∑_{X ⊇ B} m(K(X)_a) - m(S(B_+)_a)`. -/
theorem mass2_VpO_a (hjN : j + 1 < N) {b : Fin d → ℕ}
    (ha : P.a ∈ blockSet (L := L) (N := N) j b) {α β : ℂ}
    (hV : (V b : SA .two (Lam d L N)).a = α • (1 : Alg d L N) + β • pbp P.a) :
    mass2 (VpO P j C V W K b : SA .two (Lam d L N)).a =
      β - (∑ X ∈ (smallSets (L := L) (N := N) j).filter (fun X => blockSet j b ⊆ X),
        mass2 (K X : SA .two (Lam d L N)).a) -
        mass2 (SXO j C V W (Step2.Bp (L := L) (N := N) j b) : SA .two (Lam d L N)).a := by
  have hB : blockSet (L := L) (N := N) j b ⊆ Step2.Bp (L := L) (N := N) j b := subset_clo j _
  have e : (VpO P j C V W K b : SA .two (Lam d L N)).a =
      expLC C (V b : SA .two (Lam d L N)).a -
        expLC C (Q2O P j K b : SA .two (Lam d L N)).a -
        locAp Obs.Case.two P.a (Step2.Bp (L := L) (N := N) j b) (blockSet (L := L) (N := N) j b)
          (SXO j C V W (Step2.Bp (L := L) (N := N) j b) : SA .two (Lam d L N)).a -
        0 - algebraMap ℂ (Alg d L N)
          (ε (uVpO P j C V W K b : SA .two (Lam d L N)).a) := by
    have hup : (upO P j C V W K b : SA .two (Lam d L N)).a =
        algebraMap ℂ (Alg d L N) (ε (uVpO P j C V W K b : SA .two (Lam d L N)).a) := by
      show cmp true (πobs (epsO (uVpO P j C V W K b)) : SA .two (Lam d L N)) = _
      rw [cmp_πobs]; rfl
    have halg : ((algebraMap ℂ (OE .two (Lam d L N)) (upB P j C V W K b) : OE .two (Lam d L N)) :
        SA .two (Lam d L N)).a = 0 := by
      rw [Subalgebra.coe_algebraMap]; exact algebraMap_a _
    have h1 : (VpO P j C V W K b : SA .two (Lam d L N)).a =
        (uVpO P j C V W K b : SA .two (Lam d L N)).a -
          ((algebraMap ℂ (OE .two (Lam d L N)) (upB P j C V W K b) : OE .two (Lam d L N)) :
            SA .two (Lam d L N)).a - (upO P j C V W K b : SA .two (Lam d L N)).a := rfl
    have h2 : (uVpO P j C V W K b : SA .two (Lam d L N)).a =
        (VprO C V b : SA .two (Lam d L N)).a - (EthO C (Q2O P j K b) : SA .two (Lam d L N)).a -
          (LSO P j C V W b : SA .two (Lam d L N)).a := rfl
    rw [h1, halg, hup, h2, VprO, EthO_eq_expO, EthO_eq_expO]; rfl
  rw [e, mass2_sub, mass2_sub, mass2_sub, mass2_sub, mass2_algebraMap, sub_zero, hV,
    mass2_expLC_loc, Q2O_a_two P j K hjN ha, mass2_expLC_loc, locAp_two_of_mem _ (hB ha),
    locEven_single_eq' ha hB,
    mass2_loc, show mass2 (0 : Alg d L N) = 0 by simp [mass2], sub_zero]

/-- The `σ_a` component of `V_{j+1}(B)` stays localised. -/
theorem VpO_a_form_two (hjN : j + 1 < N) {b : Fin d → ℕ}
    (ha : P.a ∈ blockSet (L := L) (N := N) j b) {α β : ℂ}
    (hV : (V b : SA .two (Lam d L N)).a = α • (1 : Alg d L N) + β • pbp P.a) :
    ∃ α' : ℂ, (VpO P j C V W K b : SA .two (Lam d L N)).a =
      α' • (1 : Alg d L N) + mass2 (VpO P j C V W K b : SA .two (Lam d L N)).a • pbp P.a := by
  have hB : blockSet (L := L) (N := N) j b ⊆ Step2.Bp (L := L) (N := N) j b := subset_clo j _
  obtain ⟨r, hr⟩ := expLC_pbp C P.a
  have e : (VpO P j C V W K b : SA .two (Lam d L N)).a =
      expLC C (V b : SA .two (Lam d L N)).a -
        expLC C (Q2O P j K b : SA .two (Lam d L N)).a -
        locAp Obs.Case.two P.a (Step2.Bp (L := L) (N := N) j b) (blockSet (L := L) (N := N) j b)
          (SXO j C V W (Step2.Bp (L := L) (N := N) j b) : SA .two (Lam d L N)).a -
        0 - algebraMap ℂ (Alg d L N)
          (ε (uVpO P j C V W K b : SA .two (Lam d L N)).a) := by
    have hup : (upO P j C V W K b : SA .two (Lam d L N)).a =
        algebraMap ℂ (Alg d L N) (ε (uVpO P j C V W K b : SA .two (Lam d L N)).a) := by
      show cmp true (πobs (epsO (uVpO P j C V W K b)) : SA .two (Lam d L N)) = _
      rw [cmp_πobs]; rfl
    have halg : ((algebraMap ℂ (OE .two (Lam d L N)) (upB P j C V W K b) : OE .two (Lam d L N)) :
        SA .two (Lam d L N)).a = 0 := by
      rw [Subalgebra.coe_algebraMap]; exact algebraMap_a _
    have h1 : (VpO P j C V W K b : SA .two (Lam d L N)).a =
        (uVpO P j C V W K b : SA .two (Lam d L N)).a -
          ((algebraMap ℂ (OE .two (Lam d L N)) (upB P j C V W K b) : OE .two (Lam d L N)) :
            SA .two (Lam d L N)).a - (upO P j C V W K b : SA .two (Lam d L N)).a := rfl
    have h2 : (uVpO P j C V W K b : SA .two (Lam d L N)).a =
        (VprO C V b : SA .two (Lam d L N)).a - (EthO C (Q2O P j K b) : SA .two (Lam d L N)).a -
          (LSO P j C V W b : SA .two (Lam d L N)).a := rfl
    rw [h1, halg, hup, h2, VprO, EthO_eq_expO, EthO_eq_expO]; rfl
  rw [Q2O_a_two P j K hjN ha, locAp_two_of_mem _ (hB ha), locEven_single_eq' ha hB, hV] at e
  rw [map_add, map_smul, map_smul, expLC_one', hr, map_add, map_smul, map_smul, expLC_one',
    hr] at e
  set q1 := ∑ X ∈ (smallSets (L := L) (N := N) j).filter (fun X => blockSet j b ⊆ X),
    ε (K X : SA .two (Lam d L N)).a
  set q2 := ∑ X ∈ (smallSets (L := L) (N := N) j).filter (fun X => blockSet j b ⊆ X),
    mass2 (K X : SA .two (Lam d L N)).a
  set s := SXO j C V W (Step2.Bp (L := L) (N := N) j b)
  set u := ε (uVpO P j C V W K b : SA .two (Lam d L N)).a
  refine ⟨α + β * r - (q1 + q2 * r) - ε (s : SA .two (Lam d L N)).a - u, ?_⟩
  have hm : mass2 (VpO P j C V W K b : SA .two (Lam d L N)).a =
      β - q2 - mass2 (s : SA .two (Lam d L N)).a := by
    rw [e]
    simp only [mass2_sub, mass2_add, mass2_smul, mass2_one, mass2_pbp, mass2_algebraMap,
      show mass2 (0 : Alg d L N) = 0 by simp [mass2]]
    ring
  rw [hm, e, Algebra.algebraMap_eq_smul_one]
  module

end Two

/-! ### Case (1): `μ^{(1)}` -/

section One

variable (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
  (V W : OFam .one d L N) (K : OAct .one d L N)

theorem Q2O_a_one (hjN : j + 1 < N) {b : Fin d → ℕ}
    (ha : P.a ∈ blockSet (L := L) (N := N) j b) :
    (Q2O P j K b : SA .one (Lam d L N)).a =
      (∑ X ∈ (smallSets (L := L) (N := N) j).filter (fun X => blockSet j b ⊆ X),
        mass1 (-1) (K X : SA .one (Lam d L N)).a) • psibar P.a := by
  classical
  unfold Q2O
  rw [if_pos hjN, AddSubmonoidClass.coe_finset_sum, sum_a, sum_smul]
  refine sum_congr (by congr) fun X hX => ?_
  exact (locAp_one_of_mem _ ((mem_filter.1 hX).2 ha) _).trans
    (locOdd_single_eq' ha (mem_filter.1 hX).2 _)

/-- **The exact recursion of `μ^{(1)}`** at the block `B ∋ a`: if `V_j(B)_a = β ψ̄_a`, then
`V_{j+1}(B)_a = β' ψ̄_a` with `β' = β - ∑_{X ⊇ B} m(K(X)_a) - m(S(B_+)_a)`, `m = mass1(-1)`.
There is no `e^{ℒ_C}` correction (a single field). -/
theorem VpO_a_one (hjN : j + 1 < N) {b : Fin d → ℕ}
    (ha : P.a ∈ blockSet (L := L) (N := N) j b) {β : ℂ}
    (hV : (V b : SA .one (Lam d L N)).a = β • psibar P.a) :
    (VpO P j C V W K b : SA .one (Lam d L N)).a =
      (β - (∑ X ∈ (smallSets (L := L) (N := N) j).filter (fun X => blockSet j b ⊆ X),
        mass1 (-1) (K X : SA .one (Lam d L N)).a) -
        mass1 (-1) (SXO j C V W (Step2.Bp (L := L) (N := N) j b) : SA .one (Lam d L N)).a) •
          psibar P.a := by
  have hB : blockSet (L := L) (N := N) j b ⊆ Step2.Bp (L := L) (N := N) j b := subset_clo j _
  have hu : ε (uVpO P j C V W K b : SA .one (Lam d L N)).a = 0 := ε_a_one _
  have e : (VpO P j C V W K b : SA .one (Lam d L N)).a =
      expLC C (V b : SA .one (Lam d L N)).a -
        expLC C (Q2O P j K b : SA .one (Lam d L N)).a -
        locAp Obs.Case.one P.a (Step2.Bp (L := L) (N := N) j b) (blockSet (L := L) (N := N) j b)
          (SXO j C V W (Step2.Bp (L := L) (N := N) j b) : SA .one (Lam d L N)).a -
        0 - algebraMap ℂ (Alg d L N)
          (ε (uVpO P j C V W K b : SA .one (Lam d L N)).a) := by
    have hup : (upO P j C V W K b : SA .one (Lam d L N)).a =
        algebraMap ℂ (Alg d L N) (ε (uVpO P j C V W K b : SA .one (Lam d L N)).a) := by
      show cmp true (πobs (epsO (uVpO P j C V W K b)) : SA .one (Lam d L N)) = _
      rw [cmp_πobs]; rfl
    have halg : ((algebraMap ℂ (OE .one (Lam d L N)) (upB P j C V W K b) : OE .one (Lam d L N)) :
        SA .one (Lam d L N)).a = 0 := by
      rw [Subalgebra.coe_algebraMap]; exact algebraMap_a _
    have h1 : (VpO P j C V W K b : SA .one (Lam d L N)).a =
        (uVpO P j C V W K b : SA .one (Lam d L N)).a -
          ((algebraMap ℂ (OE .one (Lam d L N)) (upB P j C V W K b) : OE .one (Lam d L N)) :
            SA .one (Lam d L N)).a - (upO P j C V W K b : SA .one (Lam d L N)).a := rfl
    have h2 : (uVpO P j C V W K b : SA .one (Lam d L N)).a =
        (VprO C V b : SA .one (Lam d L N)).a - (EthO C (Q2O P j K b) : SA .one (Lam d L N)).a -
          (LSO P j C V W b : SA .one (Lam d L N)).a := rfl
    rw [h1, halg, hup, h2, VprO, EthO_eq_expO, EthO_eq_expO]; rfl
  rw [e, hu, map_zero, sub_zero, sub_zero, hV, map_smul, expLC_psibar, Q2O_a_one P j K hjN ha,
    map_smul, expLC_psibar, locAp_one_of_mem _ (hB ha), locOdd_single_eq' ha hB, sub_smul,
    sub_smul]

end One

/-! ### The error from `K^{obs}` -/

/-- **The activity error** in the `μ` recursions:
`|∑_{X ∈ 𝒮_j, X ⊇ B} m_p(K(X)_a)| ≤ c · p! C^p ℓ^{-p} κ` if `‖K(X)_a‖_{T_j(ℓ)} ≤ κ` and
`K(X)_a ∈ 𝒩(X^□)` for these `X` (`m_1 = mass1(-1)`, `m_2 = mass2`). -/
theorem K_term_bound (d : ℕ) : ∃ (c : ℕ) (C₀ : ℝ), 0 ≤ C₀ ∧ ∀ (L : ℕ) [NeZero L],
    2 ^ (d + 3) + 8 * d < L → ∀ N j : ℕ, j < N → ∀ b : Fin d → ℕ,
    b ∈ blockIdx (L := L) (N := N) j → ∀ (F : Finset (Lam d L N) → Alg d L N) (ℓ κ : ℝ),
    0 < ℓ → 0 ≤ κ →
    (∀ X ∈ (smallSets (L := L) (N := N) j).filter (fun X => blockSet j b ⊆ X),
      F X ∈ NX (nbhd j X : Set (Lam d L N)) ∧ Tj d (L : ℝ) j ℓ (F X) ≤ ENNReal.ofReal κ) →
    ‖∑ X ∈ (smallSets (L := L) (N := N) j).filter (fun X => blockSet j b ⊆ X), mass2 (F X)‖ ≤
        c * (2 * C₀ ^ 2 * ℓ⁻¹ ^ 2 * κ) ∧
      ‖∑ X ∈ (smallSets (L := L) (N := N) j).filter (fun X => blockSet j b ⊆ X),
        mass1 (-1) (F X)‖ ≤ c * (C₀ * ℓ⁻¹ * κ) := by
  obtain ⟨c, hc⟩ := card_small_containing d
  obtain ⟨C₀, hC₀, hm⟩ := exists_mass_bound d
  refine ⟨c, C₀, hC₀, ?_⟩
  intro L _ hL N j hj b hb F ℓ κ hℓ hκ hF
  have hcard := hc L N j b hb
  have hT : ∀ X ∈ (smallSets (L := L) (N := N) j).filter (fun X => blockSet j b ⊆ X),
      (Tj d (L : ℝ) j ℓ (F X)).toReal ≤ κ := fun X hX =>
    ENNReal.toReal_le_of_le_ofReal hκ (hF X hX).2
  constructor
  · refine (norm_sum_le _ _).trans ?_
    refine (sum_le_card_nsmul _ _ (2 * C₀ ^ 2 * ℓ⁻¹ ^ 2 * κ) fun X hX => ?_).trans ?_
    · have h := hm 2 L hL N j hj X (mem_smallSets.1 (mem_filter.1 hX).1) (F X) (hF X hX).1
        ![-1, 1] ℓ hℓ
      rw [LocObs.sum_fin_two] at h
      simp only [LocObs.seq_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
      have e : (∑ x, ∑ y, coeff (F X) ![(x, (-1 : ℤˣ)), (y, (1 : ℤˣ))]) = mass2 (F X) := rfl
      rw [e] at h
      refine h.trans ?_
      have := hT X hX
      have hC2 : 0 ≤ (2 : ℕ).factorial * C₀ ^ 2 * ℓ⁻¹ ^ 2 := by positivity
      calc _ ≤ (2 : ℕ).factorial * C₀ ^ 2 * ℓ⁻¹ ^ 2 * κ := mul_le_mul_of_nonneg_left this hC2
        _ = _ := by norm_num
    · rw [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
  · refine (norm_sum_le _ _).trans ?_
    refine (sum_le_card_nsmul _ _ (C₀ * ℓ⁻¹ * κ) fun X hX => ?_).trans ?_
    · have h := hm 1 L hL N j hj X (mem_smallSets.1 (mem_filter.1 hX).1) (F X) (hF X hX).1
        ![-1] ℓ hℓ
      rw [LocObs.sum_fin_one] at h
      simp only [LocObs.seq_one _ (-1) ![-1] rfl] at h
      have e : (∑ y, coeff (F X) ![(y, (-1 : ℤˣ))]) = mass1 (-1) (F X) := rfl
      rw [e] at h
      refine h.trans ?_
      have := hT X hX
      have hC1 : 0 ≤ (1 : ℕ).factorial * C₀ ^ 1 * ℓ⁻¹ ^ 1 := by positivity
      calc _ ≤ (1 : ℕ).factorial * C₀ ^ 1 * ℓ⁻¹ ^ 1 * κ := mul_le_mul_of_nonneg_left this hC1
        _ = _ := by norm_num
    · rw [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)

end

end Obs2
