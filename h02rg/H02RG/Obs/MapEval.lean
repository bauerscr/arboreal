import Obs.Free

/-!
# The block-additive evaluation of observable coupling constants (Section `sec:rgmap-ext`)

## Deviation / clarification: the split evaluation
The evaluation `e:VobsX` (`evalS`, `evalO`) puts the `σ_aσ̄_b` terms (`q`, `r`, and `η` in
Case (2)) only on sets containing *both* `a` and `b`.  It is therefore not additive over
blocks: if `a` and `b` lie in different blocks `B_a ≠ B_b`, then
`(u + V)^obs(B_a) + (u + V)^obs(B_b) ≠ (u + V)^obs(Λ)`.  On the other hand the renormalisation
group map uses `e^{-V(Λ)} = ∏_B e^{-V(B)}`, and the image of `Loc^obs_{X,B}` on the `ab`
component is attached to the points `a ∈ B` and `b ∈ B` separately (Proposition `prop:Loc-obs`
(iv): `loc^{ab}_{X,B} F = |X ∩ {a,b}|⁻¹ ∑_{z ∈ B ∩ {a,b}} (ε(F) + mass₂(F) ψ̄_zψ_z)`), with
weights depending on whether `X` contains one or both of `a, b`.  (In the text this is avoided
by centering the blocks at `a`, which forces `a, b` into the same block whenever the `ab`
couplings are nonzero.)

We therefore evaluate the coupling constants block additively (`splitS`, `splitO`):
`(u + V)^obs(X) = 1_{a ∈ X} H_a + 1_{b ∈ X} H_b` with the *halves* (`halfA`, `halfB`)
* Case (1): `H_a = -λ_a σ_a ψ̄_a + σ_aσ̄_b (-q_a + r_a ψ̄_aψ_a)`,
  `H_b = -λ_b ψ_b σ̄_b + σ_aσ̄_b (-q_b + r_b ψ̄_bψ_b)`;
* Case (2): `H_a = σ_a (-γ_a - λ_a ψ̄_aψ_a) + σ_aσ_b (-q_a - (η/4)(ψ̄_aψ_b + ψ̄_bψ_a) +
  r_a ψ̄_aψ_a)`, and `H_b` symmetrically;

i.e. with the split coupling constants `q_a, q_b, r_a, r_b` of `Obs.Coupling` everything except
the nonlocal `η` term is attached to one point (fully local); the `η` term is split `½ / ½`
between the block of `a` and the block of `b`, and everything has full weight on a set
containing both `a` and `b`.  The split evaluation is additive over disjoint sets
(`splitS_union`, `splitS_biUnion`) and agrees with `e:VobsX` on sets containing both or
neither of `a, b` (`splitS_eq_evalS`, `splitO_eq_evalO`), in particular on `Λ` and on every
set when `a, b` lie in a common block.

## Linear operations on coupling constants
`Coup.sub`, `Coup.toV` (the `V` part: `q = γ = 0`), `Coup.toU` (the `u` part: only `q, γ`),
`Coup.next` (the free flow of `lem:Vobs-flow-free`, `Coup1.next` / `Coup2.next`), with
`halfA_sub`, `halfA_toU_add_toV` etc.
-/

namespace Obs

noncomputable section

open Finset Grassmann SA

variable {Λ : Type*} [DecidableEq Λ]

/-! ### Linear operations on coupling constants -/

/-- `V - W`. -/
def Coup.sub : (c : Case) → Coup c → Coup c → Coup c
  | .one, V, W => (⟨Coup1.la V - Coup1.la W, Coup1.lb V - Coup1.lb W,
      Coup1.qa V - Coup1.qa W, Coup1.qb V - Coup1.qb W,
      Coup1.ra V - Coup1.ra W, Coup1.rb V - Coup1.rb W⟩ : Coup1)
  | .two, V, W => (⟨Coup2.la V - Coup2.la W, Coup2.lb V - Coup2.lb W,
      Coup2.ga V - Coup2.ga W, Coup2.gb V - Coup2.gb W,
      Coup2.qa V - Coup2.qa W, Coup2.qb V - Coup2.qb W, Coup2.eta V - Coup2.eta W,
      Coup2.ra V - Coup2.ra W, Coup2.rb V - Coup2.rb W⟩ : Coup2)

/-- The `V` part of the coupling constants (`q_a = q_b = γ = 0`). -/
def Coup.toV : (c : Case) → Coup c → Coup c
  | .one, V => (⟨Coup1.la V, Coup1.lb V, 0, 0, Coup1.ra V, Coup1.rb V⟩ : Coup1)
  | .two, V => (⟨Coup2.la V, Coup2.lb V, 0, 0, 0, 0, Coup2.eta V, Coup2.ra V, Coup2.rb V⟩ : Coup2)

/-- The `u` part of the coupling constants (only `q_a, q_b`, `γ`). -/
def Coup.toU : (c : Case) → Coup c → Coup c
  | .one, V => (⟨0, 0, Coup1.qa V, Coup1.qb V, 0, 0⟩ : Coup1)
  | .two, V => (⟨0, 0, Coup2.ga V, Coup2.gb V, Coup2.qa V, Coup2.qb V, 0, 0, 0⟩ : Coup2)

/-- The zero coupling constants. -/
def Coup.zero : (c : Case) → Coup c
  | .one => (⟨0, 0, 0, 0, 0, 0⟩ : Coup1)
  | .two => (⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : Coup2)

/-- The free flow of the coupling constants (`lem:Vobs-flow-free`), with `c_ab = C(a,b)`,
`c_aa = C(a,a)`, `c_bb = C(b,b)`. -/
def Coup.next : (c : Case) → Coup c → ℂ → ℂ → ℂ → Coup c
  | .one, V, cab, caa, cbb => Coup1.next V cab caa cbb
  | .two, V, cab, caa, cbb => Coup2.next V cab caa cbb

/-! ### The halves -/

/-- The half of `(u + V)^obs` attached to the point `a`. -/
def halfA : (c : Case) → Coup c → Λ → Λ → SA c Λ
  | .one, V, a, _ => ⟨0, -Coup1.la V • psibar a, 0,
      algebraMap ℂ (N Λ) (-Coup1.qa V) + Coup1.ra V • (psibar a * psi a)⟩
  | .two, V, a, b => ⟨0, algebraMap ℂ (N Λ) (-Coup2.ga V) - Coup2.la V • (psibar a * psi a), 0,
      algebraMap ℂ (N Λ) (-Coup2.qa V) - (Coup2.eta V / 4) • nx a b +
        Coup2.ra V • (psibar a * psi a)⟩

/-- The half of `(u + V)^obs` attached to the point `b`. -/
def halfB : (c : Case) → Coup c → Λ → Λ → SA c Λ
  | .one, V, _, b => ⟨0, 0, Coup1.lb V • psi b,
      algebraMap ℂ (N Λ) (-Coup1.qb V) + Coup1.rb V • (psibar b * psi b)⟩
  | .two, V, a, b => ⟨0, 0, algebraMap ℂ (N Λ) (-Coup2.gb V) - Coup2.lb V • (psibar b * psi b),
      algebraMap ℂ (N Λ) (-Coup2.qb V) - (Coup2.eta V / 4) • nx a b +
        Coup2.rb V • (psibar b * psi b)⟩

/-- The split evaluation `(u + V)^obs(X) = 1_{a ∈ X} H_a + 1_{b ∈ X} H_b`. -/
def splitS (c : Case) (V : Coup c) (a b : Λ) (X : Finset Λ) : SA c Λ :=
  ind (a ∈ X) • halfA c V a b + ind (b ∈ X) • halfB c V a b

theorem mem_OEv_halfA (c : Case) (V : Coup c) (a b : Λ) : halfA c V a b ∈ OEv c Λ := by
  cases c <;> refine mem_OEv.2 ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [halfA, isOdd_psibar', inv'_psibar_psi, inv'_nx, map_smul]

theorem mem_OEv_halfB (c : Case) (V : Coup c) (a b : Λ) : halfB c V a b ∈ OEv c Λ := by
  cases c <;> refine mem_OEv.2 ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [halfB, isOdd_psi', inv'_psibar_psi, inv'_nx, map_smul]

/-- `H_a` as an even element. -/
def halfAO (c : Case) (V : Coup c) (a b : Λ) : OE c Λ := ⟨halfA c V a b, mem_OEv_halfA c V a b⟩

/-- `H_b` as an even element. -/
def halfBO (c : Case) (V : Coup c) (a b : Λ) : OE c Λ := ⟨halfB c V a b, mem_OEv_halfB c V a b⟩

/-- The split evaluation as an even element. -/
def splitO (c : Case) (V : Coup c) (a b : Λ) (X : Finset Λ) : OE c Λ :=
  ind (a ∈ X) • halfAO c V a b + ind (b ∈ X) • halfBO c V a b

@[simp] theorem coe_splitO (c : Case) (V : Coup c) (a b : Λ) (X : Finset Λ) :
    (splitO c V a b X : SA c Λ) = splitS c V a b X := rfl

@[simp] theorem coe_halfAO (c : Case) (V : Coup c) (a b : Λ) :
    (halfAO c V a b : SA c Λ) = halfA c V a b := rfl

@[simp] theorem coe_halfBO (c : Case) (V : Coup c) (a b : Λ) :
    (halfBO c V a b : SA c Λ) = halfB c V a b := rfl

/-! ### Additivity -/

theorem ind_biUnion {ι : Type*} (s : Finset ι) (f : ι → Finset Λ)
    (hf : (s : Set ι).PairwiseDisjoint f) (x : Λ) :
    ind (x ∈ s.biUnion f) = ∑ i ∈ s, ind (x ∈ f i) := by
  classical
  by_cases hx : x ∈ s.biUnion f
  · obtain ⟨i, hi, hxi⟩ := mem_biUnion.1 hx
    rw [ind_pos hx, sum_eq_single i]
    · rw [ind_pos hxi]
    · intro k hk hki
      exact ind_neg fun h => Finset.disjoint_left.1 (hf hk hi hki) h hxi
    · exact fun h => absurd hi h
  · rw [ind_neg hx]
    symm
    refine sum_eq_zero fun i hi => ind_neg fun h => hx (mem_biUnion.2 ⟨i, hi, h⟩)

theorem splitO_empty (c : Case) (V : Coup c) (a b : Λ) : splitO c V a b ∅ = 0 := by
  simp [splitO]

/-- **Additivity** over disjoint unions. -/
theorem splitO_biUnion (c : Case) (V : Coup c) (a b : Λ) {ι : Type*} (s : Finset ι)
    (f : ι → Finset Λ) (hf : (s : Set ι).PairwiseDisjoint f) :
    splitO c V a b (s.biUnion f) = ∑ i ∈ s, splitO c V a b (f i) := by
  simp only [splitO, ind_biUnion s f hf, sum_smul, sum_add_distrib]

/-- Only `X ∩ {a, b}` matters. -/
theorem splitO_congr (c : Case) (V : Coup c) (a b : Λ) {X Y : Finset Λ} (ha : a ∈ X ↔ a ∈ Y)
    (hb : b ∈ X ↔ b ∈ Y) : splitO c V a b X = splitO c V a b Y := by
  have h1 : ind (a ∈ X) = ind (a ∈ Y) := by simp [ind, ha]
  have h2 : ind (b ∈ X) = ind (b ∈ Y) := by simp [ind, hb]
  rw [splitO, splitO, h1, h2]

/-! ### Agreement with `e:VobsX` -/

theorem halfA_add_halfB (c : Case) (V : Coup c) (a b : Λ) {X : Finset Λ} (ha : a ∈ X)
    (hb : b ∈ X) : halfA c V a b + halfB c V a b = evalS c V a b X := by
  cases c <;> ext <;> simp [halfA, halfB, evalS, ha, hb, nr, smul_add, sub_eq_add_neg]
  all_goals (simp only [Algebra.algebraMap_eq_smul_one]; module)

/-- **Agreement with `e:VobsX`** on sets containing both or neither of `a, b`. -/
theorem splitS_eq_evalS (c : Case) (V : Coup c) (a b : Λ) {X : Finset Λ}
    (h : a ∈ X ↔ b ∈ X) : splitS c V a b X = evalS c V a b X := by
  by_cases ha : a ∈ X
  · have hb := h.1 ha
    rw [splitS, ind_pos ha, ind_pos hb, one_smul, one_smul, halfA_add_halfB c V a b ha hb]
  · have hb : b ∉ X := fun hb => ha (h.2 hb)
    rw [splitS, ind_neg ha, ind_neg hb, zero_smul, zero_smul, add_zero]
    cases c <;> ext <;> simp [evalS, ha, hb]

theorem splitO_eq_evalO (c : Case) (V : Coup c) (a b : Λ) {X : Finset Λ}
    (h : a ∈ X ↔ b ∈ X) : splitO c V a b X = evalO c V a b X :=
  Subtype.ext (by rw [coe_splitO, coe_evalO, splitS_eq_evalS c V a b h])

theorem splitO_univ [Fintype Λ] (c : Case) (V : Coup c) (a b : Λ) :
    splitO c V a b univ = evalO c V a b univ :=
  splitO_eq_evalO c V a b (by simp)

/-- On a set containing `a` but not `b`, the split evaluation is the half at `a`. -/
theorem splitO_of_mem_not_mem (c : Case) (V : Coup c) (a b : Λ) {X : Finset Λ} (ha : a ∈ X)
    (hb : b ∉ X) : splitO c V a b X = halfAO c V a b := by
  simp [splitO, ha, hb]

theorem splitO_of_not_mem_mem (c : Case) (V : Coup c) (a b : Λ) {X : Finset Λ} (ha : a ∉ X)
    (hb : b ∈ X) : splitO c V a b X = halfBO c V a b := by
  simp [splitO, ha, hb]

/-! ### Linearity in the coupling constants -/

theorem halfA_sub (c : Case) (V W : Coup c) (a b : Λ) :
    halfA c (Coup.sub c V W) a b = halfA c V a b - halfA c W a b := by
  cases c <;> ext <;> simp [halfA, Coup.sub, sub_smul] <;> module

theorem halfB_sub (c : Case) (V W : Coup c) (a b : Λ) :
    halfB c (Coup.sub c V W) a b = halfB c V a b - halfB c W a b := by
  cases c <;> ext <;> simp [halfB, Coup.sub, sub_smul] <;> module

theorem splitO_sub (c : Case) (V W : Coup c) (a b : Λ) (X : Finset Λ) :
    splitO c (Coup.sub c V W) a b X = splitO c V a b X - splitO c W a b X := by
  have h1 : halfAO c (Coup.sub c V W) a b = halfAO c V a b - halfAO c W a b :=
    Subtype.ext (halfA_sub c V W a b)
  have h2 : halfBO c (Coup.sub c V W) a b = halfBO c V a b - halfBO c W a b :=
    Subtype.ext (halfB_sub c V W a b)
  rw [splitO, splitO, splitO, h1, h2, smul_sub, smul_sub]; abel

theorem halfA_toU_add_toV (c : Case) (V : Coup c) (a b : Λ) :
    halfA c (Coup.toU c V) a b + halfA c (Coup.toV c V) a b = halfA c V a b := by
  cases c <;> ext <;> simp [halfA, Coup.toU, Coup.toV] <;> module

theorem halfB_toU_add_toV (c : Case) (V : Coup c) (a b : Λ) :
    halfB c (Coup.toU c V) a b + halfB c (Coup.toV c V) a b = halfB c V a b := by
  cases c <;> ext <;> simp [halfB, Coup.toU, Coup.toV] <;> module

/-- `(u + V)^obs = u^obs + V^obs`. -/
theorem splitO_toU_add_toV (c : Case) (V : Coup c) (a b : Λ) (X : Finset Λ) :
    splitO c (Coup.toU c V) a b X + splitO c (Coup.toV c V) a b X = splitO c V a b X := by
  have h1 : halfAO c (Coup.toU c V) a b + halfAO c (Coup.toV c V) a b = halfAO c V a b :=
    Subtype.ext (halfA_toU_add_toV c V a b)
  have h2 : halfBO c (Coup.toU c V) a b + halfBO c (Coup.toV c V) a b = halfBO c V a b :=
    Subtype.ext (halfB_toU_add_toV c V a b)
  rw [splitO, splitO, splitO, ← h1, ← h2, smul_add, smul_add]; abel

theorem splitO_zero (c : Case) (a b : Λ) (X : Finset Λ) : splitO c (Coup.zero c) a b X = 0 := by
  have h1 : halfAO c (Coup.zero c) a b = 0 := by
    refine Subtype.ext ?_; cases c <;> ext <;> simp [halfA, Coup.zero]
  have h2 : halfBO c (Coup.zero c) a b = 0 := by
    refine Subtype.ext ?_; cases c <;> ext <;> simp [halfB, Coup.zero]
  rw [splitO, h1, h2, smul_zero, smul_zero, add_zero]

/-! ### Basic properties -/

theorem bulk_halfAO (c : Case) (V : Coup c) (a b : Λ) : bulk (halfAO c V a b) = 0 := by
  refine Subtype.ext ?_; rw [coe_bulk]; cases c <;> rfl

theorem bulk_halfBO (c : Case) (V : Coup c) (a b : Λ) : bulk (halfBO c V a b) = 0 := by
  refine Subtype.ext ?_; rw [coe_bulk]; cases c <;> rfl

/-- The split evaluation is observable. -/
theorem bulk_splitO (c : Case) (V : Coup c) (a b : Λ) (X : Finset Λ) :
    bulk (splitO c V a b X) = 0 := by
  simp [splitO, bulk_halfAO, bulk_halfBO]

end

end Obs
