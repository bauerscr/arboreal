module

public import ArborealDecay.Wiring.Expand
public import ArborealDecay.H02
public import Mathlib

/-!
# The specialised forest polynomial `p(x, y, s)`

For a finite weighted graph with weights `β`, two vertices `a, b` and a finite set `S` of vertices
we form `p(x, y, (s_v)_{v ∈ S})`, obtained from the forest polynomial `P_G` (note eq:PG-def) by
setting every vertex variable outside `{a, b} ∪ S` to zero.  It is a polynomial in the variables
`Fin 2 ⊕ ↥S` (`x = inl 0`, `y = inl 1`, `s_v = inr v`), defined as `bind₁ phi P_G`.

* `wpoly_eq_prod`: `p = ∑_F w(F) ∏_{T} (1 + ∑_{u : T ∋ lab u} X u)`;
* `coeff_wpoly`: the coefficient of the squarefree monomial `∏_{u ∈ U} X u` is
  `∑_F w(F) · [the labelled vertices of U lie in pairwise distinct components of F]`;
* `eval_wpoly_two`: the value of `p` at `(x, y, 0)`.
-/

@[expose] public section

namespace ArborealDecay.Wiring

open MvPolynomial Finset

noncomputable section

open Classical

variable {V : Type*} [Fintype V]

/-- The forest polynomial `P_G(h)` (note eq:PG-def); same body as
`ArborealDecay.ForestPoly.forestPolynomial`. -/
def forestPolynomial (β : V → V → ℝ) (hβ : ∀ i j, β i j = β j i) : MvPolynomial V ℝ :=
  ∑ F : SimpleGraph V with F.IsAcyclic, C (∏ e ∈ F.edgeFinset, Sym2.lift ⟨β, hβ⟩ e) *
    ∏ T : F.ConnectedComponent, (1 + ∑ i with F.connectedComponentMk i = T, X i)

variable [DecidableEq V]

/-- The variable type `x, y, (s_v)_{v ∈ S}`. -/
abbrev Var (S : Finset V) := Fin 2 ⊕ ↥S

/-- The vertex labelled by a variable. -/
def lab (a b : V) (S : Finset V) : Var S → V := Sum.elim ![a, b] (fun s => s.1)

theorem lab_injective {a b : V} {S : Finset V} (hab : a ≠ b) (ha : a ∉ S) (hb : b ∉ S) :
    Function.Injective (lab a b S) := by
  have key : ∀ (i : Fin 2) (t : ↥S), ![a, b] i ≠ t.1 := by
    intro i t h
    have := t.2
    rw [← h] at this
    fin_cases i
    · exact ha this
    · exact hb this
  intro u v h
  rcases u with i | s <;> rcases v with j | t
  · simp only [lab, Sum.elim_inl] at h
    fin_cases i <;> fin_cases j <;> simp_all
  · exact absurd h (key i t)
  · exact absurd h.symm (key j s)
  · simp only [lab, Sum.elim_inr] at h
    exact congrArg Sum.inr (Subtype.ext h)

/-- The substitution `P_G ↦ p`: vertex `v` becomes the variable labelled by it (or `0`). -/
def phi (a b : V) (S : Finset V) (v : V) : MvPolynomial (Var S) ℝ :=
  ∑ u with lab a b S u = v, X u

/-- The specialised forest polynomial `p(x, y, s)`. -/
def wpoly (β : V → V → ℝ) (hβ : ∀ i j, β i j = β j i) (a b : V) (S : Finset V) :
    MvPolynomial (Var S) ℝ :=
  bind₁ (phi a b S) (forestPolynomial β hβ)

/-- The component map `u ↦ component of lab u`. -/
def cmp (a b : V) (S : Finset V) (F : SimpleGraph V) (u : Var S) : F.ConnectedComponent :=
  F.connectedComponentMk (lab a b S u)

theorem sum_phi_fiber (a b : V) (S : Finset V) (F : SimpleGraph V) (T : F.ConnectedComponent) :
    ∑ i with F.connectedComponentMk i = T, phi a b S i =
      ∑ u with cmp a b S F u = T, (X u : MvPolynomial (Var S) ℝ) := by
  unfold phi
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter fun u => cmp a b S F u = T)
    (t := Finset.univ.filter fun i => F.connectedComponentMk i = T) (g := lab a b S)
    (fun u hu => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      simpa [cmp] using hu)]
  refine Finset.sum_congr rfl fun i hi => ?_
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  constructor
  · intro h; exact ⟨by simp [cmp, h, hi], h⟩
  · intro h; exact h.2

theorem wpoly_eq_prod (β : V → V → ℝ) (hβ : ∀ i j, β i j = β j i) (a b : V) (S : Finset V) :
    wpoly β hβ a b S = ∑ F : SimpleGraph V with F.IsAcyclic,
      C (∏ e ∈ F.edgeFinset, Sym2.lift ⟨β, hβ⟩ e) *
        ∏ T : F.ConnectedComponent, (1 + ∑ u with cmp a b S F u = T, (X u : MvPolynomial (Var S) ℝ)) := by
  unfold wpoly forestPolynomial
  rw [map_sum]
  refine Finset.sum_congr (Finset.ext fun F => by simp) fun F _ => ?_
  rw [map_mul, bind₁_C_right]
  refine congrArg _ ?_
  rw [map_prod]
  refine Finset.prod_congr (Finset.ext fun T => by simp) fun T _ => ?_
  rw [map_add, map_one, map_sum]
  congr 1
  rw [← sum_phi_fiber a b S F T]
  refine Finset.sum_congr (Finset.ext fun i => by simp) fun i _ => ?_
  simp

/-- The squarefree monomial of a finite set of variables. -/
def mon {σ : Type*} [DecidableEq σ] (U : Finset σ) : σ →₀ ℕ := ∑ u ∈ U, Finsupp.single u 1

theorem mon_apply {σ : Type*} [DecidableEq σ] (U : Finset σ) (v : σ) :
    mon U v = if v ∈ U then 1 else 0 := by
  simp [mon, Finsupp.finsetSum_apply, Finsupp.single_apply]

theorem mon_injective {σ : Type*} [DecidableEq σ] : Function.Injective (mon (σ := σ)) := by
  intro U W h
  ext v
  have := congrFun (congrArg DFunLike.coe h) v
  simp only [mon_apply] at this
  by_cases hU : v ∈ U <;> by_cases hW : v ∈ W <;> simp_all

theorem eq_mon_support {σ : Type*} [DecidableEq σ] {d : σ →₀ ℕ} (hd : ∀ v, d v ≤ 1) :
    d = mon d.support := by
  ext v
  rw [mon_apply]
  by_cases h : v ∈ d.support
  · rw [if_pos h]
    have := hd v
    have : d v ≠ 0 := Finsupp.mem_support_iff.1 h
    omega
  · rw [if_neg h]; exact Finsupp.notMem_support_iff.1 h

theorem prod_X_eq_monomial {σ : Type*} [DecidableEq σ] (U : Finset σ) :
    ∏ u ∈ U, (X u : MvPolynomial σ ℝ) = monomial (mon U) 1 := by
  rw [mon, monomial_sum_one]
  rfl

/-- Coefficient formula. -/
theorem coeff_wpoly (β : V → V → ℝ) (hβ : ∀ i j, β i j = β j i) (a b : V) (S : Finset V)
    (U : Finset (Var S)) :
    (wpoly β hβ a b S).coeff (mon U) =
      ∑ F : SimpleGraph V with F.IsAcyclic, (∏ e ∈ F.edgeFinset, Sym2.lift ⟨β, hβ⟩ e) *
        if Set.InjOn (cmp a b S F) ↑U then 1 else 0 := by
  rw [wpoly_eq_prod, coeff_sum]
  refine Finset.sum_congr rfl fun F _ => ?_
  rw [coeff_C_mul]
  congr 1
  have := prod_one_add_sum_fiber (cmp a b S F) (fun u => (X u : MvPolynomial (Var S) ℝ))
    Finset.univ Finset.univ
  simp only [Finset.mem_univ, implies_true, and_true] at this
  rw [this, coeff_sum]
  simp only [prod_X_eq_monomial]
  rw [Finset.sum_eq_single U]
  · by_cases h : Set.InjOn (cmp a b S F) ↑U <;> simp [h, coeff_monomial]
  · intro W _ hW
    by_cases h : Set.InjOn (cmp a b S F) ↑W
    · simp only [h, if_true, coeff_monomial]
      rw [if_neg (fun h' => hW (mon_injective h'))]
    · simp [h]
  · simp

end

end ArborealDecay.Wiring
