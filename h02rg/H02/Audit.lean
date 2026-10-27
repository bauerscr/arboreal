import H02

/-!
# Audit of `H02.thm_H02forest`

Run with `lake env lean H02/Audit.lean` (after `lake build`).

This file is not part of the library. It
1. prints every definition the statement depends on, for comparison with `h02.tex`;
2. restates the theorem verbatim, so the statement is visible without reading the proof;
3. prints the axioms the proof depends on (expected: `propext`, `Classical.choice`,
   `Quot.sound` only — no `sorryAx`, no custom axioms);
4. checks basic properties of the definitions directly against the paper;
5. specializes the theorem to two vertices, where both sides can be computed by hand:
   `[1]_{β,h} = (1 + h₀)(1 + h₁) + β₀₁ (1 + h₀ + h₁)`;
6. does the same (definitions, statements, axioms) for Corollary `cor:spin`;
7. does the same for the Ward identity `e:ward` of `h02rg.tex`.
-/

open H02

/-! ## 1. Definitions used in the statement -/

#print H02.Gen
#print H02.Grassmann
#print H02.ξ
#print H02.η
#print H02.z
#print H02.dot
#print H02.dξ
#print H02.dη
#print H02.intStep
#print H02.berezin
#print H02.int0
#print H02.action
#print H02.expect

/-! ## 2. The statement -/

open Classical in
example {Λ : Type*} [DecidableEq Λ] [Fintype Λ]
    (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) (h : Λ → ℝ) :
    expect β h 1 = ∑ F : SimpleGraph Λ with F.IsAcyclic,
      (∏ e ∈ F.edgeFinset, Sym2.lift ⟨β, hβ⟩ e) *
        ∏ T : F.ConnectedComponent, (1 + ∑ i with F.connectedComponentMk i = T, h i) :=
  thm_H02forest β hβ h

/-! ## 3. Axioms -/

#print axioms H02.thm_H02forest

/-! ## 4. Sanity checks of the definitions -/

section Sanity

variable {Λ : Type*} [DecidableEq Λ]

-- `∂_{ξ_i} ξ_j = δ_{ij}`, `∂_{ξ_i} η_j = 0`, and likewise for `∂_{η_i}`.
example (i j : Λ) : dξ i (ξ j) = if i = j then 1 else 0 := dξ_ξ i j
example (i j : Λ) : dξ i (η j) = 0 := dξ_η i j
example (i j : Λ) : dη i (η j) = if i = j then 1 else 0 := dη_η i j
example (i j : Λ) : dη i (ξ j) = 0 := dη_ξ i j

-- `∂_ξ` is an odd derivation: `∂(ab) = (∂a) b ± a (∂b)` (sign from the grade involution).
example (i : Λ) (a b : Grassmann Λ) : dξ i (a * b) = dξ i a * b + inv' a * dξ i b := dξ_mul i a b

-- The generators anticommute.
example (i j : Λ) : ξ i * η j = -(η j * ξ i) := ξ_anticomm_η i j
example (i : Λ) : ξ i * ξ i = 0 := ξ_mul_ξ i

-- `1/z_i = 1 + ξ_i η_i`, as used in the proof of Lemma `lem:tree`.
example (i : Λ) : Ring.inverse (z i) = 1 + ξ i * η i := inverse_z i

-- `u_i · u_i = -1` (the `ℍ^{0|2}` constraint) and symmetry of the inner product.
example (i : Λ) : dot i i = -1 := by
  have := congrArg cv (Xc_self i)
  rw [coe_Xc, map_zero] at this
  exact eq_neg_of_add_eq_zero_right this
example (i j : Λ) : dot i j = dot j i := by
  have := congrArg cv (Xc_comm i j); simpa [coe_Xc] using this

-- One step of the integral: `∫ ξη = 1` and `∫ 1 = 1` at a single vertex.
example (i : Λ) : intStep i (ξ i * η i) = 1 := intStep_ξη i
example (i : Λ) : intStep i 1 = 1 := by
  rw [intStep_apply, mul_one, map_add, dξ_one, zero_add, dξ_mul, dξ_ξ, dξ_η, if_pos rfl]
  simp [dη_η]

-- The integral does not depend on the enumeration of the vertices.
example (l l' : List Λ) (hp : l.Perm l') : berezin l = berezin l' := berezin_perm hp

end Sanity

/-! ## 5. The two-vertex case -/

-- Two helpers that work for any `Fintype` instance (avoids decidability-instance mismatches).
theorem audit_prod_bij {α β M : Type*} [CommMonoid M] [Fintype α] {inst : Fintype β}
    (e : α → β) (he : Function.Bijective e) (g : β → M) :
    @Finset.prod _ _ _ (@Finset.univ β inst) g = ∏ a, g (e a) := by
  convert (Fintype.prod_bijective e he (fun a => g (e a)) g (fun _ => rfl)).symm

theorem audit_prod_single {α M : Type*} [CommMonoid M] {inst : Fintype α} (g : α → M) (a : α)
    (ha : ∀ b, b = a) : @Finset.prod _ _ _ (@Finset.univ α inst) g = g a :=
  Finset.prod_eq_single a (fun b _ hb => absurd (ha b) hb) (fun h0 => absurd (Finset.mem_univ a) h0)

open Classical in
theorem audit_two_vertices (β : Fin 2 → Fin 2 → ℝ) (hβ : ∀ i j, β i j = β j i)
    (h : Fin 2 → ℝ) :
    expect β h 1 = (1 + h 0) * (1 + h 1) + β 0 1 * (1 + h 0 + h 1) := by
  rw [thm_H02forest β hβ h]
  -- every graph on two vertices is a forest, and there are exactly two graphs: `⊥` and `⊤`
  have hacyc : ∀ G : SimpleGraph (Fin 2), G.IsAcyclic := fun G =>
    SimpleGraph.IsAcyclic.of_card_le_two (by simp)
  have huniv : (Finset.univ.filter fun G : SimpleGraph (Fin 2) => G.IsAcyclic) = {⊥, ⊤} := by
    ext G
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hacyc, Finset.mem_insert,
      Finset.mem_singleton, true_iff]
    by_cases h01 : G.Adj 0 1
    · right; ext a b
      fin_cases a <;> fin_cases b <;> simp [h01, h01.symm]
    · have h10 : ¬G.Adj 1 0 := fun h => h01 h.symm
      left; ext a b
      fin_cases a <;> fin_cases b <;> simp [h01, h10]
  rw [huniv, Finset.sum_pair bot_ne_top]
  congr 1
  · -- `⊥`: no edges, two singleton components
    have hbij : Function.Bijective (⊥ : SimpleGraph (Fin 2)).connectedComponentMk :=
      ⟨fun a b hab => SimpleGraph.reachable_bot.1 (SimpleGraph.ConnectedComponent.eq.1 hab),
        fun T => T.ind fun v => ⟨v, rfl⟩⟩
    rw [Finset.prod_eq_one (fun e he => by simp at he), one_mul, audit_prod_bij _ hbij]
    simp [Fin.prod_univ_two, Finset.filter_eq']
  · -- `⊤`: the single edge `01`, one component containing both vertices
    have hE : ∀ e : Sym2 (Fin 2), e ∈ (⊤ : SimpleGraph (Fin 2)).edgeSet ↔ e ∈ ({s(0, 1)} : Finset _) := by
      intro e; induction e using Sym2.ind with
      | h a b => fin_cases a <;> fin_cases b <;> simp [Sym2.eq_swap]
    have hc : ∀ T : (⊤ : SimpleGraph (Fin 2)).ConnectedComponent,
        T = (⊤ : SimpleGraph (Fin 2)).connectedComponentMk 0 := by
      intro T; induction T using SimpleGraph.ConnectedComponent.ind with
      | h v =>
        refine SimpleGraph.ConnectedComponent.eq.2 ?_
        by_cases hv : v = 0
        · rw [hv]
        · exact ((SimpleGraph.top_adj v 0).2 hv).reachable
    rw [edgeFinset_eq_of hE, Finset.prod_singleton,
      audit_prod_single _ _ hc]
    simp [Fin.sum_univ_two, add_assoc]

#print axioms audit_two_vertices

/-! ## 6. Corollary `cor:spin` -/

#print H02.edgeSpin
#print H02.edgeProd
#print H02.forestWeight
#print H02.Zforest
#print H02.arborealProb
#print H02.avg

section Corollary

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

-- (e:edge-spin)  `P_β[ab] = β_ab ⟨u_a · u_b + 1⟩_β`
example (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) (a b : Λ) :
    arborealProb β hβ (fun F => F.Adj a b) = β a b * avg β 0 (dot a b + 1) :=
  cor_spin_edge hβ a b

-- (e:edges-spin)  `P_β[S] = ⟨∏_{ij ∈ S} β_ij (u_i · u_j + 1)⟩_β`
example (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) (S : Finset (Sym2 Λ)) :
    arborealProb β hβ (fun F => ↑S ⊆ F.edgeSet) = avg β 0 (edgeProd β hβ S) :=
  cor_spin_edges hβ S

-- (e:conn-spin)
-- `P_β[a ↔ b] = -⟨z_a z_b⟩_β = -⟨u_a · u_b⟩_β = ⟨ξ_a η_b⟩_β = 1 - ⟨η_a ξ_a η_b ξ_b⟩_β`
example (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j) (a b : Λ) :
    arborealProb β hβ (fun F => F.Reachable a b) = -avg β 0 (z a * z b) ∧
    -avg β 0 (z a * z b) = -avg β 0 (dot a b) ∧
    -avg β 0 (dot a b) = avg β 0 (ξ a * η b) ∧
    avg β 0 (ξ a * η b) = 1 - avg β 0 (η a * ξ a * η b * ξ b) :=
  cor_spin_conn hβ hβ0 a b

-- (eq:expz0)  `⟨z_a⟩_β = 0`
example (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) (a : Λ) : avg β 0 (z a) = 0 :=
  cor_spin_z β hβ a

-- Sanity check: `P_β` is normalised for non-negative weights.
example (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j) :
    arborealProb β hβ (fun _ => True) = 1 := by
  rw [arborealProb, div_eq_one_iff_eq (Zforest_pos hβ hβ0).ne', Zforest]
  exact Finset.sum_congr (by ext; simp) fun _ _ => rfl

-- Sanity check: `[1]_β = Z_β` (the `h = 0` case of the theorem).
example (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) : expect β 0 1 = Zforest β hβ :=
  expect_one_eq_Z β hβ

end Corollary

#print axioms H02.cor_spin_edge
#print axioms H02.cor_spin_edges
#print axioms H02.cor_spin_conn
#print axioms H02.cor_spin_z

/-! ## 7. The Ward identity `e:ward` (`h02rg.tex`) -/

#print H02.T

section Ward

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

-- (e:ward)  `⟨z_a⟩_{β,h} = ⟨T ξ_a⟩_{β,h} = -∑_x h ⟨ξ_a T z_x⟩_{β,h} = h ∑_x ⟨ξ_a η_x⟩_{β,h}`
example (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) (h : ℝ) (a : Λ) :
    avg β (fun _ => h) (z a) = avg β (fun _ => h) (T Finset.univ (ξ a)) ∧
    avg β (fun _ => h) (T Finset.univ (ξ a)) =
      -∑ x, h * avg β (fun _ => h) (ξ a * T Finset.univ (z x)) ∧
    -∑ x, h * avg β (fun _ => h) (ξ a * T Finset.univ (z x)) =
      h * ∑ x, avg β (fun _ => h) (ξ a * η x) :=
  ward β hβ h a

-- Sanity check: `T = ∑_x z_x ∂_{ξ_x}` (`e:Tdef`).
example (x : Grassmann Λ) : T Finset.univ x = ∑ i, z i * dξ i x := T_apply _ x

end Ward

#print axioms H02.ward
