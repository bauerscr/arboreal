module

public import ArborealDecay.SimonLieb.PathFactor

/-!
# The global Simon–Lieb inequality (`prop:Simon-Lieb`)

For `x ∈ D`, `z ∉ D`:
`τ(x, z) ≤ ∑_{u ∈ D, v ∉ D, uv ∈ E} μ(uv ∈ F) τ(x, u) τ(v, z)` (conditional on `hstab`).

Proof: path-sum identity; every simple `x`–`z` path decomposes as `α · uv · δ` with `u ∈ D`,
`v ∉ D` (`exists_exit`); path factorization (`path_factor_of_stable`); summing over all
decompositions (an upper bound, since every path is hit at least once and all terms are
nonnegative) and the path-sum identity for `τ(x, u)` and `τ(v, z)`.
-/

@[expose] public section

namespace ArborealDecay.SimonLieb

universe u

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical SimpleGraph

variable {Λ : Type u} [Fintype Λ] [DecidableEq Λ]

/-- Every walk from inside `D` to outside `D` crosses the boundary along an edge `uv`,
`u ∈ D`, `v ∉ D`. -/
theorem exists_exit (D : Finset Λ) {a z : Λ} (w : (⊤ : SimpleGraph Λ).Walk a z) (ha : a ∈ D)
    (hz : z ∉ D) :
    ∃ (u v : Λ) (huv : (⊤ : SimpleGraph Λ).Adj u v) (α : (⊤ : SimpleGraph Λ).Walk a u)
      (δ : (⊤ : SimpleGraph Λ).Walk v z), u ∈ D ∧ v ∉ D ∧ w = α.append (Walk.cons huv δ) := by
  induction w with
  | nil => exact absurd ha hz
  | @cons a b c h p ih =>
    by_cases hb : b ∈ D
    · obtain ⟨u, v, huv, α, δ, hu, hv, hw⟩ := ih hb hz
      exact ⟨u, v, huv, Walk.cons h α, δ, hu, hv, by rw [hw, Walk.cons_append]⟩
    · exact ⟨a, b, h, Walk.nil, p, ha, hb, rfl⟩

/-- Index of a decomposition `α · uv · δ` of an `x`–`z` walk. -/
abbrev DecompIdx (x z : Λ) : Type u :=
  Σ e : {p : Λ × Λ // p.1 ≠ p.2},
    (⊤ : SimpleGraph Λ).Path x e.1.1 × (⊤ : SimpleGraph Λ).Path e.1.2 z

/-- The walk `α · uv · δ`. -/
def glue {x z : Λ} (t : DecompIdx x z) : (⊤ : SimpleGraph Λ).Walk x z :=
  t.2.1.1.append (Walk.cons ((top_adj _ _).2 t.1.2) t.2.2.1)

theorem exists_decompIdx (D : Finset Λ) {x z : Λ} (hx : x ∈ D) (hz : z ∉ D)
    (γ : (⊤ : SimpleGraph Λ).Path x z) :
    ∃ t : DecompIdx x z, t.1.1.1 ∈ D ∧ t.1.1.2 ∉ D ∧ glue t = γ.1 := by
  obtain ⟨u, v, huv, α, δ, hu, hv, hw⟩ := exists_exit D γ.1 hx hz
  have hγ := γ.2
  rw [hw] at hγ
  have hα : α.IsPath := hγ.of_append_left
  have hδ : δ.IsPath := (hγ.of_append_right).of_cons
  refine ⟨⟨⟨(u, v), huv.ne⟩, ⟨α, hα⟩, ⟨δ, hδ⟩⟩, hu, hv, ?_⟩
  rw [hw]
  rfl

/-- **Global Simon–Lieb inequality** (`prop:Simon-Lieb`; conditional on `hstab`). -/
theorem simon_lieb_of_stable
    (hstab : ∀ (U : Type u) [Fintype U] [DecidableEq U] (β : U → U → ℝ)
      (hβ : ∀ i j, β i j = β j i), (∀ i j, 0 ≤ β i j) → ∀ z : U → ℂ, (∀ j, 0 < (z j).im) →
        MvPolynomial.aeval z (forestPolynomial β hβ) ≠ 0)
    {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j)
    (D : Finset Λ) (x z : Λ) (hx : x ∈ D) (hz : z ∉ D) :
    H02.arborealProb β hβ (fun F => F.Reachable x z) ≤
      ∑ u ∈ D, ∑ v ∈ Dᶜ, if u ≠ v ∧ β u v ≠ 0 then
        H02.arborealProb β hβ (fun F => F.Adj u v) *
          H02.arborealProb β hβ (fun F => F.Reachable x u) *
          H02.arborealProb β hβ (fun F => F.Reachable v z) else 0 := by
  have hμ0 : ∀ P, 0 ≤ H02.arborealProb β hβ P := fun P => H02.arborealProb_nonneg hβ hβ0 P
  set f : (⊤ : SimpleGraph Λ).Walk x z → ℝ :=
    fun w => H02.arborealProb β hβ (fun F => ∀ e ∈ w.edges, e ∈ F.edgeSet) with hf
  set g : DecompIdx x z → ℝ := fun t =>
    if t.1.1.1 ∈ D ∧ t.1.1.2 ∉ D ∧ β t.1.1.1 t.1.1.2 ≠ 0 then
      H02.arborealProb β hβ (fun F => F.Adj t.1.1.1 t.1.1.2) * H02.arborealProb β hβ (Forest.pathEvent t.2.1) *
        H02.arborealProb β hβ (Forest.pathEvent t.2.2) else 0 with hg
  have hg0 : ∀ t, 0 ≤ g t := by
    intro t
    simp only [hg]
    split_ifs
    · exact mul_nonneg (mul_nonneg (hμ0 _) (hμ0 _)) (hμ0 _)
    · exact le_rfl
  set T := univ.filter fun t : DecompIdx x z => t.1.1.1 ∈ D ∧ t.1.1.2 ∉ D ∧ (glue t).IsPath
    with hT
  -- the section
  let sec : (⊤ : SimpleGraph Λ).Path x z → DecompIdx x z := fun γ =>
    Classical.choose (exists_decompIdx D hx hz γ)
  have hsec : ∀ γ, (sec γ).1.1.1 ∈ D ∧ (sec γ).1.1.2 ∉ D ∧ glue (sec γ) = γ.1 := fun γ =>
    Classical.choose_spec (exists_decompIdx D hx hz γ)
  have hinj : Set.InjOn sec ↑(univ : Finset ((⊤ : SimpleGraph Λ).Path x z)) := by
    intro γ _ γ' _ h
    apply Subtype.ext
    rw [← (hsec γ).2.2, ← (hsec γ').2.2, h]
  -- step 1: path sum, reindexed by the section
  have step1 : H02.arborealProb β hβ (fun F => F.Reachable x z) ≤ ∑ t ∈ T, f (glue t) := by
    rw [Forest.arborealProb_reachable_eq_sum hβ x z]
    calc ∑ γ : (⊤ : SimpleGraph Λ).Path x z, H02.arborealProb β hβ (Forest.pathEvent γ)
        = ∑ γ : (⊤ : SimpleGraph Λ).Path x z, f (glue (sec γ)) := by
          refine Finset.sum_congr rfl fun γ _ => ?_
          simp only [hf, (hsec γ).2.2]
          rfl
      _ = ∑ t ∈ univ.image sec, f (glue t) := (Finset.sum_image (f := fun t => f (glue t)) hinj).symm
      _ ≤ ∑ t ∈ T, f (glue t) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun t _ _ => hμ0 _
          intro t ht
          obtain ⟨γ, _, rfl⟩ := Finset.mem_image.1 ht
          simp only [hT, mem_filter, mem_univ, true_and]
          refine ⟨(hsec γ).1, (hsec γ).2.1, ?_⟩
          rw [(hsec γ).2.2]
          exact γ.2
  -- step 2: path factorization
  have step2 : ∀ t ∈ T, f (glue t) ≤ g t := by
    intro t ht
    simp only [hT, mem_filter, mem_univ, true_and] at ht
    obtain ⟨hu, hv, hpath⟩ := ht
    obtain ⟨⟨⟨u, v⟩, huv⟩, α, δ⟩ := t
    simp only at hu hv huv
    by_cases hb : β u v = 0
    · have : f (glue ⟨⟨(u, v), huv⟩, α, δ⟩) = 0 := by
        simp only [hf]
        unfold H02.arborealProb
        rw [Finset.sum_eq_zero, zero_div]
        intro F hF
        simp only [mem_filter, mem_univ, true_and] at hF
        refine Surgery.forestWeight_eq_zero_of_adj hβ hb (p := u) (i := v) ?_
        have := hF.2 s(u, v) (by
          simp only [glue, Walk.edges_append, Walk.edges_cons, List.mem_append, List.mem_cons]
          simp)
        exact this
      rw [this]
      exact hg0 _
    · have hgt : g ⟨⟨(u, v), huv⟩, α, δ⟩ = H02.arborealProb β hβ (fun F => F.Adj u v) * H02.arborealProb β hβ (Forest.pathEvent α) *
          H02.arborealProb β hβ (Forest.pathEvent δ) := by
        simp only [hg]
        rw [ite_eq_left ⟨hu, hv, hb⟩]
      rw [hgt]
      exact path_factor_of_stable hstab hβ hβ0 ((top_adj _ _).2 huv) α.1 δ.1 hpath
  -- step 3: sum over all decompositions
  have step3 : ∑ t ∈ T, g t ≤ ∑ t : DecompIdx x z, g t :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun t _ _ => hg0 t
  have step4 : ∑ t : DecompIdx x z, g t = ∑ e : {p : Λ × Λ // p.1 ≠ p.2},
      if e.1.1 ∈ D ∧ e.1.2 ∉ D ∧ β e.1.1 e.1.2 ≠ 0 then
        H02.arborealProb β hβ (fun F => F.Adj e.1.1 e.1.2) * H02.arborealProb β hβ (fun F => F.Reachable x e.1.1) *
          H02.arborealProb β hβ (fun F => F.Reachable e.1.2 z) else 0 := by
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [hg]
    split_ifs with hc
    · rw [Fintype.sum_prod_type, Forest.arborealProb_reachable_eq_sum hβ x e.1.1,
        Forest.arborealProb_reachable_eq_sum hβ e.1.2 z, mul_assoc, Finset.sum_mul_sum,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun δ _ => ?_
      ring
    · simp
  have step5 : (∑ e : {p : Λ × Λ // p.1 ≠ p.2},
      if e.1.1 ∈ D ∧ e.1.2 ∉ D ∧ β e.1.1 e.1.2 ≠ 0 then
        H02.arborealProb β hβ (fun F => F.Adj e.1.1 e.1.2) * H02.arborealProb β hβ (fun F => F.Reachable x e.1.1) *
          H02.arborealProb β hβ (fun F => F.Reachable e.1.2 z) else 0) =
      ∑ u ∈ D, ∑ v ∈ Dᶜ, if u ≠ v ∧ β u v ≠ 0 then
        H02.arborealProb β hβ (fun F => F.Adj u v) * H02.arborealProb β hβ (fun F => F.Reachable x u) *
          H02.arborealProb β hβ (fun F => F.Reachable v z) else 0 := by
    rw [← Finset.sum_subtype (univ.filter fun p : Λ × Λ => p.1 ≠ p.2) (by simp)
      (fun p : Λ × Λ => if p.1 ∈ D ∧ p.2 ∉ D ∧ β p.1 p.2 ≠ 0 then
        H02.arborealProb β hβ (fun F => F.Adj p.1 p.2) * H02.arborealProb β hβ (fun F => F.Reachable x p.1) *
          H02.arborealProb β hβ (fun F => F.Reachable p.2 z) else 0),
      Finset.sum_filter, Fintype.sum_prod_type]
    have hS : ∀ (S : Finset Λ) (h : Λ → ℝ), ∑ u ∈ S, h u = ∑ u, if u ∈ S then h u else 0 :=
      fun S h => by rw [Finset.sum_ite_mem, Finset.univ_inter]
    rw [hS D]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hu : u ∈ D
    · rw [ite_eq_left hu, hS Dᶜ]
      refine Finset.sum_congr rfl fun v _ => ?_
      by_cases hv : v ∈ D
      · simp [hu, hv]
      · by_cases huv : u = v
        · simp [huv]
        · simp [hu, hv, huv]
    · rw [ite_eq_right hu]
      refine Finset.sum_eq_zero fun v _ => ?_
      simp [hu]
  calc H02.arborealProb β hβ (fun F => F.Reachable x z) ≤ ∑ t ∈ T, f (glue t) := step1
    _ ≤ ∑ t ∈ T, g t := Finset.sum_le_sum step2
    _ ≤ ∑ t : DecompIdx x z, g t := step3
    _ = _ := step4.trans step5

end

end ArborealDecay.SimonLieb
