module

public import ArborealDecay.TLaw
public import ArborealDecay.Surgery

/-!
# Sums against pushed-forward weights

For `f : Λ → Λ'` and the pushed-forward weights `mapW β f` (parallel edges summed, loops
dropped):

* `sum_mapW_mul`: `∑_{p,q} (mapW β f)_{pq} h_{pq} = ∑_{u,v} β_{uv} h_{f u, f v}` when `h_{pp} = 0`;
* `sum_mapW_row`: the row version `∑_m (mapW β f)_{pm} g_m`;
* `exists_of_mapW_pos`: a positive pushed weight has a positive preimage edge;
* `ind_le_mapW_ind`: `[mapW β f > 0] ≤ mapW [β > 0] f`;
* `connected_mapW`: connectivity of the support passes to `mapW β f` for surjective `f`.
-/

open Real

set_option linter.unusedSectionVars false

@[expose] public section

namespace ArborealDecay.Annulus

open ArborealDecay.Surgery ArborealDecay.TLaw

variable {Λ Λ' : Type*} [Fintype Λ] [DecidableEq Λ] [Fintype Λ'] [DecidableEq Λ']

theorem sum_mapW_mul (β : Λ → Λ → ℝ) (f : Λ → Λ') (h : Λ' → Λ' → ℝ) (hh : ∀ p, h p p = 0) :
    ∑ p, ∑ q, mapW β f p q * h p q = ∑ u, ∑ v, β u v * h (f u) (f v) := by
  have step : ∀ p q, mapW β f p q * h p q =
      ∑ u with f u = p, ∑ v with f v = q, β u v * h (f u) (f v) := by
    intro p q
    by_cases hpq : p = q
    · subst hpq
      simp only [mapW, ite_true, zero_mul]
      refine (Finset.sum_eq_zero fun u hu => Finset.sum_eq_zero fun v hv => ?_).symm
      rw [(Finset.mem_filter.1 hu).2, (Finset.mem_filter.1 hv).2, hh, mul_zero]
    · simp only [mapW, hpq, ite_false, Finset.sum_mul]
      refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv => ?_
      rw [(Finset.mem_filter.1 hu).2, (Finset.mem_filter.1 hv).2]
  simp_rw [step]
  calc ∑ p, ∑ q, ∑ u with f u = p, ∑ v with f v = q, β u v * h (f u) (f v)
      = ∑ p, ∑ u with f u = p, ∑ q, ∑ v with f v = q, β u v * h (f u) (f v) := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = ∑ p, ∑ u with f u = p, ∑ v, β u v * h (f u) (f v) := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun u _ => ?_
        exact Finset.sum_fiberwise Finset.univ f _
    _ = _ := Finset.sum_fiberwise Finset.univ f _

theorem sum_mapW_row (β : Λ → Λ → ℝ) (f : Λ → Λ') (p : Λ') (g : Λ' → ℝ) :
    ∑ m, mapW β f p m * g m =
      ∑ u with f u = p, ∑ v, if f v = p then 0 else β u v * g (f v) := by
  have step : ∀ m, mapW β f p m * g m =
      ∑ u with f u = p, ∑ v with f v = m, if f v = p then 0 else β u v * g (f v) := by
    intro m
    by_cases hpm : p = m
    · subst hpm
      simp only [mapW, ite_true, zero_mul]
      refine (Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun v hv => ?_).symm
      rw [ite_eq_left (Finset.mem_filter.1 hv).2]
    · simp only [mapW, hpm, ite_false, Finset.sum_mul]
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v hv => ?_
      have hv' := (Finset.mem_filter.1 hv).2
      rw [hv', ite_eq_right (Ne.symm hpm)]
  simp_rw [step]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  exact Finset.sum_fiberwise Finset.univ f _

theorem exists_of_mapW_pos {β : Λ → Λ → ℝ} {f : Λ → Λ'} {p q : Λ'} (h : 0 < mapW β f p q) :
    p ≠ q ∧ ∃ u v, f u = p ∧ f v = q ∧ 0 < β u v := by
  unfold mapW at h
  by_cases hpq : p = q
  · simp [hpq] at h
  · rw [ite_eq_right hpq] at h
    refine ⟨hpq, ?_⟩
    have h0 : ∑ _u ∈ Finset.univ.filter (fun u => f u = p), (0 : ℝ) <
        ∑ u ∈ Finset.univ.filter (fun u => f u = p), ∑ v ∈ Finset.univ.filter (fun v => f v = q),
          β u v := by simpa using h
    obtain ⟨u, hu, hu'⟩ := Finset.exists_lt_of_sum_lt h0
    have h1 : ∑ _v ∈ Finset.univ.filter (fun v => f v = q), (0 : ℝ) <
        ∑ v ∈ Finset.univ.filter (fun v => f v = q), β u v := by simpa using hu'
    obtain ⟨v, hv, hv'⟩ := Finset.exists_lt_of_sum_lt h1
    exact ⟨u, v, (Finset.mem_filter.1 hu).2, (Finset.mem_filter.1 hv).2, hv'⟩

theorem le_mapW {β : Λ → Λ → ℝ} (hβ0 : ∀ i j, 0 ≤ β i j) (f : Λ → Λ') {u v : Λ}
    (h : f u ≠ f v) : β u v ≤ mapW β f (f u) (f v) := by
  unfold mapW
  rw [ite_eq_right h]
  refine le_trans ?_ (Finset.single_le_sum (f := fun u' => ∑ v' with f v' = f v, β u' v')
    (fun u' _ => Finset.sum_nonneg fun v' _ => hβ0 u' v')
    (Finset.mem_filter.2 ⟨Finset.mem_univ u, rfl⟩))
  exact Finset.single_le_sum (f := fun v' => β u v') (fun v' _ => hβ0 u v')
    (Finset.mem_filter.2 ⟨Finset.mem_univ v, rfl⟩)

theorem ind_le_mapW_ind {β : Λ → Λ → ℝ} (f : Λ → Λ') (p q : Λ') :
    (if 0 < mapW β f p q then (1 : ℝ) else 0) ≤
      mapW (fun u v => if 0 < β u v then (1 : ℝ) else 0) f p q := by
  have hnn : ∀ i j, 0 ≤ (fun u v => if 0 < β u v then (1 : ℝ) else 0) i j := fun i j => by
    dsimp only; split_ifs <;> norm_num
  split_ifs with h
  · obtain ⟨hpq, u, v, rfl, rfl, huv⟩ := exists_of_mapW_pos h
    have := le_mapW hnn f hpq (u := u) (v := v)
    simp only [huv, ite_true] at this
    exact this
  · exact mapW_nonneg hnn f p q

theorem isWGraph_mapW {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j)
    (f : Λ → Λ') : IsWGraph (mapW β f) :=
  ⟨mapW_symm hβ f, mapW_nonneg hβ0 f, fun p => by simp [mapW]⟩

theorem connected_mapW {β : Λ → Λ → ℝ} (hβ0 : ∀ i j, 0 ≤ β i j) {f : Λ → Λ'}
    (hf : Function.Surjective f) (hconn : (supportGraph β).Connected) :
    (supportGraph (mapW β f)).Connected := by
  have hadj : ∀ x y, (supportGraph β).Adj x y →
      f x = f y ∨ (supportGraph (mapW β f)).Adj (f x) (f y) := by
    intro x y hxy
    by_cases h : f x = f y
    · exact Or.inl h
    · right
      simp only [supportGraph, SimpleGraph.fromRel_adj] at hxy ⊢
      refine ⟨h, ?_⟩
      rcases hxy.2 with h1 | h1
      · exact Or.inl (lt_of_lt_of_le h1 (le_mapW hβ0 f h))
      · exact Or.inr (lt_of_lt_of_le h1 (le_mapW hβ0 f (Ne.symm h)))
  have hne : Nonempty Λ := hconn.nonempty
  have : Nonempty Λ' := ⟨f hne.some⟩
  refine ⟨fun p q => ?_⟩
  obtain ⟨u, rfl⟩ := hf p
  obtain ⟨v, rfl⟩ := hf q
  exact reach_weakHom f hadj (hconn.preconnected u v)

end ArborealDecay.Annulus
