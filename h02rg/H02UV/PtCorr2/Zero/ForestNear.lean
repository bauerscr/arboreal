import PtCorr2.Zero.TwoPtGhost
import H02.Ghost
import Ward.Defs
import FRD.Dist
import Loc.Pauli

/-!
# Short distances in the arboreal gas: `P_w[u ↮ v] ≤ 1/w_{uv}`

For a forest `F` with `u ↮ v`, `F ∪ {uv}` is a forest of weight `w_{uv}` times the weight of `F`,
and `F ↦ F ∪ {uv}` is injective. Hence (`arborealProb_not_reach_mul_le`)

  `w_{uv} · P_w[u ↮ v] ≤ 1`,

uniformly in the volume and for any other weights (e.g. a ghost vertex with weights `h ≥ 0`).
With the triangle inequality for `↮` (`arborealProb_not_reach_trans`) and a nearest-neighbour path,
for the ghost arboreal gas on `Λ_N` with `β_{xy} = β·nnW`:

  `P_{β,h}[0 ↮ x] ≤ (∑_i |x_i|)/β ≤ 2|x|_∞/β`   (`ghost_not_reach_le`).
-/

namespace PtCorr2

noncomputable section

open Finset Grassmann Loc

section Pure

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem forestWeight_sup_edge {w : V → V → ℝ} (hw : ∀ i j, w i j = w j i)
    {F : SimpleGraph V} {u v : V} (huv : u ≠ v) (hn : ¬F.Adj u v) :
    H02.forestWeight w hw (F ⊔ SimpleGraph.edge u v) = w u v * H02.forestWeight w hw F := by
  unfold H02.forestWeight
  have key : ∀ s t : Finset (Sym2 V), s = insert s(u, v) t → s(u, v) ∉ t →
      ∏ e ∈ s, Sym2.lift ⟨w, hw⟩ e = w u v * ∏ e ∈ t, Sym2.lift ⟨w, hw⟩ e := by
    intro s t hs ht; subst hs; exact prod_insert ht
  refine key _ _ ?_ ?_
  · ext e
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_sup, Set.mem_union,
      SimpleGraph.edgeSet_edge_of_ne huv, Set.mem_singleton_iff, mem_insert]
    tauto
  · classical
    intro h; exact hn (SimpleGraph.mem_edgeFinset.1 h)

/-- The injection `F ↦ F ∪ {uv}` on forests with `u ↮ v`. -/
theorem sum_forest_not_reach_le {w : V → V → ℝ} (hw : ∀ i j, w i j = w j i)
    (hw0 : ∀ i j, 0 ≤ w i j) {u v : V} (huv : u ≠ v) (S : Finset (SimpleGraph V))
    (hS : ∀ F ∈ S, F.IsAcyclic ∧ ¬F.Reachable u v) :
    ∑ F ∈ S, H02.forestWeight w hw F * w u v ≤ H02.Zforest w hw := by
  classical
  set f : SimpleGraph V → SimpleGraph V := fun F => F ⊔ SimpleGraph.edge u v
  have hadj : ∀ F ∈ S, ¬F.Adj u v := fun F hF ha => (hS F hF).2 ha.reachable
  calc ∑ F ∈ S, H02.forestWeight w hw F * w u v = ∑ F ∈ S, H02.forestWeight w hw (f F) := by
        refine sum_congr rfl fun F hF => ?_
        rw [forestWeight_sup_edge hw huv (hadj F hF), mul_comm]
    _ = ∑ G ∈ S.image f, H02.forestWeight w hw G := by
        rw [sum_image]
        intro F hF G hG h
        have h' := congrArg (· \ SimpleGraph.edge u v) h
        simp only [f, sup_sdiff_right_self] at h'
        exact (SimpleGraph.sdiff_edge F (hadj F hF)).symm.trans
          (h'.trans (SimpleGraph.sdiff_edge G (hadj G hG)))
    _ ≤ H02.Zforest w hw := by
        unfold H02.Zforest
        refine sum_le_sum_of_subset_of_nonneg (fun G hG => ?_)
          fun F _ _ => H02.forestWeight_nonneg hw hw0 F
        obtain ⟨F, hF, rfl⟩ := mem_image.1 hG
        exact mem_filter.2 ⟨mem_univ _, (hS F hF).1.sup_edge_of_not_reachable (hS F hF).2⟩

/-- **`w_{uv} P_w[u ↮ v] ≤ 1`.** -/
theorem arborealProb_not_reach_mul_le {w : V → V → ℝ} (hw : ∀ i j, w i j = w j i)
    (hw0 : ∀ i j, 0 ≤ w i j) (u v : V) :
    H02.arborealProb w hw (fun F => ¬F.Reachable u v) * w u v ≤ 1 := by
  classical
  have hZ := H02.Zforest_pos hw hw0
  by_cases huv : u = v
  · subst huv
    have : H02.arborealProb w hw (fun F => ¬F.Reachable u u) = 0 := by
      unfold H02.arborealProb
      rw [div_eq_zero_iff]; left
      refine sum_eq_zero fun F hF => ?_
      simp at hF
    rw [this, zero_mul]; exact zero_le_one
  unfold H02.arborealProb
  rw [div_mul_eq_mul_div, div_le_one hZ, sum_mul]
  refine sum_forest_not_reach_le hw hw0 huv _ fun F hF => ?_
  simpa using hF

/-- Monotonicity of `P` in the event. -/
theorem arborealProb_mono {w : V → V → ℝ} (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    {A B : SimpleGraph V → Prop} (h : ∀ F, A F → B F) :
    H02.arborealProb w hw A ≤ H02.arborealProb w hw B := by
  classical
  unfold H02.arborealProb
  refine div_le_div_of_nonneg_right ?_ (H02.Zforest_pos hw hw0).le
  refine sum_le_sum_of_subset_of_nonneg (fun F hF => ?_) fun F _ _ => H02.forestWeight_nonneg hw hw0 F
  obtain ⟨-, h1, h2⟩ := mem_filter.1 hF
  exact mem_filter.2 ⟨mem_univ _, h1, h F h2⟩

/-- Union bound: `P[A] ≤ P[B] + P[C]` if `A ⊆ B ∪ C`. -/
theorem arborealProb_union_le {w : V → V → ℝ} (hw : ∀ i j, w i j = w j i)
    (hw0 : ∀ i j, 0 ≤ w i j) {A B C : SimpleGraph V → Prop} (h : ∀ F, A F → B F ∨ C F) :
    H02.arborealProb w hw A ≤ H02.arborealProb w hw B + H02.arborealProb w hw C := by
  have e := arborealProb_or_disj hw B (fun F => C F ∧ ¬B F) (fun F => B F ∨ C F)
    (fun F => by tauto) (fun F h => h.2.2 h.1)
  have h1 := arborealProb_mono hw hw0 h
  have h2 := arborealProb_mono hw hw0 (A := fun F => C F ∧ ¬B F) (B := C) fun F h => h.1
  linarith

/-- `P[u ↮ x] ≤ P[u ↮ v] + P[v ↮ x]`. -/
theorem arborealProb_not_reach_trans {w : V → V → ℝ} (hw : ∀ i j, w i j = w j i)
    (hw0 : ∀ i j, 0 ≤ w i j) (u v x : V) :
    H02.arborealProb w hw (fun F => ¬F.Reachable u x) ≤
      H02.arborealProb w hw (fun F => ¬F.Reachable u v) +
        H02.arborealProb w hw (fun F => ¬F.Reachable v x) :=
  arborealProb_union_le hw hw0 fun F h => by
    by_contra hc
    push Not at hc
    exact h (hc.1.trans hc.2)

/-- `P[A] = 1 - P[¬A]`. -/
theorem arborealProb_compl {w : V → V → ℝ} (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (A : SimpleGraph V → Prop) :
    H02.arborealProb w hw A + H02.arborealProb w hw (fun F => ¬A F) = 1 := by
  classical
  have e := arborealProb_or_disj hw A (fun F => ¬A F) (fun _ => True) (fun F => by tauto)
    (fun F h => h.2 h.1)
  have h1 : H02.arborealProb w hw (fun _ => True) = 1 := by
    unfold H02.arborealProb
    rw [div_eq_one_iff_eq (H02.Zforest_pos hw hw0).ne']
    unfold H02.Zforest
    refine sum_congr ?_ fun _ _ => rfl
    ext F; simp
  linarith

end Pure

/-! ### The ghost arboreal gas on `Λ_N` -/

variable {L N : ℕ} [NeZero L]

/-- `P_{β,h}[0 ↮ y]` (full graph on `Λ ∪ {g}`). -/
def qNR (β h : ℝ) (y : Lam 2 L N) : ℝ :=
  H02.arborealProb (H02.ghostW (Ward.nnW 2 L N β) (fun _ => h))
    (H02.ghostW_symm (Ward.nnW_symm β) _)
    (fun F => ¬F.Reachable (some (0 : Lam 2 L N)) (some y))

omit [NeZero L] in
theorem nnW_dir_ge {β : ℝ} (hβ : 0 ≤ β) (y : Lam 2 L N) (e : Dir 2) :
    β ≤ Ward.nnW 2 L N β y (y + dirVec e) := by
  unfold Ward.nnW
  have h1 : 1 ≤ (univ.filter fun e' : Dir 2 => y + dirVec e = y + dirVec e').card :=
    card_pos.2 ⟨e, mem_filter.2 ⟨mem_univ _, rfl⟩⟩
  have : (1 : ℝ) ≤ ((univ.filter fun e' : Dir 2 => y + dirVec e = y + dirVec e').card : ℝ) := by
    exact_mod_cast h1
  nlinarith

/-- One nearest-neighbour step: `P[0 ↮ y + e] ≤ P[0 ↮ y] + 1/β`. -/
theorem qNR_step {β h : ℝ} (hβ : 0 < β) (hh : 0 ≤ h) (y : Lam 2 L N) (e : Dir 2) :
    qNR β h (y + dirVec e) ≤ qNR β h y + 1 / β := by
  have hw := H02.ghostW_symm (Ward.nnW_symm (d := 2) (L := L) (N := N) β) (fun _ => h)
  have hw0 := H02.ghostW_nonneg (Ward.nnW_nonneg (d := 2) (L := L) (N := N) hβ.le)
    (h := fun _ => h) fun _ => hh
  have t := arborealProb_not_reach_trans hw hw0 (some (0 : Lam 2 L N)) (some y)
    (some (y + dirVec e))
  have m := arborealProb_not_reach_mul_le hw hw0 (some y) (some (y + dirVec e))
  rw [H02.ghostW_some_some] at m
  have hge := nnW_dir_ge hβ.le y e
  have hp := H02.arborealProb_nonneg hw hw0
    (fun F => ¬F.Reachable (some y) (some (y + dirVec e)))
  have h2 : H02.arborealProb _ hw (fun F => ¬F.Reachable (some y) (some (y + dirVec e))) ≤ 1 / β := by
    rw [le_div_iff₀ hβ]
    exact (mul_le_mul_of_nonneg_left hge hp).trans m
  unfold qNR
  linarith

theorem qNR_nsmul {β h : ℝ} (hβ : 0 < β) (hh : 0 ≤ h) (y : Lam 2 L N) (e : Dir 2) :
    ∀ k : ℕ, qNR β h (y + k • dirVec e) ≤ qNR β h y + k * (1 / β)
  | 0 => by simp
  | k + 1 => by
    have := qNR_step hβ hh (y + k • dirVec e) e
    have ih := qNR_nsmul hβ hh y e k
    rw [succ_nsmul, ← add_assoc]
    push_cast
    linarith

theorem qNR_zero {β h : ℝ} : qNR (L := L) (N := N) β h 0 = 0 := by
  classical
  unfold qNR H02.arborealProb
  rw [div_eq_zero_iff]; left
  refine sum_eq_zero fun F hF => ?_
  simp at hF

theorem qNR_sum {β h : ℝ} (hβ : 0 < β) (hh : 0 ≤ h) (α : Dir 2 → ℕ) (s : Finset (Dir 2)) :
    qNR (L := L) (N := N) β h (∑ e ∈ s, α e • (dirVec e : Lam 2 L N)) ≤ (∑ e ∈ s, (α e : ℝ)) * (1 / β) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [qNR_zero]
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha, add_comm (α a • (dirVec a : Lam 2 L N))]
    have := qNR_nsmul hβ hh (∑ e ∈ s, α e • (dirVec e : Lam 2 L N)) a (α a)
    nlinarith

/-- **`P_{β,h}[0 ↮ x] ≤ 2|x|_∞/β`.** -/
theorem qNR_le {β h : ℝ} (hβ : 0 < β) (hh : 0 ≤ h) (x : Lam 2 L N) :
    qNR β h x ≤ (2 * supNorm x : ℝ) * (1 / β) := by
  classical
  have hex : ∀ i : Fin 2, ∃ r : ℤ, (r : ZMod (L ^ N)) = (x : Fin 2 → ZMod (L ^ N)) i ∧
      r.natAbs = zabs ((x : Fin 2 → ZMod (L ^ N)) i) := fun i => FRD.exists_natAbs_eq_zabs _
  choose r hr hra using hex
  set α : Dir 2 → ℕ := fun e => match e with
    | Sum.inl i => (r i).toNat
    | Sum.inr i => (-r i).toNat with hαd
  have hx : (∑ e, α e • dirVec e : Lam 2 L N) = x := by
    have e1 : (∑ e, α e • dirVec e : Lam 2 L N) = dirHom α := rfl
    rw [e1]
    funext i
    rw [Loc.dirHom_apply, ← hr i]
    simp only [hαd]
    have : ((r i).toNat : ℤ) - ((-r i).toNat : ℤ) = r i := Int.toNat_sub_toNat_neg (r i)
    have := congrArg (fun z : ℤ => (z : ZMod (L ^ N))) this
    push_cast at this
    exact this
  have hs : (∑ e, (α e : ℝ)) ≤ 2 * supNorm x := by
    have e2 : (∑ e, (α e : ℝ)) = ∑ i : Fin 2, ((r i).natAbs : ℝ) := by
      rw [Fintype.sum_sum_type, ← sum_add_distrib]
      refine sum_congr rfl fun i _ => ?_
      simp only [hαd]
      have : (r i).toNat + (-r i).toNat = (r i).natAbs := by omega
      exact_mod_cast this
    rw [e2]
    have hle : ∀ i : Fin 2, ((r i).natAbs : ℝ) ≤ supNorm x := fun i => by
      rw [hra i]
      exact_mod_cast (Finset.le_sup (f := fun i => zabs ((x : Fin 2 → ZMod (L ^ N)) i))
        (mem_univ i))
    rw [Fin.sum_univ_two]
    linarith [hle 0, hle 1]
  have := qNR_sum (L := L) (N := N) hβ hh α univ
  rw [hx] at this
  exact this.trans (mul_le_mul_of_nonneg_right hs (by positivity))

end

end PtCorr2
