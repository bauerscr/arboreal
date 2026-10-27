import Spin2.Multiscale.Conn

/-!
# Symmetry and continuity of the connection probability

`h02uv-outline.tex`, `thm:limit`: the limit `P(x)` is invariant under the symmetries of `ℤ²`.
At finite volume this is exact:

* `H02.arborealProb_map_equiv`, `H02.arborealProb_reachable_equiv`: the arboreal gas law is
  invariant under a vertex bijection `σ` with `β_{σi,σj} = β_{ij}` (reindexing of the forest
  sum `F ↦ σ(F)`).
* `Ward.nnW_translate`, `Ward.nnW_aut`: the nearest-neighbour weights are invariant under
  translations and under additive injections of the torus permuting the unit vectors `𝓔_d`;
  `Ward.sgnPerm τ s` (`x ↦ (±x_{τ⁻¹ i})_i`) is the hyperoctahedral point group.
* `Spin2.PconnXY L N β y x = P_β[y ↔ x]`, `PconnXY_eq : PconnXY y x = Pconn (x - y)`,
  `PconnXY_comm`.
* `Spin2.Pconn_sgnPerm` (full point group), `Pconn_neg`, `Pconn_swap`, `Pconn_refl`.
* `Spin2.Pconn_continuousOn : ContinuousOn (fun β => Pconn L N β x) (Ici 0)`.
-/

namespace H02

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

theorem forestWeight_map_equiv (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) (σ : Λ ≃ Λ)
    (hσ : ∀ i j, β (σ i) (σ j) = β i j) (F : SimpleGraph Λ) :
    forestWeight β hβ (F.map σ.toEmbedding) = forestWeight β hβ F := by
  unfold forestWeight
  refine (Finset.prod_congr (s₂ := F.edgeFinset.map σ.toEmbedding.sym2Map) ?_
    fun _ _ => rfl).trans ?_
  · convert SimpleGraph.edgeFinset_map σ.toEmbedding F
  rw [Finset.prod_map]
  refine Finset.prod_congr rfl fun e _ => ?_
  induction e using Sym2.ind with | h i j => simp [hσ]

theorem sum_forest_map_equiv (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) (σ : Λ ≃ Λ)
    (hσ : ∀ i j, β (σ i) (σ j) = β i j) (Q : SimpleGraph Λ → Prop) :
    ∑ F : SimpleGraph Λ with F.IsAcyclic ∧ Q (F.map σ.toEmbedding), forestWeight β hβ F =
      ∑ F : SimpleGraph Λ with F.IsAcyclic ∧ Q F, forestWeight β hβ F := by
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Fintype.sum_equiv σ.simpleGraph _ _ fun F => ?_
  have hm : σ.simpleGraph F = F.map σ.toEmbedding := SimpleGraph.comap_symm F σ
  rw [hm, forestWeight_map_equiv β hβ σ hσ, (SimpleGraph.Iso.map σ F).isAcyclic_iff]

/-- Invariance of the arboreal gas under a weight-preserving vertex bijection. -/
theorem arborealProb_map_equiv (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) (σ : Λ ≃ Λ)
    (hσ : ∀ i j, β (σ i) (σ j) = β i j) (Q : SimpleGraph Λ → Prop) :
    arborealProb β hβ (fun F => Q (F.map σ.toEmbedding)) = arborealProb β hβ Q := by
  unfold arborealProb
  rw [sum_forest_map_equiv β hβ σ hσ Q]

/-- `P_β[a ↔ b] = P_β[σa ↔ σb]` for a weight-preserving vertex bijection `σ`. -/
theorem arborealProb_reachable_equiv (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) (σ : Λ ≃ Λ)
    (hσ : ∀ i j, β (σ i) (σ j) = β i j) (a b : Λ) :
    arborealProb β hβ (fun F => F.Reachable a b) =
      arborealProb β hβ (fun F => F.Reachable (σ a) (σ b)) := by
  have : (fun F : SimpleGraph Λ => F.Reachable a b) =
      fun F => (F.map σ.toEmbedding).Reachable (σ a) (σ b) :=
    funext fun F => propext (SimpleGraph.Iso.map σ F).reachable_iff.symm
  rw [this]
  exact arborealProb_map_equiv β hβ σ hσ (fun F => F.Reachable (σ a) (σ b))

end

end H02

namespace Ward

noncomputable section

open Finset Grassmann Loc

set_option linter.unusedSectionVars false

variable {d L N : ℕ} [NeZero L]

/-- Translation invariance of the nearest-neighbour weights. -/
theorem nnW_translate (β : ℝ) (t x y : Lam d L N) :
    nnW d L N β (x + t) (y + t) = nnW d L N β x y := by
  unfold nnW
  congr 3
  ext e
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro h; rw [add_right_comm] at h; exact add_right_cancel h
  · intro h; rw [h]; abel

/-- Invariance of the nearest-neighbour weights under an additive injection of the torus that
permutes the unit vectors `𝓔_d`. -/
theorem nnW_aut (β : ℝ) (φ : Lam d L N →+ Lam d L N) (hφ : Function.Injective φ)
    (π : Dir d ≃ Dir d) (hπ : ∀ e, φ (dirVec e) = dirVec (π e)) (x y : Lam d L N) :
    nnW d L N β (φ x) (φ y) = nnW d L N β x y := by
  unfold nnW
  congr 2
  rw [Finset.card_filter, Finset.card_filter, ← Equiv.sum_comp π]
  refine Finset.sum_congr rfl fun e _ => ?_
  have : (φ y = φ x + dirVec (π e)) ↔ y = x + dirVec e := by
    rw [← hπ, ← map_add, hφ.eq_iff]
  simp only [this]

/-- The direction relabelling `𝓔_d → 𝓔_d` of a signed permutation. -/
def dirFlip (s : Fin d → Bool) : Dir d → Dir d
  | Sum.inl i => if s i then Sum.inr i else Sum.inl i
  | Sum.inr i => if s i then Sum.inl i else Sum.inr i

theorem dirFlip_invol (s : Fin d → Bool) : Function.Involutive (dirFlip s) := by
  intro e; rcases e with i | i <;> cases h : s i <;> simp [dirFlip, h]

/-- The point-group direction permutation `e ↦ ±e_{τ i}`. -/
def dirSgnPerm (τ : Equiv.Perm (Fin d)) (s : Fin d → Bool) : Dir d ≃ Dir d :=
  (Equiv.sumCongr τ τ).trans (dirFlip_invol s).toPerm

variable (d L N) in
/-- The signed permutation `x ↦ (s_i x_{τ⁻¹ i})_i` of the torus, `s_i = -1` iff `s i`
(the hyperoctahedral point group of `ℤ^d`). -/
def sgnPerm (τ : Equiv.Perm (Fin d)) (s : Fin d → Bool) : Lam d L N →+ Lam d L N where
  toFun x := fun i => if s i then -((x : Fin d → ZMod (L ^ N)) (τ.symm i))
    else (x : Fin d → ZMod (L ^ N)) (τ.symm i)
  map_zero' := by funext i; show (if s i then -(0 : ZMod (L ^ N)) else 0) = 0; simp
  map_add' x y := by
    funext i
    show (if s i then -((x : Fin d → ZMod (L ^ N)) (τ.symm i) + y (τ.symm i)) else
      (x : Fin d → ZMod (L ^ N)) (τ.symm i) + y (τ.symm i)) = (if s i then -(x (τ.symm i))
      else x (τ.symm i)) + (if s i then -(y (τ.symm i)) else y (τ.symm i))
    split_ifs <;> abel

theorem sgnPerm_apply (τ : Equiv.Perm (Fin d)) (s : Fin d → Bool) (x : Lam d L N) (i : Fin d) :
    (sgnPerm d L N τ s x : Fin d → ZMod (L ^ N)) i =
      if s i then -((x : Fin d → ZMod (L ^ N)) (τ.symm i)) else x (τ.symm i) := rfl

theorem sgnPerm_injective (τ : Equiv.Perm (Fin d)) (s : Fin d → Bool) :
    Function.Injective (sgnPerm d L N τ s) := by
  intro x y h
  funext i
  have := congrFun (show (sgnPerm d L N τ s x : Fin d → ZMod (L ^ N)) =
    sgnPerm d L N τ s y from h) (τ i)
  rw [sgnPerm_apply, sgnPerm_apply, Equiv.symm_apply_apply] at this
  split_ifs at this
  · exact neg_inj.1 this
  · exact this

theorem sgnPerm_dirVec (τ : Equiv.Perm (Fin d)) (s : Fin d → Bool) (e : Dir d) :
    sgnPerm d L N τ s (dirVec e) = dirVec (dirSgnPerm τ s e) := by
  funext i
  rw [sgnPerm_apply]
  rcases e with j | j
  · show _ = (dirVec (dirFlip s (Sum.inl (τ j))) : Fin d → ZMod (L ^ N)) i
    by_cases hi : i = τ j
    · subst hi
      cases h : s (τ j) <;>
        simp [dirFlip, h, dirVec]
    · have hj : τ.symm i ≠ j := fun h => hi (by rw [← h, Equiv.apply_symm_apply])
      cases h : s (τ j) <;> cases h' : s i <;>
        simp [dirFlip, h, dirVec, hi, hj]
  · show _ = (dirVec (dirFlip s (Sum.inr (τ j))) : Fin d → ZMod (L ^ N)) i
    by_cases hi : i = τ j
    · subst hi
      cases h : s (τ j) <;>
        simp [dirFlip, h, dirVec]
    · have hj : τ.symm i ≠ j := fun h => hi (by rw [← h, Equiv.apply_symm_apply])
      cases h : s (τ j) <;> cases h' : s i <;>
        simp [dirFlip, h, dirVec, hi, hj]

theorem nnW_sgnPerm (β : ℝ) (τ : Equiv.Perm (Fin d)) (s : Fin d → Bool) (x y : Lam d L N) :
    nnW d L N β (sgnPerm d L N τ s x) (sgnPerm d L N τ s y) = nnW d L N β x y :=
  nnW_aut β _ (sgnPerm_injective τ s) (dirSgnPerm τ s) (sgnPerm_dirVec τ s) x y

end

end Ward

namespace Spin2

noncomputable section

set_option linter.unusedSectionVars false

open Finset Grassmann Loc

variable {L N : ℕ} [NeZero L]

variable (L N) in
/-- **Two-point connection probability** `P_β[y ↔ x]` on `Λ_N`. -/
def PconnXY (β : ℝ) (y x : Lam 2 L N) : ℝ :=
  H02.arborealProb (Ward.nnW 2 L N β) (Ward.nnW_symm β) (fun F => F.Reachable y x)

theorem PconnXY_comm (β : ℝ) (y x : Lam 2 L N) : PconnXY L N β y x = PconnXY L N β x y := by
  unfold PconnXY
  have : (fun F : SimpleGraph (Lam 2 L N) => F.Reachable y x) = fun F => F.Reachable x y :=
    funext fun F => propext ⟨fun h => h.symm, fun h => h.symm⟩
  rw [this]

/-- Translation invariance: `P_β[y ↔ x] = P_β[0 ↔ x - y]`. -/
theorem PconnXY_eq (β : ℝ) (y x : Lam 2 L N) : PconnXY L N β y x = Pconn L N β (x - y) := by
  unfold PconnXY Pconn
  rw [H02.arborealProb_reachable_equiv _ _ (Equiv.addRight (-y))
    (fun i j => Ward.nnW_translate β (-y) i j) y x]
  simp [sub_eq_add_neg]

/-- **Point-group invariance** (signed permutations of the coordinates). -/
theorem Pconn_sgnPerm (β : ℝ) (τ : Equiv.Perm (Fin 2)) (s : Fin 2 → Bool) (x : Lam 2 L N) :
    Pconn L N β (Ward.sgnPerm 2 L N τ s x) = Pconn L N β x := by
  let φ := Ward.sgnPerm 2 L N τ s
  have hb : Function.Bijective φ :=
    (Finite.injective_iff_bijective).1 (Ward.sgnPerm_injective τ s)
  unfold Pconn
  rw [H02.arborealProb_reachable_equiv _ _ (Equiv.ofBijective φ hb)
    (fun i j => Ward.nnW_sgnPerm β τ s i j) 0 x]
  simp [φ]

theorem sgnPerm_neg (x : Lam 2 L N) : Ward.sgnPerm 2 L N 1 (fun _ => true) x = -x := rfl

/-- `P_β[0 ↔ -x] = P_β[0 ↔ x]`. -/
theorem Pconn_neg (β : ℝ) (x : Lam 2 L N) : Pconn L N β (-x) = Pconn L N β x := by
  rw [← sgnPerm_neg, Pconn_sgnPerm]

/-- The coordinate swap `(x₀, x₁) ↦ (x₁, x₀)`. -/
abbrev coordSwap (x : Lam 2 L N) : Lam 2 L N := Ward.sgnPerm 2 L N (Equiv.swap 0 1) (fun _ => false) x

theorem Pconn_swap (β : ℝ) (x : Lam 2 L N) : Pconn L N β (coordSwap x) = Pconn L N β x :=
  Pconn_sgnPerm β _ _ x

/-- The reflection `x_k ↦ -x_k` of the single coordinate `k`. -/
abbrev coordRefl (k : Fin 2) (x : Lam 2 L N) : Lam 2 L N :=
  Ward.sgnPerm 2 L N 1 (fun i => decide (i = k)) x

theorem Pconn_refl (β : ℝ) (k : Fin 2) (x : Lam 2 L N) :
    Pconn L N β (coordRefl k x) = Pconn L N β x :=
  Pconn_sgnPerm β _ _ x

theorem continuous_forestWeight_nnW (F : SimpleGraph (Lam 2 L N)) :
    Continuous fun β : ℝ => H02.forestWeight (Ward.nnW 2 L N β) (Ward.nnW_symm β) F := by
  unfold H02.forestWeight
  refine continuous_finsetProd _ fun e _ => ?_
  induction e using Sym2.ind with
  | h i j => simp only [Sym2.lift_mk, Ward.nnW]; fun_prop

/-- **Continuity** of `β ↦ P_β[0 ↔ x]` on `β ≥ 0` (ratio of polynomials, `Z_β > 0`). -/
theorem Pconn_continuousOn (x : Lam 2 L N) :
    ContinuousOn (fun β => Pconn L N β x) (Set.Ici 0) := by
  unfold Pconn H02.arborealProb H02.Zforest
  refine ContinuousOn.div (Continuous.continuousOn ?_) (Continuous.continuousOn ?_) fun β hβ => ?_
  · exact continuous_finsetSum _ fun F _ => continuous_forestWeight_nnW F
  · exact continuous_finsetSum _ fun F _ => continuous_forestWeight_nnW F
  · exact (H02.Zforest_pos _ (Ward.nnW_nonneg (Set.mem_Ici.1 hβ))).ne'

end

end Spin2
