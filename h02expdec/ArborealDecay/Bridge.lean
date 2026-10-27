module

public import ArborealDecay.Frozen.ForestProb
public import ArborealDecay.Frozen.TwoPoint
public import ArborealDecay.Frozen.ForestPolynomial
public import ArborealDecay.Frozen.EdgeWeightsMap
public import ArborealDecay.Frozen.IsNN
public import ArborealDecay.Frozen.SupDist
public import ArborealDecay.Frozen.SupNorm
public import ArborealDecay.Frozen.IsTorusNN
public import ArborealDecay.Frozen.TorusSupDist
public import ArborealDecay.H02
public import ArborealDecay.Lattice
public import ArborealDecay.ForestPoly
public import ArborealDecay.Surgery

/-!
# Carrier bridge

Identifies the frozen source-facing definitions (`ArborealDecay.Frozen.*`) with the
implementation-level definitions of the provider libraries (`H02`, `ForestPoly`,
`Surgery`, `Lattice`). Used by the provider modules in `ArborealDecay/Provider/`.
-/

@[expose] public section

namespace ArborealDecay.Bridge

open ArborealDecay

variable {V : Type*} [Fintype V]

theorem sum_filter_gen {α : Type*} (i1 i2 : Fintype α) (p q : α → Prop)
    (dp : DecidablePred p) (dq : DecidablePred q) (hpq : ∀ a, p a ↔ q a)
    (f g : α → ℝ) (h : ∀ a, p a → f a = g a) :
    @Finset.sum _ _ _ (@Finset.filter α p dp (@Finset.univ α i1)) f =
      @Finset.sum _ _ _ (@Finset.filter α q dq (@Finset.univ α i2)) g := by
  refine Finset.sum_congr (Finset.ext fun a => ?_) fun a ha => h a ((hpq a).2 (by simpa using ha))
  simp [hpq a]

theorem forestWeight_eq [DecidableEq V] (W : EdgeWeights V) (F : SimpleGraph V) :
    forestWeight W F = H02.forestWeight W.w W.symm F := by
  unfold forestWeight H02.forestWeight
  exact Finset.prod_congr (by ext; simp) fun _ _ => rfl

theorem partitionFunction_eq [DecidableEq V] (W : EdgeWeights V) :
    partitionFunction W = H02.Zforest W.w W.symm := by
  unfold partitionFunction H02.Zforest
  exact sum_filter_gen _ _ _ _ _ _ (fun _ => Iff.rfl) _ _ fun F _ => forestWeight_eq W F

theorem forestProb_eq [DecidableEq V] (W : EdgeWeights V) (P : SimpleGraph V → Prop) :
    forestProb W P = H02.arborealProb W.w W.symm P := by
  unfold forestProb H02.arborealProb
  rw [partitionFunction_eq]
  exact congrArg (· / _) (sum_filter_gen _ _ _ _ _ _ (fun _ => Iff.rfl) _ _ fun F _ => forestWeight_eq W F)

theorem twoPoint_eq [DecidableEq V] (W : EdgeWeights V) (x y : V) :
    twoPoint W x y = H02.arborealProb W.w W.symm fun F => F.Reachable x y :=
  forestProb_eq W _

open Classical in
theorem forestPolynomial_eq (W : EdgeWeights V) :
    forestPolynomial W = ArborealDecay.ForestPoly.forestPolynomial W.w W.symm := by
  unfold forestPolynomial ArborealDecay.ForestPoly.forestPolynomial
  refine Finset.sum_congr rfl fun F _ => ?_
  rfl

theorem map_w_eq {V' : Type*} [DecidableEq V']
    (W : EdgeWeights V) (f : V → V') :
    (W.map f).w = ArborealDecay.Surgery.mapW W.w f := by
  funext a b
  unfold EdgeWeights.map ArborealDecay.Surgery.mapW
  by_cases h : a = b
  · simp only [h, ite_true]
  · simp only [h, ite_false]
    exact Finset.sum_congr (by ext; simp) fun _ _ => Finset.sum_congr (by ext; simp) fun _ _ => rfl

theorem isNN_eq : IsNN = ArborealDecay.Lattice.IsNN := rfl
theorem supDist_eq : supDist = ArborealDecay.Lattice.supDist := rfl
theorem supNorm_eq : supNorm = ArborealDecay.Lattice.supNorm := rfl
theorem isTorusNN_eq : IsTorusNN = ArborealDecay.Lattice.IsTorusNN := rfl
theorem torusSupDist_eq : torusSupDist = ArborealDecay.Lattice.torusSupDist := rfl

end ArborealDecay.Bridge

end
