import Obs2.Map.ExactStep

/-!
# Pair linearity, part 1: relative triples (Case (2))

`PlRel F G H` (`F, G, H : OE .two Λ`): equal `∅` and `σ_b` parts, and
`F_a − G_a = H_a`, `F_{ab} − G_{ab} = H_{ab}`.

In Case (2) the product is `(FG)_∅ = F_∅G_∅`, `(FG)_• = F_∅G_• + F_•G_∅` (`• ∈ {a, b}`),
`(FG)_{ab} = F_∅G_{ab} + F_aG_b + F_bG_a + F_{ab}G_∅`; at fixed `(∅, b)` parts this is linear
in the `(a, ab)` parts. Hence the triples form a **subalgebra** `plRelSub` of `(OE .two Λ)³`
(`pl_rel_add`, `pl_rel_mul`, `pl_rel_one`, `pl_rel_algebraMap`, `pl_rel_emb`), closed under
`ℂ`-scalars, finite sums and products, powers, `oexp` (`pl_rel_oexp`; all three nilpotent or none,
since nilpotency is decided by the common bulk part), `expU`, and therefore under the integrand
maps `IbO`, `bpowO`, `KextO`, `gZO` (`pl_rel_IbO`, `pl_rel_bpowO`, `pl_rel_KextO`, `pl_rel_gZO`).
No per-map commutation lemmas are needed: all four are built from `+`, `·`, `oexp`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD

section Alg

variable {Λ : Type*} [DecidableEq Λ]

/-- **Relative triples**: equal `∅`/`b` parts, `a` and `ab` parts `F − G = H`. -/
structure PlRel (F G H : OE .two Λ) : Prop where
  e1 : (G : SA .two Λ).e = (F : SA .two Λ).e
  e2 : (H : SA .two Λ).e = (F : SA .two Λ).e
  b1 : (G : SA .two Λ).b = (F : SA .two Λ).b
  b2 : (H : SA .two Λ).b = (F : SA .two Λ).b
  a : (F : SA .two Λ).a - (G : SA .two Λ).a = (H : SA .two Λ).a
  ab : (F : SA .two Λ).ab - (G : SA .two Λ).ab = (H : SA .two Λ).ab

theorem pl_rel_add {F G H F' G' H' : OE .two Λ} (h : PlRel F G H) (h' : PlRel F' G' H') :
    PlRel (F + F') (G + G') (H + H') where
  e1 := by simp only [Subalgebra.coe_add, add_e, h.e1, h'.e1]
  e2 := by simp only [Subalgebra.coe_add, add_e, h.e2, h'.e2]
  b1 := by simp only [Subalgebra.coe_add, add_b, h.b1, h'.b1]
  b2 := by simp only [Subalgebra.coe_add, add_b, h.b2, h'.b2]
  a := by simp only [Subalgebra.coe_add, add_a, ← h.a, ← h'.a]; abel
  ab := by simp only [Subalgebra.coe_add, add_ab, ← h.ab, ← h'.ab]; abel

theorem pl_rel_mul {F G H F' G' H' : OE .two Λ} (h : PlRel F G H) (h' : PlRel F' G' H') :
    PlRel (F * F') (G * G') (H * H') where
  e1 := by simp only [OE.mul_e, h.e1, h'.e1]
  e2 := by simp only [OE.mul_e, h.e2, h'.e2]
  b1 := by simp only [OE.mul_b, h.e1, h'.e1, h.b1, h'.b1]
  b2 := by simp only [OE.mul_b, h.e2, h'.e2, h.b2, h'.b2]
  a := by simp only [OE.mul_a, h.e1, h'.e1, h.e2, h'.e2, ← h.a, ← h'.a]; noncomm_ring
  ab := by
    simp only [OE.mul_ab, Case.s_two, one_smul, h.e1, h'.e1, h.e2, h'.e2, h.b1, h'.b1, h.b2,
      h'.b2, ← h.a, ← h'.a, ← h.ab, ← h'.ab]
    noncomm_ring

theorem pl_rel_smul (r : ℂ) {F G H : OE .two Λ} (h : PlRel F G H) :
    PlRel (r • F) (r • G) (r • H) where
  e1 := by simp only [Subalgebra.coe_smul, smul_e, h.e1]
  e2 := by simp only [Subalgebra.coe_smul, smul_e, h.e2]
  b1 := by simp only [Subalgebra.coe_smul, smul_b, h.b1]
  b2 := by simp only [Subalgebra.coe_smul, smul_b, h.b2]
  a := by simp only [Subalgebra.coe_smul, smul_a, ← h.a, smul_sub]
  ab := by simp only [Subalgebra.coe_smul, smul_ab, ← h.ab, smul_sub]

/-- Diagonal triples with vanishing `a`, `ab` parts (e.g. bulk elements, constants). -/
theorem pl_rel_diag {F : OE .two Λ} (ha : (F : SA .two Λ).a = 0) (hab : (F : SA .two Λ).ab = 0) :
    PlRel F F F where
  e1 := rfl
  e2 := rfl
  b1 := rfl
  b2 := rfl
  a := by rw [ha, sub_zero]
  ab := by rw [hab, sub_zero]

theorem pl_rel_one : PlRel (1 : OE .two Λ) 1 1 := pl_rel_diag (one_a) (one_ab)

theorem pl_rel_zero : PlRel (0 : OE .two Λ) 0 0 := pl_rel_diag (zero_a) (zero_ab)

theorem pl_rel_algebraMap (r : ℂ) :
    PlRel (algebraMap ℂ (OE .two Λ) r) (algebraMap ℂ _ r) (algebraMap ℂ _ r) :=
  pl_rel_diag (by simp [Subalgebra.coe_algebraMap]) (by simp [Subalgebra.coe_algebraMap])

theorem pl_rel_emb (x : Step.EvR Λ) : PlRel (emb x : OE .two Λ) (emb x) (emb x) :=
  pl_rel_diag (by simp) (by simp)

theorem pl_rel_neg {F G H : OE .two Λ} (h : PlRel F G H) : PlRel (-F) (-G) (-H) := by
  simpa using pl_rel_smul (-1) h

/-- **The relative triples form a subalgebra of `(OE .two Λ)³`.** -/
def plRelSub : Subalgebra ℂ (OE .two Λ × OE .two Λ × OE .two Λ) where
  carrier := {t | PlRel t.1 t.2.1 t.2.2}
  mul_mem' h h' := pl_rel_mul h h'
  add_mem' h h' := pl_rel_add h h'
  algebraMap_mem' r := pl_rel_algebraMap r

theorem pl_rel_pow {F G H : OE .two Λ} (h : PlRel F G H) (n : ℕ) :
    PlRel (F ^ n) (G ^ n) (H ^ n) := by
  induction n with
  | zero => simpa using pl_rel_one
  | succ n ih => simpa [pow_succ] using pl_rel_mul ih h

theorem pl_rel_prod {ι : Type*} (s : Finset ι) {f g h : ι → OE .two Λ}
    (H : ∀ i ∈ s, PlRel (f i) (g i) (h i)) :
    PlRel (∏ i ∈ s, f i) (∏ i ∈ s, g i) (∏ i ∈ s, h i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pl_rel_one
  | insert i s hi ih =>
    rw [prod_insert hi, prod_insert hi, prod_insert hi]
    exact pl_rel_mul (H i (mem_insert_self _ _)) (ih fun k hk => H k (mem_insert_of_mem hk))

theorem pl_rel_sum {ι : Type*} (s : Finset ι) {f g h : ι → OE .two Λ}
    (H : ∀ i ∈ s, PlRel (f i) (g i) (h i)) :
    PlRel (∑ i ∈ s, f i) (∑ i ∈ s, g i) (∑ i ∈ s, h i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pl_rel_zero
  | insert i s hi ih =>
    rw [sum_insert hi, sum_insert hi, sum_insert hi]
    exact pl_rel_add (H i (mem_insert_self _ _)) (ih fun k hk => H k (mem_insert_of_mem hk))

variable [Fintype Λ]

theorem pl_bulk_eq {F G : OE .two Λ} (h : (G : SA .two Λ).e = (F : SA .two Λ).e) :
    bulk G = bulk F := Subtype.ext h

theorem pl_nil_iff {F G : OE .two Λ} (h : (G : SA .two Λ).e = (F : SA .two Λ).e) :
    IsNilpotent G ↔ IsNilpotent F := by
  constructor
  · intro hG; exact isNilpotent_of_bulk (pl_bulk_eq h ▸ hG.map bulk)
  · intro hF; exact isNilpotent_of_bulk ((pl_bulk_eq h).symm ▸ hF.map bulk)

/-- **`oexp` preserves relative triples.** -/
theorem pl_rel_oexp {F G H : OE .two Λ} (h : PlRel F G H) : PlRel (oexp F) (oexp G) (oexp H) := by
  by_cases hF : IsNilpotent F
  · obtain ⟨k₁, hk₁⟩ := hF
    obtain ⟨k₂, hk₂⟩ := (pl_nil_iff h.e1).2 ⟨k₁, hk₁⟩
    obtain ⟨k₃, hk₃⟩ := (pl_nil_iff h.e2).2 ⟨k₁, hk₁⟩
    have p1 : F ^ (k₁ + k₂ + k₃) = 0 := pow_eq_zero_of_le (by omega) hk₁
    have p2 : G ^ (k₁ + k₂ + k₃) = 0 := pow_eq_zero_of_le (by omega) hk₂
    have p3 : H ^ (k₁ + k₂ + k₃) = 0 := pow_eq_zero_of_le (by omega) hk₃
    rw [oexp, oexp, oexp, IsNilpotent.exp_eq_sum p1, IsNilpotent.exp_eq_sum p2,
      IsNilpotent.exp_eq_sum p3]
    refine pl_rel_sum _ fun i _ => ?_
    simp only [OE.qsmul_eq]
    exact pl_rel_smul _ (pl_rel_pow h i)
  · have hG : ¬ IsNilpotent G := fun h' => hF ((pl_nil_iff h.e1).1 h')
    have hH : ¬ IsNilpotent H := fun h' => hF ((pl_nil_iff h.e2).1 h')
    rw [oexp, oexp, oexp, nilExp_of_not hF, nilExp_of_not hG, nilExp_of_not hH]
    exact pl_rel_zero

end Alg

/-! ### The integrand -/

section Integrand

variable {d L N : ℕ} [NeZero L]

/-- Relative triples of families. -/
def PlRelF {ι : Type*} (F G H : ι → OE .two (Lam d L N)) : Prop := ∀ i, PlRel (F i) (G i) (H i)

theorem pl_rel_IbO {V₁ V₂ V₃ W₁ W₂ W₃ : OFam .two d L N} (hV : PlRelF V₁ V₂ V₃)
    (hW : PlRelF W₁ W₂ W₃) (b : Fin d → ℕ) :
    PlRel (IbO V₁ W₁ b) (IbO V₂ W₂ b) (IbO V₃ W₃ b) :=
  pl_rel_mul (pl_rel_oexp (pl_rel_neg (hV b))) (pl_rel_add pl_rel_one (hW b))

theorem pl_rel_bpowO (j : ℕ) {I₁ I₂ I₃ : OFam .two d L N} (hI : PlRelF I₁ I₂ I₃)
    (X : Finset (Lam d L N)) : PlRel (bpowO j I₁ X) (bpowO j I₂ X) (bpowO j I₃ X) :=
  pl_rel_prod _ fun b _ => hI b

theorem pl_rel_KextO (j : ℕ) {K₁ K₂ K₃ : OAct .two d L N} (hK : PlRelF K₁ K₂ K₃)
    (X : Finset (Lam d L N)) : PlRel (KextO j K₁ X) (KextO j K₂ X) (KextO j K₃ X) :=
  pl_rel_prod _ fun Y _ => hK Y

/-- **`Z_j = ∑_X I^{Λ∖X}K^X` preserves relative triples.** -/
theorem pl_rel_gZO (j : ℕ) {I₁ I₂ I₃ : OFam .two d L N} (hI : PlRelF I₁ I₂ I₃)
    {K₁ K₂ K₃ : OAct .two d L N} (hK : PlRelF K₁ K₂ K₃) :
    PlRel (gZO j I₁ K₁) (gZO j I₂ K₂) (gZO j I₃ K₃) :=
  pl_rel_sum _ fun X _ => pl_rel_mul (pl_rel_bpowO j hI _) (pl_rel_KextO j hK X)

end Integrand

end

end Obs2
