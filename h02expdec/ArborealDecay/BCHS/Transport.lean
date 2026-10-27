module

public import ArborealDecay.Super.DimRedSymm
public import ArborealDecay.ForestPoly.Gaussian

/-!
# Relabelling generators: the two-flavour `ℍ^{2|4}` algebra and the fermionic Gaussian

* `relabel e : Gr O ≃ₐ Gr O'` for an index equivalence `e : O ≃ O'` (`θ_o ↦ θ_{e o}`); it
  preserves bodies and intertwines `∂_{θ_o}` with `∂_{θ_{e o}}`.
* `B Λ = SG (Λ ⊕ Λ) Empty`: both odd pairs of every vertex are integrated. `toA : B Λ ≃ₐ H24.A Λ`
  sends the flavour-`inl` pair to the parameter pair `(ξ¹, η¹)` and the flavour-`inr` pair to the
  integrated pair `(ξ², η²)` of `H24.A Λ`. Since all pair operators `∂_η∂_ξ` commute,
  `body (B1 (berezin (toA y))) = body (berezin y)` (`body_B1_berezin_toA`).
* `body_berezin_exp_quad`: the fermionic Gaussian `B(exp(∑ M_ij ξ_i η_j)) = det M` (BCHS (2.74)),
  transported from `ForestPoly.gaussian_pBer`.
-/

@[expose] public section

namespace ArborealDecay.BCHS

noncomputable section

open ArborealDecay.Super CliffordAlgebra Grassmann

set_option linter.unusedSectionVars false

/-! ### Relabelling -/

section Relabel

variable {O O' : Type*}

/-- The algebra map `θ_o ↦ θ_{e o}` (as a map). -/
def relabelHom (e : O ≃ O') : Gr O →ₐ[ℝ] Gr O' :=
  ExteriorAlgebra.map (LinearMap.funLeft ℝ ℝ e.symm)

theorem relabelHom_ι (e : O ≃ O') (v : O → ℝ) :
    relabelHom e (ExteriorAlgebra.ι ℝ v) = ExteriorAlgebra.ι ℝ (v ∘ e.symm) :=
  ExteriorAlgebra.map_apply_ι _ _

theorem relabelHom_comp (e : O ≃ O') :
    (relabelHom e.symm).comp (relabelHom e) = AlgHom.id ℝ (Gr O) := by
  rw [relabelHom, relabelHom, ExteriorAlgebra.map_comp_map]
  have : (LinearMap.funLeft ℝ ℝ e.symm.symm).comp (LinearMap.funLeft ℝ ℝ e.symm) =
      LinearMap.id := by
    ext v o; simp [LinearMap.funLeft]
  rw [this, ExteriorAlgebra.map_id]

/-- The relabelling algebra equivalence. -/
def relabel (e : O ≃ O') : Gr O ≃ₐ[ℝ] Gr O' :=
  AlgEquiv.ofAlgHom (relabelHom e) (relabelHom e.symm)
    (by simpa using relabelHom_comp e.symm) (relabelHom_comp e)

theorem relabel_apply (e : O ≃ O') (x : Gr O) : relabel e x = relabelHom e x := rfl

theorem relabel_symm_apply (e : O ≃ O') (x : Gr O') :
    (relabel e).symm x = relabelHom e.symm x := rfl

theorem relabel_ι (e : O ≃ O') (v : O → ℝ) :
    relabel e (ExteriorAlgebra.ι ℝ v) = ExteriorAlgebra.ι ℝ (v ∘ e.symm) :=
  relabelHom_ι e v

theorem relabel_gen [DecidableEq O] [DecidableEq O'] (e : O ≃ O') (o : O) :
    relabel e (gen o) = gen (e o) := by
  rw [gen, relabel_ι, gen]
  congr 1; funext o'
  simp only [Function.comp_apply, Pi.single_apply, Equiv.symm_apply_eq]

theorem body_relabel (e : O ≃ O') (x : Gr O) : body (relabel e x) = body x := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι v =>
    change body (relabel e (ExteriorAlgebra.ι ℝ v)) = body (ExteriorAlgebra.ι ℝ v)
    rw [relabel_ι, body_ι, body_ι]
  | mul a b ha hb => rw [map_mul, map_mul, map_mul, ha, hb]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

theorem inv'_relabel (e : O ≃ O') (x : Gr O) : inv' (relabel e x) = relabel e (inv' x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι v =>
    change inv' (relabel e (ExteriorAlgebra.ι ℝ v)) = relabel e (inv' (ExteriorAlgebra.ι ℝ v))
    rw [relabel_ι, inv'_ι, inv'_ι, map_neg, relabel_ι]
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb, map_mul, map_mul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

/-- `∂_{θ_{e o}} ∘ relabel = relabel ∘ ∂_{θ_o}`. -/
theorem dgen_relabel (e : O ≃ O') (o : O) (x : Gr O) :
    dgen (e o) (relabel e x) = relabel e (dgen o x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι v =>
    change dgen (e o) (relabel e (ExteriorAlgebra.ι ℝ v)) =
      relabel e (dgen o (ExteriorAlgebra.ι ℝ v))
    rw [relabel_ι]
    simp [dgen, ExteriorAlgebra.ι, contractLeft_ι]
  | mul a b ha hb =>
    rw [map_mul, dgen_mul, ha, hb, dgen_mul, map_add, map_mul, map_mul, inv'_relabel]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

end Relabel

/-! ### Pair operators and products over lists -/

section Pairs

variable {O O' : Type*}

/-- A pair operator `∂_{θ_a} ∂_{θ_b}`. -/
def pop (a b : O) : Gr O →ₗ[ℝ] Gr O := dgen a ∘ₗ dgen b

theorem pop_comm (a b c d : O) : pop a b ∘ₗ pop c d = pop c d ∘ₗ pop a b := by
  refine LinearMap.ext fun x => ?_
  simp only [pop, LinearMap.coe_comp, Function.comp_apply]
  rw [dgen_comm b c, map_neg, dgen_comm a c, neg_neg, dgen_comm b d, map_neg, map_neg,
    dgen_comm a d, map_neg, neg_neg]

theorem relabel_pop (e : O ≃ O') (a b : O) (x : Gr O) :
    relabel e (pop a b x) = pop (e a) (e b) (relabel e x) := by
  simp only [pop, LinearMap.coe_comp, Function.comp_apply, dgen_relabel]

variable {ι : Type*}

/-- `∏_{i ∈ l} f_i`, the head of `l` applied last. -/
def lcomp (f : ι → Gr O →ₗ[ℝ] Gr O) (l : List ι) : Gr O →ₗ[ℝ] Gr O :=
  l.foldr (fun i L => f i ∘ₗ L) LinearMap.id

theorem lcomp_cons (f : ι → Gr O →ₗ[ℝ] Gr O) (i : ι) (l : List ι) :
    lcomp f (i :: l) = f i ∘ₗ lcomp f l := rfl

theorem lcomp_append (f : ι → Gr O →ₗ[ℝ] Gr O) (l l' : List ι) :
    lcomp f (l ++ l') = lcomp f l ∘ₗ lcomp f l' := by
  induction l with
  | nil => rfl
  | cons i l ih => rw [List.cons_append, lcomp_cons, lcomp_cons, ih, LinearMap.comp_assoc]

theorem lcomp_perm {f : ι → Gr O →ₗ[ℝ] Gr O} (hf : ∀ i j, f i ∘ₗ f j = f j ∘ₗ f i)
    {l l' : List ι} (h : l.Perm l') : lcomp f l = lcomp f l' := by
  induction h with
  | nil => rfl
  | cons i _ ih => rw [lcomp_cons, lcomp_cons, ih]
  | swap i j l =>
    rw [lcomp_cons, lcomp_cons, lcomp_cons, lcomp_cons, ← LinearMap.comp_assoc,
      ← LinearMap.comp_assoc, hf]
  | trans _ _ ih1 ih2 => rw [ih1, ih2]

theorem lcomp_map {κ : Type*} (f : ι → Gr O →ₗ[ℝ] Gr O) (g : κ → ι) (l : List κ) :
    lcomp f (l.map g) = lcomp (f ∘ g) l := by
  induction l with
  | nil => rfl
  | cons i l ih => rw [List.map_cons, lcomp_cons, lcomp_cons, ih]; rfl

end Pairs

/-! ### The two-flavour `ℍ^{2|4}` algebra -/

section H24

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- The full two-flavour ℍ^{2|4} algebra: pairs `m : Λ ⊕ Λ`, `inl i` = flavour 1 (↔ ξ¹,η¹
parameters of `H24.A`), `inr i` = flavour 2 (↔ integrated ξ,η of `H24.A`). -/
abbrev B (Λ : Type*) := SG (Λ ⊕ Λ) Empty

/-- The index map of `toA`. -/
def eAfun : ((Λ ⊕ Λ) ⊕ (Λ ⊕ Λ)) ⊕ Empty → (Λ ⊕ Λ) ⊕ (Λ ⊕ Λ)
  | .inl (.inl (.inl i)) => .inr (.inl i)
  | .inl (.inr (.inl i)) => .inr (.inr i)
  | .inl (.inl (.inr i)) => .inl (.inl i)
  | .inl (.inr (.inr i)) => .inl (.inr i)

/-- The inverse index map of `toA`. -/
def eAinv : (Λ ⊕ Λ) ⊕ (Λ ⊕ Λ) → ((Λ ⊕ Λ) ⊕ (Λ ⊕ Λ)) ⊕ Empty
  | .inr (.inl i) => .inl (.inl (.inl i))
  | .inr (.inr i) => .inl (.inr (.inl i))
  | .inl (.inl i) => .inl (.inl (.inr i))
  | .inl (.inr i) => .inl (.inr (.inr i))

/-- The index equivalence of `toA`. -/
def eA : ((Λ ⊕ Λ) ⊕ (Λ ⊕ Λ)) ⊕ Empty ≃ (Λ ⊕ Λ) ⊕ (Λ ⊕ Λ) where
  toFun := eAfun
  invFun := eAinv
  left_inv o := by
    rcases o with ((i | i) | (i | i)) | e
    all_goals first | rfl | exact e.elim
  right_inv o := by rcases o with (i | i) | (i | i) <;> rfl

/-- The identification of the two-flavour algebra with `H24.A Λ`. -/
def toA : B Λ ≃ₐ[ℝ] H24.A Λ := relabel eA

@[simp] theorem toA_ξ_inl (i : Λ) : toA (ξ (.inl i) : B Λ) = H24.ξ1 i := relabel_gen eA _

@[simp] theorem toA_η_inl (i : Λ) : toA (η (.inl i) : B Λ) = H24.η1 i := relabel_gen eA _

@[simp] theorem toA_ξ_inr (i : Λ) : toA (ξ (.inr i) : B Λ) = (ξ i : H24.A Λ) :=
  relabel_gen eA _

@[simp] theorem toA_η_inr (i : Λ) : toA (η (.inr i) : B Λ) = (η i : H24.A Λ) :=
  relabel_gen eA _

theorem body_toA (x : B Λ) : body (toA x) = body x := body_relabel eA x

theorem body_toA_symm (x : H24.A Λ) : body (toA.symm x) = body x := by
  conv_rhs => rw [← toA.apply_symm_apply x]
  exact (body_toA _).symm

/-- The pair operators of `H24.A Λ` indexed by the flavoured pairs. -/
def Gop : Λ ⊕ Λ → H24.A Λ →ₗ[ℝ] H24.A Λ
  | .inl i => H24.bpar i
  | .inr i => bpair i

theorem Gop_eq (m : Λ ⊕ Λ) :
    Gop m = pop (eA (.inl (.inr m) : ((Λ ⊕ Λ) ⊕ (Λ ⊕ Λ)) ⊕ Empty)) (eA (.inl (.inl m))) := by
  rcases m with i | i <;> rfl

theorem Gop_comm (m m' : Λ ⊕ Λ) : Gop m ∘ₗ Gop m' = Gop m' ∘ₗ Gop m := by
  rw [Gop_eq, Gop_eq, pop_comm]

theorem toA_bpair (m : Λ ⊕ Λ) (x : B Λ) : toA (bpair m x) = Gop m (toA x) := by
  rw [Gop_eq, toA, ← relabel_pop]; rfl

theorem toA_berezinL (l : List (Λ ⊕ Λ)) (x : B Λ) :
    toA (berezinL l x) = lcomp Gop l (toA x) := by
  induction l with
  | nil => rfl
  | cons m l ih =>
    rw [berezinL_cons, toA_bpair, ih]; rfl

theorem body_B1_berezin_toA (y : B Λ) :
    body (H24.B1 (Finset.univ : Finset Λ).toList (berezin (toA y))) = body (berezin y) := by
  set l := (Finset.univ : Finset Λ).toList
  have hB1 : (H24.B1 l : H24.A Λ →ₗ[ℝ] H24.A Λ) = lcomp Gop (l.map Sum.inl) := by
    rw [H24.B1_eq_lprod, lcomp_map]; rfl
  have hB : (berezin : H24.A Λ →ₗ[ℝ] H24.A Λ) = lcomp Gop (l.map Sum.inr) := by
    rw [berezin, lcomp_map]; rfl
  have hperm : (l.map Sum.inl ++ l.map Sum.inr).Perm (Finset.univ : Finset (Λ ⊕ Λ)).toList := by
    refine List.perm_of_nodup_nodup_toFinset_eq ?_ (Finset.nodup_toList _) ?_
    · refine List.nodup_append.2 ⟨(Finset.nodup_toList _).map Sum.inl_injective,
        (Finset.nodup_toList _).map Sum.inr_injective, ?_⟩
      intro a ha b hb hab
      simp only [List.mem_map] at ha hb
      obtain ⟨_, _, rfl⟩ := ha
      obtain ⟨_, _, rfl⟩ := hb
      exact Sum.inl_ne_inr hab
    · ext m; rcases m with i | i <;> simp [l]
  have e1 : H24.B1 l (berezin (toA y)) = toA (berezin y) := by
    calc H24.B1 l (berezin (toA y))
        = (lcomp Gop (l.map Sum.inl) ∘ₗ lcomp Gop (l.map Sum.inr)) (toA y) := by
          rw [← hB1, ← hB]; rfl
      _ = lcomp Gop (Finset.univ : Finset (Λ ⊕ Λ)).toList (toA y) := by
          rw [← lcomp_append, lcomp_perm Gop_comm hperm]
      _ = toA (berezin y) := (toA_berezinL _ _).symm
  rw [e1, body_toA]

end H24

/-! ### The fermionic Gaussian -/

section Gauss

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- The relabelling `H02.Grassmann N = Gr (N ⊕ N) ≃ SG N Empty`. -/
def eG (N : Type*) : N ⊕ N ≃ (N ⊕ N) ⊕ Empty := (Equiv.sumEmpty _ _).symm

theorem relabel_H02ξ (i : N) : relabel (eG N) (H02.ξ i) = (ξ i : SG N Empty) :=
  relabel_gen (eG N) (.inl i)

theorem relabel_H02η (i : N) : relabel (eG N) (H02.η i) = (η i : SG N Empty) :=
  relabel_gen (eG N) (.inr i)

theorem relabel_pBer (l : List N) (x : H02.Grassmann N) :
    relabel (eG N) (ForestPoly.pBer l x) = lcomp bpair l.reverse (relabel (eG N) x) := by
  induction l generalizing x with
  | nil => rfl
  | cons i l ih =>
    change relabel (eG N) (ForestPoly.pBer l (ForestPoly.pStep i x)) = _
    rw [ih, List.reverse_cons, lcomp_append]
    change _ = lcomp bpair l.reverse (bpair i (lcomp bpair [] _))
    congr 1
    have h1 : eG N (.inr i) = .inl (.inr i) := rfl
    have h2 : eG N (.inl i) = .inl (.inl i) := rfl
    have h3 := relabel_pop (eG N) (Sum.inr i) (Sum.inl i) x
    rw [h1, h2] at h3
    exact h3

/-- **Fermionic Gaussian** (BCHS (2.74)) in `SG N Empty`. -/
theorem body_berezin_exp_quad (M : Matrix N N ℝ) :
    body (berezin (IsNilpotent.exp (∑ i, ∑ j, M i j • (ξ i * η j)) : SG N Empty)) = M.det := by
  have hQ := ForestPoly.isNilpotent_quad M
  have hX : relabel (eG N) (H02.cv (IsNilpotent.exp (∑ i, ∑ j, M i j • H02.pc i j))) =
      IsNilpotent.exp (∑ i, ∑ j, M i j • (ξ i * η j) : SG N Empty) := by
    rw [IsNilpotent.map_exp hQ, IsNilpotent.map_exp (hQ.map H02.cv)]
    congr 1
    simp only [map_sum, map_smul, map_mul, H02.coe_pc, relabel_H02ξ, relabel_H02η]
  have hperm : ((ForestPoly.lst N).reverse).Perm (Finset.univ : Finset N).toList :=
    (List.reverse_perm _).trans (List.perm_of_nodup_nodup_toFinset_eq ForestPoly.lst_nodup
      (Finset.nodup_toList _) (by rw [ForestPoly.lst_toFinset, Finset.toList_toFinset]))
  have hcomm : ∀ i j : N, (bpair i : SG N Empty →ₗ[ℝ] SG N Empty) ∘ₗ bpair j =
      bpair j ∘ₗ bpair i := fun i j => pop_comm _ _ _ _
  rw [← hX, berezin, ← ForestPoly.gaussian_pBer M]
  change body (lcomp bpair _ _) = _
  rw [← lcomp_perm hcomm hperm, ← relabel_pBer, body_relabel]
  rfl

end Gauss

end

end ArborealDecay.BCHS

end
