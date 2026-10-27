import Loc.Equivariance

/-!
# Generators of the lattice automorphisms

Translations `x ↦ x + t`, reflections `x_i ↦ -x_i` and transpositions of two coordinates are
affine lattice automorphisms compatible with the monomial basis (`AffAut`), and so are their
compositions.  Every automorphism of the torus considered here (translations composed with
signed permutations of the coordinates) is such a composition.
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD Matrix

variable {d L N : ℕ} [NeZero L]

/-- The list form of a local monomial with arbitrary offsets. -/
def specList (l : St d) (x : Lam d L N) : Alg d L N :=
  (l.map fun p => (p.1 : ℂ) • (psi (x + prj p.2.1) * psibar (x + prj p.2.2))).sum

theorem monoAt_eq_specList (M : Mono d) (x : Lam d L N) : monoAt M x = specList (stencil M) x := rfl

/-- Moving the offsets by an additive map compatible with `prj`. -/
theorem autAlg_specList (E : Lam d L N ≃ Lam d L N) (R : Lam d L N →+ Lam d L N)
    (hE : ∀ x, E x = R x + E 0) (Rz : Zd d →+ Zd d) (hRz : ∀ a, R (prj a) = prj (Rz a))
    (l : St d) (x : Lam d L N) :
    autAlg E (specList l x) = specList (l.map fun p => (p.1, Rz p.2.1, Rz p.2.2)) (E x) := by
  simp only [specList, List.map_map]
  rw [map_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun p _ => ?_
  simp only [Function.comp_apply, map_smul, map_mul, autAlg_psi, autAlg_psibar]
  have h1 : ∀ a, E (x + prj a) = E x + prj (Rz a) := by
    intro a; rw [hE, hE x, map_add, hRz]; abel
  rw [h1, h1]

/-! ### Composition -/

/-- The composition of two automorphisms. -/
def AffAut.comp (T₁ T₂ : AffAut d L N) : AffAut d L N where
  E := T₁.E.trans T₂.E
  R := T₂.R.comp T₁.R
  hE x := by
    simp only [Equiv.trans_apply, AddMonoidHom.comp_apply]
    rw [T₁.hE x, T₂.hE, map_add, T₂.hE (T₁.E 0)]
    abel
  Rz := T₂.Rz.comp T₁.Rz
  hRz a := by simp [T₁.hRz, T₂.hRz]
  hnorm a := (T₂.hnorm _).trans (T₁.hnorm _)
  A := T₂.A.comp T₁.A
  hA a := by
    show (fun i => ((T₂.Rz (T₁.Rz a)) i : ℝ)) = T₂.A (T₁.A _)
    rw [T₂.hA, T₁.hA]
  ρ := T₁.ρ.trans T₂.ρ
  sgn M := T₁.sgn M * T₂.sgn (T₁.ρ M)
  hmono M x := by
    have : autAlg (T₁.E.trans T₂.E) = (autAlg T₂.E).comp (autAlg T₁.E) := by
      rw [autAlg, autAlg, autAlg, ExteriorAlgebra.map_comp_map]
      congr 1
    rw [this, AlgHom.comp_apply, T₁.hmono, map_smul, T₂.hmono, smul_smul]
    rfl

/-! ### Translations -/

/-- The translation by `t`. -/
def AffAut.transl (t : Lam d L N) : AffAut d L N where
  E := Equiv.addRight t
  R := AddMonoidHom.id _
  hE x := by simp
  Rz := AddMonoidHom.id _
  hRz a := rfl
  hnorm a := le_rfl
  A := LinearMap.id
  hA a := rfl
  ρ := Equiv.refl _
  sgn _ := 1
  hmono M x := by
    rw [monoAt_eq_specList, autAlg_specList (Equiv.addRight t) (AddMonoidHom.id _) (by simp)
      (AddMonoidHom.id _) (fun _ => rfl)]
    simp [monoAt_eq_specList]

/-! ### Reflections -/

/-- `x ↦ x` with the `i`-th coordinate negated, on the torus. -/
def reflT (i : Fin d) : Lam d L N ≃+ Lam d L N where
  toFun x := (fun k => if k = i then -co x k else co x k : Fin d → ZMod (L ^ N))
  invFun x := (fun k => if k = i then -co x k else co x k : Fin d → ZMod (L ^ N))
  left_inv x := by funext k; by_cases h : k = i <;> simp [co, h]
  right_inv x := by funext k; by_cases h : k = i <;> simp [co, h]
  map_add' x y := by
    funext k
    show (if k = i then -co (x + y) k else co (x + y) k) =
      (if k = i then -co x k else co x k) + (if k = i then -co y k else co y k)
    by_cases h : k = i <;> simp [co_add, h]; ring

/-- The reflection on `ℤ^d`. -/
def reflZ (i : Fin d) : Zd d →+ Zd d where
  toFun a k := if k = i then -a k else a k
  map_zero' := by funext k; simp
  map_add' a b := by funext k; by_cases h : k = i <;> simp [h]; ring

/-- The reflection on `ℝ^d`. -/
def reflA (i : Fin d) : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) where
  toFun u k := if k = i then -u k else u k
  map_add' u v := by funext k; by_cases h : k = i <;> simp [h]; ring
  map_smul' c u := by funext k; by_cases h : k = i <;> simp [h]

theorem reflZ_ez (i k : Fin d) : reflZ i (ez k) = if k = i then -ez k else ez k := by
  funext m
  by_cases h : k = i
  · subst h; by_cases hm : m = k <;> simp [reflZ, ez, hm]
  · by_cases hm : m = i
    · subst hm; simp [reflZ, ez, h]
    · simp [reflZ, ez, hm, h]

/-- The number of derivatives in direction `i`. -/
def cnt (i : Fin d) : Mono d → ℕ
  | .c => 0
  | .a1 k => if k = i then 1 else 0
  | .b1 k => if k = i then 1 else 0
  | .a2 s => Sym2.lift ⟨fun k l => (if k = i then 1 else 0) + (if l = i then 1 else 0),
      fun _ _ => add_comm _ _⟩ s
  | .b2 s => Sym2.lift ⟨fun k l => (if k = i then 1 else 0) + (if l = i then 1 else 0),
      fun _ _ => add_comm _ _⟩ s
  | .m2 k l => (if k = i then 1 else 0) + (if l = i then 1 else 0)

theorem reflT_prj (i : Fin d) (a : Zd d) :
    (reflT (L := L) (N := N) i).toAddMonoidHom (prj a) = prj (reflZ i a) := by
  show (fun k => if k = i then -co (prj a : Lam d L N) k else co (prj a : Lam d L N) k) =
    (fun k => (((reflZ i a) k : ℤ) : ZMod (L ^ N)))
  funext k; by_cases h : k = i <;> simp [reflZ, h, co, prj]

macro "rcomp" : tactic => `(tactic| (
  simp [specList, stencil, tens, dpt, id1, lap1, fw, conv, sc, Dik, cnt, reflZ_ez, map_neg,
    map_add, *] <;> (try module)))

set_option maxHeartbeats 4000000 in
theorem specList_refl (i : Fin d) (M : Mono d) (y : Lam d L N) :
    specList ((stencil M).map fun p => (p.1, reflZ i p.2.1, reflZ i p.2.2)) y =
      ((-1 : ℂ) ^ cnt i M) • specList (stencil M) y := by
  cases M with
  | c => simp [specList, stencil, tens, id1, cnt]
  | a1 k => by_cases h : k = i <;> [subst h; skip] <;> rcomp
  | b1 k => by_cases h : k = i <;> [subst h; skip] <;> rcomp
  | a2 s =>
    induction s using Sym2.ind with
    | h k l =>
      rcases eq_or_ne k l with rfl | hkl
      · rw [show stencil (Mono.a2 s(k, k)) = tens (lap1 k) id1 by simp [stencil, Dsym, Dik]]
        by_cases h : k = i <;> [subst h; skip] <;> rcomp
      · rw [show cnt i (Mono.a2 s(k, l)) = cnt i (Mono.a2 s(min k l, max k l)) by
          rw [← sym2_minmax]]
        rw [sym2_minmax k l]
        have hab : min k l ≤ max k l := min_le_max
        have hne := minmax_ne hkl
        generalize min k l = a at *
        generalize max k l = b at *
        rw [show stencil (Mono.a2 s(a, b)) = tens (conv (dpt a) (dpt b)) id1 by
          simp [stencil, Dsym_mk hab, Dik, hne]]
        by_cases h1 : a = i <;> by_cases h2 : b = i <;> rcomp
  | b2 s =>
    induction s using Sym2.ind with
    | h k l =>
      rcases eq_or_ne k l with rfl | hkl
      · rw [show stencil (Mono.b2 s(k, k)) = tens id1 (lap1 k) by simp [stencil, Dsym, Dik]]
        by_cases h : k = i <;> [subst h; skip] <;> rcomp
      · rw [show cnt i (Mono.b2 s(k, l)) = cnt i (Mono.b2 s(min k l, max k l)) by
          rw [← sym2_minmax]]
        rw [sym2_minmax k l]
        have hab : min k l ≤ max k l := min_le_max
        have hne := minmax_ne hkl
        generalize min k l = a at *
        generalize max k l = b at *
        rw [show stencil (Mono.b2 s(a, b)) = tens id1 (conv (dpt a) (dpt b)) by
          simp [stencil, Dsym_mk hab, Dik, hne]]
        by_cases h1 : a = i <;> by_cases h2 : b = i <;> rcomp
  | m2 k l =>
    rcases eq_or_ne k l with rfl | hkl
    · by_cases h : k = i <;> [subst h; skip] <;> rcomp
    · rw [show stencil (Mono.m2 k l) = tens (dpt k) (dpt l) by simp [stencil, hkl]]
      by_cases h1 : k = i <;> by_cases h2 : l = i <;> rcomp

/-- The reflection `x_i ↦ -x_i` as an automorphism. -/
def AffAut.refl (i : Fin d) : AffAut d L N where
  E := (reflT i).toEquiv
  R := (reflT i).toAddMonoidHom
  hE x := by simp
  Rz := reflZ i
  hRz a := reflT_prj i a
  hnorm a := by
    rw [supNormZ_le_iff]; intro k
    refine le_trans ?_ (natAbs_le_supNormZ a k)
    by_cases h : k = i <;> simp [reflZ, h]
  A := reflA i
  hA a := by funext k; by_cases h : k = i <;> simp [reflZ, reflA, h]
  ρ := Equiv.refl _
  sgn M := (-1 : ℂ) ^ cnt i M
  hmono M x := by
    rw [monoAt_eq_specList, autAlg_specList _ (reflT i).toAddMonoidHom (by simp) (reflZ i)
      (reflT_prj i), specList_refl]
    rfl

/-! ### Permutations of the coordinates -/

/-- `x ↦ x ∘ σ⁻¹` on the torus (so that `e_m ↦ e_{σ m}`). -/
def permT (σ : Equiv.Perm (Fin d)) : Lam d L N ≃+ Lam d L N where
  toFun x := (fun k => co x (σ.symm k) : Fin d → ZMod (L ^ N))
  invFun x := (fun k => co x (σ k) : Fin d → ZMod (L ^ N))
  left_inv x := by funext k; simp [co]
  right_inv x := by funext k; simp [co]
  map_add' x y := rfl

/-- The permutation on `ℤ^d`. -/
def permZ (σ : Equiv.Perm (Fin d)) : Zd d →+ Zd d where
  toFun a k := a (σ.symm k)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The permutation on `ℝ^d`. -/
def permA (σ : Equiv.Perm (Fin d)) : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) where
  toFun u k := u (σ.symm k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem permZ_ez (σ : Equiv.Perm (Fin d)) (m : Fin d) : permZ σ (ez m) = ez (σ m) := by
  funext k
  simp only [permZ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, ez, Pi.single_apply]
  congr 1
  apply propext; rw [Equiv.symm_apply_eq]

/-- The action of a permutation on the monomial basis. -/
def permMono (σ : Equiv.Perm (Fin d)) : Mono d → Mono d
  | .c => .c
  | .a1 k => .a1 (σ k)
  | .b1 k => .b1 (σ k)
  | .a2 s => .a2 (s.map σ)
  | .b2 s => .b2 (s.map σ)
  | .m2 k l => .m2 (σ k) (σ l)

theorem permMono_symm (σ : Equiv.Perm (Fin d)) (M : Mono d) : permMono σ.symm (permMono σ M) = M := by
  cases M <;> simp [permMono, Sym2.map_map]

/-- `permMono σ` as an equivalence. -/
def permMonoEquiv (σ : Equiv.Perm (Fin d)) : Mono d ≃ Mono d where
  toFun := permMono σ
  invFun := permMono σ.symm
  left_inv := permMono_symm σ
  right_inv M := by simpa using permMono_symm σ.symm M

theorem permT_prj (σ : Equiv.Perm (Fin d)) (a : Zd d) :
    (permT (L := L) (N := N) σ).toAddMonoidHom (prj a) = prj (permZ σ a) := rfl

theorem specList_conv_comm (a b : Fin d) (y : Lam d L N) :
    specList (tens (conv (dpt a) (dpt b)) id1) y = specList (tens (conv (dpt b) (dpt a)) id1) y ∧
    specList (tens id1 (conv (dpt a) (dpt b))) y = specList (tens id1 (conv (dpt b) (dpt a))) y := by
  constructor <;> simp [specList, tens, conv, dpt, id1] <;>
    simp only [add_comm (ez b), add_comm (-ez b), mul_comm (2⁻¹ : ℝ)] <;> abel

macro "pcomp" : tactic => `(tactic| (
  simp [specList, stencil, tens, dpt, id1, lap1, fw, conv, sc, Dik, permMono, permZ_ez, map_neg,
    map_add, *] <;> (try abel)))

theorem stencil_a2_ne {u v : Fin d} (h : u ≠ v) (y : Lam d L N) :
    specList (stencil (Mono.a2 s(u, v))) y = specList (tens (conv (dpt u) (dpt v)) id1) y ∧
    specList (stencil (Mono.b2 s(u, v))) y = specList (tens id1 (conv (dpt u) (dpt v))) y := by
  rcases lt_or_gt_of_ne h with h' | h'
  · simp [stencil, Dsym, Dik, min_eq_left h'.le, max_eq_right h'.le, h]
  · rw [Sym2.eq_swap]
    simp only [stencil, Dsym, Sym2.lift_mk, Dik, min_eq_left h'.le, max_eq_right h'.le,
      if_neg (Ne.symm h)]
    exact ⟨(specList_conv_comm v u y).1, (specList_conv_comm v u y).2⟩

set_option maxHeartbeats 1000000 in
theorem specList_perm (σ : Equiv.Perm (Fin d)) (M : Mono d) (y : Lam d L N) :
    specList ((stencil M).map fun p => (p.1, permZ σ p.2.1, permZ σ p.2.2)) y =
      specList (stencil (permMono σ M)) y := by
  cases M with
  | c => simp [specList, stencil, tens, id1, permMono]
  | a1 k => pcomp
  | b1 k => pcomp
  | a2 s =>
    induction s using Sym2.ind with
    | h k l =>
      rcases eq_or_ne k l with rfl | hkl
      · simp only [permMono, Sym2.map_mk]
        rw [show stencil (Mono.a2 s(k, k)) = tens (lap1 k) id1 by simp [stencil, Dsym, Dik],
          show stencil (Mono.a2 s(σ k, σ k)) = tens (lap1 (σ k)) id1 by simp [stencil, Dsym, Dik]]
        pcomp
      · simp only [permMono, Sym2.map_mk]
        have hσ : σ k ≠ σ l := σ.injective.ne hkl
        rw [(stencil_a2_ne hσ y).1]
        rw [show stencil (Mono.a2 s(k, l)) = stencil (Mono.a2 s(min k l, max k l)) by
          rw [← sym2_minmax]]
        rw [show stencil (Mono.a2 s(min k l, max k l)) = tens (conv (dpt (min k l)) (dpt (max k l))) id1
          by simp [stencil, Dsym_mk (min_le_max : min k l ≤ max k l), Dik, minmax_ne hkl]]
        rcases le_total k l with h' | h'
        · simp only [min_eq_left h', max_eq_right h']; pcomp
        · simp only [min_eq_right h', max_eq_left h']
          rw [(specList_conv_comm (σ k) (σ l) y).1]
          pcomp
  | b2 s =>
    induction s using Sym2.ind with
    | h k l =>
      rcases eq_or_ne k l with rfl | hkl
      · simp only [permMono, Sym2.map_mk]
        rw [show stencil (Mono.b2 s(k, k)) = tens id1 (lap1 k) by simp [stencil, Dsym, Dik],
          show stencil (Mono.b2 s(σ k, σ k)) = tens id1 (lap1 (σ k)) by simp [stencil, Dsym, Dik]]
        pcomp
      · simp only [permMono, Sym2.map_mk]
        have hσ : σ k ≠ σ l := σ.injective.ne hkl
        rw [(stencil_a2_ne hσ y).2]
        rw [show stencil (Mono.b2 s(k, l)) = stencil (Mono.b2 s(min k l, max k l)) by
          rw [← sym2_minmax]]
        rw [show stencil (Mono.b2 s(min k l, max k l)) = tens id1 (conv (dpt (min k l)) (dpt (max k l)))
          by simp [stencil, Dsym_mk (min_le_max : min k l ≤ max k l), Dik, minmax_ne hkl]]
        rcases le_total k l with h' | h'
        · simp only [min_eq_left h', max_eq_right h']; pcomp
        · simp only [min_eq_right h', max_eq_left h']
          rw [(specList_conv_comm (σ k) (σ l) y).2]
          pcomp
  | m2 k l =>
    rcases eq_or_ne k l with rfl | hkl
    · pcomp
    · have hσ : σ k ≠ σ l := σ.injective.ne hkl
      pcomp

/-- A permutation of the coordinates as an automorphism. -/
def AffAut.perm (σ : Equiv.Perm (Fin d)) : AffAut d L N where
  E := (permT σ).toEquiv
  R := (permT σ).toAddMonoidHom
  hE x := by simp
  Rz := permZ σ
  hRz a := permT_prj σ a
  hnorm a := by
    rw [supNormZ_le_iff]; intro k
    exact natAbs_le_supNormZ a (σ.symm k)
  A := permA σ
  hA a := rfl
  ρ := permMonoEquiv σ
  sgn _ := 1
  hmono M x := by
    rw [monoAt_eq_specList, autAlg_specList _ (permT σ).toAddMonoidHom (by simp) (permZ σ)
      (permT_prj σ), specList_perm, one_smul]
    rfl

end

end Loc
