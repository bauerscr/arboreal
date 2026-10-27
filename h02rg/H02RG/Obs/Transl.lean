import Obs.TranslGen
import Obs.MapTriB

/-!
# Translation covariance of the observable map and flow

A generated lattice automorphism `T` (`Step.IsGen`) acts on the algebra with observables
componentwise (`autO T`, the source fields `σ_a, σ_b` are not moved), and the observable points
are moved: `a ↦ T a`, `b ↦ T b`.

* `autO` commutes with `θ`, `ι` and (for `T`-invariant `C`) with `𝔼_C` (`autO2_thetaO`,
  `autO2_inclO`, `autO_ECO`);
* the ingredients of the observable map at `(a, b, K)` are carried to those at
  `(T a, T b, K')` with `K'(T X) = T K(X)`: the split evaluation (`autO_splitO`, `autO_VfullX`),
  `Loc^obs` (`autO_LocO`), `J^obs` (`autO_JO`), the coupling constants of `Q^obs`
  (`Qcoup_transl`) and `nextObs` (`nextObs_transl`), `u^obs` (`autO_uObsX`);
* **one step** (`KnextO_transl`): if `T` preserves `j`- and `(j+1)`-blocks, then
  `T K_{j+1}(U) = K'_{j+1}(T U)` and the next coupling constants agree;
* **the flow** (`flowO_aut`, `flowO_transl`): for a translation `t` with `L^k ∣ t` and
  `k ≤ N`, for all `j ≤ k`:
  `V^obs_j` at `(a + t, b + t)` equals `V^obs_j` at `(a, b)`, and
  `K_j(T X)` at `(a + t, b + t)` is `autO T (K_j(X))` at `(a, b)`.
-/

namespace Obs

noncomputable section

open Finset Grassmann SA Loc Step LocObs Gen FRD

variable {d L N : ℕ} [NeZero L] {c : Case}

/-! ### The action on the algebra with observables -/

section Aut

theorem autAlg_inv' (E : Lam d L N ≃ Lam d L N) (x : Alg d L N) :
    autAlg E (inv' x) = inv' (autAlg E x) := (Grassmann.inv'_map _ x).symm

theorem autAlg2_inv' (E : Lam d L N ≃ Lam d L N) (x : Alg2 d L N) :
    autAlg2 E (inv' x) = inv' (autAlg2 E x) := (Grassmann.inv'_map _ x).symm

/-- `T` acting on the algebra with observables (componentwise). -/
def autO (T : AffAut d L N) : OE c (Lam d L N) →ₐ[ℂ] OE c (Lam d L N) :=
  mapO (autAlg T.E) (autAlg_inv' T.E)

/-- `T` acting on the doubled algebra with observables (componentwise). -/
def autO2 (T : AffAut d L N) : OE c (Lam d L N ⊕ Lam d L N) →ₐ[ℂ] OE c (Lam d L N ⊕ Lam d L N) :=
  mapO (autAlg2 T.E) (autAlg2_inv' T.E)

variable (T : AffAut d L N)

@[simp] theorem autO_e (F : OE c (Lam d L N)) :
    ((autO T F : OE c (Lam d L N)) : SA c (Lam d L N)).e = autAlg T.E (F : SA c (Lam d L N)).e := rfl
@[simp] theorem autO_a (F : OE c (Lam d L N)) :
    ((autO T F : OE c (Lam d L N)) : SA c (Lam d L N)).a = autAlg T.E (F : SA c (Lam d L N)).a := rfl
@[simp] theorem autO_b (F : OE c (Lam d L N)) :
    ((autO T F : OE c (Lam d L N)) : SA c (Lam d L N)).b = autAlg T.E (F : SA c (Lam d L N)).b := rfl
@[simp] theorem autO_ab (F : OE c (Lam d L N)) :
    ((autO T F : OE c (Lam d L N)) : SA c (Lam d L N)).ab =
      autAlg T.E (F : SA c (Lam d L N)).ab := rfl

theorem autO2_thetaO (F : OE c (Lam d L N)) : autO2 T (thetaO F) = thetaO (autO T F) :=
  Subtype.ext (SA.ext (theta_autAlg T.E (F : SA c (Lam d L N)).e).symm
    (theta_autAlg T.E (F : SA c (Lam d L N)).a).symm (theta_autAlg T.E (F : SA c (Lam d L N)).b).symm
    (theta_autAlg T.E (F : SA c (Lam d L N)).ab).symm)

theorem autO2_inclO (F : OE c (Lam d L N)) : autO2 T (inclO F) = inclO (autO T F) :=
  Subtype.ext (SA.ext (incl_autAlg T.E (F : SA c (Lam d L N)).e).symm
    (incl_autAlg T.E (F : SA c (Lam d L N)).a).symm (incl_autAlg T.E (F : SA c (Lam d L N)).b).symm
    (incl_autAlg T.E (F : SA c (Lam d L N)).ab).symm)

theorem autO_ECO {C : Matrix (Lam d L N) (Lam d L N) ℝ} (hC : ∀ x y, C (T.E x) (T.E y) = C x y)
    (F : OE c (Lam d L N ⊕ Lam d L N)) : autO T (ECO C F) = ECO C (autO2 T F) :=
  Subtype.ext (SA.ext (EC_autAlg2 T.E hC (F : SA c (Lam d L N ⊕ Lam d L N)).e).symm
    (EC_autAlg2 T.E hC (F : SA c (Lam d L N ⊕ Lam d L N)).a).symm
    (EC_autAlg2 T.E hC (F : SA c (Lam d L N ⊕ Lam d L N)).b).symm
    (EC_autAlg2 T.E hC (F : SA c (Lam d L N ⊕ Lam d L N)).ab).symm)

theorem autO_emb (x : EvR (Lam d L N)) : autO T (emb x : OE c (Lam d L N)) = emb (AE T x) :=
  Subtype.ext (SA.ext rfl (map_zero _) (map_zero _) (map_zero _))

theorem autO_oexp {F : OE c (Lam d L N)} (hn : IsNilpotent F) : autO T (oexp F) = oexp (autO T F) :=
  IsNilpotent.map_exp hn _

theorem autO_emb_VE {T : AffAut d L N} (hT : IsGen T) (V : Vcoup) (X : Finset (Lam d L N)) :
    autO T (emb (VE V X) : OE c (Lam d L N)) = emb (VE V (T.img X)) := by
  rw [autO_emb, AE_VE hT]

end Aut

/-! ### Split evaluation -/

section Split

variable (T : AffAut d L N)

theorem autAlg_nx (a b : Lam d L N) : autAlg T.E (nx a b) = nx (T.E a) (T.E b) := by
  simp [nx, autAlg_psi, autAlg_psibar]

theorem autAlg_pbp' (a : Lam d L N) :
    autAlg T.E (psibar a * psi a) = psibar (T.E a) * psi (T.E a) := by
  simp [autAlg_psi, autAlg_psibar]

theorem autO_halfAO (W : Coup c) (a b : Lam d L N) :
    autO T (halfAO c W a b) = halfAO c W (T.E a) (T.E b) := by
  refine Subtype.ext ?_
  cases c <;> ext <;> simp [halfA, autAlg_psi, autAlg_psibar, autAlg_nx]

theorem autO_halfBO (W : Coup c) (a b : Lam d L N) :
    autO T (halfBO c W a b) = halfBO c W (T.E a) (T.E b) := by
  refine Subtype.ext ?_
  cases c <;> ext <;> simp [halfB, autAlg_psi, autAlg_psibar, autAlg_nx]

theorem ind_img (x : Lam d L N) (X : Finset (Lam d L N)) :
    ind (T.E x ∈ T.img X) = ind (x ∈ X) := by
  simp only [ind, E_mem_img]

theorem autO_splitO (W : Coup c) (a b : Lam d L N) (X : Finset (Lam d L N)) :
    autO T (splitO c W a b X) = splitO c W (T.E a) (T.E b) (T.img X) := by
  rw [splitO, splitO, map_add, map_smul, map_smul, autO_halfAO, autO_halfBO, ind_img, ind_img]

theorem autO_VfullX {T : AffAut d L N} (hT : IsGen T) (V : Vcoup) (W : Coup c) (a b : Lam d L N)
    (X : Finset (Lam d L N)) :
    autO T (VfullX V W a b X) = VfullX V W (T.E a) (T.E b) (T.img X) := by
  rw [VfullX, VfullX, map_add, autO_emb_VE hT, autO_splitO]

end Split

/-! ### `Loc^obs` -/

section Loc

variable (T : AffAut d L N)

theorem mass1_autAlg (s : ℤˣ) (F : Alg d L N) : mass1 s (autAlg T.E F) = mass1 s F := by
  simp only [mass1, coeff_autAlg]
  refine Fintype.sum_equiv T.E.symm _ _ fun x => ?_
  congr 1
  funext i; fin_cases i; rfl

theorem mass2_autAlg (F : Alg d L N) : mass2 (autAlg T.E F) = mass2 F := by
  simp only [mass2, coeff_autAlg]
  refine Fintype.sum_equiv T.E.symm _ _ fun x => ?_
  refine Fintype.sum_equiv T.E.symm _ _ fun y => ?_
  congr 1
  funext i; fin_cases i <;> rfl

theorem img_inter (X Y : Finset (Lam d L N)) : T.img (X ∩ Y) = T.img X ∩ T.img Y :=
  Finset.map_inter _ _

theorem img_singleton (x : Lam d L N) : T.img {x} = {T.E x} := img_singleton' T x

theorem img_pair (x y : Lam d L N) : T.img {x, y} = {T.E x, T.E y} := by
  simp [AffAut.img, Finset.map_insert]

theorem autAlg_locGen (P X Y : Finset (Lam d L N)) (f f' : Lam d L N → Alg d L N)
    (hf : ∀ z, autAlg T.E (f z) = f' (T.E z)) (c' : ℂ) :
    autAlg T.E (locGen P X Y f c') = locGen (T.img P) (T.img X) (T.img Y) f' c' := by
  rw [locGen, locGen, map_smul, map_sum, ← img_inter, ← img_inter, T.card_img]
  congr 1
  rw [AffAut.img, sum_map]
  exact sum_congr rfl fun z _ => hf z

theorem autAlg_locOdd (s : ℤˣ) (P X Y : Finset (Lam d L N)) (F : Alg d L N) :
    autAlg T.E (locOdd s P X Y F) = locOdd s (T.img P) (T.img X) (T.img Y) (autAlg T.E F) := by
  rw [locOdd, locOdd, mass1_autAlg]
  exact autAlg_locGen T _ _ _ (fun z => ψ (z, s)) (fun z => ψ (z, s))
    (fun z => Flow.autAlg_ψ T.E (z, s)) _

theorem autAlg_locEven (P X Y : Finset (Lam d L N)) (F : Alg d L N) :
    autAlg T.E (locEven P X Y F) = locEven (T.img P) (T.img X) (T.img Y) (autAlg T.E F) := by
  rw [locEven, locEven, map_add, mass2_autAlg, ε_autAlg,
    autAlg_locGen T _ _ _ (fun _ => (1 : Alg d L N)) (fun _ => (1 : Alg d L N))
      (fun _ => map_one _),
    autAlg_locGen T _ _ _ pbp pbp (fun z => autAlg_pbp' T z)]

theorem autAlg_locA (c' : ObsCase) (a : Lam d L N) (X Y : Finset (Lam d L N)) (F : Alg d L N) :
    autAlg T.E (locA c' a X Y F) = locA c' (T.E a) (T.img X) (T.img Y) (autAlg T.E F) := by
  cases c'
  · simp only [locA]; rw [autAlg_locOdd, img_singleton]
  · simp only [locA]; rw [autAlg_locEven, img_singleton]

theorem autAlg_locB (c' : ObsCase) (b : Lam d L N) (X Y : Finset (Lam d L N)) (F : Alg d L N) :
    autAlg T.E (locB c' b X Y F) = locB c' (T.E b) (T.img X) (T.img Y) (autAlg T.E F) := by
  cases c'
  · simp only [locB]; rw [autAlg_locOdd, img_singleton]
  · simp only [locB]; rw [autAlg_locEven, img_singleton]

theorem autAlg_locAB (a b : Lam d L N) (X Y : Finset (Lam d L N)) (F : Alg d L N) :
    autAlg T.E (locAB a b X Y F) = locAB (T.E a) (T.E b) (T.img X) (T.img Y) (autAlg T.E F) := by
  rw [locAB, locAB, autAlg_locEven, img_pair]

/-- `T Loc_{Y,B} F = Loc_{TY,TB} T F` for small `Y` and `F_∅` localised in the neighbourhood
of `Y`. -/
theorem autO_LocO (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {j : ℕ} (hj : j + 1 < N) (a b : Lam d L N)
    {Y : Finset (Lam d L N)} (hY : IsSmall j Y) (B : Finset (Lam d L N)) (F : OE c (Lam d L N))
    (hF : (F : SA c (Lam d L N)).e ∈ NX (nbhd j Y : Set (Lam d L N))) :
    autO T (LocO a b Y B F) = LocO (T.E a) (T.E b) (T.img Y) (T.img B) (autO T F) := by
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_)
  · show autAlg T.E (LocXY Y B _) = LocXY (T.img Y) (T.img B) (autAlg T.E _)
    exact T.LocXY_aut (region_small hd hL hj hY) hY.2.1.1 _ hF
  · exact autAlg_locA T _ a Y B _
  · exact autAlg_locB T _ b Y B _
  · exact autAlg_locAB T a b Y B _

end Loc

/-! ### `J^obs`, `Q^obs` and the coupling constants -/

section Ingr

variable {T : AffAut d L N} (hT : IsGen T) {j : ℕ} (hj : j ≤ N) (hP : PresBlocks j T)
  {K K' : Finset (Lam d L N) → OE c (Lam d L N)}

include hT hj hP in
theorem smallAt_img (x : Lam d L N) :
    smallAt j (T.E x) = (smallAt j x).image T.img := by
  classical
  obtain ⟨T', hT', hP', e, e'⟩ := hP.exists_inv hT hj
  have eE : ∀ y, T'.E (T.E y) = y := E_inv_of_img e
  ext Y
  simp only [smallAt, mem_filter, mem_image, mem_smallSets]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨T'.img Y, ⟨(hP'.isSmall_img hT' hj).2 h1, ?_⟩, e' Y⟩
    rw [← eE x]; exact (E_mem_img T').2 h2
  · rintro ⟨Y', ⟨h1, h2⟩, rfl⟩
    exact ⟨(hP.isSmall_img hT hj).2 h1, (E_mem_img T).2 h2⟩

include hT hj hP in
theorem sum_smallAt_img {M : Type*} [AddCommMonoid M] (x : Lam d L N)
    (f : Finset (Lam d L N) → M) :
    ∑ X ∈ smallAt j (T.E x), f X = ∑ X ∈ smallAt j x, f (T.img X) := by
  rw [smallAt_img hT hj hP, sum_image fun Y _ Y' _ e => img_injective T e]

theorem cardAB_img (a b : Lam d L N) (X : Finset (Lam d L N)) :
    cardAB (T.E a) (T.E b) (T.img X) = cardAB a b X := by
  rw [cardAB, cardAB, ← img_pair, ← img_inter, T.card_img]

include hT hj hP in
/-- The coupling constants of `Q^obs` at `(T a, T b)` for `K'` with `K'(T X) = T K(X)`. -/
theorem Qcoup_transl (hKK' : ∀ Y, K' (T.img Y) = autO T (K Y)) (a b : Lam d L N) :
    Qcoup c j K' (T.E a) (T.E b) = Qcoup c j K a b := by
  cases c <;> by_cases hj1 : j + 1 < N
  · simp only [Qcoup, if_pos hj1, sum_smallAt_img hT hj hP, hKK', autO_a, autO_b, autO_ab,
      mass1_autAlg, mass2_autAlg, ε_autAlg, cardAB_img]
  · simp only [Qcoup, if_neg hj1]
  · simp only [Qcoup, if_pos hj1, sum_smallAt_img hT hj hP, hKK', autO_a, autO_b, autO_ab,
      mass1_autAlg, mass2_autAlg, ε_autAlg, cardAB_img]
  · simp only [Qcoup, if_neg hj1]

include hT hj hP in
/-- The next observable coupling constants at `(T a, T b)` for `K'` with `K'(T X) = T K(X)`. -/
theorem nextObs_transl {C : Matrix (Lam d L N) (Lam d L N) ℝ}
    (hC : ∀ x y, C (T.E x) (T.E y) = C x y) (Vo : Coup c)
    (hKK' : ∀ Y, K' (T.img Y) = autO T (K Y)) (a b : Lam d L N) :
    nextObs C j Vo K' (T.E a) (T.E b) = nextObs C j Vo K a b := by
  rw [nextObs, nextObs, Wcoup, Wcoup, Qcoup_transl hT hj hP hKK', hC, hC, hC]

include hT hj hP in
theorem autO_uObsX {C : Matrix (Lam d L N) (Lam d L N) ℝ}
    (hC : ∀ x y, C (T.E x) (T.E y) = C x y) (Vo : Coup c)
    (hKK' : ∀ Y, K' (T.img Y) = autO T (K Y)) (a b : Lam d L N)
    (X : Finset (Lam d L N)) :
    autO T (uObsX j C Vo K a b X) = uObsX j C Vo K' (T.E a) (T.E b) (T.img X) := by
  rw [uObsX, uObsX, autO_splitO, nextObs_transl hT hj hP hC Vo hKK']

include hT hj hP in
/-- `T J(B, X) = J'(T B, T X)`. -/
theorem autO_JO (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hK : InK j (bulkK K))
    (hKK' : ∀ Y, K' (T.img Y) = autO T (K Y)) (a b : Lam d L N)
    {p : Fin d → ℕ} (hp : p ∈ blockIdx (L := L) (N := N) j) (X : Finset (Lam d L N)) :
    autO T (JO a b j K p X) = JO (T.E a) (T.E b) j K' (bmap j T p) (T.img X) := by
  have hB := img_blockSet_bmap hT hj hP hp
  have hLoc : ∀ (h1 : j + 1 < N) {Y : Finset (Lam d L N)}, IsSmall j Y →
      autO T (LocO a b Y (blockSet j p) (K Y)) =
        LocO (T.E a) (T.E b) (T.img Y) (blockSet j (bmap j T p)) (K' (T.img Y)) := by
    intro h1 Y hY
    rw [autO_LocO T hd hL h1 a b hY _ _ (hK.loc Y ⟨hY.1, hY.2.1⟩), hB, ← hKK' Y]
  have c1 : (j + 1 < N ∧ IsSmall j (T.img X) ∧ blockSet j (bmap j T p) ⊆ T.img X) ↔
      (j + 1 < N ∧ IsSmall j X ∧ blockSet j p ⊆ X) := by
    rw [← hB, hP.isSmall_img hT hj, AffAut.img, AffAut.img, Finset.map_subset_map]
  have c2 : T.img X = blockSet j (bmap j T p) ↔ X = blockSet j p := by
    rw [← hB]; exact (img_injective T).eq_iff
  unfold JO
  by_cases hc : j + 1 < N ∧ IsSmall j X ∧ blockSet j p ⊆ X
  · rw [if_pos hc, if_pos (c1.2 hc)]
    by_cases hx : X = blockSet j p
    · rw [if_pos hx, if_pos (c2.2 hx), map_neg, map_sum]
      congr 1
      obtain ⟨T', hT', hP', e, e'⟩ := hP.exists_inv hT hj
      have hS : ((smallSets j).filter fun Y => blockSet j (bmap j T p) ⊆ Y ∧
          Y ≠ blockSet j (bmap j T p)) =
          ((smallSets j).filter fun Y => blockSet j p ⊆ Y ∧ Y ≠ blockSet j p).image T.img := by
        ext Y
        simp only [mem_filter, mem_image, mem_smallSets]
        constructor
        · rintro ⟨h1, h2, h3⟩
          refine ⟨T'.img Y, ⟨(hP'.isSmall_img hT' hj).2 h1, ?_, ?_⟩, e' Y⟩
          · have := img_mono T' h2
            rwa [← hB, e] at this
          · intro h4
            apply h3
            rw [← e' Y, h4, hB]
        · rintro ⟨Y', ⟨h1, h2, h3⟩, rfl⟩
          refine ⟨(hP.isSmall_img hT hj).2 h1, ?_, ?_⟩
          · rw [← hB]; exact img_mono T h2
          · rw [← hB]; exact fun h4 => h3 (img_injective T h4)
      rw [hS, sum_image fun Y _ Y' _ e => img_injective T e]
      refine sum_congr rfl fun Y hY => ?_
      exact hLoc hc.1 (mem_smallSets.1 (mem_filter.1 hY).1)
    · rw [if_neg hx, if_neg (mt c2.1 hx)]
      exact hLoc hc.1 hc.2.1
  · rw [if_neg hc, if_neg (mt c1.1 hc), map_zero]

end Ingr

/-! ### One step -/

section Step

variable {T : AffAut d L N} {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℝ} (Vb : Vcoup)
  (Vo : Coup c) {K K' : Finset (Lam d L N) → OE c (Lam d L N)}

/-- **Covariance of one step of the observable map**: if `T` preserves `j`- and `(j+1)`-blocks,
`C` is `T`-invariant, `K'(T Y) = T K(Y)` on connected `Y`, and `K`, `K'` have the same bulk part
(an element of `𝒦^∅_j`), then `T K_{j+1}(U) = K'_{j+1}(T U)` at the moved points. -/
theorem KnextO_transl (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hj1 : j + 1 ≤ N) (hT : IsGen T)
    (hP : PresBlocks j T) (hP1 : PresBlocks (j + 1) T) (hC : ∀ x y, C (T.E x) (T.E y) = C x y)
    (hK : InK j (bulkK K)) (hb : bulkK K' = bulkK K)
    (hKK' : ∀ Y, K' (T.img Y) = autO T (K Y)) (a b : Lam d L N)
    (U : Finset (Lam d L N)) :
    autO T (KnextO j C Vb Vo K a b U) = KnextO j C Vb Vo K' (T.E a) (T.E b) (T.img U) := by
  have hj : j ≤ N := by omega
  have hKs := hKK'
  have hu : uVb j C Vb K' = uVb j C Vb K := by rw [uVb, uVb, hb]
  have hn := nextObs_transl hT hj hP hC Vo hKs a b
  have hcard : ∀ p ∈ blockIdx (L := L) (N := N) j,
      ((blockSet (L := L) (N := N) j (bmap j T p)).card : ℂ) = (blockSet (L := L) (N := N) j p).card := by
    intro p hp
    rw [← img_blockSet_bmap hT hj hP hp, T.card_img]
  have hexp : ∀ F : OE c (Lam d L N), bulk F = 0 → autO T (oexp F) = oexp (autO T F) :=
    fun F hF => autO_oexp T (isNilpotent_of_obs hF)
  rw [KnextO, KnextO,
    map_KnextG (A := obsA c C) (A' := obsA c C) (autO T) (autO2 T) (autO2_thetaO T)
      (autO2_inclO T) (fun y => autO_ECO T hC y)]
  refine KnextG_relabel (obsA c C) hT hj ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ hj1 hP1 hP U
  · intro p hp
    show autO T (oexp (-VfullX Vb Vo a b (blockSet j p))) =
      oexp (-VfullX Vb Vo (T.E a) (T.E b) (blockSet j (bmap j T p)))
    rw [autO_oexp T (isNilpotent_VfullX a b Vb _ _).neg, map_neg, autO_VfullX hT,
      img_blockSet_bmap hT hj hP hp]
  · intro p hp
    show autO T (oexp (-VfullX (uVb j C Vb K).2 (nextObs C j Vo K a b) a b (blockSet j p))) =
      oexp (-VfullX (uVb j C Vb K').2 (nextObs C j Vo K' (T.E a) (T.E b)) (T.E a) (T.E b)
        (blockSet j (bmap j T p)))
    rw [autO_oexp T (isNilpotent_VfullX a b _ _ _).neg, map_neg, autO_VfullX hT,
      img_blockSet_bmap hT hj hP hp, hu, hn]
  · intro p hp
    show autO T (algebraMap ℂ _ _ * oexp (uObsX j C Vo K a b (blockSet j p))) =
      algebraMap ℂ _ _ * oexp (uObsX j C Vo K' (T.E a) (T.E b) (blockSet j (bmap j T p)))
    rw [map_mul, AlgHom.commutes, hexp _ (bulk_uObsX _ _ _ _ _ _ _),
      autO_uObsX hT hj hP hC Vo hKs, img_blockSet_bmap hT hj hP hp, hu, hcard p hp]
  · intro p hp
    show autO T (algebraMap ℂ _ _ * oexp (-uObsX j C Vo K a b (blockSet j p))) =
      algebraMap ℂ _ _ * oexp (-uObsX j C Vo K' (T.E a) (T.E b) (blockSet j (bmap j T p)))
    rw [map_mul, AlgHom.commutes, hexp _ (by rw [map_neg, bulk_uObsX, neg_zero]), map_neg,
      autO_uObsX hT hj hP hC Vo hKs, img_blockSet_bmap hT hj hP hp, hu, hcard p hp]
  · intro p hp X
    exact autO_JO hT hj hP hd hL hK hKs a b hp X
  · intro Y _
    exact (hKK' Y).symm

end Step

/-! ### The flow -/

section Flow

variable {N : ℕ} {msq ℓ₀ : ℝ} (V₀ : Vcoup) (Vo₀ : Coup c)

/-- **Automorphism covariance of the observable flow**: if the generated automorphism `T`
preserves `i`-blocks for all `i ≤ k ≤ N`, then for `j ≤ k` the observable coupling constants at
`(T a, T b)` and `(a, b)` agree and `K_j(T X) = T K_j(X)`. -/
theorem flowO_aut (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L)
    (hgood : ∀ j < N, GoodCov (d := d) (L := L) (N := N) j ℓ₀ (Flow.covAt d L N msq j))
    {T : AffAut d L N} (hT : IsGen T) {k : ℕ} (hk : k ≤ N) (hP : ∀ i ≤ k, PresBlocks i T)
    (a b : Lam d L N) :
    ∀ j ≤ k, (flowO d L c N msq V₀ Vo₀ (T.E a) (T.E b) j).1 = (flowO d L c N msq V₀ Vo₀ a b j).1 ∧
      ∀ X, (flowO d L c N msq V₀ Vo₀ (T.E a) (T.E b) j).2 (T.img X) =
        autO T ((flowO d L c N msq V₀ Vo₀ a b j).2 X)
  | 0, _ => ⟨rfl, fun _ => (map_zero _).symm⟩
  | j + 1, hj => by
    obtain ⟨ih1, ih2⟩ := flowO_aut hd hL hgood hT hk hP a b j (by omega)
    have hjN : j < N := by omega
    have hC := (hgood j hjN).covInv T hT
    have hK : InK j (bulkK (flowO d L c N msq V₀ Vo₀ a b j).2) := by
      rw [bulkK_flowO]; exact Flow.InK_flowN hd hL hgood V₀ j hjN
    have hb : bulkK (flowO d L c N msq V₀ Vo₀ (T.E a) (T.E b) j).2 =
        bulkK (flowO d L c N msq V₀ Vo₀ a b j).2 := by rw [bulkK_flowO, bulkK_flowO]
    have hPj := hP j (by omega)
    have hPj1 := hP (j + 1) hj
    have hKs := ih2
    rw [flowO_succ, flowO_succ, ih1]
    refine ⟨?_, fun X => ?_⟩
    · rw [nextObs_transl hT (by omega) hPj hC _ hKs]
    · show restrO (j + 1) _ (T.img X) = autO T (restrO (j + 1) _ X)
      by_cases hX : IsConn (j + 1) X
      · have hX' : IsConn (j + 1) (T.img X) := (hPj1.isConn_img hT (by omega)).2 hX
        rw [restrO_of_conn _ hX, restrO_of_conn _ hX',
          KnextO_transl _ _ hd hL (by omega) hT hPj hPj1 hC hK hb ih2]
      · have hX' : ¬ IsConn (j + 1) (T.img X) := fun h => hX ((hPj1.isConn_img hT (by omega)).1 h)
        simp [restrO, hX, hX']

theorem presBlocks_transl_of {k : ℕ} (hk : k ≤ N) (t : Lam d L N)
    (ht : ∀ i, L ^ k ∣ (co t i).val) : ∀ i ≤ k, PresBlocks i (AffAut.transl t) := fun i hi =>
  Flow.presBlocks_transl' (by omega) t fun m => (pow_dvd_pow L hi).trans (ht m)

/-- **Translation covariance of the observable flow**: for a translation `t` with
`L^k ∣ t` (coordinatewise) and `k ≤ N`, for all `j ≤ k`:
`V^obs_j(a + t, b + t) = V^obs_j(a, b)` and `K_j(a + t, b + t)(X + t) = T_t K_j(a, b)(X)`. -/
theorem flowO_transl (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L)
    (hgood : ∀ j < N, GoodCov (d := d) (L := L) (N := N) j ℓ₀ (Flow.covAt d L N msq j))
    {k : ℕ} (hk : k ≤ N) (t : Lam d L N) (ht : ∀ i, L ^ k ∣ (co t i).val) (a b : Lam d L N) :
    ∀ j ≤ k, (flowO d L c N msq V₀ Vo₀ (a + t) (b + t) j).1 = (flowO d L c N msq V₀ Vo₀ a b j).1 ∧
      ∀ X, (flowO d L c N msq V₀ Vo₀ (a + t) (b + t) j).2 ((AffAut.transl t).img X) =
        autO (AffAut.transl t) ((flowO d L c N msq V₀ Vo₀ a b j).2 X) :=
  flowO_aut V₀ Vo₀ hd hL hgood (IsGen.transl t) hk (presBlocks_transl_of hk t ht) a b

/-- The next coupling constants (`(u + V)^obs_{j+1}`, `nextObs`) are translation invariant for
steps `j + 1 ≤ k`. -/
theorem nextObs_flowO_transl (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L)
    (hgood : ∀ j < N, GoodCov (d := d) (L := L) (N := N) j ℓ₀ (Flow.covAt d L N msq j))
    {k : ℕ} (hk : k ≤ N) (t : Lam d L N) (ht : ∀ i, L ^ k ∣ (co t i).val) (a b : Lam d L N)
    {j : ℕ} (hj : j + 1 ≤ k) :
    nextObs (Flow.covAt d L N msq j) j (flowO d L c N msq V₀ Vo₀ (a + t) (b + t) j).1
        (flowO d L c N msq V₀ Vo₀ (a + t) (b + t) j).2 (a + t) (b + t) =
      nextObs (Flow.covAt d L N msq j) j (flowO d L c N msq V₀ Vo₀ a b j).1
        (flowO d L c N msq V₀ Vo₀ a b j).2 a b := by
  have hP := presBlocks_transl_of hk t ht
  obtain ⟨h1, h2⟩ := flowO_transl V₀ Vo₀ hd hL hgood hk t ht a b j (by omega)
  have hC := (hgood j (by omega)).covInv (AffAut.transl t) (IsGen.transl t)
  rw [h1]
  exact nextObs_transl (T := AffAut.transl t) (IsGen.transl t) (by omega) (hP j (by omega)) hC _
    h2 a b

end Flow

end

end Obs
