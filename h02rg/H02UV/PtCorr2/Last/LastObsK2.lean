import PtCorr2.Last.LastObsK1
import PtCorr2.Last.LastOneTI

/-!
# Jets of the last step: `F_N` through the reference activity

The scalars `ε(F_∅)`, `c2(F_∅)`, `ε(F_a)`, `c2(F_a)` of an even element with sources (Case 2) form a
ring homomorphism `JT : OE → 𝔻₂ = (ℂ[δ]/δ²)[σ]/σ²` (`c2` is an `ε`-derivation on even elements,
`(FG)_a = F_∅G_a + F_aG_∅`), `JT F = (εF_∅ + δc2F_∅) + σ(εF_a + δc2F_a)`.

* `finG_eq`: at the last scale (`j + 1 = N`), the final object `F_N = ∑_U Ĩ_N^{Λ∖U}K_N(U)` of the map
  with localisation equals `e^{u(Λ)}e^{-u'(Λ)}(∏_BG'(B) + K'(Λ))` with the reference map
  (`Obs2.Est.LastKO1`), since both are `e^{u}𝔼θZ_{N-1}` (`stepO_ZVK`, `stepN_ZVK_last`);
* `JT_GpN`: `JT(G'(B)) = (1 - δy_B - σδβ_B)(1 + JT S(B))`;
* `JT_expU_diff`: `JT(e^{u(Λ)}e^{-u'(Λ)}) = e^{-Λ₀}(1 - σē_L)` with `Λ₀ = ∑_Bε(Loc_{Λ,B}S(Λ))_∅`,
  `ē_L = ∑_Bε(Loc_{Λ,B}S(Λ))_a` (no `Q` at the last scale).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Obs.Gen TrivSqZeroExt

variable {L N : ℕ} [NeZero L]

/-! ### The jet homomorphism -/

abbrev D1 := DualNumber ℂ
abbrev D2 := DualNumber D1

section Jet

/-- The jet `εx + δc2x` of an even element. -/
def jt (x : EvR (Lam 2 L N)) : D1 := inl (epsR x) + inr (c2E x)

@[simp] theorem jt_fst (x : EvR (Lam 2 L N)) : (jt x).fst = epsR x := by simp [jt]
@[simp] theorem jt_snd (x : EvR (Lam 2 L N)) : (jt x).snd = c2E x := by simp [jt]

theorem jt_mul (x y : EvR (Lam 2 L N)) : jt (x * y) = jt x * jt y := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [jt_fst, fst_mul, jt_fst, jt_fst, map_mul]
  · rw [jt_snd, snd_mul, jt_fst, jt_fst, jt_snd, jt_snd, c2E_mul, smul_eq_mul,
      MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]

theorem jt_add (x y : EvR (Lam 2 L N)) : jt (x + y) = jt x + jt y := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [jt_fst, fst_add, jt_fst, jt_fst, map_add]
  · rw [jt_snd, snd_add, jt_snd, jt_snd, c2E_add]

theorem jt_one : jt (1 : EvR (Lam 2 L N)) = 1 := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [jt_fst, fst_one, map_one]
  · rw [jt_snd, snd_one]; exact c2_oneE

theorem jt_zero : jt (0 : EvR (Lam 2 L N)) = 0 := by
  have h := jt_add (0 : EvR (Lam 2 L N)) 0
  rw [add_zero] at h
  have h2 : jt (0 : EvR (Lam 2 L N)) + 0 = jt (0 : EvR (Lam 2 L N)) + jt (0 : EvR (Lam 2 L N)) := by
    rw [add_zero]; exact h
  exact (add_left_cancel h2).symm

theorem jt_smul (r : ℂ) (x : EvR (Lam 2 L N)) : jt (r • x) = r • jt x := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [jt_fst, fst_smul, jt_fst, map_smul]
  · rw [jt_snd, snd_smul, jt_snd]
    show Suscept.c2 (r • (x : Grassmann.N (Lam 2 L N))) = r • Suscept.c2 (x : Grassmann.N (Lam 2 L N))
    rw [Suscept.c2_smul, smul_eq_mul]

theorem aCmp_smul' (r : ℂ) (F : OE .two (Lam 2 L N)) : aCmp (r • F) = r • aCmp F := rfl

/-- **The jet homomorphism** `JT F = jt F_∅ + σ jt F_a`. -/
def JT (F : OE .two (Lam 2 L N)) : D2 := inl (jt (bulk F)) + inr (jt (aCmp F))

@[simp] theorem JT_fst (F : OE .two (Lam 2 L N)) : (JT F).fst = jt (bulk F) := by simp [JT]
@[simp] theorem JT_snd (F : OE .two (Lam 2 L N)) : (JT F).snd = jt (aCmp F) := by simp [JT]

theorem JT_mul (F G : OE .two (Lam 2 L N)) : JT (F * G) = JT F * JT G := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [JT_fst, fst_mul, JT_fst, JT_fst, map_mul, jt_mul]
  · rw [JT_snd, snd_mul, JT_fst, JT_fst, JT_snd, JT_snd, aCmp_mul, jt_add, jt_mul, jt_mul,
      smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]

theorem JT_add (F G : OE .two (Lam 2 L N)) : JT (F + G) = JT F + JT G := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [JT_fst, fst_add, JT_fst, JT_fst, map_add, jt_add]
  · rw [JT_snd, snd_add, JT_snd, JT_snd, aCmp_add, jt_add]

theorem JT_one : JT (1 : OE .two (Lam 2 L N)) = 1 := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [JT_fst, fst_one, map_one, jt_one]
  · rw [JT_snd, snd_one, aCmp_one, jt_zero]

theorem JT_zero : JT (0 : OE .two (Lam 2 L N)) = 0 := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [JT_fst, fst_zero, map_zero, jt_zero]
  · rw [JT_snd, snd_zero]
    show jt (0 : EvR (Lam 2 L N)) = 0
    exact jt_zero

/-- `JT` as a ring homomorphism. -/
def JTh : OE .two (Lam 2 L N) →+* D2 where
  toFun := JT
  map_one' := JT_one
  map_mul' := JT_mul
  map_zero' := JT_zero
  map_add' := JT_add

@[simp] theorem JTh_apply (F : OE .two (Lam 2 L N)) : JTh F = JT F := rfl

theorem JT_smul (r : ℂ) (F : OE .two (Lam 2 L N)) : JT (r • F) = r • JT F := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [JT_fst, fst_smul, JT_fst, map_smul, jt_smul]
  · rw [JT_snd, snd_smul, JT_snd, aCmp_smul', jt_smul]

theorem JT_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (F : ι → OE .two (Lam 2 L N)) :
    JT (∑ i ∈ s, F i) = ∑ i ∈ s, JT (F i) := by
  induction s using Finset.induction_on with
  | empty => rw [sum_empty, sum_empty, JT_zero]
  | insert i s hi ih => rw [sum_insert hi, sum_insert hi, JT_add, ih]

theorem JT_pow (F : OE .two (Lam 2 L N)) (n : ℕ) : JT (F ^ n) = JT F ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, JT_one]
  | succ n ih => rw [pow_succ, pow_succ, JT_mul, ih]

theorem JT_prod {ι : Type*} (s : Finset ι) (F : ι → OE .two (Lam 2 L N)) :
    JT (∏ i ∈ s, F i) = ∏ i ∈ s, JT (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [prod_empty, prod_empty, JT_one]
  | insert i s hi ih => rw [prod_insert hi, prod_insert hi, JT_mul, ih]

/-- The four scalars. -/
theorem JT_eps_a (F : OE .two (Lam 2 L N)) :
    (JT F).snd.fst = ε ((F : SA .two (Lam 2 L N)).a) := by simp

theorem JT_c2_a (F : OE .two (Lam 2 L N)) :
    (JT F).snd.snd = Suscept.c2 ((F : SA .two (Lam 2 L N)).a) := by simp; rfl

theorem JT_eps_e (F : OE .two (Lam 2 L N)) :
    (JT F).fst.fst = ε ((F : SA .two (Lam 2 L N)).e) := by simp

theorem JT_c2_e (F : OE .two (Lam 2 L N)) :
    (JT F).fst.snd = Suscept.c2 ((F : SA .two (Lam 2 L N)).e) := by simp; rfl

end Jet

/-! ### Exponentials -/

section ExpJ

theorem D2_sq_zero {z : D2} (h1 : z.fst.fst = 0) (h2 : z.snd.fst = 0) : z * z = 0 := by
  refine TrivSqZeroExt.ext (TrivSqZeroExt.ext ?_ ?_) (TrivSqZeroExt.ext ?_ ?_)
  · simp [fst_mul, h1]
  · simp [fst_mul, snd_mul, h1]
  · simp [fst_mul, snd_mul, h1, h2]
  · simp [fst_mul, snd_mul, h1, h2]

theorem D2_sq_zero' {z : D2} (h : z.fst = 0) : z * z = 0 := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [fst_mul, h, zero_mul, fst_zero]
  · rw [snd_mul, h, zero_smul, MulOpposite.op_zero, zero_smul, add_zero, snd_zero]

theorem sum_range_two_of {M : Type*} [AddCommMonoid M] (f : ℕ → M) (hf : ∀ i, 2 ≤ i → f i = 0)
    (n : ℕ) : ∑ i ∈ range (n + 2), f i = f 0 + f 1 := by
  rw [sum_range_succ', sum_range_succ']
  rw [sum_eq_zero fun i _ => hf (i + 1 + 1) (by omega), zero_add, add_comm (f (0 + 1)), zero_add]

/-- `JT(e^Y) = 1 + JT Y` if `ε(Y_∅) = 0` and `(JT Y)² = 0`. -/
theorem JT_oexp {Y : OE .two (Lam 2 L N)} (hY : ε ((Y : SA .two (Lam 2 L N)).e) = 0)
    (h2 : JT Y * JT Y = 0) : JT (oexp Y) = 1 + JT Y := by
  rw [coe_oexp (pow_eq_zero_of_ε hY)]
  rw [show JT (∑ i ∈ range (Nf (Lam 2 L N) + 3), ((i.factorial : ℂ)⁻¹) • Y ^ i) =
      ∑ i ∈ range (Nf (Lam 2 L N) + 3), ((i.factorial : ℂ)⁻¹) • JT Y ^ i from by
    rw [JT_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [JT_smul, JT_pow]]
  rw [show Nf (Lam 2 L N) + 3 = (Nf (Lam 2 L N) + 1) + 2 by ring, sum_range_two_of _ (fun i hi => by
    rw [show i = 2 + (i - 2) by omega, pow_add, sq, h2, zero_mul, smul_zero]) _]
  simp

theorem JT_fst_fst_of_eps {Y : OE .two (Lam 2 L N)} (hY : ε ((Y : SA .two (Lam 2 L N)).e) = 0) :
    (JT Y).fst.fst = 0 := by rw [JT_eps_e, hY]

theorem JT_snd_fst_of_eps {Y : OE .two (Lam 2 L N)} (hY : ε ((Y : SA .two (Lam 2 L N)).a) = 0) :
    (JT Y).snd.fst = 0 := by rw [JT_eps_a, hY]

/-- `JT(e^x e^F) = e^x(1 + JT F)` for an observable `F`. -/
theorem JT_expU (x : ℂ) {F : OE .two (Lam 2 L N)} (hF : bulk F = 0) :
    JT (expU x F) = Complex.exp x • (1 + JT F) := by
  have he : ε ((F : SA .two (Lam 2 L N)).e) = 0 := ε_bulk_eq_zero_of_obs hF
  have h1 : (JT F).fst = 0 := by rw [JT_fst, hF, jt_zero]
  rw [expU, JT_smul, JT_oexp he (D2_sq_zero' h1)]

end ExpJ

theorem JT_neg (F : OE .two (Lam 2 L N)) : JT (-F) = -JT F := by
  have h := JT_add F (-F)
  rw [add_neg_cancel, JT_zero] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem jt_algebraMap (r : ℂ) : jt (algebraMap ℂ (EvR (Lam 2 L N)) r) = inl r := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [jt_fst, fst_inl, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
  · rw [jt_snd, snd_inl]
    show Suscept.c2 (((algebraMap ℂ (EvR (Lam 2 L N)) r : EvR (Lam 2 L N))) :
      Grassmann.N (Lam 2 L N)) = 0
    rw [Subalgebra.coe_algebraMap]; exact Suscept.c2_algebraMap r

/-! ### The last step -/

section Last

variable (P : ObsPts 2 L N) (j : ℕ) (C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ)
  (V W : OFam .two 2 L N) (K : OAct .two 2 L N)

/-- The final object `F_N = ∑_U Ĩ^{Λ∖U}K_N(U)` of the map with localisation. -/
def finG : OE .two (Lam 2 L N) :=
  ∑ U ∈ Pj (j + 1) (univ : Finset (Lam 2 L N)),
    bpowO j (GpO P j C V W K) (univ \ U) * Knext2O P j C V W K U

/-- **`F_N` through the reference activity** (last scale). -/
theorem finG_eq (hj : j + 1 = N) :
    finG P j C V W K = expU (uXB P j C V W K univ) (uXO P j C V W K univ) *
      expU (-uXBN j C V univ) (-uXON j C V univ) *
        (bpowO j (GpN j C V W) univ + KNO j C V W K univ) := by
  have h1 := stepO_ZVK P j C V W K
  have h2 := stepN_ZVK_last j C V W K hj
  have h3 : expU (-uXB P j C V W K univ) (-uXO P j C V W K univ) * finG P j C V W K =
      expU (-uXBN j C V univ) (-uXON j C V univ) *
        (bpowO j (GpN j C V W) univ + KNO j C V W K univ) := by
    rw [← h2, h1]; rfl
  calc finG P j C V W K = expU (uXB P j C V W K univ) (uXO P j C V W K univ) *
        (expU (-uXB P j C V W K univ) (-uXO P j C V W K univ) * finG P j C V W K) := by
        rw [← mul_assoc, expU_mul_expU_neg _ (bulk_uXO P j C V W K univ), one_mul]
    _ = _ := by rw [h3, mul_assoc]

theorem eps_YpN_a (b : Fin 2 → ℕ) : ε ((YpN C V b : SA .two (Lam 2 L N)).a) = 0 := by
  have halg : ((algebraMap ℂ (OE .two (Lam 2 L N)) (upBN C V b) : OE .two (Lam 2 L N)) :
      SA .two (Lam 2 L N)).a = 0 := by
    rw [Subalgebra.coe_algebraMap]; exact algebraMap_a _
  have hu : (upON C V b : SA .two (Lam 2 L N)).a =
      algebraMap ℂ (Alg 2 L N) (ε (VprO C V b : SA .two (Lam 2 L N)).a) := by
    show cmp true (πobs (epsO (VprO C V b)) : SA .two (Lam 2 L N)) = _
    rw [cmp_πobs]; rfl
  have h1 : (YpN C V b : SA .two (Lam 2 L N)).a =
      (VprO C V b : SA .two (Lam 2 L N)).a -
        ((algebraMap ℂ (OE .two (Lam 2 L N)) (upBN C V b) : OE .two (Lam 2 L N)) :
          SA .two (Lam 2 L N)).a - (upON C V b : SA .two (Lam 2 L N)).a := rfl
  rw [h1, halg, hu, sub_zero, map_sub, AlgHom.commutes, Algebra.algebraMap_self,
    RingHom.id_apply, sub_self]

theorem JT_YpN_sq (b : Fin 2 → ℕ) : JT (YpN C V b) * JT (YpN C V b) = 0 :=
  D2_sq_zero (JT_fst_fst_of_eps (eps_YpN C V b)) (JT_snd_fst_of_eps (eps_YpN_a C V b))

/-- `JT(G'(B)) = (1 - JT Y(B))(1 + JT S(B))`. -/
theorem JT_GpN (b : Fin 2 → ℕ) :
    JT (GpN j C V W b) = (1 - JT (YpN C V b)) * (1 + JT (SbO j C V W b)) := by
  have he : ε ((-YpN C V b : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).e = 0 := by
    show ε (-(YpN C V b : SA .two (Lam 2 L N))).e = 0
    rw [neg_e, map_neg, eps_YpN, neg_zero]
  have hsq : JT (-YpN C V b) * JT (-YpN C V b) = 0 := by
    rw [JT_neg, neg_mul_neg]; exact JT_YpN_sq C V b
  rw [GpN, JT_mul, JT_oexp he hsq, JT_neg, JT_add, JT_one, ← sub_eq_add_neg]

/-- `JT(e^{u(Λ)}e^{-u'(Λ)}) = e^{-Λ₀}(1 - σ ē_L)` at the last scale. -/
theorem JT_expU_diff (hj : j + 1 = N) :
    JT (expU (uXB P j C V W K univ) (uXO P j C V W K univ) *
        expU (-uXBN j C V univ) (-uXON j C V univ)) =
      Complex.exp (-∑ b ∈ blocks (L := L) (N := N) j univ, ε ((LSO P j C V W b : SA .two (Lam 2 L N)).e)) •
        (1 + inr (inl (-∑ b ∈ blocks (L := L) (N := N) j univ, ε ((LSO P j C V W b : SA .two (Lam 2 L N)).a)))) := by
  have hb0 : bulk (-uXON j C V univ) = 0 := by rw [map_neg, bulk_uXON, neg_zero]
  rw [expU_mul_expU _ _ (bulk_uXO P j C V W K univ) hb0]
  have hb : bulk (uXO P j C V W K univ + -uXON j C V univ) = 0 := by
    rw [map_add, bulk_uXO, hb0, add_zero]
  rw [JT_expU _ hb]
  have hQ : ∀ b, Q2O P j K b = 0 := fun b => Q2O_last P hj K b
  have hE0 : ∀ b, EthO C (Q2O P j K b) = 0 := fun b => by
    rw [hQ b]; exact (EthOL C).map_zero
  congr 1
  · -- the bulk constants
    congr 1
    rw [uXB, uXBN, ← sum_neg_distrib, ← sum_add_distrib, ← sum_neg_distrib]
    refine sum_congr rfl fun b _ => ?_
    rw [upB, upBN, uVpO, hE0, sub_zero, map_sub, Subalgebra.coe_sub, map_sub]
    show ε (((bulk (VprO C V b)) : EvR (Lam 2 L N)) : Alg 2 L N) -
        ε ((LSO P j C V W b : SA .two (Lam 2 L N)).e) +
        -ε (((bulk (VprO C V b)) : EvR (Lam 2 L N)) : Alg 2 L N) = _
    ring
  · congr 1
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [JT_fst, hb, jt_zero, fst_inr]
    · rw [JT_snd, snd_inr]
      have ha : aCmp (uXO P j C V W K univ + -uXON j C V univ) =
          algebraMap ℂ (EvR (Lam 2 L N))
            (-∑ b ∈ blocks (L := L) (N := N) j univ, ε ((LSO P j C V W b : SA .two (Lam 2 L N)).a)) := by
        refine Subtype.ext ?_
        rw [Subalgebra.coe_algebraMap]
        show ((uXO P j C V W K univ + -uXON j C V univ : OE .two (Lam 2 L N)) :
          SA .two (Lam 2 L N)).a = _
        rw [Subalgebra.coe_add, SA.add_a, NegMemClass.coe_neg, SA.neg_a, uXO, uXON,
          AddSubmonoidClass.coe_finsetSum, AddSubmonoidClass.coe_finsetSum, sum_a, sum_a,
          ← sum_neg_distrib, ← sum_add_distrib, map_neg, map_sum, ← sum_neg_distrib]
        refine sum_congr rfl fun b _ => ?_
        rw [upO_a, uVpO_a]
        have hu : (upON C V b : SA .two (Lam 2 L N)).a =
            algebraMap ℂ (Alg 2 L N) (ε (VprO C V b : SA .two (Lam 2 L N)).a) := by
          show cmp true (πobs (epsO (VprO C V b)) : SA .two (Lam 2 L N)) = _
          rw [cmp_πobs]; rfl
        rw [hu, hQ b]
        have e1 : (VprO C V b : SA .two (Lam 2 L N)).a = expLC C (V b : SA .two (Lam 2 L N)).a := by
          rw [VprO, EthO_eq_expO]; rfl
        have e2 : (LSO P j C V W b : SA .two (Lam 2 L N)).a =
            locAp Obs.Case.two P.a (Step2.Bp (L := L) (N := N) j b) (blockSet (L := L) (N := N) j b)
              (SXO j C V W (Step2.Bp (L := L) (N := N) j b) : SA .two (Lam 2 L N)).a := rfl
        have e3 : ((0 : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a = 0 := rfl
        rw [e1, e2, e3, map_zero, sub_zero, map_sub, map_sub]
        abel
      rw [ha, jt_algebraMap]

end Last

end

end PtCorr2
