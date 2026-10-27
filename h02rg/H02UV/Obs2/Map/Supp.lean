import Obs2.Flow.Hist
import Obs2.Loc.LocT
import Step2.Map.Mem
import Step2.Map.StepFinal

/-!
# Support of the source components (algebraic input for Lemma `lem:coal`)

For `i : Bool` let `cmp i F` be the `σ_a`-component `F_a` (`i = true`) resp. the `σ_b`-component
`F_b` (`i = false`) of `F` in the algebra with sources. The elements **without `σ_i`**,
`F_i = 0` and `F_{ab} = 0`, form a subalgebra `noXS c Λ i` (`noX c Λ i` on even elements): the
`σ_i` and `σ_aσ_b` components of a product contain a factor `F_i` or `F_{ab}`.

## Results
* closure: `noX` is stable under `θ`, the inclusion, `𝔼_C`, `e^{±ℒ_C}`, `𝔼_Cθ`, `F_C`, `e^·`,
  `π_obs`, `ε`, every componentwise map, and `Loc_{X,Y}` (`LocO2_mem_noX`); `Loc_{X,Y}` maps
  everything with `F_{ab} = 0` to `noX i` if `p_i ∈ X ∖ Y` (`LocO2_mem_noX_of_not_mem`; with the
  pointed `loc^a` of `Obs2.Loc.Loc` this fails for `p_i ∉ X`);
* the components of the truncated expectation (`FCO_e`, `FCO_cmp`, `FCO_ab`):
  `F_C(A,B)_i = F_C(A_∅, B_i) + F_C(A_i, B_∅)`,
  `F_C(A,B)_{ab} = F_C(A_∅,B_{ab}) + F_C(τA_a, B_b) + s F_C(τA_b, B_a) + F_C(A_{ab}, B_∅)`;
* **finite range** (`FCO_mem_noX_far`): `F_C(A, B) ∈ noX i` if `A ∈ noX i`, `B_{ab} = 0`, and `C`
  vanishes between the supports of `A_∅`, `A_{¬i}` and that of `B_i`;
* the point support of the localised components: `cmp i (Loc_{X,Y} F) ∈ 𝒩({p_i})`
  (`cmp_LocO2_mem`, for the pointed `loc^a` as well);
* **the membership principle with sources** (`OGMem.gKnextO_mem`, `KoutO_mem`): copies of
  `Step2.GMem.gKnext_mem` and `Step2.Kout_mem` for `OE`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 LocObs FRD

/-! ### The subalgebras without `σ_i` -/

section Sub

variable {c : Obs.Case} {Λ : Type*} [DecidableEq Λ]

/-- The `σ_a` (`i = true`) resp. `σ_b` (`i = false`) component. -/
def cmp (i : Bool) (F : SA c Λ) : Grassmann.N Λ := if i then F.a else F.b

@[simp] theorem cmp_true (F : SA c Λ) : cmp true F = F.a := rfl
@[simp] theorem cmp_false (F : SA c Λ) : cmp false F = F.b := rfl

theorem cmp_add (i : Bool) (F G : SA c Λ) : cmp i (F + G) = cmp i F + cmp i G := by
  cases i <;> rfl

theorem cmp_sub (i : Bool) (F G : SA c Λ) : cmp i (F - G) = cmp i F - cmp i G := by
  cases i <;> rfl

theorem cmp_smul (i : Bool) (r : ℂ) (F : SA c Λ) : cmp i (r • F) = r • cmp i F := by
  cases i <;> rfl

theorem cmp_mul (i : Bool) (F G : SA c Λ) :
    cmp i (F * G) = c.tau F.e * cmp i G + cmp i F * G.e := by
  cases i <;> rfl

theorem cmp_algebraMap (i : Bool) (r : ℂ) : cmp i (algebraMap ℂ (SA c Λ) r) = 0 := by
  cases i <;> simp

theorem cmp_zero (i : Bool) : cmp i (0 : SA c Λ) = 0 := by cases i <;> rfl

theorem cmp_sum (i : Bool) {ι : Type*} (s : Finset ι) (F : ι → SA c Λ) :
    cmp i (∑ k ∈ s, F k) = ∑ k ∈ s, cmp i (F k) := by
  cases i
  · exact sum_b s F
  · exact sum_a s F

variable (c Λ) in
/-- **No `σ_i`**: `F_i = 0` and `F_{ab} = 0`. -/
def noXS (i : Bool) : Subalgebra ℂ (SA c Λ) where
  carrier := {F | cmp i F = 0 ∧ F.ab = 0}
  mul_mem' := by
    rintro F G ⟨h1, h2⟩ ⟨h3, h4⟩
    refine ⟨by show cmp i (F * G) = 0; rw [cmp_mul, h1, h3]; simp, ?_⟩
    show (F * G).ab = 0
    rw [mul_ab, h2, h4]
    cases i
    · simp only [cmp_false] at h1 h3
      rw [h1, h3]; simp
    · simp only [cmp_true] at h1 h3
      rw [h1, h3]; simp
  add_mem' := by
    rintro F G ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨by show cmp i (F + G) = 0; rw [cmp_add, h1, h3, add_zero],
      by show (F + G).ab = 0; rw [add_ab, h2, h4, add_zero]⟩
  algebraMap_mem' r := ⟨cmp_algebraMap i r, by simp⟩

variable (c Λ) in
/-- `noXS` on even elements. -/
def noX (i : Bool) : Subalgebra ℂ (OE c Λ) := (noXS c Λ i).comap (OEv c Λ).val

theorem mem_noX {i : Bool} {F : OE c Λ} :
    F ∈ noX c Λ i ↔ cmp i (F : SA c Λ) = 0 ∧ (F : SA c Λ).ab = 0 := Iff.rfl

theorem noX_cmp {i : Bool} {F : OE c Λ} (h : F ∈ noX c Λ i) : cmp i (F : SA c Λ) = 0 :=
  (mem_noX.1 h).1

theorem noX_ab {i : Bool} {F : OE c Λ} (h : F ∈ noX c Λ i) : (F : SA c Λ).ab = 0 :=
  (mem_noX.1 h).2

theorem emb_mem_noX (i : Bool) (x : EvR Λ) : (emb x : OE c Λ) ∈ noX c Λ i :=
  mem_noX.2 ⟨by cases i <;> rfl, rfl⟩

/-- A componentwise map with `f 0 = 0` preserves `noX`. -/
theorem mem_noX_of_comp {Λ' : Type*} [DecidableEq Λ'] {i : Bool} {F : OE c Λ} {G : OE c Λ'}
    (f : Grassmann.N Λ → Grassmann.N Λ') (hf : f 0 = 0)
    (hc : cmp i (G : SA c Λ') = f (cmp i (F : SA c Λ)))
    (hab : (G : SA c Λ').ab = f (F : SA c Λ).ab) (hF : F ∈ noX c Λ i) : G ∈ noX c Λ' i :=
  mem_noX.2 ⟨by rw [hc, noX_cmp hF, hf], by rw [hab, noX_ab hF, hf]⟩

theorem oexp_mem {S : Subalgebra ℂ (OE c Λ)} {F : OE c Λ} (h : F ∈ S) : oexp F ∈ S := by
  unfold oexp IsNilpotent.exp
  refine S.sum_mem fun k _ => ?_
  rw [OE.qsmul_eq]
  exact S.smul_mem (S.pow_mem h k) _

theorem expU_mem {S : Subalgebra ℂ (OE c Λ)} (x : ℂ) {F : OE c Λ} (h : F ∈ S) :
    expU x F ∈ S :=
  S.smul_mem (oexp_mem h) _

theorem coe_πobs' (F : OE c Λ) :
    (πobs F : SA c Λ) = ⟨0, (F : SA c Λ).a, (F : SA c Λ).b, (F : SA c Λ).ab⟩ := by
  rw [coe_πobs, piobs_apply]

theorem cmp_πobs (i : Bool) (F : OE c Λ) : cmp i (πobs F : SA c Λ) = cmp i (F : SA c Λ) := by
  rw [coe_πobs']; cases i <;> rfl

theorem ab_πobs (F : OE c Λ) : (πobs F : SA c Λ).ab = (F : SA c Λ).ab := by
  rw [coe_πobs']

theorem πobs_mem_noX {i : Bool} {F : OE c Λ} (h : F ∈ noX c Λ i) : πobs F ∈ noX c Λ i :=
  mem_noX.2 ⟨by rw [cmp_πobs]; exact noX_cmp h, by rw [ab_πobs]; exact noX_ab h⟩

theorem epsO_mem_noX {i : Bool} {F : OE c Λ} (h : F ∈ noX c Λ i) : epsO F ∈ noX c Λ i :=
  mem_noX_of_comp (F := F) (G := epsO F) (fun x => algebraMap ℂ (Grassmann.N Λ) (ε x)) (by simp)
    (by cases i <;> rfl) rfl h

theorem thetaO_mem_noX {i : Bool} {F : OE c Λ} (h : F ∈ noX c Λ i) :
    thetaO F ∈ noX c (Λ ⊕ Λ) i :=
  mem_noX_of_comp (F := F) (G := thetaO F) theta (map_zero _) (by cases i <;> rfl) rfl h

theorem inclO_mem_noX {i : Bool} {F : OE c Λ} (h : F ∈ noX c Λ i) :
    inclO F ∈ noX c (Λ ⊕ Λ) i :=
  mem_noX_of_comp (F := F) (G := inclO F) incl (map_zero _) (by cases i <;> rfl) rfl h

variable [Fintype Λ]

theorem ECCO_mem_noX (C : Matrix Λ Λ ℂ) {i : Bool} {F : OE c (Λ ⊕ Λ)}
    (h : F ∈ noX c (Λ ⊕ Λ) i) : ECCO C F ∈ noX c Λ i :=
  mem_noX_of_comp (F := F) (G := ECCO C F) (ECC C) (map_zero _) (by cases i <;> rfl) rfl h

theorem expO_mem_noX (C : Matrix Λ Λ ℂ) {i : Bool} {F : OE c Λ} (h : F ∈ noX c Λ i) :
    expO C F ∈ noX c Λ i :=
  mem_noX_of_comp (F := F) (G := expO C F) (expLC C) (map_zero _) (by cases i <;> rfl) rfl h

theorem EthO_mem_noX (C : Matrix Λ Λ ℂ) {i : Bool} {F : OE c Λ} (h : F ∈ noX c Λ i) :
    EthO C F ∈ noX c Λ i :=
  ECCO_mem_noX C (thetaO_mem_noX h)

theorem FCO_mem_noX (C : Matrix Λ Λ ℂ) {i : Bool} {A B : OE c Λ} (hA : A ∈ noX c Λ i)
    (hB : B ∈ noX c Λ i) : FCO C A B ∈ noX c Λ i :=
  sub_mem (expO_mem_noX C (mul_mem (expO_mem_noX (-C) hA) (expO_mem_noX (-C) hB)))
    (mul_mem hA hB)

/-! ### Components of `F_C` -/

theorem tau_expLC (C : Matrix Λ Λ ℂ) (x : Grassmann.N Λ) :
    c.tau (expLC C x) = expLC C (c.tau x) := by
  cases c
  · exact (expLC_inv' C x).symm
  · rfl

theorem FC_zero_left (C : Matrix Λ Λ ℂ) (x : Grassmann.N Λ) : FC C 0 x = 0 := by
  simp [FC]

theorem FC_zero_right (C : Matrix Λ Λ ℂ) (x : Grassmann.N Λ) : FC C x 0 = 0 := by
  simp [FC]

theorem coe_FCO (C : Matrix Λ Λ ℂ) (A B : OE c Λ) :
    (FCO C A B : SA c Λ) =
      expS C (expS (-C) (A : SA c Λ) * expS (-C) (B : SA c Λ)) - (A : SA c Λ) * (B : SA c Λ) :=
  rfl

theorem FCO_e (C : Matrix Λ Λ ℂ) (A B : OE c Λ) :
    (FCO C A B : SA c Λ).e = FC C (A : SA c Λ).e (B : SA c Λ).e := by
  rw [coe_FCO]; rfl

theorem FCO_cmp (C : Matrix Λ Λ ℂ) (i : Bool) (A B : OE c Λ) :
    cmp i (FCO C A B : SA c Λ) =
      FC C (c.tau (A : SA c Λ).e) (cmp i (B : SA c Λ)) + FC C (cmp i (A : SA c Λ)) (B : SA c Λ).e := by
  rw [coe_FCO]
  cases i
  · simp only [cmp_false, sub_b, mul_b, expS_b, expS_e, tau_expLC, FC, map_add]
    abel
  · simp only [cmp_true, sub_a, mul_a, expS_a, expS_e, tau_expLC, FC, map_add]
    abel

theorem FCO_ab (C : Matrix Λ Λ ℂ) (A B : OE c Λ) :
    (FCO C A B : SA c Λ).ab = FC C (A : SA c Λ).e (B : SA c Λ).ab +
      FC C (c.tau (A : SA c Λ).a) (B : SA c Λ).b + c.s • FC C (c.tau (A : SA c Λ).b) (B : SA c Λ).a +
      FC C (A : SA c Λ).ab (B : SA c Λ).e := by
  rw [coe_FCO]
  simp only [sub_ab, mul_ab, expS_ab, expS_e, expS_a, expS_b, tau_expLC, FC, map_add, map_smul,
    smul_sub]
  abel

/-- **Finite range**: `F_C(A, B)` has no `σ_i` if `A` has none, `B_{ab} = 0`, and `C` vanishes
between the supports of `A_∅`, `A_{¬i}` and the support of `B_i`. -/
theorem FCO_mem_noX_far (C : Matrix Λ Λ ℂ) {i : Bool} {A B : OE c Λ}
    (hA : A ∈ noX c Λ i) (hBab : (B : SA c Λ).ab = 0) {S S' T : Set Λ}
    (hST : Disjoint S T) (hCST : ∀ x ∈ S, ∀ y ∈ T, C x y = 0 ∧ C y x = 0)
    (hS'T : Disjoint S' T) (hCS'T : ∀ x ∈ S', ∀ y ∈ T, C x y = 0 ∧ C y x = 0)
    (hAe : (A : SA c Λ).e ∈ NX S) (hA' : cmp (!i) (A : SA c Λ) ∈ NX S')
    (hB : cmp i (B : SA c Λ) ∈ NX T) : FCO C A B ∈ noX c Λ i := by
  have hτe : c.tau (A : SA c Λ).e = (A : SA c Λ).e := Case.tau_of_even c A.par_e
  refine mem_noX.2 ⟨?_, ?_⟩
  · rw [FCO_cmp, noX_cmp hA, FC_zero_left, add_zero, hτe]
    exact FC_eq_zero_of_disjoint C hST hCST hAe hB
  · rw [FCO_ab, noX_ab hA, hBab, FC_zero_right, FC_zero_left, zero_add, add_zero]
    cases i
    · have h0 : (A : SA c Λ).b = 0 := noX_cmp hA
      have hτ : c.tau (A : SA c Λ).a = c.s • (A : SA c Λ).a := Case.tau_of_par c A.par_a
      have hA'' : c.s • (A : SA c Λ).a ∈ NX S' := Subalgebra.smul_mem _ hA' c.s
      have hB' : (B : SA c Λ).b ∈ NX T := hB
      rw [h0, map_zero, FC_zero_left, smul_zero, add_zero, hτ]
      exact FC_eq_zero_of_disjoint C hS'T hCS'T hA'' hB'
    · have h0 : (A : SA c Λ).a = 0 := noX_cmp hA
      have hτ : c.tau (A : SA c Λ).b = c.s • (A : SA c Λ).b := Case.tau_of_par c A.par_b
      have hA'' : c.s • (A : SA c Λ).b ∈ NX S' := Subalgebra.smul_mem _ hA' c.s
      have hB' : (B : SA c Λ).a ∈ NX T := hB
      rw [h0, map_zero, FC_zero_left, zero_add, hτ, FC_eq_zero_of_disjoint C hS'T hCS'T hA'' hB',
        smul_zero]

end Sub

/-! ### The localisation -/

section LocSupp

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

/-- The source point `p_i` (`a` for `i = true`, `b` for `i = false`). -/
def ObsPts.pt (P : ObsPts d L N) (i : Bool) : Lam d L N := if i then P.a else P.b

@[simp] theorem ObsPts.pt_true (P : ObsPts d L N) : P.pt true = P.a := rfl
@[simp] theorem ObsPts.pt_false (P : ObsPts d L N) : P.pt false = P.b := rfl

theorem locGen_single_eq_zero {a : Lam d L N} {X Y : Finset (Lam d L N)} (ha : a ∉ Y)
    (f : Lam d L N → Alg d L N) (r : ℂ) : locGen {a} X Y f r = 0 := by
  have : Y ∩ {a} = ∅ := by
    ext z; simp only [mem_inter, mem_singleton, Finset.notMem_empty, iff_false, not_and]
    rintro hz rfl; exact ha hz
  simp [locGen, this]

theorem locGen_single_mem {a : Lam d L N} (X Y : Finset (Lam d L N)) {f : Lam d L N → Alg d L N}
    (hf : f a ∈ NX ({a} : Set (Lam d L N))) (r : ℂ) :
    locGen {a} X Y f r ∈ NX ({a} : Set (Lam d L N)) := by
  refine Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun z hz => ?_) _
  rw [mem_singleton.1 (mem_inter.1 hz).2]; exact hf

theorem pbp_mem_NX (a : Lam d L N) : pbp a ∈ NX ({a} : Set (Lam d L N)) :=
  mul_mem (ψ_mem_NX (by simp)) (ψ_mem_NX (by simp))

theorem locA_eq_zero (a : Lam d L N) {X Y : Finset (Lam d L N)} (ha : a ∉ Y) (F : Alg d L N) :
    locA c.toObs a X Y F = 0 := by
  cases c
  · exact locGen_single_eq_zero ha _ _
  · show locEven {a} X Y F = 0
    rw [locEven, locGen_single_eq_zero ha, locGen_single_eq_zero ha, add_zero]

theorem locB_eq_zero (b : Lam d L N) {X Y : Finset (Lam d L N)} (hb : b ∉ Y) (F : Alg d L N) :
    locB c.toObs b X Y F = 0 := by
  cases c
  · exact locGen_single_eq_zero hb _ _
  · show locEven {b} X Y F = 0
    rw [locEven, locGen_single_eq_zero hb, locGen_single_eq_zero hb, add_zero]

theorem locA_mem (a : Lam d L N) (X Y : Finset (Lam d L N)) (F : Alg d L N) :
    locA c.toObs a X Y F ∈ NX ({a} : Set (Lam d L N)) := by
  cases c
  · exact locGen_single_mem X Y (ψ_mem_NX (by simp)) _
  · exact add_mem (locGen_single_mem X Y (one_mem _) _) (locGen_single_mem X Y (pbp_mem_NX a) _)

theorem locB_mem (b : Lam d L N) (X Y : Finset (Lam d L N)) (F : Alg d L N) :
    locB c.toObs b X Y F ∈ NX ({b} : Set (Lam d L N)) := by
  cases c
  · exact locGen_single_mem X Y (ψ_mem_NX (by simp)) _
  · exact add_mem (locGen_single_mem X Y (one_mem _) _) (locGen_single_mem X Y (pbp_mem_NX b) _)

theorem locAp_mem (a : Lam d L N) (X Y : Finset (Lam d L N)) (F : Alg d L N) :
    locAp c a X Y F ∈ NX ({a} : Set (Lam d L N)) := by
  unfold locAp; split_ifs
  · exact locA_mem _ _ _ _
  · exact Subalgebra.smul_mem _ (locA_mem _ _ _ _) _

theorem locBp_mem (b : Lam d L N) (X Y : Finset (Lam d L N)) (F : Alg d L N) :
    locBp c b X Y F ∈ NX ({b} : Set (Lam d L N)) := by
  unfold locBp; split_ifs
  · exact locB_mem _ _ _ _
  · exact Subalgebra.smul_mem _ (locB_mem _ _ _ _) _

theorem cmp_LocO2 (P : ObsPts d L N) (X Y : Finset (Lam d L N)) (i : Bool)
    (F : OE c (Lam d L N)) :
    cmp i (LocO2 P X Y F : SA c (Lam d L N)) =
      if i then locAp c P.a X Y (F : SA c (Lam d L N)).a
      else locBp c P.b X Y (F : SA c (Lam d L N)).b := by
  cases i <;> rfl

theorem LocO2_ab (P : ObsPts d L N) (X Y : Finset (Lam d L N)) (F : OE c (Lam d L N)) :
    (LocO2 P X Y F : SA c (Lam d L N)).ab = locABtXY P X Y (F : SA c (Lam d L N)).ab := rfl

/-- **Point support of the localised components**: `(Loc_{X,Y} F)_i ∈ 𝒩({p_i})`. -/
theorem cmp_LocO2_mem (P : ObsPts d L N) (X Y : Finset (Lam d L N)) (i : Bool)
    (F : OE c (Lam d L N)) :
    cmp i (LocO2 P X Y F : SA c (Lam d L N)) ∈ NX ({P.pt i} : Set (Lam d L N)) := by
  rw [cmp_LocO2]
  cases i
  · exact locBp_mem _ _ _ _
  · exact locAp_mem _ _ _ _

theorem LocO2_ab_eq_zero (P : ObsPts d L N) (X Y : Finset (Lam d L N)) {F : OE c (Lam d L N)}
    (hF : (F : SA c (Lam d L N)).ab = 0) : (LocO2 P X Y F : SA c (Lam d L N)).ab = 0 := by
  rw [LocO2_ab, hF, locABtXY_zero]

theorem LocO2_mem_noX (P : ObsPts d L N) (X Y : Finset (Lam d L N)) {i : Bool}
    {F : OE c (Lam d L N)} (hF : F ∈ noX c (Lam d L N) i) :
    LocO2 P X Y F ∈ noX c (Lam d L N) i := by
  refine mem_noX.2 ⟨?_, LocO2_ab_eq_zero P X Y (noX_ab hF)⟩
  have h0 := noX_cmp hF
  rw [cmp_LocO2]
  cases i
  · simp only [cmp_false] at h0
    simp only [Bool.false_eq_true, if_false, h0]
    exact locBp_zero P.b X Y
  · simp only [cmp_true] at h0
    simp only [if_true, h0]
    exact locAp_zero P.a X Y

end LocSupp

/-! ### The membership principle with sources -/

section OGMem

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

/-- The hypotheses of the membership principle for `gKnextO`. -/
structure OGMem (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (Ib Ip : OFam c d L N)
    (K : OAct c d L N) (J : (Fin d → ℕ) → Finset (Lam d L N) → OE c (Lam d L N))
    (U : Finset (Lam d L N)) (S : Subalgebra ℂ (OE c (Lam d L N)))
    (S2 : Subalgebra ℂ (OE c (Lam d L N ⊕ Lam d L N))) : Prop where
  hθ : ∀ F ∈ S, thetaO F ∈ S2
  hι : ∀ F ∈ S, inclO F ∈ S2
  hE : ∀ F ∈ S2, ECCO C F ∈ S
  hK : ∀ Y, IsConn j Y → Y ⊆ U → K Y ∈ S
  hJ : ∀ (b : Fin d → ℕ) (X : Finset (Lam d L N)), b ∈ blockIdx (L := L) (N := N) j →
    blockSet j b ⊆ U → J b X ∈ S
  hIb : ∀ b : Fin d → ℕ, b ∈ blockIdx (L := L) (N := N) j → blockSet j b ⊆ U → Ib b ∈ S
  hIp : ∀ b : Fin d → ℕ, b ∈ blockIdx (L := L) (N := N) j → blockSet j b ⊆ U → Ip b ∈ S

namespace OGMem

variable {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℂ} {Ib Ip : OFam c d L N}
  {K : OAct c d L N} {J : (Fin d → ℕ) → Finset (Lam d L N) → OE c (Lam d L N)}
  {U : Finset (Lam d L N)} {S : Subalgebra ℂ (OE c (Lam d L N))}
  {S2 : Subalgebra ℂ (OE c (Lam d L N ⊕ Lam d L N))}
  (h : OGMem j C Ib Ip K J U S S2)
include h

theorem KextO_mem {W : Finset (Lam d L N)} (hW : IsPolymer j W) (hWU : W ⊆ U) :
    KextO j K W ∈ S :=
  prod_mem fun Y hY => h.hK Y (isConn_of_mem_comp hW hY) ((subset_of_mem_comp hY).trans hWU)

theorem bpowO_mem (hU : IsPolymer j U) {X : Finset (Lam d L N)} (hX : X ⊆ U) :
    bpowO j Ip X ∈ S :=
  prod_mem fun b hb => h.hIp b (mem_blockIdx_of_mem_blocks hb)
    (blockSet_subset hU (blocks_mono hX hb))

theorem gdIPowO_mem (hU : IsPolymer j U) {X : Finset (Lam d L N)} (hX : X ⊆ U) :
    gdIPowO j Ib Ip X ∈ S2 :=
  prod_mem fun b hb => sub_mem (h.hθ _ (h.hIb b (mem_blockIdx_of_mem_blocks hb)
    (blockSet_subset hU (blocks_mono hX hb))))
    (h.hι _ (h.hIp b (mem_blockIdx_of_mem_blocks hb) (blockSet_subset hU (blocks_mono hX hb))))

theorem gKtilO_mem (hU : IsPolymer j U) {W : Finset (Lam d L N)} (hW : IsPolymer j W)
    (hWU : W ⊆ U) : gKtilO j Ib Ip K W ∈ S2 :=
  Subalgebra.sum_mem _ fun Y hY => mul_mem
    (h.hθ _ (h.KextO_mem (IsPolymer.sdiff hW (mem_Pj.1 hY).2) (sdiff_subset.trans hWU)))
    (h.gdIPowO_mem hU ((mem_Pj.1 hY).1.trans hWU))

theorem gKchkO_mem (hU : IsPolymer j U) {X : Finset (Lam d L N)} (hX : IsPolymer j X)
    (hXU : X ⊆ U) : gKchkO j Ib Ip K J X ∈ S2 :=
  prod_mem fun W hW => sub_mem (h.gKtilO_mem hU (isPolymer_of_mem_comp hX hW)
    ((subset_of_mem_comp hW).trans hXU)) (Subalgebra.sum_mem _ fun b hb =>
      h.hθ _ (h.hJ b W (mem_blockIdx_of_mem_blocks hb) (blockSet_subset hU (blocks_mono
        ((subset_of_mem_comp hW).trans hXU) hb))))

/-- **The membership principle with sources**: `K_{j+1}(U) ∈ S`. -/
theorem gKnextO_mem (hU : IsPolymer (j + 1) U) : gKnextO j C Ib Ip K J U ∈ S := by
  refine Subalgebra.sum_mem _ fun g hg => ?_
  obtain ⟨h1, h2, -, h4⟩ := Gset_facts hg
  have hUj := IsPolymer.of_succ hU
  have hin : gKchkO j Ib Ip K J g.2 * ∏ p ∈ g.1, thetaO (J p.1 p.2) ∈ S2 :=
    mul_mem (h.gKchkO_mem hUj h1 h2)
      (prod_mem fun p hp => h.hθ _ (h.hJ p.1 p.2 (mem_pairsU.1 (h4 p hp).1).1
        (h4 p hp).2.2.1))
  exact mul_mem (h.bpowO_mem hUj sdiff_subset) (h.hE _ hin)

end OGMem

/-- **Membership principle for `K_out` with sources.** -/
theorem KoutO_mem {k : ℕ} {I : OFam c d L N} {M : OAct c d L N}
    {J : (Fin d → ℕ) → Finset (Lam d L N) → OE c (Lam d L N)} {W : Finset (Lam d L N)}
    {S : Subalgebra ℂ (OE c (Lam d L N))}
    (hI : ∀ X, IsPolymer k X → X ⊆ W → bpowO k I X ∈ S)
    (hM : ∀ Y, IsConn k Y → Y ⊆ W → M Y ∈ S)
    (hJ : ∀ p ∈ pairsU (L := L) (N := N) k, p.2 ⊆ W → J p.1 p.2 ∈ S) :
    KoutO k I M J W ∈ S := by
  refine Subalgebra.sum_mem _ fun g hg => ?_
  obtain ⟨f2, f3, f4⟩ := G0W_facts hg
  obtain ⟨h1, h2, -, -, -⟩ := (mem_G0 k).1 (mem_filter.1 hg).1
  have hW : IsPolymer k W := by
    rw [← (mem_filter.1 hg).2]; exact IsPolymer.union h1 (isPolymer_Bbox k _)
  refine mul_mem (hI _ (IsPolymer.sdiff hW (IsPolymer.union h1 (isPolymer_Xcal h2))) sdiff_subset)
    (mul_mem (prod_mem fun Y hY => hM Y (isConn_of_mem_comp h1 hY)
      ((subset_of_mem_comp hY).trans f2)) (prod_mem fun p hp => ?_))
  have hp2 := (mem_pairsU.1 (h2 hp)).2.1
  exact mul_mem (hI _ hp2.1 (f4 p hp).2) (hJ p (h2 hp) (f4 p hp).2)

end OGMem


/-! ### The components of the sharp splitting (`SCorO`, `SFO`) -/

section Sharp

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}
  (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V : OFam c d L N)

theorem πobs_e' {Λ : Type*} [DecidableEq Λ] (F : OE c Λ) : (πobs F : SA c Λ).e = 0 := by
  rw [coe_πobs, piobs_apply]

theorem πobs_ab' {Λ : Type*} [DecidableEq Λ] (F : OE c Λ) :
    (πobs F : SA c Λ).ab = (F : SA c Λ).ab := by
  rw [coe_πobs, piobs_apply]

theorem πobs_cmp' {Λ : Type*} [DecidableEq Λ] (i : Bool) (F : OE c Λ) :
    cmp i (πobs F : SA c Λ) = cmp i (F : SA c Λ) := by
  rw [coe_πobs, piobs_apply]; cases i <;> rfl

theorem SCorO_e (b : Fin d → ℕ) : (SCorO j C V b : SA c (Lam d L N)).e = 0 := by
  show (1 / 2 : ℂ) • ((FCO C (πobs (VprO C V b)) (VprLO j C V) : SA c (Lam d L N)).e -
    (FCO C (VprO C V b) (πobs (VprLO j C V)) : SA c (Lam d L N)).e) = 0
  rw [FCO_e, FCO_e, πobs_e', πobs_e', FC_zero_left, FC_zero_right, sub_zero, smul_zero]

/-- `SCorO(B)_i = ½(F_C(V'_{B,i}, V'(Λ)_∅) − F_C(V'_{B,∅}, V'(Λ)_i))`. -/
theorem SCorO_cmp (i : Bool) (b : Fin d → ℕ) :
    cmp i (SCorO j C V b : SA c (Lam d L N)) =
      (1 / 2 : ℂ) • (FC C (cmp i (VprO C V b : SA c (Lam d L N))) (VprLO j C V : SA c (Lam d L N)).e -
        FC C (c.tau (VprO C V b : SA c (Lam d L N)).e) (cmp i (VprLO j C V : SA c (Lam d L N)))) := by
  rw [SCorO, Subalgebra.coe_smul, cmp_smul, Subalgebra.coe_sub, cmp_sub, FCO_cmp, FCO_cmp,
    πobs_e', πobs_e', πobs_cmp', πobs_cmp', map_zero, FC_zero_left, FC_zero_right, zero_add,
    add_zero]

/-- `SCorO(B)_{ab} = ½(F_C(V'_{B,ab}, V'(Λ)_∅) − F_C(V'_{B,∅}, V'(Λ)_{ab}))`. -/
theorem SCorO_ab (b : Fin d → ℕ) :
    (SCorO j C V b : SA c (Lam d L N)).ab =
      (1 / 2 : ℂ) • (FC C (VprO C V b : SA c (Lam d L N)).ab (VprLO j C V : SA c (Lam d L N)).e -
        FC C (VprO C V b : SA c (Lam d L N)).e (VprLO j C V : SA c (Lam d L N)).ab) := by
  show (1 / 2 : ℂ) • ((FCO C (πobs (VprO C V b)) (VprLO j C V) : SA c (Lam d L N)).ab -
    (FCO C (VprO C V b) (πobs (VprLO j C V)) : SA c (Lam d L N)).ab) = _
  rw [FCO_ab, FCO_ab, πobs_e', πobs_e', πobs_ab', πobs_ab', FC_zero_left, FC_zero_right]
  have ha : ∀ F : OE c (Lam d L N), (πobs F : SA c (Lam d L N)).a = (F : SA c (Lam d L N)).a :=
    fun F => πobs_cmp' true F
  have hb : ∀ F : OE c (Lam d L N), (πobs F : SA c (Lam d L N)).b = (F : SA c (Lam d L N)).b :=
    fun F => πobs_cmp' false F
  rw [ha, ha, hb, hb]
  congr 1
  abel

/-- **The `σ_i` component of the sharp second-order part**: `S^{(2)}(B)_i = F_C(V'_{B,i}, V'(Λ)_∅)`. -/
theorem SFO_cmp (i : Bool) (b : Fin d → ℕ) :
    cmp i (SFO j C V b : SA c (Lam d L N)) =
      FC C (cmp i (VprO C V b : SA c (Lam d L N))) (VprLO j C V : SA c (Lam d L N)).e := by
  rw [SFO, Subalgebra.coe_add, cmp_add, SCorO_cmp, Subalgebra.coe_smul, cmp_smul, FCO_cmp, smul_sub,
    ← add_sub_assoc, smul_add]
  set x := FC C (c.tau (VprO C V b : SA c (Lam d L N)).e) (cmp i (VprLO j C V : SA c (Lam d L N)))
  set y := FC C (cmp i (VprO C V b : SA c (Lam d L N))) (VprLO j C V : SA c (Lam d L N)).e
  rw [show (1 / 2 : ℂ) • x + (1 / 2 : ℂ) • y + (1 / 2 : ℂ) • y - (1 / 2 : ℂ) • x =
    ((1 / 2 : ℂ) + 1 / 2) • y by rw [add_smul]; abel]
  norm_num

theorem SFO_e (b : Fin d → ℕ) :
    (SFO j C V b : SA c (Lam d L N)).e =
      (1 / 2 : ℂ) • FC C (VprO C V b : SA c (Lam d L N)).e (VprLO j C V : SA c (Lam d L N)).e := by
  show _ + (SCorO j C V b : SA c (Lam d L N)).e = _
  rw [SCorO_e, add_zero]
  show (1 / 2 : ℂ) • (FCO C (VprO C V b) (VprLO j C V) : SA c (Lam d L N)).e = _
  rw [FCO_e]

/-- `∑_B SCorO(B) = 0` (symmetry of `F_C` on even elements). -/
theorem sum_SCorO : ∑ b ∈ blockIdx (L := L) (N := N) j, SCorO j C V b = 0 := by
  simp only [SCorO, ← smul_sum, sum_sub_distrib, ← FCO_sum_left, ← map_sum]
  rw [show ∑ b ∈ blockIdx (L := L) (N := N) j, VprO C V b = VprLO j C V from rfl,
    FCO_comm C (πobs _), sub_self, smul_zero]

end Sharp

end

end Obs2
