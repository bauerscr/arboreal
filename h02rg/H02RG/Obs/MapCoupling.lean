import Obs.MapLoc

/-!
# `P^obs` and the observable coupling constants `(u^obs + V^obs)_{j+1}` (Definition `def:V+obs`)

For a covariance `C = C_{j+1}`, coupling constants `Vo` of `V^obs_j` (only the `V` part
`Coup.toV` is used: `u^obs_j` is not an input of the map) and an activity `K` (with values in
the algebra with observables):

* `Vhat C j Vo K a b p = V̂^obs_j(B) = V^obs_j(B) - Q^obs(B)` (`B = blockSet j p`, split
  evaluation);
* `PobsBB … p p' = P^obs(B, B') = ½ 𝔼[θ V̂(B); θ V̂(B')]` and `Pobs … p = P^obs(B) =
  ∑_{B' ∈ 𝓑_j} P^obs(B, B')` (`e:Pobs-def`);
* `RHS … p = 𝔼_{C} θ (V^obs_j(B) - Q^obs(B)) - P^obs(B)`, the right side of `E:Qobs`;
* `nextObs C j Vo K a b` = the next coupling constants `(u^obs + V^obs)_{j+1}`: the free flow
  (`Coup.next`, Lemma `lem:Vobs-flow-free`) of `V_j - Q` (`Coup.sub (Coup.toV Vo) (Qcoup …)`),
  read off at the level of `Λ`.

## Results
* `sum_RHS`: at the level of `Λ`, `∑_B RHS(B) = freeStep C (V̂(Λ))` with
  `V̂(Λ) = ∑_B V̂(B)`: `(u + V)^obs_{j+1}(Λ) = 𝔼θ V̂(Λ) - ½ 𝔼[θV̂(Λ); θV̂(Λ)]` (no hypotheses).
* `RHS_eq` (**Definition `def:V+obs`**, the right side is of the form `(u + V)^obs(B)`): if
  `a ≠ b` and `C(a,b) = C(b,a)`, then for every block,
  `RHS(B) = (u + V)^obs_{j+1}(B)` for the coupling constants `nextObs` (split evaluation); and
  `sum_RHS_eq`: at the level of `Λ`, `∑_B RHS(B) = (u + V)^obs_{j+1}(Λ)` (evaluation
  `e:VobsX`).  The two readings are consistent (`splitO_univ`, additivity).
* `Pobs_isAB`: `P^obs` has only an `ab` component (it is quadratic in `V̂`, `σ² = 0`).
* `PobsBB_eq` (**Lemma `lem:Pjj+1`**): `P^obs(B,B') = ½ 𝔼[θV̂(B) θV̂(B')] - ½ Ṽ(B) Ṽ(B')`
  with `Ṽ = RHS = (u^obs + V^obs)_{j+1}`.

**Deviations.**  The coupling constants are the split ones of `Obs.Coupling` (`r` split into
`r_a, r_b`, `q` into `q_a, q_b`; the paper's symmetric form is not preserved by `Loc^obs` on sets
containing only one of `a, b`).  With them the per-block form needs neither translation
invariance `C(a,a) = C(b,b)` nor a vanishing condition on `K^{ab}`; `C(a,b) = C(b,a)` is used
for Case (2) as in `freeStep_two` (the hypothesis is stated for both cases).
The sign of the `r C(0,0)` term in `q` is that of `Obs.Free`.
-/

namespace Obs

noncomputable section

open Finset Grassmann SA Loc Step LocObs

/-! ### Generic algebra -/

section Generic

variable {c : Case} {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

theorem ECT_add_left (C : Matrix Λ Λ ℝ) (F G H : OE c Λ) :
    ECT C (F + G) H = ECT C F H + ECT C G H := by
  simp only [ECT, map_add, add_mul]; ring

theorem ECT_sub_left (C : Matrix Λ Λ ℝ) (F G H : OE c Λ) :
    ECT C (F - G) H = ECT C F H - ECT C G H := by
  simp only [ECT, map_sub, sub_mul]; ring

theorem ECT_smul_left (C : Matrix Λ Λ ℝ) (r : ℂ) (F H : OE c Λ) :
    ECT C (r • F) H = r • ECT C F H := by
  simp only [ECT, map_smul, smul_mul_assoc, smul_sub]

theorem ECT_sum_right (C : Matrix Λ Λ ℝ) (F : OE c Λ) {ι : Type*} (s : Finset ι)
    (G : ι → OE c Λ) : ECT C F (∑ i ∈ s, G i) = ∑ i ∈ s, ECT C F (G i) := by
  simp only [ECT, map_sum, mul_sum, sum_sub_distrib]

theorem ECT_sum_left (C : Matrix Λ Λ ℝ) {ι : Type*} (s : Finset ι) (F : ι → OE c Λ)
    (H : OE c Λ) : ECT C (∑ i ∈ s, F i) H = ∑ i ∈ s, ECT C (F i) H := by
  simp only [ECT, map_sum, sum_mul, sum_sub_distrib]

theorem ECT_comm (C : Matrix Λ Λ ℝ) (F G : OE c Λ) : ECT C F G = ECT C G F := by
  simp only [ECT, mul_comm]

/-- An element with vanishing `∅` and `b` components squares to zero. -/
theorem mul_self_eq_zero_of_b {F : OE c Λ} (he : (F : SA c Λ).e = 0) (hb : (F : SA c Λ).b = 0) :
    F * F = 0 := by
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_)
  · rw [OE.mul_e, he, zero_mul]; rfl
  · rw [OE.mul_a, he, zero_mul, mul_zero, add_zero]; rfl
  · rw [OE.mul_b, he, zero_mul, mul_zero, add_zero]; rfl
  · rw [OE.mul_ab, he, hb]; simp

theorem mul_self_eq_zero_of_a {F : OE c Λ} (he : (F : SA c Λ).e = 0) (ha : (F : SA c Λ).a = 0) :
    F * F = 0 := by
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_)
  · rw [OE.mul_e, he, zero_mul]; rfl
  · rw [OE.mul_a, he, zero_mul, mul_zero, add_zero]; rfl
  · rw [OE.mul_b, he, zero_mul, mul_zero, add_zero]; rfl
  · rw [OE.mul_ab, he, ha]; simp

theorem ECT_self_eq_zero_of_b (C : Matrix Λ Λ ℝ) {F : OE c Λ} (he : (F : SA c Λ).e = 0)
    (hb : (F : SA c Λ).b = 0) : ECT C F F = 0 := by
  have h1 : ECO C (thetaO F) * ECO C (thetaO F) = 0 :=
    mul_self_eq_zero_of_b (by simp [he]) (by simp [hb])
  rw [ECT, ← map_mul, mul_self_eq_zero_of_b he hb, map_zero, map_zero, h1, sub_zero]

theorem ECT_self_eq_zero_of_a (C : Matrix Λ Λ ℝ) {F : OE c Λ} (he : (F : SA c Λ).e = 0)
    (ha : (F : SA c Λ).a = 0) : ECT C F F = 0 := by
  have h1 : ECO C (thetaO F) * ECO C (thetaO F) = 0 :=
    mul_self_eq_zero_of_a (by simp [he]) (by simp [ha])
  rw [ECT, ← map_mul, mul_self_eq_zero_of_a he ha, map_zero, map_zero, h1, sub_zero]

/-- `𝔼_C θ V - ½ 𝔼_C[θ V; θ S]`, the per-block map applied to `V = V̂(B)`, `S = V̂(Λ)`. -/
def Rmap (C : Matrix Λ Λ ℝ) (F S : OE c Λ) : OE c Λ :=
  ECO C (thetaO F) - (1 / 2 : ℂ) • ECT C F S

theorem Rmap_add (C : Matrix Λ Λ ℝ) (F G S : OE c Λ) :
    Rmap C (F + G) S = Rmap C F S + Rmap C G S := by
  simp only [Rmap, map_add, ECT_add_left, smul_add]; abel

theorem Rmap_smul (C : Matrix Λ Λ ℝ) (r : ℂ) (F S : OE c Λ) :
    Rmap C (r • F) S = r • Rmap C F S := by
  simp only [Rmap, map_smul, ECT_smul_left, smul_sub, smul_comm r (1 / 2 : ℂ)]

theorem Rmap_sum (C : Matrix Λ Λ ℝ) {ι : Type*} (s : Finset ι) (F : ι → OE c Λ) (S : OE c Λ) :
    Rmap C (∑ i ∈ s, F i) S = ∑ i ∈ s, Rmap C (F i) S := by
  simp only [Rmap, map_sum, ECT_sum_left, smul_sum, sum_sub_distrib]

theorem Rmap_self (C : Matrix Λ Λ ℝ) (S : OE c Λ) : Rmap C S S = freeStep C S := rfl

theorem halfAO_add_halfBO (c : Case) (V : Coup c) (a b : Λ) :
    halfAO c V a b + halfBO c V a b = evalO c V a b univ :=
  Subtype.ext (by rw [coe_evalO]; exact halfA_add_halfB c V a b (mem_univ a) (mem_univ b))

/-- The free flow at the level of `Λ` (`lem:Vobs-flow-free`). -/
theorem freeStep_evalO_univ (C : Matrix Λ Λ ℝ) (V : Coup c) {a b : Λ} (hCs : C a b = C b a) :
    freeStep C (evalO c V a b univ) =
      evalO c (Coup.next c V (C a b) (C a a) (C b b)) a b univ := by
  cases c
  · exact freeStep_one C V (mem_univ a) (mem_univ b)
  · exact freeStep_two C V (mem_univ a) (mem_univ b) hCs

theorem expL_pbp (C : Matrix Λ Λ ℝ) (x : Λ) :
    expL C (psibar x * psi x) = psibar x * psi x + algebraMap ℂ (N Λ) (C x x : ℂ) :=
  expL_psibar_psi C x x

/-- The halves of `𝔼θ(H_a - H_b)`. -/
theorem ECO_thetaO_halfA_sub (C : Matrix Λ Λ ℝ) (V : Coup c) {a b : Λ} (hCs : C a b = C b a) :
    ECO C (thetaO (halfAO c V a b - halfBO c V a b)) =
      halfAO c (Coup.next c V (C a b) (C a a) (C b b)) a b -
        halfBO c (Coup.next c V (C a b) (C a a) (C b b)) a b := by
  have hF := freeStep_evalO_univ C V hCs (a := a) (b := b)
  have hW := bulk_evalO c V a b univ
  have ha : ((freeStep C (evalO c V a b univ) : OE c Λ) : SA c Λ).a =
      ((evalO c (Coup.next c V (C a b) (C a a) (C b b)) a b univ : OE c Λ) : SA c Λ).a := by
    rw [hF]
  have hb : ((freeStep C (evalO c V a b univ) : OE c Λ) : SA c Λ).b =
      ((evalO c (Coup.next c V (C a b) (C a a) (C b b)) a b univ : OE c Λ) : SA c Λ).b := by
    rw [hF]
  rw [freeStep_a C hW, ← halfAO_add_halfBO, ← halfAO_add_halfBO] at ha
  rw [freeStep_b C hW, ← halfAO_add_halfBO, ← halfAO_add_halfBO] at hb
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_)
  · cases c <;> simp [ECS_thetaS, halfA, halfB, expL_zero]
  · have e1 : ((halfAO c V a b - halfBO c V a b : OE c Λ) : SA c Λ).a =
        ((halfAO c V a b + halfBO c V a b : OE c Λ) : SA c Λ).a := by
      cases c <;> simp [halfA, halfB]
    have e2 : ((halfAO c (Coup.next c V (C a b) (C a a) (C b b)) a b -
        halfBO c (Coup.next c V (C a b) (C a a) (C b b)) a b : OE c Λ) : SA c Λ).a =
        ((halfAO c (Coup.next c V (C a b) (C a a) (C b b)) a b +
        halfBO c (Coup.next c V (C a b) (C a a) (C b b)) a b : OE c Λ) : SA c Λ).a := by
      cases c <;> simp [halfA, halfB]
    rw [e2, ← ha, coe_ECO, coe_thetaO, ECS_thetaS, e1]
  · have e1 : ((halfAO c V a b - halfBO c V a b : OE c Λ) : SA c Λ).b =
        -((halfAO c V a b + halfBO c V a b : OE c Λ) : SA c Λ).b := by
      cases c <;> simp [halfA, halfB]
    have e2 : ((halfAO c (Coup.next c V (C a b) (C a a) (C b b)) a b -
        halfBO c (Coup.next c V (C a b) (C a a) (C b b)) a b : OE c Λ) : SA c Λ).b =
        -((halfAO c (Coup.next c V (C a b) (C a a) (C b b)) a b +
        halfBO c (Coup.next c V (C a b) (C a a) (C b b)) a b : OE c Λ) : SA c Λ).b := by
      cases c <;> simp [halfA, halfB]
    rw [e2, ← hb, coe_ECO, coe_thetaO, ECS_thetaS, e1, map_neg]
  · cases c
    · simp only [coe_ECO, coe_thetaO, ECS_thetaS, halfAO, halfBO, Subalgebra.coe_sub,
        sub_ab, halfA, halfB, Coup.next, Coup1.next]
      simp only [map_sub, map_add, map_smul, expL_pbp, Algebra.algebraMap_eq_smul_one,
        expL_eq_self C (Step.Coup.Lop_one' C)]
      module
    · simp only [coe_ECO, coe_thetaO, ECS_thetaS, halfAO, halfBO, Subalgebra.coe_sub,
        sub_ab, halfA, halfB, Coup.next, Coup2.next]
      simp only [map_sub, map_add, map_smul, expL_pbp, Algebra.algebraMap_eq_smul_one,
        expL_eq_self C (Step.Coup.Lop_one' C)]
      module

/-- **The per-block free flow**: `𝔼θ(V̂(Y)) - ½ 𝔼[θV̂(Y); θV̂(Λ)]` is the split evaluation of
the next coupling constants, for every `Y`. -/
theorem Rmap_splitO (C : Matrix Λ Λ ℝ) (V : Coup c) {a b : Λ} (hCs : C a b = C b a)
    (Y : Finset Λ) :
    Rmap C (splitO c V a b Y) (evalO c V a b univ) =
      splitO c (Coup.next c V (C a b) (C a a) (C b b)) a b Y := by
  set HA := halfAO c V a b
  set HB := halfBO c V a b
  set HA' := halfAO c (Coup.next c V (C a b) (C a a) (C b b)) a b
  set HB' := halfBO c (Coup.next c V (C a b) (C a a) (C b b)) a b
  have hS : evalO c V a b univ = HA + HB := (halfAO_add_halfBO c V a b).symm
  have h1 : Rmap C HA (HA + HB) + Rmap C HB (HA + HB) = HA' + HB' := by
    rw [← Rmap_add, Rmap_self, ← hS, freeStep_evalO_univ C V hCs, ← halfAO_add_halfBO]
  have hAA : ECT C HA HA = 0 := ECT_self_eq_zero_of_b C (by cases c <;> rfl) (by cases c <;> rfl)
  have hBB : ECT C HB HB = 0 := ECT_self_eq_zero_of_a C (by cases c <;> rfl) (by cases c <;> rfl)
  have h2 : Rmap C HA (HA + HB) - Rmap C HB (HA + HB) = HA' - HB' := by
    have : ECT C HA (HA + HB) - ECT C HB (HA + HB) = 0 := by
      rw [ECT_comm C HA (HA + HB), ECT_comm C HB (HA + HB), ECT_add_left, ECT_add_left, hAA, hBB,
        ECT_comm C HB HA]
      abel
    rw [Rmap, Rmap, sub_sub_sub_comm, ← smul_sub, this, smul_zero, sub_zero, ← map_sub, ← map_sub,
      ECO_thetaO_halfA_sub C V hCs]
  have key : ∀ x y u v : OE c Λ, x + y = u + v → x - y = u - v → x = u ∧ y = v := by
    intro x y u v e1 e2
    have hx : (2 : ℂ) • x = (2 : ℂ) • u := by
      rw [two_smul, two_smul]
      calc x + x = (x + y) + (x - y) := by abel
        _ = (u + v) + (u - v) := by rw [e1, e2]
        _ = u + u := by abel
    have hx' := smul_right_injective (OE c Λ) (two_ne_zero : (2 : ℂ) ≠ 0) hx
    refine ⟨hx', ?_⟩
    rw [hx'] at e1
    exact add_left_cancel e1
  obtain ⟨hA, hB⟩ := key _ _ _ _ h1 h2
  rw [hS, splitO, splitO, Rmap_add, Rmap_smul, Rmap_smul, hA, hB]

end Generic

/-! ### The observable coupling constants -/

variable {d L N : ℕ} [NeZero L]

section Def

variable {c : Case} (C : Matrix (Lam d L N) (Lam d L N) ℝ) (j : ℕ) (Vo : Coup c)
  (K : Finset (Lam d L N) → OE c (Lam d L N)) (a b : Lam d L N)

/-- `V^obs_j(B)` (split evaluation of the `V` part). -/
def Vobs (p : Fin d → ℕ) : OE c (Lam d L N) := splitO c (Coup.toV c Vo) a b (blockSet j p)

/-- `V̂^obs_j(B) = V^obs_j(B) - Q^obs(B)`. -/
def Vhat (p : Fin d → ℕ) : OE c (Lam d L N) := Vobs j Vo a b p - QobsO a b j K p

/-- `P^obs(B, B') = ½ 𝔼_{C}[θ V̂(B); θ V̂(B')]` (`e:Pobs-def`). -/
def PobsBB (p p' : Fin d → ℕ) : OE c (Lam d L N) :=
  (1 / 2 : ℂ) • ECT C (Vhat j Vo K a b p) (Vhat j Vo K a b p')

/-- `P^obs(B) = ∑_{B' ∈ 𝓑_j} P^obs(B, B')` (`e:Pobs-def`). -/
def Pobs (p : Fin d → ℕ) : OE c (Lam d L N) :=
  ∑ p' ∈ blockIdx (L := L) (N := N) j, PobsBB C j Vo K a b p p'

/-- The right side of `E:Qobs`: `𝔼_{C} θ (V^obs_j(B) - Q^obs(B)) - P^obs(B)`. -/
def RHS (p : Fin d → ℕ) : OE c (Lam d L N) :=
  ECO C (thetaO (Vhat j Vo K a b p)) - Pobs C j Vo K a b p

/-- The coupling constants of `V_j - Q`. -/
def Wcoup : Coup c := Coup.sub c (Coup.toV c Vo) (Qcoup c j K a b)

/-- The next observable coupling constants `(u^obs + V^obs)_{j+1}` (Definition `def:V+obs`),
read off at the level of `Λ`: the free flow of `V_j - Q`. -/
def nextObs : Coup c :=
  Coup.next c (Wcoup j Vo K a b) (C a b) (C a a) (C b b)

/-- `V̂(Λ) = ∑_B V̂(B)`. -/
def VhatL : OE c (Lam d L N) := ∑ p ∈ blockIdx (L := L) (N := N) j, Vhat j Vo K a b p

theorem bulk_Vhat (p : Fin d → ℕ) : bulk (Vhat j Vo K a b p) = 0 := by
  rw [Vhat, map_sub, Vobs, bulk_splitO, QobsO, bulk_πobs, sub_zero]

theorem Pobs_eq (p : Fin d → ℕ) :
    Pobs C j Vo K a b p = (1 / 2 : ℂ) • ECT C (Vhat j Vo K a b p) (VhatL j Vo K a b) := by
  rw [Pobs, VhatL, ECT_sum_right, smul_sum]; rfl

theorem RHS_eq_Rmap (p : Fin d → ℕ) :
    RHS C j Vo K a b p = Rmap C (Vhat j Vo K a b p) (VhatL j Vo K a b) := by
  rw [RHS, Pobs_eq, Rmap]

/-- `P^obs` has only an `ab` component. -/
theorem Pobs_isAB (p : Fin d → ℕ) : IsAB (Pobs C j Vo K a b p) := by
  have h : bulk (VhatL j Vo K a b) = 0 := by
    rw [VhatL, map_sum]; exact sum_eq_zero fun p _ => bulk_Vhat j Vo K a b p
  rw [Pobs_eq]
  exact (isAB_ECT C (bulk_Vhat j Vo K a b p) h).smul _

theorem blocks_univ_biUnion :
    (blockIdx (L := L) (N := N) j).biUnion (blockSet j) = (univ : Finset (Lam d L N)) :=
  biUnion_blocks (isPolymer_univ j)

theorem blockSet_pairwiseDisjoint :
    ((blockIdx (L := L) (N := N) j : Finset (Fin d → ℕ)) : Set (Fin d → ℕ)).PairwiseDisjoint
      (blockSet (L := L) (N := N) j) :=
  fun _ _ _ _ hne => blockSet_disjoint hne

/-- The sum over blocks of a split evaluation is the evaluation on `Λ`. -/
theorem sum_splitO_blocks (V : Coup c) :
    ∑ p ∈ blockIdx (L := L) (N := N) j, splitO c V a b (blockSet j p) = evalO c V a b univ := by
  rw [← splitO_biUnion c V a b _ _ (blockSet_pairwiseDisjoint j), blocks_univ_biUnion,
    splitO_univ]

/-- **`(u + V)^obs_{j+1}(Λ)`** at the level of `Λ` (no hypotheses):
`∑_B RHS(B) = 𝔼θ V̂(Λ) - ½ 𝔼[θV̂(Λ); θV̂(Λ)]`. -/
theorem sum_RHS : ∑ p ∈ blockIdx (L := L) (N := N) j, RHS C j Vo K a b p =
    freeStep C (VhatL j Vo K a b) := by
  simp only [RHS_eq_Rmap]
  rw [← Rmap_sum, ← Rmap_self]; rfl

variable {j Vo K a b}

/-- `V̂(B)` is the split evaluation of `V_j - Q`. -/
theorem Vhat_eq (hab : a ≠ b) (p : Fin d → ℕ) :
    Vhat j Vo K a b p = splitO c (Wcoup j Vo K a b) a b (blockSet j p) := by
  rw [Vhat, Vobs, QobsO_eq hab, Wcoup, splitO_sub]

theorem VhatL_eq (hab : a ≠ b) :
    VhatL j Vo K a b = evalO c (Wcoup j Vo K a b) a b univ := by
  rw [VhatL, sum_congr rfl fun p _ => Vhat_eq hab p, sum_splitO_blocks]

/-- **Definition `def:V+obs`**: the right side of `E:Qobs` is of the form `(u + V)^obs_{j+1}(B)`
(split evaluation) for the coupling constants `nextObs`, for every block `B`. -/
theorem RHS_eq (hab : a ≠ b) (hCs : C a b = C b a) (p : Fin d → ℕ) :
    RHS C j Vo K a b p = splitO c (nextObs C j Vo K a b) a b (blockSet j p) := by
  rw [RHS_eq_Rmap, Vhat_eq hab, VhatL_eq hab, Rmap_splitO C _ hCs]; rfl

/-- **Definition `def:V+obs` at the level of `Λ`**: `∑_B RHS(B) = (u + V)^obs_{j+1}(Λ)`
(evaluation `e:VobsX`), consistently with the per-block reading. -/
theorem sum_RHS_eq (hab : a ≠ b) (hCs : C a b = C b a) :
    ∑ p ∈ blockIdx (L := L) (N := N) j, RHS C j Vo K a b p =
      evalO c (nextObs C j Vo K a b) a b univ := by
  rw [sum_RHS, VhatL_eq hab, freeStep_evalO_univ C _ hCs]; rfl

end Def

end

end Obs
