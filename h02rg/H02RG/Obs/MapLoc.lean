import Obs.MapEval
import Obs.LocObs
import Obs.Generic

/-!
# The extended `Loc`, `Q^obs(B)` and `J^obs(B, X)` (Section `sec:rgmap-ext`)

`Loc_{X,Y}` on the algebra with observables is block diagonal (Section `sec:locobs`):
`Loc_{X,Y} F = Loc_{X,Y} F_∅ + σ_a loc^a_{X,Y} F_a + σ̄_b loc^b_{X,Y} F_b +
σ_aσ̄_b loc^{ab}_{X,Y} F_ab` (resp. with `σ_b`), with the bulk `Loc` of `Loc.Image` (`LocXY`)
and the observable operators `locA`, `locB`, `locAB` of `Obs.LocObsDef` (`LocS`, `LocO`).

`QO j K p` and `JO j K p X` are `Q(B)` and `J(B, X)` of `e:Q-def`–`e:J-def` for the `j`-block
`B = blockSet j p`, with the extended `Loc` (and `Q = J = 0` if `j + 1 = N`); the bulk
components are `Step.Qb`, `Step.Jb` of the bulk components (`bulk_QO`, `bulk_JO`).
`Q^obs(B) = π_obs Q(B)`.

## The image of `Q^obs` (Proposition `prop:Loc-obs` (iv))
`Qcoup c j K a b` are coupling constants read off from the pairings of `K_j(X)`, `X ∈ 𝒮_j`
(`mass1`, `mass2`, `ε`).  If `a ≠ b`, then `Q^obs(B)` is the split evaluation of `Qcoup` for
every block (`QobsO_eq`), without further hypotheses.

**Deviation (split `q`, `r`).**  For a small set `X` containing `a` but not `b` (possible with
`K^{ab}(X) ≠ 0` once `j ≥ j_ab`, since `b` may lie in `X^□`), `loc^{ab}_{X,B}` produces
`u + r' ψ̄_aψ_a` in the block of `a` only (`locAB_eq_ind`), which is not of the symmetric form
`σσ (r/2)(ψ̄_aψ_a + ψ̄_bψ_b)` of `def:cVobs`.  With the split coupling constants of
`Obs.Coupling` (`r` split into `r_a, r_b` and `q` into `q_a, q_b`; the paper's symmetric form is
not preserved by `Loc^obs` on sets containing only one of `a, b`), the `ab` image is read off
separately at `a` and at `b`:
`q_x = -∑_{X ∈ 𝒮_j, x ∈ X} ε(K_{ab}(X)) / |X ∩ {a,b}|`,
`r_x = ∑_{X ∈ 𝒮_j, x ∈ X} mass₂(K_{ab}(X)) / |X ∩ {a,b}|` (`x = a, b`).
-/

namespace Obs

noncomputable section

open Finset Grassmann SA Loc Step LocObs

variable {d L N : ℕ} [NeZero L]

/-- The case of `Obs.LocObs`. -/
def Case.toObs : Case → ObsCase
  | .one => .one
  | .two => .two

/-! ### The extended `Loc` -/

section Loc

variable {c : Case} (a b : Lam d L N)

/-- `Loc_{X,Y}` on the algebra with observables (block diagonal). -/
def LocS (X Y : Finset (Lam d L N)) (F : SA c (Lam d L N)) : SA c (Lam d L N) :=
  ⟨LocXY X Y F.e, locA c.toObs a X Y F.a, locB c.toObs b X Y F.b, locAB a b X Y F.ab⟩

theorem inv'_locGen_odd (s : ℤˣ) (P X Y : Finset (Lam d L N)) (c' : ℂ) :
    inv' (locGen P X Y (fun z => ψ (z, s)) c') = -locGen P X Y (fun z => ψ (z, s)) c' := by
  simp only [locGen, map_smul, map_sum, inv'_ψ, sum_neg_distrib, smul_neg]

theorem inv'_locEven (P X Y : Finset (Lam d L N)) (F : Alg d L N) :
    inv' (locEven P X Y F) = locEven P X Y F := by
  simp only [locEven, locGen, map_add, map_smul, map_sum, map_one]
  congr 2
  refine sum_congr rfl fun z _ => ?_
  exact inv'_psibar_psi z z

theorem mem_OEv_LocS (X Y : Finset (Lam d L N)) (F : SA c (Lam d L N)) :
    LocS a b X Y F ∈ OEv c (Lam d L N) := by
  refine mem_OEv.2 ⟨mem_Ev.1 (LocXY_mem_Ev X Y F.e), ?_, ?_, inv'_locEven _ X Y _⟩
  · cases c
    · show inv' (locOdd (-1) {a} X Y F.a) = (-1 : ℂ) • locOdd (-1) {a} X Y F.a
      rw [neg_one_smul]; exact inv'_locGen_odd _ _ _ _ _
    · show inv' (locEven {a} X Y F.a) = (1 : ℂ) • locEven {a} X Y F.a
      rw [one_smul]; exact inv'_locEven _ _ _ _
  · cases c
    · show inv' (locOdd 1 {b} X Y F.b) = (-1 : ℂ) • locOdd 1 {b} X Y F.b
      rw [neg_one_smul]; exact inv'_locGen_odd _ _ _ _ _
    · show inv' (locEven {b} X Y F.b) = (1 : ℂ) • locEven {b} X Y F.b
      rw [one_smul]; exact inv'_locEven _ _ _ _

/-- `Loc_{X,Y}` on even elements. -/
def LocO (X Y : Finset (Lam d L N)) (F : OE c (Lam d L N)) : OE c (Lam d L N) :=
  ⟨LocS a b X Y (F : SA c (Lam d L N)), mem_OEv_LocS a b X Y _⟩

@[simp] theorem coe_LocO (X Y : Finset (Lam d L N)) (F : OE c (Lam d L N)) :
    (LocO a b X Y F : SA c (Lam d L N)) = LocS a b X Y (F : SA c (Lam d L N)) := rfl

@[simp] theorem LocS_e (X Y : Finset (Lam d L N)) (F : SA c (Lam d L N)) :
    (LocS a b X Y F).e = LocXY X Y F.e := rfl
@[simp] theorem LocS_a (X Y : Finset (Lam d L N)) (F : SA c (Lam d L N)) :
    (LocS a b X Y F).a = locA c.toObs a X Y F.a := rfl
@[simp] theorem LocS_b (X Y : Finset (Lam d L N)) (F : SA c (Lam d L N)) :
    (LocS a b X Y F).b = locB c.toObs b X Y F.b := rfl
@[simp] theorem LocS_ab (X Y : Finset (Lam d L N)) (F : SA c (Lam d L N)) :
    (LocS a b X Y F).ab = locAB a b X Y F.ab := rfl

end Loc

/-! ### `Q(B)` and `J(B, X)` -/

section QJ

variable {c : Case} (a b : Lam d L N) (j : ℕ) (K : Finset (Lam d L N) → OE c (Lam d L N))

/-- `Q(B) = ∑_{X ∈ 𝒮_j, X ⊇ B} Loc_{X,B} K(X)` (`e:Q-def`), `Q = 0` if `j + 1 = N`. -/
def QO (p : Fin d → ℕ) : OE c (Lam d L N) :=
  open Classical in
  if j + 1 < N then
    ∑ X ∈ (smallSets j).filter (fun X => blockSet j p ⊆ X), LocO a b X (blockSet j p) (K X)
  else 0

/-- `J(B, X)` (`e:J-defB`, `e:J-def`), `J = 0` if `j + 1 = N`. -/
def JO (p : Fin d → ℕ) (X : Finset (Lam d L N)) : OE c (Lam d L N) :=
  open Classical in
  if j + 1 < N ∧ IsSmall j X ∧ blockSet j p ⊆ X then
    if X = blockSet j p then
      -∑ Y ∈ (smallSets j).filter (fun Y => blockSet j p ⊆ Y ∧ Y ≠ blockSet j p),
        LocO a b Y (blockSet j p) (K Y)
    else LocO a b X (blockSet j p) (K X)
  else 0

/-- `Q^obs(B) = π_obs Q(B)`. -/
def QobsO (p : Fin d → ℕ) : OE c (Lam d L N) := πobs (QO a b j K p)

theorem bulk_JO (p : Fin d → ℕ) (X : Finset (Lam d L N)) :
    bulk (JO a b j K p X) = Jb j (fun X => bulk (K X)) p X := by
  unfold JO Jb
  split_ifs
  · rw [map_neg, map_sum]; rfl
  · rfl
  · exact map_zero _

theorem JO_of_not_small (p : Fin d → ℕ) {X : Finset (Lam d L N)} (hX : ¬ IsSmall j X) :
    JO a b j K p X = 0 := by
  unfold JO; rw [if_neg fun h => hX h.2.1]

end QJ

/-! ### The coupling constants of `Q^obs` -/

section Qcoup

open Classical in
/-- The small sets containing `x`. -/
def smallAt (j : ℕ) (x : Lam d L N) : Finset (Finset (Lam d L N)) :=
  (smallSets j).filter (fun X => x ∈ X)

/-- The weight `|X ∩ {a, b}|` of `loc^{ab}_{X,·}`. -/
def cardAB (a b : Lam d L N) (X : Finset (Lam d L N)) : ℂ := ((X ∩ {a, b}).card : ℂ)

/-- The coupling constants of `Q^obs` (`0` if `j + 1 = N`); the `ab` constants are read off
separately at `a` (`q_a`, `r_a`) and at `b` (`q_b`, `r_b`). -/
def Qcoup : (c : Case) → ℕ → (Finset (Lam d L N) → OE c (Lam d L N)) → Lam d L N →
    Lam d L N → Coup c
  | .one, j, K, a, b =>
    if j + 1 < N then
      (⟨-∑ X ∈ smallAt j a, mass1 (-1) ((K X : SA .one (Lam d L N)).a),
        ∑ X ∈ smallAt j b, mass1 1 ((K X : SA .one (Lam d L N)).b),
        -∑ X ∈ smallAt j a, ε ((K X : SA .one (Lam d L N)).ab) / cardAB a b X,
        -∑ X ∈ smallAt j b, ε ((K X : SA .one (Lam d L N)).ab) / cardAB a b X,
        ∑ X ∈ smallAt j a, mass2 ((K X : SA .one (Lam d L N)).ab) / cardAB a b X,
        ∑ X ∈ smallAt j b, mass2 ((K X : SA .one (Lam d L N)).ab) / cardAB a b X⟩ : Coup1)
    else (⟨0, 0, 0, 0, 0, 0⟩ : Coup1)
  | .two, j, K, a, b =>
    if j + 1 < N then
      (⟨-∑ X ∈ smallAt j a, mass2 ((K X : SA .two (Lam d L N)).a),
        -∑ X ∈ smallAt j b, mass2 ((K X : SA .two (Lam d L N)).b),
        -∑ X ∈ smallAt j a, ε ((K X : SA .two (Lam d L N)).a),
        -∑ X ∈ smallAt j b, ε ((K X : SA .two (Lam d L N)).b),
        -∑ X ∈ smallAt j a, ε ((K X : SA .two (Lam d L N)).ab) / cardAB a b X,
        -∑ X ∈ smallAt j b, ε ((K X : SA .two (Lam d L N)).ab) / cardAB a b X, 0,
        ∑ X ∈ smallAt j a, mass2 ((K X : SA .two (Lam d L N)).ab) / cardAB a b X,
        ∑ X ∈ smallAt j b, mass2 ((K X : SA .two (Lam d L N)).ab) / cardAB a b X⟩ : Coup2)
    else (⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : Coup2)

theorem Qcoup_of_not {c : Case} {j : ℕ} (hj : ¬ j + 1 < N)
    (K : Finset (Lam d L N) → OE c (Lam d L N)) (a b : Lam d L N) :
    Qcoup c j K a b = Coup.zero c := by
  cases c <;> simp only [Qcoup, if_neg hj] <;> rfl

/-! #### The per-set formulas -/

theorem mem_iff_blockSet_subset {j : ℕ} {X : Finset (Lam d L N)} (hX : IsPolymer j X)
    {p : Fin d → ℕ} {x : Lam d L N} (hx : x ∈ blockSet j p) : blockSet j p ⊆ X ↔ x ∈ X := by
  refine ⟨fun h => h hx, fun h => blockSet_subset hX ?_⟩
  rw [← (Loc.mem_blockSet.1 hx)]
  exact mem_image_of_mem _ h

theorem inter_singleton_of_mem {X : Finset (Lam d L N)} {x : Lam d L N} (h : x ∈ X) :
    X ∩ {x} = {x} := by
  ext z; simp only [mem_inter, mem_singleton]; constructor
  · exact fun h => h.2
  · rintro rfl; exact ⟨h, rfl⟩

theorem inter_singleton_of_not_mem {X : Finset (Lam d L N)} {x : Lam d L N} (h : x ∉ X) :
    X ∩ {x} = ∅ := by
  ext z; simp only [mem_inter, mem_singleton, notMem_empty, iff_false]
  rintro ⟨hz, rfl⟩; exact h hz

theorem locOdd_single (s : ℤˣ) (x : Lam d L N) {X B : Finset (Lam d L N)} (hBX : B ⊆ X)
    (F : Alg d L N) : locOdd s {x} X B F = ind (x ∈ B) • (mass1 s F • ψ (x, s)) := by
  by_cases hB : x ∈ B
  · rw [locOdd, locGen, inter_singleton_of_mem (hBX hB), inter_singleton_of_mem hB, ind_pos hB,
      card_singleton, sum_singleton, Nat.cast_one, div_one, one_smul]
  · rw [locOdd, locGen, inter_singleton_of_not_mem hB, ind_neg hB, sum_empty, smul_zero,
      zero_smul]

theorem locEven_single (x : Lam d L N) {X B : Finset (Lam d L N)} (hBX : B ⊆ X)
    (F : Alg d L N) : locEven {x} X B F =
      ind (x ∈ B) • (algebraMap ℂ (Alg d L N) (ε F) + mass2 F • (psibar x * psi x)) := by
  by_cases hB : x ∈ B
  · rw [locEven, locGen, locGen, inter_singleton_of_mem (hBX hB), inter_singleton_of_mem hB,
      ind_pos hB, card_singleton, sum_singleton, sum_singleton, Nat.cast_one, div_one, div_one,
      one_smul, Algebra.algebraMap_eq_smul_one, pbp]
  · rw [locEven, locGen, locGen, inter_singleton_of_not_mem hB, ind_neg hB, sum_empty,
      sum_empty, smul_zero, smul_zero, add_zero, zero_smul]

theorem sum_inter_pair {M : Type*} [AddCommMonoid M] [Module ℂ M] {a b : Lam d L N}
    (hab : a ≠ b) (B : Finset (Lam d L N)) (f : Lam d L N → M) :
    ∑ z ∈ B ∩ {a, b}, f z = ind (a ∈ B) • f a + ind (b ∈ B) • f b := by
  by_cases ha' : a ∈ B <;> by_cases hb' : b ∈ B
  · have : B ∩ {a, b} = {a, b} := by
      ext z; simp only [mem_inter, mem_insert, mem_singleton]
      constructor
      · exact fun h => h.2
      · rintro (rfl | rfl) <;> simp_all
    rw [this, sum_pair hab]; simp [ha', hb']
  · have : B ∩ {a, b} = {a} := by
      ext z; simp only [mem_inter, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hz, rfl | rfl⟩
        · rfl
        · exact absurd hz hb'
      · rintro rfl; exact ⟨ha', Or.inl rfl⟩
    rw [this, sum_singleton]; simp [ha', hb']
  · have : B ∩ {a, b} = {b} := by
      ext z; simp only [mem_inter, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hz, rfl | rfl⟩
        · exact absurd hz ha'
        · rfl
      · rintro rfl; exact ⟨hb', Or.inr rfl⟩
    rw [this, sum_singleton]; simp [ha', hb']
  · have : B ∩ {a, b} = ∅ := by
      ext z; simp only [mem_inter, mem_insert, mem_singleton, notMem_empty, iff_false]
      rintro ⟨hz, rfl | rfl⟩
      · exact ha' hz
      · exact hb' hz
    rw [this, sum_empty]; simp [ha', hb']

/-- **The `ab` component of `Loc_{X,B}`** (no hypotheses on `X` besides `a ≠ b`):
`loc^{ab}_{X,B} F = 1_{a∈B} (ε(F) + mass₂(F) ψ̄_aψ_a)/|X ∩ {a,b}| +
1_{b∈B} (ε(F) + mass₂(F) ψ̄_bψ_b)/|X ∩ {a,b}|`.  In particular for `X ∋ a`, `X ∌ b` only the
block of `a` receives a contribution, and it is asymmetric (`r_a` only). -/
theorem locAB_eq_ind {a b : Lam d L N} (hab : a ≠ b) (X B : Finset (Lam d L N))
    (F : Alg d L N) : locAB a b X B F =
      ind (a ∈ B) • ((ε F / cardAB a b X) • (1 : Alg d L N) +
          (mass2 F / cardAB a b X) • (psibar a * psi a)) +
        ind (b ∈ B) • ((ε F / cardAB a b X) • (1 : Alg d L N) +
          (mass2 F / cardAB a b X) • (psibar b * psi b)) := by
  rw [locAB, locEven, locGen, locGen, sum_inter_pair hab, sum_inter_pair hab, ← cardAB]
  simp only [pbp, smul_add, smul_smul]
  module

/-! #### Summing over the small sets containing a block -/

open Classical in
theorem sum_filter_ind {M : Type*} [AddCommMonoid M] [Module ℂ M] (j : ℕ) (p : Fin d → ℕ)
    (x : Lam d L N) (f : Finset (Lam d L N) → M) :
    ∑ X ∈ (smallSets j).filter (fun X => blockSet j p ⊆ X), ind (x ∈ blockSet j p) • f X =
      ind (x ∈ blockSet j p) • ∑ X ∈ smallAt j x, f X := by
  by_cases hx : x ∈ blockSet j p
  · rw [ind_pos hx, one_smul]
    simp only [one_smul]
    unfold smallAt
    congr 1
    refine filter_congr fun X hX => ?_
    exact mem_iff_blockSet_subset (mem_smallSets.1 hX).1 hx
  · simp [ind_neg hx]

/-- **The image of `Q^obs`** (Proposition `prop:Loc-obs` (iv) summed over `X`): if `a ≠ b`,
then `Q^obs(B)` is the split evaluation of the coupling constants `Qcoup`. -/
theorem QobsO_eq {c : Case} {j : ℕ} {K : Finset (Lam d L N) → OE c (Lam d L N)}
    {a b : Lam d L N} (hab : a ≠ b) (p : Fin d → ℕ) :
    QobsO a b j K p = splitO c (Qcoup c j K a b) a b (blockSet j p) := by
  classical
  unfold QobsO QO
  split_ifs with hj
  · rw [map_sum]
    refine Subtype.ext ?_
    simp only [AddSubmonoidClass.coe_finsetSum, coe_πobs, piobs_apply, coe_LocO, coe_splitO,
      splitS]
    have hsm : ∀ X ∈ (smallSets j).filter (fun X => blockSet (L := L) (N := N) j p ⊆ X),
        IsSmall j X ∧ blockSet j p ⊆ X := fun X hX =>
      ⟨mem_smallSets.1 (mem_filter.1 hX).1, (mem_filter.1 hX).2⟩
    have hab' : ∑ X ∈ (smallSets j).filter (fun X => blockSet (L := L) (N := N) j p ⊆ X),
        locAB a b X (blockSet j p) (K X : SA c (Lam d L N)).ab =
        ind (a ∈ blockSet j p) • (algebraMap ℂ (Alg d L N)
            (∑ X ∈ smallAt j a, ε (K X : SA c (Lam d L N)).ab / cardAB a b X) +
          (∑ X ∈ smallAt j a, mass2 (K X : SA c (Lam d L N)).ab / cardAB a b X) •
            (psibar a * psi a)) +
        ind (b ∈ blockSet j p) • (algebraMap ℂ (Alg d L N)
            (∑ X ∈ smallAt j b, ε (K X : SA c (Lam d L N)).ab / cardAB a b X) +
          (∑ X ∈ smallAt j b, mass2 (K X : SA c (Lam d L N)).ab / cardAB a b X) •
            (psibar b * psi b)) := by
      rw [sum_congr rfl fun X _ => locAB_eq_ind hab X _ _, sum_add_distrib, sum_filter_ind,
        sum_filter_ind]
      congr 2 <;>
      · rw [sum_add_distrib, ← sum_smul, ← sum_smul, Algebra.algebraMap_eq_smul_one]
    cases c
    · ext
      · simp [sum_e, halfA, halfB]
      · rw [sum_a]
        simp only [LocS_a, Case.toObs, locA]
        rw [sum_congr rfl fun X hX => locOdd_single (-1) a (hsm X hX).2 _, sum_filter_ind]
        simp [halfA, halfB, Qcoup, hj, sum_smul, psibar]
      · rw [sum_b]
        simp only [LocS_b, Case.toObs, locB]
        rw [sum_congr rfl fun X hX => locOdd_single 1 b (hsm X hX).2 _, sum_filter_ind]
        simp [halfA, halfB, Qcoup, hj, sum_smul, psi]
      · simp only [sum_ab, LocS_ab]
        rw [hab']
        simp [halfA, halfB, Qcoup, hj]
    · ext
      · simp [sum_e, halfA, halfB]
      · rw [sum_a]
        simp only [LocS_a, Case.toObs, locA]
        rw [sum_congr rfl fun X hX => locEven_single a (hsm X hX).2 _, sum_filter_ind]
        simp [halfA, halfB, Qcoup, hj, sum_smul, map_sum, sum_add_distrib, sub_eq_add_neg]
      · rw [sum_b]
        simp only [LocS_b, Case.toObs, locB]
        rw [sum_congr rfl fun X hX => locEven_single b (hsm X hX).2 _, sum_filter_ind]
        simp [halfA, halfB, Qcoup, hj, sum_smul, map_sum, sum_add_distrib, sub_eq_add_neg]
      · simp only [sum_ab, LocS_ab]
        rw [hab']
        simp [halfA, halfB, Qcoup, hj]
  · rw [map_zero, Qcoup_of_not hj, splitO_zero]

end Qcoup

end

end Obs
