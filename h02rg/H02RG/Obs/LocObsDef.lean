import Loc.LocProps

/-!
# Localisation with observables: definitions and algebraic properties (Section `sec:locobs`)

We work at the level of the components `F_a, F_b, F_{ab} ∈ 𝒩(Λ)` of an observable-extended
element `F = F_∅ + σ_a F_a + σ̄_b F_b + σ_a σ̄_b F_{ab}` (Case (1)), resp.
`F_∅ + σ_a F_a + σ_b F_b + σ_a σ_b F_{ab}` (Case (2)).  `Loc_{X,Y}` is block diagonal:
`Loc_{X,Y}(σ_a F_a) = σ_a loc^a_{X ∩ {a}, Y ∩ {a}} F_a`, etc., so it suffices to define the
operators `loc^a, loc^b, loc^{ab}` on `𝒩(Λ)`.

## Definition
With `P` the set of observable points (`{a}`, `{b}` or `{a, b}`), `X' = X ∩ P`, `Y' = Y ∩ P`:

* `locGen P X Y f c = (c / |X'|) ∑_{z ∈ Y'} f_z` (the generic form of a localised polynomial
  given by its pairing `c` with the constant test polynomial);
* `mass1 s F = ∑_x F_{(x,s)}` (the pairing of the length-one part of `F`, with spin `s`, with the
  constant test polynomial), `mass2 F = ∑_{x,y} F_{(x,-)(y,+)}` (the total coefficient of
  `ψ̄_x ψ_y`);
* `locOdd s P X Y F = locGen P X Y ψ_{(·,s)} (mass1 s F)`: in Case (1),
  `loc^a_{X,Y} F_a = 1_{a ∈ X ∩ Y} (∑_x F_{a,(x,-)}) ψ̄_a` (`s = -1`) and
  `loc^b_{X,Y} F_b = 1_{b ∈ X ∩ Y} (∑_x F_{b,(x,+)}) ψ_b` (`s = +1`);
* `locEven P X Y F = locGen P X Y 1 (ε F) + locGen P X Y (ψ̄ψ) (mass2 F)`: `loc^{ab}` in both cases
  (`P = {a, b}`) and `loc^a`, `loc^b` in Case (2) (`P = {a}`, `{b}`).

So, e.g., `loc^{ab}_{X} F = ε(F) + (∑_{x,y} F_{(x,-)(y,+)}) · (ψ̄_a ψ_a 1_{a ∈ X, b ∉ X} +
ψ̄_b ψ_b 1_{b ∈ X, a ∉ X} + ½(ψ̄_a ψ_a + ψ̄_b ψ_b) 1_{a, b ∈ X})` (`example_ii_ab`); the constant
`ε(F)` is split in the same way over the points of `X ∩ {a,b}`.

## Deviations
* **Definition via the `U(1)`-compatible image.**  The text defines `loc^a, loc^b, loc^{ab}` as the
  operators of [MR3332939, Def. 1.17] with maximal dimensions `d_+^a = d_+^b = p(d-2)/2`,
  `d_+^{ab} = d - 2`; their image is spanned by the local monomials of dimension `≤ d_+`
  (e.g. `ψ̄_a, ψ_a`, constants, first order monomials with gradients), and the text itself (proof
  of (iv)) only uses that on `U(1)`-invariant inputs only the `U(1)`-compatible monomials survive.
  Since only `U(1)`-invariant `F` occur along the flow, we define `Loc^obs` directly by its
  `U(1)`-compatible image: the test polynomials are the constant ones only, paired with the
  `U(1)`-compatible part (`ψ̄` for `F_a` in Case (1), `ψ` for `F_b`, `ε` and `ψ̄ψ` for even
  components).  On `U(1)`-invariant inputs this agrees with the text's operator; on other inputs
  our operator discards the incompatible part.  In particular (iv) holds for all inputs.
* **Points outside `X`.**  `loc_{X ∩ P, Y ∩ P} = 0` if `X ∩ P = ∅` (in Lean via `c / 0 = 0`).
* **(iv) for `ab`.**  For a block `B` with `B ∩ {a,b} = {a}` the image `u + r ψ̄_a ψ_a` is not of the
  form `e:VobsX` (which has the `q, r` terms only for `a, b ∈ B`); the text's own
  Example (ii) produces such terms.  We state (iv) as: the image is a combination of `1` and
  `ψ̄_z ψ_z`, `z ∈ B ∩ {a,b}` (`locEven_image`), and of exactly the form of `e:VobsX` when
  `a, b ∈ B` (`locEven_image_ab`).
-/

namespace Obs.LocObs

noncomputable section

open Finset Grassmann FRD Loc

/-! ### Charge (`U(1)`) -/

section Charge

variable {Λ : Type*} [DecidableEq Λ]

/-- The charge `#{ψ̄} - #{ψ}` of a sequence (spin `-1` is `ψ̄`, spin `+1` is `ψ`). -/
def charge {n : ℕ} (z : Fin n → Sf Λ) : ℤ :=
  ((univ.filter fun i => (z i).2 = -1).card : ℤ) - ((univ.filter fun i => (z i).2 = 1).card : ℤ)

/-- `F` has charge `q`: all monomials of `F` have `q` more factors `ψ̄` than `ψ`.  In Case (1)
`U(1)` invariance of `σ_a F_a` means `HasCharge 1 F_a`, of `σ̄_b F_b` means `HasCharge (-1) F_b`;
the other components have charge `0`. -/
def HasCharge (q : ℤ) (F : N Λ) : Prop :=
  ∀ (n : ℕ) (z : Fin n → Sf Λ), charge z ≠ q → coeff F z = 0

theorem hasCharge_zero_iff {d L N : ℕ} [NeZero L] (F : Alg d L N) : HasCharge 0 F ↔ IsSym F := by
  unfold HasCharge IsSym charge
  refine forall_congr' fun n => forall_congr' fun z => ?_
  constructor
  · intro h hne; exact h fun h0 => hne (by omega)
  · intro h hne; exact h fun h0 => hne (by omega)

end Charge

variable {d L N : ℕ} [NeZero L]

/-! ### Definitions -/

/-- `∑_x F_{(x,s)}`: the pairing of the length-one part of spin `s` with the constant test
polynomial. -/
def mass1 (s : ℤˣ) (F : Alg d L N) : ℂ := ∑ x, coeff F ![(x, s)]

/-- `∑_{x,y} F_{(x,-)(y,+)}`: the total coefficient of `ψ̄_x ψ_y`. -/
def mass2 (F : Alg d L N) : ℂ := ∑ x, ∑ y, coeff F ![(x, -1), (y, 1)]

/-- The monomial `ψ̄_z ψ_z`. -/
def pbp (z : Lam d L N) : Alg d L N := psibar z * psi z

/-- `(c / |X ∩ P|) ∑_{z ∈ Y ∩ P} f_z`. -/
def locGen (P X Y : Finset (Lam d L N)) (f : Lam d L N → Alg d L N) (c : ℂ) : Alg d L N :=
  (c / ((X ∩ P).card : ℂ)) • ∑ z ∈ Y ∩ P, f z

/-- Odd components (Case (1)): `loc_{X,Y} F = (∑_x F_{(x,s)} / |X ∩ P|) ∑_{z ∈ Y ∩ P} ψ_{(z,s)}`. -/
def locOdd (s : ℤˣ) (P X Y : Finset (Lam d L N)) (F : Alg d L N) : Alg d L N :=
  locGen P X Y (fun z => ψ (z, s)) (mass1 s F)

/-- Even components: `loc_{X,Y} F = (1/|X ∩ P|) ∑_{z ∈ Y ∩ P} (ε(F) + (∑_{x,y} F_{(x,-)(y,+)})
ψ̄_z ψ_z)`. -/
def locEven (P X Y : Finset (Lam d L N)) (F : Alg d L N) : Alg d L N :=
  locGen P X Y (fun _ => 1) (ε F) + locGen P X Y pbp (mass2 F)

/-- The two cases of observables: Case (1) `σ_a, σ̄_b` odd, Case (2) `σ = ϑ̄ϑ` even. -/
inductive ObsCase
  | one
  | two
  deriving DecidableEq

/-- The charge of `U(1)`-invariant `F_a`. -/
def chargeA : ObsCase → ℤ
  | .one => 1
  | .two => 0

/-- The charge of `U(1)`-invariant `F_b`. -/
def chargeB : ObsCase → ℤ
  | .one => -1
  | .two => 0

/-- `loc^a_{X,Y}` on the component `F_a`. -/
def locA : ObsCase → Lam d L N → Finset (Lam d L N) → Finset (Lam d L N) → Alg d L N →
    Alg d L N
  | .one, a, X, Y, F => locOdd (-1) {a} X Y F
  | .two, a, X, Y, F => locEven {a} X Y F

/-- `loc^b_{X,Y}` on the component `F_b`. -/
def locB : ObsCase → Lam d L N → Finset (Lam d L N) → Finset (Lam d L N) → Alg d L N →
    Alg d L N
  | .one, b, X, Y, F => locOdd 1 {b} X Y F
  | .two, b, X, Y, F => locEven {b} X Y F

/-- `loc^{ab}_{X,Y}` on the component `F_{ab}` (both cases). -/
def locAB (a b : Lam d L N) (X Y : Finset (Lam d L N)) (F : Alg d L N) : Alg d L N :=
  locEven {a, b} X Y F

/-! ### Linearity -/

theorem mass1_add (s : ℤˣ) (F G : Alg d L N) : mass1 s (F + G) = mass1 s F + mass1 s G := by
  simp [mass1, coeff_add, sum_add_distrib]

theorem mass2_add (F G : Alg d L N) : mass2 (F + G) = mass2 F + mass2 G := by
  simp [mass2, coeff_add, sum_add_distrib]

theorem mass1_smul (s : ℤˣ) (c : ℂ) (F : Alg d L N) : mass1 s (c • F) = c * mass1 s F := by
  simp [mass1, coeff_smul, mul_sum]

theorem mass2_smul (c : ℂ) (F : Alg d L N) : mass2 (c • F) = c * mass2 F := by
  simp [mass2, coeff_smul, mul_sum]

theorem locGen_add_c (P X Y : Finset (Lam d L N)) (f : Lam d L N → Alg d L N) (c c' : ℂ) :
    locGen P X Y f (c + c') = locGen P X Y f c + locGen P X Y f c' := by
  simp [locGen, add_div, add_smul]

theorem locGen_smul_c (P X Y : Finset (Lam d L N)) (f : Lam d L N → Alg d L N) (r c : ℂ) :
    locGen P X Y f (r * c) = r • locGen P X Y f c := by
  simp [locGen, mul_div_assoc, mul_smul]

theorem locOdd_add (s : ℤˣ) (P X Y : Finset (Lam d L N)) (F G : Alg d L N) :
    locOdd s P X Y (F + G) = locOdd s P X Y F + locOdd s P X Y G := by
  simp [locOdd, mass1_add, locGen_add_c]

theorem locOdd_smul (s : ℤˣ) (P X Y : Finset (Lam d L N)) (c : ℂ) (F : Alg d L N) :
    locOdd s P X Y (c • F) = c • locOdd s P X Y F := by
  simp [locOdd, mass1_smul, locGen_smul_c]

theorem locEven_add (P X Y : Finset (Lam d L N)) (F G : Alg d L N) :
    locEven P X Y (F + G) = locEven P X Y F + locEven P X Y G := by
  simp only [locEven, map_add, mass2_add, locGen_add_c]; abel

theorem locEven_smul (P X Y : Finset (Lam d L N)) (c : ℂ) (F : Alg d L N) :
    locEven P X Y (c • F) = c • locEven P X Y F := by
  simp only [locEven, map_smul, smul_eq_mul, mass2_smul, locGen_smul_c, smul_add]

/-! ### `Loc_{X,∅} = 0` and additivity (Proposition `prop:Loc-obs` (iii)) -/

theorem locGen_biUnion {ι : Type*} (s : Finset ι) (Q : ι → Finset (Lam d L N))
    (hQ : (s : Set ι).PairwiseDisjoint Q) (P X : Finset (Lam d L N)) (f : Lam d L N → Alg d L N)
    (c : ℂ) : locGen P X (s.biUnion Q) f c = ∑ i ∈ s, locGen P X (Q i) f c := by
  classical
  have hQ' : (s : Set ι).PairwiseDisjoint fun i => Q i ∩ P := by
    intro i hi i' hi' hne
    exact Disjoint.mono inter_subset_left inter_subset_left (hQ hi hi' hne)
  have e : s.biUnion Q ∩ P = s.biUnion fun i => Q i ∩ P := by
    ext z; simp only [mem_inter, mem_biUnion]; tauto
  simp only [locGen, e, sum_biUnion hQ', smul_sum]

/-- Proposition `prop:Loc-obs` (iii) for odd components. -/
theorem locOdd_eq_sum {ι : Type*} (s : Finset ι) (Q : ι → Finset (Lam d L N))
    (hQ : (s : Set ι).PairwiseDisjoint Q) (σ : ℤˣ) (P : Finset (Lam d L N)) (F : Alg d L N) :
    locOdd σ P (s.biUnion Q) (s.biUnion Q) F = ∑ i ∈ s, locOdd σ P (s.biUnion Q) (Q i) F :=
  locGen_biUnion s Q hQ _ _ _ _

/-- Proposition `prop:Loc-obs` (iii) for even components. -/
theorem locEven_eq_sum {ι : Type*} (s : Finset ι) (Q : ι → Finset (Lam d L N))
    (hQ : (s : Set ι).PairwiseDisjoint Q) (P : Finset (Lam d L N)) (F : Alg d L N) :
    locEven P (s.biUnion Q) (s.biUnion Q) F = ∑ i ∈ s, locEven P (s.biUnion Q) (Q i) F := by
  simp only [locEven, locGen_biUnion s Q hQ, sum_add_distrib]

/-! ### Locality -/

theorem pbp_mem {A : Set (Lam d L N)} {z : Lam d L N} (hz : z ∈ A) : pbp z ∈ NX A :=
  mul_mem (ψ_mem_NX (a := (z, -1)) hz) (ψ_mem_NX (a := (z, 1)) hz)

theorem locGen_mem (P X Y : Finset (Lam d L N)) {f : Lam d L N → Alg d L N} (c : ℂ)
    (hf : ∀ z ∈ Y ∩ P, f z ∈ NX ((Y ∩ P : Finset (Lam d L N)) : Set (Lam d L N))) :
    locGen P X Y f c ∈ NX ((Y ∩ P : Finset (Lam d L N)) : Set (Lam d L N)) :=
  Subalgebra.smul_mem _ (Subalgebra.sum_mem _ hf) _

/-- Locality: `loc_{X,Y} F ∈ 𝒩(Y ∩ P)` (supported at the observable points in `Y`). -/
theorem locOdd_mem (s : ℤˣ) (P X Y : Finset (Lam d L N)) (F : Alg d L N) :
    locOdd s P X Y F ∈ NX ((Y ∩ P : Finset (Lam d L N)) : Set (Lam d L N)) :=
  locGen_mem P X Y _ fun z hz => ψ_mem_NX (a := (z, s)) (by simpa using hz)

theorem locEven_mem (P X Y : Finset (Lam d L N)) (F : Alg d L N) :
    locEven P X Y F ∈ NX ((Y ∩ P : Finset (Lam d L N)) : Set (Lam d L N)) :=
  add_mem (locGen_mem P X Y _ fun _ _ => one_mem _)
    (locGen_mem P X Y _ fun z hz => pbp_mem (by simpa using hz))

theorem inter_subset_nbhd {j : ℕ} {Y : Finset (Lam d L N)} (hY : IsPolymer j Y)
    (P : Finset (Lam d L N)) :
    ((Y ∩ P : Finset (Lam d L N)) : Set (Lam d L N)) ⊆ (nbhd j Y : Set (Lam d L N)) := by
  intro z hz
  exact subset_nbhd hY (mem_of_mem_inter_left (by simpa using hz))

/-! ### The image (Proposition `prop:Loc-obs` (iv)) -/

/-- (iv), even components: `loc_{X,B} F = u |B ∩ P| + r ∑_{z ∈ B ∩ P} ψ̄_z ψ_z`.  For `P = {a}` (Case (2),
`F_a`) this is `1_{a ∈ B} (γ + λ ψ̄_a ψ_a)`; for `P = {a, b}` it is a combination of `1`,
`ψ̄_a ψ_a` and `ψ̄_b ψ_b` at the points of `B ∩ {a, b}`. -/
theorem locEven_image (P X B : Finset (Lam d L N)) (F : Alg d L N) :
    ∃ u r : ℂ, locEven P X B F = (u * (B ∩ P).card) • (1 : Alg d L N) +
      r • ∑ z ∈ B ∩ P, pbp z := by
  refine ⟨ε F / ((X ∩ P).card : ℂ), mass2 F / ((X ∩ P).card : ℂ), ?_⟩
  simp only [locEven, locGen, sum_const, nsmul_eq_mul, Algebra.smul_def, map_mul, mul_one,
    map_natCast]

/-! ### Coefficients of the local monomials -/

section Coeff

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

theorem coeff_one_seq (F : Grassmann.N Λ) (a : Sf Λ) : coeff F ![a] = ε (D a F) := by
  simp only [coeff, Dseq, contr_succ, contr_zero]
  rfl

theorem ψ_eq_ιMulti (a : Sf Λ) : ψ a = ExteriorAlgebra.ιMulti ℂ 1 (fun _ => ev a) := by
  simp [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, ψ]

theorem coeff_ψ_of_ne (a : Sf Λ) {n : ℕ} (z : Fin n → Sf Λ) (hn : n ≠ 1) : coeff (ψ a) z = 0 := by
  rw [ψ_eq_ιMulti]; exact coeff_ιMulti_of_ne _ _ hn

theorem coeff_ψ_one (a b : Sf Λ) : coeff (ψ a) ![b] = if b = a then 1 else 0 := by
  rw [coeff_one_seq, D_ψ]; split_ifs <;> simp

theorem coeff_pbp_of_ne (z : Λ) {n : ℕ} (w : Fin n → Sf Λ) (hn : n ≠ 2) :
    coeff (psibar z * psi z) w = 0 := by
  rw [psibar_mul_psi_eq, psiPow]; exact coeff_ιMulti_of_ne _ _ hn

theorem coeff_pbp_same (z a a' : Λ) (σ : ℤˣ) :
    coeff (psibar z * psi z) ![(a, σ), (a', σ)] = 0 := by
  rw [psibar_mul_psi_eq, coeff_psiPow]
  refine sum_eq_zero fun τ _ => ?_
  rw [if_neg, mul_zero]
  intro h
  have hs : ∀ i : Fin 2, (![(a, σ), (a', σ)] i).2 = σ := by intro i; fin_cases i <;> rfl
  have e0 : (-1 : ℤˣ) = σ := by
    have := congrArg Prod.snd (congrFun h 0)
    simpa [hs] using this
  have e1 : (1 : ℤˣ) = σ := by
    have := congrArg Prod.snd (congrFun h 1)
    simpa [hs] using this
  exact absurd (e0.trans e1.symm) (by decide)

theorem coeff_pbp_mp (z u v : Λ) :
    coeff (psibar z * psi z) ![(u, -1), (v, 1)] = if u = z ∧ v = z then 1 else 0 := by
  rw [coeff_two]
  by_cases hu : u = z <;> by_cases hv : v = z <;>
    simp [D_mul, D_ψ, psi, psibar, Prod.ext_iff, hu, hv]

theorem coeff_psibar_psi_mp (x y u v : Λ) :
    coeff (psibar x * psi y) ![(u, -1), (v, 1)] = if u = x ∧ v = y then 1 else 0 := by
  rw [coeff_two]
  by_cases hu : u = x <;> by_cases hv : v = y <;>
    simp [D_mul, D_ψ, psi, psibar, Prod.ext_iff, hu, hv]

end Coeff

theorem mass1_ψ (s t : ℤˣ) (z : Lam d L N) : mass1 s (ψ (z, t)) = if s = t then 1 else 0 := by
  unfold mass1
  simp only [coeff_ψ_one, Prod.ext_iff]
  split_ifs with h
  · subst h; simp
  · simp [h]

theorem mass2_pbp (z : Lam d L N) : mass2 (pbp z) = 1 := by
  simp only [mass2, pbp, coeff_pbp_mp, ite_and]
  simp

theorem mass2_one : mass2 (1 : Alg d L N) = 0 := by
  simp [mass2, coeff_two]

theorem mass1_one (s : ℤˣ) : mass1 s (1 : Alg d L N) = 0 := by
  simp [mass1, coeff_one_seq]

theorem eps_pbp (z : Lam d L N) : ε (pbp z) = 0 := by
  simp [pbp, psibar, psi, ψ]

theorem eps_ψ (a : Sf (Lam d L N)) : ε (ψ a) = 0 := by simp [ψ]

/-! ### `Loc_X` reproduces the pairings -/

theorem card_inter_ne {P X : Finset (Lam d L N)} (h : (X ∩ P).Nonempty) :
    ((X ∩ P).card : ℂ) ≠ 0 := by exact_mod_cast h.card_pos.ne'

theorem mass1_locOdd {P X : Finset (Lam d L N)} (h : (X ∩ P).Nonempty) (s : ℤˣ) (F : Alg d L N) :
    mass1 s (locOdd s P X X F) = mass1 s F := by
  simp only [locOdd, locGen, mass1_smul]
  rw [show mass1 s (∑ z ∈ X ∩ P, ψ (z, s)) = ((X ∩ P).card : ℂ) by
    rw [show mass1 s (∑ z ∈ X ∩ P, ψ (z, s)) = ∑ z ∈ X ∩ P, mass1 s (ψ (z, s)) by
      simp [mass1, coeff_sum, sum_comm (s := (univ : Finset (Lam d L N)))]]
    simp [mass1_ψ]]
  field_simp [card_inter_ne h]

theorem mass1_locOdd_ne (s t : ℤˣ) (hst : t ≠ s) (P X Y : Finset (Lam d L N)) (F : Alg d L N) :
    mass1 t (locOdd s P X Y F) = 0 := by
  simp only [locOdd, locGen, mass1_smul]
  rw [show mass1 t (∑ z ∈ Y ∩ P, ψ (z, s)) = ∑ z ∈ Y ∩ P, mass1 t (ψ (z, s)) by
    simp [mass1, coeff_sum, sum_comm (s := (univ : Finset (Lam d L N)))]]
  simp [mass1_ψ, hst]

theorem sum_one_eq (A : Finset (Lam d L N)) :
    ∑ _z ∈ A, (1 : Alg d L N) = (A.card : ℂ) • (1 : Alg d L N) := by
  rw [sum_const, ← Nat.cast_smul_eq_nsmul ℂ]

theorem locGen_one (P X Y : Finset (Lam d L N)) (c : ℂ) :
    locGen P X Y (fun _ => 1) c = (c / ((X ∩ P).card : ℂ) * (Y ∩ P).card) • (1 : Alg d L N) := by
  rw [locGen, sum_one_eq, smul_smul]

theorem mass2_locEven {P X : Finset (Lam d L N)} (h : (X ∩ P).Nonempty) (F : Alg d L N) :
    mass2 (locEven P X X F) = mass2 F := by
  have hs : ∀ (f : Lam d L N → Alg d L N) (A : Finset (Lam d L N)),
      mass2 (∑ z ∈ A, f z) = ∑ z ∈ A, mass2 (f z) := fun f A => by
    simp [mass2, coeff_sum, sum_comm (s := A)]
  rw [locEven, locGen_one, mass2_add, mass2_smul, mass2_one, mul_zero, zero_add, locGen,
    mass2_smul, hs]
  simp only [mass2_pbp, sum_const, nsmul_eq_mul, mul_one]
  field_simp [card_inter_ne h]

theorem eps_locEven {P X : Finset (Lam d L N)} (h : (X ∩ P).Nonempty) (F : Alg d L N) :
    ε (locEven P X X F) = ε F := by
  rw [locEven, locGen_one, map_add, map_smul, map_one, locGen, map_smul, map_sum]
  simp only [eps_pbp, sum_const_zero, smul_eq_mul, mul_one, mul_zero, add_zero]
  field_simp [card_inter_ne h]

/-- The coefficients of `loc_{X,Y}` of an odd component vanish except on sequences of length
one. -/
theorem coeff_locOdd_of_ne (s : ℤˣ) (P X Y : Finset (Lam d L N)) (F : Alg d L N) {n : ℕ}
    (w : Fin n → Sf (Lam d L N)) (hn : n ≠ 1) : coeff (locOdd s P X Y F) w = 0 := by
  simp [locOdd, locGen, coeff_smul, coeff_sum, coeff_ψ_of_ne _ w hn]

theorem coeff_one_of_ne' {n : ℕ} (w : Fin n → Sf (Lam d L N)) (hn0 : n ≠ 0) :
    coeff (1 : Alg d L N) w = 0 := by
  have : (1 : Alg d L N) = ExteriorAlgebra.ιMulti ℂ 0 (Fin.elim0 : Fin 0 → V (Lam d L N)) := by
    simp [ExteriorAlgebra.ιMulti_zero_apply]
  rw [this]; exact coeff_ιMulti_of_ne _ _ hn0

theorem coeff_locEven_of_ne (P X Y : Finset (Lam d L N)) (F : Alg d L N) {n : ℕ}
    (w : Fin n → Sf (Lam d L N)) (hn0 : n ≠ 0) (hn2 : n ≠ 2) : coeff (locEven P X Y F) w = 0 := by
  rw [locEven, locGen_one, coeff_add, coeff_smul, coeff_one_of_ne' w hn0, locGen, coeff_smul,
    coeff_sum]
  simp [pbp, coeff_pbp_of_ne _ w hn2]

theorem coeff_locEven_same (P X Y : Finset (Lam d L N)) (F : Alg d L N) (x y : Lam d L N)
    (σ : ℤˣ) : coeff (locEven P X Y F) ![(x, σ), (y, σ)] = 0 := by
  rw [locEven, locGen_one, coeff_add, coeff_smul, coeff_one_of_ne' _ (by norm_num), locGen,
    coeff_smul, coeff_sum]
  simp [pbp, coeff_pbp_same]

/-! ### Example (ii) (`e:ex-Locobs`) -/

theorem locOdd_single_self (s : ℤˣ) (a : Lam d L N) (X : Finset (Lam d L N)) (F : Alg d L N) :
    locOdd s {a} X X F = if a ∈ X then mass1 s F • ψ (a, s) else 0 := by
  unfold locOdd locGen
  split_ifs with h
  · rw [inter_singleton_of_mem h, sum_singleton, card_singleton]
    simp
  · rw [inter_singleton_of_notMem h]; simp

theorem mass1_psibar (x : Lam d L N) : mass1 (-1) (psibar x) = 1 := by
  have := mass1_ψ (-1) (-1) x; rw [if_pos rfl] at this; exact this

theorem mass1_psi (x : Lam d L N) : mass1 1 (psi x) = 1 := by
  have := mass1_ψ 1 1 x; rw [if_pos rfl] at this; exact this

theorem mass2_psibar_psi (x y : Lam d L N) : mass2 (psibar x * psi y) = 1 := by
  simp only [mass2, coeff_psibar_psi_mp, ite_and]
  simp

end

end Obs.LocObs
