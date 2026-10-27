import Loc.Stencil
import Loc.PolymerGeom

/-!
# Definition of the localisation operators

For `X ⊆ Λ` with base point `b = base X` and lifted coordinates `ℓ(x) = r(x - b) ∈ ℤ^d ⊆ ℝ^d`:

* `mu b β F = ∑_{x,y} F_{(x,+)(y,-)} Q_β(ℓ x, ℓ y)` is the pairing of the `ψψ̄` part of `F` with
  the test polynomial `Q_β`;
* `monoSet M X = ∑_{x ∈ X} M_x ∈ 𝒩(Λ)` is the local polynomial of the monomial `M`;
* `Amat X` is the matrix of pairings `(M, β) ↦ mu (monoSet M X) β`, which is invertible (it is
  `|X|` times a unipotent matrix, by the moment identity);
* `LocXY X Y F = (F_∅ |Y|/|X|) + ∑_M c_M(F) M(Y)`, where the coefficients `c(F) = mu(F) A_X^{-1}`
  are the unique ones for which `LocXY X X F` has the same pairings with all test polynomials as
  `F` (`mu_LocX`); `LocX X = LocXY X X`.

The constant term `F_∅` of `F` is reproduced exactly; the parts of `F` with more fields, or with
unequal numbers of `ψ` and `ψ̄`, are annihilated.

Scalars: `cf2`, `mu`, `Amat`, `locCoef` are complex; the stencil weights and the test polynomials
`Qpoly` are real (`Loc.Stencil`) and enter via the cast `ℝ → ℂ`.
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD Matrix

variable {d L N : ℕ} [NeZero L]

/-- Lifted coordinates relative to the base point `b`. -/
def lift (b x : Lam d L N) : Fin d → ℝ := fun i => (rep (x - b) i : ℝ)

/-- The coefficient `F_{(x,+)(y,-)}` of `ψ_x ψ̄_y` in `F`. -/
def cf2 (F : Alg d L N) (x y : Lam d L N) : ℂ := coeff F ![(x, 1), (y, -1)]

/-- The pairing of the `ψψ̄`-part of `F` with the test polynomial `Q_β` in coordinates based
at `b`. -/
def mu (b : Lam d L N) (β : Mono d) (F : Alg d L N) : ℂ :=
  ∑ x, ∑ y, cf2 F x y * (Qpoly β (lift b x) (lift b y) : ℂ)

/-- The monomial `M` at the point `x`: `M_x = ∑ c ψ_{x+a} ψ̄_{x+b}`. -/
def monoAt (M : Mono d) (x : Lam d L N) : Alg d L N :=
  ((stencil M).map fun p => (p.1 : ℂ) • (psi (x + prj p.2.1) * psibar (x + prj p.2.2))).sum

/-- The local polynomial `M(X) = ∑_{x ∈ X} M_x`. -/
def monoSet (M : Mono d) (X : Finset (Lam d L N)) : Alg d L N := ∑ x ∈ X, monoAt M x

/-- A base point of `X`. -/
def base (X : Finset (Lam d L N)) : Lam d L N := if h : X.Nonempty then h.choose else 0

/-- The matrix of pairings of the local monomials on `X` with the test polynomials. -/
def Amat (X : Finset (Lam d L N)) : Matrix (Mono d) (Mono d) ℂ :=
  fun M β => mu (base X) β (monoSet M X)

/-- The coefficients of the localisation of `F` on `X`. -/
def locCoef (X : Finset (Lam d L N)) (F : Alg d L N) : Mono d → ℂ :=
  (fun β => mu (base X) β F) ᵥ* (Amat X)⁻¹

/-- `Loc_{X,Y} F = F_∅ |Y|/|X| + ∑_M c_M(F) M(Y)`. -/
def LocXY (X Y : Finset (Lam d L N)) (F : Alg d L N) : Alg d L N :=
  (ε F * Y.card / X.card) • (1 : Alg d L N) + ∑ M, locCoef X F M • monoSet M Y

/-- `Loc_X = Loc_{X,X}`. -/
def LocX (X : Finset (Lam d L N)) (F : Alg d L N) : Alg d L N := LocXY X X F

/-! ### Linearity -/

theorem cf2_add (F G : Alg d L N) (x y : Lam d L N) : cf2 (F + G) x y = cf2 F x y + cf2 G x y :=
  coeff_add _ _ _

theorem cf2_smul (r : ℂ) (F : Alg d L N) (x y : Lam d L N) : cf2 (r • F) x y = r * cf2 F x y :=
  coeff_smul _ _ _

theorem mu_add (b : Lam d L N) (β : Mono d) (F G : Alg d L N) :
    mu b β (F + G) = mu b β F + mu b β G := by
  simp only [mu, cf2_add, add_mul, sum_add_distrib]

theorem mu_smul (b : Lam d L N) (β : Mono d) (r : ℂ) (F : Alg d L N) :
    mu b β (r • F) = r * mu b β F := by
  simp only [mu, cf2_smul, mul_sum]; refine sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

theorem mu_sum {ι : Type*} (s : Finset ι) (b : Lam d L N) (β : Mono d) (F : ι → Alg d L N) :
    mu b β (∑ i ∈ s, F i) = ∑ i ∈ s, mu b β (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mu, cf2]
  | insert i s hi ih => rw [sum_insert hi, mu_add, ih, sum_insert hi]

theorem mu_one (b : Lam d L N) (β : Mono d) : mu b β (1 : Alg d L N) = 0 := by
  simp [mu, cf2, coeff_two]

/-! ### Pairings of local monomials -/

theorem cf2_psi_psibar (u v x y : Lam d L N) :
    cf2 (psi u * psibar v) x y = if x = u ∧ y = v then 1 else 0 := by
  rw [cf2, coeff_two]
  by_cases hx : x = u <;> by_cases hy : y = v <;>
    simp [D_mul, D_ψ, psi, psibar, Prod.ext_iff, hx, hy]

theorem mu_list_sum (b : Lam d L N) (β : Mono d) {α : Type*} (l : List α) (f : α → Alg d L N) :
    mu b β (l.map f).sum = (l.map fun a => mu b β (f a)).sum := by
  induction l with
  | nil => simp [mu, cf2]
  | cons a l ih => simp [mu_add, ih]

theorem mu_psi_psibar (b : Lam d L N) (β : Mono d) (u v : Lam d L N) :
    mu b β (psi u * psibar v) = (Qpoly β (lift b u) (lift b v) : ℂ) := by
  simp only [mu, cf2_psi_psibar, ite_mul, one_mul, zero_mul]
  rw [sum_eq_single u (fun x _ hx => sum_eq_zero fun y _ => by simp [hx]) (by simp)]
  rw [sum_eq_single v (fun y _ hy => by simp [hy]) (by simp)]
  simp

theorem mu_monoAt (b : Lam d L N) (β : Mono d) (M : Mono d) (x : Lam d L N) :
    mu b β (monoAt M x) = (((stencil M).map fun p =>
      p.1 * Qpoly β (lift b (x + prj p.2.1)) (lift b (x + prj p.2.2))).sum : ℝ) := by
  rw [monoAt, mu_list_sum]
  conv_rhs => rw [← Complex.ofRealHom_eq_coe, map_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun p _ => ?_
  rw [Function.comp_apply, mu_smul, mu_psi_psibar, Complex.ofRealHom_eq_coe, Complex.ofReal_mul]

/-! ### Lifted coordinates in a patch -/

theorem supNormZ_rep_eq {n : ℕ} [NeZero n] (y : Torus d n) : supNormZ (rep y) = supNorm y := by
  unfold supNormZ supNorm
  congr 1; funext i; exact natAbs_rep y i

/-- Lifts are affine in a patch: `ℓ(x + a) = ℓ(x) + a`. -/
theorem lift_add {b x : Lam d L N} {a : Zd d} (h : 2 * (supNorm (x - b) + supNormZ a) < L ^ N) :
    lift b (x + prj a) = lift b x + fun i => (a i : ℝ) := by
  have hz : rep (x + prj a - b) = rep (x - b) + a := by
    symm
    refine eq_rep ?_ ?_
    · rw [prj_add, prj_rep]; abel
    · have := supNormZ_add_le (rep (x - b)) a
      rw [supNormZ_rep_eq] at this
      omega
  funext i
  simp [lift, hz]

/-- The patch condition for `X`: all points are within `n/2 - 1` of the base point. -/
def Patch (X : Finset (Lam d L N)) : Prop := ∀ x ∈ X, 2 * (supNorm (x - base X) + 1) < L ^ N

theorem supNormZ_ez (i : Fin d) : supNormZ (ez i) ≤ 1 := by
  rw [supNormZ_le_iff]; intro j; by_cases h : j = i <;> simp [ez, Pi.single_apply, h]

theorem supNormZ_neg (z : Zd d) : supNormZ (-z) = supNormZ z := by
  simp [supNormZ]

theorem supNormZ_zero : supNormZ (0 : Zd d) = 0 := by simp [supNormZ]

/-- A 1-d stencil with all offsets of size `≤ 1`. -/
def Small1 (s : St1 d) : Prop := ∀ p ∈ s, supNormZ p.2 ≤ 1

theorem small1_id1 : Small1 (id1 : St1 d) := by
  intro p hp; simp [id1] at hp; subst hp; simp [supNormZ_zero]

theorem small1_dpt (i : Fin d) : Small1 (dpt i) := by
  intro p hp; simp [dpt] at hp
  rcases hp with rfl | rfl
  · exact supNormZ_ez i
  · simpa [supNormZ_neg] using supNormZ_ez i

theorem small1_lap1 (i : Fin d) : Small1 (lap1 i) := by
  intro p hp; simp [lap1] at hp
  rcases hp with rfl | rfl | rfl
  · exact supNormZ_ez i
  · simpa [supNormZ_neg] using supNormZ_ez i
  · simp [supNormZ_zero]

theorem small1_fw {v : Zd d} (hv : supNormZ v ≤ 1) : Small1 (fw v) := by
  intro p hp; simp [fw] at hp
  rcases hp with rfl | rfl
  · exact hv
  · simp [supNormZ_zero]

theorem small1_conv_dpt {i k : Fin d} (hik : i ≠ k) : Small1 (conv (dpt i) (dpt k)) := by
  intro p hp
  simp only [conv, dpt, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.append_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  rw [supNormZ_le_iff]
  intro j
  rcases hp with rfl | rfl | rfl | rfl <;>
    by_cases h1 : j = i <;> by_cases h2 : j = k <;> simp_all [ez, Pi.single_apply]

theorem small1_Dsym (s : Sym2 (Fin d)) : Small1 (Dsym s) := by
  induction s using Sym2.ind with
  | h i k =>
    simp only [Dsym, Sym2.lift_mk, Dik]
    split_ifs with h
    · exact small1_lap1 _
    · exact small1_conv_dpt h

theorem tens_offsets {s t : St1 d} (hs : Small1 s) (ht : Small1 t) :
    ∀ p ∈ tens s t, supNormZ p.2.1 ≤ 1 ∧ supNormZ p.2.2 ≤ 1 := by
  intro p hp
  simp only [tens, List.mem_flatMap, List.mem_map] at hp
  obtain ⟨q, hq, r, hr, rfl⟩ := hp
  exact ⟨hs q hq, ht r hr⟩

/-- All offsets of the stencils have `|a|_∞ ≤ 1`. -/
theorem stencil_offsets (M : Mono d) : ∀ p ∈ stencil M, supNormZ p.2.1 ≤ 1 ∧ supNormZ p.2.2 ≤ 1 := by
  cases M with
  | c => exact tens_offsets small1_id1 small1_id1
  | a1 i => exact tens_offsets (small1_dpt i) small1_id1
  | b1 i => exact tens_offsets small1_id1 (small1_dpt i)
  | a2 s => exact tens_offsets (small1_Dsym s) small1_id1
  | b2 s => exact tens_offsets small1_id1 (small1_Dsym s)
  | m2 i k =>
    simp only [stencil]
    split_ifs with h
    · intro p hp
      simp only [sc, List.mem_map, List.mem_append] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      have he := supNormZ_ez i
      have hne : supNormZ (-ez i) ≤ 1 := by rw [supNormZ_neg]; exact he
      rcases hq with hq | hq
      · exact tens_offsets (small1_fw he) (small1_fw he) q hq
      · exact tens_offsets (small1_fw hne) (small1_fw hne) q hq
    · exact tens_offsets (small1_dpt i) (small1_dpt k)

theorem mu_monoAt_eq {X : Finset (Lam d L N)} (hX : Patch X) {x : Lam d L N} (hx : x ∈ X)
    (β M : Mono d) :
    mu (base X) β (monoAt M x) =
      (applySt (stencil M) (Qpoly β) (lift (base X) x) (lift (base X) x) : ℂ) := by
  rw [mu_monoAt, applySt]
  congr 2
  refine List.map_congr_left fun p hp => ?_
  have hb := stencil_offsets M p hp
  have h0 := hX x hx
  rw [lift_add (by omega), lift_add (by omega)]

/-- `A_X(M, β) = |X| δ_{Mβ}` for `deg β ≤ deg M`. -/
theorem Amat_eq {X : Finset (Lam d L N)} (hX : Patch X) {M β : Mono d} (h : β.deg ≤ M.deg) :
    Amat X M β = if β = M then (X.card : ℂ) else 0 := by
  rw [Amat, monoSet, mu_sum, sum_congr rfl fun x hx => by rw [mu_monoAt_eq hX hx, moment M β h]]
  split_ifs <;> simp

theorem Amat_isUnit {X : Finset (Lam d L N)} (hX : Patch X) (hne : X.Nonempty) :
    IsUnit (Amat X) := by
  rw [← vecMul_injective_iff_isUnit]
  have hc : (X.card : ℂ) ≠ 0 := by exact_mod_cast hne.card_pos.ne'
  have key : ∀ c : Mono d → ℂ, c ᵥ* Amat X = 0 → ∀ k : ℕ, ∀ M : Mono d, M.deg = k → c M = 0 := by
    intro c hc0 k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro M hM
      have h1 := congrFun hc0 M
      simp only [vecMul, dotProduct, Pi.zero_apply] at h1
      rw [sum_eq_single M] at h1
      · rw [Amat_eq hX (by omega), if_pos rfl] at h1
        exact (mul_eq_zero.1 h1).resolve_right hc
      · intro M' _ hM'
        rcases lt_or_ge M'.deg k with hlt | hge
        · rw [ih _ hlt M' rfl, zero_mul]
        · rw [Amat_eq hX (by omega), if_neg (Ne.symm hM'), mul_zero]
      · simp
  intro c c' hcc
  have hcc' : c ᵥ* Amat X = c' ᵥ* Amat X := hcc
  have : (c - c') ᵥ* Amat X = 0 := by rw [sub_vecMul, hcc', sub_self]
  funext M
  exact sub_eq_zero.1 (key _ this _ M rfl)

/-! ### The defining property -/

theorem mu_monoSet_vecMul (X Y : Finset (Lam d L N)) (c : Mono d → ℂ) (β : Mono d) :
    mu (base X) β (∑ M, c M • monoSet M Y) = ∑ M, c M * mu (base X) β (monoSet M Y) := by
  rw [mu_sum]; simp only [mu_smul]

/-- `Loc_X F` has the same pairings with the test polynomials as `F`. -/
theorem mu_LocX {X : Finset (Lam d L N)} (hX : Patch X) (hne : X.Nonempty) (F : Alg d L N)
    (β : Mono d) : mu (base X) β (LocX X F) = mu (base X) β F := by
  rw [LocX, LocXY, mu_add, mu_smul, mu_one, mul_zero, zero_add, mu_monoSet_vecMul]
  have h1 : (∑ M, locCoef X F M * mu (base X) β (monoSet M X)) = (locCoef X F ᵥ* Amat X) β := rfl
  rw [h1, locCoef, vecMul_vecMul,
    nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (Amat_isUnit hX hne)), vecMul_one]

end

end Loc
