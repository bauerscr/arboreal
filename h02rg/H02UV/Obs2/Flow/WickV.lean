import Obs2.Flow.WickPair

/-!
# The mass coefficients of `F_C(observable vertex, V_κ(Λ))` (`lem:second` (ii), (iii))

For the bulk coupling polynomial `V_κ(Λ)` (`Vcoup κ univ`, `κ = (z, y, ν, g)`) and **any** complex
covariance `C` (no symmetry or translation invariance needed; the lattice sums are over the whole
torus):

* Case (1), `mass1_FC_psibar_Vcoup`: `m₁ F_C(ψ̄_a, V_κ(Λ)) = ν ∑_x C(a, x)`.
  The gradient monomials and the quartic monomial do not contribute (`lem:second`(iii)).
* Case (2), `mass2_FC_pbp_Vcoup`:
  `m₂ F_C(ψ̄_aψ_a, V_κ(Λ)) = ν (∑_x C(a, x) + ∑_x C(x, a)) - g 𝔩_C(a)`, with
  `𝔩_C(a) = ∑_i ∑_z ½ ∑_{e = ±e_i} (C(a, z+e) - C(a, z)) (C(z+e, a) - C(z, a))` (`lfunC`), the
  double contraction (bubble) of `ψ̄_aψ_a` with the two gradient legs of `M̂`
  (`lem:second`(ii)). For a symmetric translation-invariant `C`, summation by parts gives
  `𝔩_C(a) = ∑_x C(0,x) ((-Δ)C)(x,0) = 𝔩(C)`.

Pair values: `m₁ F_C(ψ̄_a, ψ_sψ̄_t) = C(a, s)` (`mass1_FC_psibar_pair`),
`m₂ F_C(ψ̄_aψ_a, ψ_sψ̄_t) = C(t, a) + C(a, s)` (`mass2_FC_pbp_pair`),
`m₂ F_C(ψ̄_aψ_a, (∇_eψ)(∇_{e'}ψ̄)ψψ̄_z) = -(C(a,z+e) - C(a,z))(C(z+e',a) - C(z,a))`
(`mass2_FC_pbp_gmono4`).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Loc Step Step2 LocObs

variable {d L N : ℕ} [NeZero L] (C : Matrix (Lam d L N) (Lam d L N) ℂ)

local notation "ι" => (ExteriorAlgebra.ι ℂ : V (Lam d L N) →ₗ[ℂ] Alg d L N)

/-! ### Coefficients of products of linear forms -/

/-- `∑_x v(x, +)`. -/
def Sp (v : V (Lam d L N)) : ℂ := ∑ x, v (x, 1)
/-- `∑_x v(x, -)`. -/
def Sm (v : V (Lam d L N)) : ℂ := ∑ x, v (x, -1)

theorem coeff_ιι (p q : V (Lam d L N)) (b c : Sf (Lam d L N)) :
    coeff (ι p * ι q) ![b, c] = p b * q c - q b * p c := by
  rw [coeff_two, D_pair, D_ι, AlgHom.commutes]
  simp

theorem mass2_ιι (p q : V (Lam d L N)) : mass2 (ι p * ι q) = Sm p * Sp q - Sm q * Sp p := by
  unfold mass2 Sp Sm
  simp only [coeff_ιι, sum_sub_distrib, sum_mul_sum]

theorem isHom_ι (v : V (Lam d L N)) : IsHom 1 (ι v) := by
  have e : (ι v : Alg d L N) = ExteriorAlgebra.ιMulti ℂ 1 (fun _ => v) := by
    simp [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply]
  rw [e]
  exact fun m z h => coeff_ιMulti_of_ne _ z h

theorem mass2_of_isHom {n : ℕ} {F : Alg d L N} (hF : IsHom n F) (hn : n ≠ 2) : mass2 F = 0 := by
  unfold mass2
  exact sum_eq_zero fun x _ => sum_eq_zero fun y _ => hF 2 _ (Ne.symm hn)

theorem mass2_neg (F : Alg d L N) : mass2 (-F) = -mass2 F := by
  have := mass2_smul (-1 : ℂ) F; simpa using this

theorem mass2_D_D_ι (p : V (Lam d L N)) (q : V (Lam d L N)) (x y : Lam d L N) :
    mass2 (D (x, -1) (D (y, 1) (ι p * ι q))) = 0 := by
  rw [D_pair, D_ι, mass2_algebraMap]

/-! ### Case (1) -/

theorem mass1_FC_psibar_pair (a s t : Lam d L N) :
    mass1 (-1) (FC C (psibar a) (psi s * psibar t)) = C a s := by
  rw [mass1_FC_psibar]
  have e : (psi s * psibar t : Alg d L N) = ι (ev ((s, 1) : Sf (Lam d L N))) * ι (ev (t, -1)) :=
    rfl
  simp only [e, coeff_ιι]
  simp [ev, Pi.single_apply, Prod.ext_iff]

/-! ### Case (2) -/

theorem mass2_psibar_ι (a : Lam d L N) (v : V (Lam d L N)) : mass2 (psibar a * ι v) = Sp v := by
  have e : (psibar a : Alg d L N) = ι (ev ((a, -1) : Sf (Lam d L N))) := rfl
  rw [e, mass2_ιι]
  simp [Sm, Sp, ev, Pi.single_apply, Prod.ext_iff]

theorem mass2_psi_ι (a : Lam d L N) (v : V (Lam d L N)) : mass2 (psi a * ι v) = -Sm v := by
  have e : (psi a : Alg d L N) = ι (ev ((a, 1) : Sf (Lam d L N))) := rfl
  rw [e, mass2_ιι]
  simp [Sm, Sp, ev, Pi.single_apply, Prod.ext_iff]

theorem mass2_X2_pbp (a : Lam d L N) (B : Alg d L N) :
    (1 / 2 : ℂ) * mass2 (X2 C (psibar a * psi a) B) =
      ∑ x, ∑ y, (C x a * C a y) * mass2 (D (x, -1) (D (y, 1) B)) := by
  have hc : ∀ x y : Lam d L N, D (y, 1) (D (x, -1) B) = -D (x, -1) (D (y, 1) B) :=
    fun x y => D_comm _ _ _
  rw [X2_pbp1, mass2_add, mass2_sum, mass2_sum]
  simp only [mass2_smul, Xc_psi, Xc_psibar, mass2_neg, mass2_sum, hc]
  have e1 : ∑ y, C a y * ∑ x, C x a * mass2 (D (x, -1) (D (y, 1) B)) =
      ∑ x, ∑ y, (C x a * C a y) * mass2 (D (x, -1) (D (y, 1) B)) := by
    simp only [mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => by ring
  have e2 : ∑ x, C x a * -∑ y, C a y * -mass2 (D (x, -1) (D (y, 1) B)) =
      ∑ x, ∑ y, (C x a * C a y) * mass2 (D (x, -1) (D (y, 1) B)) := by
    simp only [mul_neg, sum_neg_distrib, neg_neg, mul_sum]
    exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => by ring
  rw [e1, e2]
  ring

theorem mass2_FC_pbp_split (a : Lam d L N) (B : Alg d L N) :
    mass2 (FC C (pbp a) B) = -(∑ x, C x a * mass2 (psibar a * D (x, -1) B)) -
      ∑ y, C a y * mass2 (psi a * D (y, 1) B) +
      ∑ x, ∑ y, (C x a * C a y) * mass2 (D (x, -1) (D (y, 1) B)) := by
  rw [pbp, FC_pbp', mass2_add, mass2_smul, mass2_X2_pbp, Xc_pbp]
  simp only [mass2_sub, mass2_neg, mass2_sum, mass2_smul]

theorem mass2_FC_pbp_pair (a s t : Lam d L N) :
    mass2 (FC C (pbp a) (psi s * psibar t)) = C t a + C a s := by
  have e : (psi s * psibar t : Alg d L N) = ι (ev ((s, 1) : Sf (Lam d L N))) * ι (ev (t, -1)) :=
    rfl
  rw [mass2_FC_pbp_split, e]
  simp only [mass2_D_D_ι, mul_zero, sum_const_zero, add_zero]
  simp only [D_pair, mass2_psibar_ι, mass2_psi_ι]
  simp [Sm, Sp, ev, Pi.single_apply, Prod.ext_iff, ite_apply, mul_ite, sum_ite_eq, sum_ite_eq']

/-- The quartic double contraction for four linear forms of spins `+, -, +, -`. -/
theorem mass2_DD_four {a b c e : V (Lam d L N)} (ha : ∀ y, a (y, -1) = 0)
    (hb : ∀ y, b (y, 1) = 0) (hc : ∀ y, c (y, -1) = 0) (he : ∀ y, e (y, 1) = 0)
    (x y : Lam d L N) :
    mass2 (D (x, -1) (D (y, 1) (ι a * (ι b * (ι c * ι e))))) =
      a (y, 1) * b (x, -1) * (-(Sm e * Sp c)) + a (y, 1) * e (x, -1) * (Sm b * Sp c) +
        c (y, 1) * b (x, -1) * (Sm e * Sp a) + c (y, 1) * e (x, -1) * (-(Sm b * Sp a)) := by
  have hSmc : Sm c = 0 := by unfold Sm; simp [hc]
  have hSpe : Sp e = 0 := by unfold Sp; simp [he]
  have hSma : Sm a = 0 := by unfold Sm; simp [ha]
  have hSpb : Sp b = 0 := by unfold Sp; simp [hb]
  have e1 : D (y, 1) (ι a * (ι b * (ι c * ι e))) =
      a (y, 1) • (ι b * (ι c * ι e)) + c (y, 1) • (ι a * (ι b * ι e)) := by
    rw [D_ι_mul, D_ι_mul, D_pair, hb, he]
    simp only [zero_smul, zero_sub, sub_zero, map_smul, mul_smul_comm, mul_neg, neg_neg,
      sub_neg_eq_add]
  have e2 : D (x, -1) (ι b * (ι c * ι e)) = b (x, -1) • (ι c * ι e) + e (x, -1) • (ι b * ι c) := by
    rw [D_ι_mul, D_pair, hc]
    simp only [zero_smul, zero_sub, map_neg, map_smul, mul_neg, mul_smul_comm, sub_neg_eq_add]
  have e3 : D (x, -1) (ι a * (ι b * ι e)) =
      -(b (x, -1) • (ι a * ι e)) + e (x, -1) • (ι a * ι b) := by
    rw [D_ι_mul, D_pair, ha]
    simp only [zero_smul, zero_sub, map_sub, map_smul, mul_sub, mul_smul_comm]
    abel
  rw [e1, map_add, map_smul, map_smul, e2, e3]
  simp only [mass2_add, mass2_smul, mass2_neg, mass2_ιι, hSmc, hSpe, hSma, hSpb]
  ring

theorem gmono4_ι (e e' : Dir d) (z : Lam d L N) :
    gmono4 e e' z = ι (v4g e e' z 0) * (ι (v4g e e' z 1) * (ι (v4g e e' z 2) * ι (v4g e e' z 3))) := by
  simp [gmono4, v4g, ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply,
    Matrix.vecTail]

theorem Sp_v4g2 (e e' : Dir d) (z : Lam d L N) : Sp (v4g e e' z 2) = 1 := by
  simp [Sp, v4g, ev, Pi.single_apply, Prod.ext_iff]

theorem Sm_v4g3 (e e' : Dir d) (z : Lam d L N) : Sm (v4g e e' z 3) = 1 := by
  simp [Sm, v4g, ev, Pi.single_apply, Prod.ext_iff]

theorem Sp_v4g0 (e e' : Dir d) (z : Lam d L N) : Sp (v4g e e' z 0) = 0 := by
  simp [Sp, v4g, ev, Pi.single_apply, Prod.ext_iff, sum_sub_distrib]

theorem Sm_v4g1 (e e' : Dir d) (z : Lam d L N) : Sm (v4g e e' z 1) = 0 := by
  simp [Sm, v4g, ev, Pi.single_apply, Prod.ext_iff, sum_sub_distrib]

theorem mass2_DD_gmono4 (e e' : Dir d) (z x y : Lam d L N) :
    mass2 (D (x, -1) (D (y, 1) (gmono4 e e' z))) = -(v4g e e' z 0 (y, 1) * v4g e e' z 1 (x, -1)) := by
  rw [gmono4_ι, mass2_DD_four (v4g_pos0 e e' z) (v4g_neg1 e e' z) (v4g_pos2 e e' z)
    (v4g_neg3 e e' z), Sp_v4g2, Sm_v4g3, Sp_v4g0, Sm_v4g1]
  ring

theorem isHom_Xc_part (a : Lam d L N) (s : ℤˣ) (u : Lam d L N) {P : Alg d L N} (hP : IsHom 1 P)
    {B : Alg d L N} (hB : IsHom 4 B) : mass2 (P * D (u, s) B) = 0 :=
  mass2_of_isHom (hP.mul (hB.D (u, s))) (by norm_num)

/-- **The bubble of `ψ̄_aψ_a` with the quartic monomial.** -/
theorem mass2_FC_pbp_gmono4 (a : Lam d L N) (e e' : Dir d) (z : Lam d L N) :
    mass2 (FC C (pbp a) (gmono4 e e' z)) =
      -((C a (z + dirVec e) - C a z) * (C (z + dirVec e') a - C z a)) := by
  have hB := isHom_gmono4 e e' z
  have h1 : (psibar a : Alg d L N) = ι (ev ((a, -1) : Sf (Lam d L N))) := rfl
  have h2 : (psi a : Alg d L N) = ι (ev ((a, 1) : Sf (Lam d L N))) := rfl
  have z1 : ∑ x, C x a * mass2 (psibar a * D (x, -1) (gmono4 e e' z)) = 0 :=
    sum_eq_zero fun x _ => by rw [h1, isHom_Xc_part a (-1) x (isHom_ι _) hB, mul_zero]
  have z2 : ∑ y, C a y * mass2 (psi a * D (y, 1) (gmono4 e e' z)) = 0 :=
    sum_eq_zero fun y _ => by rw [h2, isHom_Xc_part a 1 y (isHom_ι _) hB, mul_zero]
  have sA : ∑ y, C a y * v4g e e' z 0 (y, 1) = C a (z + dirVec e) - C a z := by
    simp [v4g, ev, Pi.single_apply, Prod.ext_iff, mul_sub, sum_sub_distrib]
  have sB : ∑ x, C x a * v4g e e' z 1 (x, -1) = C (z + dirVec e') a - C z a := by
    simp [v4g, ev, Pi.single_apply, Prod.ext_iff, mul_sub, sum_sub_distrib]
  have e3 : ∑ x, ∑ y, C x a * C a y * -(v4g e e' z 0 (y, 1) * v4g e e' z 1 (x, -1)) =
      -((∑ x, C x a * v4g e e' z 1 (x, -1)) * (∑ y, C a y * v4g e e' z 0 (y, 1))) := by
    rw [sum_mul_sum, ← sum_neg_distrib]
    refine sum_congr rfl fun x _ => ?_
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun y _ => by ring
  rw [mass2_FC_pbp_split]
  simp only [mass2_DD_gmono4]
  rw [z1, z2, e3, sA, sB]
  ring

end

end Obs2
