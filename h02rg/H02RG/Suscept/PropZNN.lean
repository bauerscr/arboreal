import Suscept.ZNN

/-!
# Proposition `prop:ZNN`: `e:ZNN`

Restricted to constant fields, `V_N(Λ) = |Λ| a_N ψψ̄` (`Rc_eval`), `e^{-V_N(Λ)} = 1 - |Λ| a_N ψψ̄`,
`K_N(Λ) = k_N^0 + k_N^2 ψψ̄` (`Rc_even`), and with the Wick formula
`𝔼_{t_N Q_N} θ (ψψ̄) = ψψ̄ - t_N/|Λ|` this gives
`Z̃_{N,N} = 1 + ũ_{N,N} - |Λ| ã_{N,N} ψψ̄` (`prop_ZNN`).
-/

namespace Suscept

noncomputable section

open Finset Grassmann Loc FRD Step Flow

variable {d L : ℕ} [NeZero L]

local notation "Rl" N => Rc (Lam d L N)
local notation "PP" N => psiC (Lam d L N) * psibarC (Lam d L N)

theorem Rc_grad {N : ℕ} (e : Dir d) (x : Lam d L N) : (Rl N) (grad e x) = 0 := by
  simp [grad]

theorem Rc_gradbar {N : ℕ} (e : Dir d) (x : Lam d L N) : (Rl N) (gradbar e x) = 0 := by
  simp [gradbar]

theorem Rc_lapPsi {N : ℕ} (x : Lam d L N) : (Rl N) (lapPsi x) = 0 := by
  simp [lapPsi, Rc_grad]

theorem Rc_lapPsibar {N : ℕ} (x : Lam d L N) : (Rl N) (lapPsibar x) = 0 := by
  simp [lapPsibar, Rc_gradbar]

theorem Rc_gradSq {N : ℕ} (x : Lam d L N) : (Rl N) (gradSq x) = 0 := by
  simp [gradSq, Rc_grad]

/-- Restricted to constant fields, `V(Λ) = |Λ| a ψψ̄`. -/
theorem Rc_eval {N : ℕ} (V : Vcoup) :
    (Rl N) (V.eval (univ : Finset (Lam d L N))) =
      ((Fintype.card (Lam d L N) : ℂ) * V.a) • (PP N) := by
  simp only [Vcoup.eval, map_sum, _root_.map_add, map_smul, map_mul, map_neg, Rc_gradSq, Rc_lapPsi,
    Rc_lapPsibar, Rc_psi, Rc_psibar, smul_zero, mul_zero, zero_mul, neg_zero, add_zero, zero_add,
    sum_const, card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]

/-- Restricted to constant fields, `e^{-V(Λ)} = 1 - |Λ| a ψψ̄`. -/
theorem Rc_gexp_VE {N : ℕ} (V : Vcoup) :
    (Rl N) ((gexp (-(VE V (univ : Finset (Lam d L N)) : EvR (Lam d L N))) : EvR (Lam d L N)) :
      Alg d L N) = 1 - ((Fintype.card (Lam d L N) : ℂ) * V.a) • (PP N) := by
  set RE : EvR (Lam d L N) →ₐ[ℂ] EvR (Lam d L N) := mapE (avgV (Lam d L N))
  have hRE : ∀ x : EvR (Lam d L N), (RE x : Alg d L N) = (Rl N) x := fun x => rfl
  rw [← hRE, gexp, IsNilpotent.map_exp (isNilpotent_VE V univ).neg RE, map_neg]
  set y : EvR (Lam d L N) := -RE (VE V univ) with hy
  have hy' : (y : Alg d L N) = -(((Fintype.card (Lam d L N) : ℂ) * V.a) • (PP N)) := by
    rw [hy, Subalgebra.coe_neg, hRE]
    exact congrArg Neg.neg (Rc_eval V)
  have hy2 : y ^ 2 = 0 := by
    refine Subtype.ext ?_
    rw [SubmonoidClass.coe_pow, hy', neg_pow_two, pow_two, smul_mul_smul_comm, P_mul_self,
      smul_zero]
    rfl
  rw [← gexp, coe_gexp hy2, hy']
  simp [sum_range_succ, sub_eq_add_neg]

theorem EC_theta_one {Λ : Type*} [DecidableEq Λ] [Fintype Λ] (C : Matrix Λ Λ ℝ) :
    EC C (theta (1 : Grassmann.N Λ)) = 1 := by
  rw [EC_theta, expL_eq_self]
  simp [Lop_apply, D]

theorem EC_theta_algebraMap {Λ : Type*} [DecidableEq Λ] [Fintype Λ] (C : Matrix Λ Λ ℝ) (c : ℂ) :
    EC C (theta (algebraMap ℂ (Grassmann.N Λ) c)) = algebraMap ℂ (Grassmann.N Λ) c := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, map_smul, EC_theta_one]

/-- **Proposition `prop:ZNN`, `e:ZNN`**: restricted to constant fields,
`Z̃_{N,N} = 1 + ũ_{N,N} - |Λ_N| ã_{N,N} ψψ̄`, with `ũ_{N,N} = k_N^0 + ã_{N,N} t_N` and
`ã_{N,N} = a_N - k_N^2/|Λ_N|`. -/
theorem prop_ZNN (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {N : ℕ} (hN : 1 ≤ N) {msq ℓ₀ : ℝ}
    (hmsq : 0 < msq)
    (hgood : ∀ j < N, GoodCov (d := d) (L := L) (N := N) j ℓ₀ (covAt d L N msq j)) (V₀ : Vcoup) :
    (Rl N) (ZtNN d L N msq V₀) =
      algebraMap ℂ (Alg d L N) (1 + utN d L N msq V₀) -
        ((Fintype.card (Lam d L N) : ℂ) * atN d L N msq V₀) • (PP N) := by
  have hc : (Fintype.card (Lam d L N) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [ZtNN_eq hd hL hN hmsq hgood V₀, tQ_eq_cst, Rc_EC_theta_const, Subalgebra.coe_add, _root_.map_add,
    Rc_gexp_VE, Rc_even (mem_Ev.1 (KN d L N msq V₀).2)]
  set P := psiC (Lam d L N) * psibarC (Lam d L N) with hP
  set n : ℂ := (Fintype.card (Lam d L N) : ℂ) with hn
  set a := (VN d L N msq V₀).a
  set k0 := ε (KN d L N msq V₀ : Alg d L N) with hk0
  set k2 := c2 (KN d L N msq V₀ : Alg d L N) with hk2
  have harg : (1 - (n * a) • P + (algebraMap ℂ (Alg d L N) k0 + k2 • P)) =
      algebraMap ℂ (Alg d L N) (1 + k0) + (k2 - n * a) • P := by
    rw [_root_.map_add, map_one, sub_smul]; abel
  rw [harg, _root_.map_add, _root_.map_add, map_smul, map_smul, EC_theta_algebraMap,
    EC_theta_const_P, smul_sub]
  have hsm : ∀ c : ℂ, (k2 - n * a) • algebraMap ℂ (Alg d L N) c =
      algebraMap ℂ (Alg d L N) ((k2 - n * a) * c) := fun c => by
    rw [Algebra.smul_def, ← map_mul]
  rw [hsm]
  have ek2 : kN2 d L N msq V₀ = k2 := rfl
  have ek0 : kN0 d L N msq V₀ = k0 := rfl
  have h1 : n * atN d L N msq V₀ = -(k2 - n * a) := by
    rw [atN, ek2]; field_simp; ring
  have h2 : 1 + utN d L N msq V₀ =
      (1 + k0) - (k2 - n * a) * (((tNN d L N msq / Fintype.card (Lam d L N) : ℝ)) : ℂ) := by
    rw [utN, atN, ek0, ek2]; push_cast; field_simp; ring
  rw [h1, h2, map_sub, neg_smul]
  abel

end

end Suscept
