import PtCorr2.Zero.Restrict
import Step2.Coup.Coupling

/-!
# The coupling polynomial restricted to constant fields (`PtCorr2`)

For `κ = (z, y, ν, g)`, restricted to constant fields only the mass term of
`V_κ(Y) = ∑_{x ∈ Y} [z ∇ψ∇ψ̄ + (y/2)(-Δψ ψ̄ + ψ (-Δψ̄)) + ν ψψ̄ + g M̂]` survives:
the gradient terms vanish and the quartic term has no degree-two part. Hence
`c2 (V_κ(Y)) = |Y| ν` (**`c2_Vcoup`**), and for the blocks of scale `j`,
`∑_B |B| = |Λ|` (`sum_card_blockSet`).
-/

namespace PtCorr2

noncomputable section

open Finset Grassmann Suscept Step Loc

set_option linter.unusedSectionVars false

section General

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

theorem c2_zero' : c2 (0 : Grassmann.N Λ) = 0 := by
  have := c2_smul (0 : ℂ) (0 : Grassmann.N Λ)
  rwa [zero_smul, zero_mul] at this

theorem c2C_sub (F G : Grassmann.N Λ) : c2 (F - G) = c2 F - c2 G := by
  rw [sub_eq_add_neg, c2_add, ← neg_one_smul ℂ G, c2_smul]; ring

theorem c2C_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (F : ι → Grassmann.N Λ) :
    c2 (∑ i ∈ s, F i) = ∑ i ∈ s, c2 (F i) := by
  induction s using Finset.induction_on with
  | empty => simp [c2_zero']
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, c2_add, ih]

theorem c2_psi_psibar [Nonempty Λ] (a b : Λ) : c2 (psi a * psibar b) = 1 := by
  have he : inv' (psi a * psibar b) = psi a * psibar b := by
    rw [map_mul, psi, psibar, inv'_ψ, inv'_ψ, neg_mul_neg]
  rw [← c2_Rc he, map_mul, Rc_psi, Rc_psibar, c2_P]

end General

variable {d L N : ℕ} [NeZero L]

theorem c2_monoAt_c (x : Lam d L N) : c2 (monoAt (Mono.c : Mono d) x) = 1 := by
  rw [Step2.monoAt_c, c2_psi_psibar]

theorem c2_monoAt_a2 (i : Fin d) (x : Lam d L N) : c2 (monoAt (Mono.a2 s(i, i)) x) = 0 := by
  rw [Step2.monoAt_a2]
  simp only [sub_mul, c2_add, c2C_sub, c2_psi_psibar, sub_self, add_zero]

theorem c2_monoAt_b2 (i : Fin d) (x : Lam d L N) : c2 (monoAt (Mono.b2 s(i, i)) x) = 0 := by
  rw [Step2.monoAt_b2]
  simp only [mul_sub, c2_add, c2C_sub, c2_psi_psibar, sub_self, add_zero]

theorem c2_monoAt_m2 (i : Fin d) (x : Lam d L N) : c2 (monoAt (Mono.m2 i i) x) = 0 := by
  rw [Step2.monoAt_m2]
  simp only [mul_sub, sub_mul, c2_smul, c2_add, c2C_sub, c2_psi_psibar]
  ring

theorem c2_mono4sSet (i k : Fin d) (Y : Finset (Lam d L N)) : c2 (mono4sSet i k Y) = 0 := by
  unfold c2
  refine sum_eq_zero fun x _ => sum_eq_zero fun y _ => ?_
  exact Step2.coeff_mono4Set_of_ne i k Y _ (by decide)

theorem coupC_c2_monoAt (κ : Step2.Coup) (M : Mono d) (x : Lam d L N) :
    Step2.coupC κ M * c2 (monoAt M x) = if M = Mono.c then κ.nu else 0 := by
  cases M with
  | c => simp [Step2.coupC, c2_monoAt_c]
  | a1 i => simp [Step2.coupC]
  | b1 i => simp [Step2.coupC]
  | a2 s =>
    induction s using Sym2.ind with
    | _ a b =>
      by_cases h : a = b
      · subst h; simp [c2_monoAt_a2]
      · simp [Step2.coupC, Sym2.mk_isDiag_iff, h]
  | b2 s =>
    induction s using Sym2.ind with
    | _ a b =>
      by_cases h : a = b
      · subst h; simp [c2_monoAt_b2]
      · simp [Step2.coupC, Sym2.mk_isDiag_iff, h]
  | m2 i k =>
    by_cases h : i = k
    · subst h; simp [c2_monoAt_m2]
    · simp [Step2.coupC, h]

/-- **Restricted to constant fields, `V_κ(Y) = |Y| ν ψψ̄`**: `c2 (V_κ(Y)) = |Y| ν`. -/
theorem c2_Vcoup (κ : Step2.Coup) (Y : Finset (Lam d L N)) :
    c2 (Step2.Vcoup κ Y) = (Y.card : ℂ) * κ.nu := by
  unfold Step2.Vcoup Step2.unif
  rw [c2_add, c2_add, zero_smul, c2_zero', zero_add, c2C_sum, c2C_sum]
  simp only [c2_smul, c2C_sum, c2_mono4sSet, mul_zero, sum_const_zero, add_zero]
  unfold monoSet
  simp only [c2C_sum, mul_sum, coupC_c2_monoAt]
  rw [Finset.sum_comm]
  simp

/-- The blocks of scale `j` partition `Λ`: `∑_B |B| = |Λ|`. -/
theorem sum_card_blockSet (j : ℕ) :
    ∑ b ∈ blockIdx (d := d) (L := L) (N := N) j,
      ((blockSet (d := d) (L := L) (N := N) j b).card : ℂ) =
      (Fintype.card (Lam d L N) : ℂ) := by
  rw [← Nat.cast_sum, ← card_biUnion (pairwiseDisjoint_blockSet j _)]
  show (((blocks j univ).biUnion (blockSet j)).card : ℂ) = _
  rw [biUnion_blocks (isPolymer_univ j), card_univ]

end

end PtCorr2
