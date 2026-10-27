import PtCorr2.Zero.Coupling
import Step2.Last.LastNStep

/-!
# The zero-mode integration of the final-scale object (`prop:ZNN` for the new flow)

The last step (`Step2.LastN.rawStepN`) integrates only the nonzero modes `C'^{≠0}_N` and leaves
the final-scale object (in raw fields, `LastOut`)

  `F_N = ∏_{B ∈ 𝓑_{N-1}} e^{-V_N(B)} (1 + 𝒲_N(B)) + K_N(Λ)`     (`finObj`),

`𝔼_{C'^{≠0}_N} θ Z_{N-1} = e^{-u_N(Λ)} F_N` (`rawStepN_ZVK`). The remaining covariance is the zero
mode `t_raw Q`, `t_raw = Γ̂^int_N(0)` (complex, `zmRaw`; in normalised fields `t = Z_N t_raw`,
`prop_last`). We set `Z̃_{N,N} = 𝔼_{t_raw Q} θ F_N` (`ZtFin`).

**Restriction to constant fields** (`prop_ZNN2`): if `V_N(B) = V_{κ_N}(B)` on every block,

  `Rc Z̃_{N,N} = 1 + ũ_{N,N} - |Λ| ã_{N,N} ψψ̄`,

with, writing `α_B = 1 + ε(𝒲_N(B))`,
* `P₀ = ∏_B α_B` (`P0Fin`), `k⁰ = P₀ - 1 + ε(K_N(Λ))` (`k0Fin`);
* `k^{2,𝒲} = ∑_B c2(𝒲_N(B)) ∏_{B' ≠ B} α_{B'}` (`kW2Fin`), `k^{2,K} = c2(K_N(Λ))` (`kK2Fin`);
* `ã_{N,N} = ν_N P₀ - (k^{2,𝒲} + k^{2,K})/|Λ|` (`aFin`), `ũ_{N,N} = k⁰ + ã_{N,N} t_raw` (`uFin`).

This is the old `Suscept.prop_ZNN` (`ã = a_N - k_N^2/|Λ|`, `ũ = k_N^0 + ã t_N`) with complex
`t_raw` in place of `t_N`, and with the unlocalised `𝒲_N` entering only through `ε(𝒲_N(B))`
and `c2(𝒲_N(B))` (`P₀`, `k^{2,𝒲}`). Since `V_N(B)` is a coupling polynomial, its restriction
is `|B| ν_N ψψ̄` (`c2_Vcoup`); the products over blocks are evaluated with `(ψψ̄)² = 0`.

**The full last covariance** (`lastN_full_ZVK`): `Γ^int_N = C'^{≠0}_N + t_raw Q` (`kmat_split`),
so `𝔼_{Γ^int_N} θ Z_{N-1} = e^{-u_N(Λ)} Z̃_{N,N}`.
-/

namespace PtCorr2

noncomputable section

open Finset Grassmann Suscept Step Loc Step2 Step2.LastN

set_option linter.unusedSectionVars false

variable {d L N : ℕ} [NeZero L]

/-! ### Definitions -/

/-- **The final-scale object** `F_N = ∏_B e^{-V_N(B)}(1 + 𝒲_N(B)) + K_N(Λ)` (blocks of scale `j`). -/
def finObj (j : ℕ) (out : LastOut d L N) : EvR (Lam d L N) :=
  (∏ b ∈ blockIdx (L := L) (N := N) j, gexp (-out.V b) * (1 + out.W b)) + out.K

/-- **`Z̃_{N,N} = 𝔼_{t_raw Q} θ F_N`**, the zero mode `t_raw Q`, `Q_{xy} = |Λ|^{-1}`, integrated. -/
def ZtFin (j : ℕ) (out : LastOut d L N) (tr : ℂ) : EvR (Lam d L N) :=
  ECCE (cstC (Lam d L N) (tr / Fintype.card (Lam d L N))) (thetaE (finObj j out))

/-- `P₀ = ∏_B (1 + ε(𝒲_N(B)))`. -/
def P0Fin (j : ℕ) (out : LastOut d L N) : ℂ :=
  ∏ b ∈ blockIdx (L := L) (N := N) j, (1 + ε (out.W b : Alg d L N))

/-- `k⁰ = P₀ - 1 + ε(K_N(Λ))`. -/
def k0Fin (j : ℕ) (out : LastOut d L N) : ℂ := P0Fin j out - 1 + ε (out.K : Alg d L N)

/-- `k^{2,𝒲} = ∑_B c2(𝒲_N(B)) ∏_{B' ≠ B} (1 + ε(𝒲_N(B')))`. -/
def kW2Fin (j : ℕ) (out : LastOut d L N) : ℂ :=
  ∑ b ∈ blockIdx (L := L) (N := N) j, Suscept.c2 (out.W b : Alg d L N) *
    ∏ k ∈ (blockIdx (L := L) (N := N) j).erase b, (1 + ε (out.W k : Alg d L N))

/-- `k^{2,K} = c2(K_N(Λ))`. -/
def kK2Fin (out : LastOut d L N) : ℂ := Suscept.c2 (out.K : Alg d L N)

/-- `ã_{N,N} = ν_N P₀ - (k^{2,𝒲} + k^{2,K})/|Λ|`. -/
def aFin (j : ℕ) (out : LastOut d L N) : ℂ :=
  out.κ.nu * P0Fin j out - (kW2Fin j out + kK2Fin out) / Fintype.card (Lam d L N)

/-- `ũ_{N,N} = k⁰ + ã_{N,N} t_raw`. -/
def uFin (j : ℕ) (out : LastOut d L N) (tr : ℂ) : ℂ := k0Fin j out + aFin j out * tr

/-! ### Restriction of the final object -/

theorem ECCE_thetaE_comp (C₁ C₂ : Matrix (Lam d L N) (Lam d L N) ℂ) (F : EvR (Lam d L N)) :
    ECCE C₂ (thetaE (ECCE C₁ (thetaE F))) = ECCE (C₁ + C₂) (thetaE F) :=
  Subtype.ext (by simp only [coe_ECCE, coe_thetaE]; exact ECC_theta_comp C₁ C₂ _)

/-- `Rc e^{-V} = 1 - c2(V) ψψ̄` for even `V` with `ε(V) = 0`. -/
theorem RE_gexp_neg {V : EvR (Lam d L N)} (hV : ε (V : Alg d L N) = 0) :
    RE (Lam d L N) (gexp (-V)) =
      algebraMap ℂ _ 1 + (-Suscept.c2 (V : Alg d L N)) • PPE (Lam d L N) := by
  have hn : IsNilpotent (-V) := (Step.isNilpotent_of_ε' hV).neg
  rw [gexp, IsNilpotent.map_exp hn (RE (Lam d L N)), map_neg, RE_eq, hV, map_zero, zero_add]
  have h2 : (-(Suscept.c2 (V : Alg d L N) • PPE (Lam d L N))) ^ 2 = 0 := by
    rw [neg_pow_two, pow_two, smul_mul_smul_comm, PPE_mul_self, smul_zero]
  rw [IsNilpotent.exp_eq_sum h2]
  simp [sum_range_succ, neg_smul]

/-- `Rc (1 + 𝒲) = (1 + ε 𝒲) + c2(𝒲) ψψ̄`. -/
theorem RE_one_add (W : EvR (Lam d L N)) :
    RE (Lam d L N) (1 + W) =
      algebraMap ℂ _ (1 + ε (W : Alg d L N)) + Suscept.c2 (W : Alg d L N) • PPE (Lam d L N) := by
  rw [map_add, map_one, RE_eq, map_add, map_one, add_assoc]

/-- The restriction of one block factor `e^{-V_B}(1 + 𝒲_B)`. -/
theorem RE_block {V W : EvR (Lam d L N)} (hV : ε (V : Alg d L N) = 0) :
    RE (Lam d L N) (gexp (-V) * (1 + W)) =
      algebraMap ℂ _ (1 + ε (W : Alg d L N)) +
        (Suscept.c2 (W : Alg d L N) - Suscept.c2 (V : Alg d L N) * (1 + ε (W : Alg d L N))) •
          PPE (Lam d L N) := by
  rw [map_mul, RE_gexp_neg hV, RE_one_add]
  have hP := PPE_mul_self (Λ := Lam d L N)
  simp only [Algebra.smul_def, map_one, map_sub, map_mul, map_add, map_neg]
  linear_combination (-(algebraMap ℂ (EvR (Lam d L N)) (Suscept.c2 (V : Alg d L N))) *
    algebraMap ℂ (EvR (Lam d L N)) (Suscept.c2 (W : Alg d L N))) * hP

theorem eps_coe_V {j : ℕ} {out : LastOut d L N}
    (hV : ∀ b ∈ blockIdx (L := L) (N := N) j,
      (out.V b : Alg d L N) = Vcoup out.κ (blockSet j b)) :
    ∀ b ∈ blockIdx (L := L) (N := N) j, ε (out.V b : Alg d L N) = 0 := fun b hb => by
  rw [hV b hb, eps_Vcoup]

/-- `Rc F_N = (P₀ + ε K) + (∑_B (c2 𝒲_B - c2 V_B α_B) ∏_{B' ≠ B} α_{B'} + c2 K) ψψ̄`. -/
theorem RE_finObj {j : ℕ} {out : LastOut d L N}
    (hV : ∀ b ∈ blockIdx (L := L) (N := N) j, ε (out.V b : Alg d L N) = 0) :
    RE (Lam d L N) (finObj j out) =
      algebraMap ℂ _ (P0Fin j out + ε (out.K : Alg d L N)) +
        ((∑ b ∈ blockIdx (L := L) (N := N) j,
          (Suscept.c2 (out.W b : Alg d L N) - Suscept.c2 (out.V b : Alg d L N) * (1 + ε (out.W b : Alg d L N))) *
            ∏ k ∈ (blockIdx (L := L) (N := N) j).erase b, (1 + ε (out.W k : Alg d L N))) +
          Suscept.c2 (out.K : Alg d L N)) • PPE (Lam d L N) := by
  rw [finObj, map_add, map_prod, prod_congr rfl fun b hb => RE_block (W := out.W b) (hV b hb),
    prod_add_smul_nil _ _ _ PPE_mul_self, RE_eq, P0Fin, map_add, add_smul]
  abel

/-- `ε(F_N) = P₀ + ε K` and `c2(F_N) = k^{2,𝒲} + k^{2,K} - |Λ| ν_N P₀`. -/
theorem eps_c2_finObj {j : ℕ} {out : LastOut d L N}
    (hV : ∀ b ∈ blockIdx (L := L) (N := N) j,
      (out.V b : Alg d L N) = Vcoup out.κ (blockSet j b)) :
    ε (finObj j out : Alg d L N) = P0Fin j out + ε (out.K : Alg d L N) ∧
      Suscept.c2 (finObj j out : Alg d L N) = kW2Fin j out + kK2Fin out -
        (Fintype.card (Lam d L N) : ℂ) * out.κ.nu * P0Fin j out := by
  obtain ⟨h1, h2⟩ := eps_c2_of_RE (RE_finObj (eps_coe_V hV))
  refine ⟨h1, ?_⟩
  rw [h2]
  have hs : ∑ b ∈ blockIdx (L := L) (N := N) j,
      Suscept.c2 (out.V b : Alg d L N) * (1 + ε (out.W b : Alg d L N)) *
        ∏ k ∈ (blockIdx (L := L) (N := N) j).erase b, (1 + ε (out.W k : Alg d L N)) =
      (Fintype.card (Lam d L N) : ℂ) * out.κ.nu * P0Fin j out := by
    have e : ∀ b ∈ blockIdx (L := L) (N := N) j,
        Suscept.c2 (out.V b : Alg d L N) * (1 + ε (out.W b : Alg d L N)) *
          ∏ k ∈ (blockIdx (L := L) (N := N) j).erase b, (1 + ε (out.W k : Alg d L N)) =
        ((blockSet (L := L) (N := N) j b).card : ℂ) * out.κ.nu * P0Fin j out := by
      intro b hb
      rw [mul_assoc, mul_prod_erase _ (fun k => 1 + ε (out.W k : Alg d L N)) hb, hV b hb,
        c2_Vcoup, P0Fin]
    rw [sum_congr rfl e, ← sum_mul, ← sum_mul, sum_card_blockSet]
  rw [kW2Fin, kK2Fin, ← hs]
  simp only [sub_mul, sum_sub_distrib]
  ring

/-- **`prop:ZNN` for the final object of the new flow** (complex zero mode): if `V_N(B) =
V_{κ_N}(B)` on every block, then restricted to constant fields
`Z̃_{N,N} = 1 + ũ_{N,N} - |Λ| ã_{N,N} ψψ̄`. -/
theorem prop_ZNN2 {j : ℕ} {out : LastOut d L N} (tr : ℂ)
    (hV : ∀ b ∈ blockIdx (L := L) (N := N) j,
      (out.V b : Alg d L N) = Vcoup out.κ (blockSet j b)) :
    Rc (Lam d L N) (ZtFin j out tr : Alg d L N) =
      algebraMap ℂ (Alg d L N) (1 + uFin j out tr) -
        ((Fintype.card (Lam d L N) : ℂ) * aFin j out) • (psiC (Lam d L N) * psibarC (Lam d L N)) := by
  obtain ⟨h1, h2⟩ := eps_c2_finObj hV
  have hc : (Fintype.card (Lam d L N) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [ZtFin, coe_ECCE, coe_thetaE, Rc_ECC_cstC_even _ (mem_Ev.1 (finObj j out).2), h1, h2]
  have e1 : P0Fin j out + ε (out.K : Alg d L N) - tr / (Fintype.card (Lam d L N) : ℂ) *
      (kW2Fin j out + kK2Fin out - (Fintype.card (Lam d L N) : ℂ) * out.κ.nu * P0Fin j out) =
      1 + uFin j out tr := by
    rw [uFin, k0Fin, aFin]; field_simp; ring
  have e2 : kW2Fin j out + kK2Fin out - (Fintype.card (Lam d L N) : ℂ) * out.κ.nu * P0Fin j out =
      -((Fintype.card (Lam d L N) : ℂ) * aFin j out) := by
    rw [aFin]; field_simp; ring
  rw [e1, e2, neg_smul, sub_eq_add_neg]

/-! ### The full last covariance -/

/-- The raw zero mode `t_raw = Γ̂^int_N(0)` of the dressed history `ζ` (`t = Z_N t_raw`). -/
def zmRaw (R : RGPar d L N) (j : ℕ) (ζ : ℕ → ℂ) : ℂ :=
  (⟨L, N, R.msq, DressedFRD.frdC R.P R.msq L N, ζ⟩ : DressedFRD.Data d (L ^ N)).Gint j 0

/-- The full raw covariance of the last step, `Γ^int_N`. -/
def fullCovN (R : RGPar d L N) (j : ℕ) (ζ : ℕ → ℂ) : Matrix (Lam d L N) (Lam d L N) ℂ :=
  DressedFRD.kmat
    ((⟨L, N, R.msq, DressedFRD.frdC R.P R.msq L N, ζ⟩ : DressedFRD.Data d (L ^ N)).Gint j)

/-- `Γ^int_N = C'^{≠0}_N + t_raw Q` (`kmat_split`). -/
theorem fullCovN_eq (R : RGPar d L N) (j : ℕ) (ζ : ℕ → ℂ) :
    fullCovN R j ζ = lastCov R j ζ +
      cstC (Lam d L N) (zmRaw R j ζ / Fintype.card (Lam d L N)) := by
  ext x y
  rw [fullCovN, DressedFRD.kmat_split, Matrix.add_apply, cstC, FRD.card_torus, zmRaw]
  push_cast
  rfl

/-- **The last step with the full covariance**: `𝔼_{Γ^int_N} θ Z_{N-1} = e^{-u_N(Λ)} Z̃_{N,N}`
with `Z_{N-1} = ∑_X I^{Λ∖X} K♭(X)` the input of `rawStepN` and `t_raw = zmRaw`. -/
theorem lastN_full_ZVK (R : RGPar 2 L N) {j : ℕ} (hj : j + 1 = N) (st : RawSt 2 L N) (g μ : ℝ)
    (D : Fam 2 L N) (K : Act 2 L N) :
    ECCE (fullCovN R j (rawStepN R j st g μ D K).ζ)
        (thetaE (gZ j (Ib (stVf R j st g μ) (st.Wl + D)) (Kflat j (stDelta R j st) K))) =
      Complex.exp (-(rawStepN R j st g μ D K).u) •
        ZtFin j (rawStepN R j st g μ D K) (zmRaw R j (rawStepN R j st g μ D K).ζ) := by
  rw [fullCovN_eq, ← ECCE_thetaE_comp]
  have hC : lastCov R j (rawStepN R j st g μ D K).ζ = (rawStepN R j st g μ D K).C := rfl
  rw [hC, rawStepN_ZVK R hj, map_smul, map_smul]
  rfl

end

end PtCorr2
