import Obs2.Pair.PairChain
import Obs2.Flow.Tau2Bd

/-!
# The Pauli-reduced pair observable: exact seed identities, the reduced one-step identities,
the defect bounds and `n_a = n_b`

Background (see `Log.md`, "The vertex term of the `r̃` flow"). In the `r̃` flow of
`Obs2/Pair/PairChain` the source contains the *vertex term* `β_aβ_bC(a,a)(n_a + n_b)` and the
`γ`-remainder terms `β_a'ρ_b + β_b'ρ_a`. Both are of relative size `ϑ_kǧ_k²` at every scale
`k ≥ j_x` (no decay above coalescence). In the exact merged dynamics they are cancelled, to all
orders, by the `m₂` of the third- and higher-order cumulants `F^{(3)}(V_a, V_b, V_∅), …`, which the
second-order map puts into `K_{k+1}` (hence into `e_{ab}` of the *next* step). Coupling-level
bookkeeping with norm bounds on `K` cannot see this cancellation; summed over `j_x ≤ k ≤ N` the
residues are dominated by the top scales.

The cure is to run the **Pauli-reduced pair observable**: at coalescence the `σ_aσ_b` part of the
integrand is `V_aV_b + …`, a single *linear* insertion of the quartic `β_aβ_bψ̄_aψ_aψ̄_bψ_b`
(no separate `σ_a`, `σ_b` parts, hence no products of large one-point couplings later on). Its
cumulants with the bulk all vanish at a merged point (`(ψ̄_aψ_a)² = 0`).

This file provides the exact and generic pieces:

* **Seed identities** (`expLC_pbp_mul`, `eps_expLC_pbp_mul`, `mass2_expLC_pbp_mul`):
  `ε(e^{ℒ_C}(ψ̄_aψ_aψ̄_bψ_b)) = C(a,a)C(b,b) - C(a,b)C(b,a)` (the determinant defect) and
  `m₂(e^{ℒ_C}(ψ̄_aψ_aψ̄_bψ_b)) = C(a,a) + C(b,b) - C(a,b) - C(b,a)`. Both vanish for a covariance
  that is constant on `{a,b}` (`pauli_quartic_const`), and the Pauli defects of the seed are the
  whole `ε`, `m₂` (`pauliDef_pbp_mul`, `pauliDef2_pbp_mul`).
* **The closure defect** (`pauli_closure_pure`): the second-order `r` flow misses exactly
  `2β_aβ_b(E - n(C + E))` against the exact one-loop merged flow (`E` = constant correction,
  `n` = vertex correction) — this is what `K` must carry.
* **The reduced one-step identities** (`rAB_next_red`, `pair_step_red`): with no one-point vertices
  (`β_a = β_b = 0`), `r' = (1 - n_a)r - d_r + 𝔡₂ - e_{ab} + f` and
  `Δq + Δγ_aΔγ_b = -C(a,a)r - 𝔡 + X + ρ_aρ_b`: no vertex term, no `γ`-cross terms.
* **Defect bounds** (`norm_m2Def_le`, `norm_detDef_le`): for `GoodCov2 k ℓ C` and `b` reached
  from `a` by `n` unit steps, `|C(a,a)+C(b,b)-C(a,b)-C(b,a)| ≤ 2nℓ²/L^{k+1}` and
  `|C(a,a)C(b,b) - C(a,b)C(b,a)| ≤ 2nℓ⁴/L^{k+1}`.
* **`n_a = n_b`** for a translation-invariant covariance (`mass2_FC_pbp_Vcoup_transl`).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 LocObs Flow2

section Seed

variable {d L N : ℕ} [NeZero L] (C : Matrix (Lam d L N) (Lam d L N) ℂ)

theorem isHom_pbp (a : Lam d L N) : IsHom 2 (pbp a : Alg d L N) :=
  (isHom_ι _).mul (isHom_ι _)

theorem mass2_pbp_mul (a b : Lam d L N) : mass2 (pbp a * pbp b : Alg d L N) = 0 :=
  mass2_of_isHom ((isHom_pbp a).mul (isHom_pbp b)) (by norm_num)

theorem loc2Form_expLC_pbp (a : Lam d L N) : Loc2Form a (expLC C (pbp a)) :=
  ⟨C a a, 1, by rw [expLC_pbp_eq, one_smul, add_comm]⟩

/-- `e^{ℒ_C}(ψ̄_aψ_aψ̄_bψ_b) = (ψ̄_aψ_a + C(a,a))(ψ̄_bψ_b + C(b,b)) + F_C(e^{ℒ_C}ψ̄_aψ_a, e^{ℒ_C}ψ̄_bψ_b)`. -/
theorem expLC_pbp_mul (a b : Lam d L N) :
    expLC C (pbp a * pbp b) = (pbp a + C a a • (1 : Alg d L N)) * (pbp b + C b b • 1) +
      FC C (expLC C (pbp a)) (expLC C (pbp b)) := by
  rw [FC_expLC, expLC_pbp_eq, expLC_pbp_eq]; abel

/-- **The `ε` of the quartic seed is the determinant defect**:
`ε(e^{ℒ_C}(ψ̄_aψ_aψ̄_bψ_b)) = C(a,a)C(b,b) - C(a,b)C(b,a)`. -/
theorem eps_expLC_pbp_mul (a b : Lam d L N) :
    ε (expLC C (pbp a * pbp b)) = C a a * C b b - C a b * C b a := by
  have hF : ε (FC C (expLC C (pbp a)) (expLC C (pbp b))) = -(C a b * C b a) := by
    rw [expLC_pbp_eq, expLC_pbp_eq, FC_add_left, Step2.FC_const_left, add_zero, FC_add_right,
      FC_smul_right, FC_one_right, smul_zero, add_zero, eps_FC_pbp_pbp]
  rw [expLC_pbp_mul, map_add, hF, map_mul, map_add, map_add, eps_pbp, eps_pbp, map_smul,
    map_smul, map_one]
  simp only [smul_eq_mul, mul_one, zero_add]
  ring

/-- **The `m₂` of the quartic seed is the gradient defect**:
`m₂(e^{ℒ_C}(ψ̄_aψ_aψ̄_bψ_b)) = C(a,a) + C(b,b) - C(a,b) - C(b,a)`. -/
theorem mass2_expLC_pbp_mul (a b : Lam d L N) :
    mass2 (expLC C (pbp a * pbp b)) = C a a + C b b - C a b - C b a := by
  have hF := mass2_FC_loc2_loc2 C (loc2Form_expLC_pbp C a) (loc2Form_expLC_pbp C b)
  have ha : mass2 (expLC C (pbp a)) = 1 := by
    rw [expLC_pbp_eq, mass2_add, mass2_pbp, mass2_smul, mass2_one, mul_zero, add_zero]
  have hb : mass2 (expLC C (pbp b)) = 1 := by
    rw [expLC_pbp_eq, mass2_add, mass2_pbp, mass2_smul, mass2_one, mul_zero, add_zero]
  rw [ha, hb] at hF
  have e : (pbp a + C a a • (1 : Alg d L N)) * (pbp b + C b b • 1) =
      pbp a * pbp b + C b b • pbp a + C a a • pbp b + (C a a * C b b) • (1 : Alg d L N) := by
    rw [add_mul, mul_add, mul_add, mul_smul_comm, mul_one, smul_mul_assoc, one_mul,
      smul_mul_smul_comm, one_mul]
    abel
  rw [expLC_pbp_mul, mass2_add, hF, e, mass2_add, mass2_add, mass2_add, mass2_pbp_mul,
    mass2_smul, mass2_smul, mass2_smul, mass2_pbp, mass2_pbp, mass2_one]
  ring

/-- **Pauli at a merged point**: for a covariance constant on `{a, b}`, the quartic seed has
vanishing `ε` and `m₂` after integration (`(ψ̄_aψ_a)² = 0`). -/
theorem pauli_quartic_const {a b : Lam d L N} (hab : C a b = C a a) (hba : C b a = C a a)
    (hbb : C b b = C a a) :
    ε (expLC C (pbp a * pbp b)) = 0 ∧ mass2 (expLC C (pbp a * pbp b)) = 0 := by
  rw [eps_expLC_pbp_mul, mass2_expLC_pbp_mul, hab, hba, hbb]
  constructor <;> ring

end Seed

/-! ### The closure defect of the second-order `r` flow -/

/-- **What the second-order map misses** (pure, merged picture). With the exact one-loop merged
maps `γ' = γ - (C + E)β`, `β' = (1 - n)β` (both points) and the exact linear evolution of the
`σ_aσ_b` part, `R̃' = (1 - n)R̃` for `R̃ = r + γ_aβ_b + γ_bβ_a`, the exact pair coupling is
`r'_{ex} = (1 - n)r + 2(1 - n)(C + E)β_aβ_b`, while the second-order map gives
`r'_2 = (1 - n)r + 2Cβ_aβ_b`. The difference `2β_aβ_b(E - n(C + E))` is of relative size `ǧ`
per step and is carried by the third-order cumulant in `K_{k+1}`. -/
theorem pauli_closure_pure (r ga gb βa βb n C E : ℂ) :
    ((1 - n) * (r + ga * βb + gb * βa) - (ga - (C + E) * βa) * ((1 - n) * βb) -
        (gb - (C + E) * βb) * ((1 - n) * βa)) -
      ((1 - n) * r + 2 * C * βa * βb) = 2 * βa * βb * (E - n * (C + E)) := by
  ring

/-! ### The reduced one-step identities (no one-point vertices) -/

section Red

variable {d L N : ℕ} [NeZero L] (P : ObsPts d L N) (j : ℕ)
  (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V W : OFam .two d L N) (K : OAct .two d L N)

/-- **The reduced `r` flow**: without `σ_a`-vertex (`β_a = 0`),
`r' = (1 - n_a)r - d_r + 𝔡₂ - e_{ab} + f` — no vertex term. -/
theorem rAB_next_red (hVa : ∀ b, Loc2Form P.a (V b : SA .two (Lam d L N)).a)
    (hVb : ∀ b, Loc2Form P.b (V b : SA .two (Lam d L N)).b) (hβ : betaTot2 j V = 0) :
    rAB2 (j + 1) (Vnext2O P j C V W K) =
      (1 - nA2 P j C V) * rAB2 j V - dR2 P j C V + pdefM2 j C V - eAB2 P j C W K +
        farABm P j C V W := by
  rw [rAB_next P j C V W K hVa hVb, hβ, dR2]; ring

/-- **The reduced pair-constant step**: without one-point vertices (`β_a = β_b = 0`),
`Δq + Δγ_aΔγ_b = -C(a,a)r - 𝔡 + X + ρ_aρ_b`. -/
theorem pair_step_red (hVa : ∀ b, Loc2Form P.a (V b : SA .two (Lam d L N)).a)
    (hVb : ∀ b, Loc2Form P.b (V b : SA .two (Lam d L N)).b)
    (h0ab : ∑ b ∈ blockIdx (L := L) (N := N) j, ε (V b : SA .two (Lam d L N)).ab = 0)
    (h0a : ∑ b ∈ blockIdx (L := L) (N := N) j, ε (V b : SA .two (Lam d L N)).a = 0)
    (h0b : ∑ b ∈ blockIdx (L := L) (N := N) j, ε (V b : SA .two (Lam d L N)).b = 0)
    (hC : C P.b P.b = C P.a P.a) (hβa : betaTot2 j V = 0) (hβb : betaB2 j V = 0) :
    -ε (uObsTot P j C V W K : SA .two (Lam d L N)).ab +
        (-ε (uObsTot P j C V W K : SA .two (Lam d L N)).a) *
          (-ε (uObsTot P j C V W K : SA .two (Lam d L N)).b) =
      -(C P.a P.a * rAB2 j V) - pdefAB2 P j C V +
        (xAB2 P j C V W K + rhoA2 P j C V W K * rhoB2 P j C V W K) := by
  have h := pair_step_id P j C V W K hVa hVb h0ab h0a h0b hC 0 0
  rw [hβa, hβb] at h
  simpa using h

end Red

/-! ### Defect bounds from the gradient bounds of `GoodCov2` -/

section Defect

variable {L N : ℕ} [NeZero L]

/-- The endpoint of a lattice path `w` from `a`. -/
def pathEnd (a : Lam 2 L N) (w : List (Dir 2)) : Lam 2 L N := a + (w.map dirVec).sum

/-- **Path Lipschitz bound**: unit-step increments `≤ δ` give `‖f(a + w) - f(a)‖ ≤ |w|δ`. -/
theorem norm_sub_path_le {f : Lam 2 L N → ℂ} {δ : ℝ}
    (hf : ∀ x e, ‖f (x + dirVec e) - f x‖ ≤ δ) :
    ∀ (w : List (Dir 2)) (a : Lam 2 L N), ‖f (pathEnd a w) - f a‖ ≤ w.length * δ
  | [], a => by simp [pathEnd]
  | e :: w, a => by
    have h1 := norm_sub_path_le hf w (a + dirVec e)
    have h2 := hf a e
    have e1 : pathEnd a (e :: w) = pathEnd (a + dirVec e) w := by
      simp [pathEnd, add_assoc]
    rw [e1]
    calc ‖f (pathEnd (a + dirVec e) w) - f a‖
        ≤ ‖f (pathEnd (a + dirVec e) w) - f (a + dirVec e)‖ + ‖f (a + dirVec e) - f a‖ := by
          have := norm_add_le (f (pathEnd (a + dirVec e) w) - f (a + dirVec e))
            (f (a + dirVec e) - f a)
          rwa [sub_add_sub_cancel] at this
      _ ≤ w.length * δ + δ := add_le_add h1 h2
      _ = (e :: w).length * δ := by simp; ring

variable {k : ℕ} {ℓC : ℝ} {C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ}

theorem norm_cov_path_R (hC : GoodCov2 k ℓC C) (x a : Lam 2 L N) (w : List (Dir 2)) :
    ‖C x (pathEnd a w) - C x a‖ ≤ w.length * (ℓC ^ 2 / (L : ℝ) ^ (k + 1)) :=
  norm_sub_path_le (f := fun y => C x y) (fun y e => good_gradR hC e x y) w a

theorem norm_cov_path_L (hC : GoodCov2 k ℓC C) (y a : Lam 2 L N) (w : List (Dir 2)) :
    ‖C (pathEnd a w) y - C a y‖ ≤ w.length * (ℓC ^ 2 / (L : ℝ) ^ (k + 1)) :=
  norm_sub_path_le (f := fun x => C x y) (fun x e => good_gradL hC e x y) w a

/-- **The `m₂` (gradient) defect**: `|C(a,a) + C(b,b) - C(a,b) - C(b,a)| ≤ 2nℓ²/L^{k+1}` for
`b = a + w`, `|w| = n`. -/
theorem norm_m2Def_le (hC : GoodCov2 k ℓC C) (a : Lam 2 L N) (w : List (Dir 2)) :
    ‖C a a + C (pathEnd a w) (pathEnd a w) - C a (pathEnd a w) - C (pathEnd a w) a‖ ≤
      2 * w.length * (ℓC ^ 2 / (L : ℝ) ^ (k + 1)) := by
  set b := pathEnd a w
  have h1 := norm_cov_path_R hC a a w
  have h2 := norm_cov_path_R hC b a w
  have e : C a a + C b b - C a b - C b a = -(C a b - C a a) + (C b b - C b a) := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_neg]
  linarith

/-- **The determinant defect**: `|C(a,a)C(b,b) - C(a,b)C(b,a)| ≤ 2nℓ⁴/L^{k+1}` for `b = a + w`. -/
theorem norm_detDef_le (hC : GoodCov2 k ℓC C) (a : Lam 2 L N) (w : List (Dir 2)) :
    ‖C a a * C (pathEnd a w) (pathEnd a w) - C a (pathEnd a w) * C (pathEnd a w) a‖ ≤
      2 * w.length * (ℓC ^ 2 / (L : ℝ) ^ (k + 1)) * ℓC ^ 2 := by
  set b := pathEnd a w
  set δ := ℓC ^ 2 / (L : ℝ) ^ (k + 1)
  have h1 : ‖C b b - C b a‖ ≤ w.length * δ := norm_cov_path_R hC b a w
  have h2 : ‖C a b - C a a‖ ≤ w.length * δ := norm_cov_path_R hC a a w
  have e : C a a * C b b - C a b * C b a = C a a * (C b b - C b a) - C b a * (C a b - C a a) := by
    ring
  have hδ : 0 ≤ (w.length : ℝ) * δ := (norm_nonneg _).trans h1
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have e1 := mul_le_mul (good_entry hC a a) h1 (norm_nonneg _) (sq_nonneg _)
  have e2 := mul_le_mul (good_entry hC b a) h2 (norm_nonneg _) (sq_nonneg _)
  nlinarith

end Defect

/-! ### `n_a = n_b` for a translation-invariant covariance -/

section Transl

variable {d L N : ℕ} [NeZero L] {C : Matrix (Lam d L N) (Lam d L N) ℂ}

theorem sum_row_transl (hT : ∀ v x y, C (x + v) (y + v) = C x y) (a b : Lam d L N) :
    ∑ x, C a x = ∑ x, C b x := by
  refine Fintype.sum_equiv (Equiv.addRight (b - a)) _ _ fun x => ?_
  have := hT (b - a) a x
  simp only [Equiv.coe_addRight] at this ⊢
  rw [← this, add_sub_cancel]

theorem sum_col_transl (hT : ∀ v x y, C (x + v) (y + v) = C x y) (a b : Lam d L N) :
    ∑ x, C x a = ∑ x, C x b := by
  refine Fintype.sum_equiv (Equiv.addRight (b - a)) _ _ fun x => ?_
  have := hT (b - a) x a
  simp only [Equiv.coe_addRight] at this ⊢
  rw [← this, add_sub_cancel]

theorem lfunC_transl (hT : ∀ v x y, C (x + v) (y + v) = C x y) (a b : Lam d L N) :
    lfunC C a = lfunC C b := by
  obtain ⟨v, rfl⟩ : ∃ v, b = a + v := ⟨b - a, by abel⟩
  unfold lfunC
  refine sum_congr rfl fun i _ => ?_
  refine Fintype.sum_equiv (Equiv.addRight v) _ _ fun z => ?_
  have hg : ∀ e, gpC C a e z = gpC C (a + v) e (z + v) := fun e => by
    unfold gpC
    rw [add_right_comm z v, hT, hT, hT, hT]
  simp only [Equiv.coe_addRight, hg]

/-- **`n_a = n_b`**: for a translation-invariant covariance the vertex factor
`m₂F_C(ψ̄_aψ_a, V_κ(Λ))` does not depend on the point. -/
theorem mass2_FC_pbp_Vcoup_transl (hT : ∀ v x y, C (x + v) (y + v) = C x y) (a b : Lam d L N)
    (κ : Step2.Coup) :
    mass2 (FC C (pbp a) (Step2.Vcoup κ univ)) = mass2 (FC C (pbp b) (Step2.Vcoup κ univ)) := by
  rw [mass2_FC_pbp_Vcoup, mass2_FC_pbp_Vcoup, sum_row_transl hT a b, sum_col_transl hT a b,
    lfunC_transl hT a b]

end Transl

end

end Obs2
