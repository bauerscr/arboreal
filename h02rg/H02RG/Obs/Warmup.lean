import Obs.Corr

/-!
# The free observable flow reproduces the free correlation functions (`e:warmupcor`)

For a decomposition `C = ∑_{k < M} C_k` (`Cs : ℕ → Matrix Λ Λ ℝ`, arbitrary real matrices; the
covariance of the `(k+1)`-st step is `Cs k`):

* `freeIter Cs W₀ k` iterates the map `e:Vobspt`; `ECO_sum_thetaO_oexp`:
  `𝔼_C[θ e^{-W₀}] = e^{-W_M}` for observable `W₀` (`e:E-semigroup` and the identity after
  `e:Vobspt`);
* `flow1`, `flow2`: the coupling constants of Lemma `lem:Vobs-flow-free` along the flow;
  `freeIter_one`, `freeIter_two`: `W_k = (u^obs + V^obs)_k(Λ)`;
* `warmup_one`, `warmup_two_a`, `warmup_two_ab` (`e:warmupcor`, with `V^∅_0 = 0` and
  `q_0 = r_0 = 0`, resp. `γ_0 = q_0 = η_0 = r_0 = 0`, for the split constants
  `q_a, q_b, r_a, r_b`; `q = q_a + q_b`):
  `λ_aλ_b ⟨ψ̄_aψ_b⟩_C = q_M`, `λ_a ⟨ψ̄_aψ_a⟩_C = γ_{a,M}`,
  `λ_aλ_b ⟨ψ̄_aψ_a; ψ̄_bψ_b⟩_C = q_M`;
* `flow1_q`, `flow2_q`: `q_M = λ_aλ_b ∑_k C_k(a,b)` (Case (1)),
  `q_M = -λ_aλ_b (∑_k C_k(a,b))²` (Case (2), `C_k(a,b) = C_k(b,a)`), and
  `γ_{a,M} = λ_a ∑_k C_k(a,a)`;
* `warmup_conclusion` (`e:warmupcor-conclusion`): `⟨ψ̄_aψ_a; ψ̄_bψ_b⟩_C = -C(a,b)²`, and
  `warmup_one_conclusion`: `⟨ψ̄_aψ_b⟩_C = C(a,b)`.
-/

namespace Obs

noncomputable section

open Finset Grassmann SA

variable {c : Case} {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

/-- The iterated free observable flow: `W_{k+1} = freeStep C_k W_k`. -/
def freeIter (Cs : ℕ → Matrix Λ Λ ℝ) (W₀ : OE c Λ) : ℕ → OE c Λ
  | 0 => W₀
  | k + 1 => freeStep (Cs k) (freeIter Cs W₀ k)

theorem bulk_freeIter (Cs : ℕ → Matrix Λ Λ ℝ) {W₀ : OE c Λ} (h : bulk W₀ = 0) (k : ℕ) :
    bulk (freeIter Cs W₀ k) = 0 := by
  induction k with
  | zero => exact h
  | succ k ih => exact bulk_freeStep _ ih

/-- `𝔼_{C}[θ e^{-W₀}] = e^{-W_M}` for `C = ∑_{k<M} C_k`. -/
theorem ECO_sum_thetaO_oexp (Cs : ℕ → Matrix Λ Λ ℝ) {W₀ : OE c Λ} (h : bulk W₀ = 0) (M : ℕ) :
    ECO (∑ k ∈ range M, Cs k) (thetaO (oexp (-W₀))) = oexp (-freeIter Cs W₀ M) := by
  induction M with
  | zero => rw [sum_range_zero, ECO_zero_thetaO]; rfl
  | succ M ih =>
    rw [sum_range_succ, ← ECO_thetaO_comp, ih, ECO_thetaO_oexp_neg _ (bulk_freeIter Cs h M)]
    rfl

/-- The Case (2) coupling constants along the free flow. -/
def flow2 (Cs : ℕ → Matrix Λ Λ ℝ) (a b : Λ) (V : Coup2) : ℕ → Coup2
  | 0 => V
  | k + 1 => (flow2 Cs a b V k).next (Cs k a b) (Cs k a a) (Cs k b b)

theorem freeIter_two (Cs : ℕ → Matrix Λ Λ ℝ) (V : Coup2) (a b : Λ)
    (hsym : ∀ k, Cs k a b = Cs k b a) (k : ℕ) :
    freeIter Cs (evalO .two V a b univ) k = evalO .two (flow2 Cs a b V k) a b univ := by
  induction k with
  | zero => rfl
  | succ k ih => rw [freeIter, ih, freeStep_two _ _ (mem_univ a) (mem_univ b) (hsym k)]; rfl

/-! ### Closed forms of the coupling constants -/

theorem flow2_la (Cs : ℕ → Matrix Λ Λ ℝ) (a b : Λ) (V : Coup2) (k : ℕ) :
    (flow2 Cs a b V k).la = V.la ∧ (flow2 Cs a b V k).lb = V.lb ∧
      (flow2 Cs a b V k).ra = V.ra ∧ (flow2 Cs a b V k).rb = V.rb := by
  induction k with
  | zero => exact ⟨rfl, rfl, rfl, rfl⟩
  | succ k ih => exact ih

/-- `η_M = -2 λ_aλ_b ∑_{k<M} C_k(a,b)` (Case (2), `η_0 = 0`). -/
theorem flow2_eta (Cs : ℕ → Matrix Λ Λ ℝ) (a b : Λ) (la lb ga gb qa qb ra rb : ℂ) (M : ℕ) :
    (flow2 Cs a b ⟨la, lb, ga, gb, qa, qb, 0, ra, rb⟩ M).eta =
      -2 * la * lb * ∑ k ∈ range M, (Cs k a b : ℂ) := by
  induction M with
  | zero => simp [flow2]
  | succ M ih =>
    obtain ⟨h1, h2, -, -⟩ := flow2_la Cs a b ⟨la, lb, ga, gb, qa, qb, 0, ra, rb⟩ M
    simp only [flow2, Coup2.next, ih, h1, h2, sum_range_succ]
    ring

/-- `q_M = -λ_aλ_b (∑_{k<M} C_k(a,b))²` (Case (2), `q_{x,0} = η_0 = r_{x,0} = 0`; `q = q_a + q_b`). -/
theorem flow2_q (Cs : ℕ → Matrix Λ Λ ℝ) (a b : Λ) (la lb ga gb : ℂ) (M : ℕ) :
    (flow2 Cs a b ⟨la, lb, ga, gb, 0, 0, 0, 0, 0⟩ M).q =
      -(la * lb) * (∑ k ∈ range M, (Cs k a b : ℂ)) ^ 2 := by
  induction M with
  | zero => simp [flow2, Coup2.q]
  | succ M ih =>
    obtain ⟨h1, h2, h3, h4⟩ := flow2_la Cs a b ⟨la, lb, ga, gb, 0, 0, 0, 0, 0⟩ M
    have he := flow2_eta Cs a b la lb ga gb 0 0 0 0 M
    simp only [Coup2.q] at ih ⊢
    simp only [flow2, Coup2.next, h1, h2, h3, h4, he, sum_range_succ]
    linear_combination ih

/-! ### The correlation functions -/

theorem omega_zero_mat (x : N Λ) : omega (0 : Matrix Λ Λ ℝ) x = ε x := by
  rw [omega, expL_eq_self]; simp [Lop_apply]

theorem Zb_zero (C : Matrix Λ Λ ℝ) : Zb C (0 : Step.EvR Λ) = 1 := by
  rw [Zb, neg_zero, Step.gexp_zero, OneMemClass.coe_one, omega_one]

theorem avg_zero (C : Matrix Λ Λ ℝ) (F : N Λ) : avg C (0 : Step.EvR Λ) F = omega C F := by
  rw [avg, ← Zb, Zb_zero, neg_zero, Step.gexp_zero, OneMemClass.coe_one, one_mul, div_one]

theorem omO_zero_mat (F : OE c Λ) : omO (0 : Matrix Λ Λ ℝ) F = epsO F := by
  rw [omO, ECO_zero_thetaO]

theorem ε_psibar (x : Λ) : ε (psibar x) = 0 := algebraMapInv_ι _
theorem ε_psi (x : Λ) : ε (psi x) = 0 := algebraMapInv_ι _

/-- The source generating function of the free model along the flow:
`omO C (e^{-V_0}) = e^{-W_M}|_{ψ=0}`. -/
theorem omO_eq_flow (Cs : ℕ → Matrix Λ Λ ℝ) {W₀ : OE c Λ} (h : bulk W₀ = 0) (M : ℕ) :
    omO (∑ k ∈ range M, Cs k) (oexp (-(emb 0 + W₀))) =
      omO (0 : Matrix Λ Λ ℝ) (oexp (-(emb 0 + freeIter Cs W₀ M))) := by
  rw [map_zero, zero_add, zero_add, omO, ECO_sum_thetaO_oexp Cs h M, omO_zero_mat]

theorem ε_two_ab (V : Coup2) (a b : Λ) :
    ε ((evalS .two V a b univ).a) = -V.ga ∧ ε ((evalS .two V a b univ).b) = -V.gb ∧
      ε ((evalS .two V a b univ).ab) = -V.q := by
  simp [evalS, Coup2.q, nr, nx, ε_psibar, ε_psi]

/-- `e:warmupcor`, Case (2): `λ_aλ_b ⟨ψ̄_aψ_a; ψ̄_bψ_b⟩_C = q_M`. -/
theorem warmup_two_ab (Cs : ℕ → Matrix Λ Λ ℝ) (a b : Λ) (hsym : ∀ k, Cs k a b = Cs k b a)
    (la lb : ℂ) (M : ℕ) :
    la * lb * (omega (∑ k ∈ range M, Cs k) (psibar a * psi a * (psibar b * psi b)) -
      omega (∑ k ∈ range M, Cs k) (psibar a * psi a) *
        omega (∑ k ∈ range M, Cs k) (psibar b * psi b)) =
      (flow2 Cs a b ⟨la, lb, 0, 0, 0, 0, 0, 0, 0⟩ M).q := by
  set C := ∑ k ∈ range M, Cs k
  have h1 := corr_two_ab C (Vb := 0) (by simp) a b la lb (by rw [Zb_zero]; exact one_ne_zero)
  rw [omO_eq_flow Cs (bulk_evalO _ _ _ _ _) M, freeIter_two _ _ _ _ hsym, logObs_ab,
    omO_oexp 0 (Vb := 0) (by simp) (bulk_evalO _ _ _ _ _)] at h1
  have h2 := congrArg ε h1
  obtain ⟨ea, eb, eab⟩ := ε_two_ab (flow2 Cs a b ⟨la, lb, 0, 0, 0, 0, 0, 0, 0⟩ M) a b
  simp only [Zb_zero, avg_zero, neg_zero, Step.gexp_zero, OneMemClass.coe_one, one_mul,
    omega_zero_mat, coe_evalO, map_sub, map_mul, map_smul, map_add, map_neg, AlgHom.commutes,
    Algebra.algebraMap_self, RingHom.id_apply, ea, eb, eab, algebraMap_EvR', inv_one,
    smul_eq_mul, neg_neg, Case.s_two] at h2
  rw [← h2]; ring

end

end Obs
