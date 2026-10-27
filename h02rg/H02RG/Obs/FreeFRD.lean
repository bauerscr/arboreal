import Obs.Warmup
import Suscept.Cov

/-!
# The free observable flow along the finite range decomposition

With `C_{k+1} = covAt d L N m² k` for `k < N` and, as in the text, `C_{N+1} = t_N Q_N`
(`covSeq`), `∑_{k ≤ N} C_{k+1} = (-Δ + m²)^{-1}` (`sum_covSeq`, from `Suscept.Cov_eq`, i.e.
`FRD.decomposition_inv` and `FRD.CNN_eq`).  Hence (for `m² > 0`, `N ≥ 1`):

* `frd_warmup_one`, `frd_warmup_two_a`, `frd_warmup_two_ab` (`e:warmupcor`):
  `λ_aλ_b ⟨ψ̄_aψ_b⟩ = q_{N+1}`, `λ_a ⟨ψ̄_aψ_a⟩ = γ_{a,N+1}`,
  `λ_aλ_b ⟨ψ̄_aψ_a; ψ̄_bψ_b⟩ = q_{N+1}` for the free flow with initial coupling constants
  `(λ_a, λ_b, 0, …)`, where `⟨·⟩ = omega (Cov d L N m²)`;
* `frd_q_two`: `q_{N+1} = -λ_aλ_b (∑_{k ≤ N} C_k(a,b) + t_N Q_N(a,b))² =
  -λ_aλ_b (-Δ + m²)^{-1}(a,b)²`;
* `frd_warmup_conclusion` (`e:warmupcor-conclusion`):
  `⟨ψ̄_aψ_a; ψ̄_bψ_b⟩ = -(-Δ + m²)^{-1}(a,b)²`.
-/

namespace Obs

noncomputable section

open Finset Grassmann Loc FRD Step Flow Suscept

variable {d L : ℕ} [NeZero L]

theorem psd_symm {ι : Type*} [Fintype ι] {C : Matrix ι ι ℝ} (h : C.PosSemidef) (x y : ι) :
    C x y = C y x := by
  simpa using (h.1.apply x y).symm

theorem covAt_symm {msq : ℝ} (hmsq : 0 ≤ msq) (N j : ℕ) (x y : Lam d L N) :
    covAt d L N msq j x y = covAt d L N msq j y x := by
  cases N with
  | zero => simp [covAt]
  | succ M =>
    simp only [covAt]
    split_ifs
    · exact psd_symm (Cj_posSemidef stdPt hmsq (by positivity) _) x y
    · exact psd_symm (CN_posSemidef stdPt hmsq (by positivity) _) x y

variable (d L) in
/-- The covariances `C_1, …, C_N, C_{N+1} = t_N Q_N` of the steps (indexed from `0`). -/
def covSeq (N : ℕ) (msq : ℝ) (k : ℕ) : Matrix (Lam d L N) (Lam d L N) ℝ :=
  if k < N then covAt d L N msq k else tNN d L N msq • QN

theorem sum_covSeq {msq : ℝ} (hmsq : 0 < msq) {N : ℕ} (hN : 1 ≤ N) :
    ∑ k ∈ range (N + 1), covSeq d L N msq k = Cov d L N msq := by
  rw [Cov_eq hmsq hN, sum_range_succ, covSeq, if_neg (lt_irrefl N)]
  congr 1
  exact sum_congr rfl fun k hk => by rw [covSeq, if_pos (mem_range.1 hk)]

theorem covSeq_symm {msq : ℝ} (hmsq : 0 ≤ msq) (N : ℕ) (a b : Lam d L N) (k : ℕ) :
    covSeq d L N msq k a b = covSeq d L N msq k b a := by
  unfold covSeq
  split_ifs
  · exact covAt_symm hmsq N k a b
  · simp [QN]

/-- `e:warmupcor`, Case (2) (`⟨ψ̄_aψ_a; ψ̄_bψ_b⟩`), along the finite range decomposition. -/
theorem frd_warmup_two_ab {msq : ℝ} (hmsq : 0 < msq) {N : ℕ} (hN : 1 ≤ N) (a b : Lam d L N)
    (la lb : ℂ) :
    la * lb * (omega (Cov d L N msq) (psibar a * psi a * (psibar b * psi b)) -
      omega (Cov d L N msq) (psibar a * psi a) * omega (Cov d L N msq) (psibar b * psi b)) =
      (flow2 (covSeq d L N msq) a b ⟨la, lb, 0, 0, 0, 0, 0, 0, 0⟩ (N + 1)).q := by
  rw [← sum_covSeq hmsq hN]
  exact warmup_two_ab _ a b (covSeq_symm hmsq.le N a b) la lb (N + 1)

/-- `q_{N+1} = -λ_aλ_b (∑_{k ≤ N} C_k(a,b) + t_N Q_N(a,b))² = -λ_aλ_b (-Δ + m²)^{-1}(a,b)²`. -/
theorem frd_q_two {msq : ℝ} (hmsq : 0 < msq) {N : ℕ} (hN : 1 ≤ N) (a b : Lam d L N)
    (la lb : ℂ) :
    (flow2 (covSeq d L N msq) a b ⟨la, lb, 0, 0, 0, 0, 0, 0, 0⟩ (N + 1)).q =
        -(la * lb) * ((∑ k ∈ range N, (covAt d L N msq k a b : ℂ)) +
          (tNN d L N msq * QN a b : ℝ)) ^ 2 ∧
      (flow2 (covSeq d L N msq) a b ⟨la, lb, 0, 0, 0, 0, 0, 0, 0⟩ (N + 1)).q =
        -(la * lb) * (Cov d L N msq a b : ℂ) ^ 2 := by
  have h := flow2_q (covSeq d L N msq) a b la lb 0 0 (N + 1)
  have hs : ∑ k ∈ range (N + 1), (covSeq d L N msq k a b : ℂ) = (Cov d L N msq a b : ℂ) := by
    rw [← sum_covSeq hmsq hN, Matrix.sum_apply]; push_cast; rfl
  refine ⟨?_, by rw [h, hs]⟩
  rw [h, sum_range_succ, covSeq, if_neg (lt_irrefl N)]
  congr 3
  exact sum_congr rfl fun k hk => by rw [covSeq, if_pos (mem_range.1 hk)]

/-- `e:warmupcor-conclusion`: `⟨ψ̄_aψ_a; ψ̄_bψ_b⟩ = -(-Δ + m²)^{-1}(a,b)²` (free fermions),
obtained from the free observable flow along the finite range decomposition. -/
theorem frd_warmup_conclusion {msq : ℝ} (hmsq : 0 < msq) {N : ℕ} (hN : 1 ≤ N) (a b : Lam d L N) :
    omega (Cov d L N msq) (psibar a * psi a * (psibar b * psi b)) -
      omega (Cov d L N msq) (psibar a * psi a) * omega (Cov d L N msq) (psibar b * psi b) =
      -(Cov d L N msq a b : ℂ) ^ 2 := by
  have h := frd_warmup_two_ab hmsq hN a b 1 1
  rw [(frd_q_two hmsq hN a b 1 1).2] at h
  simpa using h

end

end Obs
