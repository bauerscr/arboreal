import Spin2.Master.MasterAllFacts
import Spin2.Case2.Case2
import Obs2.Loc.Reloc

/-!
# B3, T2: the scale-`k` one-point bounds at an arbitrary vertex position (from `MasterFacts`)

This file is for the shift–relocate–restart route (Log.md, "B3"). The point configuration
`P : ObsPts 2 L N` is arbitrary, so the vertex position `a = P.a` is arbitrary. Along every
admissible trajectory the one-point Case-(2) chain from `obsInit .two V P` satisfies the
following at every intermediate scale `k`. All statements are corollaries of the fields of
`MasterFacts`; no master construction is copied.

* **`csm_hlam`** (from `M.spin` via `lamConcl_of`, `M.relG`, `M.loop`, `hLam_case2`):
  `‖λ̂^P_k − Θ_k‖ ≤ K_λ Θ_k(ǧ_k + a_k)` for `k < N_h`. Here `Θ_k = (ǧ_k/b)^{1/3}` does not depend
  on `P`, `K_λ = M.csmK`, and `a_k = zA L m k` is the mass term.
* **`csm_artefact`**: the grid artefact. For any two configurations `P`, `P'` (any `a`, `a'`) with
  the same vertex `V`, `‖β^P_k − β^{P'}_k‖ ≤ 2K_λ|μ_{a,0}|Θ_k(ǧ_k + a_k)`.
  **`csm_artefact_rel`**: if `K_λ(ǧ_k + a_k) ≤ 1/2`, then
  `‖β^P_k − β^{P'}_k‖ ≤ 4K_λ(ǧ_k + a_k)‖β^{P'}_k‖`. Here `β_k = bt2 k = −μ_{a,k}` is the
  coupling. The bound holds for all `a, a'`, not only for points in one block; the same-block
  property is not needed for the coupling.
* **`csm_K`** (`M.relBase`): `β_k ≠ 0`, `shA2 ≤ 2‖β_k‖`, the `𝒲` bound, and the `K` bound
  `A^{|X|_k − 4}‖K^{obs}_k(X)‖_{T_k(s_k), w_A} ≤ 16c_W B_k(cǧ_k)² s_k²‖β_k‖` for every connected
  `X` and every `k ≤ N_h` (`γ_a = 0`).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

variable {L : ℕ} [NeZero L]

/-- The `HLam` constant of the Case-(2) chain under the master constants. -/
def MasterFacts.csmK (M : MasterFacts L) : ℝ :=
  lamRelK (betaL L) M.core.cg (M.core.B₁ + M.core.B₂ + M.core.B₃) M.core.B' M.core.cq
    M.core.cRel (eRange (betaL L) M.core.Ke 1) 4

/-- **(H_λ) at every vertex position**: along every admissible trajectory, for every `P` and every
Case-(2) vertex with `μ_a ≠ 0`, `‖λ̂_k − (ǧ_k/b)^{1/3}‖ ≤ K_λ(ǧ_k/b)^{1/3}(ǧ_k + a_k)`, `k < N_h`. -/
theorem csm_hlam (M : MasterFacts L) (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ)
    (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μ₀)
    (P : Obs2.ObsPts 2 L N) (V : Obs2.OCoup .two) (hmu : Obs2.OCoup2.mua V ≠ 0) :
    HLam R Nh m b μ₀ (lamHat2 R P V m b μ₀) M.csmK := by
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by have := M.core.hL49; omega)
  have hLC := lamConcl_of hL2 M.eps_le M.spin
  obtain ⟨hB, -, hloop⟩ := M.loop N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm P V
  exact hLam_case2 (R := R) (P := P) (V := V) hLC hP hi0 hRℓ hRA hRρ (by omega) hm hadm hB M.cRel_nonneg hmu
    (M.relG N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm P V hmu) hloop

theorem csm_bt2_eq {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (P : Obs2.ObsPts 2 L N) (V : Obs2.OCoup .two) (hmu : Obs2.OCoup2.mua V ≠ 0) (m b μ₀ : ℝ)
    (k : ℕ) : bt2 R P V m b μ₀ k = lamHat2 R P V m b μ₀ k * (-Obs2.OCoup2.mua V) := by
  have h0 : bt2 R P V m b μ₀ 0 ≠ 0 := by rw [bt2_zero]; exact neg_ne_zero.2 hmu
  rw [lamHat2, ← bt2_zero R P V m b μ₀, div_mul_cancel₀ _ h0]

/-- **The grid artefact of the coupling**: for two vertex positions (`P`, `P'`) and the same
vertex `V`, `‖β^P_k − β^{P'}_k‖ ≤ 2K_λ|μ_{a,0}|Θ_k(ǧ_k + a_k)`, `k < N_h`. -/
theorem csm_artefact (M : MasterFacts L) (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)]
    [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ)
    (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μ₀)
    (P P' : Obs2.ObsPts 2 L N) (V : Obs2.OCoup .two) (hmu : Obs2.OCoup2.mua V ≠ 0)
    {k : ℕ} (hk : k < Nh) :
    ‖bt2 R P V m b μ₀ k - bt2 R P' V m b μ₀ k‖ ≤
      2 * M.csmK * ‖Obs2.OCoup2.mua V‖ *
        ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 / b) ^ (1 / 3 : ℝ) *
        ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) := by
  have h1 := csm_hlam M N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm P V hmu k hk
  have h2 := csm_hlam M N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm P' V hmu k hk
  rw [csm_bt2_eq R P V hmu, csm_bt2_eq R P' V hmu, ← sub_mul, norm_mul, norm_neg]
  set Θ : ℂ := ((((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 / b) ^ (1 / 3 : ℝ) : ℝ) : ℂ)
  set E := M.csmK * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 / b) ^ (1 / 3 : ℝ) *
    ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k)
  have hd : ‖lamHat2 R P V m b μ₀ k - lamHat2 R P' V m b μ₀ k‖ ≤ 2 * E := by
    have e : lamHat2 R P V m b μ₀ k - lamHat2 R P' V m b μ₀ k =
        (lamHat2 R P V m b μ₀ k - Θ) - (lamHat2 R P' V m b μ₀ k - Θ) := by ring
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    linarith
  calc ‖lamHat2 R P V m b μ₀ k - lamHat2 R P' V m b μ₀ k‖ * ‖Obs2.OCoup2.mua V‖
      ≤ 2 * E * ‖Obs2.OCoup2.mua V‖ := mul_le_mul_of_nonneg_right hd (norm_nonneg _)
    _ = _ := by simp only [E]; ring

/-- The lower bound `‖β^{P}_k‖ ≥ |μ_{a,0}|Θ_k(1 − K_λ(ǧ_k + a_k))`. -/
theorem csm_bt2_lower (M : MasterFacts L) (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)]
    [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ)
    (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μ₀)
    (P : Obs2.ObsPts 2 L N) (V : Obs2.OCoup .two) (hmu : Obs2.OCoup2.mua V ≠ 0)
    {k : ℕ} (hk : k < Nh) :
    ‖Obs2.OCoup2.mua V‖ * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 / b) ^ (1 / 3 : ℝ) *
        (1 - M.csmK * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k)) ≤
      ‖bt2 R P V m b μ₀ k‖ := by
  have h1 := csm_hlam M N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm P V hmu k hk
  rw [csm_bt2_eq R P V hmu, norm_mul, norm_neg]
  set θ := ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 / b) ^ (1 / 3 : ℝ)
  have hnθ : θ ≤ ‖((θ : ℝ) : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]; exact le_abs_self θ
  have hl : θ - M.csmK * θ * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) ≤
      ‖lamHat2 R P V m b μ₀ k‖ := by
    have := norm_sub_norm_le ((θ : ℝ) : ℂ) (((θ : ℝ) : ℂ) - lamHat2 R P V m b μ₀ k)
    rw [sub_sub_cancel, norm_sub_rev] at this
    linarith
  calc ‖Obs2.OCoup2.mua V‖ * θ * (1 - M.csmK *
        ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k))
      = (θ - M.csmK * θ * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k)) *
          ‖Obs2.OCoup2.mua V‖ := by ring
    _ ≤ ‖lamHat2 R P V m b μ₀ k‖ * ‖Obs2.OCoup2.mua V‖ :=
        mul_le_mul_of_nonneg_right hl (norm_nonneg _)

/-- **The grid artefact, relative form**: if `0 ≤ K_λ(ǧ_k + a_k) ≤ 1/2`, then
`‖β^P_k − β^{P'}_k‖ ≤ 4K_λ(ǧ_k + a_k)‖β^{P'}_k‖`. -/
theorem csm_artefact_rel (M : MasterFacts L) (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)]
    [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ)
    (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μ₀)
    (P P' : Obs2.ObsPts 2 L N) (V : Obs2.OCoup .two) (hmu : Obs2.OCoup2.mua V ≠ 0)
    {k : ℕ} (hk : k < Nh)
    (hs0 : 0 ≤ M.csmK * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k))
    (hs : M.csmK * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) ≤ 1 / 2) :
    ‖bt2 R P V m b μ₀ k - bt2 R P' V m b μ₀ k‖ ≤
      4 * (M.csmK * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k)) *
        ‖bt2 R P' V m b μ₀ k‖ := by
  have h1 := csm_artefact M N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm P P' V hmu hk
  have h2 := csm_bt2_lower M N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm P' V hmu hk
  set s := M.csmK * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k)
  set u := ‖Obs2.OCoup2.mua V‖ * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 / b) ^ (1 / 3 : ℝ)
  have e1 : 2 * M.csmK * ‖Obs2.OCoup2.mua V‖ *
      ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 / b) ^ (1 / 3 : ℝ) *
      ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) = 2 * s * u := by
    simp only [s, u]; ring
  rw [e1] at h1
  have hu2 : u * (1 / 2) ≤ u * (1 - s) ∨ u < 0 := by
    rcases le_or_gt 0 u with hu | hu
    · left; exact mul_le_mul_of_nonneg_left (by linarith) hu
    · right; exact hu
  rcases hu2 with hu2 | hu2
  · have : 2 * s * u ≤ 4 * s * (u * (1 - s)) := by
      have := mul_le_mul_of_nonneg_left hu2 (show 0 ≤ 4 * s by linarith)
      linarith
    exact h1.trans (this.trans (by
      have := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 4 * s by linarith)
      linarith))
  · have : 2 * s * u ≤ 0 := by
      have := mul_nonneg (show 0 ≤ 2 * s by linarith) (show 0 ≤ -u by linarith)
      linarith
    exact h1.trans (this.trans (mul_nonneg (by linarith) (norm_nonneg _)))

/-- **The `K` part and the coupling at every scale `k ≤ N_h`** (`M.relBase`, `γ_a = 0`), at an
arbitrary vertex position `P.a`: `β_k ≠ 0`, `shA2 ≤ 2‖β_k‖`, the `𝒲^{obs}` bound and the
`K^{obs}` bound `≤ 16c_WB_k(cǧ_k)²s_k²‖β_k‖`. -/
theorem csm_K (M : MasterFacts L) (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ)
    (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μ₀)
    (P : Obs2.ObsPts 2 L N) (V : Obs2.OCoup .two) (hga : Obs2.OCoup2.ga V = 0)
    (hmu : Obs2.OCoup2.mua V ≠ 0) (hNh0 : 0 < Nh) {k : ℕ} (hk : k ≤ Nh) :
    0 < ‖bt2 R P V m b μ₀ k‖ ∧
    Obs2.shA2 (Obs2.histVO2 (R.withMsq m) P (Obs2.obsInit .two V P)
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) k ≤ 2 * ‖bt2 R P V m b μ₀ k‖ ∧
    WbHc (R.withMsq m) P (Obs2.obsInit .two V P) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k
      (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1) *
        (2 * PtCorr2.histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
          ‖bt2 R P V m b μ₀ k‖)) ∧
    KbHc (R.withMsq m) P (Obs2.obsInit .two V P) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k
      (16 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1) ^ 2 *
        (PtCorr2.histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
          ‖bt2 R P V m b μ₀ k‖)) :=
  M.relBase N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm P V hga hmu hNh0 k hk

end

end Spin2
