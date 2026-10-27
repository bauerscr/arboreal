import Step2.Flow.FlowSharp1
import Step2.Flow.FlowThm
import Step2.Flow.FlowMaster

/-!
# The sharp marginal flow (`h02uv-outline.tex`, Expected result `thm:flow` (i))

`thm_flow_sharp`: `thm_flow` with (F1) taken from `F1_rg_sharp` (the tadpole cancels exactly
against `16 g² Z² δ w⁽¹⁾`); the band `δ = 1/2` is then a consequence, and in addition for
`1 ≤ j < N_h`:
`|1/ǧ_{j+1} - 1/ǧ_j + β| ≤ C (L^{-2j} + m² L^{2(j+1)}) + C ǧ_j`.

Now a corollary of `flow_master` (`FlowMaster.lean`): the conclusions of `thm_flow` as in
`thm_flow_hor2`, and the sharp bound from the summable `e_j` (`ginv_sharp`, `sharp_fin`).
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Filter Topology Step2.D2

/-- The last arithmetic step of the sharp bound. -/
theorem sharp_fin {β eA E0 K1 C0 B Csh Cg g : ℝ} (h1 : 32 / 7 * eA ≤ K1 * B) (h2 : E0 ≤ C0 * B)
    (hβ : 0 ≤ β) (hB : 0 ≤ B) (hg : 0 ≤ g) (hC1 : 2 * (1 + β) * (K1 + C0) ≤ Csh)
    (hC2 : Cg ≤ Csh) :
    2 * (1 + β) * (32 / 7 * eA + E0) + Cg * g ≤ Csh * B + Csh * g := by
  have a : 32 / 7 * eA + E0 ≤ (K1 + C0) * B := by linarith only [h1, h2]
  have b := mul_le_mul_of_nonneg_left a (by linarith only [hβ] : (0 : ℝ) ≤ 2 * (1 + β))
  have c := mul_le_mul_of_nonneg_right hC1 hB
  have d := mul_le_mul_of_nonneg_right hC2 hg
  have e : 2 * (1 + β) * ((K1 + C0) * B) = 2 * (1 + β) * (K1 + C0) * B := by ring
  linarith only [b, c, d, e]

/-- **Expected result `thm:flow` for the RG map, with the sharp marginal flow.** The conclusions
of `thm_flow`, and in addition, for `1 ≤ j < N_h`,
`|1/ǧ_{j+1} - 1/ǧ_j + β| ≤ C (L^{-2j} + m² L^{2(j+1)}) + C ǧ_j`. -/
theorem thm_flow_sharp : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ ϑ κ cg cm cT ε Csh : ℝ, 0 < ℓ ∧ 0 < A ∧ 0 < ρ ∧ 0 < ϑ ∧ 0 < ε ∧ 0 ≤ κ ∧ κ < 1 ∧
      0 < cg ∧ 0 < cm ∧ 0 < cT ∧ 0 ≤ Csh ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 1 ≤ N → 0 < R.msq →
      R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) →
    ∀ Nh : ℕ, Nh + 2 ≤ N → R.msq * ((L : ℝ) ^ (Nh + 1)) ^ 2 ≤ ϑ →
      (∀ b ∈ Set.Ioc 0 (bmax (betaL L) (1 / 2) cg Nh ε),
          ∃! μ₀, Admissible (rgData R) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀) ∧
      (∀ b μ₀, Admissible (rgData R) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ → ∀ j < Nh,
        |1 / (traj (rgData R) ((L : ℝ) ^ 2) b μ₀ (j + 1)).1 -
            1 / (traj (rgData R) ((L : ℝ) ^ 2) b μ₀ j).1 + betaL L| ≤
          2 * (1 + betaL L) * (1 / 2) * betaL L +
            Cgu (betaL L) cg * (traj (rgData R) ((L : ℝ) ^ 2) b μ₀ j).1) ∧
      ContinuousOn (muc (rgData R) ((L : ℝ) ^ 2) κ cm cT Nh ε)
        (Set.Ioc 0 (bmax (betaL L) (1 / 2) cg Nh ε)) ∧
      ContinuousOn (gN (rgData R) ((L : ℝ) ^ 2) κ cm cT Nh ε)
        (Set.Ioc 0 (bmax (betaL L) (1 / 2) cg Nh ε)) ∧
      (∀ b μ₀, Admissible (rgData R) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ → ∀ j, 1 ≤ j → j < Nh →
        |1 / (traj (rgData R) ((L : ℝ) ^ 2) b μ₀ (j + 1)).1 -
            1 / (traj (rgData R) ((L : ℝ) ^ 2) b μ₀ j).1 + betaL L| ≤
          Csh * ((((L : ℝ) ^ j) ^ 2)⁻¹ + R.msq * ((L : ℝ) ^ (j + 1)) ^ 2) +
            Csh * (traj (rgData R) ((L : ℝ) ^ 2) b μ₀ j).1) := by
  obtain ⟨L₀, h⟩ := flow_master_basic
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨k, ε, aB, U, hX⟩ := h L hL
  have hβ : 0 ≤ betaL L := by
    unfold betaL
    have : 0 ≤ Real.log L :=
      Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
    positivity
  refine ⟨k.ℓ, k.A, k.ρ, 1, k.κ, k.cg, k.cm, k.cT, ε,
    max (2 * (1 + betaL L) * (0 + k.Ke)) (Cgu (betaL L) k.cg), U.hℓ, U.hA, U.hρ, one_pos, U.hε,
    U.hκ0, U.hκ1, U.hcg, U.hcm, U.hcT, le_trans (mul_nonneg (by linarith) (by linarith [U.hKe])) (le_max_left _ _),
    fun N R _ _ hP hi0 hRℓ hRA hRρ hN hm0 hm Nh hNh _ => ?_⟩
  have X := hX N R hP hi0 hRℓ hRA hRρ hN hm0 hm Nh hNh
  obtain ⟨r1, r2, r3, r4⟩ := fh_flow_hist_u X.H U.he U.hε
    (fun b μ₀ μ₁ h₀ h₁ => admissible_unique_z X.H X.HZ U.ha0 U.hs h₀ h₁)
  obtain ⟨e, he0, F1s, -, hej⟩ := X.sharp
  refine ⟨r1, r2, r3, r4, fun b μ₀ hadm j hj1 hj => ?_⟩
  have hs := ginv_sharp X.H U.he hadm hj (he0 j) U.hcg.le (F1s j hj)
  have hg0 : 0 ≤ (traj (rgData R) ((L : ℝ) ^ 2) b μ₀ j).1 :=
    ((admissible_InDh X.H hadm j hj.le).1 j le_rfl).1.le
  have hB : 0 ≤ (((L : ℝ) ^ j) ^ 2)⁻¹ + R.msq * ((L : ℝ) ^ (j + 1)) ^ 2 := by
    have := hm0.le; positivity
  have hfin := sharp_fin (eA := 0) (K1 := 0) (Cg := Cgu (betaL L) k.cg)
    (Csh := max (2 * (1 + betaL L) * (0 + k.Ke)) (Cgu (betaL L) k.cg)) (by simp) (hej j hj1) hβ hB
    hg0 (le_max_left _ _) (le_max_right _ _)
  rw [mul_zero, zero_add] at hfin
  exact hs.trans hfin

end

end Step2
