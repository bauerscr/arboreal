import PtCorr2.Obs.ObsLoc
import PtCorr2.Zero.Ward2

/-!
# The two-point function as a ratio of components of the observable RG product

`thm_obs_chain_twopt_loc` gives `⟨Z_0⟩_{Γ_0} = (rgProdO)_∅` and
`μ_aμ_b⟨Z_0ψ̄_aψ_b⟩_{Γ_0} = (rgProdO)_{ab}` (Case (1), no `ab` couplings) along every trajectory.
With `⟨Z_0⟩_{Γ_0} ≠ 0` (`h ≥ 0`) this is the exact identity

  `(rgProdO)_{ab} = (μ_aμ_b⟨ψ̄_aψ_b⟩) • (rgProdO)_∅`

(`twopt_rg_repr`), i.e. `b⟨ψ̄_0ψ_x⟩` (the left side of `Spin2.TwoPtSq`) is `b/(μ_aμ_b)` times the
ratio of the `ab` and `∅` components of the observable RG product at `a = 0`, `b = x`.
`avg0_eq_omega_traj`: `⟨F⟩ = ⟨Z_0F⟩_{Γ_0}/⟨Z_0⟩_{Γ_0}` along a trajectory started at `(b, μ₀, 0)`.
-/

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD Obs2 Flow2 Flow2.Hist

variable {L N : ℕ} [NeZero L]

section Hist

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N)

/-- `⟨F⟩ = ⟨Z_0F⟩_{Γ_0}/⟨Z_0⟩_{Γ_0}` along a trajectory started at `(b, μ₀, 0)`. -/
theorem avg0_eq_omega_traj (hL7 : 7 ≤ L) (hm0 : 0 < R.msq) (hN : 1 ≤ N) (t : Hist.Seq (Xs R))
    {b μ₀ : ℝ} (ht : t 0 = (b, μ₀, 0)) (F : Alg 2 L N) :
    avg0 L N R.msq b μ₀ F =
      omegaC (Γh R 0 t) ((Zh R 0 t : Alg 2 L N) * F) / omegaC (Γh R 0 t) (Zh R 0 t : Alg 2 L N) := by
  rw [Γh_zero_eq_Cov R hL7 hm0 hN t, Zh_zero_eq_Z0 R t ht]
  simp only [← omega_eq_omegaC]
  rfl

/-- **The exact RG representation of the two-point function** (Case (1), `AbFree`, `h ≥ 0`):
`(rgProdO)_{ab} = (μ_aμ_b⟨ψ̄_aψ_b⟩) • (rgProdO)_∅` along the trajectory from `(b, μ₀)`. -/
theorem twopt_rg_repr {Nh : ℕ} (hN : Nh + 2 = N) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < R.msq)
    (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt R j)
    (hVL : ValidAtL R Nh) (hL7 : 7 ≤ L) {b μ₀ : ℝ} (hb : 0 < b) (hh : b ≤ μ₀ + R.msq)
    (V : OCoup1) (hVab : AbFree .one V) :
    let t := traj (rgData R) ((L : ℝ) ^ 2) b μ₀
    ((rgProdO R P (obsInit .one V P) Nh t : OE .one (Lam 2 L N)) : SA .one (Lam 2 L N)).ab =
      (V.mua * V.mub * avg0 L N R.msq b μ₀ (psibar P.a * psi P.b)) •
        ((rgProdO R P (obsInit .one V P) Nh t : OE .one (Lam 2 L N)) : SA .one (Lam 2 L N)).e := by
  intro t
  obtain ⟨he, hab⟩ := thm_obs_chain_twopt_loc R P hN hρ1 hspl hm0 hm hV hVL b μ₀ V hVab
  have ht : t 0 = (b, μ₀, 0) := Hist.traj_zero _ _
  have hZ := omega_Zh_zero_ne R hL7 hm0 (by omega) t hb hh ht
  have hA := avg0_eq_omega_traj R hL7 hm0 (by omega) t ht (psibar P.a * psi P.b)
  simp only [t] at hZ hA ⊢
  rw [← he, ← hab, hA, mul_smul_comm, omegaC_smul, Algebra.smul_def, ← map_mul]
  congr 1
  field_simp

end Hist

end

end PtCorr2
