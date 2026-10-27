import Flow.Continuity
import Suscept.PropSuscept

-- Merged from `Suscept/Continuity.lean` (phase 3).
section

/-!
# Proposition `prop:ZNN`: continuity of `k_N^0`, `k_N^2` in `m²`

If the coupling constants of `V₀(m²)` are continuous on `S ⊆ [0, ∞)`, then so are `a_N`, `u_N`,
`k_N^0`, `k_N^2`, `ã_{N,N}` (`prop_ZNN_cont`), and `ũ_{N,N}` is continuous on `S ∩ (0, ∞)` (it
contains `t_N ~ m^{-2}`).  This uses the continuity of the bulk flow along continuous families
(`Flow.flowN_cont`, `Flow.uflow_cont`, `Flow/Continuity.lean`).
-/

namespace Suscept

noncomputable section

open Finset Grassmann Loc FRD Step Flow Coup

variable {d L : ℕ} [NeZero L] {N : ℕ} {S : Set ℝ}

/-- **Proposition `prop:ZNN`, continuity**: if the coupling constants of `V₀(m²)` are continuous
on `S ⊆ [0, ∞)` (and the covariances satisfy `GoodCov` there, e.g. for `ℓ₀` large,
`goodCov_covAt`), then `a_N`, `u_N`, `k_N^0`, `k_N^2` and `ã_{N,N}` are continuous on `S`, and
`ũ_{N,N}` is continuous on `S ∩ (0, ∞)`. -/
theorem prop_ZNN_cont (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {ℓ₀ : ℝ} {V₀ : ℝ → Vcoup}
    (hS : S ⊆ Set.Ici 0) (hV₀ : CV S V₀)
    (hgood : ∀ m ∈ S, ∀ j < N, GoodCov (d := d) (L := L) (N := N) j ℓ₀ (covAt d L N m j)) :
    ContinuousOn (fun m => aN d L N m (V₀ m)) S ∧
      ContinuousOn (fun m => uN d L N m (V₀ m)) S ∧
      ContinuousOn (fun m => kN0 d L N m (V₀ m)) S ∧
      ContinuousOn (fun m => kN2 d L N m (V₀ m)) S ∧
      ContinuousOn (fun m => atN d L N m (V₀ m)) S ∧
      ContinuousOn (fun m => utN d L N m (V₀ m)) (S ∩ Set.Ioi 0) := by
  have hC : ∀ j < N, ∀ x y, ContinuousOn (fun m => covAt d L N m j x y) S :=
    fun j hj x y => (covAt_continuousOn hd hj x y).mono hS
  obtain ⟨hV, hK⟩ := flowN_cont hd hL hV₀ hC hgood N le_rfl
  have ha : ContinuousOn (fun m => aN d L N m (V₀ m)) S := hV.a
  have hk0 : ContinuousOn (fun m => kN0 d L N m (V₀ m)) S :=
    (hK univ).lin (ε : Alg d L N →ₐ[ℂ] ℂ).toLinearMap
  have hk2 : ContinuousOn (fun m => kN2 d L N m (V₀ m)) S := by
    unfold kN2 c2
    exact continuousOn_finsetSum _ fun x _ => continuousOn_finsetSum _ fun y _ => hK univ 2 _
  have hat : ContinuousOn (fun m => atN d L N m (V₀ m)) S := ha.sub (hk2.div_const _)
  refine ⟨ha, continuousOn_finsetSum _ fun j hj => uflow_cont hd hL hV₀ hC hgood
    (mem_range.1 hj), hk0, hk2, hat, ?_⟩
  have ht : ContinuousOn (fun m => (tNN d L N m : ℂ)) (S ∩ Set.Ioi 0) :=
    Complex.continuous_ofReal.comp_continuousOn
      ((tN_continuousOn stdPt hd (Nat.cast_nonneg L) N).mono Set.inter_subset_right)
  exact (hk0.mono Set.inter_subset_left).add ((hat.mono Set.inter_subset_left).mul ht)

end

end Suscept

end

/-!
# Section `sec:suscept`: summary for the covariances of Section `sec:frd`

`sec_suscept`: for `d ≥ 3`, `L ≥ 2^{d+3}` and `ℓ₀² ≥ K L^{d-2+2p_Φ}` (`e:Cleq1`, which gives the
hypotheses `GoodCov` of the steps), for every `N ≥ 1`, `m² > 0` and `V₀`:
`e:ZNN-def`, `e:ZNN` and `e:suscept-atilde` hold for the torus flow `flowN N m² V₀`.
-/

namespace Suscept

noncomputable section

open Finset Grassmann Loc FRD Step Flow

local notation "PP" Λ => psiC Λ * psibarC Λ

/-- **Section `sec:suscept`** (`e:ZNN-def`, `prop:ZNN` `e:ZNN`, `prop:suscept`
`e:suscept-atilde`) for the covariances of Section `sec:frd`. -/
theorem sec_suscept {d : ℕ} (hd : 3 ≤ d) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ (L : ℕ) [NeZero L], 2 ^ (d + 3) ≤ L → ∀ (ℓ₀ : ℝ), 0 < ℓ₀ →
      K * (L : ℝ) ^ ((d : ℝ) - 2 + 2 * pPhi d) ≤ ℓ₀ ^ 2 →
      ∀ (N : ℕ), 1 ≤ N → ∀ (msq : ℝ), 0 < msq → ∀ V₀ : Vcoup,
        ZNN d L N msq V₀ = Complex.exp (-(uN d L N msq V₀ * Fintype.card (Lam d L N))) •
          EC (tNN d L N msq • QN) (theta (((gexp (-(VE (VN d L N msq V₀)
            (univ : Finset (Lam d L N)) : EvR (Lam d L N))) + KN d L N msq V₀ :
              EvR (Lam d L N))) : Alg d L N)) ∧
        Rc (Lam d L N) (ZtNN d L N msq V₀) =
          algebraMap ℂ (Alg d L N) (1 + utN d L N msq V₀) -
            ((Fintype.card (Lam d L N) : ℂ) * atN d L N msq V₀) • (PP (Lam d L N)) ∧
        omega (Cov d L N msq) (Z0 d L N V₀) =
          Complex.exp (-(uN d L N msq V₀ * Fintype.card (Lam d L N))) *
            (1 + utN d L N msq V₀) ∧
        (1 + utN d L N msq V₀ ≠ 0 →
          ∑ x : Lam d L N, omega (Cov d L N msq) (Z0 d L N V₀ * (psibar 0 * psi x)) /
              omega (Cov d L N msq) (Z0 d L N V₀) =
            1 / (msq : ℂ) - 1 / (msq : ℂ) ^ 2 * (atN d L N msq V₀ / (1 + utN d L N msq V₀))) := by
  obtain ⟨K, hK, hg⟩ := goodCov_covAt hd
  refine ⟨K, hK, fun L _ hL ℓ₀ hℓ₀ hKℓ N hN msq hmsq V₀ => ?_⟩
  have hd1 : 1 ≤ d := by omega
  have hgood := hg L ℓ₀ hℓ₀ hKℓ N msq hmsq.le
  exact ⟨ZNN_eq hd1 hL hN hmsq hgood V₀, prop_ZNN hd1 hL hN hmsq hgood V₀,
    EC_Z0 hd1 hL hN hmsq hgood V₀, prop_suscept hd1 hL hN hmsq hgood V₀⟩

end

end Suscept
