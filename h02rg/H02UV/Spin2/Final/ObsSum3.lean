import Spin2.Final.ObsSum2
import Spin2.Final.ObsBeta3

set_option autoImplicit false

/-!
# The continuum limit with the summed observable renormalisation condition

**`thm_arboreal_limit_sum`**: for `t ≥ t₀` there is a sequence `β_N` with
`obsBetaSum L N β_N = β_N (E_{β_N}|T_0|/|Λ_N|)^{3/2} = t` (`N ≥ N₀`) such that the normalised
two-point functions `f^Σ_N(x) = P_{β_N}[0 ↔ x_N]/obsDens L N β_N` (`obsFS`), whose lattice
average is `1`, are asymptotically equicontinuous on every `{‖x‖ ≥ r}` and a subsequence converges
uniformly on compact subsets of `𝕋² ∖ {0}` to a continuous, nonnegative, point-group invariant
`G`, bounded on `{‖x‖ ≥ δ}`, with the short-distance law
`|G(x) − csA t |x|| ≤ K' csA t |x| csRate |x|` for `0 < |x| < δ₀`.

**Route.** The proof is that of `thm_arboreal_limit_obs` (`ObsBeta3`) with `ob_master` replaced by
`os_master` and `obsF_eq_clF` by `obsFS_eq_clF` (`f^Σ_N = clF L t b N` under
`obsBetaSum L N (1/b_N) = t`, `os_dens_of_obsBetaSum`); the clause `G(x₀) = 1` of
`thm_arboreal_limit_obs` is replaced by the lattice average `(1/L^{2N})∑_x f^Σ_N(x) = 1`
(`obsFS_avg`). The normalisation `∫_{𝕋²} G = 1` is not formalised.
-/

namespace Spin2

open Step Step2 PtCorr2 Cont Loc Grassmann Step2.D2

noncomputable section

open Finset Flow2 Flow2.Hist Set Filter Topology

variable {L : ℕ} [NeZero L]

set_option maxHeartbeats 4000000 in
/-- **The continuum limit of the arboreal gas with the summed observable renormalisation
condition.** For `L ≥ L₀` there are constants `t₀ ≥ 1`, `K, K_s, K_c, K_ε, E, a` and `N₀ ≥ 3`
depending on `L` only such that for every `t ≥ t₀` there are `δ₀ ∈ (0,1)`, `K' ≥ 0` and a sequence
`β_N > 0` with: for `N ≥ N₀`, `β_N · obsDens L N β_N^{3/2} = t`, the lattice average
`(1/L^{2N})∑_{x ∈ Λ_N} P_{β_N}[0 ↔ x]/obsDens L N β_N = 1` of the normalised two-point function,
and the conclusions `ObsScale`, `ArbShort` (at `t`) of `thm_arboreal_sum`; the normalised
two-point functions `f^Σ_N(x) = P_{β_N}[0 ↔ x_N]/obsDens L N β_N` (`obsFS`) are asymptotically
equicontinuous on every `{‖x‖ ≥ r}`; and a subsequence converges uniformly on compact subsets of
`𝕋² ∖ {0}` to a continuous, nonnegative, point-group invariant `G`, bounded on `{‖x‖ ≥ δ}` for
every `δ > 0`, with `|G(x) − (β₁λ/t)^{2/3}| ≤ K'(β₁λ/t)^{2/3} log λ/λ`, `λ = log(1/|x|)`, for
`0 < |x| < δ₀`. -/
theorem thm_arboreal_limit_sum : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ (t₀ K Ks Kc Kε E a : ℝ) (N₀ : ℕ), 1 ≤ t₀ ∧ 0 ≤ K ∧ 0 ≤ E ∧ 0 ≤ a ∧ 0 < Kc ∧ 0 ≤ Kε ∧
    3 ≤ N₀ ∧
    ∀ t : ℝ, t₀ ≤ t →
    ∃ δ₀ K' : ℝ, 0 < δ₀ ∧ δ₀ < 1 ∧ 0 ≤ K' ∧
    ∃ βs : ℕ → ℝ,
      (∀ N : ℕ, N₀ ≤ N → 0 < βs N ∧ obsBetaSum L N (βs N) = t ∧
        (∑ x : Lam 2 L N, Pconn L N (βs N) x / obsDens L N (βs N)) / (L : ℝ) ^ (2 * N) = 1 ∧
        ∃ β : ℕ → ℝ, ObsScale L N t K Kc Kε E a (βs N) β ∧ ArbShort L N t Ks Kc (βs N)) ∧
      ClEqui (obsFS L βs) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : UnitAddTorus (Fin 2) → ℝ, ContinuousOn G {0}ᶜ ∧
        (∀ S ⊆ ({0}ᶜ : Set (UnitAddTorus (Fin 2))), IsCompact S →
          TendstoUniformlyOn (fun k => obsFS L βs (φ k)) G atTop S) ∧
        (∀ x, x ≠ 0 → 0 ≤ G x) ∧
        (∀ (τ : Equiv.Perm (Fin 2)) (s : Fin 2 → Bool) x, x ≠ 0 → G (clSgn τ s x) = G x) ∧
        (∀ δ > 0, ∃ C, ∀ x, δ ≤ ‖x‖ → G x ≤ C) ∧
        (∀ x, x ≠ 0 → torusNorm x < δ₀ →
          |G x - csA t (torusNorm x)| ≤ K' * csA t (torusNorm x) * csRate (torusNorm x)) := by
  classical
  obtain ⟨L₀, h⟩ := eqs_master
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨M, -, -, hcab, hBk⟩ := h L hL
  obtain ⟨K, Ks, Kc, Kε, E, a, t₀, N₀, hK, hE, ha, hKc, hKε, ht₀, hN₀, hF⟩ := M.os_master
  obtain ⟨g₁, N₁, hg₁, hN₁, hSB⟩ := arb_eqs_shortBound M
  obtain ⟨g₂, hg₂, hEq⟩ := M.fx_clEqui hcab hBk
  have hL2 := M.ct_L2
  set N₂ := max N₀ N₁ with hN₂d
  refine ⟨t₀ + 8 / g₁ + 8 / g₂, K, Ks, Kc, Kε, E, a, N₂, by
    have : 0 ≤ 8 / g₁ + 8 / g₂ := by positivity
    linarith, hK, hE, ha, hKc, hKε, le_trans hN₀ (le_max_left _ _), fun t ht => ?_⟩
  have h81 : 0 ≤ 8 / g₁ := by positivity
  have h82 : 0 ≤ 8 / g₂ := by positivity
  have ht₀' : t₀ ≤ t := by linarith
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hgi₁ : ∀ i, 1 / obsBR t i ≤ g₁ := ob_inv_obsBR_le hg₁ ht0 (by linarith)
  have hgi₂ : ∀ i, 1 / obsBR t i ≤ g₂ := ob_inv_obsBR_le hg₂ ht0 (by linarith)
  obtain ⟨hεt, hex⟩ := hF t ht₀'
  -- the sequence
  choose! bN hbN using hex
  set b : ℕ → ℝ := fun N => if N₀ ≤ N then bN N else 1 with hbd
  have hbeq : ∀ N, N₀ ≤ N → b N = bN N := fun N hN => if_pos hN
  have hb_pos : ∀ N, 0 < b N := fun N => by
    by_cases hN : N₀ ≤ N
    · rw [hbeq N hN]; exact (hbN N hN).1
    · show (if N₀ ≤ N then bN N else 1) > 0
      rw [if_neg hN]; exact one_pos
  have hbΦ : ∀ N, N₀ ≤ N → obsBetaSum L N (1 / b N) = t := fun N hN => by
    rw [hbeq N hN]; exact (hbN N hN).2.1
  set βs : ℕ → ℝ := fun N => 1 / b N with hβsd
  have hobsF : ∀ N, N₀ ≤ N → obsFS L βs N = clF L t b N :=
    fun N hN => obsFS_eq_clF (hb_pos N) (hbΦ N hN)
  -- the four auxiliary admissible sequences
  set bI : ℕ → ℕ → ℝ := fun i N =>
    if b N ∈ ctBracket M (a5wR M N) (obsMass L N t) (obsBR t i) then b N else M.obsA N t (i + 1)
    with hbId
  have hbI_eq : ∀ i N, b N ∈ ctBracket M (a5wR M N) (obsMass L N t) (obsBR t i) → bI i N = b N :=
    fun i N h => if_pos h
  have hbI_mem : ∀ i ≤ 3, ∀ N, 2 ≤ N →
      bI i N ∈ ctBracket M (a5wR M N) (obsMass L N t) (obsBR t i) ∧ 0 < bI i N := by
    intro i hi N hN
    obtain ⟨hpos, hmono, -⟩ := M.obs_union hN ht1 hεt
    have hmem : bI i N ∈ ctBracket M (a5wR M N) (obsMass L N t) (obsBR t i) := by
      by_cases h : b N ∈ ctBracket M (a5wR M N) (obsMass L N t) (obsBR t i)
      · rw [hbI_eq i N h]; exact h
      · show (if b N ∈ ctBracket M (a5wR M N) (obsMass L N t) (obsBR t i) then b N
          else M.obsA N t (i + 1)) ∈ _
        rw [if_neg h, M.obs_bracket_eq N ht0 i]
        exact ⟨le_rfl, hmono i hi⟩
    refine ⟨hmem, ?_⟩
    rw [M.obs_bracket_eq N ht0 i] at hmem
    exact lt_of_lt_of_le (hpos (i + 1) (by omega)) hmem.1
  have hAdm : ∀ i ≤ 3, ClAdm M N₁ (obsBR t i) (a5wR M) (fun N => obsMass L N t) (bI i) := by
    intro i hi N hN
    obtain ⟨hm0, -, hwin⟩ := obsMass_spec (L := L) N ht1
    obtain ⟨hmem, hpos⟩ := hbI_mem i hi N (by omega)
    exact ⟨inferInstance, inferInstance, rfl, rfl, rfl, rfl, rfl, hm0, hwin i hi, hmem, hpos⟩
  -- the relation `clF L t b N = c_i clF L (obsBR t i) b^{(i)} N`
  set c : ℕ → ℝ := fun i => (obsBR t i / t) ^ (2 / 3 : ℝ) with hcd
  have hc : ∀ i ∈ range 4, |c i| ≤ 8 := fun i hi => ob_c_le ht0 (by
    have := Finset.mem_range.1 hi; omega)
  have hrel : ∀ N, N₀ ≤ N → ∃ i ∈ range 4, ∀ x,
      clF L t b N x = c i * clF L (obsBR t i) (bI i) N x := by
    intro N hN
    obtain ⟨-, -, ⟨i, hi, hbi⟩, -⟩ := hbN N hN
    rw [← hbeq N hN] at hbi
    refine ⟨i, Finset.mem_range.2 (by omega), fun x => ?_⟩
    have e : clF L (obsBR t i) (bI i) N x = clF L (obsBR t i) b N x := by
      unfold clF; rw [hbI_eq i N hbi]
    rw [e]
    exact clF_rescale ht0 (obsBR_pos ht0 i) (hb_pos N) x
  -- equicontinuity of `clF L t b`
  have hEqT : ∀ r > 0, ClEquiOn (clF L t b) r := fun r hr =>
    ob_equiOn_of_family (range 4) (fun i => clF L (obsBR t i) (bI i)) c hc
      (fun i hi => (clEqui_iff_on _).1 (hEq N₁ (obsBR t i) (a5wR M) _ (bI i) (obsBR_pos ht0 i)
        (hgi₂ i) (hAdm i (by have := Finset.mem_range.1 hi; omega))) r hr)
      (clF L t b) N₀ hrel
  -- the shifted sequence, bounded for all `N`
  set F : ℕ → UnitAddTorus (Fin 2) → ℝ := fun N => clF L t b (N + N₂) with hFd
  have hBdF : ∀ r > 0, ∃ C, ∀ N x, r ≤ dist x 0 → |F N x| ≤ C := fun r hr =>
    ob_bdd_of_family (range 4) (fun i => clF L (obsBR t i) (bI i)) c hc
      (fun i hi => t6_bdd hL2 (obsBR_pos ht0 i) (hAdm i (by have := Finset.mem_range.1 hi; omega))
        (hSB (obsBR t i) (obsBR_pos ht0 i) (hgi₁ i)).1 r hr)
      F (fun N => N + N₂) (fun N => hrel (N + N₂) (by omega))
  have hEqF : ∀ r > 0, ClEquiOn F r := fun r hr η hη => by
    obtain ⟨δ, hδ, N', hN'⟩ := hEqT r hr η hη
    exact ⟨δ, hδ, N', fun N hN x y hx hy hxy => hN' (N + N₂) (by omega) x y hx hy hxy⟩
  -- Ascoli
  obtain ⟨φ', hφ', G, hGc, -, hGu⟩ := ascoli_asymp_exists_subseq_annulus (0 : UnitAddTorus (Fin 2))
    0 F (fun r hr => hBdF r hr) (fun r hr => hEqF r hr)
  have hset : {x : UnitAddTorus (Fin 2) | (0 : ℝ) < dist x 0} = {0}ᶜ := by
    ext x; simp
  rw [hset] at hGc hGu
  have hpt : ∀ x : UnitAddTorus (Fin 2), 0 < ‖x‖ →
      Tendsto (fun k => F (φ' k) x) atTop (𝓝 (G x)) := by
    intro x hx
    have hK : ({x} : Set (UnitAddTorus (Fin 2))) ⊆ {0}ᶜ := by
      intro y hy; rw [Set.mem_singleton_iff.1 hy]; exact norm_pos_iff.1 hx
    exact (hGu _ hK isCompact_singleton).tendsto_at (Set.mem_singleton x)
  set φ : ℕ → ℕ := fun k => φ' k + N₂ with hφd
  have hφ : StrictMono φ := fun a b hab => Nat.add_lt_add_right (hφ' hab) _
  have hφN : ∀ k, N₂ ≤ φ k := fun k => Nat.le_add_left _ _
  have hFφ : (fun k => obsFS L βs (φ k)) = fun k => F (φ' k) := by
    funext k
    exact hobsF (φ' k + N₂) (by omega)
  -- the short-distance constants
  have hSB' : ∀ i, i ∈ range 4 → ∃ δ K' : ℝ, 0 < δ ∧ 0 ≤ K' ∧ ∀ P ℓ : ℝ,
      CsPtX M N₁ (obsBR t i) P ℓ → ℓ ≤ δ →
        |P - csA (obsBR t i) ℓ| ≤ K' * csA (obsBR t i) ℓ * csRate ℓ := fun i _ => by
    obtain ⟨-, δ, K', hδ, -, hK', hpt, -⟩ := hSB (obsBR t i) (obsBR_pos ht0 i) (hgi₁ i)
    exact ⟨δ, K', hδ, hK', hpt⟩
  choose! δf Kf hdK using hSB'
  obtain ⟨δ₁, K', hδ₁, hδ₁1, hK', hmm⟩ := ob_minmax_finset (range 4) δf Kf
    (fun i hi => (hdK i hi).1) (fun i hi => (hdK i hi).2.1)
  have hexp : Real.exp (-1) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
  have hexp0 : 0 < Real.exp (-1) := Real.exp_pos _
  refine ⟨min δ₁ (Real.exp (-1)), K', lt_min hδ₁ hexp0, (min_le_right _ _).trans_lt hexp, hK',
    βs, fun N hN => ?_, ?_, φ, hφ, G, hGc, ?_, ?_, ?_, ?_, ?_⟩
  · -- the per-`N` clause
    have hN0 : N₀ ≤ N := le_trans (le_max_left _ _) hN
    obtain ⟨hb0, hΦ, -, β, hS, hSh⟩ := hbN N hN0
    show 0 < 1 / b N ∧ obsBetaSum L N (1 / b N) = t ∧
      (∑ x : Lam 2 L N, Pconn L N (1 / b N) x / obsDens L N (1 / b N)) / (L : ℝ) ^ (2 * N) = 1 ∧
      ∃ β : ℕ → ℝ, ObsScale L N t K Kc Kε E a (1 / b N) β ∧ ArbShort L N t Ks Kc (1 / b N)
    rw [hbeq N hN0]
    exact ⟨one_div_pos.2 hb0, hΦ, obsFS_avg (one_div_pos.2 hb0).le, β, hS, hSh⟩
  · -- equicontinuity of `f_N`
    intro r hr η hη
    obtain ⟨δ, hδ, N', hN'⟩ := hEqT r hr η hη
    refine ⟨δ, hδ, max N' N₀, fun N hN x y hx hy hxy => ?_⟩
    rw [hobsF N (le_trans (le_max_right _ _) hN)]
    exact hN' N (le_trans (le_max_left _ _) hN) x y hx hy hxy
  · -- uniform convergence
    rw [hFφ]; exact hGu
  · -- nonnegativity
    intro x hx
    exact ge_of_tendsto (hpt x (norm_pos_iff.2 hx))
      (Eventually.of_forall fun k => ob_clF_nonneg ht0 (hb_pos _) x)
  · -- symmetry
    intro τ s x hx
    have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hsub : Tendsto (fun N => F N (clSgn τ s x) - F N x) atTop (𝓝 0) :=
      (t6_sym_tendsto_on hL2 (hEqT (‖x‖ / 2) (by positivity)) τ s (by linarith)).comp
        (tendsto_add_atTop_nat N₂)
    exact ascoli_asymp_limit_eq_of_tendsto_sub hφ' (hpt x hx0)
      (hpt _ (by rw [norm_clSgn]; exact hx0)) hsub
  · -- boundedness
    intro δ hδ
    obtain ⟨C, hC⟩ := hBdF δ hδ
    refine ⟨C, fun x hx => ?_⟩
    refine le_of_tendsto (hpt x (lt_of_lt_of_le hδ hx)) (Eventually.of_forall fun k => ?_)
    exact (le_abs_self _).trans (hC _ x (by rwa [dist_zero_right]))
  · -- the short-distance law
    intro x hx hxδ
    have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hptx := hpt x hx0
    set ℓ := torusNorm x with hℓd
    have hℓ0 : 0 < ℓ := t6_torusNorm_pos hx
    set ℓk : ℕ → ℝ := fun k => eucl (latPtN L (φ k) x) / (L : ℝ) ^ (φ k) with hℓkd
    have hℓk : Tendsto ℓk atTop (𝓝 ℓ) := (t6_eucl_tendsto hL2 x).comp hφ.tendsto_atTop
    have hle : ∀ᶠ k in atTop,
        |F (φ' k) x - csA t (ℓk k)| - K' * csA t (ℓk k) * csRate (ℓk k) ≤ 0 := by
      have h1 := hφ.tendsto_atTop.eventually
        (t6_eventually_small hL2 (show 0 < ‖x‖ / 2 by positivity))
      filter_upwards [h1, hℓk.eventually (ge_mem_nhds hxδ)] with k hk1 hk2
      have hφk := hφN k
      obtain ⟨i, hi, hrel_k⟩ := hrel (φ k) (by omega)
      have hi3 : i ≤ 3 := by have := Finset.mem_range.1 hi; omega
      have hFk : F (φ' k) x = c i * clF L (obsBR t i) (bI i) (φ k) x := hrel_k x
      have hne := (t6_latPt_far hL2 (φ k) x hk1.le hx0).1
      have hcs := t6_csPtX (hAdm i hi3) (show N₁ ≤ φ k by omega) hne
      obtain ⟨-, -, hpti⟩ := hdK i hi
      obtain ⟨hδ₁i, hKi'⟩ := hmm i hi
      have hb := hpti _ _ hcs (hk2.trans ((min_le_left _ _).trans hδ₁i))
      have hℓk0 : 0 < ℓk k := by
        have := cs_one_le_eucl hne
        have hL0 : (0 : ℝ) < (L : ℝ) ^ (φ k) := by positivity
        show 0 < eucl (latPtN L (φ k) x) / (L : ℝ) ^ (φ k)
        positivity
      have hℓke : ℓk k ≤ Real.exp (-1) := hk2.trans (min_le_right _ _)
      have hℓk1 : ℓk k ≤ 1 := hℓke.trans hexp.le
      obtain ⟨hA0, hR0⟩ := ob_csA_csRate_nonneg (obsBR_pos ht0 i) hℓk0 hℓke
      have hci : 0 < c i := Real.rpow_pos_of_pos (div_pos (obsBR_pos ht0 i) ht0) _
      have hcsA : csA t (ℓk k) = c i * csA (obsBR t i) (ℓk k) :=
        (ob_csA_rescale ht0 (obsBR_pos ht0 i) hℓk0 hℓk1).symm
      rw [hFk, hcsA, ← mul_sub, abs_mul, abs_of_pos hci]
      have h2 := mul_le_mul_of_nonneg_left hb hci.le
      have h3 : c i * (Kf i * csA (obsBR t i) (ℓk k) * csRate (ℓk k)) ≤
          c i * (K' * csA (obsBR t i) (ℓk k) * csRate (ℓk k)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKi' hA0) hR0) hci.le
      have e : K' * (c i * csA (obsBR t i) (ℓk k)) * csRate (ℓk k) =
          c i * (K' * csA (obsBR t i) (ℓk k) * csRate (ℓk k)) := by ring
      linarith
    have hne : Real.log (1 / ℓ) ≠ 0 := by
      have h1 := Real.log_lt_log hℓ0 (hxδ.trans_le (min_le_right _ _))
      rw [Real.log_exp] at h1
      rw [one_div, Real.log_inv]
      intro h0; linarith
    have h1 : ContinuousAt (fun s : ℝ => 1 / s) ℓ := continuousAt_const.div continuousAt_id hℓ0.ne'
    have hlog : ContinuousAt (fun s : ℝ => Real.log (1 / s)) ℓ := h1.log (one_div_pos.2 hℓ0).ne'
    have hA : ContinuousAt (fun s => csA t s) ℓ :=
      ((continuousAt_const.mul hlog).div_const t).rpow_const (Or.inr (by norm_num))
    have hR : ContinuousAt (fun s => csRate s) ℓ := (hlog.log hne).div hlog hne
    have hB : ContinuousAt (fun s => K' * csA t s * csRate s) ℓ :=
      (continuousAt_const.mul hA).mul hR
    have hT := ((hptx.sub (hA.tendsto.comp hℓk)).abs.sub (hB.tendsto.comp hℓk))
    have := le_of_tendsto hT hle
    linarith

end

end Spin2
