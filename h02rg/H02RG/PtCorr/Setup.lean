import Obs.FlowObs
import Flow.Main
import PtCorr.Conv

/-!
# A common flow for Sections `sec:obs` and `sec:proofs`

The results of `PtCorr` (`prop_1pt`, `lem_2pt_two`, `lamOne_bound`, `lem_2pt_one`) are proved
for an arbitrary initial coupling `V₀^c` satisfying the predicate `FlowData d L A ℓ₀ V₀c λ̄ C κ`
(the `_of` forms), so that they can be combined for **one** choice of `V₀^c`.  `FlowData`
packages everything that is known about such a choice:

* the bulk flow bounds `‖V_j‖_j ≤ C|b₀|L^{-κj}`, `‖K_j‖_j ≤ C|b₀|²L^{-κj}` (`j ≤ N`, from
  `Flow.thm_flow_real`, `cor:flow-finvol`);
* the observable flow bounds for all cases (`Obs.flowObs`), for `‖b₀‖ ≤ ‖l₀‖ ≤ λ̄`, `b ≠ ctr`;
* `GoodCov` of all covariances (`Obs.covAt_goodCov`), `2^{d+3} ≤ L`, `1 ≤ A`, `V₀^c.b = b₀`;
* the regularity of `V₀^c`: `|z₀|, |y₀|, |a₀| ≤ C|b₀|`, continuity in `m² ≥ 0` for fixed `b₀`,
  and holomorphy in `b₀ ∈ B(0, λ̄)` with derivatives bounded by `C` for fixed `m² ≥ 0`
  (separate, not joint, regularity: this is what the bulk flow theorem provides).

`FlowDataW` extends `FlowData` by
* the reality `V₀^c(m², b̄₀) = conj V₀^c(m², b₀)` (`conj`),
* the torus independence of `V_j` (`j + 2 ≤ N`) and of `u_{j+1}` (`j + 3 ≤ N`) and the bound
  on `∑_j u_{j+1}` (`indepV`, `indepU`, `usum`).

`setupW` produces a `V₀^c` with `FlowDataW`; `setup` is its `FlowData` part.
-/

namespace PtCorr

noncomputable section

open Finset Grassmann Loc Step Obs FRD

/-- Everything known about one choice of initial coupling `V₀c` (see the module docstring). -/
structure FlowData (d L : ℕ) [NeZero L] (A ℓ₀ : ℝ) (V₀c : ℝ → ℂ → Vcoup) (lbar C κ : ℝ) :
    Prop where
  lbar_pos : 0 < lbar
  C_nonneg : 0 ≤ C
  κ_pos : 0 < κ
  hℓ₀ : 0 < ℓ₀
  hL8 : 2 ^ (d + 3) ≤ L
  hA1 : 1 ≤ A
  hb : ∀ msq b₀, (V₀c msq b₀).b = b₀
  good : ∀ (N : ℕ) (msq : ℝ), 0 ≤ msq → ∀ k < N,
    GoodCov (d := d) (L := L) (N := N) k ℓ₀ (Flow.covAt d L N msq k)
  bulk : ∀ (N : ℕ) (msq : ℝ) (b₀ : ℂ), 0 ≤ msq → ‖b₀‖ ≤ lbar → ∀ j ≤ N,
    (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j)
        (Flow.flowN d L N msq (V₀c msq b₀) j).1).toReal ≤
      C * ‖b₀‖ * (L : ℝ) ^ (-(κ * j)) ∧
    (Knorm j (ellj d L ℓ₀ j) A (Flow.flowN d L N msq (V₀c msq b₀) j).2).toReal ≤
      C * ‖b₀‖ ^ 2 * (L : ℝ) ^ (-(κ * j))
  obs : ∀ (c : Case) (N : ℕ) (msq : ℝ) (l₀ b₀ : ℂ) (b : Lam d L N), 0 ≤ msq →
    ‖b₀‖ ≤ ‖l₀‖ → ‖l₀‖ ≤ lbar → b ≠ ctr d L N → ∀ j ≤ N,
      VnormObs c ℓ₀ (ctr d L N) b j
          (flowO d L c N msq (V₀c msq b₀) (initObs c l₀) (ctr d L N) b j).1 ≤
        ENNReal.ofReal (C * ‖l₀‖) ∧
      KnormObs c ℓ₀ (ctr d L N) b j A
          (flowO d L c N msq (V₀c msq b₀) (initObs c l₀) (ctr d L N) b j).2 ≤
        ENNReal.ofReal (C * ‖l₀‖ * ‖b₀‖ * (L : ℝ) ^ (-(κ * j)))
  coup_le : ∀ msq : ℝ, 0 ≤ msq → ∀ b₀ : ℂ, ‖b₀‖ ≤ lbar →
    ‖(V₀c msq b₀).z‖ ≤ C * ‖b₀‖ ∧ ‖(V₀c msq b₀).y‖ ≤ C * ‖b₀‖ ∧ ‖(V₀c msq b₀).a‖ ≤ C * ‖b₀‖
  cont : ∀ b₀ : ℂ, ‖b₀‖ ≤ lbar → ContinuousOn (fun msq => (V₀c msq b₀).z) (Set.Ici 0) ∧
    ContinuousOn (fun msq => (V₀c msq b₀).y) (Set.Ici 0) ∧
    ContinuousOn (fun msq => (V₀c msq b₀).a) (Set.Ici 0)
  holo : ∀ msq : ℝ, 0 ≤ msq →
    DifferentiableOn ℂ (fun b₀ => (V₀c msq b₀).z) (Metric.ball 0 lbar) ∧
    DifferentiableOn ℂ (fun b₀ => (V₀c msq b₀).y) (Metric.ball 0 lbar) ∧
    DifferentiableOn ℂ (fun b₀ => (V₀c msq b₀).a) (Metric.ball 0 lbar) ∧
    ∀ b₀ ∈ Metric.ball (0 : ℂ) lbar, ‖deriv (fun b => (V₀c msq b).z) b₀‖ ≤ C ∧
      ‖deriv (fun b => (V₀c msq b).y) b₀‖ ≤ C ∧ ‖deriv (fun b => (V₀c msq b).a) b₀‖ ≤ C

/-- `FlowData` plus reality and the torus-independence clauses of `thm_flow`. -/
structure FlowDataW (d L : ℕ) [NeZero L] (A ℓ₀ : ℝ) (V₀c : ℝ → ℂ → Vcoup) (lbar C κ : ℝ) : Prop
    extends FlowData d L A ℓ₀ V₀c lbar C κ where
  conj : ∀ msq b₀, V₀c msq (starRingEnd ℂ b₀) = (V₀c msq b₀).conj
  indepV : ∀ msq : ℝ, 0 ≤ msq → ∀ b₀ : ℂ, ‖b₀‖ ≤ lbar → ∀ N M j : ℕ, j + 2 ≤ N → N ≤ M →
    (Flow.flowN d L N msq (V₀c msq b₀) j).1 = (Flow.flowN d L M msq (V₀c msq b₀) j).1
  indepU : ∀ msq : ℝ, 0 ≤ msq → ∀ b₀ : ℂ, ‖b₀‖ ≤ lbar → ∀ N M j : ℕ, j + 3 ≤ N → N ≤ M →
    Flow.uflow d L N msq (V₀c msq b₀) j = Flow.uflow d L M msq (V₀c msq b₀) j
  usum : ∀ msq : ℝ, 0 ≤ msq → ∀ b₀ : ℂ, ‖b₀‖ ≤ lbar → ∀ N : ℕ,
    ‖∑ j ∈ range N, Flow.uflow d L N msq (V₀c msq b₀) j‖ ≤ C * ‖b₀‖

variable {d : ℕ}

/-- **The common flow with reality**: `Flow.thm_flow_real`, `Obs.flowObs` and
`Obs.covAt_goodCov` with one quantifier prefix and common constants (`κ = min(κ_bulk, κ_obs)`,
`C = max(…)`, `λ̄ = min(λ̄_obs, b̄_bulk)`), keeping the regularity, the reality and the torus
independence of `V₀^c`. -/
theorem setupW (hd : 3 ≤ d) : ∃ (L₀ : ℕ) (Kℓ : ℝ), 0 ≤ Kℓ ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → Odd L →
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∀ ℓ₀ : ℝ, 0 < ℓ₀ →
    Kℓ * (L : ℝ) ^ ((d : ℝ) - 2 + 2 * pPhi d) ≤ ℓ₀ ^ 2 →
    ∃ (V₀c : ℝ → ℂ → Vcoup) (lbar C κ : ℝ), FlowDataW d L A ℓ₀ V₀c lbar C κ := by
  obtain ⟨L₁, K₁, hK₁, hF⟩ := Flow.thm_flow_real hd
  obtain ⟨L₂, K₂, hK₂, hO⟩ := flowObs hd
  obtain ⟨Kg, hKg, hgood⟩ := covAt_goodCov hd
  refine ⟨max (max L₁ L₂) (2 ^ (d + 3)), max (max K₁ K₂) Kg,
    le_trans hK₁ (le_trans (le_max_left _ _) (le_max_left _ _)), ?_⟩
  intro L _ hL hLodd
  have hL1 : L₁ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hL2 : L₂ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hL8 : 2 ^ (d + 3) ≤ L := le_trans (le_max_right _ _) hL
  obtain ⟨A₁, hA₁, hF'⟩ := hF L hL1
  obtain ⟨A₂, hA₂, hO'⟩ := hO L hL2 hLodd
  refine ⟨max A₁ A₂, le_trans hA₁ (le_max_left _ _), ?_⟩
  intro A hA ℓ₀ hℓ₀ hKℓ
  have hpos : (0 : ℝ) ≤ (L : ℝ) ^ ((d : ℝ) - 2 + 2 * pPhi d) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hKℓ1 : K₁ * (L : ℝ) ^ ((d : ℝ) - 2 + 2 * pPhi d) ≤ ℓ₀ ^ 2 :=
    (mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_left _ _)) hpos).trans hKℓ
  have hKℓ2 : K₂ * (L : ℝ) ^ ((d : ℝ) - 2 + 2 * pPhi d) ≤ ℓ₀ ^ 2 :=
    (mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) (le_max_left _ _)) hpos).trans hKℓ
  have hKℓg : Kg * (L : ℝ) ^ ((d : ℝ) - 2 + 2 * pPhi d) ≤ ℓ₀ ^ 2 :=
    (mul_le_mul_of_nonneg_right (le_max_right _ _) hpos).trans hKℓ
  obtain ⟨bbar, C, κ, V₀c, hbbar, hC, hκ, hb, -, h2, h3, h4, h5, h6, h7, h8, hconj⟩ :=
    hF' A (le_trans (le_max_left _ _) hA) ℓ₀ hℓ₀ hKℓ1
  obtain ⟨lbar, Cf, κ', hlbar, hCf, hκ', hmain⟩ :=
    hO' A (le_trans (le_max_right _ _) hA) ℓ₀ hℓ₀ hKℓ2 κ (C * (1 + bbar)) hκ (by positivity)
  have hLr1 : (1 : ℝ) ≤ L := by exact_mod_cast (le_trans (Nat.one_le_two_pow) hL8)
  have hA1 : 1 ≤ A := le_trans hA₁ (le_trans (le_max_left _ _) hA)
  have hCC : C ≤ max C Cf := le_max_left _ _
  have hball : Metric.ball (0 : ℂ) (min lbar bbar) ⊆ Metric.ball 0 bbar :=
    Metric.ball_subset_ball (min_le_right _ _)
  refine ⟨V₀c, min lbar bbar, max C Cf, min κ κ',
    { conj := hconj
      indepV := fun msq hm b₀ hb₀ => h2 msq hm b₀ (hb₀.trans (min_le_right _ _))
      indepU := fun msq hm b₀ hb₀ => h7 msq hm b₀ (hb₀.trans (min_le_right _ _))
      usum := fun msq hm b₀ hb₀ N => (h8 msq hm b₀ (hb₀.trans (min_le_right _ _)) N).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
      lbar_pos := lt_min hlbar hbbar
      C_nonneg := le_trans hC (le_max_left _ _)
      κ_pos := lt_min hκ hκ'
      hℓ₀ := hℓ₀
      hL8 := hL8
      hA1 := hA1
      hb := hb
      good := ?_
      bulk := ?_
      obs := ?_
      coup_le := ?_
      cont := ?_
      holo := ?_ }⟩
  · intro N msq hmsq k hk
    exact hgood L (le_trans Nat.one_le_two_pow hL8) ℓ₀ hℓ₀ hKℓg N msq hmsq k hk
  · intro N msq b₀ hmsq hb₀ j hj
    obtain ⟨hV, hK⟩ := h6 msq hmsq b₀ (hb₀.trans (min_le_right _ _)) N j hj
    have hm := rpow_neg_mul_mono_one hLr1 (min_le_left κ κ') j
    have hθ : 0 ≤ (L : ℝ) ^ (-(κ * j)) := by positivity
    refine ⟨hV.trans ?_, hK.trans ?_⟩
    · calc C * ‖b₀‖ * (L : ℝ) ^ (-(κ * j)) ≤ max C Cf * ‖b₀‖ * (L : ℝ) ^ (-(κ * j)) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)) hθ
        _ ≤ _ := mul_le_mul_of_nonneg_left hm (by positivity)
    · calc C * ‖b₀‖ ^ 2 * (L : ℝ) ^ (-(κ * j)) ≤ max C Cf * ‖b₀‖ ^ 2 * (L : ℝ) ^ (-(κ * j)) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) hθ
        _ ≤ _ := mul_le_mul_of_nonneg_left hm (by positivity)
  · intro c N msq l₀ b₀ b hmsq hbl hll hne j hj
    have hb₀ : ‖b₀‖ ≤ bbar := hbl.trans (hll.trans (min_le_right _ _))
    have H := hmain c N msq (V₀c msq b₀) l₀ b₀ b hmsq ?_ hbl (hll.trans (min_le_left _ _)) hne j hj
    · obtain ⟨H1, H2⟩ := H
      have hm := rpow_neg_mul_mono_one hLr1 (min_le_right κ κ') j
      have hθ : 0 ≤ (L : ℝ) ^ (-(κ' * j)) := by positivity
      refine ⟨H1.trans (ENNReal.ofReal_le_ofReal ?_), H2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
      · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
      · calc Cf * ‖l₀‖ * ‖b₀‖ * (L : ℝ) ^ (-(κ' * j))
            ≤ max C Cf * ‖l₀‖ * ‖b₀‖ * (L : ℝ) ^ (-(κ' * j)) := by
              gcongr; exact le_max_right _ _
          _ ≤ _ := mul_le_mul_of_nonneg_left hm (by positivity)
    · intro k hk
      have hL0 : (0 : ℝ) < L := by linarith
      have hℓ := ellj_pos (d := d) hL0 hℓ₀ k
      obtain ⟨hV, hK⟩ := h6 msq hmsq b₀ hb₀ N k hk
      have hθ : 0 ≤ (L : ℝ) ^ (-(κ * k)) := by positivity
      have hV' := (ENNReal.le_ofReal_iff_toReal_le (Vnorm_ne_top hℓ _) (by positivity)).2 hV
      have hK' := (ENNReal.le_ofReal_iff_toReal_le (Knorm_ne_top hℓ _) (by positivity)).2 hK
      refine (add_le_add hV' hK').trans ?_
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have : ‖b₀‖ ^ 2 ≤ bbar * ‖b₀‖ := by
        rw [sq]; exact mul_le_mul_of_nonneg_right hb₀ (norm_nonneg _)
      have h0 : 0 ≤ C * (L : ℝ) ^ (-(κ * k)) := by positivity
      nlinarith
  · intro msq hmsq b₀ hb₀
    obtain ⟨e1, e2, e3⟩ := h3 msq hmsq b₀ (hb₀.trans (min_le_right _ _))
    have hn := norm_nonneg b₀
    exact ⟨e1.trans (mul_le_mul_of_nonneg_right hCC hn),
      e2.trans (mul_le_mul_of_nonneg_right hCC hn), e3.trans (mul_le_mul_of_nonneg_right hCC hn)⟩
  · intro b₀ hb₀
    exact h4 b₀ (hb₀.trans (min_le_right _ _))
  · intro msq hmsq
    obtain ⟨e1, e2, e3, e4⟩ := h5 msq hmsq
    refine ⟨e1.mono hball, e2.mono hball, e3.mono hball, fun b₀ hb₀ => ?_⟩
    obtain ⟨f1, f2, f3⟩ := e4 b₀ (hball hb₀)
    exact ⟨f1.trans hCC, f2.trans hCC, f3.trans hCC⟩

/-- **The common flow**: the `FlowData` part of `setupW`. -/
theorem setup (hd : 3 ≤ d) : ∃ (L₀ : ℕ) (Kℓ : ℝ), 0 ≤ Kℓ ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → Odd L →
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∀ ℓ₀ : ℝ, 0 < ℓ₀ →
    Kℓ * (L : ℝ) ^ ((d : ℝ) - 2 + 2 * pPhi d) ≤ ℓ₀ ^ 2 →
    ∃ (V₀c : ℝ → ℂ → Vcoup) (lbar C κ : ℝ), FlowData d L A ℓ₀ V₀c lbar C κ := by
  obtain ⟨L₀, Kℓ, hKℓ, H⟩ := setupW hd
  refine ⟨L₀, Kℓ, hKℓ, fun L _ hL hLodd => ?_⟩
  obtain ⟨A₀, hA₀, H⟩ := H L hL hLodd
  refine ⟨A₀, hA₀, fun A hA ℓ₀ hℓ₀ hKℓ' => ?_⟩
  obtain ⟨V₀c, lbar, C, κ, HW⟩ := H A hA ℓ₀ hℓ₀ hKℓ'
  exact ⟨V₀c, lbar, C, κ, HW.toFlowData⟩

namespace FlowData

variable {L : ℕ} [NeZero L] {A ℓ₀ lbar C κ : ℝ} {V₀c : ℝ → ℂ → Vcoup}

theorem hL2 (H : FlowData d L A ℓ₀ V₀c lbar C κ) : 2 ≤ L := by
  have : 2 ^ 1 ≤ 2 ^ (d + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have := H.hL8; omega

/-- The Case-(2) observable bounds at `l₀ = λ̄`, with `θ = L^{-κ}`, together with `GoodCov`:
the form used by `prop_1pt_of` and `lem_2pt_two_of`. -/
theorem two (H : FlowData d L A ℓ₀ V₀c lbar C κ) :
    ∀ (N : ℕ) (msq : ℝ) (b₀ : ℂ) (b : Lam d L N), 0 ≤ msq → ‖b₀‖ ≤ lbar → b ≠ ctr d L N →
      (∀ k < N, GoodCov k ℓ₀ (Flow.covAt d L N msq k)) ∧
      ∀ k ≤ N, KnormObs .two ℓ₀ (ctr d L N) b k A
        (flowO d L .two N msq (V₀c msq b₀) (initObs .two (lbar : ℂ)) (ctr d L N) b k).2 ≤
        ENNReal.ofReal (C * lbar * ‖b₀‖ * ((L : ℝ) ^ (-κ)) ^ k) := by
  intro N msq b₀ b hmsq hb₀ hne
  have hnl : ‖(lbar : ℂ)‖ = lbar := by
    rw [Complex.norm_real, Real.norm_of_nonneg H.lbar_pos.le]
  refine ⟨H.good N msq hmsq, ?_⟩
  intro k hk
  have := (H.obs .two N msq (lbar : ℂ) b₀ b hmsq (by rw [hnl]; exact hb₀) (le_of_eq hnl) hne
    k hk).2
  rw [hnl, rpow_neg_mul_nat (Nat.cast_nonneg _)] at this
  exact this

end FlowData

end

end PtCorr
