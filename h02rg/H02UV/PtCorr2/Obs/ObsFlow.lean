import Step2.Flow.FlowComplete2X
import PtCorr2.Obs.ObsHist2

/-!
# The observable bounds along the admissible trajectories of the bulk flow

**`thm_obs_flow`**: the constants of the bulk flow theorem (`Step2.thm_flow_complete2X`, whose
conclusion `FlowC2Concl` is that of `thm_flow_complete2`) can be chosen such that, in addition,
along every admissible trajectory the coupled observable recursion `obs_hist` holds
unconditionally (Case (1), the `σ_a` part, weights `Obs2.wA`):
for `j ≤ N_h`, with `r_j = c_R g_j`, `q_j = max(1, s_{j+1}/s_j)`, `M_{j+1} = M_j q_j(1 + C_M r_j)`,

  `s_j ∑_B |m₁(V_j(B)_a)| ≤ M_j`, `‖𝒲^{obs}_j(B)‖ ≤ c_W r_j M_j`,
  `A^{(|𝓑_j(X)|-4)_+}‖K^{obs}_j(X)‖ ≤ kseq(8θ̄) B r (c_W M) j`,  `θ̄ ≤ 1/36`,

for every observable initial state with `V_0(B)_a ∈ ℂψ̄_a`, `𝒲_0 = K_0 = 0` (e.g. `obsInit`),
and every `M_0 ≥ s_0 β^{abs}_0`, `M_0 > 0`.

The constants: `C₀, η` (`kobs_bounds`), `K_w` (`wobs_bounds`), `C_m, c_s, c_n` (`beta_bounds`) are
fixed first; `L ≥ L_o` with `L_o ≥ 144C₀, 6K_w` (so `C₀/L ≤ 1/144`, `K_w/L ≤ 1/6`); the requirement
on `A` (`obsAReq`: `A ≥ A₀(L)` of `kobs_bounds` and `C₀(A/2)^{-η} ≤ 1/144`, so `θ₀ ≤ 1/72`) and
the requirement on `ε` (`obsEReq`: the smallness conditions of `obs_hist` in terms of
`c_R ε`, with the constants `ε₀, C₁` of `KObsBounds` at `(L, A)` and `C₁, ε₁` of `WObsBounds`
at `L`) are passed to the bulk construction.

**The field-scale ratio.** `q_j ≤ 1 + |ζ_j|` (`histS_ratio_le`, from `fscale_mul`), so
`M_j ≤ M_0 exp(∑_{i<j}(|ζ_i| + C_M r_i))` (`Mseq_le_exp`).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2 Filter Topology Step2.D2

/-! ### The requirements on `A` and `ε` -/

/-- `θ₀ = C₀(L^{-1} + (A/2)^{-η}) ≤ 1/72` for `144C₀ ≤ L` and `2(144C₀+1)^{1/η} ≤ A`. -/
theorem kθ0_le {L : ℕ} {A C₀ η : ℝ} (hC₀ : 0 ≤ C₀) (hη : 0 < η) (hL : 144 * C₀ + 1 ≤ L)
    (hA : 2 * (144 * C₀ + 1) ^ η⁻¹ ≤ A) : kθ0 L A C₀ η ≤ 1 / 72 := by
  unfold kθ0
  have hB1 : (1 : ℝ) ≤ 144 * C₀ + 1 := by linarith
  have hB0 : 0 < (144 * C₀ + 1) ^ η⁻¹ := Real.rpow_pos_of_pos (by linarith) _
  have hA2 : (144 * C₀ + 1) ^ η⁻¹ ≤ A / 2 := by linarith
  have hpow : 144 * C₀ + 1 ≤ (A / 2) ^ η := by
    have h := Real.rpow_le_rpow hB0.le hA2 hη.le
    rwa [Real.rpow_inv_rpow (by linarith) hη.ne'] at h
  have hA0 : 0 < A / 2 := lt_of_lt_of_le hB0 hA2
  have e : (A / 2) ^ (-η) = ((A / 2) ^ η)⁻¹ := Real.rpow_neg hA0.le η
  have h1 : (A / 2) ^ (-η) ≤ (144 * C₀ + 1)⁻¹ := by
    rw [e]; exact inv_anti₀ (by linarith) hpow
  have hL0 : (0 : ℝ) < L := by linarith
  have e2 : (L : ℝ) ^ 2 / (L : ℝ) ^ 3 = (L : ℝ)⁻¹ := by
    field_simp
  rw [e2]
  have h2 : (L : ℝ)⁻¹ ≤ (144 * C₀ + 1)⁻¹ := inv_anti₀ (by linarith) hL
  have h3 : C₀ * ((L : ℝ)⁻¹ + (A / 2) ^ (-η)) ≤ C₀ * (2 * (144 * C₀ + 1)⁻¹) := by
    apply mul_le_mul_of_nonneg_left _ hC₀; linarith
  have h4 : C₀ * (2 * (144 * C₀ + 1)⁻¹) ≤ 1 / 72 := by
    rw [show C₀ * (2 * (144 * C₀ + 1)⁻¹) = 2 * C₀ / (144 * C₀ + 1) by ring,
      div_le_iff₀ (by linarith)]
    linarith
  linarith

/-- The requirement on `A` at scale `L`: the constants of `KObsBounds` exist at `(L, A)`, and
`θ₀ ≤ 1/72`. -/
def obsAReq (C₀ η : ℝ) (Lo : ℕ) (L : ℕ) (A : ℝ) : Prop :=
  ∀ [NeZero L], Lo ≤ L →
    (∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧ KObsBounds L A C₀ η ε₀ C₁) ∧ kθ0 L A C₀ η ≤ 1 / 72

/-- The requirement on `ε` (with `c = c_R`, `c' = c_x`): the smallness conditions of `obs_hist`. -/
def obsEReq (C₀ η Kw : ℝ) (Lo : ℕ) (L : ℕ) (A c c' ε : ℝ) : Prop :=
  ∀ [NeZero L], Lo ≤ L → obsAReq C₀ η Lo L A →
    ∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧ KObsBounds L A C₀ η ε₀ C₁ ∧
      C₁ * (2 + 2 * (8 * c') + 64 * kB (kθ0 L A C₀ η) C₁ (8 * c')) * (c * ε) ≤ 1 / 72 ∧
      c * ε ≤ 1 ∧ c * ε ≤ ε₀ ∧ (8 * c' + 64 * kB (kθ0 L A C₀ η) C₁ (8 * c')) * (c * ε) ≤ ε₀ ∧
      ∃ C₁w ε₁ : ℝ, 0 ≤ C₁w ∧ 0 < ε₁ ∧ WObsBounds L Kw C₁w ε₁ ∧ C₁w * (c * ε) ≤ 1 / 6 ∧
        c * ε ≤ ε₁

theorem obsAReq_ev {C₀ η : ℝ} {L₀ Lo : ℕ} (hC₀ : 0 ≤ C₀) (hη : 0 < η)
    (hk : ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
      ∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧ KObsBounds L A C₀ η ε₀ C₁)
    (hLo : L₀ ≤ Lo) (hLo' : 144 * C₀ + 1 ≤ (Lo : ℝ)) (L : ℕ) :
    ∃ A₀ : ℝ, ∀ A, A₀ ≤ A → obsAReq C₀ η Lo L A := by
  by_cases hL : L ≠ 0 ∧ Lo ≤ L
  · haveI : NeZero L := ⟨hL.1⟩
    obtain ⟨A₀, -, hA⟩ := hk L (hLo.trans hL.2)
    refine ⟨max A₀ (2 * (144 * C₀ + 1) ^ η⁻¹), fun A hA' _ _ => ⟨hA A (le_of_max_le_left hA'),
      kθ0_le hC₀ hη (hLo'.trans (by exact_mod_cast hL.2)) (le_of_max_le_right hA')⟩⟩
  · exact ⟨0, fun A _ inst hLL => absurd ⟨inst.out, hLL⟩ hL⟩

theorem obsEReq_ev {C₀ η Kw : ℝ} {L₀ Lo : ℕ}
    (hw : ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ C₁ ε₁ : ℝ, 0 ≤ C₁ ∧ 0 < ε₁ ∧ WObsBounds L Kw C₁ ε₁)
    (hLo : L₀ ≤ Lo) (L : ℕ) (A c c' : ℝ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), obsEReq C₀ η Kw Lo L A c c' ε := by
  by_cases hL : L ≠ 0 ∧ Lo ≤ L
  · haveI : NeZero L := ⟨hL.1⟩
    by_cases hA : obsAReq C₀ η Lo L A
    · obtain ⟨⟨ε₀, C₁, hε₀, hC₁, hKB⟩, -⟩ := hA hL.2
      obtain ⟨C₁w, ε₁, hC₁w, hε₁, hWB⟩ := hw L (hLo.trans hL.2)
      filter_upwards [ev_lin (C₁ * (2 + 2 * (8 * c') + 64 * kB (kθ0 L A C₀ η) C₁ (8 * c')) * c)
          (by norm_num : (0 : ℝ) < 1 / 72), ev_lin c one_pos, ev_lin c hε₀,
        ev_lin ((8 * c' + 64 * kB (kθ0 L A C₀ η) C₁ (8 * c')) * c) hε₀,
        ev_lin (C₁w * c) (by norm_num : (0 : ℝ) < 1 / 6), ev_lin c hε₁]
        with ε h1 h2 h3 h4 h5 h6
      intro _ _ _
      exact ⟨ε₀, C₁, hε₀, hC₁, hKB, by rw [← mul_assoc]; exact h1, h2, h3,
        by rw [← mul_assoc]; exact h4, C₁w, ε₁, hC₁w, hε₁, hWB, by rw [← mul_assoc]; exact h5, h6⟩
    · exact Eventually.of_forall fun _ _ _ hA' => absurd (fun (_ : NeZero L) => hA') hA
  · exact Eventually.of_forall fun _ inst hLL _ => absurd ⟨inst.out, hLL⟩ hL

/-! ### The field-scale ratio -/

theorem fscale_one_add_le' {ζ : ℂ} (h : ‖ζ‖ ≤ 1 / 2) : fscale (1 + ζ) ≤ 1 + ‖ζ‖ := by
  unfold fscale
  have hx := norm_nonneg ζ
  have h1 : 1 - ‖ζ‖ ≤ ‖1 + ζ‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-ζ)
    simp only [norm_one, norm_neg, sub_neg_eq_add] at this
    linarith
  have h0 : 0 < 1 - ‖ζ‖ := by linarith
  have h2 : ‖1 + ζ‖⁻¹ ≤ (1 - ‖ζ‖)⁻¹ := inv_anti₀ h0 h1
  have h3 : (1 - ‖ζ‖)⁻¹ ≤ (1 + ‖ζ‖) ^ 2 := by
    rw [inv_le_iff_one_le_mul₀' h0]
    nlinarith [mul_nonneg hx hx, mul_nonneg (mul_nonneg hx hx) hx]
  rw [Real.sqrt_le_left (by linarith)]
  linarith

variable {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- **The field-scale ratio**: `q_j = max(1, s_{j+1}/s_j) ≤ 1 + |ζ_j|` (`ρ ≤ 1/2`). -/
theorem histS_ratio_le (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 2) (j : ℕ) (t : Flow2.Hist.Seq (Xs R)) :
    max 1 (histS R (j + 1) t / histS R j t) ≤ 1 + ‖zetaH R j t‖ := by
  have hz : ‖zetaH R j t‖ ≤ R.ρ := absorb_le R hρ0 _ _
  refine max_le (by linarith [norm_nonneg (zetaH R j t)]) ?_
  have e : histS R (j + 1) t = histS R j t * fscale (1 + zetaH R j t) := by
    unfold histS
    rw [rawHist_succ_Z, fscale_mul]; ring
  rw [e]
  rcases eq_or_ne (histS R j t) 0 with h0 | h0
  · rw [h0, zero_mul, zero_div]; linarith [norm_nonneg (zetaH R j t)]
  · rw [mul_div_cancel_left₀ _ h0]
    exact fscale_one_add_le' (hz.trans hρ)

/-- **The crude growth of `M_j`**: `M_j ≤ M_0 exp(∑_{i<j}(|ζ_i| + C_M r_i))` if
`1 ≤ q_i ≤ 1 + z_i`, `r_i ≥ 0`. -/
theorem Mseq_le_exp {M0 CM : ℝ} {r q z : ℕ → ℝ} (hM0 : 0 ≤ M0) (hCM : 0 ≤ CM)
    (hr : ∀ i, 0 ≤ r i) (hq1 : ∀ i, 1 ≤ q i) (hq : ∀ i, q i ≤ 1 + z i) :
    ∀ j, Mseq M0 CM r q j ≤ M0 * Real.exp (∑ i ∈ range j, (z i + CM * r i))
  | 0 => by simp [Mseq]
  | j + 1 => by
    have ih := Mseq_le_exp hM0 hCM hr hq1 hq j
    rw [Mseq_succ, sum_range_succ, Real.exp_add]
    have hr' : 0 ≤ CM * r j := mul_nonneg hCM (hr j)
    have h1 : q j * (1 + CM * r j) ≤ Real.exp (z j + CM * r j) := by
      rw [Real.exp_add]
      exact mul_le_mul ((hq j).trans (by linarith [Real.add_one_le_exp (z j)]))
        (by linarith [Real.add_one_le_exp (CM * r j)]) (by linarith) (Real.exp_pos _).le
    have hq0 : 0 ≤ q j * (1 + CM * r j) := mul_nonneg (by linarith [hq1 j]) (by linarith)
    calc Mseq M0 CM r q j * (q j * (1 + CM * r j))
        ≤ M0 * Real.exp (∑ i ∈ range j, (z i + CM * r i)) * Real.exp (z j + CM * r j) :=
          mul_le_mul ih h1 hq0 (mul_nonneg hM0 (Real.exp_pos _).le)
      _ = _ := by ring

/-! ### The observable bounds along the flow -/

set_option maxHeartbeats 4000000 in
/-- **The observable bounds along the admissible trajectories of the bulk flow** (Case (1),
the `σ_a` part, weights `Obs2.wA`). The constants of the bulk flow theorem (`FlowC2Concl`, the
conclusion of `thm_flow_complete2`) are chosen such that the coupled recursion `obs_hist` holds
unconditionally along every admissible trajectory, for every observable initial state with
`V_0(B)_a ∈ ℂψ̄_a`, `𝒲_0 = K_0 = 0`. -/
theorem thm_obs_flow : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ κ cg cm cT ε Ke Cf Cb : ℝ, FlowC2Concl L ℓ A ρ κ cg cm cT ε Ke Cf Cb ∧
    ∃ θb Bk cRc cWc CM : ℝ, θb ≤ 1 / 36 ∧ 1 ≤ cWc ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
    ∀ m ∈ mRange L N, ∀ b μ₀,
      Flow2.Hist.Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
    ∀ (P : ObsPts 2 L N) (o₀ : ObsSt .one L N), o₀.IsObs → ObsLocInv P 0 o₀ → ObsSymInv 0 o₀ →
      (∀ x, (o₀.V x : SA .one (Lam 2 L N)).a ∈ (ℂ ∙ psibar P.a)) → o₀.W = 0 → o₀.K = 0 →
    ∀ M0 : ℝ, 0 < M0 →
      histS (R.withMsq m) 0 (Flow2.Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) *
        ∑ x ∈ blockIdx (L := L) (N := N) 0, ‖mass1L (-1) (o₀.V x : SA .one (Lam 2 L N)).a‖ ≤ M0 →
      let R' := R.withMsq m
      let t := Flow2.Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀
      let r := fun j => cRc * (t j).1
      let q := fun j => max 1 (histS R' (j + 1) t / histS R' j t)
      let M := Mseq M0 CM (fun j => max 0 (r j)) q
      ∀ j ≤ Nh,
        histS R' j t * ∑ x ∈ blockIdx (L := L) (N := N) j,
          ‖mass1L (-1) ((obsHist R' P o₀ j t).V x : SA .one (Lam 2 L N)).a‖ ≤ M j ∧
        (∀ x ∈ blockIdx (L := L) (N := N) j,
          oTo Obs2.wA j (histS R' j t) ((obsHist R' P o₀ j t).W x) ≤
            ENNReal.ofReal (cWc * r j * M j)) ∧
        (∀ X, IsConn j X → ENNReal.ofReal (A ^ (nb j X - 2 ^ 2)) *
          oTo Obs2.wA j (histS R' j t) ((obsHist R' P o₀ j t).K X) ≤
            ENNReal.ofReal (kseq (8 * θb) Bk r (fun i => cWc * M i) j)) := by
  obtain ⟨C₀o, ηo, L₀k, hC₀o, hηo, hk⟩ := kobs_bounds
  obtain ⟨Kw, L₀w, hKw, hw⟩ := wobs_bounds
  obtain ⟨Cm, cs, cn, L₀b, hCm, hb⟩ := beta_bounds
  obtain ⟨Lo, hLod⟩ : ∃ Lo : ℕ, Lo = max (max L₀k L₀w) (max L₀b (⌈144 * C₀o + 6 * Kw⌉₊ + 1)) :=
    ⟨_, rfl⟩
  have hLk : L₀k ≤ Lo := hLod ▸ le_trans (le_max_left _ _) (le_max_left _ _)
  have hLw' : L₀w ≤ Lo := hLod ▸ le_trans (le_max_right _ _) (le_max_left _ _)
  have hLb : L₀b ≤ Lo := hLod ▸ le_trans (le_max_left _ _) (le_max_right _ _)
  have hLc : 144 * C₀o + 6 * Kw + 1 ≤ (Lo : ℝ) := by
    have h1 : ⌈144 * C₀o + 6 * Kw⌉₊ + 1 ≤ Lo := hLod ▸ le_trans (le_max_right _ _) (le_max_right _ _)
    have h2 := Nat.le_ceil (144 * C₀o + 6 * Kw)
    have h3 : ((⌈144 * C₀o + 6 * Kw⌉₊ + 1 : ℕ) : ℝ) ≤ Lo := by exact_mod_cast h1
    push_cast at h3
    linarith
  obtain ⟨L₀, hL₀⟩ := thm_flow_complete2X (obsAReq C₀o ηo Lo)
    (obsAReq_ev hC₀o hηo hk hLk (by linarith)) (obsEReq C₀o ηo Kw Lo) (obsEReq_ev hw hLw')
  refine ⟨max L₀ Lo, fun L _ hL => ?_⟩
  have hLo : Lo ≤ L := le_trans (le_max_right _ _) hL
  have hLr : (Lo : ℝ) ≤ L := by exact_mod_cast hLo
  obtain ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, Cf, Cb, hC, hAx, C₀x, ηx, εsx, CKx, C₂x, CDx, Cqx, Clx,
    cSx, hSBx, hEx, hX⟩ := hL₀ L (le_trans (le_max_left _ _) hL)
  obtain ⟨-, hA0, -, -, -, -, -, -, -, -, -, -, -, -, -, hCN⟩ := id hC
  let R₀ : RGPar 2 L 1 := ⟨Pc, 0, ℓ, A, 0, ρ⟩
  obtain ⟨-, hθ⟩ := hAx hLo
  obtain ⟨ε₀, C₁k, hε₀, hC₁k, hKB, hsm, hε1, hεε, hεk, C₁w, ε₁, hC₁w, hε₁, hWB, hC₁ε, hε₁'⟩ :=
    hEx R₀ rfl hLo hAx
  have hBB := hb L (hLb.trans hLo)
  have hθ0 : 0 ≤ kθ0 L A C₀o ηo := by
    unfold kθ0
    exact mul_nonneg hC₀o (add_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _))
  have hLwk : Kw / L ≤ 1 / 6 := by
    have hL0 : (0 : ℝ) < L := by linarith
    rw [div_le_iff₀ hL0]; linarith
  refine ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, Cf, Cb, hC, kθ0 L A C₀o ηo + C₁k * (2 + 2 * (8 * cx κ cT) +
      64 * kB (kθ0 L A C₀o ηo) C₁k (8 * cx κ cT)) * (cR R₀ ((L : ℝ) ^ 2) cm C₂x * ε),
    kB (kθ0 L A C₀o ηo) C₁k (8 * cx κ cT), cR R₀ ((L : ℝ) ^ 2) cm C₂x, 2 * C₁w + 1,
    cs * Cm * (64 * kB (kθ0 L A C₀o ηo) C₁k (8 * cx κ cT)) * (2 * C₁w + 1) +
      Cm * (2 * Step2.cNear 2 L * Step2.Q1 2 ^ 2 + cn * Step2.Q1 2 * (2 * C₁w + 1)),
    by linarith, by linarith,
    fun N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm P o₀ h0 hl0 hs0 hf0 hW0 hK0 M0 hM0
      hM0' => ?_⟩
  intro R' t r q M j hj
  obtain ⟨H, hm1, F1⟩ := hX N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm
  have hV : ∀ j < Nh, ValidAt R' j :=
    ((hCN N R hP hi0 hRℓ hRA hRρ hN Nh hNh).2.2.2.2.2.2.2.2.2 m hm).1
  have ht := admissible_InDh_rg R' F1 hadm Nh le_rfl
  have hRA' : R'.A = A := hRA
  have hcR : cR R' ((L : ℝ) ^ 2) cm C₂x = cR R₀ ((L : ℝ) ^ 2) cm C₂x :=
    cR_congr (show R.ℓ = ℓ from hRℓ) _ _ _
  have hβ : (0 : ℝ) ≤ betaL L := by
    unfold betaL
    have : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
    positivity
  have hW0' : ∀ x, oTo Obs2.wA 0 (histS R' 0 t) (o₀.W x) = 0 := fun x => by
    have : o₀.W x = 0 := by rw [hW0]; rfl
    rw [this]; exact oTo_zero' _ _ _
  have hK0' : ∀ X, oTo Obs2.wA 0 (histS R' 0 t) (o₀.K X) = 0 := fun X => by
    have : o₀.K X = 0 := by rw [hK0]; rfl
    rw [this]; exact oTo_zero' _ _ _
  have key := obs_hist R' (by rw [hRA']; exact hKB) hC₁k hWB hC₁w hBB hCm
    (by rw [hRA']; exact hSBx) hV hm1 hβ (by norm_num : (1 / 2 : ℝ) ≤ 1) H P o₀ h0 hl0 hs0 hf0 t
    hW0' hK0' Nh le_rfl ht (by rw [hRA']; exact hθ0) (by rw [hRA']; exact hθ)
    (by rw [hRA', hcR]; exact hsm) (by rw [hcR]; exact hε1) (by rw [hcR]; exact hεε)
    (by rw [hRA', hcR]; exact hεk) hLwk (by rw [hcR]; exact hC₁ε) (by rw [hcR]; exact hε₁')
    M0 hM0 hM0'
  simp only [hRA', hcR] at key
  exact key j hj

end

end PtCorr2
