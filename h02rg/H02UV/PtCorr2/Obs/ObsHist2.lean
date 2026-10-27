import PtCorr2.Obs.ObsHist

/-!
# The coupled observable recursion along the history: the joint induction

**`obs_hist`** (Case (1), weights `Obs2.wA`): along a regular history, with `r_j = c_R g_j`,
`s_j = histS`, `q_j = max(1, s_{j+1}/s_j)`, `c_W = 2C₁ + 1`,
`C_M = c_s C_m 64B c_W + C_m(2c_{near}Q₁² + c_n Q₁ c_W)` and `M_{j+1} = M_j q_j(1 + C_M r_j)`
(`Mseq`): for `j ≤ n`,

  `s_j ∑_B |m₁(V_j(B)_a)| ≤ M_j`, `‖𝒲^{obs}_j(B)‖ ≤ c_W r_j M_j`,
  `A^{(|𝓑_j(X)|-4)_+}‖K^{obs}_j(X)‖ ≤ kseq(8θ̄) B r (c_W M) j`,

under the smallness conditions of `kobs_hist` and `K_w/L ≤ 1/6`, `C₁ c_R ε ≤ 1/6`,
`c_R ε ≤ ε₁`, and `𝒲^{obs}_0 = K^{obs}_0 = 0`, `s_0 β^{abs}_0 ≤ M_0`. In particular the observable
sizes `m_j = c_W M_j` of `kobs_hist` are discharged (`m_j ≤ m_{j+1}`).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

variable {L N : ℕ} [NeZero L]

/-- The comparison sequence `M_{j+1} = M_j q_j (1 + C_M r_j)`. -/
noncomputable def Mseq (M0 CM : ℝ) (r q : ℕ → ℝ) : ℕ → ℝ
  | 0 => M0
  | j + 1 => Mseq M0 CM r q j * (q j * (1 + CM * r j))

theorem Mseq_succ (M0 CM : ℝ) (r q : ℕ → ℝ) (j : ℕ) :
    Mseq M0 CM r q (j + 1) = Mseq M0 CM r q j * (q j * (1 + CM * r j)) := rfl

/-- The real inequality of the `β` step. -/
theorem beta_real {S β s s' k M q r cs Cm Bk cWc cN Q cn : ℝ} (hs : 0 < s) (hs' : 0 < s')
    (hβ : 0 ≤ β) (hM : 0 ≤ M) (hr : 0 ≤ r) (hr1 : r ≤ 1) (hcs : 0 ≤ cs) (hCm : 0 ≤ Cm)
    (hBk : 0 ≤ Bk) (hcW : 0 ≤ cWc) (hcN : 0 ≤ cN) (hQ : 0 ≤ Q) (hcn : 0 ≤ cn) (hk : 0 ≤ k)
    (hS : S ≤ β + cs * Cm * s⁻¹ * (8 * k) +
      Cm * s'⁻¹ * (2 * cN * Q ^ 2 * r * s * β + cn * Q * (cWc * r * M)))
    (hsβ : s * β ≤ M) (hq : s' / s ≤ q) (hq1 : 1 ≤ q) (hk8 : 8 * k ≤ 64 * Bk * r ^ 2 * (cWc * M)) :
    s' * S ≤ M * (q * (1 + (cs * Cm * (64 * Bk) * cWc + Cm * (2 * cN * Q ^ 2 + cn * Q * cWc)) * r)) := by
  have e' : s' * s'⁻¹ = 1 := mul_inv_cancel₀ hs'.ne'
  have e : s * s⁻¹ = 1 := mul_inv_cancel₀ hs.ne'
  have h1 : s' * S ≤ s' / s * (s * β) + s' / s * (cs * Cm * (8 * k)) +
      Cm * (2 * cN * Q ^ 2 * r * (s * β) + cn * Q * (cWc * r * M)) := by
    have := mul_le_mul_of_nonneg_left hS hs'.le
    have e2 : s' * (β + cs * Cm * s⁻¹ * (8 * k) +
        Cm * s'⁻¹ * (2 * cN * Q ^ 2 * r * s * β + cn * Q * (cWc * r * M))) =
        s' / s * (s * β) + s' / s * (cs * Cm * (8 * k)) +
          Cm * (2 * cN * Q ^ 2 * r * (s * β) + cn * Q * (cWc * r * M)) := by
      rw [div_eq_mul_inv]
      linear_combination (-(s' * β)) * e +
        (Cm * (2 * cN * Q ^ 2 * r * s * β + cn * Q * (cWc * r * M))) * e'
    linarith
  have hsq : 0 ≤ s' / s := div_nonneg hs'.le hs.le
  have hq0 : 0 ≤ q := by linarith
  have h2 : s' / s * (s * β) ≤ q * M :=
    mul_le_mul hq hsβ (mul_nonneg hs.le hβ) hq0
  have hk' : cs * Cm * (8 * k) ≤ cs * Cm * (64 * Bk) * cWc * r * M := by
    have h3 : 64 * Bk * r ^ 2 * (cWc * M) ≤ 64 * Bk * r * (cWc * M) := by
      have : r ^ 2 ≤ r := by nlinarith
      have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 64 * Bk)
      nlinarith [mul_nonneg hcW hM]
    have h4 := mul_le_mul_of_nonneg_left (hk8.trans h3) (mul_nonneg hcs hCm)
    linarith [h4]
  have h5 : s' / s * (cs * Cm * (8 * k)) ≤ q * (cs * Cm * (64 * Bk) * cWc * r * M) :=
    mul_le_mul hq hk' (by positivity) hq0
  have h6 : Cm * (2 * cN * Q ^ 2 * r * (s * β) + cn * Q * (cWc * r * M)) ≤
      Cm * (2 * cN * Q ^ 2 + cn * Q * cWc) * r * M := by
    have : 2 * cN * Q ^ 2 * r * (s * β) ≤ 2 * cN * Q ^ 2 * r * M :=
      mul_le_mul_of_nonneg_left hsβ (by positivity)
    have := mul_le_mul_of_nonneg_left this hCm
    nlinarith
  have h7 : Cm * (2 * cN * Q ^ 2 + cn * Q * cWc) * r * M ≤
      q * (Cm * (2 * cN * Q ^ 2 + cn * Q * cWc) * r * M) := by
    have : 0 ≤ Cm * (2 * cN * Q ^ 2 + cn * Q * cWc) * r * M := by positivity
    nlinarith
  have e8 : M * (q * (1 + (cs * Cm * (64 * Bk) * cWc + Cm * (2 * cN * Q ^ 2 + cn * Q * cWc)) * r)) =
      q * M + q * (cs * Cm * (64 * Bk) * cWc * r * M) +
        q * (Cm * (2 * cN * Q ^ 2 + cn * Q * cWc) * r * M) := by ring
  linarith

/-- The real inequality of the `𝒲` step. -/
theorem wobs_real {W a r r' M M' C₁ cWc : ℝ} (hW : W ≤ (a + C₁ * r) * (cWc * r * M) + C₁ * r * M)
    (ha : a ≤ 1 / 6) (hCr : C₁ * r ≤ 1 / 6) (hcW : cWc = 2 * C₁ + 1) (hC₁ : 0 ≤ C₁) (hr : 0 ≤ r)
    (hM : 0 ≤ M) (hr' : 5 / 6 * r ≤ r') (hM' : M ≤ M') :
    W ≤ cWc * r' * M' := by
  have hc0 : 0 ≤ cWc := by rw [hcW]; linarith
  have hrM : 0 ≤ r * M := mul_nonneg hr hM
  have h1 : (a + C₁ * r) * (cWc * r * M) ≤ 1 / 3 * (cWc * (r * M)) := by
    have : a + C₁ * r ≤ 1 / 3 := by linarith
    have h2 : 0 ≤ cWc * r * M := by positivity
    nlinarith
  have h3 : cWc * r' * M' ≥ cWc * (5 / 6 * r) * M := by
    have hr'0 : 0 ≤ r' := by linarith
    have : (5 / 6 * r) * M ≤ r' * M' := mul_le_mul hr' hM' hM hr'0
    nlinarith
  have h4 : C₁ * r * M = C₁ * (r * M) := by ring
  have h5 : C₁ * (r * M) ≤ 1 / 2 * (cWc * (r * M)) := by rw [hcW]; linarith
  have e : cWc * (5 / 6 * r) * M = 5 / 6 * (cWc * (r * M)) := by ring
  linarith

section Hist

variable {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

set_option maxHeartbeats 4000000 in
/-- **The coupled observable recursion along the history** (Case (1), `σ_a`, weights `Obs2.wA`). -/
theorem obs_hist {C₀ η ε₀ C₁k : ℝ} (hKB : KObsBounds L R.A C₀ η ε₀ C₁k) (hC₁k : 0 ≤ C₁k)
    {Kw C₁ ε₁ : ℝ} (hWB : WObsBounds L Kw C₁ ε₁) (hC₁ : 0 ≤ C₁)
    {Cm : ℝ} {cs cn : ℕ} (hBB : BetaBounds L Cm cs cn) (hCm : 0 ≤ Cm)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    (P : ObsPts 2 L N) (o₀ : ObsSt .one L N) (h0 : o₀.IsObs) (hl0 : ObsLocInv P 0 o₀)
    (hs0 : ObsSymInv 0 o₀) (hf0 : ∀ b, (o₀.V b : SA .one (Lam 2 L N)).a ∈ (ℂ ∙ psibar P.a))
    (t : Flow2.Hist.Seq (Xs R)) (hW0 : ∀ b, oTo Obs2.wA 0 (histS R 0 t) (o₀.W b) = 0)
    (hK0 : ∀ X, oTo Obs2.wA 0 (histS R 0 t) (o₀.K X) = 0)
    (n : ℕ) (hn : n ≤ Nh) (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε n t)
    (hθ0 : 0 ≤ kθ0 L R.A C₀ η) (hθ : kθ0 L R.A C₀ η ≤ 1 / 72)
    (hsm : C₁k * (2 + 2 * (8 * cx κ cT) + 64 * kB (kθ0 L R.A C₀ η) C₁k (8 * cx κ cT)) *
      (cR R Λ cm C₂ * ε) ≤ 1 / 72)
    (hε1 : cR R Λ cm C₂ * ε ≤ 1) (hεε : cR R Λ cm C₂ * ε ≤ ε₀)
    (hεk : (8 * cx κ cT + 64 * kB (kθ0 L R.A C₀ η) C₁k (8 * cx κ cT)) * (cR R Λ cm C₂ * ε) ≤ ε₀)
    (hLw : Kw / L ≤ 1 / 6) (hC₁ε : C₁ * (cR R Λ cm C₂ * ε) ≤ 1 / 6)
    (hε₁ : cR R Λ cm C₂ * ε ≤ ε₁)
    (M0 : ℝ) (hM0 : 0 < M0)
    (hM0' : histS R 0 t * ∑ b ∈ blockIdx (L := L) (N := N) 0,
      ‖mass1L (-1) (o₀.V b : SA .one (Lam 2 L N)).a‖ ≤ M0) :
    let B := kB (kθ0 L R.A C₀ η) C₁k (8 * cx κ cT)
    let θb := kθ0 L R.A C₀ η + C₁k * (2 + 2 * (8 * cx κ cT) + 64 * B) * (cR R Λ cm C₂ * ε)
    let r := fun j => cR R Λ cm C₂ * (t j).1
    let q := fun j => max 1 (histS R (j + 1) t / histS R j t)
    let cWc := 2 * C₁ + 1
    let CM := cs * Cm * (64 * B) * cWc + Cm * (2 * Step2.cNear 2 L * Step2.Q1 2 ^ 2 +
      cn * Step2.Q1 2 * cWc)
    let M := Mseq M0 CM (fun j => max 0 (r j)) q
    ∀ j ≤ n,
      histS R j t * ∑ b ∈ blockIdx (L := L) (N := N) j,
        ‖mass1L (-1) ((obsHist R P o₀ j t).V b : SA .one (Lam 2 L N)).a‖ ≤ M j ∧
      (∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo Obs2.wA j (histS R j t) ((obsHist R P o₀ j t).W b) ≤ ENNReal.ofReal (cWc * r j * M j)) ∧
      (∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
        oTo Obs2.wA j (histS R j t) ((obsHist R P o₀ j t).K X) ≤
          ENNReal.ofReal (kseq (8 * θb) B r (fun i => cWc * M i) j)) := by
  intro B θb r q cWc CM M
  have hw0 : Obs2.wA.ab = 0 := Obs2.wA_ab
  have hwa : Obs2.wA.a ≠ ⊤ := by simp [Obs2.wA]
  have hwb : Obs2.wA.b ≠ ⊤ := by simp [Obs2.wA]
  have hcx := H.hcx
  have hcb : 0 ≤ 8 * cx κ cT := by positivity
  have hB : 0 ≤ B := by
    have h1 := mul_nonneg hθ0 hcb
    have h2 := mul_nonneg hC₁k (by positivity : (0 : ℝ) ≤ 8 + 2 * (8 * cx κ cT) + (8 * cx κ cT) ^ 2)
    show 0 ≤ kθ0 L R.A C₀ η * (8 * cx κ cT) + C₁k * (8 + 2 * (8 * cx κ cT) + (8 * cx κ cT) ^ 2)
    linarith
  have hcR : 0 ≤ cR R Λ cm C₂ := by
    unfold cR cV cW cZ; have := H.hcmu; have := H.hC₂; positivity
  have hcW1 : 1 ≤ cWc := by show 1 ≤ 2 * C₁ + 1; linarith
  have hcW0 : 0 < cWc := by linarith
  have hQ := Step2.one_le_Q1 (d := 2) one_le_two
  have hcN : 0 ≤ Step2.cNear 2 L := Nat.cast_nonneg _
  have hQ0' : 0 ≤ Step2.Q1 2 := by linarith
  have hCM : 0 ≤ CM := by
    show 0 ≤ cs * Cm * (64 * B) * cWc + Cm * (2 * Step2.cNear 2 L * Step2.Q1 2 ^ 2 +
      cn * Step2.Q1 2 * cWc)
    positivity
  have hC1 : 0 ≤ C₁k * (2 + 2 * (8 * cx κ cT) + 64 * B) := by positivity
  have hθb0 : 0 ≤ θb := by
    have : 0 ≤ C₁k * (2 + 2 * (8 * cx κ cT) + 64 * B) * (cR R Λ cm C₂ * ε) := by
      have := H.hε; positivity
    show 0 ≤ kθ0 L R.A C₀ η + C₁k * (2 + 2 * (8 * cx κ cT) + 64 * B) * (cR R Λ cm C₂ * ε)
    linarith
  have hθb : θb ≤ 1 / 36 := by
    show kθ0 L R.A C₀ η + C₁k * (2 + 2 * (8 * cx κ cT) + 64 * B) * (cR R Λ cm C₂ * ε) ≤ 1 / 36
    linarith
  have hc : 72 * (8 * θb * (64 * B) + 8 * B) ≤ 25 * (64 * B) := by
    have := mul_le_mul_of_nonneg_right hθb hB
    linarith
  have hDh : ∀ j ≤ n, Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t := fun j hj =>
    ⟨fun i hi => ht.1 i (by omega), fun i hi => ht.2 i (by omega)⟩
  have hr0 : ∀ j ≤ n, 0 ≤ r j := fun j hj => mul_nonneg hcR (ht.1 j hj).1.le
  have hrε : ∀ j ≤ n, r j ≤ cR R Λ cm C₂ * ε := fun j hj =>
    mul_le_mul_of_nonneg_left (ht.1 j hj).2.1 hcR
  have hr' : ∀ j < n, 5 / 6 * r j ≤ r (j + 1) := by
    intro j hj
    have := g_succ_ge (hDh (j + 1) hj) hβ hδ1 H.hcg H.hε1 H.h6
    have := mul_le_mul_of_nonneg_left this hcR
    show 5 / 6 * (cR R Λ cm C₂ * (t j).1) ≤ cR R Λ cm C₂ * (t (j + 1)).1
    linarith
  have hq1 : ∀ j, 1 ≤ q j := fun j => le_max_left _ _
  have hfac : ∀ j, 1 ≤ q j * (1 + CM * max 0 (r j)) := fun j => by
    have h1 := hq1 j
    have h2 : 1 ≤ 1 + CM * max 0 (r j) := by
      have := mul_nonneg hCM (le_max_left 0 (r j)); linarith
    nlinarith
  have hMpos : ∀ j, 0 < M j := by
    intro j
    induction j with
    | zero => exact hM0
    | succ j ih =>
      show 0 < M j * (q j * (1 + CM * max 0 (r j)))
      have := hfac j
      exact mul_pos ih (by linarith)
  have hMmono : ∀ j, M j ≤ M (j + 1) := by
    intro j
    show M j ≤ M j * (q j * (1 + CM * max 0 (r j)))
    have h1 := (hMpos j).le
    have h2 := hfac j
    nlinarith
  have hmpos : ∀ i, 0 ≤ cWc * M i := fun i => mul_nonneg hcW0.le (hMpos i).le
  have hK := kseq_le (B := B) (r := r) (m := fun i => cWc * M i) n (by positivity)
    (by positivity : (0 : ℝ) ≤ 64 * B) hr0 (fun j _ => hmpos j)
    hr' (fun j _ => by
      have := hMmono j; have := hMpos j
      show cWc * M j ≤ 2 * (cWc * M (j + 1)); nlinarith) hc
  have hform : ∀ k b, ((obsHist R P o₀ k t).V b : SA .one (Lam 2 L N)).a ∈ (ℂ ∙ psibar P.a) :=
    fun k b => by rw [← histVO_a]; exact obsHist_hform R P o₀ t hf0 k b
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨hM0', fun b _ => ?_, fun X _ => ?_⟩
    · show oTo Obs2.wA 0 (histS R 0 t) (o₀.W b) ≤ _
      rw [hW0 b]; exact zero_le
    · show _ * oTo Obs2.wA 0 (histS R 0 t) (o₀.K X) ≤ _
      rw [hK0 X, mul_zero]; exact zero_le
  | succ j ih =>
    intro hj
    obtain ⟨ha, hb, hc'⟩ := ih (by omega)
    have hjn : j < n := by omega
    have hjN : j < Nh := by omega
    have hMj := hMpos j
    have hrj := hr0 j hjn.le
    have hr1 : r j ≤ 1 := (hrε j hjn.le).trans hε1
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hs, hs'⟩ :=
      hist_raw R hSB hV hm hβ hδ1 H t j hjN (hDh j hjn.le)
    have hs'' : histS R (j + 1) t = fscale (stZ' R (rawHist R j t)) * R.ℓ := rfl
    rw [← hs''] at hs'
    have hsdef : histS R j t = fscale (rawHist R j t).Z * R.ℓ := rfl
    rw [← hsdef] at hs
    have hk0 := kseq_nonneg (r := r) (by positivity : 0 ≤ 8 * θb) hB hmpos j
    set β0 := ∑ b ∈ blockIdx (L := L) (N := N) j,
      ‖mass1L (-1) ((obsHist R P o₀ j t).V b : SA .one (Lam 2 L N)).a‖ with hβ0
    have hβ00 : 0 ≤ β0 := sum_nonneg fun _ _ => norm_nonneg _
    -- the block bound of `V^{obs}_j`
    have hVo : ∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo Obs2.wA j (histS R j t) ((obsHist R P o₀ j t).V b) ≤ ENNReal.ofReal (M j) := by
      intro b hb'
      rw [Obs2.oTo_wA, eq_mass1_smul_of_span (hform j b), Tj_smul_psibar j hs]
      refine ENNReal.ofReal_le_ofReal (le_trans ?_ ha)
      have h1 : ‖mass1 (-1) ((obsHist R P o₀ j t).V b : SA .one (Lam 2 L N)).a‖ ≤ β0 :=
        single_le_sum (f := fun b => ‖mass1L (-1)
          ((obsHist R P o₀ j t).V b : SA .one (Lam 2 L N)).a‖) (fun _ _ => norm_nonneg _) hb'
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left h1 hs.le
    -- the activity
    have hk8 := hK j hjn.le
    have hKo : ∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
        oTo Obs2.wA j (histS R j t) ((obsHist R P o₀ j t).K X) ≤
          ENNReal.ofReal (kseq (8 * θb) B r (fun i => cWc * M i) j) := hc'
    have hWo : ∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo Obs2.wA j (histS R j t) ((obsHist R P o₀ j t).W b) ≤
          ENNReal.ofReal (cR R Λ cm C₂ * (t j).1 * (cWc * M j)) := fun b hb' =>
      (hb b hb').trans (ENNReal.ofReal_le_ofReal (le_of_eq (by
        show cWc * (cR R Λ cm C₂ * (t j).1) * M j = _; ring)))
    refine ⟨?_, ?_, ?_⟩
    · -- the `ℓ¹` coupling
      have hKs : ∀ X, IsSmall j X → oTo Obs2.wA j (histS R j t) ((obsHist R P o₀ j t).K X) ≤
          ENNReal.ofReal (kseq (8 * θb) B r (fun i => cWc * M i) j) := fun X hX => by
        have h := hKo X ⟨hX.1, hX.2.1⟩
        rw [show nb j X - 2 ^ 2 = 0 from Nat.sub_eq_zero_of_le hX.2.2, pow_zero,
          ENNReal.ofReal_one, one_mul] at h
        exact h
      have hS := beta_hist_step R hBB hSB hV hm hβ hδ1 H P o₀ h0 hl0 hs0 hf0 t j hjN
        (hDh j hjn.le) hε1 (M j) (cWc * r j * M j) _ hMj.le
        (mul_nonneg (mul_nonneg hcW0.le hrj) hMj.le) hk0 hVo hb hKs
      have hq : histS R (j + 1) t / histS R j t ≤ q j := le_max_right _ _
      have key := beta_real (S := ∑ c' ∈ blockIdx (L := L) (N := N) (j + 1),
          ‖mass1L (-1) ((obsHist R P o₀ (j + 1) t).V c' : SA .one (Lam 2 L N)).a‖) (β := β0)
        (s := histS R j t) (s' := histS R (j + 1) t)
        (k := kseq (8 * θb) B r (fun i => cWc * M i) j) (M := M j) (q := q j) (r := r j)
        (cs := cs) (Cm := Cm) (Bk := B) (cWc := cWc) (cN := Step2.cNear 2 L) (Q := Step2.Q1 2)
        (cn := cn) hs hs' hβ00 hMj.le hrj hr1 (Nat.cast_nonneg _) hCm hB hcW0.le hcN
        (by linarith) (Nat.cast_nonneg _) hk0 hS ha hq (hq1 j) hk8
      refine key.trans (le_of_eq ?_)
      show M j * (q j * (1 + CM * r j)) = M j * (q j * (1 + CM * max 0 (r j)))
      rw [max_eq_right hrj]
    · -- `𝒲^{obs}`
      intro c' hc''
      have hW := wobs_hist_step R hWB hSB hV hm hβ hδ1 H P Obs2.wA hw0 o₀ h0 hl0 hs0 t j hjN
        (hDh j hjn.le) hε₁ (M j) (cWc * r j * M j) hMj.le
        (mul_nonneg (mul_nonneg hcW0.le hrj) hMj.le) hVo hb c' hc''
      refine hW.trans (ENNReal.ofReal_le_ofReal ?_)
      have hCr : C₁ * r j ≤ 1 / 6 :=
        (mul_le_mul_of_nonneg_left (hrε j hjn.le) hC₁).trans hC₁ε
      exact wobs_real (a := Kw / L) (r := r j) (le_of_eq rfl) hLw hCr rfl hC₁ hrj hMj.le (hr' j hjn) (hMmono j)
    · -- `K^{obs}`
      intro X hX
      have hks := kobs_hist_step R hKB hSB hV hm hβ hδ1 H P Obs2.wA hw0 hwa hwb o₀ h0 hl0 hs0 t j hjN
        (hDh j hjn.le) (64 * B) (cWc * M j) (kseq (8 * θb) B r (fun i => cWc * M i) j)
        (by positivity) (mul_pos hcW0 hMj) hk0 hε1 hεε hεk hk8
        (fun b hb' => (hVo b hb').trans (ENNReal.ofReal_le_ofReal (by nlinarith))) hWo hKo X hX
      refine hks.trans (ENNReal.ofReal_le_ofReal ?_)
      rw [kseq_succ]
      have hgj : (t j).1 ≤ ε := (ht.1 j hjn.le).2.1
      have h1 : kθ0 L R.A C₀ η + C₁k * (2 + 2 * (8 * cx κ cT) + 64 * B) *
          (cR R Λ cm C₂ * (t j).1) ≤ θb := by
        have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgj hcR) hC1
        show _ ≤ kθ0 L R.A C₀ η + C₁k * (2 + 2 * (8 * cx κ cT) + 64 * B) * (cR R Λ cm C₂ * ε)
        linarith
      have h2 := mul_le_mul_of_nonneg_right h1
        (by positivity : (0 : ℝ) ≤ 8 * kseq (8 * θb) B r (fun i => cWc * M i) j)
      show _ ≤ 8 * θb * kseq (8 * θb) B r (fun i => cWc * M i) j +
        B * (cR R Λ cm C₂ * (t j).1) ^ 2 * (cWc * M j)
      linarith

end Hist

end

end PtCorr2
