import PtCorr2.Pair.KObsHistAB
import PtCorr2.Obs.ObsHist2

/-!
# The `ab` recursion along the history from scale `j₀`: geometric decay of the seed

Along `obsHistFrom j₀ o₀` (an anchored, `U(1)`-invariant, local observable state at `j₀`, e.g.
`redSt` at coalescence), weights with `w.Sub` and finite components:

* `kseqF θ B r m j₀ k₀`: the comparison sequence started at `j₀` from `k₀`,
  `k_{j₀} = k₀`, `k_{j+1} = θk_j + B r_j² m_j`; **`kseqF_eq_sum`**:
  `k_{j₀+d} = θ^d k₀ + ∑_{i<d} θ^{d-1-i} B r_{j₀+i}² m_{j₀+i}` (the seed decays geometrically);
  `kseqF_le`: the a priori condition `8k_j ≤ c_k r_j² m_j` propagates (copy of `kseq_le`), given
  it at `j₀`;
* `wobs_realAB`: the real inequality of the `𝒲` step for sizes with `M ≤ 2M'` (`c_W = 4C₁+1`);
* **`obs_histFromAB`**: the joint `K`/`𝒲` induction (copy of the `K`/`𝒲` part of `obs_hist`) with
  the `V`-sizes `m_j` as input (`‖V_j(B)‖ ≤ m_j`, `m_j ≤ 2m_{j+1}`: decay by `1/2` per step
  allowed), the seed `A^{(|𝓑(X)|-4)_+}‖K_{j₀}(X)‖ ≤ k₀` with `8k₀ ≤ 64B r_{j₀}² c_W m_{j₀}` and
  `‖𝒲_{j₀}‖ ≤ c_W r_{j₀} m_{j₀}`: for `j₀ ≤ j ≤ n`,

    `‖𝒲_j(B)‖ ≤ c_W r_j m_j`, `A^{(|𝓑_j(X)|-4)_+}‖K_j(X)‖ ≤ kseqF (8θ̄) B r (c_W m) j₀ k₀ j`,

  with `8θ̄ ≤ 2/9`. `WObsBoundsAB` holds unconditionally (`wobs_bounds_AB`).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

variable {L N : ℕ} [NeZero L]

/-! ### The comparison sequence from `j₀` -/

/-- The comparison sequence started at `j₀` from `k₀`. -/
def kseqF (θ B : ℝ) (r m : ℕ → ℝ) (j₀ : ℕ) (k₀ : ℝ) (j : ℕ) : ℝ :=
  θ ^ (j - j₀) * k₀ + kseq θ B (fun i => r (j₀ + i)) (fun i => m (j₀ + i)) (j - j₀)

theorem kseqF_start (θ B : ℝ) (r m : ℕ → ℝ) (j₀ : ℕ) (k₀ : ℝ) : kseqF θ B r m j₀ k₀ j₀ = k₀ := by
  simp [kseqF, kseq_zero]

theorem kseqF_succ (θ B : ℝ) (r m : ℕ → ℝ) {j₀ j : ℕ} (k₀ : ℝ) (hj : j₀ ≤ j) :
    kseqF θ B r m j₀ k₀ (j + 1) = θ * kseqF θ B r m j₀ k₀ j + B * r j ^ 2 * m j := by
  unfold kseqF
  rw [show j + 1 - j₀ = (j - j₀) + 1 by omega, kseq_succ, Nat.add_sub_cancel' hj, pow_succ]
  ring

/-- **The seed decays geometrically.** -/
theorem kseqF_eq_sum (θ B : ℝ) (r m : ℕ → ℝ) (j₀ : ℕ) (k₀ : ℝ) (d : ℕ) :
    kseqF θ B r m j₀ k₀ (j₀ + d) = θ ^ d * k₀ +
      ∑ i ∈ range d, θ ^ (d - 1 - i) * (B * r (j₀ + i) ^ 2 * m (j₀ + i)) := by
  unfold kseqF
  rw [Nat.add_sub_cancel_left, kseq_eq_sum]

theorem kseqF_nonneg {θ B : ℝ} {r m : ℕ → ℝ} {j₀ : ℕ} {k₀ : ℝ} (hθ : 0 ≤ θ) (hB : 0 ≤ B)
    (hm : ∀ j, 0 ≤ m j) (hk₀ : 0 ≤ k₀) (j : ℕ) : 0 ≤ kseqF θ B r m j₀ k₀ j := by
  unfold kseqF
  have := kseq_nonneg (r := fun i => r (j₀ + i)) hθ hB (fun i => hm (j₀ + i)) (j - j₀)
  positivity

/-- **The a priori condition propagates from `j₀`.** -/
theorem kseqF_le {θ B ck : ℝ} {r m : ℕ → ℝ} {j₀ : ℕ} {k₀ : ℝ} (n : ℕ) (hθ : 0 ≤ θ)
    (hck : 0 ≤ ck) (hr : ∀ j ≤ n, 0 ≤ r j) (hm : ∀ j ≤ n, 0 ≤ m j)
    (hr' : ∀ j, j₀ ≤ j → j < n → 5 / 6 * r j ≤ r (j + 1))
    (hm' : ∀ j, j₀ ≤ j → j < n → m j ≤ 2 * m (j + 1)) (hc : 72 * (θ * ck + 8 * B) ≤ 25 * ck)
    (h0 : 8 * k₀ ≤ ck * r j₀ ^ 2 * m j₀) :
    ∀ j, j₀ ≤ j → j ≤ n → 8 * kseqF θ B r m j₀ k₀ j ≤ ck * r j ^ 2 * m j := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => intro _; rw [kseqF_start]; exact h0
  | succ j hjj ih =>
    intro hj
    have ih := ih (by omega)
    rw [kseqF_succ θ B r m k₀ hjj]
    have hrj := hr' j hjj (by omega)
    have hmj := hm' j hjj (by omega)
    have hr0 := hr j (by omega)
    have hm0 := hm j (by omega)
    have hm1 := hm (j + 1) hj
    have h1 : r j ^ 2 ≤ 36 / 25 * r (j + 1) ^ 2 := by nlinarith
    have h2 : r j ^ 2 * m j ≤ 72 / 25 * (r (j + 1) ^ 2 * m (j + 1)) := by
      have a := mul_le_mul_of_nonneg_right h1 hm0
      have b := mul_le_mul_of_nonneg_left hmj (by positivity : (0 : ℝ) ≤ 36 / 25 * r (j + 1) ^ 2)
      linarith
    set X := r j ^ 2 * m j with hX
    have hX0 : 0 ≤ X := by positivity
    have a1 : θ * (8 * kseqF θ B r m j₀ k₀ j) ≤ θ * (ck * X) := by
      refine mul_le_mul_of_nonneg_left ?_ hθ
      rw [hX, ← mul_assoc]; exact ih
    have a2 : (θ * ck + 8 * B) * X ≤ 25 / 72 * ck * X :=
      mul_le_mul_of_nonneg_right (by linarith) hX0
    have a3 : 25 / 72 * ck * X ≤ ck * (r (j + 1) ^ 2 * m (j + 1)) := by
      have := mul_le_mul_of_nonneg_left h2 hck
      linarith
    have e1 : 8 * (θ * kseqF θ B r m j₀ k₀ j + B * r j ^ 2 * m j) =
        θ * (8 * kseqF θ B r m j₀ k₀ j) + 8 * B * X := by rw [hX]; ring
    have e2 : (θ * ck + 8 * B) * X = θ * (ck * X) + 8 * B * X := by ring
    have e3 : ck * r (j + 1) ^ 2 * m (j + 1) = ck * (r (j + 1) ^ 2 * m (j + 1)) := by ring
    rw [e1, e3]
    linarith

/-- The real inequality of the `𝒲` step, sizes decaying by at most `1/2` per step. -/
theorem wobs_realAB {W a r r' M M' C₁ cWc : ℝ}
    (hW : W ≤ (a + C₁ * r) * (cWc * r * M) + C₁ * r * M)
    (ha : a ≤ 1 / 12) (hCr : C₁ * r ≤ 1 / 12) (hcW : cWc = 4 * C₁ + 1) (hC₁ : 0 ≤ C₁)
    (hr : 0 ≤ r) (hM : 0 ≤ M) (hr' : 5 / 6 * r ≤ r') (hM' : M ≤ 2 * M') :
    W ≤ cWc * r' * M' := by
  have hc0 : 0 ≤ cWc := by rw [hcW]; linarith
  have hrM : 0 ≤ r * M := mul_nonneg hr hM
  have h1 : (a + C₁ * r) * (cWc * r * M) ≤ 1 / 6 * (cWc * (r * M)) := by
    have : a + C₁ * r ≤ 1 / 6 := by linarith
    have h2 : 0 ≤ cWc * r * M := by positivity
    nlinarith
  have hM'0 : 0 ≤ M' := by linarith
  have h3 : cWc * r' * M' ≥ cWc * (5 / 6 * r) * (M / 2) := by
    have hr'0 : 0 ≤ r' := by linarith
    have : (5 / 6 * r) * (M / 2) ≤ r' * M' := mul_le_mul hr' (by linarith) (by linarith) hr'0
    nlinarith
  have h4 : C₁ * r * M = C₁ * (r * M) := by ring
  have h5 : C₁ * (r * M) ≤ 1 / 4 * (cWc * (r * M)) := by rw [hcW]; nlinarith
  have e : cWc * (5 / 6 * r) * (M / 2) = 5 / 12 * (cWc * (r * M)) := by ring
  linarith

/-! ### The joint induction along the history from `j₀` -/

section Hist

variable {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

set_option maxHeartbeats 4000000 in
/-- **The `ab` recursion along the history from `j₀`** (`K` and `𝒲`, the `V`-sizes as input). -/
theorem obs_histFromAB {C₀ η ε₀ C₁k : ℝ} (hKB : KObsBoundsAB L R.A C₀ η ε₀ C₁k) (hC₁k : 0 ≤ C₁k)
    {Kw C₁ ε₁ : ℝ} (hWB : WObsBoundsAB L Kw C₁ ε₁) (hC₁ : 0 ≤ C₁)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    {c : Obs.Case} (P : ObsPts 2 L N) (w : Wt) (hws : w.Sub) (hwa : w.a ≠ ⊤) (hwb : w.b ≠ ⊤)
    (hwab : w.ab ≠ ⊤)
    {j₀ : ℕ} (o₀ : ObsSt c L N) (h0 : o₀.IsObs) (hl0 : ObsLocInv P j₀ o₀)
    (hs0 : ObsSymInv j₀ o₀) (ha0 : ObsAnchInv P j₀ o₀)
    (t : Flow2.Hist.Seq (Xs R)) (n : ℕ) (hn : n ≤ Nh)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε n t)
    (hθ0 : 0 ≤ kθ0 L R.A C₀ η) (hθ : kθ0 L R.A C₀ η ≤ 1 / 72)
    (hsm : C₁k * (2 + 2 * (8 * cx κ cT) + 64 * kB (kθ0 L R.A C₀ η) C₁k (8 * cx κ cT)) *
      (cR R Λ cm C₂ * ε) ≤ 1 / 72)
    (hε1 : cR R Λ cm C₂ * ε ≤ 1) (hεε : cR R Λ cm C₂ * ε ≤ ε₀)
    (hεk : (8 * cx κ cT + 64 * kB (kθ0 L R.A C₀ η) C₁k (8 * cx κ cT)) * (cR R Λ cm C₂ * ε) ≤ ε₀)
    (hLw : Kw / L ≤ 1 / 12) (hC₁ε : C₁ * (cR R Λ cm C₂ * ε) ≤ 1 / 12)
    (hε₁ : cR R Λ cm C₂ * ε ≤ ε₁)
    (m : ℕ → ℝ) (hm0 : ∀ j, 0 < m j) (hm' : ∀ j, j₀ ≤ j → j < n → m j ≤ 2 * m (j + 1))
    (hVo : ∀ j, j₀ ≤ j → j < n → ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (histS R j t) ((obsHistFrom R P j₀ o₀ j t).V b) ≤ ENNReal.ofReal (m j))
    (hW0 : ∀ b ∈ blockIdx (L := L) (N := N) j₀, oTo w j₀ (histS R j₀ t) (o₀.W b) ≤
      ENNReal.ofReal ((4 * C₁ + 1) * (cR R Λ cm C₂ * (t j₀).1) * m j₀))
    (k₀ : ℝ) (hk₀ : 0 ≤ k₀)
    (hK0 : ∀ X, IsConn j₀ X → ENNReal.ofReal (R.A ^ (nb j₀ X - 2 ^ 2)) *
      oTo w j₀ (histS R j₀ t) (o₀.K X) ≤ ENNReal.ofReal k₀)
    (h8 : 8 * k₀ ≤ 64 * kB (kθ0 L R.A C₀ η) C₁k (8 * cx κ cT) * (cR R Λ cm C₂ * (t j₀).1) ^ 2 *
      ((4 * C₁ + 1) * m j₀)) :
    let B := kB (kθ0 L R.A C₀ η) C₁k (8 * cx κ cT)
    let θb := kθ0 L R.A C₀ η + C₁k * (2 + 2 * (8 * cx κ cT) + 64 * B) * (cR R Λ cm C₂ * ε)
    let r := fun j => cR R Λ cm C₂ * (t j).1
    let cWc := 4 * C₁ + 1
    ∀ j, j₀ ≤ j → j ≤ n →
      8 * kseqF (8 * θb) B r (fun i => cWc * m i) j₀ k₀ j ≤ 64 * B * r j ^ 2 * (cWc * m j) ∧
      (∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo w j (histS R j t) ((obsHistFrom R P j₀ o₀ j t).W b) ≤
          ENNReal.ofReal (cWc * r j * m j)) ∧
      (∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
        oTo w j (histS R j t) ((obsHistFrom R P j₀ o₀ j t).K X) ≤
          ENNReal.ofReal (kseqF (8 * θb) B r (fun i => cWc * m i) j₀ k₀ j)) := by
  intro B θb r cWc
  have hcx := H.hcx
  have hcb : 0 ≤ 8 * cx κ cT := by positivity
  have hB : 0 ≤ B := by
    have h1 := mul_nonneg hθ0 hcb
    have h2 := mul_nonneg hC₁k (by positivity : (0 : ℝ) ≤ 8 + 2 * (8 * cx κ cT) + (8 * cx κ cT) ^ 2)
    show 0 ≤ kθ0 L R.A C₀ η * (8 * cx κ cT) + C₁k * (8 + 2 * (8 * cx κ cT) + (8 * cx κ cT) ^ 2)
    linarith
  have hcR : 0 ≤ cR R Λ cm C₂ := by
    unfold cR cV cW cZ; have := H.hcmu; have := H.hC₂; positivity
  have hcW1 : 1 ≤ cWc := by show 1 ≤ 4 * C₁ + 1; linarith
  have hcW0 : 0 < cWc := by linarith
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
  have hmpos : ∀ i, 0 ≤ cWc * m i := fun i => mul_nonneg hcW0.le (hm0 i).le
  have hK := kseqF_le (B := B) (r := r) (m := fun i => cWc * m i) (j₀ := j₀) (k₀ := k₀) n
    (by positivity) (by positivity : (0 : ℝ) ≤ 64 * B) hr0 (fun j _ => hmpos j)
    (fun j _ hj => hr' j hj) (fun j hj1 hj2 => by
      have := hm' j hj1 hj2
      show cWc * m j ≤ 2 * (cWc * m (j + 1)); nlinarith) hc (by
        have : 64 * B * r j₀ ^ 2 * (cWc * m j₀) = 64 * B * r j₀ ^ 2 * (cWc * m j₀) := rfl
        exact h8)
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    intro hjn
    refine ⟨hK j₀ le_rfl hjn, fun b hb => ?_, fun X hX => ?_⟩
    · rw [obsHistFrom_self]; exact hW0 b hb
    · rw [obsHistFrom_self, kseqF_start]; exact hK0 X hX
  | succ j hjj ih =>
    intro hj
    obtain ⟨hk8, hb, hc'⟩ := ih (by omega)
    have hjn : j < n := by omega
    have hjN : j < Nh := by omega
    have hmj := hm0 j
    have hrj := hr0 j hjn.le
    have hk0 := kseqF_nonneg (r := r) (j₀ := j₀) (by positivity : 0 ≤ 8 * θb) hB hmpos hk₀ j
    have hVoj := hVo j hjj hjn
    have hWo : ∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo w j (histS R j t) ((obsHistFrom R P j₀ o₀ j t).W b) ≤
          ENNReal.ofReal (cR R Λ cm C₂ * (t j).1 * (cWc * m j)) := fun b hb' =>
      (hb b hb').trans (ENNReal.ofReal_le_ofReal (le_of_eq (by
        show cWc * (cR R Λ cm C₂ * (t j).1) * m j = _; ring)))
    refine ⟨hK (j + 1) (by omega) hj, ?_, ?_⟩
    · -- `𝒲`
      intro c' hc''
      have hW := wobs_hist_stepAB R hWB hSB hV hm hβ hδ1 H P w hws o₀ h0 hl0 hs0 ha0 t j hjj hjN
        (hDh j hjn.le) hε₁ (m j) (cWc * r j * m j) hmj.le
        (mul_nonneg (mul_nonneg hcW0.le hrj) hmj.le) hVoj hb c' hc''
      refine hW.trans (ENNReal.ofReal_le_ofReal ?_)
      have hCr : C₁ * r j ≤ 1 / 12 :=
        (mul_le_mul_of_nonneg_left (hrε j hjn.le) hC₁).trans hC₁ε
      exact wobs_realAB (a := Kw / L) (r := r j) (le_of_eq rfl) hLw hCr rfl hC₁ hrj hmj.le
        (hr' j hjn) (hm' j hjj hjn)
    · -- `K`
      intro X hX
      have hks := kobs_hist_stepAB R hKB hSB hV hm hβ hδ1 H P w hws hwa hwb hwab o₀ h0 hl0 hs0 ha0
        t j hjj hjN (hDh j hjn.le) (64 * B) (cWc * m j)
        (kseqF (8 * θb) B r (fun i => cWc * m i) j₀ k₀ j)
        (by positivity) (mul_pos hcW0 hmj) hk0 hε1 hεε hεk hk8
        (fun b hb' => (hVoj b hb').trans (ENNReal.ofReal_le_ofReal (by nlinarith))) hWo hc' X hX
      refine hks.trans (ENNReal.ofReal_le_ofReal ?_)
      rw [kseqF_succ _ _ _ _ _ hjj]
      have hgj : (t j).1 ≤ ε := (ht.1 j hjn.le).2.1
      have h1 : kθ0 L R.A C₀ η + C₁k * (2 + 2 * (8 * cx κ cT) + 64 * B) *
          (cR R Λ cm C₂ * (t j).1) ≤ θb := by
        have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgj hcR) hC1
        show _ ≤ kθ0 L R.A C₀ η + C₁k * (2 + 2 * (8 * cx κ cT) + 64 * B) * (cR R Λ cm C₂ * ε)
        linarith
      have h2 := mul_le_mul_of_nonneg_right h1
        (by positivity : (0 : ℝ) ≤ 8 * kseqF (8 * θb) B r (fun i => cWc * m i) j₀ k₀ j)
      show _ ≤ 8 * θb * kseqF (8 * θb) B r (fun i => cWc * m i) j₀ k₀ j +
        B * (cR R Λ cm C₂ * (t j).1) ^ 2 * (cWc * m j)
      linarith

end Hist

end

end PtCorr2
