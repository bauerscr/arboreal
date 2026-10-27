import Flow2.FiniteHorizon

/-!
# The history-dependent finite-horizon flow (`h02uv-outline.tex`, Proposition `prop:C6`)

The variant of `Flow2.fh_flow` in which `G_j`, `m_j`, `T_j` depend on the whole history
`s_0, …, s_j`. The maps act on sequences `t : (i : ℕ) → ℝ × ℝ × X_i` and are *causal*: `G_j t`
depends only on `t_0, …, t_j` (`Causal`). The trajectory is the sequence `traj` with
`traj_{j+1} = (G_j traj, Λ μ_j + m_j traj, T_j traj)` (`traj_succ`).

The marginal coordinate *grows*: (F1) is `|G_j - g - β g²| ≤ δ β g² + c g³` with a relative band
`δ ≤ 1/2` around the one-loop coefficient `β > 0`. The flow stays in `D_ε` for initial data
`b ≤ b_max = (1/ε + N β₊)⁻¹`, `β₊ = (1 + δ) β + c` (`bmax`). (F2), (F3) are those of
`prop:fh-flow` at the current point, for histories in `D`.
The Lipschitz bounds (L) get a history term `a M`, where `M` bounds
`|δg_i| + |δμ_i| + ‖δx_i‖` for `i < j` (`HHyp`). The proofs are those of
`Flow2.FiniteHorizon`. The uniqueness argument also carries the bound
`|δg_i| + |δμ_i| + ‖δx_i‖ ≤ r |δμ_k|` for `i < k`, `r = 1 + p + q`, and this changes the
constants (`Kh`, `Qh`, `a0h`).
-/

open Set Filter Topology

noncomputable section

namespace Flow2

namespace Hist

variable {X : ℕ → Type*} [∀ j, NormedAddCommGroup (X j)]

/-- Histories: sequences of states. -/
abbrev Seq (X : ℕ → Type*) [∀ j, NormedAddCommGroup (X j)] := (i : ℕ) → ℝ × ℝ × X i

/-- The data: `G_j, m_j : Seq → ℝ` and `T_j : Seq → X_{j+1}`. -/
structure HData (X : ℕ → Type*) [∀ j, NormedAddCommGroup (X j)] where
  G : ℕ → Seq X → ℝ
  m : ℕ → Seq X → ℝ
  T : ∀ j, Seq X → X (j + 1)

/-- `f` depends only on `t_0, …, t_j`. -/
def Causal {Y : Type*} (j : ℕ) (f : Seq X → Y) : Prop :=
  ∀ t t' : Seq X, (∀ i ≤ j, t i = t' i) → f t = f t'

/-- `|g - g'| + |μ - μ'| + ‖x - x'‖`. -/
def dist3 {j : ℕ} (s s' : ℝ × ℝ × X j) : ℝ := |s.1 - s'.1| + |s.2.1 - s'.2.1| + ‖s.2.2 - s'.2.2‖

variable (F : HData X) (Λ β δ κ cg cm cT : ℝ)

/-- The domain `D_ε` with the separate constants `c_μ = 2 c_m/(Λ-1)` and `c_x = 2 c_T/(1-κ)`. -/
def InD3 (ε : ℝ) {j : ℕ} (s : ℝ × ℝ × X j) : Prop :=
  0 < s.1 ∧ s.1 ≤ ε ∧ |s.2.1| ≤ cmu Λ cm * s.1 ∧ ‖s.2.2‖ ≤ cx κ cT * s.1 ^ 3

/-- The steps before `j` satisfy the band (F1): the history is *regular*. -/
def RegH (j : ℕ) (t : Seq X) : Prop :=
  ∀ i < j, |(t (i + 1)).1 - (t i).1 - β * (t i).1 ^ 2| ≤ δ * β * (t i).1 ^ 2 + cg * (t i).1 ^ 3

/-- The history up to `j` lies in `D_ε` and is regular. -/
def InDh (ε : ℝ) (j : ℕ) (t : Seq X) : Prop := (∀ i ≤ j, InD3 Λ κ cm cT ε (t i)) ∧ RegH β δ cg j t

/-- The hypotheses of `prop:C6`, for `j < N`. -/
structure HHyp (N : ℕ) (A a ε : ℝ) : Prop where
  hΛ : 1 < Λ
  hβ : 0 < β
  hδ : 0 ≤ δ
  hδ1 : δ ≤ 1 / 2
  hκ0 : 0 ≤ κ
  hκ1 : κ < 1
  hcg : 0 < cg
  hcm : 0 < cm
  hcT : 0 < cT
  hA : 0 ≤ A
  ha : 0 ≤ a
  causG : ∀ j < N, Causal j (F.G j)
  causm : ∀ j < N, Causal j (F.m j)
  causT : ∀ j < N, Causal j (F.T j)
  contG : ∀ j < N, Continuous (F.G j)
  contm : ∀ j < N, Continuous (F.m j)
  contT : ∀ j < N, Continuous (F.T j)
  F1 : ∀ j < N, ∀ t, InDh Λ β δ κ cg cm cT ε j t →
    |F.G j t - (t j).1 - β * (t j).1 ^ 2| ≤ δ * β * (t j).1 ^ 2 + cg * (t j).1 ^ 3
  F2 : ∀ j < N, ∀ t, InDh Λ β δ κ cg cm cT ε j t → |F.m j t| ≤ cm * (t j).1
  F3 : ∀ j < N, ∀ t, InDh Λ β δ κ cg cm cT ε j t → ‖F.T j t‖ ≤ κ * ‖(t j).2.2‖ + cT * (t j).1 ^ 3
  LG : ∀ j < N, ∀ t t', InDh Λ β δ κ cg cm cT ε j t → InDh Λ β δ κ cg cm cT ε j t' → ∀ M, 0 ≤ M →
    (∀ i < j, dist3 (t i) (t' i) ≤ M) →
    |F.G j t - F.G j t'| ≤ (1 + a) * |(t j).1 - (t' j).1| + a * |(t j).2.1 - (t' j).2.1| +
      A * ‖(t j).2.2 - (t' j).2.2‖ + a * M
  Lm : ∀ j < N, ∀ t t', InDh Λ β δ κ cg cm cT ε j t → InDh Λ β δ κ cg cm cT ε j t' → ∀ M, 0 ≤ M →
    (∀ i < j, dist3 (t i) (t' i) ≤ M) →
    |F.m j t - F.m j t'| ≤ A * |(t j).1 - (t' j).1| + a * |(t j).2.1 - (t' j).2.1| +
      A * ‖(t j).2.2 - (t' j).2.2‖ + a * M
  LT : ∀ j < N, ∀ t t', InDh Λ β δ κ cg cm cT ε j t → InDh Λ β δ κ cg cm cT ε j t' → ∀ M, 0 ≤ M →
    (∀ i < j, dist3 (t i) (t' i) ≤ M) →
    ‖F.T j t - F.T j t'‖ ≤ κ * ‖(t j).2.2 - (t' j).2.2‖ +
      a * (|(t j).1 - (t' j).1| + |(t j).2.1 - (t' j).2.1|) + a * M

/-- `Q = 4/(1-κ)`. -/
def Qh : ℝ := 4 / (1 - κ)

/-- `K = 2(4 + AQ)/(Λ-1)`. -/
def Kh (A : ℝ) : ℝ := 2 * (4 + A * Qh κ) / (Λ - 1)

/-- `a₀ = min(1, 1/(K+Q), (Λ-1)/(2(AK + AQ + 2 + K + Q)))`. -/
def a0h (A : ℝ) : ℝ :=
  min 1 (min (1 / (Kh Λ κ A + Qh κ))
    ((Λ - 1) / (2 * (A * Kh Λ κ A + A * Qh κ + 2 + Kh Λ κ A + Qh κ))))

/-- `β₊ = (1 + δ) β + c`, the largest one-step growth rate of `1/g`. -/
def betap : ℝ := (1 + δ) * β + cg

/-- The largest admissible initial coupling, `b_max = (1/ε + N β₊)⁻¹`. -/
def bmax (N : ℕ) (ε : ℝ) : ℝ := 1 / (1 / ε + N * betap β δ cg)

/-- The smallness condition on `ε`: `eps0` and `c_μ β₊ ε ≤ c`. -/
def eps0u : ℝ := min (eps0 β κ cg) (cm / (cmu Λ cm * betap β δ cg))

/-- The constant of the band for `1/g`: `C = 2(β² + (1 + β) c)`. -/
def Cgu : ℝ := 2 * (β ^ 2 + (1 + β) * cg)

/-! ### Causal recursions -/

section Rec

variable (s0 : Seq X) (st : ∀ j, Seq X → ℝ × ℝ × X (j + 1))

/-- The approximants: `appr k` is correct on `0, …, k`. -/
def appr : ℕ → Seq X
  | 0 => s0
  | k + 1 => Function.update (appr k) (k + 1) (st k (appr k))

/-- The sequence defined by `t_0 = s0_0`, `t_{k+1} = st_k(t)`. -/
def tr : Seq X := fun i => appr s0 st i i

lemma appr_eq : ∀ k i, i ≤ k → appr s0 st k i = tr s0 st i := by
  intro k
  induction k with
  | zero => intro i hi; obtain rfl : i = 0 := by omega
            rfl
  | succ k ih =>
    intro i hi
    rcases (show i = k + 1 ∨ i ≤ k by omega) with rfl | hik
    · rfl
    · rw [appr, Function.update_of_ne (by omega), ih i hik]

lemma tr_succ {k : ℕ} (hc : Causal k (st k)) : tr s0 st (k + 1) = st k (tr s0 st) := by
  show appr s0 st (k + 1) (k + 1) = _
  rw [appr, Function.update_self]
  exact hc _ _ fun i hi => appr_eq s0 st k i hi

lemma continuous_appr {P : Type*} [TopologicalSpace P] {s0 : P → Seq X} (hs0 : Continuous s0)
    {N : ℕ} (hst : ∀ j < N, Continuous (st j)) :
    ∀ k ≤ N, Continuous fun p => appr (s0 p) st k := by
  intro k
  induction k with
  | zero => intro _; exact hs0
  | succ k ih =>
    intro hk
    have h := ih (by omega)
    exact h.update (k + 1) ((hst k (by omega)).comp h)

lemma continuous_tr {P : Type*} [TopologicalSpace P] {s0 : P → Seq X} (hs0 : Continuous s0)
    {N : ℕ} (hst : ∀ j < N, Continuous (st j)) {k : ℕ} (hk : k ≤ N) :
    Continuous fun p => tr (s0 p) st k :=
  (continuous_apply k).comp (continuous_appr st hs0 hst k hk)

end Rec

/-! ### The flow and the clamped flow -/

/-- One step of the flow. -/
def stepS (j : ℕ) (t : Seq X) : ℝ × ℝ × X (j + 1) :=
  (F.G j t, Λ * (t j).2.1 + F.m j t, F.T j t)

/-- One step of the clamped flow. -/
def stepc (j : ℕ) (t : Seq X) : ℝ × ℝ × X (j + 1) :=
  (F.G j t, clamp (cmu Λ cm * F.G j t) (Λ * (t j).2.1 + F.m j t), F.T j t)

/-- The flow started at `(b, μ₀, 0)`. -/
def traj (b μ₀ : ℝ) : Seq X := tr (fun _ => (b, μ₀, 0)) (stepS F Λ)

/-- The clamped flow. -/
def trajc (b μ₀ : ℝ) : Seq X := tr (fun _ => (b, clamp (cmu Λ cm * b) μ₀, 0)) (stepc F Λ cm)

/-- Admissible initial data. -/
def Admissible (N : ℕ) (ε b μ₀ : ℝ) : Prop :=
  (∀ j ≤ N, InD3 Λ κ cm cT ε (traj F Λ b μ₀ j)) ∧ (traj F Λ b μ₀ N).2.1 = 0

variable {F Λ β δ κ cg cm cT}

section Basic

variable {N : ℕ} {A a ε : ℝ} (H : HHyp F Λ β δ κ cg cm cT N A a ε)
include H

lemma causal_stepS {j : ℕ} (hj : j < N) : Causal j (stepS F Λ j) := fun t t' h => by
  simp only [stepS, H.causG j hj t t' h, H.causm j hj t t' h, H.causT j hj t t' h, h j le_rfl]

lemma causal_stepc {j : ℕ} (hj : j < N) : Causal j (stepc F Λ cm j) := fun t t' h => by
  simp only [stepc, H.causG j hj t t' h, H.causm j hj t t' h, H.causT j hj t t' h, h j le_rfl]

lemma traj_succ (b μ₀ : ℝ) {j : ℕ} (hj : j < N) :
    traj F Λ b μ₀ (j + 1) = (F.G j (traj F Λ b μ₀),
      Λ * (traj F Λ b μ₀ j).2.1 + F.m j (traj F Λ b μ₀), F.T j (traj F Λ b μ₀)) :=
  tr_succ _ _ (causal_stepS H hj)

lemma trajc_succ (b μ₀ : ℝ) {j : ℕ} (hj : j < N) :
    trajc F Λ cm b μ₀ (j + 1) = (F.G j (trajc F Λ cm b μ₀),
      clamp (cmu Λ cm * F.G j (trajc F Λ cm b μ₀))
        (Λ * (trajc F Λ cm b μ₀ j).2.1 + F.m j (trajc F Λ cm b μ₀)), F.T j (trajc F Λ cm b μ₀)) :=
  tr_succ _ _ (causal_stepc H hj)

end Basic

lemma traj_zero (b μ₀ : ℝ) : traj F Λ b μ₀ 0 = (b, μ₀, 0) := rfl

lemma trajc_zero (b μ₀ : ℝ) : trajc F Λ cm b μ₀ 0 = (b, clamp (cmu Λ cm * b) μ₀, 0) := rfl

/-! ### One step -/

/-- The arithmetic of one step: `5g/6 ≤ G ≤ g + β₊ g²` and `‖T‖ ≤ c_x G³`. -/
lemma step_core (hβ : 0 < β) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hc : 0 < cg) (hcT : 0 < cT) {ε : ℝ} (he : ε ≤ eps0 β κ cg) {j : ℕ} {s : ℝ × ℝ × X j} (hs : InD3 Λ κ cm cT ε s)
    {G : ℝ} {T : X (j + 1)}
    (hF1 : |G - s.1 - β * s.1 ^ 2| ≤ δ * β * s.1 ^ 2 + cg * s.1 ^ 3)
    (hF3 : ‖T‖ ≤ κ * ‖s.2.2‖ + cT * s.1 ^ 3) :
    5 / 6 * s.1 ≤ G ∧ G ≤ s.1 + betap β δ cg * s.1 ^ 2 ∧ ‖T‖ ≤ cx κ cT * G ^ 3 := by
  obtain ⟨he1, he2, he3⟩ := eps_facts hc hβ he
  have hF1 := abs_le.1 hF1
  obtain ⟨hg, hgε, -, hx⟩ := hs
  have hcx := cx_mul (c := cT) hκ1
  have hcx0 := (cx_pos hκ1 hcT).le
  set g := s.1
  set t := (β + cg) * ε with htdef
  have hg1 : g ≤ 1 := hgε.trans he1
  have f1 : g ^ 2 ≤ ε * g := by rw [sq]; exact mul_le_mul_of_nonneg_right hgε hg.le
  have f2 : g ^ 3 ≤ g ^ 2 := pow_le_pow_of_le_one hg.le hg1 (by norm_num)
  have f4 : cg * g ^ 3 ≤ cg * (ε * g) := mul_le_mul_of_nonneg_left (f2.trans f1) hc.le
  have ht0 : 0 ≤ t := mul_nonneg (by linarith) (by linarith)
  have ht : t ≤ 1 / 6 := by linarith
  have f6 : t * g = β * (ε * g) + cg * (ε * g) := by rw [htdef]; ring
  have fβ : 0 ≤ β * (ε * g) := mul_nonneg hβ.le (mul_nonneg (hg.le.trans hgε) hg.le)
  have fδ : δ * β * g ^ 2 ≤ β * g ^ 2 := by
    have : 0 ≤ β * g ^ 2 := by positivity
    nlinarith
  have hG' : g * (1 - t) ≤ G := by nlinarith
  have hlow : 5 / 6 * g ≤ G := by nlinarith
  have hup : G ≤ g + betap β δ cg * g ^ 2 := by
    unfold betap
    have : cg * g ^ 3 ≤ cg * g ^ 2 := mul_le_mul_of_nonneg_left f2 hc.le
    nlinarith
  refine ⟨hlow, hup, ?_⟩
  have hc1 : g ^ 3 * (1 - 3 * t) ≤ G ^ 3 := by
    have h1 : (g * (1 - t)) ^ 3 ≤ G ^ 3 :=
      pow_le_pow_left₀ (mul_nonneg hg.le (by linarith)) hG' 3
    have h2 : 0 ≤ g ^ 3 * (t ^ 2 * (3 - t)) :=
      mul_nonneg (pow_nonneg hg.le 3) (mul_nonneg (sq_nonneg t) (by linarith))
    nlinarith
  have k1 : 0 ≤ cx κ cT * g ^ 3 * ((1 - κ) - 6 * t) :=
    mul_nonneg (mul_nonneg hcx0 (pow_nonneg hg.le 3)) (by linarith)
  have k2 : cx κ cT * (g ^ 3 * (1 - 3 * t)) ≤ cx κ cT * G ^ 3 :=
    mul_le_mul_of_nonneg_left hc1 hcx0
  have k3 : cx κ cT * (1 - κ) * g ^ 3 = 2 * cT * g ^ 3 := by rw [hcx]
  have k4 : κ * ‖s.2.2‖ ≤ κ * (cx κ cT * g ^ 3) := mul_le_mul_of_nonneg_left hx hκ0
  nlinarith

/-- `1/g - β₊ ≤ 1/G` if `0 < G ≤ g + β₊ g²`. -/
lemma inv_step {g G bp : ℝ} (hg : 0 < g) (hG : 0 < G) (hbp : 0 ≤ bp) (h : G ≤ g + bp * g ^ 2) :
    1 / g - bp ≤ 1 / G := by
  have h1 : 1 / (g + bp * g ^ 2) ≤ 1 / G := one_div_le_one_div_of_le hG h
  have h2 : 1 / g - bp ≤ 1 / (g + bp * g ^ 2) := by
    rw [div_sub' hg.ne', div_le_div_iff₀ hg (by positivity)]
    nlinarith [sq_nonneg (bp * g), mul_nonneg hbp hg.le]
  linarith

lemma eps0u_le (he : ε ≤ eps0u Λ β δ κ cg cm) : ε ≤ eps0 β κ cg := he.trans (min_le_left _ _)

lemma eps0u_mu (hΛ : 1 < Λ) (hcm : 0 < cm) (hcg : 0 < cg) (hβ : 0 < β) (hδ : 0 ≤ δ) {ε : ℝ}
    (he : ε ≤ eps0u Λ β δ κ cg cm) : cmu Λ cm * betap β δ cg * ε ≤ cm := by
  have h : ε ≤ cm / (cmu Λ cm * betap β δ cg) := he.trans (min_le_right _ _)
  have hp : 0 < cmu Λ cm * betap β δ cg := mul_pos (cmu_pos hΛ hcm) (by unfold betap; positivity)
  rw [le_div_iff₀ hp] at h; linarith

lemma bmax_le {N : ℕ} {ε : ℝ} (hε : 0 < ε) (hβ : 0 < β) (hδ : 0 ≤ δ) (hc : 0 < cg) :
    bmax β δ cg N ε ≤ ε := by
  unfold bmax
  have : 0 ≤ (N : ℝ) * betap β δ cg := by unfold betap; positivity
  rw [div_le_iff₀ (by positivity)]
  rw [mul_add, mul_one_div_cancel hε.ne']
  nlinarith

lemma inv_b_of_mem {N : ℕ} {ε b : ℝ} (hε : 0 < ε) (hβ : 0 < β) (hδ : 0 ≤ δ) (hc : 0 < cg)
    (hb : b ∈ Ioc 0 (bmax β δ cg N ε)) : 1 / ε + N * betap β δ cg ≤ 1 / b := by
  have hp : 0 < 1 / ε + N * betap β δ cg := by unfold betap; positivity
  have := one_div_le_one_div_of_le hb.1 hb.2
  unfold bmax at this
  rwa [one_div_one_div] at this

section Step

variable {N : ℕ} {A a ε : ℝ} (H : HHyp F Λ β δ κ cg cm cT N A a ε) (he : ε ≤ eps0u Λ β δ κ cg cm)
  (hε : 0 < ε)
include H he

lemma step_D {j : ℕ} (hj : j < N) {t : Seq X} (ht : InDh Λ β δ κ cg cm cT ε j t) :
    5 / 6 * (t j).1 ≤ F.G j t ∧ F.G j t ≤ (t j).1 + betap β δ cg * (t j).1 ^ 2 ∧
      ‖F.T j t‖ ≤ cx κ cT * F.G j t ^ 3 :=
  step_core H.hβ H.hδ H.hδ1 H.hκ0 H.hκ1 H.hcg H.hcT (eps0u_le he) (ht.1 j le_rfl) (H.F1 j hj t ht)
    (H.F3 j hj t ht)

lemma step_InD {j : ℕ} (hj : j < N) {t : Seq X} (ht : InDh Λ β δ κ cg cm cT ε j t) {μ' : ℝ}
    (hGε : F.G j t ≤ ε) (hμ : |μ'| ≤ cmu Λ cm * F.G j t) :
    InD3 Λ κ cm cT ε ((F.G j t, μ', F.T j t) : ℝ × ℝ × X (j + 1)) := by
  obtain ⟨h1, h2, h3⟩ := step_D H he hj ht
  have := (ht.1 j le_rfl).1
  exact ⟨by show 0 < F.G j t; linarith, hGε, hμ, h3⟩

lemma cmu_G_le {j : ℕ} (hj : j < N) {t : Seq X} (ht : InDh Λ β δ κ cg cm cT ε j t) :
    cmu Λ cm * F.G j t ≤ cmu Λ cm * (t j).1 + cm * (t j).1 := by
  obtain ⟨-, h2, -⟩ := step_D H he hj ht
  have hcpos := cmu_pos H.hΛ H.hcm
  have hg := (ht.1 j le_rfl).1
  have hgε := (ht.1 j le_rfl).2.1
  have hμ := eps0u_mu H.hΛ H.hcm H.hcg H.hβ H.hδ he
  have hbp : 0 ≤ betap β δ cg := by have := H.hδ; have := H.hβ; have := H.hcg; unfold betap; positivity
  have e1 : cmu Λ cm * F.G j t ≤ cmu Λ cm * ((t j).1 + betap β δ cg * (t j).1 ^ 2) :=
    mul_le_mul_of_nonneg_left h2 hcpos.le
  have e2 : cmu Λ cm * betap β δ cg * (t j).1 ≤ cm := by
    calc cmu Λ cm * betap β δ cg * (t j).1 ≤ cmu Λ cm * betap β δ cg * ε :=
          mul_le_mul_of_nonneg_left hgε (mul_nonneg hcpos.le hbp)
      _ ≤ cm := hμ
  have e3 : cmu Λ cm * betap β δ cg * (t j).1 * (t j).1 ≤ cm * (t j).1 :=
    mul_le_mul_of_nonneg_right e2 hg.le
  nlinarith

lemma top_step {j : ℕ} (hj : j < N) {t : Seq X} (ht : InDh Λ β δ κ cg cm cT ε j t)
    (htop : (t j).2.1 = cmu Λ cm * (t j).1) :
    clamp (cmu Λ cm * F.G j t) (Λ * (t j).2.1 + F.m j t) = cmu Λ cm * F.G j t := by
  obtain ⟨h1, -, -⟩ := step_D H he hj ht
  have hm := (abs_le.1 (H.F2 j hj t ht)).1
  have hcm := cmu_mul (c := cm) H.hΛ
  have hcpos := cmu_pos H.hΛ H.hcm
  have hg := (ht.1 j le_rfl).1
  have hcg := mul_pos H.hcg hg
  have hG := cmu_G_le H he hj ht
  apply clamp_of_le (mul_nonneg hcpos.le (by linarith))
  rw [htop]
  have e : cmu Λ cm * (t j).1 * Λ = cmu Λ cm * (t j).1 + 2 * cm * (t j).1 := by
    linear_combination (t j).1 * hcm
  linarith

lemma bot_step {j : ℕ} (hj : j < N) {t : Seq X} (ht : InDh Λ β δ κ cg cm cT ε j t)
    (hbot : (t j).2.1 = -(cmu Λ cm * (t j).1)) :
    clamp (cmu Λ cm * F.G j t) (Λ * (t j).2.1 + F.m j t) = -(cmu Λ cm * F.G j t) := by
  obtain ⟨h1, -, -⟩ := step_D H he hj ht
  have hm := (abs_le.1 (H.F2 j hj t ht)).2
  have hcm := cmu_mul (c := cm) H.hΛ
  have hcpos := cmu_pos H.hΛ H.hcm
  have hg := (ht.1 j le_rfl).1
  have hcg := mul_pos H.hcg hg
  have hG := cmu_G_le H he hj ht
  apply clamp_of_le' (mul_nonneg hcpos.le (by linarith))
  rw [hbot]
  have e : cmu Λ cm * (t j).1 * Λ = cmu Λ cm * (t j).1 + 2 * cm * (t j).1 := by
    linear_combination (t j).1 * hcm
  linarith

/-! ### The clamped flow -/

include hε in
/-- The invariant of the clamped flow: `D_ε` and `1/g_i ≥ 1/b - i β₊`. -/
lemma trajc_InDh {b : ℝ} (hb : b ∈ Ioc 0 (bmax β δ cg N ε)) (μ₀ : ℝ) :
    ∀ j ≤ N, InDh Λ β δ κ cg cm cT ε j (trajc F Λ cm b μ₀) ∧
      ∀ i ≤ j, 1 / b - i * betap β δ cg ≤ 1 / (trajc F Λ cm b μ₀ i).1 := by
  have hbinv := inv_b_of_mem hε H.hβ H.hδ H.hcg hb
  have hbp : 0 ≤ betap β δ cg := by have := H.hδ; have := H.hβ; have := H.hcg; unfold betap; positivity
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨⟨fun i hi => ?_, fun i hi => absurd hi (Nat.not_lt_zero _)⟩, fun i hi => ?_⟩
    · obtain rfl : i = 0 := by omega
      exact ⟨hb.1, hb.2.trans (bmax_le hε H.hβ H.hδ H.hcg),
        abs_clamp_le _ (mul_nonneg (cmu_pos H.hΛ H.hcm).le hb.1.le),
        by simp only [trajc_zero, norm_zero]; exact mul_nonneg (cx_pos H.hκ1 H.hcT).le (by
          have := hb.1; positivity)⟩
    · obtain rfl : i = 0 := by omega
      simp [trajc_zero]
  | succ j ih =>
    intro hj
    obtain ⟨hs, hinv⟩ := ih (by omega)
    obtain ⟨h1, h2, -⟩ := step_D H he (by omega : j < N) hs
    have hg := (hs.1 j le_rfl).1
    have hGpos : 0 < F.G j (trajc F Λ cm b μ₀) := by linarith
    have hnew : 1 / b - ((j + 1 : ℕ) : ℝ) * betap β δ cg ≤ 1 / F.G j (trajc F Λ cm b μ₀) := by
      have := inv_step hg hGpos hbp h2
      have := hinv j le_rfl
      push_cast; linarith
    have hGε : F.G j (trajc F Λ cm b μ₀) ≤ ε := by
      have hle : 1 / ε ≤ 1 / F.G j (trajc F Λ cm b μ₀) := by
        have : ((j + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hj
        nlinarith
      rwa [one_div_le_one_div hε hGpos] at hle
    refine ⟨⟨fun i hi => ?_, fun i hi => ?_⟩, fun i hi => ?_⟩
    · rcases (show i = j + 1 ∨ i ≤ j by omega) with rfl | hij
      · rw [trajc_succ H b μ₀ (by omega)]
        exact step_InD H he (by omega) hs hGε
          (abs_clamp_le _ (mul_nonneg (cmu_pos H.hΛ H.hcm).le (by linarith)))
      · exact hs.1 i hij
    · rcases (show i = j ∨ i < j by omega) with rfl | hij
      · rw [trajc_succ H b μ₀ (by omega)]; exact H.F1 i (by omega) _ hs
      · exact hs.2 i hij
    · rcases (show i = j + 1 ∨ i ≤ j by omega) with rfl | hij
      · rw [trajc_succ H b μ₀ (by omega)]; exact hnew
      · exact hinv i hij

include hε in
lemma trajc_InD {b : ℝ} (hb : b ∈ Ioc 0 (bmax β δ cg N ε)) (μ₀ : ℝ) {j : ℕ} (hj : j ≤ N) :
    InD3 Λ κ cm cT ε (trajc F Λ cm b μ₀ j) :=
  (trajc_InDh H he hε hb μ₀ j hj).1.1 j le_rfl

omit he in
lemma continuous_trajc {j : ℕ} (hj : j ≤ N) :
    Continuous (fun p : ℝ × ℝ => trajc F Λ cm p.1 p.2 j) := by
  refine continuous_tr (s0 := fun p : ℝ × ℝ => fun _ => (p.1, clamp (cmu Λ cm * p.1) p.2, 0))
    (stepc F Λ cm) ?_ (fun k hk => ?_) hj
  · refine continuous_pi fun i => continuous_fst.prodMk ((continuous_clamp.comp
      ((continuous_const.mul continuous_fst).prodMk continuous_snd)).prodMk continuous_const)
  · have hG := H.contG k hk
    have hm := H.contm k hk
    have hT := H.contT k hk
    exact hG.prodMk ((continuous_clamp.comp ((continuous_const.mul hG).prodMk
      ((continuous_const.mul (continuous_fst.comp (continuous_snd.comp (continuous_apply k)))).add
        hm))).prodMk hT)

include hε in
lemma trajc_top {b : ℝ} (hb : b ∈ Ioc 0 (bmax β δ cg N ε)) (μ₀ : ℝ) {k : ℕ}
    (hk : (trajc F Λ cm b μ₀ k).2.1 = cmu Λ cm * (trajc F Λ cm b μ₀ k).1) :
    ∀ j, k ≤ j → j ≤ N → (trajc F Λ cm b μ₀ j).2.1 = cmu Λ cm * (trajc F Λ cm b μ₀ j).1 := by
  intro j
  induction j with
  | zero => intro h _; obtain rfl : k = 0 := by omega
            exact hk
  | succ j ih =>
    intro h1 h2
    rcases (show k = j + 1 ∨ k ≤ j by omega) with rfl | h1'
    · exact hk
    rw [trajc_succ H b μ₀ (by omega)]
    exact top_step H he (by omega) (trajc_InDh H he hε hb μ₀ j (by omega)).1 (ih h1' (by omega))

include hε in
lemma trajc_bot {b : ℝ} (hb : b ∈ Ioc 0 (bmax β δ cg N ε)) (μ₀ : ℝ) {k : ℕ}
    (hk : (trajc F Λ cm b μ₀ k).2.1 = -(cmu Λ cm * (trajc F Λ cm b μ₀ k).1)) :
    ∀ j, k ≤ j → j ≤ N → (trajc F Λ cm b μ₀ j).2.1 = -(cmu Λ cm * (trajc F Λ cm b μ₀ j).1) := by
  intro j
  induction j with
  | zero => intro h _; obtain rfl : k = 0 := by omega
            exact hk
  | succ j ih =>
    intro h1 h2
    rcases (show k = j + 1 ∨ k ≤ j by omega) with rfl | h1'
    · exact hk
    rw [trajc_succ H b μ₀ (by omega)]
    exact bot_step H he (by omega) (trajc_InDh H he hε hb μ₀ j (by omega)).1 (ih h1' (by omega))

include hε in
lemma trajc_strict {b : ℝ} (hb : b ∈ Ioc 0 (bmax β δ cg N ε)) {μ₀ : ℝ}
    (h0 : (trajc F Λ cm b μ₀ N).2.1 = 0) :
    ∀ k ≤ N, |(trajc F Λ cm b μ₀ k).2.1| < cmu Λ cm * (trajc F Λ cm b μ₀ k).1 := by
  intro k hk
  have hD := trajc_InD H he hε hb μ₀ hk
  have hN := trajc_InD H he hε hb μ₀ (le_refl N)
  have hcp := cmu_pos H.hΛ H.hcm
  have hpos : 0 < cmu Λ cm * (trajc F Λ cm b μ₀ N).1 := mul_pos hcp hN.1
  rcases hD.2.2.1.lt_or_eq with h | h
  · exact h
  exfalso
  rcases (abs_eq (mul_nonneg hcp.le hD.1.le)).1 h with h' | h'
  · have := trajc_top H he hε hb μ₀ h' N hk le_rfl; linarith
  · have := trajc_bot H he hε hb μ₀ h' N hk le_rfl; linarith

include hε in
lemma admissible_of_zero {b : ℝ} (hb : b ∈ Ioc 0 (bmax β δ cg N ε)) {μ₀ : ℝ}
    (h0 : (trajc F Λ cm b μ₀ N).2.1 = 0) : Admissible F Λ κ cm cT N ε b μ₀ := by
  have hs := trajc_strict H he hε hb h0
  have e : ∀ k ≤ N, ∀ i ≤ k, trajc F Λ cm b μ₀ i = traj F Λ b μ₀ i := by
    intro k
    induction k with
    | zero =>
      intro _ i hi
      obtain rfl : i = 0 := by omega
      have h := hs 0 (Nat.zero_le _)
      rw [trajc_zero, traj_zero, clamp_eq_of_abs_lt (r := cmu Λ cm * b) h]
    | succ k ih =>
      intro hk i hi
      rcases (show i = k + 1 ∨ i ≤ k by omega) with rfl | hik
      · have hall := ih (by omega)
        have h := hs (k + 1) hk
        have hkN : k < N := by omega
        rw [trajc_succ H b μ₀ hkN] at h ⊢
        rw [clamp_eq_of_abs_lt h, traj_succ H b μ₀ hkN, H.causG k hkN _ _ hall,
          H.causm k hkN _ _ hall, H.causT k hkN _ _ hall, hall k le_rfl]
      · exact ih (by omega) i hik
  refine ⟨fun k hk => e N le_rfl k hk ▸ trajc_InD H he hε hb μ₀ hk, ?_⟩
  rw [← e N le_rfl N le_rfl]; exact h0

omit he in
/-- Along admissible initial data the clamped flow is the flow. -/
lemma trajc_eq_traj {b μ₀ : ℝ} (h : Admissible F Λ κ cm cT N ε b μ₀) :
    ∀ k ≤ N, ∀ i ≤ k, trajc F Λ cm b μ₀ i = traj F Λ b μ₀ i := by
  intro k
  induction k with
  | zero =>
    intro _ i hi
    obtain rfl : i = 0 := by omega
    have h0 : |μ₀| ≤ cmu Λ cm * b := (h.1 0 (Nat.zero_le _)).2.2.1
    rw [trajc_zero, traj_zero, clamp_of_abs_le h0]
  | succ k ih =>
    intro hk i hi
    rcases (show i = k + 1 ∨ i ≤ k by omega) with rfl | hik
    · have hall := ih (by omega)
      have hkN : k < N := by omega
      have h1 := (h.1 (k + 1) hk).2.2.1
      rw [traj_succ H b μ₀ hkN] at h1
      rw [trajc_succ H b μ₀ hkN, H.causG k hkN _ _ hall, H.causm k hkN _ _ hall,
        H.causT k hkN _ _ hall, hall k le_rfl, clamp_of_abs_le h1, traj_succ H b μ₀ hkN]
    · exact ih (by omega) i hik

include hε in
lemma phi_pos_of_ge {b : ℝ} (hb : b ∈ Ioc 0 (bmax β δ cg N ε)) {μ₀ : ℝ} (h : cmu Λ cm * b ≤ μ₀) :
    0 < (trajc F Λ cm b μ₀ N).2.1 := by
  have hcp := cmu_pos H.hΛ H.hcm
  have h0 : (trajc F Λ cm b μ₀ 0).2.1 = cmu Λ cm * (trajc F Λ cm b μ₀ 0).1 :=
    clamp_of_le (mul_nonneg hcp.le hb.1.le) h
  rw [trajc_top H he hε hb μ₀ h0 N (Nat.zero_le _) le_rfl]
  exact mul_pos hcp (trajc_InD H he hε hb μ₀ (le_refl N)).1

include hε in
lemma phi_neg_of_le {b : ℝ} (hb : b ∈ Ioc 0 (bmax β δ cg N ε)) {μ₀ : ℝ}
    (h : μ₀ ≤ -(cmu Λ cm * b)) : (trajc F Λ cm b μ₀ N).2.1 < 0 := by
  have hcp := cmu_pos H.hΛ H.hcm
  have h0 : (trajc F Λ cm b μ₀ 0).2.1 = -(cmu Λ cm * (trajc F Λ cm b μ₀ 0).1) :=
    clamp_of_le' (mul_nonneg hcp.le hb.1.le) h
  rw [trajc_bot H he hε hb μ₀ h0 N (Nat.zero_le _) le_rfl]
  have := mul_pos hcp (trajc_InD H he hε hb μ₀ (le_refl N)).1
  linarith

omit he in
lemma continuous_phi (b : ℝ) : Continuous (fun μ => (trajc F Λ cm b μ N).2.1) :=
  (continuous_fst.comp (continuous_snd.comp (continuous_trajc H le_rfl))).comp
    (continuous_const.prodMk continuous_id)

omit he in
lemma continuous_phi' (μ : ℝ) : Continuous (fun b => (trajc F Λ cm b μ N).2.1) :=
  (continuous_fst.comp (continuous_snd.comp (continuous_trajc H le_rfl))).comp
    (continuous_id.prodMk continuous_const)

include hε in
/-- **Existence**. -/
theorem exists_admissible {b : ℝ} (hb : b ∈ Ioc 0 (bmax β δ cg N ε)) :
    ∃ μ₀, Admissible F Λ κ cm cT N ε b μ₀ := by
  have hr : 0 ≤ cmu Λ cm * b := mul_nonneg (cmu_pos H.hΛ H.hcm).le hb.1.le
  obtain ⟨μ₀, -, hμ⟩ := intermediate_value_Icc (by linarith : -(cmu Λ cm * b) ≤ cmu Λ cm * b)
    (continuous_phi H b).continuousOn
    ⟨(phi_neg_of_le H he hε hb le_rfl).le, (phi_pos_of_ge H he hε hb le_rfl).le⟩
  exact ⟨μ₀, admissible_of_zero H he hε hb hμ⟩

end Step

/-- Admissible trajectories are regular histories in `D_ε`. -/
lemma admissible_InDh {N : ℕ} {A a ε : ℝ} (H : HHyp F Λ β δ κ cg cm cT N A a ε) {b μ₀ : ℝ}
    (h : Admissible F Λ κ cm cT N ε b μ₀) : ∀ j ≤ N, InDh Λ β δ κ cg cm cT ε j (traj F Λ b μ₀) := by
  intro j
  induction j with
  | zero => intro _; exact ⟨fun i hi => h.1 i (by omega), fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ j ih =>
    intro hj
    have hs := ih (by omega)
    refine ⟨fun i hi => h.1 i (by omega), fun i hi => ?_⟩
    rcases (show i = j ∨ i < j by omega) with rfl | hij
    · rw [traj_succ H b μ₀ (by omega)]; exact H.F1 i (by omega) _ hs
    · exact hs.2 i hij

/-! ### Uniqueness -/

lemma coef_h {A a : ℝ} (hΛ : 1 < Λ) (hκ1 : κ < 1) (hA : 0 ≤ A) (ha : 0 ≤ a)
    (ha0 : a ≤ a0h Λ κ A) :
    let p := Kh Λ κ A * a
    let q := Qh κ * a
    let r := 1 + p + q
    0 ≤ p ∧ 0 ≤ q ∧
      (1 + a) * p + a + A * q + a * r ≤ p * ((1 + Λ) / 2) ∧
      κ * q + a * (p + 1) + a * r ≤ q ∧
      (1 + Λ) / 2 ≤ Λ - (A * p + a + A * q + a * r) := by
  intro p q r
  have hh : 0 < Λ - 1 := sub_pos.2 hΛ
  have hk : 0 < 1 - κ := sub_pos.2 hκ1
  have hQ : 0 < Qh κ := by unfold Qh; positivity
  have hQk : Qh κ * (1 - κ) = 4 := div_mul_cancel₀ _ hk.ne'
  have hK : 0 < Kh Λ κ A := by unfold Kh; positivity
  have hKΛ : Kh Λ κ A * (Λ - 1) = 2 * (4 + A * Qh κ) := div_mul_cancel₀ _ hh.ne'
  set K := Kh Λ κ A
  set Q := Qh κ
  have h1 : a ≤ 1 := ha0.trans (min_le_left _ _)
  have h2 : a ≤ 1 / (K + Q) := ha0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have h3 : a ≤ (Λ - 1) / (2 * (A * K + A * Q + 2 + K + Q)) :=
    ha0.trans ((min_le_right _ _).trans (min_le_right _ _))
  rw [le_div_iff₀ (by positivity)] at h2
  rw [le_div_iff₀ (by positivity)] at h3
  have hp0 : 0 ≤ p := mul_nonneg hK.le ha
  have hq0 : 0 ≤ q := mul_nonneg hQ.le ha
  have hpq : p + q ≤ 1 := by simp only [p, q]; nlinarith
  have hap : a * (p + q) ≤ a := mul_le_of_le_one_right ha hpq
  have hAK : 0 ≤ A * K := mul_nonneg hA hK.le
  have hAQ : 0 ≤ A * Q := mul_nonneg hA hQ.le
  refine ⟨hp0, hq0, ?_, ?_, ?_⟩
  · -- `(1+a)p + a + Aq + ar = a (K + 2 + AQ + a(2K + Q)) ≤ a (K + 4 + AQ) = p (1+Λ)/2`
    have e : p * ((1 + Λ) / 2) = a * (K + 4 + A * Q) := by
      simp only [p]; linear_combination (a / 2) * hKΛ
    rw [e]
    have : a * (2 * p + q) ≤ 2 * a := by nlinarith
    simp only [r, p, q] at this ⊢
    nlinarith
  · have : a * (2 * p + q) ≤ 2 * a := by nlinarith
    have e : κ * q + 4 * a = q := by simp only [q]; linear_combination (-a) * hQk
    simp only [r] at this ⊢
    nlinarith
  · have hpa : A * p + a + A * q + a * r ≤ a * (A * K + A * Q + 2 + K + Q) := by
      simp only [r, p, q]
      have : a * (K * a + Q * a) ≤ a * (K + Q) := by
        have : K * a + Q * a ≤ K + Q := by nlinarith
        exact mul_le_mul_of_nonneg_left this ha
      nlinarith
    linarith

lemma unique_step {N : ℕ} {A a ε : ℝ} (H : HHyp F Λ β δ κ cg cm cT N A a ε) {p q : ℝ}
    (hp0 : 0 ≤ p) (hq0 : 0 ≤ q)
    (eg : (1 + a) * p + a + A * q + a * (1 + p + q) ≤ p * ((1 + Λ) / 2))
    (ex : κ * q + a * (p + 1) + a * (1 + p + q) ≤ q)
    (em : (1 + Λ) / 2 ≤ Λ - (A * p + a + A * q + a * (1 + p + q)))
    {j : ℕ} (hj : j < N) {t t' : Seq X} (ht : InDh Λ β δ κ cg cm cT ε j t) (ht' : InDh Λ β δ κ cg cm cT ε j t')
    (hg : |(t j).1 - (t' j).1| ≤ p * |(t j).2.1 - (t' j).2.1|)
    (hx : ‖(t j).2.2 - (t' j).2.2‖ ≤ q * |(t j).2.1 - (t' j).2.1|)
    (hh : ∀ i < j, dist3 (t i) (t' i) ≤ (1 + p + q) * |(t j).2.1 - (t' j).2.1|) :
    (1 + Λ) / 2 * |(t j).2.1 - (t' j).2.1| ≤
        |Λ * (t j).2.1 + F.m j t - (Λ * (t' j).2.1 + F.m j t')| ∧
      |F.G j t - F.G j t'| ≤ p * |Λ * (t j).2.1 + F.m j t - (Λ * (t' j).2.1 + F.m j t')| ∧
      ‖F.T j t - F.T j t'‖ ≤ q * |Λ * (t j).2.1 + F.m j t - (Λ * (t' j).2.1 + F.m j t')| ∧
      |(t j).2.1 - (t' j).2.1| ≤ |Λ * (t j).2.1 + F.m j t - (Λ * (t' j).2.1 + F.m j t')| := by
  set D := |(t j).2.1 - (t' j).2.1|
  have hD : 0 ≤ D := abs_nonneg _
  have hM : 0 ≤ (1 + p + q) * D := by positivity
  have LG := H.LG j hj t t' ht ht' _ hM hh
  have Lm := H.Lm j hj t t' ht ht' _ hM hh
  have LT := H.LT j hj t t' ht ht' _ hM hh
  have hΛ := H.hΛ; have hA := H.hA; have ha := H.ha; have hκ0 := H.hκ0
  set D' := |Λ * (t j).2.1 + F.m j t - (Λ * (t' j).2.1 + F.m j t')|
  have h1 : Λ * D ≤ D' + |F.m j t - F.m j t'| := by
    have := abs_sub (Λ * (t j).2.1 + F.m j t - (Λ * (t' j).2.1 + F.m j t')) (F.m j t - F.m j t')
    rw [show Λ * (t j).2.1 + F.m j t - (Λ * (t' j).2.1 + F.m j t') - (F.m j t - F.m j t')
      = Λ * ((t j).2.1 - (t' j).2.1) by ring, abs_mul, abs_of_pos (by linarith : 0 < Λ)] at this
    exact this
  have a1 : A * |(t j).1 - (t' j).1| ≤ A * (p * D) := mul_le_mul_of_nonneg_left hg hA
  have a2 : A * ‖(t j).2.2 - (t' j).2.2‖ ≤ A * (q * D) := mul_le_mul_of_nonneg_left hx hA
  have a3 : (1 + a) * |(t j).1 - (t' j).1| ≤ (1 + a) * (p * D) :=
    mul_le_mul_of_nonneg_left hg (by linarith)
  have a4 : κ * ‖(t j).2.2 - (t' j).2.2‖ ≤ κ * (q * D) := mul_le_mul_of_nonneg_left hx hκ0
  have a5 : a * |(t j).1 - (t' j).1| ≤ a * (p * D) := mul_le_mul_of_nonneg_left hg ha
  have b1 := mul_le_mul_of_nonneg_right em hD
  have b2 := mul_le_mul_of_nonneg_right eg hD
  have b3 := mul_le_mul_of_nonneg_right ex hD
  have hD' : (1 + Λ) / 2 * D ≤ D' := by nlinarith
  have hDD : D ≤ D' := by nlinarith
  have b4 := mul_le_mul_of_nonneg_left hD' hp0
  have b5 := mul_le_mul_of_nonneg_left hDD hq0
  refine ⟨hD', by nlinarith, by nlinarith, hDD⟩

/-- **Uniqueness**. -/
theorem admissible_unique {N : ℕ} {A a ε : ℝ} (H : HHyp F Λ β δ κ cg cm cT N A a ε)
    (ha0 : a ≤ a0h Λ κ A) {b μ₀ μ₁ : ℝ} (h₀ : Admissible F Λ κ cm cT N ε b μ₀)
    (h₁ : Admissible F Λ κ cm cT N ε b μ₁) : μ₀ = μ₁ := by
  obtain ⟨hp0, hq0, eg, ex, em⟩ := coef_h H.hΛ H.hκ1 H.hA H.ha ha0
  set p := Kh Λ κ A * a
  set q := Qh κ * a
  set t := traj F Λ b μ₀
  set t' := traj F Λ b μ₁
  have key : ∀ k ≤ N,
      |(t k).1 - (t' k).1| ≤ p * |(t k).2.1 - (t' k).2.1| ∧
      ‖(t k).2.2 - (t' k).2.2‖ ≤ q * |(t k).2.1 - (t' k).2.1| ∧
      (∀ i < k, dist3 (t i) (t' i) ≤ (1 + p + q) * |(t k).2.1 - (t' k).2.1|) ∧
      |μ₀ - μ₁| ≤ |(t k).2.1 - (t' k).2.1| := by
    intro k
    induction k with
    | zero =>
      intro _
      simp only [t, t', traj_zero, sub_self, abs_zero, norm_zero, le_refl, and_true]
      exact ⟨mul_nonneg hp0 (abs_nonneg _), mul_nonneg hq0 (abs_nonneg _),
        fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      have hkN : k < N := by omega
      obtain ⟨ig, ix, ih', iμ⟩ := ih (by omega)
      obtain ⟨s1, s2, s3, s4⟩ := unique_step H hp0 hq0 eg ex em hkN
        (admissible_InDh H h₀ k (by omega)) (admissible_InDh H h₁ k (by omega)) ig ix ih'
      have e0 := traj_succ H b μ₀ hkN
      have e1 := traj_succ H b μ₁ hkN
      simp only [t, t'] at s1 s2 s3 s4 ih' ig ix ⊢
      rw [e0, e1]
      refine ⟨s2, s3, fun i hi => ?_, iμ.trans s4⟩
      rcases (show i = k ∨ i < k by omega) with rfl | hik
      · have : dist3 (traj F Λ b μ₀ i) (traj F Λ b μ₁ i) ≤
            (1 + p + q) * |(traj F Λ b μ₀ i).2.1 - (traj F Λ b μ₁ i).2.1| := by
          unfold dist3
          nlinarith [abs_nonneg ((traj F Λ b μ₀ i).2.1 - (traj F Λ b μ₁ i).2.1)]
        exact this.trans (mul_le_mul_of_nonneg_left s4 (by positivity))
      · exact (ih' i hik).trans (mul_le_mul_of_nonneg_left s4 (by positivity))
  have := (key N le_rfl).2.2.2
  rw [h₀.2, h₁.2, sub_self, abs_zero] at this
  exact sub_eq_zero.1 (abs_nonpos_iff.1 this)

/-! ### The marginal coordinate -/

theorem ginv_admissible {N : ℕ} {A a ε : ℝ} (H : HHyp F Λ β δ κ cg cm cT N A a ε)
    (he : ε ≤ eps0u Λ β δ κ cg cm) {b μ₀ : ℝ} (h : Admissible F Λ κ cm cT N ε b μ₀) {j : ℕ} (hj : j < N) :
    |1 / (traj F Λ b μ₀ (j + 1)).1 - 1 / (traj F Λ b μ₀ j).1 + β| ≤
      2 * (1 + β) * δ * β + Cgu β cg * (traj F Λ b μ₀ j).1 := by
  have ht : InDh Λ β δ κ cg cm cT ε j (traj F Λ b μ₀) := admissible_InDh H h j (by omega)
  obtain ⟨hlow, -, -⟩ := step_D H he hj ht
  have hF1 := H.F1 j hj _ ht
  have hβ := H.hβ; have hc := H.hcg; have hδ := H.hδ
  have hs := ht.1 j le_rfl
  have hg := hs.1
  have hg1 : (traj F Λ b μ₀ j).1 ≤ 1 := hs.2.1.trans (eps_facts hc hβ (eps0u_le he)).1
  rw [traj_succ H b μ₀ hj]
  show |1 / F.G j (traj F Λ b μ₀) - 1 / (traj F Λ b μ₀ j).1 + β| ≤ _
  set g := (traj F Λ b μ₀ j).1
  set G := F.G j (traj F Λ b μ₀)
  have hG : 0 < G := by linarith
  set r := G - g - β * g ^ 2
  have e : 1 / G - 1 / g + β = (β ^ 2 * g ^ 3 + β * g * r - r) / (g * G) := by
    field_simp; ring
  rw [e, abs_div, abs_of_pos (mul_pos hg hG), div_le_iff₀ (mul_pos hg hG)]
  have hr : |r| ≤ δ * β * g ^ 2 + cg * g ^ 3 := hF1
  have hn : |β ^ 2 * g ^ 3 + β * g * r - r| ≤ β ^ 2 * g ^ 3 + (1 + β * g) * |r| := by
    calc _ ≤ |β ^ 2 * g ^ 3 + β * g * r| + |r| := abs_sub _ _
      _ ≤ |β ^ 2 * g ^ 3| + |β * g * r| + |r| := by gcongr; exact abs_add_le _ _
      _ = β ^ 2 * g ^ 3 + (1 + β * g) * |r| := by
          rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ β ^ 2 * g ^ 3), abs_mul,
            abs_of_pos (by positivity : (0:ℝ) < β * g)]; ring
  have h1 : (1 + β * g) * |r| ≤ (1 + β) * (δ * β * g ^ 2 + cg * g ^ 3) := by
    have : 1 + β * g ≤ 1 + β := by nlinarith
    exact mul_le_mul this hr (abs_nonneg _) (by linarith)
  have h2 : g ^ 2 * (5 / 6 * g) ≤ g ^ 2 * G := mul_le_mul_of_nonneg_left hlow (sq_nonneg g)
  have h2' : g * (5 / 6 * g) ≤ g * G := mul_le_mul_of_nonneg_left hlow hg.le
  have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ β ^ 2 + (1 + β) * cg)
  have h4 := mul_le_mul_of_nonneg_left h2' (by positivity : (0 : ℝ) ≤ (1 + β) * δ * β)
  have h6 : 0 ≤ (1 + β) * δ * β * g ^ 2 := by positivity
  have h7 : 0 ≤ (β ^ 2 + (1 + β) * cg) * g ^ 3 := by positivity
  have hfin : β ^ 2 * g ^ 3 + (1 + β) * (δ * β * g ^ 2 + cg * g ^ 3) ≤
      (2 * (1 + β) * δ * β + Cgu β cg * g) * (g * G) := by
    unfold Cgu
    have e1 : (2 * (1 + β) * δ * β + 2 * (β ^ 2 + (1 + β) * cg) * g) * (g * G) =
        2 * ((1 + β) * δ * β * (g * G)) + 2 * ((β ^ 2 + (1 + β) * cg) * (g ^ 2 * G)) := by ring
    have e2 : (1 + β) * δ * β * (g * (5 / 6 * g)) = 5 / 6 * ((1 + β) * δ * β * g ^ 2) := by ring
    have e3 : (β ^ 2 + (1 + β) * cg) * (g ^ 2 * (5 / 6 * g)) =
        5 / 6 * ((β ^ 2 + (1 + β) * cg) * g ^ 3) := by ring
    rw [e1]
    nlinarith
  linarith

/-! ### Continuity and shooting -/

open Classical in
variable (F Λ κ cm cT) in
/-- The admissible initial `μ₀^c(b)`. -/
def muc (N : ℕ) (ε b : ℝ) : ℝ :=
  if h : ∃ μ₀, Admissible F Λ κ cm cT N ε b μ₀ then h.choose else 0

variable (F Λ κ cm cT) in
/-- `g_N(b)` along the admissible flow. -/
def gN (N : ℕ) (ε b : ℝ) : ℝ := (traj F Λ b (muc F Λ κ cm cT N ε b) N).1

section Cont

variable {N : ℕ} {A a ε : ℝ} (H : HHyp F Λ β δ κ cg cm cT N A a ε) (he : ε ≤ eps0u Λ β δ κ cg cm)
  (hε : 0 < ε) (ha0 : a ≤ a0h Λ κ A)
include H he hε

lemma muc_spec {b : ℝ} (hb : b ∈ Ioc 0 (bmax β δ cg N ε)) : Admissible F Λ κ cm cT N ε b (muc F Λ κ cm cT N ε b) := by
  have h := exists_admissible H he hε hb
  simp only [muc, dif_pos h]
  exact h.choose_spec

include ha0

lemma eq_muc {b μ₀ : ℝ} (hb : b ∈ Ioc 0 (bmax β δ cg N ε)) (h : Admissible F Λ κ cm cT N ε b μ₀) :
    μ₀ = muc F Λ κ cm cT N ε b :=
  admissible_unique H ha0 h (muc_spec H he hε hb)

lemma phi_pos_of_gt {b : ℝ} (hb : b ∈ Ioc 0 (bmax β δ cg N ε)) {μ : ℝ} (h : muc F Λ κ cm cT N ε b < μ) :
    0 < (trajc F Λ cm b μ N).2.1 := by
  by_contra hn
  push Not at hn
  obtain ⟨μ'', hmem, hz⟩ := intermediate_value_Icc (le_max_left μ (cmu Λ cm * b))
    (continuous_phi H b).continuousOn ⟨hn, (phi_pos_of_ge H he hε hb (le_max_right _ _)).le⟩
  have := eq_muc H he hε ha0 hb (admissible_of_zero H he hε hb hz)
  linarith [hmem.1]

lemma phi_neg_of_lt {b : ℝ} (hb : b ∈ Ioc 0 (bmax β δ cg N ε)) {μ : ℝ} (h : μ < muc F Λ κ cm cT N ε b) :
    (trajc F Λ cm b μ N).2.1 < 0 := by
  by_contra hn
  push Not at hn
  obtain ⟨μ'', hmem, hz⟩ := intermediate_value_Icc (min_le_left μ (-(cmu Λ cm * b)))
    (continuous_phi H b).continuousOn ⟨(phi_neg_of_le H he hε hb (min_le_right _ _)).le, hn⟩
  have := eq_muc H he hε ha0 hb (admissible_of_zero H he hε hb hz)
  linarith [hmem.2]

theorem continuousOn_muc : ContinuousOn (muc F Λ κ cm cT N ε) (Ioc 0 (bmax β δ cg N ε)) := by
  intro b hb
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro η hη
  set μs := muc F Λ κ cm cT N ε b
  have hp := phi_pos_of_gt H he hε ha0 hb (show μs < μs + η / 2 by linarith)
  have hn := phi_neg_of_lt H he hε ha0 hb (show μs - η / 2 < μs by linarith)
  have e1 : ∀ᶠ b' in 𝓝 b, 0 < (trajc F Λ cm b' (μs + η / 2) N).2.1 :=
    (continuous_phi' H _).continuousAt.eventually (lt_mem_nhds hp)
  have e2 : ∀ᶠ b' in 𝓝 b, (trajc F Λ cm b' (μs - η / 2) N).2.1 < 0 :=
    (continuous_phi' H _).continuousAt.eventually (gt_mem_nhds hn)
  filter_upwards [eventually_mem_nhdsWithin, (e1.and e2).filter_mono nhdsWithin_le_nhds]
    with b' hb' ⟨h1, h2⟩
  obtain ⟨μ'', hmem, hz⟩ := intermediate_value_Icc (by linarith : μs - η / 2 ≤ μs + η / 2)
    (continuous_phi H b').continuousOn ⟨h2.le, h1.le⟩
  have := eq_muc H he hε ha0 hb' (admissible_of_zero H he hε hb' hz)
  rw [Real.dist_eq, ← this, abs_lt]
  constructor <;> linarith [hmem.1, hmem.2]

theorem continuousOn_gN : ContinuousOn (gN F Λ κ cm cT N ε) (Ioc 0 (bmax β δ cg N ε)) := by
  have h : ContinuousOn (fun b => (trajc F Λ cm b (muc F Λ κ cm cT N ε b) N).1) (Ioc 0 (bmax β δ cg N ε)) :=
    (continuous_fst.comp (continuous_trajc H le_rfl)).comp_continuousOn
      (continuousOn_id.prodMk (continuousOn_muc H he hε ha0))
  refine h.congr fun b hb => ?_
  simp only [gN]
  rw [trajc_eq_traj H (muc_spec H he hε hb) N le_rfl N le_rfl]

theorem shooting {b₁ b₂ : ℝ} (h₁ : b₁ ∈ Ioc 0 (bmax β δ cg N ε)) (h₂ : b₂ ∈ Ioc 0 (bmax β δ cg N ε)) {y : ℝ}
    (hy : y ∈ uIcc (gN F Λ κ cm cT N ε b₁) (gN F Λ κ cm cT N ε b₂)) :
    ∃ b ∈ uIcc b₁ b₂, gN F Λ κ cm cT N ε b = y :=
  intermediate_value_uIcc ((continuousOn_gN H he hε ha0).mono
    (ordConnected_Ioc.uIcc_subset h₁ h₂)) hy

end Cont

lemma a0h_pos (hΛ : 1 < Λ) (hκ1 : κ < 1) {A : ℝ} (hA : 0 ≤ A) : 0 < a0h Λ κ A := by
  have hh : 0 < Λ - 1 := sub_pos.2 hΛ
  have hk : 0 < 1 - κ := sub_pos.2 hκ1
  have hQ : 0 < Qh κ := by unfold Qh; positivity
  have hK : 0 < Kh Λ κ A := by unfold Kh; positivity
  unfold a0h
  exact lt_min one_pos (lt_min (by positivity) (by positivity))

/-- **Proposition `prop:C6`**: `prop:fh-flow` for history-dependent maps. -/
theorem fh_flow_hist {N : ℕ} {A a ε : ℝ} (H : HHyp F Λ β δ κ cg cm cT N A a ε) (he : ε ≤ eps0u Λ β δ κ cg cm)
    (hε : 0 < ε) (ha0 : a ≤ a0h Λ κ A) :
    (∀ b ∈ Ioc 0 (bmax β δ cg N ε), ∃! μ₀, Admissible F Λ κ cm cT N ε b μ₀) ∧
    (∀ b μ₀, Admissible F Λ κ cm cT N ε b μ₀ → ∀ j < N,
      |1 / (traj F Λ b μ₀ (j + 1)).1 - 1 / (traj F Λ b μ₀ j).1 + β| ≤
        2 * (1 + β) * δ * β + Cgu β cg * (traj F Λ b μ₀ j).1) ∧
    ContinuousOn (muc F Λ κ cm cT N ε) (Ioc 0 (bmax β δ cg N ε)) ∧ ContinuousOn (gN F Λ κ cm cT N ε) (Ioc 0 (bmax β δ cg N ε)) := by
  refine ⟨fun b hb => ?_, fun b μ₀ h j hj => ginv_admissible H he h hj,
    continuousOn_muc H he hε ha0, continuousOn_gN H he hε ha0⟩
  obtain ⟨μ₀, h⟩ := exists_admissible H he hε hb
  exact ⟨μ₀, h, fun μ₁ h₁ => admissible_unique H ha0 h₁ h⟩

end Hist

end Flow2
