import Mathlib

/-!
# An abstract finite-horizon flow (`h02uv-outline.tex`, Proposition `prop:fh-flow`)

A flow with one marginal coordinate `g`, one relevant coordinate `μ` and irrelevant coordinates
`x ∈ X_j`:

  `g_{j+1} = G_j(s_j)`,  `μ_{j+1} = Λ μ_j + m_j(s_j)`,  `x_{j+1} = T_j(s_j)`,  `s_j = (g_j, μ_j, x_j)`,

started at `(b, μ₀, 0)`. On the domain `D = {0 < g ≤ ε, |μ| ≤ c_μ g, ‖x‖ ≤ c_x g³}` assume

* (F1) `|G_j(s) - g + β g²| ≤ c g³`, (F2) `|m_j(s)| ≤ c g`, (F3) `‖T_j(s)‖ ≤ κ ‖x‖ + c g³`,
* (L) Lipschitz bounds with a small constant `a` for the weak dependences and `A` otherwise.

Results:
* `exists_admissible` (existence, by clamping and the intermediate value theorem);
* `admissible_unique` (uniqueness, by the Lipschitz bounds);
* `ginv_step` (`|1/g_{j+1} - 1/g_j - β| ≤ C g_j`);
* `continuous_mu0`, `continuous_gN`, `shooting` (continuity in `b` and the shooting argument).
-/

open Set Filter Topology

noncomputable section

namespace Flow2

variable {X : ℕ → Type*} [∀ j, NormedAddCommGroup (X j)]

/-! ### The data -/

/-- The data of the flow: `G_j, m_j : ℝ × ℝ × X_j → ℝ` and `T_j : ℝ × ℝ × X_j → X_{j+1}`. -/
structure FHData (X : ℕ → Type*) [∀ j, NormedAddCommGroup (X j)] where
  G : ∀ j, ℝ × ℝ × X j → ℝ
  m : ∀ j, ℝ × ℝ × X j → ℝ
  T : ∀ j, ℝ × ℝ × X j → X (j + 1)

variable (F : FHData X) (Λ β κ c : ℝ)

/-- `c_μ = 2c/(Λ-1)`. -/
def cmu : ℝ := 2 * c / (Λ - 1)

/-- `c_x = 2c/(1-κ)`. -/
def cx : ℝ := 2 * c / (1 - κ)

/-- The domain `D_ε`. -/
def InD (ε : ℝ) {j : ℕ} (s : ℝ × ℝ × X j) : Prop :=
  0 < s.1 ∧ s.1 ≤ ε ∧ |s.2.1| ≤ cmu Λ c * s.1 ∧ ‖s.2.2‖ ≤ cx κ c * s.1 ^ 3

/-- The hypotheses (F1)–(F3), (L) and continuity, for `j < N`. -/
structure FHHyp (N : ℕ) (A a ε : ℝ) : Prop where
  hΛ : 1 < Λ
  hβ : 0 < β
  hκ0 : 0 ≤ κ
  hκ1 : κ < 1
  hc : 0 < c
  hA : 0 ≤ A
  ha : 0 ≤ a
  contG : ∀ j < N, Continuous (F.G j)
  contm : ∀ j < N, Continuous (F.m j)
  contT : ∀ j < N, Continuous (F.T j)
  F1 : ∀ j < N, ∀ s : ℝ × ℝ × X j, InD Λ κ c ε s → |F.G j s - s.1 + β * s.1 ^ 2| ≤ c * s.1 ^ 3
  F2 : ∀ j < N, ∀ s : ℝ × ℝ × X j, InD Λ κ c ε s → |F.m j s| ≤ c * s.1
  F3 : ∀ j < N, ∀ s : ℝ × ℝ × X j, InD Λ κ c ε s → ‖F.T j s‖ ≤ κ * ‖s.2.2‖ + c * s.1 ^ 3
  LG : ∀ j < N, ∀ s s' : ℝ × ℝ × X j, InD Λ κ c ε s → InD Λ κ c ε s' →
    |F.G j s - F.G j s'| ≤ (1 + a) * |s.1 - s'.1| + a * |s.2.1 - s'.2.1| + A * ‖s.2.2 - s'.2.2‖
  Lm : ∀ j < N, ∀ s s' : ℝ × ℝ × X j, InD Λ κ c ε s → InD Λ κ c ε s' →
    |F.m j s - F.m j s'| ≤ A * |s.1 - s'.1| + a * |s.2.1 - s'.2.1| + A * ‖s.2.2 - s'.2.2‖
  LT : ∀ j < N, ∀ s s' : ℝ × ℝ × X j, InD Λ κ c ε s → InD Λ κ c ε s' →
    ‖F.T j s - F.T j s'‖ ≤ κ * ‖s.2.2 - s'.2.2‖ + a * (|s.1 - s'.1| + |s.2.1 - s'.2.1|)

/-- `ε₀ = min(1, β/c, (1-κ)/(6(β+c)))`. -/
def eps0 : ℝ := min 1 (min (β / c) ((1 - κ) / (6 * (β + c))))

/-- An auxiliary constant: `K₁ = 4(1 + 2A/(1-κ))/(Λ-1)`. -/
def K1 (A : ℝ) : ℝ := 4 * (1 + 2 * A / (1 - κ)) / (Λ - 1)

/-- `a₀ = min(1/K₁, (Λ-1)/(2(1 + A K₁ + 2A/(1-κ))))`. -/
def a0 (A : ℝ) : ℝ :=
  min (1 / K1 Λ κ A) ((Λ - 1) / (2 * (1 + A * K1 Λ κ A + 2 * A / (1 - κ))))

/-- The constant of the `g`-asymptotics, `C = 2(β² + βc + c)`. -/
def Cg : ℝ := 2 * (β ^ 2 + β * c + c)

/-! ### The flow and the clamped flow -/

/-- The flow started at `(b, μ₀, 0)`. -/
def traj (b μ₀ : ℝ) : (j : ℕ) → ℝ × ℝ × X j
  | 0 => (b, μ₀, 0)
  | j + 1 =>
    let s := traj b μ₀ j
    (F.G j s, Λ * s.2.1 + F.m j s, F.T j s)

/-- `clamp r v = max (-r) (min r v)`. -/
def clamp (r v : ℝ) : ℝ := max (-r) (min r v)

/-- The clamped flow: `μ` is clamped to `[-c_μ g, c_μ g]` at every step (also at `j = 0`). -/
def trajc (b μ₀ : ℝ) : (j : ℕ) → ℝ × ℝ × X j
  | 0 => (b, clamp (cmu Λ c * b) μ₀, 0)
  | j + 1 =>
    let s := trajc b μ₀ j
    (F.G j s, clamp (cmu Λ c * F.G j s) (Λ * s.2.1 + F.m j s), F.T j s)

/-- Admissible initial data: the trajectory stays in `D` up to `N` and `μ_N = 0`. -/
def Admissible (N : ℕ) (ε b μ₀ : ℝ) : Prop :=
  (∀ j ≤ N, InD Λ κ c ε (traj F Λ b μ₀ j)) ∧ (traj F Λ b μ₀ N).2.1 = 0

/-! ### Elementary facts -/

variable {F Λ β κ c}

lemma traj_zero (b μ₀ : ℝ) : traj F Λ b μ₀ 0 = (b, μ₀, 0) := rfl

lemma traj_succ (b μ₀ : ℝ) (j : ℕ) :
    traj F Λ b μ₀ (j + 1) = (F.G j (traj F Λ b μ₀ j),
      Λ * (traj F Λ b μ₀ j).2.1 + F.m j (traj F Λ b μ₀ j), F.T j (traj F Λ b μ₀ j)) := rfl

lemma trajc_zero (b μ₀ : ℝ) : trajc F Λ c b μ₀ 0 = (b, clamp (cmu Λ c * b) μ₀, 0) := rfl

lemma trajc_succ (b μ₀ : ℝ) (j : ℕ) :
    trajc F Λ c b μ₀ (j + 1) = (F.G j (trajc F Λ c b μ₀ j),
      clamp (cmu Λ c * F.G j (trajc F Λ c b μ₀ j))
        (Λ * (trajc F Λ c b μ₀ j).2.1 + F.m j (trajc F Λ c b μ₀ j)),
      F.T j (trajc F Λ c b μ₀ j)) := rfl

lemma cmu_mul (hΛ : 1 < Λ) : cmu Λ c * (Λ - 1) = 2 * c :=
  div_mul_cancel₀ _ (sub_pos.2 hΛ).ne'

lemma cx_mul (hκ : κ < 1) : cx κ c * (1 - κ) = 2 * c :=
  div_mul_cancel₀ _ (sub_pos.2 hκ).ne'

lemma cmu_pos (hΛ : 1 < Λ) (hc : 0 < c) : 0 < cmu Λ c :=
  div_pos (by linarith) (sub_pos.2 hΛ)

lemma cx_pos (hκ : κ < 1) (hc : 0 < c) : 0 < cx κ c :=
  div_pos (by linarith) (sub_pos.2 hκ)

lemma eps_facts (hc : 0 < c) (hβ : 0 < β) {ε : ℝ} (he : ε ≤ eps0 β κ c) :
    ε ≤ 1 ∧ c * ε ≤ β ∧ 6 * ((β + c) * ε) ≤ 1 - κ := by
  have h1 : ε ≤ 1 := he.trans (min_le_left _ _)
  have h2 : ε ≤ β / c := he.trans ((min_le_right _ _).trans (min_le_left _ _))
  have h3 : ε ≤ (1 - κ) / (6 * (β + c)) :=
    he.trans ((min_le_right _ _).trans (min_le_right _ _))
  rw [le_div_iff₀ hc] at h2
  rw [le_div_iff₀ (by linarith)] at h3
  exact ⟨h1, by linarith, by linarith⟩

lemma abs_clamp_le {r : ℝ} (v : ℝ) (hr : 0 ≤ r) : |clamp r v| ≤ r :=
  abs_le.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

lemma clamp_of_abs_le {r v : ℝ} (h : |v| ≤ r) : clamp r v = v := by
  obtain ⟨h1, h2⟩ := abs_le.1 h
  unfold clamp; rw [min_eq_right h2, max_eq_right h1]

lemma clamp_of_le {r v : ℝ} (hr : 0 ≤ r) (h : r ≤ v) : clamp r v = r := by
  unfold clamp; rw [min_eq_left h, max_eq_right (by linarith)]

lemma clamp_of_le' {r v : ℝ} (hr : 0 ≤ r) (h : v ≤ -r) : clamp r v = -r := by
  unfold clamp; rw [min_eq_right (by linarith), max_eq_left h]

lemma clamp_eq_of_abs_lt {r v : ℝ} (h : |clamp r v| < r) : clamp r v = v := by
  have hr : 0 < r := lt_of_le_of_lt (abs_nonneg _) h
  rcases le_total r v with hv | hv
  · rw [clamp_of_le hr.le hv, abs_of_pos hr] at h; exact absurd h (lt_irrefl _)
  rcases le_total v (-r) with hv' | hv'
  · rw [clamp_of_le' hr.le hv', abs_neg, abs_of_pos hr] at h; exact absurd h (lt_irrefl _)
  exact clamp_of_abs_le (abs_le.2 ⟨hv', hv⟩)

lemma continuous_clamp : Continuous (fun p : ℝ × ℝ => clamp p.1 p.2) :=
  continuous_fst.neg.max (continuous_fst.min continuous_snd)

/-! ### One step -/

section Step

variable {N : ℕ} {A a ε : ℝ}

/-- One step maps `D` into `D` (up to the `μ`-coordinate): `5g/6 ≤ g' ≤ g` and
`‖x'‖ ≤ c_x g'³`. -/
lemma step_D (H : FHHyp F Λ β κ c N A a ε) (he : ε ≤ eps0 β κ c) {j : ℕ} (hj : j < N)
    {s : ℝ × ℝ × X j} (hs : InD Λ κ c ε s) :
    5 / 6 * s.1 ≤ F.G j s ∧ F.G j s ≤ s.1 ∧ ‖F.T j s‖ ≤ cx κ c * F.G j s ^ 3 := by
  obtain ⟨he1, he2, he3⟩ := eps_facts H.hc H.hβ he
  have hF1 := abs_le.1 (H.F1 j hj s hs)
  have hF3 := H.F3 j hj s hs
  obtain ⟨hg, hgε, -, hx⟩ := hs
  have hβ := H.hβ; have hc := H.hc; have hκ0 := H.hκ0
  have hcx := cx_mul (c := c) H.hκ1
  have hcx0 := (cx_pos H.hκ1 hc).le
  set g := s.1
  set G := F.G j s
  set t := (β + c) * ε with htdef
  have hg1 : g ≤ 1 := hgε.trans he1
  have f1 : g ^ 2 ≤ ε * g := by rw [sq]; exact mul_le_mul_of_nonneg_right hgε hg.le
  have f2 : g ^ 3 ≤ g ^ 2 := pow_le_pow_of_le_one hg.le hg1 (by norm_num)
  have f3 : β * g ^ 2 ≤ β * (ε * g) := mul_le_mul_of_nonneg_left f1 hβ.le
  have f4 : c * g ^ 3 ≤ c * (ε * g) := mul_le_mul_of_nonneg_left (f2.trans f1) hc.le
  have ht0 : 0 ≤ t := mul_nonneg (by linarith) (by linarith)
  have ht : t ≤ 1 / 6 := by linarith
  have f5 : t * g ≤ 1 / 6 * g := mul_le_mul_of_nonneg_right ht hg.le
  have f6 : t * g = β * (ε * g) + c * (ε * g) := by rw [htdef]; ring
  have hG' : g * (1 - t) ≤ G := by linarith
  have hlow : 5 / 6 * g ≤ G := by linarith
  have hcg : c * g ≤ β := (mul_le_mul_of_nonneg_left hgε hc.le).trans he2
  have f7 : c * g * g ^ 2 ≤ β * g ^ 2 := mul_le_mul_of_nonneg_right hcg (sq_nonneg g)
  have hup : G ≤ g := by nlinarith
  refine ⟨hlow, hup, ?_⟩
  have hc1 : g ^ 3 * (1 - 3 * t) ≤ G ^ 3 := by
    have h1 : (g * (1 - t)) ^ 3 ≤ G ^ 3 :=
      pow_le_pow_left₀ (mul_nonneg hg.le (by linarith)) hG' 3
    have h2 : 0 ≤ g ^ 3 * (t ^ 2 * (3 - t)) :=
      mul_nonneg (pow_nonneg hg.le 3) (mul_nonneg (sq_nonneg t) (by linarith))
    nlinarith
  have k1 : 0 ≤ cx κ c * g ^ 3 * ((1 - κ) - 6 * t) :=
    mul_nonneg (mul_nonneg hcx0 (pow_nonneg hg.le 3)) (by linarith)
  have k2 : cx κ c * (g ^ 3 * (1 - 3 * t)) ≤ cx κ c * G ^ 3 :=
    mul_le_mul_of_nonneg_left hc1 hcx0
  have k3 : cx κ c * (1 - κ) * g ^ 3 = 2 * c * g ^ 3 := by rw [hcx]
  have k4 : κ * ‖s.2.2‖ ≤ κ * (cx κ c * g ^ 3) := mul_le_mul_of_nonneg_left hx hκ0
  nlinarith

/-- If `s ∈ D` and `|μ'| ≤ c_μ G(s)`, then `(G(s), μ', T(s)) ∈ D`. -/
lemma step_InD (H : FHHyp F Λ β κ c N A a ε) (he : ε ≤ eps0 β κ c) {j : ℕ} (hj : j < N)
    {s : ℝ × ℝ × X j} (hs : InD Λ κ c ε s) {μ' : ℝ} (hμ : |μ'| ≤ cmu Λ c * F.G j s) :
    InD Λ κ c ε ((F.G j s, μ', F.T j s) : ℝ × ℝ × X (j + 1)) := by
  obtain ⟨h1, h2, h3⟩ := step_D H he hj hs
  have := hs.1
  exact ⟨by show 0 < F.G j s; linarith, h2.trans hs.2.1, hμ, h3⟩

/-- The top of the `μ`-boundary is absorbing. -/
lemma top_step (H : FHHyp F Λ β κ c N A a ε) (he : ε ≤ eps0 β κ c) {j : ℕ} (hj : j < N)
    {s : ℝ × ℝ × X j} (hs : InD Λ κ c ε s) (htop : s.2.1 = cmu Λ c * s.1) :
    clamp (cmu Λ c * F.G j s) (Λ * s.2.1 + F.m j s) = cmu Λ c * F.G j s := by
  obtain ⟨h1, h2, -⟩ := step_D H he hj hs
  have hm := (abs_le.1 (H.F2 j hj s hs)).1
  have hcm := cmu_mul (c := c) H.hΛ
  have hcpos := cmu_pos H.hΛ H.hc
  have hg := hs.1
  have hcg := mul_pos H.hc hg
  apply clamp_of_le (mul_nonneg hcpos.le (by linarith))
  rw [htop]
  have : cmu Λ c * F.G j s ≤ cmu Λ c * s.1 := mul_le_mul_of_nonneg_left h2 hcpos.le
  have e : cmu Λ c * s.1 * Λ = cmu Λ c * s.1 + 2 * c * s.1 := by linear_combination s.1 * hcm
  linarith

/-- The bottom of the `μ`-boundary is absorbing. -/
lemma bot_step (H : FHHyp F Λ β κ c N A a ε) (he : ε ≤ eps0 β κ c) {j : ℕ} (hj : j < N)
    {s : ℝ × ℝ × X j} (hs : InD Λ κ c ε s) (hbot : s.2.1 = -(cmu Λ c * s.1)) :
    clamp (cmu Λ c * F.G j s) (Λ * s.2.1 + F.m j s) = -(cmu Λ c * F.G j s) := by
  obtain ⟨h1, h2, -⟩ := step_D H he hj hs
  have hm := (abs_le.1 (H.F2 j hj s hs)).2
  have hcm := cmu_mul (c := c) H.hΛ
  have hcpos := cmu_pos H.hΛ H.hc
  have hg := hs.1
  have hcg := mul_pos H.hc hg
  apply clamp_of_le' (mul_nonneg hcpos.le (by linarith))
  rw [hbot]
  have : cmu Λ c * F.G j s ≤ cmu Λ c * s.1 := mul_le_mul_of_nonneg_left h2 hcpos.le
  have e : cmu Λ c * s.1 * Λ = cmu Λ c * s.1 + 2 * c * s.1 := by linear_combination s.1 * hcm
  linarith

/-! ### The clamped flow -/

variable (H : FHHyp F Λ β κ c N A a ε) (he : ε ≤ eps0 β κ c)
include H he

/-- The clamped flow stays in `D`. -/
lemma trajc_InD {b : ℝ} (hb : b ∈ Ioc 0 ε) (μ₀ : ℝ) :
    ∀ j ≤ N, InD Λ κ c ε (trajc F Λ c b μ₀ j) := by
  intro j
  induction j with
  | zero =>
    intro _
    exact ⟨hb.1, hb.2, abs_clamp_le _ (mul_nonneg (cmu_pos H.hΛ H.hc).le hb.1.le),
      by simp only [trajc_zero, norm_zero]; exact mul_nonneg (cx_pos H.hκ1 H.hc).le (by
        have := hb.1; positivity)⟩
  | succ j ih =>
    intro hj
    have hs := ih (by omega)
    obtain ⟨h1, -, -⟩ := step_D H he (by omega : j < N) hs
    rw [trajc_succ]
    exact step_InD H he (by omega) hs
      (abs_clamp_le _ (mul_nonneg (cmu_pos H.hΛ H.hc).le (by linarith [hs.1])))

omit he in
/-- The clamped flow is continuous in `(b, μ₀)`. -/
lemma continuous_trajc : ∀ j ≤ N, Continuous (fun p : ℝ × ℝ => trajc F Λ c p.1 p.2 j) := by
  intro j
  induction j with
  | zero =>
    intro _
    exact continuous_fst.prodMk ((continuous_clamp.comp
      ((continuous_const.mul continuous_fst).prodMk continuous_snd)).prodMk continuous_const)
  | succ j ih =>
    intro hj
    have h := ih (by omega)
    have hG := (H.contG j (by omega)).comp h
    have hm := (H.contm j (by omega)).comp h
    have hT := (H.contT j (by omega)).comp h
    exact hG.prodMk ((continuous_clamp.comp ((continuous_const.mul hG).prodMk
      ((continuous_const.mul (continuous_fst.comp (continuous_snd.comp h))).add hm))).prodMk hT)

/-- Once on the top of the boundary, the clamped flow stays there. -/
lemma trajc_top {b : ℝ} (hb : b ∈ Ioc 0 ε) (μ₀ : ℝ) {k : ℕ}
    (hk : (trajc F Λ c b μ₀ k).2.1 = cmu Λ c * (trajc F Λ c b μ₀ k).1) :
    ∀ j, k ≤ j → j ≤ N → (trajc F Λ c b μ₀ j).2.1 = cmu Λ c * (trajc F Λ c b μ₀ j).1 := by
  intro j
  induction j with
  | zero => intro h _; obtain rfl : k = 0 := by omega
            exact hk
  | succ j ih =>
    intro h1 h2
    rcases (show k = j + 1 ∨ k ≤ j by omega) with rfl | h1'
    · exact hk
    exact top_step H he (by omega) (trajc_InD H he hb μ₀ j (by omega)) (ih h1' (by omega))

/-- Once on the bottom of the boundary, the clamped flow stays there. -/
lemma trajc_bot {b : ℝ} (hb : b ∈ Ioc 0 ε) (μ₀ : ℝ) {k : ℕ}
    (hk : (trajc F Λ c b μ₀ k).2.1 = -(cmu Λ c * (trajc F Λ c b μ₀ k).1)) :
    ∀ j, k ≤ j → j ≤ N → (trajc F Λ c b μ₀ j).2.1 = -(cmu Λ c * (trajc F Λ c b μ₀ j).1) := by
  intro j
  induction j with
  | zero => intro h _; obtain rfl : k = 0 := by omega
            exact hk
  | succ j ih =>
    intro h1 h2
    rcases (show k = j + 1 ∨ k ≤ j by omega) with rfl | h1'
    · exact hk
    exact bot_step H he (by omega) (trajc_InD H he hb μ₀ j (by omega)) (ih h1' (by omega))

/-- If the clamped `μ_N` vanishes, the clamped flow never touches the boundary. -/
lemma trajc_strict {b : ℝ} (hb : b ∈ Ioc 0 ε) {μ₀ : ℝ} (h0 : (trajc F Λ c b μ₀ N).2.1 = 0) :
    ∀ k ≤ N, |(trajc F Λ c b μ₀ k).2.1| < cmu Λ c * (trajc F Λ c b μ₀ k).1 := by
  intro k hk
  have hD := trajc_InD H he hb μ₀ k hk
  have hN := trajc_InD H he hb μ₀ N le_rfl
  have hcp := cmu_pos H.hΛ H.hc
  have hpos : 0 < cmu Λ c * (trajc F Λ c b μ₀ N).1 := mul_pos hcp hN.1
  rcases hD.2.2.1.lt_or_eq with h | h
  · exact h
  exfalso
  rcases (abs_eq (mul_nonneg hcp.le hD.1.le)).1 h with h' | h'
  · have := trajc_top H he hb μ₀ h' N hk le_rfl; linarith
  · have := trajc_bot H he hb μ₀ h' N hk le_rfl; linarith

/-- A zero of the clamped `μ_N` is admissible initial data. -/
lemma admissible_of_zero {b : ℝ} (hb : b ∈ Ioc 0 ε) {μ₀ : ℝ}
    (h0 : (trajc F Λ c b μ₀ N).2.1 = 0) : Admissible F Λ κ c N ε b μ₀ := by
  have hs := trajc_strict H he hb h0
  have e : ∀ k ≤ N, trajc F Λ c b μ₀ k = traj F Λ b μ₀ k := by
    intro k
    induction k with
    | zero =>
      intro _
      have h := hs 0 (Nat.zero_le _)
      rw [trajc_zero, traj_zero, clamp_eq_of_abs_lt (r := cmu Λ c * b) h]
    | succ k ih =>
      intro hk
      have e := ih (by omega)
      have h := hs (k + 1) hk
      rw [trajc_succ] at h ⊢
      rw [clamp_eq_of_abs_lt h, e, traj_succ]
  refine ⟨fun k hk => e k hk ▸ trajc_InD H he hb μ₀ k hk, ?_⟩
  rw [← e N le_rfl]; exact h0

omit H he in
/-- Along admissible initial data the clamped flow is the flow. -/
lemma trajc_eq_traj {b μ₀ : ℝ} (h : Admissible F Λ κ c N ε b μ₀) :
    ∀ k ≤ N, trajc F Λ c b μ₀ k = traj F Λ b μ₀ k := by
  intro k
  induction k with
  | zero =>
    intro _
    have h0 : |μ₀| ≤ cmu Λ c * b := (h.1 0 (Nat.zero_le _)).2.2.1
    rw [trajc_zero, traj_zero, clamp_of_abs_le h0]
  | succ k ih =>
    intro hk
    have h1 : |Λ * (traj F Λ b μ₀ k).2.1 + F.m k (traj F Λ b μ₀ k)| ≤
        cmu Λ c * F.G k (traj F Λ b μ₀ k) := (h.1 (k + 1) hk).2.2.1
    rw [trajc_succ, ih (by omega), clamp_of_abs_le h1, traj_succ]

/-- If `μ₀ ≥ c_μ b`, the clamped `μ_N` is positive. -/
lemma phi_pos_of_ge {b : ℝ} (hb : b ∈ Ioc 0 ε) {μ₀ : ℝ} (h : cmu Λ c * b ≤ μ₀) :
    0 < (trajc F Λ c b μ₀ N).2.1 := by
  have hcp := cmu_pos H.hΛ H.hc
  have h0 : (trajc F Λ c b μ₀ 0).2.1 = cmu Λ c * (trajc F Λ c b μ₀ 0).1 :=
    clamp_of_le (mul_nonneg hcp.le hb.1.le) h
  rw [trajc_top H he hb μ₀ h0 N (Nat.zero_le _) le_rfl]
  exact mul_pos hcp (trajc_InD H he hb μ₀ N le_rfl).1

/-- If `μ₀ ≤ -c_μ b`, the clamped `μ_N` is negative. -/
lemma phi_neg_of_le {b : ℝ} (hb : b ∈ Ioc 0 ε) {μ₀ : ℝ} (h : μ₀ ≤ -(cmu Λ c * b)) :
    (trajc F Λ c b μ₀ N).2.1 < 0 := by
  have hcp := cmu_pos H.hΛ H.hc
  have h0 : (trajc F Λ c b μ₀ 0).2.1 = -(cmu Λ c * (trajc F Λ c b μ₀ 0).1) :=
    clamp_of_le' (mul_nonneg hcp.le hb.1.le) h
  rw [trajc_bot H he hb μ₀ h0 N (Nat.zero_le _) le_rfl]
  have := mul_pos hcp (trajc_InD H he hb μ₀ N le_rfl).1
  linarith

omit he in
lemma continuous_phi (b : ℝ) : Continuous (fun μ => (trajc F Λ c b μ N).2.1) :=
  (continuous_fst.comp (continuous_snd.comp (continuous_trajc H N le_rfl))).comp
    (continuous_const.prodMk continuous_id)

omit he in
lemma continuous_phi' (μ : ℝ) : Continuous (fun b => (trajc F Λ c b μ N).2.1) :=
  (continuous_fst.comp (continuous_snd.comp (continuous_trajc H N le_rfl))).comp
    (continuous_id.prodMk continuous_const)

/-! ### Existence -/

/-- **Existence** (Proposition `prop:fh-flow` (i)): for `b ∈ (0, ε]` there is admissible initial
data. -/
theorem exists_admissible {b : ℝ} (hb : b ∈ Ioc 0 ε) : ∃ μ₀, Admissible F Λ κ c N ε b μ₀ := by
  have hr : 0 ≤ cmu Λ c * b := mul_nonneg (cmu_pos H.hΛ H.hc).le hb.1.le
  obtain ⟨μ₀, -, hμ⟩ := intermediate_value_Icc (by linarith : -(cmu Λ c * b) ≤ cmu Λ c * b)
    (continuous_phi H b).continuousOn
    ⟨(phi_neg_of_le H he hb le_rfl).le, (phi_pos_of_ge H he hb le_rfl).le⟩
  exact ⟨μ₀, admissible_of_zero H he hb hμ⟩

end Step

/-! ### Uniqueness -/

lemma coef {A a : ℝ} (hΛ : 1 < Λ) (hκ1 : κ < 1) (hA : 0 ≤ A) (ha : 0 ≤ a)
    (ha0 : a ≤ a0 Λ κ A) :
    0 ≤ K1 Λ κ A * a ∧ 0 ≤ 2 * a / (1 - κ) ∧
      (1 + a) * (K1 Λ κ A * a) + a + A * (2 * a / (1 - κ)) ≤ K1 Λ κ A * a * ((1 + Λ) / 2) ∧
      κ * (2 * a / (1 - κ)) + a * (K1 Λ κ A * a + 1) ≤ 2 * a / (1 - κ) ∧
      (1 + Λ) / 2 ≤ Λ - (A * (K1 Λ κ A * a) + a + A * (2 * a / (1 - κ))) := by
  have hh : 0 < Λ - 1 := sub_pos.2 hΛ
  have hk : 0 < 1 - κ := sub_pos.2 hκ1
  have hK : 0 < K1 Λ κ A := by unfold K1; positivity
  have hM : 0 < 1 + A * K1 Λ κ A + 2 * A / (1 - κ) := by positivity
  have h1 : a ≤ 1 / K1 Λ κ A := ha0.trans (min_le_left _ _)
  have h2 : a ≤ (Λ - 1) / (2 * (1 + A * K1 Λ κ A + 2 * A / (1 - κ))) :=
    ha0.trans (min_le_right _ _)
  rw [le_div_iff₀ hK] at h1
  rw [le_div_iff₀ (by positivity)] at h2
  set p := K1 Λ κ A * a with hp
  set q := 2 * a / (1 - κ) with hq
  have hp1 : p ≤ 1 := by rw [hp]; linarith
  have hp0 : 0 ≤ p := mul_nonneg hK.le ha
  have hq0 : 0 ≤ q := div_nonneg (by linarith) hk.le
  have hqk : q * (1 - κ) = 2 * a := div_mul_cancel₀ _ hk.ne'
  have hpK : p * (Λ - 1) = 4 * a + 4 * A * q := by
    rw [hp, hq]; unfold K1; field_simp
  have hAq : A * p + a + A * q = a * (1 + A * K1 Λ κ A + 2 * A / (1 - κ)) := by
    rw [hp, hq]; ring
  have hap : a * p ≤ a := mul_le_of_le_one_right ha hp1
  have hAq0 : 0 ≤ A * q := mul_nonneg hA hq0
  refine ⟨hp0, hq0, by nlinarith, by nlinarith, by nlinarith⟩

/-- One step of the uniqueness argument: the `μ`-difference expands by `(1+Λ)/2` and keeps
dominating the `g`- and `x`-differences. -/
lemma unique_step {N : ℕ} {A a ε : ℝ} (H : FHHyp F Λ β κ c N A a ε) {p q : ℝ}
    (hp0 : 0 ≤ p) (hq0 : 0 ≤ q)
    (eg : (1 + a) * p + a + A * q ≤ p * ((1 + Λ) / 2))
    (ex : κ * q + a * (p + 1) ≤ q)
    (em : (1 + Λ) / 2 ≤ Λ - (A * p + a + A * q))
    {j : ℕ} (hj : j < N) {s s' : ℝ × ℝ × X j} (hs : InD Λ κ c ε s) (hs' : InD Λ κ c ε s')
    (hg : |s.1 - s'.1| ≤ p * |s.2.1 - s'.2.1|) (hx : ‖s.2.2 - s'.2.2‖ ≤ q * |s.2.1 - s'.2.1|) :
    (1 + Λ) / 2 * |s.2.1 - s'.2.1| ≤ |Λ * s.2.1 + F.m j s - (Λ * s'.2.1 + F.m j s')| ∧
    |F.G j s - F.G j s'| ≤ p * |Λ * s.2.1 + F.m j s - (Λ * s'.2.1 + F.m j s')| ∧
    ‖F.T j s - F.T j s'‖ ≤ q * |Λ * s.2.1 + F.m j s - (Λ * s'.2.1 + F.m j s')| := by
  have LG := H.LG j hj s s' hs hs'
  have Lm := H.Lm j hj s s' hs hs'
  have LT := H.LT j hj s s' hs hs'
  have hΛ := H.hΛ; have hA := H.hA; have ha := H.ha; have hκ0 := H.hκ0
  set D := |s.2.1 - s'.2.1|
  set D' := |Λ * s.2.1 + F.m j s - (Λ * s'.2.1 + F.m j s')|
  have hD : 0 ≤ D := abs_nonneg _
  have h1 : Λ * D ≤ D' + |F.m j s - F.m j s'| := by
    have := abs_sub (Λ * s.2.1 + F.m j s - (Λ * s'.2.1 + F.m j s')) (F.m j s - F.m j s')
    rw [show Λ * s.2.1 + F.m j s - (Λ * s'.2.1 + F.m j s') - (F.m j s - F.m j s')
      = Λ * (s.2.1 - s'.2.1) by ring, abs_mul, abs_of_pos (by linarith : 0 < Λ)] at this
    exact this
  have a1 : A * |s.1 - s'.1| ≤ A * (p * D) := mul_le_mul_of_nonneg_left hg hA
  have a2 : A * ‖s.2.2 - s'.2.2‖ ≤ A * (q * D) := mul_le_mul_of_nonneg_left hx hA
  have a3 : (1 + a) * |s.1 - s'.1| ≤ (1 + a) * (p * D) := mul_le_mul_of_nonneg_left hg (by linarith)
  have a4 : κ * ‖s.2.2 - s'.2.2‖ ≤ κ * (q * D) := mul_le_mul_of_nonneg_left hx hκ0
  have a5 : a * |s.1 - s'.1| ≤ a * (p * D) := mul_le_mul_of_nonneg_left hg ha
  have b1 := mul_le_mul_of_nonneg_right em hD
  have b2 := mul_le_mul_of_nonneg_right eg hD
  have b3 := mul_le_mul_of_nonneg_right ex hD
  have hD' : (1 + Λ) / 2 * D ≤ D' := by nlinarith
  have hDD : D ≤ D' := by nlinarith
  have b4 := mul_le_mul_of_nonneg_left hD' hp0
  have b5 := mul_le_mul_of_nonneg_left hDD hq0
  refine ⟨hD', by nlinarith, by nlinarith⟩

/-- **Uniqueness** (Proposition `prop:fh-flow` (i)). -/
theorem admissible_unique {N : ℕ} {A a ε : ℝ} (H : FHHyp F Λ β κ c N A a ε)
    (ha0 : a ≤ a0 Λ κ A) {b μ₀ μ₁ : ℝ} (h₀ : Admissible F Λ κ c N ε b μ₀)
    (h₁ : Admissible F Λ κ c N ε b μ₁) : μ₀ = μ₁ := by
  obtain ⟨hp0, hq0, eg, ex, em⟩ := coef H.hΛ H.hκ1 H.hA H.ha ha0
  have key : ∀ k ≤ N,
      |(traj F Λ b μ₀ k).1 - (traj F Λ b μ₁ k).1| ≤
        K1 Λ κ A * a * |(traj F Λ b μ₀ k).2.1 - (traj F Λ b μ₁ k).2.1| ∧
      ‖(traj F Λ b μ₀ k).2.2 - (traj F Λ b μ₁ k).2.2‖ ≤
        2 * a / (1 - κ) * |(traj F Λ b μ₀ k).2.1 - (traj F Λ b μ₁ k).2.1| ∧
      |μ₀ - μ₁| ≤ |(traj F Λ b μ₀ k).2.1 - (traj F Λ b μ₁ k).2.1| := by
    intro k
    induction k with
    | zero =>
      intro _
      simp only [traj_zero, sub_self, abs_zero, norm_zero, le_refl, and_true]
      exact ⟨mul_nonneg hp0 (abs_nonneg _), mul_nonneg hq0 (abs_nonneg _)⟩
    | succ k ih =>
      intro hk
      obtain ⟨ig, ix, iμ⟩ := ih (by omega)
      obtain ⟨s1, s2, s3⟩ := unique_step H hp0 hq0 eg ex em (by omega : k < N)
        (h₀.1 k (by omega)) (h₁.1 k (by omega)) ig ix
      rw [traj_succ, traj_succ]
      have : |(traj F Λ b μ₀ k).2.1 - (traj F Λ b μ₁ k).2.1| ≤
          (1 + Λ) / 2 * |(traj F Λ b μ₀ k).2.1 - (traj F Λ b μ₁ k).2.1| := by
        have := H.hΛ
        nlinarith [abs_nonneg ((traj F Λ b μ₀ k).2.1 - (traj F Λ b μ₁ k).2.1)]
      exact ⟨s2, s3, iμ.trans (this.trans s1)⟩
  have := (key N le_rfl).2.2
  rw [h₀.2, h₁.2, sub_self, abs_zero] at this
  exact sub_eq_zero.1 (abs_nonpos_iff.1 this)

/-! ### The marginal coordinate -/

/-- `|1/g' - 1/g - β| ≤ C g` for one step. -/
lemma ginv_step {N : ℕ} {A a ε : ℝ} (H : FHHyp F Λ β κ c N A a ε) (he : ε ≤ eps0 β κ c)
    {j : ℕ} (hj : j < N) {s : ℝ × ℝ × X j} (hs : InD Λ κ c ε s) :
    |1 / F.G j s - 1 / s.1 - β| ≤ Cg β c * s.1 := by
  obtain ⟨hlow, -, -⟩ := step_D H he hj hs
  have hF1 := H.F1 j hj s hs
  have hβ := H.hβ; have hc := H.hc
  have hg := hs.1
  have hg1 : s.1 ≤ 1 := hs.2.1.trans (eps_facts hc hβ he).1
  set g := s.1
  set G := F.G j s
  have hG : 0 < G := by linarith
  set r := G - g + β * g ^ 2
  have e : 1 / G - 1 / g - β = (β ^ 2 * g ^ 3 - r * (1 + β * g)) / (g * G) := by
    field_simp; ring
  rw [e, abs_div, abs_of_pos (mul_pos hg hG), div_le_iff₀ (mul_pos hg hG)]
  have hn : |β ^ 2 * g ^ 3 - r * (1 + β * g)| ≤ β ^ 2 * g ^ 3 + c * g ^ 3 * (1 + β * g) := by
    calc _ ≤ |β ^ 2 * g ^ 3| + |r * (1 + β * g)| := abs_sub _ _
      _ = β ^ 2 * g ^ 3 + |r| * (1 + β * g) := by
          rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ β ^ 2 * g ^ 3), abs_mul,
            abs_of_pos (by positivity : (0:ℝ) < 1 + β * g)]
      _ ≤ _ := by gcongr
  have h1 : c * g ^ 3 * (β * g) ≤ c * g ^ 3 * β :=
    mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hβ.le hg1) (by positivity)
  have h2 : g ^ 2 * (5 / 6 * g) ≤ g ^ 2 * G := mul_le_mul_of_nonneg_left hlow (sq_nonneg g)
  have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ β ^ 2 + β * c + c)
  have h4 : 0 ≤ (β ^ 2 + β * c + c) * g ^ 3 := by positivity
  unfold Cg
  nlinarith

/-- **The marginal coordinate** (Proposition `prop:fh-flow` (ii)). -/
theorem ginv_admissible {N : ℕ} {A a ε : ℝ} (H : FHHyp F Λ β κ c N A a ε)
    (he : ε ≤ eps0 β κ c) {b μ₀ : ℝ} (h : Admissible F Λ κ c N ε b μ₀) {j : ℕ} (hj : j < N) :
    |1 / (traj F Λ b μ₀ (j + 1)).1 - 1 / (traj F Λ b μ₀ j).1 - β| ≤
      Cg β c * (traj F Λ b μ₀ j).1 :=
  ginv_step H he hj (h.1 j hj.le)

/-- The summed form: `|1/g_j - 1/b - βj| ≤ C ∑_{k<j} g_k`. -/
theorem ginv_sum {N : ℕ} {A a ε : ℝ} (H : FHHyp F Λ β κ c N A a ε)
    (he : ε ≤ eps0 β κ c) {b μ₀ : ℝ} (h : Admissible F Λ κ c N ε b μ₀) :
    ∀ j ≤ N, |1 / (traj F Λ b μ₀ j).1 - 1 / b - β * j| ≤
      Cg β c * ∑ k ∈ Finset.range j, (traj F Λ b μ₀ k).1 := by
  intro j
  induction j with
  | zero => intro _; simp [traj_zero]
  | succ j ih =>
    intro hj
    have h1 := ih (by omega)
    have h2 := ginv_admissible H he h (by omega : j < N)
    rw [Finset.sum_range_succ, mul_add]
    calc _ = |(1 / (traj F Λ b μ₀ j).1 - 1 / b - β * j) +
          (1 / (traj F Λ b μ₀ (j + 1)).1 - 1 / (traj F Λ b μ₀ j).1 - β)| := by
            congr 1; push_cast; ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add h1 h2)

/-! ### Continuity and shooting -/

open Classical in
variable (F Λ κ c) in
/-- The admissible initial `μ₀ = μ₀^c(b)` (a junk value if there is none). -/
def muc (N : ℕ) (ε b : ℝ) : ℝ :=
  if h : ∃ μ₀, Admissible F Λ κ c N ε b μ₀ then h.choose else 0

variable (F Λ κ c) in
/-- `g_N(b)` along the admissible flow. -/
def gN (N : ℕ) (ε b : ℝ) : ℝ := (traj F Λ b (muc F Λ κ c N ε b) N).1

section Cont

variable {N : ℕ} {A a ε : ℝ} (H : FHHyp F Λ β κ c N A a ε) (he : ε ≤ eps0 β κ c)
  (ha0 : a ≤ a0 Λ κ A)
include H he

lemma muc_spec {b : ℝ} (hb : b ∈ Ioc 0 ε) : Admissible F Λ κ c N ε b (muc F Λ κ c N ε b) := by
  have h := exists_admissible H he hb
  simp only [muc, dif_pos h]
  exact h.choose_spec

include ha0

lemma eq_muc {b μ₀ : ℝ} (hb : b ∈ Ioc 0 ε) (h : Admissible F Λ κ c N ε b μ₀) :
    μ₀ = muc F Λ κ c N ε b :=
  admissible_unique H ha0 h (muc_spec H he hb)

/-- Above `μ₀^c(b)` the clamped `μ_N` is positive. -/
lemma phi_pos_of_gt {b : ℝ} (hb : b ∈ Ioc 0 ε) {μ : ℝ} (h : muc F Λ κ c N ε b < μ) :
    0 < (trajc F Λ c b μ N).2.1 := by
  by_contra hn
  push Not at hn
  set R := max μ (cmu Λ c * b)
  obtain ⟨μ'', hmem, hz⟩ := intermediate_value_Icc (le_max_left μ (cmu Λ c * b))
    (continuous_phi H b).continuousOn ⟨hn, (phi_pos_of_ge H he hb (le_max_right _ _)).le⟩
  have := eq_muc H he ha0 hb (admissible_of_zero H he hb hz)
  linarith [hmem.1]

/-- Below `μ₀^c(b)` the clamped `μ_N` is negative. -/
lemma phi_neg_of_lt {b : ℝ} (hb : b ∈ Ioc 0 ε) {μ : ℝ} (h : μ < muc F Λ κ c N ε b) :
    (trajc F Λ c b μ N).2.1 < 0 := by
  by_contra hn
  push Not at hn
  obtain ⟨μ'', hmem, hz⟩ := intermediate_value_Icc (min_le_left μ (-(cmu Λ c * b)))
    (continuous_phi H b).continuousOn ⟨(phi_neg_of_le H he hb (min_le_right _ _)).le, hn⟩
  have := eq_muc H he ha0 hb (admissible_of_zero H he hb hz)
  linarith [hmem.2]

/-- **Continuity** of `b ↦ μ₀^c(b)` (Proposition `prop:fh-flow` (iii)). -/
theorem continuousOn_muc : ContinuousOn (muc F Λ κ c N ε) (Ioc 0 ε) := by
  intro b hb
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro δ hδ
  set μs := muc F Λ κ c N ε b
  have hp := phi_pos_of_gt H he ha0 hb (show μs < μs + δ / 2 by linarith)
  have hn := phi_neg_of_lt H he ha0 hb (show μs - δ / 2 < μs by linarith)
  have e1 : ∀ᶠ b' in 𝓝 b, 0 < (trajc F Λ c b' (μs + δ / 2) N).2.1 :=
    (continuous_phi' H _).continuousAt.eventually (lt_mem_nhds hp)
  have e2 : ∀ᶠ b' in 𝓝 b, (trajc F Λ c b' (μs - δ / 2) N).2.1 < 0 :=
    (continuous_phi' H _).continuousAt.eventually (gt_mem_nhds hn)
  filter_upwards [eventually_mem_nhdsWithin, (e1.and e2).filter_mono nhdsWithin_le_nhds]
    with b' hb' ⟨h1, h2⟩
  obtain ⟨μ'', hmem, hz⟩ := intermediate_value_Icc (by linarith : μs - δ / 2 ≤ μs + δ / 2)
    (continuous_phi H b').continuousOn ⟨h2.le, h1.le⟩
  have := eq_muc H he ha0 hb' (admissible_of_zero H he hb' hz)
  rw [Real.dist_eq, ← this, abs_lt]
  constructor <;> linarith [hmem.1, hmem.2]

/-- **Continuity** of `b ↦ g_N(b)` (Proposition `prop:fh-flow` (iii)). -/
theorem continuousOn_gN : ContinuousOn (gN F Λ κ c N ε) (Ioc 0 ε) := by
  have h : ContinuousOn (fun b => (trajc F Λ c b (muc F Λ κ c N ε b) N).1) (Ioc 0 ε) :=
    (continuous_fst.comp (continuous_trajc H N le_rfl)).comp_continuousOn
      (continuousOn_id.prodMk (continuousOn_muc H he ha0))
  refine h.congr fun b hb => ?_
  simp only [gN]
  rw [trajc_eq_traj (muc_spec H he hb) N le_rfl]

/-- **Shooting** (Proposition `prop:fh-flow` (iii)): every value between `g_N(b₁)` and `g_N(b₂)`
is `g_N(b)` for some `b` between `b₁` and `b₂`. -/
theorem shooting {b₁ b₂ : ℝ} (h₁ : b₁ ∈ Ioc 0 ε) (h₂ : b₂ ∈ Ioc 0 ε) {y : ℝ}
    (hy : y ∈ uIcc (gN F Λ κ c N ε b₁) (gN F Λ κ c N ε b₂)) :
    ∃ b ∈ uIcc b₁ b₂, gN F Λ κ c N ε b = y :=
  intermediate_value_uIcc ((continuousOn_gN H he ha0).mono
    (ordConnected_Ioc.uIcc_subset h₁ h₂)) hy

end Cont

/-! ### The proposition -/

lemma eps0_pos (hβ : 0 < β) (hκ1 : κ < 1) (hc : 0 < c) : 0 < eps0 β κ c := by
  unfold eps0
  have : 0 < 1 - κ := sub_pos.2 hκ1
  exact lt_min one_pos (lt_min (div_pos hβ hc) (by positivity))

lemma a0_pos (hΛ : 1 < Λ) (hκ1 : κ < 1) {A : ℝ} (hA : 0 ≤ A) : 0 < a0 Λ κ A := by
  have hh : 0 < Λ - 1 := sub_pos.2 hΛ
  have hk : 0 < 1 - κ := sub_pos.2 hκ1
  have hK : 0 < K1 Λ κ A := by unfold K1; positivity
  unfold a0
  exact lt_min (by positivity) (by positivity)

/-- **Proposition `prop:fh-flow`.** For `ε ≤ ε₀` and `a ≤ a₀` (with `ε₀, a₀ > 0` depending only
on `Λ, β, κ, c, A`): for every `b ∈ (0, ε]` there is a unique `μ₀` with `s_j ∈ D_ε` for `j ≤ N`
and `μ_N = 0`; along it `|1/g_{j+1} - 1/g_j - β| ≤ C g_j`; and `μ₀^c`, `g_N` are continuous on
`(0, ε]`. -/
theorem fh_flow {N : ℕ} {A a ε : ℝ} (H : FHHyp F Λ β κ c N A a ε) (he : ε ≤ eps0 β κ c)
    (ha0 : a ≤ a0 Λ κ A) :
    (∀ b ∈ Ioc 0 ε, ∃! μ₀, Admissible F Λ κ c N ε b μ₀) ∧
    (∀ b μ₀, Admissible F Λ κ c N ε b μ₀ → ∀ j < N,
      |1 / (traj F Λ b μ₀ (j + 1)).1 - 1 / (traj F Λ b μ₀ j).1 - β| ≤
        Cg β c * (traj F Λ b μ₀ j).1) ∧
    ContinuousOn (muc F Λ κ c N ε) (Ioc 0 ε) ∧ ContinuousOn (gN F Λ κ c N ε) (Ioc 0 ε) := by
  refine ⟨fun b hb => ?_, fun b μ₀ h j hj => ginv_admissible H he h hj,
    continuousOn_muc H he ha0, continuousOn_gN H he ha0⟩
  obtain ⟨μ₀, h⟩ := exists_admissible H he hb
  exact ⟨μ₀, h, fun μ₁ h₁ => admissible_unique H ha0 h₁ h⟩

end Flow2
