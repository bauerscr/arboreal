import Obs.TranslPair
import Ward.ObsLimitCorr
import PtCorr.TwoPtOne

/-!
# The infinite-volume two-point function (Case (1))

For a fixed `x ∈ ℤ^d`, `x ≠ 0`, along `(Λ_N, ctr_N, ctr_N + x)` (Case (1), `l₀ = λ̄`):

* `qP … x j`: the `q` increment of step `j` (`q_{a,j+1} + q_{b,j+1}`), computed on
  `Λ_{NP x j}`; it is the step-`j` increment on every `Λ_N` with `j + 2 ≤ N` and
  `|x|_∞ ≤ L^{N-1}` (`qP_char`, from `Obs.pair_consist`);
* `Qone … x = ∑_j qP x j / λ̄²` (`q_∞/λ̄²`);
* `qN_rate`: `|q_N/λ̄² - Qone x| ≤ K' L^{-(d-2)N}` (uniform in `m² ≥ 0`, `|b₀| ≤ λ̄`);
* `avg_two_tendsto`: at `m² > 0`, `⟨ψ̄₀ψ_x⟩_{Λ_N} → Qone x` (from `PtCorr.avg_one_decomp`).

The one-step bounds (`StepBd1`) are those of `Obs.Vobs_recursion_one` with the bound on
`K^obs_j` of `FlowData.obs`.
-/

namespace Ward

noncomputable section

open Finset Grassmann Loc Step Obs FRD PtCorr Metric Filter Topology

variable {d L : ℕ} [NeZero L] {A ℓ₀ lbar C κ : ℝ} {V₀c : ℝ → ℂ → Vcoup}

variable (d L) in
/-- The Case (1) flow on `Λ_N` at `(a, b)`. -/
abbrev FO1 (V₀c : ℝ → ℂ → Vcoup) (lbar msq : ℝ) (b₀ : ℂ) (N : ℕ) (a b : Lam d L N) (j : ℕ) :
    Coup .one × (Finset (Lam d L N) → OE .one (Lam d L N)) :=
  flowO d L .one N msq (V₀c msq b₀) (initObs .one (lbar : ℂ)) a b j

variable (d L) in
/-- The Case (1) step data. -/
abbrev NA1 (V₀c : ℝ → ℂ → Vcoup) (lbar msq : ℝ) (b₀ : ℂ) (N : ℕ) (a b : Lam d L N) (j : ℕ) :
    Coup .one :=
  nextAt d L .one N msq (V₀c msq b₀) (initObs .one (lbar : ℂ)) a b j

/-- `q = q_a + q_b`. -/
abbrev qS (W : Coup .one) : ℂ := qaOf .one W + qbOf .one W

variable (d L) in
/-- **One-step bounds, Case (1)**, at `(ctr_N, b)`, `b ≠ ctr_N`. -/
def StepBd1 (A ℓ₀ : ℝ) (V₀c : ℝ → ℂ → Vcoup) (lbar C κ Cs : ℝ) : Prop :=
  ∀ msq : ℝ, 0 ≤ msq → ∀ b₀ : ℂ, ‖b₀‖ ≤ lbar → ∀ (N : ℕ) (b : Lam d L N), b ≠ ctr d L N →
    ∀ k < N,
    ‖laOf .one (FO1 d L V₀c lbar msq b₀ N (ctr d L N) b (k + 1)).1 -
        laOf .one (FO1 d L V₀c lbar msq b₀ N (ctr d L N) b k).1‖ ≤
      Cs * (C * lbar * ‖b₀‖ * th L κ ^ k) ∧
    ‖lbOf .one (FO1 d L V₀c lbar msq b₀ N (ctr d L N) b (k + 1)).1 -
        lbOf .one (FO1 d L V₀c lbar msq b₀ N (ctr d L N) b k).1‖ ≤
      Cs * (C * lbar * ‖b₀‖ * th L κ ^ k) ∧
    ‖qS (NA1 d L V₀c lbar msq b₀ N (ctr d L N) b k) -
        (laOf .one (FO1 d L V₀c lbar msq b₀ N (ctr d L N) b (k + 1)).1 *
            lbOf .one (FO1 d L V₀c lbar msq b₀ N (ctr d L N) b (k + 1)).1 *
            (Flow.covAt d L N msq k (ctr d L N) b : ℂ) -
          (raOf .one (FO1 d L V₀c lbar msq b₀ N (ctr d L N) b (k + 1)).1 *
              (Flow.covAt d L N msq k (ctr d L N) (ctr d L N) : ℂ) +
            rbOf .one (FO1 d L V₀c lbar msq b₀ N (ctr d L N) b (k + 1)).1 *
              (Flow.covAt d L N msq k b b : ℂ)))‖ ≤
      2 * Cs * ellj d L ℓ₀ k ^ 2 * (C * lbar * ‖b₀‖ * th L κ ^ k) ∧
    ‖raOf .one (FO1 d L V₀c lbar msq b₀ N (ctr d L N) b (k + 1)).1 -
        raOf .one (FO1 d L V₀c lbar msq b₀ N (ctr d L N) b k).1‖ ≤
      Cs * (C * lbar * ‖b₀‖ * th L κ ^ k) ∧
    ‖rbOf .one (FO1 d L V₀c lbar msq b₀ N (ctr d L N) b (k + 1)).1 -
        rbOf .one (FO1 d L V₀c lbar msq b₀ N (ctr d L N) b k).1‖ ≤
      Cs * (C * lbar * ‖b₀‖ * th L κ ^ k)

theorem ind_le_one (P : Prop) [Decidable P] : (if P then (1 : ℝ) else 0) ≤ 1 := by
  split_ifs <;> norm_num

theorem ind_nonneg (P : Prop) [Decidable P] : 0 ≤ (if P then (1 : ℝ) else 0) := by
  split_ifs <;> norm_num

/-- The Case (1) one-step bounds hold with a constant depending only on `d`. -/
theorem exists_stepBd1 (d : ℕ) (hd : 1 ≤ d) : ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ (L : ℕ) [NeZero L]
    (A ℓ₀ : ℝ) (V₀c : ℝ → ℂ → Vcoup) (lbar C κ : ℝ), ObsLimHyp d L A ℓ₀ V₀c lbar C κ →
    StepBd1 d L A ℓ₀ V₀c lbar C κ Cs := by
  obtain ⟨Cs, hCs, hrec⟩ := Vobs_recursion_one d
  refine ⟨Cs, hCs, ?_⟩
  intro L _ A ℓ₀ V₀c lbar C κ H msq hmsq b₀ hb₀ N b hb k hk
  have hθ : (L : ℝ) ^ (-(κ * k)) = th L κ ^ k := rpow_neg_mul_nat (Nat.cast_nonneg _) κ k
  have hK := (H.fd.obs .one N msq (lbar : ℂ) b₀ b hmsq (by rw [norm_lbar H]; exact hb₀)
    (le_of_eq (norm_lbar H)) hb k hk.le).2
  rw [norm_lbar H, hθ] at hK
  have he : 0 ≤ C * lbar * ‖b₀‖ * th L κ ^ k := by
    have := H.fd.C_nonneg; have := H.fd.lbar_pos; have := th_nonneg L κ; positivity
  obtain ⟨r1, r2, r3, r4, r5⟩ := hrec L N k ℓ₀ H.fd.hℓ₀ (Flow.covAt d L N msq k)
    (FO1 d L V₀c lbar msq b₀ N (ctr d L N) b k).1 (FO1 d L V₀c lbar msq b₀ N (ctr d L N) b k).2
    (ctr d L N) b A H.fd.hA1 _ he hK
    (fun hj Y hY => abSmall_flowO (V₀c msq b₀) (lbar : ℂ) (ctr d L N) b hd H.fd.hL8
      (H.fd.good N msq hmsq) hk hj hY)
  have e1 : (FO1 d L V₀c lbar msq b₀ N (ctr d L N) b (k + 1)).1 =
      Coup.toV .one (nextObs (Flow.covAt d L N msq k) k
        (FO1 d L V₀c lbar msq b₀ N (ctr d L N) b k).1
        (FO1 d L V₀c lbar msq b₀ N (ctr d L N) b k).2 (ctr d L N) b) := rfl
  rw [e1, laOf_toV, lbOf_toV, raOf_toV, rbOf_toV]
  have hI := ind_le_one (coal L (ctr d L N) b ≤ k)
  have hI0 := ind_nonneg (coal L (ctr d L N) b ≤ k)
  refine ⟨r1, r2, ?_, ?_, ?_⟩
  · refine r3.trans ?_
    rw [ellab_one_inv]
    have h0 : 0 ≤ 2 * Cs * ellj d L ℓ₀ k ^ 2 * (C * lbar * ‖b₀‖ * th L κ ^ k) := by positivity
    calc 2 * Cs * ellj d L ℓ₀ k ^ 2 * (C * lbar * ‖b₀‖ * th L κ ^ k) *
          (if coal L (ctr d L N) b ≤ k then (1 : ℝ) else 0)
        ≤ 2 * Cs * ellj d L ℓ₀ k ^ 2 * (C * lbar * ‖b₀‖ * th L κ ^ k) * 1 :=
          mul_le_mul_of_nonneg_left hI h0
      _ = _ := mul_one _
  · refine r4.trans ?_
    have h0 : 0 ≤ Cs * (C * lbar * ‖b₀‖ * th L κ ^ k) := by positivity
    calc Cs * (C * lbar * ‖b₀‖ * th L κ ^ k) *
          (if coal L (ctr d L N) b ≤ k then (1 : ℝ) else 0)
        ≤ Cs * (C * lbar * ‖b₀‖ * th L κ ^ k) * 1 := mul_le_mul_of_nonneg_left hI h0
      _ = _ := mul_one _
  · refine r5.trans ?_
    have h0 : 0 ≤ Cs * (C * lbar * ‖b₀‖ * th L κ ^ k) := by positivity
    calc Cs * (C * lbar * ‖b₀‖ * th L κ ^ k) *
          (if coal L (ctr d L N) b ≤ k then (1 : ℝ) else 0)
        ≤ Cs * (C * lbar * ‖b₀‖ * th L κ ^ k) * 1 := mul_le_mul_of_nonneg_left hI h0
      _ = _ := mul_one _

/-! ### Points -/

/-- The torus size used for the pair `(ctr, ctr + x)` at scale `j`. -/
def NP (x : Zd d) (j : ℕ) : ℕ := j + 2 + supNormZ x

theorem hx_of (hL : 16 ≤ L) {N : ℕ} (hN : 1 ≤ N) {x : Zd d} (hs : supNormZ x ≤ L ^ (N - 1)) :
    8 * ((L ^ (N - 1) - 1) / 2 + supNormZ x) ≤ L ^ N := by
  have h : L ^ N = L * L ^ (N - 1) := by rw [← pow_succ']; congr 1; omega
  have h1 : 16 * L ^ (N - 1) ≤ L * L ^ (N - 1) := Nat.mul_le_mul_right _ hL
  omega

theorem supNormZ_le_NP (hL : 2 ≤ L) (x : Zd d) (j : ℕ) : supNormZ x ≤ L ^ (NP x j - 1) := by
  have h1 : supNormZ x < L ^ supNormZ x := Nat.lt_pow_self (by omega)
  have h2 : L ^ supNormZ x ≤ L ^ (NP x j - 1) := Nat.pow_le_pow_right (by omega) (by unfold NP; omega)
  omega

theorem prj_ne_zero {N : ℕ} {x : Zd d} (hx : x ≠ 0) (hs : 2 * supNormZ x < L ^ N) :
    (prj x : Lam d L N) ≠ 0 := by
  intro h
  have h1 : x = rep (prj x : Lam d L N) := eq_rep rfl hs
  have hz : supNormZ (0 : Zd d) = 0 := by simp [supNormZ]
  have hp := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) N
  have h2 : (0 : Zd d) = rep (0 : Lam d L N) := eq_rep prj_zero (by rw [hz]; omega)
  exact hx (by rw [h1, h, ← h2])

theorem two_s_lt (hL : 3 ≤ L) {N : ℕ} {x : Zd d} (hs : supNormZ x ≤ L ^ (N - 1)) (hN : 1 ≤ N) :
    2 * supNormZ x < L ^ N := by
  have h : L ^ N = L * L ^ (N - 1) := by rw [← pow_succ']; congr 1; omega
  have h1 : 3 * L ^ (N - 1) ≤ L * L ^ (N - 1) := Nat.mul_le_mul_right _ hL
  have h0 : 0 < L ^ (N - 1) := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
  omega

theorem ctr_add_prj_ne (hL : 3 ≤ L) {N : ℕ} (hN : 1 ≤ N) {x : Zd d} (hx : x ≠ 0)
    (hs : supNormZ x ≤ L ^ (N - 1)) : ctr d L N + prj x ≠ ctr d L N := by
  intro h
  exact prj_ne_zero hx (two_s_lt hL hs hN) (by simpa using h)

/-! ### The pair sequence -/

variable (d L) in
/-- The `q` increment of step `j` at the pair `(ctr, ctr + x)`, computed on `Λ_{NP x j}`. -/
def qP (V₀c : ℝ → ℂ → Vcoup) (lbar msq : ℝ) (b₀ : ℂ) (x : Zd d) (j : ℕ) : ℂ :=
  qS (NA1 d L V₀c lbar msq b₀ (NP x j) (ctr d L (NP x j)) (ctr d L (NP x j) + prj x) j)

variable (d L) in
/-- `q_∞/λ̄²` at `x`. -/
def Qone (V₀c : ℝ → ℂ → Vcoup) (lbar msq : ℝ) (b₀ : ℂ) (x : Zd d) : ℂ :=
  (∑' j, qP d L V₀c lbar msq b₀ x j) / (lbar : ℂ) ^ 2

/-- The tail of a series with geometric bound. -/
theorem norm_tsum_tail_le' (g : ℕ → ℂ) {K ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hg : ∀ j, ‖g j‖ ≤ K * ρ ^ j) (n : ℕ) :
    ‖∑' i, g (i + n)‖ ≤ K * ρ ^ n / (1 - ρ) := by
  have hs : HasSum (fun i => K * ρ ^ n * ρ ^ i) (K * ρ ^ n * (1 - ρ)⁻¹) :=
    (hasSum_geometric_of_lt_one hρ0 hρ1).mul_left _
  refine (tsum_of_norm_bounded hs fun i => (hg (i + n)).trans (le_of_eq (by ring))).trans
    (le_of_eq (by ring))

/-- A partial sum plus a last term against the full series. -/
theorem series_core (g : ℕ → ℂ) (T : ℂ) (hs : Summable g) {K' ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) (hgb : ∀ j, ‖g j‖ ≤ K' * ρ ^ j) {n : ℕ} (hT : ‖T‖ ≤ K' * ρ ^ n) :
    ‖(∑ j ∈ range n, g j + T) - ∑' j, g j‖ ≤ K' * (1 + 1 / (1 - ρ)) * ρ ^ n := by
  rw [← hs.sum_add_tsum_nat_add n]
  have e : (∑ j ∈ range n, g j + T) - (∑ j ∈ range n, g j + ∑' i, g (i + n)) =
      T - ∑' i, g (i + n) := by abel
  rw [e]
  have htail := norm_tsum_tail_le' g hρ0 hρ1 hgb n
  calc ‖T - ∑' i, g (i + n)‖ ≤ ‖T‖ + ‖∑' i, g (i + n)‖ := norm_sub_le _ _
    _ ≤ K' * ρ ^ n + K' * ρ ^ n / (1 - ρ) := add_le_add hT htail
    _ = K' * (1 + 1 / (1 - ρ)) * ρ ^ n := by ring

variable (H : ObsLimHyp d L A ℓ₀ V₀c lbar C κ) (hd : 1 ≤ d)
include H hd

theorem sixteen_le : 16 ≤ L := by
  have : 2 ^ 4 ≤ 2 ^ (d + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have := H.fd.hL8; omega

/-- **The pair `q` increments are `N`-independent**. -/
theorem qP_char {msq : ℝ} (hmsq : 0 ≤ msq) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar) (x : Zd d) {N j : ℕ}
    (hj : j + 2 ≤ N) (hs : supNormZ x ≤ L ^ (N - 1)) :
    qS (NA1 d L V₀c lbar msq b₀ N (ctr d L N) (ctr d L N + prj x) j) =
      qP d L V₀c lbar msq b₀ x j := by
  have h16 := sixteen_le H hd
  have hNP : N ≤ max N (NP x j) := le_max_left _ _
  have hBP : NP x j ≤ max N (NP x j) := le_max_right _ _
  have hjB : j + 2 ≤ NP x j := by unfold NP; omega
  have e1 := (pair_consist hd H.fd.hL8 hNP hmsq (V₀c msq b₀) (H.fd.good _ msq hmsq)
    (H.hbulk hmsq hb₀ hNP) H.odd (initObs .one (lbar : ℂ)) x (hx_of h16 (by omega) hs) hj).2
  have e2 := (pair_consist hd H.fd.hL8 hBP hmsq (V₀c msq b₀) (H.fd.good _ msq hmsq)
    (H.hbulk hmsq hb₀ hBP) H.odd (initObs .one (lbar : ℂ)) x
    (hx_of h16 (by omega) (supNormZ_le_NP (by omega) x j)) hjB).2
  unfold qP
  show qaOf .one (nextObs _ _ _ _ _ _) + qbOf .one (nextObs _ _ _ _ _ _) =
    qaOf .one (nextObs _ _ _ _ _ _) + qbOf .one (nextObs _ _ _ _ _ _)
  rw [e1, e2]

/-! ### Bounds -/

variable {Cs : ℝ} (hCs : 0 ≤ Cs) (hS1 : StepBd1 d L A ℓ₀ V₀c lbar C κ Cs)
include hCs hS1

/-- `Rm = C_S E/(1-θ)`. -/
abbrev Rm (lbar C κ Cs : ℝ) (b₀ : ℂ) (L : ℕ) : ℝ := Cs * (C * lbar * ‖b₀‖) / (1 - th L κ)

theorem E1_nonneg (b₀ : ℂ) : 0 ≤ C * lbar * ‖b₀‖ := by
  have := H.fd.C_nonneg; have := H.fd.lbar_pos; positivity

theorem la1_bd {msq : ℝ} (hmsq : 0 ≤ msq) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar) {N : ℕ}
    {b : Lam d L N} (hb : b ≠ ctr d L N) {k : ℕ} (hk : k ≤ N) :
    ‖laOf .one (FO1 d L V₀c lbar msq b₀ N (ctr d L N) b k).1‖ ≤ Lm lbar C κ Cs b₀ L := by
  have := geom_bd H hCs
    (fun k => laOf .one (FO1 d L V₀c lbar msq b₀ N (ctr d L N) b k).1)
    (E1_nonneg H hd hCs hS1 b₀) (a := (lbar : ℂ)) rfl
    (fun i hi => (hS1 msq hmsq b₀ hb₀ N b hb i (by omega)).1) (n := k)
  rwa [norm_lbar H] at this

theorem lb1_bd {msq : ℝ} (hmsq : 0 ≤ msq) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar) {N : ℕ}
    {b : Lam d L N} (hb : b ≠ ctr d L N) {k : ℕ} (hk : k ≤ N) :
    ‖lbOf .one (FO1 d L V₀c lbar msq b₀ N (ctr d L N) b k).1‖ ≤ Lm lbar C κ Cs b₀ L := by
  have := geom_bd H hCs
    (fun k => lbOf .one (FO1 d L V₀c lbar msq b₀ N (ctr d L N) b k).1)
    (E1_nonneg H hd hCs hS1 b₀) (a := (lbar : ℂ)) rfl
    (fun i hi => (hS1 msq hmsq b₀ hb₀ N b hb i (by omega)).2.1) (n := k)
  rwa [norm_lbar H] at this

theorem ra1_bd {msq : ℝ} (hmsq : 0 ≤ msq) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar) {N : ℕ}
    {b : Lam d L N} (hb : b ≠ ctr d L N) {k : ℕ} (hk : k ≤ N) :
    ‖raOf .one (FO1 d L V₀c lbar msq b₀ N (ctr d L N) b k).1‖ ≤ Rm lbar C κ Cs b₀ L := by
  have := geom_bd H hCs
    (fun k => raOf .one (FO1 d L V₀c lbar msq b₀ N (ctr d L N) b k).1)
    (E1_nonneg H hd hCs hS1 b₀) (a := 0) rfl
    (fun i hi => (hS1 msq hmsq b₀ hb₀ N b hb i (by omega)).2.2.2.1) (n := k)
  rwa [norm_zero, zero_add] at this

theorem rb1_bd {msq : ℝ} (hmsq : 0 ≤ msq) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar) {N : ℕ}
    {b : Lam d L N} (hb : b ≠ ctr d L N) {k : ℕ} (hk : k ≤ N) :
    ‖rbOf .one (FO1 d L V₀c lbar msq b₀ N (ctr d L N) b k).1‖ ≤ Rm lbar C κ Cs b₀ L := by
  have := geom_bd H hCs
    (fun k => rbOf .one (FO1 d L V₀c lbar msq b₀ N (ctr d L N) b k).1)
    (E1_nonneg H hd hCs hS1 b₀) (a := 0) rfl
    (fun i hi => (hS1 msq hmsq b₀ hb₀ N b hb i (by omega)).2.2.2.2) (n := k)
  rwa [norm_zero, zero_add] at this

/-- `Kq = (Λm² + 2 Rm + 2 C_S E) ℓ₀²`. -/
abbrev Kq (lbar C κ Cs ℓ₀ : ℝ) (b₀ : ℂ) (L : ℕ) : ℝ :=
  (Lm lbar C κ Cs b₀ L ^ 2 + 2 * Rm lbar C κ Cs b₀ L + 2 * Cs * (C * lbar * ‖b₀‖)) * ℓ₀ ^ 2

theorem Rm_nonneg (b₀ : ℂ) : 0 ≤ Rm lbar C κ Cs b₀ L := by
  have hθ1 := th_lt_one (by have := three_le_L H; omega) H.fd.κ_pos (L := L)
  have := E1_nonneg H hd hCs hS1 b₀
  have := H.fd.C_nonneg; have := H.fd.lbar_pos
  have : 0 < 1 - th L κ := by linarith
  unfold Rm; positivity

theorem q_bd (hd2 : 2 ≤ d) {msq : ℝ} (hmsq : 0 ≤ msq) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar) {N : ℕ}
    {b : Lam d L N} (hb : b ≠ ctr d L N) {k : ℕ} (hk : k < N) :
    ‖qS (NA1 d L V₀c lbar msq b₀ N (ctr d L N) b k)‖ ≤ Kq lbar C κ Cs ℓ₀ b₀ L * rho d L ^ k := by
  obtain ⟨-, -, hq, -, -⟩ := hS1 msq hmsq b₀ hb₀ N b hb k hk
  have hla := la1_bd H hd hCs hS1 hmsq hb₀ hb (k := k + 1) (by omega)
  have hlb := lb1_bd H hd hCs hS1 hmsq hb₀ hb (k := k + 1) (by omega)
  have hra := ra1_bd H hd hCs hS1 hmsq hb₀ hb (k := k + 1) (by omega)
  have hrb := rb1_bd H hd hCs hS1 hmsq hb₀ hb (k := k + 1) (by omega)
  have hG := H.fd.good N msq hmsq k hk
  have hcab := abs_cov_le H.fd.hℓ₀ hG (ctr d L N) b
  have hcaa := abs_cov_le H.fd.hℓ₀ hG (ctr d L N) (ctr d L N)
  have hcbb := abs_cov_le H.fd.hℓ₀ hG b b
  have hLm : 0 ≤ Lm lbar C κ Cs b₀ L := by
    have hθ1 := th_lt_one (by have := three_le_L H; omega) H.fd.κ_pos (L := L)
    have := E1_nonneg H hd hCs hS1 b₀
    have := H.fd.lbar_pos
    have := H.fd.C_nonneg
    have : 0 < 1 - th L κ := by linarith
    unfold Lm; positivity
  have hRm := Rm_nonneg H hd hCs hS1 b₀
  have hE := E1_nonneg H hd hCs hS1 b₀
  have hθ1 := th_lt_one (by have := three_le_L H; omega) H.fd.κ_pos (L := L)
  have hθk : th L κ ^ k ≤ 1 := pow_le_one₀ (th_nonneg L κ) hθ1.le
  have hs : ellj d L ℓ₀ (k + 1) ^ 2 ≤ ellj d L ℓ₀ k ^ 2 := by
    rw [ellj_sq, ellj_sq, pow_succ]
    have h1 := rho_le_one hd2 L
    have h2 : 0 ≤ rho d L ^ k := pow_nonneg (rho_nonneg d L) k
    have h3 : 0 ≤ ℓ₀ ^ 2 := sq_nonneg _
    calc ℓ₀ ^ 2 * (rho d L ^ k * rho d L) ≤ ℓ₀ ^ 2 * (rho d L ^ k * 1) := by gcongr
      _ = ℓ₀ ^ 2 * rho d L ^ k := by ring
  set ℓk := ellj d L ℓ₀ k ^ 2 with hℓk
  have hℓk0 : 0 ≤ ℓk := sq_nonneg _
  have nc : ∀ x y : Lam d L N, ‖(Flow.covAt d L N msq k x y : ℂ)‖ ≤ ℓk := fun x y => by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (abs_cov_le H.fd.hℓ₀ hG x y).trans hs
  set la := laOf .one (FO1 d L V₀c lbar msq b₀ N (ctr d L N) b (k + 1)).1
  set lb := lbOf .one (FO1 d L V₀c lbar msq b₀ N (ctr d L N) b (k + 1)).1
  set ra := raOf .one (FO1 d L V₀c lbar msq b₀ N (ctr d L N) b (k + 1)).1
  set rb := rbOf .one (FO1 d L V₀c lbar msq b₀ N (ctr d L N) b (k + 1)).1
  have h1 : ‖la * lb * (Flow.covAt d L N msq k (ctr d L N) b : ℂ)‖ ≤
      Lm lbar C κ Cs b₀ L ^ 2 * ℓk := by
    rw [norm_mul, norm_mul, sq]
    exact mul_le_mul (mul_le_mul hla hlb (norm_nonneg _) hLm) (nc _ _) (norm_nonneg _)
      (by positivity)
  have h2 : ‖ra * (Flow.covAt d L N msq k (ctr d L N) (ctr d L N) : ℂ) +
      rb * (Flow.covAt d L N msq k b b : ℂ)‖ ≤ 2 * Rm lbar C κ Cs b₀ L * ℓk := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have := mul_le_mul hra (nc (ctr d L N) (ctr d L N)) (norm_nonneg _) hRm
    have := mul_le_mul hrb (nc b b) (norm_nonneg _) hRm
    linarith
  have h3 : 2 * Cs * ℓk * (C * lbar * ‖b₀‖ * th L κ ^ k) ≤ 2 * Cs * (C * lbar * ‖b₀‖) * ℓk := by
    have : C * lbar * ‖b₀‖ * th L κ ^ k ≤ C * lbar * ‖b₀‖ := by
      calc C * lbar * ‖b₀‖ * th L κ ^ k ≤ C * lbar * ‖b₀‖ * 1 :=
            mul_le_mul_of_nonneg_left hθk hE
        _ = _ := mul_one _
    have h0 : 0 ≤ 2 * Cs * ℓk := by positivity
    calc 2 * Cs * ℓk * (C * lbar * ‖b₀‖ * th L κ ^ k) ≤ 2 * Cs * ℓk * (C * lbar * ‖b₀‖) :=
          mul_le_mul_of_nonneg_left this h0
      _ = _ := by ring
  have hx : ‖qS (NA1 d L V₀c lbar msq b₀ N (ctr d L N) b k)‖ ≤
      ‖qS (NA1 d L V₀c lbar msq b₀ N (ctr d L N) b k) -
          (la * lb * (Flow.covAt d L N msq k (ctr d L N) b : ℂ) -
            (ra * (Flow.covAt d L N msq k (ctr d L N) (ctr d L N) : ℂ) +
              rb * (Flow.covAt d L N msq k b b : ℂ)))‖ +
        (‖la * lb * (Flow.covAt d L N msq k (ctr d L N) b : ℂ)‖ +
          ‖ra * (Flow.covAt d L N msq k (ctr d L N) (ctr d L N) : ℂ) +
              rb * (Flow.covAt d L N msq k b b : ℂ)‖) := by
    refine (norm_le_norm_sub_add _ _).trans (add_le_add le_rfl (norm_sub_le _ _))
  calc ‖qS (NA1 d L V₀c lbar msq b₀ N (ctr d L N) b k)‖
      ≤ 2 * Cs * (C * lbar * ‖b₀‖) * ℓk + (Lm lbar C κ Cs b₀ L ^ 2 * ℓk +
          2 * Rm lbar C κ Cs b₀ L * ℓk) := by linarith
    _ = Kq lbar C κ Cs ℓ₀ b₀ L * rho d L ^ k := by rw [hℓk, ellj_sq]; unfold Kq; ring

theorem Kq_nonneg (b₀ : ℂ) : 0 ≤ Kq lbar C κ Cs ℓ₀ b₀ L := by
  have := Rm_nonneg H hd hCs hS1 b₀
  have := E1_nonneg H hd hCs hS1 b₀
  unfold Kq; positivity

theorem qP_bd (hd2 : 2 ≤ d) {msq : ℝ} (hmsq : 0 ≤ msq) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar) {x : Zd d}
    (hx0 : x ≠ 0) (j : ℕ) :
    ‖qP d L V₀c lbar msq b₀ x j‖ ≤ Kq lbar C κ Cs ℓ₀ b₀ L * rho d L ^ j := by
  have hL3 := three_le_L H
  have hb := ctr_add_prj_ne hL3 (N := NP x j) (by unfold NP; omega) hx0
    (supNormZ_le_NP (by omega) x j)
  exact q_bd H hd hCs hS1 hd2 hmsq hb₀ hb (by unfold NP; omega)

theorem qP_summable (hd3 : 3 ≤ d) {msq : ℝ} (hmsq : 0 ≤ msq) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar)
    {x : Zd d} (hx0 : x ≠ 0) : Summable (qP d L V₀c lbar msq b₀ x) := by
  have hρ1 := rho_lt_one hd3 (by have := three_le_L H; omega) (L := L)
  exact Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (rho_nonneg d L) hρ1).mul_left (Kq lbar C κ Cs ℓ₀ b₀ L))
    fun j => qP_bd H hd hCs hS1 (by omega) hmsq hb₀ hx0 j

/-- **Rate for `q_N`**: `|q_N/λ̄² - Qone x| ≤ K' L^{-(d-2)N}` (`N ≥ 2`, `|x|_∞ ≤ L^{N-1}`). -/
theorem qN_rate (hd3 : 3 ≤ d) {msq : ℝ} (hmsq : 0 ≤ msq) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar)
    {x : Zd d} (hx0 : x ≠ 0) {N : ℕ} (hN : 2 ≤ N) (hs : supNormZ x ≤ L ^ (N - 1)) :
    ‖qN d L .one N msq (V₀c msq b₀) (initObs .one (lbar : ℂ)) (ctr d L N) (ctr d L N + prj x) /
        (lbar : ℂ) ^ 2 - Qone d L V₀c lbar msq b₀ x‖ ≤
      Kq lbar C κ Cs ℓ₀ b₀ L * (1 + 1 / (1 - rho d L)) / (rho d L * lbar ^ 2) *
        (L : ℝ) ^ (-(((d : ℝ) - 2) * N)) := by
  have hd2 : 2 ≤ d := by omega
  have hL3 := three_le_L H
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hb := ctr_add_prj_ne hL3 (N := n + 1) (by omega) hx0 hs
  have hlb := H.fd.lbar_pos
  have hρ0 := rho_nonneg d L
  have hρ1 := rho_lt_one hd3 (by omega) (L := L)
  have hρp : 0 < rho d L :=
    Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) _
  have hfin : qN d L .one (n + 1) msq (V₀c msq b₀) (initObs .one (lbar : ℂ)) (ctr d L (n + 1))
      (ctr d L (n + 1) + prj x) = ∑ j ∈ range n, qP d L V₀c lbar msq b₀ x j +
        qS (NA1 d L V₀c lbar msq b₀ (n + 1) (ctr d L (n + 1)) (ctr d L (n + 1) + prj x) n) := by
    rw [qN, sum_range_succ]
    congr 1
    exact sum_congr rfl fun j hj =>
      qP_char H hd hmsq hb₀ x (N := n + 1) (j := j) (by simp at hj; omega) hs
  have hcore := series_core (qP d L V₀c lbar msq b₀ x) _ (qP_summable H hd hCs hS1 hd3 hmsq hb₀ hx0)
    hρ0 hρ1 (qP_bd H hd hCs hS1 hd2 hmsq hb₀ hx0)
    (q_bd H hd hCs hS1 hd2 hmsq hb₀ hb (k := n) (by omega))
  have hl2 : ((lbar : ℂ) ^ 2) ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hlb.ne')
  have e1 : qN d L .one (n + 1) msq (V₀c msq b₀) (initObs .one (lbar : ℂ)) (ctr d L (n + 1))
      (ctr d L (n + 1) + prj x) / (lbar : ℂ) ^ 2 - Qone d L V₀c lbar msq b₀ x =
      ((∑ j ∈ range n, qP d L V₀c lbar msq b₀ x j +
        qS (NA1 d L V₀c lbar msq b₀ (n + 1) (ctr d L (n + 1)) (ctr d L (n + 1) + prj x) n)) -
        ∑' j, qP d L V₀c lbar msq b₀ x j) / (lbar : ℂ) ^ 2 := by
    rw [hfin, Qone, sub_div]
  have hl2' : ‖((lbar : ℂ) ^ 2)‖ = lbar ^ 2 := by rw [norm_pow, norm_lbar H]
  have hlb2 : 0 < lbar ^ 2 := by positivity
  rw [e1, norm_div, hl2', rpow_neg_mul_nat (Nat.cast_nonneg _) ((d : ℝ) - 2) (n + 1),
    div_le_iff₀ hlb2]
  refine hcore.trans (le_of_eq ?_)
  have hρne : rho d L ≠ 0 := hρp.ne'
  have h1ρne : 1 - rho d L ≠ 0 := by linarith
  field_simp
  ring

/-- **`⟨ψ̄₀ψ_x⟩_{Λ_N} → Qone x`** at `m² > 0` (`x ∈ ℤ^d`, `x ≠ 0`). -/
theorem avg_two_tendsto (hd3 : 3 ≤ d) {msq : ℝ} (hmsq : 0 < msq) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar)
    {x : Zd d} (hx0 : x ≠ 0) :
    Tendsto (fun N => avg (Suscept.Cov d L N msq) (VE (V₀c msq b₀) univ)
      (psibar (0 : Lam d L N) * psi (prj x : Lam d L N))) atTop
      (𝓝 (Qone d L V₀c lbar msq b₀ x)) := by
  have hd2 : 2 ≤ d := by omega
  have hL3 := three_le_L H
  have hL2 : 2 ≤ L := by omega
  have hlb := H.fd.lbar_pos
  have hκ := H.fd.κ_pos
  have hC0 := H.fd.C_nonneg
  have hθ0 := th_nonneg L κ
  have hθ1 := th_lt_one hL2 hκ (L := L)
  have hLm : 0 ≤ Lm lbar C κ Cs b₀ L := by
    have := E1_nonneg H hd hCs hS1 b₀
    have : 0 < 1 - th L κ := by linarith
    unfold Lm; positivity
  have hRm := Rm_nonneg H hd hCs hS1 b₀
  have hKq := Kq_nonneg H hd hCs hS1 b₀
  have hE := E1_nonneg H hd hCs hS1 b₀
  have hlb2 : 0 < lbar ^ 2 := by positivity
  -- the bound
  obtain ⟨bd, hbd_def⟩ : ∃ bd : ℕ → ℝ, bd = fun N : ℕ =>
    Kq lbar C κ Cs ℓ₀ b₀ L * (1 + 1 / (1 - rho d L)) / (rho d L * lbar ^ 2) *
        (L : ℝ) ^ (-(((d : ℝ) - 2) * N)) +
      2 * (((Lm lbar C κ Cs b₀ L ^ 2 + 2 * Rm lbar C κ Cs b₀ L) *
          (1 / (msq * Fintype.card (Lam d L N))) +
        (ℓ₀ ^ 2 + 1 / (msq * Fintype.card (Lam d L N))) *
          (C * lbar * ‖b₀‖ * (L : ℝ) ^ (-(κ * N)))) / lbar ^ 2) := ⟨_, rfl⟩
  have hbd : Tendsto bd atTop (𝓝 0) := by
    have t1 := tendsto_rpow_neg_mul (L := L) hL2 (s := (d : ℝ) - 2)
      (by have : (3 : ℝ) ≤ d := (by exact_mod_cast hd3); linarith)
    have t3 := tendsto_rpow_neg_mul (L := L) hL2 hκ
    have t4 := tendsto_inv_card (d := d) hd hL2 hmsq
    have := (t1.const_mul (Kq lbar C κ Cs ℓ₀ b₀ L * (1 + 1 / (1 - rho d L)) /
      (rho d L * lbar ^ 2))).add
      ((((t4.const_mul (Lm lbar C κ Cs b₀ L ^ 2 + 2 * Rm lbar C κ Cs b₀ L)).add
        ((t4.const_add (ℓ₀ ^ 2)).mul (t3.const_mul (C * lbar * ‖b₀‖)))).div_const
          (lbar ^ 2)).const_mul 2)
    rw [hbd_def]; simpa using this
  have hev1 : ∀ᶠ N : ℕ in atTop, 1 ≤ msq * (L : ℝ) ^ (2 * N) := by
    have : Tendsto (fun N : ℕ => msq * (L : ℝ) ^ (2 * N)) atTop atTop := by
      refine Tendsto.const_mul_atTop hmsq ?_
      have h1 : Tendsto (fun N : ℕ => ((L : ℝ) ^ 2) ^ N) atTop atTop :=
        tendsto_pow_atTop_atTop_of_one_lt (by
          have : (2 : ℝ) ≤ L := by exact_mod_cast hL2
          nlinarith)
      exact h1.congr fun N => by rw [← pow_mul]
    exact this.eventually_ge_atTop 1
  have hev2 : ∀ᶠ N : ℕ in atTop, (C * lbar + (ℓ₀ ^ 2)⁻¹ * (C * (1 + lbar))) * ‖b₀‖ *
      (L : ℝ) ^ (-(κ * N)) ≤ 1 / 2 := by
    have := (tendsto_rpow_neg_mul (L := L) hL2 hκ).const_mul
      ((C * lbar + (ℓ₀ ^ 2)⁻¹ * (C * (1 + lbar))) * ‖b₀‖)
    rw [mul_zero] at this
    exact (tendsto_order.1 this).2 (1 / 2) (by norm_num) |>.mono fun N h => h.le
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_ hbd
  filter_upwards [hev1, hev2, eventually_ge_atTop (2 + supNormZ x)] with N hm hu2 hN
  have hN2 : 2 ≤ N := by omega
  have hs : supNormZ x ≤ L ^ (N - 1) := by
    have h1 : supNormZ x < L ^ supNormZ x := Nat.lt_pow_self (by omega)
    have h2 : L ^ supNormZ x ≤ L ^ (N - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hb := ctr_add_prj_ne hL3 (N := N) (by omega) hx0 hs
  have hu : ‖Suscept.utN d L N msq (V₀c msq b₀)‖ ≤ 1 / 2 :=
    (Psi4.utN_le_of_mass hd H.fd hmsq hm hb₀).trans hu2
  have hu0 : 1 + Suscept.utN d L N msq (V₀c msq b₀) ≠ 0 := by
    intro h
    have : Suscept.utN d L N msq (V₀c msq b₀) = -1 := by linear_combination h
    rw [this, norm_neg, norm_one] at hu; norm_num at hu
  have hu1 : 1 / 2 ≤ ‖1 + Suscept.utN d L N msq (V₀c msq b₀)‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-Suscept.utN d L N msq (V₀c msq b₀))
    rw [sub_neg_eq_add, norm_one, norm_neg] at this
    linarith
  have hl : (lbar : ℂ) ≠ 0 := by exact_mod_cast hlb.ne'
  -- translation to `(ctr, ctr + x)`
  have htr := avg_psibar_psi_transl (msq := msq) hmsq (by omega : 1 ≤ N) (V₀c msq b₀)
    (ctr d L N) (0 : Lam d L N) (prj x : Lam d L N)
  rw [zero_add, add_comm (prj x : Lam d L N)] at htr
  rw [← htr, avg_one_decomp (V₀c msq b₀) (lbar : ℂ) (ctr d L N) (ctr d L N + prj x) hd H.fd.hL8
    (by omega) hmsq (H.fd.good N msq hmsq.le) hl hu0]
  have hq := qN_rate H hd hCs hS1 hd3 hmsq.le hb₀ hx0 hN2 hs
  -- the remainder
  have hτ := norm_tau_le (d := d) (L := L) (N := N) hd hmsq
  have hla := la1_bd H hd hCs hS1 hmsq.le hb₀ hb (k := N) le_rfl
  have hlb' := lb1_bd H hd hCs hS1 hmsq.le hb₀ hb (k := N) le_rfl
  have hra := ra1_bd H hd hCs hS1 hmsq.le hb₀ hb (k := N) le_rfl
  have hrb := rb1_bd H hd hCs hS1 hmsq.le hb₀ hb (k := N) le_rfl
  have hθN : (L : ℝ) ^ (-(κ * N)) = th L κ ^ N := rpow_neg_mul_nat (Nat.cast_nonneg _) κ N
  have hKN := (H.fd.obs .one N msq (lbar : ℂ) b₀ (ctr d L N + prj x) hmsq.le
    (by rw [norm_lbar H]; exact hb₀) (le_of_eq (norm_lbar H)) hb N le_rfl).2
  rw [norm_lbar H] at hKN
  have he0 : 0 ≤ C * lbar * ‖b₀‖ * (L : ℝ) ^ (-(κ * N)) := by positivity
  obtain ⟨-, -, hkab⟩ := kOne_bounds H.fd.hℓ₀ H.fd.hA1 he0 (initObs .one (lbar : ℂ)) hKN
  have hℓN : ellj d L ℓ₀ N ^ 2 ≤ ℓ₀ ^ 2 := by
    rw [ellj_sq]
    have := pow_le_one₀ (n := N) (rho_nonneg d L) (rho_le_one hd2 L)
    have h3 : 0 ≤ ℓ₀ ^ 2 := sq_nonneg _
    calc ℓ₀ ^ 2 * rho d L ^ N ≤ ℓ₀ ^ 2 * 1 := mul_le_mul_of_nonneg_left this h3
      _ = ℓ₀ ^ 2 := mul_one _
  set τb := 1 / (msq * Fintype.card (Lam d L N)) with hτb
  have hτb0 : 0 ≤ τb := by
    have := Suscept.card_lam_pos (d := d) (L := L) N
    rw [hτb]; positivity
  set la := laOf .one (Vo1 d L N msq (V₀c msq b₀) (lbar : ℂ) (ctr d L N) (ctr d L N + prj x))
  set lb := lbOf .one (Vo1 d L N msq (V₀c msq b₀) (lbar : ℂ) (ctr d L N) (ctr d L N + prj x))
  set ra := raOf .one (Vo1 d L N msq (V₀c msq b₀) (lbar : ℂ) (ctr d L N) (ctr d L N + prj x))
  set rb := rbOf .one (Vo1 d L N msq (V₀c msq b₀) (lbar : ℂ) (ctr d L N) (ctr d L N + prj x))
  have hX : ‖la * lb - (ra + rb)‖ ≤ Lm lbar C κ Cs b₀ L ^ 2 + 2 * Rm lbar C κ Cs b₀ L := by
    refine (norm_sub_le _ _).trans (add_le_add ?_ ((norm_add_le _ _).trans (by linarith)))
    rw [norm_mul, sq]; exact mul_le_mul hla hlb' (norm_nonneg _) hLm
  set kab := kabOne d L N msq (V₀c msq b₀) (initObs .one (lbar : ℂ)) (ctr d L N)
    (ctr d L N + prj x)
  set τ := tau d L N msq
  have hR : ‖((la * lb - (ra + rb)) * τ + kab) / (lbar : ℂ) ^ 2 /
      (1 + Suscept.utN d L N msq (V₀c msq b₀))‖ ≤
      2 * (((Lm lbar C κ Cs b₀ L ^ 2 + 2 * Rm lbar C κ Cs b₀ L) * τb +
        (ℓ₀ ^ 2 + τb) * (C * lbar * ‖b₀‖ * (L : ℝ) ^ (-(κ * N)))) / lbar ^ 2) := by
    have hl2' : ‖((lbar : ℂ) ^ 2)‖ = lbar ^ 2 := by rw [norm_pow, norm_lbar H]
    have hnum : ‖(la * lb - (ra + rb)) * τ + kab‖ ≤
        (Lm lbar C κ Cs b₀ L ^ 2 + 2 * Rm lbar C κ Cs b₀ L) * τb +
          (ℓ₀ ^ 2 + τb) * (C * lbar * ‖b₀‖ * (L : ℝ) ^ (-(κ * N))) := by
      refine (norm_add_le _ _).trans (add_le_add ?_ (hkab.trans ?_))
      · rw [norm_mul]; exact mul_le_mul hX hτ (norm_nonneg _) (by positivity)
      · exact mul_le_mul_of_nonneg_right (add_le_add hℓN hτ) he0
    have hpos : 0 < ‖1 + Suscept.utN d L N msq (V₀c msq b₀)‖ := by linarith
    rw [norm_div, norm_div, hl2', div_le_iff₀ hpos]
    have h0 : 0 ≤ ((Lm lbar C κ Cs b₀ L ^ 2 + 2 * Rm lbar C κ Cs b₀ L) * τb +
        (ℓ₀ ^ 2 + τb) * (C * lbar * ‖b₀‖ * (L : ℝ) ^ (-(κ * N)))) / lbar ^ 2 := by positivity
    have h1 : ‖(la * lb - (ra + rb)) * τ + kab‖ / lbar ^ 2 ≤
        ((Lm lbar C κ Cs b₀ L ^ 2 + 2 * Rm lbar C κ Cs b₀ L) * τb +
          (ℓ₀ ^ 2 + τb) * (C * lbar * ‖b₀‖ * (L : ℝ) ^ (-(κ * N)))) / lbar ^ 2 :=
      div_le_div_of_nonneg_right hnum hlb2.le
    nlinarith
  calc ‖qN d L .one N msq (V₀c msq b₀) (initObs .one (lbar : ℂ)) (ctr d L N)
          (ctr d L N + prj x) / (lbar : ℂ) ^ 2 +
        ((la * lb - (ra + rb)) * τ + kab) / (lbar : ℂ) ^ 2 /
          (1 + Suscept.utN d L N msq (V₀c msq b₀)) - Qone d L V₀c lbar msq b₀ x‖
      = ‖(qN d L .one N msq (V₀c msq b₀) (initObs .one (lbar : ℂ)) (ctr d L N)
          (ctr d L N + prj x) / (lbar : ℂ) ^ 2 - Qone d L V₀c lbar msq b₀ x) +
        ((la * lb - (ra + rb)) * τ + kab) / (lbar : ℂ) ^ 2 /
          (1 + Suscept.utN d L N msq (V₀c msq b₀))‖ := by ring_nf
    _ ≤ _ := norm_add_le _ _
    _ ≤ bd N := by rw [hbd_def]; exact add_le_add hq hR

end

end Ward
