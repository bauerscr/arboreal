import PtCorr2.Last.LastObsA
import Step2.Map.SplitSmall
import Step2.Flow.FlowThm

/-!
# Route (a1): the `ε`-requirement of the window-end slack

The slack `h0Slack` of the window ends (`Spin2/H0/H0MassFlow`) is `(cNuLast + 1)ǧ + O(ǧ²)` once
`m²|Λ| ≤ ǧ`. The `O(ǧ²)` constant `h0Xc` depends on `L`, `C_f`, `ℓ`, `ρ` and on the constants `K_T`
(`lastOut_zeroT`) and `B` (`EpsZeroSmall`) — none of which is seen by the `ε`-requirement `Eext`
of the master flow (it sees only `L, A, c_R, c_x`). Here:

* `ZeroTK L ρ K`: the conclusion of `lastOut_zeroT` with constant `K`;
* `h0KT L ρ`, `h0B L ρ`: canonical choices (`Classical.choose`) of `K_T` and `B`;
* `h0Xc`: the explicit `O(ǧ²)` constant;
* **`h0EReq L ℓ ρ C_f c_m ε`**: `ε ≤ 4/5`, `(5/4)h0Xc·ε ≤ 1`, `c_με ≤ 1/16`; **`h0EReq_ev`**: it holds
  for all small `ε > 0`. It enters the master flow as the extra requirement `Gext` of
  `flow_master_hyp0LZD` (the internal constants are fixed before `ε` there).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Filter Topology Flow2 Step2.LastN Step2.D2

/-- The conclusion of `lastOut_zeroT` with constant `K`. -/
def ZeroTK (L : ℕ) [NeZero L] (ρ' K : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → 0 ≤ R.ρ → R.ρ ≤ ρ' →
    0 < R.msq → R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) →
  ∀ (Nh : ℕ), Nh + 2 = N → ∀ t : Flow2.Hist.Seq (Xs R),
    ‖(R.msq : ℂ) * ((lastOut R Nh t).Z * zmRaw R (Nh + 1) (lastOut R Nh t).ζ) - 1‖ ≤
      K * R.msq * (L : ℝ) ^ (2 * N)

open Classical in
/-- The canonical `K_T` of `lastOut_zeroT`. -/
def h0KT (L : ℕ) [NeZero L] (ρ : ℝ) : ℝ :=
  if h : ∃ K : ℝ, 0 ≤ K ∧ ZeroTK L ρ K then h.choose else 0

open Classical in
/-- The canonical `B` of `EpsZeroSmall`. -/
def h0B (L : ℕ) (ρ : ℝ) : ℝ :=
  if h : ∃ B : ℝ, 0 ≤ B ∧ EpsZeroSmall Pc L ρ B then h.choose else 0

theorem h0KT_spec {L : ℕ} [NeZero L] {ρ : ℝ} (hZ : ZeroTOk L ρ) :
    0 ≤ h0KT L ρ ∧ ZeroTK L ρ (h0KT L ρ) := by
  have h : ∃ K : ℝ, 0 ≤ K ∧ ZeroTK L ρ K := lastOut_zeroT hZ
  unfold h0KT; rw [dif_pos h]; exact h.choose_spec

theorem h0B_spec {L : ℕ} {ρ : ℝ} (hS : SplitSmall Pc L ρ) :
    0 ≤ h0B L ρ ∧ EpsZeroSmall Pc L ρ (h0B L ρ) := by
  have h : ∃ B : ℝ, 0 ≤ B ∧ EpsZeroSmall Pc L ρ B := hS.2
  unfold h0B; rw [dif_pos h]; exact h.choose_spec

/-- `e₀ = L²C_f e^{L²C_f}` (`E ≤ e₀ǧ²` for `ǧ ≤ 1`). -/
def h0e0 (Lr Cf : ℝ) : ℝ := Lr ^ 2 * Cf * Real.exp (Lr ^ 2 * Cf)
/-- `k = e₀ + C_f` (`κ₀ ≤ kǧ²`). -/
def h0kc (Lr Cf : ℝ) : ℝ := h0e0 Lr Cf + Cf
/-- `x_a = C_fe₀ + ℓ^{-2}k` (`e_a ≤ x_aǧ²`). -/
def h0xa (Lr Cf ℓ : ℝ) : ℝ := Cf * h0e0 Lr Cf + ℓ⁻¹ ^ 2 * h0kc Lr Cf
/-- `y = C_f + x_a` (`a_hi ≤ yǧ`). -/
def h0yc (Lr Cf ℓ : ℝ) : ℝ := Cf + h0xa Lr Cf ℓ
/-- `n₁ = 1 + k + y(1 + K_T)` (`n_hi ≤ n₁ǧ` at `m²|Λ| = ǧ`). -/
def h0n1 (Lr Cf ℓ KT : ℝ) : ℝ := 1 + h0kc Lr Cf + h0yc Lr Cf ℓ * (1 + KT)
/-- **The `O(ǧ²)` constant of the slack**: `h0Slack(G, G) ≤ (cNuLast + 1 + h0Xc·G)G` for `G ≤ 1`. -/
def h0Xc (Lr Cf ℓ KT B ρ : ℝ) : ℝ :=
  h0xa Lr Cf ℓ + h0yc Lr Cf ℓ * KT + h0kc Lr Cf +
    (h0kc Lr Cf + h0yc Lr Cf ℓ * KT) * h0n1 Lr Cf ℓ KT +
    24 * ρ ^ 2 * B * Real.exp (64 / 7 * ρ * B) / Lr ^ 2 * h0n1 Lr Cf ℓ KT ^ 2 +
    64 / 7 * ρ * B * Real.exp (64 / 7 * ρ * B) / Lr ^ 2 * h0yc Lr Cf ℓ * h0n1 Lr Cf ℓ KT

/-- **The `ε`-requirement of the window-end slack.** -/
def h0EReq (L : ℕ) [NeZero L] (ℓ ρ Cf cm ε : ℝ) : Prop :=
  ε ≤ 4 / 5 ∧ 5 / 4 * h0Xc L Cf ℓ (h0KT L ρ) (h0B L ρ) ρ * ε ≤ 1 ∧
    cmu ((L : ℝ) ^ 2) cm * ε ≤ 1 / 16

theorem h0EReq_ev (L : ℕ) [NeZero L] (ℓ ρ Cf cm : ℝ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), h0EReq L ℓ ρ Cf cm ε := by
  filter_upwards [ev_lin 1 (by norm_num : (0 : ℝ) < 4 / 5),
    ev_lin (5 / 4 * h0Xc L Cf ℓ (h0KT L ρ) (h0B L ρ) ρ) one_pos,
    ev_lin (cmu ((L : ℝ) ^ 2) cm) (by norm_num : (0 : ℝ) < 1 / 16)] with ε h1 h2 h3
  exact ⟨by linarith, h2, h3⟩

end

end Spin2
