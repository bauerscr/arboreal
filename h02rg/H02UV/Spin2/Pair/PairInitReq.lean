import Spin2.Case2.Case2Rel
import PtCorr2.Obs.ObsHistU

/-!
# The requirements on `A` and `ε` of the unreduced `ab` chain

* **`kabAReq`**: the constants of `KObsBoundsU` exist at `(L, A)` and `θ₀ ≤ 1/216`
  (`kabAReq_ev`, from `kobs_bounds_U` and `kθ0_le` applied to `3C₀`).
* **`kabCond`**: the smallness conditions of `kab_hist`/`pairInit_traj` at `ε` for given
  `c₁ = 8B`, `c_W` (`kabCond_ev`: eventually as `ε ↓ 0`).
* **`c2RelReqU`**: `c2RelReq` with `kabCond` inside the scope of the constants `C₁` (of
  `KObsBounds`) and `C₁w` (of `WObsBounds`) (`c2RelReqU_ev`).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Filter Topology

/-- The requirement on `A` of the unreduced `ab` chain. -/
def kabAReq (C₀ η : ℝ) (Lu : ℕ) (L : ℕ) (A : ℝ) : Prop :=
  ∀ [NeZero L], Lu ≤ L →
    (∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧ KObsBoundsU L A C₀ η ε₀ C₁) ∧ kθ0 L A C₀ η ≤ 1 / 216

theorem kθ0_three (L : ℕ) (A C₀ η : ℝ) : kθ0 L A (3 * C₀) η = 3 * kθ0 L A C₀ η := by
  unfold kθ0; ring

theorem kabAReq_ev {C₀ η : ℝ} {L₀ Lu : ℕ} (hC₀ : 0 ≤ C₀) (hη : 0 < η)
    (hk : ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
      ∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧ KObsBoundsU L A C₀ η ε₀ C₁)
    (hLu : L₀ ≤ Lu) (hLu' : 144 * (3 * C₀) + 1 ≤ (Lu : ℝ)) (L : ℕ) :
    ∃ A₀ : ℝ, ∀ A, A₀ ≤ A → kabAReq C₀ η Lu L A := by
  by_cases hL : L ≠ 0 ∧ Lu ≤ L
  · haveI : NeZero L := ⟨hL.1⟩
    obtain ⟨A₀, -, hA⟩ := hk L (hLu.trans hL.2)
    refine ⟨max A₀ (2 * (144 * (3 * C₀) + 1) ^ η⁻¹), fun A hA' _ _ =>
      ⟨hA A (le_of_max_le_left hA'), ?_⟩⟩
    have h := kθ0_le (by linarith : 0 ≤ 3 * C₀) hη (hLu'.trans (by exact_mod_cast hL.2))
      (le_of_max_le_right hA')
    rw [kθ0_three] at h
    linarith
  · exact ⟨0, fun A _ inst hLL => absurd ⟨inst.out, hLL⟩ hL⟩

/-- The smallness conditions of the unreduced `ab` chain (`c = c_R`, `c' = c_x`). -/
def kabCond (L : ℕ) [NeZero L] (A C₀ η c₁ cW c c' ε : ℝ) : Prop :=
  ∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧ KObsBoundsU L A C₀ η ε₀ C₁ ∧
    2 * (c * ε) ≤ ε₀ ∧
    8 * (c' + c₁ + 10 * kB2 (kθ0 L A C₀ η) C₁ c' c₁) * (c * ε) ^ 3 ≤ 1 ∧
    8 * (c' + c₁ + 10 * kB2 (kθ0 L A C₀ η) C₁ c' c₁) * (c * ε) ^ 3 ≤ ε₀ ∧
    8 * kθ0 L A C₀ η + 16 * C₁ * (c * ε) +
      8 * C₁ * (8 * (c' + c₁ + 10 * kB2 (kθ0 L A C₀ η) C₁ c' c₁) * (c * ε) ^ 3) ≤ 1 / 10 ∧
    A ^ 4 * (c' * (c * ε) ^ 3 + c₁ * (c * ε) ^ 2 * (2 * cW) +
      10 * kB2 (kθ0 L A C₀ η) C₁ c' c₁ * (c * ε) * (2 * cW) ^ 2) ≤ 1

theorem kabCond_ev (L : ℕ) [NeZero L] {A C₀ η : ℝ} (c₁ cW c c' : ℝ)
    (hK : ∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧ KObsBoundsU L A C₀ η ε₀ C₁)
    (hθ : kθ0 L A C₀ η ≤ 1 / 216) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), kabCond L A C₀ η c₁ cW c c' ε := by
  obtain ⟨ε₀, C₁, hε₀, hC₁, hKB⟩ := hK
  set X := c' + c₁ + 10 * kB2 (kθ0 L A C₀ η) C₁ c' c₁
  set B₂ := kB2 (kθ0 L A C₀ η) C₁ c' c₁
  filter_upwards [ev_small (f := fun ε => 2 * (c * ε)) (c := ε₀) (by fun_prop) (by simpa using hε₀),
    ev_small (f := fun ε => 8 * X * (c * ε) ^ 3) (c := 1) (by fun_prop) (by simp),
    ev_small (f := fun ε => 8 * X * (c * ε) ^ 3) (c := ε₀) (by fun_prop) (by simpa using hε₀),
    ev_small (f := fun ε => 8 * kθ0 L A C₀ η + 16 * C₁ * (c * ε) +
      8 * C₁ * (8 * X * (c * ε) ^ 3)) (c := 1 / 10) (by fun_prop) (by simp; linarith),
    ev_small (f := fun ε => A ^ 4 * (c' * (c * ε) ^ 3 + c₁ * (c * ε) ^ 2 * (2 * cW) +
      10 * B₂ * (c * ε) * (2 * cW) ^ 2)) (c := 1) (by fun_prop) (by simp)]
    with ε h1 h2 h3 h4 h5
  exact ⟨ε₀, C₁, hε₀, hC₁, hKB, h1, h2, h3, h4, h5⟩

/-- `c2RelReq` with the smallness conditions of the unreduced `ab` chain. -/
def c2RelReqU (Cq Cl cS C₀ η Kw : ℝ) (Lo : ℕ) (Cpf εpf : ℕ → ℝ) (C₀u ηu : ℝ) (Lu : ℕ)
    (L : ℕ) (A c c' ε : ℝ) : Prop :=
  ∀ [NeZero L], Lo ≤ L → obsAReq C₀ η Lo L A → Lu ≤ L → kabAReq C₀u ηu Lu L A →
    ∃ ζbar K cS2 : ℝ, 0 < ζbar ∧ 0 ≤ K ∧ 0 ≤ cS2 ∧ LcProp L ζbar K cS2 ∧
      2 * ceff L c * ε ≤ ζbar ∧ c * ε ≤ 1 ∧ 8 * c' * ε ≤ 1 ∧ betaL L * ε ≤ 1 / 2 ∧
      c2Bp Cq Cl cS L K cS2 c c' * ε ≤ 1 / 8 ∧
      (max (c2Bp Cq Cl cS L K cS2 c c') 0 + 1) * ε ≤ 1 / 7 ∧
      4 * ceff L (max c 2) * (max (c2Bp Cq Cl cS L K cS2 c c') 0 + 1) * ε ≤ 1 / 2 ∧
      c * ε ≤ εpf L ∧
    ∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧ KObsBounds L A C₀ η ε₀ C₁ ∧
      C₁ * (2 + 2 * (8 * c') + 64 * kB (kθ0 L A C₀ η) C₁ (8 * c')) * (c * ε) ≤ 1 / 72 ∧
      c * ε ≤ ε₀ ∧ (8 * c' + 64 * kB (kθ0 L A C₀ η) C₁ (8 * c')) * (c * ε) ≤ ε₀ ∧
    ∃ C₁w ε₁ : ℝ, 0 ≤ C₁w ∧ 0 < ε₁ ∧ WObsBounds L Kw C₁w ε₁ ∧ C₁w * (c * ε) ≤ 1 / 12 ∧
      c * ε ≤ ε₁ ∧
      c2dF L (Cpf L) (c2Bp Cq Cl cS L K cS2 c c') C₁w (kB (kθ0 L A C₀ η) C₁ (8 * c')) c *
        c ^ 2 * (4 / betaL L) * ε ≤ 1 / 8 ∧
      kabCond L A C₀u ηu (8 * kB (kθ0 L A C₀ η) C₁ (8 * c')) (3 * C₁w + 1) c c' ε

theorem c2RelReqU_ev (Cq Cl cS : ℝ) {C₀ η Kw C₀u ηu : ℝ} {L₀ Lo Lu : ℕ} (Cpf εpf : ℕ → ℝ)
    (hw : ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ C₁ ε₁ : ℝ, 0 ≤ C₁ ∧ 0 < ε₁ ∧ WObsBounds L Kw C₁ ε₁)
    (hLo : L₀ ≤ Lo) (h7 : 7 ≤ Lo) (hεp : ∀ (L : ℕ) [NeZero L], Lo ≤ L → 0 < εpf L)
    (L : ℕ) (A c c' : ℝ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), c2RelReqU Cq Cl cS C₀ η Kw Lo Cpf εpf C₀u ηu Lu L A c c' ε := by
  by_cases hL : L ≠ 0 ∧ Lo ≤ L
  · haveI : NeZero L := ⟨hL.1⟩
    by_cases hA : obsAReq C₀ η Lo L A
    · by_cases hU : Lu ≤ L ∧ kabAReq C₀u ηu Lu L A
      · obtain ⟨⟨ε₀, C₁, hε₀, hC₁, hKB⟩, -⟩ := hA hL.2
        obtain ⟨hKu, hθu⟩ := hU.2 hU.1
        obtain ⟨C₁w, ε₁, hC₁w, hε₁, hWB⟩ := hw L (hLo.trans hL.2)
        obtain ⟨ζbar, hζ, K, cS2, hK, hcS2, hLc⟩ := lcProp_of (L := L) (h7.trans hL.2)
        set B' := c2Bp Cq Cl cS L K cS2 c c'
        set Bk := kB (kθ0 L A C₀ η) C₁ (8 * c')
        filter_upwards [ev_lin (2 * ceff L c) hζ, ev_lin c one_pos, ev_lin (8 * c') one_pos,
          ev_lin (betaL L) (by norm_num : (0 : ℝ) < 1 / 2),
          ev_lin B' (by norm_num : (0 : ℝ) < 1 / 8),
          ev_lin (max B' 0 + 1) (by norm_num : (0 : ℝ) < 1 / 7),
          ev_lin (4 * ceff L (max c 2) * (max B' 0 + 1)) (by norm_num : (0 : ℝ) < 1 / 2),
          ev_lin c (hεp L hL.2),
          ev_lin (C₁ * (2 + 2 * (8 * c') + 64 * Bk) * c) (by norm_num : (0 : ℝ) < 1 / 72),
          ev_lin c hε₀, ev_lin ((8 * c' + 64 * Bk) * c) hε₀,
          ev_lin (C₁w * c) (by norm_num : (0 : ℝ) < 1 / 12), ev_lin c hε₁,
          ev_lin (c2dF L (Cpf L) B' C₁w Bk c * c ^ 2 * (4 / betaL L))
            (by norm_num : (0 : ℝ) < 1 / 8),
          kabCond_ev L (8 * Bk) (3 * C₁w + 1) c c' hKu hθu]
          with ε h1 h2 h3 h4 h5 h6 h7' h8 h9 h10 h11 h12 h13 h14 h15
        intro _ _ _ _ _
        exact ⟨ζbar, K, cS2, hζ, hK, hcS2, hLc, h1, h2, h3, h4, h5, h6, h7', h8, ε₀, C₁, hε₀, hC₁,
          hKB, by rw [← mul_assoc]; exact h9, h10, by rw [← mul_assoc]; exact h11, C₁w, ε₁, hC₁w,
          hε₁, hWB, by rw [← mul_assoc]; exact h12, h13, h14, h15⟩
      · exact Eventually.of_forall fun _ _ _ _ hLu hAu => absurd ⟨hLu, hAu⟩ hU
    · exact Eventually.of_forall fun _ _ _ hA' => absurd (fun (_ : NeZero L) => hA') hA
  · exact Eventually.of_forall fun _ inst hLL _ => absurd ⟨inst.out, hLL⟩ hL

end

end Spin2
