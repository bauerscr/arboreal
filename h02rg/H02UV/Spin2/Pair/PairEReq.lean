import Spin2.Master.AbwReq
import Spin2.Pair.PairInitReq
import Spin2.Pair.PairErrAB3
import PtCorr2.Pair.PairESz1
import PtCorr2.Pair.PairEStep1

/-!
# The pair `ε`-requirements at canonical witnesses (`pairEReq`)

The three requirements of the closed pair loop (`Spin2/Pair/PairLoop6g`, `Spin2/Pair/PairFinal4`)

1. `C₁k(2 + 2·8c_x + 1)·cε ≤ 1/72` (the `hsm` of `abwEReq`),
2. `(1 + c_W(L)cε)^{L²} ≤ 2`, `c_W(L) = cWblk 2 L C_lb`,
3. `X·Θ ≤ 1/2`, `X = crErr2 1 c_δc² (4/β_L) c_t (max B' 0) 0`, `Θ = C_E(6c²G₂ + 2cε) + C_Ncε`,

involve constants which were `∃`-witnesses chosen after `ε` (`C₁k, C₁w` of `abwEReq`; `K, cS2, C₁,
C₁w` of `c2RelReqU` inside `c_δ` and `B'`) or absolute (`C_lo, C_lb` of `wpo_bounds_AB`).

* `C_lo, C_lb` are made canonical: **`cwClo`**, **`cwClb`** (`Classical.choose` of
  `wpo_bounds_AB`), **`cw_wpo_spec`**.
* **`pairEReq`** (an `Eext`-requirement at `(L, A, c, c', ε)`): **one** `∃` over all the
  `ε`-independent witnesses (`ζbar K cS2 ε₀ C₁ C₁w ε₁` of `c2RelReqU` and `ε₀a C₁ka C₁wa ε₁a` of
  `abwEReq`) with all their conditions (`c2RelReqUB`, `abwEReqB`) **and** 2., 3. at these witnesses
  (with `C₁w' = C₁wa`). The master construction takes the corresponding `MasterCore` fields from
  `pairEReq`, so the requirements constrain the exported constants.
* **`pairEReq_ev`**: eventually in `ε ↓ 0` (the witnesses are fixed at `(L, A)` before `ε`; 2. and 3.
  are continuous in `ε` with value `1 < 2`, `0 < 1/2` at `ε = 0`).

The pure constant definitions of the loop (`pl6ρ`, `pl6aQ`, …, `pl6CE`, `pl6CN`; formerly in
`Spin2/Pair/PairLoop6a`, `Spin2/Pair/PairLoop6e`) and `cQab` (formerly `Spin2/Pair/PairEStep3`) are moved here
(same names and bodies).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Filter Topology

/-! ### The constants of the loop (moved) -/

/-- `ρ = (6/5)(64/49)`, the combined growth of `s_i²β_{i+1}` downwards. -/
def pl6ρ : ℝ := 6 / 5 * (64 / 49)

/-- `a_Q = 8(128/49 + 4ρ(64/49)Bc_W)`: the small-set sizes in units of `V s_i²β_{i+1}G₀(i)`. -/
def pl6aQ (B cWc : ℝ) : ℝ := 8 * (128 / 49 + 4 * pl6ρ * (64 / 49) * B * cWc)

/-- `A_s = 2c_{near}Q₁² + Q₁c_W`: the `s_O` prefactor. -/
def pl6As (L : ℕ) (cWc : ℝ) : ℝ := 2 * Step2.cNear 2 L * Step2.Q1 2 ^ 2 + Step2.Q1 2 * cWc

/-- `c_Q = c_{NS}a_Q` (`κ^Q = 2c_Nc_S·kszQ`). -/
def pl6cQ (cNS B cWc : ℝ) : ℝ := cNS * pl6aQ B cWc

/-- `c_S = 2L²(128/49)L²A_s` (`κ^S = 2L²·kszS`). -/
def pl6cS (L : ℕ) (cWc : ℝ) : ℝ := 2 * (L : ℝ) ^ 2 * (128 / 49 * (L : ℝ) ^ 2 * pl6As L cWc)

/-- `c_M = K_{M4}(c_Q/L² + (6/5)c_S)`. -/
def pl6cM (L : ℕ) (K4 cNS B cWc : ℝ) : ℝ :=
  K4 * (pl6cQ cNS B cWc / (L : ℝ) ^ 2 + 6 / 5 * pl6cS L cWc)

/-- `c_γ = L((3/4)L²c_M + (2K_G/L + 243/64)c_Q + (2K_G + 3)c_S)`. -/
def pl6cG (L : ℕ) (K4 KG cNS B cWc : ℝ) : ℝ :=
  (L : ℝ) * (3 / 4 * (L : ℝ) ^ 2 * pl6cM L K4 cNS B cWc +
    (2 * KG / (L : ℝ) + 243 / 64) * pl6cQ cNS B cWc + (2 * KG + 3) * pl6cS L cWc)

/-- `c_O = 2(1 + C_{lo}L²)A_s'`. -/
def pl6cO (L : ℕ) (Clo cWc' : ℝ) : ℝ := 2 * (1 + Clo * (L : ℝ) ^ 2) * pl6As L cWc'

/-- **The five group constants and `C_E = C₁ + … + C₅`.** Arguments: `K_{M4}`, `K_G`,
`c_{NS} = 2c_Nc_S`, `K = locK`, `c_{Qab}`, `B = kB(θ₀, C₁k, 8c_x)`, `c_W = 4C₁w+1`,
`c_W' = 4C₁w'+1`, `C_{lo}`, `c_W(L) = cWblk(C_{lb})`, `c_B = max(B',0) + c_t`, `c_t`. -/
def pl6CE (L : ℕ) (K4 KG cNS lK cQab B cWc cWc' Clo cW cB ct : ℝ) : ℝ :=
  -- `C₁` (`s^q`)
  2 * Step2.Q1 2 * cQab * pl6aQ B cWc +
  -- `C₂` (`s^w`)
  4 * (L : ℝ) ^ 4 * cW * pl6cO L Clo cWc' * (6 / 5) * (64 / 49) ^ 2 +
  -- `C₃` (`s^p`)
  (12 * K4 * pl6cQ cNS B cWc / (L : ℝ) ^ 2 + 24 / 5 * cB * K4 * pl6cS L cWc) +
  -- `C₄` (`s^g`)
  8 * (2 * ((L : ℝ) + 39) ^ 2 * 8 ^ 4) * (256 * pl6cG L K4 KG cNS B cWc / (L : ℝ) +
    192 * pl6cM L K4 cNS B cWc) +
  -- `C₅` (`s^m`)
  (16 * ct * pl6cM L K4 cNS B cWc +
    2560 * lK ^ 2 * (4 * (2 * ((L : ℝ) + 39) ^ 2 * 9 ^ 4) *
      ((9 / 2 : ℝ) ^ 4 * (6 / 5) * pl6cG L K4 KG cNS B cWc / (L : ℝ) +
        192 * pl6cM L K4 cNS B cWc)) +
    2560 * lK ^ 2 * (2 * (L : ℝ) ^ 4 * pl6cO L Clo cWc' * cW * (64 / 49) * (6 / 5)))

/-- **The `k = N_h` vertex constant** `C_N = (27/5)K_{M4}c_S`. -/
def pl6CN (L : ℕ) (K4 cWc : ℝ) : ℝ := 27 / 5 * K4 * pl6cS L cWc

/-- The constant of `PtCorr2.Tj_Q2O_ab_le` (`d = 2`). -/
def cQab : ℝ := Classical.choose (PtCorr2.Tj_Q2O_ab_le (d := 2) one_le_two)

/-! ### Canonical `C_lo`, `C_lb` -/

/-- The canonical `C_lo` of `wpo_bounds_AB`. -/
def cwClo : ℝ := Classical.choose PtCorr2.wpo_bounds_AB

/-- The canonical `C_lb` of `wpo_bounds_AB`. -/
def cwClb : ℝ := Classical.choose (Classical.choose_spec PtCorr2.wpo_bounds_AB)

theorem cw_wpo_spec : 0 ≤ cwClo ∧ 0 ≤ cwClb ∧ ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    WpOBoundsAB L cwClo cwClb :=
  Classical.choose_spec (Classical.choose_spec PtCorr2.wpo_bounds_AB)

/-! ### The requirement -/

/-- The loop error factor `X = crErr2 1 (c_δc²) (4/β_L) c_t (max B' 0) 0` in raw constants
(`c_δ = c2dF L C_p B' C₁w B_k c`, `c_t = ceff L c`). -/
def pl6XR (L : ℕ) (Cp Bp C₁w Bk c : ℝ) : ℝ :=
  crErr2 1 (c2dF L Cp Bp C₁w Bk c * c ^ 2) (4 / betaL L) (ceff L c) (max Bp 0) 0

/-- The loop factor `Θ = C_E(6c²G₂ + 2cε) + C_Ncε` in raw constants. -/
def pl6ΘR (L : ℕ) (A C₀a ηa c' C₁k C₁w C₁w' Clo Clb Bp c ε : ℝ) : ℝ :=
  pl6CE L (Obs2.KM4 2 Ccut2) (Obs2.KG 2 Ccut2 4) (2 * (cNb2 : ℝ) * (cSm2 : ℝ)) (Obs2.locK 2) cQab
      (kB (kθ0 L A C₀a ηa) C₁k (8 * c')) (4 * C₁w + 1) (4 * C₁w' + 1) Clo (cWblk 2 L Clb)
      (max Bp 0 + ceff L c) (ceff L c) *
    (6 * c ^ 2 * (4 * ε / betaL L + ε ^ 2) + 2 * c * ε) +
  pl6CN L (Obs2.KM4 2 Ccut2) (4 * C₁w + 1) * (c * ε)

/-- The conditions of `abwEReq` at given witnesses. -/
def abwEReqB (C₀ η Kw : ℝ) (L : ℕ) [NeZero L] (A c c' ε ε₀ C₁ C₁w ε₁ : ℝ) : Prop :=
  0 < ε₀ ∧ 0 ≤ C₁ ∧ KObsBoundsABL L A C₀ η ε₀ C₁ ∧
    C₁ * (2 + 2 * (8 * c') + 1) * (c * ε) ≤ 1 / 72 ∧
    c * ε ≤ ε₀ ∧ (8 * c' + 1) * (c * ε) ≤ ε₀ ∧
    32 * kB (kθ0 L A C₀ η) C₁ (8 * c') * (c * ε) ^ 2 ≤ 1 ∧
    0 ≤ C₁w ∧ 0 < ε₁ ∧ WObsBoundsAB L Kw C₁w ε₁ ∧ C₁w * (c * ε) ≤ 1 / 12 ∧ c * ε ≤ ε₁

/-- The conditions of `c2RelReqU` at given witnesses. -/
def c2RelReqUB (Cq Cl cS C₀ η Kw : ℝ) (Cpf εpf : ℕ → ℝ) (C₀u ηu : ℝ) (L : ℕ) [NeZero L]
    (A c c' ε ζbar K cS2 ε₀ C₁ C₁w ε₁ : ℝ) : Prop :=
  0 < ζbar ∧ 0 ≤ K ∧ 0 ≤ cS2 ∧ LcProp L ζbar K cS2 ∧
    2 * ceff L c * ε ≤ ζbar ∧ c * ε ≤ 1 ∧ 8 * c' * ε ≤ 1 ∧ betaL L * ε ≤ 1 / 2 ∧
    c2Bp Cq Cl cS L K cS2 c c' * ε ≤ 1 / 8 ∧
    (max (c2Bp Cq Cl cS L K cS2 c c') 0 + 1) * ε ≤ 1 / 7 ∧
    4 * ceff L (max c 2) * (max (c2Bp Cq Cl cS L K cS2 c c') 0 + 1) * ε ≤ 1 / 2 ∧
    c * ε ≤ εpf L ∧
    0 < ε₀ ∧ 0 ≤ C₁ ∧ KObsBounds L A C₀ η ε₀ C₁ ∧
    C₁ * (2 + 2 * (8 * c') + 64 * kB (kθ0 L A C₀ η) C₁ (8 * c')) * (c * ε) ≤ 1 / 72 ∧
    c * ε ≤ ε₀ ∧ (8 * c' + 64 * kB (kθ0 L A C₀ η) C₁ (8 * c')) * (c * ε) ≤ ε₀ ∧
    0 ≤ C₁w ∧ 0 < ε₁ ∧ WObsBounds L Kw C₁w ε₁ ∧ C₁w * (c * ε) ≤ 1 / 12 ∧
    c * ε ≤ ε₁ ∧
    c2dF L (Cpf L) (c2Bp Cq Cl cS L K cS2 c c') C₁w (kB (kθ0 L A C₀ η) C₁ (8 * c')) c *
      c ^ 2 * (4 / betaL L) * ε ≤ 1 / 8 ∧
    kabCond L A C₀u ηu (8 * kB (kθ0 L A C₀ η) C₁ (8 * c')) (3 * C₁w + 1) c c' ε

/-- **The pair requirement on `ε`** (`c = c_R`, `c' = c_x`): one set of witnesses for `c2RelReqU`
and `abwEReq`, with the product condition and the loop condition at these witnesses. -/
def pairEReq (Cq Cl cS C₀ η Kw : ℝ) (Lo : ℕ) (Cpf εpf : ℕ → ℝ) (C₀u ηu : ℝ) (Lu : ℕ)
    (C₀a ηa Kwa : ℝ) (La : ℕ) (L : ℕ) (A c c' ε : ℝ) : Prop :=
  ∀ [NeZero L], Lo ≤ L → obsAReq C₀ η Lo L A → Lu ≤ L → kabAReq C₀u ηu Lu L A →
    La ≤ L → abwAReq C₀a ηa La L A →
    ∃ ζbar K cS2 ε₀ C₁ C₁w ε₁ ε₀a C₁ka C₁wa ε₁a : ℝ,
      c2RelReqUB Cq Cl cS C₀ η Kw Cpf εpf C₀u ηu L A c c' ε ζbar K cS2 ε₀ C₁ C₁w ε₁ ∧
      abwEReqB C₀a ηa Kwa L A c c' ε ε₀a C₁ka C₁wa ε₁a ∧
      (1 + cWblk 2 L cwClb * (c * ε)) ^ (L ^ 2) ≤ 2 ∧
      pl6XR L (Cpf L) (c2Bp Cq Cl cS L K cS2 c c') C₁w (kB (kθ0 L A C₀ η) C₁ (8 * c')) c *
        pl6ΘR L A C₀a ηa c' C₁ka C₁wa C₁wa cwClo cwClb (c2Bp Cq Cl cS L K cS2 c c') c ε ≤ 1 / 2

theorem pairEReq_ev (Cq Cl cS : ℝ) {C₀ η Kw C₀u ηu C₀a ηa Kwa : ℝ} {L₀ Lo Lu L₀a La : ℕ}
    (Cpf εpf : ℕ → ℝ)
    (hw : ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ C₁ ε₁ : ℝ, 0 ≤ C₁ ∧ 0 < ε₁ ∧ WObsBounds L Kw C₁ ε₁)
    (hLo : L₀ ≤ Lo) (h7 : 7 ≤ Lo) (hεp : ∀ (L : ℕ) [NeZero L], Lo ≤ L → 0 < εpf L)
    (hwa : ∀ (L : ℕ) [NeZero L], L₀a ≤ L → ∃ C₁ ε₁ : ℝ, 0 ≤ C₁ ∧ 0 < ε₁ ∧
      WObsBoundsAB L Kwa C₁ ε₁)
    (hLa : L₀a ≤ La) (L : ℕ) (A c c' : ℝ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      pairEReq Cq Cl cS C₀ η Kw Lo Cpf εpf C₀u ηu Lu C₀a ηa Kwa La L A c c' ε := by
  by_cases hL : L ≠ 0 ∧ Lo ≤ L ∧ La ≤ L
  · haveI : NeZero L := ⟨hL.1⟩
    by_cases hA : obsAReq C₀ η Lo L A ∧ (Lu ≤ L ∧ kabAReq C₀u ηu Lu L A) ∧ abwAReq C₀a ηa La L A
    · obtain ⟨hA, hU, hAa⟩ := hA
      obtain ⟨⟨ε₀, C₁, hε₀, hC₁, hKB⟩, -⟩ := hA hL.2.1
      obtain ⟨hKu, hθu⟩ := hU.2 hU.1
      obtain ⟨C₁w, ε₁, hC₁w, hε₁, hWB⟩ := hw L (hLo.trans hL.2.1)
      obtain ⟨ζbar, hζ, K, cS2, hK, hcS2, hLc⟩ := lcProp_of (L := L) (h7.trans hL.2.1)
      obtain ⟨⟨ε₀a, C₁a, hε₀a, hC₁a, hKBa⟩, -⟩ := hAa hL.2.2
      obtain ⟨C₁wa, ε₁a, hC₁wa, hε₁a, hWBa⟩ := hwa L (hLa.trans hL.2.2)
      set B' := c2Bp Cq Cl cS L K cS2 c c'
      set Bk := kB (kθ0 L A C₀ η) C₁ (8 * c')
      set X := pl6XR L (Cpf L) B' C₁w Bk c
      filter_upwards [ev_lin (2 * ceff L c) hζ, ev_lin c one_pos, ev_lin (8 * c') one_pos,
        ev_lin (betaL L) (by norm_num : (0 : ℝ) < 1 / 2),
        ev_lin B' (by norm_num : (0 : ℝ) < 1 / 8),
        ev_lin (max B' 0 + 1) (by norm_num : (0 : ℝ) < 1 / 7),
        ev_lin (4 * ceff L (max c 2) * (max B' 0 + 1)) (by norm_num : (0 : ℝ) < 1 / 2),
        ev_lin c (hεp L hL.2.1),
        ev_lin (C₁ * (2 + 2 * (8 * c') + 64 * Bk) * c) (by norm_num : (0 : ℝ) < 1 / 72),
        ev_lin c hε₀, ev_lin ((8 * c' + 64 * Bk) * c) hε₀,
        ev_lin (C₁w * c) (by norm_num : (0 : ℝ) < 1 / 12), ev_lin c hε₁,
        ev_lin (c2dF L (Cpf L) B' C₁w Bk c * c ^ 2 * (4 / betaL L))
          (by norm_num : (0 : ℝ) < 1 / 8),
        kabCond_ev L (8 * Bk) (3 * C₁w + 1) c c' hKu hθu,
        ev_lin (C₁a * (2 + 2 * (8 * c') + 1) * c) (by norm_num : (0 : ℝ) < 1 / 72),
        ev_lin c hε₀a, ev_lin ((8 * c' + 1) * c) hε₀a,
        ev_small (f := fun ε => 32 * kB (kθ0 L A C₀a ηa) C₁a (8 * c') * (c * ε) ^ 2) (c := 1)
          (by fun_prop) (by simp),
        ev_lin (C₁wa * c) (by norm_num : (0 : ℝ) < 1 / 12), ev_lin c hε₁a,
        ev_small (f := fun ε => (1 + cWblk 2 L cwClb * (c * ε)) ^ (L ^ 2)) (c := 2)
          (by fun_prop) (by simp),
        ev_small (f := fun ε => X * pl6ΘR L A C₀a ηa c' C₁a C₁wa C₁wa cwClo cwClb B' c ε)
          (c := 1 / 2) (by unfold pl6ΘR; fun_prop) (by simp [pl6ΘR])]
        with ε h1 h2 h3 h4 h5 h6 h7' h8 h9 h10 h11 h12 h13 h14 h15 a1 a2 a3 a4 a5 a6 hp hX
      intro _ _ _ _ _ _ _
      exact ⟨ζbar, K, cS2, ε₀, C₁, C₁w, ε₁, ε₀a, C₁a, C₁wa, ε₁a,
        ⟨hζ, hK, hcS2, hLc, h1, h2, h3, h4, h5, h6, h7', h8, hε₀, hC₁, hKB,
          by rw [← mul_assoc]; exact h9, h10, by rw [← mul_assoc]; exact h11, hC₁w, hε₁, hWB,
          by rw [← mul_assoc]; exact h12, h13, h14, h15⟩,
        ⟨hε₀a, hC₁a, hKBa, by rw [← mul_assoc]; exact a1, a2, by rw [← mul_assoc]; exact a3, a4,
          hC₁wa, hε₁a, hWBa, by rw [← mul_assoc]; exact a5, a6⟩, hp, hX⟩
    · exact Eventually.of_forall fun _ _ _ hA' hLu hAu _ hAa' =>
        absurd ⟨hA', ⟨hLu, hAu⟩, hAa'⟩ hA
  · exact Eventually.of_forall fun _ inst hLo' _ _ _ hLa' _ => absurd ⟨inst.out, hLo', hLa'⟩ hL

end

end Spin2
