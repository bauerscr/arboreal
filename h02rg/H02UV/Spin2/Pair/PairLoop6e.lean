import Spin2.Pair.PairLoop6d
import Spin2.Pair.PairESz8

/-!
# The constant loop, per scale (5): the per-scale bound for the explicit sequences

**`pl6_item_le`**: along every admissible trajectory of `MasterFacts`, for every `x` with
`1 ≤ j_x ≤ N_h`, every path `w` from `0` to `x` with `|w| ≤ 2|x|_∞` and every `j_x ≤ k ≤ N_h`, the
summand of the first summability condition of `pairJointSizesP3_of_VS` (the explicit sequences of
`Spin2/Pair/PairESz4`, `Spin2/Pair/PairESz6`) satisfies

`s_k ≤ V·C_E·NF(k) + [k = N_h]·V·C_N·m̄·cε`,  `NF(k) = 2^{-(k-j)}k₀ + m̄(∑_{j≤i<k}2^{-(k-i)}r_i² + r_k²)`,

with `V = ‖M_{j_x}‖ǧ_{j_x}`, `r_i = c·max(ǧ_i, 0)`, `k₀ = c_u(2ι_WA)^{(L+18)²}` and the explicit
constants **`pl6CE`** (`= C₁ + … + C₅`, one per item group, `Spin2/Pair/PairLoop6c–d`) and **`pl6CN`**
(the `k = N_h` vertex term). The `ε`-requirements used: **`C₁k(3 + 16c_x)·cε ≤ 1/72`** (the decay
`θ = 8(θ₀ + C₁k(3+16c_x)cε) ≤ 2/9` of the small-set recursion, `θρ ≤ 1/2`) and
**`(1 + c_W(L)cε)^{L²} ≤ 2`** (the product part of `𝒲'`).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs2

/-! ### The constants -/

theorem pl6As_nonneg {L : ℕ} {c : ℝ} (h : 0 ≤ c) : 0 ≤ pl6As L c := by
  have hQ : 0 ≤ Step2.Q1 2 := le_trans zero_le_one (one_le_Q1 (d := 2) one_le_two)
  have hN : 0 ≤ Step2.cNear 2 L := Nat.cast_nonneg _
  unfold pl6As
  exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hN) (sq_nonneg _)) (mul_nonneg hQ h)

/-- `C_E` with the master constants. -/
def pl6CEM {L : ℕ} [NeZero L] (M : MasterFacts L) (C₁k C₁w C₁w' Clo Clb : ℝ) : ℝ :=
  pl6CE L (KM4 2 Ccut2) (Obs2.KG 2 Ccut2 4) (2 * (cNb2 : ℝ) * (cSm2 : ℝ)) (locK 2) cQab
    (kB (kθ0 L M.core.A M.core.C₀a M.core.ηa) C₁k (8 * cx M.core.κ M.core.cT)) (4 * C₁w + 1)
    (4 * C₁w' + 1) Clo (cWblk 2 L Clb) (max M.core.B' 0 + M.core.ce) M.core.ce

/-- `C_N` with the master constants. -/
def pl6CNM (L : ℕ) (C₁w : ℝ) : ℝ := pl6CN L (KM4 2 Ccut2) (4 * C₁w + 1)

/-- `r_i = c·max(ǧ_i, 0)`. -/
def pl6r {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (m b μ₀ c : ℝ)
    (i : ℕ) : ℝ :=
  c * max (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ i).1 0

/-- The seed `k₀ = c_u(2ι_WA)^{(L+18)²}`. -/
def pl6k0 {L : ℕ} [NeZero L] (M : MasterFacts L) (cu : ℝ) : ℝ :=
  cu * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)

end

end Spin2
