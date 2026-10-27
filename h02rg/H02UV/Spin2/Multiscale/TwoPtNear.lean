import Spin2.Multiscale.ZBelow
import Spin2.Multiscale.RGInH
import PtCorr2.Zero.ForestNear

/-!
# `TwoPtNear`: the two-point function at short distance (`j_x = 0`), model level

For `|x|_∞ < L/2` (`j_x = 0`), with `β = 1/b`, `h = hPar ≥ 0`:
`b⟨ψ̄_0ψ_x⟩ = P_{β,h}[0 ↔ x, 0 ↮ g]` (`avg0_two_eq_ghost`), and the complement of this event lies in
`{0 ↔ g} ∪ {0 ↮ x}` (full graph on `Λ ∪ {g}`; `H02.reachable_some_iff`). With
`P[0 ↔ g] = 1 - b⟨ψ̄_0ψ_0⟩ = r` and `P[0 ↮ x] ≤ 2|x|_∞/β < L b` (`PtCorr2.qNR_le`: adding the edge
`uv` to a forest with `u ↮ v` is an injection gaining the factor `β`; nearest-neighbour path):

  **`|b⟨ψ̄_0ψ_x⟩ - 1| ≤ L·b + r`**   (`twoPtNear_of`, i.e. `TwoPtNear` with `K_N = L`, `K_{RN} = 1`).

No renormalisation group is used; the constants are uniform in `N`, `m²`, `μ₀`.
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD

variable {L N : ℕ} [NeZero L]

/-- `1 - P[0 ↔ x, 0 ↮ g] ≤ P[0 ↔ g] + P[0 ↮ x]`. -/
theorem one_sub_ghostTwo_le {β h : ℝ} (hβ : 0 < β) (hh : 0 ≤ h) (x : Lam 2 L N) :
    1 - ghostTwo L N β h x ≤ (1 - ghostTwo L N β h 0) + PtCorr2.qNR β h x := by
  have hw := H02.ghostW_symm (Ward.nnW_symm (d := 2) (L := L) (N := N) β) (fun _ => h)
  have hw0 := H02.ghostW_nonneg (Ward.nnW_nonneg (d := 2) (L := L) (N := N) hβ.le)
    (h := fun _ => h) fun _ => hh
  have c1 := PtCorr2.arborealProb_compl hw hw0
    (fun F => (H02.base F).Reachable 0 x ∧ ¬F.Reachable (some (0 : Lam 2 L N)) none)
  have c2 := PtCorr2.arborealProb_compl hw hw0
    (fun F => F.Reachable (some (0 : Lam 2 L N)) none)
  have e0 : ghostTwo L N β h 0 = H02.arborealProb _ hw
      (fun F => ¬F.Reachable (some (0 : Lam 2 L N)) none) := by
    unfold ghostTwo
    congr 1
    funext F
    simp
  have hu := PtCorr2.arborealProb_union_le hw hw0
    (A := fun F => ¬((H02.base F).Reachable 0 x ∧ ¬F.Reachable (some (0 : Lam 2 L N)) none))
    (B := fun F => F.Reachable (some (0 : Lam 2 L N)) none)
    (C := fun F => ¬F.Reachable (some (0 : Lam 2 L N)) (some x)) fun F hF => by
      by_cases hg : F.Reachable (some (0 : Lam 2 L N)) none
      · exact Or.inl hg
      · right
        intro hr
        rcases (H02.reachable_some_iff F 0 x).1 hr with hb | hb
        · exact hF ⟨hb, hg⟩
        · exact hg hb.1
  unfold ghostTwo at *
  unfold PtCorr2.qNR
  rw [e0]
  linarith

/-- **`TwoPtNear` from the model**: `|b⟨ψ̄_0ψ_x⟩ - 1| ≤ L b + |1 - b⟨ψ̄_0ψ_0⟩|` for `j_x = 0`. -/
theorem twoPtNear_of (hL : 2 ≤ L) {m b μ₀ : ℝ} (hb : 0 < b) (hm0 : 0 < m) (hh : b ≤ μ₀ + m) :
    TwoPtNear (L := L) (N := N) m b μ₀ (L : ℝ) 1 := by
  intro x _ h0
  have hs : 2 * supNorm x < L := by
    have := (Nat.log_eq_zero_iff).1 h0
    rw [zero_sub, supNorm_neg] at this
    omega
  have hs' : (2 * supNorm x : ℝ) ≤ L := by exact_mod_cast hs.le
  have hβ : (0 : ℝ) < 1 / b := by positivity
  have hh0 := hPar_nonneg hb hh
  rw [avg0_two_eq_ghost hb hm0 hh x, avg0_two_eq_ghost hb hm0 hh 0]
  have g1 := ghostTwo_mem (L := L) (N := N) hβ.le hh0 x
  have g0 := ghostTwo_mem (L := L) (N := N) hβ.le hh0 0
  have key := one_sub_ghostTwo_le (L := L) (N := N) hβ hh0 x
  have hq := PtCorr2.qNR_le (L := L) (N := N) hβ hh0 x
  rw [one_div_one_div] at hq
  have e1 : ‖((ghostTwo L N (1 / b) (hPar b μ₀ m) x : ℝ) : ℂ) - 1‖ =
      1 - ghostTwo L N (1 / b) (hPar b μ₀ m) x := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith), neg_sub]
  have e2 : ‖(1 : ℂ) - ((ghostTwo L N (1 / b) (hPar b μ₀ m) 0 : ℝ) : ℂ)‖ =
      1 - ghostTwo L N (1 / b) (hPar b μ₀ m) 0 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
  rw [e1, e2, one_mul]
  have : (2 * supNorm x : ℝ) * b ≤ L * b := mul_le_mul_of_nonneg_right hs' hb.le
  linarith

end

end Spin2
