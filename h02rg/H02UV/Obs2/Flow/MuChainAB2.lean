import Obs2.Est.ErrAB
import Obs2.Est.WObsAB

/-!
# The mass of `𝒲'` in the reduced `r` flow is a pure product term

`errAB` (`Obs2/Flow/MuChainAB`) contains `wTadAB_k(W_k, 0) = ∑_Bm₂(𝒲_k(B)_{ab})`, the full `m₂` of
the `ab` part of `𝒲_k`. Its crude size `‖𝒲_k‖ ≲ ǧ_k‖V'_k‖` has an `r'`-proportional part of
relative size `ǧ_k|r'_k/β_k|`, which is not summable. Exactly, however:

* **`wTadAB_zero_succ`**: `wTadAB_{j+1}(𝒲_{j+1}, 0) = farABm_j + wProdAB_j(0)`
  (`wTadAB_step` at `Γ = 0`: the one-loop part `τ^{ab}_j(0)`, the transported part and the
  localisation defect `pdefLS_j(0)` vanish; `S − Loc S` has no `m₂` on the blocks meeting `{a,b}`
  because `loc^{ab}` reproduces `m₂`). So the *linear* part of `𝒲_{j+1}` (the sum of the
  `𝒲'(B) = S(B) − Loc S(B)`) carries no mass at all, and only the product part
  `∏_{B⊆B_+}(1 + 𝒲'(B)) − 1 − ∑_B𝒲'(B)` remains. This is quadratic in `𝒲'`, and on `abSub` it
  is linear in the `ab` sizes times the bulk sizes (`oTo_prod_sub_leAB`): relative size
  `O(ǧ·ǧ²)|r'/β|`, summable. No new drift term is needed (unlike `𝔫^{(2)}`, `tadInc₂`).
* `wMassAB` (`= farABm_{k-1} + wProdAB_{k-1}(0)` for `k > j₀`, `0` at `k = j₀`),
  **`MuChainAB.wTadAB_zero_eq`**, `errAB2` (`errAB` with `wMassAB`), **`MuChainAB.errAB_eq2`**,
  **`MuChainAB.srcAB_eq2`**.
* **`norm_wProdAB0_le`**: on anchored inputs, with `‖𝒲'(B)_∅‖_{T_k(ℓ)} ≤ e`,
  `‖𝒲'(B)_{ab}‖_{T_k(ℓ)} ≤ o`: `|wProdAB_j(0)| ≤ 2L^d o((1+e)^{L^d} − 1)ℓ^{-2}`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD ENNReal

variable {d L N : ℕ} [NeZero L]

section Step

variable (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
  (V W : OFam .two d L N)

theorem tauAB_zero : tauAB j C V 0 = 0 := by
  rw [tauAB, expLC_zero, sub_self]

theorem pdefLS_zero : pdefLS P j C V W 0 = 0 := by
  unfold pdefLS
  exact sum_eq_zero fun b _ => by rw [expLC_zero, sub_self]

/-- **The mass of the new `𝒲` is its product part** (plus the far term). -/
theorem wTadAB_zero_succ :
    wTadAB (j + 1) (Wnext2O P j C V W) 0 = farABm P j C V W + wProdAB P j C V W 0 := by
  rw [wTadAB_step, tauAB_zero, pdefLS_zero, zero_add, zero_add]
  ring

end Step

/-- The mass of `𝒲_k` along a chain from `j₀`: `farABm_{k-1} + wProdAB_{k-1}(0)` (`k > j₀`). -/
def wMassAB (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : ℕ → OFam .two d L N) (j0 k : ℕ) : ℂ :=
  if j0 < k then farABm P (k - 1) (C (k - 1)) (V (k - 1)) (W (k - 1)) +
    wProdAB P (k - 1) (C (k - 1)) (V (k - 1)) (W (k - 1)) 0 else 0

/-- **The error of the reduced `r` flow, with the mass of `𝒲` as a product term.** -/
def errAB2 (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : ℕ → OFam .two d L N) (K : ℕ → OAct .two d L N) (j0 k : ℕ) : ℂ :=
  qAB P k (C k) (K k) + wMassAB P C V W j0 k -
    pdefM2 k (C k) (V k) * (1 - nA2 P k (C k) (V k)) +
    mass2 (FC (C k) (dAB P k (C k) (V k)) (VprLO k (C k) (V k) : SA .two (Lam d L N)).e) -
    farABm P k (C k) (V k) (W k) + ∑ i ∈ Ico j0 k, memAB P C V W i k

namespace MuChainAB

variable {P : ObsPts d L N} {C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ}
  {V W : ℕ → OFam .two d L N} {j0 n : ℕ} (H : MuChainAB P C V W j0 n)
include H

/-- **`wTadAB_k(0) = wMassAB_k`** along the chain (`j₀ ≤ k ≤ n`). -/
theorem wTadAB_zero_eq {k : ℕ} (hk : j0 ≤ k) (hkn : k ≤ n) :
    wTadAB k (W k) 0 = wMassAB P C V W j0 k := by
  unfold wMassAB
  split_ifs with h
  · obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
    rw [show i + 1 - 1 = i by omega, ← wTadAB_zero_succ]
    unfold wTadAB
    exact sum_congr rfl fun c' _ => by rw [H.hW i (by omega) (by omega) c']
  · obtain rfl : k = j0 := by omega
    unfold wTadAB
    exact sum_eq_zero fun b _ => by rw [H.hW0 b, map_zero, mass2_zero]

theorem errAB_eq2 (K : ℕ → OAct .two d L N) {k : ℕ} (hk : j0 ≤ k) (hkn : k ≤ n) :
    errAB P C V W K j0 k = errAB2 P C V W K j0 k := by
  rw [errAB, errAB2, H.wTadAB_zero_eq hk hkn]

end MuChainAB

/-- `‖errAB2_k‖ ≤ |qAB| + |wMassAB| + |𝔡₂||1 − n_a| + |m₂F_C(D, V'_∅)| + ∑|memAB|` when
`farABm_k = 0`. -/
theorem norm_errAB2_le (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : ℕ → OFam .two d L N) (K : ℕ → OAct .two d L N) (j0 k : ℕ)
    (hf : farABm P k (C k) (V k) (W k) = 0) :
    ‖errAB2 P C V W K j0 k‖ ≤ ‖qAB P k (C k) (K k)‖ + ‖wMassAB P C V W j0 k‖ +
      ‖pdefM2 k (C k) (V k)‖ * ‖1 - nA2 P k (C k) (V k)‖ +
      ‖mass2 (FC (C k) (dAB P k (C k) (V k)) (VprLO k (C k) (V k) : SA .two (Lam d L N)).e)‖ +
      ∑ i ∈ Ico j0 k, ‖memAB P C V W i k‖ := by
  unfold errAB2
  rw [hf, sub_zero]
  refine (norm_add_le _ _).trans (add_le_add ?_ (norm_sum_le _ _))
  refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
  refine (norm_sub_le _ _).trans (add_le_add ?_ (norm_mul _ _).le)
  exact norm_add_le _ _

/-! ### The size of the product part -/

/-- The weight `(0, 0, 1)`: on `abSub`, `oTo wAB1 = ‖·_{ab}‖`. -/
def wAB1 : Wt := ⟨0, 0, 1⟩

theorem oTo_wAB1 {c : Obs.Case} (j : ℕ) (ℓ : ℝ) {F : OE c (Lam d L N)}
    (hF : F ∈ (abSub : Subalgebra ℂ (OE c (Lam d L N)))) :
    oTo wAB1 j ℓ F = Tj d (L : ℝ) j ℓ (F : SA c (Lam d L N)).ab := by
  rw [oTo_of_ab _ _ _ hF]
  show (1 : ℝ≥0∞) * _ = _
  rw [one_mul]

/-- **The `m₂` of the product part on anchored inputs.** With `‖𝒲'(B)_∅‖_{T_k(ℓ)} ≤ e` and
`‖𝒲'(B)_{ab}‖_{T_k(ℓ)} ≤ o`: `|wProdAB_j(0)| ≤ 2L^d o((1+e)^{L^d} − 1)ℓ^{-2}`. -/
theorem norm_wProdAB0_le {P : ObsPts d L N} {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℂ}
    {V W : OFam .two d L N} {K : OAct .two d L N} (H : OAnchS P j V W K) (k : ℕ)
    {ℓ e o : ℝ} (hℓ : 0 < ℓ) (he : 0 ≤ e) (ho : 0 ≤ o)
    (hWe : ∀ b, Tj d (L : ℝ) k ℓ (WpO P j C V W b : SA .two (Lam d L N)).e ≤ ENNReal.ofReal e)
    (hWo : ∀ b, Tj d (L : ℝ) k ℓ (WpO P j C V W b : SA .two (Lam d L N)).ab ≤
      ENNReal.ofReal o) :
    ‖wProdAB P j C V W 0‖ ≤
      2 * ((L : ℝ) ^ d * o * ((1 + e) ^ (L ^ d) - 1) * ℓ⁻¹ ^ 2) := by
  have hh : (0 : ℝ) < (L : ℝ) ^ k := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) k
  have hq0 : (0 : ℝ) ≤ (1 + e) ^ (L ^ d) - 1 := by
    have := one_le_pow₀ (n := L ^ d) (show (1 : ℝ) ≤ 1 + e by linarith); linarith
  unfold wProdAB
  simp only [expLC_zero]
  refine norm_sum_two_le _ _ (blk (j + 1) P.a) (blk (j + 1) P.b) (by positivity)
    (fun c' _ h1 h2 => ?_) fun c' _ => ?_
  · have hm : (Wnext2O P j C V W c' - ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
        WpO P j C V W b : OE .two (Lam d L N)) ∈
        (anc P (blockSet (L := L) (N := N) (j + 1) c') : Subalgebra ℂ (OE .two (Lam d L N))) :=
      sub_mem (H.Wnext_anch (C := C) c') (Subalgebra.sum_mem _ fun b hb => anc_mono
        (blockSet_subset (IsPolymer.of_succ (isPolymer_blockSet (j + 1) c')) hb)
        (H.Wp_anch (C := C) b))
    rw [ab_eq_zero_of_anch P hm h1 h2, mass2_zero]
  · set s := blocks j (blockSet (L := L) (N := N) (j + 1) c') with hs
    have hab : ∀ b ∈ s, WpO P j C V W b ∈ (abSub : Subalgebra ℂ (OE .two (Lam d L N))) :=
      fun b _ => anchSub_ab (H.Wp_anch (C := C) b)
    have hP := (oTo_prod_sub_leAB (w := wAB1) hh hℓ s (fun b => WpO P j C V W b) he ho
      (fun b _ => hWe b) (fun b hb => by rw [oTo_wAB1 k ℓ (hab b hb)]; exact hWo b) hab).2
    have hmem : (∏ b ∈ s, (1 + WpO P j C V W b) - 1 - ∑ b ∈ s, WpO P j C V W b :
        OE .two (Lam d L N)) ∈ (abSub : Subalgebra ℂ (OE .two (Lam d L N))) :=
      sub_mem (sub_mem (prod_mem fun b hb => add_mem (one_mem _) (hab b hb)) (one_mem _))
        (Subalgebra.sum_mem _ hab)
    rw [oTo_wAB1 k ℓ hmem] at hP
    have hn : (s.card : ℝ) ≤ (L : ℝ) ^ d := by
      have := nb_blockSet_succ_le (L := L) (N := N) j c'
      unfold nb at this; exact_mod_cast this
    have hn' : s.card ≤ L ^ d := by exact_mod_cast hn
    have hpow : (1 + e) ^ s.card ≤ (1 + e) ^ (L ^ d) :=
      pow_le_pow_right₀ (by linarith) hn'
    have hB : (s.card : ℝ) * o * ((1 + e) ^ s.card - 1) ≤ (L : ℝ) ^ d * o * ((1 + e) ^ (L ^ d) - 1) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hn ho) (by linarith) (by
        have := one_le_pow₀ (n := s.card) (show (1 : ℝ) ≤ 1 + e by linarith); linarith)
        (by positivity)
    refine (norm_mass2_le hℓ k _).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have e1 : ((Wnext2O P j C V W c' - ∑ b ∈ s, WpO P j C V W b : OE .two (Lam d L N)) :
        SA .two (Lam d L N)).ab = ((∏ b ∈ s, (1 + WpO P j C V W b) - 1 -
          ∑ b ∈ s, WpO P j C V W b : OE .two (Lam d L N)) : SA .two (Lam d L N)).ab := by
      rw [Wnext2O]
    rw [e1]
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hP
    rw [ENNReal.toReal_ofReal (by
      have := one_le_pow₀ (n := s.card) (show (1 : ℝ) ≤ 1 + e by linarith); positivity)] at this
    exact this.trans hB

end

end Obs2
