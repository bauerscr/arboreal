import DressedFRD.Main
import DressedFRD.StdLocBound

/-!
# `thm:main` under (S1)–(S5)

`thm_main_full`: the conclusions of `thm_main` with `StdLoc` discharged by `lem:std`(e),
i.e. with `c₂ = c2val d L q M c_S`.
-/

namespace DressedFRD

noncomputable section

open Finset FRD Data Grassmann

variable {d n : ℕ} [NeZero n]

theorem c2val_nonneg {L q M : ℕ} {cS : ℝ} (hL : 2 ≤ L) (hM : q + d + 1 ≤ M) (hM3 : 3 ≤ M) (hcS : 0 ≤ cS) :
    0 ≤ c2val d L q M cS := by
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  have hP : 0 < 1 - (L : ℝ) ^ (2 - (M : ℝ)) := by
    have := Real.rpow_lt_one_of_one_lt_of_neg hL1 (by
      have : (3 : ℝ) ≤ M := by exact_mod_cast hM3
      linarith :
        2 - (M : ℝ) < 0)
    linarith
  have hQ : 0 < 1 - (2 : ℝ) ^ ((d : ℝ) - ((M : ℝ) - q)) := by
    have := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2) (by
      have : ((q + d + 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast hM
      push_cast at this; linarith : (d : ℝ) - ((M : ℝ) - q) < 0)
    linarith
  unfold c2val
  have := inv_pos.2 hP
  have := inv_pos.2 hQ
  have : (0 : ℝ) < Real.pi / 2 := by positivity
  positivity

/-- `thm:main`(i),(iii),(iv),(v) under (S1)–(S5). -/
theorem thm_main_full {q L M : ℕ} {cS : ℝ} (hd : 2 ≤ d) (hq : 2 ≤ q) (hL : 7 ≤ L)
    (hM : q + d + 1 ≤ M) (hcS : 0 ≤ cS) :
    ∃ ζbar : ℝ, 0 < ζbar ∧ ζbar ≤ 1 / 8 ∧ ∃ K : ℝ, ∀ (n : ℕ) [NeZero n] (D : Data d n), D.L = L →
      n = L ^ D.N → StdFull L D.N q M D.msq cS D.C →
      D.msq ≤ (L : ℝ) ^ (-(2 * ((D.N : ℝ) - 1))) → (∀ i, ‖D.ζ i‖ ≤ ζbar) →
      ∀ j, j < D.N → D.Concl q ζbar K j := by
  obtain ⟨ζbar, hζ, hζ8, K, hK⟩ := thm_main (c₂ := c2val d L q M cS) hd hq hL
    (c2val_nonneg (by omega) hM (by omega) hcS)
  exact ⟨ζbar, hζ, hζ8, K, fun n _ D hDL hn hS hmsq hζi j hj =>
    hK n D hDL hn hS.base (std_e hS (by omega) hq hL hn) hmsq hζi j hj⟩

theorem lam_zero' : lam (0 : Torus d n) = 0 := by
  have : ∀ i, (co (0 : Torus d n) i).val = 0 := fun i => by
    show ((0 : Fin d → ZMod n) i).val = 0; simp
  simp [lam, cosk, this]

theorem pnorm_zero' : pnorm (0 : Torus d n) = 0 := by
  unfold pnorm; simp [char_zero_left]

/-- The zero mode is controlled by the `α = 0` part of the norm. -/
theorem norm_apply_zero_le {L : ℝ} (hL : 0 < L) (q s : ℕ) (w : Sym d n) :
    ‖w 0‖ ≤ (n : ℝ) ^ d * L ^ (-((s : ℝ) * ((d : ℝ) - 2))) * snorm L q s w := by
  have h := le_snorm (L := L) (q := q) (s := s) (α := 0) (by simp [Grassmann.mabs]) w
  have hn : (0 : ℝ) < (n : ℝ) ^ d := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)) d
  have hmom : ((n : ℝ) ^ d)⁻¹ * ‖w 0‖ ≤ mom 0 w := by
    unfold mom avg
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hn.le)
    simpa [sigma_zero] using single_le_sum (f := fun m => ‖sigma (0 : Dir d → ℕ) m‖ * ‖w m‖)
      (fun m _ => by positivity) (mem_univ (0 : Torus d n))
  have hw : wgt d L s 0 = L ^ ((s : ℝ) * ((d : ℝ) - 2)) := by simp [wgt, Grassmann.mabs]
  rw [hw] at h
  have hp : 0 < L ^ ((s : ℝ) * ((d : ℝ) - 2)) := Real.rpow_pos_of_pos hL _
  rw [Real.rpow_neg hL.le]
  have h2 : ‖w 0‖ ≤ (n : ℝ) ^ d * mom 0 w := by
    rw [inv_mul_le_iff₀ hn] at hmom; exact hmom
  calc ‖w 0‖ ≤ (n : ℝ) ^ d * mom 0 w := h2
    _ ≤ (n : ℝ) ^ d * ((L ^ ((s : ℝ) * ((d : ℝ) - 2)))⁻¹ * snorm L q s w) := by
        refine mul_le_mul_of_nonneg_left ?_ hn.le
        rw [le_inv_mul_iff₀ hp]; exact h
    _ = _ := by ring

/-- `thm:main`(vi) at the zero mode: `Z_N Γ^int_N(0) = m^{-2} + O(L^{2N})`, i.e.
`Γ^int_N(0) = (Z_N m²)^{-1} (1 + O(m² L^{2N}))`. -/
theorem zero_mode_le {L N q M : ℕ} {msq cS B : ℝ} {C : ℕ → Torus d n → ℝ}
    (h : StdFull L N q M msq cS C) (hd : 1 ≤ d) (hL : 7 ≤ L) (hN : 1 ≤ N) (hn : n = L ^ N)
    (w : Sym d n) (hw : snorm L q (N - 1) (w - ofR (C N)) ≤ B) :
    ‖w 0 - ((msq⁻¹ : ℝ) : ℂ)‖ ≤
      (2 ^ M * (1 + 2 * M : ℝ) ^ d * cS + B) * (L : ℝ) ^ d * (L : ℝ) ^ (2 * (N - 1)) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  set cd := 2 ^ M * (1 + 2 * M : ℝ) ^ d * cS
  -- the zero mode of `w - C_N`
  have h1 := norm_apply_zero_le hL0 q (N - 1) (w - ofR (C N))
  have hpow : (n : ℝ) ^ d * (L : ℝ) ^ (-(((N - 1 : ℕ) : ℝ) * ((d : ℝ) - 2))) =
      (L : ℝ) ^ d * (L : ℝ) ^ (2 * (N - 1)) := by
    rw [hn]; push_cast
    rw [← pow_mul, ← Real.rpow_natCast (L : ℝ) (N * d), ← Real.rpow_natCast (L : ℝ) d,
      ← Real.rpow_natCast (L : ℝ) (2 * (N - 1)), ← Real.rpow_add hL0, ← Real.rpow_add hL0]
    congr 1; push_cast [Nat.cast_sub hN]; ring
  rw [hpow] at h1
  -- `C_N(0) = m^{-2} - ∑_{k<N} C_k(0)`
  have hs := h.base.sum_eq 0
  rw [lam_zero', zero_add] at hs
  have hsplit : ∑ k ∈ Icc 1 N, C k 0 = ∑ k ∈ Icc 1 (N - 1), C k 0 + C N 0 := by
    have : Icc 1 N = insert N (Icc 1 (N - 1)) := by
      ext k; simp only [mem_Icc, mem_insert]; omega
    rw [this, sum_insert (by simp only [mem_Icc]; omega), add_comm]
  have hC0 : ∀ k, 0 ≤ C k 0 := fun k => h.base.nonneg k 0
  have hlow : ∑ k ∈ Icc 1 (N - 1), C k 0 ≤ cd * (L : ℝ) ^ d * (L : ℝ) ^ (2 * (N - 1)) := by
    calc ∑ k ∈ Icc 1 (N - 1), C k 0 ≤ ∑ k ∈ Icc 1 (N - 1), cd * (L : ℝ) ^ d * (L : ℝ) ^ (2 * (k - 1)) := by
          refine sum_le_sum fun k hk => ?_
          rw [mem_Icc] at hk
          have := std_d h hd (by omega) hk.1 (by omega) 0
          rw [pnorm_zero', mul_zero, add_zero, one_pow, mul_one] at this
          exact this
      _ = cd * (L : ℝ) ^ d * ∑ k ∈ range (N - 1), ((L : ℝ) ^ 2) ^ k := by
          rw [mul_sum]
          refine sum_nbij' (fun k => k - 1) (fun i => i + 1) ?_ ?_ ?_ ?_ ?_
          · intro k hk; simp only [mem_Icc, mem_range] at hk ⊢; omega
          · intro i hi; simp only [mem_Icc, mem_range] at hi ⊢; omega
          · intro k hk; simp only [mem_Icc] at hk; omega
          · intro i _; omega
          · intro k _; rw [← pow_mul]
      _ ≤ cd * (L : ℝ) ^ d * ((L : ℝ) ^ 2) ^ (N - 1) := by
          have hcd : 0 ≤ cd := by have := h.hcS; positivity
          refine mul_le_mul_of_nonneg_left (sum_range_pow_le ?_ _) (by positivity)
          have : (7 : ℝ) ≤ L := by exact_mod_cast hL
          nlinarith
      _ = _ := by rw [← pow_mul]
  have hid : w 0 - ((msq⁻¹ : ℝ) : ℂ) = (w - ofR (C N)) 0 - ((∑ k ∈ Icc 1 (N - 1), C k 0 : ℝ) : ℂ) := by
    rw [← hs, hsplit]; simp only [Pi.sub_apply, ofR]; push_cast; ring
  rw [hid]
  refine (norm_sub_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_of_nonneg (sum_nonneg fun k _ => hC0 k)]
  have hP : 0 ≤ (L : ℝ) ^ d * (L : ℝ) ^ (2 * (N - 1)) := by positivity
  nlinarith

end

end DressedFRD
