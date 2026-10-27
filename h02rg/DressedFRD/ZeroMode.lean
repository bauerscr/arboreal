import DressedFRD

/-!
# The zero mode of the dressed covariance at the last scale

On the torus `Λ = (ℤ/n)^d` a symbol `w` splits into its zero mode and the rest:
`w = nzP w + zmP w`, with `zmP w = w(0) δ_{p,0}`. The kernel of `zmP w` is the constant
`w(0)/|Λ|` (`kern_zmP`), i.e. `w(0) Q` with `Q = |Λ|^{-1} 𝟙𝟙ᵀ`.

At the last step `j + 1 = N`, `Γ^int_N = Γ_{N-1}(1 + z_{N-1} A Γ_{N-1})^{-1}` contains the
zero mode of `C_N`, of size `≈ 1/(Z_N m²)`. This file shows:

* `nzP`, `zmP`, `nzP_add_zmP`, `kern_zmP`, `kmat_zmP`: the splitting;
* `snorm_nzP_le`: removing the zero mode does not increase `‖·‖_{(s)}`;
* `norm_zero_le_snorm`: `|w(0)| ≤ |Λ| L^{-s(d-2)} ‖w‖_{(s)}`;
* `absorbed_closed`: `Z_{j+1} A Γ_j(1 + z_j A Γ_j)^{-1} = (1 - ε_j)/(1 - ζ'_j ε_j)`
  (exact, every `j ≤ N`); at `p = 0`, `A = m²`, so
  `m² Z_N Γ^int_N(0) = (1 - ε_{N-1}(0))/(1 - ζ'_{N-1} ε_{N-1}(0))` (`last_zero_formula`);
* `snorm_nzP_CN_le`: `‖C_N 1_{p≠0}‖_{(N-1)} ≤ c_S L^d (1 + 2·5^d (π/2)^M)`, from (S5);
* `Concl.last_nz`, `Concl.last_zero`: the closeness `thm:main`(vi) at the last scale, split into
  the nonzero modes (`‖·‖_{(N-1)} ≤ 2 K |ζ|`) and the zero mode
  (`|Z_N Γ^int_N(0) - Ĉ_N(0)| ≤ |Λ| L^{-(N-1)(d-2)} 2 K |ζ|`);
* `Concl.last_gram`: `|Z_N| ‖nzP Γ^int_N‖_{(N-1)} ≤ c_S' + 2 K |ζ|`, the Gram admissibility of
  the nonzero modes at the last scale, uniformly in `m²`.
-/

namespace DressedFRD

noncomputable section

open Finset Complex FRD Grassmann

variable {d n : ℕ} [NeZero n]

/-! ### Splitting off the zero mode -/

/-- The symbol without its zero mode. -/
def nzP (w : Sym d n) : Sym d n := fun m => if m = 0 then 0 else w m

/-- The zero mode `w(0) δ_{p,0}` of a symbol. -/
def zmP (w : Sym d n) : Sym d n := fun m => if m = 0 then w 0 else 0

theorem nzP_add_zmP (w : Sym d n) : nzP w + zmP w = w := by
  funext m; by_cases h : m = 0 <;> simp [nzP, zmP, h]

theorem nzP_sub (w v : Sym d n) : nzP (w - v) = nzP w - nzP v := by
  funext m; by_cases h : m = 0 <;> simp [nzP, h]

theorem nzP_smul (c : ℂ) (w : Sym d n) : nzP (c • w) = c • nzP w := by
  funext m; by_cases h : m = 0 <;> simp [nzP, h]

theorem norm_nzP_le (w : Sym d n) (m : Torus d n) : ‖nzP w m‖ ≤ ‖w m‖ := by
  by_cases h : m = 0 <;> simp [nzP, h]

/-- The kernel of the zero mode is the constant `w(0)/|Λ|`. -/
theorem kern_zmP (w : Sym d n) (x : Torus d n) : kern (zmP w) x = w 0 / (n : ℂ) ^ d := by
  unfold kern zmP
  rw [Finset.sum_eq_single (0 : Torus d n)]
  · simp [char_zero_left, div_eq_inv_mul]
  · intro m _ hm; simp [hm]
  · simp

theorem kmat_zmP (w : Sym d n) (x y : Torus d n) : kmat (zmP w) x y = w 0 / (n : ℂ) ^ d :=
  kern_zmP w _

/-- **The splitting of the matrix**: `kmat w = kmat (nzP w) + w(0) Q`, `Q_{xy} = |Λ|^{-1}`. -/
theorem kmat_split (w : Sym d n) (x y : Torus d n) :
    kmat w x y = kmat (nzP w) x y + w 0 / (n : ℂ) ^ d := by
  conv_lhs => rw [← nzP_add_zmP w]
  simp only [kmat, kern_add, kern_zmP]

/-! ### Norms -/

variable {L : ℝ} {q s : ℕ}

theorem mom_nzP_le (α : Dir d → ℕ) (w : Sym d n) : mom α (nzP w) ≤ mom α w :=
  avg_mono fun m => mul_le_mul_of_nonneg_left (norm_nzP_le w m) (norm_nonneg _)

theorem snorm_nzP_le (hL : 0 < L) (w : Sym d n) : snorm L q s (nzP w) ≤ snorm L q s w :=
  snorm_le_iff.2 fun α hα => (mul_le_mul_of_nonneg_left (mom_nzP_le α w)
    (wgt_pos hL s α).le).trans (le_snorm hα w)

/-- `|w(0)| ≤ |Λ| L^{-s(d-2)} ‖w‖_{(s)}`. -/
theorem norm_zero_le_snorm (hL : 0 < L) (w : Sym d n) :
    ‖w 0‖ ≤ (n : ℝ) ^ d * L ^ (-((s : ℝ) * ((d : ℝ) - 2))) * snorm L q s w := by
  have hn : (0 : ℝ) < (n : ℝ) ^ d := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)) d
  have h1 := le_snorm (L := L) (s := s) (q := q) (α := 0) (by simp [Grassmann.mabs]) w
  rw [wgt_zero, mom_zero] at h1
  have h2 : ((n : ℝ) ^ d)⁻¹ * ‖w 0‖ ≤ avg fun m => ‖w m‖ := by
    unfold avg
    exact mul_le_mul_of_nonneg_left
      (single_le_sum (f := fun m => ‖w m‖) (fun m _ => norm_nonneg _) (mem_univ 0))
      (inv_nonneg.2 hn.le)
  have hw : 0 < L ^ ((s : ℝ) * ((d : ℝ) - 2)) := Real.rpow_pos_of_pos hL _
  have e : L ^ (-((s : ℝ) * ((d : ℝ) - 2))) = (L ^ ((s : ℝ) * ((d : ℝ) - 2)))⁻¹ :=
    Real.rpow_neg hL.le _
  rw [e]
  have h3 : ‖w 0‖ ≤ (n : ℝ) ^ d * (avg fun m => ‖w m‖) := by
    rw [← inv_mul_le_iff₀ hn]; exact h2
  calc ‖w 0‖ ≤ (n : ℝ) ^ d * (avg fun m => ‖w m‖) := h3
    _ = (n : ℝ) ^ d * (L ^ ((s : ℝ) * ((d : ℝ) - 2)))⁻¹ *
          (L ^ ((s : ℝ) * ((d : ℝ) - 2)) * avg fun m => ‖w m‖) := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)

/-! ### The last piece `C_N` without its zero mode -/

section CN

variable {L N q M : ℕ} {msq cS : ℝ} {C : ℕ → Torus d n → ℝ}

/-- **`‖C_N 1_{p ≠ 0}‖_{(N-1)} ≤ c_S L^d (1 + 2·5^d (π/2)^M)`**, from (S5), for `q + d + 2 ≤ M`. -/
theorem snorm_nzP_CN_le (h : StdFull L N q M msq cS C) (hd : 1 ≤ d) (hL : 7 ≤ L) (hN : 1 ≤ N)
    (hn : n = L ^ N) (hM : q + d + 2 ≤ M) :
    snorm L q (N - 1) (nzP (ofR (C N))) ≤
      cS * (L : ℝ) ^ d * (1 + 2 * 5 ^ d * (Real.pi / 2) ^ (M : ℝ)) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  set R : ℝ := (L : ℝ) ^ (N - 1)
  have hR : 0 < R := by positivity
  have hnR : 7 * R ≤ n := by
    rw [hn]; push_cast
    have : (L : ℝ) ^ N = L * R := by
      simp only [R]; rw [← pow_succ']; congr 1; omega
    rw [this]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hL) hR.le
  set r : ℕ := (q + d + 2) / 2
  have hr1 : q + d + 1 ≤ 2 * r := by omega
  have hr2 : 2 * r ≤ M := by omega
  set w : Torus d n → ℝ := fun m => if m = 0 then 0 else C N m
  set B : ℝ := cS * (L : ℝ) ^ d * (L : ℝ) ^ (2 * (N - 1))
  have hw0 : ∀ m, 0 ≤ w m := fun m => by
    simp only [w]; split_ifs
    · exact le_rfl
    · exact h.base.nonneg N m
  have hB0 : 0 ≤ B := by have := h.hcS; positivity
  have hS5 : ∀ m, m ≠ 0 → C N m * (1 + R * pnorm m) ^ M ≤ B := fun m hm => h.S5 m hm
  have hwB : ∀ m, w m ≤ B := fun m => by
    simp only [w]; split_ifs with hm
    · exact hB0
    · have h1 : 1 ≤ (1 + R * pnorm m) ^ M :=
        one_le_pow₀ (by have := pnorm_nonneg m; have : 0 ≤ R * pnorm m := by positivity
                        linarith)
      have := hS5 m hm
      have hC := h.base.nonneg N m
      nlinarith
  have hwB' : ∀ m, R⁻¹ < pnorm m → w m * (R * pnorm m) ^ (2 * r) ≤ B := fun m _ => by
    simp only [w]; split_ifs with hm
    · simp [hB0]
    · have hy : 0 ≤ R * pnorm m := mul_nonneg hR.le (pnorm_nonneg m)
      have h1 : (R * pnorm m) ^ (2 * r) ≤ (1 + R * pnorm m) ^ M :=
        (pow_le_pow_left₀ hy (by linarith) _).trans
          (pow_le_pow_right₀ (by linarith) hr2)
      exact (mul_le_mul_of_nonneg_left h1 (h.base.nonneg N m)).trans (hS5 m hm)
  refine snorm_le_iff.2 fun α hα => ?_
  set a := Grassmann.mabs α
  have hb : (d : ℝ) + a < 2 * r := by
    have : d + a < 2 * r := by omega
    exact_mod_cast this
  have hav := avg_pnorm_pow_le (n := n) hd (w := w) (B := B) (B' := B) a r hR hnR hb hw0 hwB
    hB0 hwB'
  -- the moment
  have hmom : mom α (nzP (ofR (C N))) ≤ avg fun m => pnorm m ^ a * w m := by
    refine avg_mono fun m => ?_
    have e : ‖nzP (ofR (C N)) m‖ = w m := by
      simp only [nzP, w, ofR]; split_ifs
      · simp
      · rw [Complex.norm_real, Real.norm_of_nonneg (h.base.nonneg N m)]
    rw [e]
    exact mul_le_mul_of_nonneg_right (norm_sigma_le_pnorm α m) (hw0 m)
  -- the tail constant
  have htail : tailC d (2 * r - a) ≤ 2 * 5 ^ d * (Real.pi / 2) ^ (M : ℝ) := by
    have hb1 : (d : ℝ) + 1 ≤ 2 * r - a := by
      have : d + a + 1 ≤ 2 * r := by omega
      have : ((d + a + 1 : ℕ) : ℝ) ≤ ((2 * r : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at this; linarith
    refine (tailC_le hb1).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    refine Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) ?_
    have : ((2 * r : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast hr2
    push_cast at this
    have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    linarith
  -- the weights
  have hwgt : wgt d (L : ℝ) (N - 1) α * (L : ℝ) ^ (2 * (N - 1)) * R ^ (-((a : ℝ) + d)) = 1 := by
    unfold wgt
    simp only [R]
    rw [← Real.rpow_natCast (L : ℝ) (2 * (N - 1)), ← Real.rpow_natCast (L : ℝ) (N - 1),
      ← Real.rpow_mul hL0.le, ← Real.rpow_add hL0, ← Real.rpow_add hL0]
    rw [show ((N - 1 : ℕ) : ℝ) * ((d : ℝ) - 2 + a) + ((2 * (N - 1) : ℕ) : ℝ) +
        ((N - 1 : ℕ) : ℝ) * -((a : ℝ) + d) = 0 by push_cast; ring, Real.rpow_zero]
  have hwp := wgt_pos hL0 (N - 1) α
  have htc0 : 0 ≤ tailC d (2 * r - a) := tailC_nonneg (by linarith)
  calc wgt d (L : ℝ) (N - 1) α * mom α (nzP (ofR (C N)))
      ≤ wgt d (L : ℝ) (N - 1) α * ((B + B * tailC d (2 * r - a)) * R ^ (-((a : ℝ) + d))) :=
        mul_le_mul_of_nonneg_left (hmom.trans (by exact_mod_cast hav)) hwp.le
    _ = cS * (L : ℝ) ^ d * (1 + tailC d (2 * r - a)) *
          (wgt d (L : ℝ) (N - 1) α * (L : ℝ) ^ (2 * (N - 1)) * R ^ (-((a : ℝ) + d))) := by
        simp only [B]; ring
    _ = cS * (L : ℝ) ^ d * (1 + tailC d (2 * r - a)) := by rw [hwgt, mul_one]
    _ ≤ _ := by
        have := h.hcS
        gcongr

end CN

/-! ### The zero mode at the last step -/

namespace Data

variable {D : Data d n}

/-- **The closed form of the absorbed covariance**:
`Z_{j+1} A Γ_j(1 + z_j A Γ_j)^{-1} = (1 - ε_j)/(1 - ζ'_j ε_j)`. -/
theorem absorbed_closed (h : StdHyp D.L D.N D.msq D.C) {j : ℕ} (hj : j ≤ D.N)
    (hZ : D.Z j ≠ 0) (hζ : 1 + D.ζ j ≠ 0) (m : Torus d n)
    (hden : 1 - D.zp j * D.eps j (D.tails j) m ≠ 0) :
    D.Z (j + 1) * Asym D.msq m * D.absorbed j m =
      (1 - D.eps j (D.tails j) m) / (1 - D.zp j * D.eps j (D.tails j) m) := by
  have hG := Z_A_Gam h hj hZ m
  have hA := Asym_ne_zero h m
  set ε := D.eps j (D.tails j) m
  set G := D.Gam j m
  set A := Asym D.msq m
  have hden' : 1 + D.ζ j * D.Z j * A * G ≠ 0 := by
    have e : 1 + D.ζ j * D.Z j * A * G = (1 + D.ζ j) * (1 - D.zp j * ε) := by
      have : D.ζ j * D.Z j * A * G = D.ζ j * (1 - ε) := by rw [← hG]; ring
      rw [this]; unfold zp; field_simp; ring
    rw [e]; exact mul_ne_zero hζ hden
  unfold absorbed
  rw [Z_succ]
  change D.Z j * (1 + D.ζ j) * A * (G / (1 + D.ζ j * D.Z j * A * G)) = (1 - ε) / (1 - D.zp j * ε)
  rw [eq_div_iff hden]
  have e2 : D.ζ j * D.Z j * A * G = D.ζ j * (1 - ε) := by rw [← hG]; ring
  rw [e2] at hden' ⊢
  have e3 : D.Z j * (1 + D.ζ j) * A * (G / (1 + D.ζ j * (1 - ε))) =
      (1 + D.ζ j) * (D.Z j * A * G) / (1 + D.ζ j * (1 - ε)) := by ring
  rw [e3, hG]
  unfold zp
  field_simp
  ring

theorem Asym_zero (msq : ℝ) : Asym (d := d) (n := n) msq 0 = (msq : ℂ) := by
  simp [Asym, lam_zero']

/-- **The zero-mode coefficient at the last step**:
`m² Z_N Γ^int_N(0) = (1 - ε_{N-1}(0))/(1 - ζ'_{N-1} ε_{N-1}(0))`. -/
theorem last_zero_formula (h : StdHyp D.L D.N D.msq D.C) {j : ℕ} (hj : j + 1 = D.N)
    (hZ : D.Z j ≠ 0) (hζ : 1 + D.ζ j ≠ 0)
    (hden : 1 - D.zp j * D.eps j (D.tails j) 0 ≠ 0) :
    (D.msq : ℂ) * (D.Z (j + 1) * D.Gint j 0) =
      (1 - D.eps j (D.tails j) 0) / (1 - D.zp j * D.eps j (D.tails j) 0) := by
  have hG : D.Gint j = D.absorbed j := by simp [Gint, hj]
  rw [hG, ← absorbed_closed h (by omega) hZ hζ 0 hden, Asym_zero]
  ring

variable {q M : ℕ} {cS ζbar K : ℝ}

/-- `thm:main`(vi) on the nonzero modes: `‖nzP (Z_N Γ^int_N - C_N)‖_{(N-1)} ≤ 2 K |ζ|`. -/
theorem Concl.last_nz {j : ℕ} (hc : D.Concl q ζbar K j) (hj : j + 1 = D.N) (hL : 0 < (D.L : ℝ)) :
    snorm D.L q j (nzP (D.Z (j + 1) • D.Gint j) - nzP (ofR (D.C (j + 1)))) ≤
      2 * K * D.Mz (j + 1) := by
  rw [← nzP_sub]; exact (snorm_nzP_le hL _).trans (hc.last hj)

/-- `thm:main`(vi) at the zero mode:
`|Z_N Γ^int_N(0) - Ĉ_N(0)| ≤ |Λ| L^{-(N-1)(d-2)} 2 K |ζ|`. -/
theorem Concl.last_zero {j : ℕ} (hc : D.Concl q ζbar K j) (hj : j + 1 = D.N)
    (hL : 0 < (D.L : ℝ)) :
    ‖D.Z (j + 1) * D.Gint j 0 - (D.C (j + 1) 0 : ℂ)‖ ≤
      (n : ℝ) ^ d * (D.L : ℝ) ^ (-((j : ℝ) * ((d : ℝ) - 2))) * (2 * K * D.Mz (j + 1)) := by
  have h := norm_zero_le_snorm (q := q) (s := j) hL (D.Z (j + 1) • D.Gint j - ofR (D.C (j + 1)))
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ofR] at h
  exact h.trans (mul_le_mul_of_nonneg_left (hc.last hj) (by positivity))

/-- **Gram admissibility of the nonzero modes at the last scale**:
`|Z_N| ‖nzP Γ^int_N‖_{(N-1)} ≤ c_S' + 2 K |ζ|`, where `c_S' ≥ ‖nzP C_N‖_{(N-1)}`. -/
theorem Concl.last_gram {j : ℕ} (hc : D.Concl q ζbar K j) (hj : j + 1 = D.N)
    (hL : 0 < (D.L : ℝ)) {cS' : ℝ} (hCN : snorm D.L q j (nzP (ofR (D.C (j + 1)))) ≤ cS') :
    ‖D.Z (j + 1)‖ * snorm D.L q j (nzP (D.Gint j)) ≤ cS' + 2 * K * D.Mz (j + 1) := by
  rw [← snorm_smul hL, ← nzP_smul]
  calc snorm D.L q j (nzP (D.Z (j + 1) • D.Gint j))
      = snorm D.L q j (nzP (ofR (D.C (j + 1))) +
          (nzP (D.Z (j + 1) • D.Gint j) - nzP (ofR (D.C (j + 1))))) := by congr 1; abel
    _ ≤ snorm D.L q j (nzP (ofR (D.C (j + 1)))) +
          snorm D.L q j (nzP (D.Z (j + 1) • D.Gint j) - nzP (ofR (D.C (j + 1)))) :=
        snorm_add_le hL _ _
    _ ≤ _ := add_le_add hCN (hc.last_nz hj hL)

end Data

end

end DressedFRD
