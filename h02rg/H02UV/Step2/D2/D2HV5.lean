import Step2.D2.D2HV4
import Step2.D2.D2Bv9
import Step2.D2.D2Prop

-- Merged from `Step2/D2Line3.lean` (phase 3).
section

/-!
# `prop:d2`, line 3 at `ζ = 0` (fallback form)

With `w_j = ∑_{k=1}^j C_k = C_{(0, L^j/2]}` (`sum_Cj_eq_cov`):

  `‖𝔅(w_{j+1}) - 𝔅(w_j) - log L/(2π)‖ ≤ 2 CB0`

for `L ≥ 7`, `1 ≤ j`, `j + 1 < N`, `0 < m² ≤ L^{-2(N-1)}`; `CB0` is absolute.
-/

namespace Step2.D2

noncomputable section

open MeasureTheory Set Real

theorem msq_mul_sq_le {L N j : ℕ} (hL : 1 ≤ L) (hjN : j + 1 < N) {msq : ℝ} (hm : 0 ≤ msq)
    (h : msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) : msq * ((L : ℝ) ^ (j + 1) / 2) ^ 2 ≤ 1 := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have e : (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) = (((L : ℝ) ^ (N - 1)) ^ 2)⁻¹ := by
    rw [Real.rpow_neg hL0.le, ← pow_mul, ← Real.rpow_natCast]
    congr 2
    push_cast [Nat.cast_sub (by omega : 1 ≤ N)]; ring
  rw [e] at h
  have hp : (L : ℝ) ^ (j + 1) ≤ (L : ℝ) ^ (N - 1) := pow_le_pow_right₀ hL1 (by omega)
  have hp0 : 0 < (L : ℝ) ^ (j + 1) := by positivity
  have h2 : ((L : ℝ) ^ (j + 1)) ^ 2 ≤ ((L : ℝ) ^ (N - 1)) ^ 2 := pow_le_pow_left₀ hp0.le hp 2
  calc msq * ((L : ℝ) ^ (j + 1) / 2) ^ 2 ≤ (((L : ℝ) ^ (N - 1)) ^ 2)⁻¹ *
        ((L : ℝ) ^ (j + 1) / 2) ^ 2 := by gcongr
    _ ≤ (((L : ℝ) ^ (N - 1)) ^ 2)⁻¹ * (((L : ℝ) ^ (N - 1)) ^ 2 / 4) := by
        gcongr; rw [div_pow]; linarith
    _ ≤ 1 := by
        rw [mul_div_assoc', inv_mul_cancel₀ (by positivity)]; norm_num

/-- **`prop:d2`, line 3, `ζ = 0` (fallback form).** With `w_j = C_{(0, L^j/2]}`:
`‖𝔅(w_{j+1}) - 𝔅(w_j) - log L/(2π)‖ ≤ 2 CB0`, `CB0` absolute. -/
theorem bub_line3 {L N j : ℕ} [NeZero L] (hL : 7 ≤ L) (hj : 1 ≤ j) (hjN : j + 1 < N) {msq : ℝ}
    (hm : 0 < msq) (hmN : msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) :
    ‖frakBT L N msq ((L : ℝ) ^ (j + 1) / 2) - frakBT L N msq ((L : ℝ) ^ j / 2) -
      ((Real.log L / (2 * π) : ℝ) : ℂ)‖ ≤ 2 * CB0 := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hL7 : (7 : ℝ) ≤ L := by exact_mod_cast hL
  have e : (L : ℝ) ^ (j + 1) / 2 = (L : ℝ) * ((L : ℝ) ^ j / 2) := by ring
  rw [e]
  have hLj : (L : ℝ) ≤ (L : ℝ) ^ j := by
    calc (L : ℝ) = (L : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hL1 hj
  refine frakBT_diff_bound (by omega) hm (by linarith) ?_ ?_
  · rw [← e]; exact msq_mul_sq_le (by omega) hjN hm.le hmN
  · -- `2(⌊L^{j+1}/2⌋ + 4) < L^N`
    rw [← e]
    have h1 : (⌊(L : ℝ) ^ (j + 1) / 2⌋₊ : ℝ) ≤ (L : ℝ) ^ (j + 1) / 2 :=
      Nat.floor_le (by positivity)
    have h2 : (L : ℝ) ^ (j + 1) * L ≤ (L : ℝ) ^ N := by
      rw [← pow_succ]; exact pow_le_pow_right₀ hL1 (by omega)
    have h3 : (1 : ℝ) ≤ (L : ℝ) ^ (j + 1) := one_le_pow₀ hL1
    have h4 : ((2 * (⌊(L : ℝ) ^ (j + 1) / 2⌋₊ + 4) : ℕ) : ℝ) < ((L ^ N : ℕ) : ℝ) := by
      push_cast; nlinarith
    exact_mod_cast h4

end

end Step2.D2

end

/-!
# The undressed bubbles as `frakBT`

For the concrete decomposition `C = frdC Pc msq L N`:

* `kmat_Cle_eq_cov`: `kmat C_{≤k} = C_{(0, L^k/2]}` (`1 ≤ k < N`);
* `frakBT_eq_bubX`: `𝔅(w_k) = frakBT(L^k/2) = -𝔅x(C_{≤k}, C_{≤k})`;
* `undressed_bubble`: `2 𝔅x(C_{≤j}, C_{j+1}) + 𝔅x(C_{j+1}, C_{j+1})
  = -(frakBT(L^{j+1}/2) - [j ≥ 1] frakBT(L^j/2))`.
-/

namespace Step2

open Step

noncomputable section

open Finset MeasureTheory Step2.D2 Loc FRD Grassmann DressedFRD

variable {L N : ℕ} [NeZero L]

local notation "Λ2" => Lam 2 L N

theorem fmat_sum {ι : Type*} (s : Finset ι) (w : ι → Grassmann.Torus 2 (L ^ N) → ℝ) :
    ∑ i ∈ s, FRD.fmat (w i) = FRD.fmat (fun m => ∑ i ∈ s, w i m) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext x y; simp [FRD.fmat]
  | insert a s ha ih =>
    rw [sum_insert ha, ih, FRD.fmat_add]
    congr 1; funext m; rw [sum_insert ha]

/-- **`kmat C_{≤k}` is the covariance of the scales `(0, L^k/2]`.** -/
theorem kmat_Cle_eq_cov {msq : ℝ} (hm : 0 ≤ msq) (hL : 1 ≤ L) {k : ℕ} (hk : 1 ≤ k) (hkN : k < N) (a b : Λ2) :
    DressedFRD.kmat (Cle (frdC Pc msq L N) k) a b =
      ((FRD.cov Pc msq (Set.Ioc 0 ((L : ℝ) ^ k / 2)) a b : ℝ) : ℂ) := by
  rw [DressedFRD.kmat, Cle_eq_ofR, kern_ofR_eq_fmat (fun m => by
    simp only [frdC_even Pc _ m])]
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hsum := sum_Cj_eq_cov (n := L ^ N) Pc (msq := msq) hm hL' k hk
  congr 1
  have e : FRD.fmat (fun m => ∑ k' ∈ Icc 1 k, frdC Pc msq L N k' m) =
      ∑ k' ∈ Icc 1 k, (FRD.Cj Pc msq (L : ℝ) k' : Matrix (Grassmann.Torus 2 (L ^ N))
        (Grassmann.Torus 2 (L ^ N)) ℝ) := by
    rw [← fmat_sum]
    refine sum_congr rfl fun k' hk' => ?_
    rw [frdC_of_lt Pc (by have := (mem_Icc.1 hk').2; omega)]
    rfl
  rw [e, hsum]
  simp only [FRD.cov, FRD.fmat, sub_zero]

theorem rng_Cle_le {msq : ℝ} (hm : 0 < msq) (hL : 1 ≤ L) {k : ℕ} (hkN : k < N) :
    rng (Cle (frdC Pc (d := 2) (n := L ^ N) msq L N) k) ≤ L ^ k := by
  unfold Cle
  refine rng_sum_le _ _ fun k' hk' => ?_
  have h := frdC_range Pc (d := 2) (n := L ^ N) (N := N) hm hL (k := k')
    (by have := (mem_Icc.1 hk').2; omega)
  have : L ^ k' ≤ L ^ k := Nat.pow_le_pow_right (by omega) (mem_Icc.1 hk').2
  omega

theorem Cle_symMem' {msq : ℝ} (k : ℕ) : Cle (frdC Pc (d := 2) (n := L ^ N) msq L N) k ∈ symSub :=
  Cle_symMem (d := 2) (n := L ^ N) (C := frdC Pc msq L N)
    (fun k π s m => frdC_symm Pc msq L N k π s m) k

/-- **`𝔅(w_k) = -𝔅x(C_{≤k}, C_{≤k})`.** -/
theorem frakBT_eq_bubX {msq : ℝ} (hm : 0 < msq) (hL : 1 ≤ L) {k : ℕ} (hk : 1 ≤ k) (hkN : k < N)
    {R : ℕ} (hR : rng (Cle (frdC Pc (d := 2) (n := L ^ N) msq L N) k) ≤ R)
    (hn : 2 * (R + 4) < L ^ N) :
    frakBT L N msq ((L : ℝ) ^ k / 2) =
      -bubX (cKer R (Cle (frdC Pc (d := 2) (n := L ^ N) msq L N) k))
        (cKer R (Cle (frdC Pc (d := 2) (n := L ^ N) msq L N) k)) := by
  unfold frakBT
  have e : (fun a b : Λ2 => ((FRD.cov Pc msq (Set.Ioc 0 ((L : ℝ) ^ k / 2)) a b : ℝ) : ℂ)) =
      DressedFRD.kmat (Cle (frdC Pc (d := 2) (n := L ^ N) msq L N) k) := by
    funext a b; rw [kmat_Cle_eq_cov hm.le hL hk hkN]
  rw [e, negBub_kmat (Cle_symMem' k) hR hn (Finset.singleton_nonempty 0) (fun x hx => by
    rw [Finset.mem_singleton] at hx
    rw [hx, base_singleton_zero, sub_zero]
    rw [Grassmann.supNorm_zero]; omega)]

theorem bubX_zero_left (c : ℤ × ℤ → ℂ) : bubX 0 c = 0 := by
  have := bubX_smul_left 0 (0 : ℤ × ℤ → ℂ) c
  simpa using this

/-- **The undressed bubble difference.** -/
theorem undressed_bubble {msq : ℝ} (hm : 0 < msq) (hL : 1 ≤ L) {j : ℕ} (hjN : j + 1 < N)
    (hn : 2 * (L ^ (j + 1) + 4) < L ^ N) :
    2 * bubX (cKer (L ^ (j + 1)) (Cle (frdC Pc (d := 2) (n := L ^ N) msq L N) j))
        (cKer (L ^ (j + 1)) (ofR (frdC Pc (d := 2) (n := L ^ N) msq L N (j + 1)))) +
      bubX (cKer (L ^ (j + 1)) (ofR (frdC Pc (d := 2) (n := L ^ N) msq L N (j + 1))))
        (cKer (L ^ (j + 1)) (ofR (frdC Pc (d := 2) (n := L ^ N) msq L N (j + 1)))) =
      -frakBT L N msq ((L : ℝ) ^ (j + 1) / 2) +
        (if 1 ≤ j then frakBT L N msq ((L : ℝ) ^ j / 2) else 0) := by
  set C := frdC Pc (d := 2) (n := L ^ N) msq L N
  set R := L ^ (j + 1)
  have hs : Cle C (j + 1) = Cle C j + ofR (C (j + 1)) := (Cle_add_ofR C j).symm
  have h1 := frakBT_eq_bubX (L := L) (N := N) hm hL (k := j + 1) (by omega) hjN
    (rng_Cle_le hm hL hjN) hn
  rw [hs, cKer_add, bubX_add_add (cKer_hfs _ _) (cKer_hfs _ _)] at h1
  split_ifs with hj
  · have hjR : rng (Cle C j) ≤ R := (rng_Cle_le hm hL (by omega)).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
    have h0 := frakBT_eq_bubX (L := L) (N := N) hm hL (k := j) hj (by omega) hjR hn
    rw [h1, h0]; ring
  · have hj0 : j = 0 := by omega
    subst hj0
    have hc : Cle C 0 = 0 := by simp [Cle]
    rw [hc] at h1 ⊢
    have hz : ∀ R' : ℕ, cKer R' (0 : DressedFRD.Sym 2 (L ^ N)) = 0 := by
      intro R'; funext u; simp [cKer, DressedFRD.kern]
    simp only [hz, bubX_zero_left, zero_add, mul_zero] at h1 ⊢
    rw [h1]; ring

end

end Step2