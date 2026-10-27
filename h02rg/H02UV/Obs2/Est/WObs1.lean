import Obs2.Est.LinBoundO
import Obs2.Est.EstBlock
import Step2.Map.WContract

/-!
# The `𝒲^{obs}` contraction, part 1: the pointed `(1 - loc)` after the expectation

In `𝒲_{j+1}(B) = S(B) - Loc_{B_+,B} S(B_+)` the localisation acts **after** the expectation
`𝔼_C θ`. For one block `B` and a component `G` of `𝒲(B)` with `p ∈ B^□` (`p = a` or `b`) we
show (`ecc_odd_contract`, `ecc_even_contract`)

  `‖𝔼θG - loc^p(𝔼θG)‖_{T_{j+1}(ℓ')} ≤ K L^{-1} ‖G‖_{T_j(ℓ)}`,

by the splitting `G = A + P`, `P = loc^p G` (as `Step2.Map.WContract` for the bulk):
* `A = G - loc^p G` gains `L^{-1}` already at scale `j + 1` with field scale `2ℓ`
  (`exists_odd_contract_pt`), and `𝔼θ` maps `T_{j+1}(2ℓ)` to `T_{j+1}(ℓ')`; `loc^p` is bounded at
  scale `j + 1` (`locOdd_pt_bound` on the small set `clo(B^□)`);
* `P` has degree `≤ 2`, so `‖𝔼θP‖_{T_j(ℓ)} ≤ ‖P‖_{T_j(2ℓ)} ≤ 16‖P‖_{T_j(ℓ)}` (`expLC_same_le`,
  `tNorm_two_le_of_deg`), and `𝔼θP` is supported at `p` with the charge of `G`, so
  `exists_odd_contract_pt` applies to it.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD ENNReal

variable {d L N : ℕ} [NeZero L]

theorem hasCharge_ecc_locOdd (C : Matrix (Lam d L N) (Lam d L N) ℂ) (s : ℤˣ) (p : Lam d L N)
    (G : Alg d L N) : HasCharge (-(s : ℤ)) (ECC C (theta (locOdd s {p} {p} {p} G))) := by
  apply hasCharge_of_scal
  rw [ECC_theta, ← expLC_scal C two_ne_zero, scal_locOdd]
  rcases Int.units_eq_one_or s with h | h
  · subst h
    simp only [Units.val_one, neg_neg, zpow_one]
    exact map_smul _ _ _
  · subst h
    simp only [if_neg (show (-1 : ℤˣ) ≠ 1 by decide), Units.val_neg, Units.val_one, neg_neg,
      zpow_neg, zpow_one]
    exact map_smul _ _ _

theorem hasCharge_ecc_locEven (C : Matrix (Lam d L N) (Lam d L N) ℂ) (p : Lam d L N)
    (G : Alg d L N) : HasCharge 0 (ECC C (theta (locEven {p} {p} {p} G))) := by
  rw [hasCharge_zero_iff, isSym_iff_mem_SymS, ECC_theta]
  exact expLC_mem_SymS C (mem_SymS.2 (scal_locEven _ _ _ _))

theorem nbhd_sub_clo_nbhd (j : ℕ) (b : Fin d → ℕ) :
    (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N)) ⊆
      (nbhd (j + 1) (clo j (nbhd j (blockSet (L := L) (N := N) j b))) : Set (Lam d L N)) := by
  intro x hx
  exact_mod_cast subset_nbhd (isPolymer_clo j _) (subset_clo j _ (by exact_mod_cast hx))

/-- **The pointed `(1 - loc)` after the expectation contracts (odd components).** -/
theorem ecc_odd_contract (d : ℕ) (hd : 1 ≤ d) : ∃ K : ℝ, 0 ≤ K ∧ ∃ L₀ : ℕ,
    ∀ (L : ℕ) [NeZero L], 2 ^ (d + 3) + 8 * d < L → L₀ ≤ L → ∀ N j : ℕ, j + 1 < N →
    ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ → ℓC ≤ ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓC C →
    ∀ b ∈ blockIdx (L := L) (N := N) j, ∀ (s : ℤˣ) (p : Lam d L N),
      p ∈ nbhd j (blockSet (L := L) (N := N) j b) →
    ∀ G ∈ NX (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N)),
      HasCharge (-(s : ℤ)) G →
      Tj d (L : ℝ) (j + 1) ℓ' (ECC C (theta G) - locOdd s {p} {p} {p} (ECC C (theta G))) ≤
        ENNReal.ofReal (K / L) * Tj d (L : ℝ) j ℓ G := by
  obtain ⟨Cc, hCc, L₀, hcon⟩ := exists_odd_contract_pt d hd
  obtain ⟨Cb, hCb, hlb⟩ := locOdd_pt_bound d
  refine ⟨Cc * (1 + Cb) + 16 * Cc * Cb, by positivity, L₀, ?_⟩
  intro L _ hL hL₀ N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum hCℓ C hC b hb s p hp G hG hGc
  have hj : j < N := by omega
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hh : (0 : ℝ) < (L : ℝ) ^ j := by positivity
  have hL2 : 2 ^ (d + 2) ≤ L := by
    have : 2 ^ (d + 2) ≤ 2 ^ (d + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hX : IsSmall j (blockSet (L := L) (N := N) j b) := isSmall_blockSet_of_mem hb
  set B := nbhd j (blockSet (L := L) (N := N) j b) with hBdef
  set P := locOdd s {p} {p} {p} G with hPdef
  set A := G - P with hAdef
  have hPmem : P ∈ NX (B : Set (Lam d L N)) :=
    NX_mono (single_inter_sub_nbhd hp) (locOdd_mem s {p} {p} {p} G)
  have hAmem : A ∈ NX (B : Set (Lam d L N)) := sub_mem hG hPmem
  -- the splitting
  have hsplit : ECC C (theta G) - locOdd s {p} {p} {p} (ECC C (theta G)) =
      (ECC C (theta A) - locOdd s {p} {p} {p} (ECC C (theta A))) +
        (ECC C (theta P) - locOdd s {p} {p} {p} (ECC C (theta P))) := by
    have e : G = A + P := by rw [hAdef, sub_add_cancel]
    conv_lhs => rw [e]
    rw [map_add, map_add, locOdd_add]; abel
  rw [hsplit]
  refine (tNorm_add_le _ _).trans ?_
  -- the `A` part
  have hA1 : Tj d (L : ℝ) (j + 1) (2 * ℓ) A ≤ ENNReal.ofReal (Cc / L) * Tj d (L : ℝ) j ℓ G :=
    hcon L hL hL₀ N j hj ℓ (2 * ℓ) hℓ (by positivity) le_rfl _ hX s p hp G hG hGc
  have hEA : ECC C (theta A) ∈ NX (B : Set (Lam d L N)) := by
    rw [ECC_theta]; exact expLC_mem_NX C hAmem
  have hX' := isSmall_clo_nbhd hd hL2 (by omega) b hb
  have hEA' : ECC C (theta A) ∈ NX (nbhd (j + 1) (clo j B) : Set (Lam d L N)) :=
    NX_mono (nbhd_sub_clo_nbhd j b) hEA
  have hA2 : Tj d (L : ℝ) (j + 1) ℓ' (ECC C (theta A) - locOdd s {p} {p} {p} (ECC C (theta A))) ≤
      ENNReal.ofReal (1 + Cb) * Tj d (L : ℝ) (j + 1) ℓ' (ECC C (theta A)) := by
    refine (tNorm_sub_le _ _).trans ?_
    have := hlb L hL N (j + 1) hjN _ hX' _ hEA' s {p} {p} {p} subset_rfl ℓ' hℓ'
    rw [ENNReal.ofReal_add zero_le_one hCb, ENNReal.ofReal_one, add_mul, one_mul]
    exact add_le_add le_rfl this
  have hA3 := EthE_succ_le2' hℓ' hℓC hsum hC A
  -- the `P` part
  have hEP : ECC C (theta P) ∈ NX (B : Set (Lam d L N)) := by
    rw [ECC_theta]; exact expLC_mem_NX C hPmem
  have hP1 := hcon L hL hL₀ N j hj ℓ ℓ' hℓ hℓ' (by linarith) _ hX s p hp _ hEP
    (hasCharge_ecc_locOdd C s p G)
  have hP2 : Tj d (L : ℝ) j ℓ (ECC C (theta P)) ≤ Tj d (L : ℝ) j (2 * ℓ) P := by
    rw [ECC_theta]; exact expLC_same_le hℓ (hC.mono hCℓ) P
  have hP3 : Tj d (L : ℝ) j (2 * ℓ) P ≤ 16 * Tj d (L : ℝ) j ℓ P :=
    tNorm_two_le_of_deg (pPhi d) hh.le hℓ fun n z hn =>
      coeff_locOdd_of_ne s _ _ _ G z (by omega)
  have hP4 := hlb L hL N j hj _ hX G hG s {p} {p} {p} subset_rfl ℓ hℓ
  -- assembly
  calc Tj d (L : ℝ) (j + 1) ℓ' (ECC C (theta A) - locOdd s {p} {p} {p} (ECC C (theta A))) +
        Tj d (L : ℝ) (j + 1) ℓ' (ECC C (theta P) - locOdd s {p} {p} {p} (ECC C (theta P)))
      ≤ ENNReal.ofReal (1 + Cb) * (ENNReal.ofReal (Cc / L) * Tj d (L : ℝ) j ℓ G) +
        ENNReal.ofReal (Cc / L) * (16 * (ENNReal.ofReal Cb * Tj d (L : ℝ) j ℓ G)) := by
        gcongr
        · exact hA2.trans (mul_le_mul_right (hA3.trans hA1) _)
        · exact hP1.trans (mul_le_mul_right (hP2.trans (hP3.trans (mul_le_mul_right hP4 _))) _)
    _ = ENNReal.ofReal ((Cc * (1 + Cb) + 16 * Cc * Cb) / L) * Tj d (L : ℝ) j ℓ G := by
        have h16 : (16 : ℝ≥0∞) = ENNReal.ofReal 16 := by simp
        rw [h16, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 2
        ring

/-- **The pointed `(1 - loc)` after the expectation contracts (even components).** -/
theorem ecc_even_contract (d : ℕ) (hd : 1 ≤ d) : ∃ K : ℝ, 0 ≤ K ∧ ∃ L₀ : ℕ,
    ∀ (L : ℕ) [NeZero L], 2 ^ (d + 3) + 8 * d < L → L₀ ≤ L → ∀ N j : ℕ, j + 1 < N →
    ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ → ℓC ≤ ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓC C →
    ∀ b ∈ blockIdx (L := L) (N := N) j, ∀ p : Lam d L N,
      p ∈ nbhd j (blockSet (L := L) (N := N) j b) →
    ∀ G ∈ NX (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N)), HasCharge 0 G →
      Tj d (L : ℝ) (j + 1) ℓ' (ECC C (theta G) - locEven {p} {p} {p} (ECC C (theta G))) ≤
        ENNReal.ofReal (K / L) * Tj d (L : ℝ) j ℓ G := by
  obtain ⟨Cc, hCc, L₀, hcon⟩ := exists_even_contract_pt d hd
  obtain ⟨Cb, hCb, hlb⟩ := locEven_pt_bound d
  refine ⟨Cc * (1 + Cb) + 16 * Cc * Cb, by positivity, L₀, ?_⟩
  intro L _ hL hL₀ N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum hCℓ C hC b hb p hp G hG hGc
  have hj : j < N := by omega
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hh : (0 : ℝ) < (L : ℝ) ^ j := by positivity
  have hL2 : 2 ^ (d + 2) ≤ L := by
    have : 2 ^ (d + 2) ≤ 2 ^ (d + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hX : IsSmall j (blockSet (L := L) (N := N) j b) := isSmall_blockSet_of_mem hb
  set B := nbhd j (blockSet (L := L) (N := N) j b) with hBdef
  set P := locEven {p} {p} {p} G with hPdef
  set A := G - P with hAdef
  have hPmem : P ∈ NX (B : Set (Lam d L N)) :=
    NX_mono (single_inter_sub_nbhd hp) (locEven_mem {p} {p} {p} G)
  have hAmem : A ∈ NX (B : Set (Lam d L N)) := sub_mem hG hPmem
  have hsplit : ECC C (theta G) - locEven {p} {p} {p} (ECC C (theta G)) =
      (ECC C (theta A) - locEven {p} {p} {p} (ECC C (theta A))) +
        (ECC C (theta P) - locEven {p} {p} {p} (ECC C (theta P))) := by
    have e : G = A + P := by rw [hAdef, sub_add_cancel]
    conv_lhs => rw [e]
    rw [map_add, map_add, locEven_add]; abel
  rw [hsplit]
  refine (tNorm_add_le _ _).trans ?_
  have hA1 : Tj d (L : ℝ) (j + 1) (2 * ℓ) A ≤ ENNReal.ofReal (Cc / L) * Tj d (L : ℝ) j ℓ G :=
    hcon L hL hL₀ N j hj ℓ (2 * ℓ) hℓ (by positivity) le_rfl _ hX p hp G hG hGc
  have hEA : ECC C (theta A) ∈ NX (B : Set (Lam d L N)) := by
    rw [ECC_theta]; exact expLC_mem_NX C hAmem
  have hX' := isSmall_clo_nbhd hd hL2 (by omega) b hb
  have hEA' : ECC C (theta A) ∈ NX (nbhd (j + 1) (clo j B) : Set (Lam d L N)) :=
    NX_mono (nbhd_sub_clo_nbhd j b) hEA
  have hA2 : Tj d (L : ℝ) (j + 1) ℓ' (ECC C (theta A) - locEven {p} {p} {p} (ECC C (theta A))) ≤
      ENNReal.ofReal (1 + Cb) * Tj d (L : ℝ) (j + 1) ℓ' (ECC C (theta A)) := by
    refine (tNorm_sub_le _ _).trans ?_
    have := hlb L hL N (j + 1) hjN _ hX' _ hEA' {p} {p} {p} subset_rfl ℓ' hℓ'
    rw [ENNReal.ofReal_add zero_le_one hCb, ENNReal.ofReal_one, add_mul, one_mul]
    exact add_le_add le_rfl this
  have hA3 := EthE_succ_le2' hℓ' hℓC hsum hC A
  have hEP : ECC C (theta P) ∈ NX (B : Set (Lam d L N)) := by
    rw [ECC_theta]; exact expLC_mem_NX C hPmem
  have hP1 := hcon L hL hL₀ N j hj ℓ ℓ' hℓ hℓ' (by linarith) _ hX p hp _ hEP
    (hasCharge_ecc_locEven C p G)
  have hP2 : Tj d (L : ℝ) j ℓ (ECC C (theta P)) ≤ Tj d (L : ℝ) j (2 * ℓ) P := by
    rw [ECC_theta]; exact expLC_same_le hℓ (hC.mono hCℓ) P
  have hP3 : Tj d (L : ℝ) j (2 * ℓ) P ≤ 16 * Tj d (L : ℝ) j ℓ P :=
    tNorm_two_le_of_deg (pPhi d) hh.le hℓ fun n z hn => by
      rcases Nat.eq_zero_or_pos n with h0 | _
      · omega
      · exact coeff_locEven_of_ne _ _ _ G z (by omega) (by omega)
  have hP4 := hlb L hL N j hj _ hX G hG {p} {p} {p} subset_rfl ℓ hℓ
  calc Tj d (L : ℝ) (j + 1) ℓ' (ECC C (theta A) - locEven {p} {p} {p} (ECC C (theta A))) +
        Tj d (L : ℝ) (j + 1) ℓ' (ECC C (theta P) - locEven {p} {p} {p} (ECC C (theta P)))
      ≤ ENNReal.ofReal (1 + Cb) * (ENNReal.ofReal (Cc / L) * Tj d (L : ℝ) j ℓ G) +
        ENNReal.ofReal (Cc / L) * (16 * (ENNReal.ofReal Cb * Tj d (L : ℝ) j ℓ G)) := by
        gcongr
        · exact hA2.trans (mul_le_mul_right (hA3.trans hA1) _)
        · exact hP1.trans (mul_le_mul_right (hP2.trans (hP3.trans (mul_le_mul_right hP4 _))) _)
    _ = ENNReal.ofReal ((Cc * (1 + Cb) + 16 * Cc * Cb) / L) * Tj d (L : ℝ) j ℓ G := by
        have h16 : (16 : ℝ≥0∞) = ENNReal.ofReal 16 := by simp
        rw [h16, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 2
        ring

end

end Obs2
