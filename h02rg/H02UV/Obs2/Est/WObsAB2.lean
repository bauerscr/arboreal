import Obs2.Loc.LocABRepro

/-!
# Proof of `EthSubLocAB` (the `(1 - loc^{ab}_{X,X})𝔼θ` contraction on the `ab` sector)

For `G ∈ 𝒩(B^□)` `U(1)`-invariant, `B ∩ {a,b} ≠ ∅`, `a, b ∈ B^□`, `X ⊇ B` small at scale `j + 1`:
split `G = A + Q`, `Q = loc^{ab}_{B,B} G`, `A = G - Q`.

* `Q ∈ 𝒩({a,b})` is `U(1)`-invariant, hence so is `𝔼θQ`, and `loc^{ab}_{X,X}` reproduces it
  **exactly** (`locABtX_repro`: the range of the barycentric `loc^{ab}` is the full charge-`0` part of
  `𝒩({a,b})`, independent of the base set). So `(1 - loc^{ab}_{X,X})𝔼θQ = 0`.
* `A` gains `L^{-1}` at scale `j + 1` with field scale `2ℓ` (`exists_locABt_contract` on `B`),
  `𝔼θ` maps `T_{j+1}(2ℓ)` to `T_{j+1}(ℓ')` (`EthE_succ_le2'`), and `loc^{ab}_X` is bounded at scale
  `j + 1` (`exists_locABt_bound` on `X`; `𝔼θA ∈ 𝒩(B^□) ⊆ 𝒩(X^□_{j+1})`).

Hence **`ethSubLocAB`**: `EthSubLocAB d` for every `d ≥ 1`, with `K = C_c (1 + C_b)`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD ENNReal

variable {d L N : ℕ} [NeZero L]

theorem pts_mem_or {P : ObsPts d L N} {X : Finset (Lam d L N)} (h : (X ∩ P.pts).Nonempty) :
    P.a ∈ X ∨ P.b ∈ X := by
  by_cases ha : P.a ∈ X
  · exact Or.inl ha
  · exact Or.inr (mem_b_of_inter h ha)

/-- **`EthSubLocAB d` holds** (`d ≥ 1`). -/
theorem ethSubLocAB (d : ℕ) (hd : 1 ≤ d) : EthSubLocAB d := by
  obtain ⟨Cc, hCc, L₀, hcon⟩ := exists_locABt_contract d hd
  obtain ⟨Cb, hCb, hlb⟩ := exists_locABt_bound d hd
  refine ⟨Cc * (1 + Cb), by positivity, L₀, ?_⟩
  intro L _ hL hL₀ N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum _ C hC P b hb X hX hBX hne ha hb' G hG hGs
  have hj : j < N := by omega
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hBs : IsSmall j (blockSet (L := L) (N := N) j b) := isSmall_blockSet_of_mem hb
  have hXne : (X ∩ P.pts).Nonempty := hne.mono (inter_subset_inter_right hBX)
  set B := blockSet (L := L) (N := N) j b with hBdef
  set Q := locABtXY P B B G with hQdef
  set A := G - Q with hAdef
  have hQab : Q ∈ NX ({P.a, P.b} : Set (Lam d L N)) := locABtXY_mem P B B G
  have hpair : ({P.a, P.b} : Set (Lam d L N)) ⊆ (nbhd j B : Set (Lam d L N)) := by
    intro x hx
    rcases hx with rfl | hx
    · exact ha
    · rw [Set.mem_singleton_iff] at hx; subst hx; exact hb'
  have hAB : A ∈ NX (nbhd j B : Set (Lam d L N)) := sub_mem hG (NX_mono hpair hQab)
  have hBX' : (nbhd j B : Set (Lam d L N)) ⊆ (nbhd (j + 1) X : Set (Lam d L N)) := by
    intro x hx
    exact_mod_cast nbhd_subset_nbhd_succ X (nbhd_mono hBX (by exact_mod_cast hx))
  -- the reproduced part vanishes
  have hEQ : ECC C (theta Q) - locABtXY P X X (ECC C (theta Q)) = 0 := by
    rw [locABtXY_self P X hXne, sub_eq_zero, ECC_theta]
    refine (locABtX_repro (pts_mem_or hXne) (expLC_mem_NX C hQab) ?_).symm
    rw [isSym_iff_mem_SymS]
    exact expLC_mem_SymS C (mem_SymS.2 (locABtXY_scal P B B G))
  have hsplit : ECC C (theta G) - locABtXY P X X (ECC C (theta G)) =
      (ECC C (theta A) - locABtXY P X X (ECC C (theta A))) +
        (ECC C (theta Q) - locABtXY P X X (ECC C (theta Q))) := by
    have e : G = A + Q := by rw [hAdef, sub_add_cancel]
    conv_lhs => rw [e]
    rw [map_add, map_add, locABtXY_add]; abel
  rw [hsplit, hEQ, add_zero]
  -- the `A` part
  have hA1 : Tj d (L : ℝ) (j + 1) (2 * ℓ) A ≤ ENNReal.ofReal (Cc / L) * Tj d (L : ℝ) j ℓ G := by
    rw [hAdef, hQdef, locABtXY_self P B hne, locABtX]
    split_ifs with hpa
    · exact hcon L hL hL₀ N j hj ℓ (2 * ℓ) hℓ (by positivity) le_rfl B hBs P.a P.b hpa G hG hGs
    · exact hcon L hL hL₀ N j hj ℓ (2 * ℓ) hℓ (by positivity) le_rfl B hBs P.b P.a
        (mem_b_of_inter hne hpa) G hG hGs
  have hEA : ECC C (theta A) ∈ NX (nbhd (j + 1) X : Set (Lam d L N)) := by
    rw [ECC_theta]; exact NX_mono hBX' (expLC_mem_NX C hAB)
  have hA2 : Tj d (L : ℝ) (j + 1) ℓ' (ECC C (theta A) - locABtXY P X X (ECC C (theta A))) ≤
      ENNReal.ofReal (1 + Cb) * Tj d (L : ℝ) (j + 1) ℓ' (ECC C (theta A)) := by
    refine (tNorm_sub_le _ _).trans ?_
    have hb2 : Tj d (L : ℝ) (j + 1) ℓ' (locABtXY P X X (ECC C (theta A))) ≤
        ENNReal.ofReal Cb * Tj d (L : ℝ) (j + 1) ℓ' (ECC C (theta A)) := by
      rw [locABtXY_self P X hXne, locABtX]
      split_ifs with hpa
      · exact hlb L hL N (j + 1) hjN ℓ' hℓ' X hX P.a P.b hpa _ hEA
      · exact hlb L hL N (j + 1) hjN ℓ' hℓ' X hX P.b P.a (mem_b_of_inter hXne hpa) _ hEA
    rw [ENNReal.ofReal_add zero_le_one hCb, ENNReal.ofReal_one, add_mul, one_mul]
    exact add_le_add le_rfl hb2
  have hA3 := EthE_succ_le2' hℓ' hℓC hsum hC A
  calc Tj d (L : ℝ) (j + 1) ℓ' (ECC C (theta A) - locABtXY P X X (ECC C (theta A)))
      ≤ ENNReal.ofReal (1 + Cb) * (ENNReal.ofReal (Cc / L) * Tj d (L : ℝ) j ℓ G) :=
        hA2.trans (mul_le_mul_right (hA3.trans hA1) _)
    _ = ENNReal.ofReal (Cc * (1 + Cb) / L) * Tj d (L : ℝ) j ℓ G := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2; ring

/-- `EthSubLocAB 2`. -/
theorem ethSubLocAB_two : EthSubLocAB 2 := ethSubLocAB 2 (by norm_num)

end

end Obs2
