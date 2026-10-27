import Step2.D2.D2LDress

/-!
# `prop:d2`: the assembled first two lines (dressed)

* `lc_ofR`: `𝔩` of a real even symbol is the torus sum `n^{-2} ∑ λ w²`;
* `lc_Cle_eq_lfun`: `𝔩(C_{≤j}) = lfun (∑_{k ≤ j} C_k)` for the concrete decomposition;
* `prop_d2_lines12`: **for the concrete decomposition, `d = 2`, `L ≥ 7`, there are `ζ̄ > 0`,
  `K`, `c_S` such that, uniformly in `N`, `0 < m² ≤ L^{-2(N-1)}`, `|ζ_i| ≤ ζ̄`, `1 ≤ j`,
  `j + 1 < N`:**
  - `|C'_{j+1}(0,0) - (1/2π) log L|`, `|C'_{j+1}(e₁,0) - (1/2π) log L|`
    `≤ (2π)^{-2}(C L^{-2j} + B m²(L^{2j} + L^{2(j+1)})) + K |ζ|_{≤j}`;
  - `|𝔩(w'_j + C'_{j+1}) - 𝔩(w'_j) - (1/2π) log L|`
    `≤ (2π)^{-2}(A L^{-2j} + B' m²(L^{2j} + L^{2(j+1)})) + |ζ|_{≤j}(4K + 2L²K²|ζ|_{≤j} + 12(K + c_S)(K|ζ|_{≤j} + c_S))`.
-/

namespace Step2.D2

noncomputable section

open Finset FRD DressedFRD DressedFRD.Data

variable {n : ℕ} [NeZero n]

theorem lc_ofR (w : Grassmann.Torus 2 n → ℝ) :
    lc (ofR w) = ((((n : ℝ) ^ 2)⁻¹ * ∑ m, lam m * w m ^ 2 : ℝ) : ℂ) := by
  simp only [lc, bl, ofR]
  push_cast
  congr 1
  exact sum_congr rfl fun m _ => by ring

theorem Cle_eq_ofR (C : ℕ → Grassmann.Torus 2 n → ℝ) (j : ℕ) :
    Cle C j = ofR (fun m => ∑ k ∈ Icc 1 j, C k m) := by
  funext m; rw [Cle_apply]; rfl

theorem lc_Cle_eq_lfun {msq : ℝ} {L N : ℕ} {j : ℕ} (hj : j < N) :
    lc (Cle (frdC Pc (d := 2) (n := n) msq L N) j) =
      ((lfun (∑ k ∈ Icc 1 j, (FRD.Cj Pc msq (L : ℝ) k :
        Matrix (Grassmann.Torus 2 n) (Grassmann.Torus 2 n) ℝ)) : ℝ) : ℂ) := by
  have e : ∑ k ∈ Icc 1 j, (FRD.Cj Pc msq (L : ℝ) k :
      Matrix (Grassmann.Torus 2 n) (Grassmann.Torus 2 n) ℝ) =
      fmat fun m => ∑ k ∈ Icc 1 j, frdC Pc msq L N k m := by
    rw [← fmat_sum]
    refine sum_congr rfl fun k hk => ?_
    rw [frdC_of_lt Pc (by have := (mem_Icc.1 hk).2; omega)]
    rfl
  rw [e, lfun_fmat (fun m => by simp only [frdC_even]), Cle_eq_ofR, lc_ofR]

omit [NeZero n] in
theorem Cle_add_ofR (C : ℕ → Grassmann.Torus 2 n → ℝ) (j : ℕ) :
    Cle C j + ofR (C (j + 1)) = Cle C (j + 1) := by
  rw [Cle, Cle, sum_Icc_succ_top (by omega)]

/-- **`prop:d2`, lines 1 and 2, dressed**, for the concrete decomposition in `d = 2`. -/
theorem prop_d2_lines12 {q L : ℕ} (hq : 2 ≤ q) (hL : 7 ≤ L) :
    ∃ ζbar : ℝ, 0 < ζbar ∧ ∃ K cS : ℝ, 0 ≤ K ∧ 0 ≤ cS ∧ ∀ (n : ℕ) [NeZero n] (N : ℕ) (msq : ℝ)
      (ζ : ℕ → ℂ), 1 ≤ N → n = L ^ N → 0 < msq → msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) →
      (∀ i, ‖ζ i‖ ≤ ζbar) → ∀ j, 1 ≤ j → j + 1 < N →
      let D : Data 2 n := ⟨L, N, msq, frdC Pc msq L N, ζ⟩
      ‖kern (Cp D (j + 1)) 0 - (Real.log L / (2 * Real.pi) : ℝ)‖ ≤
          (2 * Real.pi)⁻¹ ^ 2 * (ErrC / ((L : ℝ) ^ j) ^ 2 +
            ErrB * msq * (((L : ℝ) ^ j) ^ 2 + ((L : ℝ) ^ (j + 1)) ^ 2)) + K * D.Mz (j + 1) ∧
      ‖kern (Cp D (j + 1)) (unitT 0) - (Real.log L / (2 * Real.pi) : ℝ)‖ ≤
          (2 * Real.pi)⁻¹ ^ 2 * (ErrC1 / ((L : ℝ) ^ j) ^ 2 +
            ErrB * msq * (((L : ℝ) ^ j) ^ 2 + ((L : ℝ) ^ (j + 1)) ^ 2)) + K * D.Mz (j + 1) ∧
      ‖(lc (wp D j + Cp D (j + 1)) - lc (wp D j)) - (Real.log L / (2 * Real.pi) : ℝ)‖ ≤
          (2 * Real.pi)⁻¹ ^ 2 * (ErrL / ((L : ℝ) ^ j) ^ 2 +
            LB * msq * (((L : ℝ) ^ j) ^ 2 + ((L : ℝ) ^ (j + 1)) ^ 2)) +
          D.Mz (j + 1) * (4 * K + 2 * (L : ℝ) ^ 2 * K ^ 2 * D.Mz (j + 1) +
            12 * (K + cS) * (K * D.Mz (j + 1) + cS)) := by
  obtain ⟨ζ1, hζ1, K1, hK1⟩ := Cprime_values (L := L) hq hL
  obtain ⟨ζ2, hζ2, hζ28, K2, hK2⟩ := thm_main_frd Pc (d := 2) le_rfl hq hL
  obtain ⟨cS, hcS, hS⟩ := frd_stdFull Pc (d := 2) le_rfl hL (q := q) (M := q + 2 + 1) le_rfl
  refine ⟨min ζ1 ζ2, lt_min hζ1 hζ2, max (max K1 K2) 0, cS, le_max_right _ _, hcS,
    fun n _ N msq ζ hN hn hmsq hmsq' hζb j hj hjN => ?_⟩
  intro D
  have hb1 : ∀ i, ‖ζ i‖ ≤ ζ1 := fun i => (hζb i).trans (min_le_left _ _)
  have hb2 : ∀ i, ‖ζ i‖ ≤ ζ2 := fun i => (hζb i).trans (min_le_right _ _)
  have hKm : K1 ≤ max (max K1 K2) 0 := (le_max_left _ _).trans (le_max_left _ _)
  have hKm2 : K2 ≤ max (max K1 K2) 0 := (le_max_right _ _).trans (le_max_left _ _)
  set K := max (max K1 K2) 0
  have hMz0 : 0 ≤ D.Mz (j + 1) := Mz_nonneg _
  obtain ⟨c1, c2⟩ := hK1 n N msq ζ hN hn hmsq hmsq' hb1 j hj hjN
  have hCp : Cp D (j + 1) = D.Z (j + 1) • D.Gint j := by simp [Cp]
  refine ⟨?_, ?_, ?_⟩
  · rw [hCp]; refine c1.trans ?_
    gcongr
  · rw [hCp]; refine c2.trans ?_
    gcongr
  · have hc : ∀ i, i < N → D.Concl q ζ2 K2 i := fun i hi =>
      (hK2 n N msq ζ hN hn hmsq hmsq').1 hb2 i hi
    have hL2 : 2 ≤ D.L := by show 2 ≤ L; omega
    have hdress := lc_dress D (M := q + 2 + 1) (K := K) hq hL2 (hS n N msq hN hn hmsq)
      (fun i => (hb2 i).trans hζ28) (le_max_right _ _)
      (fun i hi => (hc i (by have : D.N = N := rfl; omega)).close hi |>.trans (by gcongr; exact Mz_nonneg _))
      (fun i hi => (hc i (by have : D.N = N := rfl; omega)).range hi) hj hjN
    -- the undressed value
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
    have hm1 := msq_le_one (by omega) hN hmsq'
    have hn' : (L : ℝ) ^ (j + 1) + 1 < (n : ℝ) := by
      rw [hn]
      have h1 : L ^ (j + 1) * L ≤ L ^ N := by
        rw [← pow_succ]; exact Nat.pow_le_pow_right (by omega) hjN
      have h2 : ((L ^ (j + 1) * L : ℕ) : ℝ) ≤ ((L ^ N : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at h2 ⊢
      have hL7 : (7 : ℝ) ≤ L := by exact_mod_cast hL
      have hp : (1 : ℝ) ≤ (L : ℝ) ^ (j + 1) := one_le_pow₀ hL1
      nlinarith
    have hval := lfun_value_sum (n := n) hmsq.le hm1 hL1 hj hn'
    have e1 : lc (Cle D.C j + ofR (D.C (j + 1))) - lc (Cle D.C j) =
        (((lfun (∑ k ∈ Icc 1 (j + 1), (FRD.Cj Pc msq (L : ℝ) k :
          Matrix (Grassmann.Torus 2 n) (Grassmann.Torus 2 n) ℝ)) -
          lfun (∑ k ∈ Icc 1 j, (FRD.Cj Pc msq (L : ℝ) k :
          Matrix (Grassmann.Torus 2 n) (Grassmann.Torus 2 n) ℝ))) : ℝ) : ℂ) := by
      rw [Cle_add_ofR]
      show lc (Cle (frdC Pc msq L N) (j + 1)) - lc (Cle (frdC Pc msq L N) j) = _
      rw [lc_Cle_eq_lfun hjN, lc_Cle_eq_lfun (by omega)]
      push_cast; ring
    have key : (lc (wp D j + Cp D (j + 1)) - lc (wp D j)) - ((Real.log L / (2 * Real.pi) : ℝ) : ℂ) =
        ((lc (wp D j + Cp D (j + 1)) - lc (wp D j)) -
          (lc (Cle D.C j + ofR (D.C (j + 1))) - lc (Cle D.C j))) +
        (((lfun (∑ k ∈ Icc 1 (j + 1), (FRD.Cj Pc msq (L : ℝ) k :
          Matrix (Grassmann.Torus 2 n) (Grassmann.Torus 2 n) ℝ)) -
          lfun (∑ k ∈ Icc 1 j, (FRD.Cj Pc msq (L : ℝ) k :
          Matrix (Grassmann.Torus 2 n) (Grassmann.Torus 2 n) ℝ)) -
            Real.log L / (2 * Real.pi) : ℝ)) : ℂ) := by
      rw [e1]; push_cast; ring
    rw [key]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    have : (D.L : ℝ) = L := rfl
    rw [this] at hdress
    linarith

end

end Step2.D2
