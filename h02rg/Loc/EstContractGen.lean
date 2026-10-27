import Loc.EstContract

/-!
# The contraction bound for general field scales (every `d ≥ 2`)

`exists_contract_bound_gen`: for `U(1)`-invariant `F ∈ 𝒩(X^□)` and field scales `ℓ' ≤ ℓ`,
`‖(1 - Loc_X) F‖_{T_{j+1}(ℓ')} ≤ C (r²/L³ + r⁴/L² + r⁸) ‖F‖_{T_j(ℓ)}`, `r = ℓ'/ℓ`.

This is the bound of `exists_contract_bound` before the choice `ℓ = ℓ_j`, `ℓ' = 2ℓ_{j+1}`,
`r = 2L^{-(d-2)/2}`; it holds in every dimension `d ≥ 2`. In `d ≥ 3` it gives `prop:Loc`(ii).
In `d = 2` with `ℓ' = 2ℓ` it does not apply (`r = 2 > 1`); see `h02uv-outline.tex`,
Lemmas `lem:pauli` and `lem:loc2`.

`Loc_bound_gen` is `prop:Loc`(i) in every dimension `d ≥ 1`.
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD Equiv

variable {d : ℕ}

/-- `prop:Loc`(i) in every dimension and for every field scale `ℓ`. -/
theorem Loc_bound_gen (hd : 1 ≤ d) : ∃ Cbar : ℝ, ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∀ N j : ℕ, j < N → ∀ ℓ : ℝ, 0 < ℓ → ∀ X Y : Finset (Lam d L N), IsSmall j X →
    IsSmall j Y → Y ⊆ X → ∀ F ∈ NX (nbhd j X : Set (Lam d L N)),
      Tj d (L : ℝ) j ℓ (LocXY X Y F) ≤ ENNReal.ofReal Cbar * Tj d (L : ℝ) j ℓ F := by
  obtain ⟨C, _, hC⟩ := exists_LocXY_bound d hd
  refine ⟨C, 2 ^ (d + 3) + 8 * d + 1, ?_⟩
  intro L _ hL N j hj ℓ hℓ X Y hX _ hYX F hF
  exact hC L (by omega) N j hj X Y hX hYX F hF _ hℓ

theorem exists_contract_bound_gen (d : ℕ) (hd : 2 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℕ) [NeZero L],
    2 ^ (d + 3) + 8 * d < L → ∀ N j : ℕ, j < N → ∀ ℓ ℓ' : ℝ, 0 < ℓ → 0 < ℓ' → ℓ' ≤ ℓ →
    ∀ X : Finset (Lam d L N), IsSmall j X → ∀ F ∈ NX (nbhd j X : Set (Lam d L N)), IsSym F →
      Tj d (L : ℝ) (j + 1) ℓ' (F - LocX X F) ≤
        ENNReal.ofReal (C * ((ℓ' / ℓ) ^ 2 / (L : ℝ) ^ 3 + (ℓ' / ℓ) ^ 4 / (L : ℝ) ^ 2 +
          (ℓ' / ℓ) ^ 8)) * Tj d (L : ℝ) j ℓ F := by
  obtain ⟨C4, hC4, hC4b⟩ := exists_long_bound d 4 (by omega) le_rfl
  obtain ⟨C6, hC6, hC6b⟩ := exists_long_bound d 6 (by omega) (by norm_num)
  obtain ⟨C2, hC2, hC2b⟩ := exists_two_bound d (by omega)
  obtain ⟨Cb, hCb, hCbb⟩ := exists_LocXY_bound d (by omega)
  refine ⟨1 + C4 + C6 + (1 + Cb) * C2, by positivity, ?_⟩
  intro L _ hL N j hj ℓ ℓ' hℓ hℓ' hℓ'ℓ X hX F hF hsym
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hL0 : (0 : ℝ) < L := by linarith
  have hL4 : (4 : ℝ) ≤ L := by
    have : 4 ≤ L := by have := Nat.one_le_two_pow (n := d + 3); omega
    exact_mod_cast this
  set r : ℝ := ℓ' / ℓ with hrdef
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 := by rw [hrdef, div_le_one hℓ]; exact hℓ'ℓ
  have hratio : ℓ' * ℓ⁻¹ = r := by rw [hrdef, div_eq_mul_inv]
  set s : ℝ := (L : ℝ) ^ j
  have hs : 0 < s := by positivity
  have hh' : (0 : ℝ) < (L : ℝ) ^ (j + 1) := by positivity
  have hss : s ≤ (L : ℝ) ^ (j + 1) := by
    rw [pow_succ]; exact le_mul_of_one_le_right hs.le hL1
  set T : ℝ := (Tj d (L : ℝ) j ℓ F).toReal
  have hT : 0 ≤ T := ENNReal.toReal_nonneg
  have hTF : Tj d (L : ℝ) j ℓ F = ENNReal.ofReal T :=
    (ENNReal.ofReal_toReal (tNorm_ne_top hs hℓ F)).symm
  have hne : X.Nonempty := hX.2.1.1
  have hpatch := patch_of_small hL hj hX
  set G := F - LocX X F with hGdef
  have hGmem : G ∈ NX (nbhd j X : Set (Lam d L N)) :=
    sub_mem hF (LocXY_mem (by omega) hX.1 X F)
  -- the norm of `G` at scale `j`
  have hTG : (Tj d (L : ℝ) j ℓ G).toReal ≤ (1 + Cb) * T := by
    have h1 := tNorm_sub_le (E := Dir d) (p := pPhi d) (h := (L : ℝ) ^ j) (ℓ := ℓ) F (LocX X F)
    have h2 := hCbb L hL N j hj X X hX subset_rfl F hF ℓ hℓ
    have h3 : Tj d (L : ℝ) j ℓ G ≤ ENNReal.ofReal ((1 + Cb) * T) := by
      refine h1.trans ?_
      rw [show tNorm (Dir d) (pPhi d) ((L : ℝ) ^ j) ℓ F = Tj d (L : ℝ) j ℓ F from rfl, hTF]
      calc ENNReal.ofReal T + tNorm (Dir d) (pPhi d) ((L : ℝ) ^ j) ℓ (LocX X F)
          ≤ ENNReal.ofReal T + ENNReal.ofReal Cb * ENNReal.ofReal T := by
            gcongr
            rw [← hTF]; exact h2
        _ = ENNReal.ofReal ((1 + Cb) * T) := by
            rw [← ENNReal.ofReal_mul hCb, ← ENNReal.ofReal_add hT (by positivity)]
            congr 1; ring
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) h3
  -- reduce to test functions
  rw [hTF, ← ENNReal.ofReal_mul (by positivity)]
  refine tNorm_le fun g hg => ?_
  set g' := asym g
  have hg' : phiNorm (Dir d) (pPhi d) ((L : ℝ) ^ (j + 1)) ℓ' g' ≤ 1 :=
    (phiNorm_asym_le hh'.le hℓ' g).trans hg
  have hgb : ∀ (n : ℕ) (z : Fin n → Sf (Lam d L N)) (γ : Fin n → Dir d → ℕ),
      (∀ k, mabs (γ k) ≤ pPhi d) → ‖nab γ (g' n) z‖ ≤ ℓ' ^ n * (((L : ℝ) ^ (j + 1)) ^ ord γ)⁻¹ :=
    fun n z γ hγ => by
      have := abs_nab_le hh' hℓ' zero_le_one (by rwa [ENNReal.ofReal_one]) (g := g') z γ hγ
      rwa [one_mul] at this
  have hg0 : ∀ (n : ℕ) (z : Fin n → Sf (Lam d L N)), ¬Function.Injective z → g' n z = 0 :=
    fun n z hz => asym_eq_zero_of_not_injective g hz
  have hga : ∀ a a' : Sf (Lam d L N), g' 2 ![a', a] = -g' 2 ![a, a'] := fun a a' => by
    have := asym_perm g ![a, a'] (Equiv.swap 0 1)
    have e : (![a, a'] ∘ Equiv.swap (0 : Fin 2) 1) = ![a', a] := by
      funext i; fin_cases i <;> rfl
    rw [e, Perm.sign_swap (by decide)] at this
    simpa using this
  rw [← pair_asym, pair_decomp]
  -- the five pieces
  have hrest : pair G (restr (fun n => n ≠ 2 ∧ n ≠ 4 ∧ n ≠ 6 ∧ n < 8) g') = 0 := by
    refine pair_restr_eq_zero _ _ fun n z hn => ?_
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      rw [coeff_elim0, eps_sub_LocX hne]
    · rw [coeff_sub_LocX_of_ne X F z (by omega) hn.1]
      exact coeff_eq_zero_of_odd hsym (Nat.odd_iff.2 (by omega)) z
  have hcong : ∀ m : ℕ, m ≠ 0 → m ≠ 2 →
      pair G (restr (fun n => n = m) g') = pair F (restr (fun n => n = m) g') :=
    fun m hm0 hm2 => pair_restr_congr _ _ fun n z hn => by
      subst hn; exact coeff_sub_LocX_of_ne X F z hm0 hm2
  have h8 : ‖pair G (restr (fun n => 8 ≤ n) g')‖ ≤ T * r ^ 8 := by
    rw [pair_restr_congr (G := F) _ _ fun n z hn =>
      coeff_sub_LocX_of_ne X F z (by omega) (by omega)]
    have hn := phiNorm_restr_ge_le hs hss hℓ hℓ' hℓ'ℓ hg' 8
    have := abs_pair_le hs hℓ F (by positivity) hn
    rw [div_eq_mul_inv, hratio] at this
    exact this
  have h4 : ‖pair G (restr (fun n => n = 4) g')‖ ≤ T * (C4 * r ^ 4 / (L : ℝ) ^ 2) := by
    rw [hcong 4 (by norm_num) (by norm_num), pair_restr_eq_single]
    have := hC4b L hL N j hj X hX F hF hsym ℓ ℓ' hℓ hℓ' (g' 4) (hg0 4) (hgb 4)
    refine this.trans (le_of_eq ?_)
    rw [← hratio]; ring
  have h6 : ‖pair G (restr (fun n => n = 6) g')‖ ≤ T * (C6 * r ^ 6 / (L : ℝ) ^ 2) := by
    rw [hcong 6 (by norm_num) (by norm_num), pair_restr_eq_single]
    have := hC6b L hL N j hj X hX F hF hsym ℓ ℓ' hℓ hℓ' (g' 6) (hg0 6) (hgb 6)
    refine this.trans (le_of_eq ?_)
    rw [← hratio]; ring
  have h2 : ‖pair G (restr (fun n => n = 2) g')‖ ≤
      (1 + Cb) * T * (C2 * r ^ 2 / (L : ℝ) ^ 3) := by
    rw [pair_restr_eq_single]
    have := hC2b L hL N j hj X hX G hGmem (coeff_sub_LocX_same X hsym)
      (mu_sub_LocX hpatch hne F) ℓ ℓ' hℓ hℓ' (g' 2) hga (hgb 2)
    refine this.trans ?_
    have hq : 0 ≤ C2 * ℓ' ^ 2 * ℓ⁻¹ ^ 2 / (L : ℝ) ^ 3 := by positivity
    calc (Tj d (L : ℝ) j ℓ G).toReal * (C2 * ℓ' ^ 2 * ℓ⁻¹ ^ 2 / (L : ℝ) ^ 3)
        ≤ (1 + Cb) * T * (C2 * ℓ' ^ 2 * ℓ⁻¹ ^ 2 / (L : ℝ) ^ 3) :=
          mul_le_mul_of_nonneg_right hTG hq
      _ = (1 + Cb) * T * (C2 * (ℓ' * ℓ⁻¹) ^ 2 / (L : ℝ) ^ 3) := by ring
      _ = _ := by rw [hratio]
  have hsum : ‖pair G (restr (fun n => n = 2) g') + pair G (restr (fun n => n = 4) g') +
      pair G (restr (fun n => n = 6) g') + pair G (restr (fun n => 8 ≤ n) g') +
      pair G (restr (fun n => n ≠ 2 ∧ n ≠ 4 ∧ n ≠ 6 ∧ n < 8) g')‖ ≤
      (1 + Cb) * T * (C2 * r ^ 2 / (L : ℝ) ^ 3) + T * (C4 * r ^ 4 / (L : ℝ) ^ 2) +
        T * (C6 * r ^ 6 / (L : ℝ) ^ 2) + T * r ^ 8 := by
    rw [hrest, add_zero]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add h2 h4)) h6)) h8)
  refine hsum.trans ?_
  have hr64 : r ^ 6 ≤ r ^ 4 := pow_le_pow_of_le_one hr0 hr1 (by norm_num)
  have hL2 : (0 : ℝ) < (L : ℝ) ^ 2 := by positivity
  have hL3 : (0 : ℝ) < (L : ℝ) ^ 3 := by positivity
  have a2 : 0 ≤ r ^ 2 / (L : ℝ) ^ 3 := by positivity
  have a4 : 0 ≤ r ^ 4 / (L : ℝ) ^ 2 := by positivity
  have a8 : 0 ≤ r ^ 8 := by positivity
  have e6 : r ^ 6 / (L : ℝ) ^ 2 ≤ r ^ 4 / (L : ℝ) ^ 2 := div_le_div_of_nonneg_right hr64 hL2.le
  have hCb0 : 0 ≤ (1 + Cb) * C2 := by positivity
  calc (1 + Cb) * T * (C2 * r ^ 2 / (L : ℝ) ^ 3) + T * (C4 * r ^ 4 / (L : ℝ) ^ 2) +
        T * (C6 * r ^ 6 / (L : ℝ) ^ 2) + T * r ^ 8
      = T * (((1 + Cb) * C2) * (r ^ 2 / (L : ℝ) ^ 3) + C4 * (r ^ 4 / (L : ℝ) ^ 2) +
          C6 * (r ^ 6 / (L : ℝ) ^ 2) + r ^ 8) := by ring
    _ ≤ T * (((1 + Cb) * C2) * (r ^ 2 / (L : ℝ) ^ 3) + C4 * (r ^ 4 / (L : ℝ) ^ 2) +
          C6 * (r ^ 4 / (L : ℝ) ^ 2) + r ^ 8) := by gcongr
    _ ≤ T * ((1 + C4 + C6 + (1 + Cb) * C2) *
          (r ^ 2 / (L : ℝ) ^ 3 + r ^ 4 / (L : ℝ) ^ 2 + r ^ 8)) := by
        refine mul_le_mul_of_nonneg_left ?_ hT
        nlinarith [mul_nonneg hC4 a2, mul_nonneg hC4 a8, mul_nonneg hC6 a2, mul_nonneg hC6 a8,
          mul_nonneg hCb0 a4, mul_nonneg hCb0 a8, a2, a4, a8]
    _ = _ := by ring

end

end Loc
