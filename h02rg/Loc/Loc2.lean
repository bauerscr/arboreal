import Loc.Loc2Large

/-!
# Lemma `lem:loc2`: the localisation contraction in `d = 2`

For `U(1)`-invariant `F ∈ 𝒩(X^□)`, `X` small, and field scales `ℓ' ≤ 2ℓ`,
`‖F - Loc2_X F‖_{T_{j+1}(ℓ')} ≤ C L^{-3} ‖F‖_{T_j(ℓ)}` (`loc2_contract`), where
`Loc2_X = Loc_X + Loc4_X` is the localisation of `d = 2` (the quartic marginal monomials
`ψ ψ̄ (∇_i ψ)(∇_k ψ̄)` are included, `Loc.Loc4Def`).

The pairing with a test function is split by the length `n` of the sequences:
* `n = 2`: `exists_two_bound` (Taylor remainder of order `3`);
* `n = 4`: `exists_four_bound` (Taylor remainder of order `3`, using `mu4 (F - Loc2_X F) = 0`);
* `n ≥ 5`: `exists_large_bound` (Pauli principle with one block);
* `n ∈ {0, 1, 3}`: the coefficients vanish.

Unlike `exists_contract_bound_gen`, no smallness of `ℓ'/ℓ` is needed: `ℓ' = 2ℓ` is allowed,
which is the case `ℓ_{j+1} = ℓ_j` of `d = 2`. With `Loc_X` in place of `Loc2_X` the bound fails
on sequences of length `4` (only `L^{-2}`, see `exists_long_bound`): the marginal quartic
monomials must be localised.
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD Equiv

variable {d L N : ℕ} [NeZero L]

theorem restr_decomp5 {X : Type*} (g : TestFn X) :
    g = restr (fun n => n = 2) g + restr (fun n => n = 4) g + restr (fun n => 5 ≤ n) g +
      restr (fun n => n ≠ 2 ∧ n ≠ 4 ∧ n < 5) g := by
  funext n z
  simp only [restr, Pi.add_apply]
  by_cases h2 : n = 2
  · subst h2; simp
  by_cases h4 : n = 4
  · subst h4; simp
  by_cases h5 : 5 ≤ n
  · simp [h2, h4, h5]
  · simp [h2, h4, h5, show n < 5 by omega]

theorem pair_decomp5 {X : Type*} [DecidableEq X] [Fintype X] (F : Grassmann.N X)
    (g : TestFn X) :
    pair F g = pair F (restr (fun n => n = 2) g) + pair F (restr (fun n => n = 4) g) +
      pair F (restr (fun n => 5 ≤ n) g) + pair F (restr (fun n => n ≠ 2 ∧ n ≠ 4 ∧ n < 5) g) := by
  conv_lhs => rw [restr_decomp5 g]
  have h : ∀ g₁ g₂ : TestFn X, pair F (g₁ + g₂) = pair F g₁ + pair F g₂ :=
    fun g₁ g₂ => map_add (pairR F) g₁ g₂
  simp only [h]

theorem mu_Loc4XY (b : Lam d L N) (X Y : Finset (Lam d L N)) (F : Alg d L N) (β : Mono d) :
    mu b β (Loc4XY X Y F) = 0 := by
  refine sum_eq_zero fun x _ => sum_eq_zero fun y _ => ?_
  rw [cf2, coeff_Loc4XY_of_ne X Y F _ (by decide), zero_mul]

theorem sub_Loc2X_eq (X : Finset (Lam d L N)) (F : Alg d L N) :
    F - Loc2X X F = (F - LocX X F) - Loc4X X F := by
  simp only [Loc2X, Loc2XY, LocX, Loc4X]; abel

theorem coeff_sub_Loc2X_of_ne (X : Finset (Lam d L N)) (F : Alg d L N) {n : ℕ}
    (z : Fin n → Sf (Lam d L N)) (hn0 : n ≠ 0) (hn2 : n ≠ 2) (hn4 : n ≠ 4) :
    coeff (F - Loc2X X F) z = coeff F z := by
  rw [sub_Loc2X_eq, sub_eq_add_neg (F - LocX X F), coeff_add, coeff_sub_LocX_of_ne X F z hn0 hn2,
    show -Loc4X X F = (-1 : ℂ) • Loc4X X F by simp, coeff_smul, Loc4X,
    coeff_Loc4XY_of_ne X X F z hn4]
  ring

/-- Lemma `lem:loc2` (`h02uv-outline.tex`). -/
theorem loc2_contract (d : ℕ) (hd : 2 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧ ∃ L₀ : ℕ,
    ∀ (L : ℕ) [NeZero L], 2 ^ (d + 3) + 8 * d < L → L₀ ≤ L → ∀ N j : ℕ, j < N →
    ∀ ℓ ℓ' : ℝ, 0 < ℓ → 0 < ℓ' → ℓ' ≤ 2 * ℓ →
    ∀ X : Finset (Lam d L N), IsSmall j X → ∀ F ∈ NX (nbhd j X : Set (Lam d L N)), IsSym F →
      Tj d (L : ℝ) (j + 1) ℓ' (F - Loc2X X F) ≤
        ENNReal.ofReal (C / (L : ℝ) ^ 3) * Tj d (L : ℝ) j ℓ F := by
  obtain ⟨C2, hC2, hC2b⟩ := exists_two_bound d hd
  obtain ⟨C4, hC4, hC4b⟩ := exists_four_bound d hd
  obtain ⟨C5, hC5, L₀, hC5b⟩ := exists_large_bound d (by omega)
  obtain ⟨Cb, hCb, hCbb⟩ := exists_Loc2XY_bound d (by omega)
  refine ⟨(1 + Cb) * (4 * C2 + 16 * C4) + C5, by positivity, L₀, ?_⟩
  intro L _ hL hL₀ N j hj ℓ ℓ' hℓ hℓ' hℓℓ X hX F hF hsym
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hL0 : (0 : ℝ) < L := by linarith
  set r : ℝ := ℓ' / ℓ with hrdef
  have hr0 : 0 ≤ r := by positivity
  have hr2 : r ≤ 2 := by rw [hrdef, div_le_iff₀ hℓ]; linarith
  have hratio : ℓ' * ℓ⁻¹ = r := by rw [hrdef, div_eq_mul_inv]
  set s : ℝ := (L : ℝ) ^ j
  have hs : 0 < s := by positivity
  have hh' : (0 : ℝ) < (L : ℝ) ^ (j + 1) := by positivity
  set T : ℝ := (Tj d (L : ℝ) j ℓ F).toReal
  have hT : 0 ≤ T := ENNReal.toReal_nonneg
  have hTF : Tj d (L : ℝ) j ℓ F = ENNReal.ofReal T :=
    (ENNReal.ofReal_toReal (tNorm_ne_top hs hℓ F)).symm
  have hne : X.Nonempty := hX.2.1.1
  have hpatch := patch_of_small hL hj hX
  set G := F - Loc2X X F with hGdef
  have hGmem : G ∈ NX (nbhd j X : Set (Lam d L N)) :=
    sub_mem hF (Subalgebra.add_mem _ (LocXY_mem (by omega) hX.1 X F)
      (Loc4XY_mem (by omega) hX.1 X F))
  -- the norm of `G` at scale `j`
  have hTG : (Tj d (L : ℝ) j ℓ G).toReal ≤ (1 + Cb) * T := by
    have h1 := tNorm_sub_le (E := Dir d) (p := pPhi d) (h := (L : ℝ) ^ j) (ℓ := ℓ) F (Loc2X X F)
    have h2 := hCbb L hL N j hj X X hX subset_rfl F hF ℓ hℓ
    have h3 : Tj d (L : ℝ) j ℓ G ≤ ENNReal.ofReal ((1 + Cb) * T) := by
      refine h1.trans ?_
      rw [show tNorm (Dir d) (pPhi d) ((L : ℝ) ^ j) ℓ F = Tj d (L : ℝ) j ℓ F from rfl, hTF]
      calc ENNReal.ofReal T + tNorm (Dir d) (pPhi d) ((L : ℝ) ^ j) ℓ (Loc2X X F)
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
  have hga : ∀ a a' : Sf (Lam d L N), g' 2 ![a', a] = -g' 2 ![a, a'] := fun a a' => by
    have := asym_perm g ![a, a'] (Equiv.swap 0 1)
    have e : (![a, a'] ∘ Equiv.swap (0 : Fin 2) 1) = ![a', a] := by
      funext i; fin_cases i <;> rfl
    rw [e, Perm.sign_swap (by decide)] at this
    simpa using this
  rw [← pair_asym, pair_decomp5]
  -- the four pieces
  have hrest : pair G (restr (fun n => n ≠ 2 ∧ n ≠ 4 ∧ n < 5) g') = 0 := by
    refine pair_restr_eq_zero _ _ fun n z hn => ?_
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      rw [coeff_elim0, hGdef, sub_Loc2X_eq, map_sub, eps_sub_LocX hne, Loc4X, eps_Loc4XY,
        sub_zero]
    · rw [coeff_sub_Loc2X_of_ne X F z (by omega) hn.1 hn.2.1]
      exact coeff_eq_zero_of_odd hsym (Nat.odd_iff.2 (by omega)) z
  have h5 : ‖pair G (restr (fun n => 5 ≤ n) g')‖ ≤ T * (C5 / (L : ℝ) ^ 3) := by
    rw [pair_restr_congr (G := F) _ _ fun n z hn =>
      coeff_sub_Loc2X_of_ne X F z (by omega) (by omega) (by omega)]
    exact hC5b L hL hL₀ N j hj X hX F hF ℓ ℓ' hℓ hℓ' hℓℓ g' hg'
  have h4 : ‖pair G (restr (fun n => n = 4) g')‖ ≤ (1 + Cb) * T * (C4 * r ^ 4 / (L : ℝ) ^ 3) := by
    rw [pair_restr_eq_single]
    have hGs : ∀ z : Fin 4 → Sf (Lam d L N), ¬U1 (spins z) → coeff G z = 0 := by
      intro z hz
      rw [hGdef, sub_Loc2X_eq, sub_eq_add_neg (F - LocX X F), coeff_add,
        coeff_sub_LocX_of_ne X F z (by decide) (by decide),
        show -Loc4X X F = (-1 : ℂ) • Loc4X X F by simp, coeff_smul, Loc4X,
        hsym 4 z hz, isSym_Loc4XY X X F 4 z hz]
      ring
    have := hC4b L hL N j hj X hX G hGmem hGs (fun i k => mu4_sub_Loc2X hpatch hne F i k) ℓ ℓ'
      hℓ hℓ' (g' 4) (hgb 4)
    refine this.trans ?_
    have hq : 0 ≤ C4 * ℓ' ^ 4 * ℓ⁻¹ ^ 4 / (L : ℝ) ^ 3 := by positivity
    calc (Tj d (L : ℝ) j ℓ G).toReal * (C4 * ℓ' ^ 4 * ℓ⁻¹ ^ 4 / (L : ℝ) ^ 3)
        ≤ (1 + Cb) * T * (C4 * ℓ' ^ 4 * ℓ⁻¹ ^ 4 / (L : ℝ) ^ 3) :=
          mul_le_mul_of_nonneg_right hTG hq
      _ = (1 + Cb) * T * (C4 * (ℓ' * ℓ⁻¹) ^ 4 / (L : ℝ) ^ 3) := by ring
      _ = _ := by rw [hratio]
  have h2 : ‖pair G (restr (fun n => n = 2) g')‖ ≤ (1 + Cb) * T * (C2 * r ^ 2 / (L : ℝ) ^ 3) := by
    rw [pair_restr_eq_single]
    have hGs : ∀ (a a' : Lam d L N) (σ : ℤˣ), coeff G ![(a, σ), (a', σ)] = 0 := by
      intro a a' σ
      rw [hGdef, sub_Loc2X_eq, sub_eq_add_neg (F - LocX X F), coeff_add,
        coeff_sub_LocX_same X hsym, show -Loc4X X F = (-1 : ℂ) • Loc4X X F by simp, coeff_smul,
        Loc4X, coeff_Loc4XY_of_ne X X F _ (by decide)]
      ring
    have hGμ : ∀ β : Mono d, mu (base X) β G = 0 := by
      intro β
      rw [hGdef, sub_Loc2X_eq, sub_eq_add_neg (F - LocX X F), mu_add, mu_sub_LocX hpatch hne F,
        show -Loc4X X F = (-1 : ℂ) • Loc4X X F by simp, mu_smul, Loc4X, mu_Loc4XY]
      ring
    have := hC2b L hL N j hj X hX G hGmem hGs hGμ ℓ ℓ' hℓ hℓ' (g' 2) hga (hgb 2)
    refine this.trans ?_
    have hq : 0 ≤ C2 * ℓ' ^ 2 * ℓ⁻¹ ^ 2 / (L : ℝ) ^ 3 := by positivity
    calc (Tj d (L : ℝ) j ℓ G).toReal * (C2 * ℓ' ^ 2 * ℓ⁻¹ ^ 2 / (L : ℝ) ^ 3)
        ≤ (1 + Cb) * T * (C2 * ℓ' ^ 2 * ℓ⁻¹ ^ 2 / (L : ℝ) ^ 3) :=
          mul_le_mul_of_nonneg_right hTG hq
      _ = (1 + Cb) * T * (C2 * (ℓ' * ℓ⁻¹) ^ 2 / (L : ℝ) ^ 3) := by ring
      _ = _ := by rw [hratio]
  rw [hrest, add_zero]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h2 h4)) h5)
    |>.trans ?_
  have hL3 : (0 : ℝ) < (L : ℝ) ^ 3 := by positivity
  have er2 : r ^ 2 ≤ 4 := by nlinarith
  have er4 : r ^ 4 ≤ 16 := by nlinarith [sq_nonneg r, mul_nonneg hr0 hr0]
  have e1 : C2 * r ^ 2 / (L : ℝ) ^ 3 ≤ C2 * 4 / (L : ℝ) ^ 3 := by gcongr
  have e2 : C4 * r ^ 4 / (L : ℝ) ^ 3 ≤ C4 * 16 / (L : ℝ) ^ 3 := by gcongr
  have hTb : 0 ≤ (1 + Cb) * T := by positivity
  calc (1 + Cb) * T * (C2 * r ^ 2 / (L : ℝ) ^ 3) + (1 + Cb) * T * (C4 * r ^ 4 / (L : ℝ) ^ 3) +
        T * (C5 / (L : ℝ) ^ 3)
      ≤ (1 + Cb) * T * (C2 * 4 / (L : ℝ) ^ 3) + (1 + Cb) * T * (C4 * 16 / (L : ℝ) ^ 3) +
        T * (C5 / (L : ℝ) ^ 3) := by gcongr
    _ = ((1 + Cb) * (4 * C2 + 16 * C4) + C5) / (L : ℝ) ^ 3 * T := by ring

end

end Loc
