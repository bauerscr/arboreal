import Obs2.Pair.AnchAB
import Obs2.Est.EstLoc
import Obs2.Loc.LocT

/-!
# The `σ_aσ_b` estimate layer on `abSub` (`w_{ab} > 0`)

On elements without one-point parts (`Obs2.abSub`) the observable part of the norm is the
`σ_aσ_b` part alone, `‖π_{obs}F‖ = w_{ab}‖F_{ab}‖` (`oTo_of_ab`), for **any** weights; the
product rule is linear in the observable data, `π_{ab}(FG) = F_∅G_{ab} + F_{ab}G_∅`
(`oTo_mul_ab`), so the `ab` sector behaves like a single-source sector. The primitives:

* `oTo_EthO_le2_ab`: the two-scale (Pauli) bound `‖𝔼_Cθ F‖_{T_{j+1}(ℓ')} ≤ q^{|𝓑_j(Y)|}
  ‖F‖_{T_j(ℓ)}` on the `ab` part (support `F_{ab} ∈ 𝒩(Y)`), and `oTo_EthO_le2'` (any `w`);
* `exists_LocO2_ab_bound`: `‖π_{obs}Loc_{X,Y}F‖ ≤ C‖π_{obs}F‖` for `X` small, `Y ⊆ X`
  (barycentric `loc^{ab}`, `exists_locABt_bound`; `0` if `X ∩ {a,b} = ∅`);
* **`exists_LocO2_anch_contract`**: `‖π_{obs}(F - Loc_{X,X}F)‖_{T_{j+1}(ℓ')} ≤ (C/L)
  ‖π_{obs}F‖_{T_j(ℓ)}` for `F` anchored at `X` (`Obs2.anc`, `exists_locABt_contract`);
* **`tNorm_m4_le`** (Pauli quartic): `‖ψ̄_aψ_aψ̄_bψ_b‖_{T_h(ℓ)} ≤ ℓ⁴(|a-b|_1/h)²`
  (`ψ̄_aψ_aψ̄_bψ_b = ψ̄_aψ_aδ̄δ`, `pbp_dbar_dlt`); at `h = L^k` this is `≲ (|a-b|/L^k)²`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD ENNReal

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

local notation "AB" => (abSub : Subalgebra ℂ (OE c (Lam d L N)))

/-! ### The norm on `abSub` -/

theorem oTo_of_ab (w : Wt) (j : ℕ) (ℓ : ℝ) {F : OE c (Lam d L N)} (hF : F ∈ AB) :
    oTo w j ℓ F = w.ab * Tj d (L : ℝ) j ℓ (F : SA c (Lam d L N)).ab := by
  simp only [oTo, oTj, oNorm, coe_πobs, piobs_apply, hF.1, hF.2, tNorm_zero', mul_zero,
    zero_add]

theorem ab_mul_of_ab {F G : OE c (Lam d L N)} (hF : F ∈ AB) (hG : G ∈ AB) :
    ((F * G : OE c (Lam d L N)) : SA c (Lam d L N)).ab =
      (F : SA c (Lam d L N)).e * (G : SA c (Lam d L N)).ab +
        (F : SA c (Lam d L N)).ab * (G : SA c (Lam d L N)).e := by
  rw [OE.mul_ab, hF.1, hF.2, hG.1, hG.2]; simp

/-- **The product rule on `abSub`** (linear in the observable data). -/
theorem oTo_mul_ab (w : Wt) {j : ℕ} {ℓ : ℝ} (hh : (0 : ℝ) < (L : ℝ) ^ j) (hℓ : 0 < ℓ)
    {F G : OE c (Lam d L N)} (hF : F ∈ AB) (hG : G ∈ AB) :
    oTo w j ℓ (F * G) ≤ Tj d (L : ℝ) j ℓ (F : SA c (Lam d L N)).e * oTo w j ℓ G +
      oTo w j ℓ F * Tj d (L : ℝ) j ℓ (G : SA c (Lam d L N)).e := by
  rw [oTo_of_ab w j ℓ (mul_mem hF hG), oTo_of_ab w j ℓ hF, oTo_of_ab w j ℓ hG,
    ab_mul_of_ab hF hG]
  calc w.ab * Tj d (L : ℝ) j ℓ ((F : SA c (Lam d L N)).e * (G : SA c (Lam d L N)).ab +
        (F : SA c (Lam d L N)).ab * (G : SA c (Lam d L N)).e)
      ≤ w.ab * (Tj d (L : ℝ) j ℓ (F : SA c (Lam d L N)).e *
          Tj d (L : ℝ) j ℓ (G : SA c (Lam d L N)).ab +
        Tj d (L : ℝ) j ℓ (F : SA c (Lam d L N)).ab *
          Tj d (L : ℝ) j ℓ (G : SA c (Lam d L N)).e) := by
        gcongr
        exact (tNorm_add_le _ _).trans (add_le_add (tNorm_mul_le hh hℓ _ _)
          (tNorm_mul_le hh hℓ _ _))
    _ = _ := by ring

/-! ### Expectation -/

/-! ### Localisation -/

theorem norm_ratio_le {P : ObsPts d L N} {X Y : Finset (Lam d L N)} (hYX : Y ⊆ X) :
    ‖(((Y ∩ P.pts).card : ℂ) / ((X ∩ P.pts).card : ℂ))‖ ≤ 1 := by
  rw [norm_div, Complex.norm_natCast, Complex.norm_natCast]
  rcases Nat.eq_zero_or_pos (X ∩ P.pts).card with h0 | hpos
  · simp [h0]
  · rw [div_le_one (by exact_mod_cast hpos)]
    exact_mod_cast card_le_card (inter_subset_inter_right hYX)

theorem mem_b_of_inter {P : ObsPts d L N} {X : Finset (Lam d L N)} (hne : (X ∩ P.pts).Nonempty)
    (ha : P.a ∉ X) : P.b ∈ X := by
  obtain ⟨z, hz⟩ := hne
  rw [mem_inter, ObsPts.pts, mem_insert, mem_singleton] at hz
  rcases hz.2 with rfl | rfl
  · exact absurd hz.1 ha
  · exact hz.1

/-- **`loc^{ab}_{X,Y}` is bounded** (barycentric, `X` small, `Y ⊆ X`). -/
theorem exists_LocO2_ab_bound (d : ℕ) (hd : 1 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℕ) [NeZero L],
    2 ^ (d + 3) + 8 * d < L → ∀ N : ℕ, ∀ (c : Obs.Case) (P : ObsPts d L N) (w : Wt),
    ∀ k : ℕ, k < N → ∀ ℓ : ℝ, 0 < ℓ → ∀ X Y : Finset (Lam d L N), IsSmall k X → Y ⊆ X →
    ∀ F : OE c (Lam d L N), F ∈ (abSub : Subalgebra ℂ (OE c (Lam d L N))) →
      (F : SA c (Lam d L N)).ab ∈ NX (nbhd k X : Set (Lam d L N)) →
      oTo w k ℓ (LocO2 P X Y F) ≤ ENNReal.ofReal C * oTo w k ℓ F := by
  obtain ⟨C, hC, h⟩ := exists_locABt_bound d hd
  refine ⟨C, hC, fun L _ hL N c P w k hk ℓ hℓ X Y hX hYX F hF hFn => ?_⟩
  rw [oTo_of_ab w _ _ (LocO2_mem_ab P X Y hF), oTo_of_ab w _ _ hF]
  have key : Tj d (L : ℝ) k ℓ (locABtXY P X Y (F : SA c (Lam d L N)).ab) ≤
      ENNReal.ofReal C * Tj d (L : ℝ) k ℓ (F : SA c (Lam d L N)).ab := by
    rw [locABtXY]
    by_cases hne : (X ∩ P.pts).Nonempty
    · refine (tNorm_smul_le _ _).trans ?_
      have hr := ENNReal.ofReal_le_ofReal (norm_ratio_le (P := P) hYX)
      rw [ENNReal.ofReal_one] at hr
      refine (mul_le_mul' hr le_rfl).trans ?_
      rw [one_mul, locABtX]
      split_ifs with ha
      · exact h L hL N k hk ℓ hℓ X hX P.a P.b ha _ hFn
      · exact h L hL N k hk ℓ hℓ X hX P.b P.a (mem_b_of_inter hne ha) _ hFn
    · have h0 : (((Y ∩ P.pts).card : ℂ) / ((X ∩ P.pts).card : ℂ)) = 0 := by
        simp [Finset.not_nonempty_iff_eq_empty.1 hne]
      rw [h0, zero_smul, Step.Tj_zero]
      exact zero_le
  calc w.ab * Tj d (L : ℝ) k ℓ (LocO2 P X Y F : SA c (Lam d L N)).ab
      ≤ w.ab * (ENNReal.ofReal C * Tj d (L : ℝ) k ℓ (F : SA c (Lam d L N)).ab) := by
        gcongr; exact key
    _ = _ := by ring

theorem ab_sub_LocO2 (P : ObsPts d L N) (X Y : Finset (Lam d L N)) (F : OE c (Lam d L N)) :
    ((F - LocO2 P X Y F : OE c (Lam d L N)) : SA c (Lam d L N)).ab =
      (F : SA c (Lam d L N)).ab - locABtXY P X Y (F : SA c (Lam d L N)).ab := rfl

/-- **`(1 - loc^{ab})` contracts on anchored elements**: for `X` small and `F` anchored at `X`
(`F_{ab} = 0` unless `X ∩ {a,b} ≠ ∅`), `U(1)`-invariant `F_{ab} ∈ 𝒩(X^□)` and `ℓ' ≤ 2ℓ`,
`‖π_{obs}(F - Loc_{X,X}F)‖_{T_{j+1}(ℓ')} ≤ (C/L)‖π_{obs}F‖_{T_j(ℓ)}` (any weights). -/
theorem exists_LocO2_anch_contract (d : ℕ) (hd : 1 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧ ∃ L₀ : ℕ,
    ∀ (L : ℕ) [NeZero L], 2 ^ (d + 3) + 8 * d < L → L₀ ≤ L → ∀ N j : ℕ, j < N →
    ∀ ℓ ℓ' : ℝ, 0 < ℓ → 0 < ℓ' → ℓ' ≤ 2 * ℓ →
    ∀ (c : Obs.Case) (P : ObsPts d L N) (w : Wt) (X : Finset (Lam d L N)), IsSmall j X →
    ∀ F : OE c (Lam d L N), F ∈ (anc P X : Subalgebra ℂ (OE c (Lam d L N))) →
      (F : SA c (Lam d L N)).ab ∈ NX (nbhd j X : Set (Lam d L N)) →
      IsSym (F : SA c (Lam d L N)).ab →
      oTo w (j + 1) ℓ' (F - LocO2 P X X F) ≤ ENNReal.ofReal (C / L) * oTo w j ℓ F := by
  obtain ⟨C, hC, L₀, h⟩ := exists_locABt_contract d hd
  refine ⟨C, hC, L₀, fun L _ hL hL₀ N j hj ℓ ℓ' hℓ hℓ' hℓℓ c P w X hX F hF hFn hFs => ?_⟩
  have hab := anchSub_ab hF
  rw [oTo_of_ab w _ _ (sub_mem hab (LocO2_mem_ab P X X hab)), oTo_of_ab w _ _ hab, ab_sub_LocO2]
  have key : Tj d (L : ℝ) (j + 1) ℓ' ((F : SA c (Lam d L N)).ab -
      locABtXY P X X (F : SA c (Lam d L N)).ab) ≤
      ENNReal.ofReal (C / L) * Tj d (L : ℝ) j ℓ (F : SA c (Lam d L N)).ab := by
    by_cases hne : (X ∩ P.pts).Nonempty
    · rw [locABtXY_self P X hne, locABtX]
      split_ifs with ha
      · exact h L hL hL₀ N j hj ℓ ℓ' hℓ hℓ' hℓℓ X hX P.a P.b ha _ hFn hFs
      · exact h L hL hL₀ N j hj ℓ ℓ' hℓ hℓ' hℓℓ X hX P.b P.a (mem_b_of_inter hne ha) _ hFn hFs
    · rw [hF.2.2 hne, locABtXY_zero, sub_zero, Step.Tj_zero]
      exact zero_le
  calc w.ab * Tj d (L : ℝ) (j + 1) ℓ' ((F : SA c (Lam d L N)).ab -
        locABtXY P X X (F : SA c (Lam d L N)).ab)
      ≤ w.ab * (ENNReal.ofReal (C / L) * Tj d (L : ℝ) j ℓ (F : SA c (Lam d L N)).ab) := by
        gcongr
    _ = _ := by ring

/-! ### The Pauli quartic -/

/-- **The quartic `ψ̄_aψ_aψ̄_bψ_b` is Pauli-small**: `‖ψ̄_aψ_aψ̄_bψ_b‖_{T_h(ℓ)} ≤
ℓ² (|e|_1 ℓ/h)²`, `|e|_1` the distance of `a, b` in the coordinates of `X` (`eN1`). -/
theorem tNorm_m4_le (hd : 1 ≤ d) {h ℓ : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ) (X : Finset (Lam d L N))
    (a b : Lam d L N) :
    tNorm (Dir d) (pPhi d) h ℓ (m4 a b : Alg d L N) ≤
      ENNReal.ofReal (ℓ * ℓ * ((eN1 X a b * ℓ * h⁻¹) * (eN1 X a b * ℓ * h⁻¹))) := by
  rw [← pbp_dbar_dlt]
  have he : 0 ≤ eN1 X a b * ℓ * h⁻¹ := by
    have := eN1_nonneg X a b; positivity
  exact tn_mul_bound hh hℓ (by positivity) (tNorm_pbp_le hh hℓ a)
    (tn_mul_bound hh hℓ he (tNorm_dbar_le hd hh hℓ X a b) (tNorm_dlt_le hd hh hℓ X a b))

end

end Obs2
