import Obs2.Est.KObsU
import Obs2.Est.WObs3
import Obs.StepObsLargeAux

/-!
# The `𝒲` step for unreduced inputs in the full norm (crude, all four components)

For unreduced inputs (one-point parts present, all four components local, `w.Sub`) with
`‖V^∅‖ ≤ ḡ`, `‖𝒲^∅‖ ≤ ḡ²`, `‖V^{obs}‖_w ≤ m`, `‖𝒲^{obs}‖_w ≤ ḡm`, `ḡ ≤ m`, `ḡ ≤ 1`:

* **`wpO_fullWU`**: `‖𝒲_{j+1}(B)‖_{w} ≤ C_W(ḡ + m²)` (full norm, `B` a `j`-block). Proof: the
  bulk part by `Step2.BH.Wp_le` (radius `ḡ`, `K = 0`); the observable part by `BHOU.Wp_o` in the
  rescaled weights `w_λ = (λw_a, λw_b, λ²w_{ab})`, `λ = ḡ/m` (`‖V‖_{w_λ} ≤ ḡ`, `‖𝒲‖_{w_λ} ≤ ḡ²`,
  so `‖WpO‖_{w_λ} ≤ c₀ḡ²`), and `λ²‖F‖_w ≤ ‖F‖_{w_λ}` (`oTo_unscale_le`), so `‖WpO‖^{obs}_w ≤ c₀m²`.
  `WpO` does not involve `K`.
* **`Wnext2O_fullWU`**: `‖𝒲_{j+1}(B_+)‖_w = ‖∏_{B ⊆ B_+}(1 + 𝒲_{j+1}(B)) − 1‖_w ≤
  e^{L^d C_W(ḡ + m²)} − 1` (`oT_prod_sub_one_le`).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD PolyAux ENNReal

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

/-- **Undoing the rescaling**: `λ²‖F‖_w ≤ ‖F‖_{w_λ}` for `λ ≤ 1`. -/
theorem oTo_unscale_le (w : Wt) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (j : ℕ) (ℓ : ℝ)
    (F : OE c (Lam d L N)) :
    ENNReal.ofReal (l ^ 2) * oTo w j ℓ F ≤ oTo (Wt.scale (ENNReal.ofReal l) w) j ℓ F := by
  rw [oTo_scale_eq, oTo_split_ab w j ℓ F, mul_add, ENNReal.ofReal_pow hl0]
  refine add_le_add (mul_le_mul_right' ?_ _) le_rfl
  calc ENNReal.ofReal l ^ 2 = ENNReal.ofReal l * ENNReal.ofReal l := pow_two _
    _ ≤ ENNReal.ofReal l * 1 :=
        mul_le_mul_left' (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hl1) _
    _ = ENNReal.ofReal l := mul_one _

/-- The constant of `wpO_fullWU`. -/
def cWU (d L : ℕ) (Cl Clo : ℝ) : ℝ :=
  Step2.cWblk d L Cl + (1 + Clo * (L : ℝ) ^ d) * (8 * Step2.cNear d L * Step2.Q1 d ^ 2 + Step2.Q1 d)

set_option maxHeartbeats 1000000 in
/-- **`‖𝒲_{j+1}(B)‖_w ≤ C_W(ḡ + m²)`** for unreduced inputs (full norm). -/
theorem wpO_fullWU (d : ℕ) (hd : 2 ≤ d) : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ Cw : ℝ, 0 ≤ Cw ∧
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓC C →
    ∀ (c : Obs.Case) (P : ObsPts d L N) (w : Wt), w.Sub →
    ∀ (V W : OFam c d L N),
      (∀ b, CmpInA (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N))
        (V b : SA c (Lam d L N))) →
      (∀ b, CmpInA (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N))
        (W b : SA c (Lam d L N))) →
      InF j (bulkF V) → InF j (bulkF W) →
      (∀ b, ε ((bulkF V b : EvR (Lam d L N)) : Alg d L N) = 0) →
      ∀ g m : ℝ, 0 < g → g ≤ 1 → g ≤ m →
      Fnorm j ℓ (bulkF V) ≤ ENNReal.ofReal g → Fnorm j ℓ (bulkF W) ≤ ENNReal.ofReal (g ^ 2) →
      (∀ b ∈ blockIdx (L := L) (N := N) j, oTo w j ℓ (V b) ≤ ENNReal.ofReal m) →
      (∀ b ∈ blockIdx (L := L) (N := N) j, oTo w j ℓ (W b) ≤ ENNReal.ofReal (g * m)) →
      ∀ b ∈ blockIdx (L := L) (N := N) j,
        oTj d L w (j + 1) ℓ' (WpO P j C V W b : SA c (Lam d L N)) ≤
          ENNReal.ofReal (Cw * (g + m ^ 2)) := by
  classical
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Cl, hCl0, hloc⟩ := exists_Loc2sXY_bound d hd1
  obtain ⟨Clo, hClo0, hlocO⟩ := exists_LocO2_full_bound d (by omega)
  obtain ⟨cN, hcN⟩ := card_small_containing d
  refine ⟨max (2 ^ (d + 3) + 8 * d + 1) ⌈pauliL0 d⌉₊, fun L _ hL => ?_⟩
  have hL8 : 2 ^ (d + 3) + 8 * d < L :=
    lt_of_lt_of_le (Nat.lt_succ_self _) (le_trans (le_max_left _ _) hL)
  have hLp : pauliL0 d ≤ L := (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hL)
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hQ := one_le_Q1 hd1
  have hn : 0 ≤ cNear d L := Nat.cast_nonneg _
  have hcw : 0 ≤ cWblk d L Cl := by
    have := Nat.cast_nonneg (α := ℝ) ((L + 2 ^ (d + 3) + 7) ^ d)
    simp only [cWblk, cSblk, cNear]; positivity
  set s₀ : ℝ := 8 * cNear d L * Q1 d ^ 2 + Q1 d with hs₀
  have hs₀0 : 0 ≤ s₀ := by positivity
  set c₀ : ℝ := (1 + Clo * (L : ℝ) ^ d) * s₀ with hc₀
  have hc₀0 : 0 ≤ c₀ := by positivity
  refine ⟨cWU d L Cl Clo, by unfold cWU; positivity, ?_⟩
  intro N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC c P w hw V W hVl hWl hV hW hV0 g m hg hg1 hgm
    hVg hWg hVo hWo b hb
  have hm : 0 < m := lt_of_lt_of_le hg hgm
  have hcount : ∀ b ∈ blockIdx (d := d) (L := L) (N := N) j,
      (((smallSets (d := d) (L := L) (N := N) j).filter
        (fun X => blockSet j b ⊆ X)).card : ℝ) ≤ cN + 1 := fun b hb => by
    have h1 : ((smallSets (d := d) (L := L) (N := N) j).filter
        (fun X => blockSet j b ⊆ X)).card ≤ cN := by convert hcN L N j b hb
    have h2 := Nat.cast_le (α := ℝ) |>.2 h1
    linarith
  have hcS1 : (1 : ℝ) ≤ cN + 1 := by linarith [Nat.cast_nonneg (α := ℝ) cN]
  -- the bulk part
  have hT0 : Tj d (L : ℝ) j ℓ (0 : Alg d L N) = 0 := Tj_zero _ _ _
  have hK0 : InK2 j (0 : Act d L N) :=
    { loc := fun _ _ => zero_mem _, sym := fun _ _ => (isSym_iff_mem_SymS _).2 (zero_mem _) }
  have hg2 : g ^ 2 ≤ g := by rw [pow_two]; exact mul_le_of_le_one_left hg.le hg1
  have HB : Step2.BH j ℓ ℓ' ℓC C (bulkF V) (bulkF W) (0 : Act d L N) 1 g Cl (cN + 1) :=
    { hd := hd1, hLp := hLp, hL8 := hL8, hjN := hjN, hℓ := hℓ, hℓ' := hℓ', hℓC := hℓC,
      hsum := hsum, hC := hC, hV := hV, hW := hW, hV0 := hV0, hK := hK0, hA := le_rfl,
      hr := hg.le, hr1 := hg1
      hVr := fun b hb => (Tj_le_Fnorm _ hb).trans hVg
      hWr := fun b hb => ((Tj_le_Fnorm _ hb).trans hWg).trans (ENNReal.ofReal_le_ofReal hg2)
      hKr := by rw [Knorm_zero]; exact zero_le
      hCl := hCl0
      hloc := fun k hk ℓ₀ hℓ₀ X Y hX hYX F hF => hloc L hL8 N k hk X Y hX hYX F hF ℓ₀ hℓ₀
      hcS := hcS1, hcount := hcount }
  have hbulk : Tj d (L : ℝ) (j + 1) ℓ' (WpO P j C V W b : SA c (Lam d L N)).e ≤
      ENNReal.ofReal (cWblk d L Cl * g) := by
    show Tj d (L : ℝ) (j + 1) ℓ' ((bulk (WpO P j C V W b) : EvR (Lam d L N)) : Alg d L N) ≤ _
    rw [bulk_WpO]; exact HB.Wp_le hb
  -- the observable part in the rescaled weights
  set l := g / m with hl
  have hl0 : 0 < l := div_pos hg hm
  have hl1 : l ≤ 1 := by rw [hl, div_le_one hm]; exact hgm
  have hlm : l * m = g := by rw [hl]; field_simp
  have hl1' : ENNReal.ofReal l ≤ 1 := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hl1
  set wl := Wt.scale (ENNReal.ofReal l) w with hwl
  have hwl0 : wl.Sub := Wt.scale_sub hw _
  have HO : BHOU P j ℓ ℓ' ℓC C V W (0 : OAct c d L N) wl (2 * g) (2 * g) (g ^ 2) 0 Clo (cN + 1) :=
    { hd := hd1, hLp := hLp, hL8 := hL8, hjN := hjN, hℓ := hℓ, hℓ' := hℓ', hℓC := hℓC,
      hsum := hsum, hC := hC, hw := hwl0, hVl := hVl, hWl := hWl
      hKl := fun X _ => CmpInA.of_eq_zero rfl
      hr := by linarith, hmV := by linarith, hmW := sq_nonneg _, hk := le_rfl
      hVr := fun b hb => ((Tj_le_Fnorm _ hb).trans hVg).trans
        (ENNReal.ofReal_le_ofReal (by linarith))
      hVm := fun b hb => by
        refine (oTo_scale_le w hl1' j ℓ _).trans ?_
        rw [show 2 * g / 2 = l * m by rw [hlm]; ring, ENNReal.ofReal_mul hl0.le]
        exact mul_le_mul_left' (hVo b hb) _
      hmVr := le_rfl
      hWm := fun b hb => by
        refine (oTo_scale_le w hl1' j ℓ _).trans ?_
        rw [show g ^ 2 = l * (g * m) by rw [← hlm]; ring, ENNReal.ofReal_mul hl0.le]
        exact mul_le_mul_left' (hWo b hb) _
      hKk := fun X _ => by
        show oTo wl j ℓ (0 : OE c (Lam d L N)) ≤ _
        rw [oTo_zero']; exact zero_le
      hCl := hClo0
      hloc := fun k' hk ℓ₀ hℓ₀ X Y hX hYX F hF =>
        hlocO L hL8 N c P wl k' hk ℓ₀ hℓ₀ X Y hX hYX F hF
      hlocl := bho_hloclAB hd1 P j, hcS := hcS1, hcount := hcount }
  have hWp := HO.Wp_o hb
  have esO : sO d L (2 * g) (2 * g) (g ^ 2) + Clo * ((L : ℝ) ^ d * sO d L (2 * g) (2 * g) (g ^ 2)) =
      ENNReal.toReal (ENNReal.ofReal (l ^ 2)) * (c₀ * m ^ 2) := by
    rw [ENNReal.toReal_ofReal (sq_nonneg _), hc₀, hs₀]
    unfold sO
    have : l ^ 2 * m ^ 2 = g ^ 2 := by rw [← mul_pow, hlm]
    linear_combination (-(1 + Clo * (L : ℝ) ^ d) * (8 * cNear d L * Q1 d ^ 2 + Q1 d)) * this
  have hobs : oTo w (j + 1) ℓ' (WpO P j C V W b) ≤ ENNReal.ofReal (c₀ * m ^ 2) := by
    have h1 := (oTo_unscale_le w hl0.le hl1 (j + 1) ℓ' (WpO P j C V W b)).trans hWp
    rw [esO, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal ENNReal.ofReal_ne_top]
      at h1
    exact (ENNReal.mul_le_mul_iff_right (by simp [hl0.ne']) ENNReal.ofReal_ne_top).1 h1
  rw [oTj_eq_bulk_add]
  refine (le_ofReal_add (by positivity) (by positivity) hbulk hobs).trans
    (ENNReal.ofReal_le_ofReal ?_)
  unfold cWU
  have hm2 : 0 ≤ m ^ 2 := sq_nonneg _
  have e1 : cWblk d L Cl * g ≤ cWblk d L Cl * (g + m ^ 2) := by nlinarith
  have e2 : c₀ * m ^ 2 ≤ c₀ * (g + m ^ 2) := by nlinarith
  rw [← hs₀, ← hc₀]
  nlinarith

/-- **`‖𝒲_{j+1}(B_+)‖_w ≤ e^{L^d C_W(ḡ + m²)} − 1`** from per-block bounds. -/
theorem Wnext2O_full_le {P : ObsPts d L N} {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℂ}
    {V W : OFam c d L N} {w : Wt} (hw : w.Sub) {ℓ' : ℝ} (hℓ' : 0 < ℓ') {t : ℝ} (ht : 0 ≤ t)
    (hWp : ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTj d L w (j + 1) ℓ' (WpO P j C V W b : SA c (Lam d L N)) ≤ ENNReal.ofReal t)
    (c' : Fin d → ℕ) :
    oTj d L w (j + 1) ℓ' (Wnext2O P j C V W c' : SA c (Lam d L N)) ≤
      ENNReal.ofReal (Real.exp ((L : ℝ) ^ d * t) - 1) := by
  classical
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hh' : (0 : ℝ) < (L : ℝ) ^ (j + 1) := pow_pos hL0 _
  set s := blocks j (blockSet (L := L) (N := N) (j + 1) c')
  have hns : (s.card : ℝ) ≤ (L : ℝ) ^ d := by
    have := nb_blockSet_succ_le (L := L) (N := N) j c'
    unfold nb at this; exact_mod_cast this
  have h := oT_prod_sub_one_le (E := Dir d) (p := pPhi d) hh' hℓ' hw s
    (fun b => 1 + WpO P j C V W b) (fun _ => t) (fun _ _ => ht) (fun b hb => by
      rw [add_sub_cancel_left]
      refine (hWp b (mem_blockIdx_of_mem_blocks hb)).trans (ENNReal.ofReal_le_ofReal ?_)
      linarith [Real.add_one_le_exp t])
  rw [Wnext2O]
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [sum_const, nsmul_eq_mul]
  have : (s.card : ℝ) * t ≤ (L : ℝ) ^ d * t := mul_le_mul_of_nonneg_right hns ht
  linarith [Real.exp_le_exp.2 this]

end

end Obs2
