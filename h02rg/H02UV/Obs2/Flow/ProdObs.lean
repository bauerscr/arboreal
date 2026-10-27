import Obs2.Est.WObs3
import Obs2.Loc.LocFlow

/-!
# The product part of `𝒲_{j+1}(B_+)` in one step

`Prod_{j+1}(B_+) = 𝒲_{j+1}(B_+) − ∑_{B ⊆ B_+} 𝒲'(B) = ∏_{B ⊆ B_+}(1 + 𝒲'(B)) − 1 − ∑ 𝒲'(B)`:

* **`prodO_obs_le`**: `‖Prod^{obs}‖_{T_{j+1}(ℓ')} ≤ L^d o ((1 + e)^{L^d} − 1)` with the block
  bounds `o = oWc` (`BHO.Wp_o`) and `e` of the bulk part (the bound of `Wnext2O_obs_le`, isolated);
* `prodO_mem`: `Prod ∈ 𝒩^{obs}(𝒩_{j+1}(B_+))` (from the locality of the `𝒲'(B)`).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD ENNReal

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

/-- The product part of the step `j`, `(j+1)`-block `c'`. -/
def prodO (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V W : OFam c d L N)
    (c' : Fin d → ℕ) : OE c (Lam d L N) :=
  Wnext2O P j C V W c' - ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'), WpO P j C V W b

theorem prodO_eq (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : OFam c d L N) (c' : Fin d → ℕ) :
    prodO P j C V W c' =
      ∏ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'), (1 + WpO P j C V W b) - 1 -
        ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'), WpO P j C V W b := rfl

/-- **The product part, observable norm.** -/
theorem prodO_obs_le {P : ObsPts d L N} {j : ℕ} {ℓ ℓ' ℓC : ℝ} {C : Matrix (Lam d L N) (Lam d L N) ℂ}
    {V W : OFam c d L N} {Kc : OAct c d L N} {w : Wt} {r mV mW k Cl cS e : ℝ}
    (H : BHO P j ℓ ℓ' ℓC C V W Kc w r mV mW k Cl cS) (he : 0 ≤ e)
    (hWe : ∀ b ∈ blockIdx (L := L) (N := N) j,
      Tj d (L : ℝ) (j + 1) ℓ' (WpO P j C V W b : SA c (Lam d L N)).e ≤ ENNReal.ofReal e)
    {c' : Fin d → ℕ} :
    oTo w (j + 1) ℓ' (prodO P j C V W c') ≤
      ENNReal.ofReal ((L : ℝ) ^ d * oWc d L r mV mW Cl * ((1 + e) ^ (L ^ d) - 1)) := by
  have hL0 := H.hL0
  have hh' : (0 : ℝ) < (L : ℝ) ^ (j + 1) := pow_pos hL0 _
  have hnL : (blocks j (blockSet (L := L) (N := N) (j + 1) c')).card ≤ L ^ d := by
    have := nb_blockSet_succ_le (L := L) (N := N) j c'
    unfold nb at this; exact this
  have hns : ((blocks j (blockSet (L := L) (N := N) (j + 1) c')).card : ℝ) ≤ (L : ℝ) ^ d := by
    exact_mod_cast hnL
  have hsI : blocks j (blockSet (L := L) (N := N) (j + 1) c') ⊆ blockIdx (L := L) (N := N) j :=
    fun b hb => mem_blockIdx_of_mem_blocks hb
  have hoW : 0 ≤ oWc d L r mV mW Cl := by
    unfold oWc; have := H.hsO; have := H.hCl; positivity
  have hprod := (oTo_prod_sub_le H.hw0 hh' H.hℓ' (blocks j (blockSet (L := L) (N := N) (j + 1) c'))
    (WpO P j C V W) he hoW (fun b hb => hWe b (hsI hb)) (fun b hb => H.Wp_o (hsI hb))).2
  rw [prodO_eq]
  refine hprod.trans (ENNReal.ofReal_le_ofReal ?_)
  set s := blocks j (blockSet (L := L) (N := N) (j + 1) c')
  have h1 : (1 + e) ^ s.card ≤ (1 + e) ^ (L ^ d) := pow_le_pow_right₀ (by linarith) hnL
  have h2 : (0 : ℝ) ≤ (1 + e) ^ s.card - 1 := by
    have := one_le_pow₀ (M₀ := ℝ) (n := s.card) (by linarith : (1 : ℝ) ≤ 1 + e)
    linarith
  have h3 : (s.card : ℝ) * oWc d L r mV mW Cl ≤ (L : ℝ) ^ d * oWc d L r mV mW Cl :=
    mul_le_mul_of_nonneg_right hns hoW
  calc (s.card : ℝ) * oWc d L r mV mW Cl * ((1 + e) ^ s.card - 1)
      ≤ (L : ℝ) ^ d * oWc d L r mV mW Cl * ((1 + e) ^ s.card - 1) :=
        mul_le_mul_of_nonneg_right h3 h2
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- **Locality of the product part**: `Prod ∈ 𝒩^{obs}(𝒩_{j+1}(B_+))`. -/
theorem prodO_mem {P : ObsPts d L N} {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℂ}
    {V W : OFam c d L N} {K : OAct c d L N} (H : OLocS P j V W K) (hd : 1 ≤ d)
    (hL : 2 ^ (d + 3) ≤ L) (hjN : j + 1 < N) (hC : CovRange j C) {c' : Fin d → ℕ} :
    prodO P j C V W c' ∈ osub P (nbhd (j + 1) (blockSet (L := L) (N := N) (j + 1) c')) := by
  have hW : ∀ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
      WpO P j C V W b ∈ osub P (nbhd (j + 1) (blockSet (L := L) (N := N) (j + 1) c')) := by
    intro b hb
    have h := H.Wp_mem hd hL hjN hC (mem_blockIdx_of_mem_blocks hb)
    obtain ⟨hb1, hb2⟩ := mem_blocks_blockSet_succ.1 hb
    rwa [Step2.Bp, clo_blockSet hb1, hb2] at h
  rw [prodO_eq]
  refine sub_mem (sub_mem (prod_mem fun b hb => add_mem (one_mem _) (hW b hb)) (one_mem _))
    (sum_mem fun b hb => hW b hb)

end

end Obs2
