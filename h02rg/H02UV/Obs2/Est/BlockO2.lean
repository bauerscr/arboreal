import Obs2.Est.BlockO1
import Obs2.Est.EstBlock
import Obs2.Map.ExactStep

/-!
# Block bounds for the map with sources in the full norm

The full norm with single-source weights is `‖F‖ = ‖F_∅‖ + ‖π_obs F‖` (`oTj_eq_bulk_add`). The
bulk components of the map with sources are the bulk map (`bulk_VpO`, `bulk_WpO`, `upB_eq`,
`bulk_LocO2`, …), bounded by `Step2.BH`; the observable components are bounded by `Obs2.BHO`.
`BHF` bundles both, at a common radius `r` (bulk sizes `≤ r`, observable sizes `≤ r`), together
with the locality and the weighted bound of the observable part of `K` on all connected
polymers. Then, in the full norm:

* `VpO_full`, `WpO_full`, `upO_full`, `upB_le`: the block coordinates at scale `j + 1`;
* `IbO_sub_one_full`: `‖I_j(B) - 1‖_{T_j(ℓ)} ≤ e^{4r} - 1`, and `IbO_sub_one_cmp` (locality);
* `IpO_sub_one_full`: `‖I_{j+1}(B) - 1‖_{T_{j+1}(ℓ')} ≤ e^{t_I} - 1`;
* `gdIO_full`: `‖δI(B)‖_{T_{j+1}(ℓ' ⊔ ℓ_C)} ≤ Q₁(e^{4r} - 1) + e^{t_I} - 1`;
* `thetaKO_full`: `‖θ K(X)‖ ≤ 2r A^{2^d} (Q₁/A)^{|𝓑_j(X)|}` for connected `X`;
* `thetaJO_full`: `‖θ J(B, X)‖ ≤ Q₁ q² c_S (C_l + C_l^{obs}) r`;
* `expU_full`, `IpO_full`: `‖e^{±u_{j+1}(B)}‖`, `‖I_{j+1}(B)‖` (for the prefactors).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step FRD ENNReal

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

/-! ### Products of factors close to `1` -/

section Exp

variable {X : Type*} [DecidableEq X] [Fintype X] {E : Type*} [Fintype E] [DecidableEq E]
  [AddAction (E → ℕ) X] {p : ℕ} {h ℓ : ℝ} {w : Wt}

theorem oT_mul_sub_one_le2 (hh : 0 < h) (hℓ : 0 < ℓ) (hw : w.Sub) (F G : OE c X) {t₁ t₂ : ℝ}
    (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂)
    (hF : oT E p h ℓ w ((F - 1 : OE c X) : SA c X) ≤ ENNReal.ofReal (Real.exp t₁ - 1))
    (hG : oT E p h ℓ w ((G - 1 : OE c X) : SA c X) ≤ ENNReal.ofReal (Real.exp t₂ - 1)) :
    oT E p h ℓ w ((F * G - 1 : OE c X) : SA c X) ≤ ENNReal.ofReal (Real.exp (t₁ + t₂) - 1) := by
  have e : F * G - 1 = F * (G - 1) + (F - 1) := by ring
  have hF1 : oT E p h ℓ w (F : SA c X) ≤ ENNReal.ofReal (Real.exp t₁) := by
    have e1 : F = (F - 1) + 1 := by ring
    rw [e1]
    refine (oT_add_le _ _).trans ((add_le_add hF (oT_one_le hh hℓ)).trans (le_of_eq ?_))
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by linarith [Real.add_one_le_exp t₁])
      zero_le_one]
    congr 1; ring
  rw [e]
  refine (oT_add_le _ _).trans ((add_le_add ((oT_mul_le hh hℓ hw _ _).trans
    (mul_le_mul' hF1 hG)) hF).trans (le_of_eq ?_))
  have h1 : 0 ≤ Real.exp t₂ - 1 := by linarith [Real.add_one_le_exp t₂]
  have h2 : 0 ≤ Real.exp t₁ - 1 := by linarith [Real.add_one_le_exp t₁]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_add (by positivity) h2]
  congr 1
  rw [Real.exp_add]; ring

/-- `‖e^z e^F - 1‖ ≤ e^{|z| + r} - 1` if `‖F‖ ≤ r`. -/
theorem oT_expU_sub_one_le (hh : 0 < h) (hℓ : 0 < ℓ) (hw : w.Sub) (z : ℂ) {F : OE c X}
    (hF : ε ((F : SA c X).e) = 0) {r : ℝ} (hr : 0 ≤ r)
    (hFr : oT E p h ℓ w (F : SA c X) ≤ ENNReal.ofReal r) :
    oT E p h ℓ w ((expU z F - 1 : OE c X) : SA c X) ≤
      ENNReal.ofReal (Real.exp (‖z‖ + r) - 1) := by
  have e : expU z F - 1 = Complex.exp z • (oexp F - 1) + (Complex.exp z - 1) • (1 : OE c X) := by
    rw [expU, smul_sub, sub_smul, one_smul]; abel
  rw [e]
  have h1 := oT_oexp_sub_one_le (E := E) (p := p) hh hℓ hw hF hr hFr
  have hz1 : ‖Complex.exp z‖ ≤ Real.exp ‖z‖ := Complex.norm_exp_le_exp_norm z
  have hz2 : ‖Complex.exp z - 1‖ ≤ Real.exp ‖z‖ - 1 := by
    simpa using Complex.norm_exp_sub_sum_le_exp_norm_sub_sum z 1
  have hr1 : 0 ≤ Real.exp r - 1 := by linarith [Real.add_one_le_exp r]
  refine (oT_add_le _ _).trans ?_
  rw [show (((Complex.exp z • (oexp F - 1) : OE c X)) : SA c X) =
      Complex.exp z • (((oexp F - 1 : OE c X)) : SA c X) from rfl,
    show ((((Complex.exp z - 1) • (1 : OE c X) : OE c X)) : SA c X) =
      (Complex.exp z - 1) • ((1 : OE c X) : SA c X) from rfl, oT_smul, oT_smul]
  calc ENNReal.ofReal ‖Complex.exp z‖ * oT E p h ℓ w (((oexp F - 1 : OE c X)) : SA c X) +
        ENNReal.ofReal ‖Complex.exp z - 1‖ * oT E p h ℓ w ((1 : OE c X) : SA c X)
      ≤ ENNReal.ofReal (Real.exp ‖z‖) * ENNReal.ofReal (Real.exp r - 1) +
        ENNReal.ofReal (Real.exp ‖z‖ - 1) * 1 := by
        gcongr
        exact oT_one_le hh hℓ
    _ = ENNReal.ofReal (Real.exp (‖z‖ + r) - 1) := by
        rw [mul_one, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
          ← ENNReal.ofReal_add (by positivity)
            (by linarith [Real.add_one_le_exp ‖z‖, norm_nonneg z])]
        congr 1; rw [Real.exp_add]; ring

/-- `‖F‖ ≤ e^t` from `‖F - 1‖ ≤ e^t - 1`. -/
theorem oT_le_exp_of_sub_one (hh : 0 < h) (hℓ : 0 < ℓ) {F : OE c X} {t : ℝ} (ht : 0 ≤ t)
    (hF : oT E p h ℓ w ((F - 1 : OE c X) : SA c X) ≤ ENNReal.ofReal (Real.exp t - 1)) :
    oT E p h ℓ w (F : SA c X) ≤ ENNReal.ofReal (Real.exp t) := by
  have e1 : F = (F - 1) + 1 := by ring
  rw [e1]
  refine (oT_add_le _ _).trans ((add_le_add hF (oT_one_le hh hℓ)).trans (le_of_eq ?_))
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by linarith [Real.add_one_le_exp t])
    zero_le_one]
  congr 1; ring

end Exp

/-! ### The hypotheses -/

/-- The full-norm block hypotheses at scale `j` (single-source weights, common radius `r`). -/
structure BHF (P : ObsPts d L N) (j : ℕ) (ℓ ℓ' ℓC : ℝ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : OFam c d L N) (K : OAct c d L N) (w : Wt) (A r Cl cS Clo : ℝ) : Prop where
  hB : Step2.BH j ℓ ℓ' ℓC C (bulkF V) (bulkF W) (bulkF K) A r Cl cS
  hO : BHO P j ℓ ℓ' ℓC C V W K w r r r r Clo cS
  hKl : ∀ X, IsConn j X → CmpIn (nbhd j X : Set (Lam d L N)) (K X : SA c (Lam d L N))
  hKo : ∀ X, IsConn j X →
    ENNReal.ofReal (A ^ (nb j X - 2 ^ d)) * oTo w j ℓ (K X) ≤ ENNReal.ofReal r

/-- The observable constant `u^{obs}` of `EstBlock` at radius `r`. -/
abbrev uoB (d L : ℕ) (r Clo cS : ℝ) : ℝ := Obs2.BHO.uO d L r r r r Clo cS

/-- The observable constant of `𝒲^{obs}`. -/
abbrev woB (d L : ℕ) (r Clo : ℝ) : ℝ :=
  Obs2.sO d L r r r + Clo * ((L : ℝ) ^ d * Obs2.sO d L r r r)

/-- The exponent of `‖I_{j+1}(B) - 1‖`. -/
abbrev tIB (d L : ℕ) (r Cl Clo cS : ℝ) : ℝ := Step2.cUblk d L Cl cS * r + uoB d L r Clo cS +
  (2 * (Step2.cUblk d L Cl cS * r) + 2 * uoB d L r Clo cS) + (Step2.cWblk d L Cl * r + woB d L r Clo)

theorem oe_one_add_sub_one (F : OE c (Lam d L N)) : (1 + F) - 1 = F := by ring

namespace BHF

variable {P : ObsPts d L N} {j : ℕ} {ℓ ℓ' ℓC : ℝ} {C : Matrix (Lam d L N) (Lam d L N) ℂ}
  {V W : OFam c d L N} {K : OAct c d L N} {w : Wt} {A r Cl cS Clo : ℝ}
  (H : BHF P j ℓ ℓ' ℓC C V W K w A r Cl cS Clo)
include H

theorem hh' : (0 : ℝ) < (L : ℝ) ^ (j + 1) := H.hB.hh'

theorem hh : (0 : ℝ) < (L : ℝ) ^ j := pow_pos H.hB.hL0 _

theorem hw0 : w.ab = 0 := H.hO.hw0

theorem hw : w.Sub := H.hO.hw

theorem hr : 0 ≤ r := H.hB.hr

theorem huo : 0 ≤ (uoB d L r Clo cS) := H.hO.huO

theorem hwo : 0 ≤ (woB d L r Clo) := add_nonneg H.hO.hsO
  (mul_nonneg H.hO.hCl (mul_nonneg (pow_nonneg H.hB.hL0.le d) H.hO.hsO))

theorem full_le {k : ℕ} {ℓ₀ : ℝ} {F : OE c (Lam d L N)} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h1 : Tj d (L : ℝ) k ℓ₀ (F : SA c (Lam d L N)).e ≤ ENNReal.ofReal a)
    (h2 : oTo w k ℓ₀ F ≤ ENNReal.ofReal b) :
    oTj d L w k ℓ₀ (F : SA c (Lam d L N)) ≤ ENNReal.ofReal (a + b) := by
  rw [oTj_eq_bulk_add]; exact le_ofReal_add ha hb h1 h2

/-! ### The inputs -/

theorem V_full {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTj d L w j ℓ (V b : SA c (Lam d L N)) ≤ ENNReal.ofReal (2 * r) := by
  have := H.hr
  refine (H.full_le this this ?_ (H.hO.hVm b hb)).trans (le_of_eq (by rw [two_mul]))
  exact H.hB.hVr b hb

theorem W_full {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTj d L w j ℓ (W b : SA c (Lam d L N)) ≤ ENNReal.ofReal (2 * r) := by
  have := H.hr
  refine (H.full_le this this ?_ (H.hO.hWm b hb)).trans (le_of_eq (by rw [two_mul]))
  exact H.hB.hWr b hb

/-! ### The block coordinates at scale `j + 1` -/

theorem upB_le {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    ‖upB P j C V W K b‖ ≤ Step2.cUblk d L Cl cS * r := by
  rw [upB_eq]; exact H.hB.up_le hb

theorem upO_full {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTj d L w (j + 1) ℓ' (upO P j C V W K b : SA c (Lam d L N)) ≤ ENNReal.ofReal (uoB d L r Clo cS) := by
  rw [oTj_eq_bulk_add]
  have e0 : (upO P j C V W K b : SA c (Lam d L N)).e = 0 := by
    show ((bulk (upO P j C V W K b) : EvR (Lam d L N)) : Alg d L N) = 0
    rw [bulk_upO]; rfl
  rw [e0, show Tj d (L : ℝ) (j + 1) ℓ' (0 : Alg d L N) = 0 from tNorm_zero', zero_add]
  rw [upO, oTo_πobs]
  exact (oTo_epsO_le w H.hh' H.hO.hℓ' _).trans (H.hO.uVp_o hb)

theorem VpO_full {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTj d L w (j + 1) ℓ' (VpO P j C V W K b : SA c (Lam d L N)) ≤
      ENNReal.ofReal (2 * (Step2.cUblk d L Cl cS * r) + 2 * uoB d L r Clo cS) := by
  have h1 := mul_nonneg H.hB.hcU H.hr
  refine H.full_le (by linarith) (by linarith [H.huo]) ?_ (H.hO.Vp_o hb)
  show Tj d (L : ℝ) (j + 1) ℓ' ((bulk (VpO P j C V W K b) : EvR (Lam d L N)) : Alg d L N) ≤ _
  rw [bulk_VpO]; exact H.hB.Vp_le hb

theorem WpO_full {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTj d L w (j + 1) ℓ' (WpO P j C V W b : SA c (Lam d L N)) ≤
      ENNReal.ofReal (Step2.cWblk d L Cl * r + woB d L r Clo) := by
  have h1 := mul_nonneg H.hB.hcW H.hr
  refine H.full_le h1 H.hwo ?_ (H.hO.Wp_o hb)
  show Tj d (L : ℝ) (j + 1) ℓ' ((bulk (WpO P j C V W b) : EvR (Lam d L N)) : Alg d L N) ≤ _
  rw [bulk_WpO]; exact H.hB.Wp_le hb

/-! ### The block factors -/

theorem eps_neg_V (b : Fin d → ℕ) : ε (((-V b : OE c (Lam d L N)) : SA c (Lam d L N)).e) = 0 := by
  show ε ((bulk (-V b) : EvR (Lam d L N)) : Alg d L N) = 0
  rw [map_neg, NegMemClass.coe_neg, map_neg]
  have := H.hB.hV0 b
  simp only [bulkF_apply] at this
  rw [this, neg_zero]

theorem eps_neg_VpO (b : Fin d → ℕ) :
    ε (((-VpO P j C V W K b : OE c (Lam d L N)) : SA c (Lam d L N)).e) = 0 := by
  show ε ((bulk (-VpO P j C V W K b) : EvR (Lam d L N)) : Alg d L N) = 0
  rw [map_neg, NegMemClass.coe_neg, map_neg, bulk_VpO, Step2.ε_Vp, neg_zero]

theorem eps_neg_upO (b : Fin d → ℕ) :
    ε (((-upO P j C V W K b : OE c (Lam d L N)) : SA c (Lam d L N)).e) = 0 := by
  show ε ((bulk (-upO P j C V W K b) : EvR (Lam d L N)) : Alg d L N) = 0
  rw [map_neg, bulk_upO, neg_zero]; simp

theorem IbO_sub_one_full {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTj d L w j ℓ ((IbO V W b - 1 : OE c (Lam d L N)) : SA c (Lam d L N)) ≤
      ENNReal.ofReal (Real.exp (2 * r + 2 * r) - 1) := by
  have hr := H.hr
  have hVr : oTj d L w j ℓ ((-V b : OE c (Lam d L N)) : SA c (Lam d L N)) ≤
      ENNReal.ofReal (2 * r) :=
    (le_of_eq (oT_neg (E := Dir d) (p := pPhi d) (h := (L : ℝ) ^ j) (ℓ := ℓ) (w := w)
      (V b : SA c (Lam d L N)))).trans (H.V_full hb)
  have h1 := oT_oexp_sub_one_le (E := Dir d) (p := pPhi d) H.hh H.hB.hℓ H.hw (H.eps_neg_V b)
    (by linarith) hVr
  have h2 : oTj d L w j ℓ (((1 + W b) - 1 : OE c (Lam d L N)) : SA c (Lam d L N)) ≤
      ENNReal.ofReal (Real.exp (2 * r) - 1) := by
    rw [oe_one_add_sub_one]
    refine (H.W_full hb).trans (ENNReal.ofReal_le_ofReal ?_)
    linarith [Real.add_one_le_exp (2 * r)]
  exact oT_mul_sub_one_le2 H.hh H.hB.hℓ H.hw _ _ (by linarith) (by linarith) h1 h2

theorem htI : 0 ≤ (tIB d L r Cl Clo cS) := by
  have := mul_nonneg H.hB.hcU H.hr
  have := mul_nonneg H.hB.hcW H.hr
  have := H.huo; have := H.hwo
  simp only [tIB]; linarith

theorem expU_neg_sub_one_full {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTj d L w (j + 1) ℓ'
      ((expU (-upB P j C V W K b) (-upO P j C V W K b) - 1 : OE c (Lam d L N)) :
        SA c (Lam d L N)) ≤
      ENNReal.ofReal (Real.exp (Step2.cUblk d L Cl cS * r + uoB d L r Clo cS) - 1) := by
  have hu : oTj d L w (j + 1) ℓ' ((-upO P j C V W K b : OE c (Lam d L N)) : SA c (Lam d L N)) ≤
      ENNReal.ofReal (uoB d L r Clo cS) :=
    (le_of_eq (oT_neg (E := Dir d) (p := pPhi d) (h := (L : ℝ) ^ (j + 1)) (ℓ := ℓ') (w := w)
      (upO P j C V W K b : SA c (Lam d L N)))).trans (H.upO_full hb)
  refine (oT_expU_sub_one_le H.hh' H.hO.hℓ' H.hw _ (H.eps_neg_upO b) H.huo hu).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have := Real.exp_le_exp.2 (add_le_add (show ‖-upB P j C V W K b‖ ≤
    Step2.cUblk d L Cl cS * r by rw [norm_neg]; exact H.upB_le hb) (le_refl (uoB d L r Clo cS)))
  linarith

theorem GpO_sub_one_full {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTj d L w (j + 1) ℓ' ((GpO P j C V W K b - 1 : OE c (Lam d L N)) : SA c (Lam d L N)) ≤
      ENNReal.ofReal (Real.exp ((2 * (Step2.cUblk d L Cl cS * r) + 2 * uoB d L r Clo cS) +
        (Step2.cWblk d L Cl * r + woB d L r Clo)) - 1) := by
  have h0 := mul_nonneg H.hB.hcU H.hr
  have h0' := mul_nonneg H.hB.hcW H.hr
  have := H.huo; have := H.hwo
  have hV : oTj d L w (j + 1) ℓ' ((-VpO P j C V W K b : OE c (Lam d L N)) : SA c (Lam d L N)) ≤
      ENNReal.ofReal (2 * (Step2.cUblk d L Cl cS * r) + 2 * uoB d L r Clo cS) :=
    (le_of_eq (oT_neg (E := Dir d) (p := pPhi d) (h := (L : ℝ) ^ (j + 1)) (ℓ := ℓ') (w := w)
      (VpO P j C V W K b : SA c (Lam d L N)))).trans (H.VpO_full hb)
  have h1 := oT_oexp_sub_one_le (E := Dir d) (p := pPhi d) H.hh' H.hO.hℓ' H.hw (H.eps_neg_VpO b)
    (by linarith) hV
  have h2 : oTj d L w (j + 1) ℓ'
      (((1 + WpO P j C V W b) - 1 : OE c (Lam d L N)) : SA c (Lam d L N)) ≤
      ENNReal.ofReal (Real.exp (Step2.cWblk d L Cl * r + woB d L r Clo) - 1) := by
    rw [oe_one_add_sub_one]
    refine (H.WpO_full hb).trans (ENNReal.ofReal_le_ofReal ?_)
    linarith [Real.add_one_le_exp (Step2.cWblk d L Cl * r + woB d L r Clo)]
  exact oT_mul_sub_one_le2 H.hh' H.hO.hℓ' H.hw _ _ (by linarith) (by linarith) h1 h2

theorem IpO_sub_one_full {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTj d L w (j + 1) ℓ' ((IpO P j C V W K b - 1 : OE c (Lam d L N)) : SA c (Lam d L N)) ≤
      ENNReal.ofReal (Real.exp (tIB d L r Cl Clo cS) - 1) := by
  have h0 := mul_nonneg H.hB.hcU H.hr
  have h0' := mul_nonneg H.hB.hcW H.hr
  have := H.huo; have := H.hwo
  have := oT_mul_sub_one_le2 H.hh' H.hO.hℓ' H.hw _ _ (by linarith) (by linarith)
    (H.expU_neg_sub_one_full hb) (H.GpO_sub_one_full hb)
  rw [IpO]
  refine this.trans (le_of_eq ?_)
  congr 3
  simp only [tIB]; ring

theorem IpO_full {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTj d L w (j + 1) ℓ' (IpO P j C V W K b : SA c (Lam d L N)) ≤
      ENNReal.ofReal (Real.exp (tIB d L r Cl Clo cS)) :=
  oT_le_exp_of_sub_one H.hh' H.hO.hℓ' H.htI (H.IpO_sub_one_full hb)

theorem expU_full {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTj d L w (j + 1) ℓ'
      (expU (upB P j C V W K b) (upO P j C V W K b) : SA c (Lam d L N)) ≤
      ENNReal.ofReal (Real.exp (Step2.cUblk d L Cl cS * r + uoB d L r Clo cS)) := by
  have h0 := mul_nonneg H.hB.hcU H.hr
  have := H.huo
  have he : ε (((upO P j C V W K b : OE c (Lam d L N)) : SA c (Lam d L N)).e) = 0 := by
    show ε ((bulk (upO P j C V W K b) : EvR (Lam d L N)) : Alg d L N) = 0
    rw [bulk_upO]; simp
  refine oT_le_exp_of_sub_one H.hh' H.hO.hℓ' (by linarith) ?_
  refine (oT_expU_sub_one_le H.hh' H.hO.hℓ' H.hw _ he H.huo (H.upO_full hb)).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have := Real.exp_le_exp.2 (add_le_add (H.upB_le hb) (le_refl (uoB d L r Clo cS)))
  linarith

/-! ### Locality of the block factors -/

theorem IbO_sub_one_cmp (b : Fin d → ℕ) :
    CmpIn (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N))
      ((IbO V W b - 1 : OE c (Lam d L N)) : SA c (Lam d L N)) := by
  set S : Set (Lam d L N) := ↑(nbhd j (blockSet (L := L) (N := N) j b))
  let T : Subalgebra ℂ (OE c (Lam d L N)) :=
    { carrier := {F | CmpIn S (F : SA c (Lam d L N))}
      mul_mem' := fun hF hG => CmpIn.mul hF hG
      add_mem' := fun hF hG => CmpIn.add hF hG
      algebraMap_mem' := fun r => by
        show CmpIn S ((algebraMap ℂ (OE c (Lam d L N)) r : OE c (Lam d L N)) : SA c (Lam d L N))
        rw [Algebra.algebraMap_eq_smul_one]
        exact CmpIn.smul r CmpIn.one }
  have hV : -V b ∈ T := by
    show CmpIn S (-(V b : SA c (Lam d L N)))
    exact (H.hO.hVl b).neg
  have hW : W b ∈ T := H.hO.hWl b
  have h : IbO V W b - 1 ∈ T := by
    rw [IbO]
    exact sub_mem (mul_mem (oexp_mem hV) (add_mem (one_mem _) hW)) (one_mem _)
  exact h

/-! ### `δI`, `θK`, `θJ` -/

theorem gdIO_full {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oT2 w j ℓ' ℓC ((Obs.Gen.dIG (algO C) (ingrO P j C V W K) b : OE c (Lam d L N ⊕ Lam d L N)) :
      SA c (Lam d L N ⊕ Lam d L N)) ≤
      ENNReal.ofReal (Step2.Q1 d * (Real.exp (2 * r + 2 * r) - 1) + (Real.exp (tIB d L r Cl Clo cS) - 1)) := by
  have hr := H.hr
  have hQ := H.hB.hQ1
  have h4 : 0 ≤ Real.exp (2 * r + 2 * r) - 1 := by
    linarith [Real.add_one_le_exp (2 * r + 2 * r), show 0 ≤ 2 * r + 2 * r by linarith]
  have hI : 0 ≤ Real.exp (tIB d L r Cl Clo cS) - 1 := by linarith [Real.add_one_le_exp (tIB d L r Cl Clo cS), H.htI]
  have e : Obs.Gen.dIG (algO C) (ingrO P j C V W K) b =
      thetaO (IbO V W b - 1) - inclO (IpO P j C V W K b - 1) := by
    show thetaO (IbO V W b) - inclO (expU (-upB P j C V W K b) (-upO P j C V W K b) *
      GpO P j C V W K b) = _
    rw [map_sub, map_sub, map_one, map_one, IpO]; abel
  rw [e]
  have t1 : oT2 w j ℓ' ℓC (thetaO (IbO V W b - 1) : SA c (Lam d L N ⊕ Lam d L N)) ≤
      ENNReal.ofReal (Step2.Q1 d * (Real.exp (2 * r + 2 * r) - 1)) :=
    Step2.tj_of (by linarith) (thetaO_block_le2 H.hB.hd H.hB.hLp H.hB.hj H.hO.hℓ' H.hO.hℓC
      H.hO.hsum H.hw0 (H.IbO_sub_one_cmp b)) (H.IbO_sub_one_full hb)
  have t2 : oT2 w j ℓ' ℓC (inclO (IpO P j C V W K b - 1) : SA c (Lam d L N ⊕ Lam d L N)) ≤
      ENNReal.ofReal (Real.exp (tIB d L r Cl Clo cS) - 1) :=
    (inclO_le2 H.hO.hℓ' _).trans (H.IpO_sub_one_full hb)
  have hn := nrmP_T2 (E := Dir d) (p := pPhi d) (X := Lam d L N) (ℓC := ℓC) H.hh' H.hO.hℓ'
  rw [show ((thetaO (IbO V W b - 1) - inclO (IpO P j C V W K b - 1) :
      OE c (Lam d L N ⊕ Lam d L N)) : SA c (Lam d L N ⊕ Lam d L N)) =
      (thetaO (IbO V W b - 1) : SA c (Lam d L N ⊕ Lam d L N)) +
        -(inclO (IpO P j C V W K b - 1) : SA c (Lam d L N ⊕ Lam d L N)) by
      rw [AddSubgroupClass.coe_sub, sub_eq_add_neg]]
  refine (oNorm_add_le' hn _ _).trans ?_
  rw [oNorm_neg' hn]
  exact le_ofReal_add (mul_nonneg (by linarith) h4) hI t1 t2

end BHF

end

end Obs2
