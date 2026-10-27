import Obs2.Est.BlockO2
import Obs2.Est.BlockOAB1
import Obs2.Est.EstBlockU

/-!
# Block bounds in the full norm on the `σ_aσ_b` sector (`ab` copy of `Obs2.Est.BlockO2`)

`BHFU` bundles the bulk block hypotheses `Step2.BH` and the `ab` observable hypotheses
`Obs2.BHOU` (inputs in `abSub`, all four components local, any weights with `w.Sub`). The block
coordinates `VpO_full`, `WpO_full`, `upO_full`, the factors `IbO_sub_one_full`, `IpO_sub_one_full`,
`gdIO_full`, `expU_full`, `IpO_full` are as in `BHF` (namespace `BHFU`); the only change is the
two-scale bound for `θ`, which holds for any weights under `CmpInA` (`thetaO_block_le2A`).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step FRD ENNReal

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

/-! ### The hypotheses -/

/-- The full-norm block hypotheses at scale `j` (single-source weights, common radius `r`). -/
structure BHFU (P : ObsPts d L N) (j : ℕ) (ℓ ℓ' ℓC : ℝ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : OFam c d L N) (K : OAct c d L N) (w : Wt) (A r Cl cS Clo : ℝ) : Prop where
  hB : Step2.BH j ℓ ℓ' ℓC C (bulkF V) (bulkF W) (bulkF K) A r Cl cS
  hO : BHOU P j ℓ ℓ' ℓC C V W K w r r r r Clo cS
  hKl : ∀ X, IsConn j X → CmpInA (nbhd j X : Set (Lam d L N)) (K X : SA c (Lam d L N))
  hKo : ∀ X, IsConn j X →
    ENNReal.ofReal (A ^ (nb j X - 2 ^ d)) * oTo w j ℓ (K X) ≤ ENNReal.ofReal r

namespace BHFU

variable {P : ObsPts d L N} {j : ℕ} {ℓ ℓ' ℓC : ℝ} {C : Matrix (Lam d L N) (Lam d L N) ℂ}
  {V W : OFam c d L N} {K : OAct c d L N} {w : Wt} {A r Cl cS Clo : ℝ}
  (H : BHFU P j ℓ ℓ' ℓC C V W K w A r Cl cS Clo)
include H

theorem hh' : (0 : ℝ) < (L : ℝ) ^ (j + 1) := H.hB.hh'

theorem hh : (0 : ℝ) < (L : ℝ) ^ j := pow_pos H.hB.hL0 _

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
  refine (H.full_le this this ?_ (H.hO.hVm' hb)).trans (le_of_eq (by rw [two_mul]))
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
    CmpInA (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N))
      ((IbO V W b - 1 : OE c (Lam d L N)) : SA c (Lam d L N)) := by
  set S : Set (Lam d L N) := ↑(nbhd j (blockSet (L := L) (N := N) j b))
  let T : Subalgebra ℂ (OE c (Lam d L N)) :=
    { carrier := {F | CmpInA S (F : SA c (Lam d L N))}
      mul_mem' := fun hF hG => CmpInA.mul hF hG
      add_mem' := fun hF hG => CmpInA.add hF hG
      algebraMap_mem' := fun r => by
        show CmpInA S ((algebraMap ℂ (OE c (Lam d L N)) r : OE c (Lam d L N)) : SA c (Lam d L N))
        rw [Algebra.algebraMap_eq_smul_one]
        exact CmpInA.smul r CmpInA.one }
  have hV : -V b ∈ T := by
    show CmpInA S (-(V b : SA c (Lam d L N)))
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
    Step2.tj_of (by linarith) (thetaO_block_le2A H.hB.hd H.hB.hLp H.hB.hj H.hO.hℓ' H.hO.hℓC
      H.hO.hsum (H.IbO_sub_one_cmp b)) (H.IbO_sub_one_full hb)
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

end BHFU

end

end Obs2
