import Obs2.Est.LastKO1
import Obs2.Est.BlockO5
import Step2.Last.LastNBlock

/-!
# The crude bound of the reference map with sources at the last scale

Block bounds for the reference map of `Obs2.Est.LastKO1` at `j + 1 = N` in the full norm with
single-source weights (`w_ab = 0`), with a common radius `r` for the bulk parts (the hypotheses
`Step2.LastN.BHN` of the bulk last step) and the observable parts. No range of `C` is used: the
second-order term `F(V'_B, V'(Λ))` is summed over all `|𝓑_j(Λ)| ≤ L^d` blocks, and there is no
localisation.

* `BHFN`: the hypotheses; `BHFN.khyp`: the block hypotheses `Obs.Gen.KHypG` of the generic crude
  bound for the reference ingredients;
* **`KNO_crude_ts`**: for `L ≥ L₀`, `A ≥ A₀(L)` there is `r₀(L, A) > 0` such that inputs of size
  `≤ r₀` (bulk and observable parts, observable `K` with the regulator `A^{(|𝓑_j(X)|-2^d)_+}`) give
  `‖K'(Λ)‖_{T_N(ℓ')} ≤ 1` (full norm).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step FRD ENNReal Obs.Gen

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

/-- The observable constant of `S(B)` at the last scale. -/
def cSNO (d L : ℕ) : ℝ := (L : ℝ) ^ d * (2 * Step2.Q1 d ^ 2) + Step2.Q1 d

/-- The exponent constant of `‖I'(B) - 1‖` at the last scale. -/
def cTN (d L : ℕ) : ℝ := 6 * Step2.Q1 d + Step2.LastN.cSN d L + cSNO d L

/-- The hypotheses for the block bounds of the reference map at the last scale. -/
structure BHFN (j : ℕ) (ℓ ℓ' ℓC : ℝ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : OFam c d L N) (K : OAct c d L N) (w : Wt) (A r : ℝ) : Prop where
  hB : Step2.LastN.BHN j ℓ ℓ' ℓC C (bulkF V) (bulkF W) (bulkF K) A r
  hw : w.Sub
  hw0 : w.ab = 0
  hVl : ∀ b, CmpIn (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N))
    (V b : SA c (Lam d L N))
  hWl : ∀ b, CmpIn (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N))
    (W b : SA c (Lam d L N))
  hKl : ∀ X, IsConn j X → CmpIn (nbhd j X : Set (Lam d L N)) (K X : SA c (Lam d L N))
  hVm : ∀ b ∈ blockIdx (L := L) (N := N) j, oTo w j ℓ (V b) ≤ ENNReal.ofReal r
  hWm : ∀ b ∈ blockIdx (L := L) (N := N) j, oTo w j ℓ (W b) ≤ ENNReal.ofReal r
  hKo : ∀ X, IsConn j X →
    ENNReal.ofReal (A ^ (nb j X - 2 ^ d)) * oTo w j ℓ (K X) ≤ ENNReal.ofReal r

namespace BHFN

variable {j : ℕ} {ℓ ℓ' ℓC : ℝ} {C : Matrix (Lam d L N) (Lam d L N) ℂ}
  {V W : OFam c d L N} {K : OAct c d L N} {w : Wt} {A r : ℝ}
  (H : BHFN j ℓ ℓ' ℓC C V W K w A r)
include H

theorem hr : 0 ≤ r := H.hB.hr
theorem hr1 : r ≤ 1 := H.hB.hr1
theorem hQ1 : 1 ≤ Step2.Q1 d := H.hB.hQ1
theorem hQ0 : 0 ≤ Step2.Q1 d := by linarith [H.hQ1]
theorem hj : j < N := H.hB.hj
theorem hh' : (0 : ℝ) < (L : ℝ) ^ (j + 1) := H.hB.hh'
theorem hh : (0 : ℝ) < (L : ℝ) ^ j := pow_pos H.hB.hL0 _
theorem hLd : (0 : ℝ) ≤ (L : ℝ) ^ d := pow_nonneg H.hB.hL0.le d

theorem hcSNO : 0 ≤ cSNO d L := by
  have := H.hQ0; have := H.hLd; unfold cSNO; positivity

theorem hcTN : 0 ≤ cTN d L := by
  have := H.hQ0; have := H.hB.hcS; have := H.hcSNO; unfold cTN; linarith

theorem full_le {k : ℕ} {ℓ₀ : ℝ} {F : OE c (Lam d L N)} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h1 : Tj d (L : ℝ) k ℓ₀ (F : SA c (Lam d L N)).e ≤ ENNReal.ofReal a)
    (h2 : oTo w k ℓ₀ F ≤ ENNReal.ofReal b) :
    oTj d L w k ℓ₀ (F : SA c (Lam d L N)) ≤ ENNReal.ofReal (a + b) := by
  rw [oTj_eq_bulk_add]; exact le_ofReal_add ha hb h1 h2

/-! ### The inputs -/

theorem V_full {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTj d L w j ℓ (V b : SA c (Lam d L N)) ≤ ENNReal.ofReal (2 * r) := by
  have := H.hr
  refine (H.full_le this this ?_ (H.hVm b hb)).trans (le_of_eq (by rw [two_mul]))
  exact H.hB.hVr b hb

theorem W_full {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTj d L w j ℓ (W b : SA c (Lam d L N)) ≤ ENNReal.ofReal (2 * r) := by
  have := H.hr
  refine (H.full_le this this ?_ (H.hWm b hb)).trans (le_of_eq (by rw [two_mul]))
  exact H.hB.hWr b hb

/-! ### The observable parts at scale `j + 1` -/

theorem Vpr_o {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTo w (j + 1) ℓ' (VprO C V b) ≤ ENNReal.ofReal (Step2.Q1 d * r) := by
  rw [VprO]
  refine (oTo_EthO_le2 H.hw0 H.hB.hd H.hB.hLp H.hj H.hB.hℓ' H.hB.hℓC H.hB.hsum H.hB.hC
    (H.hVl b)).trans ?_
  exact le_ofReal_mul H.hQ0
    (ENNReal.ofReal_le_ofReal (Step2.pq_pow_le_Q1 H.hB.hd H.hj.le b)) (H.hVm b hb)

theorem V2_o {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTo w (j + 1) (2 * ℓ) (V b) ≤ ENNReal.ofReal (Step2.Q1 d * r) := by
  refine (oTj_succ_two_le H.hw0 H.hB.hd H.hB.hLp H.hj (H.hVl b).πobs H.hB.hℓ).trans ?_
  exact le_ofReal_mul H.hQ0
    (ENNReal.ofReal_le_ofReal (Step2.pq_pow_le_Q1 H.hB.hd H.hj.le b)) (H.hVm b hb)

theorem pairh_o {b b' : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j)
    (hb' : b' ∈ blockIdx (L := L) (N := N) j) :
    oTo w (j + 1) ℓ' (FCO C (EthO C (πobs (V b)))
      (EthO C (emb (bulk (V b')) : OE c (Lam d L N)))) ≤
      ENNReal.ofReal (2 * Step2.Q1 d ^ 2 * (r * r)) := by
  have hr := H.hr
  refine (oTo_le w _ _ _).trans ((oTj_FCO_le H.hB.hℓ' H.hB.hℓC H.hB.hsum H.hB.hC H.hw _ _).trans ?_)
  have e : 2 * Step2.Q1 d ^ 2 * (r * r) = 2 * ((Step2.Q1 d * r) * (Step2.Q1 d * r)) := by ring
  rw [e, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  refine mul_le_mul_right (le_ofReal_mul (mul_nonneg H.hQ0 hr) (H.V2_o hb) ?_) _
  rw [oTj_emb]; exact H.hB.V2_le hb'

theorem card_blockIdx_le : ((blockIdx (d := d) (L := L) (N := N) j).card : ℝ) ≤ (L : ℝ) ^ d := by
  exact_mod_cast Step2.LastN.card_blockIdx_last (d := d) (L := L) H.hB.hjN

theorem SFO_o {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTo w (j + 1) ℓ' (SFO j C V b) ≤ ENNReal.ofReal ((L : ℝ) ^ d * (2 * Step2.Q1 d ^ 2) * r) := by
  have hr := H.hr
  rw [BHO.oTo_SFO_eq H.hw0]
  refine (oTo_sum_le w _ _ _ _).trans ?_
  refine (le_ofReal_sum_const _ (by positivity) fun b' hb' => H.pairh_o hb hb').trans
    (ENNReal.ofReal_le_ofReal ?_)
  have h1 := H.card_blockIdx_le
  have hrr : r * r ≤ r := by nlinarith [H.hr1]
  calc ((blockIdx (L := L) (N := N) j).card : ℝ) * (2 * Step2.Q1 d ^ 2 * (r * r))
      ≤ (L : ℝ) ^ d * (2 * Step2.Q1 d ^ 2 * r) := by gcongr
    _ = _ := by ring

theorem EthW_o {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTo w (j + 1) ℓ' (EthO C (W b)) ≤ ENNReal.ofReal (Step2.Q1 d * r) := by
  refine (oTo_EthO_le2 H.hw0 H.hB.hd H.hB.hLp H.hj H.hB.hℓ' H.hB.hℓC H.hB.hsum H.hB.hC
    (H.hWl b)).trans ?_
  exact le_ofReal_mul H.hQ0
    (ENNReal.ofReal_le_ofReal (Step2.pq_pow_le_Q1 H.hB.hd H.hj.le b)) (H.hWm b hb)

theorem Sb_o {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTo w (j + 1) ℓ' (SbO j C V W b) ≤ ENNReal.ofReal (cSNO d L * r) := by
  have hr := H.hr
  have := H.hLd
  rw [SbO]
  refine (oTo_add_le w _ _ _ _).trans ((le_ofReal_add (by positivity) (mul_nonneg H.hQ0 hr)
    (H.SFO_o hb) (H.EthW_o hb)).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_)))
  unfold cSNO; ring

theorem Sb_full {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTj d L w (j + 1) ℓ' (SbO j C V W b : SA c (Lam d L N)) ≤
      ENNReal.ofReal ((Step2.LastN.cSN d L + cSNO d L) * r) := by
  have hr := H.hr
  refine (H.full_le (mul_nonneg H.hB.hcS hr) (mul_nonneg H.hcSNO hr) ?_ (H.Sb_o hb)).trans
    (le_of_eq (by ring_nf))
  show Tj d (L : ℝ) (j + 1) ℓ' ((bulk (SbO j C V W b) : EvR (Lam d L N)) : Alg d L N) ≤ _
  rw [bulk_SbO]; exact H.hB.Sb_le hb

theorem upBN_le {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    ‖upBN C V b‖ ≤ Step2.Q1 d * r := by
  rw [upBN_eq]; exact H.hB.upN_le hb

theorem upON_full {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTj d L w (j + 1) ℓ' (upON C V b : SA c (Lam d L N)) ≤ ENNReal.ofReal (Step2.Q1 d * r) := by
  rw [oTj_eq_bulk_add]
  have e0 : (upON C V b : SA c (Lam d L N)).e = 0 := by
    show ((bulk (upON C V b) : EvR (Lam d L N)) : Alg d L N) = 0
    rw [bulk_upON]; rfl
  rw [e0, show Tj d (L : ℝ) (j + 1) ℓ' (0 : Alg d L N) = 0 from tNorm_zero', zero_add]
  rw [upON, oTo_πobs]
  exact (oTo_epsO_le w H.hh' H.hB.hℓ' _).trans (H.Vpr_o hb)

theorem YpN_full {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTj d L w (j + 1) ℓ' (YpN C V b : SA c (Lam d L N)) ≤ ENNReal.ofReal (4 * (Step2.Q1 d * r)) := by
  have h0 := mul_nonneg H.hQ0 H.hr
  have ho : oTo w (j + 1) ℓ' (YpN C V b) ≤ ENNReal.ofReal (2 * (Step2.Q1 d * r)) := by
    rw [YpN]
    refine (oTo_sub_le w _ _ _ _).trans ?_
    refine ((add_le_add (oTo_sub_le w _ _ _ _) ((oTo_le w _ _ _).trans (H.upON_full hb))).trans
      ?_)
    rw [oTo_algebraMap, add_zero]
    exact (le_ofReal_add h0 h0 (H.Vpr_o hb) le_rfl).trans (le_of_eq (by ring_nf))
  refine (H.full_le (a := 2 * (Step2.Q1 d * r)) (b := 2 * (Step2.Q1 d * r)) (by linarith)
    (by linarith) ?_ ho).trans (le_of_eq (by ring_nf))
  show Tj d (L : ℝ) (j + 1) ℓ' ((bulk (YpN C V b) : EvR (Lam d L N)) : Alg d L N) ≤ _
  rw [bulk_YpN]; exact H.hB.VpN_le hb

/-! ### The block factors -/

theorem eps_neg_V (b : Fin d → ℕ) : ε (((-V b : OE c (Lam d L N)) : SA c (Lam d L N)).e) = 0 := by
  show ε ((bulk (-V b) : EvR (Lam d L N)) : Alg d L N) = 0
  rw [map_neg, NegMemClass.coe_neg, map_neg]
  have := H.hB.hV0 b
  simp only [bulkF_apply] at this
  rw [this, neg_zero]

theorem eps_neg_YpN (b : Fin d → ℕ) :
    ε (((-YpN C V b : OE c (Lam d L N)) : SA c (Lam d L N)).e) = 0 := by
  show ε (-(YpN C V b : SA c (Lam d L N))).e = 0
  rw [neg_e, map_neg, eps_YpN, neg_zero]

theorem eps_neg_upON (b : Fin d → ℕ) :
    ε (((-upON C V b : OE c (Lam d L N)) : SA c (Lam d L N)).e) = 0 :=
  ε_bulk_eq_zero_of_obs (by rw [map_neg, bulk_upON, neg_zero])

theorem eps_upON (b : Fin d → ℕ) :
    ε (((upON C V b : OE c (Lam d L N)) : SA c (Lam d L N)).e) = 0 :=
  ε_bulk_eq_zero_of_obs (bulk_upON C V b)

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
    exact (H.hVl b).neg
  have hW : W b ∈ T := H.hWl b
  have h : IbO V W b - 1 ∈ T := by
    rw [IbO]
    exact sub_mem (mul_mem (oexp_mem hV) (add_mem (one_mem _) hW)) (one_mem _)
  exact h

theorem GpN_sub_one_full {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTj d L w (j + 1) ℓ' ((GpN j C V W b - 1 : OE c (Lam d L N)) : SA c (Lam d L N)) ≤
      ENNReal.ofReal (Real.exp (4 * (Step2.Q1 d * r) +
        (Step2.LastN.cSN d L + cSNO d L) * r) - 1) := by
  have h0 := mul_nonneg H.hQ0 H.hr
  have h0' := mul_nonneg (add_nonneg H.hB.hcS H.hcSNO) H.hr
  have hV : oTj d L w (j + 1) ℓ' ((-YpN C V b : OE c (Lam d L N)) : SA c (Lam d L N)) ≤
      ENNReal.ofReal (4 * (Step2.Q1 d * r)) :=
    (le_of_eq (oT_neg (E := Dir d) (p := pPhi d) (h := (L : ℝ) ^ (j + 1)) (ℓ := ℓ') (w := w)
      (YpN C V b : SA c (Lam d L N)))).trans (H.YpN_full hb)
  have h1 := oT_oexp_sub_one_le (E := Dir d) (p := pPhi d) H.hh' H.hB.hℓ' H.hw (H.eps_neg_YpN b)
    (by linarith) hV
  have h2 : oTj d L w (j + 1) ℓ'
      (((1 + SbO j C V W b) - 1 : OE c (Lam d L N)) : SA c (Lam d L N)) ≤
      ENNReal.ofReal (Real.exp ((Step2.LastN.cSN d L + cSNO d L) * r) - 1) := by
    rw [oe_one_add_sub_one]
    refine (H.Sb_full hb).trans (ENNReal.ofReal_le_ofReal ?_)
    linarith [Real.add_one_le_exp ((Step2.LastN.cSN d L + cSNO d L) * r)]
  exact oT_mul_sub_one_le2 H.hh' H.hB.hℓ' H.hw _ _ (by linarith) h0' h1 h2

theorem eum_sub_one_full {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTj d L w (j + 1) ℓ'
      ((expU (-upBN C V b) (-upON C V b) - 1 : OE c (Lam d L N)) : SA c (Lam d L N)) ≤
      ENNReal.ofReal (Real.exp (2 * (Step2.Q1 d * r)) - 1) := by
  have h0 := mul_nonneg H.hQ0 H.hr
  have hu : oTj d L w (j + 1) ℓ' ((-upON C V b : OE c (Lam d L N)) : SA c (Lam d L N)) ≤
      ENNReal.ofReal (Step2.Q1 d * r) :=
    (le_of_eq (oT_neg (E := Dir d) (p := pPhi d) (h := (L : ℝ) ^ (j + 1)) (ℓ := ℓ') (w := w)
      (upON C V b : SA c (Lam d L N)))).trans (H.upON_full hb)
  refine (oT_expU_sub_one_le H.hh' H.hB.hℓ' H.hw _ (H.eps_neg_upON b) h0 hu).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have := Real.exp_le_exp.2 (add_le_add (show ‖-upBN C V b‖ ≤ Step2.Q1 d * r by
    rw [norm_neg]; exact H.upBN_le hb) (le_refl (Step2.Q1 d * r)))
  have e2 : 2 * (Step2.Q1 d * r) = Step2.Q1 d * r + Step2.Q1 d * r := by ring
  rw [e2]; linarith

theorem eu_full {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTj d L w (j + 1) ℓ' (expU (upBN C V b) (upON C V b) : SA c (Lam d L N)) ≤
      ENNReal.ofReal (Real.exp (2 * (Step2.Q1 d * r))) := by
  have h0 := mul_nonneg H.hQ0 H.hr
  refine oT_le_exp_of_sub_one H.hh' H.hB.hℓ' (by linarith) ?_
  refine (oT_expU_sub_one_le H.hh' H.hB.hℓ' H.hw _ (H.eps_upON b) h0 (H.upON_full hb)).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have := Real.exp_le_exp.2 (add_le_add (H.upBN_le hb) (le_refl (Step2.Q1 d * r)))
  have e : 2 * (Step2.Q1 d * r) = Step2.Q1 d * r + Step2.Q1 d * r := by ring
  rw [e]; linarith

theorem It_sub_one_full {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTj d L w (j + 1) ℓ'
      ((It (ingrN j C V W K) b - 1 : OE c (Lam d L N)) : SA c (Lam d L N)) ≤
      ENNReal.ofReal (Real.exp (cTN d L * r) - 1) := by
  have h0 := mul_nonneg H.hQ0 H.hr
  have h0' := mul_nonneg (add_nonneg H.hB.hcS H.hcSNO) H.hr
  have := oT_mul_sub_one_le2 H.hh' H.hB.hℓ' H.hw _ _ (by linarith) (by linarith)
    (H.eum_sub_one_full hb) (H.GpN_sub_one_full hb)
  refine this.trans (le_of_eq ?_)
  congr 3
  unfold cTN; ring

theorem It_full {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTj d L w (j + 1) ℓ' ((It (ingrN j C V W K) b : OE c (Lam d L N)) : SA c (Lam d L N)) ≤
      ENNReal.ofReal (Real.exp (cTN d L * r)) :=
  oT_le_exp_of_sub_one H.hh' H.hB.hℓ' (mul_nonneg H.hcTN H.hr) (H.It_sub_one_full hb)

/-! ### `δI`, `θK`, the prefactors -/

theorem gdI_full {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oT2 w j ℓ' ℓC ((dIG (algO C) (ingrN j C V W K) b : OE c (Lam d L N ⊕ Lam d L N)) :
      SA c (Lam d L N ⊕ Lam d L N)) ≤
      ENNReal.ofReal (Step2.Q1 d * (Real.exp (2 * r + 2 * r) - 1) +
        (Real.exp (cTN d L * r) - 1)) := by
  have hr := H.hr
  have hQ := H.hQ1
  have h4 : 0 ≤ Real.exp (2 * r + 2 * r) - 1 := by
    linarith [Real.add_one_le_exp (2 * r + 2 * r), show 0 ≤ 2 * r + 2 * r by linarith]
  have hI : 0 ≤ Real.exp (cTN d L * r) - 1 := by
    linarith [Real.add_one_le_exp (cTN d L * r), mul_nonneg H.hcTN hr]
  have e : dIG (algO C) (ingrN j C V W K) b =
      thetaO (IbO V W b - 1) - inclO (It (ingrN j C V W K) b - 1) := by
    show thetaO (IbO V W b) - inclO (It (ingrN j C V W K) b) = _
    rw [map_sub, map_sub, map_one, map_one]; abel
  rw [e]
  have t1 : oT2 w j ℓ' ℓC (thetaO (IbO V W b - 1) : SA c (Lam d L N ⊕ Lam d L N)) ≤
      ENNReal.ofReal (Step2.Q1 d * (Real.exp (2 * r + 2 * r) - 1)) :=
    Step2.tj_of (by linarith) (thetaO_block_le2 H.hB.hd H.hB.hLp H.hj H.hB.hℓ' H.hB.hℓC
      H.hB.hsum H.hw0 (H.IbO_sub_one_cmp b)) (H.IbO_sub_one_full hb)
  have t2 : oT2 w j ℓ' ℓC (inclO (It (ingrN j C V W K) b - 1) : SA c (Lam d L N ⊕ Lam d L N)) ≤
      ENNReal.ofReal (Real.exp (cTN d L * r) - 1) :=
    (inclO_le2 H.hB.hℓ' _).trans (H.It_sub_one_full hb)
  have hn := nrmP_T2 (E := Dir d) (p := pPhi d) (X := Lam d L N) (ℓC := ℓC) H.hh' H.hB.hℓ'
  rw [show ((thetaO (IbO V W b - 1) - inclO (It (ingrN j C V W K) b - 1) :
      OE c (Lam d L N ⊕ Lam d L N)) : SA c (Lam d L N ⊕ Lam d L N)) =
      (thetaO (IbO V W b - 1) : SA c (Lam d L N ⊕ Lam d L N)) +
        -(inclO (It (ingrN j C V W K) b - 1) : SA c (Lam d L N ⊕ Lam d L N)) by
      rw [AddSubgroupClass.coe_sub, sub_eq_add_neg]]
  refine (oNorm_add_le' hn _ _).trans ?_
  rw [oNorm_neg' hn]
  exact le_ofReal_add (mul_nonneg (by linarith) h4) hI t1 t2

theorem gdI_le (hr4 : 4 * r ≤ 1) (hT : cTN d L * r ≤ 1)
    {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oT2 w j ℓ' ℓC ((dIG (algO C) (ingrN j C V W K) b : OE c (Lam d L N ⊕ Lam d L N)) :
      SA c (Lam d L N ⊕ Lam d L N)) ≤
      ENNReal.ofReal ((8 * Step2.Q1 d + 2 * cTN d L) * r) := by
  have hr := H.hr
  have hQ := H.hQ1
  refine (H.gdI_full hb).trans (ENNReal.ofReal_le_ofReal ?_)
  have h1 : Real.exp (2 * r + 2 * r) - 1 ≤ 2 * (2 * r + 2 * r) :=
    exp_sub_one_le (by linarith) (by linarith)
  have h2 : Real.exp (cTN d L * r) - 1 ≤ 2 * (cTN d L * r) :=
    exp_sub_one_le (mul_nonneg H.hcTN hr) hT
  have h4 := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ Step2.Q1 d by linarith)
  nlinarith

theorem K_full {X : Finset (Lam d L N)} (hX : IsConn j X) :
    oTj d L w j ℓ (K X : SA c (Lam d L N)) ≤
      ENNReal.ofReal (2 * r * A ^ 2 ^ d * A⁻¹ ^ nb j X) := by
  have hA := H.hB.hA
  have hr := H.hr
  have hb : Tj d (L : ℝ) j ℓ (K X : SA c (Lam d L N)).e ≤
      ENNReal.ofReal (r * A ^ 2 ^ d * A⁻¹ ^ nb j X) := by
    refine le_of_wt hA hr ?_
    exact (wnorm_le_Knorm (ℓ := ℓ) (A := A) (K := bulkF K) hX).trans H.hB.hKr
  have ho : oTo w j ℓ (K X) ≤ ENNReal.ofReal (r * A ^ 2 ^ d * A⁻¹ ^ nb j X) :=
    le_of_wt hA hr (H.hKo X hX)
  have hA0 : 0 < A := by linarith
  refine (H.full_le (by positivity) (by positivity) hb ho).trans (le_of_eq ?_)
  congr 1; ring

theorem thetaK_full {X : Finset (Lam d L N)} (hX : IsConn j X) :
    oT2 w j ℓ' ℓC (thetaO (K X) : SA c (Lam d L N ⊕ Lam d L N)) ≤
      ENNReal.ofReal (2 * r * A ^ 2 ^ d * (Step2.Q1 d / A) ^ nb j X) := by
  have hA := H.hB.hA
  have hA0 : 0 < A := by linarith
  have hr := H.hr
  refine (thetaO_conn_le2 H.hB.hd H.hB.hLp H.hj H.hB.hℓ' H.hB.hℓC H.hB.hsum H.hw0
    (H.hKl X hX)).trans ?_
  refine (mul_le_mul_right (H.K_full hX) _).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (pow_nonneg H.hQ0 _)]
  congr 1
  rw [div_eq_mul_inv, mul_pow]; ring

theorem pref_full (U Z : Finset (Lam d L N)) :
    oTj d L w (j + 1) ℓ' ((PrefG j (ingrN j C V W K) U *
      ItPow j (ingrN j C V W K) (U \ Z) : OE c (Lam d L N)) : SA c (Lam d L N)) ≤
      ENNReal.ofReal (Real.exp ((2 * (Step2.Q1 d * r) + cTN d L * r) * nb j U)) := by
  classical
  have h0 := mul_nonneg H.hQ0 H.hr
  have ht := mul_nonneg H.hcTN H.hr
  set n := oSN (nrmP_tNorm (E := Dir d) (p := pPhi d) (X := Lam d L N) (ℓ := ℓ') H.hh'
    H.hB.hℓ') w H.hw
  have hP : n.nrm (PrefG j (ingrN j C V W K) U) ≤
      ENNReal.ofReal (Real.exp (2 * (Step2.Q1 d * r)) ^ nb j U) := by
    have := n.prodR (blocks j U) (fun b => expU (upBN C V b) (upON C V b))
      (fun _ => Real.exp (2 * (Step2.Q1 d * r))) (fun _ _ => (Real.exp_pos _).le)
      (fun b hb => H.eu_full (mem_blockIdx_of_mem_blocks hb))
    rwa [prod_const] at this
  have hI : n.nrm (ItPow j (ingrN j C V W K) (U \ Z)) ≤
      ENNReal.ofReal (Real.exp (cTN d L * r) ^ nb j U) := by
    have := n.prodR (blocks j (U \ Z)) (fun b => It (ingrN j C V W K) b)
      (fun _ => Real.exp (cTN d L * r)) (fun _ _ => (Real.exp_pos _).le)
      (fun b hb => H.It_full (mem_blockIdx_of_mem_blocks hb))
    rw [prod_const] at this
    refine this.trans (ENNReal.ofReal_le_ofReal ?_)
    exact pow_le_pow_right₀ (Real.one_le_exp ht) (card_le_card (blocks_mono sdiff_subset))
  refine (n.mulR (by positivity) hP hI).trans (le_of_eq ?_)
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 2; ring

theorem hE (x : OE c (Lam d L N ⊕ Lam d L N)) :
    (oSN (nrmP_tNorm (E := Dir d) (p := pPhi d) (X := Lam d L N) (ℓ := ℓ') H.hh' H.hB.hℓ') w
      H.hw).nrm ((algO C).E x) ≤
    (oSN (nrmP_T2 (E := Dir d) (p := pPhi d) (X := Lam d L N) (ℓC := ℓC) H.hh' H.hB.hℓ') w
      H.hw).nrm x := by
  rw [oSN_nrm, oSN_nrm]
  show oNorm (Tj d (L : ℝ) (j + 1) ℓ') w (ECCS C (x : SA c (Lam d L N ⊕ Lam d L N))) ≤ _
  simp only [oNorm, ECCS_e, ECCS_a, ECCS_b, ECCS_ab]
  gcongr <;> exact Step2.ECC_succ_le2 H.hB.hℓ' H.hB.hℓC H.hB.hC _

/-- **The block hypotheses of the generic crude bound** for the reference map. -/
theorem khyp (hAQ : Step2.Q1 d ≤ A) (hr4 : 4 * r ≤ 1) (hT : cTN d L * r ≤ 1)
    (hκ : 2 * r * A ^ 2 ^ d ≤ 1)
    (hδ : (8 * Step2.Q1 d + 2 * cTN d L) * r * (A / Step2.Q1 d) ≤ 1) :
    KHypG (algO C) j (ingrN j C V W K)
      (oSN (nrmP_T2 (E := Dir d) (p := pPhi d) (X := Lam d L N) (ℓC := ℓC) H.hh' H.hB.hℓ') w
        H.hw)
      (A / Step2.Q1 d) (2 * r * A ^ 2 ^ d)
      ((8 * Step2.Q1 d + 2 * cTN d L) * r * (A / Step2.Q1 d)) 0 := by
  have hr := H.hr
  have hQ := H.hQ1
  have hQ0 : 0 < Step2.Q1 d := by linarith
  have hA0 : 0 < A := by linarith
  have hT0 := H.hcTN
  have hinv : (A / Step2.Q1 d)⁻¹ = Step2.Q1 d / A := inv_div _ _
  have hAQ1 : A / Step2.Q1 d * (Step2.Q1 d / A) = 1 := by
    rw [div_mul_div_comm, mul_comm A, div_self (mul_ne_zero hQ0.ne' hA0.ne')]
  exact
    { hA := by rw [le_div_iff₀ hQ0, one_mul]; exact hAQ
      hκ₀ := mul_nonneg (mul_nonneg zero_le_two hr) (pow_nonneg hA0.le _)
      hκ₀1 := hκ
      hδ₁ := mul_nonneg (mul_nonneg (by linarith) hr) (div_nonneg hA0.le hQ0.le)
      hδ₁1 := hδ
      hcJ := le_rfl
      hK := fun X hX => by
        rw [hinv]; exact H.thetaK_full hX
      hdI := fun b hb => (H.gdI_le hr4 hT hb).trans (ENNReal.ofReal_le_ofReal (le_of_eq (by
        rw [hinv, mul_assoc ((8 * Step2.Q1 d + 2 * cTN d L) * r) (A / Step2.Q1 d)
          (Step2.Q1 d / A), hAQ1, mul_one])))
      hJ := fun b hb X => by
        show (oSN _ w H.hw).nrm ((algO C).θ 0) ≤ _
        rw [map_zero, oSN_nrm, ZeroMemClass.coe_zero]
        simp [oNorm, Step2.T2_zero]
      hJs := fun b X hX => rfl }

end BHFN

set_option maxHeartbeats 1000000 in
/-- **The crude bound of the reference map with sources at the last scale.** -/
theorem KNO_crude_ts (d : ℕ) (hd : 1 ≤ d) : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 ∧
    ∀ (N j : ℕ), j + 1 = N → ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, Step2.GoodCov2 j ℓC C →
    ∀ (c : Obs.Case) (w : Wt), w.ab = 0 →
    ∀ (V W : OFam c d L N) (K : OAct c d L N),
      Step2.InF j (bulkF V) → Step2.InF j (bulkF W) →
      (∀ b, ε ((bulkF V b : EvR (Lam d L N)) : Alg d L N) = 0) → Step2.InK2 j (bulkF K) →
      Step2.Fnorm j ℓ (bulkF V) ≤ ENNReal.ofReal r₀ →
      Step2.Fnorm j ℓ (bulkF W) ≤ ENNReal.ofReal r₀ →
      Knorm j ℓ A (bulkF K) ≤ ENNReal.ofReal r₀ →
      (∀ b, CmpIn (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N))
        (V b : SA c (Lam d L N))) →
      (∀ b, CmpIn (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N))
        (W b : SA c (Lam d L N))) →
      (∀ X, IsConn j X → CmpIn (nbhd j X : Set (Lam d L N)) (K X : SA c (Lam d L N))) →
      (∀ b ∈ blockIdx (L := L) (N := N) j, oTo w j ℓ (V b) ≤ ENNReal.ofReal r₀) →
      (∀ b ∈ blockIdx (L := L) (N := N) j, oTo w j ℓ (W b) ≤ ENNReal.ofReal r₀) →
      (∀ X, IsConn j X →
        ENNReal.ofReal (A ^ (nb j X - 2 ^ d)) * oTo w j ℓ (K X) ≤ ENNReal.ofReal r₀) →
        oTj d L w (j + 1) ℓ' (KNO j C V W K univ : SA c (Lam d L N)) ≤ ENNReal.ofReal 1 := by
  classical
  obtain ⟨c, hc⟩ := card_small_containing d
  obtain ⟨η, hη0, -, hcomb⟩ := comb2 d
  refine ⟨max (2 ^ (d + 3) + 8 * d + 1) ⌈pauliL0 d⌉₊, ?_⟩
  intro L _ hL
  have hL8 : 2 ^ (d + 3) + 8 * d < L :=
    lt_of_lt_of_le (Nat.lt_succ_self _) (le_trans (le_max_left _ _) hL)
  have hLp : pauliL0 d ≤ L :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hL)
  have hd8 : 2 ^ (d + 3) = 2 ^ d * 8 := by ring
  have hd4 : 2 ^ (d + 2) = 2 ^ d * 4 := by ring
  have hL2 : 2 ^ (d + 2) ≤ L := by
    rw [hd8] at hL8; rw [hd4]; generalize 2 ^ d = t at hL8 ⊢; omega
  have hL1 : 2 ^ d + 1 ≤ L := by
    rw [hd8] at hL8; generalize 2 ^ d = t at hL8 ⊢; omega
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set Q := Step2.Q1 d with hQdef
  have hQ : 1 ≤ Q := Step2.one_le_Q1 hd
  have hQ0 : 0 < Q := by linarith
  set M : ℕ := 2 ^ ((1 + c) * L ^ d) with hMdef
  have hM1 : 1 ≤ M := Nat.one_le_two_pow
  have hM1' : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  set P' : ℝ := Q * (2 * M) with hPdef
  have hP1 : 1 ≤ P' := by rw [hPdef]; nlinarith
  have hη' : 0 < 2 * η / (1 + 2 * η) := by positivity
  set A₀ : ℝ := Q * max 1 ((4 * P') ^ ((1 + 2 * η) / (2 * η))) with hA₀
  have hA₀1 : 1 ≤ A₀ := by
    rw [hA₀]; nlinarith [le_max_left (1 : ℝ) ((4 * P') ^ ((1 + 2 * η) / (2 * η)))]
  refine ⟨A₀, hA₀1, ?_⟩
  intro A hA
  have hA1 : 1 ≤ A := hA₀1.trans hA
  have hA0 : 0 < A := by linarith
  have hAQ : Q ≤ A := by
    refine le_trans ?_ hA
    rw [hA₀]; exact le_mul_of_one_le_right hQ0.le (le_max_left _ _)
  set Ar : ℝ := A / Q with hArdef
  have hArQ : Ar * Q = A := by rw [hArdef]; field_simp
  have hAr : max 1 ((4 * P') ^ ((1 + 2 * η) / (2 * η))) ≤ Ar := by
    rw [hArdef, le_div_iff₀ hQ0, mul_comm]; exact hA
  have hAr1 : 1 ≤ Ar := (le_max_left _ _).trans hAr
  have hAP : 4 * P' ≤ Ar ^ (2 * η / (1 + 2 * η)) := by
    calc 4 * P' = ((4 * P') ^ ((1 + 2 * η) / (2 * η))) ^ (2 * η / (1 + 2 * η)) := by
          rw [← Real.rpow_mul (by positivity)]
          rw [show (1 + 2 * η) / (2 * η) * (2 * η / (1 + 2 * η)) = 1 by field_simp]
          rw [Real.rpow_one]
      _ ≤ Ar ^ (2 * η / (1 + 2 * η)) :=
          Real.rpow_le_rpow (by positivity) ((le_max_right _ _).trans hAr) hη'.le
  have hLd : (0 : ℝ) ≤ (L : ℝ) ^ d := pow_nonneg hL0.le d
  have hcS : 0 ≤ Step2.LastN.cSN d L := by unfold Step2.LastN.cSN; positivity
  have hcSO : 0 ≤ cSNO d L := by unfold cSNO; positivity
  have hcT : 0 ≤ cTN d L := by unfold cTN; linarith
  set Bc : ℝ := (1 + 2 ^ d * 0) * (2 * A ^ 2 ^ d) + (8 * Q + 2 * cTN d L) * Ar with hBc
  have hBc0 : 0 ≤ Bc := by positivity
  set D : ℝ := 4 + cTN d L + 2 * (2 * Q + cTN d L) * (L : ℝ) ^ d + 2 * A ^ 2 ^ d +
    (8 * Q + 2 * cTN d L) * Ar + (Ar * P') ^ 2 ^ d * Bc with hD
  have hD0 : 0 < D := by positivity
  have hD1 : 1 ≤ D := by
    have : 0 ≤ (Ar * P') ^ 2 ^ d * Bc := by positivity
    rw [hD]; linarith only [hcT, this, show 0 ≤ 2 * (2 * Q + cTN d L) * (L : ℝ) ^ d by positivity,
      show 0 ≤ 2 * A ^ 2 ^ d by positivity, show 0 ≤ (8 * Q + 2 * cTN d L) * Ar by positivity]
  refine ⟨1 / D, one_div_pos.2 hD0, by rw [div_le_one hD0]; exact hD1, ?_⟩
  intro N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC cc w hw0 V W K hV hW hV0 hK hVr hWr hKr
    hVl hWl hKl hVm hWm hKo
  set r := 1 / D with hrdef
  have hr0 : 0 ≤ r := (one_div_pos.2 hD0).le
  have hrle : r ≤ 1 / D := le_rfl
  have item : ∀ x : ℝ, 0 ≤ x → x ≤ D → x * r ≤ 1 := fun x hx hxD =>
    Step2.le_one_of_le_div hx hD0 hrle hxD
  have t1 : 0 ≤ 2 * (2 * Q + cTN d L) * (L : ℝ) ^ d := by positivity
  have t3 : 0 ≤ 2 * A ^ 2 ^ d := by positivity
  have t4 : 0 ≤ (8 * Q + 2 * cTN d L) * Ar := by positivity
  have t5 : 0 ≤ (Ar * P') ^ 2 ^ d * Bc := by positivity
  have hr4 : 4 * r ≤ 1 := item 4 (by norm_num) (by rw [hD]; linarith only [hcT, t1, t3, t4, t5])
  have hr1 : r ≤ 1 := by linarith only [hr4]
  have hT : cTN d L * r ≤ 1 := item _ hcT (by rw [hD]; linarith only [hcT, t1, t3, t4, t5])
  have hj : j < N := by omega
  have hw : w.Sub := by unfold Wt.Sub; rw [hw0]; exact zero_le
  have hVr' : ∀ b ∈ blockIdx (L := L) (N := N) j,
      Tj d (L : ℝ) j ℓ ((bulkF V b : EvR (Lam d L N)) : Alg d L N) ≤ ENNReal.ofReal r :=
    fun b hb => (le_iSup₂ (f := fun b (_ : b ∈ blockIdx (L := L) (N := N) j) =>
      Tj d (L : ℝ) j ℓ ((bulkF V b : EvR (Lam d L N)) : Alg d L N)) b hb).trans hVr
  have hWr' : ∀ b ∈ blockIdx (L := L) (N := N) j,
      Tj d (L : ℝ) j ℓ ((bulkF W b : EvR (Lam d L N)) : Alg d L N) ≤ ENNReal.ofReal r :=
    fun b hb => (le_iSup₂ (f := fun b (_ : b ∈ blockIdx (L := L) (N := N) j) =>
      Tj d (L : ℝ) j ℓ ((bulkF W b : EvR (Lam d L N)) : Alg d L N)) b hb).trans hWr
  have HB : Step2.LastN.BHN j ℓ ℓ' ℓC C (bulkF V) (bulkF W) (bulkF K) A r :=
    { hd := hd, hLp := hLp, hjN := hjN, hℓ := hℓ, hℓ' := hℓ', hℓC := hℓC,
      hsum := hsum, hC := hC, hV := hV, hW := hW, hV0 := hV0, hK := hK, hA := hA1, hr := hr0,
      hr1 := hr1, hVr := hVr', hWr := hWr', hKr := hKr }
  have H : BHFN j ℓ ℓ' ℓC C V W K w A r :=
    { hB := HB, hw := hw, hw0 := hw0, hVl := hVl, hWl := hWl, hKl := hKl, hVm := hVm,
      hWm := hWm, hKo := hKo }
  have hκ1 : 2 * r * A ^ 2 ^ d ≤ 1 := by
    have := item (2 * A ^ 2 ^ d) t3 (by rw [hD]; linarith only [hcT, t1, t3, t4, t5])
    linarith only [this, mul_comm r (2 * A ^ 2 ^ d)]
  have hδ1 : (8 * Q + 2 * cTN d L) * r * Ar ≤ 1 := by
    have := item ((8 * Q + 2 * cTN d L) * Ar) t4
      (by rw [hD]; linarith only [hcT, t1, t3, t4, t5])
    have e : (8 * Q + 2 * cTN d L) * r * Ar = (8 * Q + 2 * cTN d L) * Ar * r := by ring
    linarith only [this, e]
  have hDβ : (Ar * P') ^ 2 ^ d * ((1 + 2 ^ d * 0) * (2 * r * A ^ 2 ^ d) +
      (8 * Q + 2 * cTN d L) * r * Ar) ≤ 1 := by
    have e : (Ar * P') ^ 2 ^ d * ((1 + 2 ^ d * 0) * (2 * r * A ^ 2 ^ d) +
        (8 * Q + 2 * cTN d L) * r * Ar) = ((Ar * P') ^ 2 ^ d * Bc) * r := by rw [hBc]; ring
    rw [e]; exact item _ t5 (by rw [hD]; linarith only [hcT, t1, t3, t4, t5])
  have hpr : (2 * Q + cTN d L) * r * (L : ℝ) ^ d ≤ 1 / 2 := by
    have := item (2 * (2 * Q + cTN d L) * (L : ℝ) ^ d) t1
      (by rw [hD]; linarith only [hcT, t1, t3, t4, t5])
    linarith only [this]
  have G := H.khyp hAQ hr4 hT hκ1 hδ1
  have hU : IsConn (j + 1) (univ : Finset (Lam d L N)) := by
    subst hjN; exact Step2.LastN.isConn_top
  have hUj : IsPolymer j (univ : Finset (Lam d L N)) := isPolymer_univ j
  have key := G.KnextG_le
    (oSN (nrmP_tNorm (E := Dir d) (p := pPhi d) (X := Lam d L N) (ℓ := ℓ') H.hh' H.hB.hℓ') w
      H.hw) H.hE (U := univ) hQ hη0.le
    (fun g _ => by
      refine (H.pref_full univ _).trans (ENNReal.ofReal_le_ofReal ?_)
      have hnb : (nb j (univ : Finset (Lam d L N)) : ℝ) ≤
          (L : ℝ) ^ d * nb (j + 1) (univ : Finset (Lam d L N)) := by
        exact_mod_cast nb_le_of_succ hU.1
      have hsum' : 2 * (Q * r) + cTN d L * r ≤ (2 * Q + cTN d L) * r := le_of_eq (by ring)
      have hpos : 0 ≤ 2 * (Q * r) + cTN d L * r := by positivity
      exact exp_pref_le hsum' hpos hnb hpr)
    (by
      refine (card_Gset_le (fun b hb => hc L N j b hb) hUj).trans ?_
      rw [hMdef, ← pow_mul]
      exact Nat.pow_le_pow_right (by norm_num) (by
        rw [mul_assoc]; exact Nat.mul_le_mul_left _ (nb_le_of_succ hU.1)))
    (fun g hg => nU_bound (fun X hX => (hcomb L hL1 N j X hj hX).1)
      (fun b hb => (isSmall_clo_nbhd hd hL2 hj b hb).2.2) hη0.le hg)
    hPdef hM1 hAP hDβ
  have hnb1 : nb (j + 1) (univ : Finset (Lam d L N)) = 1 := by
    subst hjN; exact Step2.LastN.nb_top
  rw [hnb1, pow_one, ← hArdef, hArQ] at key
  have hA1' : ENNReal.ofReal 1 ≤ ENNReal.ofReal A := ENNReal.ofReal_le_ofReal hA1
  calc oTj d L w (j + 1) ℓ' (KNO j C V W K univ : SA cc (Lam d L N))
      = ENNReal.ofReal 1 * oTj d L w (j + 1) ℓ' (KNO j C V W K univ : SA cc (Lam d L N)) := by
        rw [ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal A * oTj d L w (j + 1) ℓ' (KNO j C V W K univ : SA cc (Lam d L N)) :=
        mul_le_mul' hA1' le_rfl
    _ ≤ ENNReal.ofReal 1 := key

end

end Obs2
