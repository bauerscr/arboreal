import Obs2.Est.Step3O
import Obs2.Est.Step2OLU

/-!
# Block bounds in the full norm on the `σ_aσ_b` sector (`ab` copy of `Obs2.Est.Step3O`)

The block bounds of `Obs2.Est.Step3O` under `BHFU` (namespace `BHFU`): `pairO_full`, `FCLO_full`,
`DO_full`, `kapO_full`, `k2O_full`, `K2O_full`, `JhO_full`, `GpO_full`, `bpowO_GpO_sub_one`,
`ItO_full`. The proofs only use the `BHOU` observable block bounds, so they are verbatim.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD PolyAux ENNReal

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

namespace BHFU

variable {P : ObsPts d L N} {j : ℕ} {ℓ ℓ' ℓC : ℝ} {C : Matrix (Lam d L N) (Lam d L N) ℂ}
  {V W : OFam c d L N} {K : OAct c d L N} {w : Wt} {A r Cl cS Clo : ℝ}
  (H : BHFU P j ℓ ℓ' ℓC C V W K w A r Cl cS Clo)
include H

/-- The full norm at scale `j + 1` as an `SNorm`. -/
abbrev nS : Obs.Gen.SNorm (OE c (Lam d L N)) :=
  oSN (nrmP_tNorm (E := Dir d) (p := pPhi d) (X := Lam d L N) (ℓ := ℓ') H.hh' H.hO.hℓ') w H.hw

theorem nS_nrm (F : OE c (Lam d L N)) :
    H.nS.nrm F = oTj d L w (j + 1) ℓ' (F : SA c (Lam d L N)) := rfl

theorem nS_smul (z : ℂ) (F : OE c (Lam d L N)) :
    H.nS.nrm (z • F) = ENNReal.ofReal ‖z‖ * H.nS.nrm F :=
  oT_smul (E := Dir d) (p := pPhi d) (h := (L : ℝ) ^ (j + 1)) (ℓ := ℓ') (w := w) z
    (F : SA c (Lam d L N))

/-- The pair constant `q = 2 (Q₁ r)² + 4 Q₁² r²`. -/
abbrev qP (d : ℕ) (r : ℝ) : ℝ := 2 * (Step2.Q1 d * r) ^ 2 + 4 * Step2.Q1 d ^ 2 * (r * r)

theorem hqP : 0 ≤ qP d r := by have := H.hr; positivity

theorem pairO_full {b b' : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j)
    (hb' : b' ∈ blockIdx (L := L) (N := N) j) :
    H.nS.nrm (FCO C (VprO C V b) (VprO C V b')) ≤ ENNReal.ofReal (qP d r) := by
  have hr := H.hr
  refine H.full_le (by positivity) (by positivity) ?_ (H.hO.pair_o hb hb')
  exact H.hB.FCE_pair_le' hr H.hB.hVr hb hb'

theorem FCL_bulk {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    Tj d (L : ℝ) (j + 1) ℓ' (FCO C (VprO C V b) (VprLO j C V) : SA c (Lam d L N)).e ≤
      ENNReal.ofReal (Step2.cNear d L * (2 * (Step2.Q1 d * r) ^ 2)) := by
  have hr := H.hr
  have eb : bulk (FCO C (VprO C V b) (VprLO j C V)) =
      FCE C (Vpr C (bulkF V) b) (VprL j C (bulkF V)) := by
    rw [bulk_FCO, bulk_VprO, bulk_VprLO]
  rw [← coe_bulk, eb, FCE_VprL_eq H.hB.hjN H.hB.hC H.hB.hV b]
  have hs := tn_sum_const (E := Dir d) (p := pPhi d) (h := (L : ℝ) ^ (j + 1)) (ℓ := ℓ')
    (nearSet (L := L) (N := N) j b) (fun b' => FCE C (Vpr C (bulkF V) b) (Vpr C (bulkF V) b'))
    (r := 2 * (Step2.Q1 d * r) ^ 2) (by positivity)
    (fun b' hb' => H.hB.FCE_pair_le' hr H.hB.hVr hb (mem_filter.1 hb').1)
  have hn : ((nearSet (L := L) (N := N) j b).card : ℝ) ≤ Step2.cNear d L := by
    unfold Step2.cNear; exact_mod_cast card_nearSet_le H.hB.hj.le b hb
  exact hs.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hn (by positivity)))

/-- The sharp second-order part in the full norm. -/
theorem SFO_full {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    H.nS.nrm (SFO j C V b) ≤ ENNReal.ofReal (Step2.cNear d L * qP d r) := by
  have hr := H.hr
  have hN := H.hB.hcNear
  have e : Step2.cNear d L * qP d r = Step2.cNear d L * (2 * (Step2.Q1 d * r) ^ 2) +
      Step2.cNear d L * (2 * Step2.Q1 d ^ 2 * (r * r)) + Step2.cNear d L * (2 * Step2.Q1 d ^ 2 *
        (r * r)) := by ring
  refine (H.full_le (a := Step2.cNear d L * (2 * (Step2.Q1 d * r) ^ 2))
    (b := Step2.cNear d L * (2 * Step2.Q1 d ^ 2 * (r * r))) (by positivity) (by positivity) ?_
    (H.hO.SF_o hb)).trans
    (ENNReal.ofReal_le_ofReal (by rw [e]; linarith [show 0 ≤ Step2.cNear d L * (2 *
      Step2.Q1 d ^ 2 * (r * r)) by positivity]))
  rw [SFO_e, ← FCO_e, Tj_smul']
  have h12 : ‖(1 / 2 : ℂ)‖ ≤ 1 := by norm_num
  refine (mul_le_mul_right' (ENNReal.ofReal_le_ofReal h12) _).trans ?_
  rw [ENNReal.ofReal_one, one_mul]
  exact H.FCL_bulk hb

/-- The single-block part of `k^{(2)}`: `‖½F(V'_B, V'_B) − S^{(2)}(B)‖ ≤ (c_near + 1) q`. -/
theorem k2one_full {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    H.nS.nrm ((1 / 2 : ℂ) • FCO C (VprO C V b) (VprO C V b) - SFO j C V b) ≤
      ENNReal.ofReal ((Step2.cNear d L + 1) * qP d r) := by
  have hN := H.hB.hcNear
  have hq := H.hqP
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  have h1 : H.nS.nrm ((1 / 2 : ℂ) • FCO C (VprO C V b) (VprO C V b)) ≤
      ENNReal.ofReal (1 / 2 * qP d r) := by
    rw [H.nS_smul, hhalf, ENNReal.ofReal_mul (by norm_num)]
    exact mul_le_mul_left' (H.pairO_full hb hb) _
  refine (H.nS.subR (by positivity) (by positivity) h1 (H.SFO_full hb)).trans
    (ENNReal.ofReal_le_ofReal (by nlinarith))

theorem GO_full {b b' : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j)
    (hb' : b' ∈ blockIdx (L := L) (N := N) j) :
    H.nS.nrm (GO C V b b') ≤ ENNReal.ofReal (qP d r) := by
  have hr := H.hr
  refine (H.full_le (a := 0) le_rfl (by positivity) ?_ (H.hO.pairG_o hb hb')).trans
    (ENNReal.ofReal_le_ofReal (by unfold qP; nlinarith [sq_nonneg (Step2.Q1 d * r)]))
  rw [← coe_bulk, bulk_GO]
  simp only [ZeroMemClass.coe_zero, ENNReal.ofReal_zero, nonpos_iff_eq_zero]
  exact tNorm_zero'

theorem kapO_full (X : Finset (Lam d L N)) (c' : Fin d → ℕ) :
    H.nS.nrm (kapO j C V X c') ≤ ENNReal.ofReal ((Step2.cNear d L + 2) * qP d r) := by
  classical
  have hN := H.hB.hcNear
  have hq := H.hqP
  have hb : ∀ b ∈ blocks j X, b ∈ blockIdx (L := L) (N := N) j :=
    fun b hb => mem_blockIdx_of_mem_blocks hb
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  have hhalf' : ‖-(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  unfold kapO
  split_ifs with h1 h2
  · have hc1 : (((blocks j X).filter (fun b => par L b = c')).card : ℝ) ≤ 1 := by
      have := card_le_card (filter_subset (fun b => par L b = c') (blocks j X))
      have h1' : (blocks j X).card = 1 := h1
      exact_mod_cast this.trans h1'.le
    refine (H.nS.sum_constR _ _ (r := (Step2.cNear d L + 1) * qP d r) (by positivity)
      fun b hbX => ?_).trans (ENNReal.ofReal_le_ofReal ?_)
    · rw [k2one_eq]; exact H.k2one_full (hb b (mem_filter.1 hbX).1)
    · have h0 : 0 ≤ (Step2.cNear d L + 1) * qP d r := by positivity
      nlinarith
  · have h2' : (blocks j X).card = 2 := h2
    have hc2 : (((blocks j X).filter (fun b => par L b = c')).card : ℝ) ≤ 2 := by
      have := card_le_card (filter_subset (fun b => par L b = c') (blocks j X))
      exact_mod_cast this.trans h2'.le
    rw [H.nS_smul, hhalf]
    have hs : H.nS.nrm (∑ b ∈ (blocks j X).filter (fun b => par L b = c'),
        ∑ b' ∈ (blocks j X).erase b, (FCO C (VprO C V b) (VprO C V b') + GO C V b b')) ≤
        ENNReal.ofReal (((blocks j X).filter (fun b => par L b = c')).card * (1 * (2 * qP d r))) := by
      refine H.nS.sum_constR _ _ (by positivity) fun b hbX => ?_
      have hbX' := (mem_filter.1 hbX).1
      have := H.nS.sum_constR ((blocks j X).erase b)
        (fun b' => FCO C (VprO C V b) (VprO C V b') + GO C V b b') (by positivity)
        (fun b' hb' => (H.nS.addR hq hq (H.pairO_full (hb b hbX') (hb b' (mem_of_mem_erase hb')))
          (H.GO_full (hb b hbX') (hb b' (mem_of_mem_erase hb')))).trans
          (ENNReal.ofReal_le_ofReal (le_of_eq (two_mul _).symm)))
      rw [card_erase_of_mem hbX', h2'] at this
      simpa using this
    refine (mul_le_mul_left' hs _).trans ?_
    rw [← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h0 : 0 ≤ qP d r := hq
    nlinarith
  · rw [H.nS.zero]; exact zero_le

theorem k2O_full (X : Finset (Lam d L N)) :
    H.nS.nrm (k2O j C V X) ≤ ENNReal.ofReal ((Step2.cNear d L + 2) * qP d r) := by
  classical
  have hN := H.hB.hcNear
  have hq := H.hqP
  have hb : ∀ b ∈ blocks j X, b ∈ blockIdx (L := L) (N := N) j :=
    fun b hb => mem_blockIdx_of_mem_blocks hb
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  have hhalf' : ‖-(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  unfold k2O
  split_ifs with h1 h2
  · have h1' : ((blocks j X).card : ℝ) = 1 := by exact_mod_cast h1
    refine (H.nS.sum_constR _ _ (r := (Step2.cNear d L + 1) * qP d r) (by positivity)
      fun b hbX => ?_).trans (ENNReal.ofReal_le_ofReal ?_)
    · rw [k2one_eq]; exact H.k2one_full (hb b hbX)
    · rw [h1']
      have h0 : 0 ≤ (Step2.cNear d L + 1) * qP d r := by positivity
      nlinarith
  · have h2' : (blocks j X).card = 2 := h2
    rw [H.nS_smul, hhalf]
    have hs : H.nS.nrm (∑ b ∈ blocks j X, ∑ b' ∈ (blocks j X).erase b,
        FCO C (VprO C V b) (VprO C V b')) ≤
        ENNReal.ofReal ((blocks j X).card * (1 * qP d r)) := by
      refine H.nS.sum_constR _ _ (by positivity) fun b hbX => ?_
      have := H.nS.sum_constR ((blocks j X).erase b) (fun b' => FCO C (VprO C V b) (VprO C V b'))
        hq (fun b' hb' => H.pairO_full (hb b hbX) (hb b' (mem_of_mem_erase hb')))
      rw [card_erase_of_mem hbX, h2'] at this
      simpa using this
    refine (mul_le_mul_left' hs _).trans ?_
    rw [← ENNReal.ofReal_mul (by norm_num), h2']
    refine ENNReal.ofReal_le_ofReal ?_
    have h0 : 0 ≤ qP d r := hq
    push_cast
    nlinarith
  · rw [H.nS.zero]; exact zero_le

theorem K2O_full {U : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U) :
    H.nS.nrm (K2O j C V U) ≤
      ENNReal.ofReal (2 ^ nb j U * ((Step2.cNear d L + 2) * qP d r)) := by
  classical
  have hN := H.hB.hcNear
  have hq := H.hqP
  unfold K2O
  refine (H.nS.sum_constR _ _ (by positivity) fun X _ => H.k2O_full X).trans
    (ENNReal.ofReal_le_ofReal ?_)
  exact mul_le_mul_of_nonneg_right (card_K2_filter_le j hU) (by positivity)

theorem JhO_full (c' : Fin d → ℕ) {U : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U) :
    H.nS.nrm (JhO j C V c' U) ≤
      ENNReal.ofReal (2 ^ nb j U * ((Step2.cNear d L + 2) * qP d r)) := by
  classical
  have hN := H.hB.hcNear
  have hq := H.hqP
  unfold JhO
  split_ifs
  · refine (H.nS.sum_constR _ _ (by positivity) fun X _ => H.kapO_full X c').trans
      (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (card_K2_filter_le j hU) (by positivity)
  · rw [H.nS.zero]; exact zero_le

/-- The exponent `t_G` of `‖Ĩ_{j+1}(B) - 1‖`. -/
abbrev tG (d L : ℕ) (r Cl Clo cS : ℝ) : ℝ :=
  (2 * (Step2.cUblk d L Cl cS * r) + 2 * uoB d L r Clo cS) + (Step2.cWblk d L Cl * r + woB d L r Clo)

theorem htG : 0 ≤ tG d L r Cl Clo cS := by
  have h0 := mul_nonneg H.hB.hcU H.hr
  have h0' := mul_nonneg H.hB.hcW H.hr
  have := H.huo; have := H.hwo
  unfold tG; positivity

theorem GpO_full {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    H.nS.nrm (GpO P j C V W K b) ≤ ENNReal.ofReal (Real.exp (tG d L r Cl Clo cS)) :=
  oT_le_exp_of_sub_one H.hh' H.hO.hℓ' H.htG (H.GpO_sub_one_full hb)

theorem bpowO_GpO_sub_one (U : Finset (Lam d L N)) :
    H.nS.nrm (bpowO j (GpO P j C V W K) U - 1) ≤
      ENNReal.ofReal (Real.exp (nb j U * tG d L r Cl Clo cS) - 1) := by
  have h := snorm_prod_sub_one_exp H.nS (blocks j U) (GpO P j C V W K)
    (fun _ => tG d L r Cl Clo cS) (fun _ _ => H.htG)
    (fun b hb => H.GpO_sub_one_full (mem_blockIdx_of_mem_blocks hb))
  rw [sum_const, nsmul_eq_mul] at h
  exact h

theorem ItO_full (c' : Fin d → ℕ) :
    H.nS.nrm (ItO P j C V W K c') ≤
      ENNReal.ofReal (Real.exp ((L : ℝ) ^ d * tG d L r Cl Clo cS)) := by
  have h := H.nS.prodR (blocks j (blockSet (L := L) (N := N) (j + 1) c')) (GpO P j C V W K)
    (fun _ => Real.exp (tG d L r Cl Clo cS)) (fun _ _ => (Real.exp_pos _).le)
    (fun b hb => H.GpO_full (mem_blockIdx_of_mem_blocks hb))
  rw [prod_const, ← Real.exp_nat_mul] at h
  refine h.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
  have hn : ((blocks j (blockSet (L := L) (N := N) (j + 1) c')).card : ℝ) ≤ (L : ℝ) ^ d := by
    exact_mod_cast nb_blockSet_succ_le j c'
  exact mul_le_mul_of_nonneg_right hn H.htG

theorem tG_le : tG d L r Cl Clo cS ≤
    (2 * Step2.cUblk d L Cl cS + 2 * cUo d L Clo cS + Step2.cWblk d L Cl + cWo d L Clo) * r := by
  have := H.uo_le; have := H.wo_le
  unfold tG; nlinarith

end BHFU

end

end Obs2
