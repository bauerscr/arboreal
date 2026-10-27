import Obs2.Est.LastKO2
import Obs2.Est.Step2O
import PtCorr2.Obs.ObsInit
import Obs2.Flow.EstMu

/-!
# The `σ_a` component of the reference activity of the last step

For the reference map of `Obs2.Est.LastKO1` at `j + 1 = N` (no localisation):

* **`KNO_a_zero`**: with vanishing bulk inputs and `K = 0` the `σ_a` component of `K'(Λ)`
  vanishes (the observable inputs enter `𝔼θZ` and `∏_BG'(B)` in the same way to first order);
* **`KNO_a_le`** (one-parameter Cauchy estimate): if the bulk sizes are `≤ τ`, the observable
  block sizes (weight `w_a = 1`) are `≤ M`, and the weighted observable activity is `≤ τM/r₀`,
  `τ ≤ r₀` (`r₀` the radius of `KNO_crude_ts`), then

    `‖K'(Λ)_a‖_{T_N(ℓ')} ≤ τ M / r₀²`.

  Proof: the family `t ↦ (tV^∅ + V^{obs}, tW^∅ + W^{obs}, tK)`; at `t = 0` the `σ_a` part
  vanishes; on `|t| ≤ r₀/τ` the crude bound with the weight `w_a = r₀/M` gives
  `‖K'_a‖ ≤ M/r₀`; Schwarz.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Obs.Gen ENNReal

variable {L N : ℕ} [NeZero L] {c : Obs.Case}

/-! ### Products of elements with unit bulk -/

section Unit

theorem unit_mul {F G : OE c (Lam 2 L N)} (hF : (F : SA c (Lam 2 L N)).e = 1)
    (hG : (G : SA c (Lam 2 L N)).e = 1) :
    ((F * G : OE c (Lam 2 L N)) : SA c (Lam 2 L N)).e = 1 ∧
      ((F * G : OE c (Lam 2 L N)) : SA c (Lam 2 L N)).a =
        (F : SA c (Lam 2 L N)).a + (G : SA c (Lam 2 L N)).a := by
  rw [OE.mul_a, OE.mul_e, hF, hG]
  exact ⟨one_mul _, by rw [one_mul, mul_one, add_comm]⟩

theorem unit_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (F : ι → OE c (Lam 2 L N))
    (h : ∀ i ∈ s, (F i : SA c (Lam 2 L N)).e = 1) :
    ((∏ i ∈ s, F i : OE c (Lam 2 L N)) : SA c (Lam 2 L N)).e = 1 ∧
      ((∏ i ∈ s, F i : OE c (Lam 2 L N)) : SA c (Lam 2 L N)).a =
        ∑ i ∈ s, (F i : SA c (Lam 2 L N)).a := by
  induction s using Finset.induction_on with
  | empty => exact ⟨rfl, rfl⟩
  | insert i s hi ih =>
    obtain ⟨h1, h2⟩ := ih fun k hk => h k (mem_insert_of_mem hk)
    obtain ⟨h3, h4⟩ := unit_mul (h i (mem_insert_self i s)) h1
    rw [prod_insert hi, sum_insert hi]
    exact ⟨h3, by rw [h4, h2]⟩

theorem oexp_unit {F : OE c (Lam 2 L N)} (hF : bulk F = 0) :
    ((oexp F : OE c (Lam 2 L N)) : SA c (Lam 2 L N)).e = 1 ∧
      ((oexp F : OE c (Lam 2 L N)) : SA c (Lam 2 L N)).a = (F : SA c (Lam 2 L N)).a :=
  ⟨oexp_obs_e hF, oexp_obs_a hF⟩

end Unit

/-! ### The reference activity at vanishing bulk inputs -/

section Zero

variable (j : ℕ) (C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ) (V W : OFam c 2 L N)

theorem EthE_zero' (C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ) : EthE C (0 : EvR (Lam 2 L N)) = 0 :=
  Subtype.ext (by rw [coe_EthE, ZeroMemClass.coe_zero, map_zero])

set_option maxHeartbeats 1000000 in
/-- **At vanishing bulk inputs and `K = 0`, `K'(Λ)_a = 0`.** -/
theorem KNO_ea_zero (hj : j + 1 = N) (hV : ∀ b, bulk (V b) = 0) (hW : ∀ b, bulk (W b) = 0) :
    ((KNO j C V W 0 univ : OE c (Lam 2 L N)) : SA c (Lam 2 L N)).e = 0 ∧
      ((KNO j C V W 0 univ : OE c (Lam 2 L N)) : SA c (Lam 2 L N)).a = 0 := by
  classical
  have hVe : ∀ b, (V b : SA c (Lam 2 L N)).e = 0 := fun b => e_eq_zero_of_bulk (hV b)
  have hWe : ∀ b, (W b : SA c (Lam 2 L N)).e = 0 := fun b => e_eq_zero_of_bulk (hW b)
  have hVp : ∀ b, bulk (VprO C V b) = 0 := fun b => by
    rw [bulk_VprO]; show EthE C (bulk (V b)) = 0; rw [hV, EthE_zero']
  have hVL : bulk (VprLO j C V) = 0 := by
    rw [VprLO, map_sum]; exact sum_eq_zero fun b _ => hVp b
  have hup : ∀ b, upBN C V b = 0 := fun b => by
    rw [upBN, hVp]; simp
  -- the block factors
  set Pr := bpowO j (GpN j C V W) univ
  have hY : ∀ b, bulk (YpN C V b) = 0 := fun b => by
    rw [YpN, map_sub, map_sub, hVp, bulk_upON, hup]; simp
  have hS : ∀ b, bulk (SbO j C V W b) = 0 := fun b => by
    rw [bulk_SbO, Step2.Sb]
    have h1 : Step2.Vpr C (bulkF V) b = 0 := hVp b
    have h2 : Step2.VprL j C (bulkF V) = 0 := by rw [← bulk_VprLO]; exact hVL
    have h3 : Step2.EthE C (bulkF W b) = 0 := by
      show EthE C (bulk (W b)) = 0; rw [hW, EthE_zero']
    rw [h1, h2, h3, add_zero]
    refine Subtype.ext ?_
    rw [Subalgebra.coe_smul, coe_FCE, ZeroMemClass.coe_zero, FC_zero_left, smul_zero]
  have hSa : ∀ b, (SbO j C V W b : SA c (Lam 2 L N)).a = (EthO C (W b) : SA c (Lam 2 L N)).a :=
    fun b => by
      have h1 := SFO_cmp j C V true b
      rw [cmp_true, cmp_true] at h1
      have h2 : (VprLO j C V : SA c (Lam 2 L N)).e = 0 := e_eq_zero_of_bulk hVL
      rw [h2, FC_zero_right] at h1
      rw [SbO, Subalgebra.coe_add, SA.add_a, h1, zero_add]
  have hG : ∀ b, (GpN j C V W b : SA c (Lam 2 L N)).e = 1 ∧
      (GpN j C V W b : SA c (Lam 2 L N)).a =
        -(EthO C (V b) : SA c (Lam 2 L N)).a + (upON C V b : SA c (Lam 2 L N)).a +
          (EthO C (W b) : SA c (Lam 2 L N)).a := fun b => by
    have hYn : bulk (-YpN C V b) = 0 := by rw [map_neg, hY, neg_zero]
    obtain ⟨e1, a1⟩ := oexp_unit hYn
    have e2 : ((1 + SbO j C V W b : OE c (Lam 2 L N)) : SA c (Lam 2 L N)).e = 1 := by
      rw [Subalgebra.coe_add, SA.add_e, e_eq_zero_of_bulk (hS b), add_zero]; rfl
    obtain ⟨e3, a3⟩ := unit_mul e1 e2
    refine ⟨e3, ?_⟩
    rw [GpN, a3, a1, Subalgebra.coe_add, SA.add_a, hSa b]
    have ha1 : ((1 : OE c (Lam 2 L N)) : SA c (Lam 2 L N)).a = 0 := rfl
    rw [ha1, zero_add, NegMemClass.coe_neg, SA.neg_a, YpN]
    have hal : ((algebraMap ℂ (OE c (Lam 2 L N)) (upBN C V b) : OE c (Lam 2 L N)) :
        SA c (Lam 2 L N)).a = 0 := by
      rw [hup b, map_zero]; rfl
    simp only [Subalgebra.coe_sub, SA.sub_a, hal, sub_zero, VprO]
    abel
  obtain ⟨hPe, hPa⟩ := unit_prod (blocks (L := L) (N := N) j univ) (GpN j C V W)
    fun b _ => (hG b).1
  -- the expectation of `Z`
  set E := ECCO C (thetaO (gZO j (IbO V W) (0 : OAct c 2 L N)))
  have hI : ∀ b, (IbO V W b : SA c (Lam 2 L N)).e = 1 ∧
      (IbO V W b : SA c (Lam 2 L N)).a = -(V b : SA c (Lam 2 L N)).a + (W b : SA c (Lam 2 L N)).a :=
    fun b => by
      have hn : bulk (-V b) = 0 := by rw [map_neg, hV, neg_zero]
      obtain ⟨e1, a1⟩ := oexp_unit hn
      have e2 : ((1 + W b : OE c (Lam 2 L N)) : SA c (Lam 2 L N)).e = 1 := by
        rw [Subalgebra.coe_add, SA.add_e, hWe, add_zero]; rfl
      obtain ⟨e3, a3⟩ := unit_mul e1 e2
      refine ⟨e3, ?_⟩
      rw [IbO, a3, a1, Subalgebra.coe_add, SA.add_a, NegMemClass.coe_neg, SA.neg_a]
      have ha1 : ((1 : OE c (Lam 2 L N)) : SA c (Lam 2 L N)).a = 0 := rfl
      rw [ha1, zero_add]
  obtain ⟨hZe, hZa⟩ := unit_prod (blocks (L := L) (N := N) j univ) (IbO V W)
    fun b _ => (hI b).1
  have hEe : (E : SA c (Lam 2 L N)).e = 1 := by
    show (EthO C (gZO j (IbO V W) 0) : SA c (Lam 2 L N)).e = 1
    have hb : bpowO j (IbO V W) univ = ∏ b ∈ blocks (L := L) (N := N) j univ, IbO V W b := rfl
    rw [EthO_e, gZO_zeroK, hb, hZe, map_one, ECC_one]
  have hEa : (E : SA c (Lam 2 L N)).a =
      ∑ b ∈ blocks (L := L) (N := N) j univ, (-(EthO C (V b) : SA c (Lam 2 L N)).a + (EthO C (W b) : SA c (Lam 2 L N)).a) := by
    show (EthO C (gZO j (IbO V W) 0) : SA c (Lam 2 L N)).a = _
    have hb : bpowO j (IbO V W) univ = ∏ b ∈ blocks (L := L) (N := N) j univ, IbO V W b := rfl
    rw [EthO_a, gZO_zeroK, hb, hZa, map_sum, map_sum]
    refine sum_congr rfl fun b _ => ?_
    rw [(hI b).2, map_add, map_add, map_neg, map_neg, EthO_a, EthO_a]
  -- the constant
  have hu0 : uXBN j C V univ = 0 := sum_eq_zero fun b _ => hup b
  have hUe : ((expU (uXBN j C V univ) (uXON j C V univ) : OE c (Lam 2 L N)) :
      SA c (Lam 2 L N)).e = 1 ∧
      ((expU (uXBN j C V univ) (uXON j C V univ) : OE c (Lam 2 L N)) : SA c (Lam 2 L N)).a =
        ∑ b ∈ blocks (L := L) (N := N) j univ, (upON C V b : SA c (Lam 2 L N)).a := by
    rw [hu0, expU, Complex.exp_zero, one_smul]
    obtain ⟨e1, a1⟩ := oexp_unit (bulk_uXON j C V univ)
    refine ⟨e1, ?_⟩
    rw [a1, uXON, AddSubmonoidClass.coe_finsetSum, sum_a]
  -- the identity
  have hZVK : E = expU (-uXBN j C V univ) (-uXON j C V univ) * (Pr + KNO j C V W 0 univ) :=
    stepN_ZVK_last j C V W (0 : OAct c 2 L N) hj
  have hK : KNO j C V W 0 univ = expU (uXBN j C V univ) (uXON j C V univ) * E - Pr := by
    rw [hZVK, ← mul_assoc, expU_mul_expU_neg _ (bulk_uXON j C V univ), one_mul]
    ring
  have hb : bpowO j (GpN j C V W) univ = ∏ b ∈ blocks (L := L) (N := N) j univ, GpN j C V W b := rfl
  rw [hK, Subalgebra.coe_sub]
  constructor
  · show _ - ((bpowO j (GpN j C V W) univ : OE c (Lam 2 L N)) : SA c (Lam 2 L N)).e = 0
    rw [(unit_mul hUe.1 hEe).1, hb, hPe, sub_self]
  rw [SA.sub_a, (unit_mul hUe.1 hEe).2, hUe.2, hEa]
  show _ - ((bpowO j (GpN j C V W) univ : OE c (Lam 2 L N)) : SA c (Lam 2 L N)).a = 0
  rw [hb, hPa, ← sum_add_distrib, sub_eq_zero]
  refine sum_congr rfl fun b _ => ?_
  rw [(hG b).2]
  abel

end Zero

/-! ### The Cauchy estimate -/

section Cauchy

/-- The weight `(λ, 0, 0)`. -/
def wLam (lam : ℝ) : Wt := ⟨ENNReal.ofReal lam, 0, 0⟩

theorem oTo_wLam {c : Obs.Case} (lam : ℝ) (j : ℕ) (ℓ : ℝ) (F : OE c (Lam 2 L N)) :
    oTo (wLam lam) j ℓ F = ENNReal.ofReal lam * Tj 2 (L : ℝ) j ℓ (F : SA c (Lam 2 L N)).a := by
  simp only [oTo, oTj, oNorm, coe_πobs, piobs_apply, wLam]
  rw [show Tj 2 (L : ℝ) j ℓ (0 : Alg 2 L N) = 0 from tNorm_zero']; simp

/-- The bulk-scaled family `t ↦ tF^∅ + F^{obs}`. -/
def scB (t : ℂ) (F : OE c (Lam 2 L N)) : OE c (Lam 2 L N) := t • (F - πobs F) + πobs F

theorem bulk_scB (t : ℂ) (F : OE c (Lam 2 L N)) : bulk (scB t F) = t • bulk F := by
  rw [scB, map_add, map_smul, map_sub, bulk_πobs, sub_zero, add_zero]

theorem scB_a (t : ℂ) (F : OE c (Lam 2 L N)) :
    ((scB t F : OE c (Lam 2 L N)) : SA c (Lam 2 L N)).a = (F : SA c (Lam 2 L N)).a := by
  simp [scB, coe_πobs, piobs_apply]

theorem scB_one (F : OE c (Lam 2 L N)) : scB 1 F = F := by rw [scB, one_smul]; abel

theorem scB_cmp {S : Set (Lam 2 L N)} (t : ℂ) {F : OE c (Lam 2 L N)}
    (hF : CmpIn S (F : SA c (Lam 2 L N))) : CmpIn S ((scB t F : OE c (Lam 2 L N)) : SA c (Lam 2 L N)) := by
  rw [scB]
  exact (CmpIn.smul t (hF.sub hF.πobs)).add hF.πobs

theorem oTo_scB (lam : ℝ) (t : ℂ) (j : ℕ) (ℓ : ℝ) (F : OE .two (Lam 2 L N)) :
    oTo (wLam lam) j ℓ (scB t F) = ENNReal.ofReal lam * oTo Obs2.wA j ℓ F := by
  rw [oTo_wLam, Obs2.oTo_wA, scB_a]

set_option maxHeartbeats 2000000 in
/-- **The `σ_a` component of the reference activity of the last step** (Cauchy estimate in the
bulk scale): `‖K'(Λ)_a‖_{T_N(ℓ')} ≤ τM/r₀²`. -/
theorem KNO_a_le : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 ∧
    ∀ (N j : ℕ), j + 1 = N → ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ →
    ∀ C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ, Step2.GoodCov2 j ℓC C →
    ∀ (V W : OFam .two 2 L N) (K : OAct .two 2 L N),
      Step2.InF j (bulkF V) → Step2.InF j (bulkF W) →
      (∀ b, ε ((bulkF V b : EvR (Lam 2 L N)) : Alg 2 L N) = 0) → Step2.InK2 j (bulkF K) →
      (∀ b, CmpIn (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam 2 L N))
        (V b : SA .two (Lam 2 L N))) →
      (∀ b, CmpIn (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam 2 L N))
        (W b : SA .two (Lam 2 L N))) →
      (∀ X, IsConn j X → CmpIn (nbhd j X : Set (Lam 2 L N)) (K X : SA .two (Lam 2 L N))) →
      ∀ τ M : ℝ, 0 < τ → τ ≤ r₀ → 0 < M →
      Step2.Fnorm j ℓ (bulkF V) ≤ ENNReal.ofReal τ →
      Step2.Fnorm j ℓ (bulkF W) ≤ ENNReal.ofReal τ →
      Knorm j ℓ A (bulkF K) ≤ ENNReal.ofReal τ →
      (∀ b ∈ blockIdx (L := L) (N := N) j, oTo Obs2.wA j ℓ (V b) ≤ ENNReal.ofReal M) →
      (∀ b ∈ blockIdx (L := L) (N := N) j, oTo Obs2.wA j ℓ (W b) ≤ ENNReal.ofReal M) →
      (∀ X, IsConn j X → ENNReal.ofReal (A ^ (nb j X - 2 ^ 2)) * oTo Obs2.wA j ℓ (K X) ≤
        ENNReal.ofReal (τ * M / r₀)) →
        Tj 2 (L : ℝ) (j + 1) ℓ' (KNO j C V W K univ : SA .two (Lam 2 L N)).a ≤
          ENNReal.ofReal (τ * M / r₀ ^ 2) ∧
        Tj 2 (L : ℝ) (j + 1) ℓ' (KNO j C V W K univ : SA .two (Lam 2 L N)).e ≤
          ENNReal.ofReal (τ / r₀) := by
  obtain ⟨L₀, h0⟩ := KNO_crude_ts 2 (by norm_num)
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨A₀, hA₀, h1⟩ := h0 L hL
  refine ⟨A₀, hA₀, fun A hA => ?_⟩
  obtain ⟨r₀, hr₀, hr₀1, hcr⟩ := h1 A hA
  refine ⟨r₀, hr₀, hr₀1, ?_⟩
  intro N j hj ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC V W K hV hW hV0 hK hVl hWl hKl τ M hτ hτr hM
    hVb hWb hKb hVo hWo hKo
  set lam : ℝ := r₀ / M with hlam
  have hlam0 : 0 < lam := div_pos hr₀ hM
  set R : ℝ := r₀ / τ with hR
  have hR1 : 1 ≤ R := by rw [hR, le_div_iff₀ hτ, one_mul]; exact hτr
  have hR0 : 0 < R := by linarith
  -- the family
  set Vt : ℂ → OFam .two 2 L N := fun t b => scB t (V b) with hVt
  set Wt : ℂ → OFam .two 2 L N := fun t b => scB t (W b) with hWt
  set Kt : ℂ → OAct .two 2 L N := fun t X => t • K X with hKt
  set F : ℂ → OE .two (Lam 2 L N) := fun t => KNO j C (Vt t) (Wt t) (Kt t) univ with hF
  have hbV : ∀ t, bulkF (Vt t) = fun b => t • bulkF V b := fun t => funext fun b => bulk_scB t _
  have hbW : ∀ t, bulkF (Wt t) = fun b => t • bulkF W b := fun t => funext fun b => bulk_scB t _
  have hbK : ∀ t, bulkF (Kt t) = t • bulkF K := fun t => funext fun X => map_smul bulk t (K X)
  have hV0t : ∀ t b, ε ((Vt t b : SA .two (Lam 2 L N)).e) = 0 := fun t b => by
    rw [← coe_bulk]
    show ε ((bulkF (Vt t) b : EvR (Lam 2 L N)) : Alg 2 L N) = 0
    rw [hbV]
    simp only [Subalgebra.coe_smul, map_smul, hV0 b, smul_zero]
  have hol : HolW F := KNO_holW j C
    (fun b => (HolW.smul differentiable_id (HolW.const _)).add (HolW.const _))
    (fun b => (HolW.smul differentiable_id (HolW.const _)).add (HolW.const _))
    (fun X => HolW.smul differentiable_id (HolW.const _)) hV0t univ
  -- the bound on the disc
  have hdisc2 : ∀ t : ℂ, ‖t‖ ≤ R →
      ENNReal.ofReal lam * Tj 2 (L : ℝ) (j + 1) ℓ' (F t : SA .two (Lam 2 L N)).a ≤
        ENNReal.ofReal 1 ∧
      Tj 2 (L : ℝ) (j + 1) ℓ' (F t : SA .two (Lam 2 L N)).e ≤ ENNReal.ofReal 1 := by
    intro t ht
    have htτ : ‖t‖ * τ ≤ r₀ := by
      calc ‖t‖ * τ ≤ R * τ := by gcongr
        _ = r₀ := by rw [hR]; field_simp
    have hFV : Step2.Fnorm j ℓ (bulkF (Vt t)) ≤ ENNReal.ofReal r₀ := by
      rw [hbV, Fnorm_smul]
      calc ENNReal.ofReal ‖t‖ * Step2.Fnorm j ℓ (bulkF V) ≤ ENNReal.ofReal ‖t‖ * ENNReal.ofReal τ :=
            by gcongr
        _ = ENNReal.ofReal (‖t‖ * τ) := (ENNReal.ofReal_mul (norm_nonneg _)).symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal htτ
    have hFW : Step2.Fnorm j ℓ (bulkF (Wt t)) ≤ ENNReal.ofReal r₀ := by
      rw [hbW, Fnorm_smul]
      calc ENNReal.ofReal ‖t‖ * Step2.Fnorm j ℓ (bulkF W) ≤ ENNReal.ofReal ‖t‖ * ENNReal.ofReal τ :=
            by gcongr
        _ = ENNReal.ofReal (‖t‖ * τ) := (ENNReal.ofReal_mul (norm_nonneg _)).symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal htτ
    have hFK : Knorm j ℓ A (bulkF (Kt t)) ≤ ENNReal.ofReal r₀ := by
      rw [hbK, Knorm_smul]
      calc ENNReal.ofReal ‖t‖ * Knorm j ℓ A (bulkF K) ≤ ENNReal.ofReal ‖t‖ * ENNReal.ofReal τ :=
            by gcongr
        _ = ENNReal.ofReal (‖t‖ * τ) := (ENNReal.ofReal_mul (norm_nonneg _)).symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal htτ
    have hlM : lam * M = r₀ := by rw [hlam]; field_simp
    have hOV : ∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo (wLam lam) j ℓ (Vt t b) ≤ ENNReal.ofReal r₀ := fun b hb => by
      show oTo (wLam lam) j ℓ (scB t (V b)) ≤ _
      rw [oTo_scB, ← hlM, ENNReal.ofReal_mul hlam0.le]
      exact mul_le_mul_right (hVo b hb) _
    have hOW : ∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo (wLam lam) j ℓ (Wt t b) ≤ ENNReal.ofReal r₀ := fun b hb => by
      show oTo (wLam lam) j ℓ (scB t (W b)) ≤ _
      rw [oTo_scB, ← hlM, ENNReal.ofReal_mul hlam0.le]
      exact mul_le_mul_right (hWo b hb) _
    have hOK : ∀ X, IsConn j X → ENNReal.ofReal (A ^ (nb j X - 2 ^ 2)) *
        oTo (wLam lam) j ℓ (Kt t X) ≤ ENNReal.ofReal r₀ := fun X hX => by
      show _ * oTo (wLam lam) j ℓ (t • K X) ≤ _
      rw [oTo_smul, oTo_wLam, ← Obs2.oTo_wA]
      have hk := hKo X hX
      have hm : ‖t‖ * lam * (τ * M / r₀) ≤ r₀ := by
        calc ‖t‖ * lam * (τ * M / r₀) ≤ R * lam * (τ * M / r₀) := by gcongr
          _ = r₀ := by rw [hR, hlam]; field_simp
      calc ENNReal.ofReal (A ^ (nb j X - 2 ^ 2)) * (ENNReal.ofReal ‖t‖ * (ENNReal.ofReal lam *
            oTo Obs2.wA j ℓ (K X)))
          = ENNReal.ofReal (‖t‖ * lam) * (ENNReal.ofReal (A ^ (nb j X - 2 ^ 2)) *
              oTo Obs2.wA j ℓ (K X)) := by
            rw [ENNReal.ofReal_mul (norm_nonneg _)]; ring
        _ ≤ ENNReal.ofReal (‖t‖ * lam) * ENNReal.ofReal (τ * M / r₀) := mul_le_mul' le_rfl hk
        _ = ENNReal.ofReal (‖t‖ * lam * (τ * M / r₀)) :=
            (ENNReal.ofReal_mul (by positivity)).symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal hm
    have hcr' := hcr N j hj ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC .two (wLam lam) rfl (Vt t) (Wt t) (Kt t)
      (by rw [hbV]; exact hV.smul t) (by rw [hbW]; exact hW.smul t)
      (fun b => by rw [hbV]; simp only [Subalgebra.coe_smul, map_smul, hV0 b, smul_zero])
      (by rw [hbK]; exact hK.smul t) hFV hFW hFK
      (fun b => scB_cmp t (hVl b)) (fun b => scB_cmp t (hWl b))
      (fun X hX => (hKl X hX).smul t) hOV hOW hOK
    refine ⟨le_trans ?_ hcr', le_trans ?_ hcr'⟩
    · rw [← oTo_wLam]
      exact oTo_le _ _ _ _
    · rw [oTj_eq_bulk_add]; exact le_self_add
  have hdisc := fun t ht => (hdisc2 t ht).1
  have hdisce := fun t ht => (hdisc2 t ht).2
  -- Schwarz
  have hF1 : F 1 = KNO j C V W K univ := by
    simp only [hF, hVt, hWt, hKt, scB_one, one_smul]
  have hF00 : (F 0 : SA .two (Lam 2 L N)).e = 0 ∧ (F 0 : SA .two (Lam 2 L N)).a = 0 := by
    have hK0 : Kt 0 = 0 := funext fun X => zero_smul _ _
    show ((KNO j C (Vt 0) (Wt 0) (Kt 0) univ : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).e = 0 ∧
      ((KNO j C (Vt 0) (Wt 0) (Kt 0) univ : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a = 0
    rw [hK0]
    exact KNO_ea_zero j C _ _ hj (fun b => by
      show bulk (scB 0 (V b)) = 0; rw [bulk_scB, zero_smul])
      (fun b => by show bulk (scB 0 (W b)) = 0; rw [bulk_scB, zero_smul])
  have hF0 := hF00.2
  have hF0e := hF00.1
  have hB : 0 ≤ τ * M / r₀ ^ 2 := by positivity
  have key := wT_le_of_pair (j := j + 1) (ℓ := ℓ') (x := (F 1 : SA .two (Lam 2 L N)).a)
    (m := 1) ENNReal.one_ne_top hB (fun g hg => by
      rw [ENNReal.toReal_one, one_mul]
      set φ : ℂ → ℂ := fun t => cpairL aL 1 g (F t) with hφ
      have hd0 : Differentiable ℂ φ := hol (cpairL aL 1 g)
      have hφn : ∀ t, ‖φ t‖ = ‖pair (F t : SA .two (Lam 2 L N)).a g‖ := fun t => by
        rw [hφ]; simp only; rw [norm_cpairL aL zero_le_one, one_mul]; rfl
      have h00 : φ 0 = 0 := by
        rw [← norm_eq_zero, hφn, hF0, show pair (0 : Alg 2 L N) g = 0 from map_zero (pairL g),
          norm_zero]
      obtain ⟨kk, hkk, e⟩ := Step2.OrdS.one_of_zero hd0 h00
      have hbd : ∀ ζ : ℂ, ‖ζ‖ = R → ‖φ ζ‖ ≤ 1 / lam := fun ζ hζ => by
        rw [hφn]
        have := pair_le_of_wT (m := ENNReal.ofReal lam) ENNReal.ofReal_ne_top zero_le_one
          (hdisc ζ hζ.le) hg
        rw [ENNReal.toReal_ofReal hlam0.le] at this
        rw [le_div_iff₀ hlam0, mul_comm]; exact this
      have hc := Step2.coeff_le hkk e hR0 hbd (z := 1) (by simp; exact hR1)
      have e1 : φ 1 = kk 1 := by simpa using e 1
      have hn1 := hφn 1
      rw [e1] at hn1
      rw [← hn1]
      refine hc.trans (le_of_eq ?_)
      rw [hR, hlam, pow_one]
      field_simp)
  rw [one_mul, hF1] at key
  have hBe : 0 ≤ τ / r₀ := by positivity
  have keye := wT_le_of_pair (j := j + 1) (ℓ := ℓ') (x := (F 1 : SA .two (Lam 2 L N)).e)
    (m := 1) ENNReal.one_ne_top hBe (fun g hg => by
      rw [ENNReal.toReal_one, one_mul]
      set φ : ℂ → ℂ := fun t => cpairL eL 1 g (F t) with hφ
      have hd0 : Differentiable ℂ φ := hol (cpairL eL 1 g)
      have hφn : ∀ t, ‖φ t‖ = ‖pair (F t : SA .two (Lam 2 L N)).e g‖ := fun t => by
        rw [hφ]; simp only; rw [norm_cpairL eL zero_le_one, one_mul]; rfl
      have h00 : φ 0 = 0 := by
        rw [← norm_eq_zero, hφn, hF0e, show pair (0 : Alg 2 L N) g = 0 from map_zero (pairL g),
          norm_zero]
      obtain ⟨kk, hkk, e⟩ := Step2.OrdS.one_of_zero hd0 h00
      have hbd : ∀ ζ : ℂ, ‖ζ‖ = R → ‖φ ζ‖ ≤ 1 := fun ζ hζ => by
        rw [hφn]
        have := pair_le_of_wT (m := 1) ENNReal.one_ne_top zero_le_one
          (by rw [one_mul]; exact hdisce ζ hζ.le) hg
        rw [ENNReal.toReal_one, one_mul] at this
        exact this
      have hc := Step2.coeff_le hkk e hR0 hbd (z := 1) (by simp; exact hR1)
      have e1 : φ 1 = kk 1 := by simpa using e 1
      have hn1 := hφn 1
      rw [e1] at hn1
      rw [← hn1]
      refine hc.trans (le_of_eq ?_)
      rw [hR, pow_one]
      field_simp)
  rw [one_mul, hF1] at keye
  exact ⟨key, keye⟩

end Cauchy

end

end PtCorr2
