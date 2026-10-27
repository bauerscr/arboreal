import Obs2.Est.BlockO3
import Obs2.Est.CrudeG
import Obs2.Est.KObs2

/-!
# The crude bound for the map with sources (`Knext2O_crude_ts`)

The analogue of `Step2.Knext2_crude_ts` on the algebra with sources, in the full norm with
single-source weights (`w_ab = 0`): if the bulk inputs obey the hypotheses of the bulk crude bound
at radius `r₀`, and the observable parts of `V(B)`, `𝒲(B)` and (with the weight
`A^{(|𝓑_j(X)| - 2^d)_+}`) of `K(X)` are `≤ r₀`, with the locality of all components, then

  `A^{(|𝓑_{j+1}(U)| - 2^d)_+} ‖K_{j+1}(U)‖_{T_{j+1}(ℓ')} ≤ 1`

for every connected `(j+1)`-polymer `U` (`Knext2O_crude_ts`). The proof: the map with sources is
the generic map `Obs.Gen.KnextG` (`Knext2O_eq_KnextG`), the block hypotheses `Obs.Gen.KHypG` hold
for the `SNorm`s with sources (`BHF.khyp`, from `Obs2.Est.BlockO2`, `Obs2.Est.BlockO3`), and the generic
crude bound `Obs.Gen.KHypG.KnextG_le` applies.

Constants: `c_s = 2 c_near Q₁² + Q₁` (`sO ≤ c_s r`), `c_u^{obs}`, `c_w^{obs}`, and
`c_T = 3c_U + c_W + 3c_u^{obs} + c_w^{obs}` with `t_I ≤ c_T r` (`BHF.tI_le`).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step FRD ENNReal

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

/-- `sO ≤ c_s r` for `r ≤ 1`. -/
def cSo (d L : ℕ) : ℝ := 2 * Step2.cNear d L * Step2.Q1 d ^ 2 + Step2.Q1 d

/-- `u^{obs} ≤ c_u^{obs} r`. -/
def cUo (d L : ℕ) (Clo cS : ℝ) : ℝ :=
  Step2.Q1 d + Step2.Q1 d * Step2.pq d ^ 2 * (cS * Clo) + Clo * ((L : ℝ) ^ d * cSo d L)

/-- `w^{obs} ≤ c_w^{obs} r`. -/
def cWo (d L : ℕ) (Clo : ℝ) : ℝ := cSo d L + Clo * ((L : ℝ) ^ d * cSo d L)

/-- `t_I ≤ c_T r`. -/
def cTo (d L : ℕ) (Cl Clo cS : ℝ) : ℝ :=
  3 * Step2.cUblk d L Cl cS + Step2.cWblk d L Cl + 3 * cUo d L Clo cS + cWo d L Clo

namespace BHF

variable {P : ObsPts d L N} {j : ℕ} {ℓ ℓ' ℓC : ℝ} {C : Matrix (Lam d L N) (Lam d L N) ℂ}
  {V W : OFam c d L N} {K : OAct c d L N} {w : Wt} {A r Cl cS Clo : ℝ}
  (H : BHF P j ℓ ℓ' ℓC C V W K w A r Cl cS Clo)
include H

theorem hcSo : 0 ≤ cSo d L := by
  have hn := H.hB.hcNear; have hQ := H.hB.hQ1
  have := mul_nonneg (mul_nonneg zero_le_two hn) (sq_nonneg (Step2.Q1 d))
  unfold cSo; linarith

theorem hcUo : 0 ≤ cUo d L Clo cS := by
  have hQ := H.hB.hQ1; have hs := H.hcSo; have hClo := H.hO.hCl; have hcS := H.hB.hcS0
  have hL := pow_nonneg H.hB.hL0.le d
  have h1 : 0 ≤ Step2.Q1 d * Step2.pq d ^ 2 * (cS * Clo) :=
    mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (mul_nonneg hcS hClo)
  have h2 : 0 ≤ Clo * ((L : ℝ) ^ d * cSo d L) := mul_nonneg hClo (mul_nonneg hL hs)
  unfold cUo; linarith

theorem hcWo : 0 ≤ cWo d L Clo := by
  have hs := H.hcSo; have hClo := H.hO.hCl
  have hL := pow_nonneg H.hB.hL0.le d
  have h2 : 0 ≤ Clo * ((L : ℝ) ^ d * cSo d L) := mul_nonneg hClo (mul_nonneg hL hs)
  unfold cWo; linarith

theorem hcTo : 0 ≤ cTo d L Cl Clo cS := by
  have := H.hB.hcU; have := H.hB.hcW; have := H.hcUo; have := H.hcWo
  unfold cTo; linarith

theorem sO_le : Obs2.sO d L r r r ≤ cSo d L * r := by
  have hr := H.hr
  have hr1 := H.hB.hr1
  have hn := H.hB.hcNear
  have hQ := H.hB.hQ1
  have hrr : r * r ≤ r := by nlinarith
  have h0 : 0 ≤ 2 * Step2.cNear d L * Step2.Q1 d ^ 2 := by positivity
  unfold Obs2.sO cSo
  nlinarith [mul_le_mul_of_nonneg_left hrr h0]

theorem uo_le : (uoB d L r Clo cS) ≤ cUo d L Clo cS * r := by
  have hs := H.sO_le
  have hClo := H.hO.hCl
  have hL := pow_nonneg H.hB.hL0.le d
  simp only [uoB, Obs2.BHO.uO, cUo]
  have : Clo * ((L : ℝ) ^ d * Obs2.sO d L r r r) ≤ Clo * ((L : ℝ) ^ d * (cSo d L * r)) := by gcongr
  nlinarith

theorem wo_le : (woB d L r Clo) ≤ cWo d L Clo * r := by
  have hs := H.sO_le
  have hClo := H.hO.hCl
  have hL := pow_nonneg H.hB.hL0.le d
  simp only [woB, cWo]
  have : Clo * ((L : ℝ) ^ d * Obs2.sO d L r r r) ≤ Clo * ((L : ℝ) ^ d * (cSo d L * r)) := by gcongr
  nlinarith

theorem tI_le : (tIB d L r Cl Clo cS) ≤ cTo d L Cl Clo cS * r := by
  have := H.uo_le; have := H.wo_le
  simp only [tIB, cTo]
  nlinarith

/-- `‖δI(B)‖ ≤ (8Q₁ + 2c_T) r`. -/
theorem gdIO_le (hr4 : 4 * r ≤ 1) (hT : cTo d L Cl Clo cS * r ≤ 1)
    {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oT2 w j ℓ' ℓC ((Obs.Gen.dIG (algO C) (ingrO P j C V W K) b : OE c (Lam d L N ⊕ Lam d L N)) :
      SA c (Lam d L N ⊕ Lam d L N)) ≤
      ENNReal.ofReal ((8 * Step2.Q1 d + 2 * cTo d L Cl Clo cS) * r) := by
  have hr := H.hr
  have hQ := H.hB.hQ1
  have ht := H.htI
  refine (H.gdIO_full hb).trans (ENNReal.ofReal_le_ofReal ?_)
  have h1 : Real.exp (2 * r + 2 * r) - 1 ≤ 2 * (2 * r + 2 * r) :=
    exp_sub_one_le (by linarith) (by linarith)
  have h2 : Real.exp (tIB d L r Cl Clo cS) - 1 ≤ 2 * (tIB d L r Cl Clo cS) :=
    exp_sub_one_le ht (H.tI_le.trans hT)
  have h3 := H.tI_le
  have h4 := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ Step2.Q1 d by linarith)
  linarith

theorem hE (hC : Step2.GoodCov2 j ℓC C) (x : OE c (Lam d L N ⊕ Lam d L N)) :
    (oSN (nrmP_tNorm (E := Dir d) (p := pPhi d) (X := Lam d L N) (ℓ := ℓ') H.hh' H.hO.hℓ') w
      H.hw).nrm ((algO C).E x) ≤
    (oSN (nrmP_T2 (E := Dir d) (p := pPhi d) (X := Lam d L N) (ℓC := ℓC) H.hh' H.hO.hℓ') w
      H.hw).nrm x := by
  rw [oSN_nrm, oSN_nrm]
  show oNorm (Tj d (L : ℝ) (j + 1) ℓ') w (ECCS C (x : SA c (Lam d L N ⊕ Lam d L N))) ≤ _
  simp only [oNorm, ECCS_e, ECCS_a, ECCS_b, ECCS_ab]
  gcongr <;> exact Step2.ECC_succ_le2 H.hO.hℓ' H.hO.hℓC hC _

/-- **The block hypotheses of the generic crude bound**, with `ρ = Q₁/A`, `κ₀ = 2r A^{2^d}`,
`δ₁ = (8Q₁ + 2c_T) r A/Q₁`, `c_J = Q₁ q² c_S (C_l + C_l^{obs})`. -/
theorem khyp (hAQ : Step2.Q1 d ≤ A) (hr4 : 4 * r ≤ 1) (hT : cTo d L Cl Clo cS * r ≤ 1)
    (hκ : 2 * r * A ^ 2 ^ d ≤ 1)
    (hδ : (8 * Step2.Q1 d + 2 * cTo d L Cl Clo cS) * r * (A / Step2.Q1 d) ≤ 1) :
    Obs.Gen.KHypG (algO C) j (ingrO P j C V W K)
      (oSN (nrmP_T2 (E := Dir d) (p := pPhi d) (X := Lam d L N) (ℓC := ℓC) H.hh' H.hO.hℓ') w
        H.hw)
      (A / Step2.Q1 d) (2 * r * A ^ 2 ^ d)
      ((8 * Step2.Q1 d + 2 * cTo d L Cl Clo cS) * r * (A / Step2.Q1 d))
      (Step2.Q1 d * Step2.pq d ^ 2 * (cS * (Cl + Clo))) := by
  have hr := H.hr
  have hQ := H.hB.hQ1
  have hQ0 : 0 < Step2.Q1 d := by linarith
  have hA0 : 0 < A := by linarith
  have hT0 := H.hcTo
  have hpq := Step2.one_le_pq H.hB.hd
  have hcS := H.hB.hcS0
  have hCl := H.hB.hCl
  have hClo := H.hO.hCl
  have hinv : (A / Step2.Q1 d)⁻¹ = Step2.Q1 d / A := inv_div _ _
  have hAQ1 : A / Step2.Q1 d * (Step2.Q1 d / A) = 1 := by
    rw [div_mul_div_comm, mul_comm A, div_self (mul_ne_zero hQ0.ne' hA0.ne')]
  exact
    { hA := by rw [le_div_iff₀ hQ0, one_mul]; exact hAQ
      hκ₀ := mul_nonneg (mul_nonneg zero_le_two hr) (pow_nonneg hA0.le _)
      hκ₀1 := hκ
      hδ₁ := mul_nonneg (mul_nonneg (by linarith) hr) (div_nonneg hA0.le hQ0.le)
      hδ₁1 := hδ
      hcJ := mul_nonneg (mul_nonneg hQ0.le (sq_nonneg _)) (mul_nonneg hcS (add_nonneg hCl hClo))
      hK := fun X hX => by
        rw [hinv]; exact H.thetaKO_full hX
      hdI := fun b hb => (H.gdIO_le hr4 hT hb).trans (ENNReal.ofReal_le_ofReal (le_of_eq (by
        rw [hinv, mul_assoc ((8 * Step2.Q1 d + 2 * cTo d L Cl Clo cS) * r) (A / Step2.Q1 d)
          (Step2.Q1 d / A), hAQ1, mul_one])))
      hJ := fun b hb X => (H.thetaJO_full hb X).trans (ENNReal.ofReal_le_ofReal (by
        rw [hinv, div_pow]
        have e2 : A ^ 2 ^ d * (Step2.Q1 d ^ 2 ^ d / A ^ 2 ^ d) = Step2.Q1 d ^ 2 ^ d :=
          mul_div_cancel₀ _ (pow_ne_zero _ hA0.ne')
        have h1 : 1 ≤ 2 * Step2.Q1 d ^ 2 ^ d := by
          have : 1 ≤ Step2.Q1 d ^ 2 ^ d := one_le_pow₀ hQ
          linarith
        have h0 : 0 ≤ Step2.Q1 d * Step2.pq d ^ 2 * (cS * ((Cl + Clo) * r)) :=
          mul_nonneg (mul_nonneg hQ0.le (sq_nonneg _))
            (mul_nonneg hcS (mul_nonneg (add_nonneg hCl hClo) hr))
        calc Step2.Q1 d * Step2.pq d ^ 2 * (cS * ((Cl + Clo) * r))
            ≤ Step2.Q1 d * Step2.pq d ^ 2 * (cS * ((Cl + Clo) * r)) * (2 * Step2.Q1 d ^ 2 ^ d) :=
              le_mul_of_one_le_right h0 h1
          _ = Step2.Q1 d * Step2.pq d ^ 2 * (cS * (Cl + Clo)) * (2 * r * A ^ 2 ^ d) *
              (Step2.Q1 d ^ 2 ^ d / A ^ 2 ^ d) := by
            rw [show Step2.Q1 d * Step2.pq d ^ 2 * (cS * (Cl + Clo)) * (2 * r * A ^ 2 ^ d) *
              (Step2.Q1 d ^ 2 ^ d / A ^ 2 ^ d) = Step2.Q1 d * Step2.pq d ^ 2 * (cS * (Cl + Clo)) *
                (2 * r) * (A ^ 2 ^ d * (Step2.Q1 d ^ 2 ^ d / A ^ 2 ^ d)) by ring, e2]
            ring))
      hJs := fun b X hX => J2O_of_not_small P j K b X hX }

end BHF

end

end Obs2
