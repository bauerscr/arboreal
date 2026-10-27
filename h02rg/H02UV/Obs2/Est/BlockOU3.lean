import Obs2.Est.BlockO3
import Obs2.Est.BlockOU2

/-!
# `θK`, `Loc K`, `θJ` and the prefactors on the `σ_aσ_b` sector (`ab` copy of `Obs2.Est.BlockO3`)

Under `BHFU`: `K_full`, `thetaKO_full`, `LocO2_full` (the localisation bound on `abSub`),
`J2O_cmp`, `J2O_full`, `thetaJO_full`, `prefO_full` (namespace `BHFU`). The Pauli bounds for `θ`
are `thetaO_conn_le2A`, `thetaO_le2A` (any weights).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step FRD ENNReal

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

namespace BHFU

variable {P : ObsPts d L N} {j : ℕ} {ℓ ℓ' ℓC : ℝ} {C : Matrix (Lam d L N) (Lam d L N) ℂ}
  {V W : OFam c d L N} {K : OAct c d L N} {w : Wt} {A r Cl cS Clo : ℝ}
  (H : BHFU P j ℓ ℓ' ℓC C V W K w A r Cl cS Clo)
include H

theorem K_full {X : Finset (Lam d L N)} (hX : IsConn j X) :
    oTj d L w j ℓ (K X : SA c (Lam d L N)) ≤
      ENNReal.ofReal (2 * r * A ^ 2 ^ d * A⁻¹ ^ nb j X) := by
  have hA := H.hB.hA
  have hr := H.hr
  have hb : Tj d (L : ℝ) j ℓ (K X : SA c (Lam d L N)).e ≤
      ENNReal.ofReal (r * A ^ 2 ^ d * A⁻¹ ^ nb j X) := by
    refine le_of_wt hA hr ?_
    have := (wnorm_le_Knorm (ℓ := ℓ) (A := A) (K := bulkF K) hX).trans H.hB.hKr
    exact this
  have ho : oTo w j ℓ (K X) ≤ ENNReal.ofReal (r * A ^ 2 ^ d * A⁻¹ ^ nb j X) :=
    le_of_wt hA hr (H.hKo X hX)
  have hA0 : 0 < A := by linarith
  refine (H.full_le (by positivity) (by positivity) hb ho).trans (le_of_eq ?_)
  congr 1; ring

theorem thetaKO_full {X : Finset (Lam d L N)} (hX : IsConn j X) :
    oT2 w j ℓ' ℓC (thetaO (K X) : SA c (Lam d L N ⊕ Lam d L N)) ≤
      ENNReal.ofReal (2 * r * A ^ 2 ^ d * (Step2.Q1 d / A) ^ nb j X) := by
  have hA := H.hB.hA
  have hA0 : 0 < A := by linarith
  have hr := H.hr
  have hQ := H.hB.hQ1
  refine (thetaO_conn_le2A H.hB.hd H.hB.hLp H.hB.hj H.hO.hℓ' H.hO.hℓC H.hO.hsum
    (H.hKl X hX)).trans ?_
  refine (mul_le_mul_left' (H.K_full hX) _).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [div_eq_mul_inv, mul_pow]; ring

theorem LocO2_full {b : Fin d → ℕ} {X : Finset (Lam d L N)} (hs : IsSmall j X)
    (hbX : blockSet (L := L) (N := N) j b ⊆ X) :
    oTj d L w j ℓ (LocO2 P X (blockSet (L := L) (N := N) j b) (K X) : SA c (Lam d L N)) ≤
      ENNReal.ofReal ((Cl + Clo) * r) := by
  have hr := H.hr
  have hCl := H.hB.hCl
  have hClo := H.hO.hCl
  refine (H.full_le (mul_nonneg hCl hr) (mul_nonneg hClo hr) ?_ ?_).trans
    (le_of_eq (by congr 1; ring))
  · show Tj d (L : ℝ) j ℓ ((bulk (LocO2 P X (blockSet (L := L) (N := N) j b) (K X)) :
      EvR (Lam d L N)) : Alg d L N) ≤ _
    rw [bulk_LocO2]
    exact H.hB.loc_term_le hs hbX
  · exact (H.hO.hloc j H.hO.hj ℓ H.hO.hℓ X _ hs hbX (K X) (H.hO.hKl X hs)).trans
      (le_ofReal_mul hClo le_rfl (H.hO.hKk X hs))

theorem J2O_cmp {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j)
    (X : Finset (Lam d L N)) :
    CmpInA (↑(nbhd j (blockSet (L := L) (N := N) j b) ∪ {P.a, P.b}) : Set (Lam d L N))
      (J2O P j K b X : SA c (Lam d L N)) := by
  classical
  have hYp : IsPolymer j (blockSet (L := L) (N := N) j b) := (isSmall_blockSet_of_mem hb).1
  rw [J2O]
  split_ifs
  · rw [NegMemClass.coe_neg, AddSubmonoidClass.coe_finsetSum]
    exact (CmpInA.sum _ fun Y _ => H.hO.hlocl Y _ hYp (K Y)).neg
  · exact H.hO.hlocl X _ hYp (K X)
  · exact CmpInA.zero

theorem J2O_full {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j)
    (X : Finset (Lam d L N)) :
    oTj d L w j ℓ (J2O P j K b X : SA c (Lam d L N)) ≤
      ENNReal.ofReal (cS * ((Cl + Clo) * r)) := by
  classical
  have hr := H.hr
  have hCl := H.hB.hCl
  have hClo := H.hO.hCl
  have hcS := H.hB.hcS0
  have h0 : 0 ≤ (Cl + Clo) * r := by positivity
  rw [J2O]
  split_ifs with h1 h2
  · rw [NegMemClass.coe_neg]
    refine (le_of_eq (oT_neg (E := Dir d) (p := pPhi d) _)).trans ?_
    rw [AddSubmonoidClass.coe_finsetSum]
    refine (oT_sum_le _ _).trans ((le_ofReal_sum_const _ h0 fun Y hY => ?_).trans
      (ENNReal.ofReal_le_ofReal ?_))
    · obtain ⟨hY1, hY2⟩ := mem_filter.1 hY
      exact H.LocO2_full (mem_smallSets.1 hY1) hY2.1
    · refine mul_le_mul_of_nonneg_right (le_trans ?_ (H.hB.hcount b hb)) h0
      exact_mod_cast card_le_card fun Y hY => by
        obtain ⟨hY1, hY2⟩ := mem_filter.1 hY
        exact mem_filter.2 ⟨hY1, hY2.1⟩
  · refine (H.LocO2_full h1.2.1 h1.2.2).trans (ENNReal.ofReal_le_ofReal ?_)
    have := mul_le_mul_of_nonneg_right H.hB.hcS h0
    linarith
  · rw [show ((0 : OE c (Lam d L N)) : SA c (Lam d L N)) = 0 from rfl]
    exact (le_of_eq (oT_zero (E := Dir d) (p := pPhi d))).trans zero_le

theorem thetaJO_full {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j)
    (X : Finset (Lam d L N)) :
    oT2 w j ℓ' ℓC (thetaO (J2O P j K b X) : SA c (Lam d L N ⊕ Lam d L N)) ≤
      ENNReal.ofReal (Step2.Q1 d * Step2.pq d ^ 2 * (cS * ((Cl + Clo) * r))) := by
  have hpq := Step2.one_le_pq H.hB.hd
  have hQ := H.hB.hQ1
  refine (thetaO_le2A H.hB.hd H.hB.hLp H.hB.hj H.hO.hℓ' H.hO.hℓC H.hO.hsum
    (H.J2O_cmp hb X)).trans ?_
  exact Step2.tj_of (mul_nonneg (by linarith) (by positivity)) (mul_le_mul_right'
    (ENNReal.ofReal_le_ofReal H.hO.pq_pow_pts_le) _) (H.J2O_full hb X)

/-! ### The prefactors -/

theorem prefO_full (U Z : Finset (Lam d L N)) :
    oTj d L w (j + 1) ℓ' ((Obs.Gen.PrefG j (ingrO P j C V W K) U *
      Obs.Gen.ItPow j (ingrO P j C V W K) (U \ Z) : OE c (Lam d L N)) : SA c (Lam d L N)) ≤
      ENNReal.ofReal (Real.exp ((Step2.cUblk d L Cl cS * r + (uoB d L r Clo cS) + tIB d L r Cl Clo cS) * nb j U)) := by
  classical
  have h0 := mul_nonneg H.hB.hcU H.hr
  have hu := H.huo
  have ht := H.htI
  set n := oSN (nrmP_tNorm (E := Dir d) (p := pPhi d) (X := Lam d L N) (ℓ := ℓ') H.hh'
    H.hO.hℓ') w H.hw
  have hP : n.nrm (Obs.Gen.PrefG j (ingrO P j C V W K) U) ≤
      ENNReal.ofReal (Real.exp (Step2.cUblk d L Cl cS * r + uoB d L r Clo cS) ^ nb j U) := by
    have := n.prodR (blocks j U) (fun b => expU (upB P j C V W K b) (upO P j C V W K b))
      (fun _ => Real.exp (Step2.cUblk d L Cl cS * r + uoB d L r Clo cS)) (fun _ _ => (Real.exp_pos _).le)
      (fun b hb => H.expU_full (mem_blockIdx_of_mem_blocks hb))
    rwa [prod_const] at this
  have hI : n.nrm (Obs.Gen.ItPow j (ingrO P j C V W K) (U \ Z)) ≤
      ENNReal.ofReal (Real.exp (tIB d L r Cl Clo cS) ^ nb j U) := by
    have := n.prodR (blocks j (U \ Z)) (fun b => IpO P j C V W K b)
      (fun _ => Real.exp (tIB d L r Cl Clo cS)) (fun _ _ => (Real.exp_pos _).le)
      (fun b hb => H.IpO_full (mem_blockIdx_of_mem_blocks hb))
    rw [prod_const] at this
    refine this.trans (ENNReal.ofReal_le_ofReal ?_)
    exact pow_le_pow_right₀ (Real.one_le_exp ht) (card_le_card (blocks_mono sdiff_subset))
  refine (n.mulR (by positivity) hP hI).trans (le_of_eq ?_)
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 2; ring

end BHFU

end

end Obs2
