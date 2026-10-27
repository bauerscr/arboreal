import Step2.Last.LastNDefs

/-!
# The last step `j = N - 1`: block bounds and the crude bound

Copies of the block bounds of `Step2.Map.Block` (`BH`) for the map of `Step2.Last.LastNDefs` at
`j + 1 = N`, with radius `r` (`‖V‖_j, ‖𝒲‖_j, ‖K‖_j ≤ r`). The differences to `BH`:

* no finite range of `C` is used: `F(V'_B, V'(Λ)) = ∑_{B'} F(V'_B, V'_{B'})` is summed over all
  `|𝓑_j(Λ)| ≤ L^d` blocks (`card_blockIdx_last`), so `‖S(B)‖ ≤ (L^d Q₁² + Q₁) r`
  (`cSN`; `BH` has the number of near blocks in place of `L^d`);
* no `Loc` and no `Q`, `J`: `u_N(B) = ε(V'_B)`, `‖V_N(B)‖ ≤ 2 Q₁ r`, `𝒲_N(B) = S(B)`.

`KN_crude_ts`: `‖K_N(Λ)‖_{T_N(ℓ')} ≤ 1` on a ball of radius `r₀(L, A)` (the argument of
`Knext2_crude_ts`, with `GH.gKnext_le` for `U = Λ`).
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

namespace LastN

/-- The block constant of `S(B)` at the last scale (no range). -/
def cSN (d L : ℕ) : ℝ := (L : ℝ) ^ d * Q1 d ^ 2 + Q1 d

/-- The block constant of `I_N(B) - 1`. -/
def cIN (d L : ℕ) : ℝ := 18 * Q1 d + 2 * cSN d L

/-- The hypotheses for the block bounds at `j + 1 = N`, with radius `r`. -/
structure BHN (j : ℕ) (ℓ ℓ' ℓC : ℝ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V W : Fam d L N)
    (K : Act d L N) (A r : ℝ) : Prop where
  hd : 1 ≤ d
  hLp : pauliL0 d ≤ L
  hjN : j + 1 = N
  hℓ : 0 < ℓ
  hℓ' : 0 < ℓ'
  hℓC : 0 < ℓC
  hsum : ℓ' + ℓC ≤ 2 * ℓ
  hC : GoodCov2 j ℓC C
  hV : InF j V
  hW : InF j W
  hV0 : ∀ b, ε (V b : Alg d L N) = 0
  hK : InK2 j K
  hA : 1 ≤ A
  hr : 0 ≤ r
  hr1 : r ≤ 1
  hVr : ∀ b ∈ blockIdx (L := L) (N := N) j, Tj d (L : ℝ) j ℓ (V b : Alg d L N) ≤ ENNReal.ofReal r
  hWr : ∀ b ∈ blockIdx (L := L) (N := N) j, Tj d (L : ℝ) j ℓ (W b : Alg d L N) ≤ ENNReal.ofReal r
  hKr : Knorm j ℓ A K ≤ ENNReal.ofReal r

namespace BHN

variable {j : ℕ} {ℓ ℓ' ℓC : ℝ} {C : Matrix (Lam d L N) (Lam d L N) ℂ} {V W : Fam d L N}
  {K : Act d L N} {A r : ℝ} (H : BHN j ℓ ℓ' ℓC C V W K A r)
include H

theorem hj : j < N := by have := H.hjN; omega

theorem hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)

theorem hh' : (0 : ℝ) < (L : ℝ) ^ (j + 1) := pow_pos H.hL0 _

theorem hQ1 : 1 ≤ Q1 d := one_le_Q1 H.hd

theorem hcS : 0 ≤ cSN d L := by
  have := H.hQ1; have := H.hL0; unfold cSN; positivity

theorem hcI : 0 ≤ cIN d L := by
  have := H.hQ1; have := H.hcS; unfold cIN; positivity

theorem Vpr_le {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    Tj d (L : ℝ) (j + 1) ℓ' (Vpr C V b : Alg d L N) ≤ ENNReal.ofReal (Q1 d * r) := by
  rw [Vpr]
  exact tj_of (by linarith [H.hQ1])
    (EthE_block_le2 H.hd H.hLp H.hj H.hℓ' H.hℓC H.hsum H.hC (H.hV.loc b)) (H.hVr b hb)

theorem V2_le {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    Tj d (L : ℝ) (j + 1) (2 * ℓ) (V b : Alg d L N) ≤ ENNReal.ofReal (Q1 d * r) := by
  rw [ENNReal.ofReal_mul (by linarith [H.hQ1])]
  exact (Tj2_block_le H.hd H.hLp H.hj H.hℓ (H.hV.loc b)).trans (mul_le_mul_left' (H.hVr b hb) _)

theorem FCE_pair_le {b b' : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j)
    (hb' : b' ∈ blockIdx (L := L) (N := N) j) :
    Tj d (L : ℝ) (j + 1) ℓ' (FCE C (Vpr C V b) (Vpr C V b') : Alg d L N) ≤
      ENNReal.ofReal (2 * (Q1 d * r) ^ 2) := by
  have e : ∀ b, (Vpr C V b : Alg d L N) = ECC C (theta (V b : Alg d L N)) := fun b => by
    rw [Vpr, coe_EthE, ECC_theta]
  rw [coe_FCE, e, e]
  refine (FC_succ_le2 H.hℓ' H.hℓC H.hsum H.hC _ _).trans ?_
  have hq : 0 ≤ Q1 d * r := mul_nonneg (by linarith [H.hQ1]) H.hr
  rw [sq, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul hq, ENNReal.ofReal_ofNat]
  gcongr
  · exact H.V2_le hb
  · exact H.V2_le hb'

/-- **`‖S(B)‖ ≤ (L^d Q₁² + Q₁) r`** without the range of `C`. -/
theorem Sb_le {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    Tj d (L : ℝ) (j + 1) ℓ' (Sb j C V W b : Alg d L N) ≤ ENNReal.ofReal (cSN d L * r) := by
  have hQ := H.hQ1
  have hr := H.hr
  have hL0 := H.hL0
  rw [Sb, VprL, FCE_sum_right]
  have h1 := tn_sum_const (E := Dir d) (p := pPhi d) (h := (L : ℝ) ^ (j + 1)) (ℓ := ℓ')
    (blockIdx (L := L) (N := N) j) (fun b' => FCE C (Vpr C V b) (Vpr C V b'))
    (r := 2 * (Q1 d * r) ^ 2) (by positivity) (fun b' hb' => H.FCE_pair_le hb hb')
  have hn : ((blockIdx (d := d) (L := L) (N := N) j).card : ℝ) ≤ (L : ℝ) ^ d := by
    exact_mod_cast card_blockIdx_last (d := d) (L := L) H.hjN
  have h2 : Tj d (L : ℝ) (j + 1) ℓ' (((1 / 2 : ℂ) • ∑ b' ∈ blockIdx (L := L) (N := N) j,
      FCE C (Vpr C V b) (Vpr C V b') : EvR (Lam d L N)) : Alg d L N) ≤
      ENNReal.ofReal ((L : ℝ) ^ d * Q1 d ^ 2 * r) := by
    rw [Subalgebra.coe_smul, Tj_smul']
    refine (mul_le_mul_left' h1 _).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hr2 : r ^ 2 ≤ r := by nlinarith [H.hr1]
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [this]
    have h0 : 0 ≤ Q1 d ^ 2 := by positivity
    calc 1 / 2 * (((blockIdx (d := d) (L := L) (N := N) j).card : ℝ) * (2 * (Q1 d * r) ^ 2))
        = ((blockIdx (d := d) (L := L) (N := N) j).card : ℝ) * (Q1 d ^ 2 * r ^ 2) := by ring
      _ ≤ (L : ℝ) ^ d * (Q1 d ^ 2 * r) := by gcongr
      _ = _ := by ring
  have h3 : Tj d (L : ℝ) (j + 1) ℓ' (EthE C (W b) : Alg d L N) ≤ ENNReal.ofReal (Q1 d * r) :=
    tj_of (by linarith)
      (EthE_block_le2 H.hd H.hLp H.hj H.hℓ' H.hℓC H.hsum H.hC (H.hW.loc b)) (H.hWr b hb)
  refine (tn_addE (by positivity) (by positivity) h2 h3).trans
    (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  unfold cSN; ring

theorem upN_le {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    ‖upN C V b‖ ≤ Q1 d * r := by
  have h := (abs_ε_le (E := Dir d) (p := pPhi d) H.hh' H.hℓ' _).trans (H.Vpr_le hb)
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by linarith [H.hQ1]) H.hr)).1 h

theorem VpN_le {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    Tj d (L : ℝ) (j + 1) ℓ' (VpN C V b : Alg d L N) ≤ ENNReal.ofReal (2 * (Q1 d * r)) := by
  have h0 : 0 ≤ Q1 d * r := mul_nonneg (by linarith [H.hQ1]) H.hr
  rw [VpN]
  refine (tn_subE h0 h0 (H.Vpr_le hb) ?_).trans (ENNReal.ofReal_le_ofReal (by linarith))
  rw [Subalgebra.coe_algebraMap]
  exact (tNorm_algebraMap_le H.hh' H.hℓ' _).trans (ENNReal.ofReal_le_ofReal (H.upN_le hb))

theorem IpN_sub_one_le (hu : Q1 d * r ≤ 1 / 4) (hw : cSN d L * r ≤ 1)
    {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    Tj d (L : ℝ) (j + 1) ℓ' ((IpN j C V W b - 1 : EvR (Lam d L N)) : Alg d L N) ≤
      ENNReal.ofReal (cIN d L * r) := by
  have hr := H.hr
  have hU0 : 0 ≤ Q1 d * r := mul_nonneg (by linarith [H.hQ1]) hr
  have hW0 : 0 ≤ cSN d L * r := mul_nonneg H.hcS hr
  set c : ℂ := Complex.exp (-upN C V b)
  set G : EvR (Lam d L N) := (gexp (-VpN C V b) - 1) * (1 + Sb j C V W b) + Sb j C V W b
  have e : IpN j C V W b - 1 = c • G + (c - 1) • (1 : EvR (Lam d L N)) := by
    have : gexp (-VpN C V b) * (1 + Sb j C V W b) = G + 1 := by simp only [G]; ring
    rw [IpN, this, smul_add, sub_smul, one_smul]; abel
  have hε : ε ((-VpN C V b : EvR (Lam d L N)) : Alg d L N) = 0 := by
    rw [NegMemClass.coe_neg, map_neg, ε_VpN, neg_zero]
  have hg : Tj d (L : ℝ) (j + 1) ℓ' ((gexp (-VpN C V b) - 1 : EvR (Lam d L N)) : Alg d L N) ≤
      ENNReal.ofReal (2 * (2 * (Q1 d * r))) := by
    refine (tNorm_gexp_sub_one_le H.hh' H.hℓ' hε (by positivity) ?_).trans
      (ENNReal.ofReal_le_ofReal (exp_sub_one_le (by positivity) (by linarith)))
    rw [NegMemClass.coe_neg, tNorm_neg]; exact H.VpN_le hb
  have h1W : Tj d (L : ℝ) (j + 1) ℓ' ((1 + Sb j C V W b : EvR (Lam d L N)) : Alg d L N) ≤
      ENNReal.ofReal (1 + cSN d L * r) :=
    tn_addE zero_le_one hW0 (by
      rw [OneMemClass.coe_one, ENNReal.ofReal_one]; exact tNorm_one_le H.hh' H.hℓ') (H.Sb_le hb)
  have hG : Tj d (L : ℝ) (j + 1) ℓ' (G : Alg d L N) ≤
      ENNReal.ofReal (2 * (2 * (Q1 d * r)) * (1 + cSN d L * r) + cSN d L * r) :=
    tn_addE (by positivity) hW0 (tn_mulE H.hh' H.hℓ' (by positivity) hg h1W) (H.Sb_le hb)
  have hupn : ‖upN C V b‖ ≤ 1 / 4 := (H.upN_le hb).trans hu
  have hc : ‖c‖ ≤ 2 := by
    rw [Complex.norm_exp]
    refine (Real.exp_le_exp.2 ((Complex.re_le_norm _).trans ?_)).trans BH.exp_quarter_le
    rw [norm_neg]; exact hupn
  have hc1 : ‖c - 1‖ ≤ 2 * (Q1 d * r) := by
    refine (Complex.norm_exp_sub_one_le (by rw [norm_neg]; linarith)).trans ?_
    rw [norm_neg]; linarith [H.upN_le hb]
  rw [e]
  refine (tNorm_add_le _ _).trans ?_
  rw [Subalgebra.coe_smul, Subalgebra.coe_smul, tNorm_smul, tNorm_smul, OneMemClass.coe_one]
  have h1 := tNorm_one_le (E := Dir d) (p := pPhi d) (X := Lam d L N) H.hh' H.hℓ'
  calc ENNReal.ofReal ‖c‖ * Tj d (L : ℝ) (j + 1) ℓ' (G : Alg d L N) +
        ENNReal.ofReal ‖c - 1‖ * Tj d (L : ℝ) (j + 1) ℓ' (1 : Alg d L N)
      ≤ ENNReal.ofReal 2 * ENNReal.ofReal
          (2 * (2 * (Q1 d * r)) * (1 + cSN d L * r) + cSN d L * r) +
        ENNReal.ofReal (2 * (Q1 d * r)) * 1 := by
        gcongr
    _ = ENNReal.ofReal (2 * (2 * (2 * (Q1 d * r)) * (1 + cSN d L * r) +
          cSN d L * r) + 2 * (Q1 d * r)) := by
        rw [mul_one, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
    _ ≤ ENNReal.ofReal (cIN d L * r) := by
        refine ENNReal.ofReal_le_ofReal ?_
        unfold cIN
        nlinarith

theorem Ib_sub_one_le {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    Tj d (L : ℝ) j ℓ ((Ib V W b - 1 : EvR (Lam d L N)) : Alg d L N) ≤ ENNReal.ofReal (5 * r) := by
  have hr := H.hr
  have hh : (0 : ℝ) < (L : ℝ) ^ j := pow_pos H.hL0 _
  have e : Ib V W b - 1 = (gexp (-V b) - 1) * (1 + W b) + W b := by rw [Ib]; ring
  have hε : ε ((-V b : EvR (Lam d L N)) : Alg d L N) = 0 := by
    rw [NegMemClass.coe_neg, map_neg, H.hV0 b, neg_zero]
  have hg : Tj d (L : ℝ) j ℓ ((gexp (-V b) - 1 : EvR (Lam d L N)) : Alg d L N) ≤
      ENNReal.ofReal (2 * r) := by
    refine (tNorm_gexp_sub_one_le hh H.hℓ hε hr ?_).trans
      (ENNReal.ofReal_le_ofReal (exp_sub_one_le hr H.hr1))
    rw [NegMemClass.coe_neg, tNorm_neg]; exact H.hVr b hb
  have h1W : Tj d (L : ℝ) j ℓ ((1 + W b : EvR (Lam d L N)) : Alg d L N) ≤
      ENNReal.ofReal (1 + r) :=
    tn_addE zero_le_one hr (by
      rw [OneMemClass.coe_one, ENNReal.ofReal_one]; exact tNorm_one_le hh H.hℓ) (H.hWr b hb)
  rw [e]
  refine (tn_addE (by positivity) hr (tn_mulE hh H.hℓ (by positivity) hg h1W)
    (H.hWr b hb)).trans (ENNReal.ofReal_le_ofReal ?_)
  nlinarith [H.hr1]

theorem Ib_sub_one_mem (b : Fin d → ℕ) :
    ((Ib V W b - 1 : EvR (Lam d L N)) : Alg d L N) ∈
      NX (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N)) := by
  have hε : ε ((-V b : EvR (Lam d L N)) : Alg d L N) = 0 := by
    rw [NegMemClass.coe_neg, map_neg, H.hV0 b, neg_zero]
  rw [Ib, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, AddMemClass.coe_add,
    OneMemClass.coe_one]
  refine sub_mem (mul_mem (gexp_mem_NX hε ?_) (add_mem (one_mem _) (H.hW.loc b))) (one_mem _)
  rw [NegMemClass.coe_neg]; exact neg_mem (H.hV.loc b)

theorem gdI_le (hu : Q1 d * r ≤ 1 / 4) (hw : cSN d L * r ≤ 1)
    {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    T2 (Dir d) (pPhi d) ((L : ℝ) ^ (j + 1)) ℓ' ℓC (gdI (Ib V W) (IpN j C V W) b : Alg2 d L N) ≤
      ENNReal.ofReal ((5 * Q1 d + cIN d L) * r) := by
  have hr := H.hr
  have hQ := H.hQ1
  have hcI := H.hcI
  have e : gdI (Ib V W) (IpN j C V W) b =
      thetaE (Ib V W b - 1) - inclE (IpN j C V W b - 1) := by
    rw [gdI, map_sub, map_sub, map_one, map_one]; abel
  rw [e]
  refine (t2_subE (s := Q1 d * (5 * r)) (t := cIN d L * r) (by positivity)
    (by positivity) ?_ ?_).trans (ENNReal.ofReal_le_ofReal (le_of_eq (by ring)))
  · rw [coe_thetaE]
    exact tj_of (by linarith)
      (theta_block_le2 H.hd H.hLp H.hj H.hℓ' H.hℓC H.hsum (H.Ib_sub_one_mem b))
      (H.Ib_sub_one_le hb)
  · rw [coe_inclE]
    exact (T2_incl_le H.hh' H.hℓ' _).trans (H.IpN_sub_one_le hu hw hb)

theorem thetaK_le {X : Finset (Lam d L N)} (hX : IsConn j X) :
    T2 (Dir d) (pPhi d) ((L : ℝ) ^ (j + 1)) ℓ' ℓC (thetaE (K X) : Alg2 d L N) ≤
      ENNReal.ofReal (r * A ^ 2 ^ d * (Q1 d / A) ^ nb j X) := by
  have hA1 := H.hA
  have hA0 : 0 < A := by linarith
  have hr := H.hr
  have hQ := H.hQ1
  rw [coe_thetaE]
  refine (theta_conn_le2 H.hd H.hLp H.hj H.hℓ' H.hℓC H.hsum (H.hK.loc X hX)).trans ?_
  have hw := (wnorm_le_Knorm (ℓ := ℓ) (A := A) (K := K) hX).trans H.hKr
  rw [wnorm] at hw
  set n := nb j X
  have hAn : (1 : ℝ) ≤ A ^ 2 ^ d * A⁻¹ ^ n * A ^ (n - 2 ^ d) := by
    have h1 : A ^ n ≤ A ^ 2 ^ d * A ^ (n - 2 ^ d) := by
      rw [← pow_add]; exact pow_le_pow_right₀ hA1 (by omega)
    have hAn0 : 0 < A ^ n := by positivity
    rw [inv_pow]
    calc (1 : ℝ) = A ^ n * (A ^ n)⁻¹ := (mul_inv_cancel₀ hAn0.ne').symm
      _ ≤ (A ^ 2 ^ d * A ^ (n - 2 ^ d)) * (A ^ n)⁻¹ := by gcongr
      _ = _ := by ring
  have hT : Tj d (L : ℝ) j ℓ (K X : Alg d L N) ≤ ENNReal.ofReal (r * A ^ 2 ^ d * A⁻¹ ^ n) := by
    calc Tj d (L : ℝ) j ℓ (K X : Alg d L N)
        ≤ ENNReal.ofReal (A ^ 2 ^ d * A⁻¹ ^ n * A ^ (n - 2 ^ d)) *
            Tj d (L : ℝ) j ℓ (K X : Alg d L N) := by
          refine le_mul_of_one_le_left zero_le ?_
          rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hAn
      _ = ENNReal.ofReal (A ^ 2 ^ d * A⁻¹ ^ n) * (ENNReal.ofReal (A ^ (n - 2 ^ d)) *
            Tj d (L : ℝ) j ℓ (K X : Alg d L N)) := by
          rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
      _ ≤ ENNReal.ofReal (A ^ 2 ^ d * A⁻¹ ^ n) * ENNReal.ofReal r := by gcongr
      _ = ENNReal.ofReal (r * A ^ 2 ^ d * A⁻¹ ^ n) := by
          rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
  refine (mul_le_mul_left' hT _).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [div_eq_mul_inv, mul_pow]; ring

theorem IpN_le (hu : Q1 d * r ≤ 1 / 4) (hw : cSN d L * r ≤ 1)
    {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    Tj d (L : ℝ) (j + 1) ℓ' (IpN j C V W b : Alg d L N) ≤
      ENNReal.ofReal (Real.exp (cIN d L * r)) := by
  have e : IpN j C V W b = 1 + (IpN j C V W b - 1) := by abel
  rw [e]
  refine (tn_addE zero_le_one (by have := H.hr; have := H.hcI; positivity)
    (by rw [OneMemClass.coe_one, ENNReal.ofReal_one]; exact tNorm_one_le H.hh' H.hℓ')
    (H.IpN_sub_one_le hu hw hb)).trans (ENNReal.ofReal_le_ofReal ?_)
  linarith [Real.add_one_le_exp (cIN d L * r)]

/-- The prefactors `e^{u_N(U)} I_N^{U ∖ Z}`. -/
theorem prefN_le (hu : Q1 d * r ≤ 1 / 4) (hw : cSN d L * r ≤ 1)
    (U Z : Finset (Lam d L N)) :
    Tj d (L : ℝ) (j + 1) ℓ' ((Complex.exp (uXN j C V U) • bpow j (IpN j C V W) (U \ Z) :
      EvR (Lam d L N)) : Alg d L N) ≤
      ENNReal.ofReal (Real.exp ((Q1 d + cIN d L) * r * nb j U)) := by
  have hr := H.hr
  have hcI := H.hcI
  have hQ := H.hQ1
  rw [Subalgebra.coe_smul, Tj_smul']
  have hb : Tj d (L : ℝ) (j + 1) ℓ' (bpow j (IpN j C V W) (U \ Z) : Alg d L N) ≤
      ENNReal.ofReal (Real.exp (cIN d L * r) ^ nb j U) := by
    have := tn_prodE (E := Dir d) (p := pPhi d) H.hh' H.hℓ' (blocks j (U \ Z)) (IpN j C V W)
      (fun _ => Real.exp (cIN d L * r)) (fun _ _ => (Real.exp_pos _).le)
      (fun b hb => H.IpN_le hu hw (mem_blockIdx_of_mem_blocks hb))
    rw [prod_const] at this
    refine this.trans (ENNReal.ofReal_le_ofReal ?_)
    exact pow_le_pow_right₀ (Real.one_le_exp (by positivity))
      (card_le_card (blocks_mono sdiff_subset))
  have hc : ‖Complex.exp (uXN j C V U)‖ ≤ Real.exp (Q1 d * r * nb j U) := by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.2 ((Complex.re_le_norm _).trans ?_)
    rw [uXN]
    refine (norm_sum_le _ _).trans ?_
    refine (sum_le_sum fun b hb => H.upN_le (mem_blockIdx_of_mem_blocks hb)).trans (le_of_eq ?_)
    rw [sum_const, nsmul_eq_mul, nb]; ring
  refine (mul_le_mul' (ENNReal.ofReal_le_ofReal hc) hb).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 2; ring

end BHN

theorem J2_last {j : ℕ} (hj : j + 1 = N) (K : Act d L N) (b : Fin d → ℕ)
    (X : Finset (Lam d L N)) : J2 j K b X = 0 := by
  rw [J2, if_neg (by omega)]

set_option maxHeartbeats 1000000 in
/-- **The crude bound** on `K_N(Λ)` at the last step `j + 1 = N`, on a ball of radius
`r₀(L, A)`, with input field scale `ℓ`, output field scale `ℓ'` and covariance field scale `ℓ_C`,
`ℓ' + ℓ_C ≤ 2ℓ`. No range of `C` is needed. -/
theorem KN_crude_ts (d : ℕ) (hd : 1 ≤ d) : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∃ r₀ : ℝ, 0 < r₀ ∧
    ∀ (N j : ℕ), j + 1 = N → ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓC C →
    ∀ (V W : Fam d L N) (K : Act d L N), InF j V → InF j W → (∀ b, ε (V b : Alg d L N) = 0) →
      InK2 j K → Fnorm j ℓ V ≤ ENNReal.ofReal r₀ → Fnorm j ℓ W ≤ ENNReal.ofReal r₀ →
      Knorm j ℓ A K ≤ ENNReal.ofReal r₀ →
        wnorm (j + 1) ℓ' A univ (KN j C V W K univ) ≤ ENNReal.ofReal 1 := by
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
  set Q := Q1 d with hQdef
  have hQ : 1 ≤ Q := one_le_Q1 hd
  have hQ0 : 0 < Q := by linarith
  set M : ℕ := 2 ^ ((1 + c) * L ^ d) with hMdef
  have hM1 : 1 ≤ M := Nat.one_le_two_pow
  have hM1' : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  set P : ℝ := Q * (2 * M) with hPdef
  have hP1 : 1 ≤ P := by rw [hPdef]; nlinarith
  have hη' : 0 < 2 * η / (1 + 2 * η) := by positivity
  set A₀ : ℝ := Q * max 1 ((4 * P) ^ ((1 + 2 * η) / (2 * η))) with hA₀
  have hA₀1 : 1 ≤ A₀ := by
    rw [hA₀]; nlinarith [le_max_left (1 : ℝ) ((4 * P) ^ ((1 + 2 * η) / (2 * η)))]
  refine ⟨A₀, hA₀1, ?_⟩
  intro A hA
  have hA1 : 1 ≤ A := hA₀1.trans hA
  have hA0 : 0 < A := by linarith
  set Ar : ℝ := A / Q with hArdef
  have hArQ : Ar * Q = A := by rw [hArdef]; field_simp
  have hAr : max 1 ((4 * P) ^ ((1 + 2 * η) / (2 * η))) ≤ Ar := by
    rw [hArdef, le_div_iff₀ hQ0, mul_comm]; exact hA
  have hAr1 : 1 ≤ Ar := (le_max_left _ _).trans hAr
  have hAP : 4 * P ≤ Ar ^ (2 * η / (1 + 2 * η)) := by
    calc 4 * P = ((4 * P) ^ ((1 + 2 * η) / (2 * η))) ^ (2 * η / (1 + 2 * η)) := by
          rw [← Real.rpow_mul (by positivity)]
          rw [show (1 + 2 * η) / (2 * η) * (2 * η / (1 + 2 * η)) = 1 by field_simp]
          rw [Real.rpow_one]
      _ ≤ Ar ^ (2 * η / (1 + 2 * η)) :=
          Real.rpow_le_rpow (by positivity) ((le_max_right _ _).trans hAr) hη'.le
  set cs := cSN d L
  set ci := cIN d L
  have hcs : 0 ≤ cs := by simp only [cs, cSN]; positivity
  have hci : 0 ≤ ci := by simp only [ci, cIN]; positivity
  set Bc : ℝ := A ^ 2 ^ d + (5 * Q + ci) * Ar with hBc
  have hBc0 : 0 ≤ Bc := by positivity
  set D : ℝ := 1 + 4 * Q + cs + 2 * (Q + ci) * (L : ℝ) ^ d + A ^ 2 ^ d + (5 * Q + ci) * Ar +
    (Ar * P) ^ 2 ^ d * Bc with hD
  have hD0 : 0 < D := by positivity
  refine ⟨1 / D, by positivity, ?_⟩
  intro N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC V W K hV hW hV0 hK hVr hWr hKr
  set r := 1 / D with hrdef
  have hr0 : 0 ≤ r := by positivity
  have hrle : r ≤ 1 / D := le_rfl
  have item : ∀ x : ℝ, 0 ≤ x → x ≤ D → x * r ≤ 1 := fun x hx hxD =>
    le_one_of_le_div hx hD0 hrle hxD
  have t1 : 0 ≤ 4 * Q := by positivity
  have t2 : 0 ≤ 2 * (Q + ci) * (L : ℝ) ^ d := by positivity
  have t3 : 0 ≤ A ^ 2 ^ d := by positivity
  have t4 : 0 ≤ (5 * Q + ci) * Ar := by positivity
  have t5 : 0 ≤ (Ar * P) ^ 2 ^ d * Bc := by positivity
  have hr1 : r ≤ 1 := by
    simpa using item 1 zero_le_one (by rw [hD]; linarith)
  have hj : j < N := by omega
  have H : BHN j ℓ ℓ' ℓC C V W K A r :=
    { hd := hd, hLp := hLp, hjN := hjN, hℓ := hℓ, hℓ' := hℓ', hℓC := hℓC,
      hsum := hsum, hC := hC, hV := hV, hW := hW,
      hV0 := hV0, hK := hK, hA := hA1, hr := hr0, hr1 := hr1
      hVr := fun b hb => (le_iSup₂ (f := fun b (_ : b ∈ blockIdx (L := L) (N := N) j) =>
        Tj d (L : ℝ) j ℓ (V b : Alg d L N)) b hb).trans hVr
      hWr := fun b hb => (le_iSup₂ (f := fun b (_ : b ∈ blockIdx (L := L) (N := N) j) =>
        Tj d (L : ℝ) j ℓ (W b : Alg d L N)) b hb).trans hWr
      hKr := hKr }
  have hu : Q * r ≤ 1 / 4 := by
    have := item (4 * Q) (by positivity) (by rw [hD]; linarith)
    linarith
  have hw : cs * r ≤ 1 := item cs hcs (by rw [hD]; linarith)
  have hpr : (Q + ci) * r * (L : ℝ) ^ d ≤ 1 / 2 := by
    have := item (2 * (Q + ci) * (L : ℝ) ^ d) (by positivity) (by rw [hD]; linarith)
    nlinarith
  have hκ1 : r * A ^ 2 ^ d ≤ 1 := by
    have := item (A ^ 2 ^ d) t3 (by rw [hD]; linarith)
    linarith [mul_comm r (A ^ 2 ^ d)]
  have hδ1 : (5 * Q + ci) * r * Ar ≤ 1 := by
    have := item ((5 * Q + ci) * Ar) t4 (by rw [hD]; linarith)
    have e : (5 * Q + ci) * r * Ar = (5 * Q + ci) * Ar * r := by ring
    linarith
  have hDβ : (Ar * P) ^ 2 ^ d * ((1 + 2 ^ d * 0) * (r * A ^ 2 ^ d) + (5 * Q + ci) * r * Ar) ≤ 1 := by
    have e : (Ar * P) ^ 2 ^ d * ((1 + 2 ^ d * 0) * (r * A ^ 2 ^ d) + (5 * Q + ci) * r * Ar) =
        ((Ar * P) ^ 2 ^ d * Bc) * r := by rw [hBc]; ring
    rw [e]; exact item _ (by positivity) (by rw [hD]; linarith)
  have hρ : Q / A = Ar⁻¹ := by rw [hArdef, inv_div]
  have G : GH j (Ib V W) (IpN j C V W) K (J2 j K) ((L : ℝ) ^ (j + 1)) ℓ' ℓC (Q / A)
      (r * A ^ 2 ^ d) ((5 * Q + ci) * r * Ar) 0 :=
    { hh' := H.hh', hℓ' := hℓ', hρ := by positivity
      hρ1 := by rw [div_le_one hA0]; exact (le_mul_of_one_le_left hQ0.le hAr1).trans hArQ.le
      hκ₀ := by positivity, hκ₀1 := hκ1, hδ₁ := by positivity, hδ₁1 := hδ1, hcJ := le_rfl
      hK := fun W hW => H.thetaK_le hW
      hdI := fun b hb => (H.gdI_le hu hw hb).trans (ENNReal.ofReal_le_ofReal (le_of_eq (by
        rw [hArdef]; field_simp; show _ = r * (5 * Q1 d + cIN d L); ring)))
      hJ := fun b hb X => by
        rw [J2_last hjN, map_zero, ZeroMemClass.coe_zero, T2_zero]; exact zero_le
      hJs := fun b X hX => J2_of_not_small j K b X hX }
  have hU : IsConn (j + 1) (univ : Finset (Lam d L N)) := by
    subst hjN; exact isConn_top
  have hUj : IsPolymer j (univ : Finset (Lam d L N)) := isPolymer_univ j
  have key := G.gKnext_le C (Complex.exp (uXN j C V univ)) hAr1 hρ hQ hη0.le
    (fun F => ECC_succ_le2 hℓ' hℓC hC F)
    (fun g _ => by
      refine (H.prefN_le hu hw univ _).trans (ENNReal.ofReal_le_ofReal ?_)
      have hnb : (nb j (univ : Finset (Lam d L N)) : ℝ) ≤
          (L : ℝ) ^ d * nb (j + 1) (univ : Finset (Lam d L N)) := by
        exact_mod_cast nb_le_of_succ hU.1
      have hx : (Q + ci) * r * nb j (univ : Finset (Lam d L N)) ≤
          (nb (j + 1) (univ : Finset (Lam d L N)) : ℝ) * (1 / 2) := by
        have : (Q + ci) * r * nb j (univ : Finset (Lam d L N)) ≤
            (Q + ci) * r * ((L : ℝ) ^ d * nb (j + 1) (univ : Finset (Lam d L N))) := by
          gcongr
        nlinarith [mul_le_mul_of_nonneg_right hpr
          (Nat.cast_nonneg (α := ℝ) (nb (j + 1) (univ : Finset (Lam d L N))))]
      have he : Real.exp (1 / 2) ≤ 2 := by
        have := (abs_le.1 (Real.abs_exp_sub_one_le (x := 1 / 2) (by norm_num))).2
        norm_num at this ⊢; linarith
      calc Real.exp ((Q1 d + cIN d L) * r * nb j (univ : Finset (Lam d L N))) ≤
            Real.exp ((nb (j + 1) (univ : Finset (Lam d L N)) : ℝ) * (1 / 2)) :=
            Real.exp_le_exp.2 hx
        _ = Real.exp (1 / 2) ^ nb (j + 1) (univ : Finset (Lam d L N)) := Real.exp_nat_mul _ _
        _ ≤ 2 ^ nb (j + 1) (univ : Finset (Lam d L N)) :=
            pow_le_pow_left₀ (Real.exp_pos _).le he _)
    (by
      refine (card_Gset_le (fun b hb => hc L N j b hb) hUj).trans ?_
      rw [hMdef, ← pow_mul]
      exact Nat.pow_le_pow_right (by norm_num) (by
        rw [mul_assoc]; exact Nat.mul_le_mul_left _ (nb_le_of_succ hU.1)))
    (fun g hg => nU_bound (fun X hX => (hcomb L hL1 N j X hj hX).1)
      (fun b hb => (isSmall_clo_nbhd hd hL2 hj b hb).2.2) hη0.le hg)
    hPdef hM1 hAP hDβ
  rw [hArQ] at key
  refine le_trans ?_ key
  unfold wnorm
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (pow_le_pow_right₀ hA1 (Nat.sub_le _ _))) le_rfl

end LastN

end

end Step2
