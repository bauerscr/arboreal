import Obs2.Est.EstAB
import Obs2.Est.EstNorm
import Obs2.Loc.LocFlow
import Obs2.Map.SigmaScale

/-!
# Locality of all four components; the lifted two-scale bounds for any weights

The `ab` copy of the componentwise layer of `Obs2.Est.EstNorm`. `CmpIn S F` only constrains the bulk
and the single-source components; **`CmpInA S F`** adds `F_{ab} ∈ 𝒩(S)` (provided by
`Obs2.osub`, `cmpInA_of_osub`). With all four components local the two-scale bounds hold for
**any** weights (`oNorm_le_cmp`, no `w_ab = 0`):

* `oTj_succ_two_leA`, `oTj_EthO_le2A`, `oTo_EthO_le2A`;
* `FCO_eq_zero_of_sepA`: finite range kills all four components of `F_C(A, B)`;
* `FCO_obs_obs_ab`: on `abSub`, `F_C(𝔼θπ_{obs}A, 𝔼θπ_{obs}B) = 0` (the product of two
  observable parts feeds only `F_aG_b + F_bG_a`).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step FRD ENNReal

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

/-- All four components of `F` lie in `𝒩(S)`. -/
structure CmpInA {Λ : Type*} [DecidableEq Λ] (S : Set Λ) (F : SA c Λ) : Prop
    extends CmpIn S F where
  ab : F.ab ∈ NX S

section CmpInA

variable {Λ : Type*} [DecidableEq Λ] {S : Set Λ}

theorem CmpInA.mono {S' : Set Λ} (h : S ⊆ S') {F : SA c Λ} (hF : CmpInA S F) : CmpInA S' F :=
  ⟨hF.toCmpIn.mono h, NX_mono h hF.ab⟩

theorem CmpInA.zero : CmpInA S (0 : SA c Λ) := ⟨CmpIn.zero, zero_mem _⟩

theorem CmpInA.add {F G : SA c Λ} (hF : CmpInA S F) (hG : CmpInA S G) : CmpInA S (F + G) :=
  ⟨hF.toCmpIn.add hG.toCmpIn, add_mem hF.ab hG.ab⟩

theorem CmpInA.neg {F : SA c Λ} (hF : CmpInA S F) : CmpInA S (-F) :=
  ⟨hF.toCmpIn.neg, neg_mem hF.ab⟩

theorem CmpInA.sub {F G : SA c Λ} (hF : CmpInA S F) (hG : CmpInA S G) : CmpInA S (F - G) :=
  ⟨hF.toCmpIn.sub hG.toCmpIn, sub_mem hF.ab hG.ab⟩

theorem CmpInA.smul (r : ℂ) {F : SA c Λ} (hF : CmpInA S F) : CmpInA S (r • F) :=
  ⟨hF.toCmpIn.smul r, Subalgebra.smul_mem _ hF.ab r⟩

theorem CmpInA.sum {ι : Type*} (s : Finset ι) {F : ι → SA c Λ} (hF : ∀ i ∈ s, CmpInA S (F i)) :
    CmpInA S (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (CmpInA.zero (c := c) (S := S))
  | insert i s hi ih =>
    rw [sum_insert hi]
    exact (hF i (mem_insert_self i s)).add (ih fun k hk => hF k (mem_insert_of_mem hk))

theorem CmpInA.mul {F G : SA c Λ} (hF : CmpInA S F) (hG : CmpInA S G) : CmpInA S (F * G) := by
  refine ⟨hF.toCmpIn.mul hG.toCmpIn, ?_⟩
  rw [mul_ab]
  exact add_mem (add_mem (add_mem (mul_mem hF.e hG.ab) (mul_mem (tau_mem_NX hF.a) hG.b))
    (Subalgebra.smul_mem _ (mul_mem (tau_mem_NX hF.b) hG.a) _)) (mul_mem hF.ab hG.e)

theorem CmpInA.one : CmpInA S (1 : SA c Λ) := ⟨CmpIn.one, zero_mem _⟩

theorem CmpInA.of_eq_zero {F : SA c Λ} (hF : F = 0) : CmpInA S F := hF ▸ CmpInA.zero

end CmpInA

section Prim

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ] {S : Set Λ}

theorem CmpInA.expS (C : Matrix Λ Λ ℂ) {F : SA c Λ} (hF : CmpInA S F) : CmpInA S (expS C F) :=
  ⟨hF.toCmpIn.expS C, expLC_mem_NX C hF.ab⟩

theorem CmpInA.EthO (C : Matrix Λ Λ ℂ) {F : OE c Λ} (hF : CmpInA S (F : SA c Λ)) :
    CmpInA S (EthO C F : SA c Λ) := by
  rw [EthO_eq_expO, coe_expO]; exact hF.expS C

theorem CmpInA.FCO (C : Matrix Λ Λ ℂ) {A B : OE c Λ} (hA : CmpInA S (A : SA c Λ))
    (hB : CmpInA S (B : SA c Λ)) : CmpInA S (FCO C A B : SA c Λ) := by
  rw [coe_FCO]; exact (((hA.expS (-C)).mul (hB.expS (-C))).expS C).sub (hA.mul hB)

theorem CmpInA.πe {F : OE c Λ} (hF : CmpInA S (F : SA c Λ)) :
    CmpInA S ((emb (bulk F) : OE c Λ) : SA c Λ) :=
  ⟨hF.toCmpIn.πe, zero_mem _⟩

theorem CmpInA.πobs {F : OE c Λ} (hF : CmpInA S (F : SA c Λ)) :
    CmpInA S (πobs F : SA c Λ) := by
  refine ⟨hF.toCmpIn.πobs, ?_⟩
  rw [coe_πobs, piobs_apply]; exact hF.ab

theorem CmpInA.toCompSub {F : OE c Λ} (hF : CmpInA S (F : SA c Λ)) :
    F ∈ (compSub (NX S) True True : Subalgebra ℂ (OE c Λ)) :=
  ⟨hF.e, hF.a, hF.b, hF.ab, fun h => absurd trivial h, fun h => absurd trivial h⟩

/-- **Finite range, all four components.** -/
theorem FCO_eq_zero_of_sepA (C : Matrix Λ Λ ℂ) {S T : Set Λ} (hST : CovSep C S T)
    {A B : OE c Λ} (hA : CmpInA S (A : SA c Λ)) (hB : CmpInA T (B : SA c Λ)) :
    FCO C A B = 0 :=
  FCO_eq_zero_far C hST.1 hST.2 hA.toCompSub hB.toCompSub

end Prim

theorem cmpInA_of_osub {P : ObsPts d L N} {S : Finset (Lam d L N)} {F : OE c (Lam d L N)}
    (h : F ∈ osub P S) : CmpInA (S : Set (Lam d L N)) (F : SA c (Lam d L N)) :=
  ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.2.2.2.1⟩

/-! ### `abSub`: products of two observable parts -/

local notation "AB" => (abSub : Subalgebra ℂ (OE c (Lam d L N)))

set_option maxHeartbeats 1000000 in
/-- **`F_C(X, Y) = 0` on `abSub` for `X_∅ = Y_∅ = 0`** (the `ab` part of `F_C(X, Y)` is
`F_C(X_∅, Y_{ab}) + F_C(X_a, Y_b) ± F_C(X_b, Y_a) + F_C(X_{ab}, Y_∅)`). -/
theorem FCO_eq_zero_of_ab (C : Matrix (Lam d L N) (Lam d L N) ℂ) {X Y : OE c (Lam d L N)}
    (hX : X ∈ AB) (hY : Y ∈ AB) (h1 : (X : SA c (Lam d L N)).e = 0)
    (h2 : (Y : SA c (Lam d L N)).e = 0) : FCO C X Y = 0 := by
  have ht : c.tau (0 : Grassmann.N (Lam d L N)) = 0 := map_zero _
  apply Subtype.ext
  rw [ZeroMemClass.coe_zero]
  refine SA.ext ?_ ?_ ?_ ?_
  · rw [SA.zero_e, FCO_e, h1, FC_zero_left]
  · have := FCO_cmp C true X Y
    simp only [cmp_true] at this
    rw [SA.zero_a, this, h1, h2, ht, FC_zero_left, FC_zero_right, add_zero]
  · have := FCO_cmp C false X Y
    simp only [cmp_false] at this
    rw [SA.zero_b, this, h1, h2, ht, FC_zero_left, FC_zero_right, add_zero]
  · rw [SA.zero_ab, FCO_ab, h1, h2, hX.1, hX.2, hY.1, hY.2, ht]
    simp only [FC_zero_left, FC_zero_right, smul_zero, add_zero]

/-- On `abSub` the product of two observable parts does not contribute. -/
theorem FCO_obs_obs_ab (C : Matrix (Lam d L N) (Lam d L N) ℂ) {A B : OE c (Lam d L N)}
    (hA : A ∈ AB) (hB : B ∈ AB) : FCO C (EthO C (πobs A)) (EthO C (πobs B)) = 0 :=
  FCO_eq_zero_of_ab C (EthO_mem_ab C (πobs_mem_ab hA)) (EthO_mem_ab C (πobs_mem_ab hB))
    (by rw [← πobs_EthO, πobs_e']) (by rw [← πobs_EthO, πobs_e'])

theorem oTo_zeroA (w : Wt) (j : ℕ) (ℓ : ℝ) : oTo w j ℓ (0 : OE c (Lam d L N)) = 0 := by
  simpa using oTo_emb w j ℓ (0 : EvR (Lam d L N)) (c := c)

theorem oTo_emb_add (w : Wt) (j : ℕ) (ℓ : ℝ) (x : EvR (Lam d L N)) (F : OE c (Lam d L N)) :
    oTo w j ℓ (emb x + F) = oTo w j ℓ F := by
  rw [oTo, oTo, map_add, πobs_emb, zero_add]

set_option maxHeartbeats 1000000 in
/-- **The observable part of `S^♯(B)` on `abSub`** sees only `F(𝔼θV^{obs}(B), 𝔼θV^∅(Λ))`
(copy of `BHO.oTo_SFO_eq`). -/
theorem oTo_SFO_eqAB (w : Wt) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) {V : OFam c d L N}
    (hV : ∀ b, V b ∈ AB) (b : Fin d → ℕ) (j' : ℕ) (ℓ₀ : ℝ) :
    oTo w j' ℓ₀ (SFO j C V b) =
      oTo w j' ℓ₀ (∑ b' ∈ blockIdx (L := L) (N := N) j, FCO C (EthO C (πobs (V b)))
        (EthO C (emb (bulk (V b')) : OE c (Lam d L N)))) := by
  have hVp : ∀ b, VprO C V b ∈ AB := fun b => EthO_mem_ab C (hV b)
  have hVL : VprLO j C V ∈ AB := Subalgebra.sum_mem _ fun b _ => hVp b
  have hΛ : (emb (bulk (VprLO j C V)) : OE c (Lam d L N)) =
      ∑ b' ∈ blockIdx (L := L) (N := N) j, EthO C (emb (bulk (V b')) : OE c (Lam d L N)) := by
    rw [VprLO, map_sum, map_sum]
    refine sum_congr rfl fun b' _ => ?_
    rw [VprO, bulk_EthO, EthO_emb]
  have hz : FCO C (πobs (VprO C V b)) (πobs (VprLO j C V)) = 0 :=
    FCO_eq_zero_of_ab C (πobs_mem_ab (hVp b)) (πobs_mem_ab hVL) (πobs_e' _) (πobs_e' _)
  have e1 : FCO C (VprO C V b) (emb (bulk (VprLO j C V))) =
      FCO C (emb (bulk (VprO C V b))) (emb (bulk (VprLO j C V))) +
        FCO C (πobs (VprO C V b)) (emb (bulk (VprLO j C V))) := by
    conv_lhs => rw [eq_emb_add_πobs (VprO C V b)]
    rw [FCO_add_left]
  have e2 : FCO C (πobs (VprO C V b)) (VprLO j C V) =
      FCO C (πobs (VprO C V b)) (emb (bulk (VprLO j C V))) +
        FCO C (πobs (VprO C V b)) (πobs (VprLO j C V)) := by
    conv_lhs => rw [eq_emb_add_πobs (VprLO j C V)]
    rw [FCO_add_right]
  set Y := FCO C (πobs (VprO C V b)) (emb (bulk (VprLO j C V)))
  have e3 : SFO j C V b = emb ((1 / 2 : ℂ) • Step2.FCE C (bulk (VprO C V b))
      (bulk (VprLO j C V))) + Y := by
    rw [SFO_eq_anch, e1, e2, hz, add_zero, FCO_emb, map_smul]
    calc (1 / 2 : ℂ) • (emb (Step2.FCE C (bulk (VprO C V b)) (bulk (VprLO j C V))) + Y) +
          (1 / 2 : ℂ) • Y
        = (1 / 2 : ℂ) • (emb (Step2.FCE C (bulk (VprO C V b)) (bulk (VprLO j C V))) :
            OE c (Lam d L N)) + ((1 / 2 : ℂ) + 1 / 2) • Y := by
          rw [smul_add, add_smul]; abel
      _ = _ := by norm_num
  rw [e3, oTo_emb_add, ← FCO_sum_right, ← hΛ, ← πobs_EthO]; rfl

/-! ### The lifted two-scale bounds (any weights) -/

section Lift

variable {w : Wt}

theorem oTj_succ_two_leA (hd : 1 ≤ d) (hL : pauliL0 d ≤ L) {j : ℕ} (hj : j < N)
    {Y : Finset (Lam d L N)} {F : SA c (Lam d L N)} (hF : CmpInA (↑Y : Set (Lam d L N)) F)
    {ℓ : ℝ} (hℓ : 0 < ℓ) :
    oTj d L w (j + 1) (2 * ℓ) F ≤ ENNReal.ofReal (Step2.pq d ^ nb j Y) * oTj d L w j ℓ F :=
  oNorm_le_cmp (Step2.Tj_succ_two_le hd hL hj hF.e hℓ) (Step2.Tj_succ_two_le hd hL hj hF.a hℓ)
    (Step2.Tj_succ_two_le hd hL hj hF.b hℓ) (Step2.Tj_succ_two_le hd hL hj hF.ab hℓ)

theorem oTj_EthO_le2A (hd : 1 ≤ d) (hL : pauliL0 d ≤ L) {j : ℕ} (hj : j < N) {ℓ ℓ' ℓC : ℝ}
    (hℓ' : 0 < ℓ') (hℓC : 0 < ℓC) (hsum : ℓ' + ℓC ≤ 2 * ℓ)
    {C : Matrix (Lam d L N) (Lam d L N) ℂ} (hC : Step2.GoodCov2 j ℓC C)
    {Y : Finset (Lam d L N)} {F : OE c (Lam d L N)}
    (hF : CmpInA (↑Y : Set (Lam d L N)) (F : SA c (Lam d L N))) :
    oTj d L w (j + 1) ℓ' (EthO C F : SA c (Lam d L N)) ≤
      ENNReal.ofReal (Step2.pq d ^ nb j Y) * oTj d L w j ℓ (F : SA c (Lam d L N)) := by
  refine oNorm_le_cmp ?_ ?_ ?_ ?_
  · rw [EthO_e]; exact Step2.EthE_succ_le2 hd hL hj hℓ' hℓC hsum hC hF.e
  · rw [EthO_a]; exact Step2.EthE_succ_le2 hd hL hj hℓ' hℓC hsum hC hF.a
  · rw [EthO_b]; exact Step2.EthE_succ_le2 hd hL hj hℓ' hℓC hsum hC hF.b
  · rw [EthO_ab]; exact Step2.EthE_succ_le2 hd hL hj hℓ' hℓC hsum hC hF.ab

theorem oTo_EthO_le2A (hd : 1 ≤ d) (hL : pauliL0 d ≤ L) {j : ℕ} (hj : j < N) {ℓ ℓ' ℓC : ℝ}
    (hℓ' : 0 < ℓ') (hℓC : 0 < ℓC) (hsum : ℓ' + ℓC ≤ 2 * ℓ)
    {C : Matrix (Lam d L N) (Lam d L N) ℂ} (hC : Step2.GoodCov2 j ℓC C)
    {Y : Finset (Lam d L N)} {F : OE c (Lam d L N)}
    (hF : CmpInA (↑Y : Set (Lam d L N)) (F : SA c (Lam d L N))) :
    oTo w (j + 1) ℓ' (EthO C F) ≤ ENNReal.ofReal (Step2.pq d ^ nb j Y) * oTo w j ℓ F := by
  rw [oTo, πobs_EthO]
  exact oTj_EthO_le2A hd hL hj hℓ' hℓC hsum hC hF.πobs

end Lift

end

end Obs2
