import Obs2.Est.WObs3
import Obs2.Est.EstBlockAB
import Obs2.Est.LinBoundAB

/-!
# The `𝒲^{obs}` contraction on the `σ_aσ_b` sector (`ab` copy of `Obs2.Est.WObs1–3`)

In `∑_{B ⊆ B_+} 𝒲_{j+1}(B) = (1 - Loc_{B_+,B_+}) S(B_+)` the localisation acts **after** the
expectation. For the one-point parts this is the pointed contraction `Obs2.ecc_pt_contract`
(`WObs1`, `WObs2`: the pointed `loc^p` does not depend on the set). For the `ab` part the
barycentric `loc^{ab}_X` depends on the `(j+1)`-set `X = B_+` (base point and interpolation
weights), and the corresponding estimate is **not** a copy of `WObs1`. It is isolated as the
hypothesis

* **`EthSubLocAB d`**: for `G ∈ 𝒩(B^□)` with `a, b ∈ B^□`, `B ∩ {a,b} ≠ ∅`, `U(1)`-invariant
  (`IsSym`), and a small `(j+1)`-set `X ⊇ B`,
  `‖𝔼θG - loc^{ab}_{X,X}(𝔼θG)‖_{T_{j+1}(ℓ')} ≤ K L^{-1} ‖G‖_{T_j(ℓ)}`.

From it, mechanically:

* `EthO_subLoc_contractAB`, `sum_EthW_subLocAB` (copies of `WObs2`);
* `oTo_prod_sub_leAB` (copy of `oTo_prod_sub_le`, with the linear product rule `oTo_mul_ab` on
  `abSub` in place of `oTo_mul_le0`);
* **`Wnext2O_obs_leAB`**: the `𝒲^{obs}` one-step bound under `BHOAB` and anchored `𝒲(B)`,
  same constants as `Obs2.Wnext2O_obs_le`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD ENNReal

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

/-- **Hypothesis: `(1 - loc^{ab}_{X,X})𝔼θ` contracts on the `ab` part of a block element.** -/
def EthSubLocAB (d : ℕ) : Prop := ∃ K : ℝ, 0 ≤ K ∧ ∃ L₀ : ℕ,
    ∀ (L : ℕ) [NeZero L], 2 ^ (d + 3) + 8 * d < L → L₀ ≤ L → ∀ N j : ℕ, j + 1 < N →
    ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ → ℓC ≤ ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓC C →
    ∀ (P : ObsPts d L N), ∀ b ∈ blockIdx (L := L) (N := N) j, ∀ X : Finset (Lam d L N),
      IsSmall (j + 1) X → blockSet (L := L) (N := N) j b ⊆ X →
      (blockSet (L := L) (N := N) j b ∩ P.pts).Nonempty →
      P.a ∈ nbhd j (blockSet (L := L) (N := N) j b) →
      P.b ∈ nbhd j (blockSet (L := L) (N := N) j b) →
    ∀ G ∈ NX (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N)), IsSym G →
      Tj d (L : ℝ) (j + 1) ℓ' (ECC C (theta G) - locABtXY P X X (ECC C (theta G))) ≤
        ENNReal.ofReal (K / L) * Tj d (L : ℝ) j ℓ G

local notation "AB" => (abSub : Subalgebra ℂ (OE c (Lam d L N)))

/-- **`(1 - Loc_{X,X})𝔼θ` contracts on an anchored `ab` block element** (from `EthSubLocAB`). -/
theorem EthO_subLoc_contractAB (d : ℕ) (hE : EthSubLocAB d) : ∃ K : ℝ, 0 ≤ K ∧ ∃ L₀ : ℕ,
    ∀ (L : ℕ) [NeZero L], 2 ^ (d + 3) + 8 * d < L → L₀ ≤ L → ∀ N j : ℕ, j + 1 < N →
    ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ → ℓC ≤ ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓC C →
    ∀ (c : Obs.Case) (P : ObsPts d L N) (w : Wt),
    ∀ b ∈ blockIdx (L := L) (N := N) j, ∀ X : Finset (Lam d L N), IsSmall (j + 1) X →
      blockSet (L := L) (N := N) j b ⊆ X →
    ∀ F : OE c (Lam d L N),
      F ∈ (anc P (blockSet (L := L) (N := N) j b) : Subalgebra ℂ (OE c (Lam d L N))) →
      (F : SA c (Lam d L N)).ab ∈ NX (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N)) →
      IsSymS (F : SA c (Lam d L N)) →
      (P.a ∉ nbhd j (blockSet (L := L) (N := N) j b) → (F : SA c (Lam d L N)).ab = 0) →
      (P.b ∉ nbhd j (blockSet (L := L) (N := N) j b) → (F : SA c (Lam d L N)).ab = 0) →
      oTo w (j + 1) ℓ' (EthO C F - LocO2 P X X (EthO C F)) ≤
        ENNReal.ofReal (K / L) * oTo w j ℓ F := by
  obtain ⟨K, hK, L₀, h⟩ := hE
  refine ⟨K, hK, L₀, ?_⟩
  intro L _ hL hL₀ N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum hCℓ C hC c P w b hb X hX hbX F hF hFl hsym
    ha hb'
  have hab := anchSub_ab hF
  have hm : EthO C F - LocO2 P X X (EthO C F) ∈ (abSub : Subalgebra ℂ (OE c (Lam d L N))) :=
    sub_mem (EthO_mem_ab C hab) (LocO2_mem_ab P X X (EthO_mem_ab C hab))
  rw [oTo_of_ab w _ _ hm, oTo_of_ab w _ _ hab, ab_sub_LocO2, EthO_ab]
  have key : Tj d (L : ℝ) (j + 1) ℓ' (ECC C (theta (F : SA c (Lam d L N)).ab) -
      locABtXY P X X (ECC C (theta (F : SA c (Lam d L N)).ab))) ≤
      ENNReal.ofReal (K / L) * Tj d (L : ℝ) j ℓ (F : SA c (Lam d L N)).ab := by
    by_cases hne : (blockSet (L := L) (N := N) j b ∩ P.pts).Nonempty
    · by_cases hpa : P.a ∈ nbhd j (blockSet (L := L) (N := N) j b)
      · by_cases hpb : P.b ∈ nbhd j (blockSet (L := L) (N := N) j b)
        · exact h L hL hL₀ N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum hCℓ C hC P b hb X hX hbX hne hpa hpb
            _ hFl ((hasCharge_zero_iff _).1 (charges_of_isSymS hsym).2.2)
        · rw [hb' hpb, map_zero, map_zero, locABtXY_zero, sub_zero, Step.Tj_zero]
          exact zero_le
      · rw [ha hpa, map_zero, map_zero, locABtXY_zero, sub_zero, Step.Tj_zero]
        exact zero_le
    · rw [hF.2.2 hne, map_zero, map_zero, locABtXY_zero, sub_zero, Step.Tj_zero]
      exact zero_le
  calc w.ab * Tj d (L : ℝ) (j + 1) ℓ' _ ≤
      w.ab * (ENNReal.ofReal (K / L) * Tj d (L : ℝ) j ℓ (F : SA c (Lam d L N)).ab) := by
        gcongr
    _ = _ := by ring

/-- **The `𝒲` part of `S(B_+)` on the `ab` sector**: `‖S^W - Loc_{X,X}S^W‖^{obs} ≤ 2cK L^{-1} m_W`. -/
theorem sum_EthW_subLocAB (d : ℕ) (hE : EthSubLocAB d) : ∃ K : ℝ, 0 ≤ K ∧ ∃ L₀ : ℕ,
    ∀ (L : ℕ) [NeZero L], 2 ^ (d + 3) + 8 * d < L → L₀ ≤ L → ∀ N j : ℕ, j + 1 < N →
    ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ → ℓC ≤ ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓC C →
    ∀ (c : Obs.Case) (P : ObsPts d L N) (w : Wt),
    ∀ X : Finset (Lam d L N), IsSmall (j + 1) X → ∀ s : Finset (Fin d → ℕ),
      s ⊆ blockIdx (L := L) (N := N) j → (∀ b ∈ s, blockSet (L := L) (N := N) j b ⊆ X) →
    ∀ (Wf : (Fin d → ℕ) → OE c (Lam d L N)) (mW : ℝ),
      0 ≤ mW →
      (∀ b ∈ s, Wf b ∈ (anc P (blockSet (L := L) (N := N) j b) :
        Subalgebra ℂ (OE c (Lam d L N)))) →
      (∀ b ∈ s, (Wf b : SA c (Lam d L N)).ab ∈
        NX (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N))) →
      (∀ b ∈ s, IsSymS (Wf b : SA c (Lam d L N))) →
      (∀ b ∈ s, P.a ∉ nbhd j (blockSet (L := L) (N := N) j b) → (Wf b : SA c (Lam d L N)).ab = 0) →
      (∀ b ∈ s, P.b ∉ nbhd j (blockSet (L := L) (N := N) j b) → (Wf b : SA c (Lam d L N)).ab = 0) →
      (∀ b ∈ s, oTo w j ℓ (Wf b) ≤ ENNReal.ofReal mW) →
      oTo w (j + 1) ℓ' ((∑ b ∈ s, EthO C (Wf b)) - LocO2 P X X (∑ b ∈ s, EthO C (Wf b))) ≤
        ENNReal.ofReal (K / L * mW) := by
  classical
  obtain ⟨K, hK, L₀, h⟩ := EthO_subLoc_contractAB d hE
  obtain ⟨cn, hcn⟩ := card_blocks_near d
  refine ⟨K * (2 * cn), by positivity, L₀, ?_⟩
  intro L _ hL hL₀ N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum hCℓ C hC c P w X hX s hs hsX Wf mW hmW
    hWan hWl hWs hWa hWb hWm
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  rw [map_sum, ← sum_sub_distrib]
  refine (oTo_sum_le w _ _ _ _).trans ?_
  set near : Finset (Fin d → ℕ) := s.filter (fun b => P.a ∈ nbhd j (blockSet (L := L) (N := N) j b) ∨
    P.b ∈ nbhd j (blockSet (L := L) (N := N) j b)) with hnear
  have hcard : (near.card : ℝ) ≤ 2 * cn := by
    have h1 : near.card ≤ (s.filter (fun b => P.a ∈ nbhd j (blockSet (L := L) (N := N) j b))).card +
        (s.filter (fun b => P.b ∈ nbhd j (blockSet (L := L) (N := N) j b))).card := by
      rw [hnear, filter_or]; exact card_union_le _ _
    have h2 := hcn L N j P.a s hs
    have h3 := hcn L N j P.b s hs
    have : near.card ≤ 2 * cn := by omega
    exact_mod_cast this
  have hterm : ∀ b ∈ s, oTo w (j + 1) ℓ' (EthO C (Wf b) - LocO2 P X X (EthO C (Wf b))) ≤
      (if b ∈ near then ENNReal.ofReal (K / L * mW) else 0) := by
    intro b hb
    have hc := h L hL hL₀ N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum hCℓ C hC c P w b (hs hb) X hX (hsX b hb)
      (Wf b) (hWan b hb) (hWl b hb) (hWs b hb) (hWa b hb) (hWb b hb)
    split_ifs with hn
    · exact hc.trans (by
        rw [ENNReal.ofReal_mul (by positivity)]; exact mul_le_mul_right (hWm b hb) _)
    · have hn' : P.a ∉ nbhd j (blockSet (L := L) (N := N) j b) ∧
          P.b ∉ nbhd j (blockSet (L := L) (N := N) j b) := by
        rw [hnear, mem_filter] at hn; push_neg at hn; exact hn hb
      have h0 : oTo w j ℓ (Wf b) = 0 := by
        rw [oTo_of_ab w j ℓ (anchSub_ab (hWan b hb)), hWa b hb hn'.1, Tj0]; simp
      rw [h0, mul_zero] at hc; exact hc
  refine (sum_le_sum hterm).trans ?_
  rw [← sum_filter]
  refine (le_ofReal_sum_const _ (by positivity) fun _ _ => le_rfl).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hfil : s.filter (fun b => b ∈ near) = near := by
    ext b; simp only [mem_filter, hnear]; tauto
  rw [hfil]
  calc (near.card : ℝ) * (K / L * mW) ≤ 2 * cn * (K / L * mW) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = K * (2 * cn) / L * mW := by ring

/-- **Products of block elements: linear in the observable sizes.** -/
theorem oTo_prod_sub_leAB {w : Wt} {j : ℕ} {ℓ : ℝ} (hh : (0 : ℝ) < (L : ℝ) ^ j)
    (hℓ : 0 < ℓ) {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → OE c (Lam d L N))
    {e o : ℝ} (he : 0 ≤ e) (ho : 0 ≤ o)
    (hxe : ∀ i ∈ s, Tj d (L : ℝ) j ℓ (x i : SA c (Lam d L N)).e ≤ ENNReal.ofReal e)
    (hxo : ∀ i ∈ s, oTo w j ℓ (x i) ≤ ENNReal.ofReal o)
    (hxab : ∀ i ∈ s, x i ∈ (abSub : Subalgebra ℂ (OE c (Lam d L N)))) :
    Tj d (L : ℝ) j ℓ (((∏ i ∈ s, (1 + x i) : OE c (Lam d L N)) : SA c (Lam d L N)).e - 1) ≤
      ENNReal.ofReal ((1 + e) ^ s.card - 1) ∧
    oTo w j ℓ (∏ i ∈ s, (1 + x i) - 1 - ∑ i ∈ s, x i) ≤
      ENNReal.ofReal (s.card * o * ((1 + e) ^ s.card - 1)) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨?_, ?_⟩
    · rw [prod_empty, OneMemClass.coe_one, SA.one_e, sub_self, Tj0]; exact zero_le
    · rw [prod_empty, sum_empty, sub_self, sub_zero, oTo_zero']; exact zero_le
  | insert a s ha ih =>
    obtain ⟨ihA, ihC⟩ := ih (fun i hi => hxe i (mem_insert_of_mem hi))
      (fun i hi => hxo i (mem_insert_of_mem hi)) (fun i hi => hxab i (mem_insert_of_mem hi))
    have hae := hxe a (mem_insert_self a s)
    have hao := hxo a (mem_insert_self a s)
    have hq : (1 : ℝ) ≤ (1 + e) ^ s.card := one_le_pow₀ (by linarith)
    have hq0 : (0 : ℝ) ≤ (1 + e) ^ s.card - 1 := by linarith
    have hco : (0 : ℝ) ≤ s.card * o := mul_nonneg (Nat.cast_nonneg _) ho
    have hpe : (0 : ℝ) ≤ (1 + e) ^ s.card := pow_nonneg (by linarith) _
    have hA0 : (0 : ℝ) ≤ s.card * o * ((1 + e) ^ s.card - 1) := mul_nonneg hco hq0
    have hB0 : (0 : ℝ) ≤ e * (s.card * o * (1 + e) ^ s.card) := mul_nonneg he (mul_nonneg hco hpe)
    -- `‖P_∅‖ ≤ (1+e)^n`
    have hPe : Tj d (L : ℝ) j ℓ ((∏ i ∈ s, (1 + x i) : OE c (Lam d L N)) : SA c (Lam d L N)).e ≤
        ENNReal.ofReal ((1 + e) ^ s.card) := by
      have e1 : ((∏ i ∈ s, (1 + x i) : OE c (Lam d L N)) : SA c (Lam d L N)).e =
          (((∏ i ∈ s, (1 + x i) : OE c (Lam d L N)) : SA c (Lam d L N)).e - 1) + 1 :=
        (sub_add_cancel _ _).symm
      rw [e1]
      refine (tNorm_add_le _ _).trans ((add_le_add ihA (tNorm_one_le hh hℓ)).trans (le_of_eq ?_))
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add hq0 zero_le_one]; congr 1; ring
    rw [prod_insert ha, sum_insert ha, card_insert_of_notMem ha]
    refine ⟨?_, ?_⟩
    · rw [e_one_add_mul]
      have h2 : Tj d (L : ℝ) j ℓ ((x a : SA c (Lam d L N)).e *
          ((∏ i ∈ s, (1 + x i) : OE c (Lam d L N)) : SA c (Lam d L N)).e) ≤
          ENNReal.ofReal (e * (1 + e) ^ s.card) :=
        (tNorm_mul_le hh hℓ _ _).trans (le_ofReal_mul he hae hPe)
      refine (tNorm_add_le _ _).trans ((le_ofReal_add hq0 (mul_nonneg he hpe) ihA h2).trans
        (ENNReal.ofReal_le_ofReal (le_of_eq ?_)))
      ring
    · -- the observable part
      have eQ : (1 + x a) * (∏ i ∈ s, (1 + x i)) - 1 - (x a + ∑ i ∈ s, x i) =
          ((∏ i ∈ s, (1 + x i)) - 1 - ∑ i ∈ s, x i) + x a * ((∏ i ∈ s, (1 + x i)) - 1) := by ring
      rw [eQ]
      have hP1 : oTo w j ℓ ((∏ i ∈ s, (1 + x i)) - 1) ≤
          ENNReal.ofReal (s.card * o * (1 + e) ^ s.card) := by
        have eP : (∏ i ∈ s, (1 + x i)) - 1 =
            ((∏ i ∈ s, (1 + x i)) - 1 - ∑ i ∈ s, x i) + ∑ i ∈ s, x i := by ring
        rw [eP]
        have hsum : oTo w j ℓ (∑ i ∈ s, x i) ≤ ENNReal.ofReal (s.card * o) :=
          (oTo_sum_le w _ _ _ _).trans
            (le_ofReal_sum_const _ ho fun i hi => hxo i (mem_insert_of_mem hi))
        refine (oTo_add_le w _ _ _ _).trans ((le_ofReal_add hA0 hco ihC hsum).trans
          (ENNReal.ofReal_le_ofReal (le_of_eq ?_)))
        ring
      have hP1e : Tj d (L : ℝ) j ℓ ((((∏ i ∈ s, (1 + x i)) - 1 : OE c (Lam d L N)) :
          SA c (Lam d L N)).e) ≤ ENNReal.ofReal ((1 + e) ^ s.card - 1) := by
        rw [AddSubgroupClass.coe_sub, OneMemClass.coe_one, SA.sub_e, SA.one_e]; exact ihA
      have hm : oTo w j ℓ (x a * ((∏ i ∈ s, (1 + x i)) - 1)) ≤
          ENNReal.ofReal (e * (s.card * o * (1 + e) ^ s.card) + o * ((1 + e) ^ s.card - 1)) :=
        (oTo_mul_ab w hh hℓ (hxab a (mem_insert_self a s))
          (sub_mem (prod_mem fun i hi => add_mem (one_mem _) (hxab i (mem_insert_of_mem hi)))
            (one_mem _))).trans
          (le_ofReal_add hB0 (mul_nonneg ho hq0) (le_ofReal_mul he hae hP1)
            (le_ofReal_mul ho hao hP1e))
      refine (oTo_add_le w _ _ _ _).trans ((le_ofReal_add hA0
        (add_nonneg hB0 (mul_nonneg ho hq0)) ihC hm).trans
        (ENNReal.ofReal_le_ofReal ?_))
      push_cast
      exact real_step_C (Nat.cast_nonneg _) ho he

/-- **The `𝒲^{obs}` one-step bound.** -/
theorem Wnext2O_obs_leAB (d : ℕ) (hE : EthSubLocAB d) : ∃ K : ℝ, 0 ≤ K ∧ ∃ L₀ : ℕ,
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∀ (N : ℕ) (c : Obs.Case) (P : ObsPts d L N) (j : ℕ)
    (ℓ ℓ' ℓC : ℝ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V W : OFam c d L N) (Kc : OAct c d L N) (w : Wt)
    (r mV mW k Cl cS e : ℝ), BHOAB P j ℓ ℓ' ℓC C V W Kc w r mV mW k Cl cS → ℓC ≤ ℓ → 0 ≤ e →
    (∀ b, IsSymS (W b : SA c (Lam d L N))) →
    (∀ b, W b ∈ (anc P (blockSet (L := L) (N := N) j b) : Subalgebra ℂ (OE c (Lam d L N)))) →
    (∀ b, P.a ∉ nbhd j (blockSet (L := L) (N := N) j b) → (W b : SA c (Lam d L N)).ab = 0) →
    (∀ b, P.b ∉ nbhd j (blockSet (L := L) (N := N) j b) → (W b : SA c (Lam d L N)).ab = 0) →
    (∀ b ∈ blockIdx (L := L) (N := N) j,
      Tj d (L : ℝ) (j + 1) ℓ' (WpO P j C V W b : SA c (Lam d L N)).e ≤ ENNReal.ofReal e) →
    ∀ c' ∈ blockIdx (L := L) (N := N) (j + 1),
      oTo w (j + 1) ℓ' (Wnext2O P j C V W c') ≤
        ENNReal.ofReal (K / L * mW +
          (1 + Cl) * ((L : ℝ) ^ d * (Step2.cNear d L * (2 * Step2.Q1 d ^ 2 * (r * mV)))) +
          (L : ℝ) ^ d * oWc d L r mV mW Cl * ((1 + e) ^ (L ^ d) - 1)) := by
  classical
  obtain ⟨K, hK, L₀, hW⟩ := sum_EthW_subLocAB d hE
  refine ⟨K, hK, L₀, ?_⟩
  intro L _ hL₀ N c P j ℓ ℓ' ℓC C V W Kc w r mV mW k Cl cS e H hCℓ he hWs hWan hWa hWb hWe c' hc'
  have hL0 := H.hL0
  have hQ := H.hQ1; have hr := H.hr; have hmV := H.hmV; have hmW := H.hmW; have hCl := H.hCl
  have hcN := H.hcNear
  have hh' : (0 : ℝ) < (L : ℝ) ^ (j + 1) := pow_pos hL0 _
  have hlin := sum_WpO_eq P j C V W c'
  have hBp : ∀ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
      Step2.Bp (L := L) (N := N) j b = blockSet (j + 1) c' := fun b hb => by
    obtain ⟨hb1, hb2⟩ := mem_blocks_blockSet_succ.1 hb
    rw [Step2.Bp, clo_blockSet hb1, hb2]
  have hXne : (blockSet (L := L) (N := N) (j + 1) c').Nonempty := by
    obtain ⟨x, -, hx⟩ := mem_image.1 hc'
    exact ⟨x, mem_blockSet.2 hx⟩
  have hnL : (blocks j (blockSet (L := L) (N := N) (j + 1) c')).card ≤ L ^ d := by
    have := nb_blockSet_succ_le (L := L) (N := N) j c'
    unfold nb at this; exact this
  have hns : ((blocks j (blockSet (L := L) (N := N) (j + 1) c')).card : ℝ) ≤ (L : ℝ) ^ d := by
    exact_mod_cast hnL
  have hsI : blocks j (blockSet (L := L) (N := N) (j + 1) c') ⊆ blockIdx (L := L) (N := N) j :=
    fun b hb => mem_blockIdx_of_mem_blocks hb
  generalize hX : blockSet (L := L) (N := N) (j + 1) c' = X at hlin hBp hXne hnL hns hsI
  have hXs : IsSmall (j + 1) X := hX ▸ isSmall_blockSet_of_mem hc'
  -- the one-loop part
  have hOab : OAbS (K := (0 : OAct c d L N)) j V W := ⟨H.hVab, H.hWab, fun _ _ => zero_mem _⟩
  have hSFab : SFo j C V (blocks j X) ∈ (abSub : Subalgebra ℂ (OE c (Lam d L N))) := by
    rw [SFo]
    refine Subalgebra.sum_mem _ fun b _ => ?_
    have e : SFO j C V b = SbO j C V W b - EthO C (W b) := by
      rw [SbO, add_sub_cancel_right]
    rw [e]; exact sub_mem (hOab.Sb_ab b) (EthO_mem_ab C (H.hWab b))
  have hSFmem : CmpInA (nbhd (j + 1) X : Set (Lam d L N)) (SFo j C V (blocks j X) : SA c (Lam d L N)) := by
    rw [SFo, AddSubmonoidClass.coe_finsetSum]
    refine CmpInA.sum _ fun b hb => ?_
    have hb' := hsI hb
    have e : SFO j C V b = SbO j C V W b - EthO C (W b) := by
      rw [SbO, add_sub_cancel_right]
    rw [e, AddSubgroupClass.coe_sub]
    have h1 := H.Sb_mem hb'
    have h2 := ((H.hWl b).EthO C).mono (H.nbhd_block_sub (Step2.mem_nearSet_self hb'))
    rw [hBp b hb] at h1 h2
    exact h1.sub h2
  have hSF : oTo w (j + 1) ℓ' (SFo j C V (blocks j X)) ≤
      ENNReal.ofReal ((L : ℝ) ^ d * (Step2.cNear d L * (2 * Step2.Q1 d ^ 2 * (r * mV)))) := by
    rw [SFo]
    exact (oTo_sum_le w _ _ _ _).trans ((le_ofReal_sum_const _ (by positivity) fun b hb =>
      H.SF_o (hsI hb)).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hns (by positivity))))
  have hSFL : oTo w (j + 1) ℓ' (SFo j C V (blocks j X) - LocO2 P X X (SFo j C V (blocks j X))) ≤
      ENNReal.ofReal ((1 + Cl) *
        ((L : ℝ) ^ d * (Step2.cNear d L * (2 * Step2.Q1 d ^ 2 * (r * mV))))) := by
    refine (oTo_sub_le w _ _ _ _).trans ?_
    have hloc := H.hloc (j + 1) H.hjN ℓ' H.hℓ' X X hXs subset_rfl _ hSFab hSFmem
    refine (add_le_add hSF (hloc.trans (mul_le_mul_right hSF _))).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul hCl, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1; ring
  -- the `𝒲` part
  have hsX : ∀ b ∈ blocks j X, blockSet (L := L) (N := N) j b ⊆ X := fun b hb => by
    rw [← hBp b hb]; exact subset_clo j _
  have hSWL := hW L H.hL8 hL₀ N j H.hjN ℓ ℓ' ℓC H.hℓ H.hℓ' H.hℓC H.hsum hCℓ C H.hC c P w X
    hXs (blocks j X) hsI hsX W mW hmW (fun b _ => hWan b) (fun b _ => (H.hWl b).ab)
    (fun b _ => hWs b) (fun b _ => hWa b) (fun b _ => hWb b) (fun b hb => H.hWm b (hsI hb))
  -- the products
  have hoW : 0 ≤ oWc d L r mV mW Cl := by
    unfold oWc; have := H.hsO; positivity
  have hprod := (oTo_prod_sub_leAB hh' H.hℓ' (blocks j X) (WpO P j C V W) he hoW
    (fun b hb => hWe b (hsI hb)) (fun b hb => H.Wp_o (hsI hb))
    (fun b _ => hOab.Wp_ab (P := P) (C := C) b)).2
  have hmono : ((blocks j X).card : ℝ) * oWc d L r mV mW Cl * ((1 + e) ^ (blocks j X).card - 1) ≤
      (L : ℝ) ^ d * oWc d L r mV mW Cl * ((1 + e) ^ (L ^ d) - 1) := by
    have h1 : (1 + e) ^ (blocks j X).card ≤ (1 + e) ^ (L ^ d) := pow_le_pow_right₀ (by linarith) hnL
    have h2 : (0 : ℝ) ≤ (1 + e) ^ (blocks j X).card - 1 := by
      have := one_le_pow₀ (M₀ := ℝ) (n := (blocks j X).card) (by linarith : (1 : ℝ) ≤ 1 + e)
      linarith
    have h3 : ((blocks j X).card : ℝ) * oWc d L r mV mW Cl ≤ (L : ℝ) ^ d * oWc d L r mV mW Cl :=
      mul_le_mul_of_nonneg_right hns hoW
    calc ((blocks j X).card : ℝ) * oWc d L r mV mW Cl * ((1 + e) ^ (blocks j X).card - 1)
        ≤ (L : ℝ) ^ d * oWc d L r mV mW Cl * ((1 + e) ^ (blocks j X).card - 1) :=
          mul_le_mul_of_nonneg_right h3 h2
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hq0 : (0 : ℝ) ≤ (1 + e) ^ (L ^ d) - 1 := by
    have := one_le_pow₀ (M₀ := ℝ) (n := L ^ d) (by linarith : (1 : ℝ) ≤ 1 + e); linarith
  -- assembly
  have eW : Wnext2O P j C V W c' =
      (∏ b ∈ blocks j X, (1 + WpO P j C V W b) - 1 - ∑ b ∈ blocks j X, WpO P j C V W b) +
        ((SFo j C V (blocks j X) - LocO2 P X X (SFo j C V (blocks j X))) +
          (SWo C W (blocks j X) - LocO2 P X X (SWo C W (blocks j X)))) := by
    rw [← hlin, Wnext2O, hX]; ring
  rw [eW]
  have hA : (0 : ℝ) ≤ (L : ℝ) ^ d * oWc d L r mV mW Cl * ((1 + e) ^ (L ^ d) - 1) :=
    mul_nonneg (by positivity) hq0
  have hB : (0 : ℝ) ≤ (1 + Cl) *
      ((L : ℝ) ^ d * (Step2.cNear d L * (2 * Step2.Q1 d ^ 2 * (r * mV)))) := by positivity
  have hC' : (0 : ℝ) ≤ K / L * mW := by positivity
  refine (oTo_add_le w _ _ _ _).trans ((le_ofReal_add hA (add_nonneg hB hC')
    (hprod.trans (ENNReal.ofReal_le_ofReal hmono))
    ((oTo_add_le w _ _ _ _).trans (le_ofReal_add hB hC' hSFL hSWL))).trans
    (ENNReal.ofReal_le_ofReal (le_of_eq ?_)))
  ring

end

end Obs2
