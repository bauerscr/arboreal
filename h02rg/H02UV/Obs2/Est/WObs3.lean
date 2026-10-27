import Obs2.Est.WObs2

/-!
# The `𝒲^{obs}` contraction, part 3: products and the one-step bound

* `oTo_mul_le0`: for `w_ab = 0`, `‖FG‖^{obs} ≤ ‖F_∅‖ ‖G‖^{obs} + ‖F‖^{obs} ‖G_∅‖` (the product of two
  observable parts only feeds the `ab` component, which is not weighted).
* `oTo_prod_sub_le`: with `‖(x_i)_∅‖ ≤ e`, `‖x_i‖^{obs} ≤ o` (`n` factors),
  `‖∏(1+x_i) - 1 - ∑x_i‖^{obs} ≤ n o ((1+e)^n - 1)`: the products are linear in the observable
  sizes, with a small factor from the bulk parts.
* **`Wnext2O_obs_le`**: the `𝒲^{obs}` one-step bound. Under the block hypotheses `BHO`, `U(1)`
  invariance of `𝒲(B)`, the support condition `𝒲(B)_a = 0` unless `a ∈ B^□` (part of `OLocS`)
  and a bulk bound `‖𝒲_{j+1}(B)_∅‖ ≤ e`:

    `‖𝒲^{obs}_{j+1}(B_+)‖_{T_{j+1}(ℓ')} ≤ K L^{-1} m_W + (1 + C_l) L^d 2c_{near}Q₁² r m_V
       + L^d o_W ((1+e)^{L^d} - 1)`,

  `o_W = (1 + C_l L^d) s^{obs}`, `s^{obs} = 2c_{near}Q₁² r m_V + Q₁ m_W` (`Wp_o`). With `e = O(r)` this
  is `‖𝒲^{obs}_{j+1}‖ ≤ (K/L + C(L) r) m_W + C(L) r m_V`: the contraction of `𝒲^{obs}`.

  Proof: `∑_{B ⊆ B_+} 𝒲_{j+1}(B) = (1 - Loc_{B_+,B_+}) S(B_+)` (`LocO2_sum_blocks`), split
  `S = S^F + S^W` into the one-loop part (bounded, `O(r m_V)`) and `S^W = ∑ 𝔼θ𝒲(B)`, which contracts by
  the pointed contraction after the expectation (`sum_EthW_subLoc`).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD ENNReal

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

theorem oTo_zero' (w : Wt) (j : ℕ) (ℓ : ℝ) : oTo w j ℓ (0 : OE c (Lam d L N)) = 0 := by
  have := oTo_algebraMap (c := c) (d := d) (L := L) (N := N) w j ℓ 0
  rwa [map_zero] at this

/-- **The sharp product rule for the observable part** (`w_ab = 0`). -/
theorem oTo_mul_le0 {w : Wt} (hw0 : w.ab = 0) {j : ℕ} {ℓ : ℝ} (hh : (0 : ℝ) < (L : ℝ) ^ j)
    (hℓ : 0 < ℓ) (F G : OE c (Lam d L N)) :
    oTo w j ℓ (F * G) ≤ Tj d (L : ℝ) j ℓ (F : SA c (Lam d L N)).e * oTo w j ℓ G +
      oTo w j ℓ F * Tj d (L : ℝ) j ℓ (G : SA c (Lam d L N)).e := by
  rw [oTo_eq_comp hw0, oTo_eq_comp hw0, oTo_eq_comp hw0, OE.mul_a, OE.mul_b]
  set fe := Tj d (L : ℝ) j ℓ (F : SA c (Lam d L N)).e
  set ge := Tj d (L : ℝ) j ℓ (G : SA c (Lam d L N)).e
  have ha : Tj d (L : ℝ) j ℓ ((F : SA c (Lam d L N)).e * (G : SA c (Lam d L N)).a +
      (F : SA c (Lam d L N)).a * (G : SA c (Lam d L N)).e) ≤
      fe * Tj d (L : ℝ) j ℓ (G : SA c (Lam d L N)).a +
        Tj d (L : ℝ) j ℓ (F : SA c (Lam d L N)).a * ge :=
    (tNorm_add_le _ _).trans (add_le_add (tNorm_mul_le hh hℓ _ _) (tNorm_mul_le hh hℓ _ _))
  have hb : Tj d (L : ℝ) j ℓ ((F : SA c (Lam d L N)).e * (G : SA c (Lam d L N)).b +
      (F : SA c (Lam d L N)).b * (G : SA c (Lam d L N)).e) ≤
      fe * Tj d (L : ℝ) j ℓ (G : SA c (Lam d L N)).b +
        Tj d (L : ℝ) j ℓ (F : SA c (Lam d L N)).b * ge :=
    (tNorm_add_le _ _).trans (add_le_add (tNorm_mul_le hh hℓ _ _) (tNorm_mul_le hh hℓ _ _))
  calc w.a * Tj d (L : ℝ) j ℓ _ + w.b * Tj d (L : ℝ) j ℓ _
      ≤ w.a * (fe * Tj d (L : ℝ) j ℓ (G : SA c (Lam d L N)).a +
          Tj d (L : ℝ) j ℓ (F : SA c (Lam d L N)).a * ge) +
        w.b * (fe * Tj d (L : ℝ) j ℓ (G : SA c (Lam d L N)).b +
          Tj d (L : ℝ) j ℓ (F : SA c (Lam d L N)).b * ge) :=
        add_le_add (mul_le_mul_right ha _) (mul_le_mul_right hb _)
    _ = _ := by ring

theorem e_one_add_mul (x P : OE c (Lam d L N)) :
    (((1 + x) * P : OE c (Lam d L N)) : SA c (Lam d L N)).e - 1 =
      ((P : SA c (Lam d L N)).e - 1) + (x : SA c (Lam d L N)).e * (P : SA c (Lam d L N)).e := by
  rw [OE.mul_e, AddMemClass.coe_add, OneMemClass.coe_one, SA.add_e, SA.one_e, add_mul, one_mul]
  abel

theorem real_step_C {n o e : ℝ} {k : ℕ} (hn : 0 ≤ n) (ho : 0 ≤ o) (he : 0 ≤ e) :
    n * o * ((1 + e) ^ k - 1) + (e * (n * o * (1 + e) ^ k) + o * ((1 + e) ^ k - 1)) ≤
      (n + 1) * o * ((1 + e) ^ (k + 1) - 1) := by
  have h : (n + 1) * o * ((1 + e) ^ (k + 1) - 1) -
      (n * o * ((1 + e) ^ k - 1) + (e * (n * o * (1 + e) ^ k) + o * ((1 + e) ^ k - 1))) =
      o * e * (1 + e) ^ k := by ring
  have : 0 ≤ o * e * (1 + e) ^ k := by positivity
  linarith

/-- **Products of block elements: linear in the observable sizes.** -/
theorem oTo_prod_sub_le {w : Wt} (hw0 : w.ab = 0) {j : ℕ} {ℓ : ℝ} (hh : (0 : ℝ) < (L : ℝ) ^ j)
    (hℓ : 0 < ℓ) {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → OE c (Lam d L N))
    {e o : ℝ} (he : 0 ≤ e) (ho : 0 ≤ o)
    (hxe : ∀ i ∈ s, Tj d (L : ℝ) j ℓ (x i : SA c (Lam d L N)).e ≤ ENNReal.ofReal e)
    (hxo : ∀ i ∈ s, oTo w j ℓ (x i) ≤ ENNReal.ofReal o) :
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
      (fun i hi => hxo i (mem_insert_of_mem hi))
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
        (oTo_mul_le0 hw0 hh hℓ (x a) _).trans
          (le_ofReal_add hB0 (mul_nonneg ho hq0) (le_ofReal_mul he hae hP1)
            (le_ofReal_mul ho hao hP1e))
      refine (oTo_add_le w _ _ _ _).trans ((le_ofReal_add hA0
        (add_nonneg hB0 (mul_nonneg ho hq0)) ihC hm).trans
        (ENNReal.ofReal_le_ofReal ?_))
      push_cast
      exact real_step_C (Nat.cast_nonneg _) ho he

/-! ### The one-step bound -/

/-- The constant of the observable part of `𝒲_{j+1}(B)` (`Wp_o`). -/
def oWc (d L : ℕ) (r mV mW Cl : ℝ) : ℝ := sO d L r mV mW + Cl * ((L : ℝ) ^ d * sO d L r mV mW)

/-- The one-loop part `S^F = ∑_{B ∈ s} ½ F(V'_B, V'(Λ))` of `S(B_+)`. -/
def SFo (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V : OFam c d L N)
    (s : Finset (Fin d → ℕ)) : OE c (Lam d L N) :=
  ∑ b ∈ s, SFO j C V b

/-- The `𝒲` part `S^W = ∑_{B ∈ s} 𝔼θ𝒲(B)` of `S(B_+)`. -/
def SWo (C : Matrix (Lam d L N) (Lam d L N) ℂ) (W : OFam c d L N) (s : Finset (Fin d → ℕ)) :
    OE c (Lam d L N) :=
  ∑ b ∈ s, EthO C (W b)

/-- `∑_{B ⊆ B_+} 𝒲_{j+1}(B) = (1 - Loc)S^F + (1 - Loc)S^W`. -/
theorem sum_WpO_eq (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : OFam c d L N) (c' : Fin d → ℕ) :
    ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'), WpO P j C V W b =
      (SFo j C V (blocks j (blockSet (L := L) (N := N) (j + 1) c')) -
        LocO2 P (blockSet (j + 1) c') (blockSet (j + 1) c')
          (SFo j C V (blocks j (blockSet (L := L) (N := N) (j + 1) c')))) +
      (SWo C W (blocks j (blockSet (L := L) (N := N) (j + 1) c')) -
        LocO2 P (blockSet (j + 1) c') (blockSet (j + 1) c')
          (SWo C W (blocks j (blockSet (L := L) (N := N) (j + 1) c')))) := by
  have hBp : ∀ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
      Step2.Bp (L := L) (N := N) j b = blockSet (j + 1) c' := fun b hb => by
    obtain ⟨hb1, hb2⟩ := mem_blocks_blockSet_succ.1 hb
    rw [Step2.Bp, clo_blockSet hb1, hb2]
  have e1 : ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'), WpO P j C V W b =
      ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'), SbO j C V W b -
        ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
          LocO2 P (blockSet (j + 1) c') (blockSet j b) (SXO j C V W (blockSet (j + 1) c')) := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun b hb => ?_
    rw [WpO, LSO, hBp b hb]
  have hpol : IsPolymer j (blockSet (L := L) (N := N) (j + 1) c') :=
    IsPolymer.of_succ (isPolymer_blockSet (j + 1) c')
  have e2 : ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'), SbO j C V W b =
      SFo j C V (blocks j (blockSet (L := L) (N := N) (j + 1) c')) +
        SWo C W (blocks j (blockSet (L := L) (N := N) (j + 1) c')) := by
    rw [SFo, SWo, ← sum_add_distrib]; rfl
  rw [e1, LocO2_sum_blocks P hpol, SXO, e2, map_add]; abel

/-- **The `𝒲^{obs}` one-step bound.** -/
theorem Wnext2O_obs_le (d : ℕ) (hd : 1 ≤ d) : ∃ K : ℝ, 0 ≤ K ∧ ∃ L₀ : ℕ,
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∀ (N : ℕ) (c : Obs.Case) (P : ObsPts d L N) (j : ℕ)
    (ℓ ℓ' ℓC : ℝ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V W : OFam c d L N) (Kc : OAct c d L N) (w : Wt)
    (r mV mW k Cl cS e : ℝ), BHO P j ℓ ℓ' ℓC C V W Kc w r mV mW k Cl cS → ℓC ≤ ℓ → 0 ≤ e →
    (∀ b, IsSymS (W b : SA c (Lam d L N))) →
    (∀ b, P.a ∉ nbhd j (blockSet (L := L) (N := N) j b) → (W b : SA c (Lam d L N)).a = 0) →
    (∀ b, P.b ∉ nbhd j (blockSet (L := L) (N := N) j b) → (W b : SA c (Lam d L N)).b = 0) →
    (∀ b ∈ blockIdx (L := L) (N := N) j,
      Tj d (L : ℝ) (j + 1) ℓ' (WpO P j C V W b : SA c (Lam d L N)).e ≤ ENNReal.ofReal e) →
    ∀ c' ∈ blockIdx (L := L) (N := N) (j + 1),
      oTo w (j + 1) ℓ' (Wnext2O P j C V W c') ≤
        ENNReal.ofReal (K / L * mW +
          (1 + Cl) * ((L : ℝ) ^ d * (Step2.cNear d L * (2 * Step2.Q1 d ^ 2 * (r * mV)))) +
          (L : ℝ) ^ d * oWc d L r mV mW Cl * ((1 + e) ^ (L ^ d) - 1)) := by
  classical
  obtain ⟨K, hK, L₀, hW⟩ := sum_EthW_subLoc d hd
  refine ⟨K, hK, L₀, ?_⟩
  intro L _ hL₀ N c P j ℓ ℓ' ℓC C V W Kc w r mV mW k Cl cS e H hCℓ he hWs hWa hWb hWe c' hc'
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
  have hSFmem : CmpIn (nbhd (j + 1) X : Set (Lam d L N)) (SFo j C V (blocks j X) : SA c (Lam d L N)) := by
    rw [SFo, AddSubmonoidClass.coe_finsetSum]
    refine CmpIn.sum _ fun b hb => ?_
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
    have hloc := H.hloc (j + 1) H.hjN ℓ' H.hℓ' X X hXs subset_rfl _ hSFmem
    refine (add_le_add hSF (hloc.trans (mul_le_mul_right hSF _))).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul hCl, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1; ring
  -- the `𝒲` part
  have hSWL := hW L H.hL8 hL₀ N j H.hjN ℓ ℓ' ℓC H.hℓ H.hℓ' H.hℓC H.hsum hCℓ C H.hC c P w H.hw0 X
    hXne (blocks j X) hsI W mW hmW (fun b _ => H.hWl b) (fun b _ => hWs b) (fun b _ => hWa b)
    (fun b _ => hWb b) (fun b hb => H.hWm b (hsI hb))
  -- the products
  have hoW : 0 ≤ oWc d L r mV mW Cl := by
    unfold oWc; have := H.hsO; positivity
  have hprod := (oTo_prod_sub_le H.hw0 hh' H.hℓ' (blocks j X) (WpO P j C V W) he hoW
    (fun b hb => hWe b (hsI hb)) (fun b hb => H.Wp_o (hsI hb))).2
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
