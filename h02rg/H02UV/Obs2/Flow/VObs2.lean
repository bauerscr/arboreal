import Obs2.Flow.VObs1
import Obs2.Flow.MuHist
import Obs2.Flow.EstMu

/-!
# The `V^{obs}` recursion, part 2: the `m`-half of `lin_iter` (Case (1), the `σ_a` part)

With `V(B)_a = β_B ψ̄_a` (`β_B = m₁(V(B)_a)`, `m₁ = mass1(-1)`), the `ℓ¹` coupling
`β^{abs} = ∑_B |β_B|` obeys (**`beta_step`**, single-source weights `Obs2.wA = (1,0,0)`, so that the
observable norm is `‖F_a‖`):

  `β^{abs}_{j+1} ≤ β^{abs}_j + c C_m ℓ^{-1} k + C_m ℓ'^{-1} (2c_{near}Q₁² r ℓ β^{abs}_j + c' Q₁ m_W)`.

Since `‖V(B)_a‖_{T_j(ℓ)} = |β_B| ℓ` (`tNorm_ψ`), `m_j = ℓ_j β^{abs}_j` bounds every block and
`m_{j+1} ≤ (ℓ'/ℓ)(1 + C r) m_j + C k + C m_W`: the `m`-half of `lin_iter` with `a_j = O(r_j)`
plus the change of the field scale. The per-block one-loop pair bound with block-dependent sizes
(`pair_o'`, `FCL_o'`, `Sb_o'`) and the symmetry of `nearSet` (`sum_near_le`) replace the uniform
`m_V` of `EstBlock`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 LocObs FRD ENNReal

variable {d L N : ℕ} [NeZero L]

/-! ### The near relation is symmetric -/

/-! ### Block bounds with block-dependent sizes -/

namespace BHO

variable {c : Obs.Case} {P : ObsPts d L N} {j : ℕ} {ℓ ℓ' ℓC : ℝ}
  {C : Matrix (Lam d L N) (Lam d L N) ℂ} {V W : OFam c d L N} {K : OAct c d L N} {w : Wt}
  {r mV mW k Cl cS : ℝ} (H : BHO P j ℓ ℓ' ℓC C V W K w r mV mW k Cl cS)
  (x : (Fin d → ℕ) → ℝ) (hx0 : ∀ b, 0 ≤ x b)
  (hx : ∀ b ∈ blockIdx (L := L) (N := N) j, oTo w j ℓ (V b) ≤ ENNReal.ofReal (x b))
include H

include hx in
theorem V2_o' {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTo w (j + 1) (2 * ℓ) (V b) ≤ ENNReal.ofReal (Step2.Q1 d * x b) := by
  refine (oTj_succ_two_le H.hw0 H.hd H.hLp H.hj (H.hVl b).πobs H.hℓ).trans ?_
  exact le_ofReal_mul (by linarith [H.hQ1])
    (ENNReal.ofReal_le_ofReal (Step2.pq_pow_le_Q1 H.hd H.hj.le b)) (hx b hb)

include hx hx0 in
theorem pairh_o' {b b' : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j)
    (hb' : b' ∈ blockIdx (L := L) (N := N) j) :
    oTo w (j + 1) ℓ' (FCO C (EthO C (πobs (V b)))
      (EthO C (emb (bulk (V b')) : OE c (Lam d L N)))) ≤
      ENNReal.ofReal (2 * Step2.Q1 d ^ 2 * r * x b) := by
  have hQ := H.hQ1; have hr := H.hr; have hxb := hx0 b
  refine (oTo_le w _ _ _).trans ((oTj_FCO_le H.hℓ' H.hℓC H.hsum H.hC H.hw _ _).trans ?_)
  have e : 2 * Step2.Q1 d ^ 2 * r * x b = 2 * ((Step2.Q1 d * x b) * (Step2.Q1 d * r)) := by ring
  rw [e, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  refine mul_le_mul_right (le_ofReal_mul (mul_nonneg H.hQ0 hxb) (H.V2_o' x hx hb) ?_) _
  rw [oTj_emb]; exact H.V2_e hb'

include hx hx0 in
/-- The sharp second-order part with block-dependent sizes: only the observable size of `B`
enters. -/
theorem SF_o' {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTo w (j + 1) ℓ' (SFO j C V b) ≤
      ENNReal.ofReal (Step2.cNear d L * (2 * Step2.Q1 d ^ 2 * r * x b)) := by
  classical
  have hQ := H.hQ1; have hr := H.hr; have hxb := hx0 b
  rw [oTo_SFO_eq H.hw0]
  refine (oTo_sum_le w _ _ _ _).trans ?_
  rw [← sum_filter_add_sum_filter_not (blockIdx (L := L) (N := N) j)
    (fun b' => b' ∈ Step2.nearSet (L := L) (N := N) j b)]
  rw [sum_eq_zero (s := filter (fun b' => ¬ _) _) fun b' hb' =>
    oTo_eq_zero_of_eab w _ _ H.hw0 (H.far_gen (mem_filter.1 hb').1 (mem_filter.1 hb').2
      ((H.hVl b).πobs.EthO C) (((H.hVl b').πe).EthO C)), add_zero]
  refine (le_ofReal_sum_const _ (by positivity) fun b' hb' =>
    H.pairh_o' x hx0 hx hb (mem_filter.1 hb').1).trans (ENNReal.ofReal_le_ofReal ?_)
  have hn : ((filter (fun b' => b' ∈ Step2.nearSet (L := L) (N := N) j b)
      (blockIdx (L := L) (N := N) j)).card : ℝ) ≤ Step2.cNear d L := by
    have h1 : (filter (fun b' => b' ∈ Step2.nearSet (L := L) (N := N) j b)
        (blockIdx (L := L) (N := N) j)).card ≤ (Step2.nearSet (L := L) (N := N) j b).card :=
      card_le_card fun b' hb' => (mem_filter.1 hb').2
    unfold Step2.cNear
    exact_mod_cast h1.trans (Step2.card_nearSet_le H.hj.le b hb)
  exact mul_le_mul_of_nonneg_right hn (by positivity)

include hx hx0 in
theorem Sb_o' {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) (y : ℝ) (hy0 : 0 ≤ y)
    (hy : oTo w j ℓ (W b) ≤ ENNReal.ofReal y) :
    oTo w (j + 1) ℓ' (SbO j C V W b) ≤
      ENNReal.ofReal (Step2.cNear d L * (2 * Step2.Q1 d ^ 2 * r * x b) + Step2.Q1 d * y) := by
  have hr := H.hr; have hxb := hx0 b; have hN := H.hcNear; have hQ := H.hQ0
  rw [SbO]
  refine (oTo_add_le w _ _ _ _).trans ?_
  have h2 : oTo w (j + 1) ℓ' (EthO C (W b)) ≤ ENNReal.ofReal (Step2.Q1 d * y) := by
    refine (oTo_EthO_le2 H.hw0 H.hd H.hLp H.hj H.hℓ' H.hℓC H.hsum H.hC (H.hWl b)).trans ?_
    exact le_ofReal_mul (by linarith [H.hQ1])
      (ENNReal.ofReal_le_ofReal (Step2.pq_pow_le_Q1 H.hd H.hj.le b)) hy
  exact le_ofReal_add (by positivity) (mul_nonneg H.hQ0 hy0) (H.SF_o' x hx0 hx hb) h2

end BHO

/-! ### The `m`-half -/

theorem Tj_smul_psibar (j : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) (β : ℂ) (a : Lam d L N) :
    Tj d (L : ℝ) j ℓ (β • psibar a) = ENNReal.ofReal (‖β‖ * ℓ) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  show tNorm (Dir d) (pPhi d) ((L : ℝ) ^ j) ℓ (β • psibar a) = _
  rw [Step.tNorm_smul, psibar, tNorm_ψ (pow_pos hL0 j) hℓ, ← ENNReal.ofReal_mul (norm_nonneg _)]

/-- **The `m`-half (Case (1), `σ_a`)**: one step of the `ℓ¹` coupling `∑_B |m₁(V(B)_a)|`. -/
theorem beta_step (d : ℕ) (hd : 1 ≤ d) : ∃ (Cm : ℝ) (cs cn : ℕ), 0 ≤ Cm ∧
    ∀ (L : ℕ) [NeZero L] (N : ℕ) (P : ObsPts d L N) (j : ℕ) (ℓ ℓ' ℓC : ℝ)
    (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V W : OFam .one d L N) (K : OAct .one d L N)
    (r mV mW k Cl cS : ℝ), BHO P j ℓ ℓ' ℓC C V W K Obs2.wA r mV mW k Cl cS →
    (∀ b, (V b : SA .one (Lam d L N)).a ∈ (ℂ ∙ psibar P.a)) →
    (∀ b, P.a ∉ nbhd j (blockSet (L := L) (N := N) j b) → (W b : SA .one (Lam d L N)).a = 0) →
    (∀ X, IsSmall j X → P.a ∉ nbhd j X → (K X : SA .one (Lam d L N)).a = 0) →
    ∑ c' ∈ blockIdx (L := L) (N := N) (j + 1),
        ‖mass1L (-1) (Vnext2O P j C V W K c' : SA .one (Lam d L N)).a‖ ≤
      ∑ b ∈ blockIdx (L := L) (N := N) j, ‖mass1L (-1) (V b : SA .one (Lam d L N)).a‖ +
        cs * Cm * ℓ⁻¹ * k +
        Cm * ℓ'⁻¹ * (2 * Step2.cNear d L * Step2.Q1 d ^ 2 * r * ℓ *
          ∑ b ∈ blockIdx (L := L) (N := N) j, ‖mass1L (-1) (V b : SA .one (Lam d L N)).a‖ +
          cn * Step2.Q1 d * mW) := by
  classical
  obtain ⟨Cm, hCm0, hCm⟩ := exists_mass_bound d
  obtain ⟨cs, hcs⟩ := card_small_near d
  obtain ⟨cn, hcn⟩ := card_blocks_near d
  refine ⟨Cm, cs, cn, hCm0, ?_⟩
  intro L _ N P j ℓ ℓ' ℓC C V W K r mV mW k Cl cS H hV hWa hKa
  have hQ := H.hQ1; have hr := H.hr; have hk := H.hk; have hmW := H.hmW
  have hℓ := H.hℓ; have hℓ' := H.hℓ'
  set I := blockIdx (L := L) (N := N) j
  set m := mass1L (L := L) (N := N) (d := d) (-1)
  have hm0 : ∀ r : ℂ, m (algebraMap ℂ (Alg d L N) r) = 0 := fun r => mass1_algebraMap (-1) r
  have hstep := abs_mass_step P j C V W K H.hjN m hm0 (locMass_one P.a)
  set β : ℝ := ∑ b ∈ I, ‖m (V b : SA .one (Lam d L N)).a‖ with hβ
  have hβ0 : 0 ≤ β := sum_nonneg fun _ _ => norm_nonneg _
  -- (i) the expectation of `V(B)_a`
  have hVpr : ∀ b, (VprO C V b : SA .one (Lam d L N)).a = (V b : SA .one (Lam d L N)).a := by
    intro b
    show ECC C (theta (V b : SA .one (Lam d L N)).a) = _
    rw [ECC_theta, eq_mass1_smul_of_span (hV b), map_smul, expLC_psibar]
  -- (ii) the activity term
  have hK : ∑ X ∈ smallSets (L := L) (N := N) j, ‖m (K X : SA .one (Lam d L N)).a‖ ≤
      cs * Cm * ℓ⁻¹ * k := by
    rw [← sum_filter_add_sum_filter_not (smallSets (L := L) (N := N) j)
      (fun X => P.a ∈ nbhd j X)]
    rw [sum_eq_zero (s := filter (fun X => ¬ _) _) fun X hX => by
      obtain ⟨hXs, hXa⟩ := mem_filter.1 hX
      rw [hKa X (mem_smallSets.1 hXs) hXa, map_zero, norm_zero], add_zero]
    have hX : ∀ X ∈ (smallSets (L := L) (N := N) j).filter (fun X => P.a ∈ nbhd j X),
        ‖m (K X : SA .one (Lam d L N)).a‖ ≤ Cm * ℓ⁻¹ * k := by
      intro X hX
      have hXs := mem_smallSets.1 (mem_filter.1 hX).1
      have h1 := mass1_le hCm H.hL8 H.hj hXs (H.hKl X hXs).a (-1) hℓ
      have h2 : (Tj d (L : ℝ) j ℓ (K X : SA .one (Lam d L N)).a).toReal ≤ k := by
        have := H.hKk X hXs
        rw [Obs2.oTo_wA] at this
        exact ENNReal.toReal_le_of_le_ofReal hk this
      exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
    refine (sum_le_sum hX).trans ?_
    rw [sum_const, nsmul_eq_mul]
    have hc := hcs L N j P.a
    have : (((smallSets (L := L) (N := N) j).filter (fun X => P.a ∈ nbhd j X)).card : ℝ) ≤ cs := by
      exact_mod_cast hc
    calc (((smallSets (L := L) (N := N) j).filter (fun X => P.a ∈ nbhd j X)).card : ℝ) *
          (Cm * ℓ⁻¹ * k) ≤ cs * (Cm * ℓ⁻¹ * k) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = cs * Cm * ℓ⁻¹ * k := by ring
  -- (iii) the localisation term
  set x : (Fin d → ℕ) → ℝ := fun b => ‖m (V b : SA .one (Lam d L N)).a‖ * ℓ with hxdef
  have hx0 : ∀ b, 0 ≤ x b := fun b => by positivity
  have hx : ∀ b ∈ I, oTo Obs2.wA j ℓ (V b) ≤ ENNReal.ofReal (x b) := fun b _ => by
    rw [Obs2.oTo_wA, eq_mass1_smul_of_span (hV b), Tj_smul_psibar j hℓ]
    exact le_rfl
  set y : (Fin d → ℕ) → ℝ := fun b => if P.a ∈ nbhd j (blockSet (L := L) (N := N) j b) then mW
    else 0 with hydef
  have hy0 : ∀ b, 0 ≤ y b := fun b => by simp only [hydef]; split_ifs <;> linarith
  have hy : ∀ b ∈ I, oTo Obs2.wA j ℓ (W b) ≤ ENNReal.ofReal (y b) := fun b hb => by
    simp only [hydef]
    split_ifs with h
    · exact H.hWm b hb
    · rw [Obs2.oTo_wA, hWa b h, Tj0]; exact zero_le
  have hysum : ∑ b ∈ I, y b ≤ cn * mW := by
    simp only [hydef]
    rw [← sum_filter]
    rw [sum_const, nsmul_eq_mul]
    have h1 := hcn L N j P.a I subset_rfl
    have : ((I.filter (fun b => P.a ∈ nbhd j (blockSet (L := L) (N := N) j b))).card : ℝ) ≤ cn := by
      exact_mod_cast h1
    exact mul_le_mul_of_nonneg_right this hmW
  have hS : ∀ b ∈ I, ‖m (SbO j C V W b : SA .one (Lam d L N)).a‖ ≤
      Cm * ℓ'⁻¹ * (Step2.cNear d L * (2 * Step2.Q1 d ^ 2 * r * x b) + Step2.Q1 d * y b) := by
    intro b hb
    have hXs : IsSmall (j + 1) (Step2.Bp (L := L) (N := N) j b) :=
      isSmall_clo (isSmall_blockSet_of_mem hb)
    have h1 := mass1_le hCm H.hL8 H.hjN hXs (H.Sb_mem hb).a (-1) hℓ'
    have hs0 : 0 ≤ Step2.cNear d L * (2 * Step2.Q1 d ^ 2 * r * x b) + Step2.Q1 d * y b := by
      have := hx0 b; have := hy0 b; have := H.hQ0; have := H.hcNear; positivity
    have h2 : (Tj d (L : ℝ) (j + 1) ℓ' (SbO j C V W b : SA .one (Lam d L N)).a).toReal ≤
        Step2.cNear d L * (2 * Step2.Q1 d ^ 2 * r * x b) + Step2.Q1 d * y b := by
      have := H.Sb_o' x hx0 hx hb (y b) (hy0 b) (hy b hb)
      rw [Obs2.oTo_wA] at this
      exact ENNReal.toReal_le_of_le_ofReal hs0 this
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
  have hSsum : ∑ b ∈ I, ‖m (SbO j C V W b : SA .one (Lam d L N)).a‖ ≤
      Cm * ℓ'⁻¹ * (2 * Step2.cNear d L * Step2.Q1 d ^ 2 * r * ℓ * β + cn * Step2.Q1 d * mW) := by
    refine (sum_le_sum hS).trans ?_
    rw [← mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum]
    have e2 : ∑ b ∈ I, x b = ℓ * β := by rw [hβ, mul_sum]; exact sum_congr rfl fun b _ => by ring
    rw [e2]
    have h4 : Step2.Q1 d * ∑ b ∈ I, y b ≤ Step2.Q1 d * (cn * mW) :=
      mul_le_mul_of_nonneg_left hysum H.hQ0
    have e3 : Step2.cNear d L * (2 * Step2.Q1 d ^ 2 * r * (ℓ * β)) =
        2 * Step2.cNear d L * Step2.Q1 d ^ 2 * r * ℓ * β := by ring
    have e4 : Step2.Q1 d * (cn * mW) = cn * Step2.Q1 d * mW := by ring
    linarith
  -- assembly
  have hpr : ∑ b ∈ I, ‖m (VprO C V b : SA .one (Lam d L N)).a‖ = β := by
    rw [hβ]; exact sum_congr rfl fun b _ => by rw [hVpr]
  rw [hpr] at hstep
  linarith

end

end Obs2
