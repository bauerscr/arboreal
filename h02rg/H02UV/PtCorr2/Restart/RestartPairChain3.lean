import PtCorr2.Pair.PairEStep1

set_option autoImplicit false

/-!
# T5, item (5)(iii): the crude one-step bound of the per-block pair mass

For one step `k → k + 1` of the `ab` chain (no `σ_a` parts needed), the mass of a new block is
exactly (`hb` of `Obs2.rABX_next_red`, summed over the children; `Loc S` keeps its mass in `B_+`,
`Obs2.mass2_sum_blocks_ab`):

  `m₂(V_{k+1}(B_+)_{ab}) = ∑_{B ⊆ B_+}(m₂(e^{ℒ_C}V_k(B)_{ab}) − m₂(e^{ℒ_C}Q_k(B)_{ab}))
      − [B_+ ∩ {a,b} ≠ ∅]·m₂(S_k(B_+)_{ab})`

(**`rpc3_mass_Vnext`**). Hence (**`rpc3_mass_next_le`**), with anchoring (only the blocks of
`a`, `b` contribute) and `|m₂(e^{ℒ_C}F)| ≤ Q₁ℓ^{-2}‖F‖` on `𝒩({a,b})`:

  `|m₂(V_{k+1}(B_+)_{ab})| ≤ 2Q₁ℓ^{-2}(v + q) + ℓ'^{-2}s`

from `‖V_k(B)_{ab}‖_{T_k(ℓ)} ≤ v`, `‖Q_k(B)_{ab}‖_{T_k(ℓ)} ≤ q`,
`‖S_k(B_+)_{ab}‖_{T_{k+1}(ℓ')} ≤ s`. This is the crude replacement of the sources of
`rRX_flow` (`driftABX`, `errABX2`): no relative-to-`β` bound and no Gronwall, one step at a time.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

variable {d L N : ℕ} [NeZero L]

/-- **The exact mass of a new block** (no hypotheses). -/
theorem rpc3_mass_Vnext (P : ObsPts d L N) (k : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : OFam .two d L N) (K : OAct .two d L N) (c' : Fin d → ℕ) :
    mass2 (Vnext2O P k C V W K c' : SA .two (Lam d L N)).ab =
      ∑ b ∈ blocks k (blockSet (L := L) (N := N) (k + 1) c'),
        (mass2 (expLC C (V b : SA .two (Lam d L N)).ab) -
          mass2 (expLC C (Q2O P k K b : SA .two (Lam d L N)).ab)) -
      (if (blockSet (L := L) (N := N) (k + 1) c' ∩ P.pts).Nonempty then
        mass2 (SXO k C V W (blockSet (L := L) (N := N) (k + 1) c') : SA .two (Lam d L N)).ab
        else 0) := by
  have hb : ∀ b, mass2 (VpO P k C V W K b : SA .two (Lam d L N)).ab =
      (mass2 (expLC C (V b : SA .two (Lam d L N)).ab) -
        mass2 (expLC C (Q2O P k K b : SA .two (Lam d L N)).ab)) -
        mass2 (LSO P k C V W b : SA .two (Lam d L N)).ab := by
    intro b
    have halg : ((algebraMap ℂ (OE .two (Lam d L N)) (upB P k C V W K b) : OE .two (Lam d L N)) :
        SA .two (Lam d L N)).ab = 0 := by
      rw [Subalgebra.coe_algebraMap]; exact algebraMap_ab _
    have h1 : (VpO P k C V W K b : SA .two (Lam d L N)).ab =
        (uVpO P k C V W K b : SA .two (Lam d L N)).ab -
          ((algebraMap ℂ (OE .two (Lam d L N)) (upB P k C V W K b) : OE .two (Lam d L N)) :
            SA .two (Lam d L N)).ab - (upO P k C V W K b : SA .two (Lam d L N)).ab := rfl
    rw [h1, halg, upO_ab_eq, sub_zero, Obs2.mass2_sub, mass2_algebraMap, sub_zero, uVpO_ab, Obs2.mass2_sub,
      Obs2.mass2_sub]
    have hLS' : (LSO P k C V W b : SA .two (Lam d L N)).ab =
        locABtXY P (Step2.Bp (L := L) (N := N) k b) (blockSet (L := L) (N := N) k b)
          (SXO k C V W (Step2.Bp (L := L) (N := N) k b) : SA .two (Lam d L N)).ab := rfl
    rw [hLS']
  have hLS : ∑ b ∈ blocks k (blockSet (L := L) (N := N) (k + 1) c'),
      mass2 (LSO P k C V W b : SA .two (Lam d L N)).ab =
      if (blockSet (L := L) (N := N) (k + 1) c' ∩ P.pts).Nonempty then
        mass2 (SXO k C V W (blockSet (L := L) (N := N) (k + 1) c') : SA .two (Lam d L N)).ab
        else 0 := by
    have e : ∀ b ∈ blocks k (blockSet (L := L) (N := N) (k + 1) c'),
        mass2 (LSO P k C V W b : SA .two (Lam d L N)).ab =
          mass2 (locABtXY P (blockSet (L := L) (N := N) (k + 1) c') (blockSet k b)
            (SXO k C V W (blockSet (L := L) (N := N) (k + 1) c') : SA .two (Lam d L N)).ab) := by
      intro b hb
      show mass2 (locABtXY P (Step2.Bp (L := L) (N := N) k b) (blockSet (L := L) (N := N) k b)
        (SXO k C V W (Step2.Bp (L := L) (N := N) k b) : SA .two (Lam d L N)).ab) = _
      rw [Bp_eq_of_mem hb]
    rw [sum_congr rfl e,
      mass2_sum_blocks_ab P (IsPolymer.of_succ (isPolymer_blockSet (k + 1) c'))]
  rw [Vnext2O, AddSubmonoidClass.coe_finsetSum, sum_ab, Obs2.mass2_sum, sum_congr rfl fun b _ => hb b,
    sum_sub_distrib, hLS]

/-- **The crude one-step bound of the mass of a new block.** -/
theorem rpc3_mass_next_le (hd : 1 ≤ d) (hL : pauliL0 d ≤ L) (P : ObsPts d L N) {k : ℕ}
    (hk : k < N) {C : Matrix (Lam d L N) (Lam d L N) ℂ} {ℓ ℓ' v q s : ℝ} (hℓ : 0 < ℓ)
    (hℓ' : 0 < ℓ') (hv : 0 ≤ v) (hq : 0 ≤ q) (hs : 0 ≤ s) (hC : GoodCov2 k ℓ C)
    {V W : OFam .two d L N} {K : OAct .two d L N} (H : OAnchS P k V W K)
    (hVm : ∀ b, (V b : SA .two (Lam d L N)).ab ∈ NX ({P.a, P.b} : Set (Lam d L N)))
    (hVb : ∀ b ∈ blockIdx (L := L) (N := N) k,
      Tj d (L : ℝ) k ℓ (V b : SA .two (Lam d L N)).ab ≤ ENNReal.ofReal v)
    (hQb : ∀ b ∈ blockIdx (L := L) (N := N) k, Tj d (L : ℝ) k ℓ (Q2O P k K b : SA .two (Lam d L N)).ab ≤ ENNReal.ofReal q)
    (hSb : ∀ b ∈ blockIdx (L := L) (N := N) k,
      Tj d (L : ℝ) (k + 1) ℓ' (SXO k C V W (Step2.Bp (L := L) (N := N) k b) :
        SA .two (Lam d L N)).ab ≤ ENNReal.ofReal s)
    (c' : Fin d → ℕ) :
    ‖mass2 (Vnext2O P k C V W K c' : SA .two (Lam d L N)).ab‖ ≤
      2 * (Q1 d * (v + q) * ℓ⁻¹ ^ 2) + s * ℓ'⁻¹ ^ 2 := by
  rw [rpc3_mass_Vnext]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · have hQ1 := one_le_Q1 hd
    refine norm_sum_two_le _ _ (blk k P.a) (blk k P.b) (by positivity)
      (fun b _ h1 h2 => by
        rw [ab_eq_zero_of_anch P (H.hV b) h1 h2, ab_eq_zero_of_anch P (H.Q2O_anch b) h1 h2,
          map_zero, mass2_zero, sub_zero]) fun b hbX => ?_
    have hbI := blocks_subset_blockIdx _ hbX
    refine (norm_sub_le _ _).trans ?_
    have h1 := norm_mass2_expLC_le_pair hd hL hk hℓ hC P.a P.b (hVm b)
    have h2 := norm_mass2_expLC_le_pair hd hL hk hℓ hC P.a P.b (Q2O_ab_mem_pair P k K b)
    have t1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hVb b hbI)
    have t2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hQb b hbI)
    rw [ENNReal.toReal_ofReal hv] at t1
    rw [ENNReal.toReal_ofReal hq] at t2
    have hl : 0 ≤ ℓ⁻¹ ^ 2 := by positivity
    have hq1 : 0 ≤ Q1 d := by linarith
    calc _ ≤ Q1 d * (Tj d (L : ℝ) k ℓ (V b : SA .two (Lam d L N)).ab).toReal * ℓ⁻¹ ^ 2 +
          Q1 d * (Tj d (L : ℝ) k ℓ (Q2O P k K b : SA .two (Lam d L N)).ab).toReal * ℓ⁻¹ ^ 2 :=
          add_le_add h1 h2
      _ ≤ Q1 d * v * ℓ⁻¹ ^ 2 + Q1 d * q * ℓ⁻¹ ^ 2 := by
          gcongr
      _ = Q1 d * (v + q) * ℓ⁻¹ ^ 2 := by ring
  · split_ifs with hne
    · obtain ⟨p, hp⟩ := hne
      have hpb : blk k p ∈ blocks k (blockSet (L := L) (N := N) (k + 1) c') :=
        mem_blocks.2 ⟨p, (mem_inter.1 hp).1, rfl⟩
      have hBp := Bp_eq_of_mem hpb
      have hS := hSb (blk k p) (blocks_subset_blockIdx _ hpb)
      rw [hBp] at hS
      have t := ENNReal.toReal_mono ENNReal.ofReal_ne_top hS
      rw [ENNReal.toReal_ofReal hs] at t
      refine (norm_mass2_le hℓ' (k + 1) _).trans ?_
      exact mul_le_mul_of_nonneg_right t (by positivity)
    · rw [norm_zero]; positivity

end

end PtCorr2
