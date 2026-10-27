import Step2.Lip.FlowLipW
import Step2.Flow.FlowStep

/-!
# Joint Lipschitz bound for the coupling outputs (Lipschitz bounds, part 6)

The couplings of `V_{j+1}` are `κ' = κ.shift(c₀, δ) - κ_Q.shift(c₀, δ) - κ_L` (`coupP_bound`), with
`c₀ = C(0,0)`, `δ = C(e₀, 0) - C(0, 0)`. The explicit part `κ.shift(c₀, δ)` is handled by hand;
the remainder `coupRem = κ' - κ.shift(c₀, δ)` is bounded by `bRem` (of order `k + v² + w`), and
`coupRem_lip_joint` is the joint Cauchy estimate for it in `(C, κ, 𝒲, K)`.
-/

namespace Step2

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD

variable {L N : ℕ} [NeZero L]

/-- `c₀ = C(0, 0)`. -/
def c0C (C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ) : ℂ := C 0 0

/-- `δ = C(e₀, 0) - C(0, 0)`. -/
def dlC (C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ) : ℂ := C (dirVec (Sum.inl 0)) 0 - C 0 0

/-- The remainder of the coupling map: `κ' - κ.shift(c₀, δ)`. -/
def coupRem (j : ℕ) (i₀ : Fin 2) (C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ) (v : Fin 4 → ℂ)
    (W : Fam 2 L N) (K : Act 2 L N) : Fin 4 → ℂ :=
  cvec4 (blockSet (L := L) (N := N) (j + 1) 0) i₀ (Vnext2 j C (VfamL j v) W K 0) -
    ((Coup.ofVec v).shift 2 (c0C C) (dlC C)).toVec

/-- The weights of the components: `(1, 1, L^{2j}, 1)`. -/
def cwt (L j : ℕ) : Fin 4 → ℝ := ![1, 1, (L : ℝ) ^ (2 * j), 1]

/-- The bound on the remainder. -/
def bRem (L : ℕ) (Cq Cl cS ℓ ℓ' ℓC v w k : ℝ) : ℝ :=
  Cq * (ℓ ^ 2)⁻¹ * (cS * (Cl * k)) + 2 * (Cq * (ℓ ^ 4)⁻¹ * (cS * (Cl * k))) * ℓC ^ 2 +
    Cq * (ℓ' ^ 2)⁻¹ * (Cl * ((L : ℝ) ^ 2 * BH.sig 2 L v w)) +
    Cq * (ℓ ^ 4)⁻¹ * (cS * (Cl * k)) + Cq * (ℓ' ^ 4)⁻¹ * (Cl * ((L : ℝ) ^ 2 * BH.sig 2 L v w))

theorem cwt_nonneg (L j : ℕ) (a : Fin 4) : 0 ≤ cwt L j a := by
  fin_cases a <;> simp [cwt]

theorem BHsig_nonneg {v w : ℝ} (hw : 0 ≤ w) : 0 ≤ BH.sig 2 L v w :=
  BH.sig_nonneg (by norm_num) v w hw

theorem BHsig_mono {v v' w w' : ℝ} (hv : 0 ≤ v) (hvv : v ≤ v') (hww : w ≤ w') :
    BH.sig 2 L v w ≤ BH.sig 2 L v' w' := by
  unfold BH.sig
  have := one_le_Q1 (d := 2) (by norm_num)
  have h2 : (0 : ℝ) ≤ cNear 2 L := Nat.cast_nonneg _
  have h3 : v ^ 2 ≤ v' ^ 2 := by nlinarith
  have := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ cNear 2 L * Q1 2 ^ 2)
  nlinarith

set_option maxHeartbeats 2000000 in
/-- **The bound on the coupling remainder.** -/
theorem coupRem_bound : ∃ Cq : ℝ, 0 ≤ Cq ∧ ∃ Cl : ℝ, 0 ≤ Cl ∧ ∃ cS : ℝ, 1 ≤ cS ∧
    ∀ (L : ℕ) [NeZero L], 2 ^ (2 + 3) + 8 * 2 < L → pauliL0 2 ≤ L →
    ∀ (N j : ℕ), j + 2 < N → ∀ (i₀ : Fin 2) (ℓ ℓ' ℓC : ℝ), 0 < ℓ → 0 < ℓ' → 0 < ℓC →
    ℓ' + ℓC ≤ 2 * ℓ →
    ∀ C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ, GoodCov2 j ℓC C → CSym C → (∀ x y, C x y = C y x) →
    ∀ (v : Fin 4 → ℂ) (W : Fam 2 L N) (K : Act 2 L N), W ∈ BSub (L := L) (N := N) j →
      K ∈ ASub (L := L) (N := N) j → ∀ A : ℝ, 1 ≤ A → ∀ vv w k : ℝ, 0 ≤ vv → 0 ≤ w → 0 ≤ k →
      vv ≤ 1 → w ≤ 1 → k ≤ 1 →
      Fnorm j ℓ (VfamL (d := 2) (L := L) (N := N) j v) ≤ ENNReal.ofReal vv →
      Fnorm j ℓ W ≤ ENNReal.ofReal w → Knorm j ℓ A K ≤ ENNReal.ofReal k →
    ∀ a : Fin 4, cwt L j a * ‖coupRem j i₀ C v W K a‖ ≤ bRem L Cq Cl cS ℓ ℓ' ℓC vv w k := by
  obtain ⟨Cq, hCq, Cl, hCl, cS, hcS, h⟩ := coupP_bound
  refine ⟨Cq, hCq, Cl, hCl, cS, hcS, ?_⟩
  intro L _ hL8 hLp N j hj2 i₀ ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC hCs hCsym v W K hW hK A hA vv w k
    hv0 hw0 hk0 hv1 hw1 hk1 hVv hWw hKk a
  obtain ⟨c₀, δ, κQ, κL, hc₀, hδ, hrep, q1, q2, q3, q4, l1, l2, l3, l4, -⟩ :=
    h L hL8 hLp N j hj2 ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC hCs hCsym (Coup.ofVec v) W K hW hK A hA vv w
      k hv0 hw0 hk0 hv1 hw1 hk1 (by rw [Coup.toVec_ofVec]; exact hVv) hWw hKk
  obtain ⟨c₀', δ', hc₀', hδ', hδ''⟩ := covProps (by norm_num) hCs hCsym
  have ec : c₀' = c₀ := by rw [← hc₀ 0, hc₀' 0]
  have ed : δ' = δ := by
    have h1 := hδ 0 (Sum.inl 0)
    have h2 := hδ' 0 (Sum.inl 0)
    rw [h1, ec] at h2
    exact (add_left_cancel h2).symm
  rw [ec, ed] at hδ''
  obtain ⟨hc0b, hδb⟩ := cov_c0_delta_le hC hc₀ hδ hδ''
  have hc0 : c0C C = c₀ := hc₀ 0
  have hdl : dlC C = δ := by
    unfold dlC
    have := hδ 0 (Sum.inl 0)
    rw [zero_add] at this
    rw [this, hc₀ 0]; ring
  have hjN : j + 1 < N := by omega
  have hcv := cvec4_Vcoup_block hL8 hjN i₀
    ((Coup.ofVec v).shift 2 c₀ δ - κQ.shift 2 c₀ δ - κL)
  rw [← hrep 0 (zero_mem_blockIdx (j + 1)), Coup.toVec_ofVec] at hcv
  have hR : coupRem j i₀ C v W K = -(κQ.shift 2 c₀ δ).toVec - κL.toVec := by
    unfold coupRem
    rw [hcv, hc0, hdl]
    funext b
    fin_cases b <;> simp [Coup.toVec] <;> ring
  rw [hR]
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hLj : (0 : ℝ) < ((L : ℝ) ^ j) ^ 2 := by positivity
  have hσ := BHsig_nonneg (L := L) (v := vv) hw0
  have hq2 : 0 ≤ Cq * (ℓ ^ 2)⁻¹ * (cS * (Cl * k)) := by positivity
  have hq4 : 0 ≤ Cq * (ℓ ^ 4)⁻¹ * (cS * (Cl * k)) := by positivity
  have hl2 : 0 ≤ Cq * (ℓ' ^ 2)⁻¹ * (Cl * ((L : ℝ) ^ 2 * BH.sig 2 L vv w)) := by positivity
  have hl4 : 0 ≤ Cq * (ℓ' ^ 4)⁻¹ * (Cl * ((L : ℝ) ^ 2 * BH.sig 2 L vv w)) := by positivity
  have hℓC2 : 0 ≤ ℓC ^ 2 := sq_nonneg _
  unfold bRem
  fin_cases a
  · simp only [cwt, Coup.toVec, Coup.shift, Fin.zero_eta, Fin.isValue, Pi.sub_apply,
      Pi.neg_apply, Matrix.cons_val_zero, one_mul]
    have : ‖-(κQ.z - κQ.g * c₀) - κL.z‖ ≤ ‖κQ.z‖ + ‖κQ.g‖ * ‖c₀‖ + ‖κL.z‖ := by
      rw [← norm_mul]
      calc ‖-(κQ.z - κQ.g * c₀) - κL.z‖ = ‖-κQ.z + κQ.g * c₀ - κL.z‖ := by ring_nf
        _ ≤ ‖-κQ.z + κQ.g * c₀‖ + ‖κL.z‖ := norm_sub_le _ _
        _ ≤ ‖κQ.z‖ + ‖κQ.g * c₀‖ + ‖κL.z‖ := by
          gcongr; exact (norm_add_le _ _).trans (by rw [norm_neg])
    refine this.trans ?_
    have h1 := mul_le_mul q4 hc0b (norm_nonneg _) hq4
    nlinarith
  · simp only [cwt, Coup.toVec, Coup.shift, Fin.mk_one, Fin.isValue, Pi.sub_apply,
      Pi.neg_apply, Matrix.cons_val_one, Matrix.cons_val_zero, one_mul]
    have : ‖-(κQ.y - κQ.g * δ) - κL.y‖ ≤ ‖κQ.y‖ + ‖κQ.g‖ * ‖δ‖ + ‖κL.y‖ := by
      rw [← norm_mul]
      calc ‖-(κQ.y - κQ.g * δ) - κL.y‖ = ‖-κQ.y + κQ.g * δ - κL.y‖ := by ring_nf
        _ ≤ ‖-κQ.y + κQ.g * δ‖ + ‖κL.y‖ := norm_sub_le _ _
        _ ≤ ‖κQ.y‖ + ‖κQ.g * δ‖ + ‖κL.y‖ := by
          gcongr; exact (norm_add_le _ _).trans (by rw [norm_neg])
    refine this.trans ?_
    have hδ1 : ‖δ‖ ≤ ℓC ^ 2 := hδb.trans (div_le_self hℓC2 (by
      have : (1 : ℝ) ≤ ((L : ℝ) ^ (j + 1)) ^ 2 := one_le_pow₀ (one_le_pow₀ (by
        exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)))
      linarith))
    have h1 := mul_le_mul q4 hδ1 (norm_nonneg _) hq4
    nlinarith
  · simp only [cwt, Coup.toVec, Coup.shift, Fin.reduceFinMk, Fin.isValue, Pi.sub_apply,
      Pi.neg_apply, Matrix.cons_val]
    have : ‖-(κQ.nu + 2 * (2 : ℕ) * κQ.g * δ) - κL.nu‖ ≤
        ‖κQ.nu‖ + 4 * (‖κQ.g‖ * ‖δ‖) + ‖κL.nu‖ := by
      calc ‖-(κQ.nu + 2 * (2 : ℕ) * κQ.g * δ) - κL.nu‖
          = ‖-κQ.nu + -(4 * (κQ.g * δ)) - κL.nu‖ := by push_cast; ring_nf
        _ ≤ ‖-κQ.nu + -(4 * (κQ.g * δ))‖ + ‖κL.nu‖ := norm_sub_le _ _
        _ ≤ ‖κQ.nu‖ + ‖4 * (κQ.g * δ)‖ + ‖κL.nu‖ := by
          gcongr; exact (norm_add_le _ _).trans (by rw [norm_neg, norm_neg])
        _ = _ := by rw [norm_mul, norm_mul]; norm_num
    have hLe : ((L : ℝ) ^ (2 * j)) = ((L : ℝ) ^ j) ^ 2 := by ring
    rw [hLe]
    refine (mul_le_mul_of_nonneg_left this hLj.le).trans ?_
    have hLj1 : ((L : ℝ) ^ (j + 1)) ^ 2 = ((L : ℝ) ^ j) ^ 2 * (L : ℝ) ^ 2 := by ring
    have hL1 : (1 : ℝ) ≤ (L : ℝ) ^ 2 := one_le_pow₀ (by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
    have e1 : ((L : ℝ) ^ j) ^ 2 * ‖κQ.nu‖ ≤ Cq * (ℓ ^ 2)⁻¹ * (cS * (Cl * k)) := by
      rw [le_div_iff₀ hLj] at q3; linarith
    have e2 : ((L : ℝ) ^ j) ^ 2 * ‖κL.nu‖ ≤ Cq * (ℓ' ^ 2)⁻¹ * (Cl * ((L : ℝ) ^ 2 * BH.sig 2 L vv w)) := by
      rw [hLj1, le_div_iff₀ (by positivity)] at l3
      have : ((L : ℝ) ^ j) ^ 2 * ‖κL.nu‖ ≤ ((L : ℝ) ^ j) ^ 2 * ‖κL.nu‖ * (L : ℝ) ^ 2 :=
        le_mul_of_one_le_right (mul_nonneg hLj.le (norm_nonneg _)) hL1
      linarith
    have e3 : ((L : ℝ) ^ j) ^ 2 * (4 * (‖κQ.g‖ * ‖δ‖)) ≤
        2 * (Cq * (ℓ ^ 4)⁻¹ * (cS * (Cl * k))) * ℓC ^ 2 := by
      have hδ2 : ((L : ℝ) ^ j) ^ 2 * ‖δ‖ ≤ ℓC ^ 2 / 2 := by
        rw [hLj1] at hδb
        rw [le_div_iff₀ (by positivity)] at hδb
        have : ((L : ℝ) ^ j) ^ 2 * ‖δ‖ * 2 ≤ ℓC ^ 2 := by nlinarith [norm_nonneg δ]
        linarith
      have := mul_le_mul q4 hδ2 (by positivity) hq4
      have e4 : ((L : ℝ) ^ j) ^ 2 * (4 * (‖κQ.g‖ * ‖δ‖)) = 4 * (‖κQ.g‖ * (((L : ℝ) ^ j) ^ 2 * ‖δ‖)) := by
        ring
      rw [e4]
      linarith only [this]
    have e5 : ((L : ℝ) ^ j) ^ 2 * (‖κQ.nu‖ + 4 * (‖κQ.g‖ * ‖δ‖) + ‖κL.nu‖) =
        ((L : ℝ) ^ j) ^ 2 * ‖κQ.nu‖ + ((L : ℝ) ^ j) ^ 2 * (4 * (‖κQ.g‖ * ‖δ‖)) +
          ((L : ℝ) ^ j) ^ 2 * ‖κL.nu‖ := by ring
    rw [e5]
    linarith only [e1, e2, e3, hq4, hl4]
  · simp only [cwt, Coup.toVec, Coup.shift, Fin.reduceFinMk, Fin.isValue, Pi.sub_apply,
      Pi.neg_apply, Matrix.cons_val, one_mul]
    have : ‖-κQ.g - κL.g‖ ≤ ‖κQ.g‖ + ‖κL.g‖ := by
      rw [show -κQ.g - κL.g = -(κQ.g + κL.g) by ring, norm_neg]; exact norm_add_le _ _
    refine this.trans ?_
    nlinarith

theorem VfamL_line (j : ℕ) (v v' : Fin 4 → ℂ) (z : ℂ) :
    VfamL (d := 2) (L := L) (N := N) j (v + z • (v' - v)) =
      VfamL j v + z • (VfamL j v' - VfamL j v) := by
  rw [map_add, map_smul, map_sub]

theorem coupRem_diff (j : ℕ) (i₀ : Fin 2) (C C' : Matrix (Lam 2 L N) (Lam 2 L N) ℂ)
    (v v' : Fin 4 → ℂ) (W W' : Fam 2 L N) (K K' : Act 2 L N) (a : Fin 4) :
    Differentiable ℂ (fun z : ℂ => coupRem j i₀ (C + z • (C' - C)) (v + z • (v' - v))
      (W + z • (W' - W)) (K + z • (K' - K)) a) := by
  have hVf : ∀ b, HolE (fun z : ℂ => VfamL (d := 2) (L := L) (N := N) j (v + z • (v' - v)) b) :=
    fun b => by
      simp only [VfamL_line]
      exact (HolE.const _).add (HolE.smul differentiable_id (HolE.const _))
  have hWf : ∀ b, HolE (fun z : ℂ => (W + z • (W' - W)) b) := fun b =>
    (HolE.const _).add (HolE.smul differentiable_id (HolE.const _))
  have hKf : ∀ X, HolE (fun z : ℂ => (K + z • (K' - K)) X) := fun X =>
    (HolE.const _).add (HolE.smul differentiable_id (HolE.const _))
  have h1 := (Vnext2_holC (Cf := fun z : ℂ => C + z • (C' - C)) j (fun x y => cov_line_diff x y)
    hVf hWf hKf 0).lin ((LinearMap.proj a).comp (cvec4 (blockSet (L := L) (N := N) (j + 1) 0) i₀))
  have h2 : Differentiable ℂ (fun z : ℂ => ((Coup.ofVec (v + z • (v' - v))).shift 2
      (c0C (C + z • (C' - C))) (dlC (C + z • (C' - C)))).toVec a) := by
    fin_cases a <;>
      simp only [Coup.toVec, Coup.shift, Coup.ofVec, c0C, dlC, Matrix.add_apply,
        Matrix.smul_apply, Matrix.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
        smul_eq_mul, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val,
        Matrix.cons_val_zero, Matrix.cons_val_one] <;> fun_prop
  exact h1.sub h2

set_option maxHeartbeats 2000000 in
/-- **Joint Lipschitz bound for the coupling remainder** in `(C, κ, 𝒲, K)`. -/
theorem coupRem_lip_joint : ∃ Cq : ℝ, 0 ≤ Cq ∧ ∃ Cl : ℝ, 0 ≤ Cl ∧ ∃ cS : ℝ, 1 ≤ cS ∧
    ∀ (L : ℕ) [NeZero L], 2 ^ (2 + 3) + 8 * 2 < L → pauliL0 2 ≤ L →
    ∀ (N j : ℕ), j + 2 < N → ∀ (i₀ : Fin 2) (ℓ ℓ' ℓC τ : ℝ), 0 < ℓ → 0 < ℓ' → 0 < ℓC → 0 < τ →
    ℓ' + (1 + τ) * ℓC ≤ 2 * ℓ →
    ∀ C C' : Matrix (Lam 2 L N) (Lam 2 L N) ℂ, GoodCov2 j ℓC C → GoodCov2 j ℓC C' →
    CSym C → CSym C' → (∀ x y, C x y = C y x) → (∀ x y, C' x y = C' y x) →
    ∀ ℓΔ : ℝ, 0 ≤ ℓΔ → GoodCov2 j ℓΔ (C' - C) →
    ∀ (v v' : Fin 4 → ℂ) (W W' : Fam 2 L N) (K K' : Act 2 L N), W ∈ BSub (L := L) (N := N) j →
      W' ∈ BSub (L := L) (N := N) j → K ∈ ASub (L := L) (N := N) j →
      K' ∈ ASub (L := L) (N := N) j → ∀ A : ℝ, 1 ≤ A → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      Fnorm j ℓ (VfamL (d := 2) (L := L) (N := N) j v) ≤ ENNReal.ofReal e →
      Fnorm j ℓ (VfamL (d := 2) (L := L) (N := N) j v') ≤ ENNReal.ofReal e →
      Fnorm j ℓ W ≤ ENNReal.ofReal (e ^ 2) → Fnorm j ℓ W' ≤ ENNReal.ofReal (e ^ 2) →
      Knorm j ℓ A K ≤ ENNReal.ofReal (e ^ 2) → Knorm j ℓ A K' ≤ ENNReal.ofReal (e ^ 2) →
      ∀ a b c : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c →
      Fnorm j ℓ (VfamL (d := 2) (L := L) (N := N) j v' - VfamL j v) ≤ ENNReal.ofReal a →
      Fnorm j ℓ (W' - W) ≤ ENNReal.ofReal b → Knorm j ℓ A (K' - K) ≤ ENNReal.ofReal c →
    ∀ i : Fin 4, cwt L j i * ‖coupRem j i₀ C' v' W' K' i - coupRem j i₀ C v W K i‖ ≤
      4 * bRem L Cq Cl cS ℓ ℓ' ((1 + τ) * ℓC) (2 * e) (2 * e ^ 2) (2 * e ^ 2) *
        relDist e a b c ℓΔ τ ℓC := by
  obtain ⟨Cq, hCq, Cl, hCl, cS, hcS, hB⟩ := coupRem_bound
  refine ⟨Cq, hCq, Cl, hCl, cS, hcS, ?_⟩
  intro L _ hL8 hLp N j hj2 i₀ ℓ ℓ' ℓC τ hℓ hℓ' hℓC hτ hsum C C' hC hC' hCs hCs' hCsym hCsym'
    ℓΔ hℓΔ hΔ v v' W W' K K' hW hW' hK hK' A hA e he he1 hVe hVe' hWe hWe' hKe hKe' a b c ha hb
    hc hda hdb hdc i
  set B := bRem L Cq Cl cS ℓ ℓ' ((1 + τ) * ℓC) (2 * e) (2 * e ^ 2) (2 * e ^ 2) with hBdef
  have hσ := BHsig_nonneg (L := L) (v := 2 * e) (by positivity : (0 : ℝ) ≤ 2 * e ^ 2)
  have hB0 : 0 ≤ B := by rw [hBdef]; unfold bRem; positivity
  have hs0 := relDist_nonneg (ℓΔ := ℓΔ) (τ := τ) (ℓC := ℓC) he ha hb hc
  have hw0 := cwt_nonneg L j i
  have hℓC' : 0 < (1 + τ) * ℓC := by positivity
  have he2 : e ^ 2 ≤ 1 / 4 := by nlinarith
  have bound := fun (Cz : Matrix (Lam 2 L N) (Lam 2 L N) ℂ) (hCz : GoodCov2 j ((1 + τ) * ℓC) Cz)
      (hCzs : CSym Cz) (hCzsym : ∀ x y, Cz x y = Cz y x) (vz : Fin 4 → ℂ) (Wz : Fam 2 L N)
      (Kz : Act 2 L N) (hWz : Wz ∈ BSub (L := L) (N := N) j) (hKz : Kz ∈ ASub (L := L) (N := N) j)
      (hVz : Fnorm j ℓ (VfamL (d := 2) (L := L) (N := N) j vz) ≤ ENNReal.ofReal (2 * e))
      (hWzn : Fnorm j ℓ Wz ≤ ENNReal.ofReal (2 * e ^ 2))
      (hKzn : Knorm j ℓ A Kz ≤ ENNReal.ofReal (2 * e ^ 2)) =>
    hB L hL8 hLp N j hj2 i₀ ℓ ℓ' ((1 + τ) * ℓC) hℓ hℓ' hℓC' hsum Cz hCz hCzs hCzsym vz Wz Kz
      hWz hKz A hA (2 * e) (2 * e ^ 2) (2 * e ^ 2) (by positivity) (by positivity) (by positivity)
      (by linarith) (by linarith) (by linarith) hVz hWzn hKzn i
  have h2e : ∀ {t : ℝ}, 0 ≤ t → ENNReal.ofReal t ≤ ENNReal.ofReal (2 * t) :=
    fun ht => ENNReal.ofReal_le_ofReal (by linarith)
  have hCm : ∀ {Cz : Matrix (Lam 2 L N) (Lam 2 L N) ℂ}, GoodCov2 j ℓC Cz →
      GoodCov2 j ((1 + τ) * ℓC) Cz := fun h => h.mono (by nlinarith)
  set φ : ℂ → ℂ := fun z => (cwt L j i : ℂ) * coupRem j i₀ (C + z • (C' - C)) (v + z • (v' - v))
    (W + z • (W' - W)) (K + z • (K' - K)) i with hφ
  have hφ1 : φ 1 = (cwt L j i : ℂ) * coupRem j i₀ C' v' W' K' i := by simp [hφ]
  have hφ0 : φ 0 = (cwt L j i : ℂ) * coupRem j i₀ C v W K i := by simp [hφ]
  have hnorm : ∀ z, ‖φ z‖ = cwt L j i * ‖coupRem j i₀ (C + z • (C' - C)) (v + z • (v' - v))
      (W + z • (W' - W)) (K + z • (K' - K)) i‖ := fun z => by
    rw [hφ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]
  have hX : cwt L j i * ‖coupRem j i₀ C' v' W' K' i - coupRem j i₀ C v W K i‖ = ‖φ 1 - φ 0‖ := by
    rw [hφ1, hφ0, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]
  rw [hX]
  refine cauchy_lip_real hB0 hs0 ?_ ?_
  · refine (norm_sub_le _ _).trans ?_
    have b1 := bound C' (hCm hC') hCs' hCsym' v' W' K' hW' hK' (hVe'.trans (h2e he.le))
      (hWe'.trans (h2e (sq_nonneg e))) (hKe'.trans (h2e (sq_nonneg e)))
    have b0 := bound C (hCm hC) hCs hCsym v W K hW hK (hVe.trans (h2e he.le))
      (hWe.trans (h2e (sq_nonneg e))) (hKe.trans (h2e (sq_nonneg e)))
    rw [hφ1, hφ0, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]
    linarith
  · intro R hR2 hRs
    have hR0 : 0 < R := by linarith
    obtain ⟨hRa, hRb, hRc, hRℓ⟩ := relDist_radius he ha hb hc hτ hℓC hℓΔ hR0.le hRs
    have hdiff : Differentiable ℂ φ := (differentiable_const _).mul
      (coupRem_diff j i₀ C C' v v' W W' K K' i)
    refine (norm_taylor_le hdiff (by linarith : (1 : ℝ) < R) fun z hz => ?_).1
    rw [hnorm]
    obtain ⟨hVz, hWz⟩ := line_norms_F (VfamL (d := 2) (L := L) (N := N) j v) (VfamL j v') W W'
      he.le hR0.le ha hb z hz hVe hWe hda hdb hRa hRb
    obtain ⟨-, -, hKz⟩ := line_norms (VfamL (d := 2) (L := L) (N := N) j v) (VfamL j v') W W' K K'
      he.le hR0.le ha hb hc z hz hVe hWe hKe hda hdb hdc hRa hRb hRc
    rw [← VfamL_line] at hVz
    exact bound _ ((hC.line hΔ hℓΔ hz.le).mono (by nlinarith)) (hCs.line hCs' z)
      (symm_line hCsym hCsym' z) _ _ _ (add_mem hW (Submodule.smul_mem _ z (sub_mem hW' hW)))
      (add_mem hK (Submodule.smul_mem _ z (sub_mem hK' hK))) hVz hWz hKz

end

end Step2
