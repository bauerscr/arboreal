import Step2.Lip.FlowZetaMain
import Step2.Last.LastCoup
import Step2.Last.LastRaw

/-!
# The Lipschitz layer at the step `j = N - 2`, part 1 (namespace `Step2.LL`)

Copies of the declarations of `Step2/Lip/FlowLipCoup`, `FlowLipStep`, `FlowLipStep2`, `FlowLipHist2`,
`FlowLipCovH`, `FlowLipCmp`, `FlowLipCmp2` that depend on the validity `ValidAt` (i.e. on
`j + 2 < N`), with the validity weakened at the top index: `SD.OK` has `k + 1 < N` and
`L > 2^6 + 4` in place of `k + 2 < N`; `DomH k` has `ValidAt` below `k` and `ValidAtL` at `k`.
The coupling remainder is bounded through `Last.coupP_bound` (`region_small_L`). The structures
`SD.OK`, `DomH`, `Cmp` shadow the originals inside `Step2.LL`, so the proofs are verbatim
otherwise.
-/
-- from Step2/Lip/FlowLipCoup.lean
namespace Step2.LL

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD

variable {L N : ℕ} [NeZero L]

set_option maxHeartbeats 2000000 in
/-- **The bound on the coupling remainder.** -/
theorem coupRem_bound : ∃ Cq : ℝ, 0 ≤ Cq ∧ ∃ Cl : ℝ, 0 ≤ Cl ∧ ∃ cS : ℝ, 1 ≤ cS ∧
    ∀ (L : ℕ) [NeZero L], 2 ^ (2 + 3) + 8 * 2 < L → pauliL0 2 ≤ L →
    ∀ (N j : ℕ), j + 1 < N → 2 ^ (2 + 4) + 4 < L → ∀ (i₀ : Fin 2) (ℓ ℓ' ℓC : ℝ), 0 < ℓ → 0 < ℓ' → 0 < ℓC →
    ℓ' + ℓC ≤ 2 * ℓ →
    ∀ C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ, GoodCov2 j ℓC C → CSym C → (∀ x y, C x y = C y x) →
    ∀ (v : Fin 4 → ℂ) (W : Fam 2 L N) (K : Act 2 L N), W ∈ BSub (L := L) (N := N) j →
      K ∈ ASub (L := L) (N := N) j → ∀ A : ℝ, 1 ≤ A → ∀ vv w k : ℝ, 0 ≤ vv → 0 ≤ w → 0 ≤ k →
      vv ≤ 1 → w ≤ 1 → k ≤ 1 →
      Fnorm j ℓ (VfamL (d := 2) (L := L) (N := N) j v) ≤ ENNReal.ofReal vv →
      Fnorm j ℓ W ≤ ENNReal.ofReal w → Knorm j ℓ A K ≤ ENNReal.ofReal k →
    ∀ a : Fin 4, cwt L j a * ‖coupRem j i₀ C v W K a‖ ≤ bRem L Cq Cl cS ℓ ℓ' ℓC vv w k := by
  obtain ⟨Cq, hCq, Cl, hCl, cS, hcS, h⟩ := Last.coupP_bound
  refine ⟨Cq, hCq, Cl, hCl, cS, hcS, ?_⟩
  intro L _ hL8 hLp N j hj2 hLg i₀ ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC hCs hCsym v W K hW hK A hA vv w k
    hv0 hw0 hk0 hv1 hw1 hk1 hVv hWw hKk a
  obtain ⟨c₀, δ, κQ, κL, hc₀, hδ, hrep, q1, q2, q3, q4, l1, l2, l3, l4, -⟩ :=
    h L hL8 hLp N j hj2 hLg ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC hCs hCsym (Coup.ofVec v) W K hW hK A hA vv w
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

set_option maxHeartbeats 2000000 in
/-- **Joint Lipschitz bound for the coupling remainder** in `(C, κ, 𝒲, K)`. -/
theorem coupRem_lip_joint : ∃ Cq : ℝ, 0 ≤ Cq ∧ ∃ Cl : ℝ, 0 ≤ Cl ∧ ∃ cS : ℝ, 1 ≤ cS ∧
    ∀ (L : ℕ) [NeZero L], 2 ^ (2 + 3) + 8 * 2 < L → pauliL0 2 ≤ L →
    ∀ (N j : ℕ), j + 1 < N → 2 ^ (2 + 4) + 4 < L → ∀ (i₀ : Fin 2) (ℓ ℓ' ℓC τ : ℝ), 0 < ℓ → 0 < ℓ' → 0 < ℓC → 0 < τ →
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
  intro L _ hL8 hLp N j hj2 hLg i₀ ℓ ℓ' ℓC τ hℓ hℓ' hℓC hτ hsum C C' hC hC' hCs hCs' hCsym hCsym'
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
    hB L hL8 hLp N j hj2 hLg i₀ ℓ ℓ' ((1 + τ) * ℓC) hℓ hℓ' hℓC' hsum Cz hCz hCzs hCzsym vz Wz Kz
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

end Step2.LL


-- from Step2/Lip/FlowLipStep.lean
namespace Step2.LL

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD

variable {L N : ℕ} [NeZero L]

namespace SD

variable (R : RGPar 2 L N) (k : ℕ) (s : SD L N)

/-- **The hypotheses on one step datum.** -/
structure OK (ℓi ℓC A cz cw cx cmu : ℝ) : Prop where
  hk : k + 1 < N
  hLg : 2 ^ (2 + 4) + 4 < L
  hC : GoodCov2 k ℓC s.C
  hCt : TInv s.C
  hCs : CSym s.C
  hCsym : ∀ x y, s.C x y = s.C y x
  hzy : ‖s.zh + s.yh‖ ≤ R.ρ
  hy : ‖s.yh‖ ≤ R.ρ
  hz' : ‖s.zh‖ ≤ cz * s.g
  hy' : ‖s.yh‖ ≤ cz * s.g
  hg : 0 < s.g
  hμ : |s.μ| ≤ cmu * s.g
  hW : s.W ∈ BSub (L := L) (N := N) k
  hD : s.D ∈ BSub (L := L) (N := N) k
  hK : s.K ∈ ASub (L := L) (N := N) k
  hWn : Fnorm k ℓi s.W ≤ ENNReal.ofReal (cw * s.g ^ 2)
  hDn : Fnorm k ℓi s.D ≤ ENNReal.ofReal (cx * s.g ^ 3)
  hKn : Knorm k ℓi A s.K ≤ ENNReal.ofReal (cx * s.g ^ 3)

end SD

namespace SD.OK

variable {R : RGPar 2 L N} {k : ℕ} {s : SD L N} {ℓi ℓC A cz cw cx cmu : ℝ}
  (H : SD.OK R k s ℓi ℓC A cz cw cx cmu)
include H

theorem hz8 (hcz : 0 ≤ cz) (hsmall : cz * s.g ≤ 1 / 16) : ‖s.zh + s.yh‖ ≤ 1 / 8 :=
  (norm_add_le _ _).trans (by linarith [H.hz', H.hy'])

theorem hzy2 : ‖s.zh + s.yh‖ ≤ 2 * cz * s.g :=
  (norm_add_le _ _).trans (by linarith [H.hz', H.hy'])

theorem Dl_mem (hL8 : 2 ^ (2 + 3) + 8 * 2 < L) : SD.Dl R k s ∈ BSub (L := L) (N := N) k :=
  VfamL_mem (by norm_num) hL8 (by have := H.hk; omega) _

theorem Kf_mem (hL8 : 2 ^ (2 + 3) + 8 * 2 < L) : SD.Kf R k s ∈ ASub (L := L) (N := N) k :=
  Kflat_mem (by have := H.hk; omega) (H.Dl_mem hL8) (eps_VfamL k _) H.hK

/-- `‖V♭‖ ≤ c_V g`. -/
theorem V_le (hℓi : 0 < ℓi) (hcz : 0 ≤ cz) (hsmall : cz * s.g ≤ 1 / 16)
    (hm : |R.msq| * ((L : ℝ) ^ k) ^ 2 ≤ 1) :
    Fnorm k ℓi (SD.V R k s) ≤ ENNReal.ofReal (cVf ℓi cz cmu * s.g) := by
  refine (Fnorm_nVec_le R k (by have := H.hk; omega) hℓi H.hzy H.hy (H.hz8 hcz hsmall) hm
    s.g s.μ s.w).trans (ENNReal.ofReal_le_ofReal ?_)
  unfold cVf
  have hg := H.hg
  rw [abs_of_pos hg]
  have h1 := H.hμ
  have h2 := H.hzy2
  have hM : 0 ≤ cM := Nat.cast_nonneg _
  have : |s.μ| + 2 * ‖s.zh + s.yh‖ ≤ (cmu + 4 * cz) * s.g := by nlinarith
  have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ cM * ℓi ^ 2)
  nlinarith [pow_pos hℓi 4]

/-- `‖Δ‖ ≤ c_Δ g`. -/
theorem Dl_le (hℓi : 0 < ℓi) (hcz : 0 ≤ cz) (hsmall : cz * s.g ≤ 1 / 16)
    (hm : |R.msq| * ((L : ℝ) ^ k) ^ 2 ≤ 1) :
    Fnorm k ℓi (SD.Dl R k s) ≤ ENNReal.ofReal (cDl ℓi cz * s.g) := by
  refine (Fnorm_nDel_le R k (by have := H.hk; omega) hℓi H.hzy H.hy (H.hz8 hcz hsmall) hm).trans
    (ENNReal.ofReal_le_ofReal ?_)
  unfold cDl
  have h1 := H.hz'
  have h2 := H.hy'
  have h3 := H.hzy2
  have hM : 0 ≤ cM := Nat.cast_nonneg _
  have : 2 * ‖s.zh + s.yh‖ + 2 * ‖s.zh‖ + 2 * ‖s.yh‖ ≤ 8 * cz * s.g := by linarith
  have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ cM * ℓi ^ 2)
  nlinarith

/-- `‖K♭‖ ≤ e c_x g³` at the weight `A e^{-1/2}`. -/
theorem Kf_le (hℓi : 0 < ℓi) (hA : 0 ≤ A) (hcz : 0 ≤ cz) (hsmall : cz * s.g ≤ 1 / 16)
    (hm : |R.msq| * ((L : ℝ) ^ k) ^ 2 ≤ 1) (hΔ : cDl ℓi cz * s.g ≤ 1 / 4) :
    Knorm k ℓi (A * Real.exp (-(1 / 4))) (SD.Kf R k s) ≤
      ENNReal.ofReal (Real.exp 1 * (cx * s.g ^ 3)) := by
  have hb : ∀ b ∈ blockIdx (L := L) (N := N) k,
      Tj 2 (L : ℝ) k ℓi (SD.Dl R k s b : Alg 2 L N) ≤ ENNReal.ofReal (1 / 4) := fun b hb =>
    (Tj_le_Fnorm _ hb).trans ((H.Dl_le hℓi hcz hsmall hm).trans (ENNReal.ofReal_le_ofReal hΔ))
  have h := Knorm_Kflat_le (d := 2) k hℓi hA (by norm_num : (0 : ℝ) ≤ 1 / 4) (SD.Dl R k s)
    (eps_VfamL k _) hb s.K
  refine h.trans ?_
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  refine mul_le_mul' (le_of_eq ?_) H.hKn
  norm_num

end SD.OK

section Diff

variable {R : RGPar 2 L N} {k : ℕ} {s s' : SD L N} {ℓi ℓC A cz cw cx cmu : ℝ}

/-- **The difference of `V♭`.** -/
theorem nVec_sub_le (H : SD.OK R k s ℓi ℓC A cz cw cx cmu) (H' : SD.OK R k s' ℓi ℓC A cz cw cx cmu)
    (hℓi : 0 < ℓi) (hcz : 0 ≤ cz) (hsmall : cz * s.g ≤ 1 / 16) (hsmall' : cz * s'.g ≤ 1 / 16)
    (hg1 : s'.g ≤ 1) (hm : |R.msq| * ((L : ℝ) ^ k) ^ 2 ≤ 1) :
    Fnorm k ℓi (SD.V R k s' - SD.V R k s) ≤ ENNReal.ofReal (aVf ℓi |s'.μ - s.μ|
      (‖s'.zh - s.zh‖ + ‖s'.yh - s.yh‖) |s'.g - s.g| ‖nCor (s'.μ : ℂ) s'.w - nCor (s.μ : ℂ) s.w‖) := by
  refine (Fnorm_nVec_sub_le R k (by have := H.hk; omega) hℓi H.hzy H.hy H'.hzy H'.hy
    (H.hz8 hcz hsmall) (H'.hz8 hcz hsmall') hm s.g s.μ s'.g s'.μ s.w s'.w
    (by rw [abs_of_pos H'.hg]; exact hg1)).trans (ENNReal.ofReal_le_ofReal ?_)
  unfold aVf
  have e : (s'.zh + s'.yh) - (s.zh + s.yh) = (s'.zh - s.zh) + (s'.yh - s.yh) := by ring
  have h1 : ‖(s'.zh + s'.yh) - (s.zh + s.yh)‖ ≤ ‖s'.zh - s.zh‖ + ‖s'.yh - s.yh‖ := by
    rw [e]; exact norm_add_le _ _
  have hM : 0 ≤ cM := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left (add_le_add_left (mul_le_mul_of_nonneg_left h1
    (by norm_num : (0 : ℝ) ≤ 2)) |s'.μ - s.μ|) (by positivity : (0 : ℝ) ≤ cM * ℓi ^ 2)
  linarith

/-- **The difference of `Δ`.** -/
theorem nDel_sub_le (H : SD.OK R k s ℓi ℓC A cz cw cx cmu) (H' : SD.OK R k s' ℓi ℓC A cz cw cx cmu)
    (hℓi : 0 < ℓi) (hcz : 0 ≤ cz) (hsmall : cz * s.g ≤ 1 / 16) (hsmall' : cz * s'.g ≤ 1 / 16)
    (hm : |R.msq| * ((L : ℝ) ^ k) ^ 2 ≤ 1) :
    Fnorm k ℓi (SD.Dl R k s' - SD.Dl R k s) ≤
      ENNReal.ofReal (cM * ℓi ^ 2 * (8 * (‖s'.zh - s.zh‖ + ‖s'.yh - s.yh‖))) := by
  have hz1 : ‖s.zh‖ ≤ 1 := H.hz'.trans (by linarith)
  have hy1 : ‖s.yh‖ ≤ 1 := H.hy'.trans (by linarith)
  refine (Fnorm_nDel_sub_le R k (by have := H.hk; omega) hℓi H.hzy H.hy H'.hzy H'.hy
    (H.hz8 hcz hsmall) (H'.hz8 hcz hsmall') hm hz1 hy1).trans (ENNReal.ofReal_le_ofReal ?_)
  have e : (s'.zh + s'.yh) - (s.zh + s.yh) = (s'.zh - s.zh) + (s'.yh - s.yh) := by ring
  have h1 : ‖(s'.zh + s'.yh) - (s.zh + s.yh)‖ ≤ ‖s'.zh - s.zh‖ + ‖s'.yh - s.yh‖ := by
    rw [e]; exact norm_add_le _ _
  have hM : 0 ≤ cM := Nat.cast_nonneg _
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  linarith

/-- **The difference of `K♭`**, at the weight `A e^{-1/2}`. -/
theorem nKf_sub_le (H : SD.OK R k s ℓi ℓC A cz cw cx cmu) (H' : SD.OK R k s' ℓi ℓC A cz cw cx cmu)
    (hℓi : 0 < ℓi) (hA : 0 < A) (hcz : 0 ≤ cz) (hsmall : cz * s.g ≤ 1 / 16)
    (hsmall' : cz * s'.g ≤ 1 / 16) (hm : |R.msq| * ((L : ℝ) ^ k) ^ 2 ≤ 1)
    (hΔ : cDl ℓi cz * s.g ≤ 1 / 4) (hΔ' : cDl ℓi cz * s'.g ≤ 1 / 4) {dK : ℝ} (hdK0 : 0 ≤ dK)
    (hdK : Knorm k ℓi A (s'.K - s.K) ≤ ENNReal.ofReal dK) (hcx : 0 ≤ cx) :
    Knorm k ℓi (A * Real.exp (-(1 / 4) * 2)) (SD.Kf R k s' - SD.Kf R k s) ≤
      ENNReal.ofReal (Real.exp 1 * dK + 4 * (Real.exp 2 * (cx * s.g ^ 3)) *
        (cM * ℓi ^ 2 * (8 * (‖s'.zh - s.zh‖ + ‖s'.yh - s.yh‖)) / (1 / 4))) := by
  have hΔn := (H.Dl_le hℓi hcz hsmall hm).trans (ENNReal.ofReal_le_ofReal hΔ)
  have hΔn' := (H'.Dl_le hℓi hcz hsmall' hm).trans (ENNReal.ofReal_le_ofReal hΔ')
  have hM : 0 ≤ cM := Nat.cast_nonneg _
  have h := Kflat_lip (d := 2) k hℓi hA (by norm_num : (0 : ℝ) < 1 / 4) (eps_VfamL k _)
    (eps_VfamL k _) hΔn hΔn' (k := cx * s.g ^ 3) (by have := H.hg; positivity) hdK0
    (by positivity) H.hKn hdK (nDel_sub_le H H' hℓi hcz hsmall hsmall' hm)
  have e1 : A * Real.exp (-(1 / 4) * 2) = A * Real.exp (-(2 * (1 / 4))) := by ring_nf
  rw [e1]
  refine h.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  norm_num

end Diff

end

end Step2.LL


-- from Step2/Lip/FlowLipStep2.lean
namespace Step2.LL

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD

variable {L N : ℕ} [NeZero L]

set_option maxHeartbeats 1000000 in
/-- **Lipschitz bound for the coupling remainder of one normalised step.** -/
theorem oKap_rem_lip : ∃ Cq : ℝ, 0 ≤ Cq ∧ ∃ Cl : ℝ, 0 ≤ Cl ∧ ∃ cS : ℝ, 1 ≤ cS ∧
    ∀ (L : ℕ) [NeZero L], 2 ^ (2 + 3) + 8 * 2 < L → pauliL0 2 ≤ L →
    ∀ (N : ℕ) (R : RGPar 2 L N) (k : ℕ) (s s' : SD L N) (ℓi ℓo ℓC : ℝ),
      0 < ℓi → 0 < ℓo → 0 < ℓC → ℓo + 2 * ℓC ≤ 2 * ℓi → k + 1 < N → 2 ^ (2 + 4) + 4 < L →
      GoodCov2 k ℓC s.C → GoodCov2 k ℓC s'.C → CSym s.C → CSym s'.C →
      (∀ x y, s.C x y = s.C y x) → (∀ x y, s'.C x y = s'.C y x) →
      ∀ ℓΔ : ℝ, 0 ≤ ℓΔ → GoodCov2 k ℓΔ (s'.C - s.C) →
      s.W + s.D ∈ BSub (L := L) (N := N) k → s'.W + s'.D ∈ BSub (L := L) (N := N) k →
      SD.Kf R k s ∈ ASub (L := L) (N := N) k → SD.Kf R k s' ∈ ASub (L := L) (N := N) k →
      ∀ A : ℝ, 1 ≤ A → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      Fnorm k ℓi (SD.V R k s) ≤ ENNReal.ofReal e → Fnorm k ℓi (SD.V R k s') ≤ ENNReal.ofReal e →
      Fnorm k ℓi (s.W + s.D) ≤ ENNReal.ofReal (e ^ 2) →
      Fnorm k ℓi (s'.W + s'.D) ≤ ENNReal.ofReal (e ^ 2) →
      Knorm k ℓi A (SD.Kf R k s) ≤ ENNReal.ofReal (e ^ 2) →
      Knorm k ℓi A (SD.Kf R k s') ≤ ENNReal.ofReal (e ^ 2) →
      ∀ a b c : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c →
      Fnorm k ℓi (SD.V R k s' - SD.V R k s) ≤ ENNReal.ofReal a →
      Fnorm k ℓi ((s'.W + s'.D) - (s.W + s.D)) ≤ ENNReal.ofReal b →
      Knorm k ℓi A (SD.Kf R k s' - SD.Kf R k s) ≤ ENNReal.ofReal c →
      ∀ i : Fin 4, cwt L k i * ‖(SD.kap R k s' i - SD.kap R k s i) -
          (SD.shv R k s' i - SD.shv R k s i)‖ ≤
        4 * bRem L Cq Cl cS ℓi ℓo ((1 + 1) * ℓC) (2 * e) (2 * e ^ 2) (2 * e ^ 2) *
          relDist e a b c ℓΔ 1 ℓC := by
  obtain ⟨Cq, hCq, Cl, hCl, cS, hcS, h⟩ := coupRem_lip_joint
  refine ⟨Cq, hCq, Cl, hCl, cS, hcS, ?_⟩
  intro L _ hL8 hLp N R k s s' ℓi ℓo ℓC hℓi hℓo hℓC hsum hkN hLg hC hC' hCs hCs' hCsym hCsym' ℓΔ hℓΔ hΔ
    hWD hWD' hK hK' A hA e he he1 hVe hVe' hWe hWe' hKe hKe' a b c ha hb hc hda hdb hdc i
  have e1 : (SD.kap R k s' i - SD.kap R k s i) - (SD.shv R k s' i - SD.shv R k s i) =
      coupRem k R.i₀ s'.C (nVec R k s'.zh s'.yh s'.g s'.μ s'.w) (s'.W + s'.D) (SD.Kf R k s') i -
        coupRem k R.i₀ s.C (nVec R k s.zh s.yh s.g s.μ s.w) (s.W + s.D) (SD.Kf R k s) i := by
    rw [SD.kap_eq, SD.kap_eq, Pi.add_apply, Pi.add_apply]; ring
  rw [e1]
  exact h L hL8 hLp N k hkN hLg R.i₀ ℓi ℓo ℓC 1 hℓi hℓo hℓC one_pos (by linarith) s.C s'.C hC hC'
    hCs hCs' hCsym hCsym' ℓΔ hℓΔ hΔ _ _ _ _ _ _ hWD hWD' hK hK' A hA e he he1 hVe hVe' hWe hWe'
    hKe hKe' a b c ha hb hc hda hdb hdc i

end

end Step2.LL


-- from Step2/Lip/FlowLipHist2.lean
namespace Step2.LL

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

section Hist

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

variable {R}

/-- **The domain at step `k`**: validity, `t_k ∈ D_ε`, the a priori bounds, and the smallness
`2 c_z ε ≤ min(ρ, 1/16)`. -/
structure DomH (k : ℕ) (t : Hist.Seq (Xs R)) (Λ κ cm cT ε cz cw : ℝ) : Prop where
  hV : ∀ i < k, ValidAt R i
  hVk : ValidAtL R k
  hD : Hist.InD3 Λ κ cm cT ε (t k)
  hA : APB R cz cw (t k).1 (rawHist R k t) k
  hcz : 0 ≤ cz
  hρ : 2 * cz * ε ≤ R.ρ
  h16 : 2 * cz * ε ≤ 1 / 16

namespace DomH

variable {k : ℕ} {t : Hist.Seq (Xs R)} {Λ κ cm cT ε cz cw : ℝ}
  (H : DomH k t Λ κ cm cT ε cz cw)
include H

theorem g_pos : 0 < (t k).1 := H.hD.1
theorem g_le : (t k).1 ≤ ε := H.hD.2.1

theorem czg : 2 * cz * (t k).1 ≤ 2 * cz * ε :=
  mul_le_mul_of_nonneg_left H.g_le (by have := H.hcz; positivity)

theorem zh_le : ‖zhH R k t‖ ≤ cz * (t k).1 := H.hA.1
theorem yh_le : ‖yhH R k t‖ ≤ cz * (t k).1 := H.hA.2.1

theorem zy_le : ‖zhH R k t + yhH R k t‖ ≤ 2 * cz * (t k).1 :=
  (norm_add_le _ _).trans (by linarith [H.zh_le, H.yh_le])

theorem zetaH_eq : zetaH R k t = zhH R k t + yhH R k t := by
  rw [zetaH, absorbZeta, add_div]
  exact clampDisk_of_le (H.zy_le.trans (H.czg.trans H.hρ))

theorem zetaH_le : ‖zetaH R k t‖ ≤ 2 * cz * (t k).1 := by rw [H.zetaH_eq]; exact H.zy_le

theorem zetaH_16 : ‖zetaH R k t‖ ≤ 1 / 16 := H.zetaH_le.trans (H.czg.trans H.h16)

theorem histOK : HistOK R k t := by
  have hV0 := H.hVk.2
  have hρ0 := hV0.2.2.2.1
  have hρ8 := hV0.2.2.2.2.1
  have HI := rawInv_hist R hρ0 k (fun i hi => H.hV i hi) t
  exact ⟨HI.Z_ne_zero (by linarith), H.zetaH_16.trans (by norm_num)⟩

theorem rawInv : RawInv R k (rawHist R k t) :=
  rawInv_hist R H.hVk.2.2.2.2.1 k (fun i hi => H.hV i hi) t

theorem uH_div : uH R k t / uH R (k + 1) t = (csq (1 + zetaH R k t))⁻¹ := by
  have hu := H.histOK.u_ne
  rw [show uH R (k + 1) t = uH R k t * csq (1 + zetaH R k t) from rfl]
  field_simp

theorem cxH_eq : cxH R k t = (csq (1 + zetaH R k t))⁻¹ := H.uH_div

theorem norm_cW : ‖uH R k t / uH R (k + 1) t‖ ≤ 16 / 15 := by
  rw [H.uH_div]; exact norm_inv_csq_le16 H.zetaH_16

theorem norm_cx : ‖cxH R k t‖ ≤ 16 / 15 := by
  rw [H.cxH_eq]
  exact norm_inv_csq_le16 H.zetaH_16

theorem cW_ne : uH R k t / uH R (k + 1) t ≠ 0 :=
  div_ne_zero H.histOK.u_ne H.histOK.u_succ_ne

theorem cx_ne : cxH R k t ≠ 0 := H.cW_ne

/-- `‖Ŵ_k‖_ℓ ≤ c_w g²`. -/
theorem WhH_le : Fnorm k R.ℓ (WhH R k t) ≤ ENNReal.ofReal (cw * (t k).1 ^ 2) := by
  have hℓ : 0 < R.ℓ := Fact.out
  have hu := H.histOK.u_ne
  rw [WhH, Fnorm_sigF_cscale hℓ (inv_ne_zero hu)]
  have hs : ‖(uH R k t)⁻¹‖ = fscale (rawHist R k t).Z := by
    rw [norm_inv, fscale, ← norm_uH_sq, Real.sqrt_inv, Real.sqrt_sq (norm_nonneg _)]
  rw [hs]
  exact H.hA.2.2

theorem WhH_mem : WhH R k t ∈ BSub (L := L) (N := N) k := sigF_mem H.rawInv.hWl _

theorem x1_le : Fnorm k R.ℓ (t k).2.2.1.toFam ≤ ENNReal.ofReal (cx κ cT * (t k).1 ^ 3) := by
  rw [BSp.Fnorm_le]
  exact ENNReal.ofReal_le_ofReal ((norm_fst_le _).trans H.hD.2.2.2)

theorem x2_le : Knorm k R.ℓ R.A (t k).2.2.2.toAct ≤ ENNReal.ofReal (cx κ cT * (t k).1 ^ 3) := by
  rw [ASp.Knorm_eq]
  exact ENNReal.ofReal_le_ofReal ((norm_snd_le _).trans H.hD.2.2.2)

/-- **The step datum of a history is admissible.** -/
theorem sdH_OK : SD.OK R k (sdH R k t) (7 / 8 * R.ℓ) (R.ℓ / 4) R.A cz cw (cx κ cT) (cmu Λ cm) where
  hk := H.hVk.2.1
  hLg := H.hVk.1
  hC := by
    obtain ⟨hC, -, -, -⟩ := H.rawInv.covL H.hVk.2
    have hC' := hC.smul (uH R (k + 1) t ^ 2)
    have hu := H.histOK.u_succ_ne
    have e : Real.sqrt ‖uH R (k + 1) t ^ 2‖ * (fscale ((rawHist R k t).Z *
        (1 + absorbZeta R (rawHist R k t).Z ((rawHist R k t).z + (rawHist R k t).y))) * R.ℓ / 4) =
        R.ℓ / 4 := by
      have hZ1 : (rawHist R k t).Z * (1 + absorbZeta R (rawHist R k t).Z
          ((rawHist R k t).z + (rawHist R k t).y)) = uH R (k + 1) t ^ 2 := (uH_succ_sq k t).symm
      rw [hZ1, fscale, norm_pow, Real.sqrt_sq (norm_nonneg _), Real.sqrt_inv,
        Real.sqrt_sq (norm_nonneg _)]
      have := norm_pos_iff.2 hu
      field_simp
    rw [e] at hC'
    exact hC'
  hCt := by
    obtain ⟨-, hCt, -, -⟩ := H.rawInv.covL H.hVk.2
    intro a x y
    simp only [sdH, CvH, nCov, Matrix.smul_apply]
    rw [hCt a x y]
  hCs := by
    obtain ⟨-, -, hCs, -⟩ := H.rawInv.covL H.hVk.2
    intro T hT x y
    simp only [sdH, CvH, nCov, Matrix.smul_apply]
    rw [hCs T hT x y]
  hCsym := by
    obtain ⟨-, -, -, hCsym⟩ := H.rawInv.covL H.hVk.2
    intro x y
    simp only [sdH, CvH, nCov, Matrix.smul_apply]
    rw [hCsym x y]
  hzy := H.zy_le.trans (H.czg.trans H.hρ)
  hy := H.yh_le.trans (by have := H.czg; have := H.hρ; have := H.hcz; have := H.g_pos; nlinarith)
  hz' := H.zh_le
  hy' := H.yh_le
  hg := H.g_pos
  hμ := H.hD.2.2.1
  hW := sigF_mem H.WhH_mem _
  hD := sigF_mem (t k).2.2.1.mem _
  hK := sigK_mem (t k).2.2.2.mem _
  hWn := by
    have hℓ : 0 < R.ℓ := Fact.out
    refine (Fnorm_sigF_le_of hℓ (by norm_num) H.cW_ne (by have := H.norm_cW; nlinarith) _).trans
      H.WhH_le
  hDn := by
    have hℓ : 0 < R.ℓ := Fact.out
    refine (Fnorm_sigF_le_of hℓ (by norm_num) H.cx_ne (by have := H.norm_cx; nlinarith) _).trans
      H.x1_le
  hKn := by
    have hℓ : 0 < R.ℓ := Fact.out
    refine (Knorm_sigK_le_of hℓ (by norm_num) H.cx_ne (by have := H.norm_cx; nlinarith) _).trans
      H.x2_le

end DomH

end Hist

section Two

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {k : ℕ} {t t' : Hist.Seq (Xs R)}
  {Λ κ cm cT ε cz cw : ℝ}

/-- **The difference of the inputs `𝒲^lin`.** -/
theorem WinH_sub_le (H : DomH k t Λ κ cm cT ε cz cw) (H' : DomH k t' Λ κ cm cT ε cz cw) {eW : ℝ}
    (heW0 : 0 ≤ eW) (heW : Fnorm k R.ℓ (WhH R k t' - WhH R k t) ≤ ENNReal.ofReal eW) (hcw : 0 ≤ cw) :
    Fnorm k (7 / 8 * R.ℓ) (WinH R k t' - WinH R k t) ≤
      ENNReal.ofReal (eW + 28 * ‖zetaH R k t' - zetaH R k t‖ * (cw * (t k).1 ^ 2)) := by
  have hℓ : 0 < R.ℓ := Fact.out
  have h := Fnorm_sigF_sub_le (θ := 7 / 8) (τ := 1 / 16) hℓ (by norm_num) (by norm_num) H.cW_ne
    H'.cW_ne (by have := H'.norm_cW; nlinarith) (by have := H.norm_cW; nlinarith)
    (by have := H'.norm_cW; nlinarith) (WhH R k t) (WhH R k t') H.WhH_le heW (by positivity) heW0
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [H.uH_div, H'.uH_div]
  have hl := inv_csq_lip (H'.zetaH_16.trans (by norm_num)) (H.zetaH_16.trans (by norm_num))
  have hf : 0 ≤ cw * (t k).1 ^ 2 := by positivity
  have e : 7 / 8 * ‖(csq (1 + zetaH R k t'))⁻¹ - (csq (1 + zetaH R k t))⁻¹‖ / (1 / 16) *
      (cw * (t k).1 ^ 2) = 14 * ‖(csq (1 + zetaH R k t'))⁻¹ - (csq (1 + zetaH R k t))⁻¹‖ *
      (cw * (t k).1 ^ 2) := by ring
  rw [e]
  have := mul_le_mul_of_nonneg_right hl hf
  nlinarith

theorem cxH_sub_le (H : DomH k t Λ κ cm cT ε cz cw) (H' : DomH k t' Λ κ cm cT ε cz cw) :
    ‖cxH R k t' - cxH R k t‖ ≤ 2 * ‖zetaH R k t' - zetaH R k t‖ := by
  rw [H.cxH_eq, H'.cxH_eq]
  exact inv_csq_lip (H'.zetaH_16.trans (by norm_num)) (H.zetaH_16.trans (by norm_num))

/-- **The difference of the inputs `D`.** -/
theorem DinH_sub_le (H : DomH k t Λ κ cm cT ε cz cw) (H' : DomH k t' Λ κ cm cT ε cz cw)
    (hcx : 0 ≤ cx κ cT) :
    Fnorm k (7 / 8 * R.ℓ) (DinH R k t' - DinH R k t) ≤
      ENNReal.ofReal (‖(t' k).2.2 - (t k).2.2‖ +
        14 * (2 * ‖zetaH R k t' - zetaH R k t‖) * (cx κ cT * (t k).1 ^ 3)) := by
  have hℓ : 0 < R.ℓ := Fact.out
  have hdx : Fnorm k R.ℓ ((t' k).2.2.1.toFam - (t k).2.2.1.toFam) ≤
      ENNReal.ofReal ‖(t' k).2.2 - (t k).2.2‖ := by
    rw [← map_sub, ← Prod.fst_sub, BSp.Fnorm_le]
    exact ENNReal.ofReal_le_ofReal (norm_fst_le _)
  have h := Fnorm_sigF_sub_le (θ := 7 / 8) (τ := 1 / 16) hℓ (by norm_num) (by norm_num) H.cx_ne
    H'.cx_ne (by have := H'.norm_cx; nlinarith) (by have := H.norm_cx; nlinarith)
    (by have := H'.norm_cx; nlinarith) _ _ H.x1_le hdx (by have := H.g_pos; positivity)
    (norm_nonneg _)
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hl := cxH_sub_le H H'
  have hf : 0 ≤ cx κ cT * (t k).1 ^ 3 := by have := H.g_pos; positivity
  have e : 7 / 8 * ‖cxH R k t' - cxH R k t‖ / (1 / 16) * (cx κ cT * (t k).1 ^ 3) =
      14 * ‖cxH R k t' - cxH R k t‖ * (cx κ cT * (t k).1 ^ 3) := by ring
  rw [e]
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl (by norm_num : (0 : ℝ) ≤ 14)) hf
  linarith

/-- **The difference of the inputs `K`.** -/
theorem KinH_sub_le (H : DomH k t Λ κ cm cT ε cz cw) (H' : DomH k t' Λ κ cm cT ε cz cw)
    (hcx : 0 ≤ cx κ cT) :
    Knorm k (7 / 8 * R.ℓ) R.A (KinH R k t' - KinH R k t) ≤
      ENNReal.ofReal (‖(t' k).2.2 - (t k).2.2‖ +
        14 * (2 * ‖zetaH R k t' - zetaH R k t‖) * (cx κ cT * (t k).1 ^ 3)) := by
  have hℓ : 0 < R.ℓ := Fact.out
  have hdx : Knorm k R.ℓ R.A ((t' k).2.2.2.toAct - (t k).2.2.2.toAct) ≤
      ENNReal.ofReal ‖(t' k).2.2 - (t k).2.2‖ := by
    rw [← map_sub, ← Prod.snd_sub, ASp.Knorm_eq]
    exact ENNReal.ofReal_le_ofReal (norm_snd_le _)
  have h := Knorm_sigK_sub_le (θ := 7 / 8) (τ := 1 / 16) hℓ (by norm_num) (by norm_num) H.cx_ne
    H'.cx_ne (by have := H'.norm_cx; nlinarith) (by have := H.norm_cx; nlinarith)
    (by have := H'.norm_cx; nlinarith) _ _ H.x2_le hdx (by have := H.g_pos; positivity)
    (norm_nonneg _)
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hl := cxH_sub_le H H'
  have hf : 0 ≤ cx κ cT * (t k).1 ^ 3 := by have := H.g_pos; positivity
  have e : 7 / 8 * ‖cxH R k t' - cxH R k t‖ / (1 / 16) * (cx κ cT * (t k).1 ^ 3) =
      14 * ‖cxH R k t' - cxH R k t‖ * (cx κ cT * (t k).1 ^ 3) := by ring
  rw [e]
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl (by norm_num : (0 : ℝ) ≤ 14)) hf
  linarith

end Two

end

end Step2.LL


-- from Step2/Lip/FlowLipCovH.lean
namespace Step2.LL

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

section Cov

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

variable {R}

/-- The invariants after the step `k` (`ValidAt` below `k`, `ValidAtL` at `k`). -/
theorem rawInv_succL {k : ℕ} (hV : ∀ i < k, ValidAt R i) (hVk : ValidAtL R k)
    (t : Hist.Seq (Xs R)) : RawInv R (k + 1) (rawHist R (k + 1) t) :=
  ((rawInv_hist R hVk.2.2.2.2.1 k hV t).stepL hVk (t k).1 (t k).2.1 (rawD_mem R _ _)
    (rawK_mem R _ _)).1

theorem CvH_eq_Cdr {k : ℕ} (hV : ∀ i < k, ValidAt R i) (hVk : ValidAtL R k)
    (t : Hist.Seq (Xs R)) :
    CvH R k t = Cdr (dataH R k t) k := by
  have HI := rawInv_succL hV hVk t
  rw [CovH_eq, Cdr, kmat_smul]
  congr 1
  rw [HI.hZprod]
  rfl

/-- **The difference of the normalised covariances of two histories.** -/
theorem CvH_sub_good (P : PtFamily) (hL7 : 7 ≤ L) {ρc : ℝ} (hρc : 0 < ρc) (hρc1 : ρc ≤ 1 / 2) :
    ∃ ζbar : ℝ, 0 < ζbar ∧ ζbar ≤ 1 / 8 ∧ ∃ Kc : ℝ, 0 ≤ Kc ∧
      ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = P →
      R.ρ ≤ ζbar / 2 → 0 < R.msq → R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) →
      ∀ (k : ℕ), (∀ i < k, ValidAt R i) → ValidAtL R k → ∀ t t' : Hist.Seq (Xs R),
      GoodCov2 k (ellLip 2 L (Kc * ∑ i ∈ range (k + 1),
          ρc ^ (k - i) * ‖zetaH R i t' - zetaH R i t‖) k) (CvH R k t' - CvH R k t) := by
  obtain ⟨ζbar, hζ, hζ8, Kc, hKc, h⟩ := prop_C5_lip P (d := 2) le_rfl hL7 hρc hρc1
  refine ⟨ζbar, hζ, hζ8, Kc, hKc, fun N R _ _ hP hρ hm0 hm1 k hV hVk t t' => ?_⟩
  have hk : k + 1 < N := hVk.2.1
  have HI := rawInv_succL hV hVk t
  have HI' := rawInv_succL hV hVk t'
  have h1 := h N R.msq (rawHist R (k + 1) t').ζ (rawHist R (k + 1) t).ζ (by omega) hm0 hm1
    (fun i => (HI'.hζ i).trans hρ) (fun i => (HI.hζ i).trans hρ) k (by omega)
  simp only at h1
  rw [CvH_eq_Cdr hV hVk, CvH_eq_Cdr hV hVk]
  have es : ∑ i ∈ range (k + 1), ρc ^ (k - i) *
      ‖(rawHist R (k + 1) t').ζ i - (rawHist R (k + 1) t).ζ i‖ =
      ∑ i ∈ range (k + 1), ρc ^ (k - i) * ‖zetaH R i t' - zetaH R i t‖ := by
    refine sum_congr rfl fun i hi => ?_
    have hi' := mem_range.1 hi
    rw [rawHist_zeta R (k + 1) t' i hi', rawHist_zeta R (k + 1) t i hi']
  rw [es] at h1
  subst hP
  exact h1

end Cov

end

end Step2.LL


-- from Step2/Lip/FlowLipCmp.lean
namespace Step2.LL

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

section Err

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

end Err

/-- **The hypotheses for comparing step `k` of two histories.** -/
structure Cmp (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (k : ℕ)
    (t t' : Hist.Seq (Xs R)) (Λ κ cm cT ε cz cw e ℓΔ : ℝ) : Prop where
  H : DomH k t Λ κ cm cT ε cz cw
  H' : DomH k t' Λ κ cm cT ε cz cw
  hm : |R.msq| * ((L : ℝ) ^ k) ^ 2 ≤ 1
  hcw : 0 ≤ cw
  hcx : 0 ≤ cx κ cT
  hcmu : 0 ≤ cmu Λ cm
  hε1 : ε ≤ 1
  hΔ : cDl (7 / 8 * R.ℓ) cz * ε ≤ 1 / 4
  he : 0 < e
  he1 : cVf (7 / 8 * R.ℓ) cz (cmu Λ cm) * ε ≤ e
  he2 : cw * ε ^ 2 + cx κ cT * ε ^ 3 ≤ e ^ 2
  he3 : Real.exp 1 * (cx κ cT * ε ^ 3) ≤ e ^ 2
  hℓΔ : 0 ≤ ℓΔ
  hC : GoodCov2 k ℓΔ (CvH R k t' - CvH R k t)

namespace Cmp

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {k : ℕ} {t t' : Hist.Seq (Xs R)}
  {Λ κ cm cT ε cz cw e ℓΔ : ℝ} (H : Cmp R k t t' Λ κ cm cT ε cz cw e ℓΔ)
include H

theorem hℓ : 0 < R.ℓ := Fact.out
theorem hA : 0 < R.A := Fact.out

theorem sOK : SD.OK R k (sdH R k t) (7 / 8 * R.ℓ) (R.ℓ / 4) R.A cz cw (cx κ cT) (cmu Λ cm) :=
  H.H.sdH_OK
theorem sOK' : SD.OK R k (sdH R k t') (7 / 8 * R.ℓ) (R.ℓ / 4) R.A cz cw (cx κ cT) (cmu Λ cm) :=
  H.H'.sdH_OK

theorem small : cz * (t k).1 ≤ 1 / 16 := by
  have := H.H.czg; have := H.H.h16; linarith
theorem small' : cz * (t' k).1 ≤ 1 / 16 := by
  have := H.H'.czg; have := H.H'.h16; linarith

theorem cDl_g : cDl (7 / 8 * R.ℓ) cz * (t k).1 ≤ 1 / 4 := by
  have h0 : 0 ≤ cDl (7 / 8 * R.ℓ) cz := by
    unfold cDl; have := H.H.hcz; have : (0 : ℝ) ≤ cM := Nat.cast_nonneg _; positivity
  exact (mul_le_mul_of_nonneg_left H.H.g_le h0).trans H.hΔ
theorem cDl_g' : cDl (7 / 8 * R.ℓ) cz * (t' k).1 ≤ 1 / 4 := by
  have h0 : 0 ≤ cDl (7 / 8 * R.ℓ) cz := by
    unfold cDl; have := H.H.hcz; have : (0 : ℝ) ≤ cM := Nat.cast_nonneg _; positivity
  exact (mul_le_mul_of_nonneg_left H.H'.g_le h0).trans H.hΔ

theorem cVf_nonneg : 0 ≤ cVf (7 / 8 * R.ℓ) cz (cmu Λ cm) := by
  unfold cVf; have := H.H.hcz; have := H.hcmu; have : (0 : ℝ) ≤ cM := Nat.cast_nonneg _
  positivity

/-- `‖V♭‖ ≤ e`. -/
theorem V_e : Fnorm k (7 / 8 * R.ℓ) (SD.V R k (sdH R k t)) ≤ ENNReal.ofReal e :=
  (H.sOK.V_le (by have := H.hℓ; positivity) H.H.hcz H.small H.hm).trans
    (ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_left H.H.g_le H.cVf_nonneg).trans H.he1))
theorem V_e' : Fnorm k (7 / 8 * R.ℓ) (SD.V R k (sdH R k t')) ≤ ENNReal.ofReal e :=
  (H.sOK'.V_le (by have := H.hℓ; positivity) H.H.hcz H.small' H.hm).trans
    (ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_left H.H'.g_le H.cVf_nonneg).trans H.he1))

theorem WD_e_of {g : ℝ} (hg0 : 0 < g) (hg : g ≤ ε) {s : SD L N}
    (hs : SD.OK R k s (7 / 8 * R.ℓ) (R.ℓ / 4) R.A cz cw (cx κ cT) (cmu Λ cm)) (hsg : s.g = g) :
    Fnorm k (7 / 8 * R.ℓ) (s.W + s.D) ≤ ENNReal.ofReal (e ^ 2) := by
  have hcw := H.hcw
  have hcx := H.hcx
  have hsg0 : 0 < s.g := hsg ▸ hg0
  refine (Fnorm_add_le _ _ (by positivity) (by positivity) hs.hWn hs.hDn).trans
    (ENNReal.ofReal_le_ofReal ?_)
  rw [hsg]
  have h2 : g ^ 2 ≤ ε ^ 2 := by gcongr
  have h3 : g ^ 3 ≤ ε ^ 3 := by gcongr
  have := mul_le_mul_of_nonneg_left h2 hcw
  have := mul_le_mul_of_nonneg_left h3 hcx
  linarith [H.he2]

theorem WD_e : Fnorm k (7 / 8 * R.ℓ) ((sdH R k t).W + (sdH R k t).D) ≤ ENNReal.ofReal (e ^ 2) :=
  H.WD_e_of H.H.g_pos H.H.g_le H.sOK rfl
theorem WD_e' : Fnorm k (7 / 8 * R.ℓ) ((sdH R k t').W + (sdH R k t').D) ≤ ENNReal.ofReal (e ^ 2) :=
  H.WD_e_of H.H'.g_pos H.H'.g_le H.sOK' rfl

theorem half_le_exp : (1 : ℝ) / 2 ≤ Real.exp (-(1 / 4) * 2) := by
  have := Real.add_one_le_exp (-(1 / 4) * 2); linarith

theorem Kf_e_of {g : ℝ} (hg0 : 0 < g) (hg : g ≤ ε) {s : SD L N}
    (hs : SD.OK R k s (7 / 8 * R.ℓ) (R.ℓ / 4) R.A cz cw (cx κ cT) (cmu Λ cm)) (hsg : s.g = g)
    (hsm : cz * s.g ≤ 1 / 16) (hΔ : cDl (7 / 8 * R.ℓ) cz * s.g ≤ 1 / 4) :
    Knorm k (7 / 8 * R.ℓ) (R.A / 2) (SD.Kf R k s) ≤ ENNReal.ofReal (e ^ 2) := by
  have hA := H.hA
  have h1 : R.A / 2 ≤ R.A * Real.exp (-(1 / 4)) := by
    have := Real.add_one_le_exp (-(1 / 4)); nlinarith
  refine (Knorm_mono_wt (by positivity) h1 _).trans ((hs.Kf_le (by have := H.hℓ; positivity)
    hA.le H.H.hcz hsm H.hm hΔ).trans (ENNReal.ofReal_le_ofReal ?_))
  rw [hsg]
  have h3 : g ^ 3 ≤ ε ^ 3 := by gcongr
  have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 H.hcx) (Real.exp_pos 1).le
  linarith [H.he3]

theorem Kf_e : Knorm k (7 / 8 * R.ℓ) (R.A / 2) (SD.Kf R k (sdH R k t)) ≤ ENNReal.ofReal (e ^ 2) :=
  H.Kf_e_of H.H.g_pos H.H.g_le H.sOK rfl H.small H.cDl_g
theorem Kf_e' : Knorm k (7 / 8 * R.ℓ) (R.A / 2) (SD.Kf R k (sdH R k t')) ≤ ENNReal.ofReal (e ^ 2) :=
  H.Kf_e_of H.H'.g_pos H.H'.g_le H.sOK' rfl H.small' H.cDl_g'

/-- **The difference of `V♭`.** -/
theorem dV : Fnorm k (7 / 8 * R.ℓ) (SD.V R k (sdH R k t') - SD.V R k (sdH R k t)) ≤
    ENNReal.ofReal (aIn R k t t') :=
  nVec_sub_le H.sOK H.sOK' (by have := H.hℓ; positivity) H.H.hcz H.small H.small'
    (H.H'.g_le.trans H.hε1) H.hm

/-- **The difference of `𝒲^lin`.** -/
theorem dW : Fnorm k (7 / 8 * R.ℓ) ((sdH R k t').W - (sdH R k t).W) ≤
    ENNReal.ofReal (bWIn R cw k t t') :=
  WinH_sub_le H.H H.H' (eWH_nonneg R k t t') (eWH_le R k t t') H.hcw

/-- **The difference of `D`.** -/
theorem dD : Fnorm k (7 / 8 * R.ℓ) ((sdH R k t').D - (sdH R k t).D) ≤
    ENNReal.ofReal (bDIn R (cx κ cT) k t t') :=
  DinH_sub_le H.H H.H' H.hcx

/-- **The difference of `K`.** -/
theorem dK : Knorm k (7 / 8 * R.ℓ) R.A ((sdH R k t').K - (sdH R k t).K) ≤
    ENNReal.ofReal (bDIn R (cx κ cT) k t t') :=
  KinH_sub_le H.H H.H' H.hcx

theorem bWIn_nonneg : 0 ≤ bWIn R cw k t t' := by
  unfold bWIn eζH; have := eWH_nonneg R k t t'; have := H.hcw; positivity
theorem bDIn_nonneg : 0 ≤ bDIn R (cx κ cT) k t t' := by
  unfold bDIn eζH; have := H.hcx; have := H.H.g_pos; positivity
theorem cIn_nonneg : 0 ≤ cIn R (cx κ cT) k t t' := by
  unfold cIn evH; have := H.bDIn_nonneg; have := H.hcx; have := H.H.g_pos
  have : (0 : ℝ) ≤ cM := Nat.cast_nonneg _; positivity
theorem aIn_nonneg : 0 ≤ aIn R k t t' := by
  unfold aIn aVf evH; have : (0 : ℝ) ≤ cM := Nat.cast_nonneg _; positivity

/-- **The difference of `𝒲^lin + D`.** -/
theorem dWD : Fnorm k (7 / 8 * R.ℓ) (((sdH R k t').W + (sdH R k t').D) -
    ((sdH R k t).W + (sdH R k t).D)) ≤
    ENNReal.ofReal (bWIn R cw k t t' + bDIn R (cx κ cT) k t t') := by
  have e : ((sdH R k t').W + (sdH R k t').D) - ((sdH R k t).W + (sdH R k t).D) =
      ((sdH R k t').W - (sdH R k t).W) + ((sdH R k t').D - (sdH R k t).D) := by abel
  rw [e]
  exact Fnorm_add_le _ _ H.bWIn_nonneg H.bDIn_nonneg H.dW H.dD

/-- **The difference of `K♭`**, at the weight `A/2`. -/
theorem dKf : Knorm k (7 / 8 * R.ℓ) (R.A / 2) (SD.Kf R k (sdH R k t') - SD.Kf R k (sdH R k t)) ≤
    ENNReal.ofReal (cIn R (cx κ cT) k t t') := by
  have hA := H.hA
  have h1 : R.A / 2 ≤ R.A * Real.exp (-(1 / 4) * 2) := by
    have := H.half_le_exp; nlinarith
  refine (Knorm_mono_wt (by positivity) h1 _).trans ?_
  have h := nKf_sub_le H.sOK H.sOK' (by have := H.hℓ; positivity) hA H.H.hcz H.small H.small' H.hm
    H.cDl_g H.cDl_g' H.bDIn_nonneg H.dK H.hcx
  exact h

end Cmp

end

end Step2.LL


-- from Step2/Lip/FlowLipCmp2.lean
namespace Step2.LL

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

set_option maxHeartbeats 1000000 in
/-- **The coupling remainders of two histories after step `k`.** -/
theorem cmp_kap : ∃ Cq : ℝ, 0 ≤ Cq ∧ ∃ Cl : ℝ, 0 ≤ Cl ∧ ∃ cS : ℝ, 1 ≤ cS ∧
    ∀ (L : ℕ) [NeZero L], 2 ^ (2 + 3) + 8 * 2 < L → pauliL0 2 ≤ L →
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], 2 ≤ R.A →
    ∀ (k : ℕ) (t t' : Hist.Seq (Xs R)) (Λ κ cm cT ε cz cw e ℓΔ : ℝ),
      Cmp R k t t' Λ κ cm cT ε cz cw e ℓΔ → e ≤ 1 / 2 →
      ∀ i : Fin 4, cwt L k i * ‖(kapH R k t' i - kapH R k t i) -
          (SD.shv R k (sdH R k t') i - SD.shv R k (sdH R k t) i)‖ ≤
        4 * bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) (2 * e) (2 * e ^ 2)
          (2 * e ^ 2) * relDist e (aIn R k t t') (bWIn R cw k t t' + bDIn R (cx κ cT) k t t')
            (cIn R (cx κ cT) k t t') ℓΔ 1 (R.ℓ / 4) := by
  obtain ⟨Cq, hCq, Cl, hCl, cS, hcS, h⟩ := oKap_rem_lip
  refine ⟨Cq, hCq, Cl, hCl, cS, hcS, ?_⟩
  intro L _ hL8 hLp N R _ _ hA2 k t t' Λ κ cm cT ε cz cw e ℓΔ H he1 i
  have hℓ := H.hℓ
  have hk := H.sOK.hk
  exact h L hL8 hLp N R k (sdH R k t) (sdH R k t') (7 / 8 * R.ℓ) R.ℓ (R.ℓ / 4) (by positivity) hℓ
    (by positivity) (by linarith) hk H.sOK.hLg H.sOK.hC H.sOK'.hC H.sOK.hCs H.sOK'.hCs H.sOK.hCsym
    H.sOK'.hCsym ℓΔ H.hℓΔ H.hC (add_mem H.sOK.hW H.sOK.hD) (add_mem H.sOK'.hW H.sOK'.hD)
    (H.sOK.Kf_mem hL8) (H.sOK'.Kf_mem hL8) (R.A / 2) (by linarith) e H.he he1 H.V_e H.V_e' H.WD_e
    H.WD_e' H.Kf_e H.Kf_e' _ _ _ H.aIn_nonneg (add_nonneg H.bWIn_nonneg H.bDIn_nonneg)
    H.cIn_nonneg H.dV H.dWD H.dKf i

end

end Step2.LL

