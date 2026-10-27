import Spin2.Pair.PairDef5e

/-!
# The `ε`-tadpole of the pair defect (pure part)

**`pd6_epsTad_le`** (pure, one scale `k`): for `C` of finite range with `GoodCov2 k ℓ C` and a
family `V` whose `ab` parts lie in `𝒩({a,b})`, are symmetric and vanish off the blocks of `a`, `b`,

  `|εF_C(V'(Λ)_{ab}, V'(Λ)_∅)| ≤ 2(64ℓ²ρ + 2·8⁴L^{-1}γ)·e`,

with `ρ ≥ |r'| = |∑_Bm₂V(B)_{ab}|`, `γ` the per-block gradient size `gradM4Sz_{a}(L^k, ℓ)` of
`V(B)_{ab}` and `e` the size of the near bulk part `‖V'^{near}_∅‖_{T_{k+1}(4ℓ)}`.

Proof: by finite range only `V'^{near}_∅` enters (`FC_pair_eq_near`); `V'(Λ)_{ab} = e^{ℒ_C}F`,
`F = V(Λ)_{ab} = εF + r'ψ̄_aψ_a + gradAB F` (`eq_grad_of_ab`), the constant drops out of `F_C`;
`|ε·| ≤ ‖·‖_{T_{k+1}(ℓ)}`, `tNorm_FC_gen_le`, `‖e^{ℒ_C}H‖_{T_{k+1}(4ℓ)} ≤ ‖H‖_{T_{k+1}(8ℓ)}`
(`tNorm_ECC_theta_le`), `‖ψ̄_aψ_a‖_{T(8ℓ)} ≤ 64ℓ²`, and the scale change of the gradient size
`(L^k, ℓ) → (L^{k+1}, 8ℓ)` (`gradM4Sz_scale_le`, factor `8⁴/L`); only two blocks contribute.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs2 Obs.LocObs

variable {L N : ℕ} [NeZero L]

set_option maxHeartbeats 2000000 in
/-- **The `ε`-tadpole at one scale** (pure). -/
theorem pd6_epsTad_le {k : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ}
    (hC : GoodCov2 k ℓ C) (hCR : CovRange k C) {a b : Lam 2 L N} (hab : a ≠ b)
    (V : OFam .two 2 L N)
    (hV : ∀ c, (V c : SA .two (Lam 2 L N)).ab ∈ NX ({a, b} : Set (Lam 2 L N)))
    (hS : ∀ c, IsSym (V c : SA .two (Lam 2 L N)).ab)
    (hz : ∀ c, c ≠ blk k a → c ≠ blk k b → (V c : SA .two (Lam 2 L N)).ab = 0)
    (hG : ∀ c, (VprO C V c : SA .two (Lam 2 L N)).e ∈
      NX (nbhd k (blockSet (L := L) (N := N) k c) : Set (Lam 2 L N)))
    {ρ γ e : ℝ} (hρ0 : 0 ≤ ρ) (hγ0 : 0 ≤ γ) (he0 : 0 ≤ e)
    (hρ : ‖∑ c ∈ blockIdx (L := L) (N := N) k, mass2 (V c : SA .two (Lam 2 L N)).ab‖ ≤ ρ)
    (hγ : ∀ c ∈ blockIdx (L := L) (N := N) k,
      gradM4Sz {a} a b ((L : ℝ) ^ k) ℓ (V c : SA .two (Lam 2 L N)).ab ≤ γ)
    (he : Tj 2 (L : ℝ) (k + 1) (2 * (2 * ℓ))
      (gNear a b k (blockIdx (L := L) (N := N) k) fun c => (VprO C V c : SA .two (Lam 2 L N)).e) ≤
        ENNReal.ofReal e) :
    ‖ε (FC C (VprLO k C V : SA .two (Lam 2 L N)).ab (VprLO k C V : SA .two (Lam 2 L N)).e)‖ ≤
      2 * ((64 * ℓ ^ 2 * ρ + 2 * ((8 : ℝ) ^ 4 * (L : ℝ)⁻¹ * γ)) * e) := by
  classical
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hh : (0 : ℝ) < (L : ℝ) ^ (k + 1) := pow_pos (by linarith) _
  set Gf : (Fin 2 → ℕ) → Alg 2 L N := fun c => (V c : SA .two (Lam 2 L N)).ab with hGfd
  set F : Alg 2 L N := ∑ c ∈ blockIdx (L := L) (N := N) k, Gf c with hFd
  -- `V'(Λ)_{ab} = e^{ℒ_C}F`
  have hA : (VprLO k C V : SA .two (Lam 2 L N)).ab = expLC C F := by
    rw [VprLO, AddSubmonoidClass.coe_finsetSum, SA.sum_ab, hFd, map_sum]
    exact sum_congr rfl fun c _ => by rw [VprO, (EthO_comp C (V c)).2.2]
  have hFN : F ∈ NX ({a, b} : Set (Lam 2 L N)) := Subalgebra.sum_mem _ fun c _ => hV c
  have hFS : IsSym F := by
    rw [isSym_iff_mem_SymS]
    exact Subalgebra.sum_mem _ fun c _ => (isSym_iff_mem_SymS _).1 (hS c)
  have hAN : (VprLO k C V : SA .two (Lam 2 L N)).ab ∈ NX ({a, b} : Set (Lam 2 L N)) := by
    rw [hA]; exact expLC_mem_NX C hFN
  -- the near reduction
  rw [VprLO_e_eq, FC_pair_eq_near hCR hAN _ hG]
  set Gn := gNear a b k (blockIdx (L := L) (N := N) k) fun c => (VprO C V c : SA .two (Lam 2 L N)).e
    with hGnd
  -- drop the constant
  set H : Alg 2 L N := mass2 F • pbp a + gradAB a b F with hHd
  have hFeq : F = ε F • (1 : Alg 2 L N) + H := by
    rw [hHd, ← add_assoc]; exact eq_grad_of_ab hab hFN hFS
  have hAeq : FC C (VprLO k C V : SA .two (Lam 2 L N)).ab Gn = FC C (expLC C H) Gn := by
    rw [hA]
    conv_lhs => rw [hFeq]
    rw [map_add, map_smul, expLC_one', FC_add_left, FC_const_left, zero_add]
  rw [hAeq]
  -- `|ε| ≤ ‖·‖_{T_{k+1}(ℓ)}`, the truncated expectation
  have h1 := Obs.norm_eps_le hℓ (k + 1) (FC C (expLC C H) Gn)
  have h2 := tNorm_FC_gen_le hℓ hC (expLC C H) Gn
  -- `‖e^{ℒ_C}H‖_{T_{k+1}(4ℓ)} ≤ ‖H‖_{T_{k+1}(8ℓ)}`
  have h3 : Tj 2 (L : ℝ) (k + 1) (2 * (2 * ℓ)) (expLC C H) ≤
      Tj 2 (L : ℝ) (k + 1) (2 * (2 * (2 * ℓ))) H := by
    obtain ⟨Hs, i1, i2, Fv, Gv, hGr, hB⟩ := hC.gram
    have := tNorm_ECC_theta_le hh (by linarith : (0 : ℝ) < 2 * (2 * ℓ)) hGr
      (gramBound_mono hh hB (by linarith : ℓ ≤ 2 * (2 * ℓ))) H
    rwa [ECC_theta] at this
  -- `‖H‖_{T_{k+1}(8ℓ)}`
  have h8 : (0 : ℝ) < 2 * (2 * (2 * ℓ)) := by linarith
  have hpb : Tj 2 (L : ℝ) (k + 1) (2 * (2 * (2 * ℓ))) (mass2 F • pbp a) ≤
      ENNReal.ofReal (64 * ℓ ^ 2 * ρ) := by
    refine tn_smul_bound (tNorm_pbp_le hh h8 a) ?_
    have hmF : mass2 F = ∑ c ∈ blockIdx (L := L) (N := N) k, mass2 (V c : SA .two (Lam 2 L N)).ab := by
      rw [hFd, mass2_sum]
    rw [hmF]
    calc ‖∑ c ∈ blockIdx (L := L) (N := N) k, mass2 (V c : SA .two (Lam 2 L N)).ab‖ *
          (2 * (2 * (2 * ℓ)) * (2 * (2 * (2 * ℓ)))) ≤ ρ * (2 * (2 * (2 * ℓ)) * (2 * (2 * (2 * ℓ)))) :=
          mul_le_mul_of_nonneg_right hρ (by positivity)
      _ = 64 * ℓ ^ 2 * ρ := by ring
  have hgr : Tj 2 (L : ℝ) (k + 1) (2 * (2 * (2 * ℓ))) (gradAB a b F) ≤
      ENNReal.ofReal (2 * ((8 : ℝ) ^ 4 * (L : ℝ)⁻¹ * γ)) := by
    rw [hFd, gradAB_sum']
    set T : Finset (Fin 2 → ℕ) := (blockIdx (L := L) (N := N) k).filter
      (fun c => c = blk k a ∨ c = blk k b)
    have hsub : ∑ c ∈ blockIdx (L := L) (N := N) k, gradAB a b (Gf c) =
        ∑ c ∈ T, gradAB a b (Gf c) := by
      refine (sum_subset (filter_subset _ _) fun c hc hcT => ?_).symm
      have hn : ¬ (c = blk k a ∨ c = blk k b) := fun h => hcT (mem_filter.2 ⟨hc, h⟩)
      push Not at hn
      show gradAB a b (V c : SA .two (Lam 2 L N)).ab = 0
      rw [hz c hn.1 hn.2, gradAB_zero']
    rw [hsub]
    have hTc : T.card ≤ 2 := by
      have : T ⊆ {blk k a, blk k b} := fun c hc => by
        rcases (mem_filter.1 hc).2 with h | h <;> simp [h]
      exact (Finset.card_le_card this).trans (card_le_two)
    have hterm : ∀ c ∈ T, Tj 2 (L : ℝ) (k + 1) (2 * (2 * (2 * ℓ))) (gradAB a b (Gf c)) ≤
        ENNReal.ofReal ((8 : ℝ) ^ 4 * (L : ℝ)⁻¹ * γ) := by
      intro c hcT
      refine (tNorm_gradAB_le_sz hh h8 a b _).trans (ENNReal.ofReal_le_ofReal ?_)
      refine (gradM4Sz_scale_le (j := k) h8.le (by norm_num : (1 : ℝ) ≤ 8)
        (by linarith : 2 * (2 * (2 * ℓ)) ≤ 8 * ℓ) a b _).trans ?_
      exact mul_le_mul_of_nonneg_left (hγ c (mem_filter.1 hcT).1) (by positivity)
    calc Tj 2 (L : ℝ) (k + 1) (2 * (2 * (2 * ℓ))) (∑ c ∈ T, gradAB a b (Gf c))
        ≤ ∑ c ∈ T, Tj 2 (L : ℝ) (k + 1) (2 * (2 * (2 * ℓ))) (gradAB a b (Gf c)) :=
          tNorm_sum_le _ _
      _ ≤ ∑ c ∈ T, ENNReal.ofReal ((8 : ℝ) ^ 4 * (L : ℝ)⁻¹ * γ) := sum_le_sum fun c hc => hterm c hc
      _ = T.card * ENNReal.ofReal ((8 : ℝ) ^ 4 * (L : ℝ)⁻¹ * γ) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ 2 * ENNReal.ofReal ((8 : ℝ) ^ 4 * (L : ℝ)⁻¹ * γ) := by gcongr; exact_mod_cast hTc
      _ = ENNReal.ofReal (2 * ((8 : ℝ) ^ 4 * (L : ℝ)⁻¹ * γ)) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  have hH : Tj 2 (L : ℝ) (k + 1) (2 * (2 * (2 * ℓ))) H ≤
      ENNReal.ofReal (64 * ℓ ^ 2 * ρ + 2 * ((8 : ℝ) ^ 4 * (L : ℝ)⁻¹ * γ)) := by
    refine (tNorm_add_le _ _).trans ?_
    rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    exact add_le_add hpb hgr
  have hX0 : 0 ≤ 64 * ℓ ^ 2 * ρ + 2 * ((8 : ℝ) ^ 4 * (L : ℝ)⁻¹ * γ) := by positivity
  have hT : Tj 2 (L : ℝ) (k + 1) ℓ (FC C (expLC C H) Gn) ≤
      ENNReal.ofReal (2 * ((64 * ℓ ^ 2 * ρ + 2 * ((8 : ℝ) ^ 4 * (L : ℝ)⁻¹ * γ)) * e)) := by
    refine h2.trans ?_
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat, ENNReal.ofReal_mul hX0]
    gcongr
    exact h3.trans hH
  refine h1.trans ?_
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hT

end

end Spin2
