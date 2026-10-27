import Obs2.Est.SplitO
import Obs.StepObsNonlinGen

/-!
# The bound on `K_out - M` with sources (`Step2.Kout_sub_le` for a general `SNorm`)

**`KoutO_sub_le`**: the proof of `Step2.Kout_sub_le` (Brydges–Slade (D.17)–(D.20)) for the
change of variables with sources (`KoutO`, `RtermO`), in any submultiplicative seminorm
`n : Obs.Gen.SNorm (OE c Λ)` (e.g. the full norm with sources `oSN`): for a polymer `W`,

  `A^{(|𝓑(W)| - 2^d)_+} ‖∑_{g ∈ Rset} R_g(W)‖ ≤ δ'' (δ'' + μ')`,

`δ'' = (2 c₀ A)^{c_B} δ`, `μ' = μ (λA)^{2^d}`, provided `‖I(B)‖ ≤ 2`, `‖J̄‖ ≤ δ`,
`(λA)^{(|𝓑(Y)| - 2^d)_+} ‖M(Y)‖ ≤ μ`, `λ ≥ 2 c₀` and `δ'', μ' ≤ 1`.
Only the norm properties (`SNorm.prodR`, `mulR`, `wsum_bound`) are used.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Loc Step Step2 FRD

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

variable {k : ℕ} {I : OFam c d L N} {M : OAct c d L N}
  {J : (Fin d → ℕ) → Finset (Lam d L N) → OE c (Lam d L N)}

/-- **The bound on `K_out(W) - M(W)` with sources**, in any `SNorm`. -/
theorem KoutO_sub_le (n : Obs.Gen.SNorm (OE c (Lam d L N))) (hk : k ≤ N) {A lam δ μ : ℝ}
    {cS : ℕ} (hA : 1 ≤ A) (hlam : 1 ≤ lam) (hδ0 : 0 ≤ δ) (hμ0 : 0 ≤ μ)
    (hcS : ∀ b ∈ blockIdx (d := d) (L := L) (N := N) k,
      ((smallSets (d := d) (L := L) (N := N) k).filter (fun X => blockSet k b ⊆ X)).card ≤ cS)
    (hlamc : 2 * (2 : ℝ) ^ (1 + cS) ≤ lam)
    (hI : ∀ b ∈ blockIdx (L := L) (N := N) k, n.nrm (I b) ≤ ENNReal.ofReal 2)
    (hJb : ∀ p ∈ pairsU (L := L) (N := N) k, n.nrm (JbarO k I J p.1 p.2) ≤ ENNReal.ofReal δ)
    (hM : ∀ Y, IsConn k Y → ENNReal.ofReal ((lam * A) ^ (nb k Y - 2 ^ d)) * n.nrm (M Y) ≤
      ENNReal.ofReal μ)
    (hδ1 : (2 * (2 : ℝ) ^ (1 + cS) * A) ^ ((2 ^ (d + 1) + 3) ^ d) * δ ≤ 1)
    (hμ1 : μ * (lam * A) ^ 2 ^ d ≤ 1)
    {W : Finset (Lam d L N)} (hW : IsPolymer k W) :
    ENNReal.ofReal (A ^ (nb k W - 2 ^ d)) * n.nrm (∑ g ∈ Rset k W, RtermO k I M J W g) ≤
      ENNReal.ofReal (((2 * (2 : ℝ) ^ (1 + cS) * A) ^ ((2 ^ (d + 1) + 3) ^ d) * δ) *
        ((2 * (2 : ℝ) ^ (1 + cS) * A) ^ ((2 ^ (d + 1) + 3) ^ d) * δ +
          μ * (lam * A) ^ 2 ^ d)) := by
  classical
  have hA0 : 0 < A := by linarith
  set c₀ : ℝ := (2 : ℝ) ^ (1 + cS) with hc₀
  have hc₀1 : 1 ≤ c₀ := one_le_pow₀ (by norm_num)
  set cB := (2 ^ (d + 1) + 3) ^ d
  set a : ℝ := 2 * c₀ * A with ha
  have ha1 : 1 ≤ a := by rw [ha]; nlinarith
  set δ'' := a ^ cB * δ
  set μ' := μ * (lam * A) ^ 2 ^ d
  have hlA1 : 1 ≤ lam * A := by nlinarith
  refine n.wsum_bound _ _ (2 ^ ((1 + cS) * nb k W)) ((card_le_card (filter_subset _ _)).trans
    (card_G0W_le hcS hW)) fun g hg => ?_
  obtain ⟨hgF, hg1, hg2⟩ := mem_filter.1 hg
  obtain ⟨f2, -, f4⟩ := G0W_facts hgF
  obtain ⟨h1, h2, -, -, -⟩ := (mem_G0 k).1 (mem_filter.1 hgF).1
  have hgW := (mem_filter.1 hgF).2
  set nn := g.1.card
  set cc := (Comp k g.2).card
  have hbI : n.nrm (bpowO k I (W \ (g.2 ∪ Xcal g.1))) ≤ ENNReal.ofReal (2 ^ nb k W) := by
    have := n.prodR (blocks k (W \ (g.2 ∪ Xcal g.1))) I
      (fun _ => 2) (fun _ _ => by norm_num) (fun b hb => hI b (mem_blockIdx_of_mem_blocks hb))
    rw [prod_const] at this
    exact this.trans (ENNReal.ofReal_le_ofReal (pow_le_pow_right₀ (by norm_num)
      (card_le_card (blocks_mono sdiff_subset))))
  have hbM : n.nrm (KextO k M g.2) ≤
      ENNReal.ofReal (∏ Y ∈ Comp k g.2, μ / (lam * A) ^ (nb k Y - 2 ^ d)) := by
    refine n.prodR _ _ _ (fun _ _ => by positivity) fun Y hY => ?_
    have := hM Y (isConn_of_mem_comp h1 hY)
    have hp : (0 : ℝ) < (lam * A) ^ (nb k Y - 2 ^ d) := by positivity
    rw [ENNReal.ofReal_div_of_pos hp, ENNReal.le_div_iff_mul_le (Or.inl (by positivity))
      (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact this
  have hbJ : n.nrm (∏ p ∈ g.1, JbarO k I J p.1 p.2) ≤ ENNReal.ofReal (δ ^ nn) := by
    have := n.prodR g.1 (fun p => JbarO k I J p.1 p.2)
      (fun _ => δ) (fun _ _ => hδ0) (fun p hp => hJb p (h2 hp))
    rwa [prod_const] at this
  have hterm := n.mulR (by positivity) hbI (n.mulR (by positivity) hbM hbJ)
  refine (mul_le_mul_left' hterm _).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hnbW : nb k W ≤ nb k g.2 + cB * nn := by
    rw [← hgW]; exact (nb_union_le _ _).trans (Nat.add_le_add_left (nb_Bbox_le hk g.1) _)
  have hprod : ∏ Y ∈ Comp k g.2, a ^ nb k Y = a ^ nb k g.2 := prod_comp_pow h1 a
  have hY : ∀ Y ∈ Comp k g.2, a ^ nb k Y * (μ / (lam * A) ^ (nb k Y - 2 ^ d)) ≤ μ' := by
    intro Y _
    have hp : (0 : ℝ) < (lam * A) ^ (nb k Y - 2 ^ d) := by positivity
    rw [mul_div_assoc', div_le_iff₀ hp]
    have h3 : a ^ nb k Y ≤ (lam * A) ^ nb k Y := pow_le_pow_left₀ (by positivity)
      (by rw [ha]; nlinarith) _
    have h4 : (lam * A) ^ nb k Y ≤ (lam * A) ^ 2 ^ d * (lam * A) ^ (nb k Y - 2 ^ d) := by
      rw [← pow_add]; exact pow_le_pow_right₀ hlA1 (by omega)
    calc a ^ nb k Y * μ ≤ (lam * A) ^ 2 ^ d * (lam * A) ^ (nb k Y - 2 ^ d) * μ :=
          mul_le_mul_of_nonneg_right (h3.trans h4) hμ0
      _ = μ' * (lam * A) ^ (nb k Y - 2 ^ d) := by simp only [μ']; ring
  have hprodμ : a ^ nb k g.2 * ∏ Y ∈ Comp k g.2, μ / (lam * A) ^ (nb k Y - 2 ^ d) ≤ μ' ^ cc := by
    rw [← hprod, ← prod_mul_distrib, ← prod_const]
    exact prod_le_prod (fun Y _ => by positivity) hY
  have hnc : 2 ≤ nn ∨ (nn = 1 ∧ 1 ≤ cc) := by
    have hn0 : nn ≠ 0 := fun h0 => hg1 (card_eq_zero.1 h0)
    by_cases hn1 : nn = 1
    · refine Or.inr ⟨hn1, ?_⟩
      have h2' : g.2 ≠ ∅ := fun he => hg2 ⟨hn1, he⟩
      exact Nat.one_le_iff_ne_zero.2 fun hc0 => h2' ((comp_card_eq_zero_iff h1).1 hc0)
    · exact Or.inl (by omega)
  have hδ''1 : δ'' ≤ 1 := hδ1
  have hμ'1 : μ' ≤ 1 := hμ1
  calc ((2 ^ ((1 + cS) * nb k W) : ℕ) : ℝ) * A ^ (nb k W - 2 ^ d) *
        (2 ^ nb k W * ((∏ Y ∈ Comp k g.2, μ / (lam * A) ^ (nb k Y - 2 ^ d)) * δ ^ nn))
      ≤ a ^ nb k W * ((∏ Y ∈ Comp k g.2, μ / (lam * A) ^ (nb k Y - 2 ^ d)) * δ ^ nn) := by
        have e : (((2 ^ ((1 + cS) * nb k W) : ℕ) : ℝ)) = c₀ ^ nb k W := by
          rw [hc₀, ← pow_mul]; push_cast; rfl
        rw [e]
        have hA' : A ^ (nb k W - 2 ^ d) ≤ A ^ nb k W := pow_le_pow_right₀ hA (Nat.sub_le _ _)
        have : c₀ ^ nb k W * A ^ (nb k W - 2 ^ d) * 2 ^ nb k W ≤ a ^ nb k W := by
          rw [ha, mul_pow, mul_pow]
          have : c₀ ^ nb k W * A ^ (nb k W - 2 ^ d) * 2 ^ nb k W ≤
              c₀ ^ nb k W * A ^ nb k W * 2 ^ nb k W := by gcongr
          linarith [show c₀ ^ nb k W * A ^ nb k W * 2 ^ nb k W =
            2 ^ nb k W * c₀ ^ nb k W * A ^ nb k W by ring]
        have h0 : 0 ≤ (∏ Y ∈ Comp k g.2, μ / (lam * A) ^ (nb k Y - 2 ^ d)) * δ ^ nn := by
          positivity
        nlinarith
    _ ≤ (a ^ nb k g.2 * a ^ (cB * nn)) *
          ((∏ Y ∈ Comp k g.2, μ / (lam * A) ^ (nb k Y - 2 ^ d)) * δ ^ nn) := by
        rw [← pow_add]; gcongr
    _ = (a ^ nb k g.2 * ∏ Y ∈ Comp k g.2, μ / (lam * A) ^ (nb k Y - 2 ^ d)) * δ'' ^ nn := by
        have e3 : δ'' ^ nn = a ^ (cB * nn) * δ ^ nn := by
          show (a ^ cB * δ) ^ nn = _
          rw [mul_pow, ← pow_mul]
        rw [e3]; ring
    _ ≤ μ' ^ cc * δ'' ^ nn := by gcongr
    _ ≤ δ'' * (δ'' + μ') := by
        rw [mul_comm]; exact real_term (by positivity) (by positivity) hδ''1 hμ'1 hnc

end

end Obs2
