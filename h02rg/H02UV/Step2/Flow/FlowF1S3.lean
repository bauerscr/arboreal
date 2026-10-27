import Step2.Flow.FlowF1S2
import Step2.Flow.FlowF1d

/-!
# Sharp (F1) along regular histories

`F1_rg_sharp`: with the tadpole `T̃_j = 16 Z_{j+1}² (C_j(e₁, 0) - C_j(0, 0)) w⁽¹⁾_j` (`htad`) in the
one-loop coefficient, the `g²`-error of (F1) is `(32/7) e_A(j) + E₀(j)`, where `e_A(j)` bounds the
mass term and `E₀(j)` the error of the sharp one-loop coefficient.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2

/-- The last step of (F1): splitting off the one-loop coefficient. -/
theorem F1_final {X g f β e E0 E1 c3 cg : ℝ}
    (hS : |X - g - f * g ^ 2| ≤ 32 / 7 * e * g ^ 2 + c3 * g ^ 3) (hHV : |f - β| ≤ E0 + E1 * g)
    (hcg : c3 + E1 ≤ cg) (hg3 : 0 ≤ g ^ 3) :
    |X - g - β * g ^ 2| ≤ (32 / 7 * e + E0) * g ^ 2 + cg * g ^ 3 := by
  have e1 : X - g - β * g ^ 2 = (X - g - f * g ^ 2) + (f - β) * g ^ 2 := by ring
  rw [e1]
  have h1 := abs_add_le (X - g - f * g ^ 2) ((f - β) * g ^ 2)
  rw [abs_mul, abs_of_nonneg (sq_nonneg g)] at h1
  have h2 := mul_le_mul_of_nonneg_right hHV (sq_nonneg g)
  have h4 := mul_le_mul_of_nonneg_right hcg hg3
  have e5 : (E0 + E1 * g) * g ^ 2 = E0 * g ^ 2 + E1 * g ^ 3 := by ring
  linarith only [h1, h2, h4, e5, hS]

variable {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- The normalised tadpole `T̃_j = 16 Z_{j+1}² (C_j(e₁, 0) - C_j(0, 0)) w⁽¹⁾_j` along a history. -/
def htad (j : ℕ) (t : Hist.Seq (Xs R)) : ℂ :=
  16 * (stZ' R (rawHist R j t) ^ 2 * (stCov R j (rawHist R j t) (dirVec (Sum.inl 0)) 0 -
    stCov R j (rawHist R j t) 0 0) * (rawHist R j t).w1)

set_option maxHeartbeats 4000000 in
/-- **(F1) for the RG map, sharp form.** Given the sharp one-loop coefficient including the
tadpole (`|Re(f1Coef + T) - β| ≤ E₀(j) + E₁ g`), the decay of the past coefficients (`HD`) and the
mass term `|a m² w⁽¹⁾| ≤ e_A(j) g`, along regular histories
`|G_j - g_j - β g_j²| ≤ ((32/7) e_A(j) + E₀(j)) g_j² + c_g g_j³`. -/
theorem F1_rg_sharp : ∃ Cq Cl cS CqD ClD : ℝ, 0 ≤ Cq ∧ 0 ≤ Cl ∧ 1 ≤ cS ∧ 0 ≤ CqD ∧ 0 ≤ ClD ∧
    ∀ (L : ℕ) [NeZero L], 2 ^ (2 + 3) + 8 * 2 < L → pauliL0 2 ≤ L →
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (C₀ η εs CK C₂ CD Cq' Cl' cS' : ℝ),
      StepBounds L R.A C₀ η εs CK C₂ CD Cq' Cl' cS' → 2 ≤ R.A →
    ∀ (Nh : ℕ), (∀ j < Nh, ValidAt R j) → (∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1) →
    ∀ (Λ β δ κ cg cm cT ε : ℝ), ApHyp R Λ κ cg cm cT ε εs C₀ C₂ Cq' Cl' cS' → 0 < β → δ ≤ 1 / 2 →
      cg * ε ≤ β / 2 → cR R Λ cm C₂ * ε ≤ 1 → 8 * cx κ cT * ε ≤ 1 →
    ∀ (KB E1 em : ℝ) (eA E0 : ℕ → ℝ), 0 ≤ KB → (∀ j, 0 ≤ eA j) → (∀ j < Nh, 32 / 7 * eA j ≤ em) →
      (∀ j < Nh, ∀ t, Hist.InDh Λ β δ κ cg cm cT ε j t →
        ‖stA R (rawHist R j t) * (R.msq : ℂ) * (rawHist R j t).w1‖ ≤ eA j * (t j).1) →
      (∀ j < Nh, ∀ t, Hist.InDh Λ β δ κ cg cm cT ε j t → ‖hqTil R j t‖ ≤ KB ∧
        ∑ k ∈ range j, ((j : ℝ) - k + 1) * 2 ^ (j - k) * ‖hbTil R j t k‖ ≤ KB) →
      (∀ j < Nh, ∀ t, Hist.InDh Λ β δ κ cg cm cT ε j t →
        |(f1Coef R j t + htad R j t).re - β| ≤ E0 j + E1 * (t j).1) →
      f1cn R.ℓ (cmu Λ cm) * ε ≤ 1 / 8 →
      f1cn' L R.ℓ (cZ R) (cmu Λ cm) Cq (f1cRQ Cl cS (cx κ cT)) (f1cRL L Cl (cV R Λ cm) (cW R Λ cm C₂))
        * ε ≤ 1 / 8 →
      (R.ℓ ^ 2 / 7 + f1cw R.ℓ (cmu Λ cm) Cq (f1cRQ Cl cS (cx κ cT))
        (f1cRL L Cl (cV R Λ cm) (cW R Λ cm C₂))) * ε ≤ R.ρ →
      f1c3s L R.ℓ (cZ R) (cmu Λ cm) Cq (f1cRQ Cl cS (cx κ cT)) (f1cRL L Cl (cV R Λ cm) (cW R Λ cm C₂))
          CqD (f1cRD L ClD (cx κ cT)) KB
          ((24 * (2 * cZ R) + 3 * f1cn R.ℓ (cmu Λ cm) + 2 * (2 * β + 1)) * KB) em + E1 ≤ cg →
      ∀ j < Nh, ∀ t, Hist.InDh Λ β δ κ cg cm cT ε j t →
        |(rgData R).G j t - (t j).1 - β * (t j).1 ^ 2| ≤
          (32 / 7 * eA j + E0 j) * (t j).1 ^ 2 + cg * (t j).1 ^ 3 := by
  obtain ⟨Cq, Cl, cS, CqD, ClD, hCq, hCl, hcS, hCqD, hClD, hstep⟩ := step_F1s
  refine ⟨Cq, Cl, cS, CqD, ClD, hCq, hCl, hcS, hCqD, hClD, ?_⟩
  intro L _ hL8 hLp N R _ _ C₀ η εs CK C₂ CD Cq' Cl' cS' hSB hA2 Nh hV hm1 Λ β δ κ cg cm cT ε
    H hβ hδ1 hcgβ hcR1 hk1 KB E1 em eA E0 hKB heA heAm HS HD HV hs1 hs2 hs3 hcg j hj t ht
  have hℓ : 0 < R.ℓ := Fact.out
  have hjN := hj
  have hVj := hV j hj
  have hρ := hVj.2.2.2.1
  have hρ8 := hVj.2.2.2.2.1
  have hVle : ∀ i ≤ j, ValidAt R i := fun i hi => hV i (by omega)
  have hTA := HS j hj t ht
  -- the a priori bounds
  have hAP : ∀ i ≤ j, APB R (cZ R) (cW R Λ cm C₂) (t i).1 (rawHist R i t) i := fun i hi =>
    apriori R hSB hV hm1 hβ.le (by linarith) H i (by omega) t
      ⟨fun i' hi' => ht.1 i' (by omega), fun i' hi' => ht.2 i' (by omega)⟩
  obtain ⟨hz, hy, hWl⟩ := hAP j le_rfl
  obtain ⟨hg, hgε, hμ, hx⟩ := ht.1 j le_rfl
  set g := (t j).1 with hgdef
  set μ := (t j).2.1
  set x := (t j).2.2
  have HI := rawInv_hist R hρ j (fun i hi => hV i (by omega)) t
  set st := rawHist R j t with hst
  have hZ : st.Z ≠ 0 := HI.Z_ne_zero (by linarith)
  have hcz : 0 ≤ cZ R := by unfold cZ; positivity
  have hcv : 0 ≤ cV R Λ cm := by unfold cV; have := H.hcmu; positivity
  have hcw : 0 ≤ cW R Λ cm C₂ := by unfold cW; have := H.hC₂; positivity
  have hcx := H.hcx
  have hcmu := H.hcmu
  have hg1 : g ≤ 1 := hgε.trans H.hε1
  have hx1 : ‖x.1‖ ≤ cx κ cT * g ^ 3 := (norm_fst_le x).trans hx
  have hx2 : ‖x.2‖ ≤ cx κ cT * g ^ 3 := (norm_snd_le x).trans hx
  have hcxg : cx κ cT * g ≤ 1 := (mul_le_mul_of_nonneg_left hgε hcx).trans H.h3
  have hg2 : g ^ 2 ≤ g := by nlinarith
  have hg3 : g ^ 3 ≤ g ^ 2 := by nlinarith [sq_nonneg g]
  -- the smallness conditions at `g ≤ ε`
  have hη : 2 * (cZ R * g) ≤ R.ρ := by
    have := H.h1; nlinarith [mul_le_mul_of_nonneg_left hgε hcz]
  have hηs : 8 * cM * R.ℓ ^ 2 * (cZ R * g) ≤ 1 / 2 := by
    have := H.h2
    have hM : 0 ≤ cM := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hgε (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num :
      (0:ℝ) ≤ 8) hM) (sq_nonneg R.ℓ)) hcz)]
  -- the input norms
  set v := cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g with hvdef
  have hv : v ≤ cV R Λ cm * g := by
    rw [hvdef]; unfold cV
    have hM : 0 ≤ cM := Nat.cast_nonneg _
    have : 2 * |μ| + 2 * (cZ R * g) ≤ (2 * cmu Λ cm + 2 * cZ R) * g := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hM (sq_nonneg R.ℓ))]
  have hcR : cV R Λ cm + cW R Λ cm C₂ + 2 ≤ cR R Λ cm C₂ := le_of_eq rfl
  have hv1 : v ≤ 1 := by
    have : cV R Λ cm * g ≤ cR R Λ cm C₂ * ε := by
      have := mul_le_mul_of_nonneg_left hgε (by linarith : (0 : ℝ) ≤ cR R Λ cm C₂)
      nlinarith
    linarith
  set w := cW R Λ cm C₂ * g ^ 2 + ‖x.1‖ with hwdef
  have hwb : w ≤ (cW R Λ cm C₂ + 1) * g ^ 2 := by
    rw [hwdef]
    have : ‖x.1‖ ≤ g ^ 2 := hx1.trans (by
      have := mul_le_mul_of_nonneg_right hcxg (sq_nonneg g)
      calc cx κ cT * g ^ 3 = cx κ cT * g * g ^ 2 := by ring
        _ ≤ 1 * g ^ 2 := this
        _ = g ^ 2 := one_mul _)
    nlinarith
  have hw1 : w ≤ 1 := by
    refine hwb.trans ?_
    have : (cW R Λ cm C₂ + 1) * g ^ 2 ≤ cR R Λ cm C₂ * g := by
      have h1 : cW R Λ cm C₂ + 1 ≤ cR R Λ cm C₂ := by linarith
      calc (cW R Λ cm C₂ + 1) * g ^ 2 ≤ cR R Λ cm C₂ * g ^ 2 :=
            mul_le_mul_of_nonneg_right h1 (sq_nonneg g)
        _ ≤ cR R Λ cm C₂ * g := mul_le_mul_of_nonneg_left hg2 (by linarith)
    have : cR R Λ cm C₂ * g ≤ 1 :=
      (mul_le_mul_of_nonneg_left hgε (by linarith : (0 : ℝ) ≤ cR R Λ cm C₂)).trans hcR1
    linarith
  have hdd1 : ‖x.1‖ ≤ 1 := hx1.trans (by nlinarith)
  have hk1' : 8 * ‖x.2‖ ≤ 1 := by
    have : cx κ cT * g ^ 3 ≤ cx κ cT * ε := by
      have : g ^ 3 ≤ ε := by nlinarith [sq_nonneg g, pow_le_one₀ hg.le hg1 (n := 2)]
      exact mul_le_mul_of_nonneg_left this hcx
    linarith
  have hWw : Fnorm j (fscale st.Z * R.ℓ) (st.Wl + rawD R st.u x) ≤ ENNReal.ofReal w :=
    Fnorm_add_le _ _ (by positivity) (norm_nonneg _) hWl (le_of_eq (Fnorm_rawD R HI.hu hZ x))
  -- `Z w⁽¹⁾`
  have hw1Z := norm_Zw1_le R hρ j (fun i hi => hV i (by omega)) t
  -- the past part
  have hζ : ∀ i ≤ j, ‖stZeta R (rawHist R i t)‖ ≤ 2 * cZ R * (t i).1 := fun i hi => by
    obtain ⟨hzi, hyi, -⟩ := hAP i hi
    unfold stZeta absorbZeta
    refine (norm_clampDisk_le_self hρ _).trans ?_
    rw [add_div]; refine (norm_add_le _ _).trans ?_; linarith
  have hnk : ∀ k < j, ‖nCor (stNu R k (rawHist R k t) (t k).2.1) (rawHist R k t).w1‖ ≤
      f1cn R.ℓ (cmu Λ cm) * (t k).1 := fun k hk => by
    unfold nCor
    refine (norm_clampDisk_le_self (by norm_num) _).trans ?_
    have hw1k := norm_Zw1_le R hρ k (fun i hi => hV i (by omega)) t
    have hμk := (ht.1 k (by omega)).2.2.1
    have e : 4 * stNu R k (rawHist R k t) (t k).2.1 * (rawHist R k t).w1 =
        4 * ((t k).2.1 : ℂ) * (stZ' R (rawHist R k t) * (rawHist R k t).w1) / (L : ℂ) ^ (2 * k) := by
      simp only [stNu]; ring
    have nP2 : ‖(L : ℂ) ^ (2 * k)‖ = ((L : ℝ) ^ k) ^ 2 := by
      rw [norm_pow, Complex.norm_natCast, ← pow_mul, mul_comm]
    have hLk : (0 : ℝ) < ((L : ℝ) ^ k) ^ 2 := by
      have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
      positivity
    rw [e, norm_div, norm_mul, norm_mul, nP2, Complex.norm_real, Real.norm_eq_abs]
    simp only [Complex.norm_ofNat]
    rw [div_le_iff₀ hLk]
    unfold f1cn
    have := mul_le_mul hμk hw1k (norm_nonneg _)
      (mul_nonneg hcmu (ht.1 k (by omega)).1.le)
    nlinarith
  obtain ⟨hSe, hESb⟩ := hist_S_decomp R hVle t ht hβ.le hδ1 H.hcg hcgβ (by linarith [H.h6])
    H.hε1 (by positivity) (by unfold f1cn; positivity) hζ hnk
  obtain ⟨hqb, hBb⟩ := HD j hj t ht
  have hSBb : ‖∑ k ∈ range j, hbTil R j t k‖ ≤ KB := by
    refine (norm_sum_le _ _).trans (le_trans ?_ hBb)
    refine sum_le_sum fun k hk => ?_
    have hkj := mem_range.1 hk
    have h1 : (1 : ℝ) ≤ ((j : ℝ) - k + 1) * 2 ^ (j - k) := by
      have : (1 : ℝ) ≤ (j : ℝ) - k + 1 := by
        have : (k : ℝ) ≤ j := by exact_mod_cast hkj.le
        linarith
      nlinarith [one_le_pow₀ (M₀ := ℝ) (by norm_num : (1 : ℝ) ≤ 2) (n := j - k)]
    nlinarith [norm_nonneg (hbTil R j t k)]
  have hESb' : ‖_‖ ≤ (24 * (2 * cZ R) + 3 * f1cn R.ℓ (cmu Λ cm) + 2 * (2 * β + 1)) * KB * g ^ 3 :=
    hESb.trans (by
      have h0 : 0 ≤ 24 * (2 * cZ R) + 3 * f1cn R.ℓ (cmu Λ cm) + 2 * (2 * β + 1) := by
        unfold f1cn; positivity
      have := mul_le_mul_of_nonneg_left hBb h0
      exact mul_le_mul_of_nonneg_right this (by positivity))
  -- the constants
  have hcR0 : 0 ≤ cR R Λ cm C₂ := by unfold cR; positivity
  have hQ1 : 1 ≤ Q1 2 := one_le_Q1 (by norm_num)
  have hN0 : 0 ≤ cNear 2 L := Nat.cast_nonneg _
  have hRQ : cS * (Cl * (8 * ‖x.2‖)) ≤ f1cRQ Cl cS (cx κ cT) * g ^ 3 := by
    unfold f1cRQ
    have h0 : 0 ≤ cS * Cl := mul_nonneg (by linarith) hCl
    have := mul_le_mul_of_nonneg_left hx2 (by positivity : (0 : ℝ) ≤ 8 * cS * Cl)
    nlinarith
  have hRL : Cl * ((L : ℝ) ^ 2 * BH.sig 2 L v w) ≤
      f1cRL L Cl (cV R Λ cm) (cW R Λ cm C₂) * g ^ 2 := by
    unfold f1cRL BH.sig
    have hv0 : 0 ≤ v := by have : (0 : ℝ) ≤ cM := Nat.cast_nonneg _; positivity
    have h1 : v ^ 2 ≤ cV R Λ cm ^ 2 * g ^ 2 := by
      have := pow_le_pow_left₀ hv0 hv 2; rw [mul_pow] at this; exact this
    have h2 : cNear 2 L * Q1 2 ^ 2 * v ^ 2 + Q1 2 * w ≤
        (cNear 2 L * Q1 2 ^ 2 * cV R Λ cm ^ 2 + Q1 2 * (cW R Λ cm C₂ + 1)) * g ^ 2 := by
      have a1 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ cNear 2 L * Q1 2 ^ 2)
      have a2 := mul_le_mul_of_nonneg_left hwb (by linarith : (0 : ℝ) ≤ Q1 2)
      linarith only [a1, a2]
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ Cl * (L : ℝ) ^ 2)
    linarith only [h3]
  have hRD : ClD * ((L : ℝ) ^ 2 * BH.sig 2 L 0 ‖x.1‖) ≤ f1cRD L ClD (cx κ cT) * g ^ 3 := by
    unfold f1cRD BH.sig
    have := mul_le_mul_of_nonneg_left hx1 (by positivity : (0 : ℝ) ≤ ClD * (L : ℝ) ^ 2 * Q1 2)
    have e : ClD * ((L : ℝ) ^ 2 * (cNear 2 L * Q1 2 ^ 2 * 0 ^ 2 + Q1 2 * ‖x.1‖)) =
        ClD * (L : ℝ) ^ 2 * Q1 2 * ‖x.1‖ := by ring
    rw [e]; linarith only [this]
  have hcRQ : 0 ≤ f1cRQ Cl cS (cx κ cT) := by unfold f1cRQ; have : 0 ≤ cS := by linarith
                                              positivity
  have hcRL : 0 ≤ f1cRL L Cl (cV R Λ cm) (cW R Λ cm C₂) := by unfold f1cRL; positivity
  have hcRD : 0 ≤ f1cRD L ClD (cx κ cT) := by unfold f1cRD; positivity
  have hcES : 0 ≤ (24 * (2 * cZ R) + 3 * f1cn R.ℓ (cmu Λ cm) + 2 * (2 * β + 1)) * KB := by
    unfold f1cn; have := hβ.le; positivity
  -- smallness at `g ≤ ε`
  have hn8 : f1cn R.ℓ (cmu Λ cm) * g ≤ 1 / 8 :=
    (mul_le_mul_of_nonneg_left hgε (by unfold f1cn; positivity)).trans hs1
  have hcK : 0 ≤ f1cK L R.ℓ (cZ R) (cmu Λ cm) Cq (f1cRQ Cl cS (cx κ cT))
      (f1cRL L Cl (cV R Λ cm) (cW R Λ cm C₂)) := by unfold f1cK; positivity
  have hn'8 : f1cn' L R.ℓ (cZ R) (cmu Λ cm) Cq (f1cRQ Cl cS (cx κ cT))
      (f1cRL L Cl (cV R Λ cm) (cW R Λ cm C₂)) * g ≤ 1 / 8 :=
    (mul_le_mul_of_nonneg_left hgε (by unfold f1cn'; positivity)).trans hs2
  have hζ8 : (R.ℓ ^ 2 / 7 + f1cw R.ℓ (cmu Λ cm) Cq (f1cRQ Cl cS (cx κ cT))
      (f1cRL L Cl (cV R Λ cm) (cW R Λ cm C₂))) * g ≤ R.ρ :=
    (mul_le_mul_of_nonneg_left hgε (by unfold f1cw f1cn; positivity)).trans hs3
  -- the step estimate
  have hS := hstep L hL8 hLp N R j hVj st HI g μ (rawD R st.u x) (rawK R st.u x) (rawD_mem R _ _)
    (rawK_mem R _ _) R.A hA2 (cZ R) (cmu Λ cm) hcz hcmu hg.le hg1 hz hy hη hηs hμ (hm1 j hj) (eA j) em (heA j) (heAm j hj) hTA
    hw1Z w ‖x.1‖ ‖x.2‖ (by positivity) (norm_nonneg _) (norm_nonneg _) hw1 hdd1 hk1' hWw
    (le_of_eq (Fnorm_rawD R HI.hu hZ x)) (le_of_eq (Knorm_rawK R HI.hu hZ x)) hv1
    _ _ _ hcRQ hcRL hcRD hRQ hRL hRD _ ((histFS R j t).betaQ j j 0 R.i₀ (eC 3) (eC 3) 3)
    (∑ k ∈ range j, hbTil R j t k) _ KB _ hKB hcES (hist_LS_g R hVle t) hSe hESb' hqb hSBb hn8 hn'8 hζ8
  have hre : (2 * (stZ' R st * stCov R j st (dirVec (Sum.inl 0)) 0) -
      (stZ' R st ^ 2 * (histFS R j t).betaQ j j 0 R.i₀ (eC 3) (eC 3) 3 +
        ∑ k ∈ range j, hbTil R j t k) +
      16 * (stZ' R st ^ 2 * (stCov R j st (dirVec (Sum.inl 0)) 0 - stCov R j st 0 0) *
        st.w1)).re = (f1Coef R j t + htad R j t).re := rfl
  rw [hre] at hS
  have hHV := HV j hj t ht
  show |(histOut R j t).g.re - g - β * g ^ 2| ≤ (32 / 7 * eA j + E0 j) * g ^ 2 + cg * g ^ 3
  exact F1_final hS hHV hcg (by positivity)

end

end Step2
