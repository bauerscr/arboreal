import Step2.Flow.FlowF1c

/-!
# (F1) along regular histories

`F1_rg`: the band (F1) for `rgData`, given the values of the one-loop coefficients (`HV`) and the
decay of the past coefficients (`HD`).
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- The normalised past coefficients `Z_{j+1}² b_{j,k}`. -/
def hbTil (j : ℕ) (t : Hist.Seq (Xs R)) (k : ℕ) : ℂ :=
  stZ' R (rawHist R j t) ^ 2 * (histFS R j t).beta j k 0 R.i₀ (eC 3) (eC 3) 3

/-- The normalised bubble `Z_{j+1}² q_{j,j}`. -/
def hqTil (j : ℕ) (t : Hist.Seq (Xs R)) : ℂ :=
  stZ' R (rawHist R j t) ^ 2 * (histFS R j t).betaQ j j 0 R.i₀ (eC 3) (eC 3) 3

/-- The normalised field-strength coefficient `Z_{j+1} C_j(e₁, 0)`. -/
def hcTil (j : ℕ) (t : Hist.Seq (Xs R)) : ℂ :=
  stZ' R (rawHist R j t) * stCov R j (rawHist R j t) (dirVec (Sum.inl 0)) 0

/-- The one-loop coefficient of (F1): `2 c - (q + ∑_k b_k)`, normalised. -/
def f1Coef (j : ℕ) (t : Hist.Seq (Xs R)) : ℂ :=
  2 * hcTil R j t - (hqTil R j t + ∑ k ∈ range j, hbTil R j t k)

/-- **The past part of `Loc S` in normalised form**: `S = Z²(g² ∑_k b̃_k + E_S)` with
`|E_S| ≤ (48 C_z + 3 c_n + 2(2β+1)) g³ ∑_k (j-k+1) 2^{j-k} |b̃_k|`. -/
theorem hist_S_decomp {j : ℕ} (hV : ∀ i ≤ j, ValidAt R i) (t : Hist.Seq (Xs R))
    {Λ β δ κ cg cm cT ε cZ' cn : ℝ} (ht : Hist.InDh Λ β δ κ cg cm cT ε j t) (hβ : 0 ≤ β)
    (hδ1 : δ ≤ 1 / 2) (hcg : 0 ≤ cg) (hcgβ : cg * ε ≤ β / 2) (hcg1 : cg * ε ≤ 1) (hε1 : ε ≤ 1)
    (hcZ : 0 ≤ cZ') (hcn : 0 ≤ cn)
    (hζ : ∀ i ≤ j, ‖stZeta R (rawHist R i t)‖ ≤ cZ' * (t i).1)
    (hn : ∀ k < j, ‖nCor (stNu R k (rawHist R k t) (t k).2.1) (rawHist R k t).w1‖ ≤ cn * (t k).1) :
    let z := stZ' R (rawHist R j t)
    let S := ∑ k ∈ range j, ((histFS R j t).κ k).g ^ 2 *
      (histFS R j t).beta j k 0 R.i₀ (eC 3) (eC 3) 3
    let ES := ∑ k ∈ range j, (stGr R k (rawHist R k t) (t k).1 (t k).2.1 ^ 2 *
      (stZ' R (rawHist R k t) / z) ^ 4 - ((t j).1 : ℂ) ^ 2) * hbTil R j t k
    S = z ^ 2 * (((t j).1 : ℂ) ^ 2 * ∑ k ∈ range j, hbTil R j t k + ES) ∧
      ‖ES‖ ≤ (24 * cZ' + 3 * cn + 2 * (2 * β + 1)) *
        (∑ k ∈ range j, ((j : ℝ) - k + 1) * 2 ^ (j - k) * ‖hbTil R j t k‖) * (t j).1 ^ 3 := by
  intro z S ES
  have hρ := (hV 0 (Nat.zero_le _)).2.2.2.1
  have hρ8 := (hV 0 (Nat.zero_le _)).2.2.2.2.1
  have hzne : ∀ i ≤ j, stZ' R (rawHist R i t) ≠ 0 := fun i hi => by
    have H := rawInv_hist R hρ i (fun i' hi' => hV i' (by omega)) t
    have hZ : (rawHist R i t).Z ≠ 0 := H.Z_ne_zero (by linarith)
    have hζ8 : ‖stZeta R (rawHist R i t)‖ ≤ 1 / 8 := (norm_stZeta_le hρ _).trans hρ8
    exact mul_ne_zero hZ (one_add_ne_zero (by linarith))
  have hz0 : z ≠ 0 := hzne j le_rfl
  refine ⟨?_, ?_⟩
  · -- the algebra
    simp only [S, ES, hbTil]
    rw [mul_add, mul_sum, mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun k hk => ?_
    have hk' : k ≤ j := (mem_range.1 hk).le
    have hzk := hzne k hk'
    have e : ((histFS R j t).κ k).g = stGr R k (rawHist R k t) (t k).1 (t k).2.1 *
        stZ' R (rawHist R k t) ^ 2 := rfl
    rw [e]
    field_simp
    ring
  · -- the bound
    have hg := (ht.1 j le_rfl).1
    have hgε := (ht.1 j le_rfl).2.1
    have hg1 : (t j).1 ≤ 1 := hgε.trans hε1
    have hmon : ∀ i ≤ j, (t i).1 ≤ (t j).1 := fun i hi => by
      have h := (g_mono ht hβ hδ1 hcg hcgβ hcg1 i (j - i) (by omega)).1
      rwa [show i + (j - i) = j by omega] at h
    refine (norm_sum_le _ _).trans ?_
    rw [mul_sum, sum_mul]
    refine sum_le_sum fun k hk => ?_
    have hkj : k < j := mem_range.1 hk
    obtain ⟨hmono, hdiff⟩ := g_mono ht hβ hδ1 hcg hcgβ hcg1 k (j - k) (by omega)
    rw [show k + (j - k) = j by omega] at hmono hdiff
    have hdiff' : (t j).1 - (t k).1 ≤ ((j : ℝ) - k) * (2 * β + 1) * (t j).1 ^ 2 := by
      have e : ((j - k : ℕ) : ℝ) = (j : ℝ) - k := by push_cast [Nat.cast_sub hkj.le]; ring
      rw [← e]; exact hdiff
    have hgk := (ht.1 k (by omega)).1
    have hnk : ‖nCor (stNu R k (rawHist R k t) (t k).2.1) (rawHist R k t).w1‖ ≤ cn * (t j).1 :=
      (hn k hkj).trans (mul_le_mul_of_nonneg_left hmono hcn)
    have hz := stZ'_ratio R t k j hkj.le
    have hpc := past_coef_le (ζ := fun i => stZeta R (rawHist R i t)) hkj.le hg.le hg1 hgk.le hmono
      hdiff' hβ hcZ hcn rfl hnk (norm_nCor_le _ _) (hzne k hkj.le) hz
      (fun i hi => (hζ i (mem_Ioc.1 hi).2).trans
        (mul_le_mul_of_nonneg_left (hmon i (mem_Ioc.1 hi).2) hcZ))
      (fun i hi => (norm_stZeta_le hρ _).trans hρ8)
    rw [norm_mul]
    have h0 := norm_nonneg (hbTil R j t k)
    calc ‖stGr R k (rawHist R k t) (t k).1 (t k).2.1 ^ 2 * (stZ' R (rawHist R k t) / z) ^ 4 -
          ((t j).1 : ℂ) ^ 2‖ * ‖hbTil R j t k‖ ≤
        ((j : ℝ) - k + 1) * 2 ^ (j - k) * (24 * cZ' + 3 * cn + 2 * (2 * β + 1)) * (t j).1 ^ 3 *
          ‖hbTil R j t k‖ := mul_le_mul_of_nonneg_right hpc h0
      _ = _ := by ring

/-- The constants of (F1) along histories. -/
def f1cRQ (Cl cS cx : ℝ) : ℝ := 8 * cS * Cl * cx
def f1cRL (L : ℕ) (Cl cV cW : ℝ) : ℝ :=
  Cl * (L : ℝ) ^ 2 * (cNear 2 L * Q1 2 ^ 2 * cV ^ 2 + Q1 2 * (cW + 1))
def f1cRD (L : ℕ) (ClD cx : ℝ) : ℝ := ClD * (L : ℝ) ^ 2 * Q1 2 * cx

set_option maxHeartbeats 4000000 in
/-- **(F1) for the RG map.** Given the values of the one-loop coefficients (`HV`: the coefficient
`2c - (q + ∑ b)` equals `β` up to `E₀ + E₁ g`) and the decay of the past coefficients (`HD`), the band
`|G_j - g_j - β g_j²| ≤ δβ g_j² + c_g g_j³` holds along regular histories. -/
theorem F1_rg : ∃ Cq Cl cS CqD ClD : ℝ, 0 ≤ Cq ∧ 0 ≤ Cl ∧ 1 ≤ cS ∧ 0 ≤ CqD ∧ 0 ≤ ClD ∧
    ∀ (L : ℕ) [NeZero L], 2 ^ (2 + 3) + 8 * 2 < L → pauliL0 2 ≤ L →
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (C₀ η εs CK C₂ CD Cq' Cl' cS' : ℝ),
      StepBounds L R.A C₀ η εs CK C₂ CD Cq' Cl' cS' → 2 ≤ R.A →
    ∀ (Nh : ℕ), (∀ j < Nh, ValidAt R j) → (∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1) →
    ∀ (Λ β δ κ cg cm cT ε : ℝ), ApHyp R Λ κ cg cm cT ε εs C₀ C₂ Cq' Cl' cS' → 0 < β → δ ≤ 1 / 2 →
      cg * ε ≤ β / 2 → cR R Λ cm C₂ * ε ≤ 1 → 8 * cx κ cT * ε ≤ 1 →
    ∀ (KB E0 E1 eA eB : ℝ), 0 ≤ KB → 0 ≤ eA → 0 ≤ eB →
      (∀ j < Nh, ∀ t, Hist.InDh Λ β δ κ cg cm cT ε j t →
        ‖stA R (rawHist R j t) * (R.msq : ℂ) * (rawHist R j t).w1‖ ≤ eA * (t j).1 ∧
        ‖stZ' R (rawHist R j t) ^ 2 * stCov R j (rawHist R j t) (dirVec (Sum.inl 0)) 0 *
            (rawHist R j t).w1 -
          stZ' R (rawHist R j t) ^ 2 * stCov R j (rawHist R j t) 0 0 * (rawHist R j t).w1‖ ≤ eB) →
      (∀ j < Nh, ∀ t, Hist.InDh Λ β δ κ cg cm cT ε j t → ‖hqTil R j t‖ ≤ KB ∧
        ∑ k ∈ range j, ((j : ℝ) - k + 1) * 2 ^ (j - k) * ‖hbTil R j t k‖ ≤ KB) →
      (∀ j < Nh, ∀ t, Hist.InDh Λ β δ κ cg cm cT ε j t →
        |(f1Coef R j t).re - β| ≤ E0 + E1 * (t j).1) →
      f1cn R.ℓ (cmu Λ cm) * ε ≤ 1 / 8 →
      f1cn' L R.ℓ (cZ R) (cmu Λ cm) Cq (f1cRQ Cl cS (cx κ cT)) (f1cRL L Cl (cV R Λ cm) (cW R Λ cm C₂))
        * ε ≤ 1 / 8 →
      (R.ℓ ^ 2 / 7 + f1cw R.ℓ (cmu Λ cm) Cq (f1cRQ Cl cS (cx κ cT))
        (f1cRL L Cl (cV R Λ cm) (cW R Λ cm C₂))) * ε ≤ R.ρ →
      f1e eA eB + E0 ≤ δ * β →
      f1c3 L R.ℓ (cZ R) (cmu Λ cm) Cq (f1cRQ Cl cS (cx κ cT)) (f1cRL L Cl (cV R Λ cm) (cW R Λ cm C₂))
          CqD (f1cRD L ClD (cx κ cT)) KB
          ((24 * (2 * cZ R) + 3 * f1cn R.ℓ (cmu Λ cm) + 2 * (2 * β + 1)) * KB) eA eB + E1 ≤ cg →
      ∀ j < Nh, ∀ t, Hist.InDh Λ β δ κ cg cm cT ε j t →
        |(rgData R).G j t - (t j).1 - β * (t j).1 ^ 2| ≤ δ * β * (t j).1 ^ 2 + cg * (t j).1 ^ 3 := by
  obtain ⟨Cq, Cl, cS, CqD, ClD, hCq, hCl, hcS, hCqD, hClD, hstep⟩ := step_F1
  refine ⟨Cq, Cl, cS, CqD, ClD, hCq, hCl, hcS, hCqD, hClD, ?_⟩
  intro L _ hL8 hLp N R _ _ C₀ η εs CK C₂ CD Cq' Cl' cS' hSB hA2 Nh hV hm1 Λ β δ κ cg cm cT ε
    H hβ hδ1 hcgβ hcR1 hk1 KB E0 E1 eA eB hKB heA heB HS HD HV hs1 hs2 hs3 hband hcg j hj t ht
  have hℓ : 0 < R.ℓ := Fact.out
  have hjN := hj
  have hVj := hV j hj
  have hρ := hVj.2.2.2.1
  have hρ8 := hVj.2.2.2.2.1
  have hVle : ∀ i ≤ j, ValidAt R i := fun i hi => hV i (by omega)
  obtain ⟨hTA, hTB⟩ := HS j hj t ht
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
    (rawK_mem R _ _) R.A hA2 (cZ R) (cmu Λ cm) hcz hcmu hg.le hg1 hz hy hη hηs hμ (hm1 j hj) eA eB heA heB hTA hTB
    hw1Z w ‖x.1‖ ‖x.2‖ (by positivity) (norm_nonneg _) (norm_nonneg _) hw1 hdd1 hk1' hWw
    (le_of_eq (Fnorm_rawD R HI.hu hZ x)) (le_of_eq (Knorm_rawK R HI.hu hZ x)) hv1
    _ _ _ hcRQ hcRL hcRD hRQ hRL hRD _ ((histFS R j t).betaQ j j 0 R.i₀ (eC 3) (eC 3) 3)
    (∑ k ∈ range j, hbTil R j t k) _ KB _ hKB hcES (hist_LS_g R hVle t) hSe hESb' hqb hSBb hn8 hn'8 hζ8
  have hre : (2 * (stZ' R st * stCov R j st (dirVec (Sum.inl 0)) 0) -
      (stZ' R st ^ 2 * (histFS R j t).betaQ j j 0 R.i₀ (eC 3) (eC 3) 3 +
        ∑ k ∈ range j, hbTil R j t k)).re = (f1Coef R j t).re := rfl
  rw [hre] at hS
  have hHV := HV j hj t ht
  show |(histOut R j t).g.re - g - β * g ^ 2| ≤ δ * β * g ^ 2 + cg * g ^ 3
  have hsplit : |(histOut R j t).g.re - g - β * g ^ 2| ≤
      |(histOut R j t).g.re - g - (f1Coef R j t).re * g ^ 2| + |(f1Coef R j t).re - β| * g ^ 2 := by
    have e : (histOut R j t).g.re - g - β * g ^ 2 =
        ((histOut R j t).g.re - g - (f1Coef R j t).re * g ^ 2) + ((f1Coef R j t).re - β) * g ^ 2 := by
      ring
    rw [e]
    refine (abs_add_le _ _).trans (le_of_eq ?_)
    rw [abs_mul, abs_of_nonneg (sq_nonneg g)]
  have h2 : |(f1Coef R j t).re - β| * g ^ 2 ≤ (E0 + E1 * g) * g ^ 2 :=
    mul_le_mul_of_nonneg_right hHV (sq_nonneg g)
  have h3 : (f1e eA eB + E0) * g ^ 2 ≤ δ * β * g ^ 2 :=
    mul_le_mul_of_nonneg_right hband (sq_nonneg g)
  have hg3' : 0 ≤ g ^ 3 := by positivity
  have h4 := mul_le_mul_of_nonneg_right hcg hg3'
  have e5 : (E0 + E1 * g) * g ^ 2 = E0 * g ^ 2 + E1 * g ^ 3 := by ring
  have hS' : |(histOut R j t).g.re - g - (f1Coef R j t).re * g ^ 2| ≤ _ := hS
  linarith [hsplit, h2, h3, h4, hS']

end

end Step2
