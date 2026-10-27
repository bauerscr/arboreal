import PtCorr2.Obs.ObsHistRelW
import Obs2.Flow.BlockFlowE
import Obs2.Flow.MuHist2
import Obs2.Flow.GamChain2

/-!
# The relative `μ^{(2)}` recursion along the history (Case (2), `σ_aψ̄_aψ_a`)

Case-(2) analogue of `obs_hist_rel_w`. The `𝒲^{obs}` and `K^{obs}` steps (`wobs_hist_step`,
`kobs_hist_step`) are case-independent in the norm; in Case (2) the `a` component of `V_k(B)` is
`c_k(B)ψ̄_aψ_a` (no constant for `k ≥ 1`, `Obs2.eps_VpO_a`; at `k = 0` for `γ_a = 0`), whose
`T_j(s)` norm is `≤ |c_k(B)|s²`, so the field-scale sequence of `RelRec` is `s_j = histS_j²`
(`m₂(F) ≤ s^{-2}‖F‖_{T(s)}`, `norm_mass2_le`):

* `Tj_smul_pbp_le`, `eq_mass2_smul_of_eps`, `obsHist2_pure` (`V_k(B)_a = m₂(V_k(B)_a)ψ̄_aψ_a`
  along the history from `obsInit .two V P` with `γ_a = 0`), `shareDev2_obsInit` (`D_0 = 0`);
* `sum_norm_mass2_le`, `histKO2_hK1`, **`kobs_EK2`** (the activity term in `ℓ¹`:
  `∑_X|m₂(K_j(X)_a)| ≤ csN 2·8k·s_j^{-2}`);
* `WbHc`, `KbHc` (block bounds, any case) and the named input **`ProdBd2`** (the `ℓ¹` bound of the
  Case-(2) product parts `G_j(B_+;0) + muProdIncX2`, the analogue of `ProdBd` with `s_i²`);
* **`obs_hist_rel2`**: along a regular history from `obsInit .two V P` (`γ_a = 0`), if
  `|tadInc2 k j| ≤ B_τq^{j−k}ǧ_k`, `|𝔫^{(2)}_i| ≤ c_g r_i`, `1 ≤ c_gc_R`, the `c_δ` condition and
  `ProdBd2` hold, then `‖∑_{B_+}err_j(B_+)‖ ≤ c_δr_j²‖β_j(1 − 𝔫^{(2)}_j)‖`, `c_δr_j² ≤ 1/8`.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

/-! ### Pure facts -/

theorem Tj_smul_pbp_le {d L N : ℕ} [NeZero L] (j : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) (c : ℂ)
    (a : Lam d L N) : Tj d (L : ℝ) j ℓ (c • pbp a) ≤ ENNReal.ofReal (‖c‖ * ℓ ^ 2) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  show tNorm (Dir d) (pPhi d) ((L : ℝ) ^ j) ℓ (c • pbp a) ≤ _
  rw [Step.tNorm_smul, pbp, psibar, psi]
  have h := tNorm_mul_le (E := Dir d) (p := pPhi d) (pow_pos hL0 j) hℓ
    (ψ ((a, -1) : Sf (Lam d L N))) (ψ (a, 1))
  rw [tNorm_ψ (pow_pos hL0 j) hℓ, tNorm_ψ (pow_pos hL0 j) hℓ] at h
  calc ENNReal.ofReal ‖c‖ * tNorm (Dir d) (pPhi d) ((L : ℝ) ^ j) ℓ
        (ψ ((a, -1) : Sf (Lam d L N)) * ψ (a, 1))
      ≤ ENNReal.ofReal ‖c‖ * (ENNReal.ofReal ℓ * ENNReal.ofReal ℓ) := mul_le_mul_left' h _
    _ = ENNReal.ofReal (‖c‖ * ℓ ^ 2) := by
      rw [← ENNReal.ofReal_mul hℓ.le, ← ENNReal.ofReal_mul (norm_nonneg _)]
      ring_nf

theorem eq_mass2_smul_of_eps {d L N : ℕ} [NeZero L] {a : Lam d L N} {F : Alg d L N}
    (hF : Loc2Form a F) (hε : ε F = 0) : F = mass2 F • pbp a := by
  obtain ⟨α, hα⟩ := hF.eq_mass2
  have h0 : α = 0 := by
    have := hε
    rw [hα] at this
    simpa only [map_add, map_smul, map_one, eps_pbp, smul_eq_mul, mul_one, mul_zero,
      add_zero] using this
  conv_lhs => rw [hα]
  rw [h0, zero_smul, zero_add]

theorem eq_mass2_smul_of_smul {d L N : ℕ} [NeZero L] {a : Lam d L N} {F : Alg d L N} {c : ℂ}
    (hF : F = c • pbp a) : F = mass2 F • pbp a := by
  conv_rhs => rw [hF]
  rw [mass2_smul, mass2_pbp, mul_one, hF]

variable {L N : ℕ} [NeZero L]

/-- **The activity term in `ℓ¹`**, Case (2) (`ℓ¹` form of the `m₂` bound). -/
theorem sum_norm_mass2_le {d : ℕ} {N j : ℕ} {c : Obs.Case} (a : Lam d L N)
    (K : Finset (Lam d L N) → OE c (Lam d L N)) {ℓ k wa : ℝ} (hℓ : 0 < ℓ) (hwa : 0 < wa)
    (hk : 0 ≤ k) (hz : ∀ X, IsSmall j X → a ∉ nbhd j X → (K X : SA c (Lam d L N)).a = 0)
    (hK : ∀ X, IsSmall j X →
      ENNReal.ofReal wa * Tj d (L : ℝ) j ℓ (K X : SA c (Lam d L N)).a ≤ ENNReal.ofReal k) :
    ∑ X ∈ smallSets (L := L) (N := N) j, ‖mass2 (K X : SA c (Lam d L N)).a‖ ≤
      csN d * (k / wa) * ℓ⁻¹ ^ 2 := by
  classical
  have hcs := Classical.choose_spec (Obs2.card_small_near d)
  set S := smallSets (L := L) (N := N) j
  set S' := S.filter (fun X => a ∈ nbhd j X)
  have hm0 : mass2 (0 : Alg d L N) = 0 := by
    simpa using mass2_smul (0 : ℂ) (0 : Alg d L N)
  have hsplit : ∑ X ∈ S, ‖mass2 (K X : SA c (Lam d L N)).a‖ =
      ∑ X ∈ S', ‖mass2 (K X : SA c (Lam d L N)).a‖ := by
    refine (sum_subset (filter_subset _ _) fun X hX hX' => ?_).symm
    rw [hz X (mem_smallSets.1 hX) (fun h => hX' (mem_filter.2 ⟨hX, h⟩)), hm0, norm_zero]
  rw [hsplit]
  have hterm : ∀ X ∈ S', ‖mass2 (K X : SA c (Lam d L N)).a‖ ≤ k / wa * ℓ⁻¹ ^ 2 := by
    intro X hX
    refine (norm_mass2_le hℓ j _).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have h := hK X (mem_smallSets.1 (mem_filter.1 hX).1)
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hwa.le, ENNReal.toReal_ofReal hk] at h2
    rw [le_div_iff₀ hwa]
    linarith [mul_comm wa (Tj d (L : ℝ) j ℓ (K X : SA c (Lam d L N)).a).toReal]
  have hc : (S'.card : ℝ) ≤ csN d := by exact_mod_cast hcs L N j a
  calc ∑ X ∈ S', ‖mass2 (K X : SA c (Lam d L N)).a‖
      ≤ ∑ _X ∈ S', k / wa * ℓ⁻¹ ^ 2 := sum_le_sum hterm
    _ = S'.card * (k / wa * ℓ⁻¹ ^ 2) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ csN d * (k / wa * ℓ⁻¹ ^ 2) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = csN d * (k / wa) * ℓ⁻¹ ^ 2 := by ring

theorem histKO2_hK1 (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (P : ObsPts 2 L N) (o₀ : ObsSt .two L N) (t : Flow2.Hist.Seq (Xs R)) (j : ℕ)
    (h0 : ObsLocInv P 0 o₀) (h : ∀ i ≤ j, ValidCore R i ∧ RawInv R i (rawHist R i t))
    {ℓ k wa : ℝ} (hℓ : 0 < ℓ) (hwa : 0 < wa) (hk : 0 ≤ k)
    (hK : ∀ X, IsSmall j X → ENNReal.ofReal wa *
      Tj 2 (L : ℝ) j ℓ (histKO2 R P o₀ t j X : SA .two (Lam 2 L N)).a ≤ ENNReal.ofReal k) :
    ∑ X ∈ smallSets (L := L) (N := N) j,
      ‖mass2 (histKO2 R P o₀ t j X : SA .two (Lam 2 L N)).a‖ ≤ csN 2 * (k / wa) * ℓ⁻¹ ^ 2 := by
  have ho := obsLocInv_hist R P o₀ h0 t j fun i hi => h i hi.le
  have HL := olocS_full R P (t j).1 (t j).2.1 (st := rawHist R j t)
    (D := rawD R (rawHist R j t).u (t j).2.2) (K := rawK R (rawHist R j t).u (t j).2.2)
    (h j le_rfl).1 (h j le_rfl).2 (rawD_mem R _ _) (rawK_mem R _ _) ho
  refine sum_norm_mass2_le P.a (histKO2 R P o₀ t j) hℓ hwa hk (fun X hX ha => ?_) hK
  exact ((HL.hK X ⟨hX.1, hX.2.1⟩).2.2.2.2.1 ha).1

set_option maxHeartbeats 2000000 in
/-- **The activity term in `ℓ¹` along the flow** (Case (2)). -/
theorem kobs_EK2 (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1) (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    (P : ObsPts 2 L N) (o₀ : ObsSt .two L N) (hl0 : ObsLocInv P 0 o₀)
    (t : Flow2.Hist.Seq (Xs R)) (j : ℕ) (hj : j < Nh)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t)
    (w : Wt) (hw0 : w.ab = 0) (wa : ℝ) (hwa0 : 0 < wa) (hwa : w.a = ENNReal.ofReal wa)
    (k : ℝ) (hk0 : 0 ≤ k)
    (hKo : ∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
        oTo w j (histS R j t) ((obsHist R P o₀ j t).K X) ≤ ENNReal.ofReal k) :
    ∑ X ∈ smallSets (L := L) (N := N) j,
        ‖mass2 (histKO2 R P o₀ t j X : SA .two (Lam 2 L N)).a‖ ≤
      csN 2 * (8 * k / wa) * (histS R j t)⁻¹ ^ 2 := by
  have hℓ : 0 < R.ℓ := Fact.out
  have hVj := hV j hj
  have hρ1 : R.ρ < 1 := by linarith [hVj.2.2.2.2.1]
  have HI := rawInv_hist R hVj.2.2.2.1 j (fun i hi => hV i (by omega)) t
  have hZ : (rawHist R j t).Z ≠ 0 := HI.Z_ne_zero hρ1
  obtain ⟨hz, hy, -⟩ := apriori R hSB hV hm hβ hδ1 H j hj.le t ht
  obtain ⟨hg, hgε, -, -⟩ := ht.1 j le_rfl
  have hcz : 0 ≤ cZ R := by unfold cZ; positivity
  have hη : 2 * (cZ R * (t j).1) ≤ R.ρ := by
    have := H.h1; nlinarith [mul_le_mul_of_nonneg_left hgε hcz]
  have hM : (0 : ℝ) ≤ cM := Nat.cast_nonneg _
  have hηs : 8 * cM * R.ℓ ^ 2 * (cZ R * (t j).1) ≤ 1 / 2 := by
    have := H.h2
    nlinarith [mul_le_mul_of_nonneg_left hgε (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num :
      (0:ℝ) ≤ 8) hM) (sq_nonneg R.ℓ)) hcz)]
  have hΔ := (rg_inputs R j hVj.toValidCore _ HI (t j).1 (t j).2.1 (hm j hj) hg.le _ hz hy hη).2
  have hs : 0 < histS R j t := mul_pos (fscale_pos hZ) hℓ
  have hval := hist_valid R hV t (n := j + 1) (by omega)
  have hA : 0 < R.A := Fact.out
  refine histKO2_hK1 R P o₀ t j hl0 (fun i hi => hval i (by omega)) hs hwa0
    (by positivity : (0 : ℝ) ≤ 8 * k) (fun X hX => ?_)
  have hXc : IsConn j X := ⟨hX.1, hX.2.1⟩
  have hnb : nb j X - 2 ^ 2 = 0 := Nat.sub_eq_zero_of_le hX.2.2
  have h1 := oTo_fullK_le R j (rawHist R j t) (rawK R (rawHist R j t).u (t j).2.2)
    (obsHist R P o₀ j t) w hw0 hs hA (by positivity) hηs hΔ X
  simp only [hnb, pow_zero, ENNReal.ofReal_one, one_mul] at h1
  have h2 := hKo X hXc
  simp only [hnb, pow_zero, ENNReal.ofReal_one, one_mul] at h2
  calc ENNReal.ofReal wa * Tj 2 (L : ℝ) j (histS R j t)
        (histKO2 R P o₀ t j X : SA .two (Lam 2 L N)).a
      ≤ oTo w j (histS R j t) (histKO2 R P o₀ t j X) := wa_Tj_a_le_oTo w hwa j _ _
    _ ≤ ENNReal.ofReal 8 * oTo w j (histS R j t) ((obsHist R P o₀ j t).K X) := h1
    _ ≤ ENNReal.ofReal 8 * ENNReal.ofReal k := mul_le_mul_left' h2 _
    _ = ENNReal.ofReal (8 * k) := (ENNReal.ofReal_mul (by norm_num)).symm

/-- The block bound of `𝒲^{obs}_j` (any case). -/
def WbHc {c : Obs.Case} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N)
    (o₀ : ObsSt c L N) (t : Flow2.Hist.Seq (Xs R)) (j : ℕ) (x : ℝ) : Prop :=
  ∀ b ∈ blockIdx (L := L) (N := N) j,
    oTo Obs2.wA j (histS R j t) ((obsHist R P o₀ j t).W b) ≤ ENNReal.ofReal x

/-- The weighted bound of `K^{obs}_j` (any case). -/
def KbHc {c : Obs.Case} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N)
    (o₀ : ObsSt c L N) (t : Flow2.Hist.Seq (Xs R)) (j : ℕ) (k : ℝ) : Prop :=
  ∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
    oTo Obs2.wA j (histS R j t) ((obsHist R P o₀ j t).K X) ≤ ENNReal.ofReal k

/-- **The Case-(2) product parts in `ℓ¹`** (named open input; analogue of `ProdBd` with the
field scale `s_i²` of `m₂`): with sizes `m_i` (`s_i²∑_B|c_i(B)| ≤ m_i`, `‖𝒲^{obs}_i‖ ≤ r_im_i`),
`∑_{B_+}|G_j(B_+;0) + prodInc^{(2)}_j(B_+)| ≤ c_P∑_{i≤j}q^{j−i}r_i²m_i/s_i²`. -/
def ProdBd2 (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N)
    (o₀ : ObsSt .two L N) (t : Flow2.Hist.Seq (Xs R)) (n : ℕ) (rr : ℕ → ℝ) (cP q : ℝ) : Prop :=
  ∀ j < n, ∀ m : ℕ → ℝ, (∀ i ≤ j, 0 ≤ m i ∧
      histS R i t ^ 2 * shA2 (histVO2 R P o₀ t) i ≤ m i ∧ WbHc R P o₀ t i (rr i * m i)) →
    shPr2 P (histCovO R t) (histVO2 R P o₀ t) (histWO2 R P o₀ t) j ≤
      cP * ∑ i ∈ range (j + 1), q ^ (j - i) * (rr i ^ 2 * m i / histS R i t ^ 2)

section Init

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N)
  (t : Flow2.Hist.Seq (Xs R))

/-- **`V_k(B)_a = m₂(V_k(B)_a)ψ̄_aψ_a`** along the history from `obsInit .two V P`, `γ_a = 0`. -/
theorem obsHist2_pure (V : OCoup .two) (hga : OCoup2.ga V = 0) :
    ∀ k b, ((obsHist R P (obsInit .two V P) k t).V b : SA .two (Lam 2 L N)).a =
      mass2 ((obsHist R P (obsInit .two V P) k t).V b : SA .two (Lam 2 L N)).a • pbp P.a
  | 0, b => by
    show ((obsInit .two V P).V b : SA .two (Lam 2 L N)).a = _
    refine eq_mass2_smul_of_smul (c := ind (P.a ∈ blockSet (L := L) (N := N) 0 b) *
      (-OCoup2.mua V)) ?_
    rw [obsInit_two_a, hga, neg_zero, map_zero, zero_sub, pbp, smul_neg, smul_smul, ← neg_smul,
      mul_neg]
  | k + 1, b => by
    have e := histVO2_succ_a R P (obsInit .two V P) t k b
    rw [histVO2_a] at e
    rw [e]
    refine eq_mass2_smul_of_eps (Vnext2O_a_two_form P k _ _ _ _ b
      (obsHist_hform2 R P (obsInit .two V P) t (fun b' => obsInit_two_form P V b') k)) ?_
    rw [Vnext2O, AddSubmonoidClass.coe_finsetSum, sum_a, map_sum]
    exact sum_eq_zero fun b' _ => eps_VpO_a P k _ _ _ _ b'

/-- The initial shares: `D_0 = 0`. -/
theorem shareDev2_obsInit (V : OCoup .two) :
    shareDev2 P.a 0 (histVO2 R P (obsInit .two V P) t 0) = 0 := by
  classical
  have h : ∀ b, mass2 (histVO2 R P (obsInit .two V P) t 0 b : SA .two (Lam 2 L N)).a =
      if P.a ∈ blockSet (L := L) (N := N) 0 b then -OCoup2.mua V else 0 := by
    intro b
    rw [histVO2_a]
    show mass2 (((obsInit .two V P).V b : SA .two (Lam 2 L N)).a) = _
    rw [obsInit_two_a, mass2_smul, Obs2.mass2_sub, mass2_algebraMap, mass2_smul]
    have hp : mass2 (psibar P.a * psi P.a : Alg 2 L N) = 1 := mass2_pbp P.a
    rw [hp]
    by_cases hb : P.a ∈ blockSet (L := L) (N := N) 0 b
    · rw [if_pos hb, ind_pos hb]; ring
    · rw [if_neg hb, ind_neg hb]; ring
  unfold shareDev2
  refine sum_eq_zero fun b _ => ?_
  rw [h b, betaTot2_obsInit]
  split_ifs <;> simp

end Init

section Main

variable {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

set_option maxHeartbeats 4000000 in
/-- **The relative `μ^{(2)}` recursion along the history** (Case (2), initial state
`obsInit .two V P` with `γ_a = 0`, `μ_a ≠ 0`). -/
theorem obs_hist_rel2 {C₀ η ε₀ C₁k : ℝ} (hKB : KObsBounds L R.A C₀ η ε₀ C₁k) (hC₁k : 0 ≤ C₁k)
    {Kw C₁ ε₁ : ℝ} (hWB : WObsBounds L Kw C₁ ε₁) (hC₁ : 0 ≤ C₁)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8)
    (P : ObsPts 2 L N) (V : OCoup .two) (hga : OCoup2.ga V = 0) (hmu : OCoup2.mua V ≠ 0)
    (t : Flow2.Hist.Seq (Xs R))
    (n : ℕ) (hn : n ≤ Nh) (hNh : 0 < Nh) (hnN : n < N)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε n t)
    (hθ0 : 0 ≤ kθ0 L R.A C₀ η) (hθ : kθ0 L R.A C₀ η ≤ 1 / 72)
    (hsm : C₁k * (2 + 2 * (8 * cx κ cT) + 64 * kB (kθ0 L R.A C₀ η) C₁k (8 * cx κ cT)) *
      (cR R Λ cm C₂ * ε) ≤ 1 / 72)
    (hε1 : cR R Λ cm C₂ * ε ≤ 1) (hεε : cR R Λ cm C₂ * ε ≤ ε₀)
    (hεk : (8 * cx κ cT + 64 * kB (kθ0 L R.A C₀ η) C₁k (8 * cx κ cT)) * (cR R Λ cm C₂ * ε) ≤ ε₀)
    (hLw : Kw / L ≤ 1 / 12) (hC₁ε : C₁ * (cR R Λ cm C₂ * ε) ≤ 1 / 12)
    (hε₁ : cR R Λ cm C₂ * ε ≤ ε₁)
    (hβp : 0 < β) (hδ2 : δ ≤ 1 / 2) (hcgε : cg * ε ≤ β / 4)
    {cgb cP cδ Bτ qq : ℝ} (hcg : 0 ≤ cgb) (hcP : 0 ≤ cP) (hcδ0 : 0 ≤ cδ) (hBτ : 0 ≤ Bτ)
    (hqq0 : 0 ≤ qq) (hqq4 : qq ≤ 1 / 4)
    (hcg1 : 1 ≤ cgb * cR R Λ cm C₂) (hcgε' : cgb * (cR R Λ cm C₂ * ε) ≤ 1 / 7)
    (hcδ : 16 * (8 * (csN 2 : ℝ)) * (3 * C₁ + 1) * kB (kθ0 L R.A C₀ η) C₁k (8 * cx κ cT) +
        3 * cP * (3 * C₁ + 1) + 4 * Bτ * cgb * (1 + cgb) +
        4 * Bτ * cgb * cδ * (cR R Λ cm C₂ * ε) ≤ 6 / 7 * cδ)
    (hsumε : cδ * (cR R Λ cm C₂ ^ 2 * (ε / (β / 4))) ≤ 1 / 8)
    (hT : ∀ k j, k < j → j < n →
      ‖tadInc2 P (histCovO R t) (histVO2 R P (obsInit .two V P) t) k j‖ ≤
        Bτ * qq ^ (j - k) * (t k).1)
    (hnn : ∀ i < n, ‖frakN2 P (histCovO R t) (histVO2 R P (obsInit .two V P) t) i‖ ≤
      cgb * (cR R Λ cm C₂ * (t i).1))
    (hPr : ProdBd2 R P (obsInit .two V P) t n (fun j => cR R Λ cm C₂ * (t j).1) cP qq) :
    ∀ j < n, ‖∑ c' ∈ blockIdx (L := L) (N := N) (j + 1),
        shareErr2 P (histCovO R t) (histVO2 R P (obsInit .two V P) t)
          (histWO2 R P (obsInit .two V P) t) (histKO2 R P (obsInit .two V P) t) j
          (blockSet (L := L) (N := N) (j + 1) c')‖ ≤
      cδ * (cR R Λ cm C₂ * (t j).1) ^ 2 *
        ‖betaTot2 (L := L) (N := N) j (histVO2 R P (obsInit .two V P) t j) *
          (1 - frakN2 P (histCovO R t) (histVO2 R P (obsInit .two V P) t) j)‖ ∧
      cδ * (cR R Λ cm C₂ * (t j).1) ^ 2 ≤ 1 / 8 := by
  set o₀ := obsInit .two V P with ho₀
  set B := kB (kθ0 L R.A C₀ η) C₁k (8 * cx κ cT)
  set rr : ℕ → ℝ := fun j => cR R Λ cm C₂ * (t j).1 with hrr
  set cWo := 3 * C₁ + 1
  have h0 : o₀.IsObs := obsInit_isObs .two V P
  have hl0 : ObsLocInv P 0 o₀ := obsLocInv_init .two V P
  have hs0 : ObsSymInv 0 o₀ := obsSymInv_init .two V P
  have HC := muChain2_obsHist R P o₀ t hnN (fun b => obsInit_two_W P V b)
    (fun b => obsInit_two_form P V b)
  have hβ' : 0 < β / 4 := by linarith
  -- the band along the history
  have hcg0 : 0 ≤ cg := H.hcg
  have hinc : ∀ k < n, (t k).1 + β / 4 * (t k).1 ^ 2 ≤ (t (k + 1)).1 := by
    intro k hk
    have hr := ht.2 k hk
    obtain ⟨hg, hgε, -, -⟩ := ht.1 k hk.le
    have h3 : cg * (t k).1 ^ 3 ≤ β / 4 * (t k).1 ^ 2 := by
      have : cg * (t k).1 ≤ cg * ε := mul_le_mul_of_nonneg_left hgε hcg0
      have e : cg * (t k).1 ^ 3 = (cg * (t k).1) * (t k).1 ^ 2 := by ring
      rw [e]; exact mul_le_mul_of_nonneg_right (this.trans hcgε) (sq_nonneg _)
    have hδβ : δ * β * (t k).1 ^ 2 ≤ 1 / 2 * β * (t k).1 ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hδ2 hβ) (sq_nonneg _)
    rw [abs_le] at hr
    linarith [hr.1]
  have hw0 : Obs2.wA.ab = 0 := Obs2.wA_ab
  have hwa : Obs2.wA.a ≠ ⊤ := by simp [Obs2.wA]
  have hwb : Obs2.wA.b ≠ ⊤ := by simp [Obs2.wA]
  have hcx := H.hcx
  have hcb : 0 ≤ 8 * cx κ cT := by positivity
  have hB : 0 ≤ B := by
    have h1 := mul_nonneg hθ0 hcb
    have h2 := mul_nonneg hC₁k (by positivity : (0 : ℝ) ≤ 8 + 2 * (8 * cx κ cT) + (8 * cx κ cT) ^ 2)
    show 0 ≤ kθ0 L R.A C₀ η * (8 * cx κ cT) + C₁k * (8 + 2 * (8 * cx κ cT) + (8 * cx κ cT) ^ 2)
    linarith
  have hcR : 0 ≤ cR R Λ cm C₂ := by
    unfold cR cV cW cZ; have := H.hcmu; have := H.hC₂; positivity
  have hC1 : 0 ≤ C₁k * (2 + 2 * (8 * cx κ cT) + 64 * B) := by positivity
  have hDh : ∀ j ≤ n, Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t := fun j hj =>
    ⟨fun i hi => ht.1 i (by omega), fun i hi => ht.2 i (by omega)⟩
  have hr0 : ∀ j ≤ n, 0 ≤ rr j := fun j hj => mul_nonneg hcR (ht.1 j hj).1.le
  have hrε : ∀ j ≤ n, rr j ≤ cR R Λ cm C₂ * ε := fun j hj =>
    mul_le_mul_of_nonneg_left (ht.1 j hj).2.1 hcR
  -- positivity of the field scales
  have hsj : ∀ j ≤ n, 0 < histS R j t := by
    intro j hj
    rcases Nat.lt_or_ge j Nh with h | h
    · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hs, -⟩ :=
        hist_raw R hSB hV hm hβ hδ1 H t j h (hDh j hj)
      exact hs
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hs'⟩ :=
        hist_raw R hSB hV hm hβ hδ1 H t i (by omega) (hDh i (by omega))
      exact hs'
  -- the block bound of `V^{obs}_j` from the `ℓ¹` size
  have hVo : ∀ j ≤ n, ∀ m, histS R j t ^ 2 * shA2 (histVO2 R P o₀ t) j ≤ m →
      ∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo Obs2.wA j (histS R j t) ((obsHist R P o₀ j t).V b) ≤ ENNReal.ofReal m := by
    intro j hj m hsm b hb'
    have hs := hsj j hj
    rw [Obs2.oTo_wA, obsHist2_pure R P t V hga j b]
    refine (Tj_smul_pbp_le j hs _ _).trans (ENNReal.ofReal_le_ofReal (le_trans ?_ hsm))
    have h1 : ‖mass2 ((obsHist R P o₀ j t).V b : SA .two (Lam 2 L N)).a‖ ≤
        shA2 (histVO2 R P o₀ t) j := by
      rw [← histVO2_a R P o₀ t j b]
      exact single_le_sum (f := fun b => ‖mass2
        (histVO2 R P o₀ t j b : SA .two (Lam 2 L N)).a‖) (fun _ _ => norm_nonneg _) hb'
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  have hgm : ∀ k < n, (t k).1 ≤ (t (k + 1)).1 := fun k hk => by
    have := hinc k hk; have : 0 ≤ β / 4 * (t k).1 ^ 2 := by positivity
    linarith
  have hgmono : ∀ k i, k ≤ i → i ≤ n → (t k).1 ≤ (t i).1 := by
    intro k i hki hin
    induction i, hki using Nat.le_induction with
    | base => exact le_rfl
    | succ i hki ih => exact (ih (by omega)).trans (hgm i (by omega))
  let Tt : ℕ → ℕ → ℝ := fun k j => Bτ * qq ^ (j - k)
  let G : ℕ → ℝ := fun i => (t i).1
  have hG : ∀ i < n, 0 ≤ G i := fun i hi => (ht.1 i hi.le).1.le
  have hTt : ∀ k j, k < j → j < n → ∀ i ∈ Ico k j,
      ‖tadInc2 P (histCovO R t) (histVO2 R P o₀ t) k j‖ ≤ Tt k j * G i := by
    intro k j hkj hj i hi
    have hi' := mem_Ico.1 hi
    refine (hT k j hkj hj).trans (mul_le_mul_of_nonneg_left (hgmono k i hi'.1 (by omega))
      (mul_nonneg hBτ (pow_nonneg hqq0 _)))
  have I : RelIn n (fun j => ‖betaTot2 (L := L) (N := N) j (histVO2 R P o₀ t j)‖)
      (shA2 (histVO2 R P o₀ t)) (fun j => shareDev2 P.a j (histVO2 R P o₀ t j))
      (fun j => shareErrL1_2 P (histCovO R t) (histVO2 R P o₀ t) (histWO2 R P o₀ t)
        (histKO2 R P o₀ t) j)
      (fun j => ‖1 - frakN2 P (histCovO R t) (histVO2 R P o₀ t) j‖)
      (fun j => histS R j t ^ 2) rr
      (shKt2 (histKO2 R P o₀ t))
      (shPr2 P (histCovO R t) (histVO2 R P o₀ t) (histWO2 R P o₀ t))
      (fun _ => 0) G (fun i => ‖frakN2 P (histCovO R t) (histVO2 R P o₀ t) i‖)
      (fun j => Kw / L + C₁ * rr j)
      (fun j => kθ0 L R.A C₀ η + C₁k * (2 + 2 * (8 * cx κ cT) + 64 * B) * rr j)
      Tt (WbHc R P o₀ t) (KbHc R P o₀ t)
      C₁ cWo B (8 * (csN 2 : ℝ)) cP cgb Bτ qq (cR R Λ cm C₂ * ε) cδ := {
    hC₁ := hC₁
    hcW1 := by show (1 : ℝ) ≤ 3 * C₁ + 1; linarith
    hcWC := by show 3 * C₁ ≤ 3 * C₁ + 1; linarith
    hBk := hB
    hcK := by positivity
    hcP := hcP
    hcg := hcg
    hBτ := hBτ
    hq0 := hqq0
    hq := hqq4
    hcδ0 := hcδ0
    hcδ := hcδ
    hsum := by
      have h1 := Step2.sum_sq_le hβ' n hinc
      have h2 : ∑ k ∈ range n, rr k ^ 2 = cR R Λ cm C₂ ^ 2 * ∑ k ∈ range n, (t k).1 ^ 2 := by
        rw [mul_sum]; exact sum_congr rfl fun k _ => by rw [hrr]; ring
      have h3 : ((t n).1 - (t 0).1) / (β / 4) ≤ ε / (β / 4) := by
        have := (ht.1 n le_rfl).2.1; have := (ht.1 0 (Nat.zero_le _)).1
        exact div_le_div_of_nonneg_right (by linarith) hβ'.le
      rw [h2]
      have h4 := mul_le_mul_of_nonneg_left (h1.trans h3) (sq_nonneg (cR R Λ cm C₂))
      have h5 := mul_le_mul_of_nonneg_left h4 hcδ0
      linarith
    hr0 := hr0
    hrb := hrε
    hrm := fun j hj => mul_le_mul_of_nonneg_left (hgm j hj) hcR
    hs := fun j hj => pow_pos (hsj j hj) 2
    hss := by
      intro j hj
      have e : histS R (j + 1) t = histS R j t * fscale (1 + zetaH R j t) := by
        unfold histS
        rw [rawHist_succ_Z, fscale_mul]; ring
      have hz : ‖zetaH R j t‖ ≤ 1 / 8 := (absorb_le R hρ0 _ _).trans hρ
      have h1 := fscale_one_add_ge hz
      have h2 := hsj j hj.le
      have h3 : histS R j t ≤ 15 / 14 * histS R (j + 1) t := by rw [e]; nlinarith
      have h4 : 0 ≤ histS R (j + 1) t := by rw [e]; nlinarith
      show histS R j t ^ 2 ≤ 6 / 5 * histS R (j + 1) t ^ 2
      nlinarith
    ha := by
      intro j hj
      have h1 := (hnn j hj).trans ((mul_le_mul_of_nonneg_left (hrε j hj.le) hcg).trans hcgε')
      have h2 := norm_sub_norm_le (1 : ℂ) (frakN2 P (histCovO R t) (histVO2 R P o₀ t) j)
      have h3 := norm_sub_le (1 : ℂ) (frakN2 P (histCovO R t) (histVO2 R P o₀ t) j)
      rw [norm_one] at h2 h3
      constructor <;> linarith
    hb0 := by
      show 0 < ‖betaTot2 (L := L) (N := N) 0 (histVO2 R P o₀ t 0)‖
      rw [betaTot2_obsInit]; exact norm_pos_iff.2 (neg_ne_zero.2 hmu)
    hD0 := shareDev2_obsInit R P t V
    hWm := fun j x y hx hxy b hb' => (hx b hb').trans (ENNReal.ofReal_le_ofReal hxy)
    hKm := fun j x y hx hxy X hX => (hx X hX).trans (ENNReal.ofReal_le_ofReal hxy)
    hW0 := fun b _ => by
      show oTo Obs2.wA 0 (histS R 0 t) (o₀.W b) ≤ _
      have : o₀.W b = 0 := rfl
      rw [this, oTo_zero']; exact zero_le
    hK0 := fun X _ => by
      show _ * oTo Obs2.wA 0 (histS R 0 t) (o₀.K X) ≤ _
      have : o₀.K X = 0 := rfl
      rw [this, oTo_zero', mul_zero]; exact zero_le
    hθW := fun j hj => by
      have := mul_le_mul_of_nonneg_left (hrε j hj.le) hC₁
      show Kw / L + C₁ * rr j ≤ 1 / 6
      linarith
    hθK := fun j hj => by
      have := mul_le_mul_of_nonneg_left (hrε j hj.le) hC1
      show kθ0 L R.A C₀ η + C₁k * (2 + 2 * (8 * cx κ cT) + 64 * B) * rr j ≤ 1 / 16
      linarith
    hW := fun j hj m w hm0 hw0' hsA hWj =>
      wobs_hist_step R hWB hSB hV hm hβ hδ1 H P Obs2.wA hw0 o₀ h0 hl0 hs0 t j (by omega)
        (hDh j hj.le) hε₁ m w hm0 hw0' (hVo j hj.le m hsA) hWj
    hK := fun j hj m k hm0 hk0 hsA hWj hKj hk8 =>
      kobs_hist_step R hKB hSB hV hm hβ hδ1 H P Obs2.wA hw0 hwa hwb o₀ h0 hl0 hs0 t j (by omega)
        (hDh j hj.le) (64 * B) m k (by positivity) hm0 hk0 hε1 hεε hεk hk8
        (hVo j hj.le m hsA) hWj hKj
    hKt := fun j hj k hk0 hKj => by
      have h := kobs_EK2 R hSB hV hm hβ hδ1 H P o₀ hl0 t j (by omega) (hDh j hj.le) Obs2.wA hw0
        1 one_pos (by simp [Obs2.wA]) k hk0 hKj
      refine h.trans (le_of_eq ?_)
      rw [div_one, inv_pow]; ring
    hPr := hPr
    hT := fun k j _ _ => ⟨mul_nonneg hBτ (pow_nonneg hqq0 _), le_rfl⟩
    hdg := fun i _ => ⟨le_rfl, mul_nonneg hcg (sq_nonneg _)⟩
    hG := fun i hi => ⟨hG i hi, by
      show (t i).1 ≤ cgb * (cR R Λ cm C₂ * (t i).1)
      rw [← mul_assoc]
      have := (ht.1 i hi.le).1.le
      nlinarith⟩
    hnn := fun i hi => ⟨norm_nonneg _, hnn i hi⟩ }
  exact HC.rel_step2 Tt hG hTt I

end Main

end

end PtCorr2
