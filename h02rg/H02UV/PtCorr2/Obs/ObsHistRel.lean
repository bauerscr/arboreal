import PtCorr2.Obs.ObsFlow
import PtCorr2.Obs.KObsEK
import Obs2.Flow.BlockFlow2
import Obs2.Flow.MuK
import Step2.Flow.ZetaSharp0

/-!
# The relative coupled observable recursion along the history (Case (1), `σ_a`)

The joint induction of `obs_hist` rerun with **sizes proportional to the coupling**,
`M_j = 2s_j|β_j|`, in the same induction as phase alignment (`Obs2.RelRec.close` via
`Obs2.MuChain.rel_flow`):

* `sum_norm_mass1_le`, `histKO_hK1`, **`kobs_EK1`**: the activity term in `ℓ¹`,
  `∑_{X ∈ 𝒮_j} |m₁(K_j(X)_a)| ≤ c (8k/w_a) s_j^{-1}` (the `ℓ¹` form of `kobs_EK`);
* **`obs_hist_rel`**: along a regular history, the `MuChain` of the history
  (`muChain_obsHist`) satisfies: if the bulk bounds `|g'_{i+1} − g'_i| ≤ c_g r_i²`,
  `|g'_i| ≤ c_g r_i`, `|𝔫_i| ≤ c_g r_i` hold for its couplings, the product parts satisfy
  the `ℓ¹` bound `ProdBd` (both named open inputs), and `c_δ` is chosen as in `RelRec.hcδ`,
  with `c_δ c_R² ε/β' ≤ 1/8`, then for `j ≤ n`: `|β_j| > 0`, phase alignment,
  `‖𝒲^{obs}_j‖ ≤ c_W r_j·2s_j|β_j|`, the `K^{obs}` bound `16c_WB r_j² s_j|β_j|`, the relative
  error `|β_{j+1} − β_j(1−𝔫_j)| ≤ c_δ r_j²|β_j(1−𝔫_j)|` and the product formula
  `|β_j − β_0∏(1−𝔫_k)| ≤ (e^{c_δ∑_{k<j} r_k²} − 1)|β_0∏(1−𝔫_k)|`.

The `𝒲`, `K` steps (`wobs_hist_step`, `kobs_hist_step`), the activity term (`kobs_EK1`), the
tadpole decay (`histCovO_htau`), the field-scale ratio (`fscale_one_add_ge`, `ρ ≤ 1/8`),
the monotonicity and square-summability of `r_j = c_R g_j` (from `g_{k+1} ≥ g_k + β'g_k²`,
`Step2.g_le_of_inc`, `Step2.sum_sq_le`) are discharged.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

/-- The counting constant of `card_small_near`. -/
def csN (d : ℕ) : ℕ := Classical.choose (Obs2.card_small_near d)

/-- **The activity term in `ℓ¹`** (`ℓ¹` form of `Obs2.sum_mass1_le`). -/
theorem sum_norm_mass1_le {d : ℕ} {L : ℕ} [NeZero L] {N j : ℕ} {c : Obs.Case} (a : Lam d L N)
    (K : Finset (Lam d L N) → OE c (Lam d L N)) {ℓ k wa : ℝ} (hℓ : 0 < ℓ) (hwa : 0 < wa)
    (hk : 0 ≤ k) (hz : ∀ X, IsSmall j X → a ∉ nbhd j X → (K X : SA c (Lam d L N)).a = 0)
    (hK : ∀ X, IsSmall j X →
      ENNReal.ofReal wa * Tj d (L : ℝ) j ℓ (K X : SA c (Lam d L N)).a ≤ ENNReal.ofReal k) :
    ∑ X ∈ smallSets (L := L) (N := N) j, ‖mass1 (-1) (K X : SA c (Lam d L N)).a‖ ≤
      csN d * (k / wa) * ℓ⁻¹ := by
  classical
  have hcs := Classical.choose_spec (Obs2.card_small_near d)
  set S := smallSets (L := L) (N := N) j
  set S' := S.filter (fun X => a ∈ nbhd j X)
  have hsplit : ∑ X ∈ S, ‖mass1 (-1) (K X : SA c (Lam d L N)).a‖ =
      ∑ X ∈ S', ‖mass1 (-1) (K X : SA c (Lam d L N)).a‖ := by
    refine (sum_subset (filter_subset _ _) fun X hX hX' => ?_).symm
    rw [hz X (mem_smallSets.1 hX) (fun h => hX' (mem_filter.2 ⟨hX, h⟩)),
      show mass1 (-1) (0 : Alg d L N) = 0 from map_zero (mass1L (d := d) (L := L) (N := N) (-1)),
      norm_zero]
  rw [hsplit]
  have hterm : ∀ X ∈ S', ‖mass1 (-1) (K X : SA c (Lam d L N)).a‖ ≤ k / wa * ℓ⁻¹ := by
    intro X hX
    refine (norm_mass1_le hℓ j (-1) _).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have h := hK X (mem_smallSets.1 (mem_filter.1 hX).1)
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hwa.le, ENNReal.toReal_ofReal hk] at h2
    rw [le_div_iff₀ hwa]
    linarith [mul_comm wa (Tj d (L : ℝ) j ℓ (K X : SA c (Lam d L N)).a).toReal]
  have hc : (S'.card : ℝ) ≤ csN d := by exact_mod_cast hcs L N j a
  calc ∑ X ∈ S', ‖mass1 (-1) (K X : SA c (Lam d L N)).a‖
      ≤ ∑ _X ∈ S', k / wa * ℓ⁻¹ := sum_le_sum hterm
    _ = S'.card * (k / wa * ℓ⁻¹) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ csN d * (k / wa * ℓ⁻¹) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = csN d * (k / wa) * ℓ⁻¹ := by ring

variable {L N : ℕ} [NeZero L]

theorem histKO_hK1 (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (P : ObsPts 2 L N) (o₀ : ObsSt .one L N) (t : Flow2.Hist.Seq (Xs R)) (j : ℕ)
    (h0 : ObsLocInv P 0 o₀) (h : ∀ i ≤ j, ValidCore R i ∧ RawInv R i (rawHist R i t))
    {ℓ k wa : ℝ} (hℓ : 0 < ℓ) (hwa : 0 < wa) (hk : 0 ≤ k)
    (hK : ∀ X, IsSmall j X → ENNReal.ofReal wa *
      Tj 2 (L : ℝ) j ℓ (histKO R P o₀ t j X : SA .one (Lam 2 L N)).a ≤ ENNReal.ofReal k) :
    ∑ X ∈ smallSets (L := L) (N := N) j,
      ‖mass1 (-1) (histKO R P o₀ t j X : SA .one (Lam 2 L N)).a‖ ≤ csN 2 * (k / wa) * ℓ⁻¹ := by
  have ho := obsLocInv_hist R P o₀ h0 t j fun i hi => h i hi.le
  have HL := olocS_full R P (t j).1 (t j).2.1 (st := rawHist R j t)
    (D := rawD R (rawHist R j t).u (t j).2.2) (K := rawK R (rawHist R j t).u (t j).2.2)
    (h j le_rfl).1 (h j le_rfl).2 (rawD_mem R _ _) (rawK_mem R _ _) ho
  refine sum_norm_mass1_le P.a (histKO R P o₀ t j) hℓ hwa hk (fun X hX ha => ?_) hK
  exact ((HL.hK X ⟨hX.1, hX.2.1⟩).2.2.2.2.1 ha).1

set_option maxHeartbeats 2000000 in
/-- **The activity term in `ℓ¹` along the flow** (`ℓ¹` form of `kobs_EK`). -/
theorem kobs_EK1 (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1) (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    (P : ObsPts 2 L N) (o₀ : ObsSt .one L N) (hl0 : ObsLocInv P 0 o₀)
    (t : Flow2.Hist.Seq (Xs R)) (j : ℕ) (hj : j < Nh)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t)
    (w : Wt) (hw0 : w.ab = 0) (wa : ℝ) (hwa0 : 0 < wa) (hwa : w.a = ENNReal.ofReal wa)
    (k : ℝ) (hk0 : 0 ≤ k)
    (hKo : ∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
        oTo w j (histS R j t) ((obsHist R P o₀ j t).K X) ≤ ENNReal.ofReal k) :
    ∑ X ∈ smallSets (L := L) (N := N) j,
        ‖mass1 (-1) (histKO R P o₀ t j X : SA .one (Lam 2 L N)).a‖ ≤
      csN 2 * (8 * k / wa) * (histS R j t)⁻¹ := by
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
  refine histKO_hK1 R P o₀ t j hl0 (fun i hi => hval i (by omega)) hs hwa0
    (by positivity : (0 : ℝ) ≤ 8 * k) (fun X hX => ?_)
  have hXc : IsConn j X := ⟨hX.1, hX.2.1⟩
  have hnb : nb j X - 2 ^ 2 = 0 := Nat.sub_eq_zero_of_le hX.2.2
  have h1 := oTo_fullK_le R j (rawHist R j t) (rawK R (rawHist R j t).u (t j).2.2)
    (obsHist R P o₀ j t) w hw0 hs hA (by positivity) hηs hΔ X
  simp only [hnb, pow_zero, ENNReal.ofReal_one, one_mul] at h1
  have h2 := hKo X hXc
  simp only [hnb, pow_zero, ENNReal.ofReal_one, one_mul] at h2
  calc ENNReal.ofReal wa * Tj 2 (L : ℝ) j (histS R j t)
        (histKO R P o₀ t j X : SA .one (Lam 2 L N)).a
      ≤ oTo w j (histS R j t) (histKO R P o₀ t j X) := wa_Tj_a_le_oTo w hwa j _ _
    _ ≤ ENNReal.ofReal 8 * oTo w j (histS R j t) ((obsHist R P o₀ j t).K X) := h1
    _ ≤ ENNReal.ofReal 8 * ENNReal.ofReal k := mul_le_mul_left' h2 _
    _ = ENNReal.ofReal (8 * k) := (ENNReal.ofReal_mul (by norm_num)).symm

/-- The block bound of `𝒲^{obs}_j` (the predicate `Wb` of `RelRec`). -/
def WbH (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N) (o₀ : ObsSt .one L N) (t : Flow2.Hist.Seq (Xs R))
    (j : ℕ) (x : ℝ) : Prop :=
  ∀ b ∈ blockIdx (L := L) (N := N) j,
    oTo Obs2.wA j (histS R j t) ((obsHist R P o₀ j t).W b) ≤ ENNReal.ofReal x

/-- The weighted bound of `K^{obs}_j` (the predicate `Kb` of `RelRec`). -/
def KbH (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N) (o₀ : ObsSt .one L N) (t : Flow2.Hist.Seq (Xs R))
    (j : ℕ) (k : ℝ) : Prop :=
  ∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
    oTo Obs2.wA j (histS R j t) ((obsHist R P o₀ j t).K X) ≤ ENNReal.ofReal k

/-- **The product parts in `ℓ¹`** (named open input): with sizes `m_i` of the observable parts
(`s_i∑_B|c_i(B)| ≤ m_i`, `‖𝒲^{obs}_i‖ ≤ r_i m_i`) at the scales `i ≤ j`,
`∑_{B_+}|G_j(B_+;0) + prodInc_j(B_+)| ≤ c_P ∑_{i≤j} q^{j-i} r_i² m_i/s_i`. -/
def ProdBd (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N) (o₀ : ObsSt .one L N) (t : Flow2.Hist.Seq (Xs R))
    (n : ℕ) (rr : ℕ → ℝ) (cP q : ℝ) : Prop :=
  ∀ j < n, ∀ m : ℕ → ℝ, (∀ i ≤ j, 0 ≤ m i ∧
      histS R i t * MuChain.shA (histVO R P o₀ t) i ≤ m i ∧ WbH R P o₀ t i (rr i * m i)) →
    MuChain.shPr P (histCovO R t) (histVO R P o₀ t) (histWO R P o₀ t) j ≤
      cP * ∑ i ∈ range (j + 1), q ^ (j - i) * (rr i ^ 2 * m i / histS R i t)

section Hist

variable {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

theorem histVO_a_mass (P : ObsPts 2 L N) (o₀ : ObsSt .one L N) (t : Flow2.Hist.Seq (Xs R))
    (j : ℕ) (b : Fin 2 → ℕ) :
    mass1 (-1) (histVO R P o₀ t j b : SA .one (Lam 2 L N)).a =
      mass1 (-1) ((obsHist R P o₀ j t).V b : SA .one (Lam 2 L N)).a := by
  rw [histVO_a]

set_option maxHeartbeats 4000000 in
/-- **The relative coupled observable recursion along the history** (Case (1), `σ_a`). -/
theorem obs_hist_rel {C₀ η ε₀ C₁k : ℝ} (hKB : KObsBounds L R.A C₀ η ε₀ C₁k) (hC₁k : 0 ≤ C₁k)
    {Kw C₁ ε₁ : ℝ} (hWB : WObsBounds L Kw C₁ ε₁) (hC₁ : 0 ≤ C₁)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8)
    (P : ObsPts 2 L N) (o₀ : ObsSt .one L N) (h0 : o₀.IsObs) (hl0 : ObsLocInv P 0 o₀)
    (hs0 : ObsSymInv 0 o₀) (hf0 : ∀ b, (o₀.V b : SA .one (Lam 2 L N)).a ∈ (ℂ ∙ psibar P.a))
    (hW0a : ∀ b, (o₀.W b : SA .one (Lam 2 L N)).a = 0)
    (t : Flow2.Hist.Seq (Xs R)) (hW0 : ∀ b, oTo Obs2.wA 0 (histS R 0 t) (o₀.W b) = 0)
    (hK0 : ∀ X, oTo Obs2.wA 0 (histS R 0 t) (o₀.K X) = 0)
    (n : ℕ) (hn : n ≤ Nh) (hNh : 0 < Nh) (hnN : n < N) (hVL : ValidAtL R n)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε n t)
    (hθ0 : 0 ≤ kθ0 L R.A C₀ η) (hθ : kθ0 L R.A C₀ η ≤ 1 / 72)
    (hsm : C₁k * (2 + 2 * (8 * cx κ cT) + 64 * kB (kθ0 L R.A C₀ η) C₁k (8 * cx κ cT)) *
      (cR R Λ cm C₂ * ε) ≤ 1 / 72)
    (hε1 : cR R Λ cm C₂ * ε ≤ 1) (hεε : cR R Λ cm C₂ * ε ≤ ε₀)
    (hεk : (8 * cx κ cT + 64 * kB (kθ0 L R.A C₀ η) C₁k (8 * cx κ cT)) * (cR R Λ cm C₂ * ε) ≤ ε₀)
    (hLw : Kw / L ≤ 1 / 12) (hC₁ε : C₁ * (cR R Λ cm C₂ * ε) ≤ 1 / 12)
    (hε₁ : cR R Λ cm C₂ * ε ≤ ε₁)
    {β' : ℝ} (hβ' : 0 < β') (hinc : ∀ k < n, (t k).1 + β' * (t k).1 ^ 2 ≤ (t (k + 1)).1) :
    let B := kB (kθ0 L R.A C₀ η) C₁k (8 * cx κ cT)
    let rr := fun j => cR R Λ cm C₂ * (t j).1
    let cWo := 3 * C₁ + 1
    let bt := fun j => ‖betaTot (L := L) (N := N) j (histVO R P o₀ t j)‖
    ∃ (κ' : ℕ → Step2.Coup) (r' : ℕ → ℂ),
      MuChain P (histCovO R t) (histVO R P o₀ t) (histWO R P o₀ t) (histKO R P o₀ t) κ' r' n ∧
      ∀ {cgb cP Bτ cδ : ℝ}, 0 ≤ cgb → 0 ≤ cP → 0 ≤ cδ →
        18 * ellM R n t ^ 4 ≤ Bτ → cgb * (cR R Λ cm C₂ * ε) ≤ 1 / 7 →
        16 * (8 * (csN 2 : ℝ)) * cWo * B + 3 * cP * cWo + 4 * Bτ * cgb * (1 + cgb) +
          4 * Bτ * cgb * cδ * (cR R Λ cm C₂ * ε) ≤ 6 / 7 * cδ →
        cδ * (cR R Λ cm C₂ ^ 2 * (ε / β')) ≤ 1 / 8 →
        (∀ i < n, ‖(κ' (i + 1)).g - (κ' i).g‖ ≤ cgb * rr i ^ 2) →
        (∀ i < n, ‖(κ' i).g‖ ≤ cgb * rr i) →
        (∀ i < n, ‖frakN (histCovO R t) κ' P.a i‖ ≤ cgb * rr i) →
        ProdBd R P o₀ t n rr cP (((L : ℝ) ^ 2)⁻¹) →
        shareDev P.a 0 (histVO R P o₀ t 0) = 0 → 0 < bt 0 →
        ∀ j ≤ n, 0 < bt j ∧
          shareDev P.a j (histVO R P o₀ t j) ≤ 6 * (cδ * ∑ k ∈ range j, rr k ^ 2) * bt j ∧
          WbH R P o₀ t j (cWo * rr j * (2 * histS R j t * bt j)) ∧
          KbH R P o₀ t j (16 * cWo * B * rr j ^ 2 * (histS R j t * bt j)) ∧
          (j < n → ‖betaTot (L := L) (N := N) (j + 1) (histVO R P o₀ t (j + 1)) -
              betaTot (L := L) (N := N) j (histVO R P o₀ t j) *
                (1 - frakN (histCovO R t) κ' P.a j)‖ ≤
            cδ * rr j ^ 2 * ‖betaTot (L := L) (N := N) j (histVO R P o₀ t j) *
              (1 - frakN (histCovO R t) κ' P.a j)‖) ∧
          ‖betaTot (L := L) (N := N) j (histVO R P o₀ t j) -
              betaTot (L := L) (N := N) 0 (histVO R P o₀ t 0) *
                ∏ k ∈ range j, (1 - frakN (histCovO R t) κ' P.a k)‖ ≤
            (Real.exp (cδ * ∑ k ∈ range j, rr k ^ 2) - 1) *
              ‖betaTot (L := L) (N := N) 0 (histVO R P o₀ t 0) *
                ∏ k ∈ range j, (1 - frakN (histCovO R t) κ' P.a k)‖ := by
  intro B rr cWo bt
  have hVn : ∀ i < n, ValidAt R i := fun i hi => hV i (by omega)
  obtain ⟨κ', r', HC⟩ := muChain_obsHist R P o₀ t hnN hVn hVL h0 hW0a hf0
  refine ⟨κ', r', HC, ?_⟩
  intro cgb cP Bτ cδ hcg hcP hcδ0 hBτ hcgε hcδ hsumε hdg hG hnn hPr hD0 hb0
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
  have hform : ∀ k b, ((obsHist R P o₀ k t).V b : SA .one (Lam 2 L N)).a ∈ (ℂ ∙ psibar P.a) :=
    fun k b => by rw [← histVO_a]; exact obsHist_hform R P o₀ t hf0 k b
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
  have hL2 : (2 : ℝ) ≤ L := by
    have := hVL.1; norm_num at this; exact_mod_cast (by omega : 2 ≤ L)
  -- the block bound of `V^{obs}_j` from the `ℓ¹` size
  have hVo : ∀ j ≤ n, ∀ m, histS R j t * MuChain.shA (histVO R P o₀ t) j ≤ m →
      ∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo Obs2.wA j (histS R j t) ((obsHist R P o₀ j t).V b) ≤ ENNReal.ofReal m := by
    intro j hj m hsm b hb'
    have hs := hsj j hj
    rw [Obs2.oTo_wA, eq_mass1_smul_of_span (hform j b), Tj_smul_psibar j hs]
    refine ENNReal.ofReal_le_ofReal (le_trans ?_ hsm)
    have h1 : ‖mass1 (-1) ((obsHist R P o₀ j t).V b : SA .one (Lam 2 L N)).a‖ ≤
        MuChain.shA (histVO R P o₀ t) j := by
      rw [← histVO_a_mass R P o₀ t j b]
      exact single_le_sum (f := fun b => ‖mass1 (-1)
        (histVO R P o₀ t j b : SA .one (Lam 2 L N)).a‖) (fun _ _ => norm_nonneg _) hb'
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left h1 hs.le
  have hgm : ∀ k < n, (t k).1 ≤ (t (k + 1)).1 := fun k hk => by
    have := hinc k hk; have : 0 ≤ β' * (t k).1 ^ 2 := by positivity
    linarith
  have I : RelIn n bt (MuChain.shA (histVO R P o₀ t))
      (fun j => shareDev P.a j (histVO R P o₀ t j))
      (fun j => shareErrL1 P (histCovO R t) (histVO R P o₀ t) (histWO R P o₀ t)
        (histKO R P o₀ t) κ' j)
      (fun j => ‖1 - frakN (histCovO R t) κ' P.a j‖) (fun j => histS R j t) rr
      (MuChain.shKt (histKO R P o₀ t))
      (MuChain.shPr P (histCovO R t) (histVO R P o₀ t) (histWO R P o₀ t))
      (fun i => ‖(κ' (i + 1)).g - (κ' i).g‖) (fun i => ‖(κ' i).g‖)
      (fun i => ‖frakN (histCovO R t) κ' P.a i‖)
      (fun j => Kw / L + C₁ * rr j)
      (fun j => kθ0 L R.A C₀ η + C₁k * (2 + 2 * (8 * cx κ cT) + 64 * B) * rr j)
      (fun k j => ‖tauC (histCovO R t k) (histCovO R t j) P.a‖) (WbH R P o₀ t) (KbH R P o₀ t)
      C₁ cWo B (8 * (csN 2 : ℝ)) cP cgb Bτ (((L : ℝ) ^ 2)⁻¹) (cR R Λ cm C₂ * ε) cδ := {
    hC₁ := hC₁
    hcW1 := by show (1 : ℝ) ≤ 3 * C₁ + 1; linarith
    hcWC := by show 3 * C₁ ≤ 3 * C₁ + 1; linarith
    hBk := hB
    hcK := by positivity
    hcP := hcP
    hcg := hcg
    hBτ := le_trans (by positivity) hBτ
    hq0 := by positivity
    hq := by
      rw [inv_le_comm₀ (by positivity) (by norm_num)]; nlinarith
    hcδ0 := hcδ0
    hcδ := hcδ
    hsum := by
      have h1 := Step2.sum_sq_le hβ' n hinc
      have h2 : ∑ k ∈ range n, rr k ^ 2 = cR R Λ cm C₂ ^ 2 * ∑ k ∈ range n, (t k).1 ^ 2 := by
        rw [mul_sum]; exact sum_congr rfl fun k _ => by ring
      have h3 : ((t n).1 - (t 0).1) / β' ≤ ε / β' := by
        have := (ht.1 n le_rfl).2.1; have := (ht.1 0 (Nat.zero_le _)).1
        exact div_le_div_of_nonneg_right (by linarith) hβ'.le
      rw [h2]
      have h4 := mul_le_mul_of_nonneg_left (h1.trans h3) (sq_nonneg (cR R Λ cm C₂))
      have h5 := mul_le_mul_of_nonneg_left h4 hcδ0
      linarith
    hr0 := hr0
    hrb := hrε
    hrm := fun j hj => mul_le_mul_of_nonneg_left (hgm j hj) hcR
    hs := hsj
    hss := by
      intro j hj
      have e : histS R (j + 1) t = histS R j t * fscale (1 + zetaH R j t) := by
        unfold histS
        rw [rawHist_succ_Z, fscale_mul]; ring
      have hz : ‖zetaH R j t‖ ≤ 1 / 8 := (absorb_le R hρ0 _ _).trans hρ
      have h1 := fscale_one_add_ge hz
      have h2 := hsj j hj.le
      rw [e]
      nlinarith
    ha := by
      intro j hj
      have h1 := (hnn j hj).trans ((mul_le_mul_of_nonneg_left (hrε j hj.le) hcg).trans
        (by linarith [hcgε] : cgb * (cR R Λ cm C₂ * ε) ≤ 1 / 7))
      have h2 := norm_sub_norm_le (1 : ℂ) (frakN (histCovO R t) κ' P.a j)
      have h3 := norm_sub_le (1 : ℂ) (frakN (histCovO R t) κ' P.a j)
      rw [norm_one] at h2 h3
      constructor <;> linarith
    hb0 := hb0
    hD0 := hD0
    hWm := fun j x y hx hxy b hb' => (hx b hb').trans (ENNReal.ofReal_le_ofReal hxy)
    hKm := fun j x y hx hxy X hX => (hx X hX).trans (ENNReal.ofReal_le_ofReal hxy)
    hW0 := fun b _ => by
      show oTo Obs2.wA 0 (histS R 0 t) (o₀.W b) ≤ _
      rw [hW0 b]; exact zero_le
    hK0 := fun X _ => by
      show _ * oTo Obs2.wA 0 (histS R 0 t) (o₀.K X) ≤ _
      rw [hK0 X, mul_zero]; exact zero_le
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
      have h := kobs_EK1 R hSB hV hm hβ hδ1 H P o₀ hl0 t j (by omega) (hDh j hj.le) Obs2.wA hw0
        1 one_pos (by simp [Obs2.wA]) k hk0 hKj
      refine h.trans (le_of_eq ?_)
      rw [div_one]; ring
    hPr := hPr
    hT := fun k j hkj hj => ⟨norm_nonneg _, (histCovO_htau R P t hnN hVn hVL hj.le k hkj).trans
      (mul_le_mul_of_nonneg_right hBτ (by positivity))⟩
    hdg := fun i hi => ⟨norm_nonneg _, hdg i hi⟩
    hG := fun i hi => ⟨norm_nonneg _, hG i hi⟩
    hnn := fun i hi => ⟨norm_nonneg _, hnn i hi⟩ }
  exact HC.rel_flow I

end Hist

end

end PtCorr2
