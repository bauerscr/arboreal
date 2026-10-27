import PtCorr2.Obs.ObsHistRelE2
import PtCorr2.Obs.ConstSplitHist

/-!
# The `K`/`𝒲` part of `ρ_k` relative to the vertex (Case (2))

`gamWK2_k = ∑_Bε(e^{ℒ_C}Q_k(B)_a) + ∑_Bε((𝔼θ𝒲_k(B))_a)` (`Obs2.gamWK2`):

* **`sum_eps_expLC_Q2O`** (exact): `∑_Bε(e^{ℒ_C}Q(B)_a) = ∑_{X small}(ε(K(X)_a) + C(a,a)m₂(K(X)_a))`
  (`Loc` in Case (2) is `α + βψ̄_aψ_a`, `e^{ℒ_C}ψ̄_aψ_a = ψ̄_aψ_a + C(a,a)`, and `∑_B loc^a_{X,B}`
  preserves `ε` and `m₂`);
* `sum_norm_eps_le_K`, `histKO2_hK1_eps`, `kobs_EK2_eps` (the `ε`-copies of the `m₂` activity
  bounds of `ObsHistRelE`); `norm_eps_expLC_le` (`|ε(e^{ℒ_C}F)| ≤ Q₁‖F‖_{T_j(ℓ)}` for `F` local
  at a block, `GoodCov2 j ℓ C`);
* **`gamWK2_le`**: with the block bounds `WbHc k w`, `KbHc k κ` of the observable flow,
  `|gamWK2_k| ≤ c_N·8κ(1 + |C_k(a,a)|s_k^{-2}) + c_BQ₁w` (`s_k = histS_k`);
* `gamWK2_zero`: `gamWK2_0 = 0` along a trajectory from `obsInit`.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

variable {L N : ℕ} [NeZero L]

/-! ### The localised activity under `ε ∘ e^{ℒ_C}` -/

section Pure

variable {d : ℕ}

theorem eps_expLC_locAp_two (C : Matrix (Lam d L N) (Lam d L N) ℂ) (a : Lam d L N)
    (X Y : Finset (Lam d L N)) (F : Alg d L N) :
    ε (expLC C (locAp Obs.Case.two a X Y F)) =
      ε (locAp Obs.Case.two a X Y F) + C a a * mass2 (locAp Obs.Case.two a X Y F) := by
  obtain ⟨r, s, h⟩ := locAp_two_form a X Y F
  rw [h, map_add, map_smul, map_smul, expLC_one', expLC_pbp_eq, mass2_loc]
  simp only [map_add, map_smul, map_one, eps_pbp, smul_eq_mul]
  ring

/-- **`∑_Bε(e^{ℒ_C}Q(B)_a) = ∑_X(ε(K(X)_a) + C(a,a)m₂(K(X)_a))`** (Case (2)). -/
theorem sum_eps_expLC_Q2O (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
    (K : OAct .two d L N) (hjN : j + 1 < N) :
    ∑ b ∈ blockIdx (L := L) (N := N) j, ε (expLC C (Q2O P j K b : SA .two (Lam d L N)).a) =
      ∑ X ∈ smallSets (L := L) (N := N) j,
        (ε (K X : SA .two (Lam d L N)).a + C P.a P.a * mass2 (K X : SA .two (Lam d L N)).a) := by
  classical
  have e1 : ∀ b, ε (expLC C (Q2O P j K b : SA .two (Lam d L N)).a) =
      ∑ X ∈ (smallSets (L := L) (N := N) j).filter (fun X => blockSet j b ⊆ X),
        (ε (locAp Obs.Case.two P.a X (blockSet j b) (K X : SA .two (Lam d L N)).a) +
          C P.a P.a * mass2 (locAp Obs.Case.two P.a X (blockSet j b) (K X : SA .two (Lam d L N)).a)) := by
    intro b
    unfold Q2O
    rw [if_pos hjN, AddSubmonoidClass.coe_finsetSum, sum_a, map_sum, map_sum]
    exact sum_congr (by congr) fun X _ => eps_expLC_locAp_two C P.a X _ _
  rw [sum_congr rfl fun b _ => e1 b]
  rw [sum_comm' (t' := smallSets (L := L) (N := N) j) (s' := fun X => blocks j X) ?_]
  · refine sum_congr rfl fun X hX => ?_
    have hs := mem_smallSets.1 hX
    rw [sum_add_distrib, ← mul_sum, eps_sum_blocks hs.1 hs.2.1.1]
    congr 2
    exact (locMass_two P.a).sum_blocks hs.1 hs.2.1.1 _
  · intro b X
    constructor
    · rintro ⟨hb, hX⟩
      obtain ⟨hXs, hbX⟩ := mem_filter.1 hX
      obtain ⟨x, hx⟩ := mem_blockIdx.1 hb
      exact ⟨mem_blocks.2 ⟨x, hbX hx, mem_blockSet.1 hx⟩, hXs⟩
    · rintro ⟨hb, hX⟩
      exact ⟨mem_blockIdx_of_mem_blocks hb,
        mem_filter.2 ⟨hX, blockSet_subset_of_mem_blocks (mem_smallSets.1 hX).1 hb⟩⟩

/-- `|ε(e^{ℒ_C}F)| ≤ Q₁‖F‖_{T_j(ℓ)}` for `F ∈ 𝒩(B^□)`, `GoodCov2 j ℓ C`. -/
theorem norm_eps_expLC_le (hd : 1 ≤ d) (hL : pauliL0 d ≤ L) {j : ℕ} (hj : j < N) {ℓ : ℝ}
    (hℓ : 0 < ℓ) {C : Matrix (Lam d L N) (Lam d L N) ℂ} (hC : GoodCov2 j ℓ C) {b : Fin d → ℕ}
    {F : Alg d L N} (hF : F ∈ NX (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N))) :
    ‖ε (expLC C F)‖ ≤ Q1 d * (Tj d (L : ℝ) j ℓ F).toReal := by
  have h1 := norm_eps_le hℓ (j + 1) (expLC C F)
  have h2 := EthE_succ_le hd hL hj hℓ hC hF
  rw [ECC_theta] at h2
  have h3 : ENNReal.ofReal (pq d ^ nb j (nbhd j (blockSet (L := L) (N := N) j b))) *
      Tj d (L : ℝ) j ℓ F ≤ ENNReal.ofReal (Q1 d) * Tj d (L : ℝ) j ℓ F :=
    mul_le_mul_right' (ENNReal.ofReal_le_ofReal (pq_pow_le_Q1 hd hj.le b)) _
  have h4 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (tNorm_ne_top (Lpow_pos j) hℓ F)) (h2.trans h3)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by
    have := one_le_Q1 hd; linarith)] at h4
  exact h1.trans h4

end Pure

/-! ### The activity, `ε`-copies -/

section Act

/-- **The `ε`-activity term in `ℓ¹`** (copy of `sum_norm_mass2_le` with `|ε(F)| ≤ ‖F‖_{T(ℓ)}`). -/
theorem sum_norm_eps_le_K {d : ℕ} {N j : ℕ} {c : Obs.Case} (a : Lam d L N)
    (K : Finset (Lam d L N) → OE c (Lam d L N)) {ℓ k wa : ℝ} (hℓ : 0 < ℓ) (hwa : 0 < wa)
    (hk : 0 ≤ k) (hz : ∀ X, IsSmall j X → a ∉ nbhd j X → (K X : SA c (Lam d L N)).a = 0)
    (hK : ∀ X, IsSmall j X →
      ENNReal.ofReal wa * Tj d (L : ℝ) j ℓ (K X : SA c (Lam d L N)).a ≤ ENNReal.ofReal k) :
    ∑ X ∈ smallSets (L := L) (N := N) j, ‖ε (K X : SA c (Lam d L N)).a‖ ≤
      csN d * (k / wa) := by
  classical
  have hcs := Classical.choose_spec (Obs2.card_small_near d)
  set S := smallSets (L := L) (N := N) j
  set S' := S.filter (fun X => a ∈ nbhd j X)
  have hm0 : ε (0 : Alg d L N) = 0 := map_zero _
  have hsplit : ∑ X ∈ S, ‖ε (K X : SA c (Lam d L N)).a‖ =
      ∑ X ∈ S', ‖ε (K X : SA c (Lam d L N)).a‖ := by
    refine (sum_subset (filter_subset _ _) fun X hX hX' => ?_).symm
    rw [hz X (mem_smallSets.1 hX) (fun h => hX' (mem_filter.2 ⟨hX, h⟩)), hm0, norm_zero]
  rw [hsplit]
  have hterm : ∀ X ∈ S', ‖ε (K X : SA c (Lam d L N)).a‖ ≤ k / wa := by
    intro X hX
    refine (norm_eps_le hℓ j _).trans ?_
    have h := hK X (mem_smallSets.1 (mem_filter.1 hX).1)
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hwa.le, ENNReal.toReal_ofReal hk] at h2
    rw [le_div_iff₀ hwa]
    linarith [mul_comm wa (Tj d (L : ℝ) j ℓ (K X : SA c (Lam d L N)).a).toReal]
  have hc : (S'.card : ℝ) ≤ csN d := by exact_mod_cast hcs L N j a
  calc ∑ X ∈ S', ‖ε (K X : SA c (Lam d L N)).a‖
      ≤ ∑ _X ∈ S', k / wa := sum_le_sum hterm
    _ = S'.card * (k / wa) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ csN d * (k / wa) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = csN d * (k / wa) := by ring

theorem histKO2_hK1_eps (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (P : ObsPts 2 L N) (o₀ : ObsSt .two L N) (t : Flow2.Hist.Seq (Xs R)) (j : ℕ)
    (h0 : ObsLocInv P 0 o₀) (h : ∀ i ≤ j, ValidCore R i ∧ RawInv R i (rawHist R i t))
    {ℓ k wa : ℝ} (hℓ : 0 < ℓ) (hwa : 0 < wa) (hk : 0 ≤ k)
    (hK : ∀ X, IsSmall j X → ENNReal.ofReal wa *
      Tj 2 (L : ℝ) j ℓ (histKO2 R P o₀ t j X : SA .two (Lam 2 L N)).a ≤ ENNReal.ofReal k) :
    ∑ X ∈ smallSets (L := L) (N := N) j,
      ‖Grassmann.ε (histKO2 R P o₀ t j X : SA .two (Lam 2 L N)).a‖ ≤ csN 2 * (k / wa) := by
  have ho := obsLocInv_hist R P o₀ h0 t j fun i hi => h i hi.le
  have HL := olocS_full R P (t j).1 (t j).2.1 (st := rawHist R j t)
    (D := rawD R (rawHist R j t).u (t j).2.2) (K := rawK R (rawHist R j t).u (t j).2.2)
    (h j le_rfl).1 (h j le_rfl).2 (rawD_mem R _ _) (rawK_mem R _ _) ho
  refine sum_norm_eps_le_K P.a (histKO2 R P o₀ t j) hℓ hwa hk (fun X hX ha => ?_) hK
  exact ((HL.hK X ⟨hX.1, hX.2.1⟩).2.2.2.2.1 ha).1

set_option maxHeartbeats 2000000 in
/-- **The `ε`-activity term in `ℓ¹` along the flow** (copy of `kobs_EK2`). -/
theorem kobs_EK2_eps (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
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
        ‖Grassmann.ε (histKO2 R P o₀ t j X : SA .two (Lam 2 L N)).a‖ ≤
      csN 2 * (8 * k / wa) := by
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
  refine histKO2_hK1_eps R P o₀ t j hl0 (fun i hi => hval i (by omega)) hs hwa0
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


end Act

/-! ### The bound -/

section Bound

/-- The number `c_B` of blocks `B` with `a ∈ B^□` (`Obs2.card_blocks_near 2`). -/
def cBn : ℕ := Classical.choose (Obs2.card_blocks_near 2)

/-- **`GoodCov2` at the field scale of the history.** -/
theorem goodCov2_histS (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1) (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    (t : Flow2.Hist.Seq (Xs R)) (k : ℕ) (hk : k < Nh)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε k t) :
    GoodCov2 k (histS R k t) (histCovO R t k) := by
  obtain ⟨hVc, HI, -, -, hz, hy, hηρ, -⟩ := hist_raw R hSB hV hm hβ hδ1 H t k hk ht
  set st := rawHist R k t with hst
  have hVc' := hVc
  obtain ⟨-, -, -, -, hρ8, hℓ, -⟩ := hVc'
  have hZ : st.Z ≠ 0 := HI.Z_ne_zero (by linarith)
  have hzy : ‖(st.z + st.y) / st.Z‖ ≤ R.ρ := by
    rw [add_div]; exact (norm_add_le _ _).trans (by linarith)
  have hζ : stZeta R st = (st.z + st.y) / st.Z := by
    unfold stZeta absorbZeta; rw [clampDisk_of_le hzy]
  have hζ8 : ‖stZeta R st‖ ≤ 1 / 8 := by
    rw [hζ, add_div]
    exact (norm_add_le _ _).trans (by linarith)
  have hs := fscale_pos hZ
  have hZ' : stZ' R st ≠ 0 := mul_ne_zero hZ (one_add_ne_zero (by linarith))
  have hs' : 0 < fscale (stZ' R st) := fscale_pos hZ'
  have hsc : fscale (stZ' R st) * R.ℓ + fscale (stZ' R st) * R.ℓ / 4 ≤
      3 / 2 * (fscale st.Z * R.ℓ) := scale_ok hZ hζ8 hℓ
  have hCℓ : fscale (stZ' R st) * R.ℓ / 4 ≤ fscale st.Z * R.ℓ := by
    have : 0 < fscale (stZ' R st) * R.ℓ := mul_pos hs' hℓ
    have : 0 < fscale st.Z * R.ℓ := mul_pos hs hℓ
    linarith
  obtain ⟨hC0, -, -, -⟩ := HI.covL hVc
  have hC : GoodCov2 k (fscale (stZ' R st) * R.ℓ / 4) (stCov R k st) := hC0
  exact hC.mono hCℓ

set_option maxHeartbeats 4000000 in
/-- **The `K`/`𝒲` part of `ρ_k` from the block bounds** (Case (2)):
`|gamWK2_k| ≤ c_N·8κ + |C_k(a,a)|c_N·8κ s_k^{-2} + c_BQ₁w`. -/
theorem gamWK2_le (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1) (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    (hLp : pauliL0 2 ≤ L) (P : ObsPts 2 L N) (o₀ : ObsSt .two L N) (hl0 : ObsLocInv P 0 o₀)
    (t : Flow2.Hist.Seq (Xs R)) (k : ℕ) (hk : k < Nh) (hkN : k + 1 < N)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε k t)
    {w kk : ℝ} (hw : 0 ≤ w) (hkk : 0 ≤ kk) (hW : WbHc R P o₀ t k w) (hK : KbHc R P o₀ t k kk) :
    ‖gamWK2 R P o₀ t k‖ ≤ csN 2 * (8 * kk) +
      ‖histCovO R t k P.a P.a‖ * (csN 2 * (8 * kk) * (histS R k t)⁻¹ ^ 2) +
      (cBn : ℝ) * (Q1 2 * w) := by
  classical
  have hℓ : 0 < R.ℓ := Fact.out
  have hVk := hV k hk
  have hρ1 : R.ρ < 1 := by linarith [hVk.2.2.2.2.1]
  have HI := rawInv_hist R hVk.2.2.2.1 k (fun i hi => hV i (by omega)) t
  have hZ : (rawHist R k t).Z ≠ 0 := HI.Z_ne_zero hρ1
  have hs : 0 < histS R k t := mul_pos (fscale_pos hZ) hℓ
  have hC := goodCov2_histS R hSB hV hm hβ hδ1 H t k hk ht
  have hval := hist_valid R hV t (n := k + 1) (by omega)
  have ho := obsLocInv_hist R P o₀ hl0 t k fun i hi => hval i (by omega)
  have hwa : Obs2.wA.a = ENNReal.ofReal 1 := by simp [Obs2.wA]
  have hw0 : Obs2.wA.ab = 0 := Obs2.wA_ab
  have hKe := kobs_EK2_eps R hSB hV hm hβ hδ1 H P o₀ hl0 t k hk ht Obs2.wA hw0 1 one_pos hwa kk hkk hK
  have hKm := kobs_EK2 R hSB hV hm hβ hδ1 H P o₀ hl0 t k hk ht Obs2.wA hw0 1 one_pos hwa kk hkk hK
  rw [div_one] at hKe hKm
  unfold gamWK2
  rw [sum_eps_expLC_Q2O P k _ _ hkN]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · -- the activity
    refine (norm_sum_le _ _).trans ?_
    have e : ∀ X ∈ smallSets (L := L) (N := N) k,
        ‖Grassmann.ε (histKO2 R P o₀ t k X : SA .two (Lam 2 L N)).a + histCovO R t k P.a P.a *
          mass2 (histKO2 R P o₀ t k X : SA .two (Lam 2 L N)).a‖ ≤
        ‖Grassmann.ε (histKO2 R P o₀ t k X : SA .two (Lam 2 L N)).a‖ + ‖histCovO R t k P.a P.a‖ *
          ‖mass2 (histKO2 R P o₀ t k X : SA .two (Lam 2 L N)).a‖ := fun X _ =>
      (norm_add_le _ _).trans (by rw [norm_mul])
    refine (sum_le_sum e).trans ?_
    rw [sum_add_distrib, ← mul_sum]
    exact add_le_add hKe (mul_le_mul_of_nonneg_left hKm (norm_nonneg _))
  · -- the remainder `𝒲`
    have e : ∀ b, Grassmann.ε (EthO (histCovO R t k) (histWO2 R P o₀ t k b) : SA .two (Lam 2 L N)).a =
        Grassmann.ε (expLC (histCovO R t k) ((obsHist R P o₀ k t).W b : SA .two (Lam 2 L N)).a) := by
      intro b; rw [EthO_a_eq, histWO2_a]
    simp only [e]
    refine (norm_sum_le _ _).trans ?_
    set S := blockIdx (L := L) (N := N) k
    set S' := S.filter (fun b => P.a ∈ nbhd k (blockSet (L := L) (N := N) k b))
    have hsplit : ∑ b ∈ S, ‖Grassmann.ε (expLC (histCovO R t k)
        ((obsHist R P o₀ k t).W b : SA .two (Lam 2 L N)).a)‖ =
        ∑ b ∈ S', ‖Grassmann.ε (expLC (histCovO R t k)
          ((obsHist R P o₀ k t).W b : SA .two (Lam 2 L N)).a)‖ := by
      refine (sum_subset (filter_subset _ _) fun b hb hb' => ?_).symm
      have hna : P.a ∉ nbhd k (blockSet (L := L) (N := N) k b) := fun h =>
        hb' (mem_filter.2 ⟨hb, h⟩)
      rw [((ho.W b).2.2.2.2.1 hna).1, map_zero, map_zero, norm_zero]
    rw [hsplit]
    have hterm : ∀ b ∈ S', ‖Grassmann.ε (expLC (histCovO R t k)
        ((obsHist R P o₀ k t).W b : SA .two (Lam 2 L N)).a)‖ ≤ Q1 2 * w := by
      intro b hb
      have hbS := (mem_filter.1 hb).1
      refine (norm_eps_expLC_le (by norm_num) hLp (by omega) hs hC (ho.W b).2.1).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (by have := one_le_Q1 (d := 2) (by norm_num); linarith)
      have h := hW b hbS
      rw [Obs2.oTo_wA] at h
      have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
      rwa [ENNReal.toReal_ofReal hw] at h2
    have hc : (S'.card : ℝ) ≤ cBn := by
      exact_mod_cast Classical.choose_spec (Obs2.card_blocks_near 2) L N k P.a S subset_rfl
    calc ∑ b ∈ S', ‖Grassmann.ε (expLC (histCovO R t k)
          ((obsHist R P o₀ k t).W b : SA .two (Lam 2 L N)).a)‖
        ≤ ∑ _b ∈ S', Q1 2 * w := sum_le_sum hterm
      _ = S'.card * (Q1 2 * w) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ cBn * (Q1 2 * w) := mul_le_mul_of_nonneg_right hc (mul_nonneg (by
          have := one_le_Q1 (d := 2) (by norm_num); linarith) hw)

/-- **`gamWK2_0 = 0`** along a history from `obsInit` with `K_0 = 0`. -/
theorem gamWK2_zero (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N)
    (V : OCoup .two) {t : Flow2.Hist.Seq (Xs R)} (ht : (t 0).2.2 = 0) :
    gamWK2 R P (obsInit .two V P) t 0 = 0 := by
  have hK : histKO2 R P (obsInit .two V P) t 0 = 0 := by
    unfold histKO2
    rw [show obsHist R P (obsInit .two V P) 0 t = obsInit .two V P from rfl, ht,
      rawK_zeroX R]
    exact fullK_obsInit_zero R P V 0 _
  have h0 : ((0 : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a = 0 := rfl
  unfold gamWK2
  rw [hK]
  simp only [Q2O_zero, h0, map_zero, sum_const_zero, zero_add]
  refine sum_eq_zero fun b _ => ?_
  rw [EthO_a_eq, histWO2_a]
  show ε (expLC _ ((0 : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a) = 0
  rw [h0, map_zero, map_zero]

end Bound

end

end PtCorr2
