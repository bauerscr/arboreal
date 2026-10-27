import PtCorr2.Pair.PairVStep1
import PtCorr2.Pair.KObsStepAB
import PtCorr2.Pair.GradABHist1
import Obs2.Est.EstLocU

/-!
# The `V`-step of the joint induction (2): `κ^Q`, `κ^S` from the `wM` sizes; the invariants of
`V_n(B)_{ab}`; the single-scale `V` bound

* **`kappaQ_le_count`**: the anchored `K` sizes summed over the blocks of a region and the small
  sets containing them are `≤ 2c_Nc_S·M` (`c_S` the number of small sets containing a block,
  `c_N` the number of blocks `B` with `x ∈ B^□`) — only blocks near `a` or `b` contribute;
* **`kappaS_le_count`**: the anchored `S_i(B_+)` summed over the blocks of a region are `≤ 2L²·M`
  (only the `(i+1)`-blocks of `a`, `b`, each with `≤ L²` children);
* **`hist_vstep_facts`**: along the history from `j₀` at a scale `j₀ ≤ j < N_h`: `GoodCov2` of the
  covariance with `ℓ_C = s_{j+1}/4`, the locality of `K_j` on small sets and of `S_j(B_+)`, the
  anchoring of the inputs, `ObsSymInv`, and (from a `K'` bound in `wM` weights) the small-set bound
  `‖K_j(X)_{ab}‖ ≤ M_aM_b·8k` (`oTo_fullK_leAB`);
* **`eps_V_ab_histFrom`**: `ε(V_j(B)_{ab}) = 0` along the history;
* **`vbound_scale`**: the `wM` bound of every `V_j(B)` at one scale from the mass and
  gradient/`M₄` bounds (the invariants derived).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2 PolyAux

variable {L N : ℕ} [NeZero L]

/-! ### Counting -/

/-- **`κ^Q` of a region from anchored small-set sizes.** -/
theorem kappaQ_le_count (P : ObsPts 2 L N) {i : ℕ} (K : OAct .two 2 L N)
    (B : Finset (Lam 2 L N))
    (hanc : ∀ Y, IsConn i Y → K Y ∈ (anc P Y : Subalgebra ℂ (OE .two (Lam 2 L N))))
    {ℓ M : ℝ} (hM : 0 ≤ M)
    (hK : ∀ X, IsSmall i X → Tj 2 (L : ℝ) i ℓ (K X : SA .two (Lam 2 L N)).ab ≤ ENNReal.ofReal M)
    {cS cN : ℝ}
    (hcS : ∀ b ∈ blockIdx (L := L) (N := N) i,
      (open Classical in ((smallSets (d := 2) (L := L) (N := N) i).filter
        (fun X => blockSet i b ⊆ X)).card : ℝ) ≤ cS)
    (hcN : ∀ (x : Lam 2 L N) (s : Finset (Fin 2 → ℕ)), s ⊆ blockIdx (L := L) (N := N) i →
      ((s.filter (fun b => x ∈ nbhd i (blockSet (L := L) (N := N) i b))).card : ℝ) ≤ cN) :
    (open Classical in ∑ b ∈ blocks i B,
      ∑ X ∈ (smallSets i).filter (fun X => blockSet i b ⊆ X),
        (Tj 2 (L : ℝ) i ℓ (K X : SA .two (Lam 2 L N)).ab).toReal) ≤ 2 * cN * cS * M := by
  classical
  set s := blocks i B with hs
  have hsI : s ⊆ blockIdx (L := L) (N := N) i := fun b hb => mem_blockIdx_of_mem_blocks hb
  have hcS0 : ∀ b ∈ s, 0 ≤ cS := fun b hb => (Nat.cast_nonneg _).trans (hcS b (hsI hb))
  set ia : (Fin 2 → ℕ) → ℝ := fun b =>
    if P.a ∈ nbhd i (blockSet (L := L) (N := N) i b) then 1 else 0
  set ib : (Fin 2 → ℕ) → ℝ := fun b =>
    if P.b ∈ nbhd i (blockSet (L := L) (N := N) i b) then 1 else 0
  have hterm : ∀ b ∈ s, ∑ X ∈ (smallSets i).filter (fun X => blockSet i b ⊆ X),
      (Tj 2 (L : ℝ) i ℓ (K X : SA .two (Lam 2 L N)).ab).toReal ≤ (ia b + ib b) * (cS * M) := by
    intro b hb
    have hbI := hsI hb
    have hne : (blockSet (L := L) (N := N) i b).Nonempty := by
      obtain ⟨x, -, hx⟩ := mem_image.1 hbI
      exact ⟨x, mem_blockSet.2 hx⟩
    by_cases hnear : P.a ∈ nbhd i (blockSet (L := L) (N := N) i b) ∨
        P.b ∈ nbhd i (blockSet (L := L) (N := N) i b)
    · have h1 : 1 ≤ ia b + ib b := by
        simp only [ia, ib]
        rcases hnear with h | h
        · rw [if_pos h]; split_ifs <;> norm_num
        · rw [if_pos h]; split_ifs <;> norm_num
      have hsum : ∑ X ∈ (smallSets i).filter (fun X => blockSet i b ⊆ X),
          (Tj 2 (L : ℝ) i ℓ (K X : SA .two (Lam 2 L N)).ab).toReal ≤
          ((smallSets (d := 2) (L := L) (N := N) i).filter (fun X => blockSet i b ⊆ X)).card * M := by
        rw [← nsmul_eq_mul]
        refine sum_le_card_nsmul _ _ _ fun X hX => ?_
        exact ENNReal.toReal_le_of_le_ofReal hM (hK X (mem_smallSets_filter.1 hX).1)
      have h2 := mul_le_mul_of_nonneg_right (hcS b hbI) hM
      have h3 : 0 ≤ cS * M := mul_nonneg (hcS0 b hb) hM
      nlinarith
    · push Not at hnear
      have h0 : ∑ X ∈ (smallSets i).filter (fun X => blockSet i b ⊆ X),
          (Tj 2 (L : ℝ) i ℓ (K X : SA .two (Lam 2 L N)).ab).toReal = 0 := by
        refine sum_eq_zero fun X hX => ?_
        obtain ⟨hXs, hbX⟩ := mem_smallSets_filter.1 hX
        have hsub := subset_nbhd_of_small hXs hbX hne
        have hab : (K X : SA .two (Lam 2 L N)).ab = 0 := by
          refine (hanc X ⟨hXs.1, hXs.2.1⟩).2.2 fun ⟨z, hz⟩ => ?_
          obtain ⟨hzX, hzP⟩ := mem_inter.1 hz
          rw [ObsPts.pts, mem_insert, mem_singleton] at hzP
          rcases hzP with rfl | rfl
          · exact hnear.1 (hsub hzX)
          · exact hnear.2 (hsub hzX)
        rw [hab, show Tj 2 (L : ℝ) i ℓ (0 : Alg 2 L N) = 0 from tNorm_zero', ENNReal.toReal_zero]
      rw [h0]
      have : 0 ≤ ia b + ib b := by simp only [ia, ib]; split_ifs <;> norm_num
      exact mul_nonneg this (mul_nonneg (hcS0 b hb) hM)
  have hca : ∑ b ∈ s, ia b ≤ cN := by
    simp only [ia]
    rw [sum_boole]
    exact hcN P.a s hsI
  have hcb : ∑ b ∈ s, ib b ≤ cN := by
    simp only [ib]
    rw [sum_boole]
    exact hcN P.b s hsI
  calc _ ≤ ∑ b ∈ s, (ia b + ib b) * (cS * M) := sum_le_sum hterm
    _ = (∑ b ∈ s, ia b + ∑ b ∈ s, ib b) * (cS * M) := by rw [← sum_mul, sum_add_distrib]
    _ ≤ (cN + cN) * (cS * M) := by
        have h' : 0 ≤ cS := by
          have hb' : blk i (0 : Lam 2 L N) ∈ blockIdx (L := L) (N := N) i :=
            mem_image_of_mem _ (mem_univ _)
          exact (Nat.cast_nonneg _).trans (hcS _ hb')
        exact mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg h' hM)
    _ = 2 * cN * cS * M := by ring

/-- **`κ^S` of a region from anchored `S(B_+)` sizes.** -/
theorem kappaS_le_count (P : ObsPts 2 L N) {i : ℕ} (S : Finset (Lam 2 L N) → Alg 2 L N)
    (B : Finset (Lam 2 L N))
    (h0 : ∀ b ∈ blockIdx (L := L) (N := N) i,
      ¬ (Step2.Bp (L := L) (N := N) i b ∩ P.pts).Nonempty → S (Step2.Bp (L := L) (N := N) i b) = 0)
    {ℓ M : ℝ} (hM : 0 ≤ M)
    (hS : ∀ b ∈ blockIdx (L := L) (N := N) i,
      Tj 2 (L : ℝ) (i + 1) ℓ (S (Step2.Bp (L := L) (N := N) i b)) ≤ ENNReal.ofReal M) :
    ∑ b ∈ blocks i B, (Tj 2 (L : ℝ) (i + 1) ℓ (S (Step2.Bp (L := L) (N := N) i b))).toReal ≤
      2 * (L : ℝ) ^ 2 * M := by
  classical
  set s := blocks i B with hs
  have hsI : s ⊆ blockIdx (L := L) (N := N) i := fun b hb => mem_blockIdx_of_mem_blocks hb
  set ia : (Fin 2 → ℕ) → ℝ := fun b => if par L b = blk (i + 1) P.a then 1 else 0
  set ib : (Fin 2 → ℕ) → ℝ := fun b => if par L b = blk (i + 1) P.b then 1 else 0
  have hterm : ∀ b ∈ s, (Tj 2 (L : ℝ) (i + 1) ℓ (S (Step2.Bp (L := L) (N := N) i b))).toReal ≤
      (ia b + ib b) * M := by
    intro b hb
    have hbI := hsI hb
    have hBp : Step2.Bp (L := L) (N := N) i b = blockSet (i + 1) (par L b) := clo_blockSet hbI
    by_cases hn : (Step2.Bp (L := L) (N := N) i b ∩ P.pts).Nonempty
    · obtain ⟨z, hz⟩ := hn
      obtain ⟨hzB, hzP⟩ := mem_inter.1 hz
      rw [hBp, mem_blockSet] at hzB
      have h1 : 1 ≤ ia b + ib b := by
        simp only [ia, ib]
        rw [ObsPts.pts, mem_insert, mem_singleton] at hzP
        rcases hzP with rfl | rfl
        · rw [if_pos hzB.symm]; split_ifs <;> norm_num
        · rw [if_pos hzB.symm]; split_ifs <;> norm_num
      have := ENNReal.toReal_le_of_le_ofReal hM (hS b hbI)
      nlinarith
    · rw [h0 b hbI hn, show Tj 2 (L : ℝ) (i + 1) ℓ (0 : Alg 2 L N) = 0 from tNorm_zero',
        ENNReal.toReal_zero]
      have : 0 ≤ ia b + ib b := by simp only [ia, ib]; split_ifs <;> norm_num
      exact mul_nonneg this hM
  have hcard : ∀ c : Fin 2 → ℕ, ((s.filter (fun b => par L b = c)).card : ℝ) ≤ (L : ℝ) ^ 2 := by
    intro c
    have hsub : s.filter (fun b => par L b = c) ⊆ blocks i (blockSet (L := L) (N := N) (i + 1) c) :=
      fun b hb => mem_blocks_blockSet_succ.2 ⟨hsI (mem_filter.1 hb).1, (mem_filter.1 hb).2⟩
    have h1 := card_le_card hsub
    have h2 := nb_blockSet_succ_le (L := L) (N := N) (d := 2) i c
    exact_mod_cast h1.trans h2
  have hca : ∑ b ∈ s, ia b ≤ (L : ℝ) ^ 2 := by
    simp only [ia]; rw [sum_boole]; exact hcard _
  have hcb : ∑ b ∈ s, ib b ≤ (L : ℝ) ^ 2 := by
    simp only [ib]; rw [sum_boole]; exact hcard _
  calc _ ≤ ∑ b ∈ s, (ia b + ib b) * M := sum_le_sum hterm
    _ = (∑ b ∈ s, ia b + ∑ b ∈ s, ib b) * M := by rw [← sum_mul, sum_add_distrib]
    _ ≤ ((L : ℝ) ^ 2 + (L : ℝ) ^ 2) * M := mul_le_mul_of_nonneg_right (by linarith) hM
    _ = 2 * (L : ℝ) ^ 2 * M := by ring

/-- **The `ab` norm from a `wM` norm** (no `abSub` needed). -/
theorem Tj_ab_le_of_oTo_wM' {c : Obs.Case} {Ma Mb : ℝ} (hMa : 0 < Ma) (hMb : 0 < Mb) (j : ℕ)
    (ℓ : ℝ) (F : OE c (Lam 2 L N)) {x : ℝ} (hx : oTo (wM Ma Mb) j ℓ F ≤ ENNReal.ofReal x) :
    Tj 2 (L : ℝ) j ℓ (F : SA c (Lam 2 L N)).ab ≤ ENNReal.ofReal (Ma * Mb * x) := by
  have h := (ab_le_oTo (wM Ma Mb) j ℓ F).trans hx
  have hw : (wM Ma Mb).ab = ENNReal.ofReal (Ma * Mb)⁻¹ := by
    show ENNReal.ofReal Ma⁻¹ * ENNReal.ofReal Mb⁻¹ = _
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hMa.le), mul_inv]
  rw [hw] at h
  have hM : 0 < Ma * Mb := mul_pos hMa hMb
  have e : ENNReal.ofReal (Ma * Mb) * ENNReal.ofReal (Ma * Mb)⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul hM.le, mul_inv_cancel₀ hM.ne', ENNReal.ofReal_one]
  calc Tj 2 (L : ℝ) j ℓ (F : SA c (Lam 2 L N)).ab
      = ENNReal.ofReal (Ma * Mb) * (ENNReal.ofReal (Ma * Mb)⁻¹ * Tj 2 (L : ℝ) j ℓ
          (F : SA c (Lam 2 L N)).ab) := by rw [← mul_assoc, e, one_mul]
    _ ≤ ENNReal.ofReal (Ma * Mb) * ENNReal.ofReal x := mul_le_mul_right h _
    _ ≤ ENNReal.ofReal (Ma * Mb * x) := by rw [ENNReal.ofReal_mul hM.le]

/-! ### `ε = 0` along the history -/

section Eps

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N)

/-- **`ε(V_k(B)_{ab}) = 0` along the history from `j`** (from `ε(V_j(B)_{ab}) = 0`). -/
theorem eps_V_ab_histFrom {j : ℕ} {o' : ObsSt .two L N}
    (hz : ∀ b, ε (o'.V b : SA .two (Lam 2 L N)).ab = 0) (t : Hist.Seq (Xs R)) :
    ∀ k b, ε ((obsHistFrom R P j o' k t).V b : SA .two (Lam 2 L N)).ab = 0
  | 0, b => by
    by_cases h : 0 ≤ j
    · rw [obsHistFrom_le o' t h]; exact hz b
    · omega
  | k + 1, b => by
    by_cases hk : k + 1 ≤ j
    · rw [obsHistFrom_le o' t hk]; exact hz b
    · rw [obsHistFrom_succ (by omega)]
      dsimp only [obsStep]
      rw [πobs_ab', Vnext2O, AddSubmonoidClass.coe_finsetSum, SA.sum_ab, map_sum]
      exact sum_eq_zero fun b' _ => eps_VpO_ab _ _ _ _ _ _ b'

end Eps

/-! ### Trajectory facts at one scale -/

section Hist

variable {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

set_option maxHeartbeats 1000000 in
/-- **The structural facts of one step of the history from `j₀`** used by the `V`-step. -/
theorem hist_vstep_facts (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    (P : ObsPts 2 L N) {j₀ : ℕ} (o₀ : ObsSt .two L N) (hl0 : ObsLocInv P j₀ o₀)
    (hs0 : ObsSymInv j₀ o₀) (ha0 : ObsAnchInv P j₀ o₀)
    (t : Flow2.Hist.Seq (Xs R)) (j : ℕ) (hjj : j₀ ≤ j) (hj : j < Nh)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t) :
    GoodCov2 j (histS R (j + 1) t / 4) (histCovO R t j) ∧
    0 < histS R j t ∧ 0 < histS R (j + 1) t ∧
    ObsSymInv j (obsHistFrom R P j₀ o₀ j t) ∧
    OAnchS P j (hVR R P j₀ o₀ t j) (hWR R P j₀ o₀ t j) (hKR R P j₀ o₀ t j) ∧
    (∀ X, IsSmall j X →
      (hKR R P j₀ o₀ t j X : SA .two (Lam 2 L N)).ab ∈ NX (nbhd j X : Set (Lam 2 L N))) ∧
    (∀ b ∈ blockIdx (L := L) (N := N) j,
      (SXO j (histCovO R t j) (hVR R P j₀ o₀ t j) (hWR R P j₀ o₀ t j)
        (Step2.Bp (L := L) (N := N) j b) : SA .two (Lam 2 L N)).ab ∈
        NX (nbhd (j + 1) (Step2.Bp (L := L) (N := N) j b) : Set (Lam 2 L N))) ∧
    (∀ (w : Wt), w.Sub → ∀ k : ℝ,
      (∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
        oTo w j (histS R j t) ((obsHistFrom R P j₀ o₀ j t).K X) ≤ ENNReal.ofReal k) →
      ∀ X, IsSmall j X → oTo w j (histS R j t) (hKR R P j₀ o₀ t j X) ≤ ENNReal.ofReal (8 * k)) := by
  obtain ⟨hVc, HI, hg, -, hz, hy, hη, hηs, -, -, -, -, -, -, -, hsℓ, hsℓ'⟩ :=
    hist_raw R hSB hV hm hβ hδ1 H t j hj ht
  have hval := hist_valid R hV t (n := j + 1) (by omega)
  have hloc := obsLocInv_histFrom' R P hl0 t hjj fun i _ hi => hval i (by omega)
  have hsym := obsSymInv_histFrom' R P hs0 t hjj fun i _ hi => hval i (by omega)
  have hanc := obsAnchInv_histFrom' R P ha0 t hjj
  set st := rawHist R j t
  obtain ⟨hC0, -, -, -⟩ := HI.covL hVc
  have hC : GoodCov2 j (histS R (j + 1) t / 4) (histCovO R t j) := hC0
  have hjN : j + 1 < N := by
    have := (hV j hj).toValidCore.1; omega
  have HL := olocS_full R P (t j).1 (t j).2.1 hVc HI (rawD_mem R st.u (t j).2.2) (rawK_mem R st.u (t j).2.2) hloc
  have HA : OAnchS P j (hVR R P j₀ o₀ t j) (hWR R P j₀ o₀ t j) (hKR R P j₀ o₀ t j) :=
    oanchS_full R P _ _ hanc
  obtain ⟨-, hΔ⟩ := rg_inputs R j hVc st HI (t j).1 (t j).2.1 (hm j hj) hg _ hz hy hη
  have hM : (0 : ℝ) ≤ cM := Nat.cast_nonneg _
  have hη0 : 0 ≤ cZ R * (t j).1 := (norm_nonneg _).trans hz
  refine ⟨hC, hsℓ, hsℓ', hsym, HA, fun X hX => (HL.hK X ⟨hX.1, hX.2.1⟩).2.2.2.1,
    fun b _ => (HL.SX_mem (by norm_num) (by have := (hV j hj).toValidCore.2.2.1; omega) hjN
      (hC.range hjN) b).2.2.2.1, ?_⟩
  intro w hw k hk X hX
  have hA0 : 0 < R.A := Fact.out
  have h1 := oTo_fullK_leAB R j st (rawK R st.u (t j).2.2) (obsHistFrom R P j₀ o₀ j t) w hw hsℓ hA0
    (by positivity : (0 : ℝ) ≤ 8 * cM * R.ℓ ^ 2 * (cZ R * (t j).1)) (by linarith) hΔ X
  have hnb : nb j X - 2 ^ 2 = 0 := by
    have := hX.2.2; unfold nb; omega
  rw [hnb, pow_zero, pow_zero, ENNReal.ofReal_one] at h1
  simp only [one_mul] at h1
  have h2 := hk X ⟨hX.1, hX.2.1⟩
  rw [hnb, pow_zero, ENNReal.ofReal_one, one_mul] at h2
  calc oTo w j (histS R j t) (hKR R P j₀ o₀ t j X) ≤ ENNReal.ofReal 8 *
        oTo w j (histS R j t) ((obsHistFrom R P j₀ o₀ j t).K X) := h1
    _ ≤ ENNReal.ofReal 8 * ENNReal.ofReal k := mul_le_mul_right h2 _
    _ = ENNReal.ofReal (8 * k) := by rw [ENNReal.ofReal_mul (by norm_num)]

end Hist

/-! ### The `V` bound at one scale -/

section VB

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N)

/-- **The `wM` bound of all `V_n(B)` at one scale** from `|m₂(V_n(B)_{ab})| ≤ ρ` and the
gradient/`M₄` size `≤ γ` (base `a` or `b`); the invariants (`abSub`, `𝒩({a,b})`, `IsSym`,
`ε = 0`) come from those of the initial state. -/
theorem vbound_scale (hab : P.a ≠ P.b) {j₀ : ℕ} (o₀ : ObsSt .two L N) (h0 : ObsVabInv P o₀)
    (ha0 : ObsAnchInv P j₀ o₀) (hz : ∀ b, ε (o₀.V b : SA .two (Lam 2 L N)).ab = 0)
    (t : Hist.Seq (Xs R)) {n : ℕ} (hn : j₀ ≤ n) (hs : ObsSymInv n (obsHistFrom R P j₀ o₀ n t))
    {Ma Mb : ℝ} (hMa : 0 < Ma) (hMb : 0 < Mb) (hℓ : 0 < histS R n t) (X : Finset (Lam 2 L N))
    {ρ γ m : ℝ}
    (hρ : ∀ b ∈ blockIdx (L := L) (N := N) n,
      ‖mass2 ((obsHistFrom R P j₀ o₀ n t).V b : SA .two (Lam 2 L N)).ab‖ ≤ ρ)
    (hγ : ∀ b ∈ blockIdx (L := L) (N := N) n,
      gradM4Sz X P.a P.b ((L : ℝ) ^ n) (histS R n t)
          ((obsHistFrom R P j₀ o₀ n t).V b : SA .two (Lam 2 L N)).ab ≤ γ ∨
        gradM4Sz X P.b P.a ((L : ℝ) ^ n) (histS R n t)
          ((obsHistFrom R P j₀ o₀ n t).V b : SA .two (Lam 2 L N)).ab ≤ γ)
    (hm : (Ma * Mb)⁻¹ * (ρ * (histS R n t * histS R n t) + γ) ≤ m) :
    ∀ b ∈ blockIdx (L := L) (N := N) n,
      oTo (wM Ma Mb) n (histS R n t) ((obsHistFrom R P j₀ o₀ n t).V b) ≤ ENNReal.ofReal m := by
  intro b hb
  have hA := obsAnchInv_histFrom' R P ha0 t hn
  exact (oTo_wM_le_massP hMa hMb n hℓ X hab (anchSub_ab (hA.V b))
    (obsVabInv_histFrom R P h0 t n b) (isSym_ab_of_symSub (hs.V b))
    (eps_V_ab_histFrom R P hz t n b) (hρ b hb) (hγ b hb)).trans (ENNReal.ofReal_le_ofReal hm)

end VB

end

end PtCorr2
