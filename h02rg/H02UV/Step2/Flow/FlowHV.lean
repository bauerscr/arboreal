import Step2.Flow.FlowMain
import Step2.D2.D2S01

/-!
# The one-loop inputs of (F1) for the concrete RG map

For `R.P = Pc` (the concrete `P_t` of `prop:d2`), the covariances of a history are the dressed
covariances `Γ^int_k` of the data `dData L N m² ζ` with the history's couplings `ζ`
(`stCov_eq_dData`), and the normalisations agree (`stZ'_eq_dData`). Hence the history-level
coefficients `hqTil`, `hbTil`, `hcTil` equal the `qTil`, `bTil`, `cTil` of `Step2.HV`, `Step2.HD`
(`hqTil_eq`, `hbTil_eq`, `hcTil_eq`), and (HV), (HD), (HS) of `flow_rg` follow
(`HV_hist`, `HD_hist`, `HS_hist`).
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2 Step2.D2

variable {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- The couplings `ζ` of a history do not change once absorbed. -/
theorem rawHist_zeta_stable (t : Hist.Seq (Xs R)) {k m : ℕ} (hk : k < m) :
    ∀ m', m ≤ m' → (rawHist R m' t).ζ k = (rawHist R m t).ζ k
  | m', h => by
    obtain ⟨n, rfl⟩ : ∃ n, m' = m + n := ⟨m' - m, by omega⟩
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [← add_assoc]
      show Function.update (rawHist R (m + n) t).ζ (m + n) _ k = _
      rw [Function.update_of_ne (by omega), ih (by omega)]

/-- The history of couplings after step `j`. -/
def zh (j : ℕ) (t : Hist.Seq (Xs R)) : ℕ → ℂ := (rawHist R (j + 1) t).ζ

theorem stCov_eq_dData (hP : R.P = Pc) {j : ℕ} (t : Hist.Seq (Xs R)) {i : ℕ} (hi : i ≤ j) :
    stCov R i (rawHist R i t) = DressedFRD.kmat ((dData L N R.msq (zh R j t)).Gint i) := by
  have e1 : stCov R i (rawHist R i t) =
      DressedFRD.kmat ((dData L N R.msq (rawHist R (i + 1) t).ζ).Gint i) := by
    have e0 : Function.update (rawHist R i t).ζ i (stZeta R (rawHist R i t)) =
        (rawHist R (i + 1) t).ζ := rfl
    show DressedFRD.kmat ((⟨L, N, R.msq, DressedFRD.frdC R.P R.msq L N,
      Function.update (rawHist R i t).ζ i (stZeta R (rawHist R i t))⟩ :
        DressedFRD.Data 2 (L ^ N)).Gint i) = _
    rw [e0, hP]
  rw [e1]
  have e2 : dData L N R.msq (zh R j t) =
      (dData L N R.msq (rawHist R (i + 1) t).ζ).withζ (zh R j t) := rfl
  rw [e2, DressedFRD.Data.Gint_congr]
  intro k hk
  exact (rawHist_zeta_stable R t (show k < i + 1 by omega) (j + 1) (by omega)).symm

theorem stZ'_eq_dData {j : ℕ} (hV : ∀ i ≤ j, ValidAt R i) (t : Hist.Seq (Xs R)) :
    stZ' R (rawHist R j t) = (dData L N R.msq (zh R j t)).Z (j + 1) := by
  have hρ := (hV 0 (Nat.zero_le _)).2.2.2.1
  have H := rawInv_hist R hρ (j + 1) (fun i hi => hV i (by omega)) t
  rw [show stZ' R (rawHist R j t) = (rawHist R (j + 1) t).Z from rfl, H.hZprod]
  rfl

theorem hbTil_eq (hP : R.P = Pc) (hi0 : R.i₀ = 0) {j : ℕ} (hV : ∀ i ≤ j, ValidAt R i)
    (t : Hist.Seq (Xs R)) {k : ℕ} (hk : k < j) :
    hbTil R j t k = bTil (dData L N R.msq (zh R j t)) (histFS R j t).κ j k := by
  unfold hbTil bTil
  rw [stZ'_eq_dData R hV t, hi0]
  rw [FlowSeq.beta_congr (D := histFS R j t)
    (D' := gFS (dData L N R.msq (zh R j t)) (histFS R j t).κ) hk.le
    (fun i _ hij => by rw [histFS_C R t hij, stCov_eq_dData R hP t hij]) (fun i _ _ => rfl)]

theorem hqTil_eq (hP : R.P = Pc) (hi0 : R.i₀ = 0) {j : ℕ} (hV : ∀ i ≤ j, ValidAt R i)
    (t : Hist.Seq (Xs R)) :
    hqTil R j t = qTil (dData L N R.msq (zh R j t)) (histFS R j t).κ j := by
  unfold hqTil qTil
  rw [stZ'_eq_dData R hV t, hi0]
  have hC : (histFS R j t).C j = (gFS (dData L N R.msq (zh R j t)) (histFS R j t).κ).C j := by
    rw [histFS_C R t le_rfl, stCov_eq_dData R hP t le_rfl]
  have hB : (histFS R j t).betaQ j j 0 0 =
      (gFS (dData L N R.msq (zh R j t)) (histFS R j t).κ).betaQ j j 0 0 := by
    unfold FlowSeq.betaQ
    rw [if_pos rfl, if_pos rfl, hC]
  rw [hB]

theorem hcTil_eq (hP : R.P = Pc) {j : ℕ} (hV : ∀ i ≤ j, ValidAt R i) (t : Hist.Seq (Xs R)) :
    hcTil R j t = cTil (dData L N R.msq (zh R j t)) j := by
  unfold hcTil cTil
  rw [stZ'_eq_dData R hV t, stCov_eq_dData R hP t le_rfl]
  simp only [DressedFRD.kmat, sub_zero]
  rfl

theorem f1Coef_eq (hP : R.P = Pc) (hi0 : R.i₀ = 0) {j : ℕ} (hV : ∀ i ≤ j, ValidAt R i)
    (t : Hist.Seq (Xs R)) :
    f1Coef R j t = 2 * cTil (dData L N R.msq (zh R j t)) j -
      (qTil (dData L N R.msq (zh R j t)) (histFS R j t).κ j +
        ∑ k ∈ range j, bTil (dData L N R.msq (zh R j t)) (histFS R j t).κ j k) := by
  unfold f1Coef
  rw [hcTil_eq R hP hV t, hqTil_eq R hP hi0 hV t,
    sum_congr rfl fun k hk => hbTil_eq R hP hi0 hV t (mem_range.1 hk)]

/-- The common hypotheses of `HV`, `HD`, `S0S1` along a history. -/
theorem hist_dData_hyps {j : ℕ} (hP : R.P = Pc) (hV : ∀ i ≤ j, ValidAt R i)
    (t : Hist.Seq (Xs R)) :
    (∀ i, ‖zh R j t i‖ ≤ R.ρ) ∧
      ∀ i ≤ j, GoodCov2 i (ellM R j t) (DressedFRD.kmat ((dData L N R.msq (zh R j t)).Gint i)) := by
  have hρ := (hV 0 (Nat.zero_le _)).2.2.2.1
  have H := rawInv_hist R hρ (j + 1) (fun i hi => hV i (by omega)) t
  refine ⟨H.hζ, fun i hi => ?_⟩
  rw [← stCov_eq_dData R hP t hi, ← histFS_C R t hi]
  exact histFS_good R hV t i

theorem ellM_nonneg {j : ℕ} (t : Hist.Seq (Xs R)) : 0 ≤ ellM R j t := by
  have hℓ : 0 < R.ℓ := Fact.out
  unfold ellM
  exact sum_nonneg fun i _ => by unfold fscale; positivity

/-- The accumulated zero mode along a history. -/
theorem rawHist_w1_eq (t : Hist.Seq (Xs R)) : ∀ j,
    (rawHist R j t).w1 = ∑ k ∈ range j, ∑ x, stCov R k (rawHist R k t) x 0
  | 0 => rfl
  | j + 1 => by rw [rawHist_w1_succ, rawHist_w1_eq t j, sum_range_succ]

/-- **(HV) along histories.** -/
theorem HV_hist : ∃ E0 : ℝ, 0 ≤ E0 ∧ ∀ (L : ℕ) [NeZero L], 49 ≤ L →
    ∃ ζbar : ℝ, 0 < ζbar ∧ ∃ E1 : ℝ, 0 ≤ E1 ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 → 1 ≤ N →
      0 < R.msq → R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) → R.ρ ≤ ζbar →
      ∀ j, j + 1 < N → (∀ i ≤ j, ValidAt R i) → ∀ t : Hist.Seq (Xs R),
        |(f1Coef R j t).re - 3 * (Real.log L / (2 * Real.pi))| ≤
          E0 + E1 * (dData L N R.msq (zh R j t)).Mz (j + 1) := by
  obtain ⟨E0, hE0, h⟩ := HV
  refine ⟨E0, hE0, fun L _ hL => ?_⟩
  obtain ⟨ζbar, hζ, E1, hE1, h'⟩ := h L hL
  refine ⟨ζbar, hζ, E1, hE1, fun N R _ _ hP hi0 hN hm0 hm hρ j hj hV t => ?_⟩
  obtain ⟨hz, hG⟩ := hist_dData_hyps R hP hV t
  rw [f1Coef_eq R hP hi0 hV t]
  exact h' N R.msq (zh R j t) hN hm0 hm (fun i => (hz i).trans hρ) j hj (ellM R j t)
    (ellM_nonneg R t) hG (histFS R j t).κ

/-- **(HD) along histories.** -/
theorem HD_hist : ∀ (L : ℕ) [NeZero L], 49 ≤ L → ∃ ζbar : ℝ, 0 < ζbar ∧ ∃ KB : ℝ, 0 ≤ KB ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 → 1 ≤ N →
      0 < R.msq → R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) → R.ρ ≤ ζbar →
      ∀ j, j + 1 < N → (∀ i ≤ j, ValidAt R i) → ∀ t : Hist.Seq (Xs R),
        ‖hqTil R j t‖ ≤ KB ∧ ∑ k ∈ range j, ((j : ℝ) - k + 1) * 2 ^ (j - k) * ‖hbTil R j t k‖ ≤ KB := by
  intro L _ hL
  obtain ⟨ζbar, hζ, KB, hKB, h'⟩ := HD L hL
  refine ⟨ζbar, hζ, KB, hKB, fun N R _ _ hP hi0 hN hm0 hm hρ j hj hV t => ?_⟩
  obtain ⟨hz, hG⟩ := hist_dData_hyps R hP hV t
  obtain ⟨h1, h2⟩ := h' N R.msq (zh R j t) hN hm0 hm (fun i => (hz i).trans hρ) j hj (ellM R j t)
    (ellM_nonneg R t) hG (histFS R j t).κ
  refine ⟨by rw [hqTil_eq R hP hi0 hV t]; exact h1, le_trans (le_of_eq ?_) h2⟩
  refine sum_congr rfl fun k hk => ?_
  have hkj := mem_range.1 hk
  rw [hbTil_eq R hP hi0 hV t hkj,
    show ((j : ℝ) - k + 1) = ((j - k + 1 : ℕ) : ℝ) by push_cast [Nat.cast_sub hkj.le]; ring]

/-- **The sharp zero mode and first difference along histories.** -/
theorem S01_hist : ∃ M₀ M₂ : ℝ, 0 ≤ M₀ ∧ 0 ≤ M₂ ∧ ∀ (L : ℕ) [NeZero L], 49 ≤ L →
    ∃ ζbar : ℝ, 0 < ζbar ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → 1 ≤ N →
      0 < R.msq → R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) → R.ρ ≤ ζbar →
      ∀ j, j + 1 < N → (∀ i ≤ j, ValidAt R i) → ∀ t : Hist.Seq (Xs R),
        ‖stZ' R (rawHist R j t) * (rawHist R j t).w1‖ ≤ (M₀ + 1) * ((L : ℝ) ^ j) ^ 2 ∧
        ‖stZ' R (rawHist R j t) * (stCov R j (rawHist R j t) (dirVec (Sum.inl 0)) 0 -
          stCov R j (rawHist R j t) 0 0)‖ ≤ (M₂ + 1) / ((L : ℝ) ^ j) ^ 2 := by
  obtain ⟨M₀, M₂, hM₀, hM₂, h⟩ := S0S1
  refine ⟨M₀, M₂, hM₀, hM₂, fun L _ hL => ?_⟩
  obtain ⟨ζbar, hζ, h'⟩ := h L hL
  refine ⟨ζbar, hζ, fun N R _ _ hP hN hm0 hm hρ j hj hV t => ?_⟩
  obtain ⟨hz, -⟩ := hist_dData_hyps R hP hV t
  obtain ⟨h1, h2⟩ := h' N R.msq (zh R j t) hN hm0 hm (fun i => (hz i).trans hρ) j hj
  refine ⟨le_trans (le_of_eq ?_) h1, le_trans (le_of_eq ?_) h2⟩
  · have e : ∑ k ∈ range j, ∑ x, stCov R k (rawHist R k t) x 0 =
        ∑ k ∈ range j, ∑ x : Lam 2 L N, DressedFRD.kern ((dData L N R.msq (zh R j t)).Gint k) x :=
      sum_congr rfl fun k hk => sum_congr rfl fun x _ => by
        rw [stCov_eq_dData R hP t (mem_range.1 hk).le]
        simp only [DressedFRD.kmat, sub_zero]
    rw [rawHist_w1_eq, stZ'_eq_dData R hV t, e]
  · rw [stZ'_eq_dData R hV t, stCov_eq_dData R hP t le_rfl]
    simp only [DressedFRD.kmat, sub_zero]
    rfl

theorem zh_eq_stZeta (t : Hist.Seq (Xs R)) {i j : ℕ} (hij : i ≤ j) :
    zh R j t i = stZeta R (rawHist R i t) := by
  unfold zh
  rw [rawHist_zeta_stable R t (show i < i + 1 by omega) (j + 1) (by omega)]
  show Function.update (rawHist R i t).ζ i _ i = _
  rw [Function.update_self]
  rfl

/-- **The sharp inputs (HS) and the size of `Mz` along regular histories.** -/
theorem HS_of_S01 {C₀ η εs CK C₂ CD Cq Cl cS : ℝ} (hSB : StepBounds L R.A C₀ η εs CK C₂ CD Cq Cl cS)
    {Nh : ℕ} (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    {Λ β δ κ cg cm cT ε : ℝ} (H : ApHyp R Λ κ cg cm cT ε εs C₀ C₂ Cq Cl cS) (hβ : 0 ≤ β)
    (hδ1 : δ ≤ 1 / 2) (hcgβ : cg * ε ≤ β / 2) {mf M₀ M₂ : ℝ} (hM₀ : 0 ≤ M₀) (hM₂ : 0 ≤ M₂)
    (hmf : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ mf) {j : ℕ} (hj : j < Nh)
    (t : Hist.Seq (Xs R)) (ht : Hist.InDh Λ β δ κ cg cm cT ε j t)
    (hS0 : ‖stZ' R (rawHist R j t) * (rawHist R j t).w1‖ ≤ (M₀ + 1) * ((L : ℝ) ^ j) ^ 2)
    (hS1 : ‖stZ' R (rawHist R j t) * (stCov R j (rawHist R j t) (dirVec (Sum.inl 0)) 0 -
          stCov R j (rawHist R j t) 0 0)‖ ≤ (M₂ + 1) / ((L : ℝ) ^ j) ^ 2) :
    ‖stA R (rawHist R j t) * (R.msq : ℂ) * (rawHist R j t).w1‖ ≤
        16 / 7 * cZ R * (M₀ + 1) * mf * (t j).1 ∧
      ‖stZ' R (rawHist R j t) ^ 2 * stCov R j (rawHist R j t) (dirVec (Sum.inl 0)) 0 *
          (rawHist R j t).w1 -
        stZ' R (rawHist R j t) ^ 2 * stCov R j (rawHist R j t) 0 0 * (rawHist R j t).w1‖ ≤
        (M₀ + 1) * (M₂ + 1) ∧
      (dData L N R.msq (zh R j t)).Mz (j + 1) ≤ 2 * cZ R * (t j).1 := by
  have hρ := (hV j hj).2.2.2.1
  have hρ8 := (hV j hj).2.2.2.2.1
  have hcz : 0 ≤ cZ R := by unfold cZ; positivity
  have hcg1 : cg * ε ≤ 1 := by linarith [H.h6]
  -- `|ζ_i| ≤ 2 C_z g_i ≤ 2 C_z g_j`
  have hζ : ∀ i ≤ j, ‖stZeta R (rawHist R i t)‖ ≤ 2 * cZ R * (t j).1 := fun i hi => by
    obtain ⟨hzi, hyi, -⟩ := apriori R hSB hV hm hβ (by linarith) H i (by omega) t
      ⟨fun i' hi' => ht.1 i' (by omega), fun i' hi' => ht.2 i' (by omega)⟩
    have hmon := (g_mono ht hβ hδ1 H.hcg hcgβ hcg1 i (j - i) (by omega)).1
    rw [show i + (j - i) = j by omega] at hmon
    unfold stZeta absorbZeta
    refine (norm_clampDisk_le_self hρ _).trans ?_
    rw [add_div]; refine (norm_add_le _ _).trans ?_
    nlinarith [mul_le_mul_of_nonneg_left hmon hcz]
  have hg := (ht.1 j le_rfl).1
  refine ⟨?_, ?_, ?_⟩
  · -- `a m² w⁽¹⁾`
    have hρ1 : R.ρ < 1 := by linarith
    have HI := rawInv_hist R hρ j (fun i hi => hV i (by omega)) t
    set st := rawHist R j t
    have hZ : st.Z ≠ 0 := HI.Z_ne_zero hρ1
    have hζ8 : ‖stZeta R st‖ ≤ 1 / 8 := (norm_stZeta_le hρ st).trans hρ8
    have h1ζ : 7 / 8 ≤ ‖1 + stZeta R st‖ := by linarith [norm_one_add_ge (ζ := stZeta R st)]
    have hzn : ‖stZ' R st‖ = ‖st.Z‖ * ‖1 + stZeta R st‖ := norm_stZ'
    have hZn : 0 < ‖st.Z‖ := norm_pos_iff.2 hZ
    have e : stA R st * (R.msq : ℂ) * st.w1 =
        stZeta R st / (1 + stZeta R st) * (R.msq : ℂ) * (stZ' R st * st.w1) := by
      have h1 : (1 + stZeta R st) ≠ 0 := one_add_ne_zero (by linarith)
      show st.Z * stZeta R st * (R.msq : ℂ) * st.w1 = _
      unfold stZ'; field_simp
    rw [e, norm_mul, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs]
    have hz1 : ‖stZeta R st‖ / ‖1 + stZeta R st‖ ≤ 8 / 7 * (2 * cZ R * (t j).1) := by
      rw [div_le_iff₀ (by linarith)]
      have := hζ j le_rfl
      have h0 : 0 ≤ 2 * cZ R * (t j).1 := by positivity
      nlinarith
    have hmf' := hmf j hj
    have hLj : (0 : ℝ) < ((L : ℝ) ^ j) ^ 2 := by
      have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
      positivity
    calc ‖stZeta R st‖ / ‖1 + stZeta R st‖ * |R.msq| * ‖stZ' R st * st.w1‖
        ≤ 8 / 7 * (2 * cZ R * (t j).1) * |R.msq| * ((M₀ + 1) * ((L : ℝ) ^ j) ^ 2) := by gcongr
      _ = 16 / 7 * cZ R * (M₀ + 1) * (t j).1 * (|R.msq| * ((L : ℝ) ^ j) ^ 2) := by ring
      _ ≤ 16 / 7 * cZ R * (M₀ + 1) * (t j).1 * mf := by gcongr
      _ = _ := by ring
  · -- `Z² δ w⁽¹⁾`
    have e : stZ' R (rawHist R j t) ^ 2 * stCov R j (rawHist R j t) (dirVec (Sum.inl 0)) 0 *
          (rawHist R j t).w1 -
        stZ' R (rawHist R j t) ^ 2 * stCov R j (rawHist R j t) 0 0 * (rawHist R j t).w1 =
        (stZ' R (rawHist R j t) * (stCov R j (rawHist R j t) (dirVec (Sum.inl 0)) 0 -
          stCov R j (rawHist R j t) 0 0)) * (stZ' R (rawHist R j t) * (rawHist R j t).w1) := by ring
    rw [e, norm_mul]
    have hLj : (0 : ℝ) < ((L : ℝ) ^ j) ^ 2 := by
      have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
      positivity
    calc _ ≤ (M₂ + 1) / ((L : ℝ) ^ j) ^ 2 * ((M₀ + 1) * ((L : ℝ) ^ j) ^ 2) :=
          mul_le_mul hS1 hS0 (norm_nonneg _) (by positivity)
      _ = _ := by
          rw [div_mul_eq_mul_div, mul_div_assoc, mul_comm (M₀ + 1), mul_div_cancel_left₀ _ hLj.ne',
            mul_comm]
  · -- `Mz`
    refine DressedFRD.Data.Mz_le (by positivity) fun i hi => ?_
    show ‖zh R j t i‖ ≤ _
    rw [zh_eq_stZeta R t (by omega)]
    exact hζ i (by omega)

end

end Step2
