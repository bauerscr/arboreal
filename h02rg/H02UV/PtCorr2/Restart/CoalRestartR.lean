import PtCorr2.Pair.PairLin2
import Obs2.Pair.CoalHistR

/-!
# The relaxed coalescence invariant along the restarted history; the relocated difference datum

* **`crr_coalInvR`**, **`crr_coal_upto`**, **`crr_coal_validL`**: `rpb_coalInv`/`rpb_coal_upto`/
  `rpb_coal_validL` for `ObsCoalInvR P m ρ δ` with `ρ ≤ L^m`: the relaxed invariant along
  `obsHistFrom R P m δ` below `j_ab`, and `V_{ab} = 0`, `u_{ab} = 0` up to `min(j_ab, N_h + 1)`.
* **`crr_rrSt_coalInvR`**: the relocated state `rrSt … P.a P'.a (pl2Beta o) o` of a state with the
  strict invariant `ObsCoalInv P j o` (and `V(B)_a = α_B + β_Bψ̄_aψ_a`) satisfies the relaxed
  invariant at `P'` (`P'.b = P.b`) with `ρ ≥ |P.a − P'.a|_∞`, below coalescence
  (`|P.a − P.b|_∞ ≥ L^{j+1}/2`).
* **`crr_diff_coalInvR`**: the relaxed invariant is closed under `plDiffSt`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2 Flow2.Hist

variable {L N : ℕ} [NeZero L]

/-! ### Along the restarted history -/

section Hist

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N)

theorem crr_rho_le {m j ρ : ℕ} (hρ : ρ ≤ L ^ m) (hmj : m ≤ j) : ρ ≤ L ^ j :=
  hρ.trans (Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) hmj)

/-- **The relaxed invariant along the restarted history** below `j_ab`. -/
theorem crr_coalInvR {c : Obs.Case} {m ρ : ℕ} {δ : ObsSt c L N} (h₀ : δ.IsObs)
    (hinv₀ : ObsCoalInvR P m ρ δ) (hρ : ρ ≤ L ^ m) (hL : 2 ^ (2 + 3) + 8 * 2 < L) {n : ℕ}
    (hnN : n ≤ N) (t : Hist.Seq (Xs R))
    (hC : ∀ k < n, ∀ x y, (L : ℝ) ^ (k + 1) / 2 ≤ supNorm (x - y) →
      stCov R k (rawHist R k t) x y = 0) :
    ∀ j, m ≤ j → j < coal L P.a P.b → j ≤ n → ObsCoalInvR P j ρ (obsHistFrom R P m δ j t) := by
  intro j
  induction j with
  | zero => intro hm _ _; obtain rfl : m = 0 := by omega
            rw [obsHistFrom_self]; exact hinv₀
  | succ k ih =>
    intro hm hk hkn
    rcases Nat.eq_or_lt_of_le hm with e | hlt
    · rw [← e, obsHistFrom_self]; exact hinv₀
    · rw [obsHistFrom_succ (by omega)]
      exact obsStep_coalInvR R P k ρ _ _ _ _ _ (ih (by omega) (by omega) (by omega))
        (obsHistFrom_isObs h₀ t k) hL (by omega) (crr_rho_le hρ (by omega)) (hC k (by omega))
        (pow_le_of_lt_coal hk)

/-- **`V_{ab} = 0`, `u_{ab} = 0` along the restarted history up to `min(j_ab, n)`** (relaxed). -/
theorem crr_coal_upto {c : Obs.Case} {m ρ : ℕ} {δ : ObsSt c L N} (h₀ : δ.IsObs)
    (hinv₀ : ObsCoalInvR P m ρ δ) (hρ : ρ ≤ L ^ m) (hL : 2 ^ (2 + 3) + 8 * 2 < L) {n : ℕ}
    (hn : n ≤ coal L P.a P.b) (hnN : n ≤ N) (t : Hist.Seq (Xs R))
    (hC : ∀ k < n, ∀ x y, (L : ℝ) ^ (k + 1) / 2 ≤ supNorm (x - y) →
      stCov R k (rawHist R k t) x y = 0) :
    ∀ j, m ≤ j → j ≤ n → (∀ B, ((obsHistFrom R P m δ j t).V B : SA c (Lam 2 L N)).ab = 0) ∧
      ((obsHistFrom R P m δ j t).u : SA c (Lam 2 L N)).ab = 0 := by
  have inv := crr_coalInvR R P h₀ hinv₀ hρ hL hnN t hC
  intro j hmj hj
  rcases Nat.lt_or_ge j (coal L P.a P.b) with hlt | hge
  · exact ⟨(inv j hmj hlt hj).Vab, (inv j hmj hlt hj).uab⟩
  · obtain rfl : j = coal L P.a P.b := le_antisymm (hj.trans hn) hge
    rcases Nat.eq_or_lt_of_le hmj with e | hlt
    · rw [← e, obsHistFrom_self]; exact ⟨hinv₀.Vab, hinv₀.uab⟩
    · obtain ⟨k, hk⟩ : ∃ k, coal L P.a P.b = k + 1 := ⟨coal L P.a P.b - 1, by omega⟩
      rw [hk, obsHistFrom_succ (by omega)]
      exact obsStep_coal_lastR R P k ρ _ _ _ _ _ (inv k (by omega) (by omega) (by omega))
        (obsHistFrom_isObs h₀ t k) hL (by omega) (crr_rho_le hρ (by omega)) (hC k (by omega))
        (pow_le_of_lt_coal (by omega))

/-- **`V_{ab} = 0`, `u_{ab} = 0` up to `min(j_ab, N_h + 1)`** (relaxed invariant at `m`). -/
theorem crr_coal_validL {c : Obs.Case} {Nh m ρ : ℕ} (hN : Nh + 2 = N) {δ : ObsSt c L N}
    (h₀ : δ.IsObs) (hinv₀ : ObsCoalInvR P m ρ δ) (hρ : ρ ≤ L ^ m)
    (hL : 2 ^ (2 + 3) + 8 * 2 < L)
    (hV : ∀ k < Nh, ValidAt R k) (hVL : ValidAtL R Nh) (t : Hist.Seq (Xs R)) :
    ∀ j, m ≤ j → j ≤ min (coal L P.a P.b) (Nh + 1) →
      (∀ B, ((obsHistFrom R P m δ j t).V B : SA c (Lam 2 L N)).ab = 0) ∧
      ((obsHistFrom R P m δ j t).u : SA c (Lam 2 L N)).ab = 0 := by
  refine crr_coal_upto R P h₀ hinv₀ hρ hL (min_le_left _ _)
    ((min_le_right _ _).trans (by omega)) t fun k hk x y hxy => ?_
  have hkN : k ≤ Nh := by have := min_le_right (coal L P.a P.b) (Nh + 1); omega
  have H := rawInv_histU R hV hVL t k (by omega)
  exact (covU R hV hVL hkN H).1.range (by omega) x y hxy

/-- **The relaxed invariant up to `min(j_ab, N_h + 1)`** (strictly below `j_ab`), e.g. for the
small-set clause `K_{ab} = 0` of the `ab` chain. -/
theorem crr_coalInv_validL {c : Obs.Case} {Nh m ρ : ℕ} (hN : Nh + 2 = N) {δ : ObsSt c L N}
    (h₀ : δ.IsObs) (hinv₀ : ObsCoalInvR P m ρ δ) (hρ : ρ ≤ L ^ m)
    (hL : 2 ^ (2 + 3) + 8 * 2 < L)
    (hV : ∀ k < Nh, ValidAt R k) (hVL : ValidAtL R Nh) (t : Hist.Seq (Xs R)) :
    ∀ j, m ≤ j → j < coal L P.a P.b → j ≤ Nh + 1 →
      ObsCoalInvR P j ρ (obsHistFrom R P m δ j t) := by
  intro j hmj hj hjN
  refine crr_coalInvR R P h₀ hinv₀ hρ hL (n := min (coal L P.a P.b) (Nh + 1))
    ((min_le_right _ _).trans (by omega)) t (fun k hk x y hxy => ?_) j hmj hj (le_min hj.le hjN)
  have hkN : k ≤ Nh := by have := min_le_right (coal L P.a P.b) (Nh + 1); omega
  have H := rawInv_histU R hV hVL t k (by omega)
  exact (covU R hV hVL hkN H).1.range (by omega) x y hxy

end Hist

/-! ### The initial invariant of the relocated difference datum -/

section Init

variable (R : RGPar 2 L N) (j : ℕ) (st : RawSt 2 L N) (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N)

theorem crr_rrD_zero (a a' : Lam 2 L N) {β : (Fin 2 → ℕ) → ℂ} {b : Fin 2 → ℕ} (h : β b = 0) :
    rrD a a' β b = 0 :=
  Subtype.ext (SA.ext rfl (by show β b • (pbp a - pbp a') = 0; rw [h, zero_smul]) rfl rfl)

theorem crr_rrD_noX (a a' : Lam 2 L N) (β : (Fin 2 → ℕ) → ℂ) (b : Fin 2 → ℕ) :
    rrD a a' β b ∈ noX .two (Lam 2 L N) false :=
  mem_noX.2 ⟨rfl, rfl⟩

theorem crr_beta_zero {o : ObsSt .two L N} {b : Fin 2 → ℕ}
    (h : o.V b ∈ noX .two (Lam 2 L N) true) : pl2Beta o b = 0 := by
  unfold pl2Beta
  have : ((o.V b : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a = 0 := noX_cmp h
  rw [this]
  exact map_zero (mass2L (d := 2) (L := L) (N := N))

theorem crr_far {P P' : ObsPts 2 L N} (hPb : P.b = P'.b) {ρ : ℕ}
    (hρ : supNorm (P.a - P'.a) ≤ ρ) (i : Bool) {X : Finset (Lam 2 L N)}
    (h : FarS (L ^ j + ρ) (P'.pt i) X) : FarS (L ^ j) (P.pt i) X := by
  cases i
  · show FarS (L ^ j) P.b X
    rw [hPb]; exact farS_mono (Nat.le_add_right _ ρ) h subset_rfl
  · intro z hz
    have h1 : L ^ j + ρ ≤ supNorm (z - P'.a) := h z hz
    have e : z - P'.a = (z - P.a) + (P.a - P'.a) := by abel
    have h2 := supNorm_add_le (z - P.a) (P.a - P'.a)
    rw [← e] at h2
    show L ^ j ≤ supNorm (z - P.a)
    omega

/-- The correction term of `rrSt` has no `σ_i` if its pieces have none. -/
theorem crr_corr_noX (a a' : Lam 2 L N) (β : (Fin 2 → ℕ) → ℂ) (o : ObsSt .two L N)
    (i : Bool) {Y : Finset (Lam 2 L N)} (hY : IsPolymer j Y) {b : Fin 2 → ℕ}
    (hD : rrD a a' β b ∈ noX .two (Lam 2 L N) i) (hV : o.V b ∈ noX .two (Lam 2 L N) i)
    (hW : o.W b ∈ noX .two (Lam 2 L N) i)
    (hK : ∀ Z, IsConn j Z → Z ⊆ Y → o.K Z ∈ noX .two (Lam 2 L N) i) :
    rrDel R j st g μ D a a' β o b * KextO j (embF K + o.K) (Y \ blockSet j b) ∈
      noX .two (Lam 2 L N) i := by
  refine mul_mem (mul_mem (neg_mem hD) ?_) ?_
  · exact mul_mem (oexp_mem (neg_mem (add_mem (emb_mem_noX i _) (sub_mem hV hD))))
      (add_mem (one_mem _) (add_mem (emb_mem_noX i _) hW))
  · refine prod_mem fun Z hZ => ?_
    have hYp : IsPolymer j (Y \ blockSet j b) := IsPolymer.sdiff hY (isPolymer_blockSet j b)
    have hZc := isConn_of_mem_comp hYp hZ
    have hZY : Z ⊆ Y := (subset_of_mem_comp hZ).trans sdiff_subset
    exact add_mem (emb_mem_noX i _) (hK Z hZc hZY)

theorem crr_corr_zero (a a' : Lam 2 L N) (β : (Fin 2 → ℕ) → ℂ) (o : ObsSt .two L N)
    {Y : Finset (Lam 2 L N)} {b : Fin 2 → ℕ} (h : β b = 0) :
    rrDel R j st g μ D a a' β o b * KextO j (embF K + o.K) (Y \ blockSet j b) = 0 := by
  unfold rrDel
  rw [crr_rrD_zero a a' h, neg_zero, zero_mul, zero_mul]

/-- **The relocated state satisfies the relaxed coalescence invariant.** -/
theorem crr_rrSt_coalInvR {P P' : ObsPts 2 L N} {o : ObsSt .two L N} (H : ObsCoalInv P j o)
    (hf : ∀ b, Loc2Form P.a ((o.V b : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a)
    (hPb : P.b = P'.b) {ρ : ℕ} (hρ : supNorm (P.a - P'.a) ≤ ρ) (hL : 2 ^ (2 + 3) ≤ L)
    (hab : (L : ℝ) ^ (j + 1) / 2 ≤ supNorm (P.a - P.b)) :
    ObsCoalInvR P' j ρ (rrSt R j st g μ D K P.a P'.a (pl2Beta o) o) := by
  have hβ : ∀ b, FarS (L ^ j) P.a (blockSet (L := L) (N := N) j b) → pl2Beta o b = 0 :=
    fun b hb => crr_beta_zero (H.Vno true b hb)
  refine
  { Vab := fun b => ?_
    Vpt := fun i b => ?_
    Vno := fun i b hb => ?_
    Wab := H.Wab
    Wno := fun i b hb => H.Wno i b (crr_far j hPb hρ i hb)
    Kab := fun Y hY => ?_
    Kno := fun i Y hY hfar => ?_
    uab := H.uab }
  · show ((o.V b - rrD P.a P'.a (pl2Beta o) b : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).ab = 0
    show (o.V b : SA .two (Lam 2 L N)).ab - 0 = 0
    rw [H.Vab b, sub_zero]
  · cases i
    · show (o.V b : SA .two (Lam 2 L N)).b - 0 ∈ NX ({P'.b} : Set (Lam 2 L N))
      rw [sub_zero, ← hPb]; exact H.Vpt false b
    · show (o.V b : SA .two (Lam 2 L N)).a - pl2Beta o b • (pbp P.a - pbp P'.a) ∈
        NX ({P'.a} : Set (Lam 2 L N))
      obtain ⟨α, β', hαβ⟩ := hf b
      have hm : pl2Beta o b = β' := by
        unfold pl2Beta
        rw [hαβ, mass2_add, mass2_smul, mass2_smul, mass2_pbp, mul_one]
        have : mass2 (1 : Alg 2 L N) = 0 := by
          have := mass2_algebraMap (d := 2) (L := L) (N := N) 1
          rwa [map_one] at this
        rw [this, mul_zero, zero_add]
      rw [hαβ, hm, show α • (1 : Alg 2 L N) + β' • pbp P.a - β' • (pbp P.a - pbp P'.a) =
        α • (1 : Alg 2 L N) + β' • pbp P'.a by rw [smul_sub]; abel]
      exact add_mem (Subalgebra.smul_mem _ (one_mem _) _) (Subalgebra.smul_mem _ (pbp_mem_NX _) _)
  · have hb' := crr_far j hPb hρ i hb
    cases i
    · exact sub_mem (H.Vno false b hb') (crr_rrD_noX _ _ _ _)
    · show o.V b - rrD P.a P'.a (pl2Beta o) b ∈ _
      rw [crr_rrD_zero _ _ (hβ b hb'), sub_zero]; exact H.Vno true b hb'
  · show ((o.K Y + ∑ b ∈ blocks j Y, rrDel R j st g μ D P.a P'.a (pl2Beta o) o b *
        KextO j (embF K + o.K) (Y \ blockSet j b) : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).ab = 0
    have hsum : ∑ b ∈ blocks j Y, rrDel R j st g μ D P.a P'.a (pl2Beta o) o b *
        KextO j (embF K + o.K) (Y \ blockSet j b) ∈ abZ .two (Lam 2 L N) := by
      rcases small_far (d := 2) hL hY hab with hfa | hfb
      · refine Submodule.sum_mem _ fun b hb => ?_
        rw [crr_corr_zero R j st g μ D K _ _ _ o (hβ b (farS_mono le_rfl hfa
          (blockSet_subset hY.1 hb)))]
        exact zero_mem _
      · refine Submodule.sum_mem _ fun b hb => abZ_of_noX (i := false) ?_
        have hbY := blockSet_subset hY.1 hb
        exact crr_corr_noX R j st g μ D K _ _ _ o false hY.1 (crr_rrD_noX _ _ _ _)
          (H.Vno false b (farS_mono le_rfl hfb hbY)) (H.Wno false b (farS_mono le_rfl hfb hbY))
          fun Z hZ hZY => H.Kno false Z hZ (farS_mono le_rfl hfb hZY)
    have := add_mem (show o.K Y ∈ abZ .two (Lam 2 L N) from H.Kab Y hY) hsum
    exact this
  · have hf' := crr_far j hPb hρ i hfar
    refine add_mem (H.Kno i Y hY hf') (Subalgebra.sum_mem _ fun b hb => ?_)
    have hbY := blockSet_subset hY.1 hb
    cases i
    · exact crr_corr_noX R j st g μ D K _ _ _ o false hY.1 (crr_rrD_noX _ _ _ _)
        (H.Vno false b (farS_mono le_rfl hf' hbY)) (H.Wno false b (farS_mono le_rfl hf' hbY))
        fun Z hZ hZY => H.Kno false Z hZ (farS_mono le_rfl hf' hZY)
    · rw [crr_corr_zero R j st g μ D K _ _ _ o (hβ b (farS_mono le_rfl hf' hbY))]
      exact zero_mem _

theorem crr_diffO_noX {i : Bool} {F G : OE .two (Lam 2 L N)} (hF : F ∈ noX .two (Lam 2 L N) i)
    (hG : G ∈ noX .two (Lam 2 L N) i) : plDiffO F G ∈ noX .two (Lam 2 L N) i := by
  obtain ⟨f1, f2⟩ := mem_noX.1 hF
  obtain ⟨g1, g2⟩ := mem_noX.1 hG
  refine mem_noX.2 ⟨?_, ?_⟩
  · cases i
    · exact g1
    · show (F : SA .two (Lam 2 L N)).a - (G : SA .two (Lam 2 L N)).a = 0
      have f1' : (F : SA .two (Lam 2 L N)).a = 0 := f1
      have g1' : (G : SA .two (Lam 2 L N)).a = 0 := g1
      rw [f1', g1', sub_zero]
  · show (F : SA .two (Lam 2 L N)).ab - (G : SA .two (Lam 2 L N)).ab = 0
    rw [f2, g2, sub_zero]

/-- **The relaxed invariant is closed under `plDiffSt`.** -/
theorem crr_diff_coalInvR {P : ObsPts 2 L N} {j ρ : ℕ} {o₁ o₂ : ObsSt .two L N}
    (h₁ : ObsCoalInvR P j ρ o₁) (h₂ : ObsCoalInvR P j ρ o₂) :
    ObsCoalInvR P j ρ (plDiffSt o₁ o₂) where
  Vab b := by
    show (o₁.V b : SA .two (Lam 2 L N)).ab - (o₂.V b : SA .two (Lam 2 L N)).ab = 0
    rw [h₁.Vab b, h₂.Vab b, sub_zero]
  Vpt i b := by
    cases i
    · exact h₂.Vpt false b
    · show (o₁.V b : SA .two (Lam 2 L N)).a - (o₂.V b : SA .two (Lam 2 L N)).a ∈ _
      exact sub_mem (h₁.Vpt true b) (h₂.Vpt true b)
  Vno i b h := crr_diffO_noX (h₁.Vno i b h) (h₂.Vno i b h)
  Wab b := by
    show (o₁.W b : SA .two (Lam 2 L N)).ab - (o₂.W b : SA .two (Lam 2 L N)).ab = 0
    rw [h₁.Wab b, h₂.Wab b, sub_zero]
  Wno i b h := crr_diffO_noX (h₁.Wno i b h) (h₂.Wno i b h)
  Kab X hX := by
    show (o₁.K X : SA .two (Lam 2 L N)).ab - (o₂.K X : SA .two (Lam 2 L N)).ab = 0
    rw [h₁.Kab X hX, h₂.Kab X hX, sub_zero]
  Kno i X hX h := crr_diffO_noX (h₁.Kno i X hX h) (h₂.Kno i X hX h)
  uab := by
    show (o₁.u : SA .two (Lam 2 L N)).ab - (o₂.u : SA .two (Lam 2 L N)).ab = 0
    rw [h₁.uab, h₂.uab, sub_zero]

end Init

end

end PtCorr2
