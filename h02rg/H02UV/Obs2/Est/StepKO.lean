import Obs2.Est.Step3OL
import Obs2.Est.ReblockO

/-!
# Theorem `stepK` with sources: the activity after the change of variables

**`stepKO_ts`** (the analogue of `Step2.stepK_ts` on `OE`, full norm with single-source weights,
`w_ab = 0`): for `‖V‖ ≤ ḡ`, `‖𝒲‖ ≤ ḡ²` (bulk and observable parts), activity size `k` (bulk and
weighted observable parts), `ḡ, k ≤ ε₀`, and every connected `(j+1)`-polymer `U`,

  `A^{(|𝓑_{j+1}(U)| - 2^d)_+} ‖K_{j+1}(U)‖_{T_{j+1}(ℓ')} ≤ C₀ (L^{d-3} + A^{-η}) k + C₁ (ḡ³ + ḡk + k²)`

for `K_{j+1} = KplusO` (the output `K_out` of the change of variables (D.13), `Obs2.Map.Map`).

Proof as `Step2.stepK_ts`: `K_{j+1}(U) = K^♯(U) + ∑_{Rset} R_g(U)` (`KoutO_split`, using
`∑_U J(B_+, U) = 0`, `JhO_sum_U`); `K^♯` is bounded by `step3OL` with the regulator `λA`,
`λ = 2^{2 + c_S}`; the correction by `KoutO_sub_le` in the full norm (`BHF.nS`), with
`‖Ĩ_{j+1}(B_+)‖ ≤ 2` (`ItO_full`) and `‖J̄‖ ≤ C_δ r²` (`JhO_full`), `r = max(ḡ, k)`.

Hypotheses beyond `step2O_tsL`: the strong locality `OLocS` (it replaces the componentwise
locality and the `a`/`b` support hypotheses, and gives the exact cancellation `JhO_sum_U`).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD PolyAux ENNReal

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

theorem cmpIn_of_osub {P : ObsPts d L N} {S : Finset (Lam d L N)} {F : OE c (Lam d L N)}
    (h : F ∈ osub P S) : CmpIn (S : Set (Lam d L N)) (F : SA c (Lam d L N)) :=
  ⟨h.1, h.2.1, h.2.2.1⟩

theorem osub_a_zero {P : ObsPts d L N} {S : Finset (Lam d L N)} {F : OE c (Lam d L N)}
    (h : F ∈ osub P S) (ha : P.a ∉ S) : (F : SA c (Lam d L N)).a = 0 :=
  (h.2.2.2.2.1 ha).1

theorem osub_b_zero {P : ObsPts d L N} {S : Finset (Lam d L N)} {F : OE c (Lam d L N)}
    (h : F ∈ osub P S) (hb : P.b ∉ S) : (F : SA c (Lam d L N)).b = 0 :=
  (h.2.2.2.2.2 hb).1

/-- The real inequality for the correction term of `stepKO_ts` (`r = max(ḡ, k)`). -/
theorem corr_real {g k X1 Cδ Λ2 C0' C₃ : ℝ} (hg0 : 0 ≤ g) (hk0 : 0 ≤ k) (hg1 : g ≤ 1)
    (hk1 : k ≤ 1) (hX1 : 0 ≤ X1) (hCδ : 0 ≤ Cδ) (hΛ2 : 0 ≤ Λ2) (hC0 : 0 ≤ C0') (hC3 : 0 ≤ C₃) :
    X1 * (Cδ * max g k ^ 2) * (X1 * (Cδ * max g k ^ 2) +
      (C0' * k + C₃ * (g ^ 3 + g * k + k ^ 2)) * Λ2) ≤
      (X1 ^ 2 * Cδ ^ 2 + X1 * Cδ * Λ2 * (C0' + C₃)) * (g ^ 3 + g * k + k ^ 2) := by
  set r := max g k with hr
  set y := g ^ 3 + g * k + k ^ 2 with hy
  have hr0 : 0 ≤ r := le_max_of_le_left hg0
  have hr1 : r ≤ 1 := max_le hg1 hk1
  have hg3 : 0 ≤ g ^ 3 := pow_nonneg hg0 3
  have hgk : 0 ≤ g * k := mul_nonneg hg0 hk0
  have hk2 : 0 ≤ k ^ 2 := sq_nonneg k
  have hy0 : 0 ≤ y := by rw [hy]; linarith only [hg3, hgk, hk2]
  have hr3 : r ^ 3 ≤ y := by
    rcases le_total g k with h | h
    · rw [hr, max_eq_right h]
      have : k ^ 3 ≤ k ^ 2 := pow_le_pow_of_le_one hk0 hk1 (by norm_num)
      rw [hy]; linarith only [this, hg3, hgk]
    · rw [hr, max_eq_left h, hy]; linarith only [hgk, hk2]
  have hr4 : r ^ 4 ≤ y := (pow_le_pow_of_le_one hr0 hr1 (by norm_num)).trans hr3
  have hrk : r * k ≤ y := by
    rcases le_total g k with h | h
    · rw [hr, max_eq_right h, hy, ← pow_two]; linarith only [hg3, hgk]
    · rw [hr, max_eq_left h, hy]; linarith only [hg3, hk2]
  have hr2 : r ^ 2 ≤ r := by
    rw [pow_two]; exact mul_le_of_le_one_left hr0 hr1
  have hr21 : r ^ 2 ≤ 1 := hr2.trans hr1
  have h1 : r ^ 2 * k ≤ y := (mul_le_mul_of_nonneg_right hr2 hk0).trans hrk
  have h2 : r ^ 2 * y ≤ y := mul_le_of_le_one_left hy0 hr21
  have hμ : r ^ 2 * (C0' * k + C₃ * y) ≤ (C0' + C₃) * y := by
    have e1 : r ^ 2 * (C0' * k + C₃ * y) = C0' * (r ^ 2 * k) + C₃ * (r ^ 2 * y) := by ring
    have e2 : (C0' + C₃) * y = C0' * y + C₃ * y := by ring
    rw [e1, e2]
    exact add_le_add (mul_le_mul_of_nonneg_left h1 hC0) (mul_le_mul_of_nonneg_left h2 hC3)
  have e : X1 * (Cδ * r ^ 2) * (X1 * (Cδ * r ^ 2) + (C0' * k + C₃ * y) * Λ2) =
      X1 ^ 2 * Cδ ^ 2 * r ^ 4 + X1 * Cδ * Λ2 * (r ^ 2 * (C0' * k + C₃ * y)) := by ring
  have e' : (X1 ^ 2 * Cδ ^ 2 + X1 * Cδ * Λ2 * (C0' + C₃)) * y =
      X1 ^ 2 * Cδ ^ 2 * y + X1 * Cδ * Λ2 * ((C0' + C₃) * y) := by ring
  rw [e, e']
  exact add_le_add (mul_le_mul_of_nonneg_left hr4 (by positivity))
    (mul_le_mul_of_nonneg_left hμ (by positivity))

set_option maxHeartbeats 2000000 in
/-- **Theorem `stepK` with sources**: the third-order estimate for `K_{j+1}` after the change of
variables, in the full norm. -/
theorem stepKO_ts (d : ℕ) (hd : 2 ≤ d) : ∃ (C₀ η : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧ 0 < η ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓC C →
    ∀ (c : Obs.Case) (P : ObsPts d L N) (w : Wt), w.ab = 0 → w.a ≠ ⊤ → w.b ≠ ⊤ →
    ∀ (V W : OFam c d L N) (K : OAct c d L N),
      InF j (bulkF V) → InF j (bulkF W) →
      (∀ b, ε ((bulkF V b : EvR (Lam d L N)) : Alg d L N) = 0) → InK2 j (bulkF K) →
      OLocS P j V W K →
      (∀ X, IsConn j X → IsSymS (K X : SA c (Lam d L N))) →
      ∀ g : ℝ, 0 ≤ g → g ≤ ε₀ →
      Fnorm j ℓ (bulkF V) ≤ ENNReal.ofReal g → Fnorm j ℓ (bulkF W) ≤ ENNReal.ofReal (g ^ 2) →
      (∀ b ∈ blockIdx (L := L) (N := N) j, oTo w j ℓ (V b) ≤ ENNReal.ofReal g) →
      (∀ b ∈ blockIdx (L := L) (N := N) j, oTo w j ℓ (W b) ≤ ENNReal.ofReal (g ^ 2)) →
      ∀ k : ℝ, 0 ≤ k → k ≤ ε₀ →
      Knorm j ℓ A (bulkF K) ≤ ENNReal.ofReal k →
      (∀ X, IsConn j X →
        ENNReal.ofReal (A ^ (nb j X - 2 ^ d)) * oTo w j ℓ (K X) ≤ ENNReal.ofReal k) →
      ∀ U : Finset (Lam d L N), IsConn (j + 1) U →
        ENNReal.ofReal (A ^ (nb (j + 1) U - 2 ^ d)) *
          oTj d L w (j + 1) ℓ' (KplusO P j C V W K U : SA c (Lam d L N)) ≤
          ENNReal.ofReal (C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3 + A ^ (-η)) * k) +
          ENNReal.ofReal (C₁ * (g ^ 3 + g * k + k ^ 2)) := by
  classical
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Cl, hCl0, hloc⟩ := exists_Loc2sXY_bound d hd1
  obtain ⟨Clo, hClo0, hlocO⟩ := exists_LocO2_obs_bound d
  obtain ⟨cN, hcN⟩ := card_small_containing d
  set lam : ℝ := 2 * (2 : ℝ) ^ (1 + cN) with hlamdef
  have hlam1 : 1 ≤ lam := by
    have : (1 : ℝ) ≤ 2 ^ (1 + cN) := one_le_pow₀ (by norm_num)
    rw [hlamdef]; linarith
  obtain ⟨C₀, η, L₃, hC₀, hη, h3⟩ := step3OL d hd
  refine ⟨C₀, η, max L₃ (max (2 ^ (d + 3) + 8 * d + 1) ⌈pauliL0 d⌉₊), hC₀, hη, ?_⟩
  intro L _ hL
  have hL3 : L₃ ≤ L := le_trans (le_max_left _ _) hL
  have hL8 : 2 ^ (d + 3) + 8 * d < L :=
    lt_of_lt_of_le (Nat.lt_succ_self _) (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL)
  have hLp : pauliL0 d ≤ L := (Nat.le_ceil _).trans
    (by exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL)
  have hL2 : 2 ^ (d + 2) ≤ L := by
    have : 2 ^ (d + 2) ≤ 2 ^ (d + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  obtain ⟨A₀, hA₀, h3'⟩ := h3 L hL3 lam hlam1
  refine ⟨A₀, hA₀, fun A hA => ?_⟩
  have hA1 : 1 ≤ A := hA₀.trans hA
  have hA0 : 0 < A := by linarith
  obtain ⟨ε₃, C₃, hε₃, hC₃, h3''⟩ := h3' A hA
  set cS : ℝ := cN + 1 with hcSdef
  have hcS1 : 1 ≤ cS := by rw [hcSdef]; linarith [Nat.cast_nonneg (α := ℝ) cN]
  have hQ := one_le_Q1 hd1
  have hn : 0 ≤ cNear d L := Nat.cast_nonneg _
  have hcu : 0 ≤ cUblk d L Cl cS := by
    have := Nat.cast_nonneg (α := ℝ) ((L + 2 ^ (d + 3) + 7) ^ d)
    simp only [cUblk, cSblk, cNear]; positivity
  have hcw : 0 ≤ cWblk d L Cl := by
    have := Nat.cast_nonneg (α := ℝ) ((L + 2 ^ (d + 3) + 7) ^ d)
    simp only [cWblk, cSblk, cNear]; positivity
  have hcSo0 : 0 ≤ cSo d L := by
    have := mul_nonneg (mul_nonneg zero_le_two hn) (sq_nonneg (Q1 d))
    unfold cSo; linarith
  have hcuo : 0 ≤ cUo d L Clo cS := by
    have h1 : 0 ≤ Q1 d * pq d ^ 2 * (cS * Clo) := by
      have := one_le_pq hd1; positivity
    have h2 : 0 ≤ Clo * ((L : ℝ) ^ d * cSo d L) := by positivity
    unfold cUo; linarith
  have hcwo : 0 ≤ cWo d L Clo := by
    have h2 : 0 ≤ Clo * ((L : ℝ) ^ d * cSo d L) := by positivity
    unfold cWo; linarith
  set cG : ℝ := 2 * cUblk d L Cl cS + 2 * cUo d L Clo cS + cWblk d L Cl + cWo d L Clo with hcG
  have hcG0 : 0 ≤ cG := by positivity
  set n₀ : ℝ := (L : ℝ) ^ d with hn₀
  have hn₀0 : 0 ≤ n₀ := by positivity
  set cB : ℕ := (2 ^ (d + 1) + 3) ^ d
  set a : ℝ := 2 * (2 : ℝ) ^ (1 + cN) * A with ha
  have ha0 : 0 ≤ a := by positivity
  set X1 : ℝ := a ^ cB with hX1
  have hX10 : 0 ≤ X1 := by positivity
  set Cδ : ℝ := (2 : ℝ) ^ (2 ^ d) * (2 : ℝ) ^ (L ^ d * 2 ^ d) * ((cNear d L + 2) * (6 * Q1 d ^ 2))
    with hCδ
  have hCδ0 : 0 ≤ Cδ := by positivity
  set C0' : ℝ := C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3 + A ^ (-η)) with hC0'
  have hC0'0 : 0 ≤ C0' := by positivity
  set Λ2 : ℝ := (lam * A) ^ 2 ^ d with hΛ2
  have hΛ20 : 0 ≤ Λ2 := by positivity
  set Cμ : ℝ := C0' + 3 * C₃ with hCμ
  have hCμ0 : 0 ≤ Cμ := by positivity
  set Cx : ℝ := X1 ^ 2 * Cδ ^ 2 + X1 * Cδ * Λ2 * (C0' + C₃) with hCx
  have hCx0 : 0 ≤ Cx := by positivity
  set ε₀ : ℝ := min ε₃ (min 1 (min (1 / (2 * n₀ * cG + 1))
    (min (1 / (X1 * Cδ + 1)) (1 / (Cμ * Λ2 + 1))))) with hε₀
  have hε₀0 : 0 < ε₀ := lt_min hε₃ (lt_min one_pos (lt_min (by positivity)
    (lt_min (by positivity) (by positivity))))
  refine ⟨ε₀, C₃ + Cx, hε₀0, by positivity, ?_⟩
  intro N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC c P w hw0 hwa hwb V W K hV hW hV0 hK HL hsym
    g hg0 hgε hVg hWg hVo hWo k hk0 hkε hKk hKo U hU
  have e1 : ε₀ ≤ ε₃ := min_le_left _ _
  have e2 : ε₀ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have e5 : ε₀ ≤ 1 / (2 * n₀ * cG + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have e6 : ε₀ ≤ 1 / (X1 * Cδ + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have e7 : ε₀ ≤ 1 / (Cμ * Λ2 + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_right _ _)))
  -- locality
  have hlocV : ∀ b, CmpIn (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N))
      (V b : SA c (Lam d L N)) := fun b => cmpIn_of_osub (HL.hV b)
  have hlocW : ∀ b, CmpIn (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N))
      (W b : SA c (Lam d L N)) := fun b => cmpIn_of_osub (HL.hW b)
  have hlocK : ∀ X, IsConn j X → CmpIn (nbhd j X : Set (Lam d L N)) (K X : SA c (Lam d L N)) :=
    fun X hX => cmpIn_of_osub (HL.hK X hX)
  have hza : ∀ X, IsConn j X → P.a ∉ nbhd j X → (K X : SA c (Lam d L N)).a = 0 :=
    fun X hX ha => osub_a_zero (HL.hK X hX) ha
  have hzb : ∀ X, IsConn j X → P.b ∉ nbhd j X → (K X : SA c (Lam d L N)).b = 0 :=
    fun X hX hb => osub_b_zero (HL.hK X hX) hb
  -- the radius
  set r := max g k with hrdef
  have hr0 : 0 ≤ r := le_max_of_le_left hg0
  have hrε : r ≤ ε₀ := max_le hgε hkε
  have hr1 : r ≤ 1 := hrε.trans e2
  have hg1 : g ≤ 1 := hgε.trans e2
  have hk1 : k ≤ 1 := hkε.trans e2
  have hgr : g ≤ r := le_max_left _ _
  have hkr : k ≤ r := le_max_right _ _
  have hg2r : g ^ 2 ≤ r := (pow_le_of_le_one hg0 hg1 two_ne_zero).trans hgr
  have hw : w.Sub := by unfold Wt.Sub; rw [hw0]; exact zero_le
  have hVr' : ∀ b ∈ blockIdx (L := L) (N := N) j,
      Tj d (L : ℝ) j ℓ ((bulkF V b : EvR (Lam d L N)) : Alg d L N) ≤ ENNReal.ofReal r :=
    fun b hb => ((le_iSup₂ (f := fun b (_ : b ∈ blockIdx (L := L) (N := N) j) =>
      Tj d (L : ℝ) j ℓ ((bulkF V b : EvR (Lam d L N)) : Alg d L N)) b hb).trans hVg).trans
        (ENNReal.ofReal_le_ofReal hgr)
  have hWr' : ∀ b ∈ blockIdx (L := L) (N := N) j,
      Tj d (L : ℝ) j ℓ ((bulkF W b : EvR (Lam d L N)) : Alg d L N) ≤ ENNReal.ofReal r :=
    fun b hb => ((le_iSup₂ (f := fun b (_ : b ∈ blockIdx (L := L) (N := N) j) =>
      Tj d (L : ℝ) j ℓ ((bulkF W b : EvR (Lam d L N)) : Alg d L N)) b hb).trans hWg).trans
        (ENNReal.ofReal_le_ofReal hg2r)
  have hcount : ∀ b ∈ blockIdx (d := d) (L := L) (N := N) j,
      (((smallSets (d := d) (L := L) (N := N) j).filter
        (fun X => blockSet j b ⊆ X)).card : ℝ) ≤ cS := fun b hb => by
    have h1 : ((smallSets (d := d) (L := L) (N := N) j).filter
        (fun X => blockSet j b ⊆ X)).card ≤ cN := by convert hcN L N j b hb
    have h2 := Nat.cast_le (α := ℝ) |>.2 h1
    linarith
  have HB : Step2.BH j ℓ ℓ' ℓC C (bulkF V) (bulkF W) (bulkF K) A r Cl cS :=
    { hd := hd1, hLp := hLp, hL8 := hL8, hjN := hjN, hℓ := hℓ, hℓ' := hℓ', hℓC := hℓC,
      hsum := hsum, hC := hC, hV := hV, hW := hW, hV0 := hV0, hK := hK, hA := hA1, hr := hr0,
      hr1 := hr1, hVr := hVr', hWr := hWr', hKr := hKk.trans (ENNReal.ofReal_le_ofReal hkr),
      hCl := hCl0
      hloc := fun k hk ℓ₀ hℓ₀ X Y hX hYX F hF => hloc L hL8 N k hk X Y hX hYX F hF ℓ₀ hℓ₀
      hcS := hcS1, hcount := hcount }
  have hKk' : ∀ X, IsSmall j X → oTo w j ℓ (K X) ≤ ENNReal.ofReal r := fun X hX => by
    have h := hKo X ⟨hX.1, hX.2.1⟩
    rw [show nb j X - 2 ^ d = 0 from Nat.sub_eq_zero_of_le hX.2.2, pow_zero,
      ENNReal.ofReal_one, one_mul] at h
    exact h.trans (ENNReal.ofReal_le_ofReal hkr)
  have HO : BHO P j ℓ ℓ' ℓC C V W K w r r r r Clo cS :=
    { hd := hd1, hLp := hLp, hL8 := hL8, hjN := hjN, hℓ := hℓ, hℓ' := hℓ', hℓC := hℓC,
      hsum := hsum, hC := hC, hw := hw, hw0 := hw0, hVl := hlocV, hWl := hlocW
      hKl := fun X hX => hlocK X ⟨hX.1, hX.2.1⟩
      hr := hr0, hmV := hr0, hmW := hr0, hk := hr0, hVr := hVr'
      hVm := fun b hb => (hVo b hb).trans (ENNReal.ofReal_le_ofReal hgr)
      hWm := fun b hb => (hWo b hb).trans (ENNReal.ofReal_le_ofReal hg2r)
      hKk := hKk', hCl := hClo0
      hloc := fun k' hk ℓ₀ hℓ₀ X Y hX hYX F hF =>
        hlocO L hL8 N c P w hw0 k' hk ℓ₀ hℓ₀ X Y hX hYX F hF
      hlocl := bho_hlocl hd1 P j, hcS := hcS1, hcount := hcount }
  have H : BHF P j ℓ ℓ' ℓC C V W K w A r Cl cS Clo :=
    ⟨HB, HO, hlocK, fun X hX => (hKo X hX).trans (ENNReal.ofReal_le_ofReal hkr)⟩
  -- `‖Ĩ_{j+1}(B_+)‖ ≤ 2`
  have hIt : ∀ c' : Fin d → ℕ, H.nS.nrm (ItO P j C V W K c') ≤ ENNReal.ofReal 2 := by
    intro c'
    refine (H.ItO_full c').trans (ENNReal.ofReal_le_ofReal ?_)
    have htG := H.tG_le
    have htG0 := H.htG
    have hx : (L : ℝ) ^ d * BHF.tG d L r Cl Clo cS ≤ 1 / 2 := by
      have h1 : 2 * n₀ * cG * r ≤ 1 :=
        le_one_of_le_div (by positivity) (by positivity) (hrε.trans e5) (by linarith)
      have h2 : (L : ℝ) ^ d * BHF.tG d L r Cl Clo cS ≤ n₀ * (cG * r) :=
        mul_le_mul_of_nonneg_left htG hn₀0
      have e : n₀ * (cG * r) = (2 * n₀ * cG * r) / 2 := by ring
      linarith only [h1, h2, e]
    have he : Real.exp (1 / 2) ≤ 2 := by
      have := (abs_le.1 (Real.abs_exp_sub_one_le (x := 1 / 2) (by norm_num))).2
      norm_num at this ⊢; linarith
    exact (Real.exp_le_exp.2 hx).trans he
  -- the second-order data
  set δ : ℝ := Cδ * r ^ 2 with hδdef
  have hδ0 : 0 ≤ δ := by positivity
  have hJb : ∀ p ∈ pairsU (L := L) (N := N) (j + 1),
      H.nS.nrm (JbarO (j + 1) (ItO P j C V W K) (JhO j C V) p.1 p.2) ≤ ENNReal.ofReal δ := by
    intro p hp
    obtain ⟨-, hs, -⟩ := mem_pairsU.1 hp
    have hb1 : H.nS.nrm (bpowO (j + 1) (ItO P j C V W K) p.2) ≤
        ENNReal.ofReal (2 ^ (2 ^ d)) := by
      have := H.nS.prodR (blocks (j + 1) p.2) (ItO P j C V W K)
        (fun _ => 2) (fun _ _ => by norm_num) (fun c' _ => hIt c')
      rw [prod_const] at this
      exact this.trans (ENNReal.ofReal_le_ofReal (pow_le_pow_right₀ (by norm_num) hs.2.2))
    have hnb : nb j p.2 ≤ L ^ d * 2 ^ d :=
      (nb_le_of_succ hs.1).trans (Nat.mul_le_mul_left _ hs.2.2)
    have hb2 := H.JhO_full p.1 hs.1
    have hb2' : H.nS.nrm (JhO j C V p.1 p.2) ≤
        ENNReal.ofReal ((2 : ℝ) ^ (L ^ d * 2 ^ d) * ((cNear d L + 2) * (6 * Q1 d ^ 2 * r ^ 2))) := by
      refine hb2.trans (ENNReal.ofReal_le_ofReal ?_)
      have e : BHF.qP d r = 6 * Q1 d ^ 2 * r ^ 2 := by unfold BHF.qP; ring
      rw [e]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hnb) (by positivity)
    refine (H.nS.mulR (by positivity) hb1 hb2').trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    rw [hδdef, hCδ]; ring
  -- the bound on `M = K^♯`
  set yy : ℝ := g ^ 3 + g * k + k ^ 2 with hyy
  have hyy0 : 0 ≤ yy := by positivity
  set μ' : ℝ := C0' * k + C₃ * yy with hμdef
  have hμ0 : 0 ≤ μ' := by positivity
  have hM : ∀ Y, IsConn (j + 1) Y → ENNReal.ofReal ((lam * A) ^ (nb (j + 1) Y - 2 ^ d)) *
      H.nS.nrm (KnewO P j C V W K Y) ≤ ENNReal.ofReal μ' := by
    intro Y hY
    have := h3'' N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC c P w hw0 hwa hwb V W K hV hW hV0 hK
      hlocV hlocW hlocK hsym hza hzb g hg0 (hgε.trans e1) hVg hWg hVo hWo k hk0 (hkε.trans e1)
      hKk hKo Y hY
    refine this.trans (le_of_eq ?_)
    rw [hμdef, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  -- smallness
  have hδ1 : (2 * (2 : ℝ) ^ (1 + cN) * A) ^ ((2 ^ (d + 1) + 3) ^ d) * δ ≤ 1 := by
    have h := le_one_of_le_div (x := X1 * Cδ) (by positivity) (by positivity) (hrε.trans e6)
      (by linarith)
    have hr2 : r ^ 2 ≤ r := by rw [pow_two]; exact mul_le_of_le_one_left hr0 hr1
    calc (2 * (2 : ℝ) ^ (1 + cN) * A) ^ ((2 ^ (d + 1) + 3) ^ d) * δ = X1 * Cδ * r ^ 2 := by
          rw [hX1, ha, hδdef]; ring
      _ ≤ X1 * Cδ * r := by gcongr
      _ ≤ 1 := h
  have hμ1 : μ' * (lam * A) ^ 2 ^ d ≤ 1 := by
    have h := le_one_of_le_div (x := Cμ * Λ2) (by positivity) (by positivity) (hrε.trans e7)
      (by linarith)
    have hμr : μ' ≤ Cμ * r := by
      have h2 : yy ≤ 3 * r := by
        have i1 : g ^ 3 ≤ r := (pow_le_of_le_one hg0 hg1 (by norm_num)).trans hgr
        have i2 : g * k ≤ r := (mul_le_of_le_one_left hk0 hg1).trans hkr
        have i3 : k ^ 2 ≤ r := (pow_le_of_le_one hk0 hk1 (by norm_num)).trans hkr
        rw [hyy]; linarith
      calc μ' = C0' * k + C₃ * yy := rfl
        _ ≤ C0' * r + C₃ * (3 * r) := by gcongr
        _ = Cμ * r := by rw [hCμ]; ring
    calc μ' * (lam * A) ^ 2 ^ d = μ' * Λ2 := rfl
      _ ≤ Cμ * r * Λ2 := by gcongr
      _ = Cμ * Λ2 * r := by ring
      _ ≤ 1 := h
  -- the decomposition
  have hCR : CovRange j C := fun x y h => hC.range hjN x y h
  have hJ0 : ∀ b ∈ blockIdx (L := L) (N := N) (j + 1),
      ∑ U ∈ (smallSets (d := d) (L := L) (N := N) (j + 1)).filter
        (fun U => blockSet (j + 1) b ⊆ U), JhO j C V b U = 0 :=
    fun b _ => JhO_sum_U HL hd1 hL2 hjN hCR b
  have hsplit : KplusO P j C V W K U = KnewO P j C V W K U +
      ∑ g ∈ Rset (j + 1) U, RtermO (j + 1) (ItO P j C V W K) (KnewO P j C V W K) (JhO j C V) U g :=
    KoutO_split hJ0 hU
  have hE := KoutO_sub_le H.nS (k := j + 1) (I := ItO P j C V W K) (M := KnewO P j C V W K)
    (J := JhO j C V) hjN.le hA1 hlam1 hδ0 hμ0
    (fun b hb => by convert hcN L N (j + 1) b hb) le_rfl (fun b _ => hIt b) hJb hM hδ1 hμ1 hU.1
  rw [← H.nS_nrm, hsplit]
  refine (mul_le_mul_left' (H.nS.add _ _) _).trans ?_
  rw [mul_add]
  have hmono : ENNReal.ofReal (A ^ (nb (j + 1) U - 2 ^ d)) * H.nS.nrm (KnewO P j C V W K U) ≤
      ENNReal.ofReal ((lam * A) ^ (nb (j + 1) U - 2 ^ d)) * H.nS.nrm (KnewO P j C V W K U) :=
    mul_le_mul_right' (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hA0.le
      (le_mul_of_one_le_left hA0.le hlam1) _)) _
  have hS3' := h3'' N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC c P w hw0 hwa hwb V W K hV hW hV0 hK
    hlocV hlocW hlocK hsym hza hzb g hg0 (hgε.trans e1) hVg hWg hVo hWo k hk0 (hkε.trans e1)
    hKk hKo U hU
  refine (add_le_add (hmono.trans hS3') hE).trans ?_
  -- the real inequality for the correction
  have hX1' : (2 * (2 : ℝ) ^ (1 + cN) * A) ^ ((2 ^ (d + 1) + 3) ^ d) = X1 := by rw [hX1, ha]
  rw [← hyy, hX1']
  have hcorr : X1 * δ * (X1 * δ + μ' * (lam * A) ^ 2 ^ d) ≤ Cx * yy :=
    corr_real hg0 hk0 hg1 hk1 hX10 hCδ0 hΛ20 hC0'0 hC₃
  rw [add_assoc]
  refine add_le_add le_rfl ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have e4 : (C₃ + Cx) * yy = C₃ * yy + Cx * yy := by ring
  rw [e4]; linarith

end

end Obs2
