import Obs2.Est.BlockO5

/-!
# The crude bound for the map with sources, output regulator `λA`

**`Knext2O_crudeL`**: `Obs2.Knext2O_crude_ts` with the output measured with the regulator `λA`
(`λ ≥ 1` fixed), as `Step2.Knext2_crudeL`: the generic crude bound `KHypG.KnextG_le` is applied
with the weight `Q_w = λ Q₁` (`A ≥ A₀(L, λ)`).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step FRD ENNReal

set_option maxHeartbeats 1000000 in
/-- **The crude bound with sources**, output regulator `λA`. -/
theorem Knext2O_crudeL (d : ℕ) (hd : 1 ≤ d) : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∀ lam : ℝ, 1 ≤ lam → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∃ r₀ : ℝ, 0 < r₀ ∧
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, Step2.GoodCov2 j ℓC C →
    ∀ (c : Obs.Case) (P : ObsPts d L N) (w : Wt), w.ab = 0 →
    ∀ (V W : OFam c d L N) (K : OAct c d L N),
      Step2.InF j (bulkF V) → Step2.InF j (bulkF W) →
      (∀ b, ε ((bulkF V b : EvR (Lam d L N)) : Alg d L N) = 0) → Step2.InK2 j (bulkF K) →
      Step2.Fnorm j ℓ (bulkF V) ≤ ENNReal.ofReal r₀ →
      Step2.Fnorm j ℓ (bulkF W) ≤ ENNReal.ofReal r₀ →
      Knorm j ℓ A (bulkF K) ≤ ENNReal.ofReal r₀ →
      (∀ b, CmpIn (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N))
        (V b : SA c (Lam d L N))) →
      (∀ b, CmpIn (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N))
        (W b : SA c (Lam d L N))) →
      (∀ X, IsConn j X → CmpIn (nbhd j X : Set (Lam d L N)) (K X : SA c (Lam d L N))) →
      (∀ b ∈ blockIdx (L := L) (N := N) j, oTo w j ℓ (V b) ≤ ENNReal.ofReal r₀) →
      (∀ b ∈ blockIdx (L := L) (N := N) j, oTo w j ℓ (W b) ≤ ENNReal.ofReal r₀) →
      (∀ X, IsConn j X →
        ENNReal.ofReal (A ^ (nb j X - 2 ^ d)) * oTo w j ℓ (K X) ≤ ENNReal.ofReal r₀) →
      ∀ U : Finset (Lam d L N), IsConn (j + 1) U →
        ENNReal.ofReal ((lam * A) ^ (nb (j + 1) U - 2 ^ d)) *
          oTj d L w (j + 1) ℓ' (Knext2O P j C V W K U : SA c (Lam d L N)) ≤ ENNReal.ofReal 1 := by
  classical
  obtain ⟨Cl, hCl0, hloc⟩ := exists_Loc2sXY_bound d hd
  obtain ⟨Clo, hClo0, hlocO⟩ := exists_LocO2_obs_bound d
  obtain ⟨c, hc⟩ := card_small_containing d
  obtain ⟨η, hη0, -, hcomb⟩ := comb2 d
  refine ⟨max (2 ^ (d + 3) + 8 * d + 1) ⌈pauliL0 d⌉₊, ?_⟩
  intro L _ hL lam hlam
  have hL8 : 2 ^ (d + 3) + 8 * d < L :=
    lt_of_lt_of_le (Nat.lt_succ_self _) (le_trans (le_max_left _ _) hL)
  have hLp : pauliL0 d ≤ L :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hL)
  have hd8 : 2 ^ (d + 3) = 2 ^ d * 8 := by ring
  have hd4 : 2 ^ (d + 2) = 2 ^ d * 4 := by ring
  have hL2 : 2 ^ (d + 2) ≤ L := by
    rw [hd8] at hL8; rw [hd4]; generalize 2 ^ d = t at hL8 ⊢; omega
  have hL1 : 2 ^ d + 1 ≤ L := by
    rw [hd8] at hL8; generalize 2 ^ d = t at hL8 ⊢; omega
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set Q := Step2.Q1 d with hQdef
  have hQ : 1 ≤ Q := Step2.one_le_Q1 hd
  have hQ0 : 0 < Q := by linarith
  set M : ℕ := 2 ^ ((1 + c) * L ^ d) with hMdef
  have hM1 : 1 ≤ M := Nat.one_le_two_pow
  have hM1' : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  set Qw : ℝ := lam * Q with hQw
  have hQw1 : 1 ≤ Qw := by rw [hQw]; nlinarith
  set P' : ℝ := Qw * (2 * M) with hPdef
  have hP1 : 1 ≤ P' := by rw [hPdef]; nlinarith
  have hη' : 0 < 2 * η / (1 + 2 * η) := by positivity
  set A₀ : ℝ := Q * max 1 ((4 * P') ^ ((1 + 2 * η) / (2 * η))) with hA₀
  have hA₀1 : 1 ≤ A₀ := by
    rw [hA₀]; nlinarith [le_max_left (1 : ℝ) ((4 * P') ^ ((1 + 2 * η) / (2 * η)))]
  refine ⟨A₀, hA₀1, ?_⟩
  intro A hA
  have hA1 : 1 ≤ A := hA₀1.trans hA
  have hA0 : 0 < A := by linarith
  have hAQ : Q ≤ A := by
    refine le_trans ?_ hA
    rw [hA₀]; exact le_mul_of_one_le_right hQ0.le (le_max_left _ _)
  set Ar : ℝ := A / Q with hArdef
  have hArQ : Ar * Qw = lam * A := by rw [hArdef, hQw]; field_simp
  have hAr : max 1 ((4 * P') ^ ((1 + 2 * η) / (2 * η))) ≤ Ar := by
    rw [hArdef, le_div_iff₀ hQ0, mul_comm]; exact hA
  have hAr1 : 1 ≤ Ar := (le_max_left _ _).trans hAr
  have hAP : 4 * P' ≤ Ar ^ (2 * η / (1 + 2 * η)) := by
    calc 4 * P' = ((4 * P') ^ ((1 + 2 * η) / (2 * η))) ^ (2 * η / (1 + 2 * η)) := by
          rw [← Real.rpow_mul (by positivity)]
          rw [show (1 + 2 * η) / (2 * η) * (2 * η / (1 + 2 * η)) = 1 by field_simp]
          rw [Real.rpow_one]
      _ ≤ Ar ^ (2 * η / (1 + 2 * η)) :=
          Real.rpow_le_rpow (by positivity) ((le_max_right _ _).trans hAr) hη'.le
  set cS : ℝ := c + 1 with hcSdef
  have hcS1 : 1 ≤ cS := by rw [hcSdef]; linarith [Nat.cast_nonneg (α := ℝ) c]
  have hpq := Step2.one_le_pq hd
  set cJ : ℝ := Q * Step2.pq d ^ 2 * (cS * (Cl + Clo)) with hcJdef
  have hcJ : 0 ≤ cJ := by positivity
  have hn : 0 ≤ Step2.cNear d L := Nat.cast_nonneg _
  have hcSo0 : 0 ≤ cSo d L := by
    have := mul_nonneg (mul_nonneg zero_le_two hn) (sq_nonneg Q)
    unfold cSo; linarith
  have hcu : 0 ≤ Step2.cUblk d L Cl cS := by
    have := Nat.cast_nonneg (α := ℝ) ((L + 2 ^ (d + 3) + 7) ^ d)
    simp only [Step2.cUblk, Step2.cSblk, Step2.cNear]; positivity
  have hcw : 0 ≤ Step2.cWblk d L Cl := by
    have := Nat.cast_nonneg (α := ℝ) ((L + 2 ^ (d + 3) + 7) ^ d)
    simp only [Step2.cWblk, Step2.cSblk, Step2.cNear]; positivity
  have hcuo : 0 ≤ cUo d L Clo cS := by
    have h1 : 0 ≤ Q * Step2.pq d ^ 2 * (cS * Clo) := by positivity
    have h2 : 0 ≤ Clo * ((L : ℝ) ^ d * cSo d L) := by positivity
    unfold cUo; linarith
  have hcwo : 0 ≤ cWo d L Clo := by
    have h2 : 0 ≤ Clo * ((L : ℝ) ^ d * cSo d L) := by positivity
    unfold cWo; linarith
  have hcT : 0 ≤ cTo d L Cl Clo cS := by unfold cTo; linarith
  set Bc : ℝ := (1 + 2 ^ d * cJ) * (2 * A ^ 2 ^ d) + (8 * Q + 2 * cTo d L Cl Clo cS) * Ar with hBc
  have hBc0 : 0 ≤ Bc := by positivity
  set D : ℝ := 4 + cTo d L Cl Clo cS + 2 * (Step2.cUblk d L Cl cS + cUo d L Clo cS + cTo d L Cl Clo cS) * (L : ℝ) ^ d + 2 * A ^ 2 ^ d +
    (8 * Q + 2 * cTo d L Cl Clo cS) * Ar + (Ar * P') ^ 2 ^ d * Bc with hD
  have hD0 : 0 < D := by positivity
  refine ⟨1 / D, one_div_pos.2 hD0, ?_⟩
  intro N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC cc P w hw0 V W K hV hW hV0 hK hVr hWr hKr
    hVl hWl hKl hVm hWm hKo U hU
  set r := 1 / D with hrdef
  have hr0 : 0 ≤ r := (one_div_pos.2 hD0).le
  have hrle : r ≤ 1 / D := le_rfl
  have item : ∀ x : ℝ, 0 ≤ x → x ≤ D → x * r ≤ 1 := fun x hx hxD =>
    Step2.le_one_of_le_div hx hD0 hrle hxD
  have t1 : 0 ≤ 2 * (Step2.cUblk d L Cl cS + cUo d L Clo cS + cTo d L Cl Clo cS) * (L : ℝ) ^ d := by positivity
  have t3 : 0 ≤ 2 * A ^ 2 ^ d := by positivity
  have t4 : 0 ≤ (8 * Q + 2 * cTo d L Cl Clo cS) * Ar := by positivity
  have t5 : 0 ≤ (Ar * P') ^ 2 ^ d * Bc := by positivity
  have hr4 : 4 * r ≤ 1 := item 4 (by norm_num) (by rw [hD]; linarith only [hcT, t1, t3, t4, t5])
  have hr1 : r ≤ 1 := by linarith only [hr4]
  have hT : cTo d L Cl Clo cS * r ≤ 1 := item _ hcT (by rw [hD]; linarith only [hcT, t1, t3, t4, t5])
  have hj : j < N := by omega
  have hw : w.Sub := by unfold Wt.Sub; rw [hw0]; exact zero_le
  have hVr' : ∀ b ∈ blockIdx (L := L) (N := N) j,
      Tj d (L : ℝ) j ℓ ((bulkF V b : EvR (Lam d L N)) : Alg d L N) ≤ ENNReal.ofReal r :=
    fun b hb => (le_iSup₂ (f := fun b (_ : b ∈ blockIdx (L := L) (N := N) j) =>
      Tj d (L : ℝ) j ℓ ((bulkF V b : EvR (Lam d L N)) : Alg d L N)) b hb).trans hVr
  have hWr' : ∀ b ∈ blockIdx (L := L) (N := N) j,
      Tj d (L : ℝ) j ℓ ((bulkF W b : EvR (Lam d L N)) : Alg d L N) ≤ ENNReal.ofReal r :=
    fun b hb => (le_iSup₂ (f := fun b (_ : b ∈ blockIdx (L := L) (N := N) j) =>
      Tj d (L : ℝ) j ℓ ((bulkF W b : EvR (Lam d L N)) : Alg d L N)) b hb).trans hWr
  have hcount : ∀ b ∈ blockIdx (d := d) (L := L) (N := N) j,
      (((smallSets (d := d) (L := L) (N := N) j).filter
        (fun X => blockSet j b ⊆ X)).card : ℝ) ≤ cS := fun b hb => by
    have h1 : ((smallSets (d := d) (L := L) (N := N) j).filter
        (fun X => blockSet j b ⊆ X)).card ≤ c := by convert hc L N j b hb
    have h2 := Nat.cast_le (α := ℝ) |>.2 h1
    linarith
  have HB : Step2.BH j ℓ ℓ' ℓC C (bulkF V) (bulkF W) (bulkF K) A r Cl cS :=
    { hd := hd, hLp := hLp, hL8 := hL8, hjN := hjN, hℓ := hℓ, hℓ' := hℓ', hℓC := hℓC,
      hsum := hsum, hC := hC, hV := hV, hW := hW, hV0 := hV0, hK := hK, hA := hA1, hr := hr0,
      hr1 := hr1, hVr := hVr', hWr := hWr', hKr := hKr, hCl := hCl0
      hloc := fun k hk ℓ₀ hℓ₀ X Y hX hYX F hF => hloc L hL8 N k hk X Y hX hYX F hF ℓ₀ hℓ₀
      hcS := hcS1, hcount := hcount }
  have hKk : ∀ X, IsSmall j X → oTo w j ℓ (K X) ≤ ENNReal.ofReal r := fun X hX => by
    have h := hKo X ⟨hX.1, hX.2.1⟩
    rwa [show nb j X - 2 ^ d = 0 from Nat.sub_eq_zero_of_le hX.2.2, pow_zero,
      ENNReal.ofReal_one, one_mul] at h
  have HO : BHO P j ℓ ℓ' ℓC C V W K w r r r r Clo cS :=
    { hd := hd, hLp := hLp, hL8 := hL8, hjN := hjN, hℓ := hℓ, hℓ' := hℓ', hℓC := hℓC,
      hsum := hsum, hC := hC, hw := hw, hw0 := hw0, hVl := hVl, hWl := hWl
      hKl := fun X hX => hKl X ⟨hX.1, hX.2.1⟩
      hr := hr0, hmV := hr0, hmW := hr0, hk := hr0, hVr := hVr', hVm := hVm, hWm := hWm
      hKk := hKk, hCl := hClo0
      hloc := fun k' hk ℓ₀ hℓ₀ X Y hX hYX F hF =>
        hlocO L hL8 N cc P w hw0 k' hk ℓ₀ hℓ₀ X Y hX hYX F hF
      hlocl := bho_hlocl hd P j, hcS := hcS1, hcount := hcount }
  have H : BHF P j ℓ ℓ' ℓC C V W K w A r Cl cS Clo := ⟨HB, HO, hKl, hKo⟩
  have hκ1 : 2 * r * A ^ 2 ^ d ≤ 1 := by
    have := item (2 * A ^ 2 ^ d) t3 (by rw [hD]; linarith only [hcT, t1, t3, t4, t5])
    linarith only [this, mul_comm r (2 * A ^ 2 ^ d)]
  have hδ1 : (8 * Q + 2 * cTo d L Cl Clo cS) * r * Ar ≤ 1 := by
    have := item ((8 * Q + 2 * cTo d L Cl Clo cS) * Ar) t4 (by rw [hD]; linarith only [hcT, t1, t3, t4, t5])
    have e : (8 * Q + 2 * cTo d L Cl Clo cS) * r * Ar = (8 * Q + 2 * cTo d L Cl Clo cS) * Ar * r := by ring
    linarith only [this, e]
  have hDβ : (Ar * P') ^ 2 ^ d * ((1 + 2 ^ d * cJ) * (2 * r * A ^ 2 ^ d) +
      (8 * Q + 2 * cTo d L Cl Clo cS) * r * Ar) ≤ 1 := by
    have e : (Ar * P') ^ 2 ^ d * ((1 + 2 ^ d * cJ) * (2 * r * A ^ 2 ^ d) +
        (8 * Q + 2 * cTo d L Cl Clo cS) * r * Ar) = ((Ar * P') ^ 2 ^ d * Bc) * r := by rw [hBc]; ring
    rw [e]; exact item _ t5 (by rw [hD]; linarith only [hcT, t1, t3, t4, t5])
  have hpr : (Step2.cUblk d L Cl cS + cUo d L Clo cS + cTo d L Cl Clo cS) * r * (L : ℝ) ^ d ≤ 1 / 2 := by
    have := item (2 * (Step2.cUblk d L Cl cS + cUo d L Clo cS + cTo d L Cl Clo cS) * (L : ℝ) ^ d) t1 (by rw [hD]; linarith only [hcT, t1, t3, t4, t5])
    linarith only [this]
  have G := H.khyp hAQ hr4 hT hκ1 hδ1
  have hUj : IsPolymer j U := IsPolymer.of_succ hU.1
  have key := G.KnextG_le
    (oSN (nrmP_tNorm (E := Dir d) (p := pPhi d) (X := Lam d L N) (ℓ := ℓ') H.hh' H.hO.hℓ') w
      H.hw) (H.hE hC) (U := U) hQw1 hη0.le
    (fun g _ => by
      refine (H.prefO_full U _).trans (ENNReal.ofReal_le_ofReal ?_)
      have hnb : (nb j U : ℝ) ≤ (L : ℝ) ^ d * nb (j + 1) U := by
        exact_mod_cast nb_le_of_succ hU.1
      have hsum' : Step2.cUblk d L Cl cS * r + (uoB d L r Clo cS) + (tIB d L r Cl Clo cS) ≤
          (Step2.cUblk d L Cl cS + cUo d L Clo cS + cTo d L Cl Clo cS) * r := by
        have h1 := H.uo_le; have h2 := H.tI_le
        rw [add_mul, add_mul]; exact add_le_add (add_le_add le_rfl h1) h2
      have hpos : 0 ≤ Step2.cUblk d L Cl cS * r + (uoB d L r Clo cS) + (tIB d L r Cl Clo cS) :=
        add_nonneg (add_nonneg (mul_nonneg hcu hr0) H.huo) H.htI
      exact exp_pref_le hsum' hpos hnb hpr)
    (by
      refine (card_Gset_le (fun b hb => hc L N j b hb) hUj).trans ?_
      rw [hMdef, ← pow_mul]
      exact Nat.pow_le_pow_right (by norm_num) (by
        rw [mul_assoc]; exact Nat.mul_le_mul_left _ (nb_le_of_succ hU.1)))
    (fun g hg => nU_bound (fun X hX => (hcomb L hL1 N j X hj hX).1)
      (fun b hb => (isSmall_clo_nbhd hd hL2 hj b hb).2.2) hη0.le hg)
    hPdef hM1 hAP hDβ
  have e : A / Step2.Q1 d * Qw = lam * A := hArQ
  have hlA : 1 ≤ lam * A := by nlinarith
  rw [Knext2O_eq_KnextG P j C V W K U]
  refine le_trans ?_ key
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  exact (pow_le_pow_right₀ hlA (Nat.sub_le _ _)).trans
    (le_of_eq (congrArg (fun x => x ^ nb (j + 1) U) e.symm))

end

end Obs2
