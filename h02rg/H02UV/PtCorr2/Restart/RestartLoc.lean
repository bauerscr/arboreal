import PtCorr2.Obs.ObsLoc
import Obs2.Loc.Reloc

/-!
# Restart, the support lemma: relocation of the Loc point inside a block (B3, T4 input)

The supports `X^□` are polymers (`isPolymer_nbhd`), so membership of a point in `X^□` depends
only on its block. Hence for `a, a'` in the same `j`-block (and the same `b`):

* `rs_osub_le`: `𝒩^{obs}_P(S) ≤ 𝒩^{obs}_{P'}(S)` for every `j`-polymer `S`;
* `rs_OLocS_reloc`: `OLocS P j V W K → OLocS P' j V W K`, hence `OLocHyp P' j V W K`;
* **`rs_K_a_zero_of_block`** (the support lemma): along the one-point history
  (`ObsLocInv`), the `σ_a` and `σ_aσ_b` parts of `K^a_j(Y)` (`Y` connected) vanish unless
  `Y^□` contains the whole `j`-block of `a`;
* `rs_blk_mono`: blocks nest (`blk m x = blk m y → blk k x = blk k y` for `k ≥ m`);
* **`rs_oLocHyp_hist`**: along every trajectory (hypotheses of `oLocH_traj`), for `m ≤ j ≤ N_h`,
  if `a, a'` lie in one `m`-block, then the full inputs of step `j` of the `P`-history satisfy
  `OLocHyp P' j` (the locality hypothesis at the relocated point);
* **`rs_reloc_hist`**: hence (`reloc_exact`) one step of the `P`-history computed with the
  Loc point `a'` equals the step with Loc point `a`.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD Obs2 Flow2 Flow2.Hist

variable {L N : ℕ} [NeZero L] {c : Obs.Case}

/-- Blocks nest. -/
theorem rs_blk_mono {d : ℕ} {x y : Lam d L N} {m : ℕ} (h : blk m x = blk m y) :
    ∀ k, m ≤ k → blk k x = blk k y := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact h
  | succ k _ ih => rw [blk_succ, blk_succ, ih]

theorem rs_mem_nbhd_iff {d j : ℕ} {X : Finset (Lam d L N)} {x y : Lam d L N}
    (h : blk j x = blk j y) : x ∈ nbhd j X ↔ y ∈ nbhd j X :=
  ⟨isPolymer_nbhd j X x y h, isPolymer_nbhd j X y x h.symm⟩

/-- `𝒩^{obs}` on a polymer only sees the block of the observable point. -/
theorem rs_osub_le {d j : ℕ} {P P' : ObsPts d L N} {S : Finset (Lam d L N)}
    (hS : IsPolymer j S) (ha : blk j P.a = blk j P'.a) (hb : P.b = P'.b) :
    (osub P S : Subalgebra ℂ (OE c (Lam d L N))) ≤ osub P' S :=
  compSub_mono le_rfl (fun h => hS _ _ ha h) (fun h => hb ▸ h)

theorem ObsLocInv.rs_reloc {P P' : ObsPts 2 L N} {j : ℕ} {o : ObsSt c L N}
    (H : ObsLocInv P j o) (ha : blk j P.a = blk j P'.a) (hb : P.b = P'.b) :
    ObsLocInv P' j o where
  V b := rs_osub_le (isPolymer_nbhd j _) ha hb (H.V b)
  W b := rs_osub_le (isPolymer_nbhd j _) ha hb (H.W b)
  K Y hY := rs_osub_le (isPolymer_nbhd j _) ha hb (H.K Y hY)

/-- **The support lemma.** The `σ_a` and `σ_aσ_b` parts of `K_j(Y)` (connected `Y`) vanish
unless `Y^□` contains the whole `j`-block of `a`. -/
theorem rs_K_a_zero_of_block {P : ObsPts 2 L N} {j : ℕ} {o : ObsSt c L N}
    (H : ObsLocInv P j o) {Y : Finset (Lam 2 L N)} (hY : IsConn j Y)
    (hB : ¬ blockSet (L := L) (N := N) j (blk j P.a) ⊆ nbhd j Y) :
    ((o.K Y : OE c (Lam 2 L N)) : SA c (Lam 2 L N)).a = 0 ∧
      ((o.K Y : OE c (Lam 2 L N)) : SA c (Lam 2 L N)).ab = 0 := by
  have ha : P.a ∉ nbhd j Y := by
    intro h
    refine hB fun x hx => ?_
    have hx' : blk j x = blk j P.a := (mem_filter.1 hx).2
    exact isPolymer_nbhd j Y P.a x hx'.symm h
  exact (H.K Y hY).2.2.2.2.1 ha

section Hist

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P P' : ObsPts 2 L N)
  (o₀ : ObsSt c L N)

/-- The locality invariant along the history, at the relocated point (`j ≥ m`). -/
theorem rs_obsLocInv_hist {Nh : ℕ} (hV : ∀ j < Nh, ValidAt R j) (hVL : ValidAtL R Nh)
    (h0 : ObsLocInv P 0 o₀) (t : Hist.Seq (Xs R)) {m : ℕ} (ha : blk m P.a = blk m P'.a)
    (hb : P.b = P'.b) {j : ℕ} (hmj : m ≤ j) (hj : j ≤ Nh) :
    ObsLocInv P' j (obsHist R P o₀ j t) := by
  have hcore : ∀ j ≤ Nh, ValidCore R j := fun j hj => by
    rcases Nat.lt_or_ge j Nh with h | h
    · exact (hV j h).toValidCore
    · rw [show j = Nh by omega]; exact hVL.2
  have hRI := rawInv_histU R hV hVL t
  exact (obsLocInv_hist R P o₀ h0 t j fun i hi => ⟨hcore i (by omega), hRI i (by omega)⟩).rs_reloc
    (rs_blk_mono ha j hmj) hb

/-- **The locality hypothesis at the relocated point** along every trajectory, `m ≤ j ≤ N_h`. -/
theorem rs_oLocHyp_hist {Nh : ℕ} (hV : ∀ j < Nh, ValidAt R j) (hVL : ValidAtL R Nh)
    (h0 : ObsLocInv P 0 o₀) (t : Hist.Seq (Xs R)) {m : ℕ} (ha : blk m P.a = blk m P'.a)
    (hb : P.b = P'.b) {j : ℕ} (hmj : m ≤ j) (hj : j ≤ Nh) :
    OLocHyp P' j (fullV R j (rawHist R j t) (t j).1 (t j).2.1 (obsHist R P o₀ j t))
      (fullW (rawHist R j t) (rawD R (rawHist R j t).u (t j).2.2) (obsHist R P o₀ j t))
      (fullK R j (rawHist R j t) (rawK R (rawHist R j t).u (t j).2.2) (obsHist R P o₀ j t)) := by
  have hcore : ValidCore R j := by
    rcases Nat.lt_or_ge j Nh with h | h
    · exact (hV j h).toValidCore
    · rw [show j = Nh by omega]; exact hVL.2
  have hRI := rawInv_histU R hV hVL t j (by omega)
  exact (olocS_full R P' _ _ hcore hRI (rawD_mem R _ _) (rawK_mem R _ _)
    (rs_obsLocInv_hist R P P' o₀ hV hVL h0 t ha hb hmj hj)).toOLocHyp

/-- **Relocation of one step along the history** (`m ≤ j ≤ N_h`, `a, a'` in one `m`-block):
step `j` computed with the Loc point `a'` equals the step with Loc point `a`. -/
theorem rs_reloc_hist {Nh : ℕ} (hV : ∀ j < Nh, ValidAt R j) (hVL : ValidAtL R Nh)
    (h0 : ObsLocInv P 0 o₀) (t : Hist.Seq (Xs R)) {m : ℕ} (ha : blk m P.a = blk m P'.a)
    (hb : P.b = P'.b) {j : ℕ} (hmj : m ≤ j) (hj : j ≤ Nh) (hjN : j + 1 < N)
    (hL : 2 ^ (2 + 3) ≤ L) {C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ} (hC : CovRange j C) :
    let V := fullV R j (rawHist R j t) (t j).1 (t j).2.1 (obsHist R P o₀ j t)
    let W := fullW (rawHist R j t) (rawD R (rawHist R j t).u (t j).2.2) (obsHist R P o₀ j t)
    let K := fullK R j (rawHist R j t) (rawK R (rawHist R j t).u (t j).2.2) (obsHist R P o₀ j t)
    expU (-uXB P j C V W K univ) (-uXO P j C V W K univ) *
        gZO (j + 1) (ItO P j C V W K) (KplusO P j C V W K) =
      expU (-uXB P' j C V W K univ) (-uXO P' j C V W K univ) *
        gZO (j + 1) (ItO P' j C V W K) (KplusO P' j C V W K) := by
  intro V W K
  have hcore : ValidCore R j := by
    rcases Nat.lt_or_ge j Nh with h | h
    · exact (hV j h).toValidCore
    · rw [show j = Nh by omega]; exact hVL.2
  have hRI := rawInv_histU R hV hVL t j (by omega)
  have hF : OLocS P j V W K := olocS_full R P _ _ hcore hRI (rawD_mem R _ _) (rawK_mem R _ _)
    (obsLocInv_hist R P o₀ h0 t j fun i hi => ⟨by
      rcases Nat.lt_or_ge i Nh with h | h
      · exact (hV i h).toValidCore
      · rw [show i = Nh by omega]; exact hVL.2, rawInv_histU R hV hVL t i (by omega)⟩)
  exact reloc_exact (by norm_num) hL hjN hC P P' hF.toOLocHyp
    (rs_oLocHyp_hist R P P' o₀ hV hVL h0 t ha hb hmj hj)

end Hist

end

end PtCorr2
