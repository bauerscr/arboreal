import Spin2.Cont.ContDiffD1
import Spin2.Pair.PairLin3
import Spin2.H0.MasterH0Multi

/-!
# B3, T6: the difference datum `pl2Delta` in the `cd3` form; the grid artefact along `D_ε`

* **`cdd_art_rel`** (pure in the `HLam` inputs): if `λ̂^P`, `λ̂^{P'}` satisfy (H_λ) with the same
  constant `K` and `0 ≤ K(ǧ_k + a_k) ≤ 1/2`, then `‖β^P_k − β^{P'}_k‖ ≤ 4K(ǧ_k + a_k)‖β^{P'}_k‖`
  (copy of `csm_artefact_rel`); **`MasterFacts.cdd_art_relD`**: along `D_ε` with `K = M.Kp`
  (`hLam_pairD`) for the pair vertex, stated for `zV0 b` (`k ≥ 1`, `cdd_bt2_zV0`).
* **`cdd_delta_a`**: for `ms ≥ 1`, the `σ_a` components of `V`, `𝒲`, `K` of `pl2Delta` are those of
  `cd3Delta (R.withMsq m) (pl2Pts x y) (ptsX y) (zV0 b) ms t` (`obsHist_zV0`: `zV`, `zV0` histories
  agree from scale `1` on, except `u`).
* **`cdd_delta_struct`**: `pl2Delta` is observable, local, `U(1)`-invariant at `ms`, with
  `V(B)_a = m₂(V(B)_a)ψ̄_0ψ_0` (`ms ≥ 1`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs FRD Flow2 Flow2.Hist Obs2 Step2.D2

variable {L : ℕ} [NeZero L]

section Art

variable {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- **The grid artefact from (H_λ)** at two vertex positions with one constant `K`. -/
theorem cdd_art_rel {Nh : ℕ} {m b μ₀ : ℝ} (P P' : ObsPts 2 L N) (V : OCoup .two)
    (hmu : OCoup2.mua V ≠ 0) {K : ℝ} (h1 : HLam R Nh m b μ₀ (lamHat2 R P V m b μ₀) K)
    (h2 : HLam R Nh m b μ₀ (lamHat2 R P' V m b μ₀) K) {k : ℕ} (hk : k < Nh)
    (hs0 : 0 ≤ K * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k))
    (hs : K * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) ≤ 1 / 2) :
    ‖bt2 R P V m b μ₀ k - bt2 R P' V m b μ₀ k‖ ≤
      4 * (K * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k)) *
        ‖bt2 R P' V m b μ₀ k‖ := by
  have e1 := h1 k hk
  have e2 := h2 k hk
  rw [csm_bt2_eq R P V hmu, csm_bt2_eq R P' V hmu, ← sub_mul, norm_mul, norm_neg,
    norm_mul (lamHat2 R P' V m b μ₀ k), norm_neg]
  set θ := ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 / b) ^ (1 / 3 : ℝ)
  set z := (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k
  set s := K * z
  set Θ : ℂ := ((θ : ℝ) : ℂ)
  have hd : ‖lamHat2 R P V m b μ₀ k - lamHat2 R P' V m b μ₀ k‖ ≤ 2 * (K * θ * z) := by
    have e : lamHat2 R P V m b μ₀ k - lamHat2 R P' V m b μ₀ k =
        (lamHat2 R P V m b μ₀ k - Θ) - (lamHat2 R P' V m b μ₀ k - Θ) := by ring
    rw [e]; refine (norm_sub_le _ _).trans ?_; linarith
  have hnθ : θ ≤ ‖Θ‖ := by
    simp only [Θ, Complex.norm_real, Real.norm_eq_abs]; exact le_abs_self θ
  have hl : θ - K * θ * z ≤ ‖lamHat2 R P' V m b μ₀ k‖ := by
    have := norm_sub_norm_le Θ (Θ - lamHat2 R P' V m b μ₀ k)
    rw [sub_sub_cancel, norm_sub_rev] at this
    linarith
  have hμ := norm_nonneg (OCoup2.mua V)
  rcases le_or_gt 0 θ with hθ | hθ
  · have hKθ : K * θ * z = s * θ := by simp only [s]; ring
    rw [hKθ] at hd hl
    have hl' : θ * (1 / 2) ≤ ‖lamHat2 R P' V m b μ₀ k‖ := by
      have : θ * (1 / 2) ≤ θ - s * θ := by nlinarith
      linarith
    have h3 : 2 * (s * θ) ≤ 4 * s * ‖lamHat2 R P' V m b μ₀ k‖ := by nlinarith
    calc ‖lamHat2 R P V m b μ₀ k - lamHat2 R P' V m b μ₀ k‖ * ‖OCoup2.mua V‖
        ≤ 2 * (s * θ) * ‖OCoup2.mua V‖ := mul_le_mul_of_nonneg_right hd hμ
      _ ≤ 4 * s * ‖lamHat2 R P' V m b μ₀ k‖ * ‖OCoup2.mua V‖ :=
          mul_le_mul_of_nonneg_right h3 hμ
      _ = _ := by ring
  · have hKθ : K * θ * z = s * θ := by simp only [s]; ring
    rw [hKθ] at hd
    have h3 : 2 * (s * θ) ≤ 0 := by nlinarith
    have h4 : ‖lamHat2 R P V m b μ₀ k - lamHat2 R P' V m b μ₀ k‖ * ‖OCoup2.mua V‖ ≤ 0 :=
      (mul_le_mul_of_nonneg_right hd hμ).trans (mul_nonpos_of_nonpos_of_nonneg h3 hμ)
    exact h4.trans (by positivity)

end Art

section Delta

variable {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- `β_k` of `zV b` is that of `zV0 b` from scale `1` on. -/
theorem cdd_bt2_zV0 (P : ObsPts 2 L N) (m b μ₀ : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    bt2 R P (zV b) m b μ₀ k = bt2 R P (zV0 b) m b μ₀ k := by
  unfold bt2 Obs2.histVO2 Obs2.fullV
  rw [(obsHist_zV0 (R.withMsq m) P (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) b
    (traj_zero_X R m b μ₀) k hk).1]

/-- The components `V, 𝒲, K` of `rrSt` depend on the state only through its `V, 𝒲, K`. -/
theorem cdd_rrSt_congr (j : ℕ) (st : RawSt 2 L N) (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N)
    (a a' : Lam 2 L N) (β : (Fin 2 → ℕ) → ℂ) {o o' : ObsSt .two L N} (hV : o.V = o'.V)
    (hW : o.W = o'.W) (hK : o.K = o'.K) :
    (rrSt R j st g μ D K a a' β o).V = (rrSt R j st g μ D K a a' β o').V ∧
      (rrSt R j st g μ D K a a' β o).W = (rrSt R j st g μ D K a a' β o').W ∧
      (rrSt R j st g μ D K a a' β o).K = (rrSt R j st g μ D K a a' β o').K := by
  obtain ⟨V, W, K', u⟩ := o
  obtain ⟨V', W', K'', u'⟩ := o'
  simp only at hV hW hK
  subst hV hW hK
  exact ⟨rfl, rfl, rfl⟩

variable (m b μ₀ : ℝ) (x y : Lam 2 L N) (ms : ℕ)

/-- **The `σ_a` components of `pl2Delta` are those of the `cd3` difference datum for `zV0 b`**
(`ms ≥ 1`). -/
theorem cdd_delta_a (hms : 1 ≤ ms) :
    (∀ B, ((pl2Delta R m b μ₀ x y ms).V B : SA .two (Lam 2 L N)).a =
      ((cd3Delta (R.withMsq m) (pl2Pts x y) (ptsX y) (zV0 b) ms
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).V B : SA .two (Lam 2 L N)).a) ∧
    (∀ B, ((pl2Delta R m b μ₀ x y ms).W B : SA .two (Lam 2 L N)).a =
      ((cd3Delta (R.withMsq m) (pl2Pts x y) (ptsX y) (zV0 b) ms
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).W B : SA .two (Lam 2 L N)).a) ∧
    (∀ X, ((pl2Delta R m b μ₀ x y ms).K X : SA .two (Lam 2 L N)).a =
      ((cd3Delta (R.withMsq m) (pl2Pts x y) (ptsX y) (zV0 b) ms
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).K X : SA .two (Lam 2 L N)).a) := by
  obtain ⟨v1, w1, k1⟩ := obsHist_zV0 (R.withMsq m) (pl2Pts x y) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) b (traj_zero_X R m b μ₀) ms hms
  obtain ⟨v2, w2, k2⟩ := obsHist_zV0 (R.withMsq m) (ptsX y) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) b (traj_zero_X R m b μ₀) ms hms
  have hβ : pl2Beta (pl2O R m b μ₀ (pl2Pts x y) ms) = cd3Beta (R.withMsq m) (pl2Pts x y) (zV0 b) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) := by
    funext B; unfold pl2Beta cd3Beta cd3O pl2O; rw [v1]
  obtain ⟨rv, rw', rk⟩ := cdd_rrSt_congr (R.withMsq m) ms (rawHist (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ms).1
    ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ms).2.1 (rawD (R.withMsq m) (rawHist (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).u ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ms).2.2)
    (rawK (R.withMsq m) (rawHist (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).u ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ms).2.2) (pl2Pts x y).a (ptsX y).a
    (cd3Beta (R.withMsq m) (pl2Pts x y) (zV0 b) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) v1 w1 k1
  refine ⟨fun B => ?_, fun B => ?_, fun X => ?_⟩
  · show (((rrStH (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (pl2Pts x y).a (ptsX y).a
        (pl2Beta (pl2O R m b μ₀ (pl2Pts x y) ms)) (pl2O R m b μ₀ (pl2Pts x y) ms)).V B :
        OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a -
      (((pl2O R m b μ₀ (ptsX y) ms).V B : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a =
      (((rrStH (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (pl2Pts x y).a (ptsX y).a
        (cd3Beta (R.withMsq m) (pl2Pts x y) (zV0 b) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) (cd3O (R.withMsq m) (pl2Pts x y) (zV0 b) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))).V B -
        (cd3O (R.withMsq m) (ptsX y) (zV0 b) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).V B : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a
    rw [hβ]
    unfold rrStH pl2O cd3O
    erw [rv, v2]; rfl
  · show (((rrStH (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (pl2Pts x y).a (ptsX y).a
        (pl2Beta (pl2O R m b μ₀ (pl2Pts x y) ms)) (pl2O R m b μ₀ (pl2Pts x y) ms)).W B :
        OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a -
      (((pl2O R m b μ₀ (ptsX y) ms).W B : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a =
      (((rrStH (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (pl2Pts x y).a (ptsX y).a
        (cd3Beta (R.withMsq m) (pl2Pts x y) (zV0 b) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) (cd3O (R.withMsq m) (pl2Pts x y) (zV0 b) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))).W B -
        (cd3O (R.withMsq m) (ptsX y) (zV0 b) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).W B : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a
    rw [hβ]
    unfold rrStH pl2O cd3O
    erw [rw', w2]; rfl
  · show (((rrStH (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (pl2Pts x y).a (ptsX y).a
        (pl2Beta (pl2O R m b μ₀ (pl2Pts x y) ms)) (pl2O R m b μ₀ (pl2Pts x y) ms)).K X :
        OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a -
      (((pl2O R m b μ₀ (ptsX y) ms).K X : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a =
      (((rrStH (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (pl2Pts x y).a (ptsX y).a
        (cd3Beta (R.withMsq m) (pl2Pts x y) (zV0 b) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) (cd3O (R.withMsq m) (pl2Pts x y) (zV0 b) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))).K X -
        (cd3O (R.withMsq m) (ptsX y) (zV0 b) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).K X : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a
    rw [hβ]
    unfold rrStH pl2O cd3O
    erw [rk, k2]; rfl

theorem cdd_diffO_sym {F G : OE .two (Lam 2 L N)}
    (hF : F ∈ (symSub : Subalgebra ℂ (OE .two (Lam 2 L N))))
    (hG : G ∈ (symSub : Subalgebra ℂ (OE .two (Lam 2 L N)))) :
    plDiffO F G ∈ (symSub : Subalgebra ℂ (OE .two (Lam 2 L N))) := by
  rw [mem_symSub, isSymS_iff_two] at hF hG ⊢
  obtain ⟨f1, f2, f3, f4⟩ := hF
  obtain ⟨g1, g2, g3, g4⟩ := hG
  refine ⟨g1, ?_, g3, ?_⟩
  · show Step.scal _ 2 ((F : SA .two (Lam 2 L N)).a - (G : SA .two (Lam 2 L N)).a) = _ - _
    rw [map_sub, f2, g2]
  · show Step.scal _ 2 ((F : SA .two (Lam 2 L N)).ab - (G : SA .two (Lam 2 L N)).ab) = _ - _
    rw [map_sub, f4, g4]

theorem cdd_diff_symInv {j : ℕ} {o₁ o₂ : ObsSt .two L N} (h₁ : ObsSymInv j o₁)
    (h₂ : ObsSymInv j o₂) : ObsSymInv j (plDiffSt o₁ o₂) where
  V b := cdd_diffO_sym (h₁.V b) (h₂.V b)
  W b := cdd_diffO_sym (h₁.W b) (h₂.W b)
  K Y hY := cdd_diffO_sym (h₁.K Y hY) (h₂.K Y hY)

/-- **The structural hypotheses of the restart for `pl2Delta`** (`1 ≤ ms ≤ N_h`). -/
theorem cdd_delta_struct {Nh : ℕ} (hV : ∀ j < Nh, ValidAt (R.withMsq m) j)
    (hVL : ValidAtL (R.withMsq m) Nh) (hms : 1 ≤ ms) (hmN : ms ≤ Nh)
    (hblk : blk ms (y - x) = blk ms (0 : Lam 2 L N)) :
    (pl2Delta R m b μ₀ x y ms).IsObs ∧ ObsLocInv (ptsX y) ms (pl2Delta R m b μ₀ x y ms) ∧
      ObsSymInv ms (pl2Delta R m b μ₀ x y ms) ∧
      (∀ B, Obs2.Loc2Form (ptsX y).a ((pl2Delta R m b μ₀ x y ms).V B : SA .two (Lam 2 L N)).a) ∧
      (∀ B, ((pl2Delta R m b μ₀ x y ms).V B : SA .two (Lam 2 L N)).a =
        LocObs.mass2 ((pl2Delta R m b μ₀ x y ms).V B : SA .two (Lam 2 L N)).a •
          LocObs.pbp (ptsX y).a) := by
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with ht
  obtain ⟨h₃, hl₃, -⟩ := pl2_delta_inv R m hV hVL b μ₀ x y hmN hblk
  have hval := pl2_valid R m hV hVL t hmN
  have hval' : ∀ j < ms + 1, ValidCore (R.withMsq m) j ∧
      RawInv (R.withMsq m) j (rawHist (R.withMsq m) j t) := fun j hj => hval j (by omega)
  have hv : ∀ j < ms, ValidCore (R.withMsq m) j ∧
      RawInv (R.withMsq m) j (rawHist (R.withMsq m) j t) := fun j hj => hval j (by omega)
  have hab : blk ms (pl2Pts x y).a = blk ms (ptsX y).a := hblk
  obtain ⟨-, -, -, hf, hp⟩ := cd3_struct (R.withMsq m) (pl2Pts x y) (ptsX y) (zV0 b) rfl ms t hval'
    hab rfl
  obtain ⟨ea, -, -⟩ := cdd_delta_a R m b μ₀ x y ms hms
  have HS₁ := obsSymInv_hist (R.withMsq m) (pl2Pts x y) (obsInit .two (zV b) (pl2Pts x y))
    (obsSymInv_init .two (zV b) (pl2Pts x y)) t ms hv
  have HS₂ := obsSymInv_hist (R.withMsq m) (ptsX y) (obsInit .two (zV b) (ptsX y))
    (obsSymInv_init .two (zV b) (ptsX y)) t ms hv
  obtain ⟨hVk, HRk⟩ := hval ms le_rfl
  have HSr := rrSt_obsSymInv_core (R := R.withMsq m) (j := ms) (st := rawHist (R.withMsq m) ms t)
    (g := (t ms).1) (μ := (t ms).2.1) (D := rawD (R.withMsq m) (rawHist (R.withMsq m) ms t).u (t ms).2.2)
    (K := rawK (R.withMsq m) (rawHist (R.withMsq m) ms t).u (t ms).2.2) (a := (pl2Pts x y).a)
    (a' := (ptsX y).a) (β := pl2Beta (pl2O R m b μ₀ (pl2Pts x y) ms)) HS₁ hVk HRk
    (rawD_mem (R.withMsq m) _ _) (rawK_mem (R.withMsq m) _ _)
  refine ⟨h₃, hl₃, cdd_diff_symInv HSr HS₂, fun B => ?_, fun B => ?_⟩
  · rw [ea B]; exact hf B
  · rw [ea B]; exact hp B

end Delta

end

end Spin2
