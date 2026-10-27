import Obs2.Map.ConstSplit
import Obs2.Flow.GamRem
import PtCorr2.Zero.ZeroInit

/-!
# The scale-0 constant `γ_a` decouples exactly from the Case-(2) observable flow

`gaZero V` is the Case-(2) vertex `V` with `γ_a = 0`. The initial block families differ by the
observable constant `κ₀(B) = −γ_a σ_a 1_{a ∈ B}` (`kap0`, `kap0_cst`). Along a history with
`K_0 = 0` (in particular along every trajectory `traj … b μ₀`, `(t 0).2.2 = 0`), by
`Obs2.Map.ConstSplit` the first step absorbs `κ₀` into the observable constant `u^{obs}_1`, so

* **`obsHist_gaZero`**: for `j ≥ 1` the states `V^{obs}_j`, `𝒲^{obs}_j`, `K^{obs}_j` from `V` and from
  `gaZero V` coincide;
* `histWO2`, `histKO2` coincide at every scale, `histVO2` up to observable constants;
* **`betaTot2_gaZero`**, **`frakN2_gaZero`**, **`shareErr2_gaZero`**, **`gamWK2_gaZero`**: the
  coupling `β_k`, the one-loop coefficient `𝔫^{(2)}_k`, the error of the `μ^{(2)}` flow and the
  `K`/`𝒲` part of `ρ_k` are those of the flow with `γ_a = 0`, at every scale.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

variable {L N : ℕ} [NeZero L]

/-! ### Sequences differing by constants -/

section Seq

variable {d : ℕ} {c : Obs.Case}

theorem betaTot2_addc {κ : OFam .two d L N} (hκ : ∀ b, IsCstObs (κ b)) (k : ℕ)
    (V : OFam .two d L N) : betaTot2 k (V + κ) = betaTot2 k V := by
  unfold betaTot2
  refine sum_congr rfl fun b _ => ?_
  show mass2 ((V b : SA .two (Lam d L N)).a + (κ b : SA .two (Lam d L N)).a) = _
  rw [mass2_add, (hκ b).mass2_a, add_zero]

theorem betaX2_addc {κ : OFam .two d L N} (hκ : ∀ b, IsCstObs (κ b)) (k : ℕ)
    (V : OFam .two d L N) (X : Finset (Lam d L N)) : betaX2 k (V + κ) X = betaX2 k V X := by
  unfold betaX2
  refine sum_congr rfl fun b _ => ?_
  show mass2 ((V b : SA .two (Lam d L N)).a + (κ b : SA .two (Lam d L N)).a) = _
  rw [mass2_add, (hκ b).mass2_a, add_zero]

/-- Two block-family sequences that differ by observable constants at every scale. -/
def CstRel (V V' : ℕ → OFam .two d L N) : Prop :=
  ∀ k, ∃ κ : OFam .two d L N, (∀ b, IsCstObs (κ b)) ∧ V k = V' k + κ

variable {V V' : ℕ → OFam .two d L N}

theorem CstRel.bulkE2 (h : CstRel V V') (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ) (k : ℕ) :
    bulkE2 C V k = bulkE2 C V' k := by
  obtain ⟨κ, hκ, e⟩ := h k
  unfold Obs2.bulkE2
  rw [e, VprLO_addc k (C k) (V' k) hκ]
  show ((VprLO k (C k) (V' k) : SA .two (Lam d L N)).e +
    ((∑ b ∈ blockIdx (L := L) (N := N) k, κ b : OE .two (Lam d L N)) : SA .two (Lam d L N)).e) = _
  rw [(IsCstObs.sum _ hκ).e_eq, add_zero]

theorem CstRel.betaTot2 (h : CstRel V V') (k : ℕ) : betaTot2 k (V k) = betaTot2 k (V' k) := by
  obtain ⟨κ, hκ, e⟩ := h k
  rw [e, betaTot2_addc hκ]

theorem CstRel.betaX2 (h : CstRel V V') (k : ℕ) (X : Finset (Lam d L N)) :
    betaX2 k (V k) X = betaX2 k (V' k) X := by
  obtain ⟨κ, hκ, e⟩ := h k
  rw [e, betaX2_addc hκ]

theorem CstRel.frakN2 (h : CstRel V V') (P : ObsPts d L N)
    (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ) (j : ℕ) :
    frakN2 P C V j = frakN2 P C V' j := by
  simp only [Obs2.frakN2, nuBar2, tadInc2, h.bulkE2 C]

theorem CstRel.tadInc2 (h : CstRel V V') (P : ObsPts d L N)
    (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ) (k j : ℕ) :
    tadInc2 P C V k j = tadInc2 P C V' k j := by
  simp only [Obs2.tadInc2, h.bulkE2 C]

theorem CstRel.shareErr2 (h : CstRel V V') (P : ObsPts d L N)
    (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ) (W : ℕ → OFam .two d L N)
    (K : ℕ → OAct .two d L N) (j : ℕ) (X : Finset (Lam d L N)) :
    shareErr2 P C V W K j X = shareErr2 P C V' W K j X := by
  have hP : ∀ k, ∀ m X Γ, wProdX P k (C k) (V k) (W k) m X Γ =
      wProdX P k (C k) (V' k) (W k) m X Γ := by
    intro k m X Γ
    obtain ⟨κ, hκ, e⟩ := h k
    rw [e, wProdX_addc P k (C k) (V' k) (W k) hκ]
  simp only [Obs2.shareErr2, muDriftX2, muProdIncX2, hP, h.betaX2, h.tadInc2 P C]

end Seq

/-! ### The vertex with `γ_a = 0` -/

/-- The Case-(2) vertex with `γ_a` set to `0`. -/
def gaZero (V : OCoup .two) : OCoup .two :=
  ⟨OCoup2.mua V, OCoup2.mub V, 0, OCoup2.gb V, OCoup2.q V, OCoup2.eta V, OCoup2.r V, OCoup2.chi V⟩

@[simp] theorem gaZero_ga (V : OCoup .two) : OCoup2.ga (gaZero V) = 0 := rfl
@[simp] theorem gaZero_mua (V : OCoup .two) : OCoup2.mua (gaZero V) = OCoup2.mua V := rfl

/-- The initial difference `κ₀(B) = −γ_aσ_a1_{a∈B}`. -/
def kap0 (V : OCoup .two) (P : ObsPts 2 L N) : OFam .two 2 L N :=
  fun b => (obsInit .two V P).V b - (obsInit .two (gaZero V) P).V b

theorem kap0_cst (V : OCoup .two) (P : ObsPts 2 L N) (b : Fin 2 → ℕ) :
    IsCstObs (kap0 V P b) := by
  refine ⟨?_, ?_⟩
  · refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;>
      simp [kap0, obsInit, Obs2.evalFam, Obs2.evalO, Obs2.evalS, Obs2.OCoup2.evalS, gaZero,
        psibar, psi, eps_ψ, smul_sub]
    rw [Algebra.smul_def]
  · show bulk (Obs2.evalO .two V P.a P.b _ - Obs2.evalO .two (gaZero V) P.a P.b _) = 0
    rw [map_sub, Obs2.bulk_evalO, Obs2.bulk_evalO, sub_zero]

theorem obsInit_V_kap0 (V : OCoup .two) (P : ObsPts 2 L N) :
    (obsInit .two V P).V = (obsInit .two (gaZero V) P).V + kap0 V P := by
  funext b; simp [kap0]

section Hist

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N)

theorem obsStep_congrVWK {c : Obs.Case} (j : ℕ) (st : RawSt 2 L N) (g μ : ℝ) (D : Fam 2 L N)
    (K : Act 2 L N) {o o' : ObsSt c L N} (hV : o.V = o'.V) (hW : o.W = o'.W)
    (hK : o.K = o'.K) :
    (obsStep R P j st g μ D K o).V = (obsStep R P j st g μ D K o').V ∧
      (obsStep R P j st g μ D K o).W = (obsStep R P j st g μ D K o').W ∧
      (obsStep R P j st g μ D K o).K = (obsStep R P j st g μ D K o').K := by
  simp only [obsStep, fullV, fullW, fullK, hV, hW, hK]
  refine ⟨?_, ?_, ?_⟩ <;> trivial

theorem fullK_obsInit_zero (V : OCoup .two) (j : ℕ) (st : RawSt 2 L N) :
    fullK R j st 0 (obsInit .two V P) = 0 := by
  funext Y
  simp [fullK, KflatO, embF, obsInit]

theorem obsStep_kap0 (V : OCoup .two) (st : RawSt 2 L N) (g μ : ℝ) (D : Fam 2 L N) :
    (obsStep R P 0 st g μ D 0 (obsInit .two V P)).V =
        (obsStep R P 0 st g μ D 0 (obsInit .two (gaZero V) P)).V ∧
      (obsStep R P 0 st g μ D 0 (obsInit .two V P)).W =
        (obsStep R P 0 st g μ D 0 (obsInit .two (gaZero V) P)).W ∧
      (obsStep R P 0 st g μ D 0 (obsInit .two V P)).K =
        (obsStep R P 0 st g μ D 0 (obsInit .two (gaZero V) P)).K := by
  have hκ := kap0_cst V P
  have hV : fullV R 0 st g μ (obsInit .two V P) =
      fullV R 0 st g μ (obsInit .two (gaZero V) P) + kap0 V P := by
    rw [fullV, fullV, obsInit_V_kap0, add_assoc]
  have hW : fullW st D (obsInit .two V P) = fullW st D (obsInit .two (gaZero V) P) := rfl
  have hK := fullK_obsInit_zero R P V 0 st
  have hK' := fullK_obsInit_zero R P (gaZero V) 0 st
  simp only [obsStep, hV, hW, hK, hK', Vnext2O_addc _ _ _ _ _ _ hκ, Wnext2O_addc _ _ _ _ _ hκ,
    KplusO_addc _ _ _ _ _ hκ]
  refine ⟨?_, ?_, ?_⟩ <;> trivial

variable (t : Hist.Seq (Xs R))

/-- **The observable states from `V` and from `gaZero V` coincide from scale `1` on** (if the
initial bulk activity vanishes). -/
theorem obsHist_gaZero (V : OCoup .two) (ht : (t 0).2.2 = 0) :
    ∀ j, 1 ≤ j →
      (obsHist R P (obsInit .two V P) j t).V = (obsHist R P (obsInit .two (gaZero V) P) j t).V ∧
      (obsHist R P (obsInit .two V P) j t).W = (obsHist R P (obsInit .two (gaZero V) P) j t).W ∧
      (obsHist R P (obsInit .two V P) j t).K = (obsHist R P (obsInit .two (gaZero V) P) j t).K
  | 0, h => absurd h (by omega)
  | 1, _ => by
    rw [obsHist_succ, obsHist_succ]
    have hK : rawK R (rawHist R 0 t).u (t 0).2.2 = 0 := by rw [ht]; exact rawK_zeroX R _
    rw [hK]
    exact obsStep_kap0 R P V _ _ _ _
  | j + 2, _ => by
    obtain ⟨h1, h2, h3⟩ := obsHist_gaZero V ht (j + 1) (by omega)
    rw [obsHist_succ R P (obsInit .two V P) (j + 1) t,
      obsHist_succ R P (obsInit .two (gaZero V) P) (j + 1) t]
    exact obsStep_congrVWK R P _ _ _ _ _ _ h1 h2 h3

variable {t}

theorem histWO2_gaZero (V : OCoup .two) (ht : (t 0).2.2 = 0) (k : ℕ) :
    histWO2 R P (obsInit .two V P) t k = histWO2 R P (obsInit .two (gaZero V) P) t k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rfl
  · unfold histWO2 fullW; rw [(obsHist_gaZero R P t V ht k hk).2.1]

theorem histKO2_gaZero (V : OCoup .two) (ht : (t 0).2.2 = 0) (k : ℕ) :
    histKO2 R P (obsInit .two V P) t k = histKO2 R P (obsInit .two (gaZero V) P) t k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rfl
  · unfold histKO2 fullK; rw [(obsHist_gaZero R P t V ht k hk).2.2]

theorem histVO2_gaZero (V : OCoup .two) (ht : (t 0).2.2 = 0) :
    CstRel (histVO2 R P (obsInit .two V P) t) (histVO2 R P (obsInit .two (gaZero V) P) t) := by
  intro k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨kap0 V P, kap0_cst V P, ?_⟩
    unfold histVO2
    rw [fullV, fullV, show obsHist R P (obsInit .two V P) 0 t = obsInit .two V P from rfl,
      show obsHist R P (obsInit .two (gaZero V) P) 0 t = obsInit .two (gaZero V) P from rfl,
      obsInit_V_kap0, add_assoc]
  · refine ⟨0, fun _ => IsCstObs.zero, ?_⟩
    unfold histVO2 fullV
    rw [(obsHist_gaZero R P t V ht k hk).1, add_zero]

theorem betaTot2_gaZero (V : OCoup .two) (ht : (t 0).2.2 = 0) (k : ℕ) :
    betaTot2 k (histVO2 R P (obsInit .two V P) t k) =
      betaTot2 k (histVO2 R P (obsInit .two (gaZero V) P) t k) :=
  (histVO2_gaZero R P V ht).betaTot2 k

theorem frakN2_gaZero (V : OCoup .two) (ht : (t 0).2.2 = 0) (k : ℕ) :
    frakN2 P (histCovO R t) (histVO2 R P (obsInit .two V P) t) k =
      frakN2 P (histCovO R t) (histVO2 R P (obsInit .two (gaZero V) P) t) k :=
  (histVO2_gaZero R P V ht).frakN2 P _ k

theorem shareErr2_gaZero (V : OCoup .two) (ht : (t 0).2.2 = 0) (k : ℕ)
    (X : Finset (Lam 2 L N)) :
    shareErr2 P (histCovO R t) (histVO2 R P (obsInit .two V P) t)
        (histWO2 R P (obsInit .two V P) t) (histKO2 R P (obsInit .two V P) t) k X =
      shareErr2 P (histCovO R t) (histVO2 R P (obsInit .two (gaZero V) P) t)
        (histWO2 R P (obsInit .two (gaZero V) P) t)
        (histKO2 R P (obsInit .two (gaZero V) P) t) k X := by
  have hW : histWO2 R P (obsInit .two V P) t = histWO2 R P (obsInit .two (gaZero V) P) t :=
    funext (histWO2_gaZero R P V ht)
  have hK : histKO2 R P (obsInit .two V P) t = histKO2 R P (obsInit .two (gaZero V) P) t :=
    funext (histKO2_gaZero R P V ht)
  rw [hW, hK]
  exact (histVO2_gaZero R P V ht).shareErr2 P _ _ _ k X

/-- **The `K`/`𝒲` part of `ρ_k` does not see `γ_a`.** -/
theorem gamWK2_gaZero (V : OCoup .two) (ht : (t 0).2.2 = 0) (k : ℕ) :
    gamWK2 R P (obsInit .two V P) t k = gamWK2 R P (obsInit .two (gaZero V) P) t k := by
  unfold gamWK2
  rw [histWO2_gaZero R P V ht, histKO2_gaZero R P V ht]

end Hist

end

end PtCorr2
