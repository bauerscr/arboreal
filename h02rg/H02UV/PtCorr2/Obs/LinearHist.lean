import PtCorr2.Obs.ObsHistFrom
import Obs2.Map.LinearStep

/-!
# Additivity of the `σ_a` part along the history from scale `m` and for the chain (Case (2))

For observable data `o₁`, `o₂` at scale `m` (vanishing bulk components) and any points `P`, along
the history started at scale `m` (`obsHistFrom`, the bulk history is shared):

* **`lin_obsHistFrom`**: every component (`V(B)`, `𝒲(B)`, `K(X)`, `u`) of the state at scale `k`
  for `o₁ + o₂` has `σ_a` part the sum of those for `o₁` and `o₂`; **`lin_obsHistFrom_sub`** for
  differences.
* **`lin_prodHiF`**, **`lin_ZhOF`** (and `_sub`): the same for the `σ_a` part of the chain
  `Π'^{≥k} = ∏_{k ≤ i ≤ N_h} chOF_i · lastOF` (the RG product, `hist_omegaOF_from`) and of the
  input `Z_k` with sources. Hence (with `hist_omegaOF_from`) the `σ_a` part of `ω_{Γ_k}(Z_k)` is
  additive in the datum.

The `σ_a` part of `u` gives the one-point vertex chain (`gamA = -ε(u_a)`), so it is additive too.
Proofs: `prjO i` and `mrgO` commute with `obsHistFrom`, `chOF`, `lastOF`, `prodHiF`, `ZhOF`
(`prj_*`, `mrg_*` below), and `Obs2.lin_a_of_comm`.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD Obs2 Flow2 Flow2.Hist LastN

variable {L N : ℕ} [NeZero L]

section PrjChain

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (i : Bool) {P P' : ObsPts 2 L N}
  (hP : P'.a = P.pt i)

include hP

/-- `prjSt i` along the history from scale `m`. -/
theorem prj_obsHistFrom (m : ℕ) (o : ObsSt .two L N) (t : Hist.Seq (Xs R)) :
    ∀ k, prjSt i (obsHistFrom R P m o k t) = obsHistFrom R P' m (prjSt i o) k t
  | 0 => rfl
  | k + 1 => by
    by_cases hk : k + 1 ≤ m
    · rw [obsHistFrom_le o t hk, obsHistFrom_le _ t hk]
    · rw [obsHistFrom_succ (by omega), obsHistFrom_succ (by omega), prj_obsStep i hP,
        prj_obsHistFrom m o t k]

theorem prj_uOutO (j : ℕ) (st : RawSt 2 L N) (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N)
    (o : ObsSt .two L N) :
    prjO i (uOutO R P j st g μ D K o) = uOutO R P' j st g μ D K (prjSt i o) := by
  rw [uOutO, uOutO, prjO_expU, map_neg, prj_uObsTot i hP, prj_fullV, prj_fullW, prj_fullK]

theorem prj_finO (j : ℕ) (st : RawSt 2 L N) (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N)
    (o : ObsSt .two L N) :
    prjO i (finO R P j st g μ D K o) = finO R P' j st g μ D K (prjSt i o) := by
  rw [finO, finO, map_sum]
  refine sum_congr rfl fun U _ => ?_
  rw [map_mul, prj_bpowO, prj_Knext2O i hP, prj_fullV, prj_fullW, prj_fullK,
    show prjF i (GpO P j (stCovN R j st) (fullV R j st g μ o) (fullW st D o) (fullK R j st K o)) =
      GpO P' j (stCovN R j st) (prjF i (fullV R j st g μ o)) (prjF i (fullW st D o))
        (prjF i (fullK R j st K o)) from funext fun b => prj_GpO i hP j _ _ _ _ b,
    prj_fullV, prj_fullW, prj_fullK]

theorem prj_uOutNO (j : ℕ) (st : RawSt 2 L N) (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N)
    (o : ObsSt .two L N) :
    prjO i (uOutNO R P j st g μ D K o) = uOutNO R P' j st g μ D K (prjSt i o) := by
  rw [uOutNO, uOutNO, prjO_expU, map_neg, prj_uXO i hP, ← prj_uXB i hP, prj_fullV, prj_fullW,
    prj_fullK]

theorem prj_chOF (m : ℕ) (o : ObsSt .two L N) (k : ℕ) (t : Hist.Seq (Xs R)) :
    prjO i (chOF R P m o k t) = chOF R P' m (prjSt i o) k t := by
  rw [chOF, chOF, map_smul, prj_uOutO R i hP, prj_obsHistFrom R i hP]

theorem prj_lastOF (m : ℕ) (o : ObsSt .two L N) (Nh : ℕ) (t : Hist.Seq (Xs R)) :
    prjO i (lastOF R P m o Nh t) = lastOF R P' m (prjSt i o) Nh t := by
  rw [lastOF, lastOF, map_smul, map_mul, prj_uOutNO R i hP, prj_obsHistFrom R i hP, zmOF, zmOF,
    omegaCO, omegaCO, prjO_epsO, prjO_expO, finOF, finOF, prj_finO R i hP, prj_obsHistFrom R i hP]

/-- **`prjO i` commutes with the chain `Π'^{≥k}`** of the history from scale `m`. -/
theorem prj_prodHiF (m : ℕ) (o : ObsSt .two L N) (Nh k : ℕ) (t : Hist.Seq (Xs R)) :
    prjO i (prodHiF R P m o Nh k t) = prodHiF R P' m (prjSt i o) Nh k t := by
  rw [prodHiF, prodHiF, map_mul, map_prod, prj_lastOF R i hP]
  simp only [prj_chOF R i hP]

theorem prj_ZhOF (m : ℕ) (o : ObsSt .two L N) (k : ℕ) (t : Hist.Seq (Xs R)) :
    prjO i (ZhOF R P m o k t) = ZhOF R P' m (prjSt i o) k t := by
  rw [ZhOF, ZhOF, ← prj_obsHistFrom R i hP m o t k, ZinO, ZinO, gZO, gZO, map_sum]
  refine sum_congr rfl fun X _ => ?_
  rw [map_mul, prj_bpowO, prj_KextO]
  congr 2
  · funext b
    simp only [prjF_apply, IbO, map_mul, map_neg, map_add, map_one, prjO_oexp, prjO_emb]
    rw [← prj_fullW, prjF_apply]
    rfl
  · funext Y
    simp only [Pi.add_apply, prjF_apply, map_add, embF, prjO_emb]
    rfl

end PrjChain

section MrgChain

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {P P' : ObsPts 2 L N}
  (hP : P'.a = P.a ∧ P.b = P.a)

include hP

/-- `mrgSt` along the history from scale `m`. -/
theorem mrg_obsHistFrom (m : ℕ) (o : ObsSt .two L N) (t : Hist.Seq (Xs R)) :
    ∀ k, mrgSt (obsHistFrom R P m o k t) = obsHistFrom R P' m (mrgSt o) k t
  | 0 => rfl
  | k + 1 => by
    by_cases hk : k + 1 ≤ m
    · rw [obsHistFrom_le o t hk, obsHistFrom_le _ t hk]
    · rw [obsHistFrom_succ (by omega), obsHistFrom_succ (by omega), mrg_obsStep hP,
        mrg_obsHistFrom m o t k]

theorem mrg_uOutO (j : ℕ) (st : RawSt 2 L N) (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N)
    (o : ObsSt .two L N) :
    mrgO (uOutO R P j st g μ D K o) = uOutO R P' j st g μ D K (mrgSt o) := by
  rw [uOutO, uOutO, mrgO_expU, map_neg, mrg_uObsTot hP, mrg_fullV, mrg_fullW, mrg_fullK]

theorem mrg_finO (j : ℕ) (st : RawSt 2 L N) (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N)
    (o : ObsSt .two L N) :
    mrgO (finO R P j st g μ D K o) = finO R P' j st g μ D K (mrgSt o) := by
  rw [finO, finO, map_sum]
  refine sum_congr rfl fun U _ => ?_
  rw [map_mul, mrg_bpowO, mrg_Knext2O hP, mrg_fullV, mrg_fullW, mrg_fullK,
    show mrgF (GpO P j (stCovN R j st) (fullV R j st g μ o) (fullW st D o) (fullK R j st K o)) =
      GpO P' j (stCovN R j st) (mrgF (fullV R j st g μ o)) (mrgF (fullW st D o))
        (mrgF (fullK R j st K o)) from funext fun b => mrg_GpO hP j _ _ _ _ b,
    mrg_fullV, mrg_fullW, mrg_fullK]

theorem mrg_uOutNO (j : ℕ) (st : RawSt 2 L N) (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N)
    (o : ObsSt .two L N) :
    mrgO (uOutNO R P j st g μ D K o) = uOutNO R P' j st g μ D K (mrgSt o) := by
  rw [uOutNO, uOutNO, mrgO_expU, map_neg, mrg_uXO hP, ← mrg_uXB hP, mrg_fullV, mrg_fullW,
    mrg_fullK]

theorem mrg_chOF (m : ℕ) (o : ObsSt .two L N) (k : ℕ) (t : Hist.Seq (Xs R)) :
    mrgO (chOF R P m o k t) = chOF R P' m (mrgSt o) k t := by
  rw [chOF, chOF, map_smul, mrg_uOutO R hP, mrg_obsHistFrom R hP]

theorem mrg_lastOF (m : ℕ) (o : ObsSt .two L N) (Nh : ℕ) (t : Hist.Seq (Xs R)) :
    mrgO (lastOF R P m o Nh t) = lastOF R P' m (mrgSt o) Nh t := by
  rw [lastOF, lastOF, map_smul, map_mul, mrg_uOutNO R hP, mrg_obsHistFrom R hP, zmOF, zmOF,
    omegaCO, omegaCO, mrgO_epsO, mrgO_expO, finOF, finOF, mrg_finO R hP, mrg_obsHistFrom R hP]

/-- **`mrgO` commutes with the chain `Π'^{≥k}`** of the history from scale `m`. -/
theorem mrg_prodHiF (m : ℕ) (o : ObsSt .two L N) (Nh k : ℕ) (t : Hist.Seq (Xs R)) :
    mrgO (prodHiF R P m o Nh k t) = prodHiF R P' m (mrgSt o) Nh k t := by
  rw [prodHiF, prodHiF, map_mul, map_prod, mrg_lastOF R hP]
  simp only [mrg_chOF R hP]

theorem mrg_ZhOF (m : ℕ) (o : ObsSt .two L N) (k : ℕ) (t : Hist.Seq (Xs R)) :
    mrgO (ZhOF R P m o k t) = ZhOF R P' m (mrgSt o) k t := by
  rw [ZhOF, ZhOF, ← mrg_obsHistFrom R hP m o t k, ZinO, ZinO, gZO, gZO, map_sum]
  refine sum_congr rfl fun X _ => ?_
  rw [map_mul, mrg_bpowO, mrg_KextO]
  congr 2
  · funext b
    simp only [mrgF_apply, IbO, map_mul, map_neg, map_add, map_one, mrgO_oexp, mrgO_emb]
    rw [← mrg_fullW, mrgF_apply]
    rfl
  · funext Y
    simp only [Pi.add_apply, mrgF_apply, map_add, embF, mrgO_emb]
    rfl

end MrgChain

section Lin

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N) (m : ℕ)
  {o₁ o₂ : ObsSt .two L N}

/-- **Additivity of the `σ_a` part along the history from scale `m`.** -/
theorem lin_obsHistFrom (h₁ : o₁.IsObs) (h₂ : o₂.IsObs) (k : ℕ) (t : Hist.Seq (Xs R)) :
    (∀ b, ((obsHistFrom R P m (addSt o₁ o₂) k t).V b : SA .two (Lam 2 L N)).a =
      ((obsHistFrom R P m o₁ k t).V b : SA .two (Lam 2 L N)).a +
        ((obsHistFrom R P m o₂ k t).V b : SA .two (Lam 2 L N)).a) ∧
    (∀ b, ((obsHistFrom R P m (addSt o₁ o₂) k t).W b : SA .two (Lam 2 L N)).a =
      ((obsHistFrom R P m o₁ k t).W b : SA .two (Lam 2 L N)).a +
        ((obsHistFrom R P m o₂ k t).W b : SA .two (Lam 2 L N)).a) ∧
    (∀ X, ((obsHistFrom R P m (addSt o₁ o₂) k t).K X : SA .two (Lam 2 L N)).a =
      ((obsHistFrom R P m o₁ k t).K X : SA .two (Lam 2 L N)).a +
        ((obsHistFrom R P m o₂ k t).K X : SA .two (Lam 2 L N)).a) ∧
    ((obsHistFrom R P m (addSt o₁ o₂) k t).u : SA .two (Lam 2 L N)).a =
      ((obsHistFrom R P m o₁ k t).u : SA .two (Lam 2 L N)).a +
        ((obsHistFrom R P m o₂ k t).u : SA .two (Lam 2 L N)).a := by
  refine ⟨fun b => ?_, fun b => ?_, fun X => ?_, ?_⟩
  · refine lin_a_of_comm (fun P o => (obsHistFrom R P m o k t).V b) (fun i P P' o hP => ?_)
      (fun P P' o hP => ?_) P h₁ h₂
    · rw [← prj_obsHistFrom R i hP]; rfl
    · rw [← mrg_obsHistFrom R hP]; rfl
  · refine lin_a_of_comm (fun P o => (obsHistFrom R P m o k t).W b) (fun i P P' o hP => ?_)
      (fun P P' o hP => ?_) P h₁ h₂
    · rw [← prj_obsHistFrom R i hP]; rfl
    · rw [← mrg_obsHistFrom R hP]; rfl
  · refine lin_a_of_comm (fun P o => (obsHistFrom R P m o k t).K X) (fun i P P' o hP => ?_)
      (fun P P' o hP => ?_) P h₁ h₂
    · rw [← prj_obsHistFrom R i hP]; rfl
    · rw [← mrg_obsHistFrom R hP]; rfl
  · refine lin_a_of_comm (fun P o => (obsHistFrom R P m o k t).u) (fun i P P' o hP => ?_)
      (fun P P' o hP => ?_) P h₁ h₂
    · rw [← prj_obsHistFrom R i hP]; rfl
    · rw [← mrg_obsHistFrom R hP]; rfl

/-- **The difference form along the history**: the history of `o₁ - o₂` has `σ_a` parts the
differences. -/
theorem lin_obsHistFrom_sub (h₁ : o₁.IsObs) (h₂ : o₂.IsObs) (k : ℕ) (t : Hist.Seq (Xs R)) :
    (∀ b, ((obsHistFrom R P m (subSt o₁ o₂) k t).V b : SA .two (Lam 2 L N)).a =
      ((obsHistFrom R P m o₁ k t).V b : SA .two (Lam 2 L N)).a -
        ((obsHistFrom R P m o₂ k t).V b : SA .two (Lam 2 L N)).a) ∧
    (∀ b, ((obsHistFrom R P m (subSt o₁ o₂) k t).W b : SA .two (Lam 2 L N)).a =
      ((obsHistFrom R P m o₁ k t).W b : SA .two (Lam 2 L N)).a -
        ((obsHistFrom R P m o₂ k t).W b : SA .two (Lam 2 L N)).a) ∧
    (∀ X, ((obsHistFrom R P m (subSt o₁ o₂) k t).K X : SA .two (Lam 2 L N)).a =
      ((obsHistFrom R P m o₁ k t).K X : SA .two (Lam 2 L N)).a -
        ((obsHistFrom R P m o₂ k t).K X : SA .two (Lam 2 L N)).a) ∧
    ((obsHistFrom R P m (subSt o₁ o₂) k t).u : SA .two (Lam 2 L N)).a =
      ((obsHistFrom R P m o₁ k t).u : SA .two (Lam 2 L N)).a -
        ((obsHistFrom R P m o₂ k t).u : SA .two (Lam 2 L N)).a := by
  obtain ⟨hV, hW, hK, hu⟩ := lin_obsHistFrom R P m (subSt_isObs h₁ h₂) h₂ k t
  rw [addSt_subSt] at hV hW hK hu
  exact ⟨fun b => by rw [hV b]; abel, fun b => by rw [hW b]; abel, fun X => by rw [hK X]; abel,
    by rw [hu]; abel⟩

/-- **Additivity of the `σ_a` part of the chain** `Π'^{≥k}`. -/
theorem lin_prodHiF (h₁ : o₁.IsObs) (h₂ : o₂.IsObs) (Nh k : ℕ) (t : Hist.Seq (Xs R)) :
    (prodHiF R P m (addSt o₁ o₂) Nh k t : SA .two (Lam 2 L N)).a =
      (prodHiF R P m o₁ Nh k t : SA .two (Lam 2 L N)).a +
        (prodHiF R P m o₂ Nh k t : SA .two (Lam 2 L N)).a :=
  lin_a_of_comm (fun P o => prodHiF R P m o Nh k t) (fun i _ _ o hP => prj_prodHiF R i hP m o Nh k t)
    (fun _ _ o hP => mrg_prodHiF R hP m o Nh k t) P h₁ h₂

theorem lin_prodHiF_sub (h₁ : o₁.IsObs) (h₂ : o₂.IsObs) (Nh k : ℕ) (t : Hist.Seq (Xs R)) :
    (prodHiF R P m (subSt o₁ o₂) Nh k t : SA .two (Lam 2 L N)).a =
      (prodHiF R P m o₁ Nh k t : SA .two (Lam 2 L N)).a -
        (prodHiF R P m o₂ Nh k t : SA .two (Lam 2 L N)).a :=
  lin_a_of_comm_sub (fun P o => prodHiF R P m o Nh k t)
    (fun i _ _ o hP => prj_prodHiF R i hP m o Nh k t)
    (fun _ _ o hP => mrg_prodHiF R hP m o Nh k t) P h₁ h₂

/-- **Additivity of the `σ_a` part of the input `Z_k`** with sources. -/
theorem lin_ZhOF_sub (h₁ : o₁.IsObs) (h₂ : o₂.IsObs) (k : ℕ) (t : Hist.Seq (Xs R)) :
    (ZhOF R P m (subSt o₁ o₂) k t : SA .two (Lam 2 L N)).a =
      (ZhOF R P m o₁ k t : SA .two (Lam 2 L N)).a - (ZhOF R P m o₂ k t : SA .two (Lam 2 L N)).a :=
  lin_a_of_comm_sub (fun P o => ZhOF R P m o k t) (fun i _ _ o hP => prj_ZhOF R i hP m o k t)
    (fun _ _ o hP => mrg_ZhOF R hP m o k t) P h₁ h₂

end Lin

end

end PtCorr2
