import Obs2.Map.LinearMrg
import Obs2.Map.SwapHist

/-!
# Additivity of the `σ_a` part of the observable step in the `σ_a` datum (Case (2))

For observable states `o₁`, `o₂` (vanishing bulk components) and any observable points `P`:

  `(obsStep_P (o₁ + o₂))_a = (obsStep_P o₁)_a + (obsStep_P o₂)_a`

componentwise (`V`, `𝒲`, `K`, `u`; **`lin_obsStep`**), and the same for differences
(**`lin_obsStep_sub`**). The bulk pieces of the step (`V♭`, `𝒲`, `K♭`, from the bulk history) are
the same for all three states; only the `σ_a` components of the output are claimed additive (the
`σ_aσ_b` component is not: it is bilinear in the `σ_a`, `σ_b` data).

**Proof** (no expansion of the map). Put the two `σ_a` data into the `σ_a` and `σ_b` slots,
`mixSt o₁ o₂ = (σ_a o₁_a + σ_b o₂_a)`, and run the step with the points `P₂ = (a, a)`. Then
* `prjO true` (`Obs2/Map/SwapO`) recovers the step of `o₁` at `P`, `prjO false` that of `o₂` at `P`
  (the `σ_b` slot is localised at `P₂.b = a`), and
* the merge `mrgO : σ_b ↦ σ_a` (`Obs2/Map/LinearMrg`) recovers the step of `o₁ + o₂` at `P`;
the `σ_a` part of `mrgO F` is `F_a + F_b`. The abstract form is **`lin_a_of_comm`**: any output that
commutes with `prjO i` and `mrgO` (with the corresponding change of points) has additive `σ_a`
part. It is reused for the history and the chain (`PtCorr2/Obs/LinearHist.lean`).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD

variable {L N : ℕ} [NeZero L]

/-! ### States: merge, mixing, sums -/

/-- `mrgO` on an observable state. -/
def mrgSt (o : ObsSt .two L N) : ObsSt .two L N :=
  ⟨mrgF o.V, mrgF o.W, mrgF o.K, mrgO o.u⟩

section Mix

variable {Λ : Type*} [DecidableEq Λ]

/-- `σ_a F₁_a + σ_b F₂_a` (bulk part of `F₁`). -/
def mixS (F₁ F₂ : SA .two Λ) : SA .two Λ := ⟨F₁.e, F₁.a, F₂.a, 0⟩

theorem mixS_mem (F₁ F₂ : OE .two Λ) : mixS (F₁ : SA .two Λ) (F₂ : SA .two Λ) ∈ OEv .two Λ := by
  obtain ⟨h1, h2, -, -⟩ := mem_OEv.1 F₁.2
  obtain ⟨-, h2', -, -⟩ := mem_OEv.1 F₂.2
  exact mem_OEv.2 ⟨h1, h2, h2', by simp [mixS]⟩

/-- The mixed element `F₁_∅ + σ_aF₁_a + σ_bF₂_a`. -/
def mixO (F₁ F₂ : OE .two Λ) : OE .two Λ := ⟨mixS (F₁ : SA .two Λ) (F₂ : SA .two Λ), mixS_mem F₁ F₂⟩

theorem prjO_true_mixO (F₁ F₂ : OE .two Λ) : prjO true (mixO F₁ F₂) = prjO true F₁ :=
  Subtype.ext (SA.ext rfl rfl rfl rfl)

theorem prjO_false_mixO {F₁ F₂ : OE .two Λ} (he : (F₁ : SA .two Λ).e = (F₂ : SA .two Λ).e) :
    prjO false (mixO F₁ F₂) = prjO true F₂ :=
  Subtype.ext (SA.ext he rfl rfl rfl)

theorem mrgO_mixO {F₁ F₂ : OE .two Λ} (he : (F₂ : SA .two Λ).e = 0) :
    mrgO (mixO F₁ F₂) = prjO true (F₁ + F₂) := by
  refine Subtype.ext (SA.ext ?_ rfl rfl rfl)
  show (F₁ : SA .two Λ).e = (F₁ : SA .two Λ).e + (F₂ : SA .two Λ).e
  rw [he, add_zero]

end Mix

/-- The mixed state `σ_a o₁ + σ_b (o₂)_a`. -/
def mixSt (o₁ o₂ : ObsSt .two L N) : ObsSt .two L N :=
  ⟨fun b => mixO (o₁.V b) (o₂.V b), fun b => mixO (o₁.W b) (o₂.W b),
    fun X => mixO (o₁.K X) (o₂.K X), mixO o₁.u o₂.u⟩

/-- The sum of two states. -/
def addSt (o₁ o₂ : ObsSt .two L N) : ObsSt .two L N :=
  ⟨o₁.V + o₂.V, o₁.W + o₂.W, o₁.K + o₂.K, o₁.u + o₂.u⟩

/-- The difference of two states. -/
def subSt (o₁ o₂ : ObsSt .two L N) : ObsSt .two L N :=
  ⟨o₁.V - o₂.V, o₁.W - o₂.W, o₁.K - o₂.K, o₁.u - o₂.u⟩

theorem ln_e_eq_zero_of_bulk {Λ : Type*} [DecidableEq Λ] {F : OE .two Λ} (h : bulk F = 0) :
    (F : SA .two Λ).e = 0 := by
  have := congrArg Subtype.val h
  simpa using this

theorem subSt_isObs {o₁ o₂ : ObsSt .two L N} (h₁ : o₁.IsObs) (h₂ : o₂.IsObs) :
    (subSt o₁ o₂).IsObs where
  V b := by simp [subSt, h₁.V b, h₂.V b]
  W b := by simp [subSt, h₁.W b, h₂.W b]
  K X := by simp [subSt, h₁.K X, h₂.K X]
  u := by simp [subSt, h₁.u, h₂.u]

theorem addSt_subSt (o₁ o₂ : ObsSt .two L N) : addSt (subSt o₁ o₂) o₂ = o₁ := by
  cases o₁; cases o₂; simp [addSt, subSt]

theorem prjSt_true_mixSt (o₁ o₂ : ObsSt .two L N) : prjSt true (mixSt o₁ o₂) = prjSt true o₁ := by
  simp only [prjSt, mixSt, ObsSt.mk.injEq]
  refine ⟨funext fun b => ?_, funext fun b => ?_, funext fun X => ?_, ?_⟩ <;>
    exact prjO_true_mixO _ _

theorem prjSt_false_mixSt {o₁ o₂ : ObsSt .two L N} (h₁ : o₁.IsObs) (h₂ : o₂.IsObs) :
    prjSt false (mixSt o₁ o₂) = prjSt true o₂ := by
  simp only [prjSt, mixSt, ObsSt.mk.injEq]
  refine ⟨funext fun b => ?_, funext fun b => ?_, funext fun X => ?_, ?_⟩
  · exact prjO_false_mixO (by rw [ln_e_eq_zero_of_bulk (h₁.V b), ln_e_eq_zero_of_bulk (h₂.V b)])
  · exact prjO_false_mixO (by rw [ln_e_eq_zero_of_bulk (h₁.W b), ln_e_eq_zero_of_bulk (h₂.W b)])
  · exact prjO_false_mixO (by rw [ln_e_eq_zero_of_bulk (h₁.K X), ln_e_eq_zero_of_bulk (h₂.K X)])
  · exact prjO_false_mixO (by rw [ln_e_eq_zero_of_bulk h₁.u, ln_e_eq_zero_of_bulk h₂.u])

theorem mrgSt_mixSt (o₁ : ObsSt .two L N) {o₂ : ObsSt .two L N} (h₂ : o₂.IsObs) :
    mrgSt (mixSt o₁ o₂) = prjSt true (addSt o₁ o₂) := by
  simp only [mrgSt, mixSt, prjSt, addSt, ObsSt.mk.injEq]
  refine ⟨funext fun b => ?_, funext fun b => ?_, funext fun X => ?_, ?_⟩
  · exact mrgO_mixO (ln_e_eq_zero_of_bulk (h₂.V b))
  · exact mrgO_mixO (ln_e_eq_zero_of_bulk (h₂.W b))
  · exact mrgO_mixO (ln_e_eq_zero_of_bulk (h₂.K X))
  · exact mrgO_mixO (ln_e_eq_zero_of_bulk h₂.u)

/-- The doubled points `(a, a)`. -/
def ObsPts.dbl (P : ObsPts 2 L N) : ObsPts 2 L N := ⟨P.a, P.a, P.Ra⟩

/-! ### The abstract additivity principle -/

/-- **Additivity of the `σ_a` part** of any output commuting with `prjO i` and `mrgO`. -/
theorem lin_a_of_comm (X : ObsPts 2 L N → ObsSt .two L N → OE .two (Lam 2 L N))
    (hprj : ∀ (i : Bool) (P P' : ObsPts 2 L N) (o : ObsSt .two L N), P'.a = P.pt i →
      prjO i (X P o) = X P' (prjSt i o))
    (hmrg : ∀ (P P' : ObsPts 2 L N) (o : ObsSt .two L N), P'.a = P.a ∧ P.b = P.a →
      mrgO (X P o) = X P' (mrgSt o))
    (P : ObsPts 2 L N) {o₁ o₂ : ObsSt .two L N} (h₁ : o₁.IsObs) (h₂ : o₂.IsObs) :
    (X P (addSt o₁ o₂) : SA .two (Lam 2 L N)).a =
      (X P o₁ : SA .two (Lam 2 L N)).a + (X P o₂ : SA .two (Lam 2 L N)).a := by
  have ha : ∀ (P' : ObsPts 2 L N) (o : ObsSt .two L N),
      (X P' o : SA .two (Lam 2 L N)).a = (X P' (prjSt true o) : SA .two (Lam 2 L N)).a :=
    fun P' o => by rw [← hprj true P' P' o rfl]; rfl
  have h1 := hprj true P.dbl P (mixSt o₁ o₂) rfl
  have h2 := hprj false P.dbl P (mixSt o₁ o₂) rfl
  have h3 := hmrg P.dbl P (mixSt o₁ o₂) ⟨rfl, rfl⟩
  rw [prjSt_true_mixSt] at h1
  rw [prjSt_false_mixSt h₁ h₂] at h2
  rw [mrgSt_mixSt o₁ h₂] at h3
  rw [ha P (addSt o₁ o₂), ← h3, ha P o₁, ← h1, ha P o₂, ← h2]
  rfl

/-- The difference form of `lin_a_of_comm`. -/
theorem lin_a_of_comm_sub (X : ObsPts 2 L N → ObsSt .two L N → OE .two (Lam 2 L N))
    (hprj : ∀ (i : Bool) (P P' : ObsPts 2 L N) (o : ObsSt .two L N), P'.a = P.pt i →
      prjO i (X P o) = X P' (prjSt i o))
    (hmrg : ∀ (P P' : ObsPts 2 L N) (o : ObsSt .two L N), P'.a = P.a ∧ P.b = P.a →
      mrgO (X P o) = X P' (mrgSt o))
    (P : ObsPts 2 L N) {o₁ o₂ : ObsSt .two L N} (h₁ : o₁.IsObs) (h₂ : o₂.IsObs) :
    (X P (subSt o₁ o₂) : SA .two (Lam 2 L N)).a =
      (X P o₁ : SA .two (Lam 2 L N)).a - (X P o₂ : SA .two (Lam 2 L N)).a := by
  have h := lin_a_of_comm X hprj hmrg P (subSt_isObs h₁ h₂) h₂
  rw [addSt_subSt] at h
  rw [h]; abel

/-! ### The step -/

section Step

variable {P P' : ObsPts 2 L N} (hP : P'.a = P.a ∧ P.b = P.a) (R : RGPar 2 L N) (j : ℕ)
  (st : RawSt 2 L N) (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N) (o : ObsSt .two L N)

omit hP in
theorem mrg_fullV : mrgF (fullV R j st g μ o) = fullV R j st g μ (mrgSt o) := by
  funext b
  simp only [mrgF_apply, fullV, Pi.add_apply, map_add, embF, mrgO_emb]
  rfl

omit hP in
theorem mrg_fullW : mrgF (fullW st D o) = fullW st D (mrgSt o) := by
  funext b
  simp only [mrgF_apply, fullW, Pi.add_apply, map_add, embF, mrgO_emb]
  rfl

omit hP in
theorem mrg_fullK : mrgF (fullK R j st K o) = fullK R j st K (mrgSt o) := by
  funext X
  rw [mrgF_apply, fullK, fullK, mrg_KflatO]
  congr 1
  funext Y
  simp only [mrgF_apply, Pi.add_apply, map_add, embF, mrgO_emb]
  rfl

include hP

/-- **`mrgSt ∘ obsStep_P = obsStep_{P'} ∘ mrgSt`** (`P.b = P.a = P'.a`). -/
theorem mrg_obsStep :
    mrgSt (obsStep R P j st g μ D K o) = obsStep R P' j st g μ D K (mrgSt o) := by
  have hV := mrg_fullV R j st g μ o
  have hW := mrg_fullW st D o
  have hK := mrg_fullK R j st K o
  unfold obsStep mrgSt
  simp only [ObsSt.mk.injEq]
  refine ⟨funext fun c' => ?_, funext fun c' => ?_, funext fun X => ?_, ?_⟩
  · rw [mrgF_apply, mrgO_πobs, mrg_Vnext2O hP, hV, hW, hK]; rfl
  · rw [mrgF_apply, mrgO_πobs, mrg_Wnext2O hP, hV, hW]; rfl
  · rw [mrgF_apply, mrgO_πobs, mrg_KconnO,
      show mrgF (KplusO P j (stCov R j st) (fullV R j st g μ o) (fullW st D o)
          (fullK R j st K o)) = KplusO P' j (stCov R j st) (mrgF (fullV R j st g μ o))
            (mrgF (fullW st D o)) (mrgF (fullK R j st K o)) from
        funext fun U => mrg_KplusO hP j _ _ _ _ U, hV, hW, hK]
    rfl
  · rw [map_add, mrg_uObsTot hP, hV, hW, hK]
    rfl

end Step

section StepLin

variable (R : RGPar 2 L N) (P : ObsPts 2 L N) (j : ℕ) (st : RawSt 2 L N) (g μ : ℝ)
  (D : Fam 2 L N) (K : Act 2 L N) {o₁ o₂ : ObsSt .two L N}

/-- **Additivity of the `σ_a` part of the observable step** in the observable datum: for
observable `o₁`, `o₂`, every component (`V(B)`, `𝒲(B)`, `K(X)`, `u`) of `obsStep (o₁ + o₂)` has
`σ_a` part the sum of those of `obsStep o₁` and `obsStep o₂`. -/
theorem lin_obsStep (h₁ : o₁.IsObs) (h₂ : o₂.IsObs) :
    (∀ b, ((obsStep R P j st g μ D K (addSt o₁ o₂)).V b : SA .two (Lam 2 L N)).a =
      ((obsStep R P j st g μ D K o₁).V b : SA .two (Lam 2 L N)).a +
        ((obsStep R P j st g μ D K o₂).V b : SA .two (Lam 2 L N)).a) ∧
    (∀ b, ((obsStep R P j st g μ D K (addSt o₁ o₂)).W b : SA .two (Lam 2 L N)).a =
      ((obsStep R P j st g μ D K o₁).W b : SA .two (Lam 2 L N)).a +
        ((obsStep R P j st g μ D K o₂).W b : SA .two (Lam 2 L N)).a) ∧
    (∀ X, ((obsStep R P j st g μ D K (addSt o₁ o₂)).K X : SA .two (Lam 2 L N)).a =
      ((obsStep R P j st g μ D K o₁).K X : SA .two (Lam 2 L N)).a +
        ((obsStep R P j st g μ D K o₂).K X : SA .two (Lam 2 L N)).a) ∧
    ((obsStep R P j st g μ D K (addSt o₁ o₂)).u : SA .two (Lam 2 L N)).a =
      ((obsStep R P j st g μ D K o₁).u : SA .two (Lam 2 L N)).a +
        ((obsStep R P j st g μ D K o₂).u : SA .two (Lam 2 L N)).a := by
  refine ⟨fun b => ?_, fun b => ?_, fun X => ?_, ?_⟩
  · refine lin_a_of_comm (fun P o => (obsStep R P j st g μ D K o).V b) (fun i P P' o hP => ?_)
      (fun P P' o hP => ?_) P h₁ h₂
    · rw [← prj_obsStep i hP]; rfl
    · rw [← mrg_obsStep hP]; rfl
  · refine lin_a_of_comm (fun P o => (obsStep R P j st g μ D K o).W b) (fun i P P' o hP => ?_)
      (fun P P' o hP => ?_) P h₁ h₂
    · rw [← prj_obsStep i hP]; rfl
    · rw [← mrg_obsStep hP]; rfl
  · refine lin_a_of_comm (fun P o => (obsStep R P j st g μ D K o).K X) (fun i P P' o hP => ?_)
      (fun P P' o hP => ?_) P h₁ h₂
    · rw [← prj_obsStep i hP]; rfl
    · rw [← mrg_obsStep hP]; rfl
  · refine lin_a_of_comm (fun P o => (obsStep R P j st g μ D K o).u) (fun i P P' o hP => ?_)
      (fun P P' o hP => ?_) P h₁ h₂
    · rw [← prj_obsStep i hP]; rfl
    · rw [← mrg_obsStep hP]; rfl

end StepLin

end

end Obs2
