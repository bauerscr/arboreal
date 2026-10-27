import PtCorr2.Obs.ObsSymFrom
import PtCorr2.Pair.PairReduceChain
import Obs2.Flow.VObsAB2

/-!
# The `ab` coupling along the reduced history: `V'_k(B)_{ab} ∈ 𝒩({a,b})`, exact Pauli defects

* `ObsVabInv P o`: the `ab` parts of `V^{obs}(B)` lie in `𝒩({a,b})`; **`obsVabInv_step`** (from
  `Obs2.Vnext2O_ab_mem_pair`: `e^{ℒ_C}` and `loc^{ab}` map into `𝒩({a,b})`), **`obsVabInv_histFrom`**.
  The reduced state at coalescence has `V' = 0` (`obsVabInv_redSt`).
* `isSym_ab_of_symSub`: `U(1)` invariance of the `ab` component.
* Along the history (`hVR`): **`hVR_ab_mem`**, **`hVR_ab_sym`**, and the exact Pauli defects
  **`pdefM2_hVR_eq`** (`𝔡₂_k = M₄_k·(C_k(a,a) + C_k(b,b) − C_k(a,b) − C_k(b,a))`) and
  **`pdefAB2_hVR_sub`** (`𝔡_k − M₄_k·det_k = ∑_B∑_{u,v}c_{uv}(V'_k(B))(C_k(u,v) − C_k(a,a))`), and
  **`dAB_hVR_eq`** (`D_k = gradAB(V'_k(Λ)_{ab})`).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD Obs2 Flow2 Flow2.Hist

variable {L N : ℕ} [NeZero L]

/-- `U(1)` invariance of the `ab` component (Case (2)). -/
theorem isSym_ab_of_symSub {F : OE .two (Lam 2 L N)}
    (h : F ∈ (symSub : Subalgebra ℂ (OE .two (Lam 2 L N)))) : IsSym (F : SA .two (Lam 2 L N)).ab := by
  rw [isSym_iff_mem_SymS, mem_SymS]
  have h1 := congrArg SA.ab (mem_symSub.1 h : IsSymS (F : SA .two (Lam 2 L N)))
  simpa [scalS, Case.ca, Case.cb] using h1

/-- **The `ab` parts of `V^{obs}` lie in `𝒩({a,b})`.** -/
def ObsVabInv (P : ObsPts 2 L N) (o : ObsSt .two L N) : Prop :=
  ∀ b, (o.V b : SA .two (Lam 2 L N)).ab ∈ NX ({P.a, P.b} : Set (Lam 2 L N))

section Step

variable (R : RGPar 2 L N) (P : ObsPts 2 L N) {j : ℕ} {st : RawSt 2 L N} (g μ : ℝ)
  {D : Fam 2 L N} {K : Act 2 L N} {o : ObsSt .two L N}

theorem fullV_ab_mem (ho : ObsVabInv P o) (b : Fin 2 → ℕ) :
    (fullV R j st g μ o b : SA .two (Lam 2 L N)).ab ∈ NX ({P.a, P.b} : Set (Lam 2 L N)) := by
  show (((emb _ : OE .two (Lam 2 L N)) + o.V b : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).ab ∈ _
  rw [emb_add_ab]; exact ho b

/-- **`ObsVabInv` is preserved by one step.** -/
theorem obsVabInv_step (ho : ObsVabInv P o) : ObsVabInv P (obsStep R P j st g μ D K o) := by
  intro c'
  show (πobs (Vnext2O P j (stCov R j st) (fullV R j st g μ o) (fullW st D o) (fullK R j st K o) c') :
    SA .two (Lam 2 L N)).ab ∈ _
  rw [ab_πobs]
  exact Vnext2O_ab_mem_pair P j _ _ _ _ (fullV_ab_mem R P g μ ho) c'

end Step

section Hist

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N)

theorem obsVabInv_histFrom {j : ℕ} {o' : ObsSt .two L N} (h0 : ObsVabInv P o')
    (t : Hist.Seq (Xs R)) : ∀ k, ObsVabInv P (obsHistFrom R P j o' k t)
  | 0 => h0
  | k + 1 => by
    by_cases hk : k + 1 ≤ j
    · rw [obsHistFrom_le o' t hk]; exact h0
    · rw [obsHistFrom_succ (by omega)]
      exact obsVabInv_step R P _ _ (obsVabInv_histFrom h0 t k)

omit [Fact (0 < R.ℓ)] [Fact (0 < R.A)] in
theorem obsVabInv_redSt {j : ℕ} {st : RawSt 2 L N} {g μ : ℝ} {Dw : Fam 2 L N} {K : Act 2 L N}
    {o : ObsSt .two L N} {Dx : Finset (Lam 2 L N)} :
    ObsVabInv P (redSt R P j st g μ Dw K o Dx) := fun _ => by
  show ((0 : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).ab ∈ _
  exact zero_mem _

variable (j : ℕ) (o' : ObsSt .two L N) (t : Hist.Seq (Xs R))

/-- The `ab` part of `hVR` is that of the observable state. -/
theorem hVR_ab (k : ℕ) (b : Fin 2 → ℕ) :
    (hVR R P j o' t k b : SA .two (Lam 2 L N)).ab =
      ((obsHistFrom R P j o' k t).V b : SA .two (Lam 2 L N)).ab :=
  emb_add_ab _ _

theorem hVR_ab_mem (h0 : ObsVabInv P o') (k : ℕ) (b : Fin 2 → ℕ) :
    (hVR R P j o' t k b : SA .two (Lam 2 L N)).ab ∈ NX ({P.a, P.b} : Set (Lam 2 L N)) := by
  rw [hVR_ab]; exact obsVabInv_histFrom R P h0 t k b

theorem hVR_ab_sym {k : ℕ} (hs : ObsSymInv k (obsHistFrom R P j o' k t)) (b : Fin 2 → ℕ) :
    IsSym (hVR R P j o' t k b : SA .two (Lam 2 L N)).ab := by
  rw [hVR_ab]; exact isSym_ab_of_symSub (hs.V b)

/-- **The `m₂` Pauli defect along the reduced history**: `𝔡₂_k = M₄_k·m2Def(C_k)`. -/
theorem pdefM2_hVR_eq (h0 : ObsVabInv P o') {k : ℕ} (hs : ObsSymInv k (obsHistFrom R P j o' k t))
    (C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ) :
    pdefM2 k C (hVR R P j o' t k) =
      m4Tot P k (hVR R P j o' t k) * (C P.a P.a + C P.b P.b - C P.a P.b - C P.b P.a) :=
  pdefM2_eq_m4Tot P k C _ (hVR_ab_mem R P j o' t h0 k) (hVR_ab_sym R P j o' t hs)

/-- **The `ε` Pauli defect along the reduced history**: determinant defect of `M₄_k` plus the
gradient defects of the quadratic coefficients. -/
theorem pdefAB2_hVR_sub (h0 : ObsVabInv P o') {k : ℕ}
    (hs : ObsSymInv k (obsHistFrom R P j o' k t)) (C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ) :
    pdefAB2 P k C (hVR R P j o' t k) -
        m4Tot P k (hVR R P j o' t k) * (C P.a P.a * C P.b P.b - C P.a P.b * C P.b P.a) =
      ∑ b ∈ blockIdx (L := L) (N := N) k, ∑ u ∈ ({P.a, P.b} : Finset (Lam 2 L N)),
        ∑ v ∈ ({P.a, P.b} : Finset (Lam 2 L N)),
          cfAB2 u v (hVR R P j o' t k b : SA .two (Lam 2 L N)).ab * (C u v - C P.a P.a) :=
  pdefAB2_sub_m4Tot P k C _ (hVR_ab_mem R P j o' t h0 k) (hVR_ab_sym R P j o' t hs)

end Hist

end

end PtCorr2
