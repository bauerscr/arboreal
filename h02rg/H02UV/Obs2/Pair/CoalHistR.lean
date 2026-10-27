import Obs2.Pair.CoalHist
import Obs2.Pair.CoalR

/-!
# The relaxed coalescence invariant along the observable flow

`ObsCoalInvR P j ρ o` is `ObsCoalInv P j o` with the `σ_i`-freeness clauses at sup-distance
`≥ L^j + ρ` from `p_i` (`Obs2/Pair/CoalR`). It is the invariant of a relocated state (Loc point moved by
`≤ ρ`), and it propagates through the step exactly as `ObsCoalInv` as long as `ρ ≤ L^j`.

* `ObsCoalInv.toR`: the strict invariant implies the relaxed one (any `ρ`);
* `coalHyp_ofR`: the invariant and the range of the step covariance give `CoalHypR`;
* **`obsStep_coalInvR`**: preserved by one step if `|a − b|_∞ ≥ L^{j+2}/2`, `ρ ≤ L^j`;
* **`obsStep_coal_lastR`**: one more step keeps `V_{ab} = 0`, `u_{ab} = 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 LocObs FRD

variable {L N : ℕ} [NeZero L] {c : Obs.Case}

/-- **The relaxed coalescence invariant** (radius `L^j + ρ`). -/
structure ObsCoalInvR (P : ObsPts 2 L N) (j ρ : ℕ) (o : ObsSt c L N) : Prop where
  Vab : ∀ b, (o.V b : SA c (Lam 2 L N)).ab = 0
  Vpt : ∀ i b, cmp i (o.V b : SA c (Lam 2 L N)) ∈ NX ({P.pt i} : Set (Lam 2 L N))
  Vno : ∀ i b, FarS (L ^ j + ρ) (P.pt i) (blockSet (L := L) (N := N) j b) →
    o.V b ∈ noX c (Lam 2 L N) i
  Wab : ∀ b, (o.W b : SA c (Lam 2 L N)).ab = 0
  Wno : ∀ i b, FarS (L ^ j + ρ) (P.pt i) (blockSet (L := L) (N := N) j b) →
    o.W b ∈ noX c (Lam 2 L N) i
  Kab : ∀ X, IsSmall j X → (o.K X : SA c (Lam 2 L N)).ab = 0
  Kno : ∀ i X, IsConn j X → FarS (L ^ j + ρ) (P.pt i) X → o.K X ∈ noX c (Lam 2 L N) i
  uab : (o.u : SA c (Lam 2 L N)).ab = 0

/-- The strict invariant implies the relaxed one. -/
theorem ObsCoalInv.toR {P : ObsPts 2 L N} {j : ℕ} {o : ObsSt c L N} (h : ObsCoalInv P j o)
    (ρ : ℕ) : ObsCoalInvR P j ρ o where
  Vab := h.Vab
  Vpt := h.Vpt
  Vno i b hf := h.Vno i b (farS_mono (Nat.le_add_right _ ρ) hf subset_rfl)
  Wab := h.Wab
  Wno i b hf := h.Wno i b (farS_mono (Nat.le_add_right _ ρ) hf subset_rfl)
  Kab := h.Kab
  Kno i X hX hf := h.Kno i X hX (farS_mono (Nat.le_add_right _ ρ) hf subset_rfl)
  uab := h.uab

variable (R : RGPar 2 L N) (P : ObsPts 2 L N) (j ρ : ℕ) (st : RawSt 2 L N) (g μ : ℝ)
  (D : Fam 2 L N) (K : Act 2 L N) {o : ObsSt c L N}

/-- **The hypotheses of one step** from the relaxed invariant. -/
theorem coalHyp_ofR (hinv : ObsCoalInvR P j ρ o) (ho : o.IsObs) (hL : 2 ^ (2 + 3) + 8 * 2 < L)
    (hjN : j < N) (hρ : ρ ≤ L ^ j)
    (hC : ∀ x y, (L : ℝ) ^ (j + 1) / 2 ≤ supNorm (x - y) → stCov R j st x y = 0)
    (hab : (L : ℝ) ^ (j + 1) / 2 ≤ supNorm (P.a - P.b)) :
    CoalHypR P j ρ (stCov R j st) (fullV R j st g μ o) (fullW st D o) (fullK R j st K o) where
  hL := by omega
  hC := hC
  hab := hab
  hVe b := by
    show (((emb (stVf R j st g μ b) : OE c (Lam 2 L N)) + o.V b : OE c (Lam 2 L N)) :
      SA c (Lam 2 L N)).e ∈ _
    rw [emb_add_e, e_eq_zero_of_bulk (ho.V b), add_zero]
    exact (inF_VfamL (d := 2) (L := L) (N := N) (by norm_num) (by omega) hjN _).loc b
  hVpt i b := by
    show cmp i (((emb (stVf R j st g μ b) : OE c (Lam 2 L N)) + o.V b : OE c (Lam 2 L N)) :
      SA c (Lam 2 L N)) ∈ _
    rw [emb_add_cmp]; exact hinv.Vpt i b
  hVab b := by
    show (((emb (stVf R j st g μ b) : OE c (Lam 2 L N)) + o.V b : OE c (Lam 2 L N)) :
      SA c (Lam 2 L N)).ab = 0
    rw [emb_add_ab]; exact hinv.Vab b
  hVno i b h := add_mem (emb_mem_noX i _) (hinv.Vno i b h)
  hWab b := by
    show (((emb ((st.Wl + D) b) : OE c (Lam 2 L N)) + o.W b : OE c (Lam 2 L N)) :
      SA c (Lam 2 L N)).ab = 0
    rw [emb_add_ab]; exact hinv.Wab b
  hWno i b h := add_mem (emb_mem_noX i _) (hinv.Wno i b h)
  hKab X hX := by
    show (((emb (bpow j (fun b => gexp (stDelta R j st b)) X) : OE c (Lam 2 L N)) *
      ((emb (K X) : OE c (Lam 2 L N)) + o.K X) : OE c (Lam 2 L N)) : SA c (Lam 2 L N)).ab = 0
    rw [emb_mul_ab, emb_add_ab, hinv.Kab X hX, mul_zero]
  hKno i X hX h := mul_mem (emb_mem_noX i _) (add_mem (emb_mem_noX i _) (hinv.Kno i X hX h))
  hρ := hρ
  hL4 := by norm_num; omega

/-- **The relaxed invariant is preserved** below the coalescence scale (`ρ ≤ L^j`). -/
theorem obsStep_coalInvR (hinv : ObsCoalInvR P j ρ o) (ho : o.IsObs)
    (hL : 2 ^ (2 + 3) + 8 * 2 < L) (hjN : j < N) (hρ : ρ ≤ L ^ j)
    (hC : ∀ x y, (L : ℝ) ^ (j + 1) / 2 ≤ supNorm (x - y) → stCov R j st x y = 0)
    (hab' : (L : ℝ) ^ (j + 1 + 1) / 2 ≤ supNorm (P.a - P.b)) :
    ObsCoalInvR P (j + 1) ρ (obsStep R P j st g μ D K o) := by
  have hL0 : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
  have hab : (L : ℝ) ^ (j + 1) / 2 ≤ supNorm (P.a - P.b) := by
    refine le_trans ?_ hab'
    have : (L : ℝ) ^ (j + 1) ≤ (L : ℝ) ^ (j + 1 + 1) := pow_le_pow_right₀ hL0 (by omega)
    linarith
  have H := coalHyp_ofR R P j ρ st g μ D K hinv ho hL hjN hρ hC hab
  exact
  { Vab := fun c' => by
      show (πobs (Vnext2O P j (stCov R j st) (fullV R j st g μ o) (fullW st D o)
        (fullK R j st K o) c') : SA c (Lam 2 L N)).ab = 0
      rw [piobs_ab]; exact H.Vnext_ab c'
    Vpt := fun i c' => by
      show cmp i (πobs (Vnext2O P j (stCov R j st) (fullV R j st g μ o) (fullW st D o)
        (fullK R j st K o) c') : SA c (Lam 2 L N)) ∈ _
      rw [piobs_cmp]; exact H.Vnext_pt i c'
    Vno := fun i c' h => πobs_mem_noX (H.Vnext_noX h)
    Wab := fun c' => by
      show (πobs (Wnext2O P j (stCov R j st) (fullV R j st g μ o) (fullW st D o) c') :
        SA c (Lam 2 L N)).ab = 0
      rw [piobs_ab]; exact H.Wnext_ab hab' c'
    Wno := fun i c' h => πobs_mem_noX (H.Wnext_noX h)
    Kab := fun X hX => by
      show (πobs (KconnO (j + 1) (KplusO P j (stCov R j st) (fullV R j st g μ o) (fullW st D o)
        (fullK R j st K o)) X) : SA c (Lam 2 L N)).ab = 0
      rw [piobs_ab, KconnO, if_pos ⟨hX.1, hX.2.1⟩]
      exact H.Kplus_ab hab' hX
    Kno := fun i X hX h => by
      refine πobs_mem_noX ?_
      unfold KconnO
      rw [if_pos hX]
      exact H.Kplus_noX hX.1 h
    uab := by
      show (o.u : SA c (Lam 2 L N)).ab + (uObsTot P j (stCov R j st) (fullV R j st g μ o)
        (fullW st D o) (fullK R j st K o) : SA c (Lam 2 L N)).ab = 0
      rw [hinv.uab, zero_add]; exact H.uObsTot_ab }

/-- **The last step before coalescence** keeps `V_{ab} = 0` and `u_{ab} = 0` (relaxed). -/
theorem obsStep_coal_lastR (hinv : ObsCoalInvR P j ρ o) (ho : o.IsObs)
    (hL : 2 ^ (2 + 3) + 8 * 2 < L) (hjN : j < N) (hρ : ρ ≤ L ^ j)
    (hC : ∀ x y, (L : ℝ) ^ (j + 1) / 2 ≤ supNorm (x - y) → stCov R j st x y = 0)
    (hab : (L : ℝ) ^ (j + 1) / 2 ≤ supNorm (P.a - P.b)) :
    (∀ c', ((obsStep R P j st g μ D K o).V c' : SA c (Lam 2 L N)).ab = 0) ∧
      ((obsStep R P j st g μ D K o).u : SA c (Lam 2 L N)).ab = 0 := by
  have H := coalHyp_ofR R P j ρ st g μ D K hinv ho hL hjN hρ hC hab
  refine ⟨fun c' => ?_, ?_⟩
  · show (πobs (Vnext2O P j (stCov R j st) (fullV R j st g μ o) (fullW st D o)
      (fullK R j st K o) c') : SA c (Lam 2 L N)).ab = 0
    rw [piobs_ab]; exact H.Vnext_ab c'
  · show (o.u : SA c (Lam 2 L N)).ab + (uObsTot P j (stCov R j st) (fullV R j st g μ o)
      (fullW st D o) (fullK R j st K o) : SA c (Lam 2 L N)).ab = 0
    rw [hinv.uab, zero_add]; exact H.uObsTot_ab

end

end Obs2
