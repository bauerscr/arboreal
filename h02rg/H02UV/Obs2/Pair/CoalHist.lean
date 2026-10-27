import Obs2.Pair.Coal

/-!
# Lemma `lem:coal` along the observable flow (`Obs2.Flow.Hist`)

The invariant `ObsCoalInv P j o` of the observable state at scale `j` (`d = 2`):
* `V^{obs}_j(B)` has no `ab` component, its `σ_i` component is supported at the point `p_i`,
  and it has no `σ_i` if `B` is at distance `≥ L^j` from `p_i` (with the pointed `loc^a`,
  `V^{obs}_j(B)_a` can be nonzero on blocks `B ∌ a` near `a`);
* `𝒲^{obs}_j(B)` has no `ab` component, and no `σ_i` if `B` is at distance `≥ L^j` from `p_i`;
* `K^{obs}_j(X)` has no `ab` component for small `X`, and no `σ_i` on connected `X` at distance
  `≥ L^j` from `p_i`;
* the accumulated constant `u^{obs}_j` has no `ab` component.

## Results
* `coalHyp_of`: the invariant and the range of the step covariance give `CoalHyp` for the full
  inputs `V♭ + V^{obs}`, `𝒲 + 𝒲^{obs}`, `K♭ + K^{obs,♭}` of the extended step;
* `obsStep_coalInv`: the invariant is preserved by one step if `|a - b|_∞ ≥ L^{j+2}/2`;
* `obsStep_coal_last`: one more step (with only `|a - b|_∞ ≥ L^{j+1}/2`) keeps `V_{ab} = 0`,
  `u_{ab} = 0`;
* `coalInv_init`: the initial state `V^{obs}_0 = (u^{obs} + V^{obs})(B)` with vanishing `ab`
  couplings (`q = r = χ = 0`, and `η = 0` in Case 2), `𝒲 = K = 0`, `u = 0` satisfies it;
* **`obsHist_coal`** (Lemma `lem:coal`): along any history whose step covariances have range
  `L^{k+1}/2` for `k < j_ab`, `V^{obs}_{j,ab} = 0` and `u^{obs}_{j,ab} = 0` for all `j ≤ j_ab`;
* **`obsHist_coal_valid`**: the same with the range hypothesis discharged by `ValidAt`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 LocObs FRD

variable {L N : ℕ} [NeZero L] {c : Obs.Case}

/-- The coalescence invariant of the observable state at scale `j`. -/
structure ObsCoalInv (P : ObsPts 2 L N) (j : ℕ) (o : ObsSt c L N) : Prop where
  Vab : ∀ b, (o.V b : SA c (Lam 2 L N)).ab = 0
  Vpt : ∀ i b, cmp i (o.V b : SA c (Lam 2 L N)) ∈ NX ({P.pt i} : Set (Lam 2 L N))
  Vno : ∀ i b, FarS (L ^ j) (P.pt i) (blockSet (L := L) (N := N) j b) →
    o.V b ∈ noX c (Lam 2 L N) i
  Wab : ∀ b, (o.W b : SA c (Lam 2 L N)).ab = 0
  Wno : ∀ i b, FarS (L ^ j) (P.pt i) (blockSet (L := L) (N := N) j b) →
    o.W b ∈ noX c (Lam 2 L N) i
  Kab : ∀ X, IsSmall j X → (o.K X : SA c (Lam 2 L N)).ab = 0
  Kno : ∀ i X, IsConn j X → FarS (L ^ j) (P.pt i) X → o.K X ∈ noX c (Lam 2 L N) i
  uab : (o.u : SA c (Lam 2 L N)).ab = 0

section Full

theorem emb_add_ab {Λ : Type*} [DecidableEq Λ] (x : EvR Λ) (F : OE c Λ) :
    (((emb x : OE c Λ) + F : OE c Λ) : SA c Λ).ab = (F : SA c Λ).ab := by
  show 0 + (F : SA c Λ).ab = _; rw [zero_add]

theorem emb_add_cmp {Λ : Type*} [DecidableEq Λ] (i : Bool) (x : EvR Λ) (F : OE c Λ) :
    cmp i (((emb x : OE c Λ) + F : OE c Λ) : SA c Λ) = cmp i (F : SA c Λ) := by
  cases i <;> exact zero_add _

theorem emb_add_e {Λ : Type*} [DecidableEq Λ] (x : EvR Λ) (F : OE c Λ) :
    (((emb x : OE c Λ) + F : OE c Λ) : SA c Λ).e = (x : Grassmann.N Λ) + (F : SA c Λ).e := rfl

theorem emb_mul_ab {Λ : Type*} [DecidableEq Λ] (x : EvR Λ) (F : OE c Λ) :
    (((emb x : OE c Λ) * F : OE c Λ) : SA c Λ).ab = (x : Grassmann.N Λ) * (F : SA c Λ).ab := by
  show (ofN (x : Grassmann.N Λ) * (F : SA c Λ)).ab = _
  simp [mul_ab]

theorem e_eq_zero_of_bulk {Λ : Type*} [DecidableEq Λ] {F : OE c Λ} (h : bulk F = 0) :
    (F : SA c Λ).e = 0 := by
  have := congrArg Subtype.val h; simpa using this

variable (R : RGPar 2 L N) (P : ObsPts 2 L N) (j : ℕ) (st : RawSt 2 L N) (g μ : ℝ)
  (D : Fam 2 L N) (K : Act 2 L N) {o : ObsSt c L N}

/-- **The hypotheses of one step** from the invariant. -/
theorem coalHyp_of (hinv : ObsCoalInv P j o) (ho : o.IsObs) (hL : 2 ^ (2 + 3) + 8 * 2 < L)
    (hjN : j < N)
    (hC : ∀ x y, (L : ℝ) ^ (j + 1) / 2 ≤ supNorm (x - y) → stCov R j st x y = 0)
    (hab : (L : ℝ) ^ (j + 1) / 2 ≤ supNorm (P.a - P.b)) :
    CoalHyp P j (stCov R j st) (fullV R j st g μ o) (fullW st D o) (fullK R j st K o) where
  hL := by omega
  hC := hC
  hab := hab
  hVe b := by
    show (((emb (stVf R j st g μ b) : OE c (Lam 2 L N)) + o.V b : OE c (Lam 2 L N)) :
      SA c (Lam 2 L N)).e ∈ _
    rw [emb_add_e, e_eq_zero_of_bulk (ho.V b), add_zero]
    exact (inF_VfamL (d := 2) (L := L) (N := N) (by norm_num) hL hjN _).loc b
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

theorem piobs_cmp {Λ : Type*} [DecidableEq Λ] (i : Bool) (F : OE c Λ) :
    cmp i (πobs F : SA c Λ) = cmp i (F : SA c Λ) := cmp_πobs i F

theorem piobs_ab {Λ : Type*} [DecidableEq Λ] (F : OE c Λ) :
    (πobs F : SA c Λ).ab = (F : SA c Λ).ab := ab_πobs F

/-- **The invariant is preserved** below the coalescence scale. -/
theorem obsStep_coalInv (hinv : ObsCoalInv P j o) (ho : o.IsObs) (hL : 2 ^ (2 + 3) + 8 * 2 < L)
    (hjN : j < N)
    (hC : ∀ x y, (L : ℝ) ^ (j + 1) / 2 ≤ supNorm (x - y) → stCov R j st x y = 0)
    (hab' : (L : ℝ) ^ (j + 1 + 1) / 2 ≤ supNorm (P.a - P.b)) :
    ObsCoalInv P (j + 1) (obsStep R P j st g μ D K o) := by
  have hL0 : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
  have hab : (L : ℝ) ^ (j + 1) / 2 ≤ supNorm (P.a - P.b) := by
    refine le_trans ?_ hab'
    have : (L : ℝ) ^ (j + 1) ≤ (L : ℝ) ^ (j + 1 + 1) := pow_le_pow_right₀ hL0 (by omega)
    linarith
  have H := coalHyp_of R P j st g μ D K hinv ho hL hjN hC hab
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

/-- **The last step before coalescence** keeps `V_{ab} = 0` and `u_{ab} = 0`. -/
theorem obsStep_coal_last (hinv : ObsCoalInv P j o) (ho : o.IsObs)
    (hL : 2 ^ (2 + 3) + 8 * 2 < L) (hjN : j < N)
    (hC : ∀ x y, (L : ℝ) ^ (j + 1) / 2 ≤ supNorm (x - y) → stCov R j st x y = 0)
    (hab : (L : ℝ) ^ (j + 1) / 2 ≤ supNorm (P.a - P.b)) :
    (∀ c', ((obsStep R P j st g μ D K o).V c' : SA c (Lam 2 L N)).ab = 0) ∧
      ((obsStep R P j st g μ D K o).u : SA c (Lam 2 L N)).ab = 0 := by
  have H := coalHyp_of R P j st g μ D K hinv ho hL hjN hC hab
  refine ⟨fun c' => ?_, ?_⟩
  · show (πobs (Vnext2O P j (stCov R j st) (fullV R j st g μ o) (fullW st D o)
      (fullK R j st K o) c') : SA c (Lam 2 L N)).ab = 0
    rw [piobs_ab]; exact H.Vnext_ab c'
  · show (o.u : SA c (Lam 2 L N)).ab + (uObsTot P j (stCov R j st) (fullV R j st g μ o)
      (fullW st D o) (fullK R j st K o) : SA c (Lam 2 L N)).ab = 0
    rw [hinv.uab, zero_add]; exact H.uObsTot_ab

end Full

/-! ### The initial state -/

section Init

/-- The `ab` couplings vanish: `q = r = χ = 0` (and `η = 0` in Case (2)). -/
def AbFree : (c : Obs.Case) → OCoup c → Prop
  | .one, V => OCoup1.q V = 0 ∧ OCoup1.r V = 0 ∧ OCoup1.chi V = 0
  | .two, V => OCoup2.q V = 0 ∧ OCoup2.eta V = 0 ∧ OCoup2.r V = 0 ∧ OCoup2.chi V = 0

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

theorem evalO_ab (c : Obs.Case) {V : OCoup c} (hV : AbFree c V) (a b : Λ) (X : Finset Λ) :
    (evalO c V a b X : SA c Λ).ab = 0 := by
  cases c
  · obtain ⟨h1, h2, h3⟩ := hV
    show (OCoup1.evalS V a b X).ab = 0
    simp [OCoup1.evalS, h1, h2, h3]
  · obtain ⟨h1, h2, h3, h4⟩ := hV
    show (OCoup2.evalS V a b X).ab = 0
    simp [OCoup2.evalS, h1, h2, h3, h4]

theorem evalO_cmp (c : Obs.Case) (V : OCoup c) (a b : Λ) (X : Finset Λ) (i : Bool) :
    cmp i (evalO c V a b X : SA c Λ) ∈ NX ({if i then a else b} : Set Λ) := by
  have ha : ψ (a, -1) ∈ NX ({a} : Set Λ) := ψ_mem_NX (by simp)
  have ha' : ψ (a, 1) ∈ NX ({a} : Set Λ) := ψ_mem_NX (by simp)
  have hb : ψ (b, -1) ∈ NX ({b} : Set Λ) := ψ_mem_NX (by simp)
  have hb' : ψ (b, 1) ∈ NX ({b} : Set Λ) := ψ_mem_NX (by simp)
  cases c <;> cases i
  · show ind (b ∈ X) • (OCoup1.mub V • psi b) ∈ _
    exact Subalgebra.smul_mem _ (Subalgebra.smul_mem _ hb' _) _
  · show ind (a ∈ X) • (-OCoup1.mua V • psibar a) ∈ _
    exact Subalgebra.smul_mem _ (Subalgebra.smul_mem _ ha _) _
  · show ind (b ∈ X) • (algebraMap ℂ (Grassmann.N Λ) (-OCoup2.gb V) -
      OCoup2.mub V • (psibar b * psi b)) ∈ _
    exact Subalgebra.smul_mem _ (sub_mem (Subalgebra.algebraMap_mem _ _)
      (Subalgebra.smul_mem _ (mul_mem hb hb') _)) _
  · show ind (a ∈ X) • (algebraMap ℂ (Grassmann.N Λ) (-OCoup2.ga V) -
      OCoup2.mua V • (psibar a * psi a)) ∈ _
    exact Subalgebra.smul_mem _ (sub_mem (Subalgebra.algebraMap_mem _ _)
      (Subalgebra.smul_mem _ (mul_mem ha ha') _)) _

theorem evalO_noX (c : Obs.Case) {V : OCoup c} (hV : AbFree c V) (a b : Λ) (X : Finset Λ)
    (i : Bool) (h : (if i then a else b) ∉ X) : evalO c V a b X ∈ noX c Λ i := by
  refine mem_noX.2 ⟨?_, evalO_ab c hV a b X⟩
  cases c <;> cases i <;> simp only [Bool.false_eq_true, if_false, if_true] at h
  · show ind (b ∈ X) • (OCoup1.mub V • psi b) = 0
    rw [ind_neg h, zero_smul]
  · show ind (a ∈ X) • (-OCoup1.mua V • psibar a) = 0
    rw [ind_neg h, zero_smul]
  · show ind (b ∈ X) • (algebraMap ℂ (Grassmann.N Λ) (-OCoup2.gb V) -
      OCoup2.mub V • (psibar b * psi b)) = 0
    rw [ind_neg h, zero_smul]
  · show ind (a ∈ X) • (algebraMap ℂ (Grassmann.N Λ) (-OCoup2.ga V) -
      OCoup2.mua V • (psibar a * psi a)) = 0
    rw [ind_neg h, zero_smul]

/-- The initial observable state: `V^{obs}_0(B) = (u^{obs} + V^{obs})(B)`, `𝒲 = K = u = 0`. -/
def obsInit (c : Obs.Case) (V : OCoup c) (P : ObsPts 2 L N) : ObsSt c L N :=
  ⟨evalFam c V P.a P.b 0, 0, 0, 0⟩

theorem obsInit_isObs (c : Obs.Case) (V : OCoup c) (P : ObsPts 2 L N) :
    (obsInit c V P).IsObs where
  V b := bulk_evalO c V _ _ _
  W _ := map_zero _
  K _ := map_zero _
  u := map_zero _

theorem pt_eq (P : ObsPts 2 L N) (i : Bool) : (if i then P.a else P.b) = P.pt i := by
  cases i <;> rfl

/-- **The initial state satisfies the invariant** if the `ab` couplings vanish. -/
theorem coalInv_init (c : Obs.Case) {V : OCoup c} (hV : AbFree c V) (P : ObsPts 2 L N) :
    ObsCoalInv P 0 (obsInit c V P) where
  Vab b := evalO_ab c hV _ _ _
  Vpt i b := by
    have := evalO_cmp c V P.a P.b (blockSet (L := L) (N := N) 0 b) i
    rwa [pt_eq] at this
  Vno i b h := evalO_noX c hV _ _ _ i (by
    rw [pt_eq]; exact not_mem_of_farS (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) 0) h)
  Wab _ := rfl
  Wno _ _ _ := zero_mem _
  Kab _ _ := rfl
  Kno _ _ _ _ := zero_mem _
  uab := rfl

end Init

/-! ### Along the history -/

section Hist

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N)
  (o₀ : ObsSt c L N)

/-- **Lemma `lem:coal`**: if the step covariances `C'_{k+1}` of the history have range
`L^{k+1}/2` for `k < j_ab`, then for every `j ≤ j_ab = coal L a b` the `ab` components of
`V^{obs}_j(B)` and of the accumulated observable constant `u^{obs}_j` vanish (the couplings
`q_j, η_j, r_j, χ_j`). -/
theorem obsHist_coal (h₀ : o₀.IsObs) (hinv₀ : ObsCoalInv P 0 o₀)
    (hL : 2 ^ (2 + 3) + 8 * 2 < L) (hcN : coal L P.a P.b ≤ N) (t : Flow2.Hist.Seq (Xs R))
    (hC : ∀ k < coal L P.a P.b, ∀ x y, (L : ℝ) ^ (k + 1) / 2 ≤ supNorm (x - y) →
      stCov R k (rawHist R k t) x y = 0) :
    ∀ j ≤ coal L P.a P.b, (∀ B, ((obsHist R P o₀ j t).V B : SA c (Lam 2 L N)).ab = 0) ∧
      ((obsHist R P o₀ j t).u : SA c (Lam 2 L N)).ab = 0 := by
  have inv : ∀ j, j < coal L P.a P.b → ObsCoalInv P j (obsHist R P o₀ j t) := by
    intro j
    induction j with
    | zero => intro _; exact hinv₀
    | succ k ih =>
      intro hk
      rw [obsHist_succ]
      exact obsStep_coalInv R P k _ _ _ _ _ (ih (by omega))
        (obsHist_isObs R P o₀ h₀ k t) hL (by omega) (hC k (by omega)) (pow_le_of_lt_coal hk)
  intro j hj
  rcases Nat.lt_or_ge j (coal L P.a P.b) with hlt | hge
  · exact ⟨(inv j hlt).Vab, (inv j hlt).uab⟩
  · obtain rfl : j = coal L P.a P.b := le_antisymm hj hge
    rcases Nat.eq_zero_or_pos (coal L P.a P.b) with h0 | hpos
    · rw [h0]; exact ⟨hinv₀.Vab, hinv₀.uab⟩
    · obtain ⟨k, hk⟩ : ∃ k, coal L P.a P.b = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
      rw [hk, obsHist_succ]
      exact obsStep_coal_last R P k _ _ _ _ _ (inv k (by omega)) (obsHist_isObs R P o₀ h₀ k t) hL
        (by omega) (hC k (by omega)) (pow_le_of_lt_coal (by omega))

/-- **Lemma `lem:coal`** with the range of the covariances from the validity of the parameters
(`ValidAt R k` for `k < j_ab`, which includes `k + 2 < N`). -/
theorem obsHist_coal_valid (h₀ : o₀.IsObs) (hinv₀ : ObsCoalInv P 0 o₀)
    (hL : 2 ^ (2 + 3) + 8 * 2 < L) (hρ : 0 ≤ R.ρ)
    (hV : ∀ k < coal L P.a P.b, ValidAt R k) (t : Flow2.Hist.Seq (Xs R)) :
    ∀ j ≤ coal L P.a P.b, (∀ B, ((obsHist R P o₀ j t).V B : SA c (Lam 2 L N)).ab = 0) ∧
      ((obsHist R P o₀ j t).u : SA c (Lam 2 L N)).ab = 0 := by
  rcases Nat.eq_zero_or_pos (coal L P.a P.b) with h0 | hpos
  · intro j hj
    have : j = 0 := by omega
    subst this; exact ⟨hinv₀.Vab, hinv₀.uab⟩
  have hcN : coal L P.a P.b ≤ N := by
    have := (hV (coal L P.a P.b - 1) (by omega)).1; omega
  refine obsHist_coal R P o₀ h₀ hinv₀ hL hcN t fun k hk x y hxy => ?_
  have hVk := hV k hk
  have hI := rawInv_hist R hρ k (fun i hi => hV i (by omega)) t
  exact (RawInv.cov hVk hI).1.range (by have := hVk.1; omega) x y hxy

end Hist

end

end Obs2
