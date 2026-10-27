import Obs2.Map.Map
import Obs2.Map.Supp
import Obs.Norm

/-!
# Norms with sources for the second-order map (complex covariance)

The observable norm `‖F‖ = ‖F_∅‖ + w_a ‖F_a‖ + w_b ‖F_b‖ + w_ab ‖F_ab‖` (`Obs.oNorm`, `Obs.oTj`)
with **arbitrary weights** `w` satisfying `w_ab ≤ w_a w_b` (`Wt.Sub`) is submultiplicative on even
elements (`Obs.oT_mul_le`). All primitives of `Obs2.Map.Map` act componentwise except products, so
the Step2 bounds lift component by component:

* `oTj_EthO_le2`: `‖𝔼_Cθ F‖_{T_{j+1}(ℓ')} ≤ q^{|𝓑_j(Y)|} ‖F‖_{T_j(ℓ)}` for `F` with all components
  in `𝒩(Y)` (Lemma `lem:pauli` and the two-scale expectation bound `Step2.EthE_succ_le2`);
* `oTj_EthO_le2'`: `‖𝔼_Cθ F‖_{T_{j+1}(ℓ')} ≤ ‖F‖_{T_{j+1}(2ℓ)}`; `oTj_succ_two_le` (Pauli);
* `oTj_FCO_le`: `‖F_C(𝔼θA, 𝔼θB)‖_{T_{j+1}(ℓ')} ≤ 2 ‖A‖_{T_{j+1}(2ℓ)} ‖B‖_{T_{j+1}(2ℓ)}`;
* `exists_LocO2_bound`: `‖Loc_{X,Y} F‖_{T_j(ℓ)} ≤ C ‖F‖_{T_j(ℓ)}` for `X` small, `Y ⊆ X` (bulk
  `Loc^{(2)} + Loc^{(4)}`, `loc^a`, `loc^b`, barycentric `loc^{ab}`).

## The observable part
`oTo w j ℓ F = ‖π_obs F‖` is the observable part of the norm, `‖F‖ = ‖F_∅‖ + ‖π_obs F‖`
(`oTj_eq_bulk_add`). Since `π_obs(FG) = F_∅ G^{obs} + F^{obs} G` (`πobs_mul`), the products obey
`‖π_obs(FG)‖ ≤ ‖F_∅‖ ‖π_obs G‖ + ‖π_obs F‖ (‖G_∅‖ + ‖π_obs G‖)` (`oTo_mul_le`); this is the
form in which the observable flow is linear in the observable data (the last term only feeds the
`ab` component).

The weights are free parameters: e.g. `(λ w_a, λ w_b, λ² w_ab)` (`Wt.scale`) rescales the source
fields (`σ ↦ λ σ`), and `w_ab = 0` (`Wt.single`) projects to the single-source parts.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step FRD ENNReal

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

/-! ### Weights -/

/-- The rescaled weights `(λ w_a, λ w_b, λ² w_ab)` (rescaling of the sources by `λ`). -/
def Wt.scale (lam : ℝ≥0∞) (w : Wt) : Wt := ⟨lam * w.a, lam * w.b, lam ^ 2 * w.ab⟩

theorem Wt.scale_sub {w : Wt} (hw : w.Sub) (lam : ℝ≥0∞) : (Wt.scale lam w).Sub := by
  unfold Wt.Sub Wt.scale
  simp only
  calc lam ^ 2 * w.ab ≤ lam ^ 2 * (w.a * w.b) := by gcongr; exact hw
    _ = lam * w.a * (lam * w.b) := by ring

/-! ### Componentwise comparison -/

/-- The bulk and single-source components vanish. -/
structure EabZero {Λ : Type*} (F : SA c Λ) : Prop where
  e : F.e = 0
  a : F.a = 0
  b : F.b = 0


theorem oNorm_le_cmp {Λ Λ' : Type*} {nrm : Grassmann.N Λ → ℝ≥0∞}
    {nrm' : Grassmann.N Λ' → ℝ≥0∞} {w : Wt} {F : SA c Λ} {G : SA c Λ'} {K : ℝ≥0∞}
    (he : nrm' G.e ≤ K * nrm F.e) (ha : nrm' G.a ≤ K * nrm F.a) (hb : nrm' G.b ≤ K * nrm F.b)
    (hab : nrm' G.ab ≤ K * nrm F.ab) : oNorm nrm' w G ≤ K * oNorm nrm w F := by
  unfold oNorm
  calc nrm' G.e + w.a * nrm' G.a + w.b * nrm' G.b + w.ab * nrm' G.ab
      ≤ K * nrm F.e + w.a * (K * nrm F.a) + w.b * (K * nrm F.b) + w.ab * (K * nrm F.ab) := by
        gcongr
    _ = K * (nrm F.e + w.a * nrm F.a + w.b * nrm F.b + w.ab * nrm F.ab) := by ring

/-- Componentwise comparison for single-source weights (`w_ab = 0`). -/
theorem oNorm_le_cmp3 {Λ Λ' : Type*} {nrm : Grassmann.N Λ → ℝ≥0∞}
    {nrm' : Grassmann.N Λ' → ℝ≥0∞} {w : Wt} (hw0 : w.ab = 0) {F : SA c Λ} {G : SA c Λ'}
    {K : ℝ≥0∞} (he : nrm' G.e ≤ K * nrm F.e) (ha : nrm' G.a ≤ K * nrm F.a)
    (hb : nrm' G.b ≤ K * nrm F.b) : oNorm nrm' w G ≤ K * oNorm nrm w F := by
  unfold oNorm
  rw [hw0, zero_mul, zero_mul, add_zero, add_zero]
  calc nrm' G.e + w.a * nrm' G.a + w.b * nrm' G.b
      ≤ K * nrm F.e + w.a * (K * nrm F.a) + w.b * (K * nrm F.b) := by gcongr
    _ = K * (nrm F.e + w.a * nrm F.a + w.b * nrm F.b) := by ring

theorem oNorm_eq_zero_of_eab {Λ : Type*} {nrm : Grassmann.N Λ → ℝ≥0∞} (hn : nrm 0 = 0) {w : Wt}
    (hw0 : w.ab = 0) {F : SA c Λ} (hF : EabZero F) : oNorm nrm w F = 0 := by
  unfold oNorm; rw [hF.e, hF.a, hF.b, hw0, hn]; simp

theorem oNorm_le_cmp' {Λ Λ' : Type*} {nrm : Grassmann.N Λ → ℝ≥0∞}
    {nrm' : Grassmann.N Λ' → ℝ≥0∞} {w : Wt} {F : SA c Λ} {G : SA c Λ'}
    (he : nrm' G.e ≤ nrm F.e) (ha : nrm' G.a ≤ nrm F.a) (hb : nrm' G.b ≤ nrm F.b)
    (hab : nrm' G.ab ≤ nrm F.ab) : oNorm nrm' w G ≤ oNorm nrm w F := by
  unfold oNorm; gcongr

/-! ### Components of the primitives -/

@[simp] theorem EthO_e (C : Matrix (Lam d L N) (Lam d L N) ℂ) (F : OE c (Lam d L N)) :
    (EthO C F : SA c (Lam d L N)).e = ECC C (theta (F : SA c (Lam d L N)).e) := rfl
@[simp] theorem EthO_a (C : Matrix (Lam d L N) (Lam d L N) ℂ) (F : OE c (Lam d L N)) :
    (EthO C F : SA c (Lam d L N)).a = ECC C (theta (F : SA c (Lam d L N)).a) := rfl
@[simp] theorem EthO_b (C : Matrix (Lam d L N) (Lam d L N) ℂ) (F : OE c (Lam d L N)) :
    (EthO C F : SA c (Lam d L N)).b = ECC C (theta (F : SA c (Lam d L N)).b) := rfl
@[simp] theorem EthO_ab (C : Matrix (Lam d L N) (Lam d L N) ℂ) (F : OE c (Lam d L N)) :
    (EthO C F : SA c (Lam d L N)).ab = ECC C (theta (F : SA c (Lam d L N)).ab) := rfl

/-! ### Locality of all components -/

/-- The bulk and the single-source components of `F` lie in `𝒩(S)` (the `ab` component is not
required to be local: the barycentric `loc^{ab}` produces `ψ_b` at the far point). -/
structure CmpIn {Λ : Type*} [DecidableEq Λ] (S : Set Λ) (F : SA c Λ) : Prop where
  e : F.e ∈ NX S
  a : F.a ∈ NX S
  b : F.b ∈ NX S

section CmpIn

variable {Λ : Type*} [DecidableEq Λ] {S : Set Λ}

theorem CmpIn.mono {S' : Set Λ} (h : S ⊆ S') {F : SA c Λ} (hF : CmpIn S F) : CmpIn S' F :=
  ⟨NX_mono h hF.e, NX_mono h hF.a, NX_mono h hF.b⟩

theorem CmpIn.zero : CmpIn S (0 : SA c Λ) := ⟨zero_mem _, zero_mem _, zero_mem _⟩

theorem CmpIn.add {F G : SA c Λ} (hF : CmpIn S F) (hG : CmpIn S G) : CmpIn S (F + G) :=
  ⟨add_mem hF.e hG.e, add_mem hF.a hG.a, add_mem hF.b hG.b⟩

theorem CmpIn.neg {F : SA c Λ} (hF : CmpIn S F) : CmpIn S (-F) :=
  ⟨neg_mem hF.e, neg_mem hF.a, neg_mem hF.b⟩

theorem CmpIn.sub {F G : SA c Λ} (hF : CmpIn S F) (hG : CmpIn S G) : CmpIn S (F - G) :=
  ⟨sub_mem hF.e hG.e, sub_mem hF.a hG.a, sub_mem hF.b hG.b⟩

theorem CmpIn.smul (r : ℂ) {F : SA c Λ} (hF : CmpIn S F) : CmpIn S (r • F) :=
  ⟨Subalgebra.smul_mem _ hF.e r, Subalgebra.smul_mem _ hF.a r, Subalgebra.smul_mem _ hF.b r⟩

theorem CmpIn.sum {ι : Type*} (s : Finset ι) {F : ι → SA c Λ} (hF : ∀ i ∈ s, CmpIn S (F i)) :
    CmpIn S (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (CmpIn.zero (c := c) (S := S))
  | insert i s hi ih =>
    rw [sum_insert hi]
    exact (hF i (mem_insert_self i s)).add (ih fun k hk => hF k (mem_insert_of_mem hk))

theorem tau_mem_NX {x : Grassmann.N Λ} (hx : x ∈ NX S) : c.tau x ∈ NX S := by
  cases c
  · exact inv'_mem_NX hx
  · exact hx

theorem CmpIn.mul {F G : SA c Λ} (hF : CmpIn S F) (hG : CmpIn S G) : CmpIn S (F * G) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [mul_e]; exact mul_mem hF.e hG.e
  · rw [mul_a]; exact add_mem (mul_mem (tau_mem_NX hF.e) hG.a) (mul_mem hF.a hG.e)
  · rw [mul_b]; exact add_mem (mul_mem (tau_mem_NX hF.e) hG.b) (mul_mem hF.b hG.e)

theorem CmpIn.one : CmpIn S (1 : SA c Λ) :=
  ⟨one_mem _, zero_mem _, zero_mem _⟩

end CmpIn

/-! ### Locality of the primitives -/

section Prim

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ] {S : Set Λ}

theorem CmpIn.expS (C : Matrix Λ Λ ℂ) {F : SA c Λ} (hF : CmpIn S F) : CmpIn S (expS C F) :=
  ⟨expLC_mem_NX C hF.e, expLC_mem_NX C hF.a, expLC_mem_NX C hF.b⟩

theorem CmpIn.EthO (C : Matrix Λ Λ ℂ) {F : OE c Λ} (hF : CmpIn S (F : SA c Λ)) :
    CmpIn S (EthO C F : SA c Λ) := by
  rw [EthO_eq_expO, coe_expO]; exact hF.expS C

theorem CmpIn.FCO (C : Matrix Λ Λ ℂ) {A B : OE c Λ} (hA : CmpIn S (A : SA c Λ))
    (hB : CmpIn S (B : SA c Λ)) : CmpIn S (FCO C A B : SA c Λ) := by
  rw [coe_FCO]; exact (((hA.expS (-C)).mul (hB.expS (-C))).expS C).sub (hA.mul hB)

theorem CmpIn.πe {F : OE c Λ} (hF : CmpIn S (F : SA c Λ)) :
    CmpIn S ((emb (bulk F) : OE c Λ) : SA c Λ) :=
  ⟨hF.e, zero_mem _, zero_mem _⟩

theorem CmpIn.πobs {F : OE c Λ} (hF : CmpIn S (F : SA c Λ)) : CmpIn S (πobs F : SA c Λ) := by
  rw [coe_πobs, piobs_apply]; exact ⟨zero_mem _, hF.a, hF.b⟩

/-- `C` vanishes between `S` and `T`. -/
def CovSep (C : Matrix Λ Λ ℂ) (S T : Set Λ) : Prop :=
  Disjoint S T ∧ ∀ x ∈ S, ∀ y ∈ T, C x y = 0 ∧ C y x = 0

/-- **Finite range for `F_C` with sources**: the bulk and single-source components of `F_C(A, B)`
vanish if `C` vanishes between the supports. -/
theorem FCO_eabZero_of_sep (C : Matrix Λ Λ ℂ) {S T : Set Λ} (hST : CovSep C S T) {A B : OE c Λ}
    (hA : CmpIn S (A : SA c Λ)) (hB : CmpIn T (B : SA c Λ)) : EabZero (FCO C A B : SA c Λ) := by
  obtain ⟨hd, hC⟩ := hST
  have z : ∀ {x y : Grassmann.N Λ}, x ∈ NX S → y ∈ NX T → FC C x y = 0 :=
    fun hx hy => FC_eq_zero_of_disjoint C hd hC hx hy
  refine ⟨?_, ?_, ?_⟩
  · rw [FCO_e]; exact z hA.e hB.e
  · have := FCO_cmp C true A B
    simp only [cmp_true] at this
    rw [this, z (tau_mem_NX hA.e) hB.a, z hA.a hB.e, add_zero]
  · have := FCO_cmp C false A B
    simp only [cmp_false] at this
    rw [this, z (tau_mem_NX hA.e) hB.b, z hA.b hB.e, add_zero]

theorem πobs_EthO (C : Matrix Λ Λ ℂ) (F : OE c Λ) : πobs (EthO C F) = EthO C (πobs F) := by
  rw [EthO_eq_expO, EthO_eq_expO]
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;> simp [piobs_apply]

/-- `π_obs(FG) = F_∅ G^{obs} + F^{obs} G`. -/
theorem πobs_mul (F G : OE c Λ) : πobs (F * G) = emb (bulk F) * πobs G + πobs F * G := by
  have e1 : ∀ X : OE c Λ, πobs X = X - emb (bulk X) := fun X => by
    rw [eq_sub_iff_add_eq, add_comm]; exact (eq_emb_add_πobs X).symm
  rw [e1 (F * G), e1 G, e1 F, map_mul, map_mul]
  ring

end Prim

/-! ### The observable part of the norm -/

variable (w : Wt)

/-- The observable part `‖π_obs F‖_{T_j(ℓ)}` of the norm. -/
def oTo (j : ℕ) (ℓ : ℝ) (F : OE c (Lam d L N)) : ℝ≥0∞ :=
  oTj d L w j ℓ (πobs F : SA c (Lam d L N))

theorem oTj_eq_bulk_add (j : ℕ) (ℓ : ℝ) (F : OE c (Lam d L N)) :
    oTj d L w j ℓ (F : SA c (Lam d L N)) = Tj d (L : ℝ) j ℓ (F : SA c (Lam d L N)).e + oTo w j ℓ F := by
  have hz : Tj d (L : ℝ) j ℓ (0 : Alg d L N) = 0 := tNorm_zero'
  simp only [oTo, oTj, oNorm, coe_πobs, piobs_apply]
  rw [hz, zero_add]; ring

theorem oTo_le (j : ℕ) (ℓ : ℝ) (F : OE c (Lam d L N)) :
    oTo w j ℓ F ≤ oTj d L w j ℓ (F : SA c (Lam d L N)) := by
  rw [oTj_eq_bulk_add]; exact le_add_self

theorem oTj_emb (j : ℕ) (ℓ : ℝ) (x : EvR (Lam d L N)) :
    oTj d L w j ℓ ((emb x : OE c (Lam d L N)) : SA c (Lam d L N)) = Tj d (L : ℝ) j ℓ (x : Alg d L N) := by
  rw [oTj_eq_bulk_add, oTo, πobs_emb]
  show _ + oNorm _ _ (0 : SA c (Lam d L N)) = _
  simp [oNorm, tNorm_zero']

/-- **The product rule for the observable part.** -/
theorem oTo_mul_le {j : ℕ} {ℓ : ℝ} (hh : (0 : ℝ) < (L : ℝ) ^ j) (hℓ : 0 < ℓ) (hw : w.Sub)
    (F G : OE c (Lam d L N)) :
    oTo w j ℓ (F * G) ≤ Tj d (L : ℝ) j ℓ (F : SA c (Lam d L N)).e * oTo w j ℓ G +
      oTo w j ℓ F * (Tj d (L : ℝ) j ℓ (G : SA c (Lam d L N)).e + oTo w j ℓ G) := by
  rw [oTo, πobs_mul]
  refine (oT_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (oT_mul_le (E := Dir d) (p := pPhi d) hh hℓ hw (emb (bulk F)) (πobs G)).trans
      (le_of_eq ?_)
    change oTj d L w j ℓ ((emb (bulk F) : OE c (Lam d L N)) : SA c (Lam d L N)) *
      oTj d L w j ℓ ((πobs G : OE c (Lam d L N)) : SA c (Lam d L N)) = _
    rw [oTj_emb, coe_bulk]; rfl
  · refine (oT_mul_le (E := Dir d) (p := pPhi d) hh hℓ hw (πobs F) G).trans (le_of_eq ?_)
    change oTj d L w j ℓ ((πobs F : OE c (Lam d L N)) : SA c (Lam d L N)) *
      oTj d L w j ℓ (G : SA c (Lam d L N)) = _
    rw [oTj_eq_bulk_add w j ℓ G]; rfl

theorem oTo_add_le (j : ℕ) (ℓ : ℝ) (F G : OE c (Lam d L N)) :
    oTo w j ℓ (F + G) ≤ oTo w j ℓ F + oTo w j ℓ G := by
  rw [oTo, oTo, oTo, map_add]; exact oT_add_le _ _

theorem oTo_sub_le (j : ℕ) (ℓ : ℝ) (F G : OE c (Lam d L N)) :
    oTo w j ℓ (F - G) ≤ oTo w j ℓ F + oTo w j ℓ G := by
  rw [oTo, oTo, oTo, map_sub]; exact oT_sub_le _ _

theorem oTo_smul (j : ℕ) (ℓ : ℝ) (r : ℂ) (F : OE c (Lam d L N)) :
    oTo w j ℓ (r • F) = ENNReal.ofReal ‖r‖ * oTo w j ℓ F := by
  rw [oTo, oTo, map_smul]; exact oT_smul _ _

theorem oTo_sum_le (j : ℕ) (ℓ : ℝ) {ι : Type*} (s : Finset ι) (F : ι → OE c (Lam d L N)) :
    oTo w j ℓ (∑ i ∈ s, F i) ≤ ∑ i ∈ s, oTo w j ℓ (F i) := by
  rw [oTo, map_sum, AddSubmonoidClass.coe_finsetSum]
  exact oT_sum_le _ _

theorem oTo_eq_comp {w : Wt} (hw0 : w.ab = 0) (j : ℕ) (ℓ : ℝ)
    (F : OE c (Lam d L N)) :
    oTo w j ℓ F = w.a * Tj d (L : ℝ) j ℓ (F : SA c (Lam d L N)).a +
      w.b * Tj d (L : ℝ) j ℓ (F : SA c (Lam d L N)).b := by
  simp only [oTo, oTj, oNorm, coe_πobs, piobs_apply, tNorm_zero', hw0, zero_mul, zero_add,
    add_zero]

theorem oTo_eq_zero_of_eab (j : ℕ) (ℓ : ℝ) (hw0 : w.ab = 0) {F : OE c (Lam d L N)}
    (hF : EabZero (F : SA c (Lam d L N))) : oTo w j ℓ F = 0 := by
  rw [oTo]
  refine oNorm_eq_zero_of_eab tNorm_zero' hw0 ⟨?_, ?_, ?_⟩
  · rw [coe_πobs, piobs_apply]
  · rw [coe_πobs, piobs_apply]; exact hF.a
  · rw [coe_πobs, piobs_apply]; exact hF.b

theorem oTo_emb (j : ℕ) (ℓ : ℝ) (x : EvR (Lam d L N)) : oTo w j ℓ (emb x : OE c (Lam d L N)) = 0 := by
  rw [oTo, πobs_emb]; show oNorm _ _ (0 : SA c (Lam d L N)) = 0; simp [oNorm, tNorm_zero']

theorem oTo_algebraMap (j : ℕ) (ℓ : ℝ) (r : ℂ) :
    oTo w j ℓ (algebraMap ℂ (OE c (Lam d L N)) r) = 0 := by
  have : algebraMap ℂ (OE c (Lam d L N)) r = emb (algebraMap ℂ (EvR (Lam d L N)) r) :=
    (AlgHom.commutes _ r).symm
  rw [this, oTo_emb]

/-- Removing the constants: `‖π_obs ε(F)‖ ≤ ‖π_obs F‖`. -/
theorem oTo_epsO_le {j : ℕ} {ℓ : ℝ} (hh : (0 : ℝ) < (L : ℝ) ^ j) (hℓ : 0 < ℓ)
    (F : OE c (Lam d L N)) : oTo w j ℓ (epsO F) ≤ oTo w j ℓ F := by
  have hc : ∀ x : Alg d L N, Tj d (L : ℝ) j ℓ (algebraMap ℂ (Alg d L N) (ε x)) ≤ Tj d (L : ℝ) j ℓ x :=
    fun x => (tNorm_algebraMap_le hh hℓ _).trans (abs_ε_le hh hℓ x)
  rw [oTo, oTo]
  refine oNorm_le_cmp' ?_ ?_ ?_ ?_ <;> simp only [coe_πobs, piobs_apply, coe_epsO, epsS_a, epsS_b,
    epsS_ab]
  · exact le_rfl
  · exact hc _
  · exact hc _
  · exact hc _

theorem oTo_πobs (j : ℕ) (ℓ : ℝ) (F : OE c (Lam d L N)) : oTo w j ℓ (πobs F) = oTo w j ℓ F := by
  rw [oTo, oTo]
  congr 1
  rw [coe_πobs, coe_πobs]
  refine SA.ext ?_ ?_ ?_ ?_ <;> simp [piobs_apply]

theorem EabZero.cmpIn {Λ : Type*} [DecidableEq Λ] {S : Set Λ} {F : SA c Λ} (hF : EabZero F) :
    CmpIn S F := ⟨by rw [hF.e]; exact zero_mem _, by rw [hF.a]; exact zero_mem _,
      by rw [hF.b]; exact zero_mem _⟩

/-! ### Elementary bounds in `ℝ≥0∞` -/

theorem le_ofReal_add {x y : ℝ≥0∞} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : x ≤ ENNReal.ofReal a)
    (hy : y ≤ ENNReal.ofReal b) : x + y ≤ ENNReal.ofReal (a + b) := by
  rw [ENNReal.ofReal_add ha hb]; exact add_le_add hx hy

theorem le_ofReal_mul {x y : ℝ≥0∞} {a b : ℝ} (ha : 0 ≤ a) (hx : x ≤ ENNReal.ofReal a)
    (hy : y ≤ ENNReal.ofReal b) : x * y ≤ ENNReal.ofReal (a * b) := by
  rw [ENNReal.ofReal_mul ha]; exact mul_le_mul' hx hy

theorem le_ofReal_sum {ι : Type*} (s : Finset ι) {x : ι → ℝ≥0∞} {a : ι → ℝ}
    (ha : ∀ i ∈ s, 0 ≤ a i) (hx : ∀ i ∈ s, x i ≤ ENNReal.ofReal (a i)) :
    ∑ i ∈ s, x i ≤ ENNReal.ofReal (∑ i ∈ s, a i) := by
  rw [ENNReal.ofReal_sum_of_nonneg ha]; exact sum_le_sum hx

theorem le_ofReal_sum_const {ι : Type*} (s : Finset ι) {x : ι → ℝ≥0∞} {a : ℝ} (ha : 0 ≤ a)
    (hx : ∀ i ∈ s, x i ≤ ENNReal.ofReal a) : ∑ i ∈ s, x i ≤ ENNReal.ofReal (s.card * a) := by
  refine (le_ofReal_sum s (fun _ _ => ha) hx).trans (le_of_eq ?_)
  rw [sum_const, nsmul_eq_mul]

/-! ### The lifted Step2 bounds -/

section Lift

variable {w}

theorem oTj_succ_two_le (hw0 : w.ab = 0) (hd : 1 ≤ d) (hL : pauliL0 d ≤ L) {j : ℕ} (hj : j < N)
    {Y : Finset (Lam d L N)} {F : SA c (Lam d L N)} (hF : CmpIn (↑Y : Set (Lam d L N)) F)
    {ℓ : ℝ} (hℓ : 0 < ℓ) :
    oTj d L w (j + 1) (2 * ℓ) F ≤ ENNReal.ofReal (Step2.pq d ^ nb j Y) * oTj d L w j ℓ F :=
  oNorm_le_cmp3 hw0 (Step2.Tj_succ_two_le hd hL hj hF.e hℓ) (Step2.Tj_succ_two_le hd hL hj hF.a hℓ)
    (Step2.Tj_succ_two_le hd hL hj hF.b hℓ)

/-- **The two-scale expectation bound with sources.** -/
theorem oTj_EthO_le2 (hw0 : w.ab = 0) (hd : 1 ≤ d) (hL : pauliL0 d ≤ L) {j : ℕ} (hj : j < N) {ℓ ℓ' ℓC : ℝ}
    (hℓ' : 0 < ℓ') (hℓC : 0 < ℓC) (hsum : ℓ' + ℓC ≤ 2 * ℓ)
    {C : Matrix (Lam d L N) (Lam d L N) ℂ} (hC : Step2.GoodCov2 j ℓC C)
    {Y : Finset (Lam d L N)} {F : OE c (Lam d L N)} (hF : CmpIn (↑Y : Set (Lam d L N)) (F : SA c (Lam d L N))) :
    oTj d L w (j + 1) ℓ' (EthO C F : SA c (Lam d L N)) ≤
      ENNReal.ofReal (Step2.pq d ^ nb j Y) * oTj d L w j ℓ (F : SA c (Lam d L N)) := by
  refine oNorm_le_cmp3 hw0 ?_ ?_ ?_
  · rw [EthO_e]; exact Step2.EthE_succ_le2 hd hL hj hℓ' hℓC hsum hC hF.e
  · rw [EthO_a]; exact Step2.EthE_succ_le2 hd hL hj hℓ' hℓC hsum hC hF.a
  · rw [EthO_b]; exact Step2.EthE_succ_le2 hd hL hj hℓ' hℓC hsum hC hF.b

theorem oTj_EthO_le2' {j : ℕ} {ℓ ℓ' ℓC : ℝ} (hℓ' : 0 < ℓ') (hℓC : 0 < ℓC)
    (hsum : ℓ' + ℓC ≤ 2 * ℓ) {C : Matrix (Lam d L N) (Lam d L N) ℂ} (hC : Step2.GoodCov2 j ℓC C)
    (F : OE c (Lam d L N)) :
    oTj d L w (j + 1) ℓ' (EthO C F : SA c (Lam d L N)) ≤
      oTj d L w (j + 1) (2 * ℓ) (F : SA c (Lam d L N)) := by
  refine oNorm_le_cmp' ?_ ?_ ?_ ?_
  · rw [EthO_e]; exact Step2.EthE_succ_le2' hℓ' hℓC hsum hC _
  · rw [EthO_a]; exact Step2.EthE_succ_le2' hℓ' hℓC hsum hC _
  · rw [EthO_b]; exact Step2.EthE_succ_le2' hℓ' hℓC hsum hC _
  · rw [EthO_ab]; exact Step2.EthE_succ_le2' hℓ' hℓC hsum hC _

theorem oTo_EthO_le2 (hw0 : w.ab = 0) (hd : 1 ≤ d) (hL : pauliL0 d ≤ L) {j : ℕ} (hj : j < N) {ℓ ℓ' ℓC : ℝ}
    (hℓ' : 0 < ℓ') (hℓC : 0 < ℓC) (hsum : ℓ' + ℓC ≤ 2 * ℓ)
    {C : Matrix (Lam d L N) (Lam d L N) ℂ} (hC : Step2.GoodCov2 j ℓC C)
    {Y : Finset (Lam d L N)} {F : OE c (Lam d L N)} (hF : CmpIn (↑Y : Set (Lam d L N)) (F : SA c (Lam d L N))) :
    oTo w (j + 1) ℓ' (EthO C F) ≤ ENNReal.ofReal (Step2.pq d ^ nb j Y) * oTo w j ℓ F := by
  rw [oTo, πobs_EthO]
  exact oTj_EthO_le2 hw0 hd hL hj hℓ' hℓC hsum hC hF.πobs

/-- **The truncated expectation with sources**: `‖F_C(𝔼θA, 𝔼θB)‖_{T_{j+1}(ℓ')} ≤
2 ‖A‖_{T_{j+1}(2ℓ)} ‖B‖_{T_{j+1}(2ℓ)}`. -/
theorem oTj_FCO_le {j : ℕ} {ℓ ℓ' ℓC : ℝ} (hℓ' : 0 < ℓ') (hℓC : 0 < ℓC)
    (hsum : ℓ' + ℓC ≤ 2 * ℓ) {C : Matrix (Lam d L N) (Lam d L N) ℂ} (hC : Step2.GoodCov2 j ℓC C)
    (hw : w.Sub) (A B : OE c (Lam d L N)) :
    oTj d L w (j + 1) ℓ' (FCO C (EthO C A) (EthO C B) : SA c (Lam d L N)) ≤
      2 * (oTj d L w (j + 1) (2 * ℓ) (A : SA c (Lam d L N)) *
        oTj d L w (j + 1) (2 * ℓ) (B : SA c (Lam d L N))) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hh : (0 : ℝ) < (L : ℝ) ^ (j + 1) := by positivity
  have hℓ : 0 < ℓ := by linarith
  rw [FCO_EthO, AddSubgroupClass.coe_sub]
  have h1 : oTj d L w (j + 1) ℓ' (EthO C (A * B) : SA c (Lam d L N)) ≤
      oTj d L w (j + 1) (2 * ℓ) (A : SA c (Lam d L N)) * oTj d L w (j + 1) (2 * ℓ) (B : SA c (Lam d L N)) := by
    refine (oTj_EthO_le2' hℓ' hℓC hsum hC _).trans ?_
    exact oT_mul_le (E := Dir d) (p := pPhi d) hh (by positivity) hw A B
  have h2 : oTj d L w (j + 1) ℓ' ((EthO C A * EthO C B : OE c (Lam d L N)) : SA c (Lam d L N)) ≤
      oTj d L w (j + 1) (2 * ℓ) (A : SA c (Lam d L N)) * oTj d L w (j + 1) (2 * ℓ) (B : SA c (Lam d L N)) := by
    refine (oT_mul_le (E := Dir d) (p := pPhi d) hh hℓ' hw _ _).trans ?_
    exact mul_le_mul' (oTj_EthO_le2' hℓ' hℓC hsum hC A) (oTj_EthO_le2' hℓ' hℓC hsum hC B)
  refine (oT_sub_le (E := Dir d) (p := pPhi d) _ _).trans ?_
  calc _ ≤ oTj d L w (j + 1) (2 * ℓ) (A : SA c (Lam d L N)) * oTj d L w (j + 1) (2 * ℓ) (B : SA c (Lam d L N)) +
        oTj d L w (j + 1) (2 * ℓ) (A : SA c (Lam d L N)) * oTj d L w (j + 1) (2 * ℓ) (B : SA c (Lam d L N)) :=
        add_le_add h1 h2
    _ = _ := by ring

end Lift

end

end Obs2
