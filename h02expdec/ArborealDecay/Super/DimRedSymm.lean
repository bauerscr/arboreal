module

public import ArborealDecay.Super.DimRedDecay

/-!
# Symmetries of the `ℍ^{2|4}` expectation and the observable `y_i y_j`

* Linearity of `expectH` (`expectH_add`, `expectH_smul`, `expectH_sub`).
* The `x ↔ y` symmetry (`expectH_sxy`): the integrand is invariant under exchanging `x` and `y`,
  and Lebesgue measure is invariant under the coordinate swap.
* The `(ξ¹, η¹) ↔ (ξ², η²)` symmetry (`expectH_sw`): the algebra automorphism `sw` exchanging the
  two fermion pairs fixes `z_i`, `u_i · u_j` and the action, and the total Berezin integral
  `∏ ∂_{η¹}∂_{ξ¹} ∂_{η²}∂_{ξ²}` is invariant under `sw`.
* `expectH_yy`: `[y_i y_j]^{ℍ^{2|4}}_{β,h} = ½ [ξ_i η_j + ξ_j η_i]^{ℍ^{0|2}}_{β,h}`.  This is the
  identity behind BCHS Cor. 2.10 (2.64) (`h02.tex` L1480–1482, proof L1542–1548): by localization
  `[x_i x_j + y_i y_j + η²_i ξ²_j - ξ²_i η²_j] = 0`, by the two symmetries
  `[x_i x_j] = [y_i y_j]` and `[η²_i ξ²_j - ξ²_i η²_j] = [η¹_i ξ¹_j - ξ¹_i η¹_j]`, and the latter is
  `[u_i · u_j + z_i z_j] - [σ_ij]`, which reduces to `ℍ^{0|2}` by Prop. 2.7.
-/

@[expose] public section

namespace ArborealDecay.Super

noncomputable section

open MeasureTheory CliffordAlgebra Grassmann Finset

set_option linter.unusedSectionVars false

namespace H24

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ### Linearity -/

theorem integrandF_add (β : Λ → Λ → ℝ) (h : Λ → ℝ) (F G : Pt Λ → A Λ) (p : Pt Λ) :
    integrandF β h (fun q => F q + G q) p = integrandF β h F p + integrandF β h G p := by
  simp only [integrandF, add_mul, mul_add]

theorem integrandF_smul (β : Λ → Λ → ℝ) (h : Λ → ℝ) (c : ℝ) (F : Pt Λ → A Λ) (p : Pt Λ) :
    integrandF β h (fun q => c • F q) p = c • integrandF β h F p := by
  simp only [integrandF, smul_mul_assoc, mul_smul_comm]

theorem integrable_integrandF {β : Λ → Λ → ℝ} {h : Λ → ℝ} {F : Pt Λ → A Λ}
    (hF : SDecay (integrandF β h F)) :
    Integrable fun p => body (B1 (Finset.univ : Finset Λ).toList (berezin (integrandF β h F p))) :=
  (hF.map berezin).sint (body.toLinearMap ∘ₗ B1 (Finset.univ : Finset Λ).toList)

theorem expectH_add {β : Λ → Λ → ℝ} {h : Λ → ℝ} {F G : Pt Λ → A Λ}
    (hF : SDecay (integrandF β h F)) (hG : SDecay (integrandF β h G)) :
    expectH β h (fun p => F p + G p) = expectH β h F + expectH β h G := by
  simp only [expectH_eq_intH, integrandF_add, map_add]
  rw [integral_add (integrable_integrandF hF) (integrable_integrandF hG), mul_add]

theorem expectH_smul (β : Λ → Λ → ℝ) (h : Λ → ℝ) (c : ℝ) (F : Pt Λ → A Λ) :
    expectH β h (fun p => c • F p) = c * expectH β h F := by
  simp only [expectH_eq_intH, integrandF_smul, map_smul, smul_eq_mul, integral_const_mul]
  ring

theorem expectH_sub {β : Λ → Λ → ℝ} {h : Λ → ℝ} {F G : Pt Λ → A Λ}
    (hF : SDecay (integrandF β h F)) (hG : SDecay (integrandF β h G)) :
    expectH β h (fun p => F p - G p) = expectH β h F - expectH β h G := by
  have hG' : SDecay (integrandF β h fun p => (-1 : ℝ) • G p) := by
    rw [show integrandF β h (fun p => (-1 : ℝ) • G p) = fun p => (-1 : ℝ) • integrandF β h G p
      from funext fun p => integrandF_smul β h (-1) G p]
    exact hG.smul (Temp.const (-1))
  have e : (fun p => F p - G p) = fun p => F p + (-1 : ℝ) • G p := by
    funext p; rw [neg_one_smul, sub_eq_add_neg]
  rw [e, expectH_add hF hG', expectH_smul]; ring

/-! ### The `x ↔ y` symmetry -/

/-- Exchange `x` and `y`. -/
def sxy (p : Pt Λ) : Pt Λ := fun k => p (Sum.swap k)

@[simp] theorem sxy_inl (p : Pt Λ) (i : Λ) : sxy p (.inl i) = p (.inr i) := rfl
@[simp] theorem sxy_inr (p : Pt Λ) (i : Λ) : sxy p (.inr i) = p (.inl i) := rfl

theorem integral_sxy (G : Pt Λ → ℝ) : ∫ p, G (sxy p) = ∫ p, G p := by
  have hmp := volume_measurePreserving_piCongrLeft (fun _ : Λ ⊕ Λ => ℝ) (Equiv.sumComm Λ Λ)
  have h := hmp.integral_comp' (g := G)
  rw [← h]
  congr 1
  funext p
  congr 1
  funext k
  simp [sxy, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]

theorem Rz_sxy (i : Λ) (p : Pt Λ) : Rz i (sxy p) = Rz i p := by
  rw [Rz, Rz, sxy_inl, sxy_inr, add_right_comm (1 : ℝ)]

theorem zH_sxy (i : Λ) (p : Pt Λ) : zH i (sxy p) = zH i p := by rw [zH, zH, Rz_sxy]

theorem dotH_sxy (i j : Λ) (p : Pt Λ) : dotH i j (sxy p) = dotH i j p := by
  rw [dotH, dotH, zH_sxy, zH_sxy, sxy_inl, sxy_inl, sxy_inr, sxy_inr,
    add_comm (p (.inr i) * p (.inr j))]

theorem actionH_sxy (β : Λ → Λ → ℝ) (h : Λ → ℝ) (p : Pt Λ) :
    actionH β h (sxy p) = actionH β h p := by
  simp only [actionH, dotH_sxy, zH_sxy]

theorem zinvProd_sxy (p : Pt Λ) : zinvProd (sxy p) = zinvProd p := by
  simp only [zinvProd, zH_sxy]

theorem integrandF_sxy (β : Λ → Λ → ℝ) (h : Λ → ℝ) (F : Pt Λ → A Λ) (p : Pt Λ) :
    integrandF β h F (sxy p) = integrandF β h (fun q => F (sxy q)) p := by
  simp only [integrandF, zinvProd_sxy, actionH_sxy]

/-- The `x ↔ y` symmetry of the `ℍ^{2|4}` expectation. -/
theorem expectH_sxy (β : Λ → Λ → ℝ) (h : Λ → ℝ) (F : Pt Λ → A Λ) :
    expectH β h (fun p => F (sxy p)) = expectH β h F := by
  rw [expectH_eq_intH, expectH_eq_intH]
  congr 1
  simp_rw [← integrandF_sxy]
  exact integral_sxy fun p =>
    body (B1 (Finset.univ : Finset Λ).toList (berezin (integrandF β h F p)))

/-! ### The `(ξ¹, η¹) ↔ (ξ², η²)` symmetry -/

/-- The automorphism exchanging the pairs `(ξ¹_i, η¹_i)` and `(ξ²_i, η²_i)`. -/
def sw : A Λ →ₐ[ℝ] A Λ :=
  ExteriorAlgebra.map (LinearMap.funLeft ℝ ℝ (Sum.swap : (Λ ⊕ Λ) ⊕ (Λ ⊕ Λ) → (Λ ⊕ Λ) ⊕ (Λ ⊕ Λ)))

theorem sw_ι (v : (Λ ⊕ Λ) ⊕ (Λ ⊕ Λ) → ℝ) :
    sw (ExteriorAlgebra.ι ℝ v) = ExteriorAlgebra.ι ℝ (fun o => v (Sum.swap o)) := by
  simp [sw, ExteriorAlgebra.map_apply_ι]; rfl

theorem sw_gen (o : (Λ ⊕ Λ) ⊕ (Λ ⊕ Λ)) : sw (gen o : A Λ) = gen (Sum.swap o) := by
  rw [gen, sw_ι, gen]
  congr 1; ext o'
  simp only [Pi.single_apply]
  congr 1
  exact propext ⟨fun h => by rw [← h, Sum.swap_swap], fun h => by rw [h, Sum.swap_swap]⟩

@[simp] theorem sw_ξ (i : Λ) : sw (ξ i : A Λ) = ξ1 i := sw_gen _
@[simp] theorem sw_η (i : Λ) : sw (η i : A Λ) = η1 i := sw_gen _
@[simp] theorem sw_ξ1 (i : Λ) : sw (ξ1 i : A Λ) = ξ i := sw_gen _
@[simp] theorem sw_η1 (i : Λ) : sw (η1 i : A Λ) = η i := sw_gen _

theorem body_sw (x : A Λ) : body (sw x) = body x := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι v =>
    change body (sw (ExteriorAlgebra.ι ℝ v)) = body (ExteriorAlgebra.ι ℝ v)
    rw [sw_ι, body_ι, body_ι]
  | mul a b ha hb => rw [map_mul, map_mul, map_mul, ha, hb]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

theorem inv'_sw (x : A Λ) : inv' (sw x) = sw (inv' x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι v =>
    change inv' (sw (ExteriorAlgebra.ι ℝ v)) = sw (inv' (ExteriorAlgebra.ι ℝ v))
    rw [sw_ι, inv'_ι, inv'_ι, map_neg, sw_ι]
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb, map_mul, map_mul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

theorem sw_dgen (o : (Λ ⊕ Λ) ⊕ (Λ ⊕ Λ)) (x : A Λ) : sw (dgen o x) = dgen (Sum.swap o) (sw x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι v =>
    change sw (dgen o (ExteriorAlgebra.ι ℝ v)) = dgen (Sum.swap o) (sw (ExteriorAlgebra.ι ℝ v))
    rw [sw_ι]
    simp [dgen, ExteriorAlgebra.ι, contractLeft_ι]
  | mul a b ha hb => rw [dgen_mul, map_add, map_mul, map_mul, ha, hb, map_mul, dgen_mul, inv'_sw]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

theorem sw_scomp (g : ℝ → ℝ) {a : A Λ} (ha : IsEven a) : sw (scomp g a) = scomp g (sw a) :=
  map_scomp sw body_sw g (isNilpotent_soul ha)

theorem sw_Rz (i : Λ) (p : Pt Λ) : sw (Rz i p) = Rz i p := by
  simp only [Rz, map_sub, map_smul, map_mul, map_one, sw_ξ, sw_η, sw_ξ1, sw_η1]
  abel

theorem sw_zH (i : Λ) (p : Pt Λ) : sw (zH i p) = zH i p := by
  rw [zH, sw_scomp _ (isEven_Rz i p), sw_Rz]

theorem sw_dotH (i j : Λ) (p : Pt Λ) : sw (dotH i j p) = dotH i j p := by
  simp only [dotH, map_sub, map_add, map_smul, map_mul, map_one, sw_ξ, sw_η, sw_ξ1, sw_η1, sw_zH]
  abel

theorem sw_actionH (β : Λ → Λ → ℝ) (h : Λ → ℝ) (p : Pt Λ) : sw (actionH β h p) = actionH β h p := by
  simp only [actionH, map_add, map_smul, map_sum, map_sub, map_one, sw_dotH, sw_zH]

theorem sw_zinvProd (p : Pt Λ) : sw (zinvProd p) = zinvProd p := by
  rw [zinvProd, map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply, inverse_zH, sw_scomp _ (isEven_zH i p), sw_zH]

theorem sw_integrandF (β : Λ → Λ → ℝ) (h : Λ → ℝ) (F : Pt Λ → A Λ) (p : Pt Λ) :
    sw (integrandF β h F p) = integrandF β h (fun q => sw (F q)) p := by
  rw [integrandF, integrandF, map_mul, map_mul, sw_zinvProd,
    sw_scomp _ (isEven_actionH β h p).neg, map_neg, sw_actionH]

/-! ### Invariance of the total Berezin integral under `sw` -/

theorem dgen4_comm (o₁ o₂ o₃ o₄ : (Λ ⊕ Λ) ⊕ (Λ ⊕ Λ)) (x : A Λ) :
    dgen o₁ (dgen o₂ (dgen o₃ (dgen o₄ x))) = dgen o₃ (dgen o₄ (dgen o₁ (dgen o₂ x))) := by
  rw [dgen_comm o₂ o₃, map_neg, dgen_comm o₁ o₃, neg_neg, dgen_comm o₂ o₄, map_neg, map_neg,
    dgen_comm o₁ o₄, map_neg, neg_neg]

/-- A pair operator `∂_{θ_a} ∂_{θ_b}`. -/
def dd (a b : (Λ ⊕ Λ) ⊕ (Λ ⊕ Λ)) : A Λ →ₗ[ℝ] A Λ := dgen a ∘ₗ dgen b

theorem dd_comm (a b c d : (Λ ⊕ Λ) ⊕ (Λ ⊕ Λ)) : dd a b ∘ₗ dd c d = dd c d ∘ₗ dd a b :=
  LinearMap.ext fun x => dgen4_comm a b c d x

theorem bpair_eq (i : Λ) : (bpair i : A Λ →ₗ[ℝ] A Λ) = dd (.inl (.inr i)) (.inl (.inl i)) := rfl

theorem bpar_eq (i : Λ) : (bpar i : A Λ →ₗ[ℝ] A Λ) = dd (.inr (.inr i)) (.inr (.inl i)) := rfl

/-- `∏_{i ∈ l} f_i`, the head of `l` applied last. -/
def lprod (f : Λ → A Λ →ₗ[ℝ] A Λ) (l : List Λ) : A Λ →ₗ[ℝ] A Λ :=
  l.foldr (fun i L => f i ∘ₗ L) LinearMap.id

theorem lprod_comm {f : Λ → A Λ →ₗ[ℝ] A Λ} {M : A Λ →ₗ[ℝ] A Λ} (hM : ∀ i, f i ∘ₗ M = M ∘ₗ f i)
    (l : List Λ) : lprod f l ∘ₗ M = M ∘ₗ lprod f l := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change (f i ∘ₗ lprod f l) ∘ₗ M = M ∘ₗ (f i ∘ₗ lprod f l)
    rw [LinearMap.comp_assoc, ih, ← LinearMap.comp_assoc, hM, LinearMap.comp_assoc]

theorem foldl_eq_lprod {f : Λ → A Λ →ₗ[ℝ] A Λ} (hf : ∀ i j, f i ∘ₗ f j = f j ∘ₗ f i)
    (l : List Λ) (L₀ : A Λ →ₗ[ℝ] A Λ) :
    l.foldl (fun L i => f i ∘ₗ L) L₀ = lprod f l ∘ₗ L₀ := by
  induction l generalizing L₀ with
  | nil => rfl
  | cons i l ih =>
    rw [List.foldl_cons, ih, ← LinearMap.comp_assoc, lprod_comm (fun j => hf j i)]
    rfl

theorem bpair_comm (i j : Λ) : (bpair i : A Λ →ₗ[ℝ] A Λ) ∘ₗ bpair j = bpair j ∘ₗ bpair i := by
  rw [bpair_eq, bpair_eq, dd_comm]

theorem bpar_comm (i j : Λ) : (bpar i : A Λ →ₗ[ℝ] A Λ) ∘ₗ bpar j = bpar j ∘ₗ bpar i := by
  rw [bpar_eq, bpar_eq, dd_comm]

theorem bpair_bpar_comm (i j : Λ) : (bpair i : A Λ →ₗ[ℝ] A Λ) ∘ₗ bpar j = bpar j ∘ₗ bpair i := by
  rw [bpair_eq, bpar_eq, dd_comm]

theorem berezinL_eq_lprod (l : List Λ) : (berezinL l : A Λ →ₗ[ℝ] A Λ) = lprod bpair l := rfl

theorem B1_eq_lprod (l : List Λ) : (B1 l : A Λ →ₗ[ℝ] A Λ) = lprod bpar l := by
  rw [B1, foldl_eq_lprod bpar_comm, LinearMap.comp_id]

theorem sw_bpair (i : Λ) (x : A Λ) : sw (bpair i x) = bpar i (sw x) := by
  simp only [bpair, bpar, dξ, dη, LinearMap.coe_comp, Function.comp_apply, sw_dgen]; rfl

theorem sw_bpar (i : Λ) (x : A Λ) : sw (bpar i x) = bpair i (sw x) := by
  simp only [bpair, bpar, dξ, dη, LinearMap.coe_comp, Function.comp_apply, sw_dgen]; rfl

theorem sw_lprod_bpair (l : List Λ) (x : A Λ) : sw (lprod bpair l x) = lprod bpar l (sw x) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change sw (bpair i (lprod bpair l x)) = bpar i (lprod bpar l (sw x))
    rw [sw_bpair, ih]

theorem sw_lprod_bpar (l : List Λ) (x : A Λ) : sw (lprod bpar l x) = lprod bpair l (sw x) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change sw (bpar i (lprod bpar l x)) = bpair i (lprod bpair l (sw x))
    rw [sw_bpar, ih]

theorem lprod_bpair_lprod_bpar (l : List Λ) :
    (lprod bpair l : A Λ →ₗ[ℝ] A Λ) ∘ₗ lprod bpar l = lprod bpar l ∘ₗ lprod bpair l :=
  lprod_comm (fun i => (lprod_comm (fun j => (bpair_bpar_comm i j).symm) l).symm) l

/-- The total Berezin integral is invariant under the exchange of the two pairs. -/
theorem body_B1_berezin_sw (l : List Λ) (x : A Λ) :
    body (B1 l (berezinL l (sw x))) = body (B1 l (berezinL l x)) := by
  rw [B1_eq_lprod, berezinL_eq_lprod]
  have e1 : lprod bpair l (sw x) = sw (lprod bpar l x) := (sw_lprod_bpar l x).symm
  rw [e1, ← sw_lprod_bpair, body_sw]
  exact congrArg body (LinearMap.congr_fun (lprod_bpair_lprod_bpar l) x)

/-- The `(ξ¹, η¹) ↔ (ξ², η²)` symmetry of the `ℍ^{2|4}` expectation. -/
theorem expectH_sw (β : Λ → Λ → ℝ) (h : Λ → ℝ) (F : Pt Λ → A Λ) :
    expectH β h (fun p => sw (F p)) = expectH β h F := by
  rw [expectH_eq_intH, expectH_eq_intH]
  congr 2
  funext p
  rw [← sw_integrandF]
  exact body_B1_berezin_sw _ _

/-! ### The observable `y_i y_j` -/

/-- `x_i x_j`. -/
def Fxx (i j : Λ) (p : Pt Λ) : A Λ := (p (.inl i) * p (.inl j)) • (1 : A Λ)

/-- `y_i y_j`. -/
def Fyy (i j : Λ) (p : Pt Λ) : A Λ := (p (.inr i) * p (.inr j)) • (1 : A Λ)

/-- `η²_i ξ²_j - ξ²_i η²_j`. -/
def π2 (i j : Λ) : A Λ := η i * ξ j - ξ i * η j

/-- The observable `u_i · u_j + z_i z_j`. -/
def oτ (i j : Λ) : Obs Λ := .add (.dot i j) (.mul (.z i) (.z j))

theorem tame_oτ (i j : Λ) : (oτ i j).Tame := by simp [oτ, Obs.Tame]

theorem σ_eq (i j : Λ) (p : Pt Λ) : σ i j p = Fxx i j p + Fyy i j p + π2 i j := by
  rw [σ, Fxx, Fyy, π2, add_smul]

theorem τ_eq (i j : Λ) (p : Pt Λ) : τ i j = obsH (oτ i j) p - σ i j p := by
  simp only [obsH, oτ, Obs.eval, dotH_eq]; abel

theorem sw_τ (i j : Λ) : sw (τ i j) = π2 i j := by
  simp only [τ, π2, map_sub, map_mul, sw_ξ1, sw_η1]

theorem stemp_Fxx (i j : Λ) : STemp (Fxx i j : Pt Λ → A Λ) :=
  (STemp.const 1).smul ((Temp.coord _).mul (Temp.coord _))

theorem stemp_Fyy (i j : Λ) : STemp (Fyy i j : Pt Λ → A Λ) :=
  (STemp.const 1).smul ((Temp.coord _).mul (Temp.coord _))

theorem stemp_σ (i j : Λ) : STemp (σ i j : Pt Λ → A Λ) :=
  ((STemp.const 1).smul (temp_quad _ _ _ _)).add (STemp.const _)

theorem tr_σ_zero (i j : Λ) : tr (σ i j 0) = 0 := by
  simp [σ, map_sub, map_mul]

theorem expect_zero (β : Λ → Λ → ℝ) (h : Λ → ℝ) : H02.expect β h 0 = 0 := by
  simp [H02.expect, H02.int0]

theorem expect_neg (β : Λ → Λ → ℝ) (h : Λ → ℝ) (X : H02.Grassmann Λ) :
    H02.expect β h (-X) = -H02.expect β h X := by
  simp [H02.expect, H02.int0, neg_mul]

theorem obs0_oτ (i j : Λ) :
    obs0 (oτ i j) = -(H02.ξ i * H02.η j + H02.ξ j * H02.η i : H02.Grassmann Λ) := by
  simp only [obs0, oτ, Obs.eval, H02.dot]; abel

/-- **`ℍ^{2|4}` → `ℍ^{0|2}` for `y_i y_j`** (the identity behind BCHS Cor. 2.10 (2.64)):
`[y_i y_j]^{ℍ^{2|4}}_{β,h} = ½ [ξ_i η_j + ξ_j η_i]^{ℍ^{0|2}}_{β,h}`, for `β ≥ 0`, `h ≥ 0` and
`Pinned β h`. -/
theorem expectH_yy {β : Λ → Λ → ℝ} (hβ : ∀ i j, 0 ≤ β i j) {h : Λ → ℝ} (hh : ∀ i, 0 ≤ h i)
    (hP : Pinned β h) (i j : Λ) :
    expectH β h (Fyy i j) =
      (1 / 2 : ℝ) * H02.expect β h (H02.ξ i * H02.η j + H02.ξ j * H02.η i) := by
  have dec : ∀ {F : Pt Λ → A Λ}, STemp F → SDecay (integrandF β h F) :=
    fun hF => sdecay_integrandF hβ hh hP hF
  -- `[x_i x_j] = [y_i y_j]`
  have h1 : expectH β h (Fxx i j) = expectH β h (Fyy i j) := by
    rw [← expectH_sxy β h (Fxx i j)]; rfl
  -- localization: `[σ_ij] = 0`
  have h2 : expectH β h (σ i j) = 0 := by
    rw [expectH_eq_of_qc β h ⟨sdiff_σ i j, Q_σ i j⟩ (dec (stemp_σ i j)), tr_σ_zero,
      expect_zero]
  -- linearity
  have h3 : expectH β h (σ i j) = expectH β h (Fxx i j) + expectH β h (Fyy i j) +
      expectH β h (fun _ => π2 i j) := by
    rw [show σ i j = fun p => (Fxx i j p + Fyy i j p) + π2 i j from funext (σ_eq i j),
      expectH_add (F := fun p => Fxx i j p + Fyy i j p)
        (by
          rw [show integrandF β h (fun p => Fxx i j p + Fyy i j p) = fun p =>
            integrandF β h (Fxx i j) p + integrandF β h (Fyy i j) p from
            funext (integrandF_add β h _ _)]
          exact (dec (stemp_Fxx i j)).add (dec (stemp_Fyy i j)))
        (dec (STemp.const _)),
      expectH_add (dec (stemp_Fxx i j)) (dec (stemp_Fyy i j))]
  -- the pair exchange: `[π²_ij] = [τ_ij]`
  have h4 : expectH β h (fun _ => π2 i j) = expectH β h (fun _ => τ i j) := by
    rw [← expectH_sw β h (fun _ => τ i j), sw_τ]
  -- `[τ_ij] = [u_i · u_j + z_i z_j] - [σ_ij]`
  have h5 : expectH β h (fun _ => τ i j) =
      expectH β h (obsH (oτ i j)) - expectH β h (σ i j) := by
    rw [show (fun _ : Pt Λ => τ i j) = fun p => obsH (oτ i j) p - σ i j p from
      funext (τ_eq i j), expectH_sub (dec (stemp_obsH _ (tame_oτ i j)))
        (dec (stemp_σ i j))]
  -- dimensional reduction
  have h6 : expectH β h (obsH (oτ i j)) = H02.expect β h (obs0 (oτ i j)) :=
    expectH_eq_expect_of_pinned hβ hh hP _ (tame_oτ i j)
  rw [h6, obs0_oτ, expect_neg] at h5
  linarith

end H24

end

end ArborealDecay.Super

end
