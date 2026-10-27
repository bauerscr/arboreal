import Obs.MapDef

/-!
# Supports with observables: `𝒩^obs(X)` and `U(1)` invariance (Section `sec:rgmap-ext`)

* `compSub T pa pb ⊆ OE c Λ`: all components in `T`, and the `a` (resp. `b`) and `ab`
  components vanish unless `pa` (resp. `pb`) holds.  This is a subalgebra (`σ_a² = 0`).
* `symSub`: the `U(1)`-invariant even elements.
* `Supp c P a b j U = compSub (𝒩(U^□)) (a ∈ U^□ ∨ P) (b ∈ U^□ ∨ P) ⊓ symSub` (`Supp2` on
  `Λ ⊔ Λ`).  With `P = False` this is the text's `𝒩_sym(U^□)` with observables (a monomial
  containing `σ_a` belongs to `𝒩(X)` only if `a ∈ X`); with `P = True` only the locality of the
  components is required (the split evaluation of the nonlocal `η` term and of the `ab` terms
  at a block containing only one of `a, b` need not lie in the former).
* `θ`, `ι`, `𝔼_C` preserve the supports (`thetaO_mem_Supp2`, `inclO_mem_Supp2`,
  `ECO_mem_Supp`), and `𝔼_C` factorises on supports whose points are not coupled by `C`
  (`ECO_mul_of_sep`, derived componentwise from `Step.EC_mul_of_sep`).
* The extended `Loc`, `J`, the split evaluations of coupling constants and the exponentials
  lie in the supports (`LocO_mem_Supp`, `JO_mem_Supp`, `splitO_mem_Supp`, …).
* `K_{j+1}` lies in the scale-`(j+1)` supports (`KnextO_mem_Supp`, `InKO_KnextO`) under
  `ObsLoc`, whose locality conditions `CoupLoc` on the coupling constants are at scale `j + 1`
  (`NearS`: in Case (2) the split `η` term `ψ̄_aψ_b` at the block of `a` is local at scale
  `j + 1` once `|a - b|_∞ ≤ L^{j+1}`, `nearS_of_le`).  The factorisation `KnextO_union` uses the
  scale-`j` supports and the stronger `ObsLocSep` (`CoupLocSep`, `Near`).
-/

namespace Obs

noncomputable section

open Finset Grassmann SA Loc Step LocObs Gen

/-! ### Componentwise supports -/

section Sub

variable {c : Case} {Λ : Type*} [DecidableEq Λ]

/-- Components in `T`; the `a`, `ab` (resp. `b`, `ab`) components vanish unless `pa` (`pb`). -/
def compSub (T : Subalgebra ℂ (N Λ)) (pa pb : Prop) : Subalgebra ℂ (OE c Λ) where
  carrier := {F | (F : SA c Λ).e ∈ T ∧ (F : SA c Λ).a ∈ T ∧ (F : SA c Λ).b ∈ T ∧
    (F : SA c Λ).ab ∈ T ∧ (¬ pa → (F : SA c Λ).a = 0 ∧ (F : SA c Λ).ab = 0) ∧
    (¬ pb → (F : SA c Λ).b = 0 ∧ (F : SA c Λ).ab = 0)}
  mul_mem' := by
    rintro F G ⟨h1, h2, h3, h4, h5, h6⟩ ⟨g1, g2, g3, g4, g5, g6⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [OE.mul_e]; exact mul_mem h1 g1
    · rw [OE.mul_a]; exact add_mem (mul_mem h1 g2) (mul_mem h2 g1)
    · rw [OE.mul_b]; exact add_mem (mul_mem h1 g3) (mul_mem h3 g1)
    · rw [OE.mul_ab]
      exact add_mem (add_mem (add_mem (mul_mem h1 g4) (Subalgebra.smul_mem _ (mul_mem h2 g3) _))
        (mul_mem h3 g2)) (mul_mem h4 g1)
    · intro hp
      obtain ⟨fa, fab⟩ := h5 hp
      obtain ⟨ga, gab⟩ := g5 hp
      rw [OE.mul_a, OE.mul_ab, fa, fab, ga, gab]; simp
    · intro hp
      obtain ⟨fb, fab⟩ := h6 hp
      obtain ⟨gb, gab⟩ := g6 hp
      rw [OE.mul_b, OE.mul_ab, fb, fab, gb, gab]; simp
  add_mem' := by
    rintro F G ⟨h1, h2, h3, h4, h5, h6⟩ ⟨g1, g2, g3, g4, g5, g6⟩
    refine ⟨add_mem h1 g1, add_mem h2 g2, add_mem h3 g3, add_mem h4 g4, ?_, ?_⟩
    · intro hp
      obtain ⟨fa, fab⟩ := h5 hp
      obtain ⟨ga, gab⟩ := g5 hp
      exact ⟨by show (F : SA c Λ).a + (G : SA c Λ).a = 0; rw [fa, ga, add_zero],
        by show (F : SA c Λ).ab + (G : SA c Λ).ab = 0; rw [fab, gab, add_zero]⟩
    · intro hp
      obtain ⟨fb, fab⟩ := h6 hp
      obtain ⟨gb, gab⟩ := g6 hp
      exact ⟨by show (F : SA c Λ).b + (G : SA c Λ).b = 0; rw [fb, gb, add_zero],
        by show (F : SA c Λ).ab + (G : SA c Λ).ab = 0; rw [fab, gab, add_zero]⟩
  algebraMap_mem' r := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (algebraMap ℂ (SA c Λ) r).e ∈ T; rw [SA.algebraMap_e]; exact T.algebraMap_mem r
    · show (algebraMap ℂ (SA c Λ) r).a ∈ T; rw [SA.algebraMap_a]; exact zero_mem _
    · show (algebraMap ℂ (SA c Λ) r).b ∈ T; rw [SA.algebraMap_b]; exact zero_mem _
    · show (algebraMap ℂ (SA c Λ) r).ab ∈ T; rw [SA.algebraMap_ab]; exact zero_mem _
    · exact fun _ => ⟨SA.algebraMap_a r, SA.algebraMap_ab r⟩
    · exact fun _ => ⟨SA.algebraMap_b r, SA.algebraMap_ab r⟩

theorem mem_compSub {T : Subalgebra ℂ (N Λ)} {pa pb : Prop} {F : OE c Λ} :
    F ∈ compSub T pa pb ↔ (F : SA c Λ).e ∈ T ∧ (F : SA c Λ).a ∈ T ∧ (F : SA c Λ).b ∈ T ∧
      (F : SA c Λ).ab ∈ T ∧ (¬ pa → (F : SA c Λ).a = 0 ∧ (F : SA c Λ).ab = 0) ∧
      (¬ pb → (F : SA c Λ).b = 0 ∧ (F : SA c Λ).ab = 0) := Iff.rfl

theorem compSub_mono {T T' : Subalgebra ℂ (N Λ)} {pa pb pa' pb' : Prop} (hT : T ≤ T')
    (ha : pa → pa') (hb : pb → pb') : (compSub T pa pb : Subalgebra ℂ (OE c Λ)) ≤
      compSub T' pa' pb' := by
  rintro F ⟨h1, h2, h3, h4, h5, h6⟩
  exact ⟨hT h1, hT h2, hT h3, hT h4, fun h => h5 (fun h' => h (ha h')),
    fun h => h6 (fun h' => h (hb h'))⟩

/-- The `U(1)`-invariant even elements. -/
def symSub : Subalgebra ℂ (OE c Λ) := (SymSA c Λ).comap (OEv c Λ).val

theorem mem_symSub {F : OE c Λ} : F ∈ (symSub : Subalgebra ℂ (OE c Λ)) ↔ IsSymS (F : SA c Λ) :=
  mem_SymSA

/-- `e^F` stays in a subalgebra. -/
theorem oexp_mem [Fintype Λ] (S : Subalgebra ℂ (OE c Λ)) {F : OE c Λ} (hF : F ∈ S) (hn : IsNilpotent F) :
    oexp F ∈ S := by
  obtain ⟨k, hk⟩ := hn
  rw [coe_oexp hk]
  exact Subalgebra.sum_mem _ fun i _ => Subalgebra.smul_mem _ (pow_mem hF i) _

/-! #### Components of the `U(1)` action -/

@[simp] theorem scalS_e (t : ℂ) (F : SA c Λ) : (scalS t F).e = Step.scal Λ t F.e := rfl
@[simp] theorem scalS_a (t : ℂ) (F : SA c Λ) : (scalS t F).a = c.ca t • Step.scal Λ t F.a := rfl
@[simp] theorem scalS_b (t : ℂ) (F : SA c Λ) : (scalS t F).b = c.cb t • Step.scal Λ t F.b := rfl
@[simp] theorem scalS_ab (t : ℂ) (F : SA c Λ) :
    (scalS t F).ab = (c.ca t * c.cb t) • Step.scal Λ t F.ab := rfl

end Sub

variable {d L N : ℕ} [NeZero L]

section Comm

variable {c : Case}

theorem scalS_thetaS (t : ℂ) (F : SA c (Lam d L N)) : scalS t (thetaS F) = thetaS (scalS t F) := by
  ext <;> simp [theta_scal, map_smul]

theorem scalS_inclS (t : ℂ) (F : SA c (Lam d L N)) : scalS t (inclS F) = inclS (scalS t F) := by
  ext <;> simp [incl_scal, map_smul]

theorem scalS_ECS (C : Matrix (Lam d L N) (Lam d L N) ℝ) {t : ℂ} (ht : t ≠ 0)
    (F : SA c (Lam d L N ⊕ Lam d L N)) : scalS t (ECS C F) = ECS C (scalS t F) := by
  ext <;> simp [EC_scal C ht, map_smul]

end Comm

/-! ### The supports of the renormalisation group map -/

section Supp

variable (c : Case) (P : Prop) (a b : Lam d L N) (j : ℕ)

/-- `𝒩^obs_sym(U^□)` (for `P = False`), resp. componentwise locality (`P = True`). -/
def Supp (U : Finset (Lam d L N)) : Subalgebra ℂ (OE c (Lam d L N)) :=
  compSub (NX (nbhd j U : Set (Lam d L N))) (a ∈ nbhd j U ∨ P) (b ∈ nbhd j U ∨ P) ⊓ symSub

/-- The supports on the doubled algebra. -/
def Supp2 (U : Finset (Lam d L N)) : Subalgebra ℂ (OE c (Lam d L N ⊕ Lam d L N)) :=
  compSub (NX2 (nbhd j U : Set (Lam d L N))) (a ∈ nbhd j U ∨ P) (b ∈ nbhd j U ∨ P) ⊓ symSub

variable {c P a b j}

theorem Supp_mono {U U' : Finset (Lam d L N)} (h : U ⊆ U') : Supp c P a b j U ≤ Supp c P a b j U' :=
  inf_le_inf (compSub_mono (NX_mono (coe_subset.2 (nbhd_mono h)))
    (Or.imp_left fun h' => nbhd_mono h h') (Or.imp_left fun h' => nbhd_mono h h')) le_rfl

theorem Supp_succ (U : Finset (Lam d L N)) : Supp c P a b j U ≤ Supp c P a b (j + 1) U :=
  inf_le_inf (compSub_mono (NX_mono (coe_subset.2 (nbhd_subset_nbhd_succ U)))
    (Or.imp_left fun h' => nbhd_subset_nbhd_succ U h')
    (Or.imp_left fun h' => nbhd_subset_nbhd_succ U h')) le_rfl

theorem thetaO_mem_Supp2 {U : Finset (Lam d L N)} {F : OE c (Lam d L N)}
    (hF : F ∈ Supp c P a b j U) : thetaO F ∈ Supp2 c P a b j U := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, hs⟩ := hF
  refine ⟨⟨theta_mem_NX2 h1, theta_mem_NX2 h2, theta_mem_NX2 h3, theta_mem_NX2 h4, ?_, ?_⟩, ?_⟩
  · intro hp; obtain ⟨x, y⟩ := h5 hp
    exact ⟨by simp [x], by simp [y]⟩
  · intro hp; obtain ⟨x, y⟩ := h6 hp
    exact ⟨by simp [x], by simp [y]⟩
  · show IsSymS (thetaS (F : SA c (Lam d L N)))
    rw [IsSymS, scalS_thetaS, (mem_symSub.1 hs : IsSymS _)]

theorem inclO_mem_Supp2 {U : Finset (Lam d L N)} {F : OE c (Lam d L N)}
    (hF : F ∈ Supp c P a b j U) : inclO F ∈ Supp2 c P a b j U := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, hs⟩ := hF
  refine ⟨⟨incl_mem_NX2 h1, incl_mem_NX2 h2, incl_mem_NX2 h3, incl_mem_NX2 h4, ?_, ?_⟩, ?_⟩
  · intro hp; obtain ⟨x, y⟩ := h5 hp
    exact ⟨by simp [x], by simp [y]⟩
  · intro hp; obtain ⟨x, y⟩ := h6 hp
    exact ⟨by simp [x], by simp [y]⟩
  · show IsSymS (inclS (F : SA c (Lam d L N)))
    rw [IsSymS, scalS_inclS, (mem_symSub.1 hs : IsSymS _)]

theorem ECO_mem_Supp (C : Matrix (Lam d L N) (Lam d L N) ℝ) {U : Finset (Lam d L N)}
    {F : OE c (Lam d L N ⊕ Lam d L N)} (hF : F ∈ Supp2 c P a b j U) :
    ECO C F ∈ Supp c P a b j U := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, hs⟩ := hF
  refine ⟨⟨EC_mem_NX C h1, EC_mem_NX C h2, EC_mem_NX C h3, EC_mem_NX C h4, ?_, ?_⟩, ?_⟩
  · intro hp; obtain ⟨x, y⟩ := h5 hp
    exact ⟨by simp [x], by simp [y]⟩
  · intro hp; obtain ⟨x, y⟩ := h6 hp
    exact ⟨by simp [x], by simp [y]⟩
  · show IsSymS (ECS C (F : SA c (Lam d L N ⊕ Lam d L N)))
    rw [IsSymS, scalS_ECS C two_ne_zero, (mem_symSub.1 hs : IsSymS _)]

/-- **Factorisation of `𝔼_C`** with observables, componentwise from `Step.EC_mul_of_sep`. -/
theorem ECO_mul_of_sep {C : Matrix (Lam d L N) (Lam d L N) ℝ} {X₁ X₂ : Set (Lam d L N)}
    (hX : ∀ x ∈ X₁, ∀ y ∈ X₂, x ≠ y ∧ C x y = 0 ∧ C y x = 0) {pa pb pa' pb' : Prop}
    {F G : OE c (Lam d L N ⊕ Lam d L N)} (hF : F ∈ compSub (NX2 X₁) pa pb)
    (hG : G ∈ compSub (NX2 X₂) pa' pb') : ECO C (F * G) = ECO C F * ECO C G := by
  obtain ⟨f1, f2, f3, f4, -, -⟩ := hF
  obtain ⟨g1, g2, g3, g4, -, -⟩ := hG
  have m := fun {x y : Alg2 d L N} (hx : x ∈ NX2 X₁) (hy : y ∈ NX2 X₂) => EC_mul_of_sep hX hx hy
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_)
  · rw [OE.mul_e, coe_ECO, ECS_e, OE.mul_e, coe_ECO, coe_ECO, ECS_e, ECS_e, m f1 g1]
  · rw [OE.mul_a, coe_ECO, ECS_a, OE.mul_a, coe_ECO, coe_ECO, ECS_e, ECS_e, ECS_a, ECS_a, map_add,
      m f1 g2, m f2 g1]
  · rw [OE.mul_b, coe_ECO, ECS_b, OE.mul_b, coe_ECO, coe_ECO, ECS_e, ECS_e, ECS_b, ECS_b, map_add,
      m f1 g3, m f3 g1]
  · rw [OE.mul_ab, coe_ECO, ECS_ab, OE.mul_ab, coe_ECO, coe_ECO, ECS_e, ECS_e, ECS_a, ECS_a,
      ECS_b, ECS_b, ECS_ab, ECS_ab, map_add, map_add, map_add, map_smul, m f1 g4, m f2 g3,
      m f3 g2, m f4 g1]

end Supp

end

end Obs

namespace Obs

noncomputable section

open Finset Grassmann SA Loc Step LocObs Gen

variable {d L N : ℕ} [NeZero L]

/-! ### `U(1)` invariance of the extended `Loc` -/

section LocSym

theorem scal_locOdd (s : ℤˣ) (P X Y : Finset (Lam d L N)) (F : Alg d L N) (t : ℂ) :
    Step.scal _ t (locOdd s P X Y F) = (if s = 1 then t else t⁻¹) • locOdd s P X Y F := by
  simp only [locOdd, locGen, map_smul, map_sum, Step.scal_ψ]
  rw [smul_comm (if s = 1 then t else t⁻¹)]
  congr 1
  rw [Finset.smul_sum]

theorem scal_locEven (P X Y : Finset (Lam d L N)) (F : Alg d L N) :
    Step.scal _ 2 (locEven P X Y F) = locEven P X Y F := by
  simp only [locEven, locGen, map_add, map_smul, map_sum, map_one, pbp,
    scal_psibar_psi 2 two_ne_zero]

theorem isSymS_LocS {c : Case} (a b : Lam d L N) (X Y : Finset (Lam d L N))
    (F : SA c (Lam d L N)) : IsSymS (LocS a b X Y F) := by
  have he : Step.scal _ 2 (LocXY X Y F.e) = LocXY X Y F.e :=
    mem_SymS.1 ((isSym_iff_mem_SymS _).1 (isSym_LocXY X Y F.e))
  cases c
  · rw [isSymS_iff_one]
    refine ⟨he, ?_, ?_, scal_locEven _ _ _ _⟩
    · show Step.scal _ 2 (locOdd (-1) {a} X Y F.a) = _
      rw [scal_locOdd, if_neg units_ne.symm]; rfl
    · show Step.scal _ 2 (locOdd 1 {b} X Y F.b) = _
      rw [scal_locOdd, if_pos rfl]; rfl
  · rw [isSymS_iff_two]
    exact ⟨he, scal_locEven _ _ _ _, scal_locEven _ _ _ _, scal_locEven _ _ _ _⟩

end LocSym

/-! ### Coupling constants and locality -/

/-- The `η` coupling constant (`0` in Case (1)). -/
def etaOf : (c : Case) → Coup c → ℂ
  | .one, _ => 0
  | .two, V => Coup2.eta V

/-- The `ab` coupling constants vanish (`q_a = q_b = r_a = r_b = 0`, resp. additionally
`η = 0`). -/
def AbZero : (c : Case) → Coup c → Prop
  | .one, V => Coup1.qa V = 0 ∧ Coup1.qb V = 0 ∧ Coup1.ra V = 0 ∧ Coup1.rb V = 0
  | .two, V => Coup2.qa V = 0 ∧ Coup2.qb V = 0 ∧ Coup2.eta V = 0 ∧ Coup2.ra V = 0 ∧
      Coup2.rb V = 0

/-- `a` and `b` are close at scale `j`: a block containing one of them has both in its small
set neighbourhood.  (Used only for the factorisation `KnextO_union`.) -/
def Near (j : ℕ) (a b : Lam d L N) : Prop :=
  ∀ p, (a ∈ blockSet j p ∨ b ∈ blockSet j p) →
    a ∈ nbhd j (blockSet j p) ∧ b ∈ nbhd j (blockSet j p)

/-- `a` and `b` are close at scale `j + 1`: a `j`-block containing one of them has both in its
scale-`(j+1)` small set neighbourhood.  This holds as soon as `|a - b|_∞ ≤ L^{j+1}`
(`nearS_of_le`), in particular for `j ≥ j_ab` (`nearS_of_coal_le`). -/
def NearS (j : ℕ) (a b : Lam d L N) : Prop :=
  ∀ p, (a ∈ blockSet j p ∨ b ∈ blockSet j p) →
    a ∈ nbhd (j + 1) (blockSet j p) ∧ b ∈ nbhd (j + 1) (blockSet j p)

/-- Locality of the split evaluation of `W` at scale `j + 1` (the scale of the output
`K_{j+1}`): the nonlocal `η` term vanishes unless `a, b` are close at scale `j + 1`, and (for
`P = False`) the `ab` terms vanish unless `a, b` are close at scale `j + 1`. -/
def CoupLoc (c : Case) (P : Prop) (a b : Lam d L N) (j : ℕ) (W : Coup c) : Prop :=
  (etaOf c W = 0 ∨ NearS j a b) ∧ (P ∨ AbZero c W ∨ NearS j a b)

/-- Locality of the split evaluation of `W` at scale `j` (needed for the factorisation
`KnextO_union` only). -/
def CoupLocSep (c : Case) (P : Prop) (a b : Lam d L N) (j : ℕ) (W : Coup c) : Prop :=
  (etaOf c W = 0 ∨ Near j a b) ∧ (P ∨ AbZero c W ∨ Near j a b)

/-- Points at distance `≤ L^k` from a point of `Y` lie in the scale-`k` small set neighbourhood
of `Y` (their `k`-blocks touch). -/
theorem mem_nbhd_of_le (hd : 1 ≤ d) {k : ℕ} (hk : k ≤ N) {Y : Finset (Lam d L N)}
    {y z : Lam d L N} (hy : y ∈ Y) (hz : supNorm (z - y) ≤ L ^ k) : z ∈ nbhd k Y := by
  classical
  have htouch : Touch (blockSet (L := L) (N := N) k (blk k y)) (blockSet k (blk k z)) := by
    by_contra hT
    have h := lt_supNorm_of_not_touch hk (isPolymer_blockSet k _) (isPolymer_blockSet k _) hT
      (mem_blockSet_blk k y) (mem_blockSet_blk k z)
    rw [FRD.supNorm_sub_comm] at h
    omega
  set S : Finset (Lam d L N) := blockSet k (blk k y) ∪ blockSet k (blk k z) with hSdef
  have hbS : blocks k S ⊆ {blk k y, blk k z} := by
    intro b hb
    obtain ⟨w, hw, rfl⟩ := mem_image.1 hb
    rcases mem_union.1 hw with hw | hw
    · simp [Loc.mem_blockSet.1 hw]
    · simp [Loc.mem_blockSet.1 hw]
  have hyS : y ∈ S := mem_union_left _ (mem_blockSet_blk k y)
  have hzS : z ∈ S := mem_union_right _ (mem_blockSet_blk k z)
  have hadj : ∀ b ∈ blocks k S, ∀ b' ∈ blocks k S, BlockAdj k S b b' := by
    intro b hb b' hb'
    refine ⟨hb, hb', ?_⟩
    rcases mem_insert.1 (hbS hb) with rfl | h1 <;>
      rcases mem_insert.1 (hbS hb') with rfl | h2
    · exact ⟨y, mem_blockSet_blk k y, y, mem_blockSet_blk k y, by simp [supNorm_zero]⟩
    · rw [mem_singleton.1 h2]; exact htouch
    · rw [mem_singleton.1 h1]; exact touch_symm htouch
    · rw [mem_singleton.1 h1, mem_singleton.1 h2]
      exact ⟨z, mem_blockSet_blk k z, z, mem_blockSet_blk k z, by simp [supNorm_zero]⟩
  have hsmall : IsSmall k S := by
    refine ⟨?_, ⟨⟨y, hyS⟩, fun b hb b' hb' => Relation.ReflTransGen.single (hadj b hb b' hb')⟩,
      ?_⟩
    · intro w w' hww' hw
      rcases mem_union.1 hw with hw | hw
      · exact mem_union_left _ (Loc.mem_blockSet.2 (hww'.symm.trans (Loc.mem_blockSet.1 hw)))
      · exact mem_union_right _ (Loc.mem_blockSet.2 (hww'.symm.trans (Loc.mem_blockSet.1 hw)))
    · refine (card_le_card hbS).trans ((card_insert_le _ _).trans ?_)
      simp only [card_singleton]
      calc 1 + 1 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
  simp only [nbhd, mem_filter, mem_univ, true_and]
  exact ⟨S, hsmall, hzS, blk k y, blk_mem_blocks hy, subset_union_left⟩

theorem nearS_of_le (hd : 1 ≤ d) {j : ℕ} (hj : j + 1 ≤ N) {a b : Lam d L N}
    (hab : supNorm (a - b) ≤ L ^ (j + 1)) : NearS j a b := by
  have h0 : ∀ x : Lam d L N, supNorm (x - x) ≤ L ^ (j + 1) := fun x => by simp [supNorm_zero]
  intro p hp
  rcases hp with ha | hb
  · exact ⟨mem_nbhd_of_le hd hj ha (h0 a),
      mem_nbhd_of_le hd hj ha (by rwa [FRD.supNorm_sub_comm])⟩
  · exact ⟨mem_nbhd_of_le hd hj hb hab, mem_nbhd_of_le hd hj hb (h0 b)⟩

theorem etaOf_toV (c : Case) (W : Coup c) : etaOf c (Coup.toV c W) = etaOf c W := by
  cases c <;> rfl

theorem etaOf_toU (c : Case) (W : Coup c) : etaOf c (Coup.toU c W) = 0 := by
  cases c <;> rfl

theorem coupLoc_true_of_eta {c : Case} {a b : Lam d L N} {j : ℕ} {W : Coup c}
    (h : etaOf c W = 0 ∨ NearS j a b) : CoupLoc c True a b j W :=
  ⟨h, Or.inl trivial⟩

/-! ### Memberships of the ingredients -/

section Mem

variable {c : Case} {P : Prop} {a b : Lam d L N} {j : ℕ}

theorem ψ_mem_nbhd {U : Finset (Lam d L N)} {x : Lam d L N} (hx : x ∈ nbhd j U) (s : ℤˣ) :
    ψ (x, s) ∈ NX (nbhd j U : Set (Lam d L N)) := ψ_mem_NX (Finset.mem_coe.2 hx)

theorem pbp_mem_nbhd {U : Finset (Lam d L N)} {x : Lam d L N} (hx : x ∈ nbhd j U) :
    psibar x * psi x ∈ NX (nbhd j U : Set (Lam d L N)) :=
  mul_mem (ψ_mem_nbhd hx _) (ψ_mem_nbhd hx _)

/-- The extended `Loc` maps into the supports. -/
theorem LocO_mem_Supp (hd : 1 ≤ d) {U : Finset (Lam d L N)} {p : Fin d → ℕ}
    (hBU : blockSet j p ⊆ U) (Y : Finset (Lam d L N)) (F : OE c (Lam d L N))
    (hF : ¬ P → (F : SA c (Lam d L N)).ab = 0) :
    LocO a b Y (blockSet j p) F ∈ Supp c P a b j U := by
  have hB := isPolymer_blockSet (L := L) (N := N) j p
  have hBn : ((blockSet (L := L) (N := N) j p : Finset (Lam d L N)) : Set (Lam d L N)) ⊆
      (nbhd j U : Set (Lam d L N)) :=
    coe_subset.2 ((subset_nbhd hB).trans (nbhd_mono hBU))
  have hnU : ((nbhd j (blockSet (L := L) (N := N) j p) : Finset (Lam d L N)) : Set (Lam d L N)) ⊆
      (nbhd j U : Set (Lam d L N)) :=
    coe_subset.2 (nbhd_mono hBU)
  have hi : ∀ Q : Finset (Lam d L N), ((blockSet j p ∩ Q : Finset (Lam d L N)) : Set (Lam d L N)) ⊆
      (nbhd j U : Set (Lam d L N)) := fun Q => (coe_subset.2 inter_subset_left).trans hBn
  have hz : ∀ x : Lam d L N, ¬ (x ∈ nbhd j U ∨ P) → blockSet j p ∩ {x} = ∅ := fun x hx =>
    inter_singleton_of_not_mem fun h => hx (Or.inl (hBn h))
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, mem_symSub.2 (isSymS_LocS a b Y _ _)⟩
  · exact NX_mono hnU (LocXY_mem hd hB Y _)
  · exact NX_mono (hi _) (locA_mem _ a Y _ _)
  · exact NX_mono (hi _) (locB_mem _ b Y _ _)
  · exact NX_mono (hi _) (locAB_mem a b Y _ _)
  · intro hp
    have hP : ¬ P := fun h => hp (Or.inr h)
    refine ⟨?_, ?_⟩
    · show locA c.toObs a Y (blockSet j p) (F : SA c (Lam d L N)).a = 0
      cases c <;> simp [Case.toObs, locA, locOdd, locEven, locGen, hz a hp]
    · show locAB a b Y (blockSet j p) (F : SA c (Lam d L N)).ab = 0
      rw [hF hP]; exact locEven_zero _ _ _
  · intro hp
    have hP : ¬ P := fun h => hp (Or.inr h)
    refine ⟨?_, ?_⟩
    · show locB c.toObs b Y (blockSet j p) (F : SA c (Lam d L N)).b = 0
      cases c <;> simp [Case.toObs, locB, locOdd, locEven, locGen, hz b hp]
    · show locAB a b Y (blockSet j p) (F : SA c (Lam d L N)).ab = 0
      rw [hF hP]; exact locEven_zero _ _ _

/-- `J(B, X)` lies in the supports. -/
theorem JO_mem_Supp (hd : 1 ≤ d) {K : Finset (Lam d L N) → OE c (Lam d L N)}
    (hKab : ¬ P → ∀ Y, IsSmall j Y → (K Y : SA c (Lam d L N)).ab = 0) {U : Finset (Lam d L N)}
    {p : Fin d → ℕ} (hBU : blockSet j p ⊆ U) (X : Finset (Lam d L N)) :
    JO a b j K p X ∈ Supp c P a b j U := by
  unfold JO
  split_ifs with h1 h2
  · refine neg_mem (Subalgebra.sum_mem _ fun Y hY => ?_)
    exact LocO_mem_Supp hd hBU Y _ fun hP =>
      hKab hP Y (mem_smallSets.1 (mem_filter.1 hY).1)
  · exact LocO_mem_Supp hd hBU X _ fun hP => hKab hP X h1.2.1
  · exact zero_mem _

theorem isSymS_halfA (c : Case) (W : Coup c) (a b : Lam d L N) : IsSymS (halfA c W a b) := by
  cases c
  · rw [isSymS_iff_one]
    refine ⟨by simp [halfA], ?_, by simp [halfA], ?_⟩ <;>
      simp only [halfA, map_smul, map_add, AlgHom.commutes, scal_psibar_psi 2 two_ne_zero]
    rw [psibar, Step.scal_ψ, if_neg units_ne.symm, smul_comm (2⁻¹ : ℂ)]
  · rw [isSymS_iff_two]
    refine ⟨by simp [halfA], ?_, by simp [halfA], ?_⟩ <;>
      simp only [halfA, map_smul, map_add, map_sub, AlgHom.commutes, scal_nx,
        scal_psibar_psi 2 two_ne_zero]

theorem isSymS_halfB (c : Case) (W : Coup c) (a b : Lam d L N) : IsSymS (halfB c W a b) := by
  cases c
  · rw [isSymS_iff_one]
    refine ⟨by simp [halfB], by simp [halfB], ?_, ?_⟩ <;>
      simp only [halfB, map_smul, map_add, AlgHom.commutes, scal_psibar_psi 2 two_ne_zero]
    rw [psi, Step.scal_ψ, if_pos rfl, smul_comm (2 : ℂ)]
  · rw [isSymS_iff_two]
    refine ⟨by simp [halfB], by simp [halfB], ?_, ?_⟩ <;>
      simp only [halfB, map_smul, map_add, map_sub, AlgHom.commutes, scal_nx,
        scal_psibar_psi 2 two_ne_zero]

theorem nx_term_mem {U : Finset (Lam d L N)} {a b : Lam d L N} (ha : a ∈ nbhd j U) (e : ℂ)
    (h : e = 0 ∨ b ∈ nbhd j U) : e • nx a b ∈ NX (nbhd j U : Set (Lam d L N)) := by
  rcases h with h | h
  · rw [h, zero_smul]; exact zero_mem _
  · exact Subalgebra.smul_mem _ (add_mem (mul_mem (ψ_mem_nbhd ha _) (ψ_mem_nbhd h _))
      (mul_mem (ψ_mem_nbhd h _) (ψ_mem_nbhd ha _))) _

theorem halfAO_mem_Supp {U : Finset (Lam d L N)} (W : Coup c) (ha : a ∈ nbhd j U)
    (hη : etaOf c W = 0 ∨ b ∈ nbhd j U) (hP : P ∨ AbZero c W ∨ b ∈ nbhd j U) :
    halfAO c W a b ∈ Supp c P a b j U := by
  refine ⟨⟨?_, ?_, ?_, ?_, fun h => absurd (Or.inl ha) h, ?_⟩, mem_symSub.2 (isSymS_halfA c W a b)⟩
  · cases c <;> exact zero_mem _
  · cases c
    · exact Subalgebra.smul_mem _ (ψ_mem_nbhd ha _) _
    · exact sub_mem (Subalgebra.algebraMap_mem _ _) (Subalgebra.smul_mem _ (pbp_mem_nbhd ha) _)
  · cases c <;> exact zero_mem _
  · cases c
    · exact add_mem (Subalgebra.algebraMap_mem _ _)
        (Subalgebra.smul_mem _ (pbp_mem_nbhd ha) _)
    · exact add_mem (sub_mem (Subalgebra.algebraMap_mem _ _)
        (nx_term_mem ha _ (hη.imp (fun h => by simp only [etaOf] at h; rw [h, zero_div]) id)))
        (Subalgebra.smul_mem _ (pbp_mem_nbhd ha) _)
  · intro hb
    have hz : AbZero c W := by
      rcases hP with h | h | h
      · exact absurd (Or.inr h) hb
      · exact h
      · exact absurd (Or.inl h) hb
    refine ⟨by cases c <;> rfl, ?_⟩
    cases c
    · obtain ⟨h1, -, h3, -⟩ := hz
      show algebraMap ℂ _ (-Coup1.qa W) + Coup1.ra W • _ = 0
      rw [h1, h3]; simp
    · obtain ⟨h1, -, h3, h4, -⟩ := hz
      show algebraMap ℂ _ (-Coup2.qa W) - (Coup2.eta W / 4) • nx a b + Coup2.ra W • _ = 0
      rw [h1, h3, h4]; simp

theorem halfBO_mem_Supp {U : Finset (Lam d L N)} (W : Coup c) (hb : b ∈ nbhd j U)
    (hη : etaOf c W = 0 ∨ a ∈ nbhd j U) (hP : P ∨ AbZero c W ∨ a ∈ nbhd j U) :
    halfBO c W a b ∈ Supp c P a b j U := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, fun h => absurd (Or.inl hb) h⟩, mem_symSub.2 (isSymS_halfB c W a b)⟩
  · cases c <;> exact zero_mem _
  · cases c <;> exact zero_mem _
  · cases c
    · exact Subalgebra.smul_mem _ (ψ_mem_nbhd hb _) _
    · exact sub_mem (Subalgebra.algebraMap_mem _ _) (Subalgebra.smul_mem _ (pbp_mem_nbhd hb) _)
  · cases c
    · exact add_mem (Subalgebra.algebraMap_mem _ _)
        (Subalgebra.smul_mem _ (pbp_mem_nbhd hb) _)
    · have hx : nx a b = nx b a := by rw [nx, nx, add_comm]
      refine add_mem (sub_mem (Subalgebra.algebraMap_mem _ _) ?_)
        (Subalgebra.smul_mem _ (pbp_mem_nbhd hb) _)
      rw [hx]
      exact nx_term_mem hb _ (hη.imp (fun h => by simp only [etaOf] at h; rw [h, zero_div]) id)
  · intro ha
    have hz : AbZero c W := by
      rcases hP with h | h | h
      · exact absurd (Or.inr h) ha
      · exact h
      · exact absurd (Or.inl h) ha
    refine ⟨by cases c <;> rfl, ?_⟩
    cases c
    · obtain ⟨-, h2, -, h4⟩ := hz
      show algebraMap ℂ _ (-Coup1.qb W) + Coup1.rb W • _ = 0
      rw [h2, h4]; simp
    · obtain ⟨-, h2, h3, -, h5⟩ := hz
      show algebraMap ℂ _ (-Coup2.qb W) - (Coup2.eta W / 4) • nx a b + Coup2.rb W • _ = 0
      rw [h2, h3, h5]; simp

/-- The split evaluation at a block lies in the supports. -/
theorem splitO_mem_Supp (W : Coup c) (hW : CoupLocSep c P a b j W) (p : Fin d → ℕ) :
    splitO c W a b (blockSet j p) ∈ Supp c P a b j (blockSet j p) := by
  have hB := isPolymer_blockSet (L := L) (N := N) j p
  obtain ⟨hη, hP⟩ := hW
  refine add_mem ?_ ?_
  · by_cases ha : a ∈ blockSet j p
    · rw [ind_pos ha, one_smul]
      have hn := fun h : Near j a b => (h p (Or.inl ha)).2
      exact halfAO_mem_Supp W (subset_nbhd hB ha) (hη.imp id hn) (hP.imp id (Or.imp id hn))
    · rw [ind_neg ha, zero_smul]; exact zero_mem _
  · by_cases hb : b ∈ blockSet j p
    · rw [ind_pos hb, one_smul]
      have hn := fun h : Near j a b => (h p (Or.inr hb)).1
      exact halfBO_mem_Supp W (subset_nbhd hB hb) (hη.imp id hn) (hP.imp id (Or.imp id hn))
    · rw [ind_neg hb, zero_smul]; exact zero_mem _

/-- The split evaluation at a `j`-block lies in the scale-`(j+1)` supports. -/
theorem splitO_mem_Supp_succ (W : Coup c) (hW : CoupLoc c P a b j W) (p : Fin d → ℕ) :
    splitO c W a b (blockSet j p) ∈ Supp c P a b (j + 1) (blockSet j p) := by
  have hB := isPolymer_blockSet (L := L) (N := N) j p
  have hs : ∀ {x : Lam d L N}, x ∈ blockSet (L := L) (N := N) j p →
      x ∈ nbhd (j + 1) (blockSet j p) := fun hx => nbhd_subset_nbhd_succ _ (subset_nbhd hB hx)
  obtain ⟨hη, hP⟩ := hW
  refine add_mem ?_ ?_
  · by_cases ha : a ∈ blockSet j p
    · rw [ind_pos ha, one_smul]
      have hn := fun h : NearS j a b => (h p (Or.inl ha)).2
      exact halfAO_mem_Supp W (hs ha) (hη.imp id hn) (hP.imp id (Or.imp id hn))
    · rw [ind_neg ha, zero_smul]; exact zero_mem _
  · by_cases hb : b ∈ blockSet j p
    · rw [ind_pos hb, one_smul]
      have hn := fun h : NearS j a b => (h p (Or.inr hb)).1
      exact halfBO_mem_Supp W (hs hb) (hη.imp id hn) (hP.imp id (Or.imp id hn))
    · rw [ind_neg hb, zero_smul]; exact zero_mem _

theorem emb_VE_mem_Supp (hd : 1 ≤ d) (V : Vcoup) (p : Fin d → ℕ) :
    (emb (VE V (blockSet j p)) : OE c (Lam d L N)) ∈ Supp c P a b j (blockSet j p) := by
  refine ⟨⟨eval_mem_NX hd (isPolymer_blockSet j p) V, zero_mem _, zero_mem _, zero_mem _,
    fun _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩⟩, mem_symSub.2 ?_⟩
  have h := mem_SymS.1 ((isSym_iff_mem_SymS _).1 (isSym_eval V (blockSet (L := L) (N := N) j p)))
  cases c
  · rw [isSymS_iff_one]; exact ⟨h, by simp, by simp, by simp⟩
  · rw [isSymS_iff_two]; exact ⟨h, by simp, by simp, by simp⟩

theorem VfullX_mem_Supp (hd : 1 ≤ d) (V : Vcoup) (W : Coup c)
    (hW : CoupLocSep c P a b j (Coup.toV c W)) (p : Fin d → ℕ) :
    VfullX V W a b (blockSet j p) ∈ Supp c P a b j (blockSet j p) :=
  add_mem (emb_VE_mem_Supp hd V p) (splitO_mem_Supp _ hW p)

theorem VfullX_mem_Supp_succ (hd : 1 ≤ d) (V : Vcoup) (W : Coup c)
    (hW : CoupLoc c P a b j (Coup.toV c W)) (p : Fin d → ℕ) :
    VfullX V W a b (blockSet j p) ∈ Supp c P a b (j + 1) (blockSet j p) :=
  add_mem (Supp_succ _ (emb_VE_mem_Supp hd V p)) (splitO_mem_Supp_succ _ hW p)

end Mem

/-! ### The support hypotheses of the generic map -/

section Hyp

variable {c : Case} {P : Prop} {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℝ} {Vb : Vcoup}
  {Vo : Coup c} {K : Finset (Lam d L N) → OE c (Lam d L N)} {a b : Lam d L N}

/-- The analogue of `𝒦_j` membership (locality and `U(1)` invariance with observables):
`K(X) ∈ 𝒩^obs_sym(X^□)` for connected `X` (`P = False`), resp. componentwise locality
(`P = True`). -/
def InKO (c : Case) (P : Prop) (a b : Lam d L N) (j : ℕ) (K : Finset (Lam d L N) → OE c (Lam d L N)) :
    Prop :=
  ∀ X, IsConn j X → K X ∈ Supp c P a b j X

/-- The hypotheses under which the ingredients lie in the scale-`(j+1)` supports (and hence
`K_{j+1}` does): `InKO` for `K`, and the scale-`(j+1)` locality `CoupLoc` of the split
evaluations of `V^obs_j`, `V^obs_{j+1}`, `u^obs_{j+1}` (in Case (2) with `P = True`:
`η = 0` or `NearS j a b`, which holds for `j ≥ j_ab`). -/
structure ObsLoc (c : Case) (P : Prop) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℝ)
    (Vo : Coup c) (K : Finset (Lam d L N) → OE c (Lam d L N)) (a b : Lam d L N) : Prop where
  hK : InKO c P a b j K
  hKab : ¬ P → ∀ Y, IsSmall j Y → (K Y : SA c (Lam d L N)).ab = 0
  hV : CoupLoc c P a b j (Coup.toV c Vo)
  hV' : CoupLoc c P a b j (Coup.toV c (nextObs C j Vo K a b))
  hu : CoupLoc c P a b j (Coup.toU c (nextObs C j Vo K a b))

/-- The stronger hypotheses (scale-`j` locality `CoupLocSep` of the split evaluations) under
which the ingredients lie in the scale-`j` supports; needed for the factorisation
`KnextO_union` only. -/
structure ObsLocSep (c : Case) (P : Prop) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℝ)
    (Vo : Coup c) (K : Finset (Lam d L N) → OE c (Lam d L N)) (a b : Lam d L N) : Prop where
  hK : InKO c P a b j K
  hKab : ¬ P → ∀ Y, IsSmall j Y → (K Y : SA c (Lam d L N)).ab = 0
  hV : CoupLocSep c P a b j (Coup.toV c Vo)
  hV' : CoupLocSep c P a b j (Coup.toV c (nextObs C j Vo K a b))
  hu : CoupLocSep c P a b j (Coup.toU c (nextObs C j Vo K a b))

/-- The support hypotheses of the generic map with the scale-`(j+1)` supports. -/
theorem ObsLoc.suppHyp (hd : 1 ≤ d) (h : ObsLoc c P j C Vo K a b) :
    SuppHyp (obsA c C) j (obsI j C Vb Vo K a b) (Supp c P a b (j + 1)) (Supp2 c P a b (j + 1)) where
  hθ _ _ hF := thetaO_mem_Supp2 hF
  hι _ _ hF := inclO_mem_Supp2 hF
  hK _ Y hY hYU := Supp_mono hYU (Supp_succ _ (h.hK Y hY))
  hJ _ _ Y hb hYU := Supp_succ _ (JO_mem_Supp hd h.hKab (hb.trans hYU) Y)
  hI0 _ p hb := Supp_mono hb (oexp_mem _ (neg_mem (VfullX_mem_Supp_succ hd Vb Vo h.hV p))
    (isNilpotent_VfullX a b _ _ _).neg)
  heV _ p hb := Supp_mono hb (oexp_mem _ (neg_mem (VfullX_mem_Supp_succ hd _ _ h.hV' p))
    (isNilpotent_VfullX a b _ _ _).neg)
  heum _ p hb := Supp_mono hb (mul_mem (Subalgebra.algebraMap_mem _ _)
    (oexp_mem _ (neg_mem (splitO_mem_Supp_succ _ h.hu p))
      (isNilpotent_of_obs (bulk_uObsX j C Vo K a b _)).neg))

theorem ObsLoc.eu_mem (h : ObsLoc c P j C Vo K a b) {U : Finset (Lam d L N)} (p : Fin d → ℕ)
    (hb : blockSet j p ⊆ U) : (obsI j C Vb Vo K a b).eu p ∈ Supp c P a b (j + 1) U :=
  Supp_mono hb (mul_mem (Subalgebra.algebraMap_mem _ _)
    (oexp_mem _ (splitO_mem_Supp_succ _ h.hu p) (isNilpotent_of_obs (bulk_uObsX j C Vo K a b _))))

/-- The support hypotheses of the generic map with the scale-`j` supports (for the
factorisation). -/
theorem ObsLocSep.suppHyp (hd : 1 ≤ d) (h : ObsLocSep c P j C Vo K a b) :
    SuppHyp (obsA c C) j (obsI j C Vb Vo K a b) (Supp c P a b j) (Supp2 c P a b j) where
  hθ _ _ hF := thetaO_mem_Supp2 hF
  hι _ _ hF := inclO_mem_Supp2 hF
  hK _ Y hY hYU := Supp_mono hYU (h.hK Y hY)
  hJ _ _ Y hb hYU := JO_mem_Supp hd h.hKab (hb.trans hYU) Y
  hI0 _ p hb := Supp_mono hb (oexp_mem _ (neg_mem (VfullX_mem_Supp hd Vb Vo h.hV p))
    (isNilpotent_VfullX a b _ _ _).neg)
  heV _ p hb := Supp_mono hb (oexp_mem _ (neg_mem (VfullX_mem_Supp hd _ _ h.hV' p))
    (isNilpotent_VfullX a b _ _ _).neg)
  heum _ p hb := Supp_mono hb (mul_mem (Subalgebra.algebraMap_mem _ _)
    (oexp_mem _ (neg_mem (splitO_mem_Supp _ h.hu p))
      (isNilpotent_of_obs (bulk_uObsX j C Vo K a b _)).neg))

/-- **Locality and `U(1)` invariance of `K_{j+1}`** (scale-`(j+1)` neighbourhood). -/
theorem KnextO_mem_Supp (hd : 1 ≤ d) (h : ObsLoc c P j C Vo K a b) {U : Finset (Lam d L N)}
    (hU : IsPolymer (j + 1) U) : KnextO j C Vb Vo K a b U ∈ Supp c P a b (j + 1) U :=
  (h.suppHyp (Vb := Vb) hd).KnextG_mem hU (fun _ hf => ECO_mem_Supp C hf)
    fun p hp => h.eu_mem p hp

/-- **The analogue of `𝒦_{j+1}` membership is preserved**: `K_{j+1}(U) ∈ 𝒩^obs_sym(U^□)` for
connected `(j+1)`-polymers (`U^□` at scale `j + 1`). -/
theorem InKO_KnextO (hd : 1 ≤ d) (h : ObsLoc c P j C Vo K a b) :
    InKO c P a b (j + 1) (KnextO j C Vb Vo K a b) :=
  fun _ hU => KnextO_mem_Supp hd h hU.1

/-- **Factorisation** (Proposition `prop:ZVK`): `K_{j+1}(U₁ ∪ U₂) = K_{j+1}(U₁) K_{j+1}(U₂)` for
non-touching `(j+1)`-polymers. -/
theorem KnextO_union (hd : 1 ≤ d) (hL : 2 ^ (d + 2) ≤ L) (hj : j + 1 ≤ N) {ℓ₀ : ℝ}
    (hC : GoodCov j ℓ₀ C) (h : ObsLocSep c P j C Vo K a b) {U₁ U₂ : Finset (Lam d L N)}
    (hU₁ : IsPolymer (j + 1) U₁) (hU₂ : IsPolymer (j + 1) U₂) (hT : ¬ Touch U₁ U₂) :
    KnextO j C Vb Vo K a b (U₁ ∪ U₂) = KnextO j C Vb Vo K a b U₁ * KnextO j C Vb Vo K a b U₂ :=
  KnextG_union hd hL hj hU₁ hU₂ hT (h.suppHyp hd) fun _ hf _ hg =>
    ECO_mul_of_sep (fun _ hx _ hy => C_eq_zero_of_nbhd hL hj hC hU₁ hU₂ hT hx hy)
      (Algebra.mem_inf.1 hf).1 (Algebra.mem_inf.1 hg).1

end Hyp

end

end Obs
