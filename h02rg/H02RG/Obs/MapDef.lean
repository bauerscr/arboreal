import Obs.MapCoupling

/-!
# The observable renormalisation group map (Section `sec:rgmap-ext`)

The renormalisation group map with observables is the generic map of `Obs.GenericDefs` with
* the algebra `R = OE c Λ` (even elements with source fields), `R2 = OE c (Λ ⊔ Λ)`,
  `θ = thetaO`, `ι = inclO`, `E = 𝔼_{C_{j+1}} = ECO C` (`obsA C`);
* the ingredients (`obsI`), for the input `(V_j, K_j)` with bulk coupling constants `Vb`,
  observable coupling constants `Vo` (only their `V` part is used) and `K : Finset Λ → OE`:
  - `I0 B = e^{-V_j(B)}`, `V_j(B) = V^∅_j(B) + V^obs_j(B)` (`Vfull`, split evaluation);
  - `(u_{j+1}, V_{j+1})`: bulk part `Step.uVnext j C Vb K^∅` (Step's bulk map), observable part
    `nextObs C j Vo K a b` (Definition `def:V+obs`), with `V^obs_{j+1} = Coup.toV nextObs`,
    `u^obs_{j+1} = Coup.toU nextObs`; `eV B = e^{-V_{j+1}(B)}`,
    `eu B = e^{u_{j+1}(B)}`, `eum B = e^{-u_{j+1}(B)}` (the bulk `u` is a constant, whose
    exponential is `Complex.exp`);
  - `J = JO` (the extended `J(B, X)`), `K = K`.
* `KnextO … U = K_{j+1}(U)` (`= K^∅_{j+1}(U) + K^obs_{j+1}(U)`, Definition `def:V+obs`).

## Results
* **Upper-triangular structure** (`bulk_KnextO`): `π_∅ K_{j+1} = Step.Knext j C (π_∅ V_j)
  (π_∅ K_j)`, i.e. `π_∅ Φ_{j+1}(V, K) = Φ^∅_{j+1}(π_∅ V, π_∅ K)`; the bulk coupling constants
  are Step's `uVnext` by definition.  (Proof: `map_KnextG` for the ring hom `bulk`.)
* **Proposition `prop:ZVK`** for the observable map (`ZVK_obs`, `ZVK_obs'`):
  `𝔼 θ Z_j = e^{-u_{j+1}(Λ)} ∑_{U ∈ 𝒫_{j+1}} e^{-V_{j+1}(Λ ∖ U)} K_{j+1}(U)` with
  `Z_j = ∑_{X ∈ 𝒫_j} e^{-V_j(Λ ∖ X)} K_j(X)` (`e:ZVK` with the extended `u, V`).
-/

namespace Obs

noncomputable section

open Finset Grassmann SA Loc Step LocObs Gen

variable {d L N : ℕ} [NeZero L]

/-! ### The data -/

/-- The algebraic data of the observable map. -/
def obsA (c : Case) (C : Matrix (Lam d L N) (Lam d L N) ℝ) :
    RGAlg (OE c (Lam d L N)) (OE c (Lam d L N ⊕ Lam d L N)) where
  θ := thetaO
  ι := inclO
  E := ECO C

section Ingr

variable {c : Case} (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (Vb : Vcoup) (Vo : Coup c)
  (K : Finset (Lam d L N) → OE c (Lam d L N)) (a b : Lam d L N)

/-- The bulk component `K^∅ = π_∅ K`. -/
def bulkK (K : Finset (Lam d L N) → OE c (Lam d L N)) : Act d L N := fun X => bulk (K X)

/-- `V_j(X) = V^∅_j(X) + V^obs_j(X)` (split evaluation of the `V` part of `Vo`). -/
def VfullX (Vb : Vcoup) (Vo : Coup c) (a b : Lam d L N) (X : Finset (Lam d L N)) :
    OE c (Lam d L N) :=
  emb (VE Vb X) + splitO c (Coup.toV c Vo) a b X

/-- The bulk coupling constants `(u^∅_{j+1}, V^∅_{j+1})` (Step's map). -/
def uVb : ℂ × Vcoup := uVnext j C Vb (bulkK K)

/-- `u^obs_{j+1}(X)`. -/
def uObsX (X : Finset (Lam d L N)) : OE c (Lam d L N) :=
  splitO c (Coup.toU c (nextObs C j Vo K a b)) a b X

/-- The ingredients of the observable map. -/
def obsI : RGIngr d L N (OE c (Lam d L N)) where
  I0 p := oexp (-VfullX Vb Vo a b (blockSet j p))
  eV p := oexp (-VfullX (uVb j C Vb K).2 (nextObs C j Vo K a b) a b (blockSet j p))
  eu p := algebraMap ℂ (OE c (Lam d L N))
      (Complex.exp ((uVb j C Vb K).1 * (blockSet (L := L) (N := N) j p).card)) *
    oexp (uObsX j C Vo K a b (blockSet j p))
  eum p := algebraMap ℂ (OE c (Lam d L N))
      (Complex.exp (-((uVb j C Vb K).1 * (blockSet (L := L) (N := N) j p).card))) *
    oexp (-uObsX j C Vo K a b (blockSet j p))
  J := JO a b j K
  K := K

/-- `K_{j+1}(U)`: the observable renormalisation group map (Definition `def:V+obs`). -/
def KnextO (U : Finset (Lam d L N)) : OE c (Lam d L N) :=
  KnextG (obsA c C) j (obsI j C Vb Vo K a b) U

end Ingr

/-! ### Basic facts -/

section Basic

variable {c : Case} (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (Vb : Vcoup) (Vo : Coup c)
  (K : Finset (Lam d L N) → OE c (Lam d L N)) (a b : Lam d L N)

theorem ε_VE (V : Vcoup) (X : Finset (Lam d L N)) : ε ((VE V X : EvR (Lam d L N)) : Alg d L N) = 0 :=
  Step.Coup.eval_ε0 V X

theorem VfullX_e (V : Vcoup) (W : Coup c) (X : Finset (Lam d L N)) :
    ((VfullX V W a b X : OE c (Lam d L N)) : SA c (Lam d L N)).e = V.eval X := by
  rw [← coe_bulk, VfullX, map_add, bulk_emb, bulk_splitO, add_zero, coe_VE]

theorem ε_neg_VfullX (V : Vcoup) (W : Coup c) (X : Finset (Lam d L N)) :
    ε ((-VfullX V W a b X : OE c (Lam d L N)) : SA c (Lam d L N)).e = 0 := by
  rw [NegMemClass.coe_neg, SA.neg_e, VfullX_e, map_neg, Step.Coup.eval_ε0, neg_zero]

theorem isNilpotent_VfullX (V : Vcoup) (W : Coup c) (X : Finset (Lam d L N)) :
    IsNilpotent (VfullX V W a b X) := by
  have h : ε ((VfullX V W a b X : OE c (Lam d L N)) : SA c (Lam d L N)).e = 0 := by
    rw [VfullX_e, Step.Coup.eval_ε0]
  exact isNilpotent_of_ε h

theorem bulk_VfullX (V : Vcoup) (W : Coup c) (X : Finset (Lam d L N)) :
    bulk (VfullX V W a b X) = VE V X := by
  rw [VfullX, map_add, bulk_emb, bulk_splitO, add_zero]

theorem bulk_uObsX (X : Finset (Lam d L N)) : bulk (uObsX j C Vo K a b X) = 0 :=
  bulk_splitO _ _ _ _ _

theorem bulk_oexp_obs {F : OE c (Lam d L N)} (hF : bulk F = 0) : bulk (oexp F) = 1 := by
  rw [bulk_oexp (ε_bulk_eq_zero_of_obs hF), hF, gexp, IsNilpotent.exp_zero]

theorem eu_mul_eum (p : Fin d → ℕ) :
    (obsI j C Vb Vo K a b).eu p * (obsI j C Vb Vo K a b).eum p = 1 := by
  simp only [obsI]
  rw [mul_mul_mul_comm, ← map_mul, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero,
    map_one, one_mul, ← oexp_add (isNilpotent_of_obs (bulk_uObsX j C Vo K a b _))
      (isNilpotent_of_obs (by rw [map_neg, bulk_uObsX, neg_zero])), add_neg_cancel, oexp_zero]

theorem obsI_hJ (p : Fin d → ℕ) (X : Finset (Lam d L N)) (hX : ¬ IsSmall j X) :
    (obsI j C Vb Vo K a b).J p X = 0 :=
  JO_of_not_small a b j K p hX

theorem obsA_hE (a' : OE c (Lam d L N)) (g : OE c (Lam d L N ⊕ Lam d L N)) :
    (obsA c C).E ((obsA c C).ι a' * g) = a' * (obsA c C).E g :=
  ECO_inclO_mul C a' g

theorem obsA_hE1 : (obsA c C).E 1 = 1 := ECO_one C

end Basic

/-! ### The bulk component: upper-triangular structure -/

section Bulk

variable {c : Case} (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (Vb : Vcoup) (Vo : Coup c)
  (K : Finset (Lam d L N) → OE c (Lam d L N)) (a b : Lam d L N)

/-- The bulk components of the ingredients are the bulk ingredients. -/
theorem map_bulk_obsI : (obsI j C Vb Vo K a b).map (fun F => bulk F) = bulkI j C Vb (bulkK K) := by
  simp only [RGIngr.map, obsI, bulkI]
  congr 1
  · funext p
    rw [bulk_oexp (ε_neg_VfullX a b _ _ _), map_neg, bulk_VfullX]
  · funext p
    rw [bulk_oexp (ε_neg_VfullX a b _ _ _), map_neg, bulk_VfullX]; rfl
  · funext p
    rw [map_mul, AlgHom.commutes, bulk_oexp_obs (bulk_uObsX j C Vo K a b _), mul_one]; rfl
  · funext p
    rw [map_mul, AlgHom.commutes,
      bulk_oexp_obs (by rw [map_neg, bulk_uObsX, neg_zero]), mul_one]; rfl
  · funext p X
    exact bulk_JO a b j K p X

/-- **Upper-triangular structure**: `π_∅ K_{j+1}(U) = K^∅_{j+1}(U)` computed by Step's bulk map
from `(π_∅ V_j, π_∅ K_j)`, for `j`-polymers `U` (i.e. `π_∅ Φ_{j+1}(V, K) =
Φ^∅_{j+1}(π_∅ V, π_∅ K)`). -/
theorem bulk_KnextO {U : Finset (Lam d L N)} (hU : IsPolymer j U) :
    bulk (KnextO j C Vb Vo K a b U) = Knext j C Vb (bulkK K) U := by
  rw [KnextO, map_KnextG (A := obsA c C) (A' := bulkA C) bulk bulk (fun x => bulk_thetaO x)
    (fun x => bulk_inclO x) (fun y => bulk_ECO C y), map_bulk_obsI, KnextG_bulk j C Vb _ hU]

end Bulk

/-! ### Proposition `prop:ZVK` -/

section ZVK

variable {c : Case} (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (Vb : Vcoup) (Vo : Coup c)
  (K : Finset (Lam d L N) → OE c (Lam d L N)) (a b : Lam d L N)

/-- **Proposition `prop:ZVK`** for the observable map, in the form of the generic map:
`𝔼_C θ Z_j = e^{-u_{j+1}(Λ)} ∑_U e^{-V_{j+1}(Λ ∖ U)} K_{j+1}(U)`. -/
theorem ZVK_obs :
    ECO C (thetaO (ZjG j (obsI j C Vb Vo K a b))) = ZnextG (obsA c C) j (obsI j C Vb Vo K a b) :=
  ZVK_G (obsA c C) j _ (obsA_hE C) (obsI_hJ j C Vb Vo K a b)
    fun p _ => eu_mul_eum j C Vb Vo K a b p

theorem oexp_neg_sum {ι : Type*} (s : Finset ι) (f : ι → OE c (Lam d L N))
    (hf : ∀ i ∈ s, IsNilpotent (f i)) : oexp (-∑ i ∈ s, f i) = ∏ i ∈ s, oexp (-f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [oexp_zero]
  | insert x s hx ih =>
    rw [sum_insert hx, prod_insert hx, neg_add, oexp_add (hf x (mem_insert_self x s)).neg
      (isNilpotent_sum fun i hi => hf i (mem_insert_of_mem hi)).neg,
      ih fun i hi => hf i (mem_insert_of_mem hi)]

/-- `V_j(X) = ∑_{B ∈ 𝓑_j(X)} V_j(B)` for polymers. -/
theorem VfullX_eq_sum (V : Vcoup) (W : Coup c) {X : Finset (Lam d L N)} (hX : IsPolymer j X) :
    VfullX V W a b X = ∑ p ∈ blocks j X, VfullX V W a b (blockSet j p) := by
  have hd : ((blocks j X : Finset (Fin d → ℕ)) : Set (Fin d → ℕ)).PairwiseDisjoint
      (blockSet (L := L) (N := N) j) := fun _ _ _ _ hne => blockSet_disjoint hne
  have hs : splitO c (Coup.toV c W) a b X =
      ∑ p ∈ blocks j X, splitO c (Coup.toV c W) a b (blockSet j p) := by
    conv_lhs => rw [← biUnion_blocks hX]
    exact splitO_biUnion c _ a b _ _ hd
  rw [VfullX, VE_eq_sum_blocks V hX, map_sum, hs, ← sum_add_distrib]; rfl

/-- `e^{-V_j(X)} = ∏_{B ∈ 𝓑_j(X)} e^{-V_j(B)}`. -/
theorem oexp_neg_VfullX (V : Vcoup) (W : Coup c) {X : Finset (Lam d L N)} (hX : IsPolymer j X) :
    oexp (-VfullX V W a b X) = bpow j (fun p => oexp (-VfullX V W a b (blockSet j p))) X := by
  rw [VfullX_eq_sum j a b V W hX, oexp_neg_sum _ _ fun p _ => isNilpotent_VfullX a b V W _]; rfl

/-- `e^{-u_{j+1}(Λ)} = ∏_B e^{-u_{j+1}(B)}`. -/
theorem bpow_eum_univ : bpow j (obsI j C Vb Vo K a b).eum (univ : Finset (Lam d L N)) =
    algebraMap ℂ (OE c (Lam d L N))
        (Complex.exp (-((uVb j C Vb K).1 * (univ : Finset (Lam d L N)).card))) *
      oexp (-uObsX j C Vo K a b univ) := by
  have hd := blockSet_pairwiseDisjoint (d := d) (L := L) (N := N) j
  have hu : uObsX j C Vo K a b univ =
      ∑ p ∈ blockIdx (L := L) (N := N) j, uObsX j C Vo K a b (blockSet j p) := by
    rw [uObsX, ← blocks_univ_biUnion j, splitO_biUnion c _ a b _ _ hd]; rfl
  have h1 := prod_exp_card (d := d) (L := L) (N := N) j (-(uVb j C Vb K).1) (isPolymer_univ j)
  simp only [neg_mul] at h1
  have h2 : ∏ p ∈ blockIdx (d := d) (L := L) (N := N) j, algebraMap ℂ (OE c (Lam d L N))
      (Complex.exp (-((uVb j C Vb K).1 * (blockSet (d := d) (L := L) (N := N) j p).card))) =
      algebraMap ℂ (OE c (Lam d L N))
        (Complex.exp (-((uVb j C Vb K).1 * (univ : Finset (Lam d L N)).card))) := by
    have := congrArg (emb (c := c)) h1
    rw [map_prod] at this
    simp only [AlgHom.commutes] at this
    exact this
  rw [bpow, hu, oexp_neg_sum _ _ fun p _ => isNilpotent_of_obs (bulk_uObsX j C Vo K a b _)]
  simp only [obsI]
  rw [prod_mul_distrib, ← h2]; rfl

/-- **Proposition `prop:ZVK`** (`e:ZVK` with the extended `u` and `V`):
`𝔼_C θ ∑_{X ∈ 𝒫_j} e^{-V_j(Λ ∖ X)} K_j(X) =
e^{-u_{j+1}(Λ)} ∑_{U ∈ 𝒫_{j+1}} e^{-V_{j+1}(Λ ∖ U)} K_{j+1}(U)`, where `V_j = V^∅_j + V^obs_j`,
`u_{j+1} = u^∅_{j+1} + u^obs_{j+1}`, `V_{j+1} = V^∅_{j+1} + V^obs_{j+1}` (split evaluation). -/
theorem ZVK_obs' :
    ECO C (thetaO (∑ X ∈ Pj j univ, oexp (-VfullX Vb Vo a b (univ \ X)) * KextG j K X)) =
      (algebraMap ℂ (OE c (Lam d L N))
          (Complex.exp (-((uVb j C Vb K).1 * (univ : Finset (Lam d L N)).card))) *
        oexp (-uObsX j C Vo K a b univ)) *
      ∑ U ∈ Pj (j + 1) univ,
        oexp (-VfullX (uVb j C Vb K).2 (nextObs C j Vo K a b) a b (univ \ U)) *
          KnextO j C Vb Vo K a b U := by
  have e1 : (∑ X ∈ Pj j univ, oexp (-VfullX Vb Vo a b (univ \ X)) * KextG j K X) =
      ZjG j (obsI j C Vb Vo K a b) := by
    rw [ZjG]
    refine sum_congr rfl fun X hX => ?_
    rw [oexp_neg_VfullX j a b Vb Vo (IsPolymer.sdiff (isPolymer_univ j) (mem_Pj.1 hX).2)]; rfl
  rw [e1, ZVK_obs, ZnextG, bpow_eum_univ]
  congr 1
  refine sum_congr rfl fun U hU => ?_
  rw [oexp_neg_VfullX j a b _ _
    (IsPolymer.sdiff (isPolymer_univ j) (IsPolymer.of_succ (mem_Pj.1 hU).2))]; rfl

end ZVK

/-! ### Definition `def:V+obs` with the bulk part -/

section DefV

variable {c : Case} {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℝ} (Vb : Vcoup) {Vo : Coup c}
  {K : Finset (Lam d L N) → OE c (Lam d L N)} {a b : Lam d L N}

end DefV

end

end Obs
