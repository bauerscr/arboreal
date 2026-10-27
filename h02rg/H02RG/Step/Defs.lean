import Loc.Image

/-!
# Definitions for Sections `sec:polymers`, `sec:step-def` and `sec:step`

Throughout, `Λ = Λ_N` is the torus of side `L^N` and `j` is a scale.

## Even elements
Polymer activities, `e^{-V}` and all other quantities whose products are taken over blocks or
components are even elements of the Grassmann algebra.  Even elements commute, so we let them
take values in the even subalgebra `EvR Λ`, which is a commutative ring; products over finite
sets are then ordinary `Finset.prod`s.  `thetaE`, `inclE`, `ECE` and `gexp` are the restrictions
of `θ`, of the inclusion `𝒩(Λ) ⊆ 𝒩(Λ ⊔ Λ)`, of `𝔼_C` and of the exponential.

## Polymers
`Pj j W` is the set `𝒫_j(W)` of `j`-polymers contained in `W`, `Comp j X` the set of connected
components of `X`, `clo j X = X̄` the closure (the smallest `(j+1)`-polymer containing `X`), and
`nb j X = |𝓑_j(X)|`.

## Polymer activities (Definition `def:cKbulk`)
A polymer activity is a function `K` on finite subsets of `Λ`; only its values on connected
polymers are used, and `Kext K X = ∏_{Y ∈ Comp(X)} K(Y)` is its extension by the component
factorisation property (`e:K-prod`).  `InK j K` is the condition `K ∈ 𝒦^∅_j`:
`K(X) ∈ 𝒩_sym(X^□)` is `U(1)` invariant, invariant under the symplectic symmetry `J`, and
automorphism invariant, for all connected `X`.  (The `J`-invariance is an addition to
Definition `def:cKbulk`; it is needed for Proposition `prop:Loc` (v).)

## The renormalisation group map (Section `sec:step-def`)
`Qb`, `Jb` are `Q(B)`, `J(B, X)` (`e:Q-def`–`e:J-def`); `uVnext` is `(u_{j+1}, V_{j+1})`
(`e:V+-def`); `dI`, `Ktil`, `Kchk`, `Gset`, `Knext` are `δI(B)`, `K̃(W)`, `Ǩ(X)`, `𝒢(U)` and
`K_{j+1}(U)` (`e:K+-def`–`e:deltaI`).
-/

namespace Step

noncomputable section

open Finset Grassmann Loc FRD

/-! ## The even subalgebra -/

section Even

variable {Λ Λ' : Type*}

/-- The even subalgebra of `𝒩(Λ)`. -/
def Ev (Λ : Type*) : Subalgebra ℂ (N Λ) := AlgHom.equalizer inv' (AlgHom.id ℂ (N Λ))

/-- The even subalgebra as a type. -/
abbrev EvR (Λ : Type*) := ↥(Ev Λ)

theorem mem_Ev {x : N Λ} : x ∈ Ev Λ ↔ inv' x = x := by simp [Ev, AlgHom.mem_equalizer]

instance : CommRing (EvR Λ) :=
  { (inferInstance : Ring (EvR Λ)) with
    mul_comm := fun a b => Subtype.ext (mul_comm_of_even a.2 (b : N Λ)) }

instance : Module ℚ (EvR Λ) := Module.compHom (EvR Λ) (algebraMap ℚ ℂ)

theorem inv'_map (f : V Λ →ₗ[ℂ] V Λ') (x : N Λ) :
    inv' (ExteriorAlgebra.map f x) = ExteriorAlgebra.map f (inv' x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι m => simp [ExteriorAlgebra.map_apply_ι]
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb, map_mul, map_mul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

/-- The restriction of `ExteriorAlgebra.map f` to even elements. -/
def mapE (f : V Λ →ₗ[ℂ] V Λ') : EvR Λ →ₐ[ℂ] EvR Λ' :=
  ((ExteriorAlgebra.map f).comp (Ev Λ).val).codRestrict (Ev Λ') fun x => by
    refine mem_Ev.2 ?_
    simp only [AlgHom.comp_apply, Subalgebra.coe_val]
    rw [inv'_map, mem_Ev.1 x.2]

@[simp] theorem coe_mapE (f : V Λ →ₗ[ℂ] V Λ') (x : EvR Λ) :
    (mapE f x : N Λ') = ExteriorAlgebra.map f (x : N Λ) := rfl

variable [DecidableEq Λ]

/-- `θ` on even elements. -/
def thetaE : EvR Λ →ₐ[ℂ] EvR (Λ ⊕ Λ) := mapE thetaV

/-- The inclusion `𝒩(Λ) ⊆ 𝒩(Λ ⊔ Λ)` (functions of `ψ` only) on even elements. -/
def inclE : EvR Λ →ₐ[ℂ] EvR (Λ ⊕ Λ) := mapE inlV

@[simp] theorem coe_thetaE (x : EvR Λ) : (thetaE x : N (Λ ⊕ Λ)) = theta (x : N Λ) := rfl

@[simp] theorem coe_inclE (x : EvR Λ) : (inclE x : N (Λ ⊕ Λ)) = incl (x : N Λ) := rfl

theorem D_inv' (a : Sf Λ) (x : N Λ) : D a (inv' x) = -inv' (D a x) := by
  rw [D, contractLeft_inv']

theorem Lζ_inv' [Fintype Λ] (C : Matrix Λ Λ ℝ) (F : N (Λ ⊕ Λ)) :
    Lζ C (inv' F) = inv' (Lζ C F) := by
  simp only [Lζ_apply, map_sum, map_smul, D_inv', map_neg, neg_neg]

theorem EC_inv' [Fintype Λ] (C : Matrix Λ Λ ℝ) (F : N (Λ ⊕ Λ)) :
    EC C (inv' F) = inv' (EC C F) := by
  have hc : Lζ C ∘ₗ (inv' : N (Λ ⊕ Λ) →ₐ[ℂ] N (Λ ⊕ Λ)).toLinearMap =
      (inv' : N (Λ ⊕ Λ) →ₐ[ℂ] N (Λ ⊕ Λ)).toLinearMap ∘ₗ Lζ C :=
    LinearMap.ext fun F => Lζ_inv' C F
  have h := Module.End.commute_exp_left_of_commute (Lζ_isNilpotent C) (Lζ_isNilpotent C) hc
  have h2 := LinearMap.congr_fun h F
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply] at h2
  rw [EC, LinearMap.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, h2,
    AlgHom.toLinearMap_apply, proj, inv'_map]

/-- `𝔼_C` on even elements. -/
def ECE [Fintype Λ] (C : Matrix Λ Λ ℝ) : EvR (Λ ⊕ Λ) →ₗ[ℂ] EvR Λ where
  toFun F := ⟨EC C (F : N (Λ ⊕ Λ)), mem_Ev.2 (by rw [← EC_inv', mem_Ev.1 F.2])⟩
  map_add' F G := Subtype.ext (map_add _ _ _)
  map_smul' r F := Subtype.ext (map_smul _ _ _)

@[simp] theorem coe_ECE [Fintype Λ] (C : Matrix Λ Λ ℝ) (F : EvR (Λ ⊕ Λ)) :
    (ECE C F : N Λ) = EC C (F : N (Λ ⊕ Λ)) := rfl

/-- The exponential of an (even, nilpotent) element. -/
def gexp (x : EvR Λ) : EvR Λ := IsNilpotent.exp x

/-- An odd element: `inv' x = -x`. -/
def IsOdd (x : N Λ) : Prop := inv' x = -x

theorem mem_Ev_of_odd_mul {x y : N Λ} (hx : IsOdd x) (hy : IsOdd y) : x * y ∈ Ev Λ := by
  refine mem_Ev.2 ?_
  rw [map_mul, hx, hy, neg_mul_neg]

theorem isOdd_ψ (a : Sf Λ) : IsOdd (ψ a) := inv'_ι _

theorem IsOdd.sub {x y : N Λ} (hx : IsOdd x) (hy : IsOdd y) : IsOdd (x - y) := by
  unfold IsOdd at *; rw [map_sub, hx, hy, neg_sub_neg, neg_sub]

theorem IsOdd.smul {x : N Λ} (hx : IsOdd x) (r : ℂ) : IsOdd (r • x) := by
  unfold IsOdd at *; rw [map_smul, hx, smul_neg]

theorem IsOdd.sum {ι : Type*} (s : Finset ι) {f : ι → N Λ} (hf : ∀ i ∈ s, IsOdd (f i)) :
    IsOdd (∑ i ∈ s, f i) := by
  unfold IsOdd at *; rw [map_sum, ← sum_neg_distrib]; exact sum_congr rfl hf

theorem IsOdd.neg {x : N Λ} (hx : IsOdd x) : IsOdd (-x) := by
  unfold IsOdd at *; rw [map_neg, hx]

end Even

variable {d L N : ℕ} [NeZero L]

/-! ## Even local polynomials -/

theorem isOdd_psi (x : Lam d L N) : IsOdd (psi x) := isOdd_ψ _

theorem isOdd_psibar (x : Lam d L N) : IsOdd (psibar x) := isOdd_ψ _

theorem isOdd_grad (e : Dir d) (x : Lam d L N) : IsOdd (grad e x) :=
  (isOdd_psi _).sub (isOdd_psi _)

theorem isOdd_gradbar (e : Dir d) (x : Lam d L N) : IsOdd (gradbar e x) :=
  (isOdd_psibar _).sub (isOdd_psibar _)

theorem isOdd_lapPsi (x : Lam d L N) : IsOdd (lapPsi x) :=
  (IsOdd.sum _ fun e _ => (isOdd_grad e _).sub (isOdd_grad e _)).smul _

theorem isOdd_lapPsibar (x : Lam d L N) : IsOdd (lapPsibar x) :=
  (IsOdd.sum _ fun e _ => (isOdd_gradbar e _).sub (isOdd_gradbar e _)).smul _

theorem gradSq_mem (x : Lam d L N) : gradSq x ∈ Ev (Lam d L N) :=
  Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun e _ =>
    mem_Ev_of_odd_mul (isOdd_grad e x) (isOdd_gradbar e x)) _

theorem eval_mem (V : Vcoup) (X : Finset (Lam d L N)) : V.eval X ∈ Ev (Lam d L N) := by
  refine Subalgebra.sum_mem _ fun x _ => ?_
  refine add_mem (add_mem (add_mem (Subalgebra.smul_mem _ (gradSq_mem x) _) ?_) ?_) ?_
  · exact Subalgebra.smul_mem _ (add_mem (mem_Ev_of_odd_mul (isOdd_lapPsi x).neg (isOdd_psibar x))
      (mem_Ev_of_odd_mul (isOdd_psi x) (isOdd_lapPsibar x).neg)) _
  · exact Subalgebra.smul_mem _ (mem_Ev_of_odd_mul (isOdd_psi x) (isOdd_psibar x)) _
  · exact Subalgebra.smul_mem _ (Subalgebra.mul_mem _
      (mem_Ev_of_odd_mul (isOdd_psi x) (isOdd_psibar x)) (gradSq_mem x)) _

/-- `V(X)` as an even element. -/
def VE (V : Vcoup) (X : Finset (Lam d L N)) : EvR (Lam d L N) := ⟨V.eval X, eval_mem V X⟩

@[simp] theorem coe_VE (V : Vcoup) (X : Finset (Lam d L N)) : (VE V X : Alg d L N) = V.eval X :=
  rfl

theorem monoAt_mem_Ev (M : Mono d) (x : Lam d L N) : monoAt M x ∈ Ev (Lam d L N) := by
  rw [monoAt]
  refine Subalgebra.list_sum_mem _ fun F hF => ?_
  obtain ⟨p, _, rfl⟩ := List.mem_map.1 hF
  exact Subalgebra.smul_mem _ (mem_Ev_of_odd_mul (isOdd_psi _) (isOdd_psibar _)) _

theorem LocXY_mem_Ev (X Y : Finset (Lam d L N)) (F : Alg d L N) :
    LocXY X Y F ∈ Ev (Lam d L N) :=
  add_mem (Subalgebra.smul_mem _ (one_mem _) _) (Subalgebra.sum_mem _ fun M _ =>
    Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun x _ => monoAt_mem_Ev M x) _)

/-- `Loc_{X,Y}` on even elements. -/
def LocE (X Y : Finset (Lam d L N)) (F : EvR (Lam d L N)) : EvR (Lam d L N) :=
  ⟨LocXY X Y F, LocXY_mem_Ev X Y F⟩

@[simp] theorem coe_LocE (X Y : Finset (Lam d L N)) (F : EvR (Lam d L N)) :
    (LocE X Y F : Alg d L N) = LocXY X Y F := rfl

/-! ## Polymers -/

/-- `𝒫_j(W)`: the `j`-polymers contained in `W`. -/
def Pj (j : ℕ) (W : Finset (Lam d L N)) : Finset (Finset (Lam d L N)) :=
  open Classical in W.powerset.filter (IsPolymer j)

/-- The number of `j`-blocks `|𝓑_j(X)|`. -/
def nb (j : ℕ) (X : Finset (Lam d L N)) : ℕ := (blocks j X).card

/-- `X ∈ 𝒞_j`: a connected polymer. -/
def IsConn (j : ℕ) (X : Finset (Lam d L N)) : Prop := IsPolymer j X ∧ IsConnected j X

/-- The component of the block `b` in the polymer `X`. -/
def compOf (j : ℕ) (X : Finset (Lam d L N)) (b : Fin d → ℕ) : Finset (Lam d L N) :=
  open Classical in X.filter fun x => Relation.ReflTransGen (BlockAdj j X) b (blk j x)

/-- The connected components `Comp(X)` of the polymer `X`. -/
def Comp (j : ℕ) (X : Finset (Lam d L N)) : Finset (Finset (Lam d L N)) :=
  (blocks j X).image (compOf j X)

/-- The closure `X̄`: the smallest `(j+1)`-polymer containing `X`. -/
def clo (j : ℕ) (X : Finset (Lam d L N)) : Finset (Lam d L N) :=
  open Classical in univ.filter fun x => blk (j + 1) x ∈ blocks (j + 1) X

/-- The small sets `𝒮_j`. -/
def smallSets (j : ℕ) : Finset (Finset (Lam d L N)) :=
  open Classical in univ.filter (IsSmall j)

/-- The connected polymers `𝒞_j`. -/
def connSets (j : ℕ) : Finset (Finset (Lam d L N)) :=
  open Classical in univ.filter (IsConn j)

/-- The block indices of `Λ` at scale `j`. -/
def blockIdx (j : ℕ) : Finset (Fin d → ℕ) := blocks (L := L) (N := N) j univ

/-! ## Automorphisms -/

/-- The automorphisms of the torus generated by translations, reflections and permutations of
the coordinates. -/
inductive IsGen : AffAut d L N → Prop
  | transl (t : Lam d L N) : IsGen (AffAut.transl t)
  | refl (i : Fin d) : IsGen (AffAut.refl i)
  | perm (σ : Equiv.Perm (Fin d)) : IsGen (AffAut.perm σ)
  | comp {T₁ T₂ : AffAut d L N} : IsGen T₁ → IsGen T₂ → IsGen (T₁.comp T₂)

/-- `T` maps `j`-blocks to `j`-blocks. -/
def PresBlocks (j : ℕ) (T : AffAut d L N) : Prop :=
  ∀ x y : Lam d L N, blk j x = blk j y → blk j (T.E x) = blk j (T.E y)

/-! ## Polymer activities -/

/-- A polymer activity. -/
abbrev Act (d L N : ℕ) [NeZero L] := Finset (Lam d L N) → EvR (Lam d L N)

/-- The extension `K(X) = ∏_{Y ∈ Comp(X)} K(Y)` (`e:K-prod`). -/
def Kext (j : ℕ) (K : Act d L N) (X : Finset (Lam d L N)) : EvR (Lam d L N) :=
  ∏ Y ∈ Comp j X, K Y

/-- `K ∈ 𝒦^∅_j(Λ_N)` (Definition `def:cKbulk`, with `J`-invariance added). -/
structure InK (j : ℕ) (K : Act d L N) : Prop where
  loc : ∀ X, IsConn j X → (K X : Alg d L N) ∈ NX (nbhd j X : Set (Lam d L N))
  sym : ∀ X, IsConn j X → IsSym (K X : Alg d L N)
  jinv : ∀ X, IsConn j X → Jsym (K X : Alg d L N) = K X
  aut : ∀ T : AffAut d L N, IsGen T → PresBlocks j T → ∀ X, IsConn j X →
    autAlg T.E (K X : Alg d L N) = K (T.img X)

/-- The partition function `Z_j = ∑_{X ∈ 𝒫_j} e^{-V_j(Λ ∖ X)} K_j(X)` (`e:ZVK` with `u_j = 0`). -/
def Zj (j : ℕ) (V : Vcoup) (K : Act d L N) : EvR (Lam d L N) :=
  ∑ X ∈ Pj j univ, gexp (-(VE V (univ \ X) : EvR (Lam d L N))) * Kext j K X

/-! ## The renormalisation group map -/

section Map

variable (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (V : Vcoup) (K : Act d L N)

/-- `Q(B) = ∑_{X ∈ 𝒮_j, X ⊇ B} Loc_{X,B} K(X)` (`e:Q-def`), and `Q = 0` if `j + 1 = N`. -/
def Qb (b : Fin d → ℕ) : EvR (Lam d L N) :=
  open Classical in
  if j + 1 < N then
    ∑ X ∈ (smallSets j).filter (fun X => blockSet j b ⊆ X), LocE X (blockSet j b) (K X)
  else 0

/-- `J(B, X)` (`e:J-defB`, `e:J-def`), and `J = 0` if `j + 1 = N`. -/
def Jb (b : Fin d → ℕ) (X : Finset (Lam d L N)) : EvR (Lam d L N) :=
  open Classical in
  if j + 1 < N ∧ IsSmall j X ∧ blockSet j b ⊆ X then
    if X = blockSet j b then
      -∑ Y ∈ (smallSets j).filter (fun Y => blockSet j b ⊆ Y ∧ Y ≠ blockSet j b),
        LocE Y (blockSet j b) (K Y)
    else LocE X (blockSet j b) (K X)
  else 0

/-- The coupling constants `(u, V)` of an element `F = u|B| + V(B)` of `(ℂ ⊕ 𝒱^∅)(B)`. -/
def coupOf (F : Alg d L N) (B : Finset (Lam d L N)) : ℂ × Vcoup :=
  open Classical in
  if h : ∃ (u : ℂ) (V' : Vcoup), F = (u * B.card) • (1 : Alg d L N) + V'.eval B then
    (h.choose, h.choose_spec.choose)
  else (0, ⟨0, 0, 0, 0⟩)

/-- `(u_{j+1}, V_{j+1})`, defined by `u_{j+1}|B| + V_{j+1}(B) = 𝔼_{C_{j+1}} θ (V_j(B) - Q(B))`
(`e:V+-def`), read off at the block `B = B_0` with index `0`. -/
def uVnext : ℂ × Vcoup :=
  coupOf (EC C (theta (V.eval (blockSet j 0) - (Qb j K 0 : Alg d L N)))) (blockSet j 0)

/-- `e^{-(u+V)_{j+1}(B)}` for the `j`-block `B` with index `b`. -/
def Inext (b : Fin d → ℕ) : EvR (Lam d L N) :=
  Complex.exp (-((uVnext j C V K).1 * (blockSet (L := L) (N := N) j b).card)) •
    gexp (-(VE (uVnext j C V K).2 (blockSet j b) : EvR (Lam d L N)))

/-- `e^{-(u+V)_{j+1}(X)} = ∏_{B ∈ 𝓑_j(X)} e^{-(u+V)_{j+1}(B)}`. -/
def InextPow (X : Finset (Lam d L N)) : EvR (Lam d L N) := ∏ b ∈ blocks j X, Inext j C V K b

/-- `δI(B) = θ e^{-V_j(B)} - e^{-(u+V)_{j+1}(B)}` (`e:deltaI`). -/
def dI (b : Fin d → ℕ) : EvR (Lam d L N ⊕ Lam d L N) :=
  thetaE (gexp (-(VE V (blockSet j b) : EvR (Lam d L N)))) - inclE (Inext j C V K b)

/-- `(δI)^X = ∏_{B ∈ 𝓑_j(X)} δI(B)`. -/
def dIPow (X : Finset (Lam d L N)) : EvR (Lam d L N ⊕ Lam d L N) :=
  ∏ b ∈ blocks j X, dI j C V K b

/-- `K̃(W) = ∑_{Y ∈ 𝒫_j(W)} θ K(W ∖ Y) (δI)^Y`. -/
def Ktil (W : Finset (Lam d L N)) : EvR (Lam d L N ⊕ Lam d L N) :=
  ∑ Y ∈ Pj j W, thetaE (Kext j K (W \ Y)) * dIPow j C V K Y

/-- `Ǩ(W) = K̃(W) - ∑_{B ∈ 𝓑_j(W)} θ J(B, W)` for connected `W`. -/
def KchkC (W : Finset (Lam d L N)) : EvR (Lam d L N ⊕ Lam d L N) :=
  Ktil j C V K W - ∑ b ∈ blocks j W, thetaE (Jb j K b W)

/-- `Ǩ(X) = ∏_{W ∈ Comp(X)} Ǩ(W)` (`e:K+-def2`). -/
def Kchk (X : Finset (Lam d L N)) : EvR (Lam d L N ⊕ Lam d L N) :=
  ∏ W ∈ Comp j X, KchkC j C V K W

end Map

/-! ## The index set `𝒢(U)` -/

/-- The pairs `(B, X)` with `X ∈ 𝒮_j` and `B ∈ 𝓑_j(X)` (a block is given by its index). -/
def pairsU (j : ℕ) : Finset ((Fin d → ℕ) × Finset (Lam d L N)) :=
  open Classical in
  (blockIdx (L := L) (N := N) j ×ˢ smallSets j).filter fun p => blockSet j p.1 ⊆ p.2

/-- `X_𝒳 = ⋃_{(B,X) ∈ 𝒳} X`. -/
def Xcal (𝒳 : Finset ((Fin d → ℕ) × Finset (Lam d L N))) : Finset (Lam d L N) :=
  𝒳.biUnion Prod.snd

/-- `⋃_{(B,X) ∈ 𝒳} B^□`. -/
def Bbox (j : ℕ) (𝒳 : Finset ((Fin d → ℕ) × Finset (Lam d L N))) : Finset (Lam d L N) :=
  𝒳.biUnion fun p => nbhd j (blockSet j p.1)

/-- The conditions defining `𝒢(U)` (Definition `def:K+`). -/
def GCond (j : ℕ) (U : Finset (Lam d L N))
    (g : Finset ((Fin d → ℕ) × Finset (Lam d L N)) × Finset (Lam d L N)) : Prop :=
  IsPolymer j g.2 ∧ g.1 ⊆ pairsU j ∧
  (∀ p ∈ g.1, ∀ q ∈ g.1, p.2 = q.2 → p = q) ∧
  (∀ p ∈ g.1, ∀ q ∈ g.1, p.2 ≠ q.2 → ¬ Touch p.2 q.2) ∧
  ¬ Touch (Xcal g.1) g.2 ∧
  clo j (g.2 ∪ Bbox j g.1) = U

/-- `𝒢(U)`: pairs `(𝒳, X̌)`. -/
def Gset (j : ℕ) (U : Finset (Lam d L N)) :
    Finset (Finset ((Fin d → ℕ) × Finset (Lam d L N)) × Finset (Lam d L N)) :=
  open Classical in ((pairsU j).powerset ×ˢ Pj j univ).filter (GCond j U)

/-- `K_{j+1}(U)` (`e:K+-def`). -/
def Knext (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (V : Vcoup) (K : Act d L N)
    (U : Finset (Lam d L N)) : EvR (Lam d L N) :=
  Complex.exp ((uVnext j C V K).1 * U.card) •
    ∑ g ∈ Gset j U, InextPow j C V K (U \ (g.2 ∪ Xcal g.1)) *
      ECE C (Kchk j C V K g.2 * ∏ p ∈ g.1, thetaE (Jb j K p.1 p.2))

/-- The partition function at the next scale,
`e^{-u_{j+1}|Λ|} ∑_{U ∈ 𝒫_{j+1}} e^{-V_{j+1}(Λ ∖ U)} K_{j+1}(U)`. -/
def Znext (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (V : Vcoup) (K : Act d L N) :
    EvR (Lam d L N) :=
  Complex.exp (-((uVnext j C V K).1 * (univ : Finset (Lam d L N)).card)) •
    ∑ U ∈ Pj (j + 1) univ, gexp (-(VE (uVnext j C V K).2 (univ \ U) : EvR (Lam d L N))) *
      Knext j C V K U

/-! ## Norms (Section `sec:step`) -/

/-- `‖V‖_j = sup_{B ∈ 𝓑_j} ‖V(B)‖_{T_j(ℓ)}` (`e:V-norm`). -/
def Vnorm (j : ℕ) (ℓ : ℝ) (V : Vcoup) : ENNReal :=
  ⨆ b ∈ blockIdx (L := L) (N := N) j,
    Tj d (L : ℝ) j ℓ (V.eval (blockSet (L := L) (N := N) j (b : Fin d → ℕ)))

/-- `‖K‖_j = sup_{X ∈ 𝒞_j} A^{(|𝓑_j(X)| - 2^d)_+} ‖K(X)‖_{T_j(ℓ)}` (`e:K-norm`). -/
def Knorm (j : ℕ) (ℓ A : ℝ) (K : Act d L N) : ENNReal :=
  ⨆ X ∈ connSets (L := L) (N := N) j,
    ENNReal.ofReal (A ^ (nb j X - 2 ^ d)) * Tj d (L : ℝ) j ℓ (K X : Alg d L N)

/-- The hypotheses on the covariance `C = C_{j+1}` used in Section `sec:step`. -/
structure GoodCov (j : ℕ) (ℓ₀ : ℝ) (C : Matrix (Lam d L N) (Lam d L N) ℝ) : Prop where
  psd : C.PosSemidef
  inv : ∀ T : AffAut d L N, IsGen T → ∀ x y, C (T.E x) (T.E y) = C x y
  range : j + 1 < N → ∀ x y, (L : ℝ) ^ (j + 1) / 2 ≤ supNorm (x - y) → C x y = 0
  norm : covNormj (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1)) C ≤ 1

end

end Step
