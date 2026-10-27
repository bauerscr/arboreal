import Obs.Map
import Obs.ConsistGen
import Flow.Consistency

/-!
# The embedding of tori on the algebra with observables (`prop:consistency`)

For `N ≤ M`, `Flow.embA N M : 𝒩(Λ_N) → 𝒩(Λ_M)` (`ψ_x ↦ ψ_{emb x}`) acts componentwise on the
algebra with observables: `embO N M` (on `OE c Λ_N`) and `embO2 N M` (on the doubled algebra).
It commutes with `θ`, `ι`, `e^{·}`, with `𝔼_C` for covariances agreeing on the support
(`embO_ECO`), maps the split evaluations at `a, b` to those at `emb a, emb b` (`embO_splitO`,
`embO_VfullX`), preserves the pairings `mass1`, `mass2`, `ε` (hence commutes with `loc^a`,
`loc^b`, `loc^{ab}`, `embA_locA`, …, and with the extended `Loc`, `embO_LocO`), and maps the
coupling constants of `Q^obs` to those on `Λ_M` (`Qcoup_emb`).
-/

namespace Obs

noncomputable section

open Finset Grassmann SA Loc Step LocObs Gen

variable {d L : ℕ} [NeZero L] {N M : ℕ} {c : Case}

/-! ### The embedding -/

theorem embA_inv' (x : Alg d L N) : Flow.embA N M (inv' x) = inv' (Flow.embA N M x) :=
  (Grassmann.inv'_map (Flow.embV N M) x).symm

theorem embA2_inv' (x : Alg2 d L N) : Flow.embA2 N M (inv' x) = inv' (Flow.embA2 N M x) :=
  (Grassmann.inv'_map (Flow.pushV (Sum.map (Flow.emb N M) (Flow.emb N M))) x).symm

variable (c) in
/-- `emb` on the algebra with observables (componentwise). -/
def embS (N M : ℕ) : SA c (Lam d L N) →ₐ[ℂ] SA c (Lam d L M) := mapS (Flow.embA N M) embA_inv'

/-- `emb` on even elements with observables. -/
def embO (N M : ℕ) : OE c (Lam d L N) →ₐ[ℂ] OE c (Lam d L M) := mapO (Flow.embA N M) embA_inv'

/-- `emb` on even elements of the doubled algebra with observables. -/
def embO2 (N M : ℕ) : OE c (Lam d L N ⊕ Lam d L N) →ₐ[ℂ] OE c (Lam d L M ⊕ Lam d L M) :=
  mapO (Flow.embA2 N M) embA2_inv'

@[simp] theorem coe_embO (F : OE c (Lam d L N)) :
    (embO N M F : SA c (Lam d L M)) = embS c N M (F : SA c (Lam d L N)) := rfl

@[simp] theorem embS_e (F : SA c (Lam d L N)) : (embS c N M F).e = Flow.embA N M F.e := rfl
@[simp] theorem embS_a (F : SA c (Lam d L N)) : (embS c N M F).a = Flow.embA N M F.a := rfl
@[simp] theorem embS_b (F : SA c (Lam d L N)) : (embS c N M F).b = Flow.embA N M F.b := rfl
@[simp] theorem embS_ab (F : SA c (Lam d L N)) : (embS c N M F).ab = Flow.embA N M F.ab := rfl


theorem embO_emb (x : EvR (Lam d L N)) :
    embO N M (emb x : OE c (Lam d L N)) = emb (Flow.embE N M x) := by
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;> simp

theorem embO_oexp {F : OE c (Lam d L N)} (hF : IsNilpotent F) :
    embO N M (oexp F) = oexp (embO N M F) :=
  IsNilpotent.map_exp hF (embO N M)

theorem coeff_one' {Λ : Type*} [DecidableEq Λ] (F : Grassmann.N Λ) (a : Sf Λ) : coeff F ![a] = ε (D a F) := by
  simp only [coeff, Dseq, contr_succ, contr_zero]
  rfl

variable (hNM : N ≤ M)
include hNM

theorem embO2_thetaO (F : OE c (Lam d L N)) : embO2 N M (thetaO F) = thetaO (embO N M F) := by
  have h := fun x : Alg d L N => (Flow.theta_pushA (Flow.emb_injective' hNM) x).symm
  exact Subtype.ext (SA.ext (h _) (h _) (h _) (h _))

theorem embO2_inclO (F : OE c (Lam d L N)) : embO2 N M (inclO F) = inclO (embO N M F) := by
  have h := fun x : Alg d L N => (Flow.incl_pushA (Flow.emb_injective' hNM) x).symm
  exact Subtype.ext (SA.ext (h _) (h _) (h _) (h _))

/-- **`𝔼_C` commutes with `emb`** for elements supported where the covariances agree. -/
theorem embO_ECO {C : Matrix (Lam d L N) (Lam d L N) ℝ} {C' : Matrix (Lam d L M) (Lam d L M) ℝ}
    {R : Set (Lam d L N)} (hC : ∀ x ∈ R, ∀ y ∈ R, C' (Flow.emb N M x) (Flow.emb N M y) = C x y)
    {F : OE c (Lam d L N ⊕ Lam d L N)} (he : (F : SA c _).e ∈ NX2 R) (ha : (F : SA c _).a ∈ NX2 R)
    (hb : (F : SA c _).b ∈ NX2 R) (hab : (F : SA c _).ab ∈ NX2 R) :
    embO N M (ECO C F) = ECO C' (embO2 N M F) :=
  Subtype.ext (SA.ext (Flow.EC_emb hNM hC he).symm (Flow.EC_emb hNM hC ha).symm
    (Flow.EC_emb hNM hC hb).symm (Flow.EC_emb hNM hC hab).symm)

/-! ### Split evaluations -/

theorem ind_emb (x : Lam d L N) (X : Finset (Lam d L N)) :
    ind (Flow.emb N M x ∈ X.image (Flow.emb N M)) = ind (x ∈ X) := by
  by_cases h : x ∈ X
  · rw [ind_pos ((Flow.emb_mem_image hNM).2 h), ind_pos h]
  · rw [ind_neg (mt (Flow.emb_mem_image hNM).1 h), ind_neg h]

theorem embS_halfA (V : Coup c) (a b : Lam d L N) :
    embS c N M (halfA c V a b) = halfA c V (Flow.emb N M a) (Flow.emb N M b) := by
  cases c <;> ext <;>
    simp [halfA, nx, Flow.embA_psi' hNM, Flow.embA_psibar' hNM, map_smul]

theorem embS_halfB (V : Coup c) (a b : Lam d L N) :
    embS c N M (halfB c V a b) = halfB c V (Flow.emb N M a) (Flow.emb N M b) := by
  cases c <;> ext <;>
    simp [halfB, nx, Flow.embA_psi' hNM, Flow.embA_psibar' hNM, map_smul]

theorem embO_splitO (V : Coup c) (a b : Lam d L N) (X : Finset (Lam d L N)) :
    embO N M (splitO c V a b X) =
      splitO c V (Flow.emb N M a) (Flow.emb N M b) (X.image (Flow.emb N M)) := by
  refine Subtype.ext ?_
  rw [coe_embO, coe_splitO, coe_splitO, splitS, splitS, map_add, map_smul, map_smul,
    embS_halfA hNM, embS_halfB hNM, ind_emb hNM, ind_emb hNM]

theorem embO_VfullX (Vb : Vcoup) (Vo : Coup c) (a b : Lam d L N) {X : Finset (Lam d L N)}
    (hX : ∀ x ∈ X, 2 * supNorm x + 2 < L ^ N) :
    embO N M (VfullX Vb Vo a b X) =
      VfullX Vb Vo (Flow.emb N M a) (Flow.emb N M b) (X.image (Flow.emb N M)) := by
  rw [VfullX, VfullX, map_add, embO_emb, Flow.embE_VE hNM _ hX, embO_splitO hNM]

/-! ### Pairings and the observable `loc` -/

theorem mass1_embA (s : ℤˣ) (F : Alg d L N) : mass1 s (Flow.embA N M F) = mass1 s F := by
  have hinj := Flow.emb_injective' (d := d) (L := L) hNM
  unfold mass1
  refine (Fintype.sum_of_injective (Flow.emb N M) hinj _ _ (fun y hy => ?_) (fun x => ?_)).symm
  · rw [coeff_one', Flow.embA_eq, Flow.D_pushA_of_not (b := (y, s)) (fun x hx => hy ⟨x, hx⟩),
      map_zero]
  · rw [coeff_one', coeff_one', Flow.embA_eq,
      show ((Flow.emb N M x, s) : Sf (Lam d L M)) = (Flow.emb N M (x, s).1, (x, s).2) from rfl,
      Flow.D_pushA hinj, Flow.ε_pushA]

theorem mass2_embA (F : Alg d L N) : mass2 (Flow.embA N M F) = mass2 F := by
  have hinj := Flow.emb_injective' (d := d) (L := L) hNM
  unfold mass2
  refine (Fintype.sum_of_injective (Flow.emb N M) hinj _ _ (fun y hy => ?_) (fun x => ?_)).symm
  · refine sum_eq_zero fun y' _ => ?_
    rw [coeff_two, Flow.embA_eq, Flow.D_pushA_of_not (b := (y, -1)) (fun x hx => hy ⟨x, hx⟩),
      map_zero, map_zero]
  · refine Fintype.sum_of_injective (Flow.emb N M) hinj
      (fun y => coeff F ![(x, -1), (y, 1)])
      (fun y' => coeff (Flow.embA N M F) ![(Flow.emb N M x, -1), (y', 1)])
      (fun y hy => ?_) (fun y => ?_)
    · rw [coeff_two, Flow.embA_eq,
        show ((Flow.emb N M x, -1) : Sf (Lam d L M)) = (Flow.emb N M (x, -1).1, (x, -1).2) from rfl,
        Flow.D_pushA hinj (x, -1), Flow.D_pushA_of_not (b := (y, 1)) (fun x hx => hy ⟨x, hx⟩), map_zero]
    · rw [coeff_two, coeff_two, Flow.embA_eq,
        show ((Flow.emb N M x, -1) : Sf (Lam d L M)) = (Flow.emb N M (x, -1).1, (x, -1).2) from rfl,
        show ((Flow.emb N M y, 1) : Sf (Lam d L M)) = (Flow.emb N M (y, 1).1, (y, 1).2) from rfl,
        Flow.D_pushA hinj (x, -1), Flow.D_pushA hinj (y, 1), Flow.ε_pushA]

theorem embA_locGen (P X Y : Finset (Lam d L N)) (f : Lam d L N → Alg d L N)
    (f' : Lam d L M → Alg d L M) (hf : ∀ z, Flow.embA N M (f z) = f' (Flow.emb N M z)) (r : ℂ) :
    Flow.embA N M (locGen P X Y f r) =
      locGen (P.image (Flow.emb N M)) (X.image (Flow.emb N M)) (Y.image (Flow.emb N M)) f' r := by
  have hinj := Flow.emb_injective' (d := d) (L := L) hNM
  unfold locGen
  rw [map_smul, map_sum, ← image_inter _ _ hinj, ← image_inter _ _ hinj,
    card_image_of_injective _ hinj, sum_image fun x _ y _ h => hinj h]
  simp only [hf]

theorem embA_locOdd (s : ℤˣ) (P X Y : Finset (Lam d L N)) (F : Alg d L N) :
    Flow.embA N M (locOdd s P X Y F) =
      locOdd s (P.image (Flow.emb N M)) (X.image (Flow.emb N M)) (Y.image (Flow.emb N M))
        (Flow.embA N M F) := by
  rw [locOdd, locOdd, mass1_embA hNM]
  exact embA_locGen hNM P X Y _ _ (fun z => Flow.embA_ψ hNM (z, s)) _

theorem embA_locEven (P X Y : Finset (Lam d L N)) (F : Alg d L N) :
    Flow.embA N M (locEven P X Y F) =
      locEven (P.image (Flow.emb N M)) (X.image (Flow.emb N M)) (Y.image (Flow.emb N M))
        (Flow.embA N M F) := by
  rw [locEven, locEven, map_add, mass2_embA hNM, Flow.ε_embA hNM]
  congr 1
  · exact embA_locGen hNM P X Y _ _ (fun z => map_one _) _
  · exact embA_locGen hNM P X Y _ _ (fun z => by
      rw [pbp, pbp, map_mul, Flow.embA_psi' hNM, Flow.embA_psibar' hNM]) _

theorem embA_locA (o : ObsCase) (a : Lam d L N) (X Y : Finset (Lam d L N)) (F : Alg d L N) :
    Flow.embA N M (locA o a X Y F) =
      locA o (Flow.emb N M a) (X.image (Flow.emb N M)) (Y.image (Flow.emb N M))
        (Flow.embA N M F) := by
  cases o
  · simp only [locA]; rw [embA_locOdd hNM, image_singleton]
  · simp only [locA]; rw [embA_locEven hNM, image_singleton]

theorem embA_locB (o : ObsCase) (b : Lam d L N) (X Y : Finset (Lam d L N)) (F : Alg d L N) :
    Flow.embA N M (locB o b X Y F) =
      locB o (Flow.emb N M b) (X.image (Flow.emb N M)) (Y.image (Flow.emb N M))
        (Flow.embA N M F) := by
  cases o
  · simp only [locB]; rw [embA_locOdd hNM, image_singleton]
  · simp only [locB]; rw [embA_locEven hNM, image_singleton]

theorem embA_locAB (a b : Lam d L N) (X Y : Finset (Lam d L N)) (F : Alg d L N) :
    Flow.embA N M (locAB a b X Y F) =
      locAB (Flow.emb N M a) (Flow.emb N M b) (X.image (Flow.emb N M)) (Y.image (Flow.emb N M))
        (Flow.embA N M F) := by
  rw [locAB, locAB, embA_locEven hNM, image_insert, image_singleton]

/-- **The extended `Loc` commutes with `emb`**, given that the bulk `Loc` does. -/
theorem embO_LocO (a b : Lam d L N) (X Y : Finset (Lam d L N)) (F : OE c (Lam d L N))
    (he : Flow.embA N M (LocXY X Y (F : SA c _).e) =
      LocXY (X.image (Flow.emb N M)) (Y.image (Flow.emb N M)) (Flow.embA N M (F : SA c _).e)) :
    embO N M (LocO a b X Y F) = LocO (Flow.emb N M a) (Flow.emb N M b) (X.image (Flow.emb N M))
      (Y.image (Flow.emb N M)) (embO N M F) :=
  Subtype.ext (SA.ext he (embA_locA hNM _ _ _ _ _) (embA_locB hNM _ _ _ _ _)
    (embA_locAB hNM _ _ _ _ _))

/-! ### The coupling constants of `Q^obs` -/

theorem cardAB_emb (a b : Lam d L N) (X : Finset (Lam d L N)) :
    cardAB (Flow.emb N M a) (Flow.emb N M b) (X.image (Flow.emb N M)) = cardAB a b X := by
  have hinj := Flow.emb_injective' (d := d) (L := L) hNM
  unfold cardAB
  rw [show ({Flow.emb N M a, Flow.emb N M b} : Finset (Lam d L M)) =
      ({a, b} : Finset (Lam d L N)).image (Flow.emb N M) by rw [image_insert, image_singleton],
    ← image_inter _ _ hinj, card_image_of_injective _ hinj]

theorem sum_smallAt_emb {j : ℕ} {x : Lam d L N} {K : Finset (Lam d L N) → OE c (Lam d L N)}
    {K' : Finset (Lam d L M) → OE c (Lam d L M)}
    (hs : smallAt j (Flow.emb N M x) = (smallAt j x).image fun X => X.image (Flow.emb N M))
    (hK : ∀ X ∈ smallAt j x, K' (X.image (Flow.emb N M)) = embO N M (K X))
    (g : Finset (Lam d L M) → SA c (Lam d L M) → ℂ) (g₀ : Finset (Lam d L N) → SA c (Lam d L N) → ℂ)
    (hg : ∀ X F, g (X.image (Flow.emb N M)) (embS c N M F) = g₀ X F) :
    ∑ X ∈ smallAt j (Flow.emb N M x), g X (K' X : SA c _) = ∑ X ∈ smallAt j x, g₀ X (K X : SA c _) := by
  rw [hs, sum_image fun X _ Y _ h => Flow.image_emb_injective hNM h]
  exact sum_congr rfl fun X hX => by rw [hK X hX, coe_embO, hg]

/-- **The coupling constants of `Q^obs` agree** for activities agreeing on the small sets
containing `a` or `b`. -/
theorem Qcoup_emb {j : ℕ} (hjN : j + 1 < N) (hjM : j + 1 < M) {a b : Lam d L N}
    {K : Finset (Lam d L N) → OE c (Lam d L N)} {K' : Finset (Lam d L M) → OE c (Lam d L M)}
    (hsa : smallAt j (Flow.emb N M a) = (smallAt j a).image fun X => X.image (Flow.emb N M))
    (hsb : smallAt j (Flow.emb N M b) = (smallAt j b).image fun X => X.image (Flow.emb N M))
    (hKa : ∀ X ∈ smallAt j a, K' (X.image (Flow.emb N M)) = embO N M (K X))
    (hKb : ∀ X ∈ smallAt j b, K' (X.image (Flow.emb N M)) = embO N M (K X)) :
    Qcoup c j K' (Flow.emb N M a) (Flow.emb N M b) = Qcoup c j K a b := by
  have S := fun {x : Lam d L N} hs hK => sum_smallAt_emb (c := c) (j := j) (x := x) (K := K) (K' := K') hNM hs hK
  have q2a := S hsa hKa (fun X F => mass2 F.ab / cardAB (Flow.emb N M a) (Flow.emb N M b) X)
    (fun X F => mass2 F.ab / cardAB a b X)
    (fun X F => by simp only [embS_ab, mass2_embA hNM, cardAB_emb hNM])
  have q2b := S hsb hKb (fun X F => mass2 F.ab / cardAB (Flow.emb N M a) (Flow.emb N M b) X)
    (fun X F => mass2 F.ab / cardAB a b X)
    (fun X F => by simp only [embS_ab, mass2_embA hNM, cardAB_emb hNM])
  have q0a := S hsa hKa (fun X F => ε F.ab / cardAB (Flow.emb N M a) (Flow.emb N M b) X)
    (fun X F => ε F.ab / cardAB a b X)
    (fun X F => by simp only [embS_ab, Flow.ε_embA hNM, cardAB_emb hNM])
  have q0b := S hsb hKb (fun X F => ε F.ab / cardAB (Flow.emb N M a) (Flow.emb N M b) X)
    (fun X F => ε F.ab / cardAB a b X)
    (fun X F => by simp only [embS_ab, Flow.ε_embA hNM, cardAB_emb hNM])
  cases c
  · have la := S hsa hKa (fun _ F => mass1 (-1) F.a) (fun _ F => mass1 (-1) F.a)
      (fun X F => by simp only [embS_a, mass1_embA hNM])
    have lb := S hsb hKb (fun _ F => mass1 1 F.b) (fun _ F => mass1 1 F.b)
      (fun X F => by simp only [embS_b, mass1_embA hNM])
    simp only [Qcoup, if_pos hjN, if_pos hjM]
    rw [la, lb, q0a, q0b, q2a, q2b]
  · have la := S hsa hKa (fun _ F => mass2 F.a) (fun _ F => mass2 F.a)
      (fun X F => by simp only [embS_a, mass2_embA hNM])
    have lb := S hsb hKb (fun _ F => mass2 F.b) (fun _ F => mass2 F.b)
      (fun X F => by simp only [embS_b, mass2_embA hNM])
    have ga := S hsa hKa (fun _ F => ε F.a) (fun _ F => ε F.a)
      (fun X F => by simp only [embS_a, Flow.ε_embA hNM])
    have gb := S hsb hKb (fun _ F => ε F.b) (fun _ F => ε F.b)
      (fun X F => by simp only [embS_b, Flow.ε_embA hNM])
    simp only [Qcoup, if_pos hjN, if_pos hjM]
    rw [la, lb, ga, gb, q0a, q0b, q2a, q2b]

end

end Obs
