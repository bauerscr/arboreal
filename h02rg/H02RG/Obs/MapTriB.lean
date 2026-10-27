import Obs.FlowObsBd

/-!
# Upper-triangular structure of the observable map: independence of the partner point

`Obs.MapTri` shows that the `a` component `(π_∅ + π_a) K_{j+1}` depends only on `π_∅ V_j`,
`λ_a` and `(π_∅ + π_a) K_j`, for fixed observable points `(a, b)`.  Here:

* **the `a` part does not depend on the partner point `b`** (`killO_KnextO_pt`): the
  `(π_∅ + π_a)` part at `(a, b)` and at `(a, b')` agree when the inputs agree;
* **the `b` part**: `killBO : F ↦ F_∅ + σ_b F_b` is an algebra homomorphism commuting
  with `θ`, `ι`, `𝔼_C`, and `(π_∅ + π_b) K_{j+1}` at `(a, b)` depends only on `π_∅ V_j`, `λ_b`
  and `(π_∅ + π_b) K_j`, and not on the partner point `a` (`killBO_KnextO`);
* along the observable flow (`flowO_a_indep`, `flowO_b_indep`): `λ_{a,j}` (resp. `λ_{b,j}`),
  the `u`-parts `γ_{a,j+1}` (resp. `γ_{b,j+1}`) of `nextObs`, and `(π_∅ + π_a) K_j`
  (resp. `(π_∅ + π_b) K_j`) do not depend on the partner point, nor on the other initial
  coupling constants.

The `ab` couplings (`q`, `η`, `r_a`, `r_b`) do depend on both points (through `|X ∩ {a,b}|` and
`C(a,b)`).
-/

namespace Obs

noncomputable section

open Finset Grassmann SA Loc Step LocObs Gen

section KillB

variable {c : Case} {Λ : Type*} [DecidableEq Λ]

/-- `F ↦ F_∅ + σ_b F_b`. -/
def killBS : SA c Λ →ₐ[ℂ] SA c Λ where
  toFun F := ⟨F.e, 0, F.b, 0⟩
  map_one' := by ext <;> simp
  map_mul' F G := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' F G := by ext <;> simp
  commutes' r := by ext <;> simp

@[simp] theorem killBS_e (F : SA c Λ) : (killBS F).e = F.e := rfl
@[simp] theorem killBS_a (F : SA c Λ) : (killBS F).a = 0 := rfl
@[simp] theorem killBS_b (F : SA c Λ) : (killBS F).b = F.b := rfl
@[simp] theorem killBS_ab (F : SA c Λ) : (killBS F).ab = 0 := rfl

/-- `F ↦ F_∅ + σ_b F_b` on even elements. -/
def killBO : OE c Λ →ₐ[ℂ] OE c Λ :=
  ((killBS : SA c Λ →ₐ[ℂ] SA c Λ).comp (OEv c Λ).val).codRestrict (OEv c Λ) fun F => by
    obtain ⟨h1, -, h3, -⟩ := mem_OEv.1 F.2
    exact mem_OEv.2 ⟨h1, by simp, h3, by simp⟩

@[simp] theorem coe_killBO (F : OE c Λ) : (killBO F : SA c Λ) = killBS (F : SA c Λ) := rfl

theorem killBO_ext {F G : OE c Λ} (he : (F : SA c Λ).e = (G : SA c Λ).e)
    (hb : (F : SA c Λ).b = (G : SA c Λ).b) : killBO F = killBO G :=
  Subtype.ext (SA.ext he rfl hb rfl)

theorem killBO_thetaO (F : OE c Λ) : killBO (thetaO F) = thetaO (killBO F) :=
  Subtype.ext (SA.ext rfl (by simp) rfl (by simp))

theorem killBO_inclO (F : OE c Λ) : killBO (inclO F) = inclO (killBO F) :=
  Subtype.ext (SA.ext rfl (by simp) rfl (by simp))

theorem killBO_ECO [Fintype Λ] (C : Matrix Λ Λ ℝ) (F : OE c (Λ ⊕ Λ)) :
    killBO (ECO C F) = ECO C (killBO F) :=
  Subtype.ext (SA.ext rfl (by simp) rfl (by simp))

theorem bulk_killBO (F : OE c Λ) : bulk (killBO F) = bulk F := rfl

theorem b_eq_of_killBO {F G : OE c Λ} (h : killBO F = killBO G) :
    (F : SA c Λ).b = (G : SA c Λ).b := by
  have := congrArg (fun F : OE c Λ => (F : SA c Λ).b) h
  simpa using this

theorem e_eq_of_killBO {F G : OE c Λ} (h : killBO F = killBO G) :
    (F : SA c Λ).e = (G : SA c Λ).e := by
  have := congrArg (fun F : OE c Λ => (F : SA c Λ).e) h
  simpa using this

theorem e_eq_of_killO {F G : OE c Λ} (h : killO F = killO G) :
    (F : SA c Λ).e = (G : SA c Λ).e := by
  have := congrArg (fun F : OE c Λ => (F : SA c Λ).e) h
  simpa using this

theorem a_eq_of_killO' {F G : OE c Λ} (h : killO F = killO G) :
    (F : SA c Λ).a = (G : SA c Λ).a := by
  have := congrArg (fun F : OE c Λ => (F : SA c Λ).a) h
  simpa using this

end KillB

variable {d L N : ℕ} [NeZero L]

/-! ### The `a` part does not depend on the partner point -/

section TriA

variable {c : Case}

theorem killO_splitO_pt {W W' : Coup c} {a b b' : Lam d L N}
    (h : (halfA c W a b).a = (halfA c W' a b').a) (X : Finset (Lam d L N)) :
    killO (splitO c W a b X) = killO (splitO c W' a b' X) := by
  rw [killO_splitO, killO_splitO,
    killO_ext (F := halfAO c W a b) (G := halfAO c W' a b') (by simp only [coe_halfAO, halfA_e]) h]

theorem killO_LocO_pt (a b b' : Lam d L N) (X Y : Finset (Lam d L N)) {F G : OE c (Lam d L N)}
    (h : killO F = killO G) : killO (LocO a b X Y F) = killO (LocO a b' X Y G) := by
  have he := e_eq_of_killO h
  have ha := a_eq_of_killO' h
  exact killO_ext (by simp [he]) (by simp [ha])

variable {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℝ} {Vb : Vcoup} {Vo Vo' : Coup c}
  {K K' : Finset (Lam d L N) → OE c (Lam d L N)} {a b b' : Lam d L N}

theorem killO_JO_pt (hK : ∀ X, killO (K X) = killO (K' X)) (p : Fin d → ℕ)
    (X : Finset (Lam d L N)) : killO (JO a b j K p X) = killO (JO a b' j K' p X) := by
  unfold JO
  split_ifs
  · simp only [map_neg, map_sum]
    exact congrArg _ (sum_congr rfl fun Y _ => killO_LocO_pt a b b' _ _ (hK Y))
  · exact killO_LocO_pt a b b' _ _ (hK X)
  · rfl

theorem halfA_toV_a_pt (hla : laOf c Vo = laOf c Vo') :
    (halfA c (Coup.toV c Vo) a b).a = (halfA c (Coup.toV c Vo') a b').a := by
  cases c
  · simp only [halfA, Coup.toV]; rw [show Coup1.la Vo = Coup1.la Vo' from hla]
  · simp only [halfA, Coup.toV]; rw [show Coup2.la Vo = Coup2.la Vo' from hla]

theorem nextObs_toV_a_pt (hla : laOf c Vo = laOf c Vo') (hK : ∀ X, killO (K X) = killO (K' X)) :
    (halfA c (Coup.toV c (nextObs C j Vo K a b)) a b).a =
      (halfA c (Coup.toV c (nextObs C j Vo' K' a b')) a b').a := by
  have h := a_eq_of_killO hK
  cases c
  · have hl : Coup1.la Vo = Coup1.la Vo' := hla
    by_cases hj : j + 1 < N <;>
      simp [halfA, nextObs, Wcoup, Coup.toV, Coup.next, Coup.sub, Coup1.next, Qcoup, hl, h, hj]
  · have hl : Coup2.la Vo = Coup2.la Vo' := hla
    by_cases hj : j + 1 < N <;>
      simp [halfA, nextObs, Wcoup, Coup.toV, Coup.next, Coup.sub, Coup2.next, Qcoup, hl, h, hj]

theorem nextObs_toU_a_pt (hla : laOf c Vo = laOf c Vo') (hK : ∀ X, killO (K X) = killO (K' X)) :
    (halfA c (Coup.toU c (nextObs C j Vo K a b)) a b).a =
      (halfA c (Coup.toU c (nextObs C j Vo' K' a b')) a b').a := by
  have h := a_eq_of_killO hK
  cases c
  · simp [halfA, Coup.toU]
  · have hl : Coup2.la Vo = Coup2.la Vo' := hla
    by_cases hj : j + 1 < N <;>
      simp [halfA, nextObs, Wcoup, Coup.toU, Coup.toV, Coup.next, Coup.sub, Coup2.next, Qcoup, hl,
        h, hj]

/-- The `(π_∅ + π_a)` part of the ingredients at `(a, b)` and `(a, b')` agree. -/
theorem map_killO_obsI_pt (hla : laOf c Vo = laOf c Vo') (hK : ∀ X, killO (K X) = killO (K' X)) :
    (obsI j C Vb Vo K a b).map killO = (obsI j C Vb Vo' K' a b').map killO := by
  have hb := bulkK_eq_of_killO hK
  have hu : uVb j C Vb K = uVb j C Vb K' := by rw [uVb, uVb, hb]
  have hV : ∀ (V : Vcoup) {W W' : Coup c}, (halfA c (Coup.toV c W) a b).a =
      (halfA c (Coup.toV c W') a b').a → ∀ X, killO (oexp (-VfullX V W a b X)) =
        killO (oexp (-VfullX V W' a b' X)) := by
    intro V W W' h X
    rw [killO_oexp (isNilpotent_VfullX a b V W X).neg,
      killO_oexp (isNilpotent_VfullX a b' V W' X).neg, map_neg, map_neg,
      VfullX, VfullX, map_add, map_add, killO_splitO_pt h]
  have hU : ∀ X, killO (uObsX j C Vo K a b X) = killO (uObsX j C Vo' K' a b' X) := fun X =>
    killO_splitO_pt (nextObs_toU_a_pt hla hK) X
  have hexp : ∀ F : OE c (Lam d L N), bulk F = 0 → killO (oexp F) = oexp (killO F) := fun F hF =>
    killO_oexp (isNilpotent_of_obs hF)
  refine RGIngr.map_congr _ (fun p => hV Vb (halfA_toV_a_pt hla) _) (fun p => ?_) (fun p => ?_)
    (fun p => ?_) (fun p X => killO_JO_pt hK p X) hK
  · show killO (oexp (-VfullX (uVb j C Vb K).2 (nextObs C j Vo K a b) a b (blockSet j p))) =
      killO (oexp (-VfullX (uVb j C Vb K').2 (nextObs C j Vo' K' a b') a b' (blockSet j p)))
    rw [hu]; exact hV _ (nextObs_toV_a_pt hla hK) _
  · show killO (algebraMap ℂ _ _ * oexp (uObsX j C Vo K a b (blockSet j p))) =
      killO (algebraMap ℂ _ _ * oexp (uObsX j C Vo' K' a b' (blockSet j p)))
    rw [map_mul, map_mul, hu, hexp _ (bulk_uObsX _ _ _ _ _ _ _),
      hexp _ (bulk_uObsX _ _ _ _ _ _ _), hU]
  · show killO (algebraMap ℂ _ _ * oexp (-uObsX j C Vo K a b (blockSet j p))) =
      killO (algebraMap ℂ _ _ * oexp (-uObsX j C Vo' K' a b' (blockSet j p)))
    rw [map_mul, map_mul, hu, hexp _ (by rw [map_neg, bulk_uObsX, neg_zero]),
      hexp _ (by rw [map_neg, bulk_uObsX, neg_zero]), map_neg, map_neg, hU]

/-- **The `a` part does not depend on the partner point**: `(π_∅ + π_a) K_{j+1}(U)` at
`(a, b)` and at `(a, b')` agree when `λ_a` and `(π_∅ + π_a) K_j` agree. -/
theorem killO_KnextO_pt (hla : laOf c Vo = laOf c Vo') (hK : ∀ X, killO (K X) = killO (K' X))
    (U : Finset (Lam d L N)) :
    killO (KnextO j C Vb Vo K a b U) = killO (KnextO j C Vb Vo' K' a b' U) := by
  rw [KnextO, KnextO,
    map_KnextG (A := obsA c C) (A' := obsA c C) killO killO killO_thetaO killO_inclO
      (fun y => killO_ECO C y),
    map_KnextG (A := obsA c C) (A' := obsA c C) killO killO killO_thetaO killO_inclO
      (fun y => killO_ECO C y), map_killO_obsI_pt hla hK]

/-- `λ_a` and `γ_a` of `nextObs` at `(a, b)` and `(a, b')` agree. -/
theorem nextObs_la_pt (hla : laOf c Vo = laOf c Vo') (hK : ∀ X, killO (K X) = killO (K' X)) :
    laOf c (nextObs C j Vo K a b) = laOf c (nextObs C j Vo' K' a b') := by
  have h := a_eq_of_killO hK
  cases c
  · have hl : Coup1.la Vo = Coup1.la Vo' := hla
    by_cases hj : j + 1 < N <;>
      simp [laOf, nextObs, Wcoup, Coup.toV, Coup.next, Coup.sub, Coup1.next, Qcoup, hl, h, hj]
  · have hl : Coup2.la Vo = Coup2.la Vo' := hla
    by_cases hj : j + 1 < N <;>
      simp [laOf, nextObs, Wcoup, Coup.toV, Coup.next, Coup.sub, Coup2.next, Qcoup, hl, h, hj]

theorem nextObs_ga_pt (hla : laOf c Vo = laOf c Vo') (hK : ∀ X, killO (K X) = killO (K' X)) :
    gaOf c (nextObs C j Vo K a b) = gaOf c (nextObs C j Vo' K' a b') := by
  have h := a_eq_of_killO hK
  cases c
  · rfl
  · have hl : Coup2.la Vo = Coup2.la Vo' := hla
    by_cases hj : j + 1 < N <;>
      simp [gaOf, nextObs, Wcoup, Coup.toV, Coup.next, Coup.sub, Coup2.next, Qcoup, hl, h, hj]

end TriA

/-! ### The `b` part -/

section TriB

variable {c : Case}

theorem halfB_e (c : Case) (W : Coup c) (a b : Lam d L N) : (halfB c W a b).e = 0 := by
  cases c <;> rfl

theorem killBO_halfAO (W : Coup c) (a b : Lam d L N) : killBO (halfAO c W a b) = 0 := by
  cases c <;> exact Subtype.ext (by ext <;> simp [halfA])

theorem killBO_splitO (W : Coup c) (a b : Lam d L N) (X : Finset (Lam d L N)) :
    killBO (splitO c W a b X) = ind (b ∈ X) • killBO (halfBO c W a b) := by
  rw [splitO, map_add, map_smul, map_smul, killBO_halfAO, smul_zero, zero_add]

theorem killBO_oexp {F : OE c (Lam d L N)} (hn : IsNilpotent F) :
    killBO (oexp F) = oexp (killBO F) :=
  IsNilpotent.map_exp hn killBO

theorem killBO_splitO_pt {W W' : Coup c} {a a' b : Lam d L N}
    (h : (halfB c W a b).b = (halfB c W' a' b).b) (X : Finset (Lam d L N)) :
    killBO (splitO c W a b X) = killBO (splitO c W' a' b X) := by
  rw [killBO_splitO, killBO_splitO,
    killBO_ext (F := halfBO c W a b) (G := halfBO c W' a' b) (by simp only [coe_halfBO, halfB_e]) h]

theorem killBO_LocO_pt (a a' b : Lam d L N) (X Y : Finset (Lam d L N)) {F G : OE c (Lam d L N)}
    (h : killBO F = killBO G) : killBO (LocO a b X Y F) = killBO (LocO a' b X Y G) := by
  have he := e_eq_of_killBO h
  have hb := b_eq_of_killBO h
  exact killBO_ext (by simp [he]) (by simp [hb])

variable {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℝ} {Vb : Vcoup} {Vo Vo' : Coup c}
  {K K' : Finset (Lam d L N) → OE c (Lam d L N)} {a a' b : Lam d L N}

theorem killBO_JO_pt (hK : ∀ X, killBO (K X) = killBO (K' X)) (p : Fin d → ℕ)
    (X : Finset (Lam d L N)) : killBO (JO a b j K p X) = killBO (JO a' b j K' p X) := by
  unfold JO
  split_ifs
  · simp only [map_neg, map_sum]
    exact congrArg _ (sum_congr rfl fun Y _ => killBO_LocO_pt a a' b _ _ (hK Y))
  · exact killBO_LocO_pt a a' b _ _ (hK X)
  · rfl

theorem b_eq_of_killBO' (hK : ∀ X, killBO (K X) = killBO (K' X)) (X : Finset (Lam d L N)) :
    (K X : SA c (Lam d L N)).b = (K' X : SA c (Lam d L N)).b :=
  b_eq_of_killBO (hK X)

theorem bulkK_eq_of_killBO (hK : ∀ X, killBO (K X) = killBO (K' X)) : bulkK K = bulkK K' :=
  funext fun X => by rw [bulkK, bulkK, ← bulk_killBO, hK X, bulk_killBO]

theorem halfB_toV_b_pt (hlb : lbOf c Vo = lbOf c Vo') :
    (halfB c (Coup.toV c Vo) a b).b = (halfB c (Coup.toV c Vo') a' b).b := by
  cases c
  · simp only [halfB, Coup.toV]; rw [show Coup1.lb Vo = Coup1.lb Vo' from hlb]
  · simp only [halfB, Coup.toV]; rw [show Coup2.lb Vo = Coup2.lb Vo' from hlb]

theorem nextObs_toV_b_pt (hlb : lbOf c Vo = lbOf c Vo') (hK : ∀ X, killBO (K X) = killBO (K' X)) :
    (halfB c (Coup.toV c (nextObs C j Vo K a b)) a b).b =
      (halfB c (Coup.toV c (nextObs C j Vo' K' a' b)) a' b).b := by
  have h := b_eq_of_killBO' hK
  cases c
  · have hl : Coup1.lb Vo = Coup1.lb Vo' := hlb
    by_cases hj : j + 1 < N <;>
      simp [halfB, nextObs, Wcoup, Coup.toV, Coup.next, Coup.sub, Coup1.next, Qcoup, hl, h, hj]
  · have hl : Coup2.lb Vo = Coup2.lb Vo' := hlb
    by_cases hj : j + 1 < N <;>
      simp [halfB, nextObs, Wcoup, Coup.toV, Coup.next, Coup.sub, Coup2.next, Qcoup, hl, h, hj]

theorem nextObs_toU_b_pt (hlb : lbOf c Vo = lbOf c Vo') (hK : ∀ X, killBO (K X) = killBO (K' X)) :
    (halfB c (Coup.toU c (nextObs C j Vo K a b)) a b).b =
      (halfB c (Coup.toU c (nextObs C j Vo' K' a' b)) a' b).b := by
  have h := b_eq_of_killBO' hK
  cases c
  · simp [halfB, Coup.toU]
  · have hl : Coup2.lb Vo = Coup2.lb Vo' := hlb
    by_cases hj : j + 1 < N <;>
      simp [halfB, nextObs, Wcoup, Coup.toU, Coup.toV, Coup.next, Coup.sub, Coup2.next, Qcoup, hl,
        h, hj]

/-- The `(π_∅ + π_b)` part of the ingredients at `(a, b)` and `(a', b)` agree. -/
theorem map_killBO_obsI (hlb : lbOf c Vo = lbOf c Vo') (hK : ∀ X, killBO (K X) = killBO (K' X)) :
    (obsI j C Vb Vo K a b).map killBO = (obsI j C Vb Vo' K' a' b).map killBO := by
  have hb := bulkK_eq_of_killBO hK
  have hu : uVb j C Vb K = uVb j C Vb K' := by rw [uVb, uVb, hb]
  have hV : ∀ (V : Vcoup) {W W' : Coup c}, (halfB c (Coup.toV c W) a b).b =
      (halfB c (Coup.toV c W') a' b).b → ∀ X, killBO (oexp (-VfullX V W a b X)) =
        killBO (oexp (-VfullX V W' a' b X)) := by
    intro V W W' h X
    rw [killBO_oexp (isNilpotent_VfullX a b V W X).neg,
      killBO_oexp (isNilpotent_VfullX a' b V W' X).neg, map_neg, map_neg,
      VfullX, VfullX, map_add, map_add, killBO_splitO_pt h]
  have hU : ∀ X, killBO (uObsX j C Vo K a b X) = killBO (uObsX j C Vo' K' a' b X) := fun X =>
    killBO_splitO_pt (nextObs_toU_b_pt hlb hK) X
  have hexp : ∀ F : OE c (Lam d L N), bulk F = 0 → killBO (oexp F) = oexp (killBO F) :=
    fun F hF => killBO_oexp (isNilpotent_of_obs hF)
  refine RGIngr.map_congr _ (fun p => hV Vb (halfB_toV_b_pt hlb) _) (fun p => ?_) (fun p => ?_)
    (fun p => ?_) (fun p X => killBO_JO_pt hK p X) hK
  · show killBO (oexp (-VfullX (uVb j C Vb K).2 (nextObs C j Vo K a b) a b (blockSet j p))) =
      killBO (oexp (-VfullX (uVb j C Vb K').2 (nextObs C j Vo' K' a' b) a' b (blockSet j p)))
    rw [hu]; exact hV _ (nextObs_toV_b_pt hlb hK) _
  · show killBO (algebraMap ℂ _ _ * oexp (uObsX j C Vo K a b (blockSet j p))) =
      killBO (algebraMap ℂ _ _ * oexp (uObsX j C Vo' K' a' b (blockSet j p)))
    rw [map_mul, map_mul, hu, hexp _ (bulk_uObsX _ _ _ _ _ _ _),
      hexp _ (bulk_uObsX _ _ _ _ _ _ _), hU]
  · show killBO (algebraMap ℂ _ _ * oexp (-uObsX j C Vo K a b (blockSet j p))) =
      killBO (algebraMap ℂ _ _ * oexp (-uObsX j C Vo' K' a' b (blockSet j p)))
    rw [map_mul, map_mul, hu, hexp _ (by rw [map_neg, bulk_uObsX, neg_zero]),
      hexp _ (by rw [map_neg, bulk_uObsX, neg_zero]), map_neg, map_neg, hU]

/-- **Upper-triangular structure, `b` component**: `(π_∅ + π_b) K_{j+1}(U)` at `(a, b)`
depends only on `π_∅ V_j`, `λ_b` and `(π_∅ + π_b) K_j`; in particular not on the partner
point `a`, on `(V^a_j, K^a_j)` or on `(V^{ab}_j, K^{ab}_j)`. -/
theorem killBO_KnextO (hlb : lbOf c Vo = lbOf c Vo') (hK : ∀ X, killBO (K X) = killBO (K' X))
    (U : Finset (Lam d L N)) :
    killBO (KnextO j C Vb Vo K a b U) = killBO (KnextO j C Vb Vo' K' a' b U) := by
  rw [KnextO, KnextO,
    map_KnextG (A := obsA c C) (A' := obsA c C) killBO killBO killBO_thetaO killBO_inclO
      (fun y => killBO_ECO C y),
    map_KnextG (A := obsA c C) (A' := obsA c C) killBO killBO killBO_thetaO killBO_inclO
      (fun y => killBO_ECO C y), map_killBO_obsI hlb hK]

/-- `λ_b` of `nextObs` at `(a, b)` and `(a', b)` agree. -/
theorem nextObs_lb_pt (hlb : lbOf c Vo = lbOf c Vo') (hK : ∀ X, killBO (K X) = killBO (K' X)) :
    lbOf c (nextObs C j Vo K a b) = lbOf c (nextObs C j Vo' K' a' b) := by
  have h := b_eq_of_killBO' hK
  cases c
  · have hl : Coup1.lb Vo = Coup1.lb Vo' := hlb
    by_cases hj : j + 1 < N <;>
      simp [lbOf, nextObs, Wcoup, Coup.toV, Coup.next, Coup.sub, Coup1.next, Qcoup, hl, h, hj]
  · have hl : Coup2.lb Vo = Coup2.lb Vo' := hlb
    by_cases hj : j + 1 < N <;>
      simp [lbOf, nextObs, Wcoup, Coup.toV, Coup.next, Coup.sub, Coup2.next, Qcoup, hl, h, hj]

/-- `γ_b` of `nextObs` at `(a, b)` and `(a', b)` agree. -/
theorem nextObs_gb_pt (hlb : lbOf c Vo = lbOf c Vo') (hK : ∀ X, killBO (K X) = killBO (K' X)) :
    gbOf c (nextObs C j Vo K a b) = gbOf c (nextObs C j Vo' K' a' b) := by
  have h := b_eq_of_killBO' hK
  cases c
  · rfl
  · have hl : Coup2.lb Vo = Coup2.lb Vo' := hlb
    by_cases hj : j + 1 < N <;>
      simp [gbOf, nextObs, Wcoup, Coup.toV, Coup.next, Coup.sub, Coup2.next, Qcoup, hl, h, hj]

end TriB

/-! ### Along the observable flow -/

section Flow

variable {c : Case} {N : ℕ} (msq : ℝ) (V₀ : Vcoup)

theorem killO_restrO {j : ℕ} {K K' : Finset (Lam d L N) → OE c (Lam d L N)}
    (h : ∀ X, killO (K X) = killO (K' X)) (X : Finset (Lam d L N)) :
    killO (restrO j K X) = killO (restrO j K' X) := by
  unfold restrO; split_ifs
  · exact h X
  · rfl

theorem killBO_restrO {j : ℕ} {K K' : Finset (Lam d L N) → OE c (Lam d L N)}
    (h : ∀ X, killBO (K X) = killBO (K' X)) (X : Finset (Lam d L N)) :
    killBO (restrO j K X) = killBO (restrO j K' X) := by
  unfold restrO; split_ifs
  · exact h X
  · rfl

/-- **The `a` part of the observable flow does not depend on the partner point**: for any
`b, b'` and initial coupling constants with the same `λ_a`, `λ_{a,j}` and `(π_∅ + π_a) K_j`
agree for all `j`. -/
theorem flowO_a_indep {Vo₀ Vo₀' : Coup c} (hla : laOf c Vo₀ = laOf c Vo₀') (a b b' : Lam d L N) :
    ∀ j, laOf c (flowO d L c N msq V₀ Vo₀ a b j).1 = laOf c (flowO d L c N msq V₀ Vo₀' a b' j).1 ∧
      ∀ X, killO ((flowO d L c N msq V₀ Vo₀ a b j).2 X) =
        killO ((flowO d L c N msq V₀ Vo₀' a b' j).2 X)
  | 0 => ⟨hla, fun _ => rfl⟩
  | j + 1 => by
    obtain ⟨h1, h2⟩ := flowO_a_indep hla a b b' j
    rw [flowO_succ, flowO_succ]
    refine ⟨?_, fun X => killO_restrO (fun U => killO_KnextO_pt h1 h2 U) X⟩
    simp only [laOf_toV]
    exact nextObs_la_pt h1 h2

/-- The `a` data of the steps (`λ_{a,j+1}`, `γ_{a,j+1}` of `nextObs`) do not depend on the
partner point. -/
theorem nextObs_flowO_a_indep {Vo₀ Vo₀' : Coup c} (hla : laOf c Vo₀ = laOf c Vo₀')
    (a b b' : Lam d L N) (j : ℕ) :
    laOf c (nextObs (Flow.covAt d L N msq j) j (flowO d L c N msq V₀ Vo₀ a b j).1
        (flowO d L c N msq V₀ Vo₀ a b j).2 a b) =
      laOf c (nextObs (Flow.covAt d L N msq j) j (flowO d L c N msq V₀ Vo₀' a b' j).1
        (flowO d L c N msq V₀ Vo₀' a b' j).2 a b') ∧
    gaOf c (nextObs (Flow.covAt d L N msq j) j (flowO d L c N msq V₀ Vo₀ a b j).1
        (flowO d L c N msq V₀ Vo₀ a b j).2 a b) =
      gaOf c (nextObs (Flow.covAt d L N msq j) j (flowO d L c N msq V₀ Vo₀' a b' j).1
        (flowO d L c N msq V₀ Vo₀' a b' j).2 a b') := by
  obtain ⟨h1, h2⟩ := flowO_a_indep msq V₀ hla a b b' j
  exact ⟨nextObs_la_pt h1 h2, nextObs_ga_pt h1 h2⟩

/-- **The `b` part of the observable flow does not depend on the partner point**: for
any `a, a'` and initial coupling constants with the same `λ_b`, `λ_{b,j}` and
`(π_∅ + π_b) K_j` agree for all `j`. -/
theorem flowO_b_indep {Vo₀ Vo₀' : Coup c} (hlb : lbOf c Vo₀ = lbOf c Vo₀') (a a' b : Lam d L N) :
    ∀ j, lbOf c (flowO d L c N msq V₀ Vo₀ a b j).1 = lbOf c (flowO d L c N msq V₀ Vo₀' a' b j).1 ∧
      ∀ X, killBO ((flowO d L c N msq V₀ Vo₀ a b j).2 X) =
        killBO ((flowO d L c N msq V₀ Vo₀' a' b j).2 X)
  | 0 => ⟨hlb, fun _ => rfl⟩
  | j + 1 => by
    obtain ⟨h1, h2⟩ := flowO_b_indep hlb a a' b j
    rw [flowO_succ, flowO_succ]
    refine ⟨?_, fun X => killBO_restrO (fun U => killBO_KnextO h1 h2 U) X⟩
    simp only [lbOf_toV]
    exact nextObs_lb_pt h1 h2

/-- The `b` data of the steps (`λ_{b,j+1}`, `γ_{b,j+1}` of `nextObs`) do not depend on the
partner point. -/
theorem nextObs_flowO_b_indep {Vo₀ Vo₀' : Coup c} (hlb : lbOf c Vo₀ = lbOf c Vo₀')
    (a a' b : Lam d L N) (j : ℕ) :
    lbOf c (nextObs (Flow.covAt d L N msq j) j (flowO d L c N msq V₀ Vo₀ a b j).1
        (flowO d L c N msq V₀ Vo₀ a b j).2 a b) =
      lbOf c (nextObs (Flow.covAt d L N msq j) j (flowO d L c N msq V₀ Vo₀' a' b j).1
        (flowO d L c N msq V₀ Vo₀' a' b j).2 a' b) ∧
    gbOf c (nextObs (Flow.covAt d L N msq j) j (flowO d L c N msq V₀ Vo₀ a b j).1
        (flowO d L c N msq V₀ Vo₀ a b j).2 a b) =
      gbOf c (nextObs (Flow.covAt d L N msq j) j (flowO d L c N msq V₀ Vo₀' a' b j).1
        (flowO d L c N msq V₀ Vo₀' a' b j).2 a' b) := by
  obtain ⟨h1, h2⟩ := flowO_b_indep msq V₀ hlb a a' b j
  exact ⟨nextObs_lb_pt h1 h2, nextObs_gb_pt h1 h2⟩

end Flow

end

end Obs
