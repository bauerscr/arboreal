import Flow.Continuity
import Obs.Consist
import Obs.FlowObsCoeff

/-!
# Regularity in a parameter: the algebra with observables and the coupling constants

For a class `R : Reg T` of regular scalar functions (`Step.Reg`, `Step/Reg.lean`):

* `RegS R f` / `RegO R f`: a family of elements of `SA c Λ` / `OE c Λ` is regular if its four
  components `e, a, b, ab` are coefficient-wise regular (`RegN`); for `Reg.cont S` this is the
  `CCE`-analogue for `OE c Λ` (componentwise continuity of all coefficients).  This class is
  closed under the algebra operations, `θ`, `ι`, `𝔼_{C(t)}` (for regular `C`), `Loc`, `π_obs`,
  `oexp` (for vanishing constant term), `emb` and `bulk`.
* `RegCp R W`: a family of observable coupling constants is regular if all the accessors
  `laOf, lbOf, gaOf, gbOf, qaOf, qbOf, etaOf, raOf, rbOf` are regular.  This class is closed
  under `Coup.sub`, `Coup.toV`, `Coup.toU`, `Coup.next` (with regular `c_ab, c_aa, c_bb`), and
  `Qcoup` of a regular activity; `splitO` of regular coupling constants is regular.
-/

namespace Obs

noncomputable section

open Finset Grassmann SA Loc Step LocObs

variable {T : Type*} {R : Reg T} {c : Case}

/-! ### Elements of the algebra with observables -/

section RegO

variable {Λ Λ' : Type*} [DecidableEq Λ] [Fintype Λ] [DecidableEq Λ'] [Fintype Λ']

/-- Componentwise (coefficient-wise) regularity of a family in `SA c Λ`. -/
structure RegS (R : Reg T) (f : T → SA c Λ) : Prop where
  e : RegN R (fun t => (f t).e)
  a : RegN R (fun t => (f t).a)
  b : RegN R (fun t => (f t).b)
  ab : RegN R (fun t => (f t).ab)

/-- Componentwise (coefficient-wise) regularity of a family in `OE c Λ`; for `Reg.cont S`
the `CCE`-analogue for `OE c Λ`. -/
def RegO (R : Reg T) (f : T → OE c Λ) : Prop := RegS R (fun t => (f t : SA c Λ))

/-- A family of activities with observables is regular if all its values are. -/
def RegKO (R : Reg T) (K : T → Finset Λ → OE c Λ) : Prop := ∀ X, RegO R (fun t => K t X)

theorem _root_.Step.RegN.algebraMap {r : T → ℂ} (hr : R.P r) :
    RegN R (fun t => algebraMap ℂ (N Λ) (r t)) :=
  RegN.of_eq (RegN.smul hr (RegN.const 1)) fun _ => Algebra.algebraMap_eq_smul_one _

theorem RegO.of_eq {f g : T → OE c Λ} (hf : RegO R f) (h : ∀ t, g t = f t) : RegO R g := by
  rwa [show g = f from funext h]

theorem RegO.congr {f g : T → OE c Λ} (hf : RegO R f) (h : ∀ t ∈ R.D, g t = f t) : RegO R g :=
  ⟨hf.e.congr fun t ht => by rw [h t ht], hf.a.congr fun t ht => by rw [h t ht],
    hf.b.congr fun t ht => by rw [h t ht], hf.ab.congr fun t ht => by rw [h t ht]⟩

theorem RegO.const (F : OE c Λ) : RegO R (fun _ => F) :=
  ⟨RegN.const _, RegN.const _, RegN.const _, RegN.const _⟩

theorem RegO.add {f g : T → OE c Λ} (hf : RegO R f) (hg : RegO R g) :
    RegO R (fun t => f t + g t) :=
  ⟨hf.e.add hg.e, hf.a.add hg.a, hf.b.add hg.b, hf.ab.add hg.ab⟩

theorem RegO.neg {f : T → OE c Λ} (hf : RegO R f) : RegO R (fun t => -f t) :=
  ⟨hf.e.neg, hf.a.neg, hf.b.neg, hf.ab.neg⟩

theorem RegO.sub {f g : T → OE c Λ} (hf : RegO R f) (hg : RegO R g) :
    RegO R (fun t => f t - g t) :=
  ⟨hf.e.sub hg.e, hf.a.sub hg.a, hf.b.sub hg.b, hf.ab.sub hg.ab⟩

theorem RegO.smul {r : T → ℂ} {f : T → OE c Λ} (hr : R.P r) (hf : RegO R f) :
    RegO R (fun t => r t • f t) :=
  ⟨RegN.smul hr hf.e, RegN.smul hr hf.a, RegN.smul hr hf.b, RegN.smul hr hf.ab⟩

theorem RegO.sum {ι : Type*} (s : Finset ι) {f : ι → T → OE c Λ} (hf : ∀ i ∈ s, RegO R (f i)) :
    RegO R (fun t => ∑ i ∈ s, f i t) := by
  refine ⟨RegN.of_eq (RegN.sum s fun i hi => (hf i hi).e) fun t => ?_,
    RegN.of_eq (RegN.sum s fun i hi => (hf i hi).a) fun t => ?_,
    RegN.of_eq (RegN.sum s fun i hi => (hf i hi).b) fun t => ?_,
    RegN.of_eq (RegN.sum s fun i hi => (hf i hi).ab) fun t => ?_⟩
  · rw [AddSubmonoidClass.coe_finsetSum, SA.sum_e]
  · rw [AddSubmonoidClass.coe_finsetSum, SA.sum_a]
  · rw [AddSubmonoidClass.coe_finsetSum, SA.sum_b]
  · rw [AddSubmonoidClass.coe_finsetSum, SA.sum_ab]

theorem RegO.mul {f g : T → OE c Λ} (hf : RegO R f) (hg : RegO R g) :
    RegO R (fun t => f t * g t) := by
  refine ⟨hf.e.mul hg.e, ?_, ?_, ?_⟩
  · exact ((hf.e.map c.tau.toLinearMap).mul hg.a).add (hf.a.mul hg.e)
  · exact ((hf.e.map c.tau.toLinearMap).mul hg.b).add (hf.b.mul hg.e)
  · exact (((hf.e.mul hg.ab).add ((hf.a.map c.tau.toLinearMap).mul hg.b)).add
      (RegN.smul (R.const c.s) ((hf.b.map c.tau.toLinearMap).mul hg.a))).add (hf.ab.mul hg.e)

theorem RegO.prod {ι : Type*} (s : Finset ι) {f : ι → T → OE c Λ} (hf : ∀ i ∈ s, RegO R (f i)) :
    RegO R (fun t => ∏ i ∈ s, f i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact RegO.of_eq (RegO.const 1) fun t => by simp
  | insert a s ha ih =>
    exact RegO.of_eq ((hf a (mem_insert_self a s)).mul (ih fun i hi => hf i (mem_insert_of_mem hi)))
      fun t => by rw [prod_insert ha]

theorem RegO.pow {f : T → OE c Λ} (hf : RegO R f) (k : ℕ) : RegO R (fun t => f t ^ k) := by
  induction k with
  | zero => exact RegO.of_eq (RegO.const 1) fun t => by simp
  | succ k ih => exact RegO.of_eq (ih.mul hf) fun t => by rw [pow_succ]

theorem RegO.algebraMap {r : T → ℂ} (hr : R.P r) :
    RegO R (fun t => algebraMap ℂ (OE c Λ) (r t)) :=
  ⟨RegN.of_eq (RegN.algebraMap hr) fun t => SA.algebraMap_e (c := c) (r t),
    RegN.of_eq (RegN.const 0) fun t => SA.algebraMap_a (c := c) (r t),
    RegN.of_eq (RegN.const 0) fun t => SA.algebraMap_b (c := c) (r t),
    RegN.of_eq (RegN.const 0) fun t => SA.algebraMap_ab (c := c) (r t)⟩

theorem RegO.emb {x : T → EvR Λ} (hx : RegE R x) : RegO R (fun t => (emb (x t) : OE c Λ)) :=
  ⟨hx, RegN.const 0, RegN.const 0, RegN.const 0⟩

theorem RegO.bulk {f : T → OE c Λ} (hf : RegO R f) : RegE R (fun t => bulk (f t)) := hf.e

theorem RegO.thetaO {f : T → OE c Λ} (hf : RegO R f) : RegO R (fun t => thetaO (f t)) :=
  ⟨hf.e.map theta.toLinearMap, hf.a.map theta.toLinearMap, hf.b.map theta.toLinearMap,
    hf.ab.map theta.toLinearMap⟩

theorem RegO.inclO {f : T → OE c Λ} (hf : RegO R f) : RegO R (fun t => inclO (f t)) :=
  ⟨hf.e.map incl.toLinearMap, hf.a.map incl.toLinearMap, hf.b.map incl.toLinearMap,
    hf.ab.map incl.toLinearMap⟩

theorem RegO.ECO {C : T → Matrix Λ Λ ℝ} (hC : ∀ x y, R.P (fun t => ((C t x y : ℝ) : ℂ)))
    {f : T → OE c (Λ ⊕ Λ)} (hf : RegO R f) : RegO R (fun t => ECO (C t) (f t)) :=
  ⟨RegN.EC hC hf.e, RegN.EC hC hf.a, RegN.EC hC hf.b, RegN.EC hC hf.ab⟩

/-- The exponential of a family with vanishing constant term. -/
theorem RegO.oexp {f : T → OE c Λ} (hf : RegO R f)
    (h0 : ∀ t ∈ R.D, ε ((f t : OE c Λ) : SA c Λ).e = 0) : RegO R (fun t => oexp (f t)) :=
  RegO.congr (RegO.sum (range (Nf Λ + 3)) fun i _ => RegO.smul (R.const _) (hf.pow i))
    fun t ht => coe_oexp (pow_eq_zero_of_ε (h0 t ht))

end RegO

/-! ### `Loc` -/

section Loc

variable {d L N : ℕ} [NeZero L]

theorem Reg.mass1 {f : T → Alg d L N} (hf : RegN R f) (s : ℤˣ) :
    R.P (fun t => mass1 s (f t)) :=
  Reg.sum _ fun x _ => hf 1 ![(x, s)]

theorem Reg.mass2 {f : T → Alg d L N} (hf : RegN R f) : R.P (fun t => mass2 (f t)) :=
  Reg.sum _ fun x _ => Reg.sum _ fun y _ => hf 2 ![(x, -1), (y, 1)]

theorem Reg.eps {I : Type*} [DecidableEq I] [Fintype I] {f : T → Grassmann.N I}
    (hf : RegN R f) : R.P (fun t => ε (f t)) :=
  hf.lin (ε : Grassmann.N I →ₐ[ℂ] ℂ).toLinearMap

theorem _root_.Step.RegN.locGen {P X Y : Finset (Lam d L N)} (g : Lam d L N → Alg d L N) {r : T → ℂ}
    (hr : R.P r) : RegN R (fun t => locGen P X Y g (r t)) :=
  RegN.smul (Reg.div_const hr _) (RegN.const _)

theorem _root_.Step.RegN.locOdd {f : T → Alg d L N} (hf : RegN R f) (s : ℤˣ) (P X Y : Finset (Lam d L N)) :
    RegN R (fun t => locOdd s P X Y (f t)) :=
  RegN.locGen _ (Reg.mass1 hf s)

theorem _root_.Step.RegN.locEven {f : T → Alg d L N} (hf : RegN R f) (P X Y : Finset (Lam d L N)) :
    RegN R (fun t => locEven P X Y (f t)) :=
  (RegN.locGen _ (Reg.eps hf)).add (RegN.locGen _ (Reg.mass2 hf))

theorem RegO.LocO {f : T → OE c (Lam d L N)} (hf : RegO R f) (a b : Lam d L N)
    (X Y : Finset (Lam d L N)) : RegO R (fun t => LocO a b X Y (f t)) := by
  refine ⟨hf.e.map (LocL X Y), ?_, ?_, hf.ab.locEven _ X Y⟩
  · cases c
    · exact hf.a.locOdd _ _ X Y
    · exact hf.a.locEven _ X Y
  · cases c
    · exact hf.b.locOdd _ _ X Y
    · exact hf.b.locEven _ X Y

theorem RegKO.restrO {K : T → Finset (Lam d L N) → OE c (Lam d L N)} (hK : RegKO R K) (j : ℕ) :
    RegKO R (fun t => restrO j (K t)) := by
  classical
  intro X
  by_cases hX : IsConn j X
  · exact RegO.of_eq (hK X) fun t => restrO_of_conn _ hX
  · exact RegO.of_eq (RegO.const 0) fun t => by simp [Obs.restrO, hX]

theorem RegKO.bulkK {K : T → Finset (Lam d L N) → OE c (Lam d L N)} (hK : RegKO R K) :
    RegK R (fun t => bulkK (K t)) := fun X => (hK X).bulk

end Loc

/-! ### Observable coupling constants -/

section Coup

/-- A regular family of observable coupling constants: all accessors are regular. -/
structure RegCp (R : Reg T) (W : T → Coup c) : Prop where
  la : R.P (fun t => laOf c (W t))
  lb : R.P (fun t => lbOf c (W t))
  ga : R.P (fun t => gaOf c (W t))
  gb : R.P (fun t => gbOf c (W t))
  qa : R.P (fun t => qaOf c (W t))
  qb : R.P (fun t => qbOf c (W t))
  eta : R.P (fun t => etaOf c (W t))
  ra : R.P (fun t => raOf c (W t))
  rb : R.P (fun t => rbOf c (W t))

theorem RegCp.const (V : Coup c) : RegCp R (fun _ => V) :=
  ⟨R.const _, R.const _, R.const _, R.const _, R.const _, R.const _, R.const _, R.const _,
    R.const _⟩

theorem RegCp.of_eq {W W' : T → Coup c} (hW : RegCp R W) (h : ∀ t, W' t = W t) : RegCp R W' := by
  rwa [show W' = W from funext h]

theorem RegCp.sub {W W' : T → Coup c} (hW : RegCp R W) (hW' : RegCp R W') :
    RegCp R (fun t => Coup.sub c (W t) (W' t)) := by
  cases c
  · exact ⟨Reg.sub hW.la hW'.la, Reg.sub hW.lb hW'.lb, R.const 0, R.const 0,
      Reg.sub hW.qa hW'.qa, Reg.sub hW.qb hW'.qb, R.const 0, Reg.sub hW.ra hW'.ra,
      Reg.sub hW.rb hW'.rb⟩
  · exact ⟨Reg.sub hW.la hW'.la, Reg.sub hW.lb hW'.lb, Reg.sub hW.ga hW'.ga,
      Reg.sub hW.gb hW'.gb, Reg.sub hW.qa hW'.qa, Reg.sub hW.qb hW'.qb, Reg.sub hW.eta hW'.eta,
      Reg.sub hW.ra hW'.ra, Reg.sub hW.rb hW'.rb⟩

theorem RegCp.toV {W : T → Coup c} (hW : RegCp R W) : RegCp R (fun t => Coup.toV c (W t)) := by
  cases c
  · exact ⟨hW.la, hW.lb, R.const 0, R.const 0, R.const 0, R.const 0, R.const 0, hW.ra, hW.rb⟩
  · exact ⟨hW.la, hW.lb, R.const 0, R.const 0, R.const 0, R.const 0, hW.eta, hW.ra, hW.rb⟩

theorem RegCp.toU {W : T → Coup c} (hW : RegCp R W) : RegCp R (fun t => Coup.toU c (W t)) := by
  cases c
  · exact ⟨R.const 0, R.const 0, R.const 0, R.const 0, hW.qa, hW.qb, R.const 0, R.const 0,
      R.const 0⟩
  · exact ⟨R.const 0, R.const 0, hW.ga, hW.gb, hW.qa, hW.qb, R.const 0, R.const 0, R.const 0⟩

/-- The free flow of the coupling constants (`lem:Vobs-flow-free`) preserves regularity. -/
theorem RegCp.next {W : T → Coup c} (hW : RegCp R W) {cab caa cbb : T → ℂ} (hab : R.P cab)
    (haa : R.P caa) (hbb : R.P cbb) :
    RegCp R (fun t => Coup.next c (W t) (cab t) (caa t) (cbb t)) := by
  cases c
  · exact ⟨hW.la, hW.lb, R.const 0, R.const 0,
      Reg.sub (R.add hW.qa (Reg.div_const (R.mul (R.mul hW.la hW.lb) hab) 2)) (R.mul hW.ra haa),
      Reg.sub (R.add hW.qb (Reg.div_const (R.mul (R.mul hW.la hW.lb) hab) 2)) (R.mul hW.rb hbb),
      R.const 0, hW.ra, hW.rb⟩
  · exact ⟨hW.la, hW.lb, R.add hW.ga (R.mul hW.la haa), R.add hW.gb (R.mul hW.lb hbb),
      Reg.sub (Reg.sub (R.add hW.qa (Reg.div_const (R.mul hW.eta hab) 2)) (R.mul hW.ra haa))
        (Reg.div_const (R.mul (R.mul hW.la hW.lb) (Reg.pow hab 2)) 2),
      Reg.sub (Reg.sub (R.add hW.qb (Reg.div_const (R.mul hW.eta hab) 2)) (R.mul hW.rb hbb))
        (Reg.div_const (R.mul (R.mul hW.la hW.lb) (Reg.pow hab 2)) 2),
      Reg.sub hW.eta (R.mul (Reg.const_mul 2 hW.la |> fun h => R.mul h hW.lb) hab),
      hW.ra, hW.rb⟩

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

theorem RegO.halfAO {W : T → Coup c} (hW : RegCp R W) (a b : Λ) :
    RegO R (fun t => halfAO c (W t) a b) := by
  cases c
  · exact ⟨RegN.const 0, RegN.smul (Reg.neg hW.la) (RegN.const _), RegN.const 0,
      (RegN.algebraMap (Reg.neg hW.qa)).add (RegN.smul hW.ra (RegN.const _))⟩
  · exact ⟨RegN.const 0,
      (RegN.algebraMap (Reg.neg hW.ga)).sub (RegN.smul hW.la (RegN.const _)), RegN.const 0,
      ((RegN.algebraMap (Reg.neg hW.qa)).sub (RegN.smul (Reg.div_const hW.eta 4)
        (RegN.const _))).add (RegN.smul hW.ra (RegN.const _))⟩

theorem RegO.halfBO {W : T → Coup c} (hW : RegCp R W) (a b : Λ) :
    RegO R (fun t => halfBO c (W t) a b) := by
  cases c
  · exact ⟨RegN.const 0, RegN.const 0, RegN.smul hW.lb (RegN.const _),
      (RegN.algebraMap (Reg.neg hW.qb)).add (RegN.smul hW.rb (RegN.const _))⟩
  · exact ⟨RegN.const 0, RegN.const 0,
      (RegN.algebraMap (Reg.neg hW.gb)).sub (RegN.smul hW.lb (RegN.const _)),
      ((RegN.algebraMap (Reg.neg hW.qb)).sub (RegN.smul (Reg.div_const hW.eta 4)
        (RegN.const _))).add (RegN.smul hW.rb (RegN.const _))⟩

theorem RegO.splitO {W : T → Coup c} (hW : RegCp R W) (a b : Λ) (X : Finset Λ) :
    RegO R (fun t => splitO c (W t) a b X) :=
  (RegO.smul (R.const _) (RegO.halfAO hW a b)).add (RegO.smul (R.const _) (RegO.halfBO hW a b))

end Coup

/-! ### `Q^obs`, `V_j(X)`, `u^obs_{j+1}(X)` -/

section Q

variable {d L N : ℕ} [NeZero L]

theorem RegCp.Qcoup {K : T → Finset (Lam d L N) → OE c (Lam d L N)} (hK : RegKO R K) (j : ℕ)
    (a b : Lam d L N) : RegCp R (fun t => Qcoup c j (K t) a b) := by
  by_cases hj : j + 1 < N
  · cases c
    · refine RegCp.of_eq (W := fun t => (⟨-∑ X ∈ smallAt j a,
          mass1 (-1) ((K t X : SA .one (Lam d L N)).a),
        ∑ X ∈ smallAt j b, mass1 1 ((K t X : SA .one (Lam d L N)).b),
        -∑ X ∈ smallAt j a, ε ((K t X : SA .one (Lam d L N)).ab) / cardAB a b X,
        -∑ X ∈ smallAt j b, ε ((K t X : SA .one (Lam d L N)).ab) / cardAB a b X,
        ∑ X ∈ smallAt j a, mass2 ((K t X : SA .one (Lam d L N)).ab) / cardAB a b X,
        ∑ X ∈ smallAt j b, mass2 ((K t X : SA .one (Lam d L N)).ab) / cardAB a b X⟩ : Coup1))
        ?_ fun t => by simp only [Obs.Qcoup, if_pos hj]
      exact ⟨Reg.neg (Reg.sum _ fun X _ => Reg.mass1 (hK X).a _),
        Reg.sum _ fun X _ => Reg.mass1 (hK X).b _, R.const 0, R.const 0,
        Reg.neg (Reg.sum _ fun X _ => Reg.div_const (Reg.eps (hK X).ab) _),
        Reg.neg (Reg.sum _ fun X _ => Reg.div_const (Reg.eps (hK X).ab) _), R.const 0,
        Reg.sum _ fun X _ => Reg.div_const (Reg.mass2 (hK X).ab) _,
        Reg.sum _ fun X _ => Reg.div_const (Reg.mass2 (hK X).ab) _⟩
    · refine RegCp.of_eq (W := fun t => (⟨-∑ X ∈ smallAt j a,
          mass2 ((K t X : SA .two (Lam d L N)).a),
        -∑ X ∈ smallAt j b, mass2 ((K t X : SA .two (Lam d L N)).b),
        -∑ X ∈ smallAt j a, ε ((K t X : SA .two (Lam d L N)).a),
        -∑ X ∈ smallAt j b, ε ((K t X : SA .two (Lam d L N)).b),
        -∑ X ∈ smallAt j a, ε ((K t X : SA .two (Lam d L N)).ab) / cardAB a b X,
        -∑ X ∈ smallAt j b, ε ((K t X : SA .two (Lam d L N)).ab) / cardAB a b X, 0,
        ∑ X ∈ smallAt j a, mass2 ((K t X : SA .two (Lam d L N)).ab) / cardAB a b X,
        ∑ X ∈ smallAt j b, mass2 ((K t X : SA .two (Lam d L N)).ab) / cardAB a b X⟩ : Coup2))
        ?_ fun t => by simp only [Obs.Qcoup, if_pos hj]
      exact ⟨Reg.neg (Reg.sum _ fun X _ => Reg.mass2 (hK X).a),
        Reg.neg (Reg.sum _ fun X _ => Reg.mass2 (hK X).b),
        Reg.neg (Reg.sum _ fun X _ => Reg.eps (hK X).a),
        Reg.neg (Reg.sum _ fun X _ => Reg.eps (hK X).b),
        Reg.neg (Reg.sum _ fun X _ => Reg.div_const (Reg.eps (hK X).ab) _),
        Reg.neg (Reg.sum _ fun X _ => Reg.div_const (Reg.eps (hK X).ab) _), R.const 0,
        Reg.sum _ fun X _ => Reg.div_const (Reg.mass2 (hK X).ab) _,
        Reg.sum _ fun X _ => Reg.div_const (Reg.mass2 (hK X).ab) _⟩
  · exact RegCp.of_eq (RegCp.const (Coup.zero c)) fun t => Qcoup_of_not hj _ a b

theorem RegO.VfullX {Vb : T → Vcoup} {Vo : T → Coup c} (hVb : RegV R Vb) (hVo : RegCp R Vo)
    (a b : Lam d L N) (X : Finset (Lam d L N)) :
    RegO R (fun t => VfullX (Vb t) (Vo t) a b X) :=
  (RegO.emb (hVb.VE X)).add (RegO.splitO hVo.toV a b X)

/-- **The observable coupling constants `(u + V)^obs_{j+1}` are regular** (for a regular
covariance, observable coupling constants and activity). -/
theorem RegCp.nextObs {C : T → Matrix (Lam d L N) (Lam d L N) ℝ}
    (hC : ∀ x y, R.P (fun t => ((C t x y : ℝ) : ℂ))) (j : ℕ) {Vo : T → Coup c}
    (hVo : RegCp R Vo) {K : T → Finset (Lam d L N) → OE c (Lam d L N)} (hK : RegKO R K)
    (a b : Lam d L N) : RegCp R (fun t => nextObs (C t) j (Vo t) (K t) a b) :=
  RegCp.next (hVo.toV.sub (RegCp.Qcoup hK j a b)) (hC a b) (hC a a) (hC b b)

theorem RegO.uObsX {C : T → Matrix (Lam d L N) (Lam d L N) ℝ}
    (hC : ∀ x y, R.P (fun t => ((C t x y : ℝ) : ℂ))) (j : ℕ) {Vo : T → Coup c}
    (hVo : RegCp R Vo) {K : T → Finset (Lam d L N) → OE c (Lam d L N)} (hK : RegKO R K)
    (a b : Lam d L N) (X : Finset (Lam d L N)) :
    RegO R (fun t => uObsX j (C t) (Vo t) (K t) a b X) :=
  RegO.splitO (RegCp.nextObs hC j hVo hK a b).toU a b X

end Q

end

end Obs
