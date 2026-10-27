import Obs.ContObsAlg

/-!
# Regularity in a parameter of the observable renormalisation group map and flow

For a class `R : Reg T` of regular scalar functions (`Step.Reg`, `Step/Reg.lean`):

* `RegO.QO`, `RegO.JO`: `Q(B)` and `J(B, X)` of a regular activity are regular;
* `RegO.KnextG_obs`: the generic `K_{j+1}(U)` (`Gen.KnextG`) with the algebra `obsA c C(t)` is
  regular if all ingredients are;
* `RegO.KnextO`: **the observable map `K_{j+1}` is regular** along regular families
  `(C(t), V^∅(t), V^obs(t), K(t))` (with `C(t)` invariant, symmetric, and `π_∅ K(t) ∈ 𝒦_j` on the
  domain);
* `flowO_reg`: **regularity along the observable flow** `Obs.flowO`: if `V₀(t)`, `V^obs_0(t)`
  and the covariances `C_{j+1}(μ(t))` are regular (and `GoodCov` holds on the domain), then so
  are `V^obs_j` (all accessors) and `K_j(X)` (componentwise, coefficient-wise), `j ≤ N`;
  `nextObs_flowO_reg`, `uObsX_flowO_reg`: the same for `(u + V)^obs_{j+1}` and `u^obs_{j+1}(X)`,
  `j < N`.
-/

namespace Obs

noncomputable section

open Finset Grassmann SA Loc Step LocObs Gen

variable {T : Type*} {R : Reg T} {c : Case} {d L N : ℕ} [NeZero L]

theorem RegO.JO {K : T → Finset (Lam d L N) → OE c (Lam d L N)} (hK : RegKO R K)
    (a b : Lam d L N) (j : ℕ) (p : Fin d → ℕ) (X : Finset (Lam d L N)) :
    RegO R (fun t => JO a b j (K t) p X) := by
  unfold Obs.JO
  split_ifs
  · exact (RegO.sum _ fun Y _ => (hK Y).LocO a b _ _).neg
  · exact (hK X).LocO a b _ _
  · exact RegO.const 0

/-- The generic `K_{j+1}(U)` with the algebra of observables is regular if all ingredients
are. -/
theorem RegO.KnextG_obs {C : T → Matrix (Lam d L N) (Lam d L N) ℝ}
    (hC : ∀ x y, R.P (fun t => ((C t x y : ℝ) : ℂ)))
    {F : T → RGIngr d L N (OE c (Lam d L N))}
    (hI0 : ∀ p, RegO R (fun t => (F t).I0 p)) (heV : ∀ p, RegO R (fun t => (F t).eV p))
    (heu : ∀ p, RegO R (fun t => (F t).eu p)) (heum : ∀ p, RegO R (fun t => (F t).eum p))
    (hJ : ∀ p X, RegO R (fun t => (F t).J p X)) (hK : ∀ X, RegO R (fun t => (F t).K X))
    (j : ℕ) (U : Finset (Lam d L N)) :
    RegO R (fun t => KnextG (obsA c (C t)) j (F t) U) := by
  have hIt : ∀ p, RegO R (fun t => It (F t) p) := fun p => (heum p).mul (heV p)
  have hItPow : ∀ X, RegO R (fun t => ItPow j (F t) X) := fun X =>
    RegO.prod _ fun p _ => hIt p
  have hdI : ∀ X, RegO R (fun t => dIPowG (obsA c (C t)) j (F t) X) := fun X =>
    RegO.prod _ fun p _ => (hI0 p).thetaO.sub (hIt p).inclO
  have hKext : ∀ X, RegO R (fun t => KextG j (F t).K X) := fun X =>
    RegO.prod _ fun Y _ => hK Y
  have hKt : ∀ W, RegO R (fun t => KtilG (obsA c (C t)) j (F t) W) := fun W =>
    RegO.sum _ fun Y _ => (hKext _).thetaO.mul (hdI Y)
  have hKc : ∀ W, RegO R (fun t => KchkCG (obsA c (C t)) j (F t) W) := fun W =>
    (hKt W).sub (RegO.sum _ fun p _ => (hJ p W).thetaO)
  have hKch : ∀ X, RegO R (fun t => KchkG (obsA c (C t)) j (F t) X) := fun X =>
    RegO.prod _ fun W _ => hKc W
  have hJp : ∀ 𝒳, RegO R (fun t => JprodG (obsA c (C t)) (F t) 𝒳) := fun 𝒳 =>
    RegO.prod _ fun p _ => (hJ p.1 p.2).thetaO
  unfold KnextG PrefG KtermG
  exact (RegO.prod _ fun p _ => heu p).mul
    (RegO.sum _ fun g _ => (hItPow _).mul (RegO.ECO hC ((hKch _).mul (hJp _))))

/-- **Regularity of the observable map `K_{j+1}`** along regular families
`(C(t), V^∅(t), V^obs(t), K(t))`. -/
theorem RegO.KnextO (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {j : ℕ} (hj : j < N)
    {C : T → Matrix (Lam d L N) (Lam d L N) ℝ}
    (hC : ∀ x y, R.P (fun t => ((C t x y : ℝ) : ℂ)))
    (hinv : ∀ t ∈ R.D, CovInv (C t)) (hsym : ∀ t ∈ R.D, ∀ x y, C t x y = C t y x)
    {Vb : T → Vcoup} {Vo : T → Coup c} {K : T → Finset (Lam d L N) → OE c (Lam d L N)}
    (hVb : RegV R Vb) (hVo : RegCp R Vo) (hK : RegKO R K)
    (hKj : ∀ t ∈ R.D, InK j (bulkK (K t))) (a b : Lam d L N) (U : Finset (Lam d L N)) :
    RegO R (fun t => KnextO j (C t) (Vb t) (Vo t) (K t) a b U) := by
  obtain ⟨hu, hU⟩ := uVnext_reg hd hL hj hC hinv hsym hVb hK.bulkK hKj
  have hnext := RegCp.nextObs hC j hVo hK a b
  have hobs := fun X => RegO.uObsX hC j hVo hK a b X
  unfold Obs.KnextO
  refine RegO.KnextG_obs (F := fun t => obsI j (C t) (Vb t) (Vo t) (K t) a b) hC
    (fun p => ?_) (fun p => ?_) (fun p => ?_) (fun p => ?_)
    (fun p X => RegO.JO hK a b j p X) (fun X => hK X) j U
  · exact RegO.oexp (RegO.VfullX hVb hVo a b _).neg fun t _ => ε_neg_VfullX a b _ _ _
  · exact RegO.oexp (RegO.VfullX hU hnext a b _).neg fun t _ => ε_neg_VfullX a b _ _ _
  · exact (RegO.algebraMap (R.exp (Reg.mul_const hu _))).mul
      (RegO.oexp (hobs _) fun t _ => ε_bulk_eq_zero_of_obs (bulk_uObsX _ _ _ _ _ _ _))
  · exact (RegO.algebraMap (R.exp (Reg.neg (Reg.mul_const hu _)))).mul
      (RegO.oexp (hobs _).neg fun t _ => ε_bulk_eq_zero_of_obs (by
        rw [map_neg, bulk_uObsX, neg_zero]))

/-- **Regularity along the observable flow** (`Obs.flowO`), for `j ≤ N`. -/
theorem flowO_reg (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {ℓ₀ : ℝ} {μ : T → ℝ} {V₀ : T → Vcoup}
    {Vo₀ : T → Coup c} (hV₀ : RegV R V₀) (hVo₀ : RegCp R Vo₀)
    (hC : ∀ j < N, ∀ x y, R.P (fun t => ((Flow.covAt d L N (μ t) j x y : ℝ) : ℂ)))
    (hgood : ∀ t ∈ R.D, ∀ j < N,
      GoodCov (d := d) (L := L) (N := N) j ℓ₀ (Flow.covAt d L N (μ t) j))
    (a b : Lam d L N) :
    ∀ j ≤ N, RegCp R (fun t => (flowO d L c N (μ t) (V₀ t) (Vo₀ t) a b j).1) ∧
      RegKO R (fun t => (flowO d L c N (μ t) (V₀ t) (Vo₀ t) a b j).2) := by
  intro j
  induction j with
  | zero => exact fun _ => ⟨hVo₀, fun X => RegO.of_eq (RegO.const 0) fun t => rfl⟩
  | succ j ih =>
    intro hj
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hbulk := (Flow.flowN_reg hd hL hV₀ hC hgood j (by omega)).1
    have hKj : ∀ t ∈ R.D, InK j (bulkK (flowO d L c N (μ t) (V₀ t) (Vo₀ t) a b j).2) :=
      fun t ht => by
        rw [bulkK_flowO]
        exact Flow.InK_flowN hd hL (hgood t ht) (V₀ t) j (by omega)
    have hinv : ∀ t ∈ R.D, CovInv (Flow.covAt d L N (μ t) j) := fun t ht =>
      (hgood t ht j (by omega)).covInv
    have hsym : ∀ t ∈ R.D, ∀ x y, Flow.covAt d L N (μ t) j x y = Flow.covAt d L N (μ t) j y x :=
      fun t ht => (hgood t ht j (by omega)).symm'
    refine ⟨(RegCp.nextObs (hC j (by omega)) j ih1 ih2 a b).toV, ?_⟩
    exact RegKO.restrO (fun U => RegO.KnextO hd hL (by omega) (hC j (by omega)) hinv hsym hbulk
      ih1 ih2 hKj a b U) (j + 1)

/-- The observable coupling constants `(u + V)^obs_{j+1}` produced by step `j < N` of the
observable flow are regular. -/
theorem nextObs_flowO_reg (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {ℓ₀ : ℝ} {μ : T → ℝ}
    {V₀ : T → Vcoup} {Vo₀ : T → Coup c} (hV₀ : RegV R V₀) (hVo₀ : RegCp R Vo₀)
    (hC : ∀ j < N, ∀ x y, R.P (fun t => ((Flow.covAt d L N (μ t) j x y : ℝ) : ℂ)))
    (hgood : ∀ t ∈ R.D, ∀ j < N,
      GoodCov (d := d) (L := L) (N := N) j ℓ₀ (Flow.covAt d L N (μ t) j))
    (a b : Lam d L N) {j : ℕ} (hj : j < N) :
    RegCp R (fun t => nextObs (Flow.covAt d L N (μ t) j) j
      (flowO d L c N (μ t) (V₀ t) (Vo₀ t) a b j).1
      (flowO d L c N (μ t) (V₀ t) (Vo₀ t) a b j).2 a b) := by
  obtain ⟨h1, h2⟩ := flowO_reg hd hL hV₀ hVo₀ hC hgood a b j hj.le
  exact RegCp.nextObs (hC j hj) j h1 h2 a b

end

end Obs
