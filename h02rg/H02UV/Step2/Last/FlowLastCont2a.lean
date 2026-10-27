import Step2.FlowCont.FlowMsqStep
import Step2.Last.LastNStep
import Step2.Map.HolC

/-!
# Continuity of the last step `j = N - 1` in the mass and its inputs

* `LastN.upN_diffC`, `VpN_holC`, `uXN_diffC`, `IpN_holC`, `KN_holC`: covariance-dependent
  versions of the holomorphy lemmas of `LastNSecond` (the covariance is a coordinate as well);
* `lastCov_contM`: the entries of `C'^{≠0}_N = kmat (nzP Γ^int_N)` are jointly continuous in
  `(m², ζ)` (from `CovContM`, as `rawCov_contM`; `nzP` only removes the zero mode);
* `LastCont`: continuity of a family of final-scale objects (`Z_N`, `κ_N`, `u_N(Λ)` continuous,
  `V_N`, `𝒲_N`, `K_N(Λ)` coefficient-wise);
* `rawStepN_contM`: the last raw step is jointly continuous in the mass, the state, `(ǧ, μ)` and
  the inputs `(D, K)` (copy of `rawStep_contM`, through the parameter space `PE` with `r = 1`).
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Set Filter Topology

variable {L N : ℕ} [NeZero L]

namespace LastN

section HolC

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (j : ℕ) {Cf : E → Matrix (Lam d L N) (Lam d L N) ℂ} {Vf Wf : E → Fam d L N}
  {Kf : E → Act d L N} (hCf : ∀ x y, Differentiable ℂ (fun e => Cf e x y))
  (hVf : ∀ b, HolE (fun e => Vf e b)) (hWf : ∀ b, HolE (fun e => Wf e b))
  (hKf : ∀ X, HolE (fun e => Kf e X))

include hCf hVf in
theorem upN_diffC (b : Fin d → ℕ) : Differentiable ℂ (fun e => upN (Cf e) (Vf e) b) :=
  (Vpr_holC hCf hVf b).ε

include hCf hVf in
theorem VpN_holC (b : Fin d → ℕ) : HolE (fun e => VpN (Cf e) (Vf e) b) :=
  (Vpr_holC hCf hVf b).sub (HolE.algMap (upN_diffC hCf hVf b))

include hCf hVf in
theorem uXN_diffC (X : Finset (Lam d L N)) : Differentiable ℂ (fun e => uXN j (Cf e) (Vf e) X) :=
  Differentiable.fun_sum fun b _ => upN_diffC hCf hVf b

include hCf hVf hWf in
theorem IpN_holC (b : Fin d → ℕ) : HolE (fun e => IpN j (Cf e) (Vf e) (Wf e) b) :=
  HolE.smul ((upN_diffC hCf hVf b).neg.cexp)
    (((VpN_holC hCf hVf b).neg.gexp fun e => by
      rw [NegMemClass.coe_neg, map_neg, ε_VpN, neg_zero]).mul
      ((HolE.const 1).add (Sb_holC j hCf hVf hWf b)))

include hCf hVf hWf hKf in
/-- **Holomorphy of `K_N`**, jointly in the covariance. -/
theorem KN_holC (hV0 : ∀ e b, ε (Vf e b : Alg d L N) = 0) (U : Finset (Lam d L N)) :
    HolE (fun e => KN j (Cf e) (Vf e) (Wf e) (Kf e) U) :=
  HolE.smul (uXN_diffC j hCf hVf U).cexp
    (gKnext_holC j hCf hKf (Ib_hol hVf hWf hV0) (IpN_holC j hCf hVf hWf) (J2_hol j hKf) U)

end HolC

end LastN

open MsqJoint DressedFRD DressedFRD.Data

/-- **The covariance of the last step is jointly continuous in the mass and the history.** -/
theorem lastCov_contM {d : ℕ} (P : PtFamily) {ζbar : ℝ}
    (hcov : ∀ j, j < N → ∀ x₀ : ℝ × (Fin (j + 1) → ℂ), 0 < x₀.1 →
      x₀.1 ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) → (∀ i, ‖x₀.2 i‖ ≤ ζbar) →
      ∀ m : Torus d (L ^ N), ContinuousAt (fun p : ℝ × (Fin (j + 1) → ℂ) =>
        (DJ P L N p : DressedFRD.Data d (L ^ N)).Gint j m) x₀)
    (R : RGPar d L N) (hP : R.P = P) {j : ℕ} (hj : j < N) {T : Type*} [TopologicalSpace T]
    {ms : T → ℝ} (hms : Continuous ms) (hms0 : ∀ t, 0 < ms t)
    (hms1 : ∀ t, ms t ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))))
    {ζ : T → ℕ → ℂ} (hζ : ∀ i, Continuous fun t => ζ t i)
    (hb : ∀ t i, ‖ζ t i‖ ≤ ζbar) (h0 : ∀ t i, j < i → ζ t i = 0) (x y : Lam d L N) :
    Continuous fun t => LastN.lastCov (R.withMsq (ms t)) j (ζ t) x y := by
  subst hP
  let zz : T → Fin (j + 1) → ℂ := fun t i => ζ t i
  have hzz : Continuous zz := continuous_pi fun i => hζ i
  have e : ∀ t, LastN.lastCov (R.withMsq (ms t)) j (ζ t) x y =
      DressedFRD.kern (DressedFRD.nzP
        ((DJ R.P L N (ms t, zz t) : DressedFRD.Data d (L ^ N)).Gint j)) (x - y) := by
    intro t
    have : ζ t = DressedFRD.Data.ext (zz t) := by
      funext i
      unfold DressedFRD.Data.ext
      split_ifs with hi
      · rfl
      · exact h0 t i (by omega)
    rw [LastN.lastCov, this]
    rfl
  simp only [e]
  have hp : Continuous fun t => ((ms t, zz t) : ℝ × (Fin (j + 1) → ℂ)) := hms.prodMk hzz
  have hG : ∀ m, Continuous fun t =>
      (DJ R.P L N (ms t, zz t) : DressedFRD.Data d (L ^ N)).Gint j m := fun m =>
    continuous_iff_continuousAt.2 fun t₀ =>
      ContinuousAt.comp (f := fun t => ((ms t, zz t) : ℝ × (Fin (j + 1) → ℂ)))
        (hcov j hj (ms t₀, zz t₀) (hms0 t₀) (hms1 t₀) (fun i => hb t₀ i) m) hp.continuousAt
  unfold DressedFRD.kern
  refine continuous_const.mul (continuous_finsetSum _ fun m _ => ?_)
  refine Continuous.mul ?_ continuous_const
  by_cases hm : m = 0
  · simp only [DressedFRD.nzP, hm, if_true]; exact continuous_const
  · simp only [DressedFRD.nzP, hm, if_false]; exact hG m

/-- **Continuity of a family of final-scale objects**: `Z_N`, the couplings `κ_N` and `u_N(Λ)`
continuous, `V_N(B)`, `𝒲_N(B)` and `K_N(Λ)` coefficient-wise. -/
structure LastCont {T : Type*} [TopologicalSpace T] (f : T → LastN.LastOut 2 L N) : Prop where
  Z : Continuous fun t => (f t).Z
  κz : Continuous fun t => (f t).κ.z
  κy : Continuous fun t => (f t).κ.y
  κnu : Continuous fun t => (f t).κ.nu
  κg : Continuous fun t => (f t).κ.g
  u : Continuous fun t => (f t).u
  V : CF fun t => (f t).V
  W : CF fun t => (f t).W
  K : ∀ n (z : Fin n → Sf (Lam 2 L N)),
    Continuous fun t => coeff (((f t).K : EvR (Lam 2 L N)) : Alg 2 L N) z

/-- An element of `ASp j ℓ A` from an admissible activity. -/
def ASp.mkL {d j : ℕ} {ℓ A : ℝ} (K : Act d L N) (h : K ∈ ASub (L := L) (N := N) j) :
    ASp d L N j ℓ A := ⟨K, h⟩

section Step

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
variable {T : Type*} [TopologicalSpace T]

set_option maxHeartbeats 4000000 in
/-- **The last raw step is jointly continuous** in the mass, the state, the coordinates `(ǧ, μ)`
and the inputs `(D, K)` (`j < N`; no validity hypothesis is needed). -/
theorem rawStepN_contM {j : ℕ} (hρ : 0 ≤ R.ρ) (hρ8 : R.ρ ≤ 1 / 8) (hj : j < N)
    (hcov : CovContM R.P L N 2 R.ρ) {ms : T → ℝ} (hms : Continuous ms) (hms0 : ∀ t, 0 < ms t)
    (hms1 : ∀ t, ms t ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))))
    {f : T → RawSt 2 L N} (hf : StCont f) (hI : ∀ t, RawInv R j (f t)) {g μ : T → ℝ}
    (hg : Continuous g) (hμ : Continuous μ) {D : T → Fam 2 L N}
    (hD : ∀ t, D t ∈ BSub (L := L) (N := N) j) (hDc : CF D) {K : T → Act 2 L N}
    (hK : ∀ t, K t ∈ ASub (L := L) (N := N) j) (hKc : CA K) :
    LastCont (fun t => LastN.rawStepN (R.withMsq (ms t)) j (f t) (g t) (μ t) (D t) (K t)) := by
  have hρ1 : R.ρ < 1 := by linarith
  have hZ0 : ∀ t, (f t).Z ≠ 0 := fun t => (hI t).Z_ne_zero hρ1
  -- scalar pieces
  have hζ : Continuous fun t => cζ R (f t) :=
    (continuous_clampDisk hρ).comp ((hf.z.add hf.y).div hf.Z hZ0)
  have hζb : ∀ t, ‖cζ R (f t)‖ ≤ R.ρ := fun t => absorb_le R hρ _ _
  have hζ' : ∀ i, Continuous fun t => cζ' R j (f t) i := fun i => by
    by_cases hi : i = j
    · subst hi; simp only [cζ', Function.update_self]; exact hζ
    · simp only [cζ', Function.update_of_ne hi]; exact hf.ζ i
  have hC : ∀ x y, Continuous fun t => LastN.stCovN (R.withMsq (ms t)) j (f t) x y := fun x y =>
    lastCov_contM R.P hcov R rfl hj hms hms0 hms1 hζ' (fun t i => RawInv.zeta'_le hρ (hI t) i)
      (fun t i hi => by
        simp only [cζ', Function.update_of_ne (show i ≠ j by omega)]
        exact (hI t).hζ0 i hi.le) x y
  have hZ1 : Continuous fun t => cZ1 R (f t) := hf.Z.mul (continuous_const.add hζ)
  have hA : Continuous fun t => cA R (f t) := hf.Z.mul hζ
  have hYc : Continuous fun t => cYc R (f t) :=
    hf.Z.mul ((continuous_clampDisk hρ).comp (hf.y.div hf.Z hZ0))
  have hNu : Continuous fun t => cNu R j (f t) (μ t) :=
    ((Complex.continuous_ofReal.comp hμ).mul hZ1).div_const _
  have hGr : Continuous fun t => cGr R j (f t) (g t) (μ t) :=
    ((Complex.continuous_ofReal.comp hg).div (continuous_const.add
      ((continuous_clampDisk (by norm_num)).comp ((continuous_const.mul hNu).mul hf.w1)))
      fun t => one_add_nCor_ne' _ _).mul (hZ1.pow 2)
  have hmsC : Continuous fun t => ((ms t : ℝ) : ℂ) := Complex.continuous_ofReal.comp hms
  have hvΔ : Continuous fun t => cvΔ (R.withMsq (ms t)) (f t) :=
    continuous_fin4 (hA.sub hYc) hYc (hA.mul hmsC) continuous_const
  have hvV : Continuous fun t => cvV (R.withMsq (ms t)) j (f t) (g t) (μ t) :=
    continuous_fin4 ((hf.z.add hYc).sub hA) (hf.y.sub hYc) (hNu.sub (hA.mul hmsC)) hGr
  -- the parameter map, with `r = 1` and the inputs `(D, K)`
  have hx1 : Continuous fun t => BSp.mk' (ℓ := R.ℓ) (D t) (hD t) :=
    (BSp.continuous_iff _).2 (by simpa only [BSp.toFam_mk'] using hDc)
  have hx2 : Continuous fun t => ASp.mkL (ℓ := R.ℓ) (A := R.A) (K t) (hK t) :=
    (ASp.continuous_iff _).2 hKc
  have hu := PE.continuous_mk (ℓ := R.ℓ) (A := R.A)
    (fun t => LastN.stCovN (R.withMsq (ms t)) j (f t)) hC hvV hvΔ (r := fun _ => (1 : ℂ))
    continuous_const (fun t => (hI t).hWl) hf.Wl hx1 hx2
  set u := fun t => (((LastN.stCovN (R.withMsq (ms t)) j (f t) : Lam 2 L N → Lam 2 L N → ℂ),
    cvV (R.withMsq (ms t)) j (f t) (g t) (μ t), cvΔ (R.withMsq (ms t)) (f t), (1 : ℂ),
    BSp.mk' (ℓ := R.ℓ) ((f t).Wl) ((hI t).hWl), BSp.mk' (ℓ := R.ℓ) (D t) (hD t),
    ASp.mkL (ℓ := R.ℓ) (A := R.A) (K t) (hK t)) : PE 2 L N j R.ℓ R.A) with hudef
  -- the identification of the inputs
  have eC : ∀ t, PE.C (u t) = LastN.stCovN (R.withMsq (ms t)) j (f t) := fun t => rfl
  have eV : ∀ t, PE.V (u t) = stVf (R.withMsq (ms t)) j (f t) (g t) (μ t) := fun t => rfl
  have eW : ∀ t, PE.Wl (u t) + PE.D (u t) = (f t).Wl + D t := fun t => by
    show (f t).Wl + sigF 1 (D t) = _
    rw [sigF_one]
  have eK : ∀ t, PE.K (u t) = Kflat j (stDelta (R.withMsq (ms t)) j (f t)) (K t) := fun t => by
    show Kflat j _ (sigK 1 (K t)) = _
    rw [sigK_one]
    rfl
  have hCe := PE.hC 2 L N j R.ℓ R.A
  have hVe := PE.hV 2 L N j R.ℓ R.A
  have hWe := PE.hW 2 L N j R.ℓ R.A
  have hKe := PE.hK 2 L N j R.ℓ R.A
  have hV0e := PE.hV0 2 L N j R.ℓ R.A
  -- the entries of the covariance used in the shift
  have hc00 := hC 0 0
  have hc10 := hC (dirVec (Sum.inl 0)) 0
  refine ⟨hZ1, ?_, ?_, ?_, (continuous_apply 3).comp hvV,
    ?_, fun b n z => ?_, fun b n z => ?_, fun n z => ?_⟩
  · exact ((continuous_apply 0).comp hvV).sub (((continuous_apply 3).comp hvV).mul hc00)
  · exact ((continuous_apply 1).comp hvV).sub (((continuous_apply 3).comp hvV).mul (hc10.sub hc00))
  · exact ((continuous_apply 2).comp hvV).add ((continuous_const.mul
      ((continuous_apply 3).comp hvV)).mul (hc10.sub hc00))
  · have h := (LastN.uXN_diffC j hCe hVe univ).continuous.comp hu
    exact h
  · have h := ((LastN.VpN_holC hCe hVe b) n z).continuous.comp hu
    exact h
  · have h := ((Sb_holC j hCe hVe hWe b) n z).continuous.comp hu
    refine h.congr fun t => ?_
    simp only [Function.comp_apply]
    show coeff ((Sb j (PE.C (u t)) (PE.V (u t)) (PE.Wl (u t) + PE.D (u t)) b : EvR _) : Alg 2 L N) z = _
    rw [eW t]
    rfl
  · have h := ((LastN.KN_holC j hCe hVe hWe hKe hV0e univ) n z).continuous.comp hu
    refine h.congr fun t => ?_
    simp only [Function.comp_apply]
    show coeff ((LastN.KN j (PE.C (u t)) (PE.V (u t)) (PE.Wl (u t) + PE.D (u t)) (PE.K (u t)) univ :
      EvR _) : Alg 2 L N) z = _
    rw [eW t, eK t]
    rfl

end Step

end

end Step2
