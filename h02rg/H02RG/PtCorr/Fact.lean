import PtCorr.FactGen
import Obs.FlowObs

/-!
# Factorisation of `K_{j+1}` along the observable flow (both Cases, no `Near` hypothesis)

`Obs.KnextO_eq_KextG` needs `ObsLocSep`, i.e. the scale-`j` locality of the split evaluations
of `V^obs_j` *and* `V^obs_{j+1}`.  Along `Obs.flowO` started at `initObs c l₀`, in Case (2)
`η_k = 0` for `k ≤ j_ab` and `a, b` are close at scale `j` for `j > j_ab`, but at the step
`j = j_ab` the new `η_{j+1}` need not vanish while `a, b` need not be close at scale `j`.

We use instead the relaxed support hypotheses `PtCorr.SuppHyp'`: `e^{-(u+V)_{j+1}(B)}` enters
`K_{j+1}` only through `ι`, and `𝔼_C` factorises on the subalgebras
`S2' U = ι(OE) ⊔ Supp2 U` (`E_mul_sup`, `sep_S2'`: the `ψ`-dependence is a spectator).  Only the
locality of `V^obs_j` (`η_j = 0` or `a, b` close at scale `j`) is needed, which holds along the
flow (`etaSep_flowO`).  Result: `flowO_fact`,
`K_{j+1}(U) = ∏_{Y ∈ Comp(U)} K_{j+1}(Y)` for all `(j+1)`-polymers and all steps `j < N`.

Along the way: `inKO_flowO`, the componentwise locality `InKO c True` of all activities of the
flow (as in the induction of `Obs.flowObs`, but without the norm bounds).
-/

namespace PtCorr

noncomputable section

open Finset Grassmann Loc Step Obs Obs.Gen

variable {d L N : ℕ} [NeZero L] {c : Case}

/-! ### `𝔼_C` factorises on `ι(OE) ⊔ T` if it factorises on `T` -/

section Sup

variable {R R2 : Type*} [CommRing R] [CommRing R2] [Algebra ℂ R] [Algebra ℂ R2]

/-- If `E(ι x g) = x E(g)` and `E` factorises on `T₁ × T₂`, then it factorises on
`(ι(R) ⊔ T₁) × (ι(R) ⊔ T₂)`. -/
theorem E_mul_sup (ι : R →ₐ[ℂ] R2) (E : R2 →ₗ[ℂ] R) (hE : ∀ x g, E (ι x * g) = x * E g)
    {T₁ T₂ : Subalgebra ℂ R2} (hT : ∀ u ∈ T₁, ∀ v ∈ T₂, E (u * v) = E u * E v)
    {f g : R2} (hf : f ∈ ι.range ⊔ T₁) (hg : g ∈ ι.range ⊔ T₂) : E (f * g) = E f * E g := by
  have key : ∀ x y : R, ∀ u ∈ T₁, ∀ v ∈ T₂, E (ι x * u * (ι y * v)) = E (ι x * u) * E (ι y * v) := by
    intro x y u hu v hv
    rw [mul_mul_mul_comm, ← map_mul ι x y, hE, hE, hE, hT u hu v hv, mul_mul_mul_comm]
  have hf' : f ∈ Subalgebra.toSubmodule ι.range * Subalgebra.toSubmodule T₁ := by
    rw [Subalgebra.mul_toSubmodule]; exact hf
  have hg' : g ∈ Subalgebra.toSubmodule ι.range * Subalgebra.toSubmodule T₂ := by
    rw [Subalgebra.mul_toSubmodule]; exact hg
  refine Submodule.mul_induction_on (C := fun f => E (f * g) = E f * E g) hf' ?_ ?_
  · intro m hm u hu
    obtain ⟨x, rfl⟩ := hm
    refine Submodule.mul_induction_on (C := fun g => E (ι x * u * g) = E (ι x * u) * E g) hg' ?_ ?_
    · intro m' hm' v hv
      obtain ⟨y, rfl⟩ := hm'
      exact key x y u hu v hv
    · intro g₁ g₂ h₁ h₂
      rw [mul_add, E.map_add, E.map_add, h₁, h₂, mul_add]
  · intro f₁ f₂ h₁ h₂
    rw [add_mul, E.map_add, E.map_add, h₁, h₂, add_mul]

end Sup

/-! ### The relaxed supports for the observable map -/

variable (c) in
/-- The factorising supports on the doubled algebra: `ι(OE) ⊔ 𝒩^obs(U^□)` (componentwise
locality, `P = True`). -/
def S2' (a b : Lam d L N) (j : ℕ) (U : Finset (Lam d L N)) :
    Subalgebra ℂ (OE c (Lam d L N ⊕ Lam d L N)) :=
  (inclO : OE c (Lam d L N) →ₐ[ℂ] OE c (Lam d L N ⊕ Lam d L N)).range ⊔ Supp2 c True a b j U

section Hyp

variable {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℝ} {Vb : Vcoup} {Vo : Coup c}
  {K : Finset (Lam d L N) → OE c (Lam d L N)} {a b : Lam d L N}

/-- The relaxed support hypotheses hold as soon as `K_j` is (componentwise) local and the split
evaluation of `V^obs_j` is local at scale `j`; no condition on `V^obs_{j+1}`, `u^obs_{j+1}`. -/
theorem suppHyp'_obs (hd : 1 ≤ d) (hK : InKO c True a b j K)
    (hV : CoupLocSep c True a b j (Coup.toV c Vo)) :
    SuppHyp' (obsA c C) j (obsI j C Vb Vo K a b) (Supp c True a b j) (S2' c a b j) where
  hθ _ _ hf := Algebra.mem_sup_right (thetaO_mem_Supp2 hf)
  hι _ f := Algebra.mem_sup_left (AlgHom.mem_range_self _ f)
  hK _ Y hY hYU := Supp_mono hYU (hK Y hY)
  hJ _ _ Y hb hYU := JO_mem_Supp hd (fun h => absurd trivial h) (hb.trans hYU) Y
  hI0 _ p hb := Supp_mono hb (oexp_mem _ (neg_mem (VfullX_mem_Supp hd Vb Vo hV p))
    (isNilpotent_VfullX a b _ _ _).neg)

/-- `𝔼_C` factorises on `Supp2 U₁ × Supp2 U₂` for non-touching `(j+1)`-polymers. -/
theorem sep_Supp2 (hL : 2 ^ (d + 2) ≤ L) (hj : j + 1 ≤ N) {ℓ₀ : ℝ} (hC : GoodCov j ℓ₀ C)
    {U₁ U₂ : Finset (Lam d L N)} (hU₁ : IsPolymer (j + 1) U₁) (hU₂ : IsPolymer (j + 1) U₂)
    (hT : ¬ Touch U₁ U₂) :
    ∀ u ∈ Supp2 c True a b j U₁, ∀ v ∈ Supp2 c True a b j U₂,
      ECO C (u * v) = ECO C u * ECO C v := fun _ hu _ hv =>
  ECO_mul_of_sep (fun _ hx _ hy => C_eq_zero_of_nbhd hL hj hC hU₁ hU₂ hT hx hy)
    (Algebra.mem_inf.1 hu).1 (Algebra.mem_inf.1 hv).1

set_option maxHeartbeats 2000000 in
/-- `𝔼_C` factorises on `S2' U₁ × S2' U₂` for non-touching `(j+1)`-polymers. -/
theorem sep_S2' (hL : 2 ^ (d + 2) ≤ L) (hj : j + 1 ≤ N) {ℓ₀ : ℝ} (hC : GoodCov j ℓ₀ C)
    {U₁ U₂ : Finset (Lam d L N)} (hU₁ : IsPolymer (j + 1) U₁) (hU₂ : IsPolymer (j + 1) U₂)
    (hT : ¬ Touch U₁ U₂) :
    ∀ f ∈ S2' c a b j U₁, ∀ g ∈ S2' c a b j U₂, ECO C (f * g) = ECO C f * ECO C g :=
  fun _ hf _ hg => E_mul_sup inclO (ECO C) (ECO_inclO_mul C)
    (sep_Supp2 (a := a) (b := b) hL hj hC hU₁ hU₂ hT) hf hg

/-- **Factorisation** `K_{j+1}(U) = ∏_{Y ∈ Comp(U)} K_{j+1}(Y)` under the scale-`j` locality of
`K_j` and `V^obs_j` only. -/
theorem KnextO_eq_KextG' (hd : 1 ≤ d) (hL : 2 ^ (d + 2) ≤ L) (hj : j + 1 ≤ N) {ℓ₀ : ℝ}
    (hC : GoodCov j ℓ₀ C) (hK : InKO c True a b j K)
    (hV : CoupLocSep c True a b j (Coup.toV c Vo)) {U : Finset (Lam d L N)}
    (hU : IsPolymer (j + 1) U) :
    KnextO j C Vb Vo K a b U = KextG (j + 1) (KnextO j C Vb Vo K a b) U :=
  KnextG_eq_KextG' (A := obsA c C) (F := obsI j C Vb Vo K a b) hd hL hj
    (suppHyp'_obs (Vb := Vb) (C := C) hd hK hV) (obsA_hE1 C)
    (fun _ _ hU₁ hU₂ hT => sep_S2' hL hj hC hU₁ hU₂ hT) hU

end Hyp

/-! ### Along the flow -/

section Flow

variable {msq ℓ₀ : ℝ} (V₀ : Vcoup) (l₀ : ℂ) (a b : Lam d L N)

theorem supNorm_le_pow_nat (x : Lam d L N) : supNorm x ≤ L ^ N := by
  refine Finset.sup_le fun i _ => ?_
  exact (FRD.zabs_le_val _).trans (ZMod.val_lt _).le

/-- `a, b` are close at scale `j` once `j > j_ab`. -/
theorem near_of_coal_lt (hd : 1 ≤ d) (hL : 2 ≤ L) {j : ℕ} (hj : j ≤ N) {a b : Lam d L N}
    (hc : coal L a b < j) : Near j a b := by
  have h1 : 2 * supNorm (a - b) < L ^ (coal L a b + 1) := by
    unfold coal; exact Nat.lt_pow_succ_log_self (by omega) _
  have h2 : L ^ (coal L a b + 1) ≤ L ^ j := Nat.pow_le_pow_right (by omega) (by omega)
  have hab : supNorm (a - b) ≤ L ^ j := by omega
  have hba : supNorm (b - a) ≤ L ^ j := by rw [FRD.supNorm_sub_comm]; exact hab
  have h0 : ∀ x : Lam d L N, supNorm (x - x) ≤ L ^ j := fun x => by simp [supNorm_zero]
  intro p hp
  rcases hp with ha | hb
  · exact ⟨mem_nbhd_of_le hd hj ha (h0 a), mem_nbhd_of_le hd hj ha hba⟩
  · exact ⟨mem_nbhd_of_le hd hj hb hab, mem_nbhd_of_le hd hj hb (h0 b)⟩

variable {V₀ l₀ a b}

/-- The `η` condition for `V^obs_{j+1}` at scale `j + 1` (no hypothesis on `j_ab`). -/
theorem eta_cond_succ' (hd1 : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L)
    (hC : ∀ k < N, GoodCov k ℓ₀ (Flow.covAt d L N msq k)) {j : ℕ} (hj : j < N) :
    etaOf c (flowO d L c N msq V₀ (initObs c l₀) a b (j + 1)).1 = 0 ∨ NearS j a b := by
  have h2 : 2 ≤ 2 ^ (d + 3) := Nat.le_self_pow (by omega) 2
  cases c
  · exact Or.inl rfl
  · by_cases h : coal L a b ≤ j
    · exact Or.inr (nearS_of_coal_le hd1 (by omega) (by omega) h)
    · by_cases hN : j + 1 ≤ N - 1
      · exact Or.inl (flowO_ab (c := .two) V₀ l₀ a b hd1 hL hC (j + 1) (by omega)).1.1
      · refine Or.inr (nearS_of_le hd1 (by omega) ?_)
        have : j + 1 = N := by omega
        rw [this]; exact supNorm_le_pow_nat _

/-- **Componentwise locality of the activities along the flow**: `K_j ∈ 𝒩^obs(X^□)` for all
connected `X` and `j ≤ N`. -/
theorem inKO_flowO (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L)
    (hC : ∀ k < N, GoodCov k ℓ₀ (Flow.covAt d L N msq k)) :
    ∀ j ≤ N, InKO c True a b j (flowO d L c N msq V₀ (initObs c l₀) a b j).2
  | 0, _ => fun _ _ => zero_mem _
  | j + 1, hj => by
    have ih := inKO_flowO hd hL hC j (by omega)
    rw [flowO_succ]
    refine InKO_restrO (InKO_KnextO hd ?_)
    refine ⟨ih, fun h => absurd trivial h, ⟨?_, Or.inl trivial⟩, ⟨?_, Or.inl trivial⟩,
      ⟨Or.inl (etaOf_toU c _), Or.inl trivial⟩⟩
    · rw [etaOf_toV]; exact eta_cond V₀ l₀ a b hd hL hC (by omega)
    · have := eta_cond_succ' (c := c) (V₀ := V₀) (l₀ := l₀) (a := a) (b := b) hd hL hC
        (j := j) (by omega)
      rw [flowO_succ] at this
      rwa [etaOf_toV] at this ⊢

/-- The scale-`j` `η` condition for `V^obs_j` along the flow. -/
theorem etaSep_flowO (hd1 : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L)
    (hC : ∀ k < N, GoodCov k ℓ₀ (Flow.covAt d L N msq k)) {j : ℕ} (hj : j < N) :
    CoupLocSep c True a b j (Coup.toV c (flowO d L c N msq V₀ (initObs c l₀) a b j).1) := by
  have h2 : 2 ≤ 2 ^ (d + 3) := Nat.le_self_pow (by omega) 2
  refine ⟨?_, Or.inl trivial⟩
  rw [etaOf_toV]
  cases c
  · exact Or.inl rfl
  · by_cases h : coal L a b < j
    · exact Or.inr (near_of_coal_lt hd1 (by omega) (by omega) h)
    · exact Or.inl (flowO_ab (c := .two) V₀ l₀ a b hd1 hL hC j (by omega)).1.1

/-- **Factorisation along the observable flow** (both Cases): for every step `j < N` and every
`(j+1)`-polymer `U`, `K_{j+1}(U) = ∏_{Y ∈ Comp(U)} K_{j+1}(Y)`. -/
theorem flowO_fact (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L)
    (hC : ∀ k < N, GoodCov k ℓ₀ (Flow.covAt d L N msq k)) {j : ℕ} (hj : j < N)
    {U : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U) :
    KnextO j (Flow.covAt d L N msq j) (Flow.flowN d L N msq V₀ j).1
        (flowO d L c N msq V₀ (initObs c l₀) a b j).1 (flowO d L c N msq V₀ (initObs c l₀) a b j).2
        a b U =
      KextG (j + 1) (KnextO j (Flow.covAt d L N msq j) (Flow.flowN d L N msq V₀ j).1
        (flowO d L c N msq V₀ (initObs c l₀) a b j).1 (flowO d L c N msq V₀ (initObs c l₀) a b j).2
        a b) U := by
  have hL2 : 2 ^ (d + 2) ≤ L := le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hL
  exact KnextO_eq_KextG' hd hL2 (by omega) (hC j hj) (inKO_flowO hd hL hC j hj.le)
    (etaSep_flowO hd hL hC hj) hU

end Flow

end

end PtCorr
