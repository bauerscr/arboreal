import Flow.RGTorus

/-!
# The renormalisation group flow as a dynamical system (`e:flowblock`)

The infinite volume activities at scale `j` are realised as compatible families of torus
activities `K_j = (K_j^N)_{N ≥ j + 3}` (`Flow.KFam d L j 3 ℓ_j A`).  With the rescaled coordinates
`v_j = (ẑ_j, ŷ_j, â_j)` and `w_j = (b̂_j, K_j)`, the renormalisation group map becomes the
dynamical system `e:flowblock` (`Flow.RGsys`):

* `E v = (ẑ, ŷ, L² â)`;
* `B_j (b̂, K)`: the `κ̂`-terms (from `𝔼 θ V`) and the `Loc`-terms `r̂(K)`, read off on the torus
  `Λ_{j+3}` (they do not depend on the torus, `BNf_compat`);
* `D_j (b̂, K) = (L^{-(d-2)} b̂, D K_{j+1}|_0 (0, K))` (the `b̂`-component is exactly
  `b̂_{j+1} = L^{-(d-2)} b̂_j`, since `Loc` produces no quartic terms);
* `g_j (v, w) = (0, K_{j+1}(v, w) - D_j K)`.

We verify the hypotheses of the abstract stable manifold theorem (`RGsys_bounds`), the
analyticity of the `g_j` along complex curves (`RGsys_analytic`), and the continuity in the
mass parameter through the torus projections (`RGsys_cont_*`).
-/

namespace Flow

noncomputable section

open Finset Grassmann Loc FRD Step Metric Filter Topology Coup

variable {d L : ℕ} [NeZero L] {ℓ₀ A ε C₁ δK Kc Cw : ℝ} [Fact (0 < ℓ₀)] [Fact (0 < A)]

variable (d L ℓ₀ A) in
/-- The space `W_j = ℂ × 𝒦_j(ℤ^d)` of `w_j = (b̂_j, K_j)`. -/
abbrev WS (j : ℕ) := ℂ × KFam d L j 3 (ellj d (L : ℝ) ℓ₀ j) A

/-- A torus at scale `j + 1` as a torus at scale `j`. -/
def Idx.low {j : ℕ} (N : Idx (j + 1) 3) : Idx j 3 := ⟨N.1, by have := N.2; omega⟩

@[simp] theorem Idx.low_val {j : ℕ} (N : Idx (j + 1) 3) : N.low.1 = N.1 := rfl

/-- The torus component `x_N = (v, b̂, K^N)` of `x = (v, b̂, K)`. -/
def xN {j : ℕ} (N : Idx j 3) (x : Vsp × WS d L ℓ₀ A j) : XS d L j N.1 ℓ₀ A :=
  (x.1, x.2.1, KFam.proj N x.2.2)

theorem norm_xN_le {j : ℕ} (N : Idx j 3) (x : Vsp × WS d L ℓ₀ A j) : ‖xN N x‖ ≤ ‖x‖ := by
  unfold xN
  simp only [Prod.norm_def]
  exact max_le_max le_rfl (max_le_max le_rfl (KFam.norm_proj_le _ _))

/-- The projection of a family at scale `j` to a torus `N ≥ j + 4`. -/
def projL {j : ℕ} (N : Idx (j + 1) 3) :
    KFam d L j 3 (ellj d (L : ℝ) ℓ₀ j) A →L[ℂ] KS d L j N.1 ℓ₀ A := KFam.proj N.low

/-- `xN` for a torus `N ≥ j + 4`. -/
def xNs {j : ℕ} (N : Idx (j + 1) 3) (x : Vsp × WS d L ℓ₀ A j) : XS d L j N.1 ℓ₀ A :=
  (x.1, x.2.1, projL N x.2.2)

theorem norm_xNs_le {j : ℕ} (N : Idx (j + 1) 3) (x : Vsp × WS d L ℓ₀ A j) : ‖xNs N x‖ ≤ ‖x‖ :=
  norm_xN_le N.low x

theorem xNs_sub {j : ℕ} (N : Idx (j + 1) 3) (x y : Vsp × WS d L ℓ₀ A j) :
    xNs N (x - y) = xNs N x - xNs N y := by
  simp [xNs]

section
variable (H : Hyp d L A ℓ₀ ε C₁ δK Kc Cw)
include H

theorem FN_lip' {j N : ℕ} (hj : j + 1 < N) (m : ℝ) {x : XS d L j N ℓ₀ A}
    (hx : ‖x‖ ≤ rad d ℓ₀ ε) : ‖FN ℓ₀ A m j N x‖ ≤ C₁ * cX d ℓ₀ * ‖x‖ := by
  have h := FN_lip H hj m hx (x' := 0) (by rw [norm_zero]; exact (rad_pos H).le)
  rwa [FN_zero H hj, sub_zero, sub_zero] at h

open Classical in
/-- `K_{j+1}` as a family over the tori `N ≥ j + 4` (defined as `0` if the family is not
bounded; on the ball of radius `r` it is bounded, `FF_bdd`). -/
def FF (m : ℝ) (j : ℕ) (x : Vsp × WS d L ℓ₀ A j) : KFam d L (j + 1) 3 (ellj d (L : ℝ) ℓ₀ (j + 1)) A :=
  if hb : BddAbove (Set.range fun N : Idx (j + 1) 3 =>
      (Knorm (j + 1) (ellj d L ℓ₀ (j + 1)) A (FN ℓ₀ A m j N.1 (xNs N x)).toAct).toReal) then
    KFam.mk (fun N => (FN ℓ₀ A m j N.1 (xNs N x)).toAct) (fun N => KSp.toAct_mem _)
      (fun N M hNM => FN_compat H (by have := N.2; omega) hNM m _ _ _ _
        (KFam.compat x.2.2 (N := N.low) (M := M.low) hNM)) hb
  else 0

theorem FF_bdd {j : ℕ} (m : ℝ) {x : Vsp × WS d L ℓ₀ A j} (hx : ‖x‖ ≤ rad d ℓ₀ ε) :
    BddAbove (Set.range fun N : Idx (j + 1) 3 =>
      (Knorm (j + 1) (ellj d L ℓ₀ (j + 1)) A (FN ℓ₀ A m j N.1 (xNs N x)).toAct).toReal) := by
  refine ⟨C₁ * cX d ℓ₀ * ‖x‖, ?_⟩
  rintro _ ⟨N, rfl⟩
  dsimp only
  rw [← KSp.norm_def]
  have hN := N.2
  have h1 := norm_xNs_le N x
  refine (FN_lip' H (by omega) m (h1.trans hx)).trans ?_
  have := cX_pos d ℓ₀; have := H.hC₁
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

theorem proj_FF {j : ℕ} (m : ℝ) {x : Vsp × WS d L ℓ₀ A j} (hx : ‖x‖ ≤ rad d ℓ₀ ε)
    (N : Idx (j + 1) 3) : KFam.proj N (FF H m j x) = FN ℓ₀ A m j N.1 (xNs N x) := by
  refine KSp.toAct_injective ?_
  rw [FF, dif_pos (FF_bdd H m hx)]
  rfl

theorem norm_FF_le {j : ℕ} (m : ℝ) {x : Vsp × WS d L ℓ₀ A j} (hx : ‖x‖ ≤ rad d ℓ₀ ε) :
    ‖FF H m j x‖ ≤ C₁ * cX d ℓ₀ * ‖x‖ := by
  have := cX_pos d ℓ₀; have := H.hC₁
  refine KFam.norm_le (by positivity) fun N => ?_
  rw [KFam.act_def, ← KSp.norm_def, proj_FF H m hx]
  have hN := N.2
  have h1 := norm_xNs_le N x
  exact (FN_lip' H (by omega) m (h1.trans hx)).trans
    (mul_le_mul_of_nonneg_left h1 (by positivity))

/-- The linearisation `D K_{j+1}|_0 (0, ·)` on families. -/
def DFf (m : ℝ) (j : ℕ) (K : KFam d L j 3 (ellj d (L : ℝ) ℓ₀ j) A) :
    KFam d L (j + 1) 3 (ellj d (L : ℝ) ℓ₀ (j + 1)) A :=
  KFam.mk (fun N => (DN ℓ₀ A m j N.1 (projL N K)).toAct) (fun N => KSp.toAct_mem _)
    (fun N M hNM => DN_compat H (by have := N.2; omega) hNM m _ _
      (KFam.compat K (N := N.low) (M := M.low) hNM))
    ⟨δK * ‖K‖, by
      rintro _ ⟨N, rfl⟩
      dsimp only
      rw [← KSp.norm_def]
      have hN := N.2
      exact (DN_norm_le H (by omega) m _).trans
        (mul_le_mul_of_nonneg_left (KFam.norm_proj_le _ _) H.hδK)⟩

theorem proj_DFf {j : ℕ} (m : ℝ) (K : KFam d L j 3 (ellj d (L : ℝ) ℓ₀ j) A)
    (N : Idx (j + 1) 3) : KFam.proj N (DFf H m j K) = DN ℓ₀ A m j N.1 (projL N K) :=
  KSp.toAct_injective rfl

/-- `D K_{j+1}|_0 (0, ·)` on families, as a continuous linear map. -/
def DF (m : ℝ) (j : ℕ) :
    KFam d L j 3 (ellj d (L : ℝ) ℓ₀ j) A →L[ℂ] KFam d L (j + 1) 3 (ellj d (L : ℝ) ℓ₀ (j + 1)) A :=
  LinearMap.mkContinuous
    { toFun := DFf H m j
      map_add' := fun K K' => KFam.ext fun N => by
        have hN := N.2
        simp only [KFam.act_def, proj_DFf]
        rw [show projL N (K + K') = (1 : ℂ) • projL N K + (1 : ℂ) • projL N K' by simp,
          DN_add_smul H (by omega) m, _root_.map_add, _root_.map_smul, _root_.map_smul,
          one_smul, one_smul]
        rfl
      map_smul' := fun c K => KFam.ext fun N => by
        have hN := N.2
        simp only [KFam.act_def, proj_DFf, RingHom.id_apply]
        rw [show projL N (c • K) = c • projL N K + (0 : ℂ) • (0 : KS d L j N.1 ℓ₀ A) by simp,
          DN_add_smul H (by omega) m, _root_.map_add, _root_.map_smul, _root_.map_smul,
          zero_smul, add_zero]
        rfl } δK
    (fun K => KFam.norm_le (by have := H.hδK; positivity) fun N => by
      rw [KFam.act_def, ← KSp.norm_def]
      show ‖KFam.proj N (DFf H m j K)‖ ≤ _
      rw [proj_DFf]
      have hN := N.2
      exact (DN_norm_le H (by omega) m _).trans
        (mul_le_mul_of_nonneg_left (KFam.norm_proj_le _ _) H.hδK))

theorem DF_apply (m : ℝ) (j : ℕ) (K : KFam d L j 3 (ellj d (L : ℝ) ℓ₀ j) A) :
    DF H m j K = DFf H m j K := rfl

theorem norm_DF_le (m : ℝ) (j : ℕ) : ‖DF H m j‖ ≤ δK :=
  LinearMap.mkContinuous_norm_le _ H.hδK _

/-- `B_j` on families (read off on the torus `Λ_{j+3}`). -/
def Bfam (m : ℝ) (j : ℕ) : WS d L ℓ₀ A j →L[ℂ] Vsp :=
  (LinearMap.toContinuousLinearMap (BNL (d := d) (L := L) ℓ₀ A H (by omega : j < j + 3) m)).comp
    ((ContinuousLinearMap.id ℂ ℂ).prodMap
      (KFam.proj (d := d) (L := L) (ℓ := ellj d L ℓ₀ j) (A := A) (⟨j + 3, le_rfl⟩ : Idx j 3)))

theorem Bfam_apply (m : ℝ) (j : ℕ) (w : WS d L ℓ₀ A j) :
    Bfam H m j w = BNf ℓ₀ A m j (j + 3) (w.1, KFam.proj ⟨j + 3, le_rfl⟩ w.2) := rfl

/-- `L^{-(d-2)}`. -/
def bfac (d L : ℕ) : ℂ := ((L : ℂ) ^ (d - 2))⁻¹

/-- `D_j (b̂, K) = (L^{-(d-2)} b̂, D K_{j+1}|_0 (0, K))`. -/
def Dfam (m : ℝ) (j : ℕ) : WS d L ℓ₀ A j →L[ℂ] WS d L ℓ₀ A (j + 1) :=
  (bfac d L • ContinuousLinearMap.id ℂ ℂ).prodMap (DF H m j)

theorem Dfam_apply (m : ℝ) (j : ℕ) (w : WS d L ℓ₀ A j) :
    Dfam H m j w = (bfac d L * w.1, DF H m j w.2) := rfl

/-- The nonlinear part `g_j`. -/
def gfam (m : ℝ) (j : ℕ) (x : Vsp × WS d L ℓ₀ A j) : WS d L ℓ₀ A (j + 1) :=
  (0, FF H m j x - DF H m j x.2.2)

end

variable (L) in
/-- The inverse of `E`. -/
def EmapInv : Vsp →ₗ[ℂ] Vsp where
  toFun v := (v.1, v.2.1, ((L : ℂ) ^ 2)⁻¹ * v.2.2)
  map_add' v w := by simp [mul_add]
  map_smul' c v := by simp; ring

variable (L) in
/-- `E` as a continuous linear equivalence. -/
def Eequiv : Vsp ≃L[ℂ] Vsp :=
  LinearEquiv.toContinuousLinearEquiv (LinearEquiv.ofLinear (Emap L) (EmapInv L)
    (by
      have hL : ((L : ℂ) ^ 2) ≠ 0 := pow_ne_zero _ (by exact_mod_cast NeZero.ne L)
      ext <;> simp [EmapInv, hL])
    (by
      have hL : ((L : ℂ) ^ 2) ≠ 0 := pow_ne_zero _ (by exact_mod_cast NeZero.ne L)
      ext <;> simp [EmapInv, hL]))

theorem Eequiv_apply (v : Vsp) : Eequiv L v = Emap L v := rfl

theorem Eequiv_symm_apply (v : Vsp) : (Eequiv L).symm v = EmapInv L v := rfl

theorem norm_Eequiv_symm_le : ‖((Eequiv L).symm : Vsp →L[ℂ] Vsp)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  rw [one_mul, ContinuousLinearEquiv.coe_coe, Eequiv_symm_apply]
  simp only [EmapInv, LinearMap.coe_mk, AddHom.coe_mk, Prod.norm_def, norm_mul, norm_inv,
    norm_Lpow]
  refine max_le_max le_rfl (max_le_max le_rfl ?_)
  have hL1 : (1 : ℝ) ≤ (L : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast NeZero.one_le)
  exact mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ hL1)

/-- The observables: `w = (b̂, K) ↦ (b̂, K^N)`. -/
def obs (j : ℕ) (N : Idx j 3) : WS d L ℓ₀ A j →L[ℂ] ℂ × KS d L j N.1 ℓ₀ A :=
  (ContinuousLinearMap.id ℂ ℂ).prodMap (KFam.proj N)

theorem obs_apply (j : ℕ) (N : Idx j 3) (w : WS d L ℓ₀ A j) :
    obs j N w = (w.1, KFam.proj N w.2) := rfl

section
variable (H : Hyp d L A ℓ₀ ε C₁ δK Kc Cw)
include H

/-- **The dynamical system `e:flowblock`** of the renormalisation group flow, for the mass
parameter `m² = max m 0`. -/
def RGsys (m : ℝ) : System Vsp (WS d L ℓ₀ A) where
  E := Eequiv L
  B := Bfam H m
  D := Dfam H m
  g := gfam H m

theorem RGsys_E (m : ℝ) : (RGsys H m).E = Eequiv L := rfl

/-- The contraction rate `δ = max(L^{-(d-2)}, δ_K)` of `D_j`. -/
def δD (d L : ℕ) (δK : ℝ) : ℝ := max (((L : ℝ) ^ (d - 2))⁻¹) δK

theorem FF_zero (m : ℝ) (j : ℕ) : FF H m j 0 = 0 := by
  refine KFam.ext fun N => ?_
  rw [KFam.act_def, KFam.act_def, proj_FF H m (by rw [norm_zero]; exact (rad_pos H).le)]
  have hN := N.2
  have : xNs N (0 : Vsp × WS d L ℓ₀ A j) = 0 := by simp [xNs]
  rw [this, FN_zero H (by omega)]
  simp

theorem RGsys_bounds (m : ℝ) :
    (RGsys H m).Bounds (βB d L ℓ₀ Kc Cw) (δD d L δK) (C₁ * cX d ℓ₀ ^ 2) (rad d ℓ₀ ε) where
  norm_Einv_le := norm_Eequiv_symm_le
  norm_B_le j := by
    have hβ : 0 ≤ βB d L ℓ₀ Kc Cw := by
      have := H.hKc; have := H.hCw; unfold βB; positivity
    refine ContinuousLinearMap.opNorm_le_bound _ hβ fun w => ?_
    show ‖Bfam H m j w‖ ≤ _
    rw [Bfam_apply]
    refine (BNf_norm_le H (by omega) m _).trans (mul_le_mul_of_nonneg_left ?_ hβ)
    simp only [Prod.norm_def]
    exact max_le_max le_rfl (KFam.norm_proj_le _ _)
  norm_D_le j := by
    have hδ : 0 ≤ δD d L δK := le_trans H.hδK (le_max_right _ _)
    refine ContinuousLinearMap.opNorm_le_bound _ hδ fun w => ?_
    show ‖Dfam H m j w‖ ≤ _
    rw [Dfam_apply, Prod.norm_def, Prod.norm_def, mul_max_of_nonneg _ _ hδ]
    refine max_le_max ?_ (((DF H m j).le_of_opNorm_le (norm_DF_le H m j) w.2).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)))
    rw [norm_mul, bfac, norm_inv, norm_Lpow]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  g_zero j := by
    show gfam H m j 0 = 0
    simp only [gfam, FF_zero, Prod.snd_zero, _root_.map_zero, sub_zero, Prod.mk_zero_zero]
  g_lipschitz j x y hx hy := by
    show ‖gfam H m j x - gfam H m j y‖ ≤ _
    have hγ : 0 ≤ C₁ * cX d ℓ₀ ^ 2 * max ‖x‖ ‖y‖ * ‖x - y‖ := by
      have := H.hC₁; positivity
    have eg : gfam H m j x - gfam H m j y =
        (0, FF H m j x - FF H m j y - DF H m j (x.2.2 - y.2.2)) := by
      simp only [gfam, Prod.mk_sub_mk, sub_zero, _root_.map_sub]
      congr 1; abel
    rw [eg, Prod.norm_def, norm_zero]
    refine max_le hγ ?_
    refine KFam.norm_le hγ fun N => ?_
    rw [KFam.act_def, ← KSp.norm_def]
    have hN := N.2
    have e : KFam.proj N (DF H m j (x.2.2 - y.2.2)) =
        DN ℓ₀ A m j N.1 ((xNs N x).2.2 - (xNs N y).2.2) := by
      rw [DF_apply, proj_DFf]; rfl
    rw [_root_.map_sub, _root_.map_sub, proj_FF H m hx, proj_FF H m hy, e]
    refine (FN_rem H (by omega) m ((norm_xNs_le N x).trans hx) ((norm_xNs_le N y).trans hy)).trans
      ?_
    rw [← xNs_sub]
    have := H.hC₁
    have hc := (cX_pos d ℓ₀).le
    exact mul_le_mul (mul_le_mul_of_nonneg_left (max_le_max (norm_xNs_le N x) (norm_xNs_le N y))
      (by positivity)) (norm_xNs_le N (x - y)) (norm_nonneg _)
      (mul_nonneg (by positivity) (le_max_of_le_left (norm_nonneg _)))

/-- **Analyticity of `g_j` along complex curves** (from `Knext_hol`). -/
theorem RGsys_analytic (m : ℝ) (j : ℕ) :
    AnalyticAlongCurves ((RGsys H m).g j) (closedBall 0 (rad d ℓ₀ ε)) := by
  intro U c hU hc hcU
  have hball : ∀ t ∈ U, ‖c t‖ ≤ rad d ℓ₀ ε := fun t ht => mem_closedBall_zero_iff.1 (hcU ht)
  have hFF : DifferentiableOn ℂ (fun t => FF H m j (c t)) U := by
    refine KFam.differentiableOn_of_coeff hU ?_ ?_
    · intro t ht
      obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.1 hU t ht
      refine ⟨r, hr, C₁ * cX d ℓ₀ * rad d ℓ₀ ε, fun s hs => ?_⟩
      have := cX_pos d ℓ₀; have := H.hC₁
      exact (norm_FF_le H m (hball s (hsub hs))).trans
        (mul_le_mul_of_nonneg_left (hball s (hsub hs)) (by positivity))
    · intro N X n z
      have hN := N.2
      have hx : DifferentiableOn ℂ (fun t => xNs N (c t)) U :=
        hc.fst.prodMk (hc.snd.fst.prodMk ((projL N).differentiable.comp_differentiableOn hc.snd.snd))
      have hd := (KFam.coeffKSp X z).toContinuousLinearMap.differentiable.comp_differentiableOn
        (FN_differentiableOn H (by omega) m hx)
      refine hd.congr fun t ht => ?_
      simp only [Function.comp_apply, LinearMap.coe_toContinuousLinearMap', coeffKSp_apply']
      rw [KFam.act_def, proj_FF H m (hball t ht)]
  show DifferentiableOn ℂ (fun t => gfam H m j (c t)) U
  exact (differentiableOn_const 0).prodMk
    (hFF.sub ((DF H m j).differentiable.comp_differentiableOn hc.snd.snd))

/-- `B_j` on the torus as a continuous linear map. -/
def BNc {j N : ℕ} (hj : j < N) (m : ℝ) : (ℂ × KS d L j N ℓ₀ A) →L[ℂ] Vsp :=
  LinearMap.toContinuousLinearMap (BNL ℓ₀ A H hj m)

theorem norm_BNc_le {j N : ℕ} (hj : j + 1 < N) (m : ℝ) :
    ‖BNc H (by omega : j < N) m‖ ≤ βB d L ℓ₀ Kc Cw := by
  have hβ : 0 ≤ βB d L ℓ₀ Kc Cw := by
    have := H.hKc; have := H.hCw; unfold βB; positivity
  exact ContinuousLinearMap.opNorm_le_bound _ hβ fun p => BNf_norm_le H hj m p

/-- `D_j` on the torus as a continuous linear map. -/
def DNc {j N : ℕ} (hj : j + 1 < N) (m : ℝ) : KS d L j N ℓ₀ A →L[ℂ] KS d L (j + 1) N ℓ₀ A :=
  LinearMap.toContinuousLinearMap (DNL ℓ₀ A H hj m)

theorem norm_DNc_le {j N : ℕ} (hj : j + 1 < N) (m : ℝ) : ‖DNc H hj m‖ ≤ δK :=
  ContinuousLinearMap.opNorm_le_bound _ H.hδK fun K => DN_norm_le H hj m K

theorem RGsys_contB (j : ℕ) (w : ℝ → WS d L ℓ₀ A j) (hw : ObsCont obs j w) :
    Continuous fun m => (RGsys H m).B j (w m) := by
  show Continuous fun m => Bfam H m j (w m)
  have h := continuous_clm_apply (fun m => BNc H (by omega : j < j + 3) m)
    (fun m => norm_BNc_le H (by omega : j + 1 < j + 3) m) (fun p => BNf_continuous_m H (by omega) p)
    (hw ⟨j + 3, le_rfl⟩)
  exact h

theorem RGsys_contD (j : ℕ) (w : ℝ → WS d L ℓ₀ A j) (hw : ObsCont obs j w) :
    ObsCont obs (j + 1) fun m => (RGsys H m).D j (w m) := by
  intro N
  have hN := N.2
  show Continuous fun m => obs (j + 1) N (Dfam H m j (w m))
  simp only [obs_apply, Dfam_apply, DF_apply, proj_DFf]
  refine (continuous_const.mul (hw N.low).fst).prodMk ?_
  exact continuous_clm_apply (fun m => DNc H (by omega : j + 1 < N.1) m)
    (fun m => norm_DNc_le H _ m) (fun K => DN_continuous_m H (by omega) K) (hw N.low).snd

theorem RGsys_contg (j : ℕ) (v : ℝ → Vsp) (w : ℝ → WS d L ℓ₀ A j) (hv : Continuous v)
    (hw : ObsCont obs j w) (hr : ∀ m, ‖(v m, w m)‖ ≤ rad d ℓ₀ ε) :
    ObsCont obs (j + 1) fun m => (RGsys H m).g j (v m, w m) := by
  intro N
  have hN := N.2
  show Continuous fun m => obs (j + 1) N (gfam H m j (v m, w m))
  have e : ∀ m, obs (j + 1) N (gfam H m j (v m, w m)) = ((0 : ℂ),
      FN ℓ₀ A m j N.1 (xNs N (v m, w m)) - DN ℓ₀ A m j N.1 (projL N (w m).2)) := fun m => by
    rw [obs_apply]
    simp only [gfam]
    rw [_root_.map_sub, proj_FF H m (hr m), DF_apply, proj_DFf]
  rw [show (fun m => obs (j + 1) N (gfam H m j (v m, w m))) = _ from funext e]
  refine continuous_const.prodMk (Continuous.sub ?_ ?_)
  · have hx : Continuous fun m => xNs N (v m, w m) :=
      hv.prodMk ((hw N.low).fst.prodMk (hw N.low).snd)
    exact FN_continuous H (by omega) continuous_id hx fun m => (norm_xNs_le N _).trans (hr m)
  · exact continuous_clm_apply (fun m => DNc H (by omega : j + 1 < N.1) m)
      (fun m => norm_DNc_le H _ m) (fun K => DN_continuous_m H (by omega) K) (hw N.low).snd

end

end

end Flow
