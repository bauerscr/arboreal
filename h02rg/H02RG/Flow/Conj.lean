import Flow.Theorem
import Step.Conj

/-!
# Complex conjugation and the renormalisation group flow

* `System.stableMap_conj`: an abstract statement. If `J_V`, `J_W` are additive, isometric and
  commute with `E`, `B_j`, `D_j`, `g_j`, then `stableMap (J_W w₀) = J_V (stableMap w₀)` for
  `‖w₀‖ ≤ ρ`. The proof is by uniqueness of the stable manifold (`stableMap_unique`) applied to
  the conjugated orbit.
* Conjugations on the spaces of the flow: `KSp.conj`, `KFam.conj`, `vconj` (on `Vsp`),
  `wconj` (on `WS`), and their commutation with `FN`, `DN`, `BNf`, `FF`, `DF`, `Bfam`, `Dfam`
  and `gfam`.
* `flowN_conj`: the torus flow started at `V̄₀` is the conjugate of the flow started at `V₀`.
* `Vc_conj`: `V₀^c(m², b̄₀) = conj V₀^c(m², b₀)` for `|b₀| ≤ ρ`.
-/

namespace Flow

noncomputable section

open Finset Grassmann Loc FRD Step Metric Filter Topology Coup

local notation "cj" => starRingEnd ℂ

/-! ### The abstract statement -/

namespace System

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {W : ℕ → Type*} [∀ j, NormedAddCommGroup (W j)] [∀ j, NormedSpace ℂ (W j)]

/-- `J_V`, `J_W` are additive isometries commuting with the dynamical system `S`. -/
structure IsConj (S : System V W) (JV : V → V) (JW : ∀ j, W j → W j) : Prop where
  JV_add : ∀ a b, JV (a + b) = JV a + JV b
  JW_add : ∀ j (a b : W j), JW j (a + b) = JW j a + JW j b
  norm_JV : ∀ v, ‖JV v‖ = ‖v‖
  norm_JW : ∀ j (w : W j), ‖JW j w‖ = ‖w‖
  E_comm : ∀ v, S.E (JV v) = JV (S.E v)
  B_comm : ∀ j (w : W j), S.B j (JW j w) = JV (S.B j w)
  D_comm : ∀ j (w : W j), S.D j (JW j w) = JW (j + 1) (S.D j w)
  g_comm : ∀ j (x : V × W j), S.g j (JV x.1, JW j x.2) = JW (j + 1) (S.g j x)

variable {S : System V W} {JV : V → V} {JW : ∀ j, W j → W j}

theorem IsConj.orbit (hJ : S.IsConj JV JW) (v₀ : V) (w₀ : W 0) (j : ℕ) :
    S.orbit (JV v₀) (JW 0 w₀) j = (JV (S.orbit v₀ w₀ j).1, JW j (S.orbit v₀ w₀ j).2) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [orbit_succ, orbit_succ, ih, hJ.E_comm, hJ.B_comm, ← hJ.JV_add, hJ.D_comm, hJ.g_comm,
      ← hJ.JW_add]

theorem IsConj.norm_orbit (hJ : S.IsConj JV JW) (v₀ : V) (w₀ : W 0) (j : ℕ) :
    ‖S.orbit (JV v₀) (JW 0 w₀) j‖ = ‖S.orbit v₀ w₀ j‖ := by
  rw [hJ.orbit, Prod.norm_def, Prod.norm_def, hJ.norm_JV, hJ.norm_JW]

/-- **The stable manifold commutes with a conjugation of the system.** -/
theorem stableMap_conj {β δ γ r θ R : ℝ} [CompleteSpace V] [∀ j, CompleteSpace (W j)]
    (hS : S.Bounds β δ γ r) (hc : Admissible β δ γ r θ R) (hJ : S.IsConj JV JW) {w₀ : W 0}
    (hw : ‖w₀‖ ≤ rho β δ θ R) : S.stableMap (JW 0 w₀) = JV (S.stableMap w₀) := by
  obtain ⟨v, ⟨⟨M, hdec⟩, hRv⟩, -⟩ := hS.existsUnique_stable hc hw
  have hv := hS.stableMap_unique hc hw ⟨M, hdec⟩ hRv
  subst hv
  have hw' : ‖JW 0 w₀‖ ≤ rho β δ θ R := by rw [hJ.norm_JW]; exact hw
  refine (hS.stableMap_unique hc hw' ⟨M, fun j => ?_⟩ fun j => ?_).symm
  · rw [hJ.norm_orbit]; exact hdec j
  · rw [hJ.norm_orbit]; exact hRv j

end System

/-! ### A derivative lemma -/

theorem hasDerivAt_conj_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (J : E → E) (hJs : ∀ x y, J (x - y) = J x - J y) (hJc : ∀ (c : ℂ) x, J (c • x) = cj c • J x)
    (hJn : ∀ x, ‖J x‖ = ‖x‖) {f : ℂ → E} {f' : E} (hf : HasDerivAt f f' 0) :
    HasDerivAt (fun t => J (f (cj t))) (J f') 0 := by
  rw [hasDerivAt_iff_isLittleO] at hf ⊢
  have ht : Tendsto (fun t : ℂ => cj t) (𝓝 0) (𝓝 0) := by
    simpa using (Complex.continuous_conj.tendsto 0)
  have h := hf.comp_tendsto ht
  rw [← Asymptotics.isLittleO_norm_left, ← Asymptotics.isLittleO_norm_right] at h ⊢
  have e1 : (fun t : ℂ => ‖J (f (cj t)) - J (f (cj 0)) - (t - 0) • J f'‖) =
      (fun t : ℂ => ‖f (cj t) - f 0 - (cj t - 0) • f'‖) := by
    funext t
    have h0 : cj (0 : ℂ) = 0 := by simp
    simp only [h0, sub_zero]
    rw [← hJn (f (cj t) - f 0 - cj t • f'), hJs, hJs, hJc, Complex.conj_conj]
  have e2 : (fun t : ℂ => ‖t - 0‖) = fun t : ℂ => ‖cj t - 0‖ := by
    funext t; simp
  rw [e1, e2]
  exact h

variable {d L : ℕ} [NeZero L]

/-! ### Activities -/

theorem restr_conjA (j : ℕ) {N : ℕ} (K : Act d L N) : restr j (conjA K) = conjA (restr j K) := by
  funext X; by_cases hX : IsConn j X <;> simp [restr, hX]

theorem conjA_mem_KSub {j N : ℕ} {K : Act d L N} (hK : K ∈ KSub j N) : conjA K ∈ KSub j N :=
  ⟨hK.1.conj, fun X hX => by simp [hK.2 X hX]⟩

theorem conjA_mem_KSub_iff {j N : ℕ} {K : Act d L N} : conjA K ∈ KSub j N ↔ K ∈ KSub j N :=
  ⟨fun h => by simpa using conjA_mem_KSub h, conjA_mem_KSub⟩

section KSp

variable {j N : ℕ} {ℓ A : ℝ}

/-- Conjugation on `𝒦_j(Λ_N)`. -/
def KSp.conj (K : KSp d L j N ℓ A) : KSp d L j N ℓ A :=
  KSp.mk (conjA K.toAct) (conjA_mem_KSub K.toAct_mem)

@[simp] theorem KSp.toAct_conj (K : KSp d L j N ℓ A) : K.conj.toAct = conjA K.toAct := rfl

theorem KSp.conj_sub (K K' : KSp d L j N ℓ A) : (K - K').conj = K.conj - K'.conj :=
  KSp.toAct_injective (by funext X; simp [_root_.map_sub])

theorem KSp.conj_smul (c : ℂ) (K : KSp d L j N ℓ A) : (c • K).conj = cj c • K.conj :=
  KSp.toAct_injective (by simp [_root_.map_smul, conjA_smul])

@[simp] theorem KSp.conj_zero : (0 : KSp d L j N ℓ A).conj = 0 :=
  KSp.toAct_injective (by simp)

@[simp] theorem KSp.norm_conj (K : KSp d L j N ℓ A) : ‖K.conj‖ = ‖K‖ := by
  rw [KSp.norm_def, KSp.norm_def, KSp.toAct_conj, Knorm_conjA]

end KSp

/-! ### Families -/

theorem realLin_embV (N M : ℕ) : RealLin (embV (d := d) (L := L) N M) := fun v => by
  ext b; simp [embV, map_sum, apply_ite]

theorem Compat.conjA {j D N M : ℕ} {K : Act d L N} {K' : Act d L M} (h : Compat j D K K') :
    Compat j D (conjA K) (conjA K') := fun X hX hc hd => by
  simp only [conjA_apply]
  rw [← h X hX hc hd]
  exact (conjE_mapE (realLin_embV N M) (K X)).symm

section KFam

variable {j c : ℕ} {ℓ A : ℝ} [Fact (0 < ℓ)] [Fact (0 < A)]

/-- Conjugation on the families `𝒦_j(ℤ^d)`. -/
def KFam.conj (K : KFam d L j c ℓ A) : KFam d L j c ℓ A :=
  KFam.mk (fun N => conjA (K.act N)) (fun N => conjA_mem_KSub (K.act_mem N))
    (fun N M h => (K.compat h).conjA)
    ⟨‖K‖, by rintro _ ⟨N, rfl⟩; simp only [Knorm_conjA]; exact K.Knorm_le N⟩

@[simp] theorem KFam.act_conj (K : KFam d L j c ℓ A) (N : Idx j c) :
    K.conj.act N = conjA (K.act N) := rfl

theorem KFam.proj_conj (K : KFam d L j c ℓ A) (N : Idx j c) :
    KFam.proj N K.conj = (KFam.proj N K).conj := KSp.toAct_injective rfl

@[simp] theorem KFam.norm_conj (K : KFam d L j c ℓ A) : ‖K.conj‖ = ‖K‖ := by
  rw [KFam.norm_eq_iSup, KFam.norm_eq_iSup]
  simp only [KFam.act_conj, Knorm_conjA]

theorem KFam.conj_add (K K' : KFam d L j c ℓ A) : (K + K').conj = K.conj + K'.conj :=
  KFam.ext fun N => by simp [conjA_add]

theorem KFam.conj_smul (a : ℂ) (K : KFam d L j c ℓ A) : (a • K).conj = cj a • K.conj :=
  KFam.ext fun N => by simp [conjA_smul]

theorem KFam.conj_sub (K K' : KFam d L j c ℓ A) : (K - K').conj = K.conj - K'.conj := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ K', KFam.conj_add, KFam.conj_smul, map_neg, map_one,
    neg_one_smul, ← sub_eq_add_neg]

@[simp] theorem KFam.conj_zero : (0 : KFam d L j c ℓ A).conj = 0 :=
  KFam.ext fun N => by simp

end KFam

/-! ### Coordinates -/

/-- Conjugation on `Vsp = ℂ³`. -/
def vconj (v : Vsp) : Vsp := (cj v.1, cj v.2.1, cj v.2.2)

@[simp] theorem norm_vconj (v : Vsp) : ‖vconj v‖ = ‖v‖ := by
  simp [vconj, Prod.norm_def]

theorem vconj_add (v w : Vsp) : vconj (v + w) = vconj v + vconj w := by
  simp [vconj]

@[simp] theorem vconj_zero : vconj 0 = 0 := by simp [vconj]

theorem VresL_conj (j : ℕ) (v : Vsp) (b : ℂ) :
    VresL d L j (vconj v, cj b) = (VresL d L j (v, b)).conj :=
  Vcoup.ext' (by simp [vconj]) (by simp [vconj]) (by simp [vconj, map_div₀])
    (by simp [vconj])

theorem vresL_conj (j : ℕ) (V : Vcoup) : vresL L j V.conj = vconj (vresL L j V) := by
  simp [vconj]

theorem Emap_vconj (v : Vsp) : Emap L (vconj v) = vconj (Emap L v) := by
  simp [vconj]

variable {ℓ₀ A : ℝ}

/-- Conjugation on `XS = Vsp × ℂ × 𝒦_j(Λ_N)`. -/
def xconj {j N : ℕ} (x : XS d L j N ℓ₀ A) : XS d L j N ℓ₀ A := (vconj x.1, cj x.2.1, x.2.2.conj)

/-! ### The torus maps -/

theorem FN_conj (hd : 1 ≤ d) (hL : 3 ≤ L) {j N : ℕ} (hj : j < N) (m : ℝ)
    (x : XS d L j N ℓ₀ A) : FN ℓ₀ A m j N (xconj x) = (FN ℓ₀ A m j N x).conj := by
  have key : restr (j + 1) (Knext j (Cm d L N m j) (VresL d L j ((xconj x).1, (xconj x).2.1))
      (xconj x).2.2.toAct) =
      conjA (restr (j + 1) (Knext j (Cm d L N m j) (VresL d L j (x.1, x.2.1)) x.2.2.toAct)) := by
    simp only [xconj, VresL_conj, KSp.toAct_conj, Knext_conjA hd hL hj, restr_conjA]
  unfold FN
  split_ifs with h1 h2 h2
  · exact KSp.toAct_injective (by simp [key])
  · exact absurd (conjA_mem_KSub_iff.1 (key ▸ h1)) h2
  · exact absurd (key ▸ conjA_mem_KSub h2) h1
  · simp

theorem BNf_conj (hd : 1 ≤ d) (hL : 3 ≤ L) {j N : ℕ} (hj : j < N) (m : ℝ) (b : ℂ)
    (K : KS d L j N ℓ₀ A) :
    BNf ℓ₀ A m j N (cj b, K.conj) = vconj (BNf ℓ₀ A m j N (b, K)) := by
  unfold BNf
  have e : VresL d L j ((0 : Vsp), cj b) = (VresL d L j (0, b)).conj := by
    rw [← VresL_conj, vconj_zero]
  simp only [e, KSp.toAct_conj, uVnext_conj j _ _ _ hd hL hj, conjUV, vresL_conj]

theorem Hyp.hL3 {ε C₁ δK Kc Cw : ℝ} (H : Hyp d L A ℓ₀ ε C₁ δK Kc Cw) : 3 ≤ L := by
  have := H.hL16; omega

section W

variable [Fact (0 < ℓ₀)] [Fact (0 < A)] {j : ℕ}

/-- Conjugation on `W_j = ℂ × 𝒦_j(ℤ^d)`. -/
def wconj (j : ℕ) (w : WS d L ℓ₀ A j) : WS d L ℓ₀ A j := (cj w.1, w.2.conj)

@[simp] theorem norm_wconj (w : WS d L ℓ₀ A j) : ‖wconj j w‖ = ‖w‖ := by
  rw [Prod.norm_def, Prod.norm_def]
  simp only [wconj, Complex.norm_conj]
  exact congrArg _ (KFam.norm_conj w.2)

theorem wconj_add (w w' : WS d L ℓ₀ A j) : wconj j (w + w') = wconj j w + wconj j w' := by
  simp [wconj, KFam.conj_add]

theorem projL_conj (N : Idx (j + 1) 3) (K : KFam d L j 3 (ellj d (L : ℝ) ℓ₀ j) A) :
    projL N K.conj = (projL N K).conj := KFam.proj_conj K _

theorem xNs_conj (N : Idx (j + 1) 3) (x : Vsp × WS d L ℓ₀ A j) :
    xNs N (vconj x.1, wconj j x.2) = xconj (xNs N x) := by
  simp only [xNs, xconj, wconj, projL_conj]


end W

section H

variable {ε C₁ δK Kc Cw : ℝ} [Fact (0 < ℓ₀)] [Fact (0 < A)]
variable (H : Hyp d L A ℓ₀ ε C₁ δK Kc Cw)
include H

variable {j : ℕ}

theorem DN_conj {j N : ℕ} (hj : j + 1 < N) (m : ℝ) (K : KS d L j N ℓ₀ A) :
    DN ℓ₀ A m j N K.conj = (DN ℓ₀ A m j N K).conj := by
  have h1 := hasDerivAt_FN_line H hj m K.conj
  have h2 := hasDerivAt_conj_comp (fun K' : KS d L (j + 1) N ℓ₀ A => K'.conj)
    KSp.conj_sub KSp.conj_smul KSp.norm_conj (hasDerivAt_FN_line H hj m K)
  have e : (fun t : ℂ => FN ℓ₀ A m j N (0, 0, t • K.conj)) =
      fun t : ℂ => (FN ℓ₀ A m j N (0, 0, cj t • K)).conj := by
    funext t
    rw [← FN_conj H.hd1 H.hL3 (by omega)]
    congr 1
    simp [xconj, KSp.conj_smul]
  rw [e] at h1
  exact h1.unique h2

set_option maxHeartbeats 800000 in
theorem FF_conj (m : ℝ) (x : Vsp × WS d L ℓ₀ A j) :
    FF H m j (vconj x.1, wconj j x.2) = (FF H m j x).conj := by
  have e : ∀ N : Idx (j + 1) 3, FN ℓ₀ A m j N.1 (xNs N (vconj x.1, wconj j x.2)) =
      (FN ℓ₀ A m j N.1 (xNs N x)).conj := fun N => by
    rw [xNs_conj, FN_conj H.hd1 H.hL3 (by have := N.2; omega)]
  have hb : (fun N : Idx (j + 1) 3 => (Knorm (j + 1) (ellj d L ℓ₀ (j + 1)) A
        (FN ℓ₀ A m j N.1 (xNs N (vconj x.1, wconj j x.2))).toAct).toReal) =
      fun N : Idx (j + 1) 3 => (Knorm (j + 1) (ellj d L ℓ₀ (j + 1)) A
        (FN ℓ₀ A m j N.1 (xNs N x)).toAct).toReal := by
    funext N; rw [e N, KSp.toAct_conj, Knorm_conjA]
  have hbb : BddAbove (Set.range fun N : Idx (j + 1) 3 =>
        (Knorm (j + 1) (ellj d L ℓ₀ (j + 1)) A
          (FN ℓ₀ A m j N.1 (xNs N (vconj x.1, wconj j x.2))).toAct).toReal) ↔
      BddAbove (Set.range fun N : Idx (j + 1) 3 => (Knorm (j + 1) (ellj d L ℓ₀ (j + 1)) A
        (FN ℓ₀ A m j N.1 (xNs N x)).toAct).toReal) := by rw [hb]
  unfold FF
  by_cases hB : BddAbove (Set.range fun N : Idx (j + 1) 3 => (Knorm (j + 1) (ellj d L ℓ₀ (j + 1)) A
      (FN ℓ₀ A m j N.1 (xNs N x)).toAct).toReal)
  · rw [dif_pos hB, dif_pos (hbb.2 hB)]
    exact KFam.ext fun N => by simp only [KFam.act_mk, KFam.act_conj, e N, KSp.toAct_conj]
  · rw [dif_neg hB, dif_neg (fun h => hB (hbb.1 h))]
    simp

theorem DF_conj (m : ℝ) (K : KFam d L j 3 (ellj d (L : ℝ) ℓ₀ j) A) :
    DF H m j K.conj = (DF H m j K).conj := by
  refine KFam.ext fun N => ?_
  have hN := N.2
  rw [KFam.act_conj, KFam.act_def, KFam.act_def, DF_apply, DF_apply, proj_DFf, proj_DFf,
    projL_conj, DN_conj H (by omega), KSp.toAct_conj]

theorem RGsys_isConj (m : ℝ) : (RGsys H m).IsConj vconj wconj where
  JV_add := vconj_add
  JW_add j := wconj_add
  norm_JV := norm_vconj
  norm_JW j := norm_wconj
  E_comm v := by rw [RGsys_E, Eequiv_apply, Eequiv_apply, Emap_vconj]
  B_comm j w := by
    show Bfam H m j (wconj j w) = vconj (Bfam H m j w)
    rw [Bfam_apply, Bfam_apply]
    simp only [wconj]
    rw [KFam.proj_conj]
    exact BNf_conj H.hd1 H.hL3 (by omega) m _ _
  D_comm j w := by
    show Dfam H m j (wconj j w) = wconj (j + 1) (Dfam H m j w)
    rw [Dfam_apply, Dfam_apply]
    simp only [wconj, DF_conj, map_mul]
    congr 2
    simp [bfac, map_inv₀, map_pow, map_natCast]
  g_comm j x := by
    show gfam H m j (vconj x.1, wconj j x.2) = wconj (j + 1) (gfam H m j x)
    unfold gfam
    rw [FF_conj H m x]
    have h0 : cj (0 : ℂ) = 0 := by simp
    simp only [wconj, DF_conj, KFam.conj_sub, h0]

variable {R : ℝ}
  (hc : Admissible (βB d L ℓ₀ Kc Cw) (δD d L δK) (C₁ * cX d ℓ₀ ^ 2) (rad d ℓ₀ ε) (3 / 4) R)
include hc

theorem stableMap_wconj (m : ℝ) {w₀ : WS d L ℓ₀ A 0}
    (hw : ‖w₀‖ ≤ rho (βB d L ℓ₀ Kc Cw) (δD d L δK) (3 / 4) R) :
    (RGsys H m).stableMap (wconj 0 w₀) = vconj ((RGsys H m).stableMap w₀) :=
  System.stableMap_conj (RGsys_bounds H m) hc (RGsys_isConj H m) hw

/-- **Reality of the stable manifold**: `V₀^c(m², b̄₀) = conj V₀^c(m², b₀)`. -/
theorem Vc_conj (m : ℝ) {b₀ : ℂ} (hb : ‖b₀‖ ≤ rho (βB d L ℓ₀ Kc Cw) (δD d L δK) (3 / 4) R) :
    Vc H m (cj b₀) = (Vc H m b₀).conj := by
  have hw : w0 d L ℓ₀ A (cj b₀) = wconj 0 (w0 d L ℓ₀ A b₀) := by simp [wconj]
  rw [Vc, Vc, hw, stableMap_wconj H hc m (by rw [norm_w0]; exact hb), VresL_conj]

end H

/-! ### The torus flow -/

/-- **The torus flow commutes with conjugation.** -/
theorem flowN_conj (hd : 1 ≤ d) (hL : 3 ≤ L) (N : ℕ) (msq : ℝ) (V₀ : Vcoup) :
    ∀ j ≤ N, flowN d L N msq V₀.conj j =
      ((flowN d L N msq V₀ j).1.conj, conjA (flowN d L N msq V₀ j).2)
  | 0, _ => by simp [flowN_zero]
  | j + 1, hj => by
    rw [flowN_succ, flowN_succ, flowN_conj hd hL N msq V₀ j (by omega),
      uVnext_conj j _ _ _ hd hL (by omega), Knext_conjA hd hL (by omega), restr_conjA]
    rfl

theorem uflow_conj (hd : 1 ≤ d) (hL : 3 ≤ L) {N : ℕ} (msq : ℝ) (V₀ : Vcoup) {j : ℕ}
    (hj : j < N) : uflow d L N msq V₀.conj j = cj (uflow d L N msq V₀ j) := by
  rw [uflow, uflow, flowN_conj hd hL N msq V₀ j hj.le, uVnext_conj j _ _ _ hd hL hj]
  rfl

end

end Flow
