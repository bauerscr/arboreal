import Flow.Consistency
import Loc.EstBasic
import Step.EstSetup
import Step.Deriv

/-!
# The Banach spaces of Section `sec:flow`

Section `sec:flow` iterates the infinite volume renormalisation group map on the Banach space
`𝒦^∅_j(ℤ^d)` with the norm `‖K‖_j` of `e:K-norm`.  We realise this space as a space of
compatible families of torus activities.

* `norm_coeff_le`, `tNorm_eq_zero_iff`: the `T` norm controls every coefficient and is definite.
* `KSp d L j N ℓ A`: the normalised activities of `𝒦_j(Λ_N)` (`InK` and vanishing off
  connected polymers) with the norm `(Knorm j ℓ A K).toReal`; a finite-dimensional, hence
  complete, normed space.
* `KFam d L j c ℓ A`: bounded families `(K^N)_{N ≥ j + c}` of normalised activities which are
  pairwise compatible (`Compat j (Dc d L N j) K^N K^M` for `N ≤ M`), with the norm
  `sup_N ‖K^N‖_j`; a closed subspace of `ℓ^∞`, hence a complex Banach space.
* `KFam.coeffCLM`, `KFam.pairCLM`: coefficient and pairing functionals; the (weighted) pairings
  norm the space (`KFam.norming_pair`).
* `Norming.hasDerivAt`: holomorphy in a Banach space normed by a family of continuous linear
  maps can be checked through the family (given a candidate derivative), and
  `KFam.differentiableOn_of_coeff`: coefficientwise holomorphic, locally bounded curves in
  `KFam` are holomorphic.
-/

namespace Flow

noncomputable section

open Finset Grassmann Loc FRD Step ENNReal Metric Filter Topology

/-! ## Definiteness of the `T` norm -/

section TNorm

variable {X : Type*} [DecidableEq X] [Fintype X] {E : Type*} [Fintype E] [DecidableEq E]
  [AddAction (E → ℕ) X] {p : ℕ} {h ℓ : ℝ}

/-- The test function `δ_z`, the indicator function of the sequence `z`. -/
def delta {m : ℕ} (z : Fin m → Sf X) : TestFn X := single m fun w => if w = z then 1 else 0

theorem pair_delta (F : N X) {m : ℕ} (z : Fin m → Sf X) :
    pair F (delta z) = (m.factorial : ℂ)⁻¹ * coeff F z := by
  rw [delta, pair_single']
  simp

theorem phiNorm_delta_ne_top {m : ℕ} (z : Fin m → Sf X) : phiNorm E p h ℓ (delta z) ≠ ⊤ := by
  classical
  set f : (Fin m → Sf X) → ℂ := fun w => if w = z then 1 else 0
  set S : Finset (Fin m → E → ℕ) :=
    Fintype.piFinset fun _ => Fintype.piFinset fun _ => range (p + 1)
  refine ne_top_of_le_ne_top ofReal_ne_top (phiNorm_single_le' (f := f)
    (M := ∑ w, ∑ α ∈ S, |ℓ⁻¹ ^ m * h ^ ord α * ‖nab α f w‖|)
    (sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _) fun w α hα => ?_)
  have hαS : α ∈ S := by
    refine Fintype.mem_piFinset.2 fun i => Fintype.mem_piFinset.2 fun e => mem_range.2 ?_
    have : α i e ≤ Grassmann.mabs (α i) :=
      single_le_sum (f := fun e => α i e) (fun _ _ => Nat.zero_le _) (mem_univ e)
    have := hα i
    omega
  refine (le_abs_self _).trans ?_
  refine (single_le_sum (f := fun α => |ℓ⁻¹ ^ m * h ^ ord α * ‖nab α f w‖|)
    (fun _ _ => abs_nonneg _) hαS).trans ?_
  exact single_le_sum (f := fun w => ∑ α ∈ S, |ℓ⁻¹ ^ m * h ^ ord α * ‖nab α f w‖|)
    (fun _ _ => sum_nonneg fun _ _ => abs_nonneg _) (mem_univ w)

variable (E p h ℓ) in
/-- The constant `c(h, ℓ, z) = |z|! ‖δ_z‖_Φ` in `|F_z| ≤ c ‖F‖_T`. -/
def cCoef {m : ℕ} (z : Fin m → Sf X) : ℝ := m.factorial * (phiNorm E p h ℓ (delta z)).toReal

/-- Every coefficient is controlled by the `T` norm: `|F_z| ≤ c(h, ℓ, z) ‖F‖_T`. -/
theorem norm_coeff_le (hh : 0 < h) (hℓ : 0 < ℓ) (F : N X) {m : ℕ} (z : Fin m → Sf X) :
    ‖coeff F z‖ ≤ cCoef E p h ℓ z * (tNorm E p h ℓ F).toReal := by
  have := abs_pair_le hh hℓ F toReal_nonneg
    (le_of_eq (ofReal_toReal (phiNorm_delta_ne_top (E := E) (p := p) (h := h) (ℓ := ℓ) z)).symm)
  rw [pair_delta, norm_mul, norm_inv, Complex.norm_natCast,
    inv_mul_le_iff₀ (by positivity)] at this
  unfold cCoef
  calc ‖coeff F z‖ ≤ m.factorial * ((tNorm E p h ℓ F).toReal *
        (phiNorm E p h ℓ (delta z)).toReal) := this
    _ = _ := by ring

/-- The `T` norm is definite. -/
theorem eq_zero_of_tNorm_eq_zero (hh : 0 < h) (hℓ : 0 < ℓ) {F : N X}
    (hF : tNorm E p h ℓ F = 0) : F = 0 := by
  rw [sum_coeff F]
  refine sum_eq_zero fun n _ => sum_eq_zero fun z _ => ?_
  have := norm_coeff_le (E := E) (p := p) hh hℓ F z
  rw [hF, toReal_zero, mul_zero] at this
  rw [norm_le_zero_iff.1 this, mul_zero, zero_smul]

theorem tNorm_zero : tNorm E p h ℓ (0 : N X) = 0 :=
  le_antisymm (by simpa using tNorm_smul_le (E := E) (p := p) (h := h) (ℓ := ℓ) 0 (0 : N X))
    bot_le

theorem tNorm_eq_zero_iff (hh : 0 < h) (hℓ : 0 < ℓ) {F : N X} :
    tNorm E p h ℓ F = 0 ↔ F = 0 :=
  ⟨eq_zero_of_tNorm_eq_zero hh hℓ, fun hF => hF ▸ tNorm_zero⟩

/-- The coefficient vector `F ↦ (F_z)_{|z| ≤ |Λ_f|}`. -/
def cvec : N X →ₗ[ℂ] (Σ n : Fin (Nf X + 1), Fin n → Sf X) → ℂ where
  toFun F s := coeff F s.2
  map_add' F G := by ext s; simp [coeff_add]
  map_smul' c F := by ext s; simp [coeff_smul]

theorem cvec_injective : Function.Injective (cvec : N X →ₗ[ℂ] _) := by
  intro F G hFG
  rw [sum_coeff F, sum_coeff G]
  refine sum_congr rfl fun n hn => sum_congr rfl fun z _ => ?_
  have := congr_fun hFG ⟨⟨n, by simpa [Nat.lt_succ_iff] using hn⟩, z⟩
  simp only [cvec, LinearMap.coe_mk, AddHom.coe_mk] at this
  rw [this]

instance : Module.Finite ℂ (N X) := Module.Finite.of_injective cvec cvec_injective

end TNorm

/-! ## Normalised activities on a torus -/

section KSp

variable {d L : ℕ} [NeZero L]

/-- The normalised activities of `𝒦_j(Λ_N)`: `K ∈ 𝒦^∅_j` vanishing off connected polymers. -/
def KSub (j N : ℕ) : Submodule ℂ (Act d L N) where
  carrier := {K | InK j K ∧ ∀ X, ¬ IsConn j X → K X = 0}
  add_mem' {K K'} hK hK' := by
    refine ⟨⟨fun X hX => ?_, fun X hX => ?_, fun X hX => ?_, fun T hT hTb X hX => ?_⟩,
      fun X hX => ?_⟩
    · exact add_mem (hK.1.loc X hX) (hK'.1.loc X hX)
    · intro n z hz
      simp only [Pi.add_apply, Subalgebra.coe_add, coeff_add, hK.1.sym X hX n z hz,
        hK'.1.sym X hX n z hz, add_zero]
    · simp only [Pi.add_apply, Subalgebra.coe_add]
      rw [_root_.map_add, hK.1.jinv X hX, hK'.1.jinv X hX]
    · simp only [Pi.add_apply, Subalgebra.coe_add]
      rw [_root_.map_add, hK.1.aut T hT hTb X hX, hK'.1.aut T hT hTb X hX]
    · simp [hK.2 X hX, hK'.2 X hX]
  zero_mem' := by
    refine ⟨⟨fun X _ => ?_, fun X _ => ?_, fun X _ => ?_, fun T _ _ X _ => ?_⟩, fun X _ => rfl⟩
    · exact zero_mem _
    · intro n z _; simp [coeff_zero]
    · simp
    · simp
  smul_mem' c K hK := by
    refine ⟨⟨fun X hX => ?_, fun X hX => ?_, fun X hX => ?_, fun T hT hTb X hX => ?_⟩,
      fun X hX => ?_⟩
    · exact Subalgebra.smul_mem _ (hK.1.loc X hX) c
    · intro n z hz
      simp only [Pi.smul_apply, Subalgebra.coe_smul, coeff_smul, hK.1.sym X hX n z hz, mul_zero]
    · simp only [Pi.smul_apply, Subalgebra.coe_smul]
      rw [_root_.map_smul, hK.1.jinv X hX]
    · simp only [Pi.smul_apply, Subalgebra.coe_smul]
      rw [_root_.map_smul, hK.1.aut T hT hTb X hX]
    · simp [hK.2 X hX]

variable (d L) in
/-- `𝒦_j(Λ_N)` (normalised activities) with the norm `‖·‖_j = (Knorm j ℓ A ·).toReal`; the
parameters `ℓ`, `A` only enter through the norm. -/
def KSp (j N : ℕ) (_ℓ _A : ℝ) : Type := KSub (d := d) (L := L) j N

variable {j N : ℕ} {ℓ A : ℝ}

instance : AddCommGroup (KSp d L j N ℓ A) := inferInstanceAs (AddCommGroup (KSub j N))
instance : Module ℂ (KSp d L j N ℓ A) := inferInstanceAs (Module ℂ (KSub j N))

/-- The underlying activity. -/
def KSp.toAct : KSp d L j N ℓ A →ₗ[ℂ] Act d L N := (KSub j N).subtype

theorem KSp.toAct_injective : Function.Injective (KSp.toAct : KSp d L j N ℓ A → Act d L N) :=
  Subtype.val_injective

theorem KSp.toAct_mem (K : KSp d L j N ℓ A) : K.toAct ∈ KSub j N := (K : KSub j N).2

theorem KSp.inK (K : KSp d L j N ℓ A) : InK j K.toAct := K.toAct_mem.1

/-- The element of `KSp` defined by a normalised activity. -/
def KSp.mk (K : Act d L N) (hK : K ∈ KSub j N) : KSp d L j N ℓ A := (⟨K, hK⟩ : KSub j N)

@[simp] theorem KSp.toAct_mk (K : Act d L N) (hK : K ∈ KSub j N) :
    (KSp.mk (ℓ := ℓ) (A := A) K hK).toAct = K := rfl

instance : Norm (KSp d L j N ℓ A) := ⟨fun K => (Knorm j ℓ A K.toAct).toReal⟩

theorem KSp.norm_def (K : KSp d L j N ℓ A) : ‖K‖ = (Knorm j ℓ A K.toAct).toReal := rfl

theorem mem_connSets {X : Finset (Lam d L N)} : X ∈ connSets (L := L) (N := N) j ↔ IsConn j X := by
  classical
  simp [connSets]

theorem Knorm_eq_zero (hℓ : 0 < ℓ) (hA : 0 < A) {K : Act d L N} (hK : K ∈ KSub j N)
    (h0 : Knorm j ℓ A K = 0) : K = 0 := by
  funext X
  by_cases hX : IsConn j X
  · have h1 := wnorm_le_Knorm (ℓ := ℓ) (A := A) (K := K) hX
    rw [h0, nonpos_iff_eq_zero, wnorm, mul_eq_zero, ENNReal.ofReal_eq_zero] at h1
    rcases h1 with h1 | h1
    · exact absurd h1 (not_le.2 (by positivity))
    · exact Subtype.ext ((tNorm_eq_zero_iff (by have := NeZero.pos L; positivity) hℓ).1 h1)
  · exact hK.2 X hX

theorem KSp.normedSpaceCore [Fact (0 < ℓ)] [Fact (0 < A)] :
    NormedSpace.Core ℂ (KSp d L j N ℓ A) where
  norm_nonneg _ := toReal_nonneg
  norm_smul c K := by
    rw [KSp.norm_def, KSp.norm_def, _root_.map_smul, Knorm_smul, toReal_mul, toReal_ofReal (norm_nonneg _)]
  norm_triangle K K' := by
    rw [KSp.norm_def, KSp.norm_def, KSp.norm_def, _root_.map_add,
      ← toReal_add (Knorm_ne_top Fact.out _) (Knorm_ne_top Fact.out _)]
    exact toReal_mono (add_ne_top.2 ⟨Knorm_ne_top Fact.out _, Knorm_ne_top Fact.out _⟩)
      (Knorm_add_le _ _ _ _ _)
  norm_eq_zero_iff K := by
    refine ⟨fun h0 => ?_, fun h0 => by
      rw [h0, KSp.norm_def, _root_.map_zero, Knorm, toReal_eq_zero_iff]
      left
      refine le_antisymm (iSup₂_le fun X _ => ?_) bot_le
      simp [tNorm_zero]⟩
    rw [KSp.norm_def, toReal_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · exact KSp.toAct_injective (by
        rw [_root_.map_zero]; exact Knorm_eq_zero Fact.out Fact.out K.toAct_mem h0)
    · exact absurd h0 (Knorm_ne_top Fact.out _)

variable [Fact (0 < ℓ)] [Fact (0 < A)]

instance : NormedAddCommGroup (KSp d L j N ℓ A) :=
  NormedAddCommGroup.ofCore KSp.normedSpaceCore

instance : NormedSpace ℂ (KSp d L j N ℓ A) := NormedSpace.ofCore KSp.normedSpaceCore

instance : FiniteDimensional ℂ (Act d L N) := by
  have : FiniteDimensional ℂ (EvR (Lam d L N)) :=
    Module.Finite.of_injective (Ev (Lam d L N)).val.toLinearMap Subtype.val_injective
  infer_instance

instance : FiniteDimensional ℂ (KSp d L j N ℓ A) :=
  inferInstanceAs (FiniteDimensional ℂ (KSub (d := d) (L := L) j N))

instance : CompleteSpace (KSp d L j N ℓ A) := FiniteDimensional.complete ℂ _

end KSp

/-! ## Holomorphy through a norming family -/

section Norming

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- Cauchy estimate for the first order Taylor remainder: if `g` is holomorphic and bounded
by `B` on the disc of radius `4ρ` about `t`, then
`‖g(t + h) - g(t) - h g'(t)‖ ≤ B ρ^{-2} |h|^2` for `|h| < ρ`. -/
theorem norm_taylor_remainder_le [CompleteSpace G] {g : ℂ → G} {t : ℂ} {ρ B : ℝ} (hρ : 0 < ρ)
    (hd : DifferentiableOn ℂ g (ball t (4 * ρ))) (hb : ∀ s ∈ ball t (4 * ρ), ‖g s‖ ≤ B)
    {h : ℂ} (hh : ‖h‖ < ρ) :
    ‖g (t + h) - g t - h • deriv g t‖ ≤ B / ρ ^ 2 * ‖h‖ ^ 2 := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hb t (mem_ball_self (by positivity)))
  -- Cauchy estimate for `g'` on `closedBall t (2ρ)`
  have h1 : ∀ w ∈ closedBall t (2 * ρ), ‖deriv g w‖ ≤ B / ρ := by
    intro w hw
    rw [mem_closedBall] at hw
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ ?_ fun z hz => hb z ?_
    · refine DifferentiableOn.diffContOnCl (hd.mono ?_)
      rw [closure_ball w hρ.ne']
      intro z hz
      rw [mem_closedBall] at hz
      rw [mem_ball]
      linarith [dist_triangle z w t]
    · rw [mem_sphere] at hz
      rw [mem_ball]
      linarith [dist_triangle z w t]
  have hd' : DifferentiableOn ℂ (deriv g) (ball t (4 * ρ)) := hd.deriv isOpen_ball
  -- Cauchy estimate for `g''` on `ball t ρ`
  have h2 : ∀ s ∈ ball t ρ, ‖deriv (deriv g) s‖ ≤ B / ρ / ρ := by
    intro s hs
    rw [mem_ball] at hs
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ ?_ fun z hz => h1 z ?_
    · refine DifferentiableOn.diffContOnCl (hd'.mono ?_)
      rw [closure_ball s hρ.ne']
      intro z hz
      rw [mem_closedBall] at hz
      rw [mem_ball]
      linarith [dist_triangle z s t]
    · rw [mem_sphere] at hz
      rw [mem_closedBall]
      linarith [dist_triangle z s t]
  have hballU : ∀ s ∈ ball t ρ, s ∈ ball t (4 * ρ) := fun s hs => by
    rw [mem_ball] at hs ⊢; linarith
  -- `‖g'(s) - g'(t)‖ ≤ B ρ^{-2} |s - t|`
  have h3 : ∀ s ∈ ball t ρ, ‖deriv g s - deriv g t‖ ≤ B / ρ / ρ * ‖s - t‖ := fun s hs =>
    (convex_ball t ρ).norm_image_sub_le_of_norm_deriv_le
      (fun x hx => hd'.differentiableAt (isOpen_ball.mem_nhds (hballU x hx))) h2
      (mem_ball_self hρ) hs
  -- the remainder
  set R : ℂ → G := fun s => g s - s • deriv g t
  have hR : ∀ s ∈ ball t ρ, HasDerivAt R (deriv g s - deriv g t) s := fun s hs => by
    have := ((hd.differentiableAt (isOpen_ball.mem_nhds (hballU s hs))).hasDerivAt).sub
      ((hasDerivAt_id s).smul_const (deriv g t))
    simp only [id, one_smul] at this
    exact this
  have hsub : closedBall t ‖h‖ ⊆ ball t ρ := closedBall_subset_ball hh
  have h4 := (convex_closedBall t ‖h‖).norm_image_sub_le_of_norm_deriv_le
    (f := R) (C := B / ρ / ρ * ‖h‖) (x := t) (y := t + h)
    (fun x hx => (hR x (hsub hx)).differentiableAt)
    (fun x hx => by
      rw [(hR x (hsub hx)).deriv]
      refine (h3 x (hsub hx)).trans ?_
      gcongr
      rwa [mem_closedBall, dist_eq_norm] at hx)
    (mem_closedBall_self (norm_nonneg _)) (by simp [mem_closedBall])
  have e : R (t + h) - R t = g (t + h) - g t - h • deriv g t := by
    simp only [R, add_smul]; abel
  rw [e, add_sub_cancel_left] at h4
  calc _ ≤ B / ρ / ρ * ‖h‖ * ‖h‖ := h4
    _ = B / ρ ^ 2 * ‖h‖ ^ 2 := by ring

/-- A family of continuous linear maps `φ_i : W → F_i` *norms* `W` if `‖φ_i w‖ ≤ ‖w‖` and
`‖w‖ = sup_i ‖φ_i w‖`. -/
structure Norming {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] {ι : Type*}
    {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℂ (F i)]
    (φ : ∀ i, W →L[ℂ] F i) : Prop where
  le : ∀ i w, ‖φ i w‖ ≤ ‖w‖
  ge : ∀ w (M : ℝ), 0 ≤ M → (∀ i, ‖φ i w‖ ≤ M) → ‖w‖ ≤ M

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] {ι : Type*}
  {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℂ (F i)]
  {φ : ∀ i, W →L[ℂ] F i} [∀ i, CompleteSpace (F i)]

/-- `f` is locally bounded on `U`. -/
def LocBdd (f : ℂ → W) (U : Set ℂ) : Prop := ∀ t ∈ U, ∃ r > 0, ∃ B, ∀ s ∈ ball t r, ‖f s‖ ≤ B

/-- **Holomorphy through a norming family.** If `φ` norms `W`, `f : ℂ → W` is locally bounded
on the open set `U`, every `φ_i ∘ f` is holomorphic on `U`, and `f'` is a candidate derivative
(`φ_i (f' t) = (φ_i ∘ f)'(t)`), then `f' t` is the derivative of `f` at `t ∈ U`. -/
theorem Norming.hasDerivAt (hφ : Norming φ) {f : ℂ → W} {U : Set ℂ} (hU : IsOpen U)
    (hb : LocBdd f U) (hd : ∀ i, DifferentiableOn ℂ (fun t => φ i (f t)) U) {f' : ℂ → W}
    (hf' : ∀ i, ∀ t ∈ U, φ i (f' t) = deriv (fun t => φ i (f t)) t) {t : ℂ} (ht : t ∈ U) :
    HasDerivAt f (f' t) t := by
  obtain ⟨r, hr, B, hB⟩ := hb t ht
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU t ht
  set ρ := min r ε / 4
  have hρ : 0 < ρ := by positivity
  have hball : ball t (4 * ρ) ⊆ ball t r ∩ U := by
    intro s hs
    rw [mem_ball] at hs
    have h1 : 4 * ρ = min r ε := by ring
    refine ⟨mem_ball.2 (hs.trans_le (h1 ▸ min_le_left _ _)),
      hεU (mem_ball.2 (hs.trans_le (h1 ▸ min_le_right _ _)))⟩
  have hrem : ∀ h : ℂ, ‖h‖ < ρ → ‖f (t + h) - f t - h • f' t‖ ≤ max B 0 / ρ ^ 2 * ‖h‖ ^ 2 := by
    intro h hh
    refine hφ.ge _ _ (by positivity) fun i => ?_
    have := norm_taylor_remainder_le (g := fun t => φ i (f t)) hρ
      ((hd i).mono fun s hs => (hball hs).2)
      (fun s hs => ((hφ.le i _).trans (hB s (hball hs).1)).trans (le_max_left B 0)) hh
    rwa [← hf' i t ht, ← (φ i).map_smul, ← (φ i).map_sub, ← (φ i).map_sub] at this
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  refine Asymptotics.IsBigO.trans_isLittleO (g := fun h : ℂ => h ^ 2) ?_
    (Asymptotics.isLittleO_pow_id (by norm_num))
  refine Asymptotics.IsBigO.of_bound (max B 0 / ρ ^ 2) ?_
  filter_upwards [ball_mem_nhds (0 : ℂ) hρ] with h hh
  rw [mem_ball_zero_iff] at hh
  rw [norm_pow]
  exact hrem h hh

theorem Norming.differentiableOn (hφ : Norming φ) {f : ℂ → W} {U : Set ℂ} (hU : IsOpen U)
    (hb : LocBdd f U) (hd : ∀ i, DifferentiableOn ℂ (fun t => φ i (f t)) U) {f' : ℂ → W}
    (hf' : ∀ i, ∀ t ∈ U, φ i (f' t) = deriv (fun t => φ i (f t)) t) :
    DifferentiableOn ℂ f U := fun _ ht =>
  (hφ.hasDerivAt hU hb hd hf' ht).differentiableAt.differentiableWithinAt

end Norming

/-! ## Compatible families -/

section KFam

variable {d L : ℕ} [NeZero L]

theorem Compat.mono_le {N M j D D' : ℕ} {K : Act d L N} {K' : Act d L M} (h : Compat j D' K K')
    (hD : D ≤ D') : Compat j D K K' :=
  fun X hX hc hd => h X hX hc (hd.trans hD)

variable (d L) in
/-- The diameter up to which the torus activities `K^N`, `K^M` (`N ≤ M`) of a family at scale
`j` are required to be compatible: `D(N, j) = L^N/8 - 2^{d+4} L^j`. -/
def Dc (N j : ℕ) : ℕ := L ^ N / 8 - 2 ^ (d + 4) * L ^ j

theorem eight_mul_Dc_le (N j : ℕ) : 8 * Dc d L N j ≤ L ^ N :=
  (Nat.mul_le_mul_left _ (Nat.sub_le _ _)).trans (Nat.mul_div_le _ _)

/-- `D(N, j + 1) ≤ D(N, j) - 2^{d+3} L^{j+1}`, so that `Knext_consist` propagates compatibility
up to `D(N, j)` at scale `j` to compatibility up to `D(N, j+1)` at scale `j + 1`. -/
theorem Dc_succ_le (hL : 2 ≤ L) (N j : ℕ) :
    Dc d L N (j + 1) ≤ Dc d L N j - 2 ^ (d + 3) * L ^ (j + 1) := by
  unfold Dc
  rw [Nat.sub_sub]
  refine Nat.sub_le_sub_left ?_ _
  have e1 : 2 ^ (d + 4) * L ^ j = 2 ^ (d + 3) * L ^ j * 2 := by ring
  have e2 : 2 ^ (d + 3) * L ^ (j + 1) = 2 ^ (d + 3) * L ^ j * L := by ring
  have e3 : 2 ^ (d + 4) * L ^ (j + 1) = 2 ^ (d + 3) * L ^ j * L * 2 := by ring
  rw [e1, e2, e3]
  have h1 : 2 ^ (d + 3) * L ^ j * 2 ≤ 2 ^ (d + 3) * L ^ j * L := Nat.mul_le_mul_left _ hL
  generalize 2 ^ (d + 3) * L ^ j = u at *
  linarith

/-- For `d ≥ 3`, `L ≥ 2^{d+3}` and `N ≥ j + 3`, the diameter `D(N, j)` is large enough for
`Knext_consist` (`2^{d+3} L^{j+1} ≤ D(N, j)`) and hence for `uVnext_consist`. -/
theorem le_Dc (hd : 3 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {N j : ℕ} (hN : j + 3 ≤ N) :
    2 ^ (d + 3) * L ^ (j + 1) ≤ Dc d L N j := by
  unfold Dc
  refine Nat.le_sub_of_add_le ((Nat.le_div_iff_mul_le (by norm_num)).2 ?_)
  have hL1 : 1 ≤ L := NeZero.one_le
  have h64 : 64 ≤ 2 ^ (d + 3) :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 6 ≤ d + 3))
  have hLN : L ^ (j + 3) ≤ L ^ N := Nat.pow_le_pow_right hL1 hN
  refine le_trans ?_ hLN
  have e : (2 ^ (d + 3) * L ^ (j + 1) + 2 ^ (d + 4) * L ^ j) * 8 =
      L ^ j * (8 * 2 ^ (d + 3) * L + 16 * 2 ^ (d + 3)) := by ring
  rw [e, pow_add L j 3]
  refine Nat.mul_le_mul_left _ ?_
  generalize 2 ^ (d + 3) = a at *
  have hL64 : 64 ≤ L := h64.trans hL
  nlinarith [Nat.mul_le_mul_left L hL, Nat.mul_le_mul_left (L * L) hL64]

/-- `Knext_consist` with the diameters `D(N, j)`: compatibility of `K^N, K^M` up to `D(N, j)`
gives compatibility of the next activities up to `D(N, j + 1)`. -/
theorem Knext_compat (hd : 3 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {N M j : ℕ} (hNM : N ≤ M)
    (hj : j + 3 ≤ N) {msq : ℝ} (hmsq : 0 ≤ msq) (V : Vcoup) {K : Act d L N} {K' : Act d L M}
    (hK : InK j K) (hK' : InK j K') (hc : Compat j (Dc d L N j) K K') :
    Compat (j + 1) (Dc d L N (j + 1))
      (Knext j (Cfrd d L N msq j) V K) (Knext j (Cfrd d L M msq j) V K') := by
  have h2L : 2 ≤ L :=
    le_trans (le_trans (by norm_num : 2 ≤ 2 ^ 1)
      (Nat.pow_le_pow_right (by norm_num) (by omega : 1 ≤ d + 3))) hL
  exact (Knext_consist hd hL hNM (by omega) hmsq V hK hK' (eight_mul_Dc_le N j)
    (le_Dc hd hL hj) hc).mono_le (Dc_succ_le h2L N j)

/-- `uVnext_consist` with the diameters `D(N, j)`. -/
theorem uVnext_compat (hd : 3 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {N M j : ℕ} (hNM : N ≤ M)
    (hj : j + 3 ≤ N) {msq : ℝ} (hmsq : 0 ≤ msq) (V : Vcoup) {K : Act d L N} {K' : Act d L M}
    (hK : InK j K) (hK' : InK j K') (hc : Compat j (Dc d L N j) K K') :
    uVnext j (Cfrd d L N msq j) V K = uVnext j (Cfrd d L M msq j) V K' := by
  refine uVnext_consist hd hL hNM (by omega) hmsq V hK hK' (hc.mono_le ?_)
  refine le_trans ?_ (le_Dc hd hL hj)
  have hL1 : 1 ≤ L := NeZero.one_le
  calc 2 ^ (d + 2) * L ^ j ≤ 2 ^ (d + 3) * L ^ j :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    _ ≤ 2 ^ (d + 3) * L ^ (j + 1) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hL1 (by omega))

variable {j : ℕ} {ℓ A : ℝ} [Fact (0 < ℓ)] [Fact (0 < A)]

/-- Pairs of compatible normalised activities, a (closed) subspace of `KSp N × KSp M`. -/
def CompatSub (j D N M : ℕ) (ℓ A : ℝ) [Fact (0 < ℓ)] [Fact (0 < A)] :
    Submodule ℂ (KSp d L j N ℓ A × KSp d L j M ℓ A) where
  carrier := {q | Compat j D q.1.toAct q.2.toAct}
  add_mem' {q q'} hq hq' X hX hc hd := by
    simp only [Prod.fst_add, Prod.snd_add, _root_.map_add, Pi.add_apply]
    rw [hq X hX hc hd, hq' X hX hc hd]
  zero_mem' X _ _ _ := by simp
  smul_mem' a q hq X hX hc hd := by
    simp only [Prod.smul_fst, Prod.smul_snd, _root_.map_smul, Pi.smul_apply]
    rw [hq X hX hc hd]

theorem isClosed_compatSub (D N M : ℕ) :
    IsClosed (CompatSub (d := d) (L := L) j D N M ℓ A :
      Set (KSp d L j N ℓ A × KSp d L j M ℓ A)) :=
  Submodule.closed_of_finiteDimensional _

/-- The index set `{N ∈ ℕ | N ≥ j + c}` of the tori in a family at scale `j`. -/
abbrev Idx (j c : ℕ) := {N : ℕ // j + c ≤ N}

variable {c : ℕ}

variable (d L) in
/-- Bounded families `(K^N)_{N ≥ j + c}` of normalised activities with the sup norm. -/
abbrev KL (j c : ℕ) (ℓ A : ℝ) [Fact (0 < ℓ)] [Fact (0 < A)] :=
  lp (fun N : Idx j c => KSp d L j N.1 ℓ A) ∞

theorem lipschitzWith_eval (N : Idx j c) :
    LipschitzWith 1 fun K : KL d L j c ℓ A => K N := by
  refine LipschitzWith.of_dist_le_mul fun K K' => ?_
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul, ← Pi.sub_apply, ← lp.coeFn_sub]
  exact lp.norm_apply_le_norm ENNReal.top_ne_zero _ N

variable (d L) in
/-- The pairwise compatible families, a closed subspace of `KL`. -/
def KFamSub (j c : ℕ) (ℓ A : ℝ) [Fact (0 < ℓ)] [Fact (0 < A)] : Submodule ℂ (KL d L j c ℓ A) where
  carrier := {K | ∀ N M : Idx j c, N.1 ≤ M.1 → (K N, K M) ∈ CompatSub j (Dc d L N.1 j) N.1 M.1 ℓ A}
  add_mem' {K K'} hK hK' N M h := by
    rw [lp.coeFn_add, Pi.add_apply, Pi.add_apply]
    exact add_mem (hK N M h) (hK' N M h)
  zero_mem' N M _ := by
    rw [lp.coeFn_zero, Pi.zero_apply, Pi.zero_apply]
    exact zero_mem _
  smul_mem' a K hK N M h := by
    rw [lp.coeFn_smul, Pi.smul_apply, Pi.smul_apply]
    exact Submodule.smul_mem _ a (hK N M h)

theorem isClosed_KFamSub : IsClosed (KFamSub d L j c ℓ A : Set (KL d L j c ℓ A)) := by
  have e : (KFamSub d L j c ℓ A : Set (KL d L j c ℓ A)) =
      ⋂ N : Idx j c, ⋂ M : Idx j c, ⋂ (_ : N.1 ≤ M.1),
        (fun K : KL d L j c ℓ A => (K N, K M)) ⁻¹'
          (CompatSub (d := d) (L := L) j (Dc d L N.1 j) N.1 M.1 ℓ A : Set _) := by
    ext K; simp [KFamSub]
  rw [e]
  exact isClosed_iInter fun N => isClosed_iInter fun M => isClosed_iInter fun _ =>
    (isClosed_compatSub _ _ _).preimage
      ((lipschitzWith_eval N).continuous.prodMk (lipschitzWith_eval M).continuous)

variable (d L) in
/-- **The space of families at scale `j`**: families `(K^N)_{N ≥ j + c}` of normalised
activities `K^N ∈ 𝒦_j(Λ_N)`, pairwise compatible (`Compat j (Dc d L N j) K^N K^M` for `N ≤ M`),
with `sup_N ‖K^N‖_j < ∞`, normed by `‖K‖ = sup_N ‖K^N‖_j`. A complex Banach space. -/
abbrev KFam (j c : ℕ) (ℓ A : ℝ) [Fact (0 < ℓ)] [Fact (0 < A)] := ↥(KFamSub d L j c ℓ A)

instance : CompleteSpace (KFam d L j c ℓ A) := isClosed_KFamSub.completeSpace_coe

namespace KFam

/-- The component of a family on `Λ_N` as an element of `KSp`. -/
def proj (N : Idx j c) : KFam d L j c ℓ A →L[ℂ] KSp d L j N.1 ℓ A :=
  LinearMap.mkContinuous
    { toFun := fun K => (K : KL d L j c ℓ A) N
      map_add' := fun K K' => by
        rw [Submodule.coe_add, lp.coeFn_add, Pi.add_apply]
      map_smul' := fun a K => by
        rw [Submodule.coe_smul, lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply] } 1
    fun K => by
      rw [one_mul]
      exact lp.norm_apply_le_norm ENNReal.top_ne_zero (K : KL d L j c ℓ A) N

/-- The activity `K^N` on `Λ_N`. -/
def act (K : KFam d L j c ℓ A) (N : Idx j c) : Act d L N.1 := (proj N K).toAct

theorem act_def (K : KFam d L j c ℓ A) (N : Idx j c) : K.act N = (proj N K).toAct := rfl

theorem act_mem (K : KFam d L j c ℓ A) (N : Idx j c) : K.act N ∈ KSub j N.1 :=
  (proj N K).toAct_mem

theorem inK (K : KFam d L j c ℓ A) (N : Idx j c) : InK j (K.act N) := (K.act_mem N).1

theorem compat (K : KFam d L j c ℓ A) {N M : Idx j c} (h : N.1 ≤ M.1) :
    Compat j (Dc d L N.1 j) (K.act N) (K.act M) := K.2 N M h

@[simp] theorem act_add (K K' : KFam d L j c ℓ A) (N : Idx j c) :
    (K + K').act N = K.act N + K'.act N := by
  simp [act_def]

@[simp] theorem act_smul (a : ℂ) (K : KFam d L j c ℓ A) (N : Idx j c) :
    (a • K).act N = a • K.act N := by
  simp [act_def]

@[simp] theorem act_zero (N : Idx j c) : (0 : KFam d L j c ℓ A).act N = 0 := by
  simp [act_def]

theorem ext {K K' : KFam d L j c ℓ A} (h : ∀ N, K.act N = K'.act N) : K = K' :=
  Subtype.ext (lp.ext (funext fun N => KSp.toAct_injective (h N)))

theorem norm_proj_le (K : KFam d L j c ℓ A) (N : Idx j c) : ‖proj N K‖ ≤ ‖K‖ :=
  lp.norm_apply_le_norm ENNReal.top_ne_zero (K : KL d L j c ℓ A) N

/-- `‖K‖ = sup_N ‖K^N‖_j`. -/
theorem norm_eq_iSup (K : KFam d L j c ℓ A) :
    ‖K‖ = ⨆ N : Idx j c, (Knorm j ℓ A (K.act N)).toReal :=
  lp.norm_eq_ciSup (K : KL d L j c ℓ A)

theorem Knorm_le (K : KFam d L j c ℓ A) (N : Idx j c) :
    (Knorm j ℓ A (K.act N)).toReal ≤ ‖K‖ := K.norm_proj_le N

theorem norm_le {K : KFam d L j c ℓ A} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ N, (Knorm j ℓ A (K.act N)).toReal ≤ M) : ‖K‖ ≤ M :=
  lp.norm_le_of_forall_le hM h

/-- Construction of a family from compatible, bounded, normalised torus activities. -/
def mk (K : ∀ N : Idx j c, Act d L N.1) (hK : ∀ N, K N ∈ KSub j N.1)
    (hc : ∀ N M : Idx j c, N.1 ≤ M.1 → Compat j (Dc d L N.1 j) (K N) (K M))
    (hb : BddAbove (Set.range fun N => (Knorm j ℓ A (K N)).toReal)) : KFam d L j c ℓ A :=
  ⟨⟨fun N => KSp.mk (K N) (hK N), memℓp_infty_iff.2 hb⟩, hc⟩

@[simp] theorem act_mk (K : ∀ N : Idx j c, Act d L N.1) (hK hc hb) (N : Idx j c) :
    (mk (ℓ := ℓ) (A := A) K hK hc hb).act N = K N := rfl

/-! ### Coefficient and pairing functionals -/

/-- The coefficient functional `K ↦ (K^N(X))_z` on `KSp`. -/
def coeffKSp {N : ℕ} (X : Finset (Lam d L N)) {n : ℕ} (z : Fin n → Sf (Lam d L N)) :
    KSp d L j N ℓ A →ₗ[ℂ] ℂ :=
  coeffL z ∘ₗ (Ev (Lam d L N)).val.toLinearMap ∘ₗ LinearMap.proj X ∘ₗ KSp.toAct

/-- The projections to the tori norm `KFam`. -/
theorem norming_proj : Norming (fun N : Idx j c => (proj N : KFam d L j c ℓ A →L[ℂ] _)) :=
  ⟨fun N K => K.norm_proj_le N, fun _ _ hM h => lp.norm_le_of_forall_le hM h⟩

end KFam

end KFam

/-! ## Holomorphic curves in `KSp` and `KFam` -/

section Holo

variable {d L : ℕ} [NeZero L] {j c : ℕ} {ℓ A : ℝ} [Fact (0 < ℓ)] [Fact (0 < A)]

/-- The derivative of a curve in a closed subspace lies in the subspace. -/
theorem deriv_mem_of_isClosed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {S : Submodule ℂ E} (hS : IsClosed (S : Set E)) {q : ℂ → E} (hq : ∀ s, q s ∈ S) (t : ℂ) :
    deriv q t ∈ S := by
  by_cases hd : DifferentiableAt ℂ q t
  · refine hS.mem_of_tendsto (hasDerivAt_iff_tendsto_slope.1 hd.hasDerivAt)
      (Eventually.of_forall fun s => ?_)
    rw [slope_def_module]
    exact S.smul_mem _ (S.sub_mem (hq s) (hq t))
  · rw [deriv_zero_of_not_differentiableAt hd]
    exact S.zero_mem

/-- All coefficients `K ↦ (K(X))_z` (`|z| ≤ |Λ_f|`), a linear injection of `KSp` into a
finite-dimensional coordinate space. -/
def KSp.coeffs {N : ℕ} : KSp d L j N ℓ A →ₗ[ℂ]
    (Finset (Lam d L N) × (Σ n : Fin (Nf (Lam d L N) + 1), Fin n → Sf (Lam d L N))) → ℂ :=
  LinearMap.pi fun q => LinearMap.proj q.2 ∘ₗ cvec ∘ₗ (Ev (Lam d L N)).val.toLinearMap ∘ₗ
    LinearMap.proj q.1 ∘ₗ KSp.toAct

theorem KSp.coeffs_injective {N : ℕ} :
    Function.Injective (KSp.coeffs : KSp d L j N ℓ A → _) := by
  intro K K' h
  refine KSp.toAct_injective (funext fun X => Subtype.ext (cvec_injective (funext fun s => ?_)))
  exact congr_fun h (X, s)

/-- A curve in `KSp` all of whose coefficients are holomorphic is holomorphic. -/
theorem KSp.differentiableOn_of_coeff {N : ℕ} {g : ℂ → KSp d L j N ℓ A} {U : Set ℂ}
    (hc : ∀ (X : Finset (Lam d L N)) (n : ℕ) (z : Fin n → Sf (Lam d L N)),
      DifferentiableOn ℂ (fun t => coeff ((g t).toAct X : Alg d L N) z) U) :
    DifferentiableOn ℂ g U := by
  obtain ⟨S, hS⟩ := LinearMap.exists_leftInverse_of_injective (KSp.coeffs (d := d) (L := L)
    (j := j) (N := N) (ℓ := ℓ) (A := A)) (LinearMap.ker_eq_bot.2 KSp.coeffs_injective)
  have hT : DifferentiableOn ℂ (fun t => KSp.coeffs (g t)) U :=
    differentiableOn_pi.2 fun q => hc q.1 q.2.1 q.2.2
  refine (LinearMap.toContinuousLinearMap S).differentiable.comp_differentiableOn hT
    |>.congr fun t _ => ?_
  exact (LinearMap.congr_fun hS (g t)).symm

/-- **Coefficientwise holomorphic, locally bounded curves in `KFam` are holomorphic.** -/
theorem KFam.differentiableOn_of_coeff {f : ℂ → KFam d L j c ℓ A} {U : Set ℂ} (hU : IsOpen U)
    (hb : LocBdd f U)
    (hc : ∀ (N : Idx j c) (X : Finset (Lam d L N.1)) (n : ℕ) (z : Fin n → Sf (Lam d L N.1)),
      DifferentiableOn ℂ (fun t => coeff ((f t).act N X : Alg d L N.1) z) U) :
    DifferentiableOn ℂ f U := by
  set g : ∀ N : Idx j c, ℂ → KSp d L j N.1 ℓ A := fun N t => KFam.proj N (f t) with hg
  have hgd : ∀ N, DifferentiableOn ℂ (g N) U := fun N =>
    KSp.differentiableOn_of_coeff fun X n z => hc N X n z
  -- the candidate derivative
  have hex : ∀ t ∈ U, ∃ w : KFam d L j c ℓ A, ∀ N, KFam.proj N w = deriv (g N) t := by
    intro t ht
    obtain ⟨r, hr, B, hB⟩ := hb t ht
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU t ht
    set ρ := min r ε / 2
    have hρ : 0 < ρ := by positivity
    have hρr : 2 * ρ = min r ε := by ring
    have hbd : ∀ N, ‖deriv (g N) t‖ ≤ B / ρ := by
      intro N
      refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ ?_ fun s hs => ?_
      · refine DifferentiableOn.diffContOnCl ((hgd N).mono ?_)
        rw [closure_ball t hρ.ne']
        intro s hs
        rw [mem_closedBall] at hs
        exact hεU (mem_ball.2 (by linarith [min_le_right r ε]))
      · rw [mem_sphere] at hs
        exact ((f s).norm_proj_le N).trans (hB s (mem_ball.2 (by linarith [min_le_left r ε])))
    have hdiff : ∀ N, DifferentiableAt ℂ (g N) t := fun N =>
      (hgd N).differentiableAt (hU.mem_nhds ht)
    refine ⟨KFam.mk (fun N => (deriv (g N) t).toAct) (fun N => KSp.toAct_mem _)
      (fun N M h => ?_) ⟨B / ρ, ?_⟩, fun N => rfl⟩
    · have hq := ((hdiff N).hasDerivAt.prodMk (hdiff M).hasDerivAt).deriv
      have := deriv_mem_of_isClosed (isClosed_compatSub (d := d) (L := L) (j := j) (ℓ := ℓ)
        (A := A) (Dc d L N.1 j) N.1 M.1) (q := fun s => (g N s, g M s))
        (fun s => (f s).2 N M h) t
      rw [hq] at this
      exact this
    · rintro _ ⟨N, rfl⟩
      exact hbd N
  classical
  set f' : ℂ → KFam d L j c ℓ A := fun t => if ht : t ∈ U then (hex t ht).choose else 0
  refine KFam.norming_proj.differentiableOn hU hb (fun N => hgd N) (f' := f') fun N t ht => ?_
  simp only [f', dif_pos ht]
  exact (hex t ht).choose_spec N

end Holo

end

end Flow
