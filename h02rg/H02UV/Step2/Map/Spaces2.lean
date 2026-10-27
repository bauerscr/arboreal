import Step2.Map.Raw
import Flow.Spaces

/-!
# The normed spaces of the irrelevant coordinates (`h02uv-outline.tex`, Section
`sec:reduction`, (O1))

* `BSub j`: block families `F` at scale `j` with `InF`, translation covariance (`FamCovG`),
  lattice symmetry (`FamSym`), `J`-invariance (`FamJ`), vanishing off the `j`-blocks;
  `BSp j ℓ` is `BSub j` with the norm `‖F‖ = ‖F‖_j` (`Fnorm`).
* `ASub j`: activities with `InK2`, `KCov`, `KSym`, `KJ`, vanishing off connected polymers;
  `ASp j ℓ A` is `ASub j` with the norm `‖K‖_{j,A}` (`Knorm`).

Both are finite-dimensional complex normed spaces. They are the spaces `Y_j`, `Z_j` of the
irrelevant coordinates `x = (D, K)` of `Flow2.Hist.XP`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD ENNReal

variable {d L N : ℕ} [NeZero L]

/-! ### Block families -/

/-- The admissible block families at scale `j`. -/
def BSub (j : ℕ) : Submodule ℂ (Fam d L N) where
  carrier := {F | InF j F ∧ FamCovG j F ∧ FamSym j F ∧ FamJ F ∧
    ∀ b, b ∉ blockIdx (L := L) (N := N) j → F b = 0}
  add_mem' {F G} hF hG := by
    refine ⟨inF_add hF.1 hG.1, FlowSeq.famCovG_add hF.2.1 hG.2.1, fun T hT hP b hb => ?_,
      fun b => ?_, fun b hb => ?_⟩
    · simp only [Pi.add_apply, map_add, hF.2.2.1 T hT hP b hb, hG.2.2.1 T hT hP b hb]
    · rw [Pi.add_apply, Subalgebra.coe_add]; exact add_mem (hF.2.2.2.1 b) (hG.2.2.2.1 b)
    · simp [hF.2.2.2.2 b hb, hG.2.2.2.2 b hb]
  zero_mem' := by
    refine ⟨inF_zero j, famCovG_zero j, fun T hT hP b hb => by simp, fun b => by simp,
      fun b _ => rfl⟩
  smul_mem' c F hF := by
    refine ⟨inF_smul hF.1 c, fun t ht b hb => ?_, fun T hT hP b hb => ?_, fun b => ?_,
      fun b hb => ?_⟩
    · simp only [Pi.smul_apply, Subalgebra.coe_smul, hF.2.1 t ht b hb, map_smul]
    · simp only [Pi.smul_apply, map_smul, hF.2.2.1 T hT hP b hb]
    · rw [Pi.smul_apply, Subalgebra.coe_smul]; exact Subalgebra.smul_mem _ (hF.2.2.2.1 b) c
    · simp [hF.2.2.2.2 b hb]

variable (d L N) in
/-- Block families with the norm `‖·‖_j`. -/
def BSp (j : ℕ) (_ℓ : ℝ) : Type := BSub (d := d) (L := L) (N := N) j

variable {j : ℕ} {ℓ A : ℝ}

instance : AddCommGroup (BSp d L N j ℓ) := inferInstanceAs (AddCommGroup (BSub j))
instance : Module ℂ (BSp d L N j ℓ) := inferInstanceAs (Module ℂ (BSub j))

/-- The underlying family. -/
def BSp.toFam : BSp d L N j ℓ →ₗ[ℂ] Fam d L N := (BSub j).subtype

theorem BSp.toFam_injective : Function.Injective (BSp.toFam : BSp d L N j ℓ → Fam d L N) :=
  Subtype.val_injective

theorem BSp.mem (F : BSp d L N j ℓ) : F.toFam ∈ BSub (L := L) (N := N) j := (F : BSub j).2

instance : Norm (BSp d L N j ℓ) := ⟨fun F => (Fnorm j ℓ F.toFam).toReal⟩

theorem BSp.norm_def (F : BSp d L N j ℓ) : ‖F‖ = (Fnorm j ℓ F.toFam).toReal := rfl

theorem Fnorm_ne_top' (hℓ : 0 < ℓ) (F : Fam d L N) : Fnorm j ℓ F ≠ ⊤ := by
  have hh : (0 : ℝ) < (L : ℝ) ^ j := pow_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L))) j
  have hs : ∑ b ∈ blockIdx (L := L) (N := N) j, Tj d (L : ℝ) j ℓ (F b : Alg d L N) ≠ ⊤ :=
    sum_ne_top.2 fun b _ => tNorm_ne_top (E := Dir d) (p := pPhi d) hh hℓ _
  refine ne_top_of_le_ne_top hs (iSup₂_le fun b hb => ?_)
  exact single_le_sum (f := fun b => Tj d (L : ℝ) j ℓ (F b : Alg d L N)) (fun _ _ => zero_le) hb

theorem Fnorm_add_le' (F G : Fam d L N) : Fnorm j ℓ (F + G) ≤ Fnorm j ℓ F + Fnorm j ℓ G :=
  iSup₂_le fun b hb => (Loc.tNorm_add_le _ _).trans
    (add_le_add (Tj_le_Fnorm F hb) (Tj_le_Fnorm G hb))

theorem Fnorm_smul' (c : ℂ) (F : Fam d L N) : Fnorm j ℓ (c • F) = ENNReal.ofReal ‖c‖ * Fnorm j ℓ F :=
  Fnorm_smul j ℓ c F

theorem BSp.normedSpaceCore [Fact (0 < ℓ)] : NormedSpace.Core ℂ (BSp d L N j ℓ) where
  norm_nonneg _ := toReal_nonneg
  norm_smul c F := by
    rw [BSp.norm_def, BSp.norm_def, map_smul, Fnorm_smul', toReal_mul, toReal_ofReal (norm_nonneg _)]
  norm_triangle F G := by
    rw [BSp.norm_def, BSp.norm_def, BSp.norm_def, map_add,
      ← toReal_add (Fnorm_ne_top' Fact.out _) (Fnorm_ne_top' Fact.out _)]
    exact toReal_mono (add_ne_top.2 ⟨Fnorm_ne_top' Fact.out _, Fnorm_ne_top' Fact.out _⟩)
      (Fnorm_add_le' _ _)
  norm_eq_zero_iff F := by
    have hh : (0 : ℝ) < (L : ℝ) ^ j :=
      pow_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L))) j
    refine ⟨fun h0 => ?_, fun h0 => ?_⟩
    · rw [BSp.norm_def, toReal_eq_zero_iff] at h0
      rcases h0 with h0 | h0
      · refine BSp.toFam_injective ?_
        rw [map_zero]
        funext b
        by_cases hb : b ∈ blockIdx (L := L) (N := N) j
        · have h1 := Tj_le_Fnorm (ℓ := ℓ) F.toFam hb
          rw [h0, nonpos_iff_eq_zero] at h1
          exact Subtype.ext ((Flow.tNorm_eq_zero_iff hh Fact.out).1 h1)
        · exact F.mem.2.2.2.2 b hb
      · exact absurd h0 (Fnorm_ne_top' Fact.out _)
    · rw [h0, BSp.norm_def, map_zero, toReal_eq_zero_iff]
      left
      refine le_antisymm (iSup₂_le fun b _ => ?_) bot_le
      simp [Flow.tNorm_zero]

variable [Fact (0 < ℓ)]

instance : NormedAddCommGroup (BSp d L N j ℓ) := NormedAddCommGroup.ofCore BSp.normedSpaceCore
instance : NormedSpace ℂ (BSp d L N j ℓ) := NormedSpace.ofCore BSp.normedSpaceCore

instance : FiniteDimensional ℂ (BSp d L N j ℓ) := by
  have : FiniteDimensional ℂ (EvR (Lam d L N)) :=
    Module.Finite.of_injective (Ev (Lam d L N)).val.toLinearMap Subtype.val_injective
  have : FiniteDimensional ℂ (blockIdx (d := d) (L := L) (N := N) j → EvR (Lam d L N)) := inferInstance
  -- restriction to the `j`-blocks is injective on `BSub j`
  let r : BSp d L N j ℓ →ₗ[ℂ] (blockIdx (d := d) (L := L) (N := N) j → EvR (Lam d L N)) :=
    { toFun := fun F b => F.toFam b
      map_add' := fun F G => by funext b; simp
      map_smul' := fun c F => by funext b; simp }
  refine Module.Finite.of_injective r fun F G h => BSp.toFam_injective (funext fun b => ?_)
  by_cases hb : b ∈ blockIdx (L := L) (N := N) j
  · exact congrFun h ⟨b, hb⟩
  · rw [F.mem.2.2.2.2 b hb, G.mem.2.2.2.2 b hb]

theorem BSp.Fnorm_le (F : BSp d L N j ℓ) : Fnorm j ℓ F.toFam = ENNReal.ofReal ‖F‖ := by
  rw [BSp.norm_def, ofReal_toReal (Fnorm_ne_top' Fact.out _)]

/-! ### Activities -/

/-- The admissible activities at scale `j`. -/
def ASub (j : ℕ) : Submodule ℂ (Act d L N) where
  carrier := {K | InK2 j K ∧ KCov j K ∧ KSym j K ∧ KJ j K ∧ ∀ X, ¬ IsConn j X → K X = 0}
  add_mem' {K K'} hK hK' := by
    refine ⟨hK.1.add hK'.1, fun t ht X => ?_, fun T hT hP X => ?_, fun X hX => ?_, fun X hX => ?_⟩
    · simp only [Pi.add_apply, Subalgebra.coe_add, hK.2.1 t ht X, hK'.2.1 t ht X, map_add]
    · simp only [Pi.add_apply, map_add, hK.2.2.1 T hT hP X, hK'.2.2.1 T hT hP X]
    · rw [Pi.add_apply, Subalgebra.coe_add]; exact add_mem (hK.2.2.2.1 X hX) (hK'.2.2.2.1 X hX)
    · simp [hK.2.2.2.2 X hX, hK'.2.2.2.2 X hX]
  zero_mem' := by
    refine ⟨⟨fun X _ => zero_mem _, fun X _ n z _ => by simp⟩, fun t _ X => by simp,
      fun T _ _ X => by simp, fun X _ => by simp, fun X _ => rfl⟩
  smul_mem' c K hK := by
    refine ⟨hK.1.smul c, fun t ht X => ?_, fun T hT hP X => ?_, fun X hX => ?_, fun X hX => ?_⟩
    · simp only [Pi.smul_apply, Subalgebra.coe_smul, hK.2.1 t ht X, map_smul]
    · simp only [Pi.smul_apply, map_smul, hK.2.2.1 T hT hP X]
    · rw [Pi.smul_apply, Subalgebra.coe_smul]; exact Subalgebra.smul_mem _ (hK.2.2.2.1 X hX) c
    · simp [hK.2.2.2.2 X hX]

variable (d L N) in
/-- Activities with the norm `‖·‖_{j,A}`. -/
def ASp (j : ℕ) (_ℓ _A : ℝ) : Type := ASub (d := d) (L := L) (N := N) j

instance : AddCommGroup (ASp d L N j ℓ A) := inferInstanceAs (AddCommGroup (ASub j))
instance : Module ℂ (ASp d L N j ℓ A) := inferInstanceAs (Module ℂ (ASub j))

/-- The underlying activity. -/
def ASp.toAct : ASp d L N j ℓ A →ₗ[ℂ] Act d L N := (ASub j).subtype

theorem ASp.toAct_injective : Function.Injective (ASp.toAct : ASp d L N j ℓ A → Act d L N) :=
  Subtype.val_injective

theorem ASp.mem (K : ASp d L N j ℓ A) : K.toAct ∈ ASub (L := L) (N := N) j := (K : ASub j).2

instance : Norm (ASp d L N j ℓ A) := ⟨fun K => (Knorm j ℓ A K.toAct).toReal⟩

theorem ASp.norm_def (K : ASp d L N j ℓ A) : ‖K‖ = (Knorm j ℓ A K.toAct).toReal := rfl

theorem ASp.normedSpaceCore [Fact (0 < ℓ)] [Fact (0 < A)] : NormedSpace.Core ℂ (ASp d L N j ℓ A) where
  norm_nonneg _ := toReal_nonneg
  norm_smul c K := by
    rw [ASp.norm_def, ASp.norm_def, map_smul, Knorm_smul, toReal_mul, toReal_ofReal (norm_nonneg _)]
  norm_triangle K K' := by
    rw [ASp.norm_def, ASp.norm_def, ASp.norm_def, map_add,
      ← toReal_add (Knorm_ne_top Fact.out _) (Knorm_ne_top Fact.out _)]
    exact toReal_mono (add_ne_top.2 ⟨Knorm_ne_top Fact.out _, Knorm_ne_top Fact.out _⟩)
      (Knorm_add_le _ _ _ _ _)
  norm_eq_zero_iff K := by
    have hh : (0 : ℝ) < (L : ℝ) ^ j :=
      pow_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L))) j
    refine ⟨fun h0 => ?_, fun h0 => ?_⟩
    · rw [ASp.norm_def, toReal_eq_zero_iff] at h0
      rcases h0 with h0 | h0
      · refine ASp.toAct_injective ?_
        rw [map_zero]
        funext X
        by_cases hX : IsConn j X
        · have h1 := wnorm_le_Knorm (ℓ := ℓ) (A := A) (K := K.toAct) hX
          rw [h0, nonpos_iff_eq_zero, wnorm, mul_eq_zero, ENNReal.ofReal_eq_zero] at h1
          rcases h1 with h1 | h1
          · exact absurd h1 (not_le.2 (by have : (0 : ℝ) < A := Fact.out; positivity))
          · exact Subtype.ext ((Flow.tNorm_eq_zero_iff hh Fact.out).1 h1)
        · exact K.mem.2.2.2.2 X hX
      · exact absurd h0 (Knorm_ne_top Fact.out _)
    · rw [h0, ASp.norm_def, map_zero, Knorm, toReal_eq_zero_iff]
      left
      refine le_antisymm (iSup₂_le fun X _ => ?_) bot_le
      simp [Flow.tNorm_zero]

section

variable [Fact (0 < ℓ)] [Fact (0 < A)]

instance : NormedAddCommGroup (ASp d L N j ℓ A) := NormedAddCommGroup.ofCore ASp.normedSpaceCore
instance : NormedSpace ℂ (ASp d L N j ℓ A) := NormedSpace.ofCore ASp.normedSpaceCore

instance : FiniteDimensional ℂ (ASp d L N j ℓ A) := by
  have : FiniteDimensional ℂ (Act d L N) := inferInstance
  exact Module.Finite.of_injective (ASp.toAct (j := j) (ℓ := ℓ) (A := A)) ASp.toAct_injective

theorem ASp.Knorm_eq (K : ASp d L N j ℓ A) : Knorm j ℓ A K.toAct = ENNReal.ofReal ‖K‖ := by
  rw [ASp.norm_def, ofReal_toReal (Knorm_ne_top Fact.out _)]

end

end

end Step2
