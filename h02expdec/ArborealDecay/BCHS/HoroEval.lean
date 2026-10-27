module

public import ArborealDecay.BCHS.HoroAlg
public import ArborealDecay.BCHS.Transport
public import ArborealDecay.BCHS.Regular
public import ArborealDecay.Horo.TSide

/-!
# The `ℍ^{2|4}` observables in horospherical coordinates (R1 applied)

In the two-flavour algebra `B Λ = SG (Λ ⊕ Λ) Empty` (`Transport.lean`), with one vertex map
`vt Λ = Sum.elim id id` (two odd pairs per vertex), the horospherical substitution `horoF` of the
transported `ℍ^{2|4}` objects (`T = toA.symm`) is computed in terms of the horospherical data
`hd p` of `ArborealDecay.Horo.HData` (BCHS (2.73)):

* `horoF_Rz`: `R_i ↦ z_i²`; `horoF_zH`: `z_i ↦ z_i = cosh t_i + e^{t_i}(½ s_i² + n_i)` (square-root
  uniqueness for even elements with positive body);
* `horoF_zinv`: `z_i⁻¹ ↦ z_i⁻¹`; `horoF_dotH`: `u_i · u_j ↦ (hd p).udot i j`;
* `horoF_actionH`: the action.
-/

@[expose] public section

namespace ArborealDecay.BCHS

noncomputable section

open Finset ArborealDecay.Super ArborealDecay.Super.H24 ArborealDecay.Horo Grassmann
open scoped ContDiff

set_option linter.unusedSectionVars false

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- The vertex map of the two-flavour model: the pairs `inl i`, `inr i` sit at `i`. -/
def vt (Λ : Type*) : Λ ⊕ Λ → Λ := Sum.elim id id

/-- The flavour `γ` pair at vertex `i`: `true ↦ inl i` (`ξ¹`), `false ↦ inr i` (`ξ²`). -/
def mf : Bool → Λ → Λ ⊕ Λ
  | true, i => .inl i
  | false, i => .inr i

@[simp] theorem vt_mf (γ : Bool) (i : Λ) : vt Λ (mf γ i) = i := by cases γ <;> rfl

/-- The transport `H24.A Λ → B Λ`. -/
abbrev T : H24.A Λ ≃ₐ[ℝ] B Λ := (toA (Λ := Λ)).symm

@[simp] theorem T_ξ1 (i : Λ) : T (ξ1 i) = (ξ (.inl i) : B Λ) := by
  rw [← toA_ξ_inl]; exact toA.symm_apply_apply _
@[simp] theorem T_η1 (i : Λ) : T (η1 i) = (η (.inl i) : B Λ) := by
  rw [← toA_η_inl]; exact toA.symm_apply_apply _
@[simp] theorem T_ξ (i : Λ) : T (ξ i : H24.A Λ) = (ξ (.inr i) : B Λ) := by
  rw [← toA_ξ_inr]; exact toA.symm_apply_apply _
@[simp] theorem T_η (i : Λ) : T (η i : H24.A Λ) = (η (.inr i) : B Λ) := by
  rw [← toA_η_inr]; exact toA.symm_apply_apply _

theorem body_T (x : H24.A Λ) : body (T x) = body x := body_toA_symm x

theorem isEven_T {x : H24.A Λ} (hx : IsEven x) : IsEven (T x) := by
  unfold IsEven at *
  conv_rhs => rw [← hx]
  change inv' (relabel eA.symm x) = relabel eA.symm (inv' x)
  exact inv'_relabel _ x

theorem T_scomp (g : ℝ → ℝ) {a : H24.A Λ} (ha : IsEven a) : T (scomp g a) = scomp g (T a) :=
  map_scomp (T (Λ := Λ)).toAlgHom (fun x => body_T x) g (isNilpotent_soul ha)

/-! ### Smoothness -/

theorem STG.sSmooth {O : Type*} [Fintype O] [DecidableEq O] {F : Pt Λ → Gr O} (hF : STG F) :
    SSmooth F := fun ℓ => (hF ℓ).1

theorem SSmooth.mapT {F : Pt Λ → H24.A Λ} (hF : SSmooth F) : SSmooth fun p => T (F p) :=
  fun ℓ => hF (ℓ ∘ₗ (T (Λ := Λ)).toAlgHom.toLinearMap)

/-! ### Horospherical data -/

/-- The horospherical data at `p = (t, s)`: `ψ^γ_i = ξ_{mf γ i}`, `ψ̄^γ_i = η_{mf γ i}`. -/
def hd (p : Pt Λ) : HData Λ Bool ((((Λ ⊕ Λ) ⊕ (Λ ⊕ Λ)) ⊕ Empty) → ℝ) where
  t i := p (.inl i)
  s i := p (.inr i)
  vψ γ i := Pi.single (.inl (.inl (mf γ i))) 1
  vψb γ i := Pi.single (.inl (.inr (mf γ i))) 1

@[simp] theorem hd_ψ (p : Pt Λ) (γ : Bool) (i : Λ) : (hd p).ψ γ i = (ξ (mf γ i) : B Λ) := rfl
@[simp] theorem hd_ψb (p : Pt Λ) (γ : Bool) (i : Λ) : (hd p).ψb γ i = (η (mf γ i) : B Λ) := rfl

theorem filter_vt (i : Λ) :
    (Finset.univ.filter fun m : Λ ⊕ Λ => vt Λ m = i) = {.inl i, .inr i} := by
  ext m; rcases m with j | j <;> simp [vt, eq_comm]

theorem nV_eq (p : Pt Λ) (i : Λ) : (nV (vt Λ) i : B Λ) = (hd p).nn i := by
  rw [nV, filter_vt, sum_pair (by simp), HData.nn, Fintype.sum_bool]
  rfl

theorem zSup_eq (p : Pt Λ) (i : Λ) : (zSup (vt Λ) p i : B Λ) = (hd p).zS i := by
  rw [zSup, nV_eq p]; rfl

/-- The coordinate `x_i` as a superfunction. -/
def Xc (i : Λ) (q : Pt Λ) : B Λ := q (.inl i) • (1 : B Λ)
/-- The coordinate `y_i` as a superfunction. -/
def Yc (i : Λ) (q : Pt Λ) : B Λ := q (.inr i) • (1 : B Λ)

theorem sSmooth_Xc (i : Λ) : SSmooth (Xc i : Pt Λ → B Λ) := sSmooth_coord _
theorem sSmooth_Yc (i : Λ) : SSmooth (Yc i : Pt Λ → B Λ) := sSmooth_coord _

theorem horoF_Xc (p : Pt Λ) (i : Λ) : horoF (vt Λ) (Xc i) p = (hd p).xS i := by
  rw [show Xc i = fun q : Pt Λ => q (.inl i) • (1 : B Λ) from rfl, horoF_x, nV_eq p]; rfl

theorem horoF_Yc (p : Pt Λ) (i : Λ) : horoF (vt Λ) (Yc i) p = (hd p).yS i := by
  rw [show Yc i = fun q : Pt Λ => q (.inr i) • (1 : B Λ) from rfl, horoF_y]; rfl

theorem scaleA_ξ (p : Pt Λ) (γ : Bool) (i : Λ) :
    scaleA (cS (vt Λ) fun i => p (.inl i)) (ξ (mf γ i) : B Λ) = (hd p).ξS γ i := by
  rw [ξ, scaleA_gen]
  simp only [cS, expScale, vt_mf]
  rfl

theorem scaleA_η (p : Pt Λ) (γ : Bool) (i : Λ) :
    scaleA (cS (vt Λ) fun i => p (.inl i)) (η (mf γ i) : B Λ) = (hd p).ηS γ i := by
  rw [η, scaleA_gen]
  simp only [cS, expScale, vt_mf]
  rfl

/-! ### `R_i` and `z_i` -/

theorem T_Rz (i : Λ) (q : Pt Λ) :
    T (Rz i q) = 1 + Xc i q * Xc i q + Yc i q * Yc i q -
      (2 : ℝ) • ∑ γ, (ξ (mf γ i) * η (mf γ i) : B Λ) := by
  simp only [Rz, map_sub, map_smul, map_mul, map_one, T_ξ1, T_η1, T_ξ, T_η, Xc, Yc,
    Fintype.sum_bool, mf, smul_add, smul_mul_smul, one_mul]
  rw [add_smul, add_smul, one_smul]
  module

theorem sSmooth_TRz (i : Λ) : SSmooth fun q => T (Rz i q) := (stg_Rz i).sSmooth.mapT

theorem horoF_Rz (p : Pt Λ) (i : Λ) :
    horoF (vt Λ) (fun q => T (Rz i q)) p = (hd p).zS i * (hd p).zS i := by
  have e : (fun q => T (Rz i q)) = fun q => ((fun _ => (1 : B Λ)) q + Xc i q * Xc i q +
      Yc i q * Yc i q) - (fun _ => (2 : ℝ) • ∑ γ, (ξ (mf γ i) * η (mf γ i) : B Λ)) q :=
    funext (T_Rz i)
  have hX := sSmooth_Xc (Λ := Λ) i
  have hY := sSmooth_Yc (Λ := Λ) i
  rw [e, horoF_sub _ (((SSmooth.const _).add (hX.mul hX)).add (hY.mul hY)) (SSmooth.const _),
    horoF_add _ ((SSmooth.const _).add (hX.mul hX)) (hY.mul hY),
    horoF_add _ (SSmooth.const _) (hX.mul hX), horoF_mul _ hX hX, horoF_mul _ hY hY,
    horoF_const, horoF_const, horoF_Xc, horoF_Yc, map_one, map_smul, map_sum, HData.zS_sq]
  simp only [map_mul, scaleA_ξ, scaleA_η]

theorem isEven_zS (p : Pt Λ) (i : Λ) : IsEven ((hd p).zS i) := by
  have : (hd p).zS i = zSup (vt Λ) p i := (zSup_eq p i).symm
  rw [this, zSup]
  exact (IsEven.one.smul _).add ((isEven_nV _ i).smul _)

theorem body_zS (p : Pt Λ) (i : Λ) : body ((hd p).zS i) = hz (p (.inl i)) (p (.inr i)) := by
  have : (hd p).zS i = zSup (vt Λ) p i := (zSup_eq p i).symm
  rw [this, zSup, map_add, map_smul, map_smul, body_nV]
  simp

theorem sSmooth_TzH (i : Λ) : SSmooth fun q => T (zH i q) := (stg_zH i).sSmooth.mapT

theorem isEven_TzH (i : Λ) (q : Pt Λ) : IsEven (T (zH i q)) := isEven_T (isEven_zH i q)

theorem horoF_zH (p : Pt Λ) (i : Λ) : horoF (vt Λ) (fun q => T (zH i q)) p = (hd p).zS i := by
  have h2 : horoF (vt Λ) (fun q => T (zH i q)) p * horoF (vt Λ) (fun q => T (zH i q)) p =
      (hd p).zS i * (hd p).zS i := by
    rw [← horoF_mul _ (sSmooth_TzH i) (sSmooth_TzH i), ← horoF_Rz p i]
    congr 1; funext q; rw [← map_mul, zH_mul_self]
  refine eq_of_sq_eq_of_body_pos (isEven_horoF _ (sSmooth_TzH i) (isEven_TzH i) p)
    (isEven_zS p i) ?_ ?_ h2
  · rw [body_horoF, body_T]; exact body_zH_pos i _
  · rw [body_zS]; exact hz_pos _ _

theorem T_zinv (i : Λ) (q : Pt Λ) :
    T (Ring.inverse (zH i q)) = scomp (fun t : ℝ => t⁻¹) (T (zH i q)) := by
  rw [inverse_zH, T_scomp _ (isEven_zH i q)]

theorem horoF_zinv (p : Pt Λ) (i : Λ) :
    horoF (vt Λ) (fun q => T (Ring.inverse (zH i q))) p = Ring.inverse ((hd p).zS i) := by
  rw [funext (T_zinv (Λ := Λ) i), horoF_scomp _ isOpen_Ioi contDiffOn_inv (sSmooth_TzH i)
    (isEven_TzH i) (fun y => by rw [body_T]; exact body_zH_pos i y), horoF_zH,
    inverse_eq_scomp_inv (isNilpotent_soul (isEven_zS p i))]
  rw [body_zS]; exact (hz_pos _ _).ne'

/-! ### Inner products -/

theorem T_dotH (i j : Λ) (q : Pt Λ) :
    T (dotH i j q) = Xc i q * Xc j q + Yc i q * Yc j q +
      ∑ γ, (η (mf γ i) * ξ (mf γ j) - ξ (mf γ i) * η (mf γ j) : B Λ) -
        T (zH i q) * T (zH j q) := by
  simp only [dotH, map_sub, map_add, map_smul, map_mul, map_one, T_ξ1, T_η1, T_ξ, T_η, Xc, Yc,
    Fintype.sum_bool, mf, smul_mul_smul, one_mul]
  rw [add_smul]
  abel

theorem sSmooth_TdotH (i j : Λ) : SSmooth fun q => T (dotH i j q) := (stg_dotH i j).sSmooth.mapT

theorem horoF_dotH (p : Pt Λ) (i j : Λ) :
    horoF (vt Λ) (fun q => T (dotH i j q)) p = (hd p).udot i j := by
  have hX := sSmooth_Xc (Λ := Λ)
  have hY := sSmooth_Yc (Λ := Λ)
  have hc := SSmooth.const (Y := Pt Λ)
    (∑ γ, (η (mf γ i) * ξ (mf γ j) - ξ (mf γ i) * η (mf γ j) : B Λ))
  have e : (fun q => T (dotH i j q)) = fun q => (Xc i q * Xc j q + Yc i q * Yc j q +
      (fun _ => ∑ γ, (η (mf γ i) * ξ (mf γ j) - ξ (mf γ i) * η (mf γ j) : B Λ)) q) -
        T (zH i q) * T (zH j q) := funext (T_dotH i j)
  rw [e, horoF_sub _ ((((hX i).mul (hX j)).add ((hY i).mul (hY j))).add hc)
      ((sSmooth_TzH i).mul (sSmooth_TzH j)),
    horoF_add _ (((hX i).mul (hX j)).add ((hY i).mul (hY j))) hc,
    horoF_add _ ((hX i).mul (hX j)) ((hY i).mul (hY j)), horoF_mul _ (hX i) (hX j),
    horoF_mul _ (hY i) (hY j), horoF_mul _ (sSmooth_TzH i) (sSmooth_TzH j), horoF_const,
    horoF_Xc, horoF_Xc, horoF_Yc, horoF_Yc, horoF_zH, horoF_zH, HData.udot, map_sum]
  simp only [map_sub, map_mul, scaleA_ξ, scaleA_η]

/-! ### The action -/

theorem T_actionH (β : Λ → Λ → ℝ) (h : Λ → ℝ) (q : Pt Λ) :
    T (actionH β h q) = (1 / 4 : ℝ) • ∑ i, ∑ j, β i j • (T (dotH i i q) - T (dotH i j q) -
      T (dotH j i q) + T (dotH j j q)) + ∑ i, h i • (T (zH i q) - 1) := by
  simp only [actionH, map_add, map_smul, map_sum, map_sub, map_one]

theorem horoF_actionH (β : Λ → Λ → ℝ) (h : Λ → ℝ) (p : Pt Λ) :
    horoF (vt Λ) (fun q => T (actionH β h q)) p =
      (1 / 4 : ℝ) • ∑ i, ∑ j, β i j • ((hd p).udot i i - (hd p).udot i j -
        (hd p).udot j i + (hd p).udot j j) + ∑ i, h i • ((hd p).zS i - 1) := by
  have hD := sSmooth_TdotH (Λ := Λ)
  have hDD : ∀ i j, SSmooth fun q => T (dotH i i q) - T (dotH i j q) - T (dotH j i q) +
      T (dotH j j q) := fun i j => (((hD i i).sub (hD i j)).sub (hD j i)).add (hD j j)
  have hZ : ∀ i, SSmooth fun q => T (zH i q) - 1 :=
    fun i => (sSmooth_TzH i).sub (SSmooth.const (1 : B Λ))
  have hS1 : SSmooth fun q => ∑ i, ∑ j, β i j • (T (dotH i i q) - T (dotH i j q) -
      T (dotH j i q) + T (dotH j j q)) :=
    SSmooth.sum _ fun i _ => SSmooth.sum _ fun j _ => (hDD i j).smul contDiff_const
  have hS2 : SSmooth fun q => ∑ i, h i • (T (zH i q) - 1) :=
    SSmooth.sum _ fun i _ => (hZ i).smul contDiff_const
  rw [funext (T_actionH (Λ := Λ) β h), horoF_add _ (hS1.smul contDiff_const) hS2,
    horoF_smul _ _ hS1, horoF_sum _ _ fun i _ => SSmooth.sum _ fun j _ =>
      (hDD i j).smul contDiff_const,
    horoF_sum _ _ fun i _ => (hZ i).smul contDiff_const]
  refine congrArg₂ (· + ·) (congrArg _ (sum_congr rfl fun i _ => ?_))
    (sum_congr rfl fun i _ => ?_)
  · rw [horoF_sum _ _ fun j _ => (hDD i j).smul contDiff_const]
    refine sum_congr rfl fun j _ => ?_
    rw [horoF_smul _ _ (hDD i j), horoF_add _ (((hD i i).sub (hD i j)).sub (hD j i)) (hD j j),
      horoF_sub _ ((hD i i).sub (hD i j)) (hD j i), horoF_sub _ (hD i i) (hD i j),
      horoF_dotH, horoF_dotH, horoF_dotH, horoF_dotH]
  · rw [horoF_smul _ _ (hZ i), horoF_sub _ (sSmooth_TzH i) (SSmooth.const (1 : B Λ)), horoF_zH,
      horoF_const, map_one]

end

end ArborealDecay.BCHS

end
