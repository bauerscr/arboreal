module

public import ArborealDecay.Horo.MultiShift
public import ArborealDecay.Horo.ShiftFun
public import ArborealDecay.Horo.Rescale

/-!
# The horospherical change of generators (BCHS (2.73) and its Berezinian)

BCHS v2 L1551–1563 and the first step of the proof of Prop. 2.9 (L1586–1596).

Setting: vertices `Λ`; bosonic coordinates `q = (x, y) ∈ Λ ⊕ Λ → ℝ` (`ArborealDecay.Super.Pt`);
odd pairs `m ∈ M`, the pair `m` sitting at vertex `vtx m`; algebra `SG M P` (parameters `P`).
For `ℍ^{2|4}`, `M = Λ ⊕ Λ` and `vtx = Sum.elim id id` (two pairs per vertex).

The change of generators is
`x_i = sinh t_i − e^{t_i}(½ s_i² + n_i)`, `y_i = e^{t_i} s_i`, `ξ_m = e^{t_{vtx m}} ψ_m`,
`η_m = e^{t_{vtx m}} ψ̄_m`, with `n_i = ∑_{vtx m = i} ψ̄_m ψ_m` (`nV`).  In Lean the generators of
`SG M P` play the role of `ψ, ψ̄` on the horospherical side.  For a superfunction `F(x, y)` the
substituted integrand is `horoF F p = F(x_super(p), y(p), e^t ψ)`, defined as
`scaleA c_t (shiftL F (horo p))` — the Taylor expansion of `F` around `x = sinh t − ½eᵗs²` in the
nilpotent shifts `−e^{t_i} n_i(ψ) = −e^{−t_i} n_i(ξ)` followed by `ξ ↦ e^t ψ`.
The super `z` is `zSup p i = z_i(t, s) + e^{t_i} n_i` (`= cosh t + eᵗ(½s² + n)`).

**Main result** (`integral_berezin_horo`): for `F` Schwartz,
`∫ dx dy ℓ (B F) = ∫ dt ds e^{∑_i t_i − 2 ∑_m t_{vtx m}} ℓ (B (horoF F p · ∏_i zSup p i))`.
For `ℍ^{2|4}` the weight is `e^{−3 ∑ t}` (`integral_berezin_horo_H24`): this is BCHS's display
L1588–1594, `Berezinian = z e^{−3t}` per vertex.

Proof: `integral_shiftL_mul` (nilpotent shifts with Berezinian `∏(1 + ∂_x g · n)`),
`integral_horo` (bosonic Jacobian `∏ eᵗ z`), `berezin_scaleA_of_param` (`e^{−t}` per odd
generator), and `∂_x g = e^{−t}/z` (`gdS_horo`).
-/

@[expose] public section

namespace ArborealDecay.Horo

noncomputable section

open MeasureTheory Real ArborealDecay.Super

set_option linter.unusedSectionVars false

variable {Λ M P : Type*} [Fintype Λ] [DecidableEq Λ] [Fintype M] [DecidableEq M]
  [Fintype P] [DecidableEq P]
variable (vtx : M → Λ)

/-- `n_i = ∑_{vtx m = i} η_m ξ_m` (`= ∑ ψ̄ ψ` on the horospherical side). -/
def nV (i : Λ) : SG M P := ∑ m ∈ Finset.univ.filter (fun m => vtx m = i), η m * ξ m

/-- The nilpotency order used for the Taylor sums. -/
def Kord (M P : Type*) [Fintype M] [Fintype P] : ℕ := Fintype.card ((M ⊕ M) ⊕ P) + 1

/-- The rescaling `ξ_m = e^{t_{vtx m}} ψ_m`, `η_m = e^{t_{vtx m}} ψ̄_m`. -/
def cS (t : Λ → ℝ) : (M ⊕ M) ⊕ P → ℝ := expScale fun m => t (vtx m)

/-- The super `z_i = z_i(t, s) + e^{t_i} n_i`. -/
def zSup (p : Λ ⊕ Λ → ℝ) (i : Λ) : SG M P :=
  hz (p (.inl i)) (p (.inr i)) • (1 : SG M P) + exp (p (.inl i)) • nV vtx i

/-- `∏_{k ∈ l} z_k` (right to left; the factors commute). -/
def zL (p : Λ ⊕ Λ → ℝ) : List Λ → SG M P
  | [] => 1
  | k :: l => zL p l * zSup vtx p k

/-- The substituted superfunction `F(x_super, y, e^t ψ)`. -/
def horoF (F : (Λ ⊕ Λ → ℝ) → SG M P) (p : Λ ⊕ Λ → ℝ) : SG M P :=
  scaleA (cS vtx fun i => p (.inl i))
    (shiftL exV gS (nV vtx) (Kord M P) Finset.univ.toList F (horo p))

/-! ### Properties of `n_i` -/

theorem isEven_η_mul_ξ (m : M) : IsEven (η m * ξ m : SG M P) := by
  simp [IsEven, η, ξ, inv'_gen]

theorem isEven_nV (i : Λ) : IsEven (nV vtx i : SG M P) :=
  IsEven.sum _ fun m _ => isEven_η_mul_ξ m

theorem nV_comm (i : Λ) (a : SG M P) : nV vtx i * a = a * nV vtx i :=
  (isEven_nV vtx i).comm a

theorem body_nV (i : Λ) : body (nV vtx i : SG M P) = 0 := by
  simp [nV, η, ξ, gen, body_ι]

theorem nV_pow_Kord (i : Λ) : nV vtx i ^ Kord M P = (0 : SG M P) :=
  pow_card_succ_eq_zero (isEven_nV vtx i) (body_nV vtx i)

theorem scaleA_nV (t : Λ → ℝ) (i : Λ) :
    scaleA (cS vtx t) (nV vtx i : SG M P) = exp (2 * t i) • nV vtx i := by
  rw [nV, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [(Finset.mem_filter.1 hm).2.symm, map_mul, η, ξ, scaleA_gen, scaleA_gen, smul_mul_smul]
  congr 1
  simp only [cS, expScale]
  rw [← exp_add]; ring_nf

/-! ### The Berezinian factor -/

theorem gdir_exV_gS_apply (k : Λ) (q : Λ ⊕ Λ → ℝ) : gdir exV gS k q = gdS k q :=
  fderiv_gS k q

/-- Under `ξ ↦ eᵗψ`, `∏_k (1 + ∂_x g_k · n_k)` at `horo p` becomes `∏_k z_k⁻¹ · ∏_k z_super,k`. -/
theorem scaleA_berL (p : Λ ⊕ Λ → ℝ) (l : List Λ) :
    scaleA (cS vtx fun i => p (.inl i)) (berL exV gS (nV vtx) l (horo p) : SG M P) =
      (l.map fun k => (hz (p (.inl k)) (p (.inr k)))⁻¹).prod • zL vtx p l := by
  induction l with
  | nil => simp [berL, zL]
  | cons k l ih =>
    simp only [berL, zL, List.map_cons, List.prod_cons]
    rw [map_mul, ih, map_add, map_one, map_smul, scaleA_nV, gdir_exV_gS_apply, gdS_horo, zSup]
    have hz0 := (hz_pos (p (.inl k)) (p (.inr k))).ne'
    have e1 : exp (-p (.inl k)) * (hz (p (.inl k)) (p (.inr k)))⁻¹ * exp (2 * p (.inl k)) =
        (hz (p (.inl k)) (p (.inr k)))⁻¹ * exp (p (.inl k)) := by
      rw [mul_comm (exp _), mul_assoc, ← exp_add]; ring_nf
    rw [smul_smul, e1]
    set c := (l.map fun k => (hz (p (.inl k)) (p (.inr k)))⁻¹).prod
    set h := hz (p (.inl k)) (p (.inr k))
    set Z : SG M P := zL vtx p l
    set n : SG M P := nV vtx k
    simp only [mul_add, mul_one, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]
    have e2 : h⁻¹ * c * h = c := by field_simp
    rw [e2, mul_right_comm]

/-- The scalar bookkeeping: `∏ eᵗ z · e^{−2∑_m t_{vtx m}} · ∏ z⁻¹ = e^{∑ t − 2∑_m t_{vtx m}}`. -/
theorem horo_weight (p : Λ ⊕ Λ → ℝ) :
    horoDens p * (∏ m, pairScale (cS (P := P) vtx fun i => p (.inl i)) m)⁻¹ *
        ((Finset.univ : Finset Λ).toList.map fun k => (hz (p (.inl k)) (p (.inr k)))⁻¹).prod =
      exp (∑ i, p (.inl i) - 2 * ∑ m, p (.inl (vtx m))) := by
  rw [Finset.prod_map_toList, horoDens]
  have hps : ∏ m, pairScale (cS (P := P) vtx fun i => p (.inl i)) m = exp (2 * ∑ m, p (.inl (vtx m))) := by
    simp only [pairScale, cS, expScale, ← exp_add, ← exp_sum]
    congr 1; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun m _ => by ring
  rw [hps, ← exp_neg, Finset.prod_mul_distrib, ← exp_sum]
  have hz0 : ∀ i : Λ, hz (p (.inl i)) (p (.inr i)) ≠ 0 := fun i => (hz_pos _ _).ne'
  have e : (∏ i, hz (p (.inl i)) (p (.inr i))) * ∏ i, (hz (p (.inl i)) (p (.inr i)))⁻¹ = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i _ => mul_inv_cancel₀ (hz0 i)
  rw [sub_eq_add_neg, exp_add]
  set a := ∏ i, hz (p (.inl i)) (p (.inr i))
  set b := ∏ i, (hz (p (.inl i)) (p (.inr i)))⁻¹
  calc exp (∑ i, p (.inl i)) * a * exp (-(2 * ∑ m, p (.inl (vtx m)))) * b
      = exp (∑ i, p (.inl i)) * exp (-(2 * ∑ m, p (.inl (vtx m)))) * (a * b) := by ring
    _ = _ := by rw [e, mul_one]

/-- **The horospherical change of generators** (BCHS (2.73) with its Berezinian): for `F`
Schwartz,
`∫ dx dy ℓ (B F) = ∫ dt ds e^{∑_i t_i − 2∑_m t_{vtx m}} ℓ (B (F(x_super, y, eᵗψ) · ∏_i z_super,i))`. -/
theorem integral_berezin_horo {F : (Λ ⊕ Λ → ℝ) → SG M P} (hF : SSchwartz F)
    (ℓ : Module.Dual ℝ (SG M P)) :
    ∫ q, ℓ (berezin (F q)) =
      ∫ p, exp (∑ i, p (.inl i) - 2 * ∑ m, p (.inl (vtx m))) *
        ℓ (berezin (horoF vtx F p * zL vtx p (Finset.univ : Finset Λ).toList)) := by
  set l := (Finset.univ : Finset Λ).toList
  have hshift := integral_shiftL_mul (v := exV) (g := gS) (n := nV vtx) (K := Kord M P) hF
    hasTemperateGrowth_gS
    (fun k => by convert hasTemperateGrowth_gdS k using 1; funext q; exact gdir_exV_gS_apply k q)
    (nV_pow_Kord vtx) (nV_comm vtx)
    (fun j k hjk x c => by rw [gdir_exV_gS_apply, gdir_exV_gS_apply]; exact gdS_add_exV hjk x c)
    (l := l) (Finset.nodup_toList Finset.univ) (ℓ ∘ₗ berezin)
  simp only [LinearMap.coe_comp, Function.comp_apply] at hshift
  rw [← hshift, integral_horo]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  simp only [smul_eq_mul]
  set c := cS (P := P) vtx fun i => p (.inl i)
  have hc : ∀ q, c (.inr q) = 1 := fun _ => rfl
  have hB := berezin_scaleA_of_param hc
    (shiftL exV gS (nV vtx) (Kord M P) l F (horo p) * berL exV gS (nV vtx) l (horo p))
  rw [map_mul, scaleA_berL, mul_smul_comm, map_smul] at hB
  have hps : 0 < ∏ m, pairScale c m := Finset.prod_pos fun m _ => by
    simp only [pairScale, c, cS, expScale]; positivity
  have hY : berezin (shiftL exV gS (nV vtx) (Kord M P) l F (horo p) *
      berL exV gS (nV vtx) l (horo p)) =
      (∏ m, pairScale c m)⁻¹ • ((l.map fun k => (hz (p (.inl k)) (p (.inr k)))⁻¹).prod •
        berezin (horoF vtx F p * zL vtx p l)) := by
    rw [show horoF vtx F p = scaleA c (shiftL exV gS (nV vtx) (Kord M P) l F (horo p)) from rfl,
      hB, smul_smul, inv_mul_cancel₀ hps.ne', one_smul]
  rw [hY, map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_assoc, horo_weight]

/-- **`ℍ^{2|4}`** (two odd pairs per vertex): the Berezinian is `∏_i z_i e^{−3 t_i}`. -/
theorem integral_berezin_horo_H24 {F : (Λ ⊕ Λ → ℝ) → SG (Λ ⊕ Λ) P} (hF : SSchwartz F)
    (ℓ : Module.Dual ℝ (SG (Λ ⊕ Λ) P)) :
    ∫ q, ℓ (berezin (F q)) =
      ∫ p, exp (-3 * ∑ i, p (.inl i)) *
        ℓ (berezin (horoF (Sum.elim id id) F p *
          zL (Sum.elim id id) p (Finset.univ : Finset Λ).toList)) := by
  rw [integral_berezin_horo (Sum.elim id id) hF]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  simp only
  congr 2
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, id]
  ring

end

end ArborealDecay.Horo

end
