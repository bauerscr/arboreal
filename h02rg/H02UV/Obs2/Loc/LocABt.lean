import Obs2.Loc.LocWeight
import Obs2.Loc.LocContract

/-!
# The two-point localisation `loc^{ab}` in `d = 2`: barycentric substitution

In `d = 2` every `U(1)`-invariant derivative-free monomial at `a, b` is marginal, so the image of
`loc^{ab}` should contain `1`, `ψ̄_uψ_v` (`u, v ∈ {a, b}`) and `ψ̄_aψ_aψ̄_bψ_b`.
`Obs2.locAB2` does this with a *sharp* region `R_a` (`ψ_x ↦ ψ_{ρ(x)}`); that operator is not
bounded uniformly in `j` (a gradient `ψ̄_xψ_y - ψ̄_{x'}ψ_y` across `∂R_a` has `T_j`-norm
`O(L^{-j})` but is mapped to `(ψ̄_a - ψ̄_b)ψ_{ρ y}`, of norm `O(|a-b| L^{-j})`).

Here the sharp region is replaced by the **barycentric (linear) weight**
`t(x) = ⟨x̂ - â, e⟩ / |e|²`, `e = b̂ - â` (`x̂ = r(x - x_X)` the coordinates relative to the base
point `x_X` of `X`), i.e. the substitution `ψ_x ↦ ψ_a + t(x) (ψ_b - ψ_a)` (`t(a) = 0`,
`t(b) = 1`). With `δ = ψ_b - ψ_a`, `δ̄ = ψ̄_b - ψ̄_a`, on `U(1)`-invariant `F`:

`loc^{ab,t}_X F = ε(F) + M_{00} ψ̄_aψ_a + M_{10} δ̄ψ_a + M_{01} ψ̄_aδ + M_{11} δ̄δ + M_4 ψ̄_aψ_aδ̄δ`

with `M_{kl} = ∑_{x,y} F_{(x,-)(y,+)} t(x)^k t(y)^l` and
`M_4 = ∑ F_{(x_0,-)(x_1,+)(x_2,-)(x_3,+)} t(x_0) t(x_1)` (`ψ̄_aψ_aδ̄δ = ψ̄_aψ_aψ̄_bψ_b`). In Lean:
`locABt X a b F = locEven {a} X X F + Dt X a b F` (`locEven {a} X X F = ε(F) + M_{00} ψ̄_aψ_a`
for `a ∈ X`).

The point: `t` has gradient `|e|^{-1}`, so `|M_{10}| ≲ L^j |e|^{-1} ℓ^{-2} ‖F‖_{T_j(ℓ)}`, while
`‖δ‖_{T_h(ℓ')} ≤ ℓ' |e|_1 / h`; the products are `O(L^j/h)` uniformly in `|e|`
(`tNorm_Dt_le`). Hence (for `a ∈ X`, `X` small, `b` arbitrary, `ℓ' ≤ 2ℓ`):

* `exists_locABt_bound`: `‖loc^{ab,t}_X F‖_{T_j(ℓ')} ≤ C ‖F‖_{T_j(ℓ)}`;
* `exists_locABt_contract`: `‖F - loc^{ab,t}_X F‖_{T_{j+1}(ℓ')} ≤ C L^{-1} ‖F‖_{T_j(ℓ)}`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann FRD Loc Obs.LocObs

variable {d L N : ℕ} [NeZero L]

/-! ### The barycentric weight -/

section Weight

variable (X : Finset (Lam d L N)) (a b : Lam d L N)

/-- `e = r(b - x_X) - r(a - x_X)`. -/
def eV (i : Fin d) : ℝ := lift (base X) b i - lift (base X) a i

/-- `|e|² = ∑ e_i²`. -/
def eN2 : ℝ := ∑ i, eV X a b i ^ 2

/-- `|e|_1 = ∑ |e_i|`. -/
def eN1 : ℝ := ∑ i, |eV X a b i|

/-- The barycentric weight `t(x) = ⟨x̂ - â, e⟩/|e|²`. -/
def tW (x : Lam d L N) : ℝ :=
  (eN2 X a b)⁻¹ * ∑ i, eV X a b i * (lift (base X) x i - lift (base X) a i)

theorem tW_a : tW X a b a = 0 := by simp [tW]

theorem tW_b (hab : eN2 X a b ≠ 0) : tW X a b b = 1 := by
  unfold tW
  rw [show (∑ i, eV X a b i * (lift (base X) b i - lift (base X) a i)) = eN2 X a b by
    unfold eN2 eV; exact sum_congr rfl fun i _ => by ring]
  exact inv_mul_cancel₀ hab

/-- The cut-off weight in coordinates relative to the base point. -/
def tCut (R : ℝ) (u : Zd d) : ℝ :=
  (eN2 X a b)⁻¹ * ∑ i, eV X a b i *
    (cutP (Pi.single i 1) R u - lift (base X) a i * cutP 0 R u)

theorem eN2_nonneg : 0 ≤ eN2 X a b := sum_nonneg fun _ _ => sq_nonneg _

theorem eN1_nonneg : 0 ≤ eN1 X a b := sum_nonneg fun _ _ => abs_nonneg _

/-- `|e|_1² ≤ d |e|²`. -/
theorem eN1_sq_le : eN1 X a b ^ 2 ≤ d * eN2 X a b := by
  have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin d))) (f := fun i => |eV X a b i|)
  simpa [eN1, eN2, sq_abs] using this

/-- `|e|_1² / |e|² ≤ d`. -/
theorem eN1_sq_div_le : eN1 X a b ^ 2 * (eN2 X a b)⁻¹ ≤ d := by
  rcases (eN2_nonneg X a b).eq_or_lt with h | h
  · rw [← h, inv_zero, mul_zero]; positivity
  · rw [← div_eq_mul_inv, div_le_iff₀ h]; exact eN1_sq_le X a b

theorem tCut_eq {R : ℝ} (hR : 0 < R) {x : Lam d L N}
    (hx : (supNormZ (rep (x - base X)) : ℝ) ≤ R) :
    tCut X a b R (rep (x - base X)) = tW X a b x := by
  unfold tCut tW
  congr 1
  refine sum_congr rfl fun i _ => ?_
  rw [cutP_single_eq hR i hx, cutP_zero_eq hR hx, mul_one]
  rfl

theorem tCut_far {R : ℝ} (hR : 0 < R) {u : Zd d} (hu : 2 * R ≤ (supNormZ u : ℝ)) :
    tCut X a b R u = 0 := by
  simp [tCut, cutP_eq_zero _ hR hu]

end Weight

/-! ### Coordinates of points of `X^□` -/

theorem abs_lift_le {j : ℕ} {X : Finset (Lam d L N)} (hX : IsSmall j X) {y : Lam d L N}
    (hy : y ∈ nbhd j X) (i : Fin d) : |lift (base X) y i| ≤ (rad d L j : ℝ) := by
  have h1 := supNorm_nbhd_base hX hy
  have h2 := natAbs_le_supNormZ (rep (y - base X)) i
  rw [supNormZ_rep_eq] at h2
  have h3 : ((rep (y - base X) i).natAbs : ℝ) ≤ (rad d L j : ℝ) := by exact_mod_cast h2.trans h1
  rw [Nat.cast_natAbs, Int.cast_abs] at h3
  exact h3

theorem supNormZ_rep_le {j : ℕ} {X : Finset (Lam d L N)} (hX : IsSmall j X) {y : Lam d L N}
    (hy : y ∈ nbhd j X) : (supNormZ (rep (y - base X)) : ℝ) ≤ (rad d L j : ℝ) := by
  rw [supNormZ_rep_eq]; exact_mod_cast supNorm_nbhd_base hX hy

/-! ### Derivatives of the cut-off weight -/

theorem D1_tCut_eq (X : Finset (Lam d L N)) (a b : Lam d L N) (R : ℝ) (α : Dir d → ℕ)
    (u : Zd d) :
    D1 (fun b v => b +ᵥ v) α (tCut X a b R) u = (eN2 X a b)⁻¹ * ∑ i, eV X a b i *
      (D1 (fun b v => b +ᵥ v) α (cutP (Pi.single i 1) R) u -
        lift (base X) a i * D1 (fun b v => b +ᵥ v) α (cutP 0 R) u) := by
  unfold tCut
  rw [D1_smul _ _ (eN2 X a b)⁻¹ (fun v => ∑ i, eV X a b i *
      (cutP (Pi.single i 1) R v - lift (base X) a i * cutP 0 R v)),
    D1_sum univ _ _ (fun i v => eV X a b i *
      (cutP (Pi.single i 1) R v - lift (base X) a i * cutP 0 R v))]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  rw [D1_smul _ _ (eV X a b i) (fun v => cutP (Pi.single i 1) R v - lift (base X) a i * cutP 0 R v),
    D1_sub _ _ (cutP (Pi.single i 1) R) (fun v => lift (base X) a i * cutP 0 R v),
    D1_smul _ _ (lift (base X) a i) (cutP 0 R)]

theorem abs_D1_tCut_le {Cc : ℝ}
    (hCc : ∀ m : Fin d → ℕ, (∀ i, m i ≤ 1) → ∀ R : ℝ, 1 ≤ R → ∀ α : Dir d → ℕ,
      Grassmann.mabs α ≤ pPhi d → ∀ u : Zd d,
      |D1 (fun b v => b +ᵥ v) α (cutP m R) u| ≤ Cc * R ^ (∑ i, m i) / R ^ Grassmann.mabs α)
    {j : ℕ} {X : Finset (Lam d L N)} (hX : IsSmall j X) {a : Lam d L N} (ha : a ∈ nbhd j X)
    (b : Lam d L N) (α : Dir d → ℕ) (hα : Grassmann.mabs α ≤ pPhi d) (u : Zd d) :
    |D1 (fun b v => b +ᵥ v) α (tCut X a b (rad d L j : ℝ)) u| ≤
      (2 * Cc * (rad d L j : ℝ) * eN1 X a b * (eN2 X a b)⁻¹) /
        (rad d L j : ℝ) ^ Grassmann.mabs α := by
  set R : ℝ := (rad d L j : ℝ)
  have hR1 : 1 ≤ R := Nat.one_le_cast.2 (one_le_rad j)
  have hRk : 0 < R ^ Grassmann.mabs α := by positivity
  have hE : 0 ≤ (eN2 X a b)⁻¹ := inv_nonneg.2 (eN2_nonneg X a b)
  have hs1 : ∀ i (k : Fin d), (Pi.single i 1 : Fin d → ℕ) k ≤ 1 := fun i k => by
    by_cases h : k = i <;> simp [h]
  rw [D1_tCut_eq, abs_mul, abs_of_nonneg hE]
  have hterm : ∀ i, |eV X a b i * (D1 (fun b v => b +ᵥ v) α (cutP (Pi.single i 1) R) u -
      lift (base X) a i * D1 (fun b v => b +ᵥ v) α (cutP 0 R) u)| ≤
      |eV X a b i| * (2 * Cc * R / R ^ Grassmann.mabs α) := by
    intro i
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have h1 := hCc _ (hs1 i) R hR1 α hα u
    rw [sum_single'] at h1
    have h0 := hCc 0 (fun _ => zero_le_one) R hR1 α hα u
    simp only [Pi.zero_apply, sum_const_zero, pow_zero] at h0
    have hl := abs_lift_le hX ha i
    refine (abs_sub _ _).trans ?_
    rw [abs_mul]
    have e2 : |lift (base X) a i| * |D1 (fun b v => b +ᵥ v) α (cutP 0 R) u| ≤
        R * (Cc * 1 / R ^ Grassmann.mabs α) :=
      mul_le_mul hl h0 (abs_nonneg _) (by linarith)
    calc |D1 (fun b v => b +ᵥ v) α (cutP (Pi.single i 1) R) u| +
          |lift (base X) a i| * |D1 (fun b v => b +ᵥ v) α (cutP 0 R) u|
        ≤ Cc * R ^ 1 / R ^ Grassmann.mabs α + R * (Cc * 1 / R ^ Grassmann.mabs α) :=
          add_le_add h1 e2
      _ = 2 * Cc * R / R ^ Grassmann.mabs α := by ring
  calc (eN2 X a b)⁻¹ * |∑ i, eV X a b i * (D1 (fun b v => b +ᵥ v) α (cutP (Pi.single i 1) R) u -
        lift (base X) a i * D1 (fun b v => b +ᵥ v) α (cutP 0 R) u)|
      ≤ (eN2 X a b)⁻¹ * ∑ i, |eV X a b i| * (2 * Cc * R / R ^ Grassmann.mabs α) :=
        mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => hterm i))
          hE
    _ = (2 * Cc * R * eN1 X a b * (eN2 X a b)⁻¹) / R ^ Grassmann.mabs α := by
        rw [← sum_mul, eN1]; ring

/-! ### The weighted coefficients -/

/-- `∑_x F_{(x,σ)} ∏_{r : w_r} t(x_r)`. -/
def Mw (X : Finset (Lam d L N)) (a b : Lam d L N) {n : ℕ} (σ : Fin n → ℤˣ) (w : Fin n → Bool)
    (F : Alg d L N) : ℂ :=
  ∑ x : Fin n → Lam d L N, coeff F (fun r => (x r, σ r)) *
    ((∏ r, if w r then tW X a b (x r) else 1 : ℝ) : ℂ)

/-- The weights with cut-off. -/
def Hsel (X : Finset (Lam d L N)) (a b : Lam d L N) (R : ℝ) {n : ℕ} (w : Fin n → Bool)
    (r : Fin n) : Zd d → ℝ :=
  if w r then tCut X a b R else cutP 0 R

theorem Mw_eq_cut {j : ℕ} {X : Finset (Lam d L N)} (hX : IsSmall j X) (a b : Lam d L N)
    {F : Alg d L N} (hF : F ∈ NX (nbhd j X : Set (Lam d L N))) {n : ℕ} (σ : Fin n → ℤˣ)
    (w : Fin n → Bool) :
    Mw X a b σ w F = ∑ x : Fin n → Lam d L N, coeff F (fun r => (x r, σ r)) *
      ((∏ r, Hsel X a b (rad d L j : ℝ) w r (rep (x r - base X)) : ℝ) : ℂ) := by
  have hR0 : (0 : ℝ) < (rad d L j : ℝ) := Nat.cast_pos.2 (one_le_rad j)
  unfold Mw
  refine sum_congr rfl fun x _ => ?_
  by_cases hx : ∀ r, x r ∈ nbhd j X
  · congr 2
    refine prod_congr rfl fun r _ => ?_
    have hu := supNormZ_rep_le hX (hx r)
    unfold Hsel
    split_ifs
    · exact (tCut_eq X a b hR0 hu).symm
    · exact (cutP_zero_eq hR0 hu).symm
  · push Not at hx
    obtain ⟨r, hr⟩ := hx
    rw [coeff_eq_zero_of_mem_NX hF _ r (by simpa using hr)]
    ring

theorem norm_Mw_le {Cc : ℝ} (hCc0 : 0 ≤ Cc)
    (hCc : ∀ m : Fin d → ℕ, (∀ i, m i ≤ 1) → ∀ R : ℝ, 1 ≤ R → ∀ α : Dir d → ℕ,
      Grassmann.mabs α ≤ pPhi d → ∀ u : Zd d,
      |D1 (fun b v => b +ᵥ v) α (cutP m R) u| ≤ Cc * R ^ (∑ i, m i) / R ^ Grassmann.mabs α)
    (hL : 2 ^ (d + 3) + 8 * d < L) {j : ℕ} (hj : j < N) {X : Finset (Lam d L N)}
    (hX : IsSmall j X) {a : Lam d L N} (ha : a ∈ nbhd j X) (b : Lam d L N)
    {F : Alg d L N} (hF : F ∈ NX (nbhd j X : Set (Lam d L N))) {n : ℕ} (σ : Fin n → ℤˣ)
    (w : Fin n → Bool) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ‖Mw X a b σ w F‖ ≤ n.factorial * (ℓ⁻¹ ^ n * ∏ r, (if w r then
      2 * Cc * (rad d L j : ℝ) * eN1 X a b * (eN2 X a b)⁻¹ else Cc)) *
      (Tj d (L : ℝ) j ℓ F).toReal := by
  set R : ℝ := (rad d L j : ℝ)
  have hR1 : 1 ≤ R := Nat.one_le_cast.2 (one_le_rad j)
  have hR0 : 0 < R := by linarith
  rw [Mw_eq_cut hX a b hF σ w]
  refine weighted_bound hL hj X F σ (Hsel X a b R w) _ (fun r => ?_) (fun r u hu => ?_)
    (fun r α u hα => ?_) hℓ
  · split_ifs
    · have := eN1_nonneg X a b
      have := inv_nonneg.2 (eN2_nonneg X a b)
      positivity
    · exact hCc0
  · unfold Hsel
    split_ifs
    · exact tCut_far X a b hR0 hu
    · exact cutP_eq_zero _ hR0 hu
  · unfold Hsel
    split_ifs
    · exact abs_D1_tCut_le hCc hX ha b α hα u
    · have h0 := hCc 0 (fun _ => zero_le_one) R hR1 α hα u
      simp only [Pi.zero_apply, sum_const_zero, pow_zero, mul_one] at h0
      exact h0

/-! ### The operator -/

/-- The spin pattern `(-, +)` (`ψ̄ψ`). -/
def sg2 : Fin 2 → ℤˣ := ![-1, 1]

/-- The spin pattern `(-, +, -, +)` (`ψ̄ψψ̄ψ`). -/
def sg4 : Fin 4 → ℤˣ := ![-1, 1, -1, 1]

/-- `δ̄ = ψ̄_b - ψ̄_a`. -/
def dbar (a b : Lam d L N) : Alg d L N := psibar b - psibar a

/-- `δ = ψ_b - ψ_a`. -/
def dlt (a b : Lam d L N) : Alg d L N := psi b - psi a

/-- The part of `loc^{ab,t}` beyond the one-point localisation at `a`:
`M_{10} δ̄ψ_a + M_{01} ψ̄_aδ + M_{11} δ̄δ + M_4 ψ̄_aψ_aδ̄δ`. -/
def Dt (X : Finset (Lam d L N)) (a b : Lam d L N) (F : Alg d L N) : Alg d L N :=
  Mw X a b sg2 ![true, false] F • (dbar a b * psi a) +
    Mw X a b sg2 ![false, true] F • (psibar a * dlt a b) +
    Mw X a b sg2 ![true, true] F • (dbar a b * dlt a b) +
    Mw X a b sg4 ![true, true, false, false] F • (pbp a * (dbar a b * dlt a b))

/-- **`loc^{ab}` in `d = 2` with barycentric weights**: `locEven {a} + Dt`, i.e.
`ε(F) + M_{00} ψ̄_aψ_a + M_{10} δ̄ψ_a + M_{01} ψ̄_aδ + M_{11} δ̄δ + M_4 ψ̄_aψ_aδ̄δ` for `a ∈ X`. -/
def locABt (X : Finset (Lam d L N)) (a b : Lam d L N) (F : Alg d L N) : Alg d L N :=
  locEven {a} X X F + Dt X a b F

/-! ### Norms of the monomials -/

theorem tn_smul_bound {h ℓ : ℝ} {c : ℂ} {x : Alg d L N} {r B : ℝ}
    (hx : tNorm (Dir d) (pPhi d) h ℓ x ≤ ENNReal.ofReal r) (hB : ‖c‖ * r ≤ B) :
    tNorm (Dir d) (pPhi d) h ℓ (c • x) ≤ ENNReal.ofReal B := by
  refine (tNorm_smul_le c x).trans ?_
  calc ENNReal.ofReal ‖c‖ * tNorm (Dir d) (pPhi d) h ℓ x
      ≤ ENNReal.ofReal ‖c‖ * ENNReal.ofReal r := by gcongr
    _ = ENNReal.ofReal (‖c‖ * r) := (ENNReal.ofReal_mul (norm_nonneg _)).symm
    _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal hB

theorem tn_mul_bound {h ℓ : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ) {x y : Alg d L N} {r r' : ℝ}
    (hr : 0 ≤ r) (hx : tNorm (Dir d) (pPhi d) h ℓ x ≤ ENNReal.ofReal r)
    (hy : tNorm (Dir d) (pPhi d) h ℓ y ≤ ENNReal.ofReal r') :
    tNorm (Dir d) (pPhi d) h ℓ (x * y) ≤ ENNReal.ofReal (r * r') := by
  refine (tNorm_mul_le hh hℓ x y).trans ?_
  rw [ENNReal.ofReal_mul hr]
  exact mul_le_mul' hx hy

theorem tNorm_dbar_le (hd : 1 ≤ d) {h ℓ : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ) (X : Finset (Lam d L N))
    (a b : Lam d L N) :
    tNorm (Dir d) (pPhi d) h ℓ (dbar a b) ≤ ENNReal.ofReal (eN1 X a b * ℓ * h⁻¹) := by
  have hp : 1 ≤ pPhi d := by simp [pPhi]; omega
  refine (tNorm_ψ_sub_le hp hh hℓ a b (-1)).trans (ENNReal.ofReal_le_ofReal ?_)
  have := dstB_le_norm1 a b (base X) (-1)
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_right this (by positivity)

theorem tNorm_dlt_le (hd : 1 ≤ d) {h ℓ : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ) (X : Finset (Lam d L N))
    (a b : Lam d L N) :
    tNorm (Dir d) (pPhi d) h ℓ (dlt a b) ≤ ENNReal.ofReal (eN1 X a b * ℓ * h⁻¹) := by
  have hp : 1 ≤ pPhi d := by simp [pPhi]; omega
  refine (tNorm_ψ_sub_le hp hh hℓ a b 1).trans (ENNReal.ofReal_le_ofReal ?_)
  have := dstB_le_norm1 a b (base X) 1
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_right this (by positivity)

theorem tNorm_pbp_le {h ℓ : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ) (a : Lam d L N) :
    tNorm (Dir d) (pPhi d) h ℓ (pbp a) ≤ ENNReal.ofReal (ℓ * ℓ) :=
  tn_mul_bound hh hℓ hℓ.le (tNorm_psibar hh hℓ a).le (tNorm_psi hh hℓ a).le

/-! ### The bound on `Dt` -/

/-- The constant of `tNorm_Dt_le`. -/
def KD (d : ℕ) (Cc : ℝ) : ℝ :=
  32 * Cc ^ 2 * d * 2 ^ (d + 1) + (32 * Cc ^ 2 * d ^ 2 + 1536 * Cc ^ 4 * d ^ 2) * 4 ^ (d + 1)

theorem norm_M10_le {Cc T At ℓ : ℝ} {c : ℂ}
    (h : ‖c‖ ≤ (Nat.factorial 2 : ℕ) * (ℓ⁻¹ ^ 2 * ∏ r : Fin 2,
      (if (![true, false] : Fin 2 → Bool) r then At else Cc)) * T) :
    ‖c‖ ≤ 2 * (ℓ⁻¹ ^ 2 * (At * Cc)) * T := by
  simpa [Fin.prod_univ_two, Nat.factorial] using h

theorem norm_M01_le {Cc T At ℓ : ℝ} {c : ℂ}
    (h : ‖c‖ ≤ (Nat.factorial 2 : ℕ) * (ℓ⁻¹ ^ 2 * ∏ r : Fin 2,
      (if (![false, true] : Fin 2 → Bool) r then At else Cc)) * T) :
    ‖c‖ ≤ 2 * (ℓ⁻¹ ^ 2 * (Cc * At)) * T := by
  simpa [Fin.prod_univ_two, Nat.factorial] using h

theorem norm_M11_le {Cc T At ℓ : ℝ} {c : ℂ}
    (h : ‖c‖ ≤ (Nat.factorial 2 : ℕ) * (ℓ⁻¹ ^ 2 * ∏ r : Fin 2,
      (if (![true, true] : Fin 2 → Bool) r then At else Cc)) * T) :
    ‖c‖ ≤ 2 * (ℓ⁻¹ ^ 2 * (At * At)) * T := by
  simpa [Fin.prod_univ_two, Nat.factorial] using h

theorem norm_M4_le {Cc T At ℓ : ℝ} {c : ℂ}
    (h : ‖c‖ ≤ (Nat.factorial 4 : ℕ) * (ℓ⁻¹ ^ 4 * ∏ r : Fin 4,
      (if (![true, true, false, false] : Fin 4 → Bool) r then At else Cc)) * T) :
    ‖c‖ ≤ 24 * (ℓ⁻¹ ^ 4 * (At * At * (Cc * Cc))) * T := by
  have e : ∏ r : Fin 4, (if (![true, true, false, false] : Fin 4 → Bool) r then At else Cc) =
      At * At * (Cc * Cc) := by
    simp [Fin.prod_univ_four]; ring
  rw [e] at h
  simpa [Nat.factorial] using h

/-- **The bound on `Dt`**: `‖Dt F‖_{T_h(ℓ')} ≤ K (L^j/h) ‖F‖_{T_j(ℓ)}` for `h ≥ L^j`,
`ℓ' ≤ 2ℓ`, `a ∈ X^□`, `b` arbitrary. -/
theorem tNorm_Dt_le (hd : 1 ≤ d) {Cc : ℝ} (hCc0 : 0 ≤ Cc)
    (hCc : ∀ m : Fin d → ℕ, (∀ i, m i ≤ 1) → ∀ R : ℝ, 1 ≤ R → ∀ α : Dir d → ℕ,
      Grassmann.mabs α ≤ pPhi d → ∀ u : Zd d,
      |D1 (fun b v => b +ᵥ v) α (cutP m R) u| ≤ Cc * R ^ (∑ i, m i) / R ^ Grassmann.mabs α)
    (hL : 2 ^ (d + 3) + 8 * d < L) {j : ℕ} (hj : j < N) {X : Finset (Lam d L N)}
    (hX : IsSmall j X) {a : Lam d L N} (ha : a ∈ nbhd j X) (b : Lam d L N)
    {F : Alg d L N} (hF : F ∈ NX (nbhd j X : Set (Lam d L N))) {ℓ ℓ' h : ℝ} (hℓ : 0 < ℓ)
    (hℓ' : 0 < ℓ') (hℓℓ : ℓ' ≤ 2 * ℓ) (hh : 0 < h) (hsh : (L : ℝ) ^ j ≤ h) :
    tNorm (Dir d) (pPhi d) h ℓ' (Dt X a b F) ≤
      ENNReal.ofReal (KD d Cc * ((L : ℝ) ^ j * h⁻¹) * (Tj d (L : ℝ) j ℓ F).toReal) := by
  have hT : 0 ≤ (Tj d (L : ℝ) j ℓ F).toReal := ENNReal.toReal_nonneg
  have he1 := eN1_nonneg X a b
  have hEi : 0 ≤ (eN2 X a b)⁻¹ := inv_nonneg.2 (eN2_nonneg X a b)
  have hq : eN1 X a b ^ 2 * (eN2 X a b)⁻¹ ≤ d := eN1_sq_div_le X a b
  have hρ : ℓ' * ℓ⁻¹ ≤ 2 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hℓ]; linarith
  have hR : ((rad d L j : ℕ) : ℝ) = 2 ^ (d + 1) * (L : ℝ) ^ j := by push_cast [rad]; ring
  have hu1 : (L : ℝ) ^ j * h⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hh]; exact hsh
  have hu0 : 0 ≤ (L : ℝ) ^ j * h⁻¹ := by positivity
  have hκ : ((rad d L j : ℕ) : ℝ) * h⁻¹ = 2 ^ (d + 1) * ((L : ℝ) ^ j * h⁻¹) := by
    rw [hR]; ring
  have hκ0 : 0 ≤ ((rad d L j : ℕ) : ℝ) * h⁻¹ := by positivity
  have hκ2 : (((rad d L j : ℕ) : ℝ) * h⁻¹) ^ 2 ≤ 4 ^ (d + 1) * ((L : ℝ) ^ j * h⁻¹) := by
    rw [hκ, mul_pow, ← pow_mul, show (2 : ℝ) ^ ((d + 1) * 2) = 4 ^ (d + 1) by
      rw [mul_comm, pow_mul]; norm_num]
    gcongr
    calc ((L : ℝ) ^ j * h⁻¹) ^ 2 = ((L : ℝ) ^ j * h⁻¹) * ((L : ℝ) ^ j * h⁻¹) := sq _
      _ ≤ ((L : ℝ) ^ j * h⁻¹) * 1 := mul_le_mul_of_nonneg_left hu1 hu0
      _ = _ := mul_one _
  set T := (Tj d (L : ℝ) j ℓ F).toReal
  set At : ℝ := 2 * Cc * (rad d L j : ℝ) * eN1 X a b * (eN2 X a b)⁻¹ with hAt
  set δn : ℝ := eN1 X a b * ℓ' * h⁻¹ with hδn
  have hδn0 : 0 ≤ δn := by positivity
  -- coefficients
  have m10 := norm_M10_le (norm_Mw_le hCc0 hCc hL hj hX ha b hF sg2 ![true, false] hℓ)
  have m01 := norm_M01_le (norm_Mw_le hCc0 hCc hL hj hX ha b hF sg2 ![false, true] hℓ)
  have m11 := norm_M11_le (norm_Mw_le hCc0 hCc hL hj hX ha b hF sg2 ![true, true] hℓ)
  have m4 := norm_M4_le (norm_Mw_le hCc0 hCc hL hj hX ha b hF sg4 ![true, true, false, false] hℓ)
  rw [← hAt] at m10 m01 m11 m4
  -- monomials
  have nb := tNorm_dbar_le hd hh hℓ' X a b
  have nd := tNorm_dlt_le hd hh hℓ' X a b
  rw [← hδn] at nb nd
  have x1 := tn_mul_bound hh hℓ' hδn0 nb (tNorm_psi hh hℓ' a).le
  have x2 := tn_mul_bound hh hℓ' hℓ'.le (tNorm_psibar hh hℓ' a).le nd
  have x3 := tn_mul_bound hh hℓ' hδn0 nb nd
  have x4 := tn_mul_bound hh hℓ' (by positivity) (tNorm_pbp_le hh hℓ' a) x3
  -- the four terms
  set κ : ℝ := ((rad d L j : ℕ) : ℝ) * h⁻¹ with hκdef
  have t1 : ‖Mw X a b sg2 ![true, false] F‖ * (δn * ℓ') ≤ 16 * Cc ^ 2 * d * κ * T := by
    calc ‖Mw X a b sg2 ![true, false] F‖ * (δn * ℓ')
        ≤ (2 * (ℓ⁻¹ ^ 2 * (At * Cc)) * T) * (δn * ℓ') :=
          mul_le_mul_of_nonneg_right m10 (by positivity)
      _ = 4 * Cc ^ 2 * (ℓ' * ℓ⁻¹) ^ 2 * κ * (eN1 X a b ^ 2 * (eN2 X a b)⁻¹) * T := by
          rw [hAt, hδn, hκdef]; ring
      _ ≤ 4 * Cc ^ 2 * 2 ^ 2 * κ * d * T := by gcongr
      _ = 16 * Cc ^ 2 * d * κ * T := by ring
  have t2 : ‖Mw X a b sg2 ![false, true] F‖ * (ℓ' * δn) ≤ 16 * Cc ^ 2 * d * κ * T := by
    calc ‖Mw X a b sg2 ![false, true] F‖ * (ℓ' * δn)
        ≤ (2 * (ℓ⁻¹ ^ 2 * (Cc * At)) * T) * (ℓ' * δn) :=
          mul_le_mul_of_nonneg_right m01 (by positivity)
      _ = 4 * Cc ^ 2 * (ℓ' * ℓ⁻¹) ^ 2 * κ * (eN1 X a b ^ 2 * (eN2 X a b)⁻¹) * T := by
          rw [hAt, hδn, hκdef]; ring
      _ ≤ 4 * Cc ^ 2 * 2 ^ 2 * κ * d * T := by gcongr
      _ = 16 * Cc ^ 2 * d * κ * T := by ring
  have t3 : ‖Mw X a b sg2 ![true, true] F‖ * (δn * δn) ≤ 32 * Cc ^ 2 * d ^ 2 * κ ^ 2 * T := by
    calc ‖Mw X a b sg2 ![true, true] F‖ * (δn * δn)
        ≤ (2 * (ℓ⁻¹ ^ 2 * (At * At)) * T) * (δn * δn) :=
          mul_le_mul_of_nonneg_right m11 (by positivity)
      _ = 8 * Cc ^ 2 * (ℓ' * ℓ⁻¹) ^ 2 * κ ^ 2 * (eN1 X a b ^ 2 * (eN2 X a b)⁻¹) ^ 2 * T := by
          rw [hAt, hδn, hκdef]; ring
      _ ≤ 8 * Cc ^ 2 * 2 ^ 2 * κ ^ 2 * (d : ℝ) ^ 2 * T := by gcongr
      _ = 32 * Cc ^ 2 * d ^ 2 * κ ^ 2 * T := by ring
  have t4 : ‖Mw X a b sg4 ![true, true, false, false] F‖ * (ℓ' * ℓ' * (δn * δn)) ≤
      1536 * Cc ^ 4 * d ^ 2 * κ ^ 2 * T := by
    calc ‖Mw X a b sg4 ![true, true, false, false] F‖ * (ℓ' * ℓ' * (δn * δn))
        ≤ (24 * (ℓ⁻¹ ^ 4 * (At * At * (Cc * Cc))) * T) * (ℓ' * ℓ' * (δn * δn)) :=
          mul_le_mul_of_nonneg_right m4 (by positivity)
      _ = 96 * Cc ^ 4 * (ℓ' * ℓ⁻¹) ^ 4 * κ ^ 2 * (eN1 X a b ^ 2 * (eN2 X a b)⁻¹) ^ 2 * T := by
          rw [hAt, hδn, hκdef]; ring
      _ ≤ 96 * Cc ^ 4 * 2 ^ 4 * κ ^ 2 * (d : ℝ) ^ 2 * T := by gcongr
      _ = 1536 * Cc ^ 4 * d ^ 2 * κ ^ 2 * T := by ring
  have y1 := tn_smul_bound (c := Mw X a b sg2 ![true, false] F) x1 t1
  have y2 := tn_smul_bound (c := Mw X a b sg2 ![false, true] F) x2 t2
  have y3 := tn_smul_bound (c := Mw X a b sg2 ![true, true] F) x3 t3
  have y4 := tn_smul_bound (c := Mw X a b sg4 ![true, true, false, false] F) x4 t4
  unfold Dt
  refine (tNorm_add_le _ _).trans ?_
  refine (add_le_add ((tNorm_add_le _ _).trans (add_le_add ((tNorm_add_le _ _).trans
    (add_le_add y1 y2)) y3)) y4).trans ?_
  have hp1 : 0 ≤ 16 * Cc ^ 2 * d * κ * T := by positivity
  have hp3 : 0 ≤ 32 * Cc ^ 2 * d ^ 2 * κ ^ 2 * T := by positivity
  have hp4 : 0 ≤ 1536 * Cc ^ 4 * d ^ 2 * κ ^ 2 * T := by positivity
  rw [← ENNReal.ofReal_add hp1 hp1, ← ENNReal.ofReal_add (by positivity) hp3,
    ← ENNReal.ofReal_add (by positivity) hp4]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hκ]
  rw [hκ] at hκ2
  set u := (L : ℝ) ^ j * h⁻¹
  have hA : 16 * Cc ^ 2 * d * (2 ^ (d + 1) * u) * T + 16 * Cc ^ 2 * d * (2 ^ (d + 1) * u) * T =
      32 * Cc ^ 2 * d * 2 ^ (d + 1) * u * T := by ring
  have hB : 32 * Cc ^ 2 * d ^ 2 * (2 ^ (d + 1) * u) ^ 2 * T + 1536 * Cc ^ 4 * d ^ 2 *
      (2 ^ (d + 1) * u) ^ 2 * T ≤
      (32 * Cc ^ 2 * d ^ 2 + 1536 * Cc ^ 4 * d ^ 2) * (4 ^ (d + 1) * u) * T := by
    have : 32 * Cc ^ 2 * d ^ 2 * (2 ^ (d + 1) * u) ^ 2 * T + 1536 * Cc ^ 4 * d ^ 2 *
        (2 ^ (d + 1) * u) ^ 2 * T =
        (32 * Cc ^ 2 * d ^ 2 + 1536 * Cc ^ 4 * d ^ 2) * (2 ^ (d + 1) * u) ^ 2 * T := by ring
    rw [this]
    gcongr
  calc 16 * Cc ^ 2 * d * (2 ^ (d + 1) * u) * T + 16 * Cc ^ 2 * d * (2 ^ (d + 1) * u) * T +
        32 * Cc ^ 2 * d ^ 2 * (2 ^ (d + 1) * u) ^ 2 * T +
        1536 * Cc ^ 4 * d ^ 2 * (2 ^ (d + 1) * u) ^ 2 * T
      = 32 * Cc ^ 2 * d * 2 ^ (d + 1) * u * T + (32 * Cc ^ 2 * d ^ 2 * (2 ^ (d + 1) * u) ^ 2 * T +
        1536 * Cc ^ 4 * d ^ 2 * (2 ^ (d + 1) * u) ^ 2 * T) := by rw [← hA]; ring
    _ ≤ 32 * Cc ^ 2 * d * 2 ^ (d + 1) * u * T +
        (32 * Cc ^ 2 * d ^ 2 + 1536 * Cc ^ 4 * d ^ 2) * (4 ^ (d + 1) * u) * T := by
        gcongr
    _ = KD d Cc * u * T := by unfold KD; ring

/-! ### Boundedness and contraction -/

theorem KD_nonneg (d : ℕ) {Cc : ℝ} : 0 ≤ KD d Cc := by unfold KD; positivity

/-- **`loc^{ab,t}` is bounded** (`prop:Loc`(i)): `‖loc^{ab,t}_X F‖_{T_j(ℓ)} ≤ C ‖F‖_{T_j(ℓ)}` for
`X` small, `a ∈ X`, `b` arbitrary and `F ∈ 𝒩(X^□)`. -/
theorem exists_locABt_bound (d : ℕ) (hd : 1 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (L : ℕ) [NeZero L], 2 ^ (d + 3) + 8 * d < L → ∀ N j : ℕ, j < N → ∀ ℓ : ℝ, 0 < ℓ →
    ∀ X : Finset (Lam d L N), IsSmall j X → ∀ a b : Lam d L N, a ∈ X →
    ∀ F ∈ NX (nbhd j X : Set (Lam d L N)),
      Tj d (L : ℝ) j ℓ (locABt X a b F) ≤ ENNReal.ofReal C * Tj d (L : ℝ) j ℓ F := by
  obtain ⟨Cb, hCb0, hCb⟩ := exists_even_bound d
  obtain ⟨Cc, hCc0, hCc⟩ := exists_D1_cutP_bound d (pPhi d) 1
  refine ⟨Cb + KD d Cc, add_nonneg hCb0 (KD_nonneg d), ?_⟩
  intro L _ hL N j hj ℓ hℓ X hX a b ha F hF
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hs : (0 : ℝ) < (L : ℝ) ^ j := by positivity
  set T := (Tj d (L : ℝ) j ℓ F).toReal
  have hT : 0 ≤ T := ENNReal.toReal_nonneg
  have hTF : Tj d (L : ℝ) j ℓ F = ENNReal.ofReal T :=
    (ENNReal.ofReal_toReal (tNorm_ne_top hs hℓ F)).symm
  have h1 := hCb L hL N j hj X X hX subset_rfl F hF {a} ℓ hℓ
  have h2 := tNorm_Dt_le hd hCc0 hCc hL hj hX (subset_nbhd hX.1 ha) b hF hℓ hℓ
    (by linarith) hs le_rfl
  rw [mul_inv_cancel₀ hs.ne', mul_one] at h2
  unfold locABt
  refine (tNorm_add_le _ _).trans ?_
  rw [hTF] at h1 ⊢
  refine (add_le_add h1 h2).trans (le_of_eq ?_)
  have hK := KD_nonneg d (Cc := Cc)
  rw [← ENNReal.ofReal_mul hCb0, ← ENNReal.ofReal_add (by positivity)
    (mul_nonneg hK hT), ← ENNReal.ofReal_mul (by positivity)]
  congr 1; ring

/-- **`loc^{ab,t}` contracts in `d = 2`**: for `X` small, `a ∈ X`, `b` arbitrary, `U(1)`-invariant
`F ∈ 𝒩(X^□)` and `ℓ' ≤ 2ℓ`, `‖F - loc^{ab,t}_X F‖_{T_{j+1}(ℓ')} ≤ C L^{-1} ‖F‖_{T_j(ℓ)}`. -/
theorem exists_locABt_contract (d : ℕ) (hd : 1 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧ ∃ L₀ : ℕ,
    ∀ (L : ℕ) [NeZero L], 2 ^ (d + 3) + 8 * d < L → L₀ ≤ L → ∀ N j : ℕ, j < N →
    ∀ ℓ ℓ' : ℝ, 0 < ℓ → 0 < ℓ' → ℓ' ≤ 2 * ℓ →
    ∀ X : Finset (Lam d L N), IsSmall j X → ∀ a b : Lam d L N, a ∈ X →
    ∀ F ∈ NX (nbhd j X : Set (Lam d L N)), IsSym F →
      Tj d (L : ℝ) (j + 1) ℓ' (F - locABt X a b F) ≤
        ENNReal.ofReal (C / L) * Tj d (L : ℝ) j ℓ F := by
  obtain ⟨C2, hC2, L₀, h2⟩ := exists_even_contract2 d hd
  obtain ⟨Cc, hCc0, hCc⟩ := exists_D1_cutP_bound d (pPhi d) 1
  refine ⟨C2 + KD d Cc, add_nonneg hC2 (KD_nonneg d), L₀, ?_⟩
  intro L _ hL hL₀ N j hj ℓ ℓ' hℓ hℓ' hℓℓ X hX a b ha F hF hFs
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hs : (0 : ℝ) < (L : ℝ) ^ j := by positivity
  have hh : (0 : ℝ) < (L : ℝ) ^ (j + 1) := by positivity
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hsh : (L : ℝ) ^ j ≤ (L : ℝ) ^ (j + 1) := by
    rw [pow_succ]; exact le_mul_of_one_le_right hs.le hL1
  set T := (Tj d (L : ℝ) j ℓ F).toReal
  have hT : 0 ≤ T := ENNReal.toReal_nonneg
  have hTF : Tj d (L : ℝ) j ℓ F = ENNReal.ofReal T :=
    (ENNReal.ofReal_toReal (tNorm_ne_top hs hℓ F)).symm
  have e1 := h2 L hL hL₀ N j hj ℓ ℓ' hℓ hℓ' hℓℓ X hX {a} (inter_singleton_nonempty ha) F hF
    ((hasCharge_zero_iff F).2 hFs)
  have e2 := tNorm_Dt_le hd hCc0 hCc hL hj hX (subset_nbhd hX.1 ha) b hF hℓ hℓ' hℓℓ hh hsh
  have hu : (L : ℝ) ^ j * ((L : ℝ) ^ (j + 1))⁻¹ = 1 / L := by
    rw [pow_succ]; field_simp
  rw [hu] at e2
  have hsplit : F - locABt X a b F = (F - locEven {a} X X F) - Dt X a b F := by
    unfold locABt; abel
  rw [hsplit]
  refine (tNorm_sub_le _ _).trans ?_
  rw [hTF] at e1 ⊢
  refine (add_le_add e1 e2).trans (le_of_eq ?_)
  have hK := KD_nonneg d (Cc := Cc)
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
    (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1; ring

/-! ### `loc^{ab,t}` reproduces the two-point monomials -/

theorem eN2_ne_zero {X : Finset (Lam d L N)} {a b : Lam d L N} (hab : a ≠ b) :
    eN2 X a b ≠ 0 := by
  intro h0
  have hz : ∀ i ∈ (univ : Finset (Fin d)), eV X a b i ^ 2 = 0 :=
    (sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg _).1 h0
  have hrep : rep (b - base X) = rep (a - base X) := by
    funext i
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (hz i (mem_univ i))
    unfold eV lift at this
    exact_mod_cast sub_eq_zero.1 this
  have : b - base X = a - base X := by
    rw [← prj_rep (b - base X), ← prj_rep (a - base X), hrep]
  exact hab (sub_left_injective this).symm

theorem locEven_singleton_eq {X : Finset (Lam d L N)} {a : Lam d L N} (ha : a ∈ X)
    (F : Alg d L N) : locEven {a} X X F = ε F • (1 : Alg d L N) + mass2 F • pbp a := by
  have h : X ∩ {a} = {a} := by
    ext x; simp only [mem_inter, mem_singleton]
    constructor
    · exact fun h => h.2
    · rintro rfl; exact ⟨ha, rfl⟩
  simp only [locEven, locGen, h, card_singleton, Nat.cast_one, div_one, sum_singleton]

theorem coeff_sg2 (F : Alg d L N) (x : Fin 2 → Lam d L N) :
    coeff F (fun r => (x r, sg2 r)) = coeff F ![(x 0, -1), (x 1, 1)] := by
  congr 1; funext r; fin_cases r <;> rfl

theorem Mw_m2 (X : Finset (Lam d L N)) (a b u v : Lam d L N) (w : Fin 2 → Bool) :
    Mw X a b sg2 w (psibar u * psi v) =
      ((∏ r : Fin 2, if w r then tW X a b (![u, v] r) else 1 : ℝ) : ℂ) := by
  unfold Mw
  rw [Loc.sum_fin_two]
  simp_rw [coeff_sg2, coeff_psibar_psi_mp]
  rw [sum_eq_single u (fun x _ hx => sum_eq_zero fun y _ => by simp [hx])
    (fun h => absurd (mem_univ u) h)]
  rw [sum_eq_single v (fun y _ hy => by simp [hy]) (fun h => absurd (mem_univ v) h)]
  simp

theorem Mw_m2_four (X : Finset (Lam d L N)) (a b u v : Lam d L N) (w : Fin 4 → Bool) :
    Mw X a b sg4 w (psibar u * psi v) = 0 := by
  unfold Mw
  refine sum_eq_zero fun x _ => ?_
  rw [psibar_mul_psi_eq, psiPow, coeff_ιMulti_of_ne _ _ (by decide), zero_mul]

theorem eps_m2 (u v : Lam d L N) : ε (psibar u * psi v) = 0 := by
  simp [psibar, psi, ψ]

theorem mass2_m2 (u v : Lam d L N) : mass2 (psibar u * psi v) = 1 := by
  simp [mass2, coeff_psibar_psi_mp, ite_and]

/-- **`loc^{ab,t}` reproduces `ψ̄_uψ_v`, `u, v ∈ {a, b}`** (for `a ∈ X`, `a ≠ b`): so the
couplings `η` and `r` of `V^obs` are in its image. -/
theorem locABt_m2 {X : Finset (Lam d L N)} {a b : Lam d L N} (ha : a ∈ X) (hab : a ≠ b)
    {u v : Lam d L N} (hu : u = a ∨ u = b) (hv : v = a ∨ v = b) :
    locABt X a b (psibar u * psi v) = psibar u * psi v := by
  have hb1 := tW_b X a b (eN2_ne_zero hab)
  have ha0 := tW_a X a b
  unfold locABt Dt
  rw [locEven_singleton_eq ha, eps_m2, mass2_m2, Mw_m2, Mw_m2, Mw_m2, Mw_m2_four]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, if_true, Bool.false_eq_true, if_false, mul_one, one_mul, zero_smul,
    one_smul, add_zero, zero_add]
  unfold pbp dbar dlt
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;>
    simp only [ha0, hb1, Complex.ofReal_zero, Complex.ofReal_one, zero_smul, one_smul, mul_zero,
      mul_one, add_zero, zero_add] <;> noncomm_ring

/-- `loc^{ab,t}` reproduces the constants. -/
theorem locABt_one {X : Finset (Lam d L N)} {a b : Lam d L N} (ha : a ∈ X) :
    locABt X a b (1 : Alg d L N) = 1 := by
  have hM : ∀ {n : ℕ} (σ : Fin n → ℤˣ) (w : Fin n → Bool), n ≠ 0 → Mw X a b σ w 1 = 0 := by
    intro n σ w hn
    unfold Mw
    exact sum_eq_zero fun x _ => by rw [coeff_one_of_ne' _ hn, zero_mul]
  have hm : mass2 (1 : Alg d L N) = 0 := by
    simp [mass2, coeff_one_of_ne' _ (show (2 : ℕ) ≠ 0 by decide)]
  unfold locABt Dt
  rw [locEven_singleton_eq ha, hm, hM _ _ (by decide), hM _ _ (by decide), hM _ _ (by decide),
    hM _ _ (by decide)]
  simp

end

end Obs2
