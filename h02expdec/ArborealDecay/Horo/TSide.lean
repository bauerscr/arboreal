module

public import ArborealDecay.TLaw.PosDef
public import ArborealDecay.Gaussian.Basic
public import ArborealDecay.Horo.Dot

/-!
# The `(t, s)` side of BCHS Proposition 2.9: the `s`-integration

Rooted setting of supplement `inp:A-BCHS`/`inp:C-BCHS`: `V` finite, `w` a connected weighted
graph (`ArborealDecay.TLaw.IsWGraph`), root `ρ`, `Λ = V ∖ ρ`, `β = w|_Λ`, `h_i = w_{ρ i}`.
Coordinates `τ, s : Λ → ℝ`, extended by `0` at `ρ` (`TLaw.ext`).

* `Htil w ρ τ s = Φ_w(τ̂) + ½ sᵀ 𝓛(τ̂) s − 2 log det 𝓛(τ̂) + 3 ∑ τ` (supplement `inp:C-BCHS`, i.e.
  BCHS (2.59) corrected by §10 (T1), (T3)).
* `horo_action_eq` identifies the bosonic horospherical action
  `½ ∑_{i,k ∈ V} w_{ik} (−u_i · u_k − 1)` (with `u_ρ = (0, 0, 1)`, i.e. `t̂_ρ = ŝ_ρ = 0`) with
  `Φ_w(τ̂) + ½ sᵀ 𝓛 s`, using `neg_mdot_hxyz` (target 2).
* `integral_exp_neg_Htil`: `∫ e^{−H̃(τ,s)} ds = (2π)^{|Λ|} · density w ρ (3/2) τ`, i.e.
  `∫ e^{−H̃(τ,s)} ∏ ds_i/(2π) = e^{−Φ} D^{3/2} (2π)^{−|Λ|/2}` — (2.61) ⇒ (2.62) with `F ≡ 1`.
* `integral_ss_exp_neg_Htil`: `∫ s_i s_j e^{τ_i + τ_j} e^{−H̃(τ,s)} ds
   = e^{τ_i+τ_j} (𝓛⁻¹)_{ij} · (2π)^{|Λ|} · density w ρ (3/2) τ` (the `s`-integration in
  supplement `thm:pinned-green`, `step:pg-gauss`).
-/

@[expose] public section

namespace ArborealDecay.Horo

noncomputable section

open Real Finset Matrix MeasureTheory ArborealDecay.TLaw

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The supplement's `H̃(τ, s)` (`inp:C-BCHS`). -/
def Htil (w : V → V → ℝ) (ρ : V) (τ s : {i // i ≠ ρ} → ℝ) : ℝ :=
  Phi w (ext ρ τ) + (1 / 2) * (s ⬝ᵥ (Lmat w ρ (ext ρ τ)) *ᵥ s) -
    2 * log (Lmat w ρ (ext ρ τ)).det + 3 * ∑ i, τ i

/-! ### The horospherical action -/

/-- Sums over `V ∖ ρ` of functions vanishing at `ρ` are sums over `V`. -/
theorem sum_subtype_ne_eq {f : V → ℝ} (ρ : V) (hf : f ρ = 0) :
    ∑ i : {i // i ≠ ρ}, f i = ∑ i, f i := by
  rw [← Finset.sum_subtype (univ.erase ρ) (p := fun i => i ≠ ρ) (by simp),
    Finset.sum_erase _ hf]

theorem dotProduct_Lmat (w : V → V → ℝ) (hW : IsWGraph w) (ρ : V) (t : V → ℝ)
    (s : {i // i ≠ ρ} → ℝ) :
    s ⬝ᵥ (Lmat w ρ t) *ᵥ s =
      ∑ i, ∑ k, w i k * exp (t i + t k) * ext ρ s i ^ 2 -
        ∑ i, ∑ k, w i k * exp (t i + t k) * ext ρ s i * ext ρ s k := by
  have hL : ∀ i k : {i // i ≠ ρ}, Lmat w ρ t i k =
      (if i = k then ∑ m, w i m * exp (t i + t m) else 0) - w i k * exp (t i + t k) := by
    intro i k
    by_cases h : i = k
    · subst h; simp [Lmat, hW.diag]
    · simp [Lmat, h]
  simp only [dotProduct, mulVec, hL, sub_mul, ite_mul, zero_mul, Finset.sum_sub_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, mul_sub, Finset.mul_sum]
  congr 1
  · rw [← sum_subtype_ne_eq ρ (by simp)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ext_val]
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  · rw [← sum_subtype_ne_eq ρ (by simp)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sum_subtype_ne_eq ρ (by simp)]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [ext_val]; ring

/-- The `s`-part of the rooted horospherical action is `½ sᵀ 𝓛 s`. -/
theorem half_sum_quad_eq (w : V → V → ℝ) (hW : IsWGraph w) (ρ : V) (t : V → ℝ)
    (s : {i // i ≠ ρ} → ℝ) :
    (1 / 2) * ∑ i, ∑ k, w i k * (exp (t i + t k) * (ext ρ s i - ext ρ s k) ^ 2 / 2) =
      (1 / 2) * (s ⬝ᵥ (Lmat w ρ t) *ᵥ s) := by
  set u := ext ρ s
  have hsym : ∑ i, ∑ k, w i k * exp (t i + t k) * u k ^ 2 =
      ∑ i, ∑ k, w i k * exp (t i + t k) * u i ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [hW.symm, add_comm (t k)]
  have e1 : ∑ i, ∑ k, w i k * (exp (t i + t k) * (u i - u k) ^ 2 / 2) =
      (∑ i, ∑ k, w i k * exp (t i + t k) * u i ^ 2 +
        ∑ i, ∑ k, w i k * exp (t i + t k) * u k ^ 2 -
        2 * ∑ i, ∑ k, w i k * exp (t i + t k) * u i * u k) / 2 := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [e1, hsym, dotProduct_Lmat w hW]
  ring

/-- **The rooted horospherical action** (BCHS (2.59) with (T1), (T3)): with `u_ρ = (0, 0, 1)`
(`t̂_ρ = ŝ_ρ = 0`), `½ ∑_{i,k ∈ V} w_{ik} (−u_i · u_k − 1) = Φ_w(τ̂) + ½ sᵀ 𝓛(τ̂) s`, where
`−u_i · u_k` is computed by `neg_mdot_hxyz`. -/
theorem horo_action_eq (w : V → V → ℝ) (hW : IsWGraph w) (ρ : V) (τ s : {i // i ≠ ρ} → ℝ) :
    (1 / 2) * ∑ i, ∑ k, w i k *
        (-(hx (ext ρ τ i) (ext ρ s i) * hx (ext ρ τ k) (ext ρ s k) +
            hy (ext ρ τ i) (ext ρ s i) * hy (ext ρ τ k) (ext ρ s k) -
            hz (ext ρ τ i) (ext ρ s i) * hz (ext ρ τ k) (ext ρ s k)) - 1) =
      Phi w (ext ρ τ) + (1 / 2) * (s ⬝ᵥ (Lmat w ρ (ext ρ τ)) *ᵥ s) := by
  simp only [neg_mdot_hxyz]
  rw [← half_sum_quad_eq w hW ρ (ext ρ τ) s, Phi, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

/-! ### The `s`-integration -/

variable {w : V → V → ℝ}

theorem exp_neg_Htil (w : V → V → ℝ) (ρ : V) (τ s : {i // i ≠ ρ} → ℝ)
    (hL : 0 < (Lmat w ρ (ext ρ τ)).det) :
    exp (-Htil w ρ τ s) =
      (exp (-Phi w (ext ρ τ)) * exp (-(3 * ∑ i, τ i)) * (Lmat w ρ (ext ρ τ)).det ^ 2) *
        exp (-(1 / 2) * (s ⬝ᵥ (Lmat w ρ (ext ρ τ)) *ᵥ s)) := by
  have h2 : exp (2 * log (Lmat w ρ (ext ρ τ)).det) = (Lmat w ρ (ext ρ τ)).det ^ 2 := by
    rw [mul_comm, exp_mul, exp_log hL]; norm_cast
  rw [Htil, ← h2, ← exp_add, ← exp_add, ← exp_add]
  congr 1; ring

/-- The scalar identity behind (2.61) ⇒ (2.62): `a² / √a · √b^n = b^n · a^{3/2} · b^{−n/2}`. -/
theorem det_pow_identity {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    a ^ 2 * (sqrt b ^ n / sqrt a) = b ^ n * (a ^ (3 / 2 : ℝ) * b ^ (-(n : ℝ) / 2)) := by
  have hsa : sqrt a = a ^ (1 / 2 : ℝ) := sqrt_eq_rpow a
  have hsb : sqrt b ^ n = b ^ ((n : ℝ) / 2) := by
    rw [sqrt_eq_rpow, ← rpow_natCast, ← rpow_mul hb.le]; ring_nf
  have ha2 : a ^ 2 = a ^ (2 : ℝ) := by norm_cast
  have hbn : b ^ n = b ^ (n : ℝ) := by norm_cast
  rw [hsa, hsb, ha2, hbn]
  have hpa : 0 < a ^ (1 / 2 : ℝ) := rpow_pos_of_pos ha _
  have e1 : a ^ (2 : ℝ) = a ^ (3 / 2 : ℝ) * a ^ (1 / 2 : ℝ) := by
    rw [← rpow_add ha]; norm_num
  have e2 : b ^ (n : ℝ) * b ^ (-(n : ℝ) / 2) = b ^ ((n : ℝ) / 2) := by
    rw [← rpow_add hb]; ring_nf
  rw [e1, ← e2]
  field_simp

variable {ρ : V}

/-- `D^{3/2} = det 𝓛^{3/2} e^{−3 ∑ τ}`. -/
theorem D_rpow_three_halves (w : V → V → ℝ) (ρ : V) (τ : {i // i ≠ ρ} → ℝ)
    (hL : 0 < (Lmat w ρ (ext ρ τ)).det) :
    D w ρ (ext ρ τ) ^ (3 / 2 : ℝ) =
      (Lmat w ρ (ext ρ τ)).det ^ (3 / 2 : ℝ) * exp (-(3 * ∑ i, τ i)) := by
  rw [D_eq_det_Lmat, mul_rpow hL.le (exp_pos _).le, ← exp_mul]
  congr 2
  simp only [ext_val]
  ring

/-- **The `s`-integration, `F ≡ 1`** ((2.61) ⇒ (2.62)):
`∫ e^{−H̃(τ, s)} ds = (2π)^{|Λ|} · e^{−Φ(τ̂)} D(τ̂)^{3/2} (2π)^{−|Λ|/2}`. -/
theorem integral_exp_neg_Htil (hW : IsWGraph w) (hconn : (supportGraph w).Connected)
    (τ : {i // i ≠ ρ} → ℝ) :
    ∫ s, exp (-Htil w ρ τ s) =
      (2 * π) ^ Fintype.card {i // i ≠ ρ} * density w ρ (3 / 2) τ := by
  have hP := Lmat_posDef hW hconn ρ (ext ρ τ)
  have hL := hP.det_pos
  simp_rw [exp_neg_Htil w ρ τ _ hL]
  rw [integral_const_mul, ArborealDecay.Gaussian.integral_exp_neg_half_quad hP, density,
    D_rpow_three_halves w ρ τ hL]
  have := det_pow_identity hL (by positivity : (0 : ℝ) < 2 * π) (Fintype.card {i // i ≠ ρ})
  calc _ = exp (-Phi w (ext ρ τ)) * exp (-(3 * ∑ i, τ i)) *
        ((Lmat w ρ (ext ρ τ)).det ^ 2 *
          (sqrt (2 * π) ^ Fintype.card {i // i ≠ ρ} / sqrt (Lmat w ρ (ext ρ τ)).det)) := by ring
    _ = _ := by rw [this]; ring

/-- **The `s`-integration, `F = y_i y_j`** (supplement `thm:pinned-green`, `step:pg-gauss`):
`∫ s_i s_j e^{τ_i + τ_j} e^{−H̃(τ, s)} ds = e^{τ_i + τ_j} (𝓛⁻¹)_{ij} ∫ e^{−H̃(τ, s)} ds`. -/
theorem integral_ss_exp_neg_Htil (hW : IsWGraph w) (hconn : (supportGraph w).Connected)
    (τ : {i // i ≠ ρ} → ℝ) (i j : {i // i ≠ ρ}) :
    ∫ s, s i * s j * exp (τ i + τ j) * exp (-Htil w ρ τ s) =
      exp (τ i + τ j) * (Lmat w ρ (ext ρ τ))⁻¹ i j * ∫ s, exp (-Htil w ρ τ s) := by
  have hP := Lmat_posDef hW hconn ρ (ext ρ τ)
  have hL := hP.det_pos
  simp_rw [exp_neg_Htil w ρ τ _ hL]
  have e : ∀ s : {i // i ≠ ρ} → ℝ,
      s i * s j * exp (τ i + τ j) *
        ((exp (-Phi w (ext ρ τ)) * exp (-(3 * ∑ i, τ i)) * (Lmat w ρ (ext ρ τ)).det ^ 2) *
          exp (-(1 / 2) * (s ⬝ᵥ (Lmat w ρ (ext ρ τ)) *ᵥ s))) =
        (exp (τ i + τ j) *
          (exp (-Phi w (ext ρ τ)) * exp (-(3 * ∑ i, τ i)) * (Lmat w ρ (ext ρ τ)).det ^ 2)) *
          (s i * s j * exp (-(1 / 2) * (s ⬝ᵥ (Lmat w ρ (ext ρ τ)) *ᵥ s))) := fun s => by ring
  simp_rw [e]
  rw [integral_const_mul, integral_const_mul,
    ArborealDecay.Gaussian.integral_coord_mul_coord_mul_exp_neg_half_quad hP]
  ring

/-- Integrability in `s` of the `F = y_i y_j` integrand at fixed `τ`. -/
theorem integrable_ss_exp_neg_Htil (hW : IsWGraph w) (hconn : (supportGraph w).Connected)
    (τ : {i // i ≠ ρ} → ℝ) (i j : {i // i ≠ ρ}) :
    Integrable fun s => s i * s j * exp (τ i + τ j) * exp (-Htil w ρ τ s) := by
  have hP := Lmat_posDef hW hconn ρ (ext ρ τ)
  have hL := hP.det_pos
  simp_rw [exp_neg_Htil w ρ τ _ hL]
  have := (ArborealDecay.Gaussian.integrable_coord_mul_coord_mul_exp_neg_half_quad hP i j).const_mul
    (exp (τ i + τ j) *
      (exp (-Phi w (ext ρ τ)) * exp (-(3 * ∑ i, τ i)) * (Lmat w ρ (ext ρ τ)).det ^ 2))
  refine this.congr (ae_of_all _ fun s => ?_)
  simp only; ring

theorem integrable_exp_neg_Htil (hW : IsWGraph w) (hconn : (supportGraph w).Connected)
    (τ : {i // i ≠ ρ} → ℝ) : Integrable fun s => exp (-Htil w ρ τ s) := by
  have hP := Lmat_posDef hW hconn ρ (ext ρ τ)
  simp_rw [exp_neg_Htil w ρ τ _ hP.det_pos]
  exact (ArborealDecay.Gaussian.integrable_exp_neg_half_quad hP).const_mul _

end

end ArborealDecay.Horo

end
