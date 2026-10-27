module

public import ArborealDecay.Super.Berezin
public import ArborealDecay.Super.Calculus

/-!
# The supersymmetry generator `Q`

Superfunctions on `ℝ^{2N|2N}` (with parameter generators `P`) are functions
`F : (N ⊕ N → ℝ) → SG N P`; the even coordinates are `x_i = p (inl i)` and `y_i = p (inr i)`.
Following BCHS (the display before Theorem 2.8, `h02.tex` L1335–1339),
`Q = ∑_i (ξ_i ∂_{x_i} + η_i ∂_{y_i} - x_i ∂_{η_i} + y_i ∂_{ξ_i})`.
On generators: `Q x_i = ξ_i`, `Q y_i = η_i`, `Q ξ_i = y_i`, `Q η_i = -x_i`.

* `Q_mul`: `Q` is an odd derivation, `Q (F G) = (Q F) G + inv' F (Q G)`.
* `lam p = ½ ∑_i (y_i ξ_i - x_i η_i)` satisfies `Q lam = S` with
  `S p = sfun p - ω`, `sfun p = ½ ∑_i (x_i² + y_i²)`, `ω = ∑_i ξ_i η_i`
  (so `S = ½ ∑_i u_i·u_i` restricted to the integrated variables).
* `Egam γ p = e^{-γ sfun p} ∏_i (1 + γ ξ_i η_i) = e^{-γ S}`, and `Q (Egam γ) = 0`.
-/

@[expose] public section

namespace ArborealDecay.Super

noncomputable section

open CliffordAlgebra Grassmann

set_option linter.unusedSectionVars false

variable {N P : Type*} [Fintype N] [DecidableEq N] [Fintype P] [DecidableEq P]

/-- Points of `ℝ^{2N}`: `x_i = p (inl i)`, `y_i = p (inr i)`. -/
abbrev Pt (N : Type*) := N ⊕ N → ℝ

/-- The unit vector of `x_i`. -/
def ex (i : N) : Pt N := Pi.single (Sum.inl i) 1

/-- The unit vector of `y_i`. -/
def ey (i : N) : Pt N := Pi.single (Sum.inr i) 1

/-- The supersymmetry generator
`Q = ∑_i (ξ_i ∂_{x_i} + η_i ∂_{y_i} - x_i ∂_{η_i} + y_i ∂_{ξ_i})` (BCHS, before Thm 2.8). -/
def Q (F : Pt N → SG N P) (p : Pt N) : SG N P :=
  ∑ i, (ξ i * pd (ex i) F p + η i * pd (ey i) F p - p (Sum.inl i) • dη i (F p) +
    p (Sum.inr i) • dξ i (F p))

/-- `Q` is an odd derivation. -/
theorem Q_mul {F G : Pt N → SG N P} (hF : SDiff F) (hG : SDiff G) (p : Pt N) :
    Q (fun q => F q * G q) p = Q F p * G p + inv' (F p) * Q G p := by
  simp only [Q, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pd_mul hF hG, pd_mul hF hG, dξ_mul, dη_mul]
  have h1 : ∀ X : SG N P, ξ i * (F p * X) = inv' (F p) * (ξ i * X) := fun X => by
    rw [← mul_assoc, ξ, gen_mul_eq, mul_assoc]
  have h2 : ∀ X : SG N P, η i * (F p * X) = inv' (F p) * (η i * X) := fun X => by
    rw [← mul_assoc, η, gen_mul_eq, mul_assoc]
  simp only [mul_add, h1, h2, smul_add, mul_smul_comm, add_mul, sub_mul, smul_mul_assoc,
    mul_sub, ← mul_assoc]
  abel

/-! ### The functions `sfun`, `lam`, `Egam` -/

/-- `sfun p = ½ ∑_i (x_i² + y_i²)`. -/
def sfun (p : Pt N) : ℝ := ∑ k, p k ^ 2 / 2

/-- `ω = ∑_i ξ_i η_i`. -/
def ω : SG N P := ωL (Finset.univ : Finset N).toList

/-- `W γ = ∏_i (1 + γ ξ_i η_i) = e^{γ ω}`. -/
def W (γ : ℝ) : SG N P := WL γ (Finset.univ : Finset N).toList

/-- `λ = ½ ∑_i (y_i ξ_i - x_i η_i)`. -/
def lam (p : Pt N) : SG N P := ∑ i, ((p (Sum.inr i) / 2) • ξ i - (p (Sum.inl i) / 2) • η i)

/-- `S = Q λ = sfun - ω`. -/
def S (p : Pt N) : SG N P := sfun p • 1 - ω

/-- `e^{-γ sfun}`. -/
def gauss (γ : ℝ) (p : Pt N) : ℝ := Real.exp (-γ * sfun p)

/-- `e^{-γ S} = e^{-γ sfun} e^{γ ω}`. -/
def Egam (γ : ℝ) (p : Pt N) : SG N P := gauss γ p • W γ

theorem ω_eq : (ω : SG N P) = ∑ i, aa i := by
  rw [ω, ωL, Finset.sum_map_toList]

theorem inv'_ω : inv' (ω : SG N P) = ω := inv'_ωL _

theorem inv'_W (γ : ℝ) : inv' (W γ : SG N P) = W γ := inv'_WL _ _

theorem sfun_nonneg (p : Pt N) : 0 ≤ sfun p := Finset.sum_nonneg fun _ _ => by positivity

theorem sfun_smul (c : ℝ) (p : Pt N) : sfun (c • p) = c ^ 2 * sfun p := by
  simp only [sfun, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem sfun_eq (p : Pt N) : sfun p = ∑ i, (p (Sum.inl i) ^ 2 / 2 + p (Sum.inr i) ^ 2 / 2) := by
  rw [sfun, Fintype.sum_sum_type, ← Finset.sum_add_distrib]

theorem hasFDerivAt_sfun (p : Pt N) :
    HasFDerivAt sfun (∑ k, p k • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) k) p := by
  unfold sfun
  refine HasFDerivAt.fun_sum fun k _ => ?_
  have h1 := HasFDerivAt.pow
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : N ⊕ N => ℝ) k).hasFDerivAt 2 (x := p)
  have h2 := HasFDerivAt.mul_const h1 (1 / 2 : ℝ)
  convert h2 using 1
  · funext q; simp; ring
  · ext v; simp; ring

theorem fderiv_sfun (p v : Pt N) : fderiv ℝ sfun p v = ∑ k, p k * v k := by
  rw [(hasFDerivAt_sfun p).fderiv]; simp [smul_eq_mul]

theorem contDiff_sfun : ContDiff ℝ 1 (sfun : Pt N → ℝ) := by
  unfold sfun
  exact ContDiff.sum fun k _ => ((contDiff_apply ℝ ℝ k).pow 2).div_const 2

theorem differentiable_sfun : Differentiable ℝ (sfun : Pt N → ℝ) :=
  fun p => (hasFDerivAt_sfun p).differentiableAt

theorem abs_coord_le (p : Pt N) (k : N ⊕ N) : |p k| ≤ ‖p‖ := by
  rw [← Real.norm_eq_abs]; exact norm_le_pi_norm p k

theorem sfun_le (p : Pt N) : sfun p ≤ Fintype.card (N ⊕ N) * ‖p‖ ^ 2 := by
  unfold sfun
  calc ∑ k, p k ^ 2 / 2 ≤ ∑ _k : N ⊕ N, ‖p‖ ^ 2 := Finset.sum_le_sum fun k _ => by
        have h := abs_coord_le p k
        have : p k ^ 2 ≤ ‖p‖ ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
        nlinarith [sq_nonneg (p k)]
    _ = _ := by simp

theorem abs_fderiv_sfun_le (p v : Pt N) :
    |fderiv ℝ sfun p v| ≤ Fintype.card (N ⊕ N) * ‖v‖ * ‖p‖ := by
  rw [fderiv_sfun]
  calc |∑ k, p k * v k| ≤ ∑ k, |p k * v k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : N ⊕ N, ‖v‖ * ‖p‖ := Finset.sum_le_sum fun k _ => by
        rw [abs_mul, mul_comm]
        exact mul_le_mul (abs_coord_le v k) (abs_coord_le p k) (abs_nonneg _) (norm_nonneg _)
    _ = _ := by simp; ring

theorem temp_sfun : Temp (sfun : Pt N → ℝ) := by
  refine ⟨contDiff_sfun, ⟨Fintype.card (N ⊕ N), 2, fun p => ?_⟩, fun v =>
    ⟨Fintype.card (N ⊕ N) * ‖v‖, 1, fun p => ?_⟩⟩
  · rw [abs_of_nonneg (sfun_nonneg p)]
    refine (sfun_le p).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact pow_le_pow_left₀ (norm_nonneg _) (by linarith) 2
  · refine (abs_fderiv_sfun_le p v).trans ?_
    rw [pow_one]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem gauss_pos (γ : ℝ) (p : Pt N) : 0 < gauss γ p := Real.exp_pos _

theorem gauss_le_one {γ : ℝ} (hγ : 0 ≤ γ) (p : Pt N) : gauss γ p ≤ 1 := by
  rw [gauss, Real.exp_le_one_iff]
  nlinarith [sfun_nonneg p]

theorem hasFDerivAt_gauss (γ : ℝ) (p : Pt N) :
    HasFDerivAt (gauss γ) (gauss γ p • (-γ) • fderiv ℝ sfun p) p := by
  have h := HasFDerivAt.exp (HasFDerivAt.const_mul (hasFDerivAt_sfun p) (-γ))
  rw [(hasFDerivAt_sfun p).fderiv]
  exact h

theorem fderiv_gauss (γ : ℝ) (p v : Pt N) :
    fderiv ℝ (gauss γ) p v = -γ * gauss γ p * fderiv ℝ sfun p v := by
  rw [(hasFDerivAt_gauss γ p).fderiv]; simp [smul_eq_mul]; ring

theorem differentiable_gauss (γ : ℝ) : Differentiable ℝ (gauss γ : Pt N → ℝ) :=
  fun p => (hasFDerivAt_gauss γ p).differentiableAt

theorem temp_gauss {γ : ℝ} (hγ : 0 ≤ γ) : Temp (gauss γ : Pt N → ℝ) := by
  refine ⟨?_, ⟨1, 0, fun p => ?_⟩, fun v => ⟨γ * Fintype.card (N ⊕ N) * ‖v‖, 1, fun p => ?_⟩⟩
  · exact (contDiff_const.mul contDiff_sfun).exp
  · rw [abs_of_pos (gauss_pos γ p)]; simpa using gauss_le_one hγ p
  · show |fderiv ℝ (gauss γ) p v| ≤ _
    rw [fderiv_gauss, abs_mul, abs_mul, abs_neg, abs_of_nonneg hγ, abs_of_pos (gauss_pos γ p),
      pow_one]
    have h1 := gauss_le_one hγ p
    have h2 := abs_fderiv_sfun_le p v
    have h3 : 0 ≤ |fderiv ℝ sfun p v| := abs_nonneg _
    calc γ * gauss γ p * |fderiv ℝ sfun p v| ≤ γ * 1 * (Fintype.card (N ⊕ N) * ‖v‖ * ‖p‖) := by
          gcongr
      _ ≤ γ * Fintype.card (N ⊕ N) * ‖v‖ * (1 + ‖p‖) := by
          have : 0 ≤ γ * Fintype.card (N ⊕ N) * ‖v‖ := by positivity
          nlinarith [norm_nonneg p]

theorem hasFDerivAt_coord_half (k : N ⊕ N) (p : Pt N) :
    HasFDerivAt (fun q : Pt N => q k / 2)
      ((1 / 2 : ℝ) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : N ⊕ N => ℝ) k) p := by
  have h := HasFDerivAt.mul_const
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : N ⊕ N => ℝ) k).hasFDerivAt (1 / 2 : ℝ)
    (x := p)
  convert h using 1
  · funext q; simp; ring

theorem fderiv_coord_half (k : N ⊕ N) (p v : Pt N) :
    fderiv ℝ (fun q : Pt N => q k / 2) p v = v k / 2 := by
  rw [(hasFDerivAt_coord_half k p).fderiv]; simp; ring

theorem differentiable_coord_half (k : N ⊕ N) : Differentiable ℝ fun q : Pt N => q k / 2 :=
  fun p => (hasFDerivAt_coord_half k p).differentiableAt

/-! ### Differentiability -/

theorem sdiff_lam : SDiff (lam : Pt N → SG N P) := by
  unfold lam
  exact SDiff.sum _ fun i _ => SDiff.sub
    (SDiff.smul (differentiable_coord_half _) (SDiff.const _))
    (SDiff.smul (differentiable_coord_half _) (SDiff.const _))

theorem sdiff_Egam (γ : ℝ) : SDiff (Egam γ : Pt N → SG N P) :=
  SDiff.smul (differentiable_gauss γ) (SDiff.const _)

/-! ### `Q λ = S` -/

theorem pd_lam (v p : Pt N) :
    pd v (lam : Pt N → SG N P) p = ∑ i, ((v (Sum.inr i) / 2) • ξ i - (v (Sum.inl i) / 2) • η i) := by
  unfold lam
  rw [pd_sum _ fun i _ => SDiff.sub (SDiff.smul (differentiable_coord_half _) (SDiff.const _))
    (SDiff.smul (differentiable_coord_half _) (SDiff.const _))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pd_sub (SDiff.smul (differentiable_coord_half _) (SDiff.const _))
    (SDiff.smul (differentiable_coord_half _) (SDiff.const _)),
    pd_smul_const (differentiable_coord_half _), pd_smul_const (differentiable_coord_half _),
    fderiv_coord_half, fderiv_coord_half]

theorem pd_ex_lam (i : N) (p : Pt N) : pd (ex i) (lam : Pt N → SG N P) p = -((1 / 2 : ℝ) • η i) := by
  rw [pd_lam]
  simp [ex, Pi.single_apply, ite_div, ite_smul]

theorem pd_ey_lam (i : N) (p : Pt N) : pd (ey i) (lam : Pt N → SG N P) p = (1 / 2 : ℝ) • ξ i := by
  rw [pd_lam]
  simp [ey, Pi.single_apply, ite_div, ite_smul]

theorem dξ_lam (i : N) (p : Pt N) :
    dξ i (lam p : SG N P) = (p (Sum.inr i) / 2) • 1 := by
  simp [lam, map_sum, dξ_ξ, dξ_η]

theorem dη_lam (i : N) (p : Pt N) :
    dη i (lam p : SG N P) = -((p (Sum.inl i) / 2) • 1) := by
  simp [lam, map_sum, dη_ξ, dη_η]

/-- `Q λ = S` with `λ = ½ ∑ (y_i ξ_i - x_i η_i)` and `S = ½ ∑ (x_i² + y_i²) - ∑ ξ_i η_i`. -/
theorem Q_lam (p : Pt N) : Q (lam : Pt N → SG N P) p = S p := by
  simp only [Q, pd_ex_lam, pd_ey_lam, dξ_lam, dη_lam, S, sfun_eq, ω_eq, Finset.sum_smul,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : (η i : SG N P) * ξ i = -aa i := by rw [aa, η, ξ, gen_anticomm]
  rw [mul_neg, mul_smul_comm, mul_smul_comm, h, aa]
  rw [← aa]
  simp only [smul_neg, smul_smul, add_smul]
  module

/-! ### `Q e^{-γ S} = 0` -/

theorem pd_Egam (γ : ℝ) (v p : Pt N) :
    pd v (Egam γ : Pt N → SG N P) p = (-γ * gauss γ p * fderiv ℝ sfun p v) • W γ := by
  rw [show (Egam γ : Pt N → SG N P) = fun q => gauss γ q • W γ from rfl,
    pd_smul_const (differentiable_gauss γ), fderiv_gauss]

theorem fderiv_sfun_ex (i : N) (p : Pt N) : fderiv ℝ sfun p (ex i) = p (Sum.inl i) := by
  rw [fderiv_sfun]; simp [ex, Pi.single_apply]

theorem fderiv_sfun_ey (i : N) (p : Pt N) : fderiv ℝ sfun p (ey i) = p (Sum.inr i) := by
  rw [fderiv_sfun]; simp [ey, Pi.single_apply]

theorem dξ_W (γ : ℝ) (i : N) : dξ i (W γ : SG N P) = γ • (η i * W γ) :=
  dξ_WL γ (Finset.nodup_toList _) (by simp)

theorem dη_W (γ : ℝ) (i : N) : dη i (W γ : SG N P) = -(γ • (ξ i * W γ)) :=
  dη_WL γ (Finset.nodup_toList _) (by simp)

theorem Q_Egam (γ : ℝ) (p : Pt N) : Q (Egam γ : Pt N → SG N P) p = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [pd_Egam, pd_Egam, fderiv_sfun_ex, fderiv_sfun_ey, Egam, map_smul, map_smul, dξ_W, dη_W]
  simp only [mul_smul_comm, smul_neg, smul_smul]
  module

end

end ArborealDecay.Super

end
