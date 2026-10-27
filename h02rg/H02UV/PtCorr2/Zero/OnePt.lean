import PtCorr2.Zero.Ward2

/-!
# The one-point function `⟨ψ̄_0ψ_0⟩` and the zero-mode coefficient from the model

For the initial model `V_0 = (0, 0, μ₀, b)` with `b > 0`, `m² > 0` and `b ≤ μ₀ + m²`
(`h = (μ₀ + m²)/b - 1 ≥ 0`), the bridge to the `ℍ^{0|2}` model (`Ward.bridge_avg_z`,
`Ward.bridge_avg_ξη`, `β = 1/b`, `s₀ = 0`, `c² = b`) and the ghost-forest representation
(`H02.arborealProb_ghost_zforest`, `H02.arborealProb_ghost_xieta`) give:

* `onept_avg0_mem`: `1 - b⟨ψ̄_0ψ_0⟩ = ⟨z_0⟩_{β,h} = P_{β,h}[0 ↔ g] ∈ [0, 1]`;
* `onept_avg0_two_mem`: `b⟨ψ̄_0ψ_x⟩ = ⟨ξ_0η_x⟩_{β,h} = P_{β,h}[0 ↔ x, 0 ↮ g] ∈ [0, 1]`;
* `onept_avg0_h0`: at `h = 0` (`b = μ₀ + m²`) the Ward identity gives `⟨ψ̄_0ψ_0⟩ = 1/b` exactly.

Combined with the dressed susceptibility along a trajectory (`ward2`), with
`X = ã π_N/(1 + ũ) + ∑_{j<N} c_jπ_j/ρ_j` and `r = 1 - b⟨ψ̄_0ψ_0⟩ ∈ [0,1]`
(`ward2_onept`): `(μ₀ + m² - b) ∑_x⟨ψ̄_0ψ_x⟩ = r`, and for `b < μ₀ + m²`
`X = m² - m⁴ r/(μ₀ + m² - b)`; in particular `X` is real and `m² - m⁴/(μ₀ + m² - b) ≤ X ≤ m²`.
-/

namespace PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Step2 Step

variable {L N : ℕ} [NeZero L]

theorem onept_h_nonneg {b μ₀ msq : ℝ} (hb : 0 < b) (hh : b ≤ μ₀ + msq) :
    0 ≤ (μ₀ + msq) / b - 1 := by
  rw [sub_nonneg, le_div_iff₀ hb]; linarith

/-- `⟨Z_0⟩_C ≠ 0` for the initial model, `b > 0`, `h ≥ 0`. -/
theorem onept_Zb_ne {b μ₀ msq : ℝ} (hb : 0 < b) (hm0 : 0 < msq) (hh : b ≤ μ₀ + msq) :
    Obs.Zb (Suscept.Cov 2 L N msq) (VE (V0c b μ₀) (univ : Finset (Lam 2 L N))) ≠ 0 := by
  have hV := Vh_eq_V0 (μ₀ := μ₀) (msq := msq) hb
  simp only [V0c]
  rw [← hV]
  intro h0
  have hB := Ward.bridge_Z (d := 2) (L := L) (N := N) (β := 1 / b) (h := (μ₀ + msq) / b - 1)
    (s₀ := 0) (by positivity) (by norm_num) hm0
  rw [h0, mul_zero] at hB
  have hpos := H02.expect_one_pos (Ward.nnW_symm (d := 2) (L := L) (N := N) (1 / b))
    (Ward.nnW_nonneg (by positivity)) (h := fun _ => (μ₀ + msq) / b - 1)
    (fun _ => onept_h_nonneg hb hh)
  exact Complex.ofReal_ne_zero.2 hpos.ne' hB

/-- `⟨z_a⟩_{β,h} ∈ [0, 1]` for `β ≥ 0`, `h ≥ 0` (it is `P[a ↔ g]`). -/
theorem onept_avg_z_mem {β h : ℝ} (hβ : 0 ≤ β) (hh : 0 ≤ h) (a : Lam 2 L N) :
    0 ≤ H02.avg (Ward.nnW 2 L N β) (fun _ => h) (H02.z a) ∧
      H02.avg (Ward.nnW 2 L N β) (fun _ => h) (H02.z a) ≤ 1 := by
  have hw := Ward.nnW_symm (d := 2) (L := L) (N := N) β
  have hw0 := Ward.nnW_nonneg (d := 2) (L := L) (N := N) hβ
  rw [← H02.arborealProb_ghost_zforest hw hw0 (h := fun _ => h) (fun _ => hh) a]
  exact ⟨H02.arborealProb_nonneg _ (H02.ghostW_nonneg hw0 (fun _ => hh)) _,
    H02.arborealProb_le_one _ (H02.ghostW_nonneg hw0 (fun _ => hh)) _⟩

/-- `⟨ξ_aη_x⟩_{β,h} ∈ [0, 1]` for `β ≥ 0`, `h ≥ 0` (it is `P[a ↔ x, a ↮ g]`). -/
theorem onept_avg_xieta_mem {β h : ℝ} (hβ : 0 ≤ β) (hh : 0 ≤ h) (a x : Lam 2 L N) :
    0 ≤ H02.avg (Ward.nnW 2 L N β) (fun _ => h) (H02.ξ a * H02.η x) ∧
      H02.avg (Ward.nnW 2 L N β) (fun _ => h) (H02.ξ a * H02.η x) ≤ 1 := by
  have hw := Ward.nnW_symm (d := 2) (L := L) (N := N) β
  have hw0 := Ward.nnW_nonneg (d := 2) (L := L) (N := N) hβ
  rw [← H02.arborealProb_ghost_xieta hw hw0 (h := fun _ => h) (fun _ => hh) a x]
  exact ⟨H02.arborealProb_nonneg _ (H02.ghostW_nonneg hw0 (fun _ => hh)) _,
    H02.arborealProb_le_one _ (H02.ghostW_nonneg hw0 (fun _ => hh)) _⟩

theorem onept_b_eq (b : ℝ) : ((1 + 0) / (1 / b) : ℝ) = b := by
  rw [add_zero, one_div_one_div]

/-- **`1 - b⟨ψ̄_0ψ_0⟩ ∈ [0, 1]`**: it is `⟨z_0⟩_{β,h} = P_{β,h}[0 ↔ g]`. -/
theorem onept_avg0_mem {b μ₀ msq : ℝ} (hb : 0 < b) (hm0 : 0 < msq) (hh : b ≤ μ₀ + msq) :
    ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧ 1 - (b : ℂ) * avg0 L N msq b μ₀ (psibar 0 * psi 0) = r := by
  have hZ := onept_Zb_ne (L := L) (N := N) hb hm0 hh
  have hV := Vh_eq_V0 (μ₀ := μ₀) (msq := msq) hb
  have hz := onept_avg_z_mem (L := L) (N := N) (β := 1 / b) (by positivity)
    (onept_h_nonneg hb hh) 0
  simp only [avg0, V0c] at hZ ⊢
  rw [← hV] at hZ ⊢
  refine ⟨_, hz.1, hz.2, ?_⟩
  rw [Ward.bridge_avg_z (s₀ := 0) (by positivity) (by norm_num) hm0 hZ, onept_b_eq b]

/-- **`b⟨ψ̄_0ψ_x⟩ ∈ [0, 1]`**: it is `⟨ξ_0η_x⟩_{β,h} = P_{β,h}[0 ↔ x, 0 ↮ g]`. -/
theorem onept_avg0_two_mem {b μ₀ msq : ℝ} (hb : 0 < b) (hm0 : 0 < msq) (hh : b ≤ μ₀ + msq)
    (x : Lam 2 L N) :
    ∃ p : ℝ, 0 ≤ p ∧ p ≤ 1 ∧ (b : ℂ) * avg0 L N msq b μ₀ (psibar 0 * psi x) = p := by
  have hV := Vh_eq_V0 (μ₀ := μ₀) (msq := msq) hb
  have hz := onept_avg_xieta_mem (L := L) (N := N) (β := 1 / b) (by positivity)
    (onept_h_nonneg hb hh) 0 x
  simp only [avg0, V0c]
  rw [← hV]
  refine ⟨_, hz.1, hz.2, ?_⟩
  rw [Ward.bridge_avg_ξη (s₀ := 0) (by positivity) (by norm_num) hm0, onept_b_eq b]

/-- **At `h = 0`** (`b = μ₀ + m²`): `⟨ψ̄_0ψ_0⟩ = 1/b` (the Ward identity with `⟨z_0⟩ = 0`). -/
theorem onept_avg0_h0 {b μ₀ msq : ℝ} (hb : 0 < b) (hm0 : 0 < msq) (hh : b = μ₀ + msq) :
    avg0 L N msq b μ₀ (psibar 0 * psi 0) = 1 / (b : ℂ) := by
  have hw := ward_V0 (L := L) (N := N) hb hm0 (onept_Zb_ne hb hm0 hh.le)
  rw [show μ₀ + msq - b = 0 by linarith, Complex.ofReal_zero, zero_mul] at hw
  have hb' : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hb.ne'
  field_simp
  linear_combination -hw

/-- The algebra: `χ = m^{-2} - m^{-4}X` and `(μ₀ + m² - b)χ = r` give `X = m² - m⁴r/(μ₀ + m² - b)`. -/
theorem onept_X_eq {m c r : ℝ} {χ X : ℂ} (hm : 0 < m) (hc : 0 < c)
    (hχ : χ = 1 / (m : ℂ) - (1 / (m : ℂ)) ^ 2 * X) (hr : (c : ℂ) * χ = r) :
    X = (m : ℂ) - (m : ℂ) ^ 2 * r / c := by
  have hm' : (m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hm.ne'
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  rw [hχ] at hr
  field_simp at hr ⊢
  linear_combination -hr

/-- `X = m² - m⁴r/c` with `r ∈ [0,1]`, `c > 0`: `‖X - m²‖ ≤ m⁴/c`. -/
theorem onept_X_bound {m c r : ℝ} {X : ℂ} (hc : 0 < c) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hX : X = (m : ℂ) - (m : ℂ) ^ 2 * r / c) : ‖X - m‖ ≤ m ^ 2 / c := by
  rw [hX, show (m : ℂ) - (m : ℂ) ^ 2 * r / c - m = ((-(m ^ 2 * r / c) : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity)]
  rw [mul_div_assoc, div_eq_mul_one_div (m ^ 2) c]
  exact mul_le_mul_of_nonneg_left (by rw [div_le_div_iff_of_pos_right hc]; exact hr1)
    (sq_nonneg m)

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- **The one-point function along a trajectory** (hypotheses of `ward2`, `0 < b ≤ μ₀ + m²`):
with `r = 1 - b⟨ψ̄_0ψ_0⟩ ∈ [0, 1]` and `X = ã π_N/(1 + ũ) + ∑_{j<N} c_jπ_j/ρ_j`,
* `(μ₀ + m² - b) ∑_x⟨ψ̄_0ψ_x⟩ = r` and `b⟨ψ̄_0ψ_x⟩ ∈ [0, 1]` for every `x`;
* `b = μ₀ + m²` ⟹ `⟨ψ̄_0ψ_0⟩ = 1/b`;
* `b < μ₀ + m²` ⟹ `X = m² - m⁴r/(μ₀ + m² - b)`, so `‖X - m²‖ ≤ m⁴/(μ₀ + m² - b)`. -/
theorem ward2_onept {Nh : ℕ} (hN : Nh + 2 = N) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < R.msq)
    (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt R j)
    (hVL : ValidAtL R Nh) {b μ₀ : ℝ} (hb : 0 < b) (hh : b ≤ μ₀ + R.msq)
    (hVN : ∀ c ∈ blockIdx (L := L) (N := N) (Nh + 1),
      ((lastOut R Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)).V c : Alg 2 L N) =
        Step2.Vcoup (lastOut R Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)).κ (blockSet (Nh + 1) c)) :
    let t := traj (rgData R) ((L : ℝ) ^ 2) b μ₀
    let X := aFin (Nh + 1) (lastOut R Nh t) * πh R (Nh + 2) t /
        (1 + uFin (Nh + 1) (lastOut R Nh t) (zmRaw R (Nh + 1) (lastOut R Nh t).ζ)) +
      ∑ j ∈ range (Nh + 2), ch₀ R j t * πh R j t / ρh R j t
    let χ := ∑ x : Lam 2 L N, avg0 L N R.msq b μ₀ (psibar 0 * psi x)
    ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧
      1 - (b : ℂ) * avg0 L N R.msq b μ₀ (psibar 0 * psi 0) = r ∧
      ((μ₀ + R.msq - b : ℝ) : ℂ) * χ = r ∧
      (∀ x : Lam 2 L N, ∃ p : ℝ, 0 ≤ p ∧ p ≤ 1 ∧
        (b : ℂ) * avg0 L N R.msq b μ₀ (psibar 0 * psi x) = p) ∧
      (b = μ₀ + R.msq → avg0 L N R.msq b μ₀ (psibar 0 * psi 0) = 1 / (b : ℂ)) ∧
      (b < μ₀ + R.msq →
        X = (R.msq : ℂ) - (R.msq : ℂ) ^ 2 * r / ((μ₀ + R.msq - b : ℝ) : ℂ) ∧
        ‖X - R.msq‖ ≤ R.msq ^ 2 / (μ₀ + R.msq - b)) := by
  intro t X χ
  obtain ⟨-, hS, hW⟩ := ward2 R hN hρ1 hspl hm0 hm hV hVL hb hh hVN
  obtain ⟨r, hr0, hr1, hr⟩ := onept_avg0_mem (L := L) (N := N) hb hm0 hh
  have hcr : ((μ₀ + R.msq - b : ℝ) : ℂ) * χ = r := hW.trans hr
  refine ⟨r, hr0, hr1, hr, hcr, fun x => onept_avg0_two_mem hb hm0 hh x,
    fun h0 => onept_avg0_h0 hb hm0 h0, fun hlt => ?_⟩
  have hc : 0 < μ₀ + R.msq - b := by linarith
  have hX := onept_X_eq hm0 hc hS hcr
  exact ⟨hX, onept_X_bound hc hr0 hr1 hX⟩

end

end PtCorr2
