import PtCorr2.Zero.ZeroInit

/-!
# The Ward identity for the dressed flow (`cor:ward`, `lem:square` route, step 1)

With `V_0 = (0, 0, μ₀, b)` (`V0c`) and `⟨F⟩ = ⟨e^{-V_0(Λ)}F⟩_C/⟨e^{-V_0(Λ)}⟩_C` (`Obs.avg`), the
bridge (`Ward.bridge_avg_z`, `Ward.bridge_avg_ξη` with `β = 1/b`, `h = (μ₀ + m²)/b - 1`, `s₀ = 0`,
`c² = b`) turns the `ℍ^{0|2}` Ward identity `⟨z_0⟩ = h ∑_x ⟨ξ_0η_x⟩` (`H02.ward`) into

  `1 - b ⟨ψ̄_0ψ_0⟩ = (μ₀ + m² - b) ∑_x ⟨ψ̄_0ψ_x⟩`        (`ward_V0`, needs `⟨Z_0⟩_C ≠ 0`).

Along a trajectory of the flow (`ward2`), under `b > 0` and `b ≤ μ₀ + m²` (`h ≥ 0`):
* `1 + ũ_{N,N} ≠ 0` (`one_add_uFin_ne_zero`);
* (susceptibility) `∑_x ⟨ψ̄_0ψ_x⟩ = m^{-2} - m^{-4}[ã π_N/(1 + ũ) + ∑_{j<N} c_jπ_j/ρ_j]`
  (`suscept2` with translation invariance `Suscept.sum_transl`, `Γ_0 = C`, `Z_0 = e^{-V_0(Λ)}`);
* (Ward) `(μ₀ + m² - b) ∑_x ⟨ψ̄_0ψ_x⟩ = 1 - b⟨ψ̄_0ψ_0⟩`.

`ward2_atilde` solves for the zero-mode coefficient when `b < μ₀ + m²`:
`ã π_N/(1 + ũ) = m² - ∑_{j<N} c_jπ_j/ρ_j - m⁴ (1 - b⟨ψ̄_0ψ_0⟩)/(μ₀ + m² - b)`.
In the old `cor:ward` the identity determines `h`; here the initial mass coupling `μ₀` of the
trajectory plays the role of `h` (`h b = μ₀ + m² - b`).
-/

namespace PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Step2 Step

variable {L N : ℕ} [NeZero L]

/-- The initial couplings `V_0 = (z, y, a, b) = (0, 0, μ₀, b)`. -/
abbrev V0c (b μ₀ : ℝ) : Loc.Vcoup := ⟨0, 0, (μ₀ : ℂ), (b : ℂ)⟩

/-- The model expectation `⟨F⟩ = ⟨e^{-V_0(Λ)}F⟩_C/⟨e^{-V_0(Λ)}⟩_C`. -/
abbrev avg0 (L N : ℕ) [NeZero L] (msq b μ₀ : ℝ) (F : Alg 2 L N) : ℂ :=
  Obs.avg (Suscept.Cov 2 L N msq) (VE (V0c b μ₀) (univ : Finset (Lam 2 L N))) F

/-- **The Ward identity in `ψ`-variables** for the initial model `V_0 = (0, 0, μ₀, b)`:
`1 - b⟨ψ̄_0ψ_0⟩ = (μ₀ + m² - b) ∑_x ⟨ψ̄_0ψ_x⟩`, provided `⟨Z_0⟩_C ≠ 0`. -/
theorem ward_V0 {b μ₀ msq : ℝ} (hb : 0 < b) (hm0 : 0 < msq)
    (hZ : Obs.Zb (Suscept.Cov 2 L N msq) (VE (V0c b μ₀) (univ : Finset (Lam 2 L N))) ≠ 0) :
    1 - (b : ℂ) * avg0 L N msq b μ₀ (psibar 0 * psi 0) =
      ((μ₀ + msq - b : ℝ) : ℂ) * ∑ x : Lam 2 L N, avg0 L N msq b μ₀ (psibar 0 * psi x) := by
  have hV := Vh_eq_V0 (μ₀ := μ₀) (msq := msq) hb
  have hβ : (0 : ℝ) < 1 / b := by positivity
  have hs : (-1 : ℝ) < 0 := by norm_num
  simp only [avg0, V0c] at hZ ⊢
  rw [← hV] at hZ ⊢
  have hw := H02.ward (Ward.nnW 2 L N (1 / b)) (Ward.nnW_symm _) ((μ₀ + msq) / b - 1)
    (0 : Lam 2 L N)
  have hw' := hw.1.trans (hw.2.1.trans hw.2.2)
  have hc := congrArg (fun r : ℝ => (r : ℂ)) hw'
  rw [Ward.bridge_avg_z hβ hs hm0 hZ, Complex.ofReal_mul, Complex.ofReal_sum] at hc
  simp only [Ward.bridge_avg_ξη hβ hs hm0] at hc
  have e1 : ((1 + 0) / (1 / b) : ℝ) = b := by rw [add_zero, one_div_one_div]
  rw [e1] at hc
  rw [hc, ← mul_sum, ← mul_assoc]
  congr 1
  rw [← Complex.ofReal_mul]
  congr 1
  field_simp

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- `∑_x ⟨ψ̄_0ψ_x⟩ = |Λ|^{-1} ∑_{x,y} ⟨Z_0ψ̄_xψ_y⟩_{Γ_0}/⟨Z_0⟩_{Γ_0}` (translation invariance). -/
theorem sum_avg0_eq (hL7 : 7 ≤ L) (hm0 : 0 < R.msq) (hN : 1 ≤ N) (t : Hist.Seq (Xs R))
    {b μ₀ : ℝ} (ht : t 0 = (b, μ₀, 0)) :
    ∑ x : Lam 2 L N, avg0 L N R.msq b μ₀ (psibar 0 * psi x) =
      (Fintype.card (Lam 2 L N) : ℂ)⁻¹ *
        (∑ x : Lam 2 L N, ∑ y : Lam 2 L N,
          omegaC (Γh R 0 t) ((Zh R 0 t : Alg 2 L N) * (psibar x * psi y))) /
        omegaC (Γh R 0 t) (Zh R 0 t : Alg 2 L N) := by
  rw [Γh_zero_eq_Cov R hL7 hm0 hN t, Zh_zero_eq_Z0 R t ht]
  simp only [← omega_eq_omegaC]
  have h := Suscept.sum_transl (d := 2) (L := L) hN hm0 (V0c b μ₀)
  show ∑ x : Lam 2 L N, omega (Suscept.Cov 2 L N R.msq) (Suscept.Z0 2 L N (V0c b μ₀) * (psibar 0 * psi x)) /
      omega (Suscept.Cov 2 L N R.msq) (Suscept.Z0 2 L N (V0c b μ₀)) = _
  rw [← sum_div, h, mul_div_assoc]

/-- **The Ward step along a trajectory**: for `b > 0` and `b ≤ μ₀ + m²` (`h ≥ 0`),
`1 + ũ_{N,N} ≠ 0`, the dressed susceptibility formula for `∑_x ⟨ψ̄_0ψ_x⟩`, and the Ward identity
`(μ₀ + m² - b) ∑_x ⟨ψ̄_0ψ_x⟩ = 1 - b⟨ψ̄_0ψ_0⟩`. -/
theorem ward2 {Nh : ℕ} (hN : Nh + 2 = N) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < R.msq)
    (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt R j)
    (hVL : ValidAtL R Nh) {b μ₀ : ℝ} (hb : 0 < b) (hh : b ≤ μ₀ + R.msq)
    (hVN : ∀ c ∈ blockIdx (L := L) (N := N) (Nh + 1),
      ((lastOut R Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)).V c : Alg 2 L N) =
        Step2.Vcoup (lastOut R Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)).κ (blockSet (Nh + 1) c)) :
    let t := traj (rgData R) ((L : ℝ) ^ 2) b μ₀
    1 + uFin (Nh + 1) (lastOut R Nh t) (zmRaw R (Nh + 1) (lastOut R Nh t).ζ) ≠ 0 ∧
    ∑ x : Lam 2 L N, avg0 L N R.msq b μ₀ (psibar 0 * psi x) =
      1 / (R.msq : ℂ) - (1 / (R.msq : ℂ)) ^ 2 *
        (aFin (Nh + 1) (lastOut R Nh t) * πh R (Nh + 2) t /
            (1 + uFin (Nh + 1) (lastOut R Nh t) (zmRaw R (Nh + 1) (lastOut R Nh t).ζ)) +
          ∑ j ∈ range (Nh + 2), ch₀ R j t * πh R j t / ρh R j t) ∧
    ((μ₀ + R.msq - b : ℝ) : ℂ) * ∑ x : Lam 2 L N, avg0 L N R.msq b μ₀ (psibar 0 * psi x) =
      1 - (b : ℂ) * avg0 L N R.msq b μ₀ (psibar 0 * psi 0) := by
  intro t
  have hL7 : 7 ≤ L := by have := hVL.1; norm_num at this; omega
  obtain ⟨hZ, hu⟩ := one_add_uFin_ne_zero R hN hρ1 hspl hm0 hm hV hVL hb hh hVN
  have ht := traj_zero_eq R b μ₀
  have hsum := sum_avg0_eq R hL7 hm0 (by omega) t ht
  refine ⟨hu, ?_, ?_⟩
  · rw [hsum]
    exact suscept2 R hL7 hN hρ1 hspl hm0 hm hV hVL b μ₀ hVN hZ
  · have hZb : Obs.Zb (Suscept.Cov 2 L N R.msq) (VE (V0c b μ₀) (univ : Finset (Lam 2 L N))) ≠ 0 := by
      have := omega_Zh_zero_eq R hL7 hm0 (by omega) t hb ht
      rw [Vh_eq_V0 hb] at this
      rw [← this]; exact hZ
    exact (ward_V0 hb hm0 hZb).symm

/-- **The zero-mode coefficient from the Ward identity** (`b < μ₀ + m²`, i.e. `h > 0`):
`ã π_N/(1 + ũ) = m² - ∑_{j<N} c_jπ_j/ρ_j - m⁴ (1 - b⟨ψ̄_0ψ_0⟩)/(μ₀ + m² - b)`. -/
theorem ward2_atilde {Nh : ℕ} (hN : Nh + 2 = N) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < R.msq)
    (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt R j)
    (hVL : ValidAtL R Nh) {b μ₀ : ℝ} (hb : 0 < b) (hh : b < μ₀ + R.msq)
    (hVN : ∀ c ∈ blockIdx (L := L) (N := N) (Nh + 1),
      ((lastOut R Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)).V c : Alg 2 L N) =
        Step2.Vcoup (lastOut R Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)).κ (blockSet (Nh + 1) c)) :
    let t := traj (rgData R) ((L : ℝ) ^ 2) b μ₀
    aFin (Nh + 1) (lastOut R Nh t) * πh R (Nh + 2) t /
        (1 + uFin (Nh + 1) (lastOut R Nh t) (zmRaw R (Nh + 1) (lastOut R Nh t).ζ)) =
      (R.msq : ℂ) - ∑ j ∈ range (Nh + 2), ch₀ R j t * πh R j t / ρh R j t -
        (R.msq : ℂ) ^ 2 * (1 - (b : ℂ) * avg0 L N R.msq b μ₀ (psibar 0 * psi 0)) /
          ((μ₀ + R.msq - b : ℝ) : ℂ) := by
  intro t
  obtain ⟨-, hS, hW⟩ := ward2 R hN hρ1 hspl hm0 hm hV hVL hb hh.le hVN
  have hc : ((μ₀ + R.msq - b : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by linarith)
  have hmC : (R.msq : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hm0.ne'
  rw [← hW, hS]
  field_simp
  ring

end

end PtCorr2
