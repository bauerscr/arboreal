import PtCorr2.Pair.TwoPtZZ
import PtCorr2.Obs.ObsZero

/-!
# The pair part above coalescence: normalised components, Pauli-adjusted constants, the zero mode

Case (2), sources `σ_a, σ_b`. For `F : OE .two Λ` write `n_a F = sA F/sE F`, `n_b F = sB F/sE F`,
`n_{ab} F = sAB F/sE F` (`nA`, `nB`, `nAB`). For `sE X, sE Y ≠ 0` (`nA_mul`, `nB_mul`, `nAB_mul`):

  `n_a(XY) = n_aX + n_aY`, `n_{ab}(XY) = n_{ab}X + n_{ab}Y + n_aX·n_bY + n_bX·n_aY`.

So `n_{ab} - n_a n_b` (the connected pair part) is additive, and `n_{ab}X` of a product of step
constants `X = ∏_{k ≤ i < n} e^{-(u_{i+1} - u_i)}` is the **Pauli-adjusted accumulated pair constant**
(`prodIco_chO_s`): with `γ_{•,i} = -ε(u^{obs}_{i,•})` (`•ε {a, b}`) and `q_i = -ε(u^{obs}_{i,ab})`,

  `n_{ab}X = (q_n - q_k) + (γ_{a,n} - γ_{a,k})(γ_{b,n} - γ_{b,k})`,  `n_aX = γ_{a,n} - γ_{a,k}`.

In the merged picture (`a = b`, Pauli `(ψ̄_aψ_a)² = 0`) the increments of this quantity are
`C_i(a,a)·r̃_i` with `r̃ = r + μ_a(γ_b - γ_{b,k}) + μ_b(γ_a - γ_{a,k})` the Pauli-adjusted pair coupling;
`r̃_k = 0` at coalescence.

**The zero mode** (`sX_omegaCO_cstC`): after the constant covariance `cQ` (Pauli at constant
fields), `s_•(ω_{cQ}F) = ε(F_•) - c·c2(F_•)`. **`zm_pauli_elim`** (pure): if the Pauli-adjusted
pair coupling of the final object is relative to the `a`-vertex,
`c2F_{ab} + Āc2F_b + B̄c2F_a = ρ̃·c2F_a`, then

  `n_{ab}Ω + Ā n_bΩ + B̄ n_aΩ = (x̃ - ρ̃ εF_a)/sE Ω + ρ̃·n_aΩ`,  `x̃ = εF_{ab} + ĀεF_b + B̄εF_a`,

i.e. the large zero-mode constant `c ≈ t/|Λ|` enters only through the one-point part `n_aΩ`, which is
fixed by the one-point function (`r = γ_{a,N} + n_aΩ`).
-/

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD Obs2 Flow2 Flow2.Hist

/-! ### Normalised components -/

section Norm

variable {Λ : Type*}

/-- `n_a F = sA F/sE F`. -/
def nA (F : OE .two Λ) : ℂ := sA F / sE F
/-- `n_b F = sB F/sE F`. -/
def nB (F : OE .two Λ) : ℂ := sB F / sE F
/-- `n_{ab} F = sAB F/sE F`. -/
def nAB (F : OE .two Λ) : ℂ := sAB F / sE F

theorem nA_mul {X Y : OE .two Λ} (hX : sE X ≠ 0) (hY : sE Y ≠ 0) :
    nA (X * Y) = nA X + nA Y := by
  unfold nA; rw [sA_mul, sE_mul]; field_simp; ring

theorem nAB_mul {X Y : OE .two Λ} (hX : sE X ≠ 0) (hY : sE Y ≠ 0) :
    nAB (X * Y) = nAB X + nAB Y + nA X * nB Y + nB X * nA Y := by
  unfold nAB nA nB; rw [sAB_mul, sE_mul]; field_simp; ring

/-- **Zero-mode Pauli elimination** (pure). With `s = x_e - c y_e ≠ 0` and the relative
Pauli-adjusted coupling `y_{ab} + Āy_b + B̄y_a = ρ̃y_a`, the Pauli-adjusted pair part after the zero
mode is `(x̃ - ρ̃x_a)/s + ρ̃·(x_a - cy_a)/s`, `x̃ = x_{ab} + Āx_b + B̄x_a`: `c` only enters through the
one-point part `(x_a - cy_a)/s`. -/
theorem zm_pauli_elim {xe xa xb xab ye ya yb yab cc Ab Bb ρ : ℂ}
    (hρ : yab + Ab * yb + Bb * ya = ρ * ya) :
    (xab - cc * yab) / (xe - cc * ye) + Ab * ((xb - cc * yb) / (xe - cc * ye)) +
        Bb * ((xa - cc * ya) / (xe - cc * ye)) =
      (xab + Ab * xb + Bb * xa - ρ * xa) / (xe - cc * ye) +
        ρ * ((xa - cc * ya) / (xe - cc * ye)) := by
  rw [mul_div_assoc', mul_div_assoc', mul_div_assoc', ← add_div, ← add_div, ← add_div]
  congr 1
  linear_combination (-cc) * hρ

/-- The bound behind `zm_pauli_elim`. -/
theorem zm_pauli_bound {s xa' ρ X : ℂ} {Kx Kρ W : ℝ} (hs : s ≠ 0) (hX : ‖X‖ ≤ Kx * ‖s‖)
    (hρ : ‖ρ‖ ≤ Kρ) (hW : ‖xa'‖ ≤ W) :
    ‖X / s + ρ * xa'‖ ≤ Kx + Kρ * W := by
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_div, div_le_iff₀ (norm_pos_iff.2 hs)]; exact hX
  · rw [norm_mul]; exact mul_le_mul hρ hW (norm_nonneg _) ((norm_nonneg _).trans hρ)

variable [DecidableEq Λ] [Fintype Λ] [Nonempty Λ]

/-- **The zero mode componentwise**: `s_•(ω_{cQ}F) = ε(F_•) - c·c2(F_•)`. -/
theorem sX_omegaCO_cstC (cc : ℂ) (F : OE .two Λ) :
    sE (omegaCO (cstC Λ cc) F) = ε (F : SA .two Λ).e - cc * Suscept.c2 (F : SA .two Λ).e ∧
      sA (omegaCO (cstC Λ cc) F) = ε (F : SA .two Λ).a - cc * Suscept.c2 (F : SA .two Λ).a ∧
      sB (omegaCO (cstC Λ cc) F) = ε (F : SA .two Λ).b - cc * Suscept.c2 (F : SA .two Λ).b ∧
      sAB (omegaCO (cstC Λ cc) F) = ε (F : SA .two Λ).ab - cc * Suscept.c2 (F : SA .two Λ).ab := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold sE; rw [omegaCO_cstC_e]; exact ε.commutes _
  · unfold sA; rw [omegaCO_cstC_two]; exact ε.commutes _
  · unfold sB
    rw [omegaCO_b, omegaC, ← ECC_theta, eps_ECC_cstC_even cc (Step.mem_Ev.1 (OE.b_mem F))]
    exact ε.commutes _
  · unfold sAB; rw [omegaCO_cstC_ab]; exact ε.commutes _

end Norm

/-! ### Step constants: the Pauli-adjusted accumulated pair constant -/

section Hist

variable {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  (P : ObsPts 2 L N)

/-- `ε(e^{-U})_{ab}/ε(e^{-U})_∅ = -εU_{ab} + εU_a εU_b` for the step constant. -/
theorem chO_sAB (o₀ : ObsSt .two L N) (j : ℕ) (t : Hist.Seq (Xs R)) :
    sAB (chO R P o₀ j t) = sE (chO R P o₀ j t) *
      (-(ε ((obsHist R P o₀ (j + 1) t).u : SA .two (Lam 2 L N)).ab -
          ε ((obsHist R P o₀ j t).u : SA .two (Lam 2 L N)).ab) +
        (ε ((obsHist R P o₀ (j + 1) t).u : SA .two (Lam 2 L N)).a -
            ε ((obsHist R P o₀ j t).u : SA .two (Lam 2 L N)).a) *
          (ε ((obsHist R P o₀ (j + 1) t).u : SA .two (Lam 2 L N)).b -
            ε ((obsHist R P o₀ j t).u : SA .two (Lam 2 L N)).b)) := by
  set U := uObsTot P j (stCov R j (rawHist R j t))
    (fullV R j (rawHist R j t) (t j).1 (t j).2.1 (obsHist R P o₀ j t))
    (fullW (rawHist R j t) (rawD R (rawHist R j t).u (t j).2.2) (obsHist R P o₀ j t))
    (fullK R j (rawHist R j t) (rawK R (rawHist R j t).u (t j).2.2) (obsHist R P o₀ j t))
    with hUd
  have hu : (obsHist R P o₀ (j + 1) t).u = (obsHist R P o₀ j t).u + U := rfl
  have hUb0 : bulk U = 0 := by
    rw [hUd, uObsTot, map_sum]; exact sum_eq_zero fun _ _ => bulk_πobs _
  have hUb : bulk (-U) = 0 := by rw [map_neg, hUb0, neg_zero]
  have ea : (((obsHist R P o₀ j t).u + U : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a =
      ((obsHist R P o₀ j t).u : SA .two (Lam 2 L N)).a + (U : SA .two (Lam 2 L N)).a := rfl
  have eb : (((obsHist R P o₀ j t).u + U : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).b =
      ((obsHist R P o₀ j t).u : SA .two (Lam 2 L N)).b + (U : SA .two (Lam 2 L N)).b := rfl
  have eab : (((obsHist R P o₀ j t).u + U : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).ab =
      ((obsHist R P o₀ j t).u : SA .two (Lam 2 L N)).ab + (U : SA .two (Lam 2 L N)).ab := rfl
  rw [hu, ea, eb, eab, map_add, map_add, map_add]
  unfold chO uOutO expU
  simp only [sAB, sE, SetLike.val_smul, SA.smul_ab, SA.smul_e, map_smul, smul_eq_mul]
  rw [oexp_obs_ab hUb, oexp_obs_e hUb, NegMemClass.coe_neg, SA.neg_a, SA.neg_b, SA.neg_ab]
  simp only [Case.s_two, one_smul, map_add, map_smul, map_mul, map_neg, map_one, smul_eq_mul]
  ring

/-- The components of a constant `d·e^x·e^{-U}` with `bulk U = 0`. -/
theorem s_smul_expU_neg (d x : ℂ) {U : OE .two (Lam 2 L N)} (hU : bulk U = 0) :
    sA (d • expU x (-U)) = sE (d • expU x (-U)) * -ε (U : SA .two (Lam 2 L N)).a ∧
      sB (d • expU x (-U)) = sE (d • expU x (-U)) * -ε (U : SA .two (Lam 2 L N)).b ∧
      sAB (d • expU x (-U)) = sE (d • expU x (-U)) *
        (-ε (U : SA .two (Lam 2 L N)).ab +
          ε (U : SA .two (Lam 2 L N)).a * ε (U : SA .two (Lam 2 L N)).b) := by
  have hUb : bulk (-U) = 0 := by rw [map_neg, hU, neg_zero]
  unfold expU
  simp only [sA, sB, sAB, sE, SetLike.val_smul, SA.smul_a, SA.smul_b, SA.smul_ab, SA.smul_e,
    map_smul, smul_eq_mul]
  rw [oexp_obs_ab hUb, oexp_obs_e hUb, oexp_obs_a hUb, oexp_obs_b' hUb, NegMemClass.coe_neg,
    SA.neg_a, SA.neg_b, SA.neg_ab]
  simp only [Case.s_two, one_smul, map_add, map_smul, map_mul, map_neg, map_one, smul_eq_mul]
  refine ⟨by ring, by ring, by ring⟩

theorem bulk_uXO (j : ℕ) (C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ) (V W : OFam .two 2 L N)
    (K : OAct .two 2 L N) (X : Finset (Lam 2 L N)) : bulk (uXO P j C V W K X) = 0 := by
  rw [uXO, map_sum]; exact sum_eq_zero fun _ _ => bulk_πobs _

/-- **The product of the step constants of scales `k ≤ i < n`**: with `g_•(i) = ε(u^{obs}_{i,•})`,
`sA = sE·(g_a(k) - g_a(n))`, `sB = sE·(g_b(k) - g_b(n))` and
`sAB = sE·((g_{ab}(k) - g_{ab}(n)) + (g_a(k) - g_a(n))(g_b(k) - g_b(n)))`. -/
theorem prodIco_chO_s (o₀ : ObsSt .two L N) (t : Hist.Seq (Xs R)) (k : ℕ) :
    ∀ n, k ≤ n →
      let X := ∏ i ∈ Ico k n, chO R P o₀ i t
      let g := fun i => ((obsHist R P o₀ i t).u : SA .two (Lam 2 L N))
      sA X = sE X * (ε (g k).a - ε (g n).a) ∧ sB X = sE X * (ε (g k).b - ε (g n).b) ∧
        sAB X = sE X * ((ε (g k).ab - ε (g n).ab) +
          (ε (g k).a - ε (g n).a) * (ε (g k).b - ε (g n).b)) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp [sA, sB, sAB, sE]
  | succ n hkn ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    simp only at h1 h2 h3 ⊢
    rw [prod_Ico_succ_top hkn, sA_mul, sB_mul, sAB_mul, sE_mul, h1, h2, h3, chO_sA, chO_sB,
      chO_sAB]
    refine ⟨by ring, by ring, by ring⟩

end Hist

end

end PtCorr2
