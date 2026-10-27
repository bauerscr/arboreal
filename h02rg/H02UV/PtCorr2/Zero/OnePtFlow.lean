import PtCorr2.Zero.EpsFlow
import PtCorr2.Zero.OnePt

/-!
# The one-point function along the flow

`thm_ward_flow_onept`: the conclusions of `thm_ward_flow_rho` (same construction of the
constants, from `thm_zero_mode_flow`), and, along every admissible trajectory with
`b ≤ μ₀ + m²` (`h ≥ 0`), the model bounds of `ward2_onept`: with `r = 1 - b⟨ψ̄_0ψ_0⟩ ∈ [0, 1]`
(`= ⟨z_0⟩ = P[0 ↔ g]`), `(μ₀ + m² - b)∑_x⟨ψ̄_0ψ_x⟩ = r`, `b⟨ψ̄_0ψ_x⟩ ∈ [0, 1]`,
`⟨ψ̄_0ψ_0⟩ = 1/b` at `h = 0`, and for `h > 0` the zero-mode coefficient
`X = ãπ_N/(1 + ũ) + ∑_{j<N} c_jπ_j/ρ_j = m² - m⁴r/(μ₀ + m² - b)`, `‖X - m²‖ ≤ m⁴/(μ₀ + m² - b)`.
-/

namespace PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2 Step2.D2 Step

/-- **The Ward step and the one-point function along the flow.** -/
theorem thm_ward_flow_onept : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ κ cm cT ε Cf B : ℝ, 0 < ℓ ∧ 0 < A ∧ 0 < ρ ∧ ρ ≤ 1 / 8 ∧ 0 < ε ∧ 0 ≤ Cf ∧ 0 ≤ B ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N →
    ∀ Nh : ℕ, Nh + 2 = N →
    ∀ m ∈ mRange L N, ∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
      let R' := R.withMsq m
      let t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀
      let out := lastOut R' Nh t
      let U := 1 + uFin (Nh + 1) out (zmRaw R' (Nh + 1) out.ζ)
      let χ := ∑ x : Lam 2 L N, avg0 L N m b μ₀ (psibar 0 * psi x)
      ZeroModeOut R' Nh Cf t ∧
      (∀ j < Nh + 2, ‖eh R' t j‖ ≤ B * m * (L : ℝ) ^ (2 * j)) ∧
      ∑ i ∈ range (Nh + 2), ‖dQ (ζr R' t) (eh R' t) i - 1‖ ≤ 5 * B * ρ ∧
      (b ≤ μ₀ + m →
        ‖χ - (1 / ((m : ℂ) * Zr R' t (Nh + 2)) -
            (1 / (m : ℂ)) ^ 2 * (aFin (Nh + 1) out / Zr R' t (Nh + 2)) / (Zr R' t (Nh + 2) * U))‖ ≤
          (‖1 / (m : ℂ)‖ * ∑ j ∈ range (Nh + 2), ‖ζr R' t j‖ / (‖Zr R' t j‖ * ‖1 + ζr R' t j‖) +
            ‖1 / (m : ℂ)‖ ^ 2 * (‖aFin (Nh + 1) out / Zr R' t (Nh + 2)‖ /
              (‖Zr R' t (Nh + 2)‖ * ‖U‖))) *
            (10 * B * Real.exp (5 * B / 4) * ρ)) ∧
      (b ≤ μ₀ + m →
        let X := aFin (Nh + 1) out * πh R' (Nh + 2) t / U +
          ∑ j ∈ range (Nh + 2), ch₀ R' j t * πh R' j t / ρh R' j t
        ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧
          1 - (b : ℂ) * avg0 L N m b μ₀ (psibar 0 * psi 0) = r ∧
          ((μ₀ + m - b : ℝ) : ℂ) * χ = r ∧
          (∀ x : Lam 2 L N, ∃ p : ℝ, 0 ≤ p ∧ p ≤ 1 ∧
            (b : ℂ) * avg0 L N m b μ₀ (psibar 0 * psi x) = p) ∧
          (b = μ₀ + m → avg0 L N m b μ₀ (psibar 0 * psi 0) = 1 / (b : ℂ)) ∧
          (b < μ₀ + m →
            X = (m : ℂ) - (m : ℂ) ^ 2 * r / ((μ₀ + m - b : ℝ) : ℂ) ∧
            ‖X - m‖ ≤ m ^ 2 / (μ₀ + m - b))) := by
  obtain ⟨L₀, h⟩ := thm_zero_mode_flow
  refine ⟨max L₀ 7, fun L _ hL => ?_⟩
  have hL7 : 7 ≤ L := le_trans (le_max_right _ _) hL
  obtain ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, Cf, Cb, hℓ, hA, hρ, hε, hκ0, hκ1, hcg, hcm, hcT, hKe,
    hCf, hCb, hCbε, hρ8, hspl, H⟩ := h L (le_trans (le_max_left _ _) hL)
  obtain ⟨-, B, hB, hE⟩ := id hspl
  refine ⟨ℓ, A, ρ, κ, cm, cT, ε, Cf, B, hℓ, hA, hρ, hρ8, hε, hCf, hB,
    fun N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm => ?_⟩
  intro R' t out U χ
  obtain ⟨main, hZMO, -⟩ := H N R hP hi0 hRℓ hRA hRρ hN Nh hNh
  obtain ⟨-, -, hGB, -, -, -, -, -, -, hval⟩ := main
  obtain ⟨hV, hVL⟩ := hval m hm
  have hspl' : SplitSmall R'.P L R'.ρ := by
    show SplitSmall R.P L R.ρ
    rw [hP, hRρ]; exact hspl
  have hE' : EpsZeroSmall R'.P L R'.ρ B := by
    show EpsZeroSmall R.P L R.ρ B
    rw [hP, hRρ]; exact hE
  have hρ1 : R'.ρ < 1 := by show R.ρ < 1; rw [hRρ]; linarith
  have hρ0 : 0 ≤ R'.ρ := by show 0 ≤ R.ρ; rw [hRρ]; exact hρ.le
  have hρ8' : R'.ρ ≤ 1 / 8 := by show R.ρ ≤ 1 / 8; rw [hRρ]; exact hρ8
  have hm0 : 0 < R'.msq := hm.1
  have hmN : R'.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) := hm.2
  have hRI : ∀ j ≤ Nh + 1, RawInv R' j (rawHist R' j t) := rawInv_histU R' hV hVL t
  have hZ : ∀ i, Zr R' t i ≠ 0 := fun i => by
    obtain ⟨hZp, -, hb⟩ := rawHist_struct R' hρ0 i t
    show (rawHist R' i t).Z ≠ 0
    rw [hZp]
    exact prod_ne_zero_iff.2 fun k _ => Step2.one_add_ne_zero ((hb k).trans_lt hρ1)
  have hez : ∀ j < Nh + 2, ‖ζr R' t j / (1 + ζr R' t j) * eh R' t j‖ ≤ 1 / 2 ∧
      ‖eh R' t j‖ ≤ B * m * (L : ℝ) ^ (2 * j) := fun j hj =>
    eh_zp_bound R' hL7 hρ0 hE' (by omega) hm0 hmN t (by omega) (hRI j (by omega)) (hZ j)
  have hSb : ∑ i ∈ range (Nh + 2), ‖dQ (ζr R' t) (eh R' t) i - 1‖ ≤ 5 * B * ρ := by
    have := sum_dQ_sub_one_le (n := Nh + 2) (L := L) (ρ := R'.ρ) (by omega) (by omega) hρ8' hB
      hm0.le (by
        have hmm := msq_mul_pow_le_one (L := L) (by omega) (by omega : 1 ≤ N) hmN
        rwa [show N - 1 = Nh + 2 - 1 by omega] at hmm)
      (fun i _ => absorb_le R' hρ0 _ _) (fun i hi => (hez i hi).1) (fun i hi => (hez i hi).2)
    rwa [show R'.ρ = ρ from hRρ] at this
  obtain ⟨hglue, -⟩ := hGB m hm b μ₀ hadm
  obtain ⟨-, -, -, -, -, hBd, -⟩ := hglue.2
  have hspl'' : SplitSmall R'.P L R'.ρ := hspl'
  have hb : 0 < b := (hadm.1 0 (Nat.zero_le _)).1
  have hVN := fun c hc => (hBd c hc).1
  refine ⟨hZMO m hm b μ₀ hadm, fun j hj => (hez j hj).2, hSb, fun hh => ?_,
    fun hh => ward2_onept R' hNh hρ1 hspl'' hm.1 hm.2 hV hVL hb hh hVN⟩
  obtain ⟨hu, hS, -⟩ := ward2 R' hNh hρ1 hspl'' hm.1 hm.2 hV hVL hb hh hVN
  have hD := suscept2_dressed R' hNh hρ1 hspl'' hm.1 hm.2 hV hVL t hu
  have hS' : χ = 1 / (m : ℂ) - (1 / (m : ℂ)) ^ 2 *
      (aFin (Nh + 1) out * πh R' (Nh + 2) t / U +
        ∑ j ∈ range (Nh + 2), ch₀ R' j t * πh R' j t / ρh R' j t) := hS
  rw [hS']
  refine hD.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  -- `e^{2S} - 1 ≤ 2S e^{2S} ≤ 10Bρ e^{5B/4}`
  set S := ∑ i ∈ range (Nh + 2), ‖dQ (ζr R' t) (eh R' t) i - 1‖
  have hS0 : 0 ≤ S := sum_nonneg fun _ _ => norm_nonneg _
  have hx : 2 * S ≤ 10 * B * ρ := by linarith
  have hx' : 10 * B * ρ ≤ 5 * B / 4 := by nlinarith
  have h1 : Real.exp (2 * S) - 1 ≤ 2 * S * Real.exp (2 * S) := by
    have := Real.add_one_le_exp (-(2 * S))
    have he : Real.exp (-(2 * S)) * Real.exp (2 * S) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (2 * S)]
  have h2 : Real.exp (2 * S) ≤ Real.exp (5 * B / 4) := Real.exp_le_exp.2 (hx.trans hx')
  have hEp := Real.exp_pos (2 * S)
  calc Real.exp (2 * S) - 1 ≤ 2 * S * Real.exp (2 * S) := h1
    _ ≤ 10 * B * ρ * Real.exp (5 * B / 4) := mul_le_mul hx h2 hEp.le (by positivity)
    _ = _ := by ring

end

end PtCorr2
