import PtCorr2.Zero.Dressing
import PtCorr2.Zero.Flow

/-!
# The zero modes `e_j = ε_j(0)` along the flow, and the dressed susceptibility with error `O(ρ)`

`SplitSmall` (`Step2/Map/SplitSmall.lean`) carries `EpsZeroSmall P L ρ B`: for every history with
`|ζ_i| ≤ ρ`, `|ζ'_jε_j(0)| ≤ 1/2` and `|ε_j(0)| ≤ B m² L^{2j}` (`DressedFRD.eps_zero_bound`). Hence:

* `eh_zp_bound`: along every history, `|ζ_j/(1+ζ_j) e_j| ≤ 1/2` and `|e_j| ≤ B m² L^{2j}`;
* `norm_dQ_sub_one_le_zp`: then `|ρ_j| = |1 + ζ_j||1 - ζ'_je_j| ≥ 7/16` and
  `|q_j - 1| = |ζ_je_j/ρ_j| ≤ (16/7)|ζ_j||e_j|`;
* `sum_dQ_sub_one_le`: `S = ∑_{i<N}|q_i - 1| ≤ 5Bρ`, since `∑_{i<N} m²L^{2i} ≤ 2m²L^{2(N-1)} ≤ 2`;
* **`thm_ward_flow_rho`**: `thm_ward_flow` with the bounds on `e_j` and `S` explicit, and the
  normalised susceptibility

  `|∑_x⟨ψ̄_0ψ_x⟩ - Z_N^{-1}[m^{-2} - m^{-4}(ã/Z_N)/(1+ũ)]|
     ≤ (m^{-2}∑_{j<N}|ζ_j|/(|Z_j||1+ζ_j|) + m^{-4}|ã/Z_N|/(|Z_N||1+ũ|)) · 10Be^{5B/4} ρ`.
-/

namespace PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2 Step2.D2 Step

/-- `|q_j - 1| ≤ (16/7)|ζ_j||e_j|` if `|ζ_j| ≤ 1/8` and `|ζ_j/(1+ζ_j) e_j| ≤ 1/2`. -/
theorem norm_dQ_sub_one_le_zp {ζ e : ℕ → ℂ} {j : ℕ} (hζ : ‖ζ j‖ ≤ 1 / 8)
    (hz : ‖ζ j / (1 + ζ j) * e j‖ ≤ 1 / 2) :
    ‖dQ ζ e j - 1‖ ≤ 16 / 7 * (‖ζ j‖ * ‖e j‖) := by
  have h1 : 7 / 8 ≤ ‖1 + ζ j‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-ζ j)
    rw [norm_one, norm_neg, sub_neg_eq_add] at this
    linarith
  have h1ne : 1 + ζ j ≠ 0 := fun h => by rw [h, norm_zero] at h1; linarith
  have h2 : 1 / 2 ≤ ‖1 - ζ j / (1 + ζ j) * e j‖ := by
    have := norm_sub_norm_le (1 : ℂ) (ζ j / (1 + ζ j) * e j)
    rw [norm_one] at this
    linarith
  have hfac : dRho ζ e j = (1 + ζ j) * (1 - ζ j / (1 + ζ j) * e j) := by
    rw [dRho]; field_simp; ring
  have hρ : 7 / 16 ≤ ‖dRho ζ e j‖ := by
    rw [hfac, norm_mul]
    nlinarith [norm_nonneg (1 + ζ j), norm_nonneg (1 - ζ j / (1 + ζ j) * e j)]
  have hρ0 : dRho ζ e j ≠ 0 := fun h => by rw [h, norm_zero] at hρ; linarith
  rw [dQ_sub_one hρ0, norm_div, norm_mul, div_le_iff₀ (by linarith)]
  nlinarith [mul_nonneg (norm_nonneg (ζ j)) (norm_nonneg (e j))]

/-- **`S = O(ρ)`**: `∑_{i<n}|q_i - 1| ≤ 5Bρ` if `|ζ_i| ≤ ρ ≤ 1/8`, `|ζ'_ie_i| ≤ 1/2`,
`|e_i| ≤ B m² L^{2i}` and `m² L^{2(n-1)} ≤ 1`. -/
theorem sum_dQ_sub_one_le {ζ e : ℕ → ℂ} {n L : ℕ} {ρ B msq : ℝ} (hL : 2 ≤ L) (hn : 1 ≤ n)
    (hρ8 : ρ ≤ 1 / 8) (hB : 0 ≤ B) (hmsq : 0 ≤ msq)
    (hm : msq * (L : ℝ) ^ (2 * (n - 1)) ≤ 1) (hζ : ∀ i < n, ‖ζ i‖ ≤ ρ)
    (hz : ∀ i < n, ‖ζ i / (1 + ζ i) * e i‖ ≤ 1 / 2)
    (he : ∀ i < n, ‖e i‖ ≤ B * msq * (L : ℝ) ^ (2 * i)) :
    ∑ i ∈ range n, ‖dQ ζ e i - 1‖ ≤ 5 * B * ρ := by
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans (hζ 0 (by omega))
  have hL2 : (2 : ℝ) ≤ (L : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ L := by exact_mod_cast hL
    nlinarith
  have hgeo : ∑ i ∈ range n, ((L : ℝ) ^ 2) ^ i ≤ 2 * ((L : ℝ) ^ 2) ^ (n - 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [sum_range_succ, Nat.add_sub_cancel]
    have := DressedFRD.sum_range_pow_le hL2 k
    linarith
  calc ∑ i ∈ range n, ‖dQ ζ e i - 1‖
      ≤ ∑ i ∈ range n, 16 / 7 * ρ * B * msq * ((L : ℝ) ^ 2) ^ i := by
        refine sum_le_sum fun i hi => ?_
        have hi' := mem_range.1 hi
        have h1 := norm_dQ_sub_one_le_zp (e := e) ((hζ i hi').trans hρ8) (hz i hi')
        have h2 : ‖ζ i‖ * ‖e i‖ ≤ ρ * (B * msq * (L : ℝ) ^ (2 * i)) :=
          mul_le_mul (hζ i hi') (he i hi') (norm_nonneg _) hρ0
        rw [← pow_mul]
        nlinarith
    _ = 16 / 7 * ρ * B * msq * ∑ i ∈ range n, ((L : ℝ) ^ 2) ^ i := by rw [mul_sum]
    _ ≤ 16 / 7 * ρ * B * msq * (2 * ((L : ℝ) ^ 2) ^ (n - 1)) :=
        mul_le_mul_of_nonneg_left hgeo (by positivity)
    _ = 32 / 7 * (B * ρ) * (msq * (L : ℝ) ^ (2 * (n - 1))) := by rw [← pow_mul]; ring
    _ ≤ 32 / 7 * (B * ρ) * 1 := mul_le_mul_of_nonneg_left hm (by positivity)
    _ ≤ 5 * B * ρ := by nlinarith [mul_nonneg hB hρ0]

/-- `m² ≤ L^{-2(N-1)}` gives `m² L^{2(N-1)} ≤ 1`. -/
theorem msq_mul_pow_le_one {L N : ℕ} {msq : ℝ} (hL : 1 ≤ L) (hN : 1 ≤ N)
    (hm : msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) : msq * (L : ℝ) ^ (2 * (N - 1)) ≤ 1 := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hp : 0 < (L : ℝ) ^ (2 * (N - 1)) := by positivity
  have e : (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) = ((L : ℝ) ^ (2 * (N - 1)))⁻¹ := by
    rw [Real.rpow_neg hL0.le, ← Real.rpow_natCast]
    congr 2
    push_cast [Nat.cast_sub hN]; ring
  rw [e] at hm
  calc msq * (L : ℝ) ^ (2 * (N - 1)) ≤ ((L : ℝ) ^ (2 * (N - 1)))⁻¹ * (L : ℝ) ^ (2 * (N - 1)) :=
        mul_le_mul_of_nonneg_right hm hp.le
    _ = 1 := inv_mul_cancel₀ hp.ne'

section Flow

variable {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- **The zero modes along a history**: `|ζ_j/(1+ζ_j) e_j| ≤ 1/2` and `|e_j| ≤ B m² L^{2j}`. -/
theorem eh_zp_bound (hL7 : 7 ≤ L) (hρ0 : 0 ≤ R.ρ) {B : ℝ} (hE : EpsZeroSmall R.P L R.ρ B)
    (hN : 1 ≤ N) (hm0 : 0 < R.msq) (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))))
    (t : Hist.Seq (Xs R)) {j : ℕ} (hj : j < N) (H : RawInv R j (rawHist R j t))
    (hZ : Zr R t j ≠ 0) :
    ‖ζr R t j / (1 + ζr R t j) * eh R t j‖ ≤ 1 / 2 ∧
      ‖eh R t j‖ ≤ B * R.msq * (L : ℝ) ^ (2 * j) := by
  obtain ⟨-, -, hb⟩ := rawHist_struct R hρ0 j t
  have h := hE N R.msq hN hm0 hm (Function.update (rawHist R j t).ζ j (stZeta R (rawHist R j t)))
    (fun i => by
      by_cases hi : i = j
      · subst hi; rw [Function.update_self]; exact absorb_le R hρ0 _ _
      · rw [Function.update_of_ne hi]; exact hb i) j hj
  have hz : (Dh R j t).zp j = ζr R t j / (1 + ζr R t j) := by
    show Function.update (rawHist R j t).ζ j (stZeta R (rawHist R j t)) j /
      (1 + Function.update (rawHist R j t).ζ j (stZeta R (rawHist R j t)) j) = _
    rw [Function.update_self]
  rw [eh_eq_eps R hL7 hm0 hN hj.le H hZ, ← hz]
  exact h

end Flow

/-- **The Ward step along the flow, with the dressing error `O(ρ)`.** The constants of
`thm_zero_mode_flow`, and `B ≥ 0` from `SplitSmall` (`EpsZeroSmall`): along every admissible
trajectory, `|e_j| ≤ B m² L^{2j}` (`e_j = ε_j(0)`), `S = ∑_{i<N}|ζ_ie_i/ρ_i| ≤ 5Bρ`, and if
`b ≤ μ₀ + m²` the normalised susceptibility holds with error factor `10Be^{5B/4}ρ`. -/
theorem thm_ward_flow_rho : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
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
            (10 * B * Real.exp (5 * B / 4) * ρ)) := by
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
  refine ⟨hZMO m hm b μ₀ hadm, fun j hj => (hez j hj).2, hSb, fun hh => ?_⟩
  obtain ⟨hglue, -⟩ := hGB m hm b μ₀ hadm
  obtain ⟨-, -, -, -, -, hBd, -⟩ := hglue.2
  have hspl'' : SplitSmall R'.P L R'.ρ := hspl'
  have hb : 0 < b := (hadm.1 0 (Nat.zero_le _)).1
  have hVN := fun c hc => (hBd c hc).1
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
