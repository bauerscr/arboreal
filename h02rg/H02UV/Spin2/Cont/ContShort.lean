import Spin2.Cont.ContTheta

/-!
# Short distances at finite `ε` (`thm:short`, finite-`ε` form)

For every `b` in the bracket `[bFin(1/(2β_R)), bFin(2/β_R)]` (`ctBracket`), uniformly in
`N ≥ N₀`, and every `x ≠ 0` with `j_x ≤ N − 2`, `ℓ = |x|/L^N`, `λ = log(1/ℓ)`:

* **`thm_short_eps`** (A): `ϑ_ε^{-2}P_ε(x) = (β_j/β_R)^{2/3}(1 + O(1/β_j))`, `j = jPhys`, with the
  constant `K` of `thm_multiscale_final_h0`; and `|β_j − β₁λ| ≤ K_c(1 + β_R + log(1 + λ))`
  (`ct_beta_scale` from `j` to `N − 2`, `(N − j)log L ∈ [λ, λ + log L)`).
  (B): if `2K_c(1 + β_R + log(1 + λ)) ≤ β₁λ`, then
  `|ϑ_ε^{-2}P_ε(x) − (β₁λ/β_R)^{2/3}| ≤ (β₁λ/β_R)^{2/3}(K_c(1 + β_R + log(1 + λ)) + 2K)/(β₁λ)`.
  `K, K_c` depend on `L` only.
* **`thm_short_eps_log`**: for fixed `β_R`, there are `δ₀ ∈ (0,1)`, `K'` (depending on `β_R`, `L`)
  with `|ϑ_ε^{-2}P_ε(x) − (β₁λ/β_R)^{2/3}| ≤ K'(β₁λ/β_R)^{2/3}(log λ)/λ` for `ℓ ≤ δ₀`
  (`CsPt`: all sample points, all `N ≥ N₀`); and every subsequential limit `G` of
  `ϑ_ε^{-2}P_ε(x_k)` with `ℓ_k → ℓ ∈ (0, δ₀)` satisfies the same bound at `ℓ`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

/-! ## Pure lemmas -/

/-- `u^{2/3}/u ≤ 2v^{2/3}/v` for `0 < v ≤ 2u`. -/
theorem cs_pow_ratio {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (h : v ≤ 2 * u) :
    u ^ (2 / 3 : ℝ) / u ≤ 2 * (v ^ (2 / 3 : ℝ) / v) := by
  have hp : 0 < u ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hu _
  have hq : 0 < v ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hv _
  have hqp : v ^ (1 / 3 : ℝ) ≤ 2 * u ^ (1 / 3 : ℝ) := by
    refine le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (by positivity) ?_
    rw [mul_pow, ct_cube_third hu.le, ct_cube_third hv.le]
    nlinarith only [h, hu]
  have key : (u ^ (1 / 3 : ℝ)) ^ 2 / (u ^ (1 / 3 : ℝ)) ^ 3 ≤
      2 * ((v ^ (1 / 3 : ℝ)) ^ 2 / (v ^ (1 / 3 : ℝ)) ^ 3) := by
    rw [show (u ^ (1 / 3 : ℝ)) ^ 2 / (u ^ (1 / 3 : ℝ)) ^ 3 = 1 / u ^ (1 / 3 : ℝ) by
        field_simp,
      show (v ^ (1 / 3 : ℝ)) ^ 2 / (v ^ (1 / 3 : ℝ)) ^ 3 = 1 / v ^ (1 / 3 : ℝ) by field_simp,
      div_le_iff₀ hp]
    rw [mul_one_div, div_mul_eq_mul_div, le_div_iff₀ hq]
    linarith
  rwa [ct_sq_third hu.le, ct_sq_third hv.le, ct_cube_third hu.le, ct_cube_third hv.le] at key

/-- **The short-distance arithmetic** (pure). From `|P − θ| ≤ Kθ/X`, `θ = (X/(1/b))^{2/3}`,
`ϑ = (β_R b)^{2/3}`: (i) `|P/ϑ − (X/β_R)^{2/3}| ≤ K(X/β_R)^{2/3}/X`; (ii) if moreover
`|X − Y| ≤ E`, `2E ≤ Y`: `|P/ϑ − (Y/β_R)^{2/3}| ≤ (Y/β_R)^{2/3}(E + 2K)/Y`. -/
theorem cs_core {P θ ϑ X K βR b : ℝ} (hβR : 0 < βR) (hb : 0 < b) (hX : 0 < X)
    (hθ : θ = (X / (1 / b)) ^ (2 / 3 : ℝ)) (hϑ : ϑ = (βR * b) ^ (2 / 3 : ℝ))
    (hP : |P - θ| ≤ K * θ / X) :
    |P / ϑ - (X / βR) ^ (2 / 3 : ℝ)| ≤ K * (X / βR) ^ (2 / 3 : ℝ) / X ∧
    ∀ Y E : ℝ, 0 < Y → |X - Y| ≤ E → 2 * E ≤ Y →
      |P / ϑ - (Y / βR) ^ (2 / 3 : ℝ)| ≤ (Y / βR) ^ (2 / 3 : ℝ) * ((E + 2 * K) / Y) := by
  have hϑ0 : 0 < ϑ := by rw [hϑ]; positivity
  have hθϑ : θ / ϑ = (X / βR) ^ (2 / 3 : ℝ) := by
    rw [hθ, hϑ, ← Real.div_rpow (by positivity) (by positivity)]
    congr 1; field_simp
  have hθ0 : 0 < θ := by rw [hθ]; positivity
  have hK : 0 ≤ K := by
    have h0 := (abs_nonneg _).trans hP
    rw [mul_div_assoc] at h0
    exact nonneg_of_mul_nonneg_left h0 (by positivity)
  have hi : |P / ϑ - (X / βR) ^ (2 / 3 : ℝ)| ≤ K * (X / βR) ^ (2 / 3 : ℝ) / X := by
    rw [← hθϑ, ← sub_div, abs_div, abs_of_pos hϑ0, div_le_iff₀ hϑ0]
    calc |P - θ| ≤ K * θ / X := hP
      _ = K * (θ / ϑ) / X * ϑ := by field_simp
  refine ⟨hi, fun Y E hY hE h2 => ?_⟩
  have hE0 : 0 ≤ E := (abs_nonneg _).trans hE
  have hXY : Y ≤ 2 * X := by have := (abs_le.1 hE).1; linarith
  have h1 := ct_rpow23_sub (X := X / βR) (Y := Y / βR) (by positivity) (by positivity)
  have e1 : |X / βR - Y / βR| / (Y / βR) = |X - Y| / Y := by
    rw [← sub_div, abs_div, abs_of_pos hβR]; field_simp
  rw [e1] at h1
  have h3 := cs_pow_ratio (u := X / βR) (v := Y / βR) (by positivity) (by positivity)
    (by rw [mul_div_assoc']; exact div_le_div_of_nonneg_right hXY hβR.le)
  have e2 : (X / βR) ^ (2 / 3 : ℝ) / X = (X / βR) ^ (2 / 3 : ℝ) / (X / βR) / βR := by
    field_simp
  have e3 : (Y / βR) ^ (2 / 3 : ℝ) / (Y / βR) / βR = (Y / βR) ^ (2 / 3 : ℝ) / Y := by
    field_simp
  have h4 : K * (X / βR) ^ (2 / 3 : ℝ) / X ≤ 2 * K * ((Y / βR) ^ (2 / 3 : ℝ) / Y) := by
    rw [mul_div_assoc, e2, ← e3]
    have := div_le_div_of_nonneg_right h3 hβR.le
    rw [mul_div_assoc] at this
    nlinarith only [this, hK]
  have h5 : |X - Y| / Y ≤ E / Y := div_le_div_of_nonneg_right hE hY.le
  have hA : 0 ≤ (Y / βR) ^ (2 / 3 : ℝ) := by positivity
  calc |P / ϑ - (Y / βR) ^ (2 / 3 : ℝ)|
      ≤ |P / ϑ - (X / βR) ^ (2 / 3 : ℝ)| + |(X / βR) ^ (2 / 3 : ℝ) - (Y / βR) ^ (2 / 3 : ℝ)| :=
        abs_sub_le _ _ _
    _ ≤ 2 * K * ((Y / βR) ^ (2 / 3 : ℝ) / Y) + (Y / βR) ^ (2 / 3 : ℝ) * (E / Y) := by
        have := mul_le_mul_of_nonneg_left h5 hA
        linarith
    _ = (Y / βR) ^ (2 / 3 : ℝ) * ((E + 2 * K) / Y) := by field_simp; ring

/-- **The physical scale vs `λ = log(1/ℓ)`**: for `j = jPhys(ℓ) ≤ N − 2`, with `n = N − 2 − j`:
`nβ ≤ β₁λ` and `|nβ − β₁λ| ≤ 2β`. -/
theorem cs_jphys {L N : ℕ} (hL : 2 ≤ L) {ℓ : ℝ} {jp : ℕ}
    (hj : (jp : ℤ) = jPhys L N ℓ) (hjN : jp ≤ N - 2) (hN : 2 ≤ N) :
    ((N - 2 - jp : ℕ) : ℝ) * betaL L ≤ betaOne * Real.log (1 / ℓ) ∧
      |((N - 2 - jp : ℕ) : ℝ) * betaL L - betaOne * Real.log (1 / ℓ)| ≤ 2 * betaL L := by
  have hlL : 0 < Real.log L := Real.log_pos (by exact_mod_cast (show 1 < L by omega))
  have h1 : ((jp : ℤ) : ℝ) ≤ (N : ℝ) + Real.logb L ℓ := by rw [hj, jPhys]; exact Int.floor_le _
  have h2 : (N : ℝ) + Real.logb L ℓ < ((jp : ℤ) : ℝ) + 1 := by
    rw [hj, jPhys]; exact Int.lt_floor_add_one _
  push_cast at h1 h2
  have hlam : Real.log (1 / ℓ) = -Real.log ℓ := by rw [one_div, Real.log_inv]
  rw [Real.logb] at h1 h2
  set lam := Real.log (1 / ℓ)
  have hlb : Real.log ℓ / Real.log L = -lam / Real.log L := by rw [hlam]; ring
  rw [hlb] at h1 h2
  have k1 : (jp : ℝ) * Real.log L ≤ N * Real.log L - lam := by
    have := mul_le_mul_of_nonneg_right h1 hlL.le
    rw [add_mul, div_mul_cancel₀ _ hlL.ne'] at this; linarith
  have k2 : N * Real.log L - lam < ((jp : ℝ) + 1) * Real.log L := by
    have := mul_lt_mul_of_pos_right h2 hlL
    rw [add_mul, div_mul_cancel₀ _ hlL.ne'] at this; linarith
  have hc : ((N - 2 - jp : ℕ) : ℝ) = N - 2 - jp := by
    rw [Nat.cast_sub hjN, Nat.cast_sub hN]; norm_num
  rw [hc, betaL_eq_betaOne]
  have hb1 := betaOne_pos
  have e : ((N : ℝ) - 2 - jp) * (betaOne * Real.log L) - betaOne * lam =
      betaOne * ((N * Real.log L - lam) - (jp : ℝ) * Real.log L - 2 * Real.log L) := by ring
  have u1 : (N * Real.log L - lam) - (jp : ℝ) * Real.log L - 2 * Real.log L ≤ -Real.log L := by
    nlinarith only [k2]
  have u2 : -(2 * Real.log L) ≤ (N * Real.log L - lam) - (jp : ℝ) * Real.log L - 2 * Real.log L := by
    linarith
  constructor
  · have := mul_le_mul_of_nonneg_left u1 hb1.le
    nlinarith only [this, e, hb1, hlL]
  · rw [e, abs_le]
    constructor
    · have := mul_le_mul_of_nonneg_left u2 hb1.le; linarith
    · have := mul_le_mul_of_nonneg_left u1 hb1.le; nlinarith only [this, hb1, hlL]

set_option maxHeartbeats 1000000 in
/-- **`thm:short` at finite `ε`** (constants `M, g₀, K, K_c, N₀` depending on `L` only). For
`N ≥ N₀`, `m² > 0`, `4m²L^{2N} ≤ 1/β_R ≤ g₀`, every `b` in the bracket, `x ≠ 0` with
`j_x ≤ N − 2`, `ℓ = |x|/L^N`, `λ = log(1/ℓ)`:
(A) at `j = jPhys(ℓ)`: `|ϑ_ε^{-2}P_ε(x) − (β_j/β_R)^{2/3}| ≤ K(β_j/β_R)^{2/3}/β_j`, and for
`λ ≥ 0`, `|β_j − β₁λ| ≤ K_c(1 + β_R + log(1 + λ))`;
(B) for `λ ≥ 0` with `2K_c(1 + β_R + log(1 + λ)) ≤ β₁λ`:
`|ϑ_ε^{-2}P_ε(x) − (β₁λ/β_R)^{2/3}| ≤ (β₁λ/β_R)^{2/3}(K_c(1 + β_R + log(1 + λ)) + 2K)/(β₁λ)`. -/
theorem thm_short_eps : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ (M : MasterFacts L) (g₀ K Kc : ℝ) (N₀ : ℕ), 0 < g₀ ∧ 0 < Kc ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → N₀ ≤ N →
    ∀ m βR : ℝ, 0 < m → 0 < βR → 4 * (m * (L : ℝ) ^ (2 * N)) ≤ 1 / βR → 1 / βR ≤ g₀ →
    ∀ b ∈ ctBracket M R m βR, ∀ x : Lam 2 L N, x ≠ 0 → Obs.coal L (0 : Lam 2 L N) x ≤ N - 2 →
      (∃ jp : ℕ, (jp : ℤ) = jPhys L N (eucl x / (L : ℝ) ^ N) ∧
        jp ≤ Obs.coal L (0 : Lam 2 L N) x ∧ Obs.coal L (0 : Lam 2 L N) x ≤ jp + 1 ∧
        |Pconn L N (1 / b) x / thetaEpsSq βR b - (betaJ R m b (b - m) jp / βR) ^ (2 / 3 : ℝ)| ≤
          K * (betaJ R m b (b - m) jp / βR) ^ (2 / 3 : ℝ) / betaJ R m b (b - m) jp ∧
        (0 ≤ Real.log (1 / (eucl x / (L : ℝ) ^ N)) →
          |betaJ R m b (b - m) jp - betaOne * Real.log (1 / (eucl x / (L : ℝ) ^ N))| ≤
            Kc * (1 + βR + Real.log (1 + Real.log (1 / (eucl x / (L : ℝ) ^ N)))))) ∧
      (0 ≤ Real.log (1 / (eucl x / (L : ℝ) ^ N)) →
        2 * (Kc * (1 + βR + Real.log (1 + Real.log (1 / (eucl x / (L : ℝ) ^ N))))) ≤
          betaOne * Real.log (1 / (eucl x / (L : ℝ) ^ N)) →
        |Pconn L N (1 / b) x / thetaEpsSq βR b -
            (betaOne * Real.log (1 / (eucl x / (L : ℝ) ^ N)) / βR) ^ (2 / 3 : ℝ)| ≤
          (betaOne * Real.log (1 / (eucl x / (L : ℝ) ^ N)) / βR) ^ (2 / 3 : ℝ) *
            ((Kc * (1 + βR + Real.log (1 + Real.log (1 / (eucl x / (L : ℝ) ^ N)))) + 2 * K) /
              (betaOne * Real.log (1 / (eucl x / (L : ℝ) ^ N))))) := by
  obtain ⟨L₀, h⟩ := ct_main
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨M, g₀, K, N₀, hg, hg1, hN₀, hF⟩ := h L hL
  have hβ := ct_betaL_pos M.ct_L2
  have hb1 := betaOne_pos
  set β := betaL L with hβd
  set a := M.ctA
  set E := M.ctE
  set c := a * |Real.log (2 * a)|
  have ha := M.ctA_nonneg
  have hE := M.ctE_nonneg
  have hc : 0 ≤ c := mul_nonneg ha (abs_nonneg _)
  set Kc := 2 * β + 5 + E + 2 * a * (betaOne + E + c) + 10 * a + a with hKcd
  have hKc : 0 < Kc := by positivity
  refine ⟨M, g₀, K, Kc, N₀, hg, hKc, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN m βR hm hβR hmass hy b hb x hx hcoal
  obtain ⟨hmR, hB, -⟩ := hF N R hP hi0 hRℓ hRA hRρ hN m βR hm hβR hmass hy
  obtain ⟨hb0, hD, hPb, hgl⟩ := hB b hb
  obtain ⟨jp, hjp, hj1, hj2, hPj⟩ := hPb x hx hcoal
  have hjN : jp ≤ N - 2 := hj1.trans hcoal
  have hm1 : m * (L : ℝ) ^ (2 * N) ≤ 1 := by
    have := one_div_pos.2 hβR
    have h0 : 0 ≤ m * (L : ℝ) ^ (2 * N) := mul_nonneg hm.le (by positivity)
    linarith
  have hT : 1 / (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (N - 2)).1 ≤ 5 * βR := by
    have hg0 : 0 < 1 / βR / 5 := by positivity
    rw [div_le_iff₀ (hg0.trans_le hgl)]
    have e : 5 * βR * (1 / βR / 5) = 1 := by field_simp
    nlinarith only [hgl, e, hβR]
  have hX : 0 < betaJ R m b (b - m) jp := one_div_pos.2 (hD jp hjN).1
  have core := cs_core (P := Pconn L N (1 / b) x) (K := K) hβR hb0 hX rfl rfl hPj
  set lam := Real.log (1 / (eucl x / (L : ℝ) ^ N)) with hlamd
  -- `β_j` vs `β₁λ`
  have hBJ : 0 ≤ lam → |betaJ R m b (b - m) jp - betaOne * lam| ≤
      Kc * (1 + βR + Real.log (1 + lam)) := by
    intro hl0
    have H := M.ct_beta_scale R hP hi0 hRℓ hRA hRρ (by omega) hmR hm1 hD hT jp hjN
    obtain ⟨j1, j2⟩ := cs_jphys M.ct_L2 hjp hjN (by omega)
    rw [← hβd, ← hlamd] at j1 j2
    set x' := ((N - 2 - jp : ℕ) : ℝ) * β
    have hx0 : 0 ≤ x' := by positivity
    have hL := ct_log_lin (x := x') (s := betaOne) (t := lam) (D := 5 * βR + E + c)
      (by positivity) hb1.le hl0 hx0 (by nlinarith only [j1, hb1, hl0])
    rw [show x' + (5 * βR + E + c) = x' + (5 * βR + E) + c by ring] at hL
    have hL' := mul_le_mul_of_nonneg_left hL ha
    have hlog : 0 ≤ Real.log (1 + lam) := Real.log_nonneg (by linarith)
    have t : |betaJ R m b (b - m) jp - betaOne * lam| ≤
        |betaJ R m b (b - m) jp - x'| + 2 * β := by
      have := abs_sub_le (betaJ R m b (b - m) jp) x' (betaOne * lam)
      linarith
    have hprod : 0 ≤ 2 * a * (betaOne + E + c) := by positivity
    have k1 : (5 + 10 * a) * βR ≤ Kc * βR := mul_le_mul_of_nonneg_right (by linarith) hβR.le
    have k2 : a * Real.log (1 + lam) ≤ Kc * Real.log (1 + lam) :=
      mul_le_mul_of_nonneg_right (by linarith) hlog
    have e : a * (2 * (betaOne + (5 * βR + E + c)) + Real.log (1 + lam)) =
        2 * a * (betaOne + E + c) + 10 * a * βR + a * Real.log (1 + lam) := by ring
    have e2 : Kc * (1 + βR + Real.log (1 + lam)) = Kc + Kc * βR + Kc * Real.log (1 + lam) := by
      ring
    linarith
  refine ⟨⟨jp, hjp, hj1, hj2, core.1, hBJ⟩, fun hl0 h2 => ?_⟩
  have hpos : 0 < betaOne * lam := by
    have : 0 < Kc * (1 + βR + Real.log (1 + lam)) :=
      mul_pos hKc (by have := Real.log_nonneg (show (1 : ℝ) ≤ 1 + lam by linarith); linarith)
    linarith
  exact core.2 _ _ hpos (hBJ hl0) h2

/-- `|x| ≥ 1` (lattice units) for `x ≠ 0`. -/
theorem cs_one_le_eucl {L N : ℕ} [NeZero L] {x : Lam 2 L N} (hx : x ≠ 0) : (1 : ℝ) ≤ eucl x := by
  have hs1 : 1 ≤ supNorm x := by
    rcases Nat.eq_zero_or_pos (supNorm x) with h0 | h0
    · exact absurd ((FRD.supNorm_eq_zero_iff x).1 h0) hx
    · exact h0
  exact le_trans (by exact_mod_cast hs1) (supNorm_le_eucl x)

/-- The short-distance profile `(β₁λ/β_R)^{2/3}`, `λ = log(1/ℓ)`. -/
def csA (βR ℓ : ℝ) : ℝ := (betaOne * Real.log (1 / ℓ) / βR) ^ (2 / 3 : ℝ)

/-- The relative rate `(log λ)/λ`, `λ = log(1/ℓ)`. -/
def csRate (ℓ : ℝ) : ℝ := Real.log (Real.log (1 / ℓ)) / Real.log (1 / ℓ)

/-- A short-distance sample: `P = ϑ_ε^{-2}P_ε(x)` and `ℓ = |x|/L^N` for some `N ≥ N₀`, master
parameters `R`, mass `m² > 0` in the window, `b` in the bracket, `x ≠ 0` with `j_x ≤ N − 2`. -/
def CsPt {L : ℕ} [NeZero L] (M : MasterFacts L) (N₀ : ℕ) (βR P ℓ : ℝ) : Prop :=
  ∃ N : ℕ, N₀ ≤ N ∧ ∃ (R : RGPar 2 L N) (_ : Fact (0 < R.ℓ)) (_ : Fact (0 < R.A)), R.P = Pc ∧
    R.i₀ = 0 ∧ R.ℓ = M.core.ℓ ∧ R.A = M.core.A ∧ R.ρ = M.core.ρ ∧
    ∃ m b : ℝ, 0 < m ∧ 4 * (m * (L : ℝ) ^ (2 * N)) ≤ 1 / βR ∧ b ∈ ctBracket M R m βR ∧
    ∃ x : Lam 2 L N, x ≠ 0 ∧ Obs.coal L (0 : Lam 2 L N) x ≤ N - 2 ∧
      P = Pconn L N (1 / b) x / thetaEpsSq βR b ∧ ℓ = eucl x / (L : ℝ) ^ N

set_option maxHeartbeats 1000000 in
/-- **`thm:short` at finite `ε`, `(log λ)/λ` form, and subsequential limits.** Constants
`M, g₀, N₀` depend on `L` only; for fixed `β_R` (`1/β_R ≤ g₀`) there are `δ₀ ∈ (0, 1)` and
`K' ≥ 0` (depending on `β_R`, `L`) such that, uniformly in `N ≥ N₀`, every sample (`CsPt`) with
`ℓ ≤ δ₀` satisfies `|ϑ_ε^{-2}P_ε − (β₁λ/β_R)^{2/3}| ≤ K'(β₁λ/β_R)^{2/3}(log λ)/λ`; and if
`P_k → G`, `ℓ_k → ℓ ∈ (0, δ₀)` along samples, then `G` satisfies the same bound at `ℓ`. -/
theorem thm_short_eps_log : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ (M : MasterFacts L) (g₀ : ℝ) (N₀ : ℕ), 0 < g₀ ∧ ∀ βR : ℝ, 0 < βR → 1 / βR ≤ g₀ →
    ∃ δ₀ K' : ℝ, 0 < δ₀ ∧ δ₀ < 1 ∧ 0 ≤ K' ∧
      (∀ P ℓ : ℝ, CsPt M N₀ βR P ℓ → ℓ ≤ δ₀ → |P - csA βR ℓ| ≤ K' * csA βR ℓ * csRate ℓ) ∧
      ∀ (Pk ℓk : ℕ → ℝ) (G ℓ : ℝ), 0 < ℓ → ℓ < δ₀ → Tendsto Pk atTop (𝓝 G) →
        Tendsto ℓk atTop (𝓝 ℓ) → (∀ᶠ k in atTop, CsPt M N₀ βR (Pk k) (ℓk k)) →
        |G - csA βR ℓ| ≤ K' * csA βR ℓ * csRate ℓ := by
  obtain ⟨L₀, h⟩ := thm_short_eps
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨M, g₀, K, Kc, N₀, hg, hKc, hF⟩ := h L hL
  refine ⟨M, g₀, N₀, hg, fun βR hβR hy => ?_⟩
  have hb1 := betaOne_pos
  have hev : ∀ᶠ y in atTop, (1 + βR + Real.log y) / y ≤ betaOne / (4 * Kc) :=
    (ct_rate_tendsto (1 + βR)).eventually (ge_mem_nhds (by positivity))
  obtain ⟨y₀, hy₀⟩ := eventually_atTop.1 hev
  set l₀ := max (max y₀ 1) (Real.exp 1) with hl₀d
  have hl₀1 : 1 ≤ l₀ := (le_max_right _ _).trans (le_max_left _ _)
  have hl₀e : Real.exp 1 ≤ l₀ := le_max_right _ _
  have hl₀y : y₀ ≤ l₀ := (le_max_left _ _).trans (le_max_left _ _)
  set K' := (Kc * (3 + βR) + 2 * |K|) / betaOne with hK'd
  have hK' : 0 ≤ K' := by positivity
  -- the two facts at `λ ≥ λ₀`
  have hlam : ∀ lam : ℝ, l₀ ≤ lam →
      2 * (Kc * (1 + βR + Real.log (1 + lam))) ≤ betaOne * lam ∧
      (Kc * (1 + βR + Real.log (1 + lam)) + 2 * K) / (betaOne * lam) ≤
        K' * (Real.log lam / lam) := by
    intro lam hl
    have hl1 : 1 ≤ lam := hl₀1.trans hl
    have hl0 : 0 < lam := by linarith
    have hq := hy₀ (1 + lam) (by linarith)
    rw [div_le_div_iff₀ (by linarith) (by positivity)] at hq
    have hlg : 1 ≤ Real.log lam := (Real.le_log_iff_exp_le hl0).2 (hl₀e.trans hl)
    have hl2 : Real.log (1 + lam) ≤ 2 * Real.log lam := by
      have h1 : Real.log (1 + lam) ≤ Real.log (2 * lam) := Real.log_le_log (by linarith) (by linarith)
      rw [Real.log_mul (by norm_num) hl0.ne'] at h1
      have h2 : Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      linarith
    refine ⟨by nlinarith only [hq, hl1, hb1], ?_⟩
    rw [div_le_iff₀ (by positivity)]
    have e : K' * (Real.log lam / lam) * (betaOne * lam) =
        (Kc * (3 + βR) + 2 * |K|) * Real.log lam := by
      rw [hK'd]; field_simp
    rw [e]
    have hlog0 : 0 ≤ Real.log (1 + lam) := Real.log_nonneg (by linarith)
    have t1 : Kc * (1 + βR) ≤ Kc * (1 + βR) * Real.log lam :=
      le_mul_of_one_le_right (by positivity) hlg
    have t2 : Kc * Real.log (1 + lam) ≤ Kc * (2 * Real.log lam) :=
      mul_le_mul_of_nonneg_left hl2 hKc.le
    have t3 : 2 * K ≤ 2 * |K| * Real.log lam := by
      have := le_mul_of_one_le_right (show 0 ≤ 2 * |K| by positivity) hlg
      have := le_abs_self K
      linarith
    nlinarith only [t1, t2, t3]
  -- the pointwise bound
  have hpt : ∀ P ℓ : ℝ, CsPt M N₀ βR P ℓ → ℓ ≤ Real.exp (-l₀) →
      |P - csA βR ℓ| ≤ K' * csA βR ℓ * csRate ℓ := by
    intro P ℓ hP hℓ
    obtain ⟨N, hN, R, _, _, hPc, hi0, hRℓ, hRA, hRρ, m, b, hm, hmass, hb, x, hx, hcoal, rfl, rfl⟩ :=
      hP
    have hℓ0 : 0 < eucl x / (L : ℝ) ^ N := by
      have := cs_one_le_eucl hx
      have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by have := M.ct_L2; omega)
      positivity
    set lam := Real.log (1 / (eucl x / (L : ℝ) ^ N)) with hlamd
    have hll : l₀ ≤ lam := by
      have h1 := Real.log_le_log hℓ0 hℓ
      rw [Real.log_exp] at h1
      rw [hlamd, one_div, Real.log_inv]; linarith
    obtain ⟨h2, h3⟩ := hlam lam hll
    have hB := (hF N R hPc hi0 hRℓ hRA hRρ hN m βR hm hβR hmass hy b hb x hx hcoal).2
      (by linarith) h2
    rw [← hlamd] at hB
    have hA0 : 0 ≤ csA βR (eucl x / (L : ℝ) ^ N) := by
      unfold csA; rw [← hlamd]
      exact Real.rpow_nonneg (div_nonneg (mul_nonneg hb1.le (by linarith)) hβR.le) _
    unfold csRate
    rw [← hlamd]
    refine hB.trans ?_
    have := mul_le_mul_of_nonneg_left h3 hA0
    unfold csA at this ⊢
    rw [← hlamd] at this ⊢
    linarith
  refine ⟨Real.exp (-l₀), K', Real.exp_pos _, Real.exp_lt_one_iff.2 (by linarith), hK', hpt, ?_⟩
  intro Pk ℓk G ℓ hℓ0 hℓδ hPk hℓk hev'
  have hlamℓ : l₀ < Real.log (1 / ℓ) := by
    have h1 := Real.log_lt_log hℓ0 hℓδ
    rw [Real.log_exp] at h1
    rw [one_div, Real.log_inv]; linarith
  have hne : Real.log (1 / ℓ) ≠ 0 := by linarith
  have h1 : ContinuousAt (fun t : ℝ => 1 / t) ℓ := continuousAt_const.div continuousAt_id hℓ0.ne'
  have hlog : ContinuousAt (fun t : ℝ => Real.log (1 / t)) ℓ := h1.log (one_div_pos.2 hℓ0).ne'
  have hA : ContinuousAt (fun t => csA βR t) ℓ :=
    ((continuousAt_const.mul hlog).div_const βR).rpow_const (Or.inr (by norm_num))
  have hR : ContinuousAt (fun t => csRate t) ℓ := (hlog.log hne).div hlog hne
  have hB : ContinuousAt (fun t => K' * csA βR t * csRate t) ℓ :=
    (continuousAt_const.mul hA).mul hR
  have hT := ((hPk.sub (hA.tendsto.comp hℓk)).abs.sub (hB.tendsto.comp hℓk))
  have hle : ∀ᶠ k in atTop, |Pk k - csA βR (ℓk k)| - K' * csA βR (ℓk k) * csRate (ℓk k) ≤ 0 := by
    filter_upwards [hev', hℓk.eventually (ge_mem_nhds hℓδ)] with k hk hk2
    have := hpt _ _ hk hk2
    linarith
  have := le_of_tendsto hT hle
  linarith

end

end Spin2
