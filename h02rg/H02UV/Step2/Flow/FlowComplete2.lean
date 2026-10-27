import Step2.Flow.FlowComplete2Hyp
import Step2.Flow.FlowComplete

/-!
# Expected result `thm:flow` with the last two steps: uniqueness and `m²`-continuity of the
shooting on the final coupling `ǧ_N`

`thm_flow_complete2`: the statement of `thm_flow_complete` and in addition
* `ρ ≤ 1/8` (the clamp radius; needed downstream for `Z_N ≠ 0`) and `SplitSmall Pc L ρ`
  (the splitting of the dressed decomposition for all histories with `|ζ_i| ≤ ρ`), and the
  validity `ValidAt` below `N_h`, `ValidAtL` at `N_h` for every mass;
* (strict monotonicity) for every mass `m² ∈ mRange L N`, `b ↦ Re ǧ_N(b)` (`gFinB`) is strictly
  increasing on `Ufix`;
* (uniqueness) for every `β_R ≥ 2/ε` the `b ∈ Ufix` with `Re ǧ_N(b) = 1/β_R` is unique;
* (continuity) the shooting solution `m² ↦ b_fin(m², 1/β_R)` (`bFin`) is continuous on
  `mRange L N`.

**Proof of the strict monotonicity** (`gFin_strictMonoOn`). For `b < b'` with admissible
trajectories `v, u`, the `ǧ`-cone at the horizon `N_h = N - 2` (`traj_cone_top_z`) gives
`e = δǧ_{N_h} > 0`, `‖δx_{N_h}‖ ≤ q₂ e`, `h_max ≤ r₂ e`, `|δζ_{N_h}| ≤ z₂ e`, `|δμ_{N_h}| ≤ p₂ e`.
The difference bounds of the step `N_h` (under `ValidAtL`, `LL.lip_rg_z2`) give
`|δǧ_{N-1} - e| ≤ c e ≤ e/4`, `|δμ_{N-1}| ≤ b_μ e`, `|δζ_{N-1}| ≤ b_ζ e`,
`|δ(Z_N w^{(1)}_{N-1}/L^{2(N-1)})| ≤ b_W e` (`top_cone_arith`). The last map is explicit,
`ǧ_N = ǧ_{N-1}/(1 + n)`, `n = clamp(4 μ_{N-1} Z_N w^{(1)}_{N-1}/L^{2(N-1)})` (`gFin_eq_div`), and
`|δ Re ǧ_N - δǧ_{N-1}| ≤ (8/7)|δǧ_{N-1}||n| + (64/49)|ǧ_{N-1}||δn|` (`last_map_diff`) with
`|n|, |ǧ_{N-1}| = O(C_f ε)`. Hence `δ Re ǧ_N ≥ e/4 > 0` under `kFin ε ≤ 1/2` (`last_arith`).

**Continuity** (`contOn_shoot`): the argument of `continuousOn_bsh_g`, with the joint continuity
of `(m², b) ↦ Re ǧ_N` on the relatively open `UfixM` (`gFin_contOn_UfixM`) and the strict
monotonicity in `b`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

variable {L : ℕ} [NeZero L]

/-! ### Arithmetic -/

/-- **The last map**: `ǧ ↦ ǧ/(1 + n)` with `|n| ≤ 1/8`. -/
theorem last_map_diff {g g' : ℝ} {n n' : ℂ} (hn : ‖n‖ ≤ 1 / 8) (hn' : ‖n'‖ ≤ 1 / 8) :
    |((g : ℂ) / (1 + n)).re - ((g' : ℂ) / (1 + n')).re - (g - g')| ≤
      8 / 7 * (|g - g'| * ‖n‖) + 64 / 49 * (|g'| * ‖n - n'‖) := by
  have h1 : 7 / 8 ≤ ‖1 + n‖ := by linarith [norm_one_add_ge (ζ := n)]
  have h1' : 7 / 8 ≤ ‖1 + n'‖ := by linarith [norm_one_add_ge (ζ := n')]
  have hne : (1 + n) ≠ 0 := fun h => by rw [h, norm_zero] at h1; linarith
  have hne' : (1 + n') ≠ 0 := fun h => by rw [h, norm_zero] at h1'; linarith
  have e0 : (g : ℂ) / (1 + n) - (g' : ℂ) / (1 + n') - ((g - g' : ℝ) : ℂ) =
      -(((g - g' : ℝ) : ℂ) * n / (1 + n)) - (g' : ℂ) * (n - n') / ((1 + n) * (1 + n')) := by
    push_cast; field_simp; ring
  have e : ((g : ℂ) / (1 + n)).re - ((g' : ℂ) / (1 + n')).re - (g - g') =
      (-(((g - g' : ℝ) : ℂ) * n / (1 + n)) - (g' : ℂ) * (n - n') / ((1 + n) * (1 + n'))).re := by
    rw [← e0, Complex.sub_re, Complex.sub_re, Complex.ofReal_re]
  rw [e]
  refine (Complex.abs_re_le_norm _).trans ((norm_sub_le _ _).trans ?_)
  simp only [norm_neg, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hP : 0 ≤ |g - g'| * ‖n‖ := by positivity
  have hQ : 0 ≤ |g'| * ‖n - n'‖ := by positivity
  have a : |g - g'| * ‖n‖ / ‖1 + n‖ ≤ 8 / 7 * (|g - g'| * ‖n‖) := by
    rw [div_le_iff₀ (by linarith)]
    have := mul_le_mul_of_nonneg_left h1 hP
    linarith only [this, hP]
  have hp : 49 / 64 ≤ ‖1 + n‖ * ‖1 + n'‖ := by
    have := mul_le_mul h1 h1' (by norm_num) (by linarith)
    linarith only [this]
  have b : |g'| * ‖n - n'‖ / (‖1 + n‖ * ‖1 + n'‖) ≤ 64 / 49 * (|g'| * ‖n - n'‖) := by
    rw [div_le_iff₀ (by linarith)]
    have := mul_le_mul_of_nonneg_left hp hQ
    linarith only [this, hQ]
  linarith only [a, b]

/-- **The step `N - 2` along the cone** (arithmetic). -/
theorem top_cone_arith {e dG dm dμ0 dx M dζ0 dζ1 dnw CL ε p₂ q₂ r₂ z₂ ℓ CNW Λ : ℝ}
    (he : 0 < e) (hCL : 0 ≤ CL) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hp : 0 ≤ p₂) (hq : q₂ ≤ 1)
    (hr : r₂ = 2 + p₂) (hΛ : 0 ≤ Λ) (hCNW : 0 ≤ CNW)
    (hc : CL * ε + CL * ε * p₂ + CL * q₂ + CL * ε * r₂ ≤ 1 / 4)
    (hdμ0' : 0 ≤ dμ0) (hdx' : 0 ≤ dx) (hM' : 0 ≤ M)
    (hdμ0 : dμ0 ≤ p₂ * e) (hdx : dx ≤ q₂ * e) (hM : M ≤ r₂ * e) (hdζ0 : dζ0 ≤ z₂ * e)
    (LG : |dG - e| ≤ CL * ε * e + CL * ε * dμ0 + CL * dx + CL * ε * M)
    (Lm : |dm| ≤ CL * e + CL * ε * dμ0 + CL * dx + CL * ε * M + 4 * dζ0)
    (LZ : dζ1 ≤ CL * (e + dx) + CL * ε * (dμ0 + M))
    (NW : dnw ≤ 2 * ℓ ^ 2 * dζ1 + CNW * M) :
    3 / 4 * e ≤ dG ∧ |dG| ≤ 5 / 4 * e ∧
      |dm| + Λ * dμ0 ≤ (Λ * p₂ + CL * (4 + 2 * p₂) + 4 * z₂) * e ∧
      dnw ≤ (2 * ℓ ^ 2 * (CL * (4 + 2 * p₂)) + CNW * r₂) * e := by
  have hCε : 0 ≤ CL * ε := mul_nonneg hCL hε0
  have hCεC : CL * ε ≤ CL := by
    have := mul_le_mul_of_nonneg_left hε1 hCL; linarith only [this]
  have a1 : CL * ε * dμ0 ≤ CL * ε * (p₂ * e) := mul_le_mul_of_nonneg_left hdμ0 hCε
  have a2 : CL * dx ≤ CL * (q₂ * e) := mul_le_mul_of_nonneg_left hdx hCL
  have a3 : CL * ε * M ≤ CL * ε * (r₂ * e) := mul_le_mul_of_nonneg_left hM hCε
  have a4 := mul_le_mul_of_nonneg_right hc he.le
  have hLG : |dG - e| ≤ 1 / 4 * e := by
    have e1 : (CL * ε + CL * ε * p₂ + CL * q₂ + CL * ε * r₂) * e =
        CL * ε * e + CL * ε * (p₂ * e) + CL * (q₂ * e) + CL * ε * (r₂ * e) := by ring
    linarith only [LG, a1, a2, a3, a4, e1]
  obtain ⟨g1, g2⟩ := abs_le.1 hLG
  have hdG0 : 0 ≤ dG := by linarith only [g1, he]
  refine ⟨by linarith only [g1], by rw [abs_of_nonneg hdG0]; linarith only [g2], ?_, ?_⟩
  · have b1 : CL * ε * dμ0 ≤ CL * (p₂ * e) :=
      (mul_le_mul_of_nonneg_right hCεC hdμ0').trans (mul_le_mul_of_nonneg_left hdμ0 hCL)
    have b2 : CL * dx ≤ CL * e := by
      have : q₂ * e ≤ 1 * e := mul_le_mul_of_nonneg_right hq he.le
      have := mul_le_mul_of_nonneg_left this hCL
      linarith only [a2, this]
    have b3 : CL * ε * M ≤ CL * (r₂ * e) :=
      (mul_le_mul_of_nonneg_right hCεC hM').trans (mul_le_mul_of_nonneg_left hM hCL)
    have b4 : Λ * dμ0 ≤ Λ * (p₂ * e) := mul_le_mul_of_nonneg_left hdμ0 hΛ
    rw [hr] at b3
    have e1 : (Λ * p₂ + CL * (4 + 2 * p₂) + 4 * z₂) * e =
        Λ * (p₂ * e) + CL * e + CL * (p₂ * e) + CL * e + CL * ((2 + p₂) * e) + 4 * (z₂ * e) := by
      ring
    linarith only [Lm, b1, b2, b3, b4, hdζ0, e1]
  · have b1 : CL * (e + dx) ≤ CL * (2 * e) := by
      have : q₂ * e ≤ 1 * e := mul_le_mul_of_nonneg_right hq he.le
      exact mul_le_mul_of_nonneg_left (by linarith only [hdx, this]) hCL
    have b2 : CL * ε * (dμ0 + M) ≤ CL * ((p₂ + r₂) * e) :=
      (mul_le_mul_of_nonneg_right hCεC (add_nonneg hdμ0' hM')).trans
        (mul_le_mul_of_nonneg_left (by linarith only [hdμ0, hM]) hCL)
    have hz1 : dζ1 ≤ CL * (4 + 2 * p₂) * e := by
      rw [hr] at b2
      have e1 : CL * (4 + 2 * p₂) * e = CL * (2 * e) + CL * ((p₂ + (2 + p₂)) * e) := by ring
      linarith only [LZ, b1, b2, e1]
    have c1 := mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ 2 * ℓ ^ 2)
    have c2 := mul_le_mul_of_nonneg_left hM hCNW
    have e1 : (2 * ℓ ^ 2 * (CL * (4 + 2 * p₂)) + CNW * r₂) * e =
        2 * ℓ ^ 2 * (CL * (4 + 2 * p₂) * e) + CNW * (r₂ * e) := by ring
    linarith only [NW, c1, c2, e1]

/-- **The last map along the cone** (arithmetic). -/
theorem last_arith {e dG gF gF' nt dn Gv dμ dnw Bμ Bw Cf ε ℓ : ℝ}
    (he : 0 < e) (hdG : 3 / 4 * e ≤ dG) (hdG' : |dG| ≤ 5 / 4 * e)
    (hgap : |gF - gF' - dG| ≤ 8 / 7 * (|dG| * nt) + 64 / 49 * (Gv * dn))
    (hnt0 : 0 ≤ nt) (hnt : nt ≤ 4 * (Cf * ε) * ℓ ^ 2) (hGv0 : 0 ≤ Gv) (hGv : Gv ≤ Cf * ε)
    (hdn0 : 0 ≤ dn) (hdn : dn ≤ 4 * (ℓ ^ 2 * dμ + Cf * ε * dnw)) (hdμ0 : 0 ≤ dμ)
    (hdnw0 : 0 ≤ dnw) (hdμ : dμ ≤ Bμ * e) (hdnw : dnw ≤ Bw * e) (hCf : 0 ≤ Cf) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1)
    (hK : Cf * (64 * ℓ ^ 2 + 40 / 7 * ℓ ^ 2 + 256 / 49 * (ℓ ^ 2 * Bμ + Cf * Bw)) * ε ≤ 1 / 2) :
    0 < gF - gF' := by
  have hCε : 0 ≤ Cf * ε := mul_nonneg hCf hε0
  have hℓ2 : 0 ≤ ℓ ^ 2 := sq_nonneg _
  have t1 : |dG| * nt ≤ 5 / 4 * e * (4 * (Cf * ε) * ℓ ^ 2) :=
    mul_le_mul hdG' hnt hnt0 (by linarith)
  have hBe : 0 ≤ Bw * e := hdnw0.trans hdnw
  have hdn2 : dn ≤ 4 * (ℓ ^ 2 * (Bμ * e) + Cf * (Bw * e)) := by
    have a1 := mul_le_mul_of_nonneg_left hdμ hℓ2
    have a2 := mul_le_mul_of_nonneg_left hdnw hCε
    have a3 : Cf * ε * (Bw * e) ≤ Cf * (Bw * e) := by
      have := mul_le_mul_of_nonneg_left hε1 hCf
      have := mul_le_mul_of_nonneg_right this hBe
      linarith only [this]
    linarith only [hdn, a1, a2, a3]
  have t2 : Gv * dn ≤ Cf * ε * (4 * (ℓ ^ 2 * (Bμ * e) + Cf * (Bw * e))) :=
    mul_le_mul hGv hdn2 hdn0 hCε
  have e1 : 8 / 7 * (5 / 4 * e * (4 * (Cf * ε) * ℓ ^ 2)) +
      64 / 49 * (Cf * ε * (4 * (ℓ ^ 2 * (Bμ * e) + Cf * (Bw * e)))) =
      Cf * (40 / 7 * ℓ ^ 2 + 256 / 49 * (ℓ ^ 2 * Bμ + Cf * Bw)) * ε * e := by ring
  have hK' : Cf * (40 / 7 * ℓ ^ 2 + 256 / 49 * (ℓ ^ 2 * Bμ + Cf * Bw)) * ε ≤ 1 / 2 := by
    have : 0 ≤ Cf * (64 * ℓ ^ 2) * ε := mul_nonneg (mul_nonneg hCf (by positivity)) hε0
    have e2 : Cf * (64 * ℓ ^ 2 + 40 / 7 * ℓ ^ 2 + 256 / 49 * (ℓ ^ 2 * Bμ + Cf * Bw)) * ε =
        Cf * (64 * ℓ ^ 2) * ε + Cf * (40 / 7 * ℓ ^ 2 + 256 / 49 * (ℓ ^ 2 * Bμ + Cf * Bw)) * ε := by
      ring
    linarith only [hK, this, e2]
  have t3 := mul_le_mul_of_nonneg_right hK' he.le
  have g1 := (abs_le.1 hgap).1
  linarith only [g1, t1, t2, e1, t3, hdG, he]

/-! ### The last map along two histories -/

section Last

variable {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- **`Re ǧ_N` in terms of the outputs of the step `N_h`**:
`ǧ_N = ǧ_{N_h+1}/(1 + n)`, `n = nCor(μ_{N_h+1}, Z_{N_h+2} w^{(1)}_{N_h+1}/L^{2(N_h+1)})`. -/
theorem gFin_eq_div {Nh : ℕ} (hV : ∀ j < Nh, ValidAt R j) (hVL : ValidAtL R Nh)
    (t : Hist.Seq (Xs R)) :
    gFin R Nh t = ((((histOut R Nh t).g.re : ℝ) : ℂ) /
      (1 + nCor (((histOut R Nh t).nu.re : ℝ) : ℂ) (nW1H R (Nh + 1) t))).re := by
  have HI := LL.rawInv_succL hV hVL t
  have hρ := hVL.2.2.2.2.1
  have hρ8 := hVL.2.2.2.2.2.1
  have hZ : (histOut R Nh t).st.Z ≠ 0 := HI.Z_ne_zero (by linarith)
  have hζ : ‖stZeta R (histOut R Nh t).st‖ ≤ 1 / 8 := (norm_stZeta_le hρ _).trans hρ8
  have hZ' : stZ' R (histOut R Nh t).st ≠ 0 := mul_ne_zero hZ (one_add_ne_zero (by linarith))
  have hn : nCor (stNu R (Nh + 1) (histOut R Nh t).st (histOut R Nh t).nu.re)
      (histOut R Nh t).st.w1 = nCor (((histOut R Nh t).nu.re : ℝ) : ℂ) (nW1H R (Nh + 1) t) := by
    unfold nW1H
    rw [rawHist_succ]
    unfold nCor stNu nW1 stZ' stZeta
    congr 1
    ring
  unfold gFin
  rw [lastG_eq R Nh t hZ']
  unfold stGr
  rw [hn]

end Last

/-! ### Strict monotonicity of `b ↦ Re ǧ_N` -/

set_option maxHeartbeats 4000000 in
/-- **`b ↦ Re ǧ_N(b)` is strictly increasing** on the `b` with an admissible trajectory, from the
cone at the horizon `N_h` (`traj_cone_top_z`), the difference bounds of the step `N_h`
(`TOP`, from `LL.lip_rg_z2`) and the explicit last map. -/
theorem gFin_strictMonoOn {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {Nh : ℕ}
    {κ cg cm cT CL aB ε Cf CNW p q r s p₂ q₂ r₂ z₂ ℓ : ℝ} (hRℓ : R.ℓ = ℓ)
    (H : HHyp (rgData R) ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT Nh CL aB ε)
    (HM : MonoZHyp (rgData R) ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT Nh (zetaH R) CL
      (CL * ε) CL 4 ε (3 / 4))
    (hC : MonoZCoef ((L : ℝ) ^ 2) κ CL (CL * ε) CL 4 (3 / 4) p q r s p₂ q₂ r₂ z₂)
    (hp₂ : p₂ = pTwo L CL) (hr₂ : r₂ = 2 + p₂) (hz₂ : z₂ = 2 * (2 * CL + 1)) (hq₂ : q₂ ≤ 1)
    (hV : ∀ j < Nh, ValidAt R j) (hVL : ValidAtL R Nh)
    (TOP : ∀ t t', InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT ε Nh t →
        InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT ε Nh t' →
      ∀ M, 0 ≤ M → (∀ i < Nh, (3 / 4 : ℝ) ^ (Nh - 1 - i) * dist3 (t i) (t' i) ≤ M) →
      |(rgData R).G Nh t - (rgData R).G Nh t' - ((t Nh).1 - (t' Nh).1)| ≤
        CL * ε * |(t Nh).1 - (t' Nh).1| +
        CL * ε * |(t Nh).2.1 - (t' Nh).2.1| + CL * ‖(t Nh).2.2 - (t' Nh).2.2‖ + CL * ε * M ∧
      |(rgData R).m Nh t - (rgData R).m Nh t'| ≤ CL * |(t Nh).1 - (t' Nh).1| +
        CL * ε * |(t Nh).2.1 - (t' Nh).2.1| + CL * ‖(t Nh).2.2 - (t' Nh).2.2‖ +
        CL * ε * M + 4 * ‖zetaH R Nh t - zetaH R Nh t'‖ ∧
      ‖zetaH R (Nh + 1) t - zetaH R (Nh + 1) t'‖ ≤
        CL * (|(t Nh).1 - (t' Nh).1| + ‖(t Nh).2.2 - (t' Nh).2.2‖) +
        CL * ε * (|(t Nh).2.1 - (t' Nh).2.1| + M) ∧
      ‖nW1H R (Nh + 1) t - nW1H R (Nh + 1) t'‖ ≤
        2 * ℓ ^ 2 * ‖zetaH R (Nh + 1) t - zetaH R (Nh + 1) t'‖ + CNW * M)
    (hglue : ∀ b μ₀, Admissible (rgData R) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
      GlueOut R Nh Cf (Hist.traj (rgData R) ((L : ℝ) ^ 2) b μ₀))
    (hCL : 0 ≤ CL) (hCf : 0 ≤ Cf) (hCNW : 0 ≤ CNW) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hL2 : 2 ≤ L)
    (hkf : kFin L ℓ CL Cf CNW * ε ≤ 1 / 2) :
    StrictMonoOn (fun b => gFin R Nh (Hist.traj (rgData R) ((L : ℝ) ^ 2) b
      (Hist.muc (rgData R) ((L : ℝ) ^ 2) κ cm cT Nh ε b)))
      {b | ∃ μ, Admissible (rgData R) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ} := by
  intro b hb b' hb' hbb
  have hspec : ∀ b, (∃ μ, Admissible (rgData R) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ) →
      Admissible (rgData R) ((L : ℝ) ^ 2) κ cm cT Nh ε b
        (Hist.muc (rgData R) ((L : ℝ) ^ 2) κ cm cT Nh ε b) := fun b hb => by
    unfold Hist.muc; rw [dif_pos hb]; exact hb.choose_spec
  have hv := hspec b hb
  have hu := hspec b' hb'
  obtain ⟨k1, k2, k3, k4, k5⟩ := traj_cone_top_z H HM hC hbb hv hu
  have htu := Hist.admissible_InDh H hu Nh le_rfl
  have htv := Hist.admissible_InDh H hv Nh le_rfl
  have gu := (hglue _ _ hu).1
  have gv := (hglue _ _ hv).1
  show gFin R Nh (Hist.traj (rgData R) ((L : ℝ) ^ 2) b (Hist.muc (rgData R) ((L : ℝ) ^ 2) κ cm cT Nh ε b)) <
    gFin R Nh (Hist.traj (rgData R) ((L : ℝ) ^ 2) b' (Hist.muc (rgData R) ((L : ℝ) ^ 2) κ cm cT Nh ε b'))
  generalize Hist.traj (rgData R) ((L : ℝ) ^ 2) b' (Hist.muc (rgData R) ((L : ℝ) ^ 2) κ cm cT Nh ε b') = u
    at k1 k2 k3 k4 k5 htu gu ⊢
  generalize Hist.traj (rgData R) ((L : ℝ) ^ 2) b (Hist.muc (rgData R) ((L : ℝ) ^ 2) κ cm cT Nh ε b) = v
    at k1 k2 k3 k4 k5 htv gv ⊢
  have hM0 := hmax_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) u v Nh
  have hMb := hmax_bound (by norm_num : (0 : ℝ) ≤ 3 / 4) u v Nh
  obtain ⟨T1, T2, T3, T4⟩ := TOP u v htu htv _ hM0 hMb
  rw [abs_of_pos k1] at T1 T2 T3
  have hgu := htu.1 Nh le_rfl
  have hgv := htv.1 Nh le_rfl
  -- the cone constants
  have hcl : CL * ε + CL * ε * p₂ + CL * q₂ + CL * ε * r₂ ≤ 1 / 4 := by
    have := hC.hw; unfold cLoss at this; linarith only [this]
  have hΛ1 : (1 : ℝ) < (L : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ L := by exact_mod_cast hL2
    nlinarith
  have hp0 : 0 ≤ p₂ := by
    rw [hp₂]; unfold pTwo
    exact div_nonneg (by linarith only [hCL]) (by linarith only [hΛ1])
  have hP : 0 ≤ pTwo L CL := hp₂ ▸ hp0
  have hB1 : 0 ≤ bMu L CL := by
    unfold bMu
    have h1 := mul_nonneg (sq_nonneg (L : ℝ)) hP
    have h2 := mul_nonneg hCL (by linarith only [hP] : (0 : ℝ) ≤ 4 + 2 * pTwo L CL)
    linarith only [h1, h2, hCL]
  have hB2 : 0 ≤ bWz L ℓ CL CNW := by
    unfold bWz bZe
    have h2 := mul_nonneg hCL (by linarith only [hP] : (0 : ℝ) ≤ 4 + 2 * pTwo L CL)
    have h3 := mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * ℓ ^ 2) h2
    have h4 := mul_nonneg hCNW (by linarith only [hP] : (0 : ℝ) ≤ 2 + pTwo L CL)
    linarith only [h3, h4]
  obtain ⟨c1, c2, c3, c4⟩ := top_cone_arith (Λ := (L : ℝ) ^ 2) k1 hCL hε0.le hε1 hp0 hq₂ hr₂
    (by positivity) hCNW hcl (abs_nonneg _) (norm_nonneg _) hM0 k5 k2 k3 k4 T1 T2 T3 T4
  -- `δμ_{N_h+1}`
  have hμd : |(histOut R Nh u).nu.re - (histOut R Nh v).nu.re| ≤ bMu L CL *
      ((u Nh).1 - (v Nh).1) := by
    have e1 : (histOut R Nh u).nu.re - (histOut R Nh v).nu.re =
        ((rgData R).m Nh u - (rgData R).m Nh v) + (L : ℝ) ^ 2 * ((u Nh).2.1 - (v Nh).2.1) := by
      show (histOut R Nh u).nu.re - (histOut R Nh v).nu.re =
        ((histOut R Nh u).nu.re - (L : ℝ) ^ 2 * (u Nh).2.1 -
          ((histOut R Nh v).nu.re - (L : ℝ) ^ 2 * (v Nh).2.1)) +
          (L : ℝ) ^ 2 * ((u Nh).2.1 - (v Nh).2.1)
      ring
    rw [e1]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (L : ℝ) ^ 2)]
    have e2 : bMu L CL = (L : ℝ) ^ 2 * p₂ + CL * (4 + 2 * p₂) + 4 * z₂ := by
      rw [hp₂, hz₂]; rfl
    rw [e2]; linarith only [c3]
  have hwd : ‖nW1H R (Nh + 1) u - nW1H R (Nh + 1) v‖ ≤
      bWz L ℓ CL CNW * ((u Nh).1 - (v Nh).1) := by
    have e2 : bWz L ℓ CL CNW = 2 * ℓ ^ 2 * (CL * (4 + 2 * p₂)) + CNW * r₂ := by
      rw [hr₂, hp₂]; rfl
    rw [e2]; exact c4
  -- the last map
  have hℓ2 : R.ℓ ^ 2 = ℓ ^ 2 := by rw [hRℓ]
  have hwu := (LL.nW1H_succ_le hV hVL u).trans (le_of_eq hℓ2)
  have hwv := (LL.nW1H_succ_le hV hVL v).trans (le_of_eq hℓ2)
  have hCe : ∀ x : ℝ, 0 < x → x ≤ ε → Cf * x ≤ Cf * ε := fun x _ hx =>
    mul_le_mul_of_nonneg_left hx hCf
  have hμu : |(histOut R Nh u).nu.re| ≤ Cf * ε :=
    (Complex.abs_re_le_norm _).trans (gu.2.2.1.trans (hCe _ hgu.1 hgu.2.1))
  have hμv : |(histOut R Nh v).nu.re| ≤ Cf * ε :=
    (Complex.abs_re_le_norm _).trans (gv.2.2.1.trans (hCe _ hgv.1 hgv.2.1))
  have hGv : |(histOut R Nh v).g.re| ≤ Cf * ε :=
    (Complex.abs_re_le_norm _).trans (gv.2.2.2.1.trans (hCe _ hgv.1 hgv.2.1))
  have hkf' : 64 * (Cf * ε * ℓ ^ 2) ≤ 1 / 2 := by
    have h0 : 0 ≤ Cf * (40 / 7 * ℓ ^ 2 + 256 / 49 * (ℓ ^ 2 * bMu L CL +
        Cf * bWz L ℓ CL CNW)) * ε := by
      have h5 := mul_nonneg (sq_nonneg ℓ) hB1
      have h6 := mul_nonneg hCf hB2
      have h7 : 0 ≤ 40 / 7 * ℓ ^ 2 + 256 / 49 * (ℓ ^ 2 * bMu L CL + Cf * bWz L ℓ CL CNW) := by
        have := sq_nonneg ℓ
        linarith only [h5, h6, this]
      exact mul_nonneg (mul_nonneg hCf h7) hε0.le
    unfold kFin at hkf
    have e1 : Cf * (64 * ℓ ^ 2 + 40 / 7 * ℓ ^ 2 + 256 / 49 * (ℓ ^ 2 * bMu L CL +
        Cf * bWz L ℓ CL CNW)) * ε = 64 * (Cf * ε * ℓ ^ 2) + Cf * (40 / 7 * ℓ ^ 2 +
        256 / 49 * (ℓ ^ 2 * bMu L CL + Cf * bWz L ℓ CL CNW)) * ε := by ring
    linarith only [hkf, h0, e1]
  have hnd : ∀ (μ : ℝ) (w : ℂ), |μ| ≤ Cf * ε → ‖w‖ ≤ ℓ ^ 2 → ‖4 * (μ : ℂ) * w‖ ≤ 1 / 8 := by
    intro μ w hμ hw
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, show ‖(4 : ℂ)‖ = 4 by norm_num]
    have := mul_le_mul hμ hw (norm_nonneg _) (mul_nonneg hCf hε0.le)
    linarith only [this, hkf']
  have hnt : ‖nCor (((histOut R Nh u).nu.re : ℝ) : ℂ) (nW1H R (Nh + 1) u)‖ ≤
      4 * (Cf * ε) * ℓ ^ 2 := by
    unfold nCor
    refine (norm_clampDisk_le_self (by norm_num) _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, show ‖(4 : ℂ)‖ = 4 by norm_num]
    have := mul_le_mul hμu hwu (norm_nonneg _) (mul_nonneg hCf hε0.le)
    linarith only [this]
  have hdn := nCor_sub_le (μ := (histOut R Nh v).nu.re) (μ' := (histOut R Nh u).nu.re)
    (w := nW1H R (Nh + 1) v) (w' := nW1H R (Nh + 1) u) hμu hwv (hnd _ _ hμv hwv)
    (hnd _ _ hμu hwu)
  have hgap := last_map_diff (g := (histOut R Nh u).g.re) (g' := (histOut R Nh v).g.re)
    (norm_nCor_le (((histOut R Nh u).nu.re : ℝ) : ℂ) (nW1H R (Nh + 1) u))
    (norm_nCor_le (((histOut R Nh v).nu.re : ℝ) : ℂ) (nW1H R (Nh + 1) v))
  rw [← gFin_eq_div R hV hVL u, ← gFin_eq_div R hV hVL v] at hgap
  have hpos := last_arith (Bμ := bMu L CL) (Bw := bWz L ℓ CL CNW) (ℓ := ℓ) k1 c1 c2 hgap
    (norm_nonneg _) hnt (abs_nonneg _) hGv (norm_nonneg _)
    hdn (abs_nonneg _) (norm_nonneg _) hμd hwd hCf hε0.le hε1
    (by unfold kFin at hkf; exact hkf)
  linarith only [hpos]

/-! ### Continuity of the shooting solution -/

/-- **Continuity of a shooting solution** in a parameter `m ∈ S`: `f(m, ·)` strictly increasing
on `U m`, `(m, b) ↦ f(m, b)` continuous on the relatively open `{(m, b) : m ∈ S, b ∈ U m}`, and
`bs m ∈ U m` solving `f(m, bs m) = y`. -/
theorem contOn_shoot {S : Set ℝ} {U : ℝ → Set ℝ} {f : ℝ → ℝ → ℝ} {y : ℝ} {bs : ℝ → ℝ}
    (hO : ∃ O : Set (ℝ × ℝ), IsOpen O ∧ O ∩ (S ×ˢ univ) = {q | q.1 ∈ S ∧ q.2 ∈ U q.1})
    (hc : ContinuousOn (fun q : ℝ × ℝ => f q.1 q.2) {q | q.1 ∈ S ∧ q.2 ∈ U q.1})
    (hmono : ∀ m ∈ S, StrictMonoOn (f m) (U m))
    (hbs : ∀ m ∈ S, bs m ∈ U m ∧ f m (bs m) = y) :
    ContinuousOn bs S := by
  intro m₁ hm₁
  obtain ⟨O, hOo, hOe⟩ := hO
  obtain ⟨hb₁U, hb₁y⟩ := hbs m₁ hm₁
  have hmemO : (m₁, bs m₁) ∈ O := by
    have : (m₁, bs m₁) ∈ O ∩ (S ×ˢ univ) := by rw [hOe]; exact ⟨hm₁, hb₁U⟩
    exact this.1
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.isOpen_iff.1 hOo _ hmemO
  have mem : ∀ m ∈ S, dist m m₁ < δ₀ → ∀ b, dist b (bs m₁) < δ₀ → b ∈ U m :=
    fun m hm hd b hb => by
      have h1 : (m, b) ∈ O := hball (by
        rw [Metric.mem_ball, Prod.dist_eq]; exact max_lt hd hb)
      have h2 : (m, b) ∈ O ∩ (S ×ˢ univ) := ⟨h1, hm, mem_univ _⟩
      rw [hOe] at h2
      exact h2.2
  rw [Metric.continuousWithinAt_iff]
  intro η hη
  obtain ⟨d, hd⟩ : ∃ d, d = min η δ₀ / 2 := ⟨_, rfl⟩
  have hd0 : 0 < d := by rw [hd]; exact half_pos (lt_min hη hδ₀)
  have hdη : d < η := by rw [hd]; linarith [min_le_left η δ₀]
  have hdδ : d < δ₀ := by rw [hd]; linarith [min_le_right η δ₀]
  have hdlo : dist (bs m₁ - d) (bs m₁) < δ₀ := by
    rw [Real.dist_eq, show bs m₁ - d - bs m₁ = -d by ring, abs_neg, abs_of_pos hd0]; exact hdδ
  have hdhi : dist (bs m₁ + d) (bs m₁) < δ₀ := by
    rw [Real.dist_eq, show bs m₁ + d - bs m₁ = d by ring, abs_of_pos hd0]; exact hdδ
  have h00 : dist m₁ m₁ < δ₀ := by rw [dist_self]; exact hδ₀
  have hlo := mem m₁ hm₁ h00 _ hdlo
  have hhi := mem m₁ hm₁ h00 _ hdhi
  have glo : f m₁ (bs m₁ - d) < y := by
    rw [← hb₁y]; exact hmono m₁ hm₁ hlo hb₁U (by linarith)
  have ghi : y < f m₁ (bs m₁ + d) := by
    rw [← hb₁y]; exact hmono m₁ hm₁ hb₁U hhi (by linarith)
  have hcw : ∀ b, dist b (bs m₁) < δ₀ →
      ContinuousWithinAt (fun m => f m b) (S ∩ Metric.ball m₁ δ₀) m₁ := fun b hb => by
    have h1 := hc (m₁, b) ⟨hm₁, mem m₁ hm₁ h00 b hb⟩
    exact h1.comp (f := fun m : ℝ => ((m, b) : ℝ × ℝ))
      (continuousWithinAt_id.prodMk continuousWithinAt_const)
      (fun m hm => ⟨hm.1, mem m hm.1 (Metric.mem_ball.1 hm.2) b hb⟩)
  obtain ⟨δ1, hδ1, h1⟩ := Metric.continuousWithinAt_iff.1 (hcw _ hdlo) (y - f m₁ (bs m₁ - d))
    (by linarith)
  obtain ⟨δ2, hδ2, h2⟩ := Metric.continuousWithinAt_iff.1 (hcw _ hdhi) (f m₁ (bs m₁ + d) - y)
    (by linarith)
  refine ⟨min δ₀ (min δ1 δ2), lt_min hδ₀ (lt_min hδ1 hδ2), fun {m} hm hdm => ?_⟩
  have hm0 : dist m m₁ < δ₀ := lt_of_lt_of_le hdm (min_le_left _ _)
  have hm1 : dist m m₁ < δ1 := lt_of_lt_of_le hdm ((min_le_right _ _).trans (min_le_left _ _))
  have hm2 : dist m m₁ < δ2 := lt_of_lt_of_le hdm ((min_le_right _ _).trans (min_le_right _ _))
  have hmS : m ∈ S ∩ Metric.ball m₁ δ₀ := ⟨hm, Metric.mem_ball.2 hm0⟩
  have l1 := h1 hmS hm1
  have l2 := h2 hmS hm2
  rw [Real.dist_eq] at l1 l2
  have l1' : f m (bs m₁ - d) < y := by linarith [(abs_lt.1 l1).2]
  have l2' : y < f m (bs m₁ + d) := by linarith [(abs_lt.1 l2).1]
  obtain ⟨hU, hy⟩ := hbs m hm
  have hlo' := mem m hm hm0 _ hdlo
  have hhi' := mem m hm hm0 _ hdhi
  have A : bs m₁ - d < bs m := by
    by_contra hcon
    push Not at hcon
    have := (hmono m hm).monotoneOn hU hlo' hcon
    rw [hy] at this
    linarith
  have B : bs m < bs m₁ + d := by
    by_contra hcon
    push Not at hcon
    have := (hmono m hm).monotoneOn hhi' hU hcon
    rw [hy] at this
    linarith
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-! ### The theorem -/

open Classical in
/-- **The shooting solution on the final coupling**: the `b ∈ Ufix` with `Re ǧ_N(b) = y`
(`0` if there is none). -/
def bFin {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (κ cm cT : ℝ) (Nh : ℕ)
    (ε m y : ℝ) : ℝ :=
  if h : ∃ b ∈ Ufix (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε, gFinB R κ cm cT Nh ε m b = y then
    h.choose else 0

theorem bFin_spec {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {κ cm cT : ℝ}
    {Nh : ℕ} {ε m y : ℝ}
    (h : ∃ b ∈ Ufix (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε, gFinB R κ cm cT Nh ε m b = y) :
    bFin R κ cm cT Nh ε m y ∈ Ufix (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε ∧
      gFinB R κ cm cT Nh ε m (bFin R κ cm cT Nh ε m y) = y := by
  unfold bFin
  rw [dif_pos h]
  exact h.choose_spec

set_option maxHeartbeats 20000000 in
/-- **Expected result `thm:flow` with the last two steps, and the shooting on `ǧ_N`, with
uniqueness and continuity in `m²`.** The conclusions of `thm_flow_complete`, and: for every mass
`b ↦ Re ǧ_N(b)` is strictly increasing on `Ufix`; for every `β_R ≥ 2/ε` the solution `b ∈ Ufix` of
`Re ǧ_N(b) = 1/β_R` is unique, and the shooting solution `m² ↦ bFin(m², 1/β_R)` is continuous on
`mRange L N`. -/
theorem thm_flow_complete2 : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ κ cg cm cT ε Ke Cf Cb : ℝ, 0 < ℓ ∧ 0 < A ∧ 0 < ρ ∧ 0 < ε ∧ 0 ≤ κ ∧ κ < 1 ∧
      0 < cg ∧ 0 < cm ∧ 0 < cT ∧ 0 ≤ Ke ∧ 0 ≤ Cf ∧ 0 ≤ Cb ∧ 2 * Cb * ε ≤ 1 / 4 ∧ ρ ≤ 1 / 8 ∧ SplitSmall Pc L ρ ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N →
    ∀ Nh : ℕ, Nh + 2 = N →
      (∀ m ∈ mRange L N, FixedConcl (rgDataM R m) ((L : ℝ) ^ 2) (betaL L) κ cg cm cT Nh ε
          (eRange (betaL L) Ke 1)) ∧
      MsqConcl R κ cm cT Nh ε (mRange L N) ∧
      (∀ m ∈ mRange L N, ∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
        GlueOut (R.withMsq m) Nh Cf (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ∧
          BandOut (R.withMsq m) Nh Cb (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) ∧
      ContinuousOn (fun q : ℝ × ℝ => gFinB R κ cm cT Nh ε q.1 q.2)
        (UfixM R κ cm cT Nh ε (mRange L N)) ∧
      (∀ m ∈ mRange L N, ∀ βR : ℝ, 2 / ε ≤ βR →
        ∃ b ∈ Ufix (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε, gFinB R κ cm cT Nh ε m b = 1 / βR) ∧
      (∀ m ∈ mRange L N, ∀ b ∈ Ufix (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε, ∀ βR : ℝ,
        gFinB R κ cm cT Nh ε m b = 1 / βR →
        |Hist.gN (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b - 1 / βR| ≤ 4 * Cb * (1 / βR) ^ 2) ∧
      -- strict monotonicity, uniqueness, continuity in `m²`
      (∀ m ∈ mRange L N, StrictMonoOn (gFinB R κ cm cT Nh ε m)
        (Ufix (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε)) ∧
      (∀ m ∈ mRange L N, ∀ βR : ℝ, 2 / ε ≤ βR →
        ∃! b, b ∈ Ufix (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε ∧
          gFinB R κ cm cT Nh ε m b = 1 / βR) ∧
      (∀ βR : ℝ, 2 / ε ≤ βR →
        (∀ m ∈ mRange L N, bFin R κ cm cT Nh ε m (1 / βR) ∈
            Ufix (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε ∧
          gFinB R κ cm cT Nh ε m (bFin R κ cm cT Nh ε m (1 / βR)) = 1 / βR) ∧
        ContinuousOn (fun m => bFin R κ cm cT Nh ε m (1 / βR)) (mRange L N)) ∧
      -- validity of the parameters (exported for the zero-mode integration)
      (∀ m ∈ mRange L N, (∀ j < Nh, ValidAt (R.withMsq m) j) ∧ ValidAtL (R.withMsq m) Nh) := by
  obtain ⟨L₀, hL₀⟩ := flow_complete2_hyp0
  refine ⟨max L₀ 2, fun L _ hL => ?_⟩
  obtain ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, CL, aB, Cf, Cb, CNW, hCNW, hkf, hε1, hℓ, hA, hρ, hε,
    hκ0, hκ1, hcg, hcm, hcT, hKe, hCL, hCf, hCb, hCbε, hcgε, he, ha0, hs, hC, hρ8, hspl, hcov, h⟩ :=
    hL₀ L (le_trans (le_max_left _ _) hL)
  obtain ⟨p, q, r, s, p₂, q₂, r₂, z₂, hCo, hp₂, hr₂, hz₂, hq₂⟩ := hC
  refine ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, Cf, Cb, hℓ, hA, hρ, hε, hκ0, hκ1, hcg, hcm, hcT, hKe,
    hCf, hCb, hCbε, hρ8, hspl, fun N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh => ?_⟩
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast le_trans (le_max_right _ _) hL
  have hL2n : 2 ≤ L := le_trans (le_max_right _ _) hL
  -- the bundles at every mass
  have hyp : ∀ m ∈ mRange L N, FinHypZ (R.withMsq m) Nh κ cg cm cT ε CL aB
      (eRange (betaL L) Ke 1) ∧
      (∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
        GlueOut (R.withMsq m) Nh Cf (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ∧
          BandOut (R.withMsq m) Nh Cb (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) ∧
      StrictMonoOn (gFinB R κ cm cT Nh ε m) (Ufix (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε) := by
    intro m hm
    obtain ⟨⟨e, hV, HD, H, HZ, HM, he0, F1s, heb, hej⟩, hglue, htop⟩ :=
      h N (R.withMsq m) hP hi0 hRℓ hRA hRρ (by omega) hm.1 hm.2 Nh hNh.le
    have hmass : m * ((L : ℝ) ^ (Nh + 1)) ^ 2 ≤ 1 := by
      have := msq_horizon (L := (L : ℝ)) (by linarith) hm.2 (Nh := Nh) (k := 0) (by omega)
      simpa using this
    obtain ⟨hVL, TOP⟩ := htop hNh
    have hmono := gFin_strictMonoOn (R.withMsq m) hRℓ H HM hCo hp₂ hr₂ hz₂ hq₂ hV hVL TOP
      (fun b μ₀ hb => (hglue hNh b μ₀ hb).1) hCL hCf hCNW hε hε1 hL2n hkf
    refine ⟨⟨hV, H, HZ, HM, HD, e,
      { hc := hcg.le, he := he0
        hE := sum_e_le hL2 hm.1.le hKe H.hβ.le he0 hmass heb hej
        F1s := F1s }⟩, hglue hNh, ?_⟩
    refine hmono.mono fun b hb => ?_
    obtain ⟨μ, hμ, -⟩ := hb
    exact ⟨μ, hμ⟩
  obtain ⟨hFix, hMsq⟩ := flow_finalZ_of
    ⟨hρ, hρ8, hcov, hε, hcgε, he, ha0, hs, ⟨p, q, r, s, p₂, q₂, r₂, z₂, hCo⟩⟩ R hP hRρ
    (by omega) (by omega) le_rfl (fun m hm => (hyp m hm).1)
  have hcont := gFinB_contOn R (S := mRange L N) le_rfl (κ := κ) (cm := cm) (cT := cT) (ε := ε)
    (by omega) (by rw [hRρ]; exact hρ.le) (by rw [hRρ]; exact hρ8)
    (by rw [hP, hRρ]; exact hcov N (by omega)) (fun m hm => (hyp m hm).1.valid) hMsq
  obtain ⟨s1, s2⟩ := complete_shoot R hFix (fun m hm b μ₀ hb => ((hyp m hm).2.1 b μ₀ hb).2) hcont
    hε hCb hCbε
  have hmono : ∀ m ∈ mRange L N, StrictMonoOn (gFinB R κ cm cT Nh ε m)
      (Ufix (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε) := fun m hm => (hyp m hm).2.2
  refine ⟨hFix, hMsq, fun m hm => (hyp m hm).2.1, hcont, s1, s2, hmono, ?_, ?_, ?_⟩
  · intro m hm βR hβR
    obtain ⟨b, hb, hby⟩ := s1 m hm βR hβR
    refine ⟨b, ⟨hb, hby⟩, fun b' hb' => ?_⟩
    rcases lt_trichotomy b' b with hlt | heq | hgt
    · have := hmono m hm hb'.1 hb hlt; rw [hb'.2, hby] at this; exact absurd this (lt_irrefl _)
    · exact heq
    · have := hmono m hm hb hb'.1 hgt; rw [hb'.2, hby] at this; exact absurd this (lt_irrefl _)
  · intro βR hβR
    have hspec : ∀ m ∈ mRange L N, bFin R κ cm cT Nh ε m (1 / βR) ∈
        Ufix (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε ∧
        gFinB R κ cm cT Nh ε m (bFin R κ cm cT Nh ε m (1 / βR)) = 1 / βR :=
      fun m hm => bFin_spec R (s1 m hm βR hβR)
    refine ⟨hspec, contOn_shoot (U := fun m => Ufix (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε)
      (f := gFinB R κ cm cT Nh ε) hMsq.isOpen hcont hmono hspec⟩
  · intro m hm
    exact ⟨(hyp m hm).1.valid, ((h N (R.withMsq m) hP hi0 hRℓ hRA hRρ (by omega) hm.1 hm.2 Nh
      hNh.le).2.2 hNh).1⟩

end

end Step2
