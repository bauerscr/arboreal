import Step2.Map.RawMap
import Step2.Map.FieldScaleC
import Flow2.Reduction

/-!
# The renormalisation group maps on histories (`h02uv-outline.tex`, Section `sec:reduction`)

Raw fields with *causal field scales*. A history `t : Seq X` with
`X_j = BSp j ℓ × ASp j ℓ A` and the marginal and relevant coordinates `(g, μ)` determines, by the
causal recursion `rawHist`, the raw state at scale `j`:
* the raw gradient couplings `(z_j, y_j)` of `V_j`,
* `W^lin_j`, the field strength `Z_j` and the dressed history `ζ_0, …, ζ_{j-1}`.

The field scale at scale `j` is `ℓ_j = s_j ℓ` with `s_j = |Z_j|^{-1/2}` (`fscale`); the
coordinates are rescaled by the *complex* consistent root `u_j = ∏_{i<j}(1 + ζ_i)^{1/2}` of `Z_j`
(`RawSt.u`, `|u_j| = s_j⁻¹`), so that no phase of `Z_j` enters the normalised step. The
coordinates are normalised so that the norms are those at `ℓ_j`:
* `g = g_raw / Z_j²`, `μ = L^{2j} ν_raw / Z_j`;
* `x_j = σ_{u_j⁻¹} (D_j, K_j)`, so `‖x_j‖_{ℓ} = ‖(D_j, K_j)‖_{ℓ_j}` (`Step2.Map.FieldScaleC`).

One step (`rawStep`): the absorbed dressed coupling is the radial clamp
`ζ_j = clamp_ρ((z_j + y_j)/Z_j)` (`absorbZeta`, continuous), so `|ζ_j| ≤ ρ`. The covariance is the
raw `Γ^int_{j+1}(ζ)`, with Gram scale `s_{j+1} ℓ/4` (`ValidAt`); the step reads its input at `ℓ_j`
and writes its output at `ℓ_{j+1}`, and `ℓ_{j+1} + s_{j+1} ℓ/4 ≤ 2ℓ_j` with room to spare for
`|ζ_j| ≤ ρ ≤ 1/8` (`scale_ok`; the room is used for the Lipschitz bounds). Then `a = Z ζ_j`, `y_c = Z clamp_ρ(y/Z)`, `Δ = V_{(a - y_c, y_c, a m², 0)}` (both gradient
couplings are absorbed; the full step allows any `Δ = V_{(z', y', (z'+y') m², 0)}` by summation
by parts), `V♭ = V_{(z + y_c - a, y - y_c, ν_raw - a m², g_raw)}`,
`K♭ = Kflat Δ K`, and the outputs are `V_{j+1}`, `D_{j+1} = Dnext`, `K_{j+1} = Kconn (Kplus …)`.

The maps of `Flow2.Hist.HData` are `G_j = Re g_{j+1}`, `m_j = Re μ_{j+1} - L² μ_j` and
`T_j = σ_{u_{j+1}⁻¹} (D, K)_{j+1}`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

/-- The parameters of the flow. -/
structure RGPar (d L N : ℕ) where
  P : PtFamily
  msq : ℝ
  ℓ : ℝ
  A : ℝ
  i₀ : Fin d
  ρ : ℝ

/-- The raw state at scale `j` that is not a coordinate. -/
structure RawSt (d L N : ℕ) [NeZero L] where
  z : ℂ
  y : ℂ
  Wl : Fam d L N
  Z : ℂ
  ζ : ℕ → ℂ
  /-- The accumulated zero mode `w^{(1)} = ∑_{k<j} ∑_x Γ^int_{k+1}(x, 0)`. -/
  w1 : ℂ
  /-- The consistent square root `u_j = ∏_{i<j} (1 + ζ_i)^{1/2}` of `Z_j` (principal branches);
  the field scale of the coordinates is `u_j` (complex). -/
  u : ℂ

/-- The field-scale factor `s = |Z|^{-1/2}`. -/
def fscale (Z : ℂ) : ℝ := Real.sqrt ‖Z‖⁻¹

/-- The radial clamp `u ↦ u min(1, r/|u|)` to the disc of radius `r` (continuous). -/
def clampDisk (r : ℝ) (u : ℂ) : ℂ := u * ((min 1 (r / ‖u‖) : ℝ) : ℂ)

/-- The absorbed dressed coupling: the clamp of `ζ = (z + y)/Z` to the disc of radius `ρ`. -/
def absorbZeta (R : RGPar d L N) (Z w : ℂ) : ℂ := clampDisk R.ρ (w / Z)

/-- The covariance of the step: the raw `Γ^int_{j+1}` of the dressed history `ζ`. -/
def rawCov (R : RGPar d L N) (j : ℕ) (ζ : ℕ → ℂ) : Matrix (Lam d L N) (Lam d L N) ℂ :=
  DressedFRD.kmat ((⟨L, N, R.msq, DressedFRD.frdC R.P R.msq L N, ζ⟩ :
    DressedFRD.Data d (L ^ N)).Gint j)

/-- The outputs of one raw step. -/
structure RawOut (d L N : ℕ) [NeZero L] where
  st : RawSt d L N
  nu : ℂ
  g : ℂ
  D : Fam d L N
  K : Act d L N

/-- The marginal coordinate change `ǧ = g (1 + n)`, `n = clamp_{1/8}(4 ν w^{(1)})` (continuous). -/
def nCor (ν w1 : ℂ) : ℂ := clampDisk (1 / 8) (4 * ν * w1)

/-- **One raw step**, from the state, the coordinates `(ǧ, μ)` and the raw `(D, K)` at scale
`j`. The couplings are normalised by `Z_{j+1} = Z_j (1 + ζ_j)`, which includes the coupling `ζ_j`
absorbed in this step: `ν_raw = μ Z_{j+1}/L^{2j}`, `g_raw = ǧ Z_{j+1}²/(1 + n)`. The outputs are
normalised by `Z_{j+2} = Z_{j+1}(1 + ζ_{j+1})`, `ζ_{j+1} = clamp_ρ((z' + y')/Z_{j+1})`, which is the
coupling absorbed in the next step. So the field strength generated in a step enters the
coordinates of that step, and `ǧ' = (1 + n') κ_g/Z_{j+2}²` with `n' = nCor κ_ν w^{(1)}_{j+1}`. -/
def rawStep (R : RGPar d L N) (j : ℕ) (st : RawSt d L N) (g μ : ℝ) (D : Fam d L N)
    (K : Act d L N) : RawOut d L N :=
  let ζj : ℂ := absorbZeta R st.Z (st.z + st.y)
  let a : ℂ := st.Z * ζj
  let ζ' : ℕ → ℂ := Function.update st.ζ j ζj
  let C := rawCov R j ζ'
  let Z1 : ℂ := st.Z * (1 + ζj)
  let nuR : ℂ := (μ : ℂ) * Z1 / (L : ℂ) ^ (2 * j)
  let gR : ℂ := (g : ℂ) / (1 + nCor nuR st.w1) * Z1 ^ 2
  let yc : ℂ := st.Z * clampDisk R.ρ (st.y / st.Z)
  let Δ : Fam d L N := VfamL j ![a - yc, yc, a * R.msq, 0]
  let Vf : Fam d L N := VfamL j ![st.z + yc - a, st.y - yc, nuR - a * R.msq, gR]
  let Kf : Act d L N := Kflat j Δ K
  let W : Fam d L N := st.Wl + D
  let κ : Fin 4 → ℂ := cvec4 (blockSet (L := L) (N := N) (j + 1) 0) R.i₀
    (Vnext2 j C Vf W Kf 0)
  let w1' : ℂ := st.w1 + ∑ x, C x 0
  let Z2 : ℂ := Z1 * (1 + absorbZeta R Z1 (κ 0 + κ 1))
  let u' : ℂ := st.u * csq (1 + ζj)
  { st := ⟨κ 0, κ 1, WlinNext j C Vf st.Wl, Z1, ζ', w1', u'⟩
    nu := κ 2 * (L : ℂ) ^ (2 * (j + 1)) / Z2
    g := κ 3 / Z2 ^ 2 * (1 + nCor (κ 2) w1')
    D := Dnext j C Vf st.Wl D
    K := Kconn (j + 1) (Kplus j C Vf W Kf) }

/-! ### The clamp -/

theorem norm_clampDisk_le {r : ℝ} (hr : 0 ≤ r) (u : ℂ) : ‖clampDisk r u‖ ≤ r := by
  unfold clampDisk
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_one
    (div_nonneg hr (norm_nonneg _)))]
  rcases (norm_nonneg u).eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul]; exact hr
  · calc ‖u‖ * min 1 (r / ‖u‖) ≤ ‖u‖ * (r / ‖u‖) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hpos.le
      _ = r := mul_div_cancel₀ _ hpos.ne'

theorem clampDisk_of_le {r : ℝ} {u : ℂ} (h : ‖u‖ ≤ r) : clampDisk r u = u := by
  unfold clampDisk
  rcases (norm_nonneg u).eq_or_lt with h0 | hpos
  · rw [norm_eq_zero.1 h0.symm, zero_mul]
  · rw [min_eq_left ((one_le_div hpos).2 h), Complex.ofReal_one, mul_one]

/-- The absorbed dressed coupling is admissible. -/
theorem absorb_le (R : RGPar d L N) (hρ : 0 ≤ R.ρ) (Z w : ℂ) : ‖absorbZeta R Z w‖ ≤ R.ρ :=
  norm_clampDisk_le hρ _

/-! ### Field scales -/

theorem fscale_pos {Z : ℂ} (hZ : Z ≠ 0) : 0 < fscale Z :=
  Real.sqrt_pos.2 (inv_pos.2 (norm_pos_iff.2 hZ))

theorem norm_one_add_ge {ζ : ℂ} : 1 - ‖ζ‖ ≤ ‖1 + ζ‖ := by
  have := norm_sub_norm_le (1 : ℂ) (-ζ)
  simp only [norm_one, norm_neg, sub_neg_eq_add] at this
  linarith

theorem one_add_ne_zero {ζ : ℂ} (h : ‖ζ‖ < 1) : 1 + ζ ≠ 0 := fun h0 => by
  have := norm_one_add_ge (ζ := ζ); rw [h0, norm_zero] at this; linarith

/-- `‖u‖ = s⁻¹` for `u² = Z`. -/
theorem norm_eq_inv_fscale {u Z : ℂ} (hu : u ^ 2 = Z) : ‖u‖ = (fscale Z)⁻¹ := by
  rw [fscale, ← hu, norm_pow, Real.sqrt_inv, Real.sqrt_sq (norm_nonneg _), inv_inv]

/-- `s' = s |1 + ζ|^{-1/2}`. -/
theorem fscale_mul {Z ζ : ℂ} : fscale (Z * (1 + ζ)) = fscale Z * fscale (1 + ζ) := by
  unfold fscale
  rw [norm_mul, mul_inv, Real.sqrt_mul (inv_nonneg.2 (norm_nonneg _))]

/-- `|1 + ζ|^{-1/2} ≤ 15/14` for `|ζ| ≤ 1/8`. -/
theorem fscale_one_add_le {ζ : ℂ} (h : ‖ζ‖ ≤ 1 / 8) : fscale (1 + ζ) ≤ 15 / 14 := by
  unfold fscale
  have h1 : 7 / 8 ≤ ‖1 + ζ‖ := by linarith [norm_one_add_ge (ζ := ζ)]
  rw [Real.sqrt_le_left (by norm_num)]
  rw [inv_le_comm₀ (by linarith) (by norm_num)]
  linarith

/-- `|1 + ζ|^{-1/2} ≥ 14/15` for `|ζ| ≤ 1/8`. -/
theorem fscale_one_add_ge {ζ : ℂ} (h : ‖ζ‖ ≤ 1 / 8) : 14 / 15 ≤ fscale (1 + ζ) := by
  unfold fscale
  have h1 : ‖1 + ζ‖ ≤ 9 / 8 := (norm_add_le _ _).trans (by rw [norm_one]; linarith)
  have h0 : 0 < ‖1 + ζ‖ := by linarith [norm_one_add_ge (ζ := ζ)]
  rw [Real.le_sqrt (by norm_num) (inv_nonneg.2 h0.le), le_inv_comm₀ (by norm_num) h0]
  linarith

/-- **The scales of the step are compatible**: with input scale `s ℓ`, output scale `s' ℓ`,
`s' = s |1 + ζ|^{-1/2}`, and the covariance at Gram scale `s' ℓ / 4`,
`(1 + 1/4) s' ℓ ≤ (3/2) s ℓ ≤ 2 s ℓ`. -/
theorem scale_ok {Z ζ : ℂ} (hZ : Z ≠ 0) (h : ‖ζ‖ ≤ 1 / 8) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    fscale (Z * (1 + ζ)) * ℓ + fscale (Z * (1 + ζ)) * ℓ / 4 ≤ 3 / 2 * (fscale Z * ℓ) := by
  rw [fscale_mul]
  have hs := fscale_pos hZ
  have h1 := fscale_one_add_le h
  have : fscale Z * fscale (1 + ζ) * ℓ ≤ fscale Z * (15 / 14) * ℓ := by gcongr
  nlinarith

/-! ### Histories -/

section Hist

variable (R : RGPar d L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- The coordinate space of the irrelevant variables at scale `j`. -/
abbrev Xs (j : ℕ) : Type := BSp d L N j R.ℓ × ASp d L N j R.ℓ R.A

/-- The raw `D` from the normalised coordinate `x = σ_{u⁻¹} (D, K)`, `u² = Z`. -/
def rawD (u : ℂ) {j : ℕ} (x : Xs R j) : Fam d L N := sigF u x.1.toFam

/-- The raw `K` from the normalised coordinate. -/
def rawK (u : ℂ) {j : ℕ} (x : Xs R j) : Act d L N := sigK u x.2.toAct

/-- **The raw state reconstructed from the history** (causal: uses `t_0, …, t_{j-1}`). -/
def rawHist : ℕ → Flow2.Hist.Seq (Xs R) → RawSt d L N
  | 0, _ => ⟨0, 0, 0, 1, 0, 0, 1⟩
  | j + 1, t => (rawStep R j (rawHist j t) (t j).1 (t j).2.1
      (rawD R (rawHist j t).u (t j).2.2) (rawK R (rawHist j t).u (t j).2.2)).st

/-- The output of step `j` along the history. -/
def histOut (j : ℕ) (t : Flow2.Hist.Seq (Xs R)) : RawOut d L N :=
  rawStep R j (rawHist R j t) (t j).1 (t j).2.1 (rawD R (rawHist R j t).u (t j).2.2)
    (rawK R (rawHist R j t).u (t j).2.2)

theorem rawHist_succ (j : ℕ) (t : Flow2.Hist.Seq (Xs R)) :
    rawHist R (j + 1) t = (histOut R j t).st := rfl

/-- `rawHist j` only depends on `t_0, …, t_{j-1}`. -/
theorem rawHist_causal : ∀ (j : ℕ) (t t' : Flow2.Hist.Seq (Xs R)), (∀ i < j, t i = t' i) →
    rawHist R j t = rawHist R j t'
  | 0, _, _, _ => rfl
  | j + 1, t, t', h => by
    rw [rawHist, rawHist, rawHist_causal j t t' fun i hi => h i (by omega), h j (by omega)]

theorem histOut_causal (j : ℕ) (t t' : Flow2.Hist.Seq (Xs R)) (h : ∀ i ≤ j, t i = t' i) :
    histOut R j t = histOut R j t' := by
  rw [histOut, histOut, rawHist_causal R j t t' fun i hi => h i hi.le, h j le_rfl]

end Hist

/-- **Validity of the parameters at scale `j`**: geometry, `0 ≤ ρ ≤ 1/8`, and the covariance
properties, at Gram scale `s_{j+1} ℓ/4`, for every admissible dressed history. -/
def ValidAt (R : RGPar d L N) (j : ℕ) : Prop :=
  j + 2 < N ∧ 1 ≤ d ∧ 2 ^ (d + 3) + 8 * d < L ∧ 0 ≤ R.ρ ∧ R.ρ ≤ 1 / 8 ∧ 0 < R.ℓ ∧
  ∀ ζ : ℕ → ℂ, (∀ i, ‖ζ i‖ ≤ R.ρ) →
    GoodCov2 j (fscale (∏ i ∈ range (j + 1), (1 + ζ i)) * R.ℓ / 4) (rawCov R j ζ) ∧
      TInv (rawCov R j ζ) ∧ CSym (rawCov R j ζ) ∧ ∀ x y, rawCov R j ζ x y = rawCov R j ζ y x

/-- The invariants of the raw state. -/
structure RawInv (R : RGPar d L N) (j : ℕ) (st : RawSt d L N) : Prop where
  hZprod : st.Z = ∏ i ∈ range j, (1 + st.ζ i)
  hζ : ∀ i, ‖st.ζ i‖ ≤ R.ρ
  hζ0 : ∀ i, j ≤ i → st.ζ i = 0
  hWl : st.Wl ∈ BSub (L := L) (N := N) j
  hu : st.u ^ 2 = st.Z

namespace RawInv

variable {R : RGPar d L N} {j : ℕ} {st : RawSt d L N}

/-- The dressed history after step `j`. -/
abbrev zeta' (R : RGPar d L N) (j : ℕ) (st : RawSt d L N) : ℕ → ℂ :=
  Function.update st.ζ j (absorbZeta R st.Z (st.z + st.y))

theorem zeta'_le (hρ : 0 ≤ R.ρ) (H : RawInv R j st) (i : ℕ) : ‖zeta' R j st i‖ ≤ R.ρ := by
  by_cases hi : i = j
  · subst hi
    simp only [zeta', Function.update_self]
    exact absorb_le R hρ _ _
  · simp only [zeta', Function.update_of_ne hi]; exact H.hζ i

theorem prod_zeta' (H : RawInv R j st) :
    ∏ i ∈ range (j + 1), (1 + zeta' R j st i) =
      st.Z * (1 + absorbZeta R st.Z (st.z + st.y)) := by
  rw [prod_range_succ]
  simp only [zeta', Function.update_self]
  rw [H.hZprod]
  congr 1
  refine prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (by have := mem_range.1 hi; omega)]

theorem Z_ne_zero (hρ1 : R.ρ < 1) (H : RawInv R j st) : st.Z ≠ 0 := by
  rw [H.hZprod]
  exact prod_ne_zero_iff.2 fun i _ => one_add_ne_zero ((H.hζ i).trans_lt hρ1)

/-- The covariance of step `j` has the properties of `ValidAt`. -/
theorem cov (hV : ValidAt R j) (H : RawInv R j st) :
    GoodCov2 j (fscale (st.Z * (1 + absorbZeta R st.Z (st.z + st.y))) * R.ℓ / 4)
        (rawCov R j (zeta' R j st)) ∧ TInv (rawCov R j (zeta' R j st)) ∧
      CSym (rawCov R j (zeta' R j st)) ∧
      ∀ x y, rawCov R j (zeta' R j st) x y = rawCov R j (zeta' R j st) y x := by
  have h := hV.2.2.2.2.2.2 _ (zeta'_le hV.2.2.2.1 H)
  rwa [prod_zeta' H] at h

end RawInv

theorem eps_VfamL (k : ℕ) (v : Fin 4 → ℂ) (b : Fin d → ℕ) :
    ε (VfamL (d := d) (L := L) (N := N) k v b : Alg d L N) = 0 :=
  eps_Vcoup (Coup.ofVec v) _

namespace RawInv

variable {R : RGPar d L N} {j : ℕ} {st : RawSt d L N}

/-- **The step hypotheses hold along every history**, and the invariants propagate. -/
theorem step (hV : ValidAt R j) (H : RawInv R j st) (g μ : ℝ) {D : Fam d L N} {K : Act d L N}
    (hD : D ∈ BSub (L := L) (N := N) j) (hK : K ∈ ASub (L := L) (N := N) j) :
    let out := rawStep R j st g μ D K
    RawInv R (j + 1) out.st ∧ out.D ∈ BSub (L := L) (N := N) (j + 1) ∧
      out.K ∈ ASub (L := L) (N := N) (j + 1) := by
  intro out
  obtain ⟨hC, hCt, hCs, hCsym⟩ := cov hV H
  have hV' := hV
  obtain ⟨hj2, hd, hL, hρ, -, -, -⟩ := hV'
  have hjN : j < N := by omega
  set a : ℂ := st.Z * absorbZeta R st.Z (st.z + st.y)
  set yc : ℂ := st.Z * clampDisk R.ρ (st.y / st.Z)
  set Z1 : ℂ := st.Z * (1 + absorbZeta R st.Z (st.z + st.y))
  have hRH : RawHyp j _ (rawCov R j (zeta' R j st))
      (VfamL j ![st.z + yc - a, st.y - yc,
        (μ : ℂ) * Z1 / (L : ℂ) ^ (2 * j) - a * R.msq,
        (g : ℂ) / (1 + nCor ((μ : ℂ) * Z1 / (L : ℂ) ^ (2 * j)) st.w1) * Z1 ^ 2]) :=
    ⟨hd, hL, hj2, hC, hCt, hCs, hCsym, VfamL_mem hd hL hjN _, eps_VfamL j _⟩
  have hΔ := VfamL_mem (L := L) (N := N) hd hL hjN ![a - yc, yc, a * R.msq, 0]
  have hKf := Kflat_mem hjN hΔ (eps_VfamL j _) hK
  refine ⟨⟨(prod_zeta' H).symm, zeta'_le hρ H, fun i hi => ?_, hRH.WlinNext_mem H.hWl, ?_⟩,
    hRH.Dnext_mem H.hWl hD, hRH.Kconn_mem (add_mem H.hWl hD) hKf⟩
  · show Function.update st.ζ j _ i = 0
    rw [Function.update_of_ne (by omega), H.hζ0 i (by omega)]
  · show (st.u * csq (1 + absorbZeta R st.Z (st.z + st.y))) ^ 2 =
      st.Z * (1 + absorbZeta R st.Z (st.z + st.y))
    rw [mul_pow, csq_sq, H.hu]

end RawInv

/-! ### The maps of the flow -/

section Maps

variable (R : RGPar d L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

theorem rawD_mem (Z : ℂ) {j : ℕ} (x : Xs R j) : rawD R Z x ∈ BSub (L := L) (N := N) j :=
  sigF_mem x.1.mem _

theorem rawK_mem (Z : ℂ) {j : ℕ} (x : Xs R j) : rawK R Z x ∈ ASub (L := L) (N := N) j :=
  sigK_mem x.2.mem _

/-- **The invariants hold along every history.** -/
theorem rawInv_hist (hρ : 0 ≤ R.ρ) :
    ∀ j, (∀ i < j, ValidAt R i) → ∀ t : Flow2.Hist.Seq (Xs R), RawInv R j (rawHist R j t)
  | 0, _, _ => ⟨by simp [rawHist], fun i => by simp [rawHist, hρ], fun i _ => rfl, zero_mem _,
      by simp [rawHist]⟩
  | j + 1, hV, t => by
    have H := rawInv_hist hρ j (fun i hi => hV i (by omega)) t
    exact (H.step (hV j (by omega)) (t j).1 (t j).2.1 (rawD_mem R _ _) (rawK_mem R _ _)).1

open Classical in
/-- **The irrelevant map** `T_j : Seq → X_{j+1}`, `σ_{u_{j+1}⁻¹} (D, K)_{j+1}` (zero for invalid
parameters). -/
def Tmap (j : ℕ) (t : Flow2.Hist.Seq (Xs R)) : Xs R (j + 1) :=
  if h : ∀ i ≤ j, ValidAt R i then
    (⟨sigF (histOut R j t).st.u⁻¹ (histOut R j t).D, sigF_mem
        ((rawInv_hist R (h 0 (Nat.zero_le _)).2.2.2.1 j (fun i hi => h i hi.le) t).step
          (h j le_rfl) (t j).1 (t j).2.1 (rawD_mem R _ _) (rawK_mem R _ _)).2.1 _⟩,
      ⟨sigK (histOut R j t).st.u⁻¹ (histOut R j t).K, sigK_mem
        ((rawInv_hist R (h 0 (Nat.zero_le _)).2.2.2.1 j (fun i hi => h i hi.le) t).step
          (h j le_rfl) (t j).1 (t j).2.1 (rawD_mem R _ _) (rawK_mem R _ _)).2.2 _⟩)
  else 0

/-- **The flow data** of the renormalisation group: `G_j = Re g_{j+1}`,
`m_j = Re μ_{j+1} - L² μ_j`, `T_j = σ_{u_{j+1}⁻¹} (D, K)_{j+1}`. -/
def rgData : Flow2.Hist.HData (Xs R) where
  G j t := (histOut R j t).g.re
  m j t := (histOut R j t).nu.re - (L : ℝ) ^ 2 * (t j).2.1
  T := Tmap R

theorem causal_G (j : ℕ) : Flow2.Hist.Causal j ((rgData R).G j) := fun t t' h => by
  simp only [rgData, histOut_causal R j t t' h]

theorem causal_m (j : ℕ) : Flow2.Hist.Causal j ((rgData R).m j) := fun t t' h => by
  simp only [rgData, histOut_causal R j t t' h, h j le_rfl]

theorem causal_T (j : ℕ) : Flow2.Hist.Causal j ((rgData R).T j) := fun t t' h => by
  simp only [rgData, Tmap]
  split_ifs with hv
  · have e := histOut_causal R j t t' h
    refine Prod.ext ?_ ?_
    · exact Subtype.ext (by simp only [e])
    · exact Subtype.ext (by simp only [e])
  · rfl

end Maps

end

end Step2
