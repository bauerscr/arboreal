import Step2.Map.RGMap
import Step2.Coup.VNorm

/-!
# One-step bounds in normalised coordinates (`h02uv-outline.tex`, Section `sec:reduction`)

`d = 2`. At the causal field scale `ℓ_j = s ℓ`, `s = |Z|^{-1/2}`:

* `Fnorm_VfamL_le`: `‖V_v‖_{T_j(ℓ)} ≤ c_M ℓ² (L^{2j}|ν| + |z| + |y|) + 4 ℓ⁴ |g|`;
* `Fnorm_VfamL_norm`: in normalised couplings, `‖V_{(z, y, μZ/L^{2j} - a m², g Z²)}‖_{T_j(sℓ)} ≤
  c_M ℓ² (|μ| + |a/Z| m² L^{2j} + |z/Z| + |y/Z|) + 4 ℓ⁴ |g|`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

variable {L N : ℕ} [NeZero L]

/-- The number of quadratic monomials in `d = 2`. -/
abbrev cM : ℝ := (Fintype.card (Mono 2) : ℝ)

theorem card_blockSet_le' (j : ℕ) (hj : j ≤ N) (b : Fin 2 → ℕ) :
    ((blockSet (L := L) (N := N) j b).card : ℝ) ≤ ((L : ℝ) ^ j) ^ 2 := by
  by_cases hb : b ∈ blockIdx (L := L) (N := N) j
  · rw [card_blockSet hj hb]; push_cast; ring_nf; rfl
  · rw [blockSet_eq_empty hb, card_empty, Nat.cast_zero]; positivity

/-- **The block norm of a coupling polynomial** (`d = 2`). -/
theorem Tj_VfamL_le (j : ℕ) (hj : j ≤ N) {ℓ : ℝ} (hℓ : 0 < ℓ) (v : Fin 4 → ℂ) (b : Fin 2 → ℕ) :
    Tj 2 (L : ℝ) j ℓ (VfamL (d := 2) (L := L) (N := N) j v b : Alg 2 L N) ≤
      ENNReal.ofReal (cM * ℓ ^ 2 * (((L : ℝ) ^ j) ^ 2 * ‖v 2‖ + ‖v 0‖ + ‖v 1‖) +
        4 * ℓ ^ 4 * ‖v 3‖) := by
  have h := Tj_Vcoup_le (d := 2) (L := L) (N := N) (by norm_num) j hℓ (Coup.ofVec v)
    (blockSet j b)
  have e : (VfamL (d := 2) (L := L) (N := N) j v b : Alg 2 L N) =
      Vcoup (Coup.ofVec v) (blockSet j b) := rfl
  rw [e]
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hh : (0 : ℝ) < (L : ℝ) ^ j := pow_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L))) j
  have hc := card_blockSet_le' (L := L) (N := N) j hj b
  simp only [Coup.ofVec]
  set n := ((blockSet (L := L) (N := N) j b).card : ℝ)
  set h2 := ((L : ℝ) ^ j) ^ 2 with hh2
  have hh2p : 0 < h2 := by positivity
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hM : 0 ≤ cM := Nat.cast_nonneg _
  have e2 : n * (cM * ℓ ^ 2 * (‖v 2‖ + (‖v 0‖ + ‖v 1‖) * h2⁻¹) + (2 : ℕ) ^ 2 * ‖v 3‖ * ℓ ^ 4 * h2⁻¹)
      = (n / h2) * (cM * ℓ ^ 2 * (h2 * ‖v 2‖ + ‖v 0‖ + ‖v 1‖) + 4 * ℓ ^ 4 * ‖v 3‖) := by
    field_simp; push_cast; ring
  rw [e2]
  have hq : n / h2 ≤ 1 := (div_le_one hh2p).2 hc
  have hX : 0 ≤ cM * ℓ ^ 2 * (h2 * ‖v 2‖ + ‖v 0‖ + ‖v 1‖) + 4 * ℓ ^ 4 * ‖v 3‖ := by positivity
  calc n / h2 * (cM * ℓ ^ 2 * (h2 * ‖v 2‖ + ‖v 0‖ + ‖v 1‖) + 4 * ℓ ^ 4 * ‖v 3‖)
      ≤ 1 * (cM * ℓ ^ 2 * (h2 * ‖v 2‖ + ‖v 0‖ + ‖v 1‖) + 4 * ℓ ^ 4 * ‖v 3‖) :=
        mul_le_mul_of_nonneg_right hq hX
    _ = _ := one_mul _

theorem Fnorm_VfamL_le (j : ℕ) (hj : j ≤ N) {ℓ : ℝ} (hℓ : 0 < ℓ) (v : Fin 4 → ℂ) :
    Fnorm j ℓ (VfamL (d := 2) (L := L) (N := N) j v) ≤
      ENNReal.ofReal (cM * ℓ ^ 2 * (((L : ℝ) ^ j) ^ 2 * ‖v 2‖ + ‖v 0‖ + ‖v 1‖) +
        4 * ℓ ^ 4 * ‖v 3‖) :=
  iSup₂_le fun b _ => Tj_VfamL_le j hj hℓ v b

/-- **The coupling polynomial at the causal field scale**, with the couplings normalised by
`Z₁` and the norm at `s ℓ`, `s = |Z|^{-1/2}`, `r = |Z₁/Z|`: `ν = μ Z₁/L^{2j} - a m²`,
`g_raw = g_c Z₁²`; the bound is `c_M ℓ² (r|μ| + |a/Z| m² L^{2j} + |z/Z| + |y/Z|) + 4 ℓ⁴ r² |g_c|`. -/
theorem Fnorm_VfamL_norm2 (j : ℕ) (hj : j ≤ N) {ℓ : ℝ} (hℓ : 0 < ℓ) {Z : ℂ} (hZ : Z ≠ 0)
    (Z₁ z y a gc : ℂ) (μ msq : ℝ) :
    Fnorm j (fscale Z * ℓ) (VfamL (d := 2) (L := L) (N := N) j
        ![z, y, (μ : ℂ) * Z₁ / (L : ℂ) ^ (2 * j) - a * msq, gc * Z₁ ^ 2]) ≤
      ENNReal.ofReal (cM * ℓ ^ 2 * (‖Z₁ / Z‖ * |μ| + ‖a / Z‖ * |msq| * ((L : ℝ) ^ j) ^ 2 +
        ‖z / Z‖ + ‖y / Z‖) + 4 * ℓ ^ 4 * (‖Z₁ / Z‖ ^ 2 * ‖gc‖)) := by
  have hZn : 0 < ‖Z‖ := norm_pos_iff.2 hZ
  have hs := fscale_pos hZ
  refine (Fnorm_VfamL_le j hj (mul_pos hs hℓ) _).trans (ENNReal.ofReal_le_ofReal ?_)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three]
  have hs2 : fscale Z ^ 2 = ‖Z‖⁻¹ := by
    unfold fscale; rw [Real.sq_sqrt (inv_nonneg.2 hZn.le)]
  have hh : (0 : ℝ) < (L : ℝ) ^ j := pow_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L))) j
  set h2 := ((L : ℝ) ^ j) ^ 2 with hh2
  have hL2 : ‖(L : ℂ) ^ (2 * j)‖ = h2 := by
    rw [norm_pow, Complex.norm_natCast, hh2, ← pow_mul, mul_comm]
  have hZ1 : ‖Z₁‖ = ‖Z₁ / Z‖ * ‖Z‖ := by rw [norm_div, div_mul_cancel₀ _ hZn.ne']
  have hnu : h2 * ‖(μ : ℂ) * Z₁ / (L : ℂ) ^ (2 * j) - a * msq‖ ≤
      ‖Z‖ * (‖Z₁ / Z‖ * |μ| + ‖a / Z‖ * |msq| * h2) := by
    have h1 : ‖(μ : ℂ) * Z₁ / (L : ℂ) ^ (2 * j) - a * msq‖ ≤
        |μ| * ‖Z₁‖ / h2 + ‖a‖ * |msq| := by
      refine (norm_sub_le _ _).trans (le_of_eq ?_)
      rw [norm_div, norm_mul, norm_mul, hL2, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs]
    have ha : ‖a‖ = ‖a / Z‖ * ‖Z‖ := by rw [norm_div, div_mul_cancel₀ _ hZn.ne']
    calc h2 * ‖(μ : ℂ) * Z₁ / (L : ℂ) ^ (2 * j) - a * msq‖
        ≤ h2 * (|μ| * ‖Z₁‖ / h2 + ‖a‖ * |msq|) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ‖Z‖ * (‖Z₁ / Z‖ * |μ| + ‖a / Z‖ * |msq| * h2) := by
          rw [ha, hZ1, mul_add, mul_div_assoc', mul_div_cancel_left₀ _ (by positivity : h2 ≠ 0)]
          ring
  have hz : ‖z‖ = ‖z / Z‖ * ‖Z‖ := by rw [norm_div, div_mul_cancel₀ _ hZn.ne']
  have hy : ‖y‖ = ‖y / Z‖ * ‖Z‖ := by rw [norm_div, div_mul_cancel₀ _ hZn.ne']
  have hg : ‖gc * Z₁ ^ 2‖ = ‖Z₁ / Z‖ ^ 2 * ‖gc‖ * ‖Z‖ ^ 2 := by
    rw [norm_mul, norm_pow, hZ1]; ring
  rw [hg, mul_pow, hs2, mul_pow, show (fscale Z) ^ 4 = (fscale Z ^ 2) ^ 2 by ring, hs2]
  have hM : 0 ≤ cM := Nat.cast_nonneg _
  have e1 : cM * (‖Z‖⁻¹ * ℓ ^ 2) * (h2 * ‖(μ : ℂ) * Z₁ / (L : ℂ) ^ (2 * j) - a * msq‖ + ‖z‖ + ‖y‖)
      ≤ cM * (‖Z‖⁻¹ * ℓ ^ 2) * (‖Z‖ * (‖Z₁ / Z‖ * |μ| + ‖a / Z‖ * |msq| * h2) + ‖z / Z‖ * ‖Z‖ +
        ‖y / Z‖ * ‖Z‖) := by
    rw [hz, hy]; gcongr
  have hZi : ‖Z‖⁻¹ * ‖Z‖ = 1 := inv_mul_cancel₀ hZn.ne'
  have e2 : cM * (‖Z‖⁻¹ * ℓ ^ 2) * (‖Z‖ * (‖Z₁ / Z‖ * |μ| + ‖a / Z‖ * |msq| * h2) +
        ‖z / Z‖ * ‖Z‖ + ‖y / Z‖ * ‖Z‖) =
      cM * ℓ ^ 2 * (‖Z₁ / Z‖ * |μ| + ‖a / Z‖ * |msq| * h2 + ‖z / Z‖ + ‖y / Z‖) := by
    calc _ = cM * ℓ ^ 2 * (‖Z‖⁻¹ * ‖Z‖) *
          (‖Z₁ / Z‖ * |μ| + ‖a / Z‖ * |msq| * h2 + ‖z / Z‖ + ‖y / Z‖) := by ring
      _ = _ := by rw [hZi, mul_one]
  have e3 : 4 * ((‖Z‖⁻¹) ^ 2 * ℓ ^ 4) * (‖Z₁ / Z‖ ^ 2 * ‖gc‖ * ‖Z‖ ^ 2) =
      4 * ℓ ^ 4 * (‖Z₁ / Z‖ ^ 2 * ‖gc‖) := by
    calc _ = 4 * ℓ ^ 4 * (‖Z₁ / Z‖ ^ 2 * ‖gc‖) * (‖Z‖⁻¹ * ‖Z‖) ^ 2 := by ring
      _ = _ := by rw [hZi, one_pow, mul_one]
  linarith

/-- **The coupling polynomial at the causal field scale**, in normalised couplings: with
`s = |Z|^{-1/2}`, `ν = μ Z/L^{2j} - a m²`, `g_raw = g Z²`, the norm at `s ℓ` is bounded by
`c_M ℓ² (|μ| + |a/Z| m² L^{2j} + |z/Z| + |y/Z|) + 4 ℓ⁴ |g|`. -/
theorem Fnorm_VfamL_norm (j : ℕ) (hj : j ≤ N) {ℓ : ℝ} (hℓ : 0 < ℓ) {Z : ℂ} (hZ : Z ≠ 0)
    (z y a : ℂ) (μ g msq : ℝ) :
    Fnorm j (fscale Z * ℓ) (VfamL (d := 2) (L := L) (N := N) j
        ![z, y, (μ : ℂ) * Z / (L : ℂ) ^ (2 * j) - a * msq, (g : ℂ) * Z ^ 2]) ≤
      ENNReal.ofReal (cM * ℓ ^ 2 * (|μ| + ‖a / Z‖ * |msq| * ((L : ℝ) ^ j) ^ 2 +
        ‖z / Z‖ + ‖y / Z‖) + 4 * ℓ ^ 4 * |g|) := by
  have hZn : 0 < ‖Z‖ := norm_pos_iff.2 hZ
  have hs := fscale_pos hZ
  refine (Fnorm_VfamL_le j hj (mul_pos hs hℓ) _).trans (ENNReal.ofReal_le_ofReal ?_)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three]
  have hs2 : fscale Z ^ 2 = ‖Z‖⁻¹ := by
    unfold fscale; rw [Real.sq_sqrt (inv_nonneg.2 hZn.le)]
  have hh : (0 : ℝ) < (L : ℝ) ^ j := pow_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L))) j
  set h2 := ((L : ℝ) ^ j) ^ 2 with hh2
  have hL2 : ‖(L : ℂ) ^ (2 * j)‖ = h2 := by
    rw [norm_pow, Complex.norm_natCast, hh2, ← pow_mul, mul_comm]
  have hnu : h2 * ‖(μ : ℂ) * Z / (L : ℂ) ^ (2 * j) - a * msq‖ ≤
      ‖Z‖ * (|μ| + ‖a / Z‖ * |msq| * h2) := by
    have h1 : ‖(μ : ℂ) * Z / (L : ℂ) ^ (2 * j) - a * msq‖ ≤
        |μ| * ‖Z‖ / h2 + ‖a‖ * |msq| := by
      refine (norm_sub_le _ _).trans (le_of_eq ?_)
      rw [norm_div, norm_mul, norm_mul, hL2, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs]
    have ha : ‖a‖ = ‖a / Z‖ * ‖Z‖ := by rw [norm_div, div_mul_cancel₀ _ hZn.ne']
    calc h2 * ‖(μ : ℂ) * Z / (L : ℂ) ^ (2 * j) - a * msq‖
        ≤ h2 * (|μ| * ‖Z‖ / h2 + ‖a‖ * |msq|) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ‖Z‖ * (|μ| + ‖a / Z‖ * |msq| * h2) := by
          rw [ha, mul_add, mul_div_assoc', mul_div_cancel_left₀ _ (by positivity : h2 ≠ 0)]; ring
  have hz : ‖z‖ = ‖z / Z‖ * ‖Z‖ := by rw [norm_div, div_mul_cancel₀ _ hZn.ne']
  have hy : ‖y‖ = ‖y / Z‖ * ‖Z‖ := by rw [norm_div, div_mul_cancel₀ _ hZn.ne']
  have hg : ‖(g : ℂ) * Z ^ 2‖ = |g| * ‖Z‖ ^ 2 := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  rw [hg, mul_pow, hs2, mul_pow, show (fscale Z) ^ 4 = (fscale Z ^ 2) ^ 2 by ring, hs2]
  have hM : 0 ≤ cM := Nat.cast_nonneg _
  have e1 : cM * (‖Z‖⁻¹ * ℓ ^ 2) * (h2 * ‖(μ : ℂ) * Z / (L : ℂ) ^ (2 * j) - a * msq‖ + ‖z‖ + ‖y‖)
      ≤ cM * (‖Z‖⁻¹ * ℓ ^ 2) * (‖Z‖ * (|μ| + ‖a / Z‖ * |msq| * h2) + ‖z / Z‖ * ‖Z‖ +
        ‖y / Z‖ * ‖Z‖) := by
    rw [hz, hy]; gcongr
  have e2 : cM * (‖Z‖⁻¹ * ℓ ^ 2) * (‖Z‖ * (|μ| + ‖a / Z‖ * |msq| * h2) + ‖z / Z‖ * ‖Z‖ +
        ‖y / Z‖ * ‖Z‖) = cM * ℓ ^ 2 * (|μ| + ‖a / Z‖ * |msq| * h2 + ‖z / Z‖ + ‖y / Z‖) := by
    have hZi : ‖Z‖⁻¹ * ‖Z‖ = 1 := inv_mul_cancel₀ hZn.ne'
    calc cM * (‖Z‖⁻¹ * ℓ ^ 2) * (‖Z‖ * (|μ| + ‖a / Z‖ * |msq| * h2) + ‖z / Z‖ * ‖Z‖ +
          ‖y / Z‖ * ‖Z‖) = cM * ℓ ^ 2 * (‖Z‖⁻¹ * ‖Z‖) *
          (|μ| + ‖a / Z‖ * |msq| * h2 + ‖z / Z‖ + ‖y / Z‖) := by ring
      _ = _ := by rw [hZi, mul_one]
  have e3 : 4 * ((‖Z‖⁻¹) ^ 2 * ℓ ^ 4) * (|g| * ‖Z‖ ^ 2) = 4 * ℓ ^ 4 * |g| := by
    have hZi : ‖Z‖⁻¹ * ‖Z‖ = 1 := inv_mul_cancel₀ hZn.ne'
    calc 4 * ((‖Z‖⁻¹) ^ 2 * ℓ ^ 4) * (|g| * ‖Z‖ ^ 2) = 4 * ℓ ^ 4 * |g| * (‖Z‖⁻¹ * ‖Z‖) ^ 2 := by
          ring
      _ = _ := by rw [hZi, one_pow, mul_one]
  linarith

/-! ### The pieces of one raw step -/

section Pieces

variable (R : RGPar 2 L N) (j : ℕ) (st : RawSt 2 L N) (g μ : ℝ)

/-- The absorbed dressed coupling `ζ_j`. -/
def stZeta : ℂ := absorbZeta R st.Z (st.z + st.y)

/-- `a = Z ζ_j`. -/
def stA : ℂ := st.Z * stZeta R st

/-- `y_c = Z clamp_ρ(y/Z)`. -/
def stYc : ℂ := st.Z * clampDisk R.ρ (st.y / st.Z)

/-- The covariance of the step. -/
def stCov : Matrix (Lam 2 L N) (Lam 2 L N) ℂ := rawCov R j (Function.update st.ζ j (stZeta R st))

/-- The absorbed polynomial `Δ`. -/
def stDelta : Fam 2 L N := VfamL j ![stA R st - stYc R st, stYc R st, stA R st * R.msq, 0]

/-- `Z_{j+1} = Z_j (1 + ζ_j)`, the normalisation of the couplings of the step. -/
def stZ' : ℂ := st.Z * (1 + stZeta R st)

/-- The raw mass coupling `μ Z_{j+1}/L^{2j}`. -/
def stNu : ℂ := (μ : ℂ) * stZ' R st / (L : ℂ) ^ (2 * j)

/-- The raw quartic coupling, divided by `Z_{j+1}²`: `ǧ/(1 + n)`. -/
def stGr : ℂ := (g : ℂ) / (1 + nCor (stNu R j st μ) st.w1)

/-- The coupling polynomial `V♭`. -/
def stVf : Fam 2 L N := VfamL j ![st.z + stYc R st - stA R st, st.y - stYc R st,
  stNu R j st μ - stA R st * R.msq, stGr R j st g μ * stZ' R st ^ 2]

variable (D : Fam 2 L N) (K : Act 2 L N)

theorem rawStep_D : (rawStep R j st g μ D K).D = Dnext j (stCov R j st) (stVf R j st g μ) st.Wl D :=
  rfl

theorem rawStep_K : (rawStep R j st g μ D K).K =
    Kconn (j + 1) (Kplus j (stCov R j st) (stVf R j st g μ) (st.Wl + D)
      (Kflat j (stDelta R j st) K)) := rfl

end Pieces

/-! ### Inactive clamps -/

theorem stA_eq {R : RGPar 2 L N} {st : RawSt 2 L N} (hZ : st.Z ≠ 0)
    (h : ‖(st.z + st.y) / st.Z‖ ≤ R.ρ) : stA R st = st.z + st.y := by
  unfold stA stZeta absorbZeta
  rw [clampDisk_of_le h, mul_div_cancel₀ _ hZ]

theorem stYc_eq {R : RGPar 2 L N} {st : RawSt 2 L N} (hZ : st.Z ≠ 0)
    (h : ‖st.y / st.Z‖ ≤ R.ρ) : stYc R st = st.y := by
  unfold stYc
  rw [clampDisk_of_le h, mul_div_cancel₀ _ hZ]

/-- **With inactive clamps, `V♭` has no gradient couplings.** -/
theorem stVf_eq {R : RGPar 2 L N} {j : ℕ} {st : RawSt 2 L N} {g μ : ℝ} (hZ : st.Z ≠ 0)
    (h1 : ‖(st.z + st.y) / st.Z‖ ≤ R.ρ) (h2 : ‖st.y / st.Z‖ ≤ R.ρ) :
    stVf R j st g μ = VfamL j ![0, 0, stNu R j st μ - stA R st * R.msq,
      stGr R j st g μ * stZ' R st ^ 2] := by
  unfold stVf
  rw [stYc_eq hZ h2, stA_eq hZ h1, sub_self, sub_self]

/-! ### Bounds on `V♭`, `Δ`, `K♭` -/

theorem norm_nCor_le (ν w1 : ℂ) : ‖nCor ν w1‖ ≤ 1 / 8 := norm_clampDisk_le (by norm_num) _

theorem norm_one_add_nCor (ν w1 : ℂ) : 7 / 8 ≤ ‖1 + nCor ν w1‖ := by
  have h := norm_nCor_le ν w1
  have := norm_sub_le (1 + nCor ν w1) (nCor ν w1)
  simp only [add_sub_cancel_right, norm_one] at this
  linarith

theorem one_add_nCor_ne (ν w1 : ℂ) : 1 + nCor ν w1 ≠ 0 := by
  intro h; have := norm_one_add_nCor ν w1; rw [h, norm_zero] at this; norm_num at this

/-- `|ǧ/(1 + n)| ≤ (8/7) |ǧ|`. -/
theorem norm_stGr_le (R : RGPar 2 L N) (j : ℕ) (st : RawSt 2 L N) (g μ : ℝ) :
    ‖stGr R j st g μ‖ ≤ 8 / 7 * |g| := by
  unfold stGr
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_le_iff₀ (by
    linarith [norm_one_add_nCor (stNu R j st μ) st.w1])]
  have := norm_one_add_nCor (stNu R j st μ) st.w1
  nlinarith [abs_nonneg g]

theorem norm_stZeta_le {R : RGPar 2 L N} (hρ : 0 ≤ R.ρ) (st : RawSt 2 L N) :
    ‖stZeta R st‖ ≤ R.ρ := absorb_le R hρ _ _

theorem norm_stA_div {R : RGPar 2 L N} {st : RawSt 2 L N} (hZ : st.Z ≠ 0) :
    stA R st / st.Z = stZeta R st := by
  unfold stA; rw [mul_div_cancel_left₀ _ hZ]

/-- **The norm of `Δ`** at the causal field scale: `≤ c_M ℓ² (m² L^{2j} + 3) ρ`. -/
theorem Fnorm_stDelta_le {R : RGPar 2 L N} {j : ℕ} (hj : j ≤ N) {ℓ : ℝ}
    (hℓ : 0 < ℓ) {st : RawSt 2 L N} (hZ : st.Z ≠ 0) (η : ℝ) (hζ : ‖stZeta R st‖ ≤ η)
    (hy : ‖stYc R st / st.Z‖ ≤ η) :
    Fnorm j (fscale st.Z * ℓ) (stDelta R j st) ≤
      ENNReal.ofReal (cM * ℓ ^ 2 * (η * |R.msq| * ((L : ℝ) ^ j) ^ 2 + 3 * η)) := by
  have hZn : 0 < ‖st.Z‖ := norm_pos_iff.2 hZ
  have e : stDelta R j st = VfamL j ![stA R st - stYc R st, stYc R st,
      (0 : ℝ) * st.Z / (L : ℂ) ^ (2 * j) - (-stA R st) * R.msq, (0 : ℝ) * st.Z ^ 2] := by
    unfold stDelta; congr 2; ext i; fin_cases i <;> simp
  rw [e]
  refine (Fnorm_VfamL_norm j hj hℓ hZ _ _ _ 0 0 R.msq).trans (ENNReal.ofReal_le_ofReal ?_)
  simp only [abs_zero, zero_add, mul_zero, add_zero]
  have hM : 0 ≤ cM := Nat.cast_nonneg _
  have h1 : ‖-stA R st / st.Z‖ = ‖stZeta R st‖ := by
    rw [neg_div, norm_neg, norm_stA_div hZ]
  have h2 : ‖(stA R st - stYc R st) / st.Z‖ ≤ 2 * η := by
    rw [sub_div, norm_stA_div hZ]
    exact (norm_sub_le _ _).trans (by linarith)
  rw [h1]
  have h0 : 0 ≤ η := (norm_nonneg _).trans hζ
  have : ‖stZeta R st‖ * |R.msq| * ((L : ℝ) ^ j) ^ 2 + ‖(stA R st - stYc R st) / st.Z‖ +
      ‖stYc R st / st.Z‖ ≤ η * |R.msq| * ((L : ℝ) ^ j) ^ 2 + 3 * η := by
    have : ‖stZeta R st‖ * |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ η * |R.msq| * ((L : ℝ) ^ j) ^ 2 := by
      gcongr
    linarith
  exact mul_le_mul_of_nonneg_left this (by positivity)

theorem eps_stDelta (R : RGPar 2 L N) (j : ℕ) (st : RawSt 2 L N) (b : Fin 2 → ℕ) :
    ε (stDelta R j st b : Alg 2 L N) = 0 := eps_VfamL j _ b

/-- **`K♭` with the weight slack**: `‖K♭‖_{j, A e^{-δ}} ≤ e^{4δ} ‖K‖_{j, A}`. -/
theorem Knorm_stKflat_le {R : RGPar 2 L N} (j : ℕ) {ℓ A δ : ℝ} (hℓ : 0 < ℓ) (hA : 0 ≤ A)
    (hδ : 0 ≤ δ) (st : RawSt 2 L N) (hΔ : Fnorm j ℓ (stDelta R j st) ≤ ENNReal.ofReal δ)
    (K : Act 2 L N) :
    Knorm j ℓ (A * Real.exp (-δ)) (Kflat j (stDelta R j st) K) ≤
      ENNReal.ofReal (Real.exp (4 * δ)) * Knorm j ℓ A K := by
  have h := Knorm_Kflat_le (d := 2) j hℓ hA hδ (stDelta R j st) (eps_stDelta R j st)
    (fun b hb => (le_iSup₂ (f := fun b (_ : b ∈ blockIdx (L := L) (N := N) j) =>
      Tj 2 (L : ℝ) j ℓ (stDelta R j st b : Alg 2 L N)) b hb).trans hΔ) K
  norm_num at h ⊢
  exact h

/-- `Knorm` is monotone in the weight. -/
theorem Knorm_mono_A {j : ℕ} {ℓ A A' : ℝ} (hA : 0 ≤ A) (hAA : A ≤ A') (K : Act 2 L N) :
    Knorm j ℓ A K ≤ Knorm j ℓ A' K := by
  unfold Knorm
  gcongr


end

end Step2
