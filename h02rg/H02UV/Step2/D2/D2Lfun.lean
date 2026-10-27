import Step2.D2.D2Cov

/-!
# The functional `𝔩(w) = (w, -Δ w)` on the torus as a Brillouin-zone integral (`prop:d2`, (R3'))

`𝔩(w) = ∑_x w(0,x) ((-Δ) w)(x,0)` (`lfun`). For `w = fmat ŵ` with even `ŵ` (Parseval on the
torus), `𝔩(w) = n^{-2} ∑_k λ(k) ŵ(k)²` (`lfun_fmat`). For the accumulated covariance
`w_T = cov P m² (0, T]` and `2T + 1 < n`, the torus average equals the Brillouin-zone integral
exactly: `𝔩(w_T) = (2π)^{-2} ∫_{[-π,π]²} λ ĉ_{(0,T]}²` (`lfun_cov_eq_integral_BZ`; the proof
writes `λ ĉ²` as a double integral over scales `t, t'` of polynomials of degree `≤ t + t' + 1`
in `û`, and uses Fubini).
-/

namespace Step2.D2

noncomputable section

open MeasureTheory Set Filter Topology Real FRD

variable {n : ℕ} [NeZero n]

/-- `𝔩(w) = ∑_x w(0,x) ((-Δ) w)(x,0)`. -/
def lfun (w : Matrix (Grassmann.Torus 2 n) (Grassmann.Torus 2 n) ℝ) : ℝ :=
  ∑ x, w 0 x * ((negLap : Matrix (Grassmann.Torus 2 n) (Grassmann.Torus 2 n) ℝ) * w) x 0

/-- **Parseval.** `𝔩(fmat ŵ) = n^{-2} ∑_k λ(k) ŵ(k)²` for even `ŵ`. -/
theorem lfun_fmat {w : Grassmann.Torus 2 n → ℝ} (hw : Even' w) :
    lfun (fmat w) = ((n : ℝ) ^ 2)⁻¹ * ∑ m, lam m * w m ^ 2 := by
  have h1 : lfun (fmat w) = (fmat w * ((negLap : Matrix (Grassmann.Torus 2 n)
      (Grassmann.Torus 2 n) ℝ) * fmat w)) 0 0 := by
    rw [lfun, Matrix.mul_apply]
  rw [h1, negLap_eq_fmat, fmat_mul lam_even hw,
    fmat_mul hw (fun m => by simp only [lam_even m, hw m])]
  simp only [fmat, sub_zero, char_zero_right, Complex.one_re, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun m _ => by ring

/-- The integrand over pairs of scales. -/
def Gq (P : PtFamily) (msq : ℝ) (q : ℝ × ℝ) (v : ℝ) : ℝ :=
  q.1 * q.2 * (((2 * 2 + msq) * v - msq) * (P.P q.1).eval v * (P.P q.2).eval v)

/-- `(K v - m²) (K⁻¹ ∫_S t P_t(v))² = K⁻² ∫∫_{S×S} G`, `K = 4 + m²`. -/
theorem sq_integral_eq (P : PtFamily) (msq : ℝ) (S : Set ℝ) (v : ℝ) :
    ((2 * 2 + msq) * v - msq) * ((2 * 2 + msq)⁻¹ * ∫ t in S, t * (P.P t).eval v) ^ 2 =
      (2 * 2 + msq)⁻¹ ^ 2 * ∫ q, Gq P msq q v ∂((volume.restrict S).prod (volume.restrict S)) := by
  have h := integral_prod_mul (μ := volume.restrict S) (ν := volume.restrict S)
    (fun t => t * (P.P t).eval v) (fun t => t * (P.P t).eval v)
  have e : ∀ q : ℝ × ℝ, Gq P msq q v =
      ((2 * 2 + msq) * v - msq) * ((q.1 * (P.P q.1).eval v) * (q.2 * (P.P q.2).eval v)) := by
    intro q; simp only [Gq]; ring
  simp_rw [e]
  rw [integral_const_mul, h]
  ring

theorem measurable_P_uhatC (P : PtFamily) (msq : ℝ) :
    Measurable (Function.uncurry fun (p : ℂ) (t : ℝ) => (P.P t).eval (uhatC msq p)) :=
  measurable_uncurry_of_continuous_of_measurable
    (fun t => (Polynomial.continuous _).comp (continuous_uhatC msq)) (fun p => P.measurable _)

theorem measurable_Gq2 (P : PtFamily) (msq : ℝ) :
    Measurable (Function.uncurry fun (q : ℝ × ℝ) (p : ℂ) => Gq P msq q (uhatC msq p)) := by
  have hu := measurable_P_uhatC P msq
  have m1 : Measurable fun z : (ℝ × ℝ) × ℂ => (P.P z.1.1).eval (uhatC msq z.2) := by
    have h : Measurable fun z : (ℝ × ℝ) × ℂ => (z.2, z.1.1) :=
      measurable_snd.prodMk (measurable_fst.comp measurable_fst)
    have := hu.comp h
    exact this
  have m2 : Measurable fun z : (ℝ × ℝ) × ℂ => (P.P z.1.2).eval (uhatC msq z.2) := by
    have h : Measurable fun z : (ℝ × ℝ) × ℂ => (z.2, z.1.2) :=
      measurable_snd.prodMk (measurable_snd.comp measurable_fst)
    have := hu.comp h
    exact this
  have m3 : Measurable fun z : (ℝ × ℝ) × ℂ => uhatC msq z.2 :=
    (continuous_uhatC msq).measurable.comp measurable_snd
  have m0 : Measurable fun z : (ℝ × ℝ) × ℂ => z.1.1 * z.1.2 :=
    (measurable_fst.comp measurable_fst).mul (measurable_snd.comp measurable_fst)
  exact m0.mul ((((measurable_const.mul m3).sub measurable_const).mul m1).mul m2)

/-- **`𝔩(w_T)` is a Brillouin-zone integral.** For `0 ≤ T` with `2T + 1 < n`,
`n^{-2} ∑_k λ(k) ŵ_T(k)² = (2π)^{-2} ∫_{[-π,π]²} λ ĉ_{(0,T]}²` exactly. -/
theorem lsum_eq_integral_BZ (P : PtFamily) {msq : ℝ} (hmsq : 0 ≤ msq) {T : ℝ} (hT : 0 ≤ T)
    (hn : 2 * T + 1 < n) :
    ((n : ℝ) ^ 2)⁻¹ * ∑ m : Grassmann.Torus 2 n, lam m * wt P msq (Ioc 0 T) m ^ 2 =
      ((2 * π) ^ 2)⁻¹ * ∫ p in BZ, lamC p * chat P msq (Ioc 0 T) p ^ 2 := by
  set S := Ioc (0 : ℝ) T
  set μ := (volume.restrict S).prod (volume.restrict S)
  set K := (2 * 2 + msq)
  have hK : 0 < K := by positivity
  have hpi := pi_pos
  haveI : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.2 (by simp [S])
  haveI : IsFiniteMeasure (volume.restrict BZ) :=
    isFiniteMeasure_restrict.2 isCompact_BZ.measure_lt_top.ne
  obtain ⟨K0, hK0, hKb⟩ := FRD.eval_le_const P
  have hmemS : ∀ᵐ q ∂μ, q ∈ S ×ˢ S := by
    simp only [μ]
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
  -- bound on `G`
  have hGb : ∀ q ∈ S ×ˢ S, ∀ v ∈ Icc (0 : ℝ) 2, |Gq P msq q v| ≤ T * T * ((K * 2 + msq) * K0 * K0) := by
    intro q hq v hv
    obtain ⟨h1, h2⟩ := hq
    have e1 := P.nonneg _ h1.1 v hv
    have e2 := P.nonneg _ h2.1 v hv
    have b1 := hKb _ h1.1 v hv
    have b2 := hKb _ h2.1 v hv
    have hlv : |K * v - msq| ≤ K * 2 + msq := by
      rw [abs_le]; constructor <;> nlinarith [hv.1, hv.2]
    simp only [Gq]
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos h1.1, abs_of_pos h2.1, abs_of_nonneg e1,
      abs_of_nonneg e2]
    have hq1 : q.1 ≤ T := h1.2
    have hq2 : q.2 ≤ T := h2.2
    have A1 : q.1 * q.2 ≤ T * T := mul_le_mul hq1 hq2 h2.1.le hT
    have A2 : |K * v - msq| * (P.P q.1).eval v * (P.P q.2).eval v ≤ (K * 2 + msq) * K0 * K0 :=
      mul_le_mul (mul_le_mul hlv b1 e1 (by positivity)) b2 e2 (by positivity)
    exact mul_le_mul A1 A2 (by positivity) (by positivity)
  have hGmeas_q : ∀ v, Measurable fun q : ℝ × ℝ => Gq P msq q v := by
    intro v
    simp only [Gq]
    exact (measurable_fst.mul measurable_snd).mul ((measurable_const.mul
      ((P.measurable v).comp measurable_fst)).mul ((P.measurable v).comp measurable_snd))
  have hGint : ∀ v ∈ Icc (0 : ℝ) 2, Integrable (fun q => Gq P msq q v) μ := by
    intro v hv
    refine Integrable.of_bound (hGmeas_q v).aestronglyMeasurable
      (T * T * ((K * 2 + msq) * K0 * K0)) ?_
    filter_upwards [hmemS] with q hq
    rw [Real.norm_eq_abs]; exact hGb q hq v hv
  -- the torus side
  have hA : ∀ m : Grassmann.Torus 2 n, lam m * wt P msq S m ^ 2 =
      K⁻¹ ^ 2 * ∫ q, Gq P msq q (uhat msq m) ∂μ := by
    intro m
    have hl : lam m = K * uhat msq m - msq := by
      simp only [uhat, K]; norm_num; field_simp; ring
    rw [hl, wt]
    have := sq_integral_eq P msq S (uhat msq m)
    simpa [K] using this
  -- each scale pair: torus average = BZ integral
  have hB : ∀ q ∈ S ×ˢ S, ((n : ℝ) ^ 2)⁻¹ * ∑ m : Grassmann.Torus 2 n, Gq P msq q (uhat msq m) =
      ((2 * π) ^ 2)⁻¹ * ∫ p in BZ, Gq P msq q (uhatC msq p) := by
    intro q hq
    obtain ⟨h1, h2⟩ := hq
    set g : Polynomial ℝ := Polynomial.C (q.1 * q.2) *
      ((Polynomial.C K * Polynomial.X - Polynomial.C msq) * P.P q.1 * P.P q.2)
    have hg : ∀ v, g.eval v = Gq P msq q v := by
      intro v; simp [g, Gq, K]
    have hdeg : g.natDegree + max ((0 : Fin 2 → ℤ) 0).natAbs ((0 : Fin 2 → ℤ) 1).natAbs < n := by
      simp only [Pi.zero_apply, Int.natAbs_zero, max_self, add_zero]
      have d1 : (Polynomial.C K * Polynomial.X - Polynomial.C msq).natDegree ≤ 1 := by
        refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ (by simp))
        exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
      have d2 : g.natDegree ≤ 1 + (P.P q.1).natDegree + (P.P q.2).natDegree := by
        refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
        refine Polynomial.natDegree_mul_le.trans ?_
        refine add_le_add (Polynomial.natDegree_mul_le.trans (add_le_add d1 le_rfl)) le_rfl
      have e1 := P.natDegree_le _ h1.1
      have e2 := P.natDegree_le _ h2.1
      have : (g.natDegree : ℝ) < n := by
        have : (g.natDegree : ℝ) ≤ 1 + (P.P q.1).natDegree + (P.P q.2).natDegree := by
          exact_mod_cast d2
        have hq1 : q.1 ≤ T := h1.2
        have hq2 : q.2 ≤ T := h2.2
        linarith
      exact_mod_cast this
    have key := sum_poly_eq_integral msq g (0 : Grassmann.Torus 2 n) 0 (fun i => by simp; rfl) hdeg
    simp only [char_zero_right, Complex.one_re, mul_one, Pi.zero_apply, Int.cast_zero, zero_mul,
      add_zero, Real.cos_zero, hg] at key
    exact key
  -- Fubini
  have hmeas2 := measurable_Gq2 P msq
  have hFub : (∫ q, (∫ p in BZ, Gq P msq q (uhatC msq p)) ∂μ) =
      ∫ p in BZ, (∫ q, Gq P msq q (uhatC msq p) ∂μ) := by
    refine integral_integral_swap ?_
    refine Integrable.of_bound hmeas2.aestronglyMeasurable (T * T * ((K * 2 + msq) * K0 * K0)) ?_
    have : ∀ᵐ z ∂(μ.prod (volume.restrict BZ)), z.1 ∈ S ×ˢ S :=
      (Measure.QuasiMeasurePreserving.ae (Measure.quasiMeasurePreserving_fst) hmemS)
    filter_upwards [this] with z hz
    rw [Real.norm_eq_abs]
    exact hGb z.1 hz _ (uhatC_mem hmsq z.2)
  -- assemble
  have lhs : ((n : ℝ) ^ 2)⁻¹ * ∑ m : Grassmann.Torus 2 n, lam m * wt P msq S m ^ 2 =
      K⁻¹ ^ 2 * ∫ q, ((n : ℝ) ^ 2)⁻¹ * ∑ m : Grassmann.Torus 2 n, Gq P msq q (uhat msq m) ∂μ := by
    simp_rw [hA]
    rw [integral_const_mul, integral_finsetSum _ fun m _ => hGint _ (uhat_mem hmsq m),
      ← Finset.mul_sum]
    ring
  have hcongr : (∫ q, ((n : ℝ) ^ 2)⁻¹ * ∑ m : Grassmann.Torus 2 n, Gq P msq q (uhat msq m) ∂μ) =
      ∫ q, ((2 * π) ^ 2)⁻¹ * (∫ p in BZ, Gq P msq q (uhatC msq p)) ∂μ :=
    integral_congr_ae (by filter_upwards [hmemS] with q hq; exact hB q hq)
  rw [lhs, hcongr, integral_const_mul, hFub]
  have hR : ∀ p, lamC p * chat P msq S p ^ 2 = K⁻¹ ^ 2 * ∫ q, Gq P msq q (uhatC msq p) ∂μ := by
    intro p
    have hl : lamC p = K * uhatC msq p - msq := by
      simp only [uhatC, K]; field_simp; ring
    rw [hl, chat]
    exact sq_integral_eq P msq S (uhatC msq p)
  simp_rw [hR]
  rw [integral_const_mul]
  ring

/-- **`𝔩(w_T) = (2π)^{-2} ∫_{[-π,π]²} λ ĉ_{(0,T]}²`** for `w_T = cov P m² (0, T]`, `2T + 1 < n`. -/
theorem lfun_cov_eq_integral_BZ (P : PtFamily) {msq : ℝ} (hmsq : 0 ≤ msq) {T : ℝ} (hT : 0 ≤ T)
    (hn : 2 * T + 1 < n) :
    lfun (FRD.cov P msq (Ioc 0 T) : Matrix (Grassmann.Torus 2 n) (Grassmann.Torus 2 n) ℝ) =
      ((2 * π) ^ 2)⁻¹ * ∫ p in BZ, lamC p * chat P msq (Ioc 0 T) p ^ 2 := by
  rw [FRD.cov, lfun_fmat (wt_even P msq _)]
  exact lsum_eq_integral_BZ P hmsq hT hn

end

end Step2.D2
