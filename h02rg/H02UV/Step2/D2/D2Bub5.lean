import Step2.D2.D2Bub4

/-!
# The bubble functional in momentum space (`prop:d2`, (R4), assembled)

* `bubF_eq_bubFZ`, `sum_bubF_eq`: on the torus `Λ = (ℤ/L^N)²`, for a covariance
  `C(a, b) = c(r(a - b))` given by an even kernel `c : ℤ² → ℂ` of range `R`, `2(R + 4) < L^N`,
  the torus density `bubF` equals the `ℤ²` density `bubFZ`, and `∑_z bubF = ∑_w bubFZ`;
* `negBub_momentum`: **the momentum form of the bubble coefficient**: for every block `X` in the
  patch condition,
  `-𝔅_X(C) = (2π)^{-2} ∫_{[-π,π]²} [(4 sin² p₀ - 2λ) Â₀(p)² + (λ²/2) Â₁(p)²] d²p`,
  with `Â_j(p) = ∑_v v₀^j c(v) e^{i v·p}` (so `Â₁ = -i ∂_{p₀} Â₀`) and the trigonometric
  polynomials written as `trigK kap0`, `trigK kap2`.
-/

namespace Step2

open Finset MeasureTheory Step2.D2 Loc FRD Grassmann

noncomputable section

/-- `|u|_∞` on `ℤ²`. -/
def nm (u : ℤ × ℤ) : ℕ := max u.1.natAbs u.2.natAbs

theorem nm_add_le (u v : ℤ × ℤ) : nm (u + v) ≤ nm u + nm v := by
  unfold nm; simp only [Prod.fst_add, Prod.snd_add]
  have h1 := Int.natAbs_add_le u.1 v.1
  have h2 := Int.natAbs_add_le u.2 v.2
  omega

theorem nm_neg (u : ℤ × ℤ) : nm (-u) = nm u := by
  unfold nm; simp

theorem nm_dZ (i t : Fin 2) : nm (dZ i t) ≤ 1 := by
  fin_cases i <;> fin_cases t <;> simp [nm, dZ]

/-- `ℤ² → Zd 2`. -/
def zd (u : ℤ × ℤ) : Zd 2 := ![u.1, u.2]

theorem supNormZ_zd (u : ℤ × ℤ) : supNormZ (zd u) = nm u := by
  unfold supNormZ nm zd
  apply le_antisymm
  · refine Finset.sup_le fun i _ => ?_
    fin_cases i <;> simp
  · apply max_le
    · exact Finset.le_sup (f := fun i => (![u.1, u.2] i).natAbs) (Finset.mem_univ 0)
    · exact Finset.le_sup (f := fun i => (![u.1, u.2] i).natAbs) (Finset.mem_univ 1)

theorem zd_rep {n : ℕ} [NeZero n] (z : Grassmann.Torus 2 n) : zd (rep z 0, rep z 1) = rep z := by
  funext i; fin_cases i <;> rfl

theorem nm_rep {n : ℕ} [NeZero n] (z : Grassmann.Torus 2 n) :
    nm (rep z 0, rep z 1) = supNorm z := by
  rw [← supNormZ_zd, zd_rep, Loc.supNormZ_rep_eq]

theorem zd_add (u v : ℤ × ℤ) : zd (u + v) = zd u + zd v := by
  funext i; fin_cases i <;> rfl

theorem zd_neg (u : ℤ × ℤ) : zd (-u) = -zd u := by
  funext i; fin_cases i <;> rfl

theorem zd_sub (u v : ℤ × ℤ) : zd (u - v) = zd u - zd v := by
  rw [sub_eq_add_neg, zd_add, zd_neg, ← sub_eq_add_neg]

theorem dirZ_pmdir (i t : Fin 2) : zd (dZ i t) = dirZ (pmdir i t) := by
  funext k; fin_cases i <;> fin_cases t <;> fin_cases k <;> simp [zd, dZ, pmdir, dirZ]

variable {L N : ℕ} [NeZero L]

theorem rep_prj_zd (u : ℤ × ℤ) (h : 2 * nm u < L ^ N) :
    (rep (prj (zd u) : Lam 2 L N) 0, rep (prj (zd u) : Lam 2 L N) 1) = u := by
  have := (eq_rep (z := zd u) (x := (prj (zd u) : Lam 2 L N)) rfl (by rw [supNormZ_zd]; exact h))
  rw [← this]; rfl

/-- The torus kernel of `c`. -/
def cTor (c : ℤ × ℤ → ℂ) (z : Lam 2 L N) : ℂ := c (rep z 0, rep z 1)

variable (c : ℤ × ℤ → ℂ) {R : ℕ}

theorem cTor_prj (hn : 2 * (R + 4) < L ^ N) (u : ℤ × ℤ) (hu : nm u ≤ R + 4) :
    cTor c (prj (zd u) : Lam 2 L N) = c u := by
  rw [cTor, rep_prj_zd u (by omega)]

set_option maxHeartbeats 8000000 in
theorem bubFZ_eq_zero (hcR : ∀ u, R < nm u → c u = 0) {w : ℤ × ℤ} (hw : R + 2 < nm w) :
    bubFZ c w = 0 := by
  unfold bubFZ
  refine sum_eq_zero fun i' _ => sum_eq_zero fun t' _ => sum_eq_zero fun i _ =>
    sum_eq_zero fun t _ => ?_
  have key : ∀ u : ℤ × ℤ, nm w ≤ nm u + 2 → c u = 0 := fun u hu => hcR u (by omega)
  obtain ⟨w1, w2⟩ := w
  fin_cases i <;> fin_cases t <;> fin_cases i' <;> fin_cases t' <;>
    (apply bubPoly_eq_zero <;> apply key <;> simp [dZ, nm] <;> omega)

theorem cTor_entry (hn : 2 * (R + 4) < L ^ N) (a b : ℤ × ℤ) (hab : nm (a - b) ≤ R + 4) :
    cTor c ((prj (zd a) : Lam 2 L N) - prj (zd b)) = c (a.1 - b.1, a.2 - b.2) := by
  rw [← prj_sub, ← zd_sub, cTor_prj c hn _ hab]; rfl

theorem dirVec_pmdir (i t : Fin 2) : (dirVec (pmdir i t) : Lam 2 L N) = prj (zd (dZ i t)) := by
  rw [dirZ_pmdir, prj_dirZ]

theorem cTor_zero_of (hcR : ∀ u, R < nm u → c u = 0) (v : Lam 2 L N) (hv : R < supNorm v) :
    cTor c v = 0 := hcR _ (by rw [nm_rep]; exact hv)

theorem nm_sub_le (a b : ℤ × ℤ) : nm (a - b) ≤ nm a + nm b := by
  rw [sub_eq_add_neg]; exact (nm_add_le a (-b)).trans (by rw [nm_neg])

/-- **The torus density is the `ℤ²` density.** -/
theorem bubF_eq_bubFZ (hcR : ∀ u, R < nm u → c u = 0) (hn : 2 * (R + 4) < L ^ N)
    (z : Lam 2 L N) : bubF (cTor c) 0 z = bubFZ c (rep z 0, rep z 1) := by
  set w : ℤ × ℤ := (rep z 0, rep z 1) with hw
  have hzw : z = prj (zd w) := by rw [hw, zd_rep, prj_rep]
  have hnw : nm w = supNorm z := nm_rep z
  by_cases hz : supNorm z ≤ R + 2
  · unfold bubF bubFZ
    refine sum_congr rfl fun i' _ => sum_congr rfl fun t' _ => sum_congr rfl fun i _ =>
      sum_congr rfl fun t _ => ?_
    have hl1 : (dirZ (pmdir i t) 0 : ℂ) = ((dZ i t).1 : ℂ) := by
      rw [← dirZ_pmdir]; rfl
    have hl2 : (dirZ (pmdir i' t') 0 : ℂ) = ((dZ i' t').1 : ℂ) := by
      rw [← dirZ_pmdir]; rfl
    rw [hl1, hl2]
    have he := nm_dZ i t
    have hf := nm_dZ i' t'
    have h0 : (0 : Lam 2 L N) = prj (zd 0) := by
      rw [show zd (0 : ℤ × ℤ) = 0 by funext k; fin_cases k <;> rfl]
      exact (Loc.prj_zero (d := 2) (L := L) (N := N)).symm
    have hzf : z + dirVec (pmdir i' t') = prj (zd (w + dZ i' t')) := by
      rw [zd_add, prj_add, ← hzw, dirVec_pmdir]
    have hwf : nm (w + dZ i' t') ≤ R + 3 := (nm_add_le _ _).trans (by omega)
    have E : ∀ (A B : Lam 2 L N) (A' B' : ℤ × ℤ), A = prj (zd A') → B = prj (zd B') →
        nm A' + nm B' ≤ R + 4 → cTor c (A - B) = c (A'.1 - B'.1, A'.2 - B'.2) := by
      intro A B A' B' hA hB hAB
      rw [hA, hB]; exact cTor_entry c hn A' B' ((nm_sub_le _ _).trans hAB)
    have hz0 : nm (0 : ℤ × ℤ) = 0 := by simp [nm]
    have he' := dirVec_pmdir (L := L) (N := N) i t
    apply bubPoly_congr
    · exact E _ _ _ _ h0 hzw (by omega)
    · exact E _ _ _ _ h0 hzf (by omega)
    · exact E _ _ _ _ he' hzw (by omega)
    · exact E _ _ _ _ he' hzf (by omega)
    · exact E _ _ _ _ hzw h0 (by omega)
    · exact E _ _ _ _ hzw he' (by omega)
    · exact E _ _ _ _ hzf h0 (by omega)
    · exact E _ _ _ _ hzf he' (by omega)
  · push_neg at hz
    rw [bubFZ_eq_zero c hcR (by omega)]
    unfold bubF
    refine sum_eq_zero fun i' _ => sum_eq_zero fun t' _ => sum_eq_zero fun i _ =>
      sum_eq_zero fun t _ => ?_
    set e := pmdir i t
    set f := pmdir i' t'
    have hzf := supNorm_add_dir_ge (L := L) (N := N) z f
    have e1 : ∀ a : Lam 2 L N, supNorm z ≤ supNorm a + 2 → cTor c a = 0 :=
      fun a ha => cTor_zero_of c hcR a (by omega)
    have n3 : supNorm z ≤ supNorm (dirVec e - z) + 2 := by
      have := supNorm_le_of_sub z (z - dirVec e); rw [sub_sub_cancel] at this
      have := supNorm_dirVec_le (n := L ^ N) e
      have h' : supNorm (dirVec e - z) = supNorm (z - dirVec e) := by rw [← supNorm_neg, neg_sub]
      omega
    have n4 : supNorm z ≤ supNorm (dirVec e - (z + dirVec f)) + 2 := by
      have := supNorm_le_of_sub (z + dirVec f) (z + dirVec f - dirVec e)
      rw [sub_sub_cancel] at this
      have := supNorm_dirVec_le (n := L ^ N) e
      have h' : supNorm (dirVec e - (z + dirVec f)) = supNorm (z + dirVec f - dirVec e) := by
        rw [← supNorm_neg, neg_sub]
      omega
    have n6 : supNorm z ≤ supNorm (z - dirVec e) + 2 := by
      have := supNorm_le_of_sub z (z - dirVec e); rw [sub_sub_cancel] at this
      have := supNorm_dirVec_le (n := L ^ N) e
      omega
    have n8 : supNorm z ≤ supNorm (z + dirVec f - dirVec e) + 2 := by
      have := supNorm_le_of_sub (z + dirVec f) (z + dirVec f - dirVec e)
      rw [sub_sub_cancel] at this
      have := supNorm_dirVec_le (n := L ^ N) e
      omega
    apply bubPoly_eq_zero
    · exact e1 _ (by rw [zero_sub, supNorm_neg]; omega)
    · exact e1 _ (by rw [zero_sub, supNorm_neg]; omega)
    · exact e1 _ n3
    · exact e1 _ n4
    · exact e1 _ (by rw [sub_zero]; omega)
    · exact e1 _ n6
    · exact e1 _ (by rw [sub_zero]; omega)
    · exact e1 _ n8

/-- `∑_z bubF = ∑_w bubFZ`. -/
theorem sum_bubF_eq (hcR : ∀ u, R < nm u → c u = 0) (hn : 2 * (R + 4) < L ^ N) :
    ∑ z : Lam 2 L N, bubF (cTor c) 0 z = ∑ᶠ w : ℤ × ℤ, bubFZ c w := by
  set ρ : Lam 2 L N → ℤ × ℤ := fun z => (rep z 0, rep z 1)
  have hinj : Function.Injective ρ := by
    intro z z' h
    have : zd (ρ z) = zd (ρ z') := by rw [h]
    simp only [ρ, zd_rep] at this
    rw [← prj_rep z, ← prj_rep z', this]
  simp_rw [bubF_eq_bubFZ c hcR hn]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.univ.image ρ)]
  · rw [Finset.sum_image (fun z _ z' _ h => hinj h)]
  · intro w hw
    simp only [Function.mem_support, ne_eq] at hw
    have hw' : nm w ≤ R + 2 := by
      by_contra h; push_neg at h; exact hw (bubFZ_eq_zero c hcR h)
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
    exact ⟨prj (zd w), rep_prj_zd w (by omega)⟩

theorem hfs_of_range (hcR : ∀ u, R < nm u → c u = 0) : Function.HasFiniteSupport c := by
  refine Set.Finite.subset ((Finset.Icc (-(R : ℤ)) R ×ˢ Finset.Icc (-(R : ℤ)) R).finite_toSet)
    (fun u hu => ?_)
  simp only [Function.mem_support, ne_eq] at hu
  have h : nm u ≤ R := by by_contra h; push_neg at h; exact hu (hcR u h)
  simp only [nm] at h
  simp only [Finset.coe_product, Set.mem_prod, Finset.coe_Icc, Set.mem_Icc]
  omega

/-- **The momentum form of the bubble coefficient (R4).** Let `C(a, b) = c(r(a - b))` on the
torus `(ℤ/L^N)²` with `c : ℤ² → ℂ` even and of range `R` (`c(u) = 0` for `|u|_∞ > R`), and let
the block `X ≠ ∅` satisfy `2(|x - b_X|_∞ + R + 3) < L^N`, `2(R + 4) < L^N`. Then
`-𝔅_X(C) = (2π)^{-2} ∫_{[-π,π]²} [(4 sin² p₀ - 2λ(p)) Â₀(p)² + (λ(p)²/2) Â₁(p)²] d²p`,
`Â_j(p) = ∑_v v₀^j c(v) e^{i v·p}` (`symb`), direction `κ = 0`. -/
theorem negBub_momentum (hcR : ∀ u, R < nm u → c u = 0)
    (heven : ∀ v : ℤ × ℤ, c (-v.1, -v.2) = c v) (hn : 2 * (R + 4) < L ^ N)
    {C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ} (hC : ∀ a b, C a b = cTor c (a - b))
    {X : Finset (Lam 2 L N)} (hne : X.Nonempty)
    (hX : ∀ x ∈ X, 2 * (supNorm (x - base X) + R + 3) < L ^ N) :
    negBub C X 0 = ((2 * (Real.pi : ℂ)) ^ 2)⁻¹ *
      ((∫ p in BZ, trigK kap0 p * (symb c 0 p * symb c 0 p)) +
        ∫ p in BZ, trigK kap2 p * (symb c 1 p * symb c 1 p)) := by
  rw [negBub_transl hC (fun z hz => cTor_zero_of c hcR z hz) hne hX 0, sum_bubF_eq c hcR hn,
    finsum_bubFZ_sym c (hfs_of_range c hcR) heven]
  ring

/-! ### The trigonometric polynomials -/

theorem ex_eq (a b : ℤ) (p : ℂ) :
    ex (a, b) p = Complex.exp (a * (p.re * Complex.I)) * Complex.exp (b * (p.im * Complex.I)) := by
  rw [ex, ← Complex.exp_add]; congr 1; push_cast; ring

/-- `trigK kap0 = 4 sin² p₀ - 2λ(p)`. -/
theorem trigK_kap0 (p : ℂ) :
    trigK kap0 p = ((4 * Real.sin p.re ^ 2 - 2 * lamC p : ℝ) : ℂ) := by
  have hs : Real.sin p.re ^ 2 = (1 - Real.cos (2 * p.re)) / 2 := by
    rw [Real.cos_two_mul, Real.sin_sq]; ring
  rw [hs]
  simp only [trigK, kap0, List.map, List.sum_cons, List.sum_nil, lamC]
  push_cast
  simp only [ex_eq, Complex.cos]
  set X := Complex.exp ((p.re : ℂ) * Complex.I)
  set Y := Complex.exp ((p.im : ℂ) * Complex.I)
  have hX : X ≠ 0 := Complex.exp_ne_zero _
  have hY : Y ≠ 0 := Complex.exp_ne_zero _
  have e1 : ∀ k : ℤ, Complex.exp (k * ((p.re : ℂ) * Complex.I)) = X ^ k := by
    intro k; rw [← Complex.exp_int_mul]
  have e2 : ∀ k : ℤ, Complex.exp (k * ((p.im : ℂ) * Complex.I)) = Y ^ k := by
    intro k; rw [← Complex.exp_int_mul]
  have e3 : Complex.exp (-((p.re : ℂ) * Complex.I)) = X⁻¹ := by rw [Complex.exp_neg]
  have e3' : Complex.exp (-(p.re : ℂ) * Complex.I) = X⁻¹ := by rw [neg_mul, Complex.exp_neg]
  have e4 : Complex.exp (-((p.im : ℂ) * Complex.I)) = Y⁻¹ := by rw [Complex.exp_neg]
  have e4' : Complex.exp (-(p.im : ℂ) * Complex.I) = Y⁻¹ := by rw [neg_mul, Complex.exp_neg]
  have e5 : Complex.exp (2 * (p.re : ℂ) * Complex.I) = X ^ 2 := by
    rw [show 2 * (p.re : ℂ) * Complex.I = ((p.re : ℂ) * Complex.I) + ((p.re : ℂ) * Complex.I) by
      ring, Complex.exp_add]; ring
  have e6 : Complex.exp (-(2 * (p.re : ℂ)) * Complex.I) = (X ^ 2)⁻¹ := by
    rw [neg_mul, Complex.exp_neg, e5]
  simp only [e1, e2, e3, e3', e4, e4', e5, e6]
  field_simp
  ring

/-- `trigK kap2 = λ(p)²/2`. -/
theorem trigK_kap2 (p : ℂ) : trigK kap2 p = ((lamC p ^ 2 / 2 : ℝ) : ℂ) := by
  simp only [trigK, kap2, List.map, List.sum_cons, List.sum_nil, lamC]
  push_cast
  simp only [ex_eq, Complex.cos]
  set X := Complex.exp ((p.re : ℂ) * Complex.I)
  set Y := Complex.exp ((p.im : ℂ) * Complex.I)
  have hX : X ≠ 0 := Complex.exp_ne_zero _
  have hY : Y ≠ 0 := Complex.exp_ne_zero _
  have e1 : ∀ k : ℤ, Complex.exp (k * ((p.re : ℂ) * Complex.I)) = X ^ k := by
    intro k; rw [← Complex.exp_int_mul]
  have e2 : ∀ k : ℤ, Complex.exp (k * ((p.im : ℂ) * Complex.I)) = Y ^ k := by
    intro k; rw [← Complex.exp_int_mul]
  have e3' : Complex.exp (-(p.re : ℂ) * Complex.I) = X⁻¹ := by rw [neg_mul, Complex.exp_neg]
  have e4' : Complex.exp (-(p.im : ℂ) * Complex.I) = Y⁻¹ := by rw [neg_mul, Complex.exp_neg]
  simp only [e1, e2, e3', e4']
  field_simp
  ring

/-- **The momentum form of the bubble coefficient, trigonometric version.**
`-𝔅_X(C) = (2π)^{-2} ∫_{[-π,π]²} [(4 sin² p₀ - 2λ) Â₀² + (λ²/2) Â₁²] d²p`. -/
theorem negBub_momentum' (hcR : ∀ u, R < nm u → c u = 0)
    (heven : ∀ v : ℤ × ℤ, c (-v.1, -v.2) = c v) (hn : 2 * (R + 4) < L ^ N)
    {C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ} (hC : ∀ a b, C a b = cTor c (a - b))
    {X : Finset (Lam 2 L N)} (hne : X.Nonempty)
    (hX : ∀ x ∈ X, 2 * (supNorm (x - base X) + R + 3) < L ^ N) :
    negBub C X 0 = ((2 * (Real.pi : ℂ)) ^ 2)⁻¹ *
      ((∫ p in BZ, ((4 * Real.sin p.re ^ 2 - 2 * lamC p : ℝ) : ℂ) * (symb c 0 p * symb c 0 p)) +
        ∫ p in BZ, ((lamC p ^ 2 / 2 : ℝ) : ℂ) * (symb c 1 p * symb c 1 p)) := by
  rw [negBub_momentum c hcR heven hn hC hne hX]
  simp_rw [trigK_kap0, trigK_kap2]

end

end Step2
