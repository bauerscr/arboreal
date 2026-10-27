import Spin2.Gam.GamBulk
import Spin2.Case2.Case2Rel
import Spin2.Case2.Case2RelPairThm
import PtCorr2.Obs.ObsHistTop
import PtCorr2.Obs.ProdBd2Top

/-!
# The bulk inputs of the step `N_h` (`ValidAtL`)

The covariance `C_{N_h}` has the properties of the lower scales (`histCovO_props_i` with `ValidAtL`):
`GoodCov2` at its Gram scale, translation invariance, symmetry. Hence the lattice constants
(`histCov_constsU`), `Bulk2` up to the horizon `N_h + 1` (`bulk2_histU`) and the `C2Ctx` bounds at
`k = N_h` (suffix `U`, `k ≤ N_h`): `dl_leU`, `rowS_leU`, `lfunX_leU`, `c0_le_gbU`, `nu_le_gbU`,
`yz_le_gbU`, **`gamBulk_le_posU`** (`‖E_{N_h}(a)‖ ≤ K_bǧ_{N_h}/|Z_{N_h+1}|`), **`tadInc2_leU`**
(`|tadInc2 k j| ≤ c(2/L)^{j−k}ǧ_k`, `k < j ≤ N_h`), `gamRem2_split_histU` (`ρ_{N_h} = gamWK2 + βE`).

**The size of `𝔫^{(2)}_{N_h}`** (`frakN2_top_le`): `𝔫_j = ν'_j rowS_{C_j} − g'_j𝔩_{C_j} +
∑_{k<j}tadInc2 k j` (`Bulk2.frakN2_eq`), hence `|𝔫_{N_h}| ≤ (4L² + 3)cǧ_{N_h}`. This is a crude
bound (the sharp `Case2Loop` bound uses the couplings at `N_h + 1`, which are not controlled); its
smallness is the new requirement `(4L² + 3)cε ≤ 1/8` on `ε`.
-/

set_option linter.unusedSectionVars false

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

section Bulk

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : Obs2.ObsPts 2 L N)
  (o₀ : Obs2.ObsSt .two L N) (t : Hist.Seq (Xs R))

/-- The lattice constants of `C_k`, `k ≤ N_h`. -/
theorem histCov_constsU {Nh : ℕ} (hV : ∀ i < Nh, ValidAt R i) (hVL : ValidAtL R Nh) {k : ℕ}
    (hk : k ≤ Nh) :
    (∀ x, Obs2.histCovO R t k x x = Obs2.c0H R t k) ∧
      (∀ x e, Obs2.histCovO R t k (x + dirVec e) x = Obs2.c0H R t k + Obs2.dlH R t k) ∧
      (∀ x e, Obs2.histCovO R t k x (x + dirVec e) = Obs2.c0H R t k + Obs2.dlH R t k) := by
  obtain ⟨-, -, hCs, hCsym⟩ := histCovO_props_i R hV hVL t hk
  obtain ⟨c₀, δ, hc, hδ, hδ'⟩ := covProps (by norm_num) hCs hCsym
  have e0 : Obs2.histCovO R t k 0 0 = c₀ := hc 0
  have e1 : Obs2.histCovO R t k (dirVec (Sum.inl (0 : Fin 2))) 0 = c₀ + δ := by
    have := hδ 0 (Sum.inl 0)
    rw [zero_add] at this
    exact this
  have hc0 : Obs2.c0H R t k = c₀ := e0
  have hd0 : Obs2.dlH R t k = δ := by
    unfold Obs2.dlH; rw [e1, e0]; ring
  rw [hc0, hd0]
  exact ⟨hc, hδ, hδ'⟩

/-- **`Bulk2` up to the horizon `N_h + 1`.** -/
theorem bulk2_histU {Nh : ℕ} (hV : ∀ i < Nh, ValidAt R i) (hVL : ValidAtL R Nh)
    (h₀ : o₀.IsObs) :
    Obs2.Bulk2 (Obs2.histCovO R t) (Obs2.histVO2 R P o₀ t) (Obs2.kapH R t) (Obs2.c0H R t)
      (Obs2.dlH R t) (Nh + 1) where
  he := fun k hk => by
    obtain ⟨hc, hδ, hδ'⟩ := histCov_constsU R t hV hVL (k := k) (by omega)
    exact Obs2.histVprLO2_e R P o₀ t (Obs2.obsHist_isObs R P o₀ h₀ k t) hc hδ hδ'
  hc := fun k hk => (histCov_constsU R t hV hVL (k := k) (by omega)).1
  hδ := fun k hk => (histCov_constsU R t hV hVL (k := k) (by omega)).2.1
  hδ' := fun k hk => (histCov_constsU R t hV hVL (k := k) (by omega)).2.2

/-- `ρ_k = gamWK2_k + β_kE_k` for `k ≤ N_h`. -/
theorem gamRem2_split_histU {Nh : ℕ} (hV : ∀ i < Nh, ValidAt R i) (hVL : ValidAtL R Nh)
    (h₀ : o₀.IsObs) (h0 : ∀ b, Obs2.Loc2Form P.a (o₀.V b : Obs.SA .two (Lam 2 L N)).a) {k : ℕ}
    (hk : k ≤ Nh) :
    Obs2.gamRem2 R P o₀ t k = Obs2.gamWK2 R P o₀ t k +
      Obs2.betaTot2 k (Obs2.histVO2 R P o₀ t k) *
        ε (FC (Obs2.histCovO R t k) (Obs.LocObs.pbp P.a) (Vcoup (Obs2.kapH R t k) univ)) := by
  rw [Obs2.gamRem2_split R P o₀ t h0]
  obtain ⟨r, hr⟩ := (bulk2_histU R P o₀ t hV hVL h₀).he k (by omega)
  have e : (Obs2.VprLO k (Obs2.histCovO R t k) (Obs2.histVO2 R P o₀ t k) :
      Obs.SA .two (Lam 2 L N)).e = Obs2.bulkE2 (Obs2.histCovO R t) (Obs2.histVO2 R P o₀ t) k := rfl
  rw [e, hr, FC_add_right, FC_smul_right, Obs2.FC_one_right, smul_zero, add_zero]

end Bulk

namespace C2Ctx

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {Nh : ℕ} {t : Hist.Seq (Xs R)}
  {cmu' cz' cd c : ℝ} (X : C2Ctx R Nh t cmu' cz' cd c)
include X

theorem covU {i : ℕ} (hi : i ≤ Nh) :
    GoodCov2 i (fscale (stZ' R (rawHist R i t)) * R.ℓ / 4) (Obs2.histCovO R t i) ∧
      TInv (Obs2.histCovO R t i) ∧ CSym (Obs2.histCovO R t i) ∧
      ∀ x y, Obs2.histCovO R t i x y = Obs2.histCovO R t i y x :=
  histCovO_props_i R X.hV X.hVL t hi

theorem iNU {i : ℕ} (hi : i ≤ Nh) : i + 1 < N := by have := X.hN; omega

theorem dl_leU {k : ℕ} (hk : k ≤ Nh) :
    ‖Obs2.dlH R t k‖ ≤ R.ℓ ^ 2 / (16 * zH R t (k + 1)) / (2 * ((L : ℝ) ^ (k + 1)) ^ 2) := by
  obtain ⟨hC, -⟩ := X.covU hk
  obtain ⟨hc, hδ, hδ'⟩ := histCov_constsU R t X.hV X.hVL hk
  have h := (cov_c0_delta_le hC hc hδ hδ').2
  rwa [ellI_sq] at h

theorem c0_le_gbU {k : ℕ} (hk : k ≤ Nh) :
    ‖Obs2.c0H R t k‖ ≤ R.ℓ ^ 2 / (16 * zH R t (k + 1)) := by
  obtain ⟨hC, -⟩ := X.covU hk
  obtain ⟨hc, hδ, hδ'⟩ := histCov_constsU R t X.hV X.hVL hk
  have h := (cov_c0_delta_le hC hc hδ hδ').1
  rwa [ellI_sq] at h

theorem rowS_leU {i : ℕ} (hi : i ≤ Nh) (a : Lam 2 L N) :
    ‖Obs2.rowS (Obs2.histCovO R t i) a‖ ≤
      18 * ((L : ℝ) ^ (i + 1)) ^ 2 * (R.ℓ ^ 2 / (16 * zH R t (i + 1))) := by
  have h := Obs2.norm_rowS_le (X.covU hi).1 (X.iNU hi) a
  rwa [ellI_sq] at h

theorem lfunX_leU {i k : ℕ} (hi : i ≤ Nh) (hk : k ≤ Nh) (a : Lam 2 L N) :
    ‖Obs2.lfunX (Obs2.histCovO R t i) (Obs2.histCovO R t k) a‖ ≤
      36 * (R.ℓ ^ 2 / (16 * zH R t (i + 1))) * (R.ℓ ^ 2 / (16 * zH R t (k + 1))) *
        ((L : ℝ) ^ (i + 1) / (L : ℝ) ^ (k + 1)) := by
  have h := Obs2.norm_lfunX_le (X.covU hi).1 (X.iNU hi) (X.covU hk).1 a
  rwa [ellI_sq, ellI_sq] at h

theorem lfunC_leU {i : ℕ} (hi : i ≤ Nh) (a : Lam 2 L N) :
    ‖Obs2.lfunC (Obs2.histCovO R t i) a‖ ≤ 18 * (R.ℓ ^ 2 / (16 * zH R t (i + 1))) ^ 2 := by
  have h := Obs2.norm_lfunC_le (X.covU hi).1 (X.iNU hi) a
  rwa [show (fscale (stZ' R (rawHist R i t)) * R.ℓ / 4) ^ 4 =
    ((fscale (stZ' R (rawHist R i t)) * R.ℓ / 4) ^ 2) ^ 2 by ring, ellI_sq] at h

/-- The bound on `ν'_k`, `k ≤ N_h`. -/
theorem nu_le_gbU {k : ℕ} (hk : k ≤ Nh) :
    ‖(Obs2.kapH R t k).nu‖ ≤
      zH R t (k + 1) * (L : ℝ) ^ 2 / ((L : ℝ) ^ (k + 1)) ^ 2 * ((cmu' + 16 / 7 * cz') * (t k).1) +
        16 / 7 * (t k).1 * zH R t (k + 1) ^ 2 * (R.ℓ ^ 2 / (16 * zH R t (k + 1))) /
          ((L : ℝ) ^ (k + 1)) ^ 2 := by
  have hL0 := X.L_pos
  set g := (t k).1
  have hg0 : 0 ≤ g := (X.hg k hk).1.le
  set zp := zH R t (k + 1)
  have hzp := X.zpos (k + 1)
  set s := R.ℓ ^ 2 / (16 * zp) with hs
  set h2 := ((L : ℝ) ^ (k + 1)) ^ 2 with hh2
  have hh2p : 0 < h2 := by positivity
  have hs0 : 0 ≤ s := by positivity
  have hnuF := X.nuFH_le_gb hk
  have hgH := X.gH_le_gb hk
  have hdl := X.dl_leU hk
  rw [Obs2.kapH_nu]
  refine (norm_add_le _ _).trans ?_
  have e1 : zp / ((L : ℝ) ^ k) ^ 2 = zp * (L : ℝ) ^ 2 / h2 := by
    rw [hh2]; field_simp; ring
  rw [e1] at hnuF
  have h4 : ‖4 * Obs2.gH R t k * Obs2.dlH R t k‖ ≤ 4 * (8 / 7 * g * zp ^ 2) * (s / (2 * h2)) := by
    rw [norm_mul, norm_mul, show ‖(4 : ℂ)‖ = 4 by norm_num]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hgH (by norm_num)) hdl (norm_nonneg _)
      (by positivity)
  have e2 : 4 * (8 / 7 * g * zp ^ 2) * (s / (2 * h2)) = 16 / 7 * g * zp ^ 2 * s / h2 := by
    field_simp; ring
  linarith

/-- The bound on `y'_k + z'_k`, `k ≤ N_h`. -/
theorem yz_le_gbU {k : ℕ} (hk : k ≤ Nh)
    (hzy : ‖(rawHist R k t).z + (rawHist R k t).y‖ ≤ 2 * cz' * (t k).1 * zH R t k) :
    ‖(rawHist R k t).z + (rawHist R k t).y - stA R (rawHist R k t) -
      Obs2.gH R t k * (Obs2.c0H R t k + Obs2.dlH R t k)‖ ≤
      32 / 7 * cz' * (t k).1 * zH R t (k + 1) +
        16 / 7 * (t k).1 * zH R t (k + 1) ^ 2 * (R.ℓ ^ 2 / (16 * zH R t (k + 1))) := by
  have hL0 := X.L_pos
  set g := (t k).1
  have hg0 : 0 ≤ g := (X.hg k hk).1.le
  set zp := zH R t (k + 1)
  have hzp := X.zpos (k + 1)
  set s := R.ℓ ^ 2 / (16 * zp) with hs
  set h2 := ((L : ℝ) ^ (k + 1)) ^ 2 with hh2
  have hh2p : 0 < h2 := by positivity
  have hh21 : 1 ≤ h2 := one_le_pow₀ (one_le_pow₀ (by linarith [X.L7]))
  have hs0 : 0 ≤ s := by positivity
  have hgH := X.gH_le_gb hk
  have hdl := X.dl_leU hk
  have hc0 := X.c0_le_gbU hk
  have hA := X.zA_le_gb hk
  have hZr : zH R t k ≤ 8 / 7 * zp := by
    have := zH_ratio_down R X.hρ0 X.hρ8 t (show k ≤ k + 1 by omega)
    rwa [show k + 1 - k = 1 by omega, pow_one] at this
  have hgH0 : 0 ≤ 8 / 7 * g * zp ^ 2 := by positivity
  refine (norm_sub_le _ _).trans ?_
  have h1 := (norm_sub_le ((rawHist R k t).z + (rawHist R k t).y) (stA R (rawHist R k t)))
  have h3 : ‖Obs2.gH R t k * (Obs2.c0H R t k + Obs2.dlH R t k)‖ ≤
      8 / 7 * g * zp ^ 2 * (s + s / (2 * h2)) := by
    rw [norm_mul]
    exact mul_le_mul hgH ((norm_add_le _ _).trans (add_le_add hc0 hdl)) (norm_nonneg _) hgH0
  have h5 : s / (2 * h2) ≤ s := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have h6 : 8 / 7 * g * zp ^ 2 * (s + s / (2 * h2)) ≤ 8 / 7 * g * zp ^ 2 * (2 * s) :=
    mul_le_mul_of_nonneg_left (by linarith) hgH0
  have h7 : 2 * cz' * g * zH R t k ≤ 2 * cz' * g * (8 / 7 * zp) :=
    mul_le_mul_of_nonneg_left hZr (by have := X.hcz; positivity)
  have e : 32 / 7 * cz' * g * zp + 16 / 7 * g * zp ^ 2 * s =
      2 * cz' * g * (8 / 7 * zp) + 8 / 7 * zp * (2 * cz' * g) + 8 / 7 * g * zp ^ 2 * (2 * s) := by
    ring
  linarith

/-- **`‖E_k(a)‖ ≤ K_bǧ_k/|Z_{k+1}|` for `1 ≤ k ≤ N_h`** (`gamBulk_le_pos` including `k = N_h`). -/
theorem gamBulk_le_posU {k : ℕ} (hk : k ≤ Nh)
    (hzy : ‖(rawHist R k t).z + (rawHist R k t).y‖ ≤ 2 * cz' * (t k).1 * zH R t k)
    (a : Lam 2 L N) :
    ‖ε (FC (Obs2.histCovO R t k) (Obs.LocObs.pbp a) (Vcoup (Obs2.kapH R t k) univ))‖ ≤
      gbKb L R.ℓ cmu' cz' * (t k).1 / zH R t (k + 1) := by
  have hL0 := X.L_pos
  have hg0 : 0 ≤ (t k).1 := (X.hg k hk).1.le
  have hzp := X.zpos (k + 1)
  rw [eps_hist_eq]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  obtain ⟨hC, -⟩ := X.covU hk
  have hT := Obs2.norm_sumCC_le hC (X.iNU hk) a
  have hlf := Obs2.norm_lfunC_le hC (X.iNU hk) a
  rw [ellI_sq] at hT
  rw [show (fscale (stZ' R (rawHist R k t)) * R.ℓ / 4) ^ 4 =
    (fscale (stZ' R (rawHist R k t)) * R.ℓ / 4) ^ 2 * (fscale (stZ' R (rawHist R k t)) * R.ℓ / 4) ^ 2
    by ring, ellI_sq] at hlf
  have hb := gb_alg_pos (nu := ‖(Obs2.kapH R t k).nu‖)
    (T := ‖∑ x, Obs2.histCovO R t k a x * Obs2.histCovO R t k x a‖)
    (lf := ‖Obs2.lfunC (Obs2.histCovO R t k) a‖) (ℓ := R.ℓ) hzp hg0 (by positivity)
    (by positivity) X.hcmu X.hcz rfl (X.nu_le_gbU hk) hT (X.yz_le_gbU hk hzy) hlf (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
  exact hb.trans_eq (by unfold gbKb; ring)

/-- **The Case-(2) tadpole increments up to `N_h`**: `|tadInc2 k j| ≤ c(2/L)^{j−k}ǧ_k`,
`k < j ≤ N_h`. -/
theorem tadInc2_leU (P : Obs2.ObsPts 2 L N) (o₀ : Obs2.ObsSt .two L N) (h₀ : o₀.IsObs)
    {k j : ℕ} (hkj : k < j) (hj : j ≤ Nh) :
    ‖Obs2.tadInc2 P (Obs2.histCovO R t) (Obs2.histVO2 R P o₀ t) k j‖ ≤
      c * (2 / (L : ℝ)) ^ (j - k) * (t k).1 := by
  have hL0 := X.L_pos
  have hL7 := X.L7
  have hℓ : 0 < R.ℓ := Fact.out
  have HB := bulk2_histU R P o₀ t X.hV X.hVL h₀
  rw [HB.tadInc2_eq P hkj (by omega), Obs2.kapH_g]
  have hg0 : 0 ≤ (t k).1 := (X.hg k (by omega)).1.le
  have hgk : ‖Obs2.gH R t k‖ ≤ 8 / 7 * (t k).1 * zH R t (k + 1) ^ 2 := by
    have h := hist_G_w R X.hρ0 X.hρ8 t k hg0
    have e : (PtCorr2.kapH R t k).g = Obs2.gH R t k := rfl
    rw [e, div_le_iff₀ (pow_pos (X.zpos (k + 1)) 2)] at h
    exact h
  have hzk := X.zpos (k + 1)
  have hzj := X.zpos (j + 1)
  have h1 := X.dl_leU hj
  have h2 := X.rowS_leU (show k ≤ Nh by omega) P.a
  have h3 := X.lfunX_leU (show k ≤ Nh by omega) hj P.a
  have hz := zH_ratio_down R X.hρ0 X.hρ8 t (show k + 1 ≤ j + 1 by omega)
  rw [show j + 1 - (k + 1) = j - k by omega] at hz
  set u : ℝ := (L : ℝ)⁻¹ ^ (j - k) with hu
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by linarith))
  have hr := pow_ratio_L hL0 hkj.le
  have hr2 := pow_ratio_L2 hL0 hkj.le
  set A := R.ℓ ^ 2 / (16 * zH R t (j + 1)) / (2 * ((L : ℝ) ^ (j + 1)) ^ 2)
  set Bk := 18 * ((L : ℝ) ^ (k + 1)) ^ 2 * (R.ℓ ^ 2 / (16 * zH R t (k + 1)))
  set Xk := 36 * (R.ℓ ^ 2 / (16 * zH R t (k + 1))) * (R.ℓ ^ 2 / (16 * zH R t (j + 1))) *
    ((L : ℝ) ^ (k + 1) / (L : ℝ) ^ (j + 1))
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ Bk := by positivity
  have hX0 : 0 ≤ Xk := by positivity
  have hin : ‖2 * ((2 : ℕ) : ℂ) * Obs2.dlH R t j * Obs2.rowS (Obs2.histCovO R t k) P.a -
      Obs2.lfunX (Obs2.histCovO R t k) (Obs2.histCovO R t j) P.a‖ ≤ 4 * A * Bk + Xk := by
    refine (norm_sub_le _ _).trans (add_le_add ?_ h3)
    rw [norm_mul, norm_mul]
    have e4 : ‖(2 : ℂ) * ((2 : ℕ) : ℂ)‖ = 4 := by norm_num
    rw [e4]
    have h12 := mul_le_mul h1 h2 (norm_nonneg _) hA0
    nlinarith
  have hLn : (L : ℝ) ^ (j + 1) > 0 := by positivity
  have eAB : 4 * A * Bk = 9 / 64 * R.ℓ ^ 4 / (zH R t (k + 1) * zH R t (j + 1)) * u ^ 2 := by
    rw [tad_eAB R.ℓ hzk hzj hLn, ← div_pow, hr]
  have eX : Xk = 9 / 64 * R.ℓ ^ 4 / (zH R t (k + 1) * zH R t (j + 1)) * u := by
    simp only [Xk]
    rw [tad_eX R.ℓ hzk hzj, hr]
  have hq : (8 / 7 : ℝ) ^ (j - k) * u ≤ (2 / (L : ℝ)) ^ (j - k) := by
    rw [hu, ← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    rw [← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right (by norm_num) hL0.le
  have hfin : 8 / 7 * (t k).1 * zH R t (k + 1) ^ 2 * (4 * A * Bk + Xk) ≤
      c * (2 / (L : ℝ)) ^ (j - k) * (t k).1 := by
    rw [eAB, eX]
    exact tad_real hg0 hzk hzj (by positivity) X.hc4 hu0 hu1 hz hq (by positivity)
  calc ‖Obs2.gH R t k * (2 * ((2 : ℕ) : ℂ) * Obs2.dlH R t j * Obs2.rowS (Obs2.histCovO R t k) P.a -
        Obs2.lfunX (Obs2.histCovO R t k) (Obs2.histCovO R t j) P.a)‖
      ≤ 8 / 7 * (t k).1 * zH R t (k + 1) ^ 2 * (4 * A * Bk + Xk) := by
        rw [norm_mul]; exact mul_le_mul hgk hin (norm_nonneg _) (by positivity)
    _ ≤ _ := hfin

set_option maxHeartbeats 1000000 in
/-- **The size of `𝔫^{(2)}_{N_h}`**: `|𝔫_{N_h}| ≤ (4L² + 3)cǧ_{N_h}`. -/
theorem frakN2_top_le (P : Obs2.ObsPts 2 L N) (o₀ : Obs2.ObsSt .two L N) (h₀ : o₀.IsObs) :
    ‖Obs2.frakN2 P (Obs2.histCovO R t) (Obs2.histVO2 R P o₀ t) Nh‖ ≤
      (4 * (L : ℝ) ^ 2 + 3) * c * (t Nh).1 := by
  have hL0 := X.L_pos
  have hL7 := X.L7
  have hℓ : 0 < R.ℓ := Fact.out
  have hc0 := X.c_nonneg
  have HB := bulk2_histU R P o₀ t X.hV X.hVL h₀
  have hsplit : Obs2.frakN2 P (Obs2.histCovO R t) (Obs2.histVO2 R P o₀ t) Nh =
      (Obs2.kapH R t Nh).nu * Obs2.rowS (Obs2.histCovO R t Nh) P.a -
        (Obs2.kapH R t Nh).g * Obs2.lfunC (Obs2.histCovO R t Nh) P.a +
        ∑ k ∈ range Nh, Obs2.tadInc2 P (Obs2.histCovO R t) (Obs2.histVO2 R P o₀ t) k Nh := by
    rw [HB.frakN2_eq P (Nat.lt_succ_self Nh)]
    congr 1
    exact (sum_congr rfl fun k hk => HB.tadInc2_eq P (mem_range.1 hk) (Nat.lt_succ_self Nh)).symm
  have hnu := X.nu_le_gbU (le_refl Nh)
  have hrow := X.rowS_leU (le_refl Nh) P.a
  have hgH := X.gH_le_gb (le_refl Nh)
  have hlf := X.lfunC_leU (le_refl Nh) P.a
  set g := (t Nh).1 with hgd
  have hg0 : 0 ≤ g := (X.hg Nh le_rfl).1.le
  set zp := zH R t (Nh + 1) with hzpd
  have hzp : 0 < zp := X.zpos (Nh + 1)
  set s := R.ℓ ^ 2 / (16 * zp) with hs
  have hs0 : 0 ≤ s := by positivity
  set h2 := ((L : ℝ) ^ (Nh + 1)) ^ 2 with hh2
  have hh2p : 0 < h2 := by positivity
  have hzs : zp * s = R.ℓ ^ 2 / 16 := by rw [hs]; field_simp
  clear_value s h2
  set A := cmu' + 16 / 7 * cz' with hA
  have hA0 : 0 ≤ A := by have := X.hcmu; have := X.hcz; positivity
  have hℓA : R.ℓ ^ 2 * A ≤ 23 / 7 * c := by
    have := X.hcm; have := X.hcz2
    have e : R.ℓ ^ 2 * A = R.ℓ ^ 2 * cmu' + 16 / 7 * (R.ℓ ^ 2 * cz') := by rw [hA]; ring
    linarith
  have hc4 := X.hc4
  -- the three parts
  have t1 : ‖(Obs2.kapH R t Nh).nu * Obs2.rowS (Obs2.histCovO R t Nh) P.a‖ ≤
      (18 / 16 * (23 / 7) * (L : ℝ) ^ 2 + 1) * c * g := by
    rw [norm_mul]
    refine (mul_le_mul hnu hrow (norm_nonneg _) (by positivity)).trans ?_
    have e : (zp * (L : ℝ) ^ 2 / h2 * (A * g) + 16 / 7 * g * zp ^ 2 * s / h2) * (18 * h2 * s) =
        18 / 16 * (L : ℝ) ^ 2 * g * (R.ℓ ^ 2 * A) + 18 * 16 / 7 / 256 * g * R.ℓ ^ 4 := by
      have e3 : (zp * (L : ℝ) ^ 2 / h2 * (A * g) + 16 / 7 * g * zp ^ 2 * s / h2) * (18 * h2 * s) =
          18 * (L : ℝ) ^ 2 * A * g * (zp * s) + 18 * 16 / 7 * g * (zp * s) ^ 2 := by
        field_simp
      rw [e3, hzs]
      ring
    rw [e]
    have hLg : 0 ≤ (L : ℝ) ^ 2 * g := by positivity
    have h1 := mul_le_mul_of_nonneg_left hℓA hLg
    have h2' := mul_le_mul_of_nonneg_left hc4 hg0
    nlinarith
  have t2 : ‖(Obs2.kapH R t Nh).g * Obs2.lfunC (Obs2.histCovO R t Nh) P.a‖ ≤ c * g := by
    rw [norm_mul, Obs2.kapH_g]
    refine (mul_le_mul hgH hlf (norm_nonneg _) (by positivity)).trans ?_
    have e : 8 / 7 * g * zp ^ 2 * (18 * s ^ 2) = 8 / 7 * 18 / 256 * g * R.ℓ ^ 4 := by
      rw [show 8 / 7 * g * zp ^ 2 * (18 * s ^ 2) = 8 / 7 * 18 * g * (zp * s) ^ 2 by ring, hzs]
      ring
    rw [e]
    have h2' := mul_le_mul_of_nonneg_left hc4 hg0
    nlinarith
  have t3 : ‖∑ k ∈ range Nh, Obs2.tadInc2 P (Obs2.histCovO R t) (Obs2.histVO2 R P o₀ t) k Nh‖ ≤
      c * g := by
    refine (norm_sum_le _ _).trans ?_
    have hy0 : (0 : ℝ) ≤ 2 / L := by positivity
    have hy3 : (2 : ℝ) / L ≤ 1 / 3 := by rw [div_le_iff₀ hL0]; linarith
    have hterm : ∀ k ∈ range Nh,
        ‖Obs2.tadInc2 P (Obs2.histCovO R t) (Obs2.histVO2 R P o₀ t) k Nh‖ ≤
          c * g * (2 / (L : ℝ)) ^ (Nh - k) := by
      intro k hk
      have hk' := mem_range.1 hk
      refine (X.tadInc2_leU P o₀ h₀ hk' le_rfl).trans ?_
      have hgk : (t k).1 ≤ g := X.gmono hk'.le le_rfl
      have : 0 ≤ c * (2 / (L : ℝ)) ^ (Nh - k) := by positivity
      nlinarith
    refine (sum_le_sum hterm).trans ?_
    rw [← mul_sum]
    have hgeo := Obs2.geom_tail_le hy0 hy3 Nh
    have hcg : 0 ≤ c * g := by positivity
    nlinarith
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add ((norm_sub_le _ _).trans (add_le_add t1 t2)) t3).trans ?_
  have hcg : 0 ≤ c * g := by positivity
  have hL2 : 0 ≤ (L : ℝ) ^ 2 * (c * g) := by positivity
  nlinarith

end C2Ctx

section TopRem

variable {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

/-- `s_k² ≤ (9/8)ℓ²/|Z_{k+1}|`. -/
theorem histS_sq_le_z (t : Hist.Seq (Xs R)) (k : ℕ) (hρ0 : 0 ≤ R.ρ) (hρ8 : R.ρ ≤ 1 / 8) :
    PtCorr2.histS R k t ^ 2 ≤ 9 / 8 * R.ℓ ^ 2 * (zH R t (k + 1))⁻¹ := by
  have hZ0 : 0 < zH R t k := zH_pos R hρ0 hρ8 t k
  have hZ1p : 0 < zH R t (k + 1) := zH_pos R hρ0 hρ8 t (k + 1)
  have hZ1 : zH R t (k + 1) ≤ 9 / 8 * zH R t k := by
    rw [norm_Z_succ]
    have := (one_add_zeta_bds R hρ0 hρ8 t k).2
    nlinarith
  have e : PtCorr2.histS R k t ^ 2 = R.ℓ ^ 2 * (zH R t k)⁻¹ := by
    unfold PtCorr2.histS; rw [mul_pow, Step2.fscale_sq]; ring
  rw [e]
  have hi : (zH R t k)⁻¹ ≤ 9 / 8 * (zH R t (k + 1))⁻¹ := by
    rw [← sub_nonneg]
    have e2 : 9 / 8 * (zH R t (k + 1))⁻¹ - (zH R t k)⁻¹ =
        (9 / 8 * zH R t k - zH R t (k + 1)) / (zH R t (k + 1) * zH R t k) := by
      field_simp
    rw [e2]
    exact div_nonneg (by linarith) (by positivity)
  have := mul_le_mul_of_nonneg_left hi (sq_nonneg R.ℓ)
  linarith

set_option maxHeartbeats 4000000 in
/-- **`ρ_{N_h}` relative to the vertex and `1/|Z_{N_h+1}|`**: from the block bounds of `𝒲^{obs}`,
`K^{obs}` at `N_h` (relative to `β_{N_h}`) and the bulk bound at `N_h`,
`‖gamWK2_{N_h} + β_{N_h}E_{N_h}‖ ≤ ((256c_Nc_WB + 2c_BQ₁c_W)(9/8)ℓ² + K_b)‖β_{N_h}‖/|Z_{N_h+1}|`. -/
theorem gamRem2_top_le {cmu' cz' cd c' : ℝ} {t : Hist.Seq (Xs R)}
    (X : C2Ctx R Nh t cmu' cz' cd c')
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hmN : |R.msq| * ((L : ℝ) ^ Nh) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1) (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    (hLp : pauliL0 2 ≤ L) (P : Obs2.ObsPts 2 L N) (V : Obs2.OCoup .two)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε Nh t)
    (hzy : ‖(rawHist R Nh t).z + (rawHist R Nh t).y‖ ≤ 2 * cz' * (t Nh).1 * zH R t Nh)
    {cW Bk r : ℝ} (hcW : 1 ≤ cW) (hBk : 0 ≤ Bk) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hWb : WbHc R P (Obs2.obsInit .two V P) t Nh (cW * r * (2 * PtCorr2.histS R Nh t ^ 2 *
      ‖Obs2.betaTot2 (L := L) (N := N) Nh (Obs2.histVO2 R P (Obs2.obsInit .two V P) t Nh)‖)))
    (hKb : KbHc R P (Obs2.obsInit .two V P) t Nh (16 * cW * Bk * r ^ 2 *
      (PtCorr2.histS R Nh t ^ 2 *
        ‖Obs2.betaTot2 (L := L) (N := N) Nh (Obs2.histVO2 R P (Obs2.obsInit .two V P) t Nh)‖))) :
    ‖Obs2.gamWK2 R P (Obs2.obsInit .two V P) t Nh +
        Obs2.betaTot2 (L := L) (N := N) Nh (Obs2.histVO2 R P (Obs2.obsInit .two V P) t Nh) *
          Grassmann.ε (FC (Obs2.histCovO R t Nh) (Obs.LocObs.pbp P.a)
            (Vcoup (Obs2.kapH R t Nh) univ))‖ ≤
      ((256 * (csN 2 : ℝ) * cW * Bk + 2 * (cBn : ℝ) * Q1 2 * cW) * (9 / 8 * R.ℓ ^ 2) +
          gbKb L R.ℓ cmu' cz') *
        ‖Obs2.betaTot2 (L := L) (N := N) Nh (Obs2.histVO2 R P (Obs2.obsInit .two V P) t Nh)‖ *
        (zH R t (Nh + 1))⁻¹ := by
  set bb := ‖Obs2.betaTot2 (L := L) (N := N) Nh (Obs2.histVO2 R P (Obs2.obsInit .two V P) t Nh)‖
    with hbb
  have hb0 : 0 ≤ bb := norm_nonneg _
  have hρ0 := X.hρ0
  have hρ8 := X.hρ8
  have hzp : 0 < zH R t (Nh + 1) := X.zpos (Nh + 1)
  have hzi : 0 ≤ (zH R t (Nh + 1))⁻¹ := inv_nonneg.2 hzp.le
  have hs := histS_pos' R hρ0 hρ8 t Nh
  have hℓ2 : 0 ≤ R.ℓ ^ 2 := sq_nonneg _
  have hQ : 1 ≤ Q1 2 := one_le_Q1 (by norm_num)
  -- the `K`/`𝒲` part
  have hbd := gamWK2_leL R hSB X.hV hm X.hVL hmN hβ hδ1 H hLp P (Obs2.obsInit .two V P)
    (obsLocInv_init .two V P) t (by have := X.hN; omega) ht
    (w := cW * r * (2 * PtCorr2.histS R Nh t ^ 2 * bb))
    (kk := 16 * cW * Bk * r ^ 2 * (PtCorr2.histS R Nh t ^ 2 * bb)) (by positivity) (by positivity)
    hWb hKb
  set G : ℝ := 9 / 8 * R.ℓ ^ 2 * (zH R t (Nh + 1))⁻¹ with hG
  have hG0 : 0 ≤ G := by positivity
  have hCaa : ‖Obs2.histCovO R t Nh P.a P.a‖ ≤ G := by
    rw [(histCov_constsU R t X.hV X.hVL (le_refl Nh)).1 P.a]
    refine (X.c0_le_gbU (le_refl Nh)).trans (le_of_eq_of_le rfl ?_)
    rw [hG, div_eq_mul_inv, mul_inv]
    have : (16 : ℝ)⁻¹ ≤ 9 / 8 := by norm_num
    have := mul_le_mul_of_nonneg_right this (mul_nonneg hℓ2 hzi)
    nlinarith
  have hT : ‖Obs2.gamWK2 R P (Obs2.obsInit .two V P) t Nh‖ ≤
      csN 2 * (8 * (16 * cW * Bk * r ^ 2 * (PtCorr2.histS R Nh t ^ 2 * bb))) +
        G * (csN 2 * (8 * (16 * cW * Bk * r ^ 2 * (PtCorr2.histS R Nh t ^ 2 * bb))) *
          (PtCorr2.histS R Nh t)⁻¹ ^ 2) +
        (cBn : ℝ) * (Q1 2 * (cW * r * (2 * PtCorr2.histS R Nh t ^ 2 * bb))) := by
    have := mul_le_mul_of_nonneg_right hCaa (by positivity : (0 : ℝ) ≤
      csN 2 * (8 * (16 * cW * Bk * r ^ 2 * (PtCorr2.histS R Nh t ^ 2 * bb))) *
        (PtCorr2.histS R Nh t)⁻¹ ^ 2)
    linarith
  have hsG : PtCorr2.histS R Nh t ^ 2 ≤ 1 * G := by
    rw [one_mul, hG]; exact histS_sq_le_z R t Nh hρ0 hρ8
  have hWK := wk_alg (c := 1) (g := r) (a := 0) hT rfl rfl hs hsG (by ring) hr0 hr1 le_rfl
    zero_le_one (Nat.cast_nonneg _) (by linarith) hBk (Nat.cast_nonneg _) (by linarith) hb0 hG0
  -- the bulk part
  have hE := X.gamBulk_le_posU (le_refl Nh) hzy P.a
  have hg1 : (t Nh).1 ≤ 1 := (X.hg Nh le_rfl).2
  have hg0 : 0 ≤ (t Nh).1 := (X.hg Nh le_rfl).1.le
  have hKb0 : 0 ≤ gbKb L R.ℓ cmu' cz' := gbKb_nonneg X.hcmu X.hcz
  have hE' : ‖Grassmann.ε (FC (Obs2.histCovO R t Nh) (Obs.LocObs.pbp P.a)
      (Vcoup (Obs2.kapH R t Nh) univ))‖ ≤
      gbKb L R.ℓ cmu' cz' * (zH R t (Nh + 1))⁻¹ := by
    refine hE.trans ?_
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hKb0 hg1) hzi
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  have h2 := mul_le_mul_of_nonneg_left hE' hb0
  have e : (1 : ℝ) * (128 * csN 2 * cW * Bk * (1 + 1) + 2 * cBn * Q1 2 * cW * 1) * (r + 0) * bb * G =
      (256 * (csN 2 : ℝ) * cW * Bk + 2 * (cBn : ℝ) * Q1 2 * cW) * (9 / 8 * R.ℓ ^ 2) * bb *
        (zH R t (Nh + 1))⁻¹ * r := by rw [hG]; ring
  rw [e] at hWK
  have hK0 : 0 ≤ (256 * (csN 2 : ℝ) * cW * Bk + 2 * (cBn : ℝ) * Q1 2 * cW) * (9 / 8 * R.ℓ ^ 2) *
      bb * (zH R t (Nh + 1))⁻¹ := by
    have : (0 : ℝ) ≤ csN 2 := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ cBn := Nat.cast_nonneg _
    have : 0 ≤ cW := by linarith
    have : 0 ≤ Q1 2 := by linarith
    positivity
  have h1 := hWK.trans (mul_le_of_le_one_right hK0 hr1)
  nlinarith

end TopRem

end

end Spin2
