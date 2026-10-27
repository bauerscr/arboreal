import Step2.Lip.FlowLipRunH

/-!
# The Lipschitz bounds for a pair of histories (Lipschitz bounds, part 33)

`lip_pair`: given the one-step comparison bounds (`cmp_K`, `cmp_D`, `cmp_W`, `cmp_kap`, the sizes
`size_rem`, the decay of the covariances), the a priori bounds and the smallness conditions,
the maps `T_j`, `G_j`, `m_j` of `rgData R` satisfy, for two histories in the domain with
`dist3 (t_i, t'_i) ≤ M` for `i < j`:
* `‖δT_j‖ ≤ κ₁ ‖δx_j‖ + C_L ε (‖δx_j‖ + |δg_j| + |δμ_j| + M)` (both components);
* `|δG_j| ≤ (1 + C_L(ε + ϑ)) |δg_j| + C_L(ε + ϑ) |δμ_j| + C_L ‖δx_j‖ + C_L(ε + ϑ) M`;
* `|δm_j| ≤ C_L |δg_j| + C_L(ε + ϑ) |δμ_j| + C_L ‖δx_j‖ + C_L(ε + ϑ) M`.
-/

namespace Step2

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD Flow2

/-! ### The constants -/

def cV0 (ℓ β : ℝ) : ℝ := 2 * ka0 ℓ β + 1
def cLam0 (L : ℕ) (Kc : ℝ) : ℝ := 2 * Kc * (L : ℝ) ^ 8
def cbb (L : ℕ) (ℓ Kc : ℝ) : ℝ := 2 * ℓ ^ 2 / (L : ℝ) ^ 2 + 9 * cLam0 L Kc
def cZ0 (L : ℕ) (ℓ Kc β : ℝ) : ℝ := 4 * cbb L ℓ Kc * cV0 ℓ β
def cA0 (L : ℕ) (ℓ β cmu cwx cw Kc C₂ κW : ℝ) : ℝ :=
  kAll ℓ β cmu (cTh ℓ cw cwx) (cLam0 L Kc) C₂ κW cw
def cW0 (L : ℕ) (ℓ β cmu cwx cw Kc C₂ κW : ℝ) : ℝ :=
  2 * cA0 L ℓ β cmu cwx cw Kc C₂ κW * (1 + 2 * cV0 ℓ β + cZ0 L ℓ Kc β)
def cKT0 (L : ℕ) (ℓ β cmu cwx cw Kc C₂ κW : ℝ) : ℝ :=
  kTh ℓ cmu (cTh ℓ cw cwx) (cLam0 L Kc) (cV0 ℓ β) (cW0 L ℓ β cmu cwx cw Kc C₂ κW) (cZ0 L ℓ Kc β)
def cK0 (L : ℕ) (ℓ β b₁ cmu cz cwx cw Kc C₂ κW : ℝ) : ℝ :=
  cKa L β b₁ ℓ cmu cz (cV0 ℓ β) (cZ0 L ℓ Kc β) (cLam0 L Kc) (cKT0 L ℓ β cmu cwx cw Kc C₂ κW)

/-- **The Lipschitz constant `C_L`.** -/
def cLip (L : ℕ) (ℓ β b₁ cmu cz cwx cw Kc C₂ κW κK κD C₁ C₃ cE : ℝ) : ℝ :=
  (cE + 1) * (300 * cK0 L ℓ β b₁ cmu cz cwx cw Kc C₂ κW ^ 4 +
    cTT κK κD C₁ C₃ (cKT0 L ℓ β cmu cwx cw Kc C₂ κW) cwx (cV0 ℓ β)) +
    500 * cK0 L ℓ β b₁ cmu cz cwx cw Kc C₂ κW ^ 4 + 2 * cK0 L ℓ β b₁ cmu cz cwx cw Kc C₂ κW

/-- The closure constant of the error recursion. -/
def cClo (L : ℕ) (ℓ β cmu cwx cw Kc C₂ κW : ℝ) : ℝ :=
  cA0 L ℓ β cmu cwx cw Kc C₂ κW * (2 * (8 * β) * (1 + 2 * cV0 ℓ β + 4 * cbb L ℓ Kc * cV0 ℓ β) +
    (2 * cV0 ℓ β + 4 * cbb L ℓ Kc * cV0 ℓ β))

variable {L N : ℕ} [NeZero L]

theorem InDh_le {X : ℕ → Type*} [∀ j, NormedAddCommGroup (X j)] {Λ β δ κ cg cm cT ε : ℝ}
    {j k : ℕ} {t : Hist.Seq X} (h : Hist.InDh Λ β δ κ cg cm cT ε j t) (hk : k ≤ j) :
    Hist.InDh Λ β δ κ cg cm cT ε k t :=
  ⟨fun i hi => h.1 i (by omega), fun i hi => h.2 i (by omega)⟩

section Pair

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

set_option maxHeartbeats 4000000 in
/-- **The Lipschitz bounds for a pair of histories.** -/
theorem lip_pair {Nh : ℕ} (hV : ∀ j < Nh, ValidAt R j) {ϑ : ℝ} (hϑ0 : 0 ≤ ϑ) (hϑ1 : ϑ ≤ 1)
    (hmϑ : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ (j + 2)) ^ 2 ≤ ϑ)
    {Λ β δ κ cg cm cT ε cz cw Kc : ℝ}
    (hAP : ∀ k ≤ Nh, ∀ t : Hist.Seq (Xs R), Hist.InDh Λ β δ κ cg cm cT ε k t →
      APB R cz cw (t k).1 (rawHist R k t) k)
    (hCov : ∀ k, (∀ i ≤ k, ValidAt R i) → ∀ t t' : Hist.Seq (Xs R),
      GoodCov2 k (lD R Kc k t t') (CvH R k t' - CvH R k t))
    {ε₁ κK κD C₁ C₃ C₂ C₀W Cq Cl cS Cq' Cl' cS' κ₁ : ℝ}
    (hcK : ∀ (k : ℕ) (t t' : Hist.Seq (Xs R)) (e ℓΔ : ℝ), Cmp R k t t' Λ κ cm cT ε cz cw e ℓΔ →
      e ≤ ε₁ → Knorm (k + 1) R.ℓ R.A (nKH R k t' - nKH R k t) ≤
        ENNReal.ofReal (4 * (2 * κK * e ^ 2 + 16 * C₁ * e ^ 3) * relDist e (aIn R k t t')
          (bWIn R cw k t t' + bDIn R (cx κ cT) k t t') (cIn R (cx κ cT) k t t') ℓΔ 1 (R.ℓ / 4)))
    (hcD : ∀ (k : ℕ) (t t' : Hist.Seq (Xs R)) (e ℓΔ : ℝ), Cmp R k t t' Λ κ cm cT ε cz cw e ℓΔ →
      e ≤ 1 / 4 → Fnorm (k + 1) R.ℓ (nDH R k t' - nDH R k t) ≤
        ENNReal.ofReal (4 * (2 * κD * e ^ 2 + 64 * C₃ * e ^ 4) * relDist e (aIn R k t t')
          (bWIn R cw k t t' + bDIn R (cx κ cT) k t t') (bDIn R (cx κ cT) k t t') ℓΔ 1 (R.ℓ / 4)))
    (hcW : ∀ (k : ℕ) (t t' : Hist.Seq (Xs R)) (e ℓΔ : ℝ), Cmp R k t t' Λ κ cm cT ε cz cw e ℓΔ →
      e ≤ 1 / 2 → Fnorm (k + 1) R.ℓ (nWlH R k t' - nWlH R k t) ≤
        ENNReal.ofReal (4 * (4 * C₂ * e ^ 2) * relDist e (aIn R k t t') 0 0 ℓΔ 1 (R.ℓ / 4) +
          4 * (2 * (C₀W * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3)) * ((cw + 1) * ε ^ 2)) *
            (bWIn R cw k t t' / ((cw + 1) * ε ^ 2) + ℓΔ ^ 2 / (1 * (R.ℓ / 4)) ^ 2)))
    (hck : ∀ (k : ℕ) (t t' : Hist.Seq (Xs R)) (e ℓΔ : ℝ), Cmp R k t t' Λ κ cm cT ε cz cw e ℓΔ →
      e ≤ 1 / 2 → ∀ i : Fin 4, cwt L k i * ‖(kapH R k t' i - kapH R k t i) -
          (SD.shv R k (sdH R k t') i - SD.shv R k (sdH R k t) i)‖ ≤
        4 * bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) (2 * e) (2 * e ^ 2)
          (2 * e ^ 2) * relDist e (aIn R k t t') (bWIn R cw k t t' + bDIn R (cx κ cT) k t t')
            (cIn R (cx κ cT) k t t') ℓΔ 1 (R.ℓ / 4))
    (hsz : ∀ (k : ℕ) (t : Hist.Seq (Xs R)), DomH k t Λ κ cm cT ε cz cw →
      |R.msq| * ((L : ℝ) ^ k) ^ 2 ≤ 1 → (t k).1 ≤ 1 → cDl (7 / 8 * R.ℓ) cz * (t k).1 ≤ 1 / 4 →
      cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) * (t k).1 ≤ 1 →
      Real.exp 1 * (cx κ cT * (t k).1 ^ 3) ≤ 1 →
      ∀ i : Fin 4, cwt L k i * ‖kapH R k t i - SD.shv R k (sdH R k t) i‖ ≤
        bRem L Cq' Cl' cS' (7 / 8 * R.ℓ) R.ℓ (R.ℓ / 4) (cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) * (t k).1)
          ((cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) * (t k).1) ^ 2)
          (Real.exp 1 * (cx κ cT * (t k).1 ^ 3)))
    (hcz : 0 ≤ cz) (hcw : 0 ≤ cw) (hcx : 0 ≤ cx κ cT) (hcmu : 0 ≤ cmu Λ cm) (hKc : 0 ≤ Kc)
    (hκK : 0 ≤ κK) (hκD : 0 ≤ κD) (hC₁ : 0 ≤ C₁) (hC₃ : 0 ≤ C₃) (hC₂ : 0 ≤ C₂) (hC₀W : 0 ≤ C₀W)
    (hCq : 0 ≤ Cq) (hCl : 0 ≤ Cl) (hcS : 0 ≤ cS) (hCq' : 0 ≤ Cq') (hCl' : 0 ≤ Cl') (hcS' : 0 ≤ cS')
    (hL2 : 2 ≤ L) (hq : 8 * (C₀W * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3)) + 9 / (8 * (L : ℝ) ^ 2) ≤ 1 / 2)
    (hκ₁ : 8 * (2 + Real.exp 1) * κK ≤ κ₁) (hκ₁' : 8 * (2 + Real.exp 1) * κD ≤ κ₁)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hρ : 2 * cz * ε ≤ R.ρ) (h16 : 2 * cz * ε ≤ 1 / 16)
    (hΔ : cDl (7 / 8 * R.ℓ) cz * ε ≤ 1 / 4)
    (hE1 : cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) * ε ≤ 1 / 4)
    (hE2 : cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) * ε ≤ ε₁)
    (hnd : 4 * cmu Λ cm * ε * R.ℓ ^ 2 ≤ 1 / 8)
    (hclo : (cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) + 1) * ε *
      cClo L R.ℓ (bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2) (cmu Λ cm)
        (cx κ cT) cw Kc C₂ (C₀W * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3)) ≤ 1 / 2)
    (hsz1 : ε * cSz (bR1 L Cq' Cl' cS' R.ℓ (cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm)) (cx κ cT)) R.ℓ ≤ R.ρ)
    (hsz2 : ε * (cSz (bR1 L Cq' Cl' cS' R.ℓ (cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm)) (cx κ cT)) R.ℓ +
      cSn L (bR1 L Cq' Cl' cS' R.ℓ (cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm)) (cx κ cT)) cz R.ℓ
        (cmu Λ cm)) ≤ 1 / 16) :
    let CL := cLip L R.ℓ (bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2)
      (bR1 L Cq' Cl' cS' R.ℓ (cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm)) (cx κ cT)) (cmu Λ cm) cz
      (cx κ cT) cw Kc C₂ (C₀W * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3)) κK κD C₁ C₃
      (cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm))
    ∀ j < Nh, ∀ t t' : Hist.Seq (Xs R), Hist.InDh Λ β δ κ cg cm cT ε j t →
      Hist.InDh Λ β δ κ cg cm cT ε j t' → ∀ M, 0 ≤ M →
      (∀ i < j, Hist.dist3 (t i) (t' i) ≤ M) →
      (‖(Tmap R j t).2 - (Tmap R j t').2‖ ≤ κ₁ * ‖(t j).2.2 - (t' j).2.2‖ +
          CL * ε * (‖(t j).2.2 - (t' j).2.2‖ + |(t j).1 - (t' j).1| + |(t j).2.1 - (t' j).2.1| + M) ∧
        ‖(Tmap R j t).1 - (Tmap R j t').1‖ ≤ κ₁ * ‖(t j).2.2 - (t' j).2.2‖ +
          CL * ε * (‖(t j).2.2 - (t' j).2.2‖ + |(t j).1 - (t' j).1| + |(t j).2.1 - (t' j).2.1| + M)) ∧
      |(rgData R).G j t - (rgData R).G j t'| ≤ (1 + CL * (ε + ϑ)) * |(t j).1 - (t' j).1| +
        CL * (ε + ϑ) * |(t j).2.1 - (t' j).2.1| + CL * ‖(t j).2.2 - (t' j).2.2‖ + CL * (ε + ϑ) * M ∧
      |(rgData R).m j t - (rgData R).m j t'| ≤ CL * |(t j).1 - (t' j).1| +
        CL * (ε + ϑ) * |(t j).2.1 - (t' j).2.1| + CL * ‖(t j).2.2 - (t' j).2.2‖ +
        CL * (ε + ϑ) * M := by
  intro CL j hj t t' ht ht' M hM hd
  have hℓ : 0 < R.ℓ := Fact.out
  have hval : ∀ i ≤ j, ValidAt R i := fun i hi => hV i (by omega)
  have hA : ∀ k ≤ j, APB R cz cw (t k).1 (rawHist R k t) k := fun k hk =>
    hAP k (by omega) t (InDh_le ht hk)
  have hA' : ∀ k ≤ j, APB R cz cw (t' k).1 (rawHist R k t') k := fun k hk =>
    hAP k (by omega) t' (InDh_le ht' hk)
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hm : ∀ k ≤ j, |R.msq| * ((L : ℝ) ^ k) ^ 2 ≤ 1 := fun k hk => by
    have h1 := hmϑ k (by omega)
    have h2 : ((L : ℝ) ^ k) ^ 2 ≤ ((L : ℝ) ^ (k + 2)) ^ 2 := by
      have : (L : ℝ) ^ k ≤ (L : ℝ) ^ (k + 2) := pow_le_pow_right₀ hL1 (by omega)
      gcongr
    have := mul_le_mul_of_nonneg_left h2 (abs_nonneg R.msq)
    linarith
  have hC : ∀ k ≤ j, GoodCov2 k (lD R Kc k t t') (CvH R k t' - CvH R k t) := fun k hk =>
    hCov k (fun i hi => hV i (by omega)) t t'
  set cE := cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) with hcEd
  have H := run_of hval ht ht' hA hA' hm hC hcz hcw hcx hcmu hKc hε0 hε1 hρ h16 hΔ
    (hE1.trans (by norm_num)) hnd
  set e := cE * ε with hed
  have he := (H.cmp 0 (Nat.zero_le _)).he
  have hcE0 : 0 ≤ cE := by
    have := he.le; rw [hed] at this
    exact nonneg_of_mul_nonneg_left (by linarith) hε0
  -- the error recursion
  set β₀ := bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2 with hβd
  have hβ0 : 0 ≤ β₀ := by
    rw [hβd]; unfold bRem
    have := BHsig_nonneg (L := L) (v := (2 : ℝ)) (by norm_num : (0 : ℝ) ≤ 2)
    have : 0 ≤ ((7 / 8 * R.ℓ) ^ 2)⁻¹ := inv_nonneg.2 (sq_nonneg _)
    have : 0 ≤ ((7 / 8 * R.ℓ) ^ 4)⁻¹ := inv_nonneg.2 (by positivity)
    have : 0 ≤ (R.ℓ ^ 2)⁻¹ := inv_nonneg.2 (sq_nonneg _)
    have : 0 ≤ (R.ℓ ^ 4)⁻¹ := inv_nonneg.2 (by positivity)
    positivity
  set κW := C₀W * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3) with hκWd
  have hκW : 0 ≤ κW := by positivity
  set kA := cA0 L R.ℓ β₀ (cmu Λ cm) (cx κ cT) cw Kc C₂ κW with hkAd
  have hcTh : 0 ≤ cTh R.ℓ cw (cx κ cT) := by
    unfold cTh; have : (0 : ℝ) ≤ cM := Nat.cast_nonneg _; positivity
  have hkA : 0 ≤ kA := by
    have hΛ : 0 ≤ cLam0 L Kc := by unfold cLam0; positivity
    obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := kAll_parts hℓ hβ0 hcmu hcTh hΛ hC₂ hκW hcw
    rw [hkAd]; unfold cA0 kAll; linarith
  have ha₀ : 0 ≤ ka0 R.ℓ β₀ := by
    unfold ka0; have := kX_nonneg R.ℓ; have := (Real.exp_pos 1).le; positivity
  have hbb : 0 ≤ cbb L R.ℓ Kc := by unfold cbb cLam0; positivity
  have hσ : 0 ≤ e + ε := by linarith
  have hsmall : ((e + ε) * kA) * (2 * (8 * β₀) * (1 + 2 * (2 * ka0 R.ℓ β₀ + 1) +
      4 * cbb L R.ℓ Kc * (2 * ka0 R.ℓ β₀ + 1)) + (2 * (2 * ka0 R.ℓ β₀ + 1) +
      4 * cbb L R.ℓ Kc * (2 * ka0 R.ℓ β₀ + 1))) ≤ 1 / 2 := by
    have e1 : ((e + ε) * kA) * (2 * (8 * β₀) * (1 + 2 * (2 * ka0 R.ℓ β₀ + 1) +
        4 * cbb L R.ℓ Kc * (2 * ka0 R.ℓ β₀ + 1)) + (2 * (2 * ka0 R.ℓ β₀ + 1) +
        4 * cbb L R.ℓ Kc * (2 * ka0 R.ℓ β₀ + 1))) = (cE + 1) * ε *
        cClo L R.ℓ β₀ (cmu Λ cm) (cx κ cT) cw Kc C₂ κW := by
      rw [hed, hkAd]; unfold cClo cV0; ring
    rw [e1]; exact hclo
  obtain ⟨c1, c2, c3⟩ := err_consts ha₀ (by positivity : (0 : ℝ) ≤ 8 * β₀) (by positivity)
    (by positivity : (0 : ℝ) ≤ 8 * κW + 9 / (8 * (L : ℝ) ^ 2)) hq hbb hsmall
  have hV0 : 0 ≤ 2 * ka0 R.ℓ β₀ + 1 := by positivity
  have hZ0 : 0 ≤ 4 * cbb L R.ℓ Kc * (2 * ka0 R.ℓ β₀ + 1) := by positivity
  have hW0 : 0 ≤ 2 * ((e + ε) * kA) * (1 + 2 * (2 * ka0 R.ℓ β₀ + 1) +
      4 * cbb L R.ℓ Kc * (2 * ka0 R.ℓ β₀ + 1)) := by positivity
  have hkAe : kA = kAll R.ℓ β₀ (cmu Λ cm) (cTh R.ℓ cw (cx κ cT)) (2 * Kc * (L : ℝ) ^ 8) C₂ κW cw := by
    rw [hkAd]; rfl
  have hbbe : cbb L R.ℓ Kc = 2 * R.ℓ ^ 2 / (L : ℝ) ^ 2 + 9 * (2 * Kc * (L : ℝ) ^ 8) := rfl
  rw [hkAe] at c1 c2
  have herr := run_errors H hM hd hC₀W hC₂ hβ0
    (fun k hk => hck k t t' e (lD R Kc k t t') (H.cmp k hk.le) (hE1.trans (by norm_num)))
    (fun k hk => hcW k t t' e (lD R Kc k t t') (H.cmp k hk.le) (hE1.trans (by norm_num)))
    hV0 hW0 hZ0 c1 c2 c3
  obtain ⟨hev, heW, hew⟩ := herr j le_rfl
  set V := 2 * ka0 R.ℓ β₀ + 1
  set Z := 4 * cbb L R.ℓ Kc * V
  set W₁ := cW0 L R.ℓ β₀ (cmu Λ cm) (cx κ cT) cw Kc C₂ κW with hW₁d
  have hW₁0 : 0 ≤ W₁ := by rw [hW₁d]; unfold cW0; have := hV0; positivity
  have heW' : eWH R j t t' ≤ (e + ε) * W₁ * M := by
    refine heW.trans (le_of_eq ?_)
    rw [hW₁d]; unfold cW0 cZ0 cV0; rw [← hkAd]; ring
  have hZ0' : 0 ≤ Z := hZ0
  -- (LT)
  have HC := H.cmp j le_rfl
  obtain ⟨LTK, LTD⟩ := LT_hist H hval hM hV0 hW₁0 hZ0' hev heW' hew hκK hκD hC₁ hC₃ hκ₁ hκ₁'
    (hcK j t t' e (lD R Kc j t t') HC hE2) (hcD j t t' e (lD R Kc j t t') HC hE1)
  -- the final-step facts
  set b₁ := bR1 L Cq' Cl' cS' R.ℓ cE (cx κ cT) with hb₁d
  have hb₁ : 0 ≤ b₁ := bR1_nonneg hCq' hCl' hcS' hcx
  have hsn : ε * cSn L b₁ cz R.ℓ (cmu Λ cm) ≤ 1 / 8 := by
    have : 0 ≤ ε * cSz b₁ R.ℓ := by unfold cSz; positivity
    linarith
  have hfin : ∀ tt : Hist.Seq (Xs R), Hist.InDh Λ β δ κ cg cm cT ε j tt →
      (∀ k ≤ j, APB R cz cw (tt k).1 (rawHist R k tt) k) →
      FinOne R j tt ε b₁ cz (cmu Λ cm) := fun tt htt hAt => by
    have HD := domH_of hval htt hAt hcz hρ h16 (le_refl j)
    have hg := HD.g_pos
    have hgε := HD.g_le
    have hcDl : 0 ≤ cDl (7 / 8 * R.ℓ) cz := by
      unfold cDl; have : (0 : ℝ) ≤ cM := Nat.cast_nonneg _; positivity
    have hd1 : cDl (7 / 8 * R.ℓ) cz * (tt j).1 ≤ 1 / 4 :=
      (mul_le_mul_of_nonneg_left hgε hcDl).trans hΔ
    have hd2 : cE * (tt j).1 ≤ 1 := (mul_le_mul_of_nonneg_left hgε hcE0).trans (hE1.trans (by norm_num))
    have h1 : (tt j).1 ^ 3 ≤ ε := by
      have : (tt j).1 ^ 3 ≤ ε ^ 3 := by gcongr
      have : ε ^ 3 ≤ ε := by
        have := pow_le_pow_of_le_one hε0.le hε1 (show 1 ≤ 3 by norm_num); simpa using this
      linarith
    have h2 : 3 * cx κ cT ≤ cE := by
      rw [hcEd]; unfold cEr
      have : 0 ≤ cVf (7 / 8 * R.ℓ) cz (cmu Λ cm) := by
        unfold cVf; have : (0 : ℝ) ≤ cM := Nat.cast_nonneg _; positivity
      linarith
    have h3 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
    have hd3 : Real.exp 1 * (cx κ cT * (tt j).1 ^ 3) ≤ 1 := by
      have a := mul_le_mul h3 (mul_le_mul_of_nonneg_left h1 hcx) (by positivity) (by norm_num)
      have b : 3 * (cx κ cT * ε) ≤ 1 := by
        have := mul_le_mul_of_nonneg_right h2 hε0.le
        linarith
      linarith
    exact finOne_of HD hCq' hCl' hcS' hcw hcx hcmu hε1 (hm j le_rfl) hL2 (nW1H_le hval tt le_rfl)
      (hsz j tt HD (hm j le_rfl) (hgε.trans hε1) hd1 hd2 hd3) hsz1 hsn
  have F := hfin t ht hA
  have F' := hfin t' ht' hA'
  have hkapj := hck j t t' e (lD R Kc j t t') HC (hE1.trans (by norm_num))
  have hLG := LG_hist H F F' hM hV0 hW₁0 hZ0' hβ0 hb₁ hev heW' hew hβd hkapj hsz2
  have hLm := Lm_hist H F F' hM hV0 hW₁0 hZ0' hβ0 hb₁ hϑ0 (hmϑ j hj) hev heW' hew hβd hkapj
    (by have : 0 ≤ ε * cSn L b₁ cz R.ℓ (cmu Λ cm) := by unfold cSn cSν cSY; positivity
        linarith)
  -- the constants
  set K₀ := cK0 L R.ℓ β₀ b₁ (cmu Λ cm) cz (cx κ cT) cw Kc C₂ κW with hK₀d
  set CT₀ := cTT κK κD C₁ C₃ (cKT0 L R.ℓ β₀ (cmu Λ cm) (cx κ cT) cw Kc C₂ κW) (cx κ cT)
    (cV0 R.ℓ β₀) with hCT₀d
  have hKeq : cKa L β₀ b₁ R.ℓ (cmu Λ cm) cz V Z (2 * Kc * (L : ℝ) ^ 8)
      (kTh R.ℓ (cmu Λ cm) (cTh R.ℓ cw (cx κ cT)) (2 * Kc * (L : ℝ) ^ 8) V W₁ Z) = K₀ := rfl
  have hCTeq : cTT κK κD C₁ C₃ (kTh R.ℓ (cmu Λ cm) (cTh R.ℓ cw (cx κ cT)) (2 * Kc * (L : ℝ) ^ 8)
      V W₁ Z) (cx κ cT) V = CT₀ := rfl
  rw [hKeq] at hLG hLm
  rw [hCTeq] at LTK LTD
  have hCLd : CL = (cE + 1) * (300 * K₀ ^ 4 + CT₀) + 500 * K₀ ^ 4 + 2 * K₀ := rfl
  have hK0 : 0 ≤ K₀ := by
    have hkT : 0 ≤ kTh R.ℓ (cmu Λ cm) (cTh R.ℓ cw (cx κ cT)) (2 * Kc * (L : ℝ) ^ 8) V W₁ Z := by
      unfold kTh; have := kX_nonneg R.ℓ; have : (0 : ℝ) ≤ cM := Nat.cast_nonneg _; positivity
    have := (cKa_ge (β := β₀) (b₁ := b₁) (ℓ := R.ℓ) (cmu := cmu Λ cm) (cz := cz) (V := V) (Z := Z)
      (Λ0 := 2 * Kc * (L : ℝ) ^ 8) (kThv := kTh R.ℓ (cmu Λ cm) (cTh R.ℓ cw (cx κ cT))
        (2 * Kc * (L : ℝ) ^ 8) V W₁ Z) L hβ0 hb₁ hcmu hcz hV0 hZ0' (by positivity) hkT).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    rw [hKeq] at this; linarith
  have hCT0 : 0 ≤ CT₀ := by
    rw [hCT₀d]; unfold cTT cKT0
    have hkT : 0 ≤ kTh R.ℓ (cmu Λ cm) (cTh R.ℓ cw (cx κ cT)) (cLam0 L Kc) (cV0 R.ℓ β₀)
        (cW0 L R.ℓ β₀ (cmu Λ cm) (cx κ cT) cw Kc C₂ κW) (cZ0 L R.ℓ Kc β₀) := by
      unfold kTh cLam0 cV0 cW0 cZ0 cbb cLam0
      have := kX_nonneg R.ℓ; have : (0 : ℝ) ≤ cM := Nat.cast_nonneg _
      positivity
    have : 0 ≤ cV0 R.ℓ β₀ := hV0
    positivity
  have hK4 : 0 ≤ K₀ ^ 4 := by positivity
  have hεσ : e + ε = (cE + 1) * ε := by rw [hed]; ring
  set dx := ‖(t j).2.2 - (t' j).2.2‖
  set dg := |(t j).1 - (t' j).1|
  set dμ := |(t j).2.1 - (t' j).2.1|
  have hdx : ‖(t' j).2.2 - (t j).2.2‖ = dx := norm_sub_rev _ _
  have hdg : |(t' j).1 - (t j).1| = dg := abs_sub_comm _ _
  have hdμ : |(t' j).2.1 - (t j).2.1| = dμ := abs_sub_comm _ _
  rw [hdx, hdg, hdμ] at LTK LTD hLG hLm
  have hdx0 : 0 ≤ dx := norm_nonneg _
  have hdg0 : 0 ≤ dg := abs_nonneg _
  have hdμ0 : 0 ≤ dμ := abs_nonneg _
  have hQ : 0 ≤ dx + dg + dμ + M := by positivity
  have hCL1 : (cE + 1) * CT₀ ≤ CL := by
    rw [hCLd]; have h1 : 0 ≤ (cE + 1) * (300 * K₀ ^ 4) := by positivity
    have h2 : 0 ≤ 500 * K₀ ^ 4 + 2 * K₀ := by positivity
    linarith only [h1, h2, show (cE + 1) * (300 * K₀ ^ 4 + CT₀) = (cE + 1) * (300 * K₀ ^ 4) +
      (cE + 1) * CT₀ by ring]
  have hCL2 : (cE + 1) * (300 * K₀ ^ 4) ≤ CL := by
    rw [hCLd]; have h1 : 0 ≤ (cE + 1) * CT₀ := by positivity
    have h2 : 0 ≤ 500 * K₀ ^ 4 + 2 * K₀ := by positivity
    linarith only [h1, h2, show (cE + 1) * (300 * K₀ ^ 4 + CT₀) = (cE + 1) * (300 * K₀ ^ 4) +
      (cE + 1) * CT₀ by ring]
  have hCL3 : 500 * K₀ ^ 4 ≤ CL := by
    rw [hCLd]; have h1 : 0 ≤ (cE + 1) * (300 * K₀ ^ 4 + CT₀) := by positivity
    have h2 : 0 ≤ 2 * K₀ := by positivity
    linarith only [h1, h2]
  have hCL4 : 2 * K₀ ≤ CL := by
    rw [hCLd]; have h1 : 0 ≤ (cE + 1) * (300 * K₀ ^ 4 + CT₀) := by positivity
    linarith only [h1, hK4]
  have hCL0 : 0 ≤ CL := le_trans (by positivity) hCL4
  have hTT : (e + ε) * CT₀ * (dx + dg + dμ + M) ≤ CL * ε * (dx + dg + dμ + M) := by
    rw [hεσ]
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCL1 hε0.le) hQ
    linarith only [this, show (cE + 1) * ε * CT₀ * (dx + dg + dμ + M) =
      (cE + 1) * CT₀ * ε * (dx + dg + dμ + M) by ring]
  have h200 : (e + ε) * (200 * K₀ ^ 4) ≤ CL * (ε + ϑ) := by
    rw [hεσ]
    have a := mul_le_mul_of_nonneg_right hCL2 hε0.le
    have b : (cE + 1) * ε * (200 * K₀ ^ 4) ≤ (cE + 1) * (300 * K₀ ^ 4) * ε := by
      have h0 : 0 ≤ (cE + 1) * ε * K₀ ^ 4 := by positivity
      linarith only [h0, show (cE + 1) * ε * (200 * K₀ ^ 4) = 200 * ((cE + 1) * ε * K₀ ^ 4) by ring,
        show (cE + 1) * (300 * K₀ ^ 4) * ε = 300 * ((cE + 1) * ε * K₀ ^ 4) by ring]
    have c := mul_nonneg hCL0 hϑ0
    linarith only [a, b, c, show CL * (ε + ϑ) = CL * ε + CL * ϑ by ring]
  have h300 : (e + ε) * (300 * K₀ ^ 4) ≤ CL * ε := by
    rw [hεσ]
    have a := mul_le_mul_of_nonneg_right hCL2 hε0.le
    linarith only [a, show (cE + 1) * ε * (300 * K₀ ^ 4) = (cE + 1) * (300 * K₀ ^ 4) * ε by ring]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [norm_sub_rev]; linarith only [LTK, hTT]
  · rw [norm_sub_rev]; linarith only [LTD, hTT]
  · have a1 := mul_le_mul_of_nonneg_right h200 hdg0
    have a2 := mul_le_mul_of_nonneg_right h200 hdμ0
    have a3 := mul_le_mul_of_nonneg_right hCL3 hdx0
    have a4 := mul_le_mul_of_nonneg_right h200 hM
    linarith only [hLG, a1, a2, a3, a4, show (1 + (e + ε) * (200 * K₀ ^ 4)) * dg =
      dg + (e + ε) * (200 * K₀ ^ 4) * dg by ring, show (1 + CL * (ε + ϑ)) * dg =
      dg + CL * (ε + ϑ) * dg by ring]
  · have b1 : 300 * K₀ ^ 4 ≤ CL := by linarith only [hCL3, hK4]
    have a1 := mul_le_mul_of_nonneg_right b1 (add_nonneg hdg0 hdx0)
    have a2 : (e + ε) * (300 * K₀ ^ 4) * dμ ≤ CL * (ε + ϑ) * dμ := by
      have h0 := mul_nonneg (mul_nonneg hCL0 hϑ0) hdμ0
      have h := mul_le_mul_of_nonneg_right h300 hdμ0
      linarith only [h0, h, show CL * (ε + ϑ) * dμ = CL * ε * dμ + CL * ϑ * dμ by ring]
    have a3 : ((e + ε) * (300 * K₀ ^ 4) + 2 * K₀ * ϑ) * M ≤ CL * (ε + ϑ) * M := by
      have h1 := mul_le_mul_of_nonneg_right hCL4 hϑ0
      have : (e + ε) * (300 * K₀ ^ 4) + 2 * K₀ * ϑ ≤ CL * (ε + ϑ) := by
        linarith only [h300, h1, show CL * (ε + ϑ) = CL * ε + CL * ϑ by ring]
      exact mul_le_mul_of_nonneg_right this hM
    linarith only [hLm, a1, a2, a3, show CL * (dg + dx) = CL * dg + CL * dx by ring]

end Pair

end

end Step2
