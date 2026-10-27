import Spin2.Gam.GamTopFull
import PtCorr2.Obs.ObsHistLast

/-!
# The last step: `ρ_N` relative to `β_{N_h+1}/|Z_{N_h+1}|`

At `j = N_h + 1 = N − 1` the map has no `Q` (no activity term in `ρ_N`, `gamRemG_last_split`), and
`ρ_N = ∑_Bε(e^{ℒ_{C_N}}𝒲^{obs}_{N_h+1}(B)_a) + β_{N_h+1}·ε(F_{C_N}(ψ̄_aψ_a, V'_N(Λ)_∅))`.

* The bulk factor: `V'_N(Λ)_∅ = V_{κ_N}(Λ) + const` (`VprLO_e_last`, `LastN.rawStepN_VN`), so
  `ε F = ν_N∑_xC_N(a,x)C_N(x,a) + (y_N + z_N)𝔩_{C_N}(a)` (`eps_FC_pbp_Vcoup`). On the torus at the
  last scale the sums run over `L^{2N}` points (`norm_sumCC_leT`, `norm_lfunC_leT`); with the final
  couplings of `GlueOut` (`|L^{2N}ν_N/Z_N|, |z_N/Z_N|, |y_N/Z_N| ≤ C_fǧ_{N_h}`) and
  `|Z_N| ≥ (7/8)|Z_{N_h+1}|`: `|ε F| ≤ C_fℓ⁴ǧ_{N_h}/|Z_{N_h+1}|` (`eps_bulk_last_le`).
* The `𝒲` term: `|∑_B…| ≤ c_BQ₁w` from the block bound `w` of `𝒲^{obs}_{N_h+1}`
  (`PtCorr2.eps_EthO_W_le`, `GoodCov2` of `C_N` at the field scale `s_{N_h+1}`).
* **`gamRemG_last_le`**: `|ρ_N| ≤ c_BQ₁w + |β_{N_h+1}|C_fℓ⁴ǧ_{N_h}/|Z_{N_h+1}|`.
-/

set_option linter.unusedSectionVars false

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs.SA

variable {L N : ℕ} [NeZero L]

/-! ### Covariance sums on the torus at the last scale -/

section Torus

variable {k : ℕ} {ℓC : ℝ} {C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ}

/-- A sum over the torus at the last scale: `|Λ| = L^{2N}`. -/
theorem norm_sum_top_le (hkN : k + 1 = N) (f : Lam 2 L N → ℂ) {M : ℝ} (hM : ∀ z, ‖f z‖ ≤ M) :
    ‖∑ z, f z‖ ≤ ((L : ℝ) ^ (k + 1)) ^ 2 * M := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  calc ‖∑ z, f z‖ ≤ ∑ z, ‖f z‖ := norm_sum_le _ _
    _ ≤ ∑ _z : Lam 2 L N, M := sum_le_sum fun z _ => hM z
    _ = (Fintype.card (Lam 2 L N) : ℝ) * M := by rw [sum_const, card_univ, nsmul_eq_mul]
    _ = ((L : ℝ) ^ (k + 1)) ^ 2 * M := by
        rw [show Fintype.card (Lam 2 L N) = (L ^ N) ^ 2 from FRD.card_torus, hkN]
        push_cast; ring

/-- `‖∑_xC(a,x)C(x,a)‖ ≤ L^{2N}ℓ_C⁴` at the last scale. -/
theorem norm_sumCC_leT (hC : GoodCov2 k ℓC C) (hkN : k + 1 = N) (a : Lam 2 L N) :
    ‖∑ x, C a x * C x a‖ ≤ ((L : ℝ) ^ (k + 1)) ^ 2 * (ℓC ^ 2 * ℓC ^ 2) := by
  refine norm_sum_top_le hkN _ fun z => ?_
  rw [norm_mul]
  exact mul_le_mul (Obs2.good_entry hC a z) (Obs2.good_entry hC z a) (norm_nonneg _)
    (by positivity)

/-- `|𝔩_C(a)| ≤ 2ℓ_C⁴` at the last scale. -/
theorem norm_lfunC_leT (hC : GoodCov2 k ℓC C) (hkN : k + 1 = N) (a : Lam 2 L N) :
    ‖Obs2.lfunC C a‖ ≤ 2 * ℓC ^ 4 := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hLk : (0 : ℝ) < (L : ℝ) ^ (k + 1) := by positivity
  set M := 2 * (ℓC ^ 2 / (L : ℝ) ^ (k + 1)) * (ℓC ^ 2 / (L : ℝ) ^ (k + 1)) with hMd
  have hi : ∀ i : Fin 2, ‖∑ z, (1 / 2 : ℂ) *
      (Obs2.gpX C C a (Sum.inl i) z + Obs2.gpX C C a (Sum.inr i) z)‖ ≤
      ((L : ℝ) ^ (k + 1)) ^ 2 * M := by
    intro i
    refine norm_sum_top_le hkN _ fun z => ?_
    rw [norm_mul]
    have e : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [e]
    have := (norm_add_le _ _).trans (add_le_add (Obs2.norm_gpX_le hC hC a (Sum.inl i) z)
      (Obs2.norm_gpX_le hC hC a (Sum.inr i) z))
    linarith
  have hX : ‖Obs2.lfunX C C a‖ ≤ 2 * (((L : ℝ) ^ (k + 1)) ^ 2 * M) := by
    unfold Obs2.lfunX
    refine (norm_sum_le _ _).trans ?_
    rw [Fin.sum_univ_two]
    linarith [hi 0, hi 1]
  have e2 : 2 * (((L : ℝ) ^ (k + 1)) ^ 2 * M) = 4 * ℓC ^ 4 := by
    rw [hMd]; field_simp; ring
  rw [e2, Obs2.lfunX_self, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num] at hX
  linarith

end Torus

/-! ### The bulk factor of the last step -/

section Bulk

/-- **`V'_N(Λ)_∅`** at the last step: `V_N(Λ) + (∑_Bu_N(B))·1`. -/
theorem VprLO_e_last (R : RGPar 2 L N) (j : ℕ) (st : RawSt 2 L N) (g μ : ℝ)
    (o : Obs2.ObsSt .two L N) (ho : o.IsObs) :
    (Obs2.VprLO j (LastN.stCovN R j st) (Obs2.fullV R j st g μ o) : SA .two (Lam 2 L N)).e =
      (LastN.VN j (LastN.stCovN R j st) (stVf R j st g μ) : Alg 2 L N) +
        (∑ b ∈ blockIdx (L := L) (N := N) j, LastN.upN (LastN.stCovN R j st) (stVf R j st g μ) b) •
          (1 : Alg 2 L N) := by
  have hb : ∀ b, (Obs2.VprO (LastN.stCovN R j st) (Obs2.fullV R j st g μ o) b :
      SA .two (Lam 2 L N)).e = (LastN.VpN (LastN.stCovN R j st) (stVf R j st g μ) b : Alg 2 L N) +
        LastN.upN (LastN.stCovN R j st) (stVf R j st g μ) b • (1 : Alg 2 L N) := by
    intro b
    rw [Obs2.VprO, (Obs2.EthO_comp _ _).1, Obs2.fullV]
    show expLC _ ((stVf R j st g μ b : Alg 2 L N) + ((o.V b : SA .two (Lam 2 L N)).e)) = _
    rw [Obs2.e_eq_zero_of_bulk (ho.V b), add_zero, LastN.VpN, AddSubgroupClass.coe_sub,
      Subalgebra.coe_algebraMap, Vpr, coe_EthE, Algebra.algebraMap_eq_smul_one, sub_add_cancel]
  rw [Obs2.VprLO, AddSubmonoidClass.coe_finsetSum, sum_e, sum_congr rfl fun b _ => hb b,
    sum_add_distrib, ← sum_smul, LastN.VN, AddSubmonoidClass.coe_finsetSum]

set_option maxHeartbeats 1000000 in
/-- **The bulk factor of the last step**:
`|ε F_{C_N}(ψ̄_aψ_a, V_{κ_N}(Λ))| ≤ C_fℓ⁴ǧ_{N_h}/|Z_{N_h+1}|` (final couplings from `GlueOut`). -/
theorem eps_bulk_last_le (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {Nh : ℕ}
    (hNh : Nh + 2 = N) (hV : ∀ i < Nh, ValidAt R i) (hVL : ValidAtL R Nh)
    (hVN : LastN.ValidLast R (Nh + 1)) {Cf : ℝ} (t : Hist.Seq (Xs R)) (hG : GlueOut R Nh Cf t)
    (a : Lam 2 L N) :
    ‖ε (FC (LastN.stCovN R (Nh + 1) (histOut R Nh t).st) (LocObs.pbp a)
        (Vcoup (lastOut R Nh t).κ univ))‖ ≤
      Cf * R.ℓ ^ 4 * (t Nh).1 / ‖(histOut R Nh t).st.Z‖ := by
  obtain ⟨-, ⟨hz, hy, hnu, -⟩⟩ := hG
  set st := (histOut R Nh t).st with hst
  set out := lastOut R Nh t with hout
  set g := (t Nh).1
  have H : RawInv R (Nh + 1) st := rawInv_histU R hV hVL t (Nh + 1) le_rfl
  have hC := (LastN.covN hVN H).1
  have hρ0 : 0 ≤ R.ρ := hVL.2.2.2.2.1
  have hρ8 : R.ρ ≤ 1 / 8 := hVL.2.2.2.2.2.1
  have hZ : st.Z ≠ 0 := H.Z_ne_zero (by linarith)
  have hZ1 : 0 < ‖st.Z‖ := norm_pos_iff.2 hZ
  have hZN : 7 / 8 * ‖st.Z‖ ≤ ‖stZ' R st‖ := norm_stZ'_ge R (j := 0) st hρ0 hρ8
  have hZp : 0 < ‖stZ' R st‖ := by linarith
  have hoZ : out.Z = stZ' R st := rfl
  rw [hoZ] at hz hy hnu
  set Zn := ‖stZ' R st‖ with hZn
  set c := R.ℓ ^ 2 / (16 * Zn) with hc
  have hc0 : 0 ≤ c := by positivity
  have hc2 : (fscale (stZ' R st) * R.ℓ / 4) ^ 2 = c := by
    rw [fscale_sq, hc, ← hZn]; field_simp
  have hT := norm_sumCC_leT hC (show Nh + 1 + 1 = N by omega) a
  have hlf := norm_lfunC_leT hC (show Nh + 1 + 1 = N by omega) a
  rw [hc2] at hT
  rw [show (fscale (stZ' R st) * R.ℓ / 4) ^ 4 = ((fscale (stZ' R st) * R.ℓ / 4) ^ 2) ^ 2 by ring,
    hc2] at hlf
  have hCg : 0 ≤ Cf * g := (norm_nonneg _).trans hz
  set X := ((L : ℝ) ^ (Nh + 1 + 1)) ^ 2 with hX
  have hnu' : X * ‖out.κ.nu‖ ≤ Cf * g * Zn := by
    have e : ‖(L : ℂ) ^ (2 * (Nh + 1 + 1)) * out.κ.nu / stZ' R st‖ = X * ‖out.κ.nu‖ / Zn := by
      rw [norm_div, norm_mul, norm_pow, Complex.norm_natCast, hX, ← pow_mul, mul_comm 2]
    rw [e, div_le_iff₀ hZp] at hnu
    exact hnu
  have hyz : ‖out.κ.y + out.κ.z‖ ≤ 2 * (Cf * g) * Zn := by
    have ey : ‖out.κ.y‖ = ‖out.κ.y / stZ' R st‖ * Zn := by
      rw [norm_div, hZn, div_mul_cancel₀ _ hZp.ne']
    have ez : ‖out.κ.z‖ = ‖out.κ.z / stZ' R st‖ * Zn := by
      rw [norm_div, hZn, div_mul_cancel₀ _ hZp.ne']
    have h1 := mul_le_mul_of_nonneg_right hy hZp.le
    have h2 := mul_le_mul_of_nonneg_right hz hZp.le
    refine (norm_add_le _ _).trans ?_
    rw [ey, ez]
    linarith
  rw [Obs2.eps_FC_pbp_Vcoup]
  have hX0 : 0 ≤ X := by positivity
  calc ‖out.κ.nu * ∑ x, LastN.stCovN R (Nh + 1) st a x * LastN.stCovN R (Nh + 1) st x a +
        (out.κ.y + out.κ.z) * Obs2.lfunC (LastN.stCovN R (Nh + 1) st) a‖
      ≤ ‖out.κ.nu‖ * (X * (c * c)) + (2 * (Cf * g) * Zn) * (2 * c ^ 2) := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left hT (norm_nonneg _))
          (mul_le_mul hyz hlf (norm_nonneg _) (by positivity))
    _ = (X * ‖out.κ.nu‖) * (c * c) + 4 * (Cf * g) * Zn * c ^ 2 := by ring
    _ ≤ (Cf * g * Zn) * (c * c) + 4 * (Cf * g) * Zn * c ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_right hnu' (by positivity)) le_rfl
    _ = 5 * (Cf * g) * R.ℓ ^ 4 / (256 * Zn) := by
        rw [hc]; field_simp; ring
    _ ≤ Cf * R.ℓ ^ 4 * g / ‖st.Z‖ := by
        rw [div_le_div_iff₀ (by positivity) hZ1]
        have hl4 : 0 ≤ Cf * g * R.ℓ ^ 4 := mul_nonneg hCg (by positivity)
        have := mul_le_mul_of_nonneg_left hZN hl4
        nlinarith

set_option maxHeartbeats 2000000 in
/-- **`ρ_N` of the last step** (any point configuration `P`, initial vertex `V`): from the block
bound `w` of `𝒲^{obs}_{N_h+1}` and `GlueOut`,
`|ρ_N| ≤ c_BQ₁w + |β_{N_h+1}|·C_fℓ⁴ǧ_{N_h}/|Z_{N_h+1}|`. -/
theorem gamRemG_last_le (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {Nh : ℕ}
    (hNh : Nh + 2 = N) (hV : ∀ i < Nh, ValidAt R i) (hVL : ValidAtL R Nh)
    (hVN : LastN.ValidLast R (Nh + 1)) (hLp : pauliL0 2 ≤ L) (P : Obs2.ObsPts 2 L N)
    (V : Obs2.OCoup .two) {Cf w : ℝ} (t : Hist.Seq (Xs R)) (hG : GlueOut R Nh Cf t)
    (hw : 0 ≤ w) (hW : WbHc R P (Obs2.obsInit .two V P) t (Nh + 1) w) :
    ‖Obs2.gamRemG P (Nh + 1) (LastN.stCovN R (Nh + 1) (histOut R Nh t).st)
        (Obs2.fullV R (Nh + 1) (histOut R Nh t).st (histOut R Nh t).g.re (histOut R Nh t).nu.re
          (Obs2.obsHist R P (Obs2.obsInit .two V P) (Nh + 1) t))
        (Obs2.fullW (histOut R Nh t).st (histOut R Nh t).D
          (Obs2.obsHist R P (Obs2.obsInit .two V P) (Nh + 1) t))
        (Obs2.fullK R (Nh + 1) (histOut R Nh t).st (histOut R Nh t).K
          (Obs2.obsHist R P (Obs2.obsInit .two V P) (Nh + 1) t))‖ ≤
      cBn * (Q1 2 * w) + ‖Obs2.betaTot2 (L := L) (N := N) (Nh + 1)
        (Obs2.histVO2 R P (Obs2.obsInit .two V P) t (Nh + 1))‖ *
        (Cf * R.ℓ ^ 4 * (t Nh).1 / ‖(histOut R Nh t).st.Z‖) := by
  have hℓ : 0 < R.ℓ := Fact.out
  set o₀ := Obs2.obsInit .two V P with ho₀
  set o := Obs2.obsHist R P o₀ (Nh + 1) t with hod
  set st := (histOut R Nh t).st with hst
  have ho : o.IsObs := Obs2.obsHist_isObs R P o₀ (Obs2.obsInit_isObs .two V P) (Nh + 1) t
  have hform : ∀ b, Obs2.Loc2Form P.a (Obs2.fullV R (Nh + 1) st (histOut R Nh t).g.re
      (histOut R Nh t).nu.re o b : SA .two (Lam 2 L N)).a := by
    intro b
    have h := Obs2.obsHist_hform2 R P o₀ t (fun b' => Obs2.obsInit_two_form P V b') (Nh + 1) b
    rw [Obs2.histVO2_a] at h
    rw [show (Obs2.fullV R (Nh + 1) st (histOut R Nh t).g.re (histOut R Nh t).nu.re o b :
      SA .two (Lam 2 L N)).a = (o.V b : SA .two (Lam 2 L N)).a from Obs2.emb_add_cmp true _ _]
    exact h
  have hβ : Obs2.betaTot2 (L := L) (N := N) (Nh + 1)
      (Obs2.fullV R (Nh + 1) st (histOut R Nh t).g.re (histOut R Nh t).nu.re o) =
      Obs2.betaTot2 (L := L) (N := N) (Nh + 1) (Obs2.histVO2 R P o₀ t (Nh + 1)) := by
    unfold Obs2.betaTot2
    refine sum_congr rfl fun b _ => ?_
    rw [Obs2.histVO2_a]
    congr 1
    exact Obs2.emb_add_cmp true _ _
  rw [PtCorr2.gamRemG_last_split P (by omega) _ _ _ _ hform, hβ,
    VprLO_e_last R (Nh + 1) st _ _ o ho]
  -- the covariance
  have H : RawInv R (Nh + 1) st := rawInv_histU R hV hVL t (Nh + 1) le_rfl
  obtain ⟨hC0, -, hCs, hCsym⟩ := LastN.covN hVN H
  have hVNe : (LastN.VN (Nh + 1) (LastN.stCovN R (Nh + 1) st)
      (stVf R (Nh + 1) st (histOut R Nh t).g.re (histOut R Nh t).nu.re) : Alg 2 L N) =
      Vcoup (lastOut R Nh t).κ univ :=
    LastN.rawStepN_VN R (Nh + 1) st _ _ (histOut R Nh t).D (histOut R Nh t).K hCs hCsym
  rw [hVNe, FC_add_right, FC_smul_right, Obs2.FC_one_right, smul_zero, add_zero]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · -- the `𝒲` term
    have hρ0 : 0 ≤ R.ρ := hVL.2.2.2.2.1
    have hρ8 : R.ρ ≤ 1 / 8 := hVL.2.2.2.2.2.1
    have hZ : st.Z ≠ 0 := H.Z_ne_zero (by linarith)
    have hζ8 : ‖stZeta R st‖ ≤ 1 / 8 := (absorb_le R hρ0 _ _).trans hρ8
    have hsc := scale_ok hZ hζ8 hℓ
    have hs' : 0 < fscale (stZ' R st) * R.ℓ :=
      mul_pos (fscale_pos (mul_ne_zero hZ (one_add_ne_zero (by linarith)))) hℓ
    have hs : 0 < histS R (Nh + 1) t := mul_pos (fscale_pos hZ) hℓ
    have hmono : fscale (stZ' R st) * R.ℓ / 4 ≤ histS R (Nh + 1) t := by
      have e : stZ' R st = st.Z * (1 + stZeta R st) := rfl
      rw [e] at hs' ⊢
      show _ ≤ fscale st.Z * R.ℓ
      linarith
    have hC := hC0.mono hmono
    have hval := hist_validL R hV hVL t
    have hloc := obsLocInv_hist R P o₀ (obsLocInv_init .two V P) t (Nh + 1)
      fun i hi => hval i (by omega)
    exact eps_EthO_W_le P (by omega) hLp hs hC o hloc st (histOut R Nh t).D hw hW
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (eps_bulk_last_le R hNh hV hVL hVN t hG P.a) (norm_nonneg _)

end Bulk

/-! ### Along the trajectory -/

/-- `|β_{N_h}| ≤ 2|β_{N_h+1}|` from `β_{N_h+1} = β_{N_h}(1 − 𝔫) − err` and `Case2TopStep`. -/
theorem beta_step_ge {β n e : ℂ} (hn : ‖n‖ ≤ 1 / 8) (he : ‖e‖ ≤ 1 / 8 * ‖β * (1 - n)‖) :
    ‖β‖ ≤ 2 * ‖β * (1 - n) - e‖ := by
  have h1 : 7 / 8 ≤ ‖1 - n‖ := by
    have := norm_sub_norm_le (1 : ℂ) n
    rw [norm_one] at this; linarith
  have h2 : 7 / 8 * ‖β‖ ≤ ‖β * (1 - n)‖ := by
    rw [norm_mul, mul_comm (7 / 8 : ℝ)]; exact mul_le_mul_of_nonneg_left h1 (norm_nonneg β)
  have h3 := norm_sub_norm_le (β * (1 - n)) e
  have h4 := norm_nonneg β
  linarith

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- `ρ_N` for any point configuration `P` (pair vertex `zV b`): `gamRemN = gamRemNP (ptsX x)`,
`gamRemNS = gamRemNP (ptsS x)`. -/
def gamRemNP (P : Obs2.ObsPts 2 L N) (Nh : ℕ) (m b μ₀ : ℝ) : ℂ :=
  Obs2.gamRemG P (Nh + 1)
    (LastN.stCovN (R.withMsq m) (Nh + 1)
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st)
    (Obs2.fullV (R.withMsq m) (Nh + 1)
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).g.re
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).nu.re
      (Obs2.obsHist (R.withMsq m) P (Obs2.obsInit .two (zV b) P) (Nh + 1)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
    (Obs2.fullW (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).D
      (Obs2.obsHist (R.withMsq m) P (Obs2.obsInit .two (zV b) P) (Nh + 1)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
    (Obs2.fullK (R.withMsq m) (Nh + 1)
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).K
      (Obs2.obsHist (R.withMsq m) P (Obs2.obsInit .two (zV b) P) (Nh + 1)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))

theorem gamRemN_eq_P (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) :
    gamRemN R Nh m b μ₀ x = gamRemNP R (ptsX x) Nh m b μ₀ := rfl

set_option maxHeartbeats 2000000 in
/-- **`ρ_N` relative to `β_{N_h+1}/|Z_{N_h+1}|`** along one trajectory: from the block bound
`c_Ws_{N_h}²|β_{N_h}|` of `𝒲^{obs}_{N_h+1}`, `GlueOut`, `ValidLast` and `Case2TopStep`,
`|ρ_N| ≤ (2c_BQ₁c_W(9/8)ℓ² + C_fℓ⁴)|β_{N_h+1}|/|Z_{N_h+1}|`. -/
theorem gamRemNP_le {Nh : ℕ} (hNh : Nh + 2 = N) {m b μ₀ Cf cW : ℝ}
    (hV : ∀ i < Nh, ValidAt (R.withMsq m) i) (hVL : ValidAtL (R.withMsq m) Nh)
    (hVN : LastN.ValidLast (R.withMsq m) (Nh + 1)) (hLp : pauliL0 2 ≤ L)
    (P : Obs2.ObsPts 2 L N)
    (hG : GlueOut (R.withMsq m) Nh Cf (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) (hCf : 0 ≤ Cf)
    (hg1 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 ≤ 1) (hcW : 0 ≤ cW)
    (hW : WbHc (R.withMsq m) P (Obs2.obsInit .two (zV b) P) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
      (Nh + 1) (cW * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
        ‖bt2 R P (zV b) m b μ₀ Nh‖))
    (htop : Case2TopStep R P (zV b) Nh m b μ₀) :
    ‖gamRemNP R P Nh m b μ₀‖ ≤ (2 * (cBn * Q1 2 * cW * (9 / 8 * R.ℓ ^ 2)) + Cf * R.ℓ ^ 4) *
      ‖bt2 R P (zV b) m b μ₀ (Nh + 1)‖ * zInvT R Nh m b μ₀ := by
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  set R' := R.withMsq m with hR'
  have hρ0 : 0 ≤ R'.ρ := hVL.2.2.2.2.1
  have hρ8 : R'.ρ ≤ 1 / 8 := hVL.2.2.2.2.2.1
  set B0 := ‖bt2 R P (zV b) m b μ₀ Nh‖ with hB0
  set B1 := ‖bt2 R P (zV b) m b μ₀ (Nh + 1)‖ with hB1
  set S2 := histS R' Nh t ^ 2 with hS2
  set Zi := zInvT R Nh m b μ₀ with hZi
  have hw0 : 0 ≤ cW * S2 * B0 := by positivity
  have h := gamRemG_last_le R' hNh hV hVL hVN hLp P (zV b) t hG hw0 hW
  have eZ : ‖(histOut R' Nh t).st.Z‖ = zH R' t (Nh + 1) := rfl
  have eB : ‖Obs2.betaTot2 (L := L) (N := N) (Nh + 1)
      (Obs2.histVO2 R' P (Obs2.obsInit .two (zV b) P) t (Nh + 1))‖ = B1 := rfl
  have eℓ : R'.ℓ = R.ℓ := rfl
  rw [eZ, eB, eℓ] at h
  have hZp : 0 < zH R' t (Nh + 1) := zH_pos R' hρ0 hρ8 t (Nh + 1)
  have eZi : Zi = (zH R' t (Nh + 1))⁻¹ := rfl
  have hZi0 : 0 ≤ Zi := by rw [eZi]; exact inv_nonneg.2 hZp.le
  have hS : S2 ≤ 9 / 8 * R.ℓ ^ 2 * Zi := histS_sq_le_z R' t Nh hρ0 hρ8
  -- `β_{N_h} ≤ 2β_{N_h+1}`
  have hflow := bt2_flow R P (zV b) (Nh := Nh + 1) (by omega) m b μ₀ (k := Nh) (by omega)
  have hBB : B0 ≤ 2 * B1 := by
    rw [hB0, hB1, hflow]; exact beta_step_ge htop.1 htop.2
  have hQ : 0 ≤ Q1 2 := by have := one_le_Q1 (d := 2) (by norm_num); linarith
  have hcB : (0 : ℝ) ≤ cBn := Nat.cast_nonneg _
  have hK : 0 ≤ (cBn : ℝ) * Q1 2 * cW := by positivity
  have t1 : (cBn : ℝ) * (Q1 2 * (cW * S2 * B0)) ≤
      (cBn * Q1 2 * cW) * (9 / 8 * R.ℓ ^ 2 * Zi) * (2 * B1) := by
    have := mul_le_mul hS hBB (norm_nonneg _) (by positivity)
    calc (cBn : ℝ) * (Q1 2 * (cW * S2 * B0)) = (cBn * Q1 2 * cW) * (S2 * B0) := by ring
      _ ≤ (cBn * Q1 2 * cW) * ((9 / 8 * R.ℓ ^ 2 * Zi) * (2 * B1)) :=
          mul_le_mul_of_nonneg_left this hK
      _ = _ := by ring
  have t2 : B1 * (Cf * R.ℓ ^ 4 * (t Nh).1 / zH R' t (Nh + 1)) ≤ B1 * (Cf * R.ℓ ^ 4) * Zi := by
    rw [eZi, div_eq_mul_inv, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_right (by positivity) hg1) (norm_nonneg _)) (inv_nonneg.2 hZp.le)
  exact h.trans ((add_le_add t1 t2).trans (le_of_eq (by ring)))

end Traj

end

end Spin2
