import Spin2.Cont.ContZab2
import PtCorr2.Cont.ContZab1

set_option autoImplicit false

/-!
# B3, T6, route (c): `Z_{ab}`, the `ab` activity of `δ = pl2Delta` at `ms`, in any weight `wM(M_a, M_b)`

`δ.K(X)_{ab} = o₁.K(X)_{ab} + corr(X)_{ab} − o₂.K(X)_{ab}` (`zab_delta_ab_eq`), `o₁`, `o₂` the
pair histories of `(y − x, y)` and `(0, y)` at `ms`, `corr` the `rrSt` correction.

* the two pair histories: `zab_sizes` in their natural weights at `ms`, converted
  (`zab_wab_conv`: `w_{ab}(M_a, M_b) = (M'_aM'_b/(M_aM_b))·w_{ab}(M'_a, M'_b)`);
* **item (b)**, the correction: `zab_corr_ab_le` in the `σ_b` weight `wB(pM(ptsS y)_{ms})` with
  `‖I'(B)‖_{wB} ≤ ι_Z = e^{7/2}(2 + 2c_W)` (`oTj_inI_le` for `rrSt o₁`: `‖V♭+Δ‖ ≤ 3/2`,
  `‖V^{o₁}(B) − rrD(B)‖_{wB} ≤ 2` since `rrD` is pure `σ_a`, `‖𝒲‖_{wB} ≤ 1 + 2c_W`), the
  regulator `A^{|𝓑(W)|}‖(K♭ + o₁.K)(W)‖_{wB} ≤ A⁴(c_x(cε)³ + 8B(cε)²(2c_W)) ≤ 1` (`kabCond`)
  and `∑_B T(β_B(ψ̄_aψ_a − ψ̄_0ψ_0)) ≤ pM(P₁)_{ms}·4|y−x|_∞/L^{ms}` (`reloc_coupling`,
  `∑|β_B| ≤ shA2 ≤ 2|β^{P₁}_{ms}|`).

**`MasterFacts.zab_Z`**: `A^{(|𝓑(X)|−4)_+}w_{ab}T(δ.K(X)_{ab}) ≤ zabZ`, with
`zabZ = ρ₁(c_{ab}r(2c_W)² + 4|y−x|_∞L^{−ms}ι_ZA) + ρ₂c_{ab}r(2c_W)²`,
`ρ_i = pM(P_i)_{ms}pM(ptsS y)_{ms}/(M_aM_b)`.
-/

set_option linter.unusedSectionVars false

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs FRD Flow2 Flow2.Hist Obs2 ENNReal Step2.D2

variable {L : ℕ} [NeZero L]

/-- The block constant of the correction, `ι_Z = e^{7/2}(2 + 2c_W)`. -/
def zabIota (cW : ℝ) : ℝ := Real.exp (7 / 2) * (2 + 2 * cW)

/-- **The conversion of the `ab` weight.** -/
theorem zab_wab_conv {a s Ma Mb : ℝ} (ha : 0 < a) (hs : 0 < s) (hMa : 0 < Ma) (hMb : 0 < Mb) :
    (wM Ma Mb).ab = ENNReal.ofReal (a * s / (Ma * Mb)) * (wM a s).ab := by
  show ENNReal.ofReal Ma⁻¹ * ENNReal.ofReal Mb⁻¹ =
    ENNReal.ofReal (a * s / (Ma * Mb)) * (ENNReal.ofReal a⁻¹ * ENNReal.ofReal s⁻¹)
  rw [← ENNReal.ofReal_mul (inv_nonneg.2 hMa.le), ← ENNReal.ofReal_mul (inv_nonneg.2 ha.le),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

/-- The explicit bound `Z_{ab}` in the weight `wM(M_a, M_b)`. -/
def zabZ (M : MasterFacts L) {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (m b μ₀ : ℝ) (x y : Lam 2 L N) (ms : ℕ) (Ma Mb : ℝ) : ℝ :=
  pM (R.withMsq m) (pl2Pts x y) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ms *
      pM (R.withMsq m) (ptsS y) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ms / (Ma * Mb) *
    (M.k2cab * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ ms).1) * (2 * M.core.cWo) ^ 2 +
      4 * supNorm (y - x) / (L : ℝ) ^ ms * zabIota M.core.cWo * M.core.A) +
  pM (R.withMsq m) (ptsX y) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ms *
      pM (R.withMsq m) (ptsS y) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ms / (Ma * Mb) *
    (M.k2cab * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ ms).1) * (2 * M.core.cWo) ^ 2)

namespace MasterFacts

variable (M : MasterFacts L)

set_option maxHeartbeats 16000000 in
/-- **`Z_{ab}`: the `ab` activity of the pair-difference datum at `ms`** in any weight
`wM(M_a, M_b)` (both pair histories and the `rrSt` correction). -/
theorem zab_Z (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN3 : 3 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ)
    (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    (x y : Lam 2 L N) {ms : ℕ} (hms0 : 0 < ms) (hms : ms < Nh)
    (hmx : ms < Obs.coal L (0 : Lam 2 L N) x) (hmy : ms < Obs.coal L (0 : Lam 2 L N) y)
    {Ma Mb : ℝ} (hMa : 0 < Ma) (hMb : 0 < Mb) :
    ∀ X, IsConn ms X → ENNReal.ofReal ((R.withMsq m).A ^ (nb ms X - 2 ^ 2)) *
      ((wM Ma Mb).ab *
        Tj 2 (L : ℝ) ms (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          ((pl2Delta R m b μ₀ x y ms).K X : SA .two (Lam 2 L N)).ab) ≤
      ENNReal.ofReal (zabZ M R m b μ₀ x y ms Ma Mb) := by
  intro X hX
  have hN2 : 2 ≤ N := by omega
  have hNh0 : 0 < Nh := by omega
  have hb0 : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hmu : Obs2.OCoup2.mua (zV0 b) ≠ 0 := zV_mua_ne hb0
  -- the two pair histories at `ms`
  have hc1 : Obs.coal L (pl2Pts x y).a (pl2Pts x y).b = Obs.coal L (0 : Lam 2 L N) x := by
    show Nat.log L (2 * supNorm (y - x - y)) = Nat.log L (2 * supNorm (0 - x))
    rw [show y - x - y = -x by abel, zero_sub]
  obtain ⟨hp1, hq1, hK1ab, hK1o, hV1o, hW1o⟩ := M.zab_sizes N R hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm
    b μ₀ hD (pl2Pts x y) (n := ms) hms0 hms.le (by rw [hc1]; exact hmx)
  obtain ⟨hp2, hq2, hK2ab, -, -, -⟩ := M.zab_sizes N R hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm
    b μ₀ hD (ptsX y) (n := ms) hms0 hms.le hmy
  have eb1 : (pl2Pts x y).b = y := rfl
  have eb2 : (ptsX y).b = y := rfl
  rw [eb1] at hq1 hK1ab hK1o hV1o hW1o
  rw [eb2] at hq2 hK2ab
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  set R' := R.withMsq m with hR'
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8, -, hCN⟩ := id M.core.hC2
  obtain ⟨H, hm1, F1⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm
  obtain ⟨hV, hVL⟩ := (hCN N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm
  have hRA' : R'.A = M.core.A := hRA
  have hρ0' : 0 ≤ R'.ρ := by rw [show R'.ρ = M.core.ρ from hRρ]; exact hρpos.le
  have hρ8' : R'.ρ ≤ 1 / 8 := by rw [show R'.ρ = M.core.ρ from hRρ]; exact hρ8
  have hcR : cR R' ((L : ℝ) ^ 2) M.core.cm M.core.C₂x = M.core.c := by
    rw [M.core.hc]; exact cR_congr (show R.ℓ = M.core.ℓ from hRℓ) _ _ _
  have hSB' : StepBounds L R'.A M.core.C₀x M.core.ηx M.core.εsx M.core.CKx M.core.C₂x M.core.CDx
      M.core.Cqx M.core.Clx M.core.cSx := by rw [hRA']; exact M.core.hSBx
  have hβ2 := betaL_ge (show 8 ≤ L by have := M.core.hL49; omega)
  have hβ0 : 0 ≤ betaL L := by linarith
  have hc2 : 2 ≤ M.core.c := hcR ▸ two_le_cR R' H.hcmu H.hC₂
  have hcW : 1 ≤ M.core.cWo := M.core.consts_nonneg.2.2.2.2.2.1
  have hBk : 0 ≤ M.core.Bk := M.core.consts_nonneg.2.2.2.2.2.2.1
  have hA2 : 2 ≤ M.core.A := M.core.hA2
  have hA1 : 1 ≤ R'.A := by rw [hRA']; linarith
  have hcε : M.core.c * M.core.ε ≤ 1 := M.core.hcε
  have hs : 0 < histS R' ms t := histS_pos' R' hρ0' hρ8' t ms
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  obtain ⟨hg, hgε, -, hxg⟩ := (inDh_rg_of_D R' F1 hD Nh le_rfl).1 ms hms.le
  have hgc : M.core.c * (t ms).1 ≤ M.core.c * M.core.ε :=
    mul_le_mul_of_nonneg_left hgε (by linarith)
  have hr0 : 0 ≤ M.core.c * (t ms).1 := mul_nonneg (by linarith) hg.le
  have hr1 : M.core.c * (t ms).1 ≤ 1 := hgc.trans hcε
  have hcab0 := M.k2cab_nonneg
  set a1 := pM R' (pl2Pts x y) (zV0 b) t ms with ha1
  set a2 := pM R' (ptsX y) (zV0 b) t ms with ha2
  set sS := pM R' (ptsS y) (zV0 b) t ms with hsS
  have hA0 : 0 ≤ R'.A := by linarith
  have ha10 : 0 ≤ a1 := hp1.le
  have ha20 : 0 ≤ a2 := hp2.le
  have hsS0 : 0 ≤ sS := hq1.le
  have hMM : 0 < Ma * Mb := mul_pos hMa hMb
  have hd0 : 0 ≤ 4 * (supNorm (y - x) : ℝ) / (L : ℝ) ^ ms :=
    div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (pow_pos hL0 _).le
  have hι0 : 0 ≤ zabIota M.core.cWo := mul_nonneg (Real.exp_pos _).le (by linarith)
  -- the step data at `ms`
  set st := rawHist R' ms t with hst
  set Dd := rawD R' st.u (t ms).2.2 with hDd
  set Kb := rawK R' st.u (t ms).2.2 with hKb
  set o₁ := pl2O R m b μ₀ (pl2Pts x y) ms with ho₁
  set o₂ := pl2O R m b μ₀ (ptsX y) ms with ho₂
  set β := pl2Beta o₁ with hβd
  have hδ : pl2Delta R m b μ₀ x y ms = plDiffSt (rrSt R' ms st (t ms).1 (t ms).2.1 Dd Kb
      (pl2Pts x y).a (ptsX y).a β o₁) o₂ := rfl
  have he := zab_delta_ab_eq R' ms st (t ms).1 (t ms).2.1 Dd Kb (pl2Pts x y).a (ptsX y).a β o₁ o₂ X
  rw [← hδ] at he
  rw [he]
  have hO₁ : o₁.IsObs := obsHist_isObs R' (pl2Pts x y) _ (obsInit_isObs .two _ _) ms t
  -- the correction
  have hbulk := inV_fullW_bulk_le R' hSB' hV hm1 hβ0 (by norm_num : (1 / 2 : ℝ) ≤ 1) H hρ0' t ms
    hms.le (inDh_rg_of_D R' F1 hD ms hms.le) (hV ms hms).toValidCore (hm1 ms hms)
    (by rw [hcR]; exact hcε)
  have hwB : ∀ F : OE .two (Lam 2 L N), oTo (wB sS) ms (histS R' ms t) F ≤
      oTo (wM a1 sS) ms (histS R' ms t) F := fun F =>
    (zab_oTo_wB_le a1 sS ms _ F).trans (by rw [← wOne_wM]; exact oTo_one_le _ _ _ _)
  have hrrB : ∀ q, oTo (wB sS) ms (histS R' ms t) (rrD (pl2Pts x y).a (ptsX y).a β q) = 0 := by
    intro q
    rw [oTo_eq_comp (show (wB sS).ab = 0 from rfl)]
    simp [wB, Step.Tj_zero]
  have hIZ : ∀ q ∈ blocks ms X, oTj 2 L (wB sS) ms (histS R' ms t)
      ((IbO (fun b' => emb (stVf R' ms st (t ms).1 (t ms).2.1 b' + stDelta R' ms st b') +
        (o₁.V b' - rrD (pl2Pts x y).a (ptsX y).a β b')) (fullW st Dd o₁) q :
          OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)) ≤
        ENNReal.ofReal (zabIota M.core.cWo) := by
    intro q hq
    have hq' : q ∈ blockIdx (L := L) (N := N) ms := blocks_subset_blockIdx X hq
    have hOr := rrSt_isObs R' ms st (t ms).1 (t ms).2.1 Dd Kb (pl2Pts x y).a (ptsX y).a β hO₁
    have hv : oTj 2 L (wB sS) ms (histS R' ms t)
        (inV R' ms st (t ms).1 (t ms).2.1 (rrSt R' ms st (t ms).1 (t ms).2.1 Dd Kb (pl2Pts x y).a
          (ptsX y).a β o₁) q : SA .two (Lam 2 L N)) ≤ ENNReal.ofReal (7 / 2) := by
      refine (oTj_emb_add_le (wB sS) ms _ _ _ (hOr.V q)).trans ?_
      have h1 := hbulk.1 q hq'
      have h2 : oTo (wB sS) ms (histS R' ms t) (o₁.V q - rrD (pl2Pts x y).a (ptsX y).a β q) ≤
          ENNReal.ofReal 2 := by
        refine (oTo_sub_le _ _ _ _ _).trans ?_
        rw [hrrB q, add_zero]
        exact (hwB _).trans (hV1o q hq')
      refine (add_le_add h1 h2).trans ?_
      rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
      norm_num
    have hf : oTj 2 L (wB sS) ms (histS R' ms t)
        (fullW st Dd (rrSt R' ms st (t ms).1 (t ms).2.1 Dd Kb (pl2Pts x y).a
          (ptsX y).a β o₁) q : SA .two (Lam 2 L N)) ≤ ENNReal.ofReal (1 + 2 * M.core.cWo) := by
      refine (oTj_emb_add_le (wB sS) ms _ _ _ (hO₁.W q)).trans ?_
      have h1 := hbulk.2 q hq'
      have h2 : oTo (wB sS) ms (histS R' ms t) (o₁.W q) ≤ ENNReal.ofReal (2 * M.core.cWo) := by
        refine ((hwB _).trans (hW1o q hq')).trans (ENNReal.ofReal_le_ofReal ?_)
        have := mul_le_mul_of_nonneg_right hr1 (by linarith : (0 : ℝ) ≤ 2 * M.core.cWo)
        linarith
      refine (add_le_add h1 h2).trans ?_
      rw [← ENNReal.ofReal_add (by norm_num) (by linarith)]
    have := oTj_inI_le R' ms st (t ms).1 (t ms).2.1 Dd _ hOr (wB sS) (wB_sub sS) hs q
      (by norm_num : (0 : ℝ) ≤ 7 / 2) (by linarith : (0 : ℝ) ≤ 1 + 2 * M.core.cWo) hv hf
    refine this.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    unfold zabIota; ring
  -- the regulator
  obtain ⟨C₁', hC₁', h5⟩ : ∃ C₁' : ℝ, 0 ≤ C₁' ∧ M.core.A ^ 4 *
      (cx M.core.κ M.core.cT * (M.core.c * M.core.ε) ^ 3 +
        8 * M.core.Bk * (M.core.c * M.core.ε) ^ 2 * (2 * M.core.cWo) +
        10 * kB2 (kθ0 L M.core.A M.core.C₀u M.core.ηu) C₁' (cx M.core.κ M.core.cT)
          (8 * M.core.Bk) * (M.core.c * M.core.ε) * (2 * M.core.cWo) ^ 2) ≤ 1 := by
    obtain ⟨-, C₁', -, hC, -, -, -, -, -, h⟩ := M.core.hkab
    exact ⟨C₁', hC, h⟩
  have hcx : 0 ≤ cx M.core.κ M.core.cT := H.hcx
  have hB20 : 0 ≤ kB2 (kθ0 L M.core.A M.core.C₀u M.core.ηu) C₁' (cx M.core.κ M.core.cT)
      (8 * M.core.Bk) := by
    have hθ : 0 ≤ kθ0 L M.core.A M.core.C₀u M.core.ηu := by
      unfold kθ0
      exact mul_nonneg M.core.hC₀u (add_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _))
    unfold kB2; positivity
  have h5' : M.core.A ^ 4 * (cx M.core.κ M.core.cT * (M.core.c * M.core.ε) ^ 3 +
      8 * M.core.Bk * (M.core.c * M.core.ε) ^ 2 * (2 * M.core.cWo)) ≤ 1 := by
    refine le_trans ?_ h5
    have : 0 ≤ 10 * kB2 (kθ0 L M.core.A M.core.C₀u M.core.ηu) C₁' (cx M.core.κ M.core.cT)
        (8 * M.core.Bk) * (M.core.c * M.core.ε) * (2 * M.core.cWo) ^ 2 := by
      have : 0 ≤ M.core.c * M.core.ε := hr0.trans hgc
      positivity
    have hA4 : 0 ≤ M.core.A ^ 4 := pow_nonneg (by linarith) 4
    nlinarith
  have hKbulk : ∀ W, IsConn ms W → ENNReal.ofReal (R'.A ^ (nb ms W - 2 ^ 2)) *
      Tj 2 (L : ℝ) ms (histS R' ms t) (Kb W : Alg 2 L N) ≤
        ENNReal.ofReal (cx M.core.κ M.core.cT * (M.core.c * M.core.ε) ^ 3) := by
    intro W hW
    have hVj : ∀ i < ms, ValidAt R' i := fun i hi => hV i (by omega)
    have HI := rawInv_hist R' hρ0' ms hVj t
    have hZ : (rawHist R' ms t).Z ≠ 0 := HI.Z_ne_zero (by linarith)
    have hKn := Knorm_rawK R' HI.hu hZ (t ms).2.2
    have h1 : ENNReal.ofReal (R'.A ^ (nb ms W - 2 ^ 2)) *
        Tj 2 (L : ℝ) ms (histS R' ms t) (Kb W : Alg 2 L N) ≤
        Knorm ms (fscale (rawHist R' ms t).Z * R'.ℓ) R'.A (rawK R' (rawHist R' ms t).u (t ms).2.2) :=
      le_iSup₂ (f := fun X (_ : X ∈ connSets (L := L) (N := N) ms) =>
        ENNReal.ofReal (R'.A ^ (nb ms X - 2 ^ 2)) *
          Tj 2 (L : ℝ) ms (fscale (rawHist R' ms t).Z * R'.ℓ)
            (rawK R' (rawHist R' ms t).u (t ms).2.2 X : Alg 2 L N)) W
        (by simp [connSets]; exact hW)
    refine (h1.trans (le_of_eq hKn)).trans (ENNReal.ofReal_le_ofReal ?_)
    have h2 : ‖(t ms).2.2.2‖ ≤ cx M.core.κ M.core.cT * (t ms).1 ^ 3 := (norm_snd_le _).trans hxg
    have hgc' : (t ms).1 ≤ M.core.c * M.core.ε := by
      have : (t ms).1 ≤ M.core.c * (t ms).1 := by nlinarith
      linarith
    have h3 : (t ms).1 ^ 3 ≤ (M.core.c * M.core.ε) ^ 3 := pow_le_pow_left₀ hg.le hgc' 3
    exact h2.trans (mul_le_mul_of_nonneg_left h3 hcx)
  have hKw : ∀ W, IsConn ms W → ENNReal.ofReal (R'.A ^ nb ms W) *
      oTj 2 L (wB sS) ms (histS R' ms t) (((embF Kb + o₁.K : OAct .two 2 L N) W :
        OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)) ≤ 1 := by
    intro W hW
    have hA0 : 0 ≤ R'.A := by linarith
    have hb1 := oTj_emb_add_le (wB sS) ms (histS R' ms t) (Kb W) (o₁.K W) (hO₁.K W)
    have hb2 : oTo (wB sS) ms (histS R' ms t) (o₁.K W) ≤
        oTo (wM1 a1 sS) ms (histS R' ms t) (o₁.K W) := zab_oTo_wB_le a1 sS ms _ _
    calc ENNReal.ofReal (R'.A ^ nb ms W) *
          oTj 2 L (wB sS) ms (histS R' ms t) (((embF Kb + o₁.K : OAct .two 2 L N) W :
            OE .two (Lam 2 L N)) : SA .two (Lam 2 L N))
        ≤ ENNReal.ofReal (R'.A ^ 4) * (ENNReal.ofReal (R'.A ^ (nb ms W - 2 ^ 2)) *
          (Tj 2 (L : ℝ) ms (histS R' ms t) (Kb W : Alg 2 L N) +
            oTo (wM1 a1 sS) ms (histS R' ms t) (o₁.K W))) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hA0 4)]
          exact mul_le_mul' (ENNReal.ofReal_le_ofReal (regA_le _ hA1 _))
            (hb1.trans (add_le_add le_rfl hb2))
      _ ≤ ENNReal.ofReal (R'.A ^ 4) *
          (ENNReal.ofReal (cx M.core.κ M.core.cT * (M.core.c * M.core.ε) ^ 3) +
            ENNReal.ofReal (8 * M.core.Bk * (M.core.c * (t ms).1) ^ 2 * (2 * M.core.cWo))) := by
          rw [mul_add]
          exact mul_le_mul_left' (add_le_add (hKbulk W hW) (hK1o W hW)) _
      _ ≤ 1 := by
          have hcε0 : 0 ≤ M.core.c * M.core.ε := hr0.trans hgc
          have hk0 : 0 ≤ cx M.core.κ M.core.cT * (M.core.c * M.core.ε) ^ 3 :=
            mul_nonneg hcx (pow_nonneg hcε0 3)
          have hk1 : 0 ≤ 8 * M.core.Bk * (M.core.c * (t ms).1) ^ 2 * (2 * M.core.cWo) :=
            mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hBk) (sq_nonneg _)) (by linarith)
          rw [← ENNReal.ofReal_add hk0 hk1,
            ← ENNReal.ofReal_mul (pow_nonneg hA0 4), ← ENNReal.ofReal_one]
          refine ENNReal.ofReal_le_ofReal (le_trans ?_ h5')
          rw [hRA']
          have h2 : (M.core.c * (t ms).1) ^ 2 ≤ (M.core.c * M.core.ε) ^ 2 :=
            pow_le_pow_left₀ hr0 hgc 2
          have hA4 : 0 ≤ M.core.A ^ 4 := pow_nonneg (by linarith) 4
          refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) hA4
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 ?_) (by linarith)
          exact mul_nonneg (by norm_num) hBk
  -- the couplings
  have hd : ∑ q ∈ blocks ms X, Tj 2 (L : ℝ) ms (histS R' ms t)
      (β q • (pbp (pl2Pts x y).a - pbp (ptsX y).a)) ≤
      ENNReal.ofReal (a1 * (4 * supNorm (y - x) / (L : ℝ) ^ ms)) := by
    have hshA := (M.cw2_relBaseD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (pl2Pts x y)
      (zV0 b) rfl hmu hNh0 ms hms.le).2.1
    obtain ⟨hVeq, -, -⟩ := obsHist_zV0 R' (pl2Pts x y) t b (traj_zero_X R m b μ₀) ms hms0
    have hβs : ∑ q ∈ blocks ms X, ‖β q‖ ≤ 2 * ‖bt2 R (pl2Pts x y) (zV0 b) m b μ₀ ms‖ := by
      refine le_trans ?_ hshA
      refine (sum_le_sum_of_subset_of_nonneg (blocks_subset_blockIdx X)
        (fun _ _ _ => norm_nonneg _)).trans (le_of_eq ?_)
      refine sum_congr rfl fun q _ => ?_
      show ‖mass2 ((o₁.V q : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a‖ = _
      rw [histVO2_a]
      show ‖mass2 (((obsHist R' (pl2Pts x y) (obsInit .two (zV b) (pl2Pts x y)) ms t).V q :
        OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a‖ = _
      rw [hVeq]
      rfl
    calc ∑ q ∈ blocks ms X, Tj 2 (L : ℝ) ms (histS R' ms t)
          (β q • (pbp (pl2Pts x y).a - pbp (ptsX y).a))
        ≤ ∑ q ∈ blocks ms X, ENNReal.ofReal (‖β q‖ * (2 * ((2 : ℕ) : ℝ) *
            supNorm ((pl2Pts x y).a - (ptsX y).a) * histS R' ms t ^ 2 / (L : ℝ) ^ ms)) :=
          sum_le_sum fun q _ => reloc_coupling (d := 2) (by norm_num) hs (β q) _ _
      _ = ENNReal.ofReal ((∑ q ∈ blocks ms X, ‖β q‖) * (2 * ((2 : ℕ) : ℝ) *
            supNorm ((pl2Pts x y).a - (ptsX y).a) * histS R' ms t ^ 2 / (L : ℝ) ^ ms)) := by
          have hc0 : 0 ≤ 2 * ((2 : ℕ) : ℝ) * (supNorm ((pl2Pts x y).a - (ptsX y).a) : ℝ) *
              histS R' ms t ^ 2 / (L : ℝ) ^ ms :=
            div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (sq_nonneg _))
              (pow_pos hL0 _).le
          rw [← ENNReal.ofReal_sum_of_nonneg (fun q _ => mul_nonneg (norm_nonneg _) hc0), sum_mul]
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have e : supNorm ((pl2Pts x y).a - (ptsX y).a) = supNorm (y - x) := by
            show supNorm (y - x - 0) = _; rw [sub_zero]
          rw [e]
          have hp : a1 = 2 * histS R' ms t ^ 2 * ‖bt2 R (pl2Pts x y) (zV0 b) m b μ₀ ms‖ := rfl
          rw [hp]
          have h0 : 0 ≤ 2 * ((2 : ℕ) : ℝ) * supNorm (y - x) * histS R' ms t ^ 2 / (L : ℝ) ^ ms :=
            div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (sq_nonneg _))
              (pow_pos hL0 _).le
          calc (∑ q ∈ blocks ms X, ‖β q‖) * (2 * ((2 : ℕ) : ℝ) * supNorm (y - x) *
                histS R' ms t ^ 2 / (L : ℝ) ^ ms)
              ≤ 2 * ‖bt2 R (pl2Pts x y) (zV0 b) m b μ₀ ms‖ * (2 * ((2 : ℕ) : ℝ) * supNorm (y - x) *
                histS R' ms t ^ 2 / (L : ℝ) ^ ms) := mul_le_mul_of_nonneg_right hβs h0
            _ = _ := by push_cast; ring
  have hcorr := zab_corr_ab_le R' ms st (t ms).1 (t ms).2.1 Dd Kb (pl2Pts x y).a (ptsX y).a β hq1
    hs hA1 o₁ hX hι0 hIZ hKw hd
  -- assembly
  set Tx := Tj 2 (L : ℝ) ms (histS R' ms t) ((o₁.K X : OE .two (Lam 2 L N)) :
    SA .two (Lam 2 L N)).ab with hTx
  set Tz := Tj 2 (L : ℝ) ms (histS R' ms t) ((zabCorr R' ms st (t ms).1 (t ms).2.1 Dd Kb
    (pl2Pts x y).a (ptsX y).a β o₁ X : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).ab with hTz
  set Ty := Tj 2 (L : ℝ) ms (histS R' ms t) ((o₂.K X : OE .two (Lam 2 L N)) :
    SA .two (Lam 2 L N)).ab with hTy
  set Aw := ENNReal.ofReal (R'.A ^ (nb ms X - 2 ^ 2)) with hAw
  have hT : Tj 2 (L : ℝ) ms (histS R' ms t) (((o₁.K X : OE .two (Lam 2 L N)) :
      SA .two (Lam 2 L N)).ab + ((zabCorr R' ms st (t ms).1 (t ms).2.1 Dd Kb
      (pl2Pts x y).a (ptsX y).a β o₁ X : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).ab -
      ((o₂.K X : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).ab) ≤ Tx + Tz + Ty := by
    refine (tNorm_sub_le _ _).trans (add_le_add ?_ le_rfl)
    exact tNorm_add_le _ _
  have hρ1 : 0 ≤ a1 * sS / (Ma * Mb) := div_nonneg (mul_nonneg ha10 hsS0) hMM.le
  have hρ2 : 0 ≤ a2 * sS / (Ma * Mb) := div_nonneg (mul_nonneg ha20 hsS0) hMM.le
  set Z1 := M.k2cab * (M.core.c * (t ms).1) * (2 * M.core.cWo) ^ 2 with hZ1
  have h1 : Aw * ((wM Ma Mb).ab * Tx) ≤ ENNReal.ofReal (a1 * sS / (Ma * Mb) * Z1) := by
    rw [zab_wab_conv hp1 hq1 hMa hMb, ENNReal.ofReal_mul hρ1]
    calc Aw * (ENNReal.ofReal (a1 * sS / (Ma * Mb)) * (wM a1 sS).ab * Tx)
        = ENNReal.ofReal (a1 * sS / (Ma * Mb)) * (Aw * ((wM a1 sS).ab * Tx)) := by ring
      _ ≤ _ := mul_le_mul_left' (hK1ab X hX) _
  have h3 : Aw * ((wM Ma Mb).ab * Ty) ≤ ENNReal.ofReal (a2 * sS / (Ma * Mb) * Z1) := by
    rw [zab_wab_conv hp2 hq2 hMa hMb, ENNReal.ofReal_mul hρ2]
    calc Aw * (ENNReal.ofReal (a2 * sS / (Ma * Mb)) * (wM a2 sS).ab * Ty)
        = ENNReal.ofReal (a2 * sS / (Ma * Mb)) * (Aw * ((wM a2 sS).ab * Ty)) := by ring
      _ ≤ _ := mul_le_mul_left' (hK2ab X hX) _
  have hwab : (wM Ma Mb).ab = ENNReal.ofReal (Ma * Mb)⁻¹ := by
    rw [wM, mul_inv, ENNReal.ofReal_mul (inv_nonneg.2 hMa.le)]
  have hzc : 0 ≤ sS * (a1 * (4 * supNorm (y - x) / (L : ℝ) ^ ms)) * zabIota M.core.cWo * R'.A :=
    mul_nonneg (mul_nonneg (mul_nonneg hsS0 (mul_nonneg ha10 hd0)) hι0) hA0
  have h2 : Aw * ((wM Ma Mb).ab * Tz) ≤ ENNReal.ofReal ((Ma * Mb)⁻¹ *
      (sS * (a1 * (4 * supNorm (y - x) / (L : ℝ) ^ ms)) * zabIota M.core.cWo * R'.A)) := by
    rw [hwab, ENNReal.ofReal_mul (inv_nonneg.2 hMM.le)]
    calc Aw * (ENNReal.ofReal (Ma * Mb)⁻¹ * Tz) = ENNReal.ofReal (Ma * Mb)⁻¹ * (Aw * Tz) := by ring
      _ ≤ _ := mul_le_mul_left' hcorr _
  calc Aw * ((wM Ma Mb).ab * Tj 2 (L : ℝ) ms (histS R' ms t) (((o₁.K X : OE .two (Lam 2 L N)) :
      SA .two (Lam 2 L N)).ab + ((zabCorr R' ms st (t ms).1 (t ms).2.1 Dd Kb
      (pl2Pts x y).a (ptsX y).a β o₁ X : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).ab -
      ((o₂.K X : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).ab))
      ≤ Aw * ((wM Ma Mb).ab * (Tx + Tz + Ty)) := mul_le_mul_left' (mul_le_mul_left' hT _) _
    _ = Aw * ((wM Ma Mb).ab * Tx) + Aw * ((wM Ma Mb).ab * Tz) + Aw * ((wM Ma Mb).ab * Ty) := by
        ring
    _ ≤ ENNReal.ofReal (a1 * sS / (Ma * Mb) * Z1) + ENNReal.ofReal ((Ma * Mb)⁻¹ *
          (sS * (a1 * (4 * supNorm (y - x) / (L : ℝ) ^ ms)) * zabIota M.core.cWo * R'.A)) +
        ENNReal.ofReal (a2 * sS / (Ma * Mb) * Z1) := add_le_add (add_le_add h1 h2) h3
    _ = _ := by
        have hZ10 : 0 ≤ Z1 := mul_nonneg (mul_nonneg hcab0 hr0) (sq_nonneg _)
        rw [← ENNReal.ofReal_add (mul_nonneg hρ1 hZ10) (mul_nonneg (inv_nonneg.2 hMM.le) hzc),
          ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hρ1 hZ10)
            (mul_nonneg (inv_nonneg.2 hMM.le) hzc)) (mul_nonneg hρ2 hZ10)]
        congr 1
        have key : ∀ p1 p2 q z A' : ℝ,
            p1 = pM (R.withMsq m) (pl2Pts x y) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ms →
            p2 = pM (R.withMsq m) (ptsX y) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ms →
            q = pM (R.withMsq m) (ptsS y) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ms →
            z = M.k2cab * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ ms).1) *
              (2 * M.core.cWo) ^ 2 → A' = M.core.A →
            p1 * q / (Ma * Mb) * z + (Ma * Mb)⁻¹ *
              (q * (p1 * (4 * supNorm (y - x) / (L : ℝ) ^ ms)) * zabIota M.core.cWo * A') +
              p2 * q / (Ma * Mb) * z = zabZ M R m b μ₀ x y ms Ma Mb := by
          intro p1 p2 q z A' h1 h2 h3 h4 h5
          subst h1 h2 h3 h4 h5
          unfold zabZ; ring
        exact key a1 a2 sS Z1 R'.A rfl rfl rfl rfl hRA'

end MasterFacts

end

end Spin2
