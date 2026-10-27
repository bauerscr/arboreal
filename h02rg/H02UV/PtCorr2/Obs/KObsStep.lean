import Step2.Flow.FlowRGIn
import Obs2.Est.KFlatO
import Obs2.Est.KObs4W
import PtCorr2.Obs.ObsLoc
import PtCorr2.Obs.ObsSym

/-!
# The `K^{obs}` step of the observable flow at the raw level

**`kobs_raw_step`**: one step of `obsStep` (the observable flow driven by `rawStep`), in the
normalisation of `Step2.rg_step_bounds`: at the causal field scales `s = |Z|^{-1/2} ℓ`,
`s' = |Z'|^{-1/2} ℓ`, under the clamp conditions of `StepBounds`, with the bulk radius `r`
(`‖V♭‖ ≤ r`, `‖W^{lin}‖ + ‖D‖ ≤ r²`, `8‖K‖_{j,A} ≤ c_b r³`), observable sizes
`‖V^{obs}_j‖ ≤ m`, `‖𝒲^{obs}_j‖ ≤ r m` and `A^{(|𝓑_j(X)|-4)_+}‖K^{obs}_j(X)‖ ≤ k`
(`8k ≤ c_k r² m`):

  `A^{(|𝓑_{j+1}(U)|-4)_+} ‖K^{obs}_{j+1}(U)‖_{T_{j+1}(s')} ≤ (θ₀ + C₁(2+2c_b+c_k) r) 8k
    + (θ₀ c_b + C₁(8+2c_b+c_b²)) r² m`,

`θ₀ = C₀(L^{-1} + (A/2)^{-η})`. Proof: `Obs2.kobsK_stepW` with `μ = 2` at input regulator
`A/2`; the regulator loss and the factor `e^{4δ} ≤ 8` come from `K♭ = ∏ e^{Δ(B)} K`
(`Obs2.oTo_KflatO_le`, `Step2.Knorm_stKflat_le`), as in `rg_step_bounds`. Locality and `U(1)`
invariance of the full inputs come from `ObsLocInv`, `ObsSymInv` (`olocS_full`, `osymS_full`).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2

variable {L N : ℕ} [NeZero L]

theorem oTo_emb_add_le (w : Wt) {c : Obs.Case} (j : ℕ) (ℓ : ℝ) (x : EvR (Lam 2 L N))
    (F : OE c (Lam 2 L N)) : oTo w j ℓ (emb x + F) ≤ oTo w j ℓ F :=
  (oTo_add_le w j ℓ _ _).trans (by rw [oTo_emb, zero_add])

/-- **The observable part of `K♭` along the step**: with `‖Δ‖ ≤ δ ≤ 1/2`, the regulator `A/2`
and the factor `8 ≥ e^{4δ}`. -/
theorem oTo_fullK_le (R : RGPar 2 L N) (j : ℕ) (st : RawSt 2 L N) (K : Act 2 L N)
    {c : Obs.Case} (o : ObsSt c L N) (w : Wt) (hw0 : w.ab = 0) {ℓ A δ : ℝ} (hℓ : 0 < ℓ)
    (hA : 0 < A) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2)
    (hΔ : Fnorm j ℓ (stDelta R j st) ≤ ENNReal.ofReal δ) (X : Finset (Lam 2 L N)) :
    ENNReal.ofReal ((A / 2) ^ (nb j X - 2 ^ 2)) * oTo w j ℓ (fullK R j st K o X) ≤
      ENNReal.ofReal 8 * (ENNReal.ofReal (A ^ (nb j X - 2 ^ 2)) * oTo w j ℓ (o.K X)) := by
  have hexp : Real.exp (2 ^ 2 * δ) ≤ 8 := by
    have : (2 : ℝ) ^ 2 * δ ≤ 2 := by linarith
    calc Real.exp (2 ^ 2 * δ) ≤ Real.exp 2 := Real.exp_le_exp.2 this
      _ ≤ 8 := by
          have := Real.exp_one_lt_d9
          have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
          nlinarith [Real.exp_pos 1]
  have hmono : A / 2 ≤ A * Real.exp (-δ) := by
    have : (1 : ℝ) / 2 ≤ Real.exp (-δ) := by
      have h1 := Real.add_one_le_exp (-δ)
      linarith
    nlinarith
  have hwsub : w.Sub := by simp [Wt.Sub, hw0]
  have h1 := oTo_KflatO_le w hwsub j hℓ hA.le hδ0 (stDelta R j st) (eps_stDelta R j st)
    (fun b hb => (Tj_le_Fnorm _ hb).trans hΔ) (embF K + o.K : OAct c 2 L N) X
  have h2 : oTo w j ℓ ((embF K + o.K : OAct c 2 L N) X) ≤ oTo w j ℓ (o.K X) :=
    oTo_emb_add_le w j _ _ _
  calc ENNReal.ofReal ((A / 2) ^ (nb j X - 2 ^ 2)) * oTo w j ℓ (fullK R j st K o X)
      ≤ ENNReal.ofReal ((A * Real.exp (-δ)) ^ (nb j X - 2 ^ 2)) *
        oTo w j ℓ (KflatO j (stDelta R j st) (embF K + o.K : OAct c 2 L N) X) :=
        mul_le_mul_right' (ENNReal.ofReal_le_ofReal
          (pow_le_pow_left₀ (by positivity) hmono _)) _
    _ ≤ ENNReal.ofReal (Real.exp (2 ^ 2 * δ)) *
        (ENNReal.ofReal (A ^ (nb j X - 2 ^ 2)) * oTo w j ℓ (o.K X)) :=
        h1.trans (mul_le_mul_left' (mul_le_mul_left' h2 _) _)
    _ ≤ _ := mul_le_mul_right' (ENNReal.ofReal_le_ofReal hexp) _

set_option maxHeartbeats 2000000 in
/-- **The `K^{obs}` step at the raw level.** -/
theorem kobs_raw_step : ∃ (C₀ η : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧ 0 < η ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) (j : ℕ), ValidCore R j → ∀ st : RawSt 2 L N, RawInv R j st →
    ∀ (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N), D ∈ BSub (L := L) (N := N) j →
      K ∈ ASub (L := L) (N := N) j → |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1 → 0 ≤ g →
    ∀ ηz : ℝ, ‖st.z / st.Z‖ ≤ ηz → ‖st.y / st.Z‖ ≤ ηz → 2 * ηz ≤ R.ρ →
      8 * cM * R.ℓ ^ 2 * ηz ≤ 1 / 2 →
    ∀ (c : Obs.Case) (P : ObsPts 2 L N) (w : Wt), w.ab = 0 → w.a ≠ ⊤ → w.b ≠ ⊤ →
    ∀ o : ObsSt c L N, o.IsObs → ObsLocInv P j o → ObsSymInv j o →
    ∀ wl dd kb r m k cb ck : ℝ, 0 ≤ wl → 0 ≤ dd → 0 ≤ kb → 0 < r → 0 < m → 0 ≤ k →
      0 ≤ cb → 0 ≤ ck →
      Fnorm j (fscale st.Z * R.ℓ) st.Wl ≤ ENNReal.ofReal wl →
      Fnorm j (fscale st.Z * R.ℓ) D ≤ ENNReal.ofReal dd →
      Knorm j (fscale st.Z * R.ℓ) A K ≤ ENNReal.ofReal kb →
      cM * R.ℓ ^ 2 * (2 * |μ| + 2 * ηz) + 8 * R.ℓ ^ 4 * g ≤ r → wl + dd ≤ r ^ 2 →
      r ≤ 1 → r ≤ ε₀ → 8 * kb ≤ cb * r ^ 3 → 8 * k ≤ ck * r ^ 2 * m →
      8 * kb + r / m * (8 * k) ≤ ε₀ →
      (∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo w j (fscale st.Z * R.ℓ) (o.V b) ≤ ENNReal.ofReal m) →
      (∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo w j (fscale st.Z * R.ℓ) (o.W b) ≤ ENNReal.ofReal (r * m)) →
      (∀ X, IsConn j X → ENNReal.ofReal (A ^ (nb j X - 2 ^ 2)) *
        oTo w j (fscale st.Z * R.ℓ) (o.K X) ≤ ENNReal.ofReal k) →
      ∀ U : Finset (Lam 2 L N), IsConn (j + 1) U →
        ENNReal.ofReal (A ^ (nb (j + 1) U - 2 ^ 2)) *
          oTo w (j + 1) (fscale (stZ' R st) * R.ℓ) ((obsStep R P j st g μ D K o).K U) ≤
        ENNReal.ofReal ((C₀ * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3 + (A / 2) ^ (-η)) +
            C₁ * (2 + 2 * cb + ck) * r) * (8 * k) +
          (C₀ * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3 + (A / 2) ^ (-η)) * cb +
            C₁ * (8 + 2 * cb + cb ^ 2)) * r ^ 2 * m) := by
  obtain ⟨C₀, η, L₀, hC₀, hη, h⟩ := kobsK_stepW 2 le_rfl
  refine ⟨C₀, η, L₀, hC₀, hη, fun L _ hL => ?_⟩
  obtain ⟨A₀, hA₀, h⟩ := h L hL 2 one_le_two
  refine ⟨2 * A₀, by linarith, fun A hA => ?_⟩
  obtain ⟨ε₀, C₁, hε₀, hC₁, h⟩ := h (A / 2) (by linarith)
  refine ⟨ε₀, C₁, hε₀, hC₁, ?_⟩
  intro N R j hV st H g μ D K hD hK hm hg0 ηz hz hy hηρ hηs c P w hw0 hwa hwb o ho hloc hsym
    wl dd kb r m k cb ck hwl0 hdd0 hkb0 hr0 hm0 hk0 hcb hck hWl hDd hKk hvr hwr hr1 hrε hbr hkr
    hεk hVo hWo hKo U hU
  have hA0 : 0 < A := by linarith
  have hV' := hV
  obtain ⟨hj1, -, hL8, hρ0, hρ8, hℓ, -⟩ := hV'
  have hZ : st.Z ≠ 0 := H.Z_ne_zero (by linarith)
  have hη0 : 0 ≤ ηz := (norm_nonneg _).trans hz
  have hjN : j < N := by omega
  have hzy : ‖(st.z + st.y) / st.Z‖ ≤ R.ρ := by
    rw [add_div]; exact (norm_add_le _ _).trans (by linarith)
  have hζ : stZeta R st = (st.z + st.y) / st.Z := by
    unfold stZeta absorbZeta; rw [clampDisk_of_le hzy]
  have hζη : ‖stZeta R st‖ ≤ 2 * ηz := by
    rw [hζ, add_div]; exact (norm_add_le _ _).trans (by linarith)
  have hζ8 : ‖stZeta R st‖ ≤ 1 / 8 := by linarith
  -- scales
  set s' := fscale (stZ' R st)
  have hs := fscale_pos hZ
  have hZ' : stZ' R st ≠ 0 := mul_ne_zero hZ (one_add_ne_zero (by linarith))
  have hs' : 0 < s' := fscale_pos hZ'
  have hsc := scale_ok hZ hζ8 hℓ
  have hsc' : s' * R.ℓ + s' * R.ℓ / 4 ≤ 3 / 2 * (fscale st.Z * R.ℓ) := hsc
  have hsℓ : 0 < fscale st.Z * R.ℓ := mul_pos hs hℓ
  have hsum : s' * R.ℓ + s' * R.ℓ / 4 ≤ 2 * (fscale st.Z * R.ℓ) := by linarith
  obtain ⟨hC0, -, -, -⟩ := H.covL hV
  have hC : GoodCov2 j (s' * R.ℓ / 4) (stCov R j st) := hC0
  -- bulk inputs
  obtain ⟨hVv, hΔ⟩ := rg_inputs R j hV st H g μ hm hg0 ηz hz hy hηρ
  have hVf_mem : stVf R j st g μ ∈ BSub (L := L) (N := N) j := by
    rw [stVf_eq_kap]
    exact VfamL_mem (L := L) (N := N) (d := 2) (by norm_num) hL8 hjN (stKap R j st g μ).toVec
  have hKfmem := Kflat_mem hjN (VfamL_mem (L := L) (N := N) (d := 2) (by norm_num) hL8 hjN _)
    (eps_stDelta R j st) hK
  have hw : Fnorm j (fscale st.Z * R.ℓ) (st.Wl + D) ≤ ENNReal.ofReal (wl + dd) :=
    Fnorm_add_le _ _ hwl0 hdd0 hWl hDd
  set δΔ := 8 * cM * R.ℓ ^ 2 * ηz with hδΔ
  have hM : (0 : ℝ) ≤ cM := Nat.cast_nonneg _
  have hδΔ0 : 0 ≤ δΔ := by positivity
  have hexp : Real.exp (4 * δΔ) ≤ 8 := by
    have : 4 * δΔ ≤ 2 := by linarith
    calc Real.exp (4 * δΔ) ≤ Real.exp 2 := Real.exp_le_exp.2 this
      _ ≤ 8 := by
          have := Real.exp_one_lt_d9
          have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
          nlinarith [Real.exp_pos 1]
  have hmono : A / 2 ≤ A * Real.exp (-δΔ) := by
    have : (1 : ℝ) / 2 ≤ Real.exp (-δΔ) := by
      have h1 := Real.add_one_le_exp (-δΔ)
      linarith
    nlinarith
  have hKf := Knorm_stKflat_le (R := R) j hsℓ hA0.le hδΔ0 st hΔ K
  have hKflat : Knorm j (fscale st.Z * R.ℓ) (A / 2) (Kflat j (stDelta R j st) K) ≤
      ENNReal.ofReal (8 * kb) := by
    refine (Knorm_mono_A (by linarith) hmono _).trans (hKf.trans ?_)
    rw [ENNReal.ofReal_mul (by norm_num)]
    calc ENNReal.ofReal (Real.exp (4 * δΔ)) * Knorm j (fscale st.Z * R.ℓ) A K
        ≤ ENNReal.ofReal 8 * ENNReal.ofReal kb := by
          gcongr
      _ = _ := rfl
  -- observable inputs
  have hwsub : w.Sub := by simp [Wt.Sub, hw0]
  have hVo' : ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (fscale st.Z * R.ℓ) (fullV R j st g μ o b) ≤ ENNReal.ofReal m :=
    fun b hb => (oTo_emb_add_le w j _ _ _).trans (hVo b hb)
  have hWo' : ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (fscale st.Z * R.ℓ) (fullW st D o b) ≤ ENNReal.ofReal (r * m) :=
    fun b hb => (oTo_emb_add_le w j _ _ _).trans (hWo b hb)
  have hKo' : ∀ X, IsConn j X → ENNReal.ofReal ((A / 2) ^ (nb j X - 2 ^ 2)) *
      oTo w j (fscale st.Z * R.ℓ) (fullK R j st K o X) ≤ ENNReal.ofReal (8 * k) := by
    intro X hX
    refine (oTo_fullK_le R j st K o w hw0 hsℓ hA0 hδΔ0 (by linarith) hΔ X).trans ?_
    rw [ENNReal.ofReal_mul (by norm_num)]
    exact mul_le_mul_left' (hKo X hX) _
  -- apply the step
  have HL := olocS_full R P g μ hV H hD hK hloc
  have HS := osymS_full R g μ hV H hD hK hsym
  have key := h N j (by omega) (fscale st.Z * R.ℓ) (s' * R.ℓ) (s' * R.ℓ / 4) hsℓ
    (mul_pos hs' hℓ) (by positivity) hsum (stCov R j st) hC c P w hw0 hwa hwb
    (fullV R j st g μ o) (fullW st D o) (fullK R j st K o)
    (by rw [bulkF_fullV R j st g μ ho]; exact hVf_mem.1)
    (by rw [bulkF_fullW st D ho]; exact (add_mem H.hWl hD).1)
    (by rw [bulkF_fullV R j st g μ ho]; exact fun b => eps_VfamL j _ b)
    (by rw [bulkF_fullK R j st K ho]; exact hKfmem.1)
    HL (fun X hX => mem_symSub.1 (HS.hK X hX))
    r m (8 * kb) (8 * k) cb ck hr0 hr1 hrε hm0 (by positivity) hbr hcb (by positivity) hkr hck
    hεk
    (by rw [bulkF_fullV R j st g μ ho]; exact hVv.trans (ENNReal.ofReal_le_ofReal hvr))
    (by rw [bulkF_fullW st D ho]; exact hw.trans (ENNReal.ofReal_le_ofReal hwr))
    hVo' hWo' (by rw [bulkF_fullK R j st K ho]; exact hKflat) hKo' U hU
  rw [show (2 : ℝ) * (A / 2) = A by ring] at key
  have e : (obsStep R P j st g μ D K o).K U = πobs (KplusO P j (stCov R j st)
      (fullV R j st g μ o) (fullW st D o) (fullK R j st K o) U) := by
    simp only [obsStep, KconnO, if_pos hU]
  rw [e, oTo_πobs]
  exact key

end

end PtCorr2
