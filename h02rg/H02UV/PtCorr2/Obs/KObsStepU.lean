import PtCorr2.Pair.KObsStepAB
import Obs2.Est.KObsU

/-!
# The `σ_aσ_b` part of the `K^{obs}` step for unreduced states at the raw level

**`kobs_raw_stepU`**: the copy of `kobs_raw_stepAB` for the **unreduced** observable state (one-point
parts present; `ObsLocInv`, `ObsSymInv`, `K(X)_{ab} = 0` on small `X` as below coalescence,
`ObsCoalInv`), finite weights with `w.Sub`: with `‖V^{obs}‖_w ≤ m`, `‖𝒲^{obs}‖_w ≤ rm`,
`A^{(|𝓑_j(X)|-4)_+}‖K^{obs}(X)‖_{(w_a,w_b,0)} ≤ k₁`, `A^{(…)}w_{ab}‖K(X)_{ab}‖ ≤ k₂` (`r ≤ m`),

  `(r/m)² A^{(|𝓑_{j+1}(U)|-4)_+} w_{ab}‖K_{j+1}(U)_{ab}‖_{T_{j+1}(s')} ≤ θ₀k_t + C₁((2r)³ + 2rk_t + k_t²)`,
  `k_t = 8k_b + (r/m)8k₁ + (r/m)²8k₂`, `θ₀ = C₀(L^{-1} + (A/2)^{-η})`.

From `Obs2.kobsK_stepWU` with `μ = 2`, `ḡ = 2r`. `ab_fullK_le`: the `ab` part of `K♭`.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2

variable {L N : ℕ} [NeZero L]

/-- **The `ab` part of `K♭` along the step.** -/
theorem ab_fullK_le (R : RGPar 2 L N) (j : ℕ) (st : RawSt 2 L N) (K : Act 2 L N)
    {c : Obs.Case} (o : ObsSt c L N) (w : Wt) (hw : w.Sub) {ℓ A δ : ℝ} (hℓ : 0 < ℓ)
    (hA : 0 < A) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2)
    (hΔ : Fnorm j ℓ (stDelta R j st) ≤ ENNReal.ofReal δ) (X : Finset (Lam 2 L N)) :
    ENNReal.ofReal ((A / 2) ^ (nb j X - 2 ^ 2)) *
        (w.ab * Tj 2 (L : ℝ) j ℓ (fullK R j st K o X : SA c (Lam 2 L N)).ab) ≤
      ENNReal.ofReal 8 * (ENNReal.ofReal (A ^ (nb j X - 2 ^ 2)) *
        (w.ab * Tj 2 (L : ℝ) j ℓ (o.K X : SA c (Lam 2 L N)).ab)) := by
  set K' : OAct c 2 L N := fun Y => πab ((embF K + o.K : OAct c 2 L N) Y) with hK'
  have hK'ab : ∀ Y, K' Y ∈ (abSub : Subalgebra ℂ (OE c (Lam 2 L N))) := fun Y =>
    ⟨by simp [hK', coe_πab, piab_apply], by simp [hK', coe_πab, piab_apply]⟩
  have hflat : KflatO j (stDelta R j st) K' X ∈ (abSub : Subalgebra ℂ (OE c (Lam 2 L N))) :=
    mul_mem (emb_mem_ab _) (hK'ab X)
  have e1 : oTo w j ℓ (KflatO j (stDelta R j st) K' X) =
      w.ab * Tj 2 (L : ℝ) j ℓ (fullK R j st K o X : SA c (Lam 2 L N)).ab := by
    rw [oTo_of_ab w j ℓ hflat]
    congr 2
    show (((emb _ : OE c (Lam 2 L N)) * K' X : OE c (Lam 2 L N)) : SA c (Lam 2 L N)).ab =
      (((emb _ : OE c (Lam 2 L N)) * (embF K + o.K : OAct c 2 L N) X : OE c (Lam 2 L N)) :
        SA c (Lam 2 L N)).ab
    rw [emb_mul_ab, emb_mul_ab]
    simp [hK', coe_πab, piab_apply]
  have e2 : oTo w j ℓ (K' X) = w.ab * Tj 2 (L : ℝ) j ℓ (o.K X : SA c (Lam 2 L N)).ab := by
    rw [oTo_of_ab w j ℓ (hK'ab X)]
    congr 2
    simp only [hK', coe_πab, piab_apply]
    exact emb_add_ab _ _
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
  have h1 := oTo_KflatO_le w hw j hℓ hA.le hδ0 (stDelta R j st) (eps_stDelta R j st)
    (fun b hb => (Tj_le_Fnorm _ hb).trans hΔ) K' X
  rw [e1, e2] at h1
  calc ENNReal.ofReal ((A / 2) ^ (nb j X - 2 ^ 2)) *
        (w.ab * Tj 2 (L : ℝ) j ℓ (fullK R j st K o X : SA c (Lam 2 L N)).ab)
      ≤ ENNReal.ofReal ((A * Real.exp (-δ)) ^ (nb j X - 2 ^ 2)) *
        (w.ab * Tj 2 (L : ℝ) j ℓ (fullK R j st K o X : SA c (Lam 2 L N)).ab) :=
        mul_le_mul_right' (ENNReal.ofReal_le_ofReal
          (pow_le_pow_left₀ (by positivity) hmono _)) _
    _ ≤ _ := h1
    _ ≤ _ := mul_le_mul_right' (ENNReal.ofReal_le_ofReal hexp) _

set_option maxHeartbeats 2000000 in
/-- **The `ab` part of the `K^{obs}` step at the raw level, unreduced states.** -/
theorem kobs_raw_stepU : ∃ (C₀ η : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧ 0 < η ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) (j : ℕ), ValidCore R j → ∀ st : RawSt 2 L N, RawInv R j st →
    ∀ (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N), D ∈ BSub (L := L) (N := N) j →
      K ∈ ASub (L := L) (N := N) j → |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1 → 0 ≤ g →
    ∀ ηz : ℝ, ‖st.z / st.Z‖ ≤ ηz → ‖st.y / st.Z‖ ≤ ηz → 2 * ηz ≤ R.ρ →
      8 * cM * R.ℓ ^ 2 * ηz ≤ 1 / 2 →
    ∀ (c : Obs.Case) (P : ObsPts 2 L N) (w : Wt), w.Sub → w.a ≠ ⊤ → w.b ≠ ⊤ → w.ab ≠ ⊤ →
    ∀ o : ObsSt c L N, o.IsObs → ObsLocInv P j o → ObsSymInv j o →
    (∀ X, IsSmall j X → (o.K X : SA c (Lam 2 L N)).ab = 0) →
    ∀ wl dd kb r m k₁ k₂ : ℝ, 0 ≤ wl → 0 ≤ dd → 0 ≤ kb → 0 < r → 0 < m → r ≤ m → 0 ≤ k₁ →
      0 ≤ k₂ →
      Fnorm j (fscale st.Z * R.ℓ) st.Wl ≤ ENNReal.ofReal wl →
      Fnorm j (fscale st.Z * R.ℓ) D ≤ ENNReal.ofReal dd →
      Knorm j (fscale st.Z * R.ℓ) A K ≤ ENNReal.ofReal kb →
      cM * R.ℓ ^ 2 * (2 * |μ| + 2 * ηz) + 8 * R.ℓ ^ 4 * g ≤ r → wl + dd ≤ r ^ 2 →
      2 * r ≤ ε₀ → 8 * kb + r / m * (8 * k₁) + (r / m) ^ 2 * (8 * k₂) ≤ ε₀ →
      (∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo w j (fscale st.Z * R.ℓ) (o.V b) ≤ ENNReal.ofReal m) →
      (∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo w j (fscale st.Z * R.ℓ) (o.W b) ≤ ENNReal.ofReal (r * m)) →
      (∀ X, IsConn j X → ENNReal.ofReal (A ^ (nb j X - 2 ^ 2)) *
        oTo (wOne w) j (fscale st.Z * R.ℓ) (o.K X) ≤ ENNReal.ofReal k₁) →
      (∀ X, IsConn j X → ENNReal.ofReal (A ^ (nb j X - 2 ^ 2)) *
        (w.ab * Tj 2 (L : ℝ) j (fscale st.Z * R.ℓ) (o.K X : SA c (Lam 2 L N)).ab) ≤
          ENNReal.ofReal k₂) →
      ∀ U : Finset (Lam 2 L N), IsConn (j + 1) U →
        ENNReal.ofReal ((r / m) ^ 2) * (ENNReal.ofReal (A ^ (nb (j + 1) U - 2 ^ 2)) *
          (w.ab * Tj 2 (L : ℝ) (j + 1) (fscale (stZ' R st) * R.ℓ)
            ((obsStep R P j st g μ D K o).K U : SA c (Lam 2 L N)).ab)) ≤
        ENNReal.ofReal (C₀ * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3 + (A / 2) ^ (-η)) *
            (8 * kb + r / m * (8 * k₁) + (r / m) ^ 2 * (8 * k₂)) +
          C₁ * ((2 * r) ^ 3 + 2 * r * (8 * kb + r / m * (8 * k₁) + (r / m) ^ 2 * (8 * k₂)) +
            (8 * kb + r / m * (8 * k₁) + (r / m) ^ 2 * (8 * k₂)) ^ 2)) := by
  obtain ⟨C₀, η, L₀, hC₀, hη, h⟩ := kobsK_stepWU 2 le_rfl
  refine ⟨C₀, η, L₀, hC₀, hη, fun L _ hL => ?_⟩
  obtain ⟨A₀, hA₀, h⟩ := h L hL 2 one_le_two
  refine ⟨2 * A₀, by linarith, fun A hA => ?_⟩
  obtain ⟨ε₀, C₁, hε₀, hC₁, h⟩ := h (A / 2) (by linarith)
  refine ⟨ε₀, C₁, hε₀, hC₁, ?_⟩
  intro N R j hV st H g μ D K hD hK hm hg0 ηz hz hy hηρ hηs c P w hwS hwa hwb hwab o ho hloc hsym hKs
    wl dd kb r m k₁ k₂ hwl0 hdd0 hkb0 hr0 hm0 hrm hk₁ hk₂ hWl hDd hKk hvr hwr hrε
    hεk hVo hWo hK1 hK2 U hU
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
  have hwsub : w.Sub := hwS
  have hVo' : ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (fscale st.Z * R.ℓ) (fullV R j st g μ o b) ≤ ENNReal.ofReal m :=
    fun b hb => (oTo_emb_add_le w j _ _ _).trans (hVo b hb)
  have hWo' : ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (fscale st.Z * R.ℓ) (fullW st D o b) ≤ ENNReal.ofReal (r * m) :=
    fun b hb => (oTo_emb_add_le w j _ _ _).trans (hWo b hb)
  have hK1' : ∀ X, IsConn j X → ENNReal.ofReal ((A / 2) ^ (nb j X - 2 ^ 2)) *
      oTo (wOne w) j (fscale st.Z * R.ℓ) (fullK R j st K o X) ≤ ENNReal.ofReal (8 * k₁) := by
    intro X hX
    refine (oTo_fullK_leAB R j st K o (wOne w) (show (wOne w).Sub from zero_le) hsℓ hA0 hδΔ0 (by linarith) hΔ X).trans ?_
    rw [ENNReal.ofReal_mul (by norm_num)]
    exact mul_le_mul_left' (hK1 X hX) _
  have hK2' : ∀ X, IsConn j X → ENNReal.ofReal ((A / 2) ^ (nb j X - 2 ^ 2)) *
      (w.ab * Tj 2 (L : ℝ) j (fscale st.Z * R.ℓ) (fullK R j st K o X : SA c (Lam 2 L N)).ab) ≤
        ENNReal.ofReal (8 * k₂) := by
    intro X hX
    refine (ab_fullK_le R j st K o w hwS hsℓ hA0 hδΔ0 (by linarith) hΔ X).trans ?_
    rw [ENNReal.ofReal_mul (by norm_num)]
    exact mul_le_mul_left' (hK2 X hX) _
  have hKs' : ∀ X, IsSmall j X → (fullK R j st K o X : SA c (Lam 2 L N)).ab = 0 := by
    intro X hX
    show (((emb (bpow j (fun b => gexp (stDelta R j st b)) X) : OE c (Lam 2 L N)) *
      ((emb (K X) : OE c (Lam 2 L N)) + o.K X) : OE c (Lam 2 L N)) : SA c (Lam 2 L N)).ab = 0
    rw [emb_mul_ab, emb_add_ab, hKs X hX, mul_zero]
  -- apply the step
  have HL := olocS_full R P g μ hV H hD hK hloc
  have HS := osymS_full R g μ hV H hD hK hsym
  have e2r : 2 * r / (2 * m) = r / m := by field_simp
  have key := h N j (by omega) (fscale st.Z * R.ℓ) (s' * R.ℓ) (s' * R.ℓ / 4) hsℓ
    (mul_pos hs' hℓ) (by positivity) hsum (stCov R j st) hC c P w hwS hwa hwb hwab
    (fullV R j st g μ o) (fullW st D o) (fullK R j st K o)
    (by rw [bulkF_fullV R j st g μ ho]; exact hVf_mem.1)
    (by rw [bulkF_fullW st D ho]; exact (add_mem H.hWl hD).1)
    (by rw [bulkF_fullV R j st g μ ho]; exact fun b => eps_VfamL j _ b)
    (by rw [bulkF_fullK R j st K ho]; exact hKfmem.1)
    HL (fun X hX => mem_symSub.1 (HS.hK X hX)) hKs'
    (2 * r) m (8 * kb) (8 * k₁) (8 * k₂) (by linarith) hm0 (by linarith) (by positivity)
    (by positivity) (by positivity) hrε (by rw [e2r]; exact hεk)
    (by
      rw [bulkF_fullV R j st g μ ho]
      exact hVv.trans (ENNReal.ofReal_le_ofReal (by linarith)))
    (by
      rw [bulkF_fullW st D ho]
      exact hw.trans (ENNReal.ofReal_le_ofReal (by nlinarith)))
    hVo' (fun b hb => (hWo' b hb).trans (ENNReal.ofReal_le_ofReal (by nlinarith)))
    (by rw [bulkF_fullK R j st K ho]; exact hKflat) hK1' hK2' U hU
  rw [show (2 : ℝ) * (A / 2) = A by ring, e2r] at key
  have e : ((obsStep R P j st g μ D K o).K U : SA c (Lam 2 L N)).ab =
      (KplusO P j (stCov R j st) (fullV R j st g μ o) (fullW st D o) (fullK R j st K o) U :
        SA c (Lam 2 L N)).ab := by
    simp only [obsStep, KconnO, if_pos hU]
    exact piobs_ab _
  rw [e]
  exact key

end

end PtCorr2
