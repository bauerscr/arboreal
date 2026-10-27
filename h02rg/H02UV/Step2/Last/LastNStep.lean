import Step2.Last.LastNMain
import Step2.Flow.FlowRG
import Step2.Last.ZeroMode

/-!
# The last step `j = N - 1` on the raw state (`h02uv-outline.tex`, Section `sec:corr`)

The raw last step `rawStepN` mirrors `Step2.rawStep` with the covariance of the **nonzero modes**
`C'^{≠0}_N = kmat (nzP Γ^int_N)` (`lastCov`); the zero mode `t Q` is not integrated (it is left to
the correlation analysis, `prop:ZNN`). The input is the raw state at scale `N - 1` and the
coordinates `(ǧ, μ, D, K)`; as in `rawStep`, the coupling `ζ_{N-1}` is absorbed (clamped), giving
`Z_N = Z_{N-1}(1 + ζ_{N-1})`, `V♭ = stVf`, `𝒲 = W^lin + D`, `K♭ = Kflat Δ K`. The output
(`LastOut`) is the final-scale object

  `𝔼_{C'^{≠0}_N} θ Z_{N-1} = e^{-u_N(Λ)} (∏_B e^{-V_N(B)} (1 + 𝒲_N(B)) + K_N(Λ))`
  (`rawStepN_ZVK`),

with `V_N(B) = V_{κ_N}(B)` a coupling polynomial (`rawStepN_V`), `κ_N = κ♭'` the first-order
shift of the couplings of `V♭` by `c₀ = C(0,0)` and `δ = C(e₁,0) - C(0,0)` (`Coup.shift`).
`ValidLast` collects the hypotheses on the covariance (the analogue of `ValidAt` at
`j + 1 = N`); `validLastN_concrete` proves them for the concrete dressed decomposition from
`validLast_concrete`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

namespace LastN

/-- The covariance of the last step: the nonzero modes of the raw `Γ^int_N` of the dressed
history `ζ`. -/
def lastCov (R : RGPar d L N) (j : ℕ) (ζ : ℕ → ℂ) : Matrix (Lam d L N) (Lam d L N) ℂ :=
  DressedFRD.kmat (DressedFRD.nzP
    ((⟨L, N, R.msq, DressedFRD.frdC R.P R.msq L N, ζ⟩ : DressedFRD.Data d (L ^ N)).Gint j))

/-- **Validity of the parameters at the last step** `j + 1 = N`: as `ValidAt`, with the
nonzero-mode covariance `lastCov` in place of `rawCov` (no range condition). -/
def ValidLast (R : RGPar d L N) (j : ℕ) : Prop :=
  j + 1 = N ∧ 1 ≤ d ∧ 2 ^ (d + 3) + 8 * d < L ∧ 0 ≤ R.ρ ∧ R.ρ ≤ 1 / 8 ∧ 0 < R.ℓ ∧
  ∀ ζ : ℕ → ℂ, (∀ i, ‖ζ i‖ ≤ R.ρ) →
    GoodCov2 j (fscale (∏ i ∈ range (j + 1), (1 + ζ i)) * R.ℓ / 4) (lastCov R j ζ) ∧
      TInv (lastCov R j ζ) ∧ CSym (lastCov R j ζ) ∧ ∀ x y, lastCov R j ζ x y = lastCov R j ζ y x

/-- **`ValidLast` for the concrete dressed decomposition** (`d = 2`). -/
theorem validLastN_concrete (P : PtFamily) (hL : 2 ^ (2 + 3) + 8 * 2 < L) :
    ∃ ℓ₀ : ℝ, 0 < ℓ₀ ∧ ∃ ζbar : ℝ, 0 < ζbar ∧ ζbar ≤ 1 / 8 ∧
    ∀ (N : ℕ) (R : RGPar 2 L N), R.P = P → 1 ≤ N → 0 < R.msq →
      R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) → ℓ₀ ≤ R.ℓ → 0 ≤ R.ρ → R.ρ ≤ ζbar →
      ∀ j, j + 1 = N → ValidLast R j := by
  obtain ⟨ℓ₀, hℓ₀, ζbar, hζ, hζ8, h⟩ := validLast_concrete P hL
  refine ⟨ℓ₀, hℓ₀, ζbar, hζ, hζ8, fun N R hP hN hm0 hm hℓ hρ0 hρ j hj => ?_⟩
  exact ⟨hj, by norm_num, hL, hρ0, hρ.trans hζ8, lt_of_lt_of_le hℓ₀ hℓ,
    fun ζ hζb => h N R hP hN hm0 hm hℓ hρ0 hρ j hj ζ hζb⟩

/-- The covariance of the last step along the raw state. -/
def stCovN (R : RGPar 2 L N) (j : ℕ) (st : RawSt 2 L N) : Matrix (Lam 2 L N) (Lam 2 L N) ℂ :=
  lastCov R j (Function.update st.ζ j (stZeta R st))

theorem covN {R : RGPar 2 L N} {j : ℕ} {st : RawSt 2 L N} (hV : ValidLast R j)
    (H : RawInv R j st) :
    GoodCov2 j (fscale (stZ' R st) * R.ℓ / 4) (stCovN R j st) ∧ TInv (stCovN R j st) ∧
      CSym (stCovN R j st) ∧ ∀ x y, stCovN R j st x y = stCovN R j st y x := by
  have h := hV.2.2.2.2.2.2 _ (RawInv.zeta'_le hV.2.2.2.1 H)
  rw [RawInv.prod_zeta' H] at h
  exact h

/-- The final-scale object produced by the last step. -/
structure LastOut (d L N : ℕ) [NeZero L] where
  /-- `Z_N = Z_{N-1}(1 + ζ_{N-1})`. -/
  Z : ℂ
  /-- The dressed history `ζ_0, …, ζ_{N-1}`. -/
  ζ : ℕ → ℂ
  /-- The covariance `C'^{≠0}_N` that was integrated (raw, nonzero modes). -/
  C : Matrix (Lam d L N) (Lam d L N) ℂ
  /-- The raw couplings `κ_N` of `V_N`. -/
  κ : Coup
  /-- `V_N(B)` on the blocks of scale `N - 1`. -/
  V : Fam d L N
  /-- `u_N(Λ)`. -/
  u : ℂ
  /-- `𝒲_N(B)` on the blocks of scale `N - 1`. -/
  W : Fam d L N
  /-- `K_N(Λ)`. -/
  K : EvR (Lam d L N)

/-- **The raw last step** (integrating `C'^{≠0}_N` only). -/
def rawStepN (R : RGPar 2 L N) (j : ℕ) (st : RawSt 2 L N) (g μ : ℝ) (D : Fam 2 L N)
    (K : Act 2 L N) : LastOut 2 L N where
  Z := stZ' R st
  ζ := Function.update st.ζ j (stZeta R st)
  C := stCovN R j st
  κ := (stKap R j st g μ).shift 2 (stCovN R j st 0 0)
    (stCovN R j st (dirVec (Sum.inl 0)) 0 - stCovN R j st 0 0)
  V := fun b => VpN (stCovN R j st) (stVf R j st g μ) b
  u := uXN j (stCovN R j st) (stVf R j st g μ) univ
  W := fun b => Sb j (stCovN R j st) (stVf R j st g μ) (st.Wl + D) b
  K := KN j (stCovN R j st) (stVf R j st g μ) (st.Wl + D) (Kflat j (stDelta R j st) K) univ

/-! ### The identity -/

theorem prod_smul_aux {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℂ)
    (G : ι → EvR (Lam d L N)) : ∏ i ∈ s, (c i • G i) = (∏ i ∈ s, c i) • ∏ i ∈ s, G i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [prod_insert ha, prod_insert ha, prod_insert ha, ih, smul_mul_smul_comm]

/-- `I_N^Λ = e^{-u_N(Λ)} ∏_B e^{-V_N(B)} (1 + 𝒲_N(B))`. -/
theorem bpow_IpN_univ (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V W : Fam d L N) :
    bpow j (IpN j C V W) univ = Complex.exp (-uXN j C V univ) •
      ∏ b ∈ blockIdx (L := L) (N := N) j, gexp (-VpN C V b) * (1 + Sb j C V W b) := by
  classical
  rw [bpow, uXN, ← sum_neg_distrib, Complex.exp_sum]
  simp only [IpN]
  rw [prod_smul_aux]
  rfl

/-- **The last step**: `𝔼_C θ Z_{N-1} = e^{-u_N(Λ)} (∏_B e^{-V_N(B)}(1 + 𝒲_N(B)) + K_N(Λ))`, with
`C = C'^{≠0}_N` and `Z_{N-1} = ∑_X I^{Λ∖X} K♭(X)`, `I(B) = e^{-V♭(B)}(1 + 𝒲(B))`. -/
theorem rawStepN_ZVK (R : RGPar 2 L N) {j : ℕ} (hj : j + 1 = N) (st : RawSt 2 L N) (g μ : ℝ)
    (D : Fam 2 L N) (K : Act 2 L N) :
    ECCE (rawStepN R j st g μ D K).C
        (thetaE (gZ j (Ib (stVf R j st g μ) (st.Wl + D)) (Kflat j (stDelta R j st) K))) =
      Complex.exp (-(rawStepN R j st g μ D K).u) •
        ((∏ b ∈ blockIdx (L := L) (N := N) j,
          gexp (-(rawStepN R j st g μ D K).V b) * (1 + (rawStepN R j st g μ D K).W b)) +
          (rawStepN R j st g μ D K).K) := by
  show ECCE (stCovN R j st) _ = _
  rw [KN_ZVK_last j _ _ _ _ hj, bpow_IpN_univ, smul_add]
  rfl

/-! ### The couplings -/

/-- **`V_N(B) = V_{κ_N}(B)`** with `κ_N = κ♭.shift(c₀, δ)`, for a symmetric, lattice-invariant
covariance. -/
theorem rawStepN_V (R : RGPar 2 L N) (j : ℕ) (st : RawSt 2 L N) (g μ : ℝ) (D : Fam 2 L N)
    (K : Act 2 L N) (hCs : CSym (stCovN R j st))
    (hCsym : ∀ x y, stCovN R j st x y = stCovN R j st y x) (b : Fin 2 → ℕ) :
    ((rawStepN R j st g μ D K).V b : Alg 2 L N) =
      Vcoup (rawStepN R j st g μ D K).κ (blockSet j b) := by
  set C := stCovN R j st
  obtain ⟨c₀, δ, hc₀, hδ, hδ'⟩ := covProps (by norm_num : 1 ≤ 2) hCs hCsym
  have e0 : C 0 0 = c₀ := hc₀ 0
  have e1 : C (dirVec (Sum.inl 0)) 0 - C 0 0 = δ := by
    have := hδ 0 (Sum.inl 0); rw [zero_add] at this; rw [this, e0]; ring
  have hκ : (rawStepN R j st g μ D K).κ = (stKap R j st g μ).shift 2 c₀ δ := by
    show (stKap R j st g μ).shift 2 (C 0 0) (C (dirVec (Sum.inl 0)) 0 - C 0 0) = _
    rw [e1, e0]
  rw [hκ]
  set B := blockSet (L := L) (N := N) j b
  obtain ⟨r₁, h₁⟩ := expLC_Vcoup hc₀ hδ hδ' (stKap R j st g μ) B
  have hVκ : (stVf R j st g μ b : Alg 2 L N) = Vcoup (stKap R j st g μ) B := by
    rw [stVf_eq_kap]; rfl
  have hVpr : (Vpr C (stVf R j st g μ) b : Alg 2 L N) =
      Vcoup ((stKap R j st g μ).shift 2 c₀ δ) B + r₁ • 1 := by
    rw [Vpr, coe_EthE, hVκ, h₁]
  have hup : upN C (stVf R j st g μ) b = r₁ := by
    rw [upN, hVpr, map_add, eps_Vcoup, map_smul, map_one, smul_eq_mul, mul_one, zero_add]
  show (VpN C (stVf R j st g μ) b : Alg 2 L N) = _
  rw [VpN, AddSubgroupClass.coe_sub, Subalgebra.coe_algebraMap, hVpr, hup,
    Algebra.algebraMap_eq_smul_one, add_sub_cancel_right]

/-- `V_N(Λ) = V_{κ_N}(Λ)`. -/
theorem rawStepN_VN (R : RGPar 2 L N) (j : ℕ) (st : RawSt 2 L N) (g μ : ℝ) (D : Fam 2 L N)
    (K : Act 2 L N) (hCs : CSym (stCovN R j st))
    (hCsym : ∀ x y, stCovN R j st x y = stCovN R j st y x) :
    (VN j (rawStepN R j st g μ D K).C (stVf R j st g μ) : Alg 2 L N) =
      Vcoup (rawStepN R j st g μ D K).κ univ := by
  have h : ∀ b, (VpN (stCovN R j st) (stVf R j st g μ) b : Alg 2 L N) =
      Vcoup (rawStepN R j st g μ D K).κ (blockSet j b) := rawStepN_V R j st g μ D K hCs hCsym
  show ((∑ b ∈ blockIdx (L := L) (N := N) j, VpN (stCovN R j st) (stVf R j st g μ) b :
    EvR (Lam 2 L N)) : Alg 2 L N) = _
  rw [AddSubmonoidClass.coe_finsetSum, sum_congr rfl fun b _ => h b]
  simp only [Vcoup]
  rw [unif_sum _ 0 _ _ _ (pairwiseDisjoint_blockSet j _), mul_zero]
  show unif 0 _ _ ((blocks j univ).biUnion (blockSet j)) = _
  rw [biUnion_blocks (isPolymer_univ j)]

/-- **The normalised final couplings.** With inactive clamps (`|z/Z|, |y/Z| ≤ η`, `2η ≤ ρ`) and
`|m²| L^{2j} ≤ 1`, at `j + 1 = N`, for a covariance with `GoodCov2` at Gram scale `s_N ℓ/4`:
`|z_N/Z_N|, |y_N/Z_N| ≤ ℓ² g/14`, `|L^{2N} ν_N/Z_N - L² μ| ≤ (16/7) L² η + ℓ² g/7` and
`|g_N/Z_N²| ≤ (8/7) g`. -/
theorem coupN_bounds (R : RGPar 2 L N) {j : ℕ} (hj : j + 1 = N) (st : RawSt 2 L N) (g μ : ℝ)
    (D : Fam 2 L N) (K : Act 2 L N) (hZ : st.Z ≠ 0) (hρ0 : 0 ≤ R.ρ) (hg0 : 0 ≤ g)
    (hm : |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1) (η : ℝ) (hz : ‖st.z / st.Z‖ ≤ η)
    (hy : ‖st.y / st.Z‖ ≤ η) (hη : 2 * η ≤ R.ρ) (hρ8 : R.ρ ≤ 1 / 8)
    (hC : GoodCov2 j (fscale (stZ' R st) * R.ℓ / 4) (stCovN R j st)) (hCs : CSym (stCovN R j st))
    (hCsym : ∀ x y, stCovN R j st x y = stCovN R j st y x) :
    let out := rawStepN R j st g μ D K
    ‖out.κ.z / out.Z‖ ≤ R.ℓ ^ 2 / 14 * g ∧ ‖out.κ.y / out.Z‖ ≤ R.ℓ ^ 2 / 14 * g ∧
      ‖(L : ℂ) ^ (2 * (j + 1)) * out.κ.nu / out.Z - (L : ℂ) ^ 2 * (μ : ℂ)‖ ≤
        16 / 7 * (L : ℝ) ^ 2 * η + R.ℓ ^ 2 / 7 * g ∧
      ‖out.κ.g / out.Z ^ 2‖ ≤ 8 / 7 * g := by
  intro out
  set C := stCovN R j st
  obtain ⟨c₀, δ, hc₀, hδ, hδ'⟩ := covProps (by norm_num : 1 ≤ 2) hCs hCsym
  have e0 : C 0 0 = c₀ := hc₀ 0
  have e1 : C (dirVec (Sum.inl 0)) 0 - C 0 0 = δ := by
    have := hδ 0 (Sum.inl 0); rw [zero_add] at this; rw [this, e0]; ring
  obtain ⟨hc0b, hδb⟩ := cov_c0_delta_le hC hc₀ hδ hδ'
  have hη0 : 0 ≤ η := (norm_nonneg _).trans hz
  -- inactive clamps
  have hzy : ‖(st.z + st.y) / st.Z‖ ≤ R.ρ := by
    rw [add_div]; exact (norm_add_le _ _).trans (by linarith)
  have hyc : ‖st.y / st.Z‖ ≤ R.ρ := by linarith
  have hζ : stZeta R st = (st.z + st.y) / st.Z := by
    unfold stZeta absorbZeta; rw [clampDisk_of_le hzy]
  have hζη : ‖stZeta R st‖ ≤ 2 * η := by
    rw [hζ, add_div]; exact (norm_add_le _ _).trans (by linarith)
  have hζ8 : ‖stZeta R st‖ ≤ 1 / 8 := by linarith
  have hκz : (stKap R j st g μ).z = 0 := by
    show st.z + stYc R st - stA R st = 0
    rw [stYc_eq hZ hyc, stA_eq hZ hzy]; ring
  have hκy : (stKap R j st g μ).y = 0 := by
    show st.y - stYc R st = 0
    rw [stYc_eq hZ hyc]; ring
  have hκν : (stKap R j st g μ).nu = stNu R j st μ - stA R st * R.msq := rfl
  have hκg : (stKap R j st g μ).g = stGr R j st g μ * stZ' R st ^ 2 := rfl
  set Z' := stZ' R st with hZ'def
  set gr := stGr R j st g μ
  have hZ' : Z' ≠ 0 := mul_ne_zero hZ (one_add_ne_zero (by linarith))
  have hZ'n : 0 < ‖Z'‖ := norm_pos_iff.2 hZ'
  have hgr : ‖gr‖ ≤ 8 / 7 * g := by
    have := norm_stGr_le R j st g μ; rwa [abs_of_nonneg hg0] at this
  have hℓC2 : (fscale Z' * R.ℓ / 4) ^ 2 = R.ℓ ^ 2 / (16 * ‖Z'‖) := by
    rw [div_pow, mul_pow, fscale_sq]; field_simp; ring
  rw [hℓC2] at hc0b hδb
  have hL1 : (1 : ℝ) ≤ ((L : ℝ) ^ (j + 1)) ^ 2 := by
    have : (1 : ℝ) ≤ L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    exact one_le_pow₀ (one_le_pow₀ this)
  have hLpos : (0 : ℝ) < ((L : ℝ) ^ (j + 1)) ^ 2 := by linarith
  have hδ2 : ‖δ‖ ≤ R.ℓ ^ 2 / (16 * ‖Z'‖) / 2 := by
    refine hδb.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : 0 ≤ R.ℓ ^ 2 / (16 * ‖Z'‖) := by positivity
    nlinarith
  have hκ : out.κ = (stKap R j st g μ).shift 2 c₀ δ := by
    show (stKap R j st g μ).shift 2 (C 0 0) (C (dirVec (Sum.inl 0)) 0 - C 0 0) = _
    rw [e1, e0]
  have hZout : out.Z = Z' := rfl
  rw [hκ, hZout]
  simp only [Coup.shift, hκz, hκy, hκν, hκg]
  -- `|g_r| |Z'| x` with `x ≤ ℓ²/(16|Z'|)`
  have key : ∀ x : ℝ, 0 ≤ x → x ≤ R.ℓ ^ 2 / (16 * ‖Z'‖) → ‖gr‖ * ‖Z'‖ * x ≤ R.ℓ ^ 2 / 14 * g := by
    intro x hx0 hx
    have h1 : ‖Z'‖ * x ≤ R.ℓ ^ 2 / 16 := by
      rw [le_div_iff₀ (by positivity)] at hx
      rw [le_div_iff₀ (by norm_num)]; nlinarith
    calc ‖gr‖ * ‖Z'‖ * x = ‖gr‖ * (‖Z'‖ * x) := by ring
      _ ≤ 8 / 7 * g * (R.ℓ ^ 2 / 16) := by gcongr
      _ = R.ℓ ^ 2 / 14 * g := by ring
  have hgZ : ∀ c : ℂ, ‖(0 - gr * Z' ^ 2 * c) / Z'‖ = ‖gr‖ * ‖Z'‖ * ‖c‖ := by
    intro c
    rw [zero_sub, neg_div, norm_neg, norm_div, norm_mul, norm_mul, norm_pow]
    field_simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hgZ]; exact key _ (norm_nonneg _) hc0b
  · rw [hgZ]; exact key _ (norm_nonneg _) (hδ2.trans (by
      have : 0 ≤ R.ℓ ^ 2 / (16 * ‖Z'‖) := by positivity
      linarith))
  · -- the mass coupling
    have hNu : (L : ℂ) ^ (2 * (j + 1)) * stNu R j st μ / Z' = (L : ℂ) ^ 2 * (μ : ℂ) := by
      unfold stNu
      have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne L
      rw [← hZ'def]
      field_simp
      ring
    have e : (L : ℂ) ^ (2 * (j + 1)) * (stNu R j st μ - stA R st * ↑R.msq +
        2 * ((2 : ℕ) : ℂ) * (gr * Z' ^ 2) * δ) / Z' - (L : ℂ) ^ 2 * (μ : ℂ) =
        -((L : ℂ) ^ (2 * (j + 1)) * (stA R st * ↑R.msq) / Z') +
          4 * ((L : ℂ) ^ (2 * (j + 1)) * gr * Z' * δ) := by
      rw [← hNu]; field_simp; push_cast; ring
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · -- `|a m² L^{2N}/Z'| ≤ (16/7) L² η`
      rw [norm_neg, norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_natCast,
        Complex.norm_real, Real.norm_eq_abs]
      have hA : ‖stA R st‖ / ‖Z'‖ ≤ 8 / 7 * (2 * η) := by
        have e2 : stA R st = st.Z * stZeta R st := rfl
        have h7 : 7 / 8 ≤ ‖1 + stZeta R st‖ := by linarith [norm_one_add_ge (ζ := stZeta R st)]
        rw [e2, hZ'def, norm_mul, norm_stZ', div_le_iff₀ (by positivity)]
        have hZn : 0 < ‖st.Z‖ := norm_pos_iff.2 hZ
        have : ‖stZeta R st‖ ≤ 8 / 7 * (2 * η) * ‖1 + stZeta R st‖ := by nlinarith
        nlinarith
      have hpow : (L : ℝ) ^ (2 * (j + 1)) = (L : ℝ) ^ 2 * ((L : ℝ) ^ j) ^ 2 := by ring
      calc (L : ℝ) ^ (2 * (j + 1)) * (‖stA R st‖ * |R.msq|) / ‖Z'‖
          = (L : ℝ) ^ 2 * (‖stA R st‖ / ‖Z'‖) * (|R.msq| * ((L : ℝ) ^ j) ^ 2) := by
            rw [hpow]; field_simp
        _ ≤ (L : ℝ) ^ 2 * (8 / 7 * (2 * η)) * 1 := by gcongr
        _ = 16 / 7 * (L : ℝ) ^ 2 * η := by ring
    · -- `|4 L^{2N} g_r Z' δ| ≤ ℓ² g/7`
      rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
      have h4 : ‖(4 : ℂ)‖ = 4 := by simp
      rw [h4]
      have hδL : ((L : ℝ) ^ (j + 1)) ^ 2 * ‖δ‖ ≤ R.ℓ ^ 2 / (16 * ‖Z'‖) / 2 := by
        rw [le_div_iff₀ (by positivity)] at hδb
        rw [le_div_iff₀ (by norm_num)]
        have : 0 ≤ R.ℓ ^ 2 / (16 * ‖Z'‖) := by positivity
        nlinarith
      have hpow : (L : ℝ) ^ (2 * (j + 1)) = ((L : ℝ) ^ (j + 1)) ^ 2 := by ring
      rw [hpow]
      have := key (2 * (((L : ℝ) ^ (j + 1)) ^ 2 * ‖δ‖)) (by positivity) (by linarith)
      nlinarith
  · rw [norm_div, norm_mul, norm_pow, mul_div_assoc, div_self (by positivity), mul_one]
    exact hgr

end LastN

end

end Step2
