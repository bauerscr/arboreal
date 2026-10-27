import PtCorr2.Pair.PairRecAB
import Obs2.Pair.SeedAB

/-!
# The `ab` recursion from the seed without the `r²` a priori condition (linear regime)

The `ab` sector of the reduced history is linear in the `ab` data given the bulk. The a priori
condition `8k_{j₀} ≤ 64B r_{j₀}² c_W m_{j₀}` of `obs_histFromAB` asks the seed `K'_{j₀}` to be
`O(r²)` relative to the `V`-size `m`; the reduced seed is `O(1)·M_aM_b` (`kRed_ab_poly_le_split`),
and a remainder after an exact seed split is still only `O(ǧ)M_aM_b`. Here the condition is
replaced by `8k ≤ c_k m` (any fixed `c_k`), at the price of `c_k` in the contraction factor
`θ₀ + C₁(2+2c_b+c_k)r` (small for `r` small after `c_k` is fixed):

* **`kobs_raw_stepABL`**, `KObsBoundsABL`, `kobs_bounds_ABL`: `kobs_raw_stepAB` with `8k ≤ c_k m`
  (from `Obs2.kobsK_stepWABL`);
* **`kobs_hist_stepABL`**: `kobs_hist_stepAB` with `8k ≤ c_k m`;
* `kseqF_leL`: the linear a priori condition `8k_j ≤ c_k m_j` propagates
  (`2(θc_k + 8Br_j²) ≤ c_k`, `m_j ≤ 2m_{j+1}`);
* **`kseqF_sum_le`**: `∑_{j₀≤k<n} k_k ≤ 2(k₀ + B∑_k r_k²m_k)` for `θ ≤ 1/2` (summability of the
  seed and of the sources: what `∑_k ŝ^q_k` in `PairErrSizesR` needs);
* **`obs_histFromABL`**: `obs_histFromAB` with `8k₀ ≤ c_k m_{j₀}` in place of
  `8k₀ ≤ 64B r_{j₀}²c_W m_{j₀}`; for `j₀ ≤ j ≤ n`: `8 kseqF_j ≤ c_k c_W m_j`,
  `‖𝒲_j(B)‖ ≤ c_W r_j m_j`, `A^{(|𝓑_j(X)|-4)_+}‖K_j(X)‖ ≤ kseqF (8θ̄) B r (c_W m) j₀ k₀ j`
  (`kseqF_eq_sum`: `θ̄^{j-j₀}`-decay of the seed).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

variable {L N : ℕ} [NeZero L]

set_option maxHeartbeats 2000000 in
/-- **The `ab` `K^{obs}` step at the raw level, linear regime** (`8k ≤ c_k m`). -/
theorem kobs_raw_stepABL : ∃ (C₀ η : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧ 0 < η ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) (j : ℕ), ValidCore R j → ∀ st : RawSt 2 L N, RawInv R j st →
    ∀ (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N), D ∈ BSub (L := L) (N := N) j →
      K ∈ ASub (L := L) (N := N) j → |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1 → 0 ≤ g →
    ∀ ηz : ℝ, ‖st.z / st.Z‖ ≤ ηz → ‖st.y / st.Z‖ ≤ ηz → 2 * ηz ≤ R.ρ →
      8 * cM * R.ℓ ^ 2 * ηz ≤ 1 / 2 →
    ∀ (c : Obs.Case) (P : ObsPts 2 L N) (w : Wt), w.Sub → w.a ≠ ⊤ → w.b ≠ ⊤ → w.ab ≠ ⊤ →
    ∀ o : ObsSt c L N, o.IsObs → ObsLocInv P j o → ObsSymInv j o → ObsAnchInv P j o →
    ∀ wl dd kb r m k cb ck : ℝ, 0 ≤ wl → 0 ≤ dd → 0 ≤ kb → 0 < r → 0 < m → 0 ≤ k →
      0 ≤ cb → 0 ≤ ck →
      Fnorm j (fscale st.Z * R.ℓ) st.Wl ≤ ENNReal.ofReal wl →
      Fnorm j (fscale st.Z * R.ℓ) D ≤ ENNReal.ofReal dd →
      Knorm j (fscale st.Z * R.ℓ) A K ≤ ENNReal.ofReal kb →
      cM * R.ℓ ^ 2 * (2 * |μ| + 2 * ηz) + 8 * R.ℓ ^ 4 * g ≤ r → wl + dd ≤ r ^ 2 →
      r ≤ 1 → r ≤ ε₀ → 8 * kb ≤ cb * r ^ 3 → 8 * k ≤ ck * m →
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
  obtain ⟨C₀, η, L₀, hC₀, hη, h⟩ := kobsK_stepWABL 2 le_rfl
  refine ⟨C₀, η, L₀, hC₀, hη, fun L _ hL => ?_⟩
  obtain ⟨A₀, hA₀, h⟩ := h L hL 2 one_le_two
  refine ⟨2 * A₀, by linarith, fun A hA => ?_⟩
  obtain ⟨ε₀, C₁, hε₀, hC₁, h⟩ := h (A / 2) (by linarith)
  refine ⟨ε₀, C₁, hε₀, hC₁, ?_⟩
  intro N R j hV st H g μ D K hD hK hm hg0 ηz hz hy hηρ hηs c P w hwS hwa hwb hwab o ho hloc hsym hanc
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
  have hwsub : w.Sub := hwS
  have hVo' : ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (fscale st.Z * R.ℓ) (fullV R j st g μ o b) ≤ ENNReal.ofReal m :=
    fun b hb => (oTo_emb_add_le w j _ _ _).trans (hVo b hb)
  have hWo' : ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (fscale st.Z * R.ℓ) (fullW st D o b) ≤ ENNReal.ofReal (r * m) :=
    fun b hb => (oTo_emb_add_le w j _ _ _).trans (hWo b hb)
  have hKo' : ∀ X, IsConn j X → ENNReal.ofReal ((A / 2) ^ (nb j X - 2 ^ 2)) *
      oTo w j (fscale st.Z * R.ℓ) (fullK R j st K o X) ≤ ENNReal.ofReal (8 * k) := by
    intro X hX
    refine (oTo_fullK_leAB R j st K o w hwS hsℓ hA0 hδΔ0 (by linarith) hΔ X).trans ?_
    rw [ENNReal.ofReal_mul (by norm_num)]
    exact mul_le_mul_left' (hKo X hX) _
  -- apply the step
  have HL := olocS_full R P g μ hV H hD hK hloc
  have HS := osymS_full R g μ hV H hD hK hsym
  have HA := oanchS_full R P g μ (st := st) (D := D) (K := K) hanc
  have HAb := HA.toAb
  have key := h N j (by omega) (fscale st.Z * R.ℓ) (s' * R.ℓ) (s' * R.ℓ / 4) hsℓ
    (mul_pos hs' hℓ) (by positivity) hsum (stCov R j st) hC c P w hwS hwa hwb hwab
    (fullV R j st g μ o) (fullW st D o) (fullK R j st K o) HAb.hV HAb.hW HAb.hK HA.hK
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

/-- The conclusion of `kobs_raw_stepABL` for given constants. -/
def KObsBoundsABL (L : ℕ) [NeZero L] (A C₀ η ε₀ C₁ : ℝ) : Prop :=
    ∀ (N : ℕ) (R : RGPar 2 L N) (j : ℕ), ValidCore R j → ∀ st : RawSt 2 L N, RawInv R j st →
    ∀ (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N), D ∈ BSub (L := L) (N := N) j →
      K ∈ ASub (L := L) (N := N) j → |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1 → 0 ≤ g →
    ∀ ηz : ℝ, ‖st.z / st.Z‖ ≤ ηz → ‖st.y / st.Z‖ ≤ ηz → 2 * ηz ≤ R.ρ →
      8 * cM * R.ℓ ^ 2 * ηz ≤ 1 / 2 →
    ∀ (c : Obs.Case) (P : ObsPts 2 L N) (w : Wt), w.Sub → w.a ≠ ⊤ → w.b ≠ ⊤ → w.ab ≠ ⊤ →
    ∀ o : ObsSt c L N, o.IsObs → ObsLocInv P j o → ObsSymInv j o → ObsAnchInv P j o →
    ∀ wl dd kb r m k cb ck : ℝ, 0 ≤ wl → 0 ≤ dd → 0 ≤ kb → 0 < r → 0 < m → 0 ≤ k →
      0 ≤ cb → 0 ≤ ck →
      Fnorm j (fscale st.Z * R.ℓ) st.Wl ≤ ENNReal.ofReal wl →
      Fnorm j (fscale st.Z * R.ℓ) D ≤ ENNReal.ofReal dd →
      Knorm j (fscale st.Z * R.ℓ) A K ≤ ENNReal.ofReal kb →
      cM * R.ℓ ^ 2 * (2 * |μ| + 2 * ηz) + 8 * R.ℓ ^ 4 * g ≤ r → wl + dd ≤ r ^ 2 →
      r ≤ 1 → r ≤ ε₀ → 8 * kb ≤ cb * r ^ 3 → 8 * k ≤ ck * m →
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
            C₁ * (8 + 2 * cb + cb ^ 2)) * r ^ 2 * m)

/-- **The constants of the `ab` `K^{obs}` step.** -/
theorem kobs_bounds_ABL : ∃ (C₀ η : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧ 0 < η ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧ KObsBoundsABL L A C₀ η ε₀ C₁ :=
  kobs_raw_stepABL

/-- **The linear a priori condition propagates from `j₀`**: `8k_j ≤ c_k m_j`. -/
theorem kseqF_leL {θ B ck : ℝ} {r m : ℕ → ℝ} {j₀ : ℕ} {k₀ : ℝ} (n : ℕ) (hθ : 0 ≤ θ)
    (hB : 0 ≤ B) (hck : 0 ≤ ck) (hm : ∀ j, 0 ≤ m j)
    (hc : ∀ j, j₀ ≤ j → j < n → 2 * (θ * ck + 8 * B * r j ^ 2) ≤ ck)
    (hm' : ∀ j, j₀ ≤ j → j < n → m j ≤ 2 * m (j + 1)) (h0 : 8 * k₀ ≤ ck * m j₀) :
    ∀ j, j₀ ≤ j → j ≤ n → 8 * kseqF θ B r m j₀ k₀ j ≤ ck * m j := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => intro _; rw [kseqF_start]; exact h0
  | succ j hjj ih =>
    intro hj
    have ih := ih (by omega)
    rw [kseqF_succ θ B r m k₀ hjj]
    have hcj := hc j hjj (by omega)
    have hmj := hm' j hjj (by omega)
    have h1 : θ * (8 * kseqF θ B r m j₀ k₀ j) ≤ θ * (ck * m j) := mul_le_mul_of_nonneg_left ih hθ
    set p := θ * ck + 8 * B * r j ^ 2 with hp
    have hp0 : 0 ≤ p := by
      positivity
    have hA : p * m j ≤ p * (2 * m (j + 1)) := mul_le_mul_of_nonneg_left hmj hp0
    have hB' : p * (2 * m (j + 1)) ≤ ck * m (j + 1) := by
      have := mul_le_mul_of_nonneg_right hcj (hm (j + 1))
      linarith
    have e : 8 * (θ * kseqF θ B r m j₀ k₀ j + B * r j ^ 2 * m j) =
        θ * (8 * kseqF θ B r m j₀ k₀ j) + 8 * B * r j ^ 2 * m j := by ring
    have e2 : p * m j = θ * (ck * m j) + 8 * B * r j ^ 2 * m j := by rw [hp]; ring
    rw [e]
    linarith

/-- **The summed comparison sequence**: for `0 ≤ θ ≤ 1/2`,
`∑_{j₀≤k<n} k_k ≤ 2(k₀ + B∑_{j₀≤k<n} r_k²m_k)` (the seed and the sources are summable). -/
theorem kseqF_sum_le {θ B : ℝ} {r m : ℕ → ℝ} {j₀ : ℕ} {k₀ : ℝ} (hθ : 0 ≤ θ) (hθ2 : θ ≤ 1 / 2)
    (hB : 0 ≤ B) (hm : ∀ j, 0 ≤ m j) (hk₀ : 0 ≤ k₀) (n : ℕ) (hn : j₀ ≤ n) :
    ∑ k ∈ Finset.Ico j₀ n, kseqF θ B r m j₀ k₀ k ≤
      2 * (k₀ + B * ∑ k ∈ Finset.Ico j₀ n, r k ^ 2 * m k) := by
  suffices h : ∑ k ∈ Finset.Ico j₀ n, kseqF θ B r m j₀ k₀ k + 2 * kseqF θ B r m j₀ k₀ n ≤
      2 * (k₀ + B * ∑ k ∈ Finset.Ico j₀ n, r k ^ 2 * m k) by
    have := kseqF_nonneg (r := r) (j₀ := j₀) hθ hB hm hk₀ n
    linarith
  induction n, hn using Nat.le_induction with
  | base => simp [kseqF_start]
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn, Finset.sum_Ico_succ_top hn, kseqF_succ θ B r m k₀ hn]
    have h0 := kseqF_nonneg (r := r) (j₀ := j₀) hθ hB hm hk₀ n
    have h1 : θ * kseqF θ B r m j₀ k₀ n ≤ 1 / 2 * kseqF θ B r m j₀ k₀ n :=
      mul_le_mul_of_nonneg_right hθ2 h0
    have e : B * (∑ k ∈ Finset.Ico j₀ n, r k ^ 2 * m k + r n ^ 2 * m n) =
        B * ∑ k ∈ Finset.Ico j₀ n, r k ^ 2 * m k + B * r n ^ 2 * m n := by ring
    rw [e]
    nlinarith

section Hist

variable {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

set_option maxHeartbeats 4000000 in
/-- **One step of the `K^{obs}` recursion along the history from `j₀`, linear regime.** -/
theorem kobs_hist_stepABL {C₀ η ε₀ C₁ : ℝ} (hKB : KObsBoundsABL L R.A C₀ η ε₀ C₁)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    {c : Obs.Case} (P : ObsPts 2 L N) (w : Wt) (hws : w.Sub) (hwa : w.a ≠ ⊤) (hwb : w.b ≠ ⊤)
    (hwab : w.ab ≠ ⊤)
    {j₀ : ℕ} (o₀ : ObsSt c L N) (h0 : o₀.IsObs) (hl0 : ObsLocInv P j₀ o₀)
    (hs0 : ObsSymInv j₀ o₀) (ha0 : ObsAnchInv P j₀ o₀)
    (t : Flow2.Hist.Seq (Xs R)) (j : ℕ) (hjj : j₀ ≤ j) (hj : j < Nh)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t)
    (ck m k : ℝ) (hck : 0 ≤ ck) (hm0 : 0 < m) (hk0 : 0 ≤ k)
    (hε1 : cR R Λ cm C₂ * ε ≤ 1) (hεε : cR R Λ cm C₂ * ε ≤ ε₀)
    (hεk : (8 * cx κ cT + ck) * (cR R Λ cm C₂ * ε) ≤ ε₀)
    (hk8 : 8 * k ≤ ck * m)
    (hVo : ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (histS R j t) ((obsHistFrom R P j₀ o₀ j t).V b) ≤ ENNReal.ofReal m)
    (hWo : ∀ b ∈ blockIdx (L := L) (N := N) j, oTo w j (histS R j t) ((obsHistFrom R P j₀ o₀ j t).W b) ≤
      ENNReal.ofReal (cR R Λ cm C₂ * (t j).1 * m))
    (hKo : ∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
      oTo w j (histS R j t) ((obsHistFrom R P j₀ o₀ j t).K X) ≤ ENNReal.ofReal k) :
    ∀ U : Finset (Lam 2 L N), IsConn (j + 1) U →
      ENNReal.ofReal (R.A ^ (nb (j + 1) U - 2 ^ 2)) *
        oTo w (j + 1) (histS R (j + 1) t) ((obsHistFrom R P j₀ o₀ (j + 1) t).K U) ≤
      ENNReal.ofReal ((kθ0 L R.A C₀ η + C₁ * (2 + 2 * (8 * cx κ cT) + ck) *
          (cR R Λ cm C₂ * (t j).1)) * (8 * k) +
        kB (kθ0 L R.A C₀ η) C₁ (8 * cx κ cT) * (cR R Λ cm C₂ * (t j).1) ^ 2 * m) := by
  have hℓ : 0 < R.ℓ := Fact.out
  have hVj := hV j hj
  have hρ1 : R.ρ < 1 := by linarith [hVj.2.2.2.2.1]
  have HI := rawInv_hist R hVj.2.2.2.1 j (fun i hi => hV i (by omega)) t
  set st := rawHist R j t with hst
  have hZ : st.Z ≠ 0 := HI.Z_ne_zero hρ1
  obtain ⟨hz, hy, hWl⟩ := apriori R hSB hV hm hβ hδ1 H j hj.le t ht
  obtain ⟨hg, hgε, hμ, hx⟩ := ht.1 j le_rfl
  set g := (t j).1 with hgdef
  set μ := (t j).2.1
  set x := (t j).2.2
  have hcz : 0 ≤ cZ R := by unfold cZ; positivity
  have hcv : 0 ≤ cV R Λ cm := by unfold cV; have := H.hcmu; positivity
  have hcw : 0 ≤ cW R Λ cm C₂ := by unfold cW; have := H.hC₂; positivity
  have hg1 : g ≤ 1 := hgε.trans H.hε1
  have hx1 : ‖x.1‖ ≤ cx κ cT * g ^ 3 := (norm_fst_le x).trans hx
  have hx2 : ‖x.2‖ ≤ cx κ cT * g ^ 3 := (norm_snd_le x).trans hx
  have hg3 : g ^ 3 ≤ ε * g ^ 2 := by
    rw [pow_succ]; nlinarith [sq_nonneg g, mul_le_mul_of_nonneg_left hgε (sq_nonneg g)]
  have hdd : ‖x.1‖ ≤ g ^ 2 := by
    have := H.h3; nlinarith [mul_le_mul_of_nonneg_left hg3 H.hcx, sq_nonneg g]
  have hv : cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g ≤ cV R Λ cm * g := by
    unfold cV
    have hM : 0 ≤ cM := Nat.cast_nonneg _
    have : 2 * |μ| + 2 * (cZ R * g) ≤ (2 * cmu Λ cm + 2 * cZ R) * g := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hM (sq_nonneg R.ℓ))]
  set r := cR R Λ cm C₂ * g with hr
  have hvr : cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g ≤ r := by
    refine hv.trans ?_; rw [hr]; unfold cR; nlinarith
  have hwr : cW R Λ cm C₂ * g ^ 2 + ‖x.1‖ ≤ r ^ 2 := by
    rw [hr]; unfold cR
    have h1 : cW R Λ cm C₂ + 1 ≤ (cV R Λ cm + cW R Λ cm C₂ + 2) ^ 2 := by nlinarith
    nlinarith [sq_nonneg g]
  have hη : 2 * (cZ R * g) ≤ R.ρ := by
    have := H.h1; nlinarith [mul_le_mul_of_nonneg_left hgε hcz]
  have hηs : 8 * cM * R.ℓ ^ 2 * (cZ R * g) ≤ 1 / 2 := by
    have := H.h2
    have hM : 0 ≤ cM := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hgε (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num :
      (0:ℝ) ≤ 8) hM) (sq_nonneg R.ℓ)) hcz)]
  -- the radius
  have hcR1 : 1 ≤ cR R Λ cm C₂ := by unfold cR; linarith
  have hgr : g ≤ r := by rw [hr]; nlinarith
  have hr0 : 0 < r := by rw [hr]; positivity
  have hrε : r ≤ cR R Λ cm C₂ * ε := mul_le_mul_of_nonneg_left hgε (by linarith)
  have hr1 : r ≤ 1 := hrε.trans hε1
  have hcx := H.hcx
  have hbr : 8 * ‖x.2‖ ≤ 8 * cx κ cT * r ^ 3 := by
    have : g ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ hg.le hgr 3
    nlinarith [mul_le_mul_of_nonneg_left this hcx]
  have hr3 : r ^ 3 ≤ r := by
    have : r ^ 2 ≤ 1 := pow_le_one₀ hr0.le hr1
    nlinarith
  have hεk' : 8 * ‖x.2‖ + r / m * (8 * k) ≤ ε₀ := by
    have h1 : r / m * (8 * k) ≤ ck * r := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hm0]
      have := mul_le_mul_of_nonneg_left hk8 hr0.le
      calc r * (8 * k) ≤ r * (ck * m) := this
        _ = ck * r * m := by ring
    have h2 : 8 * ‖x.2‖ ≤ 8 * cx κ cT * r := hbr.trans
      (mul_le_mul_of_nonneg_left hr3 (by positivity))
    have h3 : (8 * cx κ cT + ck) * r ≤ (8 * cx κ cT + ck) * (cR R Λ cm C₂ * ε) :=
      mul_le_mul_of_nonneg_left hrε (by positivity)
    nlinarith
  -- the observable invariants
  have hval := hist_valid R hV t (n := j + 1) (by omega)
  have hloc := obsLocInv_histFrom' R P hl0 t hjj fun i _ hi => hval i (by omega)
  have hsym := obsSymInv_histFrom' R P hs0 t hjj fun i _ hi => hval i (by omega)
  have hanc := obsAnchInv_histFrom' R P ha0 t hjj
  have hobs := obsHistFrom_isObs (R := R) (P := P) (j := j₀) h0 t j
  rw [obsHistFrom_succ hjj]
  exact hKB N R j hVj.toValidCore st HI g μ _ _ (rawD_mem R _ _) (rawK_mem R _ _) (hm j hj) hg.le
    (cZ R * g) hz hy hη hηs c P w hws hwa hwb hwab (obsHistFrom R P j₀ o₀ j t) hobs hloc hsym hanc
    (cW R Λ cm C₂ * g ^ 2) ‖x.1‖ ‖x.2‖ r m k (8 * cx κ cT) ck (by positivity) (norm_nonneg _)
    (norm_nonneg _) hr0 hm0 hk0 (by positivity) hck hWl (le_of_eq (Fnorm_rawD R HI.hu hZ x))
    (le_of_eq (Knorm_rawK R HI.hu hZ x)) hvr hwr hr1 (hrε.trans hεε) hbr hk8 hεk' hVo hWo hKo

set_option maxHeartbeats 4000000 in
/-- **The `ab` recursion along the history from `j₀`, linear regime** (`8k₀ ≤ c_k c_W m_{j₀}`). -/
theorem obs_histFromABL {C₀ η ε₀ C₁k : ℝ} (hKB : KObsBoundsABL L R.A C₀ η ε₀ C₁k) (hC₁k : 0 ≤ C₁k)
    (ck : ℝ) (hck : 0 ≤ ck)
    {Kw C₁ ε₁ : ℝ} (hWB : WObsBoundsAB L Kw C₁ ε₁) (hC₁ : 0 ≤ C₁)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    {c : Obs.Case} (P : ObsPts 2 L N) (w : Wt) (hws : w.Sub) (hwa : w.a ≠ ⊤) (hwb : w.b ≠ ⊤)
    (hwab : w.ab ≠ ⊤)
    {j₀ : ℕ} (o₀ : ObsSt c L N) (h0 : o₀.IsObs) (hl0 : ObsLocInv P j₀ o₀)
    (hs0 : ObsSymInv j₀ o₀) (ha0 : ObsAnchInv P j₀ o₀)
    (t : Flow2.Hist.Seq (Xs R)) (n : ℕ) (hn : n ≤ Nh)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε n t)
    (hθ0 : 0 ≤ kθ0 L R.A C₀ η) (hθ : kθ0 L R.A C₀ η ≤ 1 / 72)
    (hsm : C₁k * (2 + 2 * (8 * cx κ cT) + ck) *
      (cR R Λ cm C₂ * ε) ≤ 1 / 72)
    (hε1 : cR R Λ cm C₂ * ε ≤ 1) (hεε : cR R Λ cm C₂ * ε ≤ ε₀)
    (hεk : (8 * cx κ cT + ck) * (cR R Λ cm C₂ * ε) ≤ ε₀)
    (hBr : 32 * kB (kθ0 L R.A C₀ η) C₁k (8 * cx κ cT) * (cR R Λ cm C₂ * ε) ^ 2 ≤ ck)
    (hLw : Kw / L ≤ 1 / 12) (hC₁ε : C₁ * (cR R Λ cm C₂ * ε) ≤ 1 / 12)
    (hε₁ : cR R Λ cm C₂ * ε ≤ ε₁)
    (m : ℕ → ℝ) (hm0 : ∀ j, 0 < m j) (hm' : ∀ j, j₀ ≤ j → j < n → m j ≤ 2 * m (j + 1))
    (hVo : ∀ j, j₀ ≤ j → j < n → ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (histS R j t) ((obsHistFrom R P j₀ o₀ j t).V b) ≤ ENNReal.ofReal (m j))
    (hW0 : ∀ b ∈ blockIdx (L := L) (N := N) j₀, oTo w j₀ (histS R j₀ t) (o₀.W b) ≤
      ENNReal.ofReal ((4 * C₁ + 1) * (cR R Λ cm C₂ * (t j₀).1) * m j₀))
    (k₀ : ℝ) (hk₀ : 0 ≤ k₀)
    (hK0 : ∀ X, IsConn j₀ X → ENNReal.ofReal (R.A ^ (nb j₀ X - 2 ^ 2)) *
      oTo w j₀ (histS R j₀ t) (o₀.K X) ≤ ENNReal.ofReal k₀)
    (h8 : 8 * k₀ ≤ ck * ((4 * C₁ + 1) * m j₀)) :
    let B := kB (kθ0 L R.A C₀ η) C₁k (8 * cx κ cT)
    let θb := kθ0 L R.A C₀ η + C₁k * (2 + 2 * (8 * cx κ cT) + ck) * (cR R Λ cm C₂ * ε)
    let r := fun j => cR R Λ cm C₂ * (t j).1
    let cWc := 4 * C₁ + 1
    ∀ j, j₀ ≤ j → j ≤ n →
      8 * kseqF (8 * θb) B r (fun i => cWc * m i) j₀ k₀ j ≤ ck * (cWc * m j) ∧
      (∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo w j (histS R j t) ((obsHistFrom R P j₀ o₀ j t).W b) ≤
          ENNReal.ofReal (cWc * r j * m j)) ∧
      (∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
        oTo w j (histS R j t) ((obsHistFrom R P j₀ o₀ j t).K X) ≤
          ENNReal.ofReal (kseqF (8 * θb) B r (fun i => cWc * m i) j₀ k₀ j)) := by
  intro B θb r cWc
  have hcx := H.hcx
  have hcb : 0 ≤ 8 * cx κ cT := by positivity
  have hB : 0 ≤ B := by
    have h1 := mul_nonneg hθ0 hcb
    have h2 := mul_nonneg hC₁k (by positivity : (0 : ℝ) ≤ 8 + 2 * (8 * cx κ cT) + (8 * cx κ cT) ^ 2)
    show 0 ≤ kθ0 L R.A C₀ η * (8 * cx κ cT) + C₁k * (8 + 2 * (8 * cx κ cT) + (8 * cx κ cT) ^ 2)
    linarith
  have hcR : 0 ≤ cR R Λ cm C₂ := by
    unfold cR cV cW cZ; have := H.hcmu; have := H.hC₂; positivity
  have hcW1 : 1 ≤ cWc := by show 1 ≤ 4 * C₁ + 1; linarith
  have hcW0 : 0 < cWc := by linarith
  have hC1 : 0 ≤ C₁k * (2 + 2 * (8 * cx κ cT) + ck) := by positivity
  have hθb0 : 0 ≤ θb := by
    have : 0 ≤ C₁k * (2 + 2 * (8 * cx κ cT) + ck) * (cR R Λ cm C₂ * ε) := by
      have := H.hε; positivity
    show 0 ≤ kθ0 L R.A C₀ η + C₁k * (2 + 2 * (8 * cx κ cT) + ck) * (cR R Λ cm C₂ * ε)
    linarith
  have hθb : θb ≤ 1 / 36 := by
    show kθ0 L R.A C₀ η + C₁k * (2 + 2 * (8 * cx κ cT) + ck) * (cR R Λ cm C₂ * ε) ≤ 1 / 36
    linarith

  have hDh : ∀ j ≤ n, Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t := fun j hj =>
    ⟨fun i hi => ht.1 i (by omega), fun i hi => ht.2 i (by omega)⟩
  have hr0 : ∀ j ≤ n, 0 ≤ r j := fun j hj => mul_nonneg hcR (ht.1 j hj).1.le
  have hrε : ∀ j ≤ n, r j ≤ cR R Λ cm C₂ * ε := fun j hj =>
    mul_le_mul_of_nonneg_left (ht.1 j hj).2.1 hcR
  have hr' : ∀ j < n, 5 / 6 * r j ≤ r (j + 1) := by
    intro j hj
    have := g_succ_ge (hDh (j + 1) hj) hβ hδ1 H.hcg H.hε1 H.h6
    have := mul_le_mul_of_nonneg_left this hcR
    show 5 / 6 * (cR R Λ cm C₂ * (t j).1) ≤ cR R Λ cm C₂ * (t (j + 1)).1
    linarith
  have hmpos : ∀ i, 0 ≤ cWc * m i := fun i => mul_nonneg hcW0.le (hm0 i).le
  have hK := kseqF_leL (θ := 8 * θb) (B := B) (ck := ck) (r := r) (m := fun i => cWc * m i)
    (j₀ := j₀) (k₀ := k₀) n (by positivity) hB hck hmpos (fun j _ hj => by
      have hrj := hrε j hj.le
      have hr2 : r j ^ 2 ≤ (cR R Λ cm C₂ * ε) ^ 2 := pow_le_pow_left₀ (hr0 j hj.le) hrj 2
      have := mul_le_mul_of_nonneg_left hr2 hB
      have := mul_le_mul_of_nonneg_right hθb hck
      nlinarith)
    (fun j hj1 hj2 => by
      have := hm' j hj1 hj2
      show cWc * m j ≤ 2 * (cWc * m (j + 1)); nlinarith) h8
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    intro hjn
    refine ⟨hK j₀ le_rfl hjn, fun b hb => ?_, fun X hX => ?_⟩
    · rw [obsHistFrom_self]; exact hW0 b hb
    · rw [obsHistFrom_self, kseqF_start]; exact hK0 X hX
  | succ j hjj ih =>
    intro hj
    obtain ⟨hk8, hb, hc'⟩ := ih (by omega)
    have hjn : j < n := by omega
    have hjN : j < Nh := by omega
    have hmj := hm0 j
    have hrj := hr0 j hjn.le
    have hk0 := kseqF_nonneg (r := r) (j₀ := j₀) (by positivity : 0 ≤ 8 * θb) hB hmpos hk₀ j
    have hVoj := hVo j hjj hjn
    have hWo : ∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo w j (histS R j t) ((obsHistFrom R P j₀ o₀ j t).W b) ≤
          ENNReal.ofReal (cR R Λ cm C₂ * (t j).1 * (cWc * m j)) := fun b hb' =>
      (hb b hb').trans (ENNReal.ofReal_le_ofReal (le_of_eq (by
        show cWc * (cR R Λ cm C₂ * (t j).1) * m j = _; ring)))
    refine ⟨hK (j + 1) (by omega) hj, ?_, ?_⟩
    · -- `𝒲`
      intro c' hc''
      have hW := wobs_hist_stepAB R hWB hSB hV hm hβ hδ1 H P w hws o₀ h0 hl0 hs0 ha0 t j hjj hjN
        (hDh j hjn.le) hε₁ (m j) (cWc * r j * m j) hmj.le
        (mul_nonneg (mul_nonneg hcW0.le hrj) hmj.le) hVoj hb c' hc''
      refine hW.trans (ENNReal.ofReal_le_ofReal ?_)
      have hCr : C₁ * r j ≤ 1 / 12 :=
        (mul_le_mul_of_nonneg_left (hrε j hjn.le) hC₁).trans hC₁ε
      exact wobs_realAB (a := Kw / L) (r := r j) (le_of_eq rfl) hLw hCr rfl hC₁ hrj hmj.le
        (hr' j hjn) (hm' j hjj hjn)
    · -- `K`
      intro X hX
      have hks := kobs_hist_stepABL R hKB hSB hV hm hβ hδ1 H P w hws hwa hwb hwab o₀ h0 hl0 hs0 ha0
        t j hjj hjN (hDh j hjn.le) ck (cWc * m j)
        (kseqF (8 * θb) B r (fun i => cWc * m i) j₀ k₀ j)
        hck (mul_pos hcW0 hmj) hk0 hε1 hεε hεk hk8
        (fun b hb' => (hVoj b hb').trans (ENNReal.ofReal_le_ofReal (by nlinarith))) hWo hc' X hX
      refine hks.trans (ENNReal.ofReal_le_ofReal ?_)
      rw [kseqF_succ _ _ _ _ _ hjj]
      have hgj : (t j).1 ≤ ε := (ht.1 j hjn.le).2.1
      have h1 : kθ0 L R.A C₀ η + C₁k * (2 + 2 * (8 * cx κ cT) + ck) *
          (cR R Λ cm C₂ * (t j).1) ≤ θb := by
        have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgj hcR) hC1
        show _ ≤ kθ0 L R.A C₀ η + C₁k * (2 + 2 * (8 * cx κ cT) + ck) * (cR R Λ cm C₂ * ε)
        linarith
      have h2 := mul_le_mul_of_nonneg_right h1
        (by positivity : (0 : ℝ) ≤ 8 * kseqF (8 * θb) B r (fun i => cWc * m i) j₀ k₀ j)
      show _ ≤ 8 * θb * kseqF (8 * θb) B r (fun i => cWc * m i) j₀ k₀ j +
        B * (cR R Λ cm C₂ * (t j).1) ^ 2 * (cWc * m j)
      linarith

end Hist

end

end PtCorr2
