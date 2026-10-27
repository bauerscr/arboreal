import PtCorr2.Obs.ProdBd2Hist

/-!
# `ProdBd2` up to the step `N_h` (`ValidAtL`)

`delta_hist_le_genL`, `delta_hist_le2L`: the Pauli–Lipschitz increments of `delta_hist_le_gen`,
`delta_hist_le2` for `k < j ≤ n` with `n + 1 < N` (the covariance properties at `j = n` come from
`ValidAtL R n`, `histCovO_props_i`). **`prodBd2_histL`**: `ProdBd2` with horizon `N_h + 1` (the
product part of the step `N_h` included) along a regular history up to `N_h`; copy of
`prodBd2_hist`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

variable {L N : ℕ} [NeZero L]

section Hist

variable {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

/-- `delta_hist_le_gen` for `k < j ≤ n`, `n + 1 < N`. -/
theorem delta_hist_le_genL (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8) {n : ℕ} (hnN : n + 1 < N)
    (hVn : ∀ i < n, ValidAt R i) (hVL : ValidAtL R n) (t : Flow2.Hist.Seq (Xs R))
    (P : ObsPts 2 L N) {m : Alg 2 L N →ₗ[ℂ] ℂ} (hmP : PauliInv m) {M : ℝ} (hM : 0 ≤ M)
    {k j : ℕ} (hkj : k < j) (hjn : j ≤ n) (hL : prodLb ≤ L)
    (hmb : ∀ G : Alg 2 L N, ‖m G‖ ≤ M * (Tj 2 (L : ℝ) (k + 1) (histS R (k + 1) t / 4) G).toReal)
    {c'' : Fin 2 → ℕ} (hc'' : c'' ∈ blockIdx (L := L) (N := N) (k + 1)) {F : Alg 2 L N}
    (hF : F ∈ NX (nbhd (k + 1) (blockSet (L := L) (N := N) (k + 1) c'') : Set (Lam 2 L N)))
    (ha : P.a ∈ nbhd (k + 1) (blockSet (L := L) (N := N) (k + 1) c''))
    {B : ℝ} (hB0 : 0 ≤ B) (hFB : Tj 2 (L : ℝ) (k + 1) (histS R (k + 1) t) F ≤ ENNReal.ofReal B) :
    ‖m (expLC (histCovO R t j + cumBetween (histCovO R t) k j) F) -
        m (expLC (cumBetween (histCovO R t) k j) F)‖ ≤
      M * (80 * locK 2 ^ 2 * (8 / (7 * L) : ℝ) ^ (j - k)) * B := by
  set s := histS R (k + 1) t with hsdef
  have hs : 0 < s := histS_pos' R hρ0 hρ t (k + 1)
  set K := locK 2
  have hK := one_le_locK 2
  have hLK : 1000 * K ^ 2 + 10 ≤ (L : ℝ) := hL
  have hL10 : (10 : ℝ) ≤ L := by nlinarith [sq_nonneg K]
  have hL0 : (0 : ℝ) < L := by linarith
  set x : ℝ := 8 / (7 * L) with hx
  have hx0 : 0 ≤ x := by positivity
  have hxK : 640 * K ^ 2 * x ≤ 1 := by
    have e : 640 * K ^ 2 * x = 5120 * K ^ 2 / (7 * L) := by rw [hx]; ring
    rw [e, div_le_one (by positivity)]; nlinarith [sq_nonneg K]
  have hK2 : 640 ≤ 640 * K ^ 2 := by nlinarith
  have hx2 : x ≤ 1 / 2 := by
    have : 640 * x ≤ 640 * K ^ 2 * x := mul_le_mul_of_nonneg_right hK2 hx0
    linarith
  set σ : ℝ := s / 4 with hσdef
  have hσ : 0 < σ := by positivity
  set R₀ : ℝ := 10 * (L : ℝ) ^ (k + 1) with hR₀
  have hLk : (1 : ℝ) ≤ (L : ℝ) ^ (k + 1) := one_le_pow₀ (by linarith)
  have hkN : k + 1 + 2 ≤ N := by omega
  -- the hypotheses of `pauli_lip_loc`
  have hhR : (L : ℝ) ^ (k + 1) ≤ R₀ := by rw [hR₀]; linarith
  have hR : 2 * ((pPhi 2 : ℕ) : ℝ) + 1 ≤ R₀ := by
    rw [hR₀]; norm_num [pPhi]; linarith
  have hN : 2 * (⌈2 * R₀⌉₊ + 2 * pPhi 2) < L ^ N := by
    have e : ⌈2 * R₀⌉₊ = 20 * L ^ (k + 1) := by
      rw [hR₀, show 2 * (10 * (L : ℝ) ^ (k + 1)) = ((20 * L ^ (k + 1) : ℕ) : ℝ) by push_cast; ring,
        Nat.ceil_natCast]
    rw [e]
    have hL10' : 10 ≤ L := by exact_mod_cast hL10
    have h1 : L ^ N = L ^ (N - (k + 1)) * L ^ (k + 1) := by rw [← pow_add]; congr 1; omega
    have h2 : 100 ≤ L ^ (N - (k + 1)) := by
      calc 100 ≤ L ^ 2 := by nlinarith
        _ ≤ L ^ (N - (k + 1)) := Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : 1 ≤ L ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
    simp only [pPhi]
    nlinarith
  have hY : ∀ y ∈ (nbhd (k + 1) (blockSet (L := L) (N := N) (k + 1) c'') : Set (Lam 2 L N)),
      (supNorm (y - P.a) : ℝ) ≤ R₀ := by
    intro y hy
    obtain ⟨z, hz⟩ := mem_blockIdx.1 hc''
    have h1 := supNorm_le_of_mem_nbhd_blockSet (L := L) (N := N) hy hz
    have h2 := supNorm_le_of_mem_nbhd_blockSet (L := L) (N := N) ha hz
    have h3 := supNorm_add_le (y - z) (z - P.a)
    rw [sub_add_sub_cancel, supNorm_sub_comm z] at h3
    have h4 : supNorm (y - P.a) ≤ 10 * L ^ (k + 1) := by norm_num at h1 h2; omega
    rw [hR₀]; exact_mod_cast h4
  have hrep : ∀ i ∈ Ioo k j, ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (Fv Gv : Lam 2 L N → H), IsGram (histCovO R t i) Fv Gv ∧
        GramBound (Dir 2) (pPhi 2) ((L : ℝ) ^ (i + 1))
          (fscale (stZ' R (rawHist R i t)) * R.ℓ / 4) Fv Gv := fun i hi =>
    (histCovO_props_i R hVn hVL t (i := i) (by have := (mem_Ioo.1 hi).2; omega)).1.gram
  have hrep₁ := (histCovO_props_i R hVn hVL t (i := j) hjn).1.gram
  have hRs : ∀ i ∈ Ioo k j, R₀ ≤ (L : ℝ) ^ (i + 1) := by
    intro i hi
    have hi' := (mem_Ioo.1 hi).1
    calc R₀ ≤ (L : ℝ) * (L : ℝ) ^ (k + 1) := by rw [hR₀]; exact mul_le_mul_of_nonneg_right hL10 (by positivity)
      _ = (L : ℝ) ^ (k + 2) := by ring
      _ ≤ (L : ℝ) ^ (i + 1) := pow_le_pow_right₀ (by linarith) (by omega)
  have hR₁ : R₀ ≤ (L : ℝ) ^ (j + 1) := by
    calc R₀ ≤ (L : ℝ) * (L : ℝ) ^ (k + 1) := by rw [hR₀]; exact mul_le_mul_of_nonneg_right hL10 (by positivity)
      _ = (L : ℝ) ^ (k + 2) := by ring
      _ ≤ (L : ℝ) ^ (j + 1) := pow_le_pow_right₀ (by linarith) (by omega)
  have hsumS : ∑ i ∈ Ioo k j, locC 2 R₀ (fscale (stZ' R (rawHist R i t)) * R.ℓ / 4)
      ((L : ℝ) ^ (i + 1)) ≤ σ ^ 2 := by
    calc ∑ i ∈ Ioo k j, locC 2 R₀ (fscale (stZ' R (rawHist R i t)) * R.ℓ / 4) ((L : ℝ) ^ (i + 1))
        ≤ ∑ i ∈ Ioo k j, 20 * K ^ 2 * x ^ (i - k) * s ^ 2 :=
          sum_le_sum fun i hi => locC_hist_le R hρ0 hρ t (mem_Ioo.1 hi).1
      _ = 20 * K ^ 2 * s ^ 2 * ∑ i ∈ Ioo k j, x ^ (i - k) := by
          rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
      _ ≤ 20 * K ^ 2 * s ^ 2 * (2 * x) :=
          mul_le_mul_of_nonneg_left (geom_Ioo_le hx0 hx2 k j) (by positivity)
      _ ≤ σ ^ 2 := by
          rw [hσdef]
          have : 0 ≤ s ^ 2 := sq_nonneg s
          nlinarith
  have hxj : x ^ (j - k) ≤ x := by
    have : 1 ≤ j - k := by omega
    calc x ^ (j - k) ≤ x ^ 1 := pow_le_pow_of_le_one hx0 (by linarith) this
      _ = x := pow_one x
  have hCj := locC_hist_le R hρ0 hρ t hkj
  have hsumC : locC 2 R₀ (fscale (stZ' R (rawHist R j t)) * R.ℓ / 4) ((L : ℝ) ^ (j + 1)) ≤
      (2 * σ) ^ 2 := by
    refine hCj.trans ?_
    rw [hσdef]
    have h1 : 20 * K ^ 2 * x ^ (j - k) ≤ 20 * K ^ 2 * x :=
      mul_le_mul_of_nonneg_left hxj (by positivity)
    have : 0 ≤ s ^ 2 := sq_nonneg s
    nlinarith
  have key := pauli_lip_loc (d := 2) one_le_two hmP (k := k + 1) hσ hM
    hmb hhR hR hN P.a hY hF (Ioo k j) (histCovO R t) (fun i => (L : ℝ) ^ (i + 1))
    (fun i => fscale (stZ' R (rawHist R i t)) * R.ℓ / 4)
    (fun i _ => ellI_pos R hρ0 hρ t i) hRs hrep (histCovO R t j) (ellI_pos R hρ0 hρ t j) hR₁
    hrep₁ hsumS hsumC
  have e1 : histCovO R t j + cumBetween (histCovO R t) k j =
      ∑ i ∈ Ioo k j, histCovO R t i + histCovO R t j := by rw [cumBetween, add_comm]
  rw [e1, cumBetween]
  refine key.trans ?_
  rw [show 4 * σ = s by rw [hσdef]; ring]
  have hT : (Tj 2 (L : ℝ) (k + 1) s F).toReal ≤ B := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hFB
    rwa [ENNReal.toReal_ofReal hB0] at this
  have hlc : locC 2 R₀ (fscale (stZ' R (rawHist R j t)) * R.ℓ / 4) ((L : ℝ) ^ (j + 1)) /
      (2 * σ) ^ 2 ≤ 80 * K ^ 2 * x ^ (j - k) := by
    rw [div_le_iff₀ (by positivity)]
    refine hCj.trans (le_of_eq ?_)
    rw [hσdef]; ring
  have hT0 : 0 ≤ (Tj 2 (L : ℝ) (k + 1) s F).toReal := ENNReal.toReal_nonneg
  have hl0 : 0 ≤ locC 2 R₀ (fscale (stZ' R (rawHist R j t)) * R.ℓ / 4) ((L : ℝ) ^ (j + 1)) /
      (2 * σ) ^ 2 := div_nonneg (locC_nonneg (by positivity) (by positivity)) (by positivity)
  exact mul_le_mul (mul_le_mul_of_nonneg_left hlc hM) hT hT0 (by positivity)


/-- `delta_hist_le2` for `k < j ≤ n`, `n + 1 < N`. -/
theorem delta_hist_le2L (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8) {n : ℕ} (hnN : n + 1 < N)
    (hVn : ∀ i < n, ValidAt R i) (hVL : ValidAtL R n) (t : Flow2.Hist.Seq (Xs R))
    (P : ObsPts 2 L N) {k j : ℕ} (hkj : k < j) (hjn : j ≤ n) (hL : prodLb ≤ L)
    {c'' : Fin 2 → ℕ} (hc'' : c'' ∈ blockIdx (L := L) (N := N) (k + 1)) {F : Alg 2 L N}
    (hF : F ∈ NX (nbhd (k + 1) (blockSet (L := L) (N := N) (k + 1) c'') : Set (Lam 2 L N)))
    (ha : P.a ∈ nbhd (k + 1) (blockSet (L := L) (N := N) (k + 1) c''))
    {B : ℝ} (hB0 : 0 ≤ B) (hFB : Tj 2 (L : ℝ) (k + 1) (histS R (k + 1) t) F ≤ ENNReal.ofReal B) :
    ‖mass2L (expLC (histCovO R t j + cumBetween (histCovO R t) k j) F) -
        mass2L (expLC (cumBetween (histCovO R t) k j) F)‖ ≤
      1280 * locK 2 ^ 2 * (8 / (7 * L) : ℝ) ^ (j - k) * B / histS R (k + 1) t ^ 2 := by
  have hs := histS_pos' R hρ0 hρ t (k + 1)
  have hσ : 0 < histS R (k + 1) t / 4 := by positivity
  refine (delta_hist_le_genL R hρ0 hρ hnN hVn hVL t P pauliInv_mass2
    (M := ((histS R (k + 1) t / 4)⁻¹) ^ 2) (by positivity) hkj hjn hL
    (fun G => (norm_mass2_le hσ (k + 1) G).trans_eq (mul_comm _ _)) hc'' hF ha hB0 hFB).trans
    (le_of_eq ?_)
  field_simp; ring

set_option maxHeartbeats 2000000 in
/-- **`ProdBd2` along the history** (Case (2), `γ_a = 0`; ratio `2/L`, constant `prodCP2 L C_P`). -/
theorem prodBd2_histL {Cp εp : ℝ} (hPB : PObsBounds L Cp εp) (hCp : 0 ≤ Cp)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1) (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8)
    (P : ObsPts 2 L N) (V : OCoup .two) (hga : OCoup2.ga V = 0)
    (t : Flow2.Hist.Seq (Xs R)) (n : ℕ) (hn : n = Nh + 1) (hnN : Nh + 1 < N) (hVL : ValidAtL R Nh)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε Nh t)
    (hεp : cR R Λ cm C₂ * ε ≤ εp) (hL : prodLb ≤ L) :
    ProdBd2 R P (obsInit .two V P) t n (fun j => cR R Λ cm C₂ * (t j).1) (prodCP2 L Cp) (2 / L) := by
  intro j hj mm hmm
  set o₀ := obsInit .two V P with ho₀
  have h0 : o₀.IsObs := obsInit_isObs .two V P
  have hl0 : ObsLocInv P 0 o₀ := obsLocInv_init .two V P
  have hs0 : ObsSymInv 0 o₀ := obsSymInv_init .two V P
  set rr : ℕ → ℝ := fun j => cR R Λ cm C₂ * (t j).1 with hrr
  set K := locK 2
  have hK := one_le_locK 2
  have hLK : 1000 * K ^ 2 + 10 ≤ (L : ℝ) := hL
  have hL10 : (10 : ℝ) ≤ L := by nlinarith [sq_nonneg K]
  have hL0 : (0 : ℝ) < L := by linarith
  subst hn
  have HC := muChain2_obsHist R P o₀ t hnN (fun b => obsInit_two_W P V b)
    (fun b => obsInit_two_form P V b)
  have hDh : ∀ k ≤ Nh, Flow2.Hist.InDh Λ β δ κ cg cm cT ε k t := fun k hk =>
    ⟨fun i hi => ht.1 i (by omega), fun i hi => ht.2 i (by omega)⟩
  have hcR : 0 ≤ cR R Λ cm C₂ := by
    unfold cR cV cW cZ; have := H.hcmu; have := H.hC₂; positivity
  have hr0 : ∀ k ≤ Nh, 0 ≤ rr k := fun k hk => mul_nonneg hcR (ht.1 k hk).1.le
  have hs : ∀ i, 0 < histS R i t := histS_pos' R hρ0 hρ t
  have hm0 : ∀ k ≤ j, 0 ≤ mm k := fun k hk => (hmm k hk).1
  -- the block bound of `V^{obs}_k`
  have hVo : ∀ k ≤ j, ∀ b ∈ blockIdx (L := L) (N := N) k,
      oTo Obs2.wA k (histS R k t) ((obsHist R P o₀ k t).V b) ≤ ENNReal.ofReal (mm k) := by
    intro k hk b hb'
    have hsm := (hmm k hk).2.1
    rw [Obs2.oTo_wA, obsHist2_pure R P t V hga k b]
    refine (Tj_smul_pbp_le k (hs k) _ _).trans (ENNReal.ofReal_le_ofReal (le_trans ?_ hsm))
    have h1 : ‖mass2 ((obsHist R P o₀ k t).V b : SA .two (Lam 2 L N)).a‖ ≤
        shA2 (histVO2 R P o₀ t) k := by
      rw [← histVO2_a R P o₀ t k b]
      exact single_le_sum (f := fun b => ‖mass2
        (histVO2 R P o₀ t k b : SA .two (Lam 2 L N)).a‖) (fun _ _ => norm_nonneg _) hb'
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  -- the product parts of the steps `k < j`
  have hPk : ∀ k < j, ∀ c'' ∈ blockIdx (L := L) (N := N) (k + 1),
      Tj 2 (L : ℝ) (k + 1) (histS R (k + 1) t)
        ((prodO P k (histCovO R t k) (histVO2 R P o₀ t k) (histWO2 R P o₀ t k) c'' :
          SA .two (Lam 2 L N)).a) ≤ ENNReal.ofReal (2 * Cp * rr k ^ 2 * mm k) ∧
      prodO P k (histCovO R t k) (histVO2 R P o₀ t k) (histWO2 R P o₀ t k) c'' ∈
        osub P (nbhd (k + 1) (blockSet (L := L) (N := N) (k + 1) c'')) := by
    intro k hk c'' hc''
    have hkn : k < Nh := by omega
    have hrk := hr0 k hkn.le
    obtain ⟨h1, h2⟩ := prod_hist_step R hPB hSB hV hm hβ hδ1 H P Obs2.wA Obs2.wA_ab o₀ h0 hl0 hs0 t k
      (by omega) (hDh k hkn.le) hεp (mm k) (rr k * mm k) (hm0 k hk.le)
      (mul_nonneg hrk (hm0 k hk.le)) (hVo k hk.le) (hmm k hk.le).2.2 c'' hc''
    refine ⟨?_, h2⟩
    rw [← Obs2.oTo_wA]
    refine h1.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    simp only [hrr]; ring
  set x : ℝ := 8 / (7 * L) with hx
  have hx0 : 0 ≤ x := by positivity
  have hx2 : x ≤ 2 / L := by
    rw [hx, div_le_div_iff₀ (by positivity) hL0]; nlinarith
  have hss1 : ∀ k, (histS R (k + 1) t)⁻¹ ≤ 15 / 14 * (histS R k t)⁻¹ := by
    intro k
    have e : histS R (k + 1) t = histS R k t * fscale (1 + zetaH R k t) := by
      unfold histS; rw [rawHist_succ_Z, fscale_mul]; ring
    have hz : ‖zetaH R k t‖ ≤ 1 / 8 := (absorb_le R hρ0 _ _).trans hρ
    have h1 := fscale_one_add_ge hz
    have hf : 0 < fscale (1 + zetaH R k t) := by linarith
    have hfi : (fscale (1 + zetaH R k t))⁻¹ ≤ 15 / 14 := by
      rw [inv_le_iff_one_le_mul₀ hf]; nlinarith
    rw [e, mul_inv]
    calc (histS R k t)⁻¹ * (fscale (1 + zetaH R k t))⁻¹ ≤ (histS R k t)⁻¹ * (15 / 14) :=
          mul_le_mul_of_nonneg_left hfi (inv_nonneg.2 (hs k).le)
      _ = _ := by ring
  set gterm : (Fin 2 → ℕ) → ℝ := fun c'' => if j = 0 then 0 else
    if P.a ∈ nbhd j (blockSet (L := L) (N := N) j c'') then
      2 * Cp * rr (j - 1) ^ 2 * mm (j - 1) / histS R j t ^ 2 else 0 with hgterm
  set dterm : ℕ → (Fin 2 → ℕ) → ℝ := fun k c'' =>
    if P.a ∈ nbhd (k + 1) (blockSet (L := L) (N := N) (k + 1) c'') then
      1280 * K ^ 2 * x ^ (j - k) * (2 * Cp * rr k ^ 2 * mm k) / histS R (k + 1) t ^ 2 else 0 with hdterm
  -- the term `G_j(B_+; 0)`
  have hG : ∀ c' ∈ blockIdx (L := L) (N := N) (j + 1),
      ‖wTadX j mass2L (histWO2 R P o₀ t j) (blockSet (L := L) (N := N) (j + 1) c') 0‖ ≤
        ∑ c'' ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'), gterm c'' := by
    intro c' hc'
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · have : wTadX 0 mass2L (histWO2 R P o₀ t 0) (blockSet (L := L) (N := N) (0 + 1) c') 0
          = 0 := by
        unfold wTadX
        refine sum_eq_zero fun b _ => ?_
        rw [HC.hW0 b, map_zero, map_zero]
      rw [this, norm_zero]
      exact sum_nonneg fun c'' _ => by simp [hgterm]
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hX : IsPolymer (j' + 1) (blockSet (L := L) (N := N) (j' + 1 + 1) c') :=
        IsPolymer.of_succ (isPolymer_blockSet _ c')
      rw [HC.wTadX_succ (by omega) hX 0, tau2, expLC_zero, sub_self, mul_zero, zero_add, zero_add,
        sub_self, add_zero, wProdX_eq_prodO]
      refine (norm_sum_le _ _).trans (sum_le_sum fun c'' hc'' => ?_)
      rw [expLC_zero]
      have hc''I := mem_blockIdx_of_mem_blocks hc''
      obtain ⟨hT, hmem⟩ := hPk j' (by omega) c'' hc''I
      simp only [hgterm, if_neg (Nat.succ_ne_zero j'), Nat.add_sub_cancel]
      split_ifs with ha
      · show ‖mass2 _‖ ≤ _
        refine (norm_mass2_le (hs (j' + 1)) (j' + 1) _).trans ?_
        have hB : 0 ≤ 2 * Cp * rr j' ^ 2 * mm j' := by
          have := hm0 j' (by omega); positivity
        have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hT
        rw [ENNReal.toReal_ofReal hB] at this
        rw [div_eq_mul_inv, ← inv_pow]
        exact mul_le_mul_of_nonneg_right this (by positivity)
      · rw [osub_a_zero hmem ha, map_zero, norm_zero]
  -- the increments
  have hD : ∀ c' ∈ blockIdx (L := L) (N := N) (j + 1),
      ‖muProdIncX2 P (histCovO R t) (histVO2 R P o₀ t) (histWO2 R P o₀ t) j
          (blockSet (L := L) (N := N) (j + 1) c')‖ ≤
        ∑ k ∈ range j, ∑ c'' ∈ blocks (k + 1) (blockSet (L := L) (N := N) (j + 1) c'),
          dterm k c'' := by
    intro c' hc'
    unfold muProdIncX2
    refine (norm_sum_le _ _).trans (sum_le_sum fun k hk => ?_)
    rw [wProdX_eq_prodO, wProdX_eq_prodO, ← sum_sub_distrib]
    refine (norm_sum_le _ _).trans (sum_le_sum fun c'' hc'' => ?_)
    have hk' : k < j := mem_range.1 hk
    have hc''I := mem_blockIdx_of_mem_blocks hc''
    obtain ⟨hT, hmem⟩ := hPk k hk' c'' hc''I
    simp only [hdterm]
    split_ifs with ha
    · have hB : 0 ≤ 2 * Cp * rr k ^ 2 * mm k := by
        have := hm0 k hk'.le; have := hr0 k (by omega); positivity
      exact delta_hist_le2L R hρ0 hρ hnN hV hVL t P hk' (by omega) hL hc''I hmem.2.1 ha hB hT
    · rw [osub_a_zero hmem ha]; simp
  -- the sum over the `(j+1)`-blocks
  show ∑ c' ∈ blockIdx (L := L) (N := N) (j + 1),
      ‖wTadX j mass2L (histWO2 R P o₀ t j) (blockSet (L := L) (N := N) (j + 1) c') 0 +
        muProdIncX2 P (histCovO R t) (histVO2 R P o₀ t) (histWO2 R P o₀ t) j
          (blockSet (L := L) (N := N) (j + 1) c')‖ ≤ _
  have hS1 : ∑ c' ∈ blockIdx (L := L) (N := N) (j + 1),
      ‖wTadX j mass2L (histWO2 R P o₀ t j) (blockSet (L := L) (N := N) (j + 1) c') 0 +
        muProdIncX2 P (histCovO R t) (histVO2 R P o₀ t) (histWO2 R P o₀ t) j
          (blockSet (L := L) (N := N) (j + 1) c')‖ ≤
      ∑ c'' ∈ blockIdx (L := L) (N := N) j, gterm c'' +
        ∑ k ∈ range j, ∑ c'' ∈ blockIdx (L := L) (N := N) (k + 1), dterm k c'' := by
    refine (sum_le_sum fun c' hc' => (norm_add_le _ _).trans
      (add_le_add (hG c' hc') (hD c' hc'))).trans (le_of_eq ?_)
    rw [sum_add_distrib, sum_blockIdx_le gterm (by omega : j ≤ j + 1), sum_comm]
    congr 1
    exact sum_congr rfl fun k hk => sum_blockIdx_le (dterm k) (by have := mem_range.1 hk; omega)
  have hS2 : ∑ c'' ∈ blockIdx (L := L) (N := N) j, gterm c'' ≤
      (if j = 0 then 0 else cbnC * (2 * Cp * (rr (j - 1) ^ 2 * mm (j - 1))) / histS R j t ^ 2) := by
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp [hgterm]
    · simp only [hgterm, if_neg (by omega : j ≠ 0)]
      have hv : 0 ≤ 2 * Cp * rr (j - 1) ^ 2 * mm (j - 1) / histS R j t ^ 2 := by
        have := hm0 (j - 1) (by omega); have := hs j; positivity
      refine (sum_ite_near_le P.a hv).trans (le_of_eq ?_)
      ring
  have hS3 : ∑ k ∈ range j, ∑ c'' ∈ blockIdx (L := L) (N := N) (k + 1), dterm k c'' ≤
      ∑ k ∈ range j, cbnC * (1280 * K ^ 2 * x ^ (j - k) * (2 * Cp * (rr k ^ 2 * mm k)) /
        histS R (k + 1) t ^ 2) := by
    refine sum_le_sum fun k hk => ?_
    have hk' := mem_range.1 hk
    have hv : 0 ≤ 1280 * K ^ 2 * x ^ (j - k) * (2 * Cp * rr k ^ 2 * mm k) / histS R (k + 1) t ^ 2 := by
      have := hm0 k hk'.le; have := hs (k + 1); positivity
    refine (sum_ite_near_le P.a hv).trans (le_of_eq ?_)
    ring
  have hss : ∀ k, (histS R (k + 1) t ^ 2)⁻¹ ≤ 6 / 5 * (histS R k t ^ 2)⁻¹ := by
    intro k
    have h1 := hss1 k
    have h2 : 0 ≤ (histS R (k + 1) t)⁻¹ := inv_nonneg.2 (hs _).le
    rw [← inv_pow, ← inv_pow]
    have h3 : (histS R (k + 1) t)⁻¹ ^ 2 ≤ (15 / 14 * (histS R k t)⁻¹) ^ 2 :=
      pow_le_pow_left₀ h2 h1 2
    have h4 : 0 ≤ (histS R k t)⁻¹ ^ 2 := sq_nonneg _
    nlinarith
  have hfin := prodBd_real2 (K := K) hL0 (Nat.cast_nonneg cbnC) hCp (by positivity) hx0 hx2 j
    (fun k => rr k ^ 2 * mm k) (fun k => histS R k t ^ 2)
    (fun k hk => mul_nonneg (sq_nonneg _) (hm0 k hk)) (fun k => pow_pos (hs k) 2) hss
  refine hS1.trans ((add_le_add hS2 hS3).trans (hfin.trans (le_of_eq ?_)))
  rw [prodCP2]


end Hist

end

end PtCorr2
