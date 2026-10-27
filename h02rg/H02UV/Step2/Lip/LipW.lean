import Step2.Lip.Lip

/-!
# Lipschitz bounds for the `𝒲`-map (Expected result `thm:step-rest`)

`𝒲_{j+1} = Src_j(V, V) + T_j 𝒲 + R_j(V, 𝒲)` (`Wnext2_decomp`), where `R_j` is the product
remainder `∏(1 + 𝒲') - 1 - ∑ 𝒲'` (`RemW`). On `‖V‖ ≤ e`, `‖𝒲‖ ≤ e²`:

* `RemW_lip`: `‖R(x') - R(x)‖ ≤ C e² (e‖δV‖ + ‖δ𝒲‖)`;
* `Src_lip`: `‖Src(V', V') - Src(V, V)‖ ≤ C e ‖δV‖`;
* `Wnext2_lip`: `‖𝒲_{j+1}(x') - 𝒲_{j+1}(x)‖ ≤ C₀ L^{d-3} ‖δ𝒲‖ + C(e ‖δV‖ + e² ‖δ𝒲‖)`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

/-- **Cauchy estimate in the `T_j(ℓ)` norm.** -/
theorem Tj_sub_le_of_hol {j : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℂ → EvR (Lam d L N)} (hF : HolE F)
    {R B : ℝ} (hR : 1 < R) (hB0 : 0 ≤ B)
    (hB : ∀ z : ℂ, ‖z‖ = R → Tj d (L : ℝ) j ℓ (F z : Alg d L N) ≤ ENNReal.ofReal B) :
    Tj d (L : ℝ) j ℓ ((F 1 - F 0 : EvR (Lam d L N)) : Alg d L N) ≤ ENNReal.ofReal (B / (R - 1)) := by
  have hh : (0 : ℝ) < (L : ℝ) ^ j := pow_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L))) j
  refine tNorm_le fun g hg => ?_
  set φ : ℂ → ℂ := fun z => pairL g (F z : Alg d L N) with hφdef
  have hφ : Differentiable ℂ φ := hF.lin (pairL g)
  have hM : ∀ z : ℂ, ‖z‖ = R → ‖φ z‖ ≤ B := by
    intro z hz
    have h1 := abs_pair_le hh hℓ (F z : Alg d L N) zero_le_one (by simpa using hg)
    rw [mul_one] at h1
    exact h1.trans (ENNReal.toReal_le_of_le_ofReal hB0 (hB z hz))
  have h := (norm_taylor_le hφ hR hM).1
  have e : φ 1 - φ 0 = pair ((F 1 - F 0 : EvR (Lam d L N)) : Alg d L N) g := by
    simp only [hφdef, AddSubgroupClass.coe_sub]
    exact (map_sub (pairL g) _ _).symm
  rwa [e] at h

/-- The product remainder of `Wnext2`. -/
def RemW (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V W : Fam d L N) (c : Fin d → ℕ) :
    EvR (Lam d L N) :=
  ∏ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c), (1 + Wp j C V W b) - 1 -
    ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c), Wp j C V W b

theorem RemW_hol {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (j : ℕ)
    (C : Matrix (Lam d L N) (Lam d L N) ℂ) {Vf Wf : E → Fam d L N}
    (hVf : ∀ b, HolE (fun e => Vf e b)) (hWf : ∀ b, HolE (fun e => Wf e b)) (c : Fin d → ℕ) :
    HolE (fun e => RemW j C (Vf e) (Wf e) c) :=
  ((HolE.prod _ fun b _ => (HolE.const 1).add (Wp_hol j C hVf hWf b)).sub (HolE.const 1)).sub
    (HolE.sum _ fun b _ => Wp_hol j C hVf hWf b)

/-- **`𝒲_{j+1} = Src(V, V) + T 𝒲 + R(V, 𝒲)`.** -/
theorem Wnext2_decomp (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V W : Fam d L N)
    (c : Fin d → ℕ) :
    Wnext2 j C V W c = SrcL j C (EthEL C) V V c + TrL j C 1 W c + RemW j C V W c := by
  have hσ : (fun b' => sigE 1 (W b')) = W := funext fun b' => Subtype.ext (by
    rw [coe_sigE, sig_one])
  have h0 : ∀ b, Wp j C 0 0 b = 0 := fun b => by
    simp [Wp, Sb, LS, SX, Vpr, VprL, EthE_zero, FCE_zero_right, Loc2E_zero]
  have h : ∀ b, Wp j C V W b = Wp j C V 0 b + Wp j C 0 W b := by
    intro b
    rw [Wp_split (W := W), Wp_split (V := 0) (W := W), h0, zero_add]
  rw [SrcL_eq_Wp, TrL_eq_Wp, hσ, RemW, Wnext2]
  simp only [h, sum_add_distrib]
  abel

theorem Tj_sub_le' {j : ℕ} {ℓ : ℝ} (F G : EvR (Lam d L N)) :
    Tj d (L : ℝ) j ℓ ((F - G : EvR (Lam d L N)) : Alg d L N) ≤
      Tj d (L : ℝ) j ℓ (F : Alg d L N) + Tj d (L : ℝ) j ℓ (G : Alg d L N) := by
  rw [AddSubgroupClass.coe_sub]; exact Loc.tNorm_sub_le _ _

theorem seg_norm {j : ℕ} {ℓ : ℝ} (F G : Fam d L N) {t R u : ℝ} (ht : 0 ≤ t) (hR0 : 0 ≤ R)
    (hu : 0 ≤ u) (z : ℂ) (hz : ‖z‖ = R) (hF : Fnorm j ℓ F ≤ ENNReal.ofReal t)
    (hG : Fnorm j ℓ G ≤ ENNReal.ofReal u) :
    Fnorm j ℓ (F + z • G) ≤ ENNReal.ofReal (t + R * u) := by
  have h := Fnorm_smul j ℓ z G
  rw [hz] at h
  refine Fnorm_add_le _ _ ht (mul_nonneg hR0 hu) hF ?_
  rw [show z • G = fun b => z • G b from rfl, h, ENNReal.ofReal_mul hR0]
  exact mul_le_mul_left' hG _

/-- Norm bounds for block families along a segment. -/
theorem line_norms_F {j : ℕ} {ℓ : ℝ} (V V' W W' : Fam d L N) {e R a b : ℝ}
    (he : 0 ≤ e) (hR0 : 0 ≤ R) (ha : 0 ≤ a) (hb : 0 ≤ b) (z : ℂ) (hz : ‖z‖ = R)
    (hVe : Fnorm j ℓ V ≤ ENNReal.ofReal e) (hWe : Fnorm j ℓ W ≤ ENNReal.ofReal (e ^ 2))
    (hda : Fnorm j ℓ (V' - V) ≤ ENNReal.ofReal a) (hdb : Fnorm j ℓ (W' - W) ≤ ENNReal.ofReal b)
    (hRa : R * a ≤ e) (hRb : R * b ≤ e ^ 2) :
    Fnorm j ℓ (V + z • (V' - V)) ≤ ENNReal.ofReal (2 * e) ∧
      Fnorm j ℓ (W + z • (W' - W)) ≤ ENNReal.ofReal (2 * e ^ 2) := by
  have hsm : ∀ (F : Fam d L N) (t : ℝ), 0 ≤ t → Fnorm j ℓ F ≤ ENNReal.ofReal t →
      Fnorm j ℓ (z • F) ≤ ENNReal.ofReal (R * t) := fun F t ht hF => by
    have h := Fnorm_smul j ℓ z F
    rw [hz] at h
    rw [show z • F = fun b => z • F b from rfl, h, ENNReal.ofReal_mul hR0]
    exact mul_le_mul_left' hF _
  refine ⟨?_, ?_⟩
  · refine (Fnorm_add_le _ _ he (mul_nonneg hR0 ha) hVe (hsm _ a ha hda)).trans
      (ENNReal.ofReal_le_ofReal ?_)
    linarith
  · refine (Fnorm_add_le _ _ (sq_nonneg e) (mul_nonneg hR0 hb) hWe (hsm _ b hb hdb)).trans
      (ENNReal.ofReal_le_ofReal ?_)
    linarith

/-- **Lipschitz continuity of the product remainder.** -/
theorem RemW_lip (d : ℕ) (hd : 1 ≤ d) : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ C₃ : ℝ, 0 ≤ C₃ ∧ ∀ (N j : ℕ), j + 1 < N → ∀ ℓ : ℝ, 0 < ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓ C →
    ∀ V V' W W' : Fam d L N, InF j V → InF j V' → InF j W → InF j W' →
    (∀ b, ε (V b : Alg d L N) = 0) → (∀ b, ε (V' b : Alg d L N) = 0) →
    ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
    Fnorm j ℓ V ≤ ENNReal.ofReal e → Fnorm j ℓ V' ≤ ENNReal.ofReal e →
    Fnorm j ℓ W ≤ ENNReal.ofReal (e ^ 2) → Fnorm j ℓ W' ≤ ENNReal.ofReal (e ^ 2) →
    ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
    Fnorm j ℓ (V' - V) ≤ ENNReal.ofReal a → Fnorm j ℓ (W' - W) ≤ ENNReal.ofReal b →
    ∀ c ∈ blockIdx (L := L) (N := N) (j + 1),
      Tj d (L : ℝ) (j + 1) ℓ ((RemW j C V' W' c - RemW j C V W c : EvR (Lam d L N)) :
        Alg d L N) ≤ ENNReal.ofReal (72 * C₃ * e ^ 2 * (e * a + b)) := by
  obtain ⟨L₀, hP⟩ := prodRem_bound d hd
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨C₃, hC₃, hP⟩ := hP L hL
  refine ⟨C₃, hC₃, ?_⟩
  intro N j hjN ℓ hℓ C hC V V' W W' hV hV' hW hW' hV0 hV0' e he he1 hVe hVe' hWe hWe' a b ha hb
    hda hdb c hc
  have hs0 : 0 ≤ e * a + b := by positivity
  -- the bound on the domain
  have H : ∀ (V W : Fam d L N) (v w : ℝ), InF j V → InF j W → (∀ b, ε (V b : Alg d L N) = 0) →
      0 ≤ v → 0 ≤ w → v ≤ 1 → w ≤ 1 → Fnorm j ℓ V ≤ ENNReal.ofReal v →
      Fnorm j ℓ W ≤ ENNReal.ofReal w →
      Tj d (L : ℝ) (j + 1) ℓ (RemW j C V W c : Alg d L N) ≤ ENNReal.ofReal (C₃ * (v ^ 2 + w) ^ 2) :=
    fun V W v w hV hW hV0 hv hw hv1 hw1 hVv hWw =>
      hP N j hjN ℓ hℓ C hC V W hV hW hV0 v w hv hw hv1 hw1 hVv hWw c hc
  have he2 : e ^ 2 ≤ 1 / 4 := by nlinarith
  by_cases hbig : e ^ 2 < 2 * (e * a + b)
  · have h1 := H V' W' e (e ^ 2) hV' hW' hV0' he.le (sq_nonneg e) (by linarith) (by linarith)
      hVe' hWe'
    have h2 := H V W e (e ^ 2) hV hW hV0 he.le (sq_nonneg e) (by linarith) (by linarith) hVe hWe
    refine (Tj_sub_le' _ _).trans ((add_le_add h1 h2).trans ?_)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h4 : C₃ * e ^ 4 ≤ C₃ * e ^ 2 * (2 * (e * a + b)) := by
      have : e ^ 4 = e ^ 2 * e ^ 2 := by ring
      rw [this, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbig.le (sq_nonneg e)) hC₃
    nlinarith only [h4, mul_nonneg (mul_nonneg hC₃ (sq_nonneg e)) hs0]
  · push_neg at hbig
    have hB0 : 0 ≤ 36 * C₃ * e ^ 4 := by positivity
    have hVf : ∀ b, HolE (fun z : ℂ => (V + z • (V' - V)) b) := fun b =>
      (HolE.const _).add (HolE.smul differentiable_id (HolE.const _))
    have hWf : ∀ b, HolE (fun z : ℂ => (W + z • (W' - W)) b) := fun b =>
      (HolE.const _).add (HolE.smul differentiable_id (HolE.const _))
    have hVf0 : ∀ (z : ℂ) b, ε ((V + z • (V' - V)) b : Alg d L N) = 0 := fun z b => by
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Subalgebra.coe_add,
        Subalgebra.coe_smul, AddSubgroupClass.coe_sub, map_add, map_smul, map_sub, hV0, hV0',
        sub_self, smul_zero, add_zero]
    have hF := RemW_hol j C hVf hWf c
    have key : ∀ R : ℝ, 2 ≤ R → R * (e * a + b) ≤ e ^ 2 →
        Tj d (L : ℝ) (j + 1) ℓ ((RemW j C V' W' c - RemW j C V W c : EvR (Lam d L N)) :
          Alg d L N) ≤ ENNReal.ofReal (2 * (36 * C₃ * e ^ 4) / R) := by
      intro R hR2 hRs
      have hR0 : 0 < R := by linarith
      have hRa : R * a ≤ e := by
        have h1 : R * (e * a) ≤ e ^ 2 :=
          le_trans (mul_le_mul_of_nonneg_left (by linarith) hR0.le) hRs
        nlinarith only [h1, he]
      have hRb : R * b ≤ e ^ 2 :=
        le_trans (mul_le_mul_of_nonneg_left (by nlinarith only [he, ha]) hR0.le) hRs
      have hstep := Tj_sub_le_of_hol (j := j + 1) hℓ hF (by linarith : (1 : ℝ) < R) hB0
        fun z hz => by
          obtain ⟨hVz, hWz⟩ := line_norms_F V V' W W' he.le hR0.le ha hb z hz hVe hWe hda hdb
            hRa hRb
          refine (H _ _ (2 * e) (2 * e ^ 2) (inF_add hV (inF_smul (inF_sub hV' hV) z))
            (inF_add hW (inF_smul (inF_sub hW' hW) z)) (hVf0 z) (by positivity) (by positivity)
            (by linarith) (by linarith) hVz hWz).trans (ENNReal.ofReal_le_ofReal ?_)
          nlinarith only [hC₃, he]
      simp only [one_smul, zero_smul, add_zero, add_sub_cancel] at hstep
      refine hstep.trans (ENNReal.ofReal_le_ofReal ?_)
      rw [div_le_div_iff₀ (by linarith) hR0]
      have := mul_le_mul_of_nonneg_left hR2 hB0
      linarith
    rcases hs0.eq_or_lt with hs | hs
    · refine le_trans ?_ zero_le
      refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
      rw [zero_add]
      have hη0 : (0 : ℝ) < η := hη
      obtain ⟨R, hR⟩ : ∃ R : ℝ, R = max 2 (2 * (36 * C₃ * e ^ 4) / η + 1) := ⟨_, rfl⟩
      have hR2 : 2 ≤ R := hR ▸ le_max_left _ _
      have hR1 : 2 * (36 * C₃ * e ^ 4) / η + 1 ≤ R := hR ▸ le_max_right _ _
      refine (key R hR2 (by rw [← hs, mul_zero]; positivity)).trans ?_
      rw [ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top, ENNReal.coe_toReal]
      have hR0 : 0 < R := by linarith
      rw [div_le_iff₀ hR0]
      have h3 := (div_le_iff₀ hη0).1 (by linarith : 2 * (36 * C₃ * e ^ 4) / η ≤ R - 1)
      nlinarith only [h3, hη0]
    · refine (key (e ^ 2 / (e * a + b)) ((le_div_iff₀ hs).2 (by linarith))
        (by rw [div_mul_cancel₀ _ hs.ne'])).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [div_div_eq_mul_div]
      have he0 : 0 < e ^ 2 := by positivity
      rw [div_le_iff₀ he0]
      exact le_of_eq (by ring)

/-- Choosing the radius in a Cauchy estimate: if `X ≤ M/R` for every `R ≥ 2` with `R s ≤ T`,
and `2s ≤ T`, then `X ≤ M s/T`. -/
theorem le_of_radius {X : ENNReal} {M s T : ℝ} (hM : 0 ≤ M) (hs : 0 ≤ s) (hT : 0 < T)
    (h2 : 2 * s ≤ T) (key : ∀ R : ℝ, 2 ≤ R → R * s ≤ T → X ≤ ENNReal.ofReal (M / R)) :
    X ≤ ENNReal.ofReal (M * s / T) := by
  rcases hs.eq_or_lt with h0 | hs0
  · refine le_trans ?_ zero_le
    refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
    rw [zero_add]
    have hη0 : (0 : ℝ) < η := hη
    obtain ⟨R, hR⟩ : ∃ R : ℝ, R = max 2 (M / η + 1) := ⟨_, rfl⟩
    have hR2 : 2 ≤ R := hR ▸ le_max_left _ _
    have hR1 : M / η + 1 ≤ R := hR ▸ le_max_right _ _
    refine (key R hR2 (by rw [← h0, mul_zero]; exact hT.le)).trans ?_
    rw [ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top, ENNReal.coe_toReal]
    have hR0 : 0 < R := by linarith
    rw [div_le_iff₀ hR0]
    have h3 := (div_le_iff₀ hη0).1 (by linarith : M / η ≤ R - 1)
    nlinarith only [h3, hη0]
  · refine (key (T / s) ((le_div_iff₀ hs0).2 (by linarith))
      (by rw [div_mul_cancel₀ _ hs0.ne'])).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    field_simp

/-- **Lipschitz continuity of the quadratic source.** -/
theorem Src_lip (d : ℕ) (hd : 2 ≤ d) : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ (N k : ℕ), k + 1 < N → ∀ ℓ : ℝ, 0 < ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 k ℓ C → TInv C →
    ∀ V V' : Fam d L N, InF k V → InF k V' →
    (∀ b, ε (V b : Alg d L N) = 0) → (∀ b, ε (V' b : Alg d L N) = 0) →
    ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
    Fnorm k ℓ V ≤ ENNReal.ofReal e → Fnorm k ℓ V' ≤ ENNReal.ofReal e →
    ∀ a : ℝ, 0 ≤ a → Fnorm k ℓ (V' - V) ≤ ENNReal.ofReal a →
    ∀ c ∈ blockIdx (L := L) (N := N) (k + 1),
      Tj d (L : ℝ) (k + 1) ℓ ((SrcL k C (EthEL C) V' V' c - SrcL k C (EthEL C) V V c :
        EvR (Lam d L N)) : Alg d L N) ≤ ENNReal.ofReal (8 * C₂ * e * a) := by
  obtain ⟨L₀, hS⟩ := Src_bound d hd
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨C₂, hC₂, hS⟩ := hS L hL
  refine ⟨C₂, hC₂, ?_⟩
  intro N k hkN ℓ hℓ C hC hCt V V' hV hV' hV0 hV0' e he he1 hVe hVe' a ha hda c hc
  have H : ∀ (V : Fam d L N) (v : ℝ), InF k V → (∀ b, ε (V b : Alg d L N) = 0) →
      0 ≤ v → v ≤ 1 → Fnorm k ℓ V ≤ ENNReal.ofReal v →
      Tj d (L : ℝ) (k + 1) ℓ (SrcL k C (EthEL C) V V c : Alg d L N) ≤
        ENNReal.ofReal (C₂ * v ^ 2) :=
    fun V v hV hV0 hv hv1 hVv =>
      (Tj_le_Fnorm _ hc).trans (hS N k hkN ℓ hℓ C hC hCt V hV hV0 v hv hv1 hVv)
  by_cases hbig : e < 2 * a
  · refine (Tj_sub_le' _ _).trans ((add_le_add (H V' e hV' hV0' he.le (by linarith) hVe')
      (H V e hV hV0 he.le (by linarith) hVe)).trans ?_)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have : C₂ * e ^ 2 ≤ C₂ * (e * (2 * a)) := mul_le_mul_of_nonneg_left
      (by nlinarith only [hbig, he]) hC₂
    nlinarith only [this, mul_nonneg (mul_nonneg hC₂ he.le) ha]
  · push_neg at hbig
    have hVf : ∀ b, HolE (fun z : ℂ => (V + z • (V' - V)) b) := fun b =>
      (HolE.const _).add (HolE.smul differentiable_id (HolE.const _))
    have hVf0 : ∀ (z : ℂ) b, ε ((V + z • (V' - V)) b : Alg d L N) = 0 := fun z b => by
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Subalgebra.coe_add,
        Subalgebra.coe_smul, AddSubgroupClass.coe_sub, map_add, map_smul, map_sub, hV0, hV0',
        sub_self, smul_zero, add_zero]
    have hF : HolE (fun z : ℂ => SrcL k C (EthEL C) (V + z • (V' - V)) (V + z • (V' - V)) c) := by
      have h := HolE.sum (blocks k (blockSet (L := L) (N := N) (k + 1) c)) fun b _ =>
        Wp_hol k C (Vf := fun z : ℂ => V + z • (V' - V)) (Wf := fun _ => (0 : Fam d L N)) hVf
          (fun _ => HolE.const (0 : EvR (Lam d L N))) b
      refine Hol.congr h fun z => ?_
      show ((SrcL k C (EthEL C) (V + z • (V' - V)) (V + z • (V' - V)) c : EvR (Lam d L N)) :
        Alg d L N) = _
      rw [SrcL_eq_Wp]
    have hB0 : 0 ≤ 4 * C₂ * e ^ 2 := by positivity
    have := le_of_radius (X := Tj d (L : ℝ) (k + 1) ℓ ((SrcL k C (EthEL C) V' V' c -
        SrcL k C (EthEL C) V V c : EvR (Lam d L N)) : Alg d L N)) (M := 2 * (4 * C₂ * e ^ 2))
      (s := a) (T := e) (by positivity) ha he (by linarith) fun R hR2 hRa => by
        have hR0 : 0 < R := by linarith
        have hstep := Tj_sub_le_of_hol (j := k + 1) hℓ hF (by linarith : (1 : ℝ) < R) hB0
          fun z hz => by
            have hVz : Fnorm k ℓ (V + z • (V' - V)) ≤ ENNReal.ofReal (2 * e) :=
              (seg_norm V (V' - V) he.le hR0.le ha z hz hVe hda).trans
                (ENNReal.ofReal_le_ofReal (by linarith))
            refine (H _ (2 * e) (inF_add hV (inF_smul (inF_sub hV' hV) z)) (hVf0 z)
              (by positivity) (by linarith) hVz).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
            ring
        simp only [one_smul, zero_smul, add_zero, add_sub_cancel] at hstep
        refine hstep.trans (ENNReal.ofReal_le_ofReal ?_)
        rw [div_le_div_iff₀ (by linarith) hR0]
        have := mul_le_mul_of_nonneg_left hR2 hB0
        linarith
    refine this.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    field_simp
    ring

/-- **Lipschitz continuity of the `𝒲`-map.**
`‖𝒲_{j+1}(x') - 𝒲_{j+1}(x)‖ ≤ C₀L^{d-3}‖δ𝒲‖ + 8C₂e‖δV‖ + 72C₃e²(e‖δV‖ + ‖δ𝒲‖)`. -/
theorem Wnext2_lip (d : ℕ) (hd : 2 ≤ d) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ L₀ : ℕ,
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ C₂ C₃ : ℝ, 0 ≤ C₂ ∧ 0 ≤ C₃ ∧
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ : ℝ, 0 < ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓ C → TInv C →
    ∀ V V' W W' : Fam d L N, InF j V → InF j V' → InF j W → InF j W' →
    FamCovG j W → FamCovG j W' →
    (∀ b, ε (V b : Alg d L N) = 0) → (∀ b, ε (V' b : Alg d L N) = 0) →
    ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
    Fnorm j ℓ V ≤ ENNReal.ofReal e → Fnorm j ℓ V' ≤ ENNReal.ofReal e →
    Fnorm j ℓ W ≤ ENNReal.ofReal (e ^ 2) → Fnorm j ℓ W' ≤ ENNReal.ofReal (e ^ 2) →
    ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
    Fnorm j ℓ (V' - V) ≤ ENNReal.ofReal a → Fnorm j ℓ (W' - W) ≤ ENNReal.ofReal b →
      Fnorm (j + 1) ℓ (fun c => Wnext2 j C V' W' c - Wnext2 j C V W c) ≤
        ENNReal.ofReal (C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3) * b + 8 * C₂ * e * a +
          72 * C₃ * e ^ 2 * (e * a + b)) := by
  obtain ⟨C₀, hC₀, L₁, hT⟩ := TrL_contract' d hd
  obtain ⟨L₂, hS⟩ := Src_lip d hd
  obtain ⟨L₃, hR⟩ := RemW_lip d (by omega)
  refine ⟨C₀, hC₀, max L₁ (max L₂ L₃), fun L _ hL => ?_⟩
  obtain ⟨C₂, hC₂, hS⟩ := hS L ((le_max_left _ _).trans ((le_max_right _ _).trans hL))
  obtain ⟨C₃, hC₃, hR⟩ := hR L ((le_max_right _ _).trans ((le_max_right _ _).trans hL))
  refine ⟨C₂, C₃, hC₂, hC₃, ?_⟩
  intro N j hjN ℓ hℓ C hC hCt V V' W W' hV hV' hW hW' hWc hWc' hV0 hV0' e he he1 hVe hVe' hWe hWe'
    a b ha hb hda hdb
  have hTr := hT L ((le_max_left _ _).trans hL) N j hjN ℓ hℓ C hC hCt (W' - W) (inF_sub hW' hW)
    (FlowSeq.famCovG_sub hWc' hWc) 1 (by simp) b hb hdb
  refine iSup₂_le fun c hc => ?_
  have e1 : Wnext2 j C V' W' c - Wnext2 j C V W c =
      (SrcL j C (EthEL C) V' V' c - SrcL j C (EthEL C) V V c) + TrL j C 1 (W' - W) c +
        (RemW j C V' W' c - RemW j C V W c) := by
    rw [Wnext2_decomp, Wnext2_decomp, map_sub, Pi.sub_apply]
    abel
  show Tj d (L : ℝ) (j + 1) ℓ ((Wnext2 j C V' W' c - Wnext2 j C V W c : EvR (Lam d L N)) :
    Alg d L N) ≤ _
  rw [e1]
  have h1 := hS N j hjN ℓ hℓ C hC hCt V V' hV hV' hV0 hV0' e he he1 hVe hVe' a ha hda c hc
  have h2 := (Tj_le_Fnorm _ hc).trans hTr
  have h3 := hR N j hjN ℓ hℓ C hC V V' W W' hV hV' hW hW' hV0 hV0' e he he1 hVe hVe' hWe hWe' a b
    ha hb hda hdb c hc
  have hθ : 0 ≤ C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3) * b := by positivity
  simp only [Subalgebra.coe_add]
  refine (Loc.tNorm_add_le _ _).trans ((add_le_add (Loc.tNorm_add_le _ _) le_rfl).trans ?_)
  refine (add_le_add (add_le_add h1 h2) h3).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_add (by positivity) hθ, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

/-! ### Lipschitz continuity along covariance families -/

/-- Cauchy estimate in the `T_j(ℓ)` norm on a closed disc. -/
theorem Tj_sub_le_of_holOn {j : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℂ → EvR (Lam d L N)} {R B : ℝ}
    (hR : 1 < R)
    (hF : ∀ Λf : Alg d L N →ₗ[ℂ] ℂ,
      DifferentiableOn ℂ (fun z => Λf (F z : Alg d L N)) (Metric.closedBall 0 R)) (hB0 : 0 ≤ B)
    (hB : ∀ z : ℂ, ‖z‖ = R → Tj d (L : ℝ) j ℓ (F z : Alg d L N) ≤ ENNReal.ofReal B) :
    Tj d (L : ℝ) j ℓ ((F 1 - F 0 : EvR (Lam d L N)) : Alg d L N) ≤ ENNReal.ofReal (B / (R - 1)) := by
  have hh : (0 : ℝ) < (L : ℝ) ^ j := pow_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L))) j
  refine tNorm_le fun g hg => ?_
  set φ : ℂ → ℂ := fun z => pairL g (F z : Alg d L N) with hφdef
  have hM : ∀ z : ℂ, ‖z‖ = R → ‖φ z‖ ≤ B := by
    intro z hz
    have h1 := abs_pair_le hh hℓ (F z : Alg d L N) zero_le_one (by simpa using hg)
    rw [mul_one] at h1
    exact h1.trans (ENNReal.toReal_le_of_le_ofReal hB0 (hB z hz))
  have h := norm_taylor_le_on hR (hF (pairL g)) hM
  have e : φ 1 - φ 0 = pair ((F 1 - F 0 : EvR (Lam d L N)) : Alg d L N) g := by
    simp only [hφdef, AddSubgroupClass.coe_sub]
    exact (map_sub (pairL g) _ _).symm
  rwa [e] at h

/-- **Generic Lipschitz bound along a holomorphic covariance family.** If `Φ` is coefficient-wise
holomorphic in the entries of the covariance and bounded by `B` wherever `P` holds, and
`ζ ↦ C(ζ)` is holomorphic on `|ζ_i| < ρ₁` with `P(C(ζ))` on `|ζ_i| ≤ ρ < ρ₁`, then
`‖Φ(C(ζ')) - Φ(C(ζ))‖ ≤ 8Bδ/ρ` for `|ζ_i|, |ζ'_i| ≤ ρ/2`, `|ζ'_i - ζ_i| ≤ δ`. -/
theorem Tj_lip_cov {j : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (Φ : (Lam d L N → Lam d L N → ℂ) → EvR (Lam d L N)) (hΦ : HolE Φ)
    (P : Matrix (Lam d L N) (Lam d L N) ℂ → Prop) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ C, P C → Tj d (L : ℝ) j ℓ (Φ C : Alg d L N) ≤ ENNReal.ofReal B)
    {m : ℕ} (Cf : (Fin m → ℂ) → Matrix (Lam d L N) (Lam d L N) ℂ) {ρ ρ₁ : ℝ} (hρ : 0 < ρ)
    (hρ₁ : ρ < ρ₁) (hCf : ∀ x y, DifferentiableOn ℂ (fun ζ => Cf ζ x y) {ζ | ∀ i, ‖ζ i‖ < ρ₁})
    (hP : ∀ ζ : Fin m → ℂ, (∀ i, ‖ζ i‖ ≤ ρ) → P (Cf ζ))
    (ζ ζ' : Fin m → ℂ) (hζ : ∀ i, ‖ζ i‖ ≤ ρ / 2) (hζ' : ∀ i, ‖ζ' i‖ ≤ ρ / 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (hδζ : ∀ i, ‖ζ' i - ζ i‖ ≤ δ) :
    Tj d (L : ℝ) j ℓ ((Φ (Cf ζ') - Φ (Cf ζ) : EvR (Lam d L N)) : Alg d L N) ≤
      ENNReal.ofReal (8 * B * δ / ρ) := by
  have hle : ∀ ξ : Fin m → ℂ, (∀ i, ‖ξ i‖ ≤ ρ / 2) → ∀ i, ‖ξ i‖ ≤ ρ := fun ξ h i =>
    (h i).trans (by linarith)
  rcases hδ.eq_or_lt with h0 | hδ0
  · have : ζ' = ζ := funext fun i => by
      have := hδζ i; rw [← h0] at this; exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
    rw [this, sub_self]
    refine le_trans (le_of_eq ?_) zero_le
    simp [Step.Tj_zero]
  by_cases hbig : ρ < 4 * δ
  · refine (Tj_sub_le' _ _).trans ((add_le_add (hB _ (hP ζ' (hle ζ' hζ')))
      (hB _ (hP ζ (hle ζ hζ)))).trans ?_)
    rw [← ENNReal.ofReal_add hB0 hB0]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [le_div_iff₀ hρ]
    nlinarith only [hbig, hB0]
  · push_neg at hbig
    obtain ⟨R, hRdef⟩ : ∃ R, R = ρ / (2 * δ) := ⟨_, rfl⟩
    have hR2 : 2 ≤ R := by rw [hRdef, le_div_iff₀ (by positivity)]; linarith
    have hRδ : R * δ = ρ / 2 := by rw [hRdef]; field_simp
    have hγn : ∀ z : ℂ, ‖z‖ ≤ R → ∀ i, ‖(ζ + z • (ζ' - ζ)) i‖ ≤ ρ := fun z hz i => by
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      calc ‖ζ i + z * (ζ' i - ζ i)‖ ≤ ‖ζ i‖ + ‖z‖ * ‖ζ' i - ζ i‖ := by
            rw [← norm_mul]; exact norm_add_le _ _
        _ ≤ ρ / 2 + R * δ := by gcongr; exact hζ i; exact hδζ i
        _ = ρ := by rw [hRδ]; ring
    have hF : ∀ Λf : Alg d L N →ₗ[ℂ] ℂ, DifferentiableOn ℂ
        (fun z : ℂ => Λf (Φ (Cf (ζ + z • (ζ' - ζ))) : Alg d L N)) (Metric.closedBall 0 R) := by
      intro Λf
      have h2 : DifferentiableOn ℂ
          (fun z : ℂ => (Cf (ζ + z • (ζ' - ζ)) : Lam d L N → Lam d L N → ℂ))
          (Metric.closedBall 0 R) := by
        refine differentiableOn_pi.2 fun x => differentiableOn_pi.2 fun y => ?_
        refine (hCf x y).comp (f := fun z : ℂ => ζ + z • (ζ' - ζ)) ?_ fun z hz i => ?_
        · exact ((differentiable_const _).add (differentiable_id.smul_const _)).differentiableOn
        · exact lt_of_le_of_lt (hγn z (by simpa using hz) i) hρ₁
      exact (hΦ.lin Λf).comp_differentiableOn h2
    have hstep := Tj_sub_le_of_holOn (j := j) hℓ (F := fun z : ℂ => Φ (Cf (ζ + z • (ζ' - ζ))))
      (by linarith : (1 : ℝ) < R) hF hB0 fun z hz => hB _ (hP _ (hγn z hz.le))
    simp only [one_smul, zero_smul, add_zero, add_sub_cancel] at hstep
    refine hstep.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [div_le_div_iff₀ (by linarith) hρ]
    have hRm : ρ = 2 * R * δ := by rw [hRdef]; field_simp
    rw [hRm]
    have : 0 ≤ B * δ := mul_nonneg hB0 hδ
    nlinarith only [this, hR2, mul_nonneg this (by linarith : (0 : ℝ) ≤ R - 2)]

/-- `RemW` along a covariance family. -/
theorem RemW_lip_cov (d : ℕ) (hd : 1 ≤ d) : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ C₃ : ℝ, 0 ≤ C₃ ∧ ∀ (N j : ℕ), j + 1 < N → ∀ ℓ : ℝ, 0 < ℓ →
    ∀ (m : ℕ) (Cf : (Fin m → ℂ) → Matrix (Lam d L N) (Lam d L N) ℂ) (ρ ρ₁ : ℝ), 0 < ρ → ρ < ρ₁ →
    (∀ x y, DifferentiableOn ℂ (fun ζ => Cf ζ x y) {ζ | ∀ i, ‖ζ i‖ < ρ₁}) →
    (∀ ζ : Fin m → ℂ, (∀ i, ‖ζ i‖ ≤ ρ) → GoodCov2 j ℓ (Cf ζ)) →
    ∀ V W : Fam d L N, InF j V → InF j W → (∀ b, ε (V b : Alg d L N) = 0) →
    ∀ v w : ℝ, 0 ≤ v → 0 ≤ w → v ≤ 1 → w ≤ 1 →
    Fnorm j ℓ V ≤ ENNReal.ofReal v → Fnorm j ℓ W ≤ ENNReal.ofReal w →
    ∀ ζ ζ' : Fin m → ℂ, (∀ i, ‖ζ i‖ ≤ ρ / 2) → (∀ i, ‖ζ' i‖ ≤ ρ / 2) →
    ∀ δ : ℝ, 0 ≤ δ → (∀ i, ‖ζ' i - ζ i‖ ≤ δ) →
    ∀ c ∈ blockIdx (L := L) (N := N) (j + 1),
      Tj d (L : ℝ) (j + 1) ℓ ((RemW j (Cf ζ') V W c - RemW j (Cf ζ) V W c : EvR (Lam d L N)) :
        Alg d L N) ≤ ENNReal.ofReal (8 * (C₃ * (v ^ 2 + w) ^ 2) * δ / ρ) := by
  obtain ⟨L₀, hP⟩ := prodRem_bound d hd
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨C₃, hC₃, hP⟩ := hP L hL
  refine ⟨C₃, hC₃, ?_⟩
  intro N j hjN ℓ hℓ m Cf ρ ρ₁ hρ hρ₁ hCf hgood V W hV hW hV0 v w hv hw hv1 hw1 hVv hWw ζ ζ' hζ hζ'
    δ hδ hδζ c hc
  have hΦ : HolE (fun M : Lam d L N → Lam d L N → ℂ => RemW j M V W c) := by
    have h1 := Wp_holC (E := Lam d L N → Lam d L N → ℂ) (Cf := fun M => M) j
      (fun x y => differentiable_pi.1 (differentiable_pi.1 differentiable_id x) y)
      (Vf := fun _ => V) (Wf := fun _ => W) (fun b => HolE.const _) (fun b => HolE.const _)
    exact ((HolE.prod _ fun b _ => (HolE.const 1).add (h1 b)).sub (HolE.const 1)).sub
      (HolE.sum _ fun b _ => h1 b)
  exact Tj_lip_cov hℓ _ hΦ (GoodCov2 j ℓ) (by positivity)
    (fun C hC => hP N j hjN ℓ hℓ C hC V W hV hW hV0 v w hv hw hv1 hw1 hVv hWw c hc) Cf hρ hρ₁ hCf
    hgood ζ ζ' hζ hζ' hδ hδζ

/-- The linear transport along a covariance family. -/
theorem TrL_lip_cov (d : ℕ) (hd : 2 ≤ d) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ L₀ : ℕ,
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ : ℝ, 0 < ℓ →
    ∀ (m : ℕ) (Cf : (Fin m → ℂ) → Matrix (Lam d L N) (Lam d L N) ℂ) (ρ ρ₁ : ℝ), 0 < ρ → ρ < ρ₁ →
    (∀ x y, DifferentiableOn ℂ (fun ζ => Cf ζ x y) {ζ | ∀ i, ‖ζ i‖ < ρ₁}) →
    (∀ ζ : Fin m → ℂ, (∀ i, ‖ζ i‖ ≤ ρ) → GoodCov2 j ℓ (Cf ζ) ∧ TInv (Cf ζ)) →
    ∀ F : Fam d L N, InF j F → FamCovG j F → ∀ s : ℂ, ‖s‖ ≤ 1 →
    ∀ w : ℝ, 0 ≤ w → Fnorm j ℓ F ≤ ENNReal.ofReal w →
    ∀ ζ ζ' : Fin m → ℂ, (∀ i, ‖ζ i‖ ≤ ρ / 2) → (∀ i, ‖ζ' i‖ ≤ ρ / 2) →
    ∀ δ : ℝ, 0 ≤ δ → (∀ i, ‖ζ' i - ζ i‖ ≤ δ) →
    ∀ c ∈ blockIdx (L := L) (N := N) (j + 1),
      Tj d (L : ℝ) (j + 1) ℓ ((TrL j (Cf ζ') s F c - TrL j (Cf ζ) s F c : EvR (Lam d L N)) :
        Alg d L N) ≤
        ENNReal.ofReal (8 * (C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3) * w) * δ / ρ) := by
  obtain ⟨C₀, hC₀, L₀, hT⟩ := TrL_contract' d hd
  refine ⟨C₀, hC₀, L₀, fun L _ hL => ?_⟩
  intro N j hjN ℓ hℓ m Cf ρ ρ₁ hρ hρ₁ hCf hgood F hF hFc s hs w hw hFw ζ ζ' hζ hζ' δ hδ hδζ c hc
  have hΦ : HolE (fun M : Lam d L N → Lam d L N → ℂ => TrL j M s F c) := by
    have h1 := Wp_holC (E := Lam d L N → Lam d L N → ℂ) (Cf := fun M => M) j
      (fun x y => differentiable_pi.1 (differentiable_pi.1 differentiable_id x) y)
      (Vf := fun _ => 0) (Wf := fun _ => fun b' => sigE s (F b')) (fun b => HolE.const _)
      (fun b => HolE.const _)
    refine Hol.congr (HolE.sum (blocks j (blockSet (L := L) (N := N) (j + 1) c))
      fun b _ => h1 b) fun M => ?_
    show ((TrL j M s F c : EvR (Lam d L N)) : Alg d L N) = _
    rw [TrL_eq_Wp]
  exact Tj_lip_cov hℓ _ hΦ (fun C => GoodCov2 j ℓ C ∧ TInv C) (by positivity)
    (fun C hC => (Tj_le_Fnorm _ hc).trans (hT L hL N j hjN ℓ hℓ C hC.1 hC.2 F hF hFc s hs w hw hFw))
    Cf hρ hρ₁ hCf hgood ζ ζ' hζ hζ' hδ hδζ

end

end Step2
