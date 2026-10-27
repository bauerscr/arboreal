import Step2.Lip.FlowLipK

/-!
# Joint Lipschitz bounds for `𝒲^lin_{j+1}` and `D_{j+1}` (Lipschitz bounds, part 5)

The same joint Cauchy estimate as for `K_{j+1}` (`Kplus_lip_joint`), for the block families
`𝒲^lin_{j+1} = Src_j(V, V) + T_j 𝒲^lin_j` (`WlinNext_lip_joint`) and
`D_{j+1} = T_j D + R_j(V, 𝒲^lin + D)` (`Dnext_lip_joint`), jointly in the covariance and the
inputs.
-/

namespace Step2

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

theorem famCovG_smul {j : ℕ} {F : Fam d L N} (hF : FamCovG j F) (c : ℂ) :
    FamCovG j (c • F) := by
  intro t ht b hb; simp [hF t ht b hb]

theorem famCovG_line {j : ℕ} {F F' : Fam d L N} (hF : FamCovG j F) (hF' : FamCovG j F') (z : ℂ) :
    FamCovG j (F + z • (F' - F)) :=
  FlowSeq.famCovG_add hF (famCovG_smul (FlowSeq.famCovG_sub hF' hF) z)

/-- **Joint Cauchy estimate for a block family** along a holomorphic segment. -/
theorem Fnorm_lip_line {j : ℕ} {ℓ' : ℝ} (hℓ' : 0 < ℓ') (Φ : ℂ → Fam d L N)
    (hΦ : ∀ c, HolE (fun z => Φ z c)) {B s : ℝ} (hB : 0 ≤ B) (hs : 0 ≤ s)
    (h0 : Fnorm (j + 1) ℓ' (Φ 0) ≤ ENNReal.ofReal B) (h1 : Fnorm (j + 1) ℓ' (Φ 1) ≤ ENNReal.ofReal B)
    (hbd : ∀ R : ℝ, 2 ≤ R → R * s ≤ 1 → ∀ z : ℂ, ‖z‖ = R →
      Fnorm (j + 1) ℓ' (Φ z) ≤ ENNReal.ofReal B) :
    Fnorm (j + 1) ℓ' (Φ 1 - Φ 0) ≤ ENNReal.ofReal (4 * B * s) := by
  refine cauchy_lip hB hs ?_ ?_
  · refine iSup₂_le fun c hc => ?_
    refine (Tj_sub_le' (Φ 1 c) (Φ 0 c)).trans ((add_le_add ((Tj_le_Fnorm _ hc).trans h1)
      ((Tj_le_Fnorm _ hc).trans h0)).trans (le_of_eq ?_))
    rw [← ENNReal.ofReal_add hB hB]; ring_nf
  · intro R hR2 hRs
    refine iSup₂_le fun c hc => ?_
    have h := Tj_sub_le_of_hol (j := j + 1) hℓ' (hΦ c) (by linarith : (1 : ℝ) < R) hB
      fun z hz => (Tj_le_Fnorm _ hc).trans (hbd R hR2 hRs z hz)
    simpa using h


theorem WlinNext_hol_line (j : ℕ) (C C' : Matrix (Lam d L N) (Lam d L N) ℂ) (V V' Wl Wl' : Fam d L N)
    (c : Fin d → ℕ) : HolE (fun z : ℂ => WlinNext j (C + z • (C' - C)) (V + z • (V' - V))
      (Wl + z • (Wl' - Wl)) c) := by
  have hVf : ∀ b, HolE (fun z : ℂ => (V + z • (V' - V)) b) := fun b =>
    (HolE.const _).add (HolE.smul differentiable_id (HolE.const _))
  have hWf : ∀ b, HolE (fun z : ℂ => (Wl + z • (Wl' - Wl)) b) := fun b =>
    (HolE.const _).add (HolE.smul differentiable_id (HolE.const _))
  have h1 := HolE.sum (blocks j (blockSet (L := L) (N := N) (j + 1) c)) fun b _ =>
    Wp_holC (Cf := fun z : ℂ => C + z • (C' - C)) j (fun x y => cov_line_diff x y)
      (Vf := fun z : ℂ => V + z • (V' - V)) (Wf := fun _ => (0 : Fam d L N)) hVf
      (fun _ => HolE.const (0 : EvR (Lam d L N))) b
  have h2 := HolE.sum (blocks j (blockSet (L := L) (N := N) (j + 1) c)) fun b _ =>
    Wp_holC (Cf := fun z : ℂ => C + z • (C' - C)) j (fun x y => cov_line_diff x y)
      (Vf := fun _ => (0 : Fam d L N))
      (Wf := fun z : ℂ => fun b' => sigE 1 ((Wl + z • (Wl' - Wl)) b'))
      (fun _ => HolE.const _) (fun b' => holE_sigE (differentiable_const 1) (hWf b')) b
  refine Hol.congr (h1.add h2) fun z => ?_
  show ((WlinNext j _ _ _ c : EvR (Lam d L N)) : Alg d L N) = _
  rw [WlinNext, Pi.add_apply, SrcL_eq_Wp, TrL_eq_Wp]

theorem Dnext_hol_line (j : ℕ) (C C' : Matrix (Lam d L N) (Lam d L N) ℂ)
    (V V' Wl Wl' D D' : Fam d L N) (c : Fin d → ℕ) :
    HolE (fun z : ℂ => Dnext j (C + z • (C' - C)) (V + z • (V' - V)) (Wl + z • (Wl' - Wl))
      (D + z • (D' - D)) c) := by
  have hVf : ∀ b, HolE (fun z : ℂ => (V + z • (V' - V)) b) := fun b =>
    (HolE.const _).add (HolE.smul differentiable_id (HolE.const _))
  have hWf : ∀ b, HolE (fun z : ℂ => (Wl + z • (Wl' - Wl) + (D + z • (D' - D))) b) := fun b =>
    ((HolE.const _).add (HolE.smul differentiable_id (HolE.const _))).add
      ((HolE.const _).add (HolE.smul differentiable_id (HolE.const _)))
  have h1 := Wnext2_holC (Cf := fun z : ℂ => C + z • (C' - C)) j (fun x y => cov_line_diff x y)
    hVf hWf c
  exact h1.sub (WlinNext_hol_line j C C' V V' Wl Wl' c)

set_option maxHeartbeats 1000000 in
/-- **Joint Lipschitz bound for `𝒲^lin_{j+1}`.** -/
theorem WlinNext_lip_joint (d : ℕ) (hd : 2 ≤ d) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ L₀ : ℕ,
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ C₂ : ℝ, 0 ≤ C₂ ∧
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ ℓ' ℓC τ : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → 0 < τ →
    ℓ' + (1 + τ) * ℓC ≤ 2 * ℓ → (1 + τ) * ℓC ≤ ℓ →
    ∀ C C' : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓC C → GoodCov2 j ℓC C' →
    TInv C → TInv C' → ∀ ℓΔ : ℝ, 0 ≤ ℓΔ → GoodCov2 j ℓΔ (C' - C) →
    ∀ V V' Wl Wl' : Fam d L N, InF j V → InF j V' → InF j Wl → InF j Wl' →
    FamCovG j Wl → FamCovG j Wl' →
    (∀ b, ε (V b : Alg d L N) = 0) → (∀ b, ε (V' b : Alg d L N) = 0) →
    ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
    Fnorm j ℓ V ≤ ENNReal.ofReal e → Fnorm j ℓ V' ≤ ENNReal.ofReal e →
    Fnorm j ℓ Wl ≤ ENNReal.ofReal (e ^ 2) → Fnorm j ℓ Wl' ≤ ENNReal.ofReal (e ^ 2) →
    ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
    Fnorm j ℓ (V' - V) ≤ ENNReal.ofReal a → Fnorm j ℓ (Wl' - Wl) ≤ ENNReal.ofReal b →
      Fnorm (j + 1) ℓ' (WlinNext j C' V' Wl' - WlinNext j C V Wl) ≤
        ENNReal.ofReal (4 * (4 * C₂ * e ^ 2 + 4 * (C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3)) * e ^ 2) *
          relDist e a b 0 ℓΔ τ ℓC) := by
  obtain ⟨C₀, hC₀, L₁, hT⟩ := TrL_contract'_ts d hd
  obtain ⟨L₂, hS⟩ := Src_bound_ts d hd
  refine ⟨C₀, hC₀, max L₁ L₂, fun L _ hL => ?_⟩
  obtain ⟨C₂, hC₂, hS⟩ := hS L ((le_max_right _ _).trans hL)
  refine ⟨C₂, hC₂, ?_⟩
  intro N j hjN ℓ ℓ' ℓC τ hℓ hℓ' hℓC hτ hsum hCℓ C C' hC hC' hCt hCt' ℓΔ hℓΔ hΔ V V' Wl Wl'
    hV hV' hW hW' hWc hWc' hV0 hV0' e he he1 hVe hVe' hWe hWe' a b ha hb hda hdb
  set κ := C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set B := 4 * C₂ * e ^ 2 + 4 * κ * e ^ 2 with hB
  have hB0 : 0 ≤ B := by positivity
  have hs0 := relDist_nonneg (ℓΔ := ℓΔ) (τ := τ) (ℓC := ℓC) he ha hb le_rfl
  -- the bound on the domain
  have bound : ∀ (Cz : Matrix (Lam d L N) (Lam d L N) ℂ) (ℓz : ℝ), 0 < ℓz → ℓ' + ℓz ≤ 2 * ℓ →
      ℓz ≤ ℓ → GoodCov2 j ℓz Cz → TInv Cz → ∀ Vz Wz : Fam d L N, InF j Vz → InF j Wz →
      FamCovG j Wz → (∀ b, ε (Vz b : Alg d L N) = 0) →
      Fnorm j ℓ Vz ≤ ENNReal.ofReal (2 * e) → Fnorm j ℓ Wz ≤ ENNReal.ofReal ((2 * e) ^ 2) →
      Fnorm (j + 1) ℓ' (WlinNext j Cz Vz Wz) ≤ ENNReal.ofReal B := by
    intro Cz ℓz hℓz hsz hzℓ hCz hCzt Vz Wz hVz hWz hWzc hVz0 hVv hWw
    rw [WlinNext]
    refine (Fnorm_add_le _ _ (by positivity) (by positivity)
      (hS N j hjN ℓ ℓ' ℓz hℓ hℓ' hℓz hsz hzℓ Cz hCz hCzt Vz hVz hVz0 (2 * e) (by positivity)
        (by linarith) hVv)
      (hT L ((le_max_left _ _).trans hL) N j hjN ℓ ℓ' ℓz hℓ hℓ' hℓz hsz hzℓ Cz hCz hCzt Wz hWz
        hWzc 1 (by simp) ((2 * e) ^ 2) (by positivity) hWw)).trans
      (ENNReal.ofReal_le_ofReal (le_of_eq (by rw [hB]; ring)))
  have hle : ∀ t : ℝ, Fnorm j ℓ V ≤ ENNReal.ofReal e → Fnorm j ℓ V ≤ ENNReal.ofReal (2 * e) :=
    fun _ h => h.trans (ENNReal.ofReal_le_ofReal (by linarith))
  have hsumC : ℓ' + ℓC ≤ 2 * ℓ := by nlinarith
  have hCℓ' : ℓC ≤ ℓ := by nlinarith
  have hW2 : ∀ {F : Fam d L N}, Fnorm j ℓ F ≤ ENNReal.ofReal (e ^ 2) →
      Fnorm j ℓ F ≤ ENNReal.ofReal ((2 * e) ^ 2) :=
    fun h => h.trans (ENNReal.ofReal_le_ofReal (by nlinarith))
  have hV2 : ∀ {F : Fam d L N}, Fnorm j ℓ F ≤ ENNReal.ofReal e →
      Fnorm j ℓ F ≤ ENNReal.ofReal (2 * e) :=
    fun h => h.trans (ENNReal.ofReal_le_ofReal (by linarith))
  have hΦ := WlinNext_hol_line j C C' V V' Wl Wl'
  have key := Fnorm_lip_line (j := j) hℓ' (fun z : ℂ => WlinNext j (C + z • (C' - C))
      (V + z • (V' - V)) (Wl + z • (Wl' - Wl))) hΦ hB0 hs0
    (by simpa using bound C ℓC hℓC hsumC hCℓ' hC hCt V Wl hV hW hWc hV0 (hV2 hVe) (hW2 hWe))
    (by simpa using (bound C' ℓC hℓC hsumC hCℓ' hC' hCt' V' Wl' hV' hW' hWc' hV0' (hV2 hVe')
      (hW2 hWe')))
    fun R hR2 hRs z hz => by
      have hR0 : 0 < R := by linarith
      obtain ⟨hRa, hRb, -, hRℓ⟩ := relDist_radius he ha hb le_rfl hτ hℓC hℓΔ hR0.le hRs
      obtain ⟨hVz, hWz⟩ := line_norms_F V V' Wl Wl' he.le hR0.le ha hb z hz hVe hWe hda hdb hRa hRb
      exact bound _ ((1 + τ) * ℓC) (by positivity) hsum hCℓ
        ((hC.line hΔ hℓΔ hz.le).mono (by nlinarith)) (hCt.line hCt' z) _ _
        (inF_add hV (inF_smul (inF_sub hV' hV) z)) (inF_add hW (inF_smul (inF_sub hW' hW) z))
        (famCovG_line hWc hWc' z) (eps_line hV0 hV0' z) hVz
        (hWz.trans (ENNReal.ofReal_le_ofReal (by nlinarith)))
  simpa using key

set_option maxHeartbeats 1000000 in
/-- **Joint Lipschitz bound for `D_{j+1}`.** -/
theorem Dnext_lip_joint (d : ℕ) (hd : 2 ≤ d) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ L₀ : ℕ,
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ C₃ : ℝ, 0 ≤ C₃ ∧
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ ℓ' ℓC τ : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → 0 < τ →
    ℓ' + (1 + τ) * ℓC ≤ 2 * ℓ → (1 + τ) * ℓC ≤ ℓ →
    ∀ C C' : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓC C → GoodCov2 j ℓC C' →
    TInv C → TInv C' → ∀ ℓΔ : ℝ, 0 ≤ ℓΔ → GoodCov2 j ℓΔ (C' - C) →
    ∀ V V' Wl Wl' D D' : Fam d L N, InF j V → InF j V' → InF j Wl → InF j Wl' →
    InF j D → InF j D' → FamCovG j D → FamCovG j D' →
    (∀ b, ε (V b : Alg d L N) = 0) → (∀ b, ε (V' b : Alg d L N) = 0) →
    ∀ e : ℝ, 0 < e → e ≤ 1 / 4 →
    Fnorm j ℓ V ≤ ENNReal.ofReal e → Fnorm j ℓ V' ≤ ENNReal.ofReal e →
    Fnorm j ℓ Wl ≤ ENNReal.ofReal (e ^ 2) → Fnorm j ℓ Wl' ≤ ENNReal.ofReal (e ^ 2) →
    Fnorm j ℓ D ≤ ENNReal.ofReal (e ^ 2) → Fnorm j ℓ D' ≤ ENNReal.ofReal (e ^ 2) →
    ∀ a b c : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c →
    Fnorm j ℓ (V' - V) ≤ ENNReal.ofReal a → Fnorm j ℓ (Wl' - Wl) ≤ ENNReal.ofReal b →
    Fnorm j ℓ (D' - D) ≤ ENNReal.ofReal c →
      Fnorm (j + 1) ℓ' (Dnext j C' V' Wl' D' - Dnext j C V Wl D) ≤
        ENNReal.ofReal (4 * (2 * (C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3)) * e ^ 2 + 64 * C₃ * e ^ 4) *
          relDist e a (b + c) c ℓΔ τ ℓC) := by
  obtain ⟨C₀, hC₀, L₁, hT⟩ := Dnext_bound_ts d hd
  refine ⟨C₀, hC₀, L₁, fun L _ hL => ?_⟩
  obtain ⟨C₃, hC₃, hT⟩ := hT L hL
  refine ⟨C₃, hC₃, ?_⟩
  intro N j hjN ℓ ℓ' ℓC τ hℓ hℓ' hℓC hτ hsum hCℓ C C' hC hC' hCt hCt' ℓΔ hℓΔ hΔ V V' Wl Wl' D D'
    hV hV' hW hW' hD hD' hDc hDc' hV0 hV0' e he he1 hVe hVe' hWe hWe' hDe hDe' a b c ha hb hc
    hda hdb hdc
  set κ := C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set B := 2 * κ * e ^ 2 + 64 * C₃ * e ^ 4 with hB
  have hB0 : 0 ≤ B := by positivity
  have hs0 := relDist_nonneg (ℓΔ := ℓΔ) (τ := τ) (ℓC := ℓC) he ha (add_nonneg hb hc) hc
  have bound : ∀ (Cz : Matrix (Lam d L N) (Lam d L N) ℂ) (ℓz : ℝ), 0 < ℓz → ℓ' + ℓz ≤ 2 * ℓ →
      ℓz ≤ ℓ → GoodCov2 j ℓz Cz → TInv Cz → ∀ Vz Wz Dz : Fam d L N, InF j Vz → InF j Wz →
      InF j Dz → FamCovG j Dz → (∀ b, ε (Vz b : Alg d L N) = 0) →
      Fnorm j ℓ Vz ≤ ENNReal.ofReal (2 * e) → Fnorm j ℓ Wz ≤ ENNReal.ofReal (2 * e ^ 2) →
      Fnorm j ℓ Dz ≤ ENNReal.ofReal (2 * e ^ 2) →
      Fnorm (j + 1) ℓ' (Dnext j Cz Vz Wz Dz) ≤ ENNReal.ofReal B := by
    intro Cz ℓz hℓz hsz hzℓ hCz hCzt Vz Wz Dz hVz hWz hDz hDzc hVz0 hVv hWw hDd
    have hWD : Fnorm j ℓ (Wz + Dz) ≤ ENNReal.ofReal (4 * e ^ 2) :=
      (Fnorm_add_le _ _ (by positivity) (by positivity) hWw hDd).trans
        (ENNReal.ofReal_le_ofReal (by linarith))
    refine (hT N j hjN ℓ ℓ' ℓz hℓ hℓ' hℓz hsz hzℓ Cz hCz hCzt Vz Wz Dz hVz hWz hDz hDzc hVz0
      (2 * e) (4 * e ^ 2) (2 * e ^ 2) (by positivity) (by positivity) (by positivity)
      (by linarith) (by nlinarith) hVv hWD hDd).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hB]; nlinarith [sq_nonneg e]
  have hsumC : ℓ' + ℓC ≤ 2 * ℓ := by nlinarith
  have hCℓ' : ℓC ≤ ℓ := by nlinarith
  have h2e : ∀ {F : Fam d L N} {t : ℝ}, 0 ≤ t → Fnorm j ℓ F ≤ ENNReal.ofReal t →
      Fnorm j ℓ F ≤ ENNReal.ofReal (2 * t) :=
    fun ht h => h.trans (ENNReal.ofReal_le_ofReal (by linarith))
  have key := Fnorm_lip_line (j := j) hℓ' (fun z : ℂ => Dnext j (C + z • (C' - C))
      (V + z • (V' - V)) (Wl + z • (Wl' - Wl)) (D + z • (D' - D)))
    (Dnext_hol_line j C C' V V' Wl Wl' D D') hB0 hs0
    (by simpa using (bound C ℓC hℓC hsumC hCℓ' hC hCt V Wl D hV hW hD hDc hV0 (h2e he.le hVe)
      (h2e (sq_nonneg e) hWe) (h2e (sq_nonneg e) hDe)))
    (by simpa using (bound C' ℓC hℓC hsumC hCℓ' hC' hCt' V' Wl' D' hV' hW' hD' hDc' hV0'
      (h2e he.le hVe') (h2e (sq_nonneg e) hWe') (h2e (sq_nonneg e) hDe')))
    fun R hR2 hRs z hz => by
      have hR0 : 0 < R := by linarith
      obtain ⟨hRa, hRbc, hRc, hRℓ⟩ := relDist_radius he ha (add_nonneg hb hc) hc hτ hℓC hℓΔ
        hR0.le hRs
      have hRb : R * b ≤ e ^ 2 := le_trans (mul_le_mul_of_nonneg_left (by linarith) hR0.le) hRbc
      obtain ⟨hVz, hWz⟩ := line_norms_F V V' Wl Wl' he.le hR0.le ha hb z hz hVe hWe hda hdb hRa hRb
      obtain ⟨-, hDz⟩ := line_norms_F V V' D D' he.le hR0.le ha hc z hz hVe hDe hda hdc hRa hRc
      exact bound _ ((1 + τ) * ℓC) (by positivity) hsum hCℓ
        ((hC.line hΔ hℓΔ hz.le).mono (by nlinarith)) (hCt.line hCt' z) _ _ _
        (inF_add hV (inF_smul (inF_sub hV' hV) z)) (inF_add hW (inF_smul (inF_sub hW' hW) z))
        (inF_add hD (inF_smul (inF_sub hD' hD) z)) (famCovG_line hDc hDc' z)
        (eps_line hV0 hV0' z) hVz hWz hDz
  simpa using key

theorem Src_hol_line (j : ℕ) (C C' : Matrix (Lam d L N) (Lam d L N) ℂ) (V V' : Fam d L N)
    (c : Fin d → ℕ) : HolE (fun z : ℂ => SrcL j (C + z • (C' - C)) (EthEL (C + z • (C' - C)))
      (V + z • (V' - V)) (V + z • (V' - V)) c) := by
  have hVf : ∀ b, HolE (fun z : ℂ => (V + z • (V' - V)) b) := fun b =>
    (HolE.const _).add (HolE.smul differentiable_id (HolE.const _))
  have h1 := HolE.sum (blocks j (blockSet (L := L) (N := N) (j + 1) c)) fun b _ =>
    Wp_holC (Cf := fun z : ℂ => C + z • (C' - C)) j (fun x y => cov_line_diff x y)
      (Vf := fun z : ℂ => V + z • (V' - V)) (Wf := fun _ => (0 : Fam d L N)) hVf
      (fun _ => HolE.const (0 : EvR (Lam d L N))) b
  refine Hol.congr h1 fun z => ?_
  show ((SrcL j _ _ _ _ c : EvR (Lam d L N)) : Alg d L N) = _
  rw [SrcL_eq_Wp]

theorem TrL_hol_line (j : ℕ) (C C' : Matrix (Lam d L N) (Lam d L N) ℂ) (W W' : Fam d L N)
    (c : Fin d → ℕ) : HolE (fun z : ℂ => TrL j (C + z • (C' - C)) 1 (W + z • (W' - W)) c) := by
  have hWf : ∀ b, HolE (fun z : ℂ => (W + z • (W' - W)) b) := fun b =>
    (HolE.const _).add (HolE.smul differentiable_id (HolE.const _))
  have h2 := HolE.sum (blocks j (blockSet (L := L) (N := N) (j + 1) c)) fun b _ =>
    Wp_holC (Cf := fun z : ℂ => C + z • (C' - C)) j (fun x y => cov_line_diff x y)
      (Vf := fun _ => (0 : Fam d L N))
      (Wf := fun z : ℂ => fun b' => sigE 1 ((W + z • (W' - W)) b'))
      (fun _ => HolE.const _) (fun b' => holE_sigE (differentiable_const 1) (hWf b')) b
  refine Hol.congr h2 fun z => ?_
  show ((TrL j _ 1 _ c : EvR (Lam d L N)) : Alg d L N) = _
  rw [TrL_eq_Wp]

set_option maxHeartbeats 1000000 in
/-- **Joint Lipschitz bound for the quadratic source** in `(C, V)`. -/
theorem Src_lip_joint (d : ℕ) (hd : 2 ≤ d) : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ ℓ' ℓC τ : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → 0 < τ →
    ℓ' + (1 + τ) * ℓC ≤ 2 * ℓ → (1 + τ) * ℓC ≤ ℓ →
    ∀ C C' : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓC C → GoodCov2 j ℓC C' →
    TInv C → TInv C' → ∀ ℓΔ : ℝ, 0 ≤ ℓΔ → GoodCov2 j ℓΔ (C' - C) →
    ∀ V V' : Fam d L N, InF j V → InF j V' →
    (∀ b, ε (V b : Alg d L N) = 0) → (∀ b, ε (V' b : Alg d L N) = 0) →
    ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
    Fnorm j ℓ V ≤ ENNReal.ofReal e → Fnorm j ℓ V' ≤ ENNReal.ofReal e →
    ∀ a : ℝ, 0 ≤ a → Fnorm j ℓ (V' - V) ≤ ENNReal.ofReal a →
      Fnorm (j + 1) ℓ' (SrcL j C' (EthEL C') V' V' - SrcL j C (EthEL C) V V) ≤
        ENNReal.ofReal (4 * (4 * C₂ * e ^ 2) * relDist e a 0 0 ℓΔ τ ℓC) := by
  obtain ⟨L₂, hS⟩ := Src_bound_ts d hd
  refine ⟨L₂, fun L _ hL => ?_⟩
  obtain ⟨C₂, hC₂, hS⟩ := hS L hL
  refine ⟨C₂, hC₂, ?_⟩
  intro N j hjN ℓ ℓ' ℓC τ hℓ hℓ' hℓC hτ hsum hCℓ C C' hC hC' hCt hCt' ℓΔ hℓΔ hΔ V V'
    hV hV' hV0 hV0' e he he1 hVe hVe' a ha hda
  set B := 4 * C₂ * e ^ 2 with hB
  have hB0 : 0 ≤ B := by positivity
  have hs0 := relDist_nonneg (ℓΔ := ℓΔ) (τ := τ) (ℓC := ℓC) he ha le_rfl le_rfl
  have bound : ∀ (Cz : Matrix (Lam d L N) (Lam d L N) ℂ) (ℓz : ℝ), 0 < ℓz → ℓ' + ℓz ≤ 2 * ℓ →
      ℓz ≤ ℓ → GoodCov2 j ℓz Cz → TInv Cz → ∀ Vz : Fam d L N, InF j Vz →
      (∀ b, ε (Vz b : Alg d L N) = 0) → Fnorm j ℓ Vz ≤ ENNReal.ofReal (2 * e) →
      Fnorm (j + 1) ℓ' (SrcL j Cz (EthEL Cz) Vz Vz) ≤ ENNReal.ofReal B := by
    intro Cz ℓz hℓz hsz hzℓ hCz hCzt Vz hVz hVz0 hVv
    refine (hS N j hjN ℓ ℓ' ℓz hℓ hℓ' hℓz hsz hzℓ Cz hCz hCzt Vz hVz hVz0 (2 * e) (by positivity)
      (by linarith) hVv).trans (ENNReal.ofReal_le_ofReal (le_of_eq (by rw [hB]; ring)))
  have hsumC : ℓ' + ℓC ≤ 2 * ℓ := by nlinarith
  have hCℓ' : ℓC ≤ ℓ := by nlinarith
  have hV2 : ∀ {F : Fam d L N}, Fnorm j ℓ F ≤ ENNReal.ofReal e →
      Fnorm j ℓ F ≤ ENNReal.ofReal (2 * e) :=
    fun h => h.trans (ENNReal.ofReal_le_ofReal (by linarith))
  have key := Fnorm_lip_line (j := j) hℓ' (fun z : ℂ => SrcL j (C + z • (C' - C))
      (EthEL (C + z • (C' - C))) (V + z • (V' - V)) (V + z • (V' - V)))
    (Src_hol_line j C C' V V') hB0 hs0
    (by simpa using (bound C ℓC hℓC hsumC hCℓ' hC hCt V hV hV0 (hV2 hVe)))
    (by simpa using (bound C' ℓC hℓC hsumC hCℓ' hC' hCt' V' hV' hV0' (hV2 hVe')))
    fun R hR2 hRs z hz => by
      have hR0 : 0 < R := by linarith
      obtain ⟨hRa, -, -, hRℓ⟩ := relDist_radius he ha le_rfl le_rfl hτ hℓC hℓΔ hR0.le hRs
      have hVz : Fnorm j ℓ (V + z • (V' - V)) ≤ ENNReal.ofReal (2 * e) :=
        (seg_norm V (V' - V) he.le hR0.le ha z hz hVe hda).trans
          (ENNReal.ofReal_le_ofReal (by linarith))
      exact bound _ ((1 + τ) * ℓC) (by positivity) hsum hCℓ
        ((hC.line hΔ hℓΔ hz.le).mono (by nlinarith)) (hCt.line hCt' z) _
        (inF_add hV (inF_smul (inF_sub hV' hV) z)) (eps_line hV0 hV0' z) hVz
  simpa using key

set_option maxHeartbeats 1000000 in
/-- **Joint Lipschitz bound for the linear transport** in `(C, 𝒲)`:
`4 (2 κ w)(‖δ𝒲‖/w + ℓ_Δ²/(τℓ_C)²)`. -/
theorem TrL_lip_joint (d : ℕ) (hd : 2 ≤ d) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ L₀ : ℕ,
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ ℓ' ℓC τ : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → 0 < τ →
    ℓ' + (1 + τ) * ℓC ≤ 2 * ℓ → (1 + τ) * ℓC ≤ ℓ →
    ∀ C C' : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓC C → GoodCov2 j ℓC C' →
    TInv C → TInv C' → ∀ ℓΔ : ℝ, 0 ≤ ℓΔ → GoodCov2 j ℓΔ (C' - C) →
    ∀ W W' : Fam d L N, InF j W → InF j W' → FamCovG j W → FamCovG j W' →
    ∀ w : ℝ, 0 < w → Fnorm j ℓ W ≤ ENNReal.ofReal w → Fnorm j ℓ W' ≤ ENNReal.ofReal w →
    ∀ b : ℝ, 0 ≤ b → Fnorm j ℓ (W' - W) ≤ ENNReal.ofReal b →
      Fnorm (j + 1) ℓ' (TrL j C' 1 W' - TrL j C 1 W) ≤
        ENNReal.ofReal (4 * (2 * (C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3)) * w) *
          (b / w + ℓΔ ^ 2 / (τ * ℓC) ^ 2)) := by
  obtain ⟨C₀, hC₀, L₁, hT⟩ := TrL_contract'_ts d hd
  refine ⟨C₀, hC₀, L₁, fun L _ hL => ?_⟩
  intro N j hjN ℓ ℓ' ℓC τ hℓ hℓ' hℓC hτ hsum hCℓ C C' hC hC' hCt hCt' ℓΔ hℓΔ hΔ W W'
    hW hW' hWc hWc' w hw hWe hWe' b hb hdb
  set κ := C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set B := 2 * κ * w with hB
  have hB0 : 0 ≤ B := by positivity
  have hs0 : 0 ≤ b / w + ℓΔ ^ 2 / (τ * ℓC) ^ 2 := by positivity
  have bound : ∀ (Cz : Matrix (Lam d L N) (Lam d L N) ℂ) (ℓz : ℝ), 0 < ℓz → ℓ' + ℓz ≤ 2 * ℓ →
      ℓz ≤ ℓ → GoodCov2 j ℓz Cz → TInv Cz → ∀ Wz : Fam d L N, InF j Wz → FamCovG j Wz →
      Fnorm j ℓ Wz ≤ ENNReal.ofReal (2 * w) →
      Fnorm (j + 1) ℓ' (TrL j Cz 1 Wz) ≤ ENNReal.ofReal B := by
    intro Cz ℓz hℓz hsz hzℓ hCz hCzt Wz hWz hWzc hWw
    refine (hT L hL N j hjN ℓ ℓ' ℓz hℓ hℓ' hℓz hsz hzℓ Cz hCz hCzt Wz hWz hWzc 1 (by simp) (2 * w)
      (by positivity) hWw).trans (ENNReal.ofReal_le_ofReal (le_of_eq (by rw [hB]; ring)))
  have hsumC : ℓ' + ℓC ≤ 2 * ℓ := by nlinarith
  have hCℓ' : ℓC ≤ ℓ := by nlinarith
  have hW2 : ∀ {F : Fam d L N}, Fnorm j ℓ F ≤ ENNReal.ofReal w →
      Fnorm j ℓ F ≤ ENNReal.ofReal (2 * w) :=
    fun h => h.trans (ENNReal.ofReal_le_ofReal (by linarith))
  have key := Fnorm_lip_line (j := j) hℓ' (fun z : ℂ => TrL j (C + z • (C' - C)) 1
      (W + z • (W' - W))) (TrL_hol_line j C C' W W') hB0 hs0
    (by simpa using (bound C ℓC hℓC hsumC hCℓ' hC hCt W hW hWc (hW2 hWe)))
    (by simpa using (bound C' ℓC hℓC hsumC hCℓ' hC' hCt' W' hW' hWc' (hW2 hWe')))
    fun R hR2 hRs z hz => by
      have hR0 : 0 < R := by linarith
      have hRb : R * b ≤ w := by
        have h1 : R * (b / w) ≤ 1 := by
          have : R * (b / w) ≤ R * (b / w + ℓΔ ^ 2 / (τ * ℓC) ^ 2) :=
            mul_le_mul_of_nonneg_left (by have : 0 ≤ ℓΔ ^ 2 / (τ * ℓC) ^ 2 := by positivity
                                          linarith) hR0.le
          linarith
        rw [← mul_div_assoc, div_le_one hw] at h1; exact h1
      have hRℓ : Real.sqrt R * ℓΔ ≤ τ * ℓC := by
        have h1 : R * (ℓΔ ^ 2 / (τ * ℓC) ^ 2) ≤ 1 := by
          have : R * (ℓΔ ^ 2 / (τ * ℓC) ^ 2) ≤ R * (b / w + ℓΔ ^ 2 / (τ * ℓC) ^ 2) :=
            mul_le_mul_of_nonneg_left (by have : 0 ≤ b / w := by positivity
                                          linarith) hR0.le
          linarith
        rw [← mul_div_assoc, div_le_one (by positivity)] at h1
        have h5 : (Real.sqrt R * ℓΔ) ^ 2 ≤ (τ * ℓC) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hR0.le]; exact h1
        exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 h5
      have hWz : Fnorm j ℓ (W + z • (W' - W)) ≤ ENNReal.ofReal (2 * w) :=
        (seg_norm W (W' - W) hw.le hR0.le hb z hz hWe hdb).trans
          (ENNReal.ofReal_le_ofReal (by linarith))
      exact bound _ ((1 + τ) * ℓC) (by positivity) hsum hCℓ
        ((hC.line hΔ hℓΔ hz.le).mono (by nlinarith)) (hCt.line hCt' z) _
        (inF_add hW (inF_smul (inF_sub hW' hW) z)) (famCovG_line hWc hWc' z) hWz
  simpa using key

end

end Step2
