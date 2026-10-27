import Step2.Coup.CoupPast6

/-!
# Estimates for the coefficient maps (`h02uv-outline.tex`, Proposition `prop:C4b`(d))

* `tNorm_sig_le`: `‖σ_s F‖_{T(ℓ)} ≤ ‖F‖_{T(ℓ)}` for `|s| ≤ 1`. The order-`n` coefficients are
  scaled by `sⁿ`, so `⟨σ_s F, g⟩ = ⟨F, g'⟩` with `g'_n = sⁿ g_n` and `‖g'‖_Φ ≤ ‖g‖_Φ`.
* `sumWp_cov`, `TrL_cov`: translation covariance of the linear transport.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Matrix

/-! ### The rescaling does not increase the norm -/

section SigNorm

variable {X : Type*} [DecidableEq X] [Fintype X] {E : Type*} [Fintype E] [DecidableEq E]
  [AddAction (E → ℕ) X]

theorem nab_const_mul {n : ℕ} (α : Fin n → E → ℕ) (c : ℂ) (f : (Fin n → Sf X) → ℂ)
    (z : Fin n → Sf X) : nab α (fun z => c * f z) z = c * nab α f z := by
  simp only [nab, nabla_apply, mul_sum]
  refine sum_congr rfl fun β _ => ?_
  rw [Algebra.smul_def, Algebra.smul_def]; ring

/-- **`‖σ_s F‖_{T(ℓ)} ≤ ‖F‖_{T(ℓ)}` for `|s| ≤ 1`.** -/
theorem tNorm_sig_le {p : ℕ} {h ℓ : ℝ} (hh : 0 ≤ h) (hℓ : 0 < ℓ) {s : ℂ} (hs : ‖s‖ ≤ 1)
    (F : N X) : tNorm E p h ℓ (sig s F) ≤ tNorm E p h ℓ F := by
  refine iSup₂_le fun g hg => ?_
  set g' : TestFn X := fun n z => s ^ n * g n z
  have hpair : pair (sig s F) g = pair F g' := by
    unfold pair
    refine sum_congr rfl fun n _ => ?_
    congr 1
    refine sum_congr rfl fun z _ => ?_
    rw [coeff_sig]; simp only [g']; ring
  have hg' : phiNorm E p h ℓ g' ≤ 1 := by
    refine le_trans ?_ hg
    refine iSup_le fun n => iSup_le fun z => iSup_le fun α => iSup_le fun hα => ?_
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) (phiTerm_le g z α hα)
    unfold phiTerm
    have e : nab α (g' n) z = s ^ n * nab α (g n) z := nab_const_mul α (s ^ n) (g n) z
    rw [e, norm_mul, norm_pow]
    have h1 : ‖s‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg _) hs
    have h2 : 0 ≤ ℓ⁻¹ ^ n * h ^ ord α := by positivity
    calc ℓ⁻¹ ^ n * h ^ ord α * (‖s‖ ^ n * ‖nab α (g n) z‖)
        = ‖s‖ ^ n * (ℓ⁻¹ ^ n * h ^ ord α * ‖nab α (g n) z‖) := by ring
      _ ≤ 1 * (ℓ⁻¹ ^ n * h ^ ord α * ‖nab α (g n) z‖) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = _ := one_mul _
  rw [hpair]
  exact le_iSup₂_of_le g' hg' le_rfl

end SigNorm

/-! ### Translation covariance of the linear transport -/

variable {d L N : ℕ} [NeZero L]

theorem autAlg_sig (e : Lam d L N ≃ Lam d L N) (s : ℂ) (F : Alg d L N) :
    autAlg e (sig s F) = sig s (autAlg e F) := by
  rw [autAlg, sig, ← AlgHom.comp_apply, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map,
    ExteriorAlgebra.map_comp_map]
  congr 2

theorem famCovG_sig {j : ℕ} {F : Fam d L N} (hF : FamCovG j F) (s : ℂ) :
    FamCovG j (fun b => sigE s (F b)) := by
  intro t ht b hb
  simp only [coe_sigE]
  rw [hF t ht b hb, autAlg_sig]

theorem famCovG_zero (j : ℕ) : FamCovG (L := L) (N := N) j (0 : Fam d L N) := by
  intro t ht b hb; simp

/-- **Covariance of `∑_{B ⊆ B_+} 𝒲'(B)`** (the linear part of `Wnext2`). -/
theorem sumWp_cov {j : ℕ} {ℓ : ℝ} {C : Matrix (Lam d L N) (Lam d L N) ℂ} {V W : Fam d L N}
    (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hj2 : j + 2 < N)
    (hC : GoodCov2 j ℓ C) (hCt : TInv C) (hV : InF j V) (hW : InF j W) (hVc : FamCovG j V)
    (hWc : FamCovG j W) :
    FamCovG (j + 1) (fun c => ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c),
      Wp j C V W b) := by
  intro t ht c hc
  have ht' : ∀ i, L ^ j ∣ (co t i).val := fun i => (pow_dvd_pow L (Nat.le_succ j)).trans (ht i)
  have hP := Flow.presBlocks_transl' (by omega) t ht'
  have hP1 := Flow.presBlocks_transl' (by omega) t ht
  have hWp : ∀ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c),
      Wp j C V W (bmap j (AffAut.transl t) b) = AE (AffAut.transl t) (Wp j C V W b) :=
    fun b hb => Subtype.ext (by
      rw [coe_AE]; exact Wp_transl hd hL hj2 hC hCt hV hW hVc hWc ht (mem_blockIdx_of_mem_blocks hb))
  have e : (∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) (bmap (j + 1) (AffAut.transl t) c)),
      Wp j C V W b) = AE (AffAut.transl t) (∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c),
        Wp j C V W b) := by
    rw [← img_blockSet_bmap (IsGen.transl t) (by omega) hP1 hc, blocks_img_bmap hP, map_sum,
      sum_image fun b hb b' hb' e => bmap_injOn (IsGen.transl t) (by omega) hP
        (mem_blockIdx_of_mem_blocks hb) (mem_blockIdx_of_mem_blocks hb') e]
    exact sum_congr rfl fun b hb => hWp b hb
  show ((∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) (bmap (j + 1) (AffAut.transl t) c)),
      Wp j C V W b : EvR (Lam d L N)) : Alg d L N) = _
  rw [e, coe_AE]
  rfl

/-- **Covariance of the linear transport.** -/
theorem TrL_cov {i : ℕ} {ℓ : ℝ} {C : Matrix (Lam d L N) (Lam d L N) ℂ} (hd : 1 ≤ d)
    (hL : 2 ^ (d + 3) ≤ L) (hi2 : i + 2 < N) (hC : GoodCov2 i ℓ C) (hCt : TInv C) (s : ℂ)
    {F : Fam d L N} (hF : InF i F) (hFc : FamCovG i F) : FamCovG (i + 1) (TrL i C s F) := by
  have h := sumWp_cov (V := 0) (W := fun b => sigE s (F b)) hd hL hi2 hC hCt (inF_zero i)
    (inF_sig hF s) (famCovG_zero i) (famCovG_sig hFc s)
  intro t ht c hc
  have e : ∀ c, TrL i C s F c = ∑ b ∈ blocks i (blockSet (L := L) (N := N) (i + 1) c),
      Wp i C 0 (fun b' => sigE s (F b')) b := fun c => TrL_eq_Wp i C s F c
  rw [e, e]
  exact h t ht c hc

/-! ### Norms of families -/

theorem Fnorm_sig_le {j : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {s : ℂ} (hs : ‖s‖ ≤ 1) (F : Fam d L N) :
    Fnorm j ℓ (fun b => sigE s (F b)) ≤ Fnorm j ℓ F := by
  refine iSup₂_le fun b hb => le_iSup₂_of_le b hb ?_
  rw [coe_sigE]
  exact tNorm_sig_le (by positivity) hℓ hs _

theorem Tj_le_Fnorm {j : ℕ} {ℓ : ℝ} (F : Fam d L N) {b : Fin d → ℕ}
    (hb : b ∈ blockIdx (L := L) (N := N) j) : Tj d (L : ℝ) j ℓ (F b : Alg d L N) ≤ Fnorm j ℓ F :=
  le_iSup₂ (f := fun b (_ : b ∈ blockIdx (L := L) (N := N) j) => Tj d (L : ℝ) j ℓ (F b : Alg d L N))
    b hb

/-! ### The contraction of one transport -/

/-- **One linear transport contracts**: `‖T 𝒲‖_{i+1} ≤ C₀ L^{d-3} ‖𝒲‖_i` for covariant `𝒲`,
`|s| ≤ 1` and a translation-invariant covariance with `GoodCov2`. -/
theorem TrL_contract_ts (d : ℕ) (hd : 2 ≤ d) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ L₀ : ℕ,
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∀ (N i : ℕ), i + 1 < N → ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ → ℓC ≤ ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 i ℓC C → TInv C →
    ∀ F : Fam d L N, InF i F → FamCovG i F → ∀ s : ℂ, ‖s‖ ≤ 1 →
    ∀ w : ℝ, 0 ≤ w → w ≤ 1 → Fnorm i ℓ F ≤ ENNReal.ofReal w →
      Fnorm (i + 1) ℓ' (TrL i C s F) ≤ ENNReal.ofReal (C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3) * w) := by
  classical
  obtain ⟨Cl, hCl0, hloc⟩ := exists_Loc2sXY_bound d (by omega)
  obtain ⟨Cc, hCc0, L₁, hcon⟩ := loc2s_contract d hd
  obtain ⟨cc, hcc⟩ := card_small_containing d
  refine ⟨(1 + Cl) * (1 + 16 * Cl) * Cc, by positivity,
    max (max (2 ^ (d + 3) + 8 * d + 1) ⌈pauliL0 d⌉₊) L₁, ?_⟩
  intro L _ hL N i hiN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum hCℓ C hC hT F hF hFc s hs w hw0 hw1 hFw
  have hL8 : 2 ^ (d + 3) + 8 * d < L :=
    lt_of_lt_of_le (Nat.lt_succ_self _) ((le_max_left _ _).trans ((le_max_left _ _).trans hL))
  have hLp : pauliL0 d ≤ L := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right _ _).trans ((le_max_left _ _).trans hL))
  have hL₁ : L₁ ≤ L := (le_max_right _ _).trans hL
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set W : Fam d L N := fun b => sigE s (F b)
  have hW : InF i W := inF_sig hF s
  have hWc : FamCov i W := (famCovG_sig hFc s).toFamCov (by omega)
  have hwb : ∀ b ∈ blockIdx (L := L) (N := N) i, Tj d (L : ℝ) i ℓ (W b : Alg d L N) ≤
      ENNReal.ofReal w := fun b hb =>
    ((Tj_le_Fnorm W hb).trans (Fnorm_sig_le hℓ hs F)).trans hFw
  have hT0 : Tj d (L : ℝ) i ℓ (0 : Alg d L N) = 0 := Tj_zero _ _ _
  have hvb : ∀ b ∈ blockIdx (L := L) (N := N) i, Tj d (L : ℝ) i ℓ ((0 : Fam d L N) b : Alg d L N) ≤
      ENNReal.ofReal 0 := fun b _ => by simp [hT0]
  have hK0 : InK2 i (0 : Act d L N) :=
    { loc := fun _ _ => zero_mem _, sym := fun _ _ => (isSym_iff_mem_SymS _).2 (zero_mem _) }
  have H : BH i ℓ ℓ' ℓC C 0 W (0 : Act d L N) 1 1 Cl (cc + 1) :=
    { hd := by omega, hLp := hLp, hL8 := hL8, hjN := hiN, hℓ := hℓ, hℓ' := hℓ', hℓC := hℓC, hsum := hsum, hC := hC, hV := inF_zero i,
      hW := hW, hV0 := fun _ => by simp, hK := hK0, hA := le_rfl, hr := zero_le_one, hr1 := le_rfl
      hVr := fun b hb => by simp [hT0]
      hWr := fun b hb => (hwb b hb).trans (ENNReal.ofReal_le_ofReal hw1)
      hKr := by rw [Knorm_zero]; exact zero_le
      hCl := hCl0
      hloc := fun k hk ℓ₀ hℓ₀ X Y hX hYX G hG => hloc L hL8 N k hk X Y hX hYX G hG ℓ₀ hℓ₀
      hcS := by linarith [Nat.cast_nonneg (α := ℝ) cc]
      hcount := fun b hb => by
        have h1 : ((smallSets (d := d) (L := L) (N := N) i).filter
            (fun X => blockSet i b ⊆ X)).card ≤ cc := by convert hcc L N i b hb
        have h2 := Nat.cast_le (α := ℝ) |>.2 h1
        push_cast; linarith }
  have hcon' : ∀ ℓ₀ ℓ₁ : ℝ, 0 < ℓ₀ → 0 < ℓ₁ → ℓ₁ ≤ 2 * ℓ₀ → ∀ X : Finset (Lam d L N), IsSmall i X →
      ∀ G ∈ NX (nbhd i X : Set (Lam d L N)), IsSym G →
        Tj d (L : ℝ) (i + 1) ℓ₁ (G - Loc2sX X G) ≤
          ENNReal.ofReal (Cc / (L : ℝ) ^ 3) * Tj d (L : ℝ) i ℓ₀ G :=
    fun ℓ₀ ℓ₁ h0 h1 h2 X hX G hG hs => hcon L hL8 hL₁ N i (by omega) ℓ₀ ℓ₁ h0 h1 h2 X hX G hG hs
  refine iSup₂_le fun c' hc' => ?_
  rw [TrL_eq_Wp]
  refine (H.sumWp_le le_rfl hw0 hvb hwb hCc0 hcon' hCℓ hT hWc hc').trans
    (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  field_simp
  ring

/-- **`TrL_contract` without the restriction `w ≤ 1`** (by linearity). -/
theorem TrL_contract'_ts (d : ℕ) (hd : 2 ≤ d) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ L₀ : ℕ,
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∀ (N i : ℕ), i + 1 < N → ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ → ℓC ≤ ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 i ℓC C → TInv C →
    ∀ F : Fam d L N, InF i F → FamCovG i F → ∀ s : ℂ, ‖s‖ ≤ 1 →
    ∀ w : ℝ, 0 ≤ w → Fnorm i ℓ F ≤ ENNReal.ofReal w →
      Fnorm (i + 1) ℓ' (TrL i C s F) ≤ ENNReal.ofReal (C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3) * w) := by
  obtain ⟨C₀, hC₀, L₀, h⟩ := TrL_contract_ts d hd
  refine ⟨C₀, hC₀, L₀, fun L _ hL N i hiN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum hCℓ C hC hT F hF hFc s hs w hw0 hFw => ?_⟩
  rcases hw0.eq_or_lt with rfl | hwpos
  · exact h L hL N i hiN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum hCℓ C hC hT F hF hFc s hs 0 le_rfl zero_le_one hFw
  · set c : ℂ := ((w⁻¹ : ℝ) : ℂ)
    have hc : ‖c‖ = w⁻¹ := by simp [c, abs_of_pos hwpos]
    have hF' : InF i (fun b => c • F b) := inF_smul hF c
    have hFc' : FamCovG i (fun b => c • F b) := fun t ht b hb => by
      simp only [Subalgebra.coe_smul, map_smul, hFc t ht b hb]
    have hFw' : Fnorm i ℓ (fun b => c • F b) ≤ ENNReal.ofReal 1 := by
      rw [Fnorm_smul, hc]
      calc ENNReal.ofReal w⁻¹ * Fnorm i ℓ F ≤ ENNReal.ofReal w⁻¹ * ENNReal.ofReal w :=
            mul_le_mul_left' hFw _
        _ = ENNReal.ofReal 1 := by
            rw [← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ hwpos.ne']
    have h1 := h L hL N i hiN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum hCℓ C hC hT _ hF' hFc' s hs 1 zero_le_one le_rfl hFw'
    have e : TrL i C s (fun b => c • F b) = fun b => c • TrL i C s F b := by
      rw [show (fun b => c • F b) = c • F from rfl, map_smul]; rfl
    rw [e, Fnorm_smul, hc] at h1
    have hw' : (0 : ℝ) < w⁻¹ := inv_pos.2 hwpos
    calc Fnorm (i + 1) ℓ' (TrL i C s F)
        = ENNReal.ofReal w * (ENNReal.ofReal w⁻¹ * Fnorm (i + 1) ℓ' (TrL i C s F)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hwpos.le, mul_inv_cancel₀ hwpos.ne',
            ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal w * ENNReal.ofReal (C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3) * 1) :=
          mul_le_mul_left' h1 _
      _ = _ := by rw [← ENNReal.ofReal_mul hwpos.le]; ring_nf

/-- **`TrL_contract` without the restriction `w ≤ 1`** (by linearity). -/
theorem TrL_contract' (d : ℕ) (hd : 2 ≤ d) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ L₀ : ℕ,
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∀ (N i : ℕ), i + 1 < N → ∀ ℓ : ℝ, 0 < ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 i ℓ C → TInv C →
    ∀ F : Fam d L N, InF i F → FamCovG i F → ∀ s : ℂ, ‖s‖ ≤ 1 →
    ∀ w : ℝ, 0 ≤ w → Fnorm i ℓ F ≤ ENNReal.ofReal w →
      Fnorm (i + 1) ℓ (TrL i C s F) ≤ ENNReal.ofReal (C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3) * w) := by
  obtain ⟨C₀, hC₀, L₀, h⟩ := TrL_contract'_ts d hd
  exact ⟨C₀, hC₀, L₀, fun L _ hL N i hiN ℓ hℓ C hC =>
    h L hL N i hiN ℓ ℓ ℓ hℓ hℓ hℓ (by linarith) le_rfl C hC⟩

/-- **The source bound**: `‖Src_k(V, V)‖_{k+1} ≤ C(L) v²` for `‖V‖_k ≤ v ≤ 1`. -/
theorem Src_bound_ts (d : ℕ) (hd : 2 ≤ d) : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ (N k : ℕ), k + 1 < N → ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ → ℓC ≤ ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 k ℓC C → TInv C →
    ∀ V : Fam d L N, InF k V → (∀ b, ε (V b : Alg d L N) = 0) →
    ∀ v : ℝ, 0 ≤ v → v ≤ 1 → Fnorm k ℓ V ≤ ENNReal.ofReal v →
      Fnorm (k + 1) ℓ' (SrcL k C (EthEL C) V V) ≤ ENNReal.ofReal (C₂ * v ^ 2) := by
  classical
  obtain ⟨Cl, hCl0, hloc⟩ := exists_Loc2sXY_bound d (by omega)
  obtain ⟨Cc, hCc0, L₁, hcon⟩ := loc2s_contract d hd
  obtain ⟨cc, hcc⟩ := card_small_containing d
  refine ⟨max (max (2 ^ (d + 3) + 8 * d + 1) ⌈pauliL0 d⌉₊) L₁, fun L _ hL => ?_⟩
  have hL8 : 2 ^ (d + 3) + 8 * d < L :=
    lt_of_lt_of_le (Nat.lt_succ_self _) ((le_max_left _ _).trans ((le_max_left _ _).trans hL))
  have hLp : pauliL0 d ≤ L := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right _ _).trans ((le_max_left _ _).trans hL))
  have hL₁ : L₁ ≤ L := (le_max_right _ _).trans hL
  have hQ := one_le_Q1 (by omega : 1 ≤ d)
  have hN0 : 0 ≤ cNear d L := Nat.cast_nonneg _
  refine ⟨(1 + Cl) * ((L : ℝ) ^ d * (cNear d L * Q1 d ^ 2)), by positivity, ?_⟩
  intro N k hkN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum hCℓ C hC hT V hV hV0 v hv0 hv1 hVv
  have hvb : ∀ b ∈ blockIdx (L := L) (N := N) k, Tj d (L : ℝ) k ℓ (V b : Alg d L N) ≤
      ENNReal.ofReal v := fun b hb => (Tj_le_Fnorm V hb).trans hVv
  have hT0 : Tj d (L : ℝ) k ℓ (0 : Alg d L N) = 0 := Tj_zero _ _ _
  have hwb : ∀ b ∈ blockIdx (L := L) (N := N) k, Tj d (L : ℝ) k ℓ ((0 : Fam d L N) b : Alg d L N) ≤
      ENNReal.ofReal 0 := fun b _ => by simp [hT0]
  have hK0 : InK2 k (0 : Act d L N) :=
    { loc := fun _ _ => zero_mem _, sym := fun _ _ => (isSym_iff_mem_SymS _).2 (zero_mem _) }
  have H : BH k ℓ ℓ' ℓC C V 0 (0 : Act d L N) 1 1 Cl (cc + 1) :=
    { hd := by omega, hLp := hLp, hL8 := hL8, hjN := hkN, hℓ := hℓ, hℓ' := hℓ', hℓC := hℓC, hsum := hsum, hC := hC, hV := hV,
      hW := inF_zero k, hV0 := hV0, hK := hK0, hA := le_rfl, hr := zero_le_one, hr1 := le_rfl
      hVr := fun b hb => (hvb b hb).trans (ENNReal.ofReal_le_ofReal hv1)
      hWr := fun b hb => by simp [hT0]
      hKr := by rw [Knorm_zero]; exact zero_le
      hCl := hCl0
      hloc := fun k' hk ℓ₀ hℓ₀ X Y hX hYX G hG => hloc L hL8 N k' hk X Y hX hYX G hG ℓ₀ hℓ₀
      hcS := by linarith [Nat.cast_nonneg (α := ℝ) cc]
      hcount := fun b hb => by
        have h1 : ((smallSets (d := d) (L := L) (N := N) k).filter
            (fun X => blockSet k b ⊆ X)).card ≤ cc := by convert hcc L N k b hb
        have h2 := Nat.cast_le (α := ℝ) |>.2 h1
        push_cast; linarith }
  have hcon' : ∀ ℓ₀ ℓ₁ : ℝ, 0 < ℓ₀ → 0 < ℓ₁ → ℓ₁ ≤ 2 * ℓ₀ → ∀ X : Finset (Lam d L N), IsSmall k X →
      ∀ G ∈ NX (nbhd k X : Set (Lam d L N)), IsSym G →
        Tj d (L : ℝ) (k + 1) ℓ₁ (G - Loc2sX X G) ≤
          ENNReal.ofReal (Cc / (L : ℝ) ^ 3) * Tj d (L : ℝ) k ℓ₀ G :=
    fun ℓ₀ ℓ₁ h0 h1 h2 X hX G hG hs => hcon L hL8 hL₁ N k (by omega) ℓ₀ ℓ₁ h0 h1 h2 X hX G hG hs
  have hWc : FamCov k (0 : Fam d L N) := fun b _ => by simp
  refine iSup₂_le fun c' hc' => ?_
  rw [SrcL_eq_Wp]
  refine (H.sumWp_le hv0 le_rfl hvb hwb hCc0 hcon' hCℓ hT hWc hc').trans
    (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  ring

/-- **The source bound**: `‖Src_k(V, V)‖_{k+1} ≤ C(L) v²` for `‖V‖_k ≤ v ≤ 1`. -/
theorem Src_bound (d : ℕ) (hd : 2 ≤ d) : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ (N k : ℕ), k + 1 < N → ∀ ℓ : ℝ, 0 < ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 k ℓ C → TInv C →
    ∀ V : Fam d L N, InF k V → (∀ b, ε (V b : Alg d L N) = 0) →
    ∀ v : ℝ, 0 ≤ v → v ≤ 1 → Fnorm k ℓ V ≤ ENNReal.ofReal v →
      Fnorm (k + 1) ℓ (SrcL k C (EthEL C) V V) ≤ ENNReal.ofReal (C₂ * v ^ 2) := by
  obtain ⟨L₀, h⟩ := Src_bound_ts d hd
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨C₂, hC₂, h'⟩ := h L hL
  exact ⟨C₂, hC₂, fun N k hk ℓ hℓ C hC => h' N k hk ℓ ℓ ℓ hℓ hℓ hℓ (by linarith) le_rfl C hC⟩

/-- **The iterated transport contracts**: `‖T_{k+1+n,k} F‖ ≤ (C₀ L^{d-3})^n ‖F‖`. -/
theorem TrIt_bound (d : ℕ) (hd : 2 ≤ d) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ L₀ : ℕ,
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∀ (N : ℕ) (D : FlowSeq d L N) (k : ℕ) (ℓ : ℝ), 0 < ℓ →
    (∀ i, k + 1 ≤ i → i + 1 < N → GoodCov2 i ℓ (D.C i) ∧ TInv (D.C i) ∧ ‖D.s i‖ ≤ 1) →
    ∀ F : Fam d L N, InF (k + 1) F → FamCovG (k + 1) F →
    ∀ w : ℝ, 0 ≤ w → Fnorm (k + 1) ℓ F ≤ ENNReal.ofReal w →
    ∀ n, k + 1 + n < N → InF (k + 1 + n) (D.TrIt k n F) ∧
      (k + 1 + n + 1 < N → FamCovG (k + 1 + n) (D.TrIt k n F)) ∧
      Fnorm (k + 1 + n) ℓ (D.TrIt k n F) ≤
        ENNReal.ofReal ((C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3)) ^ n * w) := by
  obtain ⟨C₀, hC₀, L₀, h⟩ := TrL_contract' d hd
  refine ⟨C₀, hC₀, max L₀ (2 ^ (d + 3)), ?_⟩
  intro L _ hL N D k ℓ hℓ hD F hF hFc w hw0 hFw n
  have hL₀ : L₀ ≤ L := (le_max_left _ _).trans hL
  have hL8 : 2 ^ (d + 3) ≤ L := (le_max_right _ _).trans hL
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  induction n with
  | zero =>
    intro _
    exact ⟨hF, fun _ => hFc, by simpa [FlowSeq.TrIt] using hFw⟩
  | succ n ih =>
    intro hn
    obtain ⟨h1, h2, h3⟩ := ih (by omega)
    have hi : k + 1 + n + 1 < N := by omega
    obtain ⟨hC, hT, hs⟩ := hD (k + 1 + n) (by omega) hi
    have hcov := h2 hi
    rw [D.TrIt_succ, ← add_assoc, LinearMap.comp_apply]
    refine ⟨inF_TrL (i := k + 1 + n) (C := D.C (k + 1 + n)) (by omega) hL8 hi hC _ h1,
      fun hi2 => TrL_cov (by omega) hL8 hi2 hC hT _ h1 hcov, ?_⟩
    refine (h L hL₀ N (k + 1 + n) hi ℓ hℓ (D.C (k + 1 + n)) hC hT _ h1 hcov (D.s (k + 1 + n)) hs
      _ (by positivity) h3).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    ring

/-! ### Coefficient bounds -/

/-- The coefficient vector of `Loc_{X,Y} H` on a patch `Y`. -/
theorem cvec4_Loc {X Y : Finset (Lam d L N)} (hY : Patch Y) (hne : Y.Nonempty) (i₀ : Fin d)
    (H : Alg d L N) :
    cvec4 Y i₀ (Loc2sXY X Y H) = ![locCoef X H (.m2 i₀ i₀), -2 * locCoef X H (.a2 s(i₀, i₀)),
      locCoef X H .c, mu4 (base X) i₀ i₀ H / X.card] := by
  have hY0 : (Y.card : ℂ) ≠ 0 := by exact_mod_cast hne.card_pos.ne'
  rw [Loc2sXY_eq_unif]
  funext a
  fin_cases a <;> simp [cvec4, locCoef_unif hY hne, mu4_unif hY, hY0]

/-- The coefficient vector of `Loc_{B_+,B} ∑ 𝔼θ σ F` (as `cvec4` of the polynomial on `B_+`). -/
theorem cvec4_LpartL {j : ℕ} (hL : 2 ^ (d + 3) + 8 * d < L) (hj : j < N)
    (C : Matrix (Lam d L N) (Lam d L N) ℂ) (s : ℂ) (F : Fam d L N) {b : Fin d → ℕ}
    (hb : b ∈ blockIdx (L := L) (N := N) j) (i₀ : Fin d) :
    cvec4 (blockSet (L := L) (N := N) j b) i₀ (FlowSeq.LpartL j C s b F : Alg d L N) =
      ![locCoef (Bp (L := L) (N := N) j b) (∑ b' ∈ blocks j (Bp (L := L) (N := N) j b),
          (EthE C (sigE s (F b')) : Alg d L N)) (.m2 i₀ i₀),
        -2 * locCoef (Bp (L := L) (N := N) j b) (∑ b' ∈ blocks j (Bp (L := L) (N := N) j b),
          (EthE C (sigE s (F b')) : Alg d L N)) (.a2 s(i₀, i₀)),
        locCoef (Bp (L := L) (N := N) j b) (∑ b' ∈ blocks j (Bp (L := L) (N := N) j b),
          (EthE C (sigE s (F b')) : Alg d L N)) .c,
        mu4 (base (Bp (L := L) (N := N) j b)) i₀ i₀ (∑ b' ∈ blocks j (Bp (L := L) (N := N) j b),
          (EthE C (sigE s (F b')) : Alg d L N)) / (Bp (L := L) (N := N) j b).card] := by
  have hsm := isSmall_blockSet_of_mem hb
  have hP := patch_of_small hL hj hsm
  simp only [FlowSeq.LpartL, LinearMap.coe_mk, AddHom.coe_mk, coe_Loc2E,
    AddSubmonoidClass.coe_finsetSum]
  exact cvec4_Loc hP hsm.2.1.1 i₀ _

/-- Locality and norm of `H = ∑_{B' ⊆ B_+} 𝔼θ σ F(B')`: `‖H‖_{j+1} ≤ L^d Q₁ ‖F‖_j`. -/
theorem sumEthE_bound (hd : 1 ≤ d) (hLp : pauliL0 d ≤ L) {j : ℕ} (hjN : j + 1 < N) {ℓ : ℝ}
    (hℓ : 0 < ℓ) {C : Matrix (Lam d L N) (Lam d L N) ℂ} (hC : GoodCov2 j ℓ C) {s : ℂ}
    (hs : ‖s‖ ≤ 1) {F : Fam d L N} (hF : InF j F) {w : ℝ} (hw0 : 0 ≤ w)
    (hFw : Fnorm j ℓ F ≤ ENNReal.ofReal w) {b : Fin d → ℕ}
    (hb : b ∈ blockIdx (L := L) (N := N) j) :
    (∑ b' ∈ blocks j (Bp (L := L) (N := N) j b), (EthE C (sigE s (F b')) : Alg d L N)) ∈
        NX (nbhd (j + 1) (Bp (L := L) (N := N) j b) : Set (Lam d L N)) ∧
      Tj d (L : ℝ) (j + 1) ℓ (∑ b' ∈ blocks j (Bp (L := L) (N := N) j b),
        (EthE C (sigE s (F b')) : Alg d L N)) ≤ ENNReal.ofReal ((L : ℝ) ^ d * Q1 d * w) := by
  have hQ := one_le_Q1 hd
  have hBpeq : Bp (L := L) (N := N) j b = blockSet (j + 1) (PolyAux.par L b) := clo_blockSet hb
  have hsig : ∀ b', (sig s (F b' : Alg d L N)) ∈
      NX (nbhd j (blockSet (L := L) (N := N) j b') : Set (Lam d L N)) := fun b' =>
    sig_mem_NX (hF.loc b') s
  constructor
  · refine Subalgebra.sum_mem _ fun b' hb' => ?_
    have h1 : (EthE C (sigE s (F b')) : Alg d L N) ∈ NB (L := L) (N := N) j b' :=
      EthE_mem_NB (by rw [coe_sigE]; exact hsig b')
    have h2 := NB_le_NBp j b' h1
    rw [hBpeq] at hb' ⊢
    have e := Bp_eq_of_mem hb'
    simp only [NBp, e] at h2
    exact h2
  · have hterm : ∀ b' ∈ blocks j (Bp (L := L) (N := N) j b),
        Tj d (L : ℝ) (j + 1) ℓ (EthE C (sigE s (F b')) : Alg d L N) ≤
          ENNReal.ofReal (Q1 d * w) := by
      intro b' hb'
      have hb'i := mem_blockIdx_of_mem_blocks hb'
      have h1 := EthE_block_le hd hLp (by omega : j < N) hℓ hC (F := sigE s (F b'))
        (by rw [coe_sigE]; exact hsig b')
      refine h1.trans ?_
      rw [ENNReal.ofReal_mul (by linarith)]
      refine mul_le_mul_left' ?_ _
      rw [coe_sigE]
      exact (tNorm_sig_le (by positivity) hℓ hs _).trans ((Tj_le_Fnorm F hb'i).trans hFw)
    have hcard : ((blocks j (Bp (L := L) (N := N) j b)).card : ℝ) ≤ (L : ℝ) ^ d := by
      rw [hBpeq]; exact_mod_cast nb_blockSet_succ_le j (PolyAux.par L b)
    have h := tn_sum_const (E := Dir d) (p := pPhi d) (blocks j (Bp (L := L) (N := N) j b))
      (fun b' => EthE C (sigE s (F b'))) (r := Q1 d * w) (by positivity) hterm
    rw [AddSubmonoidClass.coe_finsetSum] at h
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    calc ((blocks j (Bp (L := L) (N := N) j b)).card : ℝ) * (Q1 d * w)
        ≤ (L : ℝ) ^ d * (Q1 d * w) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by ring

/-- **The coefficient vector of `Loc_{B_+,B} ∑ 𝔼θ σ F` is bounded by `‖F‖_j`**: with `h = L^{j+1}`,
`n = L^d Q₁`, the `z`, `y` components by `K ℓ^{-2} h² n w / |B_+|`, the `ν` component by
`K ℓ^{-2} n w / |B_+|`, the `g` component by `K ℓ^{-4} h² n w / |B_+|`. -/
theorem LpartL_coef_bound (d : ℕ) (hd : 1 ≤ d) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (L : ℕ) [NeZero L],
    2 ^ (d + 3) + 8 * d < L → pauliL0 d ≤ L → ∀ (N j : ℕ), j + 1 < N → ∀ ℓ : ℝ, 0 < ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓ C → ∀ s : ℂ, ‖s‖ ≤ 1 →
    ∀ F : Fam d L N, InF j F → ∀ w : ℝ, 0 ≤ w → Fnorm j ℓ F ≤ ENNReal.ofReal w →
    ∀ b ∈ blockIdx (L := L) (N := N) j, ∀ i₀ : Fin d, ∀ a : Fin 4,
      ‖cvec4 (blockSet (L := L) (N := N) j b) i₀ (FlowSeq.LpartL j C s b F : Alg d L N) a‖ ≤
        K * (ℓ ^ 2)⁻¹ * (if a = 3 then (ℓ ^ 2)⁻¹ else 1) *
          (if a = 2 then 1 else ((L : ℝ) ^ (j + 1)) ^ 2) * ((L : ℝ) ^ d * Q1 d * w) /
          (Bp (L := L) (N := N) j b).card := by
  obtain ⟨Cc, hCc0, hCc⟩ := exists_locCoef_bound d hd
  obtain ⟨Cm, hCm0, hCm⟩ := exists_mu4_bound d
  refine ⟨2 * (Cc + Cm), by positivity, ?_⟩
  intro L _ hL hLp N j hjN ℓ hℓ C hC s hs F hF w hw0 hFw b hb i₀ a
  have hsm := isSmall_blockSet_of_mem hb
  have hBp : IsSmall (j + 1) (Bp (L := L) (N := N) j b) := isSmall_clo hsm
  have hX0 : (0 : ℝ) < (Bp (L := L) (N := N) j b).card := by exact_mod_cast hBp.2.1.1.card_pos
  have hQ := one_le_Q1 hd
  obtain ⟨hmem, hH⟩ := sumEthE_bound hd hLp hjN hℓ hC hs hF hw0 hFw hb
  set H := ∑ b' ∈ blocks j (Bp (L := L) (N := N) j b), (EthE C (sigE s (F b')) : Alg d L N)
  set n : ℝ := (L : ℝ) ^ d * Q1 d * w
  have hn0 : 0 ≤ n := by positivity
  have hTR : (Tj d (L : ℝ) (j + 1) ℓ H).toReal ≤ n := ENNReal.toReal_le_of_le_ofReal hn0 hH
  have hc : ∀ M : Mono d, ‖locCoef (Bp (L := L) (N := N) j b) H M‖ ≤
      Cc * (ℓ ^ 2)⁻¹ * ((L : ℝ) ^ (j + 1)) ^ M.deg * n / (Bp (L := L) (N := N) j b).card := by
    intro M
    refine (hCc L hL N (j + 1) hjN _ hBp H hmem ℓ hℓ M).trans
      (div_le_div_of_nonneg_right ?_ hX0.le)
    exact mul_le_mul_of_nonneg_left hTR (by positivity)
  have hK : Cc ≤ 2 * (Cc + Cm) := by linarith
  have hK' : 2 * Cc ≤ 2 * (Cc + Cm) := by linarith
  have hKm : Cm ≤ 2 * (Cc + Cm) := by linarith
  have h0 := hc (.m2 i₀ i₀)
  have h1 := hc (.a2 s(i₀, i₀))
  have h2 := hc .c
  simp only [Mono.deg, pow_zero, mul_one] at h0 h1 h2
  have h3 := hCm L hL N (j + 1) hjN _ hBp H hmem i₀ i₀ ℓ hℓ
  have hX := hX0
  rw [cvec4_LpartL hL (by omega) C s F hb i₀]
  have hA : 0 ≤ (ℓ ^ 2)⁻¹ * ((L : ℝ) ^ (j + 1)) ^ 2 * n / ((Bp (L := L) (N := N) j b).card : ℝ) := by positivity
  have hA' : 0 ≤ (ℓ ^ 2)⁻¹ * n / ((Bp (L := L) (N := N) j b).card : ℝ) := by positivity
  have hA'' : 0 ≤ (ℓ ^ 2)⁻¹ * (ℓ ^ 2)⁻¹ * ((L : ℝ) ^ (j + 1)) ^ 2 * n / ((Bp (L := L) (N := N) j b).card : ℝ) := by positivity
  have p1 : 0 ≤ Cm * ((ℓ ^ 2)⁻¹ * ((L : ℝ) ^ (j + 1)) ^ 2 * n / ((Bp (L := L) (N := N) j b).card : ℝ)) := mul_nonneg hCm0 hA
  have p2 : 0 ≤ Cm * ((ℓ ^ 2)⁻¹ * n / ((Bp (L := L) (N := N) j b).card : ℝ)) := mul_nonneg hCm0 hA'
  have p3 : 0 ≤ Cc * ((ℓ ^ 2)⁻¹ * (ℓ ^ 2)⁻¹ * ((L : ℝ) ^ (j + 1)) ^ 2 * n / ((Bp (L := L) (N := N) j b).card : ℝ)) := mul_nonneg hCc0 hA''
  have p4 : 0 ≤ Cc * ((ℓ ^ 2)⁻¹ * ((L : ℝ) ^ (j + 1)) ^ 2 * n / ((Bp (L := L) (N := N) j b).card : ℝ)) := mul_nonneg hCc0 hA
  have h3' : ‖mu4 (base (Bp (L := L) (N := N) j b)) i₀ i₀ H‖ ≤ Cm * (ℓ ^ 2)⁻¹ * (ℓ ^ 2)⁻¹ * ((L : ℝ) ^ (j + 1)) ^ 2 * n := by
    refine h3.trans ?_
    rw [show ℓ ^ 4 = ℓ ^ 2 * ℓ ^ 2 by ring, mul_inv]
    have := mul_le_mul_of_nonneg_left hTR (by positivity :
      (0 : ℝ) ≤ Cm * ((ℓ ^ 2)⁻¹ * (ℓ ^ 2)⁻¹) * ((L : ℝ) ^ (j + 1)) ^ 2)
    linarith
  have h3'' : ‖mu4 (base (Bp (L := L) (N := N) j b)) i₀ i₀ H‖ / ((Bp (L := L) (N := N) j b).card : ℝ) ≤
      Cm * ((ℓ ^ 2)⁻¹ * (ℓ ^ 2)⁻¹ * ((L : ℝ) ^ (j + 1)) ^ 2 * n / ((Bp (L := L) (N := N) j b).card : ℝ)) := by
    rw [show Cm * ((ℓ ^ 2)⁻¹ * (ℓ ^ 2)⁻¹ * ((L : ℝ) ^ (j + 1)) ^ 2 * n / ((Bp (L := L) (N := N) j b).card : ℝ)) =
      Cm * (ℓ ^ 2)⁻¹ * (ℓ ^ 2)⁻¹ * ((L : ℝ) ^ (j + 1)) ^ 2 * n / ((Bp (L := L) (N := N) j b).card : ℝ) by ring]
    exact div_le_div_of_nonneg_right h3' hX0.le
  simp only [H] at h0 h1 h2 h3''
  fin_cases a <;> simp <;> simp at h0 h1 h2 h3''
  · exact h0.trans (by gcongr)
  · calc 2 * _ ≤ 2 * (Cc * (ℓ ^ 2)⁻¹ * ((L : ℝ) ^ (j + 1)) ^ 2 * n /
            ((Bp (L := L) (N := N) j b).card : ℝ)) := by gcongr
      _ = (2 * Cc) * (ℓ ^ 2)⁻¹ * ((L : ℝ) ^ (j + 1)) ^ 2 * n /
            ((Bp (L := L) (N := N) j b).card : ℝ) := by ring
      _ ≤ _ := by gcongr
  · exact h2.trans (by gcongr)
  · refine h3''.trans ?_
    rw [show Cm * ((ℓ ^ 2)⁻¹ * (ℓ ^ 2)⁻¹ * ((L : ℝ) ^ (j + 1)) ^ 2 * n /
        ((Bp (L := L) (N := N) j b).card : ℝ)) = Cm * (ℓ ^ 2)⁻¹ * (ℓ ^ 2)⁻¹ *
        ((L : ℝ) ^ (j + 1)) ^ 2 * n / ((Bp (L := L) (N := N) j b).card : ℝ) by ring]
    gcongr

/-! ### The estimate for `β_{j,k}` -/

theorem famCovG_VfamL {k : ℕ} (hk : k ≤ N) (u : Fin 4 → ℂ) :
    FamCovG k (VfamL (d := d) (L := L) (N := N) k u) := by
  intro t ht b hb
  have hP := Flow.presBlocks_transl' hk t ht
  show Vcoup (Coup.ofVec u) (blockSet k (bmap k (AffAut.transl t) b)) =
    autAlg (Equiv.addRight t) (Vcoup (Coup.ofVec u) (blockSet k b))
  rw [← img_blockSet_bmap (IsGen.transl t) hk hP hb, ← autAlg_Vcoup (IsGen.transl t)]
  rfl

theorem famCovG_SrcL {k : ℕ} {ℓ : ℝ} {C : Matrix (Lam d L N) (Lam d L N) ℂ} (hd : 1 ≤ d)
    (hL : 2 ^ (d + 3) ≤ L) (hk2 : k + 2 < N) (hC : GoodCov2 k ℓ C) (hCt : TInv C)
    {V : Fam d L N} (hV : InF k V) (hVc : FamCovG k V) :
    FamCovG (k + 1) (SrcL k C (EthEL C) V V) := by
  have h := sumWp_cov (V := V) (W := 0) hd hL hk2 hC hCt hV (inF_zero k) hVc (famCovG_zero k)
  intro t ht c hc
  rw [SrcL_eq_Wp, SrcL_eq_Wp]
  exact h t ht c hc

namespace FlowSeq

/-- **`prop:C4b`(d)**: for `k < j`, the coefficient vector of `β_{j,k}(u, u)` is bounded by
`K u_a (C₀ L^{d-3})^{j-k-1} C₂ v²`, where `v ≥ ‖V_u‖_k` and the unit factor `u_a` is
`ℓ^{-2} h² L^d Q₁ / |B_+|` (z, y), `ℓ^{-2} L^d Q₁ / |B_+|` (ν), `ℓ^{-4} h² L^d Q₁ / |B_+|` (g),
with `h = L^{j+1}`. -/
theorem beta_bound (d : ℕ) (hd : 2 ≤ d) : ∃ C₀ K : ℝ, 0 ≤ C₀ ∧ 0 ≤ K ∧ ∃ L₀ : ℕ,
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ C₂ : ℝ, 0 ≤ C₂ ∧
    ∀ (N : ℕ) (D : FlowSeq d L N) (j k : ℕ), k < j → j + 1 < N → ∀ ℓ : ℝ, 0 < ℓ →
    (∀ i, k ≤ i → i + 1 < N → GoodCov2 i ℓ (D.C i) ∧ TInv (D.C i)) →
    (∀ i, k + 1 ≤ i → i + 1 < N → ‖D.s i‖ ≤ 1) →
    ∀ u : Fin 4 → ℂ, ∀ v : ℝ, 0 ≤ v → v ≤ 1 → Fnorm k ℓ (VfamL (d := d) (L := L) (N := N) k u) ≤
      ENNReal.ofReal v →
    ∀ b ∈ blockIdx (L := L) (N := N) j, ∀ i₀ : Fin d, ∀ a : Fin 4,
      ‖D.beta j k b i₀ u u a‖ ≤
        K * (ℓ ^ 2)⁻¹ * (if a = 3 then (ℓ ^ 2)⁻¹ else 1) *
          (if a = 2 then 1 else ((L : ℝ) ^ (j + 1)) ^ 2) *
          ((L : ℝ) ^ d * Q1 d * ((C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3)) ^ (j - 1 - k) * (C₂ * v ^ 2))) /
          (Bp (L := L) (N := N) j b).card := by
  obtain ⟨C₀, hC₀, L₁, hT⟩ := TrIt_bound d hd
  obtain ⟨L₂, hS⟩ := Src_bound d hd
  obtain ⟨K, hK, hc⟩ := LpartL_coef_bound d (by omega)
  refine ⟨C₀, K, hC₀, hK, max (max L₁ L₂) (max (2 ^ (d + 3) + 8 * d + 1) ⌈pauliL0 d⌉₊), ?_⟩
  intro L _ hL
  have hL1 : L₁ ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hL2 : L₂ ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hL8 : 2 ^ (d + 3) + 8 * d < L :=
    lt_of_lt_of_le (Nat.lt_succ_self _) ((le_max_left _ _).trans ((le_max_right _ _).trans hL))
  have hLp : pauliL0 d ≤ L := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right _ _).trans ((le_max_right _ _).trans hL))
  obtain ⟨C₂, hC₂, hS'⟩ := hS L hL2
  refine ⟨C₂, hC₂, ?_⟩
  intro N D j k hkj hjN ℓ hℓ hCov hs u v hv0 hv1 hVv b hb i₀ a
  obtain ⟨n, rfl⟩ : ∃ n, j = k + 1 + n := ⟨j - k - 1, by omega⟩
  set V := VfamL (d := d) (L := L) (N := N) k u
  have hV : InF k V := inF_VfamL (by omega) hL8 (by omega) u
  have hV0 : ∀ b, ε (V b : Alg d L N) = 0 := fun b => eps_Vcoup _ _
  have hVc : FamCovG k V := famCovG_VfamL (by omega) u
  obtain ⟨hCk, hTk⟩ := hCov k le_rfl (by omega)
  set Src := SrcL k (D.C k) (EthEL (D.C k)) V V
  have hSrc := hS' N k (by omega) ℓ hℓ (D.C k) hCk hTk V hV hV0 v hv0 hv1 hVv
  have hSrcF : InF (k + 1) Src := inF_SrcL (by omega) hL8 (by omega) hCk u
  have hSrcc : FamCovG (k + 1) Src :=
    famCovG_SrcL (by omega) (by omega) (by omega) hCk hTk hV hVc
  obtain ⟨hTF, -, hTn⟩ := hT L hL1 N D k ℓ hℓ
    (fun i hi hi' => ⟨(hCov i (by omega) hi').1, (hCov i (by omega) hi').2,
      hs i hi hi'⟩) Src hSrcF hSrcc _ (by positivity) hSrc n (by omega)
  obtain ⟨hCj, -⟩ := hCov (k + 1 + n) (by omega) hjN
  have hkj' : k ≠ k + 1 + n := by omega
  have hbeta : D.beta (k + 1 + n) k b i₀ u u = cvec4 (blockSet (L := L) (N := N) (k + 1 + n) b) i₀
      (LpartL (k + 1 + n) (D.C (k + 1 + n)) (D.s (k + 1 + n)) b (D.TrIt k n Src) : Alg d L N) := by
    unfold beta
    rw [if_neg hkj']
    simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.comp_apply]
    rw [show k + 1 + n - 1 - k = n by omega]
    rfl
  rw [hbeta, show k + 1 + n - 1 - k = n by omega]
  exact hc L hL8 hLp N (k + 1 + n) hjN ℓ hℓ _ hCj _ (hs _ (by omega) hjN) _ hTF _
    (by positivity) hTn b hb i₀ a

end FlowSeq

/-! ### The product remainder -/

/-- **The product remainder of `Wnext2`**: on each `(j+1)`-block,
`‖∏ (1 + 𝒲'(B)) - 1 - ∑ 𝒲'(B)‖_{j+1} ≤ C₃ (v² + w)²`. -/
theorem prodRem_bound_ts (d : ℕ) (hd : 1 ≤ d) : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ C₃ : ℝ, 0 ≤ C₃ ∧ ∀ (N j : ℕ), j + 1 < N → ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓC C →
    ∀ V W : Fam d L N, InF j V → InF j W → (∀ b, ε (V b : Alg d L N) = 0) →
    ∀ v w : ℝ, 0 ≤ v → 0 ≤ w → v ≤ 1 → w ≤ 1 →
    Fnorm j ℓ V ≤ ENNReal.ofReal v → Fnorm j ℓ W ≤ ENNReal.ofReal w →
    ∀ c ∈ blockIdx (L := L) (N := N) (j + 1),
      Tj d (L : ℝ) (j + 1) ℓ' ((∏ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c),
        (1 + Wp j C V W b) - 1 - ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c),
          Wp j C V W b : EvR (Lam d L N)) : Alg d L N) ≤
        ENNReal.ofReal (C₃ * (v ^ 2 + w) ^ 2) := by
  classical
  obtain ⟨Cl, hCl0, hloc⟩ := exists_Loc2sXY_bound d hd
  obtain ⟨cc, hcc⟩ := card_small_containing d
  refine ⟨max (2 ^ (d + 3) + 8 * d + 1) ⌈pauliL0 d⌉₊, fun L _ hL => ?_⟩
  have hL8 : 2 ^ (d + 3) + 8 * d < L :=
    lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _ |>.trans hL)
  have hLp : pauliL0 d ≤ L := (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hL)
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hQ := one_le_Q1 hd
  have hN0 : 0 ≤ cNear d L := Nat.cast_nonneg _
  set n : ℝ := (L : ℝ) ^ d with hn
  set Cσ : ℝ := (1 + Cl * n) * (cNear d L * Q1 d ^ 2 + Q1 d) with hCσ
  have hCσ0 : 0 ≤ Cσ := by positivity
  refine ⟨n ^ 2 * Cσ ^ 2 * (1 + Cσ) ^ (L ^ d), by positivity, ?_⟩
  intro N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC V W hV hW hV0 v w hv0 hw0 hv1 hw1 hVv hWw c' hc'
  have hvb : ∀ b ∈ blockIdx (L := L) (N := N) j, Tj d (L : ℝ) j ℓ (V b : Alg d L N) ≤
      ENNReal.ofReal v := fun b hb => (Tj_le_Fnorm V hb).trans hVv
  have hwb : ∀ b ∈ blockIdx (L := L) (N := N) j, Tj d (L : ℝ) j ℓ (W b : Alg d L N) ≤
      ENNReal.ofReal w := fun b hb => (Tj_le_Fnorm W hb).trans hWw
  have hK0 : InK2 j (0 : Act d L N) :=
    { loc := fun _ _ => zero_mem _, sym := fun _ _ => (isSym_iff_mem_SymS _).2 (zero_mem _) }
  have H : BH j ℓ ℓ' ℓC C V W (0 : Act d L N) 1 1 Cl (cc + 1) :=
    { hd := hd, hLp := hLp, hL8 := hL8, hjN := hjN, hℓ := hℓ, hℓ' := hℓ', hℓC := hℓC, hsum := hsum, hC := hC, hV := hV,
      hW := hW, hV0 := hV0, hK := hK0, hA := le_rfl, hr := zero_le_one, hr1 := le_rfl
      hVr := fun b hb => (hvb b hb).trans (ENNReal.ofReal_le_ofReal hv1)
      hWr := fun b hb => (hwb b hb).trans (ENNReal.ofReal_le_ofReal hw1)
      hKr := by rw [Knorm_zero]; exact zero_le
      hCl := hCl0
      hloc := fun k hk ℓ₀ hℓ₀ X Y hX hYX G hG => hloc L hL8 N k hk X Y hX hYX G hG ℓ₀ hℓ₀
      hcS := by linarith [Nat.cast_nonneg (α := ℝ) cc]
      hcount := fun b hb => by
        have h1 : ((smallSets (d := d) (L := L) (N := N) j).filter
            (fun X => blockSet j b ⊆ X)).card ≤ cc := by convert hcc L N j b hb
        have h2 := Nat.cast_le (α := ℝ) |>.2 h1
        push_cast; linarith }
  have hsig : BH.sig d L v w ≤ (cNear d L * Q1 d ^ 2 + Q1 d) * (v ^ 2 + w) := by
    unfold BH.sig
    have h1 : 0 ≤ cNear d L * Q1 d ^ 2 * w := mul_nonneg (mul_nonneg hN0 (sq_nonneg _)) hw0
    have h2 : 0 ≤ Q1 d * v ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    nlinarith
  have hsig1 : BH.sig d L v w ≤ cNear d L * Q1 d ^ 2 + Q1 d := by
    unfold BH.sig
    have : v ^ 2 ≤ 1 := by nlinarith
    have h1 : cNear d L * Q1 d ^ 2 * v ^ 2 ≤ cNear d L * Q1 d ^ 2 :=
      mul_le_of_le_one_right (mul_nonneg hN0 (sq_nonneg _)) this
    have h2 : Q1 d * w ≤ Q1 d := mul_le_of_le_one_right (by linarith) hw1
    linarith
  set s := blocks j (blockSet (L := L) (N := N) (j + 1) c')
  set δ := (1 + Cl * (L : ℝ) ^ d) * BH.sig d L v w with hδdef
  have hδ0 : 0 ≤ δ := mul_nonneg (by positivity) (BH.sig_nonneg (L := L) hd v w hw0)
  have hR := tn_prod_sub_one_sub (E := Dir d) (p := pPhi d) H.hh' hℓ' s (Wp j C V W) hδ0
    (fun b hb => H.Wp_le' hv0 hw0 hv1 hvb hwb (mem_blockIdx_of_mem_blocks hb))
  refine hR.trans (ENNReal.ofReal_le_ofReal ?_)
  have hsn : s.card ≤ L ^ d := nb_blockSet_succ_le j c'
  have hs : (s.card : ℝ) ≤ n := by rw [hn]; exact_mod_cast hsn
  have hδ : δ ≤ Cσ * (v ^ 2 + w) := by
    rw [hδdef, hCσ, mul_assoc]; exact mul_le_mul_of_nonneg_left hsig (by positivity)
  have hδ1 : δ ≤ Cσ := by
    rw [hδdef, hCσ]; exact mul_le_mul_of_nonneg_left hsig1 (by positivity)
  have hP1 := pow_sub_one_sub_le hδ0 s.card
  have hP2 : (1 + δ) ^ s.card ≤ (1 + Cσ) ^ (L ^ d) :=
    (pow_le_pow_left₀ (by linarith) (by linarith) _).trans
      (pow_le_pow_right₀ (by linarith) hsn)
  refine hP1.trans ?_
  have h1 : (s.card : ℝ) ^ 2 ≤ n ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hs 2
  have h2 : δ ^ 2 ≤ Cσ ^ 2 * (v ^ 2 + w) ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hδ0 hδ 2
  calc (s.card : ℝ) ^ 2 * δ ^ 2 * (1 + δ) ^ s.card
      ≤ n ^ 2 * (Cσ ^ 2 * (v ^ 2 + w) ^ 2) * (1 + Cσ) ^ (L ^ d) := by gcongr
    _ = _ := by ring

/-- **The product remainder of `Wnext2`**: on each `(j+1)`-block,
`‖∏ (1 + 𝒲'(B)) - 1 - ∑ 𝒲'(B)‖_{j+1} ≤ C₃ (v² + w)²`. -/
theorem prodRem_bound (d : ℕ) (hd : 1 ≤ d) : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ C₃ : ℝ, 0 ≤ C₃ ∧ ∀ (N j : ℕ), j + 1 < N → ∀ ℓ : ℝ, 0 < ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓ C →
    ∀ V W : Fam d L N, InF j V → InF j W → (∀ b, ε (V b : Alg d L N) = 0) →
    ∀ v w : ℝ, 0 ≤ v → 0 ≤ w → v ≤ 1 → w ≤ 1 →
    Fnorm j ℓ V ≤ ENNReal.ofReal v → Fnorm j ℓ W ≤ ENNReal.ofReal w →
    ∀ c ∈ blockIdx (L := L) (N := N) (j + 1),
      Tj d (L : ℝ) (j + 1) ℓ ((∏ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c),
        (1 + Wp j C V W b) - 1 - ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c),
          Wp j C V W b : EvR (Lam d L N)) : Alg d L N) ≤
        ENNReal.ofReal (C₃ * (v ^ 2 + w) ^ 2) := by
  obtain ⟨L₀, h⟩ := prodRem_bound_ts d hd
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨C₃, hC₃, h'⟩ := h L hL
  exact ⟨C₃, hC₃, fun N j hj ℓ hℓ C hC => h' N j hj ℓ ℓ ℓ hℓ hℓ hℓ (by linarith) C hC⟩

/-! ### The recursion -/

theorem Fnorm_add_le {j : ℕ} {ℓ : ℝ} (F G : Fam d L N) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hF : Fnorm j ℓ F ≤ ENNReal.ofReal s) (hG : Fnorm j ℓ G ≤ ENNReal.ofReal t) :
    Fnorm j ℓ (F + G) ≤ ENNReal.ofReal (s + t) :=
  iSup₂_le fun b hb => tn_addE hs ht ((Tj_le_Fnorm F hb).trans hF) ((Tj_le_Fnorm G hb).trans hG)

theorem inF_sumWp {j : ℕ} {ℓ : ℝ} {C : Matrix (Lam d L N) (Lam d L N) ℂ} {V W : Fam d L N}
    (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hjN : j + 1 < N) (hC : GoodCov2 j ℓ C)
    (hV : InF j V) (hW : InF j W) :
    InF (j + 1) (fun c => ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c), Wp j C V W b) := by
  constructor
  · intro c
    rw [AddSubmonoidClass.coe_finsetSum]
    refine Subalgebra.sum_mem _ fun b hb => ?_
    have h := Wp_mem hd hL hjN hC hV hW (mem_blockIdx_of_mem_blocks hb)
    rwa [NBp, Bp_eq_of_mem hb] at h
  · intro c
    rw [AddSubmonoidClass.coe_finsetSum, isSym_iff_mem_SymS]
    exact Subalgebra.sum_mem _ fun b _ => Wp_sym (C := C) hV hW b

namespace FlowSeq

variable (D : FlowSeq d L N)

/-- The actual remainder along the flow: `𝒲_{k+1} = Wnext2 k (C k) V_k (σ_{s_k} 𝒲_k)`. -/
def Wact : ℕ → Fam d L N
  | 0 => 0
  | k + 1 => Wnext2 k (D.C k) (D.Vin k) (fun b => sigE (D.s k) (Wact k b))

/-- The product remainder at step `k`. -/
def Rem (k : ℕ) : Fam d L N := fun c =>
  ∏ b ∈ blocks k (blockSet (L := L) (N := N) (k + 1) c),
    (1 + Wp k (D.C k) (D.Vin k) (fun b' => sigE (D.s k) (D.Wact k b')) b) - 1 -
    ∑ b ∈ blocks k (blockSet (L := L) (N := N) (k + 1) c),
      Wp k (D.C k) (D.Vin k) (fun b' => sigE (D.s k) (D.Wact k b')) b

/-- **`𝒲_{k+1} - 𝒲^lin_{k+1} = R_k + T_k (𝒲_k - 𝒲^lin_k)`.** -/
theorem Wact_sub_Wlin_succ (k : ℕ) :
    D.Wact (k + 1) - D.Wlin (k + 1) =
      D.Rem k + TrL k (D.C k) (D.s k) (D.Wact k - D.Wlin k) := by
  funext c
  simp only [Wact, Wlin, Rem, Wnext2, TrL, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply,
    Pi.sub_apply]
  have hW : ∀ A B : Fam d L N, ∀ b, Wp k (D.C k) (D.Vin k) (fun b' => sigE (D.s k) (A b')) b -
      Wp k (D.C k) (D.Vin k) (fun b' => sigE (D.s k) (B b')) b =
      EthE (D.C k) (sigE (D.s k) ((A - B) b)) - Loc2E (Bp (L := L) (N := N) k b) (blockSet k b)
        (∑ b' ∈ blocks k (Bp (L := L) (N := N) k b), EthE (D.C k) (sigE (D.s k) ((A - B) b'))) := by
    intro A B b
    rw [Wp_split, Wp_split (W := fun b' => sigE (D.s k) (B b'))]
    simp only [Pi.sub_apply, map_sub, EthE_sub, sum_sub_distrib, Loc2E_sub]
    abel
  have hW' := fun b => hW (D.Wact k) (D.Wlin k) b
  simp only [Pi.sub_apply] at hW'
  rw [← sum_congr rfl fun b _ => hW' b, sum_sub_distrib]
  abel

theorem famCovG_add {j : ℕ} {F G : Fam d L N} (hF : FamCovG j F) (hG : FamCovG j G) :
    FamCovG j (F + G) := by
  intro t ht b hb; simp [hF t ht b hb, hG t ht b hb]

theorem famCovG_sub {j : ℕ} {F G : Fam d L N} (hF : FamCovG j F) (hG : FamCovG j G) :
    FamCovG j (F - G) := by
  intro t ht b hb; simp [hF t ht b hb, hG t ht b hb]

theorem eps_Vin (k : ℕ) (b : Fin d → ℕ) : ε (D.Vin k b : Alg d L N) = 0 := by
  rw [Vin, coe_VfamL]; exact eps_Vcoup _ _

/-- Locality and covariance along the flow, for `𝒲` and `𝒲^lin`. -/
theorem flow_props (hd : 1 ≤ d) (hL : 2 ^ (d + 3) + 8 * d < L) {ℓ : ℝ} {M : ℕ} (hMN : M < N)
    (hC : ∀ k < M, GoodCov2 k ℓ (D.C k) ∧ TInv (D.C k)) :
    ∀ k ≤ M, InF k (D.Wact k) ∧ InF k (D.Wlin k) ∧
      (k + 1 < N → FamCovG k (D.Wact k) ∧ FamCovG k (D.Wlin k)) := by
  have hL' : 2 ^ (d + 3) ≤ L := by omega
  intro k
  induction k with
  | zero => intro _; exact ⟨inF_zero 0, inF_zero 0, fun _ => ⟨famCovG_zero 0, famCovG_zero 0⟩⟩
  | succ k ih =>
    intro hk
    obtain ⟨hA, hB, hcov⟩ := ih (by omega)
    obtain ⟨hGk, hTk⟩ := hC k (by omega)
    have hV := inF_VfamL (L := L) (N := N) hd hL (show k < N by omega) (D.κ k).toVec
    have hVc := famCovG_VfamL (d := d) (L := L) (N := N) (show k ≤ N by omega) (D.κ k).toVec
    obtain ⟨hAc, hBc⟩ := hcov (by omega)
    refine ⟨Wnext2_inF hd hL' (by omega) hGk hV (inF_sig hA _), ?_, fun h2 => ⟨?_, ?_⟩⟩
    · rw [Wlin_succ]
      exact inF_add (inF_SrcL hd hL (by omega) hGk _) (inF_TrL hd hL' (by omega) hGk _ hB)
    · exact Wnext2_cov hd hL' h2 hGk hTk hV (inF_sig hA _) hVc (famCovG_sig hAc _)
    · rw [Wlin_succ]
      exact famCovG_add (famCovG_SrcL hd hL' h2 hGk hTk hV hVc) (TrL_cov hd hL' h2 hGk hTk _ hB hBc)

end FlowSeq

/-- **C4′(d), product remainder**: `‖𝒲_k - 𝒲^lin_k‖_k ≤ 2ρ C₃ (v_k² + w_k)²` along the flow,
provided `C₀ L^{d-3} ρ ≤ ½` and `(v_k² + w_k)²` varies by at most a factor `ρ` per step. -/
theorem Wact_sub_Wlin_bound (d : ℕ) (hd : 2 ≤ d) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ L₀ : ℕ,
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ C₃ : ℝ, 0 ≤ C₃ ∧
    ∀ (N : ℕ) (D : FlowSeq d L N) (ℓ : ℝ), 0 < ℓ → ∀ M, M < N →
    (∀ k < M, GoodCov2 k ℓ (D.C k) ∧ TInv (D.C k) ∧ ‖D.s k‖ ≤ 1) →
    ∀ v w : ℕ → ℝ, (∀ k < M, 0 ≤ v k ∧ v k ≤ 1 ∧ 0 ≤ w k ∧ w k ≤ 1 ∧
      Fnorm k ℓ (D.Vin k) ≤ ENNReal.ofReal (v k) ∧ Fnorm k ℓ (D.Wact k) ≤ ENNReal.ofReal (w k)) →
    ∀ ρ : ℝ, 0 ≤ ρ → C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3) * ρ ≤ 1 / 2 →
    (∀ k < M, (v k ^ 2 + w k) ^ 2 ≤ ρ * (v (k + 1) ^ 2 + w (k + 1)) ^ 2) →
    ∀ k ≤ M, Fnorm k ℓ (D.Wact k - D.Wlin k) ≤
      ENNReal.ofReal (2 * ρ * (C₃ * (v k ^ 2 + w k) ^ 2)) := by
  obtain ⟨C₀, hC₀, L₁, hT⟩ := TrL_contract' d hd
  obtain ⟨L₂, hR⟩ := prodRem_bound d (by omega)
  refine ⟨C₀, hC₀, max (max L₁ L₂) (2 ^ (d + 3) + 8 * d + 1), fun L _ hL => ?_⟩
  have hL1 : L₁ ≤ L := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hL)
  have hL2 : L₂ ≤ L := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hL)
  have hL3 : 2 ^ (d + 3) + 8 * d < L := lt_of_lt_of_le (Nat.lt_succ_self _) (le_trans (le_max_right _ _) hL)
  obtain ⟨C₃, hC₃, hR⟩ := hR L hL2
  refine ⟨C₃, hC₃, fun N D ℓ hℓ M hMN hC v w hvw ρ hρ hθρ hslow => ?_⟩
  have hP := D.flow_props (by omega) hL3 hMN (fun k hk => ⟨(hC k hk).1, (hC k hk).2.1⟩)
  set θ := C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3) with hθ
  have hθ0 : 0 ≤ θ := mul_nonneg hC₀ (by positivity)
  intro k
  induction k with
  | zero =>
    intro _
    simp only [FlowSeq.Wact, FlowSeq.Wlin, sub_self]
    refine le_trans (iSup₂_le fun b _ => ?_) bot_le
    have := tNorm_smul (E := Dir d) (p := pPhi d) (h := (L : ℝ) ^ 0) (ℓ := ℓ) (0 : ℂ) (0 : Alg d L N)
    simpa [Tj] using this
  | succ k ih =>
    intro hk
    have hkM : k < M := by omega
    obtain ⟨hGk, hTk, hsk⟩ := hC k hkM
    obtain ⟨hv0, hv1, hw0, hw1, hVn, hWn⟩ := hvw k hkM
    obtain ⟨hA, hB, hcov⟩ := hP k (by omega)
    obtain ⟨hAc, hBc⟩ := hcov (by omega)
    have hak : 0 ≤ C₃ * (v k ^ 2 + w k) ^ 2 := mul_nonneg hC₃ (sq_nonneg _)
    have hX : 0 ≤ 2 * ρ * (C₃ * (v k ^ 2 + w k) ^ 2) := by positivity
    have h1 : Fnorm (k + 1) ℓ (D.Rem k) ≤ ENNReal.ofReal (C₃ * (v k ^ 2 + w k) ^ 2) :=
      iSup₂_le fun c hc => hR N k (by omega) ℓ hℓ (D.C k) hGk (D.Vin k) _
        (inF_VfamL (by omega) hL3 (by omega) _) (inF_sig hA _) (D.eps_Vin k) (v k) (w k) hv0 hw0 hv1
        hw1 hVn ((Fnorm_sig_le hℓ hsk _).trans hWn) c hc
    have h2 := hT L hL1 N k (by omega) ℓ hℓ (D.C k) hGk hTk _ (inF_sub hA hB)
      (FlowSeq.famCovG_sub hAc hBc) (D.s k) hsk _ hX (ih (by omega))
    rw [D.Wact_sub_Wlin_succ k]
    refine (Fnorm_add_le _ _ hak (by positivity) h1 h2).trans (ENNReal.ofReal_le_ofReal ?_)
    have h3 := hslow k hkM
    have h4 : θ * ρ ≤ 1 / 2 := hθρ
    have h5 : θ * (2 * ρ * (C₃ * (v k ^ 2 + w k) ^ 2)) ≤ C₃ * (v k ^ 2 + w k) ^ 2 := by
      nlinarith
    have h6 : C₃ * (v k ^ 2 + w k) ^ 2 ≤ ρ * (C₃ * (v (k + 1) ^ 2 + w (k + 1)) ^ 2) := by
      nlinarith
    nlinarith

/-- **C4′(d), coefficient form**: the relevant coefficients of
`Loc S_j(𝒲_j) - Loc S_j(𝒲^lin_j)` (i.e. `κ_S - κ_S^lin`) are bounded by the coefficient
bound of `LpartL` applied with `w = 2ρ C₃ (v_j² + w_j)²`. -/
theorem kappaS_sub_lin_bound (d : ℕ) (hd : 2 ≤ d) : ∃ C₀ K : ℝ, 0 ≤ C₀ ∧ 0 ≤ K ∧ ∃ L₀ : ℕ,
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ C₃ : ℝ, 0 ≤ C₃ ∧
    ∀ (N : ℕ) (D : FlowSeq d L N) (ℓ : ℝ), 0 < ℓ → ∀ M, M + 1 < N →
    (∀ k ≤ M, GoodCov2 k ℓ (D.C k) ∧ TInv (D.C k) ∧ ‖D.s k‖ ≤ 1) →
    ∀ v w : ℕ → ℝ, (∀ k < M, 0 ≤ v k ∧ v k ≤ 1 ∧ 0 ≤ w k ∧ w k ≤ 1 ∧
      Fnorm k ℓ (D.Vin k) ≤ ENNReal.ofReal (v k) ∧ Fnorm k ℓ (D.Wact k) ≤ ENNReal.ofReal (w k)) →
    ∀ ρ : ℝ, 0 ≤ ρ → C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3) * ρ ≤ 1 / 2 →
    (∀ k < M, (v k ^ 2 + w k) ^ 2 ≤ ρ * (v (k + 1) ^ 2 + w (k + 1)) ^ 2) →
    ∀ b ∈ blockIdx (L := L) (N := N) M, ∀ i₀ : Fin d, ∀ a : Fin 4,
      ‖cvec4 (blockSet (L := L) (N := N) M b) i₀
          ((LS M (D.C M) (D.Vin M) (fun b' => sigE (D.s M) (D.Wact M b')) b -
            LS M (D.C M) (D.Vin M) (fun b' => sigE (D.s M) (D.Wlin M b')) b : EvR (Lam d L N)) :
            Alg d L N) a‖ ≤
        K * (ℓ ^ 2)⁻¹ * (if a = 3 then (ℓ ^ 2)⁻¹ else 1) *
          (if a = 2 then 1 else ((L : ℝ) ^ (M + 1)) ^ 2) *
          ((L : ℝ) ^ d * Q1 d * (2 * ρ * (C₃ * (v M ^ 2 + w M) ^ 2))) /
          (Bp (L := L) (N := N) M b).card := by
  obtain ⟨C₀, hC₀, L₁, hW⟩ := Wact_sub_Wlin_bound d hd
  obtain ⟨K, hK, hc⟩ := LpartL_coef_bound d (by omega)
  refine ⟨C₀, K, hC₀, hK, max L₁ (max (2 ^ (d + 3) + 8 * d + 1) ⌈pauliL0 d⌉₊), fun L _ hL => ?_⟩
  have hL1 : L₁ ≤ L := (le_max_left _ _).trans hL
  have hL3 : 2 ^ (d + 3) + 8 * d < L :=
    lt_of_lt_of_le (Nat.lt_succ_self _) ((le_max_left _ _).trans ((le_max_right _ _).trans hL))
  have hLp : pauliL0 d ≤ L := (Nat.le_ceil _).trans (by
    exact_mod_cast (le_max_right _ _).trans ((le_max_right _ _).trans hL))
  obtain ⟨C₃, hC₃, hW⟩ := hW L hL1
  refine ⟨C₃, hC₃, fun N D ℓ hℓ M hMN hC v w hvw ρ hρ hθρ hslow b hb i₀ a => ?_⟩
  have hb' := hW N D ℓ hℓ M (by omega) (fun k hk => hC k hk.le) v w hvw ρ hρ hθρ hslow M le_rfl
  obtain ⟨hA, hB, hcov⟩ := D.flow_props (by omega) hL3 (M := M) (by omega)
    (fun k hk => ⟨(hC k hk.le).1, (hC k hk.le).2.1⟩) M le_rfl
  rw [FlowSeq.LS_sub_lin]
  exact hc L hL3 hLp N M hMN ℓ hℓ (D.C M) (hC M le_rfl).1 (D.s M) (hC M le_rfl).2.2 _
    (inF_sub hA hB) _ (by positivity) hb' b hb i₀ a

end

end Step2
