import Step2.Last.LastNSecond

/-!
# The last step `j = N - 1`: the estimates

For the map of `Step2.Last.LastNDefs` at `j + 1 = N`, with `‖V‖_j ≤ g`, `‖𝒲‖_j ≤ g²`, `‖K‖_j ≤ ε₀`,
input field scale `ℓ`, output field scale `ℓ'` and covariance field scale `ℓ_C` with
`ℓ' + ℓ_C ≤ 2ℓ`, and **no range condition on `C`**:

* `lastK_ts`: `‖K_N(Λ)‖_{T_N(ℓ')} ≤ C₁(L, A) (g³ + ‖K‖_j)`. The second-order part `K^{(2)}(Λ)`
  vanishes at scale `N` (`K2_last`), and the part linear in `K` is bounded by the crude bound and
  the Schwarz lemma; there is no contraction (the factor `L^d` of the old `Step.EstSmall`, here
  absorbed in `C₁`).
* `Sb_le_vw`: `‖𝒲_N(B)‖ = ‖S(B)‖ ≤ L^d Q₁² v² + Q₁ w`;
* `VpN_le_v`, `upN_le_v`: `‖V_N(B)‖ ≤ 2 Q₁ v`, `|u_N(B)| ≤ Q₁ v`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

namespace LastN

/-! ### The coordinates -/

section Coord

variable (hd : 1 ≤ d) (hLp : pauliL0 d ≤ L) {j : ℕ} (hjN : j + 1 = N) {ℓ ℓ' ℓC : ℝ}
  (hℓ' : 0 < ℓ') (hℓC : 0 < ℓC) (hsum : ℓ' + ℓC ≤ 2 * ℓ)
  {C : Matrix (Lam d L N) (Lam d L N) ℂ} (hC : GoodCov2 j ℓC C) {V W : Fam d L N}
  (hV : InF j V) (hW : InF j W) {v w : ℝ} (hv : 0 ≤ v) (hw : 0 ≤ w)
  (hVv : Fnorm j ℓ V ≤ ENNReal.ofReal v) (hWw : Fnorm j ℓ W ≤ ENNReal.ofReal w)
include hd hLp hjN hℓ' hℓC hsum hC hV hv hVv

theorem Vpr_le_v {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    Tj d (L : ℝ) (j + 1) ℓ' (Vpr C V b : Alg d L N) ≤ ENNReal.ofReal (Q1 d * v) := by
  have hj : j < N := by omega
  have hVb : Tj d (L : ℝ) j ℓ (V b : Alg d L N) ≤ ENNReal.ofReal v :=
    (le_iSup₂ (f := fun b (_ : b ∈ blockIdx (L := L) (N := N) j) =>
      Tj d (L : ℝ) j ℓ (V b : Alg d L N)) b hb).trans hVv
  rw [Vpr]
  exact tj_of (by linarith [one_le_Q1 hd])
    (EthE_block_le2 hd hLp hj hℓ' hℓC hsum hC (hV.loc b)) hVb

/-- `|u_N(B)| ≤ Q₁ v`. -/
theorem upN_le_v {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    ‖upN C V b‖ ≤ Q1 d * v := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have h := (abs_ε_le (E := Dir d) (p := pPhi d) (pow_pos hL0 (j + 1)) hℓ' _).trans
    (Vpr_le_v hd hLp hjN hℓ' hℓC hsum hC hV hv hVv hb)
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by linarith [one_le_Q1 hd]) hv)).1 h

/-- `‖V_N(B)‖ ≤ 2 Q₁ v`. -/
theorem VpN_le_v {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    Tj d (L : ℝ) (j + 1) ℓ' (VpN C V b : Alg d L N) ≤ ENNReal.ofReal (2 * (Q1 d * v)) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have h0 : 0 ≤ Q1 d * v := mul_nonneg (by linarith [one_le_Q1 hd]) hv
  rw [VpN]
  refine (tn_subE h0 h0 (Vpr_le_v hd hLp hjN hℓ' hℓC hsum hC hV hv hVv hb) ?_).trans
    (ENNReal.ofReal_le_ofReal (by linarith))
  rw [Subalgebra.coe_algebraMap]
  exact (tNorm_algebraMap_le (pow_pos hL0 (j + 1)) hℓ' _).trans
    (ENNReal.ofReal_le_ofReal (upN_le_v hd hLp hjN hℓ' hℓC hsum hC hV hv hVv hb))

include hW hw hWw in
/-- **`‖𝒲_N(B)‖ = ‖S(B)‖ ≤ L^d Q₁² v² + Q₁ w`** (no range of `C`). -/
theorem Sb_le_vw {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    Tj d (L : ℝ) (j + 1) ℓ' (Sb j C V W b : Alg d L N) ≤
      ENNReal.ofReal ((L : ℝ) ^ d * Q1 d ^ 2 * v ^ 2 + Q1 d * w) := by
  have hj : j < N := by omega
  have hQ := one_le_Q1 hd
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hV2 : ∀ b ∈ blockIdx (L := L) (N := N) j,
      Tj d (L : ℝ) (j + 1) (2 * ℓ) (V b : Alg d L N) ≤ ENNReal.ofReal (Q1 d * v) := by
    intro b hb
    have hVb : Tj d (L : ℝ) j ℓ (V b : Alg d L N) ≤ ENNReal.ofReal v :=
      (le_iSup₂ (f := fun b (_ : b ∈ blockIdx (L := L) (N := N) j) =>
        Tj d (L : ℝ) j ℓ (V b : Alg d L N)) b hb).trans hVv
    have hℓ : 0 < ℓ := by linarith
    rw [ENNReal.ofReal_mul (by linarith)]
    exact (Tj2_block_le hd hLp hj hℓ (hV.loc b)).trans (mul_le_mul_left' hVb _)
  have hpair : ∀ b' ∈ blockIdx (L := L) (N := N) j,
      Tj d (L : ℝ) (j + 1) ℓ' (FCE C (Vpr C V b) (Vpr C V b') : Alg d L N) ≤
        ENNReal.ofReal (2 * (Q1 d * v) ^ 2) := by
    intro b' hb'
    have e : ∀ b, (Vpr C V b : Alg d L N) = ECC C (theta (V b : Alg d L N)) := fun b => by
      rw [Vpr, coe_EthE, ECC_theta]
    rw [coe_FCE, e, e]
    refine (FC_succ_le2 hℓ' hℓC hsum hC _ _).trans ?_
    have hq : 0 ≤ Q1 d * v := mul_nonneg (by linarith) hv
    rw [sq, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul hq, ENNReal.ofReal_ofNat]
    gcongr
    · exact hV2 b hb
    · exact hV2 b' hb'
  rw [Sb, VprL, FCE_sum_right]
  have h1 := tn_sum_const (E := Dir d) (p := pPhi d) (h := (L : ℝ) ^ (j + 1)) (ℓ := ℓ')
    (blockIdx (L := L) (N := N) j) (fun b' => FCE C (Vpr C V b) (Vpr C V b'))
    (r := 2 * (Q1 d * v) ^ 2) (by positivity) hpair
  have hn : ((blockIdx (d := d) (L := L) (N := N) j).card : ℝ) ≤ (L : ℝ) ^ d := by
    exact_mod_cast card_blockIdx_last (d := d) (L := L) hjN
  have h2 : Tj d (L : ℝ) (j + 1) ℓ' (((1 / 2 : ℂ) • ∑ b' ∈ blockIdx (L := L) (N := N) j,
      FCE C (Vpr C V b) (Vpr C V b') : EvR (Lam d L N)) : Alg d L N) ≤
      ENNReal.ofReal ((L : ℝ) ^ d * Q1 d ^ 2 * v ^ 2) := by
    rw [Subalgebra.coe_smul, Tj_smul']
    refine (mul_le_mul_left' h1 _).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [this]
    calc 1 / 2 * (((blockIdx (d := d) (L := L) (N := N) j).card : ℝ) * (2 * (Q1 d * v) ^ 2))
        = ((blockIdx (d := d) (L := L) (N := N) j).card : ℝ) * (Q1 d ^ 2 * v ^ 2) := by ring
      _ ≤ (L : ℝ) ^ d * (Q1 d ^ 2 * v ^ 2) := by gcongr
      _ = _ := by ring
  have hWb : Tj d (L : ℝ) j ℓ (W b : Alg d L N) ≤ ENNReal.ofReal w :=
    (le_iSup₂ (f := fun b (_ : b ∈ blockIdx (L := L) (N := N) j) =>
      Tj d (L : ℝ) j ℓ (W b : Alg d L N)) b hb).trans hWw
  have h3 : Tj d (L : ℝ) (j + 1) ℓ' (EthE C (W b) : Alg d L N) ≤ ENNReal.ofReal (Q1 d * w) :=
    tj_of (by linarith) (EthE_block_le2 hd hLp hj hℓ' hℓC hsum hC (hW.loc b)) hWb
  exact tn_addE (by positivity) (by positivity) h2 h3

end Coord

/-! ### The activity -/

set_option maxHeartbeats 1000000 in
/-- **The last step: `K_N(Λ)`.** At `j + 1 = N`, `‖K_N(Λ)‖_{T_N(ℓ')} ≤ C₁ (g³ + ‖K‖_j)` for
`‖V‖_j ≤ g`, `‖𝒲‖_j ≤ g²`, `g, ‖K‖_j ≤ ε₀`, with `C₁, ε₀` depending on `L, A` only. -/
theorem lastK_ts (d : ℕ) (hd : 1 ≤ d) : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧
    ∀ (N j : ℕ), j + 1 = N → ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓC C →
    ∀ (V W : Fam d L N) (K : Act d L N), InF j V → InF j W → (∀ b, ε (V b : Alg d L N) = 0) →
      InK2 j K → ∀ g : ℝ, 0 ≤ g → g ≤ ε₀ →
      Fnorm j ℓ V ≤ ENNReal.ofReal g → Fnorm j ℓ W ≤ ENNReal.ofReal (g ^ 2) →
      Knorm j ℓ A K ≤ ENNReal.ofReal ε₀ →
        Tj d (L : ℝ) (j + 1) ℓ' (KN j C V W K univ : Alg d L N) ≤
          ENNReal.ofReal C₁ * (ENNReal.ofReal (g ^ 3) + Knorm j ℓ A K) := by
  obtain ⟨Lc, hLc⟩ := KN_crude_ts d hd
  refine ⟨Lc, fun L _ hL => ?_⟩
  obtain ⟨A₂, hA₂, hA₂'⟩ := hLc L hL
  refine ⟨A₂, hA₂, fun A hA => ?_⟩
  have hA1 : 1 ≤ A := hA₂.trans hA
  have hA0 : 0 < A := by linarith
  obtain ⟨r₀, hr₀, hcr⟩ := hA₂' A hA
  set ρ := min r₀ 1 with hρdef
  have hρ0 : 0 < ρ := lt_min hr₀ one_pos
  have hρ1 : ρ ≤ 1 := min_le_right _ _
  have hρr : ρ ≤ r₀ := min_le_left _ _
  refine ⟨ρ, 7 / ρ ^ 3, hρ0, by positivity, ?_⟩
  intro N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC V W K hV hW hV0 hK g hg0 hgρ hVg hWg hKρ
  set k := (Knorm j ℓ A K).toReal with hkdef
  have hKfin : Knorm j ℓ A K ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hKρ
  have hKk : Knorm j ℓ A K = ENNReal.ofReal k := (ENNReal.ofReal_toReal hKfin).symm
  have hk0 : 0 ≤ k := ENNReal.toReal_nonneg
  have hkρ : k ≤ ρ := by
    rw [hKk] at hKρ; exact (ENNReal.ofReal_le_ofReal_iff hρ0.le).1 hKρ
  -- the two-parameter family
  set F : ℂ → ℂ → EvR (Lam d L N) := fun t s => KN j C (Vt V t) (Wt W t) (s • K) univ with hF
  have hVt0 : ∀ t b, ε (Vt V t b : Alg d L N) = 0 := fun t b => by
    rw [Vt, Subalgebra.coe_smul, map_smul, hV0, smul_zero]
  have hVf : ∀ b, HolE (fun t : ℂ => Vt V t b) := fun b =>
    HolE.smul differentiable_id (HolE.const _)
  have hWf : ∀ b, HolE (fun t : ℂ => Wt W t b) := fun b =>
    HolE.smul (differentiable_id.pow 2) (HolE.const _)
  have hF1 : ∀ s, HolE (fun t => F t s) := fun s =>
    KN_hol (E := ℂ) j C hVf hWf (Kf := fun _ => s • K) (fun X => HolE.const _) hVt0 univ
  have hF2 : ∀ t, HolE (fun s => F t s) := fun t =>
    KN_hol (E := ℂ) j C (Vf := fun _ => Vt V t) (Wf := fun _ => Wt W t) (Kf := fun s => s • K)
      (fun b => HolE.const _) (fun b => HolE.const _)
      (fun X => HolE.smul differentiable_id (HolE.const _)) (fun _ b => hVt0 t b) univ
  -- the crude bound on the polydisc
  have hball : ∀ R₁ : ℝ, 1 ≤ R₁ → R₁ * g ≤ ρ → ∀ R₂ : ℝ, 1 ≤ R₂ → R₂ * k ≤ ρ →
      ∀ t s : ℂ, ‖t‖ ≤ R₁ → ‖s‖ ≤ R₂ → wnorm (j + 1) ℓ' A univ (F t s) ≤ ENNReal.ofReal 1 := by
    intro R₁ hR₁ hR₁g R₂ hR₂ hR₂k t s ht hs
    have h1 : Fnorm j ℓ (Vt V t) ≤ ENNReal.ofReal r₀ := by
      show Fnorm j ℓ (fun b => t • V b) ≤ _
      rw [Fnorm_smul]
      calc ENNReal.ofReal ‖t‖ * Fnorm j ℓ V ≤ ENNReal.ofReal R₁ * ENNReal.ofReal g := by
            gcongr
        _ = ENNReal.ofReal (R₁ * g) := (ENNReal.ofReal_mul (by linarith)).symm
        _ ≤ ENNReal.ofReal r₀ := ENNReal.ofReal_le_ofReal (hR₁g.trans hρr)
    have h2 : Fnorm j ℓ (Wt W t) ≤ ENNReal.ofReal r₀ := by
      show Fnorm j ℓ (fun b => t ^ 2 • W b) ≤ _
      rw [Fnorm_smul, norm_pow]
      have hRg : (R₁ * g) ^ 2 ≤ ρ := by
        have : 0 ≤ R₁ * g := by positivity
        nlinarith
      calc ENNReal.ofReal (‖t‖ ^ 2) * Fnorm j ℓ W ≤ ENNReal.ofReal (R₁ ^ 2) *
            ENNReal.ofReal (g ^ 2) := by gcongr
        _ = ENNReal.ofReal ((R₁ * g) ^ 2) := by
            rw [← ENNReal.ofReal_mul (by positivity)]; ring_nf
        _ ≤ ENNReal.ofReal r₀ := ENNReal.ofReal_le_ofReal (hRg.trans hρr)
    have h3 : Knorm j ℓ A (s • K) ≤ ENNReal.ofReal r₀ := by
      rw [Knorm_smul, hKk]
      calc ENNReal.ofReal ‖s‖ * ENNReal.ofReal k ≤ ENNReal.ofReal R₂ * ENNReal.ofReal k := by
            gcongr
        _ = ENNReal.ofReal (R₂ * k) := (ENNReal.ofReal_mul (by linarith)).symm
        _ ≤ ENNReal.ofReal r₀ := ENNReal.ofReal_le_ofReal (hR₂k.trans hρr)
    exact hcr N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC (Vt V t) (Wt W t) (s • K) (hV.smul t)
      (hW.smul (t ^ 2)) (hVt0 t) (hK.smul s) h1 h2 h3
  have hw : 0 ≤ wt (j + 1) A (univ : Finset (Lam d L N)) := pow_nonneg hA0.le _
  have hrem : wnorm (j + 1) ℓ' A univ (KN j C V W K univ) ≤
      ENNReal.ofReal (7 / ρ ^ 3 * (g ^ 3 + k)) := by
    refine wnorm_le_of_wpair hA0 univ _ fun g' hg' => ?_
    set Λw := wpairL (wt (j + 1) A (univ : Finset (Lam d L N))) g' with hΛw
    have hB : ∀ R₁ : ℝ, 1 ≤ R₁ → R₁ * g ≤ ρ → ∀ R₂ : ℝ, 1 ≤ R₂ → R₂ * k ≤ ρ →
        ∀ t s : ℂ, ‖t‖ ≤ R₁ → ‖s‖ ≤ R₂ → ‖Λw (F t s : Alg d L N)‖ ≤ 1 := by
      intro R₁ hR₁ hR₁g R₂ hR₂ hR₂k t s ht hs
      rw [hΛw, norm_wpairL hw]
      refine (wpair_le_wnorm hℓ' hA0.le univ _ hg').trans ?_
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (hball R₁ hR₁ hR₁g R₂ hR₂ hR₂k t s ht hs)
    have hR0g : (1 : ℝ) * g ≤ ρ := by linarith
    have hR0k : (1 : ℝ) * k ≤ ρ := by linarith
    have hexp := KN_expansion j C (V := V) W hV0 (U := univ) univ_nonempty
    -- `F(0,0) = 0`
    have hF00 : F 0 0 = 0 := by
      obtain ⟨gg, -, e⟩ := hexp
      have := e 0
      simp only [zero_smul, zero_add, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, add_zero] at this
      simp only [hF, zero_smul]
      exact this
    -- the mixed term
    have X1 : ‖Λw (F 1 1 : Alg d L N) - Λw (F 1 0 : Alg d L N) - Λw (F 0 1 : Alg d L N) +
        Λw (F 0 0 : Alg d L N)‖ ≤ 4 * (g / ρ) * (k / ρ) := by
      refine rad2 (by norm_num) hρ0 hg0 hgρ hk0 hkρ fun R₁ hR₁ hR₁g R₂ hR₂ hR₂k => ?_
      have := mixed_le hF1 hF2 Λw hR₁ hR₂ (B := 1) (hB R₁ hR₁ hR₁g R₂ hR₂ hR₂k)
      simpa using this
    -- the third-order remainder at `K = 0` (`K^{(2)}(Λ) = 0`)
    have X2 : ‖Λw (F 1 0 : Alg d L N)‖ ≤ 2 * (g / ρ) ^ 3 := by
      have hexp' : ExpE2 (fun t => F t 0) 0 0 (K2 j C V univ) := by
        refine OrdE.congr hexp fun t => ?_
        simp only [hF, zero_smul]
      have := rad1 (n := 3) (c := 2) (X := ‖Λw (F 1 0 : Alg d L N) - Λw (K2 j C V univ : Alg d L N)‖)
        (by norm_num) (by norm_num) hρ0 hg0 hgρ fun R hR hRg => by
          have := rem3_le hexp' Λw hR (B := 1) fun ζ hζ =>
            hB R hR hRg 1 le_rfl hR0k ζ 0 hζ.le (by simp)
          simpa using this
      rwa [K2_last j C V hjN, ZeroMemClass.coe_zero, map_zero, sub_zero] at this
    -- the part linear in `K` at `V = 𝒲 = 0`: the Schwarz lemma
    have X3 : ‖Λw (F 0 1 : Alg d L N)‖ ≤ 1 * (k / ρ) ^ 1 := by
      refine rad1 (n := 1) le_rfl zero_le_one hρ0 hk0 hkρ fun R hR hRk => ?_
      have hR0 : 0 < R := by linarith
      have hd0 : Differentiable ℂ (fun s => Λw (F 0 s : Alg d L N)) := (hF2 0).lin Λw
      obtain ⟨kk, hkk, e⟩ := OrdS.one_of_zero hd0 (by simp only [hF00, ZeroMemClass.coe_zero,
        map_zero])
      have := coeff_le hkk e hR0 (B := 1) (fun ζ hζ => hB 1 le_rfl hR0g R hR hRk 0 ζ (by simp)
        hζ.le) (z := 1) (by simp; linarith)
      have e1 : Λw (F 0 1 : Alg d L N) = kk 1 := by simpa using e 1
      rw [e1]; exact this
    have e11 : F 1 1 = KN j C V W K univ := by simp only [hF, Vt_one, Wt_one, one_smul]
    have hsplit : Λw (KN j C V W K univ : Alg d L N) =
        (Λw (F 1 1 : Alg d L N) - Λw (F 1 0 : Alg d L N) - Λw (F 0 1 : Alg d L N) +
          Λw (F 0 0 : Alg d L N)) + Λw (F 1 0 : Alg d L N) + Λw (F 0 1 : Alg d L N) := by
      rw [hF00, e11]
      simp only [ZeroMemClass.coe_zero, map_zero]
      ring
    rw [← norm_wpairL hw, ← hΛw, hsplit]
    refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
    have hρ3 : 0 < ρ ^ 3 := by positivity
    have hgk : g / ρ * (k / ρ) ≤ k / ρ ^ 3 := by
      rw [div_mul_div_comm]
      have h1 : g * k ≤ k := by nlinarith
      have h2 : ρ ^ 3 ≤ ρ * ρ := by
        calc ρ ^ 3 = ρ * ρ * ρ := by ring
          _ ≤ ρ * ρ * 1 := by gcongr
          _ = ρ * ρ := by ring
      calc g * k / (ρ * ρ) ≤ k / (ρ * ρ) := div_le_div_of_nonneg_right h1 (by positivity)
        _ ≤ k / ρ ^ 3 := div_le_div_of_nonneg_left hk0 hρ3 h2
    have hk1 : k / ρ ≤ k / ρ ^ 3 :=
      div_le_div_of_nonneg_left hk0 hρ3 (by
        calc ρ ^ 3 ≤ ρ ^ 1 := pow_le_pow_of_le_one hρ0.le hρ1 (by norm_num)
          _ = ρ := pow_one ρ)
    have hg3 : (g / ρ) ^ 3 = g ^ 3 / ρ ^ 3 := div_pow _ _ _
    have : 7 / ρ ^ 3 * (g ^ 3 + k) = 7 * (g ^ 3 / ρ ^ 3) + 7 * (k / ρ ^ 3) := by ring
    rw [this]
    rw [one_mul, pow_one] at X3
    rw [hg3] at X2
    have hX1 : 4 * (g / ρ) * (k / ρ) ≤ 4 * (k / ρ ^ 3) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hgk (by norm_num)
    linarith [X1, X2, X3, hX1, hk1, show 0 ≤ g ^ 3 / ρ ^ 3 by positivity,
      show 0 ≤ k / ρ ^ 3 by positivity]
  -- assemble
  subst hjN
  rw [← wnorm_top ℓ' A]
  refine hrem.trans (le_of_eq ?_)
  rw [hKk, ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) hk0]

end LastN

end

end Step2
