import Step2.Map.Hol
import Step2.Map.Cauchy

/-!
# The renormalisation group step to second order (`h02uv-outline.tex`, Expected result 7.1)

**Theorem `step2`** (corrected form of Expected result 7.1). For `d ≥ 2`, `L ≥ L₀(d)`,
`A ≥ A₀(L, d)` there are `ε, C₁ > 0` (depending on `L, A`) such that for `j + 1 < N`, a
covariance `C = C'_{j+1}` with `GoodCov2`, block families `V, 𝒲` and an activity `K` with
`‖V‖_j ≤ ḡ`, `‖𝒲‖_j ≤ ḡ²`, `ḡ ≤ ε`, `‖K‖_j ≤ ε`, and every connected `(j+1)`-polymer `U`:

  `A^{(|𝓑_{j+1}(U)| - 2^d)_+} ‖K_{j+1}(U) - K^{(2)}(U)‖_{T_{j+1}(ℓ)}
     ≤ C₀ (L^{d-3} + A^{-η}) ‖K‖_j + C₁ (ḡ³ + ḡ ‖K‖_j + ‖K‖_j²)`,

where `K_{j+1} = Knext2` is the polymer activity of the second-order map and
`K^{(2)} = K2` the explicit second-order part (`e:K2`). In `d = 2`, `L^{d-3} = L^{-1}`
(`step2_d2`). `C₀, η` depend only on `d`.

Together with `step2_ZVK` (`𝔼θ Z_j = Z_{j+1}`, exactly) and `step2_V`
(`‖(u+V)_{j+1}(B) - V'_B + Loc_{B_+,B} S(B_+)‖ = ‖𝔼θQ(B)‖ ≤ C ‖K‖_j`), this is the
formalised content of Expected result 7.1.

Proof: `K_{j+1}` is entire (`Knext2_hol`) and bounded by `1` on a ball of radius `ε`
(`Knext2_crude`). With `F(t, s) = K_{j+1}(tV, t²𝒲, sK)`:

* `F(t, 0) = t² K^{(2)} + O(t³)` (`Knext2_expansion`), so `|F(1,0) - K^{(2)}| ≤ 2(ḡ/ε)³`;
* `F(0, s) = s 𝓛(K) + O(s²)` (`Knext2_lin`), so `|F(0,1) - 𝓛(K)| ≤ 2(‖K‖/ε)²`;
* `|F(1,1) - F(1,0) - F(0,1) + F(0,0)| ≤ 4 (ḡ/ε)(‖K‖/ε)` (`mixed_le`), and `F(0,0) = 0`;
* `‖𝓛(K)‖ ≤ C₀ (L^{d-3} + A^{-η}) ‖K‖` (`Llin2_bound`).
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

/-! ### Scaling -/

theorem IsSym.smul' {F : Alg d L N} (hF : IsSym F) (c : ℂ) : IsSym (c • F) := fun n z hz => by
  rw [coeff_smul, hF n z hz, mul_zero]

theorem InF.smul {j : ℕ} {V : Fam d L N} (hV : InF j V) (c : ℂ) : InF j (fun b => c • V b) :=
  ⟨fun b => Subalgebra.smul_mem _ (hV.loc b) c, fun b => IsSym.smul' (hV.sym b) c⟩

theorem InK2.smul {j : ℕ} {K : Act d L N} (hK : InK2 j K) (c : ℂ) : InK2 j (c • K) :=
  ⟨fun X hX => Subalgebra.smul_mem _ (hK.loc X hX) c, fun X hX => IsSym.smul' (hK.sym X hX) c⟩

theorem Fnorm_smul (j : ℕ) (ℓ : ℝ) (c : ℂ) (V : Fam d L N) :
    Fnorm j ℓ (fun b => c • V b) = ENNReal.ofReal ‖c‖ * Fnorm j ℓ V := by
  unfold Fnorm
  simp only [Subalgebra.coe_smul, Tj_smul', ENNReal.mul_iSup]

theorem Vt_zero (V : Fam d L N) : Vt V 0 = 0 := funext fun b => zero_smul _ _

theorem Wt_zero (W : Fam d L N) : Wt W 0 = 0 := funext fun _ => by simp [Wt]

theorem Vt_one (V : Fam d L N) : Vt V 1 = V := funext fun b => one_smul _ _

theorem Wt_one (W : Fam d L N) : Wt W 1 = W := funext fun _ => by simp [Wt]

/-! ### The identity `𝔼θ Z_j = Z_{j+1}` -/

/-- **`𝔼_C θ Z_j = Z_{j+1}`**, with `Z_j = ∑_X I_j^{Λ∖X} K(X)`, `I_j(B) = e^{-V(B)}(1 + 𝒲(B))`,
and `Z_{j+1} = ∑_U I_{j+1}^{Λ∖U} e^{-u_{j+1}(U)} K_{j+1}(U)`. -/
theorem step2_ZVK (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V W : Fam d L N)
    (K : Act d L N) :
    ECCE C (thetaE (gZ j (Ib V W) K)) = ∑ U ∈ Pj (j + 1) univ,
      bpow j (Ip j C V W K) (univ \ U) *
        (Complex.exp (-uX j C V W K U) • Knext2 j C V W K U) := by
  rw [gZVK j C (Ib V W) (Ip j C V W K) K (J := J2 j K) (fun b c h => J2_of_not_small j K b c h)]
  refine sum_congr rfl fun U _ => ?_
  rw [Knext2, smul_smul, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_smul]

/-! ### The coupling constants -/

/-- **The `V`-part**: `(u+V)_{j+1}(B) - (V'_B - Loc_{B_+,B} S(B_+)) = -𝔼θQ(B)` is bounded by
`C ‖K‖_j`. -/
theorem step2_V_ts (d : ℕ) (hd : 1 ≤ d) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (L : ℕ) [NeZero L],
    pauliL0 d ≤ L → 2 ^ (d + 3) + 8 * d < L →
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓC C →
    ∀ (V W : Fam d L N) (K : Act d L N), InK2 j K → ∀ A : ℝ, 1 ≤ A →
    ∀ b ∈ blockIdx (L := L) (N := N) j,
      Tj d (L : ℝ) (j + 1) ℓ' ((uVp j C V W K b - (Vpr C V b - LS j C V W b) :
        EvR (Lam d L N)) : Alg d L N) ≤ ENNReal.ofReal C₀ * Knorm j ℓ A K := by
  classical
  obtain ⟨Cl, hCl0, hloc⟩ := exists_Loc2sXY_bound d hd
  obtain ⟨c, hc⟩ := card_small_containing d
  refine ⟨Q1 d * (c * Cl), by have := one_le_Q1 hd; positivity, ?_⟩
  intro L _ hLp hL8 N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC V W K hK A hA b hb
  have hj : j < N := by omega
  have e : uVp j C V W K b - (Vpr C V b - LS j C V W b) = -EthE C (Q2 j K b) := by
    rw [uVp]; abel
  rw [e, NegMemClass.coe_neg]
  refine (le_of_eq (tNorm_neg _)).trans ?_
  have hYp : IsPolymer j (blockSet (L := L) (N := N) j b) := (isSmall_blockSet_of_mem hb).1
  have hmem : (Q2 j K b : Alg d L N) ∈
      NX (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N)) := by
    rw [Q2, if_pos hjN, AddSubmonoidClass.coe_finsetSum]
    exact Subalgebra.sum_mem _ fun X _ => Loc2XY_mem' hd hYp _ _
  refine (EthE_block_le2 hd hLp hj hℓ' hℓC hsum hC hmem).trans ?_
  rw [ENNReal.ofReal_mul (by have := one_le_Q1 hd; positivity), mul_assoc]
  refine mul_le_mul_left' ?_ _
  rw [Q2, if_pos hjN, AddSubmonoidClass.coe_finsetSum]
  refine (tNorm_sum_le _ _).trans ?_
  calc ∑ X ∈ (smallSets j).filter (fun X => blockSet j b ⊆ X),
        Tj d (L : ℝ) j ℓ (Loc2E X (blockSet (L := L) (N := N) j b) (K X) : Alg d L N)
      ≤ ∑ _X ∈ (smallSets j).filter (fun X => blockSet (L := L) (N := N) j b ⊆ X),
          ENNReal.ofReal Cl * Knorm j ℓ A K := sum_le_sum fun X hX => by
        obtain ⟨hs, hbX⟩ := mem_smallSets_filter.1 hX
        have hcX : IsConn j X := ⟨hs.1, hs.2.1⟩
        rw [coe_Loc2E]
        exact (hloc L hL8 N j hj X _ hs hbX _ (hK.loc X hcX) ℓ hℓ).trans
          (mul_le_mul_left' (Tj_le_Knorm hA hcX) _)
    _ = ((((smallSets (d := d) (L := L) (N := N) j).filter
          (fun X => blockSet (L := L) (N := N) j b ⊆ X)).card : ℕ) : ENNReal) *
          (ENNReal.ofReal Cl * Knorm j ℓ A K) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (c : ENNReal) * (ENNReal.ofReal Cl * Knorm j ℓ A K) := by
        gcongr; exact_mod_cast hc L N j b hb
    _ = ENNReal.ofReal (c * Cl) * Knorm j ℓ A K := by
        rw [← mul_assoc, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-- **The `V`-part**: `(u+V)_{j+1}(B) - (V'_B - Loc_{B_+,B} S(B_+)) = -𝔼θQ(B)` is bounded by
`C ‖K‖_j`. -/
theorem step2_V (d : ℕ) (hd : 1 ≤ d) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (L : ℕ) [NeZero L],
    pauliL0 d ≤ L → 2 ^ (d + 3) + 8 * d < L →
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ : ℝ, 0 < ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓ C →
    ∀ (V W : Fam d L N) (K : Act d L N), InK2 j K → ∀ A : ℝ, 1 ≤ A →
    ∀ b ∈ blockIdx (L := L) (N := N) j,
      Tj d (L : ℝ) (j + 1) ℓ ((uVp j C V W K b - (Vpr C V b - LS j C V W b) :
        EvR (Lam d L N)) : Alg d L N) ≤ ENNReal.ofReal C₀ * Knorm j ℓ A K := by
  obtain ⟨C₀, hC₀, h⟩ := step2_V_ts d hd
  exact ⟨C₀, hC₀, fun L _ hLp hL8 N j hj ℓ hℓ C hC =>
    h L hLp hL8 N j hj ℓ ℓ ℓ hℓ hℓ hℓ (by linarith) C hC⟩

/-! ### The polymer activity -/

/-- The weighted pairing as a linear functional. -/
def wpairL (w : ℝ) (g : TestFn (Lam d L N)) : Alg d L N →ₗ[ℂ] ℂ := (w : ℂ) • pairL g

theorem norm_wpairL {w : ℝ} (hw : 0 ≤ w) (g : TestFn (Lam d L N)) (F : Alg d L N) :
    ‖wpairL w g F‖ = w * ‖pair F g‖ := by
  rw [wpairL, LinearMap.smul_apply, smul_eq_mul]
  exact norm_wpair w hw _

set_option maxHeartbeats 1000000 in
/-- **Theorem `step2`.** -/
theorem step2_ts (d : ℕ) (hd : 2 ≤ d) : ∃ (C₀ η : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧ 0 < η ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓC C →
    ∀ (V W : Fam d L N) (K : Act d L N), InF j V → InF j W → (∀ b, ε (V b : Alg d L N) = 0) →
      InK2 j K → ∀ g : ℝ, 0 ≤ g → g ≤ ε₀ →
      Fnorm j ℓ V ≤ ENNReal.ofReal g → Fnorm j ℓ W ≤ ENNReal.ofReal (g ^ 2) →
      Knorm j ℓ A K ≤ ENNReal.ofReal ε₀ →
      ∀ U : Finset (Lam d L N), IsConn (j + 1) U →
        wnorm (j + 1) ℓ' A U (Knext2 j C V W K U - K2 j C V U) ≤
          ENNReal.ofReal (C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3 + A ^ (-η))) * Knorm j ℓ A K +
          ENNReal.ofReal C₁ * (ENNReal.ofReal (g ^ 3) + ENNReal.ofReal g * Knorm j ℓ A K +
            Knorm j ℓ A K ^ 2) := by
  obtain ⟨C₀, η, Ll, hC₀, hη, hLl⟩ := Llin2_bound_ts d hd
  obtain ⟨Lc, hLc⟩ := Knext2_crude_ts d (by omega)
  refine ⟨C₀, η, max Ll Lc, hC₀, hη, ?_⟩
  intro L _ hL
  obtain ⟨A₁, hA₁, hA₁'⟩ := hLl L (le_trans (le_max_left _ _) hL)
  obtain ⟨A₂, hA₂, hA₂'⟩ := hLc L (le_trans (le_max_right _ _) hL)
  refine ⟨max A₁ A₂, le_trans hA₁ (le_max_left _ _), ?_⟩
  intro A hA
  have hA1 : 1 ≤ A := le_trans hA₁ (le_trans (le_max_left _ _) hA)
  have hA0 : 0 < A := by linarith
  obtain ⟨r₀, hr₀, hcr⟩ := hA₂' A (le_trans (le_max_right _ _) hA)
  set ρ := min r₀ 1 with hρdef
  have hρ0 : 0 < ρ := lt_min hr₀ one_pos
  have hρ1 : ρ ≤ 1 := min_le_right _ _
  have hρr : ρ ≤ r₀ := min_le_left _ _
  refine ⟨ρ, 4 / ρ ^ 3, hρ0, by positivity, ?_⟩
  intro N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC V W K hV hW hV0 hK g hg0 hgρ hVg hWg hKρ U hU
  have hUne : U.Nonempty := hU.2.1
  set k := (Knorm j ℓ A K).toReal with hkdef
  have hKfin : Knorm j ℓ A K ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hKρ
  have hKk : Knorm j ℓ A K = ENNReal.ofReal k := (ENNReal.ofReal_toReal hKfin).symm
  have hk0 : 0 ≤ k := ENNReal.toReal_nonneg
  have hkρ : k ≤ ρ := by
    rw [hKk] at hKρ; exact (ENNReal.ofReal_le_ofReal_iff hρ0.le).1 hKρ
  -- the two-parameter family
  set F : ℂ → ℂ → EvR (Lam d L N) := fun t s => Knext2 j C (Vt V t) (Wt W t) (s • K) U with hF
  have hVt0 : ∀ t b, ε (Vt V t b : Alg d L N) = 0 := fun t b => by
    rw [Vt, Subalgebra.coe_smul, map_smul, hV0, smul_zero]
  -- holomorphy
  have hVf : ∀ b, HolE (fun t : ℂ => Vt V t b) := fun b =>
    HolE.smul differentiable_id (HolE.const _)
  have hWf : ∀ b, HolE (fun t : ℂ => Wt W t b) := fun b =>
    HolE.smul (differentiable_id.pow 2) (HolE.const _)
  have hF1 : ∀ s, HolE (fun t => F t s) := fun s =>
    Knext2_hol (E := ℂ) j C hVf hWf (Kf := fun _ => s • K) (fun X => HolE.const _) hVt0 U
  have hF2 : ∀ t, HolE (fun s => F t s) := fun t =>
    Knext2_hol (E := ℂ) j C (Vf := fun _ => Vt V t) (Wf := fun _ => Wt W t) (Kf := fun s => s • K)
      (fun b => HolE.const _) (fun b => HolE.const _)
      (fun X => HolE.smul differentiable_id (HolE.const _)) (fun _ b => hVt0 t b) U
  -- the crude bound on the polydisc
  have hball : ∀ R₁ : ℝ, 1 ≤ R₁ → R₁ * g ≤ ρ → ∀ R₂ : ℝ, 1 ≤ R₂ → R₂ * k ≤ ρ →
      ∀ t s : ℂ, ‖t‖ ≤ R₁ → ‖s‖ ≤ R₂ → wnorm (j + 1) ℓ' A U (F t s) ≤ ENNReal.ofReal 1 := by
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
    exact hcr N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC (Vt V t) (Wt W t) (s • K) (hV.smul t) (hW.smul (t ^ 2))
      (hVt0 t) (hK.smul s) h1 h2 h3 U hU
  -- the weighted pairings
  have hw : 0 ≤ wt (j + 1) A U := pow_nonneg hA0.le _
  have hrem : wnorm (j + 1) ℓ' A U (Knext2 j C V W K U - K2 j C V U - Llin2 j C K U) ≤
      ENNReal.ofReal (4 / ρ ^ 3 * (g ^ 3 + g * k + k ^ 2)) := by
    refine wnorm_le_of_wpair hA0 U _ fun g' hg' => ?_
    set Λw := wpairL (wt (j + 1) A U) g' with hΛw
    have hB : ∀ R₁ : ℝ, 1 ≤ R₁ → R₁ * g ≤ ρ → ∀ R₂ : ℝ, 1 ≤ R₂ → R₂ * k ≤ ρ →
        ∀ t s : ℂ, ‖t‖ ≤ R₁ → ‖s‖ ≤ R₂ → ‖Λw (F t s : Alg d L N)‖ ≤ 1 := by
      intro R₁ hR₁ hR₁g R₂ hR₂ hR₂k t s ht hs
      rw [hΛw, norm_wpairL hw]
      refine (wpair_le_wnorm hℓ' hA0.le U _ hg').trans ?_
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (hball R₁ hR₁ hR₁g R₂ hR₂ hR₂k t s ht hs)
    have hR0g : (1 : ℝ) * g ≤ ρ := by linarith
    have hR0k : (1 : ℝ) * k ≤ ρ := by linarith
    -- `F(0,0) = 0`
    have hF00 : F 0 0 = 0 := by
      have h := Knext2_lin j C (K := K) hUne
      obtain ⟨q, -, e⟩ := h
      have := e 0
      simp only [zero_smul, zero_add, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow] at this
      simp only [hF, Vt_zero, Wt_zero, zero_smul]
      exact this
    -- the mixed term
    have X1 : ‖Λw (F 1 1 : Alg d L N) - Λw (F 1 0 : Alg d L N) - Λw (F 0 1 : Alg d L N) +
        Λw (F 0 0 : Alg d L N)‖ ≤ 4 * (g / ρ) * (k / ρ) := by
      refine rad2 (by norm_num) hρ0 hg0 hgρ hk0 hkρ fun R₁ hR₁ hR₁g R₂ hR₂ hR₂k => ?_
      have := mixed_le hF1 hF2 Λw hR₁ hR₂ (B := 1) (hB R₁ hR₁ hR₁g R₂ hR₂ hR₂k)
      simpa using this
    -- the third-order remainder at `K = 0`
    have X2 : ‖Λw (F 1 0 : Alg d L N) - Λw (K2 j C V U : Alg d L N)‖ ≤ 2 * (g / ρ) ^ 3 := by
      have hexp := Knext2_expansion j C (V := V) (W := W) hV0 hUne
      have hexp' : ExpE2 (fun t => F t 0) 0 0 (K2 j C V U) := by
        refine OrdE.congr hexp fun t => ?_
        simp only [hF, zero_smul]
      refine rad1 (n := 3) (by norm_num) (by norm_num) hρ0 hg0 hgρ fun R hR hRg => ?_
      have := rem3_le hexp' Λw hR (B := 1) fun ζ hζ =>
        hB R hR hRg 1 le_rfl hR0k ζ 0 hζ.le (by simp)
      simpa using this
    -- the second-order remainder at `V = 𝒲 = 0`
    have X3 : ‖Λw (F 0 1 : Alg d L N) - Λw (Llin2 j C K U : Alg d L N)‖ ≤ 2 * (k / ρ) ^ 2 := by
      have hlin := Knext2_lin j C (K := K) hUne
      have hlin' : ExpE1 (fun s => F 0 s) 0 (Llin2 j C K U) := by
        refine ExpE1.congr hlin fun s => ?_
        simp only [hF, Vt_zero, Wt_zero]
      refine rad1 (n := 2) (by norm_num) (by norm_num) hρ0 hk0 hkρ fun R hR hRk => ?_
      have := rem2_le hlin' Λw hR (B := 1) fun ζ hζ =>
        hB 1 le_rfl hR0g R hR hRk 0 ζ (by simp) hζ.le
      simpa using this
    have e11 : F 1 1 = Knext2 j C V W K U := by simp only [hF, Vt_one, Wt_one, one_smul]
    have hsplit : Λw ((Knext2 j C V W K U - K2 j C V U - Llin2 j C K U : EvR (Lam d L N)) :
        Alg d L N) = (Λw (F 1 1 : Alg d L N) - Λw (F 1 0 : Alg d L N) -
          Λw (F 0 1 : Alg d L N) + Λw (F 0 0 : Alg d L N)) +
        (Λw (F 1 0 : Alg d L N) - Λw (K2 j C V U : Alg d L N)) +
        (Λw (F 0 1 : Alg d L N) - Λw (Llin2 j C K U : Alg d L N)) := by
      rw [hF00, e11]
      simp only [AddSubgroupClass.coe_sub, map_sub, ZeroMemClass.coe_zero, map_zero]
      ring
    rw [← norm_wpairL hw, ← hΛw, hsplit]
    refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
    have hρ3 : 0 < ρ ^ 3 := by positivity
    have hgk : g / ρ * (k / ρ) ≤ g * k / ρ ^ 3 := by
      rw [div_mul_div_comm, ← sq]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (by nlinarith [pow_le_pow_of_le_one hρ0.le hρ1 (show 2 ≤ 3 by norm_num)])
    have hkk : (k / ρ) ^ 2 ≤ k ^ 2 / ρ ^ 3 := by
      rw [div_pow]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_of_le_one hρ0.le hρ1 (by norm_num))
    have hg3 : (g / ρ) ^ 3 = g ^ 3 / ρ ^ 3 := div_pow _ _ _
    have : 4 / ρ ^ 3 * (g ^ 3 + g * k + k ^ 2) =
        4 * (g ^ 3 / ρ ^ 3) + 4 * (g * k / ρ ^ 3) + 4 * (k ^ 2 / ρ ^ 3) := by ring
    rw [this]
    nlinarith [X1, X2, X3, show 0 ≤ g ^ 3 / ρ ^ 3 by positivity,
      show 0 ≤ k ^ 2 / ρ ^ 3 by positivity]
  -- assemble
  have hdec : Knext2 j C V W K U - K2 j C V U =
      Llin2 j C K U + (Knext2 j C V W K U - K2 j C V U - Llin2 j C K U) := by abel
  rw [hdec]
  refine (wnorm_add_le' _ _ _ _ _ _).trans (add_le_add
    (hA₁' A (le_trans (le_max_left _ _) hA) N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC K hK U hU) (hrem.trans (le_of_eq ?_)))
  rw [hKk, ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hg0,
    ← ENNReal.ofReal_pow hk0, ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]

set_option maxHeartbeats 1000000 in
/-- **Theorem `step2`.** -/
theorem step2 (d : ℕ) (hd : 2 ≤ d) : ∃ (C₀ η : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧ 0 < η ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ : ℝ, 0 < ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓ C →
    ∀ (V W : Fam d L N) (K : Act d L N), InF j V → InF j W → (∀ b, ε (V b : Alg d L N) = 0) →
      InK2 j K → ∀ g : ℝ, 0 ≤ g → g ≤ ε₀ →
      Fnorm j ℓ V ≤ ENNReal.ofReal g → Fnorm j ℓ W ≤ ENNReal.ofReal (g ^ 2) →
      Knorm j ℓ A K ≤ ENNReal.ofReal ε₀ →
      ∀ U : Finset (Lam d L N), IsConn (j + 1) U →
        wnorm (j + 1) ℓ A U (Knext2 j C V W K U - K2 j C V U) ≤
          ENNReal.ofReal (C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3 + A ^ (-η))) * Knorm j ℓ A K +
          ENNReal.ofReal C₁ * (ENNReal.ofReal (g ^ 3) + ENNReal.ofReal g * Knorm j ℓ A K +
            Knorm j ℓ A K ^ 2) := by
  obtain ⟨C₀, η, L₀, hC₀, hη, h⟩ := step2_ts d hd
  refine ⟨C₀, η, L₀, hC₀, hη, fun L _ hL => ?_⟩
  obtain ⟨A₀, hA₀, h'⟩ := h L hL
  refine ⟨A₀, hA₀, fun A hA => ?_⟩
  obtain ⟨ε₀, C₁, hε, hC₁, h''⟩ := h' A hA
  exact ⟨ε₀, C₁, hε, hC₁, fun N j hj ℓ hℓ C hC =>
    h'' N j hj ℓ ℓ ℓ hℓ hℓ hℓ (by linarith) C hC⟩

/-- **Theorem `step2` in `d = 2`**: the contraction factor is `L^{-1}`. -/
theorem step2_d2 : ∃ (C₀ η : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧ 0 < η ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ : ℝ, 0 < ℓ →
    ∀ C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ, GoodCov2 j ℓ C →
    ∀ (V W : Fam 2 L N) (K : Act 2 L N), InF j V → InF j W → (∀ b, ε (V b : Alg 2 L N) = 0) →
      InK2 j K → ∀ g : ℝ, 0 ≤ g → g ≤ ε₀ →
      Fnorm j ℓ V ≤ ENNReal.ofReal g → Fnorm j ℓ W ≤ ENNReal.ofReal (g ^ 2) →
      Knorm j ℓ A K ≤ ENNReal.ofReal ε₀ →
      ∀ U : Finset (Lam 2 L N), IsConn (j + 1) U →
        wnorm (j + 1) ℓ A U (Knext2 j C V W K U - K2 j C V U) ≤
          ENNReal.ofReal (C₀ * ((L : ℝ)⁻¹ + A ^ (-η))) * Knorm j ℓ A K +
          ENNReal.ofReal C₁ * (ENNReal.ofReal (g ^ 3) + ENNReal.ofReal g * Knorm j ℓ A K +
            Knorm j ℓ A K ^ 2) := by
  obtain ⟨C₀, η, L₀, hC₀, hη, h⟩ := step2 2 le_rfl
  refine ⟨C₀, η, L₀, hC₀, hη, fun L _ hL => ?_⟩
  obtain ⟨A₀, hA₀, h'⟩ := h L hL
  refine ⟨A₀, hA₀, fun A hA => ?_⟩
  obtain ⟨ε', C₁, hε, hC₁, h''⟩ := h' A hA
  refine ⟨ε', C₁, hε, hC₁, fun N j hj ℓ hℓ C hC V W K hV hW hV0 hK g hg hgε hVg hWg hKε U hU => ?_⟩
  have e : (L : ℝ) ^ 2 / (L : ℝ) ^ 3 = (L : ℝ)⁻¹ := by
    have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
    field_simp
  have := h'' N j hj ℓ hℓ C hC V W K hV hW hV0 hK g hg hgε hVg hWg hKε U hU
  rwa [e] at this

end

end Step2
