import Obs2.Loc.LocContract
import Obs2.Est.EstNorm

/-!
# The localisation in the observable estimates: bounds, the closed support gap

## Bounds for `LocO2` (pointed `loc^a`, `loc^b`)
* `locAp_bound`, `exists_LocO2_obs_bound`: `‖π_obs Loc_{X,Y} F‖_{T_j(ℓ)} ≤ C ‖π_obs F‖_{T_j(ℓ)}`
  for `X` small, `Y ⊆ X`, single-source weights (the hypothesis `BHO.hloc` of `Obs2.Est.EstBlock`);
* `LocO2_cmpIn`: `Loc_{X,Y} F` has its bulk and single-source components in `𝒩(Y^□)` if each
  source point lies in `X` or the corresponding component of `F` vanishes; `LocO2_cmpIn_pts`:
  always in `𝒩(Y^□ ∪ {a, b})`. (The unconditional form of `BHO.hlocl` fails for the pointed
  `loc^a`: for `a ∉ X` it puts `m(F_a)ψ̄_a` at `a`, which need not lie in `Y^□`.)

## The support gap and its repair
With the earlier operator, `loc^a_{X,Y} = 0` for `a ∉ X`, so for a small set `X ∌ a`,
`(1 - Loc_{X,X})` was the identity on the `σ_a` component, and such components occur (the
second-order map puts `σ_a` into `𝒲(B)`, `B ∌ a`, within the range of `C`, hence into `K(X)`,
`X ∌ a`). They were only bounded, not contracted, so `k_{j+1} ≤ θ k_j + B ḡ² m_j` failed.

`Obs2.LocO2` now uses the pointed `loc^a` (`Obs2.locAp`): for `a ∉ X` it localises at the point.
Then (`sub_LocO2_a_of_not_mem`) `(F - Loc_{X,X} F)_a = F_a - locA a {a} {a} F_a`, which contracts
for `a ∈ X^□` (`exists_odd_contract_pt`, `exists_even_contract_pt`, `sub_LocO2_a_contract_one`):
`‖F - m(F) ψ̄_a‖_{T_{j+1}(ℓ')} ≤ C L^{-1} ‖F‖_{T_j(ℓ)}`. The proof is the core bound
`exists_core2_bound` (Taylor expansion of order `0` over `X^□`, which needs only the vanishing of
the masses, not `a ∈ X`) with the boundedness of the pointed localisation (`locOdd_pt_bound`,
`locEven_pt_bound`). Since the `σ_a` components of `𝒲(B)`, `K(X)` vanish at distance `≥ L^j`
from `a` (`Obs2.Pair.Coal`), every nonzero one has `a ∈ X^□`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann FRD Loc Obs Obs.SA Obs.LocObs Step ENNReal

variable {d L N : ℕ} [NeZero L]

/-! ### The support gap is closed -/

/-! ### Bounds for `LocO2` -/

theorem locA_bound (d : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℕ) [NeZero L],
    2 ^ (d + 3) + 8 * d < L → ∀ N j : ℕ, j < N → ∀ X Y : Finset (Lam d L N), IsSmall j X →
    Y ⊆ X → ∀ F ∈ NX (nbhd j X : Set (Lam d L N)), ∀ (cc : ObsCase) (a : Lam d L N),
    ∀ ℓ : ℝ, 0 < ℓ →
      Tj d (L : ℝ) j ℓ (locA cc a X Y F) ≤ ENNReal.ofReal C * Tj d (L : ℝ) j ℓ F ∧
      Tj d (L : ℝ) j ℓ (locB cc a X Y F) ≤ ENNReal.ofReal C * Tj d (L : ℝ) j ℓ F := by
  obtain ⟨C1, hC1, h1⟩ := exists_odd_bound d
  obtain ⟨C2, hC2, h2⟩ := exists_even_bound d
  refine ⟨C1 + C2, by positivity, fun L _ hL N j hj X Y hX hYX F hF cc a ℓ hℓ => ?_⟩
  have e1 : ENNReal.ofReal C1 ≤ ENNReal.ofReal (C1 + C2) := ENNReal.ofReal_le_ofReal (by linarith)
  have e2 : ENNReal.ofReal C2 ≤ ENNReal.ofReal (C1 + C2) := ENNReal.ofReal_le_ofReal (by linarith)
  cases cc
  · exact ⟨(h1 L hL N j hj X Y hX hYX F hF (-1) {a} ℓ hℓ).trans (mul_le_mul_right' e1 _),
      (h1 L hL N j hj X Y hX hYX F hF 1 {a} ℓ hℓ).trans (mul_le_mul_right' e1 _)⟩
  · exact ⟨(h2 L hL N j hj X Y hX hYX F hF {a} ℓ hℓ).trans (mul_le_mul_right' e2 _),
      (h2 L hL N j hj X Y hX hYX F hF {a} ℓ hℓ).trans (mul_le_mul_right' e2 _)⟩

/-! ### The pointed localisation -/

/-- `‖locOdd s P' X' Y' F‖ ≤ C ‖F‖` for `F ∈ 𝒩(X^□)`, `X` small, and any `Y' ⊆ X'`. -/
theorem locOdd_pt_bound (d : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℕ) [NeZero L],
    2 ^ (d + 3) + 8 * d < L → ∀ N j : ℕ, j < N → ∀ X : Finset (Lam d L N), IsSmall j X →
    ∀ F ∈ NX (nbhd j X : Set (Lam d L N)), ∀ (s : ℤˣ) (P X' Y' : Finset (Lam d L N)), Y' ⊆ X' →
    ∀ ℓ : ℝ, 0 < ℓ →
      Tj d (L : ℝ) j ℓ (locOdd s P X' Y' F) ≤ ENNReal.ofReal C * Tj d (L : ℝ) j ℓ F := by
  obtain ⟨Cm, hCm0, hCm⟩ := exists_mass_bound d
  refine ⟨Cm, hCm0, ?_⟩
  intro L _ hL N j hj X hX F hF s P X' Y' hYX ℓ hℓ
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hs : (0 : ℝ) < (L : ℝ) ^ j := by positivity
  set T := (Tj d (L : ℝ) j ℓ F).toReal
  have hm := mass1_le hCm hL hj hX hF s hℓ
  refine (tNorm_le (A := Cm * T) fun g hg => ?_).trans (le_of_eq ?_)
  · unfold locOdd locGen
    rw [pair_smul, pair_sum, norm_mul]
    have hsum : ‖∑ z ∈ Y' ∩ P, pair (ψ (z, s)) g‖ ≤ (Y' ∩ P).card * ℓ := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ z ∈ Y' ∩ P, ‖pair (ψ (z, s)) g‖ ≤ ∑ _z ∈ Y' ∩ P, ℓ :=
            sum_le_sum fun z _ => norm_pair_ψ_le hs hℓ hg _
        _ = (Y' ∩ P).card * ℓ := by rw [sum_const, nsmul_eq_mul]
    calc ‖mass1 s F / ((X' ∩ P).card : ℂ)‖ * ‖∑ z ∈ Y' ∩ P, pair (ψ (z, s)) g‖
        ≤ ‖mass1 s F / ((X' ∩ P).card : ℂ)‖ * ((Y' ∩ P).card * ℓ) := by gcongr
      _ ≤ ‖mass1 s F‖ * ℓ := norm_div_card_mul_le _ (card_inter_le hYX) hℓ.le
      _ ≤ Cm * ℓ⁻¹ * T * ℓ := by gcongr
      _ = Cm * T := by field_simp
  · rw [ENNReal.ofReal_mul hCm0, ENNReal.ofReal_toReal (tNorm_ne_top hs hℓ F)]

/-- `‖locEven P X' Y' F‖ ≤ C ‖F‖` for `F ∈ 𝒩(X^□)`, `X` small, and any `Y' ⊆ X'`. -/
theorem locEven_pt_bound (d : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℕ) [NeZero L],
    2 ^ (d + 3) + 8 * d < L → ∀ N j : ℕ, j < N → ∀ X : Finset (Lam d L N), IsSmall j X →
    ∀ F ∈ NX (nbhd j X : Set (Lam d L N)), ∀ (P X' Y' : Finset (Lam d L N)), Y' ⊆ X' →
    ∀ ℓ : ℝ, 0 < ℓ →
      Tj d (L : ℝ) j ℓ (locEven P X' Y' F) ≤ ENNReal.ofReal C * Tj d (L : ℝ) j ℓ F := by
  obtain ⟨Cm, hCm0, hCm⟩ := exists_mass_bound d
  refine ⟨1 + 2 * Cm ^ 2, by positivity, ?_⟩
  intro L _ hL N j hj X hX F hF P X' Y' hYX ℓ hℓ
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hs : (0 : ℝ) < (L : ℝ) ^ j := by positivity
  set T := (Tj d (L : ℝ) j ℓ F).toReal
  have hm := mass2_le hCm hL hj hX hF hℓ
  have he : ‖ε F‖ ≤ T := abs_eps_le hs hℓ F
  refine (tNorm_le (A := (1 + 2 * Cm ^ 2) * T) fun g hg => ?_).trans (le_of_eq ?_)
  · unfold locEven
    rw [locGen_one, locGen, pair_add, pair_smul, pair_smul, pair_sum]
    have hsum : ‖∑ z ∈ Y' ∩ P, pair (pbp z) g‖ ≤ (Y' ∩ P).card * ℓ ^ 2 := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ z ∈ Y' ∩ P, ‖pair (pbp z) g‖ ≤ ∑ _z ∈ Y' ∩ P, ℓ ^ 2 :=
            sum_le_sum fun z _ => norm_pair_pbp_le hs hℓ hg z
        _ = (Y' ∩ P).card * ℓ ^ 2 := by rw [sum_const, nsmul_eq_mul]
    have h1 := norm_pair_one_le hs hℓ hg
    have hA : ‖ε F / ((X' ∩ P).card : ℂ) * ((Y' ∩ P).card : ℂ) * pair (1 : Alg d L N) g‖ ≤ T := by
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      calc ‖ε F / ((X' ∩ P).card : ℂ)‖ * ((Y' ∩ P).card : ℝ) * ‖pair (1 : Alg d L N) g‖
          ≤ ‖ε F / ((X' ∩ P).card : ℂ)‖ * ((Y' ∩ P).card * 1) * 1 := by gcongr; rw [mul_one]
        _ ≤ ‖ε F‖ * 1 := by
            rw [mul_one]; exact norm_div_card_mul_le _ (card_inter_le hYX) zero_le_one
        _ ≤ T := by rw [mul_one]; exact he
    have hB : ‖mass2 F / ((X' ∩ P).card : ℂ) * ∑ z ∈ Y' ∩ P, pair (pbp z) g‖ ≤ 2 * Cm ^ 2 * T := by
      rw [norm_mul]
      calc ‖mass2 F / ((X' ∩ P).card : ℂ)‖ * ‖∑ z ∈ Y' ∩ P, pair (pbp z) g‖
          ≤ ‖mass2 F / ((X' ∩ P).card : ℂ)‖ * ((Y' ∩ P).card * ℓ ^ 2) := by gcongr
        _ ≤ ‖mass2 F‖ * ℓ ^ 2 := norm_div_card_mul_le _ (card_inter_le hYX) (by positivity)
        _ ≤ 2 * Cm ^ 2 * ℓ⁻¹ ^ 2 * T * ℓ ^ 2 := by gcongr
        _ = 2 * Cm ^ 2 * T := by field_simp
    refine (norm_add_le _ _).trans ((add_le_add hA hB).trans (le_of_eq ?_))
    ring
  · rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal (tNorm_ne_top hs hℓ F)]

theorem norm_card_div_le {X Y : Finset (Lam d L N)} (hYX : Y ⊆ X) :
    ‖((Y.card : ℂ) / (X.card : ℂ))‖ ≤ 1 := by
  rw [norm_div, Complex.norm_natCast, Complex.norm_natCast]
  exact div_le_one_of_le₀ (Nat.cast_le.2 (card_le_card hYX)) (Nat.cast_nonneg _)

theorem Tj_card_smul_le {j : ℕ} {ℓ : ℝ} {X Y : Finset (Lam d L N)} (hYX : Y ⊆ X) (G : Alg d L N) :
    Tj d (L : ℝ) j ℓ (((Y.card : ℂ) / (X.card : ℂ)) • G) ≤ Tj d (L : ℝ) j ℓ G := by
  refine (tNorm_smul_le _ G).trans ?_
  calc ENNReal.ofReal ‖((Y.card : ℂ) / (X.card : ℂ))‖ * Tj d (L : ℝ) j ℓ G
      ≤ ENNReal.ofReal 1 * Tj d (L : ℝ) j ℓ G :=
        mul_le_mul_right' (ENNReal.ofReal_le_ofReal (norm_card_div_le hYX)) _
    _ = Tj d (L : ℝ) j ℓ G := by rw [ENNReal.ofReal_one, one_mul]

/-- **The pointed `loc^a`, `loc^b` are bounded**: `‖loc^a_{X,Y} F‖_{T_j(ℓ)} ≤ C ‖F‖_{T_j(ℓ)}` for
`X` small, `Y ⊆ X`, `F ∈ 𝒩(X^□)` (both for `a ∈ X` and `a ∉ X`). -/
theorem locAp_bound (d : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℕ) [NeZero L],
    2 ^ (d + 3) + 8 * d < L → ∀ N j : ℕ, j < N → ∀ X Y : Finset (Lam d L N), IsSmall j X →
    Y ⊆ X → ∀ F ∈ NX (nbhd j X : Set (Lam d L N)), ∀ (c : Obs.Case) (a : Lam d L N),
    ∀ ℓ : ℝ, 0 < ℓ →
      Tj d (L : ℝ) j ℓ (locAp c a X Y F) ≤ ENNReal.ofReal C * Tj d (L : ℝ) j ℓ F ∧
      Tj d (L : ℝ) j ℓ (locBp c a X Y F) ≤ ENNReal.ofReal C * Tj d (L : ℝ) j ℓ F := by
  obtain ⟨C0, hC0, h0⟩ := locA_bound d
  obtain ⟨C1, hC1, h1⟩ := locOdd_pt_bound d
  obtain ⟨C2, hC2, h2⟩ := locEven_pt_bound d
  refine ⟨C0 + C1 + C2, by positivity, fun L _ hL N j hj X Y hX hYX F hF c a ℓ hℓ => ?_⟩
  have e0 : ENNReal.ofReal C0 ≤ ENNReal.ofReal (C0 + C1 + C2) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  have e1 : ENNReal.ofReal C1 ≤ ENNReal.ofReal (C0 + C1 + C2) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  have e2 : ENNReal.ofReal C2 ≤ ENNReal.ofReal (C0 + C1 + C2) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  have hpt : ∀ G : Alg d L N, Tj d (L : ℝ) j ℓ (locA c.toObs a {a} {a} G) ≤
      ENNReal.ofReal (C0 + C1 + C2) * Tj d (L : ℝ) j ℓ F → Tj d (L : ℝ) j ℓ
        (((Y.card : ℂ) / (X.card : ℂ)) • locA c.toObs a {a} {a} G) ≤
      ENNReal.ofReal (C0 + C1 + C2) * Tj d (L : ℝ) j ℓ F := fun G hG =>
    (Tj_card_smul_le hYX _).trans hG
  have hptB : ∀ G : Alg d L N, Tj d (L : ℝ) j ℓ (locB c.toObs a {a} {a} G) ≤
      ENNReal.ofReal (C0 + C1 + C2) * Tj d (L : ℝ) j ℓ F → Tj d (L : ℝ) j ℓ
        (((Y.card : ℂ) / (X.card : ℂ)) • locB c.toObs a {a} {a} G) ≤
      ENNReal.ofReal (C0 + C1 + C2) * Tj d (L : ℝ) j ℓ F := fun G hG =>
    (Tj_card_smul_le hYX _).trans hG
  have hA : Tj d (L : ℝ) j ℓ (locA c.toObs a {a} {a} F) ≤
      ENNReal.ofReal (C0 + C1 + C2) * Tj d (L : ℝ) j ℓ F ∧
      Tj d (L : ℝ) j ℓ (locB c.toObs a {a} {a} F) ≤
      ENNReal.ofReal (C0 + C1 + C2) * Tj d (L : ℝ) j ℓ F := by
    cases c
    · exact ⟨(h1 L hL N j hj X hX F hF (-1) {a} {a} {a} subset_rfl ℓ hℓ).trans
        (mul_le_mul_right' e1 _),
        (h1 L hL N j hj X hX F hF 1 {a} {a} {a} subset_rfl ℓ hℓ).trans (mul_le_mul_right' e1 _)⟩
    · exact ⟨(h2 L hL N j hj X hX F hF {a} {a} {a} subset_rfl ℓ hℓ).trans
        (mul_le_mul_right' e2 _),
        (h2 L hL N j hj X hX F hF {a} {a} {a} subset_rfl ℓ hℓ).trans (mul_le_mul_right' e2 _)⟩
  have hB := h0 L hL N j hj X Y hX hYX F hF c.toObs a ℓ hℓ
  by_cases ha : a ∈ X
  · rw [locAp_of_mem Y ha, locBp_of_mem Y ha]
    exact ⟨hB.1.trans (mul_le_mul_right' e0 _), hB.2.trans (mul_le_mul_right' e0 _)⟩
  · rw [locAp_of_not_mem Y ha, locBp_of_not_mem Y ha]
    exact ⟨hpt F hA.1, hptB F hA.2⟩

/-- **The observable part of `Loc` is bounded** (single-source weights; pointed `loc^a`). -/
theorem exists_LocO2_obs_bound (d : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℕ) [NeZero L],
    2 ^ (d + 3) + 8 * d < L → ∀ N : ℕ, ∀ (c : Obs.Case) (P : ObsPts d L N) (w : Wt), w.ab = 0 →
    ∀ k : ℕ, k < N → ∀ ℓ : ℝ, 0 < ℓ → ∀ X Y : Finset (Lam d L N), IsSmall k X → Y ⊆ X →
    ∀ F : OE c (Lam d L N), CmpIn (nbhd k X : Set (Lam d L N)) (F : SA c (Lam d L N)) →
      oTo w k ℓ (LocO2 P X Y F) ≤ ENNReal.ofReal C * oTo w k ℓ F := by
  obtain ⟨C, hC, h⟩ := locAp_bound d
  refine ⟨C, hC, fun L _ hL N c P w hw0 k hk ℓ hℓ X Y hX hYX F hF => ?_⟩
  rw [oTo, oTo]
  refine oNorm_le_cmp3 hw0 ?_ ?_ ?_
  · simp only [coe_πobs, piobs_apply]
    rw [show Tj d (L : ℝ) k ℓ (0 : Alg d L N) = 0 from tNorm_zero']; exact bot_le
  · simp only [coe_πobs, piobs_apply]
    exact (h L hL N k hk X Y hX hYX _ hF.a c P.a ℓ hℓ).1
  · simp only [coe_πobs, piobs_apply]
    exact (h L hL N k hk X Y hX hYX _ hF.b c P.b ℓ hℓ).2

/-- **Locality of `Loc`**: the bulk and single-source components of `Loc_{X,Y} F` lie in
`𝒩(Y^□)` provided each source point is in `X` or the corresponding component of `F` vanishes.
(For `p_i ∉ X` the pointed `loc^{p_i}` puts the component at the point `p_i`, which need not lie in
`Y^□`; see `LocO2_cmpIn_pts`.) -/
theorem LocO2_cmpIn (hd : 1 ≤ d) {c : Obs.Case} (P : ObsPts d L N) {j : ℕ}
    (X : Finset (Lam d L N)) {Y : Finset (Lam d L N)} (hY : IsPolymer j Y) (F : OE c (Lam d L N))
    (ha : P.a ∈ X ∨ (F : SA c (Lam d L N)).a = 0) (hb : P.b ∈ X ∨ (F : SA c (Lam d L N)).b = 0) :
    CmpIn (nbhd j Y : Set (Lam d L N)) (LocO2 P X Y F : SA c (Lam d L N)) := by
  refine ⟨Step2.Loc2XY_mem' hd hY X _, ?_, ?_⟩
  · show locAp c P.a X Y (F : SA c (Lam d L N)).a ∈ _
    rcases ha with haX | h0
    · rw [locAp_of_mem Y haX]
      by_cases ha : P.a ∈ Y
      · exact NX_mono (by
          intro z hz; rw [Set.mem_singleton_iff.1 hz]; exact subset_nbhd hY ha) (locA_mem _ _ _ _)
      · rw [locA_eq_zero _ ha]; exact zero_mem _
    · rw [h0, locAp_zero]; exact zero_mem _
  · show locBp c P.b X Y (F : SA c (Lam d L N)).b ∈ _
    rcases hb with hbX | h0
    · rw [locBp_of_mem Y hbX]
      by_cases hb : P.b ∈ Y
      · exact NX_mono (by
          intro z hz; rw [Set.mem_singleton_iff.1 hz]; exact subset_nbhd hY hb) (locB_mem _ _ _ _)
      · rw [locB_eq_zero _ hb]; exact zero_mem _
    · rw [h0, locBp_zero]; exact zero_mem _

/-- **Locality of `Loc` with the source points**: the bulk and single-source components of
`Loc_{X,Y} F` lie in `𝒩(Y^□ ∪ {a, b})`. -/
theorem LocO2_cmpIn_pts (hd : 1 ≤ d) {c : Obs.Case} (P : ObsPts d L N) {j : ℕ}
    (X : Finset (Lam d L N)) {Y : Finset (Lam d L N)} (hY : IsPolymer j Y) (F : OE c (Lam d L N)) :
    CmpIn ((nbhd j Y : Set (Lam d L N)) ∪ {P.a, P.b}) (LocO2 P X Y F : SA c (Lam d L N)) := by
  refine ⟨NX_mono Set.subset_union_left (Step2.Loc2XY_mem' hd hY X _), ?_, ?_⟩
  · exact NX_mono (by
      intro z hz; rw [Set.mem_singleton_iff.1 hz]; exact Or.inr (Or.inl rfl)) (locAp_mem _ _ _ _)
  · exact NX_mono (by
      intro z hz; rw [Set.mem_singleton_iff.1 hz]; exact Or.inr (Or.inr rfl)) (locBp_mem _ _ _ _)

theorem single_inter_nonempty (a : Lam d L N) : (({a} : Finset (Lam d L N)) ∩ {a}).Nonempty :=
  ⟨a, by simp⟩

theorem single_inter_sub_nbhd {j : ℕ} {X : Finset (Lam d L N)} {a : Lam d L N}
    (ha : a ∈ nbhd j X) :
    (((({a} : Finset (Lam d L N)) ∩ {a} : Finset (Lam d L N))) : Set (Lam d L N)) ⊆
      (nbhd j X : Set (Lam d L N)) := by
  intro z hz
  have : z = a := by simpa using hz
  rw [this]; exact ha

/-- **The pointed `loc^a` contracts (odd components)**: for `X` small, `a ∈ X^□` (not
necessarily in `X`), `F ∈ 𝒩(X^□)` of charge `-s` and `ℓ' ≤ 2ℓ`,
`‖F - m_s(F) ψ_{(a,s)}‖_{T_{j+1}(ℓ')} ≤ C L^{-1} ‖F‖_{T_j(ℓ)}`
(`locOdd s {a} {a} {a} F = m_s(F) ψ_{(a,s)}`). -/
theorem exists_odd_contract_pt (d : ℕ) (hd : 1 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧ ∃ L₀ : ℕ,
    ∀ (L : ℕ) [NeZero L], 2 ^ (d + 3) + 8 * d < L → L₀ ≤ L → ∀ N j : ℕ, j < N →
    ∀ ℓ ℓ' : ℝ, 0 < ℓ → 0 < ℓ' → ℓ' ≤ 2 * ℓ →
    ∀ X : Finset (Lam d L N), IsSmall j X → ∀ (s : ℤˣ) (a : Lam d L N), a ∈ nbhd j X →
    ∀ F ∈ NX (nbhd j X : Set (Lam d L N)), HasCharge (-(s : ℤ)) F →
      Tj d (L : ℝ) (j + 1) ℓ' (F - locOdd s {a} {a} {a} F) ≤
        ENNReal.ofReal (C / L) * Tj d (L : ℝ) j ℓ F := by
  obtain ⟨Cb, hCb0, hCb⟩ := locOdd_pt_bound d
  obtain ⟨Cc, hCc0, L₀, hCc⟩ := exists_core2_bound d 1 hd le_rfl (by norm_num)
  refine ⟨Cc * (2 + Cb), by positivity, L₀, ?_⟩
  intro L _ hL hL₀ N j hj ℓ ℓ' hℓ hℓ' hℓℓ X hX s a ha F hF hFc
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hs : (0 : ℝ) < (L : ℝ) ^ j := by positivity
  have hP := single_inter_nonempty a
  set G := F - locOdd s {a} {a} {a} F
  have hGmem : G ∈ NX (nbhd j X : Set (Lam d L N)) :=
    sub_mem hF (NX_mono (single_inter_sub_nbhd ha) (locOdd_mem s {a} {a} {a} F))
  have hTG := tNorm_sub_loc_le hs hℓ hCb0 (hCb L hL N j hj X hX F hF s {a} {a} {a} subset_rfl ℓ hℓ)
  have hGm : ∀ σ : Fin 1 → ℤˣ, ∑ x : Fin 1 → Lam d L N, coeff G (fun k => (x k, σ k)) = 0 := by
    intro σ
    rw [sum_seq_one, mass1_sub]
    by_cases hσ : σ 0 = s
    · rw [hσ, mass1_locOdd hP, sub_self]
    · rw [mass1_locOdd_ne s (σ 0) hσ, sub_zero]
      refine sum_eq_zero fun y _ => hFc 1 _ ?_
      rw [charge_single]
      intro h
      exact hσ (Units.ext (neg_inj.1 h))
  have hG0 : ∀ (n : ℕ) (z : Fin n → Sf (Lam d L N)), n ≠ 1 → n < 3 → coeff G z = 0 := by
    intro n z hn1 hn3
    rw [LocObs.coeff_sub', coeff_locOdd_of_ne s _ _ _ F z hn1, sub_zero]
    refine hFc n z fun h => ?_
    have h2 := charge_add z
    rcases units_val_eq s with h1 | h1 <;> rw [h1] at h <;> omega
  have hGF : ∀ (n : ℕ) (z : Fin n → Sf (Lam d L N)), 3 ≤ n → coeff G z = coeff F z := by
    intro n z hn
    rw [LocObs.coeff_sub', coeff_locOdd_of_ne s _ _ _ F z (by omega), sub_zero]
  have hc := hCc L hL hL₀ N j hj X hX F hF G hGmem hGm hG0 hGF ℓ ℓ' hℓ hℓ' hℓℓ
  exact contract_of_core hs hℓ hCc0 hCb0 hc hTG

/-- **The pointed `loc^a` contracts (even, `U(1)`-invariant components)**: for `X` small,
`a ∈ X^□`, `‖F - ε(F) - m(F) ψ̄_aψ_a‖_{T_{j+1}(ℓ')} ≤ C L^{-1} ‖F‖_{T_j(ℓ)}`
(`locEven {a} {a} {a} F = ε(F) + m(F) ψ̄_aψ_a`). -/
theorem exists_even_contract_pt (d : ℕ) (hd : 1 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧ ∃ L₀ : ℕ,
    ∀ (L : ℕ) [NeZero L], 2 ^ (d + 3) + 8 * d < L → L₀ ≤ L → ∀ N j : ℕ, j < N →
    ∀ ℓ ℓ' : ℝ, 0 < ℓ → 0 < ℓ' → ℓ' ≤ 2 * ℓ →
    ∀ X : Finset (Lam d L N), IsSmall j X → ∀ a : Lam d L N, a ∈ nbhd j X →
    ∀ F ∈ NX (nbhd j X : Set (Lam d L N)), HasCharge 0 F →
      Tj d (L : ℝ) (j + 1) ℓ' (F - locEven {a} {a} {a} F) ≤
        ENNReal.ofReal (C / L) * Tj d (L : ℝ) j ℓ F := by
  obtain ⟨Cb, hCb0, hCb⟩ := locEven_pt_bound d
  obtain ⟨Cc, hCc0, L₀, hCc⟩ := exists_core2_bound d 2 hd (by norm_num) le_rfl
  refine ⟨Cc * (2 + Cb), by positivity, L₀, ?_⟩
  intro L _ hL hL₀ N j hj ℓ ℓ' hℓ hℓ' hℓℓ X hX a ha F hF hFc
  have hsym : IsSym F := (hasCharge_zero_iff F).1 hFc
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hs : (0 : ℝ) < (L : ℝ) ^ j := by positivity
  have hP := single_inter_nonempty a
  set G := F - locEven {a} {a} {a} F
  have hGmem : G ∈ NX (nbhd j X : Set (Lam d L N)) :=
    sub_mem hF (NX_mono (single_inter_sub_nbhd ha) (locEven_mem {a} {a} {a} F))
  have hTG := tNorm_sub_loc_le hs hℓ hCb0 (hCb L hL N j hj X hX F hF {a} {a} {a} subset_rfl ℓ hℓ)
  have hsame : ∀ (x y : Lam d L N) (σ : ℤˣ), coeff G ![(x, σ), (y, σ)] = 0 := fun x y σ => by
    rw [LocObs.coeff_sub', coeff_same_spin_eq_zero hsym, coeff_locEven_same, sub_zero]
  have hmass : mass2 G = 0 := by rw [mass2_sub, mass2_locEven hP, sub_self]
  have hGm : ∀ σ : Fin 2 → ℤˣ, ∑ x : Fin 2 → Lam d L N, coeff G (fun k => (x k, σ k)) = 0 := by
    intro σ
    rw [sum_seq_two]
    rcases Int.units_eq_one_or (σ 0) with h0 | h0 <;>
      rcases Int.units_eq_one_or (σ 1) with h1 | h1 <;> rw [h0, h1]
    · simp only [hsame, sum_const_zero]
    · have e : ∀ x y : Lam d L N, coeff G ![(x, 1), (y, -1)] = -coeff G ![(y, -1), (x, 1)] :=
        fun x y => coeff_swap_two G (y, -1) (x, 1)
      simp only [e, sum_neg_distrib]
      rw [sum_comm]
      have : mass2 G = ∑ y, ∑ x, coeff G ![(y, -1), (x, 1)] := rfl
      rw [← this, hmass, neg_zero]
    · exact hmass
    · simp only [hsame, sum_const_zero]
  have hG0 : ∀ (n : ℕ) (z : Fin n → Sf (Lam d L N)), n ≠ 2 → n < 3 → coeff G z = 0 := by
    intro n z hn2 hn3
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      rw [coeff_elim0, map_sub, eps_locEven hP, sub_self]
    · rw [LocObs.coeff_sub', coeff_locEven_of_ne _ _ _ F z (by omega) hn2, sub_zero]
      exact coeff_eq_zero_of_odd hsym (Nat.odd_iff.2 (by omega)) z
  have hGF : ∀ (n : ℕ) (z : Fin n → Sf (Lam d L N)), 3 ≤ n → coeff G z = coeff F z := by
    intro n z hn
    rw [LocObs.coeff_sub', coeff_locEven_of_ne _ _ _ F z (by omega) (by omega), sub_zero]
  have hc := hCc L hL hL₀ N j hj X hX F hF G hGmem hGm hG0 hGF ℓ ℓ' hℓ hℓ' hℓℓ
  exact contract_of_core hs hℓ hCc0 hCb0 hc hTG

end

end Obs2
