import Spin2.Final.ObsBeta1

set_option autoImplicit false

/-!
# The observable renormalisation condition: existence of `β_N` and the finite-`N` theorem

For `t ≥ t₀` the equation `obsBeta L N β = t` is solved by the intermediate value theorem on the
union of the four brackets at `β_R = t4^i/8`, `i = 0, …, 3` (mass `obsMass L N t = 1/(32tL^{2N})`,
so that `4m²L^{2N} = 1/(8t) ≤ 1/β_R` for all four). Consecutive brackets share an endpoint
(`1/(2β_R) = 2/(4β_R)`), so the union is the interval `[a_4, a_0]`, `a_i = bFin(2/(t4^i/8))`
(`obs_union`). At the left end (bracket at `8t`) `obsBeta ≥ β̃_{N−2} − 3K ≥ 2t − 3K > t`, at the
right end (bracket at `t/8`) `obsBeta ≤ 5t/8 + 3K < t` (`ob_obsBeta_close`, `ArbScale`).

* `MasterFacts.obsA`, `obs_bracket_eq`, `obs_union`: the union of the brackets.
* `MasterFacts.ob_perM`: `arb_perN` plus `|obsBeta(1/b) − β̃_{N−2}| ≤ 3K` on every bracket.
* `ObsScale`: the conclusions of `ArbScale` with `t` in place of `β_R` and `|β̃_{N−2} − t| ≤ K`.
* `MasterFacts.ob_master`: constants depending on `L` only; for `t ≥ t₀`, `N ≥ N₀` there is
  `b > 0` in one of the four brackets with `obsBeta L N (1/b) = t`, `ObsScale` and `ArbShort`
  (at `t`).
* **`thm_arboreal_obs`**: the finite-`N` theorem with the observable renormalisation condition.
-/

namespace Spin2

open Step Step2 PtCorr2 Cont Loc Grassmann Step2.D2

noncomputable section

open Finset Flow2 Flow2.Hist Set Filter Topology

variable {L : ℕ} [NeZero L]

/-! ### `ObsScale` -/

variable (L) in
/-- **The conclusions of `thm:beta`/`thm:multiscale` with the observable coupling `t`**: for
`β_ε` and a sequence `β_j` (`j ≤ N − 2`): `β_0 = β_ε > 0`; `|β_ε − Nβ₁ log L| ≤ K_ε(1 + t + log N)`;
for `j ≤ N − 2`, `β_j ≥ t/32` and
`|β_j − (N−2−j)β₁ log L| ≤ (40t + E) + a log(2((N−2−j)β₁ log L + 40t + E + a|log 2a|))`;
`|β_{N−2} − t| ≤ K`; and for every `x ≠ 0`, with `ℓ = |x|/L^N`, `λ = log(1/ℓ)`, `j_p = j(ℓ)`,
`k = min(j_p, N − 2)`: `|β_k − β₁λ| ≤ K_c(1 + t + log(1 + λ))` and
`|P_{β_ε}[0 ↔ x] − ϑ_k²| ≤ Kϑ_k²/β_k` with `ϑ_k² = (β_k/β_ε)^{2/3}`. -/
def ObsScale (N : ℕ) (t K Kc Kε E a βε : ℝ) (β : ℕ → ℝ) : Prop :=
  0 < βε ∧ β 0 = βε ∧
  |βε - N * betaL L| ≤ Kε * (1 + t + Real.log N) ∧
  (∀ j ≤ N - 2, t / 32 ≤ β j ∧
    |β j - ((N - 2 - j : ℕ) : ℝ) * betaL L| ≤
      (40 * t + E) + a * Real.log (2 * (((N - 2 - j : ℕ) : ℝ) * betaL L + (40 * t + E) +
        a * |Real.log (2 * a)|))) ∧
  |β (N - 2) - t| ≤ K ∧
  ∀ x : Lam 2 L N, x ≠ 0 → ∃ jp : ℕ, (jp : ℤ) = jPhys L N (eucl x / (L : ℝ) ^ N) ∧
    |β (min jp (N - 2)) - betaOne * Real.log (1 / (eucl x / (L : ℝ) ^ N))| ≤
      Kc * (1 + t + Real.log (1 + Real.log (1 / (eucl x / (L : ℝ) ^ N)))) ∧
    |Pconn L N βε x - (β (min jp (N - 2)) / βε) ^ (2 / 3 : ℝ)| ≤
      K * (β (min jp (N - 2)) / βε) ^ (2 / 3 : ℝ) / β (min jp (N - 2))

/-- **`ObsScale` from `ArbScale` at `β_R ∈ [t/8, 8t]`** and `|β_{N−2} − t| ≤ 3K`. -/
theorem obsScale_of (hL : 2 ≤ L) {N : ℕ} (hN : 1 ≤ N) {t βR K Kc Kε E a βε : ℝ} {β : ℕ → ℝ}
    (ht : 0 < t) (hβR : t / 8 ≤ βR) (hβR' : βR ≤ 8 * t) (hK : 0 ≤ K) (hKc : 0 < Kc)
    (hKε : 0 ≤ Kε) (hE : 0 ≤ E) (ha : 0 ≤ a)
    (h : ArbScale L N βR K Kc Kε E a βε β) (hclose : |β (N - 2) - t| ≤ 3 * K)
    (hlam : ∀ x : Lam 2 L N, x ≠ 0 → 0 < Real.log (1 / (eucl x / (L : ℝ) ^ N))) :
    ObsScale L N t (3 * K) (8 * Kc) (8 * Kε) E a βε β := by
  obtain ⟨h1, h2, h3, h4, -, h6⟩ := h
  have hβL := ct_betaL_pos hL
  have hβR0 : 0 < βR := by linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  refine ⟨h1, h2, ?_, fun j hj => ?_, hclose, fun x hx => ?_⟩
  · refine h3.trans ?_
    have := mul_le_mul_of_nonneg_left
      (show 1 + βR + Real.log N ≤ 8 * (1 + t + Real.log N) by linarith) hKε
    linarith
  · obtain ⟨hj1, hj2⟩ := h4 j hj
    refine ⟨by linarith, hj2.trans ?_⟩
    have hc : 0 ≤ ((N - 2 - j : ℕ) : ℝ) * betaL L := by positivity
    have hd : 0 ≤ a * |Real.log (2 * a)| := by positivity
    have hlog : Real.log (2 * (((N - 2 - j : ℕ) : ℝ) * betaL L + (5 * βR + E) +
        a * |Real.log (2 * a)|)) ≤ Real.log (2 * (((N - 2 - j : ℕ) : ℝ) * betaL L + (40 * t + E) +
        a * |Real.log (2 * a)|)) :=
      Real.log_le_log (by positivity) (by linarith)
    have := mul_le_mul_of_nonneg_left hlog ha
    linarith
  · obtain ⟨jp, hj, hbl, hP⟩ := h6 x hx
    have hl := hlam x hx
    have hlog0 : 0 ≤ Real.log (1 + Real.log (1 / (eucl x / (L : ℝ) ^ N))) :=
      Real.log_nonneg (by linarith)
    refine ⟨jp, hj, hbl.trans ?_, hP.trans ?_⟩
    · have := mul_le_mul_of_nonneg_left
        (show 1 + βR + Real.log (1 + Real.log (1 / (eucl x / (L : ℝ) ^ N))) ≤
          8 * (1 + t + Real.log (1 + Real.log (1 / (eucl x / (L : ℝ) ^ N)))) by linarith) hKc.le
      linarith
    · have hβk : 0 < β (min jp (N - 2)) := by
        linarith [(h4 (min jp (N - 2)) (min_le_right _ _)).1]
      have : 0 ≤ (β (min jp (N - 2)) / βε) ^ (2 / 3 : ℝ) / β (min jp (N - 2)) := by positivity
      rw [mul_div_assoc, mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (by linarith) this

/-! ### The per-`M` core -/

namespace MasterFacts

variable (M : MasterFacts L)

/-- The endpoints `a_i = bFin(2/(t4^i/8))` of the brackets at `obsBR t i`, mass `obsMass`. -/
def obsA (N : ℕ) (t : ℝ) (i : ℕ) : ℝ :=
  bFin (a5wR M N) M.core.κ M.core.cm M.core.cT (N - 2) M.core.ε (obsMass L N t) (2 / obsBR t i)

/-- The bracket at `obsBR t i` is `[a_{i+1}, a_i]`. -/
theorem obs_bracket_eq (N : ℕ) {t : ℝ} (ht : 0 < t) (i : ℕ) :
    ctBracket M (a5wR M N) (obsMass L N t) (obsBR t i) = Icc (M.obsA N t (i + 1)) (M.obsA N t i) := by
  show Set.Icc _ _ = Set.Icc _ _
  unfold obsA
  rw [obsBR_succ ht i]

/-- **The union of the four brackets is `[a_4, a_0]`**: for `N ≥ 2`, `t ≥ 1`, `4/ε ≤ t/8`: the
`a_i` are positive and decreasing, and every `b ∈ [a_4, a_0]` lies in a bracket at `obsBR t i`,
`i ≤ 3`. -/
theorem obs_union {N : ℕ} (hN : 2 ≤ N) {t : ℝ} (ht : 1 ≤ t) (hε : 4 / M.core.ε ≤ t / 8) :
    (∀ i ≤ 4, 0 < M.obsA N t i) ∧ (∀ i ≤ 3, M.obsA N t (i + 1) ≤ M.obsA N t i) ∧
    ∀ b ∈ Icc (M.obsA N t 4) (M.obsA N t 0),
      ∃ i ≤ 3, b ∈ ctBracket M (a5wR M N) (obsMass L N t) (obsBR t i) := by
  have ht0 : 0 < t := by linarith
  obtain ⟨hm0, hm1, -⟩ := obsMass_spec (L := L) N ht
  have hmR : obsMass L N t ∈ mRange L N :=
    fin_mRange (by exact_mod_cast M.ct_L2) (by omega) hm0 hm1
  have hbr : ∀ i ≤ 3, 0 < M.obsA N t (i + 1) ∧ M.obsA N t (i + 1) ≤ M.obsA N t i := by
    intro i hi
    have h := M.arb_bracket_left hN hmR (hε.trans (obsBR_ge ht0 i))
    rw [obs_bracket_eq M N ht0 i] at h
    unfold obsA
    rw [← obsBR_succ ht0 i]
    exact ⟨h.1, h.2.2⟩
  refine ⟨fun i hi => ?_, fun i hi => (hbr i hi).2, fun b hb => ?_⟩
  · rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact lt_of_lt_of_le (hbr 0 (by norm_num)).1 (hbr 0 (by norm_num)).2
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      exact (hbr i' (by omega)).1
  · obtain ⟨hb4, hb0⟩ := hb
    have h0 := (hbr 0 (by norm_num)).2
    have h1 := (hbr 1 (by norm_num)).2
    have h2 := (hbr 2 (by norm_num)).2
    have h3 := (hbr 3 (by norm_num)).2
    simp only [obs_bracket_eq M N ht0]
    rcases le_or_gt b (M.obsA N t 3) with c3 | c3
    · exact ⟨3, le_rfl, hb4, c3⟩
    rcases le_or_gt b (M.obsA N t 2) with c2 | c2
    · exact ⟨2, by norm_num, c3.le, c2⟩
    rcases le_or_gt b (M.obsA N t 1) with c1 | c1
    · exact ⟨1, by norm_num, c2.le, c1⟩
    exact ⟨0, by norm_num, c1.le, hb0⟩

set_option maxHeartbeats 1000000 in
/-- **`arb_perN` with `obsBeta ≈ β̃_{N−2}`**: constants (`K, K_ε ≥ 0`) and, on every bracket,
`ArbScale`, `ArbShort` and `|obsBeta L N (1/b) − β̃_{N−2}| ≤ 3K` for `β_R ≥ 16K`. -/
theorem ob_perM : ∃ (g₀ K Ks Kc Kε E a : ℝ) (N₀ : ℕ), 0 < g₀ ∧ 0 ≤ K ∧ 0 ≤ E ∧ 0 ≤ a ∧
    0 < Kc ∧ 0 ≤ Kε ∧ 3 ≤ N₀ ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → N₀ ≤ N →
    ∀ m βR : ℝ, 0 < m → 0 < βR → 4 * (m * (L : ℝ) ^ (2 * N)) ≤ 1 / βR → 1 / βR ≤ g₀ →
    ∀ b ∈ ctBracket M R m βR,
      ArbScale L N βR K Kc Kε E a (1 / b) (betaJ R m b (b - m)) ∧
      ArbShort L N βR Ks Kc (1 / b) ∧
      (16 * K ≤ βR → |obsBeta L N (1 / b) - betaJ R m b (b - m) (N - 2)| ≤ 3 * K) := by
  obtain ⟨g₀, K, Ks, Kc, Kε, E, a, N₀, hg, hE, ha, hKc, hN₀, hF⟩ := M.arb_perN
  have hL2 := M.ct_L2
  refine ⟨g₀, |K|, Ks, Kc, |Kε|, E, a, N₀, hg, abs_nonneg _, hE, ha, hKc, abs_nonneg _, hN₀,
    fun N R _ _ hP hi0 hRℓ hRA hRρ hN m βR hm hβR hmass hy b hb => ?_⟩
  obtain ⟨hS, hSh⟩ := hF N R hP hi0 hRℓ hRA hRρ hN m βR hm hβR hmass hy b hb
  have hS' := hS.mono (by omega) hβR (le_abs_self K) (le_abs_self Kε)
  refine ⟨hS', hSh, fun h16 => ?_⟩
  obtain ⟨h1, -, -, h4, -, h6⟩ := hS'
  have hb0 : 0 < b := one_div_pos.1 h1
  obtain ⟨hne, hfar⟩ := obsX0N_far hL2 (show 1 ≤ N by omega)
  obtain ⟨jp, hj, -, hP⟩ := h6 (obsX0N L N) hne
  rw [obs_min_eq hL2 hfar hj] at hP
  have hβ := (h4 (N - 2) le_rfl).1
  exact ob_obsBeta_close hb0 (abs_nonneg _) (by linarith) (by linarith) hP

set_option maxHeartbeats 1000000 in
/-- **The master statement for the observable renormalisation condition** (constants depending on
`L` only): for `t ≥ t₀` the four couplings `obsBR t i` satisfy `4/ε ≤ t/8`, and for every
`N ≥ N₀` there is `b > 0` in a bracket at some `obsBR t i` (`i ≤ 3`, mass `obsMass L N t`) with
`obsBeta L N (1/b) = t`, `ObsScale` and `ArbShort` at `t`. -/
theorem ob_master : ∃ (K Ks Kc Kε E a t₀ : ℝ) (N₀ : ℕ), 0 ≤ K ∧ 0 ≤ E ∧ 0 ≤ a ∧ 0 < Kc ∧
    0 ≤ Kε ∧ 1 ≤ t₀ ∧ 3 ≤ N₀ ∧
    ∀ t : ℝ, t₀ ≤ t → 4 / M.core.ε ≤ t / 8 ∧
      ∀ N : ℕ, N₀ ≤ N → ∃ b : ℝ, 0 < b ∧ obsBeta L N (1 / b) = t ∧
        (∃ i ≤ 3, b ∈ ctBracket M (a5wR M N) (obsMass L N t) (obsBR t i)) ∧
        ∃ β : ℕ → ℝ, ObsScale L N t K Kc Kε E a (1 / b) β ∧ ArbShort L N t Ks Kc (1 / b) := by
  obtain ⟨g₀, K, Ks, Kc, Kε, E, a, N₀, hg, hK, hE, ha, hKc, hKε, hN₀, hF⟩ := M.ob_perM
  have hL2 := M.ct_L2
  obtain ⟨-, -, -, hε, -⟩ := M.core.hC2
  refine ⟨3 * K, Ks, 8 * Kc, 8 * Kε, E, a, 8 / g₀ + 32 / M.core.ε + 128 * K + 1, N₀,
    by positivity, hE, ha, by positivity, by positivity, by
      have : 0 ≤ 8 / g₀ + 32 / M.core.ε + 128 * K := by positivity
      linarith, hN₀, fun t ht => ?_⟩
  have h1 : 0 ≤ 8 / g₀ := by positivity
  have h2 : 0 ≤ 32 / M.core.ε := by positivity
  have h3 : 0 ≤ 128 * K := by positivity
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hεt : 4 / M.core.ε ≤ t / 8 := by
    have : 32 / M.core.ε ≤ t := by linarith
    rw [div_le_iff₀ hε] at this ⊢
    linarith
  refine ⟨hεt, fun N hN => ?_⟩
  -- the brackets at `obsBR t i`
  obtain ⟨hm0, hm1, hwin⟩ := obsMass_spec (L := L) N ht1
  have hgi : ∀ i ≤ 3, 1 / obsBR t i ≤ g₀ := fun i hi => by
    have h8 : 8 / g₀ ≤ t := by linarith
    rw [div_le_iff₀ hg] at h8
    have := obsBR_ge ht0 i
    rw [div_le_iff₀ (obsBR_pos ht0 i)]
    nlinarith
  have hKi : ∀ i, 16 * K ≤ obsBR t i := fun i => by
    have := obsBR_ge ht0 i; linarith
  have hbr : ∀ i ≤ 3, ∀ b ∈ ctBracket M (a5wR M N) (obsMass L N t) (obsBR t i),
      ArbScale L N (obsBR t i) K Kc Kε E a (1 / b) (betaJ (a5wR M N) (obsMass L N t) b (b - obsMass L N t)) ∧
      ArbShort L N (obsBR t i) Ks Kc (1 / b) ∧
      |obsBeta L N (1 / b) - betaJ (a5wR M N) (obsMass L N t) b (b - obsMass L N t) (N - 2)| ≤ 3 * K :=
    fun i hi b hb => by
      obtain ⟨hS, hSh, hcl⟩ := hF N (a5wR M N) rfl rfl rfl rfl rfl hN (obsMass L N t) (obsBR t i)
        hm0 (obsBR_pos ht0 i) (hwin i hi) (hgi i hi) b hb
      exact ⟨hS, hSh, hcl (hKi i)⟩
  -- the union and the intermediate value theorem
  obtain ⟨hpos, hmono, hcov⟩ := M.obs_union (show 2 ≤ N by omega) ht1 hεt
  have h40 : M.obsA N t 4 ≤ M.obsA N t 0 :=
    (hmono 3 (by norm_num)).trans ((hmono 2 (by norm_num)).trans
      ((hmono 1 (by norm_num)).trans (hmono 0 (by norm_num))))
  have ha4 := hpos 4 le_rfl
  have hcont : ContinuousOn (fun b => obsBeta L N (1 / b)) (Icc (M.obsA N t 4) (M.obsA N t 0)) := by
    have hne : ∀ b ∈ Icc (M.obsA N t 4) (M.obsA N t 0), b ≠ 0 :=
      fun b hb => (ha4.trans_le hb.1).ne'
    refine ContinuousOn.mul (continuousOn_const.div continuousOn_id hne) ?_
    refine (Real.continuous_rpow_const (by norm_num)).comp_continuousOn ?_
    refine (Pconn_continuousOn (obsX0N L N)).comp (continuousOn_const.div continuousOn_id hne) ?_
    intro b hb
    exact (one_div_pos.2 (ha4.trans_le hb.1)).le
  have hleft : t ≤ obsBeta L N (1 / M.obsA N t 4) := by
    have hmem : M.obsA N t 4 ∈ ctBracket M (a5wR M N) (obsMass L N t) (obsBR t 3) := by
      rw [obs_bracket_eq M N ht0 3]; exact ⟨le_rfl, hmono 3 (by norm_num)⟩
    obtain ⟨⟨-, -, -, h4, -, -⟩, -, hcl⟩ := hbr 3 (by norm_num) _ hmem
    have := (h4 (N - 2) le_rfl).1
    rw [obsBR_three] at this
    linarith [(abs_le.1 hcl).1]
  have hright : obsBeta L N (1 / M.obsA N t 0) ≤ t := by
    have hmem : M.obsA N t 0 ∈ ctBracket M (a5wR M N) (obsMass L N t) (obsBR t 0) := by
      rw [obs_bracket_eq M N ht0 0]; exact ⟨hmono 0 (by norm_num), le_rfl⟩
    obtain ⟨⟨-, -, -, -, h5, -⟩, -, hcl⟩ := hbr 0 (by norm_num) _ hmem
    rw [obsBR_zero] at h5
    linarith [(abs_le.1 hcl).2]
  obtain ⟨b, hb, hΦ⟩ := intermediate_value_Icc' h40 hcont ⟨hright, hleft⟩
  have hΦ : obsBeta L N (1 / b) = t := hΦ
  obtain ⟨i, hi, hbi⟩ := hcov b hb
  have hb0 : 0 < b := ha4.trans_le hb.1
  obtain ⟨hS, hSh, hcl⟩ := hbr i hi b hbi
  refine ⟨b, hb0, hΦ, ⟨i, hi, hbi⟩, betaJ (a5wR M N) (obsMass L N t) b (b - obsMass L N t), ?_, ?_⟩
  · refine obsScale_of hL2 (by omega) ht0 (obsBR_ge ht0 i) (obsBR_le ht0 hi) hK hKc hKε hE ha hS
      ?_ (fun x hx => (hSh x hx).1)
    rw [hΦ] at hcl
    rw [abs_sub_comm]; exact hcl
  · refine hSh.rescale (obsBR_pos ht0 i) ht0 hS.1 hKc.le (fun lam hlam => ?_)
    have := obsBR_le ht0 hi
    have := mul_le_mul_of_nonneg_left (show 1 + obsBR t i + lam ≤ 8 * (1 + t + lam) by linarith)
      hKc.le
    linarith

end MasterFacts

/-! ### The finite-`N` theorem -/

set_option maxHeartbeats 1000000 in
/-- **The arboreal gas with the observable renormalisation condition, finite `N`.**
For `L ≥ L₀` there are constants `t₀ ≥ 1`, `K, K_s, K_c, K_ε, E, a` and `N₀ ≥ 3` depending on `L`
only such that for every `N ≥ N₀` and every `t ≥ t₀` there is `β_N > 0` with
`obsBeta L N β_N = β_N · P_{β_N}[0 ↔ x₀,N]^{3/2} = t` and a sequence `β_j` with the conclusions
`ObsScale` (`β_0 = β_N`, `|β_N − β₁ log L^N| ≤ K_ε(1 + t + log N)`, `β_j ≥ t/32`, the
scale-by-scale bound on `β_j`, `|β_{N−2} − t| ≤ K`, and `|P_{β_N}[0 ↔ x] − ϑ_k²| ≤ Kϑ_k²/β_k`
for all `x ≠ 0`) and `ArbShort L N t` (the short-distance form of the normalised two-point function
`P_{β_N}[0 ↔ x]/P_{β_N}[0 ↔ x₀,N] = P_{β_N}[0 ↔ x]/(t/β_N)^{2/3}` in terms of `t`). -/
theorem thm_arboreal_obs : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ (t₀ K Ks Kc Kε E a : ℝ) (N₀ : ℕ), 1 ≤ t₀ ∧ 0 ≤ K ∧ 0 ≤ E ∧ 0 ≤ a ∧ 0 < Kc ∧ 0 ≤ Kε ∧
    3 ≤ N₀ ∧
    ∀ N : ℕ, N₀ ≤ N → ∀ t : ℝ, t₀ ≤ t →
      ∃ βN : ℝ, 0 < βN ∧ obsBeta L N βN = t ∧
        ∃ β : ℕ → ℝ, ObsScale L N t K Kc Kε E a βN β ∧ ArbShort L N t Ks Kc βN := by
  obtain ⟨L₀, h⟩ := eqs_master
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨M, -, -, -, -⟩ := h L hL
  obtain ⟨K, Ks, Kc, Kε, E, a, t₀, N₀, hK, hE, ha, hKc, hKε, ht₀, hN₀, hF⟩ := M.ob_master
  refine ⟨t₀, K, Ks, Kc, Kε, E, a, N₀, ht₀, hK, hE, ha, hKc, hKε, hN₀, fun N hN t ht => ?_⟩
  obtain ⟨b, hb0, hΦ, -, β, hS, hSh⟩ := (hF t ht).2 N hN
  exact ⟨1 / b, one_div_pos.2 hb0, hΦ, β, hS, hSh⟩

end

end Spin2
