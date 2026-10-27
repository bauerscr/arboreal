import Flow2.RangeKeep

/-!
# The range of initial couplings from the sharp marginal flow

The range `b ∈ (0, b_max]`, `1/b_max = 1/ε + N β₊` of `Flow2.History` only uses the crude band
`|G_j - g - β g²| ≤ δ β g² + c g³`; it forces `1/ǧ_N ≥ 1/ε + N (2δβ + c)`, i.e. `ǧ_N → 0` as
`N → ∞`. Here (F1) is assumed in the *sharp* form `|G_j - g - β g²| ≤ e_j g² + c g³` with a
summable error, `∑_{j<N} e_j ≤ E` (`SharpHyp`). Then `1/g` decreases by at most
`β + e_j + c g_j` per step, and `g_j ≤ (1/ε + β (N - j))⁻¹` along the worst case, so with

  `1/b_maxS = 1/ε + β N + E + (c/β) log(1 + β N ε)`      (`bmaxS`)

every clamped trajectory from `b ∈ (0, b_maxS]` stays in `D_ε` (`trajc_InDhS`, `keepD_of_bmaxS`).
The fixed-point machinery of `Flow2.RangeKeep` then gives existence, uniqueness and continuity on
`(0, b_maxS]` (`fh_flow_range`). In addition:

* `ginv_gN_bmaxS`: `1/ǧ_N(b_maxS) ≤ ginvS = 1/ε + (3 + 2β) E + ((c + C)/β) log(1 + β N ε)`,
  so the final coupling at the edge of the range is `≳ (1/ε + O(log(1 + βNε)))⁻¹`
  (only logarithmically small in `N`), and every value `1/β_R` with `β_R ≥ ginvS` is attained
  (`exists_gN_eq_invS`);
* `ginv_log`: along *any* admissible trajectory (any `b`), if `c_g ε ≤ (1-δ)β/2`,
  `|1/ǧ_n - 1/b + β n| ≤ 2(1+β) E + (5C/β) log(ǧ_n/b)`, the form
  `1/ǧ_n = β_ε - β n + O(1 + log(β_ε ǧ_n))` of Expected result `thm:flow` (i).
-/

open Set Filter Topology Finset

noncomputable section

namespace Flow2

namespace Hist

/-! ### The worst-case decrement of `1/g` -/

/-- The worst-case decrement of `1/g` at step `k`: `β + e_k + c/(1/ε + β (N - k))`. -/
def decS (β c ε : ℝ) (e : ℕ → ℝ) (N k : ℕ) : ℝ := β + e k + c / (1 / ε + β * ((N : ℝ) - k))

/-- `Φ_i = ∑_{k<i} decS_k`. -/
def phiS (β c ε : ℝ) (e : ℕ → ℝ) (N i : ℕ) : ℝ := ∑ k ∈ range i, decS β c ε e N k

/-- The largest initial coupling of the sharp range,
`b_maxS = (1/ε + β N + E + (c/β) log(1 + β N ε))⁻¹`. -/
def bmaxS (β c E : ℝ) (N : ℕ) (ε : ℝ) : ℝ :=
  1 / (1 / ε + β * N + E + c / β * Real.log (1 + β * N * ε))

/-- The bound on `1/ǧ_N(b_maxS)`: `1/ε + (3 + 2β) E + ((c + C)/β) log(1 + β N ε)`,
`C = 2(β² + (1+β) c)`. -/
def ginvS (β c E : ℝ) (N : ℕ) (ε : ℝ) : ℝ :=
  1 / ε + (3 + 2 * β) * E + (c + Cgu β c) / β * Real.log (1 + β * N * ε)

/-- `d/y ≤ log y - log y'` if `0 < y'`, `y' + d ≤ y`. -/
lemma div_le_log_sub {y y' d : ℝ} (hy' : 0 < y') (hd : 0 ≤ d) (h : y' + d ≤ y) :
    d / y ≤ Real.log y - Real.log y' := by
  have hy : 0 < y := by linarith
  have h1 := Real.log_le_sub_one_of_pos (div_pos hy' hy)
  rw [Real.log_div hy'.ne' hy.ne'] at h1
  have h2 : y' / y - 1 = -((y - y') / y) := by field_simp; ring
  have h3 : d / y ≤ (y - y') / y := div_le_div_of_nonneg_right (by linarith) hy.le
  linarith

/-- `∑_{k<N} (1/ε + β (N - k))⁻¹ ≤ log(1 + β N ε)/β`. -/
lemma sum_inv_le_log {β ε : ℝ} (hβ : 0 < β) (hε : 0 < ε) (N : ℕ) :
    ∑ k ∈ range N, 1 / (1 / ε + β * ((N : ℝ) - k)) ≤ Real.log (1 + β * N * ε) / β := by
  have hterm : ∀ k ∈ range N, 1 / (1 / ε + β * ((N : ℝ) - k)) ≤
      (Real.log (1 / ε + β * ((N : ℝ) - k)) - Real.log (1 / ε + β * ((N : ℝ) - ((k + 1 : ℕ) : ℝ)))) / β := by
    intro k hk
    have hk' : ((k + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast mem_range.1 hk
    have hp : 0 < 1 / ε + β * ((N : ℝ) - ((k + 1 : ℕ) : ℝ)) := by
      have : 0 ≤ β * ((N : ℝ) - ((k + 1 : ℕ) : ℝ)) := mul_nonneg hβ.le (by linarith)
      have : 0 < 1 / ε := by positivity
      linarith
    have h := div_le_log_sub (y := 1 / ε + β * ((N : ℝ) - k)) (d := β) hp hβ.le
      (by push_cast; linarith)
    rw [le_div_iff₀ hβ]
    have e : 1 / (1 / ε + β * ((N : ℝ) - k)) * β = β / (1 / ε + β * ((N : ℝ) - k)) := by ring
    linarith
  refine (sum_le_sum hterm).trans (le_of_eq ?_)
  rw [← sum_div, sum_range_sub' (fun k : ℕ => Real.log (1 / ε + β * ((N : ℝ) - k))) N]
  simp only [Nat.cast_zero, sub_zero, sub_self, mul_zero, add_zero]
  rw [← Real.log_div (by positivity) (by positivity)]
  congr 2
  field_simp

section Real

variable {β c ε E : ℝ} {e : ℕ → ℝ} {N : ℕ}

lemma decS_ge (hβ : 0 < β) (hε : 0 < ε) (hc : 0 ≤ c) (he : ∀ j, 0 ≤ e j) {k : ℕ} (hk : k ≤ N) :
    β ≤ decS β c ε e N k := by
  unfold decS
  have hk' : (k : ℝ) ≤ N := by exact_mod_cast hk
  have : 0 < 1 / ε + β * ((N : ℝ) - k) := by
    have : 0 ≤ β * ((N : ℝ) - k) := mul_nonneg hβ.le (by linarith)
    have : 0 < 1 / ε := by positivity
    linarith
  have := div_nonneg hc this.le
  have := he k
  linarith

lemma phiS_succ (i : ℕ) : phiS β c ε e N (i + 1) = phiS β c ε e N i + decS β c ε e N i := by
  unfold phiS; rw [sum_range_succ]

lemma phiS_gap (hβ : 0 < β) (hε : 0 < ε) (hc : 0 ≤ c) (he : ∀ j, 0 ≤ e j) (j : ℕ) :
    ∀ m : ℕ, j + m ≤ N → phiS β c ε e N j + β * m ≤ phiS β c ε e N (j + m) := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro h
    have h1 := ih (by omega)
    have h2 := decS_ge (e := e) (c := c) hβ hε hc he (show j + m ≤ N by omega)
    rw [← add_assoc, phiS_succ]
    push_cast
    linarith

lemma phiS_gap' (hβ : 0 < β) (hε : 0 < ε) (hc : 0 ≤ c) (he : ∀ j, 0 ≤ e j) {j : ℕ} (hj : j ≤ N) :
    phiS β c ε e N j + β * ((N : ℝ) - j) ≤ phiS β c ε e N N := by
  have h := phiS_gap (N := N) hβ hε hc he j (N - j) (by omega)
  rw [Nat.add_sub_cancel' hj, Nat.cast_sub hj] at h
  exact h

lemma phiS_le (hβ : 0 < β) (hε : 0 < ε) (hc : 0 ≤ c) (hE : ∑ j ∈ range N, e j ≤ E) :
    phiS β c ε e N N ≤ β * N + E + c / β * Real.log (1 + β * N * ε) := by
  unfold phiS decS
  rw [sum_add_distrib, sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
  have h := sum_inv_le_log hβ hε N
  have e1 : ∑ k ∈ range N, c / (1 / ε + β * ((N : ℝ) - k)) =
      c * ∑ k ∈ range N, 1 / (1 / ε + β * ((N : ℝ) - k)) := by
    rw [mul_sum]; exact sum_congr rfl fun k _ => by ring
  rw [e1]
  have h2 := mul_le_mul_of_nonneg_left h hc
  have e2 : c * (Real.log (1 + β * N * ε) / β) = c / β * Real.log (1 + β * N * ε) := by ring
  linarith

lemma log_nonneg_N (hβ : 0 < β) (hε : 0 < ε) : 0 ≤ Real.log (1 + β * N * ε) :=
  Real.log_nonneg (by have : 0 ≤ β * N * ε := by positivity
                      linarith)

lemma bmaxS_den_pos (hβ : 0 < β) (hε : 0 < ε) (hc : 0 ≤ c) (hE0 : 0 ≤ E) :
    0 < 1 / ε + β * N + E + c / β * Real.log (1 + β * N * ε) := by
  have := log_nonneg_N (N := N) hβ hε
  positivity

lemma bmaxS_pos (hβ : 0 < β) (hε : 0 < ε) (hc : 0 ≤ c) (hE0 : 0 ≤ E) : 0 < bmaxS β c E N ε :=
  one_div_pos.2 (bmaxS_den_pos hβ hε hc hE0)

lemma inv_le_of_mem_bmaxS (hβ : 0 < β) (hε : 0 < ε) (hc : 0 ≤ c) (hE0 : 0 ≤ E) {b : ℝ}
    (hb : b ∈ Ioc 0 (bmaxS β c E N ε)) :
    1 / ε + β * N + E + c / β * Real.log (1 + β * N * ε) ≤ 1 / b := by
  have := one_div_le_one_div_of_le hb.1 hb.2
  unfold bmaxS at this
  rwa [one_div_one_div] at this

/-- On the sharp range, `1/b ≥ 1/ε + Φ_N`. -/
lemma phiS_le_of_mem (hβ : 0 < β) (hε : 0 < ε) (hc : 0 ≤ c) (hE : ∑ j ∈ range N, e j ≤ E)
    (hE0 : 0 ≤ E) {b : ℝ} (hb : b ∈ Ioc 0 (bmaxS β c E N ε)) :
    1 / ε + phiS β c ε e N N ≤ 1 / b := by
  have h1 := inv_le_of_mem_bmaxS hβ hε hc hE0 hb
  have h2 := phiS_le (e := e) hβ hε hc hE
  linarith

end Real

/-! ### The sharp hypothesis and the a priori bound -/

variable {X : ℕ → Type*} [∀ j, NormedAddCommGroup (X j)]

/-- The sharp (F1): `|G_j - g - β g²| ≤ e_j g² + c g³` on regular histories in `D_ε`, `j < N`,
with `e_j ≥ 0` and `∑_{j<N} e_j ≤ E`. -/
structure SharpHyp (F : HData X) (Λ β δ κ cg cm cT : ℝ) (N : ℕ) (ε c E : ℝ) (e : ℕ → ℝ) :
    Prop where
  hc : 0 ≤ c
  he : ∀ j, 0 ≤ e j
  hE : ∑ j ∈ range N, e j ≤ E
  F1s : ∀ j < N, ∀ t, InDh Λ β δ κ cg cm cT ε j t →
    |F.G j t - (t j).1 - β * (t j).1 ^ 2| ≤ e j * (t j).1 ^ 2 + c * (t j).1 ^ 3

variable {F : HData X} {Λ β δ κ cg cm cT : ℝ}

lemma SharpHyp.hE0 {N : ℕ} {ε c E : ℝ} {e : ℕ → ℝ}
    (S : SharpHyp F Λ β δ κ cg cm cT N ε c E e) : 0 ≤ E :=
  (sum_nonneg fun j _ => S.he j).trans S.hE

section Apriori

variable {N : ℕ} {A a ε c E : ℝ} {e : ℕ → ℝ} (H : HHyp F Λ β δ κ cg cm cT N A a ε)
  (he : ε ≤ eps0u Λ β δ κ cg cm) (hε : 0 < ε) (S : SharpHyp F Λ β δ κ cg cm cT N ε c E e)

include H he S in
/-- One sharp step in `1/g`: `1/G_j ≥ 1/g - (β + e_j + c g)`. -/
lemma inv_step_sharp {j : ℕ} (hj : j < N) {t : Seq X} (ht : InDh Λ β δ κ cg cm cT ε j t) :
    1 / (t j).1 - (β + e j + c * (t j).1) ≤ 1 / F.G j t := by
  obtain ⟨h1, -, -⟩ := step_D H he hj ht
  have hg := (ht.1 j le_rfl).1
  have hG : 0 < F.G j t := by linarith
  have hF := (abs_le.1 (S.F1s j hj t ht)).2
  have hbp : 0 ≤ β + e j + c * (t j).1 := by
    have := H.hβ; have := S.he j; have := mul_nonneg S.hc hg.le; linarith
  refine inv_step hg hG hbp ?_
  have e1 : (β + e j + c * (t j).1) * (t j).1 ^ 2 = β * (t j).1 ^ 2 + (e j * (t j).1 ^ 2 +
    c * (t j).1 ^ 3) := by ring
  linarith

include H he hε S

omit he in
/-- The lower bound `1/ε + β (N - i) ≤ 1/b - Φ_i`. -/
lemma lower_gap {b : ℝ} (hB : 1 / ε + phiS β c ε e N N ≤ 1 / b) {i : ℕ} (hi : i ≤ N) :
    1 / ε + β * ((N : ℝ) - i) ≤ 1 / b - phiS β c ε e N i := by
  have := phiS_gap' H.hβ hε S.hc S.he hi
  linarith

/-- **The a priori bound of the sharp range**: every clamped trajectory from `b` with
`1/b ≥ 1/ε + Φ_N` is a regular history in `D_ε`, and `1/g_i ≥ 1/b - Φ_i`. -/
lemma trajc_InDhS {b : ℝ} (hb0 : 0 < b) (hB : 1 / ε + phiS β c ε e N N ≤ 1 / b) (μ₀ : ℝ) :
    ∀ j ≤ N, InDh Λ β δ κ cg cm cT ε j (trajc F Λ cm b μ₀) ∧
      ∀ i ≤ j, 1 / b - phiS β c ε e N i ≤ 1 / (trajc F Λ cm b μ₀ i).1 := by
  intro j
  induction j with
  | zero =>
    intro _
    have hbε : b ≤ ε := by
      have h0 := lower_gap H hε S hB (Nat.zero_le N)
      have hph : phiS β c ε e N 0 = 0 := by simp [phiS]
      have : 0 ≤ β * (N : ℝ) := mul_nonneg H.hβ.le (Nat.cast_nonneg _)
      rw [hph, sub_zero] at h0
      simp only [CharP.cast_eq_zero, sub_zero] at h0
      have h1 : 1 / ε ≤ 1 / b := by linarith
      rwa [one_div_le_one_div hε hb0] at h1
    refine ⟨⟨fun i hi => ?_, fun i hi => absurd hi (Nat.not_lt_zero _)⟩, fun i hi => ?_⟩
    · obtain rfl : i = 0 := by omega
      exact ⟨hb0, hbε,
        abs_clamp_le _ (mul_nonneg (cmu_pos H.hΛ H.hcm).le hb0.le),
        by simp only [trajc_zero, norm_zero]; exact mul_nonneg (cx_pos H.hκ1 H.hcT).le (by
          positivity)⟩
    · obtain rfl : i = 0 := by omega
      simp [trajc_zero, phiS]
  | succ j ih =>
    intro hj
    obtain ⟨hs, hinv⟩ := ih (by omega)
    obtain ⟨h1, -, -⟩ := step_D H he (by omega : j < N) hs
    have hg := (hs.1 j le_rfl).1
    have hGpos : 0 < F.G j (trajc F Λ cm b μ₀) := by linarith
    -- `g_j ≤ (1/ε + β (N - j))⁻¹`
    have hlow := (lower_gap H hε S hB (by omega : j ≤ N)).trans (hinv j le_rfl)
    have hden : 0 < 1 / ε + β * ((N : ℝ) - j) := by
      have hj' : (j : ℝ) ≤ N := by exact_mod_cast (show j ≤ N by omega)
      have : 0 ≤ β * ((N : ℝ) - j) := mul_nonneg H.hβ.le (by linarith)
      have : 0 < 1 / ε := by positivity
      linarith
    have hgle : (trajc F Λ cm b μ₀ j).1 ≤ 1 / (1 / ε + β * ((N : ℝ) - j)) := by
      rw [le_one_div hg hden]; exact hlow
    have hcg : c * (trajc F Λ cm b μ₀ j).1 ≤ c / (1 / ε + β * ((N : ℝ) - j)) := by
      rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hgle S.hc
    have hstep := inv_step_sharp H he S (by omega : j < N) hs
    have hnew : 1 / b - phiS β c ε e N (j + 1) ≤ 1 / F.G j (trajc F Λ cm b μ₀) := by
      rw [phiS_succ]; unfold decS
      have := hinv j le_rfl
      linarith
    have hGε : F.G j (trajc F Λ cm b μ₀) ≤ ε := by
      have hle : 1 / ε ≤ 1 / F.G j (trajc F Λ cm b μ₀) := by
        have h2 := lower_gap H hε S hB (show j + 1 ≤ N by omega)
        have : 0 ≤ β * ((N : ℝ) - ((j + 1 : ℕ) : ℝ)) := by
          have hj' : ((j + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hj
          exact mul_nonneg H.hβ.le (by linarith)
        linarith
      rwa [one_div_le_one_div hε hGpos] at hle
    refine ⟨⟨fun i hi => ?_, fun i hi => ?_⟩, fun i hi => ?_⟩
    · rcases (show i = j + 1 ∨ i ≤ j by omega) with rfl | hij
      · rw [trajc_succ H b μ₀ (by omega)]
        exact step_InD H he (by omega) hs hGε
          (abs_clamp_le _ (mul_nonneg (cmu_pos H.hΛ H.hcm).le (by linarith)))
      · exact hs.1 i hij
    · rcases (show i = j ∨ i < j by omega) with rfl | hij
      · rw [trajc_succ H b μ₀ (by omega)]; exact H.F1 i (by omega) _ hs
      · exact hs.2 i hij
    · rcases (show i = j + 1 ∨ i ≤ j by omega) with rfl | hij
      · rw [trajc_succ H b μ₀ (by omega)]; exact hnew
      · exact hinv i hij

/-- **The sharp range keeps the flow in `D_ε`.** -/
lemma keepD_of_bmaxS {b : ℝ} (hb : b ∈ Ioc 0 (bmaxS β c E N ε)) :
    KeepD F Λ β δ κ cg cm cT N ε b :=
  ⟨hb.1, fun μ₀ j hj => (trajc_InDhS H he hε S hb.1
    (phiS_le_of_mem H.hβ hε S.hc S.hE S.hE0 hb) μ₀ j hj).1⟩

/-- Along admissible trajectories of the sharp range: `1/ǧ_j ≥ 1/b - Φ_j ≥ 1/ε + β (N - j)`. -/
lemma admissible_lowerS {b μ₀ : ℝ} (hb : b ∈ Ioc 0 (bmaxS β c E N ε))
    (h : Admissible F Λ κ cm cT N ε b μ₀) {j : ℕ} (hj : j ≤ N) :
    1 / b - phiS β c ε e N j ≤ 1 / (traj F Λ b μ₀ j).1 ∧
      1 / ε + β * ((N : ℝ) - j) ≤ 1 / (traj F Λ b μ₀ j).1 := by
  have hB := phiS_le_of_mem H.hβ hε S.hc S.hE S.hE0 hb
  have h1 := (trajc_InDhS H he hε S hb.1 hB μ₀ N le_rfl).2 j hj
  rw [trajc_eq_traj H h N le_rfl j hj] at h1
  exact ⟨h1, (lower_gap H hε S hB hj).trans h1⟩

end Apriori

end Hist

end Flow2
