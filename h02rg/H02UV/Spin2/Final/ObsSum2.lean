import Spin2.Final.ObsSum1
import Spin2.Final.ObsBeta2

set_option autoImplicit false

/-!
# The summed observable renormalisation condition: existence of `β_N` and the finite-`N` theorem

As `ObsBeta2` with `obsBeta` replaced by `obsBetaSum`. The closeness
`|obsBetaSum L N (1/b) − β̃_{N−2}| ≤ 3C_L` on every bracket (`os_perM`) comes from the key estimate
`os_dens_close`, whose inputs along the `h = 0` trajectory are: the monotonicity of `ǧ`
(`gmonoD`), the per-step recursion `|β̃_{k+1} − β̃_k + β₁ log L| ≤ K_b a_k + C_gu ǧ_k` of `spinD`
summed over the steps `k, …, N−3` (`os_beta_rec`: `β̃_k ≤ β̃_{N−2} + C₁(1 + (N−2−k))`,
`C₁ = β₁ log L + C_gu + 4K_b`, using `∑ a_k ≤ 4` and `ǧ_k ≤ ε ≤ 1`), and the multiscale formula
of `ArbScale`. The constant is `C_L = 4C₁ + 2K` (`K` the constant of `arb_perN`).

* `MasterFacts.osKb`, `osC1`, `os_beta_rec`.
* `MasterFacts.os_perM`: `arb_perN` plus the closeness on every bracket.
* `MasterFacts.os_master`: constants depending on `L` only; for `t ≥ t₀`, `N ≥ N₀` there is `b > 0`
  in one of the four brackets with `obsBetaSum L N (1/b) = t`, `ObsScale` and `ArbShort` at `t`.
* **`thm_arboreal_sum`**: the finite-`N` theorem with the summed observable renormalisation
  condition.
-/

namespace Spin2

open Step Step2 PtCorr2 Cont Loc Grassmann Step2.D2

noncomputable section

open Finset Flow2 Flow2.Hist Set Filter Topology

variable {L : ℕ} [NeZero L]

namespace MasterFacts

variable (M : MasterFacts L)

/-- `K_b = 2(1 + β₁ log L) max(K_e, β₁ log L/2)`, the coefficient of `a_k` in the per-step
recursion. -/
def osKb : ℝ := 2 * (1 + betaL L) * max M.core.Ke (betaL L / 2)

/-- `C₁ = β₁ log L + C_gu + 4K_b`. -/
def osC1 : ℝ := betaL L + Cgu (betaL L) M.core.cg + 4 * M.osKb

theorem osKb_nonneg : 0 ≤ M.osKb := by
  have hβ := ct_betaL_pos M.ct_L2
  have : 0 ≤ max M.core.Ke (betaL L / 2) := le_max_of_le_right (by linarith)
  unfold osKb; positivity

theorem osC1_nonneg : 0 ≤ M.osC1 := by
  have hβ := ct_betaL_pos M.ct_L2
  obtain ⟨-, -, -, -, -, -, hcg, -⟩ := M.core.hC2
  have := M.osKb_nonneg
  unfold osC1 Cgu; positivity

set_option maxHeartbeats 1000000 in
/-- **The per-step recursion summed along a `D_ε` trajectory** (`h = 0` start `(b, b − m²)`):
for `j ≤ N − 2`, `β̃_j ≤ β̃_{N−2} + C₁(1 + (N−2−j))`. -/
theorem os_beta_rec {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN : 2 ≤ N) {m : ℝ} (hm : m ∈ mRange L N)
    (hm1 : m * (L : ℝ) ^ (2 * N) ≤ 1) {b : ℝ}
    (hD : ∀ j ≤ N - 2, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j)) :
    ∀ j ≤ N - 2, betaJ R m b (b - m) j ≤
      betaJ R m b (b - m) (N - 2) + M.osC1 * (1 + ((N - 2 - j : ℕ) : ℝ)) := by
  intro j hj
  set Nh := N - 2 with hNh
  obtain ⟨-, -, -, hstep, -⟩ := M.spinD N R hP hi0 hRℓ hRA hRρ (by omega) Nh (by omega)
  have hβ := ct_betaL_pos M.ct_L2
  obtain ⟨-, -, -, -, -, -, hcg, -⟩ := M.core.hC2
  set β := betaL L with hβd
  set cg := M.core.cg
  have hCgu : 0 ≤ Cgu β cg := by unfold Cgu; positivity
  have hKb := M.osKb_nonneg
  set g : ℕ → ℝ := fun k => (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) k).1 with hgd
  have hg1 : ∀ k ≤ Nh, g k ≤ 1 := fun k hk => (hD k hk).2.1.trans M.eps_le
  -- the per-step band summed from `j`
  have hsum : ∀ n, j ≤ n → n ≤ Nh → 1 / g j - 1 / g n ≤
      ((n : ℝ) - j) * (β + Cgu β cg) + M.osKb * ∑ k ∈ Ico j n, zA L m k := by
    intro n hjn
    induction n, hjn using Nat.le_induction with
    | base => intro _; simp
    | succ n hjn ih =>
      intro hn
      have h1 := ih (by omega)
      have h2 := hstep m hm b (b - m) hD n (by omega)
      rw [sum_Ico_succ_top hjn]
      have e2 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) n).1 = g n := rfl
      have e3 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (n + 1)).1 = g (n + 1) := rfl
      have hKbe : 2 * (1 + β) * max M.core.Ke (β / 2) = M.osKb := rfl
      rw [e2, e3, hKbe] at h2
      have h3 := (abs_le.1 h2).1
      have h4 : Cgu β cg * g n ≤ Cgu β cg := by
        have := mul_le_mul_of_nonneg_left (hg1 n (by omega)) hCgu
        linarith
      have h5 : 0 ≤ M.osKb * zA L m n := mul_nonneg hKb (zA_nonneg L hm.1.le n)
      have e : (((n + 1 : ℕ) : ℝ) - j) * (β + Cgu β cg) =
          ((n : ℝ) - j) * (β + Cgu β cg) + (β + Cgu β cg) := by push_cast; ring
      rw [e, mul_add]
      linarith [h1, h3, h4, h5]
  have H := hsum Nh hj le_rfl
  -- the `zA` sum
  have hzA : ∑ k ∈ Ico j Nh, zA L m k ≤ 4 := by
    have hm0 : 0 ≤ m := hm.1.le
    have h1 : ∑ k ∈ Ico j Nh, zA L m k ≤ ∑ k ∈ range Nh, zA L m k :=
      sum_le_sum_of_subset_of_nonneg (by intro k hk; simp at hk ⊢; omega)
        (fun k _ _ => zA_nonneg L hm0 k)
    have h2 := sum_zA_le (Ln := L) rfl (by exact_mod_cast M.ct_L2) hm0 Nh
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by have := M.ct_L2; omega)
    have h3 : ((L : ℝ) ^ Nh) ^ 2 ≤ (L : ℝ) ^ (2 * N) := by
      rw [← pow_mul]; exact pow_le_pow_right₀ hL1 (by omega)
    have h4 : m * ((L : ℝ) ^ Nh) ^ 2 ≤ 1 := (mul_le_mul_of_nonneg_left h3 hm0).trans hm1
    linarith
  have hcast : ((Nh : ℝ) - j) = ((Nh - j : ℕ) : ℝ) := by rw [Nat.cast_sub hj]
  have hi : 0 ≤ ((Nh - j : ℕ) : ℝ) := Nat.cast_nonneg _
  have t1 := mul_le_mul_of_nonneg_left hzA hKb
  have e0 : betaJ R m b (b - m) j = 1 / g j := rfl
  have e1 : betaJ R m b (b - m) Nh = 1 / g Nh := rfl
  rw [e0, e1]
  unfold osC1
  rw [← hβd]
  rw [hcast] at H
  nlinarith only [H, t1, hi, hβ, hCgu, hKb]

set_option maxHeartbeats 1000000 in
/-- **`arb_perN` with `obsBetaSum ≈ β̃_{N−2}`**: constants (`K, K_ε ≥ 0`, `K ≤ C_L`) and, on
every bracket, `ArbScale`, `ArbShort` and `|obsBetaSum L N (1/b) − β̃_{N−2}| ≤ 3C_L` for
`β_R ≥ 16C_L`. -/
theorem os_perM : ∃ (g₀ K Ks Kc Kε E a CL : ℝ) (N₀ : ℕ), 0 < g₀ ∧ 0 ≤ K ∧ 0 ≤ E ∧ 0 ≤ a ∧
    0 < Kc ∧ 0 ≤ Kε ∧ K ≤ CL ∧ 3 ≤ N₀ ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → N₀ ≤ N →
    ∀ m βR : ℝ, 0 < m → 0 < βR → 4 * (m * (L : ℝ) ^ (2 * N)) ≤ 1 / βR → 1 / βR ≤ g₀ →
    ∀ b ∈ ctBracket M R m βR,
      ArbScale L N βR K Kc Kε E a (1 / b) (betaJ R m b (b - m)) ∧
      ArbShort L N βR Ks Kc (1 / b) ∧
      (16 * CL ≤ βR → |obsBetaSum L N (1 / b) - betaJ R m b (b - m) (N - 2)| ≤ 3 * CL) := by
  obtain ⟨g₀, K, Ks, Kc, Kε, E, a, N₀, hg, hE, ha, hKc, hN₀, hF⟩ := M.arb_perN
  obtain ⟨g₁, K₁, N₁, hg₁, hg₁1, hN₁, hA⟩ := eqs_allB M
  have hL2 := M.ct_L2
  have hC1 := M.osC1_nonneg
  refine ⟨min g₀ g₁, |K|, Ks, Kc, |Kε|, E, a, 4 * M.osC1 + 2 * |K|, max N₀ N₁,
    lt_min hg hg₁, abs_nonneg _, hE, ha, hKc, abs_nonneg _, by linarith [abs_nonneg K],
    le_trans hN₀ (le_max_left _ _),
    fun N R _ _ hP hi0 hRℓ hRA hRρ hN m βR hm hβR hmass hy b hb => ?_⟩
  have hy₀ : 1 / βR ≤ g₀ := hy.trans (min_le_left _ _)
  have hy₁ : 1 / βR ≤ g₁ := hy.trans (min_le_right _ _)
  have hN0 : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : N₁ ≤ N := le_trans (le_max_right _ _) hN
  obtain ⟨hS, hSh⟩ := hF N R hP hi0 hRℓ hRA hRρ hN0 m βR hm hβR hmass hy₀ b hb
  have hS' := hS.mono (by omega) hβR (le_abs_self K) (le_abs_self Kε)
  refine ⟨hS', hSh, fun h16 => ?_⟩
  obtain ⟨hmR, -, hB, -⟩ := hA N R hP hi0 hRℓ hRA hRρ hN1 m βR hm hβR hmass hy₁
  obtain ⟨hb0, hD, -, -⟩ := hB b hb
  have hm1 : m * (L : ℝ) ^ (2 * N) ≤ 1 := by
    have h0 : 0 ≤ m * (L : ℝ) ^ (2 * N) := mul_nonneg hm.le (by positivity)
    have : 1 / βR ≤ 1 := hy₁.trans hg₁1
    linarith
  obtain ⟨h1, -, -, h4, -, h6⟩ := hS'
  -- monotonicity of `ǧ` along the trajectory: `β̃_{N−2} ≤ β̃_j`
  have hmono := M.gmonoD N R hP hi0 hRℓ hRA hRρ (by omega) (N - 2) (by omega) m hmR b (b - m) hD
  have hmonoβ : ∀ j ≤ N - 2, betaJ R m b (b - m) (N - 2) ≤ betaJ R m b (b - m) j := by
    intro j hj
    have key : ∀ n, j + n ≤ N - 2 → (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j).1 ≤
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (j + n)).1 := by
      intro n
      induction n with
      | zero => intro _; exact le_rfl
      | succ n ih => intro hn; exact (ih (by omega)).trans (hmono (j + n) (by omega))
    have := key (N - 2 - j) (by omega)
    rw [show j + (N - 2 - j) = N - 2 by omega] at this
    have hgj := (hD j hj).1
    unfold betaJ
    exact one_div_le_one_div_of_le hgj this
  have hrec := M.os_beta_rec R hP hi0 hRℓ hRA hRρ (by omega) hmR hm1 hD
  have hpos : ∀ j ≤ N - 2, 0 < betaJ R m b (b - m) j := fun j hj => by
    linarith [(h4 j hj).1]
  have hβN : 4 * |K| ≤ betaJ R m b (b - m) (N - 2) := by
    have := (h4 (N - 2) le_rfl).1
    linarith [abs_nonneg K]
  have hclose := os_dens_close hL2 (by omega) hb0 (abs_nonneg K) hC1 rfl hpos hmonoβ hrec hβN
    (fun x hx => by obtain ⟨jp, hj, -, hPx⟩ := h6 x hx; exact ⟨jp, hj, hPx⟩)
  exact os_obsBetaSum_close hb0 (by linarith [abs_nonneg K]) (by linarith [(h4 (N - 2) le_rfl).1])
    (hpos (N - 2) le_rfl) hclose

set_option maxHeartbeats 1000000 in
/-- **The master statement for the summed observable renormalisation condition** (constants
depending on `L` only): for `t ≥ t₀` the four couplings `obsBR t i` satisfy `4/ε ≤ t/8`, and for
every `N ≥ N₀` there is `b > 0` in a bracket at some `obsBR t i` (`i ≤ 3`, mass `obsMass L N t`)
with `obsBetaSum L N (1/b) = t`, `ObsScale` and `ArbShort` at `t`. -/
theorem os_master : ∃ (K Ks Kc Kε E a t₀ : ℝ) (N₀ : ℕ), 0 ≤ K ∧ 0 ≤ E ∧ 0 ≤ a ∧ 0 < Kc ∧
    0 ≤ Kε ∧ 1 ≤ t₀ ∧ 3 ≤ N₀ ∧
    ∀ t : ℝ, t₀ ≤ t → 4 / M.core.ε ≤ t / 8 ∧
      ∀ N : ℕ, N₀ ≤ N → ∃ b : ℝ, 0 < b ∧ obsBetaSum L N (1 / b) = t ∧
        (∃ i ≤ 3, b ∈ ctBracket M (a5wR M N) (obsMass L N t) (obsBR t i)) ∧
        ∃ β : ℕ → ℝ, ObsScale L N t K Kc Kε E a (1 / b) β ∧ ArbShort L N t Ks Kc (1 / b) := by
  obtain ⟨g₀, K, Ks, Kc, Kε, E, a, CL, N₀, hg, hK, hE, ha, hKc, hKε, hKCL, hN₀, hF⟩ := M.os_perM
  have hL2 := M.ct_L2
  have hCL : 0 ≤ CL := hK.trans hKCL
  obtain ⟨-, -, -, hε, -⟩ := M.core.hC2
  refine ⟨3 * CL, Ks, 8 * Kc, 8 * Kε, E, a, 8 / g₀ + 32 / M.core.ε + 128 * CL + 1, N₀,
    by positivity, hE, ha, by positivity, by positivity, by
      have : 0 ≤ 8 / g₀ + 32 / M.core.ε + 128 * CL := by positivity
      linarith, hN₀, fun t ht => ?_⟩
  have h1 : 0 ≤ 8 / g₀ := by positivity
  have h2 : 0 ≤ 32 / M.core.ε := by positivity
  have h3 : 0 ≤ 128 * CL := by positivity
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
  have hKi : ∀ i, 16 * CL ≤ obsBR t i := fun i => by
    have := obsBR_ge ht0 i; linarith
  have hbr : ∀ i ≤ 3, ∀ b ∈ ctBracket M (a5wR M N) (obsMass L N t) (obsBR t i),
      ArbScale L N (obsBR t i) K Kc Kε E a (1 / b)
        (betaJ (a5wR M N) (obsMass L N t) b (b - obsMass L N t)) ∧
      ArbShort L N (obsBR t i) Ks Kc (1 / b) ∧
      |obsBetaSum L N (1 / b) -
        betaJ (a5wR M N) (obsMass L N t) b (b - obsMass L N t) (N - 2)| ≤ 3 * CL :=
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
  have hcont : ContinuousOn (fun b => obsBetaSum L N (1 / b))
      (Icc (M.obsA N t 4) (M.obsA N t 0)) := by
    have hne : ∀ b ∈ Icc (M.obsA N t 4) (M.obsA N t 0), b ≠ 0 :=
      fun b hb => (ha4.trans_le hb.1).ne'
    refine ContinuousOn.mul (continuousOn_const.div continuousOn_id hne) ?_
    refine (Real.continuous_rpow_const (by norm_num)).comp_continuousOn ?_
    refine (obsDens_continuousOn N).comp (continuousOn_const.div continuousOn_id hne) ?_
    intro b hb
    exact (one_div_pos.2 (ha4.trans_le hb.1)).le
  have hleft : t ≤ obsBetaSum L N (1 / M.obsA N t 4) := by
    have hmem : M.obsA N t 4 ∈ ctBracket M (a5wR M N) (obsMass L N t) (obsBR t 3) := by
      rw [obs_bracket_eq M N ht0 3]; exact ⟨le_rfl, hmono 3 (by norm_num)⟩
    obtain ⟨⟨-, -, -, h4, -, -⟩, -, hcl⟩ := hbr 3 (by norm_num) _ hmem
    have := (h4 (N - 2) le_rfl).1
    rw [obsBR_three] at this
    linarith [(abs_le.1 hcl).1]
  have hright : obsBetaSum L N (1 / M.obsA N t 0) ≤ t := by
    have hmem : M.obsA N t 0 ∈ ctBracket M (a5wR M N) (obsMass L N t) (obsBR t 0) := by
      rw [obs_bracket_eq M N ht0 0]; exact ⟨hmono 0 (by norm_num), le_rfl⟩
    obtain ⟨⟨-, -, -, -, h5, -⟩, -, hcl⟩ := hbr 0 (by norm_num) _ hmem
    rw [obsBR_zero] at h5
    linarith [(abs_le.1 hcl).2]
  obtain ⟨b, hb, hΦ⟩ := intermediate_value_Icc' h40 hcont ⟨hright, hleft⟩
  have hΦ : obsBetaSum L N (1 / b) = t := hΦ
  obtain ⟨i, hi, hbi⟩ := hcov b hb
  have hb0 : 0 < b := ha4.trans_le hb.1
  obtain ⟨hS, hSh, hcl⟩ := hbr i hi b hbi
  refine ⟨b, hb0, hΦ, ⟨i, hi, hbi⟩,
    betaJ (a5wR M N) (obsMass L N t) b (b - obsMass L N t), ?_, ?_⟩
  · have hS' := hS.mono (by omega) (obsBR_pos ht0 i) hKCL le_rfl
    refine obsScale_of hL2 (by omega) ht0 (obsBR_ge ht0 i) (obsBR_le ht0 hi) hCL hKc hKε hE ha
      hS' ?_ (fun x hx => (hSh x hx).1)
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
/-- **The arboreal gas with the summed observable renormalisation condition, finite `N`.**
For `L ≥ L₀` there are constants `t₀ ≥ 1`, `K, K_s, K_c, K_ε, E, a` and `N₀ ≥ 3` depending on `L`
only such that for every `N ≥ N₀` and every `t ≥ t₀` there is `β_N > 0` with
`obsBetaSum L N β_N = β_N · (E_{β_N}|T_0|/|Λ_N|)^{3/2} = t` and a sequence `β̃_j` with the
conclusions `ObsScale` (`β̃_0 = β_N`, `|β_N − β₁ log L^N| ≤ K_ε(1 + t + log N)`, `β̃_j ≥ t/32`, the
scale-by-scale bound on `β̃_j`, `|β̃_{N−2} − t| ≤ K`, and `|P_{β_N}[0 ↔ x] − ϑ_k²| ≤ Kϑ_k²/β̃_k`
for all `x ≠ 0`) and `ArbShort L N t` (the short-distance form of the normalised two-point
function `P_{β_N}[0 ↔ x]/obsDens L N β_N = P_{β_N}[0 ↔ x]/(t/β_N)^{2/3}` in terms of `t`). -/
theorem thm_arboreal_sum : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ (t₀ K Ks Kc Kε E a : ℝ) (N₀ : ℕ), 1 ≤ t₀ ∧ 0 ≤ K ∧ 0 ≤ E ∧ 0 ≤ a ∧ 0 < Kc ∧ 0 ≤ Kε ∧
    3 ≤ N₀ ∧
    ∀ N : ℕ, N₀ ≤ N → ∀ t : ℝ, t₀ ≤ t →
      ∃ βN : ℝ, 0 < βN ∧ obsBetaSum L N βN = t ∧
        ∃ β : ℕ → ℝ, ObsScale L N t K Kc Kε E a βN β ∧ ArbShort L N t Ks Kc βN := by
  obtain ⟨L₀, h⟩ := eqs_master
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨M, -, -, -, -⟩ := h L hL
  obtain ⟨K, Ks, Kc, Kε, E, a, t₀, N₀, hK, hE, ha, hKc, hKε, ht₀, hN₀, hF⟩ := M.os_master
  refine ⟨t₀, K, Ks, Kc, Kε, E, a, N₀, ht₀, hK, hE, ha, hKc, hKε, hN₀, fun N hN t ht => ?_⟩
  obtain ⟨b, hb0, hΦ, -, β, hS, hSh⟩ := (hF t ht).2 N hN
  exact ⟨1 / b, one_div_pos.2 hb0, hΦ, β, hS, hSh⟩

end

end Spin2
