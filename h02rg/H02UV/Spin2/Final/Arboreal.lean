import Spin2.Final.ArborealEqs
import Spin2.Cont.ContEqS3
import Spin2.Cont.ContFx5b
import Spin2.Cont.ContEqS0
import Spin2.Cont.ContWindow

set_option autoImplicit false

/-!
# The main theorems of `h02uv-outline.tex` for the arboreal gas, without the auxiliary mass

The connection probability `Pconn L N β x = P_β[0 ↔ x]` is the arboreal gas on the torus
`Λ_N = (ℤ/L^Nℤ)²` with weight `β` per nearest-neighbour edge (`H02.arborealProb`, `Ward.nnW`);
it does not involve the auxiliary Gaussian mass `m²`. In the Lean theorems `thm:multiscale`,
`thm:short` and `thm:limit-fixed`, `m² > 0` enters only through the renormalisation group
parametrisation: the window `4m²L^{2N} ≤ 1/β_R`, the bracket `[bFin(1/(2β_R)), bFin(2/β_R)]` of
admissible `b = 1/β_ε`, and the running couplings `β_j = 1/ǧ_j` of the `h = 0` trajectory.

Here `m²` is fixed internally (`arbMass`: `m² = 1/(4β_R L^{2N})`, the upper end of the window) and
the RG objects are existentially quantified. The conclusions only involve `P_β[0 ↔ x]` at the
produced `β_ε` (resp. a produced sequence `β_N`), and a produced sequence `j ↦ β_j` with explicit
bounds.

* `avg0_mass_indep`: the Gaussian mass-shift identity at `h = 0`: `⟨ψ̄_0ψ_x⟩` with covariance
  `(−Δ+m²)^{-1}` and `V_0 = (0, 0, b − m², b)` does not depend on `m² > 0` (both sides equal
  `b^{-1}P_{1/b}[0 ↔ x]`, `Pconn_eq_avg0`).
* `ArbScale`, `ArbShort`: the `m`-free conclusions of `thm:beta`/`thm:multiscale` and of
  `thm:short` (B), (C) at one `N`.
* `MasterFacts.arb_perN`, `arbF_eq_clF`, ...: the ingredients of the main theorems
  `thm_arboreal_multiscale` (Theorems 1.1 and 1.2 for the arboreal gas) and
  `thm_arboreal_limit_fixed` (Theorem 1.5), which are in `H02UV/Main/Theorems.lean`.
-/

namespace Spin2

open Step Step2 PtCorr2 Cont Loc Grassmann Step2.D2

noncomputable section

open Finset Flow2 Flow2.Hist Set Filter Topology

variable {L : ℕ} [NeZero L]

/-! ### The mass-shift identity -/

/-- **Mass-shift identity at `h = 0`.** For `b > 0` the fermionic two-point function
`⟨ψ̄_0ψ_x⟩` of `PtCorr2.avg0 L N m² b (b − m²)` (covariance `(−Δ+m²)^{-1}`, quadratic coupling
`a₀ = b − m²`, so the total quadratic form is `−Δ + b`) is the same for all `m² > 0`. -/
theorem avg0_mass_indep {N : ℕ} {b m m' : ℝ} (hb : 0 < b) (hm : 0 < m) (hm' : 0 < m')
    (x : Lam 2 L N) :
    PtCorr2.avg0 L N m b (b - m) (psibar 0 * psi x) =
      PtCorr2.avg0 L N m' b (b - m') (psibar 0 * psi x) := by
  have h1 := Pconn_eq_avg0 (L := L) (N := N) hb hm (show b = (b - m) + m by ring) x
  have h2 := Pconn_eq_avg0 (L := L) (N := N) hb hm' (show b = (b - m') + m' by ring) x
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  exact mul_left_cancel₀ hb0 (h1.symm.trans h2)

/-- `b⟨ψ̄_0ψ_x⟩ = P_{1/b}[0 ↔ x]` for every auxiliary mass `m² > 0` (`Pconn_eq_avg0` at `h = 0`). -/
theorem avg0_eq_Pconn {N : ℕ} {b m : ℝ} (hb : 0 < b) (hm : 0 < m) (x : Lam 2 L N) :
    (b : ℂ) * PtCorr2.avg0 L N m b (b - m) (psibar 0 * psi x) = ((Pconn L N (1 / b) x : ℝ) : ℂ) :=
  (Pconn_eq_avg0 (L := L) (N := N) hb hm (show b = (b - m) + m by ring) x).symm

/-! ### The `m`-free conclusions -/

variable (L) in
/-- The internal choice of the auxiliary mass: `m² = 1/(4β_R L^{2N})` (`4m²L^{2N} = 1/β_R`). -/
def arbMass (N : ℕ) (βR : ℝ) : ℝ := 1 / (4 * βR * (L : ℝ) ^ (2 * N))

variable (L) in
/-- **The `m`-free conclusions of `thm:beta` and `thm:multiscale` at volume `N`** for
`β_ε` and a sequence `β_j` (`j ≤ N − 2`): `β_0 = β_ε > 0`;
`|β_ε − Nβ₁ log L| ≤ K_ε(1 + β_R + log N)`; for `j ≤ N − 2`, `β_j ≥ β_R/4` and
`|β_j − (N−2−j)β₁ log L| ≤ (5β_R + E) + a log(2((N−2−j)β₁ log L + 5β_R + E + a|log 2a|))`;
`β_{N−2} ≤ 5β_R`; and for every `x ≠ 0`, with `ℓ = |x|/L^N`, `λ = log(1/ℓ)`, `j_p = j(ℓ)`,
`k = min(j_p, N − 2)`: `|β_k − β₁λ| ≤ K_c(1 + β_R + log(1 + λ))` and
`|P_{β_ε}[0 ↔ x] − ϑ_k²| ≤ Kϑ_k²/β_k` with `ϑ_k² = (β_k/β_ε)^{2/3}`. (`betaL L = β₁ log L`.) -/
def ArbScale (N : ℕ) (βR K Kc Kε E a βε : ℝ) (β : ℕ → ℝ) : Prop :=
  0 < βε ∧ β 0 = βε ∧
  |βε - N * betaL L| ≤ Kε * (1 + βR + Real.log N) ∧
  (∀ j ≤ N - 2, βR / 4 ≤ β j ∧
    |β j - ((N - 2 - j : ℕ) : ℝ) * betaL L| ≤
      (5 * βR + E) + a * Real.log (2 * (((N - 2 - j : ℕ) : ℝ) * betaL L + (5 * βR + E) +
        a * |Real.log (2 * a)|))) ∧
  β (N - 2) ≤ 5 * βR ∧
  ∀ x : Lam 2 L N, x ≠ 0 → ∃ jp : ℕ, (jp : ℤ) = jPhys L N (eucl x / (L : ℝ) ^ N) ∧
    |β (min jp (N - 2)) - betaOne * Real.log (1 / (eucl x / (L : ℝ) ^ N))| ≤
      Kc * (1 + βR + Real.log (1 + Real.log (1 / (eucl x / (L : ℝ) ^ N)))) ∧
    |Pconn L N βε x - (β (min jp (N - 2)) / βε) ^ (2 / 3 : ℝ)| ≤
      K * (β (min jp (N - 2)) / βε) ^ (2 / 3 : ℝ) / β (min jp (N - 2))

variable (L) in
/-- **The `m`-free short-distance form (`thm:short` (B), (C) at finite `ε`)**: for every `x ≠ 0`,
with `λ = log(L^N/|x|) > 0` and `ϑ_ε² = (β_R/β_ε)^{2/3}`: if `2K_c(1 + β_R + log(1 + λ)) ≤ β₁λ`,
`|ϑ_ε^{-2}P_{β_ε}[0 ↔ x] − (β₁λ/β_R)^{2/3}| ≤ (β₁λ/β_R)^{2/3}(K_c(1 + β_R + log(1 + λ)) + 2K)/(β₁λ)`;
and always `ϑ_ε^{-2}P_{β_ε}[0 ↔ x] ≤ (1 + |K|)((β₁λ + K_c(1 + β_R + log(1 + λ)))/β_R)^{2/3}`. -/
def ArbShort (N : ℕ) (βR K Kc βε : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 →
    0 < Real.log (1 / (eucl x / (L : ℝ) ^ N)) ∧
    (2 * (Kc * (1 + βR + Real.log (1 + Real.log (1 / (eucl x / (L : ℝ) ^ N))))) ≤
        betaOne * Real.log (1 / (eucl x / (L : ℝ) ^ N)) →
      |Pconn L N βε x / (βR / βε) ^ (2 / 3 : ℝ) -
          (betaOne * Real.log (1 / (eucl x / (L : ℝ) ^ N)) / βR) ^ (2 / 3 : ℝ)| ≤
        (betaOne * Real.log (1 / (eucl x / (L : ℝ) ^ N)) / βR) ^ (2 / 3 : ℝ) *
          ((Kc * (1 + βR + Real.log (1 + Real.log (1 / (eucl x / (L : ℝ) ^ N)))) + 2 * K) /
            (betaOne * Real.log (1 / (eucl x / (L : ℝ) ^ N))))) ∧
    Pconn L N βε x / (βR / βε) ^ (2 / 3 : ℝ) ≤
      (1 + |K|) * ((betaOne * Real.log (1 / (eucl x / (L : ℝ) ^ N)) +
        Kc * (1 + βR + Real.log (1 + Real.log (1 / (eucl x / (L : ℝ) ^ N))))) / βR) ^
          (2 / 3 : ℝ)

variable (L) in
/-- The normalised arboreal-gas two-point function on `𝕋²`:
`f_N(x) = (β_R/β_N)^{-2/3} P_{β_N}[0 ↔ x_N]`, `x_N = latPtN L N x`. -/
def arbF (βR : ℝ) (βs : ℕ → ℝ) (N : ℕ) (x : UnitAddTorus (Fin 2)) : ℝ :=
  Pconn L N (βs N) (latPtN L N x) / (βR / βs N) ^ (2 / 3 : ℝ)

theorem arb_theta (βR b : ℝ) : (βR / (1 / b)) ^ (2 / 3 : ℝ) = thetaEpsSq βR b := by
  rw [thetaEpsSq, div_div_eq_mul_div, div_one]

theorem arbF_eq_clF (βR : ℝ) (b : ℕ → ℝ) :
    arbF L βR (fun N => 1 / b N) = clF L βR b := by
  funext N x
  rw [arbF, clF, arb_theta]

/-! ### The per-`M` core -/

namespace MasterFacts

variable (M : MasterFacts L)

instance arbFactℓ (N : ℕ) : Fact (0 < (a5wR M N).ℓ) := ⟨M.core.hC2.1⟩
instance arbFactA (N : ℕ) : Fact (0 < (a5wR M N).A) := ⟨M.core.hC2.2.1⟩

/-- The window identity `4 m² L^{2N} = 1/β_R` for `m² = arbMass`. -/
theorem arbMass_spec (N : ℕ) {βR : ℝ} (hβ : 0 < βR) :
    0 < arbMass L N βR ∧ 4 * (arbMass L N βR * (L : ℝ) ^ (2 * N)) ≤ 1 / βR := by
  have hL : (0 : ℝ) < (L : ℝ) ^ (2 * N) :=
    pow_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L))) _
  refine ⟨by unfold arbMass; positivity, le_of_eq ?_⟩
  unfold arbMass
  field_simp

/-- The left end of the bracket, `bFin(m², 1/(2β_R))`, at the master parameters. -/
def arbB (N : ℕ) (βR : ℝ) : ℝ :=
  bFin (a5wR M N) M.core.κ M.core.cm M.core.cT (N - 2) M.core.ε (arbMass L N βR) (1 / (2 * βR))

/-- **The bracket is nonempty** (`thm:beta`, monotonicity of `β_R ↦ β_ε`): for `N ≥ 2`,
`m² ∈ mRange` and `4/ε ≤ β_R`, the left end `bFin(1/(2β_R))` is positive and lies in the
bracket `[bFin(1/(2β_R)), bFin(2/β_R)]`. -/
theorem arb_bracket_left {N : ℕ} (hN : 2 ≤ N) {m βR : ℝ} (hm : m ∈ mRange L N)
    (hβ : 4 / M.core.ε ≤ βR) :
    0 < bFin (a5wR M N) M.core.κ M.core.cm M.core.cT (N - 2) M.core.ε m (1 / (2 * βR)) ∧
    bFin (a5wR M N) M.core.κ M.core.cm M.core.cT (N - 2) M.core.ε m (1 / (2 * βR)) ∈
      ctBracket M (a5wR M N) m βR := by
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast M.ct_L2
  obtain ⟨-, -, -, hε, -⟩ := M.core.hC2
  have hBC := betaConcl_of hL2 M.core.hε1 M.core.hC2 M.core.hSp
  obtain ⟨hpt, hmono, -⟩ := hBC N (a5wR M N) rfl rfl rfl rfl rfl hN (N - 2) (by omega) m hm
  have h4 : (0 : ℝ) < 4 / M.core.ε := by positivity
  have hβ0 : 0 < βR := h4.trans_le hβ
  have hlo : 2 / M.core.ε ≤ 2 * βR := by
    have : 2 / M.core.ε ≤ 4 / M.core.ε := div_le_div_of_nonneg_right (by norm_num) hε.le
    linarith
  have hhi : 2 / M.core.ε ≤ βR / 2 := by
    have e : 4 / M.core.ε / 2 = 2 / M.core.ε := by field_simp; norm_num
    linarith [div_le_div_of_nonneg_right hβ (show (0 : ℝ) ≤ 2 by norm_num)]
  have pos_of : ∀ b ∈ Ufix (rgDataM (a5wR M N) m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT
      (N - 2) M.core.ε, 0 < b := fun b hb => by
    obtain ⟨μ, hadm, -⟩ := hb
    exact (hadm.1 0 (Nat.zero_le _)).1
  have h1 := (hpt (2 * βR) hlo).1
  have h2 := (hpt (βR / 2) hhi).1
  have hb1 := pos_of _ h1
  have hb2 := pos_of _ h2
  have hlt := hmono (show βR / 2 ∈ Ici (2 / M.core.ε) from hhi)
    (show 2 * βR ∈ Ici (2 / M.core.ε) from hlo) (by linarith)
  simp only at hlt
  rw [one_div_lt_one_div hb2 hb1] at hlt
  refine ⟨hb1, le_rfl, ?_⟩
  have e : (2 : ℝ) / βR = 1 / (βR / 2) := by field_simp
  rw [e]
  exact hlt.le

/-- `1/β_R ≤ ε/4` gives `4/ε ≤ β_R`. -/
theorem arb_eps_le {βR : ℝ} (hβR : 0 < βR) (h1 : 1 / βR ≤ M.core.ε / 4) : 4 / M.core.ε ≤ βR := by
  obtain ⟨-, -, -, hε, -⟩ := M.core.hC2
  rw [div_le_iff₀ hε]
  rw [div_le_iff₀ hβR] at h1
  nlinarith only [h1, hβR, hε]

/-- **Admissibility of the internal choice**: for `N ≥ 2` and `4/ε ≤ β_R`,
`b = arbB N β_R > 0` lies in the bracket at the mass `arbMass`. -/
theorem arb_adm_at {N : ℕ} (hN : 2 ≤ N) {βR : ℝ} (hβR : 0 < βR) (hβ : 4 / M.core.ε ≤ βR) :
    0 < M.arbB N βR ∧ M.arbB N βR ∈ ctBracket M (a5wR M N) (arbMass L N βR) βR := by
  obtain ⟨-, -, -, hε, -⟩ := M.core.hC2
  have hε1 := M.core.hε1
  obtain ⟨hm0, hmass⟩ := MasterFacts.arbMass_spec (L := L) N hβR
  have h4 : 4 ≤ βR := le_trans ((le_div_iff₀ hε).2 (by nlinarith)) hβ
  have hmL : arbMass L N βR * (L : ℝ) ^ (2 * N) ≤ 1 := by
    have : 1 / βR ≤ 1 := by rw [div_le_one hβR]; linarith
    linarith
  have hmR : arbMass L N βR ∈ mRange L N :=
    fin_mRange (by exact_mod_cast M.ct_L2) (by omega) hm0 hmL
  exact M.arb_bracket_left hN hmR hβ

set_option maxHeartbeats 4000000 in
/-- **The per-`N` `m`-free conclusions for every `b` in the bracket** (constants depending on
`L` only, through `M`). -/
theorem arb_perN : ∃ (g₀ K Ks Kc Kε E a : ℝ) (N₀ : ℕ), 0 < g₀ ∧ 0 ≤ E ∧ 0 ≤ a ∧ 0 < Kc ∧
    3 ≤ N₀ ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → N₀ ≤ N →
    ∀ m βR : ℝ, 0 < m → 0 < βR → 4 * (m * (L : ℝ) ^ (2 * N)) ≤ 1 / βR → 1 / βR ≤ g₀ →
    ∀ b ∈ ctBracket M R m βR,
      ArbScale L N βR K Kc Kε E a (1 / b) (betaJ R m b (b - m)) ∧
      ArbShort L N βR Ks Kc (1 / b) := by
  obtain ⟨g₁, K, N₁, hg₁, hg₁1, hN₁, hA⟩ := eqs_allB M
  obtain ⟨g₂, Ks, Kc, N₂, hg₂, hKc, hS⟩ := eqs_shortX M
  obtain ⟨g₃, N₃, hg₃, hN₃, hU⟩ := eqs_bracketUp M
  have hβ := ct_betaL_pos M.ct_L2
  set β := betaL L with hβd
  set a := M.ctA
  set E := M.ctE
  set c := a * |Real.log (2 * a)|
  have ha := M.ctA_nonneg
  have hE := M.ctE_nonneg
  have hc : 0 ≤ c := mul_nonneg ha (abs_nonneg _)
  set Kε := 2 * β + 5 + E + 2 * a * (β + E + c) + 10 * a + a with hKεd
  refine ⟨min g₁ (min g₂ g₃), K, Ks, Kc, Kε, E, a, max N₁ (max N₂ N₃),
    lt_min hg₁ (lt_min hg₂ hg₃), hE, ha, hKc, le_trans hN₁ (le_max_left _ _), ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN m βR hm hβR hmass hy b hb
  have hy₁ : 1 / βR ≤ g₁ := hy.trans (min_le_left _ _)
  have hy₂ : 1 / βR ≤ g₂ := hy.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hy₃ : 1 / βR ≤ g₃ := hy.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hN1 : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN3 : N₃ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hN3' : 3 ≤ N := le_trans hN₁ hN1
  obtain ⟨hmR, -, hB, -⟩ := hA N R hP hi0 hRℓ hRA hRρ hN1 m βR hm hβR hmass hy₁
  obtain ⟨hb0, hD, hFw, hgl⟩ := hB b hb
  have hUb := hU N R hP hi0 hRℓ hRA hRρ hN3 m βR hm hβR hmass hy₃ b hb
  have hSb := hS N R hP hi0 hRℓ hRA hRρ hN2 m βR hm hβR hmass hy₂ b hb
  have hm1 : m * (L : ℝ) ^ (2 * N) ≤ 1 := by
    have h0 : 0 ≤ m * (L : ℝ) ^ (2 * N) := mul_nonneg hm.le (by positivity)
    have : 1 / βR ≤ 1 := hy₁.trans hg₁1
    linarith
  have hT : 1 / (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (N - 2)).1 ≤ 5 * βR := by
    have hg0 : 0 < 1 / βR / 5 := by positivity
    rw [div_le_iff₀ (hg0.trans_le hgl)]
    have e : 5 * βR * (1 / βR / 5) = 1 := by field_simp
    nlinarith only [hgl, e, hβR]
  have H := M.ct_beta_scale R hP hi0 hRℓ hRA hRρ (by omega) hmR hm1 hD hT
  have e0 : betaJ R m b (b - m) 0 = 1 / b := rfl
  -- the bound on `β_ε` (as in `thm_theta_eps`)
  have hεbd : |1 / b - N * β| ≤ Kε * (1 + βR + Real.log N) := by
    have H0 := H 0 (Nat.zero_le _)
    rw [e0, Nat.sub_zero] at H0
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1'
    have hcast : ((N - 2 : ℕ) : ℝ) = N - 2 := by rw [Nat.cast_sub (by omega)]; norm_num
    rw [hcast] at H0
    have hL := ct_log_lin (x := ((N : ℝ) - 2) * β) (s := β) (t := (N : ℝ) - 1)
      (D := 5 * βR + E + c) (by positivity) hβ.le (by linarith)
      (mul_nonneg (by linarith [show (3 : ℝ) ≤ N by exact_mod_cast hN3']) hβ.le)
      (by nlinarith only [hβ])
    rw [show (1 : ℝ) + (N - 1) = N by ring,
      show ((N : ℝ) - 2) * β + (5 * βR + E + c) = ((N : ℝ) - 2) * β + (5 * βR + E) + c by ring]
      at hL
    have hL' := mul_le_mul_of_nonneg_left hL ha
    have t : |1 / b - N * β| ≤ |1 / b - ((N : ℝ) - 2) * β| + 2 * β := by
      have := abs_sub_le (1 / b) (((N : ℝ) - 2) * β) (N * β)
      rw [show ((N : ℝ) - 2) * β - N * β = -(2 * β) by ring, abs_neg,
        abs_of_pos (by linarith : 0 < 2 * β)] at this
      exact this
    have hprod : 0 ≤ 2 * a * (β + E + c) := by positivity
    have k1 : (5 + 10 * a) * βR ≤ Kε * βR := mul_le_mul_of_nonneg_right (by linarith) hβR.le
    have k2 : a * Real.log N ≤ Kε * Real.log N := mul_le_mul_of_nonneg_right (by linarith) hlogN
    have e : a * (2 * (β + (5 * βR + E + c)) + Real.log N) =
        2 * a * (β + E + c) + 10 * a * βR + a * Real.log N := by ring
    have e2 : Kε * (1 + βR + Real.log N) = Kε + Kε * βR + Kε * Real.log N := by ring
    linarith
  refine ⟨⟨one_div_pos.2 hb0, e0, hεbd, fun j hj => ⟨?_, H j hj⟩, ?_, fun x hx => ?_⟩, ?_⟩
  · -- `β_j ≥ β_R/4` from `ǧ_j ≤ 4/β_R`
    have hgj := (hD j hj).1
    have hup := hUb j hj
    show βR / 4 ≤ 1 / (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j).1
    rw [le_div_iff₀ hgj]
    have e : βR / 4 * (4 * (1 / βR)) = 1 := by field_simp
    nlinarith only [hup, e, hβR]
  · exact hT
  · obtain ⟨jp, hj, -, -, hP1⟩ := hFw x hx
    obtain ⟨-, ⟨jp', hj', -, -, -, hbl⟩, -, -⟩ := hSb x hx
    have hjj : jp' = jp := by exact_mod_cast hj'.trans hj.symm
    subst hjj
    refine ⟨jp', hj', hbl, ?_⟩
    exact hP1
  · intro x hx
    obtain ⟨hlam, -, hBx, hCx⟩ := hSb x hx
    rw [arb_theta]
    exact ⟨hlam, hBx, hCx⟩

end MasterFacts

end

end Spin2
