import Spin2.Cont.ContEqF3
import Spin2.Cont.ContEqS2
import Spin2.Cont.ContEqS3

set_option autoImplicit false

/-!
# B3, `r`-dependent form, final assembly (IV): `ClEquiOn` for small `1/β_R` and `m²L^{2N}`

**`MasterFacts.eqf_equiOn (hcab) (hB)`**: there are `g(r), μ(r) > 0` such that, for every `r > 0`,
every `β_R` with `1/β_R ≤ g(r)` and every admissible sequence (`ClAdm M N₀ β_R R m b`) with
`m_N²L^{2N} ≤ μ(r)` eventually, `clF L β_R b` is asymptotically equicontinuous on `{‖x‖ ≥ r}`.
`g(r) = min(g_A, g_U, eqsGg r₀ C_δ(r)/4)`, `μ(r) = min(eqsGm … C_δ(r), eqsGg r₀ C_δ(r)/2, 1)`,
`C_δ(r) = ⌈log_L(1/r)⌉₊ + 3`.

Proof: for `ε > 0` choose `d = N_h − ms` (waiting, `ǧ_{ms} ≤ ε'` via `ct_beta_scale`,
`L^{−d}` small), `r' ≥ 1` with `L^{−r'} ≤ ε'`, `δ = 1/(2L^{d+r'+2})`; for large `N` the lattice points
`x' = latPtN x`, `y' = latPtN y` satisfy the geometry of `eqs_pairs` (`eqc_region`,
`eqf_supNorm_latPt_sub`), and `|clF x − clF y| ≤ 10·K·cddRel ≤ 10·K·K_c(ǧ_{ms} + a_{ms} + L^{−r'})`.
-/

namespace Spin2

open Step Step2 PtCorr2 Filter Topology Cont Flow2 Flow2.Hist Grassmann Loc

noncomputable section

variable {L : ℕ} [NeZero L]

namespace MasterFacts

variable (M : MasterFacts L)

set_option maxHeartbeats 16000000 in
/-- **Asymptotic equicontinuity on `{‖x‖ ≥ r}` for `1/β_R ≤ g(r)`, `m²L^{2N} ≤ μ(r)`.** -/
theorem eqf_equiOn (hcab : 0 < M.k2cab) (hBk : 0 < M.core.Bk) :
    ∃ gr μr : ℝ → ℝ, (∀ r : ℝ, 0 < r → 0 < gr r ∧ 0 < μr r) ∧
    ∀ (N₀ : ℕ) (r βR : ℝ) (R : ∀ N, RGPar 2 L N) (m b : ℕ → ℝ), 0 < r → 0 < βR →
      1 / βR ≤ gr r → ClAdm M N₀ βR R m b →
      (∃ N₁ : ℕ, ∀ N, N₁ ≤ N → m N * (L : ℝ) ^ (2 * N) ≤ μr r) →
      ClEquiOn (clF L βR b) r := by
  obtain ⟨C₁w, C₁t, C₁v, C₁m, Λ₁, Λ₂, r₀, Kt, hr₀, hPair⟩ := M.eqs_pairs hcab hBk
  obtain ⟨gA, KA0, NA, hgA, -, hNA, hFA⟩ := eqs_allB M
  obtain ⟨gU, NU, hgU, hNU, hFU⟩ := eqs_bracketUp M
  have hL2 : 2 ≤ L := M.ct_L2
  refine ⟨fun r => min (min gA gU) (M.eqsGg r₀ (eqfCd L r) / 4),
    fun r => min (M.eqsGm r₀ Kt C₁w C₁t C₁v C₁m Λ₁ (eqfCd L r))
      (min (M.eqsGg r₀ (eqfCd L r) / 2) 1), fun r _ => ⟨lt_min (lt_min hgA hgU)
        (by have := M.eqsGg_pos r₀ (eqfCd L r); positivity),
      lt_min (M.eqsGm_pos _ _ _ _ _ _ _ _) (lt_min (by have := M.eqsGg_pos r₀ (eqfCd L r); positivity)
        one_pos)⟩, ?_⟩
  intro N₀ r βR R m b hr hβ hy hA hN₁e ε hε
  obtain ⟨N₁, hN₁⟩ := hN₁e
  obtain ⟨hCdpow, hCd2⟩ := eqf_Cd_pow hL2 hr
  have hG0 : 0 < M.eqsGg r₀ (eqfCd L r) := M.eqsGg_pos r₀ (eqfCd L r)
  have hyA : 1 / βR ≤ gA := hy.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hyU : 1 / βR ≤ gU := hy.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hyG : 1 / βR ≤ M.eqsGg r₀ (eqfCd L r) / 4 := hy.trans (min_le_right _ _)
  have hβL := ct_betaL_pos hL2
  -- the constants
  set K := max (M.eqcCmid (M.eqsKA r₀)
    (M.rpc11K r₀ C₁t Λ₁ Λ₂ (rpc9Mb Λ₁ (M.eqsM0 C₁w C₁t C₁v C₁m (eqfCd L r)) (eqfCd L r))
      (eqfCd L r)) (eqfCd L r)) (M.eqcCtop (M.eqsKAt r₀) (M.eqsKEt r₀)) with hKd
  have hK0 : 0 ≤ K := by
    refine le_trans ?_ (le_max_right _ _)
    unfold eqcCtop; have := cw4Cmp_pos M 0; positivity
  set Kc := M.eqfKc (rpIota 0 0) M.core.A with hKcd
  -- `c ≥ 2` from one admissible scale
  obtain ⟨-, -, -, hε0p, -⟩ := M.core.hC2
  have hc2 : 2 ≤ M.core.c := by
    obtain ⟨hf1, hf2, hP, hi0, hRℓ, hRA, hRρ, hm0, hmass, -, -⟩ := hA (max (max N₀ NA) 3) (by omega)
    haveI := hf1; haveI := hf2
    obtain ⟨hmR, -⟩ := hFA _ (R (max (max N₀ NA) 3)) hP hi0 hRℓ hRA hRρ (by omega) (m _) βR hm0 hβ
      hmass hyA
    exact M.eqc_c_ge (R _) hP hi0 hRℓ hRA hRρ (by omega) (Nh := max (max N₀ NA) 3 - 2) (by omega) hmR
  have hΓ0 := M.core.rdtΓ_nonneg (by linarith) hε0p.le
  have hι : 0 ≤ rpIota 0 0 := by unfold rpIota; positivity
  have hKc0 : 0 ≤ Kc := by
    have hcst := M.core.consts_nonneg
    have := hcst.2.2.2.2.2.1; have := hcst.2.2.2.2.2.2.1; have := hcst.2.2.2.2.2.2.2.1
    have := M.Kp_nonneg
    have hA := M.core.hA2
    have hA0 : 0 ≤ M.core.A := by linarith
    have hc0 : 0 ≤ M.core.c := by linarith
    rw [hKcd]; unfold eqfKc; positivity
  set ε' := ε / (40 * (K * Kc) + 1) with hε'd
  have hKK : 0 ≤ K * Kc := mul_nonneg hK0 hKc0
  have hε' : 0 < ε' := by positivity
  have h40 : 40 * (K * Kc) * ε' ≤ ε := by
    rw [hε'd, ← mul_div_assoc, div_le_iff₀ (by positivity)]; linarith
  -- the choice of `d`, `r'`, `δ`, `N`
  set T := 5 * βR + M.ctE with hTd
  have hE0 := M.ctE_nonneg
  have ha0 := M.ctA_nonneg
  have hT0 : 0 < T := by positivity
  set c' := M.ctA * |Real.log (2 * M.ctA)| with hc'd
  have hc'0 : 0 ≤ c' := by positivity
  set α := betaL L * (1 + 2 * M.ctA) with hαd
  set γ := T + 2 * M.ctA * (T + c') with hγd
  set Cδ := eqfCd L r with hCδd
  set G0 := M.eqsGg r₀ Cδ with hG0d
  obtain ⟨d₁, hd₁⟩ := eqf_beta_ev hβL hT0.le ha0 hc'0 hε'
  obtain ⟨d₂, hd₂⟩ := eqf_wait_ev (M.eqsKWa Cδ * (4 / 3 : ℝ) ^ Cδ) α γ
  obtain ⟨d₃, hd₃⟩ := eqf_half_pow (lt_min hε' (by positivity : (0 : ℝ) < r / 4))
  obtain ⟨r₁, hr₁⟩ := eqf_half_pow hε'
  obtain ⟨n₂, hn₂⟩ := eqf_half_pow (lt_min hε' (lt_min (by positivity : (0 : ℝ) < G0 / 2) hr))
  set d := max (max d₁ d₂) (max d₃ Cδ) with hdd
  set rr := r₁ + 1 with hrrd
  have hd1 : d₁ ≤ d := (le_max_left _ _).trans (le_max_left _ _)
  have hd2 : d₂ ≤ d := (le_max_right _ _).trans (le_max_left _ _)
  have hd3 : d₃ ≤ d := (le_max_left _ _).trans (le_max_right _ _)
  have hdC : Cδ ≤ d := (le_max_right _ _).trans (le_max_right _ _)
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
  refine ⟨1 / (2 * (L : ℝ) ^ (d + rr + 2)), by positivity,
    max (max (max N₀ N₁) (max NA NU)) (n₂ + d + rr + 4 + Cδ), fun N hN x y hx hy' hxy => ?_⟩
  have hN0 : N₀ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _ |>.trans hN)
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _ |>.trans hN)
  have hNA' : NA ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _ |>.trans hN)
  have hNU' : NU ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _ |>.trans hN)
  have hNb : n₂ + d + rr + 4 + Cδ ≤ N := le_trans (le_max_right _ _) hN
  obtain ⟨hf1, hf2, hP, hi0, hRℓ, hRA, hRρ, hm0, hmass, hbr, hb0⟩ := hA N hN0
  haveI := hf1; haveI := hf2
  obtain ⟨hmR, -, hB, -⟩ := hFA N (R N) hP hi0 hRℓ hRA hRρ hNA' (m N) βR hm0 hβ hmass hyA
  obtain ⟨-, hD, -, hgl⟩ := hB (b N) hbr
  have hU := hFU N (R N) hP hi0 hRℓ hRA hRρ hNU' (m N) βR hm0 hβ hmass hyU (b N) hbr
  have hmμ := hN₁ N hN1
  have hm1 : m N * (L : ℝ) ^ (2 * N) ≤ 1 := hmμ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hmG : m N * (L : ℝ) ^ (2 * N) ≤ G0 / 2 :=
    hmμ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hX : m N * (L : ℝ) ^ (2 * N) ≤ M.eqsGm r₀ Kt C₁w C₁t C₁v C₁m Λ₁ Cδ :=
    hmμ.trans (min_le_left _ _)
  have hG : (traj (rgDataM (R N) (m N)) ((L : ℝ) ^ 2) (b N) (b N - m N) (N - 2)).1 ≤ G0 := (hU (N - 2) le_rfl).trans (by linarith)
  set ms := N - 2 - d with hmsd
  have hms1 : rr + 2 ≤ ms := by omega
  have hms2 : n₂ ≤ ms := by omega
  -- `ǧ_{ms}` from the `β` scale
  have hGl := (hD (N - 2) le_rfl).1
  have hTb : 1 / (traj (rgDataM (R N) (m N)) ((L : ℝ) ^ 2) (b N) (b N - m N) (N - 2)).1 ≤ 5 * βR := by
    have : 1 / βR / 5 ≤ (traj (rgDataM (R N) (m N)) ((L : ℝ) ^ 2) (b N) (b N - m N) (N - 2)).1 := hgl
    rw [one_div_le hGl (by positivity)]
    have e : 1 / (5 * βR) = 1 / βR / 5 := by field_simp
    linarith
  have hbs := M.ct_beta_scale (R N) hP hi0 hRℓ hRA hRρ (by omega) hmR hm1 hD hTb ms (by omega)
  have hNd : N - 2 - ms = d := by omega
  rw [hNd] at hbs
  obtain ⟨hpos, hsm⟩ := hd₁ d hd1
  have hgp := (hD ms (by omega)).1
  have hbJ : betaJ (R N) (m N) (b N) (b N - m N) ms = 1 / (traj (rgDataM (R N) (m N)) ((L : ℝ) ^ 2) (b N) (b N - m N) ms).1 := rfl
  rw [hbJ] at hbs
  have hlo := (abs_le.1 hbs).1
  have hhi := (abs_le.1 hbs).2
  have hg_le : (traj (rgDataM (R N) (m N)) ((L : ℝ) ^ 2) (b N) (b N - m N) ms).1 ≤ ε' := by
    have h1 : (d : ℝ) * betaL L - (T + M.ctA * Real.log (2 * ((d : ℝ) * betaL L + T + c'))) ≤
        1 / (traj (rgDataM (R N) (m N)) ((L : ℝ) ^ 2) (b N) (b N - m N) ms).1 := by linarith
    have := one_div_le_one_div_of_le hpos h1
    rw [one_div_one_div] at this
    linarith
  have hlog : Real.log (2 * ((d : ℝ) * betaL L + T + c')) ≤ 2 * ((d : ℝ) * betaL L + T + c') := by
    have hx : 0 < 2 * ((d : ℝ) * betaL L + T + c') := by positivity
    linarith [Real.log_le_sub_one_of_pos hx]
  have hαγ : 1 / (traj (rgDataM (R N) (m N)) ((L : ℝ) ^ 2) (b N) (b N - m N) ms).1 ≤ α * d + γ := by
    have := mul_le_mul_of_nonneg_left hlog ha0
    rw [hαd, hγd]; linarith
  have hαγ0 : 0 < α * d + γ := by positivity
  have hg_ge : 1 / (α * d + γ) ≤ (traj (rgDataM (R N) (m N)) ((L : ℝ) ^ 2) (b N) (b N - m N) ms).1 := by
    have := one_div_le_one_div_of_le (by positivity) hαγ
    rwa [one_div_one_div] at this
  -- the waiting condition
  have hKWa0 : 0 ≤ M.eqsKWa Cδ := by
    have hΓ : 0 < M.core.rdtΓ := M.core.eqs_rdtΓ_pos (by linarith) hε0p.le
    have hcst := M.core.consts_nonneg
    have := hcst.2.2.2.2.2.1
    have hA0 : 0 < M.core.A := by linarith [M.core.hA2]
    have hθ0 : 0 ≤ kθ0 L M.core.A M.core.C₀o M.core.ηo := by
      unfold kθ0
      exact mul_nonneg M.core.hC₀o (add_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _))
    have := M.eqsTh_pos 0
    have := M.eqsTh_pos Cδ
    have hc0 : 0 < M.core.c := by linarith
    have hTw0 : 0 ≤ M.eqsTw := by unfold eqsTw; positivity
    have hTk0 : 0 ≤ M.eqsTk := by unfold eqsTk; positivity
    have hK20 : 0 ≤ M.eqsK2 := by unfold eqsK2 zabIota; positivity
    unfold eqsKWa eqsKW eqsKWt; positivity
  have hW : (3 / 4 : ℝ) ^ ((N - Cδ) - ms) * M.eqsKWa Cδ ≤ (traj (rgDataM (R N) (m N)) ((L : ℝ) ^ 2) (b N) (b N - m N) ms).1 ^ 2 := by
    have hJm : (N - Cδ) - ms + Cδ = d + 2 := by omega
    have hp : (3 / 4 : ℝ) ^ ((N - Cδ) - ms) ≤ (3 / 4) ^ d * (4 / 3) ^ Cδ := by
      have h1 : (3 / 4 : ℝ) ^ ((N - Cδ) - ms) * (3 / 4) ^ Cδ ≤ (3 / 4) ^ d := by
        rw [← pow_add, hJm]; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      have h2 : (3 / 4 : ℝ) ^ Cδ * (4 / 3) ^ Cδ = 1 := by rw [← mul_pow]; norm_num
      calc (3 / 4 : ℝ) ^ ((N - Cδ) - ms) = (3 / 4) ^ ((N - Cδ) - ms) * (3 / 4) ^ Cδ * (4 / 3) ^ Cδ := by
            rw [mul_assoc, h2, mul_one]
        _ ≤ (3 / 4) ^ d * (4 / 3) ^ Cδ := mul_le_mul_of_nonneg_right h1 (by positivity)
    have hw := hd₂ d hd2
    have h3 : (3 / 4 : ℝ) ^ d * (4 / 3) ^ Cδ * M.eqsKWa Cδ ≤ 1 / (α * d + γ) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; linarith [show (3 / 4 : ℝ) ^ d * (M.eqsKWa Cδ * (4 / 3) ^ Cδ) *
        (α * d + γ) ^ 2 = (3 / 4) ^ d * (4 / 3) ^ Cδ * M.eqsKWa Cδ * (α * d + γ) ^ 2 by ring]
    have h4 : 1 / (α * d + γ) ^ 2 ≤ (traj (rgDataM (R N) (m N)) ((L : ℝ) ^ 2) (b N) (b N - m N) ms).1 ^ 2 := by
      rw [one_div, ← inv_pow, ← one_div]; exact pow_le_pow_left₀ (by positivity) hg_ge 2
    calc (3 / 4 : ℝ) ^ ((N - Cδ) - ms) * M.eqsKWa Cδ ≤ (3 / 4) ^ d * (4 / 3) ^ Cδ * M.eqsKWa Cδ :=
          mul_le_mul_of_nonneg_right hp hKWa0
      _ ≤ _ := h3.trans h4
  -- `a_{ms}`
  have hz_eq := zA_pos L (m N) (k := ms) (by omega)
  have hpow1 : (((L : ℝ) ^ ms) ^ 2)⁻¹ ≤ (1 / 2 : ℝ) ^ ms := by
    have h1 : (1 : ℝ) ≤ (L : ℝ) ^ ms := one_le_pow₀ hL1
    have h2 : (L : ℝ) ^ ms ≤ ((L : ℝ) ^ ms) ^ 2 := by
      rw [sq]; exact le_mul_of_one_le_left (by positivity) h1
    rw [← one_div]
    exact (one_div_le_one_div_of_le (by positivity) h2).trans (eqf_Lpow_inv_le hL2 ms)
  have hn2 := hn₂ ms hms2
  have hm2a : m N * ((L : ℝ) ^ (ms + 1)) ^ 2 ≤ m N * (L : ℝ) ^ (2 * N) := by
    refine mul_le_mul_of_nonneg_left ?_ hm0.le
    rw [← pow_mul]; exact pow_le_pow_right₀ hL1 (by omega)
  have hm2b : m N * ((L : ℝ) ^ (ms + 1)) ^ 2 ≤ (1 / 2 : ℝ) ^ d := by
    have e : (L : ℝ) ^ (2 * N) = ((L : ℝ) ^ (ms + 1)) ^ 2 * ((L : ℝ) ^ (d + 1)) ^ 2 := by
      rw [← mul_pow, ← pow_add, ← pow_mul]; congr 1; omega
    have h1 : m N * ((L : ℝ) ^ (ms + 1)) ^ 2 * ((L : ℝ) ^ (d + 1)) ^ 2 ≤ 1 := by
      rw [mul_assoc, ← e]; exact hm1
    have h3 : (2 : ℝ) ^ d ≤ (L : ℝ) ^ d := pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hL2) d
    have h4 : (L : ℝ) ^ d ≤ ((L : ℝ) ^ (d + 1)) ^ 2 := by
      have : (L : ℝ) ^ d ≤ (L : ℝ) ^ (2 * (d + 1)) := pow_le_pow_right₀ hL1 (by omega)
      rwa [pow_mul, ← pow_mul, mul_comm, pow_mul] at this
    have hB : 0 < ((L : ℝ) ^ (d + 1)) ^ 2 := by positivity
    have h5 : m N * ((L : ℝ) ^ (ms + 1)) ^ 2 ≤ 1 / ((L : ℝ) ^ (d + 1)) ^ 2 := by
      rw [le_div_iff₀ hB]; exact h1
    have h6 : 1 / ((L : ℝ) ^ (d + 1)) ^ 2 ≤ 1 / (2 : ℝ) ^ d :=
      one_div_le_one_div_of_le (by positivity) (h3.trans h4)
    rw [one_div_pow]; exact h5.trans h6
  have hz : zA L (m N) ms ≤ G0 := by
    rw [hz_eq]
    have : (1 / 2 : ℝ) ^ ms ≤ G0 / 2 := hn2.trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hz2 : zA L (m N) ms ≤ 2 * ε' := by
    rw [hz_eq]
    have a : (1 / 2 : ℝ) ^ ms ≤ ε' := hn2.trans (min_le_left _ _)
    have b' : (1 / 2 : ℝ) ^ d ≤ ε' := (hd₃ d hd3).trans (min_le_left _ _)
    linarith
  -- geometry
  have hNsplit : (L : ℝ) ^ N = (L : ℝ) ^ (ms - rr) * (L : ℝ) ^ (d + rr + 2) := by
    rw [← pow_add]; congr 1; omega
  have hDge : (4 : ℝ) ≤ (L : ℝ) ^ (ms - rr) := by
    have : (2 : ℝ) ^ 2 ≤ (L : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hL2) 2
    have h2 : (L : ℝ) ^ 2 ≤ (L : ℝ) ^ (ms - rr) := pow_le_pow_right₀ hL1 (by omega)
    norm_num at this; linarith
  have hxy' : supNorm (latPtN L N y - latPtN L N x) ≤ L ^ (ms - rr) := by
    have h := eqf_supNorm_latPt_sub (L ^ N) x y
    have hc : ((L ^ N : ℕ) : ℝ) = (L : ℝ) ^ N := by push_cast; ring
    rw [hc] at h
    have hδ : (L : ℝ) ^ N * dist x y ≤ (L : ℝ) ^ (ms - rr) / 2 := by
      have := mul_le_mul_of_nonneg_left hxy.le (by positivity : (0 : ℝ) ≤ (L : ℝ) ^ N)
      rw [hNsplit] at this ⊢
      have e : (L : ℝ) ^ (ms - rr) * (L : ℝ) ^ (d + rr + 2) * (1 / (2 * (L : ℝ) ^ (d + rr + 2))) =
          (L : ℝ) ^ (ms - rr) / 2 := by field_simp
      linarith
    have : (supNorm (latPtN L N y - latPtN L N x) : ℝ) ≤ ((L ^ (ms - rr) : ℕ) : ℝ) := by
      push_cast; unfold latPtN; linarith
    exact_mod_cast this
  have hxJ : ∀ z : Lam 2 L N, supNorm (z - latPtN L N x) ≤ L ^ (ms - rr) →
      N - Cδ ≤ Obs.coal L (0 : Lam 2 L N) z := by
    refine eqc_region hL2 (latPtN L N x) ?_
    have hsx := eqf_supNorm_latPt_ge (L ^ N) x
    have hc : ((L ^ N : ℕ) : ℝ) = (L : ℝ) ^ N := by push_cast; ring
    rw [hc] at hsx
    have hxn : r ≤ ‖x‖ := by rwa [dist_zero_right] at hx
    have hJ : (L : ℝ) ^ (N - Cδ) ≤ (L : ℝ) ^ N * r / 2 := by
      have e : (L : ℝ) ^ N = (L : ℝ) ^ (N - Cδ) * (L : ℝ) ^ Cδ := by rw [← pow_add]; congr 1; omega
      have h1 : (L : ℝ) ^ (N - Cδ) * (2 / r) ≤ (L : ℝ) ^ N := by
        rw [e]; exact mul_le_mul_of_nonneg_left hCdpow (by positivity)
      have e2 : (L : ℝ) ^ (N - Cδ) * (2 / r) = 2 * (L : ℝ) ^ (N - Cδ) / r := by ring
      rw [e2, div_le_iff₀ hr] at h1
      linarith
    have hDs : 2 * (L : ℝ) ^ (ms - rr) ≤ (L : ℝ) ^ N * r / 2 := by
      have h1 : (1 / 2 : ℝ) ^ d ≤ r / 4 := (hd₃ d hd3).trans (min_le_right _ _)
      have h2 : 1 / (L : ℝ) ^ (d + rr + 2) ≤ (1 / 2 : ℝ) ^ d / 4 := by
        have h3 := eqf_Lpow_inv_le hL2 (d + rr + 2)
        have h4 : (1 / 2 : ℝ) ^ (d + rr + 2) ≤ (1 / 2) ^ d / 4 := by
          rw [pow_add, pow_add]
          have : (1 / 2 : ℝ) ^ rr ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
          have h5 : (0 : ℝ) ≤ (1 / 2) ^ d := by positivity
          have h6 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this h5)
            (by positivity : (0 : ℝ) ≤ (1 / 2) ^ 2)
          have e : (1 / 2 : ℝ) ^ d * 1 * (1 / 2) ^ 2 = (1 / 2) ^ d / 4 := by ring
          linarith
        linarith
      have e : (L : ℝ) ^ (ms - rr) = (L : ℝ) ^ N * (1 / (L : ℝ) ^ (d + rr + 2)) := by
        rw [hNsplit]; field_simp
      rw [e]
      have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ (L : ℝ) ^ N)
      have h6 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (L : ℝ) ^ N)
      have h7 : 0 ≤ (L : ℝ) ^ N * r := by positivity
      linarith
    have hLr : 1 ≤ (L : ℝ) ^ N * r := by
      have h1 : (1 / 2 : ℝ) ^ N ≤ r :=
        (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega : n₂ ≤ N)).trans
          (hn₂ n₂ le_rfl |>.trans ((min_le_right _ _).trans (min_le_right _ _)))
      have h2 : (2 : ℝ) ^ N ≤ (L : ℝ) ^ N := pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hL2) N
      have h3 : (2 : ℝ) ^ N * (1 / 2) ^ N = 1 := by rw [← mul_pow]; norm_num
      have a := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 ^ N)
      have b' := mul_le_mul_of_nonneg_right h2 hr.le
      linarith
    have hxs : (L : ℝ) ^ N * r - 1 / 2 ≤ (supNorm (latPtN L N x) : ℝ) := by
      have := mul_le_mul_of_nonneg_left hxn (by positivity : (0 : ℝ) ≤ (L : ℝ) ^ N)
      unfold latPtN; linarith
    have : (((L ^ (N - Cδ) + 2 * L ^ (ms - rr) : ℕ)) : ℝ) ≤ ((2 * supNorm (latPtN L N x) : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast this
  -- the bound of `eqs_pairs`
  have hPb := hPair Cδ (R N) hP hi0 hRℓ hRA hRρ (by omega) (Nh := N - 2) (by omega) hmR hD hG hX
    (ms := ms) (r := rr) (J := N - Cδ) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) hz hW (latPtN L N x) (latPtN L N y) hxJ hxy'
  have hc0 : 0 ≤ M.core.c := by linarith
  have hA0 : 0 ≤ ((R N).withMsq (m N)).A := (Fact.out : 0 < (R N).A).le
  have hQ0 := M.eqc_cddRel_nonneg rr hc0 hε0p.le hgp.le (zA_nonneg L hm0.le ms) hι hA0
  have hsc := eqf_scale (P := Pconn L N (1 / b N) (latPtN L N x) - Pconn L N (1 / b N) (latPtN L N y))
    (g := (traj (rgDataM (R N) (m N)) ((L : ℝ) ^ 2) (b N) (b N - m N) (N - 2)).1) hb0 hβ hGl hgl hK0 hQ0 hPb
  have hQ := M.eqf_cddRel_le (g := (traj (rgDataM (R N) (m N)) ((L : ℝ) ^ 2) (b N) (b N - m N) ms).1) (z := zA L (m N) ms) (ι := rpIota 0 0)
    (A := ((R N).withMsq (m N)).A) rr hgp.le ((hD ms (by omega)).2.1.trans M.eps_le)
    (zA_nonneg L hm0.le ms) hι hA0 hc0 hΓ0
  have hAe : ((R N).withMsq (m N)).A = M.core.A := hRA
  have hKce : M.eqfKc (rpIota 0 0) ((R N).withMsq (m N)).A = Kc := by rw [hAe]
  rw [hKce] at hQ
  have he : 1 / (L : ℝ) ^ rr ≤ ε' :=
    (eqf_Lpow_inv_le hL2 rr).trans (hr₁ rr (by omega))
  have hQ' : M.cddRel M.Kp (traj (rgDataM (R N) (m N)) ((L : ℝ) ^ 2) (b N) (b N - m N) ms).1
      (zA L (m N) ms) (rpIota 0 0) ((R N).withMsq (m N)).A rr ≤ Kc * (4 * ε') := by
    refine hQ.trans (mul_le_mul_of_nonneg_left ?_ hKc0)
    linarith
  unfold clF thetaEpsSq
  rw [← sub_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (βR * b N) ^ (2 / 3 : ℝ))]
  refine hsc.trans ?_
  have := mul_le_mul_of_nonneg_left hQ' hK0
  linarith

end MasterFacts

end

end Spin2
