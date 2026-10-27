import Spin2.Case2.Case2
import Obs2.Flow.Tau2Hist

/-!
# `Case2Loop` from the explicit `𝔫^{(2)}`: reduction to bulk inputs, and `thm:multiscale` with it

Along `t = traj (rgDataM R m) L² b μ₀` (history from `obsInit .two V P`), with the step
covariances `C_k = covT k`, the couplings `g_k = gT k` (`= ǧ_{r,k}Z_{k+1}²`), `ν♭_k = nuT k`
(`= μ_kZ_{k+1}/L^{2k} - a_km²`), `δ_k = dlT k`, `S_j = sT j = ∑_{k<j}rowS_{C_k}(a)`,
`𝔩_{w_j} = lwT j` (bubble of `w_j = ∑_{k<j}C_k`), the drift terms `drT`, `dxT`:

* **`nn2_eq`** (`Obs2.frakN2_hist`, exact, `k < N_h`, `ValidAt` below `N_h`):
  `𝔫^{(2)}_k = (ν♭_k + 4g_kδ_k)S_{k+1} - ν♭_kS_k - g_k(𝔩_{w_{k+1}} - 𝔩_{w_k}) - drT_k + dxT_k`;
* `Case2Bulk` (named bulk input; `V`-independent): the one-loop bubble value
  `‖g_k(𝔩_{w_{k+1}} - 𝔩_{w_k}) - (β/3)ǧ_k‖ ≤ B₁(ǧ_k² + ǧ_ka_k)`, the second-order `ν` flow
  `‖(ν♭_{k+1} - ν'_k)S_{k+1}‖ ≤ B₂(ǧ_k² + ǧ_ka_k)` (`ν'_k = ν♭_k + 4g_kδ_k`), the drift
  `‖drT_k‖ + ‖dxT_k‖ ≤ B₃ǧ_k²`, and `‖ν♭_kS_k‖ ≤ c_qǧ_k` (`k ≤ N_h`);
* **`case2Loop_of`**: `Case2Bulk` ⇒ `Case2Loop` with `q_k = ν♭_kS_k`, `B = B₁ + B₂ + B₃`,
  `B' = 3B + β/3 + c_q(M + 1)` (given `0 ≤ ǧ ≤ 1`, `a ≤ 2`, `ǧ_{k+1} ≤ Mǧ_k`, `B'ǧ_k ≤ 1/8`);
* `MultiConcl2B`, `multiConcl2B_of`, **`thm_multiscale_case2B`**: `thm:multiscale` for
  `λ̂ = μ_a/μ_{a,0}` conditional on `RGInput`, `Case2Rel`, `Case2Bulk` and the smallness
  `B'ǧ_k ≤ 1/8` (no `Case2Loop`), under the master constants (`ValidConcl` of `thm_flow_master`).
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Step2.D2

variable {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  (P : Obs2.ObsPts 2 L N) (V : Obs2.OCoup .two)

/-- The step covariance `C_k` along the trajectory. -/
def covT (m b μ₀ : ℝ) (k : ℕ) : Matrix (Lam 2 L N) (Lam 2 L N) ℂ :=
  Obs2.histCovO (R.withMsq m) (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k

/-- `g_k = ǧ_{r,k}Z_{k+1}²` along the trajectory. -/
def gT (m b μ₀ : ℝ) (k : ℕ) : ℂ :=
  Obs2.gH (R.withMsq m) (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k

/-- `ν♭_k = μ_kZ_{k+1}/L^{2k} - a_km²` along the trajectory. -/
def nuT (m b μ₀ : ℝ) (k : ℕ) : ℂ :=
  Obs2.nuFH (R.withMsq m) (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k

/-- `δ_k = C_k(e₁,0) - C_k(0,0)` along the trajectory. -/
def dlT (m b μ₀ : ℝ) (k : ℕ) : ℂ :=
  Obs2.dlH (R.withMsq m) (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k

/-- `S_j = ∑_{k<j} rowS_{C_k}(a)`. -/
def sT (m b μ₀ : ℝ) (j : ℕ) : ℂ := ∑ k ∈ range j, Obs2.rowS (covT R m b μ₀ k) P.a

/-- The bubble `𝔩_{w_j}(a)` of the accumulated covariance `w_j = ∑_{k<j}C_k`. -/
def lwT (m b μ₀ : ℝ) (j : ℕ) : ℂ := Obs2.lfunC (∑ k ∈ range j, covT R m b μ₀ k) P.a

/-- The drift of the tadpole part: `4δ_j∑_{k<j}(g_j - g_k)rowS_{C_k}(a)`. -/
def drT (m b μ₀ : ℝ) (j : ℕ) : ℂ :=
  4 * dlT R m b μ₀ j * ∑ k ∈ range j, (gT R m b μ₀ j - gT R m b μ₀ k) * Obs2.rowS (covT R m b μ₀ k) P.a

/-- The drift of the bubble part: `∑_{k<j}(g_j - g_k)𝔩_{C_k,C_j}(a)`. -/
def dxT (m b μ₀ : ℝ) (j : ℕ) : ℂ :=
  ∑ k ∈ range j, (gT R m b μ₀ j - gT R m b μ₀ k) * Obs2.lfunX (covT R m b μ₀ k) (covT R m b μ₀ j) P.a

/-- `q_k = ν♭_kS_k`. -/
def qT (m b μ₀ : ℝ) (k : ℕ) : ℂ := nuT R m b μ₀ k * sT R P m b μ₀ k

/-- **`𝔫^{(2)}_k` explicitly** along the trajectory. -/
theorem nn2_eq {Nh : ℕ} {m b μ₀ : ℝ} (hV : ∀ i < Nh, ValidAt (R.withMsq m) i) {k : ℕ}
    (hk : k < Nh) :
    nn2 R P V m b μ₀ k = (nuT R m b μ₀ k + 4 * gT R m b μ₀ k * dlT R m b μ₀ k) * sT R P m b μ₀ (k + 1) -
      nuT R m b μ₀ k * sT R P m b μ₀ k - gT R m b μ₀ k * (lwT R P m b μ₀ (k + 1) - lwT R P m b μ₀ k) -
      drT R P m b μ₀ k + dxT R P m b μ₀ k :=
  Obs2.frakN2_hist (R.withMsq m) P (Obs2.obsInit .two V P) _ hV (Obs2.obsInit_isObs .two V P) hk

/-- **Named bulk input of the Case-(2) one-loop identification** (`V`-independent): the bubble
value, the second-order `ν` flow, the drift of `g`, and the size of `ν♭S`. -/
def Case2Bulk (Nh : ℕ) (m b μ₀ B₁ B₂ B₃ cq : ℝ) : Prop :=
  (∀ k < Nh, ‖gT R m b μ₀ k * (lwT R P m b μ₀ (k + 1) - lwT R P m b μ₀ k) -
      ((betaL L / 3 * (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 : ℝ) : ℂ)‖ ≤
    B₁ * (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ^ 2 +
      B₁ * (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 * zA L m k) ∧
  (∀ k < Nh, ‖(nuT R m b μ₀ (k + 1) - (nuT R m b μ₀ k + 4 * gT R m b μ₀ k * dlT R m b μ₀ k)) *
      sT R P m b μ₀ (k + 1)‖ ≤
    B₂ * (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ^ 2 +
      B₂ * (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 * zA L m k) ∧
  (∀ k < Nh, ‖drT R P m b μ₀ k‖ + ‖dxT R P m b μ₀ k‖ ≤
    B₃ * (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ^ 2) ∧
  (∀ k ≤ Nh, ‖qT R P m b μ₀ k‖ ≤ cq * (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1)

/-- The constant `B'` of `Case2Loop` obtained from `Case2Bulk`. -/
def case2BK (β B₁ B₂ B₃ cq M : ℝ) : ℝ := 3 * (B₁ + B₂ + B₃) + β / 3 + cq * (M + 1)

variable {R P V}

/-- **`Case2Loop` from `Case2Bulk`**, with `q_k = ν♭_kS_k`. -/
theorem case2Loop_of {Nh : ℕ} {m b μ₀ B₁ B₂ B₃ cq M : ℝ}
    (hV : ∀ i < Nh, ValidAt (R.withMsq m) i) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hB₃ : 0 ≤ B₃)
    (hcq : 0 ≤ cq) (hβ : 0 ≤ betaL L)
    (hg : ∀ k < Nh, 0 ≤ (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1)
    (ha : ∀ k < Nh, 0 ≤ zA L m k ∧ zA L m k ≤ 2)
    (hM : ∀ k < Nh, (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (k + 1)).1 ≤
      M * (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1)
    (hsm : ∀ k < Nh, case2BK (betaL L) B₁ B₂ B₃ cq M *
      (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1 / 8)
    (hbulk : Case2Bulk R P Nh m b μ₀ B₁ B₂ B₃ cq) :
    Case2Loop R P V Nh m b μ₀ (B₁ + B₂ + B₃) (case2BK (betaL L) B₁ B₂ B₃ cq M) cq := by
  obtain ⟨h1, h2, h3, h4⟩ := hbulk
  refine ⟨qT R P m b μ₀, by simp [qT, sT], h4, fun k hk => ?_⟩
  set g := (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 with hgd
  set g' := (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (k + 1)).1
  set a := zA L m k
  set c : ℂ := ((betaL L / 3 * g : ℝ) : ℂ) with hcd
  set E1 := gT R m b μ₀ k * (lwT R P m b μ₀ (k + 1) - lwT R P m b μ₀ k) - c
  set E2 := (nuT R m b μ₀ (k + 1) - (nuT R m b μ₀ k + 4 * gT R m b μ₀ k * dlT R m b μ₀ k)) *
      sT R P m b μ₀ (k + 1)
  have hE : -nn2 R P V m b μ₀ k - c + (qT R P m b μ₀ (k + 1) - qT R P m b μ₀ k) =
      E1 + E2 + drT R P m b μ₀ k - dxT R P m b μ₀ k := by
    rw [nn2_eq R P V hV hk]
    simp only [qT, E1, E2]
    ring
  have hg0 := (hg k hk).1
  have ha0 := (ha k hk).1
  have hga : 0 ≤ g * a := mul_nonneg hg0 ha0
  have hEn : ‖-nn2 R P V m b μ₀ k - c + (qT R P m b μ₀ (k + 1) - qT R P m b μ₀ k)‖ ≤
      (B₁ + B₂ + B₃) * g ^ 2 + (B₁ + B₂ + B₃) * g * a := by
    rw [hE]
    have t1 : ‖E1 + E2 + drT R P m b μ₀ k - dxT R P m b μ₀ k‖ ≤
        ‖E1‖ + ‖E2‖ + (‖drT R P m b μ₀ k‖ + ‖dxT R P m b μ₀ k‖) := by
      refine (norm_sub_le _ _).trans ?_
      have := norm_add₃_le (a := E1) (b := E2) (c := drT R P m b μ₀ k)
      linarith
    have t2 : 0 ≤ B₃ * (g * a) := mul_nonneg hB₃ hga
    have e1 := h1 k hk
    have e2 := h2 k hk
    have e3 := h3 k hk
    have : (B₁ + B₂ + B₃) * g ^ 2 + (B₁ + B₂ + B₃) * g * a =
        (B₁ * g ^ 2 + B₁ * g * a) + (B₂ * g ^ 2 + B₂ * g * a) + B₃ * g ^ 2 + B₃ * (g * a) := by
      ring
    rw [this]
    linarith
  refine ⟨?_, ?_, hEn⟩
  all_goals
    have hnn : nn2 R P V m b μ₀ k =
        -(-nn2 R P V m b μ₀ k - c + (qT R P m b μ₀ (k + 1) - qT R P m b μ₀ k)) - c +
          qT R P m b μ₀ (k + 1) - qT R P m b μ₀ k := by ring
    have hc : ‖c‖ = betaL L / 3 * g := by
      rw [hcd, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hq1 : ‖qT R P m b μ₀ (k + 1)‖ ≤ cq * (M * g) :=
      (h4 (k + 1) (by omega)).trans (mul_le_mul_of_nonneg_left (hM k hk) hcq)
    have hq0 : ‖qT R P m b μ₀ k‖ ≤ cq * g := h4 k hk.le
    have hn : ‖nn2 R P V m b μ₀ k‖ ≤ case2BK (betaL L) B₁ B₂ B₃ cq M * g := by
      rw [hnn]
      have t1 : ‖-(-nn2 R P V m b μ₀ k - c + (qT R P m b μ₀ (k + 1) - qT R P m b μ₀ k)) - c +
          qT R P m b μ₀ (k + 1) - qT R P m b μ₀ k‖ ≤
          ‖-nn2 R P V m b μ₀ k - c + (qT R P m b μ₀ (k + 1) - qT R P m b μ₀ k)‖ + ‖c‖ +
            ‖qT R P m b μ₀ (k + 1)‖ + ‖qT R P m b μ₀ k‖ := by
        set X := -nn2 R P V m b μ₀ k - c + (qT R P m b μ₀ (k + 1) - qT R P m b μ₀ k)
        have a1 := norm_sub_le (-X - c + qT R P m b μ₀ (k + 1)) (qT R P m b μ₀ k)
        have a2 := norm_add_le (-X - c) (qT R P m b μ₀ (k + 1))
        have a3 := norm_sub_le (-X) c
        have a4 : ‖-X‖ = ‖X‖ := norm_neg X
        linarith
      have hBn : 0 ≤ B₁ + B₂ + B₃ := by linarith
      have hg2 : (B₁ + B₂ + B₃) * g ^ 2 ≤ (B₁ + B₂ + B₃) * g := by
        refine mul_le_mul_of_nonneg_left ?_ hBn
        rw [sq]; exact mul_le_of_le_one_left hg0 (hg k hk).2
      have hga2 : (B₁ + B₂ + B₃) * g * a ≤ (B₁ + B₂ + B₃) * g * 2 :=
        mul_le_mul_of_nonneg_left (ha k hk).2 (mul_nonneg hBn hg0)
      have : case2BK (betaL L) B₁ B₂ B₃ cq M * g =
          (B₁ + B₂ + B₃) * g + (B₁ + B₂ + B₃) * g * 2 + betaL L / 3 * g + cq * (M * g) + cq * g := by
        unfold case2BK; ring
      rw [this]
      linarith
  · exact hn.trans (hsm k hk)
  · exact hn

/-- **`thm:multiscale` with `λ̂ = μ_a/μ_{a,0}`**, conditional on `RGInput`, `Case2Rel` and the
bulk input `Case2Bulk` (with the smallness `B'ǧ_k ≤ 1/8`, `B' = case2BK β B₁ B₂ B₃ c_q M`,
`M = 1 + 3β/2 + c_g`). -/
def MultiConcl2B (L : ℕ) [NeZero L] (ℓ A ρ κ cg cm cT ε Ke KZ KG : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ →
  ∀ Nh : ℕ, Nh + 2 ≤ N →
  ∀ m ∈ mRange L N, ∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
  ∀ (P : Obs2.ObsPts 2 L N) (V : Obs2.OCoup .two) (B₁ B₂ B₃ cq cδ KP : ℝ), 0 ≤ B₁ → 0 ≤ B₂ →
    0 ≤ B₃ → 0 ≤ cq → 0 ≤ cδ → 0 ≤ KP → Obs2.OCoup2.mua V ≠ 0 → Case2Rel R P V Nh m b μ₀ cδ →
    Case2Bulk R P Nh m b μ₀ B₁ B₂ B₃ cq →
    (∀ k < Nh, case2BK (betaL L) B₁ B₂ B₃ cq (1 + 3 / 2 * betaL L + cg) *
      (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1 / 8) →
    RGInput R Nh m b μ₀ (lamHat2 R P V m b μ₀) KP →
  ∀ x : Lam 2 L N, x ≠ 0 → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∃ jp : ℕ, (jp : ℤ) = jPhys L N (eucl x / (L : ℝ) ^ N) ∧
      jp ≤ Obs.coal L (0 : Lam 2 L N) x ∧ Obs.coal L (0 : Lam 2 L N) x ≤ jp + 1 ∧
      |Pconn L N (1 / b) x - thetaSq R m b μ₀ jp| ≤
        multK L cg Ke KZ KG (max (lamRelK (betaL L) cg (B₁ + B₂ + B₃)
          (case2BK (betaL L) B₁ B₂ B₃ cq (1 + 3 / 2 * betaL L + cg)) cq cδ
          (eRange (betaL L) Ke 1) 4) 0) KP * thetaSq R m b μ₀ jp / betaJ R m b μ₀ jp

/-- **`MultiConcl2B` from `MultiConcl2` and `ValidConcl`** (the same constants). -/
theorem multiConcl2B_of {L : ℕ} [NeZero L] {ℓ A ρ κ cg cm cT ε Ke KZ KG : ℝ} (hL2 : (2 : ℝ) ≤ L)
    (hε1 : ε ≤ 1) (hVC : ValidConcl L ℓ A ρ κ cg cm cT ε)
    (hM2 : MultiConcl2 L ℓ A ρ κ cg cm cT ε Ke KZ KG) : MultiConcl2B L ℓ A ρ κ cg cm cT ε Ke KZ KG := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ Nh hNh m hm b μ₀ hadm P V B₁ B₂ B₃ cq cδ KP hB₁ hB₂ hB₃ hcq
    hcδ hKP hmu hrel hbulk hsm hrg x hx hj
  obtain ⟨hV, hMr⟩ := hVC N R hP hi0 hRℓ hRA hRρ (by omega) Nh hNh m hm
  have hβ : 0 ≤ betaL L := by
    unfold betaL
    have : 0 < Real.log L := Real.log_pos (by linarith only [hL2])
    have := Real.pi_pos
    positivity
  have hmass : m * ((L : ℝ) ^ (Nh + 1)) ^ 2 ≤ 1 := by
    have := msq_horizon (L := (L : ℝ)) (by linarith only [hL2]) hm.2 (Nh := Nh) (k := 0)
      (by omega)
    simpa using this
  have hloop : Case2Loop R P V Nh m b μ₀ (B₁ + B₂ + B₃)
      (case2BK (betaL L) B₁ B₂ B₃ cq (1 + 3 / 2 * betaL L + cg)) cq := by
    refine case2Loop_of hV hB₁ hB₂ hB₃ hcq hβ (fun k hk => ⟨(hadm.1 k hk.le).1.le,
      (hadm.1 k hk.le).2.1.trans hε1⟩) (fun k hk => ⟨zA_nonneg L hm.1.le k, zA_le_two
        (by linarith only [hL2]) ?_⟩) (hMr b μ₀ hadm) hsm hbulk
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hm.1.le) hmass
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by linarith only [hL2])
      (by omega)) 2
  exact hM2 N R hP hi0 hRℓ hRA hRρ Nh hNh m hm b μ₀ hadm P V _ _ cq cδ KP
    (by linarith) hcδ hKP hmu hrel hloop hrg x hx hj

/-- **Expected result `thm:multiscale` for `λ̂ = μ_a/μ_{a,0}`**, conditional on `thm:rginput`
(`RGInput`), the observable remainders `Case2Rel` and the bulk input `Case2Bulk` (with the
smallness `B'ǧ_k ≤ 1/8`): one set of constants with `FlowC2Concl`, `ε ≤ 1`, `BetaConcl`,
`LamConcl`, `MultiConcl2B`. -/
theorem thm_multiscale_case2B : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ κ cg cm cT ε Ke Cf Cb KZ KG : ℝ, FlowC2Concl L ℓ A ρ κ cg cm cT ε Ke Cf Cb ∧ ε ≤ 1 ∧
      BetaConcl L ℓ A ρ κ cg cm cT ε Ke Cb ∧ LamConcl L ℓ A ρ κ cg cm cT ε Ke ∧
      MultiConcl2B L ℓ A ρ κ cg cm cT ε Ke KZ KG := by
  obtain ⟨L₀, hL₀⟩ := thm_flow_master_all (fun _ _ => True) (fun _ => ⟨0, fun _ _ => trivial⟩)
    (fun _ _ _ _ _ => True) (fun _ _ _ _ => Filter.Eventually.of_forall fun _ => trivial)
  refine ⟨max L₀ 2, fun L _ hL => ?_⟩
  obtain ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, Cf, Cb, KZ, KG, hC2, hε1, -, -, hSp, hMag, hB, -, hVC, -⟩ :=
    hL₀ L (le_trans (le_max_left _ _) hL)
  have hL2 : 2 ≤ L := le_trans (le_max_right _ _) hL
  have hL2' : (2 : ℝ) ≤ L := by exact_mod_cast hL2
  have hM := multiConcl_of hL2 hε1 hSp hMag
  exact ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, Cf, Cb, KZ, KG, hC2, hε1, hB, lamConcl_of hL2' hε1 hSp,
    multiConcl2B_of hL2' hε1 hVC (multiConcl2_of hL2' hε1 hSp hM)⟩

end

end Spin2
