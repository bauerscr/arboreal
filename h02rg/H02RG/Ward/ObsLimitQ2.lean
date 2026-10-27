import Ward.ObsLimitQ1

/-!
# The infinite-volume truncated four-point function (Case (2))

For a fixed `x ∈ ℤ^d`, `x ≠ 0`, along `(Λ_N, ctr_N, ctr_N + x)` (Case (2), `l₀ = λ̄`):

* `qP2 … x j`: the `q` increment of step `j`, `N`-independent (`qP2_char`, `Obs.pair_consist`);
* `Qtwo … x = ∑_j qP2 x j / λ̄²`;
* `qN2_rate`: `|q_N/λ̄² - Qtwo x| ≤ K L^{-(d-2)N}` (uniform in `m² ≥ 0`, `|b₀| ≤ λ̄`);
* `Qtwo_joint`: joint continuity on `[0, ∞) × B(0, λ̄)`;
* `trunc_tendsto`: at `m² > 0`,
  `⟨ψ̄₀ψ₀ ψ̄_xψ_x⟩ - ⟨ψ̄₀ψ₀⟩⟨ψ̄_xψ_x⟩ → Qtwo x` as `N → ∞`.

The bounds used along the Case (2) flow at `(ctr_N, b)` are collected in `PairHyp2`
(from `Obs.Vobs_recursion_two` and `Obs.Vobs_bd`).
-/

namespace Ward

noncomputable section

open Finset Grassmann Loc Step Obs FRD PtCorr Metric Filter Topology

variable {d L : ℕ} [NeZero L] {A ℓ₀ lbar C κ : ℝ} {V₀c : ℝ → ℂ → Vcoup}

/-- `q = q_a + q_b` (Case (2)). -/
abbrev qS2 (W : Coup .two) : ℂ := qaOf .two W + qbOf .two W

variable (d L) in
/-- **Bounds along the Case (2) flow** at `(ctr_N, b)`, `b ≠ ctr_N`, `E = C λ̄ |b₀|`. -/
def PairHyp2 (A ℓ₀ : ℝ) (V₀c : ℝ → ℂ → Vcoup) (lbar C κ Cq Cb : ℝ) : Prop :=
  ∀ msq : ℝ, 0 ≤ msq → ∀ b₀ : ℂ, ‖b₀‖ ≤ lbar → ∀ (N : ℕ) (b : Lam d L N), b ≠ ctr d L N →
    (∀ k ≤ N,
      ‖etaOf .two (FO d L V₀c lbar msq b₀ N (ctr d L N) b k).1‖ ≤
        4 * (lbar + Cb * (C * lbar * ‖b₀‖) / (1 - th L κ)) ^ 2 * ℓ₀ ^ 2 ∧
      ‖raOf .two (FO d L V₀c lbar msq b₀ N (ctr d L N) b k).1‖ ≤
        Cb * ℓ₀ ^ 2 * (C * lbar * ‖b₀‖) / (1 - th L κ) ∧
      ‖rbOf .two (FO d L V₀c lbar msq b₀ N (ctr d L N) b k).1‖ ≤
        Cb * ℓ₀ ^ 2 * (C * lbar * ‖b₀‖) / (1 - th L κ)) ∧
    ∀ k < N,
      ‖qS2 (NA d L V₀c lbar msq b₀ N (ctr d L N) b k) -
        (etaOf .two (FO d L V₀c lbar msq b₀ N (ctr d L N) b k).1 *
            (Flow.covAt d L N msq k (ctr d L N) b : ℂ) -
          laOf .two (FO d L V₀c lbar msq b₀ N (ctr d L N) b (k + 1)).1 *
            lbOf .two (FO d L V₀c lbar msq b₀ N (ctr d L N) b (k + 1)).1 *
            (Flow.covAt d L N msq k (ctr d L N) b : ℂ) ^ 2 -
          (raOf .two (FO d L V₀c lbar msq b₀ N (ctr d L N) b (k + 1)).1 *
              (Flow.covAt d L N msq k (ctr d L N) (ctr d L N) : ℂ) +
            rbOf .two (FO d L V₀c lbar msq b₀ N (ctr d L N) b (k + 1)).1 *
              (Flow.covAt d L N msq k b b : ℂ)))‖ ≤
        2 * Cq * ellj d L ℓ₀ k ^ 2 * ℓ₀ ^ 2 * (C * lbar * ‖b₀‖ * th L κ ^ k)

theorem ellj_sq_le (hd2 : 2 ≤ d) (ℓ₀ : ℝ) (n : ℕ) : ellj d (L : ℝ) ℓ₀ n ^ 2 ≤ ℓ₀ ^ 2 := by
  rw [ellj_sq]
  have := pow_le_one₀ (n := n) (rho_nonneg d L) (rho_le_one hd2 L)
  have h3 : 0 ≤ ℓ₀ ^ 2 := sq_nonneg _
  calc ℓ₀ ^ 2 * rho d L ^ n ≤ ℓ₀ ^ 2 * 1 := mul_le_mul_of_nonneg_left this h3
    _ = ℓ₀ ^ 2 := mul_one _

theorem ite_le (P : Prop) [Decidable P] {x : ℝ} (hx : 0 ≤ x) :
    x * (if P then (1 : ℝ) else 0) ≤ x := by
  split_ifs <;> simp [hx]

/-- The bounds `PairHyp2` hold with constants depending only on `d`. -/
theorem exists_pairHyp2 (d : ℕ) (hd : 3 ≤ d) : ∃ Cq Cb : ℝ, 0 ≤ Cq ∧ 0 ≤ Cb ∧
    ∀ (L : ℕ) [NeZero L] (A ℓ₀ : ℝ) (V₀c : ℝ → ℂ → Vcoup) (lbar C κ : ℝ),
    ObsLimHyp d L A ℓ₀ V₀c lbar C κ → PairHyp2 d L A ℓ₀ V₀c lbar C κ Cq Cb := by
  obtain ⟨Cq, hCq, hrec⟩ := Vobs_recursion_two d
  obtain ⟨Cb, hCb, hbd⟩ := Vobs_bd hd
  refine ⟨Cq, Cb, hCq, hCb, ?_⟩
  intro L _ A ℓ₀ V₀c lbar C κ H msq hmsq b₀ hb₀ N b hb
  have hd1 : 1 ≤ d := by omega
  have hd2 : 2 ≤ d := by omega
  have hL2 : 2 ≤ L := by have := three_le_L H; omega
  have hθ0 := th_nonneg L κ
  have hθ1 := th_lt_one hL2 H.fd.κ_pos (L := L)
  have hlb := H.fd.lbar_pos
  have hC0 := H.fd.C_nonneg
  have hE : 0 ≤ C * lbar * ‖b₀‖ := by positivity
  have hK : ∀ k ≤ N, KnormObs .two ℓ₀ (ctr d L N) b k A
      (FO d L V₀c lbar msq b₀ N (ctr d L N) b k).2 ≤
      ENNReal.ofReal (C * lbar * ‖b₀‖ * th L κ ^ k) := by
    intro k hk
    have := (H.fd.obs .two N msq (lbar : ℂ) b₀ b hmsq (by rw [norm_lbar H]; exact hb₀)
      (le_of_eq (norm_lbar H)) hb k hk).2
    rwa [norm_lbar H, rpow_neg_mul_nat (Nat.cast_nonneg _) κ k] at this
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · obtain ⟨-, -, hra, hrb, -, heta, -, -⟩ := hbd L H.fd.hL8 N msq (V₀c msq b₀) ℓ₀ H.fd.hℓ₀
      (H.fd.good N msq hmsq) .two (lbar : ℂ) (ctr d L N) b A H.fd.hA1 (th L κ)
      (C * lbar * ‖b₀‖) hθ0 hθ1 hE k hk (fun k' hk' => hK k' (by omega))
    rw [norm_lbar H] at heta
    have h1θ : 0 < 1 - th L κ := by linarith
    have hs := ellj_sq_le (L := L) hd2 ℓ₀ (min k (coal L (ctr d L N) b))
    have hs' := ellj_sq_le (L := L) hd2 ℓ₀ (coal L (ctr d L N) b)
    have hθc : th L κ ^ coal L (ctr d L N) b ≤ 1 := pow_le_one₀ hθ0 hθ1.le
    have hA2 : 0 ≤ 4 * (lbar + Cb * (C * lbar * ‖b₀‖) / (1 - th L κ)) ^ 2 := by positivity
    refine ⟨heta.trans (mul_le_mul_of_nonneg_left hs hA2), hra.trans ?_, hrb.trans ?_⟩ <;>
    · simp only [sab]
      rw [div_le_div_iff_of_pos_right h1θ]
      have : 0 ≤ Cb * (C * lbar * ‖b₀‖) := by positivity
      calc Cb * ellj d (L : ℝ) ℓ₀ (coal L (ctr d L N) b) ^ 2 * (C * lbar * ‖b₀‖) *
            th L κ ^ coal L (ctr d L N) b
          ≤ Cb * ℓ₀ ^ 2 * (C * lbar * ‖b₀‖) * 1 := by gcongr
        _ = _ := mul_one _
  · have he : 0 ≤ C * lbar * ‖b₀‖ * th L κ ^ k := by positivity
    obtain ⟨-, -, -, -, r5, -, -, -⟩ := hrec L N k ℓ₀ H.fd.hℓ₀ (Flow.covAt d L N msq k)
      (FO d L V₀c lbar msq b₀ N (ctr d L N) b k).1 (FO d L V₀c lbar msq b₀ N (ctr d L N) b k).2
      (ctr d L N) b A H.fd.hA1 _ he (hK k hk.le)
      (fun hj Y hY => abSmall_flowO (V₀c msq b₀) (lbar : ℂ) (ctr d L N) b hd1 H.fd.hL8
        (H.fd.good N msq hmsq) hk hj hY)
    have e1 : (FO d L V₀c lbar msq b₀ N (ctr d L N) b (k + 1)).1 =
        Coup.toV .two (nextObs (Flow.covAt d L N msq k) k
          (FO d L V₀c lbar msq b₀ N (ctr d L N) b k).1
          (FO d L V₀c lbar msq b₀ N (ctr d L N) b k).2 (ctr d L N) b) := rfl
    rw [e1, laOf_toV, lbOf_toV, raOf_toV, rbOf_toV]
    refine r5.trans ?_
    rw [ellab_two_inv]
    have hs := ellj_sq_le (L := L) hd2 ℓ₀ (jwedge k (coal L (ctr d L N) b))
    have h0 : 0 ≤ 2 * Cq * (ellj d L ℓ₀ k ^ 2 * ellj d L ℓ₀ (jwedge k (coal L (ctr d L N) b)) ^ 2) *
        (C * lbar * ‖b₀‖ * th L κ ^ k) := by positivity
    refine (ite_le _ h0).trans ?_
    have h2 : 0 ≤ 2 * Cq * ellj d L ℓ₀ k ^ 2 := by positivity
    calc 2 * Cq * (ellj d L ℓ₀ k ^ 2 * ellj d L ℓ₀ (jwedge k (coal L (ctr d L N) b)) ^ 2) *
          (C * lbar * ‖b₀‖ * th L κ ^ k)
        = 2 * Cq * ellj d L ℓ₀ k ^ 2 * ellj d L ℓ₀ (jwedge k (coal L (ctr d L N) b)) ^ 2 *
          (C * lbar * ‖b₀‖ * th L κ ^ k) := by ring
      _ ≤ 2 * Cq * ellj d L ℓ₀ k ^ 2 * ℓ₀ ^ 2 * (C * lbar * ‖b₀‖ * th L κ ^ k) := by gcongr

/-! ### The pair sequence -/

variable (d L) in
/-- The Case (2) `q` increment of step `j` at `(ctr, ctr + x)`, on `Λ_{NP x j}`. -/
def qP2 (V₀c : ℝ → ℂ → Vcoup) (lbar msq : ℝ) (b₀ : ℂ) (x : Zd d) (j : ℕ) : ℂ :=
  qS2 (NA d L V₀c lbar msq b₀ (NP x j) (ctr d L (NP x j)) (ctr d L (NP x j) + prj x) j)

variable (d L) in
/-- `q^{(2)}_∞/λ̄²` at `x`: the infinite-volume truncated four-point function. -/
def Qtwo (V₀c : ℝ → ℂ → Vcoup) (lbar msq : ℝ) (b₀ : ℂ) (x : Zd d) : ℂ :=
  (∑' j, qP2 d L V₀c lbar msq b₀ x j) / (lbar : ℂ) ^ 2

variable (H : ObsLimHyp d L A ℓ₀ V₀c lbar C κ) (hd : 1 ≤ d)
include H hd

theorem qP2_char {msq : ℝ} (hmsq : 0 ≤ msq) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar) (x : Zd d) {N j : ℕ}
    (hj : j + 2 ≤ N) (hs : supNormZ x ≤ L ^ (N - 1)) :
    qS2 (NA d L V₀c lbar msq b₀ N (ctr d L N) (ctr d L N + prj x) j) =
      qP2 d L V₀c lbar msq b₀ x j := by
  have h16 := sixteen_le H hd
  have hNP : N ≤ max N (NP x j) := le_max_left _ _
  have hBP : NP x j ≤ max N (NP x j) := le_max_right _ _
  have hjB : j + 2 ≤ NP x j := by unfold NP; omega
  have e1 := (pair_consist hd H.fd.hL8 hNP hmsq (V₀c msq b₀) (H.fd.good _ msq hmsq)
    (H.hbulk hmsq hb₀ hNP) H.odd (initObs .two (lbar : ℂ)) x (hx_of h16 (by omega) hs) hj).2
  have e2 := (pair_consist hd H.fd.hL8 hBP hmsq (V₀c msq b₀) (H.fd.good _ msq hmsq)
    (H.hbulk hmsq hb₀ hBP) H.odd (initObs .two (lbar : ℂ)) x
    (hx_of h16 (by omega) (supNormZ_le_NP (by omega) x j)) hjB).2
  unfold qP2
  show qaOf .two (nextObs _ _ _ _ _ _) + qbOf .two (nextObs _ _ _ _ _ _) =
    qaOf .two (nextObs _ _ _ _ _ _) + qbOf .two (nextObs _ _ _ _ _ _)
  rw [e1, e2]

variable {Cs Cq Cb : ℝ} (hCs : 0 ≤ Cs) (hS : StepBd d L A ℓ₀ V₀c lbar C κ Cs) (hCq : 0 ≤ Cq)
  (hCb : 0 ≤ Cb) (hP : PairHyp2 d L A ℓ₀ V₀c lbar C κ Cq Cb)
include hCs hS hCq hCb hP

/-- The constant of the `q` increments. -/
abbrev Kq2 (lbar C κ Cs Cq Cb ℓ₀ : ℝ) (b₀ : ℂ) (L : ℕ) : ℝ :=
  (4 * (lbar + Cb * (C * lbar * ‖b₀‖) / (1 - th L κ)) ^ 2 * ℓ₀ ^ 2 +
    Lm lbar C κ Cs b₀ L ^ 2 * ℓ₀ ^ 2 + 2 * (Cb * ℓ₀ ^ 2 * (C * lbar * ‖b₀‖) / (1 - th L κ)) +
    2 * Cq * ℓ₀ ^ 2 * (C * lbar * ‖b₀‖)) * ℓ₀ ^ 2

theorem q2_bd (hd2 : 2 ≤ d) {msq : ℝ} (hmsq : 0 ≤ msq) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar) {N : ℕ}
    {b : Lam d L N} (hb : b ≠ ctr d L N) {k : ℕ} (hk : k < N) :
    ‖qS2 (NA d L V₀c lbar msq b₀ N (ctr d L N) b k)‖ ≤
      Kq2 lbar C κ Cs Cq Cb ℓ₀ b₀ L * rho d L ^ k := by
  obtain ⟨hB, hQ⟩ := hP msq hmsq b₀ hb₀ N b hb
  have hq := hQ k hk
  obtain ⟨heta, -, -⟩ := hB k hk.le
  obtain ⟨-, hra, hrb⟩ := hB (k + 1) (by omega)
  have hla := la_N_bd H hd hCs hS hmsq hb₀ hb (k := k + 1) (by omega)
  have hlb := lb_N_bd H hd hCs hS hmsq hb₀ hb (k := k + 1) (by omega)
  have hθ1 := th_lt_one (by have := three_le_L H; omega) H.fd.κ_pos (L := L)
  have hθk : th L κ ^ k ≤ 1 := pow_le_one₀ (th_nonneg L κ) hθ1.le
  have hLm := Lm_nonneg H hd hCs hS b₀
  have hE := E_nonneg H hd hCs hS b₀
  have hG := H.fd.good N msq hmsq k hk
  have h1θ : 0 < 1 - th L κ := by linarith
  have hlb0 := H.fd.lbar_pos
  set ℓk := ellj d L ℓ₀ k ^ 2 with hℓk
  have hℓk0 : 0 ≤ ℓk := sq_nonneg _
  have hs : ellj d L ℓ₀ (k + 1) ^ 2 ≤ ℓk := by
    rw [hℓk, ellj_sq, ellj_sq, pow_succ]
    have h1 := rho_le_one hd2 L
    have h2 : 0 ≤ rho d L ^ k := pow_nonneg (rho_nonneg d L) k
    have h3 : 0 ≤ ℓ₀ ^ 2 := sq_nonneg _
    calc ℓ₀ ^ 2 * (rho d L ^ k * rho d L) ≤ ℓ₀ ^ 2 * (rho d L ^ k * 1) := by gcongr
      _ = ℓ₀ ^ 2 * rho d L ^ k := by ring
  have hℓkℓ₀ : ℓk ≤ ℓ₀ ^ 2 := ellj_sq_le hd2 ℓ₀ k
  have nc : ∀ x y : Lam d L N, ‖(Flow.covAt d L N msq k x y : ℂ)‖ ≤ ℓk := fun x y => by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (abs_cov_le H.fd.hℓ₀ hG x y).trans hs
  set Eta := 4 * (lbar + Cb * (C * lbar * ‖b₀‖) / (1 - th L κ)) ^ 2 * ℓ₀ ^ 2 with hEta
  set R2 := Cb * ℓ₀ ^ 2 * (C * lbar * ‖b₀‖) / (1 - th L κ) with hR2
  have hR20 : 0 ≤ R2 := by rw [hR2]; positivity
  set η := etaOf .two (FO d L V₀c lbar msq b₀ N (ctr d L N) b k).1
  set la := laOf .two (FO d L V₀c lbar msq b₀ N (ctr d L N) b (k + 1)).1
  set lb := lbOf .two (FO d L V₀c lbar msq b₀ N (ctr d L N) b (k + 1)).1
  set ra := raOf .two (FO d L V₀c lbar msq b₀ N (ctr d L N) b (k + 1)).1
  set rb := rbOf .two (FO d L V₀c lbar msq b₀ N (ctr d L N) b (k + 1)).1
  set cab := (Flow.covAt d L N msq k (ctr d L N) b : ℂ)
  set caa := (Flow.covAt d L N msq k (ctr d L N) (ctr d L N) : ℂ)
  set cbb := (Flow.covAt d L N msq k b b : ℂ)
  have t1 : ‖η * cab‖ ≤ Eta * ℓk := by
    rw [norm_mul]; exact mul_le_mul heta (nc _ _) (norm_nonneg _) (by rw [hEta]; positivity)
  have t2 : ‖la * lb * cab ^ 2‖ ≤ Lm lbar C κ Cs b₀ L ^ 2 * ℓ₀ ^ 2 * ℓk := by
    rw [norm_mul, norm_mul, norm_pow, sq, sq]
    have hc := nc (ctr d L N) b
    have hcc : ‖cab‖ * ‖cab‖ ≤ ℓ₀ ^ 2 * ℓk :=
      mul_le_mul (hc.trans hℓkℓ₀) hc (norm_nonneg _) (sq_nonneg _)
    calc ‖la‖ * ‖lb‖ * (‖cab‖ * ‖cab‖) ≤
        (Lm lbar C κ Cs b₀ L * Lm lbar C κ Cs b₀ L) * (ℓ₀ ^ 2 * ℓk) :=
          mul_le_mul (mul_le_mul hla hlb (norm_nonneg _) hLm) hcc (by positivity) (by positivity)
      _ = _ := by ring
  have t3 : ‖ra * caa + rb * cbb‖ ≤ 2 * R2 * ℓk := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have := mul_le_mul hra (nc (ctr d L N) (ctr d L N)) (norm_nonneg _) hR20
    have := mul_le_mul hrb (nc b b) (norm_nonneg _) hR20
    linarith
  have t4 : 2 * Cq * ℓk * ℓ₀ ^ 2 * (C * lbar * ‖b₀‖ * th L κ ^ k) ≤
      2 * Cq * ℓ₀ ^ 2 * (C * lbar * ‖b₀‖) * ℓk := by
    have : C * lbar * ‖b₀‖ * th L κ ^ k ≤ C * lbar * ‖b₀‖ := by
      calc C * lbar * ‖b₀‖ * th L κ ^ k ≤ C * lbar * ‖b₀‖ * 1 :=
            mul_le_mul_of_nonneg_left hθk hE
        _ = _ := mul_one _
    have h0 : 0 ≤ 2 * Cq * ℓk * ℓ₀ ^ 2 := by positivity
    calc 2 * Cq * ℓk * ℓ₀ ^ 2 * (C * lbar * ‖b₀‖ * th L κ ^ k) ≤
        2 * Cq * ℓk * ℓ₀ ^ 2 * (C * lbar * ‖b₀‖) := mul_le_mul_of_nonneg_left this h0
      _ = _ := by ring
  have hx : ‖qS2 (NA d L V₀c lbar msq b₀ N (ctr d L N) b k)‖ ≤
      ‖qS2 (NA d L V₀c lbar msq b₀ N (ctr d L N) b k) -
          (η * cab - la * lb * cab ^ 2 - (ra * caa + rb * cbb))‖ +
        (‖η * cab‖ + ‖la * lb * cab ^ 2‖ + ‖ra * caa + rb * cbb‖) := by
    refine (norm_le_norm_sub_add _ _).trans (add_le_add le_rfl ?_)
    exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
  calc ‖qS2 (NA d L V₀c lbar msq b₀ N (ctr d L N) b k)‖
      ≤ 2 * Cq * ℓ₀ ^ 2 * (C * lbar * ‖b₀‖) * ℓk +
          (Eta * ℓk + Lm lbar C κ Cs b₀ L ^ 2 * ℓ₀ ^ 2 * ℓk + 2 * R2 * ℓk) := by
        have := hq.trans t4; linarith
    _ = Kq2 lbar C κ Cs Cq Cb ℓ₀ b₀ L * rho d L ^ k := by
        rw [hℓk, ellj_sq, hEta, hR2]; unfold Kq2; ring

theorem qP2_bd (hd2 : 2 ≤ d) {msq : ℝ} (hmsq : 0 ≤ msq) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar)
    {x : Zd d} (hx0 : x ≠ 0) (j : ℕ) :
    ‖qP2 d L V₀c lbar msq b₀ x j‖ ≤ Kq2 lbar C κ Cs Cq Cb ℓ₀ b₀ L * rho d L ^ j := by
  have hL3 := three_le_L H
  have hb := ctr_add_prj_ne hL3 (N := NP x j) (by unfold NP; omega) hx0
    (supNormZ_le_NP (by omega) x j)
  exact q2_bd H hd hCs hS hCq hCb hP hd2 hmsq hb₀ hb (by unfold NP; omega)

theorem qP2_summable (hd3 : 3 ≤ d) {msq : ℝ} (hmsq : 0 ≤ msq) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar)
    {x : Zd d} (hx0 : x ≠ 0) : Summable (qP2 d L V₀c lbar msq b₀ x) := by
  have hρ1 := rho_lt_one hd3 (by have := three_le_L H; omega) (L := L)
  exact Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (rho_nonneg d L) hρ1).mul_left
      (Kq2 lbar C κ Cs Cq Cb ℓ₀ b₀ L))
    fun j => qP2_bd H hd hCs hS hCq hCb hP (by omega) hmsq hb₀ hx0 j

/-- **Rate for `q^{(2)}_N`**: `|q_N/λ̄² - Qtwo x| ≤ K L^{-(d-2)N}` (`N ≥ 2`, `|x|_∞ ≤ L^{N-1}`). -/
theorem qN2_rate (hd3 : 3 ≤ d) {msq : ℝ} (hmsq : 0 ≤ msq) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar)
    {x : Zd d} (hx0 : x ≠ 0) {N : ℕ} (hN : 2 ≤ N) (hs : supNormZ x ≤ L ^ (N - 1)) :
    ‖qN d L .two N msq (V₀c msq b₀) (initObs .two (lbar : ℂ)) (ctr d L N) (ctr d L N + prj x) /
        (lbar : ℂ) ^ 2 - Qtwo d L V₀c lbar msq b₀ x‖ ≤
      Kq2 lbar C κ Cs Cq Cb ℓ₀ b₀ L * (1 + 1 / (1 - rho d L)) / (rho d L * lbar ^ 2) *
        (L : ℝ) ^ (-(((d : ℝ) - 2) * N)) := by
  have hd2 : 2 ≤ d := by omega
  have hL3 := three_le_L H
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hb := ctr_add_prj_ne hL3 (N := n + 1) (by omega) hx0 hs
  have hlb := H.fd.lbar_pos
  have hρ0 := rho_nonneg d L
  have hρ1 := rho_lt_one hd3 (by omega) (L := L)
  have hρp : 0 < rho d L :=
    Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) _
  have hfin : qN d L .two (n + 1) msq (V₀c msq b₀) (initObs .two (lbar : ℂ)) (ctr d L (n + 1))
      (ctr d L (n + 1) + prj x) = ∑ j ∈ range n, qP2 d L V₀c lbar msq b₀ x j +
        qS2 (NA d L V₀c lbar msq b₀ (n + 1) (ctr d L (n + 1)) (ctr d L (n + 1) + prj x) n) := by
    rw [qN, sum_range_succ]
    congr 1
    exact sum_congr rfl fun j hj =>
      qP2_char H hd hmsq hb₀ x (N := n + 1) (j := j) (by simp at hj; omega) hs
  have hcore := series_core (qP2 d L V₀c lbar msq b₀ x) _
    (qP2_summable H hd hCs hS hCq hCb hP hd3 hmsq hb₀ hx0) hρ0 hρ1
    (qP2_bd H hd hCs hS hCq hCb hP hd2 hmsq hb₀ hx0)
    (q2_bd H hd hCs hS hCq hCb hP hd2 hmsq hb₀ hb (k := n) (by omega))
  have e1 : qN d L .two (n + 1) msq (V₀c msq b₀) (initObs .two (lbar : ℂ)) (ctr d L (n + 1))
      (ctr d L (n + 1) + prj x) / (lbar : ℂ) ^ 2 - Qtwo d L V₀c lbar msq b₀ x =
      ((∑ j ∈ range n, qP2 d L V₀c lbar msq b₀ x j +
        qS2 (NA d L V₀c lbar msq b₀ (n + 1) (ctr d L (n + 1)) (ctr d L (n + 1) + prj x) n)) -
        ∑' j, qP2 d L V₀c lbar msq b₀ x j) / (lbar : ℂ) ^ 2 := by
    rw [hfin, Qtwo, sub_div]
  have hl2' : ‖((lbar : ℂ) ^ 2)‖ = lbar ^ 2 := by rw [norm_pow, norm_lbar H]
  have hlb2 : 0 < lbar ^ 2 := by positivity
  rw [e1, norm_div, hl2', rpow_neg_mul_nat (Nat.cast_nonneg _) ((d : ℝ) - 2) (n + 1),
    div_le_iff₀ hlb2]
  refine hcore.trans (le_of_eq ?_)
  have hρne : rho d L ≠ 0 := hρp.ne'
  have h1ρne : 1 - rho d L ≠ 0 := by linarith
  field_simp
  ring

theorem Kq2_mono {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar) :
    Kq2 lbar C κ Cs Cq Cb ℓ₀ b₀ L ≤ Kq2 lbar C κ Cs Cq Cb ℓ₀ (lbar : ℂ) L := by
  have hb : ‖b₀‖ ≤ ‖(lbar : ℂ)‖ := by rw [norm_lbar H]; exact hb₀
  have hθ1 := th_lt_one (by have := three_le_L H; omega) H.fd.κ_pos (L := L)
  have h1 : 0 < 1 - th L κ := by linarith
  have hlb := H.fd.lbar_pos
  have hC0 := H.fd.C_nonneg
  have hE : C * lbar * ‖b₀‖ ≤ C * lbar * ‖(lbar : ℂ)‖ :=
    mul_le_mul_of_nonneg_left hb (by positivity)
  have hE0 : 0 ≤ C * lbar * ‖b₀‖ := by positivity
  have hL : Lm lbar C κ Cs b₀ L ≤ Lm lbar C κ Cs (lbar : ℂ) L := by
    unfold Lm; linarith [div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hE hCs) h1.le]
  have hL0 : 0 ≤ Lm lbar C κ Cs b₀ L := by unfold Lm; positivity
  have hq : 0 ≤ ℓ₀ ^ 2 := sq_nonneg _
  have h2 : Cb * (C * lbar * ‖b₀‖) / (1 - th L κ) ≤ Cb * (C * lbar * ‖(lbar : ℂ)‖) / (1 - th L κ) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hE hCb) h1.le
  have h20 : 0 ≤ Cb * (C * lbar * ‖b₀‖) / (1 - th L κ) := by positivity
  have h3 : Cb * ℓ₀ ^ 2 * (C * lbar * ‖b₀‖) / (1 - th L κ) ≤
      Cb * ℓ₀ ^ 2 * (C * lbar * ‖(lbar : ℂ)‖) / (1 - th L κ) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hE (by positivity)) h1.le
  have h4 : (lbar + Cb * (C * lbar * ‖b₀‖) / (1 - th L κ)) ^ 2 ≤
      (lbar + Cb * (C * lbar * ‖(lbar : ℂ)‖) / (1 - th L κ)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have h5 : Lm lbar C κ Cs b₀ L ^ 2 ≤ Lm lbar C κ Cs (lbar : ℂ) L ^ 2 := pow_le_pow_left₀ hL0 hL 2
  have h6 : 2 * Cq * ℓ₀ ^ 2 * (C * lbar * ‖b₀‖) ≤ 2 * Cq * ℓ₀ ^ 2 * (C * lbar * ‖(lbar : ℂ)‖) :=
    mul_le_mul_of_nonneg_left hE (by positivity)
  unfold Kq2
  refine mul_le_mul_of_nonneg_right ?_ hq
  have := mul_le_mul_of_nonneg_right h4 (show (0 : ℝ) ≤ 4 * 1 by norm_num)
  have := mul_le_mul_of_nonneg_right h5 hq
  have := mul_le_mul_of_nonneg_right h4 (mul_nonneg (show (0 : ℝ) ≤ 4 by norm_num) hq)
  nlinarith

/-- **Joint continuity of `Q2(x)`** on `[0, ∞) × B(0, λ̄)` (`x ≠ 0`). -/
theorem Qtwo_joint (hd3 : 3 ≤ d) {x : Zd d} (hx0 : x ≠ 0) :
    ContinuousOn (fun p : ℝ × ℂ => Qtwo d L V₀c lbar p.1 p.2 x) (Set.Ici 0 ×ˢ ball 0 lbar) := by
  have hL3 := three_le_L H
  have hL2 : 2 ≤ L := by omega
  have hρ1 := rho_lt_one hd3 hL2 (L := L)
  have hρp : 0 < rho d L :=
    Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) _
  have hlb := H.fd.lbar_pos
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = Kq2 lbar C κ Cs Cq Cb ℓ₀ (lbar : ℂ) L * (1 + 1 / (1 - rho d L)) /
      (rho d L * lbar ^ 2) := ⟨_, rfl⟩
  have hU : TendstoUniformlyOn (fun (N : ℕ) (p : ℝ × ℂ) =>
      qN d L .two N p.1 (V₀c p.1 p.2) (initObs .two (lbar : ℂ)) (ctr d L N) (ctr d L N + prj x) /
        (lbar : ℂ) ^ 2) (fun p => Qtwo d L V₀c lbar p.1 p.2 x) atTop
      (Set.Ici 0 ×ˢ ball 0 lbar) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have ht := (tendsto_rpow_neg_mul (L := L) hL2 (s := (d : ℝ) - 2)
      (by have : (3 : ℝ) ≤ d := (by exact_mod_cast hd3); linarith)).const_mul B
    rw [mul_zero] at ht
    filter_upwards [(tendsto_order.1 ht).2 ε hε, eventually_ge_atTop (2 + supNormZ x)]
      with N hN hN2 p hp
    have hb₀ : ‖p.2‖ ≤ lbar := (mem_ball_zero_iff.1 hp.2).le
    have hs : supNormZ x ≤ L ^ (N - 1) := by
      have h1 : supNormZ x < L ^ supNormZ x := Nat.lt_pow_self (by omega)
      have h2 : L ^ supNormZ x ≤ L ^ (N - 1) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have hr := qN2_rate H hd hCs hS hCq hCb hP hd3 (Set.mem_Ici.1 hp.1) hb₀ hx0 (by omega) hs
    rw [dist_eq_norm, norm_sub_rev]
    refine lt_of_le_of_lt (hr.trans ?_) hN
    have hK := Kq2_mono H hd hCs hS hCq hCb hP hb₀
    have hc : 0 ≤ (1 + 1 / (1 - rho d L)) / (rho d L * lbar ^ 2) *
        (L : ℝ) ^ (-(((d : ℝ) - 2) * N)) := by
      have : 0 < 1 - rho d L := by linarith
      have := Real.rpow_nonneg (Nat.cast_nonneg L) (-(((d : ℝ) - 2) * N))
      positivity
    rw [hB]
    calc Kq2 lbar C κ Cs Cq Cb ℓ₀ p.2 L * (1 + 1 / (1 - rho d L)) / (rho d L * lbar ^ 2) *
          (L : ℝ) ^ (-(((d : ℝ) - 2) * N))
        = Kq2 lbar C κ Cs Cq Cb ℓ₀ p.2 L * ((1 + 1 / (1 - rho d L)) / (rho d L * lbar ^ 2) *
          (L : ℝ) ^ (-(((d : ℝ) - 2) * N))) := by ring
      _ ≤ Kq2 lbar C κ Cs Cq Cb ℓ₀ (lbar : ℂ) L * ((1 + 1 / (1 - rho d L)) /
          (rho d L * lbar ^ 2) * (L : ℝ) ^ (-(((d : ℝ) - 2) * N))) :=
            mul_le_mul_of_nonneg_right hK hc
      _ = _ := by ring
  refine hU.continuousOn (Frequently.of_forall fun N => ?_)
  exact (H.fd.qN_joint hd (initObs .two (lbar : ℂ)) (ctr d L N) (ctr d L N + prj x)).div_const _

end

end Ward
