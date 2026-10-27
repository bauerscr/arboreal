import Ward.ObsLimitB

/-!
# Infinite-volume observable couplings

Along the canonical family `(Λ_N, ctr_N)` (Case (2), `l₀ = λ̄`), with `S = [0, ∞) × B(0, λ̄)`:

* `LamA m b₀ = lim_j λ_{a,j}/λ̄`, `GamA m b₀ = ∑_j γ-step_{a,j}/λ̄` at the centre;
* `LamB m b₀ z = lim_j λ_{b,j}(z)/λ̄`, `GamB m b₀ z = ∑_j γ-step_{b,j}(z)/λ̄` at `z ∈ ℕ^d`.

**Rates** (uniform in `m ≥ 0`, `|b₀| ≤ λ̄` and the point; `N ≥ 2`, `x ≠ 0`):
* `‖lamA2 N x - LamA‖ ≤ K |b₀| L^{-κN}` (`lamA2_rate`),
  `‖lamB2 N x - LamB (redZ N (ctr_N + x))‖ ≤ K |b₀| L^{-κN}` (`lamB2_rate`);
* `‖gamA2 N x - GamA‖ ≤ K' L^{-(d-2)N}` (`gamA2_rate`),
  `‖gamB2 N x - GamB (redZ N (ctr_N + x))‖ ≤ K' L^{-(d-2)N}` (`gamB2_rate`)
  (the `γ` rate has no factor `b₀`: the tail `λ ∑_{k ≥ N} C_{k+1}(0,0)` of `e:gammainfbd`).

**Continuity**: `LamA`, `GamA`, `LamB z`, `GamB z` are jointly continuous on `S`
(`LamA_joint`, …): uniform limits of the jointly continuous finite-scale couplings
(`PtCorr.FlowData.flowO_joint`).  Along a continuous family `b₀ = B(m²)` they are continuous in
`m² ≥ 0` (compose with `m ↦ (m, B m)`).
-/

namespace Ward

noncomputable section

open Finset Grassmann Loc Step Obs FRD PtCorr Metric Filter Topology

variable {d L : ℕ} [NeZero L] {A ℓ₀ lbar C κ : ℝ} {V₀c : ℝ → ℂ → Vcoup}

/-! ### The limits -/

variable (d L) in
/-- `λ^{(2)}_{a,∞}/λ̄` at the centre. -/
def LamA (V₀c : ℝ → ℂ → Vcoup) (lbar msq : ℝ) (b₀ : ℂ) : ℂ :=
  limUnder atTop (lA d L V₀c lbar msq b₀) / lbar

variable (d L) in
/-- `γ^{(2)}_{a,∞}/λ̄` at the centre. -/
def GamA (V₀c : ℝ → ℂ → Vcoup) (lbar msq : ℝ) (b₀ : ℂ) : ℂ :=
  (∑' j, gA d L V₀c lbar msq b₀ j) / lbar

variable (d L) in
/-- `λ^{(2)}_{b,∞}(z)/λ̄` at `z ∈ ℕ^d`. -/
def LamB (V₀c : ℝ → ℂ → Vcoup) (lbar msq : ℝ) (b₀ : ℂ) (z : Zd d) : ℂ :=
  limUnder atTop (lB d L V₀c lbar msq b₀ z) / lbar

variable (d L) in
/-- `γ^{(2)}_{b,∞}(z)/λ̄` at `z ∈ ℕ^d`. -/
def GamB (V₀c : ℝ → ℂ → Vcoup) (lbar msq : ℝ) (b₀ : ℂ) (z : Zd d) : ℂ :=
  (∑' j, gB d L V₀c lbar msq b₀ z j) / lbar

/-- The uniform constant `K₁ ≥ Λm + C_S E` (for `|b₀| ≤ λ̄`). -/
abbrev K1 (lbar C κ Cs : ℝ) (L : ℕ) : ℝ :=
  lbar + Cs * (C * lbar * lbar) / (1 - th L κ) + Cs * (C * lbar * lbar)

variable (H : ObsLimHyp d L A ℓ₀ V₀c lbar C κ) (hd : 1 ≤ d) {Cs : ℝ} (hCs : 0 ≤ Cs)
  (hS : StepBd d L A ℓ₀ V₀c lbar C κ Cs)
include H hd hCs hS

theorem th_facts : 0 ≤ th L κ ∧ th L κ < 1 ∧ 0 < th L κ :=
  ⟨th_nonneg L κ, th_lt_one (by have := three_le_L H; omega) H.fd.κ_pos,
    Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) _⟩

theorem E_le {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar) : C * lbar * ‖b₀‖ ≤ C * lbar * lbar := by
  have := H.fd.C_nonneg; have := H.fd.lbar_pos
  exact mul_le_mul_of_nonneg_left hb₀ (by positivity)

theorem Lm_le {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar) :
    Lm lbar C κ Cs b₀ L + Cs * (C * lbar * ‖b₀‖) ≤ K1 lbar C κ Cs L := by
  obtain ⟨-, hθ1, -⟩ := th_facts H hd hCs hS
  have hE := E_le H hd hCs hS hb₀
  have h1 : 0 < 1 - th L κ := by linarith
  have h2 : Cs * (C * lbar * ‖b₀‖) ≤ Cs * (C * lbar * lbar) := mul_le_mul_of_nonneg_left hE hCs
  have h3 : Cs * (C * lbar * ‖b₀‖) / (1 - th L κ) ≤ Cs * (C * lbar * lbar) / (1 - th L κ) :=
    div_le_div_of_nonneg_right h2 h1.le
  unfold Lm K1; linarith

/-! #### The `a` slot -/

theorem lA_geom {msq : ℝ} (hmsq : 0 ≤ msq) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar) (n : ℕ) :
    dist (lA d L V₀c lbar msq b₀ n) (lA d L V₀c lbar msq b₀ (n + 1)) ≤
      Cs * (C * lbar * ‖b₀‖) * th L κ ^ n := by
  rw [dist_eq_norm, norm_sub_rev]
  exact (lA_succ H hd hCs hS hmsq hb₀ n).trans (le_of_eq (by ring))

theorem lA_tendsto {msq : ℝ} (hmsq : 0 ≤ msq) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar) :
    Tendsto (lA d L V₀c lbar msq b₀) atTop (𝓝 (limUnder atTop (lA d L V₀c lbar msq b₀))) :=
  (cauchySeq_of_le_geometric _ _ (th_facts H hd hCs hS).2.1
    (lA_geom H hd hCs hS hmsq hb₀)).tendsto_limUnder

theorem lA_sub_lim {msq : ℝ} (hmsq : 0 ≤ msq) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar) (j : ℕ) :
    ‖lA d L V₀c lbar msq b₀ j - limUnder atTop (lA d L V₀c lbar msq b₀)‖ ≤
      Cs * (C * lbar * ‖b₀‖) * th L κ ^ j / (1 - th L κ) := by
  have := dist_le_of_le_geometric_of_tendsto _ _ (th_facts H hd hCs hS).2.1
    (lA_geom H hd hCs hS hmsq hb₀) (lA_tendsto H hd hCs hS hmsq hb₀) j
  rwa [dist_eq_norm] at this

/-- The last two steps on `Λ_N`, `N = n + 2`, and the tail: the core of the `λ` rates. -/
theorem la_last_tail (f : ℕ → ℂ) (l : ℂ) {e : ℝ} (he : 0 ≤ e) {n : ℕ}
    (hstep : ∀ k < n + 2, ‖f (k + 1) - f k‖ ≤ Cs * (e * th L κ ^ k))
    (hlim : ‖f n - l‖ ≤ Cs * e * th L κ ^ n / (1 - th L κ)) :
    ‖f (n + 2) - l‖ ≤ 2 * Cs * e / (th L κ ^ 2 * (1 - th L κ)) * th L κ ^ (n + 2) := by
  obtain ⟨hθ0, hθ1, hθp⟩ := th_facts H hd hCs hS
  have h1 := norm_sub_le_geom_tail f (mul_nonneg hCs he) hθ0 hθ1 (Nat.le_add_right n 2)
    (fun k _ hk => (hstep k hk).trans (le_of_eq (by ring)))
  have h2 : ‖f (n + 2) - l‖ ≤ ‖f n - f (n + 2)‖ + ‖f n - l‖ := by
    calc ‖f (n + 2) - l‖ = ‖-(f n - f (n + 2)) + (f n - l)‖ := by congr 1; abel
      _ ≤ ‖-(f n - f (n + 2))‖ + ‖f n - l‖ := norm_add_le _ _
      _ = _ := by rw [norm_neg]
  have h1θ : 0 < 1 - th L κ := by linarith
  have hθne : th L κ ≠ 0 := hθp.ne'
  have h1ne : 1 - th L κ ≠ 0 := h1θ.ne'
  have e3 : 2 * Cs * e / (th L κ ^ 2 * (1 - th L κ)) * th L κ ^ (n + 2) =
      2 * (Cs * e * th L κ ^ n / (1 - th L κ)) := by
    field_simp; ring
  rw [e3]; linarith

theorem ctr_add_ne {N : ℕ} {x : Lam d L N} (hx : x ≠ 0) : ctr d L N + x ≠ ctr d L N := by
  intro h; exact hx (by simpa using h)

/-- **Rate for `λ^{(2)}_a`**. -/
theorem lamA2_rate {msq : ℝ} (hmsq : 0 ≤ msq) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar) {N : ℕ}
    (hN : 2 ≤ N) {x : Lam d L N} (hx : x ≠ 0) :
    ‖lamA2 d L N msq (V₀c msq b₀) (lbar : ℂ) x - LamA d L V₀c lbar msq b₀‖ ≤
      2 * Cs * C / (th L κ ^ 2 * (1 - th L κ)) * ‖b₀‖ * (L : ℝ) ^ (-(κ * N)) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
  have hb := ctr_add_ne H hd hCs hS hx
  have hl := norm_lbar H
  have hlb := H.fd.lbar_pos
  have hfn : laOf .two (FO d L V₀c lbar msq b₀ (n + 2) (ctr d L (n + 2)) (ctr d L (n + 2) + x) n).1
      = lA d L V₀c lbar msq b₀ n := (lA_char H hd hmsq hb₀ (N := n + 2) le_rfl _).1
  have hmain := la_last_tail H hd hCs hS
    (fun k => laOf .two (FO d L V₀c lbar msq b₀ (n + 2) (ctr d L (n + 2))
      (ctr d L (n + 2) + x) k).1) (limUnder atTop (lA d L V₀c lbar msq b₀))
    (E_nonneg H hd hCs hS b₀) (fun k hk => (hS msq hmsq b₀ hb₀ _ _ hb k hk).1)
    (by rw [hfn]; exact lA_sub_lim H hd hCs hS hmsq hb₀ n)
  have e1 : lamA2 d L (n + 2) msq (V₀c msq b₀) (lbar : ℂ) x - LamA d L V₀c lbar msq b₀ =
      (laOf .two (FO d L V₀c lbar msq b₀ (n + 2) (ctr d L (n + 2)) (ctr d L (n + 2) + x)
        (n + 2)).1 - limUnder atTop (lA d L V₀c lbar msq b₀)) / lbar := by
    rw [lamA2, LamA, sub_div]
  rw [e1, norm_div, hl, rpow_neg_mul_nat (Nat.cast_nonneg _) κ (n + 2), div_le_iff₀ hlb]
  refine hmain.trans (le_of_eq ?_)
  ring

/-- `|λ^{(2)}_{a,∞} - 1| ≤ C_S C |b₀| / (1 - θ)` (any `m² ≥ 0`). -/
theorem LamA_sub_one {msq : ℝ} (hmsq : 0 ≤ msq) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar) :
    ‖LamA d L V₀c lbar msq b₀ - 1‖ ≤ Cs * C / (1 - th L κ) * ‖b₀‖ := by
  obtain ⟨hθ0, hθ1, -⟩ := th_facts H hd hCs hS
  have hlb := H.fd.lbar_pos
  have h1 := lA_sub_lim H hd hCs hS hmsq hb₀ 0
  have h0 : lA d L V₀c lbar msq b₀ 0 = lbar := rfl
  rw [h0, pow_zero, mul_one, norm_sub_rev] at h1
  have e : LamA d L V₀c lbar msq b₀ - 1 =
      (limUnder atTop (lA d L V₀c lbar msq b₀) - lbar) / lbar := by
    rw [LamA, sub_div, div_self (by exact_mod_cast hlb.ne')]
  rw [e, norm_div, norm_lbar H, div_le_iff₀ hlb]
  refine h1.trans (le_of_eq ?_)
  field_simp

/-! #### `γ` at the centre -/

theorem gA_summable (hd2 : 2 ≤ d) (hd3 : 3 ≤ d) {msq : ℝ} (hmsq : 0 ≤ msq) {b₀ : ℂ}
    (hb₀ : ‖b₀‖ ≤ lbar) : Summable (gA d L V₀c lbar msq b₀) := by
  have hρ1 := rho_lt_one hd3 (by have := three_le_L H; omega) (L := L)
  exact Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (rho_nonneg d L) hρ1).mul_left
      ((Lm lbar C κ Cs b₀ L + Cs * (C * lbar * ‖b₀‖)) * ℓ₀ ^ 2))
    fun j => (gA_bd H hd hCs hS hd2 hmsq hb₀ j).trans (le_of_eq (by ring))

/-- The tail of a series with geometric bound. -/
theorem norm_tsum_tail_le (g : ℕ → ℂ) {K ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hg : ∀ j, ‖g j‖ ≤ K * ρ ^ j) (n : ℕ) :
    ‖∑' i, g (i + n)‖ ≤ K * ρ ^ n / (1 - ρ) := by
  have hs : HasSum (fun i => K * ρ ^ n * ρ ^ i) (K * ρ ^ n * (1 - ρ)⁻¹) :=
    (hasSum_geometric_of_lt_one hρ0 hρ1).mul_left _
  refine (tsum_of_norm_bounded hs fun i => (hg (i + n)).trans (le_of_eq (by ring))).trans
    (le_of_eq (by ring))

/-- The core of the `γ` rates: a partial sum plus a last term against the full series. -/
theorem gam_core (g : ℕ → ℂ) (T : ℂ) (hs : Summable g) {K' ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hgb : ∀ j, ‖g j‖ ≤ K' * ρ ^ j) {n : ℕ} (hT : ‖T‖ ≤ K' * ρ ^ n) :
    ‖(∑ j ∈ range n, g j + T) - ∑' j, g j‖ ≤ K' * (1 + 1 / (1 - ρ)) * ρ ^ n := by
  rw [← hs.sum_add_tsum_nat_add n]
  have e : (∑ j ∈ range n, g j + T) - (∑ j ∈ range n, g j + ∑' i, g (i + n)) =
      T - ∑' i, g (i + n) := by abel
  rw [e]
  have htail := norm_tsum_tail_le H hd hCs hS g hρ0 hρ1 hgb n
  calc ‖T - ∑' i, g (i + n)‖ ≤ ‖T‖ + ‖∑' i, g (i + n)‖ := norm_sub_le _ _
    _ ≤ K' * ρ ^ n + K' * ρ ^ n / (1 - ρ) := add_le_add hT htail
    _ = K' * (1 + 1 / (1 - ρ)) * ρ ^ n := by ring

/-- **Rate for `γ^{(2)}_a`** (`N`-independent `γ`, the tail of `e:gammainfbd`). -/
theorem gamA2_rate (hd3 : 3 ≤ d) {msq : ℝ} (hmsq : 0 ≤ msq) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar)
    {N : ℕ} (hN : 2 ≤ N) {x : Lam d L N} (hx : x ≠ 0) :
    ‖gamA2 d L N msq (V₀c msq b₀) (lbar : ℂ) x - GamA d L V₀c lbar msq b₀‖ ≤
      K1 lbar C κ Cs L * ℓ₀ ^ 2 * (1 + 1 / (1 - rho d L)) / (rho d L * lbar) *
        (L : ℝ) ^ (-(((d : ℝ) - 2) * N)) := by
  have hd2 : 2 ≤ d := by omega
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hb := ctr_add_ne H hd hCs hS hx
  have hl := norm_lbar H
  have hlb := H.fd.lbar_pos
  have hρ0 := rho_nonneg d L
  have hρ1 := rho_lt_one hd3 (by have := three_le_L H; omega) (L := L)
  have hρp : 0 < rho d L :=
    Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) _
  have hfin : gaN d L .two (n + 1) msq (V₀c msq b₀) (initObs .two (lbar : ℂ)) (ctr d L (n + 1))
      (ctr d L (n + 1) + x) = ∑ j ∈ range n, gA d L V₀c lbar msq b₀ j +
        gaOf .two (NA d L V₀c lbar msq b₀ (n + 1) (ctr d L (n + 1)) (ctr d L (n + 1) + x) n) := by
    rw [gaN, sum_range_succ]
    congr 1
    exact sum_congr rfl fun j hj =>
      (lA_char H hd hmsq hb₀ (N := n + 1) (j := j) (by simp at hj; omega) _).2
  have hcore := gam_core H hd hCs hS (gA d L V₀c lbar msq b₀) _
    (gA_summable H hd hCs hS hd2 hd3 hmsq hb₀) hρ0 hρ1 (gA_bd H hd hCs hS hd2 hmsq hb₀)
    (ga_N_bd H hd hCs hS hd2 hmsq hb₀ hb (k := n) (by omega))
  have e1 : gamA2 d L (n + 1) msq (V₀c msq b₀) (lbar : ℂ) x - GamA d L V₀c lbar msq b₀ =
      ((∑ j ∈ range n, gA d L V₀c lbar msq b₀ j +
        gaOf .two (NA d L V₀c lbar msq b₀ (n + 1) (ctr d L (n + 1)) (ctr d L (n + 1) + x) n)) -
        ∑' j, gA d L V₀c lbar msq b₀ j) / lbar := by
    rw [gamA2, GamA, hfin, sub_div]
  have hK'le : (Lm lbar C κ Cs b₀ L + Cs * (C * lbar * ‖b₀‖)) * ℓ₀ ^ 2 ≤
      K1 lbar C κ Cs L * ℓ₀ ^ 2 :=
    mul_le_mul_of_nonneg_right (Lm_le H hd hCs hS hb₀) (sq_nonneg _)
  rw [e1, norm_div, hl, rpow_neg_mul_nat (Nat.cast_nonneg _) ((d : ℝ) - 2) (n + 1),
    div_le_iff₀ hlb]
  have h1ρ : 0 < 1 - rho d L := by linarith
  have hρn : 0 ≤ rho d L ^ n := pow_nonneg hρ0 n
  have hq : 0 ≤ 1 + 1 / (1 - rho d L) := by positivity
  have hρne : rho d L ≠ 0 := hρp.ne'
  have hlne : lbar ≠ 0 := hlb.ne'
  have h1ρne : 1 - rho d L ≠ 0 := h1ρ.ne'
  refine hcore.trans ?_
  calc (Lm lbar C κ Cs b₀ L + Cs * (C * lbar * ‖b₀‖)) * ℓ₀ ^ 2 * (1 + 1 / (1 - rho d L)) *
        rho d L ^ n
      ≤ K1 lbar C κ Cs L * ℓ₀ ^ 2 * (1 + 1 / (1 - rho d L)) * rho d L ^ n := by gcongr
    _ = K1 lbar C κ Cs L * ℓ₀ ^ 2 * (1 + 1 / (1 - rho d L)) / (rho d L * lbar) *
          rho d L ^ (n + 1) * lbar := by
        field_simp; ring

theorem gA_joint (j : ℕ) :
    ContinuousOn (fun p : ℝ × ℂ => gA d L V₀c lbar p.1 p.2 j) (Set.Ici 0 ×ˢ ball 0 lbar) :=
  (H.fd.nextAt_joint hd (initObs .two (lbar : ℂ)) (ctr d L (j + 2)) (ctr d L (j + 2))
    (j := j) (by omega)).ga

/-- **Joint continuity of `γ^{(2)}_{a,∞}`** on `[0, ∞) × B(0, λ̄)`. -/
theorem GamA_joint (hd3 : 3 ≤ d) :
    ContinuousOn (fun p : ℝ × ℂ => GamA d L V₀c lbar p.1 p.2) (Set.Ici 0 ×ˢ ball 0 lbar) := by
  have hd2 : 2 ≤ d := by omega
  have hρ1 := rho_lt_one hd3 (by have := three_le_L H; omega) (L := L)
  refine (continuousOn_tsum (fun j => gA_joint H hd hCs hS j)
    ((summable_geometric_of_lt_one (rho_nonneg d L) hρ1).mul_left (K1 lbar C κ Cs L * ℓ₀ ^ 2))
    fun n p hp => ?_).div_const _
  have hb₀ : ‖p.2‖ ≤ lbar := (mem_ball_zero_iff.1 hp.2).le
  refine (gA_bd H hd hCs hS hd2 (Set.mem_Ici.1 hp.1) hb₀ n).trans ?_
  have := Lm_le H hd hCs hS hb₀
  have : 0 ≤ ℓ₀ ^ 2 * rho d L ^ n := mul_nonneg (sq_nonneg _) (pow_nonneg (rho_nonneg d L) n)
  calc _ = (Lm lbar C κ Cs p.2 L + Cs * (C * lbar * ‖p.2‖)) * (ℓ₀ ^ 2 * rho d L ^ n) := by ring
    _ ≤ K1 lbar C κ Cs L * (ℓ₀ ^ 2 * rho d L ^ n) := by gcongr
    _ = _ := by ring

/-! #### The `b` slot -/

theorem lB_geom {msq : ℝ} (hmsq : 0 ≤ msq) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar) {z : Zd d}
    (hz0 : ∀ i, 0 ≤ z i) (n : ℕ) :
    dist (lB d L V₀c lbar msq b₀ z n) (lB d L V₀c lbar msq b₀ z (n + 1)) ≤
      Cs * (C * lbar * ‖b₀‖) * th L κ ^ n := by
  rw [dist_eq_norm, norm_sub_rev]
  exact (lB_succ H hd hCs hS hmsq hb₀ hz0 n).trans (le_of_eq (by ring))

theorem lB_tendsto {msq : ℝ} (hmsq : 0 ≤ msq) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar) {z : Zd d}
    (hz0 : ∀ i, 0 ≤ z i) :
    Tendsto (lB d L V₀c lbar msq b₀ z) atTop (𝓝 (limUnder atTop (lB d L V₀c lbar msq b₀ z))) :=
  (cauchySeq_of_le_geometric _ _ (th_facts H hd hCs hS).2.1
    (lB_geom H hd hCs hS hmsq hb₀ hz0)).tendsto_limUnder

theorem lB_sub_lim {msq : ℝ} (hmsq : 0 ≤ msq) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar) {z : Zd d}
    (hz0 : ∀ i, 0 ≤ z i) (j : ℕ) :
    ‖lB d L V₀c lbar msq b₀ z j - limUnder atTop (lB d L V₀c lbar msq b₀ z)‖ ≤
      Cs * (C * lbar * ‖b₀‖) * th L κ ^ j / (1 - th L κ) := by
  have := dist_le_of_le_geometric_of_tendsto _ _ (th_facts H hd hCs hS).2.1
    (lB_geom H hd hCs hS hmsq hb₀ hz0) (lB_tendsto H hd hCs hS hmsq hb₀ hz0) j
  rwa [dist_eq_norm] at this

/-- **Rate for `λ^{(2)}_b`**, at the reduced point of `ctr_N + x`. -/
theorem lamB2_rate {msq : ℝ} (hmsq : 0 ≤ msq) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar) {N : ℕ}
    (hN : 2 ≤ N) {x : Lam d L N} (hx : x ≠ 0) :
    ‖lamB2 d L N msq (V₀c msq b₀) (lbar : ℂ) x -
        LamB d L V₀c lbar msq b₀ (redZ N (ctr d L N + x))‖ ≤
      2 * Cs * C / (th L κ ^ 2 * (1 - th L κ)) * ‖b₀‖ * (L : ℝ) ^ (-(κ * N)) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
  have hb := ctr_add_ne H hd hCs hS hx
  have hl := norm_lbar H
  have hlb := H.fd.lbar_pos
  have hz0 : ∀ i, 0 ≤ redZ (n + 2) (ctr d L (n + 2) + x) i := redZ_nonneg _ _
  have hfn : lbOf .two (FO d L V₀c lbar msq b₀ (n + 2) (ctr d L (n + 2)) (ctr d L (n + 2) + x) n).1
      = lB d L V₀c lbar msq b₀ (redZ (n + 2) (ctr d L (n + 2) + x)) n :=
    (lB_eq H hd hmsq hb₀ (N := n + 2) le_rfl _ _).1
  have hmain := la_last_tail H hd hCs hS
    (fun k => lbOf .two (FO d L V₀c lbar msq b₀ (n + 2) (ctr d L (n + 2))
      (ctr d L (n + 2) + x) k).1)
    (limUnder atTop (lB d L V₀c lbar msq b₀ (redZ (n + 2) (ctr d L (n + 2) + x))))
    (E_nonneg H hd hCs hS b₀) (fun k hk => (hS msq hmsq b₀ hb₀ _ _ hb k hk).2.1)
    (by rw [hfn]; exact lB_sub_lim H hd hCs hS hmsq hb₀ hz0 n)
  have e1 : lamB2 d L (n + 2) msq (V₀c msq b₀) (lbar : ℂ) x -
      LamB d L V₀c lbar msq b₀ (redZ (n + 2) (ctr d L (n + 2) + x)) =
      (lbOf .two (FO d L V₀c lbar msq b₀ (n + 2) (ctr d L (n + 2)) (ctr d L (n + 2) + x)
        (n + 2)).1 -
        limUnder atTop (lB d L V₀c lbar msq b₀ (redZ (n + 2) (ctr d L (n + 2) + x)))) / lbar := by
    rw [lamB2, LamB, sub_div]
  rw [e1, norm_div, hl, rpow_neg_mul_nat (Nat.cast_nonneg _) κ (n + 2), div_le_iff₀ hlb]
  refine hmain.trans (le_of_eq ?_)
  ring

theorem gB_summable (hd2 : 2 ≤ d) (hd3 : 3 ≤ d) {msq : ℝ} (hmsq : 0 ≤ msq) {b₀ : ℂ}
    (hb₀ : ‖b₀‖ ≤ lbar) {z : Zd d} (hz0 : ∀ i, 0 ≤ z i) :
    Summable (gB d L V₀c lbar msq b₀ z) := by
  have hρ1 := rho_lt_one hd3 (by have := three_le_L H; omega) (L := L)
  exact Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (rho_nonneg d L) hρ1).mul_left
      ((Lm lbar C κ Cs b₀ L + Cs * (C * lbar * ‖b₀‖)) * ℓ₀ ^ 2))
    fun j => (gB_bd H hd hCs hS hd2 hmsq hb₀ hz0 j).trans (le_of_eq (by ring))

/-- **Rate for `γ^{(2)}_b`**, at the reduced point of `ctr_N + x`. -/
theorem gamB2_rate (hd3 : 3 ≤ d) {msq : ℝ} (hmsq : 0 ≤ msq) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar)
    {N : ℕ} (hN : 2 ≤ N) {x : Lam d L N} (hx : x ≠ 0) :
    ‖gamB2 d L N msq (V₀c msq b₀) (lbar : ℂ) x -
        GamB d L V₀c lbar msq b₀ (redZ N (ctr d L N + x))‖ ≤
      K1 lbar C κ Cs L * ℓ₀ ^ 2 * (1 + 1 / (1 - rho d L)) / (rho d L * lbar) *
        (L : ℝ) ^ (-(((d : ℝ) - 2) * N)) := by
  have hd2 : 2 ≤ d := by omega
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hb := ctr_add_ne H hd hCs hS hx
  have hl := norm_lbar H
  have hlb := H.fd.lbar_pos
  have hρ0 := rho_nonneg d L
  have hρ1 := rho_lt_one hd3 (by have := three_le_L H; omega) (L := L)
  have hρp : 0 < rho d L :=
    Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) _
  have hz0 : ∀ i, 0 ≤ redZ (n + 1) (ctr d L (n + 1) + x) i := redZ_nonneg _ _
  have hfin : gbN d L .two (n + 1) msq (V₀c msq b₀) (initObs .two (lbar : ℂ)) (ctr d L (n + 1))
      (ctr d L (n + 1) + x) =
        ∑ j ∈ range n, gB d L V₀c lbar msq b₀ (redZ (n + 1) (ctr d L (n + 1) + x)) j +
        gbOf .two (NA d L V₀c lbar msq b₀ (n + 1) (ctr d L (n + 1)) (ctr d L (n + 1) + x) n) := by
    rw [gbN, sum_range_succ]
    congr 1
    exact sum_congr rfl fun j hj =>
      (lB_eq H hd hmsq hb₀ (N := n + 1) (j := j) (by simp at hj; omega) _ _).2
  have hcore := gam_core H hd hCs hS
    (gB d L V₀c lbar msq b₀ (redZ (n + 1) (ctr d L (n + 1) + x))) _
    (gB_summable H hd hCs hS hd2 hd3 hmsq hb₀ hz0) hρ0 hρ1 (gB_bd H hd hCs hS hd2 hmsq hb₀ hz0)
    (gb_N_bd H hd hCs hS hd2 hmsq hb₀ hb (k := n) (by omega))
  have e1 : gamB2 d L (n + 1) msq (V₀c msq b₀) (lbar : ℂ) x -
      GamB d L V₀c lbar msq b₀ (redZ (n + 1) (ctr d L (n + 1) + x)) =
      ((∑ j ∈ range n, gB d L V₀c lbar msq b₀ (redZ (n + 1) (ctr d L (n + 1) + x)) j +
        gbOf .two (NA d L V₀c lbar msq b₀ (n + 1) (ctr d L (n + 1)) (ctr d L (n + 1) + x) n)) -
        ∑' j, gB d L V₀c lbar msq b₀ (redZ (n + 1) (ctr d L (n + 1) + x)) j) / lbar := by
    rw [gamB2, GamB, hfin, sub_div]
  have hK'le : (Lm lbar C κ Cs b₀ L + Cs * (C * lbar * ‖b₀‖)) * ℓ₀ ^ 2 ≤
      K1 lbar C κ Cs L * ℓ₀ ^ 2 :=
    mul_le_mul_of_nonneg_right (Lm_le H hd hCs hS hb₀) (sq_nonneg _)
  rw [e1, norm_div, hl, rpow_neg_mul_nat (Nat.cast_nonneg _) ((d : ℝ) - 2) (n + 1),
    div_le_iff₀ hlb]
  have h1ρ : 0 < 1 - rho d L := by linarith
  have hρn : 0 ≤ rho d L ^ n := pow_nonneg hρ0 n
  have hq : 0 ≤ 1 + 1 / (1 - rho d L) := by positivity
  have hρne : rho d L ≠ 0 := hρp.ne'
  have hlne : lbar ≠ 0 := hlb.ne'
  have h1ρne : 1 - rho d L ≠ 0 := h1ρ.ne'
  refine hcore.trans ?_
  calc (Lm lbar C κ Cs b₀ L + Cs * (C * lbar * ‖b₀‖)) * ℓ₀ ^ 2 * (1 + 1 / (1 - rho d L)) *
        rho d L ^ n
      ≤ K1 lbar C κ Cs L * ℓ₀ ^ 2 * (1 + 1 / (1 - rho d L)) * rho d L ^ n := by gcongr
    _ = K1 lbar C κ Cs L * ℓ₀ ^ 2 * (1 + 1 / (1 - rho d L)) / (rho d L * lbar) *
          rho d L ^ (n + 1) * lbar := by
        field_simp; ring

end

end Ward
