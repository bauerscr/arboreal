import PtCorr.Defs
import PtCorr.Recur
import PtCorr.CoupBd

/-!
# Summed recursions along the Case-(2) observable flow (helper for `lem:1pt`, `lem:2pt`)

Along `Obs.flowO` (Case (2), started at `initObs .two l₀`), with `‖K^obs_k‖_k ≤ e θ^k` for all
`k ≤ N` (`θ ∈ [0,1)`), the one-step recursions `Obs.Vobs_recursion_two` and the bounds
`Obs.Vobs_bd` are summed over the scales (`PtCorr.Recur`: `lam_tail_N`, `gsum_bound`,
`eta_bound`, `qsum_two_bound`).  All error terms are expressed with one constant
`KTwo Cs θ lb eb` (depending only on the constant `Cs` of `d`, on `θ`, and on upper bounds
`‖l₀‖ ≤ lb`, `e ≤ eb`), in the form `KTwo * e * X`:

* `‖λ_{x,N} - l₀‖ ≤ K e`;
* `‖γ_{x,N} - λ_{x,N} ∑_{k<N} C_k(x,x)‖ ≤ K e ℓ₀²`;
* `‖η_N + 2 λ_{a,N} λ_{b,N} ∑_{k<N} C_k(a,b)‖ ≤ K e ℓ_{j_ab}² θ^{j_ab}`;
* `‖q_N + λ_{a,N} λ_{b,N} (∑_{k<N} C_k(a,b))²‖ ≤ K e ℓ_{j_ab}⁴ θ^{j_ab}`;
* `‖r_{x,N}‖ ≤ K e ℓ_{j_ab}² θ^{j_ab}`.

Here `γ_{x,N}`, `q_N` are the accumulated `u`-parts `PtCorr.gaN`/`gbN`, `PtCorr.qN`.
No hypothesis `a ≠ b`, `a = ctr` or `m² > 0` is needed (the conversion to powers of `|a - b|`
is done in `PtCorr.TwoPtTwo`).  The `λ` of the quadratic terms are the last-scale couplings
`λ_{x,N}` (Tier 1, point-dependent couplings), via `‖λ_{x,k} - λ_{x,N}‖ ≤ C_S e θ^k/(1-θ)` (`lam_tail_N`).
-/

namespace PtCorr

noncomputable section

open Finset Grassmann Loc Step Obs FRD

/-- The constant of `flowTwo_core`. -/
def KTwo (Cs θ lb eb : ℝ) : ℝ :=
  4 * Cs + 8 * (Cs / (1 - θ) * (2 * lb + 3 * (Cs / (1 - θ)) * eb)) + 4 * (Cs / (1 - θ))

theorem KTwo_nonneg {Cs θ lb eb : ℝ} (hCs : 0 ≤ Cs) (hθ1 : θ < 1) (hlb : 0 ≤ lb)
    (heb : 0 ≤ eb) : 0 ≤ KTwo Cs θ lb eb := by
  have : 0 < 1 - θ := by linarith
  unfold KTwo; positivity

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
/-- **Summed Case-(2) recursions** (see the module docstring). -/
theorem flowTwo_core (hd : 3 ≤ d) : ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ (L : ℕ) [NeZero L], 2 ^ (d + 3) ≤ L →
    ∀ (N : ℕ) (msq : ℝ) (V₀ : Vcoup) (ℓ₀ : ℝ), 0 < ℓ₀ →
    (∀ k < N, GoodCov k ℓ₀ (Flow.covAt d L N msq k)) →
    ∀ (l₀ : ℂ) (a b : Lam d L N) (A : ℝ), 1 ≤ A → ∀ (θ e lb eb : ℝ), 0 ≤ θ → θ < 1 → 0 ≤ e →
    ‖l₀‖ ≤ lb → e ≤ eb →
    (∀ k ≤ N, KnormObs .two ℓ₀ a b k A (flowO d L .two N msq V₀ (initObs .two l₀) a b k).2 ≤
      ENNReal.ofReal (e * θ ^ k)) →
    ‖laOf .two (VoN d L .two N msq V₀ (initObs .two l₀) a b) - l₀‖ ≤ KTwo Cs θ lb eb * e ∧
    ‖lbOf .two (VoN d L .two N msq V₀ (initObs .two l₀) a b) - l₀‖ ≤ KTwo Cs θ lb eb * e ∧
    ‖gaN d L .two N msq V₀ (initObs .two l₀) a b -
        laOf .two (VoN d L .two N msq V₀ (initObs .two l₀) a b) *
          ∑ k ∈ range N, (Flow.covAt d L N msq k a a : ℂ)‖ ≤ KTwo Cs θ lb eb * e * ℓ₀ ^ 2 ∧
    ‖gbN d L .two N msq V₀ (initObs .two l₀) a b -
        lbOf .two (VoN d L .two N msq V₀ (initObs .two l₀) a b) *
          ∑ k ∈ range N, (Flow.covAt d L N msq k b b : ℂ)‖ ≤ KTwo Cs θ lb eb * e * ℓ₀ ^ 2 ∧
    ‖etaOf .two (VoN d L .two N msq V₀ (initObs .two l₀) a b) +
        2 * (laOf .two (VoN d L .two N msq V₀ (initObs .two l₀) a b) *
          lbOf .two (VoN d L .two N msq V₀ (initObs .two l₀) a b)) *
          ∑ k ∈ range N, (Flow.covAt d L N msq k a b : ℂ)‖ ≤
      KTwo Cs θ lb eb * e * (ellj d L ℓ₀ (coal L a b) ^ 2 * θ ^ coal L a b) ∧
    ‖qN d L .two N msq V₀ (initObs .two l₀) a b +
        laOf .two (VoN d L .two N msq V₀ (initObs .two l₀) a b) *
          lbOf .two (VoN d L .two N msq V₀ (initObs .two l₀) a b) *
          (∑ k ∈ range N, (Flow.covAt d L N msq k a b : ℂ)) ^ 2‖ ≤
      KTwo Cs θ lb eb * e * (ellj d L ℓ₀ (coal L a b) ^ 4 * θ ^ coal L a b) ∧
    ‖raOf .two (VoN d L .two N msq V₀ (initObs .two l₀) a b)‖ ≤
      KTwo Cs θ lb eb * e * (ellj d L ℓ₀ (coal L a b) ^ 2 * θ ^ coal L a b) ∧
    ‖rbOf .two (VoN d L .two N msq V₀ (initObs .two l₀) a b)‖ ≤
      KTwo Cs θ lb eb * e * (ellj d L ℓ₀ (coal L a b) ^ 2 * θ ^ coal L a b) := by
  obtain ⟨Cs1, hCs1, hrec⟩ := Vobs_recursion_two d
  obtain ⟨Cs2, hCs2, hbd⟩ := Vobs_bd hd
  refine ⟨max Cs1 Cs2, le_trans hCs1 (le_max_left _ _), ?_⟩
  intro L _ hL N msq V₀ ℓ₀ hℓ₀ hC l₀ a b A hA θ e lb eb hθ0 hθ1 he hlb heb hK
  have hCs : 0 ≤ max Cs1 Cs2 := le_trans hCs1 (le_max_left _ _)
  set Cs := max Cs1 Cs2 with hCsdef
  have hd1 : 1 ≤ d := by omega
  have hL2 : 2 ≤ L := by
    have : 2 ^ 1 ≤ 2 ^ (d + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h1θ : 0 < 1 - θ := by linarith
  have hlb0 : 0 ≤ lb := (norm_nonneg _).trans hlb
  have heb0 : 0 ≤ eb := he.trans heb
  set u := Cs / (1 - θ) with hu
  have hu0 : 0 ≤ u := by positivity
  have hu2 : Cs2 / (1 - θ) ≤ u := div_le_div_of_nonneg_right (le_max_right _ _) h1θ.le
  set K := KTwo Cs θ lb eb with hKdef
  have hKe : K = 4 * Cs + 8 * (u * (2 * lb + 3 * u * eb)) + 4 * u := by
    rw [hKdef, KTwo]
  set F := fun k => flowO d L .two N msq V₀ (initObs .two l₀) a b k with hF
  set jab := coal L a b with hjab
  set X2 := ellj d L ℓ₀ jab ^ 2 * θ ^ jab with hX2def
  have hX2 : 0 ≤ X2 := by positivity
  -- the one-step recursions
  have hR := fun k (hk : k < N) => hrec L N k ℓ₀ hℓ₀ (Flow.covAt d L N msq k) (F k).1 (F k).2
    a b A hA (e * θ ^ k) (by positivity) (hK k hk.le)
    (fun hj Y hY => abSmall_flowO V₀ l₀ a b hd1 hL hC hk hj hY)
  -- the bounds of `lem:Vobs-bd`
  have hB := fun k (hk : k ≤ N) => hbd L hL N msq V₀ ℓ₀ hℓ₀ hC .two l₀ a b A hA θ e hθ0 hθ1 he
    k hk (fun k' hk' => hK k' (by omega))
  -- sequences
  set la : ℕ → ℂ := fun k => laOf .two (F k).1 with hla
  set lb' : ℕ → ℂ := fun k => lbOf .two (F k).1 with hlb'
  set ra : ℕ → ℂ := fun k => raOf .two (F k).1 with hra
  set rb : ℕ → ℂ := fun k => rbOf .two (F k).1 with hrb
  set eta : ℕ → ℂ := fun k => etaOf .two (F k).1 with heta
  have hCmono : ∀ {x y : ℝ}, 0 ≤ y → x ≤ Cs1 * y → x ≤ Cs * y := fun hy h =>
    h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hy)
  -- `λ` increments and tails
  have hdla : ∀ k < N, ‖la (k + 1) - la k‖ ≤ Cs * (e * θ ^ k) := fun k hk =>
    hCmono (by positivity) (hR k hk).1
  have hdlb : ∀ k < N, ‖lb' (k + 1) - lb' k‖ ≤ Cs * (e * θ ^ k) := fun k hk =>
    hCmono (by positivity) (hR k hk).2.1
  have hΛe : Cs * e / (1 - θ) = u * e := by rw [hu]; ring
  have htla : ∀ k ≤ N, ‖la k - la N‖ ≤ u * e * θ ^ k := fun k hk => by
    have := lam_tail_N la hCs he hθ0 hθ1 hdla hk; rwa [hΛe] at this
  have htlb : ∀ k ≤ N, ‖lb' k - lb' N‖ ≤ u * e * θ ^ k := fun k hk => by
    have := lam_tail_N lb' hCs he hθ0 hθ1 hdlb hk; rwa [hΛe] at this
  -- `λ_N`
  have hlaN0 : ‖la N - l₀‖ ≤ u * e := by
    refine (hB N le_rfl).1.trans ?_
    calc Cs2 * e / (1 - θ) = Cs2 / (1 - θ) * e := by ring
      _ ≤ u * e := mul_le_mul_of_nonneg_right hu2 he
  have hlbN0 : ‖lb' N - l₀‖ ≤ u * e := by
    refine (hB N le_rfl).2.1.trans ?_
    calc Cs2 * e / (1 - θ) = Cs2 / (1 - θ) * e := by ring
      _ ≤ u * e := mul_le_mul_of_nonneg_right hu2 he
  set M := ‖l₀‖ + u * e with hM
  have hM0 : 0 ≤ M := by positivity
  have hlaN : ‖la N‖ ≤ M := by
    have := norm_sub_norm_le (la N) l₀; linarith
  have hlbN : ‖lb' N‖ ≤ M := by
    have := norm_sub_norm_le (lb' N) l₀; linarith
  -- `r`
  have hrk : ∀ k ≤ N, (‖ra k‖ ≤ u * e * X2 ∧ (k ≤ jab → ra k = 0)) ∧
      (‖rb k‖ ≤ u * e * X2 ∧ (k ≤ jab → rb k = 0)) := by
    intro k hk
    obtain ⟨-, -, h3, h4, h5, -⟩ := hB k hk
    have hconv : Cs2 * sab .two (ellj d L ℓ₀ jab) * e * θ ^ jab / (1 - θ) ≤ u * e * X2 := by
      calc Cs2 * sab .two (ellj d L ℓ₀ jab) * e * θ ^ jab / (1 - θ)
          = Cs2 / (1 - θ) * (e * X2) := by rw [hX2def]; simp only [sab]; ring
        _ ≤ u * (e * X2) := mul_le_mul_of_nonneg_right hu2 (by positivity)
        _ = u * e * X2 := by ring
    exact ⟨⟨h3.trans hconv, fun h => (h5 h).1⟩, ⟨h4.trans hconv, fun h => (h5 h).2⟩⟩
  -- the constant `D`
  have hD : u * e * (M + u * e) + M * (u * e) ≤ u * (2 * lb + 3 * u * eb) * e := by
    have h1 : u * e * (M + u * e) + M * (u * e) = u * e * (2 * ‖l₀‖ + 3 * (u * e)) := by
      rw [hM]; ring
    rw [h1]
    have h2 : 2 * ‖l₀‖ + 3 * (u * e) ≤ 2 * lb + 3 * u * eb := by
      have := mul_le_mul_of_nonneg_left heb hu0; nlinarith
    calc u * e * (2 * ‖l₀‖ + 3 * (u * e)) ≤ u * e * (2 * lb + 3 * u * eb) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = u * (2 * lb + 3 * u * eb) * e := by ring
  have hK1 : 0 ≤ u * (2 * lb + 3 * u * eb) := by positivity
  -- `γ`
  have hga : ‖gaN d L .two N msq V₀ (initObs .two l₀) a b -
      la N * ∑ k ∈ range N, (Flow.covAt d L N msq k a a : ℂ)‖ ≤ K * e * ℓ₀ ^ 2 := by
    have h := gsum_bound hd hL2 hℓ₀ hC a hθ0 hθ1.le he hCs (by positivity : 0 ≤ u * e) la
      (fun k => gaOf .two (nextAt d L .two N msq V₀ (initObs .two l₀) a b k)) htla
      (fun k hk => (hR k hk).2.2.1.trans (by gcongr; exact le_max_left _ _))
    refine h.trans ?_
    rw [hKe]
    have : 0 ≤ ℓ₀ ^ 2 := by positivity
    nlinarith [mul_nonneg hu0 he, mul_nonneg hCs he, mul_nonneg (mul_nonneg hK1 he) this,
      mul_nonneg (mul_nonneg hu0 he) this, mul_nonneg (mul_nonneg hCs he) this]
  have hgb : ‖gbN d L .two N msq V₀ (initObs .two l₀) a b -
      lb' N * ∑ k ∈ range N, (Flow.covAt d L N msq k b b : ℂ)‖ ≤ K * e * ℓ₀ ^ 2 := by
    have h := gsum_bound hd hL2 hℓ₀ hC b hθ0 hθ1.le he hCs (by positivity : 0 ≤ u * e) lb'
      (fun k => gbOf .two (nextAt d L .two N msq V₀ (initObs .two l₀) a b k)) htlb
      (fun k hk => (hR k hk).2.2.2.1.trans (by gcongr; exact le_max_left _ _))
    refine h.trans ?_
    rw [hKe]
    have : 0 ≤ ℓ₀ ^ 2 := by positivity
    nlinarith [mul_nonneg hu0 he, mul_nonneg hCs he, mul_nonneg (mul_nonneg hK1 he) this,
      mul_nonneg (mul_nonneg hu0 he) this, mul_nonneg (mul_nonneg hCs he) this]
  -- `η`
  have h0 : eta 0 = 0 := rfl
  have hetas : ∀ k < N, eta (k + 1) =
      eta k - 2 * la (k + 1) * lb' (k + 1) * (Flow.covAt d L N msq k a b : ℂ) := fun k hk =>
    (hR k hk).2.2.2.2.2.1
  have heta' := eta_bound hd hL2 hℓ₀ hC a b hθ0 hθ1.le (by positivity : 0 ≤ u * e) hM0 la lb'
    eta htla htlb hlaN hlbN h0 hetas
  -- `q`
  have hq := qsum_two_bound hd hL2 hℓ₀ hC a b hθ0 hθ1.le he hCs (by positivity : 0 ≤ u * e) hM0
    la lb' ra rb eta
    (fun k => qaOf .two (nextAt d L .two N msq V₀ (initObs .two l₀) a b k) +
      qbOf .two (nextAt d L .two N msq V₀ (initObs .two l₀) a b k))
    htla htlb hlaN hlbN (fun k hk => (hrk k hk).1) (fun k hk => (hrk k hk).2) h0 hetas
    (fun k hk => by
      have h5 := (hR k hk).2.2.2.2.1
      have hI : (0 : ℝ) ≤ (if coal L a b ≤ k then 1 else 0) := by split_ifs <;> norm_num
      have hE : 0 ≤ (ellab .two (ellj d L ℓ₀ k) (ellj d L ℓ₀ (jwedge k (coal L a b))))⁻¹ := by
        rw [ellab_two_inv]; positivity
      have hy : 0 ≤ 2 * ((ellab .two (ellj d L ℓ₀ k) (ellj d L ℓ₀ (jwedge k (coal L a b))))⁻¹ *
          (e * θ ^ k) * (if coal L a b ≤ k then 1 else 0)) := by positivity
      have := mul_le_mul_of_nonneg_right (le_max_left Cs1 Cs2) hy
      refine h5.trans ?_
      nlinarith)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine hlaN0.trans (mul_le_mul_of_nonneg_right ?_ he)
    rw [hKe]; nlinarith [mul_nonneg hK1 he]
  · refine hlbN0.trans (mul_le_mul_of_nonneg_right ?_ he)
    rw [hKe]; nlinarith [mul_nonneg hK1 he]
  · exact hga
  · exact hgb
  · refine heta'.trans ?_
    have hx : 4 * (u * e * (M + u * e) + M * (u * e)) ≤ K * e := by
      rw [hKe]; nlinarith [mul_nonneg hK1 he, mul_nonneg hu0 he, mul_nonneg hCs he]
    exact mul_le_mul_of_nonneg_right hx hX2
  · have e1 : qN d L .two N msq V₀ (initObs .two l₀) a b = ∑ k ∈ range N,
        (qaOf .two (nextAt d L .two N msq V₀ (initObs .two l₀) a b k) +
          qbOf .two (nextAt d L .two N msq V₀ (initObs .two l₀) a b k)) := rfl
    rw [e1]
    refine hq.trans ?_
    have hX4 : 0 ≤ ellj d L ℓ₀ jab ^ 4 * θ ^ jab := by positivity
    have hr : 4 * (u * e * X2) * ellj d L ℓ₀ jab ^ 2 = 4 * u * e *
        (ellj d L ℓ₀ jab ^ 4 * θ ^ jab) := by rw [hX2def]; ring
    rw [hr]
    have hx : 4 * Cs * e + 8 * (u * e * (M + u * e) + M * (u * e)) + 4 * u * e ≤ K * e := by
      rw [hKe]; nlinarith [mul_nonneg hK1 he, mul_nonneg hu0 he, mul_nonneg hCs he]
    nlinarith [mul_le_mul_of_nonneg_right hx hX4]
  · exact (hrk N le_rfl).1.1.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by rw [hKe]; nlinarith [mul_nonneg hK1 he]) he) hX2)
  · exact (hrk N le_rfl).2.1.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by rw [hKe]; nlinarith [mul_nonneg hK1 he]) he) hX2)

end

end PtCorr
