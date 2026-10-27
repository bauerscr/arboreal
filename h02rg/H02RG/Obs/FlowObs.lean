import Obs.FlowObsBd
import Flow.Main

/-!
# Proposition `prop:flow-obs` (Section `sec:flow-obs`)

The observable flow `flowO` (started at `λ_{a,0} = λ_{b,0} = λ₀`, all other observable
couplings `0`, `K_0 = 0`) along a bulk flow `Flow.flowN` whose norms decay as
`‖V^∅_j‖_j + ‖K^∅_j‖_j ≤ C_b |b₀| L^{-α j}` (`e:flowVK-bis-1`, e.g. the flow of `Flow.thm_flow`,
see `flowObs_of_thm_flow`) satisfies `e:flowVKobs`:
`‖V^obs_j‖_j ≤ C λ₀` and `‖K^obs_j‖_j ≤ C λ₀ b₀ L^{-κ j}` for all `j ≤ N`, when
`|b₀| ≤ |λ₀| ≤ λ̄` (`flowObs`).  The constants `λ̄, C, κ` depend on `L, A, ℓ₀, α, C_b`
(the paper's `O_L`), not on `N`, `j`, `m² ≥ 0`, the bulk initial condition `V₀` or `b`.

The proof is the induction of the text, based on Theorem `thm:step-obs` (`Obs.stepObs`) and
`lem:Vobs-bd` (`Obs.Vobs_bd`), with `κ = min(α, log_L(4/3))`, i.e. `L^{-κ} = max(L^{-α}, 3/4)`.
Along the flow all hypotheses of `thm:step-obs` are verified: `GoodCov` (`covAt_goodCov`),
`K^∅_j ∈ 𝒦_j` (`flowN_inK`), the supports `InKO … True …` and `InKpt` (propagated by
`thm:step-obs` itself), the `ab` condition below `j_ab` (`abSmall_flowO`), the separation
hypothesis (`sepHyp_ctr`), and the smallness conditions.

## Choices and deviations
* **Block centring.**  The text centres the blocks at `a`.  Our blocks are aligned at the origin,
  so we take `L` odd and `a = ctr d L N`, the point with all coordinates `(L^{N-1} - 1)/2`: it is
  the centre of its `j`-block for every `j ≤ N - 1`, which gives the separation hypothesis
  `blk (j+1) a ≠ blk (j+1) b → C_{j+1}(a, b) = 0` of `thm:step-obs` from the finite range
  property (`sepHyp_ctr`; for `j + 1 = N` there is one block).  (With `(L^N-1)/2` instead,
  `a` would be far from the origin, and `Obs.flowO_consist` needs `8|a|_∞ ≤ L^N`; `ctr` satisfies
  `8|ctr|_∞ ≤ L^N`.)  `b ≠ a` is arbitrary.
* **Case (2): locality of the `η` term.**  `thm:step-obs` (`ObsLoc`, via `CoupLoc`) requires
  `η_j = 0` or `NearS j a b`, and the same for `η_{j+1}` (locality at the scale `j + 1` of the
  output `K_{j+1}`).  Along the flow `η_k = 0` for `k ≤ j_ab`, and for `j ≥ j_ab`,
  `2|a-b|_∞ < L^{j_ab+1} ≤ L^{j+1}` gives `NearS j a b` (`nearS_of_coal_le`); so no extra
  hypothesis is needed (`eta_cond`, `eta_cond_succ`).
* `‖V^obs_j‖_j ≤ C λ₀` with the constant `C` (the text: `λ₀ + O_L(λ₀²) + O_L(M λ₀ b₀)`;
  here `2λ₀ + …`, see `Obs.Vobs_bd`).
* Complex `λ₀, b₀` are allowed (the text: `λ₀, b₀ > 0`), with `|b₀| ≤ |λ₀|`.
* For the last step `j + 1 = N`, `thm:step-obs` only gives `‖K^obs_N‖_N ≤ C₀ (L^m + A^{-η})
  ‖K^obs_{N-1}‖ + …`; this is absorbed into the constant `C` (as for `cor:flow-finvol`).
-/

namespace Obs

noncomputable section

open Finset Grassmann SA Loc Step LocObs Gen FRD

variable {d L N : ℕ} [NeZero L]

/-! ### The covariances and the bulk flow -/

/-- The covariances `covAt N m² k = C_{k+1}` (`C_N` for the last step) satisfy `GoodCov`. -/
theorem covAt_goodCov (hd : 3 ≤ d) : ∃ Kg : ℝ, 0 ≤ Kg ∧ ∀ (L : ℕ) [NeZero L], 1 ≤ L →
    ∀ ℓ₀ : ℝ, 0 < ℓ₀ → Kg * (L : ℝ) ^ ((d : ℝ) - 2 + 2 * pPhi d) ≤ ℓ₀ ^ 2 →
    ∀ (N : ℕ) (msq : ℝ), 0 ≤ msq → ∀ k < N,
      GoodCov (d := d) (L := L) (N := N) k ℓ₀ (Flow.covAt d L N msq k) := by
  obtain ⟨K1, hK1, h1⟩ := goodCov_Cfrd hd
  obtain ⟨K2, hK2, h2⟩ := goodCov_CfrdN hd
  refine ⟨max K1 K2, le_trans hK1 (le_max_left _ _), ?_⟩
  intro L _ hL ℓ₀ hℓ₀ hK N msq hmsq k hk
  have hpos : (0 : ℝ) ≤ (L : ℝ) ^ ((d : ℝ) - 2 + 2 * pPhi d) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  rcases Nat.lt_or_ge (k + 1) N with h | h
  · rw [Flow.covAt_lt h]
    exact h1 L hL ℓ₀ hℓ₀ ((mul_le_mul_of_nonneg_right (le_max_left _ _) hpos).trans hK) N k h
      msq hmsq
  · obtain rfl : N = k + 1 := by omega
    rw [Flow.covAt_last]
    exact h2 L hL ℓ₀ hℓ₀ ((mul_le_mul_of_nonneg_right (le_max_right _ _) hpos).trans hK) k msq hmsq

/-- The bulk activities of the flow lie in `𝒦_j` (for `j < N`). -/
theorem flowN_inK (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {ℓ₀ msq : ℝ} (V₀ : Vcoup)
    (hC : ∀ k < N, GoodCov (d := d) (L := L) (N := N) k ℓ₀ (Flow.covAt d L N msq k)) :
    ∀ j < N, InK j (Flow.flowN d L N msq V₀ j).2 := by
  intro j
  induction j with
  | zero => intro _; exact InK.zero 0
  | succ j ih =>
    intro hj
    rw [Flow.flowN_succ]
    exact (Flow.restr_mem (by omega) (InK_Knext hd hL hj (hC j (by omega)) _
      (ih (by omega)))).1

/-! ### The centre point and the separation hypothesis -/

variable (d L N) in
/-- The point with all coordinates `(L^{N-1} - 1)/2`: for `L` odd it is the centre of its
`j`-block for all `j ≤ N - 1`. -/
def ctr : Lam d L N := fun _ => (((L ^ (N - 1) - 1) / 2 : ℕ) : ZMod (L ^ N))

theorem ctr_val (hL : 2 ≤ L) (i : Fin d) :
    (co (ctr d L N) i).val = (L ^ (N - 1) - 1) / 2 := by
  show ((((L ^ (N - 1) - 1) / 2 : ℕ) : ZMod (L ^ N))).val = _
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt]
  have h1 : L ^ (N - 1) ≤ L ^ N := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : 0 < L ^ (N - 1) := by positivity
  omega

theorem supNorm_ge_zabs (x : Lam d L N) (i : Fin d) :
    zabs ((x : Fin d → ZMod (L ^ N)) i) ≤ supNorm x :=
  Finset.le_sup (f := fun i => zabs ((x : Fin d → ZMod (L ^ N)) i)) (mem_univ i)

/-- `|a - b|_∞ ≥ (L^{j+1} + 1)/2` if `a = ctr` and `b` lie in different `(j+1)`-blocks. -/
theorem supNorm_ctr_sub (hLodd : Odd L) (hL : 2 ≤ L) {j : ℕ} (hj : j + 1 < N) (b : Lam d L N)
    (hne : blk (j + 1) (ctr d L N) ≠ blk (j + 1) b) :
    (L ^ (j + 1) + 1) / 2 ≤ supNorm (ctr d L N - b) := by
  obtain ⟨i, hi⟩ : ∃ i, blk (j + 1) (ctr d L N) i ≠ blk (j + 1) b i := by
    by_contra h; push Not at h; exact hne (funext h)
  set u := L ^ (j + 1) with hu
  set w := L ^ (N - 1 - (j + 1)) with hw
  set P := L ^ (N - 1) with hPdef
  set n := L ^ N with hn
  have hP : P = u * w := by rw [hPdef, hu, hw, ← pow_add]; congr 1; omega
  have hnP : n = L * P := by rw [hn, hPdef, ← pow_succ']; congr 1; omega
  obtain ⟨t, ht⟩ := hLodd.pow (n := j + 1)
  obtain ⟨q, hq⟩ := hLodd.pow (n := N - 1 - (j + 1))
  rw [← hu] at ht
  rw [← hw] at hq
  have hu0 : 0 < u := by omega
  have huw : u * w = 2 * (t + u * q) + 1 := by rw [hq, ht]; ring
  have hcv : (P - 1) / 2 = t + u * q := by rw [hP]; omega
  have hPu : u ≤ P := by rw [hP]; exact Nat.le_mul_of_pos_right u (by omega)
  have hnP2 : 2 * P ≤ n := by rw [hnP]; exact Nat.mul_le_mul_right P hL
  have hval := ctr_val (d := d) (N := N) hL i
  rw [← hPdef, hcv] at hval
  have hblk : blk (j + 1) (ctr d L N) i = q := by
    show (co (ctr d L N) i).val / L ^ (j + 1) = q
    rw [hval, ← hu, Nat.add_mul_div_left t q hu0, Nat.div_eq_of_lt (by omega), zero_add]
  set v := (co b i).val with hv
  have hvn : v < n := ZMod.val_lt _
  have hbv : blk (j + 1) b i = v / u := rfl
  rw [hblk, hbv] at hi
  have hsub : ((ctr d L N - b : Lam d L N) : Fin d → ZMod n) i = co (ctr d L N) i - co b i := rfl
  refine le_trans ?_ (supNorm_ge_zabs _ i)
  rw [hsub]
  have hq1 : u * q ≤ t + u * q := Nat.le_add_left _ _
  rcases lt_or_gt_of_ne hi.symm with h | h
  · -- `b` in an earlier block: `v < q u`
    have hv1 : v < q * u := (Nat.div_lt_iff_lt_mul hu0).1 h
    have hle : (co b i).val ≤ (co (ctr d L N) i).val := by rw [hval, ← hv]; nlinarith
    rw [zabs, ZMod.val_sub hle, hval, ← hv]
    refine le_min ?_ ?_
    · have : q * u = u * q := mul_comm _ _
      omega
    · omega
  · -- `b` in a later block: `v ≥ (q + 1) u`
    have hv1 : (q + 1) * u ≤ v := (Nat.le_div_iff_mul_le hu0).1 h
    have hle : (co (ctr d L N) i).val ≤ (co b i).val := by
      rw [hval, ← hv]; nlinarith
    rw [← neg_sub, zabs_neg, zabs, ZMod.val_sub hle, hval, ← hv]
    refine le_min ?_ ?_
    · have : (q + 1) * u = u * q + u := by ring
      omega
    · omega

/-- **The separation hypothesis** for `a = ctr` (`L` odd): `blk_{j+1}(a) ≠ blk_{j+1}(b)` implies
`C_{j+1}(a, b) = 0`, for all `j < N`. -/
theorem sepHyp_ctr (hLodd : Odd L) (hL : 2 ≤ L) {j : ℕ} (hj : j < N) {ℓ₀ : ℝ}
    {C : Matrix (Lam d L N) (Lam d L N) ℝ} (hC : GoodCov j ℓ₀ C) (b : Lam d L N) :
    SepHyp j C (ctr d L N) b := by
  intro hne
  rcases Nat.lt_or_ge (j + 1) N with h | h
  · apply hC.range h
    have h1 := supNorm_ctr_sub hLodd hL h b hne
    obtain ⟨t, ht⟩ := hLodd.pow (n := j + 1)
    have h2 : ((L ^ (j + 1) + 1) / 2 : ℕ) = t + 1 := by omega
    rw [h2] at h1
    have h3 : ((L : ℝ) ^ (j + 1)) = 2 * t + 1 := by exact_mod_cast ht
    have h4 : ((t + 1 : ℕ) : ℝ) ≤ supNorm (ctr d L N - b) := by exact_mod_cast h1
    push_cast at h4
    rw [h3]; linarith
  · exfalso
    apply hne
    funext i
    have hNj : N = j + 1 := by omega
    have e1 : ∀ x : Lam d L N, blk (j + 1) x i = 0 := fun x => by
      show (co x i).val / L ^ (j + 1) = 0
      rw [← hNj]; exact Nat.div_eq_of_lt (ZMod.val_lt _)
    rw [e1, e1]

/-- For `L` odd, `j_ab < N` (as `2|x|_∞ < L^N`). -/
theorem coal_lt_of_odd (hLodd : Odd L) (hN : 1 ≤ N) (a b : Lam d L N) : coal L a b < N := by
  have hLN : Odd (L ^ N) := hLodd.pow
  have h1 : 2 * supNorm (a - b) < L ^ N := by
    have : supNorm (a - b) ≤ (L ^ N - 1) / 2 := by
      refine Finset.sup_le fun i _ => ?_
      have h2 := zabs_le_val ((a - b : Lam d L N) i)
      have h3 := zabs_le_sub_val ((a - b : Lam d L N) i)
      obtain ⟨k, hk⟩ := hLN
      omega
    obtain ⟨k, hk⟩ := hLN
    omega
  unfold coal
  by_cases h0 : 2 * supNorm (a - b) = 0
  · rw [h0, Nat.log_zero_right]; omega
  · exact Nat.log_lt_of_lt_pow h0 h1

/-! ### Norms of restricted activities -/

section Norms

variable {c : Case} {ℓ₀ : ℝ} {a b : Lam d L N}

theorem KnormObs_restrO (j : ℕ) (A : ℝ) (K : Finset (Lam d L N) → OE c (Lam d L N)) :
    KnormObs c ℓ₀ a b j A (restrO j K) = KnormObs c ℓ₀ a b j A K := by
  unfold KnormObs KnormFull
  refine iSup_congr fun X => iSup_congr fun hX => ?_
  dsimp only
  rw [restrO_of_conn _ (by simpa [connSets] using hX)]

theorem KnormObs_zero (j : ℕ) (A : ℝ) :
    KnormObs c ℓ₀ a b j A (0 : Finset (Lam d L N) → OE c (Lam d L N)) = 0 := by
  refine le_antisymm (iSup₂_le fun X _ => ?_) zero_le
  simp only [wnormO, Pi.zero_apply, map_zero, nrmj_zero, mul_zero, le_refl]

theorem VnormFull_le (j : ℕ) (Vb : Vcoup) (Vo : Coup c) :
    VnormFull c ℓ₀ a b j Vb Vo ≤
      Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) Vb + VnormObs c ℓ₀ a b j Vo := by
  refine iSup₂_le fun p hp => ?_
  rw [VfullX]
  refine (nrmj_add_le j _ _).trans (add_le_add ?_ (le_iSup₂_of_le (f := fun p _ =>
    nrmj c ℓ₀ a b j (splitO c (Coup.toV c Vo) a b (blockSet j p))) p hp le_rfl))
  rw [nrmj_emb, coe_VE]
  exact le_iSup₂_of_le (f := fun p _ => Tj d (L : ℝ) j (ellj d L ℓ₀ j)
    (Vb.eval (blockSet (L := L) (N := N) j p))) p hp le_rfl

theorem InKO_restrO {P : Prop} {j : ℕ} {K : Finset (Lam d L N) → OE c (Lam d L N)}
    (h : InKO c P a b j K) : InKO c P a b j (restrO j K) := fun X hX => by
  rw [restrO_of_conn _ hX]; exact h X hX

theorem InKpt_restrO {j : ℕ} {K : Finset (Lam d L N) → OE c (Lam d L N)}
    (h : InKpt c a b j K) : InKpt c a b j (restrO j K) := fun X hX => by
  rw [restrO_of_conn _ hX]; exact h X hX

end Norms

/-- **From the coalescence scale on, `a` and `b` are close at the next scale**:
`2|a - b|_∞ < L^{j_ab + 1} ≤ L^{j+1}`. -/
theorem nearS_of_coal_le (hd : 1 ≤ d) (hL : 2 ≤ L) {j : ℕ} (hj : j + 1 ≤ N) {a b : Lam d L N}
    (hc : coal L a b ≤ j) : NearS j a b := by
  refine nearS_of_le hd hj ?_
  have h1 : 2 * supNorm (a - b) < L ^ (coal L a b + 1) := by
    unfold coal; exact Nat.lt_pow_succ_log_self (by omega) _
  have h2 : L ^ (coal L a b + 1) ≤ L ^ (j + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-! ### The `η` locality conditions (Case (2)) -/

section Eta

variable {c : Case} {msq ℓ₀ : ℝ} (V₀ : Vcoup) (l₀ : ℂ) (a b : Lam d L N)

theorem eta_cond (hd1 : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L)
    (hC : ∀ k < N, GoodCov k ℓ₀ (Flow.covAt d L N msq k)) {k : ℕ} (hk : k < N) :
    etaOf c (flowO d L c N msq V₀ (initObs c l₀) a b k).1 = 0 ∨ NearS k a b := by
  cases c
  · exact Or.inl rfl
  · by_cases h : coal L a b ≤ k
    · have h2 : 2 ≤ 2 ^ (d + 3) := Nat.le_self_pow (by omega) 2
      exact Or.inr (nearS_of_coal_le hd1 (by omega) (by omega) h)
    · exact Or.inl (flowO_ab (c := .two) V₀ l₀ a b hd1 hL hC k (by omega)).1.1

theorem eta_cond_succ (hd1 : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L)
    (hC : ∀ k < N, GoodCov k ℓ₀ (Flow.covAt d L N msq k)) (hcoal : coal L a b < N)
    {j : ℕ} (hj : j < N) :
    etaOf c (flowO d L c N msq V₀ (initObs c l₀) a b (j + 1)).1 = 0 ∨ NearS j a b := by
  cases c
  · exact Or.inl rfl
  · by_cases h : coal L a b ≤ j
    · have h2 : 2 ≤ 2 ^ (d + 3) := Nat.le_self_pow (by omega) 2
      exact Or.inr (nearS_of_coal_le hd1 (by omega) (by omega) h)
    · exact Or.inl (flowO_ab (c := .two) V₀ l₀ a b hd1 hL hC (j + 1) (by omega)).1.1

end Eta

/-! ### The real inequality of the induction step -/

theorem real_step {C₀f B2 D Cb CV M lam β T : ℝ} (_hC₀f0 : 0 ≤ C₀f) (hB2 : 0 ≤ B2)
    (hCb : 0 ≤ Cb) (_hCV : 0 ≤ CV) (hD : Cb + CV + 1 ≤ D) (hlam0 : 0 ≤ lam) (hβ0 : 0 ≤ β)
    (hβl : β ≤ lam) (hT0 : 0 ≤ T) (hT1 : T ≤ 1) (hM0 : 0 ≤ M) (hel : M * lam * β ≤ lam)
    (hBD : B2 * D * lam ≤ 3 / 16) (hM : 8 / 3 * (B2 * D * Cb) ≤ M) :
    C₀f * (M * lam * β * T) +
        B2 * (Cb * β * T + M * lam * β * T) * (Cb * β * T + CV * lam + M * lam * β * T) ≤
      (C₀f + 9 / 16) * (M * lam * β * T) := by
  set E := M * lam * β * T with hE
  have hE0 : 0 ≤ E := by positivity
  have hβT : β * T ≤ lam := by nlinarith
  have hEl : E ≤ lam := by
    calc E = (M * lam * β) * T := rfl
      _ ≤ lam * 1 := mul_le_mul hel hT1 hT0 hlam0
      _ = lam := mul_one _
  have h2 : Cb * β * T + CV * lam + E ≤ D * lam := by
    have : Cb * β * T ≤ Cb * lam := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hβT hCb
    nlinarith
  have hX0 : 0 ≤ Cb * β * T + E := by positivity
  have h4 : B2 * (Cb * β * T + E) * (Cb * β * T + CV * lam + E) ≤
      B2 * (Cb * β * T + E) * (D * lam) := mul_le_mul_of_nonneg_left h2 (by positivity)
  have h5 : B2 * (Cb * β * T + E) * (D * lam) =
      (B2 * D * Cb) * (lam * β * T) + (B2 * D * lam) * E := by rw [hE]; ring
  have h6 : (B2 * D * Cb) * (lam * β * T) ≤ 3 / 8 * E := by
    have : 0 ≤ lam * β * T := by positivity
    calc (B2 * D * Cb) * (lam * β * T) ≤ (3 / 8 * M) * (lam * β * T) := by
          apply mul_le_mul_of_nonneg_right _ this; linarith
      _ = 3 / 8 * E := by rw [hE]; ring
  have h7 : (B2 * D * lam) * E ≤ 3 / 16 * E := mul_le_mul_of_nonneg_right hBD hE0
  nlinarith

/-! ### Proposition `prop:flow-obs` -/

set_option maxHeartbeats 4000000 in
/-- **Proposition `prop:flow-obs`** (`e:flowVKobs`; see the module docstring).  For `L ≥ L₀`
odd, `A ≥ A₀(L)`, `ℓ₀^2 ≥ K_ℓ L^{d-2+2p_Φ}`, and a bulk flow with
`‖V^∅_j‖_j + ‖K^∅_j‖_j ≤ C_b |b₀| L^{-α j}` (`j ≤ N`), there are `λ̄ > 0`, `C ≥ 0`, `κ > 0`
(depending on `L, A, ℓ₀, α, C_b` only) such that for `|b₀| ≤ |λ₀| ≤ λ̄`, `a = ctr`, `b ≠ a`
(no condition relating `a`, `b` in either case): for all `j ≤ N`,
`‖V^obs_j‖_j ≤ C |λ₀|` and `‖K^obs_j‖_j ≤ C |λ₀| |b₀| L^{-κ j}`. -/
theorem flowObs (hd : 3 ≤ d) : ∃ (L₀ : ℕ) (Kℓ : ℝ), 0 ≤ Kℓ ∧ ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    Odd L → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∀ ℓ₀ : ℝ, 0 < ℓ₀ →
    Kℓ * (L : ℝ) ^ ((d : ℝ) - 2 + 2 * pPhi d) ≤ ℓ₀ ^ 2 →
    ∀ α Cb : ℝ, 0 < α → 0 ≤ Cb →
    ∃ lbar Cf κ : ℝ, 0 < lbar ∧ 0 ≤ Cf ∧ 0 < κ ∧
    ∀ (c : Case) (N : ℕ) (msq : ℝ) (V₀ : Vcoup) (l₀ b₀ : ℂ) (b : Lam d L N), 0 ≤ msq →
      (∀ j ≤ N, Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j)
            (Flow.flowN d L N msq V₀ j).1 +
          Knorm j (ellj d L ℓ₀ j) A (Flow.flowN d L N msq V₀ j).2 ≤
        ENNReal.ofReal (Cb * ‖b₀‖ * (L : ℝ) ^ (-(α * j)))) →
      ‖b₀‖ ≤ ‖l₀‖ → ‖l₀‖ ≤ lbar → b ≠ ctr d L N →
      ∀ j ≤ N,
        VnormObs c ℓ₀ (ctr d L N) b j
            (flowO d L c N msq V₀ (initObs c l₀) (ctr d L N) b j).1 ≤
          ENNReal.ofReal (Cf * ‖l₀‖) ∧
        KnormObs c ℓ₀ (ctr d L N) b j A
            (flowO d L c N msq V₀ (initObs c l₀) (ctr d L N) b j).2 ≤
          ENNReal.ofReal (Cf * ‖l₀‖ * ‖b₀‖ * (L : ℝ) ^ (-(κ * j))) := by
  obtain ⟨C₀, η, ν, m, Ls, hC₀, hη, hν, hS⟩ := stepObs hd
  obtain ⟨Kg, hKg, hgood⟩ := covAt_goodCov hd
  obtain ⟨Cs, hCs, hVbd⟩ := Vobs_bd hd
  set X : ℝ := 32 * (C₀ + 1) / 3 with hX
  have hX0 : 0 < X := by positivity
  have hX3 : (C₀ + 1) * X⁻¹ = 3 / 32 := by rw [hX]; field_simp
  refine ⟨max Ls (max (2 ^ (d + 3)) (⌈X ^ 2⌉₊ + 1)), Kg, hKg, ?_⟩
  intro L _ hL hLodd
  have hLs : Ls ≤ L := le_trans (le_max_left _ _) hL
  have hL8 : 2 ^ (d + 3) ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
  have hLX : ⌈X ^ 2⌉₊ + 1 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
  have hL2 : 2 ≤ L := by
    have : 2 ^ 1 ≤ 2 ^ (d + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hd1 : 1 ≤ d := by omega
  have hLr1 : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  have hLr0 : (0 : ℝ) < L := by linarith
  -- `C₀ L^{-d_+} ≤ 3/32`
  have hLd : C₀ * (L : ℝ) ^ (-dplus d) ≤ 3 / 32 := by
    have h1 := Flow.rpow_neg_dplus_le hd hLr1.le
    have h2 : X ≤ Real.sqrt L := by
      rw [Real.le_sqrt hX0.le hLr0.le]
      have := Nat.le_ceil (X ^ 2)
      have h3 : ((⌈X ^ 2⌉₊ + 1 : ℕ) : ℝ) ≤ L := by exact_mod_cast hLX
      push_cast at h3; linarith
    have h3 : (Real.sqrt L)⁻¹ ≤ X⁻¹ := inv_anti₀ hX0 h2
    calc C₀ * (L : ℝ) ^ (-dplus d) ≤ C₀ * X⁻¹ := mul_le_mul_of_nonneg_left (h1.trans h3) hC₀
      _ ≤ (C₀ + 1) * X⁻¹ := mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.2 hX0.le)
      _ = 3 / 32 := hX3
  obtain ⟨As, hAs1, hS'⟩ := hS L hLs
  set A₁ : ℝ := X ^ (1 / η) with hA₁
  refine ⟨max As (max A₁ 1), le_trans hAs1 (le_max_left _ _), ?_⟩
  intro A hA ℓ₀ hℓ₀ hKℓ α Cb hα hCb
  have hAAs : As ≤ A := le_trans (le_max_left _ _) hA
  have hAA₁ : A₁ ≤ A := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hA
  have hA1 : 1 ≤ A := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hA
  have hA0 : 0 < A := by linarith
  have hAη : C₀ * A ^ (-η) ≤ 3 / 32 := by
    have h1 : X ≤ A ^ η := by
      have := Real.rpow_le_rpow (by positivity) hAA₁ hη.le
      rwa [hA₁, ← Real.rpow_mul hX0.le, one_div_mul_cancel hη.ne', Real.rpow_one] at this
    have h2 : A ^ (-η) ≤ X⁻¹ := by
      rw [Real.rpow_neg hA0.le]; exact inv_anti₀ hX0 h1
    calc C₀ * A ^ (-η) ≤ C₀ * X⁻¹ := mul_le_mul_of_nonneg_left h2 hC₀
      _ ≤ (C₀ + 1) * X⁻¹ := mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.2 hX0.le)
      _ = 3 / 32 := hX3
  have hAη1 : A ^ (-η) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hA1 (by linarith)
  obtain ⟨ε, hε, hstep⟩ := hS' A hAAs
  -- the rate `θ = L^{-κ} = max(L^{-α}, 3/4)`
  set κ : ℝ := min α (Real.logb L (4 / 3)) with hκdef
  have hκ : 0 < κ := lt_min hα (Real.logb_pos hLr1 (by norm_num))
  set θ : ℝ := (L : ℝ) ^ (-κ) with hθdef
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hLr1 (by linarith)
  have hθ34 : 3 / 4 ≤ θ := by
    have h1 : (L : ℝ) ^ (-Real.logb L (4 / 3)) ≤ θ :=
      Real.rpow_le_rpow_of_exponent_le hLr1.le
        (by have := min_le_right α (Real.logb L (4 / 3)); linarith)
    rw [Real.rpow_neg hLr0.le, Real.rpow_logb hLr0 hLr1.ne' (by norm_num)] at h1
    norm_num at h1; linarith
  have hθpow : ∀ j : ℕ, (L : ℝ) ^ (-(κ * j)) = θ ^ j := fun j => by
    rw [hθdef, ← Real.rpow_natCast, ← Real.rpow_mul hLr0.le]; congr 1; ring
  have hαθ : ∀ j : ℕ, (L : ℝ) ^ (-(α * j)) ≤ θ ^ j := fun j => by
    rw [← hθpow]
    refine Real.rpow_le_rpow_of_exponent_le hLr1.le ?_
    have := min_le_left α (Real.logb L (4 / 3))
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith
  -- constants
  have h1θ : 0 < 1 - θ := by linarith
  set G : ℝ := 1 + Cs / (1 - θ) with hG
  have hG1 : 1 ≤ G := by
    have : 0 ≤ Cs / (1 - θ) := by positivity
    linarith
  set CV : ℝ := 4 * G + 4 * G ^ 2 with hCV
  have hCV0 : 0 ≤ CV := by positivity
  set D : ℝ := Cb + CV + 1 with hD
  have hD1 : 1 ≤ D := by linarith
  set B2 : ℝ := C₀ * A ^ ν with hB2
  have hB20 : 0 ≤ B2 := by positivity
  set M : ℝ := max 1 (8 / 3 * (B2 * D * Cb)) with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMb : 8 / 3 * (B2 * D * Cb) ≤ M := le_max_right _ _
  set M' : ℝ := M * (C₀ * ((L : ℝ) ^ m + 1) + 1) / θ with hM'
  have hθpos : 0 < θ := by linarith
  have hMM' : M ≤ M' := by
    rw [hM', le_div_iff₀ hθpos]
    have : 0 ≤ C₀ * ((L : ℝ) ^ m + 1) := by positivity
    nlinarith
  set lbar : ℝ := min 1 (min (1 / M) (min (3 / (16 * (B2 * D + 1)))
    (min (ε / (2 * (Cb + 1))) (ε / (2 * (CV + 1)))))) with hlbar
  have hlbar : 0 < lbar := by
    refine lt_min one_pos (lt_min (by positivity) (lt_min (by positivity)
      (lt_min (by positivity) (by positivity))))
  refine ⟨lbar, max CV M', κ, hlbar, le_trans hCV0 (le_max_left _ _), hκ, ?_⟩
  intro c N msq V₀ l₀ b₀ b hmsq hbulk hbl hll hb
  have hC := hgood L (by omega) ℓ₀ hℓ₀ hKℓ N msq hmsq
  set lam := ‖l₀‖ with hlam
  set β := ‖b₀‖ with hβ
  have hlam0 : 0 ≤ lam := norm_nonneg _
  have hβ0 : 0 ≤ β := norm_nonneg _
  have hlam1 : lam ≤ 1 := hll.trans (min_le_left _ _)
  have hlamM : lam ≤ 1 / M := hll.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hlamB : lam ≤ 3 / (16 * (B2 * D + 1)) :=
    hll.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hlamε1 : lam ≤ ε / (2 * (Cb + 1)) := hll.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hlamε2 : lam ≤ ε / (2 * (CV + 1)) := hll.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hMβ : M * β ≤ 1 := by
    have := hbl.trans hlamM
    rw [le_div_iff₀ (by linarith)] at this
    linarith
  set e : ℝ := M * lam * β with he
  have he0 : 0 ≤ e := by positivity
  have hel : e ≤ lam := by
    calc e = lam * (M * β) := by rw [he]; ring
      _ ≤ lam * 1 := mul_le_mul_of_nonneg_left hMβ hlam0
      _ = lam := mul_one _
  have hBD : B2 * D * lam ≤ 3 / 16 := by
    rw [le_div_iff₀ (by positivity)] at hlamB
    nlinarith
  set a := ctr d L N with ha
  -- the `V^obs` bound (`lem:Vobs-bd`)
  have hVo : ∀ j ≤ N, (∀ k < j, KnormObs c ℓ₀ a b k A
      (flowO d L c N msq V₀ (initObs c l₀) a b k).2 ≤ ENNReal.ofReal (e * θ ^ k)) →
      VnormObs c ℓ₀ a b j (flowO d L c N msq V₀ (initObs c l₀) a b j).1 ≤
        ENNReal.ofReal (CV * lam) := by
    intro j hj hK
    refine (hVbd L hL8 N msq V₀ ℓ₀ hℓ₀ hC c l₀ a b A hA1 θ e hθ0 hθ1 he0 j hj
      hK).2.2.2.2.2.2.2.trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : Cs * e / (1 - θ) ≤ (G - 1) * lam := by
      rw [hG, add_sub_cancel_left, div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hel hCs) h1θ.le
    have h2 : lam + Cs * e / (1 - θ) ≤ G * lam := by nlinarith
    have h3 : (lam + Cs * e / (1 - θ)) ^ 2 ≤ G ^ 2 * lam := by
      have h0 : 0 ≤ lam + Cs * e / (1 - θ) := by positivity
      calc (lam + Cs * e / (1 - θ)) ^ 2 ≤ (G * lam) ^ 2 := pow_le_pow_left₀ h0 h2 2
        _ = G ^ 2 * lam * lam := by ring
        _ ≤ G ^ 2 * lam * 1 := mul_le_mul_of_nonneg_left hlam1 (by positivity)
        _ = G ^ 2 * lam := mul_one _
    have h4 : CV * lam = 4 * (G * lam) + 4 * (G ^ 2 * lam) := by rw [hCV]; ring
    nlinarith
  -- one step of the flow (Theorem `thm:step-obs`)
  have hstepj : ∀ j, j < N → (∀ k ≤ j, KnormObs c ℓ₀ a b k A
      (flowO d L c N msq V₀ (initObs c l₀) a b k).2 ≤ ENNReal.ofReal (e * θ ^ k)) →
      InKO c True a b j (flowO d L c N msq V₀ (initObs c l₀) a b j).2 →
      InKpt c a b j (flowO d L c N msq V₀ (initObs c l₀) a b j).2 →
      InKO c True a b (j + 1) (flowO d L c N msq V₀ (initObs c l₀) a b (j + 1)).2 ∧
      InKpt c a b (j + 1) (flowO d L c N msq V₀ (initObs c l₀) a b (j + 1)).2 ∧
      KnormObs c ℓ₀ a b (j + 1) A (flowO d L c N msq V₀ (initObs c l₀) a b (j + 1)).2 ≤
        ENNReal.ofReal (C₀ * ((if j + 1 < N then (L : ℝ) ^ (-dplus d) else (L : ℝ) ^ m) +
            A ^ (-η)) * (M * lam * β * θ ^ j) +
          B2 * (Cb * β * θ ^ j + M * lam * β * θ ^ j) *
            (Cb * β * θ ^ j + CV * lam + M * lam * β * θ ^ j)) := by
    intro j hj hK hO hP
    have hcoal : coal L a b < N := coal_lt_of_odd hLodd (by omega) a b
    have hloc : ObsLoc c True j (Flow.covAt d L N msq j)
        (flowO d L c N msq V₀ (initObs c l₀) a b j).1
        (flowO d L c N msq V₀ (initObs c l₀) a b j).2 a b :=
      ⟨hO, fun h => (h trivial).elim,
        coupLoc_true_of_eta (by
          rw [etaOf_toV]; exact eta_cond V₀ l₀ a b hd1 hL8 hC hj),
        coupLoc_true_of_eta (eta_cond_succ V₀ l₀ a b hd1 hL8 hC hcoal hj),
        coupLoc_true_of_eta (Or.inl (etaOf_toU _ _))⟩
    have hH : StepObsHyp c True j ℓ₀ (Flow.covAt d L N msq j) (Flow.flowN d L N msq V₀ j).1
        (flowO d L c N msq V₀ (initObs c l₀) a b j).1
        (flowO d L c N msq V₀ (initObs c l₀) a b j).2 a b :=
      { cov := hC j hj
        bulk := by rw [bulkK_flowO]; exact flowN_inK hd1 hL8 V₀ hC j hj
        hab := fun h => hb h.symm
        loc := hloc
        pt := hP
        abSmall := fun h Y hY => abSmall_flowO V₀ l₀ a b hd1 hL8 hC hj h hY }
    have hb1 := hbulk j hj.le
    have hBj : Cb * β * (L : ℝ) ^ (-(α * j)) ≤ Cb * β * θ ^ j :=
      mul_le_mul_of_nonneg_left (hαθ j) (by positivity)
    have hθj1 : θ ^ j ≤ 1 := pow_le_one₀ hθ0 hθ1.le
    have hθj0 : 0 ≤ θ ^ j := by positivity
    have hvkb : Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) (Flow.flowN d L N msq V₀ j).1 +
        Knorm j (ellj d L ℓ₀ j) A (bulkK (flowO d L c N msq V₀ (initObs c l₀) a b j).2) ≤
        ENNReal.ofReal (Cb * β * θ ^ j) := by
      rw [bulkK_flowO]; exact hb1.trans (ENNReal.ofReal_le_ofReal hBj)
    have hsm1 : Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) (Flow.flowN d L N msq V₀ j).1 +
        Knorm j (ellj d L ℓ₀ j) A (bulkK (flowO d L c N msq V₀ (initObs c l₀) a b j).2) ≤
        ENNReal.ofReal ε := by
      refine hvkb.trans (ENNReal.ofReal_le_ofReal ?_)
      have h2 : Cb * β ≤ ε / 2 := by
        have := hbl.trans hlamε1
        rw [le_div_iff₀ (by positivity)] at this
        nlinarith
      calc Cb * β * θ ^ j ≤ Cb * β * 1 := mul_le_mul_of_nonneg_left hθj1 (by positivity)
        _ ≤ ε := by linarith
    have hvo := hVo j hj.le (fun k hk => hK k hk.le)
    have hko := hK j le_rfl
    have hsm2 : VnormObs c ℓ₀ a b j (flowO d L c N msq V₀ (initObs c l₀) a b j).1 +
        KnormObs c ℓ₀ a b j A (flowO d L c N msq V₀ (initObs c l₀) a b j).2 ≤
        ENNReal.ofReal ε := by
      refine (add_le_add hvo hko).trans ?_
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h2 : (CV + 1) * lam ≤ ε / 2 := by
        rw [le_div_iff₀ (by positivity)] at hlamε2
        nlinarith
      have : e * θ ^ j ≤ lam := (mul_le_mul_of_nonneg_left hθj1 he0).trans (by rw [mul_one]; exact hel)
      nlinarith
    obtain ⟨-, -, hO', hP', hK'⟩ := hstep N j hj ℓ₀ hℓ₀ c True _ _ _ _ a b hH
      (sepHyp_ctr hLodd hL2 hj (hC j hj) b) hsm1 hsm2
    refine ⟨InKO_restrO hO', InKpt_restrO hP', ?_⟩
    rw [show (flowO d L c N msq V₀ (initObs c l₀) a b (j + 1)).2 = restrO (j + 1)
      (KnextO j (Flow.covAt d L N msq j) (Flow.flowN d L N msq V₀ j).1
        (flowO d L c N msq V₀ (initObs c l₀) a b j).1
        (flowO d L c N msq V₀ (initObs c l₀) a b j).2 a b) from rfl, KnormObs_restrO]
    refine hK'.trans ?_
    -- collect the bounds
    have hKF := KnormFull_le (c := c) (ℓ₀ := ℓ₀) (a := a) (b := b) j A
      (flowO d L c N msq V₀ (initObs c l₀) a b j).2
    have hVF := VnormFull_le (c := c) (ℓ₀ := ℓ₀) (a := a) (b := b) j
      (Flow.flowN d L N msq V₀ j).1 (flowO d L c N msq V₀ (initObs c l₀) a b j).1
    set vb := Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) (Flow.flowN d L N msq V₀ j).1
    set kb := Knorm j (ellj d L ℓ₀ j) A (bulkK (flowO d L c N msq V₀ (initObs c l₀) a b j).2)
    set vo := VnormObs c ℓ₀ a b j (flowO d L c N msq V₀ (initObs c l₀) a b j).1
    set ko := KnormObs c ℓ₀ a b j A (flowO d L c N msq V₀ (initObs c l₀) a b j).2
    have e1 : vb + KnormFull c ℓ₀ a b j A (flowO d L c N msq V₀ (initObs c l₀) a b j).2 ≤
        ENNReal.ofReal (Cb * β * θ ^ j + M * lam * β * θ ^ j) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity)]
      calc _ ≤ vb + (kb + ko) := add_le_add le_rfl hKF
        _ = (vb + kb) + ko := (add_assoc _ _ _).symm
        _ ≤ _ := add_le_add hvkb hko
    have e2 : VnormFull c ℓ₀ a b j (Flow.flowN d L N msq V₀ j).1
          (flowO d L c N msq V₀ (initObs c l₀) a b j).1 +
        KnormFull c ℓ₀ a b j A (flowO d L c N msq V₀ (initObs c l₀) a b j).2 ≤
        ENNReal.ofReal (Cb * β * θ ^ j + CV * lam + M * lam * β * θ ^ j) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_add (by positivity) (by positivity)]
      calc _ ≤ (vb + vo) + (kb + ko) := add_le_add hVF hKF
        _ = (vb + kb) + vo + ko := by ring
        _ ≤ _ := add_le_add (add_le_add hvkb hvo) hko
    have hf0 : 0 ≤ (if j + 1 < N then (L : ℝ) ^ (-dplus d) else (L : ℝ) ^ m) := by
      split_ifs <;> positivity
    have hc1 : 0 ≤ C₀ * ((if j + 1 < N then (L : ℝ) ^ (-dplus d) else (L : ℝ) ^ m) + A ^ (-η)) :=
      by positivity
    calc _ ≤ ENNReal.ofReal (C₀ * ((if j + 1 < N then (L : ℝ) ^ (-dplus d) else (L : ℝ) ^ m) +
            A ^ (-η))) * ENNReal.ofReal (M * lam * β * θ ^ j) +
          ENNReal.ofReal B2 * (ENNReal.ofReal (Cb * β * θ ^ j + M * lam * β * θ ^ j) *
            ENNReal.ofReal (Cb * β * θ ^ j + CV * lam + M * lam * β * θ ^ j)) := by
          gcongr
      _ = _ := by
          conv_rhs => rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul hc1,
            ENNReal.ofReal_mul (show 0 ≤ B2 * (Cb * β * θ ^ j + M * lam * β * θ ^ j) by positivity),
            ENNReal.ofReal_mul hB20]
          ring
  -- the induction
  have hQ : ∀ j, j < N → (∀ k ≤ j, KnormObs c ℓ₀ a b k A
      (flowO d L c N msq V₀ (initObs c l₀) a b k).2 ≤ ENNReal.ofReal (e * θ ^ k)) ∧
      InKO c True a b j (flowO d L c N msq V₀ (initObs c l₀) a b j).2 ∧
      InKpt c a b j (flowO d L c N msq V₀ (initObs c l₀) a b j).2 := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨fun k hk => ?_, fun X _ => ?_, fun X _ => ?_⟩
      · obtain rfl : k = 0 := by omega
        show KnormObs c ℓ₀ a b 0 A 0 ≤ _
        rw [KnormObs_zero]; exact zero_le
      · show (0 : OE c (Lam d L N)) ∈ _; exact zero_mem _
      · show (0 : OE c (Lam d L N)) ∈ _; exact zero_mem _
    | succ j ih =>
      intro hj1
      obtain ⟨ihK, ihO, ihP⟩ := ih (by omega)
      obtain ⟨hO', hP', hK'⟩ := hstepj j (by omega) ihK ihO ihP
      refine ⟨fun k hk => ?_, hO', hP'⟩
      rcases Nat.lt_or_ge k (j + 1) with h | h
      · exact ihK k (by omega)
      · obtain rfl : k = j + 1 := by omega
        refine hK'.trans (ENNReal.ofReal_le_ofReal ?_)
        rw [if_pos hj1]
        have hr := real_step (C₀f := C₀ * ((L : ℝ) ^ (-dplus d) + A ^ (-η))) (by positivity) hB20
          hCb hCV0 le_rfl hlam0 hβ0 (hbl) (by positivity : (0 : ℝ) ≤ θ ^ j)
          (pow_le_one₀ hθ0 hθ1.le) (by linarith) hel hBD hMb
        have hE0 : 0 ≤ M * lam * β * θ ^ j := by positivity
        calc _ ≤ (C₀ * ((L : ℝ) ^ (-dplus d) + A ^ (-η)) + 9 / 16) * (M * lam * β * θ ^ j) := hr
          _ ≤ θ * (M * lam * β * θ ^ j) := by
              apply mul_le_mul_of_nonneg_right _ hE0; nlinarith
          _ = e * θ ^ (j + 1) := by rw [he, pow_succ]; ring
  -- conclusion
  intro j hj
  have hKall : ∀ k < j, KnormObs c ℓ₀ a b k A
      (flowO d L c N msq V₀ (initObs c l₀) a b k).2 ≤ ENNReal.ofReal (e * θ ^ k) :=
    fun k hk => (hQ k (by omega)).1 k le_rfl
  refine ⟨(hVo j hj hKall).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hlam0)), ?_⟩
  rw [hθpow j]
  have hCf : M ≤ max CV M' := hMM'.trans (le_max_right _ _)
  rcases Nat.lt_or_ge j N with hjN | hjN
  · refine ((hQ j hjN).1 j le_rfl).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [he]
    have : 0 ≤ lam * β * θ ^ j := by positivity
    nlinarith
  · have hjN' : j = N := by omega
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0
      show KnormObs c ℓ₀ a b 0 A 0 ≤ _
      rw [KnormObs_zero]; exact zero_le
    · obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
      obtain ⟨hKn, hOn, hPn⟩ := hQ n (by omega)
      obtain ⟨-, -, hK'⟩ := hstepj n (by omega) hKn hOn hPn
      refine hK'.trans (ENNReal.ofReal_le_ofReal ?_)
      rw [if_neg (by omega)]
      have hr := real_step (C₀f := C₀ * ((L : ℝ) ^ m + A ^ (-η))) (by positivity) hB20
        hCb hCV0 le_rfl hlam0 hβ0 (hbl) (by positivity : (0 : ℝ) ≤ θ ^ n)
        (pow_le_one₀ hθ0 hθ1.le) (by linarith) hel hBD hMb
      have hE0 : 0 ≤ M * lam * β * θ ^ n := by positivity
      have hLm : 0 ≤ (L : ℝ) ^ m := by positivity
      calc _ ≤ (C₀ * ((L : ℝ) ^ m + A ^ (-η)) + 9 / 16) * (M * lam * β * θ ^ n) := hr
        _ ≤ (C₀ * ((L : ℝ) ^ m + 1) + 1) * (M * lam * β * θ ^ n) := by
            apply mul_le_mul_of_nonneg_right _ hE0
            have : C₀ * A ^ (-η) ≤ C₀ * 1 := mul_le_mul_of_nonneg_left hAη1 hC₀
            nlinarith
        _ = M' * lam * β * θ ^ (n + 1) := by
            rw [hM', pow_succ]; field_simp
        _ ≤ max CV M' * lam * β * θ ^ (n + 1) := by
            have : 0 ≤ lam * β * θ ^ (n + 1) := by positivity
            nlinarith [le_max_right CV M']

/-! ### Along the flow of `Flow.thm_flow` -/

set_option maxHeartbeats 1000000 in
/-- **Proposition `prop:flow-obs` along the bulk flow of Theorem `thm:flow`**: with the initial
bulk coupling constants `V_0^c(m², b₀)` of `Flow.thm_flow` (whose flow satisfies
`e:flowVK-bis-1` by `cor:flow-finvol`), for `|b₀| ≤ |λ₀| ≤ λ̄`, `a = ctr`, `b ≠ a`, for all `j ≤ N`:
`‖V^obs_j‖_j ≤ C |λ₀|`, `‖K^obs_j‖_j ≤ C |λ₀| |b₀| L^{-κ j}`. -/
theorem flowObs_of_thm_flow (hd : 3 ≤ d) : ∃ (L₀ : ℕ) (Kℓ : ℝ), 0 ≤ Kℓ ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → Odd L →
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∀ ℓ₀ : ℝ, 0 < ℓ₀ →
    Kℓ * (L : ℝ) ^ ((d : ℝ) - 2 + 2 * pPhi d) ≤ ℓ₀ ^ 2 →
    ∃ (V₀c : ℝ → ℂ → Vcoup) (lbar Cf κ : ℝ), 0 < lbar ∧ 0 ≤ Cf ∧ 0 < κ ∧
      (∀ msq b₀, (V₀c msq b₀).b = b₀) ∧
      ∀ (c : Case) (N : ℕ) (msq : ℝ) (l₀ b₀ : ℂ) (b : Lam d L N), 0 ≤ msq →
        ‖b₀‖ ≤ ‖l₀‖ → ‖l₀‖ ≤ lbar → b ≠ ctr d L N →
          ∀ j ≤ N,
          VnormObs c ℓ₀ (ctr d L N) b j
              (flowO d L c N msq (V₀c msq b₀) (initObs c l₀) (ctr d L N) b j).1 ≤
            ENNReal.ofReal (Cf * ‖l₀‖) ∧
          KnormObs c ℓ₀ (ctr d L N) b j A
              (flowO d L c N msq (V₀c msq b₀) (initObs c l₀) (ctr d L N) b j).2 ≤
            ENNReal.ofReal (Cf * ‖l₀‖ * ‖b₀‖ * (L : ℝ) ^ (-(κ * j))) := by
  obtain ⟨L₁, K₁, hK₁, hF⟩ := Flow.thm_flow hd
  obtain ⟨L₂, K₂, hK₂, hO⟩ := flowObs hd
  refine ⟨max L₁ L₂, max K₁ K₂, le_trans hK₁ (le_max_left _ _), ?_⟩
  intro L _ hL hLodd
  obtain ⟨A₁, hA₁, hF'⟩ := hF L (le_trans (le_max_left _ _) hL)
  obtain ⟨A₂, hA₂, hO'⟩ := hO L (le_trans (le_max_right _ _) hL) hLodd
  refine ⟨max A₁ A₂, le_trans hA₁ (le_max_left _ _), ?_⟩
  intro A hA ℓ₀ hℓ₀ hKℓ
  have hpos : (0 : ℝ) ≤ (L : ℝ) ^ ((d : ℝ) - 2 + 2 * pPhi d) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  obtain ⟨bbar, C, κ, V₀c, hbbar, hC, hκ, hb, -, -, -, -, -, h6, -, -⟩ :=
    hF' A (le_trans (le_max_left _ _) hA) ℓ₀ hℓ₀
      ((mul_le_mul_of_nonneg_right (le_max_left _ _) hpos).trans hKℓ)
  obtain ⟨lbar, Cf, κ', hlbar, hCf, hκ', hmain⟩ :=
    hO' A (le_trans (le_max_right _ _) hA) ℓ₀ hℓ₀
      ((mul_le_mul_of_nonneg_right (le_max_right _ _) hpos).trans hKℓ) κ (C * (1 + bbar)) hκ
      (by positivity)
  refine ⟨V₀c, min lbar bbar, Cf, κ', lt_min hlbar hbbar, hCf, hκ', hb, ?_⟩
  intro c N msq l₀ b₀ b hmsq hbl hll hne
  have hb₀ : ‖b₀‖ ≤ bbar := hbl.trans (hll.trans (min_le_right _ _))
  refine hmain c N msq (V₀c msq b₀) l₀ b₀ b hmsq ?_ hbl (hll.trans (min_le_left _ _)) hne
  intro j hj
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hℓ := ellj_pos (d := d) hL0 hℓ₀ j
  obtain ⟨hV, hK⟩ := h6 msq hmsq b₀ hb₀ N j hj
  have hθ : 0 ≤ (L : ℝ) ^ (-(κ * j)) := by positivity
  have hV' := (ENNReal.le_ofReal_iff_toReal_le (Vnorm_ne_top hℓ _) (by positivity)).2 hV
  have hK' := (ENNReal.le_ofReal_iff_toReal_le (Knorm_ne_top hℓ _) (by positivity)).2 hK
  refine (add_le_add hV' hK').trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have : ‖b₀‖ ^ 2 ≤ bbar * ‖b₀‖ := by rw [sq]; exact mul_le_mul_of_nonneg_right hb₀ (norm_nonneg _)
  have h0 : 0 ≤ C * (L : ℝ) ^ (-(κ * j)) := by positivity
  nlinarith

end

end Obs
