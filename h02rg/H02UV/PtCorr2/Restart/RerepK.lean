import PtCorr2.Restart.RerepState
import PtCorr2.Restart.HistLink

/-!
# The difference activity in the `A^{|X|}`-weighted form of `KbHF` (B3, T6 input)

For the difference datum `δ = rrSt o − o'` at scale `j` (Loc point `a'`), the weighted size
`A^{(|𝓑(Y)|−4)_+}‖δ.K(Y)‖_{T_j(ℓ), w_A}` (the form of `KbHF`/`MasterCore.restartD`) is bounded per
connected polymer by the sizes of the two activities plus the relocation corrections:

* `rr_KextO_e`: the bulk part of `(K♭ + K^o)^Z` is `K♭^Z = ∏_{W ∈ Comp Z} K♭(W)`;
* `rr_kext_wt`: the large-set regulator `A^{|𝓑(W)|}‖K♭(W)‖ ≤ 1` (connected `W`) gives
  `A^{|𝓑(Z)|}‖K♭^Z‖ ≤ 1` for polymers `Z` (`prod_comp_pow`);
* **`rr_delta_K_wt`**: with `A ≥ 1`, `A^{(|𝓑(Y)|−4)_+}‖K^o(Y)‖ ≤ k₁`,
  `A^{(|𝓑(Y)|−4)_+}‖K^{o'}(Y)‖ ≤ k₂`, the block factors `‖I'(B)_∅‖ ≤ ι` (`B ⊆ Y`), the regulator
  above, and `∑_{B ⊆ Y}|β_B| ≤ β̄`:
  `A^{(|𝓑(Y)|−4)_+}‖δ.K(Y)‖_{w_A} ≤ k₁ + k₂ + β̄·(4|a−a'|_∞ℓ²/L^j)·ι·A`
  (`|𝓑(Y)| = |𝓑(Y∖B)| + 1`; the correction of the block `B` is weighted by `A·A^{|𝓑(Y∖B)|}`);
* **`rr_delta_KbHF`**: the same as the restarted-history predicate `KbHF R P' m δ t m` at `m`
  (`obsHistFrom_self`).

Only blocks `B` with `a ∈ B^□` contribute (`β_B = 0` otherwise, `rr_beta_zero`), so the corrections
live on polymers containing the `j`-block of `a` (with `rs_K_a_zero_of_block`, also `K^o`, `K^{o'}`).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

variable {L N : ℕ} [NeZero L]

theorem rr_KextO_e {j : ℕ} (K : Act 2 L N) {o : ObsSt .two L N} (ho : o.IsObs)
    (Z : Finset (Lam 2 L N)) :
    ((KextO j (embF K + o.K) Z : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).e =
      ((Kext j K Z : Step.EvR (Lam 2 L N)) : Alg 2 L N) := by
  rw [← coe_bulk, bulk_KextO]
  congr 2
  funext W
  simp [ho.K W, embF]

/-- **The large-set regulator for the bulk product.** -/
theorem rr_kext_wt {j : ℕ} {ℓ A : ℝ} (hℓ : 0 < ℓ) (hA : 0 ≤ A) (K : Act 2 L N)
    (hKb : ∀ W, IsConn j W → ENNReal.ofReal (A ^ nb j W) *
      Tj 2 (L : ℝ) j ℓ ((K W : Step.EvR (Lam 2 L N)) : Alg 2 L N) ≤ 1)
    {Z : Finset (Lam 2 L N)} (hZ : IsPolymer j Z) :
    ENNReal.ofReal (A ^ nb j Z) * Tj 2 (L : ℝ) j ℓ ((Kext j K Z : Step.EvR (Lam 2 L N)) :
      Alg 2 L N) ≤ 1 := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hh : (0 : ℝ) < (L : ℝ) ^ j := by positivity
  rw [← prod_comp_pow hZ A, ENNReal.ofReal_prod_of_nonneg (fun W _ => by positivity)]
  calc (∏ W ∈ Comp j Z, ENNReal.ofReal (A ^ nb j W)) *
        Tj 2 (L : ℝ) j ℓ ((Kext j K Z : Step.EvR (Lam 2 L N)) : Alg 2 L N)
      ≤ (∏ W ∈ Comp j Z, ENNReal.ofReal (A ^ nb j W)) *
        ∏ W ∈ Comp j Z, Tj 2 (L : ℝ) j ℓ ((K W : Step.EvR (Lam 2 L N)) : Alg 2 L N) := by
        gcongr
        exact tNorm_prod_le hh hℓ _ _
    _ = ∏ W ∈ Comp j Z, ENNReal.ofReal (A ^ nb j W) *
        Tj 2 (L : ℝ) j ℓ ((K W : Step.EvR (Lam 2 L N)) : Alg 2 L N) := (prod_mul_distrib).symm
    _ ≤ 1 := prod_le_one' fun W hW => hKb W (isConn_of_mem_comp hZ hW)

theorem rr_oTo_wA {j : ℕ} {ℓ : ℝ} (F : OE .two (Lam 2 L N)) :
    oTo Obs2.wA j ℓ F = Tj 2 (L : ℝ) j ℓ (F : SA .two (Lam 2 L N)).a := by
  rw [oTo_eq_comp wA_ab]; simp [Obs2.wA]

theorem rr_pow_nb_le {A : ℝ} (hA : 1 ≤ A) {j : ℕ} {Y Z : Finset (Lam 2 L N)}
    (h : nb j Y ≤ nb j Z + 1) : A ^ (nb j Y - 2 ^ 2) ≤ A * A ^ nb j Z :=
  calc A ^ (nb j Y - 2 ^ 2) ≤ A ^ (nb j Z + 1) := pow_le_pow_right₀ hA (by omega)
    _ = A * A ^ nb j Z := by rw [pow_succ, mul_comm]

variable (R : RGPar 2 L N) (j : ℕ) (st : RawSt 2 L N) (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N)
  (a a' : Lam 2 L N) (β : (Fin 2 → ℕ) → ℂ)

/-- **The weighted size of the difference activity** (per connected polymer). -/
theorem rr_delta_K_wt {ℓ A : ℝ} (hℓ : 0 < ℓ) (hA : 1 ≤ A) {o o' : ObsSt .two L N}
    (ho : o.IsObs) {Y : Finset (Lam 2 L N)} (hY : IsConn j Y) {k₁ k₂ ι βs : ℝ}
    (hk₁ : 0 ≤ k₁) (hk₂ : 0 ≤ k₂) (hι : 0 ≤ ι)
    (hK₁ : ENNReal.ofReal (A ^ (nb j Y - 2 ^ 2)) * oTo Obs2.wA j ℓ (o.K Y) ≤ ENNReal.ofReal k₁)
    (hK₂ : ENNReal.ofReal (A ^ (nb j Y - 2 ^ 2)) * oTo Obs2.wA j ℓ (o'.K Y) ≤ ENNReal.ofReal k₂)
    (hI : ∀ b ∈ blocks j Y, Tj 2 (L : ℝ) j ℓ ((IbO (fun b' => emb (stVf R j st g μ b' +
      stDelta R j st b') + (o.V b' - rrD a a' β b')) (fullW st D o) b : OE .two (Lam 2 L N)) :
        SA .two (Lam 2 L N)).e ≤ ENNReal.ofReal ι)
    (hKb : ∀ W, IsConn j W → ENNReal.ofReal (A ^ nb j W) *
      Tj 2 (L : ℝ) j ℓ ((K W : Step.EvR (Lam 2 L N)) : Alg 2 L N) ≤ 1)
    (hβ : ∑ b ∈ blocks j Y, ‖β b‖ ≤ βs) :
    ENNReal.ofReal (A ^ (nb j Y - 2 ^ 2)) *
        oTo Obs2.wA j ℓ ((subSt (rrSt R j st g μ D K a a' β o) o').K Y) ≤
      ENNReal.ofReal (k₁ + k₂ +
        βs * (2 * ((2 : ℕ) : ℝ) * supNorm (a - a') * ℓ ^ 2 / (L : ℝ) ^ j) * ι * A) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hA0 : (0 : ℝ) ≤ A := by linarith
  set c := 2 * ((2 : ℕ) : ℝ) * supNorm (a - a') * ℓ ^ 2 / (L : ℝ) ^ j with hc
  have hc0 : 0 ≤ c := by
    rw [hc]; positivity
  set w := ENNReal.ofReal (A ^ (nb j Y - 2 ^ 2)) with hw
  rw [rr_oTo_wA] at hK₁ hK₂ ⊢
  -- the correction of one block
  have hcorr : ∀ b ∈ blocks j Y, w * (ENNReal.ofReal (‖β b‖ * c) *
      (Tj 2 (L : ℝ) j ℓ ((IbO (fun b' => emb (stVf R j st g μ b' + stDelta R j st b') +
        (o.V b' - rrD a a' β b')) (fullW st D o) b : OE .two (Lam 2 L N)) :
          SA .two (Lam 2 L N)).e *
        Tj 2 (L : ℝ) j ℓ ((KextO j (embF K + o.K) (Y \ blockSet j b) :
          OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).e)) ≤
      ENNReal.ofReal (‖β b‖ * c * ι * A) := by
    intro b hb
    have hBY : blockSet (L := L) (N := N) j b ⊆ Y := blockSet_subset hY.1 hb
    have hZ : IsPolymer j (Y \ blockSet j b) := IsPolymer.sdiff hY.1 (isPolymer_blockSet j b)
    have hnb := nb_sdiff_add hY.1 (isPolymer_blockSet (L := L) (N := N) j b) hBY
    have hnb1 := nb_blockSet_le (L := L) (N := N) j b
    have hpow := rr_pow_nb_le hA (j := j) (Y := Y) (Z := Y \ blockSet j b) (by omega)
    have hext := rr_kext_wt hℓ hA0 K hKb hZ
    rw [rr_KextO_e K ho]
    calc w * (ENNReal.ofReal (‖β b‖ * c) * (Tj 2 (L : ℝ) j ℓ ((IbO _ (fullW st D o) b :
            OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).e *
          Tj 2 (L : ℝ) j ℓ ((Kext j K (Y \ blockSet j b) : Step.EvR (Lam 2 L N)) : Alg 2 L N)))
        ≤ ENNReal.ofReal (A * A ^ nb j (Y \ blockSet j b)) * (ENNReal.ofReal (‖β b‖ * c) *
          (ENNReal.ofReal ι * Tj 2 (L : ℝ) j ℓ ((Kext j K (Y \ blockSet j b) :
            Step.EvR (Lam 2 L N)) : Alg 2 L N))) := by
          gcongr
          · exact ENNReal.ofReal_le_ofReal hpow
          · exact hI b hb
      _ = ENNReal.ofReal (‖β b‖ * c * ι * A) * (ENNReal.ofReal (A ^ nb j (Y \ blockSet j b)) *
          Tj 2 (L : ℝ) j ℓ ((Kext j K (Y \ blockSet j b) : Step.EvR (Lam 2 L N)) :
            Alg 2 L N)) := by
          rw [ENNReal.ofReal_mul hA0, ENNReal.ofReal_mul (p := ‖β b‖ * c * ι) (by positivity),
            ENNReal.ofReal_mul (p := ‖β b‖ * c) (by positivity)]
          ring
      _ ≤ ENNReal.ofReal (‖β b‖ * c * ι * A) * 1 := by gcongr
      _ = _ := mul_one _
  calc w * Tj 2 (L : ℝ) j ℓ (((subSt (rrSt R j st g μ D K a a' β o) o').K Y :
        OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a
      ≤ w * (Tj 2 (L : ℝ) j ℓ ((o.K Y : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a +
          ∑ b ∈ blocks j Y, ENNReal.ofReal (‖β b‖ * c) *
            (Tj 2 (L : ℝ) j ℓ ((IbO (fun b' => emb (stVf R j st g μ b' + stDelta R j st b') +
              (o.V b' - rrD a a' β b')) (fullW st D o) b : OE .two (Lam 2 L N)) :
                SA .two (Lam 2 L N)).e *
              Tj 2 (L : ℝ) j ℓ ((KextO j (embF K + o.K) (Y \ blockSet j b) :
                OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).e) +
          Tj 2 (L : ℝ) j ℓ ((o'.K Y : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a) :=
        mul_le_mul_right (rr_delta_K_norm R j st g μ D K a a' β hℓ o o' Y) _
    _ = w * Tj 2 (L : ℝ) j ℓ ((o.K Y : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a +
          ∑ b ∈ blocks j Y, w * (ENNReal.ofReal (‖β b‖ * c) *
            (Tj 2 (L : ℝ) j ℓ ((IbO (fun b' => emb (stVf R j st g μ b' + stDelta R j st b') +
              (o.V b' - rrD a a' β b')) (fullW st D o) b : OE .two (Lam 2 L N)) :
                SA .two (Lam 2 L N)).e *
              Tj 2 (L : ℝ) j ℓ ((KextO j (embF K + o.K) (Y \ blockSet j b) :
                OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).e)) +
          w * Tj 2 (L : ℝ) j ℓ ((o'.K Y : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a := by
        rw [mul_add, mul_add, mul_sum]
    _ ≤ ENNReal.ofReal k₁ + ∑ b ∈ blocks j Y, ENNReal.ofReal (‖β b‖ * c * ι * A) +
          ENNReal.ofReal k₂ := by
        gcongr with b hb
        exact hcorr b hb
    _ = ENNReal.ofReal (k₁ + k₂ + (∑ b ∈ blocks j Y, ‖β b‖) * c * ι * A) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun b _ => by positivity),
          ← ENNReal.ofReal_add hk₁ (sum_nonneg fun b _ => by positivity),
          ← ENNReal.ofReal_add (by positivity) hk₂, sum_mul, sum_mul, sum_mul]
        congr 1; ring
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have : (∑ b ∈ blocks j Y, ‖β b‖) * c * ι * A ≤ βs * c * ι * A := by
          gcongr
        linarith

/-- **`KbHF` of the difference datum at the restart scale.** -/
theorem rr_delta_KbHF (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P' : ObsPts 2 L N)
    (m : ℕ) (t : Flow2.Hist.Seq (Xs R)) (a a' : Lam 2 L N) (β : (Fin 2 → ℕ) → ℂ)
    {o o' : ObsSt .two L N} (ho : o.IsObs) {k₁ k₂ ι βs : ℝ}
    (hk₁ : 0 ≤ k₁) (hk₂ : 0 ≤ k₂) (hι : 0 ≤ ι) (hA : 1 ≤ R.A)
    (hK₁ : ∀ Y, IsConn m Y → ENNReal.ofReal (R.A ^ (nb m Y - 2 ^ 2)) *
      oTo Obs2.wA m (histS R m t) (o.K Y) ≤ ENNReal.ofReal k₁)
    (hK₂ : ∀ Y, IsConn m Y → ENNReal.ofReal (R.A ^ (nb m Y - 2 ^ 2)) *
      oTo Obs2.wA m (histS R m t) (o'.K Y) ≤ ENNReal.ofReal k₂)
    (hI : ∀ b, Tj 2 (L : ℝ) m (histS R m t) ((IbO (fun b' => emb (stVf R m (rawHist R m t)
      (t m).1 (t m).2.1 b' + stDelta R m (rawHist R m t) b') + (o.V b' - rrD a a' β b'))
      (fullW (rawHist R m t) (rawD R (rawHist R m t).u (t m).2.2) o) b :
        OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).e ≤ ENNReal.ofReal ι)
    (hKb : ∀ W, IsConn m W → ENNReal.ofReal (R.A ^ nb m W) *
      Tj 2 (L : ℝ) m (histS R m t) ((rawK R (rawHist R m t).u (t m).2.2 W :
        Step.EvR (Lam 2 L N)) : Alg 2 L N) ≤ 1)
    (hβ : ∑ b ∈ blockIdx (L := L) (N := N) m, ‖β b‖ ≤ βs) (hs : 0 < histS R m t) :
    KbHF R P' m (subSt (rrStH R m t a a' β o) o') t m
      (k₁ + k₂ + βs * (2 * ((2 : ℕ) : ℝ) * supNorm (a - a') * histS R m t ^ 2 / (L : ℝ) ^ m) *
        ι * R.A) := by
  intro Y hY
  rw [obsHistFrom_self]
  exact rr_delta_K_wt R m _ _ _ _ _ a a' β hs hA ho hY hk₁ hk₂ hι (hK₁ Y hY) (hK₂ Y hY)
    (fun b _ => hI b) hKb ((sum_le_sum_of_subset_of_nonneg (blocks_subset_blockIdx Y)
      (fun _ _ _ => norm_nonneg _)).trans hβ)

end

end PtCorr2
