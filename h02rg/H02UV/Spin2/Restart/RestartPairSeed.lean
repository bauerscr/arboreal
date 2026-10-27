import Spin2.Pair.PairTopSeed1

/-!
# T5 (pair/top restart): the seed of the reduced state at `N - 1` for a general state

The block part of `topSeed_traj` (`Spin2/Pair/PairTopSeed1`) for an **arbitrary** observable state `o`
at scale `N_h + 1` and any weights `M_a, M_b > 0`: from the sizes of `o` in `wM(M_a, M_b)`

* `‖V^{obs}(B)‖ ≤ v_T`, `‖𝒲^{obs}(B)‖ ≤ w_T`,
* `A^{(|𝓑(X)|-4)_+}‖K^{obs}(X)‖_{wM1} ≤ k_{xT}` (one-point parts),
  `A^{(|𝓑(X)|-4)_+}w_{ab}‖K^{obs}(X)_{ab}‖ ≤ k_2` (pair part),

and the bulk inputs of the last step (`GlueOut`, smallness `A⁴(C_fǧ³ + k_{xT} + k₂) ≤ 1`):

  `A^{(|𝓑(X)|-4)_+}‖K'_{N_h+1}(X)‖_{wM(M_a,M_b)} ≤ (2ι A)^{L²}`, `ι = e^{3/2+v_T}(2 + w_T)`

for the reduced state `redSt … o D` (**`rp_topSeed_gen`**). With `M_a` the `a`-side size of `o`,
the seed is `O(1)` in `wM(M_a, M_b)`, i.e. its `ab` part is `O(M_aM_b)`: linear in the `a`-side.
-/

set_option linter.unusedSectionVars false

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs FRD Flow2 Flow2.Hist Obs2 ENNReal Step2.D2

variable {L N : ℕ} [NeZero L]

/-- The block constant of the general seed. -/
def rpIota (vT wT : ℝ) : ℝ := Real.exp (3 / 2 + vT) * (2 + wT)

theorem one_le_rpIota {vT wT : ℝ} (hvT : 0 ≤ vT) (hwT : 0 ≤ wT) : 1 ≤ rpIota vT wT := by
  unfold rpIota
  have h1 : 1 ≤ Real.exp (3 / 2 + vT) := Real.one_le_exp (by linarith)
  have h2 : (1 : ℝ) ≤ 2 + wT := by linarith
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ _ := mul_le_mul h1 h2 zero_le_one (by linarith)

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

set_option maxHeartbeats 4000000 in
/-- **The seed of the reduced state at `N_h + 1` for a general state `o`.** -/
theorem rp_topSeed_gen {Nh : ℕ} (hNN : Nh + 2 = N) (hV : ∀ j < Nh, ValidAt R j)
    (hVL : ValidAtL R Nh) (hVN : LastN.ValidLast R (Nh + 1))
    (hmN : |R.msq| * ((L : ℝ) ^ (Nh + 1)) ^ 2 ≤ 1)
    (hL : 2 ^ (2 + 3) + 8 * 2 < L) (hρ0 : 0 ≤ R.ρ) (hρ8 : R.ρ ≤ 1 / 8) (hA1 : 1 ≤ R.A)
    (t : Hist.Seq (Xs R)) {Cf : ℝ} (hCf : 0 ≤ Cf) (hG : GlueOut R Nh Cf t)
    (hg0 : 0 ≤ (t Nh).1)
    (hs1 : 2 * (Cf * (t Nh).1) ≤ R.ρ) (hs2 : 8 * cM * R.ℓ ^ 2 * (Cf * (t Nh).1) ≤ 1 / 2)
    (hvb : cM * R.ℓ ^ 2 * (4 * (Cf * (t Nh).1)) + 8 * R.ℓ ^ 4 * (Cf * (t Nh).1) ≤ 1)
    (hwb : 2 * (Cf * (t Nh).1 ^ 2) ≤ 1)
    (P : ObsPts 2 L N) (o : ObsSt .two L N) (ho : o.IsObs) (D : Finset (Lam 2 L N))
    {Ma Mb vT wT kxT k2 : ℝ} (hvT : 0 ≤ vT) (hwT : 0 ≤ wT)
    (hkxT : 0 ≤ kxT) (hk2 : 0 ≤ k2)
    (hVt : ∀ q ∈ blockIdx (L := L) (N := N) (Nh + 1),
      oTo (wM Ma Mb) (Nh + 1) (histS R (Nh + 1) t) (o.V q) ≤ ENNReal.ofReal vT)
    (hWt : ∀ q ∈ blockIdx (L := L) (N := N) (Nh + 1),
      oTo (wM Ma Mb) (Nh + 1) (histS R (Nh + 1) t) (o.W q) ≤ ENNReal.ofReal wT)
    (hKt : ∀ X, IsConn (Nh + 1) X → ENNReal.ofReal (R.A ^ (nb (Nh + 1) X - 2 ^ 2)) *
      oTo (wM1 Ma Mb) (Nh + 1) (histS R (Nh + 1) t) (o.K X) ≤ ENNReal.ofReal kxT)
    (hK2 : ∀ X, IsConn (Nh + 1) X → ENNReal.ofReal (R.A ^ (nb (Nh + 1) X - 2 ^ 2)) *
      ((wM Ma Mb).ab * Tj 2 (L : ℝ) (Nh + 1) (histS R (Nh + 1) t)
        (o.K X : SA .two (Lam 2 L N)).ab) ≤ ENNReal.ofReal k2)
    (hsmT : R.A ^ 4 * (Cf * (t Nh).1 ^ 3 + kxT + k2) ≤ 1) :
    ∀ X, IsConn (Nh + 1) X → ENNReal.ofReal (R.A ^ (nb (Nh + 1) X - 2 ^ 2)) *
      oTo (wM Ma Mb) (Nh + 1) (histS R (Nh + 1) t)
        ((redSt R P (Nh + 1) (histOut R Nh t).st (histOut R Nh t).g.re (histOut R Nh t).nu.re
          (histOut R Nh t).D (histOut R Nh t).K o D).K X) ≤
      ENNReal.ofReal ((2 * rpIota vT wT * R.A) ^ (L ^ 2)) := by
  have hA : 0 < R.A := Fact.out
  have hs' : 0 < histS R (Nh + 1) t := histS_pos' R hρ0 hρ8 t (Nh + 1)
  -- the bulk inputs of the last step
  set st := (histOut R Nh t).st with hst
  have Hst : RawInv R (Nh + 1) st := rawInv_histU R hV hVL t (Nh + 1) le_rfl
  have hDm : (histOut R Nh t).D ∈ BSub (L := L) (N := N) (Nh + 1) :=
    (RawInv.stepL hVL (rawInv_hist R hρ0 Nh hV t) (t Nh).1 (t Nh).2.1 (rawD_mem R _ _)
      (rawK_mem R _ _)).2.1
  have hKm : (histOut R Nh t).K ∈ ASub (L := L) (N := N) (Nh + 1) :=
    (RawInv.stepL hVL (rawInv_hist R hρ0 Nh hV t) (t Nh).1 (t Nh).2.1 (rawD_mem R _ _)
      (rawK_mem R _ _)).2.2
  obtain ⟨⟨hz, hy, hnu, hgn, hgre, hWl, hDd, hKk⟩, -⟩ := hG
  set gg := (t Nh).1 with hgg
  have hCg : 0 ≤ Cf * gg := mul_nonneg hCf hg0
  obtain ⟨hVv, hWw, -, -, -, -, -, hΔ⟩ := bulk_last_in R hVN hL Hst (histOut R Nh t).g.re
    (histOut R Nh t).nu.re hDm hKm hmN hgre (Cf * gg) hz hy hs1 hs2 hA
    (by positivity) (by positivity) hWl hDd hKk
  have hνr : |(histOut R Nh t).nu.re| ≤ Cf * gg := (Complex.abs_re_le_norm _).trans hnu
  have hgr : (histOut R Nh t).g.re ≤ Cf * gg := (Complex.re_le_norm _).trans hgn
  have hv1 : cM * R.ℓ ^ 2 * (2 * |(histOut R Nh t).nu.re| + 2 * (Cf * gg)) +
      8 * R.ℓ ^ 4 * (histOut R Nh t).g.re ≤ 1 := by
    have hM : (0 : ℝ) ≤ cM := Nat.cast_nonneg _
    have h1 : cM * R.ℓ ^ 2 * (2 * |(histOut R Nh t).nu.re| + 2 * (Cf * gg)) ≤
        cM * R.ℓ ^ 2 * (4 * (Cf * gg)) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hM (sq_nonneg _))
    have h2 : 8 * R.ℓ ^ 4 * (histOut R Nh t).g.re ≤ 8 * R.ℓ ^ 4 * (Cf * gg) :=
      mul_le_mul_of_nonneg_left hgr (by positivity)
    linarith
  -- the block bound
  set ι := rpIota vT wT with hιd
  have hι : 1 ≤ ι := one_le_rpIota hvT hwT
  have hI : ∀ q ∈ blocks (Nh + 1) D, oTj 2 L (wM Ma Mb) (Nh + 1) (histS R (Nh + 1) t)
      (inI R (Nh + 1) st (histOut R Nh t).g.re (histOut R Nh t).nu.re (histOut R Nh t).D o q :
        SA .two (Lam 2 L N)) ≤ ENNReal.ofReal ι := by
    intro q hq
    have hqI : q ∈ blockIdx (L := L) (N := N) (Nh + 1) := mem_blockIdx_of_mem_blocks hq
    refine (oTj_inI_le R (Nh + 1) _ _ _ _ _ ho (wM Ma Mb) (wM_sub Ma Mb) hs' q
      (v := 3 / 2 + vT) (f := 1 + wT) (by linarith) (by linarith) ?_ ?_).trans
        (le_of_eq (by rw [hιd]; unfold rpIota; ring_nf))
    · refine (oTj_emb_add_le _ _ _ _ _ (ho.V q)).trans ?_
      have hb1 : Tj 2 (L : ℝ) (Nh + 1) (histS R (Nh + 1) t)
          ((stVf R (Nh + 1) st (histOut R Nh t).g.re (histOut R Nh t).nu.re q +
            stDelta R (Nh + 1) st q : EvR (Lam 2 L N)) : Alg 2 L N) ≤ ENNReal.ofReal (3 / 2) := by
        rw [AddMemClass.coe_add]
        refine (tNorm_add_le _ _).trans ?_
        have h1 := (Tj_le_Fnorm (stVf R (Nh + 1) st (histOut R Nh t).g.re (histOut R Nh t).nu.re)
          hqI).trans (hVv.trans (ENNReal.ofReal_le_ofReal hv1))
        have h2 := (Tj_le_Fnorm (stDelta R (Nh + 1) st) hqI).trans
          (hΔ.trans (ENNReal.ofReal_le_ofReal hs2))
        refine (add_le_add h1 h2).trans ?_
        rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        exact ENNReal.ofReal_le_ofReal (by norm_num)
      refine (add_le_add hb1 (hVt q hqI)).trans (le_of_eq ?_)
      rw [← ENNReal.ofReal_add (by norm_num) hvT]
    · refine (oTj_emb_add_le _ _ _ _ _ (ho.W q)).trans ?_
      have hb2 : Tj 2 (L : ℝ) (Nh + 1) (histS R (Nh + 1) t)
          ((st.Wl + (histOut R Nh t).D) q : Alg 2 L N) ≤ ENNReal.ofReal 1 := by
        refine (Tj_le_Fnorm _ hqI).trans (hWw.trans (ENNReal.ofReal_le_ofReal ?_))
        linarith
      refine (add_le_add hb2 (hWt q hqI)).trans (le_of_eq ?_)
      rw [← ENNReal.ofReal_add zero_le_one hwT]
  -- the activity
  set kb := Cf * gg ^ 3 with hkbd
  have hkb0 : 0 ≤ kb := mul_nonneg hCf (pow_nonneg hg0 3)
  have hKb : ∀ X, IsConn (Nh + 1) X → ENNReal.ofReal (R.A ^ (nb (Nh + 1) X - 2 ^ 2)) *
      Tj 2 (L : ℝ) (Nh + 1) (histS R (Nh + 1) t) ((histOut R Nh t).K X : Alg 2 L N) ≤
        ENNReal.ofReal kb := by
    intro X hX
    have h1 : ENNReal.ofReal (R.A ^ (nb (Nh + 1) X - 2 ^ 2)) *
        Tj 2 (L : ℝ) (Nh + 1) (histS R (Nh + 1) t) ((histOut R Nh t).K X : Alg 2 L N) ≤
        Knorm (Nh + 1) (fscale st.Z * R.ℓ) R.A (histOut R Nh t).K :=
      le_iSup₂ (f := fun X (_ : X ∈ connSets (L := L) (N := N) (Nh + 1)) =>
        ENNReal.ofReal (R.A ^ (nb (Nh + 1) X - 2 ^ 2)) *
          Tj 2 (L : ℝ) (Nh + 1) (fscale st.Z * R.ℓ) ((histOut R Nh t).K X : Alg 2 L N)) X
        (by simp [connSets]; exact hX)
    exact h1.trans hKk
  have hK : ∀ X, IsConn (Nh + 1) X → ENNReal.ofReal (R.A ^ nb (Nh + 1) X) *
      oTj 2 L (wM Ma Mb) (Nh + 1) (histS R (Nh + 1) t)
        (inK (histOut R Nh t).K o X : SA .two (Lam 2 L N)) ≤ 1 := by
    intro X hX
    rw [oTj_inK_eq _ _ ho]
    have hA0 : 0 ≤ R.A := by linarith
    calc ENNReal.ofReal (R.A ^ nb (Nh + 1) X) *
          (Tj 2 (L : ℝ) (Nh + 1) (histS R (Nh + 1) t) ((histOut R Nh t).K X : Alg 2 L N) +
          oTo (wM1 Ma Mb) (Nh + 1) (histS R (Nh + 1) t) (o.K X) +
          (wM Ma Mb).ab * Tj 2 (L : ℝ) (Nh + 1) (histS R (Nh + 1) t)
            (o.K X : SA .two (Lam 2 L N)).ab)
        ≤ ENNReal.ofReal (R.A ^ 4) * (ENNReal.ofReal (R.A ^ (nb (Nh + 1) X - 2 ^ 2)) *
          (Tj 2 (L : ℝ) (Nh + 1) (histS R (Nh + 1) t) ((histOut R Nh t).K X : Alg 2 L N) +
          oTo (wM1 Ma Mb) (Nh + 1) (histS R (Nh + 1) t) (o.K X) +
          (wM Ma Mb).ab * Tj 2 (L : ℝ) (Nh + 1) (histS R (Nh + 1) t)
            (o.K X : SA .two (Lam 2 L N)).ab)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hA0 _)]
          exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (regA_le R.A hA1 _)) _
      _ ≤ ENNReal.ofReal (R.A ^ 4) * (ENNReal.ofReal kb + ENNReal.ofReal kxT +
          ENNReal.ofReal k2) := by
          refine mul_le_mul_right ?_ _
          rw [mul_add, mul_add]
          exact add_le_add (add_le_add (hKb X hX) (hKt X hX)) (hK2 X hX)
      _ = ENNReal.ofReal (R.A ^ 4 * (kb + kxT + k2)) := by
          rw [← ENNReal.ofReal_add hkb0 hkxT, ← ENNReal.ofReal_add (add_nonneg hkb0 hkxT) hk2,
            ← ENNReal.ofReal_mul (pow_nonneg hA0 _)]
      _ ≤ 1 := by
          rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hsmT
  -- the reduced activity
  intro X _
  have hmain := kRed_poly_le (z0 := P.a) (D := D) (wM_sub Ma Mb) hs' hA1 hι
    (inI R (Nh + 1) st (histOut R Nh t).g.re (histOut R Nh t).nu.re (histOut R Nh t).D o)
    (inK (histOut R Nh t).K o) hI hK X
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  have hnb : nb (Nh + 1) D ≤ L ^ 2 := by
    have h1 : (blocks (Nh + 1) D).card ≤ (blockIdx (L := L) (N := N) (Nh + 1)).card :=
      card_le_card (blocks_subset_blockIdx _)
    exact h1.trans (LastN.card_blockIdx_last (d := 2) (L := L) (N := N) (by omega))
  exact pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le (by linarith) hA1) hnb

end Traj

end

end Spin2
