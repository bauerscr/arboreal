import Spin2.Restart.RestartPairSeed
import Spin2.Pair.PairInitW
import Spin2.Pair.PairDefAB2
import PtCorr2.Restart.RestartPairChain1

/-!
# T5, item (5): the seed of the reduced state at the coalescence scale `j ≤ N_h` for a general state

The analogue of `rp_topSeed_gen` (`Spin2/Restart/RestartPairSeed`, scale `N_h + 1`) and of the block part of
`pairInit_trajW` (`Spin2/Pair/PairInitW`, reference history) at a scale `j ≤ N_h`, for an **arbitrary**
observable state `o` and any weights `M_a, M_b > 0` (**`rpc_seed_gen`**): from the sizes of `o` in
`wM(M_a, M_b)` at scale `j`

* `‖V^{obs}(B)‖ ≤ v_T`, `‖𝒲^{obs}(B)‖ ≤ w_T` (blocks),
* `A^{(|𝓑(X)|-4)_+}‖K^{obs}(X)‖_{wM1} ≤ k_{xT}`, `A^{(|𝓑(X)|-4)_+}w_{ab}‖K^{obs}(X)_{ab}‖ ≤ k₂`,

the bulk inputs at `j` (`inV_fullW_bulk_le`: `‖V♭ + Δ‖ ≤ 3/2`, `‖W^{lin} + D‖ ≤ 1`; the bulk
activity `‖K_j‖ ≤ c_x ǧ_j³` from the domain), and `A⁴(c_xǧ_j³ + k_{xT} + k₂) ≤ 1`:

  `A^{(|𝓑(X)|-4)_+}‖K'_j(X)‖_{wM(M_a,M_b)} ≤ (2ιA)^{|𝓑(D)|}`, `ι = e^{3/2+v_T}(2 + w_T)`

for the reduced state `rpcRedSt … j … o D`; with `D = dxStd x` at `j = j_x` the exponent is
`≤ (L + 18)²` (**`rpc_seed_dxStd`**). With `M_a` the `a`-side size of `o`, the seed's `ab` part is
`O(M_aM_b)`: linear in the `a`-side.
-/

set_option linter.unusedSectionVars false

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs FRD Flow2 Flow2.Hist Obs2 ENNReal Step2.D2

variable {L N : ℕ} [NeZero L]

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
variable {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

set_option maxHeartbeats 4000000 in
/-- **The seed of the reduced state at a scale `j ≤ N_h` for a general state `o`.** -/
theorem rpc_seed_gen (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1) (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    (hρ0 : 0 ≤ R.ρ) (hρ8 : R.ρ ≤ 1 / 8) (hA1 : 1 ≤ R.A) (t : Hist.Seq (Xs R)) {j : ℕ}
    (hj : j ≤ Nh) (ht : InDh Λ β δ κ cg cm cT ε j t) (hVc : ValidCore R j)
    (hmj : |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1) (hε1 : cR R Λ cm C₂ * ε ≤ 1)
    (P : ObsPts 2 L N) (o : ObsSt .two L N) (ho : o.IsObs) (D : Finset (Lam 2 L N))
    {Ma Mb vT wT kxT k2 : ℝ} (hvT : 0 ≤ vT) (hwT : 0 ≤ wT) (hkxT : 0 ≤ kxT) (hk2 : 0 ≤ k2)
    (hVt : ∀ q ∈ blockIdx (L := L) (N := N) j,
      oTo (wM Ma Mb) j (histS R j t) (o.V q) ≤ ENNReal.ofReal vT)
    (hWt : ∀ q ∈ blockIdx (L := L) (N := N) j,
      oTo (wM Ma Mb) j (histS R j t) (o.W q) ≤ ENNReal.ofReal wT)
    (hKt : ∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
      oTo (wM1 Ma Mb) j (histS R j t) (o.K X) ≤ ENNReal.ofReal kxT)
    (hK2 : ∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
      ((wM Ma Mb).ab * Tj 2 (L : ℝ) j (histS R j t) (o.K X : SA .two (Lam 2 L N)).ab) ≤
        ENNReal.ofReal k2)
    (hsmT : R.A ^ 4 * (cx κ cT * (t j).1 ^ 3 + kxT + k2) ≤ 1) :
    ∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
      oTo (wM Ma Mb) j (histS R j t) ((rpcRedSt R P j t o D).K X) ≤
      ENNReal.ofReal ((2 * rpIota vT wT * R.A) ^ nb j D) := by
  have hs' : 0 < histS R j t := histS_pos' R hρ0 hρ8 t j
  obtain ⟨hbV, hbW⟩ := inV_fullW_bulk_le R hSB hV hm hβ hδ1 H hρ0 t j hj ht hVc hmj hε1
  -- the block bound
  set ι := rpIota vT wT with hιd
  have hι : 1 ≤ ι := one_le_rpIota hvT hwT
  have hI : ∀ q ∈ blocks j D, oTj 2 L (wM Ma Mb) j (histS R j t)
      (inI R j (rawHist R j t) (t j).1 (t j).2.1 (rawD R (rawHist R j t).u (t j).2.2) o q :
        SA .two (Lam 2 L N)) ≤ ENNReal.ofReal ι := by
    intro q hq
    have hqI : q ∈ blockIdx (L := L) (N := N) j := mem_blockIdx_of_mem_blocks hq
    refine (oTj_inI_le R j _ _ _ _ _ ho (wM Ma Mb) (wM_sub Ma Mb) hs' q
      (v := 3 / 2 + vT) (f := 1 + wT) (by linarith) (by linarith) ?_ ?_).trans
        (le_of_eq (by rw [hιd]; unfold rpIota; ring_nf))
    · refine (oTj_emb_add_le _ _ _ _ _ (ho.V q)).trans ?_
      refine (add_le_add (hbV q hqI) (hVt q hqI)).trans (le_of_eq ?_)
      rw [← ENNReal.ofReal_add (by norm_num) hvT]
    · refine (oTj_emb_add_le _ _ _ _ _ (ho.W q)).trans ?_
      refine (add_le_add (hbW q hqI) (hWt q hqI)).trans (le_of_eq ?_)
      rw [← ENNReal.ofReal_add zero_le_one hwT]
  -- the bulk activity
  have HI := rawInv_hist R hρ0 j (fun i hi => hV i (by omega)) t
  have hZ : (rawHist R j t).Z ≠ 0 := HI.Z_ne_zero (by linarith)
  have hKn := Knorm_rawK R HI.hu hZ (t j).2.2
  obtain ⟨hgj, -, -, hxj⟩ := ht.1 j le_rfl
  have hcx := H.hcx
  set kb : ℝ := cx κ cT * (t j).1 ^ 3 with hkbd
  have hkb0 : 0 ≤ kb := mul_nonneg hcx (pow_nonneg hgj.le 3)
  have hKb : ∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
      Tj 2 (L : ℝ) j (histS R j t) (rawK R (rawHist R j t).u (t j).2.2 X : Alg 2 L N) ≤
        ENNReal.ofReal kb := by
    intro X hX
    have h1 : ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
        Tj 2 (L : ℝ) j (histS R j t) (rawK R (rawHist R j t).u (t j).2.2 X : Alg 2 L N) ≤
        Knorm j (fscale (rawHist R j t).Z * R.ℓ) R.A (rawK R (rawHist R j t).u (t j).2.2) :=
      le_iSup₂ (f := fun X (_ : X ∈ connSets (L := L) (N := N) j) =>
        ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
          Tj 2 (L : ℝ) j (fscale (rawHist R j t).Z * R.ℓ)
            (rawK R (rawHist R j t).u (t j).2.2 X : Alg 2 L N)) X
        (by simp [connSets]; exact hX)
    refine (h1.trans (le_of_eq hKn)).trans (ENNReal.ofReal_le_ofReal ?_)
    exact (norm_snd_le _).trans hxj
  have hK : ∀ X, IsConn j X → ENNReal.ofReal (R.A ^ nb j X) *
      oTj 2 L (wM Ma Mb) j (histS R j t)
        (inK (rawK R (rawHist R j t).u (t j).2.2) o X : SA .two (Lam 2 L N)) ≤ 1 := by
    intro X hX
    rw [oTj_inK_eq _ _ ho]
    have hA0 : 0 ≤ R.A := by linarith
    calc ENNReal.ofReal (R.A ^ nb j X) *
          (Tj 2 (L : ℝ) j (histS R j t) (rawK R (rawHist R j t).u (t j).2.2 X : Alg 2 L N) +
          oTo (wM1 Ma Mb) j (histS R j t) (o.K X) +
          (wM Ma Mb).ab * Tj 2 (L : ℝ) j (histS R j t) (o.K X : SA .two (Lam 2 L N)).ab)
        ≤ ENNReal.ofReal (R.A ^ 4) * (ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
          (Tj 2 (L : ℝ) j (histS R j t) (rawK R (rawHist R j t).u (t j).2.2 X : Alg 2 L N) +
          oTo (wM1 Ma Mb) j (histS R j t) (o.K X) +
          (wM Ma Mb).ab * Tj 2 (L : ℝ) j (histS R j t) (o.K X : SA .two (Lam 2 L N)).ab)) := by
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
  exact kRed_poly_le (z0 := P.a) (D := D) (wM_sub Ma Mb) hs' hA1 hι
    (inI R j (rawHist R j t) (t j).1 (t j).2.1 (rawD R (rawHist R j t).u (t j).2.2) o)
    (inK (rawK R (rawHist R j t).u (t j).2.2) o) hI hK X

/-- **The seed at the coalescence scale with the standard covering polymer**: exponent
`|𝓑(dxStd x)| ≤ (L + 18)²`. -/
theorem rpc_seed_dxStd (hL2 : 2 ≤ L) (x : Lam 2 L N) (hjN : Obs.coal L (0 : Lam 2 L N) x ≤ N)
    {vT wT : ℝ} (hvT : 0 ≤ vT) (hwT : 0 ≤ wT) (hA1 : 1 ≤ R.A) :
    (2 * rpIota vT wT * R.A) ^ nb (Obs.coal L (0 : Lam 2 L N) x) (dxStd (L := L) (N := N) x) ≤
      (2 * rpIota vT wT * R.A) ^ ((L + 18) ^ 2) := by
  have hι := one_le_rpIota hvT hwT
  exact pow_le_pow_right₀ (by nlinarith) (nb_dxStd_le hL2 x hjN)

end Traj

end

end Spin2
