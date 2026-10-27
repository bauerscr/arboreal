import PtCorr2.Pair.PairInitAB2
import PtCorr2.Obs.ObsHistU

/-!
# The initial `σ_aσ_b` activity at coalescence from the unreduced `ab` chain

`kRed_ab_poly_le` needs the full `wM M_aM_b` norms of the unreduced input `I = inI`, `K = inK` at
`j`. For the activity, `‖inK(X)‖_{wM} = ‖K(X)‖ + ‖K^{obs}(X)‖_{wM1} + (M_aM_b)^{-1}‖K^{obs}(X)_{ab}‖`
(`oTj_inK_eq`), and `A^{|𝓑(X)|} ≤ A⁴A^{(|𝓑(X)|-4)_+}`:

* **`redHist_K_ab_le_sizes`**: `‖inI(B)‖_{wM} ≤ ι` and the three regulated activity sizes
  `k_b` (bulk), `k₁` (one-point, `wM1`), `k₂` (`ab`, `(M_aM_b)^{-1}‖·_{ab}‖`) with
  `A⁴(k_b+k₁+k₂) ≤ 1` give `A^{(|𝓑(Y)|-4)_+}‖K'_j(Y)_{ab}‖ ≤ M_aM_b(2ιA)^{|𝓑(D)|}`;
* **`redHist_K_ab_le_U`**: the same at `j = j_{ab}` with `k₂` discharged by the unreduced chain
  `kab_hist` (`k₂ = c₂r_{j}m_{j}²`, `c₂ = 10B₂`, `w = wM M_aM_b`, the one-point sizes `m_i`, `k₁_i`
  along the history below coalescence as inputs, `ObsCoalInv` from `obsHist_coalInv_valid`).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD Obs2 ENNReal Flow2 Flow2.Hist

variable {L N : ℕ} [NeZero L] {c : Obs.Case}

theorem wOne_wM (Ma Mb : ℝ) : wOne (wM Ma Mb) = wM1 Ma Mb := rfl

theorem oTj_inK_eq (K : Act 2 L N) (o : ObsSt c L N) (ho : o.IsObs) (Ma Mb : ℝ) (j : ℕ) (ℓ : ℝ)
    (X : Finset (Lam 2 L N)) :
    oTj 2 L (wM Ma Mb) j ℓ (inK K o X : SA c (Lam 2 L N)) =
      Tj 2 (L : ℝ) j ℓ (K X : Alg 2 L N) + oTo (wM1 Ma Mb) j ℓ (o.K X) +
        (wM Ma Mb).ab * Tj 2 (L : ℝ) j ℓ (o.K X : SA c (Lam 2 L N)).ab := by
  rw [oTj_eq_bulk_add, add_assoc]
  congr 1
  · show Tj 2 (L : ℝ) j ℓ ((bulk ((emb (K X) : OE c (Lam 2 L N)) + o.K X) : EvR (Lam 2 L N)) :
      Alg 2 L N) = _
    rw [map_add, bulk_emb, ho.K X, add_zero]
  · show oTo (wM Ma Mb) j ℓ ((emb (K X) : OE c (Lam 2 L N)) + o.K X) = _
    rw [oTo_emb_add, oTo_split_ab, wOne_wM]

theorem regA_le (A : ℝ) (hA : 1 ≤ A) (n : ℕ) : A ^ n ≤ A ^ 4 * A ^ (n - 2 ^ 2) := by
  rw [← pow_add]; exact pow_le_pow_right₀ hA (by omega)

section Hist

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N) (o₀ : ObsSt c L N)

/-- **The initial `ab` activity from the sizes of the unreduced input.** -/
theorem redHist_K_ab_le_sizes {j : ℕ} {D : Finset (Lam 2 L N)} (t : Hist.Seq (Xs R))
    (h0 : o₀.IsObs) {Ma Mb : ℝ} (hMa : 0 < Ma) (hMb : 0 < Mb) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {A ι kb k₁ k₂ : ℝ} (hA : 1 ≤ A) (hι : 1 ≤ ι) (hkb : 0 ≤ kb) (hk₁ : 0 ≤ k₁) (hk₂ : 0 ≤ k₂)
    (hsm : A ^ 4 * (kb + k₁ + k₂) ≤ 1)
    (hI : ∀ b ∈ blocks j D, oTj 2 L (wM Ma Mb) j ℓ
      (inI R j (rawHist R j t) (t j).1 (t j).2.1 (rawD R (rawHist R j t).u (t j).2.2)
        (obsHist R P o₀ j t) b : SA c (Lam 2 L N)) ≤ ENNReal.ofReal ι)
    (hKb : ∀ X, IsConn j X → ENNReal.ofReal (A ^ (nb j X - 2 ^ 2)) *
      Tj 2 (L : ℝ) j ℓ (rawK R (rawHist R j t).u (t j).2.2 X : Alg 2 L N) ≤ ENNReal.ofReal kb)
    (hK1 : ∀ X, IsConn j X → ENNReal.ofReal (A ^ (nb j X - 2 ^ 2)) *
      oTo (wM1 Ma Mb) j ℓ ((obsHist R P o₀ j t).K X) ≤ ENNReal.ofReal k₁)
    (hK2 : ∀ X, IsConn j X → ENNReal.ofReal (A ^ (nb j X - 2 ^ 2)) *
      ((wM Ma Mb).ab * Tj 2 (L : ℝ) j ℓ ((obsHist R P o₀ j t).K X : SA c (Lam 2 L N)).ab) ≤
        ENNReal.ofReal k₂)
    (Y : Finset (Lam 2 L N)) :
    ENNReal.ofReal (A ^ (nb j Y - 2 ^ 2)) *
        Tj 2 (L : ℝ) j ℓ ((redHist R P o₀ j D t).K Y : SA c (Lam 2 L N)).ab ≤
      ENNReal.ofReal (Ma * Mb * (2 * ι * A) ^ nb j D) := by
  refine kRed_ab_poly_le hMa hMb hℓ hA hι _ _ hI (fun X hX => ?_) Y
  rw [oTj_inK_eq _ _ (obsHist_isObs R P o₀ h0 j t)]
  have hA0 : 0 ≤ A := by linarith
  calc ENNReal.ofReal (A ^ nb j X) * (Tj 2 (L : ℝ) j ℓ
        (rawK R (rawHist R j t).u (t j).2.2 X : Alg 2 L N) +
        oTo (wM1 Ma Mb) j ℓ ((obsHist R P o₀ j t).K X) +
        (wM Ma Mb).ab * Tj 2 (L : ℝ) j ℓ ((obsHist R P o₀ j t).K X : SA c (Lam 2 L N)).ab)
      ≤ ENNReal.ofReal (A ^ 4) * (ENNReal.ofReal (A ^ (nb j X - 2 ^ 2)) *
        (Tj 2 (L : ℝ) j ℓ (rawK R (rawHist R j t).u (t j).2.2 X : Alg 2 L N) +
        oTo (wM1 Ma Mb) j ℓ ((obsHist R P o₀ j t).K X) +
        (wM Ma Mb).ab * Tj 2 (L : ℝ) j ℓ ((obsHist R P o₀ j t).K X : SA c (Lam 2 L N)).ab)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        exact mul_le_mul_right' (ENNReal.ofReal_le_ofReal (regA_le A hA _)) _
    _ ≤ ENNReal.ofReal (A ^ 4) * (ENNReal.ofReal kb + ENNReal.ofReal k₁ + ENNReal.ofReal k₂) := by
        refine mul_le_mul_left' ?_ _
        rw [mul_add, mul_add]
        exact add_le_add (add_le_add (hKb X hX) (hK1 X hX)) (hK2 X hX)
    _ = ENNReal.ofReal (A ^ 4 * (kb + k₁ + k₂)) := by
        rw [← ENNReal.ofReal_add hkb hk₁, ← ENNReal.ofReal_add (by positivity) hk₂,
          ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ 1 := by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hsm

variable {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

set_option maxHeartbeats 4000000 in
/-- **The initial `ab` activity at coalescence, `ab` part of the activity discharged** by the
unreduced chain (`kab_hist` along `j < j_{ab}`). -/
theorem redHist_K_ab_le_U {C₀ η ε₀ C₁ : ℝ} (hKB : KObsBoundsU L R.A C₀ η ε₀ C₁) (hC₀ : 0 ≤ C₀)
    (hC₁ : 0 ≤ C₁)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    (h0 : o₀.IsObs) (hl0 : ObsLocInv P 0 o₀) (hs0 : ObsSymInv 0 o₀)
    (hinv₀ : ObsCoalInv P 0 o₀) (hL : 2 ^ (2 + 3) + 8 * 2 < L) (hρ : 0 ≤ R.ρ)
    (t : Hist.Seq (Xs R)) (hK0 : ∀ X, (o₀.K X : SA c (Lam 2 L N)).ab = 0)
    (hcN : coal L P.a P.b ≤ Nh)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε (coal L P.a P.b) t)
    {Ma Mb : ℝ} (hMa : 0 < Ma) (hMb : 0 < Mb) (hA1 : 1 ≤ R.A)
    (hs : 0 < histS R (coal L P.a P.b) t)
    (m k₁ : ℕ → ℝ) (c₁ : ℝ) (hc₁ : 0 ≤ c₁) (hm0 : ∀ j, 0 < m j)
    (hmm : ∀ j < coal L P.a P.b, m j ≤ 2 * m (j + 1)) (hk₁0 : ∀ j, 0 ≤ k₁ j)
    (hk₁ : ∀ j < coal L P.a P.b, k₁ j ≤ c₁ * (cR R Λ cm C₂ * (t j).1) ^ 2 * m j)
    (hrm : ∀ j < coal L P.a P.b, cR R Λ cm C₂ * (t j).1 ≤ m j)
    (hε1 : cR R Λ cm C₂ * ε ≤ 1) (hεε : 2 * (cR R Λ cm C₂ * ε) ≤ ε₀)
    (hkt1 : 8 * (cx κ cT + c₁ + 10 * kB2 (kθ0 L R.A C₀ η) C₁ (cx κ cT) c₁) *
      (cR R Λ cm C₂ * ε) ^ 3 ≤ 1)
    (hktε : 8 * (cx κ cT + c₁ + 10 * kB2 (kθ0 L R.A C₀ η) C₁ (cx κ cT) c₁) *
      (cR R Λ cm C₂ * ε) ^ 3 ≤ ε₀)
    (hθ' : 8 * kθ0 L R.A C₀ η + 16 * C₁ * (cR R Λ cm C₂ * ε) +
      8 * C₁ * (8 * (cx κ cT + c₁ + 10 * kB2 (kθ0 L R.A C₀ η) C₁ (cx κ cT) c₁) *
        (cR R Λ cm C₂ * ε) ^ 3) ≤ 1 / 10)
    (hVo : ∀ j < coal L P.a P.b, ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo (wM Ma Mb) j (histS R j t) ((obsHist R P o₀ j t).V b) ≤ ENNReal.ofReal (m j))
    (hWo : ∀ j < coal L P.a P.b, ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo (wM Ma Mb) j (histS R j t) ((obsHist R P o₀ j t).W b) ≤
        ENNReal.ofReal (cR R Λ cm C₂ * (t j).1 * m j))
    (hK1 : ∀ j < coal L P.a P.b, ∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
      oTo (wM1 Ma Mb) j (histS R j t) ((obsHist R P o₀ j t).K X) ≤ ENNReal.ofReal (k₁ j))
    {D : Finset (Lam 2 L N)} {ι kb kx : ℝ} (hι : 1 ≤ ι) (hkb : 0 ≤ kb) (hkx : 0 ≤ kx)
    (hsm : R.A ^ 4 * (kb + kx + 10 * kB2 (kθ0 L R.A C₀ η) C₁ (cx κ cT) c₁ *
      (cR R Λ cm C₂ * (t (coal L P.a P.b)).1) * m (coal L P.a P.b) ^ 2) ≤ 1)
    (hI : ∀ b ∈ blocks (coal L P.a P.b) D, oTj 2 L (wM Ma Mb) (coal L P.a P.b)
      (histS R (coal L P.a P.b) t)
      (inI R (coal L P.a P.b) (rawHist R (coal L P.a P.b) t) (t (coal L P.a P.b)).1
        (t (coal L P.a P.b)).2.1
        (rawD R (rawHist R (coal L P.a P.b) t).u (t (coal L P.a P.b)).2.2)
        (obsHist R P o₀ (coal L P.a P.b) t) b : SA c (Lam 2 L N)) ≤ ENNReal.ofReal ι)
    (hKb : ∀ X, IsConn (coal L P.a P.b) X →
      ENNReal.ofReal (R.A ^ (nb (coal L P.a P.b) X - 2 ^ 2)) *
      Tj 2 (L : ℝ) (coal L P.a P.b) (histS R (coal L P.a P.b) t)
        (rawK R (rawHist R (coal L P.a P.b) t).u (t (coal L P.a P.b)).2.2 X : Alg 2 L N) ≤
        ENNReal.ofReal kb)
    (hKx : ∀ X, IsConn (coal L P.a P.b) X →
      ENNReal.ofReal (R.A ^ (nb (coal L P.a P.b) X - 2 ^ 2)) *
      oTo (wM1 Ma Mb) (coal L P.a P.b) (histS R (coal L P.a P.b) t)
        ((obsHist R P o₀ (coal L P.a P.b) t).K X) ≤ ENNReal.ofReal kx)
    (Y : Finset (Lam 2 L N)) :
    ENNReal.ofReal (R.A ^ (nb (coal L P.a P.b) Y - 2 ^ 2)) *
        Tj 2 (L : ℝ) (coal L P.a P.b) (histS R (coal L P.a P.b) t)
          ((redHist R P o₀ (coal L P.a P.b) D t).K Y : SA c (Lam 2 L N)).ab ≤
      ENNReal.ofReal (Ma * Mb * (2 * ι * R.A) ^ nb (coal L P.a P.b) D) := by
  have hwS : (wM Ma Mb).Sub := wM_sub Ma Mb
  have hwa : (wM Ma Mb).a ≠ ⊤ := ENNReal.ofReal_ne_top
  have hwb : (wM Ma Mb).b ≠ ⊤ := ENNReal.ofReal_ne_top
  have hwab : (wM Ma Mb).ab ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hVc : ∀ k < coal L P.a P.b, ValidAt R k := fun k hk => hV k (by omega)
  have hinv := obsHist_coalInv_valid R P o₀ h0 hinv₀ hL hρ hVc t
  have hab := kab_hist R hKB hC₀ hC₁ hSB hV hm hβ hδ1 H P (wM Ma Mb) hwS hwa hwb hwab o₀ h0 hl0
    hs0 t hK0 (coal L P.a P.b) hcN ht (fun j hj X hX => (hinv j hj).Kab X hX) m k₁ c₁ hc₁ hm0
    hmm hk₁0 hk₁ hrm hε1 hεε hkt1 hktε hθ' hVo hWo
    (fun j hj X hX => by rw [wOne_wM]; exact hK1 j hj X hX) (coal L P.a P.b) le_rfl
  have hB0 : 0 ≤ kB2 (kθ0 L R.A C₀ η) C₁ (cx κ cT) c₁ := by
    have hA0 : (0 : ℝ) ≤ R.A / 2 := by linarith
    have : 0 ≤ kθ0 L R.A C₀ η := by unfold kθ0; have := Real.rpow_nonneg hA0 (-η); positivity
    unfold kB2; have := H.hcx; positivity
  have hcR : 0 ≤ cR R Λ cm C₂ := by
    unfold cR cV cW cZ; have := H.hcmu; have := H.hC₂; positivity
  have hg0 : 0 ≤ (t (coal L P.a P.b)).1 := (ht.1 _ le_rfl).1.le
  exact redHist_K_ab_le_sizes R P o₀ t h0 hMa hMb hs hA1 hι hkb hkx
    (by have := hm0 (coal L P.a P.b); positivity) hsm hI hKb hKx hab Y

end Hist

end

end PtCorr2
