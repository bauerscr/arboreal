import PtCorr2.Pair.PairInitAB
import Obs2.Pair.CoalHist
import PtCorr2.Pair.PairSectHist

/-!
# The initial `σ_aσ_b` activity at coalescence: the hypotheses of `kRed_ab_poly_le` split into
one-point and `ab` parts

`kRed_ab_poly_le` needs the full norms of the factors `I(B)`, `K(X)` of the *unreduced* input at
`j_x` in the weights `wM M_a M_b = (M_a^{-1}, M_b^{-1}, (M_aM_b)^{-1})`. These split
(`oTj_wM_eq`) into the one-point norm (weights `wM1 = (M_a^{-1}, M_b^{-1}, 0)`, the `w_{ab} = 0`
norms of the existing `Obs2` estimates) and the `ab` part relative to `M_aM_b`:

* **`kRed_ab_poly_le_split`**: `‖I(B)‖_{wM1} ≤ ι₁`, `‖I(B)_{ab}‖ ≤ M_aM_bι₂`,
  `A^{|X|}‖K(X)‖_{wM1} ≤ κ₁`, `A^{|X|}‖K(X)_{ab}‖ ≤ M_aM_bκ₂`, `κ₁ + κ₂ ≤ 1` give
  `A^{(|𝓑(Y)|-2^d)_+}‖kRed(Y)_{ab}‖ ≤ M_aM_b(2(ι₁+ι₂)A)^{|𝓑(D)|}`;
* **`redHist_K_ab_le`**: the same for the reduced state of the history (`redHist`);
* `inV_ab_eq_zero_of_coal`: below and at coalescence (`j ≤ j_{ab}`, Lemma `lem:coal`) the block
  potentials of the input have no `ab` part, so `I(B)_{ab}` comes only from `𝒲(B)_{ab}` and from
  products of one-point parts.

What is *not* proved (the open part of the initial bound): `‖𝒲_{j_x}(B)_{ab}‖`,
`A^{|X|}‖K_{j_x}(X)_{ab}‖ ≲ M_aM_b` for the unreduced history (see `Log.md`).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD Obs2 ENNReal Flow2 Flow2.Hist

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

/-- The one-point weights `(M_a^{-1}, M_b^{-1}, 0)`. -/
def wM1 (Ma Mb : ℝ) : Wt := ⟨ENNReal.ofReal Ma⁻¹, ENNReal.ofReal Mb⁻¹, 0⟩

/-- **The split of the `wM` norm** into the one-point norm and the `ab` part. -/
theorem oTj_wM_eq {Ma Mb : ℝ} (hMa : 0 < Ma) (j : ℕ) (ℓ : ℝ) (F : SA c (Lam d L N)) :
    oTj d L (wM Ma Mb) j ℓ F =
      oTj d L (wM1 Ma Mb) j ℓ F + ENNReal.ofReal (Ma * Mb)⁻¹ * Tj d (L : ℝ) j ℓ F.ab := by
  simp only [oTj, oNorm, wM, wM1, zero_mul, add_zero]
  rw [mul_inv, ENNReal.ofReal_mul (inv_nonneg.2 hMa.le)]

theorem ofReal_inv_mul_ofReal {M x : ℝ} (hM : 0 < M) :
    ENNReal.ofReal M⁻¹ * ENNReal.ofReal (M * x) = ENNReal.ofReal x := by
  rcases le_or_gt 0 x with hx | hx
  · rw [← ENNReal.ofReal_mul (inv_nonneg.2 hM.le), ← mul_assoc, inv_mul_cancel₀ hM.ne', one_mul]
  · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hM.le hx.le),
      ENNReal.ofReal_of_nonpos hx.le, mul_zero]

variable {j : ℕ} {D : Finset (Lam d L N)} {z0 : Lam d L N}

/-- **`kRed_ab_poly_le` with split hypotheses.** -/
theorem kRed_ab_poly_le_split {Ma Mb : ℝ} (hMa : 0 < Ma) (hMb : 0 < Mb) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {A ι₁ ι₂ κ₁ κ₂ : ℝ} (hA : 1 ≤ A) (hι₁ : 0 ≤ ι₁) (hι₂ : 0 ≤ ι₂) (hκ₁ : 0 ≤ κ₁) (hκ₂ : 0 ≤ κ₂)
    (hι : 1 ≤ ι₁ + ι₂) (hκ : κ₁ + κ₂ ≤ 1)
    (I : OFam c d L N) (K : OAct c d L N)
    (hI1 : ∀ b ∈ blocks j D, oTj d L (wM1 Ma Mb) j ℓ (I b : SA c (Lam d L N)) ≤ ENNReal.ofReal ι₁)
    (hIab : ∀ b ∈ blocks j D,
      Tj d (L : ℝ) j ℓ (I b : SA c (Lam d L N)).ab ≤ ENNReal.ofReal (Ma * Mb * ι₂))
    (hK1 : ∀ X, IsConn j X →
      ENNReal.ofReal (A ^ nb j X) * oTj d L (wM1 Ma Mb) j ℓ (K X : SA c (Lam d L N)) ≤
        ENNReal.ofReal κ₁)
    (hKab : ∀ X, IsConn j X →
      ENNReal.ofReal (A ^ nb j X) * Tj d (L : ℝ) j ℓ (K X : SA c (Lam d L N)).ab ≤
        ENNReal.ofReal (Ma * Mb * κ₂))
    (Y : Finset (Lam d L N)) :
    ENNReal.ofReal (A ^ (nb j Y - 2 ^ d)) *
        Tj d (L : ℝ) j ℓ (kRed j D z0 I K Y : SA c (Lam d L N)).ab ≤
      ENNReal.ofReal (Ma * Mb * (2 * (ι₁ + ι₂) * A) ^ nb j D) := by
  have hMM : 0 < Ma * Mb := mul_pos hMa hMb
  refine kRed_ab_poly_le hMa hMb hℓ hA hι I K (fun b hb => ?_) (fun X hX => ?_) Y
  · rw [oTj_wM_eq hMa]
    calc oTj d L (wM1 Ma Mb) j ℓ (I b : SA c (Lam d L N)) +
          ENNReal.ofReal (Ma * Mb)⁻¹ * Tj d (L : ℝ) j ℓ (I b : SA c (Lam d L N)).ab
        ≤ ENNReal.ofReal ι₁ + ENNReal.ofReal (Ma * Mb)⁻¹ * ENNReal.ofReal (Ma * Mb * ι₂) :=
          add_le_add (hI1 b hb) (mul_le_mul_right (hIab b hb) _)
      _ ≤ ENNReal.ofReal (ι₁ + ι₂) := by
          rw [ofReal_inv_mul_ofReal hMM, ← ENNReal.ofReal_add hι₁ hι₂]
  · rw [oTj_wM_eq hMa, mul_add]
    calc ENNReal.ofReal (A ^ nb j X) * oTj d L (wM1 Ma Mb) j ℓ (K X : SA c (Lam d L N)) +
          ENNReal.ofReal (A ^ nb j X) *
            (ENNReal.ofReal (Ma * Mb)⁻¹ * Tj d (L : ℝ) j ℓ (K X : SA c (Lam d L N)).ab)
        = ENNReal.ofReal (A ^ nb j X) * oTj d L (wM1 Ma Mb) j ℓ (K X : SA c (Lam d L N)) +
          ENNReal.ofReal (Ma * Mb)⁻¹ *
            (ENNReal.ofReal (A ^ nb j X) * Tj d (L : ℝ) j ℓ (K X : SA c (Lam d L N)).ab) := by
          ring
      _ ≤ ENNReal.ofReal κ₁ + ENNReal.ofReal (Ma * Mb)⁻¹ * ENNReal.ofReal (Ma * Mb * κ₂) :=
          add_le_add (hK1 X hX) (mul_le_mul_right (hKab X hX) _)
      _ ≤ 1 := by
          rw [ofReal_inv_mul_ofReal hMM, ← ENNReal.ofReal_add hκ₁ hκ₂, ← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal hκ

/-! ### Along the history -/

section Hist

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N) (o₀ : ObsSt c L N)

/-- **The initial `ab` activity of the reduced history** from split bounds of the unreduced
input `I = inI`, `K = inK` at scale `j`. -/
theorem redHist_K_ab_le {j : ℕ} {D : Finset (Lam 2 L N)} (t : Hist.Seq (Xs R))
    {Ma Mb : ℝ} (hMa : 0 < Ma) (hMb : 0 < Mb) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {A ι₁ ι₂ κ₁ κ₂ : ℝ} (hA : 1 ≤ A) (hι₁ : 0 ≤ ι₁) (hι₂ : 0 ≤ ι₂) (hκ₁ : 0 ≤ κ₁) (hκ₂ : 0 ≤ κ₂)
    (hι : 1 ≤ ι₁ + ι₂) (hκ : κ₁ + κ₂ ≤ 1)
    (hI1 : ∀ b ∈ blocks j D, oTj 2 L (wM1 Ma Mb) j ℓ
      (inI R j (rawHist R j t) (t j).1 (t j).2.1 (rawD R (rawHist R j t).u (t j).2.2)
        (obsHist R P o₀ j t) b : SA c (Lam 2 L N)) ≤ ENNReal.ofReal ι₁)
    (hIab : ∀ b ∈ blocks j D, Tj 2 (L : ℝ) j ℓ
      (inI R j (rawHist R j t) (t j).1 (t j).2.1 (rawD R (rawHist R j t).u (t j).2.2)
        (obsHist R P o₀ j t) b : SA c (Lam 2 L N)).ab ≤ ENNReal.ofReal (Ma * Mb * ι₂))
    (hK1 : ∀ X, IsConn j X → ENNReal.ofReal (A ^ nb j X) * oTj 2 L (wM1 Ma Mb) j ℓ
      (inK (rawK R (rawHist R j t).u (t j).2.2) (obsHist R P o₀ j t) X : SA c (Lam 2 L N)) ≤
        ENNReal.ofReal κ₁)
    (hKab : ∀ X, IsConn j X → ENNReal.ofReal (A ^ nb j X) * Tj 2 (L : ℝ) j ℓ
      (inK (rawK R (rawHist R j t).u (t j).2.2) (obsHist R P o₀ j t) X : SA c (Lam 2 L N)).ab ≤
        ENNReal.ofReal (Ma * Mb * κ₂))
    (Y : Finset (Lam 2 L N)) :
    ENNReal.ofReal (A ^ (nb j Y - 2 ^ 2)) *
        Tj 2 (L : ℝ) j ℓ ((redHist R P o₀ j D t).K Y : SA c (Lam 2 L N)).ab ≤
      ENNReal.ofReal (Ma * Mb * (2 * (ι₁ + ι₂) * A) ^ nb j D) :=
  kRed_ab_poly_le_split hMa hMb hℓ hA hι₁ hι₂ hκ₁ hκ₂ hι hκ _ _ hI1 hIab hK1 hKab Y

/-- **Below and at coalescence the block potentials of the input have no `ab` part**
(`obsHist_coal_valid`): `I(B)_{ab}` is generated by `𝒲(B)_{ab}` and one-point products only. -/
theorem inV_ab_eq_zero_of_coal (h₀ : o₀.IsObs) (hinv₀ : ObsCoalInv P 0 o₀)
    (hL : 2 ^ (2 + 3) + 8 * 2 < L) (hρ : 0 ≤ R.ρ)
    (hV : ∀ k < coal L P.a P.b, ValidAt R k) (t : Hist.Seq (Xs R)) {j : ℕ}
    (hj : j ≤ coal L P.a P.b) (b : Fin 2 → ℕ) :
    (inV R j (rawHist R j t) (t j).1 (t j).2.1 (obsHist R P o₀ j t) b : SA c (Lam 2 L N)).ab = 0 := by
  unfold inV
  rw [emb_add_ab]
  exact ((obsHist_coal_valid R P o₀ h₀ hinv₀ hL hρ hV t) j hj).1 b

end Hist

end

end PtCorr2
