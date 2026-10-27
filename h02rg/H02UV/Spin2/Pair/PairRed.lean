import Spin2.Pair.PairCst
import Obs2.Pair.PairRed
import Step2.Flow.FlowHV

/-!
# The pair chain along the history: `n_a = n_b`, the defects at the step covariances

Along any Case-(2) observable history (`R.P = Pc`):

* **`histCovO_transl`**: the step covariances `C_k = kmat(Γ^{int}_k)` are translation invariant;
* **`nA2_eq_nB2_hist`**: hence the vertex factors agree, `n_{a,k} = n_{b,k}`
  (`V'_k(Λ)_∅ = V_{κ'_k}(Λ) + const`, `Obs2.bulk2_hist`; `Obs2.mass2_FC_pbp_Vcoup_transl`).
  So the mismatch term `(n_a - n_b)β_bA_a` of `Obs2.rSrc` vanishes identically;
* **`hist_m2Def_le`, `hist_detDef_le`**: for `b = a + w` (a lattice path of length `n`) and a
  step covariance with `GoodCov2 k ℓ_k`, the gradient and determinant defects are
  `≤ 2nℓ_k²/L^{k+1}` and `≤ 2nℓ_k⁴/L^{k+1}`. With `n ≍ |x| ≍ L^{j_x}` this is the decay
  `L^{-(k-j_x)}` above coalescence.

See `Obs2/Pair/PairRed.lean` and `Log.md` for why the `r̃` reduction of `Spin2/Pair/PairCst.lean`
(`PairSrcRel`) cannot be closed with uniform constants and for the Pauli-reduced route.
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Step2.D2

variable {L N : ℕ} [NeZero L]

section Hist

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : Obs2.ObsPts 2 L N)
  (o₀ : Obs2.ObsSt .two L N) (t : Hist.Seq (Xs R))

/-- **The step covariances are translation invariant** (`R.P = Pc`). -/
theorem histCovO_transl (hP : R.P = Pc) (k : ℕ) (v x y : Lam 2 L N) :
    Obs2.histCovO R t k (x + v) (y + v) = Obs2.histCovO R t k x y := by
  unfold Obs2.histCovO
  rw [stCov_eq_dData R hP t le_rfl]
  simp [DressedFRD.kmat]

/-- **`n_a = n_b` along the history**: `m₂F_{C_k}(ψ̄_aψ_a, V'_k(Λ)_∅) = m₂F_{C_k}(ψ̄_bψ_b, V'_k(Λ)_∅)`
for `k < n` (`ValidAt` below `n`, `R.P = Pc`). -/
theorem nA2_eq_nB2_hist (hP : R.P = Pc) {n : ℕ} (hV : ∀ i < n, ValidAt R i) (h₀ : o₀.IsObs)
    {k : ℕ} (hk : k < n) :
    Obs2.nA2 P k (Obs2.histCovO R t k) (Obs2.histVO2 R P o₀ t k) =
      Obs2.nB2 P k (Obs2.histCovO R t k) (Obs2.histVO2 R P o₀ t k) := by
  obtain ⟨r, hr⟩ := (Obs2.bulk2_hist R P o₀ t hV h₀).he k hk
  have e : (Obs2.VprLO k (Obs2.histCovO R t k) (Obs2.histVO2 R P o₀ t k) :
      Obs.SA .two (Lam 2 L N)).e = Obs2.bulkE2 (Obs2.histCovO R t) (Obs2.histVO2 R P o₀ t) k := rfl
  unfold Obs2.nA2 Obs2.nB2
  rw [e, hr, FC_add_right, FC_add_right, FC_smul_right, FC_smul_right, Obs2.FC_one_right, Obs2.FC_one_right, smul_zero,
    add_zero, add_zero]
  exact Obs2.mass2_FC_pbp_Vcoup_transl (histCovO_transl R t hP k) P.a P.b _

/-- The determinant defect of a step covariance along a lattice path. -/
theorem hist_detDef_le {k : ℕ} {ℓk : ℝ} (hC : GoodCov2 k ℓk (Obs2.histCovO R t k))
    (a : Lam 2 L N) (w : List (Dir 2)) :
    ‖Obs2.histCovO R t k a a * Obs2.histCovO R t k (Obs2.pathEnd a w) (Obs2.pathEnd a w) -
        Obs2.histCovO R t k a (Obs2.pathEnd a w) * Obs2.histCovO R t k (Obs2.pathEnd a w) a‖ ≤
      2 * w.length * (ℓk ^ 2 / (L : ℝ) ^ (k + 1)) * ℓk ^ 2 :=
  Obs2.norm_detDef_le hC a w

end Hist

end

end Spin2
