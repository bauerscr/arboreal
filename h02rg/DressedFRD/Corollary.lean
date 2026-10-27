import DressedFRD.MainFull
import DressedFRD.GramRep

/-!
# `cor:rg`(a),(b)

* `cor_gram`: `Γ^int_{j+1}` is Gram-admissible at scale `j`:
  `|Z_{j+1}| ‖Γ^int_{j+1}‖_{(j)} ≤ c_S + K |ζ|_{≤j}`. With `gram_rep`, `gF_norm_le`, `gG_norm_le`
  and `norm_dop2_le` this gives the Gram representation and the derivative bounds.
* `cor_diag`: the diagonal value
  `Z_{j+1} Γ^int_{j+1}(0,0) = C_{j+1}(0,0) + ζ_j κ_j + O(|ζ_j|² + ζ̄^{L/256} |ζ|_{≤j}) L^{-j(d-2)}`,
  with `κ_j = ⨍ ê_j (1-ê_j)/(λ+m²) ∈ [0, c₂ L^{-j(d-2)}]` (`kappa_nonneg`, `kappa_le`).
-/

namespace DressedFRD

noncomputable section

open Finset FRD Data Grassmann

variable {d n : ℕ} [NeZero n]

namespace Data

variable {D : Data d n} {q M : ℕ} {cS ζbar K : ℝ}

/-- `cor:rg`(a). -/
theorem cor_gram (hS : StdFull D.L D.N q M D.msq cS D.C) (hL : 1 ≤ D.L)
    (hζ : ∀ i, ‖D.ζ i‖ ≤ 1 / 2) {j : ℕ} (hc : D.Concl q ζbar K j) (hj : j + 1 < D.N) :
    ‖D.Z (j + 1)‖ * snorm D.L q j (D.Gint j) ≤ cS + K * D.Mz (j + 1) := by
  have hL0 : (0 : ℝ) < D.L := by exact_mod_cast (by omega : 0 < D.L)
  have h1 := hc.close hj
  have h2 : snorm D.L q j (ofR (D.C (j + 1))) ≤ cS := by
    have := std_c hS hL (k := j + 1) (by omega) hj
    simpa using this
  rw [← snorm_smul hL0]
  calc snorm D.L q j (D.Z (j + 1) • D.Gint j)
      = snorm D.L q j (ofR (D.C (j + 1)) + (D.Z (j + 1) • D.Gint j - ofR (D.C (j + 1)))) := by
        congr 1; abel
    _ ≤ snorm D.L q j (ofR (D.C (j + 1))) +
          snorm D.L q j (D.Z (j + 1) • D.Gint j - ofR (D.C (j + 1))) := snorm_add_le hL0 _ _
    _ ≤ cS + K * D.Mz (j + 1) := add_le_add h2 h1

/-- `κ_j = ⨍ ê_j (1 - ê_j) / (λ + m²) = (C_{≤j}(1 - E_j))(0,0)`. -/
def kappa (D : Data d n) (j : ℕ) : ℝ :=
  avg fun m => (∑ k ∈ Icc 1 j, D.C k m) * (1 - ereal D.msq D.C j m)

theorem kern_u_zero (j : ℕ) :
    kern (Cle D.C j * (1 - Ehat D.msq D.C j)) 0 = (D.kappa j : ℂ) := by
  unfold kern kappa avg
  simp only [char_zero_right, mul_one, Pi.mul_apply, Pi.sub_apply, Pi.one_apply, Cle_apply,
    Ehat_apply]
  push_cast; rfl

/-- `cor:rg`(b). -/
theorem cor_diag (hL : 0 < (D.L : ℝ)) {j : ℕ} (hc : D.Concl q ζbar K j) (hj : j + 1 < D.N) :
    ‖kern (D.Z (j + 1) • D.Gint j) 0 - kern (ofR (D.C (j + 1))) 0 - D.ζ j * D.kappa j‖ ≤
      (D.L : ℝ) ^ (-((j : ℝ) * ((d : ℝ) - 2))) *
        (K * (‖D.ζ j‖ ^ 2 + ζbar ^ ((D.L : ℝ) / 256) * D.Mz (j + 1))) := by
  have h := norm_kern_le (q := q) (s := j) hL
    (D.Z (j + 1) • D.Gint j - ofR (D.C (j + 1)) - D.ζ j • (Cle D.C j * (1 - Ehat D.msq D.C j))) 0
  rw [kern_sub, kern_sub, kern_smul (D.ζ j), kern_u_zero] at h
  have hw : wgt d (D.L : ℝ) j 0 = (D.L : ℝ) ^ ((j : ℝ) * ((d : ℝ) - 2)) := by
    simp [wgt, Grassmann.mabs]
  rw [hw, ← Real.rpow_neg hL.le] at h
  exact h.trans (mul_le_mul_of_nonneg_left (hc.first hj) (Real.rpow_nonneg hL.le _))

end Data

end

end DressedFRD
