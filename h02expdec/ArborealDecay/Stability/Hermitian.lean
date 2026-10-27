module

public import Mathlib

/-!
# Nonvanishing of determinants with positive imaginary quadratic form

If `M : Matrix n n ℂ` satisfies `Im (v* M v) > 0` for all `v ≠ 0`, then `det M ≠ 0`.
-/

@[expose] public section

namespace ArborealDecay.Stability

open Matrix

theorem det_ne_zero_of_im_quadForm_pos {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (h : ∀ v : n → ℂ, v ≠ 0 → 0 < (star v ⬝ᵥ M.mulVec v).im) :
    M.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have := h v hv
  rw [hMv] at this
  simp at this

end ArborealDecay.Stability
