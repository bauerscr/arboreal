import DressedFRD.Est2

/-!
# The series representation of the word sums

For `|ζ' ε_j| < 1`, every scale part is the sum of its words:
`wSc_s = ∑_k ζ'^{k+1} ∑_{|w| = k+2, s(w) = s} O_w` pointwise (`hasSum_wSc`). For `s < N` the sum
is finite (`wLen_eq_zero`); for `s = N` it is the series of `e:words`.
-/

namespace DressedFRD

noncomputable section

open Finset Grassmann FRD

variable {d n : ℕ} [NeZero n]

namespace Data

variable {D : Data d n}

theorem one_le_rbV (hL : 1 ≤ D.L) (j : ℕ) (κ : Fin 3) (ℓ : Option ℕ) : 1 ≤ D.rbV j κ ℓ := by
  have h1 : ∀ e, 1 ≤ D.L ^ e := fun e => Nat.one_le_pow _ _ (by omega)
  unfold rbV
  rcases ℓ with _ | r <;> split <;> simp_all <;> first | exact h1 _ | (have := h1 r; omega) | (have := h1 j; omega)

theorem le_rbar (hL : 1 ≤ D.L) (j : ℕ) {k : ℕ} (w : Fin (k + 2) → Option ℕ) :
    k + 2 ≤ rbar (D.rbV j) w := by
  unfold rbar
  calc k + 2 = ∑ _i : Fin (k + 2), 1 := by simp
    _ ≤ _ := sum_le_sum fun i _ => one_le_rbV hL j _ _

/-- Words of scale `s < N` have length `< L^s`. -/
theorem wLen_eq_zero (hL : 1 ≤ D.L) {j s : ℕ} (hs : s < D.N) (R : ℕ → Sym d n) {k : ℕ}
    (hk : D.L ^ s ≤ k) : D.wLen j R s k = 0 := by
  unfold wLen
  refine sum_eq_zero fun w hw => ?_
  rw [mem_filter] at hw
  have h1 := lt_pow_scale (L := D.L) (j := j) (N := D.N) (R := rbar (D.rbV j) w) (by rw [hw.2]; exact hs)
  rw [hw.2] at h1
  have := le_rbar hL j w
  omega

/-- All words of length `k + 2`, by scale. -/
theorem sum_wLen (j : ℕ) (hj : j + 1 ≤ D.N) (R : ℕ → Sym d n) (k : ℕ) :
    ∑ s ∈ Icc (j + 1) D.N, D.wLen j R s k = ∑ w ∈ words j D.N k, wordVal (D.letV j R) w := by
  unfold wLen
  refine sum_fiberwise_of_maps_to (fun w _ => ?_) _
  rw [mem_Icc]; exact ⟨le_scale, scale_le hj⟩

/-- `∑_w O_w = A^{-1} ε (1-ε) ε^k` pointwise. -/
theorem sum_words_apply (h : StdHyp D.L D.N D.msq D.C) (j : ℕ) (R : ℕ → Sym d n) (k : ℕ)
    (m : Torus d n) :
    (∑ w ∈ words j D.N k, wordVal (D.letV j R) w) m =
      (Asym D.msq m)⁻¹ * D.eps j R m * (1 - D.eps j R m) * D.eps j R m ^ k := by
  have hA := Asym_ne_zero h m
  have key : (Cle D.C j - ∑ r ∈ Ioc j D.N, D.Z j • R r) m = (Asym D.msq m)⁻¹ * D.eps j R m := by
    rw [eps_apply, Pi.sub_apply, Finset.sum_apply, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Ehat, Pi.mul_apply]
    rw [← Finset.mul_sum]
    field_simp
  rw [sum_words_prod, sum_letV_a, sum_letV_b, sum_letV_c]
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, Pi.one_apply]
  rw [← Pi.sub_apply, key]

theorem hasSum_wTot (h : StdHyp D.L D.N D.msq D.C) (j : ℕ) (hj : j + 1 ≤ D.N)
    (R : ℕ → Sym d n) (m : Torus d n) (hden : ‖D.zp j * D.eps j R m‖ < 1) :
    HasSum (fun k => ∑ s ∈ Icc (j + 1) D.N, (D.zp j ^ (k + 1) • D.wLen j R s k) m)
      (D.wTot j R m) := by
  have hg := hasSum_geometric_of_norm_lt_one hden
  have hg2 := hg.mul_left (D.zp j * (Asym D.msq m)⁻¹ * D.eps j R m * (1 - D.eps j R m))
  convert hg2 using 1
  · funext k
    rw [← Finset.sum_apply, ← Finset.smul_sum, Pi.smul_apply, smul_eq_mul, sum_wLen j hj R k,
      sum_words_apply h j R k m]
    ring

/-- `wSc_s = ∑_k ζ'^{k+1} wLen_s k` pointwise, for `s ∈ [j+1, N]`. -/
theorem hasSum_wSc (h : StdHyp D.L D.N D.msq D.C) (hL : 1 ≤ D.L) (j : ℕ) (hj : j + 1 ≤ D.N)
    (R : ℕ → Sym d n) (m : Torus d n) (hden : ‖D.zp j * D.eps j R m‖ < 1) {s : ℕ}
    (hs : s ∈ Icc (j + 1) D.N) :
    HasSum (fun k => (D.zp j ^ (k + 1) • D.wLen j R s k) m) (D.wSc j R s m) := by
  -- the finite scales
  have hlow : ∀ s', s' < D.N →
      HasSum (fun k => (D.zp j ^ (k + 1) • D.wLen j R s' k) m) (D.wLow j R s' m) := by
    intro s' hs'
    have : D.wLow j R s' m = ∑ k ∈ range (D.L ^ s'), (D.zp j ^ (k + 1) • D.wLen j R s' k) m := by
      simp [wLow, Finset.sum_apply]
    rw [this]
    refine hasSum_sum_of_ne_finset_zero fun k hk => ?_
    rw [mem_range, not_lt] at hk
    rw [wLen_eq_zero hL hs' R hk, smul_zero]; rfl
  by_cases hsN : s < D.N
  · simp only [wSc, if_pos hsN]; exact hlow s hsN
  · have hsN' : s = D.N := by rw [mem_Icc] at hs; omega
    subst hsN'
    simp only [wSc, lt_irrefl, if_false, wTop]
    have htot := hasSum_wTot h j hj R m hden
    have hI : Icc (j + 1) D.N = insert D.N (Ico (j + 1) D.N) := by
      ext s; simp only [mem_Icc, mem_insert, mem_Ico]; omega
    have hsum : HasSum (fun k => ∑ s ∈ Ico (j + 1) D.N, (D.zp j ^ (k + 1) • D.wLen j R s k) m)
        (∑ s ∈ Ico (j + 1) D.N, D.wLow j R s m) :=
      hasSum_sum fun s hs => hlow s (mem_Ico.1 hs).2
    have := htot.sub hsum
    simp only [hI, sum_insert (show D.N ∉ Ico (j + 1) D.N by simp), add_sub_cancel_right] at this
    simpa [Pi.sub_apply, Finset.sum_apply] using this

end Data

end

end DressedFRD
