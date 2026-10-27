import PtCorr.Conv
import FRD.WN

/-!
# Bounds on the bulk couplings at scale `N` and the sum of the covariances

## `|a_N| ≤ C L^{-2N} ‖V_N‖_N` (`norm_a_mul_le`, `norm_aN_le`)
At scale `N` the torus `Λ_N` is a single block (`blockSet_top`), so
`‖V(Λ)‖_{T_N(ℓ_N)} ≤ ‖V‖_N` (`Tj_top_le_Vnorm`).  Restricted to constant fields
`V(Λ) = |Λ| a ψψ̄` (`Suscept.Rc_eval`), so `F² = c2 (V(Λ)) = |Λ| a` (`c2_eval_univ`), and
`Suscept.norm_c2_le` gives `|Λ| |a| ≤ ℓ_N^{-2} ‖V‖_N`.  Since `|Λ| ℓ_N^2 = ℓ₀^2 L^{2N}`
(`card_mul_ellj_sq`): `|a| ℓ₀^2 L^{2N} ≤ ‖V‖_N`.

## `ã_{N,N}` and `ũ_{N,N}` (`norm_atN_mul_le`, `norm_utN_sub_le`, `norm_utN_le_of_mass`)
`ã = a_N - k_N^2/|Λ|` with `|k_N^2| ≤ ℓ_N^{-2} ‖K_N‖_N` (`Suscept.kN2_le`), hence
`|ã| ℓ₀^2 L^{2N} ≤ ‖V_N‖_N + ‖K_N‖_N`; `ũ - t_N ã = k_N^0` with `|k_N^0| ≤ ‖K_N‖_N`
(`Suscept.kN0_le`).  With `0 ≤ 1/m² - t_N ≤ K L^{2N}` (`FRD.tN_sub_inv`):
`|ã| (1/m² - t_N) ≤ K ℓ₀^{-2} (‖V_N‖_N + ‖K_N‖_N)` (`norm_atN_mul_inv_sub_tN_le`), and for
`1 ≤ m² L^{2N}`: `|ũ| ≤ ‖K_N‖_N + ℓ₀^{-2}(‖V_N‖_N + ‖K_N‖_N)` (`norm_utN_le_of_mass`).
The `_of` versions insert the bounds of `Flow.thm_flow`
(`‖V_N‖ ≤ C|b₀| L^{-κN}`, `‖K_N‖ ≤ C|b₀|² L^{-κN}`) as hypotheses.

## `∑_{k<N} C_{k+1}(a, b) = W_N(b - a)` (`sum_covAt_eq_WN`, `sum_covAt_diag_eq_WN`)
From `Suscept.Cov_eq` (`C = ∑_k C_{k+1} + t_N Q_N`), `Suscept.tQ_eq_cst` and translation
invariance `Suscept.Cov_transl` (for `m² > 0`, `N ≥ 1`).
-/

namespace PtCorr

noncomputable section

open Finset Grassmann Loc Step Obs FRD Flow Suscept

variable {d L N : ℕ} [NeZero L]

/-! ### Scale `N` is a single block -/

theorem blockSet_top :
    blockSet (L := L) (N := N) N (0 : Fin d → ℕ) = (univ : Finset (Lam d L N)) := by
  ext x; simp [blockSet, blk_top]

/-- `‖V(Λ)‖_{T_N(ℓ)} ≤ ‖V‖_N`. -/
theorem Tj_top_le_Vnorm (ℓ : ℝ) (V : Vcoup) :
    Tj d (L : ℝ) N ℓ (V.eval (univ : Finset (Lam d L N))) ≤
      Vnorm (d := d) (L := L) (N := N) N ℓ V := by
  have h := Tj_le_Vnorm (d := d) (L := L) (N := N) (j := N) (ℓ := ℓ) V (zero_mem_blockIdx N)
  rwa [blockSet_top] at h

/-- `F² = c2 (V(Λ)) = |Λ| a`. -/
theorem c2_eval_univ (V : Vcoup) :
    c2 (V.eval (univ : Finset (Lam d L N))) = (Fintype.card (Lam d L N) : ℂ) * V.a := by
  rw [← c2_Rc (mem_Ev.1 (eval_mem V univ)), Rc_eval, c2_smul, c2_P, mul_one]

/-- `|Λ_N| ℓ_N^2 = ℓ₀^2 L^{2N}`. -/
theorem card_mul_ellj_sq (ℓ₀ : ℝ) :
    (Fintype.card (Lam d L N) : ℝ) * ellj d L ℓ₀ N ^ 2 = ℓ₀ ^ 2 * (L : ℝ) ^ (2 * N) := by
  rw [card_lam, Obs.ellj_sq]
  have hL0 : (0 : ℝ) < L := Lr_pos
  have e : (((L ^ N : ℕ) : ℝ)) ^ d * ((L : ℝ) ^ (-((d : ℝ) - 2))) ^ N = (L : ℝ) ^ (2 * N) := by
    rw [← rpow_neg_mul_nat hL0.le, Nat.cast_pow, ← pow_mul, ← Real.rpow_natCast (L : ℝ) (N * d),
      ← Real.rpow_add hL0, ← Real.rpow_natCast (L : ℝ) (2 * N)]
    congr 1; push_cast; ring
  rw [← e]; ring

theorem card_pos' : (0 : ℝ) < Fintype.card (Lam d L N) := card_lam_pos N

/-! ### `|a| ≤ ℓ₀^{-2} L^{-2N} ‖V‖_N` -/

/-- `|a| ℓ₀^2 L^{2N} ≤ ‖V‖_N` (norm at scale `N` with `ℓ_N`). -/
theorem norm_a_mul_le {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) (V : Vcoup) :
    ‖V.a‖ * (ℓ₀ ^ 2 * (L : ℝ) ^ (2 * N)) ≤
      (Vnorm (d := d) (L := L) (N := N) N (ellj d L ℓ₀ N) V).toReal := by
  have hL0 : (0 : ℝ) < L := Lr_pos
  have hℓ := ellj_pos (d := d) hL0 hℓ₀ N
  have hh : (0 : ℝ) < (L : ℝ) ^ N := pow_pos hL0 N
  have h1 := norm_c2_le (E := Dir d) (p := pPhi d) hh hℓ (V.eval (univ : Finset (Lam d L N)))
  rw [c2_eval_univ, norm_mul, Complex.norm_natCast] at h1
  have h2 : (Tj d (L : ℝ) N (ellj d L ℓ₀ N) (V.eval (univ : Finset (Lam d L N)))).toReal ≤
      (Vnorm (d := d) (L := L) (N := N) N (ellj d L ℓ₀ N) V).toReal :=
    ENNReal.toReal_mono (Vnorm_ne_top hℓ V) (Tj_top_le_Vnorm _ V)
  rw [← card_mul_ellj_sq]
  have h3 : (Fintype.card (Lam d L N) : ℝ) * ‖V.a‖ * ellj d L ℓ₀ N ^ 2 ≤
      (Tj d (L : ℝ) N (ellj d L ℓ₀ N) (V.eval (univ : Finset (Lam d L N)))).toReal := by
    have := mul_le_mul_of_nonneg_right h1 (sq_nonneg (ellj d L ℓ₀ N))
    rwa [mul_assoc _ (_⁻¹ ^ 2), ← mul_pow, inv_mul_cancel₀ hℓ.ne', one_pow, mul_one] at this
  calc ‖V.a‖ * ((Fintype.card (Lam d L N) : ℝ) * ellj d L ℓ₀ N ^ 2)
      = (Fintype.card (Lam d L N) : ℝ) * ‖V.a‖ * ellj d L ℓ₀ N ^ 2 := by ring
    _ ≤ _ := h3.trans h2

/-! ### `ã_{N,N}` and `ũ_{N,N}` -/

/-- `|k_N^2| / |Λ| ≤ ℓ₀^{-2} L^{-2N} ‖K_N‖_N`, in multiplied form. -/
theorem norm_kN2_div_mul_le {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) (A msq : ℝ) (V₀ : Vcoup) :
    ‖kN2 d L N msq V₀ / (Fintype.card (Lam d L N) : ℂ)‖ * (ℓ₀ ^ 2 * (L : ℝ) ^ (2 * N)) ≤
      (KNnorm d L N msq V₀ (ellj d L ℓ₀ N) A).toReal := by
  have hL0 : (0 : ℝ) < L := Lr_pos
  have hℓ := ellj_pos (d := d) hL0 hℓ₀ N
  have hn := card_pos' (d := d) (L := L) (N := N)
  have h := (kN2_le (d := d) (L := L) (N := N) hℓ A msq V₀).2
  rw [norm_div, Complex.norm_natCast, ← card_mul_ellj_sq]
  set n : ℝ := (Fintype.card (Lam d L N) : ℝ)
  set ℓ := ellj d L ℓ₀ N
  set k := KNnorm d L N msq V₀ ℓ A
  have e : ‖kN2 d L N msq V₀‖ / n * (n * ℓ ^ 2) = ‖kN2 d L N msq V₀‖ * ℓ ^ 2 := by
    field_simp
  rw [e]
  have := mul_le_mul_of_nonneg_right h (sq_nonneg ℓ)
  rwa [mul_comm (ℓ⁻¹ ^ 2), mul_assoc, ← mul_pow, inv_mul_cancel₀ hℓ.ne', one_pow,
    mul_one] at this

/-- **`|ã_{N,N}| ℓ₀^2 L^{2N} ≤ ‖V_N‖_N + ‖K_N‖_N`**. -/
theorem norm_atN_mul_le {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) (A msq : ℝ) (V₀ : Vcoup) :
    ‖atN d L N msq V₀‖ * (ℓ₀ ^ 2 * (L : ℝ) ^ (2 * N)) ≤
      (Vnorm (d := d) (L := L) (N := N) N (ellj d L ℓ₀ N) (VN d L N msq V₀)).toReal +
        (KNnorm d L N msq V₀ (ellj d L ℓ₀ N) A).toReal := by
  have hp : 0 ≤ ℓ₀ ^ 2 * (L : ℝ) ^ (2 * N) := by have := Lr_pos (L := L); positivity
  have h1 := norm_a_mul_le (d := d) (L := L) (N := N) hℓ₀ (VN d L N msq V₀)
  have h2 := norm_kN2_div_mul_le (d := d) (L := L) (N := N) hℓ₀ A msq V₀
  calc ‖atN d L N msq V₀‖ * (ℓ₀ ^ 2 * (L : ℝ) ^ (2 * N))
      ≤ (‖aN d L N msq V₀‖ + ‖kN2 d L N msq V₀ / (Fintype.card (Lam d L N) : ℂ)‖) *
          (ℓ₀ ^ 2 * (L : ℝ) ^ (2 * N)) :=
        mul_le_mul_of_nonneg_right (norm_sub_le _ _) hp
    _ ≤ _ := by rw [add_mul]; exact add_le_add h1 h2

/-- `|ã_{N,N}| ≤ ℓ₀^{-2} L^{-2N} (‖V_N‖_N + ‖K_N‖_N)`. -/
theorem norm_atN_le {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) (A msq : ℝ) (V₀ : Vcoup) :
    ‖atN d L N msq V₀‖ ≤ (ℓ₀ ^ 2 * (L : ℝ) ^ (2 * N))⁻¹ *
      ((Vnorm (d := d) (L := L) (N := N) N (ellj d L ℓ₀ N) (VN d L N msq V₀)).toReal +
        (KNnorm d L N msq V₀ (ellj d L ℓ₀ N) A).toReal) := by
  have hp : 0 < ℓ₀ ^ 2 * (L : ℝ) ^ (2 * N) := by have := Lr_pos (L := L); positivity
  rw [inv_mul_eq_div, le_div_iff₀ hp]
  exact norm_atN_mul_le hℓ₀ A msq V₀

/-- **`ũ_{N,N} - t_N ã_{N,N} = k_N^0`**, so `|ũ - t_N ã| ≤ ‖K_N‖_N`. -/
theorem norm_utN_sub_le {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) (A msq : ℝ) (V₀ : Vcoup) :
    ‖utN d L N msq V₀ - atN d L N msq V₀ * (tNN d L N msq : ℂ)‖ ≤
      (KNnorm d L N msq V₀ (ellj d L ℓ₀ N) A).toReal := by
  have hℓ := ellj_pos (d := d) (Lr_pos (L := L)) hℓ₀ N
  rw [utN, add_sub_cancel_right]
  exact (kN0_le hℓ A msq V₀).2

/-- `|ã_{N,N}| (1/m² - t_N) ≤ K ℓ₀^{-2} (‖V_N‖_N + ‖K_N‖_N)`, with the constant `K` of
`FRD.tN_sub_inv` (independent of `m², L, N`). -/
theorem norm_atN_mul_inv_sub_tN_le (hd : 1 ≤ d) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (L : ℕ) [NeZero L] (N : ℕ)
    {ℓ₀ : ℝ}, 0 < ℓ₀ → ∀ (A msq : ℝ), 0 < msq → ∀ V₀ : Vcoup,
    0 ≤ 1 / msq - tNN d L N msq ∧
    ‖atN d L N msq V₀‖ * (1 / msq - tNN d L N msq) ≤ K * (ℓ₀ ^ 2)⁻¹ *
      ((Vnorm (d := d) (L := L) (N := N) N (ellj d L ℓ₀ N) (VN d L N msq V₀)).toReal +
        (KNnorm d L N msq V₀ (ellj d L ℓ₀ N) A).toReal) := by
  obtain ⟨K, hK⟩ := tN_sub_inv (P := stdPt) hd
  have hK0 : 0 ≤ K := by
    obtain ⟨h1, h2⟩ := hK 1 one_pos 1 le_rfl 0
    simp at h2
    linarith
  refine ⟨K, hK0, fun L _ N ℓ₀ hℓ₀ A msq hmsq V₀ => ?_⟩
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast NeZero.one_le
  obtain ⟨h1, h2⟩ := hK msq hmsq L hL1 N
  refine ⟨h1, ?_⟩
  have hp : 0 < ℓ₀ ^ 2 * (L : ℝ) ^ (2 * N) := by have := Lr_pos (L := L); positivity
  have h3 := norm_atN_mul_le (d := d) (L := L) (N := N) hℓ₀ A msq V₀
  set X := (Vnorm (d := d) (L := L) (N := N) N (ellj d L ℓ₀ N) (VN d L N msq V₀)).toReal +
    (KNnorm d L N msq V₀ (ellj d L ℓ₀ N) A).toReal
  have hℓ2 : 0 < ℓ₀ ^ 2 := by positivity
  calc ‖atN d L N msq V₀‖ * (1 / msq - tNN d L N msq)
      ≤ ‖atN d L N msq V₀‖ * (K * (L : ℝ) ^ (2 * N)) :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = K * (ℓ₀ ^ 2)⁻¹ * (‖atN d L N msq V₀‖ * (ℓ₀ ^ 2 * (L : ℝ) ^ (2 * N))) := by
        field_simp
    _ ≤ K * (ℓ₀ ^ 2)⁻¹ * X := mul_le_mul_of_nonneg_left h3 (by positivity)

/-- `0 ≤ t_N ≤ 1/m²` (`m² > 0`). -/
theorem tNN_nonneg_le (hd : 1 ≤ d) {msq : ℝ} (hmsq : 0 < msq) (L : ℕ) [NeZero L] (N : ℕ) :
    0 ≤ tNN d L N msq ∧ tNN d L N msq ≤ 1 / msq := by
  obtain ⟨K, hK⟩ := tN_sub_inv (P := stdPt) hd
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast NeZero.one_le
  refine ⟨(tN_pos stdPt hmsq (by linarith) N).le, ?_⟩
  have := (hK msq hmsq L hL1 N).1
  linarith

/-- **`|ũ_{N,N}| ≤ ‖K_N‖_N + ℓ₀^{-2} (‖V_N‖_N + ‖K_N‖_N)`** if `1 ≤ m² L^{2N}` (i.e.
`L^{-N} ≤ m`), as `t_N ≤ 1/m² ≤ L^{2N}`. -/
theorem norm_utN_le_of_mass (hd : 1 ≤ d) {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) (A : ℝ) {msq : ℝ}
    (hmsq : 0 < msq) (hm : 1 ≤ msq * (L : ℝ) ^ (2 * N)) (V₀ : Vcoup) :
    ‖utN d L N msq V₀‖ ≤ (KNnorm d L N msq V₀ (ellj d L ℓ₀ N) A).toReal + (ℓ₀ ^ 2)⁻¹ *
      ((Vnorm (d := d) (L := L) (N := N) N (ellj d L ℓ₀ N) (VN d L N msq V₀)).toReal +
        (KNnorm d L N msq V₀ (ellj d L ℓ₀ N) A).toReal) := by
  obtain ⟨ht0, ht1⟩ := tNN_nonneg_le hd hmsq L N
  have hp : 0 < (L : ℝ) ^ (2 * N) := pow_pos Lr_pos _
  have htL : tNN d L N msq ≤ (L : ℝ) ^ (2 * N) := by
    refine ht1.trans ?_
    rw [div_le_iff₀ hmsq]; linarith
  have h1 := norm_utN_sub_le (d := d) (L := L) (N := N) hℓ₀ A msq V₀
  have h2 := norm_atN_mul_le (d := d) (L := L) (N := N) hℓ₀ A msq V₀
  have h3 : ‖atN d L N msq V₀ * (tNN d L N msq : ℂ)‖ ≤ (ℓ₀ ^ 2)⁻¹ *
      (‖atN d L N msq V₀‖ * (ℓ₀ ^ 2 * (L : ℝ) ^ (2 * N))) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    have : (ℓ₀ ^ 2)⁻¹ * (‖atN d L N msq V₀‖ * (ℓ₀ ^ 2 * (L : ℝ) ^ (2 * N))) =
        ‖atN d L N msq V₀‖ * (L : ℝ) ^ (2 * N) := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left htL (norm_nonneg _)
  calc ‖utN d L N msq V₀‖
      ≤ ‖utN d L N msq V₀ - atN d L N msq V₀ * (tNN d L N msq : ℂ)‖ +
          ‖atN d L N msq V₀ * (tNN d L N msq : ℂ)‖ := norm_le_norm_sub_add _ _
    _ ≤ _ := add_le_add h1 (h3.trans (mul_le_mul_of_nonneg_left h2 (by positivity)))

/-! ### Along `Flow.thm_flow` -/

/-! ### `∑_{k<N} C_{k+1}(a, b) = W_N(b - a)` -/

/-- **`∑_{k<N} C_{k+1}(a, b) = C(a, b) - t_N/|Λ|`** (`m² > 0`, `N ≥ 1`). -/
theorem sum_covAt_eq {msq : ℝ} (hmsq : 0 < msq) (hN : 1 ≤ N) (a b : Lam d L N) :
    ∑ k ∈ range N, covAt d L N msq k a b =
      Cov d L N msq a b - tNN d L N msq / Fintype.card (Lam d L N) := by
  rw [Cov_eq hmsq hN, tQ_eq_cst, Matrix.add_apply, Matrix.sum_apply]
  have hc : Suscept.cst (Lam d L N) (tNN d L N msq / Fintype.card (Lam d L N)) a b =
      tNN d L N msq / Fintype.card (Lam d L N) := rfl
  rw [hc, add_sub_cancel_right]

/-- **`∑_{k<N} C_{k+1}(a, b) = W_N(b - a)`** (`m² > 0`, `N ≥ 1`). -/
theorem sum_covAt_eq_WN {msq : ℝ} (hmsq : 0 < msq) (hN : 1 ≤ N) (a b : Lam d L N) :
    ∑ k ∈ range N, covAt d L N msq k a b =
      WN (d := d) (n := L ^ N) stdPt msq (L : ℝ) N (b - a) := by
  rw [sum_covAt_eq hmsq hN, WN, ← card_lam]
  have h := Cov_transl hmsq hN 0 (b - a) a
  rw [zero_add, sub_add_cancel] at h
  rw [h]
  rfl

/-- `∑_{k<N} C_{k+1}(x, x) = W_N(0)`. -/
theorem sum_covAt_diag_eq_WN {msq : ℝ} (hmsq : 0 < msq) (hN : 1 ≤ N) (x : Lam d L N) :
    ∑ k ∈ range N, covAt d L N msq k x x =
      WN (d := d) (n := L ^ N) stdPt msq (L : ℝ) N (0 : Lam d L N) := by
  rw [sum_covAt_eq_WN hmsq hN, sub_self]

end

end PtCorr
