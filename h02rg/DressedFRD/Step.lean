import DressedFRD.SumBound

/-!
# One step of the induction (Section `sec:proof`, "Conclusion of the proof")

* `Sj_succ_le`: `𝒮_{j+1} ≤ θ^{6/256} 𝒮_j + ∑_{s ≥ j+2} W_{s-1-j} ‖w_s‖_{(s-1)}`.
* `wLow_succ_eq`: the words assigned to scale `j + 1` are standard (no tail letters).
* `snorm_Gint_sub_le`, `snorm_Gint_first_le`: `thm:main`(iv),(v) at one step.
-/

namespace DressedFRD

noncomputable section

open Finset Grassmann FRD

variable {d n : ℕ} [NeZero n]

namespace Data

variable {D : Data d n} {q : ℕ} {c₂ θ : ℝ} {j : ℕ}

theorem Z_ne_zero (hζ : ∀ i, ‖D.ζ i‖ ≤ 1 / 2) (j : ℕ) : D.Z j ≠ 0 := by
  unfold Z
  refine prod_ne_zero_iff.2 fun i _ => ?_
  intro h
  have : D.ζ i = -1 := by linear_combination h
  have := hζ i
  rw [‹D.ζ i = -1›, norm_neg, norm_one] at this
  norm_num at this

theorem one_add_ne_zero (hζ : ‖D.ζ j‖ ≤ 1 / 2) : 1 + D.ζ j ≠ 0 := by
  intro h
  have : D.ζ j = -1 := by linear_combination h
  rw [this, norm_neg, norm_one] at hζ; norm_num at hζ

theorem norm_one_add_ge (hζ : ‖D.ζ j‖ ≤ 1 / 2) : 1 / 2 ≤ ‖1 + D.ζ j‖ := by
  have := norm_sub_norm_le (1 : ℂ) (-D.ζ j)
  rw [sub_neg_eq_add, norm_one, norm_neg] at this
  linarith

theorem norm_zp_le (hζ : ‖D.ζ j‖ ≤ 1 / 2) : ‖D.zp j‖ ≤ 2 * ‖D.ζ j‖ := by
  unfold zp
  rw [norm_div, div_le_iff₀ (by linarith [norm_one_add_ge hζ])]
  nlinarith [norm_one_add_ge hζ, norm_nonneg (D.ζ j)]

theorem norm_zp_sub_le (hζ : ‖D.ζ j‖ ≤ 1 / 2) : ‖D.zp j - D.ζ j‖ ≤ 2 * ‖D.ζ j‖ ^ 2 := by
  have h1 := one_add_ne_zero hζ
  have e : D.zp j - D.ζ j = -(D.ζ j ^ 2) / (1 + D.ζ j) := by
    unfold zp; field_simp; ring
  rw [e, norm_div, norm_neg, norm_pow, div_le_iff₀ (by linarith [norm_one_add_ge hζ])]
  nlinarith [norm_one_add_ge hζ, sq_nonneg ‖D.ζ j‖]

/-- `𝒮_{j+1} ≤ θ^{6/256} 𝒮_j + ∑_{s=j+2}^N W_{s-1-j} ‖w_s‖_{(s-1)}`. -/
theorem Sj_succ_le (H : D.StepHyp q c₂ θ j) (hζ : ∀ i, ‖D.ζ i‖ ≤ 1 / 2) :
    D.Sj q θ (j + 1) ≤ θ ^ ((6 : ℝ) / 256) * D.Sj q θ j +
      ∑ s ∈ Icc (j + 2) D.N, Wt θ D.L (s - 1 - j) * snorm D.L q (s - 1) (D.wSc j (D.tails j) s) := by
  have hL7 := H.hL
  have hL1 : 1 ≤ D.L := by omega
  have hL0 : (0 : ℝ) < D.L := by exact_mod_cast (by omega : 0 < D.L)
  have hZ1 := Z_ne_zero hζ (j + 1)
  have hIoc : Ioc (j + 1) D.N = Icc (j + 2) D.N := by ext r; simp only [mem_Ioc, mem_Icc]; omega
  have htW : ∀ r ∈ Ioc (j + 1) D.N, D.tW q (j + 1) r ≤
      D.tW q j r + snorm D.L q (r - 1) (D.wSc j (D.tails j) r) := by
    intro r hr
    rw [mem_Ioc] at hr
    simp only [tW, tails, if_pos (⟨by omega, hr.2⟩ : j + 2 ≤ r ∧ r ≤ D.N), snorm_smul hL0]
    rw [← mul_assoc, norm_inv, mul_inv_cancel₀ (norm_ne_zero_iff.2 hZ1), one_mul]
    refine (snorm_add_le hL0 _ _).trans ?_
    rw [snorm_smul hL0]
  unfold Sj
  calc ∑ r ∈ Ioc (j + 1) D.N, Wt θ D.L (r - (j + 1)) * D.tW q (j + 1) r
      ≤ ∑ r ∈ Ioc (j + 1) D.N, Wt θ D.L (r - (j + 1)) *
          (D.tW q j r + snorm D.L q (r - 1) (D.wSc j (D.tails j) r)) :=
        sum_le_sum fun r hr => mul_le_mul_of_nonneg_left (htW r hr) (Wt_pos H.hθ _ _).le
    _ = ∑ r ∈ Ioc (j + 1) D.N, Wt θ D.L (r - (j + 1)) * D.tW q j r +
          ∑ r ∈ Ioc (j + 1) D.N, Wt θ D.L (r - (j + 1)) *
            snorm D.L q (r - 1) (D.wSc j (D.tails j) r) := by
        rw [← sum_add_distrib]; exact sum_congr rfl fun r _ => by ring
    _ ≤ θ ^ ((6 : ℝ) / 256) * ∑ r ∈ Ioc j D.N, Wt θ D.L (r - j) * D.tW q j r +
          ∑ s ∈ Icc (j + 2) D.N, Wt θ D.L (s - 1 - j) *
            snorm D.L q (s - 1) (D.wSc j (D.tails j) s) := by
        refine add_le_add ?_ (le_of_eq ?_)
        · rw [mul_sum]
          calc ∑ r ∈ Ioc (j + 1) D.N, Wt θ D.L (r - (j + 1)) * D.tW q j r
              ≤ ∑ r ∈ Ioc (j + 1) D.N, θ ^ ((6 : ℝ) / 256) * (Wt θ D.L (r - j) * D.tW q j r) := by
                refine sum_le_sum fun r hr => ?_
                rw [mem_Ioc] at hr
                have := Wt_succ_ge H.hθ H.hθ1 (by exact_mod_cast hL7 : (7 : ℝ) ≤ D.L) (r - (j + 1))
                rw [show r - (j + 1) + 1 = r - j by omega] at this
                rw [← mul_assoc]
                exact mul_le_mul_of_nonneg_right this (tW_nonneg hL1 q j r)
            _ ≤ ∑ r ∈ Ioc j D.N, θ ^ ((6 : ℝ) / 256) * (Wt θ D.L (r - j) * D.tW q j r) :=
                sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_left (by omega)) fun r _ _ =>
                  mul_nonneg (Real.rpow_nonneg H.hθ.le _)
                    (mul_nonneg (Wt_pos H.hθ _ _).le (tW_nonneg hL1 q j r))
        · rw [hIoc]
          exact sum_congr rfl fun s _ => by rw [show s - (j + 1) = s - 1 - j by omega]

/-! ### The scale `j + 1` -/

/-- Words with a tail letter have scale `≥ j + 2` when `j + 1 < N`. -/
theorem scale_ne_of_tail (hL : 1 ≤ D.L) (hjN : j + 1 < D.N) {k : ℕ}
    {w : Fin (k + 2) → Option ℕ} (hw : w ∈ words j D.N k) {p : Fin (k + 2)} {r : ℕ}
    (hp : w p = some r) : scale D.L j D.N (rbar (D.rbV j) w) ≠ j + 1 := by
  intro hs
  have hrj := some_mem_alph.1 (hp ▸ Fintype.mem_piFinset.1 hw p)
  have h1 := lt_pow_scale (L := D.L) (j := j) (N := D.N) (R := rbar (D.rbV j) w) (by omega)
  rw [hs] at h1
  have h2 : D.L ^ r ≤ rbar (D.rbV j) w := by
    unfold rbar
    refine le_trans ?_ (single_le_sum (f := fun i => D.rbV j (kindOf i) (w i))
      (fun _ _ => Nat.zero_le _) (mem_univ p))
    simp only [hp]; generalize kindOf p = κ; fin_cases κ <;> simp [rbV]
  have h3 : D.L ^ (j + 1) ≤ D.L ^ r := Nat.pow_le_pow_right (by omega) hrj.1
  omega

/-- The words of scale `j + 1` are standard. -/
theorem wLen_succ_eq (hL : 1 ≤ D.L) (hjN : j + 1 < D.N) (R : ℕ → Sym d n) (k : ℕ) :
    D.wLen j (D.tails j) (j + 1) k =
      if scale D.L j D.N (rbar (D.rbV j) (fun _ : Fin (k + 2) => (none : Option ℕ))) = j + 1 then
        wordVal (D.letV j (D.tails j)) (fun _ : Fin (k + 2) => (none : Option ℕ)) else 0 := by
  unfold wLen
  have hstd : (fun _ : Fin (k + 2) => (none : Option ℕ)) ∈ words j D.N k :=
    Fintype.mem_piFinset.2 fun _ => none_mem_alph j D.N
  have hsub : (words j D.N k).filter (fun w => scale D.L j D.N (rbar (D.rbV j) w) = j + 1) ⊆
      {fun _ => none} := by
    intro w hw
    rw [mem_filter] at hw
    rw [mem_singleton]
    funext i
    rcases h : w i with _ | r
    · rfl
    · exact absurd hw.2 (scale_ne_of_tail hL hjN hw.1 h)
  split_ifs with hs
  · rw [Finset.sum_subset hsub (fun w hw hw' => by
      exfalso; apply hw'; rw [mem_singleton] at hw; subst hw; exact mem_filter.2 ⟨hstd, hs⟩),
      sum_singleton]
  · refine sum_eq_zero fun w hw => ?_
    have h1 := hsub hw
    rw [mem_singleton] at h1
    subst h1
    exact absurd (mem_filter.1 hw).2 hs

theorem snorm_wLen_succ_le (H : D.StepHyp q c₂ θ j) (hjN : j + 1 < D.N) (k : ℕ) :
    snorm D.L q j (D.wLen j (D.tails j) (j + 1) k) ≤ c₂ := by
  have hL1 : 1 ≤ D.L := by have := H.hL; omega
  have hL0 : (0 : ℝ) < D.L := by exact_mod_cast (by omega : 0 < D.L)
  rw [wLen_succ_eq hL1 hjN (D.tails j) k]
  split_ifs
  · exact snorm_std_word_le H.std H.loc hL1 H.hj (D.tails j) k
  · have := snorm_smul (q := q) (s := j) hL0 0 (0 : Sym d n)
    simp only [zero_smul, norm_zero, zero_mul] at this
    rw [this]
    exact le_trans (snorm_nonneg hL0 _) (H.loc 0 (by have := H.hj; omega))

theorem sum_range_geom_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) (K : ℕ) :
    ∑ k ∈ range K, x ^ k ≤ 2 :=
  (Summable.sum_le_tsum _ (fun k _ => pow_nonneg h0 k) (summable_geom_half h0 h1)).trans
    (tsum_geom_half_le h0 h1)

/-- The words of scale `j + 1`: `‖w_{j+1}‖_{(j)} ≤ 2 c₂ |ζ'|`. -/
theorem snorm_wLow_succ_le (H : D.StepHyp q c₂ θ j) (hjN : j + 1 < D.N)
    (hzp : ‖D.zp j‖ ≤ 1 / 2) :
    snorm D.L q j (D.wLow j (D.tails j) (j + 1)) ≤ 2 * c₂ * ‖D.zp j‖ := by
  have hL0 : (0 : ℝ) < D.L := by exact_mod_cast (by have := H.hL; omega : 0 < D.L)
  have hc₂ : 0 ≤ c₂ := le_trans (snorm_nonneg hL0 _) (H.loc 0 (by have := H.hj; omega))
  unfold wLow
  refine (snorm_sum_le hL0 _ _).trans ?_
  calc ∑ k ∈ range (D.L ^ (j + 1)), snorm D.L q j (D.zp j ^ (k + 1) • D.wLen j (D.tails j) (j + 1) k)
      ≤ ∑ k ∈ range (D.L ^ (j + 1)), ‖D.zp j‖ * c₂ * ‖D.zp j‖ ^ k := by
        refine sum_le_sum fun k _ => ?_
        rw [snorm_smul hL0, norm_pow, pow_succ]
        have := snorm_wLen_succ_le H hjN k
        nlinarith [pow_nonneg (norm_nonneg (D.zp j)) k, norm_nonneg (D.zp j),
          mul_nonneg (pow_nonneg (norm_nonneg (D.zp j)) k) (norm_nonneg (D.zp j))]
    _ = ‖D.zp j‖ * c₂ * ∑ k ∈ range (D.L ^ (j + 1)), ‖D.zp j‖ ^ k := by rw [mul_sum]
    _ ≤ ‖D.zp j‖ * c₂ * 2 :=
        mul_le_mul_of_nonneg_left (sum_range_geom_le (norm_nonneg _) hzp _)
          (mul_nonneg (norm_nonneg _) hc₂)
    _ = _ := by ring

/-- The standard word of length `2` has scale `j + 1`. -/
theorem scale_std_zero (hL : 5 ≤ D.L) (hjN : j + 1 < D.N) :
    scale D.L j D.N (rbar (D.rbV j) (fun _ : Fin (0 + 2) => (none : Option ℕ))) = j + 1 := by
  rw [scale_eq_iff le_rfl hjN]
  refine ⟨?_, Or.inl rfl⟩
  have h1 : rbar (D.rbV j) (fun _ : Fin (0 + 2) => (none : Option ℕ)) = 2 * D.L ^ j + 2 := by
    simp [rbar, Fin.sum_univ_two, kindOf, rbV]; ring
  rw [h1, pow_succ]
  have : 1 ≤ D.L ^ j := Nat.one_le_pow _ _ (by omega)
  have := Nat.mul_le_mul_left (D.L ^ j) hL
  omega

/-- `‖w_{j+1} - ζ' C_{≤j}(1 - ê_j)‖_{(j)} ≤ 2 c₂ |ζ'|^2`. -/
theorem snorm_wLow_succ_first_le (H : D.StepHyp q c₂ θ j) (hjN : j + 1 < D.N)
    (hzp : ‖D.zp j‖ ≤ 1 / 2) :
    snorm D.L q j (D.wLow j (D.tails j) (j + 1) -
        D.zp j • (Cle D.C j * (1 - Ehat D.msq D.C j))) ≤ 2 * c₂ * ‖D.zp j‖ ^ 2 := by
  have hL7 := H.hL
  have hL1 : 1 ≤ D.L := by omega
  have hL0 : (0 : ℝ) < D.L := by exact_mod_cast (by omega : 0 < D.L)
  have hc₂ : 0 ≤ c₂ := le_trans (snorm_nonneg hL0 _) (H.loc 0 (by have := H.hj; omega))
  have hK : 0 < D.L ^ (j + 1) := pow_pos (by omega) _
  have h0 : D.wLen j (D.tails j) (j + 1) 0 = Cle D.C j * (1 - Ehat D.msq D.C j) := by
    rw [wLen_succ_eq hL1 hjN (D.tails j) 0, if_pos (scale_std_zero (by omega) hjN), wordVal_std]
    simp
  unfold wLow
  rw [Finset.range_eq_Ico]
  rw [Finset.sum_eq_sum_Ico_succ_bot hK, zero_add, pow_one, h0, add_sub_cancel_left]
  refine (snorm_sum_le hL0 _ _).trans ?_
  calc ∑ k ∈ Ico 1 (D.L ^ (j + 1)), snorm D.L q j (D.zp j ^ (k + 1) • D.wLen j (D.tails j) (j + 1) k)
      ≤ ∑ k ∈ Ico 1 (D.L ^ (j + 1)), ‖D.zp j‖ ^ 2 * c₂ * ‖D.zp j‖ ^ (k - 1) := by
        refine sum_le_sum fun k hk => ?_
        rw [mem_Ico] at hk
        rw [snorm_smul hL0, norm_pow, show k + 1 = 2 + (k - 1) by omega, pow_add]
        have := snorm_wLen_succ_le H hjN k
        have h1 : 0 ≤ ‖D.zp j‖ ^ 2 * ‖D.zp j‖ ^ (k - 1) := by positivity
        nlinarith
    _ = ‖D.zp j‖ ^ 2 * c₂ * ∑ k ∈ range (D.L ^ (j + 1) - 1), ‖D.zp j‖ ^ k := by
        rw [mul_sum, Finset.sum_Ico_eq_sum_range]
        refine sum_congr (by congr 1) fun k _ => by rw [show 1 + k - 1 = k by omega]
    _ ≤ ‖D.zp j‖ ^ 2 * c₂ * 2 :=
        mul_le_mul_of_nonneg_left (sum_range_geom_le (norm_nonneg _) hzp _) (by positivity)
    _ = _ := by ring

end Data

end

end DressedFRD
