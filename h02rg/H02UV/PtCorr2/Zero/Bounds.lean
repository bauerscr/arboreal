import PtCorr2.Zero.Final

/-!
# Bounds on the coefficients of the zero-mode integration (`prop:ZNN`, `e:ZNN-bd` analogue)

The coefficients of `Rc Z̃_{N,N}` (`PtCorr2.Zero.Final`) are bounded by the `T_N(h)` norms of the
final-scale object: `|ε F| ≤ ‖F‖`, `|c2 F| ≤ h^{-2} ‖F‖` (`Loc.abs_eps_le`, `Suscept.norm_c2_le`).
With `n_B ≤ M` blocks, `‖𝒲_N(B)‖ ≤ w`, `‖K_N(Λ)‖ ≤ k` and `E = e^{M w}` (`fin_bounds`):

* `|P₀ - 1| ≤ M w E`, `|k⁰| ≤ M w E + k`;
* `|k^{2,𝒲}| ≤ h^{-2} M w E`, `|k^{2,K}| ≤ h^{-2} k`;
* `||Λ| ã_{N,N} - |Λ| ν_N| ≤ ||Λ| ν_N| M w E + h^{-2} (M w E + k)`.

So `𝒲_N = O(ǧ²)` enters only the errors (no localisation of `𝒲_N` is needed): its zero-mode
integral is `O(ǧ²)`.
-/

namespace PtCorr2

noncomputable section

open Finset Grassmann Suscept Step Loc Step2 Step2.LastN

set_option linter.unusedSectionVars false

/-! ### Products -/

section Prod

variable {ι : Type*} [DecidableEq ι]

theorem norm_prod_one_add_le' (s : Finset ι) (x : ι → ℂ) :
    ‖∏ i ∈ s, (1 + x i)‖ ≤ ∏ i ∈ s, (1 + ‖x i‖) := by
  refine (Finset.norm_prod_le _ _).trans (prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => ?_)
  exact (norm_add_le _ _).trans (by rw [norm_one])

theorem norm_prod_one_add_sub_one_le' (s : Finset ι) (x : ι → ℂ) :
    ‖∏ i ∈ s, (1 + x i) - 1‖ ≤ ∏ i ∈ s, (1 + ‖x i‖) - 1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha]
    have e : (1 + x a) * ∏ i ∈ s, (1 + x i) - 1 =
        (∏ i ∈ s, (1 + x i) - 1) + x a * ∏ i ∈ s, (1 + x i) := by ring
    rw [e]
    have h1 := norm_prod_one_add_le' s x
    calc ‖(∏ i ∈ s, (1 + x i) - 1) + x a * ∏ i ∈ s, (1 + x i)‖
        ≤ (∏ i ∈ s, (1 + ‖x i‖) - 1) + ‖x a‖ * ∏ i ∈ s, (1 + ‖x i‖) := by
          refine (norm_add_le _ _).trans (add_le_add ih ?_)
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = (1 + ‖x a‖) * ∏ i ∈ s, (1 + ‖x i‖) - 1 := by ring

theorem prod_one_add_le_exp' (s : Finset ι) {a : ι → ℝ} (ha : ∀ i ∈ s, 0 ≤ a i) :
    ∏ i ∈ s, (1 + a i) ≤ Real.exp (∑ i ∈ s, a i) := by
  rw [Real.exp_sum]
  refine prod_le_prod (fun i hi => by linarith [ha i hi]) fun i _ => ?_
  linarith [Real.add_one_le_exp (a i)]

theorem exp_sub_one_le_mul_exp' {S : ℝ} : Real.exp S - 1 ≤ S * Real.exp S := by
  have h := Real.add_one_le_exp (-S)
  have hp := Real.exp_pos S
  have e : Real.exp (-S) * Real.exp S = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  nlinarith

/-- `|∏(1 + x_i) - 1| ≤ M w e^{M w}` and `|∏(1 + x_i)| ≤ e^{M w}` for `|x_i| ≤ w`, `|s| ≤ M`. -/
theorem prod_bounds (s : Finset ι) (x : ι → ℂ) {w : ℝ} (hw : 0 ≤ w) {M : ℕ} (hM : s.card ≤ M)
    (hx : ∀ i ∈ s, ‖x i‖ ≤ w) :
    ‖∏ i ∈ s, (1 + x i) - 1‖ ≤ M * w * Real.exp (M * w) ∧
      ‖∏ i ∈ s, (1 + x i)‖ ≤ Real.exp (M * w) := by
  have hS : ∑ i ∈ s, ‖x i‖ ≤ M * w := by
    calc ∑ i ∈ s, ‖x i‖ ≤ ∑ _i ∈ s, w := sum_le_sum hx
      _ = s.card * w := by rw [sum_const, nsmul_eq_mul]
      _ ≤ M * w := mul_le_mul_of_nonneg_right (by exact_mod_cast hM) hw
  have hS0 : 0 ≤ ∑ i ∈ s, ‖x i‖ := sum_nonneg fun _ _ => norm_nonneg _
  have hP := prod_one_add_le_exp' s (a := fun i => ‖x i‖) fun _ _ => norm_nonneg _
  have hE : Real.exp (∑ i ∈ s, ‖x i‖) ≤ Real.exp (M * w) := Real.exp_le_exp.2 hS
  refine ⟨(norm_prod_one_add_sub_one_le' s x).trans ?_,
    (norm_prod_one_add_le' s x).trans (hP.trans hE)⟩
  calc ∏ i ∈ s, (1 + ‖x i‖) - 1 ≤ Real.exp (∑ i ∈ s, ‖x i‖) - 1 := by linarith
    _ ≤ (∑ i ∈ s, ‖x i‖) * Real.exp (∑ i ∈ s, ‖x i‖) := exp_sub_one_le_mul_exp'
    _ ≤ M * w * Real.exp (M * w) :=
        mul_le_mul hS hE (Real.exp_pos _).le (by positivity)

end Prod

/-! ### The coefficient bounds -/

variable {d L N : ℕ} [NeZero L]

theorem toReal_le_of {T : ENNReal} {w : ℝ} (hw : 0 ≤ w) (h : T ≤ ENNReal.ofReal w) :
    T.toReal ≤ w :=
  ENNReal.toReal_le_of_le_ofReal hw h

/-- **The bounds of `prop:ZNN` for the final object.** For field scale `h > 0` at any spatial
scale `L^i`, `n_B ≤ M` blocks, `‖𝒲_N(B)‖_{T_i(h)} ≤ w` and `‖K_N(Λ)‖_{T_i(h)} ≤ k`, with
`E = e^{M w}`. -/
theorem fin_bounds {j i : ℕ} {out : LastOut d L N} {h w k : ℝ} {M : ℕ} (hh : 0 < h)
    (hw : 0 ≤ w) (hk : 0 ≤ k) (hM : (blockIdx (d := d) (L := L) (N := N) j).card ≤ M)
    (hW : ∀ b ∈ blockIdx (d := d) (L := L) (N := N) j,
      Tj d (L : ℝ) i h (out.W b : Alg d L N) ≤ ENNReal.ofReal w)
    (hK : Tj d (L : ℝ) i h (out.K : Alg d L N) ≤ ENNReal.ofReal k) :
    ‖P0Fin j out - 1‖ ≤ M * w * Real.exp (M * w) ∧
      ‖k0Fin j out‖ ≤ M * w * Real.exp (M * w) + k ∧
      ‖kW2Fin j out‖ ≤ h⁻¹ ^ 2 * (M * w * Real.exp (M * w)) ∧
      ‖kK2Fin out‖ ≤ h⁻¹ ^ 2 * k ∧
      ‖(Fintype.card (Lam d L N) : ℂ) * aFin j out -
          (Fintype.card (Lam d L N) : ℂ) * out.κ.nu‖ ≤
        ‖(Fintype.card (Lam d L N) : ℂ) * out.κ.nu‖ * (M * w * Real.exp (M * w)) +
          h⁻¹ ^ 2 * (M * w * Real.exp (M * w) + k) := by
  have hL0 : (0 : ℝ) < (L : ℝ) ^ i := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) i
  have hεW : ∀ b ∈ blockIdx (d := d) (L := L) (N := N) j, ‖ε (out.W b : Alg d L N)‖ ≤ w := fun b hb =>
    (abs_eps_le (E := Dir d) (p := pPhi d) hL0 hh _).trans (toReal_le_of hw (hW b hb))
  have hc2W : ∀ b ∈ blockIdx (d := d) (L := L) (N := N) j, ‖Suscept.c2 (out.W b : Alg d L N)‖ ≤ h⁻¹ ^ 2 * w :=
    fun b hb => by
      have := norm_c2_le (E := Dir d) (p := pPhi d) hL0 hh (out.W b : Alg d L N)
      calc _ ≤ _ := this
        _ ≤ w * h⁻¹ ^ 2 := mul_le_mul_of_nonneg_right (toReal_le_of hw (hW b hb)) (by positivity)
        _ = h⁻¹ ^ 2 * w := mul_comm _ _
  have hεK : ‖ε (out.K : Alg d L N)‖ ≤ k :=
    (abs_eps_le (E := Dir d) (p := pPhi d) hL0 hh _).trans (toReal_le_of hk hK)
  have hc2K : ‖kK2Fin out‖ ≤ h⁻¹ ^ 2 * k := by
    have := norm_c2_le (E := Dir d) (p := pPhi d) hL0 hh (out.K : Alg d L N)
    calc _ ≤ _ := this
      _ ≤ k * h⁻¹ ^ 2 := mul_le_mul_of_nonneg_right (toReal_le_of hk hK) (by positivity)
      _ = h⁻¹ ^ 2 * k := mul_comm _ _
  obtain ⟨hP1, -⟩ := prod_bounds _ (fun b => ε (out.W b : Alg d L N)) hw hM hεW
  set E := M * w * Real.exp (M * w) with hEdef
  have hE0 : 0 ≤ E := by positivity
  have hP0 : ‖P0Fin j out - 1‖ ≤ E := hP1
  have hk0 : ‖k0Fin j out‖ ≤ E + k := by
    rw [k0Fin]
    exact (norm_add_le _ _).trans (add_le_add hP0 hεK)
  have hkW : ‖kW2Fin j out‖ ≤ h⁻¹ ^ 2 * E := by
    rw [kW2Fin]
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ b ∈ blockIdx (d := d) (L := L) (N := N) j,
        ‖Suscept.c2 (out.W b : Alg d L N) *
          ∏ k ∈ (blockIdx (d := d) (L := L) (N := N) j).erase b, (1 + ε (out.W k : Alg d L N))‖ ≤
        h⁻¹ ^ 2 * w * Real.exp (M * w) := by
      intro b hb
      have hcard : ((blockIdx (d := d) (L := L) (N := N) j).erase b).card ≤ M :=
        (card_erase_le).trans hM
      obtain ⟨-, hpr⟩ := prod_bounds _ (fun b => ε (out.W b : Alg d L N)) hw hcard
        fun k hk => hεW k (mem_of_mem_erase hk)
      rw [norm_mul]
      exact mul_le_mul (hc2W b hb) hpr (norm_nonneg _) (by positivity)
    calc _ ≤ ∑ _b ∈ blockIdx (d := d) (L := L) (N := N) j, h⁻¹ ^ 2 * w * Real.exp (M * w) :=
          sum_le_sum hterm
      _ = (blockIdx (d := d) (L := L) (N := N) j).card * (h⁻¹ ^ 2 * w * Real.exp (M * w)) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ M * (h⁻¹ ^ 2 * w * Real.exp (M * w)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hM) (by positivity)
      _ = h⁻¹ ^ 2 * E := by rw [hEdef]; ring
  refine ⟨hP0, hk0, hkW, hc2K, ?_⟩
  have hc : (Fintype.card (Lam d L N) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have e : (Fintype.card (Lam d L N) : ℂ) * aFin j out -
      (Fintype.card (Lam d L N) : ℂ) * out.κ.nu =
      (Fintype.card (Lam d L N) : ℂ) * out.κ.nu * (P0Fin j out - 1) -
        (kW2Fin j out + kK2Fin out) := by
    rw [aFin]; field_simp; ring
  rw [e]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul]; exact mul_le_mul_of_nonneg_left hP0 (norm_nonneg _)
  · refine (norm_add_le _ _).trans ?_
    calc ‖kW2Fin j out‖ + ‖kK2Fin out‖ ≤ h⁻¹ ^ 2 * E + h⁻¹ ^ 2 * k := add_le_add hkW hc2K
      _ = h⁻¹ ^ 2 * (E + k) := by ring

end

end PtCorr2
