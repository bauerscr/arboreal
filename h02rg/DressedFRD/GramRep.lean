import DressedFRD.Norm

/-!
# `lem:norm`(ii): the Gram representation

For a symbol `w` (the operator `K(x,y) = k(x - y)`, `k = kern w`) put
* `gF w α x p = conj (σ_α(p) |ŵ(p)|^{1/2} e_p(x))`,
* `gG w β y p = σ_β(-p) sgn(ŵ(p)) |ŵ(p)|^{1/2} e_{-p}(y)`.

Then `∇^α_x ∇^β_y K(x,y) = ⟨gF w α x, gG w β y⟩` with `⟨u, v⟩ = ⨍ conj u · v` (`gram_rep`), and
`‖gF w α x‖² = ⨍ |σ_α|² |ŵ| ≤ L^{-s(d-2+2|α|)} ‖w‖_{(s)}` for `2|α| ≤ q` (`gF_norm_le`), and the
same for `gG` (`gG_norm_le`). So the Gram–Hadamard inequality applies to every
Gram-admissible `K`, positive or not.
-/

namespace DressedFRD

noncomputable section

open Finset Complex FRD Grassmann ComplexConjugate

variable {d n : ℕ} [NeZero n]

/-- `sgn z = z / |z|` (`0` at `0`). -/
def sgn (z : ℂ) : ℂ := z / (‖z‖ : ℂ)

theorem sgn_mul_norm (z : ℂ) : sgn z * (‖z‖ : ℂ) = z := by
  by_cases h : z = 0
  · simp [h, sgn]
  · have : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 h)
    simp [sgn, div_mul_cancel₀ _ this]

theorem norm_sgn_le (z : ℂ) : ‖sgn z‖ ≤ 1 := by
  by_cases h : z = 0
  · simp [h, sgn]
  · have : 0 < ‖z‖ := norm_pos_iff.2 h
    rw [sgn, norm_div, Complex.norm_real, Real.norm_of_nonneg this.le, div_self this.ne']

/-- The complex average `⨍ f`. -/
def avgC (f : Torus d n → ℂ) : ℂ := ((n : ℂ) ^ d)⁻¹ * ∑ m, f m

/-- The left Gram vectors. -/
def gF (w : Sym d n) (α : Dir d → ℕ) (x : Torus d n) (m : Torus d n) : ℂ :=
  conj (sigma α m * (Real.sqrt ‖w m‖ : ℂ) * char m x)

/-- The right Gram vectors. -/
def gG (w : Sym d n) (β : Dir d → ℕ) (y : Torus d n) (m : Torus d n) : ℂ :=
  sigma β (-m) * sgn (w m) * (Real.sqrt ‖w m‖ : ℂ) * char (-m) y

theorem kern_sub_eq (w : Sym d n) (x : Torus d n) :
    (fun y' => kern w (x - y')) = kern (fun m => w (-m) * char (-m) x) := by
  funext y'
  unfold kern
  congr 1
  refine Fintype.sum_equiv (Equiv.neg _) _ _ fun m => ?_
  simp only [Equiv.neg_apply, neg_neg]
  simp only [char_sub_right, char_neg_left, char_neg_right, map_mul, conj_conj]; ring

theorem kern_reindex (v : Sym d n) (y : Torus d n) :
    (fun x' => kern (fun m => v m * char (-m) x') y) =
      kern (fun m => v (-m) * char (-m) y) := by
  funext x'
  unfold kern
  congr 1
  refine Fintype.sum_equiv (Equiv.neg _) _ _ fun m => ?_
  simp only [Equiv.neg_apply, neg_neg]
  ring

/-- The `y`-derivative of `K(x,y) = k(x - y)`, as a function of `x`. -/
theorem dop_y_kern (w : Sym d n) (β : Dir d → ℕ) (y : Torus d n) :
    (fun x' => dop β (fun y' => kern w (x' - y')) y) =
      kern (fun m => sigma β (-m) * w m * char (-m) y) := by
  funext x'
  rw [kern_sub_eq, dop_kern]
  have := congrFun (kern_reindex (fun m => sigma β m * w (-m)) y) x'
  simp only [neg_neg] at this
  rw [show (fun m => sigma β m * (w (-m) * char (-m) x')) =
    (fun m => sigma β m * w (-m) * char (-m) x') by funext m; ring, this]

/-- `lem:norm`(ii): `∇^α_x ∇^β_y K(x,y) = ⟨f_x, g_y⟩`. -/
theorem gram_rep (w : Sym d n) (α β : Dir d → ℕ) (x y : Torus d n) :
    dop α (fun x' => dop β (fun y' => kern w (x' - y')) y) x =
      avgC fun m => conj (gF w α x m) * gG w β y m := by
  rw [dop_y_kern, dop_kern]
  unfold kern avgC
  congr 1
  refine sum_congr rfl fun m _ => ?_
  simp only [gF, gG, conj_conj]
  have hs : ((Real.sqrt ‖w m‖ : ℝ) : ℂ) * (Real.sqrt ‖w m‖ : ℂ) = (‖w m‖ : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (norm_nonneg _)]
  calc sigma α m * (sigma β (-m) * w m * char (-m) y) * char m x
      = sigma α m * sigma β (-m) * (sgn (w m) * (‖w m‖ : ℂ)) * char m x * char (-m) y := by
        rw [sgn_mul_norm]; ring
    _ = _ := by rw [← hs]; ring

theorem norm_char_neg_sub_one (m e : Torus d n) : ‖char (-m) e - 1‖ = ‖char m e - 1‖ := by
  rw [char_neg_left, ← Complex.norm_conj, map_sub, conj_conj, map_one]

theorem norm_sigma_neg (β : Dir d → ℕ) (m : Torus d n) : ‖sigma β (-m)‖ = ‖sigma β m‖ := by
  simp only [sigma, norm_prod, norm_pow, norm_char_neg_sub_one]

theorem norm_sigma_sq (α : Dir d → ℕ) (m : Torus d n) : ‖sigma α m‖ ^ 2 = ‖sigma (2 • α) m‖ := by
  simp only [sigma, norm_prod, norm_pow, Pi.smul_apply, smul_eq_mul]
  rw [← prod_pow]
  refine prod_congr rfl fun e _ => ?_
  rw [← pow_mul, mul_comm]

theorem mabs_two_smul (α : Dir d → ℕ) : Grassmann.mabs (2 • α) = 2 * Grassmann.mabs α := by
  unfold Grassmann.mabs
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]

theorem norm_char (m x : Torus d n) : ‖char m x‖ = 1 := by
  unfold char
  rw [norm_prod]
  exact prod_eq_one fun i _ => by
    simpa using (ZMod.stdAddChar (N := n)).norm_apply (co m i * co x i)

variable {L : ℝ} {q s : ℕ}

theorem avg_sq_sigma_le (hL : 0 < L) {α : Dir d → ℕ} (hα : 2 * Grassmann.mabs α ≤ q)
    (w : Sym d n) :
    avg (fun m => ‖sigma α m‖ ^ 2 * ‖w m‖) ≤
      L ^ (-((s : ℝ) * ((d : ℝ) - 2 + 2 * Grassmann.mabs α))) * snorm L q s w := by
  have h := le_snorm (L := L) (q := q) (s := s) (α := 2 • α) (by rw [mabs_two_smul]; exact hα) w
  have hw : wgt d L s (2 • α) = L ^ ((s : ℝ) * ((d : ℝ) - 2 + 2 * Grassmann.mabs α)) := by
    unfold wgt; rw [mabs_two_smul]; push_cast; rfl
  rw [hw] at h
  have hp : 0 < L ^ ((s : ℝ) * ((d : ℝ) - 2 + 2 * Grassmann.mabs α)) := Real.rpow_pos_of_pos hL _
  have hm : avg (fun m => ‖sigma α m‖ ^ 2 * ‖w m‖) = mom (2 • α) w := by
    unfold mom; congr 1; funext m; rw [norm_sigma_sq]
  rw [hm, Real.rpow_neg hL.le, le_inv_mul_iff₀ hp]; exact h

/-- `‖f_x‖² = ⨍ |σ_α|² |ŵ| ≤ L^{-s(d-2+2|α|)} ‖w‖_{(s)}`. -/
theorem gF_norm_le (hL : 0 < L) {α : Dir d → ℕ} (hα : 2 * Grassmann.mabs α ≤ q)
    (w : Sym d n) (x : Torus d n) :
    avg (fun m => ‖gF w α x m‖ ^ 2) ≤
      L ^ (-((s : ℝ) * ((d : ℝ) - 2 + 2 * Grassmann.mabs α))) * snorm L q s w := by
  refine le_trans (le_of_eq ?_) (avg_sq_sigma_le hL hα w)
  congr 1; funext m
  rw [gF, Complex.norm_conj, norm_mul, norm_mul, norm_char, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (norm_nonneg _)]

/-- `‖g_y‖² ≤ L^{-s(d-2+2|β|)} ‖w‖_{(s)}`. -/
theorem gG_norm_le (hL : 0 < L) {β : Dir d → ℕ} (hβ : 2 * Grassmann.mabs β ≤ q)
    (w : Sym d n) (y : Torus d n) :
    avg (fun m => ‖gG w β y m‖ ^ 2) ≤
      L ^ (-((s : ℝ) * ((d : ℝ) - 2 + 2 * Grassmann.mabs β))) * snorm L q s w := by
  refine le_trans (avg_mono fun m => ?_) (avg_sq_sigma_le hL hβ w)
  rw [gG, norm_mul, norm_mul, norm_mul, norm_char, mul_one, norm_sigma_neg, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have h1 := norm_sgn_le (w m)
  have h0 := norm_nonneg (sgn (w m))
  have hs := Real.sq_sqrt (norm_nonneg (w m))
  have hσ := norm_nonneg (sigma β m)
  calc (‖sigma β m‖ * ‖sgn (w m)‖ * Real.sqrt ‖w m‖) ^ 2
      = ‖sigma β m‖ ^ 2 * ‖sgn (w m)‖ ^ 2 * ‖w m‖ := by rw [mul_pow, mul_pow, hs]
    _ ≤ ‖sigma β m‖ ^ 2 * 1 * ‖w m‖ := by
        gcongr
        exact pow_le_one₀ h0 h1
    _ = _ := by ring

theorem norm_sigma_mul (α β : Dir d → ℕ) (m : Torus d n) :
    ‖sigma α m‖ * ‖sigma β m‖ = ‖sigma (α + β) m‖ := by
  simp only [sigma, Pi.add_apply, pow_add, prod_mul_distrib, norm_mul, norm_prod, norm_pow]

theorem mabs_add (α β : Dir d → ℕ) :
    Grassmann.mabs (α + β) = Grassmann.mabs α + Grassmann.mabs β := by
  unfold Grassmann.mabs; simp only [Pi.add_apply, sum_add_distrib]

/-- `lem:norm`(i) for the two-point function:
`|∇^α_x ∇^β_y K(x,y)| ≤ L^{-s(d-2+|α|+|β|)} ‖K‖_{(s)}` for `|α| + |β| ≤ q`. -/
theorem norm_dop2_le (hL : 0 < L) {α β : Dir d → ℕ}
    (hαβ : Grassmann.mabs α + Grassmann.mabs β ≤ q) (w : Sym d n) (x y : Torus d n) :
    ‖dop α (fun x' => dop β (fun y' => kern w (x' - y')) y) x‖ ≤
      L ^ (-((s : ℝ) * ((d : ℝ) - 2 + Grassmann.mabs α + Grassmann.mabs β))) * snorm L q s w := by
  rw [dop_y_kern, dop_kern]
  refine (norm_kern_le_avg _ x).trans ?_
  have h := le_snorm (L := L) (q := q) (s := s) (α := α + β) (by rw [mabs_add]; exact hαβ) w
  have hw : wgt d L s (α + β) =
      L ^ ((s : ℝ) * ((d : ℝ) - 2 + Grassmann.mabs α + Grassmann.mabs β)) := by
    unfold wgt; rw [mabs_add]; push_cast; ring_nf
  rw [hw] at h
  have hp := Real.rpow_pos_of_pos hL ((s : ℝ) * ((d : ℝ) - 2 + Grassmann.mabs α + Grassmann.mabs β))
  have hm : (avg fun m => ‖sigma α m * (sigma β (-m) * w m * char (-m) y)‖) = mom (α + β) w := by
    unfold mom; congr 1; funext m
    rw [norm_mul, norm_mul, norm_mul, norm_char, mul_one, norm_sigma_neg, ← mul_assoc,
      norm_sigma_mul]
  rw [hm, Real.rpow_neg hL.le, le_inv_mul_iff₀ hp]; exact h

end

end DressedFRD
