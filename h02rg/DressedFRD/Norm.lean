import DressedFRD.Symbol

/-!
# The Fourier moment norms `‖K‖_{(s)}` (`e:norm`, `lem:norm`)

`snorm L q s w = max_{|α| ≤ q} L^{s(d-2+|α|)} ⨍ |σ_α| |w|`.

* `norm_dop_kern_le` is `lem:norm`(i) for one-point derivatives: `|∇^α k(x)| ≤ L^{-s(d-2+|α|)} ‖w‖_{(s)}`.
* `snorm_mul_le` is `lem:norm`(iii): `‖w w'‖_{(s)} ≤ sup|w'| ‖w‖_{(s)}`.
* `snorm_mono_scale` is `lem:norm`(iv): `‖w‖_{(s')} ≤ L^{(s'-s)(d-2+q)} ‖w‖_{(s)}`.
* `norm_kern_A_le` bounds the kernel of `(λ + m²) w` (used in `lem:letters`(b)).
-/

namespace DressedFRD

noncomputable section

open Finset Complex FRD Grassmann ComplexConjugate

variable {d n : ℕ} [NeZero n]

/-- Multi-indices `α : 𝓔_d → ℕ` with `|α| ≤ q`. -/
def alphas (d q : ℕ) : Finset (Dir d → ℕ) :=
  (Fintype.piFinset fun _ => range (q + 1)).filter fun α => Grassmann.mabs α ≤ q

theorem mem_alphas {q : ℕ} {α : Dir d → ℕ} : α ∈ alphas d q ↔ Grassmann.mabs α ≤ q := by
  constructor
  · intro h; exact (mem_filter.1 h).2
  · intro h
    refine mem_filter.2 ⟨Fintype.mem_piFinset.2 fun e => mem_range.2 ?_, h⟩
    have : α e ≤ Grassmann.mabs α :=
      single_le_sum (f := α) (fun _ _ => Nat.zero_le _) (mem_univ e)
    omega

theorem zero_mem_alphas (q : ℕ) : (0 : Dir d → ℕ) ∈ alphas d q :=
  mem_alphas.2 (by simp [Grassmann.mabs])

/-- The average `⨍ f = |Λ|^{-1} ∑ f`. -/
def avg (f : Torus d n → ℝ) : ℝ := ((n : ℝ) ^ d)⁻¹ * ∑ m, f m

theorem avg_nonneg {f : Torus d n → ℝ} (hf : ∀ m, 0 ≤ f m) : 0 ≤ avg f :=
  mul_nonneg (by positivity) (sum_nonneg fun m _ => hf m)

theorem avg_mono {f g : Torus d n → ℝ} (h : ∀ m, f m ≤ g m) : avg f ≤ avg g :=
  mul_le_mul_of_nonneg_left (sum_le_sum fun m _ => h m) (by positivity)

theorem avg_add (f g : Torus d n → ℝ) : avg (f + g) = avg f + avg g := by
  simp [avg, sum_add_distrib, mul_add]

theorem avg_smul (c : ℝ) (f : Torus d n → ℝ) : avg (fun m => c * f m) = c * avg f := by
  simp only [avg, ← mul_sum]; ring

/-- The moment `⨍ |σ_α| |w|`. -/
def mom (α : Dir d → ℕ) (w : Sym d n) : ℝ := avg fun m => ‖sigma α m‖ * ‖w m‖

theorem mom_nonneg (α : Dir d → ℕ) (w : Sym d n) : 0 ≤ mom α w :=
  avg_nonneg fun m => by positivity

/-- The weight `L^{s(d-2+|α|)}`. -/
def wgt (d : ℕ) (L : ℝ) (s : ℕ) (α : Dir d → ℕ) : ℝ :=
  L ^ ((s : ℝ) * ((d : ℝ) - 2 + Grassmann.mabs α))

theorem wgt_pos {L : ℝ} (hL : 0 < L) (s : ℕ) (α : Dir d → ℕ) : 0 < wgt d L s α :=
  Real.rpow_pos_of_pos hL _

/-- The norm `‖w‖_{(s)} = max_{|α| ≤ q} L^{s(d-2+|α|)} ⨍ |σ_α| |w|` (`e:norm`). -/
def snorm (L : ℝ) (q s : ℕ) (w : Sym d n) : ℝ :=
  (alphas d q).sup' ⟨0, zero_mem_alphas q⟩ fun α => wgt d L s α * mom α w

variable {L : ℝ} {q s : ℕ}

theorem le_snorm {α : Dir d → ℕ} (hα : Grassmann.mabs α ≤ q) (w : Sym d n) :
    wgt d L s α * mom α w ≤ snorm L q s w :=
  le_sup' (fun α => wgt d L s α * mom α w) (mem_alphas.2 hα)

theorem snorm_le_iff {w : Sym d n} {B : ℝ} :
    snorm L q s w ≤ B ↔ ∀ α, Grassmann.mabs α ≤ q → wgt d L s α * mom α w ≤ B := by
  rw [snorm, sup'_le_iff]
  exact ⟨fun h α hα => h α (mem_alphas.2 hα), fun h α hα => h α (mem_alphas.1 hα)⟩

theorem snorm_nonneg (hL : 0 < L) (w : Sym d n) : 0 ≤ snorm L q s w :=
  (mul_nonneg (wgt_pos hL s 0).le (mom_nonneg 0 w)).trans (le_snorm (by simp [Grassmann.mabs]) w)

/-- `lem:norm`(i), one-point form: `|∇^α k(x)| ≤ L^{-s(d-2+|α|)} ‖w‖_{(s)}`. -/
theorem norm_dop_kern_le (hL : 0 < L) {α : Dir d → ℕ} (hα : Grassmann.mabs α ≤ q) (w : Sym d n)
    (x : Torus d n) : ‖dop α (kern w) x‖ ≤ (wgt d L s α)⁻¹ * snorm L q s w := by
  rw [dop_kern, le_inv_mul_iff₀ (wgt_pos hL s α)]
  refine le_trans ?_ (le_snorm hα w)
  refine mul_le_mul_of_nonneg_left ?_ (wgt_pos hL s α).le
  unfold kern mom avg
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum_le_sum fun m _ => ?_))
    (by positivity)
  rw [norm_mul, norm_mul, norm_char, mul_one]

theorem norm_kern_le (hL : 0 < L) (w : Sym d n) (x : Torus d n) :
    ‖kern w x‖ ≤ (wgt d L s 0)⁻¹ * snorm L q s w := by
  have := norm_dop_kern_le (q := q) (s := s) hL (α := 0) (by simp [Grassmann.mabs]) w x
  have h0 : dop (0 : Dir d → ℕ) (kern w) x = kern w x := by
    rw [dop_kern]; simp [sigma_zero]
  rwa [h0] at this

/-- `lem:norm`(iii): `‖w w'‖_{(s)} ≤ B ‖w‖_{(s)}` if `|w'| ≤ B`. -/
theorem snorm_mul_le (hL : 0 < L) (w w' : Sym d n) {B : ℝ} (hB : ∀ m, ‖w' m‖ ≤ B) :
    snorm L q s (w * w') ≤ B * snorm L q s w := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  refine snorm_le_iff.2 fun α hα => ?_
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (le_snorm hα w) hB0)
  rw [mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ (wgt_pos hL s α).le
  unfold mom
  rw [← avg_smul]
  refine avg_mono fun m => ?_
  simp only [Pi.mul_apply, norm_mul]
  have := hB m
  nlinarith [norm_nonneg (sigma α m), norm_nonneg (w m), norm_nonneg (w' m),
    mul_nonneg (norm_nonneg (sigma α m)) (norm_nonneg (w m))]

theorem mom_add_le (α : Dir d → ℕ) (w w' : Sym d n) : mom α (w + w') ≤ mom α w + mom α w' := by
  unfold mom
  rw [← avg_add]
  refine avg_mono fun m => ?_
  simp only [Pi.add_apply]
  nlinarith [norm_add_le (w m) (w' m), norm_nonneg (sigma α m)]

theorem snorm_add_le (hL : 0 < L) (w w' : Sym d n) :
    snorm L q s (w + w') ≤ snorm L q s w + snorm L q s w' := by
  refine snorm_le_iff.2 fun α hα => ?_
  refine le_trans ?_ (add_le_add (le_snorm hα w) (le_snorm hα w'))
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (mom_add_le α w w') (wgt_pos hL s α).le

theorem mom_smul (α : Dir d → ℕ) (c : ℂ) (w : Sym d n) : mom α (c • w) = ‖c‖ * mom α w := by
  unfold mom
  rw [← avg_smul]
  congr 1; funext m
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul]; ring

theorem snorm_smul (hL : 0 < L) (c : ℂ) (w : Sym d n) :
    snorm L q s (c • w) = ‖c‖ * snorm L q s w := by
  apply le_antisymm
  · refine snorm_le_iff.2 fun α hα => ?_
    rw [mom_smul, mul_left_comm]
    exact mul_le_mul_of_nonneg_left (le_snorm hα w) (norm_nonneg c)
  · by_cases hc : c = 0
    · subst hc; simp [snorm_nonneg hL]
    · have hc' : 0 < ‖c‖ := norm_pos_iff.2 hc
      rw [← le_div_iff₀' hc']
      refine snorm_le_iff.2 fun α hα => ?_
      rw [le_div_iff₀' hc']
      have := le_snorm (L := L) (s := s) hα (c • w)
      rw [mom_smul] at this
      linarith [this]

theorem snorm_neg (hL : 0 < L) (w : Sym d n) : snorm L q s (-w) = snorm L q s w := by
  have := snorm_smul (q := q) (s := s) hL (-1) w
  simpa using this

theorem snorm_sub_le (hL : 0 < L) (w w' : Sym d n) :
    snorm L q s (w - w') ≤ snorm L q s w + snorm L q s w' := by
  rw [sub_eq_add_neg]
  exact (snorm_add_le hL _ _).trans (by rw [snorm_neg hL])

theorem snorm_sum_le (hL : 0 < L) {ι : Type*} (t : Finset ι) (w : ι → Sym d n) :
    snorm L q s (∑ i ∈ t, w i) ≤ ∑ i ∈ t, snorm L q s (w i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [sum_empty]
    refine le_of_eq ?_
    have := snorm_smul (q := q) (s := s) hL 0 (0 : Sym d n)
    simpa using this
  | insert i t hi ih =>
    rw [sum_insert hi, sum_insert hi]
    exact (snorm_add_le hL _ _).trans (add_le_add_right ih _)

/-- `lem:norm`(iv): `‖w‖_{(s')} ≤ L^{(s'-s)(d-2+q)} ‖w‖_{(s)}` for `s ≤ s'`, `L ≥ 1`, `d ≥ 2`. -/
theorem snorm_mono_scale (hd : 2 ≤ d) (hL : 1 ≤ L) {s s' : ℕ} (hss : s ≤ s') (w : Sym d n) :
    snorm L q s' w ≤ L ^ (((s' : ℝ) - s) * ((d : ℝ) - 2 + q)) * snorm L q s w := by
  have hL0 : 0 < L := by linarith
  refine snorm_le_iff.2 fun α hα => ?_
  have hw : wgt d L s' α ≤ L ^ (((s' : ℝ) - s) * ((d : ℝ) - 2 + q)) * wgt d L s α := by
    unfold wgt
    rw [← Real.rpow_add hL0]
    refine Real.rpow_le_rpow_of_exponent_le hL ?_
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have hq : (Grassmann.mabs α : ℝ) ≤ q := by exact_mod_cast hα
    have hs : (s : ℝ) ≤ s' := by exact_mod_cast hss
    nlinarith [hs, hq, hd', (Nat.cast_nonneg (Grassmann.mabs α) : (0 : ℝ) ≤ _)]
  calc wgt d L s' α * mom α w
      ≤ (L ^ (((s' : ℝ) - s) * ((d : ℝ) - 2 + q)) * wgt d L s α) * mom α w :=
        mul_le_mul_of_nonneg_right hw (mom_nonneg α w)
    _ = L ^ (((s' : ℝ) - s) * ((d : ℝ) - 2 + q)) * (wgt d L s α * mom α w) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_snorm hα w) (by positivity)

/-! ### The Laplacian in terms of second derivatives -/

/-- `λ(p) = ∑_i |e^{ip_i} - 1|^2`. -/
theorem lam_eq_sum (m : Torus d n) :
    (lam m : ℝ) = ∑ i : Fin d, ‖char m (dirVec (Sum.inl i)) - 1‖ ^ 2 := by
  unfold lam
  refine sum_congr rfl fun i _ => ?_
  rw [dirVec_inl, char_unitT, norm_stdAddChar_sub_one_sq]; rfl

/-- The multi-index `2 δ_{e_i}`. -/
def two (i : Fin d) : Dir d → ℕ := Pi.single (Sum.inl i) 2

theorem mabs_two (i : Fin d) : Grassmann.mabs (two i) = 2 := by
  simp [Grassmann.mabs, two]

theorem norm_sigma_two (i : Fin d) (m : Torus d n) :
    ‖sigma (two i) m‖ = ‖char m (dirVec (Sum.inl i)) - 1‖ ^ 2 := by
  unfold sigma two
  rw [prod_eq_single (Sum.inl i) (fun e _ he => by simp [Pi.single_apply, he]) (by simp)]
  simp [norm_pow]

theorem lam_eq_sum_sigma (m : Torus d n) : (lam m : ℝ) = ∑ i : Fin d, ‖sigma (two i) m‖ := by
  rw [lam_eq_sum]; simp only [norm_sigma_two]

theorem lam_nonneg' (m : Torus d n) : 0 ≤ lam m := by
  rw [lam_eq_sum]; positivity

theorem norm_kern_le_avg (v : Sym d n) (x : Torus d n) : ‖kern v x‖ ≤ avg fun m => ‖v m‖ := by
  unfold kern avg
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum_le_sum fun m _ => ?_))
    (by positivity)
  rw [norm_mul, norm_char, mul_one]

theorem mom_le (hL : 0 < L) {α : Dir d → ℕ} (hα : Grassmann.mabs α ≤ q) (w : Sym d n) :
    mom α w ≤ (wgt d L s α)⁻¹ * snorm L q s w := by
  rw [le_inv_mul_iff₀ (wgt_pos hL s α)]; exact le_snorm hα w

theorem wgt_zero (L : ℝ) (s : ℕ) : wgt d L s 0 = L ^ ((s : ℝ) * ((d : ℝ) - 2)) := by
  simp [wgt, Grassmann.mabs]

theorem wgt_two (L : ℝ) (s : ℕ) (i : Fin d) : wgt d L s (two i) = L ^ ((s : ℝ) * d) := by
  rw [wgt, mabs_two]; push_cast; ring_nf

theorem mom_zero (w : Sym d n) : mom 0 w = avg fun m => ‖w m‖ := by
  simp [mom, sigma_zero]

/-- The kernel of `(λ + μ) w`: `|k(x)| ≤ (d L^{-s d} + μ L^{-s(d-2)}) ‖w‖_{(s)}`, `q ≥ 2`. -/
theorem norm_kern_A_le (hL : 0 < L) (hq : 2 ≤ q) {μ : ℝ} (hμ : 0 ≤ μ) (w : Sym d n)
    (x : Torus d n) :
    ‖kern (fun m => ((lam m + μ : ℝ) : ℂ) * w m) x‖ ≤
      (d * (L ^ ((s : ℝ) * d))⁻¹ + μ * (L ^ ((s : ℝ) * ((d : ℝ) - 2)))⁻¹) * snorm L q s w := by
  refine (norm_kern_le_avg _ x).trans ?_
  have e : (fun m => ‖((lam m + μ : ℝ) : ℂ) * w m‖) =
      (fun m => ∑ i : Fin d, ‖sigma (two i) m‖ * ‖w m‖) + fun m => μ * ‖w m‖ := by
    funext m
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (add_nonneg (lam_nonneg' m) hμ),
      lam_eq_sum_sigma, Pi.add_apply, add_mul, sum_mul]
  rw [e, avg_add, avg_smul, add_mul]
  refine add_le_add ?_ ?_
  · have : (avg fun m => ∑ i : Fin d, ‖sigma (two i) m‖ * ‖w m‖) = ∑ i : Fin d, mom (two i) w := by
      simp only [avg, mom, mul_sum]; rw [sum_comm]
    rw [this]
    calc ∑ i : Fin d, mom (two i) w ≤ ∑ _i : Fin d, (L ^ ((s : ℝ) * d))⁻¹ * snorm L q s w :=
          sum_le_sum fun i _ => by
            have := mom_le (s := s) hL (α := two i) ((mabs_two i).le.trans hq) w
            rwa [wgt_two] at this
      _ = _ := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  · rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hμ
    have := mom_le (q := q) (s := s) hL (α := 0) (by simp [Grassmann.mabs]) w
    rwa [mom_zero, wgt_zero] at this

end

end DressedFRD
