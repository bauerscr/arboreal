import DressedFRD.Main

/-!
# The step bounds of `lem:sum` for arbitrary tails

The word bounds `word_tail_bound`, `words_k_bound`, `scales_bound_all`, `norm_zp_eps_le` and
`word_sum_le` are stated for the actual tails `D.tails j`. Here they are restated, with the same
proofs, for an arbitrary tail family `R : ℕ → Sym d n` satisfying the range bound `RangeR`.
The weighted size of the tails is `SjR = ∑_r W_{r-j} |Z_j| ‖R_r‖_{(r-1)}`.
This is used for the Lipschitz bound of the step map in the tails (`DressedFRD/LipDecay.lean`).
-/

namespace DressedFRD

noncomputable section

open Finset Grassmann FRD

variable {d n : ℕ} [NeZero n]

namespace Data

variable {D : Data d n} {q : ℕ} {c₂ θ : ℝ} {j : ℕ} {R : ℕ → Sym d n}

/-- The range bound for a tail family at time `j`. -/
def RangeR (D : Data d n) (j : ℕ) (R : ℕ → Sym d n) : Prop :=
  ∀ r, j < r → r < D.N → 2 * rng (R r) < D.L ^ r

/-- `tWR r = |Z_j| ‖R_r‖_{(r-1)}`. -/
def tWR (D : Data d n) (q j : ℕ) (R : ℕ → Sym d n) (r : ℕ) : ℝ := ‖D.Z j‖ * snorm D.L q (r - 1) (R r)

theorem tWR_nonneg (hL : 1 ≤ D.L) (q j : ℕ) (R : ℕ → Sym d n) (r : ℕ) : 0 ≤ D.tWR q j R r :=
  mul_nonneg (norm_nonneg _) (snorm_nonneg (by exact_mod_cast (by omega : 0 < D.L)) _)

/-- The tail weight at the distinguished position. -/
def tailWR (D : Data d n) (q : ℕ) (θ : ℝ) (j : ℕ) (R : ℕ → Sym d n) : Option ℕ → ℝ
  | none => 0
  | some r => θ ^ (-(2 : ℝ) / 256) * Wt θ D.L (r - j) * D.tWR q j R r

/-- `𝒮_j` for the tails `R`. -/
def SjR (D : Data d n) (q : ℕ) (θ : ℝ) (j : ℕ) (R : ℕ → Sym d n) : ℝ :=
  ∑ r ∈ Ioc j D.N, Wt θ D.L (r - j) * D.tWR q j R r

/-- `σ₀` for the tails `R`. -/
def sig0R (D : Data d n) (q : ℕ) (θ : ℝ) (j : ℕ) (R : ℕ → Sym d n) : ℝ :=
  θ ^ (-(3 : ℝ) / 256) + θ ^ (-(2 : ℝ) / 256) * Crho d D.L * D.SjR q θ j R

theorem SjR_nonneg (hθ : 0 < θ) (hL : 1 ≤ D.L) : 0 ≤ D.SjR q θ j R :=
  sum_nonneg fun r _ => mul_nonneg (Wt_pos hθ _ _).le (tWR_nonneg hL q j R r)

theorem norm_rho_leR (h : StdHyp D.L D.N D.msq D.C) (hL : 3 ≤ D.L) (hn : n = D.L ^ D.N)
    {q : ℕ} (hq : 2 ≤ q) (hmsq : D.msq ≤ (D.L : ℝ) ^ (-(2 * ((D.N : ℝ) - 1))))
    {j : ℕ} (hR : D.RangeR j R) {r : ℕ} (hr : j < r ∧ r ≤ D.N) (m : Torus d n) :
    ‖((D.Z j • (Asym D.msq * R r) : Sym d n)) m‖ ≤
      Crho d D.L * (‖D.Z j‖ * snorm D.L q (r - 1) (R r)) := by
  have hL0 : (0 : ℝ) < D.L := by exact_mod_cast (by omega : 0 < D.L)
  have hL1 : (1 : ℝ) ≤ D.L := by exact_mod_cast (by omega : 1 ≤ D.L)
  have hmsq0 := h.msq_pos.le
  -- kernel bound
  have hk : ∀ x, ‖kern (Asym D.msq * R r) x‖ ≤ (d + 1) * (D.L : ℝ) ^ (-(((r - 1 : ℕ) : ℝ) * d)) *
      snorm D.L q (r - 1) (R r) := by
    intro x
    have := norm_kern_A_le (s := r - 1) hL0 hq hmsq0 (R r) x
    have hv : (fun m => ((lam m + D.msq : ℝ) : ℂ) * R r m) =
        Asym D.msq * R r := by funext m; rfl
    rw [hv] at this
    refine this.trans (mul_le_mul_of_nonneg_right ?_ (snorm_nonneg hL0 (R r)))
    have e1 : (((D.L : ℝ) ^ (((r - 1 : ℕ) : ℝ) * d))⁻¹) =
        (D.L : ℝ) ^ (-(((r - 1 : ℕ) : ℝ) * d)) := by rw [Real.rpow_neg hL0.le]
    have e2 : D.msq * ((D.L : ℝ) ^ (((r - 1 : ℕ) : ℝ) * ((d : ℝ) - 2)))⁻¹ ≤
        (D.L : ℝ) ^ (-(((r - 1 : ℕ) : ℝ) * d)) := by
      rw [← Real.rpow_neg hL0.le]
      have hr1 : ((r - 1 : ℕ) : ℝ) ≤ (D.N : ℝ) - 1 := by
        have : r - 1 ≤ D.N - 1 := by omega
        have h2 : ((D.N - 1 : ℕ) : ℝ) = (D.N : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]; simp
        rw [← h2]; exact_mod_cast this
      calc D.msq * (D.L : ℝ) ^ (-(((r - 1 : ℕ) : ℝ) * ((d : ℝ) - 2)))
          ≤ (D.L : ℝ) ^ (-(2 * ((D.N : ℝ) - 1))) *
              (D.L : ℝ) ^ (-(((r - 1 : ℕ) : ℝ) * ((d : ℝ) - 2))) :=
            mul_le_mul_of_nonneg_right hmsq (by positivity)
        _ = (D.L : ℝ) ^ (-(2 * ((D.N : ℝ) - 1)) + -(((r - 1 : ℕ) : ℝ) * ((d : ℝ) - 2))) :=
            (Real.rpow_add hL0 _ _).symm
        _ ≤ (D.L : ℝ) ^ (-(((r - 1 : ℕ) : ℝ) * d)) :=
            Real.rpow_le_rpow_of_exponent_le hL1 (by nlinarith)
    rw [e1]
    have : (d : ℝ) * (D.L : ℝ) ^ (-(((r - 1 : ℕ) : ℝ) * d)) + D.msq *
        ((D.L : ℝ) ^ (((r - 1 : ℕ) : ℝ) * ((d : ℝ) - 2)))⁻¹ ≤
        (d + 1) * (D.L : ℝ) ^ (-(((r - 1 : ℕ) : ℝ) * d)) := by linarith
    exact this
  -- support count
  have hcount : ((2 * rng (Asym D.msq * R r) + 1 : ℕ) : ℝ) ≤ 2 * (D.L : ℝ) ^ r := by
    have h1 := rng_Asym_mul_le D.msq (R r)
    have h2 : 2 * rng (R r) ≤ D.L ^ r := by
      by_cases hrN : r < D.N
      · have := hR r hr.1 hrN; omega
      · have : r = D.N := by omega
        rw [this, ← hn]; exact two_rng_le _
    have h3 : 3 ≤ D.L ^ r := le_trans hL (Nat.le_self_pow (by omega) _)
    have : 2 * rng (Asym D.msq * R r) + 1 ≤ 2 * D.L ^ r := by omega
    exact_mod_cast this
  have hsum := sum_kern_le (Asym D.msq * R r) hk
  have hv := norm_le_sum_kern (Asym D.msq * R r) m
  have hpow : ((2 * rng (Asym D.msq * R r) + 1 : ℕ) : ℝ) ^ d * ((D.L : ℝ) ^ (-(((r - 1 : ℕ) : ℝ) * d))) ≤
      (2 * D.L : ℝ) ^ d := by
    calc ((2 * rng (Asym D.msq * R r) + 1 : ℕ) : ℝ) ^ d * ((D.L : ℝ) ^ (-(((r - 1 : ℕ) : ℝ) * d)))
        ≤ (2 * (D.L : ℝ) ^ r) ^ d * ((D.L : ℝ) ^ (-(((r - 1 : ℕ) : ℝ) * d))) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hcount d) (by positivity)
      _ = (2 * D.L : ℝ) ^ d * ((D.L : ℝ) ^ ((r : ℝ) * d - 1 * d) *
            (D.L : ℝ) ^ (-(((r - 1 : ℕ) : ℝ) * d))) := by
          rw [mul_pow, mul_pow, ← Real.rpow_natCast ((D.L : ℝ) ^ r), ← Real.rpow_natCast (D.L : ℝ) r,
            ← Real.rpow_mul hL0.le, ← Real.rpow_natCast (D.L : ℝ) d]
          rw [show (r : ℝ) * d - 1 * d = (r : ℝ) * d - d by ring, Real.rpow_sub hL0]
          field_simp
      _ = (2 * D.L : ℝ) ^ d := by
          rw [← Real.rpow_add hL0]
          have : (r : ℝ) * d - 1 * d + -(((r - 1 : ℕ) : ℝ) * d) = 0 := by
            rw [Nat.cast_sub (by omega)]; push_cast; ring
          rw [this, Real.rpow_zero, mul_one]
  have hfin : ‖((Asym D.msq * R r : Sym d n)) m‖ ≤ (d + 1) * (2 * D.L : ℝ) ^ d * snorm D.L q (r - 1) (R r) := by
    calc ‖((Asym D.msq * R r : Sym d n)) m‖ ≤ ((2 * rng (Asym D.msq * R r) + 1 : ℕ) : ℝ) ^ d * ((d + 1) * (D.L : ℝ) ^ (-(((r - 1 : ℕ) : ℝ) * d)) *
          snorm D.L q (r - 1) (R r)) := by
          refine hv.trans (hsum.trans (le_of_eq ?_)); push_cast; ring
      _ = (d + 1) * (((2 * rng (Asym D.msq * R r) + 1 : ℕ) : ℝ) ^ d * (D.L : ℝ) ^ (-(((r - 1 : ℕ) : ℝ) * d))) *
          snorm D.L q (r - 1) (R r) := by ring
      _ ≤ (d + 1) * (2 * D.L : ℝ) ^ d * snorm D.L q (r - 1) (R r) := by
          refine mul_le_mul_of_nonneg_right ?_ (snorm_nonneg hL0 (R r))
          exact mul_le_mul_of_nonneg_left hpow (by positivity)
  rw [Pi.smul_apply, smul_eq_mul, norm_mul, Crho]
  calc ‖D.Z j‖ * ‖((Asym D.msq * R r : Sym d n)) m‖ ≤ ‖D.Z j‖ * ((d + 1) * (2 * D.L : ℝ) ^ d * snorm D.L q (r - 1) (R r)) :=
        mul_le_mul_of_nonneg_left hfin (norm_nonneg _)
    _ = _ := by ring


theorem rho_boundR (H : D.StepHyp q c₂ θ j) (hR : D.RangeR j R) {r : ℕ} (hr : j < r ∧ r ≤ D.N) (m : Torus d n) :
    ‖((D.Z j • (Asym D.msq * R r) : Sym d n)) m‖ ≤ Crho d D.L * D.tWR q j R r :=
  norm_rho_leR H.std (by have := H.hL; omega) H.hn H.hq H.hmsq hR hr m


/-- `W_{s-1-j} |ζ'|^{k+1} ‖O_w‖_{(s-1)}` for a word with a maximal tail letter at `p`. -/
theorem word_tail_boundR (H : D.StepHyp q c₂ θ j) (hR : D.RangeR j R) {η : ℝ} (hη : 0 ≤ η)
    (hη2 : η ^ 2 = ‖D.zp j‖) (hηc : η ≤ (D.L : ℝ) ^ (-cexp d q)) {k : ℕ}
    {w : Fin (k + 2) → Option ℕ} (hw : w ∈ words j D.N k) {p : Fin (k + 2)} {r : ℕ}
    (hp : w p = some r) (hmax : ∀ i r', w i = some r' → r' ≤ r) :
    Wt θ D.L (scale D.L j D.N (rbar (D.rbV j) w) - 1 - j) * ‖D.zp j‖ ^ (k + 1) *
        snorm D.L q (scale D.L j D.N (rbar (D.rbV j) w) - 1) (wordVal (D.letV j R) w) ≤
      ‖D.zp j‖ * (D.L : ℝ) ^ cexp d q * η ^ k *
        (D.tailWR q θ j R (w p) * ∏ i ∈ univ.erase p,
          D.omg θ j (kindOf i) (w i) * beta (fun r => Crho d D.L * D.tWR q j R r) (w i)) := by
  have hL7 := H.hL
  have hL1 : 1 ≤ D.L := by omega
  have hL0 : (0 : ℝ) < D.L := by exact_mod_cast (by omega : 0 < D.L)
  have hwi : ∀ i, w i ∈ alph j D.N := fun i => Fintype.mem_piFinset.1 hw i
  have hrj : j < r ∧ r ≤ D.N := some_mem_alph.1 (hp ▸ hwi p)
  set s := scale D.L j D.N (rbar (D.rbV j) w) with hs
  set ρ : ℕ → ℝ := fun r => Crho d D.L * D.tWR q j R r with hρdef
  have hρ0 : ∀ r, 0 ≤ ρ r := fun r => mul_nonneg (Crho_nonneg d hL0.le) (tWR_nonneg hL1 q j R r)
  have hρ : ∀ r', j < r' → r' ≤ D.N → ∀ m,
      ‖((D.Z j • (Asym D.msq * R r') : Sym d n)) m‖ ≤ ρ r' :=
    fun r' h1 h2 m => rho_boundR H hR ⟨h1, h2⟩ m
  -- the range bound of `w`
  have hrb_ge : D.L ^ r ≤ rbar (D.rbV j) w := by
    unfold rbar
    refine le_trans ?_ (single_le_sum (f := fun i => D.rbV j (kindOf i) (w i))
      (fun _ _ => Nat.zero_le _) (mem_univ p))
    simp only [hp]; generalize kindOf p = κ; fin_cases κ <;> simp [rbV]
  have hrb_le : rbar (D.rbV j) w ≤ (k + 2) * (D.L ^ r + 2) := by
    unfold rbar
    calc ∑ i, D.rbV j (kindOf i) (w i) ≤ ∑ _i : Fin (k + 2), (D.L ^ r + 2) :=
          sum_le_sum fun i _ => rbV_le_of_max hrj.1 (fun r' h => hmax i r' h) hL1
      _ = _ := by simp
  have hs1 : j + 1 ≤ s := le_scale
  have hsN : s ≤ D.N := scale_le (by have := H.hj; omega)
  have hrs : r ≤ s := by
    by_cases h : s < D.N
    · have := lt_pow_scale (L := D.L) (j := j) (N := D.N) (R := rbar (D.rbV j) w) h
      rw [← hs] at this
      have hlt : D.L ^ r < D.L ^ s := lt_of_le_of_lt hrb_ge this
      exact ((Nat.pow_lt_pow_iff_right (by omega)).1 hlt).le
    · omega
  have hpow : D.L ^ (s - 1) ≤ rbar (D.rbV j) w := by
    by_cases h : j + 2 ≤ s
    · have := pow_pred_le_of_scale (L := D.L) (j := j) (N := D.N) (R := rbar (D.rbV j) w)
        (by rw [← hs]; exact h)
      rwa [← hs] at this
    · have : s - 1 = j := by omega
      rw [this]
      exact le_trans (Nat.pow_le_pow_right (by omega) hrj.1.le) hrb_ge
  -- (b)–(d): the norm of the word
  have hpt : ∀ m, ‖wordVal (D.letV j R) w m‖ ≤
      (∏ i ∈ univ.erase p, beta ρ (w i)) * ‖(D.Z j • R r) m‖ := by
    intro m
    have := norm_wordVal_le H.std H.hj.le hρ hρ0 hw hp m
    rw [Pi.smul_apply, smul_eq_mul, norm_mul]
    linarith [this]
  have hB0 : 0 ≤ ∏ i ∈ univ.erase p, beta ρ (w i) := prod_nonneg fun i _ => beta_nonneg hρ0 _
  have hnorm : snorm D.L q (s - 1) (wordVal (D.letV j R) w) ≤
      (∏ i ∈ univ.erase p, beta ρ (w i)) *
        ((D.L : ℝ) ^ (((s - r : ℕ) : ℝ) * cexp d q) * D.tWR q j R r) := by
    refine (snorm_le_of_pointwise hL0 hB0 hpt).trans (mul_le_mul_of_nonneg_left ?_ hB0)
    rw [snorm_smul hL0, tWR]
    have hsc := snorm_scale_change (q := q) H.hd hL1 (show r - 1 ≤ s - 1 by omega) (R r)
    rw [show s - 1 - (r - 1) = s - r by omega] at hsc
    calc ‖D.Z j‖ * snorm D.L q (s - 1) (R r)
        ≤ ‖D.Z j‖ * ((D.L : ℝ) ^ (((s - r : ℕ) : ℝ) * cexp d q) *
            snorm D.L q (r - 1) (R r)) := mul_le_mul_of_nonneg_left hsc (norm_nonneg _)
      _ = _ := by ring
  -- (e): absorption
  have hab := absorb H.hL (cexp_nonneg H.hd q) hη hηc (r := r) (s := s) (k := k)
    (by omega) hrs (hpow.trans hrb_le)
  -- (f): the weights
  have hW := Wt_le_prod_omg (D := D) H.hθ H.hθ1 hL1 hs1 w hpow
  rw [← mul_prod_erase _ _ (mem_univ p)] at hW
  have hωp : D.omg θ j (kindOf p) (w p) ≤ θ ^ (-(2 : ℝ) / 256) * Wt θ D.L (r - j) := by
    rw [hp]; exact omg_some_le H.hθ H.hθ1 hL1 hrj.1.le _
  -- (g): combine
  have hzp : ‖D.zp j‖ ^ (k + 1) = ‖D.zp j‖ * η ^ k * η ^ k := by
    rw [← hη2]; ring
  set Pw := ∏ i ∈ univ.erase p, D.omg θ j (kindOf i) (w i)
  set Pb := ∏ i ∈ univ.erase p, beta ρ (w i)
  have hPw0 : 0 ≤ Pw := prod_nonneg fun i _ => (omg_pos H.hθ j _ _).le
  have hprod : Pw * Pb = ∏ i ∈ univ.erase p, D.omg θ j (kindOf i) (w i) * beta ρ (w i) :=
    (prod_mul_distrib).symm
  have htW := tWR_nonneg (D := D) hL1 q j R r
  have hLc : 0 ≤ (D.L : ℝ) ^ (((s - r : ℕ) : ℝ) * cexp d q) := by positivity
  calc Wt θ D.L (s - 1 - j) * ‖D.zp j‖ ^ (k + 1) *
        snorm D.L q (s - 1) (wordVal (D.letV j R) w)
      ≤ (θ ^ (-(2 : ℝ) / 256) * Wt θ D.L (r - j) * Pw) * (‖D.zp j‖ * η ^ k * η ^ k) *
          (Pb * ((D.L : ℝ) ^ (((s - r : ℕ) : ℝ) * cexp d q) * D.tWR q j R r)) := by
        rw [hzp]
        refine mul_le_mul (mul_le_mul_of_nonneg_right (hW.trans
          (mul_le_mul_of_nonneg_right hωp hPw0)) (by positivity)) hnorm
          (snorm_nonneg hL0 _) (mul_nonneg (mul_nonneg (mul_nonneg
            (Real.rpow_nonneg H.hθ.le _) (Wt_pos H.hθ D.L (r - j)).le) hPw0) (by positivity))
    _ = ‖D.zp j‖ * η ^ k * ((D.L : ℝ) ^ (((s - r : ℕ) : ℝ) * cexp d q) * η ^ k) *
          (θ ^ (-(2 : ℝ) / 256) * Wt θ D.L (r - j) * D.tWR q j R r) * (Pw * Pb) := by ring
    _ ≤ ‖D.zp j‖ * η ^ k * (D.L : ℝ) ^ cexp d q *
          (θ ^ (-(2 : ℝ) / 256) * Wt θ D.L (r - j) * D.tWR q j R r) * (Pw * Pb) := by
        have h1 : 0 ≤ θ ^ (-(2 : ℝ) / 256) * Wt θ D.L (r - j) * D.tWR q j R r := by
          have := (Wt_pos H.hθ D.L (r - j)).le
          have := Real.rpow_nonneg H.hθ.le (-(2 : ℝ) / 256)
          positivity
        have h2 : 0 ≤ Pw * Pb := mul_nonneg hPw0 hB0
        gcongr
    _ = _ := by rw [hprod, hp]; simp only [tailWR]; ring


theorem sum_tailWR (_hL : 1 ≤ D.L) :
    ∑ ℓ ∈ alph j D.N, D.tailWR q θ j R ℓ = θ ^ (-(2 : ℝ) / 256) * D.SjR q θ j R := by
  simp [alph, tailWR, SjR, Finset.mul_sum, mul_assoc]

theorem sum_omg_beta_leR (H : D.StepHyp q c₂ θ j) (κ : Fin 3) :
    ∑ ℓ ∈ alph j D.N, D.omg θ j κ ℓ * beta (fun r => Crho d D.L * D.tWR q j R r) ℓ ≤
      D.sig0R q θ j R := by
  have hL1 : 1 ≤ D.L := by have := H.hL; omega
  have hL0 : (0 : ℝ) ≤ D.L := by positivity
  simp only [alph, sum_insert (show (none : Option ℕ) ∉ (Ioc j D.N).map ⟨some, Option.some_injective _⟩
    by simp), sum_map, Function.Embedding.coeFn_mk, beta, mul_one, sig0R, SjR]
  refine add_le_add (omg_none_le H.hθ H.hθ1 hL1 j κ) ?_
  rw [Finset.mul_sum]
  refine sum_le_sum fun r hr => ?_
  rw [mem_Ioc] at hr
  have h1 := omg_some_le (D := D) H.hθ H.hθ1 hL1 hr.1.le κ
  have h2 : 0 ≤ Crho d D.L * D.tWR q j R r := mul_nonneg (Crho_nonneg d hL0) (tWR_nonneg hL1 q j R r)
  calc D.omg θ j κ (some r) * (Crho d D.L * D.tWR q j R r)
      ≤ θ ^ (-(2 : ℝ) / 256) * Wt θ D.L (r - j) * (Crho d D.L * D.tWR q j R r) :=
        mul_le_mul_of_nonneg_right h1 h2
    _ = _ := by ring

/-- The bound for all words of length `k + 2`. -/
theorem words_k_boundR (H : D.StepHyp q c₂ θ j) (hR : D.RangeR j R) {η : ℝ} (hη : 0 ≤ η)
    (hη2 : η ^ 2 = ‖D.zp j‖) (hηc : η ≤ (D.L : ℝ) ^ (-cexp d q)) (k : ℕ) :
    ∑ w ∈ words j D.N k, Wt θ D.L (scale D.L j D.N (rbar (D.rbV j) w) - 1 - j) *
        ‖D.zp j‖ ^ (k + 1) *
        snorm D.L q (scale D.L j D.N (rbar (D.rbV j) w) - 1) (wordVal (D.letV j R) w) ≤
      ‖D.zp j‖ * (D.L : ℝ) ^ cexp d q * η ^ k *
        (c₂ * (θ ^ (-(3 : ℝ) / 256)) ^ (k + 2) +
          (k + 2) * (θ ^ (-(2 : ℝ) / 256) * D.SjR q θ j R) * D.sig0R q θ j R ^ (k + 1)) := by
  have hL7 := H.hL
  have hL1 : 1 ≤ D.L := by omega
  have hL0 : (0 : ℝ) ≤ D.L := by positivity
  set ρ : ℕ → ℝ := fun r => Crho d D.L * D.tWR q j R r
  have hρ0 : ∀ r, 0 ≤ ρ r := fun r => mul_nonneg (Crho_nonneg d hL0) (tWR_nonneg hL1 q j R r)
  set std : Fin (k + 2) → Option ℕ := fun _ => none
  have hstd : std ∈ words j D.N k := Fintype.mem_piFinset.2 fun _ => none_mem_alph j D.N
  set G : Fin (k + 2) → (Fin (k + 2) → Option ℕ) → ℝ := fun p w =>
    D.tailWR q θ j R (w p) * ∏ i ∈ univ.erase p, D.omg θ j (kindOf i) (w i) * beta ρ (w i)
  have hG0 : ∀ p w, 0 ≤ G p w := by
    intro p w
    refine mul_nonneg ?_ (prod_nonneg fun i _ =>
      mul_nonneg (omg_pos H.hθ j _ _).le (beta_nonneg hρ0 _))
    rcases w p with _ | r
    · simp [tailWR]
    · simp only [tailWR]
      exact mul_nonneg (mul_nonneg (Real.rpow_nonneg H.hθ.le _) (Wt_pos H.hθ _ _).le)
        (tWR_nonneg hL1 q j R r)
  set K := ‖D.zp j‖ * (D.L : ℝ) ^ cexp d q * η ^ k
  have hK0 : 0 ≤ K := by positivity
  set f : (Fin (k + 2) → Option ℕ) → ℝ := fun w =>
    Wt θ D.L (scale D.L j D.N (rbar (D.rbV j) w) - 1 - j) * ‖D.zp j‖ ^ (k + 1) *
      snorm D.L q (scale D.L j D.N (rbar (D.rbV j) w) - 1) (wordVal (D.letV j R) w)
  -- per-word bound
  have hper : ∀ w ∈ words j D.N k, f w ≤
      (if w = std then K * (c₂ * (θ ^ (-(3 : ℝ) / 256)) ^ (k + 2)) else 0) +
        K * ∑ p, G p w := by
    intro w hw
    by_cases htail : ∃ i r, w i = some r
    · obtain ⟨p, r, hp, hmax⟩ := exists_max_tail htail
      have hne : w ≠ std := fun h => by rw [h] at hp; simp [std] at hp
      rw [if_neg hne, zero_add]
      refine (word_tail_boundR H hR hη hη2 hηc hw hp hmax).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hK0
      exact single_le_sum (f := fun p => G p w) (fun p _ => hG0 p w) (mem_univ p)
    · have hw' : w = std := by
        funext i
        rcases h : w i with _ | r
        · rfl
        · exact absurd ⟨i, r, h⟩ htail
      subst hw'
      rw [if_pos rfl]
      have := word_std_bound H hη hη2 hηc k
      rw [wordVal_std, ← wordVal_std (D := D) j R k] at this
      have h2 : 0 ≤ K * ∑ p, G p std := mul_nonneg hK0 (sum_nonneg fun p _ => hG0 p _)
      exact le_add_of_le_of_nonneg this h2
  -- product structure of the `G`-sums
  have hprod : ∀ p, ∑ w ∈ words j D.N k, G p w ≤
      (θ ^ (-(2 : ℝ) / 256) * D.SjR q θ j R) * D.sig0R q θ j R ^ (k + 1) := by
    intro p
    set g : Fin (k + 2) → Option ℕ → ℝ := fun i ℓ =>
      if i = p then D.tailWR q θ j R ℓ else D.omg θ j (kindOf i) ℓ * beta ρ ℓ
    have hGg : ∀ w, G p w = ∏ i, g i (w i) := by
      intro w
      simp only [G, g]
      rw [← mul_prod_erase _ _ (mem_univ p), if_pos rfl]
      congr 1
      exact prod_congr rfl fun i hi => by rw [if_neg (ne_of_mem_erase hi)]
    simp only [hGg]
    unfold words
    rw [← Finset.prod_univ_sum (fun _ => alph j D.N) g]
    rw [← mul_prod_erase _ _ (mem_univ p)]
    simp only [g, if_pos rfl]
    rw [sum_tailWR hL1]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (Real.rpow_nonneg H.hθ.le _)
      (SjR_nonneg H.hθ hL1))
    calc ∏ i ∈ univ.erase p, ∑ ℓ ∈ alph j D.N,
          (if i = p then D.tailWR q θ j R ℓ else D.omg θ j (kindOf i) ℓ * beta ρ ℓ)
        ≤ ∏ _i ∈ univ.erase p, D.sig0R q θ j R := by
          refine prod_le_prod (fun i hi => sum_nonneg fun ℓ _ => ?_) fun i hi => ?_
          · rw [if_neg (ne_of_mem_erase hi)]
            exact mul_nonneg (omg_pos H.hθ j _ _).le (beta_nonneg hρ0 _)
          · simp only [if_neg (ne_of_mem_erase hi)]
            exact sum_omg_beta_leR (R := R) H (kindOf i)
      _ = D.sig0R q θ j R ^ (k + 1) := by
          rw [prod_const, card_erase_of_mem (mem_univ p), card_univ, Fintype.card_fin]; rfl
  calc ∑ w ∈ words j D.N k, f w
      ≤ ∑ w ∈ words j D.N k, ((if w = std then K * (c₂ * (θ ^ (-(3 : ℝ) / 256)) ^ (k + 2))
          else 0) + K * ∑ p, G p w) := sum_le_sum hper
    _ = K * (c₂ * (θ ^ (-(3 : ℝ) / 256)) ^ (k + 2)) + K * ∑ p, ∑ w ∈ words j D.N k, G p w := by
        rw [sum_add_distrib, sum_ite_eq' (words j D.N k) std, if_pos hstd, ← mul_sum, sum_comm]
    _ ≤ K * (c₂ * (θ ^ (-(3 : ℝ) / 256)) ^ (k + 2)) +
          K * ∑ _p : Fin (k + 2), (θ ^ (-(2 : ℝ) / 256) * D.SjR q θ j R) * D.sig0R q θ j R ^ (k + 1) := by
        gcongr with p; exact hprod p
    _ = _ := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring


/-- The words assigned to the scales `s ≥ j + 1` (`lem:sum`(b), without the tails of `R_j`). -/
theorem scales_bound_allR (H : D.StepHyp q c₂ θ j) (hR : D.RangeR j R) {η : ℝ} (hη : 0 ≤ η)
    (hη2 : η ^ 2 = ‖D.zp j‖) (hηc : η ≤ (D.L : ℝ) ^ (-cexp d q))
    (hx : η * θ ^ (-(3 : ℝ) / 256) ≤ 1 / 2) (hy : η * D.sig0R q θ j R ≤ 1 / 2)
    (hden : ∀ m, ‖D.zp j * D.eps j R m‖ < 1) :
    ∑ s ∈ Icc (j + 1) D.N, Wt θ D.L (s - 1 - j) * snorm D.L q (s - 1) (D.wSc j R s) ≤
      ‖D.zp j‖ * (D.L : ℝ) ^ cexp d q *
        (2 * (c₂ * (θ ^ (-(3 : ℝ) / 256)) ^ 2) +
          6 * (θ ^ (-(2 : ℝ) / 256) * D.SjR q θ j R * D.sig0R q θ j R)) := by
  have hL7 := H.hL
  have hL1 : 1 ≤ D.L := by omega
  have hL0 : (0 : ℝ) < D.L := by exact_mod_cast (by omega : 0 < D.L)
  have hj1 : j + 1 ≤ D.N := H.hj
  have hS0 := SjR_nonneg (D := D) (q := q) (j := j) (R := R) H.hθ hL1
  have hc₂ : 0 ≤ c₂ := le_trans (snorm_nonneg hL0 _) (H.loc 0 (by have := H.hj; omega))
  set a := θ ^ (-(3 : ℝ) / 256)
  have ha0 : 0 ≤ a := Real.rpow_nonneg H.hθ.le _
  set σ := D.sig0R q θ j R
  have hσ0 : 0 ≤ σ := add_nonneg ha0 (mul_nonneg (mul_nonneg (Real.rpow_nonneg H.hθ.le _)
    (Crho_nonneg d hL0.le)) hS0)
  set b2 := θ ^ (-(2 : ℝ) / 256)
  have hb20 : 0 ≤ b2 := Real.rpow_nonneg H.hθ.le _
  set K0 := ‖D.zp j‖ * (D.L : ℝ) ^ cexp d q
  have hK0 : 0 ≤ K0 := by positivity
  -- the majorant `b k`
  set A1 := K0 * (c₂ * a ^ 2)
  set A2 := K0 * (b2 * D.SjR q θ j R * σ)
  have hA1 : 0 ≤ A1 := by positivity
  have hA2 : 0 ≤ A2 := by positivity
  set b : ℕ → ℝ := fun k => A1 * (η * a) ^ k + A2 * (((k : ℝ) + 2) * (η * σ) ^ k)
  have hb_eq : ∀ k, K0 * η ^ k * (c₂ * a ^ (k + 2) + (k + 2) * (b2 * D.SjR q θ j R) * σ ^ (k + 1)) =
      b k := by
    intro k; simp only [b, A1, A2]; ring
  have hbs : Summable b :=
    ((summable_geom_half (by positivity) hx).mul_left A1).add
      ((summable_k2_half (by positivity) hy).mul_left A2)
  have hbsum : ∑' k, b k ≤ 2 * A1 + 6 * A2 := by
    rw [((summable_geom_half (by positivity) hx).mul_left A1).tsum_add
      ((summable_k2_half (by positivity) hy).mul_left A2), tsum_mul_left, tsum_mul_left]
    have := tsum_geom_half_le (by positivity) hx
    have := tsum_k2_half_le (by positivity) hy
    nlinarith
  -- the per-scale word sums
  set F : ℕ → ℕ → ℝ := fun s k =>
    ∑ w ∈ (words j D.N k).filter (fun w => scale D.L j D.N (rbar (D.rbV j) w) = s),
      Wt θ D.L (scale D.L j D.N (rbar (D.rbV j) w) - 1 - j) * ‖D.zp j‖ ^ (k + 1) *
        snorm D.L q (scale D.L j D.N (rbar (D.rbV j) w) - 1) (wordVal (D.letV j R) w)
  have hF0 : ∀ s k, 0 ≤ F s k := fun s k => sum_nonneg fun w _ => by
    have := (Wt_pos H.hθ D.L (scale D.L j D.N (rbar (D.rbV j) w) - 1 - j)).le
    have := snorm_nonneg hL0 (q := q) (s := scale D.L j D.N (rbar (D.rbV j) w) - 1)
      (wordVal (D.letV j R) w)
    positivity
  have hFsum : ∀ k, ∑ s ∈ Icc (j + 1) D.N, F s k ≤ b k := by
    intro k
    rw [← hb_eq k]
    have := words_k_boundR H hR hη hη2 hηc k
    refine le_trans (le_of_eq ?_) this
    exact sum_fiberwise_of_maps_to (fun w _ => by rw [mem_Icc]; exact ⟨le_scale, scale_le hj1⟩) _
  have hFle : ∀ s ∈ Icc (j + 1) D.N, ∀ k, F s k ≤ b k := fun s hs k =>
    (single_le_sum (f := fun s => F s k) (fun s _ => hF0 s k) hs).trans (hFsum k)
  -- each scale
  have hterm : ∀ s ∈ Icc (j + 1) D.N, ∀ k, Wt θ D.L (s - 1 - j) *
      snorm D.L q (s - 1) (D.zp j ^ (k + 1) • D.wLen j R s k) ≤ F s k := by
    intro s hs k
    rw [snorm_smul hL0, norm_pow]
    have hsum := snorm_sum_le (q := q) (s := s - 1) hL0
      ((words j D.N k).filter (fun w => scale D.L j D.N (rbar (D.rbV j) w) = s))
      (fun w => wordVal (D.letV j R) w)
    calc Wt θ D.L (s - 1 - j) * (‖D.zp j‖ ^ (k + 1) * snorm D.L q (s - 1) (D.wLen j R s k))
        ≤ Wt θ D.L (s - 1 - j) * (‖D.zp j‖ ^ (k + 1) *
            ∑ w ∈ (words j D.N k).filter (fun w => scale D.L j D.N (rbar (D.rbV j) w) = s),
              snorm D.L q (s - 1) (wordVal (D.letV j R) w)) := by
          gcongr
          · exact (Wt_pos H.hθ _ _).le
          · exact hsum
      _ = F s k := by
          simp only [F, mul_sum]
          refine sum_congr rfl fun w hw => ?_
          rw [(mem_filter.1 hw).2]; ring
  have hsumm : ∀ s ∈ Icc (j + 1) D.N, Summable fun k =>
      snorm D.L q (s - 1) (D.zp j ^ (k + 1) • D.wLen j R s k) := by
    intro s hs
    refine Summable.of_nonneg_of_le (fun k => snorm_nonneg hL0 _) (fun k => ?_) hbs
    have h1 := hterm s hs k
    have h2 := one_le_Wt H.hθ H.hθ1 hL0.le (s - 1 - j)
    have h3 := snorm_nonneg hL0 (q := q) (s := s - 1) (D.zp j ^ (k + 1) • D.wLen j R s k)
    nlinarith [hFle s hs k]
  have hscale : ∀ s ∈ Icc (j + 1) D.N, snorm D.L q (s - 1) (D.wSc j R s) ≤
      ∑' k, snorm D.L q (s - 1) (D.zp j ^ (k + 1) • D.wLen j R s k) := by
    intro s hs
    exact snorm_le_tsum hL0 (fun m => hasSum_wSc H.std hL1 j hj1 R m (hden m) hs)
      (hsumm s hs)
  have hsub : Icc (j + 1) D.N ⊆ Icc (j + 1) D.N := subset_rfl
  calc ∑ s ∈ Icc (j + 1) D.N, Wt θ D.L (s - 1 - j) * snorm D.L q (s - 1) (D.wSc j R s)
      ≤ ∑ s ∈ Icc (j + 1) D.N, ∑' k, Wt θ D.L (s - 1 - j) *
          snorm D.L q (s - 1) (D.zp j ^ (k + 1) • D.wLen j R s k) := by
        refine sum_le_sum fun s hs => ?_
        rw [tsum_mul_left]
        exact mul_le_mul_of_nonneg_left (hscale s (hsub hs)) (Wt_pos H.hθ _ _).le
    _ = ∑' k, ∑ s ∈ Icc (j + 1) D.N, Wt θ D.L (s - 1 - j) *
          snorm D.L q (s - 1) (D.zp j ^ (k + 1) • D.wLen j R s k) :=
        (Summable.tsum_finsetSum fun s hs => (hsumm s (hsub hs)).mul_left _).symm
    _ ≤ ∑' k, b k := by
        refine Summable.tsum_le_tsum (fun k => ?_) (summable_sum fun s hs =>
          (hsumm s (hsub hs)).mul_left _) hbs
        calc ∑ s ∈ Icc (j + 1) D.N, Wt θ D.L (s - 1 - j) *
              snorm D.L q (s - 1) (D.zp j ^ (k + 1) • D.wLen j R s k)
            ≤ ∑ s ∈ Icc (j + 1) D.N, F s k := sum_le_sum fun s hs => hterm s (hsub hs) k
          _ ≤ b k := hFsum k
    _ ≤ 2 * A1 + 6 * A2 := hbsum
    _ = _ := by simp only [A1, A2, K0]; ring


/-- `∑_r tW r ≤ 𝒮_j`, since `W ≥ 1`. -/
theorem sum_tWR_le_SjR {q : ℕ} {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hL : 1 ≤ D.L) (j : ℕ) :
    ∑ r ∈ Ioc j D.N, D.tWR q j R r ≤ D.SjR q θ j R := by
  refine sum_le_sum fun r _ => ?_
  have := one_le_Wt hθ hθ1 (by positivity : (0 : ℝ) ≤ D.L) (r - j)
  have := tWR_nonneg (D := D) hL q j R r
  nlinarith

/-- The denominators `1 - ζ' ε_j` do not vanish, `|ζ' ε_j| ≤ 1/2`. -/
theorem norm_zp_eps_leR {q : ℕ} {c₂ θ : ℝ} {j : ℕ} (H : D.StepHyp q c₂ θ j) (hR : D.RangeR j R)
    (hζ : ‖D.ζ j‖ ≤ θ) (hθ8 : θ ≤ 1 / 8) (hS : Crho d D.L * D.SjR q θ j R ≤ 1) (m : Torus d n) :
    ‖D.zp j * D.eps j R m‖ ≤ 1 / 2 := by
  have hL1 : 1 ≤ D.L := by have := H.hL; omega
  have h1 := norm_eps_le H.std H.hj.le (fun r h1 h2 m => rho_boundR H hR ⟨h1, h2⟩ m) m
  have h2 : ∑ r ∈ Ioc j D.N, Crho d D.L * D.tWR q j R r ≤ 1 := by
    rw [← mul_sum]
    exact le_trans (mul_le_mul_of_nonneg_left (sum_tWR_le_SjR H.hθ H.hθ1 hL1 j)
      (Crho_nonneg d (by positivity))) hS
  have h3 := norm_zp_le (D := D) (j := j) (by linarith)
  rw [norm_mul]
  have : ‖D.eps j R m‖ ≤ 2 := by linarith
  nlinarith [norm_nonneg (D.zp j), norm_nonneg (D.eps j R m)]

/-- `lem:sum` with the choice of `θ`: all words of scales `s ≥ j + 1` contribute `≤ K₁ |ζ_j|`. -/
theorem word_sum_leR {q : ℕ} {c₂ θ : ℝ}
    (hG : Good D.L (cexp d q) c₂ (Crho d D.L) θ) (hζj' : ‖D.ζ j‖ ≤ θ)
    (H : D.StepHyp q c₂ θ j) (hR : D.RangeR j R)
    (hS1 : Crho d D.L * D.SjR q θ j R ≤ 1) :
    ∑ s ∈ Icc (j + 1) D.N, Wt θ D.L (s - 1 - j) * snorm D.L q (s - 1) (D.wSc j R s) ≤
      K1 D.L (cexp d q) c₂ θ * ‖D.ζ j‖ := by
  have hL7 := H.hL
  have hL1 : 1 ≤ D.L := by omega
  have hL0 : (0 : ℝ) < D.L := by exact_mod_cast (by omega : 0 < D.L)
  have hθ := hG.pos
  have hθ1 : θ ≤ 1 := by linarith [hG.le8]
  have hc₂ : 0 ≤ c₂ := le_trans (snorm_nonneg hL0 _) (H.loc 0 (by have := H.hj; omega))
  have hK1 := K1_nonneg (L := (D.L : ℝ)) (c := cexp d q) hL0.le hc₂ hθ.le
  have hS0 := SjR_nonneg (D := D) (q := q) (j := j) (R := R) hθ hL1
  have hS1' : D.SjR q θ j R ≤ 1 := by
    have := one_le_Crho d (by exact_mod_cast hL1 : (1 : ℝ) ≤ D.L)
    nlinarith
  -- `σ₀ ≤ 2 θ^{-3/256}`
  have hb2a : θ ^ (-(2 : ℝ) / 256) ≤ θ ^ (-(3 : ℝ) / 256) :=
    Real.rpow_le_rpow_of_exponent_ge hθ hθ1 (by norm_num)
  have hσ : D.sig0R q θ j R ≤ 2 * θ ^ (-(3 : ℝ) / 256) := by
    unfold sig0R
    have : θ ^ (-(2 : ℝ) / 256) * Crho d D.L * D.SjR q θ j R ≤ θ ^ (-(2 : ℝ) / 256) := by
      rw [mul_assoc]
      exact mul_le_of_le_one_right (Real.rpow_nonneg hθ.le _) hS1
    linarith
  -- `η = √|ζ'|`
  have hζj : ‖D.ζ j‖ ≤ 1 / 2 := by linarith [hζj', hG.le8]
  have hzp := norm_zp_le (D := D) hζj
  set η := Real.sqrt ‖D.zp j‖
  have hη0 : 0 ≤ η := Real.sqrt_nonneg _
  have hη2 : η ^ 2 = ‖D.zp j‖ := Real.sq_sqrt (norm_nonneg _)
  have hη : η ≤ Real.sqrt (2 * θ) :=
    Real.sqrt_le_sqrt (by linarith [hζj'])
  have hηc : η ≤ (D.L : ℝ) ^ (-cexp d q) := hη.trans hG.absorb
  have hgeom := hG.geom
  have hsq0 : 0 ≤ Real.sqrt (2 * θ) := Real.sqrt_nonneg _
  have ha0 : 0 ≤ θ ^ (-(3 : ℝ) / 256) := Real.rpow_nonneg hθ.le _
  have hx : η * θ ^ (-(3 : ℝ) / 256) ≤ 1 / 2 := by nlinarith
  have hy : η * D.sig0R q θ j R ≤ 1 / 2 := by
    have hσ0 : 0 ≤ D.sig0R q θ j R := add_nonneg ha0 (mul_nonneg (mul_nonneg
      (Real.rpow_nonneg hθ.le _) (Crho_nonneg d hL0.le)) hS0)
    nlinarith
  have hden : ∀ m, ‖D.zp j * D.eps j R m‖ < 1 := fun m =>
    lt_of_le_of_lt (norm_zp_eps_leR H hR (hζj') hG.le8 hS1 m) (by norm_num)
  have hsc := scales_bound_allR H hR hη0 hη2 hηc hx hy hden
  -- the word contribution is `≤ K₁ |ζ_j|`
  have hword : ‖D.zp j‖ * (D.L : ℝ) ^ cexp d q *
      (2 * (c₂ * (θ ^ (-(3 : ℝ) / 256)) ^ 2) +
        6 * (θ ^ (-(2 : ℝ) / 256) * D.SjR q θ j R * D.sig0R q θ j R)) ≤
      K1 D.L (cexp d q) c₂ θ * ‖D.ζ j‖ := by
    have hsq : (θ ^ (-(3 : ℝ) / 256)) ^ 2 = θ ^ (-(6 : ℝ) / 256) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hθ.le]; norm_num
    have hprod : θ ^ (-(2 : ℝ) / 256) * θ ^ (-(3 : ℝ) / 256) = θ ^ (-(5 : ℝ) / 256) := by
      rw [← Real.rpow_add hθ]; norm_num
    have hin : θ ^ (-(2 : ℝ) / 256) * D.SjR q θ j R * D.sig0R q θ j R ≤ 2 * θ ^ (-(5 : ℝ) / 256) := by
      rw [← hprod]
      have hb20 := Real.rpow_nonneg hθ.le (-(2 : ℝ) / 256)
      have hσ0 : 0 ≤ D.sig0R q θ j R := add_nonneg ha0 (mul_nonneg (mul_nonneg
        (Real.rpow_nonneg hθ.le _) (Crho_nonneg d hL0.le)) hS0)
      calc θ ^ (-(2 : ℝ) / 256) * D.SjR q θ j R * D.sig0R q θ j R
          ≤ θ ^ (-(2 : ℝ) / 256) * 1 * (2 * θ ^ (-(3 : ℝ) / 256)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hS1' hb20) hσ hσ0 (mul_nonneg hb20 zero_le_one)
        _ = _ := by ring
    have hLc := Real.rpow_nonneg hL0.le (cexp d q)
    have hpos : 0 ≤ ‖D.zp j‖ * (D.L : ℝ) ^ cexp d q := by positivity
    calc ‖D.zp j‖ * (D.L : ℝ) ^ cexp d q *
          (2 * (c₂ * (θ ^ (-(3 : ℝ) / 256)) ^ 2) +
            6 * (θ ^ (-(2 : ℝ) / 256) * D.SjR q θ j R * D.sig0R q θ j R))
        ≤ (2 * ‖D.ζ j‖) * (D.L : ℝ) ^ cexp d q *
          (2 * (c₂ * θ ^ (-(6 : ℝ) / 256)) + 6 * (2 * θ ^ (-(5 : ℝ) / 256))) := by
          rw [hsq]
          have : 0 ≤ 2 * (c₂ * θ ^ (-(6 : ℝ) / 256)) +
              6 * (θ ^ (-(2 : ℝ) / 256) * D.SjR q θ j R * D.sig0R q θ j R) := by
            have := Real.rpow_nonneg hθ.le (-(6 : ℝ) / 256)
            have := Real.rpow_nonneg hθ.le (-(2 : ℝ) / 256)
            have hσ0 : 0 ≤ D.sig0R q θ j R := add_nonneg ha0 (mul_nonneg (mul_nonneg
              (Real.rpow_nonneg hθ.le _) (Crho_nonneg d hL0.le)) hS0)
            positivity
          calc ‖D.zp j‖ * (D.L : ℝ) ^ cexp d q *
                (2 * (c₂ * θ ^ (-(6 : ℝ) / 256)) +
                  6 * (θ ^ (-(2 : ℝ) / 256) * D.SjR q θ j R * D.sig0R q θ j R))
              ≤ ‖D.zp j‖ * (D.L : ℝ) ^ cexp d q *
                (2 * (c₂ * θ ^ (-(6 : ℝ) / 256)) + 6 * (2 * θ ^ (-(5 : ℝ) / 256))) := by
                gcongr
            _ ≤ _ := by
                have : 0 ≤ 2 * (c₂ * θ ^ (-(6 : ℝ) / 256)) + 6 * (2 * θ ^ (-(5 : ℝ) / 256)) := by
                  have := Real.rpow_nonneg hθ.le (-(6 : ℝ) / 256)
                  have := Real.rpow_nonneg hθ.le (-(5 : ℝ) / 256)
                  positivity
                gcongr
      _ = K1 D.L (cexp d q) c₂ θ * ‖D.ζ j‖ := by unfold K1; ring
  exact hsc.trans hword


end Data

end

end DressedFRD
