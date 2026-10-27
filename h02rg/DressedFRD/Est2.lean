import DressedFRD.Est1

/-!
# Letter and word bounds (`lem:letters`)

At time `j`, with tails `R` satisfying the range invariant:
* `norm_rho_le`: `|Z_j (λ+m²) R̂_{j,r}| ≤ C_ρ |Z_j| ‖R_{j,r}‖_{(r-1)}` with
  `C_ρ = (d+1)(2L)^d` (`lem:letters`(b); the text has `(d+1)L^d`, see `Log.md`).
* `norm_wordVal_le`: for a tail letter at position `p`,
  `|Ô_w| ≤ |Z_j R̂_{r_p}| ∏_{i ≠ p} β_i` pointwise, where `β = 1` for standard letters and
  `β = sup|ϱ̂_r|` for tail letters. The standard letter `a = C_{≤j}` is paired with the
  letter at `p`, and a tail letter `a` is exchanged with it (`lem:letters`(c), corrected).
* `snorm_std_word_le`: standard words have `‖O_w‖_{(j)} ≤ c₂` (`lem:letters`(d)).
-/

namespace DressedFRD

noncomputable section

open Finset Grassmann FRD

variable {d n : ℕ} [NeZero n]

namespace Data

variable {D : Data d n}

/-- The constant `C_ρ = (d+1)(2L)^d`. -/
def Crho (d : ℕ) (L : ℝ) : ℝ := (d + 1) * (2 * L) ^ d

theorem Crho_nonneg (d : ℕ) {L : ℝ} (hL : 0 ≤ L) : 0 ≤ Crho d L := by unfold Crho; positivity

/-- `lem:letters`(b): `|Z_j (λ+m²) R̂_{j,r}| ≤ C_ρ |Z_j| ‖R_{j,r}‖_{(r-1)}`. -/
theorem norm_rho_le (h : StdHyp D.L D.N D.msq D.C) (hL : 3 ≤ D.L) (hn : n = D.L ^ D.N)
    {q : ℕ} (hq : 2 ≤ q) (hmsq : D.msq ≤ (D.L : ℝ) ^ (-(2 * ((D.N : ℝ) - 1))))
    {j : ℕ} (hR : D.TailRange j) {r : ℕ} (hr : j < r ∧ r ≤ D.N) (m : Torus d n) :
    ‖((D.Z j • (Asym D.msq * D.tails j r) : Sym d n)) m‖ ≤
      Crho d D.L * (‖D.Z j‖ * snorm D.L q (r - 1) (D.tails j r)) := by
  have hL0 : (0 : ℝ) < D.L := by exact_mod_cast (by omega : 0 < D.L)
  have hL1 : (1 : ℝ) ≤ D.L := by exact_mod_cast (by omega : 1 ≤ D.L)
  have hmsq0 := h.msq_pos.le
  -- kernel bound
  have hk : ∀ x, ‖kern (Asym D.msq * D.tails j r) x‖ ≤ (d + 1) * (D.L : ℝ) ^ (-(((r - 1 : ℕ) : ℝ) * d)) *
      snorm D.L q (r - 1) (D.tails j r) := by
    intro x
    have := norm_kern_A_le (s := r - 1) hL0 hq hmsq0 (D.tails j r) x
    have hv : (fun m => ((lam m + D.msq : ℝ) : ℂ) * D.tails j r m) =
        Asym D.msq * D.tails j r := by funext m; rfl
    rw [hv] at this
    refine this.trans (mul_le_mul_of_nonneg_right ?_ (snorm_nonneg hL0 (D.tails j r)))
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
  have hcount : ((2 * rng (Asym D.msq * D.tails j r) + 1 : ℕ) : ℝ) ≤ 2 * (D.L : ℝ) ^ r := by
    have h1 := rng_Asym_mul_le D.msq (D.tails j r)
    have h2 : 2 * rng (D.tails j r) ≤ D.L ^ r := by
      by_cases hrN : r < D.N
      · have := hR r hr.1 hrN; omega
      · have : r = D.N := by omega
        rw [this, ← hn]; exact two_rng_le _
    have h3 : 3 ≤ D.L ^ r := le_trans hL (Nat.le_self_pow (by omega) _)
    have : 2 * rng (Asym D.msq * D.tails j r) + 1 ≤ 2 * D.L ^ r := by omega
    exact_mod_cast this
  have hsum := sum_kern_le (Asym D.msq * D.tails j r) hk
  have hv := norm_le_sum_kern (Asym D.msq * D.tails j r) m
  have hpow : ((2 * rng (Asym D.msq * D.tails j r) + 1 : ℕ) : ℝ) ^ d * ((D.L : ℝ) ^ (-(((r - 1 : ℕ) : ℝ) * d))) ≤
      (2 * D.L : ℝ) ^ d := by
    calc ((2 * rng (Asym D.msq * D.tails j r) + 1 : ℕ) : ℝ) ^ d * ((D.L : ℝ) ^ (-(((r - 1 : ℕ) : ℝ) * d)))
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
  have hfin : ‖((Asym D.msq * D.tails j r : Sym d n)) m‖ ≤ (d + 1) * (2 * D.L : ℝ) ^ d * snorm D.L q (r - 1) (D.tails j r) := by
    calc ‖((Asym D.msq * D.tails j r : Sym d n)) m‖ ≤ ((2 * rng (Asym D.msq * D.tails j r) + 1 : ℕ) : ℝ) ^ d * ((d + 1) * (D.L : ℝ) ^ (-(((r - 1 : ℕ) : ℝ) * d)) *
          snorm D.L q (r - 1) (D.tails j r)) := by
          refine hv.trans (hsum.trans (le_of_eq ?_)); push_cast; ring
      _ = (d + 1) * (((2 * rng (Asym D.msq * D.tails j r) + 1 : ℕ) : ℝ) ^ d * (D.L : ℝ) ^ (-(((r - 1 : ℕ) : ℝ) * d))) *
          snorm D.L q (r - 1) (D.tails j r) := by ring
      _ ≤ (d + 1) * (2 * D.L : ℝ) ^ d * snorm D.L q (r - 1) (D.tails j r) := by
          refine mul_le_mul_of_nonneg_right ?_ (snorm_nonneg hL0 (D.tails j r))
          exact mul_le_mul_of_nonneg_left hpow (by positivity)
  rw [Pi.smul_apply, smul_eq_mul, norm_mul, Crho]
  calc ‖D.Z j‖ * ‖((Asym D.msq * D.tails j r : Sym d n)) m‖ ≤ ‖D.Z j‖ * ((d + 1) * (2 * D.L : ℝ) ^ d * snorm D.L q (r - 1) (D.tails j r)) :=
        mul_le_mul_of_nonneg_left hfin (norm_nonneg _)
    _ = _ := by ring

/-- The letter weights `β`: `1` for standard letters, `ρ_r` for tail letters. -/
def beta (ρ : ℕ → ℝ) : Option ℕ → ℝ
  | none => 1
  | some r => ρ r

theorem beta_nonneg {ρ : ℕ → ℝ} (hρ : ∀ r, 0 ≤ ρ r) (ℓ : Option ℕ) : 0 ≤ beta ρ ℓ := by
  cases ℓ <;> simp [beta, hρ]

theorem kindOf_ne_zero {k : ℕ} {i : Fin (k + 2)} (hi : i ≠ 0) : (kindOf i).val = 1 ∨ (kindOf i).val = 2 := by
  unfold kindOf
  have : i.val ≠ 0 := fun h => hi (Fin.ext h)
  simp only [this, if_false]
  split_ifs <;> simp

/-- Letters at positions `b`, `c` are bounded by `β`. -/
theorem norm_letV_le (h : StdHyp D.L D.N D.msq D.C) {j : ℕ} (hj : j ≤ D.N) {R : ℕ → Sym d n}
    {ρ : ℕ → ℝ} (hρ : ∀ r, j < r → r ≤ D.N → ∀ m, ‖((D.Z j • (Asym D.msq * R r) : Sym d n)) m‖ ≤ ρ r)
    {κ : Fin 3} (hκ : κ.val = 1 ∨ κ.val = 2) {ℓ : Option ℕ} (hℓ : ℓ ∈ alph j D.N)
    (m : Torus d n) : ‖D.letV j R κ ℓ m‖ ≤ beta ρ ℓ := by
  rcases ℓ with _ | r
  · rcases hκ with hκ | hκ
    · have : κ = 1 := Fin.ext hκ
      subst this
      simpa [letV, beta] using norm_one_sub_Ehat_le h hj m
    · have : κ = 2 := Fin.ext hκ
      subst this
      simpa [letV, beta] using norm_Ehat_le h hj m
  · rw [some_mem_alph] at hℓ
    have hb := hρ r hℓ.1 hℓ.2 m
    rcases hκ with hκ | hκ
    · have : κ = 1 := Fin.ext hκ
      subst this
      simpa [letV, beta] using hb
    · have : κ = 2 := Fin.ext hκ
      subst this
      simpa [letV, beta, norm_neg] using hb

theorem norm_letV_tail {j : ℕ} {R : ℕ → Sym d n} {κ : Fin 3} (hκ : κ.val = 1 ∨ κ.val = 2)
    (r : ℕ) (m : Torus d n) :
    ‖D.letV j R κ (some r) m‖ = ‖D.Z j‖ * ‖Asym D.msq m‖ * ‖R r m‖ := by
  rcases hκ with hκ | hκ
  · have : κ = 1 := Fin.ext hκ
    subst this
    simp [letV, norm_mul, mul_assoc]
  · have : κ = 2 := Fin.ext hκ
    subst this
    simp [letV, norm_mul, norm_neg, mul_assoc]

theorem wordVal_apply {k : ℕ} (V : Fin 3 → Option ℕ → Sym d n) (w : Fin (k + 2) → Option ℕ)
    (m : Torus d n) : wordVal V w m = ∏ i, V (kindOf i) (w i) m := by
  simp [wordVal, Finset.prod_apply]

/-- `lem:letters`(c), pointwise: a tail letter at position `p` dominates the word. -/
theorem norm_wordVal_le (h : StdHyp D.L D.N D.msq D.C) {j : ℕ} (hj : j ≤ D.N)
    {R : ℕ → Sym d n} {ρ : ℕ → ℝ}
    (hρ : ∀ r, j < r → r ≤ D.N → ∀ m, ‖((D.Z j • (Asym D.msq * R r) : Sym d n)) m‖ ≤ ρ r)
    (hρ0 : ∀ r, 0 ≤ ρ r) {k : ℕ} {w : Fin (k + 2) → Option ℕ} (hw : w ∈ words j D.N k)
    {p : Fin (k + 2)} {r : ℕ} (hp : w p = some r) (m : Torus d n) :
    ‖wordVal (D.letV j R) w m‖ ≤
      ‖D.Z j‖ * ‖R r m‖ * ∏ i ∈ univ.erase p, beta ρ (w i) := by
  have hwi : ∀ i, w i ∈ alph j D.N := fun i => Fintype.mem_piFinset.1 hw i
  rw [wordVal_apply, norm_prod]
  have hb : ∀ i ∈ (univ : Finset (Fin (k + 2))).erase p, i ≠ 0 →
      ‖D.letV j R (kindOf i) (w i) m‖ ≤ beta ρ (w i) :=
    fun i _ hi0 => norm_letV_le h hj hρ (kindOf_ne_zero hi0) (hwi i) m
  by_cases hp0 : p = 0
  · subst hp0
    rw [← mul_prod_erase _ _ (mem_univ 0)]
    have h0 : ‖D.letV j R (kindOf (0 : Fin (k + 2))) (w 0) m‖ = ‖D.Z j‖ * ‖R r m‖ := by
      rw [hp, kindOf_zero]; simp [letV, norm_mul]
    rw [h0]
    refine mul_le_mul_of_nonneg_left (prod_le_prod (fun i _ => norm_nonneg _) fun i hi =>
      hb i hi (ne_of_mem_erase hi)) (by positivity)
  · have hpm : p ∈ (univ : Finset (Fin (k + 2))) := mem_univ p
    rw [← mul_prod_erase _ _ hpm]
    have h0m : (0 : Fin (k + 2)) ∈ (univ : Finset (Fin (k + 2))).erase p :=
      mem_erase.2 ⟨Ne.symm hp0, mem_univ _⟩
    rw [← mul_prod_erase _ _ h0m, ← mul_prod_erase _ _ h0m]
    -- the pair `(a, ℓ_p)`
    have hpair : ‖D.letV j R (kindOf p) (w p) m‖ * ‖D.letV j R (kindOf (0 : Fin (k + 2))) (w 0) m‖ ≤
        ‖D.Z j‖ * ‖R r m‖ * beta ρ (w 0) := by
      rw [hp, norm_letV_tail (kindOf_ne_zero hp0) r m, kindOf_zero]
      rcases hw0 : w 0 with _ | ra
      · -- `|C_{≤j}| |A| = |ê_j| ≤ 1`
        have hE := norm_Ehat_le h hj m
        simp only [Ehat, Pi.mul_apply, norm_mul] at hE
        rw [show D.letV j R 0 none = Cle D.C j from rfl]
        simp only [beta]
        nlinarith [norm_nonneg (D.Z j), norm_nonneg (R r m), norm_nonneg (Asym D.msq m),
          norm_nonneg (Cle D.C j m), mul_nonneg (norm_nonneg (D.Z j)) (norm_nonneg (R r m))]
      · have hra := hwi 0
        rw [hw0, some_mem_alph] at hra
        have hρa := hρ ra hra.1 hra.2 m
        simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, norm_mul] at hρa
        rw [show D.letV j R 0 (some ra) = -(D.Z j • R ra) from rfl]
        simp only [beta, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, norm_neg, norm_mul]
        nlinarith [norm_nonneg (D.Z j), norm_nonneg (R r m), norm_nonneg (Asym D.msq m),
          norm_nonneg (R ra m), mul_nonneg (norm_nonneg (D.Z j)) (norm_nonneg (R r m))]
    have hrest : ∏ i ∈ ((univ : Finset (Fin (k + 2))).erase p).erase 0,
        ‖D.letV j R (kindOf i) (w i) m‖ ≤ ∏ i ∈ ((univ : Finset (Fin (k + 2))).erase p).erase 0,
          beta ρ (w i) :=
      prod_le_prod (fun i _ => norm_nonneg _) fun i hi =>
        hb i (mem_of_mem_erase hi) (ne_of_mem_erase hi)
    calc ‖D.letV j R (kindOf p) (w p) m‖ * (‖D.letV j R (kindOf 0) (w 0) m‖ *
          ∏ i ∈ ((univ : Finset (Fin (k + 2))).erase p).erase 0, ‖D.letV j R (kindOf i) (w i) m‖)
        = (‖D.letV j R (kindOf p) (w p) m‖ * ‖D.letV j R (kindOf 0) (w 0) m‖) *
          ∏ i ∈ ((univ : Finset (Fin (k + 2))).erase p).erase 0, ‖D.letV j R (kindOf i) (w i) m‖ := by
          ring
      _ ≤ (‖D.Z j‖ * ‖R r m‖ * beta ρ (w 0)) *
          ∏ i ∈ ((univ : Finset (Fin (k + 2))).erase p).erase 0, beta ρ (w i) :=
          mul_le_mul hpair hrest (prod_nonneg fun i _ => norm_nonneg _) (by
            have := beta_nonneg hρ0 (w 0); positivity)
      _ = _ := by ring

/-- The standard word of length `k + 2` is `C_{≤j} (1 - ê_j) ê_j^k`. -/
theorem wordVal_std (j : ℕ) (R : ℕ → Sym d n) (k : ℕ) :
    wordVal (D.letV j R) (fun _ : Fin (k + 2) => (none : Option ℕ)) =
      Cle D.C j * (1 - Ehat D.msq D.C j) * Ehat D.msq D.C j ^ k := by
  unfold wordVal
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [kindOf_succ_succ, kindOf_zero, prod_const, card_univ, Fintype.card_fin]
  rw [show (Fin.succ (0 : Fin (k + 1)) : Fin (k + 2)) = 1 from rfl, kindOf_one]
  simp [letV, mul_assoc]

/-- `lem:letters`(d): `‖C_{≤j}(1 - ê_j) ê_j^k‖_{(j)} ≤ c₂`. -/
theorem snorm_std_word_le (h : StdHyp D.L D.N D.msq D.C) {q : ℕ} {c₂ : ℝ}
    (hloc : StdLoc D.L D.N q D.msq c₂ D.C) (hL : 1 ≤ D.L) {j : ℕ} (hj : j < D.N)
    (R : ℕ → Sym d n) (k : ℕ) :
    snorm D.L q j (wordVal (D.letV j R) (fun _ : Fin (k + 2) => (none : Option ℕ))) ≤ c₂ := by
  have hL0 : (0 : ℝ) < D.L := by exact_mod_cast (by omega : 0 < D.L)
  rw [wordVal_std]
  refine (snorm_mul_le (B := 1) hL0 _ _ fun m => ?_).trans ?_
  · rw [Pi.pow_apply, norm_pow]; exact pow_le_one₀ (norm_nonneg _) (norm_Ehat_le h hj.le m)
  · rw [one_mul]; exact hloc j hj

/-- `sup |ε_j| ≤ 1 + ∑_r ρ_r`. -/
theorem norm_eps_le (h : StdHyp D.L D.N D.msq D.C) {j : ℕ} (hj : j ≤ D.N) {R : ℕ → Sym d n}
    {ρ : ℕ → ℝ} (hρ : ∀ r, j < r → r ≤ D.N → ∀ m, ‖((D.Z j • (Asym D.msq * R r) : Sym d n)) m‖ ≤ ρ r)
    (m : Torus d n) : ‖D.eps j R m‖ ≤ 1 + ∑ r ∈ Ioc j D.N, ρ r := by
  unfold eps
  rw [Pi.sub_apply, Finset.sum_apply]
  refine (norm_sub_le _ _).trans (add_le_add (norm_Ehat_le h hj m) ?_)
  refine (norm_sum_le _ _).trans (sum_le_sum fun r hr => ?_)
  rw [mem_Ioc] at hr
  exact hρ r hr.1 hr.2 m

end Data

end

end DressedFRD
