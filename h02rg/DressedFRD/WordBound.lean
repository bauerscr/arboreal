import DressedFRD.Weights

/-!
# Weighted bounds for single words (`lem:sum`, per word)

`StepHyp` collects the standing hypotheses at time `j`. With `tW r = |Z_j| ‖R_{j,r}‖_{(r-1)}`,
`ρ_r = C_ρ tW r`, `η² = |ζ'|` and `η ≤ L^{-c}`, `c = d - 2 + q`:
* `word_tail_bound`: for a word with a tail letter of maximal scale `r*` at position `p`,
  `W_{s-1-j} |ζ'|^{k+1} ‖O_w‖_{(s-1)} ≤ |ζ'| L^c η^k (θ^{-2/256} W_{r*-j} tW r*) ∏_{i≠p} ω_i β_i`.
* `word_std_bound`: for the standard word,
  `W_{s-1-j} |ζ'|^{k+1} ‖O_w‖_{(s-1)} ≤ |ζ'| L^c η^k c₂ (θ^{-3/256})^{k+2}`.
-/

namespace DressedFRD

noncomputable section

open Finset Grassmann FRD

variable {d n : ℕ} [NeZero n]

namespace Data

/-- The standing hypotheses at time `j`. -/
structure StepHyp (D : Data d n) (q : ℕ) (c₂ θ : ℝ) (j : ℕ) : Prop where
  std : StdHyp D.L D.N D.msq D.C
  loc : StdLoc D.L D.N q D.msq c₂ D.C
  hL : 7 ≤ D.L
  hn : n = D.L ^ D.N
  hq : 2 ≤ q
  hd : 2 ≤ d
  hmsq : D.msq ≤ (D.L : ℝ) ^ (-(2 * ((D.N : ℝ) - 1)))
  hj : j < D.N
  tr : D.TailRange j
  hθ : 0 < θ
  hθ1 : θ ≤ 1

variable {D : Data d n} {q : ℕ} {c₂ θ : ℝ} {j : ℕ}

/-- `tW r = |Z_j| ‖R_{j,r}‖_{(r-1)}`. -/
def tW (D : Data d n) (q j r : ℕ) : ℝ := ‖D.Z j‖ * snorm D.L q (r - 1) (D.tails j r)

theorem tW_nonneg (hL : 1 ≤ D.L) (q j r : ℕ) : 0 ≤ D.tW q j r :=
  mul_nonneg (norm_nonneg _) (snorm_nonneg (by exact_mod_cast (by omega : 0 < D.L)) _)

/-- The tail weight at the distinguished position. -/
def tailW (D : Data d n) (q : ℕ) (θ : ℝ) (j : ℕ) : Option ℕ → ℝ
  | none => 0
  | some r => θ ^ (-(2 : ℝ) / 256) * Wt θ D.L (r - j) * D.tW q j r

/-- The exponent `c = d - 2 + q`. -/
def cexp (d q : ℕ) : ℝ := (d : ℝ) - 2 + q

theorem cexp_nonneg (hd : 2 ≤ d) (q : ℕ) : 0 ≤ cexp d q := by
  unfold cexp; have : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  linarith

theorem rho_bound (H : D.StepHyp q c₂ θ j) {r : ℕ} (hr : j < r ∧ r ≤ D.N) (m : Torus d n) :
    ‖((D.Z j • (Asym D.msq * D.tails j r) : Sym d n)) m‖ ≤ Crho d D.L * D.tW q j r :=
  norm_rho_le H.std (by have := H.hL; omega) H.hn H.hq H.hmsq H.tr hr m

theorem rbV_le_of_max {r : ℕ} (hjr : j < r) {κ : Fin 3} {ℓ : Option ℕ}
    (hℓ : ∀ r', ℓ = some r' → r' ≤ r) (hL : 1 ≤ D.L) : D.rbV j κ ℓ ≤ D.L ^ r + 2 := by
  have hjr' : D.L ^ j ≤ D.L ^ r := Nat.pow_le_pow_right (by omega) hjr.le
  rcases ℓ with _ | r'
  · fin_cases κ <;> simp [rbV] <;> omega
  · have h1 : D.L ^ r' ≤ D.L ^ r := Nat.pow_le_pow_right (by omega) (hℓ r' rfl)
    fin_cases κ <;> simp [rbV] <;> omega

/-- The scale-change factor, as a real power. -/
theorem snorm_scale_change (hd : 2 ≤ d) (hL : 1 ≤ D.L) {a b : ℕ} (hab : a ≤ b) (w : Sym d n) :
    snorm D.L q b w ≤ (D.L : ℝ) ^ (((b - a : ℕ) : ℝ) * cexp d q) * snorm D.L q a w := by
  have := snorm_mono_scale (q := q) hd (by exact_mod_cast hL : (1 : ℝ) ≤ D.L) hab w
  rw [show ((b : ℝ) - a) = ((b - a : ℕ) : ℝ) by rw [Nat.cast_sub hab]] at this
  exact this

/-- `W_{s-1-j} |ζ'|^{k+1} ‖O_w‖_{(s-1)}` for a word with a maximal tail letter at `p`. -/
theorem word_tail_bound (H : D.StepHyp q c₂ θ j) {η : ℝ} (hη : 0 ≤ η)
    (hη2 : η ^ 2 = ‖D.zp j‖) (hηc : η ≤ (D.L : ℝ) ^ (-cexp d q)) {k : ℕ}
    {w : Fin (k + 2) → Option ℕ} (hw : w ∈ words j D.N k) {p : Fin (k + 2)} {r : ℕ}
    (hp : w p = some r) (hmax : ∀ i r', w i = some r' → r' ≤ r) :
    Wt θ D.L (scale D.L j D.N (rbar (D.rbV j) w) - 1 - j) * ‖D.zp j‖ ^ (k + 1) *
        snorm D.L q (scale D.L j D.N (rbar (D.rbV j) w) - 1) (wordVal (D.letV j (D.tails j)) w) ≤
      ‖D.zp j‖ * (D.L : ℝ) ^ cexp d q * η ^ k *
        (D.tailW q θ j (w p) * ∏ i ∈ univ.erase p,
          D.omg θ j (kindOf i) (w i) * beta (fun r => Crho d D.L * D.tW q j r) (w i)) := by
  have hL7 := H.hL
  have hL1 : 1 ≤ D.L := by omega
  have hL0 : (0 : ℝ) < D.L := by exact_mod_cast (by omega : 0 < D.L)
  have hwi : ∀ i, w i ∈ alph j D.N := fun i => Fintype.mem_piFinset.1 hw i
  have hrj : j < r ∧ r ≤ D.N := some_mem_alph.1 (hp ▸ hwi p)
  set s := scale D.L j D.N (rbar (D.rbV j) w) with hs
  set ρ : ℕ → ℝ := fun r => Crho d D.L * D.tW q j r with hρdef
  have hρ0 : ∀ r, 0 ≤ ρ r := fun r => mul_nonneg (Crho_nonneg d hL0.le) (tW_nonneg hL1 q j r)
  have hρ : ∀ r', j < r' → r' ≤ D.N → ∀ m,
      ‖((D.Z j • (Asym D.msq * D.tails j r') : Sym d n)) m‖ ≤ ρ r' :=
    fun r' h1 h2 m => rho_bound H ⟨h1, h2⟩ m
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
  have hpt : ∀ m, ‖wordVal (D.letV j (D.tails j)) w m‖ ≤
      (∏ i ∈ univ.erase p, beta ρ (w i)) * ‖(D.Z j • D.tails j r) m‖ := by
    intro m
    have := norm_wordVal_le H.std H.hj.le hρ hρ0 hw hp m
    rw [Pi.smul_apply, smul_eq_mul, norm_mul]
    linarith [this]
  have hB0 : 0 ≤ ∏ i ∈ univ.erase p, beta ρ (w i) := prod_nonneg fun i _ => beta_nonneg hρ0 _
  have hnorm : snorm D.L q (s - 1) (wordVal (D.letV j (D.tails j)) w) ≤
      (∏ i ∈ univ.erase p, beta ρ (w i)) *
        ((D.L : ℝ) ^ (((s - r : ℕ) : ℝ) * cexp d q) * D.tW q j r) := by
    refine (snorm_le_of_pointwise hL0 hB0 hpt).trans (mul_le_mul_of_nonneg_left ?_ hB0)
    rw [snorm_smul hL0, tW]
    have hsc := snorm_scale_change (q := q) H.hd hL1 (show r - 1 ≤ s - 1 by omega) (D.tails j r)
    rw [show s - 1 - (r - 1) = s - r by omega] at hsc
    calc ‖D.Z j‖ * snorm D.L q (s - 1) (D.tails j r)
        ≤ ‖D.Z j‖ * ((D.L : ℝ) ^ (((s - r : ℕ) : ℝ) * cexp d q) *
            snorm D.L q (r - 1) (D.tails j r)) := mul_le_mul_of_nonneg_left hsc (norm_nonneg _)
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
  have htW := tW_nonneg (D := D) hL1 q j r
  have hLc : 0 ≤ (D.L : ℝ) ^ (((s - r : ℕ) : ℝ) * cexp d q) := by positivity
  calc Wt θ D.L (s - 1 - j) * ‖D.zp j‖ ^ (k + 1) *
        snorm D.L q (s - 1) (wordVal (D.letV j (D.tails j)) w)
      ≤ (θ ^ (-(2 : ℝ) / 256) * Wt θ D.L (r - j) * Pw) * (‖D.zp j‖ * η ^ k * η ^ k) *
          (Pb * ((D.L : ℝ) ^ (((s - r : ℕ) : ℝ) * cexp d q) * D.tW q j r)) := by
        rw [hzp]
        refine mul_le_mul (mul_le_mul_of_nonneg_right (hW.trans
          (mul_le_mul_of_nonneg_right hωp hPw0)) (by positivity)) hnorm
          (snorm_nonneg hL0 _) (mul_nonneg (mul_nonneg (mul_nonneg
            (Real.rpow_nonneg H.hθ.le _) (Wt_pos H.hθ D.L (r - j)).le) hPw0) (by positivity))
    _ = ‖D.zp j‖ * η ^ k * ((D.L : ℝ) ^ (((s - r : ℕ) : ℝ) * cexp d q) * η ^ k) *
          (θ ^ (-(2 : ℝ) / 256) * Wt θ D.L (r - j) * D.tW q j r) * (Pw * Pb) := by ring
    _ ≤ ‖D.zp j‖ * η ^ k * (D.L : ℝ) ^ cexp d q *
          (θ ^ (-(2 : ℝ) / 256) * Wt θ D.L (r - j) * D.tW q j r) * (Pw * Pb) := by
        have h1 : 0 ≤ θ ^ (-(2 : ℝ) / 256) * Wt θ D.L (r - j) * D.tW q j r := by
          have := (Wt_pos H.hθ D.L (r - j)).le
          have := Real.rpow_nonneg H.hθ.le (-(2 : ℝ) / 256)
          positivity
        have h2 : 0 ≤ Pw * Pb := mul_nonneg hPw0 hB0
        gcongr
    _ = _ := by rw [hprod, hp]; simp only [tailW]; ring

/-- `W_{s-1-j} |ζ'|^{k+1} ‖O_w‖_{(s-1)}` for the standard word. -/
theorem word_std_bound (H : D.StepHyp q c₂ θ j) {η : ℝ} (hη : 0 ≤ η)
    (hη2 : η ^ 2 = ‖D.zp j‖) (hηc : η ≤ (D.L : ℝ) ^ (-cexp d q)) (k : ℕ) :
    Wt θ D.L (scale D.L j D.N (rbar (D.rbV j) (fun _ : Fin (k + 2) => (none : Option ℕ))) - 1 - j) *
        ‖D.zp j‖ ^ (k + 1) *
        snorm D.L q (scale D.L j D.N (rbar (D.rbV j) (fun _ : Fin (k + 2) => (none : Option ℕ))) - 1)
          (wordVal (D.letV j (D.tails j)) (fun _ : Fin (k + 2) => (none : Option ℕ))) ≤
      ‖D.zp j‖ * (D.L : ℝ) ^ cexp d q * η ^ k * (c₂ * (θ ^ (-(3 : ℝ) / 256)) ^ (k + 2)) := by
  have hL7 := H.hL
  have hL1 : 1 ≤ D.L := by omega
  have hL0 : (0 : ℝ) < D.L := by exact_mod_cast (by omega : 0 < D.L)
  set w : Fin (k + 2) → Option ℕ := fun _ => none
  set s := scale D.L j D.N (rbar (D.rbV j) w) with hs
  have hs1 : j + 1 ≤ s := le_scale
  have hrb_ge : D.L ^ j ≤ rbar (D.rbV j) w := by
    unfold rbar
    refine le_trans ?_ (single_le_sum (f := fun i => D.rbV j (kindOf i) (w i))
      (fun _ _ => Nat.zero_le _) (mem_univ 0))
    simp only [w, kindOf_zero]; simp [rbV]
  have hrb_le : rbar (D.rbV j) w ≤ (k + 2) * (D.L ^ (j + 1) + 2) := by
    unfold rbar
    have hjj : D.L ^ j ≤ D.L ^ (j + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    calc ∑ i, D.rbV j (kindOf i) (w i) ≤ ∑ _i : Fin (k + 2), (D.L ^ (j + 1) + 2) :=
          sum_le_sum fun i _ => by
            simp only [w]; generalize kindOf i = κ; fin_cases κ <;> simp [rbV] <;> omega
      _ = _ := by simp
  have hpow : D.L ^ (s - 1) ≤ rbar (D.rbV j) w := by
    by_cases h : j + 2 ≤ s
    · have := pow_pred_le_of_scale (L := D.L) (j := j) (N := D.N) (R := rbar (D.rbV j) w)
        (by rw [← hs]; exact h)
      rwa [← hs] at this
    · have : s - 1 = j := by omega
      rw [this]; exact hrb_ge
  have hnorm : snorm D.L q (s - 1) (wordVal (D.letV j (D.tails j)) w) ≤
      (D.L : ℝ) ^ (((s - (j + 1) : ℕ) : ℝ) * cexp d q) * c₂ := by
    have hsc := snorm_scale_change (q := q) H.hd hL1 (show j ≤ s - 1 by omega)
      (wordVal (D.letV j (D.tails j)) w)
    rw [show s - 1 - j = s - (j + 1) by omega] at hsc
    refine hsc.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact snorm_std_word_le H.std H.loc hL1 H.hj (D.tails j) k
  have hab := absorb H.hL (cexp_nonneg H.hd q) hη hηc (r := j + 1) (s := s) (k := k)
    (by omega) hs1 (hpow.trans hrb_le)
  have hW := Wt_le_prod_omg (D := D) H.hθ H.hθ1 hL1 hs1 w hpow
  have hω : ∏ i, D.omg θ j (kindOf i) (w i) ≤ (θ ^ (-(3 : ℝ) / 256)) ^ (k + 2) := by
    calc ∏ i, D.omg θ j (kindOf i) (w i) ≤ ∏ _i : Fin (k + 2), θ ^ (-(3 : ℝ) / 256) :=
          prod_le_prod (fun i _ => (omg_pos H.hθ j _ _).le) fun i _ =>
            omg_none_le H.hθ H.hθ1 hL1 j _
      _ = _ := by simp
  have hzp : ‖D.zp j‖ ^ (k + 1) = ‖D.zp j‖ * η ^ k * η ^ k := by rw [← hη2]; ring
  have hc₂ : 0 ≤ c₂ := le_trans (snorm_nonneg hL0 _) (H.loc 0 (by have := H.hj; omega))
  calc Wt θ D.L (s - 1 - j) * ‖D.zp j‖ ^ (k + 1) *
        snorm D.L q (s - 1) (wordVal (D.letV j (D.tails j)) w)
      ≤ (θ ^ (-(3 : ℝ) / 256)) ^ (k + 2) * (‖D.zp j‖ * η ^ k * η ^ k) *
          ((D.L : ℝ) ^ (((s - (j + 1) : ℕ) : ℝ) * cexp d q) * c₂) := by
        rw [hzp]
        exact mul_le_mul (mul_le_mul_of_nonneg_right (hW.trans hω) (by positivity)) hnorm
          (snorm_nonneg hL0 _) (mul_nonneg (pow_nonneg (Real.rpow_nonneg H.hθ.le _) _)
            (by positivity))
    _ = ‖D.zp j‖ * η ^ k * ((D.L : ℝ) ^ (((s - (j + 1) : ℕ) : ℝ) * cexp d q) * η ^ k) *
          (c₂ * (θ ^ (-(3 : ℝ) / 256)) ^ (k + 2)) := by ring
    _ ≤ ‖D.zp j‖ * η ^ k * (D.L : ℝ) ^ cexp d q * (c₂ * (θ ^ (-(3 : ℝ) / 256)) ^ (k + 2)) := by
        have : 0 ≤ c₂ * (θ ^ (-(3 : ℝ) / 256)) ^ (k + 2) :=
          mul_nonneg hc₂ (pow_nonneg (Real.rpow_nonneg H.hθ.le _) _)
        gcongr
    _ = _ := by ring

/-- A word with a tail letter has a tail letter of maximal scale. -/
theorem exists_max_tail {k : ℕ} {w : Fin (k + 2) → Option ℕ} (hw : ∃ i r, w i = some r) :
    ∃ p r, w p = some r ∧ ∀ i r', w i = some r' → r' ≤ r := by
  classical
  set T := univ.filter fun i : Fin (k + 2) => (w i).isSome
  have hT : T.Nonempty := by
    obtain ⟨i, r, hi⟩ := hw
    exact ⟨i, by simp [T, hi]⟩
  obtain ⟨p, hpT, hpmax⟩ := Finset.exists_max_image T (fun i => (w i).getD 0) hT
  have hps : (w p).isSome := by simpa [T] using hpT
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hps
  refine ⟨p, r, hr, fun i r' hi => ?_⟩
  have := hpmax i (by simp [T, hi])
  simpa [hi, hr] using this

end Data

end

end DressedFRD
