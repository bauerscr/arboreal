import Obs2.Flow.Tau2
import Step2.Flow.FlowF1
import Step2.Map.Geom
import Step2.D2.D2LDress

/-!
# Bounds on the bubble `𝔩_{C,Γ}`, the row sums, and `𝔩_{kmat w} = 𝔩(w)` (Case (2))

For covariances with `GoodCov2` (Gram bound at `h = L^{j+1}`, finite range `L^{j+1}/2`):

* `norm_cov_gradL_le`, `norm_cov_gradR_le`: `|C(x+e,y) - C(x,y)|, |C(x,y+e) - C(x,y)| ≤ ℓ²/h`;
* `cov_zero_far`: the four entries of a gradient leg vanish outside the ball of radius `L^{k+1}`;
* **`norm_lfunX_le`**: `|𝔩_{C,Γ}(a)| ≤ 36 ℓ_C² ℓ_Γ² L^{k+1}/L^{j+1}` (`C` at scale `k`, `Γ` at `j`);
  **`norm_lfunC_le`**: `|𝔩_C(a)| ≤ 18 ℓ_C⁴`;
* **`norm_rowS_le`**: `|rowS_C(a)| ≤ 18 L^{2(k+1)} ℓ_C²`;
* **`lfunC_kmat`** (Parseval): `𝔩_{kmat w}(a) = 𝔩(w) = n^{-2}∑_m λ(m) w(m)²` (`Step2.D2.lc`), for every
  complex symbol `w`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Loc Step Step2 FRD

/-! ### Gradients of a Gram covariance -/

section Grad

variable {d n : ℕ} [NeZero n] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem gvec_sub_tau (Fv : Torus d n → H) (f g : Torus d n → ℝ) :
    gvec Fv (f - g) = gvec Fv f - gvec Fv g := by
  simp only [gvec, Pi.sub_apply, Complex.ofReal_sub, sub_smul, sum_sub_distrib]

theorem gvec_dprof_single (Fv : Torus d n → H) (e : Dir d) (x : Torus d n) :
    gvec Fv (dprof (Pi.single e 1 : Dir d → ℕ) x) = Fv (dirVec e + x) - Fv x := by
  rw [dprof_single, gvec_sub_tau, gvec_single, gvec_single]

theorem mabs_single_tau (e : Dir d) : Grassmann.mabs (Pi.single e 1 : Dir d → ℕ) = 1 := by
  unfold Grassmann.mabs
  rw [sum_eq_single e (fun e' _ he' => by simp [he']) (by simp)]
  simp

/-- `|C(e+x,y) - C(x,y)| ≤ ℓ²/h`. -/
theorem norm_cov_gradL_le {C : Matrix (Torus d n) (Torus d n) ℂ} {Fv Gv : Torus d n → H}
    (hC : IsGram C Fv Gv) {p : ℕ} (hp : 1 ≤ p) {h ℓ : ℝ} (hB : GramBound (Dir d) p h ℓ Fv Gv)
    (e : Dir d) (x y : Torus d n) : ‖C (dirVec e + x) y - C x y‖ ≤ ℓ ^ 2 * h⁻¹ := by
  obtain ⟨h1, -⟩ := hB (Pi.single e 1) (by rw [mabs_single_tau]; exact hp) x
  obtain ⟨-, h2⟩ := hB 0 (by simp [Grassmann.mabs]) y
  rw [mabs_single_tau, pow_one, gvec_dprof_single] at h1
  rw [dprof_zero, gvec_single] at h2
  simp only [Grassmann.mabs, Pi.zero_apply, sum_const_zero, pow_zero, inv_one, mul_one] at h2
  rw [hC, hC, ← inner_sub_left]
  calc ‖inner ℂ (Fv (dirVec e + x) - Fv x) (Gv y)‖ ≤ ‖Fv (dirVec e + x) - Fv x‖ * ‖Gv y‖ :=
        norm_inner_le_norm _ _
    _ ≤ (ℓ * h⁻¹) * ℓ := mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
    _ = ℓ ^ 2 * h⁻¹ := by ring

/-- `|C(x,e+y) - C(x,y)| ≤ ℓ²/h`. -/
theorem norm_cov_gradR_le {C : Matrix (Torus d n) (Torus d n) ℂ} {Fv Gv : Torus d n → H}
    (hC : IsGram C Fv Gv) {p : ℕ} (hp : 1 ≤ p) {h ℓ : ℝ} (hB : GramBound (Dir d) p h ℓ Fv Gv)
    (e : Dir d) (x y : Torus d n) : ‖C x (dirVec e + y) - C x y‖ ≤ ℓ ^ 2 * h⁻¹ := by
  obtain ⟨-, h1⟩ := hB (Pi.single e 1) (by rw [mabs_single_tau]; exact hp) y
  obtain ⟨h2, -⟩ := hB 0 (by simp [Grassmann.mabs]) x
  rw [mabs_single_tau, pow_one, gvec_dprof_single] at h1
  rw [dprof_zero, gvec_single] at h2
  simp only [Grassmann.mabs, Pi.zero_apply, sum_const_zero, pow_zero, inv_one, mul_one] at h2
  rw [hC, hC, ← inner_sub_right]
  calc ‖inner ℂ (Fv x) (Gv (dirVec e + y) - Gv y)‖ ≤ ‖Fv x‖ * ‖Gv (dirVec e + y) - Gv y‖ :=
        norm_inner_le_norm _ _
    _ ≤ ℓ * (ℓ * h⁻¹) := mul_le_mul h2 h1 (norm_nonneg _) ((norm_nonneg _).trans h2)
    _ = ℓ ^ 2 * h⁻¹ := by ring

end Grad

variable {L N : ℕ} [NeZero L]

/-! ### `GoodCov2`: gradients and range -/

section Good

variable {k : ℕ} {ℓC : ℝ} {C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ}

theorem good_gradL (hC : GoodCov2 k ℓC C) (e : Dir 2) (x y : Lam 2 L N) :
    ‖C (x + dirVec e) y - C x y‖ ≤ ℓC ^ 2 / (L : ℝ) ^ (k + 1) := by
  obtain ⟨H, _, _, Fv, Gv, hG, hB⟩ := hC.gram
  rw [add_comm x, div_eq_mul_inv]
  exact norm_cov_gradL_le hG (by simp [pPhi]) hB e x y

theorem good_gradR (hC : GoodCov2 k ℓC C) (e : Dir 2) (x y : Lam 2 L N) :
    ‖C x (y + dirVec e) - C x y‖ ≤ ℓC ^ 2 / (L : ℝ) ^ (k + 1) := by
  obtain ⟨H, _, _, Fv, Gv, hG, hB⟩ := hC.gram
  rw [add_comm y, div_eq_mul_inv]
  exact norm_cov_gradR_le hG (by simp [pPhi]) hB e x y

theorem good_entry (hC : GoodCov2 k ℓC C) (x y : Lam 2 L N) : ‖C x y‖ ≤ ℓC ^ 2 := by
  obtain ⟨H, _, _, Fv, Gv, hG, hB⟩ := hC.gram
  exact norm_cov_le hG hB x y

/-- The ball of radius `L^{k+1}` around `a`. -/
abbrev ballT (a : Lam 2 L N) (k : ℕ) : Finset (Lam 2 L N) :=
  univ.filter fun z : Lam 2 L N => supNorm (z - a) ≤ L ^ (k + 1)

theorem card_ballT_le (a : Lam 2 L N) (k : ℕ) :
    ((ballT a k).card : ℝ) ≤ 9 * ((L : ℝ) ^ (k + 1)) ^ 2 := by
  have h := card_ball_le (d := 2) (L := L) (N := N) a (L ^ (k + 1))
  have h' : ((ballT a k).card : ℝ) ≤ ((2 * L ^ (k + 1) + 1) ^ 2 : ℕ) := by exact_mod_cast h
  have hk1 : (1 : ℝ) ≤ (L : ℝ) ^ (k + 1) := by
    have : 1 ≤ L ^ (k + 1) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
    exact_mod_cast this
  push_cast at h'
  nlinarith

/-- Outside the ball of radius `L^{k+1}` the gradient legs at `a` vanish. -/
theorem cov_zero_far (hC : GoodCov2 k ℓC C) (hkN : k + 1 < N) (a z : Lam 2 L N)
    (hz : z ∉ ballT a k) (e : Dir 2) :
    C a z = 0 ∧ C z a = 0 ∧ C a (z + dirVec e) = 0 ∧ C (z + dirVec e) a = 0 := by
  simp only [mem_filter, mem_univ, true_and, not_le] at hz
  have hz' : L ^ (k + 1) + 1 ≤ supNorm (z - a) := hz
  have hze : L ^ (k + 1) ≤ supNorm (z + dirVec e - a) := by
    have h1 : z - a = (z + dirVec e - a) + -dirVec e := by abel
    have h2 := supNorm_add_le (z + dirVec e - a) (-dirVec e : Lam 2 L N)
    rw [← h1, supNorm_neg] at h2
    have h3 := supNorm_dirVec_le (d := 2) (n := L ^ N) e
    omega
  have hL0 : (0 : ℝ) ≤ (L : ℝ) ^ (k + 1) := by positivity
  have far : ∀ x y : Lam 2 L N, L ^ (k + 1) ≤ supNorm (x - y) → C x y = 0 := by
    intro x y hxy
    refine hC.range hkN x y ?_
    have : ((L ^ (k + 1) : ℕ) : ℝ) ≤ (supNorm (x - y) : ℝ) := by exact_mod_cast hxy
    push_cast at this
    linarith
  refine ⟨far a z ?_, far z a (by omega), far a (z + dirVec e) ?_, far (z + dirVec e) a hze⟩
  · rw [supNorm_sub_comm]; omega
  · rw [supNorm_sub_comm]; exact hze

/-- A sum supported in the ball. -/
theorem norm_sum_ball_le (a : Lam 2 L N) (k : ℕ) (f : Lam 2 L N → ℂ) {M : ℝ}
    (hf : ∀ z ∉ ballT a k, f z = 0) (hM : ∀ z, ‖f z‖ ≤ M) :
    ‖∑ z, f z‖ ≤ 9 * ((L : ℝ) ^ (k + 1)) ^ 2 * M := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM a)
  rw [← sum_subset (subset_univ (ballT a k)) (fun z _ hz => hf z hz)]
  calc ‖∑ z ∈ ballT a k, f z‖ ≤ ∑ z ∈ ballT a k, ‖f z‖ := norm_sum_le _ _
    _ ≤ ∑ z ∈ ballT a k, M := sum_le_sum fun z _ => hM z
    _ = (ballT a k).card * M := by rw [sum_const, nsmul_eq_mul]
    _ ≤ 9 * ((L : ℝ) ^ (k + 1)) ^ 2 * M :=
        mul_le_mul_of_nonneg_right (card_ballT_le a k) hM0

end Good

/-! ### The bubble and the row sums -/

section Bubble

variable {k j : ℕ} {ℓC ℓΓ : ℝ} {C Γ : Matrix (Lam 2 L N) (Lam 2 L N) ℂ}

theorem norm_gpX_le (hC : GoodCov2 k ℓC C) (hΓ : GoodCov2 j ℓΓ Γ) (a : Lam 2 L N) (e : Dir 2)
    (z : Lam 2 L N) :
    ‖gpX C Γ a e z‖ ≤ 2 * (ℓC ^ 2 / (L : ℝ) ^ (k + 1)) * (ℓΓ ^ 2 / (L : ℝ) ^ (j + 1)) := by
  unfold gpX
  have h1 := good_gradR hC e a z
  have h2 := good_gradL hΓ e z a
  have h3 := good_gradR hΓ e a z
  have h4 := good_gradL hC e z a
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
  have := mul_le_mul h3 h4 (norm_nonneg _) (by positivity)
  linarith

/-- **The polarised bubble between scales**: `|𝔩_{C,Γ}(a)| ≤ 36 ℓ_C²ℓ_Γ² L^{k+1}/L^{j+1}`. -/
theorem norm_lfunX_le (hC : GoodCov2 k ℓC C) (hkN : k + 1 < N) (hΓ : GoodCov2 j ℓΓ Γ)
    (a : Lam 2 L N) :
    ‖lfunX C Γ a‖ ≤ 36 * ℓC ^ 2 * ℓΓ ^ 2 * ((L : ℝ) ^ (k + 1) / (L : ℝ) ^ (j + 1)) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set M := 2 * (ℓC ^ 2 / (L : ℝ) ^ (k + 1)) * (ℓΓ ^ 2 / (L : ℝ) ^ (j + 1)) with hMd
  have hM0 : 0 ≤ M := by positivity
  have hi : ∀ i : Fin 2, ‖∑ z, (1 / 2 : ℂ) * (gpX C Γ a (Sum.inl i) z + gpX C Γ a (Sum.inr i) z)‖ ≤
      9 * ((L : ℝ) ^ (k + 1)) ^ 2 * M := by
    intro i
    refine norm_sum_ball_le a k _ (fun z hz => ?_) (fun z => ?_)
    · obtain ⟨c1, c2, c3, c4⟩ := cov_zero_far hC hkN a z hz (Sum.inl i)
      obtain ⟨-, -, d3, d4⟩ := cov_zero_far hC hkN a z hz (Sum.inr i)
      simp only [gpX, c1, c2, c3, c4, d3, d4, sub_zero, mul_zero, zero_mul, add_zero]
    · rw [norm_mul]
      have e : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
      rw [e]
      have := (norm_add_le _ _).trans (add_le_add (norm_gpX_le hC hΓ a (Sum.inl i) z)
        (norm_gpX_le hC hΓ a (Sum.inr i) z))
      linarith
  unfold lfunX
  refine (norm_sum_le _ _).trans ?_
  rw [Fin.sum_univ_two]
  have h := add_le_add (hi 0) (hi 1)
  refine h.trans (le_of_eq ?_)
  rw [hMd]
  field_simp
  ring

theorem gpX_self (a : Lam 2 L N) (e : Dir 2) (z : Lam 2 L N) :
    gpX C C a e z = 2 * gpC C a e z := by
  simp only [gpX, gpC]; ring

theorem lfunX_self (a : Lam 2 L N) : lfunX C C a = 2 * lfunC C a := by
  unfold lfunX lfunC
  rw [mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun z _ => ?_
  rw [gpX_self, gpX_self]; ring

/-- `|𝔩_C(a)| ≤ 18 ℓ_C⁴`. -/
theorem norm_lfunC_le (hC : GoodCov2 k ℓC C) (hkN : k + 1 < N) (a : Lam 2 L N) :
    ‖lfunC C a‖ ≤ 18 * ℓC ^ 4 := by
  have h := norm_lfunX_le hC hkN hC a
  rw [lfunX_self, norm_mul] at h
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  rw [div_self (by positivity), mul_one, show ‖(2 : ℂ)‖ = 2 by norm_num] at h
  nlinarith

/-- `|rowS_C(a)| ≤ 18 L^{2(k+1)} ℓ_C²`. -/
theorem norm_rowS_le (hC : GoodCov2 k ℓC C) (hkN : k + 1 < N) (a : Lam 2 L N) :
    ‖rowS C a‖ ≤ 18 * ((L : ℝ) ^ (k + 1)) ^ 2 * ℓC ^ 2 := by
  unfold rowS
  have h1 : ‖∑ x, C a x‖ ≤ 9 * ((L : ℝ) ^ (k + 1)) ^ 2 * ℓC ^ 2 :=
    norm_sum_ball_le a k _ (fun z hz => (cov_zero_far hC hkN a z hz (Sum.inl 0)).1)
      (fun z => good_entry hC a z)
  have h2 : ‖∑ x, C x a‖ ≤ 9 * ((L : ℝ) ^ (k + 1)) ^ 2 * ℓC ^ 2 :=
    norm_sum_ball_le a k _ (fun z hz => (cov_zero_far hC hkN a z hz (Sum.inl 0)).2.1)
      (fun z => good_entry hC z a)
  have := norm_add_le (∑ x, C a x) (∑ x, C x a)
  linarith

end Bubble

/-! ### Parseval: `𝔩_{kmat w}(a) = 𝔩(w)` -/

section Parseval

open DressedFRD ComplexConjugate

variable {n : ℕ} [NeZero n]

theorem kern_shift_diff (w : Sym 2 n) (u v : Torus 2 n) :
    kern w (u + v) - kern w u =
      ((n : ℂ) ^ 2)⁻¹ * ∑ m, w m * char m u * (char m v - 1) := by
  simp only [kern, ← mul_sub, ← sum_sub_distrib, char_add_right]
  congr 1
  exact sum_congr rfl fun m _ => by ring

theorem sum_orth_pair (a b : Torus 2 n → ℂ) :
    ∑ u, (∑ m, a m * conj (char m u)) * (∑ m', b m' * char m' u) =
      (n : ℂ) ^ 2 * ∑ m, a m * b m := by
  have horth : ∀ m m' : Torus 2 n, ∑ u, conj (char m u) * char m' u =
      if m' = m then (n : ℂ) ^ 2 else 0 := by
    intro m m'
    rw [← sum_char_mul_conj m' m]
    exact sum_congr rfl fun u _ => by ring
  calc ∑ u, (∑ m, a m * conj (char m u)) * (∑ m', b m' * char m' u)
      = ∑ u, ∑ m, ∑ m', a m * b m' * (conj (char m u) * char m' u) := by
        refine sum_congr rfl fun u _ => ?_
        rw [sum_mul]
        refine sum_congr rfl fun m _ => ?_
        rw [mul_sum]
        exact sum_congr rfl fun m' _ => by ring
    _ = ∑ m, ∑ m', a m * b m' * ∑ u, conj (char m u) * char m' u := by
        rw [sum_comm]
        refine sum_congr rfl fun m _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun m' _ => ?_
        rw [mul_sum]
    _ = ∑ m, a m * b m * (n : ℂ) ^ 2 := by
        refine sum_congr rfl fun m _ => ?_
        simp only [horth, mul_ite, mul_zero]
        rw [sum_ite_eq' univ m]
        simp
    _ = _ := by rw [mul_sum]; exact sum_congr rfl fun m _ => by ring

theorem sum_gradPair (w : Sym 2 n) (v : Torus 2 n) :
    ∑ u, (kern w (-u - v) - kern w (-u)) * (kern w (u + v) - kern w u) =
      ((n : ℂ) ^ 2)⁻¹ * ∑ m, w m ^ 2 * ((‖char m v - 1‖ ^ 2 : ℝ) : ℂ) := by
  have hA : ∀ u, kern w (-u - v) - kern w (-u) =
      ((n : ℂ) ^ 2)⁻¹ * ∑ m, (w m * (conj (char m v) - 1)) * conj (char m u) := by
    intro u
    rw [show -u - v = -u + -v by abel, kern_shift_diff]
    simp only [char_neg_right]
    congr 1
    exact sum_congr rfl fun m _ => by ring
  have hB : ∀ u, kern w (u + v) - kern w u =
      ((n : ℂ) ^ 2)⁻¹ * ∑ m, (w m * (char m v - 1)) * char m u := by
    intro u
    rw [kern_shift_diff]
    congr 1
    exact sum_congr rfl fun m _ => by ring
  simp only [hA, hB]
  have hn : ((n : ℂ) ^ 2) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne n))
  have e2 : ∑ u, ((n : ℂ) ^ 2)⁻¹ * (∑ m, (w m * (conj (char m v) - 1)) * conj (char m u)) *
      (((n : ℂ) ^ 2)⁻¹ * ∑ m, (w m * (char m v - 1)) * char m u) =
      ((n : ℂ) ^ 2)⁻¹ * ((n : ℂ) ^ 2)⁻¹ * ∑ u, (∑ m, (w m * (conj (char m v) - 1)) *
        conj (char m u)) * (∑ m, (w m * (char m v - 1)) * char m u) := by
    rw [mul_sum]; exact sum_congr rfl fun u _ => by ring
  rw [e2, sum_orth_pair]
  have e3 : ∀ m, w m * (conj (char m v) - 1) * (w m * (char m v - 1)) =
      w m ^ 2 * ((‖char m v - 1‖ ^ 2 : ℝ) : ℂ) := by
    intro m
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sub, map_one]; ring
  simp only [e3]
  field_simp

theorem norm_char_neg_sub_one (m v : Torus 2 n) : ‖char m (-v) - 1‖ = ‖char m v - 1‖ := by
  rw [char_neg_right, show conj (char m v) - 1 = conj (char m v - 1) by simp, Complex.norm_conj]

end Parseval

section Parseval2

open DressedFRD ComplexConjugate

/-- **Parseval for the bubble**: `𝔩_{kmat w}(a) = 𝔩(w)`. -/
theorem lfunC_kmat (w : Sym 2 (L ^ N)) (a : Lam 2 L N) : lfunC (kmat w) a = Step2.D2.lc w := by
  have hg : ∀ (e : Dir 2) (z : Lam 2 L N), gpC (kmat w) a e z =
      (kern w (-(z - a) - dirVec e) - kern w (-(z - a))) *
        (kern w ((z - a) + dirVec e) - kern w (z - a)) := by
    intro e z
    simp only [gpC, kmat]
    congr 2 <;> congr 1 <;> abel
  have hs : ∀ e : Dir 2, ∑ z, gpC (kmat w) a e z =
      (((L ^ N : ℕ) : ℂ) ^ 2)⁻¹ * ∑ m, w m ^ 2 * ((‖char m (dirVec e) - 1‖ ^ 2 : ℝ) : ℂ) := by
    intro e
    simp only [hg]
    rw [← sum_gradPair w (dirVec e)]
    exact Fintype.sum_equiv (Equiv.subRight a) _ _ (fun z => rfl)
  unfold lfunC Step2.D2.lc Step2.D2.bl
  have e1 : ∀ i : Fin 2, ∑ z, (1 / 2 : ℂ) * (gpC (kmat w) a (Sum.inl i) z +
      gpC (kmat w) a (Sum.inr i) z) =
      (((L ^ N : ℕ) : ℂ) ^ 2)⁻¹ * ∑ m, w m ^ 2 * ((‖char m (dirVec (Sum.inl i)) - 1‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [← mul_sum, sum_add_distrib, hs, hs]
    have : ∀ m, ‖char m (dirVec (Sum.inr i) : Lam 2 L N) - 1‖ =
        ‖char m (dirVec (Sum.inl i)) - 1‖ := by
      intro m
      rw [FRD.dirVec_inr, FRD.dirVec_inl, norm_char_neg_sub_one]
    simp only [this]
    ring
  simp only [e1]
  rw [← mul_sum]
  congr 1
  rw [sum_comm]
  refine sum_congr rfl fun m _ => ?_
  rw [← mul_sum, FRD.lam]
  have hl : ∑ i : Fin 2, ((‖char m (dirVec (Sum.inl i)) - 1‖ ^ 2 : ℝ) : ℂ) =
      (((∑ i : Fin 2, (2 - 2 * cosk m i)) : ℝ) : ℂ) := by
    have := DressedFRD.lam_eq_sum (d := 2) (n := L ^ N) m
    rw [FRD.lam] at this
    rw [this]; push_cast; rfl
  rw [hl]; ring

end Parseval2

end

end Obs2
