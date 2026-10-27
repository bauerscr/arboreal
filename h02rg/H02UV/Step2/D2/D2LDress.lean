import Step2.D2.D2Dress
import Step2.D2.D2Lval

/-!
# The dressing of `𝔩` (`prop:d2`, second line, `ζ ≠ 0`)

On the torus (`d = 2`), for symbols `u, v : Sym 2 n`:
`⟨u, v⟩_𝔩 = ⨍ λ u v` (`bl`), `𝔩(w) = ⟨w, w⟩_𝔩` (`lc`).

The dressed covariances of `DressedFRD` (`thm:main`) are
`C'_k = Z_k Γ^int_k` (`Cp`), and the dressed accumulated covariance is
`w'_j = ∑_{k ≤ j} (Z_{j+1}/Z_k) C'_k` (`wp`), with `w'_{j+1} = w'_j + C'_{j+1}` (`e:Cw`).

* `bl_le_sup_avg`, `bl_le_sup_lam`: `|⟨u,v⟩| ≤ sup|λu| ⨍|v|` and `≤ sup|u| ⨍ λ|v|`;
* `avg_norm_le_snorm`, `avg_lam_le_snorm`: `⨍|v| ≤ ‖v‖_{(s)}`, `⨍ λ|v| ≤ 2 L^{-2s} ‖v‖_{(s)}`;
* `sup_le_of_rng`: `sup|w| ≤ L^{2k} sup_x|k_w(x)|` if `2 rng w < L^k`;
* `lc_dress`: **`|(𝔩(w'_j + C'_{j+1}) - 𝔩(w'_j)) - (𝔩(w_j + C_{j+1}) - 𝔩(w_j))| ≤ M_z (4K +
  2 L² K² M_z + 8 (K + c_S)(c_S + K M_z))`**, `M_z = |ζ|_{≤ j}`, uniformly in `j`.
-/

namespace Step2.D2

noncomputable section

open Finset FRD DressedFRD DressedFRD.Data

variable {n : ℕ} [NeZero n]

/-- `⟨u, v⟩_𝔩 = ⨍ λ u v`. -/
def bl (u v : Sym 2 n) : ℂ := ((n : ℂ) ^ 2)⁻¹ * ∑ m, (lam m : ℂ) * u m * v m

/-- `𝔩(w) = ⨍ λ ŵ²`. -/
def lc (w : Sym 2 n) : ℂ := bl w w

theorem bl_comm (u v : Sym 2 n) : bl u v = bl v u := by
  simp only [bl]; congr 1; exact sum_congr rfl fun m _ => by ring

theorem bl_add_left (u u' v : Sym 2 n) : bl (u + u') v = bl u v + bl u' v := by
  simp only [bl, Pi.add_apply, ← mul_add, ← sum_add_distrib]
  congr 1; exact sum_congr rfl fun m _ => by ring

theorem bl_add_right (u v v' : Sym 2 n) : bl u (v + v') = bl u v + bl u v' := by
  rw [bl_comm, bl_add_left, bl_comm v, bl_comm v']

theorem bl_sub_left (u u' v : Sym 2 n) : bl (u - u') v = bl u v - bl u' v := by
  simp only [bl, Pi.sub_apply, ← mul_sub, ← sum_sub_distrib]
  congr 1; exact sum_congr rfl fun m _ => by ring

theorem bl_smul_left (c : ℂ) (u v : Sym 2 n) : bl (c • u) v = c * bl u v := by
  simp only [bl, Pi.smul_apply, smul_eq_mul, mul_sum]
  exact sum_congr rfl fun m _ => by ring

theorem bl_sum_left {ι : Type*} (s : Finset ι) (u : ι → Sym 2 n) (v : Sym 2 n) :
    bl (∑ i ∈ s, u i) v = ∑ i ∈ s, bl (u i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [bl]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, bl_add_left, ih]

theorem lc_add_sub (a b : Sym 2 n) : lc (a + b) - lc a = 2 * bl a b + bl b b := by
  simp only [lc, bl_add_left, bl_add_right, bl_comm b a]; ring

/-- The dressing identity `(𝔩(a+b) - 𝔩(a)) - (𝔩(a₀+b₀) - 𝔩(a₀))
= 2⟨a - a₀, b⟩ + 2⟨a₀, b - b₀⟩ + ⟨b - b₀, b - b₀⟩ + 2⟨b₀, b - b₀⟩`. -/
theorem lc_dress_identity (a b a0 b0 : Sym 2 n) :
    (lc (a + b) - lc a) - (lc (a0 + b0) - lc a0) =
      2 * bl (a - a0) b + 2 * bl a0 (b - b0) + bl (b - b0) (b - b0) + 2 * bl b0 (b - b0) := by
  rw [lc_add_sub, lc_add_sub]
  have e1 := bl_sub_left a a0 b
  have e2 : bl a0 (b - b0) = bl a0 b - bl a0 b0 := by
    rw [bl_comm, bl_sub_left, bl_comm b, bl_comm b0]
  have e3 : bl (b - b0) (b - b0) = bl b b - 2 * bl b0 b + bl b0 b0 := by
    rw [bl_sub_left, bl_comm b (b - b0), bl_comm b0 (b - b0), bl_sub_left, bl_sub_left,
      bl_comm b0 b]; ring
  have e4 : bl b0 (b - b0) = bl b0 b - bl b0 b0 := by
    rw [bl_comm, bl_sub_left, bl_comm b]
  rw [e1, e2, e3, e4, bl_comm a0 b0]; ring

/-! ### Elementary bounds -/

theorem avg_eq (f : Grassmann.Torus 2 n → ℝ) : avg f = ((n : ℝ) ^ 2)⁻¹ * ∑ m, f m := rfl

theorem norm_bl_le (u v : Sym 2 n) :
    ‖bl u v‖ ≤ avg fun m => ‖(lam m : ℂ) * u m‖ * ‖v m‖ := by
  rw [bl, avg_eq, norm_mul]
  have : ‖((n : ℂ) ^ 2)⁻¹‖ = ((n : ℝ) ^ 2)⁻¹ := by simp
  rw [this]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum_le_sum fun m _ => ?_))
    (by positivity)
  rw [norm_mul]

/-- `|⟨u, v⟩| ≤ sup|λ u| ⨍|v|`. -/
theorem bl_le_sup_avg {u v : Sym 2 n} {A : ℝ} (hu : ∀ m, ‖(lam m : ℂ) * u m‖ ≤ A) :
    ‖bl u v‖ ≤ A * avg fun m => ‖v m‖ := by
  refine (norm_bl_le u v).trans ?_
  rw [← avg_smul]
  exact avg_mono fun m => mul_le_mul_of_nonneg_right (hu m) (norm_nonneg _)

/-- `|⟨u, v⟩| ≤ sup|u| ⨍ λ|v|`. -/
theorem bl_le_sup_lam {u v : Sym 2 n} {A : ℝ} (hu : ∀ m, ‖u m‖ ≤ A) :
    ‖bl u v‖ ≤ A * avg fun m => lam m * ‖v m‖ := by
  refine (norm_bl_le u v).trans ?_
  rw [← avg_smul]
  refine avg_mono fun m => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (lam_nonneg' m)]
  have := lam_nonneg' m
  calc lam m * ‖u m‖ * ‖v m‖ = ‖u m‖ * (lam m * ‖v m‖) := by ring
    _ ≤ A * (lam m * ‖v m‖) := mul_le_mul_of_nonneg_right (hu m) (by positivity)

/-- `⨍ |v| ≤ ‖v‖_{(s)}` in `d = 2`. -/
theorem avg_norm_le_snorm {L : ℝ} (hL : 0 < L) (q s : ℕ) (v : Sym 2 n) :
    avg (fun m => ‖v m‖) ≤ snorm L q s v := by
  have h := le_snorm (L := L) (q := q) (s := s) (α := 0) (by simp [Grassmann.mabs]) v
  rw [wgt_two_zero, one_mul, mom] at h
  simpa [sigma_zero] using h

/-- The multi-index `2 e_i`. -/
def al2 (i : Fin 2) : Grassmann.Dir 2 → ℕ := Pi.single (Sum.inl i) 2

theorem mabs_al2 (i : Fin 2) : Grassmann.mabs (al2 i) = 2 := by
  simp [Grassmann.mabs, al2, Finset.sum_pi_single']

theorem norm_char_sub_one_sq (m : Grassmann.Torus 2 n) (i : Fin 2) :
    ‖FRD.char m (FRD.unitT i) - 1‖ ^ 2 = 2 - 2 * cosk m i := by
  rw [char_unitT, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  have h1 := re_stdAddChar (co m i)
  have h2 : ‖ZMod.stdAddChar (co m i)‖ = 1 := by
    have := FRD.norm_char m (FRD.unitT i); rwa [char_unitT] at this
  have h3 : (ZMod.stdAddChar (co m i) : ℂ).re * (ZMod.stdAddChar (co m i) : ℂ).re +
      (ZMod.stdAddChar (co m i) : ℂ).im * (ZMod.stdAddChar (co m i) : ℂ).im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, h2]; norm_num
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
  rw [cosk, ← h1]
  nlinarith

theorem norm_sigma_al2 (m : Grassmann.Torus 2 n) (i : Fin 2) :
    ‖sigma (al2 i) m‖ = 2 - 2 * cosk m i := by
  rw [sigma, Finset.prod_eq_single (Sum.inl i)]
  · simp only [al2, Pi.single_eq_same, norm_pow]
    rw [show (Grassmann.dirVec (Sum.inl i) : Grassmann.Torus 2 n) = FRD.unitT i from rfl,
      norm_char_sub_one_sq]
  · intro e _ he; simp [al2, he]
  · simp

theorem lam_eq_sigma (m : Grassmann.Torus 2 n) :
    lam m = ‖sigma (al2 0) m‖ + ‖sigma (al2 1) m‖ := by
  rw [norm_sigma_al2, norm_sigma_al2, lam, Fin.sum_univ_two]

/-- `⨍ λ|v| ≤ 2 L^{-2s} ‖v‖_{(s)}` (`2 ≤ q`, `d = 2`). -/
theorem avg_lam_le_snorm {L : ℝ} (hL : 0 < L) {q : ℕ} (hq : 2 ≤ q) (s : ℕ) (v : Sym 2 n) :
    avg (fun m => lam m * ‖v m‖) ≤ 2 * (L ^ (2 * s))⁻¹ * snorm L q s v := by
  have hw : ∀ i, wgt 2 L s (al2 i) = L ^ (2 * s) := by
    intro i
    rw [wgt, mabs_al2]
    rw [show ((s : ℝ) * ((2 : ℕ) - 2 + ((2 : ℕ) : ℝ))) = ((2 * s : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
  have hb : ∀ i, mom (al2 i) v ≤ (L ^ (2 * s))⁻¹ * snorm L q s v := by
    intro i
    have := le_snorm (L := L) (q := q) (s := s) (α := al2 i) (by rw [mabs_al2]; exact hq) v
    rw [hw] at this
    rw [le_inv_mul_iff₀ (by positivity)]; exact this
  have e : (fun m => lam m * ‖v m‖) = (fun m => ‖sigma (al2 0) m‖ * ‖v m‖) +
      (fun m => ‖sigma (al2 1) m‖ * ‖v m‖) := by
    funext m; simp only [Pi.add_apply]; rw [lam_eq_sigma]; ring
  rw [e, avg_add]
  have h0 := hb 0; have h1 := hb 1
  simp only [mom] at h0 h1
  linarith

/-- `sup|w| ≤ L^{2k} sup_x|k_w(x)|` if `2 rng w < L^k`. -/
theorem sup_le_of_rng {w : Sym 2 n} {L k : ℕ} (hr : 2 * rng w < L ^ k) {B : ℝ}
    (hB : ∀ x, ‖kern w x‖ ≤ B) (m : Grassmann.Torus 2 n) :
    ‖w m‖ ≤ ((L : ℝ) ^ k) ^ 2 * B := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  refine (norm_le_sum_kern w m).trans ((sum_kern_le w hB).trans ?_)
  have : ((2 * rng w + 1 : ℕ) : ℝ) ≤ ((L ^ k : ℕ) : ℝ) := by exact_mod_cast hr
  push_cast at this
  gcongr

/-! ### Products `∏ (1 + ζ_i)` -/

theorem prod_one_add_bounds (s : Finset ℕ) (a : ℕ → ℂ) {x : ℝ} (hx : 0 ≤ x)
    (h : ∀ i ∈ s, ‖a i‖ ≤ x) :
    ‖∏ i ∈ s, (1 + a i)‖ ≤ (1 + x) ^ s.card ∧ ‖∏ i ∈ s, (1 + a i) - 1‖ ≤ (1 + x) ^ s.card - 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih =>
    obtain ⟨h1, h2⟩ := ih fun i hi => h i (mem_insert_of_mem hi)
    have hab : ‖a b‖ ≤ x := h b (mem_insert_self b s)
    have h1b : ‖1 + a b‖ ≤ 1 + x := (norm_add_le _ _).trans (by simp; linarith)
    rw [prod_insert hb, card_insert_of_notMem hb, pow_succ]
    have hp : 0 ≤ (1 + x) ^ s.card := by positivity
    constructor
    · rw [norm_mul]
      calc ‖1 + a b‖ * ‖∏ i ∈ s, (1 + a i)‖ ≤ (1 + x) * (1 + x) ^ s.card :=
            mul_le_mul h1b h1 (norm_nonneg _) (by linarith)
        _ = _ := by ring
    · have e : (1 + a b) * ∏ i ∈ s, (1 + a i) - 1 = (1 + a b) * (∏ i ∈ s, (1 + a i) - 1) + a b := by
        ring
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul]
      calc ‖1 + a b‖ * ‖∏ i ∈ s, (1 + a i) - 1‖ + ‖a b‖ ≤ (1 + x) * ((1 + x) ^ s.card - 1) + x :=
            add_le_add (mul_le_mul h1b h2 (norm_nonneg _) (by linarith)) hab
        _ = _ := by ring

theorem one_add_pow_sub_one_le {x : ℝ} (hx : 0 ≤ x) (m : ℕ) :
    (1 + x) ^ m - 1 ≤ m * x * (1 + x) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hp : 1 ≤ (1 + x) ^ m := one_le_pow₀ (by linarith)
    calc (1 + x) ^ (m + 1) - 1 = (1 + x) * ((1 + x) ^ m - 1) + x := by ring
      _ ≤ (1 + x) * (m * x * (1 + x) ^ m) + x * (1 + x) ^ (m + 1) := by
          have h1 := mul_le_mul_of_nonneg_left ih (by linarith : (0 : ℝ) ≤ 1 + x)
          have : 1 ≤ (1 + x) ^ (m + 1) := one_le_pow₀ (by linarith)
          have h2 : x ≤ x * (1 + x) ^ (m + 1) := by nlinarith
          linarith
      _ = ((m + 1 : ℕ) : ℝ) * x * (1 + x) ^ (m + 1) := by push_cast; ring

theorem geom_Icc_le (j : ℕ) : ∑ k ∈ Icc 1 j, ((9 : ℝ) / 16) ^ (j - k) ≤ 16 / 7 := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    rw [sum_Icc_succ_top (by omega), Nat.sub_self, pow_zero]
    have e : ∑ k ∈ Icc 1 j, ((9 : ℝ) / 16) ^ (j + 1 - k) =
        9 / 16 * ∑ k ∈ Icc 1 j, ((9 : ℝ) / 16) ^ (j - k) := by
      rw [mul_sum]
      refine sum_congr rfl fun k hk => ?_
      rw [show j + 1 - k = (j - k) + 1 by have := (mem_Icc.1 hk).2; omega, pow_succ]; ring
    rw [e]; linarith

/-- The coefficient bounds: for `k ≤ j`, `L ≥ 2`, `0 ≤ x ≤ 1/8`, `m = j + 1 - k`:
`(1+x)^m L^{2k}/L^{2j} ≤ (9/8)(9/16)^{j-k}` and `m (1+x)^m L^{2k}/L^{2j} ≤ (9/8)(9/16)^{j-k}`. -/
theorem coef_bound {L x : ℝ} (hL : 2 ≤ L) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 8) {k j : ℕ} (hk : k ≤ j) :
    ((j + 1 - k : ℕ) : ℝ) * (1 + x) ^ (j + 1 - k) * ((L ^ k) ^ 2 * ((L ^ j) ^ 2)⁻¹) ≤
        9 / 8 * (9 / 16) ^ (j - k) ∧
      (1 + x) ^ (j + 1 - k) * ((L ^ k) ^ 2 * ((L ^ j) ^ 2)⁻¹) ≤ 9 / 8 * (9 / 16) ^ (j - k) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
  have ht : k + t + 1 - k = t + 1 := by omega
  have ht' : k + t - k = t := by omega
  rw [ht, ht']
  have hL0 : 0 < L := by linarith
  have hLk : (L ^ k) ^ 2 * ((L ^ (k + t)) ^ 2)⁻¹ = ((L ^ 2) ^ t)⁻¹ := by
    rw [pow_add]; field_simp; ring
  rw [hLk]
  have h4 : (4 : ℝ) ^ t ≤ (L ^ 2) ^ t := pow_le_pow_left₀ (by norm_num) (by nlinarith) t
  have hinv : ((L ^ 2) ^ t)⁻¹ ≤ ((4 : ℝ) ^ t)⁻¹ := inv_anti₀ (by positivity) h4
  have hx1 : (1 + x) ^ (t + 1) ≤ (9 / 8) ^ (t + 1) := pow_le_pow_left₀ (by linarith) (by linarith) _
  have h2t : ((t + 1 : ℕ) : ℝ) ≤ 2 ^ t := by
    have : t + 1 ≤ 2 ^ t := Nat.lt_two_pow_self
    exact_mod_cast this
  have key : (9 / 8 : ℝ) ^ (t + 1) * ((4 : ℝ) ^ t)⁻¹ * 2 ^ t = 9 / 8 * (9 / 16) ^ t := by
    rw [pow_succ, ← inv_pow, mul_comm ((9 / 8 : ℝ) ^ t), mul_assoc, mul_assoc, ← mul_pow, ← mul_pow]
    norm_num
  have hp : 0 ≤ (1 + x) ^ (t + 1) := by positivity
  constructor
  · calc ((t + 1 : ℕ) : ℝ) * (1 + x) ^ (t + 1) * ((L ^ 2) ^ t)⁻¹
        ≤ 2 ^ t * (9 / 8) ^ (t + 1) * ((4 : ℝ) ^ t)⁻¹ := by gcongr
      _ = 9 / 8 * (9 / 16) ^ t := by rw [← key]; ring
  · calc (1 + x) ^ (t + 1) * ((L ^ 2) ^ t)⁻¹ ≤ (9 / 8) ^ (t + 1) * ((4 : ℝ) ^ t)⁻¹ * 1 := by
          rw [mul_one]; gcongr
      _ ≤ (9 / 8) ^ (t + 1) * ((4 : ℝ) ^ t)⁻¹ * 2 ^ t := by
          gcongr; exact one_le_pow₀ (by norm_num)
      _ = 9 / 8 * (9 / 16) ^ t := key

/-! ### The dressing of `𝔩` -/

/-- `C'_k = Z_k Γ^int_k` (`Gint (k-1)` is `Γ^int_k`). -/
def Cp (D : Data 2 n) (k : ℕ) : Sym 2 n := D.Z k • D.Gint (k - 1)

/-- `w'_j = ∑_{k ≤ j} (Z_{j+1}/Z_k) C'_k`. -/
def wp (D : Data 2 n) (j : ℕ) : Sym 2 n := ∑ k ∈ Icc 1 j, (D.Z (j + 1) / D.Z k) • Cp D k

theorem sup_bound_of_snorm {w : Sym 2 n} {L k : ℕ} (hL : 0 < (L : ℝ)) (q s : ℕ)
    (hr : 2 * rng w < L ^ k) {B : ℝ} (hs : snorm L q s w ≤ B) (m : Grassmann.Torus 2 n) :
    ‖w m‖ ≤ ((L : ℝ) ^ k) ^ 2 * B :=
  sup_le_of_rng hr (fun x => (norm_kern_le_snorm hL q s w x).trans hs) m

theorem Z_ratio_eq (D : Data 2 n) (hζ : ∀ i, ‖D.ζ i‖ ≤ 1 / 2) {k j : ℕ} (hk : k ≤ j + 1) :
    D.Z (j + 1) / D.Z k = ∏ i ∈ Ico k (j + 1), (1 + D.ζ i) := by
  rw [div_eq_iff (Z_ne_zero hζ k), Z, Z, ← prod_range_mul_prod_Ico _ hk, mul_comm]

variable (D : Data 2 n) {q M : ℕ} {cS K : ℝ}

/-- **The dressing of `𝔩`.** With `C'_{j+1}` and `w'_j` from `DressedFRD`
(`Z_{j+1} Γ^int_{j+1} - C_{j+1}` small in `‖·‖_{(j)}`, `thm:main`(iv)), uniformly in `j`:
`|(𝔩(w'_j + C'_{j+1}) - 𝔩(w'_j)) - (𝔩(w_j + C_{j+1}) - 𝔩(w_j))|
  ≤ M_z (4K + 2 L² K² M_z + 12 (K + c_S)(K M_z + c_S))`, `M_z = |ζ|_{≤ j}`. -/
theorem lc_dress (hq : 2 ≤ q) (hL : 2 ≤ D.L) (hS : StdFull D.L D.N q M D.msq cS D.C)
    (hζ : ∀ i, ‖D.ζ i‖ ≤ 1 / 8) (hK : 0 ≤ K)
    (hclose : ∀ i, i + 1 < D.N →
      snorm D.L q i (D.Z (i + 1) • D.Gint i - ofR (D.C (i + 1))) ≤ K * D.Mz (i + 1))
    (hrange : ∀ i, i + 1 < D.N → 2 * rng (D.Gint i) < D.L ^ (i + 1))
    {j : ℕ} (hj : 1 ≤ j) (hjN : j + 1 < D.N) :
    ‖(lc (wp D j + Cp D (j + 1)) - lc (wp D j)) -
        (lc (Cle D.C j + ofR (D.C (j + 1))) - lc (Cle D.C j))‖ ≤
      D.Mz (j + 1) * (4 * K + 2 * (D.L : ℝ) ^ 2 * K ^ 2 * D.Mz (j + 1) +
        12 * (K + cS) * (K * D.Mz (j + 1) + cS)) := by
  set Lr : ℝ := (D.L : ℝ)
  have hL0 : 0 < Lr := by simp only [Lr]; exact_mod_cast (by omega : 0 < D.L)
  have hL2 : (2 : ℝ) ≤ Lr := by simp only [Lr]; exact_mod_cast hL
  have hL1 : 1 ≤ D.L := by omega
  have hζ2 : ∀ i, ‖D.ζ i‖ ≤ 1 / 2 := fun i => (hζ i).trans (by norm_num)
  set Mz := D.Mz (j + 1)
  have hMz0 : 0 ≤ Mz := Mz_nonneg _
  have hMz : Mz ≤ 1 / 8 := Mz_le (by norm_num) fun i _ => hζ i
  have hcS := hS.hcS
  set δ : ℕ → Sym 2 n := fun k => Cp D k - ofR (D.C k)
  -- bounds on `δ_k` and `C_k`
  have hδsn : ∀ k, 1 ≤ k → k < D.N → snorm Lr q (k - 1) (δ k) ≤ K * D.Mz k := by
    intro k hk1 hkN
    have := hclose (k - 1) (by omega)
    rwa [show k - 1 + 1 = k by omega] at this
  have hrngδ : ∀ k, 1 ≤ k → k < D.N → 2 * rng (δ k) < D.L ^ k := by
    intro k hk1 hkN
    have h1 := hrange (k - 1) (by omega)
    rw [show k - 1 + 1 = k by omega] at h1
    have h2 := hS.base.range k hk1 hkN
    have h3 : rng (δ k) ≤ max (rng (Cp D k)) (rng (ofR (D.C k))) := rng_sub_le _ _
    have h4 : rng (Cp D k) ≤ rng (D.Gint (k - 1)) := rng_smul_le _ _
    omega
  have hδsup : ∀ k, 1 ≤ k → k < D.N → k ≤ j + 1 → ∀ m, ‖δ k m‖ ≤ (Lr ^ k) ^ 2 * (K * Mz) := by
    intro k hk1 hkN hkj m
    refine (sup_bound_of_snorm hL0 q (k - 1) (hrngδ k hk1 hkN) (hδsn k hk1 hkN) m).trans ?_
    gcongr
    exact Mz_mono (by omega)
  have hCsup : ∀ k, 1 ≤ k → k < D.N → ∀ m, ‖ofR (D.C k) m‖ ≤ (Lr ^ k) ^ 2 * cS := fun k hk1 hkN m =>
    sup_bound_of_snorm hL0 q (k - 1) (hS.base.range k hk1 hkN) (std_c hS hL1 hk1 hkN) m
  -- `λ C_{≤j} ≤ 1` and `λ C_{j+1} ≤ 1`
  have hlam : ∀ (s : Finset ℕ), s ⊆ Icc 1 D.N → ∀ m,
      ‖(lam m : ℂ) * ((∑ k ∈ s, D.C k m : ℝ) : ℂ)‖ ≤ 1 := by
    intro s hs m
    rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs]
    have hp := lam_add_pos hS.base m
    have h0 : 0 ≤ ∑ k ∈ s, D.C k m := sum_nonneg fun k _ => hS.base.nonneg k m
    have h1 : ∑ k ∈ s, D.C k m ≤ (lam m + D.msq)⁻¹ := by
      rw [← hS.base.sum_eq m]
      exact sum_le_sum_of_subset_of_nonneg hs fun k _ _ => hS.base.nonneg k m
    rw [abs_of_nonneg (mul_nonneg (lam_nonneg' m) h0)]
    calc lam m * ∑ k ∈ s, D.C k m ≤ (lam m + D.msq) * (lam m + D.msq)⁻¹ := by
          gcongr; linarith [hS.base.msq_pos]
      _ = 1 := mul_inv_cancel₀ hp.ne'
  have hlamCle : ∀ m, ‖(lam m : ℂ) * Cle D.C j m‖ ≤ 1 := fun m => by
    rw [Cle_apply]; exact hlam _ (Icc_subset_Icc le_rfl (by omega)) m
  have hlamC1 : ∀ m, ‖(lam m : ℂ) * ofR (D.C (j + 1)) m‖ ≤ 1 := fun m => by
    have := hlam {j + 1} (by intro k hk; rw [mem_singleton] at hk; rw [hk, mem_Icc]; omega) m
    simpa [ofR] using this
  -- the averages
  have havgδ : avg (fun m => ‖δ (j + 1) m‖) ≤ K * Mz :=
    (avg_norm_le_snorm hL0 q j _).trans (by
      have := hδsn (j + 1) (by omega) hjN; simpa using this)
  have havgLd : avg (fun m => lam m * ‖δ (j + 1) m‖) ≤ 2 * ((Lr ^ j) ^ 2)⁻¹ * (K * Mz) := by
    refine (avg_lam_le_snorm hL0 hq j _).trans ?_
    rw [show Lr ^ (2 * j) = (Lr ^ j) ^ 2 by ring]
    gcongr
    have := hδsn (j + 1) (by omega) hjN; simpa using this
  have havgLC : avg (fun m => lam m * ‖ofR (D.C (j + 1)) m‖) ≤ 2 * ((Lr ^ j) ^ 2)⁻¹ * cS := by
    refine (avg_lam_le_snorm hL0 hq j _).trans ?_
    rw [show Lr ^ (2 * j) = (Lr ^ j) ^ 2 by ring]
    gcongr
    have := std_c hS hL1 (k := j + 1) (by omega) hjN; simpa using this
  set b := Cp D (j + 1)
  have hb : b = δ (j + 1) + ofR (D.C (j + 1)) := by simp [δ, b]
  have havgLb : avg (fun m => lam m * ‖b m‖) ≤ 2 * ((Lr ^ j) ^ 2)⁻¹ * (K * Mz + cS) := by
    have : avg (fun m => lam m * ‖b m‖) ≤ avg (fun m => lam m * ‖δ (j + 1) m‖) +
        avg (fun m => lam m * ‖ofR (D.C (j + 1)) m‖) := by
      rw [← avg_add]
      refine avg_mono fun m => ?_
      simp only [Pi.add_apply, hb]
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (lam_nonneg' m)
    linarith
  -- the four terms
  have T1 : ‖bl (Cle D.C j) (δ (j + 1))‖ ≤ K * Mz :=
    (bl_le_sup_avg hlamCle).trans (by linarith)
  have T4 : ‖bl (ofR (D.C (j + 1))) (δ (j + 1))‖ ≤ K * Mz :=
    (bl_le_sup_avg hlamC1).trans (by linarith)
  have T3 : ‖bl (δ (j + 1)) (δ (j + 1))‖ ≤ 2 * Lr ^ 2 * K ^ 2 * Mz ^ 2 := by
    refine (bl_le_sup_lam (hδsup (j + 1) (by omega) hjN le_rfl)).trans ?_
    have hpos : 0 ≤ (Lr ^ (j + 1)) ^ 2 * (K * Mz) := by positivity
    calc (Lr ^ (j + 1)) ^ 2 * (K * Mz) * avg (fun m => lam m * ‖δ (j + 1) m‖)
        ≤ (Lr ^ (j + 1)) ^ 2 * (K * Mz) * (2 * ((Lr ^ j) ^ 2)⁻¹ * (K * Mz)) := by gcongr
      _ = 2 * Lr ^ 2 * K ^ 2 * Mz ^ 2 := by field_simp; ring
  -- the term `⟨w'_j - w_j, C'_{j+1}⟩`
  set ρ : ℕ → ℂ := fun k => D.Z (j + 1) / D.Z k
  have hdec : wp D j - Cle D.C j =
      ∑ k ∈ Icc 1 j, (ρ k • δ k + (ρ k - 1) • ofR (D.C k)) := by
    simp only [wp, Cle, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ => ?_
    simp only [δ, ρ, smul_sub, sub_smul, one_smul]; abel
  have hρ : ∀ k ∈ Icc 1 j, ‖ρ k‖ ≤ (1 + Mz) ^ (j + 1 - k) ∧
      ‖ρ k - 1‖ ≤ ((j + 1 - k : ℕ) : ℝ) * Mz * (1 + Mz) ^ (j + 1 - k) := by
    intro k hk
    have hk' := mem_Icc.1 hk
    have e := Z_ratio_eq D hζ2 (k := k) (j := j) (by omega)
    have hb' := prod_one_add_bounds (Ico k (j + 1)) D.ζ hMz0
      (fun i hi => norm_le_Mz (mem_Ico.1 hi).2)
    rw [Nat.card_Ico] at hb'
    simp only [ρ]
    rw [e]
    exact ⟨hb'.1, hb'.2.trans (one_add_pow_sub_one_le hMz0 _)⟩
  have T2 : ‖bl (wp D j - Cle D.C j) b‖ ≤ 6 * Mz * (K + cS) * (K * Mz + cS) := by
    rw [hdec, bl_sum_left]
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ k ∈ Icc 1 j, ‖bl (ρ k • δ k + (ρ k - 1) • ofR (D.C k)) b‖ ≤
        9 / 8 * (9 / 16) ^ (j - k) * (2 * Mz * (K + cS) * (K * Mz + cS)) := by
      intro k hk
      have hk' := mem_Icc.1 hk
      have hkN : k < D.N := by omega
      obtain ⟨c1, c2⟩ := coef_bound hL2 hMz0 hMz hk'.2
      obtain ⟨r1, r2⟩ := hρ k hk
      rw [bl_add_left, bl_smul_left, bl_smul_left]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      have e1 := bl_le_sup_lam (v := b) (hδsup k hk'.1 hkN (by omega))
      have e2 := bl_le_sup_lam (v := b) (hCsup k hk'.1 hkN)
      have hG : 0 ≤ 2 * ((Lr ^ j) ^ 2)⁻¹ * (K * Mz + cS) := by positivity
      have f1 : ‖ρ k‖ * ‖bl (δ k) b‖ ≤ 9 / 8 * (9 / 16) ^ (j - k) * (2 * (K * Mz) * (K * Mz + cS)) := by
        calc ‖ρ k‖ * ‖bl (δ k) b‖ ≤ (1 + Mz) ^ (j + 1 - k) *
            ((Lr ^ k) ^ 2 * (K * Mz) * (2 * ((Lr ^ j) ^ 2)⁻¹ * (K * Mz + cS))) :=
              mul_le_mul r1 (e1.trans (mul_le_mul_of_nonneg_left havgLb (by positivity)))
                (norm_nonneg _) (by positivity)
          _ = (1 + Mz) ^ (j + 1 - k) * ((Lr ^ k) ^ 2 * ((Lr ^ j) ^ 2)⁻¹) *
              (2 * (K * Mz) * (K * Mz + cS)) := by ring
          _ ≤ _ := by gcongr
      have f2 : ‖ρ k - 1‖ * ‖bl (ofR (D.C k)) b‖ ≤
          9 / 8 * (9 / 16) ^ (j - k) * (2 * (Mz * cS) * (K * Mz + cS)) := by
        calc ‖ρ k - 1‖ * ‖bl (ofR (D.C k)) b‖ ≤ ((j + 1 - k : ℕ) : ℝ) * Mz * (1 + Mz) ^ (j + 1 - k) *
            ((Lr ^ k) ^ 2 * cS * (2 * ((Lr ^ j) ^ 2)⁻¹ * (K * Mz + cS))) :=
              mul_le_mul r2 (e2.trans (mul_le_mul_of_nonneg_left havgLb (by positivity)))
                (norm_nonneg _) (by positivity)
          _ = ((j + 1 - k : ℕ) : ℝ) * (1 + Mz) ^ (j + 1 - k) * ((Lr ^ k) ^ 2 * ((Lr ^ j) ^ 2)⁻¹) *
              (2 * (Mz * cS) * (K * Mz + cS)) := by ring
          _ ≤ _ := by gcongr
      calc _ ≤ 9 / 8 * (9 / 16) ^ (j - k) * (2 * (K * Mz) * (K * Mz + cS)) +
            9 / 8 * (9 / 16) ^ (j - k) * (2 * (Mz * cS) * (K * Mz + cS)) := add_le_add f1 f2
        _ = _ := by ring
    refine (sum_le_sum hterm).trans ?_
    rw [← sum_mul, ← mul_sum]
    have hg := geom_Icc_le j
    have hpos : 0 ≤ 2 * Mz * (K + cS) * (K * Mz + cS) := by positivity
    calc 9 / 8 * (∑ k ∈ Icc 1 j, ((9 : ℝ) / 16) ^ (j - k)) * (2 * Mz * (K + cS) * (K * Mz + cS))
        ≤ 9 / 8 * (16 / 7) * (2 * Mz * (K + cS) * (K * Mz + cS)) := by gcongr
      _ ≤ 3 * (2 * Mz * (K + cS) * (K * Mz + cS)) := by gcongr; norm_num
      _ = 6 * Mz * (K + cS) * (K * Mz + cS) := by ring
  -- assemble
  rw [lc_dress_identity]
  have hbd : b - ofR (D.C (j + 1)) = δ (j + 1) := by simp [δ, b]
  rw [hbd]
  calc ‖2 * bl (wp D j - Cle D.C j) b + 2 * bl (Cle D.C j) (δ (j + 1)) +
        bl (δ (j + 1)) (δ (j + 1)) + 2 * bl (ofR (D.C (j + 1))) (δ (j + 1))‖
      ≤ 2 * ‖bl (wp D j - Cle D.C j) b‖ + 2 * ‖bl (Cle D.C j) (δ (j + 1))‖ +
          ‖bl (δ (j + 1)) (δ (j + 1))‖ + 2 * ‖bl (ofR (D.C (j + 1))) (δ (j + 1))‖ := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
          ((norm_add_le _ _).trans (add_le_add ?_ ?_)) le_rfl)) ?_) <;>
          rw [norm_mul] <;> norm_num
    _ ≤ 2 * (6 * Mz * (K + cS) * (K * Mz + cS)) + 2 * (K * Mz) + 2 * Lr ^ 2 * K ^ 2 * Mz ^ 2 +
          2 * (K * Mz) := by gcongr
    _ = Mz * (4 * K + 2 * Lr ^ 2 * K ^ 2 * Mz + 12 * (K + cS) * (K * Mz + cS)) := by ring

end

end Step2.D2
