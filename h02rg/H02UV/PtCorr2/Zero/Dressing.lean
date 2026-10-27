import PtCorr2.Zero.Ward2

/-!
# The dressing terms `c_jπ_j/ρ_j` of the dressed susceptibility

In `suscept2` the zero-mode absorptions enter through `c_j = a_j m² = m² Z_jζ_j`,
`γ_j = Γ̂_j(0)`, `ρ_j = 1 + c_jγ_j`, `π_j = ∏_{i<j} ρ_i^{-2}`. Write
`e_j = 1 - Z_j m² γ_j` (`eh`; this is `ε_j(0)` of the dressed decomposition, `eh_eq_eps`), so
`ρ_j = 1 + ζ_j(1 - e_j)` exactly. With `q_j = (1 + ζ_j)/ρ_j = 1 + ζ_je_j/ρ_j` and
`Q_j = ∏_{i<j} q_i`:

* `dress_pi`: `π_j = Q_j²/Z_j²`;
* `dress_term`: `c_jπ_j/ρ_j = m² (Z_j^{-1} - Z_{j+1}^{-1}) Q_j² q_j` exactly; the factor
  `Z_j^{-1} - Z_{j+1}^{-1} = ζ_j/(Z_j(1 + ζ_j))` is `O(|ζ_j|)` relative to `Z_j^{-1}`, and
  `Q_j²q_j = 1 + O(∑_{i ≤ j}|ζ_ie_i|)`;
* the sum telescopes (`Z_0 = 1`): `∑_{j<N}(Z_j^{-1} - Z_{j+1}^{-1}) = 1 - Z_N^{-1}`, so
  **`dress_suscept`** / **`suscept2_dressed`**:

  `m^{-2} - m^{-4}[ã π_N/(1 + ũ) + ∑_{j<N} c_jπ_j/ρ_j]
     = Z_N^{-1}[m^{-2} - m^{-4}(ã/Z_N)/(1 + ũ)] + Err`,

  `|Err| ≤ (m^{-2} ∑_{j<N} |ζ_j|/(|Z_j||1 + ζ_j|) + m^{-4}|ã/Z_N|/(|Z_N||1 + ũ|))(e^{2S} - 1)`,
  `S = ∑_{i<N} |q_i - 1| = ∑_{i<N} |ζ_ie_i/ρ_i|`.

  This is the normalised-field form of `prop:suscept`: the dressing terms reproduce exactly the
  field strength `Z_N^{-1}` up to the `ζ_je_j` corrections.
* `norm_dQ_sub_one_le`: if `|ζ_i| ≤ 1/8`, `|e_i| ≤ 1` then `|q_i - 1| ≤ (4/3)|ζ_i||e_i|`, so
  `S ≤ (4/3)∑_{i<N}|ζ_i||e_i|`; `dress_term_norm_le`: `|c_jπ_j/ρ_j| ≤ m²|ζ_j|/(|Z_j||1+ζ_j|) e^{2S}`.

The expected size is `e_j = ε_j(0) = O(m²L^{2j})`, which makes `S = O(ρ)`; no bound on `ε_j(0)`
is exported by the dressed decomposition (`DressedFRD.Concl`), so the bounds are stated with the
`e_j` (or with `|e_j| ≤ 1`) as explicit inputs.
-/

namespace PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Step2 Step

/-! ### Products near one -/

theorem norm_mul_sub_one_le' {a c : ℂ} {s t : ℝ} (ha : ‖a - 1‖ ≤ Real.exp s - 1)
    (hc : ‖c - 1‖ ≤ Real.exp t - 1) : ‖a * c - 1‖ ≤ Real.exp (s + t) - 1 := by
  have e : a * c - 1 = (a - 1) * (c - 1) + (a - 1) + (c - 1) := by ring
  have h0a := norm_nonneg (a - 1)
  have h0c := norm_nonneg (c - 1)
  rw [e, Real.exp_add]
  calc ‖(a - 1) * (c - 1) + (a - 1) + (c - 1)‖
      ≤ ‖a - 1‖ * ‖c - 1‖ + ‖a - 1‖ + ‖c - 1‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [← norm_mul]; linarith [norm_add_le ((a - 1) * (c - 1)) (a - 1)]
    _ ≤ (Real.exp s - 1) * (Real.exp t - 1) + (Real.exp s - 1) + (Real.exp t - 1) := by
        have := mul_le_mul ha hc h0c (h0a.trans ha)
        linarith
    _ = Real.exp s * Real.exp t - 1 := by ring

theorem norm_sub_one_le_exp (a : ℂ) : ‖a - 1‖ ≤ Real.exp ‖a - 1‖ - 1 := by
  linarith [Real.add_one_le_exp ‖a - 1‖]

theorem norm_prod_sub_one_le' {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → ℂ) :
    ‖∏ i ∈ s, x i - 1‖ ≤ Real.exp (∑ i ∈ s, ‖x i - 1‖) - 1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha]
    exact norm_mul_sub_one_le' (norm_sub_one_le_exp _) ih

/-! ### The abstract dressing algebra -/

section Abstract

variable (Z ζ e : ℕ → ℂ)

/-- `ρ_j = 1 + ζ_j(1 - e_j)`. -/
def dRho (j : ℕ) : ℂ := 1 + ζ j * (1 - e j)

/-- `q_j = (1 + ζ_j)/ρ_j`. -/
def dQ (j : ℕ) : ℂ := (1 + ζ j) / dRho ζ e j

/-- `Q_j = ∏_{i<j} q_i`. -/
def dQp (j : ℕ) : ℂ := ∏ i ∈ range j, dQ ζ e i

variable {Z ζ e}

theorem dQ_sub_one {j : ℕ} (hρ : dRho ζ e j ≠ 0) : dQ ζ e j - 1 = ζ j * e j / dRho ζ e j := by
  rw [dQ, div_sub_one hρ, dRho]; congr 1; ring

/-- `π_n = Q_n²/Z_n²`. -/
theorem dress_pi (hZ0 : Z 0 = 1) (hZs : ∀ j, Z (j + 1) = Z j * (1 + ζ j)) :
    ∀ n, (∀ i < n, dRho ζ e i ≠ 0) → (∀ i < n, 1 + ζ i ≠ 0) → (∀ i ≤ n, Z i ≠ 0) →
      ∏ i ∈ range n, (dRho ζ e i)⁻¹ ^ 2 = dQp ζ e n ^ 2 / Z n ^ 2
  | 0, _, _, _ => by simp [dQp, hZ0]
  | n + 1, hρ, hζ, hZ => by
    rw [prod_range_succ, dress_pi hZ0 hZs n (fun i hi => hρ i (by omega))
      (fun i hi => hζ i (by omega)) (fun i hi => hZ i (by omega)), dQp, dQp, prod_range_succ,
      hZs, dQ]
    have h1 := hρ n (by omega)
    have h2 := hζ n (by omega)
    have h3 := hZ n (by omega)
    field_simp

/-- **One dressing term**: `m Z_jζ_j π_j/ρ_j = m (Z_j^{-1} - Z_{j+1}^{-1}) Q_j² q_j`. -/
theorem dress_term (hZs : ∀ j, Z (j + 1) = Z j * (1 + ζ j)) (m : ℂ) {j : ℕ} (hZj : Z j ≠ 0)
    (hζj : 1 + ζ j ≠ 0) (hρj : dRho ζ e j ≠ 0) {π : ℂ} (hπ : π = dQp ζ e j ^ 2 / Z j ^ 2) :
    m * Z j * ζ j * π / dRho ζ e j = m * (1 / Z j - 1 / Z (j + 1)) * (dQp ζ e j ^ 2 * dQ ζ e j) := by
  rw [hπ, hZs, dQ]
  field_simp
  ring

theorem inv_sub_inv_succ (hZs : ∀ j, Z (j + 1) = Z j * (1 + ζ j)) {j : ℕ} (hZj : Z j ≠ 0)
    (hζj : 1 + ζ j ≠ 0) : 1 / Z j - 1 / Z (j + 1) = ζ j / (Z j * (1 + ζ j)) := by
  rw [hZs]; field_simp; ring

theorem norm_dQp_sq_dQ_sub_one_le {n j : ℕ} (hj : j < n) :
    ‖dQp ζ e j ^ 2 * dQ ζ e j - 1‖ ≤ Real.exp (2 * ∑ i ∈ range n, ‖dQ ζ e i - 1‖) - 1 := by
  show ‖(∏ i ∈ range j, dQ ζ e i) ^ 2 * dQ ζ e j - 1‖ ≤ _
  have h1 := norm_prod_sub_one_le' (range j) (dQ ζ e)
  have h2 := norm_mul_sub_one_le' (norm_mul_sub_one_le' h1 h1) (norm_sub_one_le_exp (dQ ζ e j))
  rw [← sq] at h2
  refine h2.trans (sub_le_sub_right (Real.exp_le_exp.2 ?_) _)
  have hs : ∑ i ∈ range (j + 1), ‖dQ ζ e i - 1‖ ≤ ∑ i ∈ range n, ‖dQ ζ e i - 1‖ :=
    sum_le_sum_of_subset_of_nonneg (fun x hx => by simp only [mem_range] at hx ⊢; omega)
      fun _ _ _ => norm_nonneg _
  rw [sum_range_succ] at hs
  have := norm_nonneg (dQ ζ e j - 1)
  have h0 : 0 ≤ ∑ i ∈ range j, ‖dQ ζ e i - 1‖ := sum_nonneg fun _ _ => norm_nonneg _
  linarith

theorem norm_dQp_sq_sub_one_le (n : ℕ) :
    ‖dQp ζ e n ^ 2 - 1‖ ≤ Real.exp (2 * ∑ i ∈ range n, ‖dQ ζ e i - 1‖) - 1 := by
  have h1 := norm_prod_sub_one_le' (range n) (dQ ζ e)
  have h2 := norm_mul_sub_one_le' h1 h1
  rw [← sq, ← two_mul] at h2
  exact h2

/-- **The dressed susceptibility in normalised form** (abstract): with `c_j = m Z_jζ_j` and
`π_j = ∏_{i<j}ρ_i^{-2}`,
`|m^{-1} - m^{-2}[A π_n/U + ∑_{j<n} c_jπ_j/ρ_j] - (m^{-1}Z_n^{-1} - m^{-2}(A/Z_n)/(Z_n U))|
  ≤ (|m|^{-1} ∑_{j<n}|ζ_j|/(|Z_j||1+ζ_j|) + |m|^{-2}|A/Z_n|/(|Z_n||U|))(e^{2S} - 1)`. -/
theorem dress_suscept (hZ0 : Z 0 = 1) (hZs : ∀ j, Z (j + 1) = Z j * (1 + ζ j)) {n : ℕ}
    (hρ : ∀ i < n, dRho ζ e i ≠ 0) (hζ : ∀ i < n, 1 + ζ i ≠ 0) (hZ : ∀ i ≤ n, Z i ≠ 0)
    {m A U : ℂ} (hm : m ≠ 0) (hU : U ≠ 0) :
    ‖(1 / m - (1 / m) ^ 2 * (A * (∏ i ∈ range n, (dRho ζ e i)⁻¹ ^ 2) / U +
        ∑ j ∈ range n, m * Z j * ζ j * (∏ i ∈ range j, (dRho ζ e i)⁻¹ ^ 2) / dRho ζ e j)) -
      (1 / (m * Z n) - (1 / m) ^ 2 * (A / Z n) / (Z n * U))‖ ≤
      (‖1 / m‖ * ∑ j ∈ range n, ‖ζ j‖ / (‖Z j‖ * ‖1 + ζ j‖) +
        ‖1 / m‖ ^ 2 * (‖A / Z n‖ / (‖Z n‖ * ‖U‖))) *
        (Real.exp (2 * ∑ i ∈ range n, ‖dQ ζ e i - 1‖) - 1) := by
  set E := Real.exp (2 * ∑ i ∈ range n, ‖dQ ζ e i - 1‖) - 1 with hE
  have hZn := hZ n le_rfl
  -- the terms
  have hterm : ∀ j ∈ range n, m * Z j * ζ j * (∏ i ∈ range j, (dRho ζ e i)⁻¹ ^ 2) / dRho ζ e j =
      m * (1 / Z j - 1 / Z (j + 1)) + m * (1 / Z j - 1 / Z (j + 1)) *
        (dQp ζ e j ^ 2 * dQ ζ e j - 1) := fun j hj => by
    have hj := mem_range.1 hj
    rw [dress_term hZs m (hZ j hj.le) (hζ j hj) (hρ j hj)
      (dress_pi hZ0 hZs j (fun i hi => hρ i (by omega)) (fun i hi => hζ i (by omega))
        (fun i hi => hZ i (by omega)))]
    ring
  have hsum := sum_congr rfl hterm
  rw [sum_add_distrib, ← mul_sum, sum_range_sub' (fun j => 1 / Z j), hZ0] at hsum
  rw [hsum, dress_pi hZ0 hZs n hρ hζ (fun i hi => hZ i hi)]
  set T := ∑ j ∈ range n, m * (1 / Z j - 1 / Z (j + 1)) * (dQp ζ e j ^ 2 * dQ ζ e j - 1)
  have hT0 : ‖T‖ ≤ ∑ j ∈ range n, ‖m‖ * (‖ζ j‖ / (‖Z j‖ * ‖1 + ζ j‖)) * E := by
    refine (norm_sum_le _ _).trans (sum_le_sum fun j hj => ?_)
    have hj' := mem_range.1 hj
    rw [norm_mul, norm_mul, inv_sub_inv_succ hZs (hZ j hj'.le) (hζ j hj'), norm_div, norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_dQp_sq_dQ_sub_one_le hj') (by positivity)
  have hT : ‖T‖ ≤ ‖m‖ * (∑ j ∈ range n, ‖ζ j‖ / (‖Z j‖ * ‖1 + ζ j‖)) * E := by
    rw [mul_sum, sum_mul]; exact hT0
  have hEq : 1 / m - (1 / m) ^ 2 * (A * (dQp ζ e n ^ 2 / Z n ^ 2) / U + (m * (1 / 1 - 1 / Z n) + T)) -
      (1 / (m * Z n) - (1 / m) ^ 2 * (A / Z n) / (Z n * U)) =
      -((1 / m) ^ 2 * T) - (1 / m) ^ 2 * (A / Z n) / (Z n * U) * (dQp ζ e n ^ 2 - 1) := by
    field_simp
    ring
  rw [hEq]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_neg]
  have h1 : ‖1 / m‖ ^ 2 * ‖T‖ ≤ ‖1 / m‖ * (∑ j ∈ range n, ‖ζ j‖ / (‖Z j‖ * ‖1 + ζ j‖)) * E := by
    have hm' : ‖1 / m‖ * ‖m‖ = 1 := by
      rw [norm_div, norm_one, one_div, inv_mul_cancel₀ (norm_ne_zero_iff.2 hm)]
    calc ‖1 / m‖ ^ 2 * ‖T‖ ≤ ‖1 / m‖ ^ 2 * (‖m‖ * (∑ j ∈ range n, ‖ζ j‖ / (‖Z j‖ * ‖1 + ζ j‖)) * E) :=
          mul_le_mul_of_nonneg_left hT (by positivity)
      _ = (‖1 / m‖ * ‖m‖) * (‖1 / m‖ * (∑ j ∈ range n, ‖ζ j‖ / (‖Z j‖ * ‖1 + ζ j‖)) * E) := by ring
      _ = _ := by rw [hm', one_mul]
  have h2 : ‖1 / m‖ ^ 2 * (‖A / Z n‖ / (‖Z n‖ * ‖U‖)) * ‖dQp ζ e n ^ 2 - 1‖ ≤
      ‖1 / m‖ ^ 2 * (‖A / Z n‖ / (‖Z n‖ * ‖U‖)) * E :=
    mul_le_mul_of_nonneg_left (norm_dQp_sq_sub_one_le n) (by positivity)
  have hx : ‖(1 / m) ^ 2 * T‖ ≤ ‖1 / m‖ * (∑ j ∈ range n, ‖ζ j‖ / (‖Z j‖ * ‖1 + ζ j‖)) * E := by
    rw [norm_mul, norm_pow]; exact h1
  have hy : ‖(1 / m) ^ 2 * (A / Z n) / (Z n * U) * (dQp ζ e n ^ 2 - 1)‖ ≤
      ‖1 / m‖ ^ 2 * (‖A / Z n‖ / (‖Z n‖ * ‖U‖)) * E := by
    rw [norm_mul, norm_div, norm_mul, norm_pow, norm_mul (Z n), mul_div_assoc]; exact h2
  linarith

/-- **Size of one dressing term**: `|m Z_jζ_jπ_j/ρ_j| ≤ |m| |ζ_j|/(|Z_j||1+ζ_j|) e^{2S}` (`j < n`). -/
theorem dress_term_norm_le (hZ0 : Z 0 = 1) (hZs : ∀ j, Z (j + 1) = Z j * (1 + ζ j)) {n j : ℕ}
    (hj : j < n) (hρ : ∀ i < n, dRho ζ e i ≠ 0) (hζ : ∀ i < n, 1 + ζ i ≠ 0)
    (hZ : ∀ i ≤ n, Z i ≠ 0) (m : ℂ) :
    ‖m * Z j * ζ j * (∏ i ∈ range j, (dRho ζ e i)⁻¹ ^ 2) / dRho ζ e j‖ ≤
      ‖m‖ * (‖ζ j‖ / (‖Z j‖ * ‖1 + ζ j‖)) * Real.exp (2 * ∑ i ∈ range n, ‖dQ ζ e i - 1‖) := by
  rw [dress_term hZs m (hZ j hj.le) (hζ j hj) (hρ j hj)
    (dress_pi hZ0 hZs j (fun i hi => hρ i (by omega)) (fun i hi => hζ i (by omega))
      (fun i hi => hZ i (by omega))), inv_sub_inv_succ hZs (hZ j hj.le) (hζ j hj), norm_mul,
    norm_mul, norm_div, norm_mul]
  have h := norm_dQp_sq_dQ_sub_one_le (ζ := ζ) (e := e) hj
  have h' : ‖dQp ζ e j ^ 2 * dQ ζ e j‖ ≤ Real.exp (2 * ∑ i ∈ range n, ‖dQ ζ e i - 1‖) := by
    have := norm_le_norm_add_norm_sub' (dQp ζ e j ^ 2 * dQ ζ e j) 1
    rw [norm_one] at this
    linarith
  exact mul_le_mul_of_nonneg_left h' (by positivity)

end Abstract

/-! ### Along the flow -/

variable {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- `Z_j` along the history. -/
abbrev Zr (t : Hist.Seq (Xs R)) (j : ℕ) : ℂ := (rawHist R j t).Z

/-- `ζ_j` along the history (the absorbed coupling of step `j`). -/
abbrev ζr (t : Hist.Seq (Xs R)) (j : ℕ) : ℂ := stZeta R (rawHist R j t)

/-- `e_j = 1 - Z_j m² Γ̂_j(0)`. -/
def eh (t : Hist.Seq (Xs R)) (j : ℕ) : ℂ := 1 - Zr R t j * R.msq * (Dh R j t).Gam j 0

theorem Zr_zero (t : Hist.Seq (Xs R)) : Zr R t 0 = 1 := rfl

theorem Zr_succ (t : Hist.Seq (Xs R)) (j : ℕ) : Zr R t (j + 1) = Zr R t j * (1 + ζr R t j) := rfl

theorem Dh_Z_eq {j : ℕ} {t : Hist.Seq (Xs R)} (H : RawInv R j (rawHist R j t)) :
    (Dh R j t).Z j = Zr R t j := by
  show ∏ i ∈ range j, (1 + Function.update (rawHist R j t).ζ j (stZeta R (rawHist R j t)) i) =
    (rawHist R j t).Z
  rw [H.hZprod]
  refine prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (by have := mem_range.1 hi; omega)]

/-- `c_j = m² Z_jζ_j`. -/
theorem ch₀_eq {j : ℕ} {t : Hist.Seq (Xs R)} (H : RawInv R j (rawHist R j t)) :
    ch₀ R j t = (R.msq : ℂ) * Zr R t j * ζr R t j := by
  rw [ch₀, stData_ζZ H, DressedFRD.Data.Asym_zero, stA]
  show (rawHist R j t).Z * stZeta R (rawHist R j t) * (R.msq : ℂ) = _
  ring

/-- `ρ_j = 1 + ζ_j(1 - e_j)`. -/
theorem ρh_eq {j : ℕ} {t : Hist.Seq (Xs R)} (H : RawInv R j (rawHist R j t)) :
    ρh R j t = dRho (ζr R t) (eh R t) j := by
  rw [ρh, ch₀_eq R H, dRho, eh]; ring

/-- `e_j = ε_j(0)` of the dressed decomposition. -/
theorem eh_eq_eps (hL7 : 7 ≤ L) (hm0 : 0 < R.msq) (hN : 1 ≤ N) {j : ℕ} (hj : j ≤ N)
    {t : Hist.Seq (Xs R)} (H : RawInv R j (rawHist R j t)) (hZ : Zr R t j ≠ 0) :
    eh R t j = (Dh R j t).eps j ((Dh R j t).tails j) 0 := by
  obtain ⟨cS, -, hS⟩ := DressedFRD.frd_stdFull R.P (d := 2) le_rfl hL7 (q := 2) (M := 2 + 2 + 1)
    le_rfl
  have hstd := (hS (L ^ N) N R.msq hN rfl hm0).base
  have h := DressedFRD.Data.Z_A_Gam (D := Dh R j t) hstd hj (by rw [Dh_Z_eq R H]; exact hZ) 0
  rw [Dh_Z_eq R H, DressedFRD.Data.Asym_zero] at h
  rw [eh, show (R.msq : ℂ) = ((Dh R j t).msq : ℂ) from rfl, h]
  ring

/-- **The dressed susceptibility in normalised fields along a trajectory**: the right side of
`suscept2` is `Z_N^{-1}[m^{-2} - m^{-4}(ã/Z_N)/(1 + ũ)]` up to an error bounded by
`(m^{-2}∑_{j<N}|ζ_j|/(|Z_j||1+ζ_j|) + m^{-4}|ã/Z_N|/(|Z_N||1+ũ|))(e^{2S} - 1)`,
`S = ∑_{i<N}|q_i - 1|`, `q_i - 1 = ζ_ie_i/ρ_i`. -/
theorem suscept2_dressed {Nh : ℕ} (hN : Nh + 2 = N) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < R.msq)
    (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt R j)
    (hVL : ValidAtL R Nh) (t : Hist.Seq (Xs R))
    (hu : 1 + uFin (Nh + 1) (lastOut R Nh t) (zmRaw R (Nh + 1) (lastOut R Nh t).ζ) ≠ 0) :
    ‖(1 / (R.msq : ℂ) - (1 / (R.msq : ℂ)) ^ 2 *
        (aFin (Nh + 1) (lastOut R Nh t) * πh R (Nh + 2) t /
            (1 + uFin (Nh + 1) (lastOut R Nh t) (zmRaw R (Nh + 1) (lastOut R Nh t).ζ)) +
          ∑ j ∈ range (Nh + 2), ch₀ R j t * πh R j t / ρh R j t)) -
      (1 / ((R.msq : ℂ) * Zr R t (Nh + 2)) - (1 / (R.msq : ℂ)) ^ 2 *
        (aFin (Nh + 1) (lastOut R Nh t) / Zr R t (Nh + 2)) /
          (Zr R t (Nh + 2) * (1 + uFin (Nh + 1) (lastOut R Nh t) (zmRaw R (Nh + 1) (lastOut R Nh t).ζ))))‖ ≤
      (‖1 / (R.msq : ℂ)‖ * ∑ j ∈ range (Nh + 2), ‖ζr R t j‖ / (‖Zr R t j‖ * ‖1 + ζr R t j‖) +
        ‖1 / (R.msq : ℂ)‖ ^ 2 * (‖aFin (Nh + 1) (lastOut R Nh t) / Zr R t (Nh + 2)‖ /
          (‖Zr R t (Nh + 2)‖ *
            ‖1 + uFin (Nh + 1) (lastOut R Nh t) (zmRaw R (Nh + 1) (lastOut R Nh t).ζ)‖))) *
        (Real.exp (2 * ∑ i ∈ range (Nh + 2), ‖dQ (ζr R t) (eh R t) i - 1‖) - 1) := by
  have hρ0 : 0 ≤ R.ρ := hVL.2.2.2.2.1
  have hRI : ∀ j ≤ Nh + 1, RawInv R j (rawHist R j t) := rawInv_histU R hV hVL t
  have hS : ∀ j ≤ Nh + 1, SplitOK R j (rawHist R j t) :=
    fun j hj => splitOK_hist R hρ0 hspl (by omega) hm0 hm t (by omega)
  have hρ : ∀ i < Nh + 2, dRho (ζr R t) (eh R t) i ≠ 0 := fun i hi => by
    rw [← ρh_eq R (hRI i (by omega))]; exact (hS i (by omega)).1 0
  have hζ : ∀ i < Nh + 2, 1 + ζr R t i ≠ 0 := fun i _ =>
    Step2.one_add_ne_zero ((absorb_le R hρ0 _ _).trans_lt hρ1)
  have hZ : ∀ i ≤ Nh + 2, Zr R t i ≠ 0 := fun i _ => by
    obtain ⟨hZp, -, hb⟩ := rawHist_struct R hρ0 i t
    show (rawHist R i t).Z ≠ 0
    rw [hZp]
    exact prod_ne_zero_iff.2 fun k _ => Step2.one_add_ne_zero ((hb k).trans_lt hρ1)
  have hπ : ∀ j ≤ Nh + 2, πh R j t = ∏ i ∈ range j, (dRho (ζr R t) (eh R t) i)⁻¹ ^ 2 :=
    fun j hj => prod_congr rfl fun i hi => by
      rw [ρh_eq R (hRI i (by have := mem_range.1 hi; omega))]
  have hsum : ∑ j ∈ range (Nh + 2), ch₀ R j t * πh R j t / ρh R j t =
      ∑ j ∈ range (Nh + 2), (R.msq : ℂ) * Zr R t j * ζr R t j *
        (∏ i ∈ range j, (dRho (ζr R t) (eh R t) i)⁻¹ ^ 2) / dRho (ζr R t) (eh R t) j :=
    sum_congr rfl fun j hj => by
      have hj' := mem_range.1 hj
      rw [ch₀_eq R (hRI j (by omega)), hπ j hj'.le, ρh_eq R (hRI j (by omega))]
  rw [hsum, hπ (Nh + 2) le_rfl]
  have hmC : (R.msq : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hm0.ne'
  exact dress_suscept (Z := Zr R t) (ζ := ζr R t) (e := eh R t) (Zr_zero R t) (Zr_succ R t) hρ hζ hZ
    (m := (R.msq : ℂ)) (A := aFin (Nh + 1) (lastOut R Nh t)) hmC hu

end

end PtCorr2
