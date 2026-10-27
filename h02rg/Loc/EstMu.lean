import Loc.EstBasic
import Loc.EstCutoff
import Loc.EstTransfer

/-!
# The pairings `μ_β` are bounded by the `T` norm

For a small set `X` and `F ∈ 𝒩(X^□)`, `‖μ_β(F)‖ ≤ C ℓ^{-2} L^{j deg β} ‖F‖_{T_j(ℓ)}`: `μ_β(F)` is
the pairing of `F` with a test function equal to the test polynomial `Q_β` (in lifted coordinates)
on `X^□`, cut off smoothly at scale `L^j`.
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD

variable {d L N : ℕ} [NeZero L]

/-! ### Geometry -/

theorem base_mem {X : Finset (Lam d L N)} (h : X.Nonempty) : base X ∈ X := by
  rw [base, dif_pos h]; exact h.choose_spec

/-- The radius `2^{d+1} L^j` of `X^□` around the base point. -/
abbrev rad (d L j : ℕ) : ℕ := 2 ^ (d + 1) * L ^ j

theorem supNorm_nbhd_base {j : ℕ} {X : Finset (Lam d L N)} (hX : IsSmall j X) {y : Lam d L N}
    (hy : y ∈ nbhd j X) : supNorm (y - base X) ≤ rad d L j :=
  supNorm_le_of_mem_nbhd hX (base_mem hX.2.1.1) hy

theorem one_le_rad (j : ℕ) : 1 ≤ rad d L j :=
  Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by positivity) (pow_ne_zero _ (NeZero.ne L)))

/-- The size condition: the neighbourhood (with a margin) is small compared to the torus. -/
theorem size_cond (hL : 2 ^ (d + 3) + 8 * d < L) {j : ℕ} (hj : j < N) :
    2 * (2 * rad d L j + 2 * pPhi d) < L ^ N := by
  have h2p : 0 < 2 ^ (d + 3) := by positivity
  have hL1 : 1 ≤ L := by omega
  have hLj : 1 ≤ L ^ j := Nat.one_le_pow _ _ (by omega)
  have h1 : L ^ (j + 1) ≤ L ^ N := Nat.pow_le_pow_right hL1 hj
  have h2 : 2 * (2 * rad d L j + 2 * pPhi d) ≤ (2 ^ (d + 3) + 8 * d) * L ^ j := by
    simp only [rad, pPhi]
    have : 2 ^ (d + 3) = 2 * (2 * 2 ^ (d + 1)) := by ring
    rw [this]
    nlinarith
  have h3 : (2 ^ (d + 3) + 8 * d) * L ^ j < L * L ^ j := Nat.mul_lt_mul_of_pos_right hL (by omega)
  rw [pow_succ] at h1
  linarith [mul_comm (L ^ j) L]

theorem patch_of_small (hL : 2 ^ (d + 3) + 8 * d < L) {j : ℕ} (hj : j < N)
    {X : Finset (Lam d L N)} (hX : IsSmall j X) : Patch X := by
  intro x hx
  have h1 := supNorm_nbhd_base hX (subset_nbhd hX.1 hx)
  have h2 := size_cond hL hj
  have h3 := one_le_rad (d := d) (L := L) j
  omega

/-! ### Test polynomials as products -/

theorem prod_pow_single (u : Fin d → ℝ) (i : Fin d) (k : ℕ) :
    ∏ j, u j ^ (Pi.single i k : Fin d → ℕ) j = u i ^ k := by
  rw [prod_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · simp

theorem prod_pow_add (u : Fin d → ℝ) (a b : Fin d → ℕ) :
    ∏ j, u j ^ (a + b) j = (∏ j, u j ^ a j) * ∏ j, u j ^ b j := by
  rw [← prod_mul_distrib]; simp [pow_add]

theorem sum_single' (i : Fin d) (k : ℕ) : ∑ j, (Pi.single i k : Fin d → ℕ) j = k := by
  rw [sum_eq_single i] <;> simp +contextual

/-- `Q_β(u, v) = c ∏ u_i^{m₀ i} ∏ v_i^{m₁ i}` with `|c| ≤ 1` and `∑ m₀ + ∑ m₁ = deg β`. -/
theorem Qpoly_eq_prod (β : Mono d) : ∃ (c : ℝ) (m₀ m₁ : Fin d → ℕ), |c| ≤ 1 ∧ (∀ i, m₀ i ≤ 2) ∧
    (∀ i, m₁ i ≤ 2) ∧ ∑ i, m₀ i + ∑ i, m₁ i = β.deg ∧
    ∀ u v : Fin d → ℝ, Qpoly β u v = c * (∏ i, u i ^ m₀ i) * ∏ i, v i ^ m₁ i := by
  have hs1 : ∀ i k : Fin d, (Pi.single i 1 : Fin d → ℕ) k ≤ 2 := fun i k => by
    by_cases h : k = i <;> simp [h]
  have hs2 : ∀ i k : Fin d, (Pi.single i 2 : Fin d → ℕ) k ≤ 2 := fun i k => by
    by_cases h : k = i <;> simp [h]
  have hs11 : ∀ i i' k : Fin d, i ≠ i' → (Pi.single i 1 + Pi.single i' 1 : Fin d → ℕ) k ≤ 2 :=
    fun i i' k _ => by
      simp only [Pi.add_apply, Pi.single_apply]; split_ifs <;> omega
  cases β with
  | c => exact ⟨1, 0, 0, by simp, fun _ => by simp, fun _ => by simp, by simp [Mono.deg],
      fun u v => by simp [Qpoly]⟩
  | a1 i => exact ⟨1, Pi.single i 1, 0, by simp, hs1 i, fun _ => by simp,
      by simp [sum_single', Mono.deg], fun u v => by simp [Qpoly, prod_pow_single]⟩
  | b1 i => exact ⟨1, 0, Pi.single i 1, by simp, fun _ => by simp, hs1 i,
      by simp [sum_single', Mono.deg], fun u v => by simp [Qpoly, prod_pow_single]⟩
  | a2 s =>
    induction s using Sym2.ind with
    | h i k =>
      rcases eq_or_ne i k with rfl | hik
      · exact ⟨1 / 2, Pi.single i 2, 0, by norm_num [abs_of_pos], hs2 i, fun _ => by simp,
          by simp [sum_single', Mono.deg], fun u v => by
            simp [Qpoly, prod_pow_single]; ring⟩
      · refine ⟨1, Pi.single i 1 + Pi.single k 1, 0, by simp, fun j => hs11 i k j hik,
          fun _ => by simp, ?_, fun u v => ?_⟩
        · simp [sum_add_distrib, sum_single', Mono.deg]
        · simp only [Qpoly, Sym2.lift_mk, if_neg hik, prod_pow_add, prod_pow_single, Pi.zero_apply,
            pow_zero, prod_const_one]; ring
  | b2 s =>
    induction s using Sym2.ind with
    | h i k =>
      rcases eq_or_ne i k with rfl | hik
      · exact ⟨1 / 2, 0, Pi.single i 2, by norm_num [abs_of_pos], fun _ => by simp, hs2 i,
          by simp [sum_single', Mono.deg], fun u v => by
            simp [Qpoly, prod_pow_single]; ring⟩
      · refine ⟨1, 0, Pi.single i 1 + Pi.single k 1, by simp, fun _ => by simp,
          fun j => hs11 i k j hik, ?_, fun u v => ?_⟩
        · simp [sum_add_distrib, sum_single', Mono.deg]
        · simp only [Qpoly, Sym2.lift_mk, if_neg hik, prod_pow_add, prod_pow_single, Pi.zero_apply,
            pow_zero, prod_const_one]; ring
  | m2 i k => exact ⟨1, Pi.single i 1, Pi.single k 1, by simp, hs1 i, hs1 k,
      by simp [sum_single', Mono.deg], fun u v => by simp [Qpoly, prod_pow_single]⟩

/-! ### One-point factors with a spin condition -/

/-- `(u, σ) ↦ [σ = σ₀] g(u)`. -/
def spinF (σ₀ : ℤˣ) (g : Zd d → ℝ) (a : Sf (Zd d)) : ℝ := if a.2 = σ₀ then g a.1 else 0

theorem D1_spinF (σ₀ : ℤˣ) (g : Zd d → ℝ) (a : Dir d → ℕ) (x : Sf (Zd d)) :
    D1 sh a (spinF σ₀ g) x = if x.2 = σ₀ then D1 (fun b v => b +ᵥ v) a g x.1 else 0 := by
  rw [D1_eq_sum, D1_eq_sum]
  split_ifs with h
  · refine sum_congr rfl fun b _ => ?_
    simp [spinF, sh, h]
  · refine sum_eq_zero fun b _ => ?_
    simp [spinF, sh, h]

theorem D1_const_mul (s : (Dir d → ℕ) → Zd d → Zd d) (a : Dir d → ℕ) (c : ℝ) (g : Zd d → ℝ)
    (u : Zd d) : D1 s a (fun v => c * g v) u = c * D1 s a g u := by
  rw [D1_eq_sum, D1_eq_sum, mul_sum]
  refine sum_congr rfl fun b _ => by ring

/-! ### Sums over sequences of length two -/

theorem sum_fin_two {α M : Type*} [Fintype α] [AddCommMonoid M] (φ : (Fin 2 → α) → M) :
    ∑ z, φ z = ∑ a, ∑ a', φ ![a, a'] := by
  rw [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (piFinTwoEquiv fun _ => α) _ _ fun z => ?_
  congr 1
  funext i; fin_cases i <;> rfl

theorem sum_units_int {M : Type*} [AddCommMonoid M] (f : ℤˣ → M) : ∑ σ, f σ = f 1 + f (-1) := by
  have : (univ : Finset ℤˣ) = {1, -1} := by
    ext σ; simp only [mem_univ, mem_insert, mem_singleton, true_iff]
    exact Int.units_eq_one_or σ
  rw [this, sum_pair (by decide)]

/-- `⟨F, single 2 f⟩` for `f` supported on the spin pattern `(+, -)`. -/
theorem pair_single_two {X : Type*} [DecidableEq X] [Fintype X] (F : Grassmann.N X)
    (f : (Fin 2 → Sf X) → ℂ) (hf : ∀ z, spins z ≠ ![1, -1] → f z = 0) :
    pair F (single 2 f) =
      (1 / 2 : ℂ) * ∑ x, ∑ y, coeff F ![(x, 1), (y, -1)] * f ![(x, 1), (y, -1)] := by
  rw [pair_single, sum_fin_two, Fintype.sum_prod_type]
  congr 1
  · norm_num
  refine sum_congr rfl fun x _ => ?_
  rw [sum_units_int]
  have hz : ∀ (a : Sf X) (y : X) (τ : ℤˣ), τ ≠ -1 → f ![a, (y, τ)] = 0 := fun a y τ hτ =>
    hf _ fun h => hτ (by simpa [spins] using congrFun h 1)
  have hz' : ∀ (a : Sf X), f ![(x, -1), a] = 0 := fun a => hf _ (by
    intro h
    have h0 : ((-1 : ℤˣ)) = 1 := by simpa [spins] using congrFun h 0
    exact absurd h0 (by decide))
  simp only [hz', mul_zero, sum_const_zero, add_zero]
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun y _ => ?_
  rw [sum_units_int, hz (x, 1) y 1 (by decide), mul_zero, zero_add]

/-! ### The test function for `μ_β` -/

/-- The test function on `ℤ^d` whose pairing gives `μ_β`. -/
def muH (c : ℝ) (m₀ m₁ : Fin d → ℕ) (R : ℝ) (w : Fin 2 → Sf (Zd d)) : ℝ :=
  spinF 1 (fun u => 2 * c * cutP m₀ R u) (w 0) * spinF (-1) (cutP m₁ R) (w 1)

theorem muH_eq_prod (c : ℝ) (m₀ m₁ : Fin d → ℕ) (R : ℝ) :
    muH c m₀ m₁ R = fun w => ∏ k, (![spinF 1 (fun u => 2 * c * cutP m₀ R u),
      spinF (-1) (cutP m₁ R)] : Fin 2 → Sf (Zd d) → ℝ) k (w k) := by
  funext w; simp [muH, Fin.prod_univ_two]

theorem nab_muH (c : ℝ) (m₀ m₁ : Fin d → ℕ) (R : ℝ) (α : Fin 2 → Dir d → ℕ)
    (w : Fin 2 → Sf (Zd d)) :
    nab α (muH c m₀ m₁ R) w =
      D1 sh (α 0) (spinF 1 (fun u => 2 * c * cutP m₀ R u)) (w 0) *
        D1 sh (α 1) (spinF (-1) (cutP m₁ R)) (w 1) := by
  rw [muH_eq_prod, nabla_prod, Fin.prod_univ_two]
  rfl

theorem Mono.deg_le_two (M : Mono d) : M.deg ≤ 2 := by cases M <;> simp [Mono.deg]

/-! ### The bound on `μ_β` -/

theorem muH_ρS_eq_zero (b : Lam d L N) (c : ℝ) (m₀ m₁ : Fin d → ℕ) (R : ℝ)
    (z : Fin 2 → Sf (Lam d L N)) (hz : spins z ≠ ![1, -1]) : muH c m₀ m₁ R (ρS b ∘ z) = 0 := by
  have : (z 0).2 ≠ 1 ∨ (z 1).2 ≠ -1 := by
    by_contra h
    push Not at h
    exact hz (funext fun i => by fin_cases i <;> simp [spins, h.1, h.2])
  rcases this with h | h
  · simp [muH, spinF, ρS, h]
  · simp [muH, spinF, ρS, h]

theorem muH_eq_zero_of_far (c : ℝ) (m₀ m₁ : Fin d → ℕ) {R : ℝ} (hR : 0 < R)
    (w : Fin 2 → Sf (Zd d)) (hw : ∃ k, 2 * R ≤ (supNormZ (w k).1 : ℝ)) :
    muH c m₀ m₁ R w = 0 := by
  obtain ⟨k, hk⟩ := hw
  fin_cases k
  · have h0 : cutP m₀ R (w 0).1 = 0 := cutP_eq_zero m₀ hR hk
    simp only [muH, spinF, h0]; split_ifs <;> simp
  · have h0 : cutP m₁ R (w 1).1 = 0 := cutP_eq_zero m₁ hR hk
    simp only [muH, spinF, h0]; split_ifs <;> simp

theorem exists_mu_bound (d : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℕ) [NeZero L],
    2 ^ (d + 3) + 8 * d < L → ∀ N j : ℕ, j < N → ∀ X : Finset (Lam d L N), IsSmall j X →
    ∀ F ∈ NX (nbhd j X : Set (Lam d L N)), ∀ β : Mono d, ∀ ℓ : ℝ, 0 < ℓ →
      ‖mu (base X) β F‖ ≤
        C * (ℓ ^ 2)⁻¹ * ((L : ℝ) ^ j) ^ β.deg * (Tj d (L : ℝ) j ℓ F).toReal := by
  obtain ⟨Cc, hCc0, hCc⟩ := exists_D1_cutP_bound d (pPhi d) 2
  refine ⟨2 * Cc ^ 2 * 4 ^ (d + 1), by positivity, ?_⟩
  intro L _ hL N j hj X hX F hF β ℓ hℓ
  obtain ⟨c, m₀, m₁, hc, hm₀, hm₁, hdeg, hQ⟩ := Qpoly_eq_prod β
  set b := base X with hb
  set s : ℝ := (L : ℝ) ^ j with hs
  set R : ℝ := (rad d L j : ℝ) with hRdef
  have h2p : 0 < 2 ^ (d + 3) := by positivity
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
  have hs1 : 1 ≤ s := one_le_pow₀ hL1
  have hRs : R = 2 ^ (d + 1) * s := by simp [R, rad, s]
  have hR1 : 1 ≤ R := by rw [hRdef]; exact Nat.one_le_cast.2 (one_le_rad j)
  have hR0 : 0 < R := by linarith
  have hsR : s ≤ R := by
    rw [hRs]; exact le_mul_of_one_le_left (by linarith) (one_le_pow₀ (by norm_num))
  let g : TestFn (Lam d L N) := single 2 (fun z => (muH c m₀ m₁ R (ρS b ∘ z) : ℂ))
  -- the pairing is `μ_β`
  have hpair : pair F g = mu b β F := by
    rw [pair_single_two F _ (fun z hz => by rw [muH_ρS_eq_zero b c m₀ m₁ R z hz,
      Complex.ofReal_zero]), mu, mul_sum]
    refine sum_congr rfl fun x _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun y _ => ?_
    have hval : muH c m₀ m₁ R (ρS b ∘ ![(x, 1), (y, -1)]) =
        2 * c * cutP m₀ R (rep (x - b)) * cutP m₁ R (rep (y - b)) := by
      simp [muH, spinF, ρS]
    rw [hval, cf2]
    by_cases hx : x ∈ nbhd j X
    · by_cases hy : y ∈ nbhd j X
      · have hux : (supNormZ (rep (x - b)) : ℝ) ≤ R := by
          have := supNorm_nbhd_base hX hx
          rw [supNormZ_rep_eq, hRdef]; exact_mod_cast this
        have huy : (supNormZ (rep (y - b)) : ℝ) ≤ R := by
          have := supNorm_nbhd_base hX hy
          rw [supNormZ_rep_eq, hRdef]; exact_mod_cast this
        rw [cutP_eq m₀ hR0 hux, cutP_eq m₁ hR0 huy, hQ]
        simp only [lift]
        push_cast
        ring
      · rw [coeff_eq_zero_of_mem_NX hF _ 1 (by simpa using hy)]; ring
    · rw [coeff_eq_zero_of_mem_NX hF _ 0 (by simpa using hx)]; ring
  -- the norm of the test function
  have hnorm : phiNorm (Dir d) (pPhi d) s ℓ g ≤
      ENNReal.ofReal (2 * Cc ^ 2 * 4 ^ (d + 1) * (ℓ ^ 2)⁻¹ * s ^ β.deg) := by
    refine phiNorm_single_le (by positivity) fun z α hα => ?_
    rw [nabla_ofReal, Complex.norm_real, Real.norm_eq_abs]
    rw [nab_comp_ρS b (muH c m₀ m₁ R) (S := 2 * rad d L j) (P := pPhi d) (size_cond hL hj)
      (fun w ⟨k, hk⟩ => muH_eq_zero_of_far c m₀ m₁ hR0 w ⟨k, by
        have : ((2 * rad d L j : ℕ) : ℝ) < supNormZ (w k).1 := by exact_mod_cast hk
        push_cast at this; linarith⟩) α hα z, nab_muH]
    set u := ρS b ∘ z
    have hb0 : |D1 sh (α 0) (spinF 1 (fun u => 2 * c * cutP m₀ R u)) (u 0)| ≤
        2 * (Cc * R ^ (∑ i, m₀ i) / R ^ mabs (α 0)) := by
      rw [D1_spinF]
      split_ifs
      · rw [D1_const_mul, abs_mul]
        have h1 := hCc m₀ hm₀ R hR1 (α 0) (hα 0) (u 0).1
        have h2 : |2 * c| ≤ 2 := by rw [abs_mul]; norm_num; exact hc
        exact mul_le_mul h2 h1 (abs_nonneg _) (by norm_num)
      · simp only [abs_zero]; positivity
    have hb1 : |D1 sh (α 1) (spinF (-1) (cutP m₁ R)) (u 1)| ≤
        Cc * R ^ (∑ i, m₁ i) / R ^ mabs (α 1) := by
      rw [D1_spinF]
      split_ifs
      · exact hCc m₁ hm₁ R hR1 (α 1) (hα 1) (u 1).1
      · simp only [abs_zero]; positivity
    have hord : ord α = mabs (α 0) + mabs (α 1) := by simp [ord, Fin.sum_univ_two]
    have hdeg2 : β.deg ≤ 2 := Mono.deg_le_two β
    have hpow : R ^ β.deg ≤ 4 ^ (d + 1) * s ^ β.deg := by
      rw [hRs, mul_pow]
      gcongr
      calc ((2 : ℝ) ^ (d + 1)) ^ β.deg ≤ (2 ^ (d + 1)) ^ 2 :=
            pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) hdeg2
        _ = 4 ^ (d + 1) := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have hsR' : s ^ ord α / R ^ ord α ≤ 1 :=
      (div_le_one (by positivity)).2 (pow_le_pow_left₀ (by linarith) hsR _)
    rw [abs_mul]
    calc ℓ⁻¹ ^ 2 * s ^ ord α * (|D1 sh (α 0) (spinF 1 (fun u => 2 * c * cutP m₀ R u)) (u 0)| *
          |D1 sh (α 1) (spinF (-1) (cutP m₁ R)) (u 1)|)
        ≤ ℓ⁻¹ ^ 2 * s ^ ord α * (2 * (Cc * R ^ (∑ i, m₀ i) / R ^ mabs (α 0)) *
          (Cc * R ^ (∑ i, m₁ i) / R ^ mabs (α 1))) := by
          gcongr
      _ = 2 * Cc ^ 2 * (ℓ ^ 2)⁻¹ * R ^ β.deg * (s ^ ord α / R ^ ord α) := by
          rw [← hdeg, hord, pow_add, pow_add, pow_add]
          field_simp
      _ ≤ 2 * Cc ^ 2 * (ℓ ^ 2)⁻¹ * (4 ^ (d + 1) * s ^ β.deg) * 1 := by
          gcongr
      _ = 2 * Cc ^ 2 * 4 ^ (d + 1) * (ℓ ^ 2)⁻¹ * s ^ β.deg := by ring
  have := abs_pair_le (by positivity) hℓ F (by positivity) hnorm
  rw [hpair] at this
  calc ‖mu b β F‖ ≤ (tNorm (Dir d) (pPhi d) s ℓ F).toReal *
        (2 * Cc ^ 2 * 4 ^ (d + 1) * (ℓ ^ 2)⁻¹ * s ^ β.deg) := this
    _ = _ := by simp only [Tj, s]; ring

end

end Loc
