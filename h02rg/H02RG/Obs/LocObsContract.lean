import Obs.LocObsEst

/-!
# Localisation with observables: boundedness and contraction for one component

* `exists_odd_bound`, `exists_even_bound` (`prop:Loc-obs` (i)):
  `‖loc_{X,Y} F‖_{T_j(ℓ)} ≤ C ‖F‖_{T_j(ℓ)}` for `Y ⊆ X`, `X` small, `F ∈ 𝒩(X^□)` and every `ℓ > 0`;
* `exists_odd_contract`: for `F` of charge `-s` (one more `ψ̄` than `ψ` for `s = -1`),
  `‖F - loc_X F‖_{T_{j+1}(2ℓ_{j+1})} ≤ C θ L^{-1} ‖F‖_{T_j(ℓ_j)}`, `θ = L^{-(d-2)/2} = ℓ_{j+1}/ℓ_j`;
* `exists_even_contract`: for `U(1)`-invariant `F`,
  `‖F - loc_X F‖_{T_{j+1}(2ℓ_{j+1})} ≤ C θ^2 L^{-1} ‖F‖_{T_j(ℓ_j)}`.

Proof of the contraction: `G = F - loc_X F` has vanishing masses at length `1` (odd case), resp.
`2` (even case), since `loc_X` reproduces the pairing with the constant test polynomial, and all
other coefficients of length `< 3`, resp. `< 4`, vanish by `U(1)` invariance.  The Taylor
expansion to order `0` (`exists_core_bound`) gives `C (2θ)^m L^{-1} + (2θ)^{m+2}` with `m = 1`,
resp. `2`, and `θ^2 = L^{-(d-2)} ≤ L^{-1}` for `d ≥ 3`.
-/

namespace Obs.LocObs

noncomputable section

open Finset Grassmann FRD Loc

/-! ### Charges -/

theorem charge_add {Λ : Type*} [DecidableEq Λ] {n : ℕ} (z : Fin n → Sf Λ) :
    charge z + 2 * ((univ.filter fun i => (z i).2 = 1).card : ℤ) = n := by
  have h := card_spins_add' z
  unfold charge
  omega

theorem charge_single {Λ : Type*} [DecidableEq Λ] (y : Λ) (t : ℤˣ) :
    charge ![(y, t)] = -(t : ℤ) := by
  rcases Int.units_eq_one_or t with rfl | rfl <;> simp [charge]

theorem units_val_eq (s : ℤˣ) : (s : ℤ) = 1 ∨ (s : ℤ) = -1 := by
  rcases Int.units_eq_one_or s with rfl | rfl <;> simp

variable {d L N : ℕ} [NeZero L]

theorem coeff_sub' (F G : Alg d L N) {n : ℕ} (z : Fin n → Sf (Lam d L N)) :
    coeff (F - G) z = coeff F z - coeff G z := by
  simpa [coeffL_apply] using (coeffL z).map_sub F G

theorem mass1_sub (s : ℤˣ) (F G : Alg d L N) : mass1 s (F - G) = mass1 s F - mass1 s G := by
  simp [mass1, coeff_sub', sum_sub_distrib]

theorem mass2_sub (F G : Alg d L N) : mass2 (F - G) = mass2 F - mass2 G := by
  simp [mass2, coeff_sub', sum_sub_distrib]

theorem sum_seq_one (G : Alg d L N) (σ : Fin 1 → ℤˣ) :
    ∑ x : Fin 1 → Lam d L N, coeff G (fun k => (x k, σ k)) = mass1 (σ 0) G := by
  rw [sum_fin_one, mass1]
  refine sum_congr rfl fun y _ => congrArg (coeff G) (funext fun k => ?_)
  fin_cases k; rfl

theorem sum_seq_two (G : Alg d L N) (σ : Fin 2 → ℤˣ) :
    ∑ x : Fin 2 → Lam d L N, coeff G (fun k => (x k, σ k)) =
      ∑ x, ∑ y, coeff G ![(x, σ 0), (y, σ 1)] := by
  rw [sum_fin_two]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => congrArg (coeff G) (funext fun k => ?_)
  fin_cases k <;> rfl

theorem norm_div_card_mul_le (c : ℂ) {A B : ℕ} (hAB : A ≤ B) {r : ℝ} (hr : 0 ≤ r) :
    ‖c / (B : ℂ)‖ * (A * r) ≤ ‖c‖ * r := by
  rcases Nat.eq_zero_or_pos B with hB | hB
  · subst hB
    have : A = 0 := by omega
    subst this
    simp only [Nat.cast_zero, div_zero, norm_zero, zero_mul]
    positivity
  · rw [norm_div, Complex.norm_natCast]
    have hA : (A : ℝ) ≤ B := by exact_mod_cast hAB
    have hB' : (0 : ℝ) < B := by exact_mod_cast hB
    rw [div_mul_eq_mul_div, div_le_iff₀ hB']
    have := norm_nonneg c
    nlinarith [mul_nonneg this hr]

theorem card_inter_le {P X Y : Finset (Lam d L N)} (hYX : Y ⊆ X) :
    (Y ∩ P).card ≤ (X ∩ P).card :=
  card_le_card (inter_subset_inter hYX subset_rfl)

/-! ### Boundedness (`prop:Loc-obs` (i)) -/

theorem mass1_le {Cm : ℝ} (hCm : ∀ (n L : ℕ) [NeZero L],
    2 ^ (d + 3) + 8 * d < L → ∀ N j : ℕ, j < N → ∀ X : Finset (Lam d L N), IsSmall j X →
    ∀ F ∈ NX (nbhd j X : Set (Lam d L N)), ∀ σ : Fin n → ℤˣ, ∀ ℓ : ℝ, 0 < ℓ →
      ‖∑ x : Fin n → Lam d L N, coeff F (fun k => (x k, σ k))‖ ≤
        n.factorial * Cm ^ n * ℓ⁻¹ ^ n * (Tj d (L : ℝ) j ℓ F).toReal)
    (hL : 2 ^ (d + 3) + 8 * d < L) {j : ℕ} (hj : j < N) {X : Finset (Lam d L N)}
    (hX : IsSmall j X) {F : Alg d L N} (hF : F ∈ NX (nbhd j X : Set (Lam d L N))) (s : ℤˣ)
    {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ‖mass1 s F‖ ≤ Cm * ℓ⁻¹ * (Tj d (L : ℝ) j ℓ F).toReal := by
  have := hCm 1 L hL N j hj X hX F hF ![s] ℓ hℓ
  rw [sum_seq_one] at this
  simpa using this

theorem mass2_le {Cm : ℝ} (hCm : ∀ (n L : ℕ) [NeZero L],
    2 ^ (d + 3) + 8 * d < L → ∀ N j : ℕ, j < N → ∀ X : Finset (Lam d L N), IsSmall j X →
    ∀ F ∈ NX (nbhd j X : Set (Lam d L N)), ∀ σ : Fin n → ℤˣ, ∀ ℓ : ℝ, 0 < ℓ →
      ‖∑ x : Fin n → Lam d L N, coeff F (fun k => (x k, σ k))‖ ≤
        n.factorial * Cm ^ n * ℓ⁻¹ ^ n * (Tj d (L : ℝ) j ℓ F).toReal)
    (hL : 2 ^ (d + 3) + 8 * d < L) {j : ℕ} (hj : j < N) {X : Finset (Lam d L N)}
    (hX : IsSmall j X) {F : Alg d L N} (hF : F ∈ NX (nbhd j X : Set (Lam d L N)))
    {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ‖mass2 F‖ ≤ 2 * Cm ^ 2 * ℓ⁻¹ ^ 2 * (Tj d (L : ℝ) j ℓ F).toReal := by
  have := hCm 2 L hL N j hj X hX F hF ![-1, 1] ℓ hℓ
  rw [sum_seq_two] at this
  simpa [mass2] using this

theorem norm_pair_ψ_le {j : ℕ} {ℓ : ℝ} (hs : (0 : ℝ) < (L : ℝ) ^ j) (hℓ : 0 < ℓ)
    {g : TestFn (Lam d L N)} (hg : phiNorm (Dir d) (pPhi d) ((L : ℝ) ^ j) ℓ g ≤ 1)
    (a : Sf (Lam d L N)) : ‖pair (ψ a) g‖ ≤ ℓ := by
  have := le_tNorm (ψ a) hg
  rw [tNorm_ψ hs hℓ] at this
  exact (ENNReal.ofReal_le_ofReal_iff hℓ.le).1 this

theorem norm_pair_pbp_le {j : ℕ} {ℓ : ℝ} (hs : (0 : ℝ) < (L : ℝ) ^ j) (hℓ : 0 < ℓ)
    {g : TestFn (Lam d L N)} (hg : phiNorm (Dir d) (pPhi d) ((L : ℝ) ^ j) ℓ g ≤ 1)
    (z : Lam d L N) : ‖pair (pbp z) g‖ ≤ ℓ ^ 2 := by
  have h1 := le_tNorm (pbp z) hg
  have h2 := tNorm_mul_le (E := Dir d) (p := pPhi d) hs hℓ (psibar z) (psi z)
  rw [tNorm_psibar hs hℓ, tNorm_psi hs hℓ, ← ENNReal.ofReal_mul hℓ.le, ← sq] at h2
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 (h1.trans h2)

theorem norm_pair_one_le {j : ℕ} {ℓ : ℝ} (hs : (0 : ℝ) < (L : ℝ) ^ j) (hℓ : 0 < ℓ)
    {g : TestFn (Lam d L N)} (hg : phiNorm (Dir d) (pPhi d) ((L : ℝ) ^ j) ℓ g ≤ 1) :
    ‖pair (1 : Alg d L N) g‖ ≤ 1 := by
  have h1 := le_tNorm (1 : Alg d L N) hg
  have h2 := tNorm_one_le (X := Lam d L N) (E := Dir d) (p := pPhi d) hs hℓ
  rw [← ENNReal.ofReal_one] at h2
  exact (ENNReal.ofReal_le_ofReal_iff zero_le_one).1 (h1.trans h2)

/-- `prop:Loc-obs` (i) for odd components. -/
theorem exists_odd_bound (d : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℕ) [NeZero L],
    2 ^ (d + 3) + 8 * d < L → ∀ N j : ℕ, j < N → ∀ X Y : Finset (Lam d L N), IsSmall j X →
    Y ⊆ X → ∀ F ∈ NX (nbhd j X : Set (Lam d L N)), ∀ (s : ℤˣ) (P : Finset (Lam d L N)),
    ∀ ℓ : ℝ, 0 < ℓ →
      Tj d (L : ℝ) j ℓ (locOdd s P X Y F) ≤ ENNReal.ofReal C * Tj d (L : ℝ) j ℓ F := by
  obtain ⟨Cm, hCm0, hCm⟩ := exists_mass_bound d
  refine ⟨Cm, hCm0, ?_⟩
  intro L _ hL N j hj X Y hX hYX F hF s P ℓ hℓ
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hs : (0 : ℝ) < (L : ℝ) ^ j := by positivity
  set T := (Tj d (L : ℝ) j ℓ F).toReal
  have hm := mass1_le hCm hL hj hX hF s hℓ
  refine (tNorm_le (A := Cm * T) fun g hg => ?_).trans (le_of_eq ?_)
  · unfold locOdd locGen
    rw [pair_smul, pair_sum, norm_mul]
    have hsum : ‖∑ z ∈ Y ∩ P, pair (ψ (z, s)) g‖ ≤ (Y ∩ P).card * ℓ := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ z ∈ Y ∩ P, ‖pair (ψ (z, s)) g‖ ≤ ∑ _z ∈ Y ∩ P, ℓ :=
            sum_le_sum fun z _ => norm_pair_ψ_le hs hℓ hg _
        _ = (Y ∩ P).card * ℓ := by rw [sum_const, nsmul_eq_mul]
    calc ‖mass1 s F / ((X ∩ P).card : ℂ)‖ * ‖∑ z ∈ Y ∩ P, pair (ψ (z, s)) g‖
        ≤ ‖mass1 s F / ((X ∩ P).card : ℂ)‖ * ((Y ∩ P).card * ℓ) := by gcongr
      _ ≤ ‖mass1 s F‖ * ℓ := norm_div_card_mul_le _ (card_inter_le hYX) hℓ.le
      _ ≤ Cm * ℓ⁻¹ * T * ℓ := by gcongr
      _ = Cm * T := by field_simp
  · rw [ENNReal.ofReal_mul hCm0, ENNReal.ofReal_toReal (tNorm_ne_top hs hℓ F)]

/-- `prop:Loc-obs` (i) for even components. -/
theorem exists_even_bound (d : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℕ) [NeZero L],
    2 ^ (d + 3) + 8 * d < L → ∀ N j : ℕ, j < N → ∀ X Y : Finset (Lam d L N), IsSmall j X →
    Y ⊆ X → ∀ F ∈ NX (nbhd j X : Set (Lam d L N)), ∀ P : Finset (Lam d L N),
    ∀ ℓ : ℝ, 0 < ℓ →
      Tj d (L : ℝ) j ℓ (locEven P X Y F) ≤ ENNReal.ofReal C * Tj d (L : ℝ) j ℓ F := by
  obtain ⟨Cm, hCm0, hCm⟩ := exists_mass_bound d
  refine ⟨1 + 2 * Cm ^ 2, by positivity, ?_⟩
  intro L _ hL N j hj X Y hX hYX F hF P ℓ hℓ
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hs : (0 : ℝ) < (L : ℝ) ^ j := by positivity
  set T := (Tj d (L : ℝ) j ℓ F).toReal
  have hm := mass2_le hCm hL hj hX hF hℓ
  have he : ‖ε F‖ ≤ T := abs_eps_le hs hℓ F
  refine (tNorm_le (A := (1 + 2 * Cm ^ 2) * T) fun g hg => ?_).trans (le_of_eq ?_)
  · unfold locEven
    rw [locGen_one, locGen, pair_add, pair_smul, pair_smul, pair_sum]
    have hsum : ‖∑ z ∈ Y ∩ P, pair (pbp z) g‖ ≤ (Y ∩ P).card * ℓ ^ 2 := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ z ∈ Y ∩ P, ‖pair (pbp z) g‖ ≤ ∑ _z ∈ Y ∩ P, ℓ ^ 2 :=
            sum_le_sum fun z _ => norm_pair_pbp_le hs hℓ hg z
        _ = (Y ∩ P).card * ℓ ^ 2 := by rw [sum_const, nsmul_eq_mul]
    have h1 := norm_pair_one_le hs hℓ hg
    have hA : ‖ε F / ((X ∩ P).card : ℂ) * ((Y ∩ P).card : ℂ) * pair (1 : Alg d L N) g‖ ≤ T := by
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      calc ‖ε F / ((X ∩ P).card : ℂ)‖ * ((Y ∩ P).card : ℝ) * ‖pair (1 : Alg d L N) g‖
          ≤ ‖ε F / ((X ∩ P).card : ℂ)‖ * ((Y ∩ P).card * 1) * 1 := by gcongr; rw [mul_one]
        _ ≤ ‖ε F‖ * 1 := by
            rw [mul_one]; exact norm_div_card_mul_le _ (card_inter_le hYX) zero_le_one
        _ ≤ T := by rw [mul_one]; exact he
    have hB : ‖mass2 F / ((X ∩ P).card : ℂ) * ∑ z ∈ Y ∩ P, pair (pbp z) g‖ ≤ 2 * Cm ^ 2 * T := by
      rw [norm_mul]
      calc ‖mass2 F / ((X ∩ P).card : ℂ)‖ * ‖∑ z ∈ Y ∩ P, pair (pbp z) g‖
          ≤ ‖mass2 F / ((X ∩ P).card : ℂ)‖ * ((Y ∩ P).card * ℓ ^ 2) := by gcongr
        _ ≤ ‖mass2 F‖ * ℓ ^ 2 := norm_div_card_mul_le _ (card_inter_le hYX) (by positivity)
        _ ≤ 2 * Cm ^ 2 * ℓ⁻¹ ^ 2 * T * ℓ ^ 2 := by gcongr
        _ = 2 * Cm ^ 2 * T := by field_simp
    refine (norm_add_le _ _).trans ((add_le_add hA hB).trans (le_of_eq ?_))
    ring
  · rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal (tNorm_ne_top hs hℓ F)]

/-! ### Contraction (`prop:Loc-obs` (ii)) -/

/-- The common setting: `θ = L^{-(d-2)/2}` and `2ℓ_{j+1}/ℓ_j = 2θ`, `θ^2 ≤ L^{-1}`. -/
theorem theta_facts (hd : 3 ≤ d) (hL : 2 ^ (d + 3) + 8 * d < L) {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀)
    (j : ℕ) :
    2 * ellj d L ℓ₀ (j + 1) / ellj d L ℓ₀ j = 2 * (L : ℝ) ^ (-((d : ℝ) - 2) / 2) ∧
      ((L : ℝ) ^ (-((d : ℝ) - 2) / 2)) ^ 2 ≤ 1 / L ∧
      2 * ellj d L ℓ₀ (j + 1) ≤ ellj d L ℓ₀ j := by
  have h2 : 0 < 2 ^ (d + 3) := by positivity
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
  have hL0 : (0 : ℝ) < L := by linarith
  have hL4 : (4 : ℝ) ≤ L := by
    have : 4 ≤ L := by omega
    exact_mod_cast this
  have hℓ := ellj_pos (d := d) hL0 hℓ₀ j
  refine ⟨?_, ?_, two_ellj_succ_le hd hL4 hℓ₀ j⟩
  · rw [ellj_succ hL0 j]; field_simp
  · have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
    have := theta_pow_div_le (d := d) hL1 2 0 (e := -1) (by push_cast; nlinarith)
    rw [pow_zero, div_one, Real.rpow_neg_one] at this
    rwa [one_div]

/-- `‖G‖_{T_j} ≤ (1 + C) ‖F‖_{T_j}` for `G = F - Loc F`. -/
theorem tNorm_sub_loc_le {j : ℕ} {ℓ C : ℝ} (hs : (0 : ℝ) < (L : ℝ) ^ j) (hℓ : 0 < ℓ)
    (hC : 0 ≤ C) {F LF : Alg d L N}
    (hLF : Tj d (L : ℝ) j ℓ LF ≤ ENNReal.ofReal C * Tj d (L : ℝ) j ℓ F) :
    (Tj d (L : ℝ) j ℓ (F - LF)).toReal ≤ (1 + C) * (Tj d (L : ℝ) j ℓ F).toReal := by
  set T := (Tj d (L : ℝ) j ℓ F).toReal
  have hT : 0 ≤ T := ENNReal.toReal_nonneg
  have hTF : Tj d (L : ℝ) j ℓ F = ENNReal.ofReal T :=
    (ENNReal.ofReal_toReal (tNorm_ne_top hs hℓ F)).symm
  have h1 := tNorm_sub_le (E := Dir d) (p := pPhi d) (h := (L : ℝ) ^ j) (ℓ := ℓ) F LF
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) (h1.trans ?_)
  rw [show tNorm (Dir d) (pPhi d) ((L : ℝ) ^ j) ℓ F = Tj d (L : ℝ) j ℓ F from rfl, hTF]
  calc ENNReal.ofReal T + tNorm (Dir d) (pPhi d) ((L : ℝ) ^ j) ℓ LF
      ≤ ENNReal.ofReal T + ENNReal.ofReal C * ENNReal.ofReal T := by
        gcongr
        rw [← hTF]; exact hLF
    _ = ENNReal.ofReal ((1 + C) * T) := by
        rw [← ENNReal.ofReal_mul hC, ← ENNReal.ofReal_add hT (by positivity)]
        congr 1; ring

/-- `prop:Loc-obs` (ii) for odd components of charge `-s` (Case (1): `F_a` with `s = -1`,
`F_b` with `s = +1`): `‖F - loc_X F‖_{T_{j+1}(2ℓ_{j+1})} ≤ C θ L^{-1} ‖F‖_{T_j(ℓ_j)}`. -/
theorem exists_odd_contract (d : ℕ) (hd : 3 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℕ) [NeZero L],
    2 ^ (d + 3) + 8 * d < L → ∀ N j : ℕ, j < N → ∀ ℓ₀ : ℝ, 0 < ℓ₀ →
    ∀ X : Finset (Lam d L N), IsSmall j X → ∀ (s : ℤˣ) (P : Finset (Lam d L N)),
    (X ∩ P).Nonempty → ∀ F ∈ NX (nbhd j X : Set (Lam d L N)), HasCharge (-(s : ℤ)) F →
      Tj d (L : ℝ) (j + 1) (2 * ellj d L ℓ₀ (j + 1)) (F - locOdd s P X X F) ≤
        ENNReal.ofReal (C * (L : ℝ) ^ (-((d : ℝ) - 2) / 2) / L) *
          Tj d (L : ℝ) j (ellj d L ℓ₀ j) F := by
  obtain ⟨Cb, hCb0, hCb⟩ := exists_odd_bound d
  obtain ⟨Cc, hCc0, hCc⟩ := exists_core_bound d 1 3 (by omega)
  refine ⟨(1 + Cb) * (2 * Cc + 8), by positivity, ?_⟩
  intro L _ hL N j hj ℓ₀ hℓ₀ X hX s P hP F hF hFc
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  obtain ⟨hratio, hθ2, hℓ'ℓ⟩ := theta_facts hd hL hℓ₀ j
  set ℓ := ellj d L ℓ₀ j
  set ℓ' := 2 * ellj d L ℓ₀ (j + 1)
  set θ : ℝ := (L : ℝ) ^ (-((d : ℝ) - 2) / 2)
  have hθ0 : 0 ≤ θ := Real.rpow_nonneg hL0.le _
  have hℓ : 0 < ℓ := ellj_pos hL0 hℓ₀ j
  have hℓ' : 0 < ℓ' := by have := ellj_pos (d := d) hL0 hℓ₀ (j + 1); positivity
  have hs : (0 : ℝ) < (L : ℝ) ^ j := by positivity
  set T := (Tj d (L : ℝ) j ℓ F).toReal
  have hT : 0 ≤ T := ENNReal.toReal_nonneg
  set G := F - locOdd s P X X F
  have hGmem : G ∈ NX (nbhd j X : Set (Lam d L N)) :=
    sub_mem hF (NX_mono (inter_subset_nbhd hX.1 P) (locOdd_mem s P X X F))
  have hTG : (Tj d (L : ℝ) j ℓ G).toReal ≤ (1 + Cb) * T :=
    tNorm_sub_loc_le hs hℓ hCb0 (hCb L hL N j hj X X hX subset_rfl F hF s P ℓ hℓ)
  -- the masses of `G` at length one vanish
  have hGm : ∀ σ : Fin 1 → ℤˣ, ∑ x : Fin 1 → Lam d L N, coeff G (fun k => (x k, σ k)) = 0 := by
    intro σ
    rw [sum_seq_one, mass1_sub]
    by_cases hσ : σ 0 = s
    · rw [hσ, mass1_locOdd hP, sub_self]
    · rw [mass1_locOdd_ne s (σ 0) hσ, sub_zero]
      refine sum_eq_zero fun y _ => hFc 1 _ ?_
      rw [charge_single]
      intro h
      exact hσ (Units.ext (neg_inj.1 h))
  -- the other short coefficients vanish
  have hG0 : ∀ (n : ℕ) (z : Fin n → Sf (Lam d L N)), n ≠ 1 → n < 3 → coeff G z = 0 := by
    intro n z hn1 hn3
    rw [coeff_sub', coeff_locOdd_of_ne s P X X F z hn1, sub_zero]
    refine hFc n z fun h => ?_
    have h2 := charge_add z
    rcases units_val_eq s with h1 | h1 <;> rw [h1] at h <;> omega
  have hc := hCc L hL N j hj X hX G hGmem hGm hG0 ℓ ℓ' hℓ hℓ' hℓ'ℓ
  rw [hratio] at hc
  refine hc.trans ?_
  have hTF : Tj d (L : ℝ) j ℓ F = ENNReal.ofReal T :=
    (ENNReal.ofReal_toReal (tNorm_ne_top hs hℓ F)).symm
  rw [hTF, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h3 : (2 * θ) ^ 3 ≤ 8 * θ / L := by
    calc (2 * θ) ^ 3 = 8 * θ * θ ^ 2 := by ring
      _ ≤ 8 * θ * (1 / L) := by gcongr
      _ = 8 * θ / L := by ring
  have hX0 : 0 ≤ Cc * (2 * θ) ^ 1 / L + (2 * θ) ^ 3 := by positivity
  calc (Tj d (L : ℝ) j ℓ G).toReal * (Cc * (2 * θ) ^ 1 / L + (2 * θ) ^ 3)
      ≤ ((1 + Cb) * T) * (Cc * (2 * θ) ^ 1 / L + (2 * θ) ^ 3) :=
        mul_le_mul_of_nonneg_right hTG hX0
    _ ≤ ((1 + Cb) * T) * ((2 * Cc + 8) * θ / L) := by
        gcongr
        have : Cc * (2 * θ) ^ 1 / L = 2 * Cc * θ / L := by ring
        rw [this]
        have : (2 * Cc + 8) * θ / L = 2 * Cc * θ / L + 8 * θ / L := by ring
        rw [this]
        linarith
    _ = (1 + Cb) * (2 * Cc + 8) * θ / L * T := by ring

/-- `prop:Loc-obs` (ii) for even, `U(1)`-invariant components (`F_{ab}` in both cases, `F_a`,
`F_b` in Case (2)): `‖F - loc_X F‖_{T_{j+1}(2ℓ_{j+1})} ≤ C θ^2 L^{-1} ‖F‖_{T_j(ℓ_j)}`. -/
theorem exists_even_contract (d : ℕ) (hd : 3 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℕ) [NeZero L],
    2 ^ (d + 3) + 8 * d < L → ∀ N j : ℕ, j < N → ∀ ℓ₀ : ℝ, 0 < ℓ₀ →
    ∀ X : Finset (Lam d L N), IsSmall j X → ∀ P : Finset (Lam d L N),
    (X ∩ P).Nonempty → ∀ F ∈ NX (nbhd j X : Set (Lam d L N)), HasCharge 0 F →
      Tj d (L : ℝ) (j + 1) (2 * ellj d L ℓ₀ (j + 1)) (F - locEven P X X F) ≤
        ENNReal.ofReal (C * ((L : ℝ) ^ (-((d : ℝ) - 2) / 2)) ^ 2 / L) *
          Tj d (L : ℝ) j (ellj d L ℓ₀ j) F := by
  obtain ⟨Cb, hCb0, hCb⟩ := exists_even_bound d
  obtain ⟨Cc, hCc0, hCc⟩ := exists_core_bound d 2 4 (by omega)
  refine ⟨(1 + Cb) * (4 * Cc + 16), by positivity, ?_⟩
  intro L _ hL N j hj ℓ₀ hℓ₀ X hX P hP F hF hFc
  have hsym : IsSym F := (hasCharge_zero_iff F).1 hFc
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  obtain ⟨hratio, hθ2, hℓ'ℓ⟩ := theta_facts hd hL hℓ₀ j
  set ℓ := ellj d L ℓ₀ j
  set ℓ' := 2 * ellj d L ℓ₀ (j + 1)
  set θ : ℝ := (L : ℝ) ^ (-((d : ℝ) - 2) / 2)
  have hθ0 : 0 ≤ θ := Real.rpow_nonneg hL0.le _
  have hℓ : 0 < ℓ := ellj_pos hL0 hℓ₀ j
  have hℓ' : 0 < ℓ' := by have := ellj_pos (d := d) hL0 hℓ₀ (j + 1); positivity
  have hs : (0 : ℝ) < (L : ℝ) ^ j := by positivity
  set T := (Tj d (L : ℝ) j ℓ F).toReal
  have hT : 0 ≤ T := ENNReal.toReal_nonneg
  set G := F - locEven P X X F
  have hGmem : G ∈ NX (nbhd j X : Set (Lam d L N)) :=
    sub_mem hF (NX_mono (inter_subset_nbhd hX.1 P) (locEven_mem P X X F))
  have hTG : (Tj d (L : ℝ) j ℓ G).toReal ≤ (1 + Cb) * T :=
    tNorm_sub_loc_le hs hℓ hCb0 (hCb L hL N j hj X X hX subset_rfl F hF P ℓ hℓ)
  have hsame : ∀ (x y : Lam d L N) (σ : ℤˣ), coeff G ![(x, σ), (y, σ)] = 0 := fun x y σ => by
    rw [coeff_sub', coeff_same_spin_eq_zero hsym, coeff_locEven_same, sub_zero]
  have hmass : mass2 G = 0 := by rw [mass2_sub, mass2_locEven hP, sub_self]
  -- the masses of `G` at length two vanish
  have hGm : ∀ σ : Fin 2 → ℤˣ, ∑ x : Fin 2 → Lam d L N, coeff G (fun k => (x k, σ k)) = 0 := by
    intro σ
    rw [sum_seq_two]
    rcases Int.units_eq_one_or (σ 0) with h0 | h0 <;>
      rcases Int.units_eq_one_or (σ 1) with h1 | h1 <;> rw [h0, h1]
    · simp only [hsame, sum_const_zero]
    · have e : ∀ x y : Lam d L N, coeff G ![(x, 1), (y, -1)] = -coeff G ![(y, -1), (x, 1)] :=
        fun x y => coeff_swap_two G (y, -1) (x, 1)
      simp only [e, sum_neg_distrib]
      rw [sum_comm]
      have : mass2 G = ∑ y, ∑ x, coeff G ![(y, -1), (x, 1)] := rfl
      rw [← this, hmass, neg_zero]
    · exact hmass
    · simp only [hsame, sum_const_zero]
  -- the other short coefficients vanish
  have hG0 : ∀ (n : ℕ) (z : Fin n → Sf (Lam d L N)), n ≠ 2 → n < 4 → coeff G z = 0 := by
    intro n z hn2 hn4
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      rw [coeff_elim0, map_sub, eps_locEven hP, sub_self]
    · rw [coeff_sub', coeff_locEven_of_ne P X X F z (by omega) hn2, sub_zero]
      exact coeff_eq_zero_of_odd hsym (Nat.odd_iff.2 (by omega)) z
  have hc := hCc L hL N j hj X hX G hGmem hGm hG0 ℓ ℓ' hℓ hℓ' hℓ'ℓ
  rw [hratio] at hc
  refine hc.trans ?_
  have hTF : Tj d (L : ℝ) j ℓ F = ENNReal.ofReal T :=
    (ENNReal.ofReal_toReal (tNorm_ne_top hs hℓ F)).symm
  rw [hTF, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h4 : (2 * θ) ^ 4 ≤ 16 * θ ^ 2 / L := by
    calc (2 * θ) ^ 4 = 16 * θ ^ 2 * θ ^ 2 := by ring
      _ ≤ 16 * θ ^ 2 * (1 / L) := by gcongr
      _ = 16 * θ ^ 2 / L := by ring
  have hX0 : 0 ≤ Cc * (2 * θ) ^ 2 / L + (2 * θ) ^ 4 := by positivity
  calc (Tj d (L : ℝ) j ℓ G).toReal * (Cc * (2 * θ) ^ 2 / L + (2 * θ) ^ 4)
      ≤ ((1 + Cb) * T) * (Cc * (2 * θ) ^ 2 / L + (2 * θ) ^ 4) :=
        mul_le_mul_of_nonneg_right hTG hX0
    _ ≤ ((1 + Cb) * T) * ((4 * Cc + 16) * θ ^ 2 / L) := by
        gcongr
        have : Cc * (2 * θ) ^ 2 / L = 4 * Cc * θ ^ 2 / L := by ring
        rw [this]
        have : (4 * Cc + 16) * θ ^ 2 / L = 4 * Cc * θ ^ 2 / L + 16 * θ ^ 2 / L := by ring
        rw [this]
        linarith
    _ = (1 + Cb) * (4 * Cc + 16) * θ ^ 2 / L * T := by ring

end

end Obs.LocObs
