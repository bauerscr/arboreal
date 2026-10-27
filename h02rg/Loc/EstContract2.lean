import Loc.EstContract1

/-!
# The contraction bound on sequences of length `2`, `4` and `6`

* length `4` and `6` (and generally even `n ≥ 4`): the antisymmetric test function vanishes when
  two entries of equal spin coincide, which gains `L^{-2}`;
* length `2`: the pairing kills the Taylor polynomial of degree `2`, and the remainder gains
  `L^{-3}`.
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD Equiv

/-! ### Arithmetic of the scales -/

theorem vanish_scale {L s r C : ℝ} (hL : 1 ≤ L) (hs : 1 ≤ s) (hr0 : 0 ≤ r) (hr : r ≤ C * s)
    (q : ℕ) :
    r ^ (2 - min q 2) * ((L * s)⁻¹) ^ (max q 2) * s ^ q ≤ (C + 1) ^ 2 / L ^ 2 := by
  have hL0 : 0 < L := by linarith
  have hs0 : 0 < s := by linarith
  have hC : 0 ≤ C := by
    by_contra h; push Not at h; nlinarith
  rcases Nat.lt_or_ge q 2 with hq | hq
  · interval_cases q
    · simp only [min_self, Nat.sub_zero, zero_le, max_eq_right, pow_zero, mul_one]
      calc r ^ 2 * ((L * s)⁻¹) ^ 2 ≤ (C * s) ^ 2 * ((L * s)⁻¹) ^ 2 := by gcongr
        _ = C ^ 2 / L ^ 2 := by field_simp
        _ ≤ (C + 1) ^ 2 / L ^ 2 := by gcongr; linarith
    · simp only [show min 1 2 = 1 by rfl, show max 1 2 = 2 by rfl, show 2 - 1 = 1 by rfl, pow_one]
      calc r * ((L * s)⁻¹) ^ 2 * s ≤ (C * s) * ((L * s)⁻¹) ^ 2 * s := by gcongr
        _ = C / L ^ 2 := by field_simp
        _ ≤ (C + 1) ^ 2 / L ^ 2 := by gcongr; nlinarith
  · rw [min_eq_right hq, max_eq_left hq, Nat.sub_self, pow_zero, one_mul]
    calc ((L * s)⁻¹) ^ q * s ^ q = (L ^ q)⁻¹ := by
          rw [inv_pow, mul_pow]; field_simp
      _ ≤ (L ^ 2)⁻¹ := inv_anti₀ (by positivity) (pow_le_pow_right₀ hL hq)
      _ = 1 / L ^ 2 := by ring
      _ ≤ (C + 1) ^ 2 / L ^ 2 := by gcongr; nlinarith

theorem taylor_scale {L s r C : ℝ} (hL : 1 ≤ L) (hs : 1 ≤ s) (hr0 : 0 ≤ r) (hr : r ≤ C * s)
    (q : ℕ) :
    r ^ (3 - min q 3) * ((L * s)⁻¹) ^ (max q 3) * s ^ q ≤ (C + 1) ^ 3 / L ^ 3 := by
  have hL0 : 0 < L := by linarith
  have hs0 : 0 < s := by linarith
  have hC : 0 ≤ C := by
    by_contra h; push Not at h; nlinarith
  have hC1 : 1 ≤ C + 1 := by linarith
  rcases Nat.lt_or_ge q 3 with hq | hq
  · have e1 : max q 3 = 3 := max_eq_right hq.le
    have e2 : min q 3 = q := min_eq_left hq.le
    rw [e1, e2]
    calc r ^ (3 - q) * ((L * s)⁻¹) ^ 3 * s ^ q ≤ (C * s) ^ (3 - q) * ((L * s)⁻¹) ^ 3 * s ^ q := by
          gcongr
      _ = C ^ (3 - q) / L ^ 3 := by
          rw [mul_pow, inv_pow, mul_pow]
          have : s ^ (3 - q) * s ^ q = s ^ 3 := by rw [← pow_add]; congr 1; omega
          rw [show C ^ (3 - q) * s ^ (3 - q) * (L ^ 3 * s ^ 3)⁻¹ * s ^ q =
            C ^ (3 - q) * (s ^ (3 - q) * s ^ q) * (L ^ 3 * s ^ 3)⁻¹ by ring, this]
          field_simp
      _ ≤ (C + 1) ^ 3 / L ^ 3 := by
          gcongr
          calc C ^ (3 - q) ≤ (C + 1) ^ (3 - q) := by gcongr; linarith
            _ ≤ (C + 1) ^ 3 := pow_le_pow_right₀ hC1 (by omega)
  · rw [min_eq_right hq, max_eq_left hq, Nat.sub_self, pow_zero, one_mul]
    calc ((L * s)⁻¹) ^ q * s ^ q = (L ^ q)⁻¹ := by
          rw [inv_pow, mul_pow]; field_simp
      _ ≤ (L ^ 3)⁻¹ := inv_anti₀ (by positivity) (pow_le_pow_right₀ hL hq)
      _ = 1 / L ^ 3 := by ring
      _ ≤ (C + 1) ^ 3 / L ^ 3 := by gcongr; exact one_le_pow₀ hC1

/-! ### Spins -/

theorem card_spins_add' {Y : Type*} {n : ℕ} (z : Fin n → Sf Y) :
    (univ.filter fun i => (z i).2 = 1).card + (univ.filter fun i => (z i).2 = -1).card = n := by
  rw [← card_union_of_disjoint]
  · have : (univ.filter fun i => (z i).2 = 1) ∪ (univ.filter fun i => (z i).2 = -1) = univ := by
      ext i
      simp only [mem_union, mem_filter, mem_univ, true_and, iff_true]
      exact Int.units_eq_one_or _
    rw [this, card_univ, Fintype.card_fin]
  · rw [disjoint_filter]
    intro i _ h1 h2
    exact absurd (h1.symm.trans h2) (by decide)

/-- The `U(1)` condition on spins. -/
def U1 {n : ℕ} (σ : Fin n → ℤˣ) : Prop :=
  (univ.filter fun i => σ i = 1).card = (univ.filter fun i => σ i = -1).card

instance {n : ℕ} : DecidablePred (U1 (n := n)) := fun _ => by unfold U1; infer_instance

theorem exists_pairs {Y : Type*} {n : ℕ} (hn : 4 ≤ n) {w : Fin n → Sf Y} (hw : U1 (spins w)) :
    ∃ i₁ i₂ k₁ k₂ : Fin n, i₁ ≠ i₂ ∧ k₁ ≠ k₂ ∧ (w i₁).2 = (w i₂).2 ∧ (w k₁).2 = (w k₂).2 ∧
      (w i₁).2 ≠ (w k₁).2 := by
  have hc := card_spins_add' w
  unfold U1 spins at hw
  have h1 : 1 < (univ.filter fun i => (w i).2 = 1).card := by omega
  have h2 : 1 < (univ.filter fun i => (w i).2 = -1).card := by omega
  obtain ⟨i₁, hi₁, i₂, hi₂, hi⟩ := one_lt_card.1 h1
  obtain ⟨k₁, hk₁, k₂, hk₂, hk⟩ := one_lt_card.1 h2
  simp only [mem_filter, mem_univ, true_and] at hi₁ hi₂ hk₁ hk₂
  exact ⟨i₁, i₂, k₁, k₂, hi, hk, hi₁.trans hi₂.symm, hk₁.trans hk₂.symm,
    by rw [hi₁, hk₁]; decide⟩

variable {d L N : ℕ} [NeZero L]

/-! ### Common facts -/

theorem cutS_ρS_eq_one {j : ℕ} {X : Finset (Lam d L N)} (hX : IsSmall j X) {n : ℕ}
    (z : Fin n → Sf (Lam d L N)) (hz : ∀ i, (z i).1 ∈ nbhd j X) :
    cutS (rad d L j : ℝ) (ρS (base X) ∘ z) = 1 := by
  have hR0 : (0 : ℝ) < (rad d L j : ℝ) := by exact_mod_cast one_le_rad (d := d) (L := L) j
  unfold cutS
  refine prod_eq_one fun k _ => ?_
  have hk : (supNormZ (ρS (base X) (z k)).1 : ℝ) ≤ (rad d L j : ℝ) := by
    rw [supNormZ_ρS]; exact_mod_cast supNorm_nbhd_base hX (hz k)
  simp only [Function.comp_apply]
  rw [cutP_eq 0 hR0 hk]
  simp

theorem radius_le (j : ℕ) :
    ((2 * rad d L j + 2 * pPhi d : ℕ) : ℝ) ≤ (2 ^ (d + 2) + 4 * d : ℝ) * (L : ℝ) ^ j := by
  have hLj : (1 : ℝ) ≤ (L : ℝ) ^ j :=
    one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
  push_cast [rad, pPhi]
  have : (2 : ℝ) ^ (d + 2) = 2 * 2 ^ (d + 1) := by ring
  rw [this]
  nlinarith

theorem nab_pos {n : ℕ} (γ : Fin n → Dir d → ℕ) (Φ : (Fin n → Zd d) → ℂ)
    (w : Fin n → Sf (Zd d)) :
    nab γ (fun w => Φ fun k => (w k).1) w =
      nabla (fun b u => b +ᵥ u) γ Φ (fun k => (w k).1) :=
  nabla_comp_pi sh (fun b u => b +ᵥ u) (fun _ a => a.1) (fun _ _ _ => rfl) γ Φ w

/-! ### Lengths `n ≥ 4` -/

theorem exists_long_bound (d n : ℕ) (hd : 1 ≤ d) (hn : 4 ≤ n) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (L : ℕ) [NeZero L], 2 ^ (d + 3) + 8 * d < L → ∀ N j : ℕ, j < N →
    ∀ X : Finset (Lam d L N), IsSmall j X → ∀ F ∈ NX (nbhd j X : Set (Lam d L N)), IsSym F →
    ∀ ℓ ℓ' : ℝ, 0 < ℓ → 0 < ℓ' → ∀ g : (Fin n → Sf (Lam d L N)) → ℂ,
    (∀ z : Fin n → Sf (Lam d L N), ¬Function.Injective z → g z = 0) →
    (∀ (z : Fin n → Sf (Lam d L N)) (γ : Fin n → Dir d → ℕ), (∀ k, mabs (γ k) ≤ pPhi d) →
      ‖nab γ g z‖ ≤ ℓ' ^ n * (((L : ℝ) ^ (j + 1)) ^ ord γ)⁻¹) →
    ‖pair F (single n g)‖ ≤
      (Tj d (L : ℝ) j ℓ F).toReal * (C * ℓ' ^ n * ℓ⁻¹ ^ n / (L : ℝ) ^ 2) := by
  obtain ⟨Cl, hCl0, hCl⟩ := exists_localized_bound d
  set C1 : ℝ := 2 * d * (2 ^ (d + 2) + 4 * d)
  refine ⟨Cl ^ n * (C1 + 1) ^ 2, by positivity, ?_⟩
  intro L _ hL N j hj X hX F hF hsym ℓ ℓ' hℓ hℓ' g hg0 hgb
  set b := base X
  set R : ℝ := (rad d L j : ℝ)
  set s : ℝ := (L : ℝ) ^ j
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hs1 : 1 ≤ s := one_le_pow₀ hL1
  have hs0 : 0 < s := by linarith
  have hh' : (L : ℝ) ^ (j + 1) = L * s := by rw [pow_succ, mul_comm]
  set U : (Fin n → Sf (Zd d)) → ℂ := fun w => g (ιS b ∘ w)
  -- the pairing
  have hpair : pair F (single n g) = pair F (single n (fun z => locH U1 U R (ρS b ∘ z))) := by
    rw [pair_single, pair_single]
    congr 1
    refine sum_congr rfl fun z _ => ?_
    by_cases hz : ∀ i, (z i).1 ∈ nbhd j X
    · by_cases hU : U1 (spins z)
      · have e1 : locH U1 U R (ρS b ∘ z) = g z := by
          simp only [locH]
          rw [if_pos (show U1 (spins (ρS b ∘ z)) from hU), cutS_ρS_eq_one hX z hz,
            Complex.ofReal_one, one_mul]
          simp only [U]
          congr 1
          funext i; exact ιS_ρS b (z i)
        rw [e1]
      · rw [hsym n z hU]; ring
    · push Not at hz
      obtain ⟨i, hi⟩ := hz
      rw [coeff_eq_zero_of_mem_NX hF z i hi]; ring
  -- the bound on `U`
  have hUbound : ∀ w : Fin n → Sf (Zd d), U1 (spins w) →
      (∀ k, supNormZ (w k).1 ≤ 2 * rad d L j + 2 * pPhi d) →
      ∀ δ : Fin n → Dir d → ℕ, (∀ k, mabs (δ k) ≤ pPhi d) →
        ‖nab δ U w‖ * s ^ ord δ ≤ ℓ' ^ n * ((C1 + 1) ^ 2 / (L : ℝ) ^ 2) := by
    intro w hw hr δ hδ
    obtain ⟨i₁, i₂, k₁, k₂, hi, hk, hsi, hsk, hik⟩ := exists_pairs hn hw
    have hv := vanish_bound U (K := ℓ' ^ n) (ε := ((L : ℝ) ^ (j + 1))⁻¹) (P := pPhi d)
      (by simp [pPhi]; omega) (by positivity) (by positivity)
      (fun w hw => hg0 _ fun hinj => hw fun a a' haa =>
        hinj (show (ιS b ∘ w) a = (ιS b ∘ w) a' by simp only [Function.comp_apply, haa]))
      (fun w γ hγ => by
        simp only [U]
        rw [nab_comp_ιS, inv_pow]
        exact hgb _ γ hγ) hi hk hsi hsk hik hr δ hδ
    rw [hh'] at hv
    have hr' : ((2 * d * (2 * rad d L j + 2 * pPhi d) : ℕ) : ℝ) ≤ C1 * s := by
      have := radius_le (d := d) (L := L) j
      push_cast at this ⊢
      simp only [C1, s]
      nlinarith
    have hsc := vanish_scale hL1 hs1 (Nat.cast_nonneg _) hr' (ord δ)
    calc ‖nab δ U w‖ * s ^ ord δ
        ≤ ℓ' ^ n * ((2 * d * (2 * rad d L j + 2 * pPhi d) : ℕ) : ℝ) ^ (2 - min (ord δ) 2) *
            ((L * s)⁻¹) ^ max (ord δ) 2 * s ^ ord δ := by gcongr
      _ = ℓ' ^ n * (((2 * d * (2 * rad d L j + 2 * pPhi d) : ℕ) : ℝ) ^ (2 - min (ord δ) 2) *
            ((L * s)⁻¹) ^ max (ord δ) 2 * s ^ ord δ) := by ring
      _ ≤ ℓ' ^ n * ((C1 + 1) ^ 2 / (L : ℝ) ^ 2) := by gcongr
  have hnorm := hCl n L hL N j hj b U1 U _ (by positivity) hUbound ℓ hℓ
  rw [hpair]
  refine (abs_pair_le (by positivity) hℓ F (by positivity) hnorm).trans (le_of_eq ?_)
  simp only [Tj]
  ring

/-! ### Length `2` -/

/-- The spin pattern `(+, -)`. -/
def pat2 : Fin 2 → ℤˣ := ![1, -1]

theorem exists_two_bound (d : ℕ) (hd : 2 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (L : ℕ) [NeZero L], 2 ^ (d + 3) + 8 * d < L → ∀ N j : ℕ, j < N →
    ∀ X : Finset (Lam d L N), IsSmall j X → ∀ G ∈ NX (nbhd j X : Set (Lam d L N)),
    (∀ (a a' : Lam d L N) (σ : ℤˣ), coeff G ![(a, σ), (a', σ)] = 0) →
    (∀ β : Mono d, mu (base X) β G = 0) →
    ∀ ℓ ℓ' : ℝ, 0 < ℓ → 0 < ℓ' → ∀ g : (Fin 2 → Sf (Lam d L N)) → ℂ,
    (∀ a a', g ![a', a] = -g ![a, a']) →
    (∀ (z : Fin 2 → Sf (Lam d L N)) (γ : Fin 2 → Dir d → ℕ), (∀ k, mabs (γ k) ≤ pPhi d) →
      ‖nab γ g z‖ ≤ ℓ' ^ 2 * (((L : ℝ) ^ (j + 1)) ^ ord γ)⁻¹) →
    ‖pair G (single 2 g)‖ ≤
      (Tj d (L : ℝ) j ℓ G).toReal * (C * ℓ' ^ 2 * ℓ⁻¹ ^ 2 / (L : ℝ) ^ 3) := by
  obtain ⟨Cl, hCl0, hCl⟩ := exists_localized_bound d
  set C2 : ℝ := 2 * d * (2 ^ (d + 2) + 4 * d + 2)
  refine ⟨Cl ^ 2 * (2 * (C2 + 1) ^ 3), by positivity, ?_⟩
  intro L _ hL N j hj X hX G hG hGs hGμ ℓ ℓ' hℓ hℓ' g hga hgb
  set b := base X
  set R : ℝ := (rad d L j : ℝ)
  set s : ℝ := (L : ℝ) ^ j
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hs1 : 1 ≤ s := one_le_pow₀ hL1
  have hs0 : 0 < s := by linarith
  have hh' : (L : ℝ) ^ (j + 1) = L * s := by rw [pow_succ, mul_comm]
  have hne : X.Nonempty := hX.2.1.1
  -- the function on `ℤ^d` and its Taylor remainder
  set Φ : (Fin 2 → Zd d) → ℂ := fun v => g fun k => (ιZ b (v k), pat2 k)
  set U : (Fin 2 → Sf (Zd d)) → ℂ :=
    fun w => 2 * (Φ (fun k => (w k).1) - taylor2 Φ (fun k => (w k).1))
  set P2 : (Fin 2 → ℤˣ) → Prop := fun σ => σ = pat2
  have hΦval : ∀ x y : Lam d L N, Φ (wxy b x y) = g ![(x, 1), (y, -1)] := by
    intro x y
    simp only [Φ]
    congr 1
    funext k
    fin_cases k <;> simp [wxy, pat2, ιZ, prj_rep]
  -- the pairing
  have hpair : pair G (single 2 g) = pair G (single 2 (fun z => locH P2 U R (ρS b ∘ z))) := by
    rw [pair_single_two_antisymm G hGs g hga, pair_single_two G _ (fun z hz => by
      simp only [locH, P2]
      rw [if_neg (show ¬ P2 (spins (ρS b ∘ z)) from hz)])]
    have hloc : ∀ x y : Lam d L N, locH P2 U R (ρS b ∘ ![(x, 1), (y, -1)]) =
        (cutS R (ρS b ∘ ![(x, 1), (y, -1)]) : ℂ) *
          (2 * (Φ (wxy b x y) - taylor2 Φ (wxy b x y))) := by
      intro x y
      have hsp : spins (ρS b ∘ ![(x, 1), (y, -1)]) = pat2 := by
        funext k; fin_cases k <;> rfl
      have hpos : (fun k => ((ρS b ∘ ![(x, 1), (y, -1)]) k).1) = wxy b x y := by
        funext k; fin_cases k <;> rfl
      simp only [locH, P2, hsp, if_true, U, hpos]
    simp only [hloc]
    have key : ∀ x y : Lam d L N,
        (1 / 2 : ℂ) * (coeff G ![(x, 1), (y, -1)] * ((cutS R (ρS b ∘ ![(x, 1), (y, -1)]) : ℂ) *
          (2 * (Φ (wxy b x y) - taylor2 Φ (wxy b x y))))) =
        coeff G ![(x, 1), (y, -1)] * g ![(x, 1), (y, -1)] -
          cf2 G x y * taylor2 Φ (wxy b x y) := by
      intro x y
      by_cases hx : x ∈ nbhd j X
      · by_cases hy : y ∈ nbhd j X
        · have hz : ∀ i, (![(x, (1 : ℤˣ)), (y, -1)] i).1 ∈ nbhd j X := by
            intro i; fin_cases i
            · exact hx
            · exact hy
          rw [cutS_ρS_eq_one hX _ hz, Complex.ofReal_one, hΦval, cf2]; ring
        · rw [cf2, coeff_eq_zero_of_mem_NX hG _ 1 (by simpa using hy)]; ring
      · rw [cf2, coeff_eq_zero_of_mem_NX hG _ 0 (by simpa using hx)]; ring
    rw [mul_sum]
    simp only [mul_sum, key, sum_sub_distrib]
    have h0 := omegaL_taylor2 (b := b) (G := G) hGμ Φ
    rw [omegaL_apply] at h0
    rw [h0, sub_zero]
  -- the bound on the remainder
  have hΦb : ∀ (v : Fin 2 → Zd d) (γ : Fin 2 → Dir d → ℕ), (∀ k, mabs (γ k) ≤ pPhi d) →
      ‖nabla (fun b u => b +ᵥ u) γ Φ v‖ ≤ ℓ' ^ 2 * (((L : ℝ) ^ (j + 1))⁻¹) ^ ord γ := by
    intro v γ hγ
    have e := nabla_comp_pi (fun b u => b +ᵥ u) sh (fun k u => (ιZ b u, pat2 k))
      (fun k β u => by simp [sh, ιZ_vadd]) γ g v
    simp only [Φ]
    rw [e, inv_pow]
    exact hgb _ γ hγ
  have hUbound : ∀ w : Fin 2 → Sf (Zd d), P2 (spins w) →
      (∀ k, supNormZ (w k).1 ≤ 2 * rad d L j + 2 * pPhi d) →
      ∀ δ : Fin 2 → Dir d → ℕ, (∀ k, mabs (δ k) ≤ pPhi d) →
        ‖nab δ U w‖ * s ^ ord δ ≤ 2 * ℓ' ^ 2 * ((C2 + 1) ^ 3 / (L : ℝ) ^ 3) := by
    intro w _ hr δ hδ
    have eU : nab δ U w = (2 : ℂ) * nabla (fun (b : Dir d → ℕ) (u : Zd d) => b +ᵥ u) δ
        (fun v => Φ v - taylor2 Φ v) (fun k => (w k).1) := by
      have := nabla_smul (sh (X := Zd d)) δ (2 : ℂ)
        (fun w => Φ (fun k => (w k).1) - taylor2 Φ (fun k => (w k).1)) w
      simp only [smul_eq_mul] at this
      simp only [U]
      rw [this, nab_pos δ (fun v => Φ v - taylor2 Φ v) w]
    have ht := taylor2_bound (K := ℓ' ^ 2) (ε := ((L : ℝ) ^ (j + 1))⁻¹) (P := pPhi d)
      (by positivity) (by positivity) (by simp [pPhi]; omega) hΦb (w := fun k => (w k).1)
      (r := 2 * rad d L j + 2 * pPhi d) hr δ hδ
    rw [hh'] at ht
    have hr' : ((2 * d * (2 * rad d L j + 2 * pPhi d + 2) : ℕ) : ℝ) ≤ C2 * s := by
      have := radius_le (d := d) (L := L) j
      push_cast at this ⊢
      simp only [C2, s]
      nlinarith
    have hsc := taylor_scale hL1 hs1 (Nat.cast_nonneg _) hr' (ord δ)
    rw [eU, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
    calc (2 : ℝ) * ‖nabla (fun (b : Dir d → ℕ) (u : Zd d) => b +ᵥ u) δ
          (fun v => Φ v - taylor2 Φ v) (fun k => (w k).1)‖ * s ^ ord δ
        ≤ (2 : ℝ) * (ℓ' ^ 2 * ((2 * d * (2 * rad d L j + 2 * pPhi d + 2) : ℕ) : ℝ) ^
            (3 - min (ord δ) 3) * ((L * s)⁻¹) ^ max (ord δ) 3) * s ^ ord δ := by
          gcongr
      _ = 2 * ℓ' ^ 2 * (((2 * d * (2 * rad d L j + 2 * pPhi d + 2) : ℕ) : ℝ) ^
            (3 - min (ord δ) 3) * ((L * s)⁻¹) ^ max (ord δ) 3 * s ^ ord δ) := by ring
      _ ≤ 2 * ℓ' ^ 2 * ((C2 + 1) ^ 3 / (L : ℝ) ^ 3) := by gcongr
  have hnorm := hCl 2 L hL N j hj b P2 U _ (by positivity) hUbound ℓ hℓ
  rw [hpair]
  refine (abs_pair_le (by positivity) hℓ G (by positivity) hnorm).trans (le_of_eq ?_)
  simp only [Tj]
  field_simp

end

end Loc
