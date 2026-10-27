import Obs.LocObsDef
import Loc.EstContract

/-!
# Localisation with observables: the analytic ingredients

* `sum_split`: sums over sequences in `Λ_f^n` split into spin patterns and positions;
* `exists_mass_bound`: `|∑_x F_{(x,σ)}| ≤ n! C^n ℓ^{-n} ‖F‖_{T_j(ℓ)}` for `F ∈ 𝒩(X^□)`, `X` small
  (pairing with a cut-off version of the constant test function);
* `taylor0_bound`, `exists_zero_bound`: the Taylor expansion to order `0` — if all the
  "masses" `∑_x G_{(x,σ)}` of the length-`n` part of `G ∈ 𝒩(X^□)` vanish, then the pairing of `G`
  with a test function `g` at scale `j + 1` gains `L^{-1}`:
  `|⟨G, g_n⟩| ≤ C ℓ'^n ℓ^{-n} L^{-1} ‖G‖_{T_j(ℓ)}` if `‖g‖_{Φ_{j+1}(ℓ')} ≤ 1`
  (since `g(z) - g(z_b)`, with all points moved to the base point `b` of `X`, is of size
  `L^j · L^{-(j+1)}`);
* `exists_core_bound`: if moreover the coefficients of `G` vanish for all lengths `n ≠ m`,
  `n < m'`, then `‖G‖_{T_{j+1}(ℓ')} ≤ ‖G‖_{T_j(ℓ)} (C (ℓ'/ℓ)^m L^{-1} + (ℓ'/ℓ)^{m'})`.
-/

namespace Obs.LocObs

noncomputable section

open Finset Grassmann FRD Loc

/-! ### Splitting sums by spins -/

section Split

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

theorem sum_split {n : ℕ} (f : (Fin n → Sf Λ) → ℂ) :
    ∑ z, f z = ∑ τ : Fin n → ℤˣ, ∑ x : Fin n → Λ, f (fun k => (x k, τ k)) := by
  rw [← (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Λ) (fun _ => ℤˣ)).symm.sum_comp,
    Fintype.sum_prod_type, sum_comm]
  rfl

theorem sum_spins_ite {n : ℕ} (σ : Fin n → ℤˣ) (f : (Fin n → Sf Λ) → ℂ) :
    ∑ z, (if spins z = σ then f z else 0) = ∑ x : Fin n → Λ, f (fun k => (x k, σ k)) := by
  rw [sum_split, sum_eq_single σ]
  · exact sum_congr rfl fun x _ => if_pos rfl
  · intro τ _ hτ
    exact sum_eq_zero fun x _ => if_neg hτ
  · simp

theorem sum_fin_one (f : (Fin 1 → Λ) → ℂ) : ∑ x : Fin 1 → Λ, f x = ∑ y, f fun _ => y := by
  rw [← (Equiv.funUnique (Fin 1) Λ).symm.sum_comp]
  rfl

theorem sum_fin_two (f : (Fin 2 → Λ) → ℂ) : ∑ x : Fin 2 → Λ, f x = ∑ x, ∑ y, f ![x, y] := by
  rw [← (piFinTwoEquiv fun _ => Λ).symm.sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  congr 1

theorem seq_one (y : Λ) (s : ℤˣ) (σ : Fin 1 → ℤˣ) (hσ : σ 0 = s) :
    (fun k => ((fun _ => y : Fin 1 → Λ) k, σ k)) = ![(y, s)] := by
  funext k; fin_cases k; simp [hσ]

theorem seq_two (x y : Λ) (σ : Fin 2 → ℤˣ) :
    (fun k => ((![x, y] : Fin 2 → Λ) k, σ k)) = ![(x, σ 0), (y, σ 1)] := by
  funext k; fin_cases k <;> rfl

end Split

/-! ### Derivatives of constants -/

theorem nabla_const_eq_zero {E Y W : Type*} [Fintype E] [DecidableEq E] [AddCommGroup W]
    [Module ℝ W] {n : ℕ} (s : (E → ℕ) → Y → Y) (hsa : ∀ b b' y, s (b + b') y = s b (s b' y))
    {α : Fin n → E → ℕ} (hα : α ≠ 0) (c : W) : nabla s α (fun _ => c) = 0 := by
  obtain ⟨α', i, e, rfl⟩ := exists_eq_add_single hα
  rw [nabla_succ s hsa]
  have : ediff s i e (fun _ : Fin n → Y => c) = 0 := by funext z; simp [ediff]
  rw [this, map_zero]

variable {d : ℕ}

/-! ### Pairing with the constant test function -/

theorem exists_mass_bound (d : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (n L : ℕ) [NeZero L],
    2 ^ (d + 3) + 8 * d < L → ∀ N j : ℕ, j < N → ∀ X : Finset (Lam d L N), IsSmall j X →
    ∀ F ∈ NX (nbhd j X : Set (Lam d L N)), ∀ σ : Fin n → ℤˣ, ∀ ℓ : ℝ, 0 < ℓ →
      ‖∑ x : Fin n → Lam d L N, coeff F (fun k => (x k, σ k))‖ ≤
        n.factorial * C ^ n * ℓ⁻¹ ^ n * (Tj d (L : ℝ) j ℓ F).toReal := by
  obtain ⟨Cl, hCl0, hCl⟩ := exists_localized_bound d
  refine ⟨Cl, hCl0, ?_⟩
  intro n L _ hL N j hj X hX F hF σ ℓ hℓ
  set b := base X
  set R : ℝ := (rad d L j : ℝ)
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hs : (0 : ℝ) < (L : ℝ) ^ j := by positivity
  set U : (Fin n → Sf (Zd d)) → ℂ := fun _ => 1
  have hU : ∀ w : Fin n → Sf (Zd d), (fun τ => τ = σ) (spins w) →
      (∀ k, supNormZ (w k).1 ≤ 2 * rad d L j + 2 * pPhi d) →
      ∀ δ : Fin n → Dir d → ℕ, (∀ k, mabs (δ k) ≤ pPhi d) →
        ‖nab δ U w‖ * ((L : ℝ) ^ j) ^ ord δ ≤ 1 := by
    intro w _ _ δ _
    by_cases hδ : δ = 0
    · subst hδ; rw [nabla_zero _ (fun _ => sh_zero _), ord_zero]; simp [U]
    · rw [show nab δ U = 0 from nabla_const_eq_zero _ shZ_add' hδ (1 : ℂ)]; simp
  have hnorm := hCl n L hL N j hj b (fun τ => τ = σ) U 1 zero_le_one hU ℓ hℓ
  have hpair : pair F (single n (fun z => locH (fun τ => τ = σ) U R (ρS b ∘ z))) =
      (n.factorial : ℂ)⁻¹ * ∑ x : Fin n → Lam d L N, coeff F (fun k => (x k, σ k)) := by
    rw [pair_single]
    congr 1
    rw [← sum_spins_ite]
    refine sum_congr rfl fun z _ => ?_
    have hsp : spins (ρS b ∘ z) = spins z := rfl
    simp only [locH, U, mul_one, hsp]
    split_ifs with h
    · by_cases hz : ∀ i, (z i).1 ∈ nbhd j X
      · rw [cutS_ρS_eq_one hX z hz]; simp
      · push Not at hz
        obtain ⟨i, hi⟩ := hz
        rw [coeff_eq_zero_of_mem_NX hF z i hi]; simp
    · simp
  have := abs_pair_le hs hℓ F (by positivity) hnorm
  rw [hpair, norm_mul, norm_inv, Complex.norm_natCast] at this
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  rw [inv_mul_le_iff₀ hf] at this
  refine this.trans (le_of_eq ?_)
  simp only [Tj]; ring

/-! ### Taylor expansion to order `0` -/

section Taylor0

variable {m : ℕ}

theorem taylor0_bound {Φ : (Fin m → Zd d) → ℂ} {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε) {P : ℕ}
    (hP : 1 ≤ P)
    (hΦ : ∀ (w : Fin m → Zd d) (γ : Fin m → Dir d → ℕ), (∀ k, mabs (γ k) ≤ P) →
      ‖nabla (fun b u => b +ᵥ u) γ Φ w‖ ≤ K * ε ^ ord γ)
    {r : ℕ} {w : Fin m → Zd d} (hw : ∀ k, supNormZ (w k) ≤ r) (γ : Fin m → Dir d → ℕ)
    (hγ : ∀ k, mabs (γ k) ≤ P) :
    ‖nabla (fun b u => b +ᵥ u) γ (fun w => Φ w - Φ 0) w‖ ≤
      K * ((m * d * r : ℕ) : ℝ) ^ (1 - min (ord γ) 1) * ε ^ (max (ord γ) 1) := by
  by_cases hγ0 : γ = 0
  · subst hγ0
    rw [nabla_zero _ hs0Z, ord_zero, show (1 - min 0 1 : ℕ) = 1 from rfl,
      show max 0 1 = 1 from rfl, pow_one, pow_one]
    have hM : ∀ t : Fin m → Zd d, (∀ k, supNormZ (t k) ≤ r) → ∀ k i,
        ‖Dv (ee k i) (fun w => Φ w - Φ 0) t‖ ≤ K * ε := by
      intro t _ k i
      have e : Dv (ee k i) (fun w => Φ w - Φ 0) t = Dv (ee k i) Φ t := by
        simp only [Dv]; ring
      have h := hΦ t (Pi.single k (Pi.single (Sum.inl i) 1)) (fun k' => by
        refine (mabs_le_ord _ k').trans ?_
        rw [ord_single]; exact hP)
      rw [nabla_single _ hs0Z hsaZ, ediff_eq_Dv, ord_single, pow_one] at h
      rw [e]
      exact h
    have := box_step (mul_nonneg hK hε) (g := fun w => Φ w - Φ 0) (by simp) hM w hw
    refine this.trans (le_of_eq ?_)
    ring
  · have hord : 1 ≤ ord γ := by
      by_contra h
      exact hγ0 (ord_eq_zero (by omega))
    have e : nabla (fun b u => b +ᵥ u) γ (fun w => Φ w - Φ 0) =
        nabla (fun (b : Dir d → ℕ) (u : Zd d) => b +ᵥ u) γ Φ := by
      rw [show (fun w => Φ w - Φ 0) = Φ - fun _ => Φ 0 from rfl, map_sub,
        nabla_const_eq_zero _ hsaZ hγ0, sub_zero]
    rw [e, min_eq_right hord, Nat.sub_self, pow_zero, mul_one, max_eq_left hord]
    exact hΦ w γ hγ

end Taylor0

theorem zero_scale {L s r C : ℝ} (hL : 1 ≤ L) (hs : 1 ≤ s) (hr0 : 0 ≤ r) (hr : r ≤ C * s)
    (q : ℕ) : r ^ (1 - min q 1) * ((L * s)⁻¹) ^ (max q 1) * s ^ q ≤ (C + 1) / L := by
  have hL0 : 0 < L := by linarith
  have hs0 : 0 < s := by linarith
  have hC : 0 ≤ C := by
    by_contra h; push Not at h; nlinarith
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    rw [show (1 - min 0 1 : ℕ) = 1 from rfl, show max 0 1 = 1 from rfl, pow_one, pow_one,
      pow_zero, mul_one]
    calc r * (L * s)⁻¹ ≤ (C * s) * (L * s)⁻¹ := by gcongr
      _ = C / L := by field_simp
      _ ≤ (C + 1) / L := by gcongr; linarith
  · rw [min_eq_right hq, max_eq_left hq, Nat.sub_self, pow_zero, one_mul]
    calc ((L * s)⁻¹) ^ q * s ^ q = (L ^ q)⁻¹ := by
          rw [inv_pow, mul_pow]; field_simp
      _ ≤ L⁻¹ := inv_anti₀ hL0 (le_self_pow₀ hL (by omega))
      _ = 1 / L := by ring
      _ ≤ (C + 1) / L := by gcongr; linarith

variable {L N : ℕ} [NeZero L]

/-- The Taylor expansion to order `0`: vanishing masses gain `L^{-1}`. -/
theorem exists_zero_bound (d n : ℕ) (hd : 1 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (L : ℕ) [NeZero L], 2 ^ (d + 3) + 8 * d < L → ∀ N j : ℕ, j < N →
    ∀ X : Finset (Lam d L N), IsSmall j X → ∀ G ∈ NX (nbhd j X : Set (Lam d L N)),
    (∀ σ : Fin n → ℤˣ, ∑ x : Fin n → Lam d L N, coeff G (fun k => (x k, σ k)) = 0) →
    ∀ ℓ ℓ' : ℝ, 0 < ℓ → 0 < ℓ' → ∀ g : (Fin n → Sf (Lam d L N)) → ℂ,
    (∀ (z : Fin n → Sf (Lam d L N)) (γ : Fin n → Dir d → ℕ), (∀ k, mabs (γ k) ≤ pPhi d) →
      ‖nab γ g z‖ ≤ ℓ' ^ n * (((L : ℝ) ^ (j + 1)) ^ ord γ)⁻¹) →
    ‖pair G (single n g)‖ ≤ (Tj d (L : ℝ) j ℓ G).toReal * (C * ℓ' ^ n * ℓ⁻¹ ^ n / L) := by
  obtain ⟨Cl, hCl0, hCl⟩ := exists_localized_bound d
  set C1 : ℝ := n * d * (2 ^ (d + 2) + 4 * d)
  refine ⟨Cl ^ n * (C1 + 1), by positivity, ?_⟩
  intro L _ hL N j hj X hX G hG hGm ℓ ℓ' hℓ hℓ' g hgb
  set b := base X
  set R : ℝ := (rad d L j : ℝ)
  set s : ℝ := (L : ℝ) ^ j
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hs1 : 1 ≤ s := one_le_pow₀ hL1
  have hs0 : 0 < s := by linarith
  have hh' : (L : ℝ) ^ (j + 1) = L * s := by rw [pow_succ, mul_comm]
  set Φ : (Fin n → ℤˣ) → (Fin n → Zd d) → ℂ := fun σ v => g fun k => (ιZ b (v k), σ k)
  set U : (Fin n → Sf (Zd d)) → ℂ :=
    fun w => Φ (spins w) (fun k => (w k).1) - Φ (spins w) 0
  set P : (Fin n → ℤˣ) → Prop := fun _ => True
  -- the pairing
  have hpair : pair G (single n g) = pair G (single n (fun z => locH P U R (ρS b ∘ z))) := by
    rw [pair_single, pair_single]
    congr 1
    have key : ∀ z : Fin n → Sf (Lam d L N), coeff G z * locH P U R (ρS b ∘ z) =
        coeff G z * g z - coeff G z * Φ (spins z) 0 := by
      intro z
      by_cases hz : ∀ i, (z i).1 ∈ nbhd j X
      · have e1 : Φ (spins (ρS b ∘ z)) (fun k => ((ρS b ∘ z) k).1) = g z := by
          simp only [Φ]; congr 1; funext k; exact ιS_ρS b (z k)
        have e2 : spins (ρS b ∘ z) = spins z := rfl
        simp only [locH, P, if_true, U]
        rw [cutS_ρS_eq_one hX z hz, Complex.ofReal_one, one_mul, e1, e2]; ring
      · push Not at hz
        obtain ⟨i, hi⟩ := hz
        rw [coeff_eq_zero_of_mem_NX hG z i hi]; ring
    simp only [key, sum_sub_distrib]
    have h0 : ∑ z, coeff G z * Φ (spins z) 0 = 0 := by
      rw [sum_split]
      refine sum_eq_zero fun τ _ => ?_
      have e : ∀ x : Fin n → Lam d L N, coeff G (fun k => (x k, τ k)) *
          Φ (spins (fun k => (x k, τ k))) 0 = coeff G (fun k => (x k, τ k)) * Φ τ 0 :=
        fun x => rfl
      simp only [e, ← sum_mul, hGm τ, zero_mul]
    rw [h0, sub_zero]
  -- the derivatives of `Φ`
  have hΦb : ∀ (σ : Fin n → ℤˣ) (v : Fin n → Zd d) (γ : Fin n → Dir d → ℕ),
      (∀ k, mabs (γ k) ≤ pPhi d) →
      ‖nabla (fun b u => b +ᵥ u) γ (Φ σ) v‖ ≤ ℓ' ^ n * (((L : ℝ) ^ (j + 1))⁻¹) ^ ord γ := by
    intro σ v γ hγ
    have e := nabla_comp_pi (fun b u => b +ᵥ u) sh (fun k u => (ιZ b u, σ k))
      (fun k β u => by simp [sh, ιZ_vadd]) γ g v
    simp only [Φ]
    rw [e, inv_pow]
    exact hgb _ γ hγ
  -- the bound on the remainder
  have hUbound : ∀ w : Fin n → Sf (Zd d), P (spins w) →
      (∀ k, supNormZ (w k).1 ≤ 2 * rad d L j + 2 * pPhi d) →
      ∀ δ : Fin n → Dir d → ℕ, (∀ k, mabs (δ k) ≤ pPhi d) →
        ‖nab δ U w‖ * s ^ ord δ ≤ ℓ' ^ n * ((C1 + 1) / L) := by
    intro w _ hr δ hδ
    have eU : nab δ U w = nabla (fun (b : Dir d → ℕ) (u : Zd d) => b +ᵥ u) δ
        (fun v => Φ (spins w) v - Φ (spins w) 0) (fun k => (w k).1) := by
      have e1 : nab δ U w = nab δ (fun w' : Fin n → Sf (Zd d) =>
          Φ (spins w) (fun k => (w' k).1) - Φ (spins w) 0) w :=
        nabla_congr sh δ w fun β => rfl
      rw [e1]
      exact nab_pos δ (fun v => Φ (spins w) v - Φ (spins w) 0) w
    have ht := taylor0_bound (K := ℓ' ^ n) (ε := ((L : ℝ) ^ (j + 1))⁻¹) (P := pPhi d)
      (by positivity) (by positivity) (by simp [pPhi]; omega) (hΦb (spins w))
      (w := fun k => (w k).1) (r := 2 * rad d L j + 2 * pPhi d) hr δ hδ
    rw [hh'] at ht
    have hr' : ((n * d * (2 * rad d L j + 2 * pPhi d) : ℕ) : ℝ) ≤ C1 * s := by
      have := radius_le (d := d) (L := L) j
      push_cast at this ⊢
      simp only [C1, s]
      have hnd : (0 : ℝ) ≤ n * d := by positivity
      nlinarith
    have hsc := zero_scale hL1 hs1 (Nat.cast_nonneg _) hr' (ord δ)
    rw [eU]
    calc ‖nabla (fun (b : Dir d → ℕ) (u : Zd d) => b +ᵥ u) δ
          (fun v => Φ (spins w) v - Φ (spins w) 0) (fun k => (w k).1)‖ * s ^ ord δ
        ≤ ℓ' ^ n * ((n * d * (2 * rad d L j + 2 * pPhi d) : ℕ) : ℝ) ^ (1 - min (ord δ) 1) *
            ((L * s)⁻¹) ^ max (ord δ) 1 * s ^ ord δ := by gcongr
      _ = ℓ' ^ n * (((n * d * (2 * rad d L j + 2 * pPhi d) : ℕ) : ℝ) ^ (1 - min (ord δ) 1) *
            ((L * s)⁻¹) ^ max (ord δ) 1 * s ^ ord δ) := by ring
      _ ≤ ℓ' ^ n * ((C1 + 1) / L) := by gcongr
  have hnorm := hCl n L hL N j hj b P U _ (by positivity) hUbound ℓ hℓ
  rw [hpair]
  refine (abs_pair_le (by positivity) hℓ G (by positivity) hnorm).trans (le_of_eq ?_)
  simp only [Tj]
  ring

/-! ### The contraction bound for one component -/

theorem restr_restr {X : Type*} (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    (g : TestFn X) : Loc.restr P (Loc.restr Q g) = Loc.restr (fun n => P n ∧ Q n) g := by
  funext n z; simp only [Loc.restr]; split_ifs <;> simp_all

/-- `‖G‖_{T_{j+1}(ℓ')} ≤ ‖G‖_{T_j(ℓ)} (C (ℓ'/ℓ)^m / L + (ℓ'/ℓ)^{m'})` if the masses of `G` at length
`m` vanish and the coefficients at lengths `n ≠ m`, `n < m'` vanish. -/
theorem exists_core_bound (d m m' : ℕ) (hd : 1 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (L : ℕ) [NeZero L], 2 ^ (d + 3) + 8 * d < L → ∀ N j : ℕ, j < N →
    ∀ X : Finset (Lam d L N), IsSmall j X → ∀ G ∈ NX (nbhd j X : Set (Lam d L N)),
    (∀ σ : Fin m → ℤˣ, ∑ x : Fin m → Lam d L N, coeff G (fun k => (x k, σ k)) = 0) →
    (∀ (n : ℕ) (z : Fin n → Sf (Lam d L N)), n ≠ m → n < m' → coeff G z = 0) →
    ∀ ℓ ℓ' : ℝ, 0 < ℓ → 0 < ℓ' → ℓ' ≤ ℓ →
      Tj d (L : ℝ) (j + 1) ℓ' G ≤
        ENNReal.ofReal ((Tj d (L : ℝ) j ℓ G).toReal * (C * (ℓ' / ℓ) ^ m / L + (ℓ' / ℓ) ^ m')) := by
  obtain ⟨C, hC0, hC⟩ := exists_zero_bound d m hd
  refine ⟨C, hC0, ?_⟩
  intro L _ hL N j hj X hX G hG hGm hG0 ℓ ℓ' hℓ hℓ' hℓℓ
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hs : (0 : ℝ) < (L : ℝ) ^ j := by positivity
  have hh' : (0 : ℝ) < (L : ℝ) ^ (j + 1) := by positivity
  have hss : (L : ℝ) ^ j ≤ (L : ℝ) ^ (j + 1) := by
    rw [pow_succ]; exact le_mul_of_one_le_right hs.le hL1
  set T := (Tj d (L : ℝ) j ℓ G).toReal
  refine tNorm_le fun g hg => ?_
  rw [pair_restr_add G (fun n => n = m) g,
    pair_restr_add G (fun n => m' ≤ n) (restr (fun n => ¬ n = m) g), restr_restr, restr_restr]
  have hz : pair G (restr (fun n => ¬ m' ≤ n ∧ ¬ n = m) g) = 0 :=
    pair_restr_eq_zero _ _ fun n z hn => hG0 n z hn.2 (by omega)
  rw [hz, add_zero]
  -- length `m`
  have hA : ‖pair G (restr (fun n => n = m) g)‖ ≤ T * (C * (ℓ' / ℓ) ^ m / L) := by
    rw [pair_restr_eq_single]
    have := hC L hL N j hj X hX G hG hGm ℓ ℓ' hℓ hℓ' (g m) fun z γ hγ => by
      have := abs_nab_le hh' hℓ' zero_le_one (by rwa [ENNReal.ofReal_one]) (g := g) z γ hγ
      rwa [one_mul] at this
    refine this.trans (le_of_eq ?_)
    rw [div_pow]; ring
  -- lengths `≥ m'`
  have hB : ‖pair G (restr (fun n => m' ≤ n ∧ ¬ n = m) g)‖ ≤ T * (ℓ' / ℓ) ^ m' := by
    rw [← restr_restr]
    have hg' : phiNorm (Dir d) (pPhi d) ((L : ℝ) ^ (j + 1)) ℓ' (restr (fun n => ¬ n = m) g) ≤ 1 :=
      (phiNorm_restr_le _ g).trans hg
    have hn := phiNorm_restr_ge_le hs hss hℓ hℓ' hℓℓ hg' m'
    exact abs_pair_le hs hℓ G (by positivity) hn
  refine (norm_add_le _ _).trans ((add_le_add hA hB).trans (le_of_eq ?_))
  ring

end

end Obs.LocObs
