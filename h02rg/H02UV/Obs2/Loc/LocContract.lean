import Obs2.Loc.LocContractLarge
import Obs.LocObsContract

/-!
# Contraction of the observable localisation in `d = 2` (new route, `h02uv-outline.tex`,
Section `sec:obs-flow`)

The `d ≥ 3` bounds `Obs.LocObs.exists_odd_contract` / `exists_even_contract` gain
`θ^m L^{-1}` with `θ = L^{-(d-2)/2}`. Their proof (Taylor expansion to order `0`,
`exists_core_bound`) controls the lengths `n ≥ m + 2` only by `(2θ)^{m+2}`, which is `2^{m+2}`
in `d = 2`. Here the long lengths are controlled by the Pauli principle instead
(`exists_large_bound_ge` with `m = 3`, as for the bulk Lemma `lem:loc2`):

* `exists_core2_bound`: if `G ∈ 𝒩(X^□)` has vanishing masses at length `m ∈ {1, 2}`, vanishing
  coefficients at the other lengths `< 3`, and agrees with `F ∈ 𝒩(X^□)` at lengths `≥ 3`, then
  `‖G‖_{T_{j+1}(ℓ')} ≤ C L^{-1} (‖G‖_{T_j(ℓ)} + ‖F‖_{T_j(ℓ)})` for `ℓ' ≤ 2ℓ`;
* `exists_odd_contract2`: for `F` of charge `-s`,
  `‖F - loc_X F‖_{T_{j+1}(ℓ')} ≤ C L^{-1} ‖F‖_{T_j(ℓ)}` (`loc = locOdd s P`; Case (1) `F_a`
  with `s = -1`, `P = {a}`, and `F_b` with `s = 1`, `P = {b}`);
* `exists_even_contract2`: the same for `U(1)`-invariant `F` and `loc = locEven P` (Case (2)
  `F_a`, `F_b` with `P = {a}`, `{b}`; and `F_{ab}` with `P = {a, b}` in both cases).

These hold for every `d ≥ 1` and every pair of field scales `ℓ' ≤ 2ℓ` (no relation to `ℓ_j`).
The images (`ψ̄_a`; `1, ψ̄_aψ_a`) are all `U(1)`-compatible derivative-free monomials at one
point, so in `d = 2` (where they are all marginal) nothing more needs to be in the image of
`loc^a`; `L^{-1}` is optimal (the length-one part, `ψ̄_x - ψ̄_a`, gains exactly one derivative).
Boundedness `‖loc_{X,Y} F‖_{T_j(ℓ)} ≤ C ‖F‖_{T_j(ℓ)}` is `Obs.LocObs.exists_odd_bound` /
`exists_even_bound` (all `d`).

`exists_locA_contract2`, `exists_locB_contract2` restate the bounds for the components
`loc^a`, `loc^b` of `Obs2.LocO2`.
For the `ab` component, `Obs2.locAB2` (sharp region `R_a`) is *not* bounded uniformly in `j`.
The contraction holds for `locEven {a, b}` (`exists_locAB_contract2`), and for the barycentric
operator `Obs2.locABt` (`Obs2.Loc.LocABt`), whose image contains all two-point monomials.
-/

namespace Obs2

noncomputable section

open Finset Grassmann FRD Loc Obs.LocObs

variable {d L N : ℕ} [NeZero L]

theorem restr_congr' {X : Type*} {P Q : ℕ → Prop} [DecidablePred P] [DecidablePred Q]
    (h : ∀ n, P n ↔ Q n) (g : TestFn X) : Loc.restr P g = Loc.restr Q g := by
  funext n z
  simp only [Loc.restr]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd ((h n).1 h1) h2
  · exact absurd ((h n).2 h2) h1
  · rfl

/-- **The core bound in `d = 2`.** Taylor expansion to order `0` at the length `m ∈ {1,2}` and the
Pauli bound at lengths `≥ 3`. -/
theorem exists_core2_bound (d m : ℕ) (hd : 1 ≤ d) (hm1 : 1 ≤ m) (hm2 : m ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], 2 ^ (d + 3) + 8 * d < L → L₀ ≤ L →
    ∀ N j : ℕ, j < N → ∀ X : Finset (Lam d L N), IsSmall j X →
    ∀ F ∈ NX (nbhd j X : Set (Lam d L N)), ∀ G ∈ NX (nbhd j X : Set (Lam d L N)),
    (∀ σ : Fin m → ℤˣ, ∑ x : Fin m → Lam d L N, coeff G (fun k => (x k, σ k)) = 0) →
    (∀ (n : ℕ) (z : Fin n → Sf (Lam d L N)), n ≠ m → n < 3 → coeff G z = 0) →
    (∀ (n : ℕ) (z : Fin n → Sf (Lam d L N)), 3 ≤ n → coeff G z = coeff F z) →
    ∀ ℓ ℓ' : ℝ, 0 < ℓ → 0 < ℓ' → ℓ' ≤ 2 * ℓ →
      Tj d (L : ℝ) (j + 1) ℓ' G ≤ ENNReal.ofReal (C / L *
        ((Tj d (L : ℝ) j ℓ G).toReal + (Tj d (L : ℝ) j ℓ F).toReal)) := by
  obtain ⟨Cz, hCz0, hCz⟩ := exists_zero_bound d m hd
  obtain ⟨C5, hC50, L₀, hC5⟩ := exists_large_bound_ge d 3 hd (by norm_num)
  refine ⟨4 * Cz + C5, by positivity, L₀, ?_⟩
  intro L _ hL hL₀ N j hj X hX F hF G hG hGm hG0 hGF ℓ ℓ' hℓ hℓ' hℓℓ
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hL0 : (0 : ℝ) < L := by linarith
  have hh' : (0 : ℝ) < (L : ℝ) ^ (j + 1) := by positivity
  set TG := (Tj d (L : ℝ) j ℓ G).toReal
  set TF := (Tj d (L : ℝ) j ℓ F).toReal
  have hTG : 0 ≤ TG := ENNReal.toReal_nonneg
  have hTF : 0 ≤ TF := ENNReal.toReal_nonneg
  refine tNorm_le fun g hg => ?_
  rw [pair_restr_add G (fun n => n = m) g,
    pair_restr_add G (fun n => 3 ≤ n) (Loc.restr (fun n => ¬ n = m) g), restr_restr, restr_restr]
  have hz : pair G (Loc.restr (fun n => ¬ 3 ≤ n ∧ ¬ n = m) g) = 0 :=
    pair_restr_eq_zero _ _ fun n z hn => hG0 n z hn.2 (by omega)
  rw [hz, add_zero]
  -- length `m`: Taylor expansion to order `0`
  have hA : ‖pair G (Loc.restr (fun n => n = m) g)‖ ≤ TG * (4 * Cz / L) := by
    rw [pair_restr_eq_single]
    have := hCz L hL N j hj X hX G hG hGm ℓ ℓ' hℓ hℓ' (g m) fun z γ hγ => by
      have := abs_nab_le hh' hℓ' zero_le_one (by rwa [ENNReal.ofReal_one]) (g := g) z γ hγ
      rwa [one_mul] at this
    refine this.trans (mul_le_mul_of_nonneg_left ?_ hTG)
    have hr0 : 0 ≤ ℓ' * ℓ⁻¹ := by positivity
    have hr : ℓ' * ℓ⁻¹ ≤ 2 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hℓ]; linarith
    have hpow : (ℓ' * ℓ⁻¹) ^ m ≤ 4 :=
      calc (ℓ' * ℓ⁻¹) ^ m ≤ 2 ^ m := pow_le_pow_left₀ hr0 hr m
        _ ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num) hm2
        _ = 4 := by norm_num
    calc Cz * ℓ' ^ m * ℓ⁻¹ ^ m / L = Cz * (ℓ' * ℓ⁻¹) ^ m / L := by rw [mul_pow, mul_assoc]
      _ ≤ Cz * 4 / L := by gcongr
      _ = 4 * Cz / L := by ring
  -- lengths `≥ 3`: the Pauli bound
  have hB : ‖pair G (Loc.restr (fun n => 3 ≤ n ∧ ¬ n = m) g)‖ ≤ TF * (C5 / L) := by
    rw [restr_congr' (Q := fun n => 3 ≤ n) (fun n => by omega) g,
      pair_restr_congr (G := F) _ _ fun n z hn => hGF n z hn]
    have := hC5 L hL hL₀ N j hj X hX F hF ℓ ℓ' hℓ hℓ' hℓℓ g hg
    simpa using this
  refine (norm_add_le _ _).trans ((add_le_add hA hB).trans ?_)
  have e1 : 4 * Cz / (L : ℝ) ≤ (4 * Cz + C5) / L :=
    div_le_div_of_nonneg_right (le_add_of_nonneg_right hC50) hL0.le
  have e2 : C5 / (L : ℝ) ≤ (4 * Cz + C5) / L :=
    div_le_div_of_nonneg_right (le_add_of_nonneg_left (by positivity)) hL0.le
  have h1 : TG * (4 * Cz / L) ≤ (4 * Cz + C5) / L * TG := by
    rw [mul_comm]; exact mul_le_mul_of_nonneg_right e1 hTG
  have h2 : TF * (C5 / L) ≤ (4 * Cz + C5) / L * TF := by
    rw [mul_comm]; exact mul_le_mul_of_nonneg_right e2 hTF
  calc TG * (4 * Cz / L) + TF * (C5 / L) ≤ (4 * Cz + C5) / L * TG + (4 * Cz + C5) / L * TF :=
        add_le_add h1 h2
    _ = _ := by ring

/-- From the core bound and `‖G‖_{T_j} ≤ (1 + C_b) ‖F‖_{T_j}` to the contraction. -/
theorem contract_of_core {j : ℕ} {ℓ ℓ' C Cb : ℝ} (hs : (0 : ℝ) < (L : ℝ) ^ j) (hℓ : 0 < ℓ)
    (hC : 0 ≤ C) (hCb : 0 ≤ Cb) {F G : Alg d L N}
    (hc : Tj d (L : ℝ) (j + 1) ℓ' G ≤ ENNReal.ofReal (C / L *
        ((Tj d (L : ℝ) j ℓ G).toReal + (Tj d (L : ℝ) j ℓ F).toReal)))
    (hTG : (Tj d (L : ℝ) j ℓ G).toReal ≤ (1 + Cb) * (Tj d (L : ℝ) j ℓ F).toReal) :
    Tj d (L : ℝ) (j + 1) ℓ' G ≤ ENNReal.ofReal (C * (2 + Cb) / L) * Tj d (L : ℝ) j ℓ F := by
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  set T := (Tj d (L : ℝ) j ℓ F).toReal
  have hT : 0 ≤ T := ENNReal.toReal_nonneg
  have hTF : Tj d (L : ℝ) j ℓ F = ENNReal.ofReal T :=
    (ENNReal.ofReal_toReal (tNorm_ne_top hs hℓ F)).symm
  refine hc.trans ?_
  rw [hTF, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hCL : 0 ≤ C / L := by positivity
  calc C / L * ((Tj d (L : ℝ) j ℓ G).toReal + T) ≤ C / L * ((1 + Cb) * T + T) := by gcongr
    _ = C * (2 + Cb) / L * T := by ring

/-- **Contraction of `loc` for odd components, `d = 2`** (and every `d ≥ 1`): for `F` of charge
`-s` and `ℓ' ≤ 2ℓ`, `‖F - loc_X F‖_{T_{j+1}(ℓ')} ≤ C L^{-1} ‖F‖_{T_j(ℓ)}`. -/
theorem exists_odd_contract2 (d : ℕ) (hd : 1 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧ ∃ L₀ : ℕ,
    ∀ (L : ℕ) [NeZero L], 2 ^ (d + 3) + 8 * d < L → L₀ ≤ L → ∀ N j : ℕ, j < N →
    ∀ ℓ ℓ' : ℝ, 0 < ℓ → 0 < ℓ' → ℓ' ≤ 2 * ℓ →
    ∀ X : Finset (Lam d L N), IsSmall j X → ∀ (s : ℤˣ) (P : Finset (Lam d L N)),
    (X ∩ P).Nonempty → ∀ F ∈ NX (nbhd j X : Set (Lam d L N)), HasCharge (-(s : ℤ)) F →
      Tj d (L : ℝ) (j + 1) ℓ' (F - locOdd s P X X F) ≤
        ENNReal.ofReal (C / L) * Tj d (L : ℝ) j ℓ F := by
  obtain ⟨Cb, hCb0, hCb⟩ := exists_odd_bound d
  obtain ⟨Cc, hCc0, L₀, hCc⟩ := exists_core2_bound d 1 hd le_rfl (by norm_num)
  refine ⟨Cc * (2 + Cb), by positivity, L₀, ?_⟩
  intro L _ hL hL₀ N j hj ℓ ℓ' hℓ hℓ' hℓℓ X hX s P hP F hF hFc
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hs : (0 : ℝ) < (L : ℝ) ^ j := by positivity
  set G := F - locOdd s P X X F
  have hGmem : G ∈ NX (nbhd j X : Set (Lam d L N)) :=
    sub_mem hF (NX_mono (inter_subset_nbhd hX.1 P) (locOdd_mem s P X X F))
  have hTG := tNorm_sub_loc_le hs hℓ hCb0 (hCb L hL N j hj X X hX subset_rfl F hF s P ℓ hℓ)
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
  have hG0 : ∀ (n : ℕ) (z : Fin n → Sf (Lam d L N)), n ≠ 1 → n < 3 → coeff G z = 0 := by
    intro n z hn1 hn3
    rw [coeff_sub', coeff_locOdd_of_ne s P X X F z hn1, sub_zero]
    refine hFc n z fun h => ?_
    have h2 := charge_add z
    rcases units_val_eq s with h1 | h1 <;> rw [h1] at h <;> omega
  have hGF : ∀ (n : ℕ) (z : Fin n → Sf (Lam d L N)), 3 ≤ n → coeff G z = coeff F z := by
    intro n z hn
    rw [coeff_sub', coeff_locOdd_of_ne s P X X F z (by omega), sub_zero]
  have hc := hCc L hL hL₀ N j hj X hX F hF G hGmem hGm hG0 hGF ℓ ℓ' hℓ hℓ' hℓℓ
  exact contract_of_core hs hℓ hCc0 hCb0 hc hTG

/-- **Contraction of `loc` for even, `U(1)`-invariant components, `d = 2`** (and every `d ≥ 1`):
`‖F - loc_X F‖_{T_{j+1}(ℓ')} ≤ C L^{-1} ‖F‖_{T_j(ℓ)}` for `ℓ' ≤ 2ℓ`. -/
theorem exists_even_contract2 (d : ℕ) (hd : 1 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧ ∃ L₀ : ℕ,
    ∀ (L : ℕ) [NeZero L], 2 ^ (d + 3) + 8 * d < L → L₀ ≤ L → ∀ N j : ℕ, j < N →
    ∀ ℓ ℓ' : ℝ, 0 < ℓ → 0 < ℓ' → ℓ' ≤ 2 * ℓ →
    ∀ X : Finset (Lam d L N), IsSmall j X → ∀ P : Finset (Lam d L N),
    (X ∩ P).Nonempty → ∀ F ∈ NX (nbhd j X : Set (Lam d L N)), HasCharge 0 F →
      Tj d (L : ℝ) (j + 1) ℓ' (F - locEven P X X F) ≤
        ENNReal.ofReal (C / L) * Tj d (L : ℝ) j ℓ F := by
  obtain ⟨Cb, hCb0, hCb⟩ := exists_even_bound d
  obtain ⟨Cc, hCc0, L₀, hCc⟩ := exists_core2_bound d 2 hd (by norm_num) le_rfl
  refine ⟨Cc * (2 + Cb), by positivity, L₀, ?_⟩
  intro L _ hL hL₀ N j hj ℓ ℓ' hℓ hℓ' hℓℓ X hX P hP F hF hFc
  have hsym : IsSym F := (hasCharge_zero_iff F).1 hFc
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hs : (0 : ℝ) < (L : ℝ) ^ j := by positivity
  set G := F - locEven P X X F
  have hGmem : G ∈ NX (nbhd j X : Set (Lam d L N)) :=
    sub_mem hF (NX_mono (inter_subset_nbhd hX.1 P) (locEven_mem P X X F))
  have hTG := tNorm_sub_loc_le hs hℓ hCb0 (hCb L hL N j hj X X hX subset_rfl F hF P ℓ hℓ)
  have hsame : ∀ (x y : Lam d L N) (σ : ℤˣ), coeff G ![(x, σ), (y, σ)] = 0 := fun x y σ => by
    rw [coeff_sub', coeff_same_spin_eq_zero hsym, coeff_locEven_same, sub_zero]
  have hmass : mass2 G = 0 := by rw [mass2_sub, mass2_locEven hP, sub_self]
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
  have hG0 : ∀ (n : ℕ) (z : Fin n → Sf (Lam d L N)), n ≠ 2 → n < 3 → coeff G z = 0 := by
    intro n z hn2 hn3
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      rw [coeff_elim0, map_sub, eps_locEven hP, sub_self]
    · rw [coeff_sub', coeff_locEven_of_ne P X X F z (by omega) hn2, sub_zero]
      exact coeff_eq_zero_of_odd hsym (Nat.odd_iff.2 (by omega)) z
  have hGF : ∀ (n : ℕ) (z : Fin n → Sf (Lam d L N)), 3 ≤ n → coeff G z = coeff F z := by
    intro n z hn
    rw [coeff_sub', coeff_locEven_of_ne P X X F z (by omega) (by omega), sub_zero]
  have hc := hCc L hL hL₀ N j hj X hX F hF G hGmem hGm hG0 hGF ℓ ℓ' hℓ hℓ' hℓℓ
  exact contract_of_core hs hℓ hCc0 hCb0 hc hTG

/-! ### The components `loc^a`, `loc^b`, `loc^{ab}` -/

omit [NeZero L] in
theorem inter_singleton_nonempty {X : Finset (Lam d L N)} {a : Lam d L N} (ha : a ∈ X) :
    (X ∩ {a}).Nonempty := ⟨a, mem_inter.2 ⟨ha, mem_singleton_self a⟩⟩

/-- **`loc^a` contracts in `d = 2`**: for `a ∈ X`, `X` small, `F ∈ 𝒩(X^□)` of the charge of the
`a`-component (`1` in Case (1), `0` in Case (2)) and `ℓ' ≤ 2ℓ`,
`‖F - loc^a_X F‖_{T_{j+1}(ℓ')} ≤ C L^{-1} ‖F‖_{T_j(ℓ)}`. -/
theorem exists_locA_contract2 (d : ℕ) (hd : 1 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧ ∃ L₀ : ℕ,
    ∀ (L : ℕ) [NeZero L], 2 ^ (d + 3) + 8 * d < L → L₀ ≤ L → ∀ N j : ℕ, j < N →
    ∀ ℓ ℓ' : ℝ, 0 < ℓ → 0 < ℓ' → ℓ' ≤ 2 * ℓ →
    ∀ X : Finset (Lam d L N), IsSmall j X → ∀ (c : ObsCase) (a : Lam d L N), a ∈ X →
    ∀ F ∈ NX (nbhd j X : Set (Lam d L N)), HasCharge (chargeA c) F →
      Tj d (L : ℝ) (j + 1) ℓ' (F - locA c a X X F) ≤
        ENNReal.ofReal (C / L) * Tj d (L : ℝ) j ℓ F := by
  obtain ⟨C1, hC1, L1, h1⟩ := exists_odd_contract2 d hd
  obtain ⟨C2, hC2, L2, h2⟩ := exists_even_contract2 d hd
  refine ⟨max C1 C2, le_max_of_le_left hC1, max L1 L2, ?_⟩
  intro L _ hL hL₀ N j hj ℓ ℓ' hℓ hℓ' hℓℓ X hX c a ha F hF hFc
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  cases c
  · refine (h1 L hL (le_of_max_le_left hL₀) N j hj ℓ ℓ' hℓ hℓ' hℓℓ X hX (-1) {a}
      (inter_singleton_nonempty ha) F hF (by simpa [chargeA] using hFc)).trans ?_
    gcongr; exact le_max_left _ _
  · refine (h2 L hL (le_of_max_le_right hL₀) N j hj ℓ ℓ' hℓ hℓ' hℓℓ X hX {a}
      (inter_singleton_nonempty ha) F hF (by simpa [chargeA] using hFc)).trans ?_
    gcongr; exact le_max_right _ _

/-- **`loc^b` contracts in `d = 2`** (charge `-1` in Case (1), `0` in Case (2)). -/
theorem exists_locB_contract2 (d : ℕ) (hd : 1 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧ ∃ L₀ : ℕ,
    ∀ (L : ℕ) [NeZero L], 2 ^ (d + 3) + 8 * d < L → L₀ ≤ L → ∀ N j : ℕ, j < N →
    ∀ ℓ ℓ' : ℝ, 0 < ℓ → 0 < ℓ' → ℓ' ≤ 2 * ℓ →
    ∀ X : Finset (Lam d L N), IsSmall j X → ∀ (c : ObsCase) (b : Lam d L N), b ∈ X →
    ∀ F ∈ NX (nbhd j X : Set (Lam d L N)), HasCharge (chargeB c) F →
      Tj d (L : ℝ) (j + 1) ℓ' (F - locB c b X X F) ≤
        ENNReal.ofReal (C / L) * Tj d (L : ℝ) j ℓ F := by
  obtain ⟨C1, hC1, L1, h1⟩ := exists_odd_contract2 d hd
  obtain ⟨C2, hC2, L2, h2⟩ := exists_even_contract2 d hd
  refine ⟨max C1 C2, le_max_of_le_left hC1, max L1 L2, ?_⟩
  intro L _ hL hL₀ N j hj ℓ ℓ' hℓ hℓ' hℓℓ X hX c b hb F hF hFc
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  cases c
  · refine (h1 L hL (le_of_max_le_left hL₀) N j hj ℓ ℓ' hℓ hℓ' hℓℓ X hX 1 {b}
      (inter_singleton_nonempty hb) F hF (by simpa [chargeB] using hFc)).trans ?_
    gcongr; exact le_max_left _ _
  · refine (h2 L hL (le_of_max_le_right hL₀) N j hj ℓ ℓ' hℓ hℓ' hℓℓ X hX {b}
      (inter_singleton_nonempty hb) F hF (by simpa [chargeB] using hFc)).trans ?_
    gcongr; exact le_max_right _ _

end

end Obs2
