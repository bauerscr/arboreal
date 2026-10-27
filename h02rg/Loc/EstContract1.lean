import Loc.EstQuad
import Loc.EstVanish
import Loc.EstLocal

/-!
# Ingredients of the contraction bound `prop:Loc` (ii)

* long sequences (`n ≥ 8`): the field scale alone gives `(ℓ'/ℓ)^8`;
* the decomposition of a test function according to the length of the sequences;
* the pairing of `F - Loc_X F` with an antisymmetric test function on sequences of length two.
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD Equiv

section General

variable {X : Type*} [DecidableEq X] [Fintype X] {E : Type*} [Fintype E] [DecidableEq E]
  [AddAction (E → ℕ) X] {p : ℕ}

theorem nab_restr {n : ℕ} (P : ℕ → Prop) [DecidablePred P] (g : TestFn X)
    (α : Fin n → E → ℕ) (z : Fin n → Sf X) :
    nab α (restr P g n) z = if P n then nab α (g n) z else 0 := by
  unfold restr
  split_ifs
  · rfl
  · rw [show (fun _ : Fin n → Sf X => (0 : ℂ)) = 0 from rfl, map_zero]; rfl

/-- On long sequences, only the field scale matters: `‖g 1_{n ≥ 8}‖_{Φ(h, ℓ)} ≤ (ℓ'/ℓ)^8` if
`‖g‖_{Φ(h', ℓ')} ≤ 1`, `h ≤ h'` and `ℓ' ≤ ℓ`. -/
theorem phiNorm_restr_ge_le {h h' ℓ ℓ' : ℝ} (hh : 0 < h) (hhh : h ≤ h') (hℓ : 0 < ℓ)
    (hℓ' : 0 < ℓ') (hθ : ℓ' ≤ ℓ) {g : TestFn X} (hg : phiNorm E p h' ℓ' g ≤ 1) (m : ℕ) :
    phiNorm E p h ℓ (restr (fun n => m ≤ n) g) ≤ ENNReal.ofReal ((ℓ' / ℓ) ^ m) := by
  have hh' : 0 < h' := hh.trans_le hhh
  have hθ1 : ℓ' / ℓ ≤ 1 := (div_le_one hℓ).2 hθ
  refine phiNorm_le fun n z α hα => ?_
  unfold phiTerm
  rw [nab_restr]
  split_ifs with hn
  · have hb := abs_nab_le hh' hℓ' zero_le_one (by rwa [ENNReal.ofReal_one]) (g := g) z α hα
    rw [one_mul] at hb
    calc ℓ⁻¹ ^ n * h ^ ord α * ‖nab α (g n) z‖ ≤ ℓ⁻¹ ^ n * h ^ ord α * (ℓ' ^ n * (h' ^ ord α)⁻¹) := by
          gcongr
      _ = (ℓ' / ℓ) ^ n * (h / h') ^ ord α := by
          rw [div_pow, div_pow, inv_pow]; field_simp
      _ ≤ (ℓ' / ℓ) ^ n * 1 := by
          gcongr
          exact pow_le_one₀ (by positivity) ((div_le_one hh').2 hhh)
      _ ≤ (ℓ' / ℓ) ^ m := by
          rw [mul_one]; exact pow_le_pow_of_le_one (by positivity) hθ1 hn
  · simp only [norm_zero, mul_zero]; positivity

/-- The pairing only sees coefficients: if `F` and `G` agree on sequences with lengths in `P`,
then they have the same pairing with `restr P g`. -/
theorem pair_restr_congr {F G : Grassmann.N X} (P : ℕ → Prop) [DecidablePred P] (g : TestFn X)
    (h : ∀ n (z : Fin n → Sf X), P n → coeff F z = coeff G z) :
    pair F (restr P g) = pair G (restr P g) := by
  unfold pair restr
  refine sum_congr rfl fun n _ => ?_
  split_ifs with hn
  · simp only [h n _ hn]
  · simp

theorem pair_restr_eq_zero {F : Grassmann.N X} (P : ℕ → Prop) [DecidablePred P] (g : TestFn X)
    (h : ∀ n (z : Fin n → Sf X), P n → coeff F z = 0) : pair F (restr P g) = 0 := by
  unfold pair restr
  refine sum_eq_zero fun n _ => ?_
  split_ifs with hn
  · simp [h n _ hn]
  · simp

/-- The decomposition according to the length. -/
theorem restr_decomp (g : TestFn X) :
    g = restr (fun n => n = 2) g + restr (fun n => n = 4) g + restr (fun n => n = 6) g +
      restr (fun n => 8 ≤ n) g + restr (fun n => n ≠ 2 ∧ n ≠ 4 ∧ n ≠ 6 ∧ n < 8) g := by
  funext n z
  simp only [restr, Pi.add_apply]
  by_cases h2 : n = 2
  · subst h2; simp
  by_cases h4 : n = 4
  · subst h4; simp
  by_cases h6 : n = 6
  · subst h6; simp
  by_cases h8 : 8 ≤ n
  · simp [h2, h4, h6, h8]
  · simp [h2, h4, h6, h8, show n < 8 by omega]

theorem pair_decomp (F : Grassmann.N X) (g : TestFn X) :
    pair F g = pair F (restr (fun n => n = 2) g) + pair F (restr (fun n => n = 4) g) +
      pair F (restr (fun n => n = 6) g) + pair F (restr (fun n => 8 ≤ n) g) +
      pair F (restr (fun n => n ≠ 2 ∧ n ≠ 4 ∧ n ≠ 6 ∧ n < 8) g) := by
  conv_lhs => rw [restr_decomp g]
  have h : ∀ g₁ g₂ : TestFn X, pair F (g₁ + g₂) = pair F g₁ + pair F g₂ :=
    fun g₁ g₂ => map_add (pairR F) g₁ g₂
  simp only [h]

end General

/-! ### Sequences of length two -/

variable {d L N : ℕ} [NeZero L]

theorem coeff_swap_two {Λ : Type*} [DecidableEq Λ] (F : Grassmann.N Λ) (a a' : Sf Λ) :
    coeff F ![a', a] = -coeff F ![a, a'] := by
  have := coeff_perm F ![a, a'] (Equiv.swap 0 1)
  have e : (![a, a'] ∘ Equiv.swap (0 : Fin 2) 1) = ![a', a] := by
    funext i; fin_cases i <;> rfl
  rw [e, Perm.sign_swap (by decide)] at this
  simpa using this

/-- For `G` without same-spin coefficients and an antisymmetric `f`,
`⟨G, single 2 f⟩ = ∑_{x,y} G_{(x,+)(y,-)} f((x,+),(y,-))`. -/
theorem pair_single_two_antisymm (G : Alg d L N)
    (hG : ∀ (a a' : Lam d L N) (σ : ℤˣ), coeff G ![(a, σ), (a', σ)] = 0)
    (f : (Fin 2 → Sf (Lam d L N)) → ℂ) (hf : ∀ a a', f ![a', a] = -f ![a, a']) :
    pair G (single 2 f) = ∑ x, ∑ y, coeff G ![(x, 1), (y, -1)] * f ![(x, 1), (y, -1)] := by
  rw [pair_single, sum_fin_two, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, sum_units_int, hG, zero_mul, zero_add, add_zero]
  have hsw : ∀ x y : Lam d L N, coeff G ![(x, -1), (y, 1)] * f ![(x, -1), (y, 1)] =
      coeff G ![(y, 1), (x, -1)] * f ![(y, 1), (x, -1)] := fun x y => by
    rw [coeff_swap_two G (y, 1) (x, -1), hf (y, 1) (x, -1)]; ring
  simp only [hsw, sum_add_distrib]
  rw [sum_comm (f := fun x y => coeff G ![(y, 1), (x, -1)] * f ![(y, 1), (x, -1)])]
  norm_num
  ring

end

end Loc
