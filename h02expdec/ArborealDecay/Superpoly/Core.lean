module

public import ArborealDecay.Superpoly.PieceBound
public import ArborealDecay.Superpoly.Arith

/-!
# The abstract superpolynomial bound

`superpoly_abstract_of_inputs`: for a finite vertex type with an injective position map
`φ : V → ℤ²` such that the weights are nearest-neighbour inside the relevant ball, the two-point
function is bounded by `min 1 (A exp(-a log(2 + D)²))`, `D = ‖φ b‖`.
-/

@[expose] public section

namespace ArborealDecay.Superpoly

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical ArborealDecay.Surgery ArborealDecay.ExpDecay ArborealDecay.Lattice

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Product of annulus bounds (from `(W)` and `(AN)`). -/
theorem core_of_inputs
    (hW : ∀ (V : Type) [Fintype V] [DecidableEq V] (β : V → V → ℝ)
      (hβ : ∀ i j, β i j = β j i), (∀ i j, 0 ≤ β i j) →
      ∀ (S : Finset V) (a b : V), a ∉ S → b ∉ S →
        (∀ p : (suppGraph β hβ).Walk a b, ∃ v ∈ p.support, v ∈ S) →
        connProb β hβ a b ≤
          connProb (mapW β (collapse S)) (mapW_symm hβ _) (collapse S a) (collapse S b))
    {B C κ : ℝ}
    (hAN : ∀ (r : ℕ), 2 ≤ r → ∀ (Λ : Finset (ℤ × ℤ)),
      (∀ z ∈ Λ, (r : ℤ) ≤ supNorm z ∧ supNorm z ≤ 2 * (r : ℤ)) →
      ∀ (w : Λ → Λ → ℝ) (hw : ∀ i j, w i j = w j i), (∀ i j, 0 ≤ w i j) →
        (∀ i j, w i j ≠ 0 → IsNN (i : ℤ × ℤ) j) → (∀ i j, w i j ≤ B) →
        connProb (mapW w (annulusCollapse r Λ)) (mapW_symm hw _) (Sum.inl false) (Sum.inl true)
          ≤ C * (r : ℝ) ^ (-κ))
    {φ : V → ℤ × ℤ} (hφ : Function.Injective φ) {r₀ : ℕ} (hr : 2 ≤ r₀) (m : ℕ)
    {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j)
    (hβB : ∀ i j, β i j ≤ B) (hdiag : ∀ u, β u u = 0)
    (hLip : ∀ u v, β u v ≠ 0 → |supNorm (φ u) - supNorm (φ v)| ≤ 1)
    (hNN : ∀ u v, β u v ≠ 0 → supNorm (φ u) ≤ lev r₀ m → supNorm (φ v) ≤ lev r₀ m →
      IsNN (φ u) (φ v)) {a b : V}
    (ha : supNorm (φ a) < lev r₀ 0) (hb : lev r₀ m < supNorm (φ b)) :
    connProb β hβ a b ≤ ∏ k ∈ range m, (C * ((2 ^ k * r₀ : ℕ) : ℝ) ^ (-κ)) := by
  have : Nonempty V := ⟨a⟩
  refine (chain_bound_of_inputs hW φ (by omega) m hβ hβ0 hdiag hLip ha hb).trans ?_
  exact Finset.prod_le_prod₀ (fun k _ => connProb_nonneg (wiredW_symm φ r₀ m hβ)
    (wiredW_nonneg φ r₀ m hβ0) _ _) (fun k hk =>
    piece_bound_of_inputs hAN hφ hr (Finset.mem_range.1 hk) hβ hβ0 hβB hdiag hLip hNN)

/-- **Abstract superpolynomial bound** (from `(W)` and `(AN)`). -/
theorem superpoly_abstract_of_inputs
    (hW : ∀ (V : Type) [Fintype V] [DecidableEq V] (β : V → V → ℝ)
      (hβ : ∀ i j, β i j = β j i), (∀ i j, 0 ≤ β i j) →
      ∀ (S : Finset V) (a b : V), a ∉ S → b ∉ S →
        (∀ p : (suppGraph β hβ).Walk a b, ∃ v ∈ p.support, v ∈ S) →
        connProb β hβ a b ≤
          connProb (mapW β (collapse S)) (mapW_symm hβ _) (collapse S a) (collapse S b))
    (hAN : ∀ B : ℝ, 0 ≤ B → ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧
      ∀ (r : ℕ), 2 ≤ r → ∀ (Λ : Finset (ℤ × ℤ)),
      (∀ z ∈ Λ, (r : ℤ) ≤ supNorm z ∧ supNorm z ≤ 2 * (r : ℤ)) →
      ∀ (w : Λ → Λ → ℝ) (hw : ∀ i j, w i j = w j i), (∀ i j, 0 ≤ w i j) →
        (∀ i j, w i j ≠ 0 → IsNN (i : ℤ × ℤ) j) → (∀ i j, w i j ≤ B) →
        connProb (mapW w (annulusCollapse r Λ)) (mapW_symm hw _) (Sum.inl false) (Sum.inl true)
          ≤ C * (r : ℝ) ^ (-κ)) :
    ∀ B : ℝ, 0 ≤ B → ∃ A a : ℝ, 0 < A ∧ 0 < a ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (φ : V → ℤ × ℤ), Function.Injective φ →
        ∀ (β : V → V → ℝ) (hβ : ∀ i j, β i j = β j i), (∀ i j, 0 ≤ β i j) →
        (∀ i j, β i j ≤ B) → (∀ u, β u u = 0) →
        (∀ u v, β u v ≠ 0 → |supNorm (φ u) - supNorm (φ v)| ≤ 1) → ∀ (x z : V),
        supNorm (φ x) = 0 →
        (∀ R : ℤ, 2 * R ≤ supNorm (φ z) → ∀ u v, β u v ≠ 0 → supNorm (φ u) ≤ R →
          supNorm (φ v) ≤ R → IsNN (φ u) (φ v)) →
        connProb β hβ x z ≤
          min 1 (A * Real.exp (-a * Real.log (2 + (supNorm (φ z) : ℝ)) ^ 2)) := by
  intro B hB
  obtain ⟨C₀, κ, hC₀, hκ, hANB⟩ := hAN B hB
  set C : ℝ := max C₀ 1 with hCdef
  have hC1 : 1 ≤ C := le_max_right _ _
  have hAN' : ∀ (r : ℕ), 2 ≤ r → ∀ (Λ : Finset (ℤ × ℤ)),
      (∀ z ∈ Λ, (r : ℤ) ≤ supNorm z ∧ supNorm z ≤ 2 * (r : ℤ)) →
      ∀ (w : Λ → Λ → ℝ) (hw : ∀ i j, w i j = w j i), (∀ i j, 0 ≤ w i j) →
        (∀ i j, w i j ≠ 0 → IsNN (i : ℤ × ℤ) j) → (∀ i j, w i j ≤ B) →
        connProb (mapW w (annulusCollapse r Λ)) (mapW_symm hw _) (Sum.inl false) (Sum.inl true)
          ≤ C * (r : ℝ) ^ (-κ) := by
    intro r hr Λ hΛ w hw h0 hnn hB'
    refine (hANB r hr Λ hΛ w hw h0 hnn hB').trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  obtain ⟨A₁, a, hA₁, ha, hbound⟩ := prod_annulus_le hC1 hκ
  refine ⟨max A₁ (Real.exp (a * Real.log 5 ^ 2)), a, lt_max_of_lt_left hA₁, ha, ?_⟩
  intro V _ _ φ hφ β hβ hβ0 hβB hdiag hLip x z hx hNN
  refine le_min (connProb_le_one hβ hβ0 x z) ?_
  have hD0 : 0 ≤ supNorm (φ z) := supNorm_nonneg _
  by_cases hD : supNorm (φ z) < 4
  · -- small distance
    have hDr : (supNorm (φ z) : ℝ) ≤ 3 := by exact_mod_cast (by omega : supNorm (φ z) ≤ 3)
    have hDr0 : (0 : ℝ) ≤ supNorm (φ z) := by exact_mod_cast hD0
    have hlog : Real.log (2 + (supNorm (φ z) : ℝ)) ^ 2 ≤ Real.log 5 ^ 2 := by
      apply pow_le_pow_left₀ (Real.log_nonneg (by linarith))
      exact Real.log_le_log (by linarith) (by linarith)
    have h1 : 1 ≤ Real.exp (a * Real.log 5 ^ 2) * Real.exp (-a * Real.log (2 + (supNorm (φ z) : ℝ)) ^ 2) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      nlinarith
    calc connProb β hβ x z ≤ 1 := connProb_le_one hβ hβ0 x z
      _ ≤ _ := h1
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  · push Not at hD
    obtain ⟨Dn, hDn⟩ : ∃ Dn : ℕ, (Dn : ℤ) = supNorm (φ z) := ⟨(supNorm (φ z)).toNat, by omega⟩
    have hDn4 : 4 ≤ Dn := by omega
    set m := Nat.log 2 Dn - 2 with hm
    have hlog4 : 2 ≤ Nat.log 2 Dn := by
      rw [Nat.le_log_iff_pow_le (by norm_num) (by omega)]; omega
    have hm1 : 2 ^ (m + 2) ≤ Dn := by
      have : m + 2 = Nat.log 2 Dn := by omega
      rw [this]; exact Nat.pow_log_le_self 2 (by omega)
    have hm2 : Dn < 2 ^ (m + 3) := by
      have : m + 3 = Nat.log 2 Dn + 1 := by omega
      rw [this]; exact Nat.lt_pow_succ_log_self (by norm_num) _
    have hlevm : lev 2 m = 2 ^ (m + 1) := by
      unfold lev; push_cast; ring
    have hpow : (2 : ℤ) ^ (m + 2) ≤ supNorm (φ z) := by
      rw [← hDn]; exact_mod_cast hm1
    have hmain := core_of_inputs hW hAN' hφ (r₀ := 2) le_rfl m hβ hβ0 hβB hdiag hLip
      (fun u v huv h1 h2 => hNN (lev 2 m) (by rw [hlevm]; calc (2 : ℤ) * 2 ^ (m + 1) = 2 ^ (m + 2) := by ring
        _ ≤ _ := hpow) u v huv h1 h2)
      (a := x) (b := z) (by rw [hx]; unfold lev; norm_num)
      (by rw [hlevm]; have : (2 : ℤ) ^ (m + 2) = 2 * 2 ^ (m + 1) := by ring
          have : (0 : ℤ) < 2 ^ (m + 1) := by positivity
          omega)
    have hb := hbound m Dn hm1 hm2
    have hcast : (Dn : ℝ) = (supNorm (φ z) : ℝ) := by exact_mod_cast hDn
    rw [hcast] at hb
    calc connProb β hβ x z ≤ _ := hmain
      _ ≤ _ := hb
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

end

end ArborealDecay.Superpoly
