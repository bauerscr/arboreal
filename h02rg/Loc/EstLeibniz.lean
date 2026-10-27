import Loc.EstDefs

/-!
# A Leibniz bound for discrete derivatives

`‖∇^α (c u)(z)‖ ≤ 2^{|α|} M` if `‖∇^γ c(z)‖ ‖∇^{α - γ} u(z + γ)‖ ≤ M` for all `γ ≤ α`.
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD

theorem abs_nabla_mul_le_aux {n : ℕ} {E Y : Type*} [Fintype E] [DecidableEq E]
    (s : (E → ℕ) → Y → Y) (hs0 : ∀ y, s 0 y = y) (hsa : ∀ b b' y, s (b + b') y = s b (s b' y))
    (k : ℕ) : ∀ (α : Fin n → E → ℕ), ord α = k → ∀ (c u : (Fin n → Y) → ℂ) (z : Fin n → Y) (M : ℝ),
    (∀ γ : Fin n → E → ℕ, γ ≤ α →
      ‖nabla s γ c z‖ * ‖nabla s (α - γ) u (fun i => s (γ i) (z i))‖ ≤ M) →
    ‖nabla s α (fun w => c w * u w) z‖ ≤ 2 ^ ord α * M := by
  induction k with
  | zero =>
    intro α hα c u z M hM
    have h0 := ord_eq_zero hα
    subst h0
    have := hM 0 le_rfl
    rw [tsub_zero, nabla_zero s hs0, nabla_zero s hs0] at this
    simp only [Pi.zero_apply, hs0] at this
    rw [nabla_zero s hs0, ord_zero, pow_zero, one_mul, norm_mul]
    exact this
  | succ k ih =>
    intro α hα c u z M hM
    have hne : α ≠ 0 := by rintro rfl; simp [ord_zero] at hα
    obtain ⟨α', i, e, rfl⟩ := exists_eq_add_single hne
    set D : Fin n → E → ℕ := Pi.single i (Pi.single e 1) with hD
    have hord : ord α' = k := by rw [ord_add, ord_single] at hα; omega
    have hT : ∀ w : Fin n → Y, Function.update w i (s (Pi.single e 1) (w i))
        = fun j => s (D j) (w j) := by
      intro w; funext j
      by_cases hj : j = i
      · subst hj; simp [D]
      · simp [D, hj, hs0]
    have hsplit : ediff s i e (fun w => c w * u w)
        = (fun w => ediff s i e c w * u (fun j => s (D j) (w j)))
          + (fun w => c w * ediff s i e u w) := by
      funext w
      simp only [ediff, Pi.add_apply, hT]
      ring
    rw [nabla_succ s hsa, hsplit, map_add, Pi.add_apply, ord_add, ord_single, pow_succ]
    have hDle : ∀ γ : Fin n → E → ℕ, γ ≤ α' → γ + D ≤ α' + D := fun γ h j e' =>
      Nat.add_le_add_right (h j e') _
    have h1 := ih α' hord (ediff s i e c) (fun w => u (fun j => s (D j) (w j))) z M (by
      intro γ hγ
      have := hM (γ + D) (hDle γ hγ)
      rw [nabla_succ s hsa] at this
      rw [nabla_comp_shift s hsa]
      have e1 : α' + D - (γ + D) = α' - γ := by
        funext j e'; simp only [Pi.sub_apply, Pi.add_apply]; omega
      have e2 : (fun j => s ((γ + D) j) (z j)) = fun j => s (D j) (s (γ j) (z j)) := by
        funext j; rw [← hsa, Pi.add_apply, add_comm]
      rw [e1, e2] at this
      exact this)
    have h2 := ih α' hord c (ediff s i e u) z M (by
      intro γ hγ
      have := hM γ (le_trans hγ (le_add_single α' i e))
      have heq : α' + D - γ = (α' - γ) + D := by
        funext j e'
        have h' : γ j e' ≤ α' j e' := hγ j e'
        simp only [Pi.sub_apply, Pi.add_apply]
        omega
      rw [heq, nabla_succ s hsa] at this
      exact this)
    calc _ ≤ ‖nabla s α' (fun w => ediff s i e c w * u (fun j => s (D j) (w j))) z‖
          + ‖nabla s α' (fun w => c w * ediff s i e u w) z‖ := norm_add_le _ _
      _ ≤ 2 ^ ord α' * M + 2 ^ ord α' * M := add_le_add h1 h2
      _ = _ := by ring

theorem abs_nabla_mul_le {n : ℕ} {E Y : Type*} [Fintype E] [DecidableEq E]
    (s : (E → ℕ) → Y → Y) (hs0 : ∀ y, s 0 y = y) (hsa : ∀ b b' y, s (b + b') y = s b (s b' y))
    (α : Fin n → E → ℕ) (c u : (Fin n → Y) → ℂ) (z : Fin n → Y) {M : ℝ}
    (hM : ∀ γ : Fin n → E → ℕ, γ ≤ α →
      ‖nabla s γ c z‖ * ‖nabla s (α - γ) u (fun i => s (γ i) (z i))‖ ≤ M) :
    ‖nabla s α (fun w => c w * u w) z‖ ≤ 2 ^ ord α * M :=
  abs_nabla_mul_le_aux s hs0 hsa _ α rfl c u z M hM

end

end Loc
