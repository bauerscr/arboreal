import Loc.EstMu
import Loc.EstLeibniz

/-!
# Localised test functions

Given a function `U` of sequences in `ℤ^d` whose derivatives are bounded (at scale `L^j`) on the
box of radius `2 · 2^{d+1} L^j + 2 p_Φ`, the test function `z ↦ χ(ρ_b z) U(ρ_b z)` on the torus,
where `χ = ∏_k cutP 0 R` is a smooth cut-off at scale `R = 2^{d+1} L^j`, has `Φ_j(ℓ)` norm
`≤ C^n B ℓ^{-n}` (Leibniz rule and the transfer lemma).
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD

variable {d : ℕ}

theorem shZ_add' (b b' : Dir d → ℕ) (a : Sf (Zd d)) : sh (b + b') a = sh b (sh b' a) := by
  simp [sh, add_vadd]

/-- The cut-off `w ↦ ∏_k χ(w_k)`. -/
def cutS (R : ℝ) {n : ℕ} (w : Fin n → Sf (Zd d)) : ℝ := ∏ k, cutP 0 R (w k).1

/-- The localised function `[P(spins w)] χ(w) U(w)`. -/
def locH {n : ℕ} (P : (Fin n → ℤˣ) → Prop) [DecidablePred P] (U : (Fin n → Sf (Zd d)) → ℂ)
    (R : ℝ) (w : Fin n → Sf (Zd d)) : ℂ :=
  if P (spins w) then (cutS R w : ℂ) * U w else 0

theorem D1_sh_fst (a : Dir d → ℕ) (f : Zd d → ℝ) (x : Sf (Zd d)) :
    D1 sh a (fun y => f y.1) x = D1 (fun b v => b +ᵥ v) a f x.1 := by
  rw [D1_eq_sum, D1_eq_sum]; rfl

theorem nab_cutS (R : ℝ) {n : ℕ} (γ : Fin n → Dir d → ℕ) (w : Fin n → Sf (Zd d)) :
    nab γ (cutS R) w = ∏ k, D1 (fun b v => b +ᵥ v) (γ k) (cutP 0 R) (w k).1 := by
  have : cutS (d := d) R (n := n) = fun w => ∏ k, (fun y : Sf (Zd d) => cutP 0 R y.1) (w k) := rfl
  rw [this]
  exact (nabla_prod (sh (X := Zd d)) γ (fun _ y => cutP 0 R y.1) w).trans (by simp only [D1_sh_fst])

theorem ord_le_of_mabs_le {n : ℕ} {α : Fin n → Dir d → ℕ} {P : ℕ} (h : ∀ k, mabs (α k) ≤ P) :
    ord α ≤ n * P := by
  calc ord α = ∑ k, mabs (α k) := rfl
    _ ≤ ∑ _k : Fin n, P := sum_le_sum fun k _ => h k
    _ = n * P := by simp

theorem mabs_mono {a c : Dir d → ℕ} (h : a ≤ c) : mabs a ≤ mabs c :=
  sum_le_sum fun e _ => h e

theorem ord_add_sub {n : ℕ} {α γ : Fin n → Dir d → ℕ} (h : γ ≤ α) :
    ord γ + ord (α - γ) = ord α := by
  rw [← ord_add]
  congr 1
  funext k e
  exact Nat.add_sub_cancel' (h k e)

theorem exists_localized_bound (d : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (n L : ℕ) [NeZero L],
    2 ^ (d + 3) + 8 * d < L → ∀ N j : ℕ, j < N → ∀ (b : Lam d L N)
    (P : (Fin n → ℤˣ) → Prop) [DecidablePred P] (U : (Fin n → Sf (Zd d)) → ℂ) (B : ℝ), 0 ≤ B →
    (∀ w : Fin n → Sf (Zd d), P (spins w) →
      (∀ k, supNormZ (w k).1 ≤ 2 * rad d L j + 2 * pPhi d) →
      ∀ δ : Fin n → Dir d → ℕ, (∀ k, mabs (δ k) ≤ pPhi d) →
        ‖nab δ U w‖ * ((L : ℝ) ^ j) ^ ord δ ≤ B) →
    ∀ ℓ : ℝ, 0 < ℓ →
      phiNorm (Dir d) (pPhi d) ((L : ℝ) ^ j) ℓ
          (single n (fun z => locH P U (rad d L j : ℝ) (ρS b ∘ z))) ≤
        ENNReal.ofReal (C ^ n * B * ℓ⁻¹ ^ n) := by
  obtain ⟨Cc, hCc0, hCc⟩ := exists_D1_cutP_bound d (pPhi d) 0
  refine ⟨4 ^ d * Cc, by positivity, ?_⟩
  intro n L _ hL N j hj b P _ U B hB hU ℓ hℓ
  set s : ℝ := (L : ℝ) ^ j with hs
  set R : ℝ := (rad d L j : ℝ) with hRdef
  have h2p : 0 < 2 ^ (d + 3) := by positivity
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
  have hs1 : 1 ≤ s := one_le_pow₀ hL1
  have hs0 : 0 < s := by linarith
  have hRs : R = 2 ^ (d + 1) * s := by simp [R, rad, s]
  have hR1 : 1 ≤ R := by rw [hRdef]; exact Nat.one_le_cast.2 (one_le_rad j)
  have hR0 : 0 < R := by linarith
  have hsR : s ≤ R := by
    rw [hRs]; exact le_mul_of_one_le_left (by linarith) (one_le_pow₀ (by norm_num))
  refine phiNorm_single_le (by positivity) fun z α hα => ?_
  rw [nab_comp_ρS b (locH P U R) (S := 2 * rad d L j) (P := pPhi d) (size_cond hL hj)
    (fun w ⟨k, hk⟩ => by
      have hk' : 2 * R ≤ (supNormZ (w k).1 : ℝ) := by
        have : ((2 * rad d L j : ℕ) : ℝ) < supNormZ (w k).1 := by exact_mod_cast hk
        push_cast at this; linarith
      simp only [locH]
      split_ifs
      · rw [cutS, prod_eq_zero (mem_univ k) (cutP_eq_zero 0 hR0 hk'), Complex.ofReal_zero, zero_mul]
      · rfl) α hα z]
  set w₀ := ρS b ∘ z
  have hlocH : locH P U R = fun w => if P (spins w) then (cutS R w : ℂ) * U w else 0 := rfl
  rw [hlocH, nab_ite_spins]
  split_ifs with hP
  · -- the Leibniz bound
    have hM : ∀ γ : Fin n → Dir d → ℕ, γ ≤ α →
        ‖nab γ (fun w => (cutS R w : ℂ)) w₀‖ * ‖nab (α - γ) U (fun i => sh (γ i) (w₀ i))‖ ≤
          Cc ^ n * B / s ^ ord α := by
      intro γ hγ
      rw [nabla_ofReal, Complex.norm_real, Real.norm_eq_abs, nab_cutS]
      by_cases hfar : ∃ k, 2 * R + mabs (γ k) ≤ (supNormZ (w₀ k).1 : ℝ)
      · obtain ⟨k, hk⟩ := hfar
        rw [prod_eq_zero (mem_univ k) (D1_cutP_eq_zero 0 hR0 (γ k) hk), abs_zero, zero_mul]
        positivity
      · push Not at hfar
        have hγα : ∀ k, mabs (γ k) ≤ mabs (α k) := fun k => mabs_mono (hγ k)
        set w' : Fin n → Sf (Zd d) := fun i => sh (γ i) (w₀ i)
        have hw' : ∀ k, supNormZ (w' k).1 ≤ 2 * rad d L j + 2 * pPhi d := by
          intro k
          have h1 : supNormZ (w' k).1 ≤ mabs (γ k) + supNormZ (w₀ k).1 := by
            have e1 := supNormZ_add_le (dirHomZ (γ k)) (w₀ k).1
            have e2 := supNormZ_dirHomZ_le (γ k)
            show supNormZ ((γ k) +ᵥ (w₀ k).1) ≤ _
            rw [vaddZ_def]; omega
          have h2 : (supNormZ (w₀ k).1 : ℝ) < 2 * R + mabs (γ k) := hfar k
          have h3 : mabs (γ k) ≤ pPhi d := (hγα k).trans (hα k)
          have h4 : supNormZ (w₀ k).1 < 2 * rad d L j + mabs (γ k) := by
            have : (supNormZ (w₀ k).1 : ℝ) < ((2 * rad d L j + mabs (γ k) : ℕ) : ℝ) := by
              push_cast; linarith
            exact_mod_cast this
          omega
        have hU' := hU w' (by rw [spins_sh]; exact hP) hw' (α - γ) (fun k =>
          (mabs_mono (fun e => by simp only [Pi.sub_apply]; exact Nat.sub_le _ _)).trans (hα k))
        have hC : |∏ k, D1 (fun b v => b +ᵥ v) (γ k) (cutP 0 R) (w₀ k).1| ≤
            Cc ^ n / s ^ ord γ := by
          rw [abs_prod]
          calc ∏ k, |D1 (fun b v => b +ᵥ v) (γ k) (cutP 0 R) (w₀ k).1|
              ≤ ∏ k, (Cc / s ^ mabs (γ k)) := by
                refine prod_le_prod (fun k _ => abs_nonneg _) fun k _ => ?_
                have := hCc 0 (fun _ => le_rfl) R hR1 (γ k) ((hγα k).trans (hα k)) (w₀ k).1
                simp only [Pi.zero_apply, sum_const_zero, pow_zero, mul_one] at this
                refine this.trans ?_
                gcongr
            _ = Cc ^ n / s ^ ord γ := by
                rw [prod_div_distrib, prod_const, card_univ, Fintype.card_fin, prod_pow_eq_pow_sum]
                rfl
        have hsum := ord_add_sub hγ
        have hU'' : ‖nab (α - γ) U w'‖ ≤ B / s ^ ord (α - γ) := by
          rw [le_div_iff₀ (by positivity)]; exact hU'
        calc |∏ k, D1 (fun b v => b +ᵥ v) (γ k) (cutP 0 R) (w₀ k).1| * ‖nab (α - γ) U w'‖
            ≤ (Cc ^ n / s ^ ord γ) * (B / s ^ ord (α - γ)) := by
              gcongr
          _ = Cc ^ n * B / s ^ ord α := by
              rw [← hsum, pow_add]; field_simp
    have hL := abs_nabla_mul_le sh (fun _ => sh_zero _) shZ_add' α (fun w => (cutS R w : ℂ)) U w₀ hM
    have hord : ord α ≤ n * pPhi d := ord_le_of_mabs_le hα
    have h2 : (2 : ℝ) ^ ord α ≤ (4 ^ d) ^ n := by
      calc (2 : ℝ) ^ ord α ≤ 2 ^ (n * pPhi d) := pow_le_pow_right₀ (by norm_num) hord
        _ = (4 ^ d) ^ n := by
            rw [pPhi, ← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf
    calc ℓ⁻¹ ^ n * s ^ ord α * ‖nab α (fun w => (cutS R w : ℂ) * U w) w₀‖
        ≤ ℓ⁻¹ ^ n * s ^ ord α * (2 ^ ord α * (Cc ^ n * B / s ^ ord α)) := by gcongr
      _ = 2 ^ ord α * Cc ^ n * B * ℓ⁻¹ ^ n := by field_simp
      _ ≤ (4 ^ d) ^ n * Cc ^ n * B * ℓ⁻¹ ^ n := by gcongr
      _ = (4 ^ d * Cc) ^ n * B * ℓ⁻¹ ^ n := by rw [mul_pow]
  · simp only [norm_zero, mul_zero]; positivity

end

end Loc
