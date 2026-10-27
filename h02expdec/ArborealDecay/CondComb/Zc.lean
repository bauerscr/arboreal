module

public import ArborealDecay.CondComb.Conn

/-!
# `Z_c / Z_Γ`, `Z_c / Z_d` and `τ`

* `Zc_eq`, `Zc_div_ZGamma`: the decomposition of `Z_c` (part (ii)).
* `Zc_div_Zd`, `tau_eq`, `tau_le_Zc_div_Zd`, `tau_lt_one`: part (iii).
-/

@[expose] public section

namespace ArborealDecay.CondComb

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical ArborealDecay.Surgery ArborealDecay.Wiring

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The second (last-edge) decomposition. -/
theorem N_eq {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) {a b : V} (hab : a ≠ b)
    (i : {v : V // v ∉ ({a, b} : Finset V)}) :
    ∑ F : SimpleGraph V with F.IsAcyclic ∧ ¬ F.Reachable a i.1 ∧ F.Reachable i.1 b,
        H02.forestWeight β hβ F =
      ∑ j : {v : V // v ∉ ({a, b} : Finset V)}, β j.1 b *
        ∑ F' : SimpleGraph (GamV V a b) with F'.IsAcyclic ∧ EvIJ a b i j F',
          H02.forestWeight (gammaW β a b) (gammaW_symm hβ a b) F' := by
  have hib : b ≠ i.1 := fun h => i.2 (by simp [← h])
  have step := sum_conn_eq hβ hib (fun F => if F.Reachable a i.1 then (0 : ℝ) else 1)
  have hL : ∑ F : SimpleGraph V with F.IsAcyclic ∧ ¬ F.Reachable a i.1 ∧ F.Reachable i.1 b,
        H02.forestWeight β hβ F =
      ∑ F : SimpleGraph V with F.IsAcyclic ∧ F.Reachable b i.1,
        H02.forestWeight β hβ F * (if F.Reachable a i.1 then (0 : ℝ) else 1) := by
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun F _ => ?_
    by_cases h1 : F.IsAcyclic
    · by_cases h2 : F.Reachable a i.1
      · simp [h1, h2]
      · by_cases h3 : F.Reachable i.1 b
        · simp [h1, h2, h3, h3.symm]
        · have : ¬ F.Reachable b i.1 := fun h => h3 h.symm
          simp [h1, h2, h3, this]
    · simp [h1]
  rw [hL, step]
  have hsplit : (Finset.univ.filter fun j : V => j ≠ b) =
      insert a (Finset.univ.filter fun j : V => j ∉ ({a, b} : Finset V)) := by
    ext j
    by_cases h1 : j = a <;> by_cases h2 : j = b <;> simp_all
  rw [hsplit, Finset.sum_insert (by simp)]
  rw [Finset.sum_eq_zero (s := Finset.univ.filter fun F : SimpleGraph V =>
      F.IsAcyclic ∧ ¬ F.Reachable b a ∧ F.Reachable a i.1) (fun F hF => ?_), mul_zero, zero_add]
  swap
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hF
    simp [hF.2.2.mono le_sup_left]
  rw [Finset.sum_subtype (Finset.univ.filter fun j : V => j ∉ ({a, b} : Finset V))
    (p := fun j : V => j ∉ ({a, b} : Finset V)) (by simp)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hβ b j.1]
  congr 1
  convert inner_eq hβ hab i j

/-- Part (ii), unnormalised. -/
theorem Zc_eq {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) {a b : V} (hab : a ≠ b) :
    Zc β hβ a b = β a b * ZGamma β hβ a b +
      ∑ i : {v : V // v ∉ ({a, b} : Finset V)}, ∑ j : {v : V // v ∉ ({a, b} : Finset V)},
        β a i.1 * β j.1 b *
          ∑ F' : SimpleGraph (GamV V a b) with F'.IsAcyclic ∧ EvIJ a b i j F',
            H02.forestWeight (gammaW β a b) (gammaW_symm hβ a b) F' := by
  have step := sum_conn_eq hβ hab (fun _ => (1 : ℝ))
  simp only [mul_one] at step
  unfold Zc
  rw [step]
  have hsplit : (Finset.univ.filter fun j : V => j ≠ a) =
      insert b (Finset.univ.filter fun j : V => j ∉ ({a, b} : Finset V)) := by
    ext j
    by_cases h1 : j = a <;> by_cases h2 : j = b <;> simp_all
  rw [hsplit, Finset.sum_insert (by simp)]
  have hZd : (∑ F : SimpleGraph V with F.IsAcyclic ∧ ¬ F.Reachable a b ∧ F.Reachable b b,
      H02.forestWeight β hβ F) = ZGamma β hβ a b := by
    rw [← Zd_eq_ZGamma hβ hab]
    unfold Zd
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext F
    simp
  rw [hZd]
  congr 1
  rw [Finset.sum_subtype (Finset.univ.filter fun j : V => j ∉ ({a, b} : Finset V))
    (p := fun j : V => j ∉ ({a, b} : Finset V)) (by simp)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [N_eq hβ hab i, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem ZGamma_pos {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j)
    (a b : V) : 0 < ZGamma β hβ a b :=
  H02.Zforest_pos _ (gammaW_nonneg hβ0 a b)

/-- Part (ii): `Z_c / Z_Γ = w_ab + ∑_{i,j ∈ I} w_ai w_jb P_Γ(i ↔ j, i ↮ ρ)`. -/
theorem Zc_div_ZGamma {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j)
    {a b : V} (hab : a ≠ b) :
    Zc β hβ a b / ZGamma β hβ a b = β a b +
      ∑ i : {v : V // v ∉ ({a, b} : Finset V)}, ∑ j : {v : V // v ∉ ({a, b} : Finset V)},
        β a i.1 * β j.1 b *
          H02.arborealProb (gammaW β a b) (gammaW_symm hβ a b) (EvIJ a b i j) := by
  have hZ := (ZGamma_pos hβ hβ0 a b).ne'
  rw [Zc_eq hβ hab, add_div, mul_div_cancel_right₀ _ hZ, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold H02.arborealProb ZGamma
  rw [mul_div_assoc]

theorem Zc_nonneg {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j)
    (a b : V) : 0 ≤ Zc β hβ a b :=
  Finset.sum_nonneg fun F _ => H02.forestWeight_nonneg hβ hβ0 F

theorem Zd_pos {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j)
    {a b : V} (hab : a ≠ b) : 0 < Zd β hβ a b := by
  rw [Zd_eq_ZGamma hβ hab]; exact ZGamma_pos hβ hβ0 a b

theorem Zforest_eq {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) (a b : V) :
    H02.Zforest β hβ = Zc β hβ a b + Zd β hβ a b := by
  unfold H02.Zforest Zc Zd
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter fun F : SimpleGraph V =>
    F.IsAcyclic) (fun F => F.Reachable a b)]
  simp only [Finset.filter_filter]

/-- `τ_G(a, b) = Z_c / Z_G`. -/
theorem tau_eq_Zc_div {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) (a b : V) :
    H02.arborealProb β hβ (fun F => F.Reachable a b) = Zc β hβ a b / H02.Zforest β hβ := by
  simp only [H02.arborealProb, Zc]

/-- `τ_G(a, b) < 1`. -/
theorem tau_lt_one {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j)
    {a b : V} (hab : a ≠ b) : H02.arborealProb β hβ (fun F => F.Reachable a b) < 1 := by
  rw [tau_eq_Zc_div, div_lt_one (H02.Zforest_pos hβ hβ0), Zforest_eq hβ a b]
  linarith [Zd_pos hβ hβ0 hab]

/-- Part (iii): `Z_c / Z_d = τ / (1 - τ)`. -/
theorem Zc_div_Zd {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j)
    {a b : V} (hab : a ≠ b) :
    Zc β hβ a b / Zd β hβ a b =
      H02.arborealProb β hβ (fun F => F.Reachable a b) /
        (1 - H02.arborealProb β hβ (fun F => F.Reachable a b)) := by
  have hZ := (H02.Zforest_pos hβ hβ0).ne'
  have hd := (Zd_pos hβ hβ0 hab).ne'
  rw [tau_eq_Zc_div]
  have h1 : 1 - Zc β hβ a b / H02.Zforest β hβ = Zd β hβ a b / H02.Zforest β hβ := by
    rw [Zforest_eq hβ a b]
    have : Zc β hβ a b + Zd β hβ a b ≠ 0 := by rw [← Zforest_eq hβ a b]; exact hZ
    field_simp
    ring
  rw [h1]
  field_simp

/-- Part (iii): `τ ≤ Z_c / Z_d`. -/
theorem tau_le_Zc_div_Zd {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j)
    {a b : V} (hab : a ≠ b) :
    H02.arborealProb β hβ (fun F => F.Reachable a b) ≤ Zc β hβ a b / Zd β hβ a b := by
  rw [Zc_div_Zd hβ hβ0 hab]
  have h1 := tau_lt_one hβ hβ0 hab
  have h0 : 0 ≤ H02.arborealProb β hβ (fun F => F.Reachable a b) := by
    rw [tau_eq_Zc_div]
    exact div_nonneg (Zc_nonneg hβ hβ0 a b) (H02.Zforest_pos hβ hβ0).le
  rw [le_div_iff₀ (by linarith)]
  nlinarith

end

end ArborealDecay.CondComb
