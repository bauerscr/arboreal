module

public import ArborealDecay.ExpDecay.OneStep
public import ArborealDecay.ExpDecay.TorusStep

/-!
# Exponential decay (§9): finite `ℤ²` subgraphs and the torus

Assembly of `thm:main` from the Simon–Lieb inequality (`hSL`, for every finite weighted
graph) and the superpolynomial bound (`hSP`, `prop:superpoly`).

* `expDecay_finite_of_inputs`: `eq:main-finite` for finite nearest-neighbour subgraphs of `ℤ²`.
* `expDecay_torus_of_inputs`: the same on every torus `(ℤ/L)²`.
-/

@[expose] public section

namespace ArborealDecay.ExpDecay

open Finset ArborealDecay.Lattice

theorem p_le_one {B : ℝ} (hB : 0 ≤ B) : B / (1 + B) ≤ 1 := by
  rw [div_le_one (by linarith)]; linarith

theorem eta_nonneg {A a B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (R : ℕ) :
    0 ≤ (8 * (R : ℝ) + 4) * (B / (1 + B)) * qFun A a R := by
  have := qFun_nonneg hA (a := a) R
  positivity

/-- `eq:exp-final` for finite nearest-neighbour subgraphs of `ℤ²`
(`eq:main-finite`, with `c_β = log 2 / (R(β) + 1)`). -/
theorem expDecay_finite_of_inputs
    (hSL : ∀ (V : Type) [Fintype V] [DecidableEq V] (β : V → V → ℝ)
      (hβ : ∀ i j, β i j = β j i) (_ : ∀ i j, 0 ≤ β i j) (D : Finset V) (x z : V),
      x ∈ D → z ∉ D →
      connProb β hβ x z ≤ ∑ u ∈ D, ∑ v ∈ Dᶜ,
        (if u ≠ v ∧ β u v ≠ 0 then
          adjProb β hβ u v * connProb β hβ x u * connProb β hβ v z else 0))
    (hSP : ∀ B : ℝ, 0 ≤ B → ∃ A a : ℝ, 0 < A ∧ 0 < a ∧
      ∀ (Λ : Finset (ℤ × ℤ)) (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i)
        (_ : ∀ i j, 0 ≤ β i j) (_ : ∀ i j, β i j ≠ 0 → IsNN (i : ℤ × ℤ) j)
        (_ : ∀ i j, β i j ≤ B) (x z : Λ),
        connProb β hβ x z ≤ min 1 (A * Real.exp (-a * Real.log (2 + (supDist x z : ℝ)) ^ 2))) :
    ∀ B : ℝ, 0 ≤ B → ∃ c : ℝ, 0 < c ∧
      ∀ (Λ : Finset (ℤ × ℤ)) (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i)
        (_ : ∀ i j, 0 ≤ β i j) (_ : ∀ i j, β i j ≠ 0 → IsNN (i : ℤ × ℤ) j)
        (_ : ∀ i j, β i j ≤ B) (x y : Λ),
        H02.arborealProb β hβ (fun F => F.Reachable x y)
          ≤ 2 * Real.exp (-c * (supDist (x : ℤ × ℤ) y : ℝ)) := by
  intro B hB
  obtain ⟨A, a, hA, ha, hSP'⟩ := hSP B hB
  obtain ⟨R, hR⟩ := exists_eta_le_half hA.le ha (p_le_one hB)
  refine ⟨Real.log 2 / (R + 1), by have := Real.log_pos (one_lt_two (α := ℝ)); positivity, ?_⟩
  intro Λ β hβ hβ0 hNN hBw x y
  have key := decay_of_contraction (V := Λ) (fun u v => (supDist (u : ℤ × ℤ) v).toNat)
    (fun x y z => by
      have := supDist_triangle (x : ℤ × ℤ) y z
      have := supDist_nonneg (x : ℤ × ℤ) y
      have := supDist_nonneg (x : ℤ × ℤ) z
      have := supDist_nonneg (y : ℤ × ℤ) z
      omega)
    (fun u v => connProb β hβ u v) R _ (eta_nonneg hA.le hB R) hR
    (fun u v => connProb_le_one hβ hβ0 u v)
    (fun y z hyz M hM => by
      have hyz' : (R : ℤ) < supDist (y : ℤ × ℤ) z := by omega
      exact oneStep_finite_of_inputs hSL hA.le hSP' R Λ β hβ hβ0 hNN hBw y z hyz' M
        (fun v hv => hM v (by omega))) x y
  have hd : (((supDist (x : ℤ × ℤ) y).toNat : ℕ) : ℝ) = (supDist (x : ℤ × ℤ) y : ℝ) := by
    have := Int.toNat_of_nonneg (supDist_nonneg (x : ℤ × ℤ) y)
    exact_mod_cast this
  rw [hd] at key
  exact key

/-- `eq:exp-final` on every torus `(ℤ/L)²`, including `L ≤ 2R + 2`. -/
theorem expDecay_torus_of_inputs
    (hSL : ∀ (V : Type) [Fintype V] [DecidableEq V] (β : V → V → ℝ)
      (hβ : ∀ i j, β i j = β j i) (_ : ∀ i j, 0 ≤ β i j) (D : Finset V) (x z : V),
      x ∈ D → z ∉ D →
      connProb β hβ x z ≤ ∑ u ∈ D, ∑ v ∈ Dᶜ,
        (if u ≠ v ∧ β u v ≠ 0 then
          adjProb β hβ u v * connProb β hβ x u * connProb β hβ v z else 0))
    (hSP : ∀ B : ℝ, 0 ≤ B → ∃ A a : ℝ, 0 < A ∧ 0 < a ∧
      ∀ (L : ℕ) [NeZero L] (β : ZMod L × ZMod L → ZMod L × ZMod L → ℝ)
        (hβ : ∀ i j, β i j = β j i) (_ : ∀ i j, 0 ≤ β i j)
        (_ : ∀ i j, β i j ≠ 0 → IsTorusNN L i j) (_ : ∀ i j, β i j ≤ B)
        (x z : ZMod L × ZMod L),
        connProb β hβ x z ≤
          min 1 (A * Real.exp (-a * Real.log (2 + (torusSupDist L x z : ℝ)) ^ 2))) :
    ∀ B : ℝ, 0 ≤ B → ∃ c : ℝ, 0 < c ∧
      ∀ (L : ℕ) [NeZero L] (β : ZMod L × ZMod L → ZMod L × ZMod L → ℝ)
        (hβ : ∀ i j, β i j = β j i) (_ : ∀ i j, 0 ≤ β i j)
        (_ : ∀ i j, β i j ≠ 0 → IsTorusNN L i j) (_ : ∀ i j, β i j ≤ B)
        (x y : ZMod L × ZMod L),
        H02.arborealProb β hβ (fun F => F.Reachable x y)
          ≤ 2 * Real.exp (-c * (torusSupDist L x y : ℝ)) := by
  intro B hB
  obtain ⟨A, a, hA, ha, hSP'⟩ := hSP B hB
  obtain ⟨R, hR⟩ := exists_eta_le_half hA.le ha (p_le_one hB)
  have hlog := Real.log_pos (one_lt_two (α := ℝ))
  refine ⟨Real.log 2 / (R + 1), by positivity, ?_⟩
  intro L _ β hβ hβ0 hNN hBw x y
  by_cases hL : 2 * R + 2 < L
  · exact decay_of_contraction (V := ZMod L × ZMod L) (torusSupDist L)
      (fun x y z => torusSupDist_triangle x y z)
      (fun u v => connProb β hβ u v) R _ (eta_nonneg hA.le hB R) hR
      (fun u v => connProb_le_one hβ hβ0 u v)
      (fun y z hyz M hM =>
        oneStep_torus_of_inputs hSL hA.le hSP' R L hL β hβ hβ0 hNN hBw y z hyz M hM) x y
  · have hd : torusSupDist L x y ≤ R + 1 := by
      have := torusSupDist_le_half x y
      omega
    have hd' : ((torusSupDist L x y : ℕ) : ℝ) ≤ (R : ℝ) + 1 := by exact_mod_cast hd
    have h1 : 1 ≤ 2 * Real.exp (-(Real.log 2 / (R + 1)) * (torusSupDist L x y : ℝ)) := by
      have hR1 : (0 : ℝ) < R + 1 := by positivity
      have : -Real.log 2 ≤ -(Real.log 2 / (R + 1)) * (torusSupDist L x y : ℝ) := by
        have : Real.log 2 / (R + 1) * (torusSupDist L x y : ℝ) ≤ Real.log 2 := by
          calc Real.log 2 / (R + 1) * (torusSupDist L x y : ℝ)
              ≤ Real.log 2 / (R + 1) * (R + 1) :=
                mul_le_mul_of_nonneg_left hd' (by positivity)
            _ = Real.log 2 := by field_simp
        linarith
      calc (1 : ℝ) = 2 * Real.exp (-Real.log 2) := by
            rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
        _ ≤ _ := by gcongr
    exact (connProb_le_one hβ hβ0 x y).trans h1

end ArborealDecay.ExpDecay
