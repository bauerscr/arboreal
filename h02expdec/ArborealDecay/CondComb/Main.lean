module

public import ArborealDecay.CondComb.Edge
public import ArborealDecay.Wiring

/-!
# Combinatorial half of `prop:conductance-identity`

Let `Γ = G/(a=b)`, i.e. the vertex set `Option {v // v ∉ {a, b}}` (with `none = ρ`) and weights
`gammaW β a b = mapW β (collapse {a, b})` (parallel edges summed).  Write `Z_c`, `Z_d` for the total
weight of forests of `G` in which `a, b` are connected / not connected.

* `Zd_eq_ZGamma` (`eq:Zd-ZGamma`): `Z_d = Z_Γ`.
* `Zc_eq` / `Zc_div_ZGamma` : `Z_c = w_ab Z_Γ + ∑_{i,j ∈ I} w_ai w_jb Z_Γ[i ↔ j, i ↮ ρ]`, i.e.
  `Z_c / Z_Γ = w_ab + ∑_{i,j ∈ I} w_ai w_jb P_Γ(i ↔ j, i ↮ ρ)`.
* `Zc_div_Zd`, `tau_eq`, `tau_le_Zc_div_Zd`, `tau_lt_one`.
-/

@[expose] public section

namespace ArborealDecay.CondComb

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical ArborealDecay.Surgery ArborealDecay.Wiring

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The vertex set of `Γ = G/(a=b)`: `none` is `ρ`. -/
abbrev GamV (V : Type*) [DecidableEq V] (a b : V) := Option {v : V // v ∉ ({a, b} : Finset V)}

/-- The weights of `Γ = G/(a=b)`. -/
def gammaW (β : V → V → ℝ) (a b : V) : GamV V a b → GamV V a b → ℝ :=
  mapW β (collapse ({a, b} : Finset V))

theorem gammaW_symm {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) (a b : V) (x y : GamV V a b) :
    gammaW β a b x y = gammaW β a b y x := mapW_symm hβ _ x y

theorem gammaW_nonneg {β : V → V → ℝ} (hβ0 : ∀ i j, 0 ≤ β i j) (a b : V) (x y : GamV V a b) :
    0 ≤ gammaW β a b x y := mapW_nonneg hβ0 _ x y

/-- Total weight of forests of `G` in which `a` and `b` are connected. -/
def Zc (β : V → V → ℝ) (hβ : ∀ i j, β i j = β j i) (a b : V) : ℝ :=
  ∑ F : SimpleGraph V with F.IsAcyclic ∧ F.Reachable a b, H02.forestWeight β hβ F

/-- Total weight of forests of `G` in which `a` and `b` are not connected. -/
def Zd (β : V → V → ℝ) (hβ : ∀ i j, β i j = β j i) (a b : V) : ℝ :=
  ∑ F : SimpleGraph V with F.IsAcyclic ∧ ¬ F.Reachable a b, H02.forestWeight β hβ F

/-- The partition function of `Γ = G/(a=b)`. -/
def ZGamma (β : V → V → ℝ) (hβ : ∀ i j, β i j = β j i) (a b : V) : ℝ :=
  H02.Zforest (gammaW β a b) (gammaW_symm hβ a b)

/-- The event `i ↔ j, i ↮ ρ` on forests of `Γ`, for `i, j ∈ I = V ∖ {a, b}`. -/
def EvIJ (a b : V) (i j : {v : V // v ∉ ({a, b} : Finset V)}) (F' : SimpleGraph (GamV V a b)) :
    Prop :=
  F'.Reachable (some i) (some j) ∧ ¬ F'.Reachable (some i) none

theorem sepS_pair_iff {a b : V} (hab : a ≠ b) (F : SimpleGraph V) :
    SepS ({a, b} : Finset V) F ↔ ¬ F.Reachable a b := by
  constructor
  · intro h hr
    exact hab (h a (by simp) b (by simp) hr)
  · intro h s hs s' hs' hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs hs'
    rcases hs with rfl | rfl <;> rcases hs' with rfl | rfl
    · rfl
    · exact absurd hr h
    · exact absurd hr.symm h
    · rfl

/-- `eq:Zd-ZGamma`: `Z_d = Z_Γ`. -/
theorem Zd_eq_ZGamma {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) {a b : V} (hab : a ≠ b) :
    Zd β hβ a b = ZGamma β hβ a b := by
  have h := sum_sep_eq (S := ({a, b} : Finset V)) (s₀ := a) (by simp) hβ (fun _ => True)
  unfold Zd ZGamma H02.Zforest gammaW
  simp only [and_true] at h
  rw [← h]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext F
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, sepS_pair_iff hab]

end

end ArborealDecay.CondComb
