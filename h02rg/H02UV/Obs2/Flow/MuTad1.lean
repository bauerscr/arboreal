import Obs2.Flow.TotalMu

/-!
# The `𝒲^{obs}` term of the total `μ` recursion: exact recursion of its tadpole functional

`Obs2.Flow.TotalMu` gives the exact recursion of the total coupling `β = ∑_B m(V(B)_a)`:
`β' = β(1 - ν'∑_x C(a,x)) - ∑_{X ∈ 𝒮_j} m(K(X)_a) - ∑_B m((𝔼θ𝒲(B))_a)`.
The last term is `G_j(C)`, where for a covariance `Γ`

  `G_j(Γ) = ∑_{B ∈ 𝓑_j} m(e^{ℒ_Γ} 𝒲_j(B)_a)`    (`wTad`).

This file proves the **exact one-step recursion of the functional `G`** along the map
(`wTad_step`): for every `Γ`,

  `G_{j+1}(Γ) = T_j(Γ) + (G_j(Γ + C) - G_j(C)) + P_{j+1}(Γ)`,

with `T_j(Γ) = m(e^{ℒ_Γ} F) - m(F)`, `F = F_C(V'(Λ)_a, V'(Λ)_∅)` the one-loop term (`oneTad`), and
`P_{j+1}(Γ) = ∑_{B_+} m(e^{ℒ_Γ}(𝒲_{j+1}(B_+) - ∑_{B ⊆ B_+} 𝒲'(B))_a)` the product part of
`∏(1 + 𝒲') - 1` (`wProd`). The mechanism: `𝒲'(B) = S(B) - Loc_{B_+,B} S(B_+)`, the localised part
has `e^{ℒ}`-invariant mass (`LocMass.exp`) and `Loc_{X,·}` extracts the full mass
(`total_LS`), and `∑_B S(B)_a = F + e^{ℒ_C} 𝒲_j(Λ)_a` with `e^{ℒ_Γ} e^{ℒ_C} = e^{ℒ_{Γ+C}}`.

* `wTad_step`, `wTad_zero_step` (`G_{j+1}(0) = P_{j+1}(0)`);
* `EthO_W_mass`: `∑_B m((𝔼θ𝒲(B))_a) = G_j(C)`;
* **`total_mu_one_tad`**: the total `μ^{(1)}` recursion with the `𝒲` term written as `G_j(C)`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 LocObs

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

/-- `G_k(Γ) = ∑_{B ∈ 𝓑_k} m(e^{ℒ_Γ} 𝒲(B)_a)`. -/
def wTad (k : ℕ) (m : Alg d L N →ₗ[ℂ] ℂ) (W : OFam c d L N)
    (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) : ℂ :=
  ∑ b ∈ blockIdx (L := L) (N := N) k, m (expLC Γ (W b : SA c (Lam d L N)).a)

section Step

variable (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
  (V W : OFam c d L N) (m : Alg d L N →ₗ[ℂ] ℂ) (Γ : Matrix (Lam d L N) (Lam d L N) ℂ)

/-- The product part `P_{j+1}(Γ) = ∑_{B_+} m(e^{ℒ_Γ}(𝒲_{j+1}(B_+) - ∑_{B ⊆ B_+} 𝒲'(B))_a)`. -/
def wProd : ℂ :=
  ∑ c' ∈ blockIdx (L := L) (N := N) (j + 1),
    m (expLC Γ ((Wnext2O P j C V W c' - ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
      WpO P j C V W b : OE c (Lam d L N)) : SA c (Lam d L N)).a)

/-- The one-loop tadpole `T_j(Γ) = m(e^{ℒ_Γ} F) - m(F)`, `F = F_C(V'(Λ)_a, V'(Λ)_∅)`. -/
def oneTad : ℂ :=
  m (expLC Γ (FC C (VprLO j C V : SA c (Lam d L N)).a (VprLO j C V : SA c (Lam d L N)).e)) -
    m (FC C (VprLO j C V : SA c (Lam d L N)).a (VprLO j C V : SA c (Lam d L N)).e)

theorem EthO_a_eq (F : OE c (Lam d L N)) :
    (EthO C F : SA c (Lam d L N)).a = expLC C (F : SA c (Lam d L N)).a := by
  have h0 := (EthO_comp C F).2.1 true
  simp only [cmp_true] at h0
  exact h0

/-- `∑_B S(B)_a = F_C(V'(Λ)_a, V'(Λ)_∅) + ∑_B e^{ℒ_C} 𝒲(B)_a`. -/
theorem sum_SbO_a :
    ∑ b ∈ blockIdx (L := L) (N := N) j, (SbO j C V W b : SA c (Lam d L N)).a =
      FC C (VprLO j C V : SA c (Lam d L N)).a (VprLO j C V : SA c (Lam d L N)).e +
        ∑ b ∈ blockIdx (L := L) (N := N) j, expLC C (W b : SA c (Lam d L N)).a := by
  rw [← sum_a, ← AddSubmonoidClass.coe_finset_sum, SbO_sum, Subalgebra.coe_add,
    Subalgebra.coe_smul, add_a, smul_a, FCO_self_a, smul_smul, AddSubmonoidClass.coe_finset_sum,
    sum_a, show ((1 / 2 : ℂ) * 2) = 1 by norm_num, one_smul]
  rw [sum_congr rfl fun b _ => EthO_a_eq C (W b)]

/-- `∑_B m((𝔼θ𝒲(B))_a) = G_j(C)`. -/
theorem EthO_W_mass :
    ∑ b ∈ blockIdx (L := L) (N := N) j, m (EthO C (W b) : SA c (Lam d L N)).a = wTad j m W C :=
  sum_congr rfl fun b _ => by rw [EthO_a_eq]

theorem sum_m_expLC_SbO :
    ∑ b ∈ blockIdx (L := L) (N := N) j, m (expLC Γ (SbO j C V W b : SA c (Lam d L N)).a) =
      m (expLC Γ (FC C (VprLO j C V : SA c (Lam d L N)).a (VprLO j C V : SA c (Lam d L N)).e)) +
        wTad j m W (Γ + C) := by
  rw [← map_sum, ← map_sum, sum_SbO_a, map_add, map_add, map_sum, map_sum, wTad]
  congr 1
  exact sum_congr rfl fun b _ => by rw [expLC_add]

variable {P m}

/-- **The exact recursion of the tadpole functional**:
`G_{j+1}(Γ) = T_j(Γ) + (G_j(Γ + C) - G_j(C)) + P_{j+1}(Γ)`. -/
theorem wTad_step (hm : LocMass c P.a m) :
    wTad (j + 1) m (Wnext2O P j C V W) Γ =
      oneTad j C V m Γ + (wTad j m W (Γ + C) - wTad j m W C) + wProd P j C V W m Γ := by
  have h1 : ∀ c', m (expLC Γ (Wnext2O P j C V W c' : SA c (Lam d L N)).a) =
      m (expLC Γ ((Wnext2O P j C V W c' - ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
        WpO P j C V W b : OE c (Lam d L N)) : SA c (Lam d L N)).a) +
      ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
        m (expLC Γ (WpO P j C V W b : SA c (Lam d L N)).a) := by
    intro c'
    rw [AddSubgroupClass.coe_sub, sub_a, map_sub, map_sub, AddSubmonoidClass.coe_finset_sum,
      sum_a, map_sum, map_sum]
    ring
  have h2 : ∀ b, m (expLC Γ (WpO P j C V W b : SA c (Lam d L N)).a) =
      m (expLC Γ (SbO j C V W b : SA c (Lam d L N)).a) - m (SbO j C V W b : SA c (Lam d L N)).a +
        (m (LSO P j C V W b : SA c (Lam d L N)).a -
          m (expLC Γ (LSO P j C V W b : SA c (Lam d L N)).a)) +
        (m (SbO j C V W b : SA c (Lam d L N)).a - m (LSO P j C V W b : SA c (Lam d L N)).a) := by
    intro b
    have e : (WpO P j C V W b : SA c (Lam d L N)).a =
        (SbO j C V W b : SA c (Lam d L N)).a - (LSO P j C V W b : SA c (Lam d L N)).a := rfl
    rw [e, map_sub, map_sub]
    ring
  have h3 : ∀ b, m (expLC Γ (LSO P j C V W b : SA c (Lam d L N)).a) =
      m (LSO P j C V W b : SA c (Lam d L N)).a := fun b =>
    hm.exp Γ (Step2.Bp (L := L) (N := N) j b) (blockSet j b) _
  show ∑ c' ∈ blockIdx (L := L) (N := N) (j + 1),
    m (expLC Γ (Wnext2O P j C V W c' : SA c (Lam d L N)).a) = _
  rw [sum_congr rfl fun c' _ => h1 c', sum_add_distrib, sum_blockIdx_succ j]
  simp only [h2, h3, sub_self, add_zero, sum_add_distrib, sum_sub_distrib]
  rw [total_LS P j C V W m hm, sum_m_expLC_SbO]
  have h4 : ∑ b ∈ blockIdx (L := L) (N := N) j, m (SbO j C V W b : SA c (Lam d L N)).a =
      m (FC C (VprLO j C V : SA c (Lam d L N)).a (VprLO j C V : SA c (Lam d L N)).e) +
        wTad j m W C := by
    rw [← map_sum, sum_SbO_a, map_add, map_sum]; rfl
  rw [h4, oneTad, wProd]
  ring

end Step

/-! ### The total recursion of `μ^{(1)}` with the tadpole functional -/

/-- **The total `μ^{(1)}` recursion** (Case (1)), with the `𝒲` term written as the tadpole
functional at the covariance of the step: `β' = β(1 - ν'∑_x C(a,x)) - ∑_{X ∈ 𝒮_j} m₁(K(X)_a) -
G_j(C)`. -/
theorem total_mu_one_tad (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : OFam .one d L N) (K : OAct .one d L N) (hjN : j + 1 < N)
    (β : (Fin d → ℕ) → ℂ) (hV : ∀ b, (V b : SA .one (Lam d L N)).a = β b • psibar P.a)
    (κ : Step2.Coup) (r : ℂ)
    (he : (VprLO j C V : SA .one (Lam d L N)).e = Step2.Vcoup κ univ + r • (1 : Alg d L N)) :
    ∑ b ∈ blockIdx (L := L) (N := N) j, mass1 (-1) (VpO P j C V W K b : SA .one (Lam d L N)).a =
      (∑ b ∈ blockIdx (L := L) (N := N) j, β b) * (1 - κ.nu * ∑ x, C P.a x) -
        ∑ X ∈ smallSets (L := L) (N := N) j, mass1 (-1) (K X : SA .one (Lam d L N)).a -
        wTad j (mass1L (-1)) W C := by
  rw [total_mu_one P j C V W K hjN β hV κ r he, ← EthO_W_mass j C W (mass1L (-1))]
  rfl

end

end Obs2
