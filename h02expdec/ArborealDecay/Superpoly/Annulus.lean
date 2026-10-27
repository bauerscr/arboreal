module

public import ArborealDecay.Superpoly.Wired
public import ArborealDecay.Superpoly.Window

/-!
# Comparison of the wired window with the wired annulus graph

For the level window `lev k ≤ height ≤ lev (k+1)` the graph `mapW β' ...` restricted to the
window is the push-forward, along the injection `j : Bool ⊕ Λ_k → T`, of the wired annulus graph
`mapW w (annulusCollapse r Λ_k)`.
-/

@[expose] public section

namespace ArborealDecay.Superpoly

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical ArborealDecay.Surgery ArborealDecay.ExpDecay ArborealDecay.Lattice

/-- The collapse of the annulus `r ≤ ‖z‖ ≤ 2r`: the inner boundary goes to `inl false`, the outer
boundary to `inl true`. -/
def annulusCollapse (r : ℕ) (Λ : Finset (ℤ × ℤ)) (z : Λ) : Bool ⊕ Λ :=
  if supNorm (z : ℤ × ℤ) = (r : ℤ) then Sum.inl false
  else if supNorm (z : ℤ × ℤ) = 2 * (r : ℤ) then Sum.inl true else Sum.inr z

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The lattice points of the window `lev k ≤ ‖z‖ ≤ lev (k+1)` coming from `V`. -/
def lamF (φ : V → ℤ × ℤ) (r₀ k : ℕ) : Finset (ℤ × ℤ) :=
  ((univ : Finset V).filter fun v =>
    lev r₀ k ≤ supNorm (φ v) ∧ supNorm (φ v) ≤ lev r₀ (k + 1)).image φ

theorem mem_lamF {φ : V → ℤ × ℤ} {r₀ k : ℕ} {z : ℤ × ℤ} :
    z ∈ lamF φ r₀ k ↔ ∃ v, (lev r₀ k ≤ supNorm (φ v) ∧ supNorm (φ v) ≤ lev r₀ (k + 1)) ∧
      φ v = z := by
  simp [lamF]

theorem lamF_bounds {φ : V → ℤ × ℤ} {r₀ k : ℕ} {z : ℤ × ℤ} (hz : z ∈ lamF φ r₀ k) :
    lev r₀ k ≤ supNorm z ∧ supNorm z ≤ lev r₀ (k + 1) := by
  obtain ⟨v, hv, rfl⟩ := mem_lamF.1 hz
  exact hv

section

variable [Nonempty V]

/-- A left inverse of `φ`. -/
def psiF (φ : V → ℤ × ℤ) : ℤ × ℤ → V := Function.invFun φ

theorem phi_psiF {φ : V → ℤ × ℤ} {r₀ k : ℕ} {z : ℤ × ℤ} (hz : z ∈ lamF φ r₀ k) :
    φ (psiF φ z) = z := by
  obtain ⟨v, _, hv⟩ := mem_lamF.1 hz
  exact Function.invFun_eq ⟨v, hv⟩

theorem psiF_phi {φ : V → ℤ × ℤ} (hφ : Function.Injective φ) (v : V) : psiF φ (φ v) = v :=
  Function.leftInverse_invFun hφ v

/-- The embedding of the window into the ambient type. -/
def iotaF (φ : V → ℤ × ℤ) (r₀ m k : ℕ) (z : lamF φ r₀ k) : Amb V m := Sum.inr (psiF φ z.1)

theorem iotaF_injective {φ : V → ℤ × ℤ} (r₀ m k : ℕ) :
    Function.Injective (iotaF (V := V) φ r₀ m k) := by
  intro z z' h
  have h1 : psiF φ z.1 = psiF φ z'.1 := Sum.inr_injective h
  have := congrArg φ h1
  rw [phi_psiF z.2, phi_psiF z'.2] at this
  exact Subtype.ext this

/-- The weights on the window. -/
def wF (φ : V → ℤ × ℤ) (r₀ k : ℕ) (β : V → V → ℝ) (z z' : lamF φ r₀ k) : ℝ :=
  β (psiF φ z.1) (psiF φ z'.1)

/-- The vertices of the window in the ambient type. -/
def AkF (φ : V → ℤ × ℤ) (r₀ m k : ℕ) : Finset (Amb V m) :=
  univ.filter fun u => ∃ z, iotaF φ r₀ m k z = u

theorem mem_AkF {φ : V → ℤ × ℤ} (hφ : Function.Injective φ) {r₀ m k : ℕ} {u : Amb V m} :
    u ∈ AkF φ r₀ m k ↔ ∃ x, u = Sum.inr x ∧ lev r₀ k ≤ supNorm (φ x) ∧
      supNorm (φ x) ≤ lev r₀ (k + 1) := by
  simp only [AkF, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨psiF φ z.1, rfl, ?_⟩
    rw [phi_psiF z.2]
    exact lamF_bounds z.2
  · rintro ⟨x, rfl, hx⟩
    have hmem : φ x ∈ lamF φ r₀ k := mem_lamF.2 ⟨x, hx, rfl⟩
    refine ⟨⟨φ x, hmem⟩, ?_⟩
    simp [iotaF, psiF_phi hφ]

theorem mapW_wF_iotaF {φ : V → ℤ × ℤ} (r₀ m k : ℕ)
    {β : V → V → ℝ} (hdiag : ∀ u, β u u = 0) (u v : Amb V m) :
    mapW (wF φ r₀ k β) (iotaF φ r₀ m k) u v = restrW (AkF φ r₀ m k) (liftW β) u v := by
  unfold restrW
  by_cases hu : ∃ z, iotaF φ r₀ m k z = u
  · by_cases hv : ∃ z, iotaF φ r₀ m k z = v
    · obtain ⟨z, rfl⟩ := hu
      obtain ⟨z', rfl⟩ := hv
      have hz : iotaF φ r₀ m k z ∈ AkF φ r₀ m k := by
        simp only [AkF, mem_filter, mem_univ, true_and]; exact ⟨z, rfl⟩
      have hz' : iotaF φ r₀ m k z' ∈ AkF φ r₀ m k := by
        simp only [AkF, mem_filter, mem_univ, true_and]; exact ⟨z', rfl⟩
      rw [mapW_inj_apply (iotaF_injective r₀ m k) _ (fun a => hdiag _)]
      simp only [hz, hz', and_self, ↓reduceIte]
      simp only [iotaF, liftW_inr hdiag, wF]
    · have : ¬ (u ∈ AkF φ r₀ m k ∧ v ∈ AkF φ r₀ m k) := fun h => by
        simp only [AkF, mem_filter, mem_univ, true_and] at h
        exact hv h.2
      simp only [this, ↓reduceIte]
      exact mapW_not_range_right _ (fun a ha => hv ⟨a, ha⟩) u
  · have : ¬ (u ∈ AkF φ r₀ m k ∧ v ∈ AkF φ r₀ m k) := fun h => by
      simp only [AkF, mem_filter, mem_univ, true_and] at h
      exact hu h.1
    simp only [this, ↓reduceIte]
    exact mapW_not_range_left _ (fun a ha => hu ⟨a, ha⟩) v

end

end

end ArborealDecay.Superpoly
