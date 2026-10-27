module

public import ArborealDecay.Lattice

/-!
# Geometry of the wired annulus (note L824–879)

`annulusCollapse r Λ` wires the inner boundary `‖z‖∞ = r` of `Λ ⊆ {r ≤ ‖z‖∞ ≤ 2r}` to
`a = inl false` and the outer boundary `‖z‖∞ = 2r` to `b = inl true`.

* `fWire`: the Lipschitz cutoff `f` (`lipCutoff r`) on the wired graph (`1` at `a`, `0` at `b`);
  `fWire_coll`: `f ∘ collapse = lipCutoff r`.
* `band_of_ne`: an edge where `f` varies has both endpoints in `5r/4 - 1 ≤ ‖·‖∞ ≤ 7r/4 + 1`
  (`coll_of_band`: these are not wired, for `r ≥ 8`).
* `far_of_band`: for `r ≥ 32` and `y` in the band, the boundary is at sup-distance `≥ r/8 = c₀ r`
  from `y` (`c₀ = 1/8`, supplement `thm:annulus` (N3)).
* `vWire`: a lattice function extended by `0` at the wired vertices; `vWire_coll`.
-/

open Real

set_option linter.unusedSectionVars false

@[expose] public section

namespace ArborealDecay.Annulus

open ArborealDecay.Lattice

/-- Wiring of the annulus `{r ≤ ‖z‖∞ ≤ 2r}`: the inner boundary becomes `inl false`, the outer
boundary `inl true`. -/
def annulusCollapse (r : ℕ) (Λ : Finset (ℤ × ℤ)) (z : Λ) : Bool ⊕ Λ :=
  if supNorm (z : ℤ × ℤ) = (r : ℤ) then Sum.inl false
  else if supNorm (z : ℤ × ℤ) = 2 * (r : ℤ) then Sum.inl true else Sum.inr z

variable {r : ℕ} {Λ : Finset (ℤ × ℤ)}

/-- The cutoff `f` on the wired vertex set. -/
noncomputable def fWire (r : ℕ) (Λ : Finset (ℤ × ℤ)) : Bool ⊕ Λ → ℝ :=
  Sum.elim (fun t => if t then 0 else 1) (fun z => lipCutoff r z)

theorem fWire_coll (hr : 0 < r) (u : Λ) :
    fWire r Λ (annulusCollapse r Λ u) = lipCutoff r u := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  unfold annulusCollapse
  split_ifs with h1 h2
  · simp only [fWire, Sum.elim_inl, Bool.false_eq_true, ite_false]
    refine (lipCutoff_eq_one hr' ?_).symm
    have : (supNorm (u : ℤ × ℤ) : ℝ) = r := by exact_mod_cast h1
    rw [this]; linarith
  · simp only [fWire, Sum.elim_inl, ite_true]
    refine (lipCutoff_eq_zero hr' ?_).symm
    have : (supNorm (u : ℤ × ℤ) : ℝ) = 2 * r := by exact_mod_cast h2
    rw [this]; linarith
  · rfl

theorem abs_supNorm_sub_le_supDist (y z : ℤ × ℤ) :
    |(supNorm y : ℝ) - supNorm z| ≤ supDist y z := by
  have h1 := supDist_triangle y z 0
  have h2 := supDist_triangle z y 0
  rw [← supNorm_eq_supDist] at h1 h2
  rw [supNorm_eq_supDist y, supNorm_eq_supDist z]
  rw [← supNorm_eq_supDist, ← supNorm_eq_supDist, supDist_comm z y] at *
  have : |supNorm y - supNorm z| ≤ supDist y z := by
    rw [abs_le]; constructor <;> linarith
  exact_mod_cast this

/-- Edges on which the cutoff varies lie in the band `5r/4 - 1 ≤ ‖·‖∞ ≤ 7r/4 + 1`. -/
theorem band_of_ne (hr : 0 < r) {u u' : ℤ × ℤ} (h : IsNN u u')
    (hne : lipCutoff r u ≠ lipCutoff r u') :
    5 * (r : ℝ) / 4 - 1 ≤ supNorm u ∧ (supNorm u : ℝ) ≤ 7 * r / 4 + 1 := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hd : |(supNorm u : ℝ) - supNorm u'| ≤ 1 := by
    have := abs_supNorm_sub_le h
    exact_mod_cast this
  rw [abs_le] at hd
  constructor
  · by_contra hc
    push Not at hc
    exact hne ((lipCutoff_eq_one hr' (by linarith)).trans (lipCutoff_eq_one hr' (by linarith)).symm)
  · by_contra hc
    push Not at hc
    exact hne ((lipCutoff_eq_zero hr' (by linarith)).trans
      (lipCutoff_eq_zero hr' (by linarith)).symm)

theorem coll_of_band (hr : 8 ≤ r) {u : Λ}
    (hb : 5 * (r : ℝ) / 4 - 1 ≤ supNorm (u : ℤ × ℤ) ∧ (supNorm (u : ℤ × ℤ) : ℝ) ≤ 7 * r / 4 + 1) :
    annulusCollapse r Λ u = Sum.inr u := by
  have hr' : (8 : ℝ) ≤ r := by exact_mod_cast hr
  unfold annulusCollapse
  have h1 : supNorm (u : ℤ × ℤ) ≠ (r : ℤ) := by
    intro h
    have : (supNorm (u : ℤ × ℤ) : ℝ) = r := by exact_mod_cast h
    linarith [hb.1]
  have h2 : supNorm (u : ℤ × ℤ) ≠ 2 * (r : ℤ) := by
    intro h
    have : (supNorm (u : ℤ × ℤ) : ℝ) = 2 * r := by exact_mod_cast h
    linarith [hb.2]
  rw [ite_eq_right h1, ite_eq_right h2]

/-- For `r ≥ 32` and `y` in the band, every wired lattice point is at sup-distance `≥ r/8`. -/
theorem far_of_band (hr : 32 ≤ r) {y z : ℤ × ℤ}
    (hb : 5 * (r : ℝ) / 4 - 1 ≤ supNorm y ∧ (supNorm y : ℝ) ≤ 7 * r / 4 + 1)
    (hz : supNorm z = (r : ℤ) ∨ supNorm z = 2 * (r : ℤ)) : (r : ℝ) / 8 ≤ supDist y z := by
  have hr' : (32 : ℝ) ≤ r := by exact_mod_cast hr
  have hd := abs_supNorm_sub_le_supDist y z
  rw [abs_le] at hd
  rcases hz with h | h
  · have : (supNorm z : ℝ) = r := by exact_mod_cast h
    linarith [hb.1]
  · have : (supNorm z : ℝ) = 2 * r := by exact_mod_cast h
    linarith [hb.2]

/-- A lattice function on the wired vertex set, `0` at the two wired terminals. -/
noncomputable def vWire (Λ : Finset (ℤ × ℤ)) (v : ℤ × ℤ → ℝ) : Bool ⊕ Λ → ℝ :=
  Sum.elim (fun _ => 0) (fun z => v z)

theorem vWire_coll {v : ℤ × ℤ → ℝ}
    (hv : ∀ z : Λ, supNorm (z : ℤ × ℤ) = (r : ℤ) ∨ supNorm (z : ℤ × ℤ) = 2 * (r : ℤ) → v z = 0)
    (u : Λ) : vWire Λ v (annulusCollapse r Λ u) = v u := by
  unfold annulusCollapse
  split_ifs with h1 h2
  · exact (hv u (Or.inl h1)).symm
  · exact (hv u (Or.inr h2)).symm
  · rfl

end ArborealDecay.Annulus
