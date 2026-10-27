module

public import ArborealDecay.Annulus.Energy
public import ArborealDecay.Annulus.Restrict
public import ArborealDecay.Annulus.Wired

/-!
# The second moment at a band vertex of the wired annulus (supplement `thm:annulus`, (N3))

Setting: `Λ ⊆ {r ≤ ‖z‖∞ ≤ 2r}`, nearest-neighbour weights `0 ≤ w ≤ β`, the wired graph
`wiredW = mapW w (annulusCollapse r Λ)`, its restriction `resW` to the component `compW` of the
inner terminal `a`, and `Γ = resW/(a=b)` with root `ρ = none`.

`second_moment_of_inputs`: for `r ≥ 32` and a lattice point `u` in the band
`5r/4 - 1 ≤ ‖u‖∞ ≤ 7r/4 + 1` (with `inr u` in the component),
`E^ρ_Γ e^{2 t_u} ≤ (r/8)^{-κ}`, `κ = 1/(6 C₁ (β+3))`, where `C₁ = logC` is the constant of the
logarithmic cutoff (`exists_log_cutoff`, `lem:log-cutoff`). The test function is the log cutoff
centred at `u` with `R = c₀ r = r/8`, extended by `0` at the wired vertices; it uses
`cor:sabot`(i) (`s = 2/3`), with (H1), (H2) from (A).
-/

open Matrix Real MeasureTheory

set_option linter.unusedSectionVars false

@[expose] public section

namespace ArborealDecay.Annulus

open ArborealDecay.TLaw ArborealDecay.Surgery ArborealDecay.Wiring ArborealDecay.CondComb
  ArborealDecay.Lattice

/-- The constant `C₁` of the logarithmic cutoff (`lem:log-cutoff`). -/
noncomputable def logC : ℝ := Classical.choose exists_log_cutoff

theorem logC_pos : 0 < logC := (Classical.choose_spec exists_log_cutoff).1

theorem logC_spec : ∀ (y : ℤ × ℤ) (R : ℝ), 4 ≤ R →
    ∃ v : ℤ × ℤ → ℝ, (∀ z, 0 ≤ v z ∧ v z ≤ 1) ∧ v y = 1 ∧
      (∀ z, R ≤ (supDist y z : ℝ) → v z = 0) ∧
      (∀ i j, IsNN i j → |v i - v j| ≤ logC / Real.log R) ∧
      ∑ p ∈ edgePairs y ((⌊R⌋₊ : ℤ) + 1), (v p.1 - v p.2) ^ 2 ≤ logC / Real.log R :=
  (Classical.choose_spec exists_log_cutoff).2

/-- The decay exponent `κ_β = 1/(6 C₁ (β+3))`. -/
noncomputable def kappaB (β : ℝ) : ℝ := 1 / (6 * logC * (β + 3))

theorem kappaB_pos {β : ℝ} (hβ : 0 ≤ β) : 0 < kappaB β := by
  unfold kappaB; have := logC_pos; positivity

variable {r : ℕ} {Λ : Finset (ℤ × ℤ)}

/-- The wired graph `G_r`. -/
noncomputable abbrev wiredW (r : ℕ) (Λ : Finset (ℤ × ℤ)) (w : Λ → Λ → ℝ) :
    Bool ⊕ Λ → Bool ⊕ Λ → ℝ :=
  mapW w (annulusCollapse r Λ)

/-- The component of the inner terminal `a = inl false`. -/
noncomputable def compW (r : ℕ) (Λ : Finset (ℤ × ℤ)) (w : Λ → Λ → ℝ) : Finset (Bool ⊕ Λ) :=
  compOf (wiredW r Λ w) (Sum.inl false)

/-- A small `DecidableEq` instance for vertex sets `C ⊆ Bool ⊕ Λ` (keeps instance terms on
`GamV C a b` below the synthesis size limit). -/
instance instDecidableEqWiredFinset (Λ : Finset (ℤ × ℤ)) (C : Finset (Bool ⊕ Λ)) :
    DecidableEq C :=
  Subtype.instDecidableEq

/-- `G_r` restricted to the component of the terminals. -/
noncomputable def resW (r : ℕ) (Λ : Finset (ℤ × ℤ)) (w : Λ → Λ → ℝ) :
    compW r Λ w → compW r Λ w → ℝ :=
  fun x y => wiredW r Λ w x y

/-- The terminal `a` in the component. -/
noncomputable def aW (r : ℕ) (Λ : Finset (ℤ × ℤ)) (w : Λ → Λ → ℝ) : compW r Λ w :=
  ⟨Sum.inl false, self_mem_compOf _ _⟩

theorem isWGraph_resW {w : Λ → Λ → ℝ} (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j) :
    IsWGraph (resW r Λ w) :=
  ⟨fun x y => mapW_symm hw _ x.1 y.1, fun x y => mapW_nonneg hw0 _ x.1 y.1,
    fun x => by simp [resW, wiredW, mapW]⟩

/-- Counting the energy of the log cutoff on the lattice (`eq:cutoff-gradient`). -/
theorem edgeSum_lattice_le {β : ℝ} (hβ : 0 ≤ β) {w : Λ → Λ → ℝ}
    (hnn : ∀ i j, w i j ≠ 0 → IsNN (i : ℤ × ℤ) j) (hB : ∀ i j, w i j ≤ β)
    {u : ℤ × ℤ} {R : ℝ} (hR : 0 ≤ R) {v : ℤ × ℤ → ℝ} (hv : ∀ z, R ≤ (supDist u z : ℝ) → v z = 0) :
    edgeSum w (fun z z' => (w z z' + 3) * (v z - v z') ^ 2) ≤
      (1 / 2) * ((β + 3) * ∑ p ∈ edgePairs u ((⌊R⌋₊ : ℤ) + 1), (v p.1 - v p.2) ^ 2) := by
  unfold edgeSum
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  rw [← Fintype.sum_prod_type' (f := fun z z' => if 0 < w z z' then
    (w z z' + 3) * (v z - v z') ^ 2 else 0), Finset.mul_sum]
  refine sum_le_of_injective (fun q : Λ × Λ => ((q.1 : ℤ × ℤ), (q.2 : ℤ × ℤ)))
    (fun q q' h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)) _ _ _
    (fun p _ => by have : 0 ≤ β + 3 := by linarith
                   positivity) ?_
  intro q hq
  by_cases hwq : 0 < w q.1 q.2
  · simp only [hwq, ite_true] at hq ⊢
    have hΔ : v q.1 ≠ v q.2 := fun h => hq (by rw [h, sub_self]; ring)
    have hnnq := hnn q.1 q.2 hwq.ne'
    have hd : |(supDist u q.1 : ℝ) - supDist u q.2| ≤ 1 := by
      have := abs_supDist_sub_le' hnnq u
      exact_mod_cast this
    rw [abs_le] at hd
    have hlt : (supDist u q.1 : ℝ) < R ∨ (supDist u q.2 : ℝ) < R := by
      by_contra hc
      push Not at hc
      exact hΔ ((hv _ hc.1).trans (hv _ hc.2).symm)
    refine ⟨(mem_edgePairs_floor hR).2 ⟨?_, ?_, hnnq⟩, ?_⟩
    · rcases hlt with h | h <;> linarith
    · rcases hlt with h | h <;> linarith
    · exact mul_le_mul_of_nonneg_right (by linarith [hB q.1 q.2]) (sq_nonneg _)
  · simp [hwq] at hq

/-- **Second moment at a band vertex** (supplement `thm:annulus`, steps (N3) and `ann-param`):
`E^ρ_Γ e^{2 t_u} ≤ (r/8)^{-κ_β}` for `r ≥ 32`, from (A). -/
theorem second_moment_of_inputs
    (hA : ∀ (V : Type) [Fintype V] [DecidableEq V] (w : V → V → ℝ) (hW : IsWGraph w),
      (supportGraph w).Connected → ∀ ρ : V,
        Z w ρ (3 / 2) = ENNReal.ofReal (H02.Zforest w hW.symm))
    {β : ℝ} (hβ : 0 ≤ β) (hr : 32 ≤ r) {w : Λ → Λ → ℝ} (hw : ∀ i j, w i j = w j i)
    (hw0 : ∀ i j, 0 ≤ w i j) (hnn : ∀ i j, w i j ≠ 0 → IsNN (i : ℤ × ℤ) j)
    (hB : ∀ i j, w i j ≤ β) {bW : compW r Λ w} (hbW : bW.1 = Sum.inl true)
    (hconn : (supportGraph (gammaW (resW r Λ w) (aW r Λ w) bW)).Connected)
    (u : Λ) (hband : 5 * (r : ℝ) / 4 - 1 ≤ supNorm (u : ℤ × ℤ) ∧
      (supNorm (u : ℤ × ℤ) : ℝ) ≤ 7 * r / 4 + 1)
    (hu : (Sum.inr u : Bool ⊕ Λ) ∈ compW r Λ w) :
    expect (gammaW (resW r Λ w) (aW r Λ w) bW) none (3 / 2)
      (fun τ => exp (2 * TLaw.ext none τ (colAB (aW r Λ w) bW ⟨Sum.inr u, hu⟩))) ≤
        ((r : ℝ) / 8) ^ (-kappaB β) := by
  have hr' : (32 : ℝ) ≤ r := by exact_mod_cast hr
  set R : ℝ := (r : ℝ) / 8 with hRdef
  have hR4 : 4 ≤ R := by rw [hRdef]; linarith
  obtain ⟨v, -, hvu, hvfar, hvgrad, hvsum⟩ := logC_spec (u : ℤ × ℤ) R hR4
  set L := Real.log R with hLdef
  have hL : 0 < L := Real.log_pos (by linarith)
  have hC := logC_pos
  have hvb : ∀ z : Λ, supNorm (z : ℤ × ℤ) = (r : ℤ) ∨ supNorm (z : ℤ × ℤ) = 2 * (r : ℤ) →
      v z = 0 := fun z hz => hvfar z (far_of_band hr hband hz)
  have hcoll : ∀ z : Λ, vWire Λ v (annulusCollapse r Λ z) = v z := vWire_coll hvb
  set φ : compW r Λ w → ℝ := fun x => vWire Λ v x.1 with hφdef
  have hya : (⟨Sum.inr u, hu⟩ : compW r Λ w) ≠ aW r Λ w := fun h => by
    have := congrArg Subtype.val h
    simp [aW] at this
  have hyb : (⟨Sum.inr u, hu⟩ : compW r Λ w) ≠ bW := fun h => by
    have := congrArg Subtype.val h
    rw [hbW] at this
    simp at this
  set y : Conductance.Interior (aW r Λ w) bW := ⟨⟨Sum.inr u, hu⟩, hya, hyb⟩
  have hφa : φ (aW r Λ w) = 0 := rfl
  have hφb : φ bW = 0 := by simp only [hφdef, hbW]; rfl
  have hφy : φ y.1 = 1 := hvu
  have hgrad : ∀ x x', 0 < resW r Λ w x x' → |φ x - φ x'| ≤ logC / L := fun x x' h =>
    grad_mapW (β := w) (annulusCollapse r Λ) (vWire Λ v) (fun z => v z) hcoll
      (fun z z' hz => hvgrad _ _ (hnn z z' hz.ne')) x.1 x'.1 h
  set γ : ℝ := L / (6 * logC * (β + 3)) with hγdef
  have hγ : 0 < γ := by positivity
  have hγG : γ * (logC / L) ≤ 1 / 18 := by
    rw [hγdef, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_pos hL hC]
  have hE : edgeSum (resW r Λ w) (fun x x' => (resW r Λ w x x' + 3) * (φ x - φ x') ^ 2) ≤
      (β + 3) * logC / L := by
    have h1 := edgeSum_restrict_le (compW r Λ w) (wiredW r Λ w)
      (fun y y' => (wiredW r Λ w y y' + 3) * (vWire Λ v y - vWire Λ v y') ^ 2)
      (fun y y' => mul_nonneg
        (by unfold wiredW; linarith [mapW_nonneg hw0 (annulusCollapse r Λ) y y'])
        (sq_nonneg _))
    have h2 := edgeSum_mapW_le hw0 (annulusCollapse r Λ) (vWire Λ v) (fun z => v z) hcoll
    have h3 := edgeSum_lattice_le hβ hnn hB (u := (u : ℤ × ℤ)) (R := R) (by linarith) hvfar
    have h4 : (1 / 2) * ((β + 3) * ∑ p ∈ edgePairs (u : ℤ × ℤ) ((⌊R⌋₊ : ℤ) + 1),
        (v p.1 - v p.2) ^ 2) ≤ (β + 3) * logC / L := by
      have hβ3 : 0 ≤ β + 3 := by linarith
      have := mul_le_mul_of_nonneg_left hvsum hβ3
      have hpos : 0 ≤ (β + 3) * (logC / L) := by positivity
      rw [mul_div_assoc]
      linarith
    exact h1.trans (h2.trans (h3.trans h4))
  have hm := moment_bound_of_inputs hA (isWGraph_resW hw hw0) hconn φ hφa hφb y hφy hγ hgrad
    hγG hE
  rw [← colAB_interior y] at hm
  refine hm.trans (le_of_eq ?_)
  rw [rpow_def_of_pos (by positivity : (0 : ℝ) < R), ← hLdef]
  congr 1
  simp only [hγdef, kappaB]
  field_simp
  ring

end ArborealDecay.Annulus
