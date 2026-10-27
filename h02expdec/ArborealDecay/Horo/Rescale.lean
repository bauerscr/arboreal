module

public import ArborealDecay.Super.IntQ
public import ArborealDecay.Super.Compose
public import ArborealDecay.Horo.Diffeo

/-!
# Rescaling odd generators: `ξ = eᵗ ψ`

For `c : O → ℝ`, `scaleA c : Gr O →ₐ Gr O` is the algebra map `θ_o ↦ c_o θ_o`; for a polynomial
`G` in the generators, `scaleA c (G(θ)) = G(c θ)`.

* `dgen_scaleA`: `∂_{θ_o} (G(c θ)) = c_o (∂_{θ_o} G)(c θ)`.
* `berezin_scaleA`: on `SG N P`, `B(G(cθ)) = ∏_i c_{ξ_i} c_{η_i} • (B G)(cθ)`, and if `c` is `1` on
  the parameter generators, `(B G)(cθ) = B G` (`scaleA_berezin`), so
  `berezin_scaleA_of_param`: `B(G(cθ)) = (∏_i c_{ξ_i} c_{η_i}) • B(G)`.
  Equivalently: the Berezin integral in `ψ` of `G(eᵗψ)` is `e^{t}` per generator times the Berezin
  integral in `ξ` of `G(ξ)` — a factor `e^{−t}` per generator in the measure `∂_ξ = e^{−t} ∂_ψ`.
* `berezinian_H24`: for `ℍ^{2|4}` (four odd generators per vertex, BCHS L1586–1596) combined
  with the bosonic Jacobian `eᵗ z` (`ArborealDecay.Horo.horoDens`) this gives the Berezinian
  `z e^{−3t}` per vertex.

Uses `ArborealDecay.Super.expand` (`x = π_o x + θ_o ∂_{θ_o} x`) from `Super/Compose.lean`.
-/

@[expose] public section

namespace ArborealDecay.Horo

noncomputable section

open ArborealDecay.Super CliffordAlgebra Grassmann

set_option linter.unusedSectionVars false

variable {O : Type*}

/-- The linear map `v ↦ (c_o v_o)_o`. -/
def scaleV (c : O → ℝ) : (O → ℝ) →ₗ[ℝ] (O → ℝ) where
  toFun v o := c o * v o
  map_add' v w := by funext o; simp [mul_add]
  map_smul' r v := by funext o; simp [smul_eq_mul]; ring

/-- The algebra map `θ_o ↦ c_o θ_o`. -/
def scaleA (c : O → ℝ) : Gr O →ₐ[ℝ] Gr O := ExteriorAlgebra.map (scaleV c)

theorem scaleA_ι (c : O → ℝ) (v : O → ℝ) :
    scaleA c (ExteriorAlgebra.ι ℝ v) = ExteriorAlgebra.ι ℝ (scaleV c v) :=
  ExteriorAlgebra.map_apply_ι _ _

theorem scaleA_gen [DecidableEq O] (c : O → ℝ) (o : O) : scaleA c (gen o) = c o • gen o := by
  rw [gen, scaleA_ι, ← map_smul]
  congr 1; funext o'
  by_cases h : o' = o
  · subst h; simp [scaleV]
  · simp [scaleV, h]

theorem inv'_scaleA (c : O → ℝ) (x : Gr O) : inv' (scaleA c x) = scaleA c (inv' x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι v => simp [scaleA, ExteriorAlgebra.ι]
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb, map_mul, map_mul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

/-- `∂_{θ_o} (G(cθ)) = c_o (∂_{θ_o} G)(cθ)`. -/
theorem dgen_scaleA (c : O → ℝ) (o : O) (x : Gr O) :
    dgen o (scaleA c x) = c o • scaleA c (dgen o x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι v =>
    have h0 : CliffordAlgebra.ι 0 v = ExteriorAlgebra.ι ℝ v := rfl
    rw [h0, scaleA_ι]
    simp only [dgen, contractLeft_ι, LinearMap.proj_apply, scaleV, LinearMap.coe_mk,
      AddHom.coe_mk, Algebra.algebraMap_eq_smul_one]
    rw [map_smul, map_one, smul_smul]
  | mul a b ha hb =>
    rw [map_mul, dgen_mul, ha, hb, dgen_mul, map_add, map_mul, map_mul, inv'_scaleA,
      smul_add, smul_mul_assoc, mul_smul_comm]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add, smul_add]

theorem scaleA_killA {c : O → ℝ} {S : Set O} (hc : ∀ o ∉ S, c o = 1) (x : Gr O) :
    scaleA c (killA S x) = killA S x := by
  have : (scaleV c).comp (killV S) = killV S := by
    ext v o
    simp only [LinearMap.comp_apply, scaleV, LinearMap.coe_mk, AddHom.coe_mk, killV_apply]
    by_cases h : o ∈ S
    · simp [Set.indicator_of_notMem (Set.notMem_compl_iff.2 h)]
    · rw [hc o h, one_mul]
  change ((scaleA c).comp (killA S)) x = _
  rw [scaleA, killA, ExteriorAlgebra.map_comp_map, this]

/-- If `∂_{θ_o} y = 0` for every `o ∈ S` (`S` finite), then `y` is free of the generators in
`S`. -/
theorem killA_eq_self_of_dgen [DecidableEq O] (S : Finset O) {y : Gr O}
    (h : ∀ o ∈ S, dgen o y = 0) : killA (S : Set O) y = y := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    have hT := ih fun o ho => h o (Finset.mem_insert_of_mem ho)
    rw [Finset.coe_insert, Set.insert_eq, ← killA_killA, hT]
    have := expand a y
    rw [h a (Finset.mem_insert_self a T), mul_zero, add_zero] at this
    exact this.symm

/-- If `∂_{θ_o} y = 0` whenever `c_o ≠ 1`, then `y(cθ) = y`. -/
theorem scaleA_eq_self_of_dgen [DecidableEq O] [Fintype O] {c : O → ℝ} {y : Gr O}
    (h : ∀ o, c o ≠ 1 → dgen o y = 0) : scaleA c y = y := by
  classical
  let S : Finset O := Finset.univ.filter fun o => c o ≠ 1
  have hy := killA_eq_self_of_dgen S (y := y) fun o ho => h o (Finset.mem_filter.1 ho).2
  rw [← hy, scaleA_killA]
  intro o ho
  by_contra hne
  exact ho (by simp [S, hne])

/-! ### The Berezin integral -/

section Berezin

variable {N P : Type*} [DecidableEq N] [DecidableEq P]

/-- The scale of the pair `i`. -/
def pairScale (c : (N ⊕ N) ⊕ P → ℝ) (i : N) : ℝ := c (.inl (.inl i)) * c (.inl (.inr i))

theorem bpair_scaleA (c : (N ⊕ N) ⊕ P → ℝ) (i : N) (x : SG N P) :
    bpair i (scaleA c x) = pairScale c i • scaleA c (bpair i x) := by
  simp only [bpair, LinearMap.coe_comp, Function.comp_apply, dξ, dη]
  rw [dgen_scaleA, map_smul, dgen_scaleA, smul_smul, pairScale, mul_comm]

theorem berezinL_scaleA (c : (N ⊕ N) ⊕ P → ℝ) (l : List N) (x : SG N P) :
    berezinL l (scaleA c x) = (l.map (pairScale c)).prod • scaleA c (berezinL l x) := by
  induction l with
  | nil => simp [berezinL]
  | cons i l ih =>
    rw [berezinL_cons, ih, map_smul, bpair_scaleA, berezinL_cons, smul_smul, List.map_cons,
      List.prod_cons, mul_comm]

variable [Fintype N]

theorem berezin_scaleA (c : (N ⊕ N) ⊕ P → ℝ) (x : SG N P) :
    berezin (scaleA c x) = (∏ i, pairScale c i) • scaleA c (berezin x) := by
  rw [berezin, berezinL_scaleA, Finset.prod_map_toList]

theorem dξ_berezin (j : N) (x : SG N P) : dξ j (berezin x) = 0 := by
  rw [berezin, ← berezinL_dξ_comm, berezinL_dξ (by simp)]

theorem dη_berezin (j : N) (x : SG N P) : dη j (berezin x) = 0 := by
  rw [berezin, ← berezinL_dη_comm, berezinL_dη (by simp)]

/-- The Berezin integral is free of the integrated generators, so rescaling them does nothing. -/
theorem scaleA_berezin [Fintype P] {c : (N ⊕ N) ⊕ P → ℝ} (hc : ∀ p, c (.inr p) = 1)
    (x : SG N P) : scaleA c (berezin x) = berezin x := by
  refine scaleA_eq_self_of_dgen fun o ho => ?_
  rcases o with (j | j) | p
  · exact dξ_berezin j x
  · exact dη_berezin j x
  · exact absurd (hc p) ho

/-- **Rescaling of the odd generators.** If `c` is `1` on the parameters,
`B(G(cθ)) = (∏_i c_{ξ_i} c_{η_i}) • B(G)`. -/
theorem berezin_scaleA_of_param [Fintype P] {c : (N ⊕ N) ⊕ P → ℝ} (hc : ∀ p, c (.inr p) = 1)
    (x : SG N P) : berezin (scaleA c x) = (∏ i, pairScale c i) • berezin x := by
  rw [berezin_scaleA, scaleA_berezin hc]

/-- The scaling `ξ_i = e^{τ_i} ψ_i`, `η_i = e^{τ_i} ψ̄_i` (parameters fixed). -/
def expScale (τ : N → ℝ) : (N ⊕ N) ⊕ P → ℝ
  | .inl (.inl i) => Real.exp (τ i)
  | .inl (.inr i) => Real.exp (τ i)
  | .inr _ => 1

theorem berezin_expScale [Fintype P] (τ : N → ℝ) (x : SG N P) :
    berezin (scaleA (expScale τ) x) = Real.exp (2 * ∑ i, τ i) • berezin x := by
  rw [berezin_scaleA_of_param (fun _ => rfl)]
  congr 1
  simp only [pairScale, expScale, ← Real.exp_add, ← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

end Berezin

/-! ### The `ℍ^{2|4}` Berezinian -/

section H24

variable {Λ P : Type*} [Fintype Λ] [DecidableEq Λ] [Fintype P] [DecidableEq P]

/-- The `ℍ^{2|4}` scaling: both odd pairs `(ξ^γ_i, η^γ_i)`, `γ = 1, 2`, of vertex `i` (pairs
indexed by `Λ ⊕ Λ`) are rescaled by `e^{t_i}`. -/
def scaleH24 (t : Λ → ℝ) : ((Λ ⊕ Λ) ⊕ (Λ ⊕ Λ)) ⊕ P → ℝ :=
  expScale (Sum.elim t t)

theorem berezin_scaleH24 (t : Λ → ℝ) (x : SG (Λ ⊕ Λ) P) :
    berezin (scaleA (scaleH24 t) x) = Real.exp (4 * ∑ i, t i) • berezin x := by
  rw [scaleH24, berezin_expScale, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  congr 2; ring

/-- **The `ℍ^{2|4}` Berezinian** (BCHS L1586–1596): the bosonic Jacobian `∏ eᵗ z` times `e^{−t}`
for each of the four odd generators per vertex is `∏ z e^{−3t}`. -/
theorem berezinian_H24 (p : Λ ⊕ Λ → ℝ) :
    horoDens p * Real.exp (-(4 * ∑ i, p (.inl i))) =
      ∏ i, hz (p (.inl i)) (p (.inr i)) * Real.exp (-3 * p (.inl i)) := by
  rw [horoDens, Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [mul_comm (Real.exp _), mul_assoc, ← Real.exp_add]
  ring_nf

end H24

end

end ArborealDecay.Horo

end
