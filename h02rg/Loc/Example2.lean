import Loc.Image

/-!
# Example (ii) of Section `sec:Loc`: localisation of a quadratic convolution

Let `q : ℤ^d → ℝ` be finitely supported and invariant under lattice rotations, and
`F = ∑_{x ∈ X} ∑_y q(x - y) ψ̄_y ψ_y`. Then (`LocXY_exF`, `LocX_exF`)
`Loc_{X,Y} F = ∑_{y ∈ Y} P_y` with
`P_x = q^{(1)} ψ̄_xψ_x + q^{(**)} (½ ψ̄_x(Δψ)_x + ½ (Δψ̄)_xψ_x + (∇ψ̄)_x(∇ψ)_x)`,
`q^{(1)} = ∑_y q(y)`, `q^{(**)} = ∑_y y_1² q(y)`.

Formalization choices:

* The support of `q` is taken to lie in the box `ball d r = {|w|_∞ ≤ r}`, and the sum over
  `y ∈ Λ` is written as a sum over offsets `w = x - y ∈ ball d r` (`exF`); `q^{(1)}`, `q^{(**)}`
  are the corresponding sums over the box (`qOne`, `qTwo`). This is the text's `F` as soon as
  the box does not wrap around the torus, which is our "`Λ` large enough" condition
  `2 (|x - b|_∞ + r + 1) < L^N` for `x ∈ X` (it also makes `X` a patch).
* Invariance under lattice rotations is expressed as invariance under the coordinate
  reflections `reflZ i` and the coordinate permutations `permZ σ` (these generate the
  hyperoctahedral group).
* `(∇ψ̄)_x(∇ψ)_x = ½ ∑_{e ∈ 𝓔_d} (∇_e ψ̄)_x(∇_e ψ)_x` (`gradbarSq`); it equals `-gradSq x`.
* Scalars: as in the text the kernel `q` is real, and so are its moments `qOne`, `qTwo`; they are
  cast to `ℂ` in `exF` and in the (complex) coefficients `cEx` and polynomial `exP`.

Proof: the pairings of `F` with the test polynomials are
`-∑_x ∑_w q(w) Q_β(ℓ_x - w, ℓ_x - w)`; by the vanishing of the first and mixed second moments
of `q` (reflection invariance) and the equality of the diagonal second moments (permutation
invariance), these equal `-∑_x (q^{(1)} f(ℓ_x) + ½ q^{(**)} ∑_i (Δ_i f)(ℓ_x))`,
`f(m) = Q_β(m, m)` (`key`), which are the pairings of an explicit combination of local
monomials (`cEx`).  By uniqueness of the coefficients, these are the coefficients of `Loc F`.
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD Matrix

variable {d L N : ℕ} [NeZero L]

/-- The box `{w ∈ ℤ^d : |w|_∞ ≤ r}`. -/
def ball (d r : ℕ) : Finset (Zd d) := Fintype.piFinset fun _ => Finset.Icc (-(r : ℤ)) r

theorem mem_ball {r : ℕ} {w : Zd d} : w ∈ ball d r ↔ ∀ k, -(r : ℤ) ≤ w k ∧ w k ≤ r := by
  simp [ball]

theorem supNormZ_le_of_mem_ball {r : ℕ} {w : Zd d} (hw : w ∈ ball d r) : supNormZ w ≤ r := by
  rw [supNormZ_le_iff]; intro k; have := (mem_ball.1 hw) k; omega

theorem psibar_mul_psi (u v : Lam d L N) : psibar u * psi v = -(psi v * psibar u) :=
  ι_anticomm _ _

theorem ε_psibar_mul_psi (u v : Lam d L N) : ε (psibar u * psi v) = 0 := by
  simp [psibar, psi, ψ]

/-- Reindexing a sum over the box by a bijection preserving the box. -/
theorem sum_ball_equiv {r : ℕ} (φ : Zd d ≃ Zd d) (hφ : ∀ w, φ w ∈ ball d r ↔ w ∈ ball d r)
    (g : Zd d → ℝ) : ∑ w ∈ ball d r, g (φ w) = ∑ w ∈ ball d r, g w := by
  refine Finset.sum_nbij' φ φ.symm (fun w hw => (hφ w).2 hw)
    (fun w hw => by rw [← hφ, Equiv.apply_symm_apply]; exact hw) (fun w _ => by simp)
    (fun w _ => by simp) (fun w _ => rfl)

theorem reflZ_apply (i k : Fin d) (w : Zd d) : reflZ i w k = if k = i then -w k else w k := rfl

theorem reflZ_reflZ (i : Fin d) (w : Zd d) : reflZ i (reflZ i w) = w := by
  funext k; by_cases h : k = i <;> simp [reflZ_apply, h]

theorem permZ_apply (σ : Equiv.Perm (Fin d)) (w : Zd d) (k : Fin d) : permZ σ w k = w (σ.symm k) :=
  rfl

/-- The reflection as an equivalence. -/
def reflEquiv (i : Fin d) : Zd d ≃ Zd d where
  toFun := reflZ i
  invFun := reflZ i
  left_inv := reflZ_reflZ i
  right_inv := reflZ_reflZ i

/-- The permutation as an equivalence. -/
def permEquiv (σ : Equiv.Perm (Fin d)) : Zd d ≃ Zd d where
  toFun := permZ σ
  invFun := permZ σ.symm
  left_inv w := by funext k; simp [permZ_apply]
  right_inv w := by funext k; simp [permZ_apply]

theorem reflZ_mem_ball {r : ℕ} (i : Fin d) (w : Zd d) : reflZ i w ∈ ball d r ↔ w ∈ ball d r := by
  simp only [mem_ball, reflZ_apply]
  refine forall_congr' fun k => ?_
  split_ifs <;> constructor <;> intro h <;> omega

theorem permZ_mem_ball {r : ℕ} (σ : Equiv.Perm (Fin d)) (w : Zd d) :
    permZ σ w ∈ ball d r ↔ w ∈ ball d r := by
  simp only [mem_ball, permZ_apply]
  exact ⟨fun h k => by simpa using h (σ k), fun h k => h _⟩

/-! ### Moments of the kernel -/

/-- `q^{(1)} = ∑_w q(w)`. -/
def qOne (r : ℕ) (q : Zd d → ℝ) : ℝ := ∑ w ∈ ball d r, q w

/-- `q^{(**)} = ∑_w w_{i₀}² q(w)`. -/
def qTwo (r : ℕ) (q : Zd d → ℝ) (i₀ : Fin d) : ℝ := ∑ w ∈ ball d r, q w * (w i₀ : ℝ) ^ 2

/-- The lattice vector `w ∈ ℤ^d` as an element of `ℝ^d`. -/
def cz (w : Zd d) : Fin d → ℝ := fun k => (w k : ℝ)

/-- The unit vector `e_i ∈ ℝ^d`. -/
def er (i : Fin d) : Fin d → ℝ := cz (ez i)

theorem er_apply (i k : Fin d) : er i k = if k = i then 1 else 0 := by
  by_cases h : k = i <;> simp [er, cz, ez, h]

theorem diff2 (ℓ : Fin d → ℝ) (j l : Fin d) :
    ∑ i, ((ℓ j + er i j) * (ℓ l + er i l) + (ℓ j - er i j) * (ℓ l - er i l) - 2 * (ℓ j * ℓ l)) =
      if j = l then 2 else 0 := by
  have e : ∀ i, (ℓ j + er i j) * (ℓ l + er i l) + (ℓ j - er i j) * (ℓ l - er i l) -
      2 * (ℓ j * ℓ l) = if i = j then (if j = l then 2 else 0) else 0 := fun i => by
    rw [show (ℓ j + er i j) * (ℓ l + er i l) + (ℓ j - er i j) * (ℓ l - er i l) - 2 * (ℓ j * ℓ l) =
      2 * (er i j * er i l) by ring, er_apply, er_apply]
    split_ifs <;> subst_vars <;> simp_all
  rw [sum_congr rfl fun i _ => e i]; simp

section Moments

variable {r : ℕ} {q : Zd d → ℝ} (hrefl : ∀ i w, q (reflZ i w) = q w)
  (hperm : ∀ σ w, q (permZ σ w) = q w)
include hrefl

theorem mom1 (j : Fin d) : ∑ w ∈ ball d r, q w * (w j : ℝ) = 0 := by
  have h := sum_ball_equiv (r := r) (reflEquiv j) (reflZ_mem_ball j) fun w => q w * (w j : ℝ)
  simp only [reflEquiv, Equiv.coe_fn_mk, hrefl, reflZ_apply, if_true,
    Int.cast_neg, mul_neg, sum_neg_distrib] at h
  linarith

include hperm in
theorem mom2 (i₀ j l : Fin d) :
    ∑ w ∈ ball d r, q w * ((w j : ℝ) * w l) = if j = l then qTwo r q i₀ else 0 := by
  split_ifs with hjl
  · subst hjl
    have h := sum_ball_equiv (r := r) (permEquiv (Equiv.swap i₀ j)) (permZ_mem_ball _)
      fun w => q w * (w i₀ : ℝ) ^ 2
    simp only [permEquiv, Equiv.coe_fn_mk, hperm, permZ_apply, Equiv.symm_swap,
      Equiv.swap_apply_left] at h
    rw [qTwo, ← h]; exact sum_congr rfl fun w _ => by ring
  · have h := sum_ball_equiv (r := r) (reflEquiv j) (reflZ_mem_ball j)
      fun w => q w * ((w j : ℝ) * w l)
    simp only [reflEquiv, Equiv.coe_fn_mk, hrefl, reflZ_apply, if_true,
      if_neg (Ne.symm hjl), Int.cast_neg, neg_mul, mul_neg, sum_neg_distrib] at h
    linarith

theorem mom1' (ℓ : Fin d → ℝ) (j : Fin d) :
    ∑ w ∈ ball d r, q w * (ℓ j - cz w j) = qOne r q * ℓ j := by
  simp only [mul_sub, sum_sub_distrib, cz, mom1 hrefl, qOne, sum_mul]
  ring

include hperm in
theorem mom2' (i₀ : Fin d) (ℓ : Fin d → ℝ) (j l : Fin d) :
    ∑ w ∈ ball d r, q w * ((ℓ j - cz w j) * (ℓ l - cz w l)) =
      qOne r q * (ℓ j * ℓ l) + if j = l then qTwo r q i₀ else 0 := by
  have e : ∀ w, q w * ((ℓ j - cz w j) * (ℓ l - cz w l)) =
      q w * (ℓ j * ℓ l) - ℓ j * (q w * (w l : ℝ)) - ℓ l * (q w * (w j : ℝ)) +
        q w * ((w j : ℝ) * w l) := fun w => by simp only [cz]; ring
  simp only [e, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← sum_mul, mom1 hrefl,
    mom2 hrefl hperm i₀, qOne]
  ring

include hperm in
theorem key_prod (i₀ : Fin d) (ℓ : Fin d → ℝ) (κ : ℝ) (j l : Fin d) :
    ∑ w ∈ ball d r, q w * (κ * ((ℓ j - cz w j) * (ℓ l - cz w l))) =
      qOne r q * (κ * (ℓ j * ℓ l)) + qTwo r q i₀ / 2 * ∑ i, (κ * ((ℓ j + er i j) * (ℓ l + er i l))
        + κ * ((ℓ j - er i j) * (ℓ l - er i l)) - 2 * (κ * (ℓ j * ℓ l))) := by
  have e1 : ∀ w, q w * (κ * ((ℓ j - cz w j) * (ℓ l - cz w l))) =
      κ * (q w * ((ℓ j - cz w j) * (ℓ l - cz w l))) := fun w => by ring
  have e2 : ∀ i, κ * ((ℓ j + er i j) * (ℓ l + er i l)) + κ * ((ℓ j - er i j) * (ℓ l - er i l)) -
      2 * (κ * (ℓ j * ℓ l)) = κ * ((ℓ j + er i j) * (ℓ l + er i l) +
        (ℓ j - er i j) * (ℓ l - er i l) - 2 * (ℓ j * ℓ l)) := fun i => by ring
  rw [sum_congr rfl fun w _ => e1 w, sum_congr rfl fun i _ => e2 i, ← mul_sum, ← mul_sum,
    mom2' hrefl hperm i₀, diff2]
  split_ifs <;> ring

include hperm in
/-- The Taylor expansion of the convolution with `q` on the test polynomials:
`∑_w q(w) f(ℓ - w) = q^{(1)} f(ℓ) + ½ q^{(**)} ∑_i (Δ_i f)(ℓ)` for `f(m) = Q_β(m, m)`. -/
theorem key (i₀ : Fin d) (β : Mono d) (ℓ : Fin d → ℝ) :
    ∑ w ∈ ball d r, q w * Qpoly β (ℓ - cz w) (ℓ - cz w) =
      qOne r q * Qpoly β ℓ ℓ + qTwo r q i₀ / 2 * ∑ i, (Qpoly β (ℓ + er i) (ℓ + er i) +
        Qpoly β (ℓ - er i) (ℓ - er i) - 2 * Qpoly β ℓ ℓ) := by
  have hsq : ∀ x : ℝ, x ^ 2 / 2 = 1 / 2 * (x * x) := fun x => by ring
  cases β with
  | c =>
    simp only [Qpoly]
    rw [Finset.sum_eq_zero (s := univ) fun i _ => by ring]; simp [qOne]
  | a1 j =>
    simp only [Qpoly, Pi.add_apply, Pi.sub_apply, mom1' hrefl]
    rw [Finset.sum_eq_zero (s := univ) fun i _ => by ring]; ring
  | b1 j =>
    simp only [Qpoly, Pi.add_apply, Pi.sub_apply, mom1' hrefl]
    rw [Finset.sum_eq_zero (s := univ) fun i _ => by ring]; ring
  | a2 s =>
    induction s using Sym2.ind with
    | h j l =>
      simp only [Qpoly, Sym2.lift_mk, Pi.add_apply, Pi.sub_apply]
      split_ifs with hjl
      · subst hjl; simp only [hsq]; exact key_prod hrefl hperm i₀ ℓ _ j j
      · simpa using key_prod hrefl hperm i₀ ℓ 1 j l
  | b2 s =>
    induction s using Sym2.ind with
    | h j l =>
      simp only [Qpoly, Sym2.lift_mk, Pi.add_apply, Pi.sub_apply]
      split_ifs with hjl
      · subst hjl; simp only [hsq]; exact key_prod hrefl hperm i₀ ℓ _ j j
      · simpa using key_prod hrefl hperm i₀ ℓ 1 j l
  | m2 j l =>
    simp only [Qpoly, Pi.add_apply, Pi.sub_apply]
    simpa using key_prod hrefl hperm i₀ ℓ 1 j l

end Moments

/-! ### The Grassmann side -/

/-- `(∇ψ̄)_x (∇ψ)_x = ½ ∑_{e ∈ 𝓔_d} (∇_e ψ̄)_x (∇_e ψ)_x` (the ordering of the text). -/
def gradbarSq (x : Lam d L N) : Alg d L N := (1 / 2 : ℂ) • ∑ e : Dir d, gradbar e x * grad e x

theorem grad_eq_ι (e : Dir d) (x : Lam d L N) :
    grad e x = ExteriorAlgebra.ι ℂ (ev (x + dirVec e, 1) - ev (x, 1)) := by
  simp [grad, psi, ψ, map_sub]

theorem gradbar_eq_ι (e : Dir d) (x : Lam d L N) :
    gradbar e x = ExteriorAlgebra.ι ℂ (ev (x + dirVec e, -1) - ev (x, -1)) := by
  simp [gradbar, psibar, ψ, map_sub]

theorem gradbarSq_eq (x : Lam d L N) : gradbarSq x = -gradSq x := by
  rw [gradbarSq, gradSq, ← smul_neg, ← sum_neg_distrib]
  congr 1
  refine sum_congr rfl fun e _ => ?_
  rw [grad_eq_ι, gradbar_eq_ι, ι_anticomm]

theorem lapPsi_eq_ι (x : Lam d L N) : ∃ v, lapPsi x = ExteriorAlgebra.ι ℂ v :=
  ⟨∑ i : Fin d, (ev (x + dirVec (Sum.inl i), 1) + ev (x - dirVec (Sum.inl i), 1) -
    (2 : ℂ) • ev (x, 1)), by
      rw [lapPsi_eq]; simp only [psi, ψ, map_sum, map_add, map_sub, map_smul]⟩

theorem lapPsibar_eq_ι (x : Lam d L N) : ∃ v, lapPsibar x = ExteriorAlgebra.ι ℂ v :=
  ⟨∑ i : Fin d, (ev (x + dirVec (Sum.inl i), -1) + ev (x - dirVec (Sum.inl i), -1) -
    (2 : ℂ) • ev (x, -1)), by
      rw [lapPsibar_eq]; simp only [psibar, ψ, map_sum, map_add, map_sub, map_smul]⟩

theorem psibar_mul_lapPsi (x : Lam d L N) : psibar x * lapPsi x = -(lapPsi x * psibar x) := by
  obtain ⟨v, hv⟩ := lapPsi_eq_ι x
  rw [hv, psibar, ψ, ι_anticomm]

theorem lapPsibar_mul_psi (x : Lam d L N) : lapPsibar x * psi x = -(psi x * lapPsibar x) := by
  obtain ⟨v, hv⟩ := lapPsibar_eq_ι x
  rw [hv, psi, ψ, ι_anticomm]

/-- `ψ(Δψ̄) + (Δψ)ψ̄ + 2(∇ψ)(∇ψ̄) = ∑_i Δ_i(ψψ̄)`. -/
theorem lap_prod (x : Lam d L N) :
    lapPsi x * psibar x + psi x * lapPsibar x + (2 : ℂ) • gradSq x =
      ∑ i : Fin d, (psi (x + dirVec (Sum.inl i)) * psibar (x + dirVec (Sum.inl i)) +
        psi (x - dirVec (Sum.inl i)) * psibar (x - dirVec (Sum.inl i)) -
          (2 : ℂ) • (psi x * psibar x)) := by
  rw [lapPsi_eq, lapPsibar_eq, gradSq, Fintype.sum_sum_type]
  simp only [sum_mul, mul_sum, smul_add, smul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  simp only [grad, gradbar, dirVec_inr_eq, ← sub_eq_add_neg]
  simp only [mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm,
    smul_sub, smul_smul]
  module

/-- The coefficients of `Loc F` in the monomial basis. -/
def cEx (q1 q2 : ℂ) : Mono d → ℂ
  | .c => -q1
  | .a2 s => if s.IsDiag then -(q2 / 2) else 0
  | .b2 s => if s.IsDiag then -(q2 / 2) else 0
  | .m2 i k => if i = k then -q2 else 0
  | _ => 0

theorem sum_cEx (q1 q2 : ℂ) (Z : Finset (Lam d L N)) :
    ∑ M, cEx q1 q2 M • monoSet M Z = ∑ z ∈ Z, ((-q1) • (psi z * psibar z) -
      (q2 / 2) • (lapPsi z * psibar z + psi z * lapPsibar z + (2 : ℂ) • gradSq z)) := by
  rw [sum_mono]
  have h1 : ∑ i, cEx q1 q2 (.a1 i) • monoSet (.a1 i) Z = 0 := by simp [cEx]
  have h2 : ∑ i, cEx q1 q2 (.b1 i) • monoSet (.b1 i) Z = 0 := by simp [cEx]
  have h3 : ∑ s, cEx q1 q2 (.a2 s) • monoSet (.a2 s) Z =
      ∑ i, (-(q2 / 2)) • monoSet (.a2 s(i, i)) Z := by
    rw [sum_sym2_diag]
    · simp [cEx]
    · intro s hs; simp [cEx, hs]
  have h4 : ∑ s, cEx q1 q2 (.b2 s) • monoSet (.b2 s) Z =
      ∑ i, (-(q2 / 2)) • monoSet (.b2 s(i, i)) Z := by
    rw [sum_sym2_diag]
    · simp [cEx]
    · intro s hs; simp [cEx, hs]
  have h5 : ∑ i, ∑ k, cEx q1 q2 (.m2 i k) • monoSet (.m2 i k) Z =
      ∑ i, (-q2) • monoSet (.m2 i i) Z := by
    refine sum_congr rfl fun i _ => ?_
    rw [sum_eq_single i]
    · simp [cEx]
    · intro k _ hik; simp [cEx, Ne.symm hik]
    · simp
  rw [h1, h2, h3, h4, h5, add_zero, add_zero]
  simp only [← smul_sum, monoSet]
  rw [sum_comm (s := univ) (t := Z), sum_comm (s := univ) (t := Z), sum_comm (s := univ) (t := Z)]
  simp only [sum_monoAt_a2, sum_monoAt_b2, sum_monoAt_m2, monoAt_c, cEx, sum_add_distrib,
    sum_sub_distrib, ← smul_sum]
  module

/-! ### The example -/

/-- The polynomial `F = ∑_{x ∈ X} ∑_{w} q(w) ψ̄_{x-w} ψ_{x-w}` of Example (ii) (with `y = x - w`),
the kernel `q` being summed over the box `|w|_∞ ≤ r` containing its support. -/
def exF (X : Finset (Lam d L N)) (r : ℕ) (q : Zd d → ℝ) : Alg d L N :=
  ∑ x ∈ X, ∑ w ∈ ball d r, (q w : ℂ) • (psibar (x - prj w) * psi (x - prj w))

/-- `P_x = q^{(1)} ψ̄_x ψ_x + q^{(**)} (½ ψ̄_x (Δψ)_x + ½ (Δψ̄)_x ψ_x + (∇ψ̄)_x (∇ψ)_x)`. -/
def exP (q1 q2 : ℂ) (x : Lam d L N) : Alg d L N :=
  q1 • (psibar x * psi x) + q2 • ((1 / 2 : ℂ) • (psibar x * lapPsi x) +
    (1 / 2 : ℂ) • (lapPsibar x * psi x) + gradbarSq x)

theorem exP_eq (q1 q2 : ℂ) (x : Lam d L N) : exP q1 q2 x = (-q1) • (psi x * psibar x) -
    (q2 / 2) • (lapPsi x * psibar x + psi x * lapPsibar x + (2 : ℂ) • gradSq x) := by
  rw [exP, psibar_mul_psi, psibar_mul_lapPsi, lapPsibar_mul_psi, gradbarSq_eq]
  module

theorem ε_exF (X : Finset (Lam d L N)) (r : ℕ) (q : Zd d → ℝ) : ε (exF X r q) = 0 := by
  simp only [exF, map_sum, map_smul, ε_psibar_mul_psi, smul_zero, sum_const_zero]

theorem mu_neg (b : Lam d L N) (β : Mono d) (F : Alg d L N) : mu b β (-F) = -mu b β F := by
  rw [← neg_one_smul ℂ F, mu_smul]; ring

theorem mu_sub (b : Lam d L N) (β : Mono d) (F G : Alg d L N) :
    mu b β (F - G) = mu b β F - mu b β G := by
  rw [sub_eq_add_neg, mu_add, mu_neg, sub_eq_add_neg]

variable {X : Finset (Lam d L N)} {r : ℕ}

theorem patch_of (hX : ∀ x ∈ X, 2 * (supNorm (x - base X) + r + 1) < L ^ N) : Patch X :=
  fun x hx => by have := hX x hx; omega

theorem lift_sub_prj (hX : ∀ x ∈ X, 2 * (supNorm (x - base X) + r + 1) < L ^ N) {x : Lam d L N}
    (hx : x ∈ X) {w : Zd d} (hw : w ∈ ball d r) :
    lift (base X) (x - prj w) = lift (base X) x - cz w := by
  have h1 := hX x hx
  have h2 := supNormZ_le_of_mem_ball hw
  rw [sub_eq_add_neg, ← prj_neg, lift_add (by rw [supNormZ_neg]; omega)]
  funext k; simp [cz, sub_eq_add_neg]

theorem lift_add_e (hX : ∀ x ∈ X, 2 * (supNorm (x - base X) + r + 1) < L ^ N) {x : Lam d L N}
    (hx : x ∈ X) (i : Fin d) :
    lift (base X) (x + dirVec (Sum.inl i)) = lift (base X) x + er i := by
  have h1 := hX x hx
  have h2 := supNormZ_ez i
  rw [← prj_ez, lift_add (by omega)]; rfl

theorem lift_sub_e (hX : ∀ x ∈ X, 2 * (supNorm (x - base X) + r + 1) < L ^ N) {x : Lam d L N}
    (hx : x ∈ X) (i : Fin d) :
    lift (base X) (x - dirVec (Sum.inl i)) = lift (base X) x - er i := by
  have h1 := hX x hx
  have h2 := supNormZ_ez i
  rw [sub_eq_add_neg, ← dirVec_inr_eq, ← prj_neg_ez, lift_add (by rw [supNormZ_neg]; omega)]
  funext k; simp [er, cz, sub_eq_add_neg]

theorem mu_exF (hX : ∀ x ∈ X, 2 * (supNorm (x - base X) + r + 1) < L ^ N) (q : Zd d → ℝ)
    (β : Mono d) : mu (base X) β (exF X r q) = -∑ x ∈ X, ∑ w ∈ ball d r,
      (q w : ℂ) * (Qpoly β (lift (base X) x - cz w) (lift (base X) x - cz w) : ℂ) := by
  rw [exF, mu_sum, ← sum_neg_distrib]
  refine sum_congr rfl fun x hx => ?_
  rw [mu_sum, ← sum_neg_distrib]
  refine sum_congr rfl fun w hw => ?_
  rw [mu_smul, psibar_mul_psi, mu_neg, mu_psi_psibar, lift_sub_prj hX hx hw]
  ring

theorem mu_cEx (hX : ∀ x ∈ X, 2 * (supNorm (x - base X) + r + 1) < L ^ N) (q1 q2 : ℂ)
    (β : Mono d) : mu (base X) β (∑ M, cEx q1 q2 M • monoSet M X) =
      -∑ x ∈ X, (q1 * (Qpoly β (lift (base X) x) (lift (base X) x) : ℂ) + q2 / 2 *
        ∑ i, ((Qpoly β (lift (base X) x + er i) (lift (base X) x + er i) : ℂ) +
          (Qpoly β (lift (base X) x - er i) (lift (base X) x - er i) : ℂ) -
            2 * (Qpoly β (lift (base X) x) (lift (base X) x) : ℂ))) := by
  rw [sum_cEx, mu_sum, ← sum_neg_distrib]
  refine sum_congr rfl fun x hx => ?_
  rw [lap_prod]
  simp only [mu_sub, mu_smul, mu_sum, mu_add, mu_psi_psibar, lift_add_e hX hx, lift_sub_e hX hx]
  ring

theorem mu_exF_eq (hX : ∀ x ∈ X, 2 * (supNorm (x - base X) + r + 1) < L ^ N) {q : Zd d → ℝ}
    (hrefl : ∀ i w, q (reflZ i w) = q w) (hperm : ∀ σ w, q (permZ σ w) = q w) (i₀ : Fin d)
    (β : Mono d) : mu (base X) β (exF X r q) =
      mu (base X) β (∑ M, cEx (qOne r q : ℂ) (qTwo r q i₀ : ℂ) M • monoSet M X) := by
  rw [mu_exF hX, mu_cEx hX]
  congr 1
  refine sum_congr rfl fun x _ => ?_
  have h := congrArg (fun t : ℝ => (t : ℂ)) (key (r := r) hrefl hperm i₀ β (lift (base X) x))
  push_cast at h
  exact h

theorem locCoef_exF (hX : ∀ x ∈ X, 2 * (supNorm (x - base X) + r + 1) < L ^ N)
    (hne : X.Nonempty) {q : Zd d → ℝ} (hrefl : ∀ i w, q (reflZ i w) = q w)
    (hperm : ∀ σ w, q (permZ σ w) = q w) (i₀ : Fin d) :
    locCoef X (exF X r q) = cEx (qOne r q : ℂ) (qTwo r q i₀ : ℂ) := by
  refine coef_unique (patch_of hX) hne fun β => ?_
  have := mu_LocX (patch_of hX) hne (exF X r q) β
  rw [LocX, LocXY, mu_add, mu_smul, mu_one, mul_zero, zero_add] at this
  rw [this, mu_exF_eq hX hrefl hperm i₀]

/-- **Example (ii) of Section `sec:Loc`**, for an arbitrary reference coordinate `i₀`.
Let `q` be invariant under reflections and permutations of the coordinates and let `X` be
nonempty and small compared with the torus. Then
`Loc_{X,Y} (∑_{x∈X} ∑_w q(w) ψ̄_{x-w}ψ_{x-w}) = ∑_{y∈Y} P_y`. -/
theorem LocXY_exF' (hne : X.Nonempty)
    (hX : ∀ x ∈ X, 2 * (supNorm (x - base X) + r + 1) < L ^ N) {q : Zd d → ℝ}
    (hrefl : ∀ i w, q (reflZ i w) = q w) (hperm : ∀ σ w, q (permZ σ w) = q w) (i₀ : Fin d)
    (Y : Finset (Lam d L N)) :
    LocXY X Y (exF X r q) = ∑ y ∈ Y, exP (qOne r q : ℂ) (qTwo r q i₀ : ℂ) y := by
  rw [LocXY, ε_exF, zero_mul, zero_div, zero_smul, zero_add, locCoef_exF hX hne hrefl hperm i₀,
    sum_cEx]
  exact sum_congr rfl fun y _ => (exP_eq _ _ y).symm

/-- **Example (ii) of Section `sec:Loc`.** Let `q : ℤ^d → ℝ` be supported in the box
`|w|_∞ ≤ r` (the sums run over this box) and invariant under the lattice rotations and
reflections, and let `X` be nonempty with `2(|x - b|_∞ + r + 1) < L^N` for `x ∈ X`. Then for
`F = ∑_{x∈X} ∑_y q(x - y) ψ̄_y ψ_y` and every `Y`,
`Loc_{X,Y} F = ∑_{y∈Y} P_y` with `P_x = q^{(1)} ψ̄_xψ_x + q^{(**)} (½ ψ̄_x(Δψ)_x + ½ (Δψ̄)_xψ_x +
(∇ψ̄)_x(∇ψ)_x)`, `q^{(1)} = ∑_w q(w)`, `q^{(**)} = ∑_w w_1² q(w)`. -/
theorem LocXY_exF (hd : 1 ≤ d) (hne : X.Nonempty)
    (hX : ∀ x ∈ X, 2 * (supNorm (x - base X) + r + 1) < L ^ N) {q : Zd d → ℝ}
    (hrefl : ∀ i w, q (reflZ i w) = q w) (hperm : ∀ σ w, q (permZ σ w) = q w)
    (Y : Finset (Lam d L N)) :
    LocXY X Y (exF X r q) = ∑ y ∈ Y, exP (qOne r q : ℂ) (qTwo r q ⟨0, hd⟩ : ℂ) y :=
  LocXY_exF' hne hX hrefl hperm _ Y

/-- **Example (ii)**, the case `Y = X`: `Loc_X F = ∑_{x∈X} P_x`. -/
theorem LocX_exF (hd : 1 ≤ d) (hne : X.Nonempty)
    (hX : ∀ x ∈ X, 2 * (supNorm (x - base X) + r + 1) < L ^ N) {q : Zd d → ℝ}
    (hrefl : ∀ i w, q (reflZ i w) = q w) (hperm : ∀ σ w, q (permZ σ w) = q w) :
    LocX X (exF X r q) = ∑ x ∈ X, exP (qOne r q : ℂ) (qTwo r q ⟨0, hd⟩ : ℂ) x :=
  LocXY_exF hd hne hX hrefl hperm X

end

end Loc
