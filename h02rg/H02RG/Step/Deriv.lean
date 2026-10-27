import Step.DerivAux
import Step.Theorem

/-!
# Derivatives of the renormalisation group map (Theorem `thm:step`, derivative claims)

Theorem `thm:step` asserts that the maps `Φ_{j+1} : (V_j, K_j) ↦ (u_{j+1}, V_{j+1}, K_{j+1})` are
entire and that all their derivatives are uniformly bounded on `‖V_j‖_j + ‖K_j‖_j ≤ ε`; Section
`sec:flow` uses this in the form of a bound on the linearisation `D_j` at `0` and a Lipschitz
bound for the nonlinear remainder `g_{j+1}`.

## Main results

* Holomorphy (`Step/DerivAux.lean`): `Knext_hol`, `uVnext_hol` (composition with holomorphic
  families is holomorphic), `uVnext_lin` (the coupling constants are even *linear*),
  `DKnext_lin` (the directional derivative is linear in the direction).
* Cauchy estimates (this file), for a bound `‖K_{j+1}‖_{j+1} ≤ M₀` on the ball
  `‖(V, K)‖_j ≤ ε`:
  `DKnext_bound` (`‖D K_{j+1}|_x ẋ‖ ≤ (2M₀/ε) ‖ẋ‖` for `‖x‖ ≤ ε/2`),
  `Knext_lipschitz` (`‖K_{j+1}(x) - K_{j+1}(y)‖ ≤ (16 M₀/ε) ‖x - y‖`),
  `Knext_remainder` (`‖K_{j+1}(x) - K_{j+1}(y) - D K_{j+1}|_0 (x - y)‖ ≤
  C(M₀, ε) max(‖x‖, ‖y‖) ‖x - y‖`), and, from the form of `e:step-K`,
  `DKnext_zero_bound` (`‖D K_{j+1}|_0 (V̇, K̇)‖ ≤ C₀ (L^{-d_+} + A^{-η}) ‖K̇‖`).
* `step_deriv`: the above with the quantifier structure of `Step.step`, and `coupling_deriv`
  for the coupling constants.

## Method

For a connected `U`, a test function `g` with `‖g‖_{Φ_{j+1}} ≤ 1` and a complex line
`t ↦ x + t ẋ`, the scalar function `t ↦ A^{(|𝓑(U)| - 2^d)_+} ⟨K_{j+1}(x + t ẋ)(U), g⟩` is entire
(`Knext_line_hol`, since `⟨·, g⟩` is a linear functional), and the norms are suprema of these
pairings.  The one-variable Cauchy estimates `norm_deriv_le_of_sphere` and `norm_taylor_le`
(Taylor remainders of order one and two) then give the bounds, with the radius of the circle
chosen according to the norms of the points involved (`le_of_forall_radius`,
`le_of_forall_radius₂`, and `le_of_forall_small` for the radius `→ 0` in the bound on `D_j`).

## Differences from the paper

* The paper regards `𝒱^∅ ⊕ 𝒦_j` as a Banach space and uses Fréchet derivatives of all orders.
  Here derivatives are **directional derivatives along complex lines**,
  `DKnext j C V K V̇ K̇ = d/dt K_{j+1}(V + t V̇, K + t K̇)|_{t=0}`, computed coefficient-wise in
  the Grassmann algebra (`derivE`); linearity in `(V̇, K̇)` is proved separately
  (`DKnext_lin`, via two-variable holomorphy).  Only derivatives of order one are formalised,
  together with the second-order information needed in Section `sec:flow` (the Lipschitz bound
  `Knext_remainder` for the remainder `g_{j+1}`, which in the paper follows from bounds on
  second derivatives).  Directions are required to lie in `𝒦_j` (`InK j K̇`), as the
  definition of `(u_{j+1}, V_{j+1})` via `coupOf` only makes sense there.
* "Entire" is formalised as: composition with holomorphic families `e ↦ (V(e), K(e))` on any
  complex normed space, with `K(e) ∈ 𝒦_j`, is coefficient-wise holomorphic (`Knext_hol`,
  `uVnext_hol`).  No auxiliary coordinates are added.
* The norm on pairs is the sum `‖V‖_j + ‖K‖_j` (`xnorm`), as in `thm:step`; Section
  `sec:flow` uses maximum norms, which are equivalent up to a factor `2`.
* `D K_{j+1}|_0 (V̇, 0) = 0` is proved in the form `‖D K_{j+1}|_0 (V̇, 0)‖_{j+1} = 0`.
* The coupling constants `(u_{j+1}, V_{j+1})` are linear in `(V_j, K_j)` (`uVnext_lin`), so their
  derivative is `(u_{j+1}, V_{j+1})(V̇, K̇)` and is bounded by `coupling_bounds`
  (`coupling_deriv`).
-/

namespace Step

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

/-! ### Elementary real lemmas -/

theorem le_zero_of_forall_le_div {X c : ℝ} (_hc : 0 ≤ c) (R₀ : ℝ)
    (h : ∀ R : ℝ, R₀ ≤ R → 0 < R → X ≤ c / R) : X ≤ 0 := by
  by_contra hX
  push Not at hX
  set R := max (max R₀ 1) (2 * c / X + 1)
  have hR1 : 1 ≤ R := (le_max_right _ _).trans (le_max_left _ _)
  have hR0 : 0 < R := by linarith
  have hRc : 2 * c / X + 1 ≤ R := le_max_right _ _
  have := h R ((le_max_left _ _).trans (le_max_left _ _)) hR0
  rw [le_div_iff₀ hR0] at this
  have h2 : 2 * c / X * X = 2 * c := div_mul_cancel₀ _ hX.ne'
  nlinarith

/-- Choosing the radius in a Cauchy estimate for the first derivative. -/
theorem le_of_forall_radius {X c δ ε : ℝ} (hc : 0 ≤ c) (hε : 0 < ε) (hδ : 0 ≤ δ)
    (h : ∀ R : ℝ, 0 < R → R * δ ≤ ε / 2 → X ≤ c / R) : X ≤ 2 * c * δ / ε := by
  rcases hδ.eq_or_lt with rfl | hδ
  · simpa using le_zero_of_forall_le_div hc 0 fun R _ hR => h R hR (by simp; positivity)
  · have hR : 0 < ε / (2 * δ) := by positivity
    have := h _ hR (by field_simp; rfl)
    calc X ≤ c / (ε / (2 * δ)) := this
      _ = 2 * c * δ / ε := by field_simp

/-- Choosing the radius (at least `2`) in a Cauchy estimate for a Taylor remainder. -/
theorem le_of_forall_radius₂ {X c B m ε : ℝ} (hc : 0 ≤ c) (hB : 0 ≤ B) (hε : 0 < ε) (hm : 0 ≤ m)
    (h : ∀ R : ℝ, 2 ≤ R → R * m ≤ ε / 2 → X ≤ c / R) (hX : X ≤ B) :
    X ≤ 4 * (c + B) * m / ε := by
  rcases hm.eq_or_lt with rfl | hm
  · simpa using le_zero_of_forall_le_div hc 2 fun R hR _ => h R hR (by simp; positivity)
  · by_cases hm4 : m ≤ ε / 4
    · have hR : 2 ≤ ε / (2 * m) := by rw [le_div_iff₀ (by positivity)]; linarith
      have := h _ hR (by field_simp; rfl)
      calc X ≤ c / (ε / (2 * m)) := this
        _ = 2 * c * m / ε := by field_simp
        _ ≤ 4 * (c + B) * m / ε := div_le_div_of_nonneg_right (by nlinarith) hε.le
    · push Not at hm4
      calc X ≤ B := hX
        _ ≤ 4 * B * m / ε := by rw [le_div_iff₀ hε]; nlinarith
        _ ≤ 4 * (c + B) * m / ε := by gcongr; linarith

/-- Letting the radius tend to `0`. -/
theorem le_of_forall_small {X a b R₀ : ℝ} (hR₀ : 0 < R₀)
    (h : ∀ R : ℝ, 0 < R → R ≤ R₀ → X ≤ a + b * R) : X ≤ a := by
  by_contra hX
  push Not at hX
  rcases le_or_gt b 0 with hb | hb
  · have := h R₀ hR₀ le_rfl
    nlinarith
  · set R := min R₀ ((X - a) / (2 * b))
    have hR : 0 < R := lt_min hR₀ (by apply div_pos <;> linarith)
    have h1 := h R hR (min_le_left _ _)
    have h2 : b * R ≤ (X - a) / 2 := by
      calc b * R ≤ b * ((X - a) / (2 * b)) := by gcongr; exact min_le_right _ _
        _ = (X - a) / 2 := by field_simp
    linarith

/-! ### Norms on `𝒱^∅ ⊕ 𝒦_j` -/

/-- `‖(V, K)‖_j = ‖V‖_j + ‖K‖_j`. -/
def xnorm (j : ℕ) (ℓ A : ℝ) (V : Vcoup) (K : Act d L N) : ENNReal :=
  Vnorm (d := d) (L := L) (N := N) j ℓ V + Knorm j ℓ A K

theorem Vnorm_smul (j : ℕ) (ℓ : ℝ) (c : ℂ) (V : Vcoup) :
    Vnorm (d := d) (L := L) (N := N) j ℓ (c • V) =
      ENNReal.ofReal ‖c‖ * Vnorm (d := d) (L := L) (N := N) j ℓ V := by
  unfold Vnorm
  simp only [eval_smul, Tj_smul', ENNReal.mul_iSup]

theorem Vnorm_add_le (j : ℕ) (ℓ : ℝ) (V W : Vcoup) :
    Vnorm (d := d) (L := L) (N := N) j ℓ (V + W) ≤
      Vnorm (d := d) (L := L) (N := N) j ℓ V + Vnorm (d := d) (L := L) (N := N) j ℓ W := by
  refine iSup₂_le fun b hb => ?_
  rw [eval_add]
  exact (tNorm_add_le _ _).trans (add_le_add (le_iSup₂ (f := fun b _ =>
    Tj d (L : ℝ) j ℓ (V.eval (blockSet (L := L) (N := N) j b))) b hb)
    (le_iSup₂ (f := fun b _ => Tj d (L : ℝ) j ℓ (W.eval (blockSet (L := L) (N := N) j b))) b hb))

theorem Knorm_smul (j : ℕ) (ℓ A : ℝ) (c : ℂ) (K : Act d L N) :
    Knorm j ℓ A (c • K) = ENNReal.ofReal ‖c‖ * Knorm j ℓ A K := by
  unfold Knorm
  simp only [Pi.smul_apply, Subalgebra.coe_smul, Tj_smul', ENNReal.mul_iSup]
  congr 1; funext X; congr 1; funext _
  ring

theorem Knorm_add_le (j : ℕ) (ℓ A : ℝ) (K K' : Act d L N) :
    Knorm j ℓ A (K + K') ≤ Knorm j ℓ A K + Knorm j ℓ A K' := by
  refine iSup₂_le fun X hX => ?_
  have hX' : IsConn j X := by simpa [connSets] using hX
  exact (wnorm_add_le j ℓ A X (K X) (K' X)).trans
    (add_le_add (wnorm_le_Knorm hX') (wnorm_le_Knorm hX'))

theorem Knorm_zero (j : ℕ) (ℓ A : ℝ) : Knorm j ℓ A (0 : Act d L N) = 0 := by
  unfold Knorm
  simp [Tj_zero]

theorem xnorm_smul (j : ℕ) (ℓ A : ℝ) (c : ℂ) (V : Vcoup) (K : Act d L N) :
    xnorm j ℓ A (c • V) (c • K) = ENNReal.ofReal ‖c‖ * xnorm j ℓ A V K := by
  simp only [xnorm, Vnorm_smul, Knorm_smul, mul_add]

theorem xnorm_add_le (j : ℕ) (ℓ A : ℝ) (V W : Vcoup) (K K' : Act d L N) :
    xnorm j ℓ A (V + W) (K + K') ≤ xnorm j ℓ A V K + xnorm j ℓ A W K' := by
  unfold xnorm
  calc _ ≤ (Vnorm (d := d) (L := L) (N := N) j ℓ V + Vnorm (d := d) (L := L) (N := N) j ℓ W) +
        (Knorm j ℓ A K + Knorm j ℓ A K') :=
        add_le_add (Vnorm_add_le _ _ _ _) (Knorm_add_le _ _ _ _ _)
    _ = _ := by ring

theorem xnorm_line_le (j : ℕ) (ℓ A : ℝ) (V V' : Vcoup) (K K' : Act d L N) (t : ℂ) :
    xnorm j ℓ A (V + t • V') (K + t • K') ≤
      xnorm j ℓ A V K + ENNReal.ofReal ‖t‖ * xnorm j ℓ A V' K' :=
  (xnorm_add_le _ _ _ _ _ _ _).trans (by rw [xnorm_smul])

theorem xnorm_zero (j : ℕ) (ℓ A : ℝ) : xnorm j ℓ A (0 : Vcoup) (0 : Act d L N) = 0 := by
  have := xnorm_smul j ℓ A (0 : ℂ) (0 : Vcoup) (0 : Act d L N)
  simpa using this

theorem Vnorm_ne_top {j : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (V : Vcoup) :
    Vnorm (d := d) (L := L) (N := N) j ℓ V ≠ ⊤ := by
  have hh : (0 : ℝ) < (L : ℝ) ^ j := pow_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L))) j
  have hs : ∑ b ∈ blockIdx (d := d) (L := L) (N := N) j,
      Tj d (L : ℝ) j ℓ (V.eval (blockSet (L := L) (N := N) j b)) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun b _ => tNorm_ne_top (E := Dir d) (p := pPhi d) hh hℓ _
  refine ne_top_of_le_ne_top hs (iSup₂_le fun b hb => ?_)
  exact single_le_sum (f := fun (b : Fin d → ℕ) =>
    Tj d (L : ℝ) j ℓ (V.eval (blockSet (L := L) (N := N) j b))) (fun _ _ => zero_le) hb

theorem Knorm_ne_top {j : ℕ} {ℓ A : ℝ} (hℓ : 0 < ℓ) (K : Act d L N) : Knorm j ℓ A K ≠ ⊤ := by
  have hh : (0 : ℝ) < (L : ℝ) ^ j := pow_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L))) j
  have hs : ∑ X ∈ connSets (L := L) (N := N) j, ENNReal.ofReal (A ^ (nb j X - 2 ^ d)) *
      Tj d (L : ℝ) j ℓ (K X : Alg d L N) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun X _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (tNorm_ne_top (E := Dir d) (p := pPhi d) hh hℓ _)
  refine ne_top_of_le_ne_top hs (iSup₂_le fun X hX => ?_)
  exact single_le_sum (f := fun (X : Finset (Lam d L N)) => ENNReal.ofReal (A ^ (nb j X - 2 ^ d)) *
    Tj d (L : ℝ) j ℓ (K X : Alg d L N)) (fun _ _ => zero_le) hX

theorem xnorm_ne_top {j : ℕ} {ℓ A : ℝ} (hℓ : 0 < ℓ) (V : Vcoup) (K : Act d L N) :
    xnorm j ℓ A V K ≠ ⊤ := ENNReal.add_ne_top.2 ⟨Vnorm_ne_top hℓ V, Knorm_ne_top hℓ K⟩

theorem InK.sub {j : ℕ} {K K' : Act d L N} (hK : InK j K) (hK' : InK j K') : InK j (K - K') := by
  simpa [sub_eq_add_neg] using hK.lin hK' 1 (-1)

/-! ### Weighted norms and pairings -/

/-- The weight `A^{(|𝓑_j(U)| - 2^d)_+}`. -/
abbrev wt (j : ℕ) (A : ℝ) (U : Finset (Lam d L N)) : ℝ := A ^ (nb j U - 2 ^ d)

theorem wpair_le_wnorm {j : ℕ} {ℓ A : ℝ} (hℓ : 0 < ℓ) (hA : 0 ≤ A) (U : Finset (Lam d L N))
    (F : EvR (Lam d L N)) {g : TestFn (Lam d L N)} (hg : Phij (L : ℝ) j ℓ g ≤ 1) :
    wt j A U * ‖pair (F : Alg d L N) g‖ ≤ (wnorm j ℓ A U F).toReal := by
  have hh : (0 : ℝ) < (L : ℝ) ^ j := pow_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L))) j
  have hw : 0 ≤ wt j A U := pow_nonneg hA _
  unfold wnorm
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hw]
  gcongr
  simpa using abs_pair_le hh hℓ (F : Alg d L N) zero_le_one (by simpa using hg)

theorem wnorm_le_of_wpair {j : ℕ} {ℓ A B : ℝ} (hA : 0 < A) (U : Finset (Lam d L N))
    (F : EvR (Lam d L N))
    (h : ∀ g : TestFn (Lam d L N), Phij (L : ℝ) j ℓ g ≤ 1 → wt j A U * ‖pair (F : Alg d L N) g‖ ≤ B) :
    wnorm j ℓ A U F ≤ ENNReal.ofReal B := by
  have hw : 0 < wt j A U := pow_pos hA _
  unfold wnorm
  have h2 : Tj d (L : ℝ) j ℓ (F : Alg d L N) ≤ ENNReal.ofReal (B / wt j A U) :=
    tNorm_le fun g hg => by rw [le_div_iff₀ hw, mul_comm]; exact h g hg
  calc ENNReal.ofReal (wt j A U) * Tj d (L : ℝ) j ℓ (F : Alg d L N)
      ≤ ENNReal.ofReal (wt j A U) * ENNReal.ofReal (B / wt j A U) := by gcongr
    _ = ENNReal.ofReal B := by
      rw [← ENNReal.ofReal_mul hw.le, mul_div_cancel₀ _ hw.ne']

theorem Knorm_le_of_wnorm {j : ℕ} {ℓ A : ℝ} {K : Act d L N} {B : ENNReal}
    (h : ∀ U, IsConn j U → wnorm j ℓ A U (K U) ≤ B) : Knorm j ℓ A K ≤ B :=
  iSup₂_le fun U hU => h U (by simpa [connSets] using hU)

theorem Knorm_le_of_wpair {j : ℕ} {ℓ A B : ℝ} (hA : 0 < A) {K : Act d L N}
    (h : ∀ U, IsConn j U → ∀ g : TestFn (Lam d L N), Phij (L : ℝ) j ℓ g ≤ 1 →
      wt j A U * ‖pair (K U : Alg d L N) g‖ ≤ B) : Knorm j ℓ A K ≤ ENNReal.ofReal B :=
  Knorm_le_of_wnorm fun U hU => wnorm_le_of_wpair hA U _ (h U hU)

theorem wpair_le_of_Knorm {j : ℕ} {ℓ A B : ℝ} (hℓ : 0 < ℓ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {K : Act d L N} (hK : Knorm j ℓ A K ≤ ENNReal.ofReal B) {U : Finset (Lam d L N)}
    (hU : IsConn j U) {g : TestFn (Lam d L N)} (hg : Phij (L : ℝ) j ℓ g ≤ 1) :
    wt j A U * ‖pair (K U : Alg d L N) g‖ ≤ B := by
  refine (wpair_le_wnorm hℓ hA U (K U) hg).trans ?_
  have h1 := (wnorm_le_Knorm (A := A) (ℓ := ℓ) (K := K) hU).trans hK
  exact ENNReal.toReal_le_of_le_ofReal hB h1


/-! ### Cauchy estimates for `K_{j+1}` -/

section Cauchy

variable {j : ℕ} {ℓ₀ A ε M₀ : ℝ} {C : Matrix (Lam d L N) (Lam d L N) ℝ}

theorem toReal_xnorm {j : ℕ} {ℓ A : ℝ} (hℓ : 0 < ℓ) (V : Vcoup) (K : Act d L N) :
    xnorm j ℓ A V K = ENNReal.ofReal (xnorm j ℓ A V K).toReal :=
  (ENNReal.ofReal_toReal (xnorm_ne_top hℓ V K)).symm

theorem xnorm_line_le_ofReal {j : ℕ} {ℓ A : ℝ} (hℓ : 0 < ℓ) {V V' : Vcoup} {K K' : Act d L N}
    {r ε : ℝ} (hx : xnorm j ℓ A V K ≤ ENNReal.ofReal (ε / 2)) (hr : 0 ≤ r) (ζ : ℂ) (hζ : ‖ζ‖ = r)
    (hrδ : r * (xnorm j ℓ A V' K').toReal ≤ ε / 2) :
    xnorm j ℓ A (V + ζ • V') (K + ζ • K') ≤ ENNReal.ofReal ε := by
  refine (xnorm_line_le _ _ _ _ _ _ _ ζ).trans ?_
  rw [hζ, toReal_xnorm hℓ V' K', ← ENNReal.ofReal_mul hr]
  refine (add_le_add hx le_rfl).trans ?_
  have h0 := mul_nonneg hr (ENNReal.toReal_nonneg (a := xnorm j ℓ A V' K'))
  rw [← ENNReal.ofReal_add (by linarith) h0]
  exact ENNReal.ofReal_le_ofReal (by linarith)

theorem pair_sub (F G : Alg d L N) (g : TestFn (Lam d L N)) :
    pair (F - G) g = pair F g - pair G g := map_sub (pairL g) F G

theorem pair_neg (F : Alg d L N) (g : TestFn (Lam d L N)) : pair (-F) g = -pair F g :=
  map_neg (pairL g) F

theorem norm_wpair (w : ℝ) (hw : 0 ≤ w) (z : ℂ) : ‖(w : ℂ) * z‖ = w * ‖z‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw]

/-- **First derivative bound**: on the half ball `‖(V, K)‖_j ≤ ε/2`,
`‖D_{(V̇,K̇)} K_{j+1}|_{(V,K)}‖_{j+1} ≤ (2 M₀/ε) ‖(V̇, K̇)‖_j`, where `M₀` bounds `‖K_{j+1}‖_{j+1}` on
the ball `‖(V, K)‖_j ≤ ε`. -/
theorem DKnext_bound (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hj : j < N) (hℓ₀ : 0 < ℓ₀)
    (hA : 1 ≤ A) (hC : GoodCov j ℓ₀ C) (hε : 0 < ε) (hM₀ : 0 ≤ M₀)
    (hM : ∀ (V : Vcoup) (K : Act d L N), InK j K → xnorm j (ellj d L ℓ₀ j) A V K ≤ ENNReal.ofReal ε →
      Knorm (j + 1) (ellj d L ℓ₀ (j + 1)) A (Knext j C V K) ≤ ENNReal.ofReal M₀)
    {V V' : Vcoup} {K K' : Act d L N} (hK : InK j K) (hK' : InK j K')
    (hx : xnorm j (ellj d L ℓ₀ j) A V K ≤ ENNReal.ofReal (ε / 2)) :
    Knorm (j + 1) (ellj d L ℓ₀ (j + 1)) A (DKnext j C V K V' K') ≤
      ENNReal.ofReal (2 * M₀ / ε) * xnorm j (ellj d L ℓ₀ j) A V' K' := by
  have hℓ := ellj_pos (d := d) (L := L) (Nat.cast_pos.2 (NeZero.pos L)) hℓ₀ j
  have hℓ' := ellj_pos (d := d) (L := L) (Nat.cast_pos.2 (NeZero.pos L)) hℓ₀ (j + 1)
  set δ := (xnorm j (ellj d L ℓ₀ j) A V' K').toReal with hδdef
  have hδ0 : 0 ≤ δ := ENNReal.toReal_nonneg
  have hA0 : 0 < A := by linarith
  rw [toReal_xnorm hℓ V' K', ← hδdef, ← ENNReal.ofReal_mul (by positivity)]
  refine Knorm_le_of_wpair hA0 fun U hU g hg => ?_
  have hF := Knext_line_hol hd hL hj hC.covInv hC.symm' V V' hK hK' U
  have hw : 0 ≤ wt (j + 1) A U := pow_nonneg hA0.le _
  set ψ : ℂ → ℂ := fun t => (wt (j + 1) A U : ℂ) *
    pair (Knext j C (V + t • V') (K + t • K') U : Alg d L N) g with hψdef
  have hl : Differentiable ℂ fun t : ℂ =>
      pair (Knext j C (V + t • V') (K + t • K') U : Alg d L N) g := hF.lin (pairL g)
  have hψ : Differentiable ℂ ψ := hl.const_mul _
  have hd0 : deriv ψ 0 = (wt (j + 1) A U : ℂ) *
      pair (DKnext j C V K V' K' U : Alg d L N) g := by
    rw [pair_DKnext hd hL hj hC.covInv hC.symm' V V' hK hK' U g]
    exact deriv_const_mul _ (hl 0)
  rw [← norm_wpair _ hw, ← hd0]
  have key := le_of_forall_radius hM₀ hε hδ0 fun R hR hRδ =>
    norm_deriv_le_of_sphere hψ hR fun ζ hζ => by
      rw [hψdef, norm_wpair _ hw]
      exact wpair_le_of_Knorm hℓ' hA0.le hM₀ (hM _ _ (hK.add (hK'.smul ζ))
        (xnorm_line_le_ofReal hℓ hx hR.le ζ hζ hRδ)) hU hg
  calc _ ≤ 2 * M₀ * δ / ε := key
    _ = 2 * M₀ / ε * δ := by ring

theorem DKnext_bound_pair (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hj : j < N) (hℓ₀ : 0 < ℓ₀)
    (hA : 1 ≤ A) (hC : GoodCov j ℓ₀ C) (hε : 0 < ε) (hM₀ : 0 ≤ M₀)
    (hM : ∀ (V : Vcoup) (K : Act d L N), InK j K → xnorm j (ellj d L ℓ₀ j) A V K ≤ ENNReal.ofReal ε →
      Knorm (j + 1) (ellj d L ℓ₀ (j + 1)) A (Knext j C V K) ≤ ENNReal.ofReal M₀)
    {V V' : Vcoup} {K K' : Act d L N} (hK : InK j K) (hK' : InK j K')
    (hx : xnorm j (ellj d L ℓ₀ j) A V K ≤ ENNReal.ofReal (ε / 2))
    {U : Finset (Lam d L N)} (hU : IsConn (j + 1) U) {g : TestFn (Lam d L N)}
    (hg : Phij (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1)) g ≤ 1) :
    wt (j + 1) A U * ‖pair (DKnext j C V K V' K' U : Alg d L N) g‖ ≤
      2 * M₀ / ε * (xnorm j (ellj d L ℓ₀ j) A V' K').toReal := by
  have hℓ := ellj_pos (d := d) (L := L) (Nat.cast_pos.2 (NeZero.pos L)) hℓ₀ j
  have hℓ' := ellj_pos (d := d) (L := L) (Nat.cast_pos.2 (NeZero.pos L)) hℓ₀ (j + 1)
  have hA0 : 0 < A := by linarith
  have h := DKnext_bound hd hL hj hℓ₀ hA hC hε hM₀ hM (V' := V') hK hK' hx
  rw [toReal_xnorm hℓ V' K', ← ENNReal.ofReal_mul (by positivity)] at h
  exact wpair_le_of_Knorm hℓ' hA0.le (by positivity) h hU hg

/-- **Lipschitz bound** on the half ball:
`‖K_{j+1}(x) - K_{j+1}(y)‖_{j+1} ≤ (16 M₀/ε) ‖x - y‖_j`. -/
theorem Knext_lipschitz (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hj : j < N) (hℓ₀ : 0 < ℓ₀)
    (hA : 1 ≤ A) (hC : GoodCov j ℓ₀ C) (hε : 0 < ε) (hM₀ : 0 ≤ M₀)
    (hM : ∀ (V : Vcoup) (K : Act d L N), InK j K → xnorm j (ellj d L ℓ₀ j) A V K ≤ ENNReal.ofReal ε →
      Knorm (j + 1) (ellj d L ℓ₀ (j + 1)) A (Knext j C V K) ≤ ENNReal.ofReal M₀)
    {V₁ V₂ : Vcoup} {K₁ K₂ : Act d L N} (hK₁ : InK j K₁) (hK₂ : InK j K₂)
    (hx₁ : xnorm j (ellj d L ℓ₀ j) A V₁ K₁ ≤ ENNReal.ofReal (ε / 2))
    (hx₂ : xnorm j (ellj d L ℓ₀ j) A V₂ K₂ ≤ ENNReal.ofReal (ε / 2)) :
    Knorm (j + 1) (ellj d L ℓ₀ (j + 1)) A (fun U => Knext j C V₁ K₁ U - Knext j C V₂ K₂ U) ≤
      ENNReal.ofReal (16 * M₀ / ε) * xnorm j (ellj d L ℓ₀ j) A (V₁ - V₂) (K₁ - K₂) := by
  have hℓ := ellj_pos (d := d) (L := L) (Nat.cast_pos.2 (NeZero.pos L)) hℓ₀ j
  have hℓ' := ellj_pos (d := d) (L := L) (Nat.cast_pos.2 (NeZero.pos L)) hℓ₀ (j + 1)
  set δ := (xnorm j (ellj d L ℓ₀ j) A (V₁ - V₂) (K₁ - K₂)).toReal with hδdef
  have hδ0 : 0 ≤ δ := ENNReal.toReal_nonneg
  have hA0 : 0 < A := by linarith
  have hK₁₂ := hK₁.sub hK₂
  rw [toReal_xnorm hℓ (V₁ - V₂) (K₁ - K₂), ← hδdef, ← ENNReal.ofReal_mul (by positivity)]
  refine Knorm_le_of_wpair hA0 fun U hU g hg => ?_
  have hF := Knext_line_hol hd hL hj hC.covInv hC.symm' V₂ (V₁ - V₂) hK₂ hK₁₂ U
  have hw : 0 ≤ wt (j + 1) A U := pow_nonneg hA0.le _
  set σ : ℂ → ℂ := fun t => (wt (j + 1) A U : ℂ) *
    pair (Knext j C (V₂ + t • (V₁ - V₂)) (K₂ + t • (K₁ - K₂)) U : Alg d L N) g with hσdef
  have hσ : Differentiable ℂ σ := (hF.lin (pairL g)).const_mul _
  have hσ1 : σ 1 = (wt (j + 1) A U : ℂ) * pair (Knext j C V₁ K₁ U : Alg d L N) g := by
    simp [hσdef]
  have hσ0 : σ 0 = (wt (j + 1) A U : ℂ) * pair (Knext j C V₂ K₂ U : Alg d L N) g := by
    simp [hσdef]
  have hbd : ∀ (V : Vcoup) (K : Act d L N), InK j K →
      xnorm j (ellj d L ℓ₀ j) A V K ≤ ENNReal.ofReal ε →
      ‖(wt (j + 1) A U : ℂ) * pair (Knext j C V K U : Alg d L N) g‖ ≤ M₀ := fun V K hK hx => by
    rw [norm_wpair _ hw]
    exact wpair_le_of_Knorm hℓ' hA0.le hM₀ (hM V K hK hx) hU hg
  have hε2 : ENNReal.ofReal (ε / 2) ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal (by linarith)
  have hX : ‖σ 1 - σ 0‖ = wt (j + 1) A U *
      ‖pair (((fun U => Knext j C V₁ K₁ U - Knext j C V₂ K₂ U) U : EvR (Lam d L N)) :
        Alg d L N) g‖ := by
    rw [hσ1, hσ0, ← mul_sub, norm_wpair _ hw]
    congr 2
    simp only [Subalgebra.coe_sub, pair_sub]
  rw [← hX]
  have key := le_of_forall_radius₂ (c := 2 * M₀) (B := 2 * M₀) (by positivity) (by positivity)
    hε hδ0 (fun R hR hRδ => by
      have h1 := (norm_taylor_le hσ (by linarith : (1 : ℝ) < R) fun ζ hζ =>
        hbd _ _ (hK₂.add (hK₁₂.smul ζ))
          (xnorm_line_le_ofReal hℓ hx₂ (by linarith) ζ hζ hRδ)).1
      refine h1.trans ?_
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith)
    ((norm_sub_le _ _).trans (by
      rw [hσ1, hσ0]
      linarith [hbd V₁ K₁ hK₁ (hx₁.trans hε2), hbd V₂ K₂ hK₂ (hx₂.trans hε2)]))
  calc _ ≤ 4 * (2 * M₀ + 2 * M₀) * δ / ε := key
    _ = 16 * M₀ / ε * δ := by ring


theorem Knext_lipschitz_pair (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hj : j < N) (hℓ₀ : 0 < ℓ₀)
    (hA : 1 ≤ A) (hC : GoodCov j ℓ₀ C) (hε : 0 < ε) (hM₀ : 0 ≤ M₀)
    (hM : ∀ (V : Vcoup) (K : Act d L N), InK j K → xnorm j (ellj d L ℓ₀ j) A V K ≤ ENNReal.ofReal ε →
      Knorm (j + 1) (ellj d L ℓ₀ (j + 1)) A (Knext j C V K) ≤ ENNReal.ofReal M₀)
    {V₁ V₂ : Vcoup} {K₁ K₂ : Act d L N} (hK₁ : InK j K₁) (hK₂ : InK j K₂)
    (hx₁ : xnorm j (ellj d L ℓ₀ j) A V₁ K₁ ≤ ENNReal.ofReal (ε / 2))
    (hx₂ : xnorm j (ellj d L ℓ₀ j) A V₂ K₂ ≤ ENNReal.ofReal (ε / 2))
    {U : Finset (Lam d L N)} (hU : IsConn (j + 1) U) {g : TestFn (Lam d L N)}
    (hg : Phij (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1)) g ≤ 1) :
    wt (j + 1) A U * ‖pair (Knext j C V₁ K₁ U : Alg d L N) g -
        pair (Knext j C V₂ K₂ U : Alg d L N) g‖ ≤
      16 * M₀ / ε * (xnorm j (ellj d L ℓ₀ j) A (V₁ - V₂) (K₁ - K₂)).toReal := by
  have hℓ := ellj_pos (d := d) (L := L) (Nat.cast_pos.2 (NeZero.pos L)) hℓ₀ j
  have hℓ' := ellj_pos (d := d) (L := L) (Nat.cast_pos.2 (NeZero.pos L)) hℓ₀ (j + 1)
  have hA0 : 0 < A := by linarith
  have h := Knext_lipschitz hd hL hj hℓ₀ hA hC hε hM₀ hM hK₁ hK₂ hx₁ hx₂
  rw [toReal_xnorm hℓ (V₁ - V₂) (K₁ - K₂), ← ENNReal.ofReal_mul (by positivity)] at h
  have := wpair_le_of_Knorm hℓ' hA0.le (by positivity) h hU hg
  simpa only [Subalgebra.coe_sub, pair_sub] using this

/-- The constant of the remainder bound `Knext_remainder`. -/
def remConst (M₀ ε : ℝ) : ℝ := 4 * (3 * (16 * M₀ / ε) + 2 * M₀ / ε) / ε

/-- **Lipschitz bound for the nonlinear remainder**: on the half ball,
`‖K_{j+1}(x) - K_{j+1}(y) - D K_{j+1}|_0 (x - y)‖_{j+1} ≤ C max(‖x‖_j, ‖y‖_j) ‖x - y‖_j`. -/
theorem Knext_remainder (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hj : j < N) (hℓ₀ : 0 < ℓ₀)
    (hA : 1 ≤ A) (hC : GoodCov j ℓ₀ C) (hε : 0 < ε) (hM₀ : 0 ≤ M₀)
    (hM : ∀ (V : Vcoup) (K : Act d L N), InK j K → xnorm j (ellj d L ℓ₀ j) A V K ≤ ENNReal.ofReal ε →
      Knorm (j + 1) (ellj d L ℓ₀ (j + 1)) A (Knext j C V K) ≤ ENNReal.ofReal M₀)
    {V₁ V₂ : Vcoup} {K₁ K₂ : Act d L N} (hK₁ : InK j K₁) (hK₂ : InK j K₂)
    (hx₁ : xnorm j (ellj d L ℓ₀ j) A V₁ K₁ ≤ ENNReal.ofReal (ε / 2))
    (hx₂ : xnorm j (ellj d L ℓ₀ j) A V₂ K₂ ≤ ENNReal.ofReal (ε / 2)) :
    Knorm (j + 1) (ellj d L ℓ₀ (j + 1)) A (fun U => Knext j C V₁ K₁ U - Knext j C V₂ K₂ U -
        DKnext j C 0 0 (V₁ - V₂) (K₁ - K₂) U) ≤
      ENNReal.ofReal (remConst M₀ ε) *
        max (xnorm j (ellj d L ℓ₀ j) A V₁ K₁) (xnorm j (ellj d L ℓ₀ j) A V₂ K₂) *
        xnorm j (ellj d L ℓ₀ j) A (V₁ - V₂) (K₁ - K₂) := by
  have hℓ := ellj_pos (d := d) (L := L) (Nat.cast_pos.2 (NeZero.pos L)) hℓ₀ j
  have hℓ' := ellj_pos (d := d) (L := L) (Nat.cast_pos.2 (NeZero.pos L)) hℓ₀ (j + 1)
  set ℓj := ellj d L ℓ₀ j with hℓjdef
  set r₁ := (xnorm j ℓj A V₁ K₁).toReal with hr₁def
  set r₂ := (xnorm j ℓj A V₂ K₂).toReal with hr₂def
  set δ := (xnorm j ℓj A (V₁ - V₂) (K₁ - K₂)).toReal with hδdef
  set m := max r₁ r₂ with hmdef
  have hr₁0 : 0 ≤ r₁ := ENNReal.toReal_nonneg
  have hδ0 : 0 ≤ δ := ENNReal.toReal_nonneg
  have hm0 : 0 ≤ m := hr₁0.trans (le_max_left _ _)
  have hA0 : 0 < A := by linarith
  have hK₁₂ := hK₁.sub hK₂
  have h0K := InK.zero (d := d) (L := L) (N := N) j
  have hC₂0 : 0 ≤ (16 * M₀ / ε) := by positivity
  have hCa0 : 0 ≤ (2 * M₀ / ε) := by positivity
  have hrc : 0 ≤ remConst M₀ ε := by unfold remConst; positivity
  have hRHS : ENNReal.ofReal (remConst M₀ ε) * max (xnorm j ℓj A V₁ K₁) (xnorm j ℓj A V₂ K₂) *
      xnorm j ℓj A (V₁ - V₂) (K₁ - K₂) = ENNReal.ofReal (remConst M₀ ε * m * δ) := by
    have e1 : xnorm j ℓj A V₁ K₁ = ENNReal.ofReal r₁ := toReal_xnorm hℓ V₁ K₁
    have e2 : xnorm j ℓj A V₂ K₂ = ENNReal.ofReal r₂ := toReal_xnorm hℓ V₂ K₂
    have e3 : xnorm j ℓj A (V₁ - V₂) (K₁ - K₂) = ENNReal.ofReal δ := toReal_xnorm hℓ _ _
    rw [e1, e2, e3, ← ENNReal.ofReal_max, ENNReal.ofReal_mul (mul_nonneg hrc hm0),
      ENNReal.ofReal_mul hrc]
  rw [hRHS]
  refine Knorm_le_of_wpair hA0 fun U hU g hg => ?_
  have hF₁ := Knext_line_hol hd hL hj hC.covInv hC.symm' 0 V₁ h0K hK₁ U
  have hF₂ := Knext_line_hol hd hL hj hC.covInv hC.symm' 0 V₂ h0K hK₂ U
  have hl₁ : Differentiable ℂ fun t : ℂ =>
      pair (Knext j C (0 + t • V₁) (0 + t • K₁) U : Alg d L N) g := hF₁.lin (pairL g)
  have hl₂ : Differentiable ℂ fun t : ℂ =>
      pair (Knext j C (0 + t • V₂) (0 + t • K₂) U : Alg d L N) g := hF₂.lin (pairL g)
  have hw : 0 ≤ wt (j + 1) A U := pow_nonneg hA0.le _
  set w : ℂ := (wt (j + 1) A U : ℂ) with hwdef
  set ρ : ℂ → ℂ := fun t => w * (pair (Knext j C (0 + t • V₁) (0 + t • K₁) U : Alg d L N) g -
    pair (Knext j C (0 + t • V₂) (0 + t • K₂) U : Alg d L N) g) with hρdef
  have hρ : Differentiable ℂ ρ := (hl₁.sub hl₂).const_mul _
  have hρ1 : ρ 1 = w * (pair (Knext j C V₁ K₁ U : Alg d L N) g -
      pair (Knext j C V₂ K₂ U : Alg d L N) g) := by simp [hρdef]
  have hρ0 : ρ 0 = 0 := by simp [hρdef]
  have hlin := DKnext_lin hd hL hj hC.covInv hC.symm' 0 V₁ V₂ h0K hK₁ hK₂ 1 (-1)
  have eV : V₁ - V₂ = (1 : ℂ) • V₁ + (-1 : ℂ) • V₂ := by simp [sub_eq_add_neg]
  have eK : K₁ - K₂ = (1 : ℂ) • K₁ + (-1 : ℂ) • K₂ := by simp [sub_eq_add_neg]
  have hρd : deriv ρ 0 = w * pair (DKnext j C 0 0 (V₁ - V₂) (K₁ - K₂) U : Alg d L N) g := by
    have h : HasDerivAt ρ (w * (deriv (fun t : ℂ =>
        pair (Knext j C (0 + t • V₁) (0 + t • K₁) U : Alg d L N) g) 0 - deriv (fun t : ℂ =>
        pair (Knext j C (0 + t • V₂) (0 + t • K₂) U : Alg d L N) g) 0)) 0 :=
      ((hl₁ 0).hasDerivAt.sub (hl₂ 0).hasDerivAt).const_mul w
    rw [h.deriv, ← pair_DKnext hd hL hj hC.covInv hC.symm' 0 V₁ h0K hK₁ U g,
      ← pair_DKnext hd hL hj hC.covInv hC.symm' 0 V₂ h0K hK₂ U g, eV, eK, hlin]
    congr 1
    simp only [Pi.add_apply, Subalgebra.coe_add, one_smul, neg_one_smul, pair_add]
    rw [Pi.neg_apply, NegMemClass.coe_neg, pair_neg, sub_eq_add_neg]
  have hX : ‖ρ 1 - ρ 0 - deriv ρ 0‖ = wt (j + 1) A U *
      ‖pair (((fun U => Knext j C V₁ K₁ U - Knext j C V₂ K₂ U -
        DKnext j C 0 0 (V₁ - V₂) (K₁ - K₂) U) U : EvR (Lam d L N)) : Alg d L N) g‖ := by
    rw [hρ1, hρ0, hρd, sub_zero, ← mul_sub, norm_wpair _ hw]
    congr 2
    simp only [Subalgebra.coe_sub, pair_sub]
  rw [← hX]
  -- the Lipschitz bound, in pairing form
  have hLip : ∀ {V V' : Vcoup} {K K' : Act d L N}, InK j K → InK j K' →
      xnorm j ℓj A V K ≤ ENNReal.ofReal (ε / 2) → xnorm j ℓj A V' K' ≤ ENNReal.ofReal (ε / 2) →
      ‖w * (pair (Knext j C V K U : Alg d L N) g - pair (Knext j C V' K' U : Alg d L N) g)‖ ≤
        (16 * M₀ / ε) * (xnorm j ℓj A (V - V') (K - K')).toReal := fun {V V' K K'} hK hK' hx hx' => by
    rw [norm_wpair _ hw]
    exact Knext_lipschitz_pair hd hL hj hℓ₀ hA hC hε hM₀ hM hK hK' hx hx' hU hg
  have hε2 : (0 : ℝ) ≤ ε / 2 := by linarith
  have hc0 : 0 ≤ 2 * (16 * M₀ / ε) * δ := mul_nonneg (mul_nonneg zero_le_two hC₂0) hδ0
  have hB0 : 0 ≤ ((16 * M₀ / ε) + (2 * M₀ / ε)) * δ := mul_nonneg (add_nonneg hC₂0 hCa0) hδ0
  have key := le_of_forall_radius₂ (X := ‖ρ 1 - ρ 0 - deriv ρ 0‖) (c := 2 * (16 * M₀ / ε) * δ)
    (B := ((16 * M₀ / ε) + (2 * M₀ / ε)) * δ) hc0 hB0 hε hm0 (fun R hR hRm => by
      have hR0 : 0 < R := by linarith
      have hsc : ∀ (ζ : ℂ), ‖ζ‖ = R → ∀ (V : Vcoup) (K : Act d L N),
          (xnorm j ℓj A V K).toReal ≤ m →
          xnorm j ℓj A (0 + ζ • V) (0 + ζ • K) ≤ ENNReal.ofReal (ε / 2) := by
        intro ζ hζ V K hVK
        rw [zero_add, zero_add, xnorm_smul, hζ, toReal_xnorm hℓ V K,
          ← ENNReal.ofReal_mul hR0.le]
        exact ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_left hVK hR0.le).trans hRm)
      have h1 := (norm_taylor_le hρ (by linarith : (1 : ℝ) < R) (M := (16 * M₀ / ε) * (R * δ))
        fun ζ hζ => by
          refine (hLip (h0K.add (hK₁.smul ζ)) (h0K.add (hK₂.smul ζ))
            (hsc ζ hζ V₁ K₁ (le_max_left _ _)) (hsc ζ hζ V₂ K₂ (le_max_right _ _))).trans ?_
          rw [zero_add, zero_add, zero_add, zero_add, ← smul_sub, ← smul_sub, xnorm_smul, hζ,
            ENNReal.toReal_mul, ENNReal.toReal_ofReal hR0.le]).2
      have e : (16 * M₀ / ε) * (R * δ) / (R * (R - 1)) = (16 * M₀ / ε) * δ / (R - 1) := by
        have : R - 1 ≠ 0 := by linarith
        field_simp
      rw [e] at h1
      refine h1.trans ?_
      rw [div_le_div_iff₀ (by linarith) hR0]
      nlinarith [mul_nonneg (mul_nonneg hC₂0 hδ0) (by linarith : (0 : ℝ) ≤ R - 2)])
    ((norm_sub_le _ _).trans (by
      have ha := hLip hK₁ hK₂ hx₁ hx₂
      rw [← hδdef] at ha
      have hb : ‖deriv ρ 0‖ ≤ (2 * M₀ / ε) * δ := by
        rw [hρd, norm_wpair _ hw]
        exact DKnext_bound_pair hd hL hj hℓ₀ hA hC hε hM₀ hM (V := 0) (V' := V₁ - V₂) h0K hK₁₂
          (by rw [xnorm_zero]; exact zero_le) hU hg
      rw [hρ0, sub_zero, hρ1]
      linarith))
  calc _ ≤ 4 * (2 * (16 * M₀ / ε) * δ + ((16 * M₀ / ε) + (2 * M₀ / ε)) * δ) * m / ε := key
    _ = remConst M₀ ε * m * δ := by rw [remConst]; ring


/-- **The linearisation at `0`**: if `‖K_{j+1}(V, K)‖_{j+1} ≤ a ‖K‖_j + b (‖V‖_j² + ‖K‖_j²)` on the
ball `‖(V, K)‖_j ≤ ε` (the bound `e:step-K`), then `‖D K_{j+1}|_0 (V̇, K̇)‖_{j+1} ≤ a ‖K̇‖_j`. -/
theorem DKnext_zero_bound (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hj : j < N) (hℓ₀ : 0 < ℓ₀)
    (hA : 1 ≤ A) (hC : GoodCov j ℓ₀ C) (hε : 0 < ε) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hS : ∀ (V : Vcoup) (K : Act d L N), InK j K → xnorm j (ellj d L ℓ₀ j) A V K ≤ ENNReal.ofReal ε →
      Knorm (j + 1) (ellj d L ℓ₀ (j + 1)) A (Knext j C V K) ≤
        ENNReal.ofReal a * Knorm j (ellj d L ℓ₀ j) A K +
          ENNReal.ofReal b * (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V ^ 2 +
            Knorm j (ellj d L ℓ₀ j) A K ^ 2))
    (V' : Vcoup) {K' : Act d L N} (hK' : InK j K') :
    Knorm (j + 1) (ellj d L ℓ₀ (j + 1)) A (DKnext j C 0 0 V' K') ≤
      ENNReal.ofReal a * Knorm j (ellj d L ℓ₀ j) A K' := by
  have hℓ := ellj_pos (d := d) (L := L) (Nat.cast_pos.2 (NeZero.pos L)) hℓ₀ j
  have hℓ' := ellj_pos (d := d) (L := L) (Nat.cast_pos.2 (NeZero.pos L)) hℓ₀ (j + 1)
  have hA0 : 0 < A := by linarith
  have h0K := InK.zero (d := d) (L := L) (N := N) j
  set v := (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V').toReal with hvdef
  set k := (Knorm j (ellj d L ℓ₀ j) A K').toReal with hkdef
  have hv0 : 0 ≤ v := ENNReal.toReal_nonneg
  have hk0 : 0 ≤ k := ENNReal.toReal_nonneg
  have ev : Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V' = ENNReal.ofReal v :=
    (ENNReal.ofReal_toReal (Vnorm_ne_top hℓ V')).symm
  have ek : Knorm j (ellj d L ℓ₀ j) A K' = ENNReal.ofReal k :=
    (ENNReal.ofReal_toReal (Knorm_ne_top hℓ K')).symm
  rw [ek, ← ENNReal.ofReal_mul ha]
  refine Knorm_le_of_wpair hA0 fun U hU g hg => ?_
  have hF := Knext_line_hol hd hL hj hC.covInv hC.symm' 0 V' h0K hK' U
  have hw : 0 ≤ wt (j + 1) A U := pow_nonneg hA0.le _
  set ψ : ℂ → ℂ := fun t => (wt (j + 1) A U : ℂ) *
    pair (Knext j C (0 + t • V') (0 + t • K') U : Alg d L N) g with hψdef
  have hl : Differentiable ℂ fun t : ℂ =>
      pair (Knext j C (0 + t • V') (0 + t • K') U : Alg d L N) g := hF.lin (pairL g)
  have hψ : Differentiable ℂ ψ := hl.const_mul _
  have hd0 : deriv ψ 0 = (wt (j + 1) A U : ℂ) *
      pair (DKnext j C 0 0 V' K' U : Alg d L N) g := by
    rw [pair_DKnext hd hL hj hC.covInv hC.symm' 0 V' h0K hK' U g]
    exact deriv_const_mul _ (hl 0)
  rw [← norm_wpair _ hw, ← hd0]
  have hR₀ : 0 < ε / (v + k + 1) := by positivity
  refine le_of_forall_small (b := b * (v ^ 2 + k ^ 2)) hR₀ fun R hR hRR => ?_
  have hsmall : R * (v + k) ≤ ε := by
    calc R * (v + k) ≤ ε / (v + k + 1) * (v + k + 1) :=
          mul_le_mul hRR (by linarith) (by linarith) hR₀.le
      _ = ε := by field_simp
  have key := norm_deriv_le_of_sphere hψ hR
    (M := a * (R * k) + b * ((R * v) ^ 2 + (R * k) ^ 2)) fun ζ hζ => by
      rw [hψdef, norm_wpair _ hw]
      simp only [zero_add]
      refine wpair_le_of_Knorm hℓ' hA0.le (by positivity) ?_ hU hg
      have hx : xnorm j (ellj d L ℓ₀ j) A (ζ • V') (ζ • K') ≤ ENNReal.ofReal ε := by
        rw [xnorm_smul, xnorm, ev, ek, hζ, ← ENNReal.ofReal_add hv0 hk0,
          ← ENNReal.ofReal_mul hR.le]
        exact ENNReal.ofReal_le_ofReal hsmall
      refine (hS _ _ (hK'.smul ζ) hx).trans (le_of_eq ?_)
      rw [Vnorm_smul, Knorm_smul, ev, ek, hζ, ← ENNReal.ofReal_mul hR.le,
        ← ENNReal.ofReal_mul hR.le, ← ENNReal.ofReal_pow (by positivity),
        ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul hb,
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine key.trans (le_of_eq ?_)
  field_simp

end Cauchy


/-! ### The derivative claims of Theorem `thm:step` -/

/-- `L^{-d_+} ≤ 1`. -/
theorem rpow_neg_dplus_le_one {d L : ℕ} (hd : 3 ≤ d) (hL : 1 ≤ L) :
    (L : ℝ) ^ (-dplus d) ≤ 1 := by
  have h0 : 0 ≤ dplus d := by
    unfold dplus
    refine le_min ?_ zero_le_one
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hL) (by linarith)

/-- **Theorem `thm:step`, derivative claims.**  With the constants `C₀, η` of `e:step-K`
(`Step.step`) and `ε = ε(L, A)`, there is `C₁ = C₁(L, A)` such that for `j < N`, `C = C_{j+1}`
satisfying `GoodCov`, and polymer coordinates in `𝒦_j`:

1. (first derivatives on the half ball) for `‖(V, K)‖_j ≤ ε/2`,
   `‖D_{(V̇, K̇)} K_{j+1}|_{(V,K)}‖_{j+1} ≤ C₁ ‖(V̇, K̇)‖_j`;
2. (Lipschitz bound) `‖K_{j+1}(x) - K_{j+1}(y)‖_{j+1} ≤ C₁ ‖x - y‖_j` on the half ball;
3. (linearisation at `0`, the operator `D_j` of Section `sec:flow`)
   `‖D K_{j+1}|_0 (V̇, K̇)‖_{j+1} ≤ C₀ (L^{-d_+} + A^{-η}) ‖K̇‖_j` if `j + 1 < N`
   (`L^d` instead of `L^{-d_+}` if `j + 1 = N`);
4. `D K_{j+1}|_0 (V̇, 0) = 0` (in the norm `‖·‖_{j+1}`);
5. (the nonlinear remainder `g_{j+1}` of Section `sec:flow`) on the half ball,
   `‖K_{j+1}(x) - K_{j+1}(y) - D K_{j+1}|_0 (x - y)‖_{j+1} ≤ C₁ max(‖x‖_j, ‖y‖_j) ‖x - y‖_j`.

Here `‖(V, K)‖_j = ‖V‖_j + ‖K‖_j` (`xnorm`) and `D K_{j+1}|_x ẋ = DKnext j C V K V̇ K̇` is the
derivative along the complex line `t ↦ x + t ẋ`, which is linear in `ẋ` (`DKnext_lin`). -/
theorem step_deriv {d : ℕ} (hd : 3 ≤ d) : ∃ (C₀ η : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧ 0 < η ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∃ ε C₁ : ℝ, 0 < ε ∧ 0 ≤ C₁ ∧
    ∀ (N j : ℕ), j < N → ∀ (ℓ₀ : ℝ), 0 < ℓ₀ →
    ∀ (C : Matrix (Lam d L N) (Lam d L N) ℝ), GoodCov j ℓ₀ C →
      (∀ (V V' : Vcoup) (K K' : Act d L N), InK j K → InK j K' →
        xnorm j (ellj d L ℓ₀ j) A V K ≤ ENNReal.ofReal (ε / 2) →
        Knorm (j + 1) (ellj d L ℓ₀ (j + 1)) A (DKnext j C V K V' K') ≤
          ENNReal.ofReal C₁ * xnorm j (ellj d L ℓ₀ j) A V' K') ∧
      (∀ (V₁ V₂ : Vcoup) (K₁ K₂ : Act d L N), InK j K₁ → InK j K₂ →
        xnorm j (ellj d L ℓ₀ j) A V₁ K₁ ≤ ENNReal.ofReal (ε / 2) →
        xnorm j (ellj d L ℓ₀ j) A V₂ K₂ ≤ ENNReal.ofReal (ε / 2) →
        Knorm (j + 1) (ellj d L ℓ₀ (j + 1)) A
            (fun U => Knext j C V₁ K₁ U - Knext j C V₂ K₂ U) ≤
          ENNReal.ofReal C₁ * xnorm j (ellj d L ℓ₀ j) A (V₁ - V₂) (K₁ - K₂)) ∧
      (∀ (V' : Vcoup) (K' : Act d L N), InK j K' →
        Knorm (j + 1) (ellj d L ℓ₀ (j + 1)) A (DKnext j C 0 0 V' K') ≤
          ENNReal.ofReal (C₀ * ((if j + 1 < N then (L : ℝ) ^ (-dplus d) else (L : ℝ) ^ d) +
            A ^ (-η))) * Knorm j (ellj d L ℓ₀ j) A K') ∧
      (∀ V' : Vcoup, Knorm (j + 1) (ellj d L ℓ₀ (j + 1)) A (DKnext j C 0 0 V' 0) = 0) ∧
      (∀ (V₁ V₂ : Vcoup) (K₁ K₂ : Act d L N), InK j K₁ → InK j K₂ →
        xnorm j (ellj d L ℓ₀ j) A V₁ K₁ ≤ ENNReal.ofReal (ε / 2) →
        xnorm j (ellj d L ℓ₀ j) A V₂ K₂ ≤ ENNReal.ofReal (ε / 2) →
        Knorm (j + 1) (ellj d L ℓ₀ (j + 1)) A (fun U => Knext j C V₁ K₁ U -
            Knext j C V₂ K₂ U - DKnext j C 0 0 (V₁ - V₂) (K₁ - K₂) U) ≤
          ENNReal.ofReal C₁ *
            max (xnorm j (ellj d L ℓ₀ j) A V₁ K₁) (xnorm j (ellj d L ℓ₀ j) A V₂ K₂) *
            xnorm j (ellj d L ℓ₀ j) A (V₁ - V₂) (K₁ - K₂)) := by
  obtain ⟨C₀, η, ν, L₀, hC₀, hη, hν, hstep⟩ := step hd
  refine ⟨C₀, η, max L₀ (2 ^ (d + 3)), hC₀, hη, ?_⟩
  intro L _ hL
  have hL8 : 2 ^ (d + 3) ≤ L := le_trans (le_max_right _ _) hL
  have hL1 : 1 ≤ L := le_trans (Nat.one_le_two_pow) hL8
  have hd1 : 1 ≤ d := by omega
  obtain ⟨A₀, hA₀, hA⟩ := hstep L (le_trans (le_max_left _ _) hL)
  refine ⟨A₀, hA₀, fun A hAA => ?_⟩
  have hA1 : 1 ≤ A := hA₀.trans hAA
  have hA0 : 0 < A := by linarith
  obtain ⟨ε, hε, hS⟩ := hA A hAA
  set M₀ := C₀ * (1 + (L : ℝ) ^ d + A ^ (-η)) * ε + C₀ * A ^ ν * (2 * ε ^ 2) with hM₀def
  have hM₀ : 0 ≤ M₀ := by positivity
  refine ⟨ε, 2 * M₀ / ε + 16 * M₀ / ε + remConst M₀ ε, hε, by unfold remConst; positivity, ?_⟩
  intro N j hj ℓ₀ hℓ₀ C hC
  set f : ℝ := if j + 1 < N then (L : ℝ) ^ (-dplus d) else (L : ℝ) ^ d with hf
  have hf0 : 0 ≤ f := by rw [hf]; split_ifs <;> positivity
  have hf1 : f ≤ 1 + (L : ℝ) ^ d := by
    rw [hf]
    split_ifs
    · linarith [rpow_neg_dplus_le_one hd hL1, pow_nonneg (Nat.cast_nonneg (α := ℝ) L) d]
    · linarith
  have hSK : ∀ (V : Vcoup) (K : Act d L N), InK j K →
      xnorm j (ellj d L ℓ₀ j) A V K ≤ ENNReal.ofReal ε →
      Knorm (j + 1) (ellj d L ℓ₀ (j + 1)) A (Knext j C V K) ≤
        ENNReal.ofReal (C₀ * (f + A ^ (-η))) * Knorm j (ellj d L ℓ₀ j) A K +
          ENNReal.ofReal (C₀ * A ^ ν) * (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V ^ 2 +
            Knorm j (ellj d L ℓ₀ j) A K ^ 2) :=
    fun V K hK hx => (hS N j hj ℓ₀ hℓ₀ C hC V K hK hx).2.2
  have hM : ∀ (V : Vcoup) (K : Act d L N), InK j K →
      xnorm j (ellj d L ℓ₀ j) A V K ≤ ENNReal.ofReal ε →
      Knorm (j + 1) (ellj d L ℓ₀ (j + 1)) A (Knext j C V K) ≤ ENNReal.ofReal M₀ := by
    intro V K hK hx
    refine (hSK V K hK hx).trans ?_
    have hv : Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V ≤ ENNReal.ofReal ε :=
      le_self_add.trans hx
    have hk : Knorm j (ellj d L ℓ₀ j) A K ≤ ENNReal.ofReal ε := le_add_self.trans hx
    calc _ ≤ ENNReal.ofReal (C₀ * (f + A ^ (-η))) * ENNReal.ofReal ε +
          ENNReal.ofReal (C₀ * A ^ ν) * (ENNReal.ofReal ε ^ 2 + ENNReal.ofReal ε ^ 2) := by
          gcongr
      _ = ENNReal.ofReal (C₀ * (f + A ^ (-η)) * ε + C₀ * A ^ ν * (ε ^ 2 + ε ^ 2)) := by
          rw [← ENNReal.ofReal_pow hε.le, ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
      _ ≤ ENNReal.ofReal M₀ := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [hM₀def]
          have : C₀ * (f + A ^ (-η)) * ε ≤ C₀ * (1 + (L : ℝ) ^ d + A ^ (-η)) * ε := by gcongr
          nlinarith
  have hC1a : 2 * M₀ / ε ≤ 2 * M₀ / ε + 16 * M₀ / ε + remConst M₀ ε := by
    have : 0 ≤ remConst M₀ ε := by unfold remConst; positivity
    have : 0 ≤ 16 * M₀ / ε := by positivity
    linarith
  have hC1b : 16 * M₀ / ε ≤ 2 * M₀ / ε + 16 * M₀ / ε + remConst M₀ ε := by
    have : 0 ≤ remConst M₀ ε := by unfold remConst; positivity
    have : 0 ≤ 2 * M₀ / ε := by positivity
    linarith
  have hC1c : remConst M₀ ε ≤ 2 * M₀ / ε + 16 * M₀ / ε + remConst M₀ ε := by
    have : 0 ≤ 16 * M₀ / ε := by positivity
    have : 0 ≤ 2 * M₀ / ε := by positivity
    linarith
  have hb := fun (V' : Vcoup) (K' : Act d L N) (hK' : InK j K') =>
    DKnext_zero_bound hd1 hL8 hj hℓ₀ hA1 hC hε (a := C₀ * (f + A ^ (-η))) (b := C₀ * A ^ ν)
      (by positivity) (by positivity) hSK V' hK'
  refine ⟨fun V V' K K' hK hK' hx => ?_, fun V₁ V₂ K₁ K₂ hK₁ hK₂ hx₁ hx₂ => ?_,
    fun V' K' hK' => hb V' K' hK', fun V' => ?_, fun V₁ V₂ K₁ K₂ hK₁ hK₂ hx₁ hx₂ => ?_⟩
  · refine (DKnext_bound hd1 hL8 hj hℓ₀ hA1 hC hε hM₀ hM hK hK' hx).trans ?_
    gcongr
  · refine (Knext_lipschitz hd1 hL8 hj hℓ₀ hA1 hC hε hM₀ hM hK₁ hK₂ hx₁ hx₂).trans ?_
    gcongr
  · refine le_antisymm ((hb V' 0 (InK.zero j)).trans (le_of_eq ?_)) zero_le
    rw [Knorm_zero, mul_zero]
  · refine (Knext_remainder hd1 hL8 hj hℓ₀ hA1 hC hε hM₀ hM hK₁ hK₂ hx₁ hx₂).trans ?_
    gcongr

/-- **Theorem `thm:step`, derivatives of the coupling constants.**  The map
`(V_j, K_j) ↦ (u_{j+1}, V_{j+1})` is linear on `𝒱^∅ ⊕ 𝒦_j`, so its derivative in the direction
`(V̇, K̇)` is `(u̇, V̇_{+}) = (u_{j+1}, V_{j+1})(V̇, K̇)`, which satisfies the bounds of
`coupling_bounds` (in particular `e:step-V`). -/
theorem coupling_deriv {d : ℕ} (hd : 3 ≤ d) : ∃ (C₀ : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∀ (N j : ℕ), j < N → ∀ (ℓ₀ : ℝ), 0 < ℓ₀ →
    ∀ (C : Matrix (Lam d L N) (Lam d L N) ℝ), GoodCov j ℓ₀ C →
    ∀ (V V' : Vcoup) (K K' : Act d L N) (A : ℝ), 1 ≤ A → InK j K → InK j K' →
      (∀ t : ℂ, uVnext j C (V + t • V') (K + t • K') = uVnext j C V K + t • uVnext j C V' K') ∧
      (∀ b ∈ blockIdx (d := d) (L := L) (N := N) j,
        Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1))
            (((uVnext j C V' K').1 * (blockSet (L := L) (N := N) j b).card) • (1 : Alg d L N) +
              (uVnext j C V' K').2.eval (blockSet j b)) ≤
          Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V' +
            ENNReal.ofReal C₀ * Knorm j (ellj d L ℓ₀ j) A K') ∧
      (∀ b ∈ blockIdx (d := d) (L := L) (N := N) (j + 1),
        Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1))
            (((uVnext j C V' K').1 * (blockSet (L := L) (N := N) (j + 1) b).card) •
                (1 : Alg d L N) + (uVnext j C V' K').2.eval (blockSet (j + 1) b) -
              EC C (theta (V'.eval (blockSet (L := L) (N := N) (j + 1) b)))) ≤
          ENNReal.ofReal (C₀ * (L : ℝ) ^ d) * Knorm j (ellj d L ℓ₀ j) A K') := by
  obtain ⟨C₀, L₀, hC₀, h⟩ := coupling_bounds hd
  refine ⟨C₀, max L₀ (2 ^ (d + 3)), hC₀, fun L _ hL N j hj ℓ₀ hℓ₀ C hC V V' K K' A hA hK hK' => ?_⟩
  have hL8 : 2 ^ (d + 3) ≤ L := le_trans (le_max_right _ _) hL
  obtain ⟨-, -, h3, h4⟩ := h L (le_trans (le_max_left _ _) hL) N j hj ℓ₀ hℓ₀ C hC V' K' A hA hK'
  exact ⟨fun t => uVnext_line (by omega) hL8 hj hC.covInv hC.symm' V V' hK hK' t, h3, h4⟩

end

end Step
