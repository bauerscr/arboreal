module

public import ArborealDecay.Stability.Operator

/-!
# Closure properties of stability (§2.C)

* identification of variables: `IsStable p → IsStable (rename f p)` for *any* map `f`;
* real translation `X k ↦ X k + a k`;
* real specialization of a variable `s` of a multi-affine stable polynomial gives a stable or
  zero polynomial (`IsStable.specialize_isStableOrZero`), via the two-variable root-moving
  lemma `TwoVarZeroFree.eq_zero_of_root`.
-/

@[expose] public section

open MvPolynomial Filter Topology

namespace ArborealDecay.Stability

noncomputable section

variable {σ τ : Type*}

/-! ### Identification of variables and translation -/

theorem IsStable.rename {p : MvPolynomial σ ℂ} (hp : IsStable p) (f : σ → τ) :
    IsStable (MvPolynomial.rename f p) := by
  intro z hz
  rw [MvPolynomial.eval_rename]
  exact hp _ fun i => hz (f i)

theorem IsRealStable.rename {p : MvPolynomial σ ℝ} (hp : IsRealStable p) (f : σ → τ) :
    IsRealStable (MvPolynomial.rename f p) := by
  rw [isRealStable_iff_aeval] at hp ⊢
  intro z hz
  rw [MvPolynomial.aeval_rename]
  exact hp _ fun i => hz (f i)

/-- Real translation `X k ↦ X k + a k`. -/
@[expose] def shiftReal (a : σ → ℝ) (p : MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  bind₁ (fun k => X k + C (a k)) p

theorem IsRealStable.shift {p : MvPolynomial σ ℝ} (hp : IsRealStable p) (a : σ → ℝ) :
    IsRealStable (shiftReal a p) := by
  rw [isRealStable_iff_aeval] at hp ⊢
  intro z hz
  have h : (fun i => aeval z (X i + C (a i) : MvPolynomial σ ℝ)) = fun k => z k + (a k : ℂ) := by
    funext k; simp
  rw [shiftReal, MvPolynomial.aeval_bind₁, h]
  exact hp _ fun k => by simpa using hz k

/-- Complex version of real translation. -/
@[expose] def shiftRealC (a : σ → ℝ) (p : MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  bind₁ (fun k => X k + C (a k : ℂ)) p

theorem eval_bind₁ {R : Type*} [CommSemiring R] (z : τ → R) (g : σ → MvPolynomial τ R)
    (p : MvPolynomial σ R) : eval z (bind₁ g p) = eval (fun k => eval z (g k)) p :=
  eval₂Hom_bind₁ _ _ _ _

theorem IsStable.shiftC {p : MvPolynomial σ ℂ} (hp : IsStable p) (a : σ → ℝ) :
    IsStable (shiftRealC a p) := by
  intro z hz
  rw [shiftRealC, eval_bind₁]
  exact hp _ fun k => by simpa using hz k

end

end ArborealDecay.Stability
