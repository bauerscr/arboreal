-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Mathlib
public import ArborealDecay.Frozen.IsRealStable
public import ArborealDecay.Frozen.SMonomial
public import ArborealDecay.Provider.StableSeparator

/-!
# Frozen declaration `ArborealDecay.stable_separator`

Source: `h02expdec.tex`. Author-approved; see `FROZEN_MANIFEST.json`.
-/

@[expose] public section

namespace ArborealDecay

/-- **Lemma `lem:stable-separator`** (note L339–352). Variables: `x = inl 0`, `y = inl 1`,
`s_k = inr k`. -/
theorem stable_separator {ι : Type*} [Fintype ι] (p : MvPolynomial (Fin 2 ⊕ ι) ℝ)
    (hstab : IsRealStable p) (hma : ∀ v, p.degreeOf v ≤ 1)
    (hpos : ∀ d : Fin 2 ⊕ ι →₀ ℕ, (∀ v, d v ≤ 1) → 0 < p.coeff d)
    (c A B : ℝ) (hc : 0 < c) (hA : 0 < A) (hB : 0 < B)
    (htop :
      p.coeff (sMonomial ι + Finsupp.single (Sum.inl 0) 1 + Finsupp.single (Sum.inl 1) 1) = c ∧
      p.coeff (sMonomial ι + Finsupp.single (Sum.inl 0) 1) = c * B ∧
      p.coeff (sMonomial ι + Finsupp.single (Sum.inl 1) 1) = c * A ∧
      p.coeff (sMonomial ι) = c * A * B) :
    0 ≤ MvPolynomial.eval (Sum.elim ![-A, -B] 0) p :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact ArborealDecay.Provider.stable_separator p hstab hma hpos c A B hc hA hB htop
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ArborealDecay

end
-- FROZEN_ANCHOR_SUFFIX_END
