module

public import ArborealDecay.Frozen.IsRealStable
public import ArborealDecay.Frozen.SMonomial
public import ArborealDecay.Separator
public import ArborealDecay.Bridge

/-!
# Provider for the frozen anchor `StableSeparator`

Proves the exact frozen statement from the verified libraries via `ArborealDecay.Bridge`.
-/

@[expose] public section

namespace ArborealDecay.Provider

open ArborealDecay ArborealDecay.Bridge

variable {V : Type*} [Fintype V]

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
  ArborealDecay.Separator.stable_separator p hstab hma hpos c A B hc hA hB htop

end ArborealDecay.Provider

end
