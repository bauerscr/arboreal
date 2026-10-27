module

public import ArborealDecay.Wiring.PolyProps
public import ArborealDecay.Stability

/-!
# Real stability of the specialised polynomial `p`

Setting the vertex variables outside `{a, b} ∪ S` of the stable multi-affine polynomial `P_G` to
zero one at a time (`IsRealStable.specializeReal_isRealStableOrZero`) gives a polynomial that is
stable or zero; `p` is this polynomial with its variables renamed by `lab`.
-/

@[expose] public section

namespace ArborealDecay.Wiring

open MvPolynomial Finset ArborealDecay.Stability

noncomputable section

open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Set the variables of `T` to zero. -/
def zeroOn (T : Finset V) (v : V) : MvPolynomial V ℝ := if v ∈ T then 0 else X v

/-- The polynomial `P` with the variables of `T` set to zero. -/
def qpoly (P : MvPolynomial V ℝ) (T : Finset V) : MvPolynomial V ℝ := bind₁ (zeroOn T) P

theorem qpoly_empty (P : MvPolynomial V ℝ) : qpoly P ∅ = P := by
  unfold qpoly zeroOn
  simp [bind₁_X_left]

theorem qpoly_insert (P : MvPolynomial V ℝ) (T : Finset V) (w : V) :
    qpoly P (insert w T) = specializeReal w 0 (qpoly P T) := by
  unfold qpoly specializeReal
  rw [bind₁_bind₁]
  refine congrArg (fun g => bind₁ g P) ?_
  funext v
  unfold zeroOn
  by_cases hvT : v ∈ T
  · simp [hvT]
  · by_cases hvw : v = w
    · subst hvw; simp [hvT]
    · simp [hvT, hvw, Function.update_of_ne hvw]

theorem qpoly_isMultiAffine {P : MvPolynomial V ℝ} (hP : IsMultiAffine P) (T : Finset V) :
    IsMultiAffine (qpoly P T) := by
  intro j
  refine degreeOf_bind₁_le_one hP id (zeroOn T) (fun j k => ?_) j
  unfold zeroOn
  by_cases hk : k ∈ T
  · simp [hk]
  · simp only [hk, if_false, id]
    rw [degreeOf_X]
    by_cases hkj : k = j
    · subst hkj; simp
    · simp [hkj, Ne.symm hkj]

theorem qpoly_stable {P : MvPolynomial V ℝ} (hP : IsMultiAffine P) (hs : IsRealStable P)
    (T : Finset V) : IsRealStableOrZero (qpoly P T) := by
  induction T using Finset.induction_on with
  | empty => rw [qpoly_empty]; exact Or.inr hs
  | @insert w T _ ih =>
    rw [qpoly_insert]
    rcases ih with h0 | h1
    · left
      rw [h0]
      unfold specializeReal
      exact map_zero _
    · exact IsRealStable.specializeReal_isRealStableOrZero (qpoly_isMultiAffine hP T) h1 w 0

theorem rename_phi {a b : V} {S : Finset V} (hab : a ≠ b) (ha : a ∉ S) (hb : b ∉ S) (v : V) :
    rename (lab a b S) (phi a b S v) =
      zeroOn (Finset.univ.filter fun v => ∀ u, lab a b S u ≠ v) v := by
  have hinj := lab_injective hab ha hb
  unfold phi zeroOn
  by_cases h : ∃ u, lab a b S u = v
  · obtain ⟨u0, hu0⟩ := h
    have hf : (Finset.univ.filter fun u => lab a b S u = v) = {u0} := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h => hinj (h.trans hu0.symm), fun h => h ▸ hu0⟩
    rw [hf, if_neg]
    · simp [hu0]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_not]
      exact ⟨u0, hu0⟩
  · have hf : (Finset.univ.filter fun u => lab a b S u = v) = ∅ := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      exact fun hu => h ⟨u, hu⟩
    rw [hf, if_pos]
    · simp
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun u hu => h ⟨u, hu⟩

theorem rename_wpoly {β : V → V → ℝ} {hβ : ∀ i j, β i j = β j i} {a b : V} {S : Finset V}
    (hab : a ≠ b) (ha : a ∉ S) (hb : b ∉ S) :
    rename (lab a b S) (wpoly β hβ a b S) =
      qpoly (forestPolynomial β hβ) (Finset.univ.filter fun v => ∀ u, lab a b S u ≠ v) := by
  unfold wpoly qpoly
  rw [rename_bind₁]
  refine congrArg (fun g => bind₁ g (forestPolynomial β hβ)) ?_
  funext v
  exact rename_phi hab ha hb v

/-- **Stability of `p`**, from stability and multi-affinity of `P_G`. -/
theorem wpoly_aeval_ne_zero_of_forest {β : V → V → ℝ} {hβ : ∀ i j, β i j = β j i}
    (hβ0 : ∀ i j, 0 ≤ β i j)
    (hPma : IsMultiAffine (forestPolynomial β hβ))
    (hPst : ∀ z : V → ℂ, (∀ j, 0 < (z j).im) → aeval z (forestPolynomial β hβ) ≠ 0)
    {a b : V} {S : Finset V} (hab : a ≠ b) (ha : a ∉ S) (hb : b ∉ S) :
    ∀ z : Var S → ℂ, (∀ j, 0 < (z j).im) → aeval z (wpoly β hβ a b S) ≠ 0 := by
  have hinj := lab_injective hab ha hb
  have hst := qpoly_stable hPma ((isRealStable_iff_aeval _).2 hPst)
    (Finset.univ.filter fun v => ∀ u, lab a b S u ≠ v)
  rw [← rename_wpoly hab ha hb] at hst
  have hne : wpoly β hβ a b S ≠ 0 := by
    intro h0
    have := coeff_wpoly_pos β hβ hβ0 hab ha hb 0 (fun _ => by simp)
    rw [h0] at this
    simp at this
  rcases hst with h0 | hst
  · exact absurd ((rename_injective _ hinj).eq_iff.1 (h0.trans (map_zero _).symm)) hne
  · intro z hz
    rw [isRealStable_iff_aeval] at hst
    let z' : V → ℂ := fun v => if h : ∃ u, lab a b S u = v then z h.choose else Complex.I
    have hz' : ∀ v, 0 < (z' v).im := by
      intro v
      by_cases h : ∃ u, lab a b S u = v
      · simp only [z', dif_pos h]; exact hz _
      · have : z' v = Complex.I := dif_neg h
        rw [this]; simp
    have := hst z' hz'
    rw [aeval_rename] at this
    have hzz : z' ∘ lab a b S = z := by
      funext u
      have h : ∃ u', lab a b S u' = lab a b S u := ⟨u, rfl⟩
      simp only [Function.comp, z', dif_pos h]
      exact congrArg z (hinj h.choose_spec)
    rw [hzz] at this
    exact this

end

end ArborealDecay.Wiring
