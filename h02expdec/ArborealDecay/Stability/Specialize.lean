module

public import ArborealDecay.Stability.Closure

/-!
# Real specialization of a multi-affine variable (§2.C, lemmas C1 and C2)

* `TwoVarZeroFree.eq_zero_of_root` (C1): if `q(w, s) = α + β w + γ s + δ w s` is zero-free on
  `H × H`, `a ∈ ℝ`, and `q(w₀, a) = 0` for some `w₀ ∈ H`, then `q(·, a) ≡ 0`.
* `IsStable.specialize_isStableOrZero` (C2): if `p` is multi-affine and stable, `s : σ` and
  `a ∈ ℝ`, then `p` with `X s` replaced by `a` is stable or zero.
-/

@[expose] public section

open MvPolynomial Filter Topology

namespace ArborealDecay.Stability

noncomputable section

variable {σ : Type*} [DecidableEq σ]

namespace TwoVarZeroFree

variable {α β γ δ : ℂ}

/-- Lemma C1. -/
theorem eq_zero_of_root (h : TwoVarZeroFree α β γ δ) (a : ℝ) {w₀ : ℂ} (hw : 0 < w₀.im)
    (hroot : (α + γ * a) + (β + δ * a) * w₀ = 0) : α + γ * a = 0 ∧ β + δ * a = 0 := by
  by_contra hcon
  have hβ : β + δ * a ≠ 0 := by
    intro h0
    apply hcon
    rw [h0, zero_mul, add_zero] at hroot
    exact ⟨hroot, h0⟩
  set F : ℝ → ℂ := fun ε => -(α + γ * (a + ε * Complex.I)) / (β + δ * (a + ε * Complex.I))
    with hF
  have hD : ContinuousAt (fun ε : ℝ => β + δ * ((a : ℂ) + ε * Complex.I)) 0 := by fun_prop
  have hN : ContinuousAt (fun ε : ℝ => -(α + γ * ((a : ℂ) + ε * Complex.I))) 0 := by fun_prop
  have hD0 : β + δ * ((a : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) ≠ 0 := by simpa using hβ
  have hFc : ContinuousAt F 0 := hN.div hD hD0
  have hF0 : F 0 = w₀ := by
    simp only [hF, Complex.ofReal_zero, zero_mul, add_zero]
    rw [div_eq_iff hβ]
    linear_combination -hroot
  have hev1 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < (F ε).im :=
    (Complex.continuous_im.continuousAt.comp hFc).eventually (lt_mem_nhds (by simpa [hF0] using hw))
  have hev2 : Filter.Eventually (fun ε : ℝ => β + δ * ((a : ℂ) + (ε : ℂ) * Complex.I) ≠ 0)
      (𝓝 0) := hD.eventually_ne hD0
  obtain ⟨ε, ⟨h1, h2⟩, hε⟩ := (((hev1.and hev2).filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))).exists
  apply h (F ε) (a + ε * Complex.I) h1 (by simpa using hε)
  have hDF : (β + δ * ((a : ℂ) + ε * Complex.I)) * F ε =
      -(α + γ * ((a : ℂ) + ε * Complex.I)) := by
    simp only [hF]; field_simp
  linear_combination hDF

end TwoVarZeroFree

/-- Replace `X s` by the constant `a`. -/
@[expose] def specialize (s : σ) (a : ℂ) (p : MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  bind₁ (Function.update X s (C a)) p

theorem eval_specialize (s : σ) (a : ℂ) (p : MvPolynomial σ ℂ) (z : σ → ℂ) :
    eval z (specialize s a p) = eval (Function.update z s a) p := by
  unfold specialize
  rw [eval_bind₁]
  have : (fun k => eval z (Function.update X s (C a) k)) = Function.update z s a := by
    funext k
    by_cases hk : k = s
    · subst hk; simp
    · simp [Function.update_of_ne hk]
  rw [this]

/-- Lemma C2, one coordinate: if `p(z[s := a]) = 0` then also `p(z[k := w][s := a]) = 0`. -/
theorem eval_update_eq_zero_of_isStable {p : MvPolynomial σ ℂ} (hp : IsMultiAffine p)
    (hs : IsStable p) (s : σ) (a : ℝ) {z : σ → ℂ} (hz : ∀ k, 0 < (z k).im)
    (hz0 : eval (Function.update z s (a : ℂ)) p = 0) (k : σ) {w : ℂ} (hw : 0 < w.im) :
    eval (Function.update (Function.update z k w) s (a : ℂ)) p = 0 := by
  by_cases hks : k = s
  · subst hks
    rw [Function.update_idem]; exact hz0
  obtain ⟨p₀₀, p₁₀, p₀₁, p₁₁, hdec, -⟩ := exists_isTwoVarDecomp hks (hp k) (hp s)
  have hZF := hs.twoVarZeroFree hks hdec hz
  have e1 := hdec.eval_update hks z (z k) (a : ℂ)
  rw [Function.update_eq_self] at e1
  rw [e1] at hz0
  obtain ⟨h1, h2⟩ := hZF.eq_zero_of_root a (hz k)
    (by linear_combination hz0)
  rw [hdec.eval_update hks]
  linear_combination h1 + w * h2

/-- Lemma C2: real specialization of a variable of a multi-affine stable polynomial is stable or
zero. -/
theorem IsStable.specialize_isStableOrZero [Fintype σ] {p : MvPolynomial σ ℂ}
    (hp : IsMultiAffine p) (hs : IsStable p) (s : σ) (a : ℝ) :
    IsStableOrZero (specialize s (a : ℂ) p) := by
  by_cases hex : ∃ z : σ → ℂ, (∀ k, 0 < (z k).im) ∧ eval z (specialize s (a : ℂ) p) = 0
  · left
    obtain ⟨z, hz, hz0⟩ := hex
    rw [eval_specialize] at hz0
    have hall : ∀ F : Finset σ, ∀ z' : σ → ℂ, (∀ k, 0 < (z' k).im) →
        (∀ k, k ∉ F → z' k = z k) → eval (Function.update z' s (a : ℂ)) p = 0 := by
      intro F
      induction F using Finset.induction_on with
      | empty =>
        intro z' _ h
        have : z' = z := funext fun k => h k (Finset.notMem_empty k)
        subst this; exact hz0
      | insert k F hk ih =>
        intro z' hz' hagree
        have h1 : eval (Function.update (Function.update z' k (z k)) s (a : ℂ)) p = 0 := by
          apply ih
          · intro l
            by_cases hl : l = k
            · subst hl; simpa using hz l
            · simpa [Function.update_of_ne hl] using hz' l
          · intro l hl
            by_cases hlk : l = k
            · subst hlk; simp
            · rw [Function.update_of_ne hlk]
              exact hagree l (by simp [hlk, hl])
        have := eval_update_eq_zero_of_isStable hp hs s a (z := Function.update z' k (z k))
          (fun l => by
            by_cases hl : l = k
            · subst hl; simpa using hz l
            · simpa [Function.update_of_ne hl] using hz' l) h1 k (hz' k)
        simpa using this
    apply MvPolynomial.funext_set (fun _ => {w : ℂ | 0 < w.im}) (fun _ => ?_)
    · intro x hx
      rw [eval_specialize, map_zero]
      exact hall Finset.univ x (fun k => hx k (Set.mem_univ k)) (fun k hk => absurd (Finset.mem_univ k) hk)
    · refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((n : ℂ) + 1) * Complex.I) ?_ ?_
      · intro m n hmn
        have := congrArg Complex.im hmn
        simp at this
        exact_mod_cast this
      · intro n
        simp
        positivity
  · right
    intro z hz h0
    exact hex ⟨z, hz, h0⟩

/-- Replace `X s` by the real constant `a` in a real polynomial. -/
@[expose] def specializeReal (s : σ) (a : ℝ) (p : MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  bind₁ (Function.update X s (C a)) p

theorem map_specializeReal (s : σ) (a : ℝ) (p : MvPolynomial σ ℝ) :
    (specializeReal s a p).map Complex.ofRealHom =
      specialize s (a : ℂ) (p.map Complex.ofRealHom) := by
  unfold specializeReal specialize
  rw [MvPolynomial.map_bind₁]
  have : (fun i => (MvPolynomial.map Complex.ofRealHom)
      (Function.update X s (C a : MvPolynomial σ ℝ) i)) =
      Function.update X s (C (a : ℂ)) := by
    funext k
    by_cases hk : k = s
    · subst hk; simp
    · simp [Function.update_of_ne hk]
  rw [this]

/-- Lemma C2, real version. -/
theorem IsRealStable.specializeReal_isRealStableOrZero [Fintype σ] {p : MvPolynomial σ ℝ}
    (hp : IsMultiAffine p) (hs : IsRealStable p) (s : σ) (a : ℝ) :
    IsRealStableOrZero (specializeReal s a p) := by
  rw [isRealStableOrZero_iff, map_specializeReal]
  exact IsStable.specialize_isStableOrZero (hp.map Complex.ofRealHom) hs s a

end

end ArborealDecay.Stability
