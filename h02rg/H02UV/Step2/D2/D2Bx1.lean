import Step2.D2.D2Bub5

/-!
# The polarised bubble `𝔅x(a, c)` and its position form

For finitely supported `a, c : ℤ² → ℂ`:

* `bubX a c = (2π)^{-2} [∫ (4 sin² p₀ - 2λ) Â₀ Ĉ₀ + ∫ (λ²/2) Â₁ Ĉ₁]` (`trigK kap0`, `trigK kap2`),
  symmetric and bilinear; `negBub C X 0 = bubX c c` for even `c` (`negBub_eq_bubX`);
* `bubX_pos`: **position form**
  `bubX a c = ∑_v a(v) (K₀ c)(-v) + ∑_v v₀ a(v) (K₂ g)(-v)`, `g(u) = u₀ c(u)`,
  `(K f)(u) = ∑_{(s, κ) ∈ kap} κ f(u - s)` (no evenness needed).
-/

namespace Step2

open Finset MeasureTheory Step2.D2 Loc FRD Grassmann

noncomputable section

section Two

variable (a c : ℤ × ℤ → ℂ)

/-- `∫ Â_j Ĉ_k e^{i s·p} = (2π)² ∑_v v₀^j (-v₀ - s₀)^k a(v) c(-v - s)`. -/
theorem integral_symb_symb2 (ha : Function.HasFiniteSupport a) (hc : Function.HasFiniteSupport c)
    (j k : ℕ) (s : ℤ × ℤ) :
    ∫ p in BZ, symb a j p * symb c k p * ex s p = (2 * (Real.pi : ℂ)) ^ 2 *
      ∑ᶠ v : ℤ × ℤ, (v.1 : ℂ) ^ j * (-(v.1 : ℂ) - s.1) ^ k * a v * c (-v.1 - s.1, -v.2 - s.2) := by
  set Sa := ha.toFinset
  set Sc := hc.toFinset
  have hSa : ∀ u, u ∉ Sa → a u = 0 := by
    intro u hu
    simp only [Sa, Set.Finite.mem_toFinset, Function.mem_support, ne_eq, not_not] at hu
    exact hu
  have hSc : ∀ u, u ∉ Sc → c u = 0 := by
    intro u hu
    simp only [Sc, Set.Finite.mem_toFinset, Function.mem_support, ne_eq, not_not] at hu
    exact hu
  have hint : ∀ p, symb a j p * symb c k p * ex s p =
      ∑ v ∈ Sa, ∑ u ∈ Sc, ((v.1 : ℂ) ^ j * a v * ((u.1 : ℂ) ^ k * c u)) * ex (v + u + s) p := by
    intro p
    rw [symb_eq_sum a ha, symb_eq_sum c hc, sum_mul, sum_mul]
    refine sum_congr rfl fun v _ => ?_
    rw [mul_sum, sum_mul]
    refine sum_congr rfl fun u _ => ?_
    rw [← ex_add, ← ex_add]; ring
  simp_rw [hint]
  rw [integral_finsetSum _ fun v _ => integrable_finsetSum _ fun u _ =>
    (integrableOn_ex _).const_mul _]
  simp_rw [integral_finsetSum _ fun u _ => (integrableOn_ex _).const_mul _]
  simp_rw [integral_const_mul, integral_ex_BZ]
  rw [finsum_eq_sum_of_support_subset _ (s := Sa) (by
    intro v hv
    simp only [Function.mem_support, ne_eq] at hv
    simp only [Sa, Set.Finite.coe_toFinset, Function.mem_support, ne_eq]
    intro h; apply hv; rw [h]; ring), mul_sum]
  refine sum_congr rfl fun v _ => ?_
  have key : ∀ u ∈ Sc, ((v.1 : ℂ) ^ j * a v * ((u.1 : ℂ) ^ k * c u)) *
      (if v + u + s = 0 then (2 * (Real.pi : ℂ)) ^ 2 else 0) =
      if u = (-v.1 - s.1, -v.2 - s.2) then (2 * (Real.pi : ℂ)) ^ 2 *
        ((v.1 : ℂ) ^ j * (-(v.1 : ℂ) - s.1) ^ k * a v * c (-v.1 - s.1, -v.2 - s.2)) else 0 := by
    intro u _
    by_cases h : u = (-v.1 - s.1, -v.2 - s.2)
    · rw [if_pos h, if_pos (by rw [h]; ext <;> simp <;> ring), h]; push_cast; ring
    · rw [if_neg h, if_neg (by
        intro h'; apply h
        have h1 := congrArg Prod.fst h'; have h2 := congrArg Prod.snd h'
        simp at h1 h2; ext <;> simp <;> linarith)]; ring
  rw [sum_congr rfl key, sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [hSc _ h]; ring

theorem continuous_trigK (l : List KCoef) : Continuous (trigK l) := by
  unfold trigK
  induction l with
  | nil => simp; exact continuous_const
  | cons u l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (continuous_const.mul (continuous_ex _)).add ih

theorem integral_trigK2 (ha : Function.HasFiniteSupport a) (hc : Function.HasFiniteSupport c)
    (l : List KCoef) (j k : ℕ) :
    ∫ p in BZ, trigK l p * (symb a j p * symb c k p) =
      (l.map fun t => (t.v : ℂ) * ∫ p in BZ, symb a j p * symb c k p * ex t.s p).sum := by
  induction l with
  | nil => simp [trigK]
  | cons t l ih =>
    simp only [trigK, List.map_cons, List.sum_cons] at ih ⊢
    have h1 : Continuous fun p => (t.v : ℂ) * ex t.s p * (symb a j p * symb c k p) :=
      (continuous_const.mul (continuous_ex _)).mul
        ((continuous_symb a ha j).mul (continuous_symb c hc k))
    have h2 : Continuous fun p => (l.map fun t => (t.v : ℂ) * ex t.s p).sum *
        (symb a j p * symb c k p) :=
      (continuous_trigK l).mul ((continuous_symb a ha j).mul (continuous_symb c hc k))
    have e : ∫ p in BZ, ((t.v : ℂ) * ex t.s p + (l.map fun t => (t.v : ℂ) * ex t.s p).sum) *
        (symb a j p * symb c k p) = (∫ p in BZ, (t.v : ℂ) * ex t.s p * (symb a j p * symb c k p)) +
        ∫ p in BZ, (l.map fun t => (t.v : ℂ) * ex t.s p).sum * (symb a j p * symb c k p) := by
      rw [← integral_add (h1.continuousOn.integrableOn_compact isCompact_BZ)
        (h2.continuousOn.integrableOn_compact isCompact_BZ)]
      congr 1; funext p; ring
    rw [e, ih, ← integral_const_mul]
    congr 2; funext p; ring

end Two

/-! ### The polarised bubble -/

/-- `𝔅x(a, c) = (2π)^{-2} [∫ trigK kap0 Â₀ Ĉ₀ + ∫ trigK kap2 Â₁ Ĉ₁]`. -/
def bubX (a c : ℤ × ℤ → ℂ) : ℂ := ((2 * (Real.pi : ℂ)) ^ 2)⁻¹ *
  ((∫ p in BZ, trigK kap0 p * (symb a 0 p * symb c 0 p)) +
    ∫ p in BZ, trigK kap2 p * (symb a 1 p * symb c 1 p))

theorem bubX_comm (a c : ℤ × ℤ → ℂ) : bubX a c = bubX c a := by
  unfold bubX; simp only [mul_comm (symb a _ _)]

/-- `(K f)(u) = ∑_{(s, κ) ∈ l} κ f(u - s)`. -/
def stK (l : List KCoef) (f : ℤ × ℤ → ℂ) (u : ℤ × ℤ) : ℂ :=
  (l.map fun t => (t.v : ℂ) * f (u.1 - t.s.1, u.2 - t.s.2)).sum

/-- The first moment `g(u) = u₀ f(u)`. -/
def mom0 (f : ℤ × ℤ → ℂ) (u : ℤ × ℤ) : ℂ := (u.1 : ℂ) * f u

theorem list_sum_finsum {l : List KCoef} (F : KCoef → ℤ × ℤ → ℂ)
    (hF : ∀ t ∈ l, Function.HasFiniteSupport (F t)) :
    (l.map fun t => ∑ᶠ v, F t v).sum = ∑ᶠ v, (l.map fun t => F t v).sum := by
  induction l with
  | nil => simp
  | cons t l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih (fun t' ht' => hF t' (List.mem_cons_of_mem _ ht'))]
    have h2 : Function.HasFiniteSupport fun v => (l.map fun t => F t v).sum := by
      clear ih
      induction l with
      | nil => simp [Function.HasFiniteSupport]
      | cons u l ih2 =>
        simp only [List.map_cons, List.sum_cons]
        exact (hF u (by simp)).add
          (ih2 (fun t' ht' => hF t' (by simp at ht' ⊢; tauto)))
    rw [finsum_add_distrib (hF t (by simp)) h2]

theorem list_sum_mul_left (l : List KCoef) (r : ℂ) (G : KCoef → ℂ) :
    (l.map fun t => (t.v : ℂ) * (r * G t)).sum = r * (l.map fun t => (t.v : ℂ) * G t).sum := by
  induction l with
  | nil => simp
  | cons t l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem list_sum_mul_mid (l : List KCoef) (r : ℂ) (G : KCoef → ℂ) :
    (l.map fun t => (t.v : ℂ) * r * G t).sum = r * (l.map fun t => (t.v : ℂ) * G t).sum := by
  induction l with
  | nil => simp
  | cons t l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- **The position form of `𝔅x`.**
`𝔅x(a, c) = ∑_v a(v) (K₀ c)(-v) + ∑_v v₀ a(v) (K₂ (u₀ c))(-v)`. -/
theorem bubX_pos (a c : ℤ × ℤ → ℂ) (ha : Function.HasFiniteSupport a)
    (hc : Function.HasFiniteSupport c) :
    bubX a c = (∑ᶠ v : ℤ × ℤ, a v * stK kap0 c (-v.1, -v.2)) +
      ∑ᶠ v : ℤ × ℤ, (v.1 : ℂ) * a v * stK kap2 (mom0 c) (-v.1, -v.2) := by
  have hpi : (2 * (Real.pi : ℂ)) ^ 2 ≠ 0 := by
    have := Real.pi_pos; exact pow_ne_zero _ (mul_ne_zero two_ne_zero (by exact_mod_cast this.ne'))
  unfold bubX
  rw [integral_trigK2 a c ha hc, integral_trigK2 a c ha hc]
  simp only [integral_symb_symb2 a c ha hc, ← mul_assoc, list_sum_mul_mid]
  rw [← mul_add, ← mul_assoc, inv_mul_cancel₀ hpi, one_mul]
  have hfs : ∀ (j k : ℕ) (t : KCoef), Function.HasFiniteSupport fun v : ℤ × ℤ =>
      (v.1 : ℂ) ^ j * (-(v.1 : ℂ) - t.s.1) ^ k * a v * c (-v.1 - t.s.1, -v.2 - t.s.2) :=
    fun j k t => Set.Finite.subset ha (fun v hv => by
      simp only [Function.mem_support, ne_eq] at hv ⊢
      intro h; apply hv; rw [h]; ring)
  have e1 : ∀ (l : List KCoef) (j k : ℕ), (l.map fun t => (t.v : ℂ) * ∑ᶠ v : ℤ × ℤ,
      (v.1 : ℂ) ^ j * (-(v.1 : ℂ) - t.s.1) ^ k * a v * c (-v.1 - t.s.1, -v.2 - t.s.2)).sum =
      ∑ᶠ v : ℤ × ℤ, (l.map fun t => (t.v : ℂ) *
        ((v.1 : ℂ) ^ j * (-(v.1 : ℂ) - t.s.1) ^ k * a v * c (-v.1 - t.s.1, -v.2 - t.s.2))).sum := by
    intro l j k
    have := list_sum_finsum (l := l) (fun t v => (t.v : ℂ) *
      ((v.1 : ℂ) ^ j * (-(v.1 : ℂ) - t.s.1) ^ k * a v * c (-v.1 - t.s.1, -v.2 - t.s.2)))
      (fun t _ => Set.Finite.subset (hfs j k t) (fun v hv => by
        simp only [Function.mem_support, ne_eq] at hv ⊢
        intro h; apply hv; rw [h]; ring))
    rw [← this]
    congr 1
    refine List.map_congr_left fun t _ => ?_
    rw [mul_finsum]
  rw [e1, e1]
  congr 1
  · refine finsum_congr fun v => ?_
    unfold stK
    rw [← list_sum_mul_left]
    congr 1
    refine List.map_congr_left fun t _ => ?_
    simp only [pow_zero, one_mul]
  · refine finsum_congr fun v => ?_
    unfold stK mom0
    rw [← list_sum_mul_left]
    congr 1
    refine List.map_congr_left fun t _ => ?_
    push_cast
    ring

/-- **`negBub = 𝔅x(c, c)`** for even `c` of range `R`. -/
theorem negBub_eq_bubX {L N : ℕ} [NeZero L] {c : ℤ × ℤ → ℂ} {R : ℕ}
    (hcR : ∀ u, R < nm u → c u = 0)
    (heven : ∀ v : ℤ × ℤ, c (-v.1, -v.2) = c v) (hn : 2 * (R + 4) < L ^ N)
    {C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ} (hC : ∀ a b, C a b = cTor c (a - b))
    {X : Finset (Lam 2 L N)} (hne : X.Nonempty)
    (hX : ∀ x ∈ X, 2 * (supNorm (x - base X) + R + 3) < L ^ N) :
    negBub C X 0 = bubX c c := by
  rw [negBub_momentum c hcR heven hn hC hne hX]; rfl

end

end Step2
