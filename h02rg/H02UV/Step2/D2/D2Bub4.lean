import Step2.D2.D2Bub3
import Step2.D2.D2Torus

/-!
# The bubble in momentum space (`prop:d2`, (R4))

For an even, finitely supported `c : ℤ² → ℂ` with Fourier symbols
`Â_j(p) = ∑_v v₀^j c(v) e^{i v·p}` (`symb c j`):

* `Tj_eq_integral`: `T_j(s) = ∑_v v₀^j c(v) c(v+s) = (2π)^{-2} ∫_{[-π,π]²} Â_j(p) Â_0(p) e^{i s·p} d²p`;
* `finsum_bubFZ_integral`: **the momentum form of the bubble**
  `∑_w bubFZ c w = (2π)^{-2} ∫_{[-π,π]²} Â_0(p) ∑_{(j,s)} T_{j,s} e^{i s·p} Â_j(p) d²p`.
-/

namespace Step2

open Finset MeasureTheory Step2.D2

noncomputable section

section Mom

variable (c : ℤ × ℤ → ℂ)

/-- `Â_j(p) = ∑_v v₀^j c(v) e^{i v·p}`. -/
def symb (j : ℕ) (p : ℂ) : ℂ := ∑ᶠ v : ℤ × ℤ, (v.1 : ℂ) ^ j * c v * ex v p

theorem hfs_symb (hc : Function.HasFiniteSupport c) (j : ℕ) (p : ℂ) :
    Function.HasFiniteSupport (fun v : ℤ × ℤ => (v.1 : ℂ) ^ j * c v * ex v p) :=
  Set.Finite.subset hc (fun v hv => by
    simp only [Function.mem_support, ne_eq] at hv ⊢
    intro h; apply hv; rw [h]; ring)

theorem symb_eq_sum (hc : Function.HasFiniteSupport c) (j : ℕ) (p : ℂ) :
    symb c j p = ∑ v ∈ hc.toFinset, (v.1 : ℂ) ^ j * c v * ex v p := by
  rw [symb, finsum_eq_sum_of_support_subset _ (s := hc.toFinset)]
  intro v hv
  simp only [Function.mem_support, ne_eq] at hv
  simp only [Set.Finite.coe_toFinset, Function.mem_support, ne_eq]
  intro h; apply hv; rw [h]; ring

theorem integrableOn_ex (a : ℤ × ℤ) : IntegrableOn (ex a) BZ :=
  (continuous_ex a).continuousOn.integrableOn_compact isCompact_BZ

theorem continuous_symb (hc : Function.HasFiniteSupport c) (j : ℕ) : Continuous (symb c j) := by
  have : symb c j = fun p => ∑ v ∈ hc.toFinset, (v.1 : ℂ) ^ j * c v * ex v p := by
    funext p; exact symb_eq_sum c hc j p
  rw [this]
  exact continuous_finset_sum _ fun v _ => continuous_const.mul (continuous_ex v)

/-! ### Relations among the `T_j(s)` and the symmetric form -/

theorem Tj_one (hc : Function.HasFiniteSupport c) (heven : ∀ v : ℤ × ℤ, c (-v.1, -v.2) = c v)
    (s : ℤ × ℤ) : Tj c 1 s = -((s.1 : ℂ) / 2) * Tj c 0 s := by
  have h : Tj c 1 s = ∑ᶠ v : ℤ × ℤ, (-(v.1 : ℂ) - s.1) * c v * c (v.1 + s.1, v.2 + s.2) := by
    rw [Tj, ← finsum_comp_equiv (affEquiv (-1) (by norm_num) (-s.1, -s.2))]
    refine finsum_congr fun v => ?_
    simp only [affEquiv, Equiv.coe_fn_mk]
    have e1 : (-1 * v.1 + -s.1, -1 * v.2 + -s.2) = (-(v.1 + s.1), -(v.2 + s.2)) := by
      ext <;> simp <;> ring
    have e2 : (-1 * v.1 + -s.1 + s.1, -1 * v.2 + -s.2 + s.2) = (-v.1, -v.2) := by
      ext <;> simp
    rw [e1, e2, heven, heven (v.1 + s.1, v.2 + s.2)]
    push_cast; ring
  have f0 := hfs_Tj c hc 0 s
  have f1 := hfs_Tj c hc 1 s
  have h2 : ∑ᶠ v : ℤ × ℤ, (-(v.1 : ℂ) - s.1) * c v * c (v.1 + s.1, v.2 + s.2) =
      -Tj c 1 s - s.1 * Tj c 0 s := by
    have hA : Function.HasFiniteSupport (fun v : ℤ × ℤ =>
        -((v.1 : ℂ) ^ 1 * c v * c (v.1 + s.1, v.2 + s.2))) := f1.neg
    have hB := hfs_const_mul f0 (s.1 : ℂ)
    calc _ = ∑ᶠ v : ℤ × ℤ, (-((v.1 : ℂ) ^ 1 * c v * c (v.1 + s.1, v.2 + s.2)) -
          (s.1 : ℂ) * ((v.1 : ℂ) ^ 0 * c v * c (v.1 + s.1, v.2 + s.2))) :=
          finsum_congr fun v => by ring
      _ = _ := by
          rw [finsum_sub_distrib (f := fun v : ℤ × ℤ =>
            -((v.1 : ℂ) ^ 1 * c v * c (v.1 + s.1, v.2 + s.2)))
            (g := fun v : ℤ × ℤ => (s.1 : ℂ) * ((v.1 : ℂ) ^ 0 * c v * c (v.1 + s.1, v.2 + s.2)))
            hA hB, finsum_neg_distrib, ← mul_finsum]
          rfl
  rw [h2] at h
  linear_combination h / 2

theorem Tj_neg0 (heven : ∀ v : ℤ × ℤ, c (-v.1, -v.2) = c v) (s : ℤ × ℤ) :
    Tj c 0 (-s.1, -s.2) = Tj c 0 s := by
  rw [Tj, ← finsum_comp_equiv (affEquiv 1 (by norm_num) s)]
  rw [Tj, ← finsum_comp_equiv (Equiv.refl (ℤ × ℤ))]
  refine finsum_congr fun v => ?_
  simp only [affEquiv, Equiv.coe_fn_mk, Equiv.refl_apply, one_mul, pow_zero]
  have e : (v.1 + s.1 + -s.1, v.2 + s.2 + -s.2) = v := by ext <;> simp
  rw [e]; ring

theorem Tj_neg2 (heven : ∀ v : ℤ × ℤ, c (-v.1, -v.2) = c v) (s : ℤ × ℤ) :
    Tj c 2 (-s.1, -s.2) = Tj c 2 s := by
  rw [Tj, ← finsum_comp_equiv (Equiv.neg (ℤ × ℤ)), Tj]
  refine finsum_congr fun v => ?_
  simp only [Equiv.neg_apply]
  have e1 : ((-v).1 + -s.1, (-v).2 + -s.2) = (-(v.1 + s.1), -(v.2 + s.2)) := by
    ext <;> simp <;> ring
  rw [e1, heven (v.1 + s.1, v.2 + s.2), show (-v : ℤ × ℤ) = (-v.1, -v.2) from rfl, heven]
  push_cast; ring

/-- `∫ Â_j Â_k e^{i s·p} = (2π)² ∑_v v₀^j (-v₀ - s₀)^k c(v) c(-v - s)`. -/
theorem integral_symb_symb (hc : Function.HasFiniteSupport c) (j k : ℕ) (s : ℤ × ℤ) :
    ∫ p in BZ, symb c j p * symb c k p * ex s p = (2 * (Real.pi : ℂ)) ^ 2 *
      ∑ᶠ v : ℤ × ℤ, (v.1 : ℂ) ^ j * (-(v.1 : ℂ) - s.1) ^ k * c v * c (-v.1 - s.1, -v.2 - s.2) := by
  set S := hc.toFinset
  have hS : ∀ u, u ∉ S → c u = 0 := by
    intro u hu
    simp only [S, Set.Finite.mem_toFinset, Function.mem_support, ne_eq, not_not] at hu
    exact hu
  have hint : ∀ p, symb c j p * symb c k p * ex s p =
      ∑ v ∈ S, ∑ u ∈ S, ((v.1 : ℂ) ^ j * c v * ((u.1 : ℂ) ^ k * c u)) * ex (v + u + s) p := by
    intro p
    rw [symb_eq_sum c hc, symb_eq_sum c hc, sum_mul, sum_mul]
    refine sum_congr rfl fun v _ => ?_
    rw [mul_sum, sum_mul]
    refine sum_congr rfl fun u _ => ?_
    rw [← ex_add, ← ex_add]; ring
  simp_rw [hint]
  rw [integral_finset_sum _ fun v _ => integrable_finset_sum _ fun u _ =>
    (integrableOn_ex _).const_mul _]
  simp_rw [integral_finset_sum _ fun u _ => (integrableOn_ex _).const_mul _]
  simp_rw [integral_const_mul, integral_ex_BZ]
  have hfs : Function.HasFiniteSupport (fun v : ℤ × ℤ => (v.1 : ℂ) ^ j * (-(v.1 : ℂ) - s.1) ^ k *
      c v * c (-v.1 - s.1, -v.2 - s.2)) :=
    Set.Finite.subset hc (fun v hv => by
      simp only [Function.mem_support, ne_eq] at hv ⊢
      intro h; apply hv; rw [h]; ring)
  rw [finsum_eq_sum_of_support_subset _ (s := S) (by
    intro v hv
    simp only [Function.mem_support, ne_eq] at hv
    simp only [S, Set.Finite.coe_toFinset, Function.mem_support, ne_eq]
    intro h; apply hv; rw [h]; ring), mul_sum]
  refine sum_congr rfl fun v _ => ?_
  have key : ∀ u ∈ S, ((v.1 : ℂ) ^ j * c v * ((u.1 : ℂ) ^ k * c u)) *
      (if v + u + s = 0 then (2 * (Real.pi : ℂ)) ^ 2 else 0) =
      if u = (-v.1 - s.1, -v.2 - s.2) then (2 * (Real.pi : ℂ)) ^ 2 *
        ((v.1 : ℂ) ^ j * (-(v.1 : ℂ) - s.1) ^ k * c v * c (-v.1 - s.1, -v.2 - s.2)) else 0 := by
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
  · rw [hS _ h]; ring

/-- A coefficient `κ(s) e^{i s·p}`. -/
structure KCoef where
  s : ℤ × ℤ
  v : ℚ

/-- `4 sin² p₀ - 2λ(p) = ∑ κ₀(s) e^{i s·p}`. -/
def kap0 : List KCoef := [⟨((-2), 0), (-1)⟩, ⟨((-1), 0), 2⟩, ⟨(0, (-1)), 2⟩, ⟨(0, 0), (-6)⟩, ⟨(0, 1), 2⟩, ⟨(1, 0), 2⟩, ⟨(2, 0), (-1)⟩]

/-- `λ(p)²/2 = ∑ κ₂(s) e^{i s·p}`. -/
def kap2 : List KCoef := [⟨((-2), 0), (1/2)⟩, ⟨((-1), (-1)), 1⟩, ⟨((-1), 0), (-4)⟩, ⟨((-1), 1), 1⟩, ⟨(0, (-2)), (1/2)⟩, ⟨(0, (-1)), (-4)⟩, ⟨(0, 0), 10⟩, ⟨(0, 1), (-4)⟩, ⟨(0, 2), (1/2)⟩, ⟨(1, (-1)), 1⟩, ⟨(1, 0), (-4)⟩, ⟨(1, 1), 1⟩, ⟨(2, 0), (1/2)⟩]

/-- The trigonometric polynomial `∑ κ(s) e^{i s·p}`. -/
def trigK (l : List KCoef) (p : ℂ) : ℂ := (l.map fun t => (t.v : ℂ) * ex t.s p).sum

theorem integral_trigK (hc : Function.HasFiniteSupport c) (l : List KCoef) (j k : ℕ) :
    ∫ p in BZ, trigK l p * (symb c j p * symb c k p) =
      (l.map fun t => (t.v : ℂ) * ∫ p in BZ, symb c j p * symb c k p * ex t.s p).sum := by
  induction l with
  | nil => simp [trigK]
  | cons t l ih =>
    simp only [trigK, List.map_cons, List.sum_cons] at ih ⊢
    have h1 : Continuous fun p => (t.v : ℂ) * ex t.s p * (symb c j p * symb c k p) :=
      (continuous_const.mul (continuous_ex _)).mul
        ((continuous_symb c hc j).mul (continuous_symb c hc k))
    have h2 : Continuous fun p => (l.map fun t => (t.v : ℂ) * ex t.s p).sum *
        (symb c j p * symb c k p) := by
      refine Continuous.mul ?_ ((continuous_symb c hc j).mul (continuous_symb c hc k))
      clear ih
      induction l with
      | nil => simp; exact continuous_const
      | cons u l ih2 =>
        simp only [List.map_cons, List.sum_cons]
        exact (continuous_const.mul (continuous_ex _)).add ih2
    have e : ∫ p in BZ, ((t.v : ℂ) * ex t.s p + (l.map fun t => (t.v : ℂ) * ex t.s p).sum) *
        (symb c j p * symb c k p) = (∫ p in BZ, (t.v : ℂ) * ex t.s p * (symb c j p * symb c k p)) +
        ∫ p in BZ, (l.map fun t => (t.v : ℂ) * ex t.s p).sum * (symb c j p * symb c k p) := by
      rw [← integral_add (h1.continuousOn.integrableOn_compact isCompact_BZ)
        (h2.continuousOn.integrableOn_compact isCompact_BZ)]
      congr 1; funext p; ring
    rw [e, ih, ← integral_const_mul]
    congr 2; funext p; ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The momentum form of the bubble, symmetric version.** For even, finitely supported `c`,
`∑_w bubFZ c w = 8 (2π)^{-2} ∫_{[-π,π]²} [(4 sin² p₀ - 2λ) Â_0² + (λ²/2) Â_1²] d²p`,
with the trigonometric polynomials written as `trigK kap0`, `trigK kap2`. -/
theorem finsum_bubFZ_sym (hc : Function.HasFiniteSupport c)
    (heven : ∀ v : ℤ × ℤ, c (-v.1, -v.2) = c v) :
    ∑ᶠ w : ℤ × ℤ, bubFZ c w = 8 * ((2 * (Real.pi : ℂ)) ^ 2)⁻¹ *
      ((∫ p in BZ, trigK kap0 p * (symb c 0 p * symb c 0 p)) +
        ∫ p in BZ, trigK kap2 p * (symb c 1 p * symb c 1 p)) := by
  have hpi : (2 * (Real.pi : ℂ)) ^ 2 ≠ 0 := by
    have := Real.pi_pos; exact pow_ne_zero _ (mul_ne_zero two_ne_zero (by exact_mod_cast this.ne'))
  rw [finsum_bubFZ c hc heven, integral_trigK c hc, integral_trigK c hc]
  simp only [integral_symb_symb c hc]
  have ev2 : ∀ s : ℤ × ℤ, ∑ᶠ v : ℤ × ℤ, (v.1 : ℂ) ^ 0 * (-(v.1 : ℂ) - s.1) ^ 0 * c v *
      c (-v.1 - s.1, -v.2 - s.2) = Tj c 0 s := by
    intro s; rw [Tj]; refine finsum_congr fun v => ?_
    rw [show (-v.1 - s.1, -v.2 - s.2) = (-(v.1 + s.1), -(v.2 + s.2)) by ext <;> simp <;> ring,
      heven (v.1 + s.1, v.2 + s.2)]; ring
  have ev1 : ∀ s : ℤ × ℤ, ∑ᶠ v : ℤ × ℤ, (v.1 : ℂ) ^ 1 * (-(v.1 : ℂ) - s.1) ^ 1 * c v *
      c (-v.1 - s.1, -v.2 - s.2) = -Tj c 2 s - s.1 * Tj c 1 s := by
    intro s
    have f1 := hfs_Tj c hc 1 s
    have f2 := hfs_Tj c hc 2 s
    have hA : Function.HasFiniteSupport (fun v : ℤ × ℤ =>
        -((v.1 : ℂ) ^ 2 * c v * c (v.1 + s.1, v.2 + s.2))) := f2.neg
    have hB := hfs_const_mul f1 (s.1 : ℂ)
    calc _ = ∑ᶠ v : ℤ × ℤ, (-((v.1 : ℂ) ^ 2 * c v * c (v.1 + s.1, v.2 + s.2)) -
          (s.1 : ℂ) * ((v.1 : ℂ) ^ 1 * c v * c (v.1 + s.1, v.2 + s.2))) :=
          finsum_congr fun v => by
            rw [show (-v.1 - s.1, -v.2 - s.2) = (-(v.1 + s.1), -(v.2 + s.2)) by
              ext <;> simp <;> ring, heven (v.1 + s.1, v.2 + s.2)]; ring
      _ = _ := by
          rw [finsum_sub_distrib (f := fun v : ℤ × ℤ =>
            -((v.1 : ℂ) ^ 2 * c v * c (v.1 + s.1, v.2 + s.2)))
            (g := fun v : ℤ × ℤ => (s.1 : ℂ) * ((v.1 : ℂ) ^ 1 * c v * c (v.1 + s.1, v.2 + s.2)))
            hA hB, finsum_neg_distrib, ← mul_finsum]
          rfl
  simp only [ev1, ev2]
  have r0 : Tj c 1 ((-2), 0) = -((-2 : ℂ) / 2) * Tj c 0 ((-2), 0) := by
    have := Tj_one c hc heven ((-2), 0); push_cast at this; exact this
  have r1 : Tj c 1 ((-1), (-1)) = -((-1 : ℂ) / 2) * Tj c 0 ((-1), (-1)) := by
    have := Tj_one c hc heven ((-1), (-1)); push_cast at this; exact this
  have r2 : Tj c 1 ((-1), 0) = -((-1 : ℂ) / 2) * Tj c 0 ((-1), 0) := by
    have := Tj_one c hc heven ((-1), 0); push_cast at this; exact this
  have r3 : Tj c 1 ((-1), 1) = -((-1 : ℂ) / 2) * Tj c 0 ((-1), 1) := by
    have := Tj_one c hc heven ((-1), 1); push_cast at this; exact this
  have r4 : Tj c 1 (0, (-2)) = -((0 : ℂ) / 2) * Tj c 0 (0, (-2)) := by
    have := Tj_one c hc heven (0, (-2)); push_cast at this; exact this
  have r5 : Tj c 1 (0, (-1)) = -((0 : ℂ) / 2) * Tj c 0 (0, (-1)) := by
    have := Tj_one c hc heven (0, (-1)); push_cast at this; exact this
  have r6 : Tj c 1 (0, 0) = -((0 : ℂ) / 2) * Tj c 0 (0, 0) := by
    have := Tj_one c hc heven (0, 0); push_cast at this; exact this
  have r7 : Tj c 1 (0, 1) = -((0 : ℂ) / 2) * Tj c 0 (0, 1) := by
    have := Tj_one c hc heven (0, 1); push_cast at this; exact this
  have r8 : Tj c 1 (0, 2) = -((0 : ℂ) / 2) * Tj c 0 (0, 2) := by
    have := Tj_one c hc heven (0, 2); push_cast at this; exact this
  have r9 : Tj c 1 (1, (-1)) = -((1 : ℂ) / 2) * Tj c 0 (1, (-1)) := by
    have := Tj_one c hc heven (1, (-1)); push_cast at this; exact this
  have r10 : Tj c 1 (1, 0) = -((1 : ℂ) / 2) * Tj c 0 (1, 0) := by
    have := Tj_one c hc heven (1, 0); push_cast at this; exact this
  have r11 : Tj c 1 (1, 1) = -((1 : ℂ) / 2) * Tj c 0 (1, 1) := by
    have := Tj_one c hc heven (1, 1); push_cast at this; exact this
  have r12 : Tj c 1 (2, 0) = -((2 : ℂ) / 2) * Tj c 0 (2, 0) := by
    have := Tj_one c hc heven (2, 0); push_cast at this; exact this
  have r13 : Tj c 0 ((-2), 0) = Tj c 0 (2, 0) := by
    have := Tj_neg0 c heven (2, 0); simpa using this
  have r14 : Tj c 0 ((-1), (-1)) = Tj c 0 (1, 1) := by
    have := Tj_neg0 c heven (1, 1); simpa using this
  have r15 : Tj c 0 ((-1), 0) = Tj c 0 (1, 0) := by
    have := Tj_neg0 c heven (1, 0); simpa using this
  have r16 : Tj c 0 ((-1), 1) = Tj c 0 (1, (-1)) := by
    have := Tj_neg0 c heven (1, (-1)); simpa using this
  have r17 : Tj c 0 (0, (-2)) = Tj c 0 (0, 2) := by
    have := Tj_neg0 c heven (0, 2); simpa using this
  have r18 : Tj c 0 (0, (-1)) = Tj c 0 (0, 1) := by
    have := Tj_neg0 c heven (0, 1); simpa using this
  have r19 : Tj c 2 ((-2), 0) = Tj c 2 (2, 0) := by
    have := Tj_neg2 c heven (2, 0); simpa using this
  have r20 : Tj c 2 ((-1), (-1)) = Tj c 2 (1, 1) := by
    have := Tj_neg2 c heven (1, 1); simpa using this
  have r21 : Tj c 2 ((-1), 0) = Tj c 2 (1, 0) := by
    have := Tj_neg2 c heven (1, 0); simpa using this
  have r22 : Tj c 2 ((-1), 1) = Tj c 2 (1, (-1)) := by
    have := Tj_neg2 c heven (1, (-1)); simpa using this
  have r23 : Tj c 2 (0, (-2)) = Tj c 2 (0, 2) := by
    have := Tj_neg2 c heven (0, 2); simpa using this
  have r24 : Tj c 2 (0, (-1)) = Tj c 2 (0, 1) := by
    have := Tj_neg2 c heven (0, 1); simpa using this
  simp only [bubT, kap0, kap2, List.map, List.sum_cons, List.sum_nil]
  norm_num
  simp only [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24]
  field_simp
  ring

end Mom

end

end Step2
