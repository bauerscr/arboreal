import Step2.D2.D2Bub2

/-!
# The bubble on `ℤ²`: position-space normal form (`prop:d2`, (R4))

For an even kernel `c : ℤ² → ℂ` (`d = 2`, direction `κ = 0`):

* `bubFZ c w`: the density `bubF` of `D2Bub2` on `ℤ²`;
* `bubFZ_eq`: `bubFZ c w = ∑_t coef_t w₀^{k_t} c(ε_t w + a_t) c(ε'_t w + b_t)` (140 explicit terms);
* `sum_bubFZ`: `∑_w bubFZ c w = ∑_{(j,s)} T_{j,s} ∑_v v₀^j c(v) c(v + s)` (28 explicit terms).
-/

namespace Step2

open Finset

noncomputable section

/-- The unit vectors `±e_i` of `ℤ²` (`pmdir i t`). -/
def dZ (i : Fin 2) (t : Fin 2) : ℤ × ℤ :=
  if i = 0 then (if t = 0 then (1, 0) else (-1, 0)) else (if t = 0 then (0, 1) else (0, -1))

/-- The density of `D2Bub2.bubF` on `ℤ²`, direction `κ = 0`. -/
def bubFZ (c : ℤ × ℤ → ℂ) (w : ℤ × ℤ) : ℂ :=
  ∑ i' : Fin 2, ∑ t' : Fin 2, ∑ i : Fin 2, ∑ t : Fin 2,
    bubPoly (fun a b : ℤ × ℤ => c (a.1 - b.1, a.2 - b.2)) 0 (dZ i t) w (w + dZ i' t')
      0 ((dZ i t).1 : ℂ) (w.1 : ℂ) ((w.1 : ℂ) + ((dZ i' t').1 : ℂ))

/-- A term `coef · w₀^k · c(ε w + a) · c(ε' w + b)`. -/
structure BTerm where
  coef : ℤ
  k : ℕ
  e1 : ℤ
  a : ℤ × ℤ
  e2 : ℤ
  b : ℤ × ℤ

/-- The value of a term. -/
def BTerm.val (c : ℤ × ℤ → ℂ) (w : ℤ × ℤ) (t : BTerm) : ℂ :=
  (t.coef : ℂ) * (w.1 : ℂ) ^ t.k * c (t.e1 * w.1 + t.a.1, t.e1 * w.2 + t.a.2) *
    c (t.e2 * w.1 + t.b.1, t.e2 * w.2 + t.b.2)

/-- The 140 terms of `bubFZ`. -/
def bubTerms : List BTerm :=
  [⟨(-1), 0, (-1), ((-2), 0), (-1), (0, 0)⟩,
    ⟨(-1), 0, (-1), ((-2), 0), 1, (0, 0)⟩,
    ⟨1, 0, (-1), ((-1), 0), (-1), ((-1), 0)⟩,
    ⟨(-2), 0, (-1), ((-1), 0), (-1), (1, 0)⟩,
    ⟨4, 0, (-1), ((-1), 0), 1, (0, 0)⟩,
    ⟨(-4), 0, (-1), ((-1), 0), 1, (1, 0)⟩,
    ⟨4, 0, (-1), (0, (-1)), 1, (0, 0)⟩,
    ⟨(-4), 0, (-1), (0, (-1)), 1, (0, 1)⟩,
    ⟨2, 0, (-1), (0, 0), (-1), (0, 0)⟩,
    ⟨(-1), 0, (-1), (0, 0), (-1), (2, 0)⟩,
    ⟨(-1), 0, (-1), (0, 0), 1, ((-2), 0)⟩,
    ⟨4, 0, (-1), (0, 0), 1, ((-1), 0)⟩,
    ⟨4, 0, (-1), (0, 0), 1, (0, (-1))⟩,
    ⟨(-12), 0, (-1), (0, 0), 1, (0, 0)⟩,
    ⟨4, 0, (-1), (0, 0), 1, (0, 1)⟩,
    ⟨4, 0, (-1), (0, 0), 1, (1, 0)⟩,
    ⟨(-1), 0, (-1), (0, 0), 1, (2, 0)⟩,
    ⟨(-4), 0, (-1), (0, 1), 1, (0, (-1))⟩,
    ⟨4, 0, (-1), (0, 1), 1, (0, 0)⟩,
    ⟨1, 0, (-1), (1, 0), (-1), (1, 0)⟩,
    ⟨(-4), 0, (-1), (1, 0), 1, ((-1), 0)⟩,
    ⟨4, 0, (-1), (1, 0), 1, (0, 0)⟩,
    ⟨(-1), 0, (-1), (2, 0), 1, (0, 0)⟩,
    ⟨(-1), 0, 1, ((-2), 0), 1, (0, 0)⟩,
    ⟨1, 0, 1, ((-1), 0), 1, ((-1), 0)⟩,
    ⟨(-2), 0, 1, ((-1), 0), 1, (1, 0)⟩,
    ⟨2, 0, 1, (0, 0), 1, (0, 0)⟩,
    ⟨(-1), 0, 1, (0, 0), 1, (2, 0)⟩,
    ⟨1, 0, 1, (1, 0), 1, (1, 0)⟩,
    ⟨(-2), 1, (-1), ((-2), 0), 1, (0, 0)⟩,
    ⟨2, 1, (-1), ((-2), 0), 1, (1, 0)⟩,
    ⟨(-2), 1, (-1), ((-1), (-1)), 1, (0, 0)⟩,
    ⟨2, 1, (-1), ((-1), (-1)), 1, (0, 1)⟩,
    ⟨(-2), 1, (-1), ((-1), 0), 1, (0, (-1))⟩,
    ⟨6, 1, (-1), ((-1), 0), 1, (0, 0)⟩,
    ⟨(-2), 1, (-1), ((-1), 0), 1, (0, 1)⟩,
    ⟨(-4), 1, (-1), ((-1), 0), 1, (1, 0)⟩,
    ⟨2, 1, (-1), ((-1), 0), 1, (2, 0)⟩,
    ⟨2, 1, (-1), ((-1), 1), 1, (0, (-1))⟩,
    ⟨(-2), 1, (-1), ((-1), 1), 1, (0, 0)⟩,
    ⟨2, 1, (-1), (0, (-1)), 1, ((-1), 0)⟩,
    ⟨(-2), 1, (-1), (0, (-1)), 1, ((-1), 1)⟩,
    ⟨(-2), 1, (-1), (0, (-1)), 1, (1, 0)⟩,
    ⟨2, 1, (-1), (0, (-1)), 1, (1, 1)⟩,
    ⟨2, 1, (-1), (0, 0), 1, ((-2), 0)⟩,
    ⟨2, 1, (-1), (0, 0), 1, ((-1), (-1))⟩,
    ⟨(-6), 1, (-1), (0, 0), 1, ((-1), 0)⟩,
    ⟨2, 1, (-1), (0, 0), 1, ((-1), 1)⟩,
    ⟨(-2), 1, (-1), (0, 0), 1, (1, (-1))⟩,
    ⟨6, 1, (-1), (0, 0), 1, (1, 0)⟩,
    ⟨(-2), 1, (-1), (0, 0), 1, (1, 1)⟩,
    ⟨(-2), 1, (-1), (0, 0), 1, (2, 0)⟩,
    ⟨(-2), 1, (-1), (0, 1), 1, ((-1), (-1))⟩,
    ⟨2, 1, (-1), (0, 1), 1, ((-1), 0)⟩,
    ⟨2, 1, (-1), (0, 1), 1, (1, (-1))⟩,
    ⟨(-2), 1, (-1), (0, 1), 1, (1, 0)⟩,
    ⟨2, 1, (-1), (1, (-1)), 1, (0, 0)⟩,
    ⟨(-2), 1, (-1), (1, (-1)), 1, (0, 1)⟩,
    ⟨(-2), 1, (-1), (1, 0), 1, ((-2), 0)⟩,
    ⟨4, 1, (-1), (1, 0), 1, ((-1), 0)⟩,
    ⟨2, 1, (-1), (1, 0), 1, (0, (-1))⟩,
    ⟨(-6), 1, (-1), (1, 0), 1, (0, 0)⟩,
    ⟨2, 1, (-1), (1, 0), 1, (0, 1)⟩,
    ⟨(-2), 1, (-1), (1, 1), 1, (0, (-1))⟩,
    ⟨2, 1, (-1), (1, 1), 1, (0, 0)⟩,
    ⟨(-2), 1, (-1), (2, 0), 1, ((-1), 0)⟩,
    ⟨2, 1, (-1), (2, 0), 1, (0, 0)⟩,
    ⟨(-1), 2, (-1), ((-2), 0), 1, (0, 0)⟩,
    ⟨2, 2, (-1), ((-2), 0), 1, (1, 0)⟩,
    ⟨(-1), 2, (-1), ((-2), 0), 1, (2, 0)⟩,
    ⟨(-2), 2, (-1), ((-1), (-1)), 1, (0, 0)⟩,
    ⟨2, 2, (-1), ((-1), (-1)), 1, (0, 1)⟩,
    ⟨2, 2, (-1), ((-1), (-1)), 1, (1, 0)⟩,
    ⟨(-2), 2, (-1), ((-1), (-1)), 1, (1, 1)⟩,
    ⟨(-2), 2, (-1), ((-1), 0), 1, ((-1), 0)⟩,
    ⟨(-2), 2, (-1), ((-1), 0), 1, (0, (-1))⟩,
    ⟨10, 2, (-1), ((-1), 0), 1, (0, 0)⟩,
    ⟨(-2), 2, (-1), ((-1), 0), 1, (0, 1)⟩,
    ⟨2, 2, (-1), ((-1), 0), 1, (1, (-1))⟩,
    ⟨(-10), 2, (-1), ((-1), 0), 1, (1, 0)⟩,
    ⟨2, 2, (-1), ((-1), 0), 1, (1, 1)⟩,
    ⟨2, 2, (-1), ((-1), 0), 1, (2, 0)⟩,
    ⟨2, 2, (-1), ((-1), 1), 1, (0, (-1))⟩,
    ⟨(-2), 2, (-1), ((-1), 1), 1, (0, 0)⟩,
    ⟨(-2), 2, (-1), ((-1), 1), 1, (1, (-1))⟩,
    ⟨2, 2, (-1), ((-1), 1), 1, (1, 0)⟩,
    ⟨(-1), 2, (-1), (0, (-2)), 1, (0, 0)⟩,
    ⟨2, 2, (-1), (0, (-2)), 1, (0, 1)⟩,
    ⟨(-1), 2, (-1), (0, (-2)), 1, (0, 2)⟩,
    ⟨(-2), 2, (-1), (0, (-1)), 1, ((-1), 0)⟩,
    ⟨2, 2, (-1), (0, (-1)), 1, ((-1), 1)⟩,
    ⟨(-2), 2, (-1), (0, (-1)), 1, (0, (-1))⟩,
    ⟨10, 2, (-1), (0, (-1)), 1, (0, 0)⟩,
    ⟨(-10), 2, (-1), (0, (-1)), 1, (0, 1)⟩,
    ⟨2, 2, (-1), (0, (-1)), 1, (0, 2)⟩,
    ⟨(-2), 2, (-1), (0, (-1)), 1, (1, 0)⟩,
    ⟨2, 2, (-1), (0, (-1)), 1, (1, 1)⟩,
    ⟨(-1), 2, (-1), (0, 0), 1, ((-2), 0)⟩,
    ⟨(-2), 2, (-1), (0, 0), 1, ((-1), (-1))⟩,
    ⟨10, 2, (-1), (0, 0), 1, ((-1), 0)⟩,
    ⟨(-2), 2, (-1), (0, 0), 1, ((-1), 1)⟩,
    ⟨(-1), 2, (-1), (0, 0), 1, (0, (-2))⟩,
    ⟨10, 2, (-1), (0, 0), 1, (0, (-1))⟩,
    ⟨(-28), 2, (-1), (0, 0), 1, (0, 0)⟩,
    ⟨10, 2, (-1), (0, 0), 1, (0, 1)⟩,
    ⟨(-1), 2, (-1), (0, 0), 1, (0, 2)⟩,
    ⟨(-2), 2, (-1), (0, 0), 1, (1, (-1))⟩,
    ⟨10, 2, (-1), (0, 0), 1, (1, 0)⟩,
    ⟨(-2), 2, (-1), (0, 0), 1, (1, 1)⟩,
    ⟨(-1), 2, (-1), (0, 0), 1, (2, 0)⟩,
    ⟨2, 2, (-1), (0, 1), 1, ((-1), (-1))⟩,
    ⟨(-2), 2, (-1), (0, 1), 1, ((-1), 0)⟩,
    ⟨2, 2, (-1), (0, 1), 1, (0, (-2))⟩,
    ⟨(-10), 2, (-1), (0, 1), 1, (0, (-1))⟩,
    ⟨10, 2, (-1), (0, 1), 1, (0, 0)⟩,
    ⟨(-2), 2, (-1), (0, 1), 1, (0, 1)⟩,
    ⟨2, 2, (-1), (0, 1), 1, (1, (-1))⟩,
    ⟨(-2), 2, (-1), (0, 1), 1, (1, 0)⟩,
    ⟨(-1), 2, (-1), (0, 2), 1, (0, (-2))⟩,
    ⟨2, 2, (-1), (0, 2), 1, (0, (-1))⟩,
    ⟨(-1), 2, (-1), (0, 2), 1, (0, 0)⟩,
    ⟨2, 2, (-1), (1, (-1)), 1, ((-1), 0)⟩,
    ⟨(-2), 2, (-1), (1, (-1)), 1, ((-1), 1)⟩,
    ⟨(-2), 2, (-1), (1, (-1)), 1, (0, 0)⟩,
    ⟨2, 2, (-1), (1, (-1)), 1, (0, 1)⟩,
    ⟨2, 2, (-1), (1, 0), 1, ((-2), 0)⟩,
    ⟨2, 2, (-1), (1, 0), 1, ((-1), (-1))⟩,
    ⟨(-10), 2, (-1), (1, 0), 1, ((-1), 0)⟩,
    ⟨2, 2, (-1), (1, 0), 1, ((-1), 1)⟩,
    ⟨(-2), 2, (-1), (1, 0), 1, (0, (-1))⟩,
    ⟨10, 2, (-1), (1, 0), 1, (0, 0)⟩,
    ⟨(-2), 2, (-1), (1, 0), 1, (0, 1)⟩,
    ⟨(-2), 2, (-1), (1, 0), 1, (1, 0)⟩,
    ⟨(-2), 2, (-1), (1, 1), 1, ((-1), (-1))⟩,
    ⟨2, 2, (-1), (1, 1), 1, ((-1), 0)⟩,
    ⟨2, 2, (-1), (1, 1), 1, (0, (-1))⟩,
    ⟨(-2), 2, (-1), (1, 1), 1, (0, 0)⟩,
    ⟨(-1), 2, (-1), (2, 0), 1, ((-2), 0)⟩,
    ⟨2, 2, (-1), (2, 0), 1, ((-1), 0)⟩,
    ⟨(-1), 2, (-1), (2, 0), 1, (0, 0)⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The pointwise normal form of the bubble density.** -/
theorem bubFZ_eq (c : ℤ × ℤ → ℂ) (w : ℤ × ℤ) :
    bubFZ c w = (bubTerms.map (BTerm.val c w)).sum := by
  obtain ⟨w1, w2⟩ := w
  simp only [bubFZ, Fin.sum_univ_two, dZ, Fin.isValue, if_true, Fin.one_eq_zero_iff,
    one_ne_zero, if_false]
  simp only [bubPoly, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero]
  simp only [bubTerms, List.map, List.sum_cons, List.sum_nil, BTerm.val]
  push_cast
  ring_nf

/-! ### Sums over `ℤ²` -/

section Sums

variable (c : ℤ × ℤ → ℂ)

/-- `T_j(s) = ∑_v v₀^j c(v) c(v + s)`. -/
def Tj (j : ℕ) (s : ℤ × ℤ) : ℂ := ∑ᶠ v : ℤ × ℤ, (v.1 : ℂ) ^ j * c v * c (v.1 + s.1, v.2 + s.2)

/-- The affine map `w ↦ ε w + a` of `ℤ²` for `ε = ±1`, as an equivalence. -/
def affEquiv (e : ℤ) (he : e * e = 1) (a : ℤ × ℤ) : ℤ × ℤ ≃ ℤ × ℤ where
  toFun w := (e * w.1 + a.1, e * w.2 + a.2)
  invFun v := (e * (v.1 - a.1), e * (v.2 - a.2))
  left_inv w := by
    ext <;> simp only <;> rw [add_sub_cancel_right, ← mul_assoc, he, one_mul]
  right_inv v := by
    ext <;> simp only <;> rw [← mul_assoc, he, one_mul, sub_add_cancel]

theorem hfs_comp (hc : Function.HasFiniteSupport c) (e : ℤ) (he : e * e = 1) (a : ℤ × ℤ)
    (g : ℤ × ℤ → ℂ) :
    Function.HasFiniteSupport (fun w => g w * c (e * w.1 + a.1, e * w.2 + a.2)) := by
  have h : (Function.support fun w => g w * c (e * w.1 + a.1, e * w.2 + a.2)) ⊆
      (affEquiv e he a) ⁻¹' Function.support c := by
    intro w hw
    simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hw
    exact hw.2
  exact Set.Finite.subset (hc.preimage (affEquiv e he a).injective.injOn) h

theorem hfs_Tj (hc : Function.HasFiniteSupport c) (j : ℕ) (s : ℤ × ℤ) :
    Function.HasFiniteSupport (fun v : ℤ × ℤ => (v.1 : ℂ) ^ j * c v * c (v.1 + s.1, v.2 + s.2)) := by
  have := hfs_comp c hc 1 (by norm_num) (0, 0) (fun v => (v.1 : ℂ) ^ j * c (v.1 + s.1, v.2 + s.2))
  refine this.subset (fun v hv => ?_)
  simp only [Function.mem_support, ne_eq] at hv ⊢
  simpa [mul_comm, mul_left_comm, mul_assoc] using hv

/-- The shift of a reindexed term. -/
def sOf (e1 e2 : ℤ) (a b : ℤ × ℤ) : ℤ × ℤ :=
  if e2 = e1 then (b.1 - a.1, b.2 - a.2) else (-a.1 - b.1, -a.2 - b.2)

/-- Reindexing a term: `∑_w w₀^k c(εw + a) c(ε'w + b) = ε^k ∑_v (v₀ - a₀)^k c(v) c(v + s)`. -/
theorem finsum_term (heven : ∀ v : ℤ × ℤ, c (-v.1, -v.2) = c v) (k : ℕ) (e1 e2 : ℤ)
    (h1 : e1 * e1 = 1) (h2 : e2 = e1 ∨ e2 = -e1) (a b : ℤ × ℤ) :
    ∑ᶠ w : ℤ × ℤ, (w.1 : ℂ) ^ k * c (e1 * w.1 + a.1, e1 * w.2 + a.2) *
        c (e2 * w.1 + b.1, e2 * w.2 + b.2) =
      (e1 : ℂ) ^ k * ∑ᶠ v : ℤ × ℤ, ((v.1 : ℂ) - a.1) ^ k * c v *
        c (v.1 + (sOf e1 e2 a b).1, v.2 + (sOf e1 e2 a b).2) := by
  rw [← finsum_comp_equiv (affEquiv e1 h1 a).symm, mul_finsum]
  refine finsum_congr fun v => ?_
  simp only [affEquiv, Equiv.coe_fn_symm_mk]
  have ev1 : (e1 * (e1 * (v.1 - a.1)) + a.1, e1 * (e1 * (v.2 - a.2)) + a.2) = v := by
    rw [← mul_assoc, ← mul_assoc, h1, one_mul, one_mul, sub_add_cancel, sub_add_cancel]
  rw [ev1]
  rcases h2 with h2 | h2
  · rw [h2]
    simp only [sOf, if_pos rfl]
    have : (e1 * (e1 * (v.1 - a.1)) + b.1, e1 * (e1 * (v.2 - a.2)) + b.2) =
        (v.1 + (b.1 - a.1), v.2 + (b.2 - a.2)) := by
      rw [← mul_assoc, ← mul_assoc, h1, one_mul, one_mul]; ext <;> simp <;> ring
    rw [this]
    push_cast
    rw [mul_pow, ← mul_assoc, ← mul_assoc]
  · have hne : e2 ≠ e1 := by
      rw [h2]; intro h
      have : e1 = 0 := by linarith
      rw [this] at h1; norm_num at h1
    simp only [sOf, if_neg hne]
    rw [h2]
    have : (-e1 * (e1 * (v.1 - a.1)) + b.1, -e1 * (e1 * (v.2 - a.2)) + b.2) =
        (-(v.1 + (-a.1 - b.1)), -(v.2 + (-a.2 - b.2))) := by
      rw [neg_mul, neg_mul, ← mul_assoc, ← mul_assoc, h1, one_mul, one_mul]; ext <;> simp <;> ring
    rw [this, heven (v.1 + (-a.1 - b.1), v.2 + (-a.2 - b.2))]
    push_cast
    rw [mul_pow, ← mul_assoc, ← mul_assoc]

theorem hfs_const_mul {f : ℤ × ℤ → ℂ} (hf : Function.HasFiniteSupport f) (a : ℂ) :
    Function.HasFiniteSupport (fun v => a * f v) :=
  Set.Finite.subset hf (Function.support_mul_subset_right (fun _ => a) f)

/-- `∑_v (v₀ - α)^k c(v) c(v+s)` in terms of `T_j(s)`, `k ≤ 2`. -/
def redT (k : ℕ) (α : ℤ) (s : ℤ × ℤ) : ℂ :=
  match k with
  | 0 => Tj c 0 s
  | 1 => Tj c 1 s - α * Tj c 0 s
  | _ => Tj c 2 s - 2 * α * Tj c 1 s + (α : ℂ) ^ 2 * Tj c 0 s

theorem finsum_pow_sub (hc : Function.HasFiniteSupport c) {k : ℕ} (hk : k ≤ 2) (α : ℤ)
    (s : ℤ × ℤ) :
    ∑ᶠ v : ℤ × ℤ, ((v.1 : ℂ) - α) ^ k * c v * c (v.1 + s.1, v.2 + s.2) = redT c k α s := by
  have f0 := hfs_Tj c hc 0 s
  have f1 := hfs_Tj c hc 1 s
  have f2 := hfs_Tj c hc 2 s
  interval_cases k
  · simp [redT, Tj]
  · simp only [redT, Tj]
    rw [mul_finsum, ← finsum_sub_distrib f1 (hfs_const_mul f0 _)]
    refine finsum_congr fun v => ?_; ring
  · simp only [redT, Tj]
    set A := fun v : ℤ × ℤ => (v.1 : ℂ) ^ 2 * c v * c (v.1 + s.1, v.2 + s.2)
    set B := fun v : ℤ × ℤ => (v.1 : ℂ) ^ 1 * c v * c (v.1 + s.1, v.2 + s.2)
    set C0 := fun v : ℤ × ℤ => (v.1 : ℂ) ^ 0 * c v * c (v.1 + s.1, v.2 + s.2)
    have hB := hfs_const_mul f1 (2 * (α : ℂ))
    have hC := hfs_const_mul f0 ((α : ℂ) ^ 2)
    have e1 : ∑ᶠ v : ℤ × ℤ, ((v.1 : ℂ) - α) ^ 2 * c v * c (v.1 + s.1, v.2 + s.2) =
        ∑ᶠ v : ℤ × ℤ, ((A v - 2 * α * B v) + (α : ℂ) ^ 2 * C0 v) :=
      finsum_congr fun v => by simp only [A, B, C0]; ring
    have hAB : Function.HasFiniteSupport (fun v => A v - 2 * (α : ℂ) * B v) := f2.sub hB
    rw [e1, finsum_add_distrib (f := fun v => A v - 2 * (α : ℂ) * B v)
      (g := fun v => (α : ℂ) ^ 2 * C0 v) hAB hC,
      finsum_sub_distrib (f := A) (g := fun v => 2 * (α : ℂ) * B v) f2 hB, ← mul_finsum,
      ← mul_finsum]

/-- The reduced value of a term. -/
def BTerm.red (t : BTerm) : ℂ :=
  t.coef * (t.e1 : ℂ) ^ t.k * redT c t.k t.a.1 (sOf t.e1 t.e2 t.a t.b)

/-- The terms are admissible: `ε = ±1`, `ε' = ±ε`, `k ≤ 2`. -/
def BTerm.ok (t : BTerm) : Prop := t.e1 * t.e1 = 1 ∧ (t.e2 = t.e1 ∨ t.e2 = -t.e1) ∧ t.k ≤ 2

theorem bubTerms_ok : ∀ t ∈ bubTerms, t.ok := by
  intro t ht
  simp only [bubTerms, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    (subst h; simp only [BTerm.ok]; norm_num)

theorem BTerm.finsum_val (heven : ∀ v : ℤ × ℤ, c (-v.1, -v.2) = c v)
    (hc : Function.HasFiniteSupport c) (t : BTerm) (ht : t.ok) :
    ∑ᶠ w : ℤ × ℤ, t.val c w = t.red c := by
  obtain ⟨h1, h2, hk⟩ := ht
  have e : ∀ w : ℤ × ℤ, t.val c w = (t.coef : ℂ) * ((w.1 : ℂ) ^ t.k *
      c (t.e1 * w.1 + t.a.1, t.e1 * w.2 + t.a.2) * c (t.e2 * w.1 + t.b.1, t.e2 * w.2 + t.b.2)) := by
    intro w; simp only [BTerm.val]; ring
  simp_rw [e]
  rw [← mul_finsum, finsum_term c heven t.k t.e1 t.e2 h1 h2 t.a t.b, finsum_pow_sub c hc hk,
    BTerm.red]
  ring

theorem BTerm.hfs (hc : Function.HasFiniteSupport c) (t : BTerm) (ht : t.ok) :
    Function.HasFiniteSupport (t.val c) := by
  obtain ⟨h1, -, -⟩ := ht
  have := hfs_comp c hc t.e1 h1 t.a (fun w => (t.coef : ℂ) * (w.1 : ℂ) ^ t.k *
    c (t.e2 * w.1 + t.b.1, t.e2 * w.2 + t.b.2))
  refine this.subset (fun w hw => ?_)
  simp only [Function.mem_support, ne_eq, BTerm.val] at hw ⊢
  intro h; apply hw; rw [← h]; ring

theorem finsum_list (l : List BTerm) (hc : Function.HasFiniteSupport c)
    (hl : ∀ t ∈ l, t.ok) (heven : ∀ v : ℤ × ℤ, c (-v.1, -v.2) = c v) :
    Function.HasFiniteSupport (fun w => (l.map (BTerm.val c w)).sum) ∧
      ∑ᶠ w : ℤ × ℤ, (l.map (BTerm.val c w)).sum = (l.map (BTerm.red c)).sum := by
  induction l with
  | nil => simp [Function.HasFiniteSupport]
  | cons t l ih =>
    obtain ⟨ih1, ih2⟩ := ih fun u hu => hl u (List.mem_cons_of_mem t hu)
    have ht := hl t List.mem_cons_self
    simp only [List.map_cons, List.sum_cons]
    refine ⟨(BTerm.hfs c hc t ht).add ih1, ?_⟩
    rw [finsum_add_distrib (BTerm.hfs c hc t ht) ih1, ih2, BTerm.finsum_val c heven hc t ht]

/-- The reduced coefficients `T_{j,s}`. -/
structure TCoef where
  j : ℕ
  s : ℤ × ℤ
  v : ℤ

/-- The 28 coefficients. -/
def bubT : List TCoef :=
  [⟨0, ((-2), 0), (-4)⟩,
    ⟨0, ((-1), 0), 16⟩,
    ⟨0, (0, (-1)), 16⟩,
    ⟨0, (0, 0), (-48)⟩,
    ⟨0, (0, 1), 16⟩,
    ⟨0, (1, 0), 16⟩,
    ⟨0, (2, 0), (-12)⟩,
    ⟨1, ((-2), 0), 8⟩,
    ⟨1, ((-1), (-1)), 8⟩,
    ⟨1, ((-1), 0), (-32)⟩,
    ⟨1, ((-1), 1), 8⟩,
    ⟨1, (1, (-1)), (-8)⟩,
    ⟨1, (1, 0), 32⟩,
    ⟨1, (1, 1), (-8)⟩,
    ⟨1, (2, 0), (-8)⟩,
    ⟨2, ((-2), 0), (-4)⟩,
    ⟨2, ((-1), (-1)), (-8)⟩,
    ⟨2, ((-1), 0), 32⟩,
    ⟨2, ((-1), 1), (-8)⟩,
    ⟨2, (0, (-2)), (-4)⟩,
    ⟨2, (0, (-1)), 32⟩,
    ⟨2, (0, 0), (-80)⟩,
    ⟨2, (0, 1), 32⟩,
    ⟨2, (0, 2), (-4)⟩,
    ⟨2, (1, (-1)), (-8)⟩,
    ⟨2, (1, 0), 32⟩,
    ⟨2, (1, 1), (-8)⟩,
    ⟨2, (2, 0), (-4)⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem red_sum : (bubTerms.map (BTerm.red c)).sum =
    (bubT.map fun t => (t.v : ℂ) * Tj c t.j t.s).sum := by
  simp only [bubTerms, bubT, List.map, List.sum_cons, List.sum_nil, BTerm.red, redT, sOf]
  norm_num
  ring_nf

/-- **The bubble sum in position space.** For an even, finitely supported `c : ℤ² → ℂ`,
`∑_w bubFZ c w = ∑_{(j,s)} T_{j,s} ∑_v v₀^j c(v) c(v + s)` (`bubT`). -/
theorem finsum_bubFZ (hc : Function.HasFiniteSupport c)
    (heven : ∀ v : ℤ × ℤ, c (-v.1, -v.2) = c v) :
    ∑ᶠ w : ℤ × ℤ, bubFZ c w = (bubT.map fun t => (t.v : ℂ) * Tj c t.j t.s).sum := by
  simp_rw [bubFZ_eq]
  rw [(finsum_list c bubTerms hc bubTerms_ok heven).2, red_sum]

end Sums

end

end Step2
