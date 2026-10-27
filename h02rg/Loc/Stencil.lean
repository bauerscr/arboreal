import Loc.Polymer

-- Merged from `Loc/LocalPoly.lean` (phase 3).
section

/-!
# Local field polynomials (Definition `def:cV`)

* `grad e x = (∇_e ψ)_x`, `gradbar e x = (∇_e ψ̄)_x`, `lapPsi x = (Δψ)_x`, `lapPsibar x = (Δψ̄)_x`
  with `Δ = -½ ∑_{e ∈ 𝓔_d} ∇_{-e} ∇_e`, and `gradSq x = (∇ψ)_x (∇ψ̄)_x = ½ ∑_e ∇_eψ_x ∇_eψ̄_x`;
* `Vcoup` is `𝒱^∅ ≅ ℂ^4` (complex coupling constants `(z, y, a, b)`), and
  `Vcoup.eval V X = V(X)` (`e:VX`); `(ℂ ⊕ 𝒱^∅)(X) = {u|X| + V(X)}` (`u ∈ ℂ`) is `VXspace X`.

As in the paper, the coupling constants are complex (`𝒩(Λ)` is an algebra over `ℂ`).
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD

variable {d L N : ℕ} [NeZero L]

/-- The Grassmann algebra `𝒩(Λ_N)`. -/
abbrev Alg (d L N : ℕ) [NeZero L] := Grassmann.N (Lam d L N)

/-- `(∇_e ψ)_x = ψ_{x+e} - ψ_x`. -/
def grad (e : Dir d) (x : Lam d L N) : Alg d L N := psi (x + dirVec e) - psi x

/-- `(∇_e ψ̄)_x`. -/
def gradbar (e : Dir d) (x : Lam d L N) : Alg d L N := psibar (x + dirVec e) - psibar x

/-- `(Δψ)_x = -½ ∑_{e ∈ 𝓔_d} (∇_{-e} ∇_e ψ)_x`, where `(∇_{-e} g)_x = g_{x-e} - g_x`. -/
def lapPsi (x : Lam d L N) : Alg d L N :=
  (-(1 / 2 : ℂ)) • ∑ e : Dir d, (grad e (x - dirVec e) - grad e x)

/-- `(Δψ̄)_x`. -/
def lapPsibar (x : Lam d L N) : Alg d L N :=
  (-(1 / 2 : ℂ)) • ∑ e : Dir d, (gradbar e (x - dirVec e) - gradbar e x)

/-- `(∇ψ)_x (∇ψ̄)_x = ½ ∑_{e ∈ 𝓔_d} (∇_e ψ)_x (∇_e ψ̄)_x`. -/
def gradSq (x : Lam d L N) : Alg d L N := (1 / 2 : ℂ) • ∑ e : Dir d, grad e x * gradbar e x

/-- The coupling constants `V = (z, y, a, b) ∈ 𝒱^∅`. -/
structure Vcoup where
  z : ℂ
  y : ℂ
  a : ℂ
  b : ℂ

/-- `V(X) = ∑_{x ∈ X} [y (∇ψ)(∇ψ̄) + z/2 ((-Δψ)ψ̄ + ψ(-Δψ̄)) + a ψψ̄ + b ψψ̄(∇ψ)(∇ψ̄)]_x`. -/
def Vcoup.eval (V : Vcoup) (X : Finset (Lam d L N)) : Alg d L N :=
  ∑ x ∈ X, (V.y • gradSq x + (V.z / 2) • ((-lapPsi x) * psibar x + psi x * (-lapPsibar x)) +
    V.a • (psi x * psibar x) + V.b • (psi x * psibar x * gradSq x))

/-- `(ℂ ⊕ 𝒱^∅)(X) = {u|X| + V(X)}`. -/
def VXspace (X : Finset (Lam d L N)) : Set (Alg d L N) :=
  {F | ∃ (u : ℂ) (V : Vcoup), F = (u * X.card) • (1 : Alg d L N) + V.eval X}

end

end Loc

end

/-!
# The monomial basis of the localisation and its dual test polynomials

The range of `Loc` consists of (a constant plus) the local polynomials `∑_{x ∈ X} M_x` where `M`
runs over the following basis `Mono d` of `ψψ̄`-monomials of dimension `≤ d` (with
`∂_i f(x) = ½(f(x+e_i) - f(x-e_i))`, `Δ_i f(x) = f(x+e_i) + f(x-e_i) - 2 f(x)`):

* `c`: `ψ ψ̄`;
* `a1 i`: `(∂_i ψ) ψ̄`, `b1 i`: `ψ (∂_i ψ̄)`;
* `a2 {i,k}`: `(D_{ik} ψ) ψ̄`, `b2 {i,k}`: `ψ (D_{ik} ψ̄)` with `D_{ii} = Δ_i`, `D_{ik} = ∂_i∂_k`;
* `m2 i k`: `(∂_i ψ)(∂_k ψ̄)` for `i ≠ k` and `½ ∑_{s=±} (∇_{s e_i} ψ)(∇_{s e_i} ψ̄)` for `i = k`.

This basis is invariant (up to signs) under the lattice symmetries.  Each monomial is encoded
by a *stencil*: a list of weights `c` and offsets `(a, b)` of the `ψ` and `ψ̄` factor,
`M_x = ∑ c ψ_{x+a} ψ̄_{x+b}`.  `Qpoly β` are the dual test polynomials `1, u_i, v_i, u_i u_k,
v_i v_k, u_i v_k` (with `u_i²/2`, `v_i²/2` on the diagonal): the moment identity
`moment_eq` says that pairing `M` with `Qpoly β` gives `δ_{Mβ}` when `deg β ≤ deg M`.

Scalars: the Grassmann algebra is over `ℂ`, but stencil weights and the test polynomials `Qpoly`
are kept *real-valued* (they are rational numbers / real polynomials); they are cast to `ℂ`
wherever they multiply Grassmann coefficients (`monoAt`, `mu` in `Loc.LocDef`).
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD

variable {d : ℕ}

/-- The monomial basis. -/
inductive Mono (d : ℕ) where
  | c : Mono d
  | a1 : Fin d → Mono d
  | b1 : Fin d → Mono d
  | a2 : Sym2 (Fin d) → Mono d
  | b2 : Sym2 (Fin d) → Mono d
  | m2 : Fin d → Fin d → Mono d
  deriving DecidableEq

/-- The number of derivatives. -/
def Mono.deg : Mono d → ℕ
  | .c => 0
  | .a1 _ => 1
  | .b1 _ => 1
  | .a2 _ => 2
  | .b2 _ => 2
  | .m2 _ _ => 2

/-- The equivalence of `Mono d` with a sum type (to get a `Fintype` instance). -/
def Mono.equiv : Mono d ≃ Unit ⊕ Fin d ⊕ Fin d ⊕ Sym2 (Fin d) ⊕ Sym2 (Fin d) ⊕ (Fin d × Fin d) where
  toFun
    | .c => .inl ()
    | .a1 i => .inr (.inl i)
    | .b1 i => .inr (.inr (.inl i))
    | .a2 s => .inr (.inr (.inr (.inl s)))
    | .b2 s => .inr (.inr (.inr (.inr (.inl s))))
    | .m2 i k => .inr (.inr (.inr (.inr (.inr (i, k)))))
  invFun
    | .inl () => .c
    | .inr (.inl i) => .a1 i
    | .inr (.inr (.inl i)) => .b1 i
    | .inr (.inr (.inr (.inl s))) => .a2 s
    | .inr (.inr (.inr (.inr (.inl s)))) => .b2 s
    | .inr (.inr (.inr (.inr (.inr (i, k))))) => .m2 i k
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with _ | _ | _ | _ | _ | ⟨_, _⟩ <;> rfl

instance : Fintype (Mono d) := Fintype.ofEquiv _ Mono.equiv.symm

/-- The unit vector `e_i ∈ ℤ^d`. -/
def ez (i : Fin d) : Zd d := Pi.single i 1

/-- A 1-d stencil: weights and offsets. -/
abbrev St1 (d : ℕ) := List (ℝ × Zd d)

/-- A quadratic stencil: weights and offsets of the `ψ` and the `ψ̄` factor. -/
abbrev St (d : ℕ) := List (ℝ × Zd d × Zd d)

/-- `δ_0`. -/
def id1 : St1 d := [(1, 0)]
/-- `∂_i`. -/
def dpt (i : Fin d) : St1 d := [(1 / 2, ez i), (-(1 / 2), -ez i)]
/-- `Δ_i`. -/
def lap1 (i : Fin d) : St1 d := [(1, ez i), (1, -ez i), (-2, 0)]
/-- `∇_v`. -/
def fw (v : Zd d) : St1 d := [(1, v), (-1, 0)]
/-- Composition of 1-d stencils. -/
def conv (s t : St1 d) : St1 d := s.flatMap fun p => t.map fun q => (p.1 * q.1, p.2 + q.2)
/-- `D_{ik}`. -/
def Dik (i k : Fin d) : St1 d := if i = k then lap1 i else conv (dpt i) (dpt k)
/-- The tensor product of stencils acting on `ψ` and `ψ̄`. -/
def tens (s t : St1 d) : St d := s.flatMap fun p => t.map fun q => (p.1 * q.1, p.2, q.2)
/-- Scaling a stencil. -/
def sc (r : ℝ) (m : St d) : St d := m.map fun p => (r * p.1, p.2)

/-- The stencil of `D_s`, `s ∈ Sym2 (Fin d)`: we use `min`/`max` of the pair to be symmetric. -/
def Dsym (s : Sym2 (Fin d)) : St1 d :=
  Sym2.lift ⟨fun i k => Dik (min i k) (max i k), fun i k => by simp only [min_comm, max_comm]⟩ s

/-- The stencil of a monomial. -/
def stencil : Mono d → St d
  | .c => tens id1 id1
  | .a1 i => tens (dpt i) id1
  | .b1 i => tens id1 (dpt i)
  | .a2 s => tens (Dsym s) id1
  | .b2 s => tens id1 (Dsym s)
  | .m2 i k => if i = k then sc (1 / 2) (tens (fw (ez i)) (fw (ez i)) ++ tens (fw (-ez i)) (fw (-ez i)))
      else tens (dpt i) (dpt k)

/-- `Q ↦ ∑ c Q(w₁ + a, w₂ + b)`: the pairing of a stencil with a function of two points. -/
def applySt (m : St d) (Q : (Fin d → ℝ) → (Fin d → ℝ) → ℝ) (w₁ w₂ : Fin d → ℝ) : ℝ :=
  (m.map fun p => p.1 * Q (w₁ + fun i => (p.2.1 i : ℝ)) (w₂ + fun i => (p.2.2 i : ℝ))).sum

/-- The dual test polynomials. -/
def Qpoly : Mono d → (Fin d → ℝ) → (Fin d → ℝ) → ℝ
  | .c, _, _ => 1
  | .a1 i, u, _ => u i
  | .b1 i, _, v => v i
  | .a2 s, u, _ => Sym2.lift ⟨fun i k => if i = k then u i ^ 2 / 2 else u i * u k,
      fun i k => by by_cases h : i = k <;> simp [h, eq_comm, mul_comm]⟩ s
  | .b2 s, _, v => Sym2.lift ⟨fun i k => if i = k then v i ^ 2 / 2 else v i * v k,
      fun i k => by by_cases h : i = k <;> simp [h, eq_comm, mul_comm]⟩ s
  | .m2 i k, u, v => u i * v k


theorem sym2_minmax (i k : Fin d) : (s(i, k) : Sym2 (Fin d)) = s(min i k, max i k) := by
  rcases le_total i k with h' | h'
  · simp [min_eq_left h', max_eq_right h']
  · simp [min_eq_right h', max_eq_left h', Sym2.eq_swap]

theorem minmax_ne {i k : Fin d} (hik : i ≠ k) : min i k ≠ max i k := by
  rcases le_total i k with h' | h'
  · simp [min_eq_left h', max_eq_right h', hik]
  · simp [min_eq_right h', max_eq_left h', Ne.symm hik]

theorem Dsym_mk {a b : Fin d} (hab : a ≤ b) : Dsym s(a, b) = Dik a b := by
  simp [Dsym, min_eq_left hab, max_eq_right hab]

macro "mcomp" : tactic => `(tactic| (
  simp [applySt, stencil, tens, conv, dpt, id1, lap1, fw, sc, Dik, Qpoly, ez, Pi.single_apply,
    Sym2.eq_iff] <;> (try split_ifs) <;> (try simp_all [Pi.single_apply]) <;>
    (try (split_ifs <;> simp_all)) <;> (try ring_nf)))

macro "betacases" β:ident : tactic => `(tactic| (
  cases $β:ident with
  | c => mcomp
  | a1 j => mcomp
  | b1 j => mcomp
  | a2 t => induction t using Sym2.ind with
      | h j l => rcases eq_or_ne j l with rfl | hjl <;> mcomp
  | b2 t => induction t using Sym2.ind with
      | h j l => rcases eq_or_ne j l with rfl | hjl <;> mcomp
  | m2 j l => rcases eq_or_ne j l with rfl | hjl <;> mcomp))

set_option maxHeartbeats 4000000 in
/-- The moment identity: `⟨M, Q_β⟩ = δ_{Mβ}` for `deg β ≤ deg M`, at every point. -/
theorem moment (M β : Mono d) (h : β.deg ≤ M.deg) (w₁ w₂ : Fin d → ℝ) :
    applySt (stencil M) (Qpoly β) w₁ w₂ = if β = M then 1 else 0 := by
  cases M with
  | c => cases β <;> simp [Mono.deg] at h ⊢; simp [applySt, stencil, tens, id1, Qpoly]
  | a1 i => cases β <;> simp [Mono.deg] at h ⊢ <;> mcomp
  | b1 i => cases β <;> simp [Mono.deg] at h ⊢ <;> mcomp
  | a2 s =>
    induction s using Sym2.ind with
    | h i k =>
      rcases eq_or_ne i k with rfl | hik
      · rw [show stencil (Mono.a2 s(i, i)) = tens (lap1 i) id1 by simp [stencil, Dsym, Dik]]
        betacases β
      · rw [sym2_minmax i k]
        have hab : min i k ≤ max i k := min_le_max
        have hne := minmax_ne hik
        generalize min i k = a at *
        generalize max i k = b at *
        rw [show stencil (Mono.a2 s(a, b)) = tens (conv (dpt a) (dpt b)) id1 by
          simp [stencil, Dsym_mk hab, Dik, hne]]
        betacases β
  | b2 s =>
    induction s using Sym2.ind with
    | h i k =>
      rcases eq_or_ne i k with rfl | hik
      · rw [show stencil (Mono.b2 s(i, i)) = tens id1 (lap1 i) by simp [stencil, Dsym, Dik]]
        betacases β
      · rw [sym2_minmax i k]
        have hab : min i k ≤ max i k := min_le_max
        have hne := minmax_ne hik
        generalize min i k = a at *
        generalize max i k = b at *
        rw [show stencil (Mono.b2 s(a, b)) = tens id1 (conv (dpt a) (dpt b)) by
          simp [stencil, Dsym_mk hab, Dik, hne]]
        betacases β
  | m2 i k =>
    rcases eq_or_ne i k with rfl | hik
    · betacases β
    · betacases β

end

end Loc
