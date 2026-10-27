import Obs2.Flow.VObsAB4
import Obs2.Pair.ShareAB1

/-!
# The `M₄` and quadratic-coefficient flows of `V'_{ab}` in a region

For a region `X` (an `(j+1)`-polymer) the region sums `M₄(X) = ∑_{B∈𝓑_j(X)}M₄(V(B)_{ab})`
(`m4X`) and `c_{uv}(X) = ∑_{B∈𝓑_j(X)}c_{uv}(V(B)_{ab})` (`cf2X`) obey exact one-step identities
(`m4X_succ`, `cf2X_succ`; the region analogues of `m4Tot_succ`, `cfAB2_VpO`, as `rABX_next_red`
is that of `rAB2`). For a `k`-block `X = B` the region sums are the coefficients of `V_k(B)`
(`m4X_blockSet`, `cf2X_blockSet`), and `B` is an `i`-polymer for every `i ≤ k`, so the per-block
coefficients at scale `k` are obtained by following the fixed region `B` from `j_x` to `k`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD

variable {d L N : ℕ} [NeZero L]

/-- The quartic coefficient of the region `X` at scale `j`. -/
def m4X (P : ObsPts d L N) (j : ℕ) (V : OFam .two d L N) (X : Finset (Lam d L N)) : ℂ :=
  ∑ b ∈ blocks j X, cfAB4 P.a P.b (V b : SA .two (Lam d L N)).ab

/-- The quadratic coefficient `c_{uv}` of the region `X` at scale `j`. -/
def cf2X (u v : Lam d L N) (j : ℕ) (V : OFam .two d L N) (X : Finset (Lam d L N)) : ℂ :=
  ∑ b ∈ blocks j X, cfAB2 u v (V b : SA .two (Lam d L N)).ab

theorem m4X_blockSet (P : ObsPts d L N) (k : ℕ) (V : OFam .two d L N) {c : Fin d → ℕ}
    (hne : (blockSet (L := L) (N := N) k c).Nonempty) :
    m4X P k V (blockSet (L := L) (N := N) k c) = cfAB4 P.a P.b (V c : SA .two (Lam d L N)).ab := by
  rw [m4X, blocks_blockSet_self hne, sum_singleton]

section Step

variable (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
  (V W : OFam .two d L N) (K : OAct .two d L N) {X : Finset (Lam d L N)}

theorem cfAB4_sum_eq {ι : Type*} (s : Finset ι) (f : ι → Alg d L N) (a b : Lam d L N) :
    cfAB4 a b (∑ i ∈ s, f i) = ∑ i ∈ s, cfAB4 a b (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [sum_empty, sum_empty]; exact coeff_zero _
  | insert x s hx ih => rw [sum_insert hx, sum_insert hx, cfAB4_add, ih]

theorem cfAB2_sum_eq {ι : Type*} (s : Finset ι) (f : ι → Alg d L N) (u v : Lam d L N) :
    cfAB2 u v (∑ i ∈ s, f i) = ∑ i ∈ s, cfAB2 u v (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [sum_empty, sum_empty]; exact coeff_zero _
  | insert x s hx ih => rw [sum_insert hx, sum_insert hx, cfAB2_add, ih]

/-- **The `M₄` step in a region** (`X` an `(j+1)`-polymer). -/
theorem m4X_succ (hX : IsPolymer (j + 1) X)
    (hV : ∀ b, (V b : SA .two (Lam d L N)).ab ∈ NX ({P.a, P.b} : Set (Lam d L N)))
    (hS : ∀ b, IsSym (V b : SA .two (Lam d L N)).ab) :
    m4X P (j + 1) (Vnext2O P j C V W K) X = m4X P j V X -
      ∑ b ∈ blocks j X, cfAB4 P.a P.b (Q2O P j K b : SA .two (Lam d L N)).ab -
      ∑ b ∈ blocks j X, cfAB4 P.a P.b (LSO P j C V W b : SA .two (Lam d L N)).ab := by
  have e : m4X P (j + 1) (Vnext2O P j C V W K) X =
      ∑ b ∈ blocks j X, cfAB4 P.a P.b (VpO P j C V W K b : SA .two (Lam d L N)).ab := by
    rw [m4X, ← Step2.sum_blocks_succ hX]
    refine sum_congr rfl fun c' _ => ?_
    rw [Vnext2O, AddSubmonoidClass.coe_finsetSum, SA.sum_ab, cfAB4_sum_eq]
  rw [e, sum_congr rfl fun b _ => cfAB4_VpO P j C V W K hV hS b, sum_sub_distrib,
    sum_sub_distrib]
  rfl

/-- **The step of the quadratic coefficients in a region**: `κ_{uv} = c_{uv}(LopM4 C)`. -/
theorem cf2X_succ (hX : IsPolymer (j + 1) X)
    (hV : ∀ b, (V b : SA .two (Lam d L N)).ab ∈ NX ({P.a, P.b} : Set (Lam d L N)))
    (hS : ∀ b, IsSym (V b : SA .two (Lam d L N)).ab) {u v : Lam d L N}
    (hu : u = P.a ∨ u = P.b) (hv : v = P.a ∨ v = P.b) :
    cf2X u v (j + 1) (Vnext2O P j C V W K) X =
      cf2X u v j V X + m4X P j V X * cfAB2 u v (LopM4 C P.a P.b) -
        (∑ b ∈ blocks j X, cfAB2 u v (Q2O P j K b : SA .two (Lam d L N)).ab +
          (∑ b ∈ blocks j X, cfAB4 P.a P.b (Q2O P j K b : SA .two (Lam d L N)).ab) *
            cfAB2 u v (LopM4 C P.a P.b)) -
        ∑ b ∈ blocks j X, cfAB2 u v (LSO P j C V W b : SA .two (Lam d L N)).ab := by
  have e : cf2X u v (j + 1) (Vnext2O P j C V W K) X =
      ∑ b ∈ blocks j X, cfAB2 u v (VpO P j C V W K b : SA .two (Lam d L N)).ab := by
    rw [cf2X, ← Step2.sum_blocks_succ hX]
    refine sum_congr rfl fun c' _ => ?_
    rw [Vnext2O, AddSubmonoidClass.coe_finsetSum, SA.sum_ab, cfAB2_sum_eq]
  rw [e, sum_congr rfl fun b _ => cfAB2_VpO P j C V W K hV hS hu hv b]
  unfold cf2X m4X
  simp only [sum_sub_distrib, sum_add_distrib, sum_mul]

end Step

end

end Obs2
