import Loc.LocProps
import Grassmann.Examples

/-!
# Common definitions for the estimates on the localisation (`prop:Loc` (i), (ii))

* the translation action of multi-indices on `ℤ^d` (`zAct`), so that the norms `Φ`, and
  discrete derivatives, make sense for functions of points of `ℤ^d`;
* the embedding `ιS b : Sf ℤ^d → Sf Λ`, `(u, σ) ↦ (b + u, σ)`, and the (local) inverse
  `ρS b : Sf Λ → Sf ℤ^d`, `(x, σ) ↦ (r(x - b), σ)`;
* the one-point derivative `D1 s a f y = ∇^a f(y)`;
* test functions supported on sequences of one length (`single`) and restrictions of test
  functions to a set of lengths (`restr`);
* elementary facts on `ord` and `ediff`.
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD

/-! ### Multi-indices -/

section MultiIndex

variable {n : ℕ} {E : Type*} [Fintype E] [DecidableEq E]

theorem mabs_add (a b : E → ℕ) : Grassmann.mabs (a + b) = Grassmann.mabs a + Grassmann.mabs b := by
  simp [Grassmann.mabs, sum_add_distrib]

theorem mabs_single (e : E) : Grassmann.mabs (Pi.single e 1 : E → ℕ) = 1 := by
  simp [Grassmann.mabs]

theorem ord_add (α β : Fin n → E → ℕ) : ord (α + β) = ord α + ord β := by
  simp [ord, mabs_add, sum_add_distrib]

theorem ord_single (i : Fin n) (e : E) : ord (Pi.single i (Pi.single e 1) : Fin n → E → ℕ) = 1 := by
  rw [ord, sum_eq_single i]
  · simp [Grassmann.mabs]
  · intro j _ hj; simp [hj, Grassmann.mabs]
  · simp

theorem ord_zero : ord (0 : Fin n → E → ℕ) = 0 := by simp [ord, Grassmann.mabs]

theorem mabs_eq_zero {a : E → ℕ} (h : Grassmann.mabs a = 0) : a = 0 := by
  funext e
  have := (sum_eq_zero_iff.1 h) e (mem_univ e)
  simpa using this

theorem ord_eq_zero {α : Fin n → E → ℕ} (h : ord α = 0) : α = 0 := by
  funext i
  exact mabs_eq_zero ((sum_eq_zero_iff.1 h) i (mem_univ i))

/-- A nonzero multi-index is a smaller one plus a unit multi-index. -/
theorem exists_eq_add_single {α : Fin n → E → ℕ} (h : α ≠ 0) :
    ∃ (α' : Fin n → E → ℕ) (i : Fin n) (e : E), α = α' + Pi.single i (Pi.single e 1) := by
  obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
    by_contra hc; push Not at hc; exact h (funext hc)
  obtain ⟨e, he⟩ : ∃ e, α i e ≠ 0 := by
    by_contra hc; push Not at hc; exact hi (funext hc)
  refine ⟨α - Pi.single i (Pi.single e 1), i, e, ?_⟩
  funext j e'
  by_cases hj : j = i
  · subst hj
    by_cases he' : e' = e
    · subst he'; simp; omega
    · simp [he']
  · simp [hj]

theorem le_add_single (α : Fin n → E → ℕ) (i : Fin n) (e : E) : α ≤ α + Pi.single i (Pi.single e 1) :=
  fun _ _ => Nat.le_add_right _ _

/-- A multi-index of order one is a unit multi-index. -/
theorem eq_single_of_ord_eq_one {α : Fin n → E → ℕ} (h : ord α = 1) :
    ∃ (i : Fin n) (e : E), α = Pi.single i (Pi.single e 1) := by
  have hne : α ≠ 0 := by rintro rfl; simp [ord_zero] at h
  obtain ⟨α', i, e, rfl⟩ := exists_eq_add_single hne
  rw [ord_add, ord_single] at h
  rw [ord_eq_zero (by omega : ord α' = 0), zero_add]
  exact ⟨i, e, rfl⟩

end MultiIndex

/-! ### Discrete derivatives commute with elementary differences -/

section Nabla

variable {κ E Y W : Type*} [Fintype κ] [DecidableEq κ] [Fintype E] [DecidableEq E]
  [AddCommGroup W] [Module ℝ W]

/-- `∇_{i,e} ∇^γ f = ∇^{γ + δ_{i,e}} f`. -/
theorem ediff_nabla (s : (E → ℕ) → Y → Y) (hsa : ∀ b b' y, s (b + b') y = s b (s b' y))
    (γ : κ → E → ℕ) (i : κ) (e : E) (f : (κ → Y) → W) :
    ediff s i e (nabla s γ f) = nabla s (γ + Pi.single i (Pi.single e 1)) f := by
  rw [nabla_succ s hsa]
  funext z
  simp only [ediff, nabla_apply, ← sum_sub_distrib, ← smul_sub]
  refine sum_congr rfl fun β _ => ?_
  congr 2
  congr 1
  funext j
  by_cases hj : j = i
  · subst hj
    simp only [Function.update_self]
    rw [← hsa, ← hsa, add_comm]
  · simp [Function.update_of_ne hj]

/-- `∇^γ` commutes with translations of the points. -/
theorem nabla_comp_shift (s : (E → ℕ) → Y → Y) (hsa : ∀ b b' y, s (b + b') y = s b (s b' y))
    (γ : κ → E → ℕ) (c : κ → E → ℕ) (f : (κ → Y) → W) (z : κ → Y) :
    nabla s γ (fun w => f fun i => s (c i) (w i)) z = nabla s γ f (fun i => s (c i) (z i)) := by
  simp only [nabla_apply]
  refine sum_congr rfl fun β _ => ?_
  congr 2
  funext i
  rw [← hsa, ← hsa, add_comm]

end Nabla

/-! ### The one-point derivative -/

section D1

variable {E Y : Type*} [Fintype E] [DecidableEq E]

/-- `∇^a f(y)` for a function of one point. -/
def D1 (s : (E → ℕ) → Y → Y) (a : E → ℕ) (f : Y → ℝ) (y : Y) : ℝ :=
  nabla s (fun _ : Fin 1 => a) (fun z => f (z 0)) (fun _ => y)

theorem D1_eq_sum (s : (E → ℕ) → Y → Y) (a : E → ℕ) (f : Y → ℝ) (y : Y) :
    D1 s a f y = ∑ b ∈ Iic a, cf a b * f (s b y) := by
  have := nabla_multilinear s (fun _ : Fin 1 => a) (MultilinearMap.mkPiAlgebra ℝ (Fin 1) ℝ)
    (fun _ => f) (fun _ => y)
  simp only [MultilinearMap.mkPiAlgebra_apply, Fin.prod_univ_one, smul_eq_mul] at this
  exact this

theorem D1_zero (s : (E → ℕ) → Y → Y) (hs0 : ∀ y, s 0 y = y) (f : Y → ℝ) (y : Y) :
    D1 s 0 f y = f y := by
  rw [D1, show (fun _ : Fin 1 => (0 : E → ℕ)) = 0 from rfl, nabla_zero s hs0]

/-- `∇^{a + δ_e} f = ∇^a (∇_e f)`. -/
theorem D1_succ (s : (E → ℕ) → Y → Y) (hsa : ∀ b b' y, s (b + b') y = s b (s b' y))
    (a : E → ℕ) (e : E) (f : Y → ℝ) (y : Y) :
    D1 s (a + Pi.single e 1) f y = D1 s a (fun y => f (s (Pi.single e 1) y) - f y) y := by
  have h := nabla_succ s hsa (fun _ : Fin 1 => a) 0 e (fun z => f (z 0))
  have e1 : ((fun _ : Fin 1 => a) + Pi.single 0 (Pi.single e 1)) = fun _ => a + Pi.single e 1 := by
    funext i; fin_cases i; simp
  rw [e1] at h
  rw [D1, h, D1]
  congr 2

/-- The derivative of a product of functions of the individual points. -/
theorem nabla_prod {κ : Type*} [Fintype κ] [DecidableEq κ] (s : (E → ℕ) → Y → Y)
    (α : κ → E → ℕ) (f : κ → Y → ℝ) (z : κ → Y) :
    nabla s α (fun w => ∏ i, f i (w i)) z = ∏ i, D1 s (α i) (f i) (z i) := by
  have := nabla_multilinear s α (MultilinearMap.mkPiAlgebra ℝ κ ℝ) f z
  simp only [MultilinearMap.mkPiAlgebra_apply, smul_eq_mul] at this
  rw [this]
  simp only [D1_eq_sum]

end D1

/-! ### Predicates on the spins -/

section Spin

variable {X : Type*} [DecidableEq X] {E : Type*} [Fintype E] [DecidableEq E]
  [AddAction (E → ℕ) X]

/-- The spins of a sequence. -/
def spins {n : ℕ} (z : Fin n → Sf X) : Fin n → ℤˣ := fun i => (z i).2

theorem spins_sh {n : ℕ} (β : Fin n → E → ℕ) (z : Fin n → Sf X) :
    spins (fun i => sh (β i) (z i)) = spins z := rfl

/-- Multiplying by an indicator of the spins commutes with derivatives. -/
theorem nab_ite_spins {W : Type*} [AddCommGroup W] [Module ℝ W] {n : ℕ}
    (P : (Fin n → ℤˣ) → Prop) [DecidablePred P] (α : Fin n → E → ℕ) (f : (Fin n → Sf X) → W) (z : Fin n → Sf X) :
    nab α (fun w => if P (spins w) then f w else 0) z = if P (spins z) then nab α f z else 0 := by
  split_ifs with h
  · exact nabla_congr _ α z fun β => by rw [spins_sh, if_pos h]
  · rw [nabla_congr _ α z (g := 0) fun β => by rw [spins_sh, if_neg h]; rfl]
    simp

end Spin

/-! ### Test functions of one length, and restrictions -/

section Single

variable {X : Type*}

/-- The test function equal to `f` on sequences of length `m` and to `0` otherwise. -/
def single (m : ℕ) (f : (Fin m → Sf X) → ℂ) : TestFn X :=
  fun n z => if h : n = m then f (z ∘ Fin.cast h.symm) else 0

@[simp] theorem single_self (m : ℕ) (f : (Fin m → Sf X) → ℂ) : single m f m = f := by
  funext z; simp [single]

theorem single_ne {m n : ℕ} (f : (Fin m → Sf X) → ℂ) (h : n ≠ m) : single m f n = 0 := by
  funext z; simp [single, h]

/-- The restriction of a test function to the lengths `n` with `P n`. -/
def restr (P : ℕ → Prop) [DecidablePred P] (g : TestFn X) : TestFn X :=
  fun n z => if P n then g n z else 0

end Single

/-! ### `ℤ^d` with the translation action of multi-indices -/

variable {d : ℕ}

/-- `α ↦ ∑_e α(e) e` in `ℤ^d`. -/
def dirHomZ : (Dir d → ℕ) →+ Zd d where
  toFun α := ∑ e, α e • dirZ e
  map_zero' := by simp
  map_add' α β := by simp [add_smul, sum_add_distrib]

/-- Translation by multi-indices on `ℤ^d`: `α +ᵥ u = u + ∑_e α(e) e`. -/
instance zAct : AddAction (Dir d → ℕ) (Zd d) := AddAction.compHom (Zd d) (dirHomZ (d := d))

theorem vaddZ_def (α : Dir d → ℕ) (u : Zd d) : α +ᵥ u = dirHomZ α + u := rfl

theorem single_vaddZ (e : Dir d) (u : Zd d) : (Pi.single e 1 : Dir d → ℕ) +ᵥ u = u + dirZ e := by
  rw [vaddZ_def, add_comm]
  congr 1
  show ∑ e', (Pi.single e 1 : Dir d → ℕ) e' • dirZ e' = dirZ e
  rw [sum_eq_single e (fun b _ hb => by simp [hb]) (by simp)]
  simp

theorem supNormZ_dirHomZ_le (α : Dir d → ℕ) : supNormZ (dirHomZ α) ≤ mabs α := by
  show supNormZ (∑ e, α e • dirZ e) ≤ ∑ e, α e
  have key : ∀ s : Finset (Dir d), supNormZ (∑ e ∈ s, α e • dirZ e) ≤ ∑ e ∈ s, α e := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [supNormZ]
    | insert e s he ih =>
      rw [sum_insert he, sum_insert he]
      refine (supNormZ_add_le _ _).trans (add_le_add ?_ ih)
      rw [supNormZ_le_iff]
      intro i
      have := natAbs_le_supNormZ (dirZ e) i
      have h1 := supNormZ_dirZ e
      simp only [Pi.smul_apply, nsmul_eq_mul]
      rw [Int.natAbs_mul, Int.natAbs_natCast]
      nlinarith
  exact key univ

/-! ### Embedding `ℤ^d` into the torus -/

variable {L N : ℕ} [NeZero L]

/-- `u ↦ b + u` from `ℤ^d` to `Λ_N`. -/
def ιZ (b : Lam d L N) (u : Zd d) : Lam d L N := b + prj u

/-- `(u, σ) ↦ (b + u, σ)`. -/
def ιS (b : Lam d L N) (a : Sf (Zd d)) : Sf (Lam d L N) := (ιZ b a.1, a.2)

/-- `(x, σ) ↦ (r(x - b), σ)`, the inverse of `ιS b` on a patch. -/
def ρS (b : Lam d L N) (a : Sf (Lam d L N)) : Sf (Zd d) := (rep (a.1 - b), a.2)

theorem ιS_ρS (b : Lam d L N) (a : Sf (Lam d L N)) : ιS b (ρS b a) = a := by
  simp [ιS, ρS, ιZ, prj_rep]

theorem prj_dirHomZ (α : Dir d → ℕ) : (prj (dirHomZ α) : Lam d L N) = dirHom α := by
  show prj (∑ e, α e • dirZ e) = ∑ e, α e • dirVec e
  have key : ∀ s : Finset (Dir d),
      (prj (∑ e ∈ s, α e • dirZ e) : Lam d L N) = ∑ e ∈ s, α e • dirVec e := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [sum_empty]
      show (fun i => (((0 : Zd d) i : ℤ) : ZMod (L ^ N))) = 0
      funext i; simp
    | insert e s he ih =>
      rw [sum_insert he, sum_insert he, prj_add, ih, ← prj_dirZ]
      congr 1
      show (fun i => (((α e • dirZ e) i : ℤ) : ZMod (L ^ N))) =
        α e • (fun i => ((dirZ e i : ℤ) : ZMod (L ^ N)))
      funext i; simp
  exact key univ

theorem ιZ_vadd (b : Lam d L N) (α : Dir d → ℕ) (u : Zd d) : ιZ b (α +ᵥ u) = α +ᵥ ιZ b u := by
  rw [vaddZ_def, ιZ, prj_add, prj_dirHomZ, Grassmann.vadd_def, ιZ]
  show b + (∑ e, α e • dirVec e + prj u) = ∑ e, α e • dirVec e + (b + prj u)
  abel

theorem ιS_sh (b : Lam d L N) (α : Dir d → ℕ) (a : Sf (Zd d)) : ιS b (sh α a) = sh α (ιS b a) := by
  simp [ιS, sh, ιZ_vadd]

/-- Equivariance: `∇^α (g ∘ ιS) = (∇^α g) ∘ ιS`. -/
theorem nab_comp_ιS {W : Type*} [AddCommGroup W] [Module ℝ W] (b : Lam d L N) {n : ℕ}
    (α : Fin n → Dir d → ℕ) (g : (Fin n → Sf (Lam d L N)) → W) (w : Fin n → Sf (Zd d)) :
    nab α (fun w => g (ιS b ∘ w)) w = nab α g (ιS b ∘ w) :=
  nabla_comp_equivariant sh sh (ιS b) (fun β a => ιS_sh b β a) α g w

end

end Loc
