import Step.Defs

/-!
# The algebra with source fields (`e:Nabdecomp`, `e:Fdecomp`)

Section `sec:obs-flow` amends the Grassmann algebra `𝒩(Λ)` by two source fields localised at
points `a, b`.  Every element is written uniquely as (`e:Fdecomp`)

* Case (1): `F = F_∅ + σ_a F_a + σ̄_b F_b + σ_a σ̄_b F_ab`,
* Case (2): `F = F_∅ + σ_a F_a + σ_b F_b + σ_a σ_b F_ab`,

with `F_∅, F_a, F_b, F_ab ∈ 𝒩(Λ)`.  In Case (1) `σ_a, σ̄_b` are odd Grassmann generators
(anticommuting with each other and with `ψ, ψ̄`); in Case (2) `σ_a = ϑ̄_a ϑ_a`, `σ_b = ϑ̄_b ϑ_b`
are even, commuting, and `σ_a² = σ_b² = 0`.  We do not adjoin generators: we represent `F` by
its four components (`SA c Λ`, a structure with fields `e a b ab`) and put the multiplication
of the (super) tensor product on the four-tuples.

## Conventions
* `Case` is `one` or `two`; `Case.p` is `1` resp. `2`.
* `Case.tau c : 𝒩(Λ) →ₐ 𝒩(Λ)` is the grade involution `inv'` in Case (1) and the identity in
  Case (2): moving `x ∈ 𝒩(Λ)` to the right past a source field gives `x σ = σ (τ x)`.
* `Case.s c` is `-1` in Case (1) and `1` in Case (2): `σ̄_b σ_a = s σ_a σ̄_b`
  (resp. `σ_b σ_a = σ_a σ_b`).  It is also the parity of `σ_a`, `σ̄_b`.
* Multiplication (`mul_e`, `mul_a`, `mul_b`, `mul_ab`):
  `(FG)_∅ = F_∅ G_∅`, `(FG)_a = τ(F_∅) G_a + F_a G_∅`, `(FG)_b = τ(F_∅) G_b + F_b G_∅`,
  `(FG)_ab = F_∅ G_ab + τ(F_a) G_b + s τ(F_b) G_a + F_ab G_∅`.
  E.g. in Case (1) for odd `F_a`: `(σ_a F_a)(σ̄_b G_b) = σ_a σ̄_b τ(F_a) G_b = -σ_a σ̄_b F_a G_b`.
* `sa, sb, sab` are the source monomials `σ_a`, `σ̄_b` (resp. `σ_b`) and `σ_a σ̄_b`
  (resp. `σ_a σ_b`), and `ofN : 𝒩(Λ) →ₐ SA c Λ` is the inclusion of bulk elements, so
  `F = ofN F_∅ + sa * ofN F_a + sb * ofN F_b + sab * ofN F_ab` (`eq_decomp`).

## Even elements
`invS` is the grade involution of the amended algebra (`σ_a`, `σ̄_b` odd in Case (1)); the even
elements `OEv c Λ` (its fixed points) are: `F_∅, F_ab` even and `inv' F_a = s F_a`,
`inv' F_b = s F_b` (i.e. `F_a, F_b` odd in Case (1), even in Case (2)) (`mem_OEv`).
`OE c Λ` (the type of even elements) is a *commutative* `ℂ`-algebra (with the `ℚ`-module
structure induced from `ℂ`, so that `IsNilpotent.exp` applies).  On even elements
`(FG)_ab = F_∅ G_ab + s F_a G_b + F_b G_a + F_ab G_∅` (`OE.mul_ab`).

## Projections and the bulk component
`pie, pia, pib, piab, piobs` (on `SA`) and `πe, πa, πb, πab, πobs` (on `OE`) are the projections
`π_∅, π_a, π_b, π_ab, π_obs = π_a + π_b + π_ab`; they keep the source monomials, e.g.
`π_a F = σ_a F_a`.  `bulk : OE c Λ →ₐ[ℂ] EvR Λ` is `F ↦ F_∅` (a ring hom: the bulk component
of a product only depends on the bulk components), and `emb : EvR Λ →ₐ[ℂ] OE c Λ` the
embedding of bulk elements.  An element is *observable* (`IsObs`) if `F_∅ = 0`; products of
three observable elements vanish (`mul_mul_eq_zero_of_isObs`, the principle behind
`e:norm-obs-nonmon`).
-/

namespace Obs

noncomputable section

open Finset Grassmann

/-! ### The two cases -/

/-- Case (1) (`⟨ψ̄_a ψ_b⟩`, odd source fields) and Case (2) (`⟨ψ̄_a ψ_a ψ̄_b ψ_b⟩`, even
source fields). -/
inductive Case
  | one
  | two
  deriving DecidableEq

namespace Case

/-- `p = 1` in Case (1) and `p = 2` in Case (2). -/
def p : Case → ℕ
  | one => 1
  | two => 2

/-- The sign `s`: `σ̄_b σ_a = s σ_a σ̄_b`; also the parity of the source fields. -/
def s : Case → ℂ
  | one => -1
  | two => 1

/-- `τ`: `x σ = σ τ(x)` for `x ∈ 𝒩(Λ)` and a source field `σ`. -/
def tau {Λ : Type*} : Case → (N Λ →ₐ[ℂ] N Λ)
  | one => inv'
  | two => AlgHom.id ℂ (N Λ)

@[simp] theorem p_one : one.p = 1 := rfl
@[simp] theorem p_two : two.p = 2 := rfl
@[simp] theorem s_one : one.s = -1 := rfl
@[simp] theorem s_two : two.s = 1 := rfl

theorem tau_one {Λ : Type*} (x : N Λ) : one.tau x = inv' x := rfl
theorem tau_two {Λ : Type*} (x : N Λ) : two.tau x = x := rfl

theorem s_mul_s (c : Case) : c.s * c.s = 1 := by cases c <;> simp

@[simp] theorem norm_s (c : Case) : ‖c.s‖ = 1 := by cases c <;> simp

@[simp] theorem tau_tau {Λ : Type*} (c : Case) (x : N Λ) : c.tau (c.tau x) = x := by
  cases c
  · exact inv'_inv' x
  · rfl

theorem tau_inv' {Λ : Type*} (c : Case) (x : N Λ) : c.tau (inv' x) = inv' (c.tau x) := by
  cases c <;> rfl

/-- `τ` commutes with the maps induced by linear maps of the generators. -/
theorem tau_comm {Λ Λ' : Type*} (c : Case) (f : N Λ →ₐ[ℂ] N Λ')
    (hf : ∀ x, f (inv' x) = inv' (f x)) (x : N Λ) : c.tau (f x) = f (c.tau x) := by
  cases c
  · exact (hf x).symm
  · rfl

/-- On elements of parity `s` (`inv' x = s x`), `τ x = s x`. -/
theorem tau_of_par {Λ : Type*} (c : Case) {x : N Λ} (hx : inv' x = c.s • x) :
    c.tau x = c.s • x := by
  cases c
  · exact hx
  · simp [tau_two]

/-- On even elements, `τ x = x`. -/
theorem tau_of_even {Λ : Type*} (c : Case) {x : N Λ} (hx : inv' x = x) : c.tau x = x := by
  cases c
  · exact hx
  · rfl

end Case

/-! ### Graded commutativity -/

section Graded

variable {Λ : Type*}

/-- An odd element `x` satisfies `x y = inv'(y) x`. -/
theorem odd_mul {x : N Λ} (hx : inv' x = -x) (y : N Λ) : x * y = inv' y * x := by
  induction y using CliffordAlgebra.induction with
  | algebraMap r => simp [Algebra.commutes]
  | ι n =>
    have h := ι_mul_eq (R := ℂ) n x
    rw [hx, neg_mul] at h
    rw [inv'_ι, neg_mul, h, neg_neg]
  | mul a b ha hb => rw [← mul_assoc, ha, mul_assoc, hb, ← mul_assoc, map_mul]
  | add a b ha hb => rw [mul_add, ha, hb, map_add, add_mul]

/-- Elements of parity `s` supercommute: `x y = s y x`. -/
theorem mul_of_par (c : Case) {x y : N Λ} (hx : inv' x = c.s • x) (hy : inv' y = c.s • y) :
    x * y = c.s • (y * x) := by
  cases c
  · have hx' : inv' x = -x := by simpa using hx
    have hy' : inv' y = -y := by simpa using hy
    rw [odd_mul hx', hy']; simp
  · have hx' : inv' x = x := by simpa using hx
    simp [mul_comm_of_even hx' y]

end Graded

/-! ### The amended algebra -/

/-- An element `F = F_∅ + σ_a F_a + σ̄_b F_b + σ_a σ̄_b F_ab` (Case (1)) resp.
`F_∅ + σ_a F_a + σ_b F_b + σ_a σ_b F_ab` (Case (2)) of the algebra with source fields. -/
@[ext]
structure SA (c : Case) (Λ : Type*) where
  /-- The bulk component `F_∅`. -/
  e : N Λ
  /-- The component `F_a`. -/
  a : N Λ
  /-- The component `F_b`. -/
  b : N Λ
  /-- The component `F_ab`. -/
  ab : N Λ

namespace SA

variable {c : Case} {Λ Λ' : Type*}

/-- The four components. -/
def toT (F : SA c Λ) : N Λ × N Λ × N Λ × N Λ := (F.e, F.a, F.b, F.ab)

theorem toT_injective : Function.Injective (toT : SA c Λ → _) := by
  intro F G h
  simp only [toT, Prod.mk.injEq] at h
  ext <;> simp [h]

instance : Zero (SA c Λ) := ⟨⟨0, 0, 0, 0⟩⟩
instance : Add (SA c Λ) := ⟨fun F G => ⟨F.e + G.e, F.a + G.a, F.b + G.b, F.ab + G.ab⟩⟩
instance : Neg (SA c Λ) := ⟨fun F => ⟨-F.e, -F.a, -F.b, -F.ab⟩⟩
instance : Sub (SA c Λ) := ⟨fun F G => ⟨F.e - G.e, F.a - G.a, F.b - G.b, F.ab - G.ab⟩⟩
instance : SMul ℕ (SA c Λ) := ⟨fun n F => ⟨n • F.e, n • F.a, n • F.b, n • F.ab⟩⟩
instance : SMul ℤ (SA c Λ) := ⟨fun n F => ⟨n • F.e, n • F.a, n • F.b, n • F.ab⟩⟩
instance : SMul ℂ (SA c Λ) := ⟨fun r F => ⟨r • F.e, r • F.a, r • F.b, r • F.ab⟩⟩

@[simp] theorem zero_e : (0 : SA c Λ).e = 0 := rfl
@[simp] theorem zero_a : (0 : SA c Λ).a = 0 := rfl
@[simp] theorem zero_b : (0 : SA c Λ).b = 0 := rfl
@[simp] theorem zero_ab : (0 : SA c Λ).ab = 0 := rfl
@[simp] theorem add_e (F G : SA c Λ) : (F + G).e = F.e + G.e := rfl
@[simp] theorem add_a (F G : SA c Λ) : (F + G).a = F.a + G.a := rfl
@[simp] theorem add_b (F G : SA c Λ) : (F + G).b = F.b + G.b := rfl
@[simp] theorem add_ab (F G : SA c Λ) : (F + G).ab = F.ab + G.ab := rfl
@[simp] theorem neg_e (F : SA c Λ) : (-F).e = -F.e := rfl
@[simp] theorem neg_a (F : SA c Λ) : (-F).a = -F.a := rfl
@[simp] theorem neg_b (F : SA c Λ) : (-F).b = -F.b := rfl
@[simp] theorem neg_ab (F : SA c Λ) : (-F).ab = -F.ab := rfl
@[simp] theorem sub_e (F G : SA c Λ) : (F - G).e = F.e - G.e := rfl
@[simp] theorem sub_a (F G : SA c Λ) : (F - G).a = F.a - G.a := rfl
@[simp] theorem sub_b (F G : SA c Λ) : (F - G).b = F.b - G.b := rfl
@[simp] theorem sub_ab (F G : SA c Λ) : (F - G).ab = F.ab - G.ab := rfl
@[simp] theorem smul_e (r : ℂ) (F : SA c Λ) : (r • F).e = r • F.e := rfl
@[simp] theorem smul_a (r : ℂ) (F : SA c Λ) : (r • F).a = r • F.a := rfl
@[simp] theorem smul_b (r : ℂ) (F : SA c Λ) : (r • F).b = r • F.b := rfl
@[simp] theorem smul_ab (r : ℂ) (F : SA c Λ) : (r • F).ab = r • F.ab := rfl

instance : AddCommGroup (SA c Λ) :=
  Function.Injective.addCommGroup toT toT_injective rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/-- The components as an additive map. -/
def toTHom : SA c Λ →+ N Λ × N Λ × N Λ × N Λ where
  toFun := toT
  map_zero' := rfl
  map_add' _ _ := rfl

instance : Module ℂ (SA c Λ) :=
  Function.Injective.module ℂ toTHom toT_injective fun _ _ => rfl

@[simp] theorem nsmul_e (n : ℕ) (F : SA c Λ) : (n • F).e = n • F.e := rfl
@[simp] theorem nsmul_a (n : ℕ) (F : SA c Λ) : (n • F).a = n • F.a := rfl
@[simp] theorem nsmul_b (n : ℕ) (F : SA c Λ) : (n • F).b = n • F.b := rfl
@[simp] theorem nsmul_ab (n : ℕ) (F : SA c Λ) : (n • F).ab = n • F.ab := rfl

theorem sum_e {ι : Type*} (s : Finset ι) (F : ι → SA c Λ) : (∑ i ∈ s, F i).e = ∑ i ∈ s, (F i).e :=
  map_sum (⟨⟨fun G : SA c Λ => G.e, rfl⟩, fun _ _ => rfl⟩ : SA c Λ →+ N Λ) F s
theorem sum_a {ι : Type*} (s : Finset ι) (F : ι → SA c Λ) : (∑ i ∈ s, F i).a = ∑ i ∈ s, (F i).a :=
  map_sum (⟨⟨fun G : SA c Λ => G.a, rfl⟩, fun _ _ => rfl⟩ : SA c Λ →+ N Λ) F s
theorem sum_b {ι : Type*} (s : Finset ι) (F : ι → SA c Λ) : (∑ i ∈ s, F i).b = ∑ i ∈ s, (F i).b :=
  map_sum (⟨⟨fun G : SA c Λ => G.b, rfl⟩, fun _ _ => rfl⟩ : SA c Λ →+ N Λ) F s
theorem sum_ab {ι : Type*} (s : Finset ι) (F : ι → SA c Λ) :
    (∑ i ∈ s, F i).ab = ∑ i ∈ s, (F i).ab :=
  map_sum (⟨⟨fun G : SA c Λ => G.ab, rfl⟩, fun _ _ => rfl⟩ : SA c Λ →+ N Λ) F s

/-! #### Multiplication -/

instance : One (SA c Λ) := ⟨⟨1, 0, 0, 0⟩⟩
instance : NatCast (SA c Λ) := ⟨fun n => ⟨n, 0, 0, 0⟩⟩
instance : IntCast (SA c Λ) := ⟨fun n => ⟨n, 0, 0, 0⟩⟩

@[simp] theorem natCast_e (n : ℕ) : (n : SA c Λ).e = n := rfl
@[simp] theorem natCast_a (n : ℕ) : (n : SA c Λ).a = 0 := rfl
@[simp] theorem natCast_b (n : ℕ) : (n : SA c Λ).b = 0 := rfl
@[simp] theorem natCast_ab (n : ℕ) : (n : SA c Λ).ab = 0 := rfl
@[simp] theorem intCast_e (n : ℤ) : (n : SA c Λ).e = n := rfl
@[simp] theorem intCast_a (n : ℤ) : (n : SA c Λ).a = 0 := rfl
@[simp] theorem intCast_b (n : ℤ) : (n : SA c Λ).b = 0 := rfl
@[simp] theorem intCast_ab (n : ℤ) : (n : SA c Λ).ab = 0 := rfl

instance : Mul (SA c Λ) :=
  ⟨fun F G => ⟨F.e * G.e, c.tau F.e * G.a + F.a * G.e, c.tau F.e * G.b + F.b * G.e,
    F.e * G.ab + c.tau F.a * G.b + c.s • (c.tau F.b * G.a) + F.ab * G.e⟩⟩

@[simp] theorem one_e : (1 : SA c Λ).e = 1 := rfl
@[simp] theorem one_a : (1 : SA c Λ).a = 0 := rfl
@[simp] theorem one_b : (1 : SA c Λ).b = 0 := rfl
@[simp] theorem one_ab : (1 : SA c Λ).ab = 0 := rfl

@[simp] theorem mul_e (F G : SA c Λ) : (F * G).e = F.e * G.e := rfl
@[simp] theorem mul_a (F G : SA c Λ) : (F * G).a = c.tau F.e * G.a + F.a * G.e := rfl
@[simp] theorem mul_b (F G : SA c Λ) : (F * G).b = c.tau F.e * G.b + F.b * G.e := rfl
@[simp] theorem mul_ab (F G : SA c Λ) :
    (F * G).ab = F.e * G.ab + c.tau F.a * G.b + c.s • (c.tau F.b * G.a) + F.ab * G.e := rfl

private theorem mul_assoc' (F G H : SA c Λ) : F * G * H = F * (G * H) := by
  ext <;> simp only [mul_e, mul_a, mul_b, mul_ab, map_add, map_mul, Case.tau_tau,
    mul_add, add_mul, mul_assoc, smul_mul_assoc, mul_smul_comm, smul_add] <;> abel

instance : Ring (SA c Λ) :=
  { (inferInstance : AddCommGroup (SA c Λ)) with
    mul_assoc := mul_assoc'
    one_mul := fun F => by ext <;> simp
    mul_one := fun F => by ext <;> simp
    left_distrib := fun F G H => by
      ext <;> simp only [mul_e, mul_a, mul_b, mul_ab, add_e, add_a, add_b, add_ab, mul_add,
        smul_add] <;> abel
    right_distrib := fun F G H => by
      ext <;> simp only [mul_e, mul_a, mul_b, mul_ab, add_e, add_a, add_b, add_ab, add_mul,
        map_add, smul_add] <;> abel
    zero_mul := fun F => by ext <;> simp
    mul_zero := fun F => by ext <;> simp
    natCast_zero := by ext <;> simp
    natCast_succ := fun n => by ext <;> simp
    intCast_ofNat := fun n => by ext <;> simp
    intCast_negSucc := fun n => by ext <;> simp [Int.negSucc_eq] <;> ring }

instance : Algebra ℂ (SA c Λ) :=
  Algebra.ofModule
    (fun r F G => by ext <;> simp [smul_add, smul_mul_assoc, smul_comm r c.s])
    (fun r F G => by ext <;> simp [smul_add, mul_smul_comm, smul_comm r c.s])

theorem algebraMap_eq (r : ℂ) : algebraMap ℂ (SA c Λ) r = ⟨algebraMap ℂ (N Λ) r, 0, 0, 0⟩ := by
  rw [Algebra.algebraMap_eq_smul_one]
  ext <;> simp [Algebra.algebraMap_eq_smul_one]

@[simp] theorem algebraMap_e (r : ℂ) : (algebraMap ℂ (SA c Λ) r).e = algebraMap ℂ (N Λ) r := by
  rw [algebraMap_eq]
@[simp] theorem algebraMap_a (r : ℂ) : (algebraMap ℂ (SA c Λ) r).a = 0 := by rw [algebraMap_eq]
@[simp] theorem algebraMap_b (r : ℂ) : (algebraMap ℂ (SA c Λ) r).b = 0 := by rw [algebraMap_eq]
@[simp] theorem algebraMap_ab (r : ℂ) : (algebraMap ℂ (SA c Λ) r).ab = 0 := by
  rw [algebraMap_eq]

@[simp] theorem pow_e (F : SA c Λ) (n : ℕ) : (F ^ n).e = F.e ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; rfl
  | succ n ih => rw [pow_succ, mul_e, ih, pow_succ]

/-! #### Source monomials and the embedding of bulk elements -/

/-- The inclusion `𝒩(Λ) → SA c Λ` of bulk elements. -/
def ofN : N Λ →ₐ[ℂ] SA c Λ where
  toFun x := ⟨x, 0, 0, 0⟩
  map_one' := rfl
  map_mul' x y := by ext <;> simp
  map_zero' := rfl
  map_add' x y := by ext <;> simp
  commutes' r := by rw [algebraMap_eq]

@[simp] theorem ofN_e (x : N Λ) : (ofN x : SA c Λ).e = x := rfl
@[simp] theorem ofN_a (x : N Λ) : (ofN x : SA c Λ).a = 0 := rfl
@[simp] theorem ofN_b (x : N Λ) : (ofN x : SA c Λ).b = 0 := rfl
@[simp] theorem ofN_ab (x : N Λ) : (ofN x : SA c Λ).ab = 0 := rfl



/-! #### Maps -/

/-- The map induced by an algebra hom of the bulk algebras commuting with `inv'`
(componentwise). -/
def mapS (f : N Λ →ₐ[ℂ] N Λ') (hf : ∀ x, f (inv' x) = inv' (f x)) : SA c Λ →ₐ[ℂ] SA c Λ' where
  toFun F := ⟨f F.e, f F.a, f F.b, f F.ab⟩
  map_one' := by ext <;> simp
  map_mul' F G := by
    ext <;> simp [map_add, map_mul, map_smul, Case.tau_comm c f hf]
  map_zero' := by ext <;> simp
  map_add' F G := by ext <;> simp
  commutes' r := by ext <;> simp

@[simp] theorem mapS_e (f : N Λ →ₐ[ℂ] N Λ') (hf) (F : SA c Λ) : (mapS f hf F).e = f F.e := rfl
@[simp] theorem mapS_a (f : N Λ →ₐ[ℂ] N Λ') (hf) (F : SA c Λ) : (mapS f hf F).a = f F.a := rfl
@[simp] theorem mapS_b (f : N Λ →ₐ[ℂ] N Λ') (hf) (F : SA c Λ) : (mapS f hf F).b = f F.b := rfl
@[simp] theorem mapS_ab (f : N Λ →ₐ[ℂ] N Λ') (hf) (F : SA c Λ) : (mapS f hf F).ab = f F.ab :=
  rfl

/-- The map induced by a linear map of the bulk algebras (componentwise). -/
def mapL (f : N Λ →ₗ[ℂ] N Λ') : SA c Λ →ₗ[ℂ] SA c Λ' where
  toFun F := ⟨f F.e, f F.a, f F.b, f F.ab⟩
  map_add' F G := by ext <;> simp
  map_smul' r F := by ext <;> simp

@[simp] theorem mapL_e (f : N Λ →ₗ[ℂ] N Λ') (F : SA c Λ) : (mapL f F).e = f F.e := rfl
@[simp] theorem mapL_a (f : N Λ →ₗ[ℂ] N Λ') (F : SA c Λ) : (mapL f F).a = f F.a := rfl
@[simp] theorem mapL_b (f : N Λ →ₗ[ℂ] N Λ') (F : SA c Λ) : (mapL f F).b = f F.b := rfl
@[simp] theorem mapL_ab (f : N Λ →ₗ[ℂ] N Λ') (F : SA c Λ) : (mapL f F).ab = f F.ab := rfl

/-- The grade involution of the amended algebra (`σ_a`, `σ̄_b` have parity `s`). -/
def invS : SA c Λ →ₐ[ℂ] SA c Λ where
  toFun F := ⟨inv' F.e, c.s • inv' F.a, c.s • inv' F.b, inv' F.ab⟩
  map_one' := by ext <;> simp
  map_mul' F G := by
    ext <;> simp only [mul_e, mul_a, mul_b, mul_ab, map_add, map_mul, map_smul, Case.tau_inv',
      smul_add, mul_smul_comm, smul_mul_assoc, smul_smul, Case.s_mul_s, one_smul, mul_comm c.s]
  map_zero' := by ext <;> simp
  map_add' F G := by ext <;> simp [smul_add]
  commutes' r := by ext <;> simp

@[simp] theorem invS_e (F : SA c Λ) : (invS F).e = inv' F.e := rfl
@[simp] theorem invS_a (F : SA c Λ) : (invS F).a = c.s • inv' F.a := rfl
@[simp] theorem invS_b (F : SA c Λ) : (invS F).b = c.s • inv' F.b := rfl
@[simp] theorem invS_ab (F : SA c Λ) : (invS F).ab = inv' F.ab := rfl

/-! #### Projections -/

/-- `π_∅`. -/
def pie : SA c Λ →ₗ[ℂ] SA c Λ where
  toFun F := ⟨F.e, 0, 0, 0⟩
  map_add' F G := by ext <;> simp
  map_smul' r F := by ext <;> simp

/-- `π_a`: `π_a F = σ_a F_a`. -/
def pia : SA c Λ →ₗ[ℂ] SA c Λ where
  toFun F := ⟨0, F.a, 0, 0⟩
  map_add' F G := by ext <;> simp
  map_smul' r F := by ext <;> simp

/-- `π_b`. -/
def pib : SA c Λ →ₗ[ℂ] SA c Λ where
  toFun F := ⟨0, 0, F.b, 0⟩
  map_add' F G := by ext <;> simp
  map_smul' r F := by ext <;> simp

/-- `π_ab`. -/
def piab : SA c Λ →ₗ[ℂ] SA c Λ where
  toFun F := ⟨0, 0, 0, F.ab⟩
  map_add' F G := by ext <;> simp
  map_smul' r F := by ext <;> simp

/-- `π_obs = π_a + π_b + π_ab`. -/
def piobs : SA c Λ →ₗ[ℂ] SA c Λ := pia + pib + piab

theorem pie_apply (F : SA c Λ) : pie F = ⟨F.e, 0, 0, 0⟩ := rfl
theorem pia_apply (F : SA c Λ) : pia F = ⟨0, F.a, 0, 0⟩ := rfl
theorem pib_apply (F : SA c Λ) : pib F = ⟨0, 0, F.b, 0⟩ := rfl
theorem piab_apply (F : SA c Λ) : piab F = ⟨0, 0, 0, F.ab⟩ := rfl
theorem piobs_apply (F : SA c Λ) : piobs F = ⟨0, F.a, F.b, F.ab⟩ := by
  ext <;> simp [piobs, pia, pib, piab]


theorem pie_add_piobs (F : SA c Λ) : pie F + piobs F = F := by
  rw [piobs_apply]; ext <;> simp [pie_apply]

/-! #### Observable elements -/

/-- `F ∈ 𝒩^obs`: the bulk component vanishes. -/
def IsObs (F : SA c Λ) : Prop := F.e = 0

theorem isObs_piobs (F : SA c Λ) : IsObs (piobs F) := by simp [IsObs, piobs_apply]

/-- The product of two observable elements only has an `ab` component. -/
theorem mul_of_isObs {F G : SA c Λ} (hF : IsObs F) (hG : IsObs G) :
    F * G = ⟨0, 0, 0, c.tau F.a * G.b + c.s • (c.tau F.b * G.a)⟩ := by
  unfold IsObs at hF hG
  ext <;> simp [hF, hG]

/-- Products of three observable elements vanish (the principle behind `e:norm-obs-nonmon`). -/
theorem mul_mul_eq_zero_of_isObs {F G H : SA c Λ} (hF : IsObs F) (hG : IsObs G) (hH : IsObs H) :
    F * G * H = 0 := by
  rw [mul_of_isObs hF hG]
  unfold IsObs at hH
  ext <;> simp [hH]

end SA

/-! ### The even subalgebra -/

open SA

variable {c : Case} {Λ Λ' : Type*}

variable (c Λ) in
/-- The even elements of the amended algebra. -/
def OEv : Subalgebra ℂ (SA c Λ) := AlgHom.equalizer invS (AlgHom.id ℂ (SA c Λ))

variable (c Λ) in
/-- The type of even elements of the amended algebra. -/
abbrev OE := ↥(OEv c Λ)

theorem mem_OEv {F : SA c Λ} :
    F ∈ OEv c Λ ↔ inv' F.e = F.e ∧ inv' F.a = c.s • F.a ∧ inv' F.b = c.s • F.b ∧
      inv' F.ab = F.ab := by
  simp only [OEv, AlgHom.mem_equalizer, AlgHom.id_apply, SA.ext_iff, invS_e, invS_a, invS_b,
    invS_ab]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, ?_, ?_, h4⟩
    · have := congrArg (c.s • ·) h2
      simpa [smul_smul, Case.s_mul_s] using this
    · have := congrArg (c.s • ·) h3
      simpa [smul_smul, Case.s_mul_s] using this
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, ?_, ?_, h4⟩
    · rw [h2, smul_smul, Case.s_mul_s, one_smul]
    · rw [h3, smul_smul, Case.s_mul_s, one_smul]

namespace OE

theorem par_e (F : OE c Λ) : inv' (F : SA c Λ).e = (F : SA c Λ).e := (mem_OEv.1 F.2).1
theorem par_a (F : OE c Λ) : inv' (F : SA c Λ).a = c.s • (F : SA c Λ).a := (mem_OEv.1 F.2).2.1
theorem par_b (F : OE c Λ) : inv' (F : SA c Λ).b = c.s • (F : SA c Λ).b :=
  (mem_OEv.1 F.2).2.2.1
theorem par_ab (F : OE c Λ) : inv' (F : SA c Λ).ab = (F : SA c Λ).ab := (mem_OEv.1 F.2).2.2.2

theorem e_mem (F : OE c Λ) : (F : SA c Λ).e ∈ Step.Ev Λ := Step.mem_Ev.2 F.par_e
theorem ab_mem (F : OE c Λ) : (F : SA c Λ).ab ∈ Step.Ev Λ := Step.mem_Ev.2 F.par_ab

/-- In Case (1), `F_a` is odd. -/
theorem isOdd_a (F : OE Case.one Λ) : Step.IsOdd (F : SA Case.one Λ).a := by
  show inv' _ = -_
  simpa using F.par_a

/-- In Case (1), `F_b` is odd. -/
theorem isOdd_b (F : OE Case.one Λ) : Step.IsOdd (F : SA Case.one Λ).b := by
  show inv' _ = -_
  simpa using F.par_b

/-- In Case (2), `F_a` is even. -/
theorem a_mem (F : OE Case.two Λ) : (F : SA Case.two Λ).a ∈ Step.Ev Λ :=
  Step.mem_Ev.2 (by have := F.par_a; simpa using this)

/-- In Case (2), `F_b` is even. -/
theorem b_mem (F : OE Case.two Λ) : (F : SA Case.two Λ).b ∈ Step.Ev Λ :=
  Step.mem_Ev.2 (by have := F.par_b; simpa using this)

/-- The `ab` component of a product of even elements. -/
theorem mul_ab (F G : OE c Λ) :
    ((F * G : OE c Λ) : SA c Λ).ab = (F : SA c Λ).e * (G : SA c Λ).ab +
      c.s • ((F : SA c Λ).a * (G : SA c Λ).b) + (F : SA c Λ).b * (G : SA c Λ).a +
      (F : SA c Λ).ab * (G : SA c Λ).e := by
  show ((F : SA c Λ) * G).ab = _
  rw [SA.mul_ab, c.tau_of_par F.par_a, c.tau_of_par F.par_b, smul_mul_assoc, smul_mul_assoc,
    smul_smul, Case.s_mul_s, one_smul]

theorem mul_a (F G : OE c Λ) :
    ((F * G : OE c Λ) : SA c Λ).a = (F : SA c Λ).e * (G : SA c Λ).a +
      (F : SA c Λ).a * (G : SA c Λ).e := by
  show ((F : SA c Λ) * G).a = _
  rw [SA.mul_a, c.tau_of_even F.par_e]

theorem mul_b (F G : OE c Λ) :
    ((F * G : OE c Λ) : SA c Λ).b = (F : SA c Λ).e * (G : SA c Λ).b +
      (F : SA c Λ).b * (G : SA c Λ).e := by
  show ((F : SA c Λ) * G).b = _
  rw [SA.mul_b, c.tau_of_even F.par_e]

theorem mul_e (F G : OE c Λ) :
    ((F * G : OE c Λ) : SA c Λ).e = (F : SA c Λ).e * (G : SA c Λ).e := rfl

private theorem mul_comm' (F G : OE c Λ) : F * G = G * F := by
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_)
  · rw [mul_e, mul_e, mul_comm_of_even F.par_e]
  · rw [mul_a, mul_a, mul_comm_of_even F.par_e, mul_comm_of_even G.par_e]; abel
  · rw [mul_b, mul_b, mul_comm_of_even F.par_e, mul_comm_of_even G.par_e]; abel
  · rw [mul_ab, mul_ab, mul_comm_of_even F.par_e, mul_comm_of_even G.par_e,
      mul_of_par c F.par_a G.par_b, mul_of_par c F.par_b G.par_a, smul_smul, Case.s_mul_s,
      one_smul]
    abel

instance : CommRing (OE c Λ) :=
  { (inferInstance : Ring (OE c Λ)) with mul_comm := mul_comm' }

instance : Module ℚ (OE c Λ) := Module.compHom (OE c Λ) (algebraMap ℚ ℂ)

theorem qsmul_eq (q : ℚ) (F : OE c Λ) : q • F = (q : ℂ) • F := rfl

end OE

/-! ### Maps on even elements -/

/-- The restriction of `mapS f` to even elements. -/
def mapO (f : N Λ →ₐ[ℂ] N Λ') (hf : ∀ x, f (inv' x) = inv' (f x)) : OE c Λ →ₐ[ℂ] OE c Λ' :=
  ((mapS f hf).comp (OEv c Λ).val).codRestrict (OEv c Λ') fun F => by
    obtain ⟨h1, h2, h3, h4⟩ := mem_OEv.1 F.2
    refine mem_OEv.2 ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [AlgHom.comp_apply, Subalgebra.coe_val, mapS_e, mapS_a, mapS_b, mapS_ab,
        ← hf, h1, h2, h3, h4, map_smul]

@[simp] theorem coe_mapO (f : N Λ →ₐ[ℂ] N Λ') (hf) (F : OE c Λ) :
    (mapO f hf F : SA c Λ') = mapS f hf (F : SA c Λ) := rfl

/-- The embedding of bulk even elements. -/
def emb : Step.EvR Λ →ₐ[ℂ] OE c Λ :=
  (ofN.comp (Step.Ev Λ).val).codRestrict (OEv c Λ) fun x => by
    refine mem_OEv.2 ⟨?_, ?_, ?_, ?_⟩ <;> simp [Step.mem_Ev.1 x.2]

@[simp] theorem coe_emb (x : Step.EvR Λ) : ((emb x : OE c Λ) : SA c Λ) = ofN (x : N Λ) := rfl

/-- The bulk component `π_∅ F = F_∅`, a ring hom. -/
def bulkS : SA c Λ →ₐ[ℂ] N Λ where
  toFun F := F.e
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' r := by simp

@[simp] theorem bulkS_apply (F : SA c Λ) : bulkS F = F.e := rfl

/-- The bulk component `F ↦ F_∅` of even elements, a ring hom. -/
def bulk : OE c Λ →ₐ[ℂ] Step.EvR Λ :=
  (bulkS.comp (OEv c Λ).val).codRestrict (Step.Ev Λ) fun F => OE.e_mem F

@[simp] theorem coe_bulk (F : OE c Λ) : (bulk F : N Λ) = (F : SA c Λ).e := rfl

@[simp] theorem bulk_emb (x : Step.EvR Λ) : bulk (emb x : OE c Λ) = x := rfl

/-- The `ab` component of an even element, as an even element of `𝒩(Λ)`. -/
def abE (F : OE c Λ) : Step.EvR Λ := ⟨(F : SA c Λ).ab, F.ab_mem⟩

@[simp] theorem coe_abE (F : OE c Λ) : (abE F : N Λ) = (F : SA c Λ).ab := rfl

/-- The projections on even elements. -/
def restrictL (T : SA c Λ →ₗ[ℂ] SA c Λ) (hT : ∀ F ∈ OEv c Λ, T F ∈ OEv c Λ) :
    OE c Λ →ₗ[ℂ] OE c Λ :=
  (T.comp (OEv c Λ).val.toLinearMap).codRestrict (OEv c Λ).toSubmodule fun F => hT F F.2

theorem mem_OEv_of (F : SA c Λ) {G : OE c Λ}
    (he : F.e = 0 ∨ F.e = (G : SA c Λ).e) (ha : F.a = 0 ∨ F.a = (G : SA c Λ).a)
    (hb : F.b = 0 ∨ F.b = (G : SA c Λ).b) (hab : F.ab = 0 ∨ F.ab = (G : SA c Λ).ab) :
    F ∈ OEv c Λ := by
  refine mem_OEv.2 ⟨?_, ?_, ?_, ?_⟩
  · rcases he with h | h <;> simp [h, G.par_e]
  · rcases ha with h | h <;> simp [h, G.par_a]
  · rcases hb with h | h <;> simp [h, G.par_b]
  · rcases hab with h | h <;> simp [h, G.par_ab]

/-- `π_∅` on even elements. -/
def πe : OE c Λ →ₗ[ℂ] OE c Λ :=
  restrictL pie fun F hF => mem_OEv_of (G := ⟨F, hF⟩) _ (.inr rfl) (.inl rfl) (.inl rfl) (.inl rfl)
/-- `π_a` on even elements. -/
def πa : OE c Λ →ₗ[ℂ] OE c Λ :=
  restrictL pia fun F hF => mem_OEv_of (G := ⟨F, hF⟩) _ (.inl rfl) (.inr rfl) (.inl rfl) (.inl rfl)
/-- `π_b` on even elements. -/
def πb : OE c Λ →ₗ[ℂ] OE c Λ :=
  restrictL pib fun F hF => mem_OEv_of (G := ⟨F, hF⟩) _ (.inl rfl) (.inl rfl) (.inr rfl) (.inl rfl)
/-- `π_ab` on even elements. -/
def πab : OE c Λ →ₗ[ℂ] OE c Λ :=
  restrictL piab fun F hF =>
    mem_OEv_of (G := ⟨F, hF⟩) _ (.inl rfl) (.inl rfl) (.inl rfl) (.inr rfl)
/-- `π_obs = π_a + π_b + π_ab` on even elements. -/
def πobs : OE c Λ →ₗ[ℂ] OE c Λ := πa + πb + πab

@[simp] theorem coe_πe (F : OE c Λ) : (πe F : SA c Λ) = pie (F : SA c Λ) := rfl
@[simp] theorem coe_πa (F : OE c Λ) : (πa F : SA c Λ) = pia (F : SA c Λ) := rfl
@[simp] theorem coe_πb (F : OE c Λ) : (πb F : SA c Λ) = pib (F : SA c Λ) := rfl
@[simp] theorem coe_πab (F : OE c Λ) : (πab F : SA c Λ) = piab (F : SA c Λ) := rfl
@[simp] theorem coe_πobs (F : OE c Λ) : (πobs F : SA c Λ) = piobs (F : SA c Λ) := rfl

theorem πe_add_πobs (F : OE c Λ) : πe F + πobs F = F :=
  Subtype.ext (pie_add_piobs (F : SA c Λ))

theorem eq_emb_add_πobs (F : OE c Λ) : F = emb (bulk F) + πobs F := (πe_add_πobs F).symm

theorem isObs_πobs (F : OE c Λ) : IsObs (πobs F : SA c Λ) := isObs_piobs _

theorem bulk_πobs (F : OE c Λ) : bulk (πobs F) = 0 := Subtype.ext (isObs_πobs F)

theorem isObs_iff_bulk (F : OE c Λ) : IsObs (F : SA c Λ) ↔ bulk F = 0 := by
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

/-- Products of three observable even elements vanish. -/
theorem OE.mul_mul_eq_zero {F G H : OE c Λ} (hF : bulk F = 0) (hG : bulk G = 0)
    (hH : bulk H = 0) : F * G * H = 0 :=
  Subtype.ext (mul_mul_eq_zero_of_isObs ((isObs_iff_bulk F).2 hF) ((isObs_iff_bulk G).2 hG)
    ((isObs_iff_bulk H).2 hH))

theorem OE.pow_three_eq_zero {F : OE c Λ} (hF : bulk F = 0) : F ^ 3 = 0 := by
  rw [pow_succ, pow_two]; exact OE.mul_mul_eq_zero hF hF hF

/-- `π_obs` of a product (`e:norm-obs-nonmon` for two factors). -/
theorem πobs_mul (F G : OE c Λ) :
    πobs (F * G) = emb (bulk F) * πobs G + πobs F * emb (bulk G) + πobs F * πobs G := by
  have key : ∀ x y o q : OE c Λ, (x + o) * (y + q) - x * y = x * q + o * y + o * q := by
    intros; ring
  have h1 : πobs (F * G) = F * G - emb (bulk (F * G)) := by
    rw [eq_sub_iff_add_eq, add_comm]; exact (eq_emb_add_πobs _).symm
  rw [h1, map_mul, map_mul, ← key]
  rw [← eq_emb_add_πobs F, ← eq_emb_add_πobs G]

end

end Obs
