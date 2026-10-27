import PtCorr2.Obs.ObsHistFrom
import PtCorr.ConstCalc
import Obs2.Flow.GamChain2
import Obs2.Pair.PairChain
import Obs.FlowObsCoeff

/-!
# PR6 (exact): the components of the final object at the last scale

Case (2). At the last scale `N = j + 1` there is a single `N`-block, `𝒫_N(Λ) = {∅, Λ}` and
`K_N(∅) = 1` (`Knext2O_empty`), so the final object with sources is (`finO_last`)

  `F_N = ∏_B Ĩ_N(B) + K_N(Λ)`,  `Ĩ_N(B) = e^{-V_N(B)}(1 + 𝒲_N(B))`.

Restricted to constant fields an even element is `ε F + c2 F·ψψ̄` with `ψψ̄² = 0`, so `(ε, c2)` is
multiplicative in the dual-number sense (`c2(XY) = εX c2Y + c2X εY`). Since the `σ_a` component
(Case 2, all components even) and, without one-point parts, the `σ_aσ_b` component of a product
are derivations of the product (`deriv_prod_of`), the components of `F_N` are explicit:

* **`finO_last_a`** (any observable state): with `α_B = 1 + ε𝒲_N(B)_∅`, `P₀ = ∏_Bα_B`,
  `β_N = ∑_B m₂(V_N(B)_a)`,
  `c2(F_N)_a = β_N·P₀ + R_a`, `ε(F_N)_a = ∑_Bε(𝒲_N(B)_a)∏_{B'≠B}α_{B'} + ε K_N(Λ)_a`, where
  `R_a = ∑_B[(c2𝒲_a(B) - c2V_∅(B)·ε𝒲_a(B))∏_{B'≠B}α_{B'} + ε𝒲_a(B)·c2(∏_{B'≠B}Ĩ(B')_∅)]
  + c2K_N(Λ)_a` (`remC`) only contains the observable parts of `𝒲_N` and `K_N`.
* **`finO_last_ab`** (no one-point parts, e.g. the reduced history): the same with `ab` in place of
  `a` and `r'_N = ∑_Bm₂(V_N(B)_{ab})` in place of `β_N`.

So if `𝒲_N`, `K_N` have no `σ_aσ_b` part, `c2F'_{ab} = r'_N P₀` and `εF'_{ab} = 0` exactly: the
zero-mode identity `c2F'_{ab} = ρ̃·c2F_a` of `PairZeroRelR` holds with `ρ̃ = r'_NP₀/c2F_a ≈ r'_N/β_N`,
and all deviations are activity (`𝒲`, `K`) terms of the last step.
-/

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Step Obs2 Loc LocObs

set_option linter.unusedSectionVars false

/-! ### Derivations along finite products -/

/-- A derivation `D` (relative to a multiplicative `f`) of a commutative monoid, on a
multiplicatively closed predicate: `D(∏x_i) = ∑_iD(x_i)∏_{k≠i}f(x_k)`. -/
theorem deriv_prod_of {ι M R : Type*} [DecidableEq ι] [CommMonoid M] [CommSemiring R]
    (p : M → Prop) (f : M →* R) (D : M → R) (hp1 : p 1)
    (hpm : ∀ x y, p x → p y → p (x * y)) (hD1 : D 1 = 0)
    (hD : ∀ x y, p x → p y → D (x * y) = f x * D y + D x * f y)
    (S : Finset ι) (x : ι → M) (hx : ∀ i ∈ S, p (x i)) :
    p (∏ i ∈ S, x i) ∧ D (∏ i ∈ S, x i) = ∑ i ∈ S, D (x i) * ∏ k ∈ S.erase i, f (x k) := by
  induction S using Finset.induction_on with
  | empty => simp [hp1, hD1]
  | insert a S ha ih =>
    obtain ⟨hpS, hDS⟩ := ih fun i hi => hx i (mem_insert_of_mem hi)
    have hpa := hx a (mem_insert_self a S)
    rw [prod_insert ha]
    refine ⟨hpm _ _ hpa hpS, ?_⟩
    rw [hD _ _ hpa hpS, hDS, sum_insert ha, erase_insert ha, map_prod, add_comm, mul_sum]
    congr 1
    refine sum_congr rfl fun i hi => ?_
    have hne : a ≠ i := fun h => ha (h ▸ hi)
    rw [erase_insert_of_ne hne, prod_insert fun h => ha (mem_of_mem_erase h)]
    ring

section Restr

variable {d L N : ℕ} [NeZero L]

theorem c2_mulE (x y : EvR (Lam d L N)) :
    Suscept.c2 ((x * y : EvR (Lam d L N)) : Grassmann.N (Lam d L N)) =
      ε (x : Grassmann.N (Lam d L N)) * Suscept.c2 (y : Grassmann.N (Lam d L N)) +
        Suscept.c2 (x : Grassmann.N (Lam d L N)) * ε (y : Grassmann.N (Lam d L N)) :=
  PtCorr.c2_mul_of_even (mem_Ev.1 x.2) (mem_Ev.1 y.2)

theorem c2_oneE : Suscept.c2 ((1 : EvR (Lam d L N)) : Grassmann.N (Lam d L N)) = 0 := by
  rw [OneMemClass.coe_one, ← map_one (algebraMap ℂ (Grassmann.N (Lam d L N))),
    Suscept.c2_algebraMap]

/-- `ε` on the even subalgebra, as an algebra hom. -/
def epsR : EvR (Lam d L N) →ₐ[ℂ] ℂ := (ε : Grassmann.N (Lam d L N) →ₐ[ℂ] ℂ).comp (Ev (Lam d L N)).val

@[simp] theorem epsR_apply (x : EvR (Lam d L N)) : epsR x = ε (x : Grassmann.N (Lam d L N)) := rfl

/-- `c2` on the even subalgebra. -/
def c2E (x : EvR (Lam d L N)) : ℂ := Suscept.c2 (x : Grassmann.N (Lam d L N))

theorem c2E_add (x y : EvR (Lam d L N)) : c2E (x + y) = c2E x + c2E y := Suscept.c2_add _ _
theorem c2E_neg (x : EvR (Lam d L N)) : c2E (-x) = -c2E x := PtCorr.c2_neg _
theorem c2E_mul (x y : EvR (Lam d L N)) : c2E (x * y) = epsR x * c2E y + c2E x * epsR y :=
  c2_mulE x y

/-- `c2(∏x_i) = ∑_ic2(x_i)∏_{k≠i}εx_k` on the even subalgebra. -/
theorem c2_prodE {ι : Type*} [DecidableEq ι] (S : Finset ι) (x : ι → EvR (Lam d L N)) :
    c2E (∏ i ∈ S, x i) = ∑ i ∈ S, c2E (x i) * ∏ k ∈ S.erase i, epsR (x k) := by
  have h := (deriv_prod_of (fun _ => True) epsR.toMonoidHom c2E trivial (fun _ _ _ _ => trivial)
    c2_oneE (fun y z _ _ => c2E_mul y z) S x fun _ _ => trivial).2
  exact h

/-- `c2(e^{-V}) = -c2 V` and `ε(e^{-V}) = 1` for `ε V = 0`. -/
theorem eps_c2_gexp_neg {V : EvR (Lam d L N)} (hV : ε (V : Grassmann.N (Lam d L N)) = 0) :
    ε (gexp (-V) : Grassmann.N (Lam d L N)) = 1 ∧
      Suscept.c2 (gexp (-V) : Grassmann.N (Lam d L N)) = -Suscept.c2 (V : Grassmann.N (Lam d L N)) :=
  eps_c2_of_RE (RE_gexp_neg hV)

/-! ### The components as even elements -/

/-- The `σ_a` component (Case 2) as an even element. -/
def aCmp (F : OE .two (Lam d L N)) : EvR (Lam d L N) :=
  ⟨(F : SA .two (Lam d L N)).a, mem_Ev.2 (obsTwo_a_b_even F).1⟩

@[simp] theorem coe_aCmp (F : OE .two (Lam d L N)) :
    (aCmp F : Grassmann.N (Lam d L N)) = (F : SA .two (Lam d L N)).a := rfl

theorem aCmp_mul (F G : OE .two (Lam d L N)) : aCmp (F * G) = bulk F * aCmp G + aCmp F * bulk G :=
  Subtype.ext (OE.mul_a F G)

theorem aCmp_one : aCmp (1 : OE .two (Lam d L N)) = 0 := rfl

theorem abE_mul_ab {F G : OE .two (Lam d L N)}
    (hF : F ∈ (abSub : Subalgebra ℂ (OE .two (Lam d L N))))
    (hG : G ∈ (abSub : Subalgebra ℂ (OE .two (Lam d L N)))) :
    abE (F * G) = bulk F * abE G + abE F * bulk G := by
  refine Subtype.ext ?_
  show ((F * G : OE .two (Lam d L N)) : SA .two (Lam d L N)).ab = _
  rw [OE.mul_ab, hF.1, hF.2, hG.2, zero_mul, smul_zero, add_zero, zero_mul, add_zero]
  rfl

theorem abE_one : abE (1 : OE .two (Lam d L N)) = 0 := rfl

/-- `(∏G_i)_a = ∑_i(G_i)_a∏_{k≠i}(G_k)_∅`. -/
theorem aCmp_prod {ι : Type*} [DecidableEq ι] (S : Finset ι) (G : ι → OE .two (Lam d L N)) :
    aCmp (∏ i ∈ S, G i) = ∑ i ∈ S, aCmp (G i) * ∏ k ∈ S.erase i, bulk (G k) :=
  (deriv_prod_of (fun _ => True) (bulk : OE .two (Lam d L N) →ₐ[ℂ] EvR (Lam d L N)).toMonoidHom
    aCmp trivial (fun _ _ _ _ => trivial) aCmp_one (fun y z _ _ => aCmp_mul y z) S G
    fun _ _ => trivial).2

/-- `(∏G_i)_{ab} = ∑_i(G_i)_{ab}∏_{k≠i}(G_k)_∅` without one-point parts. -/
theorem abE_prod {ι : Type*} [DecidableEq ι] (S : Finset ι) (G : ι → OE .two (Lam d L N))
    (hG : ∀ i ∈ S, G i ∈ (abSub : Subalgebra ℂ (OE .two (Lam d L N)))) :
    abE (∏ i ∈ S, G i) = ∑ i ∈ S, abE (G i) * ∏ k ∈ S.erase i, bulk (G k) :=
  (deriv_prod_of (fun F => F ∈ (abSub : Subalgebra ℂ (OE .two (Lam d L N))))
    (bulk : OE .two (Lam d L N) →ₐ[ℂ] EvR (Lam d L N)).toMonoidHom abE (one_mem _)
    (fun _ _ hx hy => mul_mem hx hy) abE_one (fun _ _ hy hz => abE_mul_ab hy hz) S G hG).2

/-! ### One block factor `e^{-V}(1 + 𝒲)` -/

/-- The components of `e^{-V}` (Case 2): `(e^{-V})_∅ = g`, `(e^{-V})_a = -gV_a`, and without
one-point parts `(e^{-V})_{ab} = -gV_{ab}`, `g = e^{-V_∅}`. -/
theorem oexp_neg_cmp {V : OE .two (Lam d L N)} (hV : ε ((V : SA .two (Lam d L N)).e) = 0) :
    bulk (oexp (-V)) = gexp (-bulk V) ∧ aCmp (oexp (-V)) = -(gexp (-bulk V) * aCmp V) ∧
      (V ∈ (abSub : Subalgebra ℂ (OE .two (Lam d L N))) →
        abE (oexp (-V)) = -(gexp (-bulk V) * abE V)) := by
  set V1 := V - emb (bulk V) with hV1
  have hb : bulk V1 = 0 := by rw [hV1, map_sub, bulk_emb, sub_self]
  have he : V = emb (bulk V) + V1 := by rw [hV1]; abel
  have h := PtCorr.coe_oexp_neg_emb_add (c := .two) (Vb := bulk V) hV hb
  rw [← he] at h
  have ha : (V1 : SA .two (Lam d L N)).a = (V : SA .two (Lam d L N)).a := by
    rw [hV1]; show (V : SA .two (Lam d L N)).a - _ = _; simp
  have hbb : (V1 : SA .two (Lam d L N)).b = (V : SA .two (Lam d L N)).b := by
    rw [hV1]; show (V : SA .two (Lam d L N)).b - _ = _; simp
  have hab : (V1 : SA .two (Lam d L N)).ab = (V : SA .two (Lam d L N)).ab := by
    rw [hV1]; show (V : SA .two (Lam d L N)).ab - _ = _; simp
  refine ⟨Subtype.ext ?_, Subtype.ext ?_, fun hab0 => Subtype.ext ?_⟩
  · show ((oexp (-V) : OE .two (Lam d L N)) : SA .two (Lam d L N)).e = _
    rw [h]
  · show ((oexp (-V) : OE .two (Lam d L N)) : SA .two (Lam d L N)).a = _
    rw [h]
    show (gexp (-bulk V) : Grassmann.N (Lam d L N)) * -(V1 : SA .two (Lam d L N)).a = _
    rw [ha, mul_neg]; rfl
  · show ((oexp (-V) : OE .two (Lam d L N)) : SA .two (Lam d L N)).ab = _
    rw [h]
    show (gexp (-bulk V) : Grassmann.N (Lam d L N)) * (-(V1 : SA .two (Lam d L N)).ab +
      (1 / 2 : ℂ) • (Obs.Case.two.s • ((V1 : SA .two (Lam d L N)).a *
        (V1 : SA .two (Lam d L N)).b) + (V1 : SA .two (Lam d L N)).b *
          (V1 : SA .two (Lam d L N)).a)) = _
    rw [ha, hbb, hab, hab0.1, hab0.2]
    simp only [mul_zero, smul_zero, add_zero, mul_neg]
    rfl

theorem eps_bulk_one_add (W : OE .two (Lam d L N)) :
    epsR (bulk (1 + W)) = 1 + ε ((W : SA .two (Lam d L N)).e) := by
  rw [map_add, map_one, map_add, map_one]; rfl

theorem c2E_bulk_one_add (W : OE .two (Lam d L N)) :
    c2E (bulk (1 + W)) = Suscept.c2 ((W : SA .two (Lam d L N)).e) := by
  rw [map_add, map_one, c2E_add]; unfold c2E; rw [c2_oneE, zero_add]; rfl

/-- **One block factor, `σ_a` component**: for `G = e^{-V}(1 + 𝒲)` with `εV_∅ = εV_a = 0`,
`ε G_∅ = 1 + ε𝒲_∅`, `ε G_a = ε𝒲_a`, `c2 G_a = -c2V_a(1 + ε𝒲_∅) + c2𝒲_a - c2V_∅ ε𝒲_a`. -/
theorem block_cmp_a {V W : OE .two (Lam d L N)} (hVe : ε ((V : SA .two (Lam d L N)).e) = 0)
    (hVa : ε ((V : SA .two (Lam d L N)).a) = 0) :
    epsR (bulk (oexp (-V) * (1 + W))) = 1 + ε ((W : SA .two (Lam d L N)).e) ∧
      epsR (aCmp (oexp (-V) * (1 + W))) = ε ((W : SA .two (Lam d L N)).a) ∧
      c2E (aCmp (oexp (-V) * (1 + W))) =
        -Suscept.c2 ((V : SA .two (Lam d L N)).a) * (1 + ε ((W : SA .two (Lam d L N)).e)) +
          Suscept.c2 ((W : SA .two (Lam d L N)).a) -
          Suscept.c2 ((V : SA .two (Lam d L N)).e) * ε ((W : SA .two (Lam d L N)).a) := by
  obtain ⟨h1, h2, -⟩ := oexp_neg_cmp hVe
  obtain ⟨g1, g2⟩ := eps_c2_gexp_neg (V := bulk V) hVe
  have eg : epsR (gexp (-bulk V)) = 1 := g1
  have cg : c2E (gexp (-bulk V)) = -Suscept.c2 ((V : SA .two (Lam d L N)).e) := g2
  have hW1a : aCmp (1 + W) = aCmp W := by
    refine Subtype.ext ?_; show (0 : Grassmann.N (Lam d L N)) + _ = _; rw [zero_add]; rfl
  have hG : aCmp (oexp (-V) * (1 + W)) =
      gexp (-bulk V) * aCmp W + -(gexp (-bulk V) * aCmp V) * bulk (1 + W) := by
    rw [aCmp_mul, h1, h2, hW1a]
  have eaV : epsR (aCmp V) = 0 := hVa
  have eaW : epsR (aCmp W) = ε ((W : SA .two (Lam d L N)).a) := rfl
  have caV : c2E (aCmp V) = Suscept.c2 ((V : SA .two (Lam d L N)).a) := rfl
  have caW : c2E (aCmp W) = Suscept.c2 ((W : SA .two (Lam d L N)).a) := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [map_mul, map_mul, h1, eg, one_mul]; exact eps_bulk_one_add W
  · rw [hG]
    simp only [map_add, map_mul, map_neg, eg, eaV, eaW]
    ring
  · rw [hG]
    simp only [c2E_add, c2E_mul, c2E_neg, map_mul, map_neg, eg, cg, eaV, eaW, caV, caW,
      eps_bulk_one_add, c2E_bulk_one_add]
    ring

/-- **One block factor, `σ_aσ_b` component** (no one-point parts): with `εV_∅ = εV_{ab} = 0`,
`ε G_{ab} = ε𝒲_{ab}`, `c2 G_{ab} = -c2V_{ab}(1 + ε𝒲_∅) + c2𝒲_{ab} - c2V_∅ ε𝒲_{ab}`. -/
theorem block_cmp_ab {V W : OE .two (Lam d L N)}
    (hV : V ∈ (abSub : Subalgebra ℂ (OE .two (Lam d L N))))
    (hW : W ∈ (abSub : Subalgebra ℂ (OE .two (Lam d L N))))
    (hVe : ε ((V : SA .two (Lam d L N)).e) = 0) (hVab : ε ((V : SA .two (Lam d L N)).ab) = 0) :
    epsR (abE (oexp (-V) * (1 + W))) = ε ((W : SA .two (Lam d L N)).ab) ∧
      c2E (abE (oexp (-V) * (1 + W))) =
        -Suscept.c2 ((V : SA .two (Lam d L N)).ab) * (1 + ε ((W : SA .two (Lam d L N)).e)) +
          Suscept.c2 ((W : SA .two (Lam d L N)).ab) -
          Suscept.c2 ((V : SA .two (Lam d L N)).e) * ε ((W : SA .two (Lam d L N)).ab) := by
  obtain ⟨h1, -, h3⟩ := oexp_neg_cmp hVe
  have h3 := h3 hV
  obtain ⟨g1, g2⟩ := eps_c2_gexp_neg (V := bulk V) hVe
  have eg : epsR (gexp (-bulk V)) = 1 := g1
  have cg : c2E (gexp (-bulk V)) = -Suscept.c2 ((V : SA .two (Lam d L N)).e) := g2
  have hmem : oexp (-V) ∈ (abSub : Subalgebra ℂ (OE .two (Lam d L N))) :=
    oexp_mem (neg_mem hV)
  have hW1 : (1 + W) ∈ (abSub : Subalgebra ℂ (OE .two (Lam d L N))) := add_mem (one_mem _) hW
  have hW1a : abE (1 + W) = abE W := by
    refine Subtype.ext ?_; show (0 : Grassmann.N (Lam d L N)) + _ = _; rw [zero_add]; rfl
  have hG : abE (oexp (-V) * (1 + W)) =
      gexp (-bulk V) * abE W + -(gexp (-bulk V) * abE V) * bulk (1 + W) := by
    rw [abE_mul_ab hmem hW1, h1, h3, hW1a]
  have eaV : epsR (abE V) = 0 := hVab
  have eaW : epsR (abE W) = ε ((W : SA .two (Lam d L N)).ab) := rfl
  have caV : c2E (abE V) = Suscept.c2 ((V : SA .two (Lam d L N)).ab) := rfl
  have caW : c2E (abE W) = Suscept.c2 ((W : SA .two (Lam d L N)).ab) := rfl
  refine ⟨?_, ?_⟩
  · rw [hG]
    simp only [map_add, map_mul, map_neg, eg, eaV, eaW]
    ring
  · rw [hG]
    simp only [c2E_add, c2E_mul, c2E_neg, map_mul, map_neg, eg, cg, eaV, eaW, caV, caW,
      eps_bulk_one_add, c2E_bulk_one_add]
    ring

theorem c2_zeroG : Suscept.c2 (0 : Grassmann.N (Lam d L N)) = 0 := by
  simpa using Suscept.c2_algebraMap (Λ := Lam d L N) 0

theorem c2E_zero : c2E (0 : EvR (Lam d L N)) = 0 := by
  have h := c2E_add (0 : EvR (Lam d L N)) 0
  rw [add_zero] at h
  linear_combination -h

theorem c2E_sum {ι : Type*} (S : Finset ι) (x : ι → EvR (Lam d L N)) :
    c2E (∑ i ∈ S, x i) = ∑ i ∈ S, c2E (x i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [c2E_zero]
  | insert a S ha ih => rw [sum_insert ha, sum_insert ha, c2E_add, ih]

theorem aCmp_add (F G : OE .two (Lam d L N)) : aCmp (F + G) = aCmp F + aCmp G := rfl

theorem eps_prodR {ι : Type*} (S : Finset ι) (x : ι → EvR (Lam d L N)) :
    epsR (∏ i ∈ S, x i) = ∏ i ∈ S, epsR (x i) := map_prod _ _ _

/-! ### A product of block factors plus an activity -/

section Fin

variable {ι : Type*} [DecidableEq ι] (S : Finset ι) (V W : ι → OE .two (Lam d L N))
  (K : OE .two (Lam d L N))

/-- `F = ∏_{i∈S}e^{-V_i}(1 + 𝒲_i) + K`. -/
def blkF : OE .two (Lam d L N) := (∏ i ∈ S, oexp (-V i) * (1 + W i)) + K

/-- `P₀ = ∏_i(1 + ε𝒲_{i,∅})`. -/
def blkP0 : ℂ := ∏ i ∈ S, (1 + ε ((W i : SA .two (Lam d L N)).e))

/-- The activity part of `c2 F_a` (only `𝒲_a`, `K_a` enter). -/
def remCa : ℂ :=
  (∑ i ∈ S, ((Suscept.c2 ((W i : SA .two (Lam d L N)).a) -
      Suscept.c2 ((V i : SA .two (Lam d L N)).e) * ε ((W i : SA .two (Lam d L N)).a)) *
        ∏ k ∈ S.erase i, (1 + ε ((W k : SA .two (Lam d L N)).e)) +
      ε ((W i : SA .two (Lam d L N)).a) *
        c2E (∏ k ∈ S.erase i, bulk (oexp (-V k) * (1 + W k))))) +
    Suscept.c2 ((K : SA .two (Lam d L N)).a)

/-- The activity part of `c2 F_{ab}` (only `𝒲_{ab}`, `K_{ab}` enter). -/
def remCab : ℂ :=
  (∑ i ∈ S, ((Suscept.c2 ((W i : SA .two (Lam d L N)).ab) -
      Suscept.c2 ((V i : SA .two (Lam d L N)).e) * ε ((W i : SA .two (Lam d L N)).ab)) *
        ∏ k ∈ S.erase i, (1 + ε ((W k : SA .two (Lam d L N)).e)) +
      ε ((W i : SA .two (Lam d L N)).ab) *
        c2E (∏ k ∈ S.erase i, bulk (oexp (-V k) * (1 + W k))))) +
    Suscept.c2 ((K : SA .two (Lam d L N)).ab)

variable {S V W K}

/-- **The `σ_a` component of `∏_ie^{-V_i}(1 + 𝒲_i) + K`** (Case 2, `εV_{i,∅} = εV_{i,a} = 0`):
`c2F_a = (∑_i -c2V_{i,a})·P₀ + remCa`, `εF_a = ∑_iε𝒲_{i,a}∏_{k≠i}(1 + ε𝒲_{k,∅}) + εK_a`. -/
theorem blkF_a (hVe : ∀ i ∈ S, ε ((V i : SA .two (Lam d L N)).e) = 0)
    (hVa : ∀ i ∈ S, ε ((V i : SA .two (Lam d L N)).a) = 0) :
    Suscept.c2 ((blkF S V W K : SA .two (Lam d L N)).a) =
        (∑ i ∈ S, -Suscept.c2 ((V i : SA .two (Lam d L N)).a)) * blkP0 S W + remCa S V W K ∧
      ε ((blkF S V W K : SA .two (Lam d L N)).a) =
        (∑ i ∈ S, ε ((W i : SA .two (Lam d L N)).a) *
          ∏ k ∈ S.erase i, (1 + ε ((W k : SA .two (Lam d L N)).e))) +
          ε ((K : SA .two (Lam d L N)).a) := by
  have hF : aCmp (blkF S V W K) = (∑ i ∈ S, aCmp (oexp (-V i) * (1 + W i)) *
      ∏ k ∈ S.erase i, bulk (oexp (-V k) * (1 + W k))) + aCmp K := by
    rw [blkF, aCmp_add, aCmp_prod]
  have hQ : ∀ i ∈ S, epsR (∏ k ∈ S.erase i, bulk (oexp (-V k) * (1 + W k))) =
      ∏ k ∈ S.erase i, (1 + ε ((W k : SA .two (Lam d L N)).e)) := fun i _ => by
    rw [eps_prodR]
    exact prod_congr rfl fun k hk =>
      (block_cmp_a (W := W k) (hVe k (mem_of_mem_erase hk)) (hVa k (mem_of_mem_erase hk))).1
  refine ⟨?_, ?_⟩
  · show c2E (aCmp (blkF S V W K)) = _
    rw [hF, c2E_add, c2E_sum, remCa, ← add_assoc]
    congr 1
    rw [sum_mul, ← sum_add_distrib]
    refine sum_congr rfl fun i hi => ?_
    obtain ⟨-, e2, e3⟩ := block_cmp_a (W := W i) (hVe i hi) (hVa i hi)
    rw [c2E_mul, e2, e3, hQ i hi, blkP0, ← mul_prod_erase S _ hi]
    ring
  · show epsR (aCmp (blkF S V W K)) = _
    rw [hF, map_add, map_sum]
    congr 1
    refine sum_congr rfl fun i hi => ?_
    rw [map_mul, (block_cmp_a (W := W i) (hVe i hi) (hVa i hi)).2.1, hQ i hi]

/-- **The `σ_aσ_b` component of `∏_ie^{-V_i}(1 + 𝒲_i) + K` without one-point parts**
(`εV_{i,∅} = εV_{i,ab} = 0`): `c2F_{ab} = (∑_i -c2V_{i,ab})·P₀ + remCab`,
`εF_{ab} = ∑_iε𝒲_{i,ab}∏_{k≠i}(1 + ε𝒲_{k,∅}) + εK_{ab}`. -/
theorem blkF_ab (hV : ∀ i ∈ S, V i ∈ (abSub : Subalgebra ℂ (OE .two (Lam d L N))))
    (hW : ∀ i ∈ S, W i ∈ (abSub : Subalgebra ℂ (OE .two (Lam d L N))))
    (hVe : ∀ i ∈ S, ε ((V i : SA .two (Lam d L N)).e) = 0)
    (hVab : ∀ i ∈ S, ε ((V i : SA .two (Lam d L N)).ab) = 0) :
    Suscept.c2 ((blkF S V W K : SA .two (Lam d L N)).ab) =
        (∑ i ∈ S, -Suscept.c2 ((V i : SA .two (Lam d L N)).ab)) * blkP0 S W + remCab S V W K ∧
      ε ((blkF S V W K : SA .two (Lam d L N)).ab) =
        (∑ i ∈ S, ε ((W i : SA .two (Lam d L N)).ab) *
          ∏ k ∈ S.erase i, (1 + ε ((W k : SA .two (Lam d L N)).e))) +
          ε ((K : SA .two (Lam d L N)).ab) := by
  have hG : ∀ i ∈ S, oexp (-V i) * (1 + W i) ∈ (abSub : Subalgebra ℂ (OE .two (Lam d L N))) :=
    fun i hi => mul_mem (oexp_mem (neg_mem (hV i hi))) (add_mem (one_mem _) (hW i hi))
  have hF : abE (blkF S V W K) = (∑ i ∈ S, abE (oexp (-V i) * (1 + W i)) *
      ∏ k ∈ S.erase i, bulk (oexp (-V k) * (1 + W k))) + abE K := by
    rw [blkF, show abE ((∏ i ∈ S, oexp (-V i) * (1 + W i)) + K) =
      abE (∏ i ∈ S, oexp (-V i) * (1 + W i)) + abE K from rfl, abE_prod S _ hG]
  have hQ : ∀ i ∈ S, epsR (∏ k ∈ S.erase i, bulk (oexp (-V k) * (1 + W k))) =
      ∏ k ∈ S.erase i, (1 + ε ((W k : SA .two (Lam d L N)).e)) := fun i _ => by
    rw [eps_prodR]
    refine prod_congr rfl fun k hk => ?_
    obtain ⟨h1, -⟩ := oexp_neg_cmp (hVe k (mem_of_mem_erase hk))
    obtain ⟨g1, -⟩ := eps_c2_gexp_neg (V := bulk (V k)) (hVe k (mem_of_mem_erase hk))
    rw [map_mul, map_mul, h1, show epsR (gexp (-bulk (V k))) = 1 from g1, one_mul]
    exact eps_bulk_one_add (W k)
  refine ⟨?_, ?_⟩
  · show c2E (abE (blkF S V W K)) = _
    rw [hF, c2E_add, c2E_sum, remCab, ← add_assoc]
    congr 1
    rw [sum_mul, ← sum_add_distrib]
    refine sum_congr rfl fun i hi => ?_
    obtain ⟨e2, e3⟩ := block_cmp_ab (hV i hi) (hW i hi) (hVe i hi) (hVab i hi)
    rw [c2E_mul, e2, e3, hQ i hi, blkP0, ← mul_prod_erase S _ hi]
    ring
  · show epsR (abE (blkF S V W K)) = _
    rw [hF, map_add, map_sum]
    congr 1
    refine sum_congr rfl fun i hi => ?_
    rw [map_mul, (block_cmp_ab (hV i hi) (hW i hi) (hVe i hi) (hVab i hi)).1, hQ i hi]

end Fin

end Restr

/-! ### The final object at the last scale -/

section Last

open Step2 Step2.LastN

theorem Knext2O_empty {c : Obs.Case} {d L N : ℕ} [NeZero L] (P : ObsPts d L N) (j : ℕ)
    (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V W : OFam c d L N) (K : OAct c d L N) :
    Knext2O P j C V W K ∅ = 1 := by
  rw [Knext2O, gKnextO, Gset_empty, sum_singleton]
  simp only [uXB, uXO, blocks, image_empty, sum_empty, Xcal, biUnion_empty, union_empty,
    empty_sdiff, bpowO, prod_empty, gKchkO, comp_empty, mul_one, ECCO_one, expU,
    Complex.exp_zero, one_smul, oexp_zero]

variable {L N : ℕ} [NeZero L] (R : RGPar 2 L N) (P : ObsPts 2 L N) (j : ℕ) (st : RawSt 2 L N)
  (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N) (o : ObsSt .two L N)

/-- **`F_N = ∏_BĨ_N(B) + K_N(Λ)`** at the last scale (`j + 1 = N`). -/
theorem finO_last (hj : j + 1 = N) :
    finO R P j st g μ D K o =
      blkF (blocks j (univ : Finset (Lam 2 L N)))
        (VpO P j (stCovN R j st) (fullV R j st g μ o) (fullW st D o) (fullK R j st K o))
        (WpO P j (stCovN R j st) (fullV R j st g μ o) (fullW st D o))
        (Knext2O P j (stCovN R j st) (fullV R j st g μ o) (fullW st D o) (fullK R j st K o)
          univ) := by
  unfold finO blkF
  subst hj
  have hne : (∅ : Finset (Lam 2 L (j + 1))) ≠ univ := fun h =>
    (univ_nonempty (α := Lam 2 L (j + 1))).ne_empty h.symm
  rw [Suscept.Pj_top, sum_pair hne, Knext2O_empty, sdiff_empty, sdiff_self, mul_one]
  simp only [bpowO, blocks, bot_eq_empty, image_empty, prod_empty, one_mul, GpO]

/-- **PR6, exact: the `σ_a` component of `F_N`** (any observable state, `j + 1 = N`): with
`β_N = ∑_B m₂(V_N(B)_a)` and `P₀ = ∏_B(1 + ε𝒲_N(B)_∅)`, `c2(F_N)_a = β_NP₀ + remCa` and
`ε(F_N)_a = ∑_Bε𝒲_N(B)_a∏_{B'≠B}(1 + ε𝒲_N(B')_∅) + εK_N(Λ)_a`. -/
theorem finO_last_a (hj : j + 1 = N) :
    let C := stCovN R j st
    let V := VpO P j C (fullV R j st g μ o) (fullW st D o) (fullK R j st K o)
    let W := WpO P j C (fullV R j st g μ o) (fullW st D o)
    let KN := Knext2O P j C (fullV R j st g μ o) (fullW st D o) (fullK R j st K o) univ
    let S := blocks j (univ : Finset (Lam 2 L N))
    Suscept.c2 ((finO R P j st g μ D K o : SA .two (Lam 2 L N)).a) =
        (∑ B ∈ S, mass2 ((V B : SA .two (Lam 2 L N)).a)) * blkP0 S W + remCa S V W KN ∧
      ε ((finO R P j st g μ D K o : SA .two (Lam 2 L N)).a) =
        (∑ B ∈ S, ε ((W B : SA .two (Lam 2 L N)).a) *
          ∏ B' ∈ S.erase B, (1 + ε ((W B' : SA .two (Lam 2 L N)).e))) +
          ε ((KN : SA .two (Lam 2 L N)).a) := by
  intro C V W KN S
  rw [finO_last R P j st g μ D K o hj]
  have hVe : ∀ B ∈ S, ε ((V B : SA .two (Lam 2 L N)).e) = 0 := fun B _ => by
    show ε ((bulk (V B) : EvR (Lam 2 L N)) : Grassmann.N (Lam 2 L N)) = 0
    rw [bulk_VpO, Step2.ε_Vp]
  have h := blkF_a (S := S) (V := V) (W := W) (K := KN) hVe fun B _ => eps_VpO_a P j C _ _ _ B
  simp only [Obs.mass2_eq_neg_c2]
  exact h

/-- **PR6, exact: the `σ_aσ_b` component of `F_N` without one-point parts** (`j + 1 = N`, the
inputs of the last step in `abSub`, e.g. the reduced history): with `r'_N = ∑_Bm₂(V_N(B)_{ab})`,
`c2(F_N)_{ab} = r'_NP₀ + remCab` and `ε(F_N)_{ab} = ∑_Bε𝒲_N(B)_{ab}∏_{B'≠B}(…) + εK_N(Λ)_{ab}`. -/
theorem finO_last_ab (hj : j + 1 = N)
    (H : OAbS j (fullV R j st g μ o) (fullW st D o) (fullK R j st K o)) :
    let C := stCovN R j st
    let V := VpO P j C (fullV R j st g μ o) (fullW st D o) (fullK R j st K o)
    let W := WpO P j C (fullV R j st g μ o) (fullW st D o)
    let KN := Knext2O P j C (fullV R j st g μ o) (fullW st D o) (fullK R j st K o) univ
    let S := blocks j (univ : Finset (Lam 2 L N))
    Suscept.c2 ((finO R P j st g μ D K o : SA .two (Lam 2 L N)).ab) =
        (∑ B ∈ S, mass2 ((V B : SA .two (Lam 2 L N)).ab)) * blkP0 S W + remCab S V W KN ∧
      ε ((finO R P j st g μ D K o : SA .two (Lam 2 L N)).ab) =
        (∑ B ∈ S, ε ((W B : SA .two (Lam 2 L N)).ab) *
          ∏ B' ∈ S.erase B, (1 + ε ((W B' : SA .two (Lam 2 L N)).e))) +
          ε ((KN : SA .two (Lam 2 L N)).ab) := by
  intro C V W KN S
  rw [finO_last R P j st g μ D K o hj]
  have hVe : ∀ B ∈ S, ε ((V B : SA .two (Lam 2 L N)).e) = 0 := fun B _ => by
    show ε ((bulk (V B) : EvR (Lam 2 L N)) : Grassmann.N (Lam 2 L N)) = 0
    rw [bulk_VpO, Step2.ε_Vp]
  have h := blkF_ab (S := S) (V := V) (W := W) (K := KN) (fun B _ => H.Vp_ab B)
    (fun B _ => H.Wp_ab B) hVe fun B _ => eps_VpO_ab P j C _ _ _ B
  simp only [Obs.mass2_eq_neg_c2]
  exact h

/-- **Without `σ_aσ_b` activity at the last scale the zero-mode identity is exact**: if
`𝒲_N(B)_{ab} = 0` and `K_N(Λ)_{ab} = 0`, then `c2(F_N)_{ab} = r'_NP₀` and `ε(F_N)_{ab} = 0`. -/
theorem finO_last_ab_noAct (hj : j + 1 = N)
    (H : OAbS j (fullV R j st g μ o) (fullW st D o) (fullK R j st K o))
    (hW0 : ∀ B, ((WpO P j (stCovN R j st) (fullV R j st g μ o) (fullW st D o) B :
      OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).ab = 0)
    (hK0 : ((Knext2O P j (stCovN R j st) (fullV R j st g μ o) (fullW st D o) (fullK R j st K o)
      univ : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).ab = 0) :
    Suscept.c2 ((finO R P j st g μ D K o : SA .two (Lam 2 L N)).ab) =
        (∑ B ∈ blocks j (univ : Finset (Lam 2 L N)),
          mass2 ((VpO P j (stCovN R j st) (fullV R j st g μ o) (fullW st D o) (fullK R j st K o) B :
            OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).ab) *
          blkP0 (blocks j (univ : Finset (Lam 2 L N)))
            (WpO P j (stCovN R j st) (fullV R j st g μ o) (fullW st D o)) ∧
      ε ((finO R P j st g μ D K o : SA .two (Lam 2 L N)).ab) = 0 := by
  obtain ⟨h1, h2⟩ := finO_last_ab R P j st g μ D K o hj H
  refine ⟨?_, ?_⟩
  · rw [h1, remCab]
    simp only [hW0, hK0, c2_zeroG, map_zero, sub_zero, zero_mul, add_zero,
      sum_const_zero, mul_zero]
  · rw [h2]; simp [hW0, hK0]

end Last

end

end PtCorr2
