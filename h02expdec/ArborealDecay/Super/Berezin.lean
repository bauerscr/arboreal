module

public import ArborealDecay.Super.Grassmann

/-!
# Paired odd generators and the Berezin integral

The superspace `ℝ^{2N|2N}` of BCHS Theorem 2.8 has, for every `i : N`, a pair of odd generators
`ξ_i, η_i`.  We allow further *parameter* generators indexed by `P` (in the application to
dimensional reduction these are the `ξ¹, η¹` generators, which are spectators).  So the odd
generators are indexed by `(N ⊕ N) ⊕ P`: `ξ_i = θ_{inl (inl i)}`, `η_i = θ_{inl (inr i)}`.

* `bpair i = ∂_{η_i} ∂_{ξ_i}` (first `∂_{ξ_i}`, then `∂_{η_i}`), the Berezin integral in the
  pair `i`, as in `∫ dx dy ∂_η ∂_ξ` of BCHS (Thm 2.8).
* `berezinL l` composes the `bpair i`, `i ∈ l`; `berezin` uses all of `N`.  It is a linear map
  `SG N P → SG N P` whose values are forms in the parameter generators only.
* `piPair i` kills `ξ_i, η_i`; `pi0` kills all `ξ_i, η_i` (the degree-zero part in the
  integrated generators).
* `aa i = ξ_i η_i`, `wpair γ i = 1 + γ ξ_i η_i`, `WL γ l = ∏_{i ∈ l} (1 + γ ξ_i η_i)`
  (`= e^{γ ∑ ξ_i η_i}`), `ωL l = ∑_{i ∈ l} ξ_i η_i`.
* `TL s t l = ∏_{i ∈ l} (s ∂_{η_i}∂_{ξ_i} + t π_i)`.

Main facts: `berezinL_mul_WL` (`∫ H e^{γω} = ∏ (∂_{η_i}∂_{ξ_i} + γ π_i) H`),
`berezinL_dξ`/`berezinL_dη` (Berezin integrals of fermionic derivatives vanish),
`TL_zero_one` (`∏ π_i = pi0`), and the derivatives of `WL` in the generators.
-/

@[expose] public section

namespace ArborealDecay.Super

noncomputable section

open CliffordAlgebra Grassmann

set_option linter.unusedSectionVars false

variable {N P : Type*} [DecidableEq N] [DecidableEq P]

/-- The Grassmann algebra with pairs `(ξ_i, η_i)_{i : N}` and parameter generators `P`. -/
abbrev SG (N P : Type*) := Gr ((N ⊕ N) ⊕ P)

/-- The generator `ξ_i`. -/
def ξ (i : N) : SG N P := gen (.inl (.inl i))

/-- The generator `η_i`. -/
def η (i : N) : SG N P := gen (.inl (.inr i))

/-- `∂_{ξ_i}`. -/
def dξ (i : N) : SG N P →ₗ[ℝ] SG N P := dgen (.inl (.inl i))

/-- `∂_{η_i}`. -/
def dη (i : N) : SG N P →ₗ[ℝ] SG N P := dgen (.inl (.inr i))

/-- The generators of the pair `i`. -/
def pairSet (i : N) : Set ((N ⊕ N) ⊕ P) := {.inl (.inl i), .inl (.inr i)}

/-- `π_i`: kill `ξ_i` and `η_i`. -/
def piPair (i : N) : SG N P →ₐ[ℝ] SG N P := killA (pairSet i)

/-- The degree-zero part in the generators `ξ, η` (parameters are kept). -/
def pi0 : SG N P →ₐ[ℝ] SG N P := killA (Set.range Sum.inl)

/-- `∂_{η_i} ∂_{ξ_i}`. -/
def bpair (i : N) : SG N P →ₗ[ℝ] SG N P := dη i ∘ₗ dξ i

/-- `ξ_i η_i`. -/
def aa (i : N) : SG N P := ξ i * η i

/-- `1 + γ ξ_i η_i = e^{γ ξ_i η_i}`. -/
def wpair (γ : ℝ) (i : N) : SG N P := 1 + γ • aa i

/-- `∏_{i ∈ l} ∂_{η_i} ∂_{ξ_i}` (the head of `l` is applied last). -/
def berezinL (l : List N) : SG N P →ₗ[ℝ] SG N P :=
  l.foldr (fun i L => bpair i ∘ₗ L) LinearMap.id

/-- `∏_{i ∈ l} (s ∂_{η_i} ∂_{ξ_i} + t π_i)`. -/
def TL (s t : ℝ) (l : List N) : SG N P →ₗ[ℝ] SG N P :=
  l.foldr (fun i L => (s • bpair i + t • (piPair i).toLinearMap) ∘ₗ L) LinearMap.id

/-- `∏_{i ∈ l} (1 + γ ξ_i η_i)`. -/
def WL (γ : ℝ) (l : List N) : SG N P := (l.map (wpair γ)).prod

/-- `∑_{i ∈ l} ξ_i η_i`. -/
def ωL (l : List N) : SG N P := (l.map aa).sum

theorem TL_cons (s t : ℝ) (i : N) (l : List N) (x : SG N P) :
    TL s t (i :: l) x = s • bpair i (TL s t l x) + t • piPair i (TL s t l x) := rfl

theorem berezinL_cons (i : N) (l : List N) (x : SG N P) :
    berezinL (i :: l) x = bpair i (berezinL l x) := rfl

/-! ### Generators -/

@[simp] theorem inv'_ξ (i : N) : inv' (ξ i : SG N P) = -ξ i := inv'_gen _
@[simp] theorem inv'_η (i : N) : inv' (η i : SG N P) = -η i := inv'_gen _

theorem dξ_ξ (i j : N) : dξ i (ξ j : SG N P) = if i = j then 1 else 0 := by
  simp [dξ, ξ, dgen_gen]

theorem dξ_η (i j : N) : dξ i (η j : SG N P) = 0 := by simp [dξ, η, dgen_gen]
theorem dη_ξ (i j : N) : dη i (ξ j : SG N P) = 0 := by simp [dη, ξ, dgen_gen]

theorem dη_η (i j : N) : dη i (η j : SG N P) = if i = j then 1 else 0 := by
  simp [dη, η, dgen_gen]

@[simp] theorem dξ_ξ_self (i : N) : dξ i (ξ i : SG N P) = 1 := by simp [dξ_ξ]
@[simp] theorem dη_η_self (i : N) : dη i (η i : SG N P) = 1 := by simp [dη_η]

theorem dξ_mul (i : N) (a b : SG N P) : dξ i (a * b) = dξ i a * b + inv' a * dξ i b :=
  dgen_mul _ a b

theorem dη_mul (i : N) (a b : SG N P) : dη i (a * b) = dη i a * b + inv' a * dη i b :=
  dgen_mul _ a b

@[simp] theorem dξ_one (i : N) : dξ i (1 : SG N P) = 0 := dgen_one _
@[simp] theorem dη_one (i : N) : dη i (1 : SG N P) = 0 := dgen_one _

theorem ξ_mul_ξ (i : N) : ξ i * ξ i = (0 : SG N P) := gen_mul_gen_self _
theorem η_mul_η (i : N) : η i * η i = (0 : SG N P) := gen_mul_gen_self _

@[simp] theorem inv'_aa (i : N) : inv' (aa i : SG N P) = aa i := by simp [aa]

theorem aa_mul_aa (i : N) : aa i * aa i = (0 : SG N P) := by
  have h : (η i : SG N P) * ξ i = -(ξ i * η i) := gen_anticomm _ _
  calc aa i * aa i = ξ i * (η i * ξ i) * (η i : SG N P) := by simp [aa, mul_assoc]
    _ = -(ξ i * ξ i * (η i * η i)) := by rw [h]; noncomm_ring
    _ = 0 := by rw [ξ_mul_ξ, zero_mul, neg_zero]

theorem aa_comm (i : N) (x : SG N P) : aa i * x = x * aa i := mul_comm_of_even' (inv'_aa i) x

theorem ξ_mul_aa (i : N) : ξ i * aa i = (0 : SG N P) := by
  rw [aa, ← mul_assoc, ξ_mul_ξ, zero_mul]

theorem η_mul_aa (i : N) : η i * aa i = (0 : SG N P) := by
  rw [aa, ← mul_assoc, η, ξ, gen_anticomm, neg_mul, mul_assoc, gen_mul_gen_self, mul_zero,
    neg_zero]

theorem dξ_aa (i : N) : dξ i (aa i : SG N P) = η i := by simp [aa, dξ_mul, dξ_η]

theorem dη_aa (i : N) : dη i (aa i : SG N P) = -ξ i := by simp [aa, dη_mul, dη_ξ]

theorem inv'_wpair (γ : ℝ) (i : N) : inv' (wpair γ i : SG N P) = wpair γ i := by simp [wpair]

theorem dξ_wpair (γ : ℝ) (i : N) : dξ i (wpair γ i : SG N P) = γ • η i := by
  simp [wpair, dξ_aa]

theorem dη_wpair (γ : ℝ) (i : N) : dη i (wpair γ i : SG N P) = -(γ • ξ i) := by
  simp [wpair, dη_aa]

theorem η_mul_wpair (γ : ℝ) (i : N) : η i * wpair γ i = (η i : SG N P) := by
  rw [wpair, mul_add, mul_one, mul_smul_comm, η_mul_aa, smul_zero, add_zero]

theorem ξ_mul_wpair (γ : ℝ) (i : N) : ξ i * wpair γ i = (ξ i : SG N P) := by
  rw [wpair, mul_add, mul_one, mul_smul_comm, ξ_mul_aa, smul_zero, add_zero]

/-! ### Elements free of a pair -/

/-- `c` does not involve `ξ_i, η_i`. -/
def PF (i : N) (c : SG N P) : Prop := dξ i c = 0 ∧ dη i c = 0 ∧ piPair i c = c

theorem PF.one (i : N) : PF i (1 : SG N P) := ⟨by simp, by simp, by simp⟩

theorem PF.mul {i : N} {a b : SG N P} (ha : PF i a) (hb : PF i b) : PF i (a * b) :=
  ⟨by rw [dξ_mul, ha.1, hb.1]; simp, by rw [dη_mul, ha.2.1, hb.2.1]; simp,
    by rw [map_mul, ha.2.2, hb.2.2]⟩

theorem PF.add {i : N} {a b : SG N P} (ha : PF i a) (hb : PF i b) : PF i (a + b) :=
  ⟨by rw [map_add, ha.1, hb.1, add_zero], by rw [map_add, ha.2.1, hb.2.1, add_zero],
    by rw [map_add, ha.2.2, hb.2.2]⟩

theorem PF.smul {i : N} {a : SG N P} (ha : PF i a) (c : ℝ) : PF i (c • a) :=
  ⟨by rw [map_smul, ha.1, smul_zero], by rw [map_smul, ha.2.1, smul_zero],
    by rw [map_smul, ha.2.2]⟩

theorem PF.gen {i : N} {o : (N ⊕ N) ⊕ P} (h : o ∉ pairSet i) : PF i (gen o : SG N P) := by
  refine ⟨dgen_gen_of_ne ?_, dgen_gen_of_ne ?_, killA_gen_of_notMem h⟩ <;>
    (rintro rfl; simp [pairSet] at h)

theorem PF.ξ {i j : N} (h : j ≠ i) : PF i (ξ j : SG N P) :=
  PF.gen (by simp [pairSet, h])

theorem PF.η {i j : N} (h : j ≠ i) : PF i (η j : SG N P) :=
  PF.gen (by simp [pairSet, h])

theorem PF.aa {i j : N} (h : j ≠ i) : PF i (aa j : SG N P) := (PF.ξ h).mul (PF.η h)

theorem PF.wpair {i j : N} (h : j ≠ i) (γ : ℝ) : PF i (wpair γ j : SG N P) :=
  (PF.one i).add ((PF.aa h).smul γ)

theorem PF.WL {i : N} {l : List N} (h : i ∉ l) (γ : ℝ) : PF i (WL γ l : SG N P) := by
  induction l with
  | nil => exact PF.one i
  | cons j l ih =>
    simp only [List.mem_cons, not_or] at h
    simp only [Super.WL, List.map_cons, List.prod_cons]
    exact (PF.wpair (Ne.symm h.1) γ).mul (ih h.2)

theorem bpair_mul_PF {i : N} {c : SG N P} (hc : PF i c) (H : SG N P) :
    bpair i (H * c) = bpair i H * c := by
  simp only [bpair, LinearMap.coe_comp, Function.comp_apply]
  rw [dξ_mul, hc.1, mul_zero, add_zero, dη_mul, hc.2.1, mul_zero, add_zero]

theorem piPair_mul_PF {i : N} {c : SG N P} (hc : PF i c) (H : SG N P) :
    piPair i (H * c) = piPair i H * c := by
  rw [map_mul, hc.2.2]

theorem TL_mul_PF {l : List N} {c : SG N P} (hc : ∀ i ∈ l, PF i c) (s t : ℝ) (H : SG N P) :
    TL s t l (H * c) = TL s t l H * c := by
  induction l generalizing H with
  | nil => rfl
  | cons j l ih =>
    rw [TL_cons, TL_cons, ih (fun i hi => hc i (List.mem_cons_of_mem _ hi)),
      bpair_mul_PF (hc j List.mem_cons_self), piPair_mul_PF (hc j List.mem_cons_self),
      add_mul, smul_mul_assoc, smul_mul_assoc]

/-! ### The basic one-pair identities -/

theorem ι_eq_kill_add (i : N) (v : (N ⊕ N) ⊕ P → ℝ) :
    ExteriorAlgebra.ι ℝ v = killA (pairSet i) (ExteriorAlgebra.ι ℝ v) +
      v (.inl (.inl i)) • (ξ i : SG N P) + v (.inl (.inr i)) • η i := by
  simp only [killA, ExteriorAlgebra.map_apply_ι, ξ, η, gen, ← map_smul, ← map_add]
  congr 1
  ext o
  simp only [Pi.add_apply, Pi.smul_apply, killV_apply, Set.indicator_apply, Set.mem_compl_iff,
    pairSet, Set.mem_insert_iff, Set.mem_singleton_iff, Pi.single_apply, smul_eq_mul]
  by_cases h1 : o = .inl (.inl i)
  · subst h1; simp
  · by_cases h2 : o = .inl (.inr i)
    · subst h2; simp
    · simp [h1, h2]

/-- Multiplication by `ξ_i η_i` only sees the part free of the pair `i`. -/
theorem mul_aa_eq (i : N) (H : SG N P) : H * aa i = piPair i H * aa i := by
  induction H using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι v =>
    conv_lhs => rw [ι_eq_kill_add i v]
    have h0 : ExteriorAlgebra.ι ℝ v = CliffordAlgebra.ι 0 v := rfl
    rw [← h0, add_mul, add_mul, smul_mul_assoc, smul_mul_assoc, ξ_mul_aa, η_mul_aa, smul_zero,
      smul_zero, add_zero, add_zero]
    rfl
  | mul a b ha hb =>
    calc a * b * aa i = a * (b * aa i) := mul_assoc _ _ _
      _ = a * (piPair i b * aa i) := by rw [hb]
      _ = a * aa i * piPair i b := by rw [← aa_comm, mul_assoc]
      _ = piPair i a * aa i * piPair i b := by rw [ha]
      _ = piPair i (a * b) * aa i := by rw [mul_assoc, aa_comm, ← mul_assoc, map_mul]
  | add a b ha hb => rw [add_mul, ha, hb, map_add, add_mul]

theorem PF.piPair (i : N) (H : SG N P) : PF i (piPair i H) :=
  ⟨dgen_killA (by simp [pairSet]) H, dgen_killA (by simp [pairSet]) H,
    by rw [Super.piPair, killA_killA, Set.union_self]⟩

theorem bpair_mul_aa_of_PF {i : N} {c : SG N P} (hc : PF i c) : bpair i (c * aa i) = c := by
  simp only [bpair, LinearMap.coe_comp, Function.comp_apply]
  rw [dξ_mul, hc.1, zero_mul, zero_add, dξ_aa, dη_mul, dη_η_self, mul_one, Grassmann.inv'_inv',
    dη, dgen_inv', ← dη, hc.2.1, map_zero, neg_zero, zero_mul, zero_add]

/-- `∂_{η_i}∂_{ξ_i} (H ξ_i η_i) = π_i H`. -/
theorem bpair_mul_aa (i : N) (H : SG N P) : bpair i (H * aa i) = piPair i H := by
  rw [mul_aa_eq, bpair_mul_aa_of_PF (PF.piPair i H)]

theorem bpair_mul_wpair (γ : ℝ) (i : N) (H : SG N P) :
    bpair i (H * wpair γ i) = bpair i H + γ • piPair i H := by
  rw [wpair, mul_add, mul_one, mul_smul_comm, map_add, map_smul, bpair_mul_aa]

/-! ### Products over lists -/

theorem WL_cons (γ : ℝ) (i : N) (l : List N) :
    (WL γ (i :: l) : SG N P) = wpair γ i * WL γ l := by simp [WL]

theorem ωL_cons (i : N) (l : List N) : (ωL (i :: l) : SG N P) = aa i + ωL l := by simp [ωL]

@[simp] theorem WL_nil (γ : ℝ) : (WL γ [] : SG N P) = 1 := rfl

@[simp] theorem WL_zero (l : List N) : (WL 0 l : SG N P) = 1 := by
  induction l with
  | nil => rfl
  | cons i l ih => rw [WL_cons, ih, wpair]; simp

theorem inv'_WL (γ : ℝ) (l : List N) : inv' (WL γ l : SG N P) = WL γ l := by
  induction l with
  | nil => simp
  | cons i l ih => rw [WL_cons, map_mul, inv'_wpair, ih]

theorem inv'_ωL (l : List N) : inv' (ωL l : SG N P) = ωL l := by
  induction l with
  | nil => simp [ωL]
  | cons i l ih => rw [ωL_cons, map_add, inv'_aa, ih]

/-- `∫ H e^{γ ω} = ∏ (∂_{η_i}∂_{ξ_i} + γ π_i) H`. -/
theorem berezinL_mul_WL (γ : ℝ) {l : List N} (hl : l.Nodup) (H : SG N P) :
    berezinL l (H * WL γ l) = TL 1 γ l H := by
  induction l generalizing H with
  | nil => simp [berezinL, TL]
  | cons i l ih =>
    rw [List.nodup_cons] at hl
    have hPF : ∀ j ∈ l, PF j (wpair γ i : SG N P) := fun j hj =>
      PF.wpair (by rintro rfl; exact hl.1 hj) γ
    rw [berezinL_cons, TL_cons, WL_cons, ← mul_assoc, ih hl.2, TL_mul_PF hPF, bpair_mul_wpair,
      one_smul]

/-- `∂_{ξ_j}` commutes with the even operator `∂_{η_i}∂_{ξ_i}`. -/
theorem bpair_dξ (i j : N) (x : SG N P) : bpair i (dξ j x) = dξ j (bpair i x) := by
  simp only [bpair, LinearMap.coe_comp, Function.comp_apply, dξ, dη]
  rw [dgen_comm (O := (N ⊕ N) ⊕ P) (Sum.inl (Sum.inl i)) (Sum.inl (Sum.inl j)) x, map_neg,
    dgen_comm (O := (N ⊕ N) ⊕ P) (Sum.inl (Sum.inr i)) (Sum.inl (Sum.inl j)), neg_neg]

theorem bpair_dη (i j : N) (x : SG N P) : bpair i (dη j x) = dη j (bpair i x) := by
  simp only [bpair, LinearMap.coe_comp, Function.comp_apply, dξ, dη]
  rw [dgen_comm (O := (N ⊕ N) ⊕ P) (Sum.inl (Sum.inl i)) (Sum.inl (Sum.inr j)) x, map_neg,
    dgen_comm (O := (N ⊕ N) ⊕ P) (Sum.inl (Sum.inr i)) (Sum.inl (Sum.inr j)), neg_neg]

theorem berezinL_dξ_comm (l : List N) (j : N) (x : SG N P) :
    berezinL l (dξ j x) = dξ j (berezinL l x) := by
  induction l with
  | nil => rfl
  | cons i l ih => rw [berezinL_cons, berezinL_cons, ih, bpair_dξ]

theorem berezinL_dη_comm (l : List N) (j : N) (x : SG N P) :
    berezinL l (dη j x) = dη j (berezinL l x) := by
  induction l with
  | nil => rfl
  | cons i l ih => rw [berezinL_cons, berezinL_cons, ih, bpair_dη]

/-- The Berezin integral of a `ξ_j`-derivative vanishes. -/
theorem berezinL_dξ {l : List N} {j : N} (hj : j ∈ l) (x : SG N P) :
    berezinL l (dξ j x) = 0 := by
  induction l with
  | nil => simp at hj
  | cons i l ih =>
    rw [berezinL_cons]
    by_cases hjl : j ∈ l
    · rw [ih hjl, map_zero]
    · have hij : j = i := by simpa [hjl] using hj
      subst hij
      rw [berezinL_dξ_comm]
      simp [bpair, dξ, dgen_dgen]

/-- The Berezin integral of an `η_j`-derivative vanishes. -/
theorem berezinL_dη {l : List N} {j : N} (hj : j ∈ l) (x : SG N P) :
    berezinL l (dη j x) = 0 := by
  induction l with
  | nil => simp at hj
  | cons i l ih =>
    rw [berezinL_cons]
    by_cases hjl : j ∈ l
    · rw [ih hjl, map_zero]
    · have hij : j = i := by simpa [hjl] using hj
      subst hij
      rw [berezinL_dη_comm]
      simp only [bpair, LinearMap.coe_comp, Function.comp_apply, dξ, dη]
      rw [dgen_comm (O := (N ⊕ N) ⊕ P) (Sum.inl (Sum.inl j)) (Sum.inl (Sum.inr j)), map_neg,
        dgen_dgen, neg_zero]

/-! ### Derivatives of `WL` in the generators -/

theorem dξ_WL (γ : ℝ) {l : List N} (hl : l.Nodup) {i : N} (hi : i ∈ l) :
    dξ i (WL γ l : SG N P) = γ • (η i * WL γ l) := by
  induction l with
  | nil => simp at hi
  | cons j l ih =>
    rw [List.nodup_cons] at hl
    rw [WL_cons, dξ_mul, inv'_wpair]
    by_cases hij : i = j
    · subst hij
      rw [(PF.WL hl.1 γ).1, mul_zero, add_zero, dξ_wpair, ← mul_assoc, η_mul_wpair,
        smul_mul_assoc]
    · have hil : i ∈ l := by simpa [hij] using hi
      rw [(PF.wpair (Ne.symm hij) γ).1, zero_mul, zero_add, ih hl.2 hil, mul_smul_comm,
        ← mul_assoc, ← mul_assoc, mul_comm_of_even' (inv'_wpair γ j)]

theorem dη_WL (γ : ℝ) {l : List N} (hl : l.Nodup) {i : N} (hi : i ∈ l) :
    dη i (WL γ l : SG N P) = -(γ • (ξ i * WL γ l)) := by
  induction l with
  | nil => simp at hi
  | cons j l ih =>
    rw [List.nodup_cons] at hl
    rw [WL_cons, dη_mul, inv'_wpair]
    by_cases hij : i = j
    · subst hij
      rw [(PF.WL hl.1 γ).2.1, mul_zero, add_zero, dη_wpair, ← mul_assoc, ξ_mul_wpair,
        neg_mul, smul_mul_assoc]
    · have hil : i ∈ l := by simpa [hij] using hi
      rw [(PF.wpair (Ne.symm hij) γ).2.1, zero_mul, zero_add, ih hl.2 hil, mul_neg,
        mul_smul_comm, ← mul_assoc, ← mul_assoc, mul_comm_of_even' (inv'_wpair γ j)]

/-! ### The operators `TL` -/

theorem TL_smul (c s t : ℝ) (l : List N) (x : SG N P) :
    TL (c * s) (c * t) l x = c ^ l.length • TL s t l x := by
  induction l with
  | nil => simp [TL]
  | cons i l ih =>
    rw [TL_cons, TL_cons, ih, map_smul, map_smul, List.length_cons]
    module

/-- The generators of the pairs in `l`. -/
def pairSetL (l : List N) : Set ((N ⊕ N) ⊕ P) := {o | ∃ i ∈ l, o ∈ pairSet i}

theorem TL_zero_one_eq (l : List N) (x : SG N P) : TL 0 1 l x = killA (pairSetL l) x := by
  induction l generalizing x with
  | nil =>
    have : pairSetL ([] : List N) = (∅ : Set ((N ⊕ N) ⊕ P)) := by simp [pairSetL]
    rw [this, killA_empty]; rfl
  | cons i l ih =>
    rw [TL_cons, ih, zero_smul, zero_add, one_smul]
    change killA (pairSet i) _ = _
    rw [killA_killA]
    have : pairSet i ∪ pairSetL l = (pairSetL (i :: l) : Set ((N ⊕ N) ⊕ P)) := by
      ext o; simp [pairSetL]
    rw [this]

theorem TL_zero_one [Fintype N] (x : SG N P) :
    TL 0 1 (Finset.univ : Finset N).toList x = pi0 x := by
  rw [TL_zero_one_eq, pi0]
  have : pairSetL (Finset.univ : Finset N).toList = (Set.range Sum.inl : Set ((N ⊕ N) ⊕ P)) := by
    ext o
    simp only [pairSetL, Finset.mem_toList, Finset.mem_univ, true_and, pairSet,
      Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
    constructor
    · rintro ⟨i, rfl | rfl⟩ <;> exact ⟨_, rfl⟩
    · rintro ⟨e, rfl⟩
      rcases e with i | i
      · exact ⟨i, Or.inl rfl⟩
      · exact ⟨i, Or.inr rfl⟩
  rw [this]

end

end ArborealDecay.Super

end
