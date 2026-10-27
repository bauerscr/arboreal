import Step2.Coup.Wick

/-!
# Coupling constants (`h02uv-outline.tex`, Section `sec:coupling-coords`)

For `κ = (z, y, ν, g)` the coupling polynomial is

  `V_κ(Y) = ∑_{x ∈ Y} [z (∇ψ∇ψ̄)_x + (y/2)((-Δψ)_x ψ̄_x + ψ_x (-Δψ̄)_x) + ν ψ_x ψ̄_x + g M̂_x]`

(`Vcoup`), a uniform polynomial (`unif`) with coefficients `coupC κ`, `coupE κ`.

`expLC_Vcoup` (Proposition `prop:C2`(i), Lemma `lem:first` in exact form): if
`C(x,x) = c₀` and `C(x+e,x) = C(x,x+e) = c₀ + δ` for all `x` and unit directions `e`, then
`𝔼_C θ V_κ(Y) = V_{κ'}(Y) + const` with `κ' = (z - g c₀, y - g δ, ν + 2d g δ, g)`. In particular
`z' + y' = z + y - g C(e₁, 0)` and `ν' = ν + g ΔC(0)`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Matrix

variable {d L N : ℕ} [NeZero L]

/-- Coupling constants `(z, y, ν, g)`. -/
structure Coup where
  z : ℂ
  y : ℂ
  nu : ℂ
  g : ℂ

/-- The quadratic coefficients of `V_κ`. -/
def coupC (κ : Coup) : Mono d → ℂ
  | .c => κ.nu
  | .a2 s => if s.IsDiag then -κ.y / 2 else 0
  | .b2 s => if s.IsDiag then -κ.y / 2 else 0
  | .m2 i k => if i = k then κ.z else 0
  | _ => 0

/-- The quartic coefficients of `V_κ`. -/
def coupE (κ : Coup) : Fin d → Fin d → ℂ := fun i k => if i = k then κ.g else 0

/-- The coupling polynomial `V_κ(Y)`. -/
def Vcoup (κ : Coup) (Y : Finset (Lam d L N)) : Alg d L N := unif 0 (coupC κ) (coupE κ) Y

/-- `κ' = (z - g c₀, y - g δ, ν + 2d g δ, g)`. -/
def Coup.shift (d : ℕ) (κ : Coup) (c₀ δ : ℂ) : Coup :=
  ⟨κ.z - κ.g * c₀, κ.y - κ.g * δ, κ.nu + 2 * d * κ.g * δ, κ.g⟩

/-! ### Explicit forms of the monomials -/

theorem psi_def (x : Lam d L N) : psi x = ψ ((x, 1) : Sf (Lam d L N)) := rfl
theorem psibar_def (x : Lam d L N) : psibar x = ψ ((x, -1) : Sf (Lam d L N)) := rfl

theorem monoAt_c (x : Lam d L N) : monoAt (Mono.c : Mono d) x = psi x * psibar x := by
  simp [monoAt, stencil, tens, id1, prj_zero]

theorem shift_lemmas (i : Fin d) (x : Lam d L N) :
    x + prj (ez i) = x + dirVec (Sum.inl i) ∧ x + prj (-ez i) = x + dirVec (Sum.inr i) ∧
      x + prj (0 : Zd d) = x :=
  ⟨by rw [Loc.prj_ez], by rw [Loc.prj_neg_ez], by rw [Loc.prj_zero, add_zero]⟩

theorem monoAt_a2 (i : Fin d) (x : Lam d L N) :
    monoAt (Mono.a2 s(i, i)) x =
      (psi (x + dirVec (Sum.inl i)) - psi x) * psibar x +
        (psi (x + dirVec (Sum.inr i)) - psi x) * psibar x := by
  obtain ⟨h1, h2, h3⟩ := shift_lemmas (L := L) (N := N) i x
  simp only [monoAt, stencil, Dsym_mk (le_refl i), Dik, if_true, tens, lap1, id1,
    List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.append_nil, List.sum_cons, List.sum_nil, h1, h2, h3]
  simp only [sub_mul]
  push_cast
  module

theorem monoAt_b2 (i : Fin d) (x : Lam d L N) :
    monoAt (Mono.b2 s(i, i)) x =
      psi x * (psibar (x + dirVec (Sum.inl i)) - psibar x) +
        psi x * (psibar (x + dirVec (Sum.inr i)) - psibar x) := by
  obtain ⟨h1, h2, h3⟩ := shift_lemmas (L := L) (N := N) i x
  simp only [monoAt, stencil, Dsym_mk (le_refl i), Dik, if_true, tens, lap1, id1,
    List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.append_nil, List.sum_cons, List.sum_nil, h1, h2, h3]
  simp only [mul_sub]
  push_cast
  module

theorem monoAt_m2 (i : Fin d) (x : Lam d L N) :
    monoAt (Mono.m2 i i) x = (1 / 2 : ℂ) •
      ((psi (x + dirVec (Sum.inl i)) - psi x) * (psibar (x + dirVec (Sum.inl i)) - psibar x) +
        (psi (x + dirVec (Sum.inr i)) - psi x) * (psibar (x + dirVec (Sum.inr i)) - psibar x)) := by
  obtain ⟨h1, h2, h3⟩ := shift_lemmas (L := L) (N := N) i x
  simp only [monoAt, stencil, if_true, sc, tens, fw, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_nil,
    List.sum_cons, List.sum_nil, h1, h2, h3]
  simp only [mul_sub, sub_mul, smul_add, smul_sub]
  push_cast
  module

/-! ### Sums over the monomial basis -/

theorem sum_mono {M : Type*} [AddCommMonoid M] (F : Mono d → M) :
    ∑ m, F m = F .c + ∑ i, F (.a1 i) + ∑ i, F (.b1 i) + ∑ s, F (.a2 s) + ∑ s, F (.b2 s) +
      ∑ i, ∑ k, F (.m2 i k) := by
  rw [← Fintype.sum_equiv Mono.equiv.symm _ F (fun _ => rfl)]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.univ_punit, sum_singleton]
  simp only [Mono.equiv, Equiv.coe_fn_symm_mk]
  abel

theorem sum_sym2_diag {M : Type*} [AddCommMonoid M] (f : Sym2 (Fin d) → M) :
    (∑ s, if s.IsDiag then f s else 0) = ∑ i, f s(i, i) := by
  classical
  rw [← sum_filter]
  have e : (univ.filter fun s : Sym2 (Fin d) => s.IsDiag) = univ.image Sym2.diag := by
    ext s
    induction s using Sym2.ind with
    | _ a b =>
      simp only [mem_filter, mem_univ, true_and, mem_image, Sym2.mk_isDiag_iff, Sym2.diag]
      constructor
      · rintro rfl; exact ⟨a, rfl⟩
      · rintro ⟨i, h⟩
        rw [Sym2.eq_iff] at h
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  rw [e, sum_image fun i _ k _ h => Sym2.diag_injective h]
  rfl

/-! ### The Wick computation -/

section Wick

variable {C : Matrix (Lam d L N) (Lam d L N) ℂ} {c₀ δ : ℂ}

theorem pairC_ev (C : Matrix (Lam d L N) (Lam d L N) ℂ) (p q : Lam d L N) :
    pairC C (ev ((p, 1) : Sf (Lam d L N))) (ev ((q, -1) : Sf (Lam d L N))) = C q p := by
  simp only [pairC, ev, Pi.single_apply, Prod.mk.injEq, and_true, mul_ite, mul_one, mul_zero]
  rw [sum_eq_single q (fun x _ hx => by simp [hx]) (by simp)]
  rw [sum_eq_single p (fun y _ hy => by simp [hy]) (by simp)]
  simp

theorem pairC_sub_left (C : Matrix (Lam d L N) (Lam d L N) ℂ) (u u' v : V (Lam d L N)) :
    pairC C (u - u') v = pairC C u v - pairC C u' v := by
  simp only [pairC, Pi.sub_apply, sub_mul, mul_sub, sum_sub_distrib]

theorem pairC_sub_right (C : Matrix (Lam d L N) (Lam d L N) ℂ) (u v v' : V (Lam d L N)) :
    pairC C u (v - v') = pairC C u v - pairC C u v' := by
  simp only [pairC, Pi.sub_apply, mul_sub, sum_sub_distrib]

theorem PM_ev (p q : Lam d L N) : PM (ev ((p, 1) : Sf (Lam d L N))) (ev ((q, -1) : Sf (Lam d L N))) :=
  ⟨fun x => by simp [ev, Pi.single_apply, units_ne.symm], fun x => by simp [ev, Pi.single_apply, units_ne]⟩

theorem PM_sub {u u' v v' : V (Lam d L N)} (h : PM u v) (h' : PM u' v') : PM (u - u') (v - v') :=
  ⟨fun x => by simp [h.hu, h'.hu], fun x => by simp [h.hv, h'.hv]⟩

theorem ι_ev (a : Sf (Lam d L N)) : ExteriorAlgebra.ι ℂ (ev a) = ψ a := rfl

/-- **`𝔼θ` of the diagonal quartic monomial.** -/
theorem expLC_gmono4 (hc₀ : ∀ x, C x x = c₀) (hδ : ∀ x e, C (x + dirVec e) x = c₀ + δ)
    (hδ' : ∀ x e, C x (x + dirVec e) = c₀ + δ) (e : Dir d) (x : Lam d L N) :
    ∃ r : ℂ, expLC C (gmono4 e e x) = gmono4 e e x +
      ((2 * δ) • (psi x * psibar x) + δ • ((psi (x + dirVec e) - psi x) * psibar x) +
        δ • (psi x * (psibar (x + dirVec e) - psibar x)) +
        (-c₀) • ((psi (x + dirVec e) - psi x) * (psibar (x + dirVec e) - psibar x))) + r • 1 := by
  set u₁ : V (Lam d L N) := ev ((x + dirVec e, 1) : Sf (Lam d L N)) - ev (x, 1)
  set v₁ : V (Lam d L N) := ev ((x + dirVec e, -1) : Sf (Lam d L N)) - ev (x, -1)
  set u₂ : V (Lam d L N) := ev ((x, 1) : Sf (Lam d L N))
  set v₂ : V (Lam d L N) := ev ((x, -1) : Sf (Lam d L N))
  have h₁ : PM u₁ v₁ := PM_sub (PM_ev _ _) (PM_ev _ _)
  have h₂ : PM u₂ v₂ := PM_ev _ _
  have hG : gmono4 e e x = ExteriorAlgebra.ι ℂ u₁ * (ExteriorAlgebra.ι ℂ v₁ *
      (ExteriorAlgebra.ι ℂ u₂ * ExteriorAlgebra.ι ℂ v₂)) := by
    rw [gmono4_eq]; simp only [u₁, v₁, u₂, v₂, map_sub, ι_ev]
  have p11 : pairC C u₁ v₁ = -(2 * δ) := by
    simp only [u₁, v₁, pairC_sub_left, pairC_sub_right, pairC_ev, hc₀, hδ, hδ']; ring
  have p21 : pairC C u₂ v₁ = δ := by
    simp only [u₂, v₁, pairC_sub_right, pairC_ev, hc₀, hδ]; ring
  have p12 : pairC C u₁ v₂ = δ := by
    simp only [u₁, v₂, pairC_sub_left, pairC_ev, hc₀, hδ']; ring
  have p22 : pairC C u₂ v₂ = c₀ := by simp only [u₂, v₂, pairC_ev, hc₀]
  refine ⟨pairC C u₁ v₁ * pairC C u₂ v₂ - pairC C u₁ v₂ * pairC C u₂ v₁, ?_⟩
  rw [hG, expLC_four C h₁ h₂, LopC_four C h₁ h₂, p11, p21, p12, p22]
  have hba : ExteriorAlgebra.ι ℂ v₁ * ExteriorAlgebra.ι ℂ u₂ =
      -(ExteriorAlgebra.ι ℂ u₂ * ExteriorAlgebra.ι ℂ v₁) := ι_anticomm v₁ u₂
  rw [hba]
  simp only [u₁, v₁, u₂, v₂, map_sub, ι_ev, ← psi_def, ← psibar_def]
  rw [neg_neg]
  module

/-- `𝔼θ` of the symmetric diagonal quartic monomial. -/
theorem expLC_mono4s (hc₀ : ∀ x, C x x = c₀) (hδ : ∀ x e, C (x + dirVec e) x = c₀ + δ)
    (hδ' : ∀ x e, C x (x + dirVec e) = c₀ + δ) (i : Fin d) (x : Lam d L N) :
    ∃ r : ℂ, expLC C (mono4s i i x) = mono4s i i x +
      ((2 * δ) • monoAt (Mono.c : Mono d) x +
        (δ / 2) • (monoAt (Mono.a2 s(i, i)) x + monoAt (Mono.b2 s(i, i)) x) +
        (-c₀) • monoAt (Mono.m2 i i) x) + r • 1 := by
  obtain ⟨r₁, h₁⟩ := expLC_gmono4 hc₀ hδ hδ' (Sum.inl i) x
  obtain ⟨r₂, h₂⟩ := expLC_gmono4 hc₀ hδ hδ' (Sum.inr i) x
  refine ⟨(1 / 2 : ℂ) * (r₁ + r₂), ?_⟩
  unfold mono4s
  rw [if_pos rfl, map_smul, map_add, h₁, h₂, monoAt_c, monoAt_a2, monoAt_b2, monoAt_m2]
  module

/-- `𝔼θ` of a quadratic monomial is the monomial plus a constant. -/
theorem expLC_monoAt (C : Matrix (Lam d L N) (Lam d L N) ℂ) (M : Mono d) (x : Lam d L N) :
    ∃ r : ℂ, expLC C (monoAt M x) = monoAt M x + r • 1 := by
  rw [monoAt]
  induction (stencil M) with
  | nil => exact ⟨0, by simp⟩
  | cons p l ih =>
    obtain ⟨r, hr⟩ := ih
    have h2 := expLC_two C (PM_ev (x + prj p.2.1) (x + prj p.2.2))
    simp only [ι_ev] at h2
    refine ⟨r + p.1 * -pairC C (ev ((x + prj p.2.1, 1) : Sf (Lam d L N)))
      (ev ((x + prj p.2.2, -1) : Sf (Lam d L N))), ?_⟩
    simp only [List.map_cons, List.sum_cons, map_add, hr, map_smul]
    rw [show psi (x + prj p.2.1) * psibar (x + prj p.2.2) =
      ψ ((x + prj p.2.1, 1) : Sf (Lam d L N)) * ψ ((x + prj p.2.2, -1) : Sf (Lam d L N)) from rfl,
      h2]
    module

theorem expLC_monoSet (C : Matrix (Lam d L N) (Lam d L N) ℂ) (M : Mono d)
    (Y : Finset (Lam d L N)) : ∃ r : ℂ, expLC C (monoSet M Y) = monoSet M Y + r • 1 := by
  rw [monoSet]
  induction Y using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a Y ha ih =>
    obtain ⟨r, hr⟩ := ih
    obtain ⟨r', hr'⟩ := expLC_monoAt C M a
    refine ⟨r' + r, ?_⟩
    rw [sum_insert ha, map_add, hr, hr']
    module

/-- **Proposition `prop:C2`(i)**: `𝔼θ V_κ(Y) = V_{κ'}(Y) + const`. -/
theorem expLC_Vcoup (hc₀ : ∀ x, C x x = c₀) (hδ : ∀ x e, C (x + dirVec e) x = c₀ + δ)
    (hδ' : ∀ x e, C x (x + dirVec e) = c₀ + δ) (κ : Coup) (Y : Finset (Lam d L N)) :
    ∃ r : ℂ, expLC C (Vcoup κ Y) = Vcoup (κ.shift d c₀ δ) Y + r • 1 := by
  classical
  -- the quartic part
  have h4 : ∀ i, ∃ r : ℂ, expLC C (mono4sSet i i Y) = mono4sSet i i Y +
      ((2 * δ) • monoSet (Mono.c : Mono d) Y +
        (δ / 2) • (monoSet (Mono.a2 s(i, i)) Y + monoSet (Mono.b2 s(i, i)) Y) +
        (-c₀) • monoSet (Mono.m2 i i) Y) + r • 1 := by
    intro i
    rw [mono4sSet, monoSet, monoSet, monoSet, monoSet]
    induction Y using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | insert a Y ha ih =>
      obtain ⟨r, hr⟩ := ih
      obtain ⟨r', hr'⟩ := expLC_mono4s hc₀ hδ hδ' i a
      refine ⟨r' + r, ?_⟩
      simp only [sum_insert ha, map_add, hr, hr']
      module
  -- the quadratic part
  have hq : ∃ r : ℂ, expLC C (∑ M, coupC κ M • monoSet M Y) =
      ∑ M, coupC κ M • monoSet M Y + r • 1 := by
    induction (univ : Finset (Mono d)) using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | insert M s hM ih =>
      obtain ⟨r, hr⟩ := ih
      obtain ⟨r', hr'⟩ := expLC_monoSet C M Y
      refine ⟨coupC κ M * r' + r, ?_⟩
      rw [sum_insert hM, map_add, map_smul, hr, hr']
      module
  choose r4 hr4 using h4
  obtain ⟨rq, hrq⟩ := hq
  refine ⟨rq + ∑ i, κ.g * r4 i, ?_⟩
  have hdiag : ∀ (κ : Coup) (G : Fin d → Fin d → Alg d L N),
      ∑ i, ∑ k, coupE κ i k • G i k = ∑ i, κ.g • G i i := by
    intro κ G
    refine sum_congr rfl fun i _ => ?_
    rw [sum_eq_single i (fun k _ hk => by simp [coupE, Ne.symm hk]) (by simp)]
    simp [coupE]
  simp only [Vcoup, unif, zero_smul, zero_add]
  rw [map_add, hrq, hdiag κ, hdiag (κ.shift d c₀ δ), map_sum]
  simp only [show (κ.shift d c₀ δ).g = κ.g from rfl]
  simp only [map_smul, hr4]
  -- compare the quadratic coefficients
  have key : ∑ M, coupC (κ.shift d c₀ δ) M • monoSet M Y = ∑ M, coupC κ M • monoSet M Y +
      ∑ i, κ.g • ((2 * δ) • monoSet (Mono.c : Mono d) Y +
        (δ / 2) • (monoSet (Mono.a2 s(i, i)) Y + monoSet (Mono.b2 s(i, i)) Y) +
        (-c₀) • monoSet (Mono.m2 i i) Y) := by
    rw [sum_mono, sum_mono]
    simp only [coupC, Coup.shift, ite_smul, zero_smul, sum_sym2_diag, sum_const_zero,
      add_zero, zero_add]
    have hm : ∀ (a : ℂ), (∑ i : Fin d, ∑ k : Fin d,
        if i = k then a • monoSet (Mono.m2 i k) Y else 0) = ∑ i, a • monoSet (Mono.m2 i i) Y := by
      intro a
      refine sum_congr rfl fun i _ => ?_
      rw [sum_eq_single i (fun k _ hk => by simp [Ne.symm hk]) (by simp)]
      simp
    rw [hm, hm]
    set A : Fin d → Alg d L N := fun i => monoSet (Mono.a2 s(i, i)) Y
    set B : Fin d → Alg d L N := fun i => monoSet (Mono.b2 s(i, i)) Y
    set M2 : Fin d → Alg d L N := fun i => monoSet (Mono.m2 i i) Y
    set C0 : Alg d L N := monoSet (Mono.c : Mono d) Y
    have split : ∀ (p q : ℂ) (F : Fin d → Alg d L N),
        ∑ i, (p + q) • F i = ∑ i, p • F i + ∑ i, q • F i := fun p q F => by
      rw [← sum_add_distrib]; exact sum_congr rfl fun i _ => add_smul _ _ _
    have e1 : -(κ.y - κ.g * δ) / 2 = -κ.y / 2 + κ.g * δ / 2 := by ring
    have e2 : κ.z - κ.g * c₀ = κ.z + -(κ.g * c₀) := by ring
    rw [e1, e2, split, split, split]
    have hR : ∑ i, κ.g • ((2 * δ) • C0 + (δ / 2) • (A i + B i) + (-c₀) • M2 i) =
        ((d : ℂ) * (κ.g * (2 * δ))) • C0 + ∑ i, (κ.g * δ / 2) • A i + ∑ i, (κ.g * δ / 2) • B i +
          ∑ i, (-(κ.g * c₀)) • M2 i := by
      rw [show ∑ i, κ.g • ((2 * δ) • C0 + (δ / 2) • (A i + B i) + (-c₀) • M2 i) =
          ∑ i, ((κ.g * (2 * δ)) • C0 + (κ.g * δ / 2) • A i + (κ.g * δ / 2) • B i +
            (-(κ.g * c₀)) • M2 i) from sum_congr rfl fun i _ => by module]
      simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin,
        ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    rw [hR, add_smul,
      show (2 * (d : ℂ) * κ.g * δ) = (d : ℂ) * (κ.g * (2 * δ)) by ring]
    abel
  rw [key]
  simp only [smul_add, sum_add_distrib, add_smul, ← smul_sum, smul_smul]
  rw [sum_smul]
  module

end Wick

end

end Step2
