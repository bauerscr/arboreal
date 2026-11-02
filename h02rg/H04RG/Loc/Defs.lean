import Loc.LocDef

/-!
# Localisation for two species (`ℍ^{0|4}`, `d ≥ 3`)

The `ℍ^{0|4}` model has two species of fermions `ψ^a, ψ̄^a`, `a ∈ Fin 2`. Its Grassmann algebra is
`𝒩(Λ × Fin 2)` (`AlgS`). In `d ≥ 5` the relevant and marginal local monomials are, by the
`U(1) × U(1)` (species-wise) symmetry, the species-diagonal quadratic monomials
`∑_a M(ψ^a, ψ̄^a)` with `M` in the single-species basis `Loc.Mono d`. In `d = 3, 4` the
quartic `Q` must be added; that is not done here.

We do not change the single-species library `Loc`. Instead we transport it species by species:

* `extV a : V(Λ) → V(Λ × Fin 2)` extends a vector by zero off species `a`, and
  `emb a = ExteriorAlgebra.map (extV a) : 𝒩(Λ) →ₐ 𝒩(Λ × Fin 2)` puts a single-species element
  on species `a` (`emb a ψ_x = ψ^a_x`);
* `coeff_emb`: the coefficients of `emb a F` on species-`a` sequences are those of `F`;
  `coeff_emb_ne`: they vanish on species-`a` sequences if `F` was put on another species;
* `cf2s a F x y = F_{((x,a),+)((y,a),-)}` and `mus a b β F` are the species-`a` versions of
  `Loc.cf2` and `Loc.mu`; `mus_emb` / `mus_emb_ne` reduce them to the single-species ones;
* `LocSXY X Y F = F_∅ |Y|/|X| + ∑_a ∑_M c^a_M(F) emb a (M(Y))` with
  `c^a(F) = mus a (F) A_X^{-1}` (the matrix `A_X = Loc.Amat X` is the single-species one);
* `mus_LocSX`: `LocS_X F` has the same species-diagonal pairings with all test polynomials as
  `F` (the defining property, analogue of `Loc.mu_LocX`), and `ε_LocSX`: the same constant term.
-/

namespace H04RG.LocS

noncomputable section

open Finset Matrix Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

/-- The sites of the two-species model. -/
abbrev LamS (d L N : ℕ) := Lam d L N × Fin 2

/-- The Grassmann algebra `𝒩(Λ × Fin 2)` of the two-species model. -/
abbrev AlgS (d L N : ℕ) [NeZero L] := Grassmann.N (LamS d L N)

/-- Label of species `a`: `(x, σ) ↦ ((x, a), σ)`. -/
def lab (a : Fin 2) (z : Sf (Lam d L N)) : Sf (LamS d L N) := ((z.1, a), z.2)

/-- Extension by zero off species `a`. -/
def extV (a : Fin 2) : V (Lam d L N) →ₗ[ℂ] V (LamS d L N) where
  toFun v w := if w.1.2 = a then v (w.1.1, w.2) else 0
  map_add' v v' := by
    funext w
    by_cases h : w.1.2 = a <;> simp [h]
  map_smul' r v := by
    funext w
    by_cases h : w.1.2 = a <;> simp [h]

theorem extV_apply_lab (a : Fin 2) (v : V (Lam d L N)) (z : Sf (Lam d L N)) :
    extV a v (lab a z) = v z := by
  simp [extV, lab]

theorem extV_apply_lab_ne {a b : Fin 2} (h : b ≠ a) (v : V (Lam d L N)) (z : Sf (Lam d L N)) :
    extV b v (lab a z) = 0 := by
  simp [extV, lab, Ne.symm h]

theorem extV_ev (a : Fin 2) (z : Sf (Lam d L N)) : extV a (ev z) = ev (lab a z) := by
  funext w
  obtain ⟨⟨y, b⟩, σ⟩ := w
  obtain ⟨x, τ⟩ := z
  by_cases hb : b = a
  · subst hb
    simp [extV, ev, lab, Pi.single_apply, Prod.ext_iff]
  · simp [extV, ev, lab, Prod.ext_iff, hb]

/-- Put a single-species element on species `a`. -/
def emb (a : Fin 2) : Alg d L N →ₐ[ℂ] AlgS d L N := ExteriorAlgebra.map (extV a)

theorem emb_ψ (a : Fin 2) (z : Sf (Lam d L N)) : emb a (ψ z) = ψ (lab a z) := by
  simp [emb, ψ, extV_ev]

theorem emb_psi (a : Fin 2) (x : Lam d L N) : emb a (psi x) = psi (x, a) := by
  simp [psi, emb_ψ, lab]

theorem emb_psibar (a : Fin 2) (x : Lam d L N) : emb a (psibar x) = psibar (x, a) := by
  simp [psibar, emb_ψ, lab]

/-- The constant term is preserved. -/
theorem ε_emb (a : Fin 2) (F : Alg d L N) : ε (emb a F) = ε F := by
  have h : (ε : AlgS d L N →ₐ[ℂ] ℂ).comp (emb a) = (ε : Alg d L N →ₐ[ℂ] ℂ) := by
    refine ExteriorAlgebra.hom_ext ?_
    ext v
    simp [emb, ExteriorAlgebra.algebraMapInv]
  exact congrArg (fun f : Alg d L N →ₐ[ℂ] ℂ => f F) h

/-- Coefficients of `emb a F` on species-`a` sequences are those of `F`. -/
theorem coeff_emb (a : Fin 2) (F : Alg d L N) {n : ℕ} (z : Fin n → Sf (Lam d L N)) :
    coeff (emb a F) (lab a ∘ z) = coeff F z := by
  induction F using induction_ιMulti with
  | hzero => simp
  | hadd F G hF hG => rw [map_add, coeff_add, coeff_add, hF, hG]
  | hsmul r F hF => rw [map_smul, coeff_smul, coeff_smul, hF]
  | hι m v =>
    rw [emb, ExteriorAlgebra.map_apply_ιMulti]
    by_cases h : n = m
    · subst h
      rw [coeff_ιMulti, coeff_ιMulti]
      congr 1
      ext i j
      simp [extV_apply_lab]
    · rw [coeff_ιMulti_of_ne _ _ h, coeff_ιMulti_of_ne _ _ h]

/-- Coefficients of `emb b F` vanish on non-empty species-`a` sequences, `b ≠ a`. -/
theorem coeff_emb_ne {a b : Fin 2} (hab : b ≠ a) (F : Alg d L N) {n : ℕ} (hn : 0 < n)
    (z : Fin n → Sf (Lam d L N)) : coeff (emb b F) (lab a ∘ z) = 0 := by
  induction F using induction_ιMulti with
  | hzero => simp
  | hadd F G hF hG => rw [map_add, coeff_add, hF, hG, add_zero]
  | hsmul r F hF => rw [map_smul, coeff_smul, hF, mul_zero]
  | hι m v =>
    rw [emb, ExteriorAlgebra.map_apply_ιMulti]
    by_cases h : n = m
    · subst h
      rw [coeff_ιMulti]
      have : (Matrix.of fun i j => (extV b ∘ v) j ((lab a ∘ z) i)) = 0 := by
        ext i j
        simp [extV_apply_lab_ne hab]
      rw [this]
      haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      exact Matrix.det_zero inferInstance
    · rw [coeff_ιMulti_of_ne _ _ h]

/-! ### Species-diagonal quadratic coefficients and pairings -/

/-- `F_{((x,a),+)((y,a),-)}`. -/
def cf2s (a : Fin 2) (F : AlgS d L N) (x y : Lam d L N) : ℂ :=
  coeff F ![(((x, a) : LamS d L N), (1 : ℤˣ)), ((y, a), -1)]

theorem pair_lab (a : Fin 2) (x y : Lam d L N) :
    (![(((x, a) : LamS d L N), (1 : ℤˣ)), ((y, a), -1)] : Fin 2 → Sf (LamS d L N)) =
      lab a ∘ ![(x, (1 : ℤˣ)), (y, -1)] := by
  funext i
  fin_cases i <;> rfl

theorem cf2s_emb (a : Fin 2) (G : Alg d L N) (x y : Lam d L N) :
    cf2s a (emb a G) x y = cf2 G x y := by
  rw [cf2s, pair_lab, coeff_emb, cf2]

theorem cf2s_emb_ne {a b : Fin 2} (hab : b ≠ a) (G : Alg d L N) (x y : Lam d L N) :
    cf2s a (emb b G) x y = 0 := by
  rw [cf2s, pair_lab, coeff_emb_ne hab G (by norm_num)]

/-- The species-`a` pairing with the test polynomial `Q_β`, based at `b`. -/
def mus (a : Fin 2) (b : Lam d L N) (β : Mono d) (F : AlgS d L N) : ℂ :=
  ∑ x, ∑ y, cf2s a F x y * (Qpoly β (lift b x) (lift b y) : ℂ)

theorem mus_emb (a : Fin 2) (b : Lam d L N) (β : Mono d) (G : Alg d L N) :
    mus a b β (emb a G) = mu b β G := by
  simp only [mus, mu, cf2s_emb]

theorem mus_emb_ne {a c : Fin 2} (hac : c ≠ a) (b : Lam d L N) (β : Mono d) (G : Alg d L N) :
    mus a b β (emb c G) = 0 := by
  simp only [mus, cf2s_emb_ne hac, zero_mul, sum_const_zero]

theorem cf2s_add (a : Fin 2) (F G : AlgS d L N) (x y : Lam d L N) :
    cf2s a (F + G) x y = cf2s a F x y + cf2s a G x y := by
  simp [cf2s]

theorem cf2s_smul (a : Fin 2) (r : ℂ) (F : AlgS d L N) (x y : Lam d L N) :
    cf2s a (r • F) x y = r * cf2s a F x y := by
  simp [cf2s]

theorem mus_add (a : Fin 2) (b : Lam d L N) (β : Mono d) (F G : AlgS d L N) :
    mus a b β (F + G) = mus a b β F + mus a b β G := by
  simp only [mus, cf2s_add, add_mul, sum_add_distrib]

theorem mus_smul (a : Fin 2) (b : Lam d L N) (β : Mono d) (r : ℂ) (F : AlgS d L N) :
    mus a b β (r • F) = r * mus a b β F := by
  simp only [mus, cf2s_smul, mul_assoc, mul_sum]

theorem mus_sum {ι : Type*} (s : Finset ι) (a : Fin 2) (b : Lam d L N) (β : Mono d)
    (F : ι → AlgS d L N) : mus a b β (∑ i ∈ s, F i) = ∑ i ∈ s, mus a b β (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [sum_empty]
    simp [mus, cf2s]
  | insert i s hi ih => rw [sum_insert hi, sum_insert hi, mus_add, ih]

theorem mus_one (a : Fin 2) (b : Lam d L N) (β : Mono d) : mus a b β (1 : AlgS d L N) = 0 := by
  have h1 : (1 : AlgS d L N) = emb a 1 := (map_one _).symm
  rw [h1, mus_emb, mu_one]

/-! ### The two-species localisation -/

/-- The local polynomial `M(Y)` on species `a`. -/
def monoSets (a : Fin 2) (M : Mono d) (Y : Finset (Lam d L N)) : AlgS d L N :=
  emb a (monoSet M Y)

/-- The species-`a` coefficients of the localisation. -/
def locCoefs (a : Fin 2) (X : Finset (Lam d L N)) (F : AlgS d L N) : Mono d → ℂ :=
  (fun β => mus a (base X) β F) ᵥ* (Amat X)⁻¹

/-- `LocS_{X,Y} F = F_∅ |Y|/|X| + ∑_a ∑_M c^a_M(F) M(ψ^a,ψ̄^a)(Y)`. -/
def LocSXY (X Y : Finset (Lam d L N)) (F : AlgS d L N) : AlgS d L N :=
  (ε F * Y.card / X.card) • (1 : AlgS d L N) + ∑ a, ∑ M, locCoefs a X F M • monoSets a M Y

/-- `LocS_X = Loc2_{X,X}`. -/
def LocSX (X : Finset (Lam d L N)) (F : AlgS d L N) : AlgS d L N := LocSXY X X F

theorem mus_monoSets (a c : Fin 2) (b : Lam d L N) (β M : Mono d) (Y : Finset (Lam d L N)) :
    mus a b β (monoSets c M Y) = if c = a then mu b β (monoSet M Y) else 0 := by
  rw [monoSets]
  split_ifs with h
  · subst h; exact mus_emb _ _ _ _
  · exact mus_emb_ne h _ _ _

/-- The defining property: `LocS_X F` has the same species-diagonal pairings as `F`. -/
theorem mus_LocSX {X : Finset (Lam d L N)} (hX : Patch X) (hne : X.Nonempty) (F : AlgS d L N)
    (a : Fin 2) (β : Mono d) : mus a (base X) β (LocSX X F) = mus a (base X) β F := by
  rw [LocSX, LocSXY, mus_add, mus_smul, mus_one, mul_zero, zero_add, mus_sum]
  simp only [mus_sum, mus_smul, mus_monoSets, mul_ite, mul_zero]
  rw [sum_eq_single a (fun c _ hc => by simp [hc]) (by simp)]
  simp only [if_true]
  have h1 : (∑ M, locCoefs a X F M * mu (base X) β (monoSet M X)) =
      (locCoefs a X F ᵥ* Amat X) β := rfl
  rw [h1, locCoefs, vecMul_vecMul,
    nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (Amat_isUnit hX hne)), vecMul_one]

/-- `ε (M(Y)) = 0`: local monomials have no constant term. -/
theorem ε_monoSets (a : Fin 2) (M : Mono d) (Y : Finset (Lam d L N)) :
    ε (monoSets a M Y) = 0 := by
  rw [monoSets, ε_emb, monoSet, map_sum]
  refine sum_eq_zero fun x _ => ?_
  rw [monoAt, map_list_sum, List.map_map]
  refine List.sum_eq_zero fun r hr => ?_
  obtain ⟨p, _, rfl⟩ := List.mem_map.1 hr
  have hψ : ∀ z : Sf (Lam d L N), ε (ψ z : Alg d L N) = 0 := fun z => by
    simp [ψ, ExteriorAlgebra.algebraMapInv]
  simp only [Function.comp_apply, map_smul, map_mul, psi, psibar, hψ, mul_zero, smul_zero]

/-- The constant term is reproduced. -/
theorem ε_LocSX {X : Finset (Lam d L N)} (hne : X.Nonempty) (F : AlgS d L N) :
    ε (LocSX X F) = ε F := by
  have hc : (X.card : ℂ) ≠ 0 := by exact_mod_cast hne.card_pos.ne'
  rw [LocSX, LocSXY, map_add, map_smul, map_one, map_sum]
  simp only [map_sum, map_smul, ε_monoSets, smul_eq_mul, mul_one, mul_zero, sum_const_zero,
    add_zero]
  field_simp

end

end H04RG.LocS
