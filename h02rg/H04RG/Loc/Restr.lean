import H04RG.Loc.Defs

/-!
# Restriction to one species

`res a : 𝒩(Λ × Fin 2) →ₐ 𝒩(Λ)` sets the fields of the other species to zero and relabels species
`a` as the single species. It is a left inverse of `emb a` (`res_emb`) and kills `emb b` for
`b ≠ a` up to constants (`res_emb_ne`). Its coefficients are the species-`a` coefficients
(`coeff_res`), so the species-`a` pairings are single-species pairings of the restriction
(`mus_eq_mu_res`), and the two-species localisation restricts to the single-species one:
`res a (LocS_{X,Y} F) = Loc_{X,Y} (res a F)` (`res_LocSXY`).

This is how the two-species contraction bound will be reduced, on species-diagonal sequences of
length `2`, to the single-species bound `Loc.exists_two_bound`.
-/

namespace H04RG.LocS

noncomputable section

open Finset Matrix Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

/-- Restriction of vectors to species `a`. -/
def resV (a : Fin 2) : V (LamS d L N) →ₗ[ℂ] V (Lam d L N) where
  toFun v z := v (lab a z)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem resV_extV (a : Fin 2) : (resV a).comp (extV a) = (LinearMap.id : V (Lam d L N) →ₗ[ℂ] _) := by
  ext v z
  simp [resV, extV_apply_lab]

theorem resV_extV_ne {a b : Fin 2} (hab : b ≠ a) :
    (resV a).comp (extV b) = (0 : V (Lam d L N) →ₗ[ℂ] V (Lam d L N)) := by
  ext v z
  simp [resV, extV_apply_lab_ne hab]

/-- Restriction to species `a`. -/
def res (a : Fin 2) : AlgS d L N →ₐ[ℂ] Alg d L N := ExteriorAlgebra.map (resV a)

theorem res_emb (a : Fin 2) (G : Alg d L N) : res a (emb a G) = G := by
  have h : (res a).comp (emb a) = AlgHom.id ℂ (Alg d L N) := by
    refine ExteriorAlgebra.hom_ext ?_
    ext v
    simp [res, emb, ← LinearMap.comp_apply (resV a) (extV a), resV_extV]
  exact congrArg (fun f : Alg d L N →ₐ[ℂ] Alg d L N => f G) h

theorem res_emb_ne {a b : Fin 2} (hab : b ≠ a) (G : Alg d L N) :
    res a (emb b G) = algebraMap ℂ (Alg d L N) (ε G) := by
  have h : (res a).comp (emb b) = (Algebra.ofId ℂ (Alg d L N)).comp (ε : Alg d L N →ₐ[ℂ] ℂ) := by
    refine ExteriorAlgebra.hom_ext ?_
    ext v
    simp [res, emb, ← LinearMap.comp_apply (resV a) (extV b), resV_extV_ne hab,
      ExteriorAlgebra.algebraMapInv]
  exact congrArg (fun f : Alg d L N →ₐ[ℂ] Alg d L N => f G) h

theorem ε_res (a : Fin 2) (F : AlgS d L N) : ε (res a F) = ε F := by
  have h : (ε : Alg d L N →ₐ[ℂ] ℂ).comp (res a) = (ε : AlgS d L N →ₐ[ℂ] ℂ) := by
    refine ExteriorAlgebra.hom_ext ?_
    ext v
    simp [res, ExteriorAlgebra.algebraMapInv]
  exact congrArg (fun f : AlgS d L N →ₐ[ℂ] ℂ => f F) h

/-- The coefficients of the restriction are the species-`a` coefficients. -/
theorem coeff_res (a : Fin 2) (F : AlgS d L N) {n : ℕ} (z : Fin n → Sf (Lam d L N)) :
    coeff (res a F) z = coeff F (lab a ∘ z) := by
  induction F using induction_ιMulti with
  | hzero => simp
  | hadd F G hF hG => rw [map_add, coeff_add, coeff_add, hF, hG]
  | hsmul r F hF => rw [map_smul, coeff_smul, coeff_smul, hF]
  | hι m v =>
    rw [res, ExteriorAlgebra.map_apply_ιMulti]
    by_cases h : n = m
    · subst h
      rw [coeff_ιMulti, coeff_ιMulti]
      rfl
    · rw [coeff_ιMulti_of_ne _ _ h, coeff_ιMulti_of_ne _ _ h]

theorem cf2s_eq_cf2_res (a : Fin 2) (F : AlgS d L N) (x y : Lam d L N) :
    cf2s a F x y = cf2 (res a F) x y := by
  rw [cf2s, pair_lab, cf2, coeff_res]

theorem mus_eq_mu_res (a : Fin 2) (b : Lam d L N) (β : Mono d) (F : AlgS d L N) :
    mus a b β F = mu b β (res a F) := by
  simp only [mus, mu, cf2s_eq_cf2_res]

theorem locCoefs_eq (a : Fin 2) (X : Finset (Lam d L N)) (F : AlgS d L N) :
    locCoefs a X F = locCoef X (res a F) := by
  simp only [locCoefs, locCoef, mus_eq_mu_res]

theorem ε_monoSet (M : Mono d) (Y : Finset (Lam d L N)) : ε (monoSet M Y) = 0 := by
  rw [← ε_emb 0, ← monoSets]
  exact ε_monoSets 0 M Y

theorem res_monoSets (a c : Fin 2) (M : Mono d) (Y : Finset (Lam d L N)) :
    res a (monoSets c M Y) = if c = a then monoSet M Y else 0 := by
  rw [monoSets]
  split_ifs with h
  · subst h; exact res_emb _ _
  · rw [res_emb_ne h, ε_monoSet, map_zero]

/-- The two-species localisation restricts to the single-species one. -/
theorem res_LocSXY (a : Fin 2) (X Y : Finset (Lam d L N)) (F : AlgS d L N) :
    res a (LocSXY X Y F) = LocXY X Y (res a F) := by
  rw [LocSXY, LocXY, map_add, map_smul, map_one, ε_res, map_sum]
  congr 1
  simp only [map_sum, map_smul, res_monoSets, smul_ite, smul_zero]
  rw [sum_eq_single a (fun c _ hc => by simp [hc]) (by simp)]
  simp only [if_true, locCoefs_eq]

end

end H04RG.LocS
