import Step2.Map.SymCov
import Loc.Symplectic

/-!
# The symplectic symmetry `J` (`h02uv-outline.tex`, Section `sec:coupling-coords`)

`J ψ = ψ̄`, `J ψ̄ = -ψ` (`Loc.Jsym`).

* `ECC_Jsym2`: `𝔼_C` commutes with `J` for symmetric complex `C`.
* `Jsym_mono4s`: `J M̂^{ik}_x = M̂^{ki}_x`; `mu4_Jsym`: `μ⁽⁴⁾_{κκ'}(J F) = μ⁽⁴⁾_{κ'κ}(F)`.
* `Loc2sXY_Jsym`: the symmetric localisation commutes with `J`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Matrix

variable {d L N : ℕ} [NeZero L]

/-! ### `𝔼_C` and `J` -/

theorem ECC_Jsym2 {C : Matrix (Lam d L N) (Lam d L N) ℂ} (hC : ∀ x y, C x y = C y x)
    (F : Alg2 d L N) : ECC C (Jsym2 F) = Jsym (ECC C F) := by
  refine ECC_comm_of _ _ (fun G => ?_) (fun G => ?_) F
  · have h1 : ∀ (b : Lam d L N ⊕ Lam d L N) (H : Alg2 d L N),
        D (b, -1) (Jsym2 H) = Jsym2 (D (b, 1) H) := by
      intro b H
      rw [Jsym2, D_map]; rfl
    have h2 : ∀ (b : Lam d L N ⊕ Lam d L N) (H : Alg2 d L N),
        D (b, 1) (Jsym2 H) = -Jsym2 (D (b, -1) H) := by
      intro b H
      rw [Jsym2, D_map, ← map_neg]
      have : coord ((b, 1) : Sf (Lam d L N ⊕ Lam d L N)) ∘ₗ JV2 = -coord (b, -1) := by
        refine LinearMap.ext fun v => ?_
        simp [JV2]
      rw [this, map_neg, LinearMap.neg_apply]; rfl
    simp only [LζC_apply, h1, h2, map_sum, map_smul, smul_neg]
    rw [sum_comm]
    refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
    rw [hC, D_comm, map_neg, smul_neg, neg_neg]
  · simp only [proj, Jsym2, Jsym, map_map_apply]
    exact map_congr_apply (fun v b => rfl) G

theorem expLC_Jsym {C : Matrix (Lam d L N) (Lam d L N) ℂ} (hC : ∀ x y, C x y = C y x)
    (F : Alg d L N) : expLC C (Jsym F) = Jsym (expLC C F) := by
  rw [← ECC_theta, ← ECC_theta, theta_Jsym, ECC_Jsym2 hC]

theorem FC_Jsym {C : Matrix (Lam d L N) (Lam d L N) ℂ} (hC : ∀ x y, C x y = C y x)
    (A B : Alg d L N) : Jsym (FC C A B) = FC C (Jsym A) (Jsym B) := by
  have hC' : ∀ x y, (-C) x y = (-C) y x := fun x y => by simp [hC x y]
  simp only [FC, map_sub, map_mul, ← expLC_Jsym hC, ← expLC_Jsym hC']

/-! ### The quartic part -/

theorem Jsym_ψ_plus (x : Lam d L N) : Jsym (ψ ((x, 1) : Sf (Lam d L N))) = ψ (x, -1) :=
  Jsym_psi x

theorem Jsym_ψ_minus (x : Lam d L N) : Jsym (ψ ((x, -1) : Sf (Lam d L N))) = -ψ (x, 1) :=
  Jsym_psibar x

theorem Jsym_gmono4 (e e' : Dir d) (x : Lam d L N) : Jsym (gmono4 e e' x) = gmono4 e' e x := by
  rw [gmono4_eq, gmono4_eq]
  simp only [map_mul, map_sub, Jsym_ψ_plus, Jsym_ψ_minus]
  set a := ψ ((x + dirVec e, 1) : Sf (Lam d L N)) - ψ (x, 1)
  set a' := ψ ((x + dirVec e', 1) : Sf (Lam d L N)) - ψ (x, 1)
  set b := ψ ((x + dirVec e, -1) : Sf (Lam d L N)) - ψ (x, -1)
  set b' := ψ ((x + dirVec e', -1) : Sf (Lam d L N)) - ψ (x, -1)
  have hra : ∀ u v : Sf (Lam d L N), ψ u - ψ v ∈
      LinearMap.range (ExteriorAlgebra.ι ℂ : V _ →ₗ[ℂ] Alg d L N) :=
    fun u v => sub_mem (ψ_mem_range _) (ψ_mem_range _)
  have e1 : -ψ ((x + dirVec e', 1) : Sf (Lam d L N)) - -ψ (x, 1) = -a' := by
    simp only [a']; abel
  rw [e1]
  have hab : b * a' = -(a' * b) := anticomm_of_mem_range (hra _ _) (hra _ _)
  have hpp : ψ ((x, -1) : Sf (Lam d L N)) * ψ (x, 1) = -(ψ (x, 1) * ψ (x, -1)) :=
    anticomm_of_mem_range (ψ_mem_range _) (ψ_mem_range _)
  calc b * (-a' * (ψ (x, -1) * -ψ (x, 1)))
      = (b * a') * (ψ ((x, -1) : Sf (Lam d L N)) * ψ (x, 1)) := by
        simp only [neg_mul, mul_neg, neg_neg, mul_assoc]
    _ = a' * (b * (ψ (x, 1) * ψ (x, -1))) := by
        rw [hab, hpp, neg_mul_neg, mul_assoc]

theorem Jsym_mono4s (i k : Fin d) (x : Lam d L N) : Jsym (mono4s i k x) = mono4s k i x := by
  unfold mono4s
  by_cases hik : i = k
  · subst hik
    rw [if_pos rfl, map_smul, map_add, Jsym_gmono4, Jsym_gmono4]
  · rw [if_neg hik, if_neg (Ne.symm hik), map_smul, map_add, map_sub, map_sub, Jsym_gmono4,
      Jsym_gmono4, Jsym_gmono4, Jsym_gmono4]
    congr 1; abel

theorem Jsym_mono4sSet (i k : Fin d) (Y : Finset (Lam d L N)) :
    Jsym (mono4sSet i k Y) = mono4sSet k i Y := by
  rw [mono4sSet, map_sum, mono4sSet]
  exact sum_congr rfl fun x _ => Jsym_mono4s i k x

/-! ### Coefficients under `J` -/

theorem contr_smul_family {M : Type*} [AddCommGroup M] [Module ℂ M] {m : ℕ} (c : Fin m → ℂ)
    (φ : Fin m → Module.Dual ℂ M) (x : ExteriorAlgebra ℂ M) :
    contr (fun i => c i • φ i) x = (∏ i, c i) • contr φ x := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    show contr (fun i : Fin m => c i.succ • φ i.succ)
        (CliffordAlgebra.contractLeft (c 0 • φ 0) x) =
      (∏ i, c i) • contr (fun i : Fin m => φ i.succ) (CliffordAlgebra.contractLeft (φ 0) x)
    rw [ih (fun i => c i.succ) (fun i => φ i.succ), map_smul, LinearMap.smul_apply, map_smul,
      smul_smul, Fin.prod_univ_succ, mul_comm]

theorem coeff_Jsym (F : Alg d L N) {n : ℕ} (z : Fin n → Sf (Lam d L N)) :
    coeff (Jsym F) z = (∏ i, (if (z i).2 = 1 then (-1 : ℂ) else 1)) *
      coeff F (fun i => ((z i).1, -(z i).2)) := by
  have hc : ∀ i, coord (z i) ∘ₗ JV =
      (if (z i).2 = 1 then (-1 : ℂ) else 1) • coord ((z i).1, -(z i).2) := by
    intro i
    obtain ⟨y, σ⟩ := z i
    rcases Int.units_eq_one_or σ with rfl | rfl
    · simp only [if_pos rfl]
      rw [coord_JV_plus]; ext v; simp
    · simp only [if_neg units_ne.symm]
      rw [coord_JV_minus]; ext v; simp
  rw [coeff, Dseq, Jsym, contr_map, algebraMapInv_map]
  simp only [hc]
  rw [contr_smul_family, map_smul, smul_eq_mul]
  rfl

theorem cf4_Jsym (F : Alg d L N) (x : Fin 4 → Lam d L N) :
    cf4 (Jsym F) x = cf4 F ![x 1, x 0, x 3, x 2] := by
  rw [cf4, coeff_Jsym]
  have hsign : (∏ i : Fin 4, (if ((x i, pat4 i) : Sf (Lam d L N)).2 = 1 then (-1 : ℂ) else 1)) = 1 := by
    simp [Fin.prod_univ_four, pat4, units_ne.symm]
  rw [hsign, one_mul]
  set σ : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3
  have e : (fun i => (((x i, pat4 i) : Sf (Lam d L N)).1, -((x i, pat4 i) : Sf (Lam d L N)).2)) =
      (fun r => ((![x 1, x 0, x 3, x 2] : Fin 4 → Lam d L N) r, pat4 r)) ∘ σ := by
    funext r
    fin_cases r <;> simp [σ, pat4, Equiv.swap_apply_of_ne_of_ne]
  rw [e, coeff_perm]
  have hs : Equiv.Perm.sign σ = 1 := by
    simp only [σ, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (show (0 : Fin 4) ≠ 1 by decide),
      Equiv.Perm.sign_swap (show (2 : Fin 4) ≠ 3 by decide)]
    decide
  rw [hs]; simp [cf4]

theorem mu4_Jsym (b : Lam d L N) (κ κ' : Fin d) (F : Alg d L N) :
    mu4 b κ κ' (Jsym F) = mu4 b κ' κ F := by
  simp only [mu4, cf4_Jsym]
  set τ : (Fin 4 → Lam d L N) ≃ (Fin 4 → Lam d L N) :=
    ⟨fun x => ![x 1, x 0, x 3, x 2], fun x => ![x 1, x 0, x 3, x 2],
      fun x => by funext r; fin_cases r <;> rfl, fun x => by funext r; fin_cases r <;> rfl⟩
  refine Fintype.sum_equiv τ _ _ fun x => ?_
  simp only [τ, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  push_cast; ring

/-! ### The localisation commutes with `J` -/

theorem Loc4sXY_Jsym (X Y : Finset (Lam d L N)) (F : Alg d L N) :
    Loc4sXY X Y (Jsym F) = Jsym (Loc4sXY X Y F) := by
  rw [Loc4sXY, Loc4sXY, map_sum]
  simp only [map_sum, map_smul, Jsym_mono4sSet, mu4_Jsym]
  rw [sum_comm]

theorem Loc2sXY_Jsym {X : Finset (Lam d L N)} (hX : Patch X) (hne : X.Nonempty)
    (Y : Finset (Lam d L N)) (F : Alg d L N) : Loc2sXY X Y (Jsym F) = Jsym (Loc2sXY X Y F) := by
  rw [Loc2sXY, Loc2sXY, map_add, LocXY_Jsym hX hne, Loc4sXY_Jsym]

end

end Step2
