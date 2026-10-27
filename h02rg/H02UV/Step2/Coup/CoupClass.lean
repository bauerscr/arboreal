import Step2.Coup.Coupling

/-!
# Classification of symmetric uniform polynomials (`h02uv-outline.tex`, Proposition `prop:C2`(ii))

* `unif_coeff`: the coefficients of a uniform polynomial on a patch are determined by it.
* `reflCenter_unif`, `permCorner_unif`, `Jsym_unif`: the action of the block-centred reflections,
  the coordinate permutations about a block corner and `J` on the coefficients.
* `unif_eq_Vcoup`: a uniform polynomial on a block that is invariant under these maps is
  `const + V_κ`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Matrix

variable {d L N : ℕ} [NeZero L]

/-! ### Uniqueness of the coefficients -/

theorem eps_unif (κ : ℂ) (c : Mono d → ℂ) (e : Fin d → Fin d → ℂ) (X : Finset (Lam d L N)) :
    ε (unif κ c e X) = κ := by
  simp only [unif, map_add, map_smul, map_one, map_sum, eps_monoSet, eps_mono4Set, smul_eq_mul,
    mul_zero, sum_const_zero, add_zero, mul_one]

theorem locCoef_unif {X : Finset (Lam d L N)} (hX : Patch X) (hne : X.Nonempty) (κ : ℂ)
    (c : Mono d → ℂ) (e : Fin d → Fin d → ℂ) : locCoef X (unif κ c e X) = c := by
  have hmu : ∀ β, mu (base X) β (unif κ c e X) = (c ᵥ* Amat X) β := by
    intro β
    simp only [unif, mu_add, mu_smul, mu_one, mu_sum, mu_mono4Set, mul_zero, sum_const_zero,
      add_zero, zero_add]
    rfl
  rw [locCoef]
  have : (fun β => mu (base X) β (unif κ c e X)) = c ᵥ* Amat X := funext hmu
  rw [this, vecMul_vecMul,
    mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (Amat_isUnit hX hne)), vecMul_one]

theorem mu4_unif {X : Finset (Lam d L N)} (hX : Patch X) (κ : ℂ) (c : Mono d → ℂ)
    (e : Fin d → Fin d → ℂ) (i k : Fin d) : mu4 (base X) i k (unif κ c e X) = e i k * X.card := by
  simp only [unif, mu4_add, mu4_smul, mu4_one, mu4_sum, mu4_monoSet, mu4_mono4Set hX,
    mul_zero, sum_const_zero, zero_add]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, sum_ite_eq, mem_univ, if_true]
  ring

/-- **The coefficients of a uniform polynomial are unique.** -/
theorem unif_coeff {X : Finset (Lam d L N)} (hX : Patch X) (hne : X.Nonempty)
    {κ κ' : ℂ} {c c' : Mono d → ℂ} {e e' : Fin d → Fin d → ℂ}
    (h : unif κ c e X = unif κ' c' e' X) : κ = κ' ∧ c = c' ∧ e = e' := by
  have hX0 : (X.card : ℂ) ≠ 0 := by exact_mod_cast hne.card_pos.ne'
  refine ⟨by rw [← eps_unif κ c e X, h, eps_unif], by
    rw [← locCoef_unif hX hne κ c e, h, locCoef_unif hX hne], ?_⟩
  funext i k
  have := mu4_unif hX κ c e i k
  rw [h, mu4_unif hX] at this
  exact (mul_right_cancel₀ hX0 this).symm

/-- `Loc_{X,Y} F` is uniform on `Y`, with the coefficients of `Loc_X F`. -/
theorem Loc2sXY_eq_unif {X : Finset (Lam d L N)} (Y : Finset (Lam d L N)) (F : Alg d L N) :
    Loc2sXY X Y F = unif (ε F * Y.card / X.card) (locCoef X F)
      (fun i k => mu4 (base X) i k F / X.card) Y := by
  rw [Loc2sXY, LocXY, Loc4sXY, unif]

/-! ### The action of the symmetries -/

/-- The sign of the reflection in direction `m`. -/
def rsg (m i : Fin d) : ℂ := if i = m then -1 else 1

theorem sperm_reflCenter (j : ℕ) (b : Fin d → ℕ) (m : Fin d) :
    SPerm (reflCenter (L := L) (N := N) j b m) ((Equiv.refl _).trans (Equiv.refl _))
      (fun i => (if i = m then -1 else 1) * 1) :=
  sperm_comp (sperm_refl m) (sperm_transl _)

theorem sperm_permCorner (j : ℕ) (b : Fin d → ℕ) (σ : Equiv.Perm (Fin d)) :
    SPerm (permCorner (L := L) (N := N) j b σ) ((Equiv.refl _).trans (σ.trans (Equiv.refl _)))
      (fun i => 1 * (1 * 1)) :=
  sperm_comp (sperm_transl _) (sperm_comp (sperm_perm σ) (sperm_transl _))

theorem reflCenter_rho (j : ℕ) (b : Fin d → ℕ) (m : Fin d) (M : Mono d) :
    (reflCenter (L := L) (N := N) j b m).ρ.symm M = M := rfl

theorem reflCenter_sgn (j : ℕ) (b : Fin d → ℕ) (m : Fin d) (M : Mono d) :
    (reflCenter (L := L) (N := N) j b m).sgn M = (-1 : ℂ) ^ cnt m M := by
  show (-1 : ℂ) ^ cnt m M * 1 = _
  rw [mul_one]

theorem permCorner_rho (j : ℕ) (b : Fin d → ℕ) (σ : Equiv.Perm (Fin d)) (M : Mono d) :
    (permCorner (L := L) (N := N) j b σ).ρ.symm M = permMono σ.symm M := rfl

theorem permCorner_sgn (j : ℕ) (b : Fin d → ℕ) (σ : Equiv.Perm (Fin d)) (M : Mono d) :
    (permCorner (L := L) (N := N) j b σ).sgn M = 1 := by
  show (1 : ℂ) * ((1 : ℂ) * 1) = 1
  ring

theorem reflCenter_unif {j : ℕ} (hj : j ≤ N) (b : Fin d → ℕ) (m : Fin d) (κ : ℂ)
    (c : Mono d → ℂ) (e : Fin d → Fin d → ℂ) :
    autAlg (reflCenter (L := L) (N := N) j b m).E (unif κ c e (blockSet j b)) =
      unif κ (fun M => (-1 : ℂ) ^ cnt m M * c M) (fun i k => rsg m i * rsg m k * e i k)
        (blockSet j b) := by
  have hS := sperm_reflCenter (L := L) (N := N) j b m
  have himg := reflCenter_img (L := L) (N := N) hj b m
  have hq := (reflCenter (L := L) (N := N) j b m).autAlg_sum_monoSet c (blockSet j b)
  rw [himg] at hq
  simp only [reflCenter_rho, reflCenter_sgn] at hq
  have h4 : ∀ i k, autAlg (reflCenter (L := L) (N := N) j b m).E (mono4sSet i k (blockSet j b)) =
      (rsg m i * rsg m k) • mono4sSet i k (blockSet j b) := by
    intro i k
    rw [hS.autAlg_mono4sSet, himg]
    simp only [Equiv.trans_apply, Equiv.refl_apply, rsg]
    congr 1
    split_ifs <;> push_cast <;> ring
  rw [unif, map_add, map_add, map_smul, map_one, hq, map_sum]
  simp only [map_sum, map_smul, h4, smul_smul]
  rw [unif]
  congr 2
  · exact sum_congr rfl fun M _ => by rw [mul_comm]
  · funext i
    exact sum_congr rfl fun k _ => by rw [mul_comm]

theorem permCorner_unif {j : ℕ} (hj : j ≤ N) (b : Fin d → ℕ) (σ : Equiv.Perm (Fin d)) (κ : ℂ)
    (c : Mono d → ℂ) (e : Fin d → Fin d → ℂ) :
    autAlg (permCorner (L := L) (N := N) j b σ).E (unif κ c e (blockSet j b)) =
      unif κ (fun M => c (permMono σ.symm M)) (fun a a' => e (σ.symm a) (σ.symm a'))
        (blockSet j b) := by
  have hS := sperm_permCorner (L := L) (N := N) j b σ
  have himg := permCorner_img (L := L) (N := N) hj b σ
  have hq := (permCorner (L := L) (N := N) j b σ).autAlg_sum_monoSet c (blockSet j b)
  rw [himg] at hq
  simp only [permCorner_rho, permCorner_sgn, mul_one] at hq
  have h4 : ∀ i k, autAlg (permCorner (L := L) (N := N) j b σ).E (mono4sSet i k (blockSet j b)) =
      mono4sSet (σ i) (σ k) (blockSet j b) := by
    intro i k
    rw [hS.autAlg_mono4sSet, himg]
    simp
  have e' : ∀ G : Fin d → Fin d → Alg d L N,
      ∑ i, ∑ k, G (σ i) (σ k) = ∑ a, ∑ a', G a a' := fun G =>
    Fintype.sum_equiv σ _ _ fun i => Fintype.sum_equiv σ _ _ fun k => rfl
  rw [unif, map_add, map_add, map_smul, map_one, hq, map_sum]
  simp only [map_sum, map_smul, h4]
  rw [unif, ← e' (fun a a' => e (σ.symm a) (σ.symm a') • mono4sSet a a' (blockSet j b))]
  simp only [Equiv.symm_apply_apply]

theorem Jsym_unif (κ : ℂ) (c : Mono d → ℂ) (e : Fin d → Fin d → ℂ) (Y : Finset (Lam d L N)) :
    Jsym (unif κ c e Y) = unif κ (fun M => c (swapM M)) (fun a a' => e a' a) Y := by
  rw [unif, map_add, map_add, map_smul, map_one, Jsym_sum_monoSet, map_sum]
  simp only [map_sum, map_smul, Jsym_mono4sSet]
  rw [unif, sum_comm (f := fun i k => e i k • mono4sSet k i Y)]

/-! ### The classification -/

/-- **Symmetric uniform polynomials are coupling polynomials.** -/
theorem coup_of_sym (c : Mono d → ℂ) (e : Fin d → Fin d → ℂ)
    (hr : ∀ m M, (-1 : ℂ) ^ cnt m M * c M = c M)
    (hre : ∀ m i k, rsg m i * rsg m k * e i k = e i k)
    (hp : ∀ (σ : Equiv.Perm (Fin d)) M, c (permMono σ.symm M) = c M)
    (hpe : ∀ (σ : Equiv.Perm (Fin d)) a a', e (σ.symm a) (σ.symm a') = e a a')
    (hJ : ∀ M, c (swapM M) = c M) (i₀ : Fin d) :
    c = coupC ⟨c (.m2 i₀ i₀), -2 * c (.a2 s(i₀, i₀)), c .c, e i₀ i₀⟩ ∧
      e = coupE ⟨c (.m2 i₀ i₀), -2 * c (.a2 s(i₀, i₀)), c .c, e i₀ i₀⟩ := by
  -- a coefficient which is odd under a reflection vanishes
  have hodd : ∀ m M, cnt m M = 1 → c M = 0 := by
    intro m M h
    have := hr m M
    rw [h, pow_one] at this
    linear_combination -this / 2
  have hdiag : ∀ i, c (.a2 s(i, i)) = c (.a2 s(i₀, i₀)) := by
    intro i
    have := hp (Equiv.swap i i₀) (.a2 s(i, i))
    rw [← this]
    simp [permMono, Equiv.swap_apply_left]
  have hm2 : ∀ i, c (.m2 i i) = c (.m2 i₀ i₀) := by
    intro i
    have := hp (Equiv.swap i i₀) (.m2 i i)
    rw [← this]
    simp [permMono, Equiv.swap_apply_left]
  refine ⟨funext fun M => ?_, funext fun i => funext fun k => ?_⟩
  · cases M with
    | c => rfl
    | a1 k => rw [hodd k _ (by simp [cnt])]; rfl
    | b1 k => rw [hodd k _ (by simp [cnt])]; rfl
    | a2 s =>
      induction s using Sym2.ind with
      | _ i k =>
        by_cases hik : i = k
        · subst hik
          simp only [coupC, Sym2.mk_isDiag_iff, if_true, hdiag]; ring
        · rw [hodd i _ (by simp [cnt, hik, Ne.symm hik])]
          simp [coupC, Sym2.mk_isDiag_iff, hik]
    | b2 s =>
      rw [← hJ]
      show c (.a2 s) = coupC _ (.b2 s)
      induction s using Sym2.ind with
      | _ i k =>
        by_cases hik : i = k
        · subst hik
          simp only [coupC, Sym2.mk_isDiag_iff, if_true, hdiag]; ring
        · rw [hodd i _ (by simp [cnt, hik, Ne.symm hik])]
          simp [coupC, Sym2.mk_isDiag_iff, hik]
    | m2 i k =>
      by_cases hik : i = k
      · subst hik; simp only [coupC, if_true, hm2]
      · rw [hodd i _ (by simp [cnt, hik, Ne.symm hik])]
        simp [coupC, hik]
  · by_cases hik : i = k
    · subst hik
      have := hpe (Equiv.swap i i₀) i₀ i₀
      simp only [Equiv.symm_swap, Equiv.swap_apply_right] at this
      simp [coupE, this]
    · have := hre i i k
      simp only [rsg, if_pos rfl, if_neg (Ne.symm hik), if_true] at this
      have h0 : e i k = 0 := by linear_combination (-1 / 2 : ℂ) * this
      simp [coupE, hik, h0]

/-- The coefficient form of `unif_eq_Vcoup`. -/
theorem unif_sym_coeff {j : ℕ} (hj : j ≤ N) (hL : 2 ^ (d + 3) + 8 * d < L) (hjN : j < N)
    {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) (i₀ : Fin d) {κ : ℂ}
    {c : Mono d → ℂ} {e : Fin d → Fin d → ℂ}
    (hR : ∀ m, autAlg (reflCenter (L := L) (N := N) j b m).E (unif κ c e (blockSet j b)) =
      unif κ c e (blockSet j b))
    (hP : ∀ σ, autAlg (permCorner (L := L) (N := N) j b σ).E (unif κ c e (blockSet j b)) =
      unif κ c e (blockSet j b))
    (hJ : Jsym (unif κ c e (blockSet (L := L) (N := N) j b)) = unif κ c e (blockSet j b)) :
    ∃ κ' : Coup, c = coupC κ' ∧ e = coupE κ' := by
  have hsm := isSmall_blockSet_of_mem hb
  have hX := patch_of_small hL hjN hsm
  have hne := hsm.2.1.1
  have hr : ∀ m M, (-1 : ℂ) ^ cnt m M * c M = c M := fun m M => by
    have := (unif_coeff hX hne ((reflCenter_unif hj b m κ c e).symm.trans (hR m))).2.1
    exact congrFun this M
  have hre : ∀ m i k, rsg m i * rsg m k * e i k = e i k := fun m i k => by
    have := (unif_coeff hX hne ((reflCenter_unif hj b m κ c e).symm.trans (hR m))).2.2
    exact congrFun (congrFun this i) k
  have hp : ∀ (σ : Equiv.Perm (Fin d)) M, c (permMono σ.symm M) = c M := fun σ M => by
    have := (unif_coeff hX hne ((permCorner_unif hj b σ κ c e).symm.trans (hP σ))).2.1
    exact congrFun this M
  have hpe : ∀ (σ : Equiv.Perm (Fin d)) a a', e (σ.symm a) (σ.symm a') = e a a' := fun σ a a' => by
    have := (unif_coeff hX hne ((permCorner_unif hj b σ κ c e).symm.trans (hP σ))).2.2
    exact congrFun (congrFun this a) a'
  have hJc : ∀ M, c (swapM M) = c M := fun M => by
    have := (unif_coeff hX hne ((Jsym_unif κ c e _).symm.trans hJ)).2.1
    exact congrFun this M
  exact ⟨_, coup_of_sym c e hr hre hp hpe hJc i₀⟩

end

end Step2
