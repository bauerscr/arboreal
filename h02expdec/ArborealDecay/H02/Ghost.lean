module

public import ArborealDecay.H02.Tree
public import ArborealDecay.H02.Symm
public import ArborealDecay.H02.Ward

/-!
# The ghost vertex: `prop:h02-forest` for `h ≥ 0`

The arboreal gas with external field `h` is the arboreal gas on the extended graph
`Λ ∪ {g}` (`Option Λ`, ghost `g = none`) with weights `ghostW w h` (`w` on `Λ`, `h_i` on `ig`).

* `emb : Ω^{2Λ} → Ω^{2(Λ ∪ {g})}`, `ξ_i ↦ ξ_{some i}`, `η_i ↦ η_{some i}`.
* **Pinning** (`expect_ghost`): if `Y` is `T`-invariant on `Λ ∪ {g}` and
  `ξ_gη_g Y = ξ_gη_g emb(G)`, then `[Y]^{Λ∪g}_{ghostW w h', 0} = [G]^Λ_{w, h'}` (any real field
  `h'`).  Consequences:
  - `Zforest_ghostW`: `Z^{forest}(ghostW w h') = [1]_{w,h'}`;
  - `arborealProb_ghost_zforest` (`e:zforest`): `P[a ↔ g] = ⟨z_a⟩_{w,h}`;
  - `arborealProb_ghost_uu` (`e:u0uxforest`): `P[a ↔ x] = -⟨u_a·u_x⟩_{w,h}` (on `Λ ∪ {g}`).
-/

@[expose] public section

namespace H02

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical CliffordAlgebra

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

local notation "A" => Grassmann Λ
local notation "AO" => Grassmann (Option Λ)

/-- The generator embedding `Λ → Option Λ`. -/
def embLin : Gen Λ →ₗ[ℝ] Gen (Option Λ) where
  toFun v := fun s => match s with
    | Sum.inl (some i) => v (Sum.inl i)
    | Sum.inr (some i) => v (Sum.inr i)
    | Sum.inl none => 0
    | Sum.inr none => 0
  map_add' v w := by funext s; rcases s with (_ | i) | (_ | i) <;> simp
  map_smul' r v := by funext s; rcases s with (_ | i) | (_ | i) <;> simp

/-- `emb : Ω^{2Λ} → Ω^{2(Λ∪g)}`. -/
def emb : A →ₐ[ℝ] AO := ExteriorAlgebra.map embLin

theorem emb_ξ (i : Λ) : emb (ξ i) = ξ (some i) := by
  rw [emb, ξ, ExteriorAlgebra.map_apply_ι, ξ]; congr 1
  funext s; rcases s with (_ | j) | (_ | j) <;> simp [embLin, Pi.single_apply]

theorem emb_η (i : Λ) : emb (η i) = η (some i) := by
  rw [emb, η, ExteriorAlgebra.map_apply_ι, η]; congr 1
  funext s; rcases s with (_ | j) | (_ | j) <;> simp [embLin, Pi.single_apply]

theorem emb_z (i : Λ) : emb (z i) = z (some i) := by
  rw [z, map_sub, map_one, map_mul, emb_ξ, emb_η, z]

theorem emb_dot (i j : Λ) : emb (dot i j) = dot (some i) (some j) := by
  simp only [dot, map_sub, map_neg, map_mul, emb_ξ, emb_η, emb_z]

theorem proj_comp_embLin_inl (i : Λ) :
    (LinearMap.proj (R := ℝ) (φ := fun _ : Option Λ ⊕ Option Λ => ℝ) (Sum.inl (some i))) ∘ₗ
      embLin = LinearMap.proj (R := ℝ) (φ := fun _ : Λ ⊕ Λ => ℝ) (Sum.inl i) := by
  ext v; simp [embLin]

theorem proj_comp_embLin_inr (i : Λ) :
    (LinearMap.proj (R := ℝ) (φ := fun _ : Option Λ ⊕ Option Λ => ℝ) (Sum.inr (some i))) ∘ₗ
      embLin = LinearMap.proj (R := ℝ) (φ := fun _ : Λ ⊕ Λ => ℝ) (Sum.inr i) := by
  ext v; simp [embLin]

theorem proj_comp_embLin_inl_none :
    (LinearMap.proj (R := ℝ) (φ := fun _ : Option Λ ⊕ Option Λ => ℝ) (Sum.inl none)) ∘ₗ
      (embLin : Gen Λ →ₗ[ℝ] _) = 0 := by
  ext v; simp [embLin]

theorem proj_comp_embLin_inr_none :
    (LinearMap.proj (R := ℝ) (φ := fun _ : Option Λ ⊕ Option Λ => ℝ) (Sum.inr none)) ∘ₗ
      (embLin : Gen Λ →ₗ[ℝ] _) = 0 := by
  ext v; simp [embLin]

theorem dξ_emb (i : Λ) (X : A) : dξ (some i) (emb X) = emb (dξ i X) := by
  rw [dξ, emb, contractLeft_map', proj_comp_embLin_inl]; rfl

theorem dη_emb (i : Λ) (X : A) : dη (some i) (emb X) = emb (dη i X) := by
  rw [dη, emb, contractLeft_map', proj_comp_embLin_inr]; rfl

theorem dξ_none_emb (X : A) : dξ none (emb X) = 0 := by
  rw [dξ, emb, contractLeft_map', proj_comp_embLin_inl_none]
  simp

theorem dη_none_emb (X : A) : dη none (emb X) = 0 := by
  rw [dη, emb, contractLeft_map', proj_comp_embLin_inr_none]
  simp

theorem intStep_emb (i : Λ) (X : A) : intStep (some i) (emb X) = emb (intStep i X) := by
  rw [intStep_apply, intStep_apply, ← dη_emb, ← dξ_emb, map_mul emb, map_add emb, map_one emb,
    map_mul emb, emb_ξ, emb_η]

theorem inv'_emb (X : A) : inv' (emb X) = emb (inv' X) := inv'_map' embLin X

theorem berezin_emb (l : List Λ) (X : A) :
    berezin (l.map some) (emb X) = emb (berezin l X) := by
  induction l generalizing X with
  | nil => rfl
  | cons i l ih => rw [List.map_cons, berezin_cons, berezin_cons, intStep_emb, ih]

theorem algebraMapInv_emb (X : A) :
    ExteriorAlgebra.algebraMapInv (emb X) = ExteriorAlgebra.algebraMapInv X := by
  have : (ExteriorAlgebra.algebraMapInv : AO →ₐ[ℝ] ℝ).comp emb = ExteriorAlgebra.algebraMapInv := by
    refine ExteriorAlgebra.hom_ext (LinearMap.ext fun v => ?_)
    simp [emb, ExteriorAlgebra.map_apply_ι, ExteriorAlgebra.algebraMapInv]
  exact congrArg (fun f : A →ₐ[ℝ] ℝ => f X) this

/-- `∂_{η_v}∂_{ξ_v} z_v⁻¹ (ξ_v η_v Y) = Y` for `Y` not involving `ξ_v, η_v`. -/
theorem intStep_ξη_mul {V : Type*} [DecidableEq V] (v : V) {Y : Grassmann V}
    (h1 : dξ v Y = 0) (h2 : dη v Y = 0) : intStep v (ξ v * η v * Y) = Y := by
  rw [intStep_apply, ← mul_assoc, add_mul, one_mul, ξη_sq, add_zero, mul_assoc, dξ_mul, dξ_ξ,
    if_pos rfl, one_mul, dξ_mul, dξ_η, zero_mul, zero_add, inv'_η, h1, mul_zero, mul_zero,
    add_zero, dη_mul, dη_η, if_pos rfl, one_mul, inv'_η, h2, mul_zero, add_zero]

theorem univ_toList_perm :
    (univ : Finset (Option Λ)).toList.Perm (none :: (univ : Finset Λ).toList.map some) := by
  refine (List.perm_ext_iff_of_nodup (nodup_toList _) ?_).2 fun x => ?_
  · refine List.nodup_cons.2 ⟨by simp, (nodup_toList _).map (Option.some_injective _)⟩
  · rcases x with _ | x <;> simp

/-- `[ξ_g η_g emb(X)]_0^{Λ∪g} = [X]_0^Λ`. -/
theorem int0_ξη_emb (X : A) :
    int0 (ξ (none : Option Λ) * η none * emb X) = int0 X := by
  rw [int0, berezin_perm univ_toList_perm, berezin_cons,
    intStep_ξη_mul none (dξ_none_emb X) (dη_none_emb X), berezin_emb, algebraMapInv_emb, int0]

/-! ### The action on the extended graph -/

theorem sum_option {M : Type*} [AddCommMonoid M] (f : Option Λ → M) :
    ∑ p : Option Λ, f p = f none + ∑ i : Λ, f (some i) := Fintype.sum_option f

/-- `-H_{β,h} = ½ ∑_{ij} β_{ij} (1 + u_i·u_j) + ∑_i h_i ξ_i η_i`. -/
theorem neg_action_eq {V : Type*} [DecidableEq V] [Fintype V] (w : V → V → ℝ) (h : V → ℝ) :
    -action w h = (1 / 2 : ℝ) • ∑ i, ∑ j, w i j • (1 + dot i j) + ∑ i, h i • (ξ i * η i) := by
  have e1 : ∀ i j : V, dot i i - dot i j - dot j i + dot j j = (-2 : ℝ) • (1 + dot i j) := by
    intro i j
    have h1 : dot i i = -1 := by
      have := congrArg cv (Xc_self i); rw [coe_Xc, map_zero] at this
      exact eq_neg_of_add_eq_zero_right this
    have h2 : dot j j = -1 := by
      have := congrArg cv (Xc_self j); rw [coe_Xc, map_zero] at this
      exact eq_neg_of_add_eq_zero_right this
    rw [h1, h2, dot_comm j i]
    module
  have e2 : ∀ i : V, z i - 1 = -(ξ i * η i) := fun i => by simp [z]
  simp only [action, e1, e2]
  have h3 : ∑ i, ∑ j, w i j • ((-2 : ℝ) • (1 + dot i j)) =
      (-2 : ℝ) • ∑ i, ∑ j, w i j • (1 + dot i j) := by
    simp only [Finset.smul_sum, smul_comm (-2 : ℝ)]
  rw [h3, smul_smul]
  simp only [smul_neg, Finset.sum_neg_distrib]
  rw [neg_add, neg_neg, ← neg_smul]
  norm_num

/-- The ghost part of the extended action. -/
def ghostD (h : Λ → ℝ) : AO :=
  ∑ i : Λ, h i • ((1 + dot (some i) none) - ξ (some i) * η (some i))

/-- `-H^{Λ∪g}_{ghostW w h, 0} = emb(-H^Λ_{w,h}) + D` with `ξ_gη_g D = 0`. -/
theorem neg_action_ghost (w : Λ → Λ → ℝ) (h : Λ → ℝ) :
    -action (ghostW w h) (fun _ => 0) = emb (-action w h) + ghostD h := by
  have hd : ∀ i : Λ, dot none (some i) = dot (some i) none := fun i => dot_comm _ _
  have hL : -action (ghostW w h) (fun _ => 0) = ∑ i : Λ, h i • (1 + dot (some i) none) +
      (1 / 2 : ℝ) • ∑ i : Λ, ∑ j : Λ, w i j • (1 + dot (some i) (some j)) := by
    rw [neg_action_eq]
    simp only [sum_option, ghostW_none_none, ghostW_none_some, ghostW_some_none,
      ghostW_some_some, zero_smul, zero_add, Finset.sum_const_zero, add_zero, hd,
      Finset.sum_add_distrib, smul_add]
    module
  have hR : emb (-action w h) = (1 / 2 : ℝ) • ∑ i : Λ, ∑ j : Λ, w i j • (1 + dot (some i) (some j)) +
      ∑ i : Λ, h i • (ξ (some i) * η (some i)) := by
    rw [neg_action_eq]
    simp only [map_add, map_sum, map_smul, map_one, map_mul, emb_dot, emb_ξ, emb_η]
  rw [hL, hR, ghostD]
  simp only [smul_sub, Finset.sum_sub_distrib]
  abel

theorem ξη_mul_one_add_dot_ghost (i : Λ) :
    ξ (none : Option Λ) * η none * (1 + dot (some i) none) =
      ξ (none : Option Λ) * η none * (ξ (some i) * η (some i)) := by
  have := congrArg cv (pc_mul_Xc (none : Option Λ) (some i))
  simp only [map_mul, coe_pc, coe_Xc] at this
  rw [dot_comm]; exact this

theorem ξη_mul_ghostD (h : Λ → ℝ) : ξ (none : Option Λ) * η none * ghostD h = 0 := by
  rw [ghostD, Finset.mul_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [mul_smul_comm, mul_sub, ξη_mul_one_add_dot_ghost, sub_self, smul_zero]

theorem isNilpotent_emb_neg_action {w : Λ → Λ → ℝ} (hw : ∀ i j, w i j = w j i) (h : Λ → ℝ) :
    IsNilpotent (emb (-action w h)) :=
  (isNilpotent_neg_action w hw h).map emb

/-- `ξ_gη_g e^{-H^{Λ∪g}} = ξ_gη_g emb(e^{-H^Λ})`. -/
theorem ξη_mul_exp_ghost {w : Λ → Λ → ℝ} (hw : ∀ i j, w i j = w j i) (h : Λ → ℝ) :
    ξ (none : Option Λ) * η none * IsNilpotent.exp (-action (ghostW w h) (fun _ => 0)) =
      ξ (none : Option Λ) * η none * emb (IsNilpotent.exp (-action w h)) := by
  have hY := isNilpotent_emb_neg_action hw h
  have hO := isNilpotent_neg_action (ghostW w h) (ghostW_symm hw h) (fun _ => 0)
  have hev : inv' (emb (-action w h)) = emb (-action w h) := by
    rw [inv'_emb, inv'_action]
  have hc : Commute (emb (-action w h)) (ghostD h) := mul_comm_of_even hev _
  have hD : IsNilpotent (ghostD h) := by
    have : ghostD h = -action (ghostW w h) (fun _ => 0) - emb (-action w h) := by
      rw [neg_action_ghost]; abel
    rw [this]
    have hc2 : Commute (-action (ghostW w h) (fun _ => 0)) (emb (-action w h)) :=
      mul_comm_of_even (inv'_action _ _) _
    exact hc2.isNilpotent_sub hO hY
  obtain ⟨k, hk⟩ := hD
  have hk1 : ghostD h ^ (k + 1) = 0 := by rw [pow_succ, hk, zero_mul]
  have hPD : ξ (none : Option Λ) * η none * IsNilpotent.exp (ghostD h) = ξ none * η none := by
    rw [IsNilpotent.exp_eq_sum hk1, Finset.mul_sum, Finset.sum_range_succ', pow_zero,
      Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, mul_one, add_eq_right]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [mul_smul_comm, pow_succ', ← mul_assoc, ξη_mul_ghostD, zero_mul, smul_zero]
  have hPc : ∀ X : AO, ξ (none : Option Λ) * η none * X = X * (ξ none * η none) :=
    fun X => mul_comm_of_even (inv'_ξη _ _) X
  rw [neg_action_ghost, IsNilpotent.exp_add_of_commute hc hY ⟨k, hk⟩,
    ← IsNilpotent.map_exp (isNilpotent_neg_action w hw h) emb, ← mul_assoc, hPc, mul_assoc,
    hPD, ← hPc]

/-- **Pinning at the ghost.** If `Y` is `T`-invariant on `Λ ∪ {g}` and
`ξ_gη_g Y = ξ_gη_g emb(G)`, then `[Y]^{Λ∪g}_{ghostW w h, 0} = [G]^Λ_{w,h}` (any real `h`). -/
theorem expect_ghost {w : Λ → Λ → ℝ} (hw : ∀ i j, w i j = w j i) (h : Λ → ℝ) (Y : AO) (G : A)
    (hT : T univ Y = 0) (hY : ξ (none : Option Λ) * η none * Y = ξ none * η none * emb G) :
    expect (ghostW w h) (fun _ => 0) Y = expect w h G := by
  have hO := isNilpotent_neg_action (ghostW w h) (ghostW_symm hw h) (fun _ => 0)
  set E := IsNilpotent.exp (-action (ghostW w h) (fun _ => 0))
  have hTE : T univ (Y * E) = 0 := by
    rw [T_mul, hT, T_exp (inv'_action _ _) hO, T_action]
    simp
  have hPc : ∀ X : AO, ξ (none : Option Λ) * η none * X = X * (ξ none * η none) :=
    fun X => mul_comm_of_even (inv'_ξη _ _) X
  have key : ξ (none : Option Λ) * η none * (Y * E) =
      ξ none * η none * emb (G * IsNilpotent.exp (-action w h)) := by
    calc ξ (none : Option Λ) * η none * (Y * E) = (ξ none * η none * Y) * E := (mul_assoc _ _ _).symm
      _ = (ξ none * η none * emb G) * E := by rw [hY]
      _ = emb G * (ξ none * η none * E) := by rw [hPc (emb G), mul_assoc]
      _ = emb G * (ξ none * η none * emb (IsNilpotent.exp (-action w h))) := by
          rw [ξη_mul_exp_ghost hw h]
      _ = _ := by rw [← mul_assoc, ← hPc (emb G), mul_assoc, map_mul]
  rw [expect, int0, berezin_pin (fun i _ => Finset.mem_toList.2 (mem_univ i)) (mem_univ none) hTE,
    key, ← int0, int0_ξη_emb, expect]

/-! ### Consequences of pinning -/

/-- The normalising constants agree: `Z^{forest}_{ghostW w h} = [1]_{w,h}` (any real `h`). -/
theorem Zforest_ghostW {w : Λ → Λ → ℝ} (hw : ∀ i j, w i j = w j i) (h : Λ → ℝ) :
    Zforest (ghostW w h) (ghostW_symm hw h) = expect w h 1 := by
  rw [← expect_one_eq_Z]
  exact expect_ghost hw h 1 1 (T_one _) (by rw [map_one])

/-- **`Z_{β,h} > 0`** for non-negative symmetric `β` and non-negative `h`. -/
theorem expect_one_pos {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j)
    {h : Λ → ℝ} (hh : ∀ i, 0 ≤ h i) : 0 < expect β h 1 := by
  rw [← Zforest_ghostW hβ h]
  exact Zforest_pos _ (ghostW_nonneg hβ0 hh)

theorem T_one_add_dot {V : Type*} [DecidableEq V] [Fintype V] (a b : V) :
    T univ (1 + dot a b) = 0 := by
  have := T_Xc (s := (univ : Finset V)) (mem_univ a) (mem_univ b)
  rwa [coe_Xc] at this

theorem expect_ghost_one_add_dot_g {w : Λ → Λ → ℝ} (hw : ∀ i j, w i j = w j i) (h : Λ → ℝ)
    (a : Λ) : expect (ghostW w h) (fun _ => 0) (1 + dot (some a) none) = expect w h (ξ a * η a) :=
  expect_ghost hw h _ _ (T_one_add_dot _ _) (by
    rw [map_mul, emb_ξ, emb_η, ξη_mul_one_add_dot_ghost])

theorem expect_ghost_one_add_dot {w : Λ → Λ → ℝ} (hw : ∀ i j, w i j = w j i) (h : Λ → ℝ)
    (a x : Λ) : expect (ghostW w h) (fun _ => 0) (1 + dot (some a) (some x)) =
      expect w h (1 + dot a x) :=
  expect_ghost hw h _ _ (T_one_add_dot _ _) (by rw [map_add, map_one, emb_dot])

/-- `P[a ↔ b] = -⟨u_a · u_b⟩` at zero field (from `cor_spin_conn`). -/
theorem arborealProb_reach_eq {V : Type*} [DecidableEq V] [Fintype V] {β : V → V → ℝ}
    (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j) (a b : V) :
    arborealProb β hβ (fun F => F.Reachable a b) = -avg β 0 (dot a b) :=
  (cor_spin_conn hβ hβ0 a b).1.trans (cor_spin_conn hβ hβ0 a b).2.1

/-- **`e:zforest`**: `P_{β,h}[a ↔ g] = ⟨z_a⟩_{β,h}`. -/
theorem arborealProb_ghost_zforest {w : Λ → Λ → ℝ} (hw : ∀ i j, w i j = w j i)
    (hw0 : ∀ i j, 0 ≤ w i j) {h : Λ → ℝ} (hh : ∀ i, 0 ≤ h i) (a : Λ) :
    arborealProb (ghostW w h) (ghostW_symm hw h) (fun F => F.Reachable (some a) none) =
      avg w h (z a) := by
  rw [arborealProb_reach_eq (ghostW_symm hw h) (ghostW_nonneg hw0 hh), avg, avg]
  have e1 : expect (ghostW w h) 0 (dot (some a) none) = expect w h (ξ a * η a) - expect w h 1 := by
    have := expect_ghost_one_add_dot_g hw h a
    rw [expect_add] at this
    have h1 : expect (ghostW w h) (fun _ => 0) 1 = expect w h 1 := by
      rw [← Zforest_ghostW hw h, ← expect_one_eq_Z]; rfl
    show expect (ghostW w h) (fun _ => 0) (dot (some a) none) = _
    linarith
  have e2 : expect (ghostW w h) 0 1 = expect w h 1 := by
    rw [expect_one_eq_Z _ (ghostW_symm hw h), Zforest_ghostW hw h]
  rw [e1, e2, z, expect_sub]
  ring

/-- **`e:u0uxforest`**: `P_{β,h}[a ↔ x] = -⟨u_a · u_x⟩_{β,h}` (connections in `Λ ∪ {g}`). -/
theorem arborealProb_ghost_uu {w : Λ → Λ → ℝ} (hw : ∀ i j, w i j = w j i)
    (hw0 : ∀ i j, 0 ≤ w i j) {h : Λ → ℝ} (hh : ∀ i, 0 ≤ h i) (a x : Λ) :
    arborealProb (ghostW w h) (ghostW_symm hw h) (fun F => F.Reachable (some a) (some x)) =
      -avg w h (dot a x) := by
  rw [arborealProb_reach_eq (ghostW_symm hw h) (ghostW_nonneg hw0 hh), avg, avg]
  have e2 : expect (ghostW w h) 0 1 = expect w h 1 := by
    rw [expect_one_eq_Z _ (ghostW_symm hw h), Zforest_ghostW hw h]
  have e1 : expect (ghostW w h) 0 (dot (some a) (some x)) = expect w h (dot a x) := by
    have := expect_ghost_one_add_dot hw h a x
    rw [expect_add, expect_add] at this
    have h1 : expect (ghostW w h) (fun _ => 0) 1 = expect w h 1 := e2
    show expect (ghostW w h) (fun _ => 0) (dot (some a) (some x)) = _
    linarith
  rw [e1, e2]

/-! ### Shifting the field: `z_a e^{-H_h} = e^{-H_{h - 1_a}}` -/

theorem neg_action_shift (w : Λ → Λ → ℝ) (h : Λ → ℝ) (a : Λ) :
    -action w (h - Pi.single a 1) = -action w h + -(ξ a * η a) := by
  rw [neg_action_eq, neg_action_eq]
  simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
  have hs : ∑ i, (Pi.single a (1 : ℝ) : Λ → ℝ) i • (ξ i * η i) = ξ a * η a := by
    rw [Finset.sum_eq_single a (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]
    simp
  rw [hs]
  abel

theorem exp_neg_ξη (a : Λ) : IsNilpotent.exp (-(ξ a * η a)) = z a := by
  have hsq : (-(ξ a * η a)) ^ 2 = 0 := by rw [neg_sq, pow_two, ξη_sq]
  rw [IsNilpotent.exp_eq_sum hsq]
  simp [Finset.sum_range_succ, z, sub_eq_add_neg]

/-- `[z_a F]_{β,h} = [F]_{β, h - 1_a}`. -/
theorem expect_z_mul {w : Λ → Λ → ℝ} (hw : ∀ i j, w i j = w j i) (h : Λ → ℝ) (a : Λ) (F : A) :
    expect w h (z a * F) = expect w (h - Pi.single a 1) F := by
  have hn := isNilpotent_neg_action w hw h
  have hq : IsNilpotent (-(ξ a * η a)) := ⟨2, by rw [neg_sq, pow_two, ξη_sq]⟩
  have hc : Commute (-action w h) (-(ξ a * η a)) := mul_comm_of_even (inv'_action _ _) _
  rw [expect, expect, neg_action_shift, IsNilpotent.exp_add_of_commute hc hn hq, exp_neg_ξη,
    mul_comm_of_even (inv'_z a) F, mul_assoc,
    mul_comm_of_even (inv'_z a) (IsNilpotent.exp (-action w h))]

/-! ### Forest sums over predicates -/

section FSum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `{F : P F}` as a finset (with a fixed classical decidability instance). -/
def fset (P : SimpleGraph V → Prop) : Finset (SimpleGraph V) := by
  classical exact Finset.univ.filter P

@[simp] theorem mem_fset {P : SimpleGraph V → Prop} {F : SimpleGraph V} : F ∈ fset P ↔ P F := by
  unfold fset; simp

/-- `∑_{F : P F} ∏_{e ∈ F} β_e`. -/
def fsum (β : V → V → ℝ) (hβ : ∀ i j, β i j = β j i) (P : SimpleGraph V → Prop) : ℝ :=
  ∑ F ∈ fset P, forestWeight β hβ F

theorem arborealProb_eq_fsum {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i)
    (P : SimpleGraph V → Prop) :
    arborealProb β hβ P = fsum β hβ (fun F => F.IsAcyclic ∧ P F) / Zforest β hβ := by
  rw [arborealProb, fsum]
  congr 1
  exact Finset.sum_congr (by ext F; simp) fun _ _ => rfl

theorem Zforest_eq_fsum {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) :
    Zforest β hβ = fsum β hβ (fun F => F.IsAcyclic) := by
  rw [Zforest, fsum]
  exact Finset.sum_congr (by ext F; simp) fun _ _ => rfl

theorem fsum_add_not {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) (P Q : SimpleGraph V → Prop) :
    fsum β hβ (fun F => P F ∧ Q F) + fsum β hβ (fun F => P F ∧ ¬Q F) = fsum β hβ P := by
  simp only [fsum]
  rw [← Finset.sum_union]
  · exact Finset.sum_congr (by ext F; simp; tauto) fun _ _ => rfl
  · rw [Finset.disjoint_left]; intro F h1 h2; simp at h1 h2; exact h2.2 h1.2

/-- Linearity: `∑_{F : P} (∑_k c_k [Q_k F]) w(F)`, stated through indicators. -/
theorem fsum_eq_sum_ite {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) (P Q : SimpleGraph V → Prop) :
    fsum β hβ (fun F => P F ∧ Q F) =
      ∑ F ∈ fset P, (if Q F then forestWeight β hβ F else 0) := by
  classical
  rw [fsum, ← Finset.sum_filter]
  exact Finset.sum_congr (by ext F; simp) fun _ _ => rfl

end FSum

/-! ### The edge-insertion bijection -/

section EdgeIns

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem E_deleteEdges (F : SimpleGraph V) (e₀ : Sym2 V) :
    E (F.deleteEdges {e₀}) = (E F).erase e₀ := by
  ext e; simp [SimpleGraph.edgeSet_deleteEdges, and_comm]

theorem sup_edge_deleteEdges {F : SimpleGraph V} {u v : V} (h : ¬F.Adj u v) :
    (F ⊔ SimpleGraph.edge u v).deleteEdges {s(u, v)} = F := by
  ext a b
  simp only [SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj,
    Set.mem_singleton_iff, Sym2.eq_iff]
  constructor
  · rintro ⟨h1 | ⟨h2, _⟩, h3⟩
    · exact h1
    · exact absurd h2 h3
  · intro hab
    refine ⟨Or.inl hab, ?_⟩
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact h hab
    · exact h hab.symm

theorem acyclic_sup_edge_iff {F : SimpleGraph V} {u v : V} (huv : u ≠ v) (h : ¬F.Adj u v) :
    (F ⊔ SimpleGraph.edge u v).IsAcyclic ↔ F.IsAcyclic ∧ ¬F.Reachable u v := by
  rw [SimpleGraph.isAcyclic_sup_fromEdgeSet_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun hr => (h2 hr).elim huv h⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun hr => absurd hr h2⟩

/-- **Edge insertion**: forests containing the edge `uv` correspond to forests in which `u` and
`v` are not connected. -/
theorem sum_edge_insert {u v : V} (huv : u ≠ v) (Q : SimpleGraph V → Prop)
    (g : SimpleGraph V → ℝ) :
    ∑ F ∈ fset (fun F => F.IsAcyclic ∧ F.Adj u v ∧ Q F), g (F.deleteEdges {s(u, v)}) =
      ∑ F ∈ fset (fun F => F.IsAcyclic ∧ ¬F.Reachable u v ∧ Q (F ⊔ SimpleGraph.edge u v)),
        g F := by
  have hnadj : ∀ F : SimpleGraph V, ¬(F.deleteEdges {s(u, v)}).Adj u v := by
    intro F; simp [SimpleGraph.deleteEdges_adj]
  refine Finset.sum_nbij' (fun F => F.deleteEdges {s(u, v)}) (fun F => F ⊔ SimpleGraph.edge u v)
    ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · intro F hF
    simp only [Finset.mem_coe, mem_fset] at hF ⊢
    have hS := deleteEdges_sup_edge hF.2.1
    have hac := hF.1
    rw [← hS, acyclic_sup_edge_iff huv (hnadj F)] at hac
    exact ⟨hac.1, hac.2, by rw [hS]; exact hF.2.2⟩
  · intro F hF
    simp only [Finset.mem_coe, mem_fset] at hF ⊢
    have hna : ¬F.Adj u v := fun ha => hF.2.1 ha.reachable
    refine ⟨(acyclic_sup_edge_iff huv hna).2 ⟨hF.1, hF.2.1⟩, ?_, hF.2.2⟩
    rw [SimpleGraph.sup_adj, SimpleGraph.edge_adj]
    exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, huv⟩
  · intro F hF
    simp only [Finset.mem_coe, mem_fset] at hF
    exact deleteEdges_sup_edge hF.2.1
  · intro F hF
    simp only [Finset.mem_coe, mem_fset] at hF
    exact sup_edge_deleteEdges fun ha => hF.2.1 ha.reachable

/-- Lowering one edge weight by `1`. -/
theorem prod_shift (S : Finset (Sym2 V)) (ω ω' : Sym2 V → ℝ) (e₀ : Sym2 V)
    (hω : ∀ e, e ≠ e₀ → ω' e = ω e) (h0 : ω' e₀ = ω e₀ - 1) :
    ∏ e ∈ S, ω' e = ∏ e ∈ S, ω e - if e₀ ∈ S then ∏ e ∈ S.erase e₀, ω e else 0 := by
  split_ifs with he
  · rw [← Finset.mul_prod_erase S ω' he, ← Finset.mul_prod_erase S ω he, h0,
      Finset.prod_congr rfl fun e he' => hω e (Finset.ne_of_mem_erase he')]
    ring
  · rw [sub_zero]
    exact Finset.prod_congr rfl fun e he' => hω e fun h => he (h ▸ he')

end EdgeIns

/-! ### Shifting the ghost weights -/

theorem lift_ghostW_shift_ne {w : Λ → Λ → ℝ} (hw : ∀ i j, w i j = w j i) (h : Λ → ℝ) (a : Λ)
    (e : Sym2 (Option Λ)) (he : e ≠ s(some a, none)) :
    Sym2.lift ⟨ghostW w (h - Pi.single a 1), ghostW_symm hw _⟩ e =
      Sym2.lift ⟨ghostW w h, ghostW_symm hw h⟩ e := by
  induction e using Sym2.ind with
  | h p q =>
    rcases p with _ | i <;> rcases q with _ | j
    · rfl
    · have : j ≠ a := by rintro rfl; exact he Sym2.eq_swap
      simp [Pi.single_apply, this]
    · have : i ≠ a := by rintro rfl; exact he rfl
      simp [Pi.single_apply, this]
    · rfl

theorem lift_ghostW_shift_eq {w : Λ → Λ → ℝ} (hw : ∀ i j, w i j = w j i) (h : Λ → ℝ) (a : Λ) :
    Sym2.lift ⟨ghostW w (h - Pi.single a 1), ghostW_symm hw _⟩ s(some a, none) =
      Sym2.lift ⟨ghostW w h, ghostW_symm hw h⟩ s(some a, none) - 1 := by
  simp

/-- Lowering the field at `a` by `1`: for any predicate `P`,
`∑_{F : P} w_{h - 1_a}(F) = ∑_{F : P} w_h(F) - ∑_{F : a ↮ g, P(F + ag)} w_h(F)`. -/
theorem fsum_shift {w : Λ → Λ → ℝ} (hw : ∀ i j, w i j = w j i) (h : Λ → ℝ) (a : Λ)
    (P : SimpleGraph (Option Λ) → Prop) :
    fsum (ghostW w (h - Pi.single a 1)) (ghostW_symm hw _) (fun F => F.IsAcyclic ∧ P F) =
      fsum (ghostW w h) (ghostW_symm hw h) (fun F => F.IsAcyclic ∧ P F) -
        fsum (ghostW w h) (ghostW_symm hw h) (fun F => F.IsAcyclic ∧
          ¬F.Reachable (some a) none ∧ P (F ⊔ SimpleGraph.edge (some a) none)) := by
  set ω := Sym2.lift ⟨ghostW w h, ghostW_symm hw h⟩
  have hstep : ∀ F : SimpleGraph (Option Λ),
      forestWeight (ghostW w (h - Pi.single a 1)) (ghostW_symm hw _) F =
        forestWeight (ghostW w h) (ghostW_symm hw h) F -
          if F.Adj (some a) none then ∏ e ∈ E (F.deleteEdges {s(some a, none)}), ω e else 0 := by
    intro F
    rw [forestWeight_eq, forestWeight_eq, prod_shift (E F) ω _ s(some a, none)
      (lift_ghostW_shift_ne hw h a) (lift_ghostW_shift_eq hw h a), E_deleteEdges]
    congr 2
    simp
  simp only [fsum]
  rw [Finset.sum_congr rfl fun F _ => hstep F, Finset.sum_sub_distrib]
  congr 1
  have := sum_edge_insert (u := some a) (v := none) (Option.some_ne_none a) P
    (fun F => ∏ e ∈ E F, ω e)
  rw [Finset.sum_congr rfl fun F _ => forestWeight_eq _ _ F, ← this, ← Finset.sum_filter]
  exact Finset.sum_congr (by ext F; simp; tauto) fun _ _ => rfl

/-! ### The two-point functions of `z` -/

theorem fsum_ghost_eq_prob {w : Λ → Λ → ℝ} (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    {h : Λ → ℝ} (hh : ∀ i, 0 ≤ h i) (Q : SimpleGraph (Option Λ) → Prop) :
    fsum (ghostW w h) (ghostW_symm hw h) (fun F => F.IsAcyclic ∧ Q F) =
      arborealProb (ghostW w h) (ghostW_symm hw h) Q * expect w h 1 := by
  rw [arborealProb_eq_fsum, ← Zforest_ghostW hw h,
    div_mul_cancel₀ _ (Zforest_pos (ghostW_symm hw h) (ghostW_nonneg hw0 hh)).ne']

/-- `⟨z_a z_x⟩_{β,h} = 1 - P[a ↮ g] - P[x ↮ g] + P[a ↮ g, x ↮ g, a ↮ x]` for `a ≠ x`. -/
theorem avg_zz_ghost {w : Λ → Λ → ℝ} (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    {h : Λ → ℝ} (hh : ∀ i, 0 ≤ h i) (a x : Λ) :
    avg w h (z a * z x) = 1 - arborealProb (ghostW w h) (ghostW_symm hw h)
        (fun F => ¬F.Reachable (some a) none) -
      arborealProb (ghostW w h) (ghostW_symm hw h) (fun F => ¬F.Reachable (some x) none) +
      arborealProb (ghostW w h) (ghostW_symm hw h) (fun F => ¬F.Reachable (some a) none ∧
        ¬F.Reachable (some x) none ∧ ¬F.Reachable (some a) (some x)) := by
  have hZ := expect_one_pos hw hw0 hh
  have e1 : expect w h (z a * z x) = expect w (h - Pi.single a 1 - Pi.single x 1) 1 := by
    rw [expect_z_mul hw, ← mul_one (z x), expect_z_mul hw]
  have z1 := fsum_shift hw (h - Pi.single a 1) x (fun _ => True)
  have z2 := fsum_shift hw h a (fun _ => True)
  have z3 := fsum_shift hw h a (fun F => ¬F.Reachable (some x) none)
  simp only [and_true] at z1 z2
  have c3 : (fun F : SimpleGraph (Option Λ) => F.IsAcyclic ∧ ¬F.Reachable (some a) none ∧
      ¬(F ⊔ SimpleGraph.edge (some a) none).Reachable (some x) none) =
      (fun F => F.IsAcyclic ∧ (¬F.Reachable (some a) none ∧ ¬F.Reachable (some x) none ∧
        ¬F.Reachable (some a) (some x))) := by
    funext F
    apply propext
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, fun hx => h3 (hx.mono le_sup_left), fun hax' => h3 ?_⟩
      exact (hax'.symm.mono le_sup_left).trans
        (SimpleGraph.Adj.reachable (by simp [SimpleGraph.edge_adj]))
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨h1, h2, fun hr => ?_⟩
      rcases reachable_sup_edge hr with h5 | ⟨h5, _⟩ | ⟨h5, _⟩
      · exact h3 h5
      · exact h4 h5.symm
      · exact h3 h5
  rw [c3] at z3
  have hZ0 : expect w (h - Pi.single a 1 - Pi.single x 1) 1 =
      fsum (ghostW w (h - Pi.single a 1 - Pi.single x 1)) (ghostW_symm hw _)
        (fun F => F.IsAcyclic) := by
    rw [← Zforest_ghostW hw, Zforest_eq_fsum]
  rw [avg, e1, hZ0, z1, z2, z3, fsum_ghost_eq_prob hw hw0 hh, fsum_ghost_eq_prob hw hw0 hh,
    fsum_ghost_eq_prob hw hw0 hh, ← Zforest_eq_fsum, Zforest_ghostW hw]
  field_simp
  ring

/-- `P[a ↔ g] + P[a ↮ g] = 1`. -/
theorem arborealProb_not {V : Type*} [Fintype V] [DecidableEq V] {β : V → V → ℝ}
    (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j) (Q : SimpleGraph V → Prop) :
    arborealProb β hβ (fun F => ¬Q F) = 1 - arborealProb β hβ Q := by
  have hZ := Zforest_pos hβ hβ0
  rw [arborealProb_eq_fsum, arborealProb_eq_fsum, eq_sub_iff_add_eq, ← add_div,
    add_comm, fsum_add_not hβ (fun F => F.IsAcyclic) Q, ← Zforest_eq_fsum, div_self hZ.ne']

/-- **The `σ` relation**:
`⟨z_a z_x⟩ - ⟨z_a⟩⟨z_x⟩ = P[a ↮ g, x ↮ g, a ↮ x] - P[a ↮ g] P[x ↮ g]`. -/
theorem sigma_ghost {w : Λ → Λ → ℝ} (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    {h : Λ → ℝ} (hh : ∀ i, 0 ≤ h i) (a x : Λ) :
    avg w h (z a * z x) - avg w h (z a) * avg w h (z x) =
      arborealProb (ghostW w h) (ghostW_symm hw h) (fun F => ¬F.Reachable (some a) none ∧
          ¬F.Reachable (some x) none ∧ ¬F.Reachable (some a) (some x)) -
        arborealProb (ghostW w h) (ghostW_symm hw h) (fun F => ¬F.Reachable (some a) none) *
          arborealProb (ghostW w h) (ghostW_symm hw h) (fun F => ¬F.Reachable (some x) none) := by
  rw [avg_zz_ghost hw hw0 hh, ← arborealProb_ghost_zforest hw hw0 hh,
    ← arborealProb_ghost_zforest hw hw0 hh,
    arborealProb_not _ (ghostW_nonneg hw0 hh) (fun F => F.Reachable (some a) none),
    arborealProb_not _ (ghostW_nonneg hw0 hh) (fun F => F.Reachable (some x) none)]
  ring

/-! ### Reachability through the ghost -/

theorem base_reachable_of_walk (F : SimpleGraph (Option Λ)) {u v : Option Λ} (p : F.Walk u v) :
    none ∉ p.support → ∀ a b : Λ, u = some a → v = some b → (base F).Reachable a b := by
  induction p with
  | nil =>
    intro _ a b h1 h2
    rw [h1] at h2
    cases Option.some_injective _ h2
    exact SimpleGraph.Reachable.rfl
  | @cons u w v hadj p ih =>
    intro hn a b h1 h2
    rw [SimpleGraph.Walk.support_cons, List.mem_cons, not_or] at hn
    obtain ⟨c, hc⟩ : ∃ c, w = some c := by
      rcases hw' : w with _ | c
      · exact absurd (hw' ▸ p.start_mem_support) hn.2
      · exact ⟨c, rfl⟩
    have hr := ih hn.2 c b hc h2
    subst h1 hc
    exact (SimpleGraph.Adj.reachable (G := base F) hadj).trans hr

/-- The embedding `base F →g F`. -/
def baseHom (F : SimpleGraph (Option Λ)) : base F →g F := ⟨some, fun h => h⟩

/-- `a ↔ x` in `Λ ∪ {g}` iff `a ↔ x` in `Λ` or both `a ↔ g` and `x ↔ g`. -/
theorem reachable_some_iff (F : SimpleGraph (Option Λ)) (a x : Λ) :
    F.Reachable (some a) (some x) ↔
      (base F).Reachable a x ∨ (F.Reachable (some a) none ∧ F.Reachable (some x) none) := by
  constructor
  · rintro ⟨p⟩
    by_cases hn : none ∈ p.support
    · exact Or.inr ⟨⟨p.takeUntil none hn⟩, ⟨(p.dropUntil none hn).reverse⟩⟩
    · exact Or.inl (base_reachable_of_walk F p hn a x rfl rfl)
  · rintro (h | ⟨h1, h2⟩)
    · exact h.map (baseHom F)
    · exact h1.trans h2.symm

/-! ### `e:xietaforest` -/

theorem avg_ξη_add {w : Λ → Λ → ℝ} (hw : ∀ i j, w i j = w j i) (h : Λ → ℝ) (a x : Λ) :
    -avg w h (dot a x) = 2 * avg w h (ξ a * η x) + avg w h (z a * z x) := by
  rw [avg, avg, avg, dot, expect_sub, expect_sub, expect_neg, expect_ξη_symm w hw h x a]
  ring

/-- **`e:xietaforest`**: `P_{β,h}[a ↔ x, a ↮ g] = ⟨ξ_a η_x⟩_{β,h}` (`a ↔ x` in `Λ`). -/
theorem arborealProb_ghost_xieta {w : Λ → Λ → ℝ} (hw : ∀ i j, w i j = w j i)
    (hw0 : ∀ i j, 0 ≤ w i j) {h : Λ → ℝ} (hh : ∀ i, 0 ≤ h i) (a x : Λ) :
    arborealProb (ghostW w h) (ghostW_symm hw h)
        (fun F => (base F).Reachable a x ∧ ¬F.Reachable (some a) none) =
      avg w h (ξ a * η x) := by
  set β := ghostW w h
  have hβ := ghostW_symm hw h
  have hZ := Zforest_pos hβ (ghostW_nonneg hw0 hh)
  set fw := forestWeight β hβ
  have key : ∀ F : SimpleGraph (Option Λ),
      (if F.Reachable (some a) (some x) then fw F else 0) - fw F +
          (if ¬F.Reachable (some a) none then fw F else 0) +
          (if ¬F.Reachable (some x) none then fw F else 0) -
          (if ¬F.Reachable (some a) none ∧ ¬F.Reachable (some x) none ∧
            ¬F.Reachable (some a) (some x) then fw F else 0) =
        2 * (if (base F).Reachable a x ∧ ¬F.Reachable (some a) none then fw F else 0) := by
    intro F
    have rs := reachable_some_iff F a x
    have hB : (base F).Reachable a x →
        (F.Reachable (some a) none ↔ F.Reachable (some x) none) := fun hb =>
      ⟨fun ha => (hb.map (baseHom F)).symm.trans ha, fun hx => (hb.map (baseHom F)).trans hx⟩
    simp only [rs]
    by_cases hb : (base F).Reachable a x
    · have hAX := hB hb
      by_cases hA : F.Reachable (some a) none
      · have hX := hAX.1 hA
        simp [hA, hX, hb]
      · have hX : ¬F.Reachable (some x) none := fun hx => hA (hAX.2 hx)
        simp [hA, hX, hb]; ring
    · by_cases hA : F.Reachable (some a) none <;> by_cases hX : F.Reachable (some x) none <;>
        simp [hA, hX, hb]
  have hsum : fsum β hβ (fun F => F.IsAcyclic ∧ F.Reachable (some a) (some x)) -
      fsum β hβ (fun F => F.IsAcyclic) +
      fsum β hβ (fun F => F.IsAcyclic ∧ ¬F.Reachable (some a) none) +
      fsum β hβ (fun F => F.IsAcyclic ∧ ¬F.Reachable (some x) none) -
      fsum β hβ (fun F => F.IsAcyclic ∧ (¬F.Reachable (some a) none ∧
        ¬F.Reachable (some x) none ∧ ¬F.Reachable (some a) (some x))) =
      2 * fsum β hβ (fun F => F.IsAcyclic ∧ ((base F).Reachable a x ∧
        ¬F.Reachable (some a) none)) := by
    rw [fsum_eq_sum_ite, fsum_eq_sum_ite, fsum_eq_sum_ite, fsum_eq_sum_ite, fsum_eq_sum_ite,
      fsum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun F _ => by convert key F
  have e1 := arborealProb_ghost_uu hw hw0 hh a x
  have e2 := avg_ξη_add hw h a x
  have e3 := avg_zz_ghost hw hw0 hh a x
  have e4 : avg w h (ξ a * η x) =
      (arborealProb β hβ (fun F => F.Reachable (some a) (some x)) - avg w h (z a * z x)) / 2 := by
    rw [e1]; linarith
  rw [e4, e3]
  simp only [arborealProb_eq_fsum]
  rw [Zforest_eq_fsum] at hZ ⊢
  field_simp
  linarith [hsum]

/-! ### `prop:h02-forest` -/

/-- **Proposition `prop:h02-forest`** (for a general finite graph given by symmetric
non-negative weights `w`, and a constant field `h ≥ 0`; `g = none` is the ghost vertex and the
arboreal gas lives on `Λ ∪ {g}` with weights `ghostW w h`):
* `e:zforest`: `P[a ↔ g] = ⟨z_a⟩`;
* `e:xietaforest`: `P[a ↔ x, a ↮ g] = ⟨ξ_a η_x⟩`;
* `e:u0uxforest`: `P[a ↔ x] = -⟨u_a·u_x⟩` (in `Λ ∪ {g}`, so this is
  `P[a ↔ x in Λ] + P[a ↮_Λ x, a ↔ g, x ↔ g]`, see `reachable_some_iff`);
* the normalising constants agree;
* the `σ` relation `⟨z_a z_x⟩ - ⟨z_a⟩⟨z_x⟩ = P[a ↮ g, x ↮ g, a ↮ x] - P[a ↮ g] P[x ↮ g]`. -/
theorem prop_h02_forest {w : Λ → Λ → ℝ} (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (h : ℝ) (hh : 0 ≤ h) (a x : Λ) :
    arborealProb (ghostW w (fun _ => h)) (ghostW_symm hw _)
        (fun F => F.Reachable (some a) none) = avg w (fun _ => h) (z a) ∧
    arborealProb (ghostW w (fun _ => h)) (ghostW_symm hw _)
        (fun F => (base F).Reachable a x ∧ ¬F.Reachable (some a) none) =
      avg w (fun _ => h) (ξ a * η x) ∧
    arborealProb (ghostW w (fun _ => h)) (ghostW_symm hw _)
        (fun F => F.Reachable (some a) (some x)) = -avg w (fun _ => h) (dot a x) ∧
    Zforest (ghostW w (fun _ => h)) (ghostW_symm hw _) = expect w (fun _ => h) 1 ∧
    avg w (fun _ => h) (z a * z x) - avg w (fun _ => h) (z a) * avg w (fun _ => h) (z x) =
      arborealProb (ghostW w (fun _ => h)) (ghostW_symm hw _) (fun F =>
          ¬F.Reachable (some a) none ∧ ¬F.Reachable (some x) none ∧
            ¬F.Reachable (some a) (some x)) -
        arborealProb (ghostW w (fun _ => h)) (ghostW_symm hw _)
            (fun F => ¬F.Reachable (some a) none) *
          arborealProb (ghostW w (fun _ => h)) (ghostW_symm hw _)
            (fun F => ¬F.Reachable (some x) none) :=
  ⟨arborealProb_ghost_zforest hw hw0 (fun _ => hh) a,
    arborealProb_ghost_xieta hw hw0 (fun _ => hh) a x,
    arborealProb_ghost_uu hw hw0 (fun _ => hh) a x,
    Zforest_ghostW hw _,
    sigma_ghost hw hw0 (fun _ => hh) a x⟩

end

end H02

end
