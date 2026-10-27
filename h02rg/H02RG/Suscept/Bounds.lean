import Suscept.PropZNN

/-!
# Proposition `prop:ZNN`: the bounds `e:ZNN-bd`

`|F⁰| = |ε F| ≤ ‖F‖_{T_j(ℓ)}` and `|F²| ≤ ℓ^{-2} ‖F‖_{T_j(ℓ)}` (`norm_c2_le`), via the test function
`g_{(x,+),(y,-)} = 1`, `g_{(x,-),(y,+)} = -1` (antisymmetrised), which has `‖g‖_{Φ_j(ℓ)} ≤ ℓ^{-2}`
and `⟨F, g⟩ = F²`.  Since `Λ_N` is a single connected `N`-polymer with one block,
`‖K_N(Λ)‖_{T_N(ℓ_N)} ≤ ‖K_N‖_N` (`Tj_le_Knorm`).  Hence `|k_N^0| ≤ ‖K_N‖_N` and
`|k_N^2| ≤ ℓ_N^{-2} ‖K_N‖_N` (`kN0_le`, `kN2_le`).
-/

namespace Suscept

noncomputable section

open Finset Grassmann Loc FRD Step Flow

variable {d L : ℕ} [NeZero L]

/-- The spin pattern of the test function for `F²`. -/
def gsp {X : Type*} (z : Fin 2 → Sf X) : ℂ :=
  if (z 0).2 = 1 ∧ (z 1).2 = -1 then 1 else if (z 0).2 = -1 ∧ (z 1).2 = 1 then -1 else 0

theorem norm_gsp_le {X : Type*} (z : Fin 2 → Sf X) : ‖gsp z‖ ≤ 1 := by
  unfold gsp; split_ifs <;> simp

section General

variable {X : Type*} [DecidableEq X] [Fintype X] {E : Type*} [Fintype E] [DecidableEq E]
  [AddAction (E → ℕ) X] {p : ℕ} {h ℓ : ℝ}

theorem pair_gsp (F : Grassmann.N X) : pair F (single 2 gsp) = c2 F := by
  rw [pair_single', sum_fin_two]
  simp only [Fintype.sum_prod_type, sum_units_int, gsp]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  simp only [show ((1 : ℤˣ) = -1) = False by decide, show ((-1 : ℤˣ) = 1) = False by decide,
    and_false, false_and, and_self, if_true, if_false, mul_zero, mul_one, add_zero, zero_add,
    mul_neg]
  have hswap : ∀ x y : X, coeff F ![((x, -1) : Sf X), (y, 1)] = -coeff F ![((y, 1) : Sf X), (x, -1)] := by
    intro x y
    have := coeff_perm F ![((y, 1) : Sf X), (x, -1)] (Equiv.swap 0 1)
    have e : (![((y, 1) : Sf X), (x, -1)] ∘ Equiv.swap 0 1) = ![((x, -1) : Sf X), (y, 1)] := by
      funext i; fin_cases i <;> rfl
    rw [e] at this
    rw [this]; simp
  simp only [hswap, neg_neg, sum_add_distrib]
  rw [Finset.sum_comm (f := fun x y => coeff F ![((y, 1) : Sf X), (x, -1)]), c2]
  norm_num
  ring

theorem phiNorm_gsp_le (hh : 0 < h) (hℓ : 0 < ℓ) :
    phiNorm E p h ℓ (single 2 (gsp (X := X))) ≤ ENNReal.ofReal (ℓ⁻¹ ^ 2) := by
  refine phiNorm_single_le' (by positivity) fun z α _ => ?_
  by_cases hα : α = 0
  · subst hα
    rw [nabla_zero _ (fun y => sh_zero y)]
    have : ord (0 : Fin 2 → E → ℕ) = 0 := by simp [ord, Grassmann.mabs]
    rw [this, pow_zero, mul_one]
    calc ℓ⁻¹ ^ 2 * ‖gsp z‖ ≤ ℓ⁻¹ ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (norm_gsp_le z) (by positivity)
      _ = ℓ⁻¹ ^ 2 := mul_one _
  · have hc : nab α (gsp (X := X)) z = nab α (fun _ => gsp z) z :=
      nabla_congr _ α z fun β => rfl
    rw [hc, nabla_const _ hα, norm_zero, mul_zero]; positivity

/-- `|F²| ≤ ℓ^{-2} ‖F‖_T`. -/
theorem norm_c2_le (hh : 0 < h) (hℓ : 0 < ℓ) (F : Grassmann.N X) :
    ‖c2 F‖ ≤ (tNorm E p h ℓ F).toReal * ℓ⁻¹ ^ 2 := by
  rw [← pair_gsp]
  exact abs_pair_le hh hℓ F (by positivity) (phiNorm_gsp_le hh hℓ)

end General

theorem nb_top (N : ℕ) : nb N (univ : Finset (Lam d L N)) ≤ 2 ^ d := by
  refine le_trans (Finset.card_le_one.2 fun a ha b hb => ?_) (Nat.one_le_two_pow)
  obtain ⟨x, -, rfl⟩ := mem_blocks.1 ha
  obtain ⟨y, -, rfl⟩ := mem_blocks.1 hb
  rw [blk_top, blk_top]

/-- `‖K(Λ_N)‖_{T_N(ℓ)} ≤ ‖K‖_N`: `Λ_N` is a connected `N`-polymer with a single block. -/
theorem Tj_le_Knorm {N : ℕ} (ℓ A : ℝ) (K : Act d L N) :
    Tj d (L : ℝ) N ℓ (K univ : Alg d L N) ≤ Knorm N ℓ A K := by
  refine le_trans ?_ (le_iSup₂_of_le univ (mem_connSets.2 (isConn_top N)) le_rfl)
  rw [Nat.sub_eq_zero_of_le (nb_top N), pow_zero, ENNReal.ofReal_one, one_mul]

variable (d L) in
/-- The norm `‖K_N‖_N` of the last activity. -/
abbrev KNnorm (N : ℕ) (msq : ℝ) (V₀ : Vcoup) (ℓ A : ℝ) : ENNReal :=
  Knorm N ℓ A (flowN d L N msq V₀ N).2

/-- **`e:ZNN-bd`**, first part: `|k_N^0| ≤ ‖K_N(Λ)‖_{T_N(ℓ)} ≤ ‖K_N‖_N`. -/
theorem kN0_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (A : ℝ) (msq : ℝ) (V₀ : Vcoup) :
    ‖kN0 d L N msq V₀‖ ≤ (Tj d (L : ℝ) N ℓ (KN d L N msq V₀ : Alg d L N)).toReal ∧
      ‖kN0 d L N msq V₀‖ ≤ (KNnorm d L N msq V₀ ℓ A).toReal := by
  have hh : (0 : ℝ) < (L : ℝ) ^ N := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) N
  have h1 := abs_eps_le (E := Dir d) (p := pPhi d) hh hℓ (KN d L N msq V₀ : Alg d L N)
  refine ⟨h1, h1.trans (ENNReal.toReal_mono (Step.Knorm_ne_top hℓ _) (Tj_le_Knorm ℓ A _))⟩

/-- **`e:ZNN-bd`**, second part: `|k_N^2| ≤ ℓ^{-2} ‖K_N(Λ)‖_{T_N(ℓ)} ≤ ℓ^{-2} ‖K_N‖_N`. -/
theorem kN2_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (A : ℝ) (msq : ℝ) (V₀ : Vcoup) :
    ‖kN2 d L N msq V₀‖ ≤ ℓ⁻¹ ^ 2 * (Tj d (L : ℝ) N ℓ (KN d L N msq V₀ : Alg d L N)).toReal ∧
      ‖kN2 d L N msq V₀‖ ≤ ℓ⁻¹ ^ 2 * (KNnorm d L N msq V₀ ℓ A).toReal := by
  have hh : (0 : ℝ) < (L : ℝ) ^ N := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) N
  have h1 := norm_c2_le (E := Dir d) (p := pPhi d) hh hℓ (KN d L N msq V₀ : Alg d L N)
  rw [mul_comm] at h1
  refine ⟨h1, h1.trans (mul_le_mul_of_nonneg_left
    (ENNReal.toReal_mono (Step.Knorm_ne_top hℓ _) (Tj_le_Knorm ℓ A _)) (by positivity))⟩

end

end Suscept
