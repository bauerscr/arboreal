import Step2.Coup.BubbleX

/-!
# The bubble: explicit evaluation of `μ₄ X₂` for two `gmono4` (`prop:d2`, (R4))

`mu4_X2_v4g`: for the legs `v(e,x)`, `v(f,y)` of `(∇_eψ)(∇_eψ̄)ψψ̄` at `x` and `(∇_fψ)(∇_fψ̄)ψψ̄` at
`y`, `μ₄ X₂ = 2 · bubPoly(C; x, x+e, y, y+f; ℓ)` with an explicit polynomial `bubPoly`, quadratic in
the eight entries `C(x', y')`, `C(y', x')` (`x' ∈ {x, x+e}`, `y' ∈ {y, y+f}`) and quadratic in
the lifts `ℓ(x), ℓ(x+e), ℓ(y), ℓ(y+f)` (direction `κ`), depending on them only through differences.
-/

set_option maxRecDepth 10000

namespace Step2

open Step Finset Grassmann Loc FRD

noncomputable section

variable {d L N : ℕ} [NeZero L]

theorem pairC_ev_pm (C : Matrix (Lam d L N) (Lam d L N) ℂ) (a b : Lam d L N) :
    pairC C (ev (a, 1)) (ev (b, -1)) = C b a := by
  simp [pairC, ev, Pi.single_apply, Prod.ext_iff]

theorem pairC_ev_mm (C : Matrix (Lam d L N) (Lam d L N) ℂ) (a : Lam d L N) (w : V (Lam d L N)) :
    pairC C (ev (a, -1)) w = 0 := by
  simp [pairC, ev, Prod.ext_iff]

theorem pairC_ev_pp (C : Matrix (Lam d L N) (Lam d L N) ℂ) (u : V (Lam d L N)) (b : Lam d L N) :
    pairC C u (ev (b, 1)) = 0 := by
  simp [pairC, ev, Prod.ext_iff]

theorem pairC_sub_l (C : Matrix (Lam d L N) (Lam d L N) ℂ) (u u' w : V (Lam d L N)) :
    pairC C (u - u') w = pairC C u w - pairC C u' w := by
  simp only [pairC, Pi.sub_apply, sub_mul, mul_sub, sum_sub_distrib]

theorem pairC_sub_r (C : Matrix (Lam d L N) (Lam d L N) ℂ) (u w w' : V (Lam d L N)) :
    pairC C u (w - w') = pairC C u w - pairC C u w' := by
  simp only [pairC, Pi.sub_apply, sub_mul, mul_sub, sum_sub_distrib]

/-- `μ₄ X₂` with the index maps written out. -/
theorem mu4_X2_explicit (C : Matrix (Lam d L N) (Lam d L N) ℂ) (b : Lam d L N) (κ κ' : Fin d)
    (p q : Fin 4 → V (Lam d L N)) :
    mu4 b κ κ' (X2 C (ExteriorAlgebra.ιMulti ℂ 4 p) (ExteriorAlgebra.ιMulti ℂ 4 q)) =
      ∑ r : Fin 4, ∑ s : Fin 4, ∑ r' : Fin 3, ∑ s' : Fin 3,
        -((-1 : ℂ) ^ (r : ℕ) * (-1 : ℂ) ^ (s : ℕ) * Kc C (p r) (q s)) *
          ((-1 : ℂ) ^ (r' : ℕ) * (-1 : ℂ) ^ (s' : ℕ) *
            Kc C (p (r.succAbove r')) (q (s.succAbove s'))) *
          Matrix.det (Matrix.of ![
            ![col b κ κ' (p (r.succAbove (r'.succAbove 0))) 0, col b κ κ' (p (r.succAbove (r'.succAbove 1))) 0,
              col b κ κ' (q (s.succAbove (s'.succAbove 0))) 0, col b κ κ' (q (s.succAbove (s'.succAbove 1))) 0],
            ![col b κ κ' (p (r.succAbove (r'.succAbove 0))) 1, col b κ κ' (p (r.succAbove (r'.succAbove 1))) 1,
              col b κ κ' (q (s.succAbove (s'.succAbove 0))) 1, col b κ κ' (q (s.succAbove (s'.succAbove 1))) 1],
            ![col b κ κ' (p (r.succAbove (r'.succAbove 0))) 2, col b κ κ' (p (r.succAbove (r'.succAbove 1))) 2,
              col b κ κ' (q (s.succAbove (s'.succAbove 0))) 2, col b κ κ' (q (s.succAbove (s'.succAbove 1))) 2],
            ![col b κ κ' (p (r.succAbove (r'.succAbove 0))) 3, col b κ κ' (p (r.succAbove (r'.succAbove 1))) 3,
              col b κ κ' (q (s.succAbove (s'.succAbove 0))) 3, col b κ κ' (q (s.succAbove (s'.succAbove 1))) 3]]) := by
  rw [mu4_X2_ιMulti]
  refine sum_congr rfl fun r _ => sum_congr rfl fun s _ => sum_congr rfl fun r' _ =>
    sum_congr rfl fun s' _ => ?_
  congr 2
  congr 1
  ext a c
  fin_cases a <;> fin_cases c <;> rfl

@[simp] theorem sa4_0_0 : ((0 : Fin 4).succAbove (0 : Fin 3)) = (1 : Fin 4) := by decide

@[simp] theorem sa4_0_1 : ((0 : Fin 4).succAbove (1 : Fin 3)) = (2 : Fin 4) := by decide

@[simp] theorem sa4_0_2 : ((0 : Fin 4).succAbove (2 : Fin 3)) = (3 : Fin 4) := by decide

@[simp] theorem sa4_1_0 : ((1 : Fin 4).succAbove (0 : Fin 3)) = (0 : Fin 4) := by decide

@[simp] theorem sa4_1_1 : ((1 : Fin 4).succAbove (1 : Fin 3)) = (2 : Fin 4) := by decide

@[simp] theorem sa4_1_2 : ((1 : Fin 4).succAbove (2 : Fin 3)) = (3 : Fin 4) := by decide

@[simp] theorem sa4_2_0 : ((2 : Fin 4).succAbove (0 : Fin 3)) = (0 : Fin 4) := by decide

@[simp] theorem sa4_2_1 : ((2 : Fin 4).succAbove (1 : Fin 3)) = (1 : Fin 4) := by decide

@[simp] theorem sa4_2_2 : ((2 : Fin 4).succAbove (2 : Fin 3)) = (3 : Fin 4) := by decide

@[simp] theorem sa4_3_0 : ((3 : Fin 4).succAbove (0 : Fin 3)) = (0 : Fin 4) := by decide

@[simp] theorem sa4_3_1 : ((3 : Fin 4).succAbove (1 : Fin 3)) = (1 : Fin 4) := by decide

@[simp] theorem sa4_3_2 : ((3 : Fin 4).succAbove (2 : Fin 3)) = (2 : Fin 4) := by decide

@[simp] theorem sa3_0_0 : ((0 : Fin 3).succAbove (0 : Fin 2)) = (1 : Fin 3) := by decide

@[simp] theorem sa3_0_1 : ((0 : Fin 3).succAbove (1 : Fin 2)) = (2 : Fin 3) := by decide

@[simp] theorem sa3_1_0 : ((1 : Fin 3).succAbove (0 : Fin 2)) = (0 : Fin 3) := by decide

@[simp] theorem sa3_1_1 : ((1 : Fin 3).succAbove (1 : Fin 2)) = (2 : Fin 3) := by decide

@[simp] theorem sa3_2_0 : ((2 : Fin 3).succAbove (0 : Fin 2)) = (0 : Fin 3) := by decide

@[simp] theorem sa3_2_1 : ((2 : Fin 3).succAbove (1 : Fin 2)) = (1 : Fin 3) := by decide


@[simp] theorem sgn4_0 : (-1 : ℂ) ^ (((0 : Fin 4) : ℕ)) = 1 := by norm_num
@[simp] theorem sgn4_1 : (-1 : ℂ) ^ (((1 : Fin 4) : ℕ)) = -1 := by norm_num
@[simp] theorem sgn4_2 : (-1 : ℂ) ^ (((2 : Fin 4) : ℕ)) = 1 := by norm_num
@[simp] theorem sgn4_3 : (-1 : ℂ) ^ (((3 : Fin 4) : ℕ)) = -1 := by norm_num
@[simp] theorem sgn3_0 : (-1 : ℂ) ^ (((0 : Fin 3) : ℕ)) = 1 := by norm_num
@[simp] theorem sgn3_1 : (-1 : ℂ) ^ (((1 : Fin 3) : ℕ)) = -1 := by norm_num
@[simp] theorem sgn3_2 : (-1 : ℂ) ^ (((2 : Fin 3) : ℕ)) = 1 := by norm_num

/-- The polynomial of `mu4_X2_v4g`. -/
def bubPoly {Λ : Type*} (C : Matrix Λ Λ ℂ) (x xe y yf : Λ) (lx lxe ly lyf : ℂ) : ℂ :=
  (C x y)*(C xe yf)*(lx)*(ly) - (C x y)*(C xe yf)*(lx)*(lyf) - (C x y)*(C xe yf)*(lxe)*(ly) + (C x y)*(C xe yf)*(lxe)*(lyf) - (C x y)*(C y x)*(lxe)^2 + 2*(C x y)*(C y x)*(lxe)*(lyf) - (C x y)*(C y x)*(lyf)^2 + (C x y)*(C y xe)*(lx)*(lxe) - (C x y)*(C y xe)*(lx)*(lyf) - (C x y)*(C y xe)*(lxe)*(lyf) + (C x y)*(C y xe)*(lyf)^2 + (C x y)*(C yf x)*(lxe)^2 - (C x y)*(C yf x)*(lxe)*(ly) - (C x y)*(C yf x)*(lxe)*(lyf) + (C x y)*(C yf x)*(ly)*(lyf) - (C x y)*(C yf xe)*(lx)*(lxe) + (C x y)*(C yf xe)*(lx)*(ly) + (C x y)*(C yf xe)*(lxe)*(lyf) - (C x y)*(C yf xe)*(ly)*(lyf) - (C x yf)*(C xe y)*(lx)*(ly) + (C x yf)*(C xe y)*(lx)*(lyf) + (C x yf)*(C xe y)*(lxe)*(ly) - (C x yf)*(C xe y)*(lxe)*(lyf) + (C x yf)*(C y x)*(lxe)^2 - (C x yf)*(C y x)*(lxe)*(ly) - (C x yf)*(C y x)*(lxe)*(lyf) + (C x yf)*(C y x)*(ly)*(lyf) - (C x yf)*(C y xe)*(lx)*(lxe) + (C x yf)*(C y xe)*(lx)*(lyf) + (C x yf)*(C y xe)*(lxe)*(ly) - (C x yf)*(C y xe)*(ly)*(lyf) - (C x yf)*(C yf x)*(lxe)^2 + 2*(C x yf)*(C yf x)*(lxe)*(ly) - (C x yf)*(C yf x)*(ly)^2 + (C x yf)*(C yf xe)*(lx)*(lxe) - (C x yf)*(C yf xe)*(lx)*(ly) - (C x yf)*(C yf xe)*(lxe)*(ly) + (C x yf)*(C yf xe)*(ly)^2 + (C xe y)*(C y x)*(lx)*(lxe) - (C xe y)*(C y x)*(lx)*(lyf) - (C xe y)*(C y x)*(lxe)*(lyf) + (C xe y)*(C y x)*(lyf)^2 - (C xe y)*(C y xe)*(lx)^2 + 2*(C xe y)*(C y xe)*(lx)*(lyf) - (C xe y)*(C y xe)*(lyf)^2 - (C xe y)*(C yf x)*(lx)*(lxe) + (C xe y)*(C yf x)*(lx)*(lyf) + (C xe y)*(C yf x)*(lxe)*(ly) - (C xe y)*(C yf x)*(ly)*(lyf) + (C xe y)*(C yf xe)*(lx)^2 - (C xe y)*(C yf xe)*(lx)*(ly) - (C xe y)*(C yf xe)*(lx)*(lyf) + (C xe y)*(C yf xe)*(ly)*(lyf) - (C xe yf)*(C y x)*(lx)*(lxe) + (C xe yf)*(C y x)*(lx)*(ly) + (C xe yf)*(C y x)*(lxe)*(lyf) - (C xe yf)*(C y x)*(ly)*(lyf) + (C xe yf)*(C y xe)*(lx)^2 - (C xe yf)*(C y xe)*(lx)*(ly) - (C xe yf)*(C y xe)*(lx)*(lyf) + (C xe yf)*(C y xe)*(ly)*(lyf) + (C xe yf)*(C yf x)*(lx)*(lxe) - (C xe yf)*(C yf x)*(lx)*(ly) - (C xe yf)*(C yf x)*(lxe)*(ly) + (C xe yf)*(C yf x)*(ly)^2 - (C xe yf)*(C yf xe)*(lx)^2 + 2*(C xe yf)*(C yf xe)*(lx)*(ly) - (C xe yf)*(C yf xe)*(ly)^2 + (C y x)*(C yf xe)*(lx)*(ly) - (C y x)*(C yf xe)*(lx)*(lyf) - (C y x)*(C yf xe)*(lxe)*(ly) + (C y x)*(C yf xe)*(lxe)*(lyf) - (C y xe)*(C yf x)*(lx)*(ly) + (C y xe)*(C yf x)*(lx)*(lyf) + (C y xe)*(C yf x)*(lxe)*(ly) - (C y xe)*(C yf x)*(lxe)*(lyf)

section V4

variable (C : Matrix (Lam d L N) (Lam d L N) ℂ) (e f : Dir d) (x y : Lam d L N)

theorem col_v4g (b : Lam d L N) (κ : Fin d) (e : Dir d) (x : Lam d L N) :
    (col b κ κ (v4g e e x 0) = ![(lift b (x + dirVec e) κ : ℂ) - lift b x κ, 0, 0, 0]) ∧
    (col b κ κ (v4g e e x 1) = ![0, (lift b (x + dirVec e) κ : ℂ) - lift b x κ, 0, 0]) ∧
    (col b κ κ (v4g e e x 2) = ![(lift b x κ : ℂ), 0, 1, 0]) ∧
    (col b κ κ (v4g e e x 3) = ![0, (lift b x κ : ℂ), 0, 1]) := by
  refine ⟨?_, ?_, col_ev_pos b κ κ x, col_ev_neg b κ κ x⟩
  · show col b κ κ (ev (x + dirVec e, 1) - ev (x, 1)) = _
    rw [col_sub, col_ev_pos, col_ev_pos]
    funext a; fin_cases a <;> simp
  · show col b κ κ (ev (x + dirVec e, -1) - ev (x, -1)) = _
    rw [col_sub, col_ev_neg, col_ev_neg]
    funext a; fin_cases a <;> simp

theorem v4g_vals (e : Dir d) (x : Lam d L N) :
    v4g e e x 0 = ev (x + dirVec e, 1) - ev (x, 1) ∧ v4g e e x 1 = ev (x + dirVec e, -1) - ev (x, -1) ∧
      v4g e e x 2 = ev (x, 1) ∧ v4g e e x 3 = ev (x, -1) := ⟨rfl, rfl, rfl, rfl⟩

/-- The summand of `mu4_X2_explicit`. -/
def bt (C : Matrix (Lam d L N) (Lam d L N) ℂ) (b : Lam d L N) (κ κ' : Fin d)
    (p q : Fin 4 → V (Lam d L N)) (r s : Fin 4) (r' s' : Fin 3) : ℂ :=
  -((-1 : ℂ) ^ (r : ℕ) * (-1 : ℂ) ^ (s : ℕ) * Kc C (p r) (q s)) *
    ((-1 : ℂ) ^ (r' : ℕ) * (-1 : ℂ) ^ (s' : ℕ) *
      Kc C (p (r.succAbove r')) (q (s.succAbove s'))) *
    Matrix.det (Matrix.of ![
      ![col b κ κ' (p (r.succAbove (r'.succAbove 0))) 0, col b κ κ' (p (r.succAbove (r'.succAbove 1))) 0,
        col b κ κ' (q (s.succAbove (s'.succAbove 0))) 0, col b κ κ' (q (s.succAbove (s'.succAbove 1))) 0],
      ![col b κ κ' (p (r.succAbove (r'.succAbove 0))) 1, col b κ κ' (p (r.succAbove (r'.succAbove 1))) 1,
        col b κ κ' (q (s.succAbove (s'.succAbove 0))) 1, col b κ κ' (q (s.succAbove (s'.succAbove 1))) 1],
      ![col b κ κ' (p (r.succAbove (r'.succAbove 0))) 2, col b κ κ' (p (r.succAbove (r'.succAbove 1))) 2,
        col b κ κ' (q (s.succAbove (s'.succAbove 0))) 2, col b κ κ' (q (s.succAbove (s'.succAbove 1))) 2],
      ![col b κ κ' (p (r.succAbove (r'.succAbove 0))) 3, col b κ κ' (p (r.succAbove (r'.succAbove 1))) 3,
        col b κ κ' (q (s.succAbove (s'.succAbove 0))) 3, col b κ κ' (q (s.succAbove (s'.succAbove 1))) 3]])

theorem mu4_X2_bt (C : Matrix (Lam d L N) (Lam d L N) ℂ) (b : Lam d L N) (κ κ' : Fin d)
    (p q : Fin 4 → V (Lam d L N)) :
    mu4 b κ κ' (X2 C (ExteriorAlgebra.ιMulti ℂ 4 p) (ExteriorAlgebra.ιMulti ℂ 4 q)) =
      ∑ r : Fin 4, ∑ s : Fin 4, ∑ r' : Fin 3, ∑ s' : Fin 3, bt C b κ κ' p q r s r' s' :=
  mu4_X2_explicit C b κ κ' p q

/-- Block `(0, 0)`. -/
def bp00 {Λ : Type*} (C : Matrix Λ Λ ℂ) (x xe y yf : Λ) (lx lxe ly lyf : ℂ) : ℂ :=
  0

/-- Block `(0, 1)`. -/
def bp01 {Λ : Type*} (C : Matrix Λ Λ ℂ) (x xe y yf : Λ) (lx lxe ly lyf : ℂ) : ℂ :=
  -(C x y)*(C y x)*(lx)*(lxe) + (C x y)*(C y x)*(lx)*(ly) + (C x y)*(C y x)*(lxe)*(lyf) - (C x y)*(C y x)*(ly)*(lyf) + (C x y)*(C y xe)*(lx)*(lxe) - (C x y)*(C y xe)*(lx)*(ly) - (C x y)*(C y xe)*(lxe)*(lyf) + (C x y)*(C y xe)*(ly)*(lyf) + (C x y)*(C yf x)*(lx)*(lxe) - (C x y)*(C yf x)*(lx)*(ly) - (C x y)*(C yf x)*(lxe)*(lyf) + (C x y)*(C yf x)*(ly)*(lyf) - (C x y)*(C yf xe)*(lx)*(lxe) + (C x y)*(C yf xe)*(lx)*(ly) + (C x y)*(C yf xe)*(lxe)*(lyf) - (C x y)*(C yf xe)*(ly)*(lyf) + (C x yf)*(C y x)*(lx)*(lxe) - (C x yf)*(C y x)*(lx)*(ly) - (C x yf)*(C y x)*(lxe)*(ly) + (C x yf)*(C y x)*(ly)^2 - (C x yf)*(C y xe)*(lx)*(lxe) + (C x yf)*(C y xe)*(lx)*(ly) + (C x yf)*(C y xe)*(lxe)*(ly) - (C x yf)*(C y xe)*(ly)^2 - (C x yf)*(C yf x)*(lx)*(lxe) + (C x yf)*(C yf x)*(lx)*(ly) + (C x yf)*(C yf x)*(lxe)*(ly) - (C x yf)*(C yf x)*(ly)^2 + (C x yf)*(C yf xe)*(lx)*(lxe) - (C x yf)*(C yf xe)*(lx)*(ly) - (C x yf)*(C yf xe)*(lxe)*(ly) + (C x yf)*(C yf xe)*(ly)^2 + (C xe y)*(C y x)*(lx)^2 - (C xe y)*(C y x)*(lx)*(ly) - (C xe y)*(C y x)*(lx)*(lyf) + (C xe y)*(C y x)*(ly)*(lyf) - (C xe y)*(C y xe)*(lx)^2 + (C xe y)*(C y xe)*(lx)*(ly) + (C xe y)*(C y xe)*(lx)*(lyf) - (C xe y)*(C y xe)*(ly)*(lyf) - (C xe y)*(C yf x)*(lx)^2 + (C xe y)*(C yf x)*(lx)*(ly) + (C xe y)*(C yf x)*(lx)*(lyf) - (C xe y)*(C yf x)*(ly)*(lyf) + (C xe y)*(C yf xe)*(lx)^2 - (C xe y)*(C yf xe)*(lx)*(ly) - (C xe y)*(C yf xe)*(lx)*(lyf) + (C xe y)*(C yf xe)*(ly)*(lyf) - (C xe yf)*(C y x)*(lx)^2 + 2*(C xe yf)*(C y x)*(lx)*(ly) - (C xe yf)*(C y x)*(ly)^2 + (C xe yf)*(C y xe)*(lx)^2 - 2*(C xe yf)*(C y xe)*(lx)*(ly) + (C xe yf)*(C y xe)*(ly)^2 + (C xe yf)*(C yf x)*(lx)^2 - 2*(C xe yf)*(C yf x)*(lx)*(ly) + (C xe yf)*(C yf x)*(ly)^2 - (C xe yf)*(C yf xe)*(lx)^2 + 2*(C xe yf)*(C yf xe)*(lx)*(ly) - (C xe yf)*(C yf xe)*(ly)^2 + (C y x)^2*(lx)*(ly) - (C y x)^2*(lx)*(lyf) - (C y x)^2*(lxe)*(ly) + (C y x)^2*(lxe)*(lyf) - (C y x)*(C y xe)*(lx)*(ly) + (C y x)*(C y xe)*(lx)*(lyf) + (C y x)*(C y xe)*(lxe)*(ly) - (C y x)*(C y xe)*(lxe)*(lyf) - (C y x)*(C yf x)*(lx)*(ly) + (C y x)*(C yf x)*(lx)*(lyf) + (C y x)*(C yf x)*(lxe)*(ly) - (C y x)*(C yf x)*(lxe)*(lyf) + (C y x)*(C yf xe)*(lx)*(ly) - (C y x)*(C yf xe)*(lx)*(lyf) - (C y x)*(C yf xe)*(lxe)*(ly) + (C y x)*(C yf xe)*(lxe)*(lyf)

/-- Block `(0, 2)`. -/
def bp02 {Λ : Type*} (C : Matrix Λ Λ ℂ) (x xe y yf : Λ) (lx lxe ly lyf : ℂ) : ℂ :=
  0

/-- Block `(0, 3)`. -/
def bp03 {Λ : Type*} (C : Matrix Λ Λ ℂ) (x xe y yf : Λ) (lx lxe ly lyf : ℂ) : ℂ :=
  -(C x y)*(C y x)*(lx)*(ly) + (C x y)*(C y x)*(lx)*(lyf) + (C x y)*(C y x)*(ly)*(lyf) - (C x y)*(C y x)*(lyf)^2 + (C x y)*(C y xe)*(lx)*(ly) - (C x y)*(C y xe)*(lx)*(lyf) - (C x y)*(C y xe)*(ly)*(lyf) + (C x y)*(C y xe)*(lyf)^2 + (C x yf)*(C y x)*(lx)*(ly) - (C x yf)*(C y x)*(lx)*(lyf) - (C x yf)*(C y x)*(ly)^2 + (C x yf)*(C y x)*(ly)*(lyf) - (C x yf)*(C y xe)*(lx)*(ly) + (C x yf)*(C y xe)*(lx)*(lyf) + (C x yf)*(C y xe)*(ly)^2 - (C x yf)*(C y xe)*(ly)*(lyf) + (C xe y)*(C y x)*(lx)*(ly) - (C xe y)*(C y x)*(lx)*(lyf) - (C xe y)*(C y x)*(ly)*(lyf) + (C xe y)*(C y x)*(lyf)^2 - (C xe y)*(C y xe)*(lx)*(ly) + (C xe y)*(C y xe)*(lx)*(lyf) + (C xe y)*(C y xe)*(ly)*(lyf) - (C xe y)*(C y xe)*(lyf)^2 - (C xe yf)*(C y x)*(lx)*(ly) + (C xe yf)*(C y x)*(lx)*(lyf) + (C xe yf)*(C y x)*(ly)^2 - (C xe yf)*(C y x)*(ly)*(lyf) + (C xe yf)*(C y xe)*(lx)*(ly) - (C xe yf)*(C y xe)*(lx)*(lyf) - (C xe yf)*(C y xe)*(ly)^2 + (C xe yf)*(C y xe)*(ly)*(lyf) - (C y x)^2*(lx)*(ly) + (C y x)^2*(lx)*(lyf) + (C y x)^2*(lxe)*(ly) - (C y x)^2*(lxe)*(lyf) + (C y x)*(C y xe)*(lx)*(ly) - (C y x)*(C y xe)*(lx)*(lyf) - (C y x)*(C y xe)*(lxe)*(ly) + (C y x)*(C y xe)*(lxe)*(lyf) + (C y x)*(C yf x)*(lx)*(ly) - (C y x)*(C yf x)*(lx)*(lyf) - (C y x)*(C yf x)*(lxe)*(ly) + (C y x)*(C yf x)*(lxe)*(lyf) - (C y xe)*(C yf x)*(lx)*(ly) + (C y xe)*(C yf x)*(lx)*(lyf) + (C y xe)*(C yf x)*(lxe)*(ly) - (C y xe)*(C yf x)*(lxe)*(lyf)

/-- Block `(1, 0)`. -/
def bp10 {Λ : Type*} (C : Matrix Λ Λ ℂ) (x xe y yf : Λ) (lx lxe ly lyf : ℂ) : ℂ :=
  (C x y)^2*(lx)*(ly) - (C x y)^2*(lx)*(lyf) - (C x y)^2*(lxe)*(ly) + (C x y)^2*(lxe)*(lyf) - (C x y)*(C x yf)*(lx)*(ly) + (C x y)*(C x yf)*(lx)*(lyf) + (C x y)*(C x yf)*(lxe)*(ly) - (C x y)*(C x yf)*(lxe)*(lyf) - (C x y)*(C xe y)*(lx)*(ly) + (C x y)*(C xe y)*(lx)*(lyf) + (C x y)*(C xe y)*(lxe)*(ly) - (C x y)*(C xe y)*(lxe)*(lyf) + (C x y)*(C xe yf)*(lx)*(ly) - (C x y)*(C xe yf)*(lx)*(lyf) - (C x y)*(C xe yf)*(lxe)*(ly) + (C x y)*(C xe yf)*(lxe)*(lyf) - (C x y)*(C y x)*(lx)*(lxe) + (C x y)*(C y x)*(lx)*(ly) + (C x y)*(C y x)*(lxe)*(lyf) - (C x y)*(C y x)*(ly)*(lyf) + (C x y)*(C y xe)*(lx)^2 - (C x y)*(C y xe)*(lx)*(ly) - (C x y)*(C y xe)*(lx)*(lyf) + (C x y)*(C y xe)*(ly)*(lyf) + (C x y)*(C yf x)*(lx)*(lxe) - (C x y)*(C yf x)*(lx)*(ly) - (C x y)*(C yf x)*(lxe)*(ly) + (C x y)*(C yf x)*(ly)^2 - (C x y)*(C yf xe)*(lx)^2 + 2*(C x y)*(C yf xe)*(lx)*(ly) - (C x y)*(C yf xe)*(ly)^2 + (C x yf)*(C y x)*(lx)*(lxe) - (C x yf)*(C y x)*(lx)*(ly) - (C x yf)*(C y x)*(lxe)*(lyf) + (C x yf)*(C y x)*(ly)*(lyf) - (C x yf)*(C y xe)*(lx)^2 + (C x yf)*(C y xe)*(lx)*(ly) + (C x yf)*(C y xe)*(lx)*(lyf) - (C x yf)*(C y xe)*(ly)*(lyf) - (C x yf)*(C yf x)*(lx)*(lxe) + (C x yf)*(C yf x)*(lx)*(ly) + (C x yf)*(C yf x)*(lxe)*(ly) - (C x yf)*(C yf x)*(ly)^2 + (C x yf)*(C yf xe)*(lx)^2 - 2*(C x yf)*(C yf xe)*(lx)*(ly) + (C x yf)*(C yf xe)*(ly)^2 + (C xe y)*(C y x)*(lx)*(lxe) - (C xe y)*(C y x)*(lx)*(ly) - (C xe y)*(C y x)*(lxe)*(lyf) + (C xe y)*(C y x)*(ly)*(lyf) - (C xe y)*(C y xe)*(lx)^2 + (C xe y)*(C y xe)*(lx)*(ly) + (C xe y)*(C y xe)*(lx)*(lyf) - (C xe y)*(C y xe)*(ly)*(lyf) - (C xe y)*(C yf x)*(lx)*(lxe) + (C xe y)*(C yf x)*(lx)*(ly) + (C xe y)*(C yf x)*(lxe)*(ly) - (C xe y)*(C yf x)*(ly)^2 + (C xe y)*(C yf xe)*(lx)^2 - 2*(C xe y)*(C yf xe)*(lx)*(ly) + (C xe y)*(C yf xe)*(ly)^2 - (C xe yf)*(C y x)*(lx)*(lxe) + (C xe yf)*(C y x)*(lx)*(ly) + (C xe yf)*(C y x)*(lxe)*(lyf) - (C xe yf)*(C y x)*(ly)*(lyf) + (C xe yf)*(C y xe)*(lx)^2 - (C xe yf)*(C y xe)*(lx)*(ly) - (C xe yf)*(C y xe)*(lx)*(lyf) + (C xe yf)*(C y xe)*(ly)*(lyf) + (C xe yf)*(C yf x)*(lx)*(lxe) - (C xe yf)*(C yf x)*(lx)*(ly) - (C xe yf)*(C yf x)*(lxe)*(ly) + (C xe yf)*(C yf x)*(ly)^2 - (C xe yf)*(C yf xe)*(lx)^2 + 2*(C xe yf)*(C yf xe)*(lx)*(ly) - (C xe yf)*(C yf xe)*(ly)^2

/-- Block `(1, 1)`. -/
def bp11 {Λ : Type*} (C : Matrix Λ Λ ℂ) (x xe y yf : Λ) (lx lxe ly lyf : ℂ) : ℂ :=
  0

/-- Block `(1, 2)`. -/
def bp12 {Λ : Type*} (C : Matrix Λ Λ ℂ) (x xe y yf : Λ) (lx lxe ly lyf : ℂ) : ℂ :=
  -(C x y)^2*(lx)*(ly) + (C x y)^2*(lx)*(lyf) + (C x y)^2*(lxe)*(ly) - (C x y)^2*(lxe)*(lyf) + (C x y)*(C x yf)*(lx)*(ly) - (C x y)*(C x yf)*(lx)*(lyf) - (C x y)*(C x yf)*(lxe)*(ly) + (C x y)*(C x yf)*(lxe)*(lyf) + (C x y)*(C xe y)*(lx)*(ly) - (C x y)*(C xe y)*(lx)*(lyf) - (C x y)*(C xe y)*(lxe)*(ly) + (C x y)*(C xe y)*(lxe)*(lyf) - (C x y)*(C y x)*(lx)*(ly) + (C x y)*(C y x)*(lx)*(lyf) + (C x y)*(C y x)*(ly)*(lyf) - (C x y)*(C y x)*(lyf)^2 + (C x y)*(C y xe)*(lx)*(ly) - (C x y)*(C y xe)*(lx)*(lyf) - (C x y)*(C y xe)*(ly)*(lyf) + (C x y)*(C y xe)*(lyf)^2 + (C x y)*(C yf x)*(lx)*(ly) - (C x y)*(C yf x)*(lx)*(lyf) - (C x y)*(C yf x)*(ly)^2 + (C x y)*(C yf x)*(ly)*(lyf) - (C x y)*(C yf xe)*(lx)*(ly) + (C x y)*(C yf xe)*(lx)*(lyf) + (C x y)*(C yf xe)*(ly)^2 - (C x y)*(C yf xe)*(ly)*(lyf) - (C x yf)*(C xe y)*(lx)*(ly) + (C x yf)*(C xe y)*(lx)*(lyf) + (C x yf)*(C xe y)*(lxe)*(ly) - (C x yf)*(C xe y)*(lxe)*(lyf) + (C xe y)*(C y x)*(lx)*(ly) - (C xe y)*(C y x)*(lx)*(lyf) - (C xe y)*(C y x)*(ly)*(lyf) + (C xe y)*(C y x)*(lyf)^2 - (C xe y)*(C y xe)*(lx)*(ly) + (C xe y)*(C y xe)*(lx)*(lyf) + (C xe y)*(C y xe)*(ly)*(lyf) - (C xe y)*(C y xe)*(lyf)^2 - (C xe y)*(C yf x)*(lx)*(ly) + (C xe y)*(C yf x)*(lx)*(lyf) + (C xe y)*(C yf x)*(ly)^2 - (C xe y)*(C yf x)*(ly)*(lyf) + (C xe y)*(C yf xe)*(lx)*(ly) - (C xe y)*(C yf xe)*(lx)*(lyf) - (C xe y)*(C yf xe)*(ly)^2 + (C xe y)*(C yf xe)*(ly)*(lyf)

/-- Block `(1, 3)`. -/
def bp13 {Λ : Type*} (C : Matrix Λ Λ ℂ) (x xe y yf : Λ) (lx lxe ly lyf : ℂ) : ℂ :=
  0

/-- Block `(2, 0)`. -/
def bp20 {Λ : Type*} (C : Matrix Λ Λ ℂ) (x xe y yf : Λ) (lx lxe ly lyf : ℂ) : ℂ :=
  0

/-- Block `(2, 1)`. -/
def bp21 {Λ : Type*} (C : Matrix Λ Λ ℂ) (x xe y yf : Λ) (lx lxe ly lyf : ℂ) : ℂ :=
  (C x y)*(C y x)*(lx)*(lxe) - (C x y)*(C y x)*(lx)*(ly) - (C x y)*(C y x)*(lxe)^2 + (C x y)*(C y x)*(lxe)*(ly) - (C x y)*(C yf x)*(lx)*(lxe) + (C x y)*(C yf x)*(lx)*(ly) + (C x y)*(C yf x)*(lxe)^2 - (C x y)*(C yf x)*(lxe)*(ly) - (C x yf)*(C y x)*(lx)*(lxe) + (C x yf)*(C y x)*(lx)*(ly) + (C x yf)*(C y x)*(lxe)^2 - (C x yf)*(C y x)*(lxe)*(ly) + (C x yf)*(C yf x)*(lx)*(lxe) - (C x yf)*(C yf x)*(lx)*(ly) - (C x yf)*(C yf x)*(lxe)^2 + (C x yf)*(C yf x)*(lxe)*(ly) - (C xe y)*(C y x)*(lx)^2 + (C xe y)*(C y x)*(lx)*(lxe) + (C xe y)*(C y x)*(lx)*(ly) - (C xe y)*(C y x)*(lxe)*(ly) + (C xe y)*(C yf x)*(lx)^2 - (C xe y)*(C yf x)*(lx)*(lxe) - (C xe y)*(C yf x)*(lx)*(ly) + (C xe y)*(C yf x)*(lxe)*(ly) + (C xe yf)*(C y x)*(lx)^2 - (C xe yf)*(C y x)*(lx)*(lxe) - (C xe yf)*(C y x)*(lx)*(ly) + (C xe yf)*(C y x)*(lxe)*(ly) - (C xe yf)*(C yf x)*(lx)^2 + (C xe yf)*(C yf x)*(lx)*(lxe) + (C xe yf)*(C yf x)*(lx)*(ly) - (C xe yf)*(C yf x)*(lxe)*(ly) - (C y x)^2*(lx)*(ly) + (C y x)^2*(lx)*(lyf) + (C y x)^2*(lxe)*(ly) - (C y x)^2*(lxe)*(lyf) + (C y x)*(C y xe)*(lx)*(ly) - (C y x)*(C y xe)*(lx)*(lyf) - (C y x)*(C y xe)*(lxe)*(ly) + (C y x)*(C y xe)*(lxe)*(lyf) + (C y x)*(C yf x)*(lx)*(ly) - (C y x)*(C yf x)*(lx)*(lyf) - (C y x)*(C yf x)*(lxe)*(ly) + (C y x)*(C yf x)*(lxe)*(lyf) - (C y xe)*(C yf x)*(lx)*(ly) + (C y xe)*(C yf x)*(lx)*(lyf) + (C y xe)*(C yf x)*(lxe)*(ly) - (C y xe)*(C yf x)*(lxe)*(lyf)

/-- Block `(2, 2)`. -/
def bp22 {Λ : Type*} (C : Matrix Λ Λ ℂ) (x xe y yf : Λ) (lx lxe ly lyf : ℂ) : ℂ :=
  0

/-- Block `(2, 3)`. -/
def bp23 {Λ : Type*} (C : Matrix Λ Λ ℂ) (x xe y yf : Λ) (lx lxe ly lyf : ℂ) : ℂ :=
  (C x y)*(C y x)*(lx)*(ly) - (C x y)*(C y x)*(lx)*(lyf) - (C x y)*(C y x)*(lxe)*(ly) + (C x y)*(C y x)*(lxe)*(lyf) - (C x yf)*(C y x)*(lx)*(ly) + (C x yf)*(C y x)*(lx)*(lyf) + (C x yf)*(C y x)*(lxe)*(ly) - (C x yf)*(C y x)*(lxe)*(lyf) - (C xe y)*(C y x)*(lx)*(ly) + (C xe y)*(C y x)*(lx)*(lyf) + (C xe y)*(C y x)*(lxe)*(ly) - (C xe y)*(C y x)*(lxe)*(lyf) + (C xe yf)*(C y x)*(lx)*(ly) - (C xe yf)*(C y x)*(lx)*(lyf) - (C xe yf)*(C y x)*(lxe)*(ly) + (C xe yf)*(C y x)*(lxe)*(lyf) + (C y x)^2*(lx)*(ly) - (C y x)^2*(lx)*(lyf) - (C y x)^2*(lxe)*(ly) + (C y x)^2*(lxe)*(lyf) - (C y x)*(C y xe)*(lx)*(ly) + (C y x)*(C y xe)*(lx)*(lyf) + (C y x)*(C y xe)*(lxe)*(ly) - (C y x)*(C y xe)*(lxe)*(lyf) - (C y x)*(C yf x)*(lx)*(ly) + (C y x)*(C yf x)*(lx)*(lyf) + (C y x)*(C yf x)*(lxe)*(ly) - (C y x)*(C yf x)*(lxe)*(lyf) + (C y x)*(C yf xe)*(lx)*(ly) - (C y x)*(C yf xe)*(lx)*(lyf) - (C y x)*(C yf xe)*(lxe)*(ly) + (C y x)*(C yf xe)*(lxe)*(lyf)

/-- Block `(3, 0)`. -/
def bp30 {Λ : Type*} (C : Matrix Λ Λ ℂ) (x xe y yf : Λ) (lx lxe ly lyf : ℂ) : ℂ :=
  -(C x y)^2*(lx)*(ly) + (C x y)^2*(lx)*(lyf) + (C x y)^2*(lxe)*(ly) - (C x y)^2*(lxe)*(lyf) + (C x y)*(C x yf)*(lx)*(ly) - (C x y)*(C x yf)*(lx)*(lyf) - (C x y)*(C x yf)*(lxe)*(ly) + (C x y)*(C x yf)*(lxe)*(lyf) + (C x y)*(C xe y)*(lx)*(ly) - (C x y)*(C xe y)*(lx)*(lyf) - (C x y)*(C xe y)*(lxe)*(ly) + (C x y)*(C xe y)*(lxe)*(lyf) + (C x y)*(C y x)*(lx)*(lxe) - (C x y)*(C y x)*(lx)*(ly) - (C x y)*(C y x)*(lxe)^2 + (C x y)*(C y x)*(lxe)*(ly) - (C x y)*(C y xe)*(lx)^2 + (C x y)*(C y xe)*(lx)*(lxe) + (C x y)*(C y xe)*(lx)*(ly) - (C x y)*(C y xe)*(lxe)*(ly) - (C x y)*(C yf x)*(lx)*(lxe) + (C x y)*(C yf x)*(lx)*(ly) + (C x y)*(C yf x)*(lxe)^2 - (C x y)*(C yf x)*(lxe)*(ly) + (C x y)*(C yf xe)*(lx)^2 - (C x y)*(C yf xe)*(lx)*(lxe) - (C x y)*(C yf xe)*(lx)*(ly) + (C x y)*(C yf xe)*(lxe)*(ly) - (C x yf)*(C xe y)*(lx)*(ly) + (C x yf)*(C xe y)*(lx)*(lyf) + (C x yf)*(C xe y)*(lxe)*(ly) - (C x yf)*(C xe y)*(lxe)*(lyf) - (C x yf)*(C y x)*(lx)*(lxe) + (C x yf)*(C y x)*(lx)*(ly) + (C x yf)*(C y x)*(lxe)^2 - (C x yf)*(C y x)*(lxe)*(ly) + (C x yf)*(C y xe)*(lx)^2 - (C x yf)*(C y xe)*(lx)*(lxe) - (C x yf)*(C y xe)*(lx)*(ly) + (C x yf)*(C y xe)*(lxe)*(ly) + (C x yf)*(C yf x)*(lx)*(lxe) - (C x yf)*(C yf x)*(lx)*(ly) - (C x yf)*(C yf x)*(lxe)^2 + (C x yf)*(C yf x)*(lxe)*(ly) - (C x yf)*(C yf xe)*(lx)^2 + (C x yf)*(C yf xe)*(lx)*(lxe) + (C x yf)*(C yf xe)*(lx)*(ly) - (C x yf)*(C yf xe)*(lxe)*(ly)

/-- Block `(3, 1)`. -/
def bp31 {Λ : Type*} (C : Matrix Λ Λ ℂ) (x xe y yf : Λ) (lx lxe ly lyf : ℂ) : ℂ :=
  0

/-- Block `(3, 2)`. -/
def bp32 {Λ : Type*} (C : Matrix Λ Λ ℂ) (x xe y yf : Λ) (lx lxe ly lyf : ℂ) : ℂ :=
  (C x y)^2*(lx)*(ly) - (C x y)^2*(lx)*(lyf) - (C x y)^2*(lxe)*(ly) + (C x y)^2*(lxe)*(lyf) - (C x y)*(C x yf)*(lx)*(ly) + (C x y)*(C x yf)*(lx)*(lyf) + (C x y)*(C x yf)*(lxe)*(ly) - (C x y)*(C x yf)*(lxe)*(lyf) - (C x y)*(C xe y)*(lx)*(ly) + (C x y)*(C xe y)*(lx)*(lyf) + (C x y)*(C xe y)*(lxe)*(ly) - (C x y)*(C xe y)*(lxe)*(lyf) + (C x y)*(C xe yf)*(lx)*(ly) - (C x y)*(C xe yf)*(lx)*(lyf) - (C x y)*(C xe yf)*(lxe)*(ly) + (C x y)*(C xe yf)*(lxe)*(lyf) + (C x y)*(C y x)*(lx)*(ly) - (C x y)*(C y x)*(lx)*(lyf) - (C x y)*(C y x)*(lxe)*(ly) + (C x y)*(C y x)*(lxe)*(lyf) - (C x y)*(C y xe)*(lx)*(ly) + (C x y)*(C y xe)*(lx)*(lyf) + (C x y)*(C y xe)*(lxe)*(ly) - (C x y)*(C y xe)*(lxe)*(lyf) - (C x y)*(C yf x)*(lx)*(ly) + (C x y)*(C yf x)*(lx)*(lyf) + (C x y)*(C yf x)*(lxe)*(ly) - (C x y)*(C yf x)*(lxe)*(lyf) + (C x y)*(C yf xe)*(lx)*(ly) - (C x y)*(C yf xe)*(lx)*(lyf) - (C x y)*(C yf xe)*(lxe)*(ly) + (C x y)*(C yf xe)*(lxe)*(lyf)

/-- Block `(3, 3)`. -/
def bp33 {Λ : Type*} (C : Matrix Λ Λ ℂ) (x xe y yf : Λ) (lx lxe ly lyf : ℂ) : ℂ :=
  0

section V4b

variable (C : Matrix (Lam d L N) (Lam d L N) ℂ) (e f : Dir d) (x y : Lam d L N) (b : Lam d L N)
  (κ : Fin d)

set_option maxHeartbeats 1000000 in
theorem blk00 : ∑ r' : Fin 3, ∑ s' : Fin 3, bt C b κ κ (v4g e e x) (v4g f f y) 0 0 r' s' =
    bp00 C x (x + dirVec e) y (y + dirVec f) (lift b x κ) (lift b (x + dirVec e) κ)
      (lift b y κ) (lift b (y + dirVec f) κ) := by
  obtain ⟨cx0, cx1, cx2, cx3⟩ := col_v4g b κ e x
  obtain ⟨cy0, cy1, cy2, cy3⟩ := col_v4g b κ f y
  obtain ⟨vx0, vx1, vx2, vx3⟩ := v4g_vals e x
  obtain ⟨vy0, vy1, vy2, vy3⟩ := v4g_vals f y
  simp only [bt, Fin.sum_univ_three, sgn4_0, sgn4_1, sgn4_2, sgn4_3, sgn3_0, sgn3_1,
    sgn3_2, sa4_0_0, sa4_0_1, sa4_0_2, sa4_1_0, sa4_1_1,
    sa4_1_2, sa4_2_0, sa4_2_1, sa4_2_2, sa4_3_0, sa4_3_1, sa4_3_2, sa3_0_0, sa3_0_1, sa3_1_0,
    sa3_1_1, sa3_2_0, sa3_2_1]
  try simp only [cx0, cx1, cx2, cx3, cy0, cy1, cy2, cy3]
  try simp only [Kc, vx0, vx1, vx2, vx3, vy0, vy1, vy2, vy3, pairC_sub_l, pairC_sub_r, pairC_ev_pm,
    pairC_ev_mm, pairC_ev_pp, sub_zero, zero_sub, sub_self, neg_zero, mul_zero, zero_mul, add_zero,
    zero_add, neg_neg]
  try simp only [det4, Matrix.of_apply, Matrix.cons_val]
  try simp only [mul_zero, zero_mul, sub_zero, zero_sub, add_zero, zero_add, neg_zero, mul_one,
    one_mul]
  all_goals (first | (unfold bp00; ring) | (simp only [bp00]) | rfl)

set_option maxHeartbeats 1000000 in
theorem blk01 : ∑ r' : Fin 3, ∑ s' : Fin 3, bt C b κ κ (v4g e e x) (v4g f f y) 0 1 r' s' =
    bp01 C x (x + dirVec e) y (y + dirVec f) (lift b x κ) (lift b (x + dirVec e) κ)
      (lift b y κ) (lift b (y + dirVec f) κ) := by
  obtain ⟨cx0, cx1, cx2, cx3⟩ := col_v4g b κ e x
  obtain ⟨cy0, cy1, cy2, cy3⟩ := col_v4g b κ f y
  obtain ⟨vx0, vx1, vx2, vx3⟩ := v4g_vals e x
  obtain ⟨vy0, vy1, vy2, vy3⟩ := v4g_vals f y
  simp only [bt, Fin.sum_univ_three, sgn4_0, sgn4_1, sgn4_2, sgn4_3, sgn3_0, sgn3_1,
    sgn3_2, sa4_0_0, sa4_0_1, sa4_0_2, sa4_1_0, sa4_1_1,
    sa4_1_2, sa4_2_0, sa4_2_1, sa4_2_2, sa4_3_0, sa4_3_1, sa4_3_2, sa3_0_0, sa3_0_1, sa3_1_0,
    sa3_1_1, sa3_2_0, sa3_2_1]
  try simp only [cx0, cx1, cx2, cx3, cy0, cy1, cy2, cy3]
  try simp only [Kc, vx0, vx1, vx2, vx3, vy0, vy1, vy2, vy3, pairC_sub_l, pairC_sub_r, pairC_ev_pm,
    pairC_ev_mm, pairC_ev_pp, sub_zero, zero_sub, sub_self, neg_zero, mul_zero, zero_mul, add_zero,
    zero_add, neg_neg]
  try simp only [det4, Matrix.of_apply, Matrix.cons_val]
  try simp only [mul_zero, zero_mul, sub_zero, zero_sub, add_zero, zero_add, neg_zero, mul_one,
    one_mul]
  all_goals (first | (unfold bp01; ring) | (simp only [bp01]) | rfl)

set_option maxHeartbeats 1000000 in
theorem blk02 : ∑ r' : Fin 3, ∑ s' : Fin 3, bt C b κ κ (v4g e e x) (v4g f f y) 0 2 r' s' =
    bp02 C x (x + dirVec e) y (y + dirVec f) (lift b x κ) (lift b (x + dirVec e) κ)
      (lift b y κ) (lift b (y + dirVec f) κ) := by
  obtain ⟨cx0, cx1, cx2, cx3⟩ := col_v4g b κ e x
  obtain ⟨cy0, cy1, cy2, cy3⟩ := col_v4g b κ f y
  obtain ⟨vx0, vx1, vx2, vx3⟩ := v4g_vals e x
  obtain ⟨vy0, vy1, vy2, vy3⟩ := v4g_vals f y
  simp only [bt, Fin.sum_univ_three, sgn4_0, sgn4_1, sgn4_2, sgn4_3, sgn3_0, sgn3_1,
    sgn3_2, sa4_0_0, sa4_0_1, sa4_0_2, sa4_1_0, sa4_1_1,
    sa4_1_2, sa4_2_0, sa4_2_1, sa4_2_2, sa4_3_0, sa4_3_1, sa4_3_2, sa3_0_0, sa3_0_1, sa3_1_0,
    sa3_1_1, sa3_2_0, sa3_2_1]
  try simp only [cx0, cx1, cx2, cx3, cy0, cy1, cy2, cy3]
  try simp only [Kc, vx0, vx1, vx2, vx3, vy0, vy1, vy2, vy3, pairC_sub_l, pairC_sub_r, pairC_ev_pm,
    pairC_ev_mm, pairC_ev_pp, sub_zero, zero_sub, sub_self, neg_zero, mul_zero, zero_mul, add_zero,
    zero_add, neg_neg]
  try simp only [det4, Matrix.of_apply, Matrix.cons_val]
  try simp only [mul_zero, zero_mul, sub_zero, zero_sub, add_zero, zero_add, neg_zero, mul_one,
    one_mul]
  all_goals (first | (unfold bp02; ring) | (simp only [bp02]) | rfl)

set_option maxHeartbeats 1000000 in
theorem blk03 : ∑ r' : Fin 3, ∑ s' : Fin 3, bt C b κ κ (v4g e e x) (v4g f f y) 0 3 r' s' =
    bp03 C x (x + dirVec e) y (y + dirVec f) (lift b x κ) (lift b (x + dirVec e) κ)
      (lift b y κ) (lift b (y + dirVec f) κ) := by
  obtain ⟨cx0, cx1, cx2, cx3⟩ := col_v4g b κ e x
  obtain ⟨cy0, cy1, cy2, cy3⟩ := col_v4g b κ f y
  obtain ⟨vx0, vx1, vx2, vx3⟩ := v4g_vals e x
  obtain ⟨vy0, vy1, vy2, vy3⟩ := v4g_vals f y
  simp only [bt, Fin.sum_univ_three, sgn4_0, sgn4_1, sgn4_2, sgn4_3, sgn3_0, sgn3_1,
    sgn3_2, sa4_0_0, sa4_0_1, sa4_0_2, sa4_1_0, sa4_1_1,
    sa4_1_2, sa4_2_0, sa4_2_1, sa4_2_2, sa4_3_0, sa4_3_1, sa4_3_2, sa3_0_0, sa3_0_1, sa3_1_0,
    sa3_1_1, sa3_2_0, sa3_2_1]
  try simp only [cx0, cx1, cx2, cx3, cy0, cy1, cy2, cy3]
  try simp only [Kc, vx0, vx1, vx2, vx3, vy0, vy1, vy2, vy3, pairC_sub_l, pairC_sub_r, pairC_ev_pm,
    pairC_ev_mm, pairC_ev_pp, sub_zero, zero_sub, sub_self, neg_zero, mul_zero, zero_mul, add_zero,
    zero_add, neg_neg]
  try simp only [det4, Matrix.of_apply, Matrix.cons_val]
  try simp only [mul_zero, zero_mul, sub_zero, zero_sub, add_zero, zero_add, neg_zero, mul_one,
    one_mul]
  all_goals (first | (unfold bp03; ring) | (simp only [bp03]) | rfl)

set_option maxHeartbeats 1000000 in
theorem blk10 : ∑ r' : Fin 3, ∑ s' : Fin 3, bt C b κ κ (v4g e e x) (v4g f f y) 1 0 r' s' =
    bp10 C x (x + dirVec e) y (y + dirVec f) (lift b x κ) (lift b (x + dirVec e) κ)
      (lift b y κ) (lift b (y + dirVec f) κ) := by
  obtain ⟨cx0, cx1, cx2, cx3⟩ := col_v4g b κ e x
  obtain ⟨cy0, cy1, cy2, cy3⟩ := col_v4g b κ f y
  obtain ⟨vx0, vx1, vx2, vx3⟩ := v4g_vals e x
  obtain ⟨vy0, vy1, vy2, vy3⟩ := v4g_vals f y
  simp only [bt, Fin.sum_univ_three, sgn4_0, sgn4_1, sgn4_2, sgn4_3, sgn3_0, sgn3_1,
    sgn3_2, sa4_0_0, sa4_0_1, sa4_0_2, sa4_1_0, sa4_1_1,
    sa4_1_2, sa4_2_0, sa4_2_1, sa4_2_2, sa4_3_0, sa4_3_1, sa4_3_2, sa3_0_0, sa3_0_1, sa3_1_0,
    sa3_1_1, sa3_2_0, sa3_2_1]
  try simp only [cx0, cx1, cx2, cx3, cy0, cy1, cy2, cy3]
  try simp only [Kc, vx0, vx1, vx2, vx3, vy0, vy1, vy2, vy3, pairC_sub_l, pairC_sub_r, pairC_ev_pm,
    pairC_ev_mm, pairC_ev_pp, sub_zero, zero_sub, sub_self, neg_zero, mul_zero, zero_mul, add_zero,
    zero_add, neg_neg]
  try simp only [det4, Matrix.of_apply, Matrix.cons_val]
  try simp only [mul_zero, zero_mul, sub_zero, zero_sub, add_zero, zero_add, neg_zero, mul_one,
    one_mul]
  all_goals (first | (unfold bp10; ring) | (simp only [bp10]) | rfl)

set_option maxHeartbeats 1000000 in
theorem blk11 : ∑ r' : Fin 3, ∑ s' : Fin 3, bt C b κ κ (v4g e e x) (v4g f f y) 1 1 r' s' =
    bp11 C x (x + dirVec e) y (y + dirVec f) (lift b x κ) (lift b (x + dirVec e) κ)
      (lift b y κ) (lift b (y + dirVec f) κ) := by
  obtain ⟨cx0, cx1, cx2, cx3⟩ := col_v4g b κ e x
  obtain ⟨cy0, cy1, cy2, cy3⟩ := col_v4g b κ f y
  obtain ⟨vx0, vx1, vx2, vx3⟩ := v4g_vals e x
  obtain ⟨vy0, vy1, vy2, vy3⟩ := v4g_vals f y
  simp only [bt, Fin.sum_univ_three, sgn4_0, sgn4_1, sgn4_2, sgn4_3, sgn3_0, sgn3_1,
    sgn3_2, sa4_0_0, sa4_0_1, sa4_0_2, sa4_1_0, sa4_1_1,
    sa4_1_2, sa4_2_0, sa4_2_1, sa4_2_2, sa4_3_0, sa4_3_1, sa4_3_2, sa3_0_0, sa3_0_1, sa3_1_0,
    sa3_1_1, sa3_2_0, sa3_2_1]
  try simp only [cx0, cx1, cx2, cx3, cy0, cy1, cy2, cy3]
  try simp only [Kc, vx0, vx1, vx2, vx3, vy0, vy1, vy2, vy3, pairC_sub_l, pairC_sub_r, pairC_ev_pm,
    pairC_ev_mm, pairC_ev_pp, sub_zero, zero_sub, sub_self, neg_zero, mul_zero, zero_mul, add_zero,
    zero_add, neg_neg]
  try simp only [det4, Matrix.of_apply, Matrix.cons_val]
  try simp only [mul_zero, zero_mul, sub_zero, zero_sub, add_zero, zero_add, neg_zero, mul_one,
    one_mul]
  all_goals (first | (unfold bp11; ring) | (simp only [bp11]) | rfl)

set_option maxHeartbeats 1000000 in
theorem blk12 : ∑ r' : Fin 3, ∑ s' : Fin 3, bt C b κ κ (v4g e e x) (v4g f f y) 1 2 r' s' =
    bp12 C x (x + dirVec e) y (y + dirVec f) (lift b x κ) (lift b (x + dirVec e) κ)
      (lift b y κ) (lift b (y + dirVec f) κ) := by
  obtain ⟨cx0, cx1, cx2, cx3⟩ := col_v4g b κ e x
  obtain ⟨cy0, cy1, cy2, cy3⟩ := col_v4g b κ f y
  obtain ⟨vx0, vx1, vx2, vx3⟩ := v4g_vals e x
  obtain ⟨vy0, vy1, vy2, vy3⟩ := v4g_vals f y
  simp only [bt, Fin.sum_univ_three, sgn4_0, sgn4_1, sgn4_2, sgn4_3, sgn3_0, sgn3_1,
    sgn3_2, sa4_0_0, sa4_0_1, sa4_0_2, sa4_1_0, sa4_1_1,
    sa4_1_2, sa4_2_0, sa4_2_1, sa4_2_2, sa4_3_0, sa4_3_1, sa4_3_2, sa3_0_0, sa3_0_1, sa3_1_0,
    sa3_1_1, sa3_2_0, sa3_2_1]
  try simp only [cx0, cx1, cx2, cx3, cy0, cy1, cy2, cy3]
  try simp only [Kc, vx0, vx1, vx2, vx3, vy0, vy1, vy2, vy3, pairC_sub_l, pairC_sub_r, pairC_ev_pm,
    pairC_ev_mm, pairC_ev_pp, sub_zero, zero_sub, sub_self, neg_zero, mul_zero, zero_mul, add_zero,
    zero_add, neg_neg]
  try simp only [det4, Matrix.of_apply, Matrix.cons_val]
  try simp only [mul_zero, zero_mul, sub_zero, zero_sub, add_zero, zero_add, neg_zero, mul_one,
    one_mul]
  all_goals (first | (unfold bp12; ring) | (simp only [bp12]) | rfl)

set_option maxHeartbeats 1000000 in
theorem blk13 : ∑ r' : Fin 3, ∑ s' : Fin 3, bt C b κ κ (v4g e e x) (v4g f f y) 1 3 r' s' =
    bp13 C x (x + dirVec e) y (y + dirVec f) (lift b x κ) (lift b (x + dirVec e) κ)
      (lift b y κ) (lift b (y + dirVec f) κ) := by
  obtain ⟨cx0, cx1, cx2, cx3⟩ := col_v4g b κ e x
  obtain ⟨cy0, cy1, cy2, cy3⟩ := col_v4g b κ f y
  obtain ⟨vx0, vx1, vx2, vx3⟩ := v4g_vals e x
  obtain ⟨vy0, vy1, vy2, vy3⟩ := v4g_vals f y
  simp only [bt, Fin.sum_univ_three, sgn4_0, sgn4_1, sgn4_2, sgn4_3, sgn3_0, sgn3_1,
    sgn3_2, sa4_0_0, sa4_0_1, sa4_0_2, sa4_1_0, sa4_1_1,
    sa4_1_2, sa4_2_0, sa4_2_1, sa4_2_2, sa4_3_0, sa4_3_1, sa4_3_2, sa3_0_0, sa3_0_1, sa3_1_0,
    sa3_1_1, sa3_2_0, sa3_2_1]
  try simp only [cx0, cx1, cx2, cx3, cy0, cy1, cy2, cy3]
  try simp only [Kc, vx0, vx1, vx2, vx3, vy0, vy1, vy2, vy3, pairC_sub_l, pairC_sub_r, pairC_ev_pm,
    pairC_ev_mm, pairC_ev_pp, sub_zero, zero_sub, sub_self, neg_zero, mul_zero, zero_mul, add_zero,
    zero_add, neg_neg]
  try simp only [det4, Matrix.of_apply, Matrix.cons_val]
  try simp only [mul_zero, zero_mul, sub_zero, zero_sub, add_zero, zero_add, neg_zero, mul_one,
    one_mul]
  all_goals (first | (unfold bp13; ring) | (simp only [bp13]) | rfl)

set_option maxHeartbeats 1000000 in
theorem blk20 : ∑ r' : Fin 3, ∑ s' : Fin 3, bt C b κ κ (v4g e e x) (v4g f f y) 2 0 r' s' =
    bp20 C x (x + dirVec e) y (y + dirVec f) (lift b x κ) (lift b (x + dirVec e) κ)
      (lift b y κ) (lift b (y + dirVec f) κ) := by
  obtain ⟨cx0, cx1, cx2, cx3⟩ := col_v4g b κ e x
  obtain ⟨cy0, cy1, cy2, cy3⟩ := col_v4g b κ f y
  obtain ⟨vx0, vx1, vx2, vx3⟩ := v4g_vals e x
  obtain ⟨vy0, vy1, vy2, vy3⟩ := v4g_vals f y
  simp only [bt, Fin.sum_univ_three, sgn4_0, sgn4_1, sgn4_2, sgn4_3, sgn3_0, sgn3_1,
    sgn3_2, sa4_0_0, sa4_0_1, sa4_0_2, sa4_1_0, sa4_1_1,
    sa4_1_2, sa4_2_0, sa4_2_1, sa4_2_2, sa4_3_0, sa4_3_1, sa4_3_2, sa3_0_0, sa3_0_1, sa3_1_0,
    sa3_1_1, sa3_2_0, sa3_2_1]
  try simp only [cx0, cx1, cx2, cx3, cy0, cy1, cy2, cy3]
  try simp only [Kc, vx0, vx1, vx2, vx3, vy0, vy1, vy2, vy3, pairC_sub_l, pairC_sub_r, pairC_ev_pm,
    pairC_ev_mm, pairC_ev_pp, sub_zero, zero_sub, sub_self, neg_zero, mul_zero, zero_mul, add_zero,
    zero_add, neg_neg]
  try simp only [det4, Matrix.of_apply, Matrix.cons_val]
  try simp only [mul_zero, zero_mul, sub_zero, zero_sub, add_zero, zero_add, neg_zero, mul_one,
    one_mul]
  all_goals (first | (unfold bp20; ring) | (simp only [bp20]) | rfl)

set_option maxHeartbeats 1000000 in
theorem blk21 : ∑ r' : Fin 3, ∑ s' : Fin 3, bt C b κ κ (v4g e e x) (v4g f f y) 2 1 r' s' =
    bp21 C x (x + dirVec e) y (y + dirVec f) (lift b x κ) (lift b (x + dirVec e) κ)
      (lift b y κ) (lift b (y + dirVec f) κ) := by
  obtain ⟨cx0, cx1, cx2, cx3⟩ := col_v4g b κ e x
  obtain ⟨cy0, cy1, cy2, cy3⟩ := col_v4g b κ f y
  obtain ⟨vx0, vx1, vx2, vx3⟩ := v4g_vals e x
  obtain ⟨vy0, vy1, vy2, vy3⟩ := v4g_vals f y
  simp only [bt, Fin.sum_univ_three, sgn4_0, sgn4_1, sgn4_2, sgn4_3, sgn3_0, sgn3_1,
    sgn3_2, sa4_0_0, sa4_0_1, sa4_0_2, sa4_1_0, sa4_1_1,
    sa4_1_2, sa4_2_0, sa4_2_1, sa4_2_2, sa4_3_0, sa4_3_1, sa4_3_2, sa3_0_0, sa3_0_1, sa3_1_0,
    sa3_1_1, sa3_2_0, sa3_2_1]
  try simp only [cx0, cx1, cx2, cx3, cy0, cy1, cy2, cy3]
  try simp only [Kc, vx0, vx1, vx2, vx3, vy0, vy1, vy2, vy3, pairC_sub_l, pairC_sub_r, pairC_ev_pm,
    pairC_ev_mm, pairC_ev_pp, sub_zero, zero_sub, sub_self, neg_zero, mul_zero, zero_mul, add_zero,
    zero_add, neg_neg]
  try simp only [det4, Matrix.of_apply, Matrix.cons_val]
  try simp only [mul_zero, zero_mul, sub_zero, zero_sub, add_zero, zero_add, neg_zero, mul_one,
    one_mul]
  all_goals (first | (unfold bp21; ring) | (simp only [bp21]) | rfl)

set_option maxHeartbeats 1000000 in
theorem blk22 : ∑ r' : Fin 3, ∑ s' : Fin 3, bt C b κ κ (v4g e e x) (v4g f f y) 2 2 r' s' =
    bp22 C x (x + dirVec e) y (y + dirVec f) (lift b x κ) (lift b (x + dirVec e) κ)
      (lift b y κ) (lift b (y + dirVec f) κ) := by
  obtain ⟨cx0, cx1, cx2, cx3⟩ := col_v4g b κ e x
  obtain ⟨cy0, cy1, cy2, cy3⟩ := col_v4g b κ f y
  obtain ⟨vx0, vx1, vx2, vx3⟩ := v4g_vals e x
  obtain ⟨vy0, vy1, vy2, vy3⟩ := v4g_vals f y
  simp only [bt, Fin.sum_univ_three, sgn4_0, sgn4_1, sgn4_2, sgn4_3, sgn3_0, sgn3_1,
    sgn3_2, sa4_0_0, sa4_0_1, sa4_0_2, sa4_1_0, sa4_1_1,
    sa4_1_2, sa4_2_0, sa4_2_1, sa4_2_2, sa4_3_0, sa4_3_1, sa4_3_2, sa3_0_0, sa3_0_1, sa3_1_0,
    sa3_1_1, sa3_2_0, sa3_2_1]
  try simp only [cx0, cx1, cx2, cx3, cy0, cy1, cy2, cy3]
  try simp only [Kc, vx0, vx1, vx2, vx3, vy0, vy1, vy2, vy3, pairC_sub_l, pairC_sub_r, pairC_ev_pm,
    pairC_ev_mm, pairC_ev_pp, sub_zero, zero_sub, sub_self, neg_zero, mul_zero, zero_mul, add_zero,
    zero_add, neg_neg]
  try simp only [det4, Matrix.of_apply, Matrix.cons_val]
  try simp only [mul_zero, zero_mul, sub_zero, zero_sub, add_zero, zero_add, neg_zero, mul_one,
    one_mul]
  all_goals (first | (unfold bp22; ring) | (simp only [bp22]) | rfl)

set_option maxHeartbeats 1000000 in
theorem blk23 : ∑ r' : Fin 3, ∑ s' : Fin 3, bt C b κ κ (v4g e e x) (v4g f f y) 2 3 r' s' =
    bp23 C x (x + dirVec e) y (y + dirVec f) (lift b x κ) (lift b (x + dirVec e) κ)
      (lift b y κ) (lift b (y + dirVec f) κ) := by
  obtain ⟨cx0, cx1, cx2, cx3⟩ := col_v4g b κ e x
  obtain ⟨cy0, cy1, cy2, cy3⟩ := col_v4g b κ f y
  obtain ⟨vx0, vx1, vx2, vx3⟩ := v4g_vals e x
  obtain ⟨vy0, vy1, vy2, vy3⟩ := v4g_vals f y
  simp only [bt, Fin.sum_univ_three, sgn4_0, sgn4_1, sgn4_2, sgn4_3, sgn3_0, sgn3_1,
    sgn3_2, sa4_0_0, sa4_0_1, sa4_0_2, sa4_1_0, sa4_1_1,
    sa4_1_2, sa4_2_0, sa4_2_1, sa4_2_2, sa4_3_0, sa4_3_1, sa4_3_2, sa3_0_0, sa3_0_1, sa3_1_0,
    sa3_1_1, sa3_2_0, sa3_2_1]
  try simp only [cx0, cx1, cx2, cx3, cy0, cy1, cy2, cy3]
  try simp only [Kc, vx0, vx1, vx2, vx3, vy0, vy1, vy2, vy3, pairC_sub_l, pairC_sub_r, pairC_ev_pm,
    pairC_ev_mm, pairC_ev_pp, sub_zero, zero_sub, sub_self, neg_zero, mul_zero, zero_mul, add_zero,
    zero_add, neg_neg]
  try simp only [det4, Matrix.of_apply, Matrix.cons_val]
  try simp only [mul_zero, zero_mul, sub_zero, zero_sub, add_zero, zero_add, neg_zero, mul_one,
    one_mul]
  all_goals (first | (unfold bp23; ring) | (simp only [bp23]) | rfl)

set_option maxHeartbeats 1000000 in
theorem blk30 : ∑ r' : Fin 3, ∑ s' : Fin 3, bt C b κ κ (v4g e e x) (v4g f f y) 3 0 r' s' =
    bp30 C x (x + dirVec e) y (y + dirVec f) (lift b x κ) (lift b (x + dirVec e) κ)
      (lift b y κ) (lift b (y + dirVec f) κ) := by
  obtain ⟨cx0, cx1, cx2, cx3⟩ := col_v4g b κ e x
  obtain ⟨cy0, cy1, cy2, cy3⟩ := col_v4g b κ f y
  obtain ⟨vx0, vx1, vx2, vx3⟩ := v4g_vals e x
  obtain ⟨vy0, vy1, vy2, vy3⟩ := v4g_vals f y
  simp only [bt, Fin.sum_univ_three, sgn4_0, sgn4_1, sgn4_2, sgn4_3, sgn3_0, sgn3_1,
    sgn3_2, sa4_0_0, sa4_0_1, sa4_0_2, sa4_1_0, sa4_1_1,
    sa4_1_2, sa4_2_0, sa4_2_1, sa4_2_2, sa4_3_0, sa4_3_1, sa4_3_2, sa3_0_0, sa3_0_1, sa3_1_0,
    sa3_1_1, sa3_2_0, sa3_2_1]
  try simp only [cx0, cx1, cx2, cx3, cy0, cy1, cy2, cy3]
  try simp only [Kc, vx0, vx1, vx2, vx3, vy0, vy1, vy2, vy3, pairC_sub_l, pairC_sub_r, pairC_ev_pm,
    pairC_ev_mm, pairC_ev_pp, sub_zero, zero_sub, sub_self, neg_zero, mul_zero, zero_mul, add_zero,
    zero_add, neg_neg]
  try simp only [det4, Matrix.of_apply, Matrix.cons_val]
  try simp only [mul_zero, zero_mul, sub_zero, zero_sub, add_zero, zero_add, neg_zero, mul_one,
    one_mul]
  all_goals (first | (unfold bp30; ring) | (simp only [bp30]) | rfl)

set_option maxHeartbeats 1000000 in
theorem blk31 : ∑ r' : Fin 3, ∑ s' : Fin 3, bt C b κ κ (v4g e e x) (v4g f f y) 3 1 r' s' =
    bp31 C x (x + dirVec e) y (y + dirVec f) (lift b x κ) (lift b (x + dirVec e) κ)
      (lift b y κ) (lift b (y + dirVec f) κ) := by
  obtain ⟨cx0, cx1, cx2, cx3⟩ := col_v4g b κ e x
  obtain ⟨cy0, cy1, cy2, cy3⟩ := col_v4g b κ f y
  obtain ⟨vx0, vx1, vx2, vx3⟩ := v4g_vals e x
  obtain ⟨vy0, vy1, vy2, vy3⟩ := v4g_vals f y
  simp only [bt, Fin.sum_univ_three, sgn4_0, sgn4_1, sgn4_2, sgn4_3, sgn3_0, sgn3_1,
    sgn3_2, sa4_0_0, sa4_0_1, sa4_0_2, sa4_1_0, sa4_1_1,
    sa4_1_2, sa4_2_0, sa4_2_1, sa4_2_2, sa4_3_0, sa4_3_1, sa4_3_2, sa3_0_0, sa3_0_1, sa3_1_0,
    sa3_1_1, sa3_2_0, sa3_2_1]
  try simp only [cx0, cx1, cx2, cx3, cy0, cy1, cy2, cy3]
  try simp only [Kc, vx0, vx1, vx2, vx3, vy0, vy1, vy2, vy3, pairC_sub_l, pairC_sub_r, pairC_ev_pm,
    pairC_ev_mm, pairC_ev_pp, sub_zero, zero_sub, sub_self, neg_zero, mul_zero, zero_mul, add_zero,
    zero_add, neg_neg]
  try simp only [det4, Matrix.of_apply, Matrix.cons_val]
  try simp only [mul_zero, zero_mul, sub_zero, zero_sub, add_zero, zero_add, neg_zero, mul_one,
    one_mul]
  all_goals (first | (unfold bp31; ring) | (simp only [bp31]) | rfl)

set_option maxHeartbeats 1000000 in
theorem blk32 : ∑ r' : Fin 3, ∑ s' : Fin 3, bt C b κ κ (v4g e e x) (v4g f f y) 3 2 r' s' =
    bp32 C x (x + dirVec e) y (y + dirVec f) (lift b x κ) (lift b (x + dirVec e) κ)
      (lift b y κ) (lift b (y + dirVec f) κ) := by
  obtain ⟨cx0, cx1, cx2, cx3⟩ := col_v4g b κ e x
  obtain ⟨cy0, cy1, cy2, cy3⟩ := col_v4g b κ f y
  obtain ⟨vx0, vx1, vx2, vx3⟩ := v4g_vals e x
  obtain ⟨vy0, vy1, vy2, vy3⟩ := v4g_vals f y
  simp only [bt, Fin.sum_univ_three, sgn4_0, sgn4_1, sgn4_2, sgn4_3, sgn3_0, sgn3_1,
    sgn3_2, sa4_0_0, sa4_0_1, sa4_0_2, sa4_1_0, sa4_1_1,
    sa4_1_2, sa4_2_0, sa4_2_1, sa4_2_2, sa4_3_0, sa4_3_1, sa4_3_2, sa3_0_0, sa3_0_1, sa3_1_0,
    sa3_1_1, sa3_2_0, sa3_2_1]
  try simp only [cx0, cx1, cx2, cx3, cy0, cy1, cy2, cy3]
  try simp only [Kc, vx0, vx1, vx2, vx3, vy0, vy1, vy2, vy3, pairC_sub_l, pairC_sub_r, pairC_ev_pm,
    pairC_ev_mm, pairC_ev_pp, sub_zero, zero_sub, sub_self, neg_zero, mul_zero, zero_mul, add_zero,
    zero_add, neg_neg]
  try simp only [det4, Matrix.of_apply, Matrix.cons_val]
  try simp only [mul_zero, zero_mul, sub_zero, zero_sub, add_zero, zero_add, neg_zero, mul_one,
    one_mul]
  all_goals (first | (unfold bp32; ring) | (simp only [bp32]) | rfl)

set_option maxHeartbeats 1000000 in
theorem blk33 : ∑ r' : Fin 3, ∑ s' : Fin 3, bt C b κ κ (v4g e e x) (v4g f f y) 3 3 r' s' =
    bp33 C x (x + dirVec e) y (y + dirVec f) (lift b x κ) (lift b (x + dirVec e) κ)
      (lift b y κ) (lift b (y + dirVec f) κ) := by
  obtain ⟨cx0, cx1, cx2, cx3⟩ := col_v4g b κ e x
  obtain ⟨cy0, cy1, cy2, cy3⟩ := col_v4g b κ f y
  obtain ⟨vx0, vx1, vx2, vx3⟩ := v4g_vals e x
  obtain ⟨vy0, vy1, vy2, vy3⟩ := v4g_vals f y
  simp only [bt, Fin.sum_univ_three, sgn4_0, sgn4_1, sgn4_2, sgn4_3, sgn3_0, sgn3_1,
    sgn3_2, sa4_0_0, sa4_0_1, sa4_0_2, sa4_1_0, sa4_1_1,
    sa4_1_2, sa4_2_0, sa4_2_1, sa4_2_2, sa4_3_0, sa4_3_1, sa4_3_2, sa3_0_0, sa3_0_1, sa3_1_0,
    sa3_1_1, sa3_2_0, sa3_2_1]
  try simp only [cx0, cx1, cx2, cx3, cy0, cy1, cy2, cy3]
  try simp only [Kc, vx0, vx1, vx2, vx3, vy0, vy1, vy2, vy3, pairC_sub_l, pairC_sub_r, pairC_ev_pm,
    pairC_ev_mm, pairC_ev_pp, sub_zero, zero_sub, sub_self, neg_zero, mul_zero, zero_mul, add_zero,
    zero_add, neg_neg]
  try simp only [det4, Matrix.of_apply, Matrix.cons_val]
  try simp only [mul_zero, zero_mul, sub_zero, zero_sub, add_zero, zero_add, neg_zero, mul_one,
    one_mul]
  all_goals (first | (unfold bp33; ring) | (simp only [bp33]) | rfl)

set_option maxHeartbeats 1000000 in
/-- **`μ₄ X₂` of two quartic monomials.** -/
theorem mu4_X2_v4g :
    mu4 b κ κ (X2 C (ExteriorAlgebra.ιMulti ℂ 4 (v4g e e x)) (ExteriorAlgebra.ιMulti ℂ 4 (v4g f f y))) =
      2 * bubPoly C x (x + dirVec e) y (y + dirVec f) (lift b x κ) (lift b (x + dirVec e) κ)
        (lift b y κ) (lift b (y + dirVec f) κ) := by
  rw [mu4_X2_bt]
  simp only [Fin.sum_univ_four]
  rw [blk00, blk01, blk02, blk03, blk10, blk11, blk12, blk13, blk20, blk21, blk22, blk23, blk30,
    blk31, blk32, blk33]
  simp only [bp00, bp01, bp02, bp03, bp10, bp11, bp12, bp13, bp20, bp21, bp22, bp23, bp30, bp31,
    bp32, bp33, bubPoly]
  ring

end V4b

end V4

end

end Step2
