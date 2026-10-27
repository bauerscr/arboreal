import Obs.FlowObsCoeff
import Obs.Consist

/-!
# Lemmas `lem:Vobs-recursion` and `lem:Vobs-bd` (Section `sec:flow-obs`)

## `lem:Vobs-recursion` (`Vobs_recursion_one`, `Vobs_recursion_two`)
The next observable coupling constants `nextObs C j Vo K a b` (Definition `def:V+obs`, read off
at the level of `Λ`: the free flow `Coup.next` of `V_j - Q`) are, up to error terms controlled by
`‖K^obs_j‖_j ≤ e` (`Qcoup_bounds`), the free ones of `lem:Vobs-flow-free`.  The `ab` error terms
carry the factor `1_{j ≥ j_ab}` under the hypothesis `K^{ab}_j(X) = 0` for `X ∈ 𝒮_j` if
`j < j_ab`.  The error terms are bounded by the full `‖K^obs_j‖_j` (the text: `‖K^x_j‖_j`,
`‖K^{ab}_j‖_j`, which are `≤ ‖K^obs_j‖_j`); the constant `C_S` depends only on `d` (it is the
number of small sets containing a point).

**Deviations.**
* Split couplings (`Obs.Coupling`): `q = q_a + q_b`, `r_a, r_b` (text: `r_a = r_b = r/2`).
  Accordingly the `r`-term of the `q` recursion is `-(r_a C(a,a) + r_b C(b,b))` (text:
  `+ r C(0,0)`, the sign deviation recorded in `Obs.Free`).
* Only the `V` part of the couplings is an input of the map (`Coup.toV`), so the `u` parts
  `q_j`, `γ_j` of the input are `0`: the recursions for `q` and `γ` are stated for the
  increments, `q_{j+1} = λ_a λ_b C(a,b) - … + O(…)` (text: `q_{j+1} = q_j + …`, with the
  accumulated `q_j`).
* In the quadratic terms `λ_a λ_b C(a,b)`, `λ_a λ_b C(a,b)^2`, `r_x C(x,x)` the coupling
  constants are those of scale `j + 1` (i.e. of `V_j - Q`), not of scale `j` (the difference is
  a further error term `O(‖K‖ |λ| |C|)`, and the exact form is what the map produces).
* The `N`-independence for `j + 1 < N` is `Obs.nextObs_flowO_consist` (for observable points with
  `8|a|_∞, 8|b|_∞ ≤ L^N`, compared on `Λ_N ⊂ Λ_M` via `Flow.emb`).

## `lem:Vobs-bd` (`Vobs_bd`)
Along the observable flow `flowO` started at `initObs c λ₀` (`λ_{a,0} = λ_{b,0} = λ₀`, all
other couplings `0`, `K_0 = 0`), with covariances satisfying `GoodCov` and
`‖K^obs_k‖_k ≤ e θ^k` for `k < j` (the text: `e = M λ₀ b₀`, `θ = L^{-κ}`):
* `|λ_{x,j} - λ₀| ≤ C_S e / (1 - θ)` (`e:Vobs-bd1`, `e:Vobs-bd3`);
* `|r_{x,j}| ≤ C_S sab e θ^{j_ab} / (1 - θ)` with `sab = 1` (Case 1) resp. `ℓ_{j_ab}^2` (Case 2),
  and `r_{x,j} = 0` for `j ≤ j_ab` (`e:Vobs-bd2`, `e:Vobs-bd5`; `θ^{j_ab} = L^{-κ j_ab} ≍_L |a-b|^{-κ}`
  and `ℓ_{j_ab}^2 ≍_L |a-b|^{-(d-2)}`);
* `|η_j| ≤ 4 Λ̄^2 ℓ_{j ∧ j_ab}^2`, `Λ̄ = |λ₀| + C_S e / (1 - θ)` (`e:Vobs-bd4`);
* the `ab` couplings `r_x`, `η` vanish for `j ≤ min(j_ab, N - 1)` (`flowO_ab`);
* `‖V^obs_j‖_j ≤ 2 Λ̄ + 4 Λ̄^2 + 2 C_S e / (1 - θ)` (`e:Vobs-bd6`; **deviation**: the text has
  `λ₀` instead of `2λ₀`, but a block containing both `a` and `b` carries both `λ_a` and `λ_b`).
-/

namespace Obs

noncomputable section

open Finset Grassmann SA Loc Step LocObs Gen FRD

variable {d L N : ℕ} [NeZero L]

/-! ### Exact form of the recursion -/

section Rec

variable (C : Matrix (Lam d L N) (Lam d L N) ℝ) (j : ℕ) (a b : Lam d L N)

/-- The next coupling constants, Case (1). -/
theorem nextObs_one (Vo : Coup .one) (K : Finset (Lam d L N) → OE .one (Lam d L N)) :
    (nextObs C j Vo K a b : Coup1) =
      ⟨Coup1.la Vo - Coup1.la (Qcoup .one j K a b), Coup1.lb Vo - Coup1.lb (Qcoup .one j K a b),
        -Coup1.qa (Qcoup .one j K a b) + (Coup1.la Vo - Coup1.la (Qcoup .one j K a b)) *
          (Coup1.lb Vo - Coup1.lb (Qcoup .one j K a b)) * C a b / 2 -
          (Coup1.ra Vo - Coup1.ra (Qcoup .one j K a b)) * C a a,
        -Coup1.qb (Qcoup .one j K a b) + (Coup1.la Vo - Coup1.la (Qcoup .one j K a b)) *
          (Coup1.lb Vo - Coup1.lb (Qcoup .one j K a b)) * C a b / 2 -
          (Coup1.rb Vo - Coup1.rb (Qcoup .one j K a b)) * C b b,
        Coup1.ra Vo - Coup1.ra (Qcoup .one j K a b), Coup1.rb Vo - Coup1.rb (Qcoup .one j K a b)⟩ := by
  simp only [nextObs, Wcoup, Coup.next, Coup.sub, Coup.toV, Coup1.next, zero_sub]

/-- The next coupling constants, Case (2) (`Q` has no `η` part). -/
theorem nextObs_two (Vo : Coup .two) (K : Finset (Lam d L N) → OE .two (Lam d L N)) :
    (nextObs C j Vo K a b : Coup2) =
      ⟨Coup2.la Vo - Coup2.la (Qcoup .two j K a b), Coup2.lb Vo - Coup2.lb (Qcoup .two j K a b),
        -Coup2.ga (Qcoup .two j K a b) + (Coup2.la Vo - Coup2.la (Qcoup .two j K a b)) * C a a,
        -Coup2.gb (Qcoup .two j K a b) + (Coup2.lb Vo - Coup2.lb (Qcoup .two j K a b)) * C b b,
        -Coup2.qa (Qcoup .two j K a b) + Coup2.eta Vo * C a b / 2 -
          (Coup2.ra Vo - Coup2.ra (Qcoup .two j K a b)) * C a a -
          (Coup2.la Vo - Coup2.la (Qcoup .two j K a b)) *
            (Coup2.lb Vo - Coup2.lb (Qcoup .two j K a b)) * C a b ^ 2 / 2,
        -Coup2.qb (Qcoup .two j K a b) + Coup2.eta Vo * C a b / 2 -
          (Coup2.rb Vo - Coup2.rb (Qcoup .two j K a b)) * C b b -
          (Coup2.la Vo - Coup2.la (Qcoup .two j K a b)) *
            (Coup2.lb Vo - Coup2.lb (Qcoup .two j K a b)) * C a b ^ 2 / 2,
        Coup2.eta Vo - 2 * (Coup2.la Vo - Coup2.la (Qcoup .two j K a b)) *
          (Coup2.lb Vo - Coup2.lb (Qcoup .two j K a b)) * C a b,
        Coup2.ra Vo - Coup2.ra (Qcoup .two j K a b), Coup2.rb Vo - Coup2.rb (Qcoup .two j K a b)⟩ := by
  have he : Coup2.eta (Qcoup .two j K a b) = 0 := by
    by_cases hj : j + 1 < N
    · simp only [Qcoup, if_pos hj]
    · rw [Qcoup_of_not hj]; rfl
  simp only [nextObs, Wcoup, Coup.next, Coup.sub, Coup.toV, Coup2.next, zero_sub, he, sub_zero]

variable {c : Case} (Vo : Coup c) (K : Finset (Lam d L N) → OE c (Lam d L N))

theorem laOf_nextObs : laOf c (nextObs C j Vo K a b) = laOf c Vo - laOf c (Qcoup c j K a b) := by
  cases c
  · rw [show laOf .one (nextObs C j Vo K a b) = Coup1.la (nextObs C j Vo K a b) from rfl,
      nextObs_one]; rfl
  · rw [show laOf .two (nextObs C j Vo K a b) = Coup2.la (nextObs C j Vo K a b) from rfl,
      nextObs_two]; rfl

theorem lbOf_nextObs : lbOf c (nextObs C j Vo K a b) = lbOf c Vo - lbOf c (Qcoup c j K a b) := by
  cases c
  · rw [show lbOf .one (nextObs C j Vo K a b) = Coup1.lb (nextObs C j Vo K a b) from rfl,
      nextObs_one]; rfl
  · rw [show lbOf .two (nextObs C j Vo K a b) = Coup2.lb (nextObs C j Vo K a b) from rfl,
      nextObs_two]; rfl

theorem raOf_nextObs : raOf c (nextObs C j Vo K a b) = raOf c Vo - raOf c (Qcoup c j K a b) := by
  cases c
  · rw [show raOf .one (nextObs C j Vo K a b) = Coup1.ra (nextObs C j Vo K a b) from rfl,
      nextObs_one]; rfl
  · rw [show raOf .two (nextObs C j Vo K a b) = Coup2.ra (nextObs C j Vo K a b) from rfl,
      nextObs_two]; rfl

theorem rbOf_nextObs : rbOf c (nextObs C j Vo K a b) = rbOf c Vo - rbOf c (Qcoup c j K a b) := by
  cases c
  · rw [show rbOf .one (nextObs C j Vo K a b) = Coup1.rb (nextObs C j Vo K a b) from rfl,
      nextObs_one]; rfl
  · rw [show rbOf .two (nextObs C j Vo K a b) = Coup2.rb (nextObs C j Vo K a b) from rfl,
      nextObs_two]; rfl

theorem norm_etaOf_nextObs_le : ‖etaOf c (nextObs C j Vo K a b)‖ ≤
    ‖etaOf c Vo‖ + 2 * ‖laOf c (nextObs C j Vo K a b)‖ * ‖lbOf c (nextObs C j Vo K a b)‖ *
      |C a b| := by
  cases c
  · simp only [etaOf, norm_zero, zero_add]; positivity
  · rw [show etaOf .two (nextObs C j Vo K a b) = Coup2.eta (nextObs C j Vo K a b) from rfl,
      show laOf .two (nextObs C j Vo K a b) = Coup2.la (nextObs C j Vo K a b) from rfl,
      show lbOf .two (nextObs C j Vo K a b) = Coup2.lb (nextObs C j Vo K a b) from rfl,
      nextObs_two]
    simp only [etaOf]
    refine (norm_sub_le _ _).trans (le_of_eq ?_)
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    norm_num

theorem laOf_toV (W : Coup c) : laOf c (Coup.toV c W) = laOf c W := by cases c <;> rfl
theorem lbOf_toV (W : Coup c) : lbOf c (Coup.toV c W) = lbOf c W := by cases c <;> rfl
theorem raOf_toV (W : Coup c) : raOf c (Coup.toV c W) = raOf c W := by cases c <;> rfl
theorem rbOf_toV (W : Coup c) : rbOf c (Coup.toV c W) = rbOf c W := by cases c <;> rfl

theorem raOf_of_abZero {W : Coup c} (h : AbZero c W) : raOf c W = 0 ∧ rbOf c W = 0 := by
  cases c
  · exact ⟨h.2.2.1, h.2.2.2⟩
  · exact ⟨h.2.2.2.1, h.2.2.2.2⟩

end Rec

/-! ### `lem:Vobs-recursion` -/

/-- `Q`'s coupling constants in Case (1), as an element of `Coup1`. -/
def Qc1 (j : ℕ) (K : Finset (Lam d L N) → OE .one (Lam d L N)) (a b : Lam d L N) : Coup1 :=
  Qcoup .one j K a b

/-- `Q`'s coupling constants in Case (2), as an element of `Coup2`. -/
def Qc2 (j : ℕ) (K : Finset (Lam d L N) → OE .two (Lam d L N)) (a b : Lam d L N) : Coup2 :=
  Qcoup .two j K a b

section RecComp

variable (C : Matrix (Lam d L N) (Lam d L N) ℝ) (j : ℕ) (a b : Lam d L N)

section One

variable (Vo : Coup1) (K : Finset (Lam d L N) → OE .one (Lam d L N))

theorem n1_la : Coup1.la (nextObs (c := .one) C j Vo K a b) = Vo.la - (Qc1 j K a b).la := rfl
theorem n1_lb : Coup1.lb (nextObs (c := .one) C j Vo K a b) = Vo.lb - (Qc1 j K a b).lb := rfl
theorem n1_ra : Coup1.ra (nextObs (c := .one) C j Vo K a b) = Vo.ra - (Qc1 j K a b).ra := rfl
theorem n1_rb : Coup1.rb (nextObs (c := .one) C j Vo K a b) = Vo.rb - (Qc1 j K a b).rb := rfl
theorem n1_qa : Coup1.qa (nextObs (c := .one) C j Vo K a b) = (0 - (Qc1 j K a b).qa) +
    (Vo.la - (Qc1 j K a b).la) * (Vo.lb - (Qc1 j K a b).lb) * C a b / 2 -
    (Vo.ra - (Qc1 j K a b).ra) * C a a := rfl
theorem n1_qb : Coup1.qb (nextObs (c := .one) C j Vo K a b) = (0 - (Qc1 j K a b).qb) +
    (Vo.la - (Qc1 j K a b).la) * (Vo.lb - (Qc1 j K a b).lb) * C a b / 2 -
    (Vo.rb - (Qc1 j K a b).rb) * C b b := rfl

end One

section Two

variable (Vo : Coup2) (K : Finset (Lam d L N) → OE .two (Lam d L N))

theorem Qc2_eta (K : Finset (Lam d L N) → OE .two (Lam d L N)) : (Qc2 j K a b).eta = 0 := by
  unfold Qc2
  by_cases hj : j + 1 < N
  · simp only [Qcoup, if_pos hj]
  · rw [Qcoup_of_not hj]; rfl

theorem n2_la : Coup2.la (nextObs (c := .two) C j Vo K a b) = Vo.la - (Qc2 j K a b).la := rfl
theorem n2_lb : Coup2.lb (nextObs (c := .two) C j Vo K a b) = Vo.lb - (Qc2 j K a b).lb := rfl
theorem n2_ra : Coup2.ra (nextObs (c := .two) C j Vo K a b) = Vo.ra - (Qc2 j K a b).ra := rfl
theorem n2_rb : Coup2.rb (nextObs (c := .two) C j Vo K a b) = Vo.rb - (Qc2 j K a b).rb := rfl
theorem n2_ga : Coup2.ga (nextObs (c := .two) C j Vo K a b) = (0 - (Qc2 j K a b).ga) +
    (Vo.la - (Qc2 j K a b).la) * C a a := rfl
theorem n2_gb : Coup2.gb (nextObs (c := .two) C j Vo K a b) = (0 - (Qc2 j K a b).gb) +
    (Vo.lb - (Qc2 j K a b).lb) * C b b := rfl
theorem n2_eta : Coup2.eta (nextObs (c := .two) C j Vo K a b) = (Vo.eta - (Qc2 j K a b).eta) -
    2 * (Vo.la - (Qc2 j K a b).la) * (Vo.lb - (Qc2 j K a b).lb) * C a b := rfl
theorem n2_qa : Coup2.qa (nextObs (c := .two) C j Vo K a b) = (0 - (Qc2 j K a b).qa) +
    (Vo.eta - (Qc2 j K a b).eta) * C a b / 2 - (Vo.ra - (Qc2 j K a b).ra) * C a a -
    (Vo.la - (Qc2 j K a b).la) * (Vo.lb - (Qc2 j K a b).lb) * C a b ^ 2 / 2 := rfl
theorem n2_qb : Coup2.qb (nextObs (c := .two) C j Vo K a b) = (0 - (Qc2 j K a b).qb) +
    (Vo.eta - (Qc2 j K a b).eta) * C a b / 2 - (Vo.rb - (Qc2 j K a b).rb) * C b b -
    (Vo.la - (Qc2 j K a b).la) * (Vo.lb - (Qc2 j K a b).lb) * C a b ^ 2 / 2 := rfl

end Two

end RecComp

/-- **Lemma `lem:Vobs-recursion`, Case (1)** (see the module docstring for the deviations):
with `δ := 1_{j ≥ j_ab}` and `‖K^obs_j‖_j ≤ e`,
`λ_{x,j+1} = λ_{x,j} + O(e)`, `q_{j+1} = λ_{a,j+1} λ_{b,j+1} C(a,b) - (r_{a,j+1} C(a,a) +
r_{b,j+1} C(b,b)) + O(ℓ_{ab,j}^{-1} e δ)`, `r_{x,j+1} = r_{x,j} + O(ℓ_{ab,j}^{-1} ℓ_j^{-2} e δ)`
(`ℓ_{ab,j}^{-1} ℓ_j^{-2} = 1`), with the constant `C_S` of `Qcoup_bounds`. -/
theorem Vobs_recursion_one (d : ℕ) : ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ (L : ℕ) [NeZero L] (N j : ℕ) (ℓ₀ : ℝ),
    0 < ℓ₀ → ∀ (C : Matrix (Lam d L N) (Lam d L N) ℝ) (Vo : Coup1)
    (K : Finset (Lam d L N) → OE .one (Lam d L N)) (a b : Lam d L N) (A : ℝ), 1 ≤ A →
    ∀ e : ℝ, 0 ≤ e → KnormObs .one ℓ₀ a b j A K ≤ ENNReal.ofReal e →
    (j < coal L a b → ∀ Y, IsSmall j Y → (K Y : SA .one (Lam d L N)).ab = 0) →
      ‖Coup1.la (nextObs (c := .one) C j Vo K a b) - Vo.la‖ ≤ Cs * e ∧
      ‖Coup1.lb (nextObs (c := .one) C j Vo K a b) - Vo.lb‖ ≤ Cs * e ∧
      ‖(Coup1.qa (nextObs (c := .one) C j Vo K a b) + Coup1.qb (nextObs (c := .one) C j Vo K a b)) -
          (Coup1.la (nextObs (c := .one) C j Vo K a b) *
              Coup1.lb (nextObs (c := .one) C j Vo K a b) * C a b -
            (Coup1.ra (nextObs (c := .one) C j Vo K a b) * C a a +
              Coup1.rb (nextObs (c := .one) C j Vo K a b) * C b b))‖ ≤
        2 * Cs * (ellab .one (ellj d L ℓ₀ j) (ellj d L ℓ₀ (jwedge j (coal L a b))))⁻¹ * e *
          (if coal L a b ≤ j then 1 else 0) ∧
      ‖Coup1.ra (nextObs (c := .one) C j Vo K a b) - Vo.ra‖ ≤
        Cs * e * (if coal L a b ≤ j then 1 else 0) ∧
      ‖Coup1.rb (nextObs (c := .one) C j Vo K a b) - Vo.rb‖ ≤
        Cs * e * (if coal L a b ≤ j then 1 else 0) := by
  obtain ⟨Cs, hCs, hQ⟩ := Qcoup_bounds d
  refine ⟨Cs, hCs, ?_⟩
  intro L _ N j ℓ₀ hℓ₀ C Vo K a b A hA e he0 he hab0
  obtain ⟨h1, h2, -, -, h5, h6, h7, h8⟩ := hQ L N j ℓ₀ hℓ₀ .one K a b A hA e he0 he
  have g1 : ‖(Qc1 j K a b).la‖ ≤ Cs * e := h1
  have g2 : ‖(Qc1 j K a b).lb‖ ≤ Cs * e := h2
  have g5 : ‖(Qc1 j K a b).qa‖ ≤
      Cs * (ellab .one (ellj d L ℓ₀ j) (ellj d L ℓ₀ (jwedge j (coal L a b))))⁻¹ * e := h5
  have g6 : ‖(Qc1 j K a b).qb‖ ≤
      Cs * (ellab .one (ellj d L ℓ₀ j) (ellj d L ℓ₀ (jwedge j (coal L a b))))⁻¹ * e := h6
  have g7 : ‖(Qc1 j K a b).ra‖ ≤ Cs * 1 * e := h7
  have g8 : ‖(Qc1 j K a b).rb‖ ≤ Cs * 1 * e := h8
  rw [mul_one] at g7 g8
  have hz : j < coal L a b → (Qc1 j K a b).qa = 0 ∧ (Qc1 j K a b).qb = 0 ∧
      (Qc1 j K a b).ra = 0 ∧ (Qc1 j K a b).rb = 0 := fun hj =>
    Qcoup_abZero (a := a) (b := b) (hab0 hj)
  rw [n1_la, n1_lb, n1_qa, n1_qb, n1_ra, n1_rb]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [show Vo.la - (Qc1 j K a b).la - Vo.la = -(Qc1 j K a b).la by ring, norm_neg]; exact g1
  · rw [show Vo.lb - (Qc1 j K a b).lb - Vo.lb = -(Qc1 j K a b).lb by ring, norm_neg]; exact g2
  · rw [show ∀ x y u v w p q r s : ℂ, ((0 - x) + u * v * w / 2 - p * q) + ((0 - y) + u * v * w / 2 -
        r * s) - (u * v * w - (p * q + r * s)) = -(x + y) from fun _ _ _ _ _ _ _ _ _ => by ring,
      norm_neg]
    split_ifs with hj
    · rw [mul_one]; refine (norm_add_le _ _).trans ?_; linarith
    · obtain ⟨hqa, hqb, -, -⟩ := hz (by omega)
      rw [hqa, hqb, add_zero, norm_zero, mul_zero]
  · rw [show Vo.ra - (Qc1 j K a b).ra - Vo.ra = -(Qc1 j K a b).ra by ring, norm_neg]
    split_ifs with hj
    · rw [mul_one]; exact g7
    · rw [(hz (by omega)).2.2.1, norm_zero, mul_zero]
  · rw [show Vo.rb - (Qc1 j K a b).rb - Vo.rb = -(Qc1 j K a b).rb by ring, norm_neg]
    split_ifs with hj
    · rw [mul_one]; exact g8
    · rw [(hz (by omega)).2.2.2, norm_zero, mul_zero]

/-- **Lemma `lem:Vobs-recursion`, Case (2)** (see the module docstring for the deviations):
with `δ := 1_{j ≥ j_ab}`, `‖K^obs_j‖_j ≤ e`, and the couplings `λ', r'` of scale `j + 1`:
`λ_{x,j+1} = λ_{x,j} + O(e)`, `γ_{x,j+1} = λ'_x C(x,x) + O(ℓ_j^2 e)`,
`q_{j+1} = η_j C(a,b) - λ'_a λ'_b C(a,b)^2 - (r'_a C(a,a) + r'_b C(b,b)) + O(ℓ_{ab,j}^{-1} e δ)`,
`η_{j+1} = η_j - 2 λ'_a λ'_b C(a,b)` (exactly), and
`r_{x,j+1} = r_{x,j} + O(ℓ_{ab,j}^{-1} ℓ_j^{-2} e δ)`, `ℓ_{ab,j}^{-1} ℓ_j^{-2} = ℓ_{j ∧ j_ab}^2`. -/
theorem Vobs_recursion_two (d : ℕ) : ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ (L : ℕ) [NeZero L] (N j : ℕ) (ℓ₀ : ℝ),
    0 < ℓ₀ → ∀ (C : Matrix (Lam d L N) (Lam d L N) ℝ) (Vo : Coup2)
    (K : Finset (Lam d L N) → OE .two (Lam d L N)) (a b : Lam d L N) (A : ℝ), 1 ≤ A →
    ∀ e : ℝ, 0 ≤ e → KnormObs .two ℓ₀ a b j A K ≤ ENNReal.ofReal e →
    (j < coal L a b → ∀ Y, IsSmall j Y → (K Y : SA .two (Lam d L N)).ab = 0) →
      ‖Coup2.la (nextObs (c := .two) C j Vo K a b) - Vo.la‖ ≤ Cs * e ∧
      ‖Coup2.lb (nextObs (c := .two) C j Vo K a b) - Vo.lb‖ ≤ Cs * e ∧
      ‖Coup2.ga (nextObs (c := .two) C j Vo K a b) -
          Coup2.la (nextObs (c := .two) C j Vo K a b) * C a a‖ ≤ Cs * ellj d L ℓ₀ j ^ 2 * e ∧
      ‖Coup2.gb (nextObs (c := .two) C j Vo K a b) -
          Coup2.lb (nextObs (c := .two) C j Vo K a b) * C b b‖ ≤ Cs * ellj d L ℓ₀ j ^ 2 * e ∧
      ‖(Coup2.qa (nextObs (c := .two) C j Vo K a b) + Coup2.qb (nextObs (c := .two) C j Vo K a b)) -
          (Vo.eta * C a b -
            Coup2.la (nextObs (c := .two) C j Vo K a b) *
              Coup2.lb (nextObs (c := .two) C j Vo K a b) * C a b ^ 2 -
            (Coup2.ra (nextObs (c := .two) C j Vo K a b) * C a a +
              Coup2.rb (nextObs (c := .two) C j Vo K a b) * C b b))‖ ≤
        2 * Cs * (ellab .two (ellj d L ℓ₀ j) (ellj d L ℓ₀ (jwedge j (coal L a b))))⁻¹ * e *
          (if coal L a b ≤ j then 1 else 0) ∧
      Coup2.eta (nextObs (c := .two) C j Vo K a b) = Vo.eta -
        2 * Coup2.la (nextObs (c := .two) C j Vo K a b) *
          Coup2.lb (nextObs (c := .two) C j Vo K a b) * C a b ∧
      ‖Coup2.ra (nextObs (c := .two) C j Vo K a b) - Vo.ra‖ ≤
        Cs * ellj d L ℓ₀ (jwedge j (coal L a b)) ^ 2 * e * (if coal L a b ≤ j then 1 else 0) ∧
      ‖Coup2.rb (nextObs (c := .two) C j Vo K a b) - Vo.rb‖ ≤
        Cs * ellj d L ℓ₀ (jwedge j (coal L a b)) ^ 2 * e * (if coal L a b ≤ j then 1 else 0) := by
  obtain ⟨Cs, hCs, hQ⟩ := Qcoup_bounds d
  refine ⟨Cs, hCs, ?_⟩
  intro L _ N j ℓ₀ hℓ₀ C Vo K a b A hA e he0 he hab0
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hQ L N j ℓ₀ hℓ₀ .two K a b A hA e he0 he
  have g1 : ‖(Qc2 j K a b).la‖ ≤ Cs * e := h1
  have g2 : ‖(Qc2 j K a b).lb‖ ≤ Cs * e := h2
  have g3 : ‖(Qc2 j K a b).ga‖ ≤ Cs * ellj d L ℓ₀ j ^ 2 * e := h3
  have g4 : ‖(Qc2 j K a b).gb‖ ≤ Cs * ellj d L ℓ₀ j ^ 2 * e := h4
  have g5 : ‖(Qc2 j K a b).qa‖ ≤
      Cs * (ellab .two (ellj d L ℓ₀ j) (ellj d L ℓ₀ (jwedge j (coal L a b))))⁻¹ * e := h5
  have g6 : ‖(Qc2 j K a b).qb‖ ≤
      Cs * (ellab .two (ellj d L ℓ₀ j) (ellj d L ℓ₀ (jwedge j (coal L a b))))⁻¹ * e := h6
  have g7 : ‖(Qc2 j K a b).ra‖ ≤ Cs * ellj d L ℓ₀ (jwedge j (coal L a b)) ^ 2 * e := h7
  have g8 : ‖(Qc2 j K a b).rb‖ ≤ Cs * ellj d L ℓ₀ (jwedge j (coal L a b)) ^ 2 * e := h8
  have hz : j < coal L a b → (Qc2 j K a b).qa = 0 ∧ (Qc2 j K a b).qb = 0 ∧
      (Qc2 j K a b).eta = 0 ∧ (Qc2 j K a b).ra = 0 ∧ (Qc2 j K a b).rb = 0 := fun hj =>
    Qcoup_abZero (a := a) (b := b) (hab0 hj)
  have he' := Qc2_eta j a b K
  rw [n2_la, n2_lb, n2_ga, n2_gb, n2_qa, n2_qb, n2_eta, n2_ra, n2_rb, he']
  refine ⟨?_, ?_, ?_, ?_, ?_, by ring, ?_, ?_⟩
  · rw [show Vo.la - (Qc2 j K a b).la - Vo.la = -(Qc2 j K a b).la by ring, norm_neg]; exact g1
  · rw [show Vo.lb - (Qc2 j K a b).lb - Vo.lb = -(Qc2 j K a b).lb by ring, norm_neg]; exact g2
  · rw [show ∀ x u w : ℂ, (0 - x) + u * w - u * w = -x from fun _ _ _ => by ring, norm_neg]
    exact g3
  · rw [show ∀ x u w : ℂ, (0 - x) + u * w - u * w = -x from fun _ _ _ => by ring, norm_neg]
    exact g4
  · rw [show ∀ x y u v w p q r s t : ℂ,
        ((0 - x) + (t - 0) * w / 2 - p * q - u * v * w ^ 2 / 2) +
          ((0 - y) + (t - 0) * w / 2 - r * s - u * v * w ^ 2 / 2) -
          (t * w - u * v * w ^ 2 - (p * q + r * s)) = -(x + y) from
        fun _ _ _ _ _ _ _ _ _ _ => by ring, norm_neg]
    split_ifs with hj
    · rw [mul_one]; refine (norm_add_le _ _).trans ?_; linarith
    · obtain ⟨hqa, hqb, -, -, -⟩ := hz (by omega)
      rw [hqa, hqb, add_zero, norm_zero, mul_zero]
  · rw [show Vo.ra - (Qc2 j K a b).ra - Vo.ra = -(Qc2 j K a b).ra by ring, norm_neg]
    split_ifs with hj
    · rw [mul_one]; exact g7
    · rw [(hz (by omega)).2.2.2.1, norm_zero, mul_zero]
  · rw [show Vo.rb - (Qc2 j K a b).rb - Vo.rb = -(Qc2 j K a b).rb by ring, norm_neg]
    split_ifs with hj
    · rw [mul_one]; exact g8
    · rw [(hz (by omega)).2.2.2.2, norm_zero, mul_zero]

/-! ### Geometric sums and the covariance at `(a, b)` -/

theorem sum_geom_ite_eq {θ : ℝ} (hθ1 : θ ≠ 1) (m : ℕ) : ∀ j : ℕ,
    ∑ k ∈ range j, (if m ≤ k then θ ^ k else 0) = (θ ^ m - θ ^ max m j) / (1 - θ)
  | 0 => by simp
  | j + 1 => by
    rw [sum_range_succ, sum_geom_ite_eq hθ1 m j]
    have h1 : (1 - θ) ≠ 0 := sub_ne_zero.2 (Ne.symm hθ1)
    split_ifs with h
    · rw [max_eq_right h, max_eq_right (by omega : m ≤ j + 1)]
      field_simp; ring
    · rw [max_eq_left (by omega : j ≤ m), max_eq_left (by omega : j + 1 ≤ m), add_zero]

theorem mul_frac_le {K u v t : ℝ} (hK : 0 ≤ K) (ht : 0 < t) (huv : u ≤ v) :
    K * (u / t) ≤ K * v / t := by
  rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right huv ht.le) hK

theorem geom_step {θ : ℝ} (hθ1 : θ < 1) (x : ℝ) (j : ℕ) :
    (x - θ ^ j) / (1 - θ) + θ ^ j = (x - θ ^ (j + 1)) / (1 - θ) := by
  have h1 : (1 - θ) ≠ 0 := by linarith
  field_simp; ring

theorem ellj_sq {ℓ₀ : ℝ} (n : ℕ) :
    ellj d (L : ℝ) ℓ₀ n ^ 2 = ℓ₀ ^ 2 * ((L : ℝ) ^ (-((d : ℝ) - 2))) ^ n := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  unfold ellj
  rw [mul_pow, ← Real.rpow_natCast ((L : ℝ) ^ (-((d : ℝ) - 2) * n / 2)) 2, ← Real.rpow_mul hL.le,
    ← Real.rpow_natCast ((L : ℝ) ^ (-((d : ℝ) - 2))) n, ← Real.rpow_mul hL.le]
  congr 2; push_cast; ring

/-- `∑_{k < j} |C_{k+1}(a, b)| ≤ 2 ℓ_{j ∧ j_ab}^2`: by finite range only the scales
`k + 1 > j_ab` (and the last one) contribute, and `|C_{k+1}(a,b)| ≤ ℓ_{k+1}^2`. -/
theorem sum_cov_le (hd : 3 ≤ d) (hL : 2 ≤ L) {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) {msq : ℝ}
    (hC : ∀ k < N, GoodCov k ℓ₀ (Flow.covAt d L N msq k)) (a b : Lam d L N) {j : ℕ} (hj : j ≤ N) :
    ∑ k ∈ range j, |Flow.covAt d L N msq k a b| ≤ 2 * ellj d L ℓ₀ (min j (coal L a b)) ^ 2 := by
  set m := min j (coal L a b) with hm
  set ρ : ℝ := (L : ℝ) ^ (-((d : ℝ) - 2)) with hρ
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ ≤ 1 / 2 := by
    have h1 : ρ ≤ (L : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by have h3 : (3 : ℝ) ≤ d := (by exact_mod_cast hd); linarith)
    rw [Real.rpow_neg_one] at h1
    have h2 : (L : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div]; exact div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        (by exact_mod_cast hL)
    linarith
  have step1 : ∀ k ∈ range j, |Flow.covAt d L N msq k a b| ≤
      ℓ₀ ^ 2 * (if m ≤ k + 1 then ρ ^ (k + 1) else 0) := by
    intro k hk
    rw [mem_range] at hk
    by_cases hmk : m ≤ k + 1
    · rw [if_pos hmk, ← ellj_sq]
      exact abs_cov_le hℓ₀ (hC k (by omega)) a b
    · have : Flow.covAt d L N msq k a b = 0 :=
        C_eq_zero_of_lt_coal (hC k (by omega)) (by omega) (by omega)
      rw [this, abs_zero, if_neg hmk, mul_zero]
  have step2 : ∑ k ∈ range j, (if m ≤ k + 1 then ρ ^ (k + 1) else 0) ≤ 2 * ρ ^ m := by
    have e1 := sum_range_succ' (fun k => if m ≤ k then ρ ^ k else 0) j
    rw [sum_geom_ite_eq (by linarith) m (j + 1)] at e1
    have e2 : ∑ k ∈ range j, (if m ≤ k + 1 then ρ ^ (k + 1) else 0) ≤
        (ρ ^ m - ρ ^ max m (j + 1)) / (1 - ρ) := by
      rw [e1]
      have : 0 ≤ (if m ≤ 0 then ρ ^ 0 else 0) := by split_ifs <;> positivity
      linarith
    refine e2.trans ?_
    rw [div_le_iff₀ (by linarith)]
    have : 0 ≤ ρ ^ max m (j + 1) := by positivity
    have : 0 ≤ ρ ^ m := by positivity
    nlinarith
  calc ∑ k ∈ range j, |Flow.covAt d L N msq k a b|
      ≤ ∑ k ∈ range j, ℓ₀ ^ 2 * (if m ≤ k + 1 then ρ ^ (k + 1) else 0) := sum_le_sum step1
    _ = ℓ₀ ^ 2 * ∑ k ∈ range j, (if m ≤ k + 1 then ρ ^ (k + 1) else 0) := by rw [mul_sum]
    _ ≤ ℓ₀ ^ 2 * (2 * ρ ^ m) := mul_le_mul_of_nonneg_left step2 (by positivity)
    _ = 2 * ellj d L ℓ₀ m ^ 2 := by rw [ellj_sq]; ring

/-! ### The `ab` components below `j_ab` along the flow -/

/-- The initial observable coupling constants `λ_{a,0} = λ_{b,0} = l₀`, all others `0`. -/
def initObs : (c : Case) → ℂ → Coup c
  | .one, l => (⟨l, l, 0, 0, 0, 0⟩ : Coup1)
  | .two, l => (⟨l, l, 0, 0, 0, 0, 0, 0, 0⟩ : Coup2)

section FlowAB

variable {c : Case} {msq ℓ₀ : ℝ} (V₀ : Vcoup) (l₀ : ℂ) (a b : Lam d L N)

/-- Along the observable flow started at `initObs`, `V_j` has no `ab` couplings and
`K_j ∈ 𝒩^obs_sym` for `j ≤ min(j_ab, N - 1)` (`flow_ab`). -/
theorem flowO_ab (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L)
    (hC : ∀ k < N, GoodCov k ℓ₀ (Flow.covAt d L N msq k)) :
    ∀ k ≤ min (coal L a b) (N - 1),
      AbZeroV c (flowO d L c N msq V₀ (initObs c l₀) a b k).1 ∧
        InKO c False a b k (flowO d L c N msq V₀ (initObs c l₀) a b k).2 := by
  refine flow_ab a b hd (Flow.covAt d L N msq) (fun k => (Flow.flowN d L N msq V₀ k).1)
    (fun k => (flowO d L c N msq V₀ (initObs c l₀) a b k).1)
    (fun k => (flowO d L c N msq V₀ (initObs c l₀) a b k).2) (fun k => rfl)
    (fun k X hX => ?_) ?_ (fun X _ => ?_)
    (fun k hk => C_eq_zero_of_lt_coal (hC k (by omega)) (by omega) (by omega))
    (fun k hk => far_of_lt_coal hL (by omega))
  · show restrO (k + 1) _ X = _
    exact restrO_of_conn _ hX
  · cases c
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl⟩
  · show (0 : OE c (Lam d L N)) ∈ _
    exact zero_mem _

/-- `K^{ab}_k(Y) = 0` for small `Y` and `k < j_ab` along the flow. -/
theorem abSmall_flowO (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L)
    (hC : ∀ k < N, GoodCov k ℓ₀ (Flow.covAt d L N msq k)) {k : ℕ} (hkN : k < N)
    (hk : k < coal L a b) {Y : Finset (Lam d L N)} (hY : IsSmall k Y) :
    ((flowO d L c N msq V₀ (initObs c l₀) a b k).2 Y : SA c (Lam d L N)).ab = 0 :=
  ab_eq_zero_of_far (flowO_ab V₀ l₀ a b hd hL hC k (by omega)).2 (far_of_lt_coal hL hk) hY

end FlowAB

/-! ### The norm of `V^obs(B)` in terms of the coupling constants -/

section VNorm

theorem Tj_ind_smul_le (L' : ℝ) (j : ℕ) (ℓ : ℝ) (P : Prop) [Decidable P] (F : Alg d L N) :
    Tj d L' j ℓ (ind P • F) ≤ Tj d L' j ℓ F := by
  by_cases hP : P
  · rw [ind_pos hP, one_smul]
  · rw [ind_neg hP, zero_smul, Tj_zero]; exact zero_le

theorem Tj_split_le {L' : ℝ} {j : ℕ} {ℓ : ℝ} (P Q : Prop) [Decidable P] [Decidable Q]
    {F G : Alg d L N} {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hF : Tj d L' j ℓ F ≤ ENNReal.ofReal x)
    (hG : Tj d L' j ℓ G ≤ ENNReal.ofReal y) :
    Tj d L' j ℓ (ind P • F + ind Q • G) ≤ ENNReal.ofReal (x + y) := by
  rw [ENNReal.ofReal_add hx hy]
  exact (tNorm_add_le _ _).trans (add_le_add ((Tj_ind_smul_le L' j ℓ P F).trans hF)
    ((Tj_ind_smul_le L' j ℓ Q G).trans hG))

theorem Tj_smul_le_of {L' : ℝ} {j : ℕ} {ℓ : ℝ} (r : ℂ) {F : Alg d L N} {t : ℝ}
    (hF : Tj d L' j ℓ F ≤ ENNReal.ofReal t) : Tj d L' j ℓ (r • F) ≤ ENNReal.ofReal (‖r‖ * t) := by
  rw [ENNReal.ofReal_mul (norm_nonneg _)]
  exact (tNorm_smul_le r F).trans (by gcongr)

theorem Tj_add_le_of {L' : ℝ} {j : ℕ} {ℓ : ℝ} {F G : Alg d L N} {x y : ℝ} (hx : 0 ≤ x)
    (hy : 0 ≤ y) (hF : Tj d L' j ℓ F ≤ ENNReal.ofReal x) (hG : Tj d L' j ℓ G ≤ ENNReal.ofReal y) :
    Tj d L' j ℓ (F + G) ≤ ENNReal.ofReal (x + y) := by
  rw [ENNReal.ofReal_add hx hy]
  exact (tNorm_add_le _ _).trans (add_le_add hF hG)

theorem oNorm_le_ofReal {c : Case} {Λ : Type*} {nrm : Grassmann.N Λ → ENNReal} {w : Wt}
    {F : SA c Λ} {wa wab xa xb xab : ℝ} (hwa : 0 ≤ wa) (hwab : 0 ≤ wab) (hxa : 0 ≤ xa)
    (hxb : 0 ≤ xb) (hxab : 0 ≤ xab) (h_a : w.a = ENNReal.ofReal wa)
    (h_b : w.b = ENNReal.ofReal wa) (h_ab : w.ab = ENNReal.ofReal wab) (he : nrm F.e = 0)
    (ha : nrm F.a ≤ ENNReal.ofReal xa) (hb : nrm F.b ≤ ENNReal.ofReal xb)
    (hab : nrm F.ab ≤ ENNReal.ofReal xab) :
    oNorm nrm w F ≤ ENNReal.ofReal (wa * xa + wa * xb + wab * xab) := by
  unfold oNorm
  rw [he, h_a, h_b, h_ab, zero_add, ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hwa,
    ENNReal.ofReal_mul hwa, ENNReal.ofReal_mul hwab]
  gcongr

variable {c : Case} {ℓ₀ : ℝ} (a b : Lam d L N)

/-- `‖V^obs(X)‖_{T_j(ℓ_j)} ≤ |λ_a| + |λ_b| + ℓ_{ab,j} ℓ_j^2 (|η| + |r_a| + |r_b|)` (the `q`, `γ`
terms are not part of `V^obs`). -/
theorem nrmj_splitO_toV_coup_le (hℓ₀ : 0 < ℓ₀) (V : Coup c) (j : ℕ) (X : Finset (Lam d L N)) :
    nrmj c ℓ₀ a b j (splitO c (Coup.toV c V) a b X) ≤ ENNReal.ofReal (‖laOf c V‖ + ‖lbOf c V‖ +
      ellab c (ellj d L ℓ₀ j) (ellj d L ℓ₀ (jwedge j (coal L a b))) * ellj d L ℓ₀ j ^ 2 *
        (‖etaOf c V‖ + ‖raOf c V‖ + ‖rbOf c V‖)) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set ℓ := ellj d L ℓ₀ j with hℓdef
  set ℓ' := ellj d L ℓ₀ (jwedge j (coal L a b)) with hℓ'def
  have hℓ : 0 < ℓ := ellj_pos hL0 hℓ₀ j
  have hℓ' : 0 < ℓ' := ellj_pos hL0 hℓ₀ _
  have hh := Lpow_pos (L := L) j
  have hpsb : ∀ x : Lam d L N, Tj d (L : ℝ) j ℓ (psibar x) ≤ ENNReal.ofReal ℓ := fun x =>
    le_of_eq (tNorm_psibar hh hℓ x)
  have hψ : ∀ x : Lam d L N, Tj d (L : ℝ) j ℓ (psi x) ≤ ENNReal.ofReal ℓ := fun x =>
    le_of_eq (tNorm_psi hh hℓ x)
  have hpp : ∀ x y : Lam d L N, Tj d (L : ℝ) j ℓ (psibar x * psi y) ≤ ENNReal.ofReal (ℓ ^ 2) :=
    fun x y => (tNorm_mul_le hh hℓ _ _).trans (by
      rw [sq, ENNReal.ofReal_mul hℓ.le]; exact mul_le_mul' (hpsb x) (hψ y))
  have hnx : Tj d (L : ℝ) j ℓ (nx a b) ≤ ENNReal.ofReal (ℓ ^ 2 + ℓ ^ 2) :=
    Tj_add_le_of (by positivity) (by positivity) (hpp a b) (hpp b a)
  have h0 : Tj d (L : ℝ) j ℓ (0 : Alg d L N) ≤ ENNReal.ofReal 0 := by
    rw [Tj_zero, ENNReal.ofReal_zero]
  have hab0 : 0 ≤ ellab c ℓ ℓ' := by cases c <;> simp only [ellab] <;> positivity
  simp only [nrmj, normj, oTj, wj, coe_splitO]
  cases c
  · -- Case (1)
    have ea : (splitS .one (Coup.toV .one V) a b X).a =
        ind (a ∈ X) • ((-Coup1.la V) • psibar a) + ind (b ∈ X) • (0 : Alg d L N) := by
      simp [splitS, halfA, halfB, Coup.toV]
    have eb : (splitS .one (Coup.toV .one V) a b X).b =
        ind (a ∈ X) • (0 : Alg d L N) + ind (b ∈ X) • (Coup1.lb V • psi b) := by
      simp [splitS, halfA, halfB, Coup.toV]
    have eab : (splitS .one (Coup.toV .one V) a b X).ab =
        ind (a ∈ X) • (Coup1.ra V • (psibar a * psi a)) +
          ind (b ∈ X) • (Coup1.rb V • (psibar b * psi b)) := by
      simp [splitS, halfA, halfB, Coup.toV]
    have ee : (splitS .one (Coup.toV .one V) a b X).e = 0 := by
      simp [splitS, halfA, halfB, Coup.toV]
    have hTe : Tj d (L : ℝ) j ℓ (splitS .one (Coup.toV .one V) a b X).e = 0 := by
      rw [ee, Tj_zero]
    have hTa : Tj d (L : ℝ) j ℓ (splitS .one (Coup.toV .one V) a b X).a ≤
        ENNReal.ofReal (‖-Coup1.la V‖ * ℓ + 0) := by
      rw [ea]; exact Tj_split_le _ _ (by positivity) le_rfl (Tj_smul_le_of _ (hpsb a)) h0
    have hTb : Tj d (L : ℝ) j ℓ (splitS .one (Coup.toV .one V) a b X).b ≤
        ENNReal.ofReal (0 + ‖Coup1.lb V‖ * ℓ) := by
      rw [eb]; exact Tj_split_le _ _ le_rfl (by positivity) h0 (Tj_smul_le_of _ (hψ b))
    have hTab : Tj d (L : ℝ) j ℓ (splitS .one (Coup.toV .one V) a b X).ab ≤
        ENNReal.ofReal (‖Coup1.ra V‖ * ℓ ^ 2 + ‖Coup1.rb V‖ * ℓ ^ 2) := by
      rw [eab]
      exact Tj_split_le _ _ (by positivity) (by positivity) (Tj_smul_le_of _ (hpp a a))
        (Tj_smul_le_of _ (hpp b b))
    refine (oNorm_le_ofReal (nrm := Tj d (L : ℝ) j ℓ)
      (w := obsWt .one ℓ ℓ') (ella_nonneg .one hℓ.le) hab0 (by positivity) (by positivity)
      (by positivity) rfl rfl rfl hTe hTa hTb hTab).trans
      (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    simp only [ella, Case.p, pow_one, laOf, lbOf, etaOf, raOf, rbOf, norm_neg, norm_zero]
    field_simp
    ring
  · -- Case (2)
    have ea : (splitS .two (Coup.toV .two V) a b X).a =
        ind (a ∈ X) • ((-Coup2.la V) • (psibar a * psi a)) + ind (b ∈ X) • (0 : Alg d L N) := by
      simp [splitS, halfA, halfB, Coup.toV]
    have eb : (splitS .two (Coup.toV .two V) a b X).b =
        ind (a ∈ X) • (0 : Alg d L N) + ind (b ∈ X) • ((-Coup2.lb V) • (psibar b * psi b)) := by
      simp [splitS, halfA, halfB, Coup.toV]
    have eab : (splitS .two (Coup.toV .two V) a b X).ab =
        ind (a ∈ X) • ((-(Coup2.eta V / 4)) • nx a b + Coup2.ra V • (psibar a * psi a)) +
          ind (b ∈ X) • ((-(Coup2.eta V / 4)) • nx a b + Coup2.rb V • (psibar b * psi b)) := by
      simp [splitS, halfA, halfB, Coup.toV, sub_eq_add_neg]
    have ee : (splitS .two (Coup.toV .two V) a b X).e = 0 := by
      simp [splitS, halfA, halfB, Coup.toV]
    have hTe : Tj d (L : ℝ) j ℓ (splitS .two (Coup.toV .two V) a b X).e = 0 := by
      rw [ee, Tj_zero]
    have hTa : Tj d (L : ℝ) j ℓ (splitS .two (Coup.toV .two V) a b X).a ≤
        ENNReal.ofReal (‖-Coup2.la V‖ * ℓ ^ 2 + 0) := by
      rw [ea]; exact Tj_split_le _ _ (by positivity) le_rfl (Tj_smul_le_of _ (hpp a a)) h0
    have hTb : Tj d (L : ℝ) j ℓ (splitS .two (Coup.toV .two V) a b X).b ≤
        ENNReal.ofReal (0 + ‖-Coup2.lb V‖ * ℓ ^ 2) := by
      rw [eb]; exact Tj_split_le _ _ le_rfl (by positivity) h0 (Tj_smul_le_of _ (hpp b b))
    have hTab : Tj d (L : ℝ) j ℓ (splitS .two (Coup.toV .two V) a b X).ab ≤
        ENNReal.ofReal ((‖-(Coup2.eta V / 4)‖ * (ℓ ^ 2 + ℓ ^ 2) + ‖Coup2.ra V‖ * ℓ ^ 2) +
          (‖-(Coup2.eta V / 4)‖ * (ℓ ^ 2 + ℓ ^ 2) + ‖Coup2.rb V‖ * ℓ ^ 2)) := by
      rw [eab]
      exact Tj_split_le _ _ (by positivity) (by positivity)
        (Tj_add_le_of (by positivity) (by positivity) (Tj_smul_le_of _ hnx)
          (Tj_smul_le_of _ (hpp a a)))
        (Tj_add_le_of (by positivity) (by positivity) (Tj_smul_le_of _ hnx)
          (Tj_smul_le_of _ (hpp b b)))
    refine (oNorm_le_ofReal (nrm := Tj d (L : ℝ) j ℓ)
      (w := obsWt .two ℓ ℓ') (ella_nonneg .two hℓ.le) hab0 (by positivity) (by positivity)
      (by positivity) rfl rfl rfl hTe hTa hTb hTab).trans
      (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    simp only [ella, Case.p, laOf, lbOf, etaOf, raOf, rbOf, norm_neg, norm_div]
    norm_num
    field_simp
    ring

end VNorm

/-! ### Lemma `lem:Vobs-bd` -/

set_option maxHeartbeats 1000000 in
/-- **Lemma `lem:Vobs-bd`** (see the module docstring). -/
theorem Vobs_bd (hd : 3 ≤ d) : ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ (L : ℕ) [NeZero L], 2 ^ (d + 3) ≤ L →
    ∀ (N : ℕ) (msq : ℝ) (V₀ : Vcoup) (ℓ₀ : ℝ), 0 < ℓ₀ →
    (∀ k < N, GoodCov k ℓ₀ (Flow.covAt d L N msq k)) →
    ∀ (c : Case) (l₀ : ℂ) (a b : Lam d L N) (A : ℝ), 1 ≤ A → ∀ (θ e : ℝ), 0 ≤ θ → θ < 1 →
    0 ≤ e → ∀ j ≤ N,
    (∀ k < j, KnormObs c ℓ₀ a b k A (flowO d L c N msq V₀ (initObs c l₀) a b k).2 ≤
      ENNReal.ofReal (e * θ ^ k)) →
      ‖laOf c (flowO d L c N msq V₀ (initObs c l₀) a b j).1 - l₀‖ ≤ Cs * e / (1 - θ) ∧
      ‖lbOf c (flowO d L c N msq V₀ (initObs c l₀) a b j).1 - l₀‖ ≤ Cs * e / (1 - θ) ∧
      ‖raOf c (flowO d L c N msq V₀ (initObs c l₀) a b j).1‖ ≤
        Cs * sab c (ellj d L ℓ₀ (coal L a b)) * e * θ ^ coal L a b / (1 - θ) ∧
      ‖rbOf c (flowO d L c N msq V₀ (initObs c l₀) a b j).1‖ ≤
        Cs * sab c (ellj d L ℓ₀ (coal L a b)) * e * θ ^ coal L a b / (1 - θ) ∧
      (j ≤ coal L a b → raOf c (flowO d L c N msq V₀ (initObs c l₀) a b j).1 = 0 ∧
        rbOf c (flowO d L c N msq V₀ (initObs c l₀) a b j).1 = 0) ∧
      ‖etaOf c (flowO d L c N msq V₀ (initObs c l₀) a b j).1‖ ≤
        4 * (‖l₀‖ + Cs * e / (1 - θ)) ^ 2 * ellj d L ℓ₀ (min j (coal L a b)) ^ 2 ∧
      (j ≤ min (coal L a b) (N - 1) →
        etaOf c (flowO d L c N msq V₀ (initObs c l₀) a b j).1 = 0) ∧
      VnormObs c ℓ₀ a b j (flowO d L c N msq V₀ (initObs c l₀) a b j).1 ≤
        ENNReal.ofReal (2 * (‖l₀‖ + Cs * e / (1 - θ)) + 4 * (‖l₀‖ + Cs * e / (1 - θ)) ^ 2 +
          2 * (Cs * e / (1 - θ))) := by
  obtain ⟨Cs, hCs, hQ⟩ := Qcoup_bounds d
  refine ⟨Cs, hCs, ?_⟩
  intro L _ hL N msq V₀ ℓ₀ hℓ₀ hC c l₀ a b A hA θ e hθ0 hθ1 he0
  have hd1 : 1 ≤ d := by omega
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have h1θ : 0 < 1 - θ := by linarith
  set F := fun k => flowO d L c N msq V₀ (initObs c l₀) a b k with hF
  set jab := coal L a b with hjab
  set S := sab c (ellj d L ℓ₀ jab) with hS
  have hS0 : 0 ≤ S := sab_nonneg c _
  set lamB := ‖l₀‖ + Cs * e / (1 - θ) with hlamB
  have hCe : 0 ≤ Cs * e / (1 - θ) := by positivity
  have hlamB0 : 0 ≤ lamB := by positivity
  have hsucc : ∀ k, (F (k + 1)).1 = Coup.toV c (nextObs (Flow.covAt d L N msq k) k (F k).1
      (F k).2 a b) := fun k => rfl
  -- the invariant
  have inv : ∀ j, j ≤ N → (∀ k < j, KnormObs c ℓ₀ a b k A (F k).2 ≤ ENNReal.ofReal (e * θ ^ k)) →
      ‖laOf c (F j).1 - l₀‖ ≤ Cs * e * ((1 - θ ^ j) / (1 - θ)) ∧
      ‖lbOf c (F j).1 - l₀‖ ≤ Cs * e * ((1 - θ ^ j) / (1 - θ)) ∧
      ‖raOf c (F j).1‖ ≤ Cs * S * e * ((θ ^ jab - θ ^ max jab j) / (1 - θ)) ∧
      ‖rbOf c (F j).1‖ ≤ Cs * S * e * ((θ ^ jab - θ ^ max jab j) / (1 - θ)) ∧
      ‖etaOf c (F j).1‖ ≤ 2 * lamB ^ 2 * ∑ k ∈ range j, |Flow.covAt d L N msq k a b| := by
    intro j
    induction j with
    | zero =>
      intro _ _
      have e0 : (F 0).1 = initObs c l₀ := rfl
      rw [e0]
      cases c <;> simp [initObs, laOf, lbOf, raOf, rbOf, etaOf]
    | succ j ih =>
      intro hj hK
      obtain ⟨ila, ilb, ira, irb, ieta⟩ := ih (by omega) (fun k hk => hK k (by omega))
      obtain ⟨q1, q2, -, -, -, -, q7, q8⟩ := hQ L N j ℓ₀ hℓ₀ c (F j).2 a b A hA (e * θ ^ j)
        (by positivity) (hK j (Nat.lt_succ_self j))
      have hθj : 0 ≤ θ ^ j := by positivity
      have hla : laOf c (F (j + 1)).1 = laOf c (F j).1 - laOf c (Qcoup c j (F j).2 a b) := by
        rw [hsucc, laOf_toV, laOf_nextObs]
      have hlb : lbOf c (F (j + 1)).1 = lbOf c (F j).1 - lbOf c (Qcoup c j (F j).2 a b) := by
        rw [hsucc, lbOf_toV, lbOf_nextObs]
      have hra : raOf c (F (j + 1)).1 = raOf c (F j).1 - raOf c (Qcoup c j (F j).2 a b) := by
        rw [hsucc, raOf_toV, raOf_nextObs]
      have hrb : rbOf c (F (j + 1)).1 = rbOf c (F j).1 - rbOf c (Qcoup c j (F j).2 a b) := by
        rw [hsucc, rbOf_toV, rbOf_nextObs]
      have hgs := geom_step hθ1 1 j
      -- `λ`
      have hla' : ‖laOf c (F (j + 1)).1 - l₀‖ ≤ Cs * e * ((1 - θ ^ (j + 1)) / (1 - θ)) := by
        rw [hla, show laOf c (F j).1 - laOf c (Qcoup c j (F j).2 a b) - l₀ =
          (laOf c (F j).1 - l₀) - laOf c (Qcoup c j (F j).2 a b) by ring]
        refine (norm_sub_le _ _).trans ?_
        rw [← hgs]; nlinarith
      have hlb' : ‖lbOf c (F (j + 1)).1 - l₀‖ ≤ Cs * e * ((1 - θ ^ (j + 1)) / (1 - θ)) := by
        rw [hlb, show lbOf c (F j).1 - lbOf c (Qcoup c j (F j).2 a b) - l₀ =
          (lbOf c (F j).1 - l₀) - lbOf c (Qcoup c j (F j).2 a b) by ring]
        refine (norm_sub_le _ _).trans ?_
        rw [← hgs]; nlinarith
      -- `r`
      have hr : ‖raOf c (F (j + 1)).1‖ ≤ Cs * S * e * ((θ ^ jab - θ ^ max jab (j + 1)) / (1 - θ)) ∧
          ‖rbOf c (F (j + 1)).1‖ ≤ Cs * S * e * ((θ ^ jab - θ ^ max jab (j + 1)) / (1 - θ)) := by
        rw [hra, hrb]
        by_cases hjj : jab ≤ j
        · have hw : jwedge j (coal L a b) = jab := jwedge_eq_of_ge hjj
          rw [hw] at q7 q8
          rw [max_eq_right (by omega : jab ≤ j + 1)]
          rw [max_eq_right hjj] at ira irb
          have hg := geom_step hθ1 (θ ^ jab) j
          constructor
          · refine (norm_sub_le _ _).trans ?_
            rw [← hg]; nlinarith
          · refine (norm_sub_le _ _).trans ?_
            rw [← hg]; nlinarith
        · have hz := raOf_of_abZero (Qcoup_abZero (c := c) (j := j) (K := (F j).2) (a := a) (b := b)
            (fun Y hY => abSmall_flowO V₀ l₀ a b hd1 hL hC (k := j) (by omega) (by omega) hY))
          rw [hz.1, hz.2, sub_zero, sub_zero, max_eq_left (by omega : j + 1 ≤ jab)]
          rw [max_eq_left (by omega : j ≤ jab)] at ira irb
          exact ⟨ira, irb⟩
      -- `η`
      have hlaB : ‖laOf c (F (j + 1)).1‖ ≤ lamB := by
        have h1 : (1 - θ ^ (j + 1)) / (1 - θ) ≤ 1 / (1 - θ) :=
          div_le_div_of_nonneg_right (by have h0 : 0 ≤ θ ^ (j + 1) := (by positivity); linarith) h1θ.le
        calc ‖laOf c (F (j + 1)).1‖ = ‖l₀ + (laOf c (F (j + 1)).1 - l₀)‖ := by ring_nf
          _ ≤ ‖l₀‖ + ‖laOf c (F (j + 1)).1 - l₀‖ := norm_add_le _ _
          _ ≤ lamB := by
            rw [hlamB]
            have := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ Cs * e)
            rw [mul_one_div] at this
            linarith
      have hlbB : ‖lbOf c (F (j + 1)).1‖ ≤ lamB := by
        have h1 : (1 - θ ^ (j + 1)) / (1 - θ) ≤ 1 / (1 - θ) :=
          div_le_div_of_nonneg_right (by have h0 : 0 ≤ θ ^ (j + 1) := (by positivity); linarith) h1θ.le
        calc ‖lbOf c (F (j + 1)).1‖ = ‖l₀ + (lbOf c (F (j + 1)).1 - l₀)‖ := by ring_nf
          _ ≤ ‖l₀‖ + ‖lbOf c (F (j + 1)).1 - l₀‖ := norm_add_le _ _
          _ ≤ lamB := by
            rw [hlamB]
            have := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ Cs * e)
            rw [mul_one_div] at this
            linarith
      have heta : ‖etaOf c (F (j + 1)).1‖ ≤
          2 * lamB ^ 2 * ∑ k ∈ range (j + 1), |Flow.covAt d L N msq k a b| := by
        have h := norm_etaOf_nextObs_le (Flow.covAt d L N msq j) j a b (F j).1 (F j).2
        rw [hsucc, etaOf_toV]
        have hla2 : ‖laOf c (nextObs (Flow.covAt d L N msq j) j (F j).1 (F j).2 a b)‖ ≤ lamB := by
          rw [← laOf_toV]; exact hlaB
        have hlb2 : ‖lbOf c (nextObs (Flow.covAt d L N msq j) j (F j).1 (F j).2 a b)‖ ≤ lamB := by
          rw [← lbOf_toV]; exact hlbB
        refine h.trans ?_
        rw [sum_range_succ, mul_add]
        have hc0 : 0 ≤ |Flow.covAt d L N msq j a b| := abs_nonneg _
        have : ‖laOf c (nextObs (Flow.covAt d L N msq j) j (F j).1 (F j).2 a b)‖ *
            ‖lbOf c (nextObs (Flow.covAt d L N msq j) j (F j).1 (F j).2 a b)‖ ≤ lamB ^ 2 := by
          rw [sq]; exact mul_le_mul hla2 hlb2 (norm_nonneg _) hlamB0
        nlinarith
      exact ⟨hla', hlb', hr.1, hr.2, heta⟩
  intro j hj hK
  obtain ⟨ila, ilb, ira, irb, ieta⟩ := inv j hj hK
  have hθp : 0 ≤ θ ^ j := by positivity
  have hθab : θ ^ jab ≤ 1 := pow_le_one₀ hθ0 hθ1.le
  have hθab0 : 0 ≤ θ ^ jab := by positivity
  have hmax0 : 0 ≤ θ ^ max jab j := by positivity
  have hla : ‖laOf c (F j).1 - l₀‖ ≤ Cs * e / (1 - θ) :=
    (ila.trans (mul_frac_le (by positivity) h1θ (by linarith : 1 - θ ^ j ≤ 1))).trans_eq
      (by ring)
  have hlb : ‖lbOf c (F j).1 - l₀‖ ≤ Cs * e / (1 - θ) :=
    (ilb.trans (mul_frac_le (by positivity) h1θ (by linarith : 1 - θ ^ j ≤ 1))).trans_eq
      (by ring)
  have hra : ‖raOf c (F j).1‖ ≤ Cs * S * e * θ ^ jab / (1 - θ) :=
    ira.trans (mul_frac_le (by positivity) h1θ (by linarith))
  have hrb : ‖rbOf c (F j).1‖ ≤ Cs * S * e * θ ^ jab / (1 - θ) :=
    irb.trans (mul_frac_le (by positivity) h1θ (by linarith))
  have hr0 : j ≤ jab → raOf c (F j).1 = 0 ∧ rbOf c (F j).1 = 0 := by
    intro h
    rw [max_eq_left h, sub_self, zero_div, mul_zero] at ira irb
    exact ⟨norm_le_zero_iff.1 ira, norm_le_zero_iff.1 irb⟩
  have heta : ‖etaOf c (F j).1‖ ≤ 4 * lamB ^ 2 * ellj d L ℓ₀ (min j jab) ^ 2 := by
    refine ieta.trans ?_
    have := sum_cov_le hd (by
      have : 2 ^ 1 ≤ 2 ^ (d + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega) hℓ₀ hC a b hj
    have h2 : 0 ≤ 2 * lamB ^ 2 := by positivity
    calc 2 * lamB ^ 2 * ∑ k ∈ range j, |Flow.covAt d L N msq k a b|
        ≤ 2 * lamB ^ 2 * (2 * ellj d L ℓ₀ (min j jab) ^ 2) := mul_le_mul_of_nonneg_left this h2
      _ = _ := by ring
  have heta0 : j ≤ min jab (N - 1) → etaOf c (F j).1 = 0 := by
    intro h
    have := (flowO_ab (c := c) V₀ l₀ a b hd1 hL hC j h).1
    cases c
    · rfl
    · exact this.1
  refine ⟨hla, hlb, hra, hrb, hr0, heta, heta0, ?_⟩
  -- the norm of `V^obs_j`
  refine iSup₂_le fun p _ => (nrmj_splitO_toV_coup_le a b hℓ₀ (F j).1 j _).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hlaB : ‖laOf c (F j).1‖ ≤ lamB := by
    calc ‖laOf c (F j).1‖ = ‖l₀ + (laOf c (F j).1 - l₀)‖ := by ring_nf
      _ ≤ ‖l₀‖ + ‖laOf c (F j).1 - l₀‖ := norm_add_le _ _
      _ ≤ lamB := by rw [hlamB]; linarith
  have hlbB : ‖lbOf c (F j).1‖ ≤ lamB := by
    calc ‖lbOf c (F j).1‖ = ‖l₀ + (lbOf c (F j).1 - l₀)‖ := by ring_nf
      _ ≤ ‖l₀‖ + ‖lbOf c (F j).1 - l₀‖ := norm_add_le _ _
      _ ≤ lamB := by rw [hlamB]; linarith
  have hℓ := ellj_pos (d := d) hL0 hℓ₀ j
  set ℓ := ellj d L ℓ₀ j with hℓdef
  set ℓ' := ellj d L ℓ₀ (jwedge j (coal L a b)) with hℓ'def
  have hℓ' : 0 < ℓ' := ellj_pos hL0 hℓ₀ _
  have hw : ℓ' = ellj d L ℓ₀ (min j jab) := by rw [hℓ'def, jwedge_coe]
  -- the `η` part
  have hE : ellab c ℓ ℓ' * ℓ ^ 2 * ‖etaOf c (F j).1‖ ≤ 4 * lamB ^ 2 := by
    cases c
    · simp [etaOf]; positivity
    · rw [← hw] at heta
      have e1 : ellab .two ℓ ℓ' * ℓ ^ 2 * (4 * lamB ^ 2 * ℓ' ^ 2) = 4 * lamB ^ 2 := by
        simp only [ellab]; field_simp
      have h0 : 0 ≤ ellab .two ℓ ℓ' * ℓ ^ 2 := by simp only [ellab]; positivity
      calc _ ≤ ellab .two ℓ ℓ' * ℓ ^ 2 * (4 * lamB ^ 2 * ℓ' ^ 2) :=
            mul_le_mul_of_nonneg_left heta h0
        _ = _ := e1
  -- the `r` part
  have hR : ellab c ℓ ℓ' * ℓ ^ 2 * (‖raOf c (F j).1‖ + ‖rbOf c (F j).1‖) ≤
      2 * (Cs * e / (1 - θ)) := by
    by_cases hjj : j ≤ jab
    · rw [(hr0 hjj).1, (hr0 hjj).2, norm_zero, add_zero, mul_zero]; positivity
    · have hw' : ℓ' = ellj d L ℓ₀ jab := by
        rw [hℓ'def, jwedge_eq_of_ge (by omega : jab ≤ j)]
      have e1 : ellab c ℓ ℓ' * ℓ ^ 2 * S = 1 := by
        rw [hS, ← hw', mul_comm, ← mul_assoc, sab_mul_ellab c hℓ hℓ']; field_simp
      have h0 : 0 ≤ ellab c ℓ ℓ' * ℓ ^ 2 := by
        have : 0 ≤ ellab c ℓ ℓ' := by cases c <;> simp only [ellab] <;> positivity
        positivity
      have hsum : ‖raOf c (F j).1‖ + ‖rbOf c (F j).1‖ ≤ 2 * (Cs * S * e * θ ^ jab / (1 - θ)) := by
        linarith
      calc _ ≤ ellab c ℓ ℓ' * ℓ ^ 2 * (2 * (Cs * S * e * θ ^ jab / (1 - θ))) :=
            mul_le_mul_of_nonneg_left hsum h0
        _ = 2 * (Cs * e * θ ^ jab / (1 - θ)) * (ellab c ℓ ℓ' * ℓ ^ 2 * S) := by ring
        _ = 2 * (Cs * e * θ ^ jab / (1 - θ)) := by rw [e1, mul_one]
        _ ≤ 2 * (Cs * e / (1 - θ)) := by
            have h5 : Cs * e * θ ^ jab ≤ Cs * e :=
              (mul_le_mul_of_nonneg_left hθab (by positivity)).trans_eq (mul_one _)
            exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h5 h1θ.le) (by norm_num)
  nlinarith

end

end Obs
