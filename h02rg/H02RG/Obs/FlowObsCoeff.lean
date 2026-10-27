import Obs.StepObs
import Suscept.Bounds

/-!
# Coefficient bounds for the observable flow (Section `sec:flow-obs`)

Auxiliary estimates for `lem:Vobs-recursion`: the coefficients read off by `Loc^obs`
(`mass1`, `mass2`, `ε`) are controlled by the `T_j(ℓ)` norm (`norm_mass1_le`, `norm_mass2_le`,
as in `e:kN2normbd`, via constant test functions), hence the coupling constants of
`Q^obs` (`Qcoup`) by `‖K^obs_j‖_j` (`Qcoup_bounds`); and `|C_{j+1}(x,y)| ≤ ℓ_{j+1}^2`
(`abs_cov_le`).
-/

namespace Obs

noncomputable section

open Finset Grassmann SA Loc Step LocObs Gen

variable {d L N : ℕ} [NeZero L]

/-! ### Coefficients versus norms -/

section Mass

theorem Lpow_pos (j : ℕ) : (0 : ℝ) < (L : ℝ) ^ j :=
  pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) j

/-- `|∑_x F_{(x,s)}| ≤ ℓ^{-1} ‖F‖_{T_j(ℓ)}`. -/
theorem norm_mass1_le {ℓ : ℝ} (hℓ : 0 < ℓ) (j : ℕ) (s : ℤˣ) (F : Alg d L N) :
    ‖mass1 s F‖ ≤ (Tj d (L : ℝ) j ℓ F).toReal * ℓ⁻¹ := by
  have hh := Lpow_pos (L := L) j
  let g : (Fin 1 → Sf (Lam d L N)) → ℂ := fun z => if (z 0).2 = s then 1 else 0
  have hp : pair F (single 1 g) = mass1 s F := by
    rw [pair_single']
    simp only [Nat.factorial_one, Nat.cast_one, inv_one, one_mul]
    rw [← (Equiv.funUnique (Fin 1) (Sf (Lam d L N))).symm.sum_comp]
    simp only [Fintype.sum_prod_type, g, mass1]
    refine sum_congr rfl fun x _ => ?_
    rw [Finset.sum_eq_single s]
    · have : (Equiv.funUnique (Fin 1) (Sf (Lam d L N))).symm (x, s) = ![(x, s)] := by
        funext i; fin_cases i; rfl
      simp [this]
    · intro t _ ht
      simp [Equiv.funUnique, ht]
    · intro h; exact absurd (mem_univ s) h
  have hg : phiNorm (Dir d) (pPhi d) ((L : ℝ) ^ j) ℓ (single 1 g) ≤ ENNReal.ofReal ℓ⁻¹ := by
    refine phiNorm_single_le' (by positivity) fun z α _ => ?_
    by_cases hα : α = 0
    · subst hα
      rw [nabla_zero _ (fun y => sh_zero y)]
      have : ord (0 : Fin 1 → Dir d → ℕ) = 0 := by simp [ord, Grassmann.mabs]
      rw [this, pow_zero, mul_one, pow_one]
      have : ‖g z‖ ≤ 1 := by simp only [g]; split_ifs <;> simp
      calc ℓ⁻¹ * ‖g z‖ ≤ ℓ⁻¹ * 1 := mul_le_mul_of_nonneg_left this (by positivity)
        _ = ℓ⁻¹ := mul_one _
    · have hc : nab α g z = nab α (fun _ => g z) z := nabla_congr _ α z fun β => rfl
      rw [hc, nabla_const _ hα, norm_zero, mul_zero]; positivity
  rw [← hp]
  exact abs_pair_le hh hℓ F (by positivity) hg

theorem mass2_eq_neg_c2 (F : Alg d L N) : mass2 F = -Suscept.c2 F := by
  have hswap : ∀ x y : Lam d L N, coeff F ![((x, -1) : Sf (Lam d L N)), (y, 1)] =
      -coeff F ![((y, 1) : Sf (Lam d L N)), (x, -1)] := by
    intro x y
    have := coeff_perm F ![((y, 1) : Sf (Lam d L N)), (x, -1)] (Equiv.swap 0 1)
    have e : (![((y, 1) : Sf (Lam d L N)), (x, -1)] ∘ Equiv.swap 0 1) =
        ![((x, -1) : Sf (Lam d L N)), (y, 1)] := by
      funext i; fin_cases i <;> rfl
    rw [e] at this
    rw [this]; simp
  simp only [mass2, Suscept.c2, hswap, sum_neg_distrib]
  rw [Finset.sum_comm]

/-- `|∑_{x,y} F_{(x,-)(y,+)}| ≤ ℓ^{-2} ‖F‖_{T_j(ℓ)}` (as `e:kN2normbd`). -/
theorem norm_mass2_le {ℓ : ℝ} (hℓ : 0 < ℓ) (j : ℕ) (F : Alg d L N) :
    ‖mass2 F‖ ≤ (Tj d (L : ℝ) j ℓ F).toReal * ℓ⁻¹ ^ 2 := by
  rw [mass2_eq_neg_c2, norm_neg]
  exact Suscept.norm_c2_le (Lpow_pos j) hℓ F

theorem norm_eps_le {ℓ : ℝ} (hℓ : 0 < ℓ) (j : ℕ) (F : Alg d L N) :
    ‖ε F‖ ≤ (Tj d (L : ℝ) j ℓ F).toReal :=
  abs_eps_le (Lpow_pos j) hℓ F

end Mass

/-! ### Components of `K^obs` versus `‖K^obs‖_j` -/

section Comp

variable {c : Case} {ℓ₀ : ℝ} {a b : Lam d L N}

theorem mul_toReal_le_of {x e : ℝ} {T : ENNReal} (hx : 0 ≤ x) (he : 0 ≤ e)
    (h : ENNReal.ofReal x * T ≤ ENNReal.ofReal e) : x * T.toReal ≤ e := by
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hx, ENNReal.toReal_ofReal he] at this

/-- The components of `K(X)`, `X` connected, are bounded by `‖K^obs‖_j` with the weights
`ℓ_{a,j}`, `ℓ_{b,j}`, `ℓ_{ab,j}` (`e:ellsigma`). -/
theorem comp_le (hℓ₀ : 0 < ℓ₀) {j : ℕ} {A : ℝ} (hA : 1 ≤ A)
    {K : Finset (Lam d L N) → OE c (Lam d L N)} {X : Finset (Lam d L N)} (hX : IsConn j X)
    {e : ℝ} (he0 : 0 ≤ e) (he : KnormObs c ℓ₀ a b j A K ≤ ENNReal.ofReal e) :
    ella c (ellj d L ℓ₀ j) *
        (Tj d (L : ℝ) j (ellj d L ℓ₀ j) (K X : SA c (Lam d L N)).a).toReal ≤ e ∧
      ella c (ellj d L ℓ₀ j) *
        (Tj d (L : ℝ) j (ellj d L ℓ₀ j) (K X : SA c (Lam d L N)).b).toReal ≤ e ∧
      ellab c (ellj d L ℓ₀ j) (ellj d L ℓ₀ (jwedge j (coal L a b))) *
        (Tj d (L : ℝ) j (ellj d L ℓ₀ j) (K X : SA c (Lam d L N)).ab).toReal ≤ e := by
  have hℓ := ellj_pos (d := d) (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L) : (0 : ℝ) < L)
    hℓ₀ j
  have hℓ' := ellj_pos (d := d) (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L) : (0 : ℝ) < L)
    hℓ₀ (jwedge j (coal L a b))
  have h := (nrmj_le_KnormObs (c := c) (ℓ₀ := ℓ₀) (a := a) (b := b) hA hX).trans he
  rw [nrmj_πobs_eq] at h
  simp only [wj, obsWt] at h
  have hab : 0 ≤ ellab c (ellj d L ℓ₀ j) (ellj d L ℓ₀ (jwedge j (coal L a b))) := by
    cases c <;> simp only [ellab] <;> positivity
  refine ⟨mul_toReal_le_of (ella_nonneg c hℓ.le) he0 (le_trans ?_ h),
    mul_toReal_le_of (ella_nonneg c hℓ.le) he0 (le_trans ?_ h),
    mul_toReal_le_of hab he0 (le_trans ?_ h)⟩
  · exact le_add_right (le_add_right le_rfl)
  · exact le_add_right (le_add_left le_rfl)
  · exact le_add_left le_rfl

end Comp

/-! ### The number of small sets containing a point -/

theorem card_smallAt_le (d : ℕ) : ∃ cs : ℕ, ∀ (L : ℕ) [NeZero L] (N j : ℕ) (x : Lam d L N),
    (smallAt j x).card ≤ cs := by
  classical
  obtain ⟨cs, hcs⟩ := card_small_containing d
  refine ⟨cs, fun L _ N j x => le_trans (card_le_card ?_) (hcs L N j (blk j x)
    (mem_image_of_mem _ (mem_univ x)))⟩
  intro X hX
  obtain ⟨hXs, hxX⟩ := mem_filter.1 hX
  have hXs' := mem_smallSets.1 hXs
  refine mem_smallSets_filter.2 ⟨hXs', fun y hy => ?_⟩
  exact hXs'.1 x y (Loc.mem_blockSet.1 hy).symm hxX

/-! ### The coupling constants of `Q^obs` -/

/-- `λ_b`. -/
def lbOf : (c : Case) → Coup c → ℂ
  | .one, V => Coup1.lb V
  | .two, V => Coup2.lb V

/-- `γ_a` (`0` in Case (1)). -/
def gaOf : (c : Case) → Coup c → ℂ
  | .one, _ => 0
  | .two, V => Coup2.ga V

/-- `γ_b` (`0` in Case (1)). -/
def gbOf : (c : Case) → Coup c → ℂ
  | .one, _ => 0
  | .two, V => Coup2.gb V

/-- `q_a`. -/
def qaOf : (c : Case) → Coup c → ℂ
  | .one, V => Coup1.qa V
  | .two, V => Coup2.qa V

/-- `q_b`. -/
def qbOf : (c : Case) → Coup c → ℂ
  | .one, V => Coup1.qb V
  | .two, V => Coup2.qb V

/-- `r_a`. -/
def raOf : (c : Case) → Coup c → ℂ
  | .one, V => Coup1.ra V
  | .two, V => Coup2.ra V

/-- `r_b`. -/
def rbOf : (c : Case) → Coup c → ℂ
  | .one, V => Coup1.rb V
  | .two, V => Coup2.rb V

/-- The factor `ℓ_j^{-2} ℓ_{ab,j}^{-1}` in the error term of `r` (`e:obs-r-rec-K`): `1` in
Case (1), `ℓ'^2 = ℓ_{j ∧ j_ab}^2` in Case (2). -/
def sab : Case → ℝ → ℝ
  | .one, _ => 1
  | .two, ℓ' => ℓ' ^ 2

theorem sab_nonneg (c : Case) (ℓ' : ℝ) : 0 ≤ sab c ℓ' := by
  cases c <;> simp only [sab] <;> positivity

theorem sab_mul_ellab (c : Case) {ℓ ℓ' : ℝ} (hℓ : 0 < ℓ) (hℓ' : 0 < ℓ') :
    sab c ℓ' * ellab c ℓ ℓ' = ℓ⁻¹ ^ 2 := by
  cases c <;> simp only [sab, ellab] <;> field_simp

theorem norm_div_cardAB_le {a b : Lam d L N} {X : Finset (Lam d L N)} (hX : a ∈ X ∨ b ∈ X)
    (z : ℂ) : ‖z / cardAB a b X‖ ≤ ‖z‖ := by
  have h1 : 1 ≤ (X ∩ {a, b}).card := by
    rcases hX with h | h
    · exact card_pos.2 ⟨a, mem_inter.2 ⟨h, by simp⟩⟩
    · exact card_pos.2 ⟨b, mem_inter.2 ⟨h, by simp⟩⟩
  rw [cardAB, norm_div, Complex.norm_natCast]
  exact div_le_self (norm_nonneg _) (by exact_mod_cast h1)

theorem norm_sum_smallAt_le {cs : ℕ} (hcs : ∀ (j : ℕ) (x : Lam d L N), (smallAt j x).card ≤ cs)
    (j : ℕ) (x : Lam d L N) (f : Finset (Lam d L N) → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ X ∈ smallAt j x, ‖f X‖ ≤ B) : ‖∑ X ∈ smallAt j x, f X‖ ≤ cs * B := by
  refine (norm_sum_le _ _).trans ((sum_le_card_nsmul _ _ _ hf).trans ?_)
  rw [nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcs j x) hB

/-- **The error terms of `lem:Vobs-recursion`**: the coupling constants of `Q^obs`
(`Qcoup`) are bounded by `‖K^obs_j‖_j ≤ e`:
`|δλ_x| ≤ C_S e`, `|δγ_x| ≤ C_S ℓ_j^2 e`, `|δq_x| ≤ C_S ℓ_{ab,j}^{-1} e`,
`|δr_x| ≤ C_S ℓ_j^{-2} ℓ_{ab,j}^{-1} e = C_S sab e`, where `C_S` is the number of small sets
containing a point (depending only on `d`); moreover the `ab` constants vanish if
`K^{ab}_j(X) = 0` for small `X` (`Qcoup_abZero`). -/
theorem Qcoup_bounds (d : ℕ) : ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ (L : ℕ) [NeZero L] (N j : ℕ) (ℓ₀ : ℝ),
    0 < ℓ₀ → ∀ (c : Case) (K : Finset (Lam d L N) → OE c (Lam d L N)) (a b : Lam d L N) (A : ℝ),
    1 ≤ A → ∀ e : ℝ, 0 ≤ e → KnormObs c ℓ₀ a b j A K ≤ ENNReal.ofReal e →
      ‖laOf c (Qcoup c j K a b)‖ ≤ Cs * e ∧ ‖lbOf c (Qcoup c j K a b)‖ ≤ Cs * e ∧
      ‖gaOf c (Qcoup c j K a b)‖ ≤ Cs * ellj d L ℓ₀ j ^ 2 * e ∧
      ‖gbOf c (Qcoup c j K a b)‖ ≤ Cs * ellj d L ℓ₀ j ^ 2 * e ∧
      ‖qaOf c (Qcoup c j K a b)‖ ≤
        Cs * (ellab c (ellj d L ℓ₀ j) (ellj d L ℓ₀ (jwedge j (coal L a b))))⁻¹ * e ∧
      ‖qbOf c (Qcoup c j K a b)‖ ≤
        Cs * (ellab c (ellj d L ℓ₀ j) (ellj d L ℓ₀ (jwedge j (coal L a b))))⁻¹ * e ∧
      ‖raOf c (Qcoup c j K a b)‖ ≤ Cs * sab c (ellj d L ℓ₀ (jwedge j (coal L a b))) * e ∧
      ‖rbOf c (Qcoup c j K a b)‖ ≤ Cs * sab c (ellj d L ℓ₀ (jwedge j (coal L a b))) * e := by
  obtain ⟨cs, hcs⟩ := card_smallAt_le d
  refine ⟨cs, by positivity, ?_⟩
  intro L _ N j ℓ₀ hℓ₀ c K a b A hA e he0 he
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set ℓ := ellj d L ℓ₀ j with hℓdef
  set ℓ' := ellj d L ℓ₀ (jwedge j (coal L a b)) with hℓ'def
  have hℓ : 0 < ℓ := ellj_pos hL0 hℓ₀ j
  have hℓ' : 0 < ℓ' := ellj_pos hL0 hℓ₀ _
  have hab0 : 0 < ellab c ℓ ℓ' := by cases c <;> simp only [ellab] <;> positivity
  have hcs' := hcs L N
  -- per small set bounds
  have hX : ∀ x : Lam d L N, ∀ X ∈ smallAt j x, IsConn j X ∧ x ∈ X := fun x X hX' => by
    obtain ⟨h1, h2⟩ := mem_filter.1 hX'
    have := mem_smallSets.1 h1
    exact ⟨⟨this.1, this.2.1⟩, h2⟩
  have hTa : ∀ x : Lam d L N, ∀ X ∈ smallAt j x,
      (Tj d (L : ℝ) j ℓ (K X : SA c (Lam d L N)).a).toReal ≤ e / ella c ℓ ∧
      (Tj d (L : ℝ) j ℓ (K X : SA c (Lam d L N)).b).toReal ≤ e / ella c ℓ ∧
      (Tj d (L : ℝ) j ℓ (K X : SA c (Lam d L N)).ab).toReal ≤ e / ellab c ℓ ℓ' := by
    intro x X hX'
    have hella : 0 < ella c ℓ := by unfold ella; positivity
    obtain ⟨h1, h2, h3⟩ := comp_le (a := a) (b := b) hℓ₀ hA (hX x X hX').1 he0 he
    refine ⟨?_, ?_, ?_⟩
    · rw [le_div_iff₀ hella, mul_comm]; exact h1
    · rw [le_div_iff₀ hella, mul_comm]; exact h2
    · rw [le_div_iff₀ hab0, mul_comm]; exact h3
  have hab_a : ∀ X ∈ smallAt j a, a ∈ X ∨ b ∈ X := fun X hX' => Or.inl (hX a X hX').2
  have hab_b : ∀ X ∈ smallAt j b, a ∈ X ∨ b ∈ X := fun X hX' => Or.inr (hX b X hX').2
  -- `ab` parts
  have hq : ∀ x : Lam d L N, (∀ X ∈ smallAt j x, a ∈ X ∨ b ∈ X) →
      ‖∑ X ∈ smallAt j x, ε ((K X : SA c (Lam d L N)).ab) / cardAB a b X‖ ≤
        cs * ((ellab c ℓ ℓ')⁻¹ * e) := by
    intro x hx
    refine norm_sum_smallAt_le hcs' j x _ (mul_nonneg (inv_nonneg.2 hab0.le) he0) fun X hX' => (norm_div_cardAB_le (hx X hX') _).trans ?_
    refine (norm_eps_le hℓ j _).trans ((hTa x X hX').2.2.trans (le_of_eq ?_))
    rw [div_eq_inv_mul]
  have hr : ∀ x : Lam d L N, (∀ X ∈ smallAt j x, a ∈ X ∨ b ∈ X) →
      ‖∑ X ∈ smallAt j x, mass2 ((K X : SA c (Lam d L N)).ab) / cardAB a b X‖ ≤
        cs * (sab c ℓ' * e) := by
    intro x hx
    refine norm_sum_smallAt_le hcs' j x _ (mul_nonneg (sab_nonneg c ℓ') he0) fun X hX' => (norm_div_cardAB_le (hx X hX') _).trans ?_
    refine (norm_mass2_le hℓ j _).trans ?_
    have h3 := (hTa x X hX').2.2
    have e1 : sab c ℓ' * e = e / ellab c ℓ ℓ' * ℓ⁻¹ ^ 2 := by
      rw [← sab_mul_ellab c hℓ hℓ']; field_simp
    rw [e1]
    exact mul_le_mul_of_nonneg_right h3 (by positivity)
  by_cases hj : j + 1 < N
  · cases c
    · simp only [Qcoup, if_pos hj, laOf, lbOf, gaOf, gbOf, qaOf, qbOf, raOf, rbOf, norm_neg,
        norm_zero]
      have hella : ella .one ℓ = ℓ⁻¹ := by simp [ella, Case.p]
      refine ⟨?_, ?_, by positivity, by positivity, ?_, ?_, ?_, ?_⟩
      · refine norm_sum_smallAt_le hcs' j a _ (by positivity) fun X hX' => (norm_mass1_le hℓ j _ _).trans ?_
        have := (hTa a X hX').1
        rw [hella] at this
        calc _ ≤ e / ℓ⁻¹ * ℓ⁻¹ := mul_le_mul_of_nonneg_right this (by positivity)
          _ = e := by field_simp
      · refine norm_sum_smallAt_le hcs' j b _ (by positivity) fun X hX' => (norm_mass1_le hℓ j _ _).trans ?_
        have := (hTa b X hX').2.1
        rw [hella] at this
        calc _ ≤ e / ℓ⁻¹ * ℓ⁻¹ := mul_le_mul_of_nonneg_right this (by positivity)
          _ = e := by field_simp
      · rw [mul_assoc]; exact hq a hab_a
      · rw [mul_assoc]; exact hq b hab_b
      · rw [mul_assoc]; exact hr a hab_a
      · rw [mul_assoc]; exact hr b hab_b
    · simp only [Qcoup, if_pos hj, laOf, lbOf, gaOf, gbOf, qaOf, qbOf, raOf, rbOf, norm_neg]
      have hella : ella .two ℓ = ℓ⁻¹ ^ 2 := by simp [ella, Case.p]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · refine norm_sum_smallAt_le hcs' j a _ (by positivity) fun X hX' => (norm_mass2_le hℓ j _).trans ?_
        have := (hTa a X hX').1
        rw [hella] at this
        calc _ ≤ e / ℓ⁻¹ ^ 2 * ℓ⁻¹ ^ 2 := mul_le_mul_of_nonneg_right this (by positivity)
          _ = e := by field_simp
      · refine norm_sum_smallAt_le hcs' j b _ (by positivity) fun X hX' => (norm_mass2_le hℓ j _).trans ?_
        have := (hTa b X hX').2.1
        rw [hella] at this
        calc _ ≤ e / ℓ⁻¹ ^ 2 * ℓ⁻¹ ^ 2 := mul_le_mul_of_nonneg_right this (by positivity)
          _ = e := by field_simp
      · rw [mul_assoc]
        refine norm_sum_smallAt_le hcs' j a _ (by positivity) fun X hX' => (norm_eps_le hℓ j _).trans ?_
        have := (hTa a X hX').1
        rw [hella] at this
        exact this.trans (le_of_eq (by field_simp))
      · rw [mul_assoc]
        refine norm_sum_smallAt_le hcs' j b _ (by positivity) fun X hX' => (norm_eps_le hℓ j _).trans ?_
        have := (hTa b X hX').2.1
        rw [hella] at this
        exact this.trans (le_of_eq (by field_simp))
      · rw [mul_assoc]; exact hq a hab_a
      · rw [mul_assoc]; exact hq b hab_b
      · rw [mul_assoc]; exact hr a hab_a
      · rw [mul_assoc]; exact hr b hab_b
  · rw [Qcoup_of_not hj]
    have h0 : 0 ≤ (cs : ℝ) := by positivity
    have h1 := sab_nonneg c ℓ'
    have h2 : 0 ≤ (ellab c ℓ ℓ')⁻¹ := inv_nonneg.2 hab0.le
    cases c <;> simp only [Coup.zero, laOf, lbOf, gaOf, gbOf, qaOf, qbOf, raOf, rbOf, norm_zero] <;>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> positivity

/-! ### The covariance -/

/-- `|C_{j+1}(x, y)| ≤ ℓ_{j+1}^2` (from `‖C_{j+1}‖_{Φ_{j+1}(ℓ_{j+1})} ≤ 1`). -/
theorem abs_cov_le {j : ℕ} {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) {C : Matrix (Lam d L N) (Lam d L N) ℝ}
    (hC : GoodCov j ℓ₀ C) (x y : Lam d L N) : |C x y| ≤ ellj d L ℓ₀ (j + 1) ^ 2 := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have h := abs_le_of_phiNorm_le (Lpow_pos (L := L) (j + 1)) (ellj_pos (d := d) hL0 hℓ₀ (j + 1))
    zero_le_one (by rw [ENNReal.ofReal_one]; exact hC.norm) (g := covTest C)
    ![((x, -1) : Sf (Lam d L N)), (y, 1)]
  rw [covTest_two] at h
  simpa [Complex.norm_real] using h

end

end Obs
