import Obs.StepObsLargeAux

/-!
# Block estimates for the large set bound

For the observable map: the bulk part of `δI(B)` is Step's `δI(B)` (`bulk_dIoL`), the observable
part of `δI(B)` vanishes unless `B` contains `a` or `b` (`πobs_dIo_eq_zero`) and is bounded
by `O(‖V^obs‖ + L^{2(d-2)} ‖K^obs‖)` (`n2_πobs_dIo_le`), and for `a ∈ B₁ ∌ b`, `b ∈ B₂ ∌ a` with
`C(a, b) = 0` the product of the observable parts has expectation of second order in `K^obs`
up to terms with a bulk factor (`e:deltaI-obs-4`, `ECO_πobs_dIo_mul_le`).
-/

namespace Obs

noncomputable section

open Finset Grassmann SA Loc Step LocObs Gen

variable {d L N : ℕ} [NeZero L]

section Alg

variable {c : Case} (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (Vb : Vcoup) (Vo : Coup c)
  (K : Finset (Lam d L N) → OE c (Lam d L N)) (a b : Lam d L N)

/-- `δI(B)` of the observable map. -/
abbrev dIoL (p : Fin d → ℕ) : OE c (Lam d L N ⊕ Lam d L N) :=
  dIG (obsA c C) (obsI j C Vb Vo K a b) p

theorem bulk_dIoL (p : Fin d → ℕ) : bulk (dIoL j C Vb Vo K a b p) = dI j C Vb (bulkK K) p := by
  rw [← dIG_bulk, ← map_bulk_obsI j C Vb Vo K a b]
  simp only [dIoL, dIG, It, RGIngr.map, obsA, bulkA, map_sub, map_mul, bulk_thetaO, bulk_inclO]

theorem I0_eqL (p : Fin d → ℕ) : (obsI j C Vb Vo K a b).I0 p =
    algebraMap ℂ (OE c (Lam d L N)) (Complex.exp 0) *
      oexp (-(emb (VE Vb (blockSet j p)) + splitO c (Coup.toV c Vo) a b (blockSet j p))) := by
  rw [Complex.exp_zero, map_one, one_mul]; rfl

theorem It_eqL (p : Fin d → ℕ) : It (obsI j C Vb Vo K a b) p =
    algebraMap ℂ (OE c (Lam d L N))
        (Complex.exp (-((uVb j C Vb K).1 * (blockSet (L := L) (N := N) j p).card))) *
      oexp (-(emb (VE (uVb j C Vb K).2 (blockSet j p)) +
        splitO c (nextObs C j Vo K a b) a b (blockSet j p))) := by
  simp only [It, obsI]
  rw [mul_assoc, ← oexp_add (isNilpotent_of_obs (by rw [map_neg, bulk_uObsX, neg_zero]))
    (isNilpotent_VfullX a b _ _ _).neg]
  congr 2
  rw [VfullX, uObsX, ← splitO_toU_add_toV c (nextObs C j Vo K a b) a b]
  abel

theorem πobs_dIoL (p : Fin d → ℕ) : πobs (dIoL j C Vb Vo K a b p) =
    thetaO (πobs ((obsI j C Vb Vo K a b).I0 p)) - inclO (πobs (It (obsI j C Vb Vo K a b) p)) := by
  simp only [dIoL, dIG, obsA, map_sub, πobs_thetaOL, πobs_inclOL]

theorem splitO_not_mem (W : Coup c) {B : Finset (Lam d L N)} (ha : a ∉ B) (hb : b ∉ B) :
    splitO c W a b B = 0 := by
  rw [splitO_congr c W a b (Y := ∅) (by simp [ha]) (by simp [hb]), splitO_empty]

theorem πobs_dIo_eq_zero (p : Fin d → ℕ) (ha : a ∉ blockSet (L := L) (N := N) j p)
    (hb : b ∉ blockSet (L := L) (N := N) j p) : πobs (dIoL j C Vb Vo K a b p) = 0 := by
  have key : ∀ (z : ℂ) (V : Vcoup), πobs (algebraMap ℂ (OE c (Lam d L N)) z *
      oexp (-(emb (VE V (blockSet j p)) + (0 : OE c (Lam d L N))))) = 0 := by
    intro z V
    rw [add_zero, ← map_neg, oexp_emb (by simp [Step.Coup.eval_ε0]), ← AlgHom.commutes emb z, ← map_mul,
      πobs_emb]
  rw [πobs_dIoL, I0_eqL, It_eqL, splitO_not_mem a b _ ha hb, splitO_not_mem a b _ ha hb, key, key,
    map_zero, map_zero, sub_zero]

end Alg

/-! ### Supports of the half evaluations -/

section Supp

variable {c : Case} {a b : Lam d L N}

theorem halfA_a_memL (W : Coup c) : (halfA c W a b).a ∈ NX ({a} : Set (Lam d L N)) := by
  cases c
  · exact Subalgebra.smul_mem _ (ψ_mem_NX (Set.mem_singleton a)) _
  · exact sub_mem (Subalgebra.algebraMap_mem _ _) (Subalgebra.smul_mem _
      (mul_mem (ψ_mem_NX (Set.mem_singleton a)) (ψ_mem_NX (Set.mem_singleton a))) _)

theorem halfB_b_memL (W : Coup c) : (halfB c W a b).b ∈ NX ({b} : Set (Lam d L N)) := by
  cases c
  · exact Subalgebra.smul_mem _ (ψ_mem_NX (Set.mem_singleton b)) _
  · exact sub_mem (Subalgebra.algebraMap_mem _ _) (Subalgebra.smul_mem _
      (mul_mem (ψ_mem_NX (Set.mem_singleton b)) (ψ_mem_NX (Set.mem_singleton b))) _)

theorem halfA_e' (W : Coup c) : (halfA c W a b).e = 0 := by cases c <;> rfl
theorem halfA_b' (W : Coup c) : (halfA c W a b).b = 0 := by cases c <;> rfl
theorem halfB_e' (W : Coup c) : (halfB c W a b).e = 0 := by cases c <;> rfl
theorem halfB_a' (W : Coup c) : (halfB c W a b).a = 0 := by cases c <;> rfl

theorem splitS_of_a (W : Coup c) {B : Finset (Lam d L N)} (ha : a ∈ B) (hb : b ∉ B) :
    splitS c W a b B = halfA c W a b := by
  simp [splitS, ha, hb]

theorem splitS_of_b (W : Coup c) {B : Finset (Lam d L N)} (ha : a ∉ B) (hb : b ∈ B) :
    splitS c W a b B = halfB c W a b := by
  simp [splitS, ha, hb]

/-- **Factorisation** of `𝔼[θ G₁ θ G₂]` for `G₁` living at `a` (only an `a` component) and `G₂`
living at `b`, if `C(a, b) = C(b, a) = 0`. -/
theorem ECO_theta_mul_of_sep {C : Matrix (Lam d L N) (Lam d L N) ℝ} (hab : a ≠ b)
    (hC1 : C a b = 0) (hC2 : C b a = 0) {G₁ G₂ : OE c (Lam d L N)}
    (h1e : (G₁ : SA c (Lam d L N)).e = 0) (h1b : (G₁ : SA c (Lam d L N)).b = 0)
    (h1a : (G₁ : SA c (Lam d L N)).a ∈ NX ({a} : Set (Lam d L N)))
    (h2e : (G₂ : SA c (Lam d L N)).e = 0) (h2a : (G₂ : SA c (Lam d L N)).a = 0)
    (h2b : (G₂ : SA c (Lam d L N)).b ∈ NX ({b} : Set (Lam d L N))) :
    ECO C (thetaO G₁ * thetaO G₂) = ECO C (thetaO G₁) * ECO C (thetaO G₂) := by
  have hX : ∀ x ∈ ({a} : Set (Lam d L N)), ∀ y ∈ ({b} : Set (Lam d L N)),
      x ≠ y ∧ C x y = 0 ∧ C y x = 0 := by
    intro x hx y hy
    rw [Set.mem_singleton_iff] at hx hy
    subst hx hy
    exact ⟨hab, hC1, hC2⟩
  have m := EC_mul_of_sep hX (theta_mem_NX2 h1a) (theta_mem_NX2 h2b)
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_)
  · rw [OE.mul_e, coe_ECO, ECS_e, OE.mul_e, coe_ECO, coe_ECO, ECS_e, ECS_e]
    simp [h1e, h2e]
  · rw [OE.mul_a, coe_ECO, ECS_a, OE.mul_a, coe_ECO, coe_ECO, ECS_e, ECS_e, ECS_a, ECS_a]
    simp [h1e, h2e]
  · rw [OE.mul_b, coe_ECO, ECS_b, OE.mul_b, coe_ECO, coe_ECO, ECS_e, ECS_e, ECS_b, ECS_b]
    simp [h1e, h2e]
  · rw [OE.mul_ab, coe_ECO, ECS_ab, OE.mul_ab, coe_ECO, coe_ECO, ECS_e, ECS_e, ECS_a, ECS_a,
      ECS_b, ECS_b, ECS_ab, ECS_ab]
    simp only [coe_thetaO, thetaS_e, thetaS_a, thetaS_b, thetaS_ab, h1e, h2e, h1b, h2a, map_zero,
      zero_mul, mul_zero, add_zero, zero_add, map_smul]
    rw [m]

end Supp

/-! ### `IsAB` and the doubling -/

section AB

variable {c : Case} {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

theorem IsAB.thetaO {F : OE c Λ} (hF : IsAB F) : IsAB (thetaO F) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [hF.1, hF.2.1, hF.2.2]

theorem IsAB.inclO {F : OE c Λ} (hF : IsAB F) : IsAB (inclO F) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [hF.1, hF.2.1, hF.2.2]

theorem IsAB.mul_eq_zero' {F G : OE c Λ} (hF : IsAB F) (hG : bulk G = 0) : G * F = 0 := by
  rw [mul_comm]; exact hF.mul_eq_zero hG

end AB

/-! ### The expansion of `π_obs δI(B)` -/

section Expansion

variable {c : Case} (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (Vb : Vcoup) (Vo : Coup c)
  (K : Finset (Lam d L N) → OE c (Lam d L N)) (a b : Lam d L N)

/-- `V^obs_j(B)`. -/
abbrev Gv (p : Fin d → ℕ) : OE c (Lam d L N) := Vobs j Vo a b p

/-- `(u + V)^obs_{j+1}(B)`. -/
abbrev Gn (p : Fin d → ℕ) : OE c (Lam d L N) := splitO c (nextObs C j Vo K a b) a b (blockSet j p)

/-- The remainder of `π_obs e^{-V_j(B)} = -V^obs_j(B) + ½ V^obs_j(B)² + R`. -/
def Rv (p : Fin d → ℕ) : OE c (Lam d L N) :=
  πobs ((obsI j C Vb Vo K a b).I0 p) - (-Gv j Vo a b p + (1 / 2 : ℂ) • Gv j Vo a b p ^ 2)

/-- The remainder of `π_obs e^{-(u+V)_{j+1}(B)} = -(u+V)^obs(B) + ½ (u+V)^obs(B)² + R'`. -/
def Rn (p : Fin d → ℕ) : OE c (Lam d L N) :=
  πobs (It (obsI j C Vb Vo K a b) p) -
    (-Gn j C Vo K a b p + (1 / 2 : ℂ) • Gn j C Vo K a b p ^ 2)

/-- The linear part `-θ V^obs_j(B) + (u + V)^obs_{j+1}(B)` of `π_obs δI(B)`. -/
def Mo (p : Fin d → ℕ) : OE c (Lam d L N ⊕ Lam d L N) :=
  -thetaO (Gv j Vo a b p) + inclO (Gn j C Vo K a b p)

/-- The quadratic part (only an `ab` component). -/
def Ho (p : Fin d → ℕ) : OE c (Lam d L N ⊕ Lam d L N) :=
  (1 / 2 : ℂ) • thetaO (Gv j Vo a b p ^ 2) - (1 / 2 : ℂ) • inclO (Gn j C Vo K a b p ^ 2)

/-- The remainder part (with a bulk factor). -/
def Zo (p : Fin d → ℕ) : OE c (Lam d L N ⊕ Lam d L N) :=
  thetaO (Rv j C Vb Vo K a b p) - inclO (Rn j C Vb Vo K a b p)

/-- `P^obs`-type correction: `(u+V)^obs_{j+1}(B) - (𝔼 θ V^obs(B) - ½ 𝔼[θ V^obs(B); θ V^obs(Λ)])`. -/
def Dl (p : Fin d → ℕ) : OE c (Lam d L N) :=
  Gn j C Vo K a b p - (ECO C (thetaO (Gv j Vo a b p)) -
    (1 / 2 : ℂ) • ECT C (Gv j Vo a b p) (evalO c (Coup.toV c Vo) a b univ))

theorem πobs_dIo_eq_MHZ (p : Fin d → ℕ) :
    πobs (dIoL j C Vb Vo K a b p) = Mo j C Vo K a b p + Ho j C Vo K a b p + Zo j C Vb Vo K a b p := by
  rw [πobs_dIoL]
  simp only [Mo, Ho, Zo, Rv, Rn, map_sub, map_add, map_neg, map_smul, map_pow]
  abel

theorem bulk_Gv (p : Fin d → ℕ) : bulk (Gv j Vo a b p) = 0 := bulk_splitO _ _ _ _ _
theorem bulk_Gn (p : Fin d → ℕ) : bulk (Gn j C Vo K a b p) = 0 := bulk_splitO _ _ _ _ _

theorem bulk_Mo (p : Fin d → ℕ) : bulk (Mo j C Vo K a b p) = 0 := by
  simp [Mo, bulk_thetaO, bulk_inclO, bulk_Gv, bulk_Gn]

theorem bulk_Zo (p : Fin d → ℕ) : bulk (Zo j C Vb Vo K a b p) = 0 := by
  simp [Zo, Rv, Rn, bulk_thetaO, bulk_inclO, bulk_Gv, bulk_Gn, bulk_πobs]

theorem isAB_Ho (p : Fin d → ℕ) : IsAB (Ho j C Vo K a b p) := by
  have h1 : IsAB (Gv j Vo a b p ^ 2) := by
    rw [pow_two]; exact isAB_mul (bulk_Gv j Vo a b p) (bulk_Gv j Vo a b p)
  have h2 : IsAB (Gn j C Vo K a b p ^ 2) := by
    rw [pow_two]; exact isAB_mul (bulk_Gn j C Vo K a b p) (bulk_Gn j C Vo K a b p)
  exact (h1.thetaO.smul _).sub (h2.inclO.smul _)

theorem bulk_Dl (p : Fin d → ℕ) : bulk (Dl j C Vo K a b p) = 0 := by
  have hT := (isAB_ECT C (bulk_Gv j Vo a b p) (bulk_evalO c (Coup.toV c Vo) a b univ)).bulk_eq_zero
  simp only [Dl, map_sub, map_smul, hT, bulk_Gn, bulk_ECO_thetaO (bulk_Gv j Vo a b p)]
  simp

set_option maxHeartbeats 2000000 in
/-- **`e:deltaI-obs-4`, algebraic part**: for `a ∈ B₁ ∌ b`, `b ∈ B₂ ∌ a` and `C(a, b) = 0`,
`𝔼[π_obs δI(B₁) π_obs δI(B₂)] = D(B₁) D(B₂) + 𝔼[M₁ Z₂ + Z₁ M₂ + Z₁ Z₂]`. -/
theorem ECO_πobs_dIo_mul {p₁ p₂ : Fin d → ℕ} (hab : a ≠ b) (hC1 : C a b = 0) (hC2 : C b a = 0)
    (ha1 : a ∈ blockSet (L := L) (N := N) j p₁) (hb1 : b ∉ blockSet (L := L) (N := N) j p₁)
    (ha2 : a ∉ blockSet (L := L) (N := N) j p₂) (hb2 : b ∈ blockSet (L := L) (N := N) j p₂) :
    ECO C (πobs (dIoL j C Vb Vo K a b p₁) * πobs (dIoL j C Vb Vo K a b p₂)) =
      Dl j C Vo K a b p₁ * Dl j C Vo K a b p₂ +
        ECO C (Mo j C Vo K a b p₁ * Zo j C Vb Vo K a b p₂ +
          Zo j C Vb Vo K a b p₁ * Mo j C Vo K a b p₂ +
          Zo j C Vb Vo K a b p₁ * Zo j C Vb Vo K a b p₂) := by
  set M1 := Mo j C Vo K a b p₁
  set M2 := Mo j C Vo K a b p₂
  set Z1 := Zo j C Vb Vo K a b p₁
  set Z2 := Zo j C Vb Vo K a b p₂
  set H1 := Ho j C Vo K a b p₁
  set H2 := Ho j C Vo K a b p₂
  have hMZ1 : bulk (M1 + Z1) = 0 := by
    rw [map_add, bulk_Mo, bulk_Zo, add_zero]
  have hMHZ2 : bulk (M2 + H2 + Z2) = 0 := by
    rw [map_add, map_add, bulk_Mo, bulk_Zo, (isAB_Ho j C Vo K a b p₂).bulk_eq_zero]; simp
  have e1 : πobs (dIoL j C Vb Vo K a b p₁) * πobs (dIoL j C Vb Vo K a b p₂) =
      M1 * M2 + (M1 * Z2 + Z1 * M2 + Z1 * Z2) := by
    rw [πobs_dIo_eq_MHZ, πobs_dIo_eq_MHZ]
    have h1 : H1 * (M2 + H2 + Z2) = 0 := (isAB_Ho j C Vo K a b p₁).mul_eq_zero hMHZ2
    have h2 : (M1 + Z1) * H2 = 0 := (isAB_Ho j C Vo K a b p₂).mul_eq_zero' hMZ1
    linear_combination h1 + h2
  rw [e1, map_add]
  congr 1
  -- the linear part
  set G1 := Gv j Vo a b p₁
  set G2 := Gv j Vo a b p₂
  set G1' := Gn j C Vo K a b p₁
  set G2' := Gn j C Vo K a b p₂
  have hsep : ECO C (thetaO G1 * thetaO G2) = ECO C (thetaO G1) * ECO C (thetaO G2) := by
    have s1 : (G1 : SA c (Lam d L N)) = halfA c (Coup.toV c Vo) a b := by
      show splitS c _ a b _ = _; exact splitS_of_a _ ha1 hb1
    have s2 : (G2 : SA c (Lam d L N)) = halfB c (Coup.toV c Vo) a b := by
      show splitS c _ a b _ = _; exact splitS_of_b _ ha2 hb2
    refine ECO_theta_mul_of_sep hab hC1 hC2 ?_ ?_ ?_ ?_ ?_ ?_
    · rw [s1, halfA_e']
    · rw [s1, halfA_b']
    · rw [s1]; exact halfA_a_memL _
    · rw [s2, halfB_e']
    · rw [s2, halfB_a']
    · rw [s2]; exact halfB_b_memL _
  have eM : M1 * M2 = thetaO G1 * thetaO G2 - inclO G1' * thetaO G2 - inclO G2' * thetaO G1 +
      inclO (G1' * G2') := by
    simp only [M1, M2, Mo, map_mul]; ring
  -- `D_k = ½ T_k - (𝔼θG_k - G'_k)` with `T_k` an `ab`-element
  have hT : ∀ p, IsAB (ECT C (Gv j Vo a b p) (evalO c (Coup.toV c Vo) a b univ)) := fun p =>
    isAB_ECT C (bulk_Gv j Vo a b p) (bulk_evalO c (Coup.toV c Vo) a b univ)
  have eD' : ∀ p, ECO C (thetaO (Gv j Vo a b p)) - Gn j C Vo K a b p =
      (1 / 2 : ℂ) • ECT C (Gv j Vo a b p) (evalO c (Coup.toV c Vo) a b univ) -
        Dl j C Vo K a b p := by
    intro p; simp only [Dl]; abel
  have hDl := fun p => bulk_Dl j C Vo K a b p
  calc ECO C (M1 * M2) = (ECO C (thetaO G1) - G1') * (ECO C (thetaO G2) - G2') := by
        rw [eM, map_add, map_sub, map_sub, ECO_inclO_mul, ECO_inclO_mul, ECO_inclO, hsep]; ring
    _ = Dl j C Vo K a b p₁ * Dl j C Vo K a b p₂ := by
        rw [eD' p₁, eD' p₂]
        have t1 := ((hT p₁).smul (1 / 2 : ℂ)).mul_eq_zero
          (G := (1 / 2 : ℂ) • ECT C (Gv j Vo a b p₂) (evalO c (Coup.toV c Vo) a b univ) -
            Dl j C Vo K a b p₂)
          (by rw [map_sub, map_smul, (hT p₂).bulk_eq_zero, hDl, smul_zero, sub_zero])
        have t2 := ((hT p₂).smul (1 / 2 : ℂ)).mul_eq_zero' (hDl p₁)
        linear_combination t1 - t2

end Expansion

/-! ### Norms -/

section Norms

variable {c : Case} {ℓ₀ : ℝ} {a b : Lam d L N}

/-- The norm of scale `j + 1` on the doubled algebra. -/
abbrev n2 (c : Case) (ℓ₀ : ℝ) (a b : Lam d L N) (j : ℕ) (F : OE c (Lam d L N ⊕ Lam d L N)) :
    ENNReal :=
  oT (Dir d) (pPhi d) ((L : ℝ) ^ (j + 1)) (ellj d L ℓ₀ (j + 1))
    (wj d L c ℓ₀ (coal L a b : ℕ∞) (j + 1)) (F : SA c (Lam d L N ⊕ Lam d L N))

/-- The norm `T_{j+1}(2 ℓ_{j+1})` with the weights of scale `j + 1`. -/
abbrev n1' (c : Case) (ℓ₀ : ℝ) (a b : Lam d L N) (j : ℕ) (F : OE c (Lam d L N)) : ENNReal :=
  oTj d L (wj d L c ℓ₀ (coal L a b : ℕ∞) (j + 1)) (j + 1) (2 * ellj d L ℓ₀ (j + 1))
    (F : SA c (Lam d L N))

theorem L_pos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)

theorem hpow_pos (j : ℕ) : (0 : ℝ) < (L : ℝ) ^ j := pow_pos L_pos j

theorem n1_ECO_le (hℓ₀ : 0 < ℓ₀) {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℝ}
    (hC : GoodCov j ℓ₀ C) (F : OE c (Lam d L N ⊕ Lam d L N)) :
    nrmj c ℓ₀ a b (j + 1) (ECO C F) ≤ n2 c ℓ₀ a b j F :=
  oT_EC_le (hpow_pos _) (Grassmann.ellj_pos (d := d) (L_pos (L := L)) hℓ₀ _) hC.psd hC.norm _

theorem n2_thetaO_le (hℓ₀ : 0 < ℓ₀) (j : ℕ) (F : OE c (Lam d L N)) :
    n2 c ℓ₀ a b j (thetaO F) ≤ n1' c ℓ₀ a b j F :=
  oT_theta_le (hpow_pos _) (Grassmann.ellj_pos (d := d) (L_pos (L := L)) hℓ₀ _) _

theorem n2_inclO_le (hℓ₀ : 0 < ℓ₀) (j : ℕ) (F : OE c (Lam d L N)) :
    n2 c ℓ₀ a b j (inclO F) ≤ nrmj c ℓ₀ a b (j + 1) F :=
  oT_incl_le (hpow_pos _) (Grassmann.ellj_pos (d := d) (L_pos (L := L)) hℓ₀ _) _

theorem n2_mul_le (hd : 2 ≤ d) (hℓ₀ : 0 < ℓ₀) (j : ℕ) (F G : OE c (Lam d L N ⊕ Lam d L N)) :
    n2 c ℓ₀ a b j (F * G) ≤ n2 c ℓ₀ a b j F * n2 c ℓ₀ a b j G :=
  oT_mul_le (hpow_pos _) (Grassmann.ellj_pos (d := d) (L_pos (L := L)) hℓ₀ _) (wj_sub hd c hℓ₀ _ _) F G

variable (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (Vb : Vcoup) (Vo : Coup c)
  (K : Finset (Lam d L N) → OE c (Lam d L N))

/-- The observable part of `δI(B)`: `‖π_obs δI(B)‖ ≤ e^r (s + s²/2) + e^{α + r'} (s' + s'²/2)`. -/
theorem n2_πobs_dIo_le (hd : 2 ≤ d) (hℓ₀ : 0 < ℓ₀) (p : Fin d → ℕ) {r s α r' s' : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hr' : 0 ≤ r') (hs' : 0 ≤ s')
    (hx : Tj d (L : ℝ) (j + 1) (2 * ellj d L ℓ₀ (j + 1))
      ((VE Vb (blockSet j p) : EvR (Lam d L N)) : Alg d L N) ≤ ENNReal.ofReal r)
    (hG : n1' c ℓ₀ a b j (Gv j Vo a b p) ≤ ENNReal.ofReal s)
    (hz : ‖(uVb j C Vb K).1 * (blockSet (L := L) (N := N) j p).card‖ ≤ α)
    (hx' : Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1))
      ((VE (uVb j C Vb K).2 (blockSet j p) : EvR (Lam d L N)) : Alg d L N) ≤ ENNReal.ofReal r')
    (hG' : nrmj c ℓ₀ a b (j + 1) (Gn j C Vo K a b p) ≤ ENNReal.ofReal s') :
    n2 c ℓ₀ a b j (πobs (dIoL j C Vb Vo K a b p)) ≤
      ENNReal.ofReal (Real.exp r * (s + s ^ 2 / 2) + Real.exp (α + r') * (s' + s' ^ 2 / 2)) := by
  have hh := hpow_pos (L := L) (j + 1)
  have hℓ := Grassmann.ellj_pos (d := d) (L_pos (L := L)) hℓ₀ (j + 1)
  have hw := wj_sub (L := L) hd c hℓ₀ (coal L a b : ℕ∞) (j + 1)
  rw [πobs_dIoL]
  refine (oT_sub_le _ _).trans ?_
  rw [ENNReal.ofReal_add (by positivity) (by positivity)]
  refine add_le_add ((oT_theta_le hh hℓ _).trans ?_) ((oT_incl_le hh hℓ _).trans ?_)
  · rw [I0_eqL]
    refine (oT_πobs_exp_le (by positivity) (by positivity) hw 0 (ε_VE _ _)
      (bulk_splitO _ _ _ _ _) hr hs hx hG).trans ?_
    simp
  · rw [It_eqL]
    refine (oT_πobs_exp_le hh hℓ hw _ (ε_VE _ _) (bulk_splitO _ _ _ _ _) hr' hs' hx' hG').trans ?_
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (by positivity))
    rw [norm_neg]
    exact Real.exp_le_exp.2 (by linarith)

theorem n2_Mo_le (hℓ₀ : 0 < ℓ₀) (p : Fin d → ℕ) {s s' : ℝ} (hs : 0 ≤ s) (hs' : 0 ≤ s')
    (hG : n1' c ℓ₀ a b j (Gv j Vo a b p) ≤ ENNReal.ofReal s)
    (hG' : nrmj c ℓ₀ a b (j + 1) (Gn j C Vo K a b p) ≤ ENNReal.ofReal s') :
    n2 c ℓ₀ a b j (Mo j C Vo K a b p) ≤ ENNReal.ofReal (s + s') := by
  refine (oT_add_le _ _).trans ?_
  rw [NegMemClass.coe_neg, oT_neg, ENNReal.ofReal_add hs hs']
  exact add_le_add ((n2_thetaO_le hℓ₀ j _).trans hG) ((n2_inclO_le hℓ₀ j _).trans hG')

theorem n2_Zo_le (hd : 2 ≤ d) (hℓ₀ : 0 < ℓ₀) (p : Fin d → ℕ) {r s α r' s' : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hr' : 0 ≤ r') (hs' : 0 ≤ s')
    (hx : Tj d (L : ℝ) (j + 1) (2 * ellj d L ℓ₀ (j + 1))
      ((VE Vb (blockSet j p) : EvR (Lam d L N)) : Alg d L N) ≤ ENNReal.ofReal r)
    (hG : n1' c ℓ₀ a b j (Gv j Vo a b p) ≤ ENNReal.ofReal s)
    (hz : ‖(uVb j C Vb K).1 * (blockSet (L := L) (N := N) j p).card‖ ≤ α)
    (hx' : Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1))
      ((VE (uVb j C Vb K).2 (blockSet j p) : EvR (Lam d L N)) : Alg d L N) ≤ ENNReal.ofReal r')
    (hG' : nrmj c ℓ₀ a b (j + 1) (Gn j C Vo K a b p) ≤ ENNReal.ofReal s') :
    n2 c ℓ₀ a b j (Zo j C Vb Vo K a b p) ≤
      ENNReal.ofReal ((Real.exp r - 1) * (s + s ^ 2 / 2) +
        (Real.exp (α + r') - 1) * (s' + s' ^ 2 / 2)) := by
  have hh := hpow_pos (L := L) (j + 1)
  have hℓ := Grassmann.ellj_pos (d := d) (L_pos (L := L)) hℓ₀ (j + 1)
  have hw := wj_sub (L := L) hd c hℓ₀ (coal L a b : ℕ∞) (j + 1)
  have hα : 0 ≤ α := (norm_nonneg _).trans hz
  have e1 : 0 ≤ Real.exp r - 1 := by linarith [Real.add_one_le_exp r]
  have e2 : 0 ≤ Real.exp (α + r') - 1 := by linarith [Real.add_one_le_exp (α + r')]
  refine (oT_sub_le _ _).trans ?_
  rw [ENNReal.ofReal_add (by positivity) (by positivity)]
  refine add_le_add ((oT_theta_le hh hℓ _).trans ?_) ((oT_incl_le hh hℓ _).trans ?_)
  · have := πobs_oexp_expansion_le (by positivity) (by positivity) hw 0 (ε_VE Vb (blockSet j p))
      (bulk_Gv j Vo a b p) hr hs hx hG
    rw [norm_zero, zero_add] at this
    refine le_trans (le_of_eq ?_) this
    rw [Rv, I0_eqL]; rfl
  · have := πobs_oexp_expansion_le hh hℓ hw
      (-((uVb j C Vb K).1 * (blockSet (L := L) (N := N) j p).card))
      (ε_VE (uVb j C Vb K).2 (blockSet j p)) (bulk_Gn j C Vo K a b p) hr' hs' hx' hG'
    refine le_trans (le_of_eq ?_) (this.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right ?_ (by positivity))))
    · rw [Rn, It_eqL]; rfl
    · rw [norm_neg]
      linarith [Real.exp_le_exp.2 (show ‖(uVb j C Vb K).1 *
        (blockSet (L := L) (N := N) j p).card‖ + r' ≤ α + r' by linarith)]

/-- **`e:deltaI-obs-4`**, the bound. -/
theorem n1_ECO_πobs_dIo_mul_le (hd : 2 ≤ d) (hℓ₀ : 0 < ℓ₀) {p₁ p₂ : Fin d → ℕ} (hab : a ≠ b)
    (hC1 : C a b = 0) (hC2 : C b a = 0) (hC : GoodCov j ℓ₀ C)
    (ha1 : a ∈ blockSet (L := L) (N := N) j p₁) (hb1 : b ∉ blockSet (L := L) (N := N) j p₁)
    (ha2 : a ∉ blockSet (L := L) (N := N) j p₂) (hb2 : b ∈ blockSet (L := L) (N := N) j p₂)
    {δ m z : ℝ} (hδ : 0 ≤ δ) (hm : 0 ≤ m) (hz : 0 ≤ z)
    (hD : ∀ p ∈ ({p₁, p₂} : Finset (Fin d → ℕ)),
      nrmj c ℓ₀ a b (j + 1) (Dl j C Vo K a b p) ≤ ENNReal.ofReal δ)
    (hM : ∀ p ∈ ({p₁, p₂} : Finset (Fin d → ℕ)),
      n2 c ℓ₀ a b j (Mo j C Vo K a b p) ≤ ENNReal.ofReal m)
    (hZ : ∀ p ∈ ({p₁, p₂} : Finset (Fin d → ℕ)),
      n2 c ℓ₀ a b j (Zo j C Vb Vo K a b p) ≤ ENNReal.ofReal z) :
    nrmj c ℓ₀ a b (j + 1)
        (ECO C (πobs (dIoL j C Vb Vo K a b p₁) * πobs (dIoL j C Vb Vo K a b p₂))) ≤
      ENNReal.ofReal (δ ^ 2 + 2 * m * z + z ^ 2) := by
  have m1 : p₁ ∈ ({p₁, p₂} : Finset (Fin d → ℕ)) := mem_insert_self _ _
  have m2 : p₂ ∈ ({p₁, p₂} : Finset (Fin d → ℕ)) := mem_insert_of_mem (mem_singleton_self _)
  rw [ECO_πobs_dIo_mul j C Vb Vo K a b hab hC1 hC2 ha1 hb1 ha2 hb2]
  refine (nrmj_add_le _ _ _).trans ?_
  have e : δ ^ 2 + 2 * m * z + z ^ 2 = δ * δ + (m * z + z * m + z * z) := by ring
  rw [e, ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hδ,
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hm,
    ENNReal.ofReal_mul hz, ENNReal.ofReal_mul hz]
  refine add_le_add ((nrmj_mul_le hd hℓ₀ _ _ _).trans (mul_le_mul' (hD _ m1) (hD _ m2))) ?_
  refine (n1_ECO_le hℓ₀ hC _).trans ((oT_add_le _ _).trans (add_le_add
    ((oT_add_le _ _).trans (add_le_add ?_ ?_)) ?_))
  · exact (n2_mul_le hd hℓ₀ j _ _).trans (mul_le_mul' (hM _ m1) (hZ _ m2))
  · exact (n2_mul_le hd hℓ₀ j _ _).trans (mul_le_mul' (hZ _ m1) (hM _ m2))
  · exact (n2_mul_le hd hℓ₀ j _ _).trans (mul_le_mul' (hZ _ m1) (hZ _ m2))

end Norms

/-! ### The prefactor and the products over blocks -/

section Pref

variable {c : Case} {ℓ₀ : ℝ} {a b : Lam d L N} (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℝ)
  (Vb : Vcoup) (Vo : Coup c) (K : Finset (Lam d L N) → OE c (Lam d L N))

theorem n1_VfullX_le (k : ℕ) (V : Vcoup) (W : Coup c) (X : Finset (Lam d L N)) :
    nrmj c ℓ₀ a b k (VfullX V W a b X) ≤
      Tj d (L : ℝ) k (ellj d L ℓ₀ k) (V.eval X) + nrmj c ℓ₀ a b k (splitO c (Coup.toV c W) a b X) := by
  rw [nrmj_split, bulk_VfullX, coe_VE, VfullX, map_add, πobs_emb, zero_add,
    πobs_of_bulk (bulk_splitO _ _ _ _ _)]

/-- The block factors of the prefactor. -/
theorem n1_factor_le (hd : 2 ≤ d) (hℓ₀ : 0 < ℓ₀) (p : Fin d → ℕ) {α s' r' : ℝ} (hs' : 0 ≤ s')
    (hr' : 0 ≤ r')
    (hz : ‖(uVb j C Vb K).1 * (blockSet (L := L) (N := N) j p).card‖ ≤ α)
    (hu : nrmj c ℓ₀ a b (j + 1) (uObsX j C Vo K a b (blockSet j p)) ≤ ENNReal.ofReal s')
    (hV : nrmj c ℓ₀ a b (j + 1) (VfullX (uVb j C Vb K).2 (nextObs C j Vo K a b) a b
      (blockSet j p)) ≤ ENNReal.ofReal r') :
    nrmj c ℓ₀ a b (j + 1) ((obsI j C Vb Vo K a b).eu p - 1) ≤
        ENNReal.ofReal (Real.exp (α + s' + r') - 1) ∧
      nrmj c ℓ₀ a b (j + 1) ((obsI j C Vb Vo K a b).eum p - 1) ≤
        ENNReal.ofReal (Real.exp (α + s' + r') - 1) ∧
      nrmj c ℓ₀ a b (j + 1) ((obsI j C Vb Vo K a b).eV p - 1) ≤
        ENNReal.ofReal (Real.exp (α + s' + r') - 1) := by
  have hh := hpow_pos (L := L) (j + 1)
  have hℓ := Grassmann.ellj_pos (d := d) (L_pos (L := L)) hℓ₀ (j + 1)
  have hw := wj_sub (L := L) hd c hℓ₀ (coal L a b : ℕ∞) (j + 1)
  have hα : 0 ≤ α := (norm_nonneg _).trans hz
  have mono : ∀ x : ℝ, x ≤ α + s' + r' →
      ENNReal.ofReal (Real.exp x - 1) ≤ ENNReal.ofReal (Real.exp (α + s' + r') - 1) :=
    fun x hx => ENNReal.ofReal_le_ofReal (by linarith [Real.exp_le_exp.2 hx])
  have hε : ε ((uObsX j C Vo K a b (blockSet j p) : OE c (Lam d L N)) : SA c (Lam d L N)).e = 0 :=
    ε_bulk_eq_zero_of_obs (bulk_uObsX j C Vo K a b _)
  refine ⟨?_, ?_, ?_⟩
  · exact (oT_exp_oexp_sub_one_le hh hℓ hw _ hε hs' hu).trans (mono _ (by linarith))
  · have hε' : ε ((-uObsX j C Vo K a b (blockSet j p) : OE c (Lam d L N)) :
        SA c (Lam d L N)).e = 0 := by
      rw [NegMemClass.coe_neg, SA.neg_e, map_neg, hε, neg_zero]
    have hu' : nrmj c ℓ₀ a b (j + 1) (-uObsX j C Vo K a b (blockSet j p)) ≤ ENNReal.ofReal s' := by
      rw [nrmj_neg]; exact hu
    refine (oT_exp_oexp_sub_one_le hh hℓ hw _ hε' hs' hu').trans (mono _ ?_)
    rw [norm_neg]; linarith
  · have e : (obsI j C Vb Vo K a b).eV p = algebraMap ℂ (OE c (Lam d L N)) (Complex.exp 0) *
        oexp (-VfullX (uVb j C Vb K).2 (nextObs C j Vo K a b) a b (blockSet j p)) := by
      rw [Complex.exp_zero, map_one, one_mul]; rfl
    have hV' : nrmj c ℓ₀ a b (j + 1)
        (-VfullX (uVb j C Vb K).2 (nextObs C j Vo K a b) a b (blockSet j p)) ≤ ENNReal.ofReal r' := by
      rw [nrmj_neg]; exact hV
    rw [e]
    refine (oT_exp_oexp_sub_one_le hh hℓ hw _ (ε_neg_VfullX a b _ _ _) hr' hV').trans (mono _ ?_)
    rw [norm_zero]; linarith

/-- `‖e^{u(U)} e^{-(u+V)(U ∖ X)} - 1‖ ≤ e^{t |𝓑(U)| + 2 t |𝓑(U ∖ X)|} - 1`. -/
theorem n1_prefG_sub_one_le (hd : 2 ≤ d) (hℓ₀ : 0 < ℓ₀) {t : ℝ} (ht : 0 ≤ t)
    (hf : ∀ p ∈ blockIdx (L := L) (N := N) j,
      nrmj c ℓ₀ a b (j + 1) ((obsI j C Vb Vo K a b).eu p - 1) ≤ ENNReal.ofReal (Real.exp t - 1) ∧
      nrmj c ℓ₀ a b (j + 1) ((obsI j C Vb Vo K a b).eum p - 1) ≤ ENNReal.ofReal (Real.exp t - 1) ∧
      nrmj c ℓ₀ a b (j + 1) ((obsI j C Vb Vo K a b).eV p - 1) ≤ ENNReal.ofReal (Real.exp t - 1))
    (U X : Finset (Lam d L N)) :
    nrmj c ℓ₀ a b (j + 1) (prefG j (obsI j C Vb Vo K a b) U X - 1) ≤
      ENNReal.ofReal (Real.exp (t * nb j U + 2 * t * nb j (U \ X)) - 1) := by
  have hh := hpow_pos (L := L) (j + 1)
  have hℓ := Grassmann.ellj_pos (d := d) (L_pos (L := L)) hℓ₀ (j + 1)
  have hw := wj_sub (L := L) hd c hℓ₀ (coal L a b : ℕ∞) (j + 1)
  have h1 : nrmj c ℓ₀ a b (j + 1) (PrefG j (obsI j C Vb Vo K a b) U - 1) ≤
      ENNReal.ofReal (Real.exp (t * nb j U) - 1) := by
    have := oT_prod_sub_one_le hh hℓ hw (blocks j U) (obsI j C Vb Vo K a b).eu (fun _ => t)
      (fun _ _ => ht) (fun p hp => (hf p (mem_blockIdx_of_mem_blocks hp)).1)
    rw [sum_const, nsmul_eq_mul, mul_comm] at this
    exact this
  have h2 : nrmj c ℓ₀ a b (j + 1) (ItPow j (obsI j C Vb Vo K a b) (U \ X) - 1) ≤
      ENNReal.ofReal (Real.exp (2 * t * nb j (U \ X)) - 1) := by
    have := oT_prod_sub_one_le hh hℓ hw (blocks j (U \ X)) (It (obsI j C Vb Vo K a b))
      (fun _ => 2 * t) (fun _ _ => by positivity) (fun p hp => by
        have hp' := hf p (mem_blockIdx_of_mem_blocks hp)
        have := oT_mul_sub_one_le hh hℓ hw _ _ ht ht hp'.2.1 hp'.2.2
        rw [show t + t = 2 * t by ring] at this
        exact this)
    rw [sum_const, nsmul_eq_mul, mul_comm] at this
    exact this
  exact oT_mul_sub_one_le hh hℓ hw _ _ (by positivity) (by positivity) h1 h2

end Pref

end

end Obs
