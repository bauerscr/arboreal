import Step2.Map.TwoScale
import Step.EstNonlinAux

/-!
# The doubled-algebra norm with two field scales

On `𝒩(Λ ⊔ Λ)` the field `ψ` is measured at `ℓ'` and the fluctuation field `ζ` at `ℓ_C`:
`‖x‖_{T(ℓ' ⊔ ℓ_C)} = ‖σ_λ x‖_{T(ℓ')}` with `λ = ℓ_C/ℓ'` (`T2`). Since `σ_λ` is an algebra
homomorphism fixing the first copy, `T2` inherits the algebra estimates of `tNorm`, and

* `T2_theta_le`: `‖θ F‖_{T(ℓ' ⊔ ℓ_C)} ≤ ‖F‖_{T(ℓ' + ℓ_C)}`;
* `T2_incl_le`: `‖F‖_{T(ℓ' ⊔ ℓ_C)} ≤ ‖F‖_{T(ℓ')}` on the first copy;
* `tNorm_ECC_le_T2`: `‖𝔼_C x‖_{T(ℓ')} ≤ ‖x‖_{T(ℓ' ⊔ ℓ_C)}` for a Gram bound at `ℓ_C`;
* `T2_self`: `T2` at `ℓ_C = ℓ'` is the old norm.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

section Gen

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ] {E : Type*} [Fintype E] [DecidableEq E]
  [AddAction (E → ℕ) Λ] {p : ℕ} {h ℓ' ℓC : ℝ}

/-- The ratio `λ = ℓ_C/ℓ'` as a complex number. -/
def rat2 (ℓ' ℓC : ℝ) : ℂ := ((ℓC / ℓ' : ℝ) : ℂ)

variable (E p h ℓ' ℓC) in
/-- The doubled-algebra norm `‖x‖_{T(ℓ' ⊔ ℓ_C)}`. -/
def T2 (x : N (Λ ⊕ Λ)) : ENNReal := tNorm E p h ℓ' (sigR (rat2 ℓ' ℓC) x)

theorem T2_mul_le (hh : 0 < h) (hℓ : 0 < ℓ') (x y : N (Λ ⊕ Λ)) :
    T2 E p h ℓ' ℓC (x * y) ≤ T2 E p h ℓ' ℓC x * T2 E p h ℓ' ℓC y := by
  rw [T2, map_mul]; exact tNorm_mul_le hh hℓ _ _

theorem T2_add_le (x y : N (Λ ⊕ Λ)) :
    T2 E p h ℓ' ℓC (x + y) ≤ T2 E p h ℓ' ℓC x + T2 E p h ℓ' ℓC y := by
  rw [T2, map_add]; exact tNorm_add_le _ _

theorem T2_smul (c : ℂ) (x : N (Λ ⊕ Λ)) :
    T2 E p h ℓ' ℓC (c • x) = ENNReal.ofReal ‖c‖ * T2 E p h ℓ' ℓC x := by
  rw [T2, map_smul, tNorm_smul]; rfl

theorem T2_zero : T2 E p h ℓ' ℓC (0 : N (Λ ⊕ Λ)) = 0 := by rw [T2, map_zero, tn_zero']

theorem T2_one_le (hh : 0 < h) (hℓ : 0 < ℓ') : T2 E p h ℓ' ℓC (1 : N (Λ ⊕ Λ)) ≤ 1 := by
  rw [T2, map_one]; exact tNorm_one_le hh hℓ

/-! #### Versions for the even subalgebra, as in `Step.EstNonlinAux` -/

theorem t2_mulE (hh : 0 < h) (hℓ : 0 < ℓ') {F G : EvR (Λ ⊕ Λ)} {s t : ℝ} (hs : 0 ≤ s)
    (hF : T2 E p h ℓ' ℓC (F : N (Λ ⊕ Λ)) ≤ ENNReal.ofReal s)
    (hG : T2 E p h ℓ' ℓC (G : N (Λ ⊕ Λ)) ≤ ENNReal.ofReal t) :
    T2 E p h ℓ' ℓC ((F * G : EvR (Λ ⊕ Λ)) : N (Λ ⊕ Λ)) ≤ ENNReal.ofReal (s * t) := by
  rw [MulMemClass.coe_mul]
  exact (T2_mul_le hh hℓ _ _).trans (by rw [ENNReal.ofReal_mul hs]; exact mul_le_mul' hF hG)

theorem t2_prodE (hh : 0 < h) (hℓ : 0 < ℓ') {ι : Type*} (s : Finset ι) (F : ι → EvR (Λ ⊕ Λ))
    (r : ι → ℝ) (hr : ∀ i ∈ s, 0 ≤ r i)
    (hF : ∀ i ∈ s, T2 E p h ℓ' ℓC (F i : N (Λ ⊕ Λ)) ≤ ENNReal.ofReal (r i)) :
    T2 E p h ℓ' ℓC ((∏ i ∈ s, F i : EvR (Λ ⊕ Λ)) : N (Λ ⊕ Λ)) ≤ ENNReal.ofReal (∏ i ∈ s, r i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [prod_empty, prod_empty, OneMemClass.coe_one, ENNReal.ofReal_one]
    exact T2_one_le hh hℓ
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha]
    exact t2_mulE hh hℓ (hr a (mem_insert_self a s)) (hF a (mem_insert_self a s))
      (ih (fun i hi => hr i (mem_insert_of_mem hi)) fun i hi => hF i (mem_insert_of_mem hi))

theorem t2_sumE {ι : Type*} (s : Finset ι) (F : ι → EvR (Λ ⊕ Λ)) (r : ι → ℝ)
    (hr : ∀ i ∈ s, 0 ≤ r i)
    (hF : ∀ i ∈ s, T2 E p h ℓ' ℓC (F i : N (Λ ⊕ Λ)) ≤ ENNReal.ofReal (r i)) :
    T2 E p h ℓ' ℓC ((∑ i ∈ s, F i : EvR (Λ ⊕ Λ)) : N (Λ ⊕ Λ)) ≤ ENNReal.ofReal (∑ i ∈ s, r i) := by
  rw [AddSubmonoidClass.coe_finsetSum, T2, map_sum]
  exact (tNorm_sum_le _ _).trans
    (by rw [ENNReal.ofReal_sum_of_nonneg hr]; exact sum_le_sum hF)

theorem t2_sum_const {ι : Type*} (s : Finset ι) (F : ι → EvR (Λ ⊕ Λ)) {r : ℝ} (hr : 0 ≤ r)
    (hF : ∀ i ∈ s, T2 E p h ℓ' ℓC (F i : N (Λ ⊕ Λ)) ≤ ENNReal.ofReal r) :
    T2 E p h ℓ' ℓC ((∑ i ∈ s, F i : EvR (Λ ⊕ Λ)) : N (Λ ⊕ Λ)) ≤ ENNReal.ofReal (s.card * r) := by
  have := t2_sumE s F (fun _ => r) (fun _ _ => hr) hF
  rwa [sum_const, nsmul_eq_mul] at this

theorem t2_subE {F G : EvR (Λ ⊕ Λ)} {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hF : T2 E p h ℓ' ℓC (F : N (Λ ⊕ Λ)) ≤ ENNReal.ofReal s)
    (hG : T2 E p h ℓ' ℓC (G : N (Λ ⊕ Λ)) ≤ ENNReal.ofReal t) :
    T2 E p h ℓ' ℓC ((F - G : EvR (Λ ⊕ Λ)) : N (Λ ⊕ Λ)) ≤ ENNReal.ofReal (s + t) := by
  rw [AddSubgroupClass.coe_sub, T2, map_sub]; exact tn_sub hs ht hF hG

/-! #### The doubling map, the first copy, and the expectation -/

/-- `‖θ F‖_{T(ℓ' ⊔ ℓ_C)} ≤ ‖F‖_{T(ℓ' + ℓ_C)}`. -/
theorem T2_theta_le (hh : 0 < h) (hℓ : 0 < ℓ') (hℓC : 0 ≤ ℓC) (F : N Λ) :
    T2 E p h ℓ' ℓC (theta F) ≤ tNorm E p h (ℓ' + ℓC) F := by
  rw [T2, ← thetaL_eq, rat2]
  have e : (1 + ℓC / ℓ') * ℓ' = ℓ' + ℓC := by field_simp
  rw [← e]
  exact tNorm_thetaL_le hh hℓ (by positivity) F

theorem T2_incl_le (hh : 0 < h) (hℓ : 0 < ℓ') (F : N Λ) :
    T2 E p h ℓ' ℓC (incl F) ≤ tNorm E p h ℓ' F := by
  rw [T2, sigR_incl]; exact tNorm_incl_le hh hℓ F

/-- `‖𝔼_C x‖_{T(ℓ')} ≤ ‖x‖_{T(ℓ' ⊔ ℓ_C)}` for a covariance with a Gram bound at `ℓ_C`. -/
theorem tNorm_ECC_le_T2 (hh : 0 < h) (hℓ : 0 < ℓ') (hℓC : 0 < ℓC) {C : Matrix Λ Λ ℂ}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {Fv Gv : Λ → H}
    (hC : IsGram C Fv Gv) (hB : GramBound E p h ℓC Fv Gv) (x : N (Λ ⊕ Λ)) :
    tNorm E p h ℓ' (ECC C x) ≤ T2 E p h ℓ' ℓC x := by
  set c : ℝ := ℓC / ℓ' with hc
  have hc0 : 0 < c := by positivity
  have hcℓ : c⁻¹ * ℓC = ℓ' := by rw [hc]; field_simp
  have hB' := gramBound_smul_real hB hc0
  rw [hcℓ] at hB'
  rw [ECC_sigR (c := (c : ℂ)) (by exact_mod_cast hc0.ne') C x, T2, rat2]
  exact tNorm_ECC_le hh hℓ (isGram_smul_real hC hc0.ne') hB' _

end Gen

/-! ### At scale `j + 1` -/

variable {d L N : ℕ} [NeZero L]

theorem GoodCov2.mono {j : ℕ} {ℓ ℓ' : ℝ} {C : Matrix (Lam d L N) (Lam d L N) ℂ} (hℓ : ℓ ≤ ℓ')
    (hC : GoodCov2 j ℓ C) : GoodCov2 j ℓ' C := by
  obtain ⟨H, i1, i2, Fv, Gv, hG, hB⟩ := hC.gram
  refine ⟨⟨H, i1, i2, Fv, Gv, hG, fun a ha x => ?_⟩, hC.range⟩
  obtain ⟨h1, h2⟩ := hB a ha x
  have hp : 0 ≤ (((L : ℝ) ^ (j + 1)) ^ Grassmann.mabs a)⁻¹ := by positivity
  exact ⟨h1.trans (mul_le_mul_of_nonneg_right hℓ hp), h2.trans (mul_le_mul_of_nonneg_right hℓ hp)⟩

/-- `‖𝔼_C x‖_{T_{j+1}(ℓ')} ≤ ‖x‖_{T_{j+1}(ℓ' ⊔ ℓ_C)}`. -/
theorem ECC_succ_le2 {j : ℕ} {ℓ' ℓC : ℝ} (hℓ : 0 < ℓ') (hℓC : 0 < ℓC)
    {C : Matrix (Lam d L N) (Lam d L N) ℂ} (hC : GoodCov2 j ℓC C) (x : Alg2 d L N) :
    Tj d (L : ℝ) (j + 1) ℓ' (ECC C x) ≤ T2 (Dir d) (pPhi d) ((L : ℝ) ^ (j + 1)) ℓ' ℓC x := by
  obtain ⟨H, _, _, Fv, Gv, hG, hB⟩ := hC.gram
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  exact tNorm_ECC_le_T2 (by positivity) hℓ hℓC hG hB x

/-- `‖θ F‖_{T_{j+1}(ℓ' ⊔ ℓ_C)} ≤ q^{|𝓑(Y)|} ‖F‖_{T_j(ℓ)}` if `ℓ' + ℓ_C ≤ 2ℓ`. -/
theorem theta_succ_le2 (hd : 1 ≤ d) (hL : pauliL0 d ≤ L) {j : ℕ} (hj : j < N)
    {Y : Finset (Lam d L N)} {F : Alg d L N} (hF : F ∈ NX (↑Y : Set (Lam d L N))) {ℓ ℓ' ℓC : ℝ}
    (hℓ' : 0 < ℓ') (hℓC : 0 < ℓC) (hsum : ℓ' + ℓC ≤ 2 * ℓ) :
    T2 (Dir d) (pPhi d) ((L : ℝ) ^ (j + 1)) ℓ' ℓC (theta F) ≤
      ENNReal.ofReal (pq d ^ nb j Y) * Tj d (L : ℝ) j ℓ F := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hh : (0 : ℝ) < (L : ℝ) ^ (j + 1) := by positivity
  refine (T2_theta_le hh hℓ' hℓC.le F).trans ?_
  refine (tNorm_mono hh.le le_rfl (by positivity) hsum F).trans ?_
  exact Tj_succ_two_le hd hL hj hF (by linarith)

/-- `‖𝔼_C θ F‖_{T_{j+1}(ℓ')} ≤ ‖F‖_{T_{j+1}(2ℓ)}` if `ℓ' + ℓ_C ≤ 2ℓ`. -/
theorem EthE_succ_le2' {j : ℕ} {ℓ ℓ' ℓC : ℝ} (hℓ' : 0 < ℓ') (hℓC : 0 < ℓC)
    (hsum : ℓ' + ℓC ≤ 2 * ℓ) {C : Matrix (Lam d L N) (Lam d L N) ℂ} (hC : GoodCov2 j ℓC C)
    (F : Alg d L N) :
    Tj d (L : ℝ) (j + 1) ℓ' (ECC C (theta F)) ≤ Tj d (L : ℝ) (j + 1) (2 * ℓ) F := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hh : (0 : ℝ) < (L : ℝ) ^ (j + 1) := by positivity
  refine (ECC_succ_le2 hℓ' hℓC hC _).trans ((T2_theta_le hh hℓ' hℓC.le F).trans ?_)
  exact tNorm_mono hh.le le_rfl (by positivity) hsum F

/-- The truncated expectation with two field scales. -/
theorem FC_succ_le2 {j : ℕ} {ℓ ℓ' ℓC : ℝ} (hℓ' : 0 < ℓ') (hℓC : 0 < ℓC)
    (hsum : ℓ' + ℓC ≤ 2 * ℓ) {C : Matrix (Lam d L N) (Lam d L N) ℂ} (hC : GoodCov2 j ℓC C)
    (A B : Alg d L N) :
    Tj d (L : ℝ) (j + 1) ℓ' (FC C (ECC C (theta A)) (ECC C (theta B))) ≤
      2 * (Tj d (L : ℝ) (j + 1) (2 * ℓ) A * Tj d (L : ℝ) (j + 1) (2 * ℓ) B) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hh : (0 : ℝ) < (L : ℝ) ^ (j + 1) := by positivity
  have hℓ : 0 < ℓ := by linarith
  rw [FC_ECC_theta]
  refine (tNorm_sub_le _ _).trans ?_
  have h1 := (EthE_succ_le2' hℓ' hℓC hsum hC (A * B)).trans
    (tNorm_mul_le hh (by positivity) A B)
  have h2 := (tNorm_mul_le hh hℓ' (ECC C (theta A)) (ECC C (theta B))).trans
    (mul_le_mul' (EthE_succ_le2' hℓ' hℓC hsum hC A) (EthE_succ_le2' hℓ' hℓC hsum hC B))
  calc _ ≤ Tj d (L : ℝ) (j + 1) (2 * ℓ) A * Tj d (L : ℝ) (j + 1) (2 * ℓ) B +
        Tj d (L : ℝ) (j + 1) (2 * ℓ) A * Tj d (L : ℝ) (j + 1) (2 * ℓ) B := add_le_add h1 h2
    _ = _ := (two_mul _).symm

end

end Step2
