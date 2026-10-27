import Obs.StepObsSmallAlg
import Obs.StepObsCoupling

/-!
# Small sets for `thm:step-obs`: estimates

Norm estimates for the proof of `SmallObsStmt'` (`Obs.StepObsSmall`):
* the doubled norm `nrmD` (`‖·‖_{T_{j+1}(ℓ_{j+1})}` on `Λ ⊔ Λ` with the weights of scale
  `j + 1`) and its properties: `𝔼` is a contraction, `‖θ F‖ ≤ L^{2(d-2)} ‖F‖_j`, the product
  property, and the telescoping bound for `π_obs ∏ δI(B)`;
* the bounds on the block quantities (`block_bounds`);
* the contraction `prop:Loc-obs` (ii) for `K^obs` (`Lt_bound`, `lem:smallset-Kobs`).
-/

namespace Obs

noncomputable section

open Finset Grassmann SA Loc Step LocObs Gen

variable {d L N : ℕ} [NeZero L]

/-! ### The doubled norm -/

section D

variable {c : Case} {ℓ₀ : ℝ} {a b : Lam d L N}

variable (c ℓ₀ a b) in
/-- `‖F‖_{T_{j+1}(ℓ_{j+1})}` on `Λ ⊔ Λ`, with the weights of scale `j + 1`. -/
abbrev nrmD (j : ℕ) (F : OE c (Lam d L N ⊕ Lam d L N)) : ENNReal :=
  oT (Dir d) (pPhi d) ((L : ℝ) ^ (j + 1)) (ellj d L ℓ₀ (j + 1))
    (wj d L c ℓ₀ (coal L a b : ℕ∞) (j + 1)) (F : SA c (Lam d L N ⊕ Lam d L N))

theorem nrmD_add_le (j : ℕ) (F G : OE c (Lam d L N ⊕ Lam d L N)) :
    nrmD c ℓ₀ a b j (F + G) ≤ nrmD c ℓ₀ a b j F + nrmD c ℓ₀ a b j G :=
  oT_add_le _ _

theorem nrmD_sub_le (j : ℕ) (F G : OE c (Lam d L N ⊕ Lam d L N)) :
    nrmD c ℓ₀ a b j (F - G) ≤ nrmD c ℓ₀ a b j F + nrmD c ℓ₀ a b j G :=
  oT_sub_le _ _

theorem nrmD_neg (j : ℕ) (F : OE c (Lam d L N ⊕ Lam d L N)) :
    nrmD c ℓ₀ a b j (-F) = nrmD c ℓ₀ a b j F :=
  oT_neg _

theorem nrmD_mul_le (hd : 2 ≤ d) (hℓ₀ : 0 < ℓ₀) (j : ℕ) (F G : OE c (Lam d L N ⊕ Lam d L N)) :
    nrmD c ℓ₀ a b j (F * G) ≤ nrmD c ℓ₀ a b j F * nrmD c ℓ₀ a b j G := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  exact oT_mul_le (by positivity) (ellj_pos hL0 hℓ₀ _) (wj_sub hd c hℓ₀ _ _) F G

theorem nrmD_emb (j : ℕ) (x : EvR (Lam d L N ⊕ Lam d L N)) :
    nrmD c ℓ₀ a b j (emb x) =
      Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1)) (x : Grassmann.N (Lam d L N ⊕ Lam d L N)) := by
  rw [nrmD, coe_emb, oT_ofN]

theorem nrmD_emb_bulk_le (j : ℕ) (F : OE c (Lam d L N ⊕ Lam d L N)) :
    nrmD c ℓ₀ a b j (emb (bulk F)) ≤ nrmD c ℓ₀ a b j F := by
  rw [nrmD_emb, coe_bulk, nrmD, oT_def]
  exact le_self_add.trans (le_self_add.trans le_self_add)

theorem nrmD_zero (j : ℕ) : nrmD c ℓ₀ a b j (0 : OE c (Lam d L N ⊕ Lam d L N)) = 0 := by
  have := nrmD_emb (c := c) (ℓ₀ := ℓ₀) (a := a) (b := b) j 0
  rw [map_zero] at this
  rw [this, ZeroMemClass.coe_zero]
  exact tNorm_zero' (E := Dir d) (p := pPhi d) (h := (L : ℝ) ^ (j + 1)) (ℓ := ellj d L ℓ₀ (j + 1))

/-- `𝔼_{C_{j+1}}` is a contraction from the doubled norm to `‖·‖_{j+1}`. -/
theorem nrmj_ECO_le_nrmD (hℓ₀ : 0 < ℓ₀) {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℝ}
    (hC : GoodCov j ℓ₀ C) (F : OE c (Lam d L N ⊕ Lam d L N)) :
    nrmj c ℓ₀ a b (j + 1) (ECO C F) ≤ nrmD c ℓ₀ a b j F := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hh : (0 : ℝ) < (L : ℝ) ^ (j + 1) := by positivity
  exact oT_EC_le hh (ellj_pos hL0 hℓ₀ _) hC.psd hC.norm _

/-- `‖θ F‖_{T_{j+1}(ℓ_{j+1})} ≤ L^{2(d-2)} ‖F‖_j` (`e:Tphi-obs-ub`). -/
theorem nrmD_thetaO_le (hd : 3 ≤ d) (hL : (4 : ℝ) ≤ L) (hℓ₀ : 0 < ℓ₀) (j : ℕ)
    (F : OE c (Lam d L N)) :
    nrmD c ℓ₀ a b j (thetaO F) ≤
      ENNReal.ofReal ((L : ℝ) ^ (2 * ((d : ℝ) - 2))) * nrmj c ℓ₀ a b j F := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hh : (0 : ℝ) < (L : ℝ) ^ (j + 1) := by positivity
  exact (oT_theta_le hh (ellj_pos hL0 hℓ₀ _) _).trans (normj_succ_le hd hL c hℓ₀ _ j _).2

theorem nrmD_inclO_le (hℓ₀ : 0 < ℓ₀) (j : ℕ) (F : OE c (Lam d L N)) :
    nrmD c ℓ₀ a b j (inclO F) ≤ nrmj c ℓ₀ a b (j + 1) F := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hh : (0 : ℝ) < (L : ℝ) ^ (j + 1) := by positivity
  exact oT_incl_le hh (ellj_pos hL0 hℓ₀ _) _

/-! #### Real-valued bookkeeping -/

theorem dn_add {j : ℕ} {F G : OE c (Lam d L N ⊕ Lam d L N)} {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hF : nrmD c ℓ₀ a b j F ≤ ENNReal.ofReal s) (hG : nrmD c ℓ₀ a b j G ≤ ENNReal.ofReal t) :
    nrmD c ℓ₀ a b j (F + G) ≤ ENNReal.ofReal (s + t) :=
  (nrmD_add_le j F G).trans ((add_le_add hF hG).trans_eq (ENNReal.ofReal_add hs ht).symm)

theorem dn_sub {j : ℕ} {F G : OE c (Lam d L N ⊕ Lam d L N)} {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hF : nrmD c ℓ₀ a b j F ≤ ENNReal.ofReal s) (hG : nrmD c ℓ₀ a b j G ≤ ENNReal.ofReal t) :
    nrmD c ℓ₀ a b j (F - G) ≤ ENNReal.ofReal (s + t) :=
  (nrmD_sub_le j F G).trans ((add_le_add hF hG).trans_eq (ENNReal.ofReal_add hs ht).symm)

theorem dn_mul (hd : 2 ≤ d) (hℓ₀ : 0 < ℓ₀) {j : ℕ} {F G : OE c (Lam d L N ⊕ Lam d L N)}
    {s t : ℝ} (hs : 0 ≤ s) (hF : nrmD c ℓ₀ a b j F ≤ ENNReal.ofReal s)
    (hG : nrmD c ℓ₀ a b j G ≤ ENNReal.ofReal t) :
    nrmD c ℓ₀ a b j (F * G) ≤ ENNReal.ofReal (s * t) :=
  (nrmD_mul_le hd hℓ₀ j F G).trans ((mul_le_mul' hF hG).trans_eq (ENNReal.ofReal_mul hs).symm)

theorem nn_mul (hd : 2 ≤ d) (hℓ₀ : 0 < ℓ₀) {k : ℕ} {F G : OE c (Lam d L N)}
    {s t : ℝ} (hs : 0 ≤ s) (hF : nrmj c ℓ₀ a b k F ≤ ENNReal.ofReal s)
    (hG : nrmj c ℓ₀ a b k G ≤ ENNReal.ofReal t) :
    nrmj c ℓ₀ a b k (F * G) ≤ ENNReal.ofReal (s * t) :=
  (nrmj_mul_le hd hℓ₀ k F G).trans ((mul_le_mul' hF hG).trans_eq (ENNReal.ofReal_mul hs).symm)

theorem dn_theta (hd : 3 ≤ d) (hL : (4 : ℝ) ≤ L) (hℓ₀ : 0 < ℓ₀) {j : ℕ} {F : OE c (Lam d L N)}
    {s : ℝ} (hF : nrmj c ℓ₀ a b j F ≤ ENNReal.ofReal s) :
    nrmD c ℓ₀ a b j (thetaO F) ≤ ENNReal.ofReal ((L : ℝ) ^ (2 * ((d : ℝ) - 2)) * s) := by
  refine (nrmD_thetaO_le hd hL hℓ₀ j F).trans ?_
  rw [ENNReal.ofReal_mul (by positivity)]
  gcongr

theorem dn_incl (hℓ₀ : 0 < ℓ₀) {j : ℕ} {F : OE c (Lam d L N)} {s : ℝ}
    (hF : nrmj c ℓ₀ a b (j + 1) F ≤ ENNReal.ofReal s) :
    nrmD c ℓ₀ a b j (inclO F) ≤ ENNReal.ofReal s :=
  (nrmD_inclO_le hℓ₀ j F).trans hF

/-- **Telescoping** (`e:norm-obs-nonmon`): if `‖δ_i‖ ≤ 1` and `‖π_obs δ_i‖ ≤ σ`, then
`‖π_obs ∏_{i ∈ s} δ_i‖ ≤ |s| σ`. -/
theorem nrmD_πobs_prod_le (hd : 2 ≤ d) (hℓ₀ : 0 < ℓ₀) (j : ℕ) {ι : Type*} (s : Finset ι)
    (δ : ι → OE c (Lam d L N ⊕ Lam d L N)) {σ : ℝ} (hσ : 0 ≤ σ)
    (h1 : ∀ i ∈ s, nrmD c ℓ₀ a b j (δ i) ≤ 1)
    (h2 : ∀ i ∈ s, nrmD c ℓ₀ a b j (πobs (δ i)) ≤ ENNReal.ofReal σ) :
    nrmD c ℓ₀ a b j (πobs (∏ i ∈ s, δ i)) ≤ ENNReal.ofReal (s.card * σ) := by
  classical
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hh : (0 : ℝ) < (L : ℝ) ^ (j + 1) := by positivity
  induction s using Finset.induction_on with
  | empty =>
    have : πobs (1 : OE c (Lam d L N ⊕ Lam d L N)) = 0 := by
      rw [← map_one (emb (c := c) (Λ := Lam d L N ⊕ Lam d L N)), πobs_emb]
    rw [prod_empty, this, nrmD_zero]
    exact zero_le
  | insert i s hi ih =>
    have ih' := ih (fun k hk => h1 k (mem_insert_of_mem hk)) (fun k hk => h2 k (mem_insert_of_mem hk))
    have hP : nrmD c ℓ₀ a b j (∏ k ∈ s, δ k) ≤ 1 := by
      refine (oT_prod_le hh (ellj_pos hL0 hℓ₀ _) (wj_sub hd c hℓ₀ _ _) s δ).trans ?_
      exact prod_le_one' fun k hk => h1 k (mem_insert_of_mem hk)
    rw [prod_insert hi, πobs_mul', card_insert_of_notMem hi]
    refine (nrmD_add_le j _ _).trans ?_
    have e1 : nrmD c ℓ₀ a b j (δ i * πobs (∏ k ∈ s, δ k)) ≤ ENNReal.ofReal (s.card * σ) :=
      (nrmD_mul_le hd hℓ₀ j _ _).trans ((mul_le_mul' (h1 i (mem_insert_self i s)) ih').trans
        (by rw [one_mul]))
    have e2 : nrmD c ℓ₀ a b j (πobs (δ i) * emb (bulk (∏ k ∈ s, δ k))) ≤ ENNReal.ofReal σ :=
      (nrmD_mul_le hd hℓ₀ j _ _).trans ((mul_le_mul' (h2 i (mem_insert_self i s))
        ((nrmD_emb_bulk_le j _).trans hP)).trans (by rw [mul_one]))
    refine (add_le_add e1 e2).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_add (by positivity) hσ]
    congr 1; push_cast; ring

end D

/-! ### Real exponential bounds -/

theorem exp_sub_one_le_two_mul {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : Real.exp y - 1 ≤ 2 * y := by
  have := Real.abs_exp_sub_one_le (x := y) (by rw [abs_of_nonneg h0]; exact h1)
  rw [abs_of_nonneg h0, abs_of_nonneg (by linarith [Real.add_one_le_exp y])] at this
  exact this

/-! ### The block quantities -/

section BlockQ

variable {c : Case}

/-- `I_0(B) = e^{-(V^∅(B) + V^obs(B))}` in the form of `πobs_oexp_expansion_le`. -/
theorem I0_eq (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (Vb : Vcoup) (Vo : Coup c)
    (K : Finset (Lam d L N) → OE c (Lam d L N)) (a b : Lam d L N) (p : Fin d → ℕ) :
    (obsI j C Vb Vo K a b).I0 p = algebraMap ℂ (OE c (Lam d L N)) (Complex.exp 0) *
      oexp (-(emb (VE Vb (blockSet j p)) + Vobs j Vo a b p)) := by
  rw [Complex.exp_zero, map_one, one_mul]; rfl

/-- `e^{-(u+V)_{j+1}(B)}` in the form of `πobs_oexp_expansion_le`. -/
theorem It_eq (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (Vb : Vcoup) (Vo : Coup c)
    (K : Finset (Lam d L N) → OE c (Lam d L N)) (a b : Lam d L N) (p : Fin d → ℕ) :
    It (obsI j C Vb Vo K a b) p = algebraMap ℂ (OE c (Lam d L N))
        (Complex.exp (-((uVb j C Vb K).1 * (blockSet (L := L) (N := N) j p).card))) *
      oexp (-(emb (VE (uVb j C Vb K).2 (blockSet j p)) + vt j C Vo K a b p)) := by
  have hx : ε (((-VE (uVb j C Vb K).2 (blockSet (L := L) (N := N) j p) : EvR (Lam d L N))) :
      Alg d L N) = 0 := by
    rw [NegMemClass.coe_neg, map_neg, ε_VE, neg_zero]
  rw [It_fac, map_mul, AlgHom.commutes, mul_assoc, neg_add,
    oexp_add (isNilpotent_of_ε (F := -emb _) ?_)
      (isNilpotent_of_obs (by rw [map_neg, bulk_splitO, neg_zero])), ← map_neg, oexp_emb hx]
  rw [NegMemClass.coe_neg, SA.neg_e, coe_emb, map_neg, neg_eq_zero]
  exact ε_VE _ _

theorem Inext_eq (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (Vb : Vcoup)
    (K : Act d L N) (p : Fin d → ℕ) :
    ((Inext j C Vb K p - 1 : EvR (Lam d L N)) : Alg d L N) =
      Complex.exp (-((uVnext j C Vb K).1 * (blockSet (L := L) (N := N) j p).card)) •
          ((gexp (-(VE (uVnext j C Vb K).2 (blockSet (L := L) (N := N) j p) : EvR (Lam d L N)))
            - 1 : EvR (Lam d L N)) : Alg d L N) +
        (Complex.exp (-((uVnext j C Vb K).1 * (blockSet (L := L) (N := N) j p).card)) - 1) •
          (1 : Alg d L N) := by
  rw [Inext]
  simp only [AddSubgroupClass.coe_sub, SetLike.val_smul, OneMemClass.coe_one, smul_sub, sub_smul,
    one_smul]
  abel

end BlockQ

set_option maxHeartbeats 4000000 in
/-- **The block bounds.**  With `t = ‖V^∅‖_j + ‖K^∅‖_j`, `s = ‖V^obs‖_j + ‖K^obs‖_j`,
`K₂ = L^{2(d-2)}`, for `B ∈ 𝓑_j` and `X ∈ 𝒫_j`:
`‖V^obs(B)‖_j ≤ v^obs`, `‖Q^obs(B)‖_j ≤ M ‖K^obs‖`, `‖(u+V)^obs_{j+1}(X)‖, ‖u^obs_{j+1}(X)‖ ≤ M K₂ s`,
`‖ρ(B)‖ ≤ M K₂ s t` (`e:expVobs2-expansion`), `‖π_∅ δI(B)‖ ≤ M t` (`e:deltaIbd`),
`‖e^{-(u+V)^∅_{j+1}(B)} - 1‖ ≤ M t`. -/
theorem block_bounds (hd : 3 ≤ d) : ∃ (M εb : ℝ) (L₀ : ℕ), 1 ≤ M ∧ 0 < εb ∧ εb ≤ 1 ∧
    2 ^ (d + 3) + 8 * d + 1 ≤ L₀ ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∀ (N j : ℕ), j < N → ∀ (ℓ₀ : ℝ), 0 < ℓ₀ →
    ∀ (c : Case) (P : Prop) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (Vb : Vcoup) (Vo : Coup c)
      (K : Finset (Lam d L N) → OE c (Lam d L N)) (a b : Lam d L N) (A : ℝ), 1 ≤ A →
      StepObsHyp c P j ℓ₀ C Vb Vo K a b →
      ∀ vb kb vo ko : ℝ, 0 ≤ vb → 0 ≤ kb → 0 ≤ vo → 0 ≤ ko →
      Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) Vb = ENNReal.ofReal vb →
      Knorm j (ellj d L ℓ₀ j) A (bulkK K) = ENNReal.ofReal kb →
      VnormObs c ℓ₀ a b j Vo = ENNReal.ofReal vo → KnormObs c ℓ₀ a b j A K = ENNReal.ofReal ko →
      vb + kb ≤ εb → (L : ℝ) ^ (2 * ((d : ℝ) - 2)) * (vo + ko) ≤ εb →
      (∀ X : Finset (Lam d L N), IsPolymer j X →
        nrmj c ℓ₀ a b (j + 1) (splitO c (nextObs C j Vo K a b) a b X) ≤
          ENNReal.ofReal (M * (L : ℝ) ^ (2 * ((d : ℝ) - 2)) * (vo + ko)) ∧
        nrmj c ℓ₀ a b (j + 1) (uObsX j C Vo K a b X) ≤
          ENNReal.ofReal (M * (L : ℝ) ^ (2 * ((d : ℝ) - 2)) * (vo + ko))) ∧
      ∀ p ∈ blockIdx (L := L) (N := N) j,
        nrmj c ℓ₀ a b j (Vobs j Vo a b p) ≤ ENNReal.ofReal vo ∧
        nrmj c ℓ₀ a b j (QobsO a b j K p) ≤ ENNReal.ofReal (M * ko) ∧
        nrmD c ℓ₀ a b j (rhoO j C Vb Vo K a b p) ≤
          ENNReal.ofReal (M * (L : ℝ) ^ (2 * ((d : ℝ) - 2)) * (vo + ko) * (vb + kb)) ∧
        nrmD c ℓ₀ a b j (emb (bulk (dIo j C Vb Vo K a b p))) ≤ ENNReal.ofReal (M * (vb + kb)) ∧
        Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1))
            ((Inext j C Vb (bulkK K) p - 1 : EvR (Lam d L N)) : Alg d L N) ≤
          ENNReal.ofReal (M * (vb + kb)) := by
  obtain ⟨CU, LU, hCU, hLU, hbr⟩ := block_real hd
  obtain ⟨CV, LV, hCV, hLV, hVn⟩ := Vobs_next_bounds hd
  obtain ⟨Cq, hCq, hQb⟩ := Qobs_bounds d
  obtain ⟨C₁, εd, Ld, hC₁, hεd, hLd, hdI⟩ := dI_bounds hd
  set M : ℝ := CV + Cq + C₁ + 6 * (1 + CU) + (4 + 12 * (1 + CU) * CV) + 1 with hM
  set εb : ℝ := min εd (1 / (3 * (1 + CU) * CV)) with hεb
  have hεb0 : 0 < εb := lt_min hεd (by positivity)
  have hεb1 : εb ≤ 1 / (3 * (1 + CU) * CV) := min_le_right _ _
  have hCV1 : (1 : ℝ) ≤ CV := hCV
  have h3 : (1 : ℝ) ≤ 3 * (1 + CU) * CV := by nlinarith
  have hεb2 : εb ≤ 1 := hεb1.trans (by rw [div_le_one (by positivity)]; exact h3)
  refine ⟨M, εb, max (max LU LV) Ld, by rw [hM]; nlinarith, hεb0, hεb2,
    hLU.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro L _ hL N j hj ℓ₀ hℓ₀ c P C Vb Vo K a b A hA h vb kb vo ko hvb0 hkb0 hvo0 hko0 hvb hkb hvo hko
    ht hs
  have hLU' : LU ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hLV' : LV ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hLd' : Ld ≤ L := (le_max_right _ _).trans hL
  have hL4 : (4 : ℝ) ≤ L := four_le_of_L₀ (hLU.trans hLU')
  have hL0 : (0 : ℝ) < L := by linarith
  set K₂ : ℝ := (L : ℝ) ^ (2 * ((d : ℝ) - 2)) with hK₂
  have hK1 : 1 ≤ K₂ := one_le_K₂ hd
  have hK0 : 0 ≤ K₂ := by linarith
  set t := vb + kb with ht_def
  set s := vo + ko with hs_def
  have ht0 : 0 ≤ t := by positivity
  have hs0 : 0 ≤ s := by positivity
  have hCUk : 0 ≤ vb + CU * kb := by have := mul_nonneg hCU hkb0; linarith
  have hsK : K₂ * s ≤ 1 := hs.trans hεb2
  have hsm : ENNReal.ofReal K₂ * (VnormObs c ℓ₀ a b j Vo + KnormObs c ℓ₀ a b j A K) ≤ 1 := by
    rw [hvo, hko, ← ENNReal.ofReal_add hvo0 hko0, ← ENNReal.ofReal_mul hK0, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hsK
  have hso : ENNReal.ofReal (CV * K₂) * (VnormObs c ℓ₀ a b j Vo + KnormObs c ℓ₀ a b j A K) =
      ENNReal.ofReal (CV * K₂ * s) := by
    rw [hvo, hko, ← ENNReal.ofReal_add hvo0 hko0, ← ENNReal.ofReal_mul (by positivity)]
  obtain ⟨-, -, -, -, h5⟩ := hVn L hLV' N j hj ℓ₀ hℓ₀ c P C Vb Vo K a b A hA h hsm
  have hMV : CV ≤ M := by rw [hM]; nlinarith
  have hMq : Cq ≤ M := by rw [hM]; nlinarith
  have hM1 : C₁ ≤ M := by rw [hM]; nlinarith
  have hbulk : Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) Vb +
      Knorm j (ellj d L ℓ₀ j) A (bulkK K) ≤ ENNReal.ofReal εb := by
    rw [hvb, hkb, ← ENNReal.ofReal_add hvb0 hkb0]; exact ENNReal.ofReal_le_ofReal ht
  obtain ⟨-, -, -, -, -, hblk⟩ :=
    hbr L hLU' N j hj ℓ₀ hℓ₀ C h.cov Vb (bulkK K) A hA h.bulk εb hεb0.le hbulk
  have hvbr : (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) Vb).toReal = vb := by
    rw [hvb, ENNReal.toReal_ofReal hvb0]
  have hkbr : (Knorm j (ellj d L ℓ₀ j) A (bulkK K)).toReal = kb := by
    rw [hkb, ENNReal.toReal_ofReal hkb0]
  rw [hvbr, hkbr] at hblk
  obtain ⟨hQp, -, -⟩ := hQb L (by omega) N j hj ℓ₀ hℓ₀ c P K a b A hA h.loc.hK
  refine ⟨fun X hX => ⟨?_, ?_⟩, fun p hp => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · refine ((h5 X hX).1.trans (by rw [hso])).trans (ENNReal.ofReal_le_ofReal ?_)
    gcongr
  · refine ((h5 X hX).2.1.trans (by rw [hso])).trans (ENNReal.ofReal_le_ofReal ?_)
    gcongr
  · rw [← hvo]; exact nrmj_Vobs_le Vo hp
  · refine (hQp p hp).trans ?_
    rw [hko, ← ENNReal.ofReal_mul hCq]
    exact ENNReal.ofReal_le_ofReal (by gcongr)
  · -- `ρ(B)`
    obtain ⟨hVB, hu, hV'⟩ := hblk p hp
    have hh : (0 : ℝ) < (L : ℝ) ^ j := by positivity
    have hh1 : (0 : ℝ) < (L : ℝ) ^ (j + 1) := by positivity
    have hℓ := ellj_pos (d := d) hL0 hℓ₀ j
    have hℓ1 := ellj_pos (d := d) hL0 hℓ₀ (j + 1)
    have hw := wj_sub (d := d) (L := L) (by omega) c hℓ₀ (coal L a b : ℕ∞) j
    have hw1 := wj_sub (d := d) (L := L) (by omega) c hℓ₀ (coal L a b : ℕ∞) (j + 1)
    have hvn : nrmj c ℓ₀ a b j (Vobs j Vo a b p) ≤ ENNReal.ofReal vo := by
      rw [← hvo]; exact nrmj_Vobs_le Vo hp
    set σ := CV * K₂ * s with hσ
    have hσ0 : 0 ≤ σ := by positivity
    have hσ1 : σ ≤ 1 := by
      have : K₂ * s ≤ 1 / (3 * (1 + CU) * CV) := hs.trans hεb1
      rw [le_div_iff₀ (by positivity)] at this
      calc σ = CV * (K₂ * s) := by ring
        _ ≤ 3 * (1 + CU) * CV * (K₂ * s) := by gcongr; nlinarith
        _ ≤ 1 := by linarith
    have hvtn : nrmj c ℓ₀ a b (j + 1) (vt j C Vo K a b p) ≤ ENNReal.ofReal σ :=
      (h5 _ (isPolymer_blockSet j p)).1.trans (by rw [hso])
    have hvo1 : vo ≤ 1 := by nlinarith
    have hvb1 : vb ≤ 1 := by linarith
    -- the expansion for `I_0`
    have e1 := πobs_oexp_expansion_le (E := Dir d) (p := pPhi d) (h := (L : ℝ) ^ j)
      (ℓ := ellj d L ℓ₀ j) (w := wj d L c ℓ₀ (coal L a b : ℕ∞) j) hh hℓ hw 0
      (x := VE Vb (blockSet j p)) (ε_VE _ _) (G := Vobs j Vo a b p) (bulk_splitO _ _ _ _ _)
      (r := vb) (s := vo) hvb0 hvo0 (by rw [coe_VE]; exact hVB) hvn
    rw [← I0_eq j C Vb Vo K a b p, norm_zero, zero_add] at e1
    -- the expansion for `e^{-(u+V)_{j+1}(B)}`
    set u := (uVb j C Vb K).1 * (blockSet (L := L) (N := N) j p).card with hu_def
    have hu' : ‖-u‖ ≤ vb + CU * kb := by rw [norm_neg]; exact hu
    have e2 := πobs_oexp_expansion_le (E := Dir d) (p := pPhi d) (h := (L : ℝ) ^ (j + 1))
      (ℓ := ellj d L ℓ₀ (j + 1)) (w := wj d L c ℓ₀ (coal L a b : ℕ∞) (j + 1)) hh1 hℓ1 hw1 (-u)
      (x := VE (uVb j C Vb K).2 (blockSet j p)) (ε_VE _ _) (G := vt j C Vo K a b p)
      (bulk_splitO _ _ _ _ _) (r := 2 * (vb + CU * kb)) (s := σ) (by linarith) hσ0
      (by rw [coe_VE]; exact hV') hvtn
    rw [← It_eq j C Vb Vo K a b p] at e2
    have hA1 : 0 ≤ Real.exp vb - 1 := by linarith [Real.add_one_le_exp vb]
    have hA2 : 0 ≤ Real.exp (‖-u‖ + 2 * (vb + CU * kb)) - 1 := by
      have := norm_nonneg (-u)
      linarith [Real.add_one_le_exp (‖-u‖ + 2 * (vb + CU * kb))]
    have hρ := dn_sub (c := c) (ℓ₀ := ℓ₀) (a := a) (b := b) (j := j)
      (mul_nonneg hK0 (mul_nonneg hA1 (by positivity))) (mul_nonneg hA2 (by positivity))
      (dn_theta hd hL4 hℓ₀ e1) (dn_incl hℓ₀ e2)
    refine hρ.trans (ENNReal.ofReal_le_ofReal ?_)
    -- real bookkeeping
    have hx1 : Real.exp vb - 1 ≤ 2 * vb := exp_sub_one_le_two_mul hvb0 hvb1
    have hy0 : 0 ≤ ‖-u‖ + 2 * (vb + CU * kb) := by have := norm_nonneg (-u); linarith
    have hy1 : ‖-u‖ + 2 * (vb + CU * kb) ≤ 3 * (1 + CU) * t := by
      have : vb + CU * kb ≤ (1 + CU) * t := by rw [ht_def]; nlinarith
      nlinarith
    have hy2 : 3 * (1 + CU) * t ≤ 1 := by
      have : t ≤ 1 / (3 * (1 + CU) * CV) := ht.trans hεb1
      rw [le_div_iff₀ (by positivity)] at this
      nlinarith
    have hx2 : Real.exp (‖-u‖ + 2 * (vb + CU * kb)) - 1 ≤ 2 * (3 * (1 + CU) * t) :=
      (exp_sub_one_le_two_mul hy0 (hy1.trans hy2)).trans (by linarith)
    have hq1 : vo + vo ^ 2 / 2 ≤ 2 * s := by nlinarith
    have hq2 : σ + σ ^ 2 / 2 ≤ 2 * σ := by nlinarith
    calc K₂ * ((Real.exp vb - 1) * (vo + vo ^ 2 / 2)) +
          (Real.exp (‖-u‖ + 2 * (vb + CU * kb)) - 1) * (σ + σ ^ 2 / 2)
        ≤ K₂ * ((2 * t) * (2 * s)) + (2 * (3 * (1 + CU) * t)) * (2 * σ) := by
          gcongr
          · linarith
    _ = (4 + 12 * (1 + CU) * CV) * K₂ * s * t := by rw [hσ]; ring
    _ ≤ M * K₂ * s * t := by gcongr; rw [hM]; nlinarith
  · -- `π_∅ δI(B)`
    rw [bulk_dIo, nrmD_emb]
    refine ((hdI L (hLd'.trans le_rfl) N j hj ℓ₀ hℓ₀ C h.cov Vb (bulkK K) A hA h.bulk
      (hbulk.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _))) p hp).1).trans ?_
    rw [hvb, hkb, ← ENNReal.ofReal_add hvb0 hkb0, ← ENNReal.ofReal_mul hC₁]
    exact ENNReal.ofReal_le_ofReal (by gcongr)
  · -- `e^{-(u+V)^∅_{j+1}(B)} - 1`
    obtain ⟨-, hu, hV'⟩ := hblk p hp
    have hh1 : (0 : ℝ) < (L : ℝ) ^ (j + 1) := by positivity
    have hℓ1 := ellj_pos (d := d) hL0 hℓ₀ (j + 1)
    set z := -((uVnext j C Vb (bulkK K)).1 * (blockSet (L := L) (N := N) j p).card) with hz
    have hz' : ‖z‖ ≤ vb + CU * kb := by rw [hz, norm_neg]; exact hu
    have hx' : ε (((-VE (uVnext j C Vb (bulkK K)).2 (blockSet (L := L) (N := N) j p) :
        EvR (Lam d L N))) : Alg d L N) = 0 := by
      rw [NegMemClass.coe_neg, map_neg, ε_VE, neg_zero]
    have hxr : tNorm (Dir d) (pPhi d) ((L : ℝ) ^ (j + 1)) (ellj d L ℓ₀ (j + 1))
        (((-VE (uVnext j C Vb (bulkK K)).2 (blockSet (L := L) (N := N) j p) :
          EvR (Lam d L N))) : Alg d L N) ≤ ENNReal.ofReal (2 * (vb + CU * kb)) := by
      rw [NegMemClass.coe_neg, Loc.tNorm_neg, coe_VE]; exact hV'
    rw [Inext_eq]
    have h1 := tn_smul (Complex.exp z) (tNorm_gexp_sub_one_le hh1 hℓ1 hx' (by linarith) hxr)
    have h2 := tn_smul (Complex.exp z - 1) (tn_one (E := Dir d) (p := pPhi d)
      (X := Lam d L N) hh1 hℓ1)
    have hr1 : 0 ≤ Real.exp (2 * (vb + CU * kb)) - 1 := by
      linarith [Real.add_one_le_exp (2 * (vb + CU * kb))]
    have hnz := norm_nonneg z
    refine (tn_add (mul_nonneg (norm_nonneg _) hr1) (by positivity) h1 h2).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have hz1 : ‖Complex.exp z‖ ≤ Real.exp ‖z‖ := Complex.norm_exp_le_exp_norm z
    have hz2 : ‖Complex.exp z - 1‖ ≤ Real.exp ‖z‖ - 1 := by
      simpa using Complex.norm_exp_sub_sum_le_exp_norm_sub_sum z 1
    have hy1 : ‖z‖ + 2 * (vb + CU * kb) ≤ 3 * (1 + CU) * t := by
      have : vb + CU * kb ≤ (1 + CU) * t := by rw [ht_def]; nlinarith
      nlinarith
    have hy2 : 3 * (1 + CU) * t ≤ 1 := by
      have : t ≤ 1 / (3 * (1 + CU) * CV) := ht.trans hεb1
      rw [le_div_iff₀ (by positivity)] at this
      nlinarith
    have hmono : Real.exp (‖z‖ + 2 * (vb + CU * kb)) ≤ Real.exp (3 * (1 + CU) * t) :=
      Real.exp_le_exp.2 hy1
    have hx3 := exp_sub_one_le_two_mul (by positivity) hy2
    have hr2 : 0 ≤ Real.exp ‖z‖ - 1 := by linarith [Real.add_one_le_exp ‖z‖]
    calc ‖Complex.exp z‖ * (Real.exp (2 * (vb + CU * kb)) - 1) + ‖Complex.exp z - 1‖ * 1
        ≤ Real.exp ‖z‖ * (Real.exp (2 * (vb + CU * kb)) - 1) + (Real.exp ‖z‖ - 1) := by
          rw [mul_one]; gcongr
      _ = Real.exp (‖z‖ + 2 * (vb + CU * kb)) - 1 := by rw [Real.exp_add]; ring
      _ ≤ Real.exp (3 * (1 + CU) * t) - 1 := by linarith
      _ ≤ 2 * (3 * (1 + CU) * t) := hx3
      _ ≤ M * t := by
          have : 6 * (1 + CU) ≤ M := by rw [hM]; nlinarith
          nlinarith

/-! ### `U(1)` charges from `scal` -/

theorem hasCharge_of_scal {Λ : Type*} [DecidableEq Λ] (q : ℤ) (F : Grassmann.N Λ)
    (h : Step.scal Λ 2 F = ((2 : ℂ) ^ (-q)) • F) : HasCharge q F := by
  intro n z hz
  have h1 := congrArg (fun G => coeff G z) h
  simp only [coeff_scal, prod_scal_factor, coeff_smul] at h1
  by_contra hc
  have h2 : (2 : ℂ) ^ (univ.filter fun i => (z i).2 = 1).card *
      2⁻¹ ^ (univ.filter fun i => (z i).2 = -1).card = 2 ^ (-q) := mul_right_cancel₀ hc h1
  have h3 : (2 : ℂ) ^ (((univ.filter fun i => (z i).2 = 1).card : ℤ) -
      ((univ.filter fun i => (z i).2 = -1).card : ℤ)) = 2 ^ (-q) := by
    rw [zpow_sub₀ two_ne_zero, zpow_natCast, zpow_natCast, div_eq_mul_inv, ← inv_pow]
    exact h2
  have h4 := congrArg (fun x : ℂ => ‖x‖) h3
  simp only [norm_zpow, Complex.norm_ofNat] at h4
  have h5 := zpow_right_injective₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) h4
  apply hz
  unfold charge
  omega

theorem charges_of_isSymS {c : Case} {Λ : Type*} [DecidableEq Λ] {F : SA c Λ}
    (h : IsSymS F) : HasCharge (chargeA c.toObs) F.a ∧ HasCharge (chargeB c.toObs) F.b ∧
      HasCharge 0 F.ab := by
  cases c
  · rw [isSymS_iff_one] at h
    obtain ⟨-, ha, hb, hab⟩ := h
    refine ⟨hasCharge_of_scal _ _ ?_, hasCharge_of_scal _ _ ?_, hasCharge_of_scal _ _ ?_⟩
    · rw [ha]; simp [chargeA, Case.toObs]
    · rw [hb]; simp [chargeB, Case.toObs]
    · rw [hab]; simp
  · rw [isSymS_iff_two] at h
    obtain ⟨-, ha, hb, hab⟩ := h
    refine ⟨hasCharge_of_scal _ _ ?_, hasCharge_of_scal _ _ ?_, hasCharge_of_scal _ _ ?_⟩
    · rw [ha]; simp [chargeA, Case.toObs]
    · rw [hb]; simp [chargeB, Case.toObs]
    · rw [hab]; simp

/-! ### The weighted norm as `obsNorm` -/

theorem oTj_eq_obsNorm {c : Case} {ℓ₀ : ℝ} (a b : Lam d L N) (k : ℕ) (ℓ : ℝ)
    (G : SA c (Lam d L N)) (he : G.e = 0) :
    oTj d L (wj d L c ℓ₀ (coal L a b : ℕ∞) k) k ℓ G =
      obsNorm c.toObs ℓ₀ (coal L a b) k ℓ G.a G.b G.ab := by
  cases c <;> simp [oTj, oNorm, wj, obsWt, ella, ellab, obsNorm, wA, wAB, jwedge_coe, Case.p,
    Case.toObs, he, Tj_zero]

/-! ### `lem:smallset-Kobs`: one summand -/

set_option maxHeartbeats 4000000 in
/-- **Lemma `lem:smallset-Kobs`** (one summand): for `X ∈ 𝒮_j`,
`‖𝔼 θ π_obs (1 - Loc_X) K(X)‖_{T_{j+1}(ℓ_{j+1})} ≤ C̄ L^{-d_+} ‖K^obs‖_j` (resp. `≤ L^{2(d-2)} ‖K^obs‖_j`
for `j + 1 = N`), and it vanishes unless `a ∈ X` or `b ∈ X`. -/
theorem Lt_bound (hd : 3 ≤ d) : ∃ (Cl : ℝ) (L₀ : ℕ), 0 ≤ Cl ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∀ (N j : ℕ), j < N → ∀ (ℓ₀ : ℝ), 0 < ℓ₀ →
    ∀ (c : Case) (P : Prop) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (Vb : Vcoup) (Vo : Coup c)
      (K : Finset (Lam d L N) → OE c (Lam d L N)) (a b : Lam d L N) (A : ℝ), 1 ≤ A →
      StepObsHyp c P j ℓ₀ C Vb Vo K a b → ∀ X : Finset (Lam d L N), IsSmall j X →
        nrmj c ℓ₀ a b (j + 1) (ECO C (thetaO (πobs (K X - LocCO j a b X (K X))))) ≤
          ENNReal.ofReal (Cl * (if j + 1 < N then (L : ℝ) ^ (-dplus d)
            else (L : ℝ) ^ (2 * ((d : ℝ) - 2)))) * KnormObs c ℓ₀ a b j A K ∧
        (a ∉ X → b ∉ X → πobs (K X - LocCO j a b X (K X)) = 0) := by
  obtain ⟨Cbar, L₁, hloc⟩ := locObs_contract d hd
  refine ⟨max Cbar 0 + 1, max L₁ (2 ^ (d + 3) + 8 * d + 1), by positivity, ?_⟩
  intro L _ hL N j hj ℓ₀ hℓ₀ c P C Vb Vo K a b A hA h X hX
  have hL₁ : L₁ ≤ L := (le_max_left _ _).trans hL
  have hL4 : (4 : ℝ) ≤ L := four_le_of_L₀ ((le_max_right _ _).trans hL)
  have hL0 : (0 : ℝ) < L := by linarith
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hXc : IsConn j X := ⟨hX.1, hX.2.1⟩
  have hko : nrmj c ℓ₀ a b j (πobs (K X)) ≤ KnormObs c ℓ₀ a b j A K := nrmj_le_KnormObs hA hXc
  obtain ⟨hpa, hpb, hpab⟩ := h.pt X hXc
  obtain ⟨⟨-, hma, hmb, hmab, -, -⟩, hsym⟩ := Algebra.mem_inf.1 (h.loc.hK X hXc)
  obtain ⟨hca, hcb, hcab⟩ := charges_of_isSymS (mem_symSub.1 hsym)
  have hCm : Cbar ≤ max Cbar 0 + 1 := by linarith [le_max_left Cbar 0]
  have hCm0 : 0 ≤ max Cbar 0 + 1 := by positivity
  refine ⟨?_, fun ha hb => ?_⟩
  · by_cases hjN : j + 1 < N
    · rw [LocCO, if_pos hjN, if_pos hjN]
      have hh : (0 : ℝ) < (L : ℝ) ^ (j + 1) := by positivity
      refine (oT_EC_theta_le hh (ellj_pos hL0 hℓ₀ _) h.cov.psd h.cov.norm _).trans ?_
      have hG : ((πobs (K X - LocO a b X X (K X)) : OE c (Lam d L N)) : SA c (Lam d L N)).e = 0 := by
        simp [piobs_apply]
      refine (le_of_eq (oTj_eq_obsNorm (c := c) (ℓ₀ := ℓ₀) a b (j + 1)
        (2 * ellj d L ℓ₀ (j + 1)) _ hG)).trans ?_
      have hko' : obsNorm c.toObs ℓ₀ (coal L a b) j (ellj d L ℓ₀ j) (K X : SA c (Lam d L N)).a
          (K X : SA c (Lam d L N)).b (K X : SA c (Lam d L N)).ab ≤ KnormObs c ℓ₀ a b j A K := by
        have e := oTj_eq_obsNorm (c := c) (ℓ₀ := ℓ₀) a b j (ellj d L ℓ₀ j)
          ((πobs (K X) : OE c (Lam d L N)) : SA c (Lam d L N)) (by simp [piobs_apply])
        simp only [coe_πobs, piobs_apply] at e
        rw [← e]; simpa [nrmj, normj, piobs_apply] using hko
      have hcomp := hloc L hL₁ N j hj ℓ₀ hℓ₀ (coal L a b) X hX c.toObs a b _ hma _ hmb _ hmab
        hca hcb hcab
        (by by_cases ha : a ∈ X; exacts [Or.inl ha, Or.inr (hpa ha)])
        (by by_cases hb : b ∈ X; exacts [Or.inl hb, Or.inr (hpb hb)])
        (by
          by_cases hab : a ∈ X ∨ b ∈ X
          · by_cases hjab : coal L a b ≤ j
            · exact Or.inl ⟨hab, hjab⟩
            · exact Or.inr (h.abSmall (by omega) X hX)
          · push_neg at hab; exact Or.inr (hpab hab.1 hab.2))
      simp only [coe_πobs, piobs_apply, AddSubgroupClass.coe_sub, SA.sub_a, SA.sub_b, SA.sub_ab,
        coe_LocO, LocS_a, LocS_b, LocS_ab]
      refine hcomp.trans ?_
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) hko'
      have hLd : (L : ℝ)⁻¹ ≤ (L : ℝ) ^ (-dplus d) := by
        rw [← Real.rpow_neg_one]
        exact Real.rpow_le_rpow_of_exponent_le hL1 (by
          have : dplus d ≤ 1 := min_le_right _ _
          linarith)
      rw [div_eq_mul_inv]
      have h0 : 0 ≤ (L : ℝ)⁻¹ := by positivity
      calc Cbar * (L : ℝ)⁻¹ ≤ (max Cbar 0 + 1) * (L : ℝ)⁻¹ := by gcongr
        _ ≤ (max Cbar 0 + 1) * (L : ℝ) ^ (-dplus d) := by gcongr
    · rw [LocCO, if_neg hjN, if_neg hjN, sub_zero]
      refine (nrmj_ECO_le hd hL4 hℓ₀ h.cov _).trans ?_
      rw [ENNReal.ofReal_mul hCm0]
      refine le_trans ?_ (mul_le_mul' le_rfl hko)
      refine mul_le_mul' ?_ le_rfl
      refine le_mul_of_one_le_left zero_le ?_
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by linarith [le_max_right Cbar 0])
  · have e1 : πobs (K X) = 0 := by
      refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_)
      · simp [piobs_apply]
      · simp [piobs_apply, hpa ha]
      · simp [piobs_apply, hpb hb]
      · simp [piobs_apply, hpab ha hb]
    have e2 : πobs (LocCO j a b X (K X)) = 0 := by
      unfold LocCO
      split_ifs
      · refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_)
        · simp [piobs_apply]
        · simp [piobs_apply, hpa ha, locA_zero]
        · simp [piobs_apply, hpb hb, locB_zero]
        · simp [piobs_apply, hpab ha hb, locAB, locEven_zero]
      · exact map_zero _
    rw [map_sub, e1, e2, sub_zero]

/-! ### Remainder bounds -/

section Rem

variable {c : Case} {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℝ} {Vb : Vcoup} {Vo : Coup c}
  {K : Finset (Lam d L N) → OE c (Lam d L N)} {a b : Lam d L N} {ℓ₀ : ℝ}

theorem nrmj_half_le' {k : ℕ} (F : OE c (Lam d L N)) :
    nrmj c ℓ₀ a b k ((1 / 2 : ℂ) • F) ≤ nrmj c ℓ₀ a b k F := nrmj_half_smul k F

theorem nrmj_sq_le (hd : 2 ≤ d) (hℓ₀ : 0 < ℓ₀) {k : ℕ} {F : OE c (Lam d L N)} {s : ℝ}
    (hs : 0 ≤ s) (hF : nrmj c ℓ₀ a b k F ≤ ENNReal.ofReal s) :
    nrmj c ℓ₀ a b k (F ^ 2) ≤ ENNReal.ofReal (s * s) := by
  rw [sq]; exact nn_mul hd hℓ₀ hs hF hF

variable (hd : 3 ≤ d) (hL : (4 : ℝ) ≤ L) (hℓ₀ : 0 < ℓ₀) (hC : GoodCov j ℓ₀ C)
include hd hL hℓ₀

/-- `‖π_obs δI(B)‖ ≤ K₂ (v + v²) + (σ + σ²) + r` from `πobs_dIo`. -/
theorem o_bound {p : Fin d → ℕ} {vo σ r : ℝ} (hvo : 0 ≤ vo) (hσ : 0 ≤ σ) (hr : 0 ≤ r)
    (hv : nrmj c ℓ₀ a b j (Vobs j Vo a b p) ≤ ENNReal.ofReal vo)
    (hvt : nrmj c ℓ₀ a b (j + 1) (vt j C Vo K a b p) ≤ ENNReal.ofReal σ)
    (hρ : nrmD c ℓ₀ a b j (rhoO j C Vb Vo K a b p) ≤ ENNReal.ofReal r) :
    nrmD c ℓ₀ a b j (πobs (dIo j C Vb Vo K a b p)) ≤
      ENNReal.ofReal ((L : ℝ) ^ (2 * ((d : ℝ) - 2)) * (vo + vo * vo) + (σ + σ * σ) + r) := by
  rw [πobs_dIo]
  have h1 : nrmj c ℓ₀ a b j (-Vobs j Vo a b p + (1 / 2 : ℂ) • Vobs j Vo a b p ^ 2) ≤
      ENNReal.ofReal (vo + vo * vo) := by
    refine nn_add (by positivity) (by positivity) (by rw [nrmj_neg]; exact hv) ?_
    exact (nrmj_half_le' _).trans (nrmj_sq_le (by omega) hℓ₀ hvo hv)
  have h2 : nrmj c ℓ₀ a b (j + 1) (-vt j C Vo K a b p + (1 / 2 : ℂ) • vt j C Vo K a b p ^ 2) ≤
      ENNReal.ofReal (σ + σ * σ) := by
    refine nn_add (by positivity) (by positivity) (by rw [nrmj_neg]; exact hvt) ?_
    exact (nrmj_half_le' _).trans (nrmj_sq_le (by omega) hℓ₀ hσ hvt)
  exact dn_add (by positivity) hr (dn_sub (by positivity) (by positivity)
    (dn_theta hd hL hℓ₀ h1) (dn_incl hℓ₀ h2)) hρ

theorem A_bound {p : Fin d → ℕ} {vh σ : ℝ} (hvh : 0 ≤ vh) (hσ : 0 ≤ σ)
    (hv : nrmj c ℓ₀ a b j (Vhat j Vo K a b p) ≤ ENNReal.ofReal vh)
    (hvt : nrmj c ℓ₀ a b (j + 1) (vt j C Vo K a b p) ≤ ENNReal.ofReal σ) :
    nrmD c ℓ₀ a b j (Aq j C Vo K a b p) ≤
      ENNReal.ofReal ((L : ℝ) ^ (2 * ((d : ℝ) - 2)) * vh + σ) :=
  dn_sub (by positivity) hσ (dn_theta hd hL hℓ₀ hv) (dn_incl hℓ₀ hvt)

theorem Y_bound {p : Fin d → ℕ} {q r : ℝ} (hq0 : 0 ≤ q) (hr : 0 ≤ r)
    (hq : nrmj c ℓ₀ a b j (QobsO a b j K p) ≤ ENNReal.ofReal q)
    (hρ : nrmD c ℓ₀ a b j (rhoO j C Vb Vo K a b p) ≤ ENNReal.ofReal r) :
    nrmD c ℓ₀ a b j (Yq j C Vb Vo K a b p) ≤
      ENNReal.ofReal ((L : ℝ) ^ (2 * ((d : ℝ) - 2)) * q + r) := by
  refine dn_add (by positivity) hr ?_ hρ
  rw [nrmD_neg]; exact dn_theta hd hL hℓ₀ hq

include hC in
/-- The remainder of the two-block terms (`pair_eq`). -/
theorem rem_pair_bound {p p' : Fin d → ℕ} {e o α y : ℝ} (he0 : 0 ≤ e) (ho0 : 0 ≤ o)
    (hα0 : 0 ≤ α) (hy0 : 0 ≤ y)
    (he : nrmD c ℓ₀ a b j (emb (bulk (dIo j C Vb Vo K a b p))) ≤ ENNReal.ofReal e)
    (he' : nrmD c ℓ₀ a b j (emb (bulk (dIo j C Vb Vo K a b p'))) ≤ ENNReal.ofReal e)
    (ho : nrmD c ℓ₀ a b j (πobs (dIo j C Vb Vo K a b p)) ≤ ENNReal.ofReal o)
    (ho' : nrmD c ℓ₀ a b j (πobs (dIo j C Vb Vo K a b p')) ≤ ENNReal.ofReal o)
    (hA : nrmD c ℓ₀ a b j (Aq j C Vo K a b p) ≤ ENNReal.ofReal α)
    (hA' : nrmD c ℓ₀ a b j (Aq j C Vo K a b p') ≤ ENNReal.ofReal α)
    (hY : nrmD c ℓ₀ a b j (Yq j C Vb Vo K a b p) ≤ ENNReal.ofReal y)
    (hY' : nrmD c ℓ₀ a b j (Yq j C Vb Vo K a b p') ≤ ENNReal.ofReal y) :
    nrmj c ℓ₀ a b (j + 1) (ECO C (emb (bulk (dIo j C Vb Vo K a b p)) *
        πobs (dIo j C Vb Vo K a b p') +
        πobs (dIo j C Vb Vo K a b p) * emb (bulk (dIo j C Vb Vo K a b p')) -
        Aq j C Vo K a b p * Yq j C Vb Vo K a b p' - Yq j C Vb Vo K a b p * Aq j C Vo K a b p' +
        Yq j C Vb Vo K a b p * Yq j C Vb Vo K a b p')) ≤
      ENNReal.ofReal (e * o + o * e + α * y + y * α + y * y) := by
  have hd2 : 2 ≤ d := by omega
  refine (nrmj_ECO_le_nrmD hℓ₀ hC _).trans ?_
  refine dn_add (by positivity) (by positivity) ?_ (dn_mul hd2 hℓ₀ hy0 hY hY')
  refine dn_sub (by positivity) (by positivity) ?_ (dn_mul hd2 hℓ₀ hy0 hY hA')
  refine dn_sub (by positivity) (by positivity) ?_ (dn_mul hd2 hℓ₀ hα0 hA hY')
  exact dn_add (by positivity) (by positivity) (dn_mul hd2 hℓ₀ he0 he ho')
    (dn_mul hd2 hℓ₀ ho0 ho he')

include hC in
/-- The remainder of the single-block terms (`Mb_eq`). -/
theorem rem_block_bound {p : Fin d → ℕ} {vo q r : ℝ} (hvo : 0 ≤ vo) (hq0 : 0 ≤ q) (hr : 0 ≤ r)
    (hv : nrmj c ℓ₀ a b j (Vobs j Vo a b p) ≤ ENNReal.ofReal vo)
    (hq : nrmj c ℓ₀ a b j (QobsO a b j K p) ≤ ENNReal.ofReal q)
    (hρ : nrmD c ℓ₀ a b j (rhoO j C Vb Vo K a b p) ≤ ENNReal.ofReal r) :
    nrmj c ℓ₀ a b (j + 1) ((1 / 2 : ℂ) • ECO C (thetaO (Vobs j Vo a b p ^ 2 -
        Vhat j Vo K a b p ^ 2)) + ECO C (rhoO j C Vb Vo K a b p)) ≤
      ENNReal.ofReal ((L : ℝ) ^ (2 * ((d : ℝ) - 2)) * (q * (2 * vo + q)) + r) := by
  have hd2 : 2 ≤ d := by omega
  have e : Vobs j Vo a b p ^ 2 - Vhat j Vo K a b p ^ 2 =
      QobsO a b j K p * (2 * Vobs j Vo a b p - QobsO a b j K p) := by
    rw [Vhat]; ring
  have h1 : nrmj c ℓ₀ a b j (Vobs j Vo a b p ^ 2 - Vhat j Vo K a b p ^ 2) ≤
      ENNReal.ofReal (q * (2 * vo + q)) := by
    rw [e]
    refine nn_mul hd2 hℓ₀ hq0 hq (nn_sub (by positivity) hq0 ?_ hq)
    rw [two_mul]; exact (nn_add hvo hvo hv hv).trans_eq (by rw [two_mul])
  refine nn_add (by positivity) hr ((nrmj_half_le' _).trans (nn_ECO hd hL hℓ₀ hC h1)) ?_
  exact (nrmj_ECO_le_nrmD hℓ₀ hC _).trans hρ

include hC in
/-- `(δI)^X` with a block without source points. -/
theorem rem_many_bound {X : Finset (Lam d L N)} {p₀ : Fin d → ℕ} (hp₀ : p₀ ∈ blocks j X)
    (ha : a ∉ blockSet (L := L) (N := N) j p₀) (hb : b ∉ blockSet (L := L) (N := N) j p₀)
    {e o : ℝ} (he0 : 0 ≤ e) (ho0 : 0 ≤ o)
    (he : nrmD c ℓ₀ a b j (emb (bulk (dIo j C Vb Vo K a b p₀))) ≤ ENNReal.ofReal e)
    (h1 : ∀ p ∈ blocks j X, nrmD c ℓ₀ a b j (dIo j C Vb Vo K a b p) ≤ 1)
    (ho : ∀ p ∈ blocks j X, nrmD c ℓ₀ a b j (πobs (dIo j C Vb Vo K a b p)) ≤ ENNReal.ofReal o) :
    nrmj c ℓ₀ a b (j + 1) (πobs (ECO C (dIPowG (obsA c C) j (obsI j C Vb Vo K a b) X))) ≤
      ENNReal.ofReal (e * ((blocks j X).card * o)) := by
  have hd2 : 2 ≤ d := by omega
  rw [πobs_ECO, πobs_dIPowG_of_block hp₀ (πobs_dIo_of_not_mem ha hb)]
  refine (nrmj_ECO_le_nrmD hℓ₀ hC _).trans (dn_mul hd2 hℓ₀ he0 he ?_)
  refine (nrmD_πobs_prod_le hd2 hℓ₀ j _ _ ho0 (fun p hp => h1 p (mem_of_mem_erase hp))
    (fun p hp => ho p (mem_of_mem_erase hp))).trans (ENNReal.ofReal_le_ofReal ?_)
  gcongr
  exact erase_subset _ _

end Rem

end

end Obs
