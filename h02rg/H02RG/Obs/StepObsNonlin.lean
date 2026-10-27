import Obs.StepObsNonlinGen
import Obs.StepObsCoupling

/-!
# Theorem `thm:step-obs`: the non-linear part (`NonlinObsStmt`)

"The non-linear contribution does not require any changes as the bound from Section
`sec:K-nonlinear` already gives `A^ν O(‖K‖(‖V‖ + ‖K‖))`."  We apply the generic Lemmas
`lem:NonlinearCheckK`, `lem:Ri-bd` of `Obs.StepObsNonlinGen` to the algebra with observables,
with the norms
* `‖·‖_{T_{j+1}(ℓ_{j+1})}` with the weights of scale `j + 1` on `OE c Λ` (`nrmj (j+1)`), and
* the same norm on the doubled algebra `OE c (Λ ⊔ Λ)`,
which have the product property (`oT_mul_le`), `𝔼_{C_{j+1}}` is a contraction (`oT_EC_le`) and
`‖θ F‖ ≤ L^{2(d-2)} ‖F‖_j` (`e:Tphi-obs-ub`, `normj_succ_le`).  The inputs are bounded crudely,
in terms of the *full* norms (bulk plus observable parts):
* `‖θ K(W)‖ ≤ K₂ ‖K(W)‖_j`, `‖θ J(B, X)‖ ≤ K₂ (C_J ‖K^∅‖ + C_Q ‖K^obs‖)` (`QJ_bounds`,
  `Qobs_bounds`);
* `‖δI(B)‖ ≤ K₂ ‖e^{-V_j(B)} - 1‖_j + ‖e^{-(u+V)_{j+1}(B)} - 1‖_{j+1}` with the coupling
  constant bounds of `Step.block_real` and `Obs.Vobs_next_bounds` (`e:uobs+`, `e:vobs+`).
Here `K₂ = L^{2(d-2)}`; the resulting powers of `L` are the factor `L^m` of `NonlinObsStmt`.
-/

namespace Obs

noncomputable section

open Finset Grassmann SA Loc Step LocObs Gen

/-! ### The norms as submultiplicative norms -/

section SN

variable {c : Case} {X : Type*} [DecidableEq X] [Fintype X] {E : Type*} [Fintype E]
  [DecidableEq E] [AddAction (E → ℕ) X]

/-- `oT E p h ℓ w` on the even elements, a submultiplicative norm (`e:T-product`). -/
def oTSN (E : Type*) [Fintype E] [DecidableEq E] [AddAction (E → ℕ) X] (p : ℕ) (h ℓ : ℝ)
    (w : Wt) (hh : 0 < h) (hℓ : 0 < ℓ) (hw : w.Sub) : SNorm (OE c X) where
  nrm F := oT E p h ℓ w (F : SA c X)
  zero := oT_zero
  add F G := oT_add_le (F : SA c X) (G : SA c X)
  neg F := oT_neg (F : SA c X)
  mul F G := oT_mul_le hh hℓ hw F G
  one := oT_one_le hh hℓ

end SN

variable {d L N : ℕ} [NeZero L]

/-! ### `J^obs` -/

section JO

variable {c : Case} (a b : Lam d L N) (j : ℕ) (K : Finset (Lam d L N) → OE c (Lam d L N))

theorem JO_of_not_small' {p : Fin d → ℕ} {X : Finset (Lam d L N)} (hX : ¬ IsSmall j X) :
    JO a b j K p X = 0 := by
  unfold JO
  rw [if_neg (fun h => hX h.2.1)]

/-- `e:J-zero` for `J^obs`: `∑_{X ⊇ B} J(B, X) = 0`. -/
theorem JO_zero {p : Fin d → ℕ} (hp : p ∈ blockIdx (L := L) (N := N) j) :
    ∑ X ∈ (smallSets (L := L) (N := N) j).filter (fun X => blockSet j p ⊆ X),
      JO a b j K p X = 0 := by
  classical
  by_cases hN : j + 1 < N
  · have hBs := isSmall_blockSet_of_mem hp
    have hBm : blockSet j p ∈ (smallSets (L := L) (N := N) j).filter
        (fun X => blockSet j p ⊆ X) := mem_filter.2 ⟨mem_smallSets.2 hBs, subset_rfl⟩
    rw [← add_sum_erase _ _ hBm]
    unfold JO
    rw [if_pos ⟨hN, hBs, subset_rfl⟩, if_pos rfl, neg_add_eq_zero]
    refine sum_congr ?_ fun Y hY => ?_
    · ext Y; simp only [mem_erase, mem_filter]; tauto
    · obtain ⟨hne, hY'⟩ := mem_erase.1 hY
      obtain ⟨hYs, hBY⟩ := mem_filter.1 hY'
      rw [if_pos ⟨hN, mem_smallSets.1 hYs, hBY⟩, if_neg hne]
  · refine sum_eq_zero fun X _ => ?_
    unfold JO
    rw [if_neg (fun h => hN h.1)]

end JO

/-! ### Elementary norm bounds -/

section Bounds

variable {c : Case} {ℓ₀ : ℝ} {a b : Lam d L N}

theorem nrmj_one_le (hℓ₀ : 0 < ℓ₀) (k : ℕ) : nrmj c ℓ₀ a b k (1 : OE c (Lam d L N)) ≤ 1 := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  exact oT_one_le (by positivity) (ellj_pos hL0 hℓ₀ k)

/-- `‖e^z e^G‖ ≤ e^{|z| + ‖G‖}`. -/
theorem nrmj_alg_mul_oexp_le (hd : 2 ≤ d) (hℓ₀ : 0 < ℓ₀) (k : ℕ) {z : ℂ}
    {G : OE c (Lam d L N)} (hG : bulk G = 0) {s r : ℝ} (hz : ‖z‖ ≤ s) (hr : 0 ≤ r)
    (hGr : nrmj c ℓ₀ a b k G ≤ ENNReal.ofReal r) :
    nrmj c ℓ₀ a b k (algebraMap ℂ (OE c (Lam d L N)) (Complex.exp z) * oexp G) ≤
      ENNReal.ofReal (Real.exp (s + r)) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hGe : ε ((G : SA c (Lam d L N)).e) = 0 := by
    rw [← coe_bulk, hG]; simp
  rw [← Algebra.smul_def, nrmj_smul, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_)
    (oT_oexp_le (by positivity) (ellj_pos hL0 hℓ₀ k) (wj_sub hd c hℓ₀ _ k) hGe hr hGr)
  rw [Complex.norm_exp]
  exact Real.exp_le_exp.2 ((Complex.re_le_norm z).trans hz)

/-- `‖e^z - 1‖ ≤ 2 |z|` for `|z| ≤ 1`. -/
theorem nrmj_alg_sub_one_le (hℓ₀ : 0 < ℓ₀) (k : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    nrmj c ℓ₀ a b k (algebraMap ℂ (OE c (Lam d L N)) (Complex.exp z) - 1) ≤
      ENNReal.ofReal (2 * ‖z‖) := by
  have e : algebraMap ℂ (OE c (Lam d L N)) (Complex.exp z) - 1 =
      (Complex.exp z - 1) • (1 : OE c (Lam d L N)) := by
    rw [sub_smul, one_smul, Algebra.algebraMap_eq_smul_one]
  rw [e, nrmj_smul]
  refine (mul_le_of_le_one_right zero_le (nrmj_one_le hℓ₀ k)).trans
    (ENNReal.ofReal_le_ofReal (Complex.norm_exp_sub_one_le hz))

/-- `‖e^G - 1‖ ≤ 2 ‖G‖` for `‖G‖ ≤ r ≤ 1`, `ε(G_∅) = 0`. -/
theorem nrmj_oexp_sub_one_le (hd : 2 ≤ d) (hℓ₀ : 0 < ℓ₀) (k : ℕ) {G : OE c (Lam d L N)}
    (hG : ε ((G : SA c (Lam d L N)).e) = 0) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hGr : nrmj c ℓ₀ a b k G ≤ ENNReal.ofReal r) :
    nrmj c ℓ₀ a b k (oexp G - 1) ≤ ENNReal.ofReal (2 * r) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  exact (oT_oexp_sub_one_le (by positivity) (ellj_pos hL0 hℓ₀ k) (wj_sub hd c hℓ₀ _ k) hG hr
    hGr).trans (ENNReal.ofReal_le_ofReal (exp_sub_one_le hr hr1))

/-- `‖V_j(B)‖_{T_k(ℓ_k)} ≤ ‖V^∅(B)‖ + ‖V^obs(B)‖`. -/
theorem nrmj_VfullX_le (k : ℕ) (Vb : Vcoup) (Vo : Coup c) (X : Finset (Lam d L N)) :
    nrmj c ℓ₀ a b k (VfullX Vb Vo a b X) ≤
      Tj d (L : ℝ) k (ellj d L ℓ₀ k) (Vb.eval X) +
        nrmj c ℓ₀ a b k (splitO c (Coup.toV c Vo) a b X) := by
  refine (nrmj_add_le k _ _).trans (add_le_add (le_of_eq ?_) le_rfl)
  rw [nrmj_emb, coe_VE]

variable (c ℓ₀ a b) in
/-- The norm on the doubled algebra at scale `j + 1`. -/
abbrev nrm2 (k : ℕ) (F : OE c (Lam d L N ⊕ Lam d L N)) : ENNReal :=
  oT (Dir d) (pPhi d) ((L : ℝ) ^ k) (ellj d L ℓ₀ k) (wj d L c ℓ₀ (coal L a b : ℕ∞) k)
    (F : SA c (Lam d L N ⊕ Lam d L N))

/-- `‖θ F‖_{j+1} ≤ L^{2(d-2)} ‖F‖_j` (`e:Tphi-obs-ub`). -/
theorem nrm2_theta_le (hd : 3 ≤ d) (hL : (4 : ℝ) ≤ L) (hℓ₀ : 0 < ℓ₀) (j : ℕ)
    (F : OE c (Lam d L N)) :
    nrm2 c ℓ₀ a b (j + 1) (thetaO F) ≤
      ENNReal.ofReal ((L : ℝ) ^ (2 * ((d : ℝ) - 2))) * nrmj c ℓ₀ a b j F := by
  have hL0 : (0 : ℝ) < L := by linarith
  rw [nrm2, coe_thetaO]
  exact (oT_theta_le (by positivity) (ellj_pos hL0 hℓ₀ (j + 1)) _).trans
    (normj_succ_le hd hL c hℓ₀ _ j _).2

/-- `‖ι F‖ ≤ ‖F‖`. -/
theorem nrm2_incl_le (hℓ₀ : 0 < ℓ₀) (k : ℕ) (F : OE c (Lam d L N)) :
    nrm2 c ℓ₀ a b k (inclO F) ≤ nrmj c ℓ₀ a b k F := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  rw [nrm2, coe_inclO]
  exact oT_incl_le (by positivity) (ellj_pos hL0 hℓ₀ k) _

/-- `𝔼_{C_{j+1}}` is a contraction. -/
theorem nrmj_ECO_le' (hℓ₀ : 0 < ℓ₀) {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℝ}
    (hC : GoodCov j ℓ₀ C) (F : OE c (Lam d L N ⊕ Lam d L N)) :
    nrmj c ℓ₀ a b (j + 1) (ECO C F) ≤ nrm2 c ℓ₀ a b (j + 1) F := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  rw [nrm2, nrmj, normj, oTj, coe_ECO]
  exact oT_EC_le (by positivity) (ellj_pos hL0 hℓ₀ (j + 1)) hC.psd hC.norm _

end Bounds


/-- The real inequality for `‖e^{-(u+V)_{j+1}(B)} - 1‖`. -/
theorem It_real {x y a : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y ≤ a) (ha : a ≤ 1 / 40) :
    (2 * x + 2 * y + 2 * x * (2 * y)) + 2 * (2 * x + y) +
      (2 * x + 2 * y + 2 * x * (2 * y)) * (2 * (2 * x + y)) ≤ 10 * a := by
  have h1 : x * y ≤ (x + y) / 40 := by nlinarith
  have h2 : (2 * x + 2 * y + 2 * x * (2 * y)) ≤ 3 * (x + y) := by nlinarith
  have h3 : (2 * x + 2 * y + 2 * x * (2 * y)) * (2 * (2 * x + y)) ≤ 3 * (x + y) * (4 * (x + y)) := by
    have : 0 ≤ 2 * x + 2 * y + 2 * x * (2 * y) := by positivity
    have : 2 * (2 * x + y) ≤ 4 * (x + y) := by linarith
    calc _ ≤ 3 * (x + y) * (2 * (2 * x + y)) := by gcongr
      _ ≤ _ := by gcongr
  nlinarith

/-- Real inequalities of the main proof. -/
theorem r_vk {Cv K v k : ℝ} (hCv : 1 ≤ Cv) (hK : 0 ≤ K) (hk : 0 ≤ k) :
    Cv * K * v + K * k ≤ Cv * K * (v + k) := by
  nlinarith [mul_le_mul_of_nonneg_right hCv (mul_nonneg hK hk)]

theorem r_abru {vb kb vo ko CB CV K : ℝ} (hK : 1 ≤ K) (hCB : 0 ≤ CB) (hCV : 0 ≤ CV)
    (hvb : 0 ≤ vb) (hkb : 0 ≤ kb) (hvo : 0 ≤ vo) (hko : 0 ≤ ko) :
    vb + CB * kb + CV * K * (vo + ko) ≤
      (3 + 2 * CV) * K * (vb + vo) + (3 * CB + 2 * CV) * (K * (kb + ko)) := by
  have h1 : vb ≤ K * vb := le_mul_of_one_le_left hvb hK
  have h2 : kb ≤ K * kb := le_mul_of_one_le_left hkb hK
  have h3 : 0 ≤ K * vb := by positivity
  have h4 : 0 ≤ K * vo := by positivity
  have h5 : 0 ≤ K * kb := by positivity
  have h6 : 0 ≤ K * ko := by positivity
  nlinarith [mul_nonneg hCV h3, mul_nonneg hCV h4, mul_nonneg hCV h5, mul_nonneg hCV h6,
    mul_nonneg hCB h5, mul_nonneg hCB h6, mul_le_mul_of_nonneg_left h2 hCB]

theorem r_r0 {Cv K v c k : ℝ} (hCv : 1 ≤ Cv) (hK : 1 ≤ K) (hv : 0 ≤ v) (hc : 0 ≤ c)
    (hk : 0 ≤ k) : v ≤ Cv * K * v + c * k := by
  have : 1 ≤ Cv * K := one_le_mul_of_one_le_of_one_le hCv hK
  nlinarith [mul_nonneg hc hk]

theorem r_dI {Cv K v c k : ℝ} (hCv : 2 ≤ Cv) (hK : 0 ≤ K) (hv : 0 ≤ v) (hc : 0 ≤ c)
    (hk : 0 ≤ k) :
    K * (2 * v) + 10 * (Cv * K * v + c * k) ≤ (11 + 10 * c) * (Cv * K * v + k) := by
  have h1 : 0 ≤ K * v := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hCv h1, mul_nonneg hc (mul_nonneg (by linarith : (0:ℝ) ≤ Cv) h1)]

theorem r_J {K CJ Cq kb ko : ℝ} (hK : 0 ≤ K) (hCJ : 0 ≤ CJ) (hCq : 0 ≤ Cq) (hkb : 0 ≤ kb)
    (hko : 0 ≤ ko) : K * (CJ * kb + Cq * ko) ≤ (CJ + Cq) * (K * (kb + ko)) := by
  nlinarith [mul_nonneg (mul_nonneg hK hCJ) hko, mul_nonneg (mul_nonneg hK hCq) hkb]

theorem r_pref {a Ld n n' : ℝ} (ha : 0 ≤ a) (hLd : 0 ≤ Ld) (hn' : 0 ≤ n')
    (h : 4 * a * (3 * Ld) ≤ 1 / 2) (hn : n ≤ Ld * n') : 11 * a * n ≤ n' * (1 / 2) := by
  have h1 : 11 * a * n ≤ 11 * a * (Ld * n') := by gcongr
  have h2 : 12 * (a * Ld) ≤ 1 / 2 := by linarith
  have h3 : 0 ≤ a * Ld * n' := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h2 hn']

theorem r_final {Cf Aν Cv K Ld vb kb vo ko : ℝ} (hCf : 0 ≤ Cf) (hAν : 0 ≤ Aν) (hCv : 1 ≤ Cv)
    (_hK : 0 ≤ K) (hKL : K ^ 2 ≤ Ld) (hvb : 0 ≤ vb) (hkb : 0 ≤ kb) (hvo : 0 ≤ vo)
    (hko : 0 ≤ ko) :
    Cf * Aν * (K * (kb + ko)) * (K * (kb + ko) + Cv * K * (vb + vo)) ≤
      Cf * Cv * Ld * Aν * ((vb + kb + ko) * (vb + vo + kb + ko)) := by
  set k := kb + ko
  set v := vb + vo
  have hk : 0 ≤ k := by positivity
  have hv : 0 ≤ v := by positivity
  have h1 : K * k * (K * k + Cv * K * v) ≤ Cv * K ^ 2 * (k * (k + v)) := by
    have : k * k ≤ Cv * (k * k) := le_mul_of_one_le_left (by positivity) hCv
    have hK2' : 0 ≤ K ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this hK2']
  have h2 : k * (k + v) ≤ (vb + kb + ko) * (vb + vo + kb + ko) := by
    have e1 : vb + kb + ko = vb + k := by ring
    have e2 : vb + vo + kb + ko = v + k := by ring
    rw [e1, e2]; nlinarith [mul_nonneg hvb (add_nonneg hk hv)]
  have hq : 0 ≤ k * (k + v) := by positivity
  calc Cf * Aν * (K * k) * (K * k + Cv * K * v) = Cf * Aν * (K * k * (K * k + Cv * K * v)) := by
        ring
    _ ≤ Cf * Aν * (Cv * K ^ 2 * (k * (k + v))) := by gcongr
    _ ≤ Cf * Aν * (Cv * Ld * ((vb + kb + ko) * (vb + vo + kb + ko))) := by
        have : 0 ≤ Cv * Ld := mul_nonneg (by linarith) ((sq_nonneg K).trans hKL)
        gcongr
    _ = _ := by ring

set_option maxHeartbeats 4000000 in
/-- **The non-linear part of Theorem `thm:step-obs`** (`NonlinObsStmt`), with `ν = 2^{d+3}` and
`m = 4d`. -/
theorem obs_nonlinear_bound_proof {d : ℕ} (hd : 3 ≤ d) : NonlinObsStmt d := by
  obtain ⟨CB, LB, hCB, hLB, hbr⟩ := block_real hd
  obtain ⟨CJ, LJ, hCJ, hLJ, hQJ⟩ := QJ_bounds hd
  obtain ⟨Cq, hCq, hQo⟩ := Qobs_bounds d
  obtain ⟨CV, LV, hCV, hLV, hV⟩ := Vobs_next_bounds hd
  obtain ⟨η, hη0, hη1, hcomb⟩ := comb2 d
  obtain ⟨cc, hc⟩ := card_small_containing d
  set Cv : ℝ := 3 + 2 * CV with hCv
  set CB' : ℝ := 3 * CB + 2 * CV with hCB'
  set cJ : ℝ := CJ + Cq with hcJ
  set C₁ : ℝ := 11 + 10 * CB' with hC₁
  have hCV0 : 0 ≤ CV := by linarith
  have hCB'0 : 0 ≤ CB' := by positivity
  have hcJ0 : 0 ≤ cJ := by positivity
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hCv1 : 1 ≤ Cv := by linarith
  set Cf : ℝ := (1 + 2 ^ d * cJ) * (1 + 2 ^ d * cJ + C₁) + C₁ +
    2 ^ d * 10 * (1 + CB') * 2 ^ 2 ^ d * cJ with hCf
  have hCf0 : 0 ≤ Cf := by rw [hCf]; positivity
  refine ⟨Cf * Cv, ((2 ^ (d + 3) : ℕ) : ℝ), 4 * d, max LB (max LJ LV), by positivity,
    by positivity, ?_⟩
  intro L _ hL
  have hLB' : LB ≤ L := le_trans (le_max_left _ _) hL
  have hLJ' : LJ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
  have hLV' : LV ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
  have hL4 : (4 : ℝ) ≤ L := four_le_of_L₀ (hLB.trans hLB')
  have hL0 : (0 : ℝ) < L := by linarith
  have hL1r : (1 : ℝ) ≤ L := by linarith
  have hd8 : 2 ^ (d + 3) = 2 ^ d * 8 := by ring
  have hd4 : 2 ^ (d + 2) = 2 ^ d * 4 := by ring
  have hLL := hLB.trans hLB'
  have hL2 : 2 ^ (d + 2) ≤ L := by
    rw [hd8] at hLL; rw [hd4]; generalize 2 ^ d = t at hLL ⊢; omega
  have hL1 : 2 ^ d + 1 ≤ L := by
    rw [hd8] at hLL; generalize 2 ^ d = t at hLL ⊢; omega
  have hLq : 2 ^ (d + 3) + 8 * d < L := by have := hLV.trans hLV'; omega
  set K₂ : ℝ := (L : ℝ) ^ (2 * ((d : ℝ) - 2)) with hK₂
  have hK1 : 1 ≤ K₂ := one_le_K₂ hd
  have hK0 : 0 < K₂ := by linarith
  set M : ℕ := 2 ^ ((1 + cc) * L ^ d) with hMdef
  have hM1 : 1 ≤ M := Nat.one_le_two_pow
  set P : ℝ := 2 * M with hPdef
  have hP1 : 1 ≤ P := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM1
    linarith
  have hP0 : 0 < P := by linarith
  have hη2 : 2 * η ≠ 0 := by positivity
  have hη3 : 1 + 2 * η ≠ 0 := by positivity
  have hη' : 0 < 2 * η / (1 + 2 * η) := by positivity
  set A₀ : ℝ := max (P ^ 2 ^ (d + 1)) ((4 * P) ^ ((1 + 2 * η) / (2 * η))) with hA₀
  have hA₀1 : 1 ≤ A₀ := le_trans (one_le_pow₀ hP1) (le_max_left _ _)
  refine ⟨A₀, hA₀1, ?_⟩
  intro A hA
  have hA1 : 1 ≤ A := hA₀1.trans hA
  have hA0 : 0 < A := by linarith
  have hA0' : A ≠ 0 := hA0.ne'
  have hPA : P ^ 2 ^ (d + 1) ≤ A := le_trans (le_max_left _ _) hA
  have hAP : 4 * P ≤ A ^ (2 * η / (1 + 2 * η)) := by
    calc 4 * P = ((4 * P) ^ ((1 + 2 * η) / (2 * η))) ^ (2 * η / (1 + 2 * η)) := by
          rw [← Real.rpow_mul (by positivity)]
          rw [show (1 + 2 * η) / (2 * η) * (2 * η / (1 + 2 * η)) = 1 by field_simp]
          rw [Real.rpow_one]
      _ ≤ A ^ (2 * η / (1 + 2 * η)) :=
          Real.rpow_le_rpow (by positivity) (le_trans (le_max_right _ _) hA) hη'.le
  set D : ℝ := (A * P) ^ 2 ^ d with hD
  have hD0 : 0 < D := by positivity
  set G : ℝ := (1 + 2 ^ d * cJ) * A ^ 2 ^ d + C₁ * A with hG
  have hG0 : 0 ≤ G := by positivity
  have hLd : (0 : ℝ) < 3 * (L : ℝ) ^ d := by positivity
  set ε' : ℝ := min (1 / (40 * (1 + CB'))) (min (1 / (8 * (1 + CB') * (3 * (L : ℝ) ^ d)))
    (min (1 / A ^ 2 ^ d) (min (1 / (C₁ * A + 1)) (1 / (D * G + 1))))) with hε'
  have hε'0 : 0 < ε' := by
    refine lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity)
      (lt_min (by positivity) (by positivity))))
  have e2 : ε' ≤ 1 / (40 * (1 + CB')) := min_le_left _ _
  have e3 : ε' ≤ 1 / (8 * (1 + CB') * (3 * (L : ℝ) ^ d)) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have e4 : ε' ≤ 1 / A ^ 2 ^ d :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have e5 : ε' ≤ 1 / (C₁ * A + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _)))
  have e6 : ε' ≤ 1 / (D * G + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_right _ _)))
  set ε₀ : ℝ := min (ε' / (2 * Cv * K₂)) (1 / K₂) with hε₀
  have hε₀0 : 0 < ε₀ := lt_min (by positivity) (by positivity)
  refine ⟨ε₀, hε₀0, ?_⟩
  intro N j hj ℓ₀ hℓ₀ c P' C Vb Vo K a b h hb ho U hU
  classical
  have hε₀1 : ε₀ ≤ ε' / (2 * Cv * K₂) := min_le_left _ _
  have hε₀2 : ε₀ ≤ 1 / K₂ := min_le_right _ _
  have hC := h.cov
  obtain ⟨hvb, hkb, hvb0, hkb0, hvkb, hblk⟩ :=
    hbr L hLB' N j hj ℓ₀ hℓ₀ C hC Vb (bulkK K) A hA1 h.bulk ε₀ hε₀0.le hb
  have hsm : ENNReal.ofReal K₂ * (VnormObs c ℓ₀ a b j Vo + KnormObs c ℓ₀ a b j A K) ≤ 1 := by
    calc ENNReal.ofReal K₂ * (VnormObs c ℓ₀ a b j Vo + KnormObs c ℓ₀ a b j A K)
        ≤ ENNReal.ofReal K₂ * ENNReal.ofReal (1 / K₂) :=
          mul_le_mul_right (ho.trans (ENNReal.ofReal_le_ofReal hε₀2)) _
      _ = 1 := by
          rw [← ENNReal.ofReal_mul hK0.le, mul_one_div_cancel hK0.ne', ENNReal.ofReal_one]
  obtain ⟨hvo, hko, -⟩ := finite_of_small hK1 hsm
  set vbR := (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) Vb).toReal with hvbR
  set kbR := (Knorm j (ellj d L ℓ₀ j) A (bulkK K)).toReal with hkbR
  set voR := (VnormObs c ℓ₀ a b j Vo).toReal with hvoR
  set koR := (KnormObs c ℓ₀ a b j A K).toReal with hkoR
  have hvo0 : 0 ≤ voR := ENNReal.toReal_nonneg
  have hko0 : 0 ≤ koR := ENNReal.toReal_nonneg
  have hvkoR : voR + koR ≤ ε₀ := by
    have := ho
    rw [hvo, hko, ← ENNReal.ofReal_add hvo0 hko0] at this
    exact (ENNReal.ofReal_le_ofReal_iff hε₀0.le).1 this
  -- the parameters
  set kr : ℝ := K₂ * (kbR + koR) with hkr
  set vr : ℝ := Cv * K₂ * (vbR + voR) with hvr
  have hkr0 : 0 ≤ kr := by positivity
  have hvr0 : 0 ≤ vr := by positivity
  have hvk' : vr + kr ≤ ε' := by
    have h1 : vr + kr ≤ Cv * K₂ * ((vbR + voR) + (kbR + koR)) :=
      r_vk hCv1 hK0.le (add_nonneg hkb0 hko0)
    have h2 : (vbR + voR) + (kbR + koR) ≤ 2 * ε₀ := by
      have := hvkb; have := hvkoR; linarith
    calc vr + kr ≤ Cv * K₂ * (2 * ε₀) := h1.trans (by gcongr)
      _ ≤ Cv * K₂ * (2 * (ε' / (2 * Cv * K₂))) := by gcongr
      _ = ε' := by field_simp
  obtain ⟨ha1, ha2, hκ₀1, hδ₁1, hDβ⟩ := eps_facts (d := d) hCB'0 hC₁0 hcJ0 hLd hA1 hD0.le
    hvr0 hkr0 hvk' e2 e3 e4 e5 (by rw [hG] at e6; exact e6)
  set aa := vr + CB' * kr with haa
  have haa0 : 0 ≤ aa := by positivity
  set κ₀ := A ^ 2 ^ d * kr with hκ₀
  have hκ₀0 : 0 ≤ κ₀ := by positivity
  set δ₁ := C₁ * (vr + kr) * A with hδ₁
  have hδ₁0 : 0 ≤ δ₁ := by positivity
  set ab := vbR + CB * kbR with hab
  set ru := CV * K₂ * (voR + koR) with hru
  have hab0 : 0 ≤ ab := by positivity
  have hru0 : 0 ≤ ru := by positivity
  have habru : ab + ru ≤ aa := r_abru hK1 hCB hCV0 hvb0 hkb0 hvo0 hko0
  have hr0a : vbR + voR ≤ aa := r_r0 hCv1 hK1 (add_nonneg hvb0 hvo0) hCB'0 hkr0
  -- the norms
  have hd2 : 2 ≤ d := by omega
  have hh' : (0 : ℝ) < (L : ℝ) ^ (j + 1) := by positivity
  have hℓ' := ellj_pos (d := d) hL0 hℓ₀ (j + 1)
  have hw' := wj_sub (L := L) hd2 c hℓ₀ (coal L a b : ℕ∞) (j + 1)
  set n1 : SNorm (OE c (Lam d L N)) := oTSN (Dir d) (pPhi d) ((L : ℝ) ^ (j + 1))
    (ellj d L ℓ₀ (j + 1)) (wj d L c ℓ₀ (coal L a b : ℕ∞) (j + 1)) hh' hℓ' hw' with hn1
  set n2 : SNorm (OE c (Lam d L N ⊕ Lam d L N)) := oTSN (Dir d) (pPhi d) ((L : ℝ) ^ (j + 1))
    (ellj d L ℓ₀ (j + 1)) (wj d L c ℓ₀ (coal L a b : ℕ∞) (j + 1)) hh' hℓ' hw' with hn2
  have hn1e : ∀ F, n1.nrm F = nrmj c ℓ₀ a b (j + 1) F := fun F => rfl
  have hn2e : ∀ F, n2.nrm F = nrm2 c ℓ₀ a b (j + 1) F := fun F => rfl
  set Fi := obsI j C Vb Vo K a b with hFi
  set Al := obsA c C with hAl
  -- coupling constants
  obtain ⟨-, -, -, -, h5⟩ := hV L hLV' N j hj ℓ₀ hℓ₀ c P' C Vb Vo K a b A hA1 h hsm
  have hru_e : ENNReal.ofReal (CV * K₂) * (VnormObs c ℓ₀ a b j Vo + KnormObs c ℓ₀ a b j A K) =
      ENNReal.ofReal ru := by
    rw [hvo, hko, ← ENNReal.ofReal_add hvo0 hko0, ← ENNReal.ofReal_mul (by positivity)]
  -- per block
  have heu : ∀ p ∈ blockIdx (d := d) (L := L) (N := N) j,
      n1.nrm (Fi.eu p) ≤ ENNReal.ofReal (Real.exp aa) := by
    intro p hp
    rw [hn1e]
    have hu := (hblk p hp).2.1
    refine (nrmj_alg_mul_oexp_le hd2 hℓ₀ (j + 1) (bulk_splitO _ _ _ _ _) hu hru0
      (((h5 _ (isPolymer_blockSet j p)).2.1).trans (le_of_eq hru_e))).trans
      (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 habru))
  have hIt : ∀ p ∈ blockIdx (d := d) (L := L) (N := N) j,
      n1.nrm (It Fi p - 1) ≤ ENNReal.ofReal (10 * aa) := by
    intro p hp
    have hu := (hblk p hp).2.1
    have hV' := (hblk p hp).2.2
    have hu1 : ‖(uVb j C Vb K).1 * ((blockSet (L := L) (N := N) j p).card : ℂ)‖ ≤ ab := hu
    have hz1 : ‖-((uVb j C Vb K).1 * ((blockSet (L := L) (N := N) j p).card : ℂ))‖ ≤ 1 := by
      rw [norm_neg]; linarith
    have hs := nrmj_alg_sub_one_le (c := c) (a := a) (b := b) hℓ₀ (j + 1) hz1
    rw [norm_neg] at hs
    have hs' : n1.nrm (algebraMap ℂ (OE c (Lam d L N))
        (Complex.exp (-((uVb j C Vb K).1 * ((blockSet (L := L) (N := N) j p).card : ℂ)))) - 1) ≤
        ENNReal.ofReal (2 * ab) :=
      hs.trans (ENNReal.ofReal_le_ofReal (by linarith))
    have hbu : bulk (-uObsX j C Vo K a b (blockSet j p)) = 0 := by
      rw [map_neg, uObsX, bulk_splitO, neg_zero]
    have hεu : ε ((-uObsX j C Vo K a b (blockSet j p) : OE c (Lam d L N)) :
        SA c (Lam d L N)).e = 0 := by
      rw [← coe_bulk, hbu]; simp
    have ht : n1.nrm (oexp (-uObsX j C Vo K a b (blockSet j p)) - 1) ≤
        ENNReal.ofReal (2 * ru) := by
      rw [hn1e]
      refine nrmj_oexp_sub_one_le hd2 hℓ₀ (j + 1) hεu hru0 (by linarith) ?_
      rw [nrmj_neg]
      exact ((h5 _ (isPolymer_blockSet j p)).2.1).trans (le_of_eq hru_e)
    have hVf : n1.nrm (oexp (-VfullX (uVb j C Vb K).2 (nextObs C j Vo K a b) a b
        (blockSet j p)) - 1) ≤ ENNReal.ofReal (2 * (2 * ab + ru)) := by
      rw [hn1e]
      refine nrmj_oexp_sub_one_le hd2 hℓ₀ (j + 1) (ε_neg_VfullX a b _ _ _) (by positivity)
        (by linarith) ?_
      rw [nrmj_neg]
      refine (nrmj_VfullX_le (j + 1) _ _ _).trans ?_
      rw [ENNReal.ofReal_add (by positivity) hru0]
      exact add_le_add hV' (((h5 _ (isPolymer_blockSet j p)).2.2).trans (le_of_eq hru_e))
    have h1 := n1.mul_sub_one_le (by positivity) (by positivity) hs' ht
    have h2 := n1.mul_sub_one_le (by positivity) (by positivity) h1 hVf
    refine le_trans ?_ (h2.trans (ENNReal.ofReal_le_ofReal (It_real hab0 hru0 habru ha1)))
    exact le_rfl
  have hdI : ∀ p ∈ blockIdx (L := L) (N := N) j,
      n2.nrm (dIG Al Fi p) ≤ ENNReal.ofReal (δ₁ * A⁻¹) := by
    intro p hp
    have e : dIG Al Fi p = thetaO (Fi.I0 p - 1) - inclO (It Fi p - 1) := by
      rw [dIG, map_sub, map_sub, map_one, map_one]
      show thetaO (Fi.I0 p) - inclO (It Fi p) = _
      ring
    rw [e]
    have h1 : nrm2 c ℓ₀ a b (j + 1) (thetaO (Fi.I0 p - 1)) ≤
        ENNReal.ofReal (K₂ * (2 * (vbR + voR))) := by
      refine (nrm2_theta_le hd hL4 hℓ₀ j _).trans ?_
      rw [ENNReal.ofReal_mul hK0.le]
      gcongr
      refine nrmj_oexp_sub_one_le hd2 hℓ₀ j (ε_neg_VfullX a b _ _ _) (by positivity)
        (by linarith) ?_
      rw [nrmj_neg]
      refine (nrmj_VfullX_le j _ _ _).trans ?_
      rw [ENNReal.ofReal_add hvb0 hvo0]
      refine add_le_add (hblk p hp).1 ?_
      rw [← hvo]
      exact le_iSup₂_of_le (f := fun p _ => nrmj c ℓ₀ a b j
        (splitO c (Coup.toV c Vo) a b (blockSet j p))) p hp le_rfl
    have h2 : nrm2 c ℓ₀ a b (j + 1) (inclO (It Fi p - 1)) ≤ ENNReal.ofReal (10 * aa) :=
      (nrm2_incl_le hℓ₀ (j + 1) _).trans (hIt p hp)
    refine (n2.subR (by positivity) (by positivity) h1 h2).trans (ENNReal.ofReal_le_ofReal ?_)
    have e : δ₁ * A⁻¹ = C₁ * (vr + kr) := by
      rw [hδ₁, mul_assoc, mul_inv_cancel₀ hA0', mul_one]
    rw [e]
    exact r_dI (by linarith) hK0.le (add_nonneg hvb0 hvo0) hCB'0 hkr0
  have hKb : ∀ W : Finset (Lam d L N), IsConn j W →
      n2.nrm (Al.θ (Fi.K W)) ≤ ENNReal.ofReal (κ₀ * A⁻¹ ^ nb j W) := by
    intro W hW
    have hw := (wnormO_le_KnormFull (c := c) (ℓ₀ := ℓ₀) (a := a) (b := b) (A := A)
      (K := K) hW).trans (KnormFull_le j A K)
    rw [wnormO, hkb, hko, ← ENNReal.ofReal_add hkb0 hko0] at hw
    set n := nb j W
    have hAn : (1 : ℝ) ≤ A ^ 2 ^ d * A⁻¹ ^ n * A ^ (n - 2 ^ d) := by
      have h1 : A ^ n ≤ A ^ 2 ^ d * A ^ (n - 2 ^ d) := by
        rw [← pow_add]; exact pow_le_pow_right₀ hA1 (by omega)
      have hAn0 : 0 < A ^ n := by positivity
      rw [inv_pow]
      calc (1 : ℝ) = A ^ n * (A ^ n)⁻¹ := (mul_inv_cancel₀ hAn0.ne').symm
        _ ≤ (A ^ 2 ^ d * A ^ (n - 2 ^ d)) * (A ^ n)⁻¹ := by gcongr
        _ = _ := by ring
    have hKW : nrmj c ℓ₀ a b j (K W) ≤ ENNReal.ofReal (A ^ 2 ^ d * A⁻¹ ^ n * (kbR + koR)) := by
      calc nrmj c ℓ₀ a b j (K W)
          ≤ ENNReal.ofReal (A ^ 2 ^ d * A⁻¹ ^ n * A ^ (n - 2 ^ d)) * nrmj c ℓ₀ a b j (K W) := by
            refine le_mul_of_one_le_left zero_le ?_
            rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hAn
        _ = ENNReal.ofReal (A ^ 2 ^ d * A⁻¹ ^ n) * (ENNReal.ofReal (A ^ (n - 2 ^ d)) *
              nrmj c ℓ₀ a b j (K W)) := by
            rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
        _ ≤ ENNReal.ofReal (A ^ 2 ^ d * A⁻¹ ^ n) * ENNReal.ofReal (kbR + koR) := by gcongr
        _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]
    rw [hn2e]
    refine (nrm2_theta_le hd hL4 hℓ₀ j _).trans ?_
    refine (mul_le_mul_right hKW _).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul hK0.le]
    congr 1
    rw [hκ₀, hkr]; ring
  have hJb : ∀ p ∈ blockIdx (L := L) (N := N) j, ∀ X : Finset (Lam d L N),
      n2.nrm (Al.θ (Fi.J p X)) ≤ ENNReal.ofReal (cJ * κ₀ * A⁻¹ ^ 2 ^ d) := by
    intro p hp X
    rw [hn2e]
    refine (nrm2_theta_le hd hL4 hℓ₀ j _).trans ?_
    have hJ1 := (hQJ L hLJ' N j hj ℓ₀ hℓ₀ (bulkK K) A hA1 h.bulk).2 p hp X
    have hJ2 := (hQo L hLq N j hj ℓ₀ hℓ₀ c P' K a b A hA1 h.loc.hK).2.1 p hp X
    rw [hkb, ← ENNReal.ofReal_mul hCJ] at hJ1
    rw [hko, ← ENNReal.ofReal_mul hCq] at hJ2
    have hJ : nrmj c ℓ₀ a b j (JO a b j K p X) ≤ ENNReal.ofReal (CJ * kbR + Cq * koR) := by
      rw [nrmj_split, bulk_JO, ENNReal.ofReal_add (by positivity) (by positivity)]
      exact add_le_add hJ1 hJ2
    refine (mul_le_mul_right hJ _).trans ?_
    rw [← ENNReal.ofReal_mul hK0.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have e : cJ * κ₀ * A⁻¹ ^ 2 ^ d = cJ * kr := by
      rw [hκ₀, inv_pow]; field_simp
    rw [e]
    exact r_J hK0.le hCJ hCq hkb0 hko0
  have hJs : ∀ p X, ¬ IsSmall j X → Fi.J p X = 0 := fun p X hX => JO_of_not_small' a b j K hX
  have hJ0 : ∀ p ∈ blockIdx (d := d) (L := L) (N := N) j,
      ∑ X ∈ (smallSets (L := L) (N := N) j).filter (fun X => blockSet j p ⊆ X), Fi.J p X = 0 :=
    fun p hp => JO_zero a b j K hp
  have hUj : IsPolymer j U := IsPolymer.of_succ hU.1
  have hpref : Real.exp (11 * aa * nb j U) ≤ 2 ^ nb (j + 1) U := by
    have hnb : (nb j U : ℝ) ≤ (L : ℝ) ^ d * nb (j + 1) U := by
      exact_mod_cast nb_le_of_succ hU.1
    have hx : 11 * aa * nb j U ≤ (nb (j + 1) U : ℝ) * (1 / 2) :=
      r_pref haa0 (by positivity) (Nat.cast_nonneg _) ha2 hnb
    have he : Real.exp (1 / 2) ≤ 2 := by
      have := (abs_le.1 (Real.abs_exp_sub_one_le (x := 1 / 2) (by norm_num))).2
      norm_num at this ⊢; linarith
    calc Real.exp (11 * aa * nb j U) ≤ Real.exp ((nb (j + 1) U : ℝ) * (1 / 2)) :=
          Real.exp_le_exp.2 hx
      _ = Real.exp (1 / 2) ^ nb (j + 1) U := Real.exp_nat_mul _ _
      _ ≤ 2 ^ nb (j + 1) U := pow_le_pow_left₀ (Real.exp_pos _).le he _
  have RH : RHypG Al j Fi n1 n2 U A κ₀ δ₁ cJ aa η P M :=
    { hA := hA1, hκ₀ := hκ₀0, hκ₀1 := hκ₀1, hδ₁ := hδ₁0, hδ₁1 := hδ₁1, hcJ := hcJ0
      hK := hKb, hdI := hdI, hJ := hJb, hJs := hJs
      hE := fun x => nrmj_ECO_le' hℓ₀ hC x
      hJ0 := hJ0, hU := hU.1, ha := haa0, ha1 := ha1, heu := heu, hIt := hIt
      hpref := hpref
      hcount := by
        refine (card_Gset_le (fun b hb => hc L N j b hb) hUj).trans ?_
        rw [hMdef, ← pow_mul]
        exact Nat.pow_le_pow_right (by norm_num) (by
          rw [mul_assoc]; exact Nat.mul_le_mul_left _ (nb_le_of_succ hU.1))
      hη := hη0.le
      hgeom := fun g hg => nU_bound (fun X hX => (hcomb L hL1 N j X hj hX).1)
        (fun b hb => (isSmall_clo_nbhd (by omega) hL2 hj b hb).2.2) hη0.le hg
      hP := rfl
      hM := hM1
      hAP := hAP }
  have hR := RH.R_le hDβ
  have hfin := final_real (d := d) hA1 hP1 hPA hCB'0 hC₁0 hcJ0 hvr0 hkr0
  have hw : wnormO c ℓ₀ a b (j + 1) A U (πobs (R1G Al j Fi U + R2G Al j Fi U + R3G Al j Fi U)) ≤
      ENNReal.ofReal (A ^ nb (j + 1) U) * n1.nrm (R1G Al j Fi U + R2G Al j Fi U + R3G Al j Fi U) := by
    rw [wnormO, hn1e]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (pow_le_pow_right₀ hA1 (Nat.sub_le _ _)))
      (nrmj_πobs_le _ _)
  refine hw.trans (hR.trans ((ENNReal.ofReal_le_ofReal hfin).trans ?_))
  rw [quadO, hvb, hvo, hkb, hko, ← ENNReal.ofReal_add hvb0 hkb0,
    ← ENNReal.ofReal_add (by positivity) hko0, ← ENNReal.ofReal_add hvb0 hvo0,
    ← ENNReal.ofReal_add (by positivity) hkb0, ← ENNReal.ofReal_add (by positivity) hko0,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hK2 : K₂ ≤ (L : ℝ) ^ (2 * d) := by
    rw [hK₂, ← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le hL1r ?_
    push_cast; linarith
  have hK22 : K₂ ^ 2 ≤ (L : ℝ) ^ (4 * d) := by
    calc K₂ ^ 2 ≤ ((L : ℝ) ^ (2 * d)) ^ 2 := by gcongr
      _ = (L : ℝ) ^ (4 * d) := by rw [← pow_mul]; ring_nf
  exact r_final hCf0 (by positivity) hCv1 hK0.le hK22 hvb0 hkb0 hvo0 hko0

end

end Obs
