import Step.Deriv
import Step.FRDCov
import Loc.EstCoef
import Grassmann.NablaRec

/-!
# The coupling constants along the flow (Section `sec:flow`, `eq:tildeflow`–`eq:flow2`)

* `cov_bounds`: `|C_{j+1}(0,0)| ≤ K L^{-(d-2)j}` and `|C_{j+1}(0,e) - C_{j+1}(0,0)| ≤ K L^{-dj}`
  (the latter is a second difference by symmetry), uniformly in `m² ≥ 0`; these give the bounds
  on the rescaled coefficients `κ̂_j`.
* `uVnext_V`: for `K = 0`, `V_{j+1} = V + W(V)` with `W(V) = (b(c₀-c₁), -b c₀, 2d b(c₁-c₀), 0)`
  (`eq:tildeflow`, from the Wick formula `EC_theta_eval_eq`).
* `uVnext_K`: for `V = 0`, `V_{j+1} = -W_Q(K)` where `W_Q(K)` is read off from the coefficients of
  `Loc`; in particular its `b`-component vanishes (`Loc` produces no quartic terms), so that
  `b_{j+1} = b_j` exactly.
* `uVnext_K_bounds`: `|z|, |y| ≤ C ℓ₀^{-2} ‖K‖_j`, `|a| ≤ C ℓ₀^{-2} L^{-2j} ‖K‖_j` for `W_Q(K)`.
* `Vnorm_le_coef`: `‖V‖_j ≤ d (ℓ₀² + ℓ₀⁴) (|z| + |y| + L^{2j} |a| + L^{-(d-2)j} |b|)`.
-/

namespace Flow

noncomputable section

open Finset Grassmann Loc FRD Step

variable {d L : ℕ} [NeZero L]

/-! ### Covariance bounds -/

theorem nabC_zero_zero {n : ℕ} [NeZero n] (C : Matrix (Torus d n) (Torus d n) ℝ) (x y : Torus d n) :
    nabC C (0 : Dir d → ℕ) 0 x y = C x y := by
  unfold nabC
  have e : (![0, 0] : Fin 2 → Dir d → ℕ) = 0 := by
    funext i; fin_cases i <;> rfl
  rw [e, nabla_zero _ (fun y => zero_vadd _ y)]
  rfl

theorem nabC_second {n : ℕ} [NeZero n] (C : Matrix (Torus d n) (Torus d n) ℝ) (i : Fin d)
    (x y : Torus d n) :
    nabC C 0 (Pi.single (Sum.inl i) 1 + Pi.single (Sum.inr i) 1) x y =
      C x (y + dirVec (Sum.inr i) + dirVec (Sum.inl i)) - C x (y + dirVec (Sum.inl i)) -
        (C x (y + dirVec (Sum.inr i)) - C x y) := by
  unfold nabC
  have hsa : ∀ (b b' : Dir d → ℕ) (y : Torus d n), (b + b') +ᵥ y = b +ᵥ (b' +ᵥ y) :=
    fun b b' y => add_vadd b b' y
  have e : (![0, Pi.single (Sum.inl i) 1 + Pi.single (Sum.inr i) 1] : Fin 2 → Dir d → ℕ) =
      (Pi.single 1 (Pi.single (Sum.inr i) 1) : Fin 2 → Dir d → ℕ) +
        Pi.single 1 (Pi.single (Sum.inl i) 1) := by
    funext k; fin_cases k
    · simp
    · simp [add_comm]
  rw [e, nabla_succ _ hsa, nabla_single _ (fun y => zero_vadd _ y) hsa]
  simp only [ediff, single_vadd]
  simp [Function.update]
  ring

/-- **Covariance bounds** for the rescaled coefficients `κ̂_j`: `|C_{j+1}(0,0)| ≤ K L^{-(d-2)j}`
and `|C_{j+1}(0,e) - C_{j+1}(0,0)| ≤ K L^{-dj}`, uniformly in `m² ≥ 0`. -/
theorem cov_bounds (hd : 3 ≤ d) : ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ (L : ℕ) [NeZero L] (N j : ℕ),
    j + 1 ≤ N → ∀ msq : ℝ, 0 ≤ msq →
    |Cfrd d L N msq j 0 0| ≤ Kc * (L : ℝ) ^ (-(((d : ℝ) - 2) * j)) ∧
    ∀ e : Dir d, |Cfrd d L N msq j 0 (dirVec e) - Cfrd d L N msq j 0 0| ≤
      Kc * (L : ℝ) ^ (-((d : ℝ) * j)) := by
  obtain ⟨K, hK⟩ := Cj_bound stdPt hd 0 le_rfl 2
  refine ⟨max K 0, le_max_right _ _, fun L _ N j hj msq hmsq => ?_⟩
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast NeZero.one_le
  have hLn : (L : ℝ) ^ (j + 1) ≤ ((L ^ N : ℕ) : ℝ) := by
    push_cast; exact pow_le_pow_right₀ hL1 hj
  have hd6 : (6 : ℝ) ≤ 2 * d + msq := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hfac : K * ((2 * (d : ℝ) + msq)⁻¹ *
      (1 + msq * (L : ℝ) ^ (2 * j) / (2 * d + msq)) ^ (-(0 : ℝ))) ≤ max K 0 := by
    rw [neg_zero, Real.rpow_zero, mul_one]
    have h1 : (2 * (d : ℝ) + msq)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    have h0 : 0 ≤ (2 * (d : ℝ) + msq)⁻¹ := by positivity
    calc K * (2 * (d : ℝ) + msq)⁻¹ ≤ max K 0 * (2 * (d : ℝ) + msq)⁻¹ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) h0
      _ ≤ max K 0 * 1 := mul_le_mul_of_nonneg_left h1 (le_max_right _ _)
      _ = max K 0 := mul_one _
  have hpos : ∀ t : ℝ, 0 ≤ (L : ℝ) ^ t := fun t => Real.rpow_nonneg (by linarith) t
  have hC := hinv_frd (d := d) (L := L) (N := N) j msq hmsq
  have hCs := hsym_frd (d := d) (L := L) (N := N) j msq hmsq
  constructor
  · have h := hK (L ^ N) (L : ℝ) hL1 j hLn msq hmsq 0 0 (by simp [Grassmann.mabs]) (by simp [Grassmann.mabs]) 0 0
    rw [nabC_zero_zero] at h
    simp only [Grassmann.mabs, Pi.zero_apply, sum_const_zero, CharP.cast_eq_zero, add_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_right hfac (hpos _))
  · intro e
    obtain ⟨i⟩ : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    have hm : Grassmann.mabs (Pi.single (Sum.inl i) 1 + Pi.single (Sum.inr i) 1 : Dir d → ℕ) = 2 := by
      simp [Grassmann.mabs, sum_add_distrib]
    have h := hK (L ^ N) (L : ℝ) hL1 j hLn msq hmsq 0 _ (by simp [Grassmann.mabs]) hm.le 0 0
    rw [nabC_second, hm] at h
    have e1 : (0 : Lam d L N) + dirVec (Sum.inr i) + dirVec (Sum.inl i) = 0 := by
      rw [zero_add, dirVec_inr_eq, neg_add_cancel]
    have hdir : ∀ e', Cj stdPt msq (L : ℝ) (j + 1) (0 : Lam d L N) (dirVec e') =
        Cj stdPt msq (L : ℝ) (j + 1) (0 : Lam d L N) (dirVec e) := fun e' => hC.dir hCs e' e
    rw [e1, zero_add, zero_add, hdir (Sum.inl i), hdir (Sum.inr i)] at h
    show |Cj stdPt msq (L : ℝ) (j + 1) (0 : Lam d L N) (dirVec e) -
      Cj stdPt msq (L : ℝ) (j + 1) (0 : Lam d L N) 0| ≤ _
    simp only [Grassmann.mabs, Pi.zero_apply, sum_const_zero, CharP.cast_eq_zero] at h
    set c0 := Cj stdPt msq (L : ℝ) (j + 1) (0 : Lam d L N) 0
    set c1 := Cj stdPt msq (L : ℝ) (j + 1) (0 : Lam d L N) (dirVec e)
    have e2 : c0 - c1 - (c1 - c0) = -2 * (c1 - c0) := by ring
    rw [e2, abs_mul, show |(-2 : ℝ)| = 2 by norm_num, show ((2 : ℕ) : ℝ) = 2 by norm_num,
      show ((d : ℝ) - 2 + 0 + 2) = d by ring] at h
    have h3 := h.trans (mul_le_mul_of_nonneg_right hfac (hpos _))
    have h4 : 0 ≤ |c1 - c0| := abs_nonneg _
    have h5 : 0 ≤ max K 0 * (L : ℝ) ^ (-((d : ℝ) * j)) := mul_nonneg (le_max_right _ _) (hpos _)
    linarith

/-! ### The coupling constants for `K = 0` -/

variable {N : ℕ}

open Coup

theorem Qb_zero (j : ℕ) (b : Fin d → ℕ) : Qb j (0 : Act d L N) b = 0 := by
  have := Qb_lin j (0 : Act d L N) 0 0 0 b
  simpa using this

theorem three_le_pow (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (N : ℕ) (hN : 1 ≤ N) : 3 ≤ L ^ N :=
  (three_le_L hd hL).trans (Nat.le_self_pow (by omega) L)

/-- **`eq:tildeflow`**: for `K = 0` the coupling constants are those of `𝔼_C θ V(B)`,
`V_{j+1} = V + W(V)` with `W(V) = (b(c₀-c₁), -b c₀, 2d b(c₁-c₀), 0)`. -/
theorem uVnext_V (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {j : ℕ} (hj : j < N)
    {C : Matrix (Lam d L N) (Lam d L N) ℝ} (hC : CovInv C) (hCs : ∀ x y, C x y = C y x)
    (e : Dir d) (V : Vcoup) :
    (uVnext j C V 0).2 = Vlin 1 1 V (Wf d (C 0 0 : ℂ) (C 0 (dirVec e) : ℂ) V) := by
  have h1 := uVnext_spec hd hL hj hC hCs V (InK.zero j) (zero_mem_blockIdx (L := L) (N := N) j)
  rw [Qb_zero, Subalgebra.coe_zero, sub_zero] at h1
  have h2 := EC_theta_eval_eq hC hCs (C 0 (dirVec e)) (fun e' => hC.dir hCs e' e) V
    (blockSet (L := L) (N := N) j 0)
  have h3 := coup_injective hd (three_le_pow hd hL N (by omega))
    (mem_blockIdx.1 (zero_mem_blockIdx (L := L) (N := N) j)) (patch_blockSet hj (three_le_L hd hL) 0)
    (h1.symm.trans h2)
  exact h3.2

/-! ### The coupling constants produced by `Loc` -/

/-- The explicit form of a local polynomial with symmetric coefficients
(`mem_VXspace_of_symCoef` with the witness made explicit). -/
theorem symCoef_eval (i₀ : Fin d) {B : Finset (Lam d L N)} (hne : B.Nonempty) (κ : ℂ)
    {C : Mono d → ℂ} (hC : SymCoef C) :
    κ • (1 : Alg d L N) + ∑ M, C M • monoSet M B =
      (κ / B.card * B.card) • (1 : Alg d L N) +
        (⟨-2 * C (.a2 s(i₀, i₀)), C (.m2 i₀ i₀), C .c, 0⟩ : Vcoup).eval B := by
  have hcard : (B.card : ℂ) ≠ 0 := by exact_mod_cast hne.card_pos.ne'
  rw [div_mul_cancel₀ _ hcard, sum_mono]
  have h1 : ∑ i, C (.a1 i) • monoSet (.a1 i) B = 0 :=
    sum_eq_zero fun i _ => by rw [hC.odd (i := i) (by simp [cnt]), zero_smul]
  have h2 : ∑ i, C (.b1 i) • monoSet (.b1 i) B = 0 :=
    sum_eq_zero fun i _ => by rw [hC.odd (i := i) (by simp [cnt]), zero_smul]
  have h3 : ∑ s, C (.a2 s) • monoSet (.a2 s) B =
      ∑ i, C (.a2 s(i₀, i₀)) • monoSet (.a2 s(i, i)) B := by
    rw [sum_sym2_diag]
    · exact sum_congr rfl fun i _ => by rw [hC.a2 i i₀]
    · intro s hs
      induction s using Sym2.ind with
      | h i k =>
        have hik : k ≠ i := fun h => hs (by simp [h])
        rw [hC.odd (cnt_self i hik).2.1, zero_smul]
  have h4 : ∑ s, C (.b2 s) • monoSet (.b2 s) B =
      ∑ i, C (.a2 s(i₀, i₀)) • monoSet (.b2 s(i, i)) B := by
    rw [sum_sym2_diag]
    · exact sum_congr rfl fun i _ => by rw [hC.b2 i i₀]
    · intro s hs
      induction s using Sym2.ind with
      | h i k =>
        have hik : k ≠ i := fun h => hs (by simp [h])
        rw [hC.odd (cnt_self i hik).2.2, zero_smul]
  have h5 : ∑ i, ∑ k, C (.m2 i k) • monoSet (.m2 i k) B =
      ∑ i, C (.m2 i₀ i₀) • monoSet (.m2 i i) B := by
    refine sum_congr rfl fun i _ => ?_
    rw [sum_eq_single i, hC.m2 i i₀]
    · intro k _ hik; rw [hC.odd (cnt_self i hik).1, zero_smul]
    · simp
  rw [h1, h2, h3, h4, h5, add_zero, add_zero]
  simp only [← smul_sum, monoSet]
  rw [sum_comm (s := univ) (t := B), sum_comm (s := univ) (t := B), sum_comm (s := univ) (t := B)]
  simp only [sum_monoAt_a2, sum_monoAt_b2, sum_monoAt_m2, monoAt_c, Vcoup.eval, sum_add_distrib,
    zero_smul, add_zero, ← smul_sum]
  simp only [neg_mul, mul_neg, sum_neg_distrib]
  module

open Classical in
/-- The coefficients `c_M(Q(B_0)) = ∑_{X ∈ 𝒮_j, X ⊇ B_0} c_M(K(X))` of `Q(B_0)`. -/
def cQ (j : ℕ) (K : Act d L N) (M : Mono d) : ℂ :=
  ∑ X ∈ (smallSets j).filter (fun X => blockSet j (0 : Fin d → ℕ) ⊆ X),
    locCoef X (K X : Alg d L N) M

/-- The coupling constants of `Q(B_0)`. -/
def WQ (i₀ : Fin d) (j : ℕ) (K : Act d L N) : Vcoup :=
  ⟨-2 * cQ j K (.a2 s(i₀, i₀)), cQ j K (.m2 i₀ i₀), cQ j K .c, 0⟩

/-- `Q(B_0) = κ + W_Q(K)(B_0)`. -/
theorem Qb_rep (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {j : ℕ} (hj : j + 1 < N) {K : Act d L N}
    (hK : InK j K) (i₀ : Fin d) : ∃ κ : ℂ,
    (Qb j K 0 : Alg d L N) = κ • (1 : Alg d L N) + (WQ i₀ j K).eval (blockSet j 0) := by
  classical
  have hb := zero_mem_blockIdx (d := d) (L := L) (N := N) j
  set B := blockSet (L := L) (N := N) j (0 : Fin d → ℕ) with hBdef
  set S := (smallSets (L := L) (N := N) j).filter (fun X => B ⊆ X) with hSdef
  have hjN : j ≤ N := by omega
  have hne : B.Nonempty := mem_blockIdx.1 hb
  have h3 := three_le_L hd hL
  have key : ∀ T : AffAut d L N, IsGen T → PresBlocks j T → T.img B = B →
      autAlg T.E (∑ X ∈ S, LocXY X B (K X : Alg d L N)) = ∑ X ∈ S, LocXY X B (K X : Alg d L N) := by
    intro T hT hP hTB
    have := Qb_img hd hL hK hT hP hTB
    simp only [Qb_coe, if_pos hj] at this
    exact this
  have hG : ∑ X ∈ S, LocXY X B (K X : Alg d L N) =
      (∑ X ∈ S, ε (K X : Alg d L N) * B.card / X.card) • (1 : Alg d L N) +
        ∑ M, cQ j K M • monoSet M B := by
    simp only [LocXY, sum_add_distrib, sum_smul, cQ]
    rw [sum_comm]
  have hJ : Jsym (∑ X ∈ S, LocXY X B (K X : Alg d L N)) = ∑ X ∈ S, LocXY X B (K X : Alg d L N) := by
    rw [map_sum]
    refine sum_congr rfl fun X hX => ?_
    have hXs := (mem_smallSets_filter.1 hX).1
    rw [← LocXY_Jsym (patch_small hd hL hj hXs) hXs.2.1.1,
      hK.jinv X ⟨hXs.1, hXs.2.1⟩]
  have hR := fun i => key _ (isGen_reflCenter j 0 i) (presBlocks_reflCenter hjN hb i)
    (reflCenter_img hjN 0 i)
  have hP := fun σ => key _ (isGen_permCorner j 0 σ) (presBlocks_permCorner hjN hb σ)
    (permCorner_img hjN 0 σ)
  rw [hG] at hR hP hJ
  have hsym := symCoef_of_inv' hjN (patch_blockSet (by omega) h3 0) hne _ _ hR hP hJ
  refine ⟨(∑ X ∈ S, ε (K X : Alg d L N) * B.card / X.card) / B.card * B.card, ?_⟩
  rw [Qb_coe, if_pos hj, hG, symCoef_eval i₀ hne _ hsym]
  rfl

theorem Wf_b_zero (c0 c1 : ℂ) {W : Vcoup} (hW : W.b = 0) : Wf d c0 c1 W = 0 := by
  unfold Wf; rw [hW]; exact Vcoup.ext' (by simp) (by simp) (by simp) (by simp)

theorem eval_zero' (X : Finset (Lam d L N)) : (0 : Vcoup).eval X = 0 := by
  simpa using eval_smul (0 : ℂ) (0 : Vcoup) X

theorem eval_neg' (V : Vcoup) (X : Finset (Lam d L N)) : (-V).eval X = -V.eval X := by
  have := eval_smul (-1 : ℂ) V X
  rw [neg_one_smul, neg_one_smul] at this
  exact this

/-- **The coupling constants produced by `Loc`**: for `V = 0`, `V_{j+1} = -W_Q(K)`; in
particular `b_{j+1} = 0`. -/
theorem uVnext_K (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {j : ℕ} (hj : j + 1 < N)
    {C : Matrix (Lam d L N) (Lam d L N) ℝ} (hC : CovInv C) (hCs : ∀ x y, C x y = C y x)
    {K : Act d L N} (hK : InK j K) (i₀ : Fin d) :
    (uVnext j C 0 K).2 = -WQ i₀ j K := by
  obtain ⟨κ, hQ⟩ := Qb_rep hd hL hj hK i₀
  set B := blockSet (L := L) (N := N) j (0 : Fin d → ℕ) with hBdef
  have hne : B.Nonempty := mem_blockIdx.1 (zero_mem_blockIdx (d := d) (L := L) (N := N) j)
  have hcard : (B.card : ℂ) ≠ 0 := by exact_mod_cast hne.card_pos.ne'
  have h1 := uVnext_spec hd hL (by omega) hC hCs 0 hK (zero_mem_blockIdx (L := L) (N := N) j)
  obtain ⟨e⟩ : Nonempty (Dir d) := ⟨Sum.inl i₀⟩
  have h2 := EC_theta_eval_eq hC hCs (C 0 (dirVec e)) (fun e' => hC.dir hCs e' e) (WQ i₀ j K) B
  rw [Wf_b_zero _ _ rfl] at h2
  have hV : Vlin 1 1 (WQ i₀ j K) 0 = WQ i₀ j K :=
    Vcoup.ext' (by simp [Vlin]) (by simp [Vlin]) (by simp [Vlin]) (by simp [Vlin])
  rw [hV] at h2
  rw [eval_zero', zero_sub, hQ] at h1
  simp only [map_neg, _root_.map_add, _root_.map_smul, map_one, EC_one, h2] at h1
  have h4 : ∀ u : ℂ, -(κ • (1 : Alg d L N) + ((u * B.card) • (1 : Alg d L N) +
      (WQ i₀ j K).eval B)) =
      ((-(κ / B.card) - u) * B.card) • (1 : Alg d L N) + (-WQ i₀ j K).eval B := by
    intro u
    rw [eval_neg', sub_mul, neg_mul, div_mul_cancel₀ _ hcard]
    module
  rw [h4] at h1
  exact (coup_injective hd (three_le_pow hd hL N (by omega)) hne
    (patch_blockSet (by omega) (three_le_L hd hL) 0) h1.symm).2

/-! ### Scale factors -/

theorem ellj_sq (hd : 2 ≤ d) (ℓ₀ : ℝ) (j : ℕ) :
    ellj d L ℓ₀ j ^ 2 = ℓ₀ ^ 2 / (L : ℝ) ^ ((d - 2) * j) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  unfold ellj
  rw [mul_pow, ← Real.rpow_natCast (L ^ (-((d : ℝ) - 2) * j / 2) : ℝ) 2,
    ← Real.rpow_mul hL0.le, div_eq_mul_inv (ℓ₀ ^ 2), ← Real.rpow_natCast (L : ℝ) ((d - 2) * j),
    ← Real.rpow_neg hL0.le]
  congr 2
  push_cast [Nat.cast_sub hd]
  ring

theorem pow_jd (hd : 2 ≤ d) (j : ℕ) :
    (L : ℝ) ^ (j * d) = (L : ℝ) ^ ((d - 2) * j) * ((L : ℝ) ^ j) ^ 2 := by
  rw [← pow_mul, ← pow_add]
  congr 1
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring

/-! ### Bounds on the coupling constants produced by `Loc` -/

/-- `|c_M(Q(B_0))| ≤ C ℓ^{-2} L^{j deg M} ‖K‖_j / L^{jd}`. -/
theorem cQ_bound (hd : 1 ≤ d) : ∃ Cq : ℝ, 0 ≤ Cq ∧ ∀ (L : ℕ) [NeZero L],
    2 ^ (d + 3) + 8 * d < L → ∀ (N j : ℕ), j + 1 < N → ∀ ℓ : ℝ, 0 < ℓ → ∀ A : ℝ, 1 ≤ A →
    ∀ K : Act d L N, InK j K → ∀ M : Mono d,
      ‖cQ j K M‖ ≤ Cq * (ℓ ^ 2)⁻¹ * ((L : ℝ) ^ j) ^ M.deg * (Knorm j ℓ A K).toReal /
        (L : ℝ) ^ (j * d) := by
  classical
  obtain ⟨Cl, hCl0, hCl⟩ := exists_locCoef_bound d hd
  obtain ⟨c, hc⟩ := card_small_containing d
  refine ⟨c * Cl, by positivity, fun L _ hL N j hj ℓ hℓ A hA K hK M => ?_⟩
  have hb := zero_mem_blockIdx (d := d) (L := L) (N := N) j
  set B := blockSet (L := L) (N := N) j (0 : Fin d → ℕ) with hBdef
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hB : (B.card : ℝ) = (L : ℝ) ^ (j * d) := by
    rw [hBdef, card_blockSet (by omega) hb]; push_cast; rfl
  set k := (Knorm j ℓ A K).toReal
  have hk : 0 ≤ k := ENNReal.toReal_nonneg
  set t := Cl * (ℓ ^ 2)⁻¹ * ((L : ℝ) ^ j) ^ M.deg * k / (L : ℝ) ^ (j * d)
  have ht : 0 ≤ t := by positivity
  have hterm : ∀ X ∈ (smallSets (L := L) (N := N) j).filter (fun X => B ⊆ X),
      ‖locCoef X (K X : Alg d L N) M‖ ≤ t := by
    intro X hX
    have hXs := (mem_smallSets_filter.1 hX).1
    have hBX := (mem_smallSets_filter.1 hX).2
    have hc' : IsConn j X := ⟨hXs.1, hXs.2.1⟩
    have h1 := hCl L hL N j (by omega) X hXs _ (hK.loc X hc') ℓ hℓ M
    have hT : (Tj d (L : ℝ) j ℓ (K X : Alg d L N)).toReal ≤ k :=
      ENNReal.toReal_mono (Knorm_ne_top hℓ K) (Tj_le_Knorm hA hc')
    have hX : (L : ℝ) ^ (j * d) ≤ X.card := by
      rw [← hB]; exact_mod_cast card_le_card hBX
    refine h1.trans ?_
    have hpos : (0 : ℝ) < (L : ℝ) ^ (j * d) := by positivity
    rw [div_le_div_iff₀ (lt_of_lt_of_le hpos hX) hpos]
    have h0 : 0 ≤ Cl * (ℓ ^ 2)⁻¹ * ((L : ℝ) ^ j) ^ M.deg := by positivity
    exact mul_le_mul (mul_le_mul_of_nonneg_left hT h0) hX hpos.le (by positivity)
  unfold cQ
  refine (norm_sum_le _ _).trans ((sum_le_sum hterm).trans ?_)
  rw [sum_const, nsmul_eq_mul]
  have hcard : ((((smallSets (L := L) (N := N) j).filter (fun X => B ⊆ X)).card : ℕ) : ℝ) ≤ c := by
    exact_mod_cast hc L N j 0 hb
  calc (((smallSets (L := L) (N := N) j).filter (fun X => B ⊆ X)).card : ℝ) * t ≤ c * t :=
        mul_le_mul_of_nonneg_right hcard ht
    _ = _ := by simp only [t]; ring

/-- The bounds on the coupling constants `W_Q(K)` produced by `Loc`:
`|z|, |y|, L^{2j} |a| ≤ C ℓ₀^{-2} ‖K‖_j`. -/
theorem WQ_bounds (hd : 3 ≤ d) : ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ (L : ℕ) [NeZero L],
    2 ^ (d + 3) + 8 * d < L → ∀ (N j : ℕ), j + 1 < N → ∀ ℓ₀ : ℝ, 0 < ℓ₀ → ∀ A : ℝ, 1 ≤ A →
    ∀ K : Act d L N, InK j K → ∀ i₀ : Fin d,
      ‖(WQ i₀ j K).z‖ ≤ Cw / ℓ₀ ^ 2 * (Knorm j (ellj d L ℓ₀ j) A K).toReal ∧
      ‖(WQ i₀ j K).y‖ ≤ Cw / ℓ₀ ^ 2 * (Knorm j (ellj d L ℓ₀ j) A K).toReal ∧
      (L : ℝ) ^ (2 * j) * ‖(WQ i₀ j K).a‖ ≤
        Cw / ℓ₀ ^ 2 * (Knorm j (ellj d L ℓ₀ j) A K).toReal := by
  obtain ⟨Cq, hCq0, hCq⟩ := cQ_bound (d := d) (by omega)
  refine ⟨2 * Cq, by positivity, fun L _ hL N j hj ℓ₀ hℓ₀ A hA K hK i₀ => ?_⟩
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hℓ := ellj_pos (d := d) (L := L) (Nat.cast_pos.2 (NeZero.pos L)) hℓ₀ j
  have h := hCq L hL N j hj _ hℓ A hA K hK
  set k := (Knorm j (ellj d L ℓ₀ j) A K).toReal
  have hk : 0 ≤ k := ENNReal.toReal_nonneg
  rw [ellj_sq (d := d) (L := L) (by omega), pow_jd (d := d) (L := L) (by omega) j] at h
  set P := (L : ℝ) ^ ((d - 2) * j) with hP
  set Q := (L : ℝ) ^ j with hQ
  have hP0 : 0 < P := by positivity
  have hQ0 : 0 < Q := by positivity
  have e2 : ∀ M : Mono d, M.deg = 2 →
      Cq * (ℓ₀ ^ 2 / P)⁻¹ * Q ^ M.deg * k / (P * Q ^ 2) = Cq / ℓ₀ ^ 2 * k := by
    intro M hM; rw [hM]; field_simp
  have e0 : Cq * (ℓ₀ ^ 2 / P)⁻¹ * Q ^ (Mono.c : Mono d).deg * k / (P * Q ^ 2) * Q ^ 2 =
      Cq / ℓ₀ ^ 2 * k := by
    simp only [Mono.deg, pow_zero]; field_simp
  have hC0 : 0 ≤ Cq / ℓ₀ ^ 2 * k := by positivity
  refine ⟨?_, ?_, ?_⟩
  · simp only [WQ, norm_mul, norm_neg, RCLike.norm_ofNat]
    have := h (.a2 s(i₀, i₀))
    rw [e2 _ rfl] at this
    calc 2 * ‖cQ j K (.a2 s(i₀, i₀))‖ ≤ 2 * (Cq / ℓ₀ ^ 2 * k) := by linarith
      _ = 2 * Cq / ℓ₀ ^ 2 * k := by ring
  · simp only [WQ]
    have := h (.m2 i₀ i₀)
    rw [e2 _ rfl] at this
    calc ‖cQ j K (.m2 i₀ i₀)‖ ≤ Cq / ℓ₀ ^ 2 * k := this
      _ ≤ 2 * Cq / ℓ₀ ^ 2 * k := by
        have : Cq / ℓ₀ ^ 2 * k ≤ 2 * (Cq / ℓ₀ ^ 2 * k) := by linarith
        linarith [show 2 * Cq / ℓ₀ ^ 2 * k = 2 * (Cq / ℓ₀ ^ 2 * k) by ring]
  · simp only [WQ]
    have := mul_le_mul_of_nonneg_right (h .c) (sq_nonneg Q)
    rw [e0] at this
    rw [pow_mul', ← hQ, mul_comm]
    calc ‖cQ j K .c‖ * Q ^ 2 ≤ Cq / ℓ₀ ^ 2 * k := this
      _ ≤ 2 * Cq / ℓ₀ ^ 2 * k := by
        linarith [show 2 * Cq / ℓ₀ ^ 2 * k = 2 * (Cq / ℓ₀ ^ 2 * k) by ring]

/-! ### Comparison of `‖V‖_j` with the coupling constants -/

theorem tn_sum {X : Type*} [DecidableEq X] [Fintype X] {E : Type*} [Fintype E] [DecidableEq E]
    [AddAction (E → ℕ) X] {p : ℕ} {h ℓ : ℝ} {ι : Type*} (s : Finset ι) (F : ι → Grassmann.N X)
    (t : ι → ℝ) (ht : ∀ i ∈ s, 0 ≤ t i) (hF : ∀ i ∈ s, tNorm E p h ℓ (F i) ≤ ENNReal.ofReal (t i)) :
    tNorm E p h ℓ (∑ i ∈ s, F i) ≤ ENNReal.ofReal (∑ i ∈ s, t i) := by
  refine (tNorm_sum_le _ _).trans ((sum_le_sum hF).trans ?_)
  rw [ENNReal.ofReal_sum_of_nonneg ht]

/-- The constant of `Vnorm_le_coef`. -/
def cV (d : ℕ) (ℓ₀ : ℝ) : ℝ := ((Fintype.card (Mono d) : ℝ) + d) * (ℓ₀ ^ 2 + ℓ₀ ^ 4)

theorem cV_nonneg (d : ℕ) (ℓ₀ : ℝ) : 0 ≤ cV d ℓ₀ := by unfold cV; positivity

theorem norm_cW_le (V : Vcoup) {h : ℝ} (hh : 0 < h) (M : Mono d) :
    ‖cW V M‖ * (h ^ M.deg)⁻¹ ≤ ‖V.a‖ + (‖V.z‖ + ‖V.y‖) * (h ^ 2)⁻¹ := by
  have hz : ‖-(V.z / 2)‖ ≤ ‖V.z‖ := by
    rw [norm_neg, norm_div, RCLike.norm_ofNat]; linarith [norm_nonneg V.z]
  have h2 : 0 ≤ (h ^ 2)⁻¹ := by positivity
  have hza : 0 ≤ ‖V.a‖ := norm_nonneg _
  have hzz : 0 ≤ ‖V.z‖ := norm_nonneg _
  have hyy : 0 ≤ ‖V.y‖ := norm_nonneg _
  cases M with
  | c => simp [cW, Mono.deg]; nlinarith
  | a1 i => simp [cW, Mono.deg]; positivity
  | b1 i => simp [cW, Mono.deg]; positivity
  | a2 s =>
    simp only [cW, Mono.deg]
    split_ifs
    · nlinarith [mul_le_mul_of_nonneg_right hz h2]
    · simp; positivity
  | b2 s =>
    simp only [cW, Mono.deg]
    split_ifs
    · nlinarith [mul_le_mul_of_nonneg_right hz h2]
    · simp; positivity
  | m2 i k =>
    simp only [cW, Mono.deg]
    split_ifs
    · nlinarith
    · simp; positivity

/-- **Comparison of `‖V(B)‖_{T_j(ℓ_j)}` with the coupling constants**:
`‖V(B)‖ ≤ c_V (|z| + |y| + L^{2j} |a| + L^{-(d-2)j} |b|)` for `j`-blocks `B`. -/
theorem Tj_eval_le (hd : 2 ≤ d) {j : ℕ} (hj : j ≤ N) {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) (V : Vcoup)
    {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    Tj d (L : ℝ) j (ellj d L ℓ₀ j) (V.eval (blockSet (L := L) (N := N) j b)) ≤
      ENNReal.ofReal (cV d ℓ₀ * (‖V.z‖ + ‖V.y‖ + (L : ℝ) ^ (2 * j) * ‖V.a‖ +
        ‖V.b‖ / (L : ℝ) ^ ((d - 2) * j))) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set ℓ := ellj d L ℓ₀ j with hℓdef
  have hℓ : 0 < ℓ := ellj_pos hL0 hℓ₀ j
  set B := blockSet (L := L) (N := N) j b with hBdef
  set Q := (L : ℝ) ^ j with hQ
  set P := (L : ℝ) ^ ((d - 2) * j) with hP
  have hQ0 : 0 < Q := by positivity
  have hP0 : 0 < P := by positivity
  have hp2 : 2 ≤ pPhi d := by simp [pPhi]; omega
  have hB : (B.card : ℝ) = P * Q ^ 2 := by
    rw [hBdef, card_blockSet hj hb]; push_cast; exact pow_jd hd j
  have hℓ2 : ℓ ^ 2 = ℓ₀ ^ 2 / P := ellj_sq hd ℓ₀ j
  have hsplit : V = (⟨V.z, V.y, V.a, 0⟩ : Vcoup) + ⟨0, 0, 0, V.b⟩ :=
    Vcoup.ext' (by simp) (by simp) (by simp) (by simp)
  set V₀ : Vcoup := ⟨V.z, V.y, V.a, 0⟩ with hV₀
  set Vb : Vcoup := ⟨0, 0, 0, V.b⟩ with hVb
  set nM : ℝ := (Fintype.card (Mono d) : ℝ)
  -- the quadratic part
  have h1 : Tj d (L : ℝ) j ℓ (V₀.eval B) ≤ ENNReal.ofReal (∑ M : Mono d,
      ‖cW V₀ M‖ * (B.card * (ℓ ^ 2 * (Q ^ M.deg)⁻¹))) := by
    rw [eval_eq_monoSet V₀ rfl]
    refine tn_sum _ _ _ (fun M _ => mul_nonneg (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (sq_nonneg _) (inv_nonneg.2 (pow_nonneg hQ0.le _))))) fun M _ => tn_smul _ ?_
    exact tNorm_monoSet_le hp2 hQ0 hℓ M B
  have h1' : ∑ M : Mono d, ‖cW V₀ M‖ * (B.card * (ℓ ^ 2 * (Q ^ M.deg)⁻¹)) ≤
      nM * (B.card * ℓ ^ 2) * (‖V.a‖ + (‖V.z‖ + ‖V.y‖) * (Q ^ 2)⁻¹) := by
    have : ∀ M : Mono d, ‖cW V₀ M‖ * (B.card * (ℓ ^ 2 * (Q ^ M.deg)⁻¹)) ≤
        (B.card * ℓ ^ 2) * (‖V.a‖ + (‖V.z‖ + ‖V.y‖) * (Q ^ 2)⁻¹) := by
      intro M
      have := norm_cW_le V₀ hQ0 M
      calc ‖cW V₀ M‖ * (B.card * (ℓ ^ 2 * (Q ^ M.deg)⁻¹)) =
          (B.card * ℓ ^ 2) * (‖cW V₀ M‖ * (Q ^ M.deg)⁻¹) := by ring
        _ ≤ (B.card * ℓ ^ 2) * (‖V₀.a‖ + (‖V₀.z‖ + ‖V₀.y‖) * (Q ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left this (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
    refine (sum_le_sum fun M _ => this M).trans (le_of_eq ?_)
    rw [sum_const, card_univ, nsmul_eq_mul]
    ring
  -- the quartic part
  have hgs : ∀ x : Lam d L N, Tj d (L : ℝ) j ℓ (gradSq x) ≤
      ENNReal.ofReal (d * (ℓ ^ 2 * (Q ^ 2)⁻¹)) := by
    intro x
    rw [← sum_monoAt_m2]
    have := tn_sum (E := Dir d) (p := pPhi d) (h := Q) (ℓ := ℓ) univ
      (fun i : Fin d => monoAt (Mono.m2 i i) x) (fun _ => ℓ ^ 2 * (Q ^ 2)⁻¹)
      (fun _ _ => by positivity) (fun i _ => tNorm_monoAt_le hp2 hQ0 hℓ _ x)
    simpa [sum_const, card_univ] using this
  have hpp : ∀ x : Lam d L N, Tj d (L : ℝ) j ℓ (psi x * psibar x) ≤ ENNReal.ofReal (ℓ ^ 2) := by
    intro x
    rw [← monoAt_c]
    simpa [Mono.deg] using tNorm_monoAt_le hp2 hQ0 hℓ (Mono.c : Mono d) x
  have h2 : Tj d (L : ℝ) j ℓ (Vb.eval B) ≤
      ENNReal.ofReal (∑ _x ∈ B, ‖V.b‖ * (ℓ ^ 2 * (d * (ℓ ^ 2 * (Q ^ 2)⁻¹)))) := by
    have e : Vb.eval B = ∑ x ∈ B, V.b • (psi x * psibar x * gradSq x) := by
      rw [hVb]; simp only [Vcoup.eval, zero_smul, zero_div, zero_add]
    rw [e]
    refine tn_sum _ _ _ (fun _ _ => mul_nonneg (norm_nonneg _) (mul_nonneg (sq_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (sq_nonneg _)
        (inv_nonneg.2 (pow_nonneg hQ0.le _)))))) fun x _ => tn_smul _ ?_
    refine (tNorm_mul_le hQ0 hℓ _ _).trans ?_
    rw [ENNReal.ofReal_mul (sq_nonneg _)]
    exact mul_le_mul' (hpp x) (hgs x)
  have hsum := tn_add (E := Dir d) (p := pPhi d) (h := Q) (ℓ := ℓ)
    (sum_nonneg fun M _ => mul_nonneg (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (sq_nonneg _) (inv_nonneg.2 (pow_nonneg hQ0.le _)))))
    (sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (mul_nonneg (sq_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (sq_nonneg _)
        (inv_nonneg.2 (pow_nonneg hQ0.le _)))))) h1 h2
  conv_lhs => rw [hsplit, eval_add]
  refine hsum.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [sum_const, nsmul_eq_mul]
  refine (add_le_add_left h1' _).trans ?_
  rw [hB, hℓ2]
  have hz := norm_nonneg V.z
  have hy := norm_nonneg V.y
  have ha := norm_nonneg V.a
  have hb' := norm_nonneg V.b
  have hnM : 0 ≤ nM := by positivity
  have e1 : nM * (P * Q ^ 2 * (ℓ₀ ^ 2 / P)) * (‖V.a‖ + (‖V.z‖ + ‖V.y‖) * (Q ^ 2)⁻¹) =
      nM * ℓ₀ ^ 2 * (Q ^ 2 * ‖V.a‖ + ‖V.z‖ + ‖V.y‖) := by field_simp; ring
  have e2 : P * Q ^ 2 * (‖V.b‖ * (ℓ₀ ^ 2 / P * (d * (ℓ₀ ^ 2 / P * (Q ^ 2)⁻¹)))) =
      d * ℓ₀ ^ 4 * (‖V.b‖ / P) := by field_simp
  rw [e1, e2, pow_mul', ← hQ]
  unfold cV
  have hbP : 0 ≤ ‖V.b‖ / P := by positivity
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hQa : 0 ≤ Q ^ 2 * ‖V.a‖ := by positivity
  nlinarith [sq_nonneg ℓ₀, pow_nonneg (sq_nonneg ℓ₀) 2, mul_nonneg hnM (sq_nonneg ℓ₀),
    mul_nonneg hd0 (pow_nonneg hℓ₀.le 4), mul_nonneg hnM (pow_nonneg hℓ₀.le 4),
    mul_nonneg hd0 (sq_nonneg ℓ₀)]

/-- `‖V‖_j ≤ c_V (|z| + |y| + L^{2j} |a| + L^{-(d-2)j} |b|)`. -/
theorem Vnorm_le_coef (hd : 2 ≤ d) {j : ℕ} (hj : j ≤ N) {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) (V : Vcoup) :
    Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V ≤
      ENNReal.ofReal (cV d ℓ₀ * (‖V.z‖ + ‖V.y‖ + (L : ℝ) ^ (2 * j) * ‖V.a‖ +
        ‖V.b‖ / (L : ℝ) ^ ((d - 2) * j))) :=
  iSup₂_le fun _ hb => Tj_eval_le hd hj hℓ₀ V hb

end

end Flow
