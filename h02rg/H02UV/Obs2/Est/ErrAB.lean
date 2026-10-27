import Obs2.Flow.MuChainAB
import Obs2.Pair.AnchAB
import Obs2.Loc.PauliLip
import Obs.FlowObsCoeff

/-!
# The pieces of `errAB` that do not need the `ab` step chain (`w_{ab} > 0`)

On anchored inputs (`OAnchS`: the `ab` parts of `V(B)`, `𝒲(B)`, `K(Y)` vanish unless `B`, `Y`
meet `{a, b}`):

* **`farABm_eq_zero_of_anch`**: `farABm = 0` exactly (every `S(B)` is anchored at `B`, and a
  `(j+1)`-block not meeting `{a,b}` contains no `j`-block meeting `{a,b}`);
* `norm_sum_two_le`, `eq_blk_of_inter`: a sum over blocks of terms vanishing off the blocks of `a`
  and `b` has at most two terms;
* **`norm_wTadAB0_le`**: `|wTadAB_k(0)| = |∑_Bm₂(𝒲(B)_{ab})| ≤ 2ℓ^{-2}w̄` if
  `‖𝒲(B)_{ab}‖_{T_k(ℓ)} ≤ w̄`;
* `norm_mass2_expLC_le` (`|m₂(e^{ℒ_C}F)| ≤ Q₁ℓ^{-2}‖F‖_{T_j(ℓ)}`, `F` local at a block) and
  **`norm_qAB_le`**: `|qAB| ≤ 2Q₁ℓ^{-2}q̄` if `‖Q(B)_{ab}‖_{T_j(ℓ)} ≤ q̄`;
* **`norm_pauliDef2_le`** (`pauli_lip_loc` with `I = ∅`): `|𝔡₂_C(F)| = |m₂(e^{ℒ_C}F) - m₂(F)| ≤
  σ^{-2}(locC(R, γ, h)/(2σ)²)‖F‖_{T_k(4σ)}` for `F` supported in a box of radius `R ≥ L^k` and `C`
  with a Gram representation of range `h ≥ R`; **`norm_pdefM2_le`**: `|𝔡₂| ≤ 2·(…)·v̄` on anchored
  `V` (at most two blocks);
* **`norm_errAB_le`**: `‖errAB_k‖ ≤ |qAB| + |wTadAB(0)| + |𝔡₂||1 - n_a| + |m₂F_C(D, V'_∅)| +
  ∑_{j₀≤i<k}|memAB i k|` when `farABm_k = 0`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD ENNReal

variable {d L N : ℕ} [NeZero L]

/-! ### Sums supported on two blocks -/

theorem norm_sum_two_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℂ) (x y : ι)
    {M : ℝ} (hM : 0 ≤ M) (hz : ∀ i ∈ s, i ≠ x → i ≠ y → f i = 0) (hb : ∀ i ∈ s, ‖f i‖ ≤ M) :
    ‖∑ i ∈ s, f i‖ ≤ 2 * M := by
  have e : ∑ i ∈ s, f i = ∑ i ∈ s.filter (fun i => i = x ∨ i = y), f i := by
    refine (sum_subset (filter_subset _ _) fun i hi hi' => ?_).symm
    rw [mem_filter, not_and_or] at hi'
    rcases hi' with h | h
    · exact absurd hi h
    · exact hz i hi (fun e => h (Or.inl e)) (fun e => h (Or.inr e))
  rw [e]
  have hc : (s.filter (fun i => i = x ∨ i = y)).card ≤ 2 := by
    refine (card_le_card (t := {x, y}) fun i hi => ?_).trans card_le_two
    rcases (mem_filter.1 hi).2 with rfl | rfl <;> simp
  calc ‖∑ i ∈ s.filter (fun i => i = x ∨ i = y), f i‖
      ≤ ∑ i ∈ s.filter (fun i => i = x ∨ i = y), ‖f i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ s.filter (fun i => i = x ∨ i = y), M :=
        sum_le_sum fun i hi => hb i (mem_filter.1 hi).1
    _ = (s.filter (fun i => i = x ∨ i = y)).card * M := by rw [sum_const, nsmul_eq_mul]
    _ ≤ 2 * M := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hM

theorem eq_blk_of_inter (P : ObsPts d L N) {k : ℕ} {b : Fin d → ℕ}
    (h : (blockSet (L := L) (N := N) k b ∩ P.pts).Nonempty) : b = blk k P.a ∨ b = blk k P.b := by
  obtain ⟨z, hz⟩ := h
  rw [mem_inter, ObsPts.pts, mem_insert, mem_singleton] at hz
  have hb := (mem_blockSet.1 hz.1)
  rcases hz.2 with rfl | rfl
  · exact Or.inl hb.symm
  · exact Or.inr hb.symm

theorem ab_eq_zero_of_anch (P : ObsPts d L N) {k : ℕ} {b : Fin d → ℕ} {c : Obs.Case}
    {F : OE c (Lam d L N)}
    (hF : F ∈ (anc P (blockSet (L := L) (N := N) k b) : Subalgebra ℂ (OE c (Lam d L N))))
    (h1 : b ≠ blk k P.a) (h2 : b ≠ blk k P.b) : (F : SA c (Lam d L N)).ab = 0 :=
  hF.2.2 fun hne => (eq_blk_of_inter P hne).elim h1 h2

/-! ### `farABm` -/

/-- **`farABm = 0` on anchored inputs.** -/
theorem farABm_eq_zero_of_anch {P : ObsPts d L N} {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℂ}
    {V W : OFam .two d L N} {K : OAct .two d L N} (H : OAnchS P j V W K) :
    farABm P j C V W = 0 := by
  unfold farABm
  refine sum_eq_zero fun c' _ => ?_
  split_ifs with h
  · rfl
  · rw [SXO, AddSubmonoidClass.coe_finsetSum, SA.sum_ab, mass2_sum]
    refine sum_eq_zero fun b hb => ?_
    have hsub : blockSet (L := L) (N := N) j b ⊆ blockSet (L := L) (N := N) (j + 1) c' :=
      blockSet_subset_of_mem_blocks (IsPolymer.of_succ (isPolymer_blockSet (j + 1) c')) hb
    rw [(H.Sb_anch (C := C) b).2.2 fun hne => h (hne.mono (inter_subset_inter_right hsub)),
      mass2_zero]

/-! ### `wTadAB(0)` and `qAB` -/

/-- **`|wTadAB_k(0)| ≤ 2ℓ^{-2}w̄`** on anchored `𝒲`. -/
theorem norm_wTadAB0_le (P : ObsPts d L N) {k : ℕ} {W : OFam .two d L N}
    (hW : ∀ b, W b ∈ (anc P (blockSet (L := L) (N := N) k b) :
      Subalgebra ℂ (OE .two (Lam d L N))))
    {ℓ w : ℝ} (hℓ : 0 < ℓ) (hw : 0 ≤ w)
    (hWb : ∀ b, Tj d (L : ℝ) k ℓ (W b : SA .two (Lam d L N)).ab ≤ ENNReal.ofReal w) :
    ‖wTadAB k W 0‖ ≤ 2 * (w * ℓ⁻¹ ^ 2) := by
  unfold wTadAB
  simp only [expLC_zero]
  refine norm_sum_two_le _ _ (blk k P.a) (blk k P.b) (by positivity)
    (fun b _ h1 h2 => by rw [ab_eq_zero_of_anch P (hW b) h1 h2, mass2_zero]) fun b _ => ?_
  refine (norm_mass2_le hℓ k _).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hWb b)
  rwa [ENNReal.toReal_ofReal hw] at this

/-- `|m₂(e^{ℒ_C}F)| ≤ Q₁ℓ^{-2}‖F‖_{T_j(ℓ)}` for `F ∈ 𝒩(B^□)`, `GoodCov2 j ℓ C`. -/
theorem norm_mass2_expLC_le (hd : 1 ≤ d) (hL : pauliL0 d ≤ L) {j : ℕ} (hj : j < N) {ℓ : ℝ}
    (hℓ : 0 < ℓ) {C : Matrix (Lam d L N) (Lam d L N) ℂ} (hC : GoodCov2 j ℓ C) {b : Fin d → ℕ}
    {F : Alg d L N} (hF : F ∈ NX (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N))) :
    ‖mass2 (expLC C F)‖ ≤ Q1 d * (Tj d (L : ℝ) j ℓ F).toReal * ℓ⁻¹ ^ 2 := by
  have h1 := norm_mass2_le hℓ (j + 1) (expLC C F)
  have h2 := EthE_succ_le hd hL hj hℓ hC hF
  rw [ECC_theta] at h2
  have h3 : ENNReal.ofReal (pq d ^ nb j (nbhd j (blockSet (L := L) (N := N) j b))) *
      Tj d (L : ℝ) j ℓ F ≤ ENNReal.ofReal (Q1 d) * Tj d (L : ℝ) j ℓ F :=
    mul_le_mul_left (ENNReal.ofReal_le_ofReal (pq_pow_le_Q1 hd hj.le b)) _
  have h4 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (tNorm_ne_top (pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) j) hℓ F))
    (h2.trans h3)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by have := one_le_Q1 hd; linarith)] at h4
  exact h1.trans (mul_le_mul_of_nonneg_right h4 (by positivity))

/-- **`|qAB| ≤ 2Q₁ℓ^{-2}q̄`** on anchored `K`, with `‖Q(B)_{ab}‖_{T_j(ℓ)} ≤ q̄`. -/
theorem norm_qAB_le (hd : 1 ≤ d) (hL : pauliL0 d ≤ L) (P : ObsPts d L N) {j : ℕ} (hj : j < N)
    {C : Matrix (Lam d L N) (Lam d L N) ℂ} {ℓ q : ℝ} (hℓ : 0 < ℓ) (hq : 0 ≤ q)
    (hC : GoodCov2 j ℓ C) {V W : OFam .two d L N} {K : OAct .two d L N} (H : OAnchS P j V W K)
    (hloc : ∀ b, (Q2O P j K b : SA .two (Lam d L N)).ab ∈
      NX (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N)))
    (hQ : ∀ b, Tj d (L : ℝ) j ℓ (Q2O P j K b : SA .two (Lam d L N)).ab ≤ ENNReal.ofReal q) :
    ‖qAB P j C K‖ ≤ 2 * (Q1 d * q * ℓ⁻¹ ^ 2) := by
  unfold qAB
  have hQ1 := one_le_Q1 hd
  refine norm_sum_two_le _ _ (blk j P.a) (blk j P.b) (by positivity)
    (fun b _ h1 h2 => by
      rw [ab_eq_zero_of_anch P (H.Q2O_anch b) h1 h2, map_zero, mass2_zero])
    fun b _ => ?_
  refine (norm_mass2_expLC_le hd hL hj hℓ hC (hloc b)).trans ?_
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hQ b)
  rw [ENNReal.toReal_ofReal hq] at this
  gcongr

/-! ### The Pauli defect `𝔡₂` -/

/-! ### The error -/

/-- **The triangle inequality for `errAB`** when `farABm_k = 0`. -/
theorem norm_errAB_le (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : ℕ → OFam .two d L N) (K : ℕ → OAct .two d L N) (j0 k : ℕ)
    (hf : farABm P k (C k) (V k) (W k) = 0) :
    ‖errAB P C V W K j0 k‖ ≤ ‖qAB P k (C k) (K k)‖ + ‖wTadAB k (W k) 0‖ +
      ‖pdefM2 k (C k) (V k)‖ * ‖1 - nA2 P k (C k) (V k)‖ +
      ‖mass2 (FC (C k) (dAB P k (C k) (V k)) (VprLO k (C k) (V k) : SA .two (Lam d L N)).e)‖ +
      ∑ i ∈ Ico j0 k, ‖memAB P C V W i k‖ := by
  unfold errAB
  rw [hf, sub_zero]
  refine (norm_add_le _ _).trans (add_le_add ?_ (norm_sum_le _ _))
  refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
  refine (norm_sub_le _ _).trans (add_le_add ?_ (norm_mul _ _).le)
  exact norm_add_le _ _

end

end Obs2
