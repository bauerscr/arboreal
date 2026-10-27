import PtCorr2.Pair.PairVStep4
import PtCorr2.Obs.ObsHistLast
import PtCorr2.Pair.SFirst1

/-!
# The `E`-step sizes (2, trajectory level): small sets at `N_h`, the bulk `V'` near the pair, the
gradient part `dABX` at the next scale

* **`hist_smallK_leL`**: the small-set bound `‖K_{N_h}(X)‖_w ≤ 8k` from the `K'` bound at the top
  scale `j = N_h` (only `ValidAtL R N_h`; copy of the last item of `hist_vstep_facts` with
  `hist_rawL`);
* **`Fnorm_stVf_scale`**: the bulk block bound at field scale `c·s_j` (`c ≥ 1`):
  `‖V_j(B)_∅‖_{T_j(cs_j)} ≤ c⁴(c_Mℓ²(2|μ| + 2η) + 8ℓ⁴g)` (copy of `rg_inputs`, first part);
* **`card_near_le`**: at most `2(L + 39)²` blocks are near `a` or `b` (`card_nearSet_le`);
* **`Tj_VprO_e_le`**: `‖V'_j(B)_∅‖_{T_{j+1}(ℓ')} ≤ ‖V_j(B)_∅‖_{T_j(2ℓ')}` (`GoodCov2 j ℓ₀`,
  `ℓ₀ ≤ ℓ'`);
* **`Tj_dABX_le`**: the `T_{j+1}(ℓ')` size of the gradient part of a region from per-block
  gradient sizes (`gradM4Sz` at `(L^{j+1}, ℓ')`), the per-block `M₄` and the `LopM4` term (only
  the blocks of `a`, `b` contribute);
* **`gradM4Sz_scale_le`**: the scale change `(L^j, s) → (L^{j+1}, ℓ')`, `ℓ' ≤ qs`:
  factor `q⁴/L` (`Obs2.gSzE_scale_le_q`).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

variable {L N : ℕ} [NeZero L]

section Hist

variable {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

set_option maxHeartbeats 1000000 in
/-- **The small-set bound at the top scale `N_h`.** -/
theorem hist_smallK_leL (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS) (hVL : ValidAtL R Nh)
    (hmN : |R.msq| * ((L : ℝ) ^ Nh) ^ 2 ≤ 1)
    (P : ObsPts 2 L N) {j₀ : ℕ} (o₀ : ObsSt .two L N)
    (t : Flow2.Hist.Seq (Xs R)) (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε Nh t)
    (w : Wt) (hw : w.Sub) (k : ℝ)
    (hk : ∀ X, IsConn Nh X → ENNReal.ofReal (R.A ^ (nb Nh X - 2 ^ 2)) *
        oTo w Nh (histS R Nh t) ((obsHistFrom R P j₀ o₀ Nh t).K X) ≤ ENNReal.ofReal k) :
    ∀ X, IsSmall Nh X → oTo w Nh (histS R Nh t) (hKR R P j₀ o₀ t Nh X) ≤ ENNReal.ofReal (8 * k) := by
  obtain ⟨hVc, HI, hg, -, hz, hy, hη, hηs, -, -, -, -, -, -, -, hsℓ, hsℓ'⟩ :=
    hist_rawL R hSB hV hm hβ hδ1 H hVL t ht
  set st := rawHist R Nh t
  obtain ⟨-, hΔ⟩ := rg_inputs R Nh hVc st HI (t Nh).1 (t Nh).2.1 hmN hg _ hz hy hη
  have hM : (0 : ℝ) ≤ cM := Nat.cast_nonneg _
  have hη0 : 0 ≤ cZ R * (t Nh).1 := (norm_nonneg _).trans hz
  intro X hX
  have hA0 : 0 < R.A := Fact.out
  have h1 := oTo_fullK_leAB R Nh st (rawK R st.u (t Nh).2.2) (obsHistFrom R P j₀ o₀ Nh t) w hw hsℓ
    hA0 (by positivity : (0 : ℝ) ≤ 8 * cM * R.ℓ ^ 2 * (cZ R * (t Nh).1)) (by linarith) hΔ X
  have hnb : nb Nh X - 2 ^ 2 = 0 := by
    have := hX.2.2; unfold nb; omega
  rw [hnb, pow_zero, pow_zero, ENNReal.ofReal_one] at h1
  simp only [one_mul] at h1
  have h2 := hk X ⟨hX.1, hX.2.1⟩
  rw [hnb, pow_zero, ENNReal.ofReal_one, one_mul] at h2
  calc oTo w Nh (histS R Nh t) (hKR R P j₀ o₀ t Nh X) ≤ ENNReal.ofReal 8 *
        oTo w Nh (histS R Nh t) ((obsHistFrom R P j₀ o₀ Nh t).K X) := h1
    _ ≤ ENNReal.ofReal 8 * ENNReal.ofReal k := mul_le_mul_right h2 _
    _ = ENNReal.ofReal (8 * k) := by rw [ENNReal.ofReal_mul (by norm_num)]

end Hist

/-! ### The bulk coupling at a larger field scale -/

set_option maxHeartbeats 1000000 in
/-- **The bulk block bound at field scale `c·fscale(Z)ℓ`** (`c ≥ 1`; copy of the first part of
`rg_inputs`). -/
theorem Fnorm_stVf_scale (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (j : ℕ) (hV : ValidCore R j) (st : RawSt 2 L N)
    (H : RawInv R j st) (g μ : ℝ) (hm : |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1) (hg0 : 0 ≤ g)
    (η : ℝ) (hz : ‖st.z / st.Z‖ ≤ η) (hy : ‖st.y / st.Z‖ ≤ η) (hη : 2 * η ≤ R.ρ)
    {c : ℝ} (hc : 1 ≤ c) :
    Fnorm j (fscale st.Z * (c * R.ℓ)) (stVf R j st g μ) ≤
      ENNReal.ofReal (c ^ 4 * (cM * R.ℓ ^ 2 * (2 * |μ| + 2 * η) + 8 * R.ℓ ^ 4 * g)) := by
  have hV' := hV
  obtain ⟨hj1, -, -, hρ0, hρ8, hℓ, -⟩ := hV'
  have hZ : st.Z ≠ 0 := H.Z_ne_zero (by linarith)
  have hη0 : 0 ≤ η := (norm_nonneg _).trans hz
  have hjN : j < N := by omega
  have hzy : ‖(st.z + st.y) / st.Z‖ ≤ R.ρ := by
    rw [add_div]; exact (norm_add_le _ _).trans (by linarith)
  have hyc : ‖st.y / st.Z‖ ≤ R.ρ := by linarith
  have hζ : stZeta R st = (st.z + st.y) / st.Z := by
    unfold stZeta absorbZeta; rw [clampDisk_of_le hzy]
  have hζη : ‖stZeta R st‖ ≤ 2 * η := by
    rw [hζ, add_div]; exact (norm_add_le _ _).trans (by linarith)
  have hgr := norm_stGr_le R j st g μ
  rw [abs_of_nonneg hg0] at hgr
  have hrZ : ‖stZ' R st / st.Z‖ ≤ 9 / 8 := by
    have e : stZ' R st / st.Z = 1 + stZeta R st := by
      unfold stZ'; rw [mul_div_cancel_left₀ _ hZ]
    rw [e]; refine (norm_add_le _ _).trans ?_; rw [norm_one]; linarith
  have hℓ0 : 0 < R.ℓ := Fact.out
  have e : stVf R j st g μ = VfamL j ![0, 0, (μ : ℂ) * stZ' R st / (L : ℂ) ^ (2 * j) -
      stA R st * R.msq, stGr R j st g μ * stZ' R st ^ 2] := stVf_eq hZ hzy hyc
  rw [e]
  refine (Fnorm_VfamL_norm2 j hjN.le (mul_pos (by linarith) hℓ0) hZ _ 0 0 _ _ μ R.msq).trans
    (ENNReal.ofReal_le_ofReal ?_)
  simp only [zero_div, norm_zero, add_zero]
  rw [norm_stA_div hZ]
  have hA : ‖stZeta R st‖ * |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 2 * η := by
    rw [mul_assoc]
    calc ‖stZeta R st‖ * (|R.msq| * ((L : ℝ) ^ j) ^ 2) ≤ 2 * η * 1 := by gcongr
      _ = 2 * η := mul_one _
  have h1 : ‖stZ' R st / st.Z‖ * |μ| ≤ 2 * |μ| := by
    have := mul_le_mul_of_nonneg_right hrZ (abs_nonneg μ); linarith [abs_nonneg μ]
  have h2 : ‖stZ' R st / st.Z‖ ^ 2 * ‖stGr R j st g μ‖ ≤ 2 * g := by
    have hr2 : ‖stZ' R st / st.Z‖ ^ 2 ≤ 81 / 64 := by
      have := norm_nonneg (stZ' R st / st.Z); nlinarith
    calc ‖stZ' R st / st.Z‖ ^ 2 * ‖stGr R j st g μ‖ ≤ 81 / 64 * (8 / 7 * g) := by
          gcongr
      _ ≤ 2 * g := by linarith
  have hM : 0 ≤ cM := Nat.cast_nonneg _
  have hc0 : 0 ≤ c := by linarith
  have hc2 : c ^ 2 ≤ c ^ 4 := pow_le_pow_right₀ hc (by norm_num)
  set A := ‖stZ' R st / st.Z‖ * |μ| + ‖stZeta R st‖ * |R.msq| * ((L : ℝ) ^ j) ^ 2 with hAd
  set G := ‖stZ' R st / st.Z‖ ^ 2 * ‖stGr R j st g μ‖ with hGd
  have hA0 : 0 ≤ A := by positivity
  have hAle : A ≤ 2 * |μ| + 2 * η := by linarith
  have hG0 : 0 ≤ G := by positivity
  have e1 : cM * (c * R.ℓ) ^ 2 * A + 4 * (c * R.ℓ) ^ 4 * G =
      c ^ 2 * (cM * R.ℓ ^ 2 * A) + c ^ 4 * (4 * R.ℓ ^ 4 * G) := by ring
  rw [e1]
  have hX0 : 0 ≤ cM * R.ℓ ^ 2 * A := by positivity
  have k1 : c ^ 2 * (cM * R.ℓ ^ 2 * A) ≤ c ^ 4 * (cM * R.ℓ ^ 2 * (2 * |μ| + 2 * η)) :=
    mul_le_mul hc2 (mul_le_mul_of_nonneg_left hAle (by positivity)) hX0 (by positivity)
  have k2 : c ^ 4 * (4 * R.ℓ ^ 4 * G) ≤ c ^ 4 * (8 * R.ℓ ^ 4 * g) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 * R.ℓ ^ 4)
    linarith
  calc _ ≤ c ^ 4 * (cM * R.ℓ ^ 2 * (2 * |μ| + 2 * η)) + c ^ 4 * (8 * R.ℓ ^ 4 * g) :=
        add_le_add k1 k2
    _ = _ := by ring

/-! ### Counting the near blocks -/

open Classical in
theorem nearAB_sub (a b : Lam 2 L N) {j : ℕ} (s : Finset (Fin 2 → ℕ))
    (hs : s ⊆ blockIdx (L := L) (N := N) j) :
    s.filter (NearAB a b j) ⊆ nearSet (L := L) (N := N) j (blk j a) ∪
      nearSet (L := L) (N := N) j (blk j b) := by
  intro c hc
  obtain ⟨hcs, y, hy, hya | hyb⟩ := mem_filter.1 hc
  · refine mem_union_left _ (mem_filter.2 ⟨hs hcs, a, ?_, y, hy, ?_⟩)
    · exact subset_nbhd (isPolymer_blockSet j _) (mem_blockSet.2 rfl)
    · rw [← supNorm_neg, neg_sub]; exact hya
  · refine mem_union_right _ (mem_filter.2 ⟨hs hcs, b, ?_, y, hy, ?_⟩)
    · exact subset_nbhd (isPolymer_blockSet j _) (mem_blockSet.2 rfl)
    · rw [← supNorm_neg, neg_sub]; exact hyb

open Classical in
/-- **At most `2(L + 39)²` blocks are near `a` or `b`.** -/
theorem card_near_le (a b : Lam 2 L N) {j : ℕ} (hj : j ≤ N) (s : Finset (Fin 2 → ℕ))
    (hs : s ⊆ blockIdx (L := L) (N := N) j) :
    ((s.filter (NearAB a b j)).card : ℝ) ≤ 2 * ((L : ℝ) + 39) ^ 2 := by
  have h1 := card_le_card (nearAB_sub a b s hs)
  have h2 := card_union_le (nearSet (L := L) (N := N) j (blk j a))
    (nearSet (L := L) (N := N) j (blk j b))
  have ha := card_nearSet_le (d := 2) (L := L) (N := N) hj (blk j a) (mem_image_of_mem _ (mem_univ _))
  have hb := card_nearSet_le (d := 2) (L := L) (N := N) hj (blk j b) (mem_image_of_mem _ (mem_univ _))
  have : (s.filter (NearAB a b j)).card ≤ 2 * (L + 39) ^ 2 := by
    have e : (L + 2 ^ (2 + 3) + 7) = L + 39 := by norm_num
    rw [e] at ha hb; omega
  exact_mod_cast this

/-! ### The bulk `V'` of a block at the next scale -/

/-- **`‖V'_j(B)_∅‖_{T_{j+1}(ℓ')} ≤ ‖V_j(B)_∅‖_{T_j(2ℓ')}`** for `GoodCov2 j ℓ₀ C`, `ℓ₀ ≤ ℓ'`. -/
theorem Tj_VprO_e_le {j : ℕ} {ℓ₀ ℓ' : ℝ} (hℓ' : 0 < ℓ') (hℓ₀ : ℓ₀ ≤ ℓ')
    {C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ} (hC : GoodCov2 j ℓ₀ C) (V : OFam .two 2 L N)
    (c : Fin 2 → ℕ) :
    Tj 2 (L : ℝ) (j + 1) ℓ' (VprO C V c : SA .two (Lam 2 L N)).e ≤
      Tj 2 (L : ℝ) j (2 * ℓ') (V c : SA .two (Lam 2 L N)).e := by
  obtain ⟨H, i1, i2, Fv, Gv, hG, hB⟩ := hC.gram
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hh : (0 : ℝ) < (L : ℝ) ^ (j + 1) := pow_pos (by linarith) _
  have h1 := tNorm_ECC_theta_le hh hℓ' hG (gramBound_mono hh hB hℓ₀)
    (V c : SA .two (Lam 2 L N)).e
  refine h1.trans (tNorm_mono (pow_pos (by linarith) j).le ?_ (by linarith) le_rfl _)
  rw [pow_succ]; nlinarith [pow_pos (show (0 : ℝ) < L by linarith) j]

/-! ### The gradient part of a region at the next scale -/

theorem gradAB_zero' (a b : Lam 2 L N) : gradAB a b (0 : Alg 2 L N) = 0 := by
  have := gradAB_smul a b 0 (0 : Alg 2 L N)
  simpa using this

theorem gradAB_sum' (a b : Lam 2 L N) {ι : Type*} (s : Finset ι) (f : ι → Alg 2 L N) :
    gradAB a b (∑ i ∈ s, f i) = ∑ i ∈ s, gradAB a b (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [gradAB_zero']
  | insert x s hx ih => rw [sum_insert hx, sum_insert hx, gradAB_add, ih]

theorem tNorm_gradAB_le_sz {h ℓ : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ) (a b : Lam 2 L N)
    (F : Alg 2 L N) :
    tNorm (Dir 2) (pPhi 2) h ℓ (gradAB a b F) ≤ ENNReal.ofReal (gradM4Sz {a} a b h ℓ F) :=
  tNorm_gradAB_le one_le_two hh hℓ {a} a b F

/-- **The gradient part of a region at scale `j + 1`** from per-block sizes: only the blocks of
`a` and `b` contribute, each with `γ + μλ` (`γ` the gradient size of `V_j(B)_{ab}`, `μ` its `M₄`,
`λ` the gradient size of `LopM4 C`). -/
theorem Tj_dABX_le (P : ObsPts 2 L N) (hab : P.a ≠ P.b) (j : ℕ)
    (C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ) (V : OFam .two 2 L N) (X : Finset (Lam 2 L N))
    (hV : ∀ c, (V c : SA .two (Lam 2 L N)).ab ∈ NX ({P.a, P.b} : Set (Lam 2 L N)))
    (hS : ∀ c, IsSym (V c : SA .two (Lam 2 L N)).ab)
    (hz : ∀ c, c ≠ blk j P.a → c ≠ blk j P.b → (V c : SA .two (Lam 2 L N)).ab = 0)
    {ℓ' : ℝ} (hℓ' : 0 < ℓ') {γ μ lam : ℝ} (hγ0 : 0 ≤ γ) (hμ0 : 0 ≤ μ) (hlam0 : 0 ≤ lam)
    (hγ : ∀ c, gradM4Sz {P.a} P.a P.b ((L : ℝ) ^ (j + 1)) ℓ' (V c : SA .two (Lam 2 L N)).ab ≤ γ)
    (hμ : ∀ c, ‖cfAB4 P.a P.b (V c : SA .two (Lam 2 L N)).ab‖ ≤ μ)
    (hlam : gradM4Sz {P.a} P.a P.b ((L : ℝ) ^ (j + 1)) ℓ' (LopM4 C P.a P.b) ≤ lam) :
    Tj 2 (L : ℝ) (j + 1) ℓ' (dABX P j C V X) ≤ ENNReal.ofReal (2 * (γ + μ * lam)) := by
  classical
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hh : (0 : ℝ) < (L : ℝ) ^ (j + 1) := pow_pos (by linarith) _
  set G : (Fin 2 → ℕ) → Alg 2 L N := fun c => (V c : SA .two (Lam 2 L N)).ab with hGd
  have hF : (VprXO j C V X : SA .two (Lam 2 L N)).ab = ∑ c ∈ blocks j X, expLC C (G c) := by
    rw [VprXO, AddSubmonoidClass.coe_finsetSum, SA.sum_ab]
    exact sum_congr rfl fun c _ => by rw [VprO, (EthO_comp C (V c)).2.2]
  have hN : (VprXO j C V X : SA .two (Lam 2 L N)).ab ∈ NX ({P.a, P.b} : Set (Lam 2 L N)) := by
    rw [hF]; exact Subalgebra.sum_mem _ fun c _ => expLC_mem_NX C (hV c)
  have hSy : IsSym (VprXO j C V X : SA .two (Lam 2 L N)).ab := by
    rw [hF, isSym_iff_mem_SymS]
    exact Subalgebra.sum_mem _ fun c _ =>
      expLC_mem_SymS C ((isSym_iff_mem_SymS _).1 (hS c))
  rw [dABX_eq_grad P hab j C V X hN hSy, hF, gradAB_sum']
  set f : (Fin 2 → ℕ) → Alg 2 L N := fun c => gradAB P.a P.b (expLC C (G c)) with hfd
  have hf : ∀ c, f c = gradAB P.a P.b (G c) + cfAB4 P.a P.b (G c) • gradAB P.a P.b (LopM4 C P.a P.b) :=
    fun c => gradAB_expLC_of_ab C (hV c) (hS c)
  set T : Finset (Fin 2 → ℕ) := (blocks j X).filter (fun c => c = blk j P.a ∨ c = blk j P.b)
  have hsub : ∑ c ∈ blocks j X, f c = ∑ c ∈ T, f c := by
    refine (sum_subset (filter_subset _ _) fun c hc hcT => ?_).symm
    have hn : ¬ (c = blk j P.a ∨ c = blk j P.b) := fun h => hcT (mem_filter.2 ⟨hc, h⟩)
    push Not at hn
    show gradAB P.a P.b (expLC C (G c)) = 0
    rw [show G c = 0 from hz c hn.1 hn.2, map_zero, gradAB_zero']
  rw [hsub]
  have hTc : T.card ≤ 2 := by
    have : T ⊆ {blk j P.a, blk j P.b} := fun c hc => by
      rcases (mem_filter.1 hc).2 with h | h <;> simp [h]
    exact (card_le_card this).trans (card_le_two)
  have hterm : ∀ c, Tj 2 (L : ℝ) (j + 1) ℓ' (f c) ≤ ENNReal.ofReal (γ + μ * lam) := by
    intro c
    rw [hf c]
    refine (tNorm_add_le _ _).trans ?_
    rw [ENNReal.ofReal_add hγ0 (mul_nonneg hμ0 hlam0)]
    refine add_le_add ((tNorm_gradAB_le_sz hh hℓ' _ _ _).trans (ENNReal.ofReal_le_ofReal (hγ c)))
      (tn_smul_bound ((tNorm_gradAB_le_sz hh hℓ' _ _ _).trans (ENNReal.ofReal_le_ofReal hlam)) ?_)
    exact mul_le_mul_of_nonneg_right (hμ c) hlam0
  calc Tj 2 (L : ℝ) (j + 1) ℓ' (∑ c ∈ T, f c) ≤ ∑ c ∈ T, Tj 2 (L : ℝ) (j + 1) ℓ' (f c) :=
        tNorm_sum_le _ _
    _ ≤ ∑ c ∈ T, ENNReal.ofReal (γ + μ * lam) := sum_le_sum fun c _ => hterm c
    _ = T.card * ENNReal.ofReal (γ + μ * lam) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ 2 * ENNReal.ofReal (γ + μ * lam) := by gcongr; exact_mod_cast hTc
    _ = ENNReal.ofReal (2 * (γ + μ * lam)) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]

/-- **Scale change of the gradient size**: `(L^j, s) → (L^{j+1}, ℓ')` with `ℓ' ≤ qs`, `q ≥ 1`
gives the factor `q⁴/L`. -/
theorem gradM4Sz_scale_le {j : ℕ} {s ℓ' q : ℝ} (hℓ' : 0 ≤ ℓ') (hq : 1 ≤ q) (hs : ℓ' ≤ q * s)
    (a b : Lam 2 L N) (F : Alg 2 L N) :
    gradM4Sz {a} a b ((L : ℝ) ^ (j + 1)) ℓ' F ≤
      q ^ 4 * (L : ℝ)⁻¹ * gradM4Sz {a} a b ((L : ℝ) ^ j) s F := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hh : (0 : ℝ) < (L : ℝ) ^ j := pow_pos (by linarith) _
  have hhh : (L : ℝ) ^ j ≤ (L : ℝ) ^ (j + 1) := by
    rw [pow_succ]; nlinarith
  have h := gSzE_scale_le_q (eN1_nonneg {a} a b) hh hhh hℓ' hq hs a b F
  have e : (L : ℝ) ^ j * ((L : ℝ) ^ (j + 1))⁻¹ = (L : ℝ)⁻¹ := by
    rw [pow_succ]; field_simp
  rw [e] at h
  exact h

/-- **The `LopM4` gradient size** from the covariance and its differences. -/
theorem gradM4Sz_LopM4_le {h ℓ c dc : ℝ} (hh : 0 ≤ h) (hℓ : 0 ≤ ℓ)
    (C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ) {a b : Lam 2 L N} (hab : a ≠ b)
    (hC : ‖C a a‖ ≤ c) (hD1 : ‖C a a - C b a‖ ≤ dc) (hD2 : ‖C a a - C a b‖ ≤ dc) :
    gradM4Sz {a} a b h ℓ (LopM4 C a b) ≤
      2 * dc * (ℓ * (eN1 {a} a b * ℓ * h⁻¹)) + c * ((eN1 {a} a b * ℓ * h⁻¹) *
        (eN1 {a} a b * ℓ * h⁻¹)) :=
  gSzE_LopM4_leD (eN1_nonneg {a} a b) hh hℓ C hab hC hD1 hD2

/-! ### The per-scale gradient size of `V_n(B)_{ab}` along the history -/

/-- The right side of `gradM4Sz_hVR_block_sizesD` with the covariance scale `ℓ_{i+1}/4`, the path
length `≤ 2|a−b|_∞`, `q = 9/8` and the `μ_i` of `m4SrcX_le_sizes` (`s = |a−b|_∞`). -/
def gradRHS (Lr KG KM s : ℝ) (ℓ κQ κS : ℕ → ℝ) (j k : ℕ) : ℝ :=
  ∑ i ∈ Ico j k, ((9 / 8 : ℝ) ^ 4 * Lr⁻¹) ^ (k - 1 - i) *
    ((∑ i' ∈ Ico j (i + 1), KM * ((ℓ i')⁻¹ ^ 4 * ((Lr ^ i') ^ 2 / s ^ 2) * κQ i' +
        (ℓ (i' + 1))⁻¹ ^ 4 * ((Lr ^ (i' + 1)) ^ 2 / s ^ 2) * κS i')) *
      (2 * (2 * s * (ℓ (i + 1) / 4) ^ 2 / Lr ^ (i + 1)) *
          (ℓ (i + 1) * (2 * s * ℓ (i + 1) * (Lr ^ (i + 1))⁻¹)) +
        (ℓ (i + 1) / 4) ^ 2 * ((2 * s * ℓ (i + 1) * (Lr ^ (i + 1))⁻¹) *
          (2 * s * ℓ (i + 1) * (Lr ^ (i + 1))⁻¹))) +
      ((1 + 2 * s * (Lr ^ (i + 1))⁻¹) * (KG * (Lr ^ i * (Lr ^ (i + 1))⁻¹)) +
        (ℓ i)⁻¹ ^ 2 * (2 * (ℓ (i + 1) * (2 * s * ℓ (i + 1) * (Lr ^ (i + 1))⁻¹)) +
          (2 * s * ℓ (i + 1) * (Lr ^ (i + 1))⁻¹) * (2 * s * ℓ (i + 1) * (Lr ^ (i + 1))⁻¹))) *
        κQ i +
      ((1 + 2 * s * (Lr ^ (i + 1))⁻¹) * (KG * (Lr ^ (i + 1) * (Lr ^ (i + 1))⁻¹)) +
        (ℓ (i + 1))⁻¹ ^ 2 * (2 * (ℓ (i + 1) * (2 * s * ℓ (i + 1) * (Lr ^ (i + 1))⁻¹)) +
          (2 * s * ℓ (i + 1) * (Lr ^ (i + 1))⁻¹) * (2 * s * ℓ (i + 1) * (Lr ^ (i + 1))⁻¹))) *
        κS i)

/-- The `μ`-part: `∑_{j≤i<k}` (region `M₄` source sizes). -/
def m4RHS (Lr KM s : ℝ) (ℓ κQ κS : ℕ → ℝ) (j k : ℕ) : ℝ :=
  ∑ i' ∈ Ico j k, KM * ((ℓ i')⁻¹ ^ 4 * ((Lr ^ i') ^ 2 / s ^ 2) * κQ i' +
    (ℓ (i' + 1))⁻¹ ^ 4 * ((Lr ^ (i' + 1)) ^ 2 / s ^ 2) * κS i')

section HistS

variable {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

set_option maxHeartbeats 4000000 in
/-- **The per-scale gradient/`M₄` size of `V_n(B)_{ab}` and the per-block `M₄`** (copy of
`gradV_hist_le` with per-scale small-set sizes `Q_i` and `S` sizes `S_i`, stopped before the
budget): for every `n`-block `c`, `gradM4Sz_{a}(V_n(c)_{ab}) ≤ gradRHS(…, 2c_Nc_SQ, 2L²S)` and
`|M₄(V_n(c)_{ab})| ≤ m4RHS(…)`. -/
theorem gradV_hist_leS (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    (hNh : Nh + 2 ≤ N) (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8) (hL : 2 ^ (2 + 3) + 8 * 2 < L)
    {Cc : ℝ} (hCc0 : 0 ≤ Cc)
    (hCc : ∀ m : Fin 2 → ℕ, (∀ i, m i ≤ 1) → ∀ R : ℝ, 1 ≤ R → ∀ α : Dir 2 → ℕ,
      Grassmann.mabs α ≤ pPhi 2 → ∀ u : Zd 2,
      |D1 (fun b v => b +ᵥ v) α (cutP m R) u| ≤ Cc * R ^ (∑ i, m i) / R ^ Grassmann.mabs α)
    {cSn cNn : ℝ}
    (hcS : ∀ i, ∀ b ∈ blockIdx (L := L) (N := N) i,
      (open Classical in ((smallSets (d := 2) (L := L) (N := N) i).filter
        (fun X => blockSet i b ⊆ X)).card : ℝ) ≤ cSn)
    (hcN : ∀ i (x : Lam 2 L N) (s : Finset (Fin 2 → ℕ)), s ⊆ blockIdx (L := L) (N := N) i →
      ((s.filter (fun b => x ∈ nbhd i (blockSet (L := L) (N := N) i b))).card : ℝ) ≤ cNn)
    (P : ObsPts 2 L N) (hab : P.a ≠ P.b) (w : List (Dir 2)) (hw : pathEnd P.a w = P.b)
    (hwl : (w.length : ℝ) ≤ 2 * ((supNorm (P.a - P.b) : ℕ) : ℝ))
    {j₀ : ℕ} (o₀ : ObsSt .two L N) (hl0 : ObsLocInv P j₀ o₀) (hs0 : ObsSymInv j₀ o₀)
    (ha0 : ObsAnchInv P j₀ o₀) (hvab : ObsVabInv P o₀)
    (hz : ∀ b, (o₀.V b : SA .two (Lam 2 L N)).ab = 0)
    (t : Flow2.Hist.Seq (Xs R)) {n : ℕ} (hjn : j₀ ≤ n) (hn : n ≤ Nh)
    (ht : ∀ i ≤ n, Flow2.Hist.InDh Λ β δ κ cg cm cT ε i t)
    (QK SS : ℕ → ℝ) (hQ0 : ∀ i, 0 ≤ QK i) (hS0 : ∀ i, 0 ≤ SS i)
    (hK : ∀ i, j₀ ≤ i → i < n → ∀ X, IsSmall i X →
      Tj 2 (L : ℝ) i (histS R i t) (hKR R P j₀ o₀ t i X : SA .two (Lam 2 L N)).ab ≤
        ENNReal.ofReal (QK i))
    (hS : ∀ i, j₀ ≤ i → i < n → ∀ b ∈ blockIdx (L := L) (N := N) i,
      Tj 2 (L : ℝ) (i + 1) (histS R (i + 1) t)
        (SXO i (histCovO R t i) (hVR R P j₀ o₀ t i) (hWR R P j₀ o₀ t i)
          (Step2.Bp (L := L) (N := N) i b) : SA .two (Lam 2 L N)).ab ≤ ENNReal.ofReal (SS i)) :
    ∀ c ∈ blockIdx (L := L) (N := N) n,
      gradM4Sz {P.a} P.a P.b ((L : ℝ) ^ n) (histS R n t)
          (hVR R P j₀ o₀ t n c : SA .two (Lam 2 L N)).ab ≤
        gradRHS (L : ℝ) (KG 2 Cc 4) (KM4 2 Cc) ((supNorm (P.a - P.b) : ℕ) : ℝ)
          (fun i => histS R i t) (fun i => 2 * cNn * cSn * QK i)
          (fun i => 2 * (L : ℝ) ^ 2 * SS i) j₀ n ∧
      ‖cfAB4 P.a P.b (hVR R P j₀ o₀ t n c : SA .two (Lam 2 L N)).ab‖ ≤
        m4RHS (L : ℝ) (KM4 2 Cc) ((supNorm (P.a - P.b) : ℕ) : ℝ)
          (fun i => histS R i t) (fun i => 2 * cNn * cSn * QK i)
          (fun i => 2 * (L : ℝ) ^ 2 * SS i) j₀ n := by
  classical
  intro c hc
  have hne : (blockSet (L := L) (N := N) n c).Nonempty := by
    obtain ⟨x, -, hx⟩ := mem_image.1 hc
    exact ⟨x, mem_blockSet.2 hx⟩
  set B := blockSet (L := L) (N := N) n c with hB
  set s : ℝ := ((supNorm (P.a - P.b) : ℕ) : ℝ) with hsd
  set ℓ : ℕ → ℝ := fun i => histS R i t with hℓd
  have hℓ : ∀ i, 0 < ℓ i := fun i => histS_pos' R hρ0 hρ t i
  have hℓq : ∀ i, ℓ (i + 1) ≤ 9 / 8 * ℓ i := fun i => histS_succ_le_q R hρ0 hρ t i
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hcS0 : 0 ≤ cSn := (Nat.cast_nonneg _).trans (hcS n c hc)
  have hcN0 : 0 ≤ cNn := by
    have := hcN n P.a ∅ (empty_subset _); simpa using this
  have hF := fun i (hi : j₀ ≤ i) (hin : i < n) =>
    hist_vstep_facts R hSB hV hm hβ hδ1 H P o₀ hl0 hs0 ha0 t i hi (by omega) (ht i (by omega))
  set κQ : ℕ → ℝ := fun i => ∑ b ∈ blocks i B,
    ∑ X ∈ (smallSets i).filter (fun X => blockSet i b ⊆ X),
      (Tj 2 (L : ℝ) i (ℓ i) (hKR R P j₀ o₀ t i X : SA .two (Lam 2 L N)).ab).toReal with hκQd
  set κS : ℕ → ℝ := fun i => ∑ b ∈ blocks i B,
    (Tj 2 (L : ℝ) (i + 1) (ℓ (i + 1))
      (SXO i (histCovO R t i) (hVR R P j₀ o₀ t i) (hWR R P j₀ o₀ t i)
        (Step2.Bp (L := L) (N := N) i b) : SA .two (Lam 2 L N)).ab).toReal with hκSd
  have hκQ : ∀ i, j₀ ≤ i → i < n → κQ i ≤ 2 * cNn * cSn * QK i := fun i hi hin =>
    kappaQ_le_count P (hKR R P j₀ o₀ t i) B (hF i hi hin).2.2.2.2.1.hK (hQ0 i) (hK i hi hin)
      (hcS i) (hcN i)
  have hκS : ∀ i, j₀ ≤ i → i < n → κS i ≤ 2 * (L : ℝ) ^ 2 * SS i := by
    intro i hi hin
    have HA := (hF i hi hin).2.2.2.2.1
    exact kappaS_le_count P (i := i)
      (fun U => (SXO i (histCovO R t i) (hVR R P j₀ o₀ t i) (hWR R P j₀ o₀ t i) U :
        SA .two (Lam 2 L N)).ab) B
      (fun b _ hn' => (SXO_Bp_anch (C := histCovO R t i) HA b).2.2 hn') (hS0 i) (hS i hi hin)
  have hμ : ∀ i, j₀ ≤ i → i < n →
      ‖m4X P i (hVR R P j₀ o₀ t i) B‖ +
        ‖∑ b ∈ blocks i B, cfAB4 P.a P.b (Q2O P i (hKR R P j₀ o₀ t i) b : SA .two (Lam 2 L N)).ab‖ ≤
      m4RHS (L : ℝ) (KM4 2 Cc) s ℓ (fun i => 2 * cNn * cSn * QK i)
          (fun i => 2 * (L : ℝ) ^ 2 * SS i) j₀ (i + 1) := by
    intro i hi hin
    refine (m4X_hVR_mu_le R P j₀ o₀ t hvab hz (fun i' hi' hi'i => (hF i' hi' (by omega)).2.2.2.1)
      (fun i' _ hi'i => isPolymer_of_le (isPolymer_blockSet n c) (i' + 1) (by omega)) hi).trans
      (sum_le_sum fun i' hi' => ?_)
    obtain ⟨hji', hi'i⟩ := mem_Ico.1 hi'
    have hF' := hF i' hji' (by omega)
    exact m4SrcX_le_sizes R P j₀ o₀ t hCc0 hCc hL hab (by omega) B (hℓ i') (hℓ (i' + 1))
      hF'.2.2.2.2.2.1 hF'.2.2.2.2.2.2.1 (hκQ i' hji' (by omega)) (hκS i' hji' (by omega))
  have hCD : ∀ i, j₀ ≤ i → i < n →
      ‖histCovO R t i P.a P.a‖ ≤ (ℓ (i + 1) / 4) ^ 2 ∧
      ‖histCovO R t i P.a P.a - histCovO R t i P.b P.a‖ ≤
        2 * s * (ℓ (i + 1) / 4) ^ 2 / (L : ℝ) ^ (i + 1) ∧
      ‖histCovO R t i P.a P.a - histCovO R t i P.a P.b‖ ≤
        2 * s * (ℓ (i + 1) / 4) ^ 2 / (L : ℝ) ^ (i + 1) := by
    intro i hi hin
    obtain ⟨h1, h2, h3⟩ := covDiff_le_path (hF i hi hin).1 P.a w
    rw [hw] at h2 h3
    have hLp : (0 : ℝ) < (L : ℝ) ^ (i + 1) := pow_pos (by linarith) _
    have hx : (w.length : ℝ) * ((histS R (i + 1) t / 4) ^ 2 / (L : ℝ) ^ (i + 1)) ≤
        2 * s * (ℓ (i + 1) / 4) ^ 2 / (L : ℝ) ^ (i + 1) := by
      rw [mul_div_assoc']
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hwl (sq_nonneg _)) hLp.le
    exact ⟨h1, h2.trans hx, h3.trans hx⟩
  refine ⟨?_, ?_⟩
  · have H1 := gradM4Sz_hVR_block_sizesD R P j₀ o₀ t hCc0 hCc hL hab hvab hz (k := n) (by omega)
      (fun i hi hin => (hF i hi hin).2.2.2.1) hjn hne (q := 9 / 8) (by norm_num) ℓ hℓ
      (fun i _ _ => hℓq i) (fun i _ _ => (hℓq i).trans (by linarith [hℓ i]))
      (fun i => (ℓ (i + 1) / 4) ^ 2) (fun i => 2 * s * (ℓ (i + 1) / 4) ^ 2 / (L : ℝ) ^ (i + 1))
      (fun i => 2 * s * ((L : ℝ) ^ (i + 1))⁻¹)
      (fun i => m4RHS (L : ℝ) (KM4 2 Cc) s ℓ (fun i => 2 * cNn * cSn * QK i)
          (fun i => 2 * (L : ℝ) ^ 2 * SS i) j₀ (i + 1))
      (fun i => 2 * cNn * cSn * QK i) (fun i => 2 * (L : ℝ) ^ 2 * SS i)
      (fun i hi hin => (hCD i hi hin).1) (fun i hi hin => (hCD i hi hin).2)
      (fun i _ _ => le_rfl) hμ
      (fun i hi hin => (hF i hi hin).2.2.2.2.2.1) (fun i hi hin => (hF i hi hin).2.2.2.2.2.2.1)
      hκQ hκS
    refine H1.trans (le_of_eq ?_)
    unfold gradRHS m4RHS
    refine sum_congr rfl fun i _ => ?_
    ring
  · -- the per-block `M₄`: `m4X` of the block itself
    have e : m4X P n (hVR R P j₀ o₀ t n) B =
        cfAB4 P.a P.b (hVR R P j₀ o₀ t n c : SA .two (Lam 2 L N)).ab := by
      unfold m4X
      rw [hB, Step2.blocks_blockSet_eq hc, sum_singleton]
    rw [← e]
    refine (m4X_hVR_le R P j₀ o₀ t hvab hz (fun i' hi' hi'n => (hF i' hi' hi'n).2.2.2.1)
      (fun i' _ hi'n => isPolymer_of_le (isPolymer_blockSet n c) (i' + 1) (by omega)) hjn).trans
      (sum_le_sum fun i' hi' => ?_)
    obtain ⟨hji', hi'n⟩ := mem_Ico.1 hi'
    have hF' := hF i' hji' hi'n
    exact m4SrcX_le_sizes R P j₀ o₀ t hCc0 hCc hL hab (by omega) B (hℓ i') (hℓ (i' + 1))
      hF'.2.2.2.2.2.1 hF'.2.2.2.2.2.2.1 (hκQ i' hji' hi'n) (hκS i' hji' hi'n)

end HistS

/-! ### Anchoring and the region `M₄` sizes -/

section Anch

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N) (j : ℕ)
  (o' : ObsSt .two L N) (t : Hist.Seq (Xs R))

/-- `V_k(B)_{ab} = 0` unless `B` is the block of `a` or of `b`. -/
theorem hVR_ab_anch (ha0 : ObsAnchInv P j o') {k : ℕ} (hk : j ≤ k) (c : Fin 2 → ℕ)
    (h1 : c ≠ blk k P.a) (h2 : c ≠ blk k P.b) :
    (hVR R P j o' t k c : SA .two (Lam 2 L N)).ab = 0 := by
  rw [hVR_ab]
  refine ((obsAnchInv_histFrom' R P ha0 t hk).V c).2.2 fun ⟨z, hz⟩ => ?_
  obtain ⟨hzX, hzP⟩ := mem_inter.1 hz
  rw [ObsPts.pts, mem_insert, mem_singleton] at hzP
  have hc := (mem_blockSet.1 hzX)
  rcases hzP with rfl | rfl
  · exact h1 hc.symm
  · exact h2 hc.symm

/-- **`|M₄_k(X)| ≤ 2μ`** from per-block `M₄` sizes `≤ μ` (only the blocks of `a`, `b`). -/
theorem norm_m4X_le_two (ha0 : ObsAnchInv P j o') {k : ℕ} (hk : j ≤ k) (X : Finset (Lam 2 L N))
    {μ : ℝ} (hμ0 : 0 ≤ μ)
    (hμ : ∀ c, ‖cfAB4 P.a P.b (hVR R P j o' t k c : SA .two (Lam 2 L N)).ab‖ ≤ μ) :
    ‖m4X P k (hVR R P j o' t k) X‖ ≤ 2 * μ := by
  classical
  unfold m4X
  set T : Finset (Fin 2 → ℕ) := (blocks k X).filter (fun c => c = blk k P.a ∨ c = blk k P.b)
  have hsub : ∑ c ∈ blocks k X, cfAB4 P.a P.b (hVR R P j o' t k c : SA .two (Lam 2 L N)).ab =
      ∑ c ∈ T, cfAB4 P.a P.b (hVR R P j o' t k c : SA .two (Lam 2 L N)).ab := by
    refine (sum_subset (filter_subset _ _) fun c hc hcT => ?_).symm
    have hn : ¬ (c = blk k P.a ∨ c = blk k P.b) := fun h => hcT (mem_filter.2 ⟨hc, h⟩)
    push Not at hn
    rw [hVR_ab_anch R P j o' t ha0 hk c hn.1 hn.2]
    exact coeff_zero _
  rw [hsub]
  have hTc : T.card ≤ 2 := by
    have : T ⊆ {blk k P.a, blk k P.b} := fun c hc => by
      rcases (mem_filter.1 hc).2 with h | h <;> simp [h]
    exact (card_le_card this).trans (card_le_two)
  calc _ ≤ ∑ c ∈ T, ‖cfAB4 P.a P.b (hVR R P j o' t k c : SA .two (Lam 2 L N)).ab‖ :=
        norm_sum_le _ _
    _ ≤ ∑ c ∈ T, μ := sum_le_sum fun c _ => hμ c
    _ = T.card * μ := by rw [sum_const, nsmul_eq_mul]
    _ ≤ 2 * μ := mul_le_mul_of_nonneg_right (by exact_mod_cast hTc) hμ0

variable {Cc : ℝ} (hCc0 : 0 ≤ Cc)
  (hCc : ∀ m : Fin 2 → ℕ, (∀ i, m i ≤ 1) → ∀ R : ℝ, 1 ≤ R → ∀ α : Dir 2 → ℕ,
    Grassmann.mabs α ≤ pPhi 2 → ∀ u : Zd 2,
    |D1 (fun b v => b +ᵥ v) α (cutP m R) u| ≤ Cc * R ^ (∑ i, m i) / R ^ Grassmann.mabs α)
  (hL : 2 ^ (2 + 3) + 8 * 2 < L) (hab : P.a ≠ P.b)

include hCc0 hCc hL hab

/-- **The `Q` source of a region**: `|M₄(Q_i)(X)| ≤ K_{M4}ℓ_i^{-4}(L^i/|a−b|)²κ^Q`. -/
theorem norm_m4QX_le {i : ℕ} (X : Finset (Lam 2 L N)) {ℓi : ℝ} (hℓi : 0 < ℓi)
    (hKl : ∀ X', IsSmall i X' →
      (hKR R P j o' t i X' : SA .two (Lam 2 L N)).ab ∈ NX (nbhd i X' : Set (Lam 2 L N)))
    {κQ : ℝ}
    (hκQ : (open Classical in ∑ b ∈ blocks i X,
        ∑ X' ∈ (smallSets i).filter (fun X' => blockSet i b ⊆ X'),
          (Tj 2 (L : ℝ) i ℓi (hKR R P j o' t i X' : SA .two (Lam 2 L N)).ab).toReal) ≤ κQ) :
    ‖m4QX P i (hKR R P j o' t i) X‖ ≤
      KM4 2 Cc * (ℓi⁻¹ ^ 4 * (((L : ℝ) ^ i) ^ 2 / ((supNorm (P.a - P.b) : ℕ) : ℝ) ^ 2) * κQ) := by
  classical
  have hK := KM4_nonneg 2 (Cc := Cc)
  set s : ℝ := ((supNorm (P.a - P.b) : ℕ) : ℝ)
  unfold m4QX
  refine (norm_sum_le _ _).trans ((sum_le_sum fun b _ => norm_cfAB4_Q2O_le hCc0 hCc hL P hab i
    (hKR R P j o' t i) hKl b hℓi).trans ?_)
  rw [← mul_sum]
  have hu : 0 ≤ KM4 2 Cc * ℓi⁻¹ ^ 4 * (((L : ℝ) ^ i) ^ 2 / s ^ 2) := by positivity
  calc _ ≤ KM4 2 Cc * ℓi⁻¹ ^ 4 * (((L : ℝ) ^ i) ^ 2 / s ^ 2) * κQ :=
        mul_le_mul_of_nonneg_left hκQ hu
    _ = _ := by ring

/-- **The `Loc S` source of a region**: `|M₄(Loc S_i)(X)| ≤ K_{M4}ℓ_{i+1}^{-4}(L^{i+1}/|a−b|)²κ^S`. -/
theorem norm_m4LSX_le {i : ℕ} (hiN : i + 1 < N) (X : Finset (Lam 2 L N)) {ℓi1 : ℝ}
    (hℓi1 : 0 < ℓi1)
    (hSl : ∀ b ∈ blockIdx (L := L) (N := N) i,
      (SXO i (histCovO R t i) (hVR R P j o' t i) (hWR R P j o' t i)
        (Step2.Bp (L := L) (N := N) i b) : SA .two (Lam 2 L N)).ab ∈
        NX (nbhd (i + 1) (Step2.Bp (L := L) (N := N) i b) : Set (Lam 2 L N)))
    {κS : ℝ}
    (hκS : ∑ b ∈ blocks i X,
        (Tj 2 (L : ℝ) (i + 1) ℓi1
          (SXO i (histCovO R t i) (hVR R P j o' t i) (hWR R P j o' t i)
            (Step2.Bp (L := L) (N := N) i b) : SA .two (Lam 2 L N)).ab).toReal ≤ κS) :
    ‖m4LSX P i (histCovO R t i) (hVR R P j o' t i) (hWR R P j o' t i) X‖ ≤
      KM4 2 Cc * (ℓi1⁻¹ ^ 4 * (((L : ℝ) ^ (i + 1)) ^ 2 / ((supNorm (P.a - P.b) : ℕ) : ℝ) ^ 2) *
        κS) := by
  have hK := KM4_nonneg 2 (Cc := Cc)
  set s : ℝ := ((supNorm (P.a - P.b) : ℕ) : ℝ)
  have hbI : ∀ b ∈ blocks i X, b ∈ blockIdx (L := L) (N := N) i :=
    fun b hb => mem_blockIdx_of_mem_blocks hb
  unfold m4LSX
  refine (norm_sum_le _ _).trans ((sum_le_sum fun b hb => norm_cfAB4_LSO_le hCc0 hCc hL P hab hiN
    _ _ _ (hbI b hb) (hSl b (hbI b hb)) hℓi1).trans ?_)
  rw [← mul_sum]
  have hu : 0 ≤ KM4 2 Cc * ℓi1⁻¹ ^ 4 * (((L : ℝ) ^ (i + 1)) ^ 2 / s ^ 2) := by positivity
  calc _ ≤ KM4 2 Cc * ℓi1⁻¹ ^ 4 * (((L : ℝ) ^ (i + 1)) ^ 2 / s ^ 2) * κS :=
        mul_le_mul_of_nonneg_left hκS hu
    _ = _ := by ring

end Anch

end

end PtCorr2
