import Obs2.Est.WObs1

/-!
# The `𝒲^{obs}` contraction, part 2: the block sum with sources

* `locAp_self`, `locBp_self`: `loc^a_{X,X} = loc^a_{\{a\},\{a\}}` for every nonempty `X` (both
  branches of the pointed operator extract the full mass at `a`).
* `oTo_eq_comp`: for `w_ab = 0`, `‖F‖^{obs} = w_a ‖F_a‖ + w_b ‖F_b‖`.
* **`EthO_subLoc_contract`**: for `F` local in `B^□` (`B` a `j`-block), `U(1)` invariant, with
  `F_a = 0` unless `a ∈ B^□` (`F_b = 0` unless `b ∈ B^□`), and any nonempty `X`,
  `‖𝔼θF - Loc_{X,X}𝔼θF‖^{obs}_{T_{j+1}(ℓ')} ≤ K L^{-1} ‖F‖^{obs}_{T_j(ℓ)}`.
* `card_blocks_near`: at most `c` blocks `B` (uniformly in `L`, `j`) have `a ∈ B^□`.
* **`sum_EthW_subLoc`**: for the `𝒲`-part `S^W = ∑_{B ⊆ B_+} 𝔼θ𝒲(B)` of `S(B_+)`,
  `‖S^W - Loc_{X,X} S^W‖^{obs}_{T_{j+1}(ℓ')} ≤ 2cK L^{-1} m_W` if `‖𝒲(B)^{obs}‖ ≤ m_W`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD ENNReal

variable {d L N : ℕ} [NeZero L]

theorem locAp_self (c : Obs.Case) (a : Lam d L N) {X : Finset (Lam d L N)} (hX : X.Nonempty)
    (G : Alg d L N) : locAp c a X X G = locA c.toObs a {a} {a} G := by
  unfold locAp
  split_ifs with ha
  · have e : X ∩ {a} = ({a} : Finset (Lam d L N)) ∩ {a} := by
      rw [Finset.inter_singleton_of_mem ha, inter_self]
    cases c
    · show locOdd (-1) {a} X X G = locOdd (-1) {a} {a} {a} G
      unfold locOdd locGen; rw [e]
    · show locEven {a} X X G = locEven {a} {a} {a} G
      unfold locEven locGen; rw [e]
  · rw [div_self (Nat.cast_ne_zero.2 (card_ne_zero.2 hX)), one_smul]

theorem locBp_self (c : Obs.Case) (b : Lam d L N) {X : Finset (Lam d L N)} (hX : X.Nonempty)
    (G : Alg d L N) : locBp c b X X G = locB c.toObs b {b} {b} G := by
  unfold locBp
  split_ifs with hb
  · have e : X ∩ {b} = ({b} : Finset (Lam d L N)) ∩ {b} := by
      rw [Finset.inter_singleton_of_mem hb, inter_self]
    cases c
    · show locOdd 1 {b} X X G = locOdd 1 {b} {b} {b} G
      unfold locOdd locGen; rw [e]
    · show locEven {b} X X G = locEven {b} {b} {b} G
      unfold locEven locGen; rw [e]
  · rw [div_self (Nat.cast_ne_zero.2 (card_ne_zero.2 hX)), one_smul]

theorem Tj0 (j : ℕ) (ℓ : ℝ) : Tj d (L : ℝ) j ℓ (0 : Alg d L N) = 0 := tNorm_zero'


theorem locA_zero' (cc : ObsCase) (a : Lam d L N) (X Y : Finset (Lam d L N)) :
    locA cc a X Y (0 : Alg d L N) = 0 := by
  cases cc
  · show locOdd (-1) {a} X Y 0 = 0
    simpa using locOdd_smul (-1) {a} X Y 0 (0 : Alg d L N)
  · show locEven {a} X Y 0 = 0
    simpa using locEven_smul {a} X Y 0 (0 : Alg d L N)

theorem locB_zero' (cc : ObsCase) (b : Lam d L N) (X Y : Finset (Lam d L N)) :
    locB cc b X Y (0 : Alg d L N) = 0 := by
  cases cc
  · show locOdd 1 {b} X Y 0 = 0
    simpa using locOdd_smul 1 {b} X Y 0 (0 : Alg d L N)
  · show locEven {b} X Y 0 = 0
    simpa using locEven_smul {b} X Y 0 (0 : Alg d L N)

/-- **The pointed contraction after the expectation, one component, both cases.** -/
theorem ecc_pt_contract (d : ℕ) (hd : 1 ≤ d) : ∃ K : ℝ, 0 ≤ K ∧ ∃ L₀ : ℕ,
    ∀ (L : ℕ) [NeZero L], 2 ^ (d + 3) + 8 * d < L → L₀ ≤ L → ∀ N j : ℕ, j + 1 < N →
    ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ → ℓC ≤ ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓC C →
    ∀ b ∈ blockIdx (L := L) (N := N) j, ∀ (cc : ObsCase) (p : Lam d L N),
    ∀ G ∈ NX (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N)),
      (p ∉ nbhd j (blockSet (L := L) (N := N) j b) → G = 0) →
      (HasCharge (chargeA cc) G →
        Tj d (L : ℝ) (j + 1) ℓ' (ECC C (theta G) - locA cc p {p} {p} (ECC C (theta G))) ≤
          ENNReal.ofReal (K / L) * Tj d (L : ℝ) j ℓ G) ∧
      (HasCharge (chargeB cc) G →
        Tj d (L : ℝ) (j + 1) ℓ' (ECC C (theta G) - locB cc p {p} {p} (ECC C (theta G))) ≤
          ENNReal.ofReal (K / L) * Tj d (L : ℝ) j ℓ G) := by
  obtain ⟨K1, hK1, L₁, h1⟩ := ecc_odd_contract d hd
  obtain ⟨K2, hK2, L₂, h2⟩ := ecc_even_contract d hd
  refine ⟨K1 + K2, by positivity, max L₁ L₂, ?_⟩
  intro L _ hL hL₀ N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum hCℓ C hC b hb cc p G hG hG0
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have e1 : ENNReal.ofReal (K1 / L) ≤ ENNReal.ofReal ((K1 + K2) / L) :=
    ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (by linarith) hL0.le)
  have e2 : ENNReal.ofReal (K2 / L) ≤ ENNReal.ofReal ((K1 + K2) / L) :=
    ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (by linarith) hL0.le)
  have hL1 : L₁ ≤ L := (le_max_left _ _).trans hL₀
  have hL2 : L₂ ≤ L := (le_max_right _ _).trans hL₀
  by_cases hp : p ∈ nbhd j (blockSet (L := L) (N := N) j b)
  · cases cc
    · refine ⟨fun hc => ?_, fun hc => ?_⟩
      · exact (h1 L hL hL1 N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum hCℓ C hC b hb (-1) p hp G hG
          (by simpa [chargeA] using hc)).trans (mul_le_mul_left e1 _)
      · exact (h1 L hL hL1 N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum hCℓ C hC b hb 1 p hp G hG
          (by simpa [chargeB] using hc)).trans (mul_le_mul_left e1 _)
    · refine ⟨fun hc => ?_, fun hc => ?_⟩
      · exact (h2 L hL hL2 N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum hCℓ C hC b hb p hp G hG
          (by simpa [chargeA] using hc)).trans (mul_le_mul_left e2 _)
      · exact (h2 L hL hL2 N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum hCℓ C hC b hb p hp G hG
          (by simpa [chargeB] using hc)).trans (mul_le_mul_left e2 _)
  · rw [hG0 hp, map_zero, map_zero, locA_zero', locB_zero', sub_zero, Tj0]
    exact ⟨fun _ => zero_le, fun _ => zero_le⟩

/-- **`(1 - Loc_{X,X})𝔼θ` contracts on the observable part of a block element.** -/
theorem EthO_subLoc_contract (d : ℕ) (hd : 1 ≤ d) : ∃ K : ℝ, 0 ≤ K ∧ ∃ L₀ : ℕ,
    ∀ (L : ℕ) [NeZero L], 2 ^ (d + 3) + 8 * d < L → L₀ ≤ L → ∀ N j : ℕ, j + 1 < N →
    ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ → ℓC ≤ ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓC C →
    ∀ (c : Obs.Case) (P : ObsPts d L N) (w : Wt), w.ab = 0 →
    ∀ b ∈ blockIdx (L := L) (N := N) j, ∀ X : Finset (Lam d L N), X.Nonempty →
    ∀ F : OE c (Lam d L N),
      CmpIn (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N)) (F : SA c (Lam d L N)) →
      IsSymS (F : SA c (Lam d L N)) →
      (P.a ∉ nbhd j (blockSet (L := L) (N := N) j b) → (F : SA c (Lam d L N)).a = 0) →
      (P.b ∉ nbhd j (blockSet (L := L) (N := N) j b) → (F : SA c (Lam d L N)).b = 0) →
      oTo w (j + 1) ℓ' (EthO C F - LocO2 P X X (EthO C F)) ≤
        ENNReal.ofReal (K / L) * oTo w j ℓ F := by
  obtain ⟨K, hK, L₀, h⟩ := ecc_pt_contract d hd
  refine ⟨K, hK, L₀, ?_⟩
  intro L _ hL hL₀ N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum hCℓ C hC c P w hw0 b hb X hX F hFl hsym ha hb'
  have hch := charges_of_isSymS hsym
  have hA := (h L hL hL₀ N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum hCℓ C hC b hb c.toObs P.a _ hFl.a ha).1
    hch.1
  have hB := (h L hL hL₀ N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum hCℓ C hC b hb c.toObs P.b _ hFl.b hb').2
    hch.2.1
  have ea : ((EthO C F - LocO2 P X X (EthO C F) : OE c (Lam d L N)) : SA c (Lam d L N)).a =
      ECC C (theta (F : SA c (Lam d L N)).a) -
        locA c.toObs P.a {P.a} {P.a} (ECC C (theta (F : SA c (Lam d L N)).a)) := by
    show ECC C (theta (F : SA c (Lam d L N)).a) -
      locAp c P.a X X (ECC C (theta (F : SA c (Lam d L N)).a)) = _
    rw [locAp_self c P.a hX]
  have eb : ((EthO C F - LocO2 P X X (EthO C F) : OE c (Lam d L N)) : SA c (Lam d L N)).b =
      ECC C (theta (F : SA c (Lam d L N)).b) -
        locB c.toObs P.b {P.b} {P.b} (ECC C (theta (F : SA c (Lam d L N)).b)) := by
    show ECC C (theta (F : SA c (Lam d L N)).b) -
      locBp c P.b X X (ECC C (theta (F : SA c (Lam d L N)).b)) = _
    rw [locBp_self c P.b hX]
  rw [oTo_eq_comp hw0, oTo_eq_comp hw0, ea, eb]
  calc w.a * Tj d (L : ℝ) (j + 1) ℓ' _ + w.b * Tj d (L : ℝ) (j + 1) ℓ' _
      ≤ w.a * (ENNReal.ofReal (K / L) * Tj d (L : ℝ) j ℓ (F : SA c (Lam d L N)).a) +
        w.b * (ENNReal.ofReal (K / L) * Tj d (L : ℝ) j ℓ (F : SA c (Lam d L N)).b) :=
        add_le_add (mul_le_mul_right hA _) (mul_le_mul_right hB _)
    _ = _ := by ring

/-- At most `c` blocks `B` have `a ∈ B^□`. -/
theorem card_blocks_near (d : ℕ) : ∃ c : ℕ, ∀ (L : ℕ) [NeZero L] (N j : ℕ) (a : Lam d L N)
    (s : Finset (Fin d → ℕ)), s ⊆ blockIdx (L := L) (N := N) j →
      (s.filter (fun b => a ∈ nbhd j (blockSet (L := L) (N := N) j b))).card ≤ c := by
  classical
  obtain ⟨c, hc⟩ := card_small_near d
  refine ⟨c, fun L _ N j a s hs => ?_⟩
  refine le_trans ?_ (hc L N j a)
  refine card_le_card_of_injOn (fun b => blockSet (L := L) (N := N) j b) ?_ ?_
  · intro b hb
    obtain ⟨hbs, hba⟩ := mem_filter.1 hb
    exact mem_filter.2 ⟨mem_smallSets.2 (isSmall_blockSet_of_mem (hs hbs)), hba⟩
  · intro b₁ hb₁ b₂ _ he
    obtain ⟨x, -, hx⟩ := mem_image.1 (hs (mem_filter.1 hb₁).1)
    have h1 : x ∈ blockSet (L := L) (N := N) j b₁ := mem_blockSet.2 hx
    have h2 : x ∈ blockSet (L := L) (N := N) j b₂ := by
      have := he; simp only at this; rw [← this]; exact h1
    rw [← hx]; exact mem_blockSet.1 h2

/-- **The `𝒲` part of `S(B_+)`**: `‖S^W - Loc_{X,X}S^W‖^{obs} ≤ 2cK L^{-1} m_W`. -/
theorem sum_EthW_subLoc (d : ℕ) (hd : 1 ≤ d) : ∃ K : ℝ, 0 ≤ K ∧ ∃ L₀ : ℕ,
    ∀ (L : ℕ) [NeZero L], 2 ^ (d + 3) + 8 * d < L → L₀ ≤ L → ∀ N j : ℕ, j + 1 < N →
    ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ → ℓC ≤ ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓC C →
    ∀ (c : Obs.Case) (P : ObsPts d L N) (w : Wt), w.ab = 0 →
    ∀ X : Finset (Lam d L N), X.Nonempty → ∀ s : Finset (Fin d → ℕ),
      s ⊆ blockIdx (L := L) (N := N) j →
    ∀ (Wf : (Fin d → ℕ) → OE c (Lam d L N)) (mW : ℝ),
      0 ≤ mW →
      (∀ b ∈ s, CmpIn (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N))
        (Wf b : SA c (Lam d L N))) →
      (∀ b ∈ s, IsSymS (Wf b : SA c (Lam d L N))) →
      (∀ b ∈ s, P.a ∉ nbhd j (blockSet (L := L) (N := N) j b) → (Wf b : SA c (Lam d L N)).a = 0) →
      (∀ b ∈ s, P.b ∉ nbhd j (blockSet (L := L) (N := N) j b) → (Wf b : SA c (Lam d L N)).b = 0) →
      (∀ b ∈ s, oTo w j ℓ (Wf b) ≤ ENNReal.ofReal mW) →
      oTo w (j + 1) ℓ' ((∑ b ∈ s, EthO C (Wf b)) - LocO2 P X X (∑ b ∈ s, EthO C (Wf b))) ≤
        ENNReal.ofReal (K / L * mW) := by
  classical
  obtain ⟨K, hK, L₀, h⟩ := EthO_subLoc_contract d hd
  obtain ⟨cn, hcn⟩ := card_blocks_near d
  refine ⟨K * (2 * cn), by positivity, L₀, ?_⟩
  intro L _ hL hL₀ N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum hCℓ C hC c P w hw0 X hX s hs Wf mW hmW
    hWl hWs hWa hWb hWm
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  rw [map_sum, ← sum_sub_distrib]
  refine (oTo_sum_le w _ _ _ _).trans ?_
  set near : Finset (Fin d → ℕ) := s.filter (fun b => P.a ∈ nbhd j (blockSet (L := L) (N := N) j b) ∨
    P.b ∈ nbhd j (blockSet (L := L) (N := N) j b)) with hnear
  have hcard : (near.card : ℝ) ≤ 2 * cn := by
    have h1 : near.card ≤ (s.filter (fun b => P.a ∈ nbhd j (blockSet (L := L) (N := N) j b))).card +
        (s.filter (fun b => P.b ∈ nbhd j (blockSet (L := L) (N := N) j b))).card := by
      rw [hnear, filter_or]; exact card_union_le _ _
    have h2 := hcn L N j P.a s hs
    have h3 := hcn L N j P.b s hs
    have : near.card ≤ 2 * cn := by omega
    exact_mod_cast this
  have hterm : ∀ b ∈ s, oTo w (j + 1) ℓ' (EthO C (Wf b) - LocO2 P X X (EthO C (Wf b))) ≤
      (if b ∈ near then ENNReal.ofReal (K / L * mW) else 0) := by
    intro b hb
    have hc := h L hL hL₀ N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum hCℓ C hC c P w hw0 b (hs hb) X hX (Wf b)
      (hWl b hb) (hWs b hb) (hWa b hb) (hWb b hb)
    split_ifs with hn
    · exact hc.trans (by
        rw [ENNReal.ofReal_mul (by positivity)]; exact mul_le_mul_right (hWm b hb) _)
    · have hn' : P.a ∉ nbhd j (blockSet (L := L) (N := N) j b) ∧
          P.b ∉ nbhd j (blockSet (L := L) (N := N) j b) := by
        rw [hnear, mem_filter] at hn; push_neg at hn; exact hn hb
      have h0 : oTo w j ℓ (Wf b) = 0 := by
        rw [oTo_eq_comp hw0, hWa b hb hn'.1, hWb b hb hn'.2, Tj0]; simp
      rw [h0, mul_zero] at hc; exact hc
  refine (sum_le_sum hterm).trans ?_
  rw [← sum_filter]
  refine (le_ofReal_sum_const _ (by positivity) fun _ _ => le_rfl).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hfil : s.filter (fun b => b ∈ near) = near := by
    ext b; simp only [mem_filter, hnear]; tauto
  rw [hfil]
  calc (near.card : ℝ) * (K / L * mW) ≤ 2 * cn * (K / L * mW) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = K * (2 * cn) / L * mW := by ring

end

end Obs2
