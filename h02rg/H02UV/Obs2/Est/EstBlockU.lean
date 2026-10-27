import Obs2.Est.EstBlockAB

/-!
# Block bounds of the second-order map with all four components (unreduced inputs, `w_{ab} > 0`)

The copy `BHOU` of `Obs2.BHOAB` for inputs **with** one-point parts (no `abSub` hypothesis), all
four components local (`CmpInA`), weights with `w.Sub`. On `abSub` the product of two observable
parts vanished (`FCO_obs_obs_ab`); here it does not (it feeds `F_aG_b + F_bG_a`). It is absorbed
by halving the `V` sizes: `‖V(B)^∅‖ ≤ r/2`, `‖V(B)^{obs}‖ ≤ m_V/2`, `m_V ≤ r`. Then the pair bounds
`pair_o`, `pairπ_o`, `SF_o` hold with the **same** constants as in `BHO` (`2(Q₁m/2)² ≤ Q₁²rm/2`), so
all conclusions keep the names and constants of `BHOAB`. The localisation bound `hloc` is required
for all `F` (discharged by `exists_LocO2_full_bound`).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step FRD ENNReal

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

/-- The hypotheses for the block bounds at scale `j`, unreduced inputs (all four components). -/
structure BHOU (P : ObsPts d L N) (j : ℕ) (ℓ ℓ' ℓC : ℝ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : OFam c d L N) (K : OAct c d L N) (w : Wt) (r mV mW k Cl cS : ℝ) : Prop where
  hd : 1 ≤ d
  hLp : pauliL0 d ≤ L
  hL8 : 2 ^ (d + 3) + 8 * d < L
  hjN : j + 1 < N
  hℓ : 0 < ℓ
  hℓ' : 0 < ℓ'
  hℓC : 0 < ℓC
  hsum : ℓ' + ℓC ≤ 2 * ℓ
  hC : Step2.GoodCov2 j ℓC C
  hw : w.Sub
  hVl : ∀ b, CmpInA (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N)) (V b : SA c (Lam d L N))
  hWl : ∀ b, CmpInA (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N)) (W b : SA c (Lam d L N))
  hKl : ∀ X, IsSmall j X → CmpInA (nbhd j X : Set (Lam d L N)) (K X : SA c (Lam d L N))
  hr : 0 ≤ r
  hmV : 0 ≤ mV
  hmW : 0 ≤ mW
  hk : 0 ≤ k
  hVr : ∀ b ∈ blockIdx (L := L) (N := N) j,
    Tj d (L : ℝ) j ℓ (V b : SA c (Lam d L N)).e ≤ ENNReal.ofReal (r / 2)
  hVm : ∀ b ∈ blockIdx (L := L) (N := N) j, oTo w j ℓ (V b) ≤ ENNReal.ofReal (mV / 2)
  hmVr : mV ≤ r
  hWm : ∀ b ∈ blockIdx (L := L) (N := N) j, oTo w j ℓ (W b) ≤ ENNReal.ofReal mW
  hKk : ∀ X, IsSmall j X → oTo w j ℓ (K X) ≤ ENNReal.ofReal k
  hCl : 0 ≤ Cl
  hloc : ∀ k' : ℕ, k' < N → ∀ ℓ₀ : ℝ, 0 < ℓ₀ → ∀ X Y : Finset (Lam d L N), IsSmall k' X →
    Y ⊆ X → ∀ F : OE c (Lam d L N),
      CmpInA (nbhd k' X : Set (Lam d L N)) (F : SA c (Lam d L N)) →
      oTo w k' ℓ₀ (LocO2 P X Y F) ≤ ENNReal.ofReal Cl * oTo w k' ℓ₀ F
  hlocl : ∀ X Y : Finset (Lam d L N), IsPolymer j Y → ∀ F : OE c (Lam d L N),
    CmpInA (↑(nbhd j Y ∪ {P.a, P.b}) : Set (Lam d L N)) (LocO2 P X Y F : SA c (Lam d L N))
  hcS : 1 ≤ cS
  hcount : ∀ b ∈ blockIdx (d := d) (L := L) (N := N) j,
    (((smallSets (d := d) (L := L) (N := N) j).filter (fun X => blockSet j b ⊆ X)).card : ℝ) ≤ cS

namespace BHOU

variable {P : ObsPts d L N} {j : ℕ} {ℓ ℓ' ℓC : ℝ} {C : Matrix (Lam d L N) (Lam d L N) ℂ}
  {V W : OFam c d L N} {K : OAct c d L N} {w : Wt} {r mV mW k Cl cS : ℝ}
  (H : BHOU P j ℓ ℓ' ℓC C V W K w r mV mW k Cl cS)
include H

theorem hj : j < N := by have := H.hjN; omega

theorem hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)

theorem hQ1 : 1 ≤ Step2.Q1 d := Step2.one_le_Q1 H.hd

theorem hcNear : 0 ≤ Step2.cNear d L := Nat.cast_nonneg _

theorem hQ0 : 0 ≤ Step2.Q1 d := by linarith [H.hQ1]

theorem hsO : 0 ≤ sO d L r mV mW := by
  have := H.hcNear; have := H.hr; have := H.hmV
  unfold sO
  exact add_nonneg (by positivity) (mul_nonneg H.hQ0 H.hmW)

theorem hVm' {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTo w j ℓ (V b) ≤ ENNReal.ofReal mV :=
  (H.hVm b hb).trans (ENNReal.ofReal_le_ofReal (by linarith [H.hmV]))

/-! ### `V'_B` -/

theorem Vpr_o {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTo w (j + 1) ℓ' (VprO C V b) ≤ ENNReal.ofReal (Step2.Q1 d * mV) := by
  rw [VprO]
  refine (oTo_EthO_le2A H.hd H.hLp H.hj H.hℓ' H.hℓC H.hsum H.hC (H.hVl b)).trans ?_
  exact le_ofReal_mul (by linarith [H.hQ1])
    (ENNReal.ofReal_le_ofReal (Step2.pq_pow_le_Q1 H.hd H.hj.le b)) (H.hVm' hb)

theorem V2_eh {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    Tj d (L : ℝ) (j + 1) (2 * ℓ) (V b : SA c (Lam d L N)).e ≤
      ENNReal.ofReal (Step2.Q1 d * (r / 2)) := by
  rw [ENNReal.ofReal_mul (by linarith [H.hQ1])]
  exact (Step2.Tj2_block_le H.hd H.hLp H.hj H.hℓ (H.hVl b).e).trans
    (mul_le_mul_left' (H.hVr b hb) _)

theorem V2_oh {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTo w (j + 1) (2 * ℓ) (V b) ≤ ENNReal.ofReal (Step2.Q1 d * (mV / 2)) := by
  refine (oTj_succ_two_leA H.hd H.hLp H.hj (H.hVl b).πobs H.hℓ).trans ?_
  exact le_ofReal_mul (by linarith [H.hQ1])
    (ENNReal.ofReal_le_ofReal (Step2.pq_pow_le_Q1 H.hd H.hj.le b)) (H.hVm b hb)

/-- The product of two observable parts at scale `j + 1`: `≤ 2(Q₁m_V/2)²`. -/
theorem obsobs_o {b b' : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j)
    (hb' : b' ∈ blockIdx (L := L) (N := N) j) :
    oTo w (j + 1) ℓ' (FCO C (EthO C (πobs (V b))) (EthO C (πobs (V b')))) ≤
      ENNReal.ofReal (2 * ((Step2.Q1 d * (mV / 2)) * (Step2.Q1 d * (mV / 2)))) := by
  refine (oTo_le w _ _ _).trans ((oTj_FCO_le H.hℓ' H.hℓC H.hsum H.hC H.hw _ _).trans ?_)
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  exact mul_le_mul_left' (le_ofReal_mul (mul_nonneg H.hQ0 (by linarith [H.hmV]))
    (H.V2_oh hb) (H.V2_oh hb')) _

/-! ### The pair terms `F(V'_B, V'_{B'})` -/

omit H in
theorem FCO_split (A B : OE c (Lam d L N)) :
    FCO C (EthO C A) (EthO C B) = FCO C (EthO C (emb (bulk A) : OE c (Lam d L N)))
        (EthO C (emb (bulk B) : OE c (Lam d L N))) +
      FCO C (EthO C (emb (bulk A) : OE c (Lam d L N))) (EthO C (πobs B)) +
      FCO C (EthO C (πobs A)) (EthO C (emb (bulk B) : OE c (Lam d L N))) +
      FCO C (EthO C (πobs A)) (EthO C (πobs B)) := by
  conv_lhs => rw [eq_emb_add_πobs A, eq_emb_add_πobs B]
  rw [EthO_add, EthO_add, FCO_add_left, FCO_add_right, FCO_add_right]
  abel

theorem pair_o {b b' : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j)
    (hb' : b' ∈ blockIdx (L := L) (N := N) j) :
    oTo w (j + 1) ℓ' (FCO C (VprO C V b) (VprO C V b')) ≤
      ENNReal.ofReal (4 * Step2.Q1 d ^ 2 * (r * mV)) := by
  have hQ := H.hQ1; have hr := H.hr; have hm := H.hmV
  rw [VprO, VprO, FCO_split]
  have e1 := oTo_FCO_bulk w C (V b) (V b') (j + 1) ℓ'
  have e4 := H.obsobs_o hb hb'
  have h2 : oTo w (j + 1) ℓ' (FCO C (EthO C (emb (bulk (V b)) : OE c (Lam d L N)))
      (EthO C (πobs (V b')))) ≤
      ENNReal.ofReal (2 * ((Step2.Q1 d * (r / 2)) * (Step2.Q1 d * (mV / 2)))) := by
    refine (oTo_le w _ _ _).trans ((oTj_FCO_le H.hℓ' H.hℓC H.hsum H.hC H.hw _ _).trans ?_)
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    refine mul_le_mul_left' (le_ofReal_mul (mul_nonneg H.hQ0 (by linarith)) ?_ ?_) _
    · rw [oTj_emb]; exact H.V2_eh hb
    · exact H.V2_oh hb'
  have h3 : oTo w (j + 1) ℓ' (FCO C (EthO C (πobs (V b)))
      (EthO C (emb (bulk (V b')) : OE c (Lam d L N)))) ≤
      ENNReal.ofReal (2 * ((Step2.Q1 d * (mV / 2)) * (Step2.Q1 d * (r / 2)))) := by
    refine (oTo_le w _ _ _).trans ((oTj_FCO_le H.hℓ' H.hℓC H.hsum H.hC H.hw _ _).trans ?_)
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    refine mul_le_mul_left' (le_ofReal_mul (mul_nonneg H.hQ0 (by linarith)) (H.V2_oh hb) ?_) _
    rw [oTj_emb]; exact H.V2_eh hb'
  refine (oTo_add_le w _ _ _ _).trans ?_
  refine (add_le_add ((oTo_add_le w _ _ _ _).trans (add_le_add ((oTo_add_le w _ _ _ _).trans
    (add_le_add (le_of_eq e1) h2)) h3)) e4).trans ?_
  have hQ0 := H.hQ0
  have hmr := H.hmVr
  rw [zero_add, ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hq2 : 0 ≤ Step2.Q1 d ^ 2 := sq_nonneg _
  have : Step2.Q1 d ^ 2 * (mV * mV) ≤ Step2.Q1 d ^ 2 * (r * mV) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmr hm) hq2
  have hrm : 0 ≤ Step2.Q1 d ^ 2 * (r * mV) := by positivity
  nlinarith

/-! ### `S(B)` -/

theorem far_sep {b b' : Fin d → ℕ} (hb' : b' ∈ blockIdx (L := L) (N := N) j)
    (h : b' ∉ Step2.nearSet (L := L) (N := N) j b) :
    CovSep C (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N))
      (nbhd j (blockSet (L := L) (N := N) j b') : Set (Lam d L N)) := by
  set Y1 : Finset (Lam d L N) := nbhd j (blockSet (L := L) (N := N) j b)
  set Y2 : Finset (Lam d L N) := nbhd j (blockSet (L := L) (N := N) j b')
  have hfar : ∀ x ∈ Y1, ∀ y ∈ Y2, L ^ (j + 1) ≤ 2 * supNorm (x - y) :=
    fun x hx y hy => Step2.not_near_far hb' h hx hy
  have hpos : 0 < L ^ (j + 1) := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
  have hdis : Disjoint (Y1 : Set (Lam d L N)) (Y2 : Set (Lam d L N)) := by
    rw [Set.disjoint_left]
    intro z hz hz'
    have h3 := hfar z hz z hz'
    rw [sub_self, supNorm_zero, mul_zero] at h3
    omega
  have hCz : ∀ x ∈ (Y1 : Set (Lam d L N)), ∀ y ∈ (Y2 : Set (Lam d L N)),
      C x y = 0 ∧ C y x = 0 := by
    intro x hx y hy
    have h1 : L ^ (j + 1) ≤ 2 * supNorm (x - y) := hfar x hx y hy
    have h1' : ((L : ℝ) ^ (j + 1)) / 2 ≤ (supNorm (x - y) : ℝ) := by
      have h4 : ((L ^ (j + 1) : ℕ) : ℝ) ≤ ((2 * supNorm (x - y) : ℕ) : ℝ) := Nat.cast_le.2 h1
      rw [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] at h4
      linarith
    have h2 : supNorm (y - x) = supNorm (x - y) := by
      rw [← neg_sub, supNorm_neg]
    exact ⟨H.hC.range H.hjN x y h1', H.hC.range H.hjN y x (by rw [h2]; exact h1')⟩
  exact ⟨hdis, hCz⟩

/-- Far blocks do not interact (bulk and single-source components). -/
theorem far_gen {b b' : Fin d → ℕ} (hb' : b' ∈ blockIdx (L := L) (N := N) j)
    (h : b' ∉ Step2.nearSet (L := L) (N := N) j b) {A B : OE c (Lam d L N)}
    (hA : CmpInA (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N)) (A : SA c (Lam d L N)))
    (hB : CmpInA (nbhd j (blockSet (L := L) (N := N) j b') : Set (Lam d L N))
      (B : SA c (Lam d L N))) :
    FCO C A B = 0 :=
  FCO_eq_zero_of_sepA C (H.far_sep hb' h) hA hB

theorem EthW_o {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTo w (j + 1) ℓ' (EthO C (W b)) ≤ ENNReal.ofReal (Step2.Q1 d * mW) := by
  refine (oTo_EthO_le2A H.hd H.hLp H.hj H.hℓ' H.hℓC H.hsum H.hC (H.hWl b)).trans ?_
  exact le_ofReal_mul (by linarith [H.hQ1])
    (ENNReal.ofReal_le_ofReal (Step2.pq_pow_le_Q1 H.hd H.hj.le b)) (H.hWm b hb)

theorem pairh_oh {b b' : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j)
    (hb' : b' ∈ blockIdx (L := L) (N := N) j) :
    oTo w (j + 1) ℓ' (FCO C (EthO C (πobs (V b)))
      (EthO C (emb (bulk (V b')) : OE c (Lam d L N)))) ≤
      ENNReal.ofReal (2 * ((Step2.Q1 d * (mV / 2)) * (Step2.Q1 d * (r / 2)))) := by
  have hm := H.hmV
  refine (oTo_le w _ _ _).trans ((oTj_FCO_le H.hℓ' H.hℓC H.hsum H.hC H.hw _ _).trans ?_)
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  refine mul_le_mul_left' (le_ofReal_mul (mul_nonneg H.hQ0 (by linarith)) (H.V2_oh hb) ?_) _
  rw [oTj_emb]; exact H.V2_eh hb'

/-- `‖F(V'^{obs}_B, V'_{B'})^{obs}‖ ≤ Q₁² r m_V` (the obs-obs product included). -/
theorem pairπ_oh {b b' : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j)
    (hb' : b' ∈ blockIdx (L := L) (N := N) j) :
    oTo w (j + 1) ℓ' (FCO C (πobs (VprO C V b)) (VprO C V b')) ≤
      ENNReal.ofReal (Step2.Q1 d ^ 2 * (r * mV)) := by
  have hm := H.hmV; have hmr := H.hmVr; have hQ0 := H.hQ0; have hr := H.hr
  rw [VprO, VprO, πobs_EthO, eq_emb_add_πobs (V b'), EthO_add, FCO_add_right]
  refine (oTo_add_le w _ _ _ _).trans ((add_le_add (H.pairh_oh hb hb') (H.obsobs_o hb hb')).trans ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hq2 : 0 ≤ Step2.Q1 d ^ 2 := sq_nonneg _
  have : Step2.Q1 d ^ 2 * (mV * mV) ≤ Step2.Q1 d ^ 2 * (r * mV) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmr hm) hq2
  nlinarith

theorem pairπ_o {b b' : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j)
    (hb' : b' ∈ blockIdx (L := L) (N := N) j) :
    oTo w (j + 1) ℓ' (FCO C (πobs (VprO C V b)) (VprO C V b')) ≤
      ENNReal.ofReal (2 * Step2.Q1 d ^ 2 * (r * mV)) := by
  have hm := H.hmV; have hr := H.hr
  refine (H.pairπ_oh hb hb').trans (ENNReal.ofReal_le_ofReal ?_)
  have : 0 ≤ Step2.Q1 d ^ 2 * (r * mV) := by positivity
  linarith

/-- `‖G(B, B')^{obs}‖ ≤ 4 Q₁² r m_V`. -/
theorem pairG_o {b b' : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j)
    (hb' : b' ∈ blockIdx (L := L) (N := N) j) :
    oTo w (j + 1) ℓ' (GO C V b b') ≤ ENNReal.ofReal (4 * Step2.Q1 d ^ 2 * (r * mV)) := by
  have hr := H.hr; have hm := H.hmV
  rw [GO, FCO_comm C (VprO C V b)]
  refine (oTo_sub_le w _ _ _ _).trans ?_
  refine (add_le_add (H.pairπ_o hb hb') (H.pairπ_o hb' hb)).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))

/-- Sums over the blocks with finite range: only the `c_near` near blocks contribute. -/
theorem near_sum_o {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j)
    (f : (Fin d → ℕ) → OE c (Lam d L N)) {x : ℝ} (hx : 0 ≤ x)
    (hfar : ∀ b' ∈ blockIdx (L := L) (N := N) j, b' ∉ Step2.nearSet (L := L) (N := N) j b →
      f b' = 0)
    (hnear : ∀ b' ∈ blockIdx (L := L) (N := N) j, oTo w (j + 1) ℓ' (f b') ≤ ENNReal.ofReal x) :
    oTo w (j + 1) ℓ' (∑ b' ∈ blockIdx (L := L) (N := N) j, f b') ≤
      ENNReal.ofReal (Step2.cNear d L * x) := by
  classical
  refine (oTo_sum_le w _ _ _ _).trans ?_
  rw [← sum_filter_add_sum_filter_not (blockIdx (L := L) (N := N) j)
    (fun b' => b' ∈ Step2.nearSet (L := L) (N := N) j b)]
  rw [sum_eq_zero (s := filter (fun b' => ¬ _) _) fun b' hb' =>
    by rw [hfar b' (mem_filter.1 hb').1 (mem_filter.1 hb').2, oTo_zeroA], add_zero]
  refine (le_ofReal_sum_const _ hx fun b' hb' =>
    hnear b' (mem_filter.1 hb').1).trans (ENNReal.ofReal_le_ofReal ?_)
  have hn : ((filter (fun b' => b' ∈ Step2.nearSet (L := L) (N := N) j b)
      (blockIdx (L := L) (N := N) j)).card : ℝ) ≤ Step2.cNear d L := by
    have h1 : (filter (fun b' => b' ∈ Step2.nearSet (L := L) (N := N) j b)
        (blockIdx (L := L) (N := N) j)).card ≤ (Step2.nearSet (L := L) (N := N) j b).card :=
      card_le_card fun b' hb' => (mem_filter.1 hb').2
    unfold Step2.cNear
    exact_mod_cast h1.trans (Step2.card_nearSet_le H.hj.le b hb)
  exact mul_le_mul_of_nonneg_right hn hx

/-- **`‖S^{(2)}(B)^{obs}‖_{T_{j+1}(ℓ')} ≤ 2 c_near Q₁² r m_V`** (sharp splitting, the
obs-obs product included). -/
theorem SF_o {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTo w (j + 1) ℓ' (SFO j C V b) ≤
      ENNReal.ofReal (Step2.cNear d L * (2 * Step2.Q1 d ^ 2 * (r * mV))) := by
  classical
  have hQ := H.hQ1; have hr := H.hr; have hm := H.hmV; have hn := H.hcNear
  have hQ0 := H.hQ0
  have hΛ : (emb (bulk (VprLO j C V)) : OE c (Lam d L N)) =
      ∑ b' ∈ blockIdx (L := L) (N := N) j, EthO C (emb (bulk (V b')) : OE c (Lam d L N)) := by
    rw [VprLO, map_sum, map_sum]
    refine sum_congr rfl fun b' _ => ?_
    rw [VprO, bulk_EthO, EthO_emb]
  have e1 : FCO C (VprO C V b) (emb (bulk (VprLO j C V))) =
      FCO C (emb (bulk (VprO C V b))) (emb (bulk (VprLO j C V))) +
        ∑ b' ∈ blockIdx (L := L) (N := N) j, FCO C (EthO C (πobs (V b)))
          (EthO C (emb (bulk (V b')) : OE c (Lam d L N))) := by
    conv_lhs => rw [eq_emb_add_πobs (VprO C V b)]
    rw [FCO_add_left, hΛ, ← FCO_sum_right, VprO, πobs_EthO]
  have h1 : oTo w (j + 1) ℓ' (FCO C (VprO C V b) (emb (bulk (VprLO j C V)))) ≤
      ENNReal.ofReal (Step2.cNear d L * (2 * ((Step2.Q1 d * (mV / 2)) * (Step2.Q1 d * (r / 2))))) := by
    rw [e1, FCO_emb, oTo_emb_add]
    refine H.near_sum_o hb _ (by positivity) (fun b' hb' h => ?_) (fun b' hb' => H.pairh_oh hb hb')
    exact H.far_gen hb' h ((H.hVl b).πobs.EthO C) (((H.hVl b').πe).EthO C)
  have h2 : oTo w (j + 1) ℓ' (FCO C (πobs (VprO C V b)) (VprLO j C V)) ≤
      ENNReal.ofReal (Step2.cNear d L * (Step2.Q1 d ^ 2 * (r * mV))) := by
    rw [VprLO, FCO_sum_right]
    refine H.near_sum_o hb _ (by positivity) (fun b' hb' h => ?_) (fun b' hb' => H.pairπ_oh hb hb')
    rw [VprO, πobs_EthO]
    exact H.far_gen hb' h ((H.hVl b).πobs.EthO C) ((H.hVl b').EthO C)
  rw [SFO_eq_anch]
  refine (oTo_add_le w _ _ _ _).trans ?_
  rw [oTo_smul, oTo_smul]
  have hh : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [hh]
  refine (add_le_add (mul_le_mul_left' h1 _) (mul_le_mul_left' h2 _)).trans ?_
  rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have : 0 ≤ Step2.cNear d L * (Step2.Q1 d ^ 2 * (r * mV)) := by positivity
  nlinarith

/-- **`‖S(B)^{obs}‖_{T_{j+1}(ℓ')} ≤ 2 c_near Q₁² r m_V + Q₁ m_W`.** -/
theorem Sb_o {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTo w (j + 1) ℓ' (SbO j C V W b) ≤ ENNReal.ofReal (sO d L r mV mW) := by
  have hQ := H.hQ1; have hr := H.hr; have hm := H.hmV; have hmW := H.hmW
  have hn := H.hcNear
  rw [SbO]
  refine (oTo_add_le w _ _ _ _).trans ?_
  refine (le_ofReal_add (by positivity) (mul_nonneg H.hQ0 hmW) (H.SF_o hb) (H.EthW_o hb)).trans
    (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  unfold sO; ring

theorem hL8' : 2 ^ (d + 3) ≤ L := by have := H.hL8; omega

theorem nbhd_block_sub {b b' : Fin d → ℕ} (hb' : b' ∈ Step2.nearSet (L := L) (N := N) j b) :
    (nbhd j (blockSet (L := L) (N := N) j b') : Set (Lam d L N)) ⊆
      (nbhd (j + 1) (Step2.Bp (L := L) (N := N) j b) : Set (Lam d L N)) := fun _ hy =>
  Step2.mem_nbhd_succ_of_near H.hd H.hL8' H.hjN.le hb' hy

theorem FCsum_mem {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) {A : OE c (Lam d L N)}
    (hA : CmpInA (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N)) (A : SA c (Lam d L N)))
    {Bf : (Fin d → ℕ) → OE c (Lam d L N)}
    (hB : ∀ b', CmpInA (nbhd j (blockSet (L := L) (N := N) j b') : Set (Lam d L N))
      (Bf b' : SA c (Lam d L N))) :
    CmpInA (nbhd (j + 1) (Step2.Bp (L := L) (N := N) j b) : Set (Lam d L N))
      (FCO C A (∑ b' ∈ blockIdx (L := L) (N := N) j, Bf b') : SA c (Lam d L N)) := by
  classical
  have hs := H.nbhd_block_sub (Step2.mem_nearSet_self hb)
  rw [FCO_sum_right, AddSubmonoidClass.coe_finsetSum]
  refine CmpInA.sum _ fun b' hb' => ?_
  by_cases hn : b' ∈ Step2.nearSet (L := L) (N := N) j b
  · exact CmpInA.FCO C (hA.mono hs) ((hB b').mono (H.nbhd_block_sub hn))
  · rw [H.far_gen hb' hn hA (hB b')]; exact CmpInA.zero

theorem Sb_mem {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    CmpInA (nbhd (j + 1) (Step2.Bp (L := L) (N := N) j b) : Set (Lam d L N))
      (SbO j C V W b : SA c (Lam d L N)) := by
  have hs := H.nbhd_block_sub (Step2.mem_nearSet_self hb)
  have hX := (H.hVl b).EthO C
  have hY : ∀ b', CmpInA (nbhd j (blockSet (L := L) (N := N) j b') : Set (Lam d L N))
      (VprO C V b' : SA c (Lam d L N)) := fun b' => (H.hVl b').EthO C
  rw [SbO, SFO, SCorO]
  refine CmpInA.add (CmpInA.add (CmpInA.smul _ ?_) (CmpInA.smul _ (CmpInA.sub ?_ ?_)))
    (((H.hWl b).EthO C).mono hs)
  · rw [VprLO]; exact H.FCsum_mem hb hX hY
  · rw [VprLO]; exact H.FCsum_mem hb hX.πobs hY
  · rw [VprLO, map_sum]; exact H.FCsum_mem hb hX fun b' => (hY b').πobs

omit H in
theorem nb_Bp_le (b : Fin d → ℕ) : nb j (Step2.Bp (L := L) (N := N) j b) ≤ L ^ d := by
  have h1 := nb_le_of_succ (isPolymer_clo (L := L) (N := N) j (blockSet j b))
  have h2 := (nb_clo_le (L := L) (N := N) j (blockSet j b)).trans (nb_blockSet_le j b)
  calc nb j (Step2.Bp (L := L) (N := N) j b) ≤ L ^ d * nb (j + 1) (clo j (blockSet j b)) := h1
    _ ≤ L ^ d * 1 := Nat.mul_le_mul_left _ h2
    _ = L ^ d := mul_one _

theorem SX_mem {b : Fin d → ℕ} :
    CmpInA (nbhd (j + 1) (Step2.Bp (L := L) (N := N) j b) : Set (Lam d L N))
      (SXO j C V W (Step2.Bp (L := L) (N := N) j b) : SA c (Lam d L N)) := by
  rw [SXO, AddSubmonoidClass.coe_finsetSum]
  refine CmpInA.sum _ fun b'' hb'' => ?_
  exact (H.Sb_mem (mem_blockIdx_of_mem_blocks hb'')).mono
    (by exact_mod_cast nbhd_mono (Step2.BH.Bp_sub hb''))

theorem SX_o (b : Fin d → ℕ) :
    oTo w (j + 1) ℓ' (SXO j C V W (Step2.Bp (L := L) (N := N) j b)) ≤
      ENNReal.ofReal ((L : ℝ) ^ d * sO d L r mV mW) := by
  have := H.hsO
  rw [SXO]
  refine (oTo_sum_le w _ _ _ _).trans ((le_ofReal_sum_const _ this fun b'' hb'' =>
    H.Sb_o (mem_blockIdx_of_mem_blocks hb'')).trans (ENNReal.ofReal_le_ofReal ?_))
  have h' : ((blocks j (Step2.Bp (L := L) (N := N) j b)).card : ℝ) ≤ (L : ℝ) ^ d := by
    exact_mod_cast nb_Bp_le b
  exact mul_le_mul_of_nonneg_right h' this

/-! ### `Loc S`, `𝔼θQ` and the coordinates at scale `j + 1` -/

theorem LS_o {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTo w (j + 1) ℓ' (LSO P j C V W b) ≤ ENNReal.ofReal (Cl * ((L : ℝ) ^ d * sO d L r mV mW)) := by
  have := H.hsO
  rw [LSO]
  refine (H.hloc (j + 1) H.hjN ℓ' H.hℓ' _ _ (isSmall_clo (isSmall_blockSet_of_mem hb))
    (subset_clo j _) _ H.SX_mem).trans ?_
  exact le_ofReal_mul H.hCl le_rfl (H.SX_o b)

theorem Q_mem {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    CmpInA (↑(nbhd j (blockSet (L := L) (N := N) j b) ∪ {P.a, P.b}) : Set (Lam d L N))
      (Q2O P j K b : SA c (Lam d L N)) := by
  classical
  rw [Q2O, if_pos H.hjN, AddSubmonoidClass.coe_finsetSum]
  exact CmpInA.sum _ fun X _ => H.hlocl X _ (isSmall_blockSet_of_mem hb).1 (K X)

omit H in
theorem nb_union_pts_le (A : Finset (Lam d L N)) (a b : Lam d L N) :
    nb j (A ∪ {a, b}) ≤ nb j A + 2 := by
  classical
  unfold nb blocks
  rw [image_union]
  refine (card_union_le _ _).trans (Nat.add_le_add_left ?_ _)
  exact card_image_le.trans ((card_insert_le _ _).trans (by simp))

theorem pq_pow_pts_le {b : Fin d → ℕ} :
    Step2.pq d ^ nb j (nbhd j (blockSet (L := L) (N := N) j b) ∪ {P.a, P.b}) ≤
      Step2.Q1 d * Step2.pq d ^ 2 := by
  have h1 := Step2.one_le_pq H.hd
  calc Step2.pq d ^ nb j (nbhd j (blockSet (L := L) (N := N) j b) ∪ {P.a, P.b})
      ≤ Step2.pq d ^ (nb j (nbhd j (blockSet (L := L) (N := N) j b)) + 2) :=
        pow_le_pow_right₀ h1 (nb_union_pts_le _ _ _)
    _ = Step2.pq d ^ nb j (nbhd j (blockSet (L := L) (N := N) j b)) * Step2.pq d ^ 2 := pow_add _ _ _
    _ ≤ Step2.Q1 d * Step2.pq d ^ 2 :=
        mul_le_mul_of_nonneg_right (Step2.pq_pow_le_Q1 H.hd H.hj.le b) (by positivity)

theorem Q_o {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTo w (j + 1) ℓ' (EthO C (Q2O P j K b)) ≤
      ENNReal.ofReal (Step2.Q1 d * Step2.pq d ^ 2 * (cS * (Cl * k))) := by
  classical
  have hk := H.hk; have hCl := H.hCl; have hcS := H.hcS
  have hpq := Step2.one_le_pq H.hd
  refine (oTo_EthO_le2A H.hd H.hLp H.hj H.hℓ' H.hℓC H.hsum H.hC (H.Q_mem hb)).trans ?_
  refine le_ofReal_mul (mul_nonneg H.hQ0 (by positivity))
    (ENNReal.ofReal_le_ofReal H.pq_pow_pts_le) ?_
  rw [Q2O, if_pos H.hjN]
  refine (oTo_sum_le w _ _ _ _).trans ((le_ofReal_sum_const _ (mul_nonneg hCl hk) fun X hX => ?_).trans
    (ENNReal.ofReal_le_ofReal ?_))
  · obtain ⟨hs, hbX⟩ := mem_smallSets_filter.1 hX
    exact (H.hloc j H.hj ℓ H.hℓ X _ hs hbX (K X) (H.hKl X hs)).trans
      (le_ofReal_mul hCl le_rfl (H.hKk X hs))
  · exact mul_le_mul_of_nonneg_right (H.hcount b hb) (mul_nonneg hCl hk)

theorem huO : 0 ≤ BHO.uO d L r mV mW k Cl cS := by
  unfold BHO.uO
  have hpq := Step2.one_le_pq H.hd
  exact add_nonneg (add_nonneg (mul_nonneg H.hQ0 H.hmV) (mul_nonneg
    (mul_nonneg H.hQ0 (by positivity))
    (mul_nonneg (by linarith [H.hcS]) (mul_nonneg H.hCl H.hk))))
    (mul_nonneg H.hCl (mul_nonneg (pow_nonneg H.hL0.le d) H.hsO))

theorem uVp_o {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTo w (j + 1) ℓ' (uVpO P j C V W K b) ≤ ENNReal.ofReal (BHO.uO d L r mV mW k Cl cS) := by
  have p1 := mul_nonneg H.hQ0 H.hmV
  have hpq := Step2.one_le_pq H.hd
  have p2 := mul_nonneg (mul_nonneg H.hQ0 (by positivity : (0 : ℝ) ≤ Step2.pq d ^ 2))
    (mul_nonneg (by linarith [H.hcS] : (0 : ℝ) ≤ cS) (mul_nonneg H.hCl H.hk))
  have p3 := mul_nonneg H.hCl (mul_nonneg (pow_nonneg H.hL0.le d) H.hsO)
  rw [uVpO]
  refine (oTo_sub_le w _ _ _ _).trans ?_
  exact le_ofReal_add (add_nonneg p1 p2) p3 ((oTo_sub_le w _ _ _ _).trans
    (le_ofReal_add p1 p2 (H.Vpr_o hb) (H.Q_o hb))) (H.LS_o hb)

/-- **`‖V^{obs}_{j+1}(B)‖_{T_{j+1}(ℓ')} ≤ 2 (Q₁ m_V + Q₁ c_S C_l k + C_l L^d s^{obs})`.** -/
theorem Vp_o {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTo w (j + 1) ℓ' (VpO P j C V W K b) ≤ ENNReal.ofReal (2 * BHO.uO d L r mV mW k Cl cS) := by
  have h0 := H.huO
  have hh : (0 : ℝ) < (L : ℝ) ^ (j + 1) := pow_pos H.hL0 _
  have e0 : oTo w (j + 1) ℓ' (algebraMap ℂ (OE c (Lam d L N)) (upB P j C V W K b)) = 0 :=
    oTo_algebraMap w _ _ _
  have e1 : oTo w (j + 1) ℓ' (upO P j C V W K b) ≤ ENNReal.ofReal (BHO.uO d L r mV mW k Cl cS) := by
    rw [upO, oTo_πobs]; exact (oTo_epsO_le w hh H.hℓ' _).trans (H.uVp_o hb)
  have e2 : oTo w (j + 1) ℓ' (uVpO P j C V W K b -
      algebraMap ℂ (OE c (Lam d L N)) (upB P j C V W K b)) ≤
      ENNReal.ofReal (BHO.uO d L r mV mW k Cl cS) := by
    refine (oTo_sub_le w _ _ _ _).trans ?_
    rw [e0, add_zero]; exact H.uVp_o hb
  rw [VpO]
  refine (oTo_sub_le w _ _ _ _).trans ((add_le_add e2 e1).trans ?_)
  rw [← ENNReal.ofReal_add h0 h0]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- **`‖𝒲^{obs}_{j+1}(B)‖_{T_{j+1}(ℓ')} ≤ (1 + C_l L^d) s^{obs}`.** -/
theorem Wp_o {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTo w (j + 1) ℓ' (WpO P j C V W b) ≤
      ENNReal.ofReal (sO d L r mV mW + Cl * ((L : ℝ) ^ d * sO d L r mV mW)) := by
  rw [WpO]
  exact (oTo_sub_le w _ _ _ _).trans (le_ofReal_add H.hsO
    (mul_nonneg H.hCl (mul_nonneg (pow_nonneg H.hL0.le d) H.hsO)) (H.Sb_o hb) (H.LS_o hb))

end BHOU

end

end Obs2
