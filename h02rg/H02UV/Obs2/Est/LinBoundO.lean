import Obs2.Est.LinBO
import Obs2.Est.LinComp
import Obs2.Est.EstLoc
import Obs.StepObsSmallEst

/-!
# The contraction of the linear part with sources (`Step2.Map.LinBound` on `OE`, `w_ab = 0`)

* `locAp_contract`, `locBp_contract`: for a small set `X` and `F ∈ 𝒩(X^□)` with the charge of the
  `a` (`b`) component, vanishing unless `a ∈ X^□`:
  `‖F - loc^a_{X,X} F‖_{T_{j+1}(ℓ')} ≤ (C/L) ‖F‖_{T_j(ℓ)}` (both branches of the pointed `loc^a`).
* **`Llin2O_obs_bound`**: the single-source part of `𝓛(K)` is contracted,
  `A^{(|𝓑_{j+1}(U)| - 2^d)_+} ‖𝓛(K)(U)^{obs}‖_{T_{j+1}(ℓ')} ≤ C₀ (L^{-1} + A^{-η}) k` if
  `A^{(|𝓑_j(X)| - 2^d)_+} ‖K(X)^{obs}‖_{T_j(ℓ)} ≤ k` for connected `X`, all components of `K(X)`
  are local in `X^□`, `K(X)` is `U(1)`-invariant (`IsSymS`), and the `σ_a` (`σ_b`) component of
  `K(X)` vanishes unless `a ∈ X^□` (`b ∈ X^□`).
* **`Llin2O_bound`**: with the bulk part (`Step2.Llin2_bound_ts`, via `bulk_Llin2O`), the bound
  in the full norm.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD PolyAux ENNReal

variable {d L N : ℕ} [NeZero L]

/-! ### The pointed contractions -/

theorem locAp_contract (d : ℕ) (hd : 1 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧ ∃ L₀ : ℕ,
    ∀ (L : ℕ) [NeZero L], 2 ^ (d + 3) + 8 * d < L → L₀ ≤ L → ∀ N j : ℕ, j < N →
    ∀ ℓ ℓ' : ℝ, 0 < ℓ → 0 < ℓ' → ℓ' ≤ 2 * ℓ →
    ∀ X : Finset (Lam d L N), IsSmall j X → ∀ (c : Obs.Case) (a : Lam d L N),
    ∀ F ∈ NX (nbhd j X : Set (Lam d L N)), HasCharge (chargeA c.toObs) F →
      (a ∉ nbhd j X → F = 0) →
      Tj d (L : ℝ) (j + 1) ℓ' (F - locAp c a X X F) ≤
        ENNReal.ofReal (C / L) * Tj d (L : ℝ) j ℓ F := by
  obtain ⟨C1, hC1, L1, h1⟩ := exists_locA_contract2 d hd
  obtain ⟨C2, hC2, L2, h2⟩ := exists_odd_contract_pt d hd
  obtain ⟨C3, hC3, L3, h3⟩ := exists_even_contract_pt d hd
  refine ⟨max C1 (max C2 C3), le_max_of_le_left hC1, max L1 (max L2 L3), ?_⟩
  intro L _ hL hL₀ N j hj ℓ ℓ' hℓ hℓ' hℓℓ X hX c a F hF hFc hz
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have mono : ∀ C' : ℝ, C' ≤ max C1 (max C2 C3) →
      ENNReal.ofReal (C' / L) * Tj d (L : ℝ) j ℓ F ≤
        ENNReal.ofReal (max C1 (max C2 C3) / L) * Tj d (L : ℝ) j ℓ F := fun C' hC' =>
    mul_le_mul_right' (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hC' hL0)) _
  by_cases ha : a ∈ X
  · rw [locAp_of_mem _ ha]
    exact (h1 L hL (le_trans (le_max_left _ _) hL₀) N j hj ℓ ℓ' hℓ hℓ' hℓℓ X hX c.toObs a ha F hF
      hFc).trans (mono _ (le_max_left _ _))
  · rw [locAp_of_not_mem _ ha, div_self (Nat.cast_ne_zero.2 (card_ne_zero.2 hX.2.1.1)), one_smul]
    by_cases hn : a ∈ nbhd j X
    · cases c
      · exact (h2 L hL (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL₀) N j hj ℓ ℓ'
          hℓ hℓ' hℓℓ X hX (-1) a hn F hF (by simpa [chargeA, Case.toObs] using hFc)).trans
          (mono _ (le_trans (le_max_left _ _) (le_max_right _ _)))
      · exact (h3 L hL (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL₀) N j hj ℓ ℓ'
          hℓ hℓ' hℓℓ X hX a hn F hF (by simpa [chargeA, Case.toObs] using hFc)).trans
          (mono _ (le_trans (le_max_right _ _) (le_max_right _ _)))
    · rw [hz hn, locA_zero, sub_zero, Step.Tj_zero]
      exact zero_le

theorem locBp_contract (d : ℕ) (hd : 1 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧ ∃ L₀ : ℕ,
    ∀ (L : ℕ) [NeZero L], 2 ^ (d + 3) + 8 * d < L → L₀ ≤ L → ∀ N j : ℕ, j < N →
    ∀ ℓ ℓ' : ℝ, 0 < ℓ → 0 < ℓ' → ℓ' ≤ 2 * ℓ →
    ∀ X : Finset (Lam d L N), IsSmall j X → ∀ (c : Obs.Case) (b : Lam d L N),
    ∀ F ∈ NX (nbhd j X : Set (Lam d L N)), HasCharge (chargeB c.toObs) F →
      (b ∉ nbhd j X → F = 0) →
      Tj d (L : ℝ) (j + 1) ℓ' (F - locBp c b X X F) ≤
        ENNReal.ofReal (C / L) * Tj d (L : ℝ) j ℓ F := by
  obtain ⟨C1, hC1, L1, h1⟩ := exists_locB_contract2 d hd
  obtain ⟨C2, hC2, L2, h2⟩ := exists_odd_contract_pt d hd
  obtain ⟨C3, hC3, L3, h3⟩ := exists_even_contract_pt d hd
  refine ⟨max C1 (max C2 C3), le_max_of_le_left hC1, max L1 (max L2 L3), ?_⟩
  intro L _ hL hL₀ N j hj ℓ ℓ' hℓ hℓ' hℓℓ X hX c b F hF hFc hz
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have mono : ∀ C' : ℝ, C' ≤ max C1 (max C2 C3) →
      ENNReal.ofReal (C' / L) * Tj d (L : ℝ) j ℓ F ≤
        ENNReal.ofReal (max C1 (max C2 C3) / L) * Tj d (L : ℝ) j ℓ F := fun C' hC' =>
    mul_le_mul_right' (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hC' hL0)) _
  by_cases hb : b ∈ X
  · rw [locBp, if_pos hb]
    exact (h1 L hL (le_trans (le_max_left _ _) hL₀) N j hj ℓ ℓ' hℓ hℓ' hℓℓ X hX c.toObs b hb F hF
      hFc).trans (mono _ (le_max_left _ _))
  · rw [locBp, if_neg hb, div_self (Nat.cast_ne_zero.2 (card_ne_zero.2 hX.2.1.1)), one_smul]
    by_cases hn : b ∈ nbhd j X
    · cases c
      · exact (h2 L hL (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL₀) N j hj ℓ ℓ'
          hℓ hℓ' hℓℓ X hX 1 b hn F hF (by simpa [chargeB, Case.toObs] using hFc)).trans
          (mono _ (le_trans (le_max_left _ _) (le_max_right _ _)))
      · exact (h3 L hL (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL₀) N j hj ℓ ℓ'
          hℓ hℓ' hℓℓ X hX b hn F hF (by simpa [chargeB, Case.toObs] using hFc)).trans
          (mono _ (le_trans (le_max_right _ _) (le_max_right _ _)))
    · rw [hz hn, locB_zero, sub_zero, Step.Tj_zero]
      exact zero_le

/-! ### Components -/

variable {c : Obs.Case}

theorem oTo_eq_ab {w : Wt} (hw0 : w.ab = 0) (j : ℕ) (ℓ : ℝ) (F : OE c (Lam d L N)) :
    oTo w j ℓ F = w.a * Tj d (L : ℝ) j ℓ (F : SA c (Lam d L N)).a +
      w.b * Tj d (L : ℝ) j ℓ (F : SA c (Lam d L N)).b := by
  simp only [oTo, oTj, oNorm, coe_πobs, piobs_apply, hw0, zero_mul, add_zero]
  rw [show Tj d (L : ℝ) j ℓ (0 : Alg d L N) = 0 from tNorm_zero', zero_add]

theorem coe_sumO_a {ι : Type*} (s : Finset ι) (f : ι → OE c (Lam d L N)) :
    ((∑ i ∈ s, f i : OE c (Lam d L N)) : SA c (Lam d L N)).a = ∑ i ∈ s, (f i : SA c (Lam d L N)).a := by
  rw [AddSubmonoidClass.coe_finsetSum]; exact map_sum aL _ _

theorem coe_sumO_b {ι : Type*} (s : Finset ι) (f : ι → OE c (Lam d L N)) :
    ((∑ i ∈ s, f i : OE c (Lam d L N)) : SA c (Lam d L N)).b = ∑ i ∈ s, (f i : SA c (Lam d L N)).b := by
  rw [AddSubmonoidClass.coe_finsetSum]; exact map_sum bL _ _

theorem bulk_Llin2O (P : ObsPts d L N) {j : ℕ} (hN : j + 1 < N) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
    (K : OAct c d L N) (U : Finset (Lam d L N)) :
    bulk (Llin2O P j C K U) = Step2.Llin2 j C (bulkF K) U := by
  rw [Llin2O_eq P j C K hN U, Step2.Llin2_eq j C (bulkF K) hN U, map_add, map_sum, map_sum]
  congr 1
  all_goals (try (refine sum_congr rfl fun X _ => ?_))
  all_goals (try rw [bulk_EthO, map_sub, bulk_LocO2])

/-! ### The observable part -/

open Classical in
/-- **The contraction of the single-source part of the linear part.** -/
theorem Llin2O_obs_bound (d : ℕ) (hd : 2 ≤ d) : ∃ (C₀ η : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧ 0 < η ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓC C →
    ∀ (c : Obs.Case) (P : ObsPts d L N) (w : Wt), w.ab = 0 →
    ∀ K : OAct c d L N,
      (∀ X, IsConn j X → CmpIn (nbhd j X : Set (Lam d L N)) (K X : SA c (Lam d L N))) →
      (∀ X, IsConn j X → IsSymS (K X : SA c (Lam d L N))) →
      (∀ X, IsConn j X → P.a ∉ nbhd j X → (K X : SA c (Lam d L N)).a = 0) →
      (∀ X, IsConn j X → P.b ∉ nbhd j X → (K X : SA c (Lam d L N)).b = 0) →
      ∀ k : ℝ≥0∞, (∀ X, IsConn j X → ENNReal.ofReal (A ^ (nb j X - 2 ^ d)) * oTo w j ℓ (K X) ≤ k) →
      ∀ U : Finset (Lam d L N), IsConn (j + 1) U →
        ENNReal.ofReal (A ^ (nb (j + 1) U - 2 ^ d)) * oTo w (j + 1) ℓ' (Llin2O P j C K U) ≤
          ENNReal.ofReal (C₀ * ((L : ℝ)⁻¹ + A ^ (-η))) * k := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨cn, η, L₁, hcn, hη, hlin⟩ := lin_comp_bound d hd
  obtain ⟨Ca, hCa, La, hla⟩ := locAp_contract d hd1
  obtain ⟨Cb, hCb, Lb, hlb⟩ := locBp_contract d hd1
  set Cl := max Ca Cb
  refine ⟨2 * (cn * Cl + 1), η, max (max L₁ (2 ^ (d + 3) + 8 * d + 1)) (max La Lb),
    by positivity, hη, ?_⟩
  intro L _ hL
  have hL8 : 2 ^ (d + 3) + 8 * d < L :=
    lt_of_lt_of_le (Nat.lt_succ_self _) (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL)
  have hLa : La ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
  have hLb : Lb ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
  obtain ⟨A₀, hA₀, hA⟩ := hlin L (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL)
  refine ⟨A₀, hA₀, fun A hAA => ?_⟩
  intro N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC c P w hw0 K hloc hsym hza hzb k hk U hU
  have hj : j < N := by omega
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hA1 : 1 ≤ A := hA₀.trans hAA
  have hAη : 0 ≤ A ^ (-η) := Real.rpow_nonneg (by linarith) _
  have hClL : ∀ C' : ℝ, C' ≤ Cl → ∀ x : Alg d L N,
      ENNReal.ofReal (C' / L) * Tj d (L : ℝ) j ℓ x ≤ ENNReal.ofReal (Cl / L) * Tj d (L : ℝ) j ℓ x :=
    fun C' hC' x => mul_le_mul_right' (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right hC' hL0.le)) _
  have hcomp : ∀ X, IsConn j X → ENNReal.ofReal (A ^ (nb j X - 2 ^ d)) *
      (w.a * Tj d (L : ℝ) j ℓ (K X : SA c (Lam d L N)).a) ≤ k ∧
      ENNReal.ofReal (A ^ (nb j X - 2 ^ d)) *
      (w.b * Tj d (L : ℝ) j ℓ (K X : SA c (Lam d L N)).b) ≤ k := by
    intro X hX
    have h := hk X hX
    rw [oTo_eq_ab hw0] at h
    exact ⟨le_trans (mul_le_mul_left' le_self_add _) h,
      le_trans (mul_le_mul_left' le_add_self _) h⟩
  -- the `a` component
  have hEa := hA A hAA N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC P.a Cl (le_max_of_le_left hCa)
    (fun X => (K X : SA c (Lam d L N)).a)
    (fun X => (K X : SA c (Lam d L N)).a - locAp c P.a X X (K X : SA c (Lam d L N)).a) w.a k
    (fun X hX => (hla L hL8 hLa N j hj ℓ (2 * ℓ) hℓ (by positivity) le_rfl X hX c P.a _
      ((hloc X ⟨hX.1, hX.2.1⟩).a) (charges_of_isSymS (hsym X ⟨hX.1, hX.2.1⟩)).1
      (hza X ⟨hX.1, hX.2.1⟩)).trans (hClL _ (le_max_left _ _) _))
    (fun X hX hn => by rw [hza X ⟨hX.1, hX.2.1⟩ hn, locAp_zero, sub_zero])
    (fun X hX _ => (hloc X hX).a) (fun X hX => (hcomp X hX).1) U hU
  have hEb := hA A hAA N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC P.b Cl (le_max_of_le_left hCa)
    (fun X => (K X : SA c (Lam d L N)).b)
    (fun X => (K X : SA c (Lam d L N)).b - locBp c P.b X X (K X : SA c (Lam d L N)).b) w.b k
    (fun X hX => (hlb L hL8 hLb N j hj ℓ (2 * ℓ) hℓ (by positivity) le_rfl X hX c P.b _
      ((hloc X ⟨hX.1, hX.2.1⟩).b) (charges_of_isSymS (hsym X ⟨hX.1, hX.2.1⟩)).2.1
      (hzb X ⟨hX.1, hX.2.1⟩)).trans (hClL _ (le_max_right _ _) _))
    (fun X hX hn => by rw [hzb X ⟨hX.1, hX.2.1⟩ hn, locBp_zero, sub_zero])
    (fun X hX _ => (hloc X hX).b) (fun X hX => (hcomp X hX).2) U hU
  -- the components of `𝓛(K)(U)`
  have ea : (Llin2O P j C K U : SA c (Lam d L N)).a =
      (∑ X ∈ (Pj j univ).filter (fun X => IsSmall j X ∧ clo j X = U),
        ECC C (theta ((K X : SA c (Lam d L N)).a - locAp c P.a X X (K X : SA c (Lam d L N)).a))) +
      ∑ X ∈ (Pj j univ).filter (fun X => IsConn j X ∧ ¬ IsSmall j X ∧ clo j X = U),
        ECC C (theta (K X : SA c (Lam d L N)).a) := by
    rw [Llin2O_eq P j C K hjN U]
    show ((_ : OE c (Lam d L N)) : SA c (Lam d L N)).a + ((_ : OE c (Lam d L N)) : SA c (Lam d L N)).a = _
    rw [coe_sumO_a, coe_sumO_a]
    rfl
  have eb : (Llin2O P j C K U : SA c (Lam d L N)).b =
      (∑ X ∈ (Pj j univ).filter (fun X => IsSmall j X ∧ clo j X = U),
        ECC C (theta ((K X : SA c (Lam d L N)).b - locBp c P.b X X (K X : SA c (Lam d L N)).b))) +
      ∑ X ∈ (Pj j univ).filter (fun X => IsConn j X ∧ ¬ IsSmall j X ∧ clo j X = U),
        ECC C (theta (K X : SA c (Lam d L N)).b) := by
    rw [Llin2O_eq P j C K hjN U]
    show ((_ : OE c (Lam d L N)) : SA c (Lam d L N)).b + ((_ : OE c (Lam d L N)) : SA c (Lam d L N)).b = _
    rw [coe_sumO_b, coe_sumO_b]
    rfl
  rw [oTo_eq_ab hw0, ea, eb, mul_add]
  refine (add_le_add hEa hEb).trans ?_
  rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine mul_le_mul_right' (ENNReal.ofReal_le_ofReal ?_) _
  have hc1 : cn * Cl / L ≤ (cn * Cl + 1) * (L : ℝ)⁻¹ := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hc2 : A ^ (-η) ≤ (cn * Cl + 1) * A ^ (-η) :=
    le_mul_of_one_le_left hAη (by have : 0 ≤ cn * Cl := mul_nonneg hcn (le_max_of_le_left hCa); linarith)
  have hLi : 0 ≤ (L : ℝ)⁻¹ := by positivity
  calc cn * Cl / L + A ^ (-η) + (cn * Cl / L + A ^ (-η))
      ≤ (cn * Cl + 1) * (L : ℝ)⁻¹ + (cn * Cl + 1) * A ^ (-η) +
          ((cn * Cl + 1) * (L : ℝ)⁻¹ + (cn * Cl + 1) * A ^ (-η)) := by
        gcongr
    _ = 2 * (cn * Cl + 1) * ((L : ℝ)⁻¹ + A ^ (-η)) := by ring

end

end Obs2
