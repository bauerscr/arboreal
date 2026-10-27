import Obs2.Est.LinBoundOL
import Obs2.Est.EstAB

/-!
# The contraction of the linear part on the `σ_aσ_b` sector (`w_{ab} > 0`)

The `ab` copy of `Obs2.Llin2O_obs_bound` / `Obs2.Llin2O_obs_boundL`. On anchored elements
without one-point parts (`K(X) ∈ anc P X`, i.e. `K(X)_a = K(X)_b = 0` and `K(X)_{ab} = 0` unless
`X ∩ {a,b} ≠ ∅`) the observable norm is `w_{ab}‖K(X)_{ab}‖` (`oTo_of_ab`, any weights), and
`(1 - loc^{ab}_{X,X})` contracts by `C/L` on small sets (`exists_LocO2_anch_contract`).

* `lin_comp_bound2L`: `Obs2.lin_comp_boundL` for an `H` vanishing unless `a ∈ X^□` or
  `b ∈ X^□` (split `H = H·1[a ∈ X^□] + H·1[a ∉ X^□]`; constant doubled);
* **`Llin2O_ab_boundL`**: the `ab` sector of `𝓛(K)` is contracted, output regulator `λA`;
* **`Llin2O_ab_bound`**: the same with `λ = 1`;
* `Llin2O_mem_ab`: `𝓛(K)(U) ∈ abSub` if all `K(X) ∈ abSub`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD PolyAux ENNReal

variable {d L N : ℕ} [NeZero L]

open Classical in
/-- **The contraction of the linear part, one component, two base points.** -/
theorem lin_comp_bound2L (d : ℕ) (hd : 2 ≤ d) : ∃ (cn η : ℝ) (L₀ : ℕ), 0 ≤ cn ∧ 0 < η ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∀ lam : ℝ, 1 ≤ lam → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓC C →
    ∀ (a b : Lam d L N) (Cl : ℝ), 0 ≤ Cl →
    ∀ (G H : Finset (Lam d L N) → Alg d L N) (m k : ENNReal),
      (∀ X, IsSmall j X → Tj d (L : ℝ) (j + 1) (2 * ℓ) (H X) ≤
        ENNReal.ofReal (Cl / L) * Tj d (L : ℝ) j ℓ (G X)) →
      (∀ X, IsSmall j X → a ∉ nbhd j X → b ∉ nbhd j X → H X = 0) →
      (∀ X, IsConn j X → ¬ IsSmall j X → G X ∈ NX (nbhd j X : Set (Lam d L N))) →
      (∀ X, IsConn j X → ENNReal.ofReal (A ^ (nb j X - 2 ^ d)) * (m * Tj d (L : ℝ) j ℓ (G X)) ≤ k) →
      ∀ U : Finset (Lam d L N), IsConn (j + 1) U →
        ENNReal.ofReal ((lam * A) ^ (nb (j + 1) U - 2 ^ d)) * (m * Tj d (L : ℝ) (j + 1) ℓ'
          ((∑ X ∈ (Pj j univ).filter (fun X => IsSmall j X ∧ clo j X = U), ECC C (theta (H X))) +
            ∑ X ∈ (Pj j univ).filter (fun X => IsConn j X ∧ ¬ IsSmall j X ∧ clo j X = U),
              ECC C (theta (G X)))) ≤
          ENNReal.ofReal (2 * (cn * Cl / L + A ^ (-η))) * k := by
  obtain ⟨cn, η, L₀, hcn, hη, h⟩ := lin_comp_boundL d hd
  refine ⟨cn, η, L₀, hcn, hη, fun L _ hL lam hlam => ?_⟩
  obtain ⟨A₀, hA₀, hA⟩ := h L hL lam hlam
  refine ⟨A₀, hA₀, fun A hAA N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC a b Cl hCl G H m k hH hz hG
    hk U hU => ?_⟩
  set H₁ : Finset (Lam d L N) → Alg d L N := fun X => if a ∈ nbhd j X then H X else 0
  set H₂ : Finset (Lam d L N) → Alg d L N := fun X => if a ∈ nbhd j X then 0 else H X
  set G₂ : Finset (Lam d L N) → Alg d L N := fun X => if IsSmall j X then G X else 0
  have h1 := hA A hAA N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC a Cl hCl G H₁ m k
    (fun X hX => by
      simp only [H₁]; split_ifs
      · exact hH X hX
      · rw [Step.Tj_zero]; exact zero_le)
    (fun X _ ha => by simp only [H₁, if_neg ha]) hG hk U hU
  have h2 := hA A hAA N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC b Cl hCl G₂ H₂ m k
    (fun X hX => by
      simp only [H₂, G₂, if_pos hX]; split_ifs
      · rw [Step.Tj_zero]; exact zero_le
      · exact hH X hX)
    (fun X hX hb => by
      simp only [H₂]; split_ifs with ha
      · rfl
      · exact hz X hX ha hb)
    (fun X _ hs => by simp only [G₂, if_neg hs]; exact zero_mem _)
    (fun X hX => by
      simp only [G₂]; split_ifs
      · exact hk X hX
      · rw [Step.Tj_zero, mul_zero, mul_zero]; exact zero_le) U hU
  have eH : ∀ X, H X = H₁ X + H₂ X := fun X => by
    simp only [H₁, H₂]; split_ifs <;> simp
  have eS : (∑ X ∈ (Pj j univ).filter (fun X => IsSmall j X ∧ clo j X = U), ECC C (theta (H X))) =
      (∑ X ∈ (Pj j univ).filter (fun X => IsSmall j X ∧ clo j X = U), ECC C (theta (H₁ X))) +
      ∑ X ∈ (Pj j univ).filter (fun X => IsSmall j X ∧ clo j X = U), ECC C (theta (H₂ X)) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun X _ => ?_
    rw [eH X, map_add, map_add]
  have eL : (∑ X ∈ (Pj j univ).filter (fun X => IsConn j X ∧ ¬ IsSmall j X ∧ clo j X = U),
      ECC C (theta (G₂ X))) = 0 := by
    refine sum_eq_zero fun X hX => ?_
    rw [mem_filter] at hX
    simp only [G₂, if_neg hX.2.2.1, map_zero]
  rw [eL, add_zero] at h2
  rw [eS]
  set S₁ := ∑ X ∈ (Pj j univ).filter (fun X => IsSmall j X ∧ clo j X = U), ECC C (theta (H₁ X))
  set S₂ := ∑ X ∈ (Pj j univ).filter (fun X => IsSmall j X ∧ clo j X = U), ECC C (theta (H₂ X))
  set Lg := ∑ X ∈ (Pj j univ).filter (fun X => IsConn j X ∧ ¬ IsSmall j X ∧ clo j X = U),
    ECC C (theta (G X))
  have htri : Tj d (L : ℝ) (j + 1) ℓ' (S₁ + S₂ + Lg) ≤
      Tj d (L : ℝ) (j + 1) ℓ' (S₁ + Lg) + Tj d (L : ℝ) (j + 1) ℓ' S₂ := by
    rw [show S₁ + S₂ + Lg = (S₁ + Lg) + S₂ by abel]
    exact tNorm_add_le _ _
  have hc0 : 0 ≤ cn * Cl / L + A ^ (-η) := by
    have hA1 : (0 : ℝ) ≤ A := by linarith
    have := Real.rpow_nonneg hA1 (-η)
    have : 0 ≤ cn * Cl / L := by positivity
    linarith
  calc ENNReal.ofReal ((lam * A) ^ (nb (j + 1) U - 2 ^ d)) *
        (m * Tj d (L : ℝ) (j + 1) ℓ' (S₁ + S₂ + Lg))
      ≤ ENNReal.ofReal ((lam * A) ^ (nb (j + 1) U - 2 ^ d)) *
          (m * Tj d (L : ℝ) (j + 1) ℓ' (S₁ + Lg)) +
        ENNReal.ofReal ((lam * A) ^ (nb (j + 1) U - 2 ^ d)) *
          (m * Tj d (L : ℝ) (j + 1) ℓ' S₂) := by
        rw [← mul_add, ← mul_add]; gcongr
    _ ≤ ENNReal.ofReal (cn * Cl / L + A ^ (-η)) * k +
          ENNReal.ofReal (cn * Cl / L + A ^ (-η)) * k := add_le_add h1 h2
    _ = ENNReal.ofReal (2 * (cn * Cl / L + A ^ (-η))) * k := by
        rw [← add_mul, ← ENNReal.ofReal_add hc0 hc0, two_mul]

variable {c : Obs.Case}

theorem Llin2O_mem_ab (P : ObsPts d L N) {j : ℕ} (hN : j + 1 < N)
    (C : Matrix (Lam d L N) (Lam d L N) ℂ) (K : OAct c d L N)
    (hK : ∀ X, K X ∈ (abSub : Subalgebra ℂ (OE c (Lam d L N)))) (U : Finset (Lam d L N)) :
    Llin2O P j C K U ∈ (abSub : Subalgebra ℂ (OE c (Lam d L N))) := by
  rw [Llin2O_eq P j C K hN U]
  refine add_mem (sum_mem fun X _ => EthO_mem_ab C (sub_mem (hK X) (LocO2_mem_ab P X X (hK X))))
    (sum_mem fun X _ => EthO_mem_ab C (hK X))

theorem coe_sumO_ab {ι : Type*} (s : Finset ι) (f : ι → OE c (Lam d L N)) :
    ((∑ i ∈ s, f i : OE c (Lam d L N)) : SA c (Lam d L N)).ab =
      ∑ i ∈ s, (f i : SA c (Lam d L N)).ab := by
  rw [AddSubmonoidClass.coe_finsetSum]; exact map_sum abL _ _

open Classical in
theorem Llin2O_ab_eq (P : ObsPts d L N) {j : ℕ} (hN : j + 1 < N)
    (C : Matrix (Lam d L N) (Lam d L N) ℂ) (K : OAct c d L N) (U : Finset (Lam d L N)) :
    (Llin2O P j C K U : SA c (Lam d L N)).ab =
      (∑ X ∈ (Pj j univ).filter (fun X => IsSmall j X ∧ clo j X = U),
        ECC C (theta ((K X : SA c (Lam d L N)).ab -
          locABtXY P X X (K X : SA c (Lam d L N)).ab))) +
      ∑ X ∈ (Pj j univ).filter (fun X => IsConn j X ∧ ¬ IsSmall j X ∧ clo j X = U),
        ECC C (theta (K X : SA c (Lam d L N)).ab) := by
  rw [Llin2O_eq P j C K hN U]
  show ((_ : OE c (Lam d L N)) : SA c (Lam d L N)).ab +
    ((_ : OE c (Lam d L N)) : SA c (Lam d L N)).ab = _
  rw [coe_sumO_ab, coe_sumO_ab]
  rfl

open Classical in
/-- **The contraction of the `σ_aσ_b` part of the linear part** (output regulator `λA`, any
weights `w`, anchored `K`). -/
theorem Llin2O_ab_boundL (d : ℕ) (hd : 2 ≤ d) : ∃ (C₀ η : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧ 0 < η ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∀ lam : ℝ, 1 ≤ lam → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓC C →
    ∀ (c : Obs.Case) (P : ObsPts d L N) (w : Wt) (K : OAct c d L N),
      (∀ X, K X ∈ (abSub : Subalgebra ℂ (OE c (Lam d L N)))) →
      (∀ X, IsConn j X → K X ∈ (anc P X : Subalgebra ℂ (OE c (Lam d L N)))) →
      (∀ X, IsConn j X → (K X : SA c (Lam d L N)).ab ∈ NX (nbhd j X : Set (Lam d L N))) →
      (∀ X, IsConn j X → IsSymS (K X : SA c (Lam d L N))) →
      ∀ k : ℝ≥0∞, (∀ X, IsConn j X → ENNReal.ofReal (A ^ (nb j X - 2 ^ d)) * oTo w j ℓ (K X) ≤ k) →
      ∀ U : Finset (Lam d L N), IsConn (j + 1) U →
        ENNReal.ofReal ((lam * A) ^ (nb (j + 1) U - 2 ^ d)) * oTo w (j + 1) ℓ' (Llin2O P j C K U) ≤
          ENNReal.ofReal (C₀ * ((L : ℝ)⁻¹ + A ^ (-η))) * k := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨cn, η, L₁, hcn, hη, hlin⟩ := lin_comp_bound2L d hd
  obtain ⟨Cl, hCl, Lc, hlc⟩ := exists_LocO2_anch_contract d hd1
  refine ⟨2 * (cn * Cl + 1), η, max (max L₁ (2 ^ (d + 3) + 8 * d + 1)) Lc,
    by positivity, hη, ?_⟩
  intro L _ hL lam hlam
  have hL8 : 2 ^ (d + 3) + 8 * d < L :=
    lt_of_lt_of_le (Nat.lt_succ_self _) (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL)
  have hLc : Lc ≤ L := le_trans (le_max_right _ _) hL
  obtain ⟨A₀, hA₀, hA⟩ := hlin L (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL)
    lam hlam
  refine ⟨A₀, hA₀, fun A hAA => ?_⟩
  intro N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC c P w K hab hanc hloc hsym k hk U hU
  have hj : j < N := by omega
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hA1 : 1 ≤ A := hA₀.trans hAA
  have hAη : 0 ≤ A ^ (-η) := Real.rpow_nonneg (by linarith) _
  -- the single-set contraction, unweighted
  have hH : ∀ X, IsSmall j X → Tj d (L : ℝ) (j + 1) (2 * ℓ)
      ((K X : SA c (Lam d L N)).ab - locABtXY P X X (K X : SA c (Lam d L N)).ab) ≤
      ENNReal.ofReal (Cl / L) * Tj d (L : ℝ) j ℓ (K X : SA c (Lam d L N)).ab := by
    intro X hX
    have hc : IsConn j X := ⟨hX.1, hX.2.1⟩
    have h := hlc L hL8 hLc N j hj ℓ (2 * ℓ) hℓ (by positivity) le_rfl c P ⟨0, 0, 1⟩ X hX (K X)
      (hanc X hc) (hloc X hc) ((hasCharge_zero_iff _).1 (charges_of_isSymS (hsym X hc)).2.2)
    rw [oTo_of_ab _ _ _ (sub_mem (hab X) (LocO2_mem_ab P X X (hab X))), oTo_of_ab _ _ _ (hab X),
      ab_sub_LocO2, show ((⟨0, 0, 1⟩ : Wt).ab) = 1 from rfl, one_mul, one_mul] at h
    exact h
  have hz : ∀ X, IsSmall j X → P.a ∉ nbhd j X → P.b ∉ nbhd j X →
      (K X : SA c (Lam d L N)).ab - locABtXY P X X (K X : SA c (Lam d L N)).ab = 0 := by
    intro X hX ha hb
    have hne : ¬ (X ∩ P.pts).Nonempty := by
      rintro ⟨z, hz⟩
      rw [mem_inter, ObsPts.pts, mem_insert, mem_singleton] at hz
      rcases hz.2 with rfl | rfl
      · exact ha (subset_nbhd hX.1 hz.1)
      · exact hb (subset_nbhd hX.1 hz.1)
    rw [(hanc X ⟨hX.1, hX.2.1⟩).2.2 hne, locABtXY_zero, sub_zero]
  have hk' : ∀ X, IsConn j X → ENNReal.ofReal (A ^ (nb j X - 2 ^ d)) *
      (w.ab * Tj d (L : ℝ) j ℓ (K X : SA c (Lam d L N)).ab) ≤ k := fun X hX => by
    have h := hk X hX
    rwa [oTo_of_ab w j ℓ (hab X)] at h
  have hE := hA A hAA N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC P.a P.b Cl hCl
    (fun X => (K X : SA c (Lam d L N)).ab)
    (fun X => (K X : SA c (Lam d L N)).ab - locABtXY P X X (K X : SA c (Lam d L N)).ab) w.ab k
    hH hz (fun X hX _ => hloc X hX) hk' U hU
  rw [oTo_of_ab w _ _ (Llin2O_mem_ab P hjN C K hab U), Llin2O_ab_eq P hjN C K U]
  refine hE.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
  have hc1 : cn * Cl / L ≤ (cn * Cl + 1) * (L : ℝ)⁻¹ := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hc2 : A ^ (-η) ≤ (cn * Cl + 1) * A ^ (-η) :=
    le_mul_of_one_le_left hAη (by have : 0 ≤ cn * Cl := mul_nonneg hcn hCl; linarith)
  calc 2 * (cn * Cl / L + A ^ (-η))
      ≤ 2 * ((cn * Cl + 1) * (L : ℝ)⁻¹ + (cn * Cl + 1) * A ^ (-η)) := by gcongr
    _ = 2 * (cn * Cl + 1) * ((L : ℝ)⁻¹ + A ^ (-η)) := by ring

open Classical in
/-- **`Llin2O_ab_boundL` with `λ = 1`** (the `ab` copy of `Llin2O_obs_bound`). -/
theorem Llin2O_ab_bound (d : ℕ) (hd : 2 ≤ d) : ∃ (C₀ η : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧ 0 < η ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓC C →
    ∀ (c : Obs.Case) (P : ObsPts d L N) (w : Wt) (K : OAct c d L N),
      (∀ X, K X ∈ (abSub : Subalgebra ℂ (OE c (Lam d L N)))) →
      (∀ X, IsConn j X → K X ∈ (anc P X : Subalgebra ℂ (OE c (Lam d L N)))) →
      (∀ X, IsConn j X → (K X : SA c (Lam d L N)).ab ∈ NX (nbhd j X : Set (Lam d L N))) →
      (∀ X, IsConn j X → IsSymS (K X : SA c (Lam d L N))) →
      ∀ k : ℝ≥0∞, (∀ X, IsConn j X → ENNReal.ofReal (A ^ (nb j X - 2 ^ d)) * oTo w j ℓ (K X) ≤ k) →
      ∀ U : Finset (Lam d L N), IsConn (j + 1) U →
        ENNReal.ofReal (A ^ (nb (j + 1) U - 2 ^ d)) * oTo w (j + 1) ℓ' (Llin2O P j C K U) ≤
          ENNReal.ofReal (C₀ * ((L : ℝ)⁻¹ + A ^ (-η))) * k := by
  obtain ⟨C₀, η, L₀, hC₀, hη, h⟩ := Llin2O_ab_boundL d hd
  refine ⟨C₀, η, L₀, hC₀, hη, fun L _ hL => ?_⟩
  obtain ⟨A₀, hA₀, hA⟩ := h L hL 1 le_rfl
  refine ⟨A₀, hA₀, fun A hAA N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC c P w K hab hanc hloc hsym k hk
    U hU => ?_⟩
  have h := hA A hAA N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC c P w K hab hanc hloc hsym k hk U hU
  rwa [one_mul] at h

end

end Obs2
