import Obs2.Est.WObs3
import Obs2.Flow.WickTotal
import Obs2.Flow.TotalMu

/-!
# The `V^{obs}` recursion, part 1: the absolute masses (`ℓ¹` over blocks)

With the pointed `loc^a`, the coupling of `σ_a` is spread over the blocks (`TotalMu`): the
quantity that obeys a recursion with leading coefficient `1` is the `ℓ¹` sum of the block masses
`∑_B |m(V(B)_a)|`, not a supremum over blocks. For a linear functional `m` compatible with the
localisation (`LocMass`, e.g. `m₁ = mass1(-1)`) and vanishing on constants:

* `sum_norm_locAp_blocks`: `∑_{B ⊆ X} |m(loc^a_{X,B}F)| = |m(F)|` (the weights are `≥ 0` with sum `1`);
* **`abs_mass_step`**: `∑_{B_+} |m(V_{j+1}(B_+)_a)| ≤ ∑_B |m((𝔼θV(B))_a)| + ∑_{X ∈ 𝒮_j} |m(K(X)_a)|
    + ∑_B |m(S(B)_a)|`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 LocObs

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

/-- **`∑_{B ⊆ X} |m(loc^a_{X,B} F)| = |m(F)|`.** -/
theorem sum_norm_locAp_blocks {a : Lam d L N} {m : Alg d L N →ₗ[ℂ] ℂ} (hm : LocMass c a m)
    {j : ℕ} {X : Finset (Lam d L N)} (hX : IsPolymer j X) (hne : X.Nonempty) (F : Alg d L N) :
    ∑ b ∈ blocks j X, ‖m (locAp c a X (blockSet j b) F)‖ = ‖m F‖ := by
  by_cases ha : a ∈ X
  · have h : ∀ b ∈ blocks j X, ‖m (locAp c a X (blockSet j b) F)‖ =
        if blk j a = b then ‖m F‖ else 0 := by
      intro b hb
      rw [locAp_of_mem _ ha]
      split_ifs with h
      · rw [hm.mem X _ F (blockSet_subset_of_mem_blocks hX hb) (mem_blockSet.2 h)]
      · rw [locA_eq_zero _ (fun h' => h (mem_blockSet.1 h')), map_zero, norm_zero]
    rw [sum_congr rfl h, sum_ite_eq, if_pos (blk_mem_blocks ha)]
  · have h : ∀ b ∈ blocks j X, ‖m (locAp c a X (blockSet j b) F)‖ =
        ((blockSet (L := L) (N := N) j b).card : ℝ) / (X.card : ℝ) * ‖m F‖ := by
      intro b _
      rw [locAp_of_not_mem _ ha, map_smul, hm.pt, smul_eq_mul, norm_mul, norm_div,
        Complex.norm_natCast, Complex.norm_natCast]
    rw [sum_congr rfl h, ← sum_mul, ← sum_div]
    have hc : ∑ b ∈ blocks j X, ((blockSet (L := L) (N := N) j b).card : ℝ) = (X.card : ℝ) := by
      rw [← Nat.cast_sum, ← card_biUnion (pairwiseDisjoint_blockSet j _), biUnion_blocks hX]
    rw [hc, div_self (Nat.cast_ne_zero.2 (card_ne_zero.2 hne)), one_mul]

section Step

variable (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
  (V W : OFam c d L N) (K : OAct c d L N)

theorem m_VpO_a (m : Alg d L N →ₗ[ℂ] ℂ) (hm0 : ∀ r : ℂ, m (algebraMap ℂ (Alg d L N) r) = 0)
    (b : Fin d → ℕ) :
    m (VpO P j C V W K b : SA c (Lam d L N)).a =
      m (VprO C V b : SA c (Lam d L N)).a - m (EthO C (Q2O P j K b) : SA c (Lam d L N)).a -
        m (LSO P j C V W b : SA c (Lam d L N)).a := by
  have hup : (upO P j C V W K b : SA c (Lam d L N)).a =
      algebraMap ℂ (Alg d L N) (ε (uVpO P j C V W K b : SA c (Lam d L N)).a) := by
    show cmp true (πobs (epsO (uVpO P j C V W K b)) : SA c (Lam d L N)) = _
    rw [cmp_πobs]; rfl
  have halg : ((algebraMap ℂ (OE c (Lam d L N)) (upB P j C V W K b) : OE c (Lam d L N)) :
      SA c (Lam d L N)).a = 0 := by
    rw [Subalgebra.coe_algebraMap]; exact algebraMap_a _
  have h1 : (VpO P j C V W K b : SA c (Lam d L N)).a =
      (uVpO P j C V W K b : SA c (Lam d L N)).a -
        ((algebraMap ℂ (OE c (Lam d L N)) (upB P j C V W K b) : OE c (Lam d L N)) :
          SA c (Lam d L N)).a - (upO P j C V W K b : SA c (Lam d L N)).a := rfl
  have h2 : (uVpO P j C V W K b : SA c (Lam d L N)).a =
      (VprO C V b : SA c (Lam d L N)).a - (EthO C (Q2O P j K b) : SA c (Lam d L N)).a -
        (LSO P j C V W b : SA c (Lam d L N)).a := rfl
  rw [h1, h2, halg, hup]
  simp only [map_sub, map_zero, hm0, sub_zero]

/-- **The absolute masses after one step.** -/
theorem abs_mass_step (hjN : j + 1 < N) (m : Alg d L N →ₗ[ℂ] ℂ)
    (hm0 : ∀ r : ℂ, m (algebraMap ℂ (Alg d L N) r) = 0) (hm : LocMass c P.a m) :
    ∑ c' ∈ blockIdx (L := L) (N := N) (j + 1), ‖m (Vnext2O P j C V W K c' : SA c (Lam d L N)).a‖ ≤
      ∑ b ∈ blockIdx (L := L) (N := N) j, ‖m (VprO C V b : SA c (Lam d L N)).a‖ +
        ∑ X ∈ smallSets (L := L) (N := N) j, ‖m (K X : SA c (Lam d L N)).a‖ +
        ∑ b ∈ blockIdx (L := L) (N := N) j, ‖m (SbO j C V W b : SA c (Lam d L N)).a‖ := by
  classical
  -- `V_{j+1}(B_+) = ∑_{B ⊆ B_+} V_{j+1}(B)`
  have h1 : ∀ c', ‖m (Vnext2O P j C V W K c' : SA c (Lam d L N)).a‖ ≤
      ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
        ‖m (VpO P j C V W K b : SA c (Lam d L N)).a‖ := by
    intro c'
    rw [Vnext2O, AddSubmonoidClass.coe_finset_sum, sum_a, map_sum]
    exact norm_sum_le _ _
  refine (sum_le_sum fun c' _ => h1 c').trans ?_
  rw [sum_blockIdx_succ j]
  -- one block
  have h2 : ∀ b, ‖m (VpO P j C V W K b : SA c (Lam d L N)).a‖ ≤
      ‖m (VprO C V b : SA c (Lam d L N)).a‖ + ‖m (EthO C (Q2O P j K b) : SA c (Lam d L N)).a‖ +
        ‖m (LSO P j C V W b : SA c (Lam d L N)).a‖ := by
    intro b
    rw [m_VpO_a P j C V W K m hm0 b]
    exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
  refine (sum_le_sum fun b _ => h2 b).trans ?_
  rw [sum_add_distrib, sum_add_distrib]
  refine add_le_add (add_le_add le_rfl ?_) ?_
  · -- the activity term
    have e1 : ∀ b, m (EthO C (Q2O P j K b) : SA c (Lam d L N)).a =
        ∑ X ∈ (smallSets (L := L) (N := N) j).filter (fun X => blockSet j b ⊆ X),
          m (locAp c P.a X (blockSet j b) (K X : SA c (Lam d L N)).a) := by
      intro b
      have h0 := (EthO_comp C (Q2O P j K b)).2.1 true
      simp only [cmp_true] at h0
      rw [h0]
      unfold Q2O
      rw [if_pos hjN, AddSubmonoidClass.coe_finset_sum, sum_a, map_sum, map_sum]
      exact sum_congr (by congr) fun X _ => hm.exp C X _ _
    have e2 : ∀ b, ‖m (EthO C (Q2O P j K b) : SA c (Lam d L N)).a‖ ≤
        ∑ X ∈ (smallSets (L := L) (N := N) j).filter (fun X => blockSet j b ⊆ X),
          ‖m (locAp c P.a X (blockSet j b) (K X : SA c (Lam d L N)).a)‖ := fun b => by
      rw [e1 b]; exact norm_sum_le _ _
    refine (sum_le_sum fun b _ => e2 b).trans (le_of_eq ?_)
    rw [sum_comm' (t' := smallSets (L := L) (N := N) j) (s' := fun X => blocks j X) ?_]
    · refine sum_congr rfl fun X hX => ?_
      have hs := mem_smallSets.1 hX
      exact sum_norm_locAp_blocks hm hs.1 hs.2.1.1 _
    · intro b X
      constructor
      · rintro ⟨hb, hX⟩
        obtain ⟨hXs, hbX⟩ := mem_filter.1 hX
        obtain ⟨x, hx⟩ := mem_blockIdx.1 hb
        exact ⟨mem_blocks.2 ⟨x, hbX hx, mem_blockSet.1 hx⟩, hXs⟩
      · rintro ⟨hb, hX⟩
        exact ⟨mem_blockIdx_of_mem_blocks hb,
          mem_filter.2 ⟨hX, blockSet_subset_of_mem_blocks (mem_smallSets.1 hX).1 hb⟩⟩
  · -- the localisation of `S(B_+)`
    rw [← sum_blockIdx_succ j, ← sum_blockIdx_succ j]
    refine sum_le_sum fun c' hc' => ?_
    have hne : (blockSet (L := L) (N := N) (j + 1) c').Nonempty := mem_blockIdx.1 hc'
    have e : ∀ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
        ‖m (LSO P j C V W b : SA c (Lam d L N)).a‖ =
          ‖m (locAp c P.a (blockSet (L := L) (N := N) (j + 1) c') (blockSet j b)
            (SXO j C V W (blockSet (L := L) (N := N) (j + 1) c') : SA c (Lam d L N)).a)‖ := by
      intro b hb
      show ‖m (locAp c P.a (Step2.Bp (L := L) (N := N) j b) (blockSet j b)
        (SXO j C V W (Step2.Bp (L := L) (N := N) j b) : SA c (Lam d L N)).a)‖ = _
      rw [Bp_eq_of_mem hb]
    rw [sum_congr rfl e, sum_norm_locAp_blocks hm
      (IsPolymer.of_succ (isPolymer_blockSet (j + 1) c')) hne,
      SXO, AddSubmonoidClass.coe_finset_sum, sum_a, map_sum]
    exact norm_sum_le _ _

end Step

end

end Obs2
