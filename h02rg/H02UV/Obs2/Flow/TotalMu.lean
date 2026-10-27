import Obs2.Flow.WickTotal
import Step2.Coup.CoupPast6
import Step2.Coup.CoupPast

/-!
# The total recursion of `μ^{(1)}, μ^{(2)}` with the pointed `loc^a`

With the pointed `loc^a` of `Obs2.Loc.Loc` (`locAp`: localisation at the point `a` also for
`a ∉ X`, weighted by `|Y|/|X|`), `loc^a_{X,·}` is additive over the blocks of `X` and
`Loc_{X,X}` extracts the **full** mass of `F_a` for every polymer `X` (`LocMass.sum_blocks`).
Hence, summed over all `j`-blocks:

* `total_LS`: `∑_B m(Loc_{B_+,B} S(B_+))_a = ∑_B m(S(B)_a)`;
* **`total_W_mass`**: `∑_B m(𝒲_{j+1}(B)_a) = 0`: the new remainder `𝒲^{obs}` carries no mass
  (with the earlier operator, the mass of `S(B_+)_a` for `a ∉ B_+` stayed in `𝒲^{obs}`);
* `total_Q`: `∑_B m(Q(B)_a) = ∑_{X ∈ 𝒮_j} m(K(X)_a)` (and with `𝔼θ`, `total_EQ`);
* `total_Wnext_mass`: `∑_{B_+} m(𝒲_{j+1}(B_+)_a) = ∑_{B_+} m((𝒲_{j+1}(B_+) - ∑_{B ⊆ B_+} 𝒲_{j+1}(B))_a)`,
  the product (nonlinear) part of `∏(1 + 𝒲_{j+1}(B)) - 1` only;
* **`total_mu_one`**, **`total_mu_two`**: the exact recursion of the **total** coupling
  `β = ∑_B m(V(B)_a)` (`β = -μ`): if `V(B)_a = β_B ψ̄_a` (Case 1) resp. `α_B + β_B ψ̄_aψ_a`
  (Case 2) and `V'(Λ)_∅ = V_{κ'}(Λ) + const`, then
  `β' = β (1 - ν' ∑_x C(a,x)) - ∑_{X ∈ 𝒮_j} m₁(K(X)_a) - ∑_B m₁((𝔼θ𝒲(B))_a)` resp.
  `β' = β (1 - ν'(∑_x C(a,x) + ∑_x C(x,a)) + g' 𝔩_C(a)) - ∑_X m₂(K(X)_a) - ∑_B m₂((𝔼θ𝒲(B))_a)`.

So the one-loop `μ` flow is exact for the total coupling, with remainders the activity term and
the `𝒲` term. Since `∑_B m(𝒲_j(B)_a)` is the product part only (`total_Wnext_mass`), the `𝒲` term
is `∑_B [m(e^{ℒ_C}𝒲_j(B)_a) - m(𝒲_j(B)_a)]` (the tadpole of the cubic part of `𝒲^{obs}`, which
contains the `(ν' - ν) w^{(1)}` part of `𝔫_j`) plus the product part.

**The per-block flow does not hold** (and is not meaningful any more): `V_{j+1}(B)_a` for blocks
`B ∌ a` with `B_+ ∌ a` receives `(|B|/|B_+|) m(S(B_+)_a) ψ̄_a`. The coupling of the flow
equations is the total `∑_B` (the coefficient of `σ_aψ̄_a` in `V^{obs}(Λ)`).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 LocObs

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

/-! ### Linear functionals compatible with the single-point localisation -/

/-- `m` is compatible with the localisation at `a`: it is reproduced by `loc^a_{X,Y}` for
`a ∈ Y ⊆ X` and by the point localisation, and it is invariant under `e^{ℒ_C}` on the image of
`loc^a`. -/
structure LocMass (c : Obs.Case) (a : Lam d L N) (m : Alg d L N →ₗ[ℂ] ℂ) : Prop where
  mem : ∀ (X Y : Finset (Lam d L N)) (F : Alg d L N), Y ⊆ X → a ∈ Y →
    m (locA c.toObs a X Y F) = m F
  pt : ∀ F : Alg d L N, m (locA c.toObs a {a} {a} F) = m F
  exp : ∀ (C : Matrix (Lam d L N) (Lam d L N) ℂ) (X Y : Finset (Lam d L N)) (F : Alg d L N),
    m (expLC C (locAp c a X Y F)) = m (locAp c a X Y F)

theorem sum_single_inter (a : Lam d L N) (Y : Finset (Lam d L N)) (f : Lam d L N → Alg d L N) :
    ∑ z ∈ Y ∩ {a}, f z = if a ∈ Y then f a else 0 := by
  split_ifs with h
  · rw [Finset.inter_singleton_of_mem h, sum_singleton]
  · rw [Finset.inter_singleton_of_notMem h, sum_empty]

theorem locOdd_single_form (a : Lam d L N) (X Y : Finset (Lam d L N)) (F : Alg d L N) :
    ∃ r : ℂ, locOdd (-1) {a} X Y F = r • psibar a := by
  unfold locOdd locGen
  rw [sum_single_inter]
  split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨0, by rw [smul_zero, zero_smul]⟩

theorem locEven_single_form (a : Lam d L N) (X Y : Finset (Lam d L N)) (F : Alg d L N) :
    ∃ r s : ℂ, locEven {a} X Y F = r • (1 : Alg d L N) + s • pbp a := by
  unfold locEven
  rw [locGen_one]
  unfold locGen
  rw [sum_single_inter]
  split_ifs
  · exact ⟨_, _, rfl⟩
  · refine ⟨ε F / (#(X ∩ {a}) : ℂ) * (#(Y ∩ {a}) : ℂ), 0, ?_⟩
    simp only [smul_zero, zero_smul, add_zero]

theorem locAp_one_form (a : Lam d L N) (X Y : Finset (Lam d L N)) (F : Alg d L N) :
    ∃ r : ℂ, locAp Obs.Case.one a X Y F = r • psibar a := by
  by_cases ha : a ∈ X
  · rw [locAp_one_of_mem Y ha]; exact locOdd_single_form a X Y F
  · rw [locAp_one_of_not_mem Y ha]
    obtain ⟨r, hr⟩ := locOdd_single_form a {a} {a} F
    exact ⟨_, by rw [hr, smul_smul]⟩

theorem locAp_two_form (a : Lam d L N) (X Y : Finset (Lam d L N)) (F : Alg d L N) :
    ∃ r s : ℂ, locAp Obs.Case.two a X Y F = r • (1 : Alg d L N) + s • pbp a := by
  by_cases ha : a ∈ X
  · rw [locAp_two_of_mem Y ha]; exact locEven_single_form a X Y F
  · rw [locAp_two_of_not_mem Y ha]
    obtain ⟨r, s, hr⟩ := locEven_single_form a {a} {a} F
    exact ⟨_, _, by rw [hr, smul_add, smul_smul, smul_smul]⟩

/-- `m₁ = mass1(-1)` is compatible with the localisation (Case (1)). -/
theorem locMass_one (a : Lam d L N) : LocMass .one a (mass1L (d := d) (L := L) (N := N) (-1)) where
  mem X Y F hYX haY := by
    show mass1 (-1) (locOdd (-1) {a} X Y F) = mass1 (-1) F
    rw [locOdd_single_eq' haY hYX, mass1_smul, mass1_psibar, mul_one]
  pt F := by
    show mass1 (-1) (locOdd (-1) {a} {a} {a} F) = mass1 (-1) F
    exact mass1_locOdd ⟨a, by simp⟩ (-1) F
  exp C X Y F := by
    obtain ⟨r, hr⟩ := locAp_one_form a X Y F
    show mass1 (-1) (expLC C (locAp Obs.Case.one a X Y F)) = mass1 (-1) (locAp Obs.Case.one a X Y F)
    rw [hr, map_smul, expLC_psibar]

/-- `m₂ = mass2` is compatible with the localisation (Case (2)). -/
theorem locMass_two (a : Lam d L N) : LocMass .two a (mass2L (d := d) (L := L) (N := N)) where
  mem X Y F hYX haY := by
    show mass2 (locEven {a} X Y F) = mass2 F
    rw [locEven_single_eq' haY hYX, mass2_loc]
  pt F := by
    show mass2 (locEven {a} {a} {a} F) = mass2 F
    exact mass2_locEven ⟨a, by simp⟩ F
  exp C X Y F := by
    obtain ⟨r, s, hr⟩ := locAp_two_form a X Y F
    show mass2 (expLC C (locAp Obs.Case.two a X Y F)) = mass2 (locAp Obs.Case.two a X Y F)
    rw [hr, mass2_expLC_loc, mass2_loc]

/-- **`Loc_{X,·}` extracts the full mass**: `∑_{B ∈ 𝓑_j(X)} m(loc^a_{X,B} F) = m(F)` for every
nonempty `j`-polymer `X` (both for `a ∈ X` and `a ∉ X`). -/
theorem LocMass.sum_blocks {a : Lam d L N} {m : Alg d L N →ₗ[ℂ] ℂ} (hm : LocMass c a m) {j : ℕ}
    {X : Finset (Lam d L N)} (hX : IsPolymer j X) (hne : X.Nonempty) (F : Alg d L N) :
    ∑ b ∈ blocks j X, m (locAp c a X (blockSet j b) F) = m F := by
  by_cases ha : a ∈ X
  · have h : ∀ b ∈ blocks j X, m (locAp c a X (blockSet j b) F) =
        if blk j a = b then m F else 0 := by
      intro b hb
      rw [locAp_of_mem _ ha]
      split_ifs with h
      · exact hm.mem X _ F (blockSet_subset_of_mem_blocks hX hb) (mem_blockSet.2 h)
      · rw [locA_eq_zero _ (fun h' => h (mem_blockSet.1 h')), map_zero]
    rw [sum_congr rfl h, sum_ite_eq, if_pos (blk_mem_blocks ha)]
  · have h : ∀ b ∈ blocks j X, m (locAp c a X (blockSet j b) F) =
        ((blockSet (L := L) (N := N) j b).card : ℂ) / (X.card : ℂ) * m F := by
      intro b _
      rw [locAp_of_not_mem _ ha, map_smul, hm.pt, smul_eq_mul]
    rw [sum_congr rfl h, ← sum_mul, ← sum_div]
    have hc : ∑ b ∈ blocks j X, ((blockSet (L := L) (N := N) j b).card : ℂ) = (X.card : ℂ) := by
      rw [← Nat.cast_sum, ← card_biUnion (pairwiseDisjoint_blockSet j _), biUnion_blocks hX]
    rw [hc, div_self (Nat.cast_ne_zero.2 (card_ne_zero.2 hne)), one_mul]

/-! ### Sums over all blocks -/

section Total

variable (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
  (V W : OFam c d L N) (K : OAct c d L N)

theorem sum_blockIdx_succ {M : Type*} [AddCommMonoid M] (G : (Fin d → ℕ) → M) :
    ∑ c' ∈ blockIdx (L := L) (N := N) (j + 1),
        ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'), G b =
      ∑ b ∈ blockIdx (L := L) (N := N) j, G b :=
  sum_blocks_succ (isPolymer_univ (j + 1)) G

/-- **`∑_B m(Loc_{B_+,B} S(B_+))_a = ∑_B m(S(B)_a)`.** -/
theorem total_LS (m : Alg d L N →ₗ[ℂ] ℂ) (hm : LocMass c P.a m) :
    ∑ b ∈ blockIdx (L := L) (N := N) j, m (LSO P j C V W b : SA c (Lam d L N)).a =
      ∑ b ∈ blockIdx (L := L) (N := N) j, m (SbO j C V W b : SA c (Lam d L N)).a := by
  rw [← sum_blockIdx_succ j, ← sum_blockIdx_succ j]
  refine sum_congr rfl fun c' hc' => ?_
  have hne : (blockSet (L := L) (N := N) (j + 1) c').Nonempty := mem_blockIdx.1 hc'
  have e : ∀ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
      m (LSO P j C V W b : SA c (Lam d L N)).a =
        m (locAp c P.a (blockSet (L := L) (N := N) (j + 1) c') (blockSet j b)
          (SXO j C V W (blockSet (L := L) (N := N) (j + 1) c') : SA c (Lam d L N)).a) := by
    intro b hb
    show m (locAp c P.a (Step2.Bp (L := L) (N := N) j b) (blockSet j b)
      (SXO j C V W (Step2.Bp (L := L) (N := N) j b) : SA c (Lam d L N)).a) = _
    rw [Bp_eq_of_mem hb]
  rw [sum_congr rfl e, hm.sum_blocks (IsPolymer.of_succ (isPolymer_blockSet (j + 1) c')) hne,
    SXO, AddSubmonoidClass.coe_finset_sum, sum_a, map_sum]

/-- **The new remainder carries no mass**: `∑_B m(𝒲_{j+1}(B)_a) = 0`. -/
theorem total_W_mass (m : Alg d L N →ₗ[ℂ] ℂ) (hm : LocMass c P.a m) :
    ∑ b ∈ blockIdx (L := L) (N := N) j, m (WpO P j C V W b : SA c (Lam d L N)).a = 0 := by
  have h : ∀ b, m (WpO P j C V W b : SA c (Lam d L N)).a =
      m (SbO j C V W b : SA c (Lam d L N)).a - m (LSO P j C V W b : SA c (Lam d L N)).a :=
    fun b => by
      rw [← map_sub]; rfl
  rw [sum_congr rfl fun b _ => h b, sum_sub_distrib, total_LS P j C V W m hm, sub_self]

/-- **The total one-loop recursion with the pointed `loc^a`** (no `𝒲_{j+1}` term). -/
theorem total_step_pt (m : Alg d L N →ₗ[ℂ] ℂ)
    (hm0 : ∀ r : ℂ, m (algebraMap ℂ (Alg d L N) r) = 0) (hm : LocMass c P.a m) :
    ∑ b ∈ blockIdx (L := L) (N := N) j, m (VpO P j C V W K b : SA c (Lam d L N)).a =
      ∑ b ∈ blockIdx (L := L) (N := N) j, m (VprO C V b : SA c (Lam d L N)).a -
        ∑ b ∈ blockIdx (L := L) (N := N) j, m (EthO C (Q2O P j K b) : SA c (Lam d L N)).a -
        m (FC C (VprLO j C V : SA c (Lam d L N)).a (VprLO j C V : SA c (Lam d L N)).e) -
        ∑ b ∈ blockIdx (L := L) (N := N) j, m (EthO C (W b) : SA c (Lam d L N)).a := by
  have h := total_step P j C V W K m hm0
  rw [sum_sub_distrib, total_W_mass P j C V W m hm, sub_zero] at h
  exact h

/-- **The activity term**: `∑_B m((𝔼θQ(B))_a) = ∑_{X ∈ 𝒮_j} m(K(X)_a)`. -/
theorem total_EQ (hjN : j + 1 < N) (m : Alg d L N →ₗ[ℂ] ℂ) (hm : LocMass c P.a m) :
    ∑ b ∈ blockIdx (L := L) (N := N) j, m (EthO C (Q2O P j K b) : SA c (Lam d L N)).a =
      ∑ X ∈ smallSets (L := L) (N := N) j, m (K X : SA c (Lam d L N)).a := by
  classical
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
  rw [sum_congr rfl fun b _ => e1 b]
  rw [sum_comm' (t' := smallSets (L := L) (N := N) j) (s' := fun X => blocks j X) ?_]
  · refine sum_congr rfl fun X hX => ?_
    have hs := mem_smallSets.1 hX
    exact hm.sum_blocks hs.1 hs.2.1.1 _
  · intro b X
    constructor
    · rintro ⟨hb, hX⟩
      obtain ⟨hXs, hbX⟩ := mem_filter.1 hX
      obtain ⟨x, hx⟩ := mem_blockIdx.1 hb
      exact ⟨mem_blocks.2 ⟨x, hbX hx, mem_blockSet.1 hx⟩, hXs⟩
    · rintro ⟨hb, hX⟩
      exact ⟨mem_blockIdx_of_mem_blocks hb,
        mem_filter.2 ⟨hX, blockSet_subset_of_mem_blocks (mem_smallSets.1 hX).1 hb⟩⟩

end Total

/-! ### The total recursions of `μ^{(1)}` and `μ^{(2)}` -/

section Mu

variable (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)

/-- **The total recursion of `μ^{(1)}`** (Case (1)): with `V(B)_a = β_B ψ̄_a` and
`V'(Λ)_∅ = V_{κ'}(Λ) + r`, the total `β = ∑_B β_B` satisfies
`β' = β (1 - ν' ∑_x C(a,x)) - ∑_{X ∈ 𝒮_j} m₁(K(X)_a) - ∑_B m₁((𝔼θ𝒲(B))_a)`. -/
theorem total_mu_one (V W : OFam .one d L N) (K : OAct .one d L N) (hjN : j + 1 < N)
    (β : (Fin d → ℕ) → ℂ) (hV : ∀ b, (V b : SA .one (Lam d L N)).a = β b • psibar P.a)
    (κ : Step2.Coup) (r : ℂ)
    (he : (VprLO j C V : SA .one (Lam d L N)).e = Step2.Vcoup κ univ + r • (1 : Alg d L N)) :
    ∑ b ∈ blockIdx (L := L) (N := N) j, mass1 (-1) (VpO P j C V W K b : SA .one (Lam d L N)).a =
      (∑ b ∈ blockIdx (L := L) (N := N) j, β b) * (1 - κ.nu * ∑ x, C P.a x) -
        ∑ X ∈ smallSets (L := L) (N := N) j, mass1 (-1) (K X : SA .one (Lam d L N)).a -
        ∑ b ∈ blockIdx (L := L) (N := N) j,
          mass1 (-1) (EthO C (W b) : SA .one (Lam d L N)).a := by
  have hm := locMass_one (d := d) (L := L) (N := N) P.a
  have h := total_step_pt P j C V W K (mass1L (-1)) (fun r => mass1_algebraMap (-1) r) hm
  rw [total_EQ P j C K hjN _ hm] at h
  have hpr : ∀ b, (VprO C V b : SA .one (Lam d L N)).a = β b • psibar P.a := fun b => by
    have h0 := (EthO_comp C (V b)).2.1 true
    simp only [cmp_true] at h0
    rw [VprO, h0, hV b, map_smul, expLC_psibar]
  have hL : (VprLO j C V : SA .one (Lam d L N)).a =
      (∑ b ∈ blockIdx (L := L) (N := N) j, β b) • psibar P.a := by
    rw [VprLO, AddSubmonoidClass.coe_finset_sum, sum_a, sum_smul]
    exact sum_congr rfl fun b _ => hpr b
  rw [hL, he] at h
  have h1 : ∀ b, (mass1L (d := d) (L := L) (N := N) (-1)) (VprO C V b : SA .one (Lam d L N)).a =
      β b := fun b => by
    show mass1 (-1) _ = _
    rw [hpr b, mass1_smul, mass1_psibar, mul_one]
  simp only [h1] at h
  have h2 : (mass1L (d := d) (L := L) (N := N) (-1)) (FC C
      ((∑ b ∈ blockIdx (L := L) (N := N) j, β b) • psibar P.a)
      (Step2.Vcoup κ univ + r • (1 : Alg d L N))) =
      (∑ b ∈ blockIdx (L := L) (N := N) j, β b) * (κ.nu * ∑ x, C P.a x) :=
    total_FC_one C P.a κ r _
  rw [h2] at h
  have e : ∀ F : Alg d L N, (mass1L (d := d) (L := L) (N := N) (-1)) F = mass1 (-1) F :=
    fun _ => rfl
  simp only [e] at h
  rw [h]; ring

/-- **The total recursion of `μ^{(2)}`** (Case (2)): with `V(B)_a = α_B + β_B ψ̄_aψ_a` and
`V'(Λ)_∅ = V_{κ'}(Λ) + r`, the total `β = ∑_B β_B` satisfies
`β' = β (1 - ν'(∑_x C(a,x) + ∑_x C(x,a)) + g' 𝔩_C(a)) - ∑_X m₂(K(X)_a) - ∑_B m₂((𝔼θ𝒲(B))_a)`. -/
theorem total_mu_two (V W : OFam .two d L N) (K : OAct .two d L N) (hjN : j + 1 < N)
    (α β : (Fin d → ℕ) → ℂ)
    (hV : ∀ b, (V b : SA .two (Lam d L N)).a = α b • (1 : Alg d L N) + β b • pbp P.a)
    (κ : Step2.Coup) (r : ℂ)
    (he : (VprLO j C V : SA .two (Lam d L N)).e = Step2.Vcoup κ univ + r • (1 : Alg d L N)) :
    ∑ b ∈ blockIdx (L := L) (N := N) j, mass2 (VpO P j C V W K b : SA .two (Lam d L N)).a =
      (∑ b ∈ blockIdx (L := L) (N := N) j, β b) *
          (1 - κ.nu * (∑ x, C P.a x + ∑ x, C x P.a) + κ.g * lfunC C P.a) -
        ∑ X ∈ smallSets (L := L) (N := N) j, mass2 (K X : SA .two (Lam d L N)).a -
        ∑ b ∈ blockIdx (L := L) (N := N) j, mass2 (EthO C (W b) : SA .two (Lam d L N)).a := by
  have hm := locMass_two (d := d) (L := L) (N := N) P.a
  have h := total_step_pt P j C V W K mass2L (fun r => mass2_algebraMap r) hm
  rw [total_EQ P j C K hjN _ hm] at h
  have hpr : ∀ b, ∃ α' : ℂ, (VprO C V b : SA .two (Lam d L N)).a =
      α' • (1 : Alg d L N) + β b • pbp P.a := fun b => by
    obtain ⟨s, hs⟩ := expLC_pbp C P.a
    refine ⟨α b + β b * s, ?_⟩
    have h0 := (EthO_comp C (V b)).2.1 true
    simp only [cmp_true] at h0
    rw [VprO, h0, hV b, map_add, map_smul, map_smul, expLC_one', hs, smul_add, smul_smul, add_smul]
    abel
  choose α' hα' using hpr
  have hL : (VprLO j C V : SA .two (Lam d L N)).a =
      (∑ b ∈ blockIdx (L := L) (N := N) j, α' b) • (1 : Alg d L N) +
        (∑ b ∈ blockIdx (L := L) (N := N) j, β b) • pbp P.a := by
    rw [VprLO, AddSubmonoidClass.coe_finset_sum, sum_a, sum_smul, sum_smul, ← sum_add_distrib]
    exact sum_congr rfl fun b _ => hα' b
  rw [hL, he] at h
  have h1 : ∀ b, (mass2L (d := d) (L := L) (N := N)) (VprO C V b : SA .two (Lam d L N)).a =
      β b := fun b => by
    show mass2 _ = _
    rw [hα' b, mass2_loc]
  simp only [h1] at h
  have h2 : (mass2L (d := d) (L := L) (N := N)) (FC C
      ((∑ b ∈ blockIdx (L := L) (N := N) j, α' b) • (1 : Alg d L N) +
        (∑ b ∈ blockIdx (L := L) (N := N) j, β b) • pbp P.a)
      (Step2.Vcoup κ univ + r • (1 : Alg d L N))) =
      (∑ b ∈ blockIdx (L := L) (N := N) j, β b) *
        (κ.nu * (∑ x, C P.a x + ∑ x, C x P.a) - κ.g * lfunC C P.a) :=
    total_FC_two C P.a κ r _ _
  rw [h2] at h
  have e : ∀ F : Alg d L N, (mass2L (d := d) (L := L) (N := N)) F = mass2 F := fun _ => rfl
  simp only [e] at h
  rw [h]; ring

end Mu

end

end Obs2
