import Obs2.Pair.PairSect
import Obs2.Est.EstAB

/-!
# The initial `σ_aσ_b` activity at coalescence: polymer-norm bound of `kRed` (`w_{ab} > 0`)

`kRed Y = π_{ab}(zLoc Y)`, `zLoc Y = ∑_{A ∈ 𝒮_Y} I^{Y∖A}K^A` (`Obs2.Pair.PairSect`). For weights with
`ℓ_{ab} ≤ ℓ_aℓ_b` the full norm is submultiplicative (`Obs.oT_mul_le`), and `‖π_{obs}π_{ab}F‖ =
ℓ_{ab}‖F_{ab}‖ ≤ ‖F‖`, so the `ab` part of `zLoc` is bounded by products of full norms of the
factors. With `ℓ_a = M_a^{-1}`, `ℓ_b = M_b^{-1}`, `ℓ_{ab} = (M_aM_b)^{-1}` (`M_• ≍ s|β_•|` the size
of the one-point parts) this is the bound `‖π_{ab}zLoc Y‖ ≲ M_aM_b`.

* `oTo_πab_le`, **`oTj_zLoc_le`**: `‖π_{ab}zLoc Y‖ ≤ ∑_{A∈𝒮_Y}∏_{B∈𝓑(Y∖A)}‖I(B)‖∏_{X∈Comp A}‖K(X)‖`;
* geometry of `𝒮_Y`: `sdiff_subset_of_mem_sY` (`Y∖A ⊆ D`), `nb_le_of_mem_sY`
  (`|𝓑(Y)| ≤ |𝓑(D)| + ∑_{X∈Comp A}|𝓑(X)|`), **`card_sY_le`** (`|𝒮_Y| ≤ 2^{|𝓑(D)|}`: `A` is fixed by
  `𝓑(A) ∩ 𝓑(D)`);
* **`kRed_poly_le`**: if `‖I(B)‖ ≤ ι` (`ι ≥ 1`) on the blocks of `D` and `A^{|𝓑(X)|}‖K(X)‖ ≤ 1` on
  connected `X`, then `A^{(|𝓑(Y)| - 2^d)_+}‖π_{obs}kRed Y‖ ≤ (2ιA)^{|𝓑(D)|}` for every `Y`
  (uniformly in `Y`, `j`, `N`);
* **`kRed_ab_poly_le`**: the same with the weights `(M_a^{-1}, M_b^{-1}, (M_aM_b)^{-1})`:
  `A^{(|𝓑(Y)| - 2^d)_+}‖kRed(Y)_{ab}‖_{T_j(ℓ)} ≤ M_aM_b(2ιA)^{|𝓑(D)|}`;
* `tNorm_seed_le`: the quartic seed `β_aβ_b ψ̄_aψ_aψ̄_bψ_b` at scale `h`:
  `≤ |β_aβ_b| ℓ²(|a−b|_1ℓ/h)²` (`Obs2.tNorm_m4_le`).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step FRD Obs2 ENNReal

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

/-! ### Norms -/

theorem oTo_πab_le (w : Wt) (j : ℕ) (ℓ : ℝ) (F : OE c (Lam d L N)) :
    oTo w j ℓ (πab F) ≤ oTj d L w j ℓ (F : SA c (Lam d L N)) := by
  have hab : πab F ∈ (abSub : Subalgebra ℂ (OE c (Lam d L N))) := by
    refine ⟨?_, ?_⟩ <;> rw [coe_πab, piab_apply]
  rw [oTo_of_ab w j ℓ hab]
  show w.ab * Tj d (L : ℝ) j ℓ (F : SA c (Lam d L N)).ab ≤
    Tj d (L : ℝ) j ℓ (F : SA c (Lam d L N)).e + w.a * Tj d (L : ℝ) j ℓ (F : SA c (Lam d L N)).a +
      w.b * Tj d (L : ℝ) j ℓ (F : SA c (Lam d L N)).b +
      w.ab * Tj d (L : ℝ) j ℓ (F : SA c (Lam d L N)).ab
  exact le_add_self

theorem oTj_prod_le {w : Wt} (hw : w.Sub) {j : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {ι : Type*}
    (s : Finset ι) (F : ι → OE c (Lam d L N)) :
    oTj d L w j ℓ ((∏ i ∈ s, F i : OE c (Lam d L N)) : SA c (Lam d L N)) ≤
      ∏ i ∈ s, oTj d L w j ℓ (F i : SA c (Lam d L N)) :=
  oT_prod_le (E := Dir d) (p := pPhi d) (pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) j) hℓ hw s F

theorem oTj_mul_le {w : Wt} (hw : w.Sub) {j : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (F G : OE c (Lam d L N)) :
    oTj d L w j ℓ ((F * G : OE c (Lam d L N)) : SA c (Lam d L N)) ≤
      oTj d L w j ℓ (F : SA c (Lam d L N)) * oTj d L w j ℓ (G : SA c (Lam d L N)) :=
  oT_mul_le (E := Dir d) (p := pPhi d) (pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) j) hℓ hw F G

theorem oTj_sumO_le {w : Wt} {j : ℕ} {ℓ : ℝ} {ι : Type*} (s : Finset ι)
    (F : ι → OE c (Lam d L N)) :
    oTj d L w j ℓ ((∑ i ∈ s, F i : OE c (Lam d L N)) : SA c (Lam d L N)) ≤
      ∑ i ∈ s, oTj d L w j ℓ (F i : SA c (Lam d L N)) := by
  rw [AddSubmonoidClass.coe_finsetSum]
  exact oT_sum_le (E := Dir d) (p := pPhi d) s _

variable {j : ℕ} {D : Finset (Lam d L N)} {z0 : Lam d L N}

/-- **The `ab` part of `zLoc` by products of full norms.** -/
theorem oTj_zLoc_le {w : Wt} (hw : w.Sub) {ℓ : ℝ} (hℓ : 0 < ℓ) (I : OFam c d L N)
    (K : OAct c d L N) (Y : Finset (Lam d L N)) :
    oTj d L w j ℓ (zLoc j D z0 I K Y : SA c (Lam d L N)) ≤
      ∑ A ∈ sY j D z0 Y, (∏ b ∈ blocks j (Y \ A), oTj d L w j ℓ (I b : SA c (Lam d L N))) *
        ∏ X ∈ Comp j A, oTj d L w j ℓ (K X : SA c (Lam d L N)) := by
  refine (oTj_sumO_le _ _).trans (sum_le_sum fun A _ => ?_)
  refine (oTj_mul_le hw hℓ _ _).trans (mul_le_mul' ?_ ?_)
  · exact oTj_prod_le hw hℓ _ _
  · exact oTj_prod_le hw hℓ _ _

/-! ### The geometry of `𝒮_Y` -/

theorem sdiff_subset_of_mem_sY {Y A : Finset (Lam d L N)} (hA : A ∈ sY j D z0 Y) :
    Y \ A ⊆ D := by
  intro y hy
  rw [mem_sdiff] at hy
  have hY : Y ⊆ A ∪ D := (mem_sY.1 hA).2 ▸ dComp_subset (j := j) (D := D) (z0 := z0) A
  rcases mem_union.1 (hY hy.1) with h | h
  · exact absurd h hy.2
  · exact h

theorem nb_le_of_mem_sY {Y A : Finset (Lam d L N)} (hA : A ∈ sY j D z0 Y) :
    nb j Y ≤ nb j D + ∑ X ∈ Comp j A, nb j X := by
  classical
  have hAp := (mem_sY.1 hA).1.2
  have hY : Y ⊆ A ∪ D := (mem_sY.1 hA).2 ▸ dComp_subset (j := j) (D := D) (z0 := z0) A
  have h1 : blocks j Y ⊆ blocks j D ∪ (Comp j A).biUnion (blocks j) := by
    intro c hc
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hc
    rcases mem_union.1 (hY hy) with h | h
    · refine mem_union_right _ (mem_biUnion.2 ?_)
      rw [← biUnion_comp hAp] at h
      obtain ⟨X, hX, hyX⟩ := mem_biUnion.1 h
      exact ⟨X, hX, blk_mem_blocks hyX⟩
    · exact mem_union_left _ (blk_mem_blocks h)
  calc nb j Y ≤ (blocks j D ∪ (Comp j A).biUnion (blocks j)).card := card_le_card h1
    _ ≤ (blocks j D).card + ((Comp j A).biUnion (blocks j)).card := card_union_le _ _
    _ ≤ nb j D + ∑ X ∈ Comp j A, nb j X := Nat.add_le_add_left card_biUnion_le _

theorem blocks_sdiff_subset_of_mem_sY {Y A : Finset (Lam d L N)} (hA : A ∈ sY j D z0 Y) :
    blocks j (Y \ A) ⊆ blocks j D := by
  intro c hc
  obtain ⟨y, hy, rfl⟩ := mem_image.1 hc
  exact blk_mem_blocks (sdiff_subset_of_mem_sY hA hy)

/-- **`|𝒮_Y| ≤ 2^{|𝓑(D)|}`**: `A ∈ 𝒮_Y` contains the blocks of `Y` outside `D`, so it is fixed
by `𝓑(A) ∩ 𝓑(D)`. -/
theorem card_sY_le (Y : Finset (Lam d L N)) :
    (sY j D z0 Y).card ≤ 2 ^ nb j D := by
  classical
  rw [nb, ← card_powerset]
  refine card_le_card_of_injOn (fun A => blocks j A ∩ blocks j D)
    (fun A _ => by simp only [coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_subset];
                   exact inter_subset_right) ?_
  intro A hA A' hA' hAA'
  simp only [mem_coe] at hA hA'
  have key : ∀ {A : Finset (Lam d L N)}, A ∈ sY j D z0 Y →
      blocks j A = (blocks j Y \ blocks j D) ∪ (blocks j A ∩ blocks j D) := by
    intro A hA
    have hAY := (mem_sY.1 hA).1.1
    have hY : Y ⊆ A ∪ D := (mem_sY.1 hA).2 ▸ dComp_subset (j := j) (D := D) (z0 := z0) A
    ext c
    simp only [mem_union, mem_sdiff, mem_inter]
    constructor
    · intro hc
      by_cases hcD : c ∈ blocks j D
      · exact Or.inr ⟨hc, hcD⟩
      · obtain ⟨y, hy, rfl⟩ := mem_image.1 hc
        exact Or.inl ⟨blk_mem_blocks (hAY hy), hcD⟩
    · rintro (⟨hc, hcD⟩ | ⟨hc, -⟩)
      · obtain ⟨y, hy, rfl⟩ := mem_image.1 hc
        rcases mem_union.1 (hY hy) with h | h
        · exact blk_mem_blocks h
        · exact absurd (blk_mem_blocks h) hcD
      · exact hc
  have hb : blocks j A = blocks j A' := by
    rw [key hA, key hA']; exact congrArg _ hAA'
  rw [← biUnion_blocks (mem_sY.1 hA).1.2, ← biUnion_blocks (mem_sY.1 hA').1.2, hb]

/-! ### The polymer bound -/

theorem prod_le_pow_of_le {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) {a : ℝ≥0∞} (ha : 1 ≤ a)
    (hf : ∀ i ∈ s, f i ≤ a) {n : ℕ} (hn : s.card ≤ n) : ∏ i ∈ s, f i ≤ a ^ n :=
  (prod_le_prod' hf).trans (by rw [prod_const]; exact pow_le_pow_right₀ ha hn)

/-- **The polymer bound of the reduced activity at coalescence.** For `ℓ_{ab} ≤ ℓ_aℓ_b`,
`‖I(B)‖ ≤ ι` on the blocks of `D`, `A^{|𝓑(X)|}‖K(X)‖ ≤ 1` on connected `X`:
`A^{(|𝓑(Y)| - 2^d)_+}‖π_{obs}kRed Y‖ ≤ (2ιA)^{|𝓑(D)|}`. -/
theorem kRed_poly_le {w : Wt} (hw : w.Sub) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {A ι : ℝ} (hA : 1 ≤ A) (hι : 1 ≤ ι) (I : OFam c d L N) (K : OAct c d L N)
    (hI : ∀ b ∈ blocks j D, oTj d L w j ℓ (I b : SA c (Lam d L N)) ≤ ENNReal.ofReal ι)
    (hK : ∀ X, IsConn j X →
      ENNReal.ofReal (A ^ nb j X) * oTj d L w j ℓ (K X : SA c (Lam d L N)) ≤ 1)
    (Y : Finset (Lam d L N)) :
    ENNReal.ofReal (A ^ (nb j Y - 2 ^ d)) * oTo w j ℓ (kRed j D z0 I K Y) ≤
      ENNReal.ofReal ((2 * ι * A) ^ nb j D) := by
  classical
  have hA0 : 0 ≤ A := by linarith
  by_cases hDY : D ⊆ Y
  swap
  · rw [kRed_of_not _ _ hDY]
    simp only [oTo, map_zero, ZeroMemClass.coe_zero]
    rw [show oTj d L w j ℓ (0 : SA c (Lam d L N)) = 0 from
      oT_zero (E := Dir d) (p := pPhi d), mul_zero]
    exact zero_le
  rw [kRed_of_sub _ _ hDY]
  have hz := (oTo_πab_le w j ℓ (zLoc j D z0 I K Y)).trans (oTj_zLoc_le hw hℓ I K Y)
  refine (mul_le_mul_right hz _).trans ?_
  rw [mul_sum]
  -- each configuration
  have hterm : ∀ A' ∈ sY j D z0 Y, ENNReal.ofReal (A ^ (nb j Y - 2 ^ d)) *
      ((∏ b ∈ blocks j (Y \ A'), oTj d L w j ℓ (I b : SA c (Lam d L N))) *
        ∏ X ∈ Comp j A', oTj d L w j ℓ (K X : SA c (Lam d L N))) ≤
      ENNReal.ofReal ((ι * A) ^ nb j D) := by
    intro A' hA'
    have hAp := (mem_sY.1 hA').1.2
    have hpow : A ^ (nb j Y - 2 ^ d) ≤ A ^ nb j D * ∏ X ∈ Comp j A', A ^ nb j X := by
      rw [prod_pow_eq_pow_sum, ← pow_add]
      exact pow_le_pow_right₀ hA ((Nat.sub_le _ _).trans (nb_le_of_mem_sY hA'))
    have hprodK : ENNReal.ofReal (∏ X ∈ Comp j A', A ^ nb j X) *
        ∏ X ∈ Comp j A', oTj d L w j ℓ (K X : SA c (Lam d L N)) ≤ 1 := by
      rw [ENNReal.ofReal_prod_of_nonneg (fun X _ => pow_nonneg hA0 _), ← prod_mul_distrib]
      exact prod_le_one' fun X hX => hK X (isConn_of_mem_comp hAp hX)
    have hprodI : ∏ b ∈ blocks j (Y \ A'), oTj d L w j ℓ (I b : SA c (Lam d L N)) ≤
        ENNReal.ofReal ι ^ nb j D :=
      prod_le_pow_of_le _ _ (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hι)
        (fun b hb => hI b (blocks_sdiff_subset_of_mem_sY hA' hb))
        (card_le_card (blocks_sdiff_subset_of_mem_sY hA'))
    calc ENNReal.ofReal (A ^ (nb j Y - 2 ^ d)) *
          ((∏ b ∈ blocks j (Y \ A'), oTj d L w j ℓ (I b : SA c (Lam d L N))) *
            ∏ X ∈ Comp j A', oTj d L w j ℓ (K X : SA c (Lam d L N)))
        ≤ ENNReal.ofReal (A ^ nb j D) * ENNReal.ofReal (∏ X ∈ Comp j A', A ^ nb j X) *
          ((∏ b ∈ blocks j (Y \ A'), oTj d L w j ℓ (I b : SA c (Lam d L N))) *
            ∏ X ∈ Comp j A', oTj d L w j ℓ (K X : SA c (Lam d L N))) := by
          rw [← ENNReal.ofReal_mul (pow_nonneg hA0 _)]
          exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hpow) _
      _ = ENNReal.ofReal (A ^ nb j D) *
          (∏ b ∈ blocks j (Y \ A'), oTj d L w j ℓ (I b : SA c (Lam d L N))) *
          (ENNReal.ofReal (∏ X ∈ Comp j A', A ^ nb j X) *
            ∏ X ∈ Comp j A', oTj d L w j ℓ (K X : SA c (Lam d L N))) := by ring
      _ ≤ ENNReal.ofReal (A ^ nb j D) * ENNReal.ofReal ι ^ nb j D * 1 := by
          gcongr
      _ = ENNReal.ofReal ((ι * A) ^ nb j D) := by
          rw [mul_one, ← ENNReal.ofReal_pow (by linarith), ← ENNReal.ofReal_mul (pow_nonneg hA0 _),
            ← mul_pow, mul_comm A ι]
  refine (sum_le_sum hterm).trans ?_
  rw [sum_const, nsmul_eq_mul]
  have hc : ((sY j D z0 Y).card : ℝ≥0∞) ≤ ENNReal.ofReal (2 ^ nb j D) := by
    rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
    exact_mod_cast card_sY_le Y
  calc ((sY j D z0 Y).card : ℝ≥0∞) * ENNReal.ofReal ((ι * A) ^ nb j D)
      ≤ ENNReal.ofReal (2 ^ nb j D) * ENNReal.ofReal ((ι * A) ^ nb j D) :=
        mul_le_mul_left hc _
    _ = ENNReal.ofReal ((2 * ι * A) ^ nb j D) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow, mul_assoc]

/-- The weights `(M_a^{-1}, M_b^{-1}, (M_aM_b)^{-1})`. -/
def wM (Ma Mb : ℝ) : Wt := ⟨ENNReal.ofReal Ma⁻¹, ENNReal.ofReal Mb⁻¹,
  ENNReal.ofReal Ma⁻¹ * ENNReal.ofReal Mb⁻¹⟩

theorem wM_sub (Ma Mb : ℝ) : (wM Ma Mb).Sub := le_rfl

/-- **`‖π_{ab}zLoc Y‖ ≲ M_aM_b`** in the polymer norm: the hypotheses of `kRed_poly_le` in the
weights `wM M_a M_b` (one-point parts of the factors measured relative to `M_a`, `M_b`, the
`ab` parts relative to `M_aM_b`). -/
theorem kRed_ab_poly_le {Ma Mb : ℝ} (hMa : 0 < Ma) (hMb : 0 < Mb) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {A ι : ℝ} (hA : 1 ≤ A) (hι : 1 ≤ ι) (I : OFam c d L N)
    (K : OAct c d L N)
    (hI : ∀ b ∈ blocks j D, oTj d L (wM Ma Mb) j ℓ (I b : SA c (Lam d L N)) ≤ ENNReal.ofReal ι)
    (hK : ∀ X, IsConn j X →
      ENNReal.ofReal (A ^ nb j X) * oTj d L (wM Ma Mb) j ℓ (K X : SA c (Lam d L N)) ≤ 1)
    (Y : Finset (Lam d L N)) :
    ENNReal.ofReal (A ^ (nb j Y - 2 ^ d)) *
        Tj d (L : ℝ) j ℓ (kRed j D z0 I K Y : SA c (Lam d L N)).ab ≤
      ENNReal.ofReal (Ma * Mb * (2 * ι * A) ^ nb j D) := by
  have h := kRed_poly_le (z0 := z0) (wM_sub Ma Mb) hℓ hA hι I K hI hK Y
  have hab : kRed j D z0 I K Y ∈ (abSub : Subalgebra ℂ (OE c (Lam d L N))) := kRed_mem_ab I K Y
  rw [oTo_of_ab _ _ _ hab] at h
  have hw : (wM Ma Mb).ab = ENNReal.ofReal (Ma * Mb)⁻¹ := by
    rw [wM, mul_inv, ENNReal.ofReal_mul (inv_nonneg.2 hMa.le)]
  rw [hw] at h
  have hMM : 0 < Ma * Mb := mul_pos hMa hMb
  have e1 : ENNReal.ofReal (Ma * Mb) * ENNReal.ofReal (Ma * Mb)⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul hMM.le, mul_inv_cancel₀ hMM.ne', ENNReal.ofReal_one]
  calc ENNReal.ofReal (A ^ (nb j Y - 2 ^ d)) *
        Tj d (L : ℝ) j ℓ (kRed j D z0 I K Y : SA c (Lam d L N)).ab
      = ENNReal.ofReal (Ma * Mb) * ENNReal.ofReal (Ma * Mb)⁻¹ *
          (ENNReal.ofReal (A ^ (nb j Y - 2 ^ d)) *
            Tj d (L : ℝ) j ℓ (kRed j D z0 I K Y : SA c (Lam d L N)).ab) := by
        rw [e1, one_mul]
    _ = ENNReal.ofReal (Ma * Mb) * (ENNReal.ofReal (A ^ (nb j Y - 2 ^ d)) *
          (ENNReal.ofReal (Ma * Mb)⁻¹ *
            Tj d (L : ℝ) j ℓ (kRed j D z0 I K Y : SA c (Lam d L N)).ab)) := by ring
    _ ≤ ENNReal.ofReal (Ma * Mb) * ENNReal.ofReal ((2 * ι * A) ^ nb j D) :=
        mul_le_mul_right h _
    _ = ENNReal.ofReal (Ma * Mb * (2 * ι * A) ^ nb j D) :=
        (ENNReal.ofReal_mul hMM.le).symm

/-! ### The quartic seed -/

end

end PtCorr2
