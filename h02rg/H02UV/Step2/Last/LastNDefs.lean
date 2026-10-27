import Step2.Map.Main
import Step2.Map.Reapp

/-!
# The last step `j = N - 1`: the map (`h02uv-outline.tex`, Section `sec:corr`, "The last scale")

At the last step `j + 1 = N` the second-order map of `Step2.Map.Defs` cannot be used unchanged: its
`V_{j+1}` contains `Loc_{B_+,B} S(B_+)` with `B_+ = Λ`, and `Λ` is not a small set at any scale
`< N`, so `lem:loc2` (`exists_Loc2sXY_bound`, `j < N`) does not apply. As in the old library
(`Step.LocC = 0` for `j + 1 = N`) the last step has **no localisation and no `Q`, `J`**:

* `u_N(B) = ε(V'_B)`, `V_N(B) = V'_B - u_N(B)` with `V'_B = 𝔼_C θ V(B)` (`upN`, `VpN`);
* `𝒲_N(B) = S(B) = ½ F(V'_B, V'(Λ)) + 𝔼_C θ 𝒲(B)` (`Step2.Sb`, unchanged);
* `I_N(B) = e^{-u_N(B)} e^{-V_N(B)} (1 + 𝒲_N(B))` (`IpN`);
* `K_N(U) = e^{u_N(U)} gKnext(U)` (`KN`), the polymer formula of `Step2.Map.Gen` with these block
  factors and `J = J2 j K` (which is `0` at `j + 1 = N`).

Results:
* `KN_ZVK` (any `j`): `𝔼_C θ Z_j = ∑_U I_N^{Λ∖U} e^{-u_N(U)} K_N(U)`;
* `KN_ZVK_last` (`j + 1 = N`): since `𝒫_N(Λ) = {∅, Λ}`,
  `𝔼_C θ Z_{N-1} = I_N^Λ + e^{-u_N(Λ)} K_N(Λ)`;
* `K2_last`: the explicit second-order part `K^{(2)}(Λ)` vanishes at `j + 1 = N`
  (from `K2_sum_zero`).
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

namespace LastN

/-! ### Scale `N` is a single block -/

theorem blk_top (x : Lam d L N) : blk N x = 0 := by
  funext i
  have := blk_lt (le_refl N) x i
  simp at this
  simpa using this

theorem isPolymer_top {X : Finset (Lam d L N)} (hX : IsPolymer N X) : X = ∅ ∨ X = univ := by
  rcases X.eq_empty_or_nonempty with h | ⟨x, hx⟩
  · exact Or.inl h
  · exact Or.inr (eq_univ_of_forall fun y => hX x y (by rw [blk_top, blk_top]) hx)

theorem Pj_top : Pj N (univ : Finset (Lam d L N)) = {∅, univ} := by
  ext X
  simp only [mem_Pj, subset_univ, true_and, mem_insert, mem_singleton]
  constructor
  · exact isPolymer_top
  · rintro (rfl | rfl)
    · exact isPolymer_empty N
    · exact isPolymer_univ N

theorem blocks_top : blocks N (univ : Finset (Lam d L N)) = {0} := by
  ext b
  simp only [mem_blocks, mem_univ, true_and, mem_singleton]
  constructor
  · rintro ⟨x, rfl⟩; exact blk_top x
  · rintro rfl; exact ⟨0, blk_top 0⟩

theorem nb_top : nb N (univ : Finset (Lam d L N)) = 1 := by
  rw [nb, blocks_top, card_singleton]

theorem isConn_top : IsConn N (univ : Finset (Lam d L N)) := by
  refine ⟨isPolymer_univ N, univ_nonempty, fun b hb b' hb' => ?_⟩
  obtain ⟨x, -, rfl⟩ := mem_blocks.1 hb
  obtain ⟨y, -, rfl⟩ := mem_blocks.1 hb'
  rw [blk_top, blk_top]

/-- At `j + 1 = N` the torus contains at most `L^d` blocks of scale `j`. -/
theorem card_blockIdx_last {j : ℕ} (hj : j + 1 = N) :
    (blockIdx (d := d) (L := L) (N := N) j).card ≤ L ^ d := by
  subst hj
  have h := nb_le_of_succ (isPolymer_univ (L := L) (N := j + 1) (d := d) (j + 1))
  rw [nb_top, mul_one] at h
  exact h

theorem wnorm_top (ℓ A : ℝ) (F : EvR (Lam d L N)) :
    wnorm N ℓ A (univ : Finset (Lam d L N)) F = Tj d (L : ℝ) N ℓ (F : Alg d L N) := by
  rw [wnorm, nb_top]
  have : 1 - 2 ^ d = 0 := Nat.sub_eq_zero_of_le (Nat.one_le_two_pow)
  rw [this, pow_zero, ENNReal.ofReal_one, one_mul]

/-! ### The map -/

section Map

variable (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V W : Fam d L N) (K : Act d L N)

/-- `u_N(B) = ε(V'_B)`. -/
def upN (b : Fin d → ℕ) : ℂ := ε (Vpr C V b : Alg d L N)

/-- `V_N(B) = V'_B - u_N(B)`. -/
def VpN (b : Fin d → ℕ) : EvR (Lam d L N) := Vpr C V b - algebraMap ℂ _ (upN C V b)

/-- `I_N(B) = e^{-u_N(B)} e^{-V_N(B)} (1 + S(B))`. -/
def IpN (b : Fin d → ℕ) : EvR (Lam d L N) :=
  Complex.exp (-upN C V b) • (gexp (-VpN C V b) * (1 + Sb j C V W b))

/-- `u_N(X) = ∑_{B ∈ 𝓑_j(X)} u_N(B)`. -/
def uXN (X : Finset (Lam d L N)) : ℂ := ∑ b ∈ blocks j X, upN C V b

/-- **`K_N(U)`**: the polymer formula with the block factors `I_N` and `Q = J = 0`. -/
def KN (U : Finset (Lam d L N)) : EvR (Lam d L N) :=
  Complex.exp (uXN j C V U) • gKnext j C (Ib V W) (IpN j C V W) K (J2 j K) U

/-- `V_N(Λ) = ∑_B V_N(B)`. -/
def VN : EvR (Lam d L N) := ∑ b ∈ blockIdx (L := L) (N := N) j, VpN C V b

theorem ε_VpN (b : Fin d → ℕ) : ε (VpN C V b : Alg d L N) = 0 := by
  simp [VpN, upN]

theorem KN_empty : KN j C V W K ∅ = 1 := by
  rw [KN, gKnext, Gset_empty, sum_singleton]
  simp only [uXN, blocks, image_empty, sum_empty, Complex.exp_zero, one_smul, Xcal, biUnion_empty,
    union_empty, empty_sdiff, bpow, prod_empty, one_mul, gKchk, comp_empty, mul_one]
  exact Subtype.ext (by simp [ECCE, ECC_one])

/-- **`𝔼_C θ Z_j = ∑_U I_N^{Λ∖U} e^{-u_N(U)} K_N(U)`.** -/
theorem KN_ZVK :
    ECCE C (thetaE (gZ j (Ib V W) K)) = ∑ U ∈ Pj (j + 1) univ,
      bpow j (IpN j C V W) (univ \ U) * (Complex.exp (-uXN j C V U) • KN j C V W K U) := by
  rw [gZVK j C (Ib V W) (IpN j C V W) K (J := J2 j K) (fun b c h => J2_of_not_small j K b c h)]
  refine sum_congr rfl fun U _ => ?_
  rw [KN, smul_smul, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_smul]

/-- **The last step**: `𝔼_C θ Z_{N-1} = I_N^Λ + e^{-u_N(Λ)} K_N(Λ)`. -/
theorem KN_ZVK_last (hj : j + 1 = N) :
    ECCE C (thetaE (gZ j (Ib V W) K)) =
      bpow j (IpN j C V W) univ + Complex.exp (-uXN j C V univ) • KN j C V W K univ := by
  rw [KN_ZVK]
  subst hj
  have hne : (∅ : Finset (Lam d L (j + 1))) ≠ univ := fun h =>
    (univ_nonempty (α := Lam d L (j + 1))).ne_empty h.symm
  rw [Pj_top, sum_pair hne, KN_empty, sdiff_empty, sdiff_self]
  simp only [uXN, blocks, image_empty, sum_empty, neg_zero, Complex.exp_zero, one_smul, mul_one,
    bpow, Finset.bot_eq_empty, prod_empty, one_mul]

/-- `K^{(2)}(Λ) = 0` at the last scale. -/
theorem K2_last (hj : j + 1 = N) : K2 j C V univ = 0 := by
  classical
  have h := K2_sum_zero (L := L) (N := N) j C V
  have h0 : K2 j C V ∅ = 0 := by
    rw [K2]
    refine sum_eq_zero fun X hX => ?_
    have hX0 : X = ∅ := subset_empty.1 ((subset_clo j X).trans (mem_filter.1 hX).2.le)
    subst hX0
    have : nb j (∅ : Finset (Lam d L N)) = 0 := by simp [nb, blocks]
    rw [k2, if_neg (by omega), if_neg (by omega)]
  subst hj
  have hne : (∅ : Finset (Lam d L (j + 1))) ≠ univ := fun h =>
    (univ_nonempty (α := Lam d L (j + 1))).ne_empty h.symm
  rw [Pj_top, sum_pair hne, h0, zero_add] at h
  exact h

end Map

end LastN

end

end Step2
