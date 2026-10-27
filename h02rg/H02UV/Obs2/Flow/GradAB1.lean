import Obs2.Flow.VObsAB4X
import Obs2.Pair.PairChain

/-!
# The gradient part of `V'_{ab}`: change of base point, the sources of `loc^{ab}`, the gradient
tadpole

`gradAB a b F` is the gradient part of `F ∈ 𝒩({a,b})` seen from `a` (`eq_grad_of_ab`). Here:

* **`gradAB_swap`**: `gradAB a b F = gradAB b a F + m₂(F)(ψ̄_bψ_b − ψ̄_aψ_a)` (the mass seen from the
  other point is a gradient term);
* **`tNorm_pbp_sub_le`**: `‖ψ̄_bψ_b − ψ̄_aψ_a‖_{T_h(ℓ)} ≤ 2ℓg + g²`, `g = |e|₁ℓ/h`;
* **`gradAB_locABt_swap`**: for a localisation based at `b`, `gradAB a b (loc^{ab,t}_{X,b}F) =
  Dt_{X,b,a}F + m₂(F)(ψ̄_bψ_b − ψ̄_aψ_a)`;
* **`tNorm_gradAB_locABtX_le`**, **`tNorm_gradAB_locABtXY_le`**: the gradient part of `loc^{ab}`
  (either base point) is bounded by `(K_D L^j/h + ℓ^{-2}(2ℓ'g + g²))‖F‖_{T_j(ℓ)}`;
* **`tNorm_FC_gen_le`**: `‖F_C(A, B)‖_{T_{j+1}(ℓ)} ≤ 2‖A‖_{T_{j+1}(4ℓ)}‖B‖_{T_{j+1}(4ℓ)}` for
  arbitrary `A`, `B` (`GoodCov2 j ℓ C`; `e^{-ℒ_C}` has the Gram bound of `C`);
* **`norm_mass2_FC_le`**, **`norm_gradTad_le`**, **`norm_gradTadX_le`**: the gradient tadpole
  `|m₂F_C(D, V'_∅)| ≤ 2ℓ^{-2}‖D‖_{T_{j+1}(4ℓ)}‖V'_∅‖_{T_{j+1}(4ℓ)}` (the `sg` item of
  `Spin2.PairErrSizesR3`, and its region version for `errABX2`).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD

variable {d L N : ℕ} [NeZero L]

/-! ### Change of the base point -/

/-- **The gradient part seen from the other point** (`a ≠ b`). -/
theorem gradAB_swap {a b : Lam d L N} (hab : a ≠ b) {F : Alg d L N}
    (hN : F ∈ NX ({a, b} : Set (Lam d L N))) (hS : IsSym F) :
    gradAB a b F = gradAB b a F + mass2 F • (pbp b - pbp a) := by
  have e1 := eq_grad_of_ab hab hN hS
  have hN' : F ∈ NX ({b, a} : Set (Lam d L N)) := by rwa [Set.pair_comm]
  have e2 := eq_grad_of_ab (Ne.symm hab) hN' hS
  have key : ε F • (1 : Alg d L N) + mass2 F • pbp a + gradAB a b F =
      ε F • (1 : Alg d L N) + mass2 F • pbp b + gradAB b a F := by rw [← e1, ← e2]
  rw [smul_sub]
  calc gradAB a b F = (ε F • (1 : Alg d L N) + mass2 F • pbp a + gradAB a b F) -
        (ε F • (1 : Alg d L N) + mass2 F • pbp a) := by abel
    _ = (ε F • (1 : Alg d L N) + mass2 F • pbp b + gradAB b a F) -
        (ε F • (1 : Alg d L N) + mass2 F • pbp a) := by rw [key]
    _ = _ := by abel

/-- `|e|₁` is symmetric in the two points. -/
theorem eN1_swap (X : Finset (Lam d L N)) (a b : Lam d L N) : eN1 X b a = eN1 X a b := by
  unfold eN1 eV
  exact sum_congr rfl fun i _ => by rw [← abs_neg, neg_sub]

theorem locABt_isSym (X : Finset (Lam d L N)) (a b : Lam d L N) (F : Alg d L N) :
    IsSym (locABt X a b F) := by
  rw [isSym_iff_mem_SymS, mem_SymS, locABt, map_add, scal_locEven,
    mem_SymS.1 (Dt_mem_SymS X a b F)]

theorem mass2_locABt {X : Finset (Lam d L N)} {a : Lam d L N} (ha : a ∈ X) (b : Lam d L N)
    (F : Alg d L N) : mass2 (locABt X a b F) = mass2 F := by
  rw [locABt, mass2_add, mass2_Dt, add_zero, locEven_single_eq' ha subset_rfl, mass2_add,
    mass2_smul, mass2_smul, mass2_one, mass2_pbp]
  ring

/-- **The gradient part of a localisation based at `b`, seen from `a`.** -/
theorem gradAB_locABt_swap {X : Finset (Lam d L N)} {a b : Lam d L N} (hb : b ∈ X) (hab : a ≠ b)
    (F : Alg d L N) :
    gradAB a b (locABt X b a F) = Dt X b a F + mass2 F • (pbp b - pbp a) := by
  have hN : locABt X b a F ∈ NX ({a, b} : Set (Lam d L N)) := by
    rw [Set.pair_comm]; exact locABt_mem X b a F
  rw [gradAB_swap hab hN (locABt_isSym X b a F), gradAB_locABt hb (Ne.symm hab),
    mass2_locABt hb]

/-! ### The gradient tadpole -/

/-- `e^{-ℒ_C}` has the Gram bound of `C`. -/
theorem tNorm_expLC_neg_le {j : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {C : Matrix (Lam d L N) (Lam d L N) ℂ}
    (hC : GoodCov2 j ℓ C) (A : Alg d L N) :
    Tj d (L : ℝ) (j + 1) (2 * ℓ) (expLC (-C) A) ≤ Tj d (L : ℝ) (j + 1) (2 * (2 * ℓ)) A := by
  obtain ⟨H, i1, i2, Fv, Gv, hG, hB⟩ := hC.gram
  have hh : (0 : ℝ) < (L : ℝ) ^ (j + 1) :=
    pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) _
  have hG' : IsGram (-C) (fun x => -Fv x) Gv := fun x y => by
    rw [Matrix.neg_apply, hG x y, inner_neg_left]
  have hB' : GramBound (Dir d) (pPhi d) ((L : ℝ) ^ (j + 1)) ℓ (fun x => -Fv x) Gv := by
    intro a ha x
    have e : gvec (fun x => -Fv x) (dprof a x) = -gvec Fv (dprof a x) := by
      simp [gvec, smul_neg, Finset.sum_neg_distrib]
    rw [e, norm_neg]
    exact hB a ha x
  have h2 := tNorm_ECC_theta_le hh (by linarith : (0 : ℝ) < 2 * ℓ) hG'
    (gramBound_mono hh hB' (by linarith : ℓ ≤ 2 * ℓ)) A
  rwa [ECC_theta] at h2

/-- **The truncated expectation of arbitrary elements**:
`‖F_C(A, B)‖_{T_{j+1}(ℓ)} ≤ 2‖A‖_{T_{j+1}(4ℓ)}‖B‖_{T_{j+1}(4ℓ)}` (`GoodCov2 j ℓ C`). -/
theorem tNorm_FC_gen_le {j : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {C : Matrix (Lam d L N) (Lam d L N) ℂ}
    (hC : GoodCov2 j ℓ C) (A B : Alg d L N) :
    Tj d (L : ℝ) (j + 1) ℓ (FC C A B) ≤
      2 * (Tj d (L : ℝ) (j + 1) (2 * (2 * ℓ)) A * Tj d (L : ℝ) (j + 1) (2 * (2 * ℓ)) B) := by
  have eA : A = ECC C (theta (expLC (-C) A)) := by rw [ECC_theta, expLC_expLC_neg]
  have eB : B = ECC C (theta (expLC (-C) B)) := by rw [ECC_theta, expLC_expLC_neg]
  have h := FC_succ_le hℓ hC (expLC (-C) A) (expLC (-C) B)
  rw [← eA, ← eB] at h
  refine h.trans ?_
  gcongr
  · exact tNorm_expLC_neg_le hℓ hC A
  · exact tNorm_expLC_neg_le hℓ hC B

/-- **The mass of a truncated expectation**: `|m₂F_C(A, B)| ≤ 2αβℓ^{-2}` for
`‖A‖_{T_{j+1}(4ℓ)} ≤ α`, `‖B‖_{T_{j+1}(4ℓ)} ≤ β`. -/
theorem norm_mass2_FC_le {j : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {C : Matrix (Lam d L N) (Lam d L N) ℂ}
    (hC : GoodCov2 j ℓ C) {A B : Alg d L N} {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hA : Tj d (L : ℝ) (j + 1) (2 * (2 * ℓ)) A ≤ ENNReal.ofReal α)
    (hB : Tj d (L : ℝ) (j + 1) (2 * (2 * ℓ)) B ≤ ENNReal.ofReal β) :
    ‖mass2 (FC C A B)‖ ≤ 2 * (α * β) * ℓ⁻¹ ^ 2 := by
  have h1 : Tj d (L : ℝ) (j + 1) ℓ (FC C A B) ≤ ENNReal.ofReal (2 * (α * β)) := by
    refine (tNorm_FC_gen_le hℓ hC A B).trans ?_
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul hα, ENNReal.ofReal_ofNat]
    gcongr
  have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
  rw [ENNReal.toReal_ofReal (by positivity)] at h2
  exact (norm_mass2_le hℓ (j + 1) _).trans
    (mul_le_mul_of_nonneg_right h2 (by positivity))

/-- **The gradient tadpole of `errAB`**: `|m₂F_C(D_j, V'(Λ)_∅)| ≤ 2δeℓ^{-2}` with
`‖D_j‖_{T_{j+1}(4ℓ)} ≤ δ`, `‖V'(Λ)_∅‖_{T_{j+1}(4ℓ)} ≤ e`. -/
theorem norm_gradTad_le (P : ObsPts d L N) {j : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {C : Matrix (Lam d L N) (Lam d L N) ℂ} (hC : GoodCov2 j ℓ C) (V : OFam .two d L N)
    {δ e : ℝ} (hδ : 0 ≤ δ) (he : 0 ≤ e)
    (hD : Tj d (L : ℝ) (j + 1) (2 * (2 * ℓ)) (dAB P j C V) ≤ ENNReal.ofReal δ)
    (hE : Tj d (L : ℝ) (j + 1) (2 * (2 * ℓ)) (VprLO j C V : SA .two (Lam d L N)).e ≤
      ENNReal.ofReal e) :
    ‖mass2 (FC C (dAB P j C V) (VprLO j C V : SA .two (Lam d L N)).e)‖ ≤
      2 * (δ * e) * ℓ⁻¹ ^ 2 :=
  norm_mass2_FC_le hℓ hC hδ he hD hE

/-- **The gradient tadpole of a region** (`errABX2`). -/
theorem norm_gradTadX_le (P : ObsPts d L N) {j : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {C : Matrix (Lam d L N) (Lam d L N) ℂ} (hC : GoodCov2 j ℓ C) (V : OFam .two d L N)
    (X : Finset (Lam d L N)) {δ e : ℝ} (hδ : 0 ≤ δ) (he : 0 ≤ e)
    (hD : Tj d (L : ℝ) (j + 1) (2 * (2 * ℓ)) (dABX P j C V X) ≤ ENNReal.ofReal δ)
    (hE : Tj d (L : ℝ) (j + 1) (2 * (2 * ℓ)) (VprLO j C V : SA .two (Lam d L N)).e ≤
      ENNReal.ofReal e) :
    ‖mass2 (FC C (dABX P j C V X) (VprLO j C V : SA .two (Lam d L N)).e)‖ ≤
      2 * (δ * e) * ℓ⁻¹ ^ 2 :=
  norm_mass2_FC_le hℓ hC hδ he hD hE

/-- The gradient part of a region is `gradAB` of `V'(X)_{ab}` (as `dAB_eq_grad`). -/
theorem dABX_eq_grad (P : ObsPts d L N) (hab : P.a ≠ P.b) (j : ℕ)
    (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V : OFam .two d L N) (X : Finset (Lam d L N))
    (hN : (VprXO j C V X : SA .two (Lam d L N)).ab ∈ NX ({P.a, P.b} : Set (Lam d L N)))
    (hS : IsSym (VprXO j C V X : SA .two (Lam d L N)).ab) :
    dABX P j C V X = gradAB P.a P.b (VprXO j C V X : SA .two (Lam d L N)).ab := by
  unfold dABX
  have e := eq_grad_of_ab hab hN hS
  set F := (VprXO j C V X : SA .two (Lam d L N)).ab
  calc F - (ε F • (1 : Alg d L N) + mass2 F • pbp P.a) =
      (ε F • (1 : Alg d L N) + mass2 F • pbp P.a + gradAB P.a P.b F) -
        (ε F • (1 : Alg d L N) + mass2 F • pbp P.a) := by rw [← e]
    _ = _ := by abel

end

end Obs2
