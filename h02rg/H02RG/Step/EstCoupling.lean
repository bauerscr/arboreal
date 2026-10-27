import Loc.Estimates
import Step.EstSetup
import Step.Coupling
import Step.ExpNorm

/-!
# Estimates for the coupling constants (Section `sec:K-coupling`)

* `E:Q`: `‖Q(B)‖_{T_j(ℓ_j)} ≤ O(1) ‖K‖_j`, and the same for `J(B, X)`;
* `E:vj`: `‖(u+V)_{j+1}(B)‖_{T_{j+1}(ℓ_{j+1})} ≤ ‖V‖_j + O(‖K‖_j)` for `B ∈ 𝓑_j`;
* `e:step-V`: `‖(u+V)_{j+1}(B') - 𝔼 θ V_j(B')‖_{T_{j+1}(ℓ_{j+1})} ≤ O(L^d) ‖K‖_j` for
  `B' ∈ 𝓑_{j+1}`.

We also prove the basic bounds used in Sections `sec:K-smallset`–`sec:K-nonlinear`:

* `uVnext_bounds`: `E:vj` for `|u_{j+1}| |B|`, `V_{j+1}(B)` and `(u+V)_{j+1}(X)`, `X ∈ 𝒫_j`;
* `dI_bound`: `‖δI(B)‖_{T_{j+1}(ℓ_{j+1})} = O(‖V‖_j + ‖K‖_j)` (`e:deltaIbd`);
* `EdI_Q_bound`: `‖𝔼 [δI(B) + θ Q(B)]‖ = O(‖V‖_j^2 + ‖K‖_j^2)` (Lemma `lem:smallset-V`);
* `pert12`: Lemma `lem:pert12`;
* `thetaJ_bounds`: `‖θ J(B, X)‖, ‖𝔼 θ J(B, X)‖ = O(‖K‖_j)`.
-/

namespace Step

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

/-! ### Preliminaries -/

theorem Tj_zero {X : Type*} [DecidableEq X] [Fintype X] [AddAction (Dir d → ℕ) X] (L' : ℝ)
    (j : ℕ) (ℓ : ℝ) : Tj d L' j ℓ (0 : Grassmann.N X) = 0 := by
  have := tNorm_smul (E := Dir d) (p := pPhi d) (h := L' ^ j) (ℓ := ℓ) (0 : ℂ) (0 : Grassmann.N X)
  simpa using this

theorem Tj_neg' {X : Type*} [DecidableEq X] [Fintype X] [AddAction (Dir d → ℕ) X] {L' : ℝ}
    {j : ℕ} {ℓ : ℝ} (F : Grassmann.N X) : Tj d L' j ℓ (-F) = Tj d L' j ℓ F := tNorm_neg F

theorem Tj_smul' {X : Type*} [DecidableEq X] [Fintype X] [AddAction (Dir d → ℕ) X] {L' : ℝ}
    {j : ℕ} {ℓ : ℝ} (c : ℂ) (F : Grassmann.N X) :
    Tj d L' j ℓ (c • F) = ENNReal.ofReal ‖c‖ * Tj d L' j ℓ F := tNorm_smul c F

theorem one_le_ofReal_pow {A : ℝ} (hA : 1 ≤ A) (n : ℕ) : 1 ≤ ENNReal.ofReal (A ^ n) := by
  rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (one_le_pow₀ hA)

/-- `‖K(X)‖_{T_j(ℓ)} ≤ ‖K‖_j` for connected `X` (as `A ≥ 1`). -/
theorem Tj_le_Knorm {j : ℕ} {ℓ A : ℝ} (hA : 1 ≤ A) {K : Act d L N} {X : Finset (Lam d L N)}
    (hX : IsConn j X) : Tj d (L : ℝ) j ℓ (K X : Alg d L N) ≤ Knorm j ℓ A K :=
  le_trans (le_mul_of_one_le_left (by simp) (one_le_ofReal_pow hA _)) (wnorm_le_Knorm hX)

theorem Tj_le_Vnorm {j : ℕ} {ℓ : ℝ} (V : Vcoup) {b : Fin d → ℕ}
    (hb : b ∈ blockIdx (d := d) (L := L) (N := N) j) :
    Tj d (L : ℝ) j ℓ (V.eval (blockSet (L := L) (N := N) j b)) ≤ Vnorm (d := d) (L := L) (N := N) j ℓ V :=
  le_iSup₂_of_le (f := fun b _ => Tj d (L : ℝ) j ℓ (V.eval (blockSet (L := L) (N := N) j b)))
    b hb le_rfl

theorem isSmall_blockSet_of_mem {j : ℕ} {b : Fin d → ℕ}
    (hb : b ∈ blockIdx (d := d) (L := L) (N := N) j) : IsSmall j (blockSet (L := L) (N := N) j b) := by
  obtain ⟨x, _, rfl⟩ := mem_image.1 hb
  exact isSmall_blockSet j x

theorem mem_blockIdx_of_mem_blocks {j : ℕ} {X : Finset (Lam d L N)} {b : Fin d → ℕ}
    (hb : b ∈ blocks j X) : b ∈ blockIdx (d := d) (L := L) (N := N) j :=
  image_subset_image (subset_univ X) hb

theorem pairwiseDisjoint_blockSet (j : ℕ) (s : Finset (Fin d → ℕ)) :
    (s : Set (Fin d → ℕ)).PairwiseDisjoint (blockSet (L := L) (N := N) j) := by
  intro b _ b' _ hbb'
  rw [Function.onFun, disjoint_left]
  intro x hx hx'
  exact hbb' ((mem_blockSet.1 hx).symm.trans (mem_blockSet.1 hx'))

theorem eval_polymer (V : Vcoup) {j : ℕ} {X : Finset (Lam d L N)} (hX : IsPolymer j X) :
    V.eval X = ∑ b ∈ blocks j X, V.eval (blockSet (L := L) (N := N) j b) := by
  conv_lhs => rw [← biUnion_blocks hX]
  rw [Vcoup.eval, sum_biUnion (pairwiseDisjoint_blockSet j _)]
  rfl

theorem card_polymer {j : ℕ} {X : Finset (Lam d L N)} (hX : IsPolymer j X) :
    X.card = ∑ b ∈ blocks j X, (blockSet (L := L) (N := N) j b).card := by
  conv_lhs => rw [← biUnion_blocks hX]
  exact card_biUnion (pairwiseDisjoint_blockSet j _)

theorem ε_eval (V : Vcoup) (X : Finset (Lam d L N)) : ε (V.eval X) = 0 := by
  simp [Vcoup.eval, gradSq, lapPsi, lapPsibar, grad, gradbar, psi, psibar, ψ]

theorem EC_incl (C : Matrix (Lam d L N) (Lam d L N) ℝ) (F : Alg d L N) : EC C (incl F) = F := by
  simpa [EC_one] using EC_incl_mul C F 1

theorem nb_blockSet_succ_le (j : ℕ) (b : Fin d → ℕ) :
    nb j (blockSet (L := L) (N := N) (j + 1) b) ≤ L ^ d := by
  have h1 : nb (j + 1) (blockSet (L := L) (N := N) (j + 1) b) ≤ 1 := by
    refine (card_le_card (s := blocks (j + 1) (blockSet (L := L) (N := N) (j + 1) b))
      (t := {b}) ?_).trans (by simp)
    intro c hc
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hc
    exact mem_singleton.2 (mem_blockSet.1 hy)
  exact (nb_le_of_succ (isPolymer_blockSet (j + 1) b)).trans
    (by simpa using Nat.mul_le_mul_left (L ^ d) h1)

/-! ### `E:Q` and the bound on `J` -/

/-- `E:Q` and the bound on `J(B, X)`. -/
theorem QJ_bounds (hd : 3 ≤ d) : ∃ (C₀ : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧ 2 ^ (d + 3) + 8 * d + 1 ≤ L₀ ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∀ (N j : ℕ), j < N → ∀ (ℓ₀ : ℝ), 0 < ℓ₀ →
    ∀ (K : Act d L N) (A : ℝ), 1 ≤ A → InK j K →
      (∀ b ∈ blockIdx (d := d) (L := L) (N := N) j,
        Tj d (L : ℝ) j (ellj d L ℓ₀ j) (Qb j K b : Alg d L N) ≤
          ENNReal.ofReal C₀ * Knorm j (ellj d L ℓ₀ j) A K) ∧
      (∀ b ∈ blockIdx (d := d) (L := L) (N := N) j, ∀ X : Finset (Lam d L N),
        Tj d (L : ℝ) j (ellj d L ℓ₀ j) (Jb j K b X : Alg d L N) ≤
          ENNReal.ofReal C₀ * Knorm j (ellj d L ℓ₀ j) A K) := by
  classical
  obtain ⟨Cb, L₁, hCb⟩ := Loc_bound hd
  obtain ⟨c, hc⟩ := card_small_containing d
  set C' := max Cb 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  refine ⟨(c + 1) * C', max L₁ (2 ^ (d + 3) + 8 * d + 1), by positivity, le_max_right _ _, ?_⟩
  intro L _ hL N j hj ℓ₀ hℓ₀ K A hA hK
  set k := Knorm j (ellj d L ℓ₀ j) A K
  have hterm : ∀ b ∈ blockIdx (d := d) (L := L) (N := N) j, ∀ X ∈ smallSets (L := L) (N := N) j,
      blockSet j b ⊆ X →
      Tj d (L : ℝ) j (ellj d L ℓ₀ j) (LocE X (blockSet j b) (K X) : Alg d L N) ≤
        ENNReal.ofReal C' * k := by
    intro b hb X hX hbX
    have hXs : IsSmall j X := by simpa [smallSets] using hX
    rw [coe_LocE]
    refine (hCb L (le_of_max_le_left hL) N j hj ℓ₀ hℓ₀ X _ hXs (isSmall_blockSet_of_mem hb) hbX _
      (hK.loc X ⟨hXs.1, hXs.2.1⟩)).trans ?_
    gcongr
    · exact le_max_left _ _
    · exact Tj_le_Knorm hA ⟨hXs.1, hXs.2.1⟩
  have hsum : ∀ b ∈ blockIdx (d := d) (L := L) (N := N) j,
      ∀ S ⊆ (smallSets (L := L) (N := N) j).filter (fun X => blockSet j b ⊆ X),
      Tj d (L : ℝ) j (ellj d L ℓ₀ j) (∑ X ∈ S, (LocE X (blockSet j b) (K X) : Alg d L N)) ≤
        ENNReal.ofReal ((c + 1) * C') * k := by
    intro b hb S hS
    refine (tNorm_sum_le _ _).trans ?_
    refine (sum_le_sum fun X hX =>
      hterm b hb X (mem_filter.1 (hS hX)).1 (mem_filter.1 (hS hX)).2).trans ?_
    rw [sum_const, nsmul_eq_mul, ← mul_assoc, ENNReal.ofReal_mul (by positivity)]
    gcongr
    rw [← ENNReal.ofReal_natCast]
    refine ENNReal.ofReal_le_ofReal ?_
    have := (card_le_card hS).trans (hc L N j b hb)
    have h2 : (S.card : ℝ) ≤ c := by exact_mod_cast this
    nlinarith
  have hle : ENNReal.ofReal C' * k ≤ ENNReal.ofReal ((c + 1) * C') * k := by
    gcongr
    nlinarith [(Nat.cast_nonneg c : (0 : ℝ) ≤ c)]
  refine ⟨fun b hb => ?_, fun b hb X => ?_⟩
  · unfold Qb
    split_ifs with h
    · rw [AddSubmonoidClass.coe_finsetSum]
      exact hsum b hb _ subset_rfl
    · simp [Tj_zero]
  · unfold Jb
    split_ifs with h h'
    · rw [NegMemClass.coe_neg, Tj_neg', AddSubmonoidClass.coe_finsetSum]
      refine hsum b hb _ ?_
      intro Y hY
      simp only [mem_filter] at hY ⊢
      exact ⟨hY.1, hY.2.1⟩
    · exact (hterm b hb X (by simp [smallSets, h.2.1]) h.2.2).trans hle
    · simp [Tj_zero]

/-! ### `E:vj` and `e:step-V` -/

theorem four_le_of_L₀ {L : ℕ} (hL : 2 ^ (d + 3) + 8 * d + 1 ≤ L) : (4 : ℝ) ≤ L := by
  have : 8 ≤ 2 ^ (d + 3) := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (d + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : 4 ≤ L := by omega
  exact_mod_cast this

/-- `coupling_bounds`, with the information `2^{d+3} + 8d + 1 ≤ L₀` on `L₀`. -/
theorem coupling_bounds' (hd : 3 ≤ d) : ∃ (C₀ : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧
    2 ^ (d + 3) + 8 * d + 1 ≤ L₀ ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∀ (N j : ℕ), j < N → ∀ (ℓ₀ : ℝ), 0 < ℓ₀ →
    ∀ (C : Matrix (Lam d L N) (Lam d L N) ℝ), GoodCov j ℓ₀ C →
    ∀ (V : Vcoup) (K : Act d L N) (A : ℝ), 1 ≤ A → InK j K →
      (∀ b ∈ blockIdx (d := d) (L := L) (N := N) j,
        Tj d (L : ℝ) j (ellj d L ℓ₀ j) (Qb j K b : Alg d L N) ≤
          ENNReal.ofReal C₀ * Knorm j (ellj d L ℓ₀ j) A K) ∧
      (∀ b ∈ blockIdx (d := d) (L := L) (N := N) j, ∀ X : Finset (Lam d L N),
        Tj d (L : ℝ) j (ellj d L ℓ₀ j) (Jb j K b X : Alg d L N) ≤
          ENNReal.ofReal C₀ * Knorm j (ellj d L ℓ₀ j) A K) ∧
      (∀ b ∈ blockIdx (d := d) (L := L) (N := N) j,
        Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1))
            (((uVnext j C V K).1 * (blockSet (L := L) (N := N) j b).card) • (1 : Alg d L N) +
              (uVnext j C V K).2.eval (blockSet j b)) ≤
          Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V +
            ENNReal.ofReal C₀ * Knorm j (ellj d L ℓ₀ j) A K) ∧
      (∀ b ∈ blockIdx (d := d) (L := L) (N := N) (j + 1),
        Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1))
            (((uVnext j C V K).1 * (blockSet (L := L) (N := N) (j + 1) b).card) •
                (1 : Alg d L N) + (uVnext j C V K).2.eval (blockSet (j + 1) b) -
              EC C (theta (V.eval (blockSet (L := L) (N := N) (j + 1) b)))) ≤
          ENNReal.ofReal (C₀ * (L : ℝ) ^ d) * Knorm j (ellj d L ℓ₀ j) A K) := by
  obtain ⟨C₀, L₀, hC₀, hL₀, hQJ⟩ := QJ_bounds hd
  refine ⟨C₀, L₀, hC₀, hL₀, ?_⟩
  intro L _ hL N j hj ℓ₀ hℓ₀ C hC V K A hA hK
  obtain ⟨hQ, hJ⟩ := hQJ L hL N j hj ℓ₀ hℓ₀ K A hA hK
  have hL3 : 2 ^ (d + 3) ≤ L := by omega
  have hL4 : (4 : ℝ) ≤ L := four_le_of_L₀ (hL₀.trans hL)
  refine ⟨hQ, hJ, fun b hb => ?_, fun b' _ => ?_⟩
  · rw [← uVnext_spec (by omega) hL3 hj hC.covInv hC.symm' V hK hb]
    refine (Tj_EC_theta_le hd hL4 hℓ₀ j hC.psd hC.norm _).trans ((tNorm_sub_le _ _).trans ?_)
    exact add_le_add (Tj_le_Vnorm V hb) (hQ b hb)
  · have hP : IsPolymer j (blockSet (L := L) (N := N) (j + 1) b') :=
      IsPolymer.of_succ (isPolymer_blockSet (L := L) (N := N) (j + 1) b')
    rw [← uVnext_spec_polymer (by omega) hL3 hj hC.covInv hC.symm' V hK hP, map_sub, map_sub,
      sub_sub_cancel_left, Tj_neg']
    refine (Tj_EC_theta_le hd hL4 hℓ₀ j hC.psd hC.norm _).trans ((tNorm_sum_le _ _).trans ?_)
    refine (sum_le_sum fun b hb => hQ b (mem_blockIdx_of_mem_blocks hb)).trans ?_
    rw [sum_const, nsmul_eq_mul, ← mul_assoc]
    gcongr
    rw [mul_comm, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hC₀]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hC₀)
    have := nb_blockSet_succ_le (L := L) (N := N) j b'
    rw [nb] at this
    exact_mod_cast this

/-- The bounds `E:Q`, the bound on `J`, `E:vj`, and `e:step-V`. The constant `C₀` depends only
on `d`. -/
theorem coupling_bounds {d : ℕ} (hd : 3 ≤ d) : ∃ (C₀ : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∀ (N j : ℕ), j < N → ∀ (ℓ₀ : ℝ), 0 < ℓ₀ →
    ∀ (C : Matrix (Lam d L N) (Lam d L N) ℝ), GoodCov j ℓ₀ C →
    ∀ (V : Vcoup) (K : Act d L N) (A : ℝ), 1 ≤ A → InK j K →
      (∀ b ∈ blockIdx (d := d) (L := L) (N := N) j,
        Tj d (L : ℝ) j (ellj d L ℓ₀ j) (Qb j K b : Alg d L N) ≤
          ENNReal.ofReal C₀ * Knorm j (ellj d L ℓ₀ j) A K) ∧
      (∀ b ∈ blockIdx (d := d) (L := L) (N := N) j, ∀ X : Finset (Lam d L N),
        Tj d (L : ℝ) j (ellj d L ℓ₀ j) (Jb j K b X : Alg d L N) ≤
          ENNReal.ofReal C₀ * Knorm j (ellj d L ℓ₀ j) A K) ∧
      (∀ b ∈ blockIdx (d := d) (L := L) (N := N) j,
        Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1))
            (((uVnext j C V K).1 * (blockSet (L := L) (N := N) j b).card) • (1 : Alg d L N) +
              (uVnext j C V K).2.eval (blockSet j b)) ≤
          Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V +
            ENNReal.ofReal C₀ * Knorm j (ellj d L ℓ₀ j) A K) ∧
      (∀ b ∈ blockIdx (d := d) (L := L) (N := N) (j + 1),
        Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1))
            (((uVnext j C V K).1 * (blockSet (L := L) (N := N) (j + 1) b).card) •
                (1 : Alg d L N) + (uVnext j C V K).2.eval (blockSet (j + 1) b) -
              EC C (theta (V.eval (blockSet (L := L) (N := N) (j + 1) b)))) ≤
          ENNReal.ofReal (C₀ * (L : ℝ) ^ d) * Knorm j (ellj d L ℓ₀ j) A K) := by
  obtain ⟨C₀, L₀, hC₀, -, h⟩ := coupling_bounds' hd
  exact ⟨C₀, L₀, hC₀, h⟩

/-! ### (a) `E:vj` for `u_{j+1}`, `V_{j+1}` and for polymers -/

/-- `E:vj`: for `B ∈ 𝓑_j`, `|u_{j+1}| |B| ≤ ‖V‖_j + C₀ ‖K‖_j` and
`‖V_{j+1}(B)‖_{T_{j+1}(ℓ_{j+1})} ≤ 2 (‖V‖_j + C₀ ‖K‖_j)`; for `X ∈ 𝒫_j`,
`‖(u+V)_{j+1}(X)‖_{T_{j+1}(ℓ_{j+1})} ≤ |𝓑_j(X)| (‖V‖_j + C₀ ‖K‖_j)`. -/
theorem uVnext_bounds (hd : 3 ≤ d) : ∃ (C₀ : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧
    2 ^ (d + 3) + 8 * d + 1 ≤ L₀ ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∀ (N j : ℕ), j < N → ∀ (ℓ₀ : ℝ), 0 < ℓ₀ →
    ∀ (C : Matrix (Lam d L N) (Lam d L N) ℝ), GoodCov j ℓ₀ C →
    ∀ (V : Vcoup) (K : Act d L N) (A : ℝ), 1 ≤ A → InK j K →
      (∀ b ∈ blockIdx (d := d) (L := L) (N := N) j,
        ENNReal.ofReal (‖(uVnext j C V K).1‖ * (blockSet (L := L) (N := N) j b).card) ≤
          Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V +
            ENNReal.ofReal C₀ * Knorm j (ellj d L ℓ₀ j) A K) ∧
      (∀ b ∈ blockIdx (d := d) (L := L) (N := N) j,
        Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1))
            ((uVnext j C V K).2.eval (blockSet (L := L) (N := N) j b)) ≤
          2 * (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V +
            ENNReal.ofReal C₀ * Knorm j (ellj d L ℓ₀ j) A K)) ∧
      (∀ X : Finset (Lam d L N), IsPolymer j X →
        Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1))
            (((uVnext j C V K).1 * X.card) • (1 : Alg d L N) + (uVnext j C V K).2.eval X) ≤
          nb j X * (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V +
            ENNReal.ofReal C₀ * Knorm j (ellj d L ℓ₀ j) A K)) := by
  obtain ⟨C₀, L₀, hC₀, hL₀, hcb⟩ := coupling_bounds' hd
  refine ⟨C₀, L₀, hC₀, hL₀, ?_⟩
  intro L _ hL N j hj ℓ₀ hℓ₀ C hC V K A hA hK
  obtain ⟨-, -, hvj, -⟩ := hcb L hL N j hj ℓ₀ hℓ₀ C hC V K A hA hK
  have hL0 : (0 : ℝ) < L := by linarith [four_le_of_L₀ (hL₀.trans hL)]
  have hh : (0 : ℝ) < (L : ℝ) ^ (j + 1) := by positivity
  have hℓ := ellj_pos (d := d) hL0 hℓ₀ (j + 1)
  set a := Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V +
    ENNReal.ofReal C₀ * Knorm j (ellj d L ℓ₀ j) A K
  set u := (uVnext j C V K).1
  set V' := (uVnext j C V K).2
  have hu : ∀ b ∈ blockIdx (d := d) (L := L) (N := N) j,
      ENNReal.ofReal (‖u‖ * (blockSet (L := L) (N := N) j b).card) ≤ a := by
    intro b hb
    refine le_trans (le_of_eq ?_) ((abs_ε_le hh hℓ _).trans (hvj b hb))
    congr 1
    simp [ε_eval]
  refine ⟨hu, fun b hb => ?_, fun X hX => ?_⟩
  · have e : V'.eval (blockSet (L := L) (N := N) j b) =
        ((u * (blockSet (L := L) (N := N) j b).card) • (1 : Alg d L N) +
          V'.eval (blockSet j b)) - (u * (blockSet (L := L) (N := N) j b).card) • 1 := by abel
    rw [e, two_mul]
    refine (tNorm_sub_le _ _).trans (add_le_add (hvj b hb) ?_)
    rw [tNorm_smul]
    refine le_trans ?_ (hu b hb)
    calc ENNReal.ofReal ‖u * (blockSet (L := L) (N := N) j b).card‖ *
          Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1)) (1 : Alg d L N)
        ≤ ENNReal.ofReal ‖u * (blockSet (L := L) (N := N) j b).card‖ * 1 := by
          gcongr; exact tNorm_one_le hh hℓ
      _ = _ := by rw [mul_one, norm_mul, Complex.norm_natCast]
  · have e : ((u * X.card) • (1 : Alg d L N) + V'.eval X) =
        ∑ b ∈ blocks j X, ((u * (blockSet (L := L) (N := N) j b).card) • (1 : Alg d L N) +
          V'.eval (blockSet j b)) := by
      rw [sum_add_distrib, ← sum_smul, ← mul_sum, ← eval_polymer V' hX, card_polymer hX]
      push_cast; rfl
    rw [e]
    refine (tNorm_sum_le _ _).trans ?_
    refine (sum_le_sum fun b hb => hvj b (mem_blockIdx_of_mem_blocks hb)).trans ?_
    rw [sum_const, nsmul_eq_mul]
    rfl

/-! ### Real-valued bookkeeping -/

section RealAux

variable {X : Type*} [DecidableEq X] [Fintype X] {E : Type*} [Fintype E] [DecidableEq E]
  [AddAction (E → ℕ) X] {p : ℕ} {h ℓ : ℝ}

theorem tn_add {F G : Grassmann.N X} {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hF : tNorm E p h ℓ F ≤ ENNReal.ofReal s) (hG : tNorm E p h ℓ G ≤ ENNReal.ofReal t) :
    tNorm E p h ℓ (F + G) ≤ ENNReal.ofReal (s + t) :=
  (tNorm_add_le F G).trans (by rw [ENNReal.ofReal_add hs ht]; exact add_le_add hF hG)

theorem tn_sub {F G : Grassmann.N X} {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hF : tNorm E p h ℓ F ≤ ENNReal.ofReal s) (hG : tNorm E p h ℓ G ≤ ENNReal.ofReal t) :
    tNorm E p h ℓ (F - G) ≤ ENNReal.ofReal (s + t) :=
  (tNorm_sub_le F G).trans (by rw [ENNReal.ofReal_add hs ht]; exact add_le_add hF hG)

theorem tn_smul (r : ℂ) {F : Grassmann.N X} {t : ℝ}
    (hF : tNorm E p h ℓ F ≤ ENNReal.ofReal t) :
    tNorm E p h ℓ (r • F) ≤ ENNReal.ofReal (‖r‖ * t) := by
  rw [tNorm_smul, ENNReal.ofReal_mul (norm_nonneg _)]
  gcongr

theorem tn_one (hh : 0 < h) (hℓ : 0 < ℓ) : tNorm E p h ℓ (1 : Grassmann.N X) ≤ ENNReal.ofReal 1 :=
  by rw [ENNReal.ofReal_one]; exact tNorm_one_le hh hℓ

end RealAux

theorem real_of_le {v k : ENNReal} {ε : ℝ} (hε : 0 ≤ ε) (h : v + k ≤ ENNReal.ofReal ε) :
    v = ENNReal.ofReal v.toReal ∧ k = ENNReal.ofReal k.toReal ∧ 0 ≤ v.toReal ∧ 0 ≤ k.toReal ∧
      v.toReal + k.toReal ≤ ε := by
  have hv : v ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_self_add.trans h)
  have hk : k ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_add_self.trans h)
  refine ⟨(ENNReal.ofReal_toReal hv).symm, (ENNReal.ofReal_toReal hk).symm,
    ENNReal.toReal_nonneg, ENNReal.toReal_nonneg, ?_⟩
  rw [← ENNReal.toReal_add hv hk]
  exact ENNReal.toReal_le_of_le_ofReal hε h

/-- The block data in real form: under `‖V‖_j + ‖K‖_j ≤ ε`, with `v = ‖V‖_j`, `k = ‖K‖_j` and
`a = v + C₀ k`, for `B ∈ 𝓑_j`: `‖V(B)‖_{T_j(ℓ_j)} ≤ v`, `|u_{j+1}| |B| ≤ a`,
`‖V_{j+1}(B)‖_{T_{j+1}(ℓ_{j+1})} ≤ 2a`. -/
theorem block_real (hd : 3 ≤ d) : ∃ (C₀ : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧
    2 ^ (d + 3) + 8 * d + 1 ≤ L₀ ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∀ (N j : ℕ), j < N → ∀ (ℓ₀ : ℝ), 0 < ℓ₀ →
    ∀ (C : Matrix (Lam d L N) (Lam d L N) ℝ), GoodCov j ℓ₀ C →
    ∀ (V : Vcoup) (K : Act d L N) (A : ℝ), 1 ≤ A → InK j K → ∀ ε : ℝ, 0 ≤ ε →
      Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V + Knorm j (ellj d L ℓ₀ j) A K ≤ ENNReal.ofReal ε →
      Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V = ENNReal.ofReal (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V).toReal ∧
      Knorm j (ellj d L ℓ₀ j) A K = ENNReal.ofReal (Knorm j (ellj d L ℓ₀ j) A K).toReal ∧
      0 ≤ (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V).toReal ∧
      0 ≤ (Knorm j (ellj d L ℓ₀ j) A K).toReal ∧
      (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V).toReal + (Knorm j (ellj d L ℓ₀ j) A K).toReal ≤
        ε ∧
      ∀ b ∈ blockIdx (d := d) (L := L) (N := N) j,
        Tj d (L : ℝ) j (ellj d L ℓ₀ j) (V.eval (blockSet (L := L) (N := N) j b)) ≤
          ENNReal.ofReal (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V).toReal ∧
        ‖(uVnext j C V K).1 * (blockSet (L := L) (N := N) j b).card‖ ≤
          (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V).toReal + C₀ * (Knorm j (ellj d L ℓ₀ j) A K).toReal ∧
        Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1))
            ((uVnext j C V K).2.eval (blockSet (L := L) (N := N) j b)) ≤
          ENNReal.ofReal (2 * ((Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V).toReal +
            C₀ * (Knorm j (ellj d L ℓ₀ j) A K).toReal)) := by
  obtain ⟨C₀, L₀, hC₀, hL₀, hub⟩ := uVnext_bounds hd
  refine ⟨C₀, L₀, hC₀, hL₀, ?_⟩
  intro L _ hL N j hj ℓ₀ hℓ₀ C hC V K A hA hK ε hε hvk
  obtain ⟨hu, hV', -⟩ := hub L hL N j hj ℓ₀ hℓ₀ C hC V K A hA hK
  obtain ⟨hv, hk, hv0, hk0, hvkr⟩ := real_of_le hε hvk
  have ha : Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V +
    ENNReal.ofReal C₀ * Knorm j (ellj d L ℓ₀ j) A K =
      ENNReal.ofReal ((Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V).toReal +
        C₀ * (Knorm j (ellj d L ℓ₀ j) A K).toReal) := by
    rw [ENNReal.ofReal_add hv0 (by positivity), ENNReal.ofReal_mul hC₀, ← hv, ← hk]
  refine ⟨hv, hk, hv0, hk0, hvkr, fun b hb => ⟨?_, ?_, ?_⟩⟩
  · rw [← hv]; exact Tj_le_Vnorm V hb
  · have := hu b hb
    rw [ha, ENNReal.ofReal_le_ofReal_iff (by positivity)] at this
    rwa [norm_mul, Complex.norm_natCast]
  · have := hV' b hb
    rw [ha, ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num)] at this
    exact this

/-! ### (b), (c): `e:deltaIbd` and Lemma `lem:smallset-V` -/

set_option maxHeartbeats 1000000 in
/-- `e:deltaIbd` for one block, `‖δI(B)‖_{T_{j+1}(ℓ_{j+1})} ≤ C₁ (‖V‖_j + ‖K‖_j)`, and
Lemma `lem:smallset-V` (`e:Kblock2`), `‖𝔼[δI(B) + θ Q(B)]‖_{T_{j+1}(ℓ_{j+1})} ≤
C₁ (‖V‖_j^2 + ‖K‖_j^2)`, for `‖V‖_j + ‖K‖_j ≤ ε₀`, with `C₁, ε₀` depending only on `d`. -/
theorem dI_bounds (hd : 3 ≤ d) : ∃ (C₁ ε₀ : ℝ) (L₀ : ℕ), 0 ≤ C₁ ∧ 0 < ε₀ ∧
    2 ^ (d + 3) + 8 * d + 1 ≤ L₀ ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∀ (N j : ℕ), j < N → ∀ (ℓ₀ : ℝ), 0 < ℓ₀ →
    ∀ (C : Matrix (Lam d L N) (Lam d L N) ℝ), GoodCov j ℓ₀ C →
    ∀ (V : Vcoup) (K : Act d L N) (A : ℝ), 1 ≤ A → InK j K →
      Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V + Knorm j (ellj d L ℓ₀ j) A K ≤ ENNReal.ofReal ε₀ →
      ∀ b ∈ blockIdx (d := d) (L := L) (N := N) j,
        Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1))
            (dI j C V K b : Grassmann.N (Lam d L N ⊕ Lam d L N)) ≤
          ENNReal.ofReal C₁ * (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V + Knorm j (ellj d L ℓ₀ j) A K) ∧
        Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1))
            (EC C ((dI j C V K b : Grassmann.N (Lam d L N ⊕ Lam d L N)) +
              theta (Qb j K b : Alg d L N))) ≤
          ENNReal.ofReal C₁ *
            (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V ^ 2 + Knorm j (ellj d L ℓ₀ j) A K ^ 2) := by
  obtain ⟨C₀, L₀, hC₀, hL₀, hbr⟩ := block_real hd
  refine ⟨27 + 26 * C₀ ^ 2 + 12 + 10 * C₀, 1 / (4 * (1 + C₀)), L₀, by positivity, by positivity,
    hL₀, ?_⟩
  intro L _ hL N j hj ℓ₀ hℓ₀ C hC V K A hA hK hvk b hb
  obtain ⟨hv, hk, hv0, hk0, hvkr, hblk⟩ :=
    hbr L hL N j hj ℓ₀ hℓ₀ C hC V K A hA hK _ (by positivity) hvk
  obtain ⟨hF, hc, hG⟩ := hblk b hb
  have hL3 : 2 ^ (d + 3) ≤ L := by omega
  have hL4 : (4 : ℝ) ≤ L := four_le_of_L₀ (hL₀.trans hL)
  have hL0 : (0 : ℝ) < L := by linarith
  have hh : (0 : ℝ) < (L : ℝ) ^ (j + 1) := by positivity
  have hh' : (0 : ℝ) < (L : ℝ) ^ j := by positivity
  have hℓ := ellj_pos (d := d) hL0 hℓ₀ (j + 1)
  have hℓ' := ellj_pos (d := d) hL0 hℓ₀ j
  set v := Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V
  set k := Knorm j (ellj d L ℓ₀ j) A K
  set vr := v.toReal
  set kr := k.toReal
  set a := vr + C₀ * kr with ha_def
  set u := (uVnext j C V K).1
  set V' := (uVnext j C V K).2
  set B := blockSet (L := L) (N := N) j b
  set c := u * B.card
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a ≤ 1 / 4 := by
    have h1 : a ≤ (1 + C₀) * (vr + kr) := by nlinarith
    have h2 : (1 + C₀) * (vr + kr) ≤ (1 + C₀) * (1 / (4 * (1 + C₀))) := by gcongr
    have h3 : (1 + C₀) * (1 / (4 * (1 + C₀))) = 1 / 4 := by field_simp
    linarith
  have hvr1 : vr ≤ 1 / 4 := by nlinarith
  have hcabs : ‖-c‖ ≤ 1 := by rw [norm_neg]; linarith
  have hE1 : ‖Complex.exp (-c) - 1‖ ≤ 2 * a :=
    (Complex.norm_exp_sub_one_le hcabs).trans (by rw [norm_neg]; linarith)
  have hE : ‖Complex.exp (-c)‖ ≤ 2 := by
    have := norm_sub_norm_le (Complex.exp (-c)) 1
    rw [norm_one] at this; linarith
  have hE2 : ‖Complex.exp (-c) - 1 + c‖ ≤ a ^ 2 := by
    have := Complex.norm_exp_sub_one_sub_id_le hcabs
    rw [sub_neg_eq_add, norm_neg] at this
    refine this.trans ?_
    exact pow_le_pow_left₀ (norm_nonneg _) hc 2
  set F : EvR (Lam d L N) := VE V B
  set G : EvR (Lam d L N) := VE V' B
  have hεF : ε ((-F : EvR (Lam d L N)) : Alg d L N) = 0 := by simp [F, ε_eval]
  have hεG : ε ((-G : EvR (Lam d L N)) : Alg d L N) = 0 := by simp [G, ε_eval]
  have hFn : Tj d (L : ℝ) j (ellj d L ℓ₀ j) ((-F : EvR (Lam d L N)) : Alg d L N) ≤
      ENNReal.ofReal vr := by
    simpa [F, Tj_neg'] using hF
  have hGn : Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1)) ((-G : EvR (Lam d L N)) : Alg d L N) ≤
      ENNReal.ofReal (2 * a) := by
    simpa [G, Tj_neg'] using hG
  have hdI' : dI j C V K b = thetaE (gexp (-F)) - inclE (Complex.exp (-c) • gexp (-G)) := rfl
  have hC1 : 0 ≤ 27 + 26 * C₀ ^ 2 + 12 + 10 * C₀ := by positivity
  refine ⟨?_, ?_⟩
  · have hdI : (dI j C V K b : Grassmann.N (Lam d L N ⊕ Lam d L N)) =
        theta ((gexp (-F) - 1 : EvR (Lam d L N)) : Alg d L N) -
          incl (Complex.exp (-c) • ((gexp (-G) - 1 : EvR (Lam d L N)) : Alg d L N) +
            (Complex.exp (-c) - 1) • (1 : Alg d L N)) := by
      rw [hdI']
      simp only [AddSubgroupClass.coe_sub, coe_thetaE, coe_inclE, OneMemClass.coe_one,
        map_sub, map_add, map_smul, map_one, SetLike.val_smul]
      module
    have hθ1 : Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1))
        (theta ((gexp (-F) - 1 : EvR (Lam d L N)) : Alg d L N)) ≤ ENNReal.ofReal (2 * vr) :=
      (tNorm_theta_le hh hℓ _).trans ((Tj_succ_le hd hL4 hℓ₀ j _).2.trans
        ((tNorm_gexp_sub_one_le hh' hℓ' hεF hv0 hFn).trans
          (ENNReal.ofReal_le_ofReal (exp_sub_one_le hv0 (by linarith)))))
    have hI1 : Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1))
        (Complex.exp (-c) • ((gexp (-G) - 1 : EvR (Lam d L N)) : Alg d L N) +
          (Complex.exp (-c) - 1) • (1 : Alg d L N)) ≤
        ENNReal.ofReal (2 * (2 * (2 * a)) + 2 * a * 1) := by
      refine tn_add (by positivity) (by positivity)
        ((tn_smul (Complex.exp (-c)) ((tNorm_gexp_sub_one_le hh hℓ hεG (by positivity) hGn).trans
          (ENNReal.ofReal_le_ofReal (exp_sub_one_le (by positivity) (by linarith))))).trans ?_)
        ((tn_smul (Complex.exp (-c) - 1) (tn_one hh hℓ)).trans ?_)
      · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hE (by positivity))
      · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hE1 (by norm_num))
    rw [hdI]
    refine (tn_sub (by positivity) (by positivity) hθ1 ((tNorm_incl_le hh hℓ _).trans hI1)).trans ?_
    rw [hv, hk, ← ENNReal.ofReal_add hv0 hk0, ← ENNReal.ofReal_mul hC1]
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith [mul_nonneg hC₀ hv0, mul_nonneg hC₀ hk0, mul_nonneg (sq_nonneg C₀) hv0,
      mul_nonneg (sq_nonneg C₀) hk0]
  · have hs := uVnext_spec (by omega) hL3 hj hC.covInv hC.symm' V hK hb
    have hQ' : EC C (theta (Qb j K b : Alg d L N)) =
        EC C (theta (V.eval B)) - (c • (1 : Alg d L N) + V'.eval B) := by
      rw [← hs, map_sub, map_sub]; abel
    have hid : EC C ((dI j C V K b : Grassmann.N (Lam d L N ⊕ Lam d L N)) +
          theta (Qb j K b : Alg d L N)) =
        EC C (theta ((gexp (-F) - 1 - (-F) : EvR (Lam d L N)) : Alg d L N)) -
          (Complex.exp (-c) • ((gexp (-G) - 1 - (-G) : EvR (Lam d L N)) : Alg d L N) +
            (Complex.exp (-c) - 1 + c) • (1 : Alg d L N) - (Complex.exp (-c) - 1) • V'.eval B) := by
      rw [hdI', map_add, hQ']
      simp only [AddSubgroupClass.coe_sub, NegMemClass.coe_neg, coe_thetaE, coe_inclE,
        OneMemClass.coe_one, map_sub, map_smul, map_one, map_neg, SetLike.val_smul,
        EC_one, EC_incl, F, G, coe_VE]
      module
    have hT1 : Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1))
        (EC C (theta ((gexp (-F) - 1 - (-F) : EvR (Lam d L N)) : Alg d L N))) ≤
        ENNReal.ofReal (vr ^ 2) :=
      (Tj_EC_theta_le hd hL4 hℓ₀ j hC.psd hC.norm _).trans
        ((tNorm_gexp_sub_one_sub_le hh' hℓ' hεF hv0 hFn).trans
          (ENNReal.ofReal_le_ofReal (exp_sub_one_sub_le hv0 (by linarith))))
    have p1 : 0 ≤ ‖Complex.exp (-c)‖ * (2 * a) ^ 2 := mul_nonneg (norm_nonneg _) (sq_nonneg _)
    have p2 : 0 ≤ ‖Complex.exp (-c) - 1 + c‖ * 1 := mul_nonneg (norm_nonneg _) zero_le_one
    have p3 : 0 ≤ ‖Complex.exp (-c) - 1‖ * (2 * a) := mul_nonneg (norm_nonneg _) (by linarith)
    have hT2 : Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1))
        (Complex.exp (-c) • ((gexp (-G) - 1 - (-G) : EvR (Lam d L N)) : Alg d L N) +
            (Complex.exp (-c) - 1 + c) • (1 : Alg d L N) - (Complex.exp (-c) - 1) • V'.eval B) ≤
        ENNReal.ofReal (‖Complex.exp (-c)‖ * (2 * a) ^ 2 + ‖Complex.exp (-c) - 1 + c‖ * 1 +
          ‖Complex.exp (-c) - 1‖ * (2 * a)) := by
      have t1 : Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1))
          (Complex.exp (-c) • ((gexp (-G) - 1 - (-G) : EvR (Lam d L N)) : Alg d L N)) ≤
          ENNReal.ofReal (‖Complex.exp (-c)‖ * (2 * a) ^ 2) :=
        tn_smul (Complex.exp (-c)) ((tNorm_gexp_sub_one_sub_le hh hℓ hεG (by positivity) hGn).trans
          (ENNReal.ofReal_le_ofReal (exp_sub_one_sub_le (by positivity) (by linarith))))
      have t2 : Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1))
          ((Complex.exp (-c) - 1 + c) • (1 : Alg d L N)) ≤
          ENNReal.ofReal (‖Complex.exp (-c) - 1 + c‖ * 1) :=
        tn_smul (Complex.exp (-c) - 1 + c) (tn_one hh hℓ)
      have t3 : Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1))
          ((Complex.exp (-c) - 1) • V'.eval B) ≤
          ENNReal.ofReal (‖Complex.exp (-c) - 1‖ * (2 * a)) :=
        tn_smul (Complex.exp (-c) - 1) hG
      exact tn_sub (add_nonneg p1 p2) p3 (tn_add p1 p2 t1 t2) t3
    rw [hid]
    refine (tn_sub (sq_nonneg _) (add_nonneg (add_nonneg p1 p2) p3) hT1 hT2).trans ?_
    rw [hv, hk, ← ENNReal.ofReal_pow hv0, ← ENNReal.ofReal_pow hk0,
      ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), ← ENNReal.ofReal_mul hC1]
    refine ENNReal.ofReal_le_ofReal ?_
    have e1 : ‖Complex.exp (-c)‖ * (2 * a) ^ 2 ≤ 2 * (2 * a) ^ 2 :=
      mul_le_mul_of_nonneg_right hE (sq_nonneg _)
    have e3 : ‖Complex.exp (-c) - 1‖ * (2 * a) ≤ 2 * a * (2 * a) :=
      mul_le_mul_of_nonneg_right hE1 (by positivity)
    have e4 : a ^ 2 ≤ 2 * vr ^ 2 + 2 * C₀ ^ 2 * kr ^ 2 := by
      rw [ha_def]; nlinarith [sq_nonneg (vr - C₀ * kr)]
    have e5 : 0 ≤ C₀ ^ 2 * kr ^ 2 := by positivity
    nlinarith [sq_nonneg vr, sq_nonneg kr, mul_nonneg (sq_nonneg C₀) (sq_nonneg vr),
      mul_nonneg hC₀ (sq_nonneg vr), mul_nonneg hC₀ (sq_nonneg kr)]

/-! ### (d): Lemma `lem:pert12` -/

/-- **Lemma `lem:pert12`**: for `X ∈ 𝒫_j` with `X̄ = U`,
`‖e^{u_{j+1}|U|} e^{-(u+V)_{j+1}(U ∖ X)}‖_{T_{j+1}(ℓ_{j+1})} ≤ 2^{|𝓑_j(X)|}` if
`‖V‖_j + ‖K‖_j ≤ c₀ / L^d`, with `c₀` depending only on `d`. -/
theorem pert12 (hd : 3 ≤ d) : ∃ (c₀ : ℝ) (L₀ : ℕ), 0 < c₀ ∧ 2 ^ (d + 3) + 8 * d + 1 ≤ L₀ ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∀ (N j : ℕ), j < N → ∀ (ℓ₀ : ℝ), 0 < ℓ₀ →
    ∀ (C : Matrix (Lam d L N) (Lam d L N) ℝ), GoodCov j ℓ₀ C →
    ∀ (V : Vcoup) (K : Act d L N) (A : ℝ), 1 ≤ A → InK j K →
      Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V + Knorm j (ellj d L ℓ₀ j) A K ≤
        ENNReal.ofReal (c₀ / (L : ℝ) ^ d) →
      ∀ X U : Finset (Lam d L N), IsPolymer j X → clo j X = U →
        Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1))
            (Complex.exp ((uVnext j C V K).1 * U.card) • (InextPow j C V K (U \ X) : Alg d L N)) ≤
          2 ^ nb j X := by
  obtain ⟨C₀, L₀, hC₀, hL₀, hbr⟩ := block_real hd
  refine ⟨1 / (6 * (1 + C₀)), L₀, by positivity, hL₀, ?_⟩
  intro L _ hL N j hj ℓ₀ hℓ₀ C hC V K A hA hK hvk X U hX hU
  have hL4 : (4 : ℝ) ≤ L := four_le_of_L₀ (hL₀.trans hL)
  have hL0 : (0 : ℝ) < L := by linarith
  have hLd : (0 : ℝ) < (L : ℝ) ^ d := by positivity
  obtain ⟨-, -, hv0, hk0, hvkr, hblk⟩ :=
    hbr L hL N j hj ℓ₀ hℓ₀ C hC V K A hA hK _ (by positivity) hvk
  have hh : (0 : ℝ) < (L : ℝ) ^ (j + 1) := by positivity
  have hℓ := ellj_pos (d := d) hL0 hℓ₀ (j + 1)
  set vr := (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V).toReal
  set kr := (Knorm j (ellj d L ℓ₀ j) A K).toReal
  set a := vr + C₀ * kr
  set u := (uVnext j C V K).1
  set ur := u.re
  have hre : ∀ n : ℕ, (u * (n : ℂ)).re = ur * n := fun n => by simp [ur]
  have ha0 : 0 ≤ a := by positivity
  have ha1 : 6 * a * (L : ℝ) ^ d ≤ 1 := by
    have h1 : a ≤ (1 + C₀) * (vr + kr) := by nlinarith
    have h2 : (1 + C₀) * (vr + kr) ≤ (1 + C₀) * (1 / (6 * (1 + C₀)) / (L : ℝ) ^ d) := by
      gcongr
    have h3 : (1 + C₀) * (1 / (6 * (1 + C₀)) / (L : ℝ) ^ d) * (6 * (L : ℝ) ^ d) = 1 := by
      field_simp
    nlinarith
  subst hU
  have hUp : IsPolymer (j + 1) (clo j X) := isPolymer_clo j X
  have hUj : IsPolymer j (clo j X) := IsPolymer.of_succ hUp
  have hXU : X ⊆ clo j X := subset_clo j X
  have hY : IsPolymer j (clo j X \ X) := IsPolymer.sdiff hUj hX
  have hI : ∀ b ∈ blocks j (clo j X \ X),
      Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1)) ((Inext j C V K b : EvR (Lam d L N)) : Alg d L N)
        ≤ ENNReal.ofReal (Real.exp (-(ur * (blockSet (L := L) (N := N) j b).card) + 2 * a)) := by
    intro b hb
    obtain ⟨-, -, hG⟩ := hblk b (mem_blockIdx_of_mem_blocks hb)
    have hεG : ε (((-(VE (uVnext j C V K).2 (blockSet (L := L) (N := N) j b))) : EvR (Lam d L N)) : Alg d L N) =
        0 := by simp [ε_eval]
    have hGn : Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1))
        (((-(VE (uVnext j C V K).2 (blockSet (L := L) (N := N) j b))) : EvR (Lam d L N)) : Alg d L N) ≤
        ENNReal.ofReal (2 * a) := by
      simpa [Tj_neg'] using hG
    rw [Inext, SetLike.val_smul]
    refine (tn_smul _ (tNorm_gexp_le hh hℓ hεG (by positivity) hGn)).trans (le_of_eq ?_)
    rw [Complex.norm_exp, Complex.neg_re, hre, Real.exp_add]
  have hux : ur * X.card ≤ nb j X * a := by
    rw [card_polymer hX]
    push_cast
    rw [mul_sum]
    calc ∑ b ∈ blocks j X, ur * ((blockSet (L := L) (N := N) j b).card : ℝ)
        ≤ ∑ _b ∈ blocks j X, a := sum_le_sum fun b hb => by
          rw [← hre]
          exact (Complex.re_le_norm _).trans (hblk b (mem_blockIdx_of_mem_blocks hb)).2.1
      _ = nb j X * a := by rw [sum_const, nsmul_eq_mul, nb]
  have hnbY : (nb j (clo j X \ X) : ℝ) ≤ nb j (clo j X) := by
    exact_mod_cast card_le_card (image_subset_image sdiff_subset)
  have hnbX : (nb j X : ℝ) ≤ nb j (clo j X) := by
    exact_mod_cast card_le_card (image_subset_image hXU)
  have hnbU : (nb j (clo j X) : ℝ) ≤ (L : ℝ) ^ d * nb j X := by
    exact_mod_cast (nb_le_of_succ hUp).trans (Nat.mul_le_mul_left _ (nb_clo_le j X))
  have he : Real.exp (1 / 2) ≤ 2 := by
    have := (abs_le.1 (Real.abs_exp_sub_one_le (x := 1 / 2) (by norm_num))).2
    norm_num at this ⊢; linarith
  rw [Tj_smul', Complex.norm_exp, hre, InextPow]
  calc ENNReal.ofReal (Real.exp (ur * (clo j X).card)) *
        Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1))
          ((∏ b ∈ blocks j (clo j X \ X), Inext j C V K b : EvR (Lam d L N)) : Alg d L N)
      ≤ ENNReal.ofReal (Real.exp (ur * (clo j X).card)) * ∏ b ∈ blocks j (clo j X \ X),
          ENNReal.ofReal (Real.exp (-(ur * (blockSet (L := L) (N := N) j b).card) + 2 * a)) := by
        gcongr
        exact (tNorm_prod_le hh hℓ _ _).trans (prod_le_prod' hI)
    _ = ENNReal.ofReal (Real.exp (ur * X.card + 2 * a * nb j (clo j X \ X))) := by
        rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le),
          ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_sum, ← Real.exp_add]
        congr 2
        rw [sum_add_distrib, sum_neg_distrib, ← mul_sum, sum_const, nsmul_eq_mul,
          ← Nat.cast_sum, ← card_polymer hY, nb, ← card_sdiff_add_card_eq_card hXU]
        push_cast; ring
    _ ≤ ENNReal.ofReal (2 ^ nb j X) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have s1 : ur * X.card + 2 * a * nb j (clo j X \ X) ≤ 3 * a * nb j (clo j X) := by
          nlinarith [mul_le_mul_of_nonneg_left hnbX ha0, mul_le_mul_of_nonneg_left hnbY ha0]
        have s2 : 3 * a * (nb j (clo j X) : ℝ) ≤ 3 * a * ((L : ℝ) ^ d * nb j X) :=
          mul_le_mul_of_nonneg_left hnbU (by positivity)
        have s3 : 3 * a * ((L : ℝ) ^ d * nb j X) ≤ (nb j X : ℝ) * (1 / 2) := by
          nlinarith [mul_le_mul_of_nonneg_right ha1 (Nat.cast_nonneg (α := ℝ) (nb j X))]
        calc Real.exp (ur * X.card + 2 * a * nb j (clo j X \ X))
            ≤ Real.exp ((nb j X : ℝ) * (1 / 2)) := Real.exp_le_exp.2 (by linarith)
          _ = Real.exp (1 / 2) ^ nb j X := Real.exp_nat_mul _ _
          _ ≤ 2 ^ nb j X := pow_le_pow_left₀ (Real.exp_pos _).le he _
    _ = 2 ^ nb j X := by rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]

/-! ### (e): `θ J` and `𝔼 θ J` -/

/-- `‖θ J(B, X)‖_{T_{j+1}(ℓ_{j+1})}, ‖𝔼 θ J(B, X)‖_{T_{j+1}(ℓ_{j+1})} ≤ C₀ ‖K‖_j`, and the same
for `Q(B)`. -/
theorem thetaJ_bounds (hd : 3 ≤ d) : ∃ (C₀ : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧
    2 ^ (d + 3) + 8 * d + 1 ≤ L₀ ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∀ (N j : ℕ), j < N → ∀ (ℓ₀ : ℝ), 0 < ℓ₀ →
    ∀ (C : Matrix (Lam d L N) (Lam d L N) ℝ), GoodCov j ℓ₀ C →
    ∀ (K : Act d L N) (A : ℝ), 1 ≤ A → InK j K → ∀ b ∈ blockIdx (d := d) (L := L) (N := N) j,
      (∀ X : Finset (Lam d L N),
        Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1)) (theta (Jb j K b X : Alg d L N)) ≤
          ENNReal.ofReal C₀ * Knorm j (ellj d L ℓ₀ j) A K ∧
        Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1)) (EC C (theta (Jb j K b X : Alg d L N))) ≤
          ENNReal.ofReal C₀ * Knorm j (ellj d L ℓ₀ j) A K) ∧
      Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1)) (theta (Qb j K b : Alg d L N)) ≤
          ENNReal.ofReal C₀ * Knorm j (ellj d L ℓ₀ j) A K ∧
      Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1)) (EC C (theta (Qb j K b : Alg d L N))) ≤
          ENNReal.ofReal C₀ * Knorm j (ellj d L ℓ₀ j) A K := by
  obtain ⟨C₀, L₀, hC₀, hL₀, hQJ⟩ := QJ_bounds hd
  refine ⟨C₀, L₀, hC₀, hL₀, ?_⟩
  intro L _ hL N j hj ℓ₀ hℓ₀ C hC K A hA hK b hb
  have hL4 : (4 : ℝ) ≤ L := four_le_of_L₀ (hL₀.trans hL)
  have hL0 : (0 : ℝ) < L := by linarith
  have hh : (0 : ℝ) < (L : ℝ) ^ (j + 1) := by positivity
  obtain ⟨hQ, hJ⟩ := hQJ L hL N j hj ℓ₀ hℓ₀ K A hA hK
  have key : ∀ F : Alg d L N, Tj d (L : ℝ) j (ellj d L ℓ₀ j) F ≤
      ENNReal.ofReal C₀ * Knorm j (ellj d L ℓ₀ j) A K →
      Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1)) (theta F) ≤
          ENNReal.ofReal C₀ * Knorm j (ellj d L ℓ₀ j) A K ∧
        Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1)) (EC C (theta F)) ≤
          ENNReal.ofReal C₀ * Knorm j (ellj d L ℓ₀ j) A K := fun F hF =>
    ⟨(tNorm_theta_le hh (ellj_pos hL0 hℓ₀ _) _).trans ((Tj_succ_le hd hL4 hℓ₀ j _).2.trans hF),
      (Tj_EC_theta_le hd hL4 hℓ₀ j hC.psd hC.norm _).trans hF⟩
  exact ⟨fun X => key _ (hJ b hb X), key _ (hQ b hb)⟩

end

end Step
