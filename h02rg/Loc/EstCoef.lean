import Loc.EstMu
import Loc.EstMono

/-!
# Bounds on the matrix `A_X` and on the coefficients of `Loc`

* `‖M(X)‖_T ≤ |X| ℓ^2 L^{-j deg M}` and `M(X) ∈ 𝒩(X^□)`;
* `‖A_X(M, β)‖ ≤ C |X| L^{j (deg β - deg M)}` (from the bound on `μ_β`);
* `‖c_M(F)‖ ≤ C ℓ^{-2} L^{j deg M} ‖F‖_{T_j(ℓ)} / |X|`, by solving the triangular system
  `c A_X = μ(F)` degree by degree (`A_X(M, β) = |X| δ_{Mβ}` for `deg β ≤ deg M`).
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD Matrix

variable {d L N : ℕ} [NeZero L]

theorem monoSet_mem (hd : 1 ≤ d) {j : ℕ} {X : Finset (Lam d L N)} (hX : IsPolymer j X)
    (M : Mono d) : monoSet M X ∈ NX (nbhd j X : Set (Lam d L N)) := by
  refine Subalgebra.sum_mem _ fun x hx => monoAt_mem fun a ha => ?_
  refine mem_nbhd_of_near hd hX hx ?_
  rw [add_sub_cancel_left]
  exact (supNorm_prj_le a).trans ha

theorem tNorm_monoSet_le {p : ℕ} (hp : 2 ≤ p) {h ℓ : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ) (M : Mono d)
    (X : Finset (Lam d L N)) :
    tNorm (Dir d) p h ℓ (monoSet M X) ≤ ENNReal.ofReal (X.card * (ℓ ^ 2 * (h ^ M.deg)⁻¹)) := by
  refine (tNorm_sum_le _ _).trans ?_
  calc ∑ x ∈ X, tNorm (Dir d) p h ℓ (monoAt M x)
      ≤ ∑ _x ∈ X, ENNReal.ofReal (ℓ ^ 2 * (h ^ M.deg)⁻¹) :=
        sum_le_sum fun x _ => tNorm_monoAt_le hp hh hℓ M x
    _ = ENNReal.ofReal (X.card * (ℓ ^ 2 * (h ^ M.deg)⁻¹)) := by
        rw [sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (p := (X.card : ℝ)) (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]

theorem toReal_tNorm_monoSet_le {p : ℕ} (hp : 2 ≤ p) {h ℓ : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ)
    (M : Mono d) (X : Finset (Lam d L N)) :
    (tNorm (Dir d) p h ℓ (monoSet M X)).toReal ≤ X.card * (ℓ ^ 2 * (h ^ M.deg)⁻¹) :=
  ENNReal.toReal_le_of_le_ofReal (by positivity) (tNorm_monoSet_le hp hh hℓ M X)

/-- `‖A_X(M, β)‖ ≤ C |X| L^{j deg β} / L^{j deg M}`. -/
theorem exists_Amat_bound (d : ℕ) (hd : 1 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℕ) [NeZero L],
    2 ^ (d + 3) + 8 * d < L → ∀ N j : ℕ, j < N → ∀ X : Finset (Lam d L N), IsSmall j X →
    ∀ M β : Mono d, ‖Amat X M β‖ ≤ C * X.card * ((L : ℝ) ^ j) ^ β.deg / ((L : ℝ) ^ j) ^ M.deg := by
  obtain ⟨C, hC0, hC⟩ := exists_mu_bound d
  refine ⟨C, hC0, fun L _ hL N j hj X hX M β => ?_⟩
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hs : (0 : ℝ) < (L : ℝ) ^ j := by positivity
  have h1 := hC L hL N j hj X hX (monoSet M X) (monoSet_mem hd hX.1 M) β 1 one_pos
  have h2 := toReal_tNorm_monoSet_le (show 2 ≤ pPhi d by simp [pPhi]; omega) hs one_pos M X
  rw [Amat]
  calc ‖mu (base X) β (monoSet M X)‖
      ≤ C * (1 ^ 2)⁻¹ * ((L : ℝ) ^ j) ^ β.deg * (Tj d (L : ℝ) j 1 (monoSet M X)).toReal := h1
    _ ≤ C * (1 ^ 2)⁻¹ * ((L : ℝ) ^ j) ^ β.deg * (X.card * (1 ^ 2 * (((L : ℝ) ^ j) ^ M.deg)⁻¹)) := by
        gcongr
    _ = C * X.card * ((L : ℝ) ^ j) ^ β.deg / ((L : ℝ) ^ j) ^ M.deg := by
        field_simp

/-- The coefficients solve `c A_X = μ(F)`. -/
theorem locCoef_vecMul {X : Finset (Lam d L N)} (hX : Patch X) (hne : X.Nonempty)
    (F : Alg d L N) : locCoef X F ᵥ* Amat X = fun β => mu (base X) β F := by
  rw [locCoef, vecMul_vecMul,
    nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (Amat_isUnit hX hne)), vecMul_one]

/-- The triangular structure: `μ_β(F) = |X| c_β + ∑_{deg M < deg β} c_M A_X(M, β)`. -/
theorem mu_eq_triangular {X : Finset (Lam d L N)} (hX : Patch X) (hne : X.Nonempty)
    (F : Alg d L N) (β : Mono d) :
    mu (base X) β F = locCoef X F β * X.card +
      ∑ M ∈ univ.filter (fun M : Mono d => M.deg < β.deg), locCoef X F M * Amat X M β := by
  have h := congrFun (locCoef_vecMul hX hne F) β
  simp only [vecMul, dotProduct] at h
  rw [← h, ← sum_filter_add_sum_filter_not univ (fun M : Mono d => M.deg < β.deg), add_comm]
  congr 1
  rw [sum_eq_single β]
  · rw [Amat_eq hX le_rfl, if_pos rfl]
  · intro M hM hMβ
    simp only [mem_filter, mem_univ, true_and, not_lt] at hM
    rw [Amat_eq hX hM, if_neg (Ne.symm hMβ), mul_zero]
  · intro h; simp at h

/-- `‖c_M(F)‖ ≤ C ℓ^{-2} L^{j deg M} ‖F‖_{T_j(ℓ)} / |X|`. -/
theorem exists_locCoef_bound (d : ℕ) (hd : 1 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℕ) [NeZero L],
    2 ^ (d + 3) + 8 * d < L → ∀ N j : ℕ, j < N → ∀ X : Finset (Lam d L N), IsSmall j X →
    ∀ F ∈ NX (nbhd j X : Set (Lam d L N)), ∀ ℓ : ℝ, 0 < ℓ → ∀ M : Mono d,
      ‖locCoef X F M‖ ≤
        C * (ℓ ^ 2)⁻¹ * ((L : ℝ) ^ j) ^ M.deg * (Tj d (L : ℝ) j ℓ F).toReal / X.card := by
  obtain ⟨Cμ, hCμ0, hCμ⟩ := exists_mu_bound d
  obtain ⟨Ca, hCa0, hCa⟩ := exists_Amat_bound d hd
  set n : ℝ := (Fintype.card (Mono d) : ℝ)
  set q : ℝ := 1 + n * Ca
  have hq : 1 ≤ q := by simp only [q]; nlinarith [show (0 : ℝ) ≤ n by positivity]
  refine ⟨Cμ * q ^ 2, by positivity, fun L _ hL N j hj X hX F hF ℓ hℓ => ?_⟩
  have hne : X.Nonempty := hX.2.1.1
  have hpatch := patch_of_small hL hj hX
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set s : ℝ := (L : ℝ) ^ j
  have hs : 0 < s := by positivity
  set T : ℝ := (Tj d (L : ℝ) j ℓ F).toReal
  have hT : 0 ≤ T := ENNReal.toReal_nonneg
  have hX0 : (0 : ℝ) < X.card := by exact_mod_cast hne.card_pos
  set c := locCoef X F
  -- induction on the degree
  have key : ∀ k : ℕ, ∀ β : Mono d, β.deg = k →
      ‖c β‖ * X.card ≤ Cμ * q ^ k * (ℓ ^ 2)⁻¹ * s ^ k * T := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro β hβ
      have htri := mu_eq_triangular hpatch hne F β
      have hμ := hCμ L hL N j hj X hX F hF β ℓ hℓ
      rw [hβ] at hμ
      have hsum : ‖∑ M ∈ univ.filter (fun M : Mono d => M.deg < β.deg), c M * Amat X M β‖ ≤
          ∑ _M ∈ univ.filter (fun M : Mono d => M.deg < β.deg),
            Cμ * q ^ (k - 1) * Ca * (ℓ ^ 2)⁻¹ * s ^ k * T := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun M hM => ?_)
        simp only [mem_filter, mem_univ, true_and] at hM
        rw [hβ] at hM
        have h1 := ih M.deg hM M rfl
        have h2 := hCa L hL N j hj X hX M β
        rw [hβ] at h2
        rw [norm_mul]
        have hc' : ‖c M‖ ≤ Cμ * q ^ M.deg * (ℓ ^ 2)⁻¹ * s ^ M.deg * T / X.card := by
          rw [le_div_iff₀ hX0]; exact h1
        have hqk : q ^ M.deg ≤ q ^ (k - 1) := pow_le_pow_right₀ hq (by omega)
        calc ‖c M‖ * ‖Amat X M β‖
            ≤ (Cμ * q ^ M.deg * (ℓ ^ 2)⁻¹ * s ^ M.deg * T / X.card) *
              (Ca * X.card * s ^ k / s ^ M.deg) := by gcongr
          _ = Cμ * q ^ M.deg * Ca * (ℓ ^ 2)⁻¹ * s ^ k * T := by
              field_simp
          _ ≤ Cμ * q ^ (k - 1) * Ca * (ℓ ^ 2)⁻¹ * s ^ k * T := by gcongr
      have hcard : ((univ.filter (fun M : Mono d => M.deg < β.deg)).card : ℝ) ≤ n := by
        show _ ≤ ((Fintype.card (Mono d) : ℕ) : ℝ)
        exact_mod_cast (card_filter_le _ _).trans_eq card_univ
      rw [sum_const, nsmul_eq_mul] at hsum
      have e1 : c β * X.card = mu (base X) β F -
          ∑ M ∈ univ.filter (fun M : Mono d => M.deg < β.deg), c M * Amat X M β := by
        rw [htri]; ring
      have habs : ‖c β‖ * X.card = ‖c β * X.card‖ := by
        rw [norm_mul, Complex.norm_natCast]
      rw [habs, e1]
      refine (norm_sub_le _ _).trans ?_
      rcases Nat.eq_zero_or_pos k with hk | hk
      · -- no lower degrees
        subst hk
        have hempty : univ.filter (fun M : Mono d => M.deg < β.deg) = ∅ := by
          ext M; simp [hβ]
        rw [hempty, sum_empty, norm_zero, add_zero]
        simpa using hμ
      · have hA : 0 ≤ Cμ * q ^ (k - 1) * Ca * (ℓ ^ 2)⁻¹ * s ^ k * T := by positivity
        calc ‖mu (base X) β F‖ + ‖∑ M ∈ univ.filter (fun M : Mono d => M.deg < β.deg),
              c M * Amat X M β‖
            ≤ Cμ * (ℓ ^ 2)⁻¹ * s ^ k * T +
              n * (Cμ * q ^ (k - 1) * Ca * (ℓ ^ 2)⁻¹ * s ^ k * T) := by
              gcongr
              exact hsum.trans (mul_le_mul_of_nonneg_right hcard hA)
          _ = Cμ * (ℓ ^ 2)⁻¹ * s ^ k * T * (1 + n * Ca * q ^ (k - 1)) := by ring
          _ ≤ Cμ * (ℓ ^ 2)⁻¹ * s ^ k * T * (q ^ (k - 1) + n * Ca * q ^ (k - 1)) := by
              gcongr
              exact one_le_pow₀ hq
          _ = Cμ * q ^ k * (ℓ ^ 2)⁻¹ * s ^ k * T := by
              have : q ^ k = q ^ (k - 1) * q := by
                rw [← pow_succ]; congr 1; omega
              rw [this]; simp only [q]; ring
  intro M
  have h := key M.deg M rfl
  rw [le_div_iff₀ hX0]
  have hdeg : M.deg ≤ 2 := Mono.deg_le_two M
  calc ‖c M‖ * X.card ≤ Cμ * q ^ M.deg * (ℓ ^ 2)⁻¹ * s ^ M.deg * T := h
    _ ≤ Cμ * q ^ 2 * (ℓ ^ 2)⁻¹ * s ^ M.deg * T := by
        gcongr

end

end Loc
