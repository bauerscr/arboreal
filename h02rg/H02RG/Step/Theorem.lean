import Step.EstSmall
import Step.EstLarge
import Step.EstNonlin
import Step.Structure

/-!
# Theorem `thm:step`

For `d ≥ 3`, `L ≥ L₀(d)`, `A ≥ A₀(L, d)` there is `ε = ε(L, A) > 0` such that for `j < N`,
covariances `C = C_{j+1}` satisfying `GoodCov` and `(V_j, K_j)` with `K_j ∈ 𝒦_j` and
`‖V_j‖_j + ‖K_j‖_j ≤ ε`:

* `e:step-V`: `‖u_{j+1} + V_{j+1} - 𝔼_{C_{j+1}} θ V_j‖_{j+1} ≤ O(L^d ‖K_j‖_j)`;
* `e:step-K`: `‖K_{j+1}‖_{j+1} ≤ O(L^{-d_+} + A^{-η}) ‖K_j‖_j + O(A^ν)(‖V_j‖_j^2 + ‖K_j‖_j^2)`
  if `j + 1 < N`, and the same with `L^{-d_+}` replaced by `L^d` if `j + 1 = N`.

`η, ν` and the constants in `O(·)` depend only on `d`.
-/

namespace Step

noncomputable section

open Finset Grassmann Loc FRD


theorem ennreal_add_sq_le (a b : ENNReal) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  have h := ENNReal.rpow_add_le_mul_rpow_add_rpow a b (p := 2) (by norm_num)
  simp only [show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one] at h
  have e : ∀ x : ENNReal, x ^ (2 : ℝ) = x ^ 2 := fun x => by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  rwa [e, e, e] at h

theorem wnorm_add_le {d L N : ℕ} [NeZero L] (j : ℕ) (ℓ A : ℝ) (U : Finset (Lam d L N))
    (F G : EvR (Lam d L N)) : wnorm j ℓ A U (F + G) ≤ wnorm j ℓ A U F + wnorm j ℓ A U G := by
  unfold wnorm
  rw [← mul_add]
  gcongr
  exact tNorm_add_le _ _

/-- **Theorem `thm:step`.** -/
theorem step {d : ℕ} (hd : 3 ≤ d) : ∃ (C₀ η ν : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧ 0 < η ∧ 0 < ν ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∃ ε : ℝ, 0 < ε ∧
    ∀ (N j : ℕ), j < N → ∀ (ℓ₀ : ℝ), 0 < ℓ₀ →
    ∀ (C : Matrix (Lam d L N) (Lam d L N) ℝ), GoodCov j ℓ₀ C →
    ∀ (V : Vcoup) (K : Act d L N), InK j K →
      Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V + Knorm j (ellj d L ℓ₀ j) A K ≤ ENNReal.ofReal ε →
      (⨆ b ∈ blockIdx (L := L) (N := N) (j + 1),
        Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1))
            (((uVnext j C V K).1 * (blockSet (L := L) (N := N) (j + 1) b).card) •
                (1 : Alg d L N) + (uVnext j C V K).2.eval (blockSet (j + 1) b) -
              EC C (theta (V.eval (blockSet (L := L) (N := N) (j + 1) b))))) ≤
          ENNReal.ofReal (C₀ * (L : ℝ) ^ d) * Knorm j (ellj d L ℓ₀ j) A K ∧
      (j + 1 < N → InK (j + 1) (Knext j C V K)) ∧
      Knorm (j + 1) (ellj d L ℓ₀ (j + 1)) A (Knext j C V K) ≤
        ENNReal.ofReal (C₀ * ((if j + 1 < N then (L : ℝ) ^ (-dplus d) else (L : ℝ) ^ d) +
            A ^ (-η))) * Knorm j (ellj d L ℓ₀ j) A K +
          ENNReal.ofReal (C₀ * A ^ ν) *
            (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V ^ 2 + Knorm j (ellj d L ℓ₀ j) A K ^ 2) := by
  obtain ⟨CV, LV, hCV, hV⟩ := coupling_bounds hd
  obtain ⟨CS, LS, hCS, hS⟩ := smallset_bound hd
  obtain ⟨CL, η, νL, LL, hCL, hη, hνL, hLg⟩ := largeset_bound hd
  obtain ⟨CN, νN, LN, hCN, hνN, hNl⟩ := nonlinear_bound hd
  set ν := max (max νL νN) 1 with hν
  have hν1 : 1 ≤ ν := le_max_right _ _
  set C₀ := CV + CS + 3 * CL + 2 * CN + 1 with hC₀
  refine ⟨C₀, η, ν, max (max LV LS) (max (max LL LN) (2 ^ (d + 3))), by positivity, hη,
    by linarith, ?_⟩
  intro L _ hL
  have hLV : LV ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hLS : LS ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hLL : LL ≤ L :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hL
  have hLN : LN ≤ L :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hL
  have hL8 : 2 ^ (d + 3) ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
  obtain ⟨εS, hεS, hS'⟩ := hS L hLS
  obtain ⟨AL, hAL1, hAL⟩ := hLg L hLL
  obtain ⟨AN, hAN1, hAN⟩ := hNl L hLN
  refine ⟨max (max AL AN) ((L : ℝ) ^ d), le_trans hAL1 (le_trans (le_max_left _ _)
    (le_max_left _ _)), ?_⟩
  intro A hA
  have hAAL : AL ≤ A := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hA
  have hAAN : AN ≤ A := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hA
  have hALd : (L : ℝ) ^ d ≤ A := le_trans (le_max_right _ _) hA
  have hA1 : 1 ≤ A := hAL1.trans hAAL
  obtain ⟨εL, hεL, hL'⟩ := hAL A hAAL
  obtain ⟨εN, hεN, hN'⟩ := hAN A hAAN
  refine ⟨min εS (min εL εN), lt_min hεS (lt_min hεL hεN), ?_⟩
  intro N j hj ℓ₀ hℓ₀ C hC V K hK hsmall
  have hsS := hsmall.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _))
  have hsL := hsmall.trans (ENNReal.ofReal_le_ofReal
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hsN := hsmall.trans (ENNReal.ofReal_le_ofReal
    ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨-, -, -, hVb⟩ := hV L hLV N j hj ℓ₀ hℓ₀ C hC V K A hA1 hK
  set v := Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V
  set k := Knorm j (ellj d L ℓ₀ j) A K
  refine ⟨?_, fun hj' => InK_Knext (by omega) hL8 hj' hC V hK, ?_⟩
  · refine iSup₂_le fun b hb => (hVb b hb).trans ?_
    gcongr
    linarith
  · refine iSup₂_le fun U hU => ?_
    have hUc : IsConn (j + 1) U := by simpa [connSets] using hU
    have eS := hS' N j hj ℓ₀ hℓ₀ C hC V K A hA1 hK hsS U hUc
    have eL := hL' N j hj ℓ₀ hℓ₀ C hC V K hK hsL U hUc
    have eN := hN' N j hj ℓ₀ hℓ₀ C hC V K hK hsN U hUc
    have hdec : Knext j C V K U =
        LlinS j C V K U + (LlinL j C V K U + (R1 j C V K U + R2 j C V K U + R3 j C V K U)) := by
      rw [Knext_eq_decomp, Llin_eq]; abel
    have hsplit : wnorm (j + 1) (ellj d L ℓ₀ (j + 1)) A U (Knext j C V K U) ≤
        wnorm (j + 1) (ellj d L ℓ₀ (j + 1)) A U (LlinS j C V K U) +
          (wnorm (j + 1) (ellj d L ℓ₀ (j + 1)) A U (LlinL j C V K U) +
            wnorm (j + 1) (ellj d L ℓ₀ (j + 1)) A U
              (R1 j C V K U + R2 j C V K U + R3 j C V K U)) := by
      rw [hdec]
      exact (wnorm_add_le _ _ _ _ _ _).trans (add_le_add le_rfl (wnorm_add_le _ _ _ _ _ _))
    refine hsplit.trans ((add_le_add eS (add_le_add eL eN)).trans ?_)
    set f : ℝ := if j + 1 < N then (L : ℝ) ^ (-dplus d) else (L : ℝ) ^ d with hf
    have hf0 : 0 ≤ f := by rw [hf]; split_ifs <;> positivity
    have hA0 : 0 ≤ A := by linarith
    have hAη : 0 ≤ A ^ (-η) := Real.rpow_nonneg hA0 _
    have hAν : 0 ≤ A ^ ν := Real.rpow_nonneg hA0 _
    have hLdν : (L : ℝ) ^ d ≤ A ^ ν :=
      hALd.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hA1 hν1)
    have hνL' : A ^ νL ≤ A ^ ν :=
      Real.rpow_le_rpow_of_exponent_le hA1 ((le_max_left _ _).trans (le_max_left _ _))
    have hνN' : A ^ νN ≤ A ^ ν :=
      Real.rpow_le_rpow_of_exponent_le hA1 ((le_max_right _ _).trans (le_max_left _ _))
    have hsq : (v + k) ^ 2 ≤ 2 * (v ^ 2 + k ^ 2) := ennreal_add_sq_le v k
    have hkk : k * (k + v) ≤ 2 * (v ^ 2 + k ^ 2) := by
      calc k * (k + v) ≤ (v + k) * (v + k) := by
            rw [add_comm k v]; gcongr; exact le_add_self
        _ = (v + k) ^ 2 := (sq _).symm
        _ ≤ _ := hsq
    -- first order terms
    have h1 : ENNReal.ofReal (CS * f) * k + ENNReal.ofReal (CL * A ^ (-η)) * k ≤
        ENNReal.ofReal (C₀ * (f + A ^ (-η))) * k := by
      rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      gcongr
      nlinarith
    -- second order terms
    have h2 : ENNReal.ofReal (CS * (L : ℝ) ^ d) * (v ^ 2 + k ^ 2) +
        ENNReal.ofReal (CL * A ^ νL) * (v + k) ^ 2 +
        ENNReal.ofReal (CN * A ^ νN) * k * (k + v) ≤
        ENNReal.ofReal (C₀ * A ^ ν) * (v ^ 2 + k ^ 2) := by
      calc _ ≤ ENNReal.ofReal (CS * A ^ ν) * (v ^ 2 + k ^ 2) +
            ENNReal.ofReal (CL * A ^ ν) * (2 * (v ^ 2 + k ^ 2)) +
            ENNReal.ofReal (CN * A ^ ν) * (2 * (v ^ 2 + k ^ 2)) := by
            rw [mul_assoc (ENNReal.ofReal (CN * A ^ νN))]
            gcongr
        _ = ENNReal.ofReal ((CS + 2 * CL + 2 * CN) * A ^ ν) * (v ^ 2 + k ^ 2) := by
            rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_ofNat 2,
              ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
              ← add_mul, ← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity),
              ← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 2; ring
        _ ≤ _ := by gcongr; nlinarith
    calc ENNReal.ofReal (CS * f) * k + ENNReal.ofReal (CS * (L : ℝ) ^ d) * (v ^ 2 + k ^ 2) +
          (ENNReal.ofReal (CL * A ^ (-η)) * k + ENNReal.ofReal (CL * A ^ νL) * (v + k) ^ 2 +
            ENNReal.ofReal (CN * A ^ νN) * k * (k + v))
        = (ENNReal.ofReal (CS * f) * k + ENNReal.ofReal (CL * A ^ (-η)) * k) +
          (ENNReal.ofReal (CS * (L : ℝ) ^ d) * (v ^ 2 + k ^ 2) +
            ENNReal.ofReal (CL * A ^ νL) * (v + k) ^ 2 +
            ENNReal.ofReal (CN * A ^ νN) * k * (k + v)) := by ring
      _ ≤ _ := add_le_add h1 h2


end

end Step
