import Step2.Coup.CoupPast6
import Step2.D2.D2Bub2

/-!
# The past coefficients summed: `∑_{k<j} b_{j,k} + q_{j,j} = -(𝔅(w + C_j) - 𝔅(w)) + T_j` (V2′)

With `A = V_g(B_+)`, `B = V_g(Λ)` (the `g`-monomials, homogeneous of degree `4`):

* `FC_sub_Xc_degLe4`: `F_C(A, B) - X_C(A, B)` has degree `≤ 4`, so
  `mu4 𝓛_{C'} F_C(A, B) = mu4 𝓛_{C'} X_C(A, B)` is **linear in `C`** (`mu4_lop_FC_sum`);
* `mu4_FC_exp`: `mu4 F_C(e^{𝓛_{C'}}A, e^{𝓛_{C'}}B) = mu4 F_C(A,B) + mu4 X_C(𝓛_{C'}A, B)
  + mu4 X_C(𝓛_{C'}B, A)` (the tadpoles);
* `mu4_lop_FC_eq`: `mu4 𝓛_{C_j} F_w(A, B) = mu4 F_{w+C_j}(A,B) - mu4 F_w(A,B) - mu4 F_{C_j}(A,B)
  + mu4 X_w(𝓛_{C_j}A, B) + mu4 X_w(𝓛_{C_j}B, A)`;
* `negBub_eq_mu4_FC`: `negBub C X i₀ = mu4 F_C(A, B) / (2|X|)`;
* `FlowSeq.past_sum_eq`: **for `s ≡ 1`**,
  `∑_{k<j} b_{j,k} + q_{j,j} = negBub(w + C_j) - negBub(w) + T_j`, `w = ∑_{k<j} C_k`,
  `T_j = (mu4 X_w(𝓛_{C_j}A, B) + mu4 X_w(𝓛_{C_j}B, A)) / (2|B_+|)`.
  With `𝔅 = -negBub` this is `-(𝔅(w + C_j) - 𝔅(w)) + T_j`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

section General

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

theorem Xc_add_cov (C₁ C₂ : Matrix Λ Λ ℂ) (A B : N Λ) :
    Xc (C₁ + C₂) A B = Xc C₁ A B + Xc C₂ A B := by
  simp only [Xc, Matrix.add_apply, add_smul, sum_add_distrib]

theorem Xc_zero_cov (A B : N Λ) : Xc (0 : Matrix Λ Λ ℂ) A B = 0 := by
  simp [Xc]

theorem Xc_sum_cov {ι : Type*} (s : Finset ι) (C : ι → Matrix Λ Λ ℂ) (A B : N Λ) :
    Xc (∑ k ∈ s, C k) A B = ∑ k ∈ s, Xc (C k) A B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Xc_zero_cov]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, Xc_add_cov, ih]

theorem Xc_degLe_zero_left (C : Matrix Λ Λ ℂ) {R : N Λ} (hR : DegLe 0 R) (B : N Λ) :
    Xc C R B = 0 := by
  simp [Xc, D_eq_zero_of_degLe_zero hR]

/-- **`F_C(A, B) - X_C(A, B)` has degree `≤ 4`** for even `A` and `A`, `B` of degree `≤ 4`. -/
theorem FC_sub_Xc_degLe4 (C : Matrix Λ Λ ℂ) {A B : N Λ} (hA : inv' A = A) (hA4 : DegLe 4 A)
    (hB4 : DegLe 4 B) : DegLe 4 (FC C A B - Xc C A B) := by
  set RA := expLC (-C) A - A - LopC (-C) A
  set RB := expLC (-C) B - B - LopC (-C) B
  have hRA : DegLe 0 RA := hA4.exp_sub2 (-C) (n := 0)
  have hRB : DegLe 0 RB := hB4.exp_sub2 (-C) (n := 0)
  have hLA : DegLe 2 (LopC C A) := hA4.lop C
  have hLB : DegLe 2 (LopC C B) := hB4.lop C
  have hnA : LopC (-C) A = -LopC C A := by rw [LopC_neg]; rfl
  have hnB : LopC (-C) B = -LopC C B := by rw [LopC_neg]; rfl
  have eA : expLC (-C) A = A - LopC C A + RA := by simp only [RA, hnA]; abel
  have eB : expLC (-C) B = B - LopC C B + RB := by simp only [RB, hnB]; abel
  set Q := LopC C A * B + A * LopC C B
  set Rest := LopC C A * LopC C B - LopC C A * RB + A * RB + RA * B - RA * LopC C B + RA * RB
  have hQ : DegLe 6 Q := (hLA.mul hB4).add (hA4.mul hLB)
  have hRest : DegLe 4 Rest := by
    have e1 : DegLe 4 (LopC C A * LopC C B) := hLA.mul hLB
    have e2 : DegLe 4 (LopC C A * RB) := (hLA.mul hRB).mono (by norm_num)
    have e3 : DegLe 4 (A * RB) := hA4.mul hRB
    have e4 : DegLe 4 (RA * B) := by simpa using hRA.mul hB4
    have e5 : DegLe 4 (RA * LopC C B) := (hRA.mul hLB).mono (by norm_num)
    have e6 : DegLe 4 (RA * RB) := (hRA.mul hRB).mono (by norm_num)
    simp only [Rest, sub_eq_add_neg]
    refine ((((e1.add ?_).add e3).add e4).add ?_).add e6
    · simpa using e2.smul (-1)
    · simpa using e5.smul (-1)
  set P := expLC (-C) A * expLC (-C) B
  have hP : P = A * B - Q + Rest := by
    simp only [P, eA, eB, Q, Rest]; noncomm_ring
  have hP8 : DegLe 8 P := by
    rw [hP]
    have h8 : DegLe 8 (A * B) := hA4.mul hB4
    rw [sub_eq_add_neg]
    exact (h8.add (by simpa using (hQ.mono (by norm_num)).smul (-1))).add (hRest.mono (by norm_num))
  have hE : DegLe 4 (expLC C P - P - LopC C P) := hP8.exp_sub2 C (n := 4)
  have hLAB := LopC_mul_even C hA B
  have hLP : LopC C P = LopC C A * B + A * LopC C B + Xc C A B - LopC C Q + LopC C Rest := by
    rw [hP, map_add, map_sub, hLAB]
  have e : FC C A B - Xc C A B = (expLC C P - P - LopC C P) + Rest + LopC C (-Q + Rest) := by
    have hF : FC C A B = expLC C P - A * B := rfl
    rw [hF, map_add, map_neg, hLP, hP]
    simp only [Q]; abel
  rw [e]
  have h1 : DegLe 4 (LopC C (-Q + Rest)) := by
    have : DegLe 6 (-Q + Rest) := by
      simpa using ((hQ.smul (-1)).add (hRest.mono (by norm_num)))
    exact this.lop C
  exact (hE.add hRest).add h1

end General

variable {d L N : ℕ} [NeZero L]

section Mu

variable (b : Lam d L N) (κ κ' : Fin d)

/-- `mu4 𝓛_{C'} F_C(A, B) = mu4 𝓛_{C'} X_C(A, B)`. -/
theorem mu4_lop_FC (C' C : Matrix (Lam d L N) (Lam d L N) ℂ) {A B : Alg d L N}
    (hA : inv' A = A) (hA4 : DegLe 4 A) (hB4 : DegLe 4 B) :
    mu4 b κ κ' (LopC C' (FC C A B)) = mu4 b κ κ' (LopC C' (Xc C A B)) := by
  have h := mu4_lop_of_degLe C' b κ κ' (FC_sub_Xc_degLe4 C hA hA4 hB4)
  rw [map_sub, mu4_sub, sub_eq_zero] at h
  exact h

/-- **Linearity in the covariance**: `mu4 𝓛_{C'} F_{∑ C_k}(A, B) = ∑ mu4 𝓛_{C'} F_{C_k}(A, B)`. -/
theorem mu4_lop_FC_sum (C' : Matrix (Lam d L N) (Lam d L N) ℂ) {ι : Type*} (s : Finset ι)
    (C : ι → Matrix (Lam d L N) (Lam d L N) ℂ) {A B : Alg d L N}
    (hA : inv' A = A) (hA4 : DegLe 4 A) (hB4 : DegLe 4 B) :
    mu4 b κ κ' (LopC C' (FC (∑ k ∈ s, C k) A B)) = ∑ k ∈ s, mu4 b κ κ' (LopC C' (FC (C k) A B)) := by
  rw [mu4_lop_FC b κ κ' C' _ hA hA4 hB4, Xc_sum_cov, map_sum, mu4_sum]
  exact sum_congr rfl fun k _ => (mu4_lop_FC b κ κ' C' _ hA hA4 hB4).symm

/-- **The tadpoles**: `mu4 F_C(e^{𝓛_{C'}}A, e^{𝓛_{C'}}B)
= mu4 F_C(A,B) + mu4 X_C(𝓛_{C'}A, B) + mu4 X_C(𝓛_{C'}B, A)`. -/
theorem mu4_FC_exp (C C' : Matrix (Lam d L N) (Lam d L N) ℂ) {A B : Alg d L N}
    (hA : inv' A = A) (hB : inv' B = B) (hA4 : DegLe 4 A) (hB4 : DegLe 4 B) :
    mu4 b κ κ' (FC C (expLC C' A) (expLC C' B)) =
      mu4 b κ κ' (FC C A B) + mu4 b κ κ' (Xc C (LopC C' A) B) +
        mu4 b κ κ' (Xc C (LopC C' B) A) := by
  set A' := expLC C' A - A
  set B' := expLC C' B - B
  have hA' : DegLe 2 A' := hA4.exp_sub C' (n := 2)
  have hB' : DegLe 2 B' := hB4.exp_sub C' (n := 2)
  have hAe : inv' A' = A' := by simp only [A', map_sub, expLC_even C' hA, hA]
  have hBe : inv' B' = B' := by simp only [B', map_sub, expLC_even C' hB, hB]
  have eA : expLC C' A = A + A' := by simp [A']
  have eB : expLC C' B = B + B' := by simp [B']
  rw [eA, eB, FC_add_left, FC_add_right, FC_add_right, mu4_add, mu4_add, mu4_add]
  -- the three corrections
  have h1 : mu4 b κ κ' (FC C A' B) = mu4 b κ κ' (Xc C (LopC C' A) B) := by
    have h := mu4_of_degLe ((FC_sub_Xc_degLe C hAe hA' hB4).mono (by norm_num)) b κ κ'
    rw [mu4_sub, sub_eq_zero] at h
    rw [h]
    have hR : DegLe 0 (expLC C' A - A - LopC C' A) := hA4.exp_sub2 C' (n := 0)
    have e : A' = LopC C' A + (expLC C' A - A - LopC C' A) := by simp only [A']; abel
    rw [e, Xc_add_left, Xc_degLe_zero_left C hR, add_zero]
  have h2 : mu4 b κ κ' (FC C A B') = mu4 b κ κ' (Xc C (LopC C' B) A) := by
    rw [FC_comm C hA hBe]
    have h := mu4_of_degLe ((FC_sub_Xc_degLe C hBe hB' hA4).mono (by norm_num)) b κ κ'
    rw [mu4_sub, sub_eq_zero] at h
    rw [h]
    have hR : DegLe 0 (expLC C' B - B - LopC C' B) := hB4.exp_sub2 C' (n := 0)
    have e : B' = LopC C' B + (expLC C' B - B - LopC C' B) := by simp only [B']; abel
    rw [e, Xc_add_left, Xc_degLe_zero_left C hR, add_zero]
  have h3 : mu4 b κ κ' (FC C A' B') = 0 := by
    have : DegLe 2 (FC C A' B') := DegLe.fc (n := 0) (m := 0) C hA' hB'
    exact mu4_of_degLe (this.mono (by norm_num)) b κ κ'
  rw [h1, h2, h3]; ring

/-- **The cross term**: `mu4 𝓛_{C_j} F_w(A, B) = mu4 F_{w+C_j}(A,B) - mu4 F_w(A,B)
- mu4 F_{C_j}(A,B) + mu4 X_w(𝓛_{C_j}A, B) + mu4 X_w(𝓛_{C_j}B, A)`. -/
theorem mu4_lop_FC_eq (w Cj : Matrix (Lam d L N) (Lam d L N) ℂ) {A B : Alg d L N}
    (hA : inv' A = A) (hB : inv' B = B) (hA4 : DegLe 4 A) (hB4 : DegLe 4 B) :
    mu4 b κ κ' (LopC Cj (FC w A B)) =
      mu4 b κ κ' (FC (w + Cj) A B) - mu4 b κ κ' (FC w A B) - mu4 b κ κ' (FC Cj A B) +
        (mu4 b κ κ' (Xc w (LopC Cj A) B) + mu4 b κ κ' (Xc w (LopC Cj B) A)) := by
  have h := mu4_FC_add_cov w Cj hA4 hB4 b κ κ'
  rw [mu4_FC_exp b κ κ' _ _ hA hB hA4 hB4, mu4_FC_exp b κ κ' _ _ hA hB hA4 hB4,
    Xc_add_cov, Xc_add_cov, mu4_add, mu4_add] at h
  linear_combination -h

end Mu

/-! ### The bubble as `mu4 F` -/

theorem even_VcoupL (Y : Finset (Lam d L N)) (v : Fin 4 → ℂ) : inv' (VcoupL Y v) = VcoupL Y v :=
  mem_Ev.1 (unif_mem_Ev _ _ _ _)

theorem degLe_VcoupL_eg (Y : Finset (Lam d L N)) : DegLe 4 (VcoupL Y (eC 3)) :=
  fun m z h => isHom_VcoupL_eg Y m z (by omega)

/-- **`negBub C X i₀ = mu4 F_C(V_g(X), V_g(Λ)) / (2|X|)`** for a `(j+1)`-block `X = B_+`. -/
theorem negBub_eq_mu4_FC (hL : 2 ^ (d + 3) + 8 * d < L) {j : ℕ} (hj : j < N) {b : Fin d → ℕ}
    (hb : b ∈ blockIdx (L := L) (N := N) j) (i₀ : Fin d) (C : Matrix (Lam d L N) (Lam d L N) ℂ) :
    negBub C (Bp (L := L) (N := N) j b) i₀ = mu4 (base (Bp (L := L) (N := N) j b)) i₀ i₀
      (FC C (VcoupL (Bp (L := L) (N := N) j b) (eC 3)) (VcoupL univ (eC 3))) /
        (2 * (Bp (L := L) (N := N) j b).card) := by
  let D : FlowSeq d L N := ⟨fun _ => C, fun _ => 1, fun _ => ⟨0, 0, 0, 0⟩⟩
  have h1 := D.betaQ_eq_negBub hL hj hb i₀
  have h2 := D.bubble_eq hL hj hb i₀
  have hDC : D.C j = C := rfl
  rw [hDC] at h1 h2
  rw [← h1, h2, mu4_FC_quartic _ (isHom_VcoupL_eg _) (isHom_VcoupL_eg _),
    c2_eq_X2 _ (even_VcoupL _ _), mu4_smul]
  have hc : ((Bp (L := L) (N := N) j b).card : ℂ) ≠ 0 := by
    have := (isSmall_clo (isSmall_blockSet_of_mem hb)).2.1.1.card_pos
    exact_mod_cast this.ne'
  field_simp
  ring

/-! ### The summed past coefficients -/

/-- The tadpole term `T_j = (mu4 X_w(𝓛_{C_j}A, B) + mu4 X_w(𝓛_{C_j}B, A)) / (2|X|)`, with
`A = V_g(X)`, `B = V_g(Λ)`. -/
def tadT (X : Finset (Lam d L N)) (i₀ : Fin d) (w Cj : Matrix (Lam d L N) (Lam d L N) ℂ) : ℂ :=
  (mu4 (base X) i₀ i₀ (Xc w (LopC Cj (VcoupL X (eC 3))) (VcoupL univ (eC 3))) +
    mu4 (base X) i₀ i₀ (Xc w (LopC Cj (VcoupL univ (eC 3))) (VcoupL X (eC 3)))) / (2 * X.card)

namespace FlowSeq

variable (D : FlowSeq d L N)

/-- **V2′: the summed past coefficients.** For `s ≡ 1` (as in `histFS`), `k < j`,
`w = ∑_{k<j} C_k`, `X = B_+`:
`∑_{k<j} b_{j,k} + q_{j,j} = negBub(w + C_j) - negBub(w) + T_j`, i.e. with `𝔅 = -negBub`,
`∑_{k<j} b_{j,k} + q_{j,j} = -(𝔅(w + C_j) - 𝔅(w)) + T_j`. -/
theorem past_sum_eq (hd : 1 ≤ d) (hL : 2 ^ (d + 3) + 8 * d < L) (hs : ∀ i, D.s i = 1) {j : ℕ}
    (hjN : j + 1 < N) {ℓ : ℝ} (hC : ∀ i, GoodCov2 i ℓ (D.C i)) {b : Fin d → ℕ}
    (hb : b ∈ blockIdx (L := L) (N := N) j) (i₀ : Fin d) :
    ∑ k ∈ range j, D.beta j k b i₀ (eC 3) (eC 3) 3 + D.betaQ j j b i₀ (eC 3) (eC 3) 3 =
      negBub (∑ k ∈ range j, D.C k + D.C j) (Bp (L := L) (N := N) j b) i₀ -
        negBub (∑ k ∈ range j, D.C k) (Bp (L := L) (N := N) j b) i₀ +
        tadT (Bp (L := L) (N := N) j b) i₀ (∑ k ∈ range j, D.C k) (D.C j) := by
  set X := Bp (L := L) (N := N) j b
  set A := VcoupL X (eC 3)
  set B := VcoupL (L := L) (N := N) (d := d) univ (eC 3)
  have hA := even_VcoupL X (eC 3)
  have hB := even_VcoupL (L := L) (N := N) (d := d) univ (eC 3)
  have hA4 := degLe_VcoupL_eg X
  have hB4 := degLe_VcoupL_eg (L := L) (N := N) (d := d) univ
  have hc : (X.card : ℂ) ≠ 0 := by
    have := (isSmall_clo (isSmall_blockSet_of_mem hb)).2.1.1.card_pos
    exact_mod_cast this.ne'
  -- each past coefficient
  have hbk : ∀ k ∈ range j, D.beta j k b i₀ (eC 3) (eC 3) 3 =
      mu4 (base X) i₀ i₀ (LopC (D.C j) (FC (D.C k) A B)) / (2 * X.card) := by
    intro k hk
    rw [D.beta_past_eq hd hL (mem_range.1 hk) hjN (fun i _ => hC i) hb i₀]
    simp only [hs, one_pow, prod_const_one, one_mul, map_smul, mu4_smul]
    simp only [X, A, B] at hc ⊢
    field_simp
  rw [sum_congr rfl hbk, ← sum_div, ← mu4_lop_FC_sum _ _ _ _ _ _ hA hA4 hB4,
    mu4_lop_FC_eq _ _ _ _ _ hA hB hA4 hB4]
  have hq : D.betaQ j j b i₀ (eC 3) (eC 3) 3 = negBub (D.C j) X i₀ :=
    D.betaQ_eq_negBub hL (by omega) hb i₀
  rw [hq, negBub_eq_mu4_FC hL (by omega) hb, negBub_eq_mu4_FC hL (by omega) hb,
    negBub_eq_mu4_FC hL (by omega) hb, tadT]
  simp only [X] at hc ⊢
  field_simp
  ring

end FlowSeq

/-! ### The tadpoles in terms of the first-order shift -/

theorem degLe_zero_const (r : ℂ) : DegLe 0 (r • (1 : Alg d L N)) := by
  intro m z hm
  rw [coeff_smul]
  have : coeff (1 : Alg d L N) z = 0 := by
    have : (1 : Alg d L N) = ExteriorAlgebra.ιMulti ℂ 0 (Fin.elim0 : Fin 0 → V (Lam d L N)) := by
      simp [ExteriorAlgebra.ιMulti_zero_apply]
    rw [this]; exact coeff_ιMulti_of_ne _ _ (by omega)
  rw [this, mul_zero]

/-- `X_w(𝓛_C V_g(Y), F) = X_w(V_s(Y), F)` with `s = κ'(e_g) - e_g = (-c₀, -δ, 2dδ, 0)`. -/
theorem Xc_lop_VcoupL {C : Matrix (Lam d L N) (Lam d L N) ℂ} {c₀ δ : ℂ}
    (hc₀ : ∀ x, C x x = c₀) (hδ : ∀ x e, C (x + dirVec e) x = c₀ + δ)
    (hδ' : ∀ x e, C x (x + dirVec e) = c₀ + δ) (w : Matrix (Lam d L N) (Lam d L N) ℂ)
    (Y : Finset (Lam d L N)) (F : Alg d L N) :
    Xc w (LopC C (VcoupL Y (eC 3))) F = Xc w (VcoupL Y (shiftL d c₀ δ (eC 3) - eC 3)) F := by
  obtain ⟨r, hr⟩ := expLC_Vcoup hc₀ hδ hδ' (Coup.ofVec (eC 3)) Y
  have hR : DegLe 0 (expLC C (VcoupL Y (eC 3)) - VcoupL Y (eC 3) - LopC C (VcoupL Y (eC 3))) :=
    (degLe_VcoupL_eg Y).exp_sub2 C (n := 0)
  have hE : expLC C (VcoupL Y (eC 3)) = VcoupL Y (shiftL d c₀ δ (eC 3)) + r • 1 := hr
  have e : LopC C (VcoupL Y (eC 3)) = VcoupL Y (shiftL d c₀ δ (eC 3) - eC 3) +
      (r • 1 - (expLC C (VcoupL Y (eC 3)) - VcoupL Y (eC 3) - LopC C (VcoupL Y (eC 3)))) := by
    rw [map_sub, hE]; abel
  have h0 : DegLe 0 (r • (1 : Alg d L N) -
      (expLC C (VcoupL Y (eC 3)) - VcoupL Y (eC 3) - LopC C (VcoupL Y (eC 3)))) := by
    rw [sub_eq_add_neg]
    exact (degLe_zero_const r).add (by simpa using hR.smul (-1))
  rw [e, Xc_add_left, Xc_degLe_zero_left w h0, add_zero]

/-- **The tadpole term in shift form**: with `s = κ'(e_g) - e_g = (-c₀, -δ, 2dδ, 0)` for the
values `c₀ = C_j(x,x)`, `c₀ + δ = C_j(x ± e, x)`:
`T_j = (mu4 X_w(V_s(X), V_g(Λ)) + mu4 X_w(V_s(Λ), V_g(X))) / (2|X|)`. -/
theorem tadT_shift {C : Matrix (Lam d L N) (Lam d L N) ℂ} {c₀ δ : ℂ}
    (hc₀ : ∀ x, C x x = c₀) (hδ : ∀ x e, C (x + dirVec e) x = c₀ + δ)
    (hδ' : ∀ x e, C x (x + dirVec e) = c₀ + δ) (X : Finset (Lam d L N)) (i₀ : Fin d)
    (w : Matrix (Lam d L N) (Lam d L N) ℂ) :
    tadT X i₀ w C =
      (mu4 (base X) i₀ i₀ (Xc w (VcoupL X (shiftL d c₀ δ (eC 3) - eC 3)) (VcoupL univ (eC 3))) +
        mu4 (base X) i₀ i₀ (Xc w (VcoupL univ (shiftL d c₀ δ (eC 3) - eC 3)) (VcoupL X (eC 3)))) /
        (2 * X.card) := by
  rw [tadT, Xc_lop_VcoupL hc₀ hδ hδ', Xc_lop_VcoupL hc₀ hδ hδ']

end

end Step2
