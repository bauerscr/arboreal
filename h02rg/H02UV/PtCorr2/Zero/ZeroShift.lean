import PtCorr2.Zero.ChainHist

/-!
# Route (A): a constant shift of the covariance through the dressed steps

For the constant covariance `cstC s` (all entries `s`, i.e. `s|Λ|` times the zero-mode projector):

* `omegaC_add_cstC`: `⟨F⟩_{Γ + s𝟙} = ⟨F⟩_Γ − s·c2(𝔼_Γθ F)` (exact, even `F`);
* `kmat_zsym`: the zero-mode symbol `zsym x = x δ_{p,0}` is the constant matrix `x/|Λ|`;
* `split_kmat_gen`, `split_shift`: the absorption step with `Γ_j + x/|Λ|` splits as
  `Γ^int_{j+1} + (Γ_{j+1} + x'/|Λ|)` with `x' = shiftNext D j x`
  (`(γ + x)/(1 + a m²(γ + x)) − γ/(1 + a m²γ)`, `γ = Γ̂_j(0)`), i.e. the RG maps do not see
  the shift;
* `det_shift`: `det(1 + aA(Γ_j + x/|Λ|)) = det(1 + aAΓ_j)·(1 + a m²(γ + x))/(1 + a m²γ)`;
* `rawStep_omega_gen`, `lastStep_omega_gen`: the step identities for arbitrary splittings;
  at the last step the shift enters only the zero-mode integral: `1 + ũ + ã·x_N`.
-/

namespace PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Step2 Step Step2.LastN

variable {L N : ℕ} [NeZero L]

/-! ### Linearity in a constant shift -/

theorem expLC_even {Λ : Type*} [DecidableEq Λ] [Fintype Λ] (C : Matrix Λ Λ ℂ) {F : Grassmann.N Λ}
    (hF : inv' F = F) : inv' (expLC C F) = expLC C F := by
  rw [← expLC_inv', hF]

/-- **`⟨F⟩_{Γ + s𝟙} = ⟨F⟩_Γ − s c2(𝔼_Γθ F)`** for even `F`. -/
theorem omegaC_add_cstC {Λ : Type*} [DecidableEq Λ] [Fintype Λ] [Nonempty Λ] (Γ : Matrix Λ Λ ℂ)
    (s : ℂ) {F : Grassmann.N Λ} (hF : inv' F = F) :
    omegaC (Γ + cstC Λ s) F = omegaC Γ F - s * Suscept.c2 (expLC Γ F) := by
  rw [omegaC, add_comm, expLC_add, ← ECC_theta (cstC Λ s)]
  have h := congrArg ε (Rc_ECC_cstC_even (Λ := Λ) s (expLC_even Γ hF))
  rw [Suscept.ε_Rc, map_add, AlgHom.commutes, map_smul, ε_PP, smul_zero, add_zero,
    Algebra.algebraMap_self, RingHom.id_apply] at h
  rw [h, omegaC]

/-! ### The zero-mode symbol -/

/-- The zero-mode symbol `x δ_{p,0}`. -/
def zsym (x : ℂ) : DressedFRD.Sym 2 (L ^ N) := fun m => if m = 0 then x else 0

theorem kmat_zsym (x : ℂ) :
    DressedFRD.kmat (zsym (L := L) (N := N) x) =
      cstC (Lam 2 L N) (x / Fintype.card (Lam 2 L N)) := by
  ext a b
  have : zsym (L := L) (N := N) x = DressedFRD.zmP (fun _ => x) := by
    funext m; simp [zsym, DressedFRD.zmP]
  rw [this, DressedFRD.kmat_zmP, cstC, FRD.card_torus]
  push_cast; rfl

/-- `det(1 + c𝟙) = 1 + |Λ| c`. -/
theorem det_one_add_cstC (c : ℂ) :
    (1 + cstC (Lam 2 L N) c).det = 1 + (Fintype.card (Lam 2 L N) : ℂ) * c := by
  have e : cstC (Lam 2 L N) c =
      Matrix.replicateCol Unit (fun _ => c) * Matrix.replicateRow Unit (fun _ => (1 : ℂ)) := by
    ext a b; simp [cstC, Matrix.mul_apply]
  rw [e, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp [dotProduct, mul_comm]

/-! ### Splitting of multipliers -/

open DressedFRD in
/-- **A splitting of multipliers** `Γ(1 + aAΓ)^{-1} = Γ₁ + Γ₂` from the symbols. -/
theorem split_kmat_gen (G G1 G2 : Sym 2 (L ^ N)) (a : ℂ) (msq : ℝ)
    (hden : ∀ m, 1 + a * Asym msq m * G m ≠ 0)
    (hsplit : ∀ m, G m / (1 + a * Asym msq m * G m) = G1 m + G2 m) :
    IsUnit (1 + a • (Aop (d := 2) (L := L) (N := N) msq * kmat G)).det ∧
    kmat G * (1 + a • (Aop (d := 2) (L := L) (N := N) msq * kmat G))⁻¹ = kmat G1 + kmat G2 := by
  set w : Sym 2 (L ^ N) := 1 + a • (Asym msq * G) with hw
  have hw0 : ∀ m, w m ≠ 0 := fun m => by
    simp only [hw, Pi.add_apply, Pi.one_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    have := hden m
    convert this using 2; ring
  have hM : 1 + a • (Aop (d := 2) (L := L) (N := N) msq * kmat G) = kmat w := by
    rw [hw, kmat_add, kmat_one, kmat_smul, kmat_mul, Aop_eq_kmat]
  have hinv : kmat w⁻¹ * kmat w = 1 := by
    rw [← kmat_mul, ← kmat_one]; congr 1; funext m; simp [hw0 m]
  refine ⟨?_, ?_⟩
  · rw [hM]; exact Matrix.isUnit_det_of_left_inverse hinv
  · rw [hM, kmat_inv hw0, ← kmat_mul, ← kmat_add]
    congr 1; funext m
    rw [Pi.add_apply, ← hsplit m]
    simp only [Pi.mul_apply, Pi.inv_apply, hw, Pi.add_apply, Pi.one_apply, Pi.smul_apply,
      smul_eq_mul, div_eq_mul_inv]
    ring_nf

open DressedFRD in
/-- `det(1 + aA kmat(G + x δ_0)) = det(1 + aA kmat G) · (1 + a m²(G(0) + x))/(1 + a m² G(0))`. -/
theorem det_shift (G : Sym 2 (L ^ N)) (a x : ℂ) (msq : ℝ)
    (hden : ∀ m, 1 + a * Asym msq m * G m ≠ 0) :
    (1 + a • (Aop (d := 2) (L := L) (N := N) msq * kmat (G + zsym x))).det =
      (1 + a • (Aop (d := 2) (L := L) (N := N) msq * kmat G)).det *
        ((1 + a * Asym (d := 2) (n := L ^ N) msq 0 * (G 0 + x)) / (1 + a * Asym (d := 2) (n := L ^ N) msq 0 * G 0)) := by
  set w : Sym 2 (L ^ N) := 1 + a • (Asym msq * G) with hw
  set r : ℂ := (1 + a * Asym (d := 2) (n := L ^ N) msq 0 * (G 0 + x)) / (1 + a * Asym (d := 2) (n := L ^ N) msq 0 * G 0) with hr
  have h0 := hden 0
  have h0' : 1 + a * (Asym (d := 2) (n := L ^ N) msq 0 * G 0) ≠ 0 := by rw [← mul_assoc]; exact h0
  have hM : ∀ G' : Sym 2 (L ^ N), 1 + a • (Aop (d := 2) (L := L) (N := N) msq * kmat G') =
      kmat (1 + a • (Asym msq * G')) := fun G' => by
    rw [kmat_add, kmat_one, kmat_smul, kmat_mul, Aop_eq_kmat]
  have hw' : (1 + a • (Asym msq * (G + zsym x)) : Sym 2 (L ^ N)) = w * (1 + zsym (r - 1)) := by
    funext m
    simp only [hw, Pi.add_apply, Pi.one_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, zsym]
    split_ifs with hm
    · subst hm
      rw [hr]
      field_simp
      ring
    · ring
  rw [hM, hM, hw', kmat_mul, Matrix.det_mul, kmat_add 1 (zsym (r - 1)), kmat_one, kmat_zsym,
    det_one_add_cstC]
  have hc : (Fintype.card (Lam 2 L N) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  congr 1
  field_simp
  ring

/-- The next zero-mode shift `x' = (γ + x)/(1 + a m²(γ + x)) − γ/(1 + a m²γ)`. -/
def shiftNext (D : DressedFRD.Data 2 (L ^ N)) (j : ℕ) (x : ℂ) : ℂ :=
  (D.Gam j 0 + x) / (1 + D.ζ j * D.Z j * DressedFRD.Asym (d := 2) (n := L ^ N) D.msq 0 * (D.Gam j 0 + x)) -
    D.Gam j 0 / (1 + D.ζ j * D.Z j * DressedFRD.Asym (d := 2) (n := L ^ N) D.msq 0 * D.Gam j 0)

open DressedFRD in
/-- **The shifted splitting**: the shift goes from `Γ_j` to `Γ_{j+1}`; `Γ^int_{j+1}` is unchanged. -/
theorem split_shift (D : Data 2 (L ^ N)) (j : ℕ) (x : ℂ)
    (hden : ∀ m, 1 + D.ζ j * D.Z j * Asym D.msq m * D.Gam j m ≠ 0)
    (hsplit : ∀ m, D.absorbed j m = D.Gint j m + D.Gam (j + 1) m)
    (hx : 1 + D.ζ j * D.Z j * Asym (d := 2) (n := L ^ N) D.msq 0 * (D.Gam j 0 + x) ≠ 0) :
    IsUnit (1 + (D.ζ j * D.Z j) • (Aop (d := 2) (L := L) (N := N) D.msq *
      kmat (D.Gam j + zsym x))).det ∧
    kmat (D.Gam j + zsym x) * (1 + (D.ζ j * D.Z j) • (Aop (d := 2) (L := L) (N := N) D.msq *
      kmat (D.Gam j + zsym x)))⁻¹ =
      kmat (D.Gint j) + kmat (D.Gam (j + 1) + zsym (shiftNext D j x)) := by
  refine split_kmat_gen _ _ _ _ _ (fun m => ?_) (fun m => ?_)
  · by_cases hm : m = 0
    · subst hm
      have e : (D.Gam j + zsym (L := L) (N := N) x) 0 = D.Gam j 0 + x := by simp [zsym]
      rw [e]; exact hx
    · have e : (D.Gam j + zsym (L := L) (N := N) x) m = D.Gam j m := by simp [zsym, hm]
      rw [e]; exact hden m
  · by_cases hm : m = 0
    · subst hm
      have h0 := hsplit 0
      simp only [DressedFRD.Data.absorbed] at h0
      have e1 : (D.Gam j + zsym (L := L) (N := N) x) 0 = D.Gam j 0 + x := by simp [zsym]
      have e2 : (D.Gam (j + 1) + zsym (L := L) (N := N) (shiftNext D j x)) 0 =
          D.Gam (j + 1) 0 + shiftNext D j x := by simp [zsym]
      rw [e1, e2, shiftNext, h0]
      ring
    · have h1 := hsplit m
      simp only [DressedFRD.Data.absorbed] at h1
      have e1 : (D.Gam j + zsym (L := L) (N := N) x) m = D.Gam j m := by simp [zsym, hm]
      have e2 : (D.Gam (j + 1) + zsym (L := L) (N := N) (shiftNext D j x)) m = D.Gam (j + 1) m := by simp [zsym, hm]
      rw [e1, e2]
      exact h1

/-! ### The step identities for arbitrary splittings -/

variable {R : RGPar 2 L N} {j : ℕ} {st : RawSt 2 L N} {g μ : ℝ} {D : Fam 2 L N} {K : Act 2 L N}

/-- **One raw step on Gaussian integrals, for any splitting** `Γ(1 + aAΓ)^{-1} = Γ^int + Γ₂`. -/
theorem rawStep_omega_gen (hV : ValidCore R j) (H : RawInv R j st)
    (hD : D ∈ BSub (L := L) (N := N) j) (hK : K ∈ ASub (L := L) (N := N) j)
    (Γ Γ₂ : Matrix (Lam 2 L N) (Lam 2 L N) ℂ)
    (hT : IsUnit (1 + stA R st • (Aop (d := 2) (L := L) (N := N) R.msq * Γ)).det)
    (hΓ : Γ * (1 + stA R st • (Aop (d := 2) (L := L) (N := N) R.msq * Γ))⁻¹ = stCov R j st + Γ₂) :
    omegaC Γ (Zin R j st g μ D K : Alg 2 L N) =
      (1 + stA R st • (Aop (d := 2) (L := L) (N := N) R.msq * Γ)).det *
        Complex.exp (-uOut R j st g μ D K) * omegaC Γ₂ (Zout R j st g μ D K : Alg 2 L N) := by
  have e : stA R st - stYc R st + stYc R st = stA R st := sub_add_cancel _ _
  obtain ⟨hC, -, -, -⟩ := RawInv.covL hV H
  obtain ⟨hj2, hd, hL, hρ, -, -, -⟩ := hV
  have hjN : j < N := by omega
  have hL' : 2 ^ (2 + 2) ≤ L := by norm_num at hL ⊢; omega
  have hΔm := VfamL_mem (L := L) (N := N) hd hL hjN
    ![stA R st - stYc R st, stYc R st, stA R st * R.msq, 0]
  have hVm := VfamL_mem (L := L) (N := N) hd hL hjN ![st.z + stYc R st - stA R st,
    st.y - stYc R st, stNu R j st μ - stA R st * R.msq, stGr R j st g μ * stZ' R st ^ 2]
  have hKf := Kflat_mem hjN hΔm (eps_VfamL j _) hK
  have h := omegaC_full_step_raw j R.msq (stA R st - stYc R st) (stYc R st) (stVf R j st g μ)
    (stDelta R j st) (st.Wl + D) K (eps_VfamL j _) (fun b => coe_stDelta b)
    Γ (stCov R j st) Γ₂ (by rw [e]; exact hT) (by rw [e]; exact hΓ)
    hd hL' (by omega) hC hVm.1 (add_mem H.hWl hD).1 hKf.1
  rw [e] at h
  rw [Zin, h, show (fun Y => bpow j (fun b => gexp (stDelta R j st b)) Y * K Y) =
    Kflat j (stDelta R j st) K from rfl, sum_Ip_eq_gZ, omegaC_smul', uOut, Zout, mul_assoc]

/-- `⟨Z̃⟩_{s𝟙} = 1 + ũ(t_raw + s|Λ|) = 1 + ũ + ã s|Λ|`. -/
theorem omegaC_cstC_ZtFin {out : LastOut 2 L N} {j : ℕ} (tr s : ℂ)
    (hV : ∀ b ∈ blockIdx (L := L) (N := N) j,
      (out.V b : Alg 2 L N) = Vcoup out.κ (blockSet j b)) :
    omegaC (cstC (Lam 2 L N) s) (ZtFin j out tr : Alg 2 L N) =
      1 + uFin j out tr + aFin j out * (s * Fintype.card (Lam 2 L N)) := by
  have hc : (Fintype.card (Lam 2 L N) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have e1 : ∀ tr' : ℂ, (ZtFin j out tr' : Alg 2 L N) =
      expLC (cstC (Lam 2 L N) (tr' / Fintype.card (Lam 2 L N))) (finObj j out : Alg 2 L N) :=
    fun tr' => by rw [ZtFin, coe_ECCE, coe_thetaE, ECC_theta]
  have e2 : cstC (Lam 2 L N) s + cstC (Lam 2 L N) (tr / Fintype.card (Lam 2 L N)) =
      cstC (Lam 2 L N) ((tr + s * Fintype.card (Lam 2 L N)) / Fintype.card (Lam 2 L N)) := by
    ext a b; simp only [cstC, Matrix.add_apply]; field_simp; ring
  have hz := congrArg ε (prop_ZNN2 (tr + s * Fintype.card (Lam 2 L N)) hV)
  rw [Suscept.ε_Rc] at hz
  rw [omegaC, e1, ← expLC_add, e2, ← e1, hz, map_sub, AlgHom.commutes, map_smul, ε_PP, smul_zero,
    sub_zero, Algebra.algebraMap_self, RingHom.id_apply, uFin, uFin]
  ring

end

end PtCorr2
