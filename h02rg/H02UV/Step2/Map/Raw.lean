import Step2.FlowCont.MsqCont
import Step2.Lip.CdrHol

/-!
# The step in raw (unrescaled) fields (`h02uv-outline.tex`, Section `sec:reduction`, (O5))

Route (O5): no field rescaling. At step `j` the fluctuation covariance is the *raw*
`Γ^int_{j+1} = C'_{j+1}/Z_{j+1}`.

* `kmat_mul`, `kmat_one`, `kmat_inv`, `Aop_eq_kmat`: Fourier multipliers multiply as symbols;
* `split_kmat`: the DressedFRD split `Γ_j(1 + z_j A Γ_j)^{-1} = Γ^int_{j+1} + Γ_{j+1}` as an identity
  of matrices (the hypothesis `hΓ` of `omegaC_full_step` with `r = s = 1`);
* `GoodCov2.smul`: `c • C` satisfies `GoodCov2` at `|c|^{1/2} ℓ`;
* `rawCov_good`: `Γ^int_{j+1}` satisfies `GoodCov2` at `ℓ_C |Z_{j+1}|^{-1/2}`;
* `omegaC_full_step_raw`: the full step without rescaling.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

section Kmat

variable {d n : ℕ} [NeZero n]

open DressedFRD

theorem kmat_mul (w w' : Sym d n) : kmat (w * w') = kmat w * kmat w' := by
  ext x y
  simp only [kmat, Matrix.mul_apply, kern_mul]
  rw [← Equiv.sum_comp (Equiv.subLeft x)]
  refine sum_congr rfl fun z _ => ?_
  simp [sub_sub_sub_cancel_left]

theorem kmat_one : kmat (1 : Sym d n) = 1 := by
  ext x y
  simp only [kmat, kern, Pi.one_apply, one_mul, Matrix.one_apply]
  rw [sum_char_left]
  by_cases h : x = y
  · subst h; simp
  · have h' : x - y ≠ 0 := sub_ne_zero.2 h
    simp [h, h']

theorem kmat_add (w w' : Sym d n) : kmat (w + w') = kmat w + kmat w' := by
  ext x y; simp [kmat, kern_add]

theorem kmat_smul (c : ℂ) (w : Sym d n) : kmat (c • w) = c • kmat w := by
  ext x y; simp [kmat, kern_smul]

/-- A symbol without zeros gives an invertible multiplier. -/
theorem kmat_inv {w : Sym d n} (hw : ∀ m, w m ≠ 0) : (kmat w)⁻¹ = kmat w⁻¹ := by
  have h : kmat w⁻¹ * kmat w = 1 := by
    rw [← kmat_mul, ← kmat_one]
    congr 1; funext m; simp [hw m]
  exact Matrix.inv_eq_left_inv h

end Kmat

section Aop

variable {d L N : ℕ} [NeZero L]

theorem negLap_transl (x y : Lam d L N) :
    (negLap x y : ℝ) = negLap (x - y) 0 := by
  unfold negLap
  simp only [sub_eq_zero]
  congr 1
  refine sum_congr rfl fun e _ => ?_
  congr 1
  apply propext
  constructor
  · intro h; rw [h]; abel
  · intro h
    have h' : x + dirVec e - y = 0 := by rw [h]; abel
    exact (eq_of_sub_eq_zero h').symm

theorem Aop_eq_kmat (msq : ℝ) :
    Aop (d := d) (L := L) (N := N) msq = DressedFRD.kmat (DressedFRD.Asym msq) := by
  ext x y
  have h1 := DressedFRD.kern_lam (d := d) (n := L ^ N) (x - y)
  have hA : DressedFRD.Asym (d := d) (n := L ^ N) msq =
      (fun m => (lam m : ℂ)) + (msq : ℂ) • (1 : DressedFRD.Sym d (L ^ N)) := by
    funext m; simp [DressedFRD.Asym]
  have h2 : DressedFRD.kmat (1 : DressedFRD.Sym d (L ^ N)) x y = if x = y then 1 else 0 := by
    rw [kmat_one, Matrix.one_apply]
  simp only [Aop, DressedFRD.kmat] at h2 ⊢
  rw [hA, DressedFRD.kern_add, DressedFRD.kern_smul, h1, ← negLap_transl, h2]

end Aop

section Split

variable {d L N : ℕ} [NeZero L]

open DressedFRD

/-- **The DressedFRD split as a matrix identity**: `Γ_j(1 + z_j A Γ_j)^{-1} = Γ^int_{j+1} + Γ_{j+1}`. -/
theorem split_kmat (D : Data d (L ^ N)) (j : ℕ)
    (hden : ∀ m, 1 + D.ζ j * D.Z j * Asym D.msq m * D.Gam j m ≠ 0)
    (hsplit : ∀ m, D.absorbed j m = D.Gint j m + D.Gam (j + 1) m) :
    IsUnit (1 + (D.ζ j * D.Z j) • (Aop (d := d) (L := L) (N := N) D.msq * kmat (D.Gam j))).det ∧
    kmat (D.Gam j) * (1 + (D.ζ j * D.Z j) • (Aop (d := d) (L := L) (N := N) D.msq *
      kmat (D.Gam j)))⁻¹ = kmat (D.Gint j) + kmat (D.Gam (j + 1)) := by
  set w : Sym d (L ^ N) := 1 + (D.ζ j * D.Z j) • (Asym D.msq * D.Gam j) with hw
  have hw0 : ∀ m, w m ≠ 0 := fun m => by
    simp only [hw, Pi.add_apply, Pi.one_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    have := hden m
    convert this using 2; ring
  have hM : 1 + (D.ζ j * D.Z j) • (Aop (d := d) (L := L) (N := N) D.msq * kmat (D.Gam j)) =
      kmat w := by
    rw [hw, kmat_add, kmat_one, kmat_smul, kmat_mul, Aop_eq_kmat]
  have hinv : kmat w⁻¹ * kmat w = 1 := by
    rw [← kmat_mul, ← kmat_one]; congr 1; funext m; simp [hw0 m]
  refine ⟨?_, ?_⟩
  · rw [hM]; exact Matrix.isUnit_det_of_left_inverse hinv
  · rw [hM, kmat_inv hw0, ← kmat_mul, ← kmat_add]
    congr 1; funext m
    rw [Pi.add_apply, ← hsplit m, Data.absorbed]
    simp only [Pi.mul_apply, Pi.inv_apply, hw, Pi.add_apply, Pi.one_apply, Pi.smul_apply,
      Pi.mul_apply, smul_eq_mul, div_eq_mul_inv]
    ring_nf

end Split

section Scale

variable {d L N : ℕ} [NeZero L]

/-- **`GoodCov2` under scaling**: `c • C` satisfies `GoodCov2` at `|c|^{1/2} ℓ`. -/
theorem GoodCov2.smul {j : ℕ} {ℓ : ℝ} {C : Matrix (Lam d L N) (Lam d L N) ℂ}
    (hC : GoodCov2 j ℓ C) (c : ℂ) : GoodCov2 j (Real.sqrt ‖c‖ * ℓ) (c • C) := by
  obtain ⟨H, i1, i2, Fv, Gv, hG, hB⟩ := hC.gram
  set a : ℂ := c ^ (2⁻¹ : ℂ) with ha
  have ha2 : a * a = c := by
    have := Complex.cpow_ofNat_inv_pow c 2
    rw [← this, sq]
  have hna : ‖a‖ = Real.sqrt ‖c‖ := by
    rw [← ha2, norm_mul, Real.sqrt_mul_self (norm_nonneg _)]
  refine ⟨⟨H, i1, i2, fun x => (starRingEnd ℂ a) • Fv x, fun y => a • Gv y, ?_, ?_⟩, ?_⟩
  · intro x y
    rw [Matrix.smul_apply, hG x y, inner_smul_left, inner_smul_right, Complex.conj_conj,
      smul_eq_mul, ← mul_assoc, ha2]
  · intro α hα x
    obtain ⟨h1, h2⟩ := hB α hα x
    have e1 : gvec (fun x => (starRingEnd ℂ a) • Fv x) (dprof α x) =
        (starRingEnd ℂ a) • gvec Fv (dprof α x) := by
      simp [gvec, smul_sum, smul_comm (starRingEnd ℂ a)]
    have e2 : gvec (fun y => a • Gv y) (dprof α x) = a • gvec Gv (dprof α x) := by
      simp [gvec, smul_sum, smul_comm a]
    rw [e1, e2, norm_smul, norm_smul, Complex.norm_conj, hna, mul_assoc]
    exact ⟨mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _),
      mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)⟩
  · intro hjN x y hxy
    rw [Matrix.smul_apply, hC.range hjN x y hxy, smul_zero]

end Scale

section RawStep

variable {d L N : ℕ} [NeZero L] (j : ℕ)

theorem sigE_one' {Λ : Type*} [DecidableEq Λ] [Fintype Λ] (F : EvR Λ) : sigE 1 F = F :=
  Subtype.ext (by rw [coe_sigE, sig_one])

/-- **The full step in raw fields** (route (O5), `r = s = 1`): no rescaling; the `Step2` map is
applied with the raw covariance `Γ₁` to `(V♭, 𝒲, K♭)`. -/
theorem omegaC_full_step_raw (msq : ℝ) (z y : ℂ) (Vf Δ W : Fam d L N)
    (K : Act d L N) (hVf : ∀ b, ε (Vf b : Alg d L N) = 0)
    (hΔ : ∀ b, (Δ b : Alg d L N) = Vcoup ⟨z, y, (z + y) * msq, 0⟩ (blockSet (L := L) (N := N) j b))
    (Γ Γ₁ Γ₂ : Matrix (Lam d L N) (Lam d L N) ℂ)
    (hT : IsUnit (1 + (z + y) • (Aop msq * Γ)).det)
    (hΓ : Γ * (1 + (z + y) • (Aop msq * Γ))⁻¹ = Γ₁ + Γ₂) {ℓ : ℝ}
    (hd : 1 ≤ d) (hL : 2 ^ (d + 2) ≤ L) (hjN : j + 1 < N) (hC : GoodCov2 j ℓ Γ₁)
    (hV : InF j Vf) (hW : InF j W)
    (hK : InK2 j fun Y => bpow j (fun b => gexp (Δ b)) Y * K Y) :
    omegaC Γ (gZ j (Ib (fun b => Vf b + Δ b) W) K : Alg d L N) =
      (1 + (z + y) • (Aop msq * Γ)).det * omegaC Γ₂
        ((∑ U ∈ Pj (j + 1) univ,
          bpow j (Ip j Γ₁ Vf W (fun Y => bpow j (fun b => gexp (Δ b)) Y * K Y)) (univ \ U) *
          (Complex.exp (-uX j Γ₁ Vf W (fun Y => bpow j (fun b => gexp (Δ b)) Y * K Y) U) •
            Kext (j + 1) (Kplus j Γ₁ Vf W (fun Y => bpow j (fun b => gexp (Δ b)) Y * K Y)) U) :
            EvR (Lam d L N)) : Alg d L N) := by
  have h1 : ((1 : ℂ) ^ 2 • Γ₁) = Γ₁ := by simp
  have h2 : ((1 : ℂ) ^ 2 • Γ₂) = Γ₂ := by simp
  have hVs : (fun b => sigE 1 (Vf b)) = Vf := funext fun b => sigE_one' _
  have hWs : (fun b => sigE 1 (W b)) = W := funext fun b => sigE_one' _
  have hKs : (fun Y => sigE 1 (bpow j (fun b => gexp (Δ b)) Y * K Y)) =
      fun Y => bpow j (fun b => gexp (Δ b)) Y * K Y := funext fun Y => sigE_one' _
  have := omegaC_full_step j msq z y 1 1 (by norm_num) Vf Δ W K hVf hΔ Γ Γ₁ Γ₂ hT hΓ hd hL hjN
    (by rw [h1]; exact hC) (by rw [hVs]; exact hV) (by rw [hWs]; exact hW) (by rw [hKs]; exact hK)
  simp only [h1, h2, hVs, hWs, hKs] at this
  exact this

end RawStep

section RawCov

variable {d L N : ℕ} [NeZero L]

/-- **The raw covariance `Γ^int_{j+1}` satisfies `GoodCov2`** with field scale
`|Z_{j+1}|^{-1/2} ℓ_C`, where `ℓ_C` is that of `prop:C5`; `|z_i| ≤ ζ̄`. -/
theorem raw_family (P : PtFamily) (hd : 2 ≤ d) (hL7 : 7 ≤ L) :
    ∃ cS : ℝ, 0 ≤ cS ∧ ∃ ζbar : ℝ, 0 < ζbar ∧ ζbar ≤ 1 / 8 ∧ ∃ K : ℝ, 0 ≤ K ∧
    ∀ (N : ℕ) (msq : ℝ), 1 ≤ N → 0 < msq → msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) →
    ∀ j, j + 1 < N →
      let D₀ : DressedFRD.Data d (L ^ N) := ⟨L, N, msq, DressedFRD.frdC P msq L N, 0⟩
      ∀ z : Fin (j + 1) → ℂ, (∀ i, ‖z i‖ ≤ ζbar) →
        GoodCov2 (d := d) (L := L) (N := N) j
          (Real.sqrt ‖((D₀.Dz z).Z (j + 1))⁻¹‖ * ellDr d L cS K ζbar j)
          (DressedFRD.kmat ((D₀.Dz z).Gint j)) := by
  obtain ⟨cS, hcS, ζbar, hζ, hζ8, K, hK0, h⟩ := dressed_family P hd hL7
  refine ⟨cS, hcS, ζbar, hζ, hζ8, K, hK0, ?_⟩
  intro N msq hN hmsq hmsq' j hj D₀ z hz
  have hg := ((h N msq hN hmsq hmsq' j hj).2 z hz).1
  have hZ : (D₀.Dz z).Z (j + 1) ≠ 0 := by
    refine prod_ne_zero_iff.2 fun i _ h0 => ?_
    have h1 : ‖(D₀.Dz z).ζ i‖ ≤ ζbar := by
      show ‖DressedFRD.Data.ext z i‖ ≤ ζbar
      unfold DressedFRD.Data.ext; split_ifs
      · exact hz _
      · simp [hζ.le]
    have h2 : (D₀.Dz z).ζ i = -1 := by linear_combination h0
    rw [h2] at h1; norm_num at h1; linarith
  have e : DressedFRD.kmat ((D₀.Dz z).Gint j) =
      ((D₀.Dz z).Z (j + 1))⁻¹ • Cdr (D₀.Dz z) j := by
    rw [Cdr, kmat_smul, smul_smul, inv_mul_cancel₀ hZ, one_smul]
  rw [e]
  exact hg.smul _

end RawCov

end

end Step2
