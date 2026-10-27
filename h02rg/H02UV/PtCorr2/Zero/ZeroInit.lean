import PtCorr2.Zero.Suscept2
import Ward.Bridge
import H02.Ghost
import Suscept.PropSuscept

/-!
# The initial object of the dressed flow is the `ℍ^{0|2}` model; `⟨Z_0⟩_C ≠ 0`

Along a trajectory started at `(b, μ₀, 0)` the input of step `0` is the bare model:

* `Γh_zero_eq_Cov`: `Γ_0 = C = (-Δ + m²)^{-1}` as a matrix (`C_{>0} = ∑_{k=1}^N C_k` has symbol
  `(λ + m²)^{-1}`, `StdHyp.sum_eq`);
* `vcoup_zy_eq_eval`: for `z = y = 0` the coupling polynomial of `Step2` is the one of `Loc`,
  `V_{(0,0,ν,g)}(Y) = ∑_{x ∈ Y} [ν ψ_xψ̄_x + g ψ_xψ̄_x(∇ψ∇ψ̄)_x]` (`Loc.Vcoup.eval`); the
  symmetric quartic `∑_i M̂^{ii}_x = ½ ∑_{e} (∇_eψ)(∇_eψ̄)ψψ̄` is the `Loc` quartic `ψψ̄ (∇ψ∇ψ̄)`;
* `Zh_zero_eq_Z0`: `Z_0 = e^{-V_0(Λ)}` with `V_0 = (z, y, a, b) = (0, 0, μ₀, b)`
  (`Suscept.Z0`), the clamps being inactive at `Z_0 = 1`, `ζ = 0`;
* `Vh_eq_V0`: `V_0 = Ward.Vh β h m² 0` with `β = 1/b`, `h = (μ₀ + m²)/b - 1` (the bridge
  couplings with `s₀ = 0`): the dressed flow starts from the `ℍ^{0|2}` model at `(β, h)`;
* **`omega_Zh_zero_ne`**: `⟨Z_0⟩_C ≠ 0` if `b > 0` and `b ≤ μ₀ + m²` (i.e. `h ≥ 0`), by
  `Ward.bridge_Z` and the positivity `H02.expect_one_pos` (forest representation with a ghost
  vertex). The condition `h ≥ 0` is a real sign condition on the initial mass coupling.
* **`one_add_uFin_ne_zero`**: hence `1 + ũ_{N,N} ≠ 0` along every trajectory as in
  `hist_omega_traj`, under `b ≤ μ₀ + m²`.
-/

namespace PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Step2 Step

/-! ### The coupling polynomial with `z = y = 0` -/

section Poly

variable {d L N : ℕ} [NeZero L]

theorem gmono4_diag_eq (e : Dir d) (x : Lam d L N) :
    gmono4 e e x = grad e x * gradbar e x * (psi x * psibar x) := by
  rw [gmono4_eq, mul_assoc]; rfl

/-- `ψ_xψ̄_x (∇ψ∇ψ̄)_x = ∑_i M̂^{ii}_x`. -/
theorem pp_gradSq_eq (x : Lam d L N) :
    psi x * psibar x * gradSq x = ∑ i, mono4s i i x := by
  rw [Grassmann.mul_comm_of_even (Ward.inv'_pp x), gradSq, smul_mul_assoc, sum_mul,
    Fintype.sum_sum_type]
  simp only [mono4s, if_true, gmono4_diag_eq, ← smul_sum, ← sum_add_distrib]

/-- **The coupling polynomial for `z = y = 0`** agrees with `Loc.Vcoup.eval`. -/
theorem vcoup_zy_eq_eval (ν g : ℂ) (Y : Finset (Lam d L N)) :
    Step2.Vcoup (⟨0, 0, ν, g⟩ : Coup) Y = (⟨0, 0, ν, g⟩ : Loc.Vcoup).eval Y := by
  have hC : ∑ M, coupC (⟨0, 0, ν, g⟩ : Coup) M • monoSet M Y = ν • monoSet (Mono.c : Mono d) Y := by
    rw [sum_eq_single (Mono.c : Mono d)]
    · rfl
    · intro M _ hM
      cases M with
      | c => exact absurd rfl hM
      | a1 _ => simp [coupC]
      | b1 _ => simp [coupC]
      | a2 s => simp [coupC]
      | b2 s => simp [coupC]
      | m2 i k => simp [coupC]
    · simp
  have hE : ∑ i, ∑ k, coupE (⟨0, 0, ν, g⟩ : Coup) i k • mono4sSet (L := L) (N := N) i k Y =
      g • ∑ i, mono4sSet (L := L) (N := N) i i Y := by
    rw [smul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_eq_single i]
    · simp [coupE]
    · intro k _ hk; simp [coupE, Ne.symm hk]
    · simp
  rw [Step2.Vcoup, unif, zero_smul, zero_add, hC, hE, Loc.Vcoup.eval, monoSet]
  simp only [mono4sSet]
  rw [sum_comm, smul_sum, smul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun x _ => ?_
  rw [Step2.monoAt_c, ← pp_gradSq_eq]
  simp

end Poly

variable {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-! ### `Γ_0 = C` -/

/-- **`Γ_0 = (-Δ + m²)^{-1}`** as a matrix. -/
theorem Γh_zero_eq_Cov (hL7 : 7 ≤ L) (hm0 : 0 < R.msq) (hN : 1 ≤ N) (t : Hist.Seq (Xs R)) :
    Γh R 0 t = cplx (Suscept.Cov 2 L N R.msq) := by
  obtain ⟨cS, -, hS⟩ := DressedFRD.frd_stdFull R.P (d := 2) le_rfl hL7 (q := 2) (M := 2 + 2 + 1)
    le_rfl
  have hstd := (hS (L ^ N) N R.msq hN rfl hm0).base
  have hpos : ∀ m : Torus 2 (L ^ N), (0 : ℝ) < lam m + R.msq := fun m => by
    have := FRD.lam_nonneg m; linarith
  have hA : ∀ m, DressedFRD.Asym (d := 2) (n := L ^ N) R.msq m ≠ 0 := fun m => by
    simp only [DressedFRD.Asym]; exact_mod_cast (hpos m).ne'
  have hG : (Dh R 0 t).Gam 0 = (DressedFRD.Asym (d := 2) (n := L ^ N) R.msq)⁻¹ := by
    rw [Gam0_eq]; funext m
    simp only [DressedFRD.ofR, Pi.inv_apply, DressedFRD.Asym]
    have hI : Ioc 0 N = Icc 1 N := by ext k; simp only [mem_Ioc, mem_Icc]; omega
    rw [hI, hstd.sum_eq m, Complex.ofReal_inv]
  have h1 : Γh R 0 t = (Aop (d := 2) (L := L) (N := N) R.msq)⁻¹ := by
    show DressedFRD.kmat ((Dh R 0 t).Gam 0) = _
    rw [hG, Aop_eq_kmat, kmat_inv hA]
  have hAop : Aop (d := 2) (L := L) (N := N) R.msq =
      cplx (FRD.negLap + R.msq • 1 : Matrix (Lam 2 L N) (Lam 2 L N) ℝ) := by
    ext x y
    simp only [Aop, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, Complex.ofReal_add, Complex.ofReal_mul]
    split_ifs <;> simp
  have hU : IsUnit (FRD.negLap + R.msq • 1 : Matrix (Lam 2 L N) (Lam 2 L N) ℝ).det :=
    FRD.isUnit_det_negLap_add hm0
  rw [h1]
  refine Matrix.inv_eq_right_inv ?_
  have key : ((FRD.negLap + R.msq • 1 : Matrix (Lam 2 L N) (Lam 2 L N) ℝ) *
      (FRD.negLap + R.msq • 1 : Matrix (Lam 2 L N) (Lam 2 L N) ℝ)⁻¹).map Complex.ofRealHom = 1 := by
    rw [Matrix.mul_nonsing_inv _ hU]; exact Matrix.map_one _ (map_zero _) (map_one _)
  rw [Matrix.map_mul] at key
  rw [hAop, Suscept.Cov]
  exact key

/-! ### `Z_0 = e^{-V_0(Λ)}` -/

theorem rawD_zeroX (u : ℂ) {j : ℕ} : rawD R u (0 : Xs R j) = 0 := by
  funext b
  simp only [rawD, Prod.fst_zero, map_zero, Pi.zero_apply]
  exact map_zero (sigE u)

theorem rawK_zeroX (u : ℂ) {j : ℕ} : rawK R u (0 : Xs R j) = 0 := by
  funext X
  simp only [rawK, Prod.snd_zero, map_zero, Pi.zero_apply]
  exact map_zero (sigE u)

/-- `gZ` with the zero activity is the block product over `Λ`. -/
theorem gZ_zeroK (j : ℕ) (I : (Fin 2 → ℕ) → EvR (Lam 2 L N)) :
    gZ j I (0 : Act 2 L N) = bpow j I univ := by
  rw [gZ, sum_eq_single (∅ : Finset (Lam 2 L N))]
  · rw [Kext_empty, mul_one, sdiff_empty]
  · intro X _ hX
    rw [Kext_zero j (Finset.nonempty_iff_ne_empty.2 hX), mul_zero]
  · intro h
    exact absurd (mem_Pj.2 ⟨empty_subset _, isPolymer_empty j⟩) h

/-- The initial raw state. -/
theorem rawHist_zero_eq (t : Hist.Seq (Xs R)) : rawHist R 0 t = ⟨0, 0, 0, 1, 0, 0, 1⟩ := rfl

/-- **The input of step `0` is `e^{-V_0(Λ)}`** with `V_0 = (0, 0, μ₀, b)`. -/
theorem Zh_zero_eq_Z0 (t : Hist.Seq (Xs R)) {b μ₀ : ℝ} (ht : t 0 = (b, μ₀, 0)) :
    (Zh R 0 t : Alg 2 L N) = Suscept.Z0 2 L N (⟨0, 0, (μ₀ : ℂ), (b : ℂ)⟩ : Loc.Vcoup) := by
  set st : RawSt 2 L N := ⟨0, 0, 0, 1, 0, 0, 1⟩
  have hz : stZeta R st = 0 := by simp [st, stZeta, absorbZeta, clampDisk]
  have hA : stA R st = 0 := by simp [stA, hz]
  have hY : stYc R st = 0 := by simp [st, stYc, clampDisk]
  have hZ' : stZ' R st = 1 := by simp [st, stZ', hz]
  have hD : stDelta R 0 st = 0 := by
    rw [stDelta, hA, hY]
    rw [show (![0 - 0, 0, 0 * R.msq, 0] : Fin 4 → ℂ) = 0 by
      ext i; fin_cases i <;> simp]
    exact map_zero _
  have hV : stVf R 0 st b μ₀ = VfamL 0 (⟨0, 0, (μ₀ : ℂ), (b : ℂ)⟩ : Coup).toVec := by
    rw [stVf, stGr, stNu, hA, hY, hZ']
    congr 1
    ext i; fin_cases i <;> simp [st, nCor, clampDisk, Coup.toVec]
  have h0 : (Zh R 0 t : EvR (Lam 2 L N)) =
      gexp (-VE (⟨0, 0, (μ₀ : ℂ), (b : ℂ)⟩ : Loc.Vcoup) (univ : Finset (Lam 2 L N))) := by
    rw [Zh, ht, rawHist_zero_eq]
    rw [rawD_zeroX, rawK_zeroX, Zin, gZ_zeroK, bpow, gexp_neg_VE _ (isPolymer_univ 0)]
    refine prod_congr rfl fun c _ => ?_
    rw [Ib, hD, hV]
    simp only [Pi.add_apply, add_zero, Pi.zero_apply, mul_one]
    congr 2
    exact Subtype.ext (by rw [coe_VfamL, vcoup_zy_eq_eval, coe_VE])
  rw [h0]; rfl

/-- The couplings of `V_0` are those of the bridge with `β = 1/b`, `h = (μ₀ + m²)/b - 1`,
`s₀ = 0`. -/
theorem Vh_eq_V0 {b μ₀ msq : ℝ} (hb : 0 < b) :
    Ward.Vh (1 / b) ((μ₀ + msq) / b - 1) msq 0 = (⟨0, 0, (μ₀ : ℂ), (b : ℂ)⟩ : Loc.Vcoup) := by
  unfold Ward.Vh
  have e1 : (1 + 0) * (1 + ((μ₀ + msq) / b - 1)) / (1 / b) - msq = μ₀ := by
    field_simp; ring
  have e2 : (1 + (0 : ℝ)) ^ 2 / (1 / b) = b := by norm_num
  rw [e1, e2, Complex.ofReal_zero]

/-- `⟨Z_0⟩_{Γ_0}` is the partition function of the bridge model. -/
theorem omega_Zh_zero_eq (hL7 : 7 ≤ L) (hm0 : 0 < R.msq) (hN : 1 ≤ N) (t : Hist.Seq (Xs R))
    {b μ₀ : ℝ} (hb : 0 < b) (ht : t 0 = (b, μ₀, 0)) :
    omegaC (Γh R 0 t) (Zh R 0 t : Alg 2 L N) =
      Obs.Zb (Suscept.Cov 2 L N R.msq)
        (VE (Ward.Vh (1 / b) ((μ₀ + R.msq) / b - 1) R.msq 0) (univ : Finset (Lam 2 L N))) := by
  rw [Γh_zero_eq_Cov R hL7 hm0 hN, Zh_zero_eq_Z0 R t ht, Vh_eq_V0 hb, Obs.Zb, omega_eq_omegaC]
  rfl

/-- **`⟨Z_0⟩_C ≠ 0`** for `b > 0` and `h = (μ₀ + m²)/b - 1 ≥ 0`. -/
theorem omega_Zh_zero_ne (hL7 : 7 ≤ L) (hm0 : 0 < R.msq) (hN : 1 ≤ N) (t : Hist.Seq (Xs R))
    {b μ₀ : ℝ} (hb : 0 < b) (hh : b ≤ μ₀ + R.msq) (ht : t 0 = (b, μ₀, 0)) :
    omegaC (Γh R 0 t) (Zh R 0 t : Alg 2 L N) ≠ 0 := by
  rw [omega_Zh_zero_eq R hL7 hm0 hN t hb ht]
  intro h0
  have hB := Ward.bridge_Z (d := 2) (L := L) (N := N) (β := 1 / b) (h := (μ₀ + R.msq) / b - 1)
    (s₀ := 0) (by positivity) (by norm_num) hm0
  rw [h0, mul_zero] at hB
  have hh0 : 0 ≤ (μ₀ + R.msq) / b - 1 := by
    rw [sub_nonneg, le_div_iff₀ hb]; linarith
  have hpos := H02.expect_one_pos (Ward.nnW_symm (d := 2) (L := L) (N := N) (1 / b))
    (Ward.nnW_nonneg (by positivity)) (h := fun _ => (μ₀ + R.msq) / b - 1) (fun _ => hh0)
  have : (H02.expect (Ward.nnW 2 L N (1 / b)) (fun _ => (μ₀ + R.msq) / b - 1) 1 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 hpos.ne'
  exact this hB

/-- The initial point of a trajectory. -/
theorem traj_zero_eq (b μ₀ : ℝ) : traj (rgData R) ((L : ℝ) ^ 2) b μ₀ 0 = (b, μ₀, 0) := rfl

/-- **`1 + ũ_{N,N} ≠ 0`** along a trajectory with `b > 0`, `b ≤ μ₀ + m²` (`h ≥ 0`). -/
theorem one_add_uFin_ne_zero {Nh : ℕ} (hN : Nh + 2 = N) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < R.msq)
    (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt R j)
    (hVL : ValidAtL R Nh) {b μ₀ : ℝ} (hb : 0 < b) (hh : b ≤ μ₀ + R.msq)
    (hVN : ∀ c ∈ blockIdx (L := L) (N := N) (Nh + 1),
      ((lastOut R Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)).V c : Alg 2 L N) =
        Step2.Vcoup (lastOut R Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)).κ (blockSet (Nh + 1) c)) :
    let t := traj (rgData R) ((L : ℝ) ^ 2) b μ₀
    omegaC (Γh R 0 t) (Zh R 0 t : Alg 2 L N) ≠ 0 ∧
      1 + uFin (Nh + 1) (lastOut R Nh t) (zmRaw R (Nh + 1) (lastOut R Nh t).ζ) ≠ 0 := by
  intro t
  have hL7 : 7 ≤ L := by have := hVL.1; norm_num at this; omega
  have hZ := omega_Zh_zero_ne R hL7 hm0 (by omega) t hb hh (traj_zero_eq R b μ₀)
  refine ⟨hZ, fun h => hZ ?_⟩
  rw [hist_omega_traj R hN hρ1 hspl hm0 hm hV hVL b μ₀ hVN, h, mul_zero, mul_zero]

end

end PtCorr2
