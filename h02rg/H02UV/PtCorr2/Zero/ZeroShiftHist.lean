import PtCorr2.Zero.ZeroShift
import PtCorr2.Zero.ChainFlow

/-!
# Route (A) along a trajectory: `⟨Z_0⟩_{C + s𝟙}` through the dressed flow

Along a trajectory of the flow, with the zero-mode shifts `x_0 = s`, `x_{j+1} = shiftNext D_j j x_j`
(`xh`) and the shifted covariances `Γ_j + x_j/|Λ|` (`Γs`), the RG maps are unchanged and
(`hist_omega_shift`)

`⟨Z_0⟩_{Γ_0 + s/|Λ|} = ∏_{j ≤ N_h}[det(1 + a_jA(Γ_j + x_j/|Λ|)) e^{-u_{j+1}(Λ)}] ·
det(1 + a_{N-1}A(Γ_{N-1} + x_{N-1}/|Λ|)) e^{-u_N(Λ)} (1 + ũ_{N,N} + ã_{N,N} x_N)`,

provided the shifted absorption denominators `1 + a_j m²(γ_j + x_j)` do not vanish (`ShiftOK`).
The left side is `⟨Z_0⟩_{Γ_0} − (s/|Λ|) c2(𝔼_{Γ_0}θ Z_0)` (`omegaC_add_cstC`). At `s = 0` this is
`hist_omega_traj`.
-/

namespace PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Step2 Step Step2.LastN

variable {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- The dressed data of step `j` along the history. -/
abbrev Dh (j : ℕ) (t : Hist.Seq (Xs R)) : DressedFRD.Data 2 (L ^ N) := stData R j (rawHist R j t)

/-- The zero-mode shifts along the history. -/
def xh (t : Hist.Seq (Xs R)) (s : ℂ) : ℕ → ℂ
  | 0 => s
  | j + 1 => shiftNext (Dh R j t) j (xh t s j)

/-- The shifted covariance `Γ_j + x_j/|Λ|`. -/
def Γs (j : ℕ) (t : Hist.Seq (Xs R)) (s : ℂ) : Matrix (Lam 2 L N) (Lam 2 L N) ℂ :=
  DressedFRD.kmat ((Dh R j t).Gam j + zsym (xh R t s j))

/-- The factor of step `j` with the shift. -/
def chs (j : ℕ) (t : Hist.Seq (Xs R)) (s : ℂ) : ℂ :=
  (1 + stA R (rawHist R j t) • (Aop (d := 2) (L := L) (N := N) R.msq * Γs R j t s)).det *
    Complex.exp (-uOut R j (rawHist R j t) (t j).1 (t j).2.1 (rawD R (rawHist R j t).u (t j).2.2)
      (rawK R (rawHist R j t).u (t j).2.2))

/-- The shifted absorption denominators do not vanish. -/
def ShiftOK (t : Hist.Seq (Xs R)) (s : ℂ) (n : ℕ) : Prop :=
  ∀ j ≤ n, 1 + (Dh R j t).ζ j * (Dh R j t).Z j * DressedFRD.Asym (d := 2) (n := L ^ N) (Dh R j t).msq 0 *
    ((Dh R j t).Gam j 0 + xh R t s j) ≠ 0

theorem Γs_zero_shift (t : Hist.Seq (Xs R)) (s : ℂ) :
    Γs R 0 t s = Γh R 0 t + cstC (Lam 2 L N) (s / Fintype.card (Lam 2 L N)) := by
  rw [Γs, kmat_add, kmat_zsym]; rfl

variable {R}

/-- **The last step with a shift**: the shift ends up in the zero-mode integral. -/
theorem lastStep_omega_shift {j : ℕ} {st : RawSt 2 L N} {g μ : ℝ} {D : Fam 2 L N}
    {K : Act 2 L N} (hj : j + 1 = N) (H : RawInv R j st) (hS : SplitOK R j st) (x : ℂ)
    (hx : 1 + (stData R j st).ζ j * (stData R j st).Z j * DressedFRD.Asym (d := 2) (n := L ^ N) (stData R j st).msq 0 *
      ((stData R j st).Gam j 0 + x) ≠ 0)
    (hV : ∀ b ∈ blockIdx (L := L) (N := N) j,
      ((rawStepN R j st g μ D K).V b : Alg 2 L N) =
        Vcoup (rawStepN R j st g μ D K).κ (blockSet j b)) :
    omegaC (DressedFRD.kmat ((stData R j st).Gam j + zsym x)) (Zin R j st g μ D K : Alg 2 L N) =
      (1 + stA R st • (Aop (d := 2) (L := L) (N := N) R.msq *
          DressedFRD.kmat ((stData R j st).Gam j + zsym x))).det *
        Complex.exp (-(rawStepN R j st g μ D K).u) *
        (1 + uFin j (rawStepN R j st g μ D K) (zmRaw R j (rawStepN R j st g μ D K).ζ) +
          aFin j (rawStepN R j st g μ D K) * shiftNext (stData R j st) j x) := by
  obtain ⟨hT, hΓ⟩ := split_shift (L := L) (N := N) (stData R j st) j x hS.1 hS.2 hx
  rw [stData_ζZ H] at hT hΓ
  have e : stA R st - stYc R st + stYc R st = stA R st := sub_add_cancel _ _
  have hG0 : (stData R j st).Gam (j + 1) = 0 := by
    funext m
    simp only [DressedFRD.Data.Gam, Pi.add_apply, Pi.smul_apply, Finset.sum_apply]
    have h1 : DressedFRD.Cgt (stData R j st).C (stData R j st).N (j + 1) = 0 := by
      show DressedFRD.Cgt _ N (j + 1) = 0
      simp [DressedFRD.Cgt, ← hj]
    have h2 : Ioc (j + 1) (stData R j st).N = ∅ := by
      show Ioc (j + 1) N = ∅
      rw [← hj, Finset.Ioc_self]
    rw [h1, h2]; simp
  have hΓ2 : DressedFRD.kmat ((stData R j st).Gam (j + 1) + zsym (shiftNext (stData R j st) j x)) =
      cstC (Lam 2 L N) (shiftNext (stData R j st) j x / Fintype.card (Lam 2 L N)) := by
    rw [hG0, zero_add, kmat_zsym]
  have hstep := omegaC_gZ_step j R.msq (stA R st - stYc R st) (stYc R st) 1 1 (by norm_num)
    (stVf R j st g μ) (stDelta R j st) (st.Wl + D) K (eps_VfamL j _) (fun b => coe_stDelta b)
    (DressedFRD.kmat ((stData R j st).Gam j + zsym x))
    (fullCovN R j (Function.update st.ζ j (stZeta R st)))
    (DressedFRD.kmat ((stData R j st).Gam (j + 1) + zsym (shiftNext (stData R j st) j x)))
    (by rw [e]; exact hT) (by rw [e]; exact hΓ)
  rw [e, hΓ2] at hstep
  have hVs : (fun b => sigE 1 (stVf R j st g μ b)) = stVf R j st g μ := funext fun b => sigE_one' _
  have hWs : (fun b => sigE 1 ((st.Wl + D) b)) = st.Wl + D := funext fun b => sigE_one' _
  have hKs : (fun Y => sigE 1 (bpow j (fun b => gexp (stDelta R j st b)) Y * K Y)) =
      Kflat j (stDelta R j st) K := funext fun Y => sigE_one' _
  simp only [hVs, hWs, hKs, one_pow, one_smul] at hstep
  have hl := lastN_full_ZVK R hj st g μ D K
  rw [show fullCovN R j (rawStepN R j st g μ D K).ζ =
    fullCovN R j (Function.update st.ζ j (stZeta R st)) from rfl] at hl
  have hc : (Fintype.card (Lam 2 L N) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [Zin, hstep, hl, omegaC_smul', omegaC_cstC_ZtFin _ _ hV, mul_assoc,
    div_mul_cancel₀ _ hc]

/-- **One raw step with a shift.** -/
theorem rawStep_omega_shift {j : ℕ} {st : RawSt 2 L N} {g μ : ℝ} {D : Fam 2 L N}
    {K : Act 2 L N} (hV : ValidCore R j) (H : RawInv R j st) (hD : D ∈ BSub (L := L) (N := N) j)
    (hK : K ∈ ASub (L := L) (N := N) j) (hS : SplitOK R j st) (x : ℂ)
    (hx : 1 + (stData R j st).ζ j * (stData R j st).Z j * DressedFRD.Asym (d := 2) (n := L ^ N) (stData R j st).msq 0 *
      ((stData R j st).Gam j 0 + x) ≠ 0) :
    omegaC (DressedFRD.kmat ((stData R j st).Gam j + zsym x)) (Zin R j st g μ D K : Alg 2 L N) =
      (1 + stA R st • (Aop (d := 2) (L := L) (N := N) R.msq *
          DressedFRD.kmat ((stData R j st).Gam j + zsym x))).det *
        Complex.exp (-uOut R j st g μ D K) *
        omegaC (DressedFRD.kmat ((stData R j st).Gam (j + 1) + zsym (shiftNext (stData R j st) j x)))
          (Zout R j st g μ D K : Alg 2 L N) := by
  obtain ⟨hT, hΓ⟩ := split_shift (L := L) (N := N) (stData R j st) j x hS.1 hS.2 hx
  rw [stData_ζZ H] at hT hΓ
  exact rawStep_omega_gen hV H hD hK _ _ hT hΓ

variable (R)

set_option maxHeartbeats 1000000 in
/-- **The partition function with a zero-mode shift along a trajectory.** -/
theorem hist_omega_shift {Nh : ℕ} (hN : Nh + 2 = N) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < R.msq)
    (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt R j)
    (hVL : ValidAtL R Nh) (b μ₀ : ℝ) (s : ℂ)
    (hVN : ∀ c ∈ blockIdx (L := L) (N := N) (Nh + 1),
      ((lastOut R Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)).V c : Alg 2 L N) =
        Vcoup (lastOut R Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)).κ (blockSet (Nh + 1) c))
    (hx : ShiftOK R (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) s (Nh + 1)) :
    let t := traj (rgData R) ((L : ℝ) ^ 2) b μ₀
    omegaC (Γs R 0 t s) (Zh R 0 t : Alg 2 L N) =
      (∏ j ∈ range (Nh + 1), chs R j t s) *
        ((1 + stA R (histOut R Nh t).st • (Aop (d := 2) (L := L) (N := N) R.msq *
            Γs R (Nh + 1) t s)).det * Complex.exp (-(lastOut R Nh t).u) *
          (1 + uFin (Nh + 1) (lastOut R Nh t) (zmRaw R (Nh + 1) (lastOut R Nh t).ζ) +
            aFin (Nh + 1) (lastOut R Nh t) * xh R t s (Nh + 2))) := by
  intro t
  have hρ0 : 0 ≤ R.ρ := hVL.2.2.2.2.1
  have hLg := hVL.1
  have hcore : ∀ j ≤ Nh, ValidCore R j := fun j hj => by
    rcases Nat.lt_or_ge j Nh with h | h
    · exact (hV j h).toValidCore
    · rw [show j = Nh by omega]; exact hVL.2
  have hRI : ∀ j ≤ Nh + 1, RawInv R j (rawHist R j t) := rawInv_histU R hV hVL t
  have hS : ∀ j ≤ Nh + 1, SplitOK R j (rawHist R j t) :=
    fun j hj => splitOK_hist R hρ0 hspl (by omega) hm0 hm t (by omega)
  have hstep : ∀ j ≤ Nh, omegaC (Γs R j t s) (Zh R j t : Alg 2 L N) =
      chs R j t s * omegaC (DressedFRD.kmat ((Dh R j t).Gam (j + 1) + zsym (xh R t s (j + 1))))
        (Zout R j (rawHist R j t) (t j).1 (t j).2.1 (rawD R (rawHist R j t).u (t j).2.2)
          (rawK R (rawHist R j t).u (t j).2.2) : Alg 2 L N) := fun j hj =>
    rawStep_omega_shift (hcore j hj) (hRI j (by omega)) (rawD_mem R _ _) (rawK_mem R _ _)
      (hS j (by omega)) _ (hx j (by omega))
  have h1 := chain_omega (Γ := fun j => Γs R j t s) (Zs := fun j => Zh R j t)
    (c := fun j => chs R j t s) Nh fun i hi => by
      show omegaC (Γs R i t s) (Zh R i t : Alg 2 L N) =
        chs R i t s * omegaC (Γs R (i + 1) t s) (Zh R (i + 1) t : Alg 2 L N)
      have hE := traj_exact R hρ1 hLg b μ₀ (j := i) (fun k hk => hV k (by omega))
      rw [hstep i hi.le, hE.1, hE.2]
      rfl
  have h2 := hstep Nh le_rfl
  have hEL := traj_exactL R hρ1 b μ₀ hV hVL
  rw [hEL.1, hEL.2] at h2
  have h3 := lastStep_omega_shift (R := R) (j := Nh + 1) (st := (histOut R Nh t).st)
    (g := (histOut R Nh t).g.re) (μ := (histOut R Nh t).nu.re) (D := (histOut R Nh t).D)
    (K := (histOut R Nh t).K) (by omega) (hRI (Nh + 1) le_rfl) (hS (Nh + 1) le_rfl)
    (xh R t s (Nh + 1)) (hx (Nh + 1) le_rfl) hVN
  rw [h1, h2, h3, prod_range_succ]
  simp only [lastOut, Γs, Dh, xh, rawHist_succ]
  ring

end

end PtCorr2
