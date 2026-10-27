import PtCorr2.Zero.ZeroShiftDeriv
import Suscept.Moments

/-!
# The dressed `prop:suscept`: the susceptibility from the flow (route (A))

`Γ_0 = C = (−Δ + m²)^{-1}` (the first covariance of the dressed decomposition is the full one,
`StdHyp.sum_eq`), real with row and column sums `1/m²` (`Γ0_real`, `Γ0_row`).
With Gaussian integration by parts (`Suscept.sum_omega_psibar_psi`) and `c2_formula`,

`∑_{x,y} ⟨Z_0 ψ̄_x ψ_y⟩_C = m^{-2}|Λ| ⟨Z_0⟩_C + m^{-4} c2(𝔼_Cθ Z_0)`, and (**`suscept2`**)

`|Λ|^{-1} ∑_{x,y} ⟨Z_0 ψ̄_xψ_y⟩_C / ⟨Z_0⟩_C =
  m^{-2} − m^{-4} [ ã π_N/(1 + ũ) + ∑_{j<N} c_jπ_j/ρ_j ]`,

provided `⟨Z_0⟩_C ≠ 0`. With `a_j = 0` (no dressing) this is the old `prop_suscept`.
-/

namespace PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Step2 Step Step2.LastN

local notation "cj" => starRingEnd ℂ

variable {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- `Γ_0 = C_{>0} = ∑_{k=1}^N C_k`. -/
theorem Gam0_eq (t : Hist.Seq (Xs R)) :
    (Dh R 0 t).Gam 0 = DressedFRD.ofR fun m => ∑ k ∈ Ioc 0 N, DressedFRD.frdC R.P R.msq L N k m := by
  funext m
  simp [DressedFRD.Data.Gam, DressedFRD.Data.Z, DressedFRD.Data.tails, DressedFRD.Cgt,
    DressedFRD.ofR, Dh, stData]

theorem Γ0_real (t : Hist.Seq (Xs R)) (x y : Lam 2 L N) : cj (Γh R 0 t x y) = Γh R 0 t x y := by
  have hm : (Dh R 0 t).Gam 0 ∈ DressedFRD.realSub := by
    rw [Gam0_eq]
    exact DressedFRD.ofR_mem fun m => sum_congr rfl fun k _ => DressedFRD.frdC_even R.P k m
  exact kern_real hm (x - y)

/-- The real matrix of `Γ_0`. -/
def Γ0r (t : Hist.Seq (Xs R)) : Matrix (Lam 2 L N) (Lam 2 L N) ℝ := fun x y => (Γh R 0 t x y).re

theorem cplx_Γ0r (t : Hist.Seq (Xs R)) : cplx (Γ0r R t) = Γh R 0 t := by
  ext x y
  exact Complex.conj_eq_iff_re.1 (Γ0_real R t x y)

theorem sum_kern_eq (w : DressedFRD.Sym 2 (L ^ N)) : ∑ z : Lam 2 L N, DressedFRD.kern w z = w 0 := by
  have := DressedFRD.sum_kern_mul_conj w 0
  simpa [FRD.char_zero_left] using this

theorem Γh_zero_apply (t : Hist.Seq (Xs R)) (x y : Lam 2 L N) :
    Γh R 0 t x y = DressedFRD.kern ((Dh R 0 t).Gam 0) (x - y) := rfl

/-- **The row and column sums of `Γ_0` are `1/m²`.** -/
theorem Γ0_sums (hL7 : 7 ≤ L) (hm0 : 0 < R.msq) (hN : 1 ≤ N) (t : Hist.Seq (Xs R)) :
    (∀ x, ∑ y, Γ0r R t x y = 1 / R.msq) ∧ ∀ y, ∑ x, Γ0r R t x y = 1 / R.msq := by
  obtain ⟨cS, -, hS⟩ := DressedFRD.frd_stdFull R.P (d := 2) le_rfl hL7 (q := 2) (M := 2 + 2 + 1)
    le_rfl
  have hstd := (hS (L ^ N) N R.msq hN rfl hm0).base
  have h0 : (Dh R 0 t).Gam 0 0 = ((1 / R.msq : ℝ) : ℂ) := by
    rw [Gam0_eq]
    simp only [DressedFRD.ofR]
    congr 1
    have hI : Ioc 0 N = Icc 1 N := by ext k; simp only [mem_Ioc, mem_Icc]; omega
    rw [hI, hstd.sum_eq 0, DressedFRD.lam_zero', zero_add, one_div]
  have hrow : ∀ x, ∑ y, Γh R 0 t x y = ((1 / R.msq : ℝ) : ℂ) := fun x => by
    simp only [Γh_zero_apply]
    rw [← h0, ← sum_kern_eq ((Dh R 0 t).Gam 0)]
    exact (Equiv.subLeft x).sum_comp (fun z => DressedFRD.kern ((Dh R 0 t).Gam 0) z)
  have hcol : ∀ y, ∑ x, Γh R 0 t x y = ((1 / R.msq : ℝ) : ℂ) := fun y => by
    simp only [Γh_zero_apply]
    rw [← h0, ← sum_kern_eq ((Dh R 0 t).Gam 0)]
    exact (Equiv.subRight y).sum_comp (fun z => DressedFRD.kern ((Dh R 0 t).Gam 0) z)
  refine ⟨fun x => ?_, fun y => ?_⟩
  · simp only [Γ0r]; rw [← Complex.re_sum, hrow, Complex.ofReal_re]
  · simp only [Γ0r]; rw [← Complex.re_sum, hcol, Complex.ofReal_re]

/-- **The dressed `prop:suscept`** (route (A)): the averaged susceptibility from the flow. -/
theorem suscept2 (hL7 : 7 ≤ L) {Nh : ℕ} (hN : Nh + 2 = N) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < R.msq)
    (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt R j)
    (hVL : ValidAtL R Nh) (b μ₀ : ℝ)
    (hVN : ∀ c ∈ blockIdx (L := L) (N := N) (Nh + 1),
      ((lastOut R Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)).V c : Alg 2 L N) =
        Vcoup (lastOut R Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)).κ (blockSet (Nh + 1) c))
    (hZ : omegaC (Γh R 0 (traj (rgData R) ((L : ℝ) ^ 2) b μ₀))
      (Zh R 0 (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) : Alg 2 L N) ≠ 0) :
    let t := traj (rgData R) ((L : ℝ) ^ 2) b μ₀
    (Fintype.card (Lam 2 L N) : ℂ)⁻¹ *
        (∑ x : Lam 2 L N, ∑ y : Lam 2 L N,
          omegaC (Γh R 0 t) ((Zh R 0 t : Alg 2 L N) * (psibar x * psi y))) /
        omegaC (Γh R 0 t) (Zh R 0 t : Alg 2 L N) =
      1 / (R.msq : ℂ) - (1 / (R.msq : ℂ)) ^ 2 *
        (aFin (Nh + 1) (lastOut R Nh t) * πh R (Nh + 2) t /
            (1 + uFin (Nh + 1) (lastOut R Nh t) (zmRaw R (Nh + 1) (lastOut R Nh t).ζ)) +
          ∑ j ∈ range (Nh + 2), ch₀ R j t * πh R j t / ρh R j t) := by
  have hc2 := c2_formula R hN hρ1 hspl hm0 hm hV hVL b μ₀ hVN
  have hZ0 := hist_omega_traj R hN hρ1 hspl hm0 hm hV hVL b μ₀ hVN
  dsimp only at hc2 hZ0 ⊢
  set t := traj (rgData R) ((L : ℝ) ^ 2) b μ₀ with ht
  obtain ⟨hrow, hcol⟩ := Γ0_sums R hL7 hm0 (by omega) t
  have hIBP := Suscept.sum_omega_psibar_psi (Γ0r R t) hrow hcol (mem_Ev.1 (Zh R 0 t).2)
  simp only [omega_eq_omegaC, EC_eq_ECC, cplx_Γ0r, ECC_theta] at hIBP
  rw [hIBP, hc2]
  rw [hZ0] at hZ ⊢
  have hc : (Fintype.card (Lam 2 L N) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hmC : (R.msq : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hm0.ne'
  have hu : 1 + uFin (Nh + 1) (lastOut R Nh t) (zmRaw R (Nh + 1) (lastOut R Nh t).ζ) ≠ 0 := by
    intro h; apply hZ; rw [h]; ring
  have hP : (∏ j ∈ range (Nh + 1), ch R j t) *
      (detStep R (Nh + 1) (histOut R Nh t).st * Complex.exp (-(lastOut R Nh t).u)) ≠ 0 := by
    intro h; apply hZ
    rw [show ∀ A d e u : ℂ, A * (d * e * u) = A * (d * e) * u from fun A d e u => by ring, h,
      zero_mul]
  have hA := left_ne_zero_of_mul hP
  have hde := right_ne_zero_of_mul hP
  have hd := left_ne_zero_of_mul hde
  push_cast
  field_simp
  ring

end

end PtCorr2
