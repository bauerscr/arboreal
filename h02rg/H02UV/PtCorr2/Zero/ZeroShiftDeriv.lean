import PtCorr2.Zero.ZeroShiftHist

/-!
# Route (A): the `ψψ̄` coefficient of `𝔼_{Γ_0}θ Z_0` from the dressed flow

Differentiating `hist_omega_shift` at `s = 0`. With `c_j = a_j m²` (`ch₀`),
`ρ_j = 1 + c_jγ_j` (`ρh`, `γ_j = Γ̂_j(0)`) and `π_j = ∏_{i<j} ρ_i^{-2}` (`πh`):

* `xh_zero`, `hasDerivAt_xh`: `x_j(0) = 0`, `x_j'(0) = π_j`;
* **`c2_formula`**: `c2(𝔼_{Γ_0}θ Z_0) = −|Λ| P [(1 + ũ) ∑_{j ≤ N-1} c_jπ_j/ρ_j + ã π_N]`, where
  `P (1 + ũ) = ⟨Z_0⟩_{Γ_0}` (`hist_omega_traj`).

For the undressed flow (`a_j = 0`) this is `c2 = −|Λ| P ã`, the old `prop:ZNN` relation
`k² = −|Λ| ã`. The dressed corrections are the zero-mode absorption terms `c_jπ_j/ρ_j`.
-/

namespace PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Step2 Step Step2.LastN Filter Topology

variable {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- `c_j = a_j m²`. -/
def ch₀ (j : ℕ) (t : Hist.Seq (Xs R)) : ℂ :=
  (Dh R j t).ζ j * (Dh R j t).Z j * DressedFRD.Asym (d := 2) (n := L ^ N) (Dh R j t).msq 0

/-- `ρ_j = 1 + c_j γ_j`. -/
def ρh (j : ℕ) (t : Hist.Seq (Xs R)) : ℂ := 1 + ch₀ R j t * (Dh R j t).Gam j 0

/-- `π_j = ∏_{i<j} ρ_i^{-2}`. -/
def πh (j : ℕ) (t : Hist.Seq (Xs R)) : ℂ := ∏ i ∈ range j, (ρh R i t)⁻¹ ^ 2

theorem xh_zero (t : Hist.Seq (Xs R)) : ∀ j, xh R t 0 j = 0
  | 0 => rfl
  | j + 1 => by
    show shiftNext (Dh R j t) j (xh R t 0 j) = 0
    rw [xh_zero t j, shiftNext, add_zero, sub_self]

theorem hasDerivAt_xh (t : Hist.Seq (Xs R)) :
    ∀ j, (∀ i < j, ρh R i t ≠ 0) → HasDerivAt (fun s => xh R t s j) (πh R j t) 0
  | 0, _ => by
    show HasDerivAt (fun s : ℂ => s) (∏ i ∈ range 0, (ρh R i t)⁻¹ ^ 2) 0
    rw [prod_range_zero]
    exact hasDerivAt_id' 0
  | j + 1, h => by
    have ih := hasDerivAt_xh t j fun i hi => h i (by omega)
    have hρ := h j (by omega)
    have hρ'' : 1 + ch₀ R j t * (Dh R j t).Gam j 0 ≠ 0 := hρ
    have hρ' : 1 + ch₀ R j t * ((Dh R j t).Gam j 0 + 0) ≠ 0 := by rw [add_zero]; exact hρ
    have hf : HasDerivAt (fun y : ℂ => ((Dh R j t).Gam j 0 + y) /
        (1 + ch₀ R j t * ((Dh R j t).Gam j 0 + y)) -
          (Dh R j t).Gam j 0 / (1 + ch₀ R j t * (Dh R j t).Gam j 0))
        ((ρh R j t)⁻¹ ^ 2) 0 := by
      have h1 : HasDerivAt (fun y : ℂ => (Dh R j t).Gam j 0 + y) 1 0 :=
        (hasDerivAt_id' 0).const_add _
      have h2 : HasDerivAt (fun y : ℂ => 1 + ch₀ R j t * ((Dh R j t).Gam j 0 + y)) (ch₀ R j t) 0 := by
        simpa using (h1.const_mul (ch₀ R j t)).const_add 1
      have h3 := (h1.div h2 hρ').sub_const ((Dh R j t).Gam j 0 / (1 + ch₀ R j t * (Dh R j t).Gam j 0))
      convert h3 using 1
      rw [ρh, add_zero, inv_pow]
      field_simp
      ring
    have hx0 := xh_zero R t j
    have hf' : HasDerivAt (fun y : ℂ => ((Dh R j t).Gam j 0 + y) /
        (1 + ch₀ R j t * ((Dh R j t).Gam j 0 + y)) -
          (Dh R j t).Gam j 0 / (1 + ch₀ R j t * (Dh R j t).Gam j 0))
        ((ρh R j t)⁻¹ ^ 2) (xh R t 0 j) := by rw [hx0]; exact hf
    have hc := hf'.comp (0 : ℂ) ih
    convert hc using 1
    rw [πh, prod_range_succ, πh]; ring

/-- `r_j(s) = (1 + c_j(γ_j + x_j(s)))/ρ_j`, the zero-mode factor of the shifted determinant. -/
def rh (j : ℕ) (t : Hist.Seq (Xs R)) (s : ℂ) : ℂ :=
  (1 + ch₀ R j t * ((Dh R j t).Gam j 0 + xh R t s j)) / ρh R j t

theorem hasDerivAt_rh (t : Hist.Seq (Xs R)) (j : ℕ) (h : ∀ i < j, ρh R i t ≠ 0) :
    HasDerivAt (fun s => rh R j t s) (ch₀ R j t * πh R j t / ρh R j t) 0 := by
  have hx := hasDerivAt_xh R t j h
  have h1 := ((hx.const_add ((Dh R j t).Gam j 0)).const_mul (ch₀ R j t)).const_add 1
  have h2 := h1.div_const (ρh R j t)
  simpa [rh] using h2

theorem rh_zero (t : Hist.Seq (Xs R)) (j : ℕ) (h : ρh R j t ≠ 0) : rh R j t 0 = 1 := by
  rw [rh, xh_zero, add_zero]; exact div_self h

/-- The factor of step `j` with a shift: `det(1 + aA(Γ_j + x_j)) e^{-u} = det(1 + aAΓ_j) e^{-u} r_j`. -/
theorem chs_eq (t : Hist.Seq (Xs R)) {j : ℕ} (H : RawInv R j (rawHist R j t))
    (hS : SplitOK R j (rawHist R j t)) (s : ℂ) : chs R j t s = ch R j t * rh R j t s := by
  have hden : ∀ m, 1 + stA R (rawHist R j t) * DressedFRD.Asym R.msq m * (Dh R j t).Gam j m ≠ 0 :=
    fun m => by have := hS.1 m; rwa [stData_ζZ H] at this
  have hd := det_shift (L := L) (N := N) ((Dh R j t).Gam j) (stA R (rawHist R j t))
    (xh R t s j) R.msq hden
  have hc : ch₀ R j t = stA R (rawHist R j t) * DressedFRD.Asym (d := 2) (n := L ^ N) R.msq 0 := by
    rw [ch₀, stData_ζZ H]; rfl
  rw [chs, ch, rh, ρh, Γs, hd, hc, detStep]
  ring

/-- **The ψψ̄ coefficient of `𝔼_{Γ_0}θ Z_0` from the dressed flow** (route (A)). -/
theorem c2_formula {Nh : ℕ} (hN : Nh + 2 = N) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < R.msq)
    (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt R j)
    (hVL : ValidAtL R Nh) (b μ₀ : ℝ)
    (hVN : ∀ c ∈ blockIdx (L := L) (N := N) (Nh + 1),
      ((lastOut R Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)).V c : Alg 2 L N) =
        Vcoup (lastOut R Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)).κ (blockSet (Nh + 1) c)) :
    let t := traj (rgData R) ((L : ℝ) ^ 2) b μ₀
    Suscept.c2 (expLC (Γh R 0 t) (Zh R 0 t : Alg 2 L N)) =
      -(Fintype.card (Lam 2 L N) : ℂ) * ((∏ j ∈ range (Nh + 1), ch R j t) * (detStep R (Nh + 1) (histOut R Nh t).st * Complex.exp (-(lastOut R Nh t).u))) *
        ((1 + uFin (Nh + 1) (lastOut R Nh t) (zmRaw R (Nh + 1) (lastOut R Nh t).ζ)) *
            ∑ j ∈ range (Nh + 2), ch₀ R j t * πh R j t / ρh R j t +
          aFin (Nh + 1) (lastOut R Nh t) * πh R (Nh + 2) t) := by
  intro t
  have hρ0 : 0 ≤ R.ρ := hVL.2.2.2.2.1
  have hRI : ∀ j ≤ Nh + 1, RawInv R j (rawHist R j t) := rawInv_histU R hV hVL t
  have hS : ∀ j ≤ Nh + 1, SplitOK R j (rawHist R j t) :=
    fun j hj => splitOK_hist R hρ0 hspl (by omega) hm0 hm t (by omega)
  have hρ : ∀ j ≤ Nh + 1, ρh R j t ≠ 0 := fun j hj => by
    exact (hS j hj).1 0
  have hc : (Fintype.card (Lam 2 L N) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  -- the shifted partition function
  have hF : ∀ s, omegaC (Γs R 0 t s) (Zh R 0 t : Alg 2 L N) =
      omegaC (Γh R 0 t) (Zh R 0 t : Alg 2 L N) - s / Fintype.card (Lam 2 L N) * Suscept.c2 (expLC (Γh R 0 t) (Zh R 0 t : Alg 2 L N)) := by
    intro s
    rw [Γs_zero_shift, omegaC_add_cstC _ _ (mem_Ev.1 (Zh R 0 t).2)]
  have hdF : HasDerivAt (fun s => omegaC (Γs R 0 t s) (Zh R 0 t : Alg 2 L N))
      (-(Suscept.c2 (expLC (Γh R 0 t) (Zh R 0 t : Alg 2 L N)) / Fintype.card (Lam 2 L N))) 0 := by
    have h0 : HasDerivAt (fun s : ℂ => s / (Fintype.card (Lam 2 L N) : ℂ) * Suscept.c2 (expLC (Γh R 0 t) (Zh R 0 t : Alg 2 L N)))
        (1 / (Fintype.card (Lam 2 L N) : ℂ) * Suscept.c2 (expLC (Γh R 0 t) (Zh R 0 t : Alg 2 L N))) 0 :=
      ((hasDerivAt_id (0 : ℂ)).div_const _).mul_const _
    have h1 := h0.const_sub (omegaC (Γh R 0 t) (Zh R 0 t : Alg 2 L N))
    rw [show (fun s => omegaC (Γs R 0 t s) (Zh R 0 t : Alg 2 L N)) = fun s =>
      omegaC (Γh R 0 t) (Zh R 0 t : Alg 2 L N) - s / Fintype.card (Lam 2 L N) * Suscept.c2 (expLC (Γh R 0 t) (Zh R 0 t : Alg 2 L N))
      from funext hF]
    convert h1 using 1
    ring
  -- the right side
  have hR2 : ∀ s, ShiftOK R t s (Nh + 1) → omegaC (Γs R 0 t s) (Zh R 0 t : Alg 2 L N) =
      ((∏ j ∈ range (Nh + 1), ch R j t) * (detStep R (Nh + 1) (histOut R Nh t).st * Complex.exp (-(lastOut R Nh t).u))) * (∏ j ∈ range (Nh + 2), rh R j t s) * ((1 + uFin (Nh + 1) (lastOut R Nh t) (zmRaw R (Nh + 1) (lastOut R Nh t).ζ)) + (aFin (Nh + 1) (lastOut R Nh t)) * xh R t s (Nh + 2)) := by
    intro s hs
    rw [hist_omega_shift R hN hρ1 hspl hm0 hm hV hVL b μ₀ s hVN hs]
    have e1 : ∀ j ∈ range (Nh + 1), chs R j t s = ch R j t * rh R j t s := fun j hj =>
      chs_eq R t (hRI j (by simp at hj; omega)) (hS j (by simp at hj; omega)) s
    have e2 := chs_eq R t (hRI (Nh + 1) le_rfl) (hS (Nh + 1) le_rfl) s
    simp only [chs, ch] at e2
    rw [prod_congr rfl e1, prod_mul_distrib]
    rw [prod_range_succ (fun j => rh R j t s) (Nh + 1)]
    have e3 : (1 + stA R (histOut R Nh t).st • (Aop (d := 2) (L := L) (N := N) R.msq *
        Γs R (Nh + 1) t s)).det = detStep R (Nh + 1) (histOut R Nh t).st * rh R (Nh + 1) t s := by
      have hden : ∀ m, 1 + stA R (histOut R Nh t).st * DressedFRD.Asym R.msq m *
          (Dh R (Nh + 1) t).Gam (Nh + 1) m ≠ 0 :=
        fun m => by have := (hS (Nh + 1) le_rfl).1 m; rwa [stData_ζZ (hRI (Nh + 1) le_rfl)] at this
      have hd := det_shift (L := L) (N := N) ((Dh R (Nh + 1) t).Gam (Nh + 1))
        (stA R (histOut R Nh t).st) (xh R t s (Nh + 1)) R.msq hden
      have hc' : ch₀ R (Nh + 1) t = stA R (histOut R Nh t).st * DressedFRD.Asym (d := 2) (n := L ^ N) R.msq 0 := by
        rw [ch₀, stData_ζZ (hRI (Nh + 1) le_rfl)]; rfl
      rw [Γs, hd, rh, ρh, hc', detStep]
      simp only [Dh, rawHist_succ]
    rw [e3]
    ring
  have hev : ∀ᶠ s in 𝓝 (0 : ℂ), ShiftOK R t s (Nh + 1) := by
    have : ∀ j ∈ range (Nh + 2), ∀ᶠ s in 𝓝 (0 : ℂ),
        1 + (Dh R j t).ζ j * (Dh R j t).Z j * DressedFRD.Asym (d := 2) (n := L ^ N) (Dh R j t).msq 0 *
          ((Dh R j t).Gam j 0 + xh R t s j) ≠ 0 := by
      intro j hj
      have hj' : j ≤ Nh + 1 := by simp at hj; omega
      have hcont : ContinuousAt (fun s => 1 + (Dh R j t).ζ j * (Dh R j t).Z j *
          DressedFRD.Asym (d := 2) (n := L ^ N) (Dh R j t).msq 0 * ((Dh R j t).Gam j 0 + xh R t s j)) 0 :=
        (((hasDerivAt_xh R t j fun i hi => hρ i (by omega)).continuousAt.const_add _).const_mul
          _).const_add _
      refine hcont.eventually_ne ?_
      rw [xh_zero, add_zero]
      exact (hS j hj').1 0
    filter_upwards [(Finset.range (Nh + 2)).eventually_all.2 this] with s hs
    exact fun j hj => hs j (by simp; omega)
  have hdR2 : HasDerivAt (fun s => ((∏ j ∈ range (Nh + 1), ch R j t) * (detStep R (Nh + 1) (histOut R Nh t).st * Complex.exp (-(lastOut R Nh t).u))) * (∏ j ∈ range (Nh + 2), rh R j t s) *
      ((1 + uFin (Nh + 1) (lastOut R Nh t) (zmRaw R (Nh + 1) (lastOut R Nh t).ζ)) + (aFin (Nh + 1) (lastOut R Nh t)) * xh R t s (Nh + 2))) (((∏ j ∈ range (Nh + 1), ch R j t) * (detStep R (Nh + 1) (histOut R Nh t).st * Complex.exp (-(lastOut R Nh t).u))) * ((∑ j ∈ range (Nh + 2), ch₀ R j t * πh R j t / ρh R j t) * (1 + uFin (Nh + 1) (lastOut R Nh t) (zmRaw R (Nh + 1) (lastOut R Nh t).ζ)) +
      (aFin (Nh + 1) (lastOut R Nh t)) * πh R (Nh + 2) t)) 0 := by
    have hprod := HasDerivAt.fun_finsetProd (u := range (Nh + 2)) (x := (0 : ℂ))
      (f := fun j s => rh R j t s) (f' := fun j => ch₀ R j t * πh R j t / ρh R j t)
      fun j hj => hasDerivAt_rh R t j fun i hi => hρ i (by simp at hj; omega)
    have h1 : ∀ i ∈ range (Nh + 2), (∏ j ∈ (range (Nh + 2)).erase i, rh R j t 0) = 1 :=
      fun i _ => prod_eq_one fun j hj => rh_zero R t j (hρ j (by
        have := (mem_erase.1 hj).2; simp at this; omega))
    rw [sum_congr rfl fun i hi => by rw [h1 i hi, one_smul]] at hprod
    have hx := hasDerivAt_xh R t (Nh + 2) fun i hi => hρ i (by omega)
    have hB := (hx.const_mul (aFin (Nh + 1) (lastOut R Nh t))).const_add (1 + uFin (Nh + 1) (lastOut R Nh t) (zmRaw R (Nh + 1) (lastOut R Nh t).ζ))
    have := (hprod.const_mul ((∏ j ∈ range (Nh + 1), ch R j t) * (detStep R (Nh + 1) (histOut R Nh t).st * Complex.exp (-(lastOut R Nh t).u)))).mul hB
    convert this using 1
    rw [prod_eq_one fun j hj => rh_zero R t j (hρ j (by simp at hj; omega)), xh_zero]
    ring
  have hdR2' : HasDerivAt (fun s => omegaC (Γs R 0 t s) (Zh R 0 t : Alg 2 L N))
      (((∏ j ∈ range (Nh + 1), ch R j t) * (detStep R (Nh + 1) (histOut R Nh t).st * Complex.exp (-(lastOut R Nh t).u))) * ((∑ j ∈ range (Nh + 2), ch₀ R j t * πh R j t / ρh R j t) * (1 + uFin (Nh + 1) (lastOut R Nh t) (zmRaw R (Nh + 1) (lastOut R Nh t).ζ)) +
        (aFin (Nh + 1) (lastOut R Nh t)) * πh R (Nh + 2) t)) 0 :=
    hdR2.congr_of_eventuallyEq (hev.mono fun s hs => hR2 s hs)
  have huniq := hdF.unique hdR2'
  rw [show Suscept.c2 (expLC (Γh R 0 t) (Zh R 0 t : Alg 2 L N)) = -(Fintype.card (Lam 2 L N) : ℂ) *
    -(Suscept.c2 (expLC (Γh R 0 t) (Zh R 0 t : Alg 2 L N)) / Fintype.card (Lam 2 L N)) by field_simp, huniq]
  ring

end

end PtCorr2
