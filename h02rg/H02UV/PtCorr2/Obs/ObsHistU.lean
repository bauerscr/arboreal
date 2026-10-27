import PtCorr2.Obs.KObsHist
import PtCorr2.Obs.KObsStepU
import Obs2.Pair.CoalHist

/-!
# The `σ_aσ_b` part of the unreduced activity along the history below coalescence

The unreduced history `obsHist R P o₀` (one-point parts present). Below the coalescence scale the
invariant `ObsCoalInv` holds (`obsHist_coalInv_valid`, the induction inside
`Obs2.obsHist_coal_valid`), in particular `K_j(X)_{ab} = 0` on small `X`, so the unreduced step
bound `kobs_raw_stepU` applies at every `j < j_{ab}` (and gives the `ab` part at `j_{ab}`).

* `KObsBoundsU`, `kobs_bounds_U`: the conclusion of `kobs_raw_stepU` as a named property;
* **`kobs_hist_stepU`**: one step along a regular history (`Flow2.Hist.InDh`, a priori bounds as in
  `kobs_hist_step`), `r_j = c_Rg_j`, `ρ_j = r_j/m_j`:
  `ρ_j²A^{(…)}w_{ab}‖K_{j+1}(U)_{ab}‖ ≤ θ₀k_t + C₁((2r_j)³ + 2r_jk_t + k_t²)`,
  `k_t = 8c_xr_j³ + ρ_j8k₁ + ρ_j²8k₂`, from the one-point sizes (`‖V^{obs}_j‖_w ≤ m_j`,
  `‖𝒲^{obs}_j‖_w ≤ r_jm_j`, `A^{(…)}‖K^{obs}_j‖_{(w_a,w_b,0)} ≤ k₁`) and the `ab` size `k₂` at `j`.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

variable {L N : ℕ} [NeZero L]

/-- The conclusion of `kobs_raw_stepU` for given constants. -/
def KObsBoundsU (L : ℕ) [NeZero L] (A C₀ η ε₀ C₁ : ℝ) : Prop :=
    ∀ (N : ℕ) (R : RGPar 2 L N) (j : ℕ), ValidCore R j → ∀ st : RawSt 2 L N, RawInv R j st →
    ∀ (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N), D ∈ BSub (L := L) (N := N) j →
      K ∈ ASub (L := L) (N := N) j → |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1 → 0 ≤ g →
    ∀ ηz : ℝ, ‖st.z / st.Z‖ ≤ ηz → ‖st.y / st.Z‖ ≤ ηz → 2 * ηz ≤ R.ρ →
      8 * cM * R.ℓ ^ 2 * ηz ≤ 1 / 2 →
    ∀ (c : Obs.Case) (P : ObsPts 2 L N) (w : Wt), w.Sub → w.a ≠ ⊤ → w.b ≠ ⊤ → w.ab ≠ ⊤ →
    ∀ o : ObsSt c L N, o.IsObs → ObsLocInv P j o → ObsSymInv j o →
    (∀ X, IsSmall j X → (o.K X : SA c (Lam 2 L N)).ab = 0) →
    ∀ wl dd kb r m k₁ k₂ : ℝ, 0 ≤ wl → 0 ≤ dd → 0 ≤ kb → 0 < r → 0 < m → r ≤ m → 0 ≤ k₁ →
      0 ≤ k₂ →
      Fnorm j (fscale st.Z * R.ℓ) st.Wl ≤ ENNReal.ofReal wl →
      Fnorm j (fscale st.Z * R.ℓ) D ≤ ENNReal.ofReal dd →
      Knorm j (fscale st.Z * R.ℓ) A K ≤ ENNReal.ofReal kb →
      cM * R.ℓ ^ 2 * (2 * |μ| + 2 * ηz) + 8 * R.ℓ ^ 4 * g ≤ r → wl + dd ≤ r ^ 2 →
      2 * r ≤ ε₀ → 8 * kb + r / m * (8 * k₁) + (r / m) ^ 2 * (8 * k₂) ≤ ε₀ →
      (∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo w j (fscale st.Z * R.ℓ) (o.V b) ≤ ENNReal.ofReal m) →
      (∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo w j (fscale st.Z * R.ℓ) (o.W b) ≤ ENNReal.ofReal (r * m)) →
      (∀ X, IsConn j X → ENNReal.ofReal (A ^ (nb j X - 2 ^ 2)) *
        oTo (wOne w) j (fscale st.Z * R.ℓ) (o.K X) ≤ ENNReal.ofReal k₁) →
      (∀ X, IsConn j X → ENNReal.ofReal (A ^ (nb j X - 2 ^ 2)) *
        (w.ab * Tj 2 (L : ℝ) j (fscale st.Z * R.ℓ) (o.K X : SA c (Lam 2 L N)).ab) ≤
          ENNReal.ofReal k₂) →
      ∀ U : Finset (Lam 2 L N), IsConn (j + 1) U →
        ENNReal.ofReal ((r / m) ^ 2) * (ENNReal.ofReal (A ^ (nb (j + 1) U - 2 ^ 2)) *
          (w.ab * Tj 2 (L : ℝ) (j + 1) (fscale (stZ' R st) * R.ℓ)
            ((obsStep R P j st g μ D K o).K U : SA c (Lam 2 L N)).ab)) ≤
        ENNReal.ofReal (C₀ * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3 + (A / 2) ^ (-η)) *
            (8 * kb + r / m * (8 * k₁) + (r / m) ^ 2 * (8 * k₂)) +
          C₁ * ((2 * r) ^ 3 + 2 * r * (8 * kb + r / m * (8 * k₁) + (r / m) ^ 2 * (8 * k₂)) +
            (8 * kb + r / m * (8 * k₁) + (r / m) ^ 2 * (8 * k₂)) ^ 2))

/-- **The constants of the unreduced `ab` step.** -/
theorem kobs_bounds_U : ∃ (C₀ η : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧ 0 < η ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧ KObsBoundsU L A C₀ η ε₀ C₁ :=
  kobs_raw_stepU

/-- **The real inequality of one `ab` step**: with `ρ = r/m`, `k₁ ≤ c₁r²m`,
`k_t = 8c_xr³ + 8ρk₁ + 8ρ²k₂ ≤ 1`, `r ≤ 1`, the step right side is
`≤ ρ²(θ'k₂ + B₂rm²)`, `θ' = 8θ₀ + 16C₁r + 8C₁k_t`, `B₂ = 8θ₀(c_x+c₁) + 8C₁ + 24C₁(c_x+c₁)`. -/
theorem kab_real {r m k₁ k₂ θ₀ C₁ cx c₁ : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (hm : 0 < m)
    (hk₁0 : 0 ≤ k₁) (hk₂ : 0 ≤ k₂) (hθ₀ : 0 ≤ θ₀) (hC₁ : 0 ≤ C₁) (hcx : 0 ≤ cx) (hc₁ : 0 ≤ c₁)
    (hk₁ : k₁ ≤ c₁ * r ^ 2 * m)
    (hkt1 : 8 * cx * r ^ 3 + r / m * (8 * k₁) + (r / m) ^ 2 * (8 * k₂) ≤ 1) :
    θ₀ * (8 * cx * r ^ 3 + r / m * (8 * k₁) + (r / m) ^ 2 * (8 * k₂)) +
        C₁ * ((2 * r) ^ 3 + 2 * r * (8 * cx * r ^ 3 + r / m * (8 * k₁) + (r / m) ^ 2 * (8 * k₂)) +
          (8 * cx * r ^ 3 + r / m * (8 * k₁) + (r / m) ^ 2 * (8 * k₂)) ^ 2) ≤
      (r / m) ^ 2 * ((8 * θ₀ + 16 * C₁ * r +
          8 * C₁ * (8 * cx * r ^ 3 + r / m * (8 * k₁) + (r / m) ^ 2 * (8 * k₂))) * k₂ +
        (8 * θ₀ * (cx + c₁) + 8 * C₁ + 24 * C₁ * (cx + c₁)) * r * m ^ 2) := by
  set ρ := r / m with hρ
  set kt := 8 * cx * r ^ 3 + ρ * (8 * k₁) + ρ ^ 2 * (8 * k₂) with hkt
  have hρ0 : 0 ≤ ρ := by positivity
  have hρk : ρ * k₁ ≤ c₁ * r ^ 3 := by
    rw [hρ, div_mul_eq_mul_div, div_le_iff₀ hm]
    calc r * k₁ ≤ r * (c₁ * r ^ 2 * m) := mul_le_mul_of_nonneg_left hk₁ hr0.le
      _ = c₁ * r ^ 3 * m := by ring
  have hr3 : r ^ 3 = ρ ^ 2 * (r * m ^ 2) := by rw [hρ]; field_simp
  have hr4 : r ^ 4 ≤ r ^ 3 := pow_le_pow_of_le_one hr0.le hr1 (by norm_num)
  have hkt0 : 0 ≤ kt := by positivity
  have hA : kt ≤ 8 * (cx + c₁) * r ^ 3 + ρ ^ 2 * (8 * k₂) := by
    rw [hkt]; nlinarith
  -- termwise
  have t1 : θ₀ * kt ≤ 8 * θ₀ * (cx + c₁) * r ^ 3 + ρ ^ 2 * (8 * θ₀ * k₂) := by
    have := mul_le_mul_of_nonneg_left hA hθ₀; nlinarith
  have t2 : C₁ * (2 * r * kt) ≤ 16 * C₁ * (cx + c₁) * r ^ 3 + ρ ^ 2 * (16 * C₁ * r * k₂) := by
    have h := mul_le_mul_of_nonneg_left hA (by positivity : 0 ≤ C₁ * (2 * r))
    have h2 : C₁ * (2 * r) * (8 * (cx + c₁) * r ^ 3) ≤ 16 * C₁ * (cx + c₁) * r ^ 3 := by
      have : C₁ * (2 * r) * (8 * (cx + c₁) * r ^ 3) = 16 * C₁ * (cx + c₁) * r ^ 4 := by ring
      rw [this]; exact mul_le_mul_of_nonneg_left hr4 (by positivity)
    nlinarith
  have t3 : C₁ * kt ^ 2 ≤ 8 * C₁ * (cx + c₁) * r ^ 3 + ρ ^ 2 * (8 * C₁ * kt * k₂) := by
    have h := mul_le_mul_of_nonneg_left hA (by positivity : 0 ≤ C₁ * kt)
    have h2 : C₁ * kt * (8 * (cx + c₁) * r ^ 3) ≤ 8 * C₁ * (cx + c₁) * r ^ 3 := by
      have : C₁ * kt * (8 * (cx + c₁) * r ^ 3) = (8 * C₁ * (cx + c₁) * r ^ 3) * kt := by ring
      rw [this]; exact mul_le_of_le_one_right (by positivity) hkt1
    nlinarith
  have e : C₁ * ((2 * r) ^ 3 + 2 * r * kt + kt ^ 2) =
      8 * C₁ * r ^ 3 + C₁ * (2 * r * kt) + C₁ * kt ^ 2 := by ring
  rw [e]
  have goal : 8 * θ₀ * (cx + c₁) * r ^ 3 + ρ ^ 2 * (8 * θ₀ * k₂) + (8 * C₁ * r ^ 3 +
      (16 * C₁ * (cx + c₁) * r ^ 3 + ρ ^ 2 * (16 * C₁ * r * k₂)) +
      (8 * C₁ * (cx + c₁) * r ^ 3 + ρ ^ 2 * (8 * C₁ * kt * k₂))) =
      ρ ^ 2 * ((8 * θ₀ + 16 * C₁ * r + 8 * C₁ * kt) * k₂ +
        (8 * θ₀ * (cx + c₁) + 8 * C₁ + 24 * C₁ * (cx + c₁)) * r * m ^ 2) := by
    rw [show (8 * θ₀ * (cx + c₁) + 8 * C₁ + 24 * C₁ * (cx + c₁)) * r * m ^ 2 =
      (8 * θ₀ * (cx + c₁) + 8 * C₁ + 24 * C₁ * (cx + c₁)) * (r * m ^ 2) by ring]
    have : ρ ^ 2 * ((8 * θ₀ * (cx + c₁) + 8 * C₁ + 24 * C₁ * (cx + c₁)) * (r * m ^ 2)) =
        (8 * θ₀ * (cx + c₁) + 8 * C₁ + 24 * C₁ * (cx + c₁)) * r ^ 3 := by rw [hr3]; ring
    linear_combination (-1 : ℝ) * this
  linarith

section Hist

variable {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

/-- **The coalescence invariant along the history** below `j_{ab}`. -/
theorem obsHist_coalInv_valid {c : Obs.Case} (P : ObsPts 2 L N) (o₀ : ObsSt c L N)
    (h₀ : o₀.IsObs) (hinv₀ : ObsCoalInv P 0 o₀)
    (hL : 2 ^ (2 + 3) + 8 * 2 < L) (hρ : 0 ≤ R.ρ)
    (hV : ∀ k < coal L P.a P.b, ValidAt R k) (t : Flow2.Hist.Seq (Xs R)) :
    ∀ j < coal L P.a P.b, ObsCoalInv P j (obsHist R P o₀ j t) := by
  intro j
  induction j with
  | zero => intro _; exact hinv₀
  | succ k ih =>
    intro hk
    rw [obsHist_succ]
    have hVk := hV k (by omega)
    have hI := rawInv_hist R hρ k (fun i hi => hV i (by omega)) t
    exact obsStep_coalInv R P k _ _ _ _ _ (ih (by omega))
      (obsHist_isObs R P o₀ h₀ k t) hL (by have := hVk.1; omega)
      (fun x y hxy => (RawInv.cov hVk hI).1.range (by have := hVk.1; omega) x y hxy)
      (pow_le_of_lt_coal hk)

set_option maxHeartbeats 4000000 in
/-- **One step of the unreduced `ab` recursion along the history.** -/
theorem kobs_hist_stepU {C₀ η ε₀ C₁ : ℝ} (hKB : KObsBoundsU L R.A C₀ η ε₀ C₁) (hC₀ : 0 ≤ C₀)
    (hC₁ : 0 ≤ C₁)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    {c : Obs.Case} (P : ObsPts 2 L N) (w : Wt) (hw : w.Sub) (hwa : w.a ≠ ⊤) (hwb : w.b ≠ ⊤)
    (hwab : w.ab ≠ ⊤)
    (o₀ : ObsSt c L N) (h0 : o₀.IsObs) (hl0 : ObsLocInv P 0 o₀) (hs0 : ObsSymInv 0 o₀)
    (t : Flow2.Hist.Seq (Xs R)) (j : ℕ) (hj : j < Nh)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t)
    (hKs : ∀ X, IsSmall j X → ((obsHist R P o₀ j t).K X : SA c (Lam 2 L N)).ab = 0)
    (m k₁ k₂ : ℝ) (hm0 : 0 < m) (hk₁ : 0 ≤ k₁) (hk₂ : 0 ≤ k₂)
    (hrm : cR R Λ cm C₂ * (t j).1 ≤ m)
    (hεε : 2 * (cR R Λ cm C₂ * ε) ≤ ε₀)
    (hkt : 8 * cx κ cT * (cR R Λ cm C₂ * (t j).1) ^ 3 +
      cR R Λ cm C₂ * (t j).1 / m * (8 * k₁) + (cR R Λ cm C₂ * (t j).1 / m) ^ 2 * (8 * k₂) ≤ ε₀)
    (hVo : ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (histS R j t) ((obsHist R P o₀ j t).V b) ≤ ENNReal.ofReal m)
    (hWo : ∀ b ∈ blockIdx (L := L) (N := N) j, oTo w j (histS R j t) ((obsHist R P o₀ j t).W b) ≤
      ENNReal.ofReal (cR R Λ cm C₂ * (t j).1 * m))
    (hK1 : ∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
      oTo (wOne w) j (histS R j t) ((obsHist R P o₀ j t).K X) ≤ ENNReal.ofReal k₁)
    (hK2 : ∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
      (w.ab * Tj 2 (L : ℝ) j (histS R j t) ((obsHist R P o₀ j t).K X : SA c (Lam 2 L N)).ab) ≤
        ENNReal.ofReal k₂) :
    let r := cR R Λ cm C₂ * (t j).1
    let kt := 8 * cx κ cT * r ^ 3 + r / m * (8 * k₁) + (r / m) ^ 2 * (8 * k₂)
    ∀ U : Finset (Lam 2 L N), IsConn (j + 1) U →
      ENNReal.ofReal ((r / m) ^ 2) * (ENNReal.ofReal (R.A ^ (nb (j + 1) U - 2 ^ 2)) *
        (w.ab * Tj 2 (L : ℝ) (j + 1) (histS R (j + 1) t)
          ((obsHist R P o₀ (j + 1) t).K U : SA c (Lam 2 L N)).ab)) ≤
      ENNReal.ofReal (kθ0 L R.A C₀ η * kt + C₁ * ((2 * r) ^ 3 + 2 * r * kt + kt ^ 2)) := by
  intro r0 kt0 U hU
  have hℓ : 0 < R.ℓ := Fact.out
  have hVj := hV j hj
  have hρ1 : R.ρ < 1 := by linarith [hVj.2.2.2.2.1]
  have HI := rawInv_hist R hVj.2.2.2.1 j (fun i hi => hV i (by omega)) t
  set st := rawHist R j t with hst
  have hZ : st.Z ≠ 0 := HI.Z_ne_zero hρ1
  obtain ⟨hz, hy, hWl⟩ := apriori R hSB hV hm hβ hδ1 H j hj.le t ht
  obtain ⟨hg, hgε, hμ, hx⟩ := ht.1 j le_rfl
  set g := (t j).1 with hgdef
  set μ := (t j).2.1
  set x := (t j).2.2
  have hcz : 0 ≤ cZ R := by unfold cZ; positivity
  have hcv : 0 ≤ cV R Λ cm := by unfold cV; have := H.hcmu; positivity
  have hcw : 0 ≤ cW R Λ cm C₂ := by unfold cW; have := H.hC₂; positivity
  have hg1 : g ≤ 1 := hgε.trans H.hε1
  have hx1 : ‖x.1‖ ≤ cx κ cT * g ^ 3 := (norm_fst_le x).trans hx
  have hx2 : ‖x.2‖ ≤ cx κ cT * g ^ 3 := (norm_snd_le x).trans hx
  have hg3 : g ^ 3 ≤ ε * g ^ 2 := by
    rw [pow_succ]; nlinarith [sq_nonneg g, mul_le_mul_of_nonneg_left hgε (sq_nonneg g)]
  have hv : cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g ≤ cV R Λ cm * g := by
    unfold cV
    have hM : 0 ≤ cM := Nat.cast_nonneg _
    have : 2 * |μ| + 2 * (cZ R * g) ≤ (2 * cmu Λ cm + 2 * cZ R) * g := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hM (sq_nonneg R.ℓ))]
  set r := cR R Λ cm C₂ * g with hr
  have hvr : cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g ≤ r := by
    refine hv.trans ?_; rw [hr]; unfold cR; nlinarith
  have hwr : cW R Λ cm C₂ * g ^ 2 + ‖x.1‖ ≤ r ^ 2 := by
    rw [hr]; unfold cR
    have h1 : cW R Λ cm C₂ + 1 ≤ (cV R Λ cm + cW R Λ cm C₂ + 2) ^ 2 := by nlinarith
    have := H.h3
    nlinarith [sq_nonneg g, mul_le_mul_of_nonneg_left hg3 H.hcx]
  have hη : 2 * (cZ R * g) ≤ R.ρ := by
    have := H.h1; nlinarith [mul_le_mul_of_nonneg_left hgε hcz]
  have hηs : 8 * cM * R.ℓ ^ 2 * (cZ R * g) ≤ 1 / 2 := by
    have := H.h2
    have hM : 0 ≤ cM := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hgε (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num :
      (0:ℝ) ≤ 8) hM) (sq_nonneg R.ℓ)) hcz)]
  have hcR1 : 1 ≤ cR R Λ cm C₂ := by unfold cR; linarith
  have hgr : g ≤ r := by rw [hr]; nlinarith
  have hr0 : 0 < r := by rw [hr]; positivity
  have hrε : r ≤ cR R Λ cm C₂ * ε := mul_le_mul_of_nonneg_left hgε (by linarith)
  have hcx := H.hcx
  have hbr : 8 * ‖x.2‖ ≤ 8 * cx κ cT * r ^ 3 := by
    have : g ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ hg.le hgr 3
    nlinarith [mul_le_mul_of_nonneg_left this hcx]
  set ktr := 8 * ‖x.2‖ + r / m * (8 * k₁) + (r / m) ^ 2 * (8 * k₂) with hktr
  have hkt' : ktr ≤ kt0 := by
    show 8 * ‖x.2‖ + r / m * (8 * k₁) + (r / m) ^ 2 * (8 * k₂) ≤
      8 * cx κ cT * r ^ 3 + r / m * (8 * k₁) + (r / m) ^ 2 * (8 * k₂)
    linarith
  have hktr0 : 0 ≤ ktr := by positivity
  -- the observable invariants
  have hval := hist_valid R hV t (n := j + 1) (by omega)
  have hloc := obsLocInv_hist R P o₀ hl0 t j fun i hi => hval i (by omega)
  have hsym := obsSymInv_hist R P o₀ hs0 t j fun i hi => hval i (by omega)
  have hobs := obsHist_isObs R P o₀ h0 j t
  have key := hKB N R j hVj.toValidCore st HI g μ _ _ (rawD_mem R _ _) (rawK_mem R _ _) (hm j hj)
    hg.le (cZ R * g) hz hy hη hηs c P w hw hwa hwb hwab (obsHist R P o₀ j t) hobs hloc hsym hKs
    (cW R Λ cm C₂ * g ^ 2) ‖x.1‖ ‖x.2‖ r m k₁ k₂ (by positivity) (norm_nonneg _)
    (norm_nonneg _) hr0 hm0 hrm hk₁ hk₂ hWl (le_of_eq (Fnorm_rawD R HI.hu hZ x))
    (le_of_eq (Knorm_rawK R HI.hu hZ x)) hvr hwr (by linarith) (hkt'.trans hkt) hVo hWo hK1 hK2 U hU
  rw [obsHist_succ]
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  have hA0 : (0 : ℝ) ≤ R.A / 2 := by have : 0 < R.A := Fact.out; positivity
  have hθ : 0 ≤ C₀ * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3 + (R.A / 2) ^ (-η)) := by
    have := Real.rpow_nonneg hA0 (-η); positivity
  have h1 : C₀ * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3 + (R.A / 2) ^ (-η)) * ktr ≤ kθ0 L R.A C₀ η * kt0 :=
    mul_le_mul_of_nonneg_left hkt' hθ
  have h2 : (2 * r) ^ 3 + 2 * r * ktr + ktr ^ 2 ≤ (2 * r) ^ 3 + 2 * r * kt0 + kt0 ^ 2 := by
    have : 2 * r * ktr ≤ 2 * r * kt0 := mul_le_mul_of_nonneg_left hkt' (by linarith)
    have : ktr ^ 2 ≤ kt0 ^ 2 := pow_le_pow_left₀ hktr0 hkt' 2
    linarith
  have h3 := mul_le_mul_of_nonneg_left h2 hC₁
  linarith

/-- The source constant of the `ab` recursion. -/
def kB2 (θ₀ C₁ cx c₁ : ℝ) : ℝ := 8 * θ₀ * (cx + c₁) + 8 * C₁ + 24 * C₁ * (cx + c₁)

set_option maxHeartbeats 4000000 in
/-- **The `ab` part of the unreduced activity along the history**: `K_0^{ab} = 0` and the
one-point sizes `m_j`, `k₁_j ≤ c₁r_j²m_j` give, for `j ≤ n` (`n ≤ j_{ab}`),
`A^{(|𝓑_j(X)|-4)_+}w_{ab}‖K_j(X)_{ab}‖ ≤ c₂r_jm_j²`, `c₂ = 10B₂`. -/
theorem kab_hist {C₀ η ε₀ C₁ : ℝ} (hKB : KObsBoundsU L R.A C₀ η ε₀ C₁) (hC₀ : 0 ≤ C₀)
    (hC₁ : 0 ≤ C₁)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    {c : Obs.Case} (P : ObsPts 2 L N) (w : Wt) (hw : w.Sub) (hwa : w.a ≠ ⊤) (hwb : w.b ≠ ⊤)
    (hwab : w.ab ≠ ⊤)
    (o₀ : ObsSt c L N) (h0 : o₀.IsObs) (hl0 : ObsLocInv P 0 o₀) (hs0 : ObsSymInv 0 o₀)
    (t : Flow2.Hist.Seq (Xs R)) (hK0 : ∀ X, (o₀.K X : SA c (Lam 2 L N)).ab = 0)
    (n : ℕ) (hn : n ≤ Nh) (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε n t)
    (hKs : ∀ j < n, ∀ X, IsSmall j X → ((obsHist R P o₀ j t).K X : SA c (Lam 2 L N)).ab = 0)
    (m k₁ : ℕ → ℝ) (c₁ : ℝ) (hc₁ : 0 ≤ c₁) (hm0 : ∀ j, 0 < m j)
    (hmm : ∀ j < n, m j ≤ 2 * m (j + 1)) (hk₁0 : ∀ j, 0 ≤ k₁ j)
    (hk₁ : ∀ j < n, k₁ j ≤ c₁ * (cR R Λ cm C₂ * (t j).1) ^ 2 * m j)
    (hrm : ∀ j < n, cR R Λ cm C₂ * (t j).1 ≤ m j)
    (hε1 : cR R Λ cm C₂ * ε ≤ 1) (hεε : 2 * (cR R Λ cm C₂ * ε) ≤ ε₀)
    (hkt1 : 8 * (cx κ cT + c₁ + 10 * kB2 (kθ0 L R.A C₀ η) C₁ (cx κ cT) c₁) *
      (cR R Λ cm C₂ * ε) ^ 3 ≤ 1)
    (hktε : 8 * (cx κ cT + c₁ + 10 * kB2 (kθ0 L R.A C₀ η) C₁ (cx κ cT) c₁) *
      (cR R Λ cm C₂ * ε) ^ 3 ≤ ε₀)
    (hθ' : 8 * kθ0 L R.A C₀ η + 16 * C₁ * (cR R Λ cm C₂ * ε) +
      8 * C₁ * (8 * (cx κ cT + c₁ + 10 * kB2 (kθ0 L R.A C₀ η) C₁ (cx κ cT) c₁) *
        (cR R Λ cm C₂ * ε) ^ 3) ≤ 1 / 10)
    (hVo : ∀ j < n, ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (histS R j t) ((obsHist R P o₀ j t).V b) ≤ ENNReal.ofReal (m j))
    (hWo : ∀ j < n, ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (histS R j t) ((obsHist R P o₀ j t).W b) ≤
        ENNReal.ofReal (cR R Λ cm C₂ * (t j).1 * m j))
    (hK1 : ∀ j < n, ∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
      oTo (wOne w) j (histS R j t) ((obsHist R P o₀ j t).K X) ≤ ENNReal.ofReal (k₁ j)) :
    ∀ j ≤ n, ∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
      (w.ab * Tj 2 (L : ℝ) j (histS R j t) ((obsHist R P o₀ j t).K X : SA c (Lam 2 L N)).ab) ≤
        ENNReal.ofReal (10 * kB2 (kθ0 L R.A C₀ η) C₁ (cx κ cT) c₁ *
          (cR R Λ cm C₂ * (t j).1) * m j ^ 2) := by
  set B₂ := kB2 (kθ0 L R.A C₀ η) C₁ (cx κ cT) c₁ with hB₂
  set c₂ := 10 * B₂ with hc₂
  have hcx := H.hcx
  have hA0 : (0 : ℝ) ≤ R.A / 2 := by have : 0 < R.A := Fact.out; positivity
  have hθ0 : 0 ≤ kθ0 L R.A C₀ η := by
    unfold kθ0; have := Real.rpow_nonneg hA0 (-η); positivity
  have hB0 : 0 ≤ B₂ := by rw [hB₂]; unfold kB2; positivity
  have hcR : 0 ≤ cR R Λ cm C₂ := by
    unfold cR cV cW cZ; have := H.hcmu; have := H.hC₂; positivity
  have hDh : ∀ j ≤ n, Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t := fun j hj =>
    ⟨fun i hi => ht.1 i (by omega), fun i hi => ht.2 i (by omega)⟩
  intro j
  induction j with
  | zero =>
    intro _ X _
    show _ * (w.ab * Tj 2 (L : ℝ) 0 (histS R 0 t) (o₀.K X : SA c (Lam 2 L N)).ab) ≤ _
    rw [hK0 X, Step.Tj_zero, mul_zero, mul_zero]
    exact zero_le
  | succ j ih =>
    intro hj X hX
    have hjn : j < n := by omega
    have ih := ih hjn.le
    set r := cR R Λ cm C₂ * (t j).1 with hr
    have hg := (ht.1 j hjn.le)
    have hcv : 0 ≤ cV R Λ cm := by unfold cV cZ; have := H.hcmu; positivity
    have hcw : 0 ≤ cW R Λ cm C₂ := by unfold cW; have := H.hC₂; positivity
    have hcR1 : 1 ≤ cR R Λ cm C₂ := by unfold cR; linarith
    have hr0 : 0 < r := by rw [hr]; have := hg.1; nlinarith
    have hrε : r ≤ cR R Λ cm C₂ * ε := mul_le_mul_of_nonneg_left hg.2.1 hcR
    have hr1 : r ≤ 1 := hrε.trans hε1
    have hmj := hm0 j
    have hk₂0 : 0 ≤ c₂ * r * m j ^ 2 := by positivity
    have hρk : r / m j * k₁ j ≤ c₁ * r ^ 3 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hmj]
      calc r * k₁ j ≤ r * (c₁ * r ^ 2 * m j) := mul_le_mul_of_nonneg_left (hk₁ j hjn) hr0.le
        _ = c₁ * r ^ 3 * m j := by ring
    have hρ2 : (r / m j) ^ 2 * (c₂ * r * m j ^ 2) = c₂ * r ^ 3 := by field_simp
    have hr3 : r ^ 3 ≤ (cR R Λ cm C₂ * ε) ^ 3 := pow_le_pow_left₀ hr0.le hrε 3
    set kt := 8 * cx κ cT * r ^ 3 + r / m j * (8 * k₁ j) + (r / m j) ^ 2 * (8 * (c₂ * r * m j ^ 2))
      with hkt
    have hktb : kt ≤ 8 * (cx κ cT + c₁ + c₂) * (cR R Λ cm C₂ * ε) ^ 3 := by
      have e : kt = 8 * cx κ cT * r ^ 3 + 8 * (r / m j * k₁ j) + 8 * ((r / m j) ^ 2 * (c₂ * r * m j ^ 2)) := by
        rw [hkt]; ring
      rw [e, hρ2]
      have : 8 * (cx κ cT + c₁ + c₂) * r ^ 3 ≤ 8 * (cx κ cT + c₁ + c₂) * (cR R Λ cm C₂ * ε) ^ 3 :=
        mul_le_mul_of_nonneg_left hr3 (by positivity)
      nlinarith
    have hstep := kobs_hist_stepU R hKB hC₀ hC₁ hSB hV hm hβ hδ1 H P w hw hwa hwb hwab o₀ h0 hl0 hs0 t j
      (by omega) (hDh j hjn.le) (hKs j hjn) (m j) (k₁ j) (c₂ * r * m j ^ 2) hmj (hk₁0 j) hk₂0
      (hrm j hjn) hεε (hktb.trans hktε) (hVo j hjn) (hWo j hjn) (hK1 j hjn) ih X hX
    have hreal := kab_real (θ₀ := kθ0 L R.A C₀ η) (C₁ := C₁) (cx := cx κ cT) (c₁ := c₁) hr0 hr1 hmj
      (hk₁0 j) hk₂0 hθ0 hC₁ hcx hc₁ (hk₁ j hjn) (hktb.trans hkt1)
    have hρ0 : 0 < (r / m j) ^ 2 := by positivity
    set Z := (8 * kθ0 L R.A C₀ η + 16 * C₁ * r + 8 * C₁ * kt) * (c₂ * r * m j ^ 2) +
      B₂ * r * m j ^ 2 with hZ
    have hY : ENNReal.ofReal (R.A ^ (nb (j + 1) X - 2 ^ 2)) *
        (w.ab * Tj 2 (L : ℝ) (j + 1) (histS R (j + 1) t)
          ((obsHist R P o₀ (j + 1) t).K X : SA c (Lam 2 L N)).ab) ≤ ENNReal.ofReal Z := by
      have h1 : ENNReal.ofReal ((r / m j) ^ 2) * (ENNReal.ofReal (R.A ^ (nb (j + 1) X - 2 ^ 2)) *
          (w.ab * Tj 2 (L : ℝ) (j + 1) (histS R (j + 1) t)
            ((obsHist R P o₀ (j + 1) t).K X : SA c (Lam 2 L N)).ab)) ≤
          ENNReal.ofReal ((r / m j) ^ 2) * ENNReal.ofReal Z := by
        refine hstep.trans ?_
        rw [← ENNReal.ofReal_mul hρ0.le]
        exact ENNReal.ofReal_le_ofReal hreal
      exact (ENNReal.mul_le_mul_iff_right (ne_of_gt (ENNReal.ofReal_pos.2 hρ0)) ENNReal.ofReal_ne_top).1 h1
    refine hY.trans (ENNReal.ofReal_le_ofReal ?_)
    -- `Z ≤ (c₂/5) r m² ≤ c₂ r' m'²`
    have hθt : 8 * kθ0 L R.A C₀ η + 16 * C₁ * r + 8 * C₁ * kt ≤ 1 / 10 := by
      have a1 : 16 * C₁ * r ≤ 16 * C₁ * (cR R Λ cm C₂ * ε) :=
        mul_le_mul_of_nonneg_left hrε (by positivity)
      have a2 : 8 * C₁ * kt ≤ 8 * C₁ * (8 * (cx κ cT + c₁ + c₂) * (cR R Λ cm C₂ * ε) ^ 3) :=
        mul_le_mul_of_nonneg_left hktb (by positivity)
      linarith
    have hZ1 : Z ≤ c₂ / 5 * (r * m j ^ 2) := by
      have := mul_le_mul_of_nonneg_right hθt hk₂0
      rw [hZ]
      have e : B₂ * r * m j ^ 2 = c₂ / 10 * (r * m j ^ 2) := by rw [hc₂]; ring
      rw [e]
      nlinarith
    have hr' : 5 / 6 * (t j).1 ≤ (t (j + 1)).1 :=
      g_succ_ge (hDh (j + 1) hj) hβ hδ1 H.hcg H.hε1 H.h6
    have hrr : r ≤ 6 / 5 * (cR R Λ cm C₂ * (t (j + 1)).1) := by
      rw [hr]; nlinarith
    have hmm' : m j ^ 2 ≤ 4 * m (j + 1) ^ 2 := by
      have := hmm j hjn
      nlinarith
    have hprod : r * m j ^ 2 ≤ 24 / 5 * ((cR R Λ cm C₂ * (t (j + 1)).1) * m (j + 1) ^ 2) := by
      have hr'0 : 0 ≤ cR R Λ cm C₂ * (t (j + 1)).1 := by linarith
      calc r * m j ^ 2 ≤ (6 / 5 * (cR R Λ cm C₂ * (t (j + 1)).1)) * (4 * m (j + 1) ^ 2) :=
            mul_le_mul hrr hmm' (sq_nonneg _) (by positivity)
        _ = 24 / 5 * ((cR R Λ cm C₂ * (t (j + 1)).1) * m (j + 1) ^ 2) := by ring
    have hc20 : 0 ≤ c₂ := by positivity
    calc Z ≤ c₂ / 5 * (r * m j ^ 2) := hZ1
      _ ≤ c₂ / 5 * (24 / 5 * ((cR R Λ cm C₂ * (t (j + 1)).1) * m (j + 1) ^ 2)) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
      _ ≤ c₂ * (cR R Λ cm C₂ * (t (j + 1)).1) * m (j + 1) ^ 2 := by
          have : 0 ≤ c₂ * ((cR R Λ cm C₂ * (t (j + 1)).1) * m (j + 1) ^ 2) := by
            have : 0 ≤ (t (j + 1)).1 := (ht.1 (j + 1) hj).1.le
            positivity
          nlinarith

end Hist

end

end PtCorr2
