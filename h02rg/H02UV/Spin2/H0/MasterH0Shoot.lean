import Spin2.H0.MasterH0
import Spin2.H0.MasterH0OnePt
import Spin2.Multiscale.RGInH

/-!
# Route (a1), tasks 4–5: shooting on the `h = 0` family and `thm:multiscale` at `h = 0`

**Task 4 (bracketing).** `gFinH0_near`: with `BandOut` at the `h = 0` trajectory `(b, b − m²)` and
at an admissible `(b, μ₀^c)` (both from `GlueD`, the `h = 0` trajectory being windowed),
`|Re ǧ_N(b, b − m²) − Re ǧ_N(b, μ₀^c)| ≤ E + 2C_b(ǧ^0_{N_h})² + 2C_b(ǧ^c_{N_h})²` when
`|ǧ^0_{N_h} − ǧ^c_{N_h}| ≤ E` (`E = 2p_Wc₁` from `H0WindowConcl`). `h0_bracket` (pure IVT) and
**`MasterCore.h0Shoot`**: under the master construction, if the `h = 0` trajectories at `b₁ ≤ b₂`
are windowed (`H0WindowConcl`, i.e. the named inputs at `b₁`, `b₂`) and the admissible shooting
values bracket `y` with these margins, some `b ∈ [b₁, b₂]` has `Re ǧ_N(b, b − m²) = y`.

**Task 5.** **`MasterCore.multiConclD`**: `thm:multiscale` along every windowed trajectory
(`SpinConclD` → `magConcl_ofD` → `multiConcl_ofD`); **`MasterCore.multiscale_h0`**: on the `h = 0`
trajectory (`b = μ₀ + m²`), `TwoPtSq` gives `RGInput` (`rgInput_of_twoPtSq_h0`), hence
`|P_{1/b}[0 ↔ x] − ϑ_j²| ≤ Kϑ_j²/β_j` at fixed `m²`. **`thm_master_h0`**: one master construction
with `H0WindowConcl`, `GlueD` and `MultiConclD`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

/-- **The `h = 0` shooting function near the admissible one.** -/
theorem gFinH0_near {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    {Nh : ℕ} {Cb m b μc E : ℝ}
    (hB0 : BandOut (R.withMsq m) Nh Cb (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
    (hBc : BandOut (R.withMsq m) Nh Cb (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc))
    (hg : |(traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 -
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1| ≤ E) :
    |gFinH0 R Nh m b - gFin (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc)| ≤
      E + 2 * Cb * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ^ 2 +
        2 * Cb * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 ^ 2 := by
  have h1 : |gFin (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) -
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1| ≤
      2 * Cb * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ^ 2 := hB0.gFin_sub
  have h2 : |gFin (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc) -
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1| ≤
      2 * Cb * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 ^ 2 := hBc.gFin_sub
  show |gFin (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) - _| ≤ _
  rw [abs_le] at h1 h2 hg ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, hg.1, hg.2]

/-- **Bracketing** (IVT for the continuous `h = 0` shooting function). -/
theorem h0_bracket {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    {Nh : ℕ} {m : ℝ} (hc : Continuous (gFinH0 R Nh m)) {b₁ b₂ y g₁ g₂ E₁ E₂ : ℝ}
    (hb : b₁ ≤ b₂) (hn1 : |gFinH0 R Nh m b₁ - g₁| ≤ E₁) (hn2 : |gFinH0 R Nh m b₂ - g₂| ≤ E₂)
    (h1 : g₁ + E₁ ≤ y) (h2 : y ≤ g₂ - E₂) : ∃ b ∈ Icc b₁ b₂, gFinH0 R Nh m b = y := by
  rw [abs_le] at hn1 hn2
  exact intermediate_value_Icc hb hc.continuousOn ⟨by linarith [hn1.2], by linarith [hn2.1]⟩

/-- **Task 4 under the master construction: existence of the shooting parameter on the `h = 0`
family.** If at `b₁ ≤ b₂` the `h = 0` trajectories are in `D_ε` with
`|ǧ^0_{N_h}(b_i) − ǧ^c_{N_h}(b_i)| ≤ E_i` around admissible `(b_i, μ_i)` (the conclusion of
`H0WindowConcl` under the named inputs, `E_i = 2p_Wc_i`), and the admissible shooting values bracket
`y` with the margins `E_i + 2C_b((ǧ^0)² + (ǧ^c)²)`, then some `b ∈ [b₁, b₂]` has
`Re ǧ_N(b, b − m²) = y`. -/
theorem MasterCore.h0Shoot {L : ℕ} [NeZero L] (D : MasterCore L) {N : ℕ} (R : RGPar 2 L N)
    [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = D.ℓ)
    (hRA : R.A = D.A) (hRρ : R.ρ = D.ρ) (hN : 2 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) {b₁ b₂ μ₁ μ₂ E₁ E₂ y : ℝ} (hb : b₁ ≤ b₂)
    (ha₁ : Admissible (rgDataM R m) ((L : ℝ) ^ 2) D.κ D.cm D.cT Nh D.ε b₁ μ₁)
    (ha₂ : Admissible (rgDataM R m) ((L : ℝ) ^ 2) D.κ D.cm D.cT Nh D.ε b₂ μ₂)
    (hD₁ : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) D.κ D.cm D.cT D.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b₁ (b₁ - m) j))
    (hD₂ : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) D.κ D.cm D.cT D.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b₂ (b₂ - m) j))
    (hg₁ : |(traj (rgDataM R m) ((L : ℝ) ^ 2) b₁ (b₁ - m) Nh).1 -
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b₁ μ₁ Nh).1| ≤ E₁)
    (hg₂ : |(traj (rgDataM R m) ((L : ℝ) ^ 2) b₂ (b₂ - m) Nh).1 -
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b₂ μ₂ Nh).1| ≤ E₂)
    (h1 : gFin (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b₁ μ₁) +
      (E₁ + 2 * D.Cb * (traj (rgDataM R m) ((L : ℝ) ^ 2) b₁ (b₁ - m) Nh).1 ^ 2 +
        2 * D.Cb * (traj (rgDataM R m) ((L : ℝ) ^ 2) b₁ μ₁ Nh).1 ^ 2) ≤ y)
    (h2 : y ≤ gFin (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b₂ μ₂) -
      (E₂ + 2 * D.Cb * (traj (rgDataM R m) ((L : ℝ) ^ 2) b₂ (b₂ - m) Nh).1 ^ 2 +
        2 * D.Cb * (traj (rgDataM R m) ((L : ℝ) ^ 2) b₂ μ₂ Nh).1 ^ 2)) :
    ∃ b ∈ Icc b₁ b₂, gFinH0 R Nh m b = y := by
  obtain ⟨-, -, hρ, -, -, -, -, -, -, -, -, -, -, hρ8, -, H⟩ := D.hC2
  obtain ⟨-, -, -, -, -, -, -, -, -, hval⟩ := H N R hP hi0 hRℓ hRA hRρ hN Nh hNh
  obtain ⟨CL, aB, -, -, -, -, -, -, hcov, hWH⟩ := D.hWin
  obtain ⟨HH, -⟩ := hWH N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm
  have hc : Continuous (gFinH0 R Nh m) :=
    gFinH0_cont R hm (by omega) (by rw [hRρ]; exact hρ.le) (by rw [hRρ]; exact hρ8)
      (by rw [hP, hRρ]; exact hcov N (by omega)) (hval m hm).1 HH
  have G := fun b μ₀ h => D.hGD N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ h
  exact h0_bracket R hc hb
    (gFinH0_near R (G _ _ hD₁).2 (G _ _ ha₁.1).2 hg₁)
    (gFinH0_near R (G _ _ hD₂).2 (G _ _ ha₂.1).2 hg₂) h1 h2

/-- **`thm:multiscale` along windowed trajectories under the master construction.** -/
theorem MasterCore.multiConclD {L : ℕ} [NeZero L] (D : MasterCore L) :
    MultiConclD L D.ℓ D.A D.ρ D.κ D.cg D.cm D.cT D.ε D.Ke D.KZ D.KG :=
  multiConcl_ofD (by have := D.hL49; omega) D.hε1 D.hSpD
    (magConcl_ofD (by exact_mod_cast (by have := D.hL49; omega : 2 ≤ L)) D.hε1 D.hKZ D.hKG D.hSpD)

/-- **`thm:multiscale` on the `h = 0` trajectory at fixed `m²`** (task 5): if `(b, b − m²)` is in
`D_ε` up to `N_h` (e.g. by `H0WindowConcl`), then (H_λ) and the two-point input `TwoPtSq` give
`RGInput` (`h = 0`: `r = 0`) and `|P_{1/b}[0 ↔ x] − ϑ_j²| ≤ K ϑ_j²/β_j`. -/
theorem MasterCore.multiscale_h0 {L : ℕ} [NeZero L] (D : MasterCore L) {N : ℕ} (R : RGPar 2 L N)
    [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = D.ℓ)
    (hRA : R.A = D.A) (hRρ : R.ρ = D.ρ) {Nh : ℕ} (hNh : Nh + 2 ≤ N) {m : ℝ}
    (hm : m ∈ mRange L N) {b : ℝ} (hb : 0 < b)
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) D.κ D.cm D.cT D.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j))
    (lam : ℕ → ℂ) {Kl KP Kr : ℝ} (hKl : 0 ≤ Kl) (hKP : 0 ≤ KP)
    (hl : HLam R Nh m b (b - m) lam Kl) (hsq : TwoPtSq R Nh m b (b - m) lam KP Kr)
    (x : Lam 2 L N) (hx : x ≠ 0) (hj : Obs.coal L (0 : Lam 2 L N) x ≤ Nh) :
    ∃ jp : ℕ, (jp : ℤ) = jPhys L N (eucl x / (L : ℝ) ^ N) ∧
      jp ≤ Obs.coal L (0 : Lam 2 L N) x ∧ Obs.coal L (0 : Lam 2 L N) x ≤ jp + 1 ∧
      |Pconn L N (1 / b) x - thetaSq R m b (b - m) jp| ≤
        multK L D.cg D.Ke D.KZ D.KG Kl KP * thetaSq R m b (b - m) jp / betaJ R m b (b - m) jp :=
  D.multiConclD N R hP hi0 hRℓ hRA hRρ Nh hNh m hm b (b - m) hD lam Kl KP hKl hKP hl
    (rgInput_of_twoPtSq_h0 R hb hm.1 (by ring) hsq) x hx hj

end

end Spin2
