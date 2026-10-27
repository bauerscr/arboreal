import Spin2.Multiscale.ZBelow
import PtCorr2.Pair.PairAbove

/-!
# `PairAboveW1`: the pair part above coalescence, reduced to the Pauli-adjusted pair couplings

Pair observable `z̃_0z̃_x` (`zV b`, `ptsX x`), trajectory `t` at mass `m²`, coalescence scale
`j = j_x`. Split `Π^{≥j} = ω_{Γ_j}(Z_j)` (`zOm`) into the **constants** `X = ∏_{j≤i≤N_h} chO_i ·
det·e^{-u_N}` (`zCst`) and the **zero-mode integral** `Ω = ω_{cQ}(F_N)` of the final object
(`zZm`, `F_N = zFin`, `c = t_raw/|Λ| = zCc`): `zHi_eq`, `Π^{≥j} = XΩ`.

Exact (`pair_E_split`, `zCst_coup`): with `γ_{•,k} = -ε(u^{obs}_{k,•})` (`uA`, `uB`),
`q_k = -ε(u^{obs}_{k,ab})` (`zq`), and the scale-`N` constants `γ_{•,N}`, `q_N` (including `u_N` of
the last step: `gamNa`, `gamNb`, `qN`):

* `E = n_{ab}X + [n_{ab}Ω + n_aX·n_bΩ + n_bX·n_aΩ]`;
* `n_aX = γ_{a,N} - γ_{a,j}`, `n_bX = γ_{b,N} - γ_{b,j}`,
  `n_{ab}X = (q_N - q_j) + (γ_{a,N} - γ_{a,j})(γ_{b,N} - γ_{b,j})` (Pauli-adjusted accumulated
  pair constant);
* one-point closure (the Ward/one-point relation `⟨z̃_0⟩ = r`): `n_aΩ = r - γ_{a,N}`,
  `r = 1 - b⟨ψ̄_0ψ_0⟩`.

The bracket is the zero-mode term. By `zm_pauli_elim` the zero-mode constant `c ≈ t/|Λ|` (of size
`(m²|Λ|)^{-1}`) enters only through `n_aΩ = r - γ_{a,N}`, once the Pauli-adjusted pair coupling of
`F_N` is measured relative to its `a`-vertex.

Named inputs (open analysis), exactly (for `x ≠ 0`, `1 ≤ j_x ≤ N_h`, `M = M_{j_x}`, `ǧ = ǧ_{j_x}`):
* **`PairCstRel K₁`**: `‖n_{ab}X‖ ≤ K₁‖M‖²ǧ`, i.e.
  `|(q_N - q_j) + (γ_{a,N} - γ_{a,j})(γ_{b,N} - γ_{b,j})| ≤ K₁‖M‖²ǧ` (Pauli: in the merged picture
  the increments are `C_i(a,a)·r̃_i`, `r̃` the Pauli-adjusted pair coupling, `r̃_j = 0`);
* **`PairZeroRel K₂ K₃`**: `∃ρ̃`, `c2F_{ab} + n_aX·c2F_b + n_bX·c2F_a = ρ̃·c2F_a`, `‖ρ̃‖ ≤ K₃‖M‖ǧ`,
  `‖εF_{ab} + n_aX·εF_b + n_bX·εF_a - ρ̃εF_a‖ ≤ K₂‖M‖²ǧ‖sE Ω‖` (the relative Pauli-adjusted pair
  coupling and the constant part of the final object);
* **`GamTopBd K₄`**: `‖γ_{a,N}‖ ≤ K₄‖M‖`.

**`pairAboveW1_of_parts`**: these, `‖M_k‖ ≤ M_b` and `0 ≤ ǧ ≤ 1` give `PairAboveW1` with
`K_E = K₁ + K₂ + K₃K₄`, `K_R = K₃M_b`; **`pairAboveW1_of_parts_flow`** along the admissible
trajectories (`FlowC2Concl`).
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

variable {L N : ℕ} [NeZero L]

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- The `u^{obs}`-increment `u_N - u_{N-1}` of the last step (pair history). -/
def zUN (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) : Obs.OE .two (Lam 2 L N) :=
  Obs2.uXO (ptsX x) (Nh + 1)
    (LastN.stCovN (R.withMsq m) (Nh + 1)
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st)
    (Obs2.fullV (R.withMsq m) (Nh + 1)
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).g.re
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).nu.re
      (Obs2.obsHist (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) (Nh + 1)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
    (Obs2.fullW (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).D
      (Obs2.obsHist (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) (Nh + 1)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
    (Obs2.fullK (R.withMsq m) (Nh + 1)
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).K
      (Obs2.obsHist (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) (Nh + 1)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
    univ

/-- The constant factor `det(1 + aAΓ_{N-1})·e^{-u_N}` of the last step (pair history). -/
def zUo (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) : Obs.OE .two (Lam 2 L N) :=
  PtCorr2.detStep (R.withMsq m) (Nh + 1)
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st •
    PtCorr2.uOutNO (R.withMsq m) (ptsX x) (Nh + 1)
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).g.re
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).nu.re
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).D
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).K
      (Obs2.obsHist (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) (Nh + 1)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))

/-- The constants of `Π^{≥k}`: `X = ∏_{k ≤ i ≤ N_h} chO_i · det·e^{-u_N}`. -/
def zCst (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) (k : ℕ) : Obs.OE .two (Lam 2 L N) :=
  (∏ i ∈ Ico k (Nh + 1), PtCorr2.chO (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) i
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) * zUo R Nh m b μ₀ x

/-- The final object `F_N` (after the nonzero modes of the last step), pair history. -/
def zFin (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) : Obs.OE .two (Lam 2 L N) :=
  PtCorr2.finO (R.withMsq m) (ptsX x) (Nh + 1)
    (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st
    (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).g.re
    (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).nu.re
    (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).D
    (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).K
    (Obs2.obsHist (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) (Nh + 1)
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))

/-- The zero-mode constant `c = t_raw/|Λ|`. -/
def zCc (Nh : ℕ) (m b μ₀ : ℝ) : ℂ :=
  PtCorr2.zmRaw (R.withMsq m) (Nh + 1)
    (Function.update (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st.ζ
      (Nh + 1) (stZeta (R.withMsq m)
        (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st)) /
    Fintype.card (Lam 2 L N)

/-- The zero-mode integral `Ω = ω_{cQ}(F_N)`. -/
def zZm (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) : Obs.OE .two (Lam 2 L N) :=
  PtCorr2.omegaCO (PtCorr2.cstC (Lam 2 L N) (zCc R Nh m b μ₀)) (zFin R Nh m b μ₀ x)

/-- `q_k = -ε(u^{obs}_{k,ab})`: the accumulated pair constant. -/
def zq (m b μ₀ : ℝ) (x : Lam 2 L N) (k : ℕ) : ℂ :=
  -ε ((Obs2.obsHist (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) k
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).u : Obs.SA .two (Lam 2 L N)).ab

/-- `γ_{a,N} = γ_{a,N-1} - ε((u_N - u_{N-1})_a)`. -/
def gamNa (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) : ℂ :=
  uA R m b μ₀ x (Nh + 1) - ε (zUN R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a

/-- `γ_{b,N}`. -/
def gamNb (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) : ℂ :=
  uB R m b μ₀ x (Nh + 1) - ε (zUN R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).b

/-- `q_N`. -/
def qN (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) : ℂ :=
  zq R m b μ₀ x (Nh + 1) - ε (zUN R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).ab

theorem zHi_eq (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) :
    zHi R Nh m b μ₀ x =
      zCst R Nh m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x) * zZm R Nh m b μ₀ x := by
  unfold zHi PtCorr2.prodHi PtCorr2.lastO zCst zUo zZm zFin zCc
  simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]

/-- **The constants above `k` in couplings**: `sA X = sE X·(γ_{a,N} - γ_{a,k})`, the same for `b`,
and `sAB X = sE X·((q_N - q_k) + (γ_{a,N} - γ_{a,k})(γ_{b,N} - γ_{b,k}))`. -/
theorem zCst_coup (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) {k : ℕ} (hk : k ≤ Nh + 1) :
    PtCorr2.sA (zCst R Nh m b μ₀ x k) =
        PtCorr2.sE (zCst R Nh m b μ₀ x k) * (gamNa R Nh m b μ₀ x - uA R m b μ₀ x k) ∧
      PtCorr2.sB (zCst R Nh m b μ₀ x k) =
        PtCorr2.sE (zCst R Nh m b μ₀ x k) * (gamNb R Nh m b μ₀ x - uB R m b μ₀ x k) ∧
      PtCorr2.sAB (zCst R Nh m b μ₀ x k) =
        PtCorr2.sE (zCst R Nh m b μ₀ x k) * ((qN R Nh m b μ₀ x - zq R m b μ₀ x k) +
          (gamNa R Nh m b μ₀ x - uA R m b μ₀ x k) * (gamNb R Nh m b μ₀ x - uB R m b μ₀ x k)) := by
  obtain ⟨h1, h2, h3⟩ := PtCorr2.prodIco_chO_s (R.withMsq m) (ptsX x)
    (Obs2.obsInit .two (zV b) (ptsX x)) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k (Nh + 1) hk
  simp only at h1 h2 h3
  obtain ⟨u1, u2, u3⟩ := PtCorr2.s_smul_expU_neg (L := L) (N := N) (U := zUN R Nh m b μ₀ x)
    (PtCorr2.detStep (R.withMsq m) (Nh + 1)
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st)
    (-Obs2.uXB (ptsX x) (Nh + 1)
      (LastN.stCovN (R.withMsq m) (Nh + 1)
        (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st)
      (Obs2.fullV (R.withMsq m) (Nh + 1)
        (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st
        (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).g.re
        (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).nu.re
        (Obs2.obsHist (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) (Nh + 1)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
      (Obs2.fullW (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st
        (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).D
        (Obs2.obsHist (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) (Nh + 1)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
      (Obs2.fullK (R.withMsq m) (Nh + 1)
        (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st
        (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).K
        (Obs2.obsHist (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) (Nh + 1)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
      univ)
    (PtCorr2.bulk_uXO (ptsX x) _ _ _ _ _ _ : Obs.bulk (zUN R Nh m b μ₀ x) = 0)
  have hU : zUo R Nh m b μ₀ x = PtCorr2.detStep (R.withMsq m) (Nh + 1)
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st •
      Obs2.expU (-Obs2.uXB (ptsX x) (Nh + 1)
      (LastN.stCovN (R.withMsq m) (Nh + 1)
        (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st)
      (Obs2.fullV (R.withMsq m) (Nh + 1)
        (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st
        (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).g.re
        (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).nu.re
        (Obs2.obsHist (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) (Nh + 1)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
      (Obs2.fullW (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st
        (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).D
        (Obs2.obsHist (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) (Nh + 1)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
      (Obs2.fullK (R.withMsq m) (Nh + 1)
        (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st
        (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).K
        (Obs2.obsHist (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) (Nh + 1)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
      univ) (-zUN R Nh m b μ₀ x) := rfl
  unfold zCst
  rw [hU, PtCorr2.sA_mul, PtCorr2.sB_mul, PtCorr2.sAB_mul, PtCorr2.sE_mul, h1, h2, h3, u1, u2, u3]
  unfold gamNa gamNb qN uA uB zq
  refine ⟨by ring, by ring, by ring⟩

set_option maxHeartbeats 1000000 in
/-- **The pair part above coalescence, split into constants and zero mode** (exact, along the
trajectory; hypotheses of `twopt_zz_eq`): with `X = zCst j`, `Ω = zZm`,
`E = n_{ab}X + (n_{ab}Ω + n_aX·n_bΩ + n_bX·n_aΩ)` and the one-point closure
`n_aΩ = r - (γ_{0,j} + n_aX)`, `r = 1 - b⟨ψ̄_0ψ_0⟩`. -/
theorem pair_E_split {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < m)
    (hm : m ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt (R.withMsq m) j)
    (hVL : ValidAtL (R.withMsq m) Nh) (hL : 2 ^ (2 + 3) + 8 * 2 < L) {b μ₀ : ℝ} (hb : 0 < b)
    (hh : b ≤ μ₀ + m) (x : Lam 2 L N) (hj : Obs.coal L (0 : Lam 2 L N) x ≤ Nh) :
    PtCorr2.sE (zCst R Nh m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x)) ≠ 0 ∧
      PtCorr2.sE (zZm R Nh m b μ₀ x) ≠ 0 ∧
      PtCorr2.sAB (zOm R m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x)) /
          PtCorr2.sE (zOm R m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x)) =
        PtCorr2.nAB (zCst R Nh m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x)) +
          (PtCorr2.nAB (zZm R Nh m b μ₀ x) +
            PtCorr2.nA (zCst R Nh m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x)) *
              PtCorr2.nB (zZm R Nh m b μ₀ x) +
            PtCorr2.nB (zCst R Nh m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x)) *
              PtCorr2.nA (zZm R Nh m b μ₀ x)) ∧
      PtCorr2.nA (zZm R Nh m b μ₀ x) =
        (1 - (b : ℂ) * PtCorr2.avg0 L N m b μ₀ (psibar 0 * psi 0)) -
          (uA R m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x) +
            PtCorr2.nA (zCst R Nh m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x))) := by
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  set X := zCst R Nh m b μ₀ x j with hXd
  set Ω := zZm R Nh m b μ₀ x with hΩd
  obtain ⟨hX0, hY0, ha, -, -⟩ := PtCorr2.zz_square_split (R.withMsq m) (ptsX x) hN hρ1 hspl hm0
    hm hV hVL hL hj hb hh (zV b) (zV_abFree b)
  have hw := PtCorr2.hist_omegaO_from (R.withMsq m) (ptsX x)
    (Obs2.obsInit .two (zV b) (ptsX x)) hN hρ1 hspl hm0 hm hV hVL b μ₀
    (Obs2.obsInit_isObs .two (zV b) (ptsX x)) (PtCorr2.obsLocInv_init .two (zV b) (ptsX x)) hj
  have hY : zHi R Nh m b μ₀ x = X * Ω := zHi_eq R Nh m b μ₀ x
  have e : zOm R m b μ₀ x j = X * Ω := hw.trans hY
  have hY0' : PtCorr2.sE (X * Ω) ≠ 0 := by rw [← hY]; exact hY0
  have hX : PtCorr2.sE X ≠ 0 := fun h => hY0' (by rw [PtCorr2.sE_mul, h, zero_mul])
  have hΩ : PtCorr2.sE Ω ≠ 0 := fun h => hY0' (by rw [PtCorr2.sE_mul, h, mul_zero])
  refine ⟨hX, hΩ, ?_, ?_⟩
  · rw [e]; show PtCorr2.nAB (X * Ω) = _; rw [PtCorr2.nAB_mul hX hΩ]; ring
  · obtain ⟨ea, -⟩ := PtCorr2.prodLo_sA_sB (R.withMsq m) (ptsX x)
      (Obs2.obsInit .two (zV b) (ptsX x)) rfl (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j
    have hX0' : PtCorr2.sE (zLo R m b μ₀ x) ≠ 0 := hX0
    have hA : PtCorr2.sA (zLo R m b μ₀ x) / PtCorr2.sE (zLo R m b μ₀ x) = uA R m b μ₀ x j := by
      have ea' : PtCorr2.sA (zLo R m b μ₀ x) = PtCorr2.sE (zLo R m b μ₀ x) * uA R m b μ₀ x j := ea
      rw [ea', mul_div_cancel_left₀ _ hX0']
    have hra : PtCorr2.avg0 L N m b μ₀ (PtCorr2.zObsA (zV b) (ptsX x)) =
        1 - (b : ℂ) * PtCorr2.avg0 L N m b μ₀ (psibar 0 * psi 0) := by
      rw [zObsA_zV]; exact Ward.avg_one_sub_smul _ _ (PtCorr2.onept_Zb_ne hb hm0 hh) _ _
    have ha' : PtCorr2.avg0 L N m b μ₀ (PtCorr2.zObsA (zV b) (ptsX x)) =
        PtCorr2.sA (zLo R m b μ₀ x) / PtCorr2.sE (zLo R m b μ₀ x) +
          PtCorr2.sA (zHi R Nh m b μ₀ x) / PtCorr2.sE (zHi R Nh m b μ₀ x) := ha
    have hn : PtCorr2.sA (zHi R Nh m b μ₀ x) / PtCorr2.sE (zHi R Nh m b μ₀ x) =
        PtCorr2.nA X + PtCorr2.nA Ω := by
      rw [hY]; exact PtCorr2.nA_mul hX hΩ
    rw [hra, hA, hn] at ha'
    rw [ha']; ring

/-- The scale-`N` one-point parts: `γ_{0,j} + n_aX = γ_{a,N}`. -/
theorem uA_add_nA_zCst (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) {k : ℕ} (hk : k ≤ Nh + 1)
    (hX : PtCorr2.sE (zCst R Nh m b μ₀ x k) ≠ 0) :
    uA R m b μ₀ x k + PtCorr2.nA (zCst R Nh m b μ₀ x k) = gamNa R Nh m b μ₀ x := by
  obtain ⟨h1, -, -⟩ := zCst_coup R Nh m b μ₀ x hk
  unfold PtCorr2.nA; rw [h1, mul_div_cancel_left₀ _ hX]; ring


/-! ### Named inputs and the reduction -/

/-- **Named input: the Pauli-adjusted accumulated pair constant above coalescence is small**:
`|(q_N - q_j) + (γ_{a,N} - γ_{a,j})(γ_{b,N} - γ_{b,j})| ≤ K₁‖M_j‖²ǧ_j` (in normalised form
`n_{ab}X`, `zCst_coup`). -/
def PairCstRel (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (K1 : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ‖PtCorr2.nAB (zCst R Nh m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x))‖ ≤
      K1 * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ ^ 2 *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1

/-- **Named input: the final object (before the zero mode).** With `F = F_N`, `Ā = n_aX`,
`B̄ = n_bX`: the Pauli-adjusted pair coupling `c2F_{ab} + Āc2F_b + B̄c2F_a` is `ρ̃·c2F_a` with
`‖ρ̃‖ ≤ K₃‖M_j‖ǧ_j` (relative to the `a`-vertex), and the constant part
`‖εF_{ab} + ĀεF_b + B̄εF_a - ρ̃εF_a‖ ≤ K₂‖M_j‖²ǧ_j‖sE Ω‖`. -/
def PairZeroRel (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (K2 K3 : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∃ ρ : ℂ,
      Suscept.c2 (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).ab +
          PtCorr2.nA (zCst R Nh m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x)) *
            Suscept.c2 (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).b +
          PtCorr2.nB (zCst R Nh m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x)) *
            Suscept.c2 (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a =
        ρ * Suscept.c2 (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a ∧
      ‖ρ‖ ≤ K3 * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 ∧
      ‖ε (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).ab +
          PtCorr2.nA (zCst R Nh m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x)) *
            ε (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).b +
          PtCorr2.nB (zCst R Nh m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x)) *
            ε (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a -
          ρ * ε (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a‖ ≤
        K2 * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ ^ 2 *
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 *
          ‖ε (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).e -
            zCc R Nh m b μ₀ * Suscept.c2 (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).e‖

/-- **Named input: the `γ` coupling at scale `N`** is `O(M_{j_x})`. -/
def GamTopBd (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (K4 : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ‖gamNa R Nh m b μ₀ x‖ ≤ K4 * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖

/-- Pure assembly of the bound. -/
theorem pair_bound_pure {E C Z wa rc : ℂ} {K1 K2 K3 K4 M g Mb : ℝ} (hK3 : 0 ≤ K3)
    (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (hMb : M ≤ Mb) (hM0 : 0 ≤ M)
    (hE : E = C + Z) (hC : ‖C‖ ≤ K1 * M ^ 2 * g) (hZ : ‖Z‖ ≤ K2 * M ^ 2 * g + K3 * M * g * ‖wa‖)
    (hwa : ‖wa‖ ≤ ‖rc‖ + K4 * M) :
    ‖E‖ ≤ (K1 + K2 + K3 * K4) * M ^ 2 * g + K3 * Mb * ‖rc‖ := by
  have hMg : M * g ≤ Mb := (mul_le_of_le_one_right hM0 hg1).trans hMb
  have h1 : K3 * M * g * ‖wa‖ ≤ K3 * K4 * M ^ 2 * g + K3 * Mb * ‖rc‖ := by
    have hK3Mg : 0 ≤ K3 * M * g := mul_nonneg (mul_nonneg hK3 hM0) hg0
    have := mul_le_mul_of_nonneg_left hwa hK3Mg
    have h2 : K3 * M * g * ‖rc‖ ≤ K3 * Mb * ‖rc‖ := by
      have := mul_le_mul_of_nonneg_left hMg hK3
      have := mul_le_mul_of_nonneg_right this (norm_nonneg rc)
      linarith
    have e : K3 * M * g * (‖rc‖ + K4 * M) = K3 * M * g * ‖rc‖ + K3 * K4 * M ^ 2 * g := by ring
    linarith
  rw [hE]
  refine (norm_add_le _ _).trans ?_
  have e : (K1 + K2 + K3 * K4) * M ^ 2 * g + K3 * Mb * ‖rc‖ =
      K1 * M ^ 2 * g + (K2 * M ^ 2 * g + (K3 * K4 * M ^ 2 * g + K3 * Mb * ‖rc‖)) := by ring
  rw [e]
  exact add_le_add hC (hZ.trans (add_le_add le_rfl h1))

set_option maxHeartbeats 1000000 in
/-- **`PairAboveW1` from the Pauli-adjusted pair couplings** (trajectory level):
`PairCstRel K₁`, `PairZeroRel K₂ K₃`, `GamTopBd K₄`, `‖M_k‖ ≤ M_b`, `0 ≤ ǧ ≤ 1` give
`PairAboveW1` with `K_E = K₁ + K₂ + K₃K₄`, `K_R = K₃M_b`. -/
theorem pairAboveW1_of_parts {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < m)
    (hm : m ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt (R.withMsq m) j)
    (hVL : ValidAtL (R.withMsq m) Nh) (hL : 2 ^ (2 + 3) + 8 * 2 < L) {b μ₀ : ℝ} (hb : 0 < b)
    (hh : b ≤ μ₀ + m) (lam : ℕ → ℂ) {K1 K2 K3 K4 Mb : ℝ} (hK3 : 0 ≤ K3)
    (hg : ∀ k ≤ Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1)
    (hMb : ∀ k ≤ Nh, ‖Mmag R m b μ₀ lam k‖ ≤ Mb)
    (hC : PairCstRel R Nh m b μ₀ lam K1) (hZ : PairZeroRel R Nh m b μ₀ lam K2 K3)
    (hT : GamTopBd R Nh m b μ₀ lam K4) :
    PairAboveW1 R Nh m b μ₀ lam (K1 + K2 + K3 * K4) (K3 * Mb) := by
  intro x hx h1 hj
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  obtain ⟨hX, hΩ, hE, hω⟩ := pair_E_split R hN m hρ1 hspl hm0 hm hV hVL hL hb hh x hj
  rw [← hjd] at hX hE hω
  obtain ⟨ρ, hρ, hρn, hx'⟩ := hZ x hx h1 hj
  rw [← hjd] at hρ hρn hx'
  set X := zCst R Nh m b μ₀ x j
  set F := zFin R Nh m b μ₀ x
  set cc := zCc R Nh m b μ₀
  obtain ⟨s1, s2, s3, s4⟩ := PtCorr2.sX_omegaCO_cstC cc F
  have hΩd : zZm R Nh m b μ₀ x = PtCorr2.omegaCO (PtCorr2.cstC (Lam 2 L N) cc) F := rfl
  have hs : ε (F : Obs.SA .two (Lam 2 L N)).e - cc * Suscept.c2 (F : Obs.SA .two (Lam 2 L N)).e ≠ 0 := by
    rw [← s1, ← hΩd]; exact hΩ
  have hbr : PtCorr2.nAB (zZm R Nh m b μ₀ x) + PtCorr2.nA X * PtCorr2.nB (zZm R Nh m b μ₀ x) +
      PtCorr2.nB X * PtCorr2.nA (zZm R Nh m b μ₀ x) =
      (ε (F : Obs.SA .two (Lam 2 L N)).ab + PtCorr2.nA X * ε (F : Obs.SA .two (Lam 2 L N)).b +
          PtCorr2.nB X * ε (F : Obs.SA .two (Lam 2 L N)).a - ρ * ε (F : Obs.SA .two (Lam 2 L N)).a) /
        (ε (F : Obs.SA .two (Lam 2 L N)).e - cc * Suscept.c2 (F : Obs.SA .two (Lam 2 L N)).e) +
      ρ * PtCorr2.nA (zZm R Nh m b μ₀ x) := by
    have hnA : PtCorr2.nA (zZm R Nh m b μ₀ x) =
        (ε (F : Obs.SA .two (Lam 2 L N)).a - cc * Suscept.c2 (F : Obs.SA .two (Lam 2 L N)).a) /
        (ε (F : Obs.SA .two (Lam 2 L N)).e - cc * Suscept.c2 (F : Obs.SA .two (Lam 2 L N)).e) := by
      unfold PtCorr2.nA; rw [hΩd, s1, s2]
    have hnB : PtCorr2.nB (zZm R Nh m b μ₀ x) =
        (ε (F : Obs.SA .two (Lam 2 L N)).b - cc * Suscept.c2 (F : Obs.SA .two (Lam 2 L N)).b) /
        (ε (F : Obs.SA .two (Lam 2 L N)).e - cc * Suscept.c2 (F : Obs.SA .two (Lam 2 L N)).e) := by
      unfold PtCorr2.nB; rw [hΩd, s1, s3]
    have hnAB : PtCorr2.nAB (zZm R Nh m b μ₀ x) =
        (ε (F : Obs.SA .two (Lam 2 L N)).ab - cc * Suscept.c2 (F : Obs.SA .two (Lam 2 L N)).ab) /
        (ε (F : Obs.SA .two (Lam 2 L N)).e - cc * Suscept.c2 (F : Obs.SA .two (Lam 2 L N)).e) := by
      unfold PtCorr2.nAB; rw [hΩd, s1, s4]
    rw [hnAB, hnB, hnA]
    exact PtCorr2.zm_pauli_elim hρ
  have hwa : ‖PtCorr2.nA (zZm R Nh m b μ₀ x)‖ ≤
      ‖1 - (b : ℂ) * PtCorr2.avg0 L N m b μ₀ (psibar 0 * psi 0)‖ +
        K4 * ‖Mmag R m b μ₀ lam j‖ := by
    rw [hω, uA_add_nA_zCst R Nh m b μ₀ x (by omega) hX]
    exact (norm_sub_le _ _).trans (add_le_add le_rfl (hT x hx h1 hj))
  have hZb := PtCorr2.zm_pauli_bound hs hx' hρn (le_refl ‖PtCorr2.nA (zZm R Nh m b μ₀ x)‖)
  exact pair_bound_pure hK3 (hg j hj).1 (hg j hj).2 (hMb j hj) (norm_nonneg _) hE
    (hC x hx h1 hj) (by rw [hbr]; exact hZb.trans (le_of_eq (by ring))) hwa

end Traj

end

end Spin2
