import Spin2.Multiscale.LamFlow
import Obs2.Flow.MuHist2

/-!
# (H_λ) for the Case-(2) vertex `λ̂_k = μ_{a,k}/μ_{a,0}`, and `thm:multiscale` with it

Along the trajectory `t = traj (rgDataM R m) L² b μ₀` (mass `m²`), the Case-(2) observable history
from `obsInit .two V P` (the vertex `-μ_aσ_aψ̄_aψ_a`, `V.mua = μ_{a,0}`):

* `bt2 k = ∑_B m₂(V_k(B)_a) = -μ_{a,k}` (`bt2_zero`: `= -V.mua` at `k = 0`), `nn2 k = 𝔫^{(2)}_k`
  (`Obs2.frakN2`, the one-loop coefficient: `ν̄^{(2)}_k = m₂F_{C_k}(ψ̄_aψ_a, V'_k(Λ)_∅)` plus the
  tadpoles of the earlier `𝒲^{obs}` cubics), `err2 k = ∑_{B_+} err_k(B_+)` (`Obs2.shareErr2`);
  `lamHat2 k = bt2 k/bt2 0 = μ_{a,k}/μ_{a,0}`;
* **`bt2_flow`** (exact, `Obs2.MuChain2.betaTot2_succ_eq` along the history):
  `β_{k+1} = β_k(1 - 𝔫^{(2)}_k) - err_k` for `k < N_h`;
* the two named inputs (`N_h` steps):
  - `Case2Rel` (the observable remainders, Case (2) analogue of the output of
    `PtCorr2.obs_hist_rel`): `‖err_k‖ ≤ c_δǧ_k²‖β_k(1 - 𝔫^{(2)}_k)‖`, `c_δǧ_k² ≤ 1/8`;
  - `Case2Loop` (the one-loop identification, bulk only): `‖𝔫^{(2)}_k‖ ≤ min(1/8, B'ǧ_k)` and
    `‖-𝔫^{(2)}_k - (β/3)ǧ_k + (q_{k+1} - q_k)‖ ≤ B(ǧ_k² + ǧ_ka_k)` with `q_0 = 0`,
    `‖q_k‖ ≤ c_qǧ_k` (complex; the phase is controlled by the imaginary part);
* **`hLam_case2`**: `LamConcl` (from `SpinConcl`) and these give `HLam` for `lamHat2`;
* `MultiConcl2`, `multiConcl2_of`, **`thm_multiscale_case2`**: `thm:multiscale` for
  `λ̂ = μ_a/μ_{a,0}` conditional on `RGInput`, `Case2Rel`, `Case2Loop` (no (H_λ)).
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Step2.D2

variable {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  (P : Obs2.ObsPts 2 L N) (V : Obs2.OCoup .two)

/-- `β_k = ∑_B m₂(V_k(B)_a) = -μ_{a,k}` along the Case-(2) history of the trajectory. -/
def bt2 (m b μ₀ : ℝ) (k : ℕ) : ℂ :=
  Obs2.betaTot2 (L := L) (N := N) k (Obs2.histVO2 (R.withMsq m) P (Obs2.obsInit .two V P)
    (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)

/-- `𝔫^{(2)}_k` along the Case-(2) history of the trajectory. -/
def nn2 (m b μ₀ : ℝ) (k : ℕ) : ℂ :=
  Obs2.frakN2 P (Obs2.histCovO (R.withMsq m) (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
    (Obs2.histVO2 (R.withMsq m) P (Obs2.obsInit .two V P) (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) k

/-- The error `∑_{B_+} err_k(B_+)` of the `μ^{(2)}` flow along the trajectory. -/
def err2 (m b μ₀ : ℝ) (k : ℕ) : ℂ :=
  ∑ c' ∈ blockIdx (L := L) (N := N) (k + 1),
    Obs2.shareErr2 P (Obs2.histCovO (R.withMsq m) (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
      (Obs2.histVO2 (R.withMsq m) P (Obs2.obsInit .two V P) (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
      (Obs2.histWO2 (R.withMsq m) P (Obs2.obsInit .two V P) (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
      (Obs2.histKO2 (R.withMsq m) P (Obs2.obsInit .two V P) (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
      k (blockSet (L := L) (N := N) (k + 1) c')

/-- `λ̂_k = μ_{a,k}/μ_{a,0}`. -/
def lamHat2 (m b μ₀ : ℝ) (k : ℕ) : ℂ := bt2 R P V m b μ₀ k / bt2 R P V m b μ₀ 0

theorem bt2_zero (m b μ₀ : ℝ) : bt2 R P V m b μ₀ 0 = -Obs2.OCoup2.mua V :=
  Obs2.betaTot2_obsInit (R.withMsq m) P _ V

/-- **The exact `μ^{(2)}` flow along the trajectory**. -/
theorem bt2_flow {Nh : ℕ} (hNh : Nh < N) (m b μ₀ : ℝ) {k : ℕ} (hk : k < Nh) :
    bt2 R P V m b μ₀ (k + 1) = bt2 R P V m b μ₀ k * (1 - nn2 R P V m b μ₀ k) - err2 R P V m b μ₀ k :=
  (Obs2.muChain2_obsHist (R.withMsq m) P (Obs2.obsInit .two V P)
    (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (n := Nh) hNh
    (fun b' => Obs2.obsInit_two_W P V b') (fun b' => Obs2.obsInit_two_form P V b')).betaTot2_succ_eq hk

/-- **Named input: the observable remainders of the `μ^{(2)}` flow** (relative form). -/
def Case2Rel (Nh : ℕ) (m b μ₀ cδ : ℝ) : Prop :=
  ∀ k < Nh, ‖err2 R P V m b μ₀ k‖ ≤ cδ * (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ^ 2 *
      ‖bt2 R P V m b μ₀ k * (1 - nn2 R P V m b μ₀ k)‖ ∧
    cδ * (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ^ 2 ≤ 1 / 8

/-- **Named input: the one-loop identification of `𝔫^{(2)}`** (`Re 𝔫^{(2)}_k ≈ -(β/3)ǧ_k` up to
a telescoping `q`). -/
def Case2Loop (Nh : ℕ) (m b μ₀ B B' cq : ℝ) : Prop :=
  ∃ q : ℕ → ℂ, q 0 = 0 ∧
    (∀ k ≤ Nh, ‖q k‖ ≤ cq * (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1) ∧
    ∀ k < Nh, ‖nn2 R P V m b μ₀ k‖ ≤ 1 / 8 ∧
      ‖nn2 R P V m b μ₀ k‖ ≤ B' * (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      ‖-nn2 R P V m b μ₀ k - ((betaL L / 3 * (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 : ℝ) : ℂ) +
          (q (k + 1) - q k)‖ ≤ B * (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ^ 2 +
        B * (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 * zA L m k

variable {R P V}

/-- **(H_λ) for `λ̂ = μ_a/μ_{a,0}`** from `Case2Rel` and `Case2Loop`, at one trajectory
(`LamConclAt`). -/
theorem hLam_case2_at {cg Ke : ℝ} {Nh : ℕ} {m b μ₀ : ℝ} (hLC : LamConclAt L cg Ke R Nh m b μ₀)
    (hNh : Nh + 2 ≤ N)
    {B B' cq cδ : ℝ} (hB : 0 ≤ B) (hcδ : 0 ≤ cδ) (hmu : Obs2.OCoup2.mua V ≠ 0)
    (hrel : Case2Rel R P V Nh m b μ₀ cδ) (hloop : Case2Loop R P V Nh m b μ₀ B B' cq) :
    HLam R Nh m b μ₀ (lamHat2 R P V m b μ₀)
      (lamRelK (betaL L) cg B B' cq cδ (eRange (betaL L) Ke 1) 4) := by
  obtain ⟨q, hq0, hq, hl⟩ := hloop
  have hb0 : bt2 R P V m b μ₀ 0 ≠ 0 := by rw [bt2_zero]; exact neg_ne_zero.2 hmu
  refine hLC (bt2 R P V m b μ₀)
    (nn2 R P V m b μ₀) q B B' cq cδ hB hcδ hb0 (fun k hk => ?_) (fun k hk => (hrel k hk).2)
    (fun k hk => (hl k hk).1) (fun k hk => (hl k hk).2.1) hq0 hq (fun k hk => (hl k hk).2.2)
  rw [bt2_flow R P V (by omega) m b μ₀ hk, sub_sub_cancel_left, norm_neg]
  exact (hrel k hk).1

/-- **(H_λ) for `λ̂ = μ_a/μ_{a,0}`** from `Case2Rel` and `Case2Loop`. -/
theorem hLam_case2 {ℓ A ρ κ cg cm cT ε Ke : ℝ} (hLC : LamConcl L ℓ A ρ κ cg cm cT ε Ke)
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = ℓ) (hRA : R.A = A) (hRρ : R.ρ = ρ)
    {Nh : ℕ} (hNh : Nh + 2 ≤ N) {m : ℝ} (hm : m ∈ mRange L N) {b μ₀ : ℝ}
    (hadm : Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀)
    {B B' cq cδ : ℝ} (hB : 0 ≤ B) (hcδ : 0 ≤ cδ) (hmu : Obs2.OCoup2.mua V ≠ 0)
    (hrel : Case2Rel R P V Nh m b μ₀ cδ) (hloop : Case2Loop R P V Nh m b μ₀ B B' cq) :
    HLam R Nh m b μ₀ (lamHat2 R P V m b μ₀)
      (lamRelK (betaL L) cg B B' cq cδ (eRange (betaL L) Ke 1) 4) :=
  hLam_case2_at (hLC N R hP hi0 hRℓ hRA hRρ (by omega) Nh hNh m hm b μ₀ hadm) hNh hB hcδ hmu hrel
    hloop

/-- **`thm:multiscale` with `λ̂ = μ_a/μ_{a,0}`** (Case (2)), for given constants: along every
admissible trajectory, `RGInput`, `Case2Rel`, `Case2Loop` give, for `x ≠ 0` with `j_x ≤ N_h`,
`j = j(|x|) ∈ {j_x - 1, j_x}` and `|P_{1/b}[0 ↔ x] - ϑ_j²| ≤ K ϑ_j²/β_j`. -/
def MultiConcl2 (L : ℕ) [NeZero L] (ℓ A ρ κ cg cm cT ε Ke KZ KG : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ →
  ∀ Nh : ℕ, Nh + 2 ≤ N →
  ∀ m ∈ mRange L N, ∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
  ∀ (P : Obs2.ObsPts 2 L N) (V : Obs2.OCoup .two) (B B' cq cδ KP : ℝ), 0 ≤ B → 0 ≤ cδ → 0 ≤ KP →
    Obs2.OCoup2.mua V ≠ 0 → Case2Rel R P V Nh m b μ₀ cδ → Case2Loop R P V Nh m b μ₀ B B' cq →
    RGInput R Nh m b μ₀ (lamHat2 R P V m b μ₀) KP →
  ∀ x : Lam 2 L N, x ≠ 0 → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∃ jp : ℕ, (jp : ℤ) = jPhys L N (eucl x / (L : ℝ) ^ N) ∧
      jp ≤ Obs.coal L (0 : Lam 2 L N) x ∧ Obs.coal L (0 : Lam 2 L N) x ≤ jp + 1 ∧
      |Pconn L N (1 / b) x - thetaSq R m b μ₀ jp| ≤
        multK L cg Ke KZ KG (max (lamRelK (betaL L) cg B B' cq cδ (eRange (betaL L) Ke 1) 4) 0)
          KP * thetaSq R m b μ₀ jp / betaJ R m b μ₀ jp

theorem hLam_mono {Nh : ℕ} {m b μ₀ : ℝ} {lam : ℕ → ℂ} {Kl Kl' : ℝ} (hb : 0 < b)
    (hm : 0 ≤ m) (hg : ∀ k < Nh, 0 < (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1)
    (h : HLam R Nh m b μ₀ lam Kl) (hK : Kl ≤ Kl') : HLam R Nh m b μ₀ lam Kl' := by
  intro k hk
  refine (h k hk).trans ?_
  have h1 : 0 ≤ ((Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 / b) ^ (1 / 3 : ℝ) *
      ((Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) :=
    mul_nonneg (Real.rpow_nonneg (div_pos (hg k hk) hb).le _)
      (add_nonneg (hg k hk).le (zA_nonneg L hm k))
  rw [mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_right hK h1

/-- **`MultiConcl2` from `SpinConcl` and `MultiConcl`** (the same constants). -/
theorem multiConcl2_of {L : ℕ} [NeZero L] {ℓ A ρ κ cg cm cT ε Ke KZ KG : ℝ} (hL2 : (2 : ℝ) ≤ L)
    (hε1 : ε ≤ 1) (hSp : SpinConcl L ℓ A ρ κ cg cm cT ε Ke KZ KG)
    (hM : MultiConcl L ℓ A ρ κ cg cm cT ε Ke KZ KG) : MultiConcl2 L ℓ A ρ κ cg cm cT ε Ke KZ KG := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ Nh hNh m hm b μ₀ hadm P V B B' cq cδ KP hB hcδ hKP hmu hrel
    hloop hrg x hx hj
  have hLC := lamConcl_of hL2 hε1 hSp
  have hl := hLam_case2 hLC hP hi0 hRℓ hRA hRρ hNh hm hadm hB hcδ hmu hrel hloop
  have hb : 0 < b := by
    have := (hadm.1 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hl' := hLam_mono hb hm.1.le (fun k hk => (hadm.1 k hk.le).1) hl (le_max_left _ 0)
  exact hM N R hP hi0 hRℓ hRA hRρ Nh hNh m hm b μ₀ hadm _ _ KP (le_max_right _ _) hKP hl' hrg x
    hx hj

/-- **Expected result `thm:multiscale` for `λ̂ = μ_a/μ_{a,0}`**, conditional on `thm:rginput`
(`RGInput`) and the two Case-(2) flow inputs `Case2Rel`, `Case2Loop` (no (H_λ)): one set of
constants with `FlowC2Concl`, `ε ≤ 1`, `BetaConcl`, `LamConcl`, `MultiConcl2`. -/
theorem thm_multiscale_case2 : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ κ cg cm cT ε Ke Cf Cb KZ KG : ℝ, FlowC2Concl L ℓ A ρ κ cg cm cT ε Ke Cf Cb ∧ ε ≤ 1 ∧
      BetaConcl L ℓ A ρ κ cg cm cT ε Ke Cb ∧ LamConcl L ℓ A ρ κ cg cm cT ε Ke ∧
      MultiConcl2 L ℓ A ρ κ cg cm cT ε Ke KZ KG := by
  obtain ⟨L₀, hL₀⟩ := thm_flow_master_all (fun _ _ => True) (fun _ => ⟨0, fun _ _ => trivial⟩)
    (fun _ _ _ _ _ => True) (fun _ _ _ _ => Filter.Eventually.of_forall fun _ => trivial)
  refine ⟨max L₀ 2, fun L _ hL => ?_⟩
  obtain ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, Cf, Cb, KZ, KG, hC2, hε1, -, -, hSp, hMag, hB, -⟩ :=
    hL₀ L (le_trans (le_max_left _ _) hL)
  have hL2 : 2 ≤ L := le_trans (le_max_right _ _) hL
  have hL2' : (2 : ℝ) ≤ L := by exact_mod_cast hL2
  have hM := multiConcl_of hL2 hε1 hSp hMag
  exact ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, Cf, Cb, KZ, KG, hC2, hε1, hB, lamConcl_of hL2' hε1 hSp,
    multiConcl2_of hL2' hε1 hSp hM⟩

end

end Spin2
