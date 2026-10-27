import Spin2.Restart.Restart2Lin
import Spin2.Restart.Restart2DMaster
import Spin2.Cont.ContDiff
import Spin2.Cont.ContDiff2
import PtCorr2.Restart.RerepK
import PtCorr2.Restart.RerepSym
import PtCorr2.Restart.HistLink

/-!
# B3, T6: the small restarted output of the difference datum (route (A), T4′)

The difference datum at the restart scale `k` (Log, "B3, T6 inputs"):
`δ = rrStH(o^P) − o^{P'}`, `o^P = obsHist (R.withMsq m) P (obsInit .two V P) k t`, Loc point `P'.a`,
with `β_B = m₂(V^P_k(B)_a)` (`cd3Delta`).

* **`cd3_struct`**: `δ` is observable, local (`ObsLocInv P' k`), symmetric, and
  `V^δ(B)_a = m₂(V^δ(B)_a)ψ̄_{a'}ψ_{a'}` (so `Loc2Form`), for `blk k P.a = blk k P'.a`,
  `P.b = P'.b`, `γ_a = 0`.
* **`cd3_dev`**: `D^δ_k ≤ D^P_k + D^{P'}_k` (same `k`-block).
* **`cd3_W`**: `‖𝒲^δ_k(B)‖ ≤ ‖𝒲^P_k(B)‖ + ‖𝒲^{P'}_k(B)‖` (bounds of the form `WbHc`).
* **`cd3_restart`** (the T6 statement, `MasterFacts`): along every admissible trajectory, for
  `0 < k < N_h`, same `k`-block, `|a − a'|_∞ ≤ L^{k−r}`, `r ≤ k`, with the bulk inputs
  `T_k(I'(B)_∅) ≤ ι` and `A^{|𝓑(W)|}T_k(K♭_k(W)) ≤ 1` (named, see Log), the small-coupling
  conditions `K_λ(ǧ_k + a_k) ≤ 1/2` and `c_bn(…)·2c_W cǧ_k ≤ 1/1344`:
  `|β^δ_{k+j}| ≤ (4/3)M^δ ∏_{i<j}|1 − 𝔫F_{k+i}|` (`j ≤ N_h − k`) with
  `M^δ = 4K_λ(ǧ_k + a_k)|β^{P'}_k| + 6c_δc²(ǧ_k/(β_L/4))(|β^P_k| + |β^{P'}_k|)
    + 1344(8c_N(16c_WB(cǧ_k)²(|β^P_k| + |β^{P'}_k|) + 2|β^P_k|·4L^{−r}ιA)
    + Γ_w c_W(cǧ_k)·2(|β^P_k| + |β^{P'}_k|))`, i.e. `M^δ ≲ (ǧ_k + a_k + ιAL^{−r})|β_k|`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc FRD Flow2 Flow2.Hist Obs2 Step2.D2

variable {L : ℕ} [NeZero L]

section Struct

variable {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- The one-point state at scale `k` at the vertex position `P.a`. -/
def cd3O (P : ObsPts 2 L N) (V : OCoup .two) (k : ℕ) (t : Hist.Seq (Xs R)) : ObsSt .two L N :=
  obsHist R P (obsInit .two V P) k t

/-- The block couplings `β_B = m₂(V_k(B)_a)` of the one-point state. -/
def cd3Beta (P : ObsPts 2 L N) (V : OCoup .two) (k : ℕ) (t : Hist.Seq (Xs R)) :
    (Fin 2 → ℕ) → ℂ :=
  fun b => LocObs.mass2 (((cd3O R P V k t).V b : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a

/-- **The difference datum** `δ = rrStH(o^P) − o^{P'}` at scale `k` (Loc point `P'.a`). -/
def cd3Delta (P P' : ObsPts 2 L N) (V : OCoup .two) (k : ℕ) (t : Hist.Seq (Xs R)) :
    ObsSt .two L N :=
  subSt (rrStH R k t P.a P'.a (cd3Beta R P V k t) (cd3O R P V k t)) (cd3O R P' V k t)

theorem cd3_pure (P : ObsPts 2 L N) (V : OCoup .two) (hga : OCoup2.ga V = 0) (k : ℕ)
    (t : Hist.Seq (Xs R)) (b : Fin 2 → ℕ) :
    (((cd3O R P V k t).V b : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a =
      cd3Beta R P V k t b • LocObs.pbp P.a :=
  obsHist2_pure R P t V hga k b

set_option maxHeartbeats 1000000 in
/-- **The structural hypotheses of the restart for the difference datum.** -/
theorem cd3_struct (P P' : ObsPts 2 L N) (V : OCoup .two) (hga : OCoup2.ga V = 0) (k : ℕ)
    (t : Hist.Seq (Xs R)) (hval : ∀ j < k + 1, ValidCore R j ∧ RawInv R j (rawHist R j t))
    (hab : blk k P.a = blk k P'.a) (hPb : P.b = P'.b) :
    (cd3Delta R P P' V k t).IsObs ∧ ObsLocInv P' k (cd3Delta R P P' V k t) ∧
      ObsSymInv k (cd3Delta R P P' V k t) ∧
      (∀ b, Obs2.Loc2Form P'.a ((cd3Delta R P P' V k t).V b : SA .two (Lam 2 L N)).a) ∧
      (∀ b, ((cd3Delta R P P' V k t).V b : SA .two (Lam 2 L N)).a =
        LocObs.mass2 ((cd3Delta R P P' V k t).V b : SA .two (Lam 2 L N)).a •
          LocObs.pbp P'.a) := by
  have hv : ∀ j < k, ValidCore R j ∧ RawInv R j (rawHist R j t) := fun j hj => hval j (by omega)
  have hO := obsHist_isObs R P (obsInit .two V P) (obsInit_isObs .two V P) k t
  have hO' := obsHist_isObs R P' (obsInit .two V P') (obsInit_isObs .two V P') k t
  have HL := obsLocInv_hist R P (obsInit .two V P) (obsLocInv_init .two V P) t k hv
  have HL' := obsLocInv_hist R P' (obsInit .two V P') (obsLocInv_init .two V P') t k hv
  have HS := obsSymInv_hist R P (obsInit .two V P) (obsSymInv_init .two V P) t k hv
  have HS' := obsSymInv_hist R P' (obsInit .two V P') (obsSymInv_init .two V P') t k hv
  obtain ⟨hVk, HRk⟩ := hval k (by omega)
  have HLr := rrSt_obsLocInv_core (R := R) (j := k) (st := rawHist R k t) (g := (t k).1)
    (μ := (t k).2.1) (D := rawD R (rawHist R k t).u (t k).2.2)
    (K := rawK R (rawHist R k t).u (t k).2.2) (a' := P'.a) (β := cd3Beta R P V k t)
    (P' := P') HL rfl hab hPb (cd3_pure R P V hga k t) hVk HRk (rawD_mem R _ _) (rawK_mem R _ _)
  have HSr := rrSt_obsSymInv_core (R := R) (j := k) (st := rawHist R k t) (g := (t k).1)
    (μ := (t k).2.1) (D := rawD R (rawHist R k t).u (t k).2.2)
    (K := rawK R (rawHist R k t).u (t k).2.2) (a := P.a) (a' := P'.a) (β := cd3Beta R P V k t)
    HS hVk HRk (rawD_mem R _ _) (rawK_mem R _ _)
  have hform : ∀ b, ((cd3Delta R P P' V k t).V b : SA .two (Lam 2 L N)).a =
      (cd3Beta R P V k t b - cd3Beta R P' V k t b) • LocObs.pbp P'.a := by
    intro b
    have e1 := rrSt_V_a_eq (R := R) (j := k) (st := rawHist R k t) (g := (t k).1)
      (μ := (t k).2.1) (D := rawD R (rawHist R k t).u (t k).2.2)
      (K := rawK R (rawHist R k t).u (t k).2.2) (a := P.a) (a' := P'.a)
      (β := cd3Beta R P V k t) (cd3_pure R P V hga k t b)
    have e2 := cd3_pure R P' V hga k t b
    show (((rrStH R k t P.a P'.a (cd3Beta R P V k t) (cd3O R P V k t)).V b : OE .two (Lam 2 L N)) :
        SA .two (Lam 2 L N)).a - (((cd3O R P' V k t).V b : OE .two (Lam 2 L N)) :
        SA .two (Lam 2 L N)).a = _
    rw [rrStH, e1, e2, sub_smul]
  refine ⟨subSt_isObs (rrSt_isObs _ _ _ _ _ _ _ _ _ _ hO) hO',
    ⟨fun b => sub_mem (HLr.V b) (HL'.V b), fun b => sub_mem (HLr.W b) (HL'.W b),
      fun Y hY => sub_mem (HLr.K Y hY) (HL'.K Y hY)⟩,
    ⟨fun b => sub_mem (HSr.V b) (HS'.V b), fun b => sub_mem (HSr.W b) (HS'.W b),
      fun Y hY => sub_mem (HSr.K Y hY) (HS'.K Y hY)⟩, fun b => ?_, fun b => ?_⟩
  · exact ⟨0, cd3Beta R P V k t b - cd3Beta R P' V k t b, by rw [hform b, zero_smul, zero_add]⟩
  · rw [hform b, LocObs.mass2_smul, LocObs.mass2_pbp, mul_one]

/-- The coupling form of the difference datum: `V^δ(B)_a = (β_B − β'_B)ψ̄_{a'}ψ_{a'}`. -/
theorem cd3_form (P P' : ObsPts 2 L N) (V : OCoup .two) (hga : OCoup2.ga V = 0) (k : ℕ)
    (t : Hist.Seq (Xs R)) (b : Fin 2 → ℕ) :
    ((cd3Delta R P P' V k t).V b : SA .two (Lam 2 L N)).a =
      (cd3Beta R P V k t b - cd3Beta R P' V k t b) • LocObs.pbp P'.a := by
  have e1 := rrSt_V_a_eq (R := R) (j := k) (st := rawHist R k t) (g := (t k).1)
    (μ := (t k).2.1) (D := rawD R (rawHist R k t).u (t k).2.2)
    (K := rawK R (rawHist R k t).u (t k).2.2) (a := P.a) (a' := P'.a)
    (β := cd3Beta R P V k t) (cd3_pure R P V hga k t b)
  have e2 := cd3_pure R P' V hga k t b
  show (((rrStH R k t P.a P'.a (cd3Beta R P V k t) (cd3O R P V k t)).V b : OE .two (Lam 2 L N)) :
      SA .two (Lam 2 L N)).a - (((cd3O R P' V k t).V b : OE .two (Lam 2 L N)) :
      SA .two (Lam 2 L N)).a = _
  rw [rrStH, e1, e2, sub_smul]

theorem cd3_mass (P : ObsPts 2 L N) (V : OCoup .two) (k : ℕ) (t : Hist.Seq (Xs R))
    (b : Fin 2 → ℕ) :
    LocObs.mass2 (histVO2 R P (obsInit .two V P) t k b : SA .two (Lam 2 L N)).a =
      cd3Beta R P V k t b := by
  rw [histVO2_a]; rfl

theorem cd3_betaTot (P : ObsPts 2 L N) (V : OCoup .two) (k : ℕ) (t : Hist.Seq (Xs R)) :
    betaTot2 k (histVO2 R P (obsInit .two V P) t k) = ∑ b ∈ blockIdx (L := L) (N := N) k,
      cd3Beta R P V k t b := by
  unfold betaTot2; exact sum_congr rfl fun b _ => cd3_mass R P V k t b

/-- **The share deviation of the difference datum**: `D^δ_k ≤ D^P_k + D^{P'}_k`. -/
theorem cd3_dev (P P' : ObsPts 2 L N) (V : OCoup .two) (hga : OCoup2.ga V = 0) (k : ℕ)
    (t : Hist.Seq (Xs R)) (hab : blk k P.a = blk k P'.a) :
    shareDev2 P'.a k (cd3Delta R P P' V k t).V ≤
      shareDev2 P.a k (histVO2 R P (obsInit .two V P) t k) +
        shareDev2 P'.a k (histVO2 R P' (obsInit .two V P') t k) := by
  have hm : ∀ b, LocObs.mass2 ((cd3Delta R P P' V k t).V b : SA .two (Lam 2 L N)).a =
      cd3Beta R P V k t b - cd3Beta R P' V k t b := fun b => by
    rw [cd3_form R P P' V hga k t b, LocObs.mass2_smul, LocObs.mass2_pbp, mul_one]
  have hB : betaTot2 k (cd3Delta R P P' V k t).V =
      ∑ b ∈ blockIdx (L := L) (N := N) k, cd3Beta R P V k t b -
        ∑ b ∈ blockIdx (L := L) (N := N) k, cd3Beta R P' V k t b := by
    unfold betaTot2; rw [← sum_sub_distrib]; exact sum_congr rfl fun b _ => hm b
  unfold shareDev2
  rw [cd3_betaTot, cd3_betaTot, hB, ← sum_add_distrib]
  refine sum_le_sum fun b _ => ?_
  rw [hm, cd3_mass, cd3_mass]
  have hiff : P'.a ∈ blockSet (L := L) (N := N) k b ↔ P.a ∈ blockSet (L := L) (N := N) k b := by
    rw [mem_blockSet, mem_blockSet, hab]
  by_cases h : P.a ∈ blockSet (L := L) (N := N) k b
  · rw [if_pos (hiff.2 h), if_pos h, if_pos (hiff.2 h)]
    refine le_trans (le_of_eq ?_) (norm_sub_le _ _)
    congr 1; ring
  · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h, if_neg (fun h' => h (hiff.1 h'))]
    refine le_trans (le_of_eq ?_) (norm_sub_le _ _)
    congr 1; ring

/-- The coupling and the share deviation of the restarted history at its own scale. -/
theorem cd3_hist_k (P' : ObsPts 2 L N) (k : ℕ) (o : ObsSt .two L N) (t : Hist.Seq (Xs R)) :
    betaTot2 k (histVF2 R P' k o t k) = betaTot2 k o.V ∧
      shareDev2 P'.a k (histVF2 R P' k o t k) = shareDev2 P'.a k o.V := by
  have h : ∀ b, (histVF2 R P' k o t k b : SA .two (Lam 2 L N)).a =
      (o.V b : SA .two (Lam 2 L N)).a := fun b => by rw [histVF2_a, obsHistFrom_self]
  have hb : betaTot2 k (histVF2 R P' k o t k) = betaTot2 k o.V := by
    unfold betaTot2; exact sum_congr rfl fun b _ => by rw [h b]
  refine ⟨hb, ?_⟩
  unfold shareDev2
  rw [hb]
  exact sum_congr rfl fun b _ => by rw [h b]

/-- **The `𝒲` of the difference datum**: `WbHc` bounds of the two one-point states add. -/
theorem cd3_W (P P' : ObsPts 2 L N) (V : OCoup .two) (k : ℕ) (t : Hist.Seq (Xs R)) {x x' : ℝ}
    (hx : 0 ≤ x) (hx' : 0 ≤ x')
    (hW : WbHc R P (obsInit .two V P) t k x) (hW' : WbHc R P' (obsInit .two V P') t k x') :
    WbHF R P' k (cd3Delta R P P' V k t) t k (x + x') := by
  intro b hb
  rw [obsHistFrom_self, rr_oTo_wA]
  have h1 := hW b hb
  have h2 := hW' b hb
  rw [rr_oTo_wA] at h1 h2
  show Tj 2 (L : ℝ) k (histS R k t) ((((rrStH R k t P.a P'.a (cd3Beta R P V k t)
      (cd3O R P V k t)).W b - (cd3O R P' V k t).W b : OE .two (Lam 2 L N)) :
        SA .two (Lam 2 L N)).a) ≤ _
  refine (tNorm_sub_le _ _).trans ?_
  rw [ENNReal.ofReal_add hx hx']
  exact add_le_add h1 h2

end Struct

/-! ### The small restarted output -/

/-- `Γ_w ≥ 0`. -/
theorem MasterCore.rdtΓ_nonneg (D : MasterCore L) (hc : 0 ≤ D.c) (hε : 0 ≤ D.ε) :
    0 ≤ D.rdtΓ := by
  obtain ⟨-, -, -, -, -, -, hBk, -, -, -⟩ := D.consts_nonneg
  have hcP : 0 ≤ D.cP := by
    show 0 ≤ (cbnC : ℝ) * D.Cpf L * (6 / 5 * L + 3072 * Obs2.locK 2 ^ 2)
    have := D.hCpf L; positivity
  have hC : 0 ≤ D.rdtC := by
    unfold MasterCore.rdtC; have := Obs2.one_le_locK 2; positivity
  unfold MasterCore.rdtΓ
  have := mul_nonneg hc hε
  positivity


/-- **The envelope of the difference datum** (`g = ǧ_k`, `z = a_k`, `β = |β^P_k|`,
`β' = |β^{P'}_k|`, `s = s_k`): `M^δ ≲ (ǧ_k + a_k + ιAL^{-r})|β_k|`. -/
def MasterFacts.cd3M (M : MasterFacts L) (g z bb bb' s ι A : ℝ) (r : ℕ) : ℝ :=
  4 * (M.csmK * (g + z)) * bb' + 6 * (M.core.cδ * (M.core.c ^ 2 * (g / (betaL L / 4)))) * (bb + bb') +
    1344 * (8 * (PtCorr2.csN 2 : ℝ) * (16 * M.core.cWo * M.core.Bk * (M.core.c * g) ^ 2 * (s ^ 2 * bb) +
        16 * M.core.cWo * M.core.Bk * (M.core.c * g) ^ 2 * (s ^ 2 * bb') +
        2 * bb * (4 * s ^ 2 / (L : ℝ) ^ r) * ι * A) +
      M.core.rdtΓ * (M.core.cWo * (M.core.c * g) * (2 * s ^ 2 * bb) +
        M.core.cWo * (M.core.c * g) * (2 * s ^ 2 * bb'))) / s ^ 2 + g * bb'

set_option maxHeartbeats 4000000 in
/-- **T6: the restarted coupling of the difference datum is small** (route (A), `restartDT`). -/
theorem cd3_restart (M : MasterFacts L) (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)]
    [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ)
    (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N)
    (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μ₀)
    (P P' : ObsPts 2 L N) (V : OCoup .two) (hga : OCoup2.ga V = 0) (hmu : OCoup2.mua V ≠ 0)
    {k r : ℕ} (hk0 : 0 < k) (hkN : k < Nh) (hrk : r ≤ k)
    (hab : blk k P.a = blk k P'.a) (hPb : P.b = P'.b)
    (hdist : supNorm (P.a - P'.a) ≤ L ^ (k - r))
    (hs0 : 0 ≤ M.csmK * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k))
    (hs : M.csmK * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) ≤ 1 / 2)
    (hg : M.core.rdtC * (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1) * 2) ≤
      1 / 1344)
    {ι : ℝ} (hι : 0 ≤ ι)
    (hI : ∀ b', Tj 2 (L : ℝ) k (histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
      ((IbO (fun b'' => emb (stVf (R.withMsq m) k (rawHist (R.withMsq m) k
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).2.1 b'' +
        stDelta (R.withMsq m) k (rawHist (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) b'') +
        ((cd3O (R.withMsq m) P V k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).V b'' -
          rrD P.a P'.a (cd3Beta (R.withMsq m) P V k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) b''))
        (fullW (rawHist (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          (rawD (R.withMsq m) (rawHist (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).u
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).2.2)
          (cd3O (R.withMsq m) P V k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))) b' :
        OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).e ≤ ENNReal.ofReal ι)
    (hKb : ∀ W, IsConn k W → ENNReal.ofReal ((R.withMsq m).A ^ nb k W) *
      Tj 2 (L : ℝ) k (histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((rawK (R.withMsq m) (rawHist (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).u
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).2.2 W : Step.EvR (Lam 2 L N)) : Alg 2 L N) ≤ 1) :
    ∀ j ≤ Nh - k,
      ‖betaTot2 (L := L) (N := N) (k + j) (histVF2 (R.withMsq m) P' k
          (cd3Delta (R.withMsq m) P P' V k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (k + j))‖ ≤
        4 / 3 * M.cd3M (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 (zA L m k)
            ‖bt2 R P V m b μ₀ k‖ ‖bt2 R P' V m b μ₀ k‖
            (histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) ι (R.withMsq m).A r *
          ∏ i ∈ range j, ‖1 - frakN2F P' (histCovO (R.withMsq m)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
            (histVF2 (R.withMsq m) P' k
              (cd3Delta (R.withMsq m) P P' V k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
              (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) k (k + i)‖ := by
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  set R' := R.withMsq m with hR'
  set s := histS R' k t with hsd
  set g := (t k).1 with hgd
  set bb := ‖bt2 R P V m b μ₀ k‖ with hbbd
  set bb' := ‖bt2 R P' V m b μ₀ k‖ with hbb'd
  have hNh0 : 0 < Nh := by omega
  -- bulk validity
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8, -, hCN⟩ := id M.core.hC2
  obtain ⟨hV, -⟩ := (hCN N R hP hi0 hRℓ hRA hRρ hN Nh hNh).2.2.2.2.2.2.2.2.2 m hm
  have hval := hist_valid R' hV t (n := k + 1) (by omega)
  have hρ0' : 0 ≤ R'.ρ := by rw [show R'.ρ = M.core.ρ from hRρ]; exact hρpos.le
  have hρ8' : R'.ρ ≤ 1 / 8 := by rw [show R'.ρ = M.core.ρ from hRρ]; exact hρ8
  have hsp : 0 < s := histS_pos' R' hρ0' hρ8' t k
  have hgp : 0 < g := (hadm.1 k (by omega)).1
  -- the one-point data
  obtain ⟨hbb0, hsh, hWP, hKP⟩ := csm_K M N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm P V hga
    hmu hNh0 hkN.le
  obtain ⟨hbb0', -, hWP', hKP'⟩ := csm_K M N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm P' V
    hga hmu hNh0 hkN.le
  have hDP := M.core.relDev N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm P V hga hmu hNh0 k
    hkN.le
  have hDP' := M.core.relDev N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm P' V hga hmu hNh0 k
    hkN.le
  have hβδ := cd_delta_beta_le M N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm P P' V hmu hkN
    hs0 hs (cd3Beta R' P V k t)
  -- constants
  obtain ⟨-, -, -, -, -, hcWo, hBk, hcδ, -, -⟩ := M.core.consts_nonneg
  have hc2 : 0 ≤ M.core.c := by
    obtain ⟨H, -, -⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm
    have hcR : cR R' ((L : ℝ) ^ 2) M.core.cm M.core.C₂x = M.core.c := by
      rw [M.core.hc]; exact cR_congr (show R.ℓ = M.core.ℓ from hRℓ) _ _ _
    have := hcR ▸ two_le_cR R' H.hcmu H.hC₂
    linarith
  have hβL : 0 ≤ betaL L := by
    have := betaL_ge (show 8 ≤ L by have := M.core.hL49; omega); linarith
  have hA1 : 1 ≤ R'.A := by
    rw [show R'.A = M.core.A from hRA]; linarith [M.core.hA2]
  -- structure
  obtain ⟨h0, hl0, hsy0, hf0, hp0⟩ := cd3_struct R' P P' V hga k t hval hab hPb
  -- sizes
  have hcW0 : 0 ≤ M.core.cWo := by linarith
  have hcg : 0 ≤ M.core.c * g := mul_nonneg hc2 hgp.le
  have hx1 : 0 ≤ M.core.cWo * (M.core.c * g) * (2 * s ^ 2 * bb) :=
    mul_nonneg (mul_nonneg hcW0 hcg) (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (norm_nonneg _))
  have hx2 : 0 ≤ M.core.cWo * (M.core.c * g) * (2 * s ^ 2 * bb') :=
    mul_nonneg (mul_nonneg hcW0 hcg) (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (norm_nonneg _))
  have hW := cd3_W R' P P' V k t hx1 hx2 hWP hWP'
  obtain ⟨ww, hwwd⟩ : ∃ x, x = M.core.cWo * (M.core.c * g) * (2 * s ^ 2 * bb) +
      M.core.cWo * (M.core.c * g) * (2 * s ^ 2 * bb') := ⟨_, rfl⟩
  rw [← hwwd] at hW
  have hww : 0 ≤ ww := by rw [hwwd]; exact add_nonneg hx1 hx2
  obtain ⟨k₁, hk₁d⟩ : ∃ x, x = 16 * M.core.cWo * M.core.Bk * (M.core.c * g) ^ 2 * (s ^ 2 * bb) :=
    ⟨_, rfl⟩
  obtain ⟨k₂, hk₂d⟩ : ∃ x, x = 16 * M.core.cWo * M.core.Bk * (M.core.c * g) ^ 2 * (s ^ 2 * bb') :=
    ⟨_, rfl⟩
  have hk₁0 : 0 ≤ k₁ := by
    rw [hk₁d]; exact mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hBk) (sq_nonneg _))
      (mul_nonneg (sq_nonneg _) (norm_nonneg _))
  have hk₂0 : 0 ≤ k₂ := by
    rw [hk₂d]; exact mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hBk) (sq_nonneg _))
      (mul_nonneg (sq_nonneg _) (norm_nonneg _))
  have hKP1 : KbHc R' P (obsInit .two V P) t k k₁ := by rw [hk₁d]; exact hKP
  have hKP2 : KbHc R' P' (obsInit .two V P') t k k₂ := by rw [hk₂d]; exact hKP'
  have hLp : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  obtain ⟨kk, hkkd⟩ : ∃ x, x = k₁ + k₂ + 2 * bb * (4 * s ^ 2 / (L : ℝ) ^ r) * ι * R'.A :=
    ⟨_, rfl⟩
  have hkk : 0 ≤ kk := by
    rw [hkkd]
    have : 0 ≤ 2 * bb * (4 * s ^ 2 / (L : ℝ) ^ r) * ι * R'.A :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _))
        (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (pow_nonneg (Nat.cast_nonneg _) _)))
        hι) (by linarith)
    linarith
  have hβs : ∑ b' ∈ blockIdx (L := L) (N := N) k, ‖cd3Beta R' P V k t b'‖ ≤ 2 * bb := by
    refine le_trans (le_of_eq ?_) hsh
    exact sum_congr rfl fun b' _ => by rw [cd3_mass]; rfl
  have hOo := obsHist_isObs R' P (obsInit .two V P) (obsInit_isObs .two V P) k t
  have hK0 := rr_delta_KbHF R' P' k t P.a P'.a (cd3Beta R' P V k t)
    (o := cd3O R' P V k t) (o' := cd3O R' P' V k t) hOo hk₁0 hk₂0 hι hA1 hKP1 hKP2 hI hKb hβs hsp
  have hK : KbHF R' P' k (cd3Delta R' P P' V k t) t k kk := by
    intro X hX
    refine (hK0 X hX).trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 := cd2_reloc_le (s := s) hLp hrk hdist
    have hA0 : 0 ≤ R'.A := by linarith
    have h3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left h1 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg
        (bt2 R P V m b μ₀ k)))) hι) hA0
    rw [hkkd]
    linarith only [h3]
  -- the envelope
  have hε0 : 0 ≤ M.core.ε := by
    obtain ⟨H, -, -⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm
    have := H.hε; linarith
  have hΓ := M.core.rdtΓ_nonneg hc2 hε0
  have hX : 0 ≤ 1344 * (8 * (PtCorr2.csN 2 : ℝ) * kk + M.core.rdtΓ * ww) :=
    mul_nonneg (by norm_num) (add_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (Nat.cast_nonneg _)) hkk) (mul_nonneg hΓ hww))
  have hb0 : 0 ≤ 4 * (M.csmK * (g + zA L m k)) * bb' +
      6 * (M.core.cδ * (M.core.c ^ 2 * (g / (betaL L / 4)))) * (bb + bb') := by
    refine add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hs0) (norm_nonneg _))
      (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hcδ (mul_nonneg (sq_nonneg _)
        (div_nonneg hgp.le (by linarith))))) (add_nonneg (norm_nonneg _) (norm_nonneg _)))
  have hgb : 0 < g * bb' := mul_pos hgp hbb0'
  have hMe : M.cd3M g (zA L m k) bb bb' s ι R'.A r =
      (4 * (M.csmK * (g + zA L m k)) * bb' +
        6 * (M.core.cδ * (M.core.c ^ 2 * (g / (betaL L / 4)))) * (bb + bb')) +
      1344 * (8 * (PtCorr2.csN 2 : ℝ) * kk + M.core.rdtΓ * ww) / s ^ 2 + g * bb' := by
    rw [hkkd, hwwd, hk₁d, hk₂d]; rfl
  have hXs : 0 ≤ 1344 * (8 * (PtCorr2.csN 2 : ℝ) * kk + M.core.rdtΓ * ww) / s ^ 2 :=
    div_nonneg hX (sq_nonneg _)
  have hM0 : 0 < M.cd3M g (zA L m k) bb bb' s ι R'.A r := by rw [hMe]; linarith
  have hM : 1344 * (8 * (PtCorr2.csN 2 : ℝ) * kk + M.core.rdtΓ * ww) ≤
      s ^ 2 * M.cd3M g (zA L m k) bb bb' s ι R'.A r := by
    rw [hMe]
    have e : s ^ 2 * (1344 * (8 * (PtCorr2.csN 2 : ℝ) * kk + M.core.rdtΓ * ww) / s ^ 2) =
        1344 * (8 * (PtCorr2.csN 2 : ℝ) * kk + M.core.rdtΓ * ww) := by
      field_simp
    have h1 := mul_nonneg (sq_nonneg s) hb0
    have h2 := mul_nonneg (sq_nonneg s) hgb.le
    generalize 1344 * (8 * (PtCorr2.csN 2 : ℝ) * kk + M.core.rdtΓ * ww) = X at e ⊢
    generalize 4 * (M.csmK * (g + zA L m k)) * bb' +
      6 * (M.core.cδ * (M.core.c ^ 2 * (g / (betaL L / 4)))) * (bb + bb') = B0 at h1 ⊢
    rw [mul_add, mul_add, e]
    linarith only [h1, h2]
  obtain ⟨hhb, hhd⟩ := cd3_hist_k R' P' k (cd3Delta R' P P' V k t) t
  have hdev := cd3_dev R' P P' V hga k t hab
  have hb : ‖betaTot2 (L := L) (N := N) k (histVF2 R' P' k (cd3Delta R' P P' V k t) t k)‖ +
      shareDev2 P'.a k (histVF2 R' P' k (cd3Delta R' P P' V k t) t k) ≤
      M.cd3M g (zA L m k) bb bb' s ι R'.A r := by
    rw [hhb, hhd, hMe]
    have h1 : ‖betaTot2 (L := L) (N := N) k (cd3Delta R' P P' V k t).V‖ ≤
        4 * (M.csmK * (g + zA L m k)) * bb' := hβδ
    refine le_trans (add_le_add h1 (hdev.trans (add_le_add hDP hDP'))) ?_
    rw [show 4 * (M.csmK * (g + zA L m k)) * bb' +
        (6 * (M.core.cδ * (M.core.c ^ 2 * (g / (betaL L / 4)))) * bb +
          6 * (M.core.cδ * (M.core.c ^ 2 * (g / (betaL L / 4)))) * bb') =
        4 * (M.csmK * (g + zA L m k)) * bb' +
          6 * (M.core.cδ * (M.core.c ^ 2 * (g / (betaL L / 4)))) * (bb + bb') by ring]
    exact le_add_of_le_of_nonneg (le_add_of_nonneg_right hXs) hgb.le
  exact M.core.restartDT_lin N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm.1 P' V k
    (cd3Delta R' P P' V k t) hk0 hkN.le h0 hl0 hsy0 hf0 hp0 hM0 hkk hww hb hW hK hg hM

end

end Spin2
