import Spin2.Pair.PairZeroAB3
import Spin2.Pair.PairEStep1
import PtCorr2.Restart.RestartPairChain3
import PtCorr2.Pair.PairDef5S
import Spin2.Pair.PairJoint6Def

set_option autoImplicit false

/-!
# T5, item (5)(iii), task 1: the crude per-block masses of the `ab` chain from its sizes

**`MasterCore.rpc8_massD`** (domain form): there are `C₁w ≥ 0` and `Λ₁ ≥ 0` (depending only on
the master constants and `L`) such that along every trajectory in `D_ε`, for every pair `P`, every
anchored, `U(1)`-invariant observable state `o₀` at `j₀` with `𝒲_{j₀} = 0`, constant weights
`M_a, M_b > 0`, a seed `A^{(|𝓑(X)|-4)_+}‖K_{j₀}(X)‖_{wM} ≤ k₀`, a target `m̄ > 0` with
`8k₀ ≤ vck(C₁w)(4C₁w+1)m̄`, and every `j₀ ≤ k ≤ N_h`:

  if `‖V_i(B)‖_{wM(M_a,M_b)} ≤ m̄` for `j₀ ≤ i ≤ k`, then for every `(k+1)`-block `B_+`
  `|m₂(V_{k+1}(B_+)_{ab})|·s_{k+1}² ≤ M_aM_b·Λ₁·m̄`.

Proof: the exact one-step identity `PtCorr2.rpc3_mass_Vnext` and `rpc3_mass_next_le`, with
`‖V_k(B)_{ab}‖_{T_k(s_k)} ≤ M_aM_bm̄` (the `wM` bound), the small-set `K` sizes and the
`S_k(B_+)` sizes of the chain (as in `MasterCore.vstepTopD`: `obs_histFromABL_wM`,
`kseqF_leL`, `hist_vstep_facts(T)`, `sxo_hist_ab_le(L)`), `Tj_Q2O_ab_le`, `GoodCov2 k s_k`
(`MasterCore.pairTrajD`) and `s_{k+1} ≤ (9/8)s_k`. This is the crude bound of the sources of
`rRX_flow` (no `β`-relative sizes, no Gronwall): one step at a time, a factor `Λ₁` per step.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2 Obs Obs2


section Pure

variable {L N : ℕ} [NeZero L]

/-- **The crude one-step defect of the `ab` constant** (`hDefR_k = -𝔡_k + X_k` of a reduced
step, `hDefR_eq`): with anchoring, no `σ_a` parts, `GoodCov2 k ℓ C`,
`‖V_k(B)_{ab}‖, ‖Q_k(B)_{ab}‖ ≤ v, q` in `T_k(ℓ)` and `‖S_k(B_+)_{ab}‖_{T_{k+1}(ℓ')} ≤ s`:
`|-𝔡_k + X_k| ≤ 2(Q₁+2)v + 2Q₁q + 2s`. The `ε`-tadpole `εF_C(V'(Λ)_{ab}, V'(Λ)_∅)` is
`∑_{B_+}εS(B_+)_{ab} − ∑_Bε(e^{ℒ_C}𝒲(B))_{ab}` (`SFO_ab_red`), and the `𝒲` sum cancels against
that of `wkAB2`; so no gradient and no `𝒲` sizes are needed. -/
theorem rpc8_def_le (P : ObsPts 2 L N) {k : ℕ} (hk : k < N)
    {C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ} {ℓ ℓ' v q s : ℝ} (hℓ : 0 < ℓ) (hℓ' : 0 < ℓ')
    (hv : 0 ≤ v) (hq : 0 ≤ q) (hs : 0 ≤ s) (hLp : pauliL0 2 ≤ L)
    (hC : GoodCov2 k ℓ C)
    {V W : OFam .two 2 L N} {K : OAct .two 2 L N} (H : OAnchS P k V W K)
    (hVa : ∀ b, (V b : SA .two (Lam 2 L N)).a = 0)
    (hVm : ∀ b, (V b : SA .two (Lam 2 L N)).ab ∈ NX ({P.a, P.b} : Set (Lam 2 L N)))
    (hVb : ∀ b ∈ blockIdx (L := L) (N := N) k,
      Tj 2 (L : ℝ) k ℓ (V b : SA .two (Lam 2 L N)).ab ≤ ENNReal.ofReal v)
    (hQb : ∀ b ∈ blockIdx (L := L) (N := N) k,
      Tj 2 (L : ℝ) k ℓ (Q2O P k K b : SA .two (Lam 2 L N)).ab ≤ ENNReal.ofReal q)
    (hSb : ∀ b ∈ blockIdx (L := L) (N := N) k,
      Tj 2 (L : ℝ) (k + 1) ℓ' (SXO k C V W (Step2.Bp (L := L) (N := N) k b) :
        SA .two (Lam 2 L N)).ab ≤ ENNReal.ofReal s) :
    ‖-pdefAB2 P k C V + xAB2 P k C V W K‖ ≤
      2 * ((Step2.Q1 2 + 2) * v) + 2 * (Step2.Q1 2 * q) + 2 * s := by
  classical
  have hQ1 := Step2.one_le_Q1 (d := 2) one_le_two
  have hQ0 : (0 : ℝ) ≤ Step2.Q1 2 := by linarith
  -- the `ε`-tadpole as an `S`-sum minus a `𝒲`-sum
  have hF : ε (FC C (VprLO k C V : SA .two (Lam 2 L N)).ab (VprLO k C V : SA .two (Lam 2 L N)).e) =
      ∑ c' ∈ blockIdx (L := L) (N := N) (k + 1),
        ε (SXO k C V W (blockSet (L := L) (N := N) (k + 1) c') : SA .two (Lam 2 L N)).ab -
      ∑ b ∈ blockIdx (L := L) (N := N) k, ε (EthO C (W b) : SA .two (Lam 2 L N)).ab := by
    have e1 : (VprLO k C V : SA .two (Lam 2 L N)).ab =
        ∑ b ∈ blockIdx (L := L) (N := N) k, (VprO C V b : SA .two (Lam 2 L N)).ab := by
      rw [VprLO, AddSubmonoidClass.coe_finsetSum, SA.sum_ab]
    rw [e1, Grassmann.FC_sum_left, map_sum]
    have e2 : ∀ b, ε (FC C (VprO C V b : SA .two (Lam 2 L N)).ab
        (VprLO k C V : SA .two (Lam 2 L N)).e) =
        ε (SbO k C V W b : SA .two (Lam 2 L N)).ab - ε (EthO C (W b) : SA .two (Lam 2 L N)).ab := by
      intro b
      rw [← SFO_ab_red k C V hVa b, SbO, Subalgebra.coe_add, SA.add_ab, map_add]
      ring
    rw [sum_congr rfl fun b _ => e2 b, sum_sub_distrib]
    congr 1
    rw [show (blockIdx (L := L) (N := N) k) = blocks k (univ : Finset (Lam 2 L N)) from rfl,
      show (blockIdx (L := L) (N := N) (k + 1)) = blocks (k + 1) (univ : Finset (Lam 2 L N))
        from rfl, ← Step2.sum_blocks_succ (isPolymer_univ (k + 1))]
    refine sum_congr rfl fun c' _ => ?_
    rw [SXO, AddSubmonoidClass.coe_finsetSum, SA.sum_ab, map_sum]
  -- the four pieces
  have hP : ‖pdefAB2 P k C V‖ ≤ 2 * ((Step2.Q1 2 + 2) * v) := by
    unfold pdefAB2
    refine norm_sum_two_le _ _ (blk k P.a) (blk k P.b) (mul_nonneg (by linarith) hv)
      (fun b _ h1 h2 => by
        rw [ab_eq_zero_of_anch P (H.hV b) h1 h2]
        simp [pauliDef]) fun b hb => ?_
    have e := eps_expLC_pauli C P.a (V b : SA .two (Lam 2 L N)).ab
    have hpd : pauliDef C P.a (V b : SA .two (Lam 2 L N)).ab =
        ε (expLC C (V b : SA .two (Lam 2 L N)).ab) - ε (V b : SA .two (Lam 2 L N)).ab -
          C P.a P.a * LocObs.mass2 (V b : SA .two (Lam 2 L N)).ab := by rw [e]; ring
    rw [hpd]
    have hT : (Tj 2 (L : ℝ) k ℓ (V b : SA .two (Lam 2 L N)).ab).toReal ≤ v :=
      ENNReal.toReal_le_of_le_ofReal hv (hVb b hb)
    have k1 : ‖ε (expLC C (V b : SA .two (Lam 2 L N)).ab)‖ ≤ Step2.Q1 2 * v :=
      (PtCorr2.norm_eps_expLC_le_pair one_le_two hLp hk hℓ hC P.a P.b (hVm b)).trans
        (mul_le_mul_of_nonneg_left hT hQ0)
    have k2 : ‖ε (V b : SA .two (Lam 2 L N)).ab‖ ≤ v := (norm_eps_le hℓ k _).trans hT
    have k3 : ‖C P.a P.a * LocObs.mass2 (V b : SA .two (Lam 2 L N)).ab‖ ≤ v := by
      rw [norm_mul]
      have hCe := good_entry hC P.a P.a
      have hm := norm_mass2_le hℓ k (V b : SA .two (Lam 2 L N)).ab
      have hm' : ‖LocObs.mass2 (V b : SA .two (Lam 2 L N)).ab‖ ≤ v * ℓ⁻¹ ^ 2 :=
        hm.trans (mul_le_mul_of_nonneg_right hT (by positivity))
      calc ‖C P.a P.a‖ * ‖LocObs.mass2 (V b : SA .two (Lam 2 L N)).ab‖ ≤ ℓ ^ 2 * (v * ℓ⁻¹ ^ 2) :=
            mul_le_mul hCe hm' (norm_nonneg _) (by positivity)
        _ = v := by field_simp
    calc _ ≤ ‖ε (expLC C (V b : SA .two (Lam 2 L N)).ab)‖ + ‖ε (V b : SA .two (Lam 2 L N)).ab‖ +
          ‖C P.a P.a * LocObs.mass2 (V b : SA .two (Lam 2 L N)).ab‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ Step2.Q1 2 * v + v + v := add_le_add (add_le_add k1 k2) k3
      _ = (Step2.Q1 2 + 2) * v := by ring
  have hQs : ‖∑ b ∈ blockIdx (L := L) (N := N) k,
      ε (expLC C (Q2O P k K b : SA .two (Lam 2 L N)).ab)‖ ≤ 2 * (Step2.Q1 2 * q) := by
    refine norm_sum_two_le _ _ (blk k P.a) (blk k P.b) (mul_nonneg hQ0 hq)
      (fun b _ h1 h2 => by rw [ab_eq_zero_of_anch P (H.Q2O_anch b) h1 h2, map_zero, map_zero])
      fun b hb => ?_
    have hT : (Tj 2 (L : ℝ) k ℓ (Q2O P k K b : SA .two (Lam 2 L N)).ab).toReal ≤ q :=
      ENNReal.toReal_le_of_le_ofReal hq (hQb b hb)
    exact (PtCorr2.norm_eps_expLC_le_pair one_le_two hLp hk hℓ hC P.a P.b
      (Q2O_ab_mem_pair P k K b)).trans (mul_le_mul_of_nonneg_left hT hQ0)
  have hSs : ‖∑ c' ∈ blockIdx (L := L) (N := N) (k + 1),
      ε (SXO k C V W (blockSet (L := L) (N := N) (k + 1) c') : SA .two (Lam 2 L N)).ab‖ ≤
      2 * s := by
    refine norm_sum_two_le _ _ (blk (k + 1) P.a) (blk (k + 1) P.b) hs
      (fun c' _ h1 h2 => ?_) fun c' hc' => ?_
    · rw [SXO, AddSubmonoidClass.coe_finsetSum, SA.sum_ab, map_sum]
      refine sum_eq_zero fun b hb => ?_
      have hsub : blockSet (L := L) (N := N) k b ⊆ blockSet (L := L) (N := N) (k + 1) c' :=
        blockSet_subset_of_mem_blocks (IsPolymer.of_succ (isPolymer_blockSet (k + 1) c')) hb
      rw [(H.Sb_anch (C := C) b).2.2 fun hne =>
        (eq_blk_of_inter P (hne.mono (inter_subset_inter_right hsub))).elim h1 h2, map_zero]
    · obtain ⟨p, -, hp⟩ := mem_blocks.1 hc'
      have hpb : blk k p ∈ blocks k (blockSet (L := L) (N := N) (k + 1) c') :=
        mem_blocks.2 ⟨p, mem_blockSet.2 hp, rfl⟩
      have hS := hSb (blk k p) (blocks_subset_blockIdx _ hpb)
      rw [Bp_eq_of_mem hpb] at hS
      exact (norm_eps_le hℓ' (k + 1) _).trans (ENNReal.toReal_le_of_le_ofReal hs hS)
  unfold xAB2 wkAB2
  rw [Obs2.farAB_eq_zero_of_anch (C := C) H, sub_zero, hF]
  have e : -pdefAB2 P k C V +
      (∑ b ∈ blockIdx (L := L) (N := N) k, ε (expLC C (Q2O P k K b : SA .two (Lam 2 L N)).ab) +
        ∑ b ∈ blockIdx (L := L) (N := N) k, ε (EthO C (W b) : SA .two (Lam 2 L N)).ab +
      (∑ c' ∈ blockIdx (L := L) (N := N) (k + 1),
        ε (SXO k C V W (blockSet (L := L) (N := N) (k + 1) c') : SA .two (Lam 2 L N)).ab -
      ∑ b ∈ blockIdx (L := L) (N := N) k, ε (EthO C (W b) : SA .two (Lam 2 L N)).ab)) =
      -pdefAB2 P k C V +
        ∑ b ∈ blockIdx (L := L) (N := N) k, ε (expLC C (Q2O P k K b : SA .two (Lam 2 L N)).ab) +
        ∑ c' ∈ blockIdx (L := L) (N := N) (k + 1),
          ε (SXO k C V W (blockSet (L := L) (N := N) (k + 1) c') : SA .two (Lam 2 L N)).ab := by
    ring
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add (by rw [norm_neg]; exact hP) hQs)) hSs)

end Pure

/-- The per-step defect constant of `MasterCore.rpc8_massD`. -/
def rpc8Lam2 {L : ℕ} [NeZero L] (D : MasterCore L) (CQ C₁w : ℝ) : ℝ :=
  2 * (Step2.Q1 2 + 2) + 2 * (Step2.Q1 2 * (CQ * (vck C₁w * (4 * C₁w + 1)))) +
    2 * ((L : ℝ) ^ 2 * (2 * Step2.cNear 2 L * Step2.Q1 2 ^ 2 * (D.c * D.ε) +
      Step2.Q1 2 * ((4 * C₁w + 1) * (D.c * D.ε))))

/-- The per-step mass constant of `MasterCore.rpc8_massD`. -/
def rpc8Lam {L : ℕ} [NeZero L] (D : MasterCore L) (CQ C₁w : ℝ) : ℝ :=
  2 * Step2.Q1 2 * (1 + CQ * (vck C₁w * (4 * C₁w + 1))) * (81 / 64) +
    (L : ℝ) ^ 2 * (2 * Step2.cNear 2 L * Step2.Q1 2 ^ 2 * (D.c * D.ε) +
      Step2.Q1 2 * ((4 * C₁w + 1) * (D.c * D.ε)))

set_option maxHeartbeats 8000000 in
/-- **The crude per-block masses of the `ab` chain** (domain form). -/
theorem MasterCore.rpc8_massD {L : ℕ} [NeZero L] (D : MasterCore L) :
    ∃ C₁w Λ₁ Λ₂ : ℝ, 0 ≤ C₁w ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = D.ℓ → R.A = D.A → R.ρ = D.ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
    ∀ m ∈ mRange L N, ∀ b μ₀, (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) D.κ D.cm D.cT D.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) →
    ∀ (P : Obs2.ObsPts 2 L N) (Ma Mb : ℝ), 0 < Ma → 0 < Mb →
    ∀ (j₀ : ℕ) (o₀ : ObsSt .two L N), o₀.IsObs → ObsLocInv P j₀ o₀ → ObsSymInv j₀ o₀ →
      ObsAnchInv P j₀ o₀ → ObsVabInv P o₀ → (∀ b', o₀.W b' = 0) →
    ∀ k₀ : ℝ, 0 ≤ k₀ →
    (∀ X, IsConn j₀ X → ENNReal.ofReal ((R.withMsq m).A ^ (nb j₀ X - 2 ^ 2)) *
      oTo (wM Ma Mb) j₀
        (histS (R.withMsq m) j₀ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) (o₀.K X) ≤
        ENNReal.ofReal k₀) →
    ∀ mbar : ℝ, 0 < mbar → 8 * k₀ ≤ vck C₁w * ((4 * C₁w + 1) * mbar) →
    ∀ k, j₀ ≤ k → k ≤ Nh →
    (∀ i, j₀ ≤ i → i ≤ k → ∀ b' ∈ blockIdx (L := L) (N := N) i,
      oTo (wM Ma Mb) i (histS (R.withMsq m) i (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((obsHistFrom (R.withMsq m) P j₀ o₀ i (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).V b') ≤
        ENNReal.ofReal mbar) →
    (∀ c' : Fin 2 → ℕ,
      ‖LocObs.mass2 ((obsHistFrom (R.withMsq m) P j₀ o₀ (k + 1)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).V c' : SA .two (Lam 2 L N)).ab‖ *
        (histS (R.withMsq m) (k + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) *
          histS (R.withMsq m) (k + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) ≤
        Ma * Mb * (Λ₁ * mbar)) ∧
    ‖-pdefAB2 P k (histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)
        (hVR (R.withMsq m) P j₀ o₀ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k) +
      xAB2 P k (histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)
        (hVR (R.withMsq m) P j₀ o₀ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)
        (hWR (R.withMsq m) P j₀ o₀ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)
        (hKR (R.withMsq m) P j₀ o₀ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)‖ ≤
      Ma * Mb * (Λ₂ * mbar) := by
  obtain ⟨CQ, hCQ, hQ2O⟩ := PtCorr2.Tj_Q2O_ab_le (d := 2) one_le_two
  obtain ⟨hθa0, hθa⟩ : 0 ≤ kθ0 L D.A D.C₀a D.ηa ∧ kθ0 L D.A D.C₀a D.ηa ≤ 1 / 72 := by
    refine ⟨?_, (D.hAa D.hLa).2⟩
    unfold kθ0
    have := D.hA2
    exact mul_nonneg D.hC₀a (add_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _))
  obtain ⟨ε₀, C₁k, hε₀, hC₁k, hKB, hsm, hεε, hεk, hBr, C₁w, ε₁, hC₁w, hε₁, hWB, hC₁ε, hε₁',
    hA2v, hBrv⟩ := D.hEv D.hLa D.hAa
  have hQ10 : (0 : ℝ) ≤ Step2.Q1 2 := by have := Step2.one_le_Q1 (d := 2) one_le_two; linarith
  have hcN0 : (0 : ℝ) ≤ Step2.cNear 2 L := by unfold Step2.cNear; exact Nat.cast_nonneg _
  have hvck := vck_le_one hC₁w
  have hvck0 := vck_pos hC₁w
  have hcW0 : 0 < 4 * C₁w + 1 := by linarith
  refine ⟨C₁w, rpc8Lam D CQ C₁w, rpc8Lam2 D CQ C₁w, hC₁w, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hD P Ma Mb hMa hMb j₀ o₀
    h0 hl0 hs0 ha0 hvab hW0z k₀ hk₀ hK0 mbar hmbar h8 k hjk hkN hVo
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8, -, hCN⟩ := id D.hC2
  set R' := R.withMsq m with hR'
  obtain ⟨H, hm1, F1⟩ := D.hXm N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm
  obtain ⟨hV, hVL⟩ := (hCN N R hP hi0 hRℓ hRA hRρ hN Nh hNh).2.2.2.2.2.2.2.2.2 m hm
  obtain ⟨-, -, hGC, -⟩ := D.pairTrajD N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hD
  have hmN : |R'.msq| * ((L : ℝ) ^ Nh) ^ 2 ≤ 1 := by
    have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by have := D.hL49; omega)
    have h1 := msq_horizon (L := (L : ℝ)) (by linarith only [hL2]) hm.2 (Nh := Nh) (k := 0)
      (by omega)
    simp only [pow_zero, one_pow, inv_one] at h1
    show |m| * ((L : ℝ) ^ Nh) ^ 2 ≤ 1
    rw [abs_of_pos hm.1]
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hm.1.le) h1
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by linarith only [hL2]) (by omega)) 2
  have hRA' : R'.A = D.A := hRA
  have hcR : cR R' ((L : ℝ) ^ 2) D.cm D.C₂x = D.c := by
    rw [D.hc]; exact cR_congr (show R.ℓ = D.ℓ from hRℓ) _ _ _
  have hSB' : StepBounds L R'.A D.C₀x D.ηx D.εsx D.CKx D.C₂x D.CDx D.Cqx D.Clx D.cSx := by
    rw [hRA']; exact D.hSBx
  have hβ2 := betaL_ge (by have := D.hL49; omega : 8 ≤ L)
  have hβ0 : 0 ≤ betaL L := by linarith
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  have ht := inDh_rg_of_D R' F1 hD k hkN
  have hti : ∀ i ≤ Nh, Flow2.Hist.InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) D.κ D.cg D.cm D.cT D.ε i t :=
    fun i hi => inDh_rg_of_D R' F1 hD i hi
  have hKB' : KObsBoundsABL L R'.A D.C₀a D.ηa ε₀ C₁k := by rw [hRA']; exact hKB
  have hθa0' : 0 ≤ kθ0 L R'.A D.C₀a D.ηa := by rw [hRA']; exact hθa0
  have hθa' : kθ0 L R'.A D.C₀a D.ηa ≤ 1 / 72 := by rw [hRA']; exact hθa
  have hBr' : 32 * kB (kθ0 L R'.A D.C₀a D.ηa) C₁k (8 * cx D.κ D.cT) *
      (cR R' ((L : ℝ) ^ 2) D.cm D.C₂x * D.ε) ^ 2 ≤ 1 := by rw [hRA', hcR]; exact hBr
  -- constant weights
  have hMa' : ∀ j, 0 < (fun _ : ℕ => Ma) j := fun _ => hMa
  have hMb' : ∀ j, 0 < (fun _ : ℕ => Mb) j := fun _ => hMb
  have hm' : ∀ j, j₀ ≤ j → j < k → (fun _ : ℕ => Ma) j * (fun _ : ℕ => Mb) j /
      ((fun _ : ℕ => Ma) j₀ * (fun _ : ℕ => Mb) j₀) * (fun _ : ℕ => mbar) j ≤
      2 * ((fun _ : ℕ => Ma) (j + 1) * (fun _ : ℕ => Mb) (j + 1) /
        ((fun _ : ℕ => Ma) j₀ * (fun _ : ℕ => Mb) j₀) * (fun _ : ℕ => mbar) (j + 1)) := by
    intro j _ _
    have : 0 ≤ Ma * Mb / (Ma * Mb) * mbar := by positivity
    dsimp only; linarith
  have hW0' : ∀ b' ∈ blockIdx (L := L) (N := N) j₀, oTo (wM ((fun _ : ℕ => Ma) j₀)
      ((fun _ : ℕ => Mb) j₀)) j₀ (histS R' j₀ t) (o₀.W b') ≤ ENNReal.ofReal ((4 * C₁w + 1) *
        (cR R' ((L : ℝ) ^ 2) D.cm D.C₂x * (t j₀).1) * (fun _ : ℕ => mbar) j₀) := by
    intro b' _
    rw [hW0z b', oTo_zero']; exact bot_le
  have h8' : 8 * k₀ ≤ 1 * ((4 * C₁w + 1) * (fun _ : ℕ => mbar) j₀) := by
    have : vck C₁w * ((4 * C₁w + 1) * mbar) ≤ 1 * ((4 * C₁w + 1) * mbar) :=
      mul_le_mul_of_nonneg_right hvck (by positivity)
    exact h8.trans this
  have hM := obs_histFromABL_wM R' hKB' hC₁k 1 zero_le_one hWB hC₁w hSB' hV hm1 hβ0
    (by norm_num : (1 / 2 : ℝ) ≤ 1) H P (fun _ => Ma) (fun _ => Mb) hMa' hMb' o₀ h0 hl0 hs0 ha0
    t k hkN ht hθa0' hθa' (by rw [hcR]; exact hsm)
    (by rw [hcR]; exact D.hcε) (by rw [hcR]; exact hεε) (by rw [hcR]; exact hεk) hBr' D.hLwa
    (by rw [hcR]; exact hC₁ε) (by rw [hcR]; exact hε₁') (fun _ => mbar) (fun _ => hmbar) hm'
    (fun j hj hjn => hVo j hj hjn.le) hW0' k₀ hk₀ hK0 h8'
  -- notation of the chain
  set θb := kθ0 L R'.A D.C₀a D.ηa + C₁k * (2 + 2 * (8 * cx D.κ D.cT) + 1) *
    (cR R' ((L : ℝ) ^ 2) D.cm D.C₂x * D.ε) with hθbd
  set B := kB (kθ0 L R'.A D.C₀a D.ηa) C₁k (8 * cx D.κ D.cT) with hBd
  set r := fun j => cR R' ((L : ℝ) ^ 2) D.cm D.C₂x * (t j).1 with hrd
  set cWc := 4 * C₁w + 1 with hcWc
  set lamM := fun i => (fun _ : ℕ => Ma) i * (fun _ : ℕ => Mb) i /
    ((fun _ : ℕ => Ma) j₀ * (fun _ : ℕ => Mb) j₀) with hlamM
  have hcR0 : 0 ≤ cR R' ((L : ℝ) ^ 2) D.cm D.C₂x := by
    unfold cR cV cW cZ; have := H.hcmu; have := H.hC₂; positivity
  have hcε : 0 ≤ D.c * D.ε := by rw [← hcR]; exact mul_nonneg hcR0 H.hε.le
  have hr0 : ∀ i ≤ k, 0 ≤ r i := fun i hi => mul_nonneg hcR0 (ht.1 i hi).1.le
  have hrε : ∀ i ≤ k, r i ≤ D.c * D.ε := fun i hi => by
    rw [← hcR]; exact mul_le_mul_of_nonneg_left (ht.1 i hi).2.1 hcR0
  have hθb : 8 * θb ≤ 2 / 9 := by
    have h1 : C₁k * (2 + 2 * (8 * cx D.κ D.cT) + 1) * (cR R' ((L : ℝ) ^ 2) D.cm D.C₂x * D.ε) ≤
        1 / 72 := by rw [hcR]; exact hsm
    rw [hθbd]; linarith
  have hθb0 : 0 ≤ θb := by
    have : 0 ≤ C₁k * (2 + 2 * (8 * cx D.κ D.cT) + 1) * (cR R' ((L : ℝ) ^ 2) D.cm D.C₂x * D.ε) := by
      have := H.hcx; have := H.hε; positivity
    rw [hθbd]; linarith
  have hB0 : 0 ≤ B := by
    have hcb : 0 ≤ 8 * cx D.κ D.cT := by have := H.hcx; positivity
    have h1 := mul_nonneg hθa0' hcb
    have h2 := mul_nonneg hC₁k (by positivity : (0 : ℝ) ≤ 8 + 2 * (8 * cx D.κ D.cT) +
      (8 * cx D.κ D.cT) ^ 2)
    rw [hBd]; unfold kB; linarith
  have hBrv' : 32 * B * (D.c * D.ε) ^ 2 ≤ vck C₁w := by
    rw [hBd, hRA']; exact hBrv
  have hlam1 : ∀ i, lamM i = 1 := fun i => div_self (mul_pos hMa hMb).ne'
  have hkL := kseqF_leL (θ := 8 * θb) (B := B) (ck := vck C₁w) (r := r)
    (m := fun i => cWc * (lamM i * (fun _ : ℕ => mbar) i)) (j₀ := j₀) (k₀ := k₀) k
    (by positivity) hB0 hvck0.le
    (fun i => mul_nonneg hcW0.le (mul_nonneg (by rw [hlam1 i]; exact zero_le_one) hmbar.le))
    (fun j hj hjn => by
      have h1 : 8 * θb * vck C₁w ≤ 2 / 9 * vck C₁w := mul_le_mul_of_nonneg_right hθb hvck0.le
      have hr2 : r j ^ 2 ≤ (D.c * D.ε) ^ 2 :=
        pow_le_pow_left₀ (hr0 j hjn.le) (hrε j hjn.le) 2
      have h2 : 8 * B * r j ^ 2 ≤ 8 * B * (D.c * D.ε) ^ 2 := mul_le_mul_of_nonneg_left hr2 (by positivity)
      linarith)
    (fun j hj hjn => by
      show cWc * (lamM j * mbar) ≤ 2 * (cWc * (lamM (j + 1) * mbar))
      simp only [hlam1]
      have : 0 ≤ cWc * (1 * mbar) := by positivity
      linarith)
    (by
      show 8 * k₀ ≤ vck C₁w * (cWc * (lamM j₀ * mbar))
      rw [hlam1 j₀, one_mul]; exact h8)
  -- the step facts at `k`
  have hF := if h : k < Nh then
      hist_vstep_facts R' hSB' hV hm1 hβ0 (by norm_num : (1 / 2 : ℝ) ≤ 1) H P o₀ hl0 hs0
        ha0 t k hjk h ht
    else
      hist_vstep_factsT R' hSB' hV hm1 hβ0 (by norm_num : (1 / 2 : ℝ) ≤ 1) H P o₀ hl0 hs0
        ha0 hVL hmN t k hjk (by omega) ht
  obtain ⟨-, hs0', hs1', -, hAnch, hKloc, -, hKsm⟩ := hF
  -- the small-set `K` sizes at `k`
  set Q₀ := vck C₁w * (cWc * mbar) with hQ₀
  have hQ₀0 : 0 ≤ Q₀ := by positivity
  have hK : ∀ X, IsSmall k X →
      Tj 2 (L : ℝ) k (histS R' k t) (hKR R' P j₀ o₀ t k X : SA .two (Lam 2 L N)).ab ≤
        ENNReal.ofReal (Ma * Mb * Q₀) := by
    intro X hX
    have hKi := hKsm (wM Ma Mb) (wM_sub _ _) _ (hM k hjk le_rfl).2.2 X hX
    have hT := Tj_ab_le_of_oTo_wM' hMa hMb k (histS R' k t) (hKR R' P j₀ o₀ t k X) hKi
    refine hT.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (mul_pos hMa hMb).le))
    have h1 := hkL k hjk le_rfl
    rw [hlam1 k, div_one]
    calc 8 * kseqF (8 * θb) B r (fun i => cWc * (lamM i * (fun _ : ℕ => mbar) i)) j₀ k₀ k
        ≤ vck C₁w * (cWc * (lamM k * mbar)) := h1
      _ = Q₀ := by rw [hQ₀, hlam1 k, one_mul]
  have hQb : ∀ b' ∈ blockIdx (L := L) (N := N) k,
      Tj 2 (L : ℝ) k (histS R' k t) (Q2O P k (hKR R' P j₀ o₀ t k) b' : SA .two (Lam 2 L N)).ab ≤
        ENNReal.ofReal (CQ * (Ma * Mb * Q₀)) := fun b' _ =>
    hQ2O L (by have := D.hL49; omega) N P k (by omega) (histS R' k t) hs0' _ _ _ hAnch _
      (by positivity) hKloc hK b'
  -- the `S` sizes at `k`
  set S₀ := (L : ℝ) ^ 2 * sO 2 L (D.c * D.ε) mbar (cWc * (D.c * D.ε) * mbar) with hS₀
  have hS : ∀ b' ∈ blockIdx (L := L) (N := N) k,
      Tj 2 (L : ℝ) (k + 1) (histS R' (k + 1) t)
        (SXO k (histCovO R' t k) (hVR R' P j₀ o₀ t k) (hWR R' P j₀ o₀ t k)
          (Step2.Bp (L := L) (N := N) k b') : SA .two (Lam 2 L N)).ab ≤
        ENNReal.ofReal (Ma * Mb * S₀) := by
    intro b' hb'
    have hWi := (hM k hjk le_rfl).2.1
    have H' := if h : k < Nh then (sxo_hist_ab_le R' D.hSX hSB' hV hm1 hβ0 (by norm_num : (1 / 2 : ℝ) ≤ 1) H P
      hMa hMb o₀ h0 hl0 hs0 ha0 t k hjk h ht mbar (cWc * r k * mbar)
      hmbar.le (by have := hr0 k le_rfl; positivity) (hVo k hjk le_rfl) hWi b' hb').1
    else by
      obtain rfl : k = Nh := by omega
      exact (sxo_hist_ab_leL R' D.hSX hSB' hV hm1 hβ0 (by norm_num : (1 / 2 : ℝ) ≤ 1) H hVL hmN P
        hMa hMb o₀ h0 hl0 hs0 ha0 t hjk ht mbar (cWc * r k * mbar)
        hmbar.le (by have := hr0 k le_rfl; positivity) (hVo k hjk le_rfl) hWi b' hb').1
    refine H'.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (mul_pos hMa hMb).le))
    rw [hS₀]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    unfold sO
    have hri := hrε k le_rfl
    have h1 : cR R' ((L : ℝ) ^ 2) D.cm D.C₂x * (t k).1 * mbar ≤ D.c * D.ε * mbar :=
      mul_le_mul_of_nonneg_right hri hmbar.le
    have h2 : cWc * r k * mbar ≤ cWc * (D.c * D.ε) * mbar :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hri hcW0.le) hmbar.le
    have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * Step2.cNear 2 L * Step2.Q1 2 ^ 2)
    have h4 := mul_le_mul_of_nonneg_left h2 hQ10
    linarith
  have hS₀0 : 0 ≤ S₀ := by
    rw [hS₀]; unfold sO
    generalize Step2.Q1 2 = q at *
    generalize Step2.cNear 2 L = cn at *
    positivity
  -- the `V` sizes at `k`
  have hVb : ∀ b' ∈ blockIdx (L := L) (N := N) k,
      Tj 2 (L : ℝ) k (histS R' k t) (hVR R' P j₀ o₀ t k b' : SA .two (Lam 2 L N)).ab ≤
        ENNReal.ofReal (Ma * Mb * mbar) := by
    intro b' hb'
    rw [hVR_ab]
    exact Tj_ab_le_of_oTo_wM' hMa hMb k (histS R' k t) _ (hVo k hjk le_rfl b' hb')
  -- the defect
  have hdef := rpc8_def_le P (k := k) (by omega) hs0' hs1'
    (by positivity : (0 : ℝ) ≤ Ma * Mb * mbar)
    (mul_nonneg hCQ (mul_nonneg (mul_pos hMa hMb).le hQ₀0)) (mul_nonneg (mul_pos hMa hMb).le hS₀0)
    D.hLpl (hGC k hkN) hAnch (fun b' => (hAnch.toAb.hV b').1) (hVR_ab_mem R' P j₀ o₀ t hvab k)
    hVb hQb hS
  refine ⟨fun c' => ?_, hdef.trans (le_of_eq ?_)⟩
  swap
  · rw [hS₀, hQ₀]
    unfold rpc8Lam2 sO
    ring
  -- the one-step bound
  have hmass := PtCorr2.rpc3_mass_next_le (d := 2) one_le_two D.hLpl P
    (k := k) (by omega) (ℓ' := histS R' (k + 1) t) hs0' hs1' (by positivity)
    (mul_nonneg hCQ (mul_nonneg (mul_pos hMa hMb).le hQ₀0)) (mul_nonneg (mul_pos hMa hMb).le hS₀0) (hGC k hkN) hAnch (hVR_ab_mem R' P j₀ o₀ t hvab k) hVb hQb hS c'
  have e := (hVR_succ_ab (R := R') (P := P) (j := j₀) (o' := o₀) (t := t) hjk c').symm.trans
    (hVR_ab R' P j₀ o₀ t (k + 1) c')
  have hmass' : ‖LocObs.mass2 ((obsHistFrom R' P j₀ o₀ (k + 1) t).V c' :
      SA .two (Lam 2 L N)).ab‖ ≤ 2 * (Step2.Q1 2 * (Ma * Mb * mbar + CQ * (Ma * Mb * Q₀)) *
        (histS R' k t)⁻¹ ^ 2) + Ma * Mb * S₀ * (histS R' (k + 1) t)⁻¹ ^ 2 := by
    rw [← e]; exact hmass
  have hρ0' : 0 ≤ R'.ρ := by rw [show R'.ρ = D.ρ from hRρ]; linarith
  have hρ8' : R'.ρ ≤ 1 / 8 := by rw [show R'.ρ = D.ρ from hRρ]; linarith
  have hsr := histS_succ_le_q R' hρ0' hρ8' t k
  set s := histS R' k t with hsd
  set s1 := histS R' (k + 1) t with hs1d
  have key := mul_le_mul_of_nonneg_right hmass' (by positivity : (0 : ℝ) ≤ s1 * s1)
  refine le_trans (le_of_eq ?_) (key.trans ?_)
  · rfl
  have hratio : (s1 * s1) * s⁻¹ ^ 2 ≤ 81 / 64 := by
    rw [inv_pow, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    nlinarith [hsr, hs1'.le]
  have e1 : Ma * Mb * S₀ * s1⁻¹ ^ 2 * (s1 * s1) = Ma * Mb * S₀ := by
    field_simp
  have hvq : 0 ≤ 2 * Step2.Q1 2 * (Ma * Mb * mbar + CQ * (Ma * Mb * Q₀)) := by positivity
  have h2 : 2 * (Step2.Q1 2 * (Ma * Mb * mbar + CQ * (Ma * Mb * Q₀)) * s⁻¹ ^ 2) * (s1 * s1) ≤
      2 * Step2.Q1 2 * (Ma * Mb * mbar + CQ * (Ma * Mb * Q₀)) * (81 / 64) := by
    have e : 2 * (Step2.Q1 2 * (Ma * Mb * mbar + CQ * (Ma * Mb * Q₀)) * s⁻¹ ^ 2) * (s1 * s1) =
        2 * Step2.Q1 2 * (Ma * Mb * mbar + CQ * (Ma * Mb * Q₀)) * ((s1 * s1) * s⁻¹ ^ 2) := by ring
    rw [e]; exact mul_le_mul_of_nonneg_left hratio hvq
  rw [add_mul, e1]
  refine (add_le_add h2 le_rfl).trans (le_of_eq ?_)
  rw [hS₀, hQ₀]
  unfold rpc8Lam sO
  ring

end

end Spin2
