import Spin2.Restart.RestartPairChain8
import Spin2.Restart.RestartPairChain7

set_option autoImplicit false

/-!
# T5, item (5)(iii), task 1: the joint induction for the reduced chain of a general seed

Pair `(0, x)`, `1 ≤ j_x ≤ N_h`, a general observable state `o` at `j_x` (local, `U(1)`-invariant),
`o' = rpcRed o`, constant weights `wM(M_a, M_b)`, the seed `k₀` of `o'` in these weights.

**`rpc9_chainD`**: there are `C₁v, C₁m ≥ 0` and `Λ₁, Λ₂` (master constants and `L` only) such
that, with `Λ₀ = max(1, 2Λ₁)` and the growing targets `m̄_i = Λ₀^i·m̄₀` (`rpc9Mb`), for every
`m̄₀ > 0` with `8k₀ ≤ vck(C)(4C+1)m̄₀` (`C = C₁v, C₁m`):

* `‖V_n(B)‖_{wM} ≤ m̄_{n−j_x}` for `j_x ≤ n ≤ N_h`;
* the per-block masses: `|m₂(V_n(B)_{ab})|·s_n² ≤ M_aM_bΛ₁m̄_{n−1−j_x}` for `j_x < n ≤ N_h + 1`;
* the per-step defects: `|−𝔡_k + X_k| ≤ M_aM_bΛ₂m̄_{k−j_x}` for `j_x ≤ k ≤ N_h`.

Joint induction over `≤ N_h + 1 − j_x` steps: the `V`-step `MasterCore.vstepD` at scale `n + 1`
with target `m̄_{n+1−j_x}` takes the mass `ρ_{n+1} = M_aM_bΛ₁m̄_{n−j_x}/s_{n+1}²` from
`MasterCore.rpc8_massD` at `n` (target `m̄_{n−j_x}`), and `Λ₁m̄_{n−j_x} ≤ m̄_{n+1−j_x}/2`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs2

/-- The growing targets `m̄_i = max(1, 2Λ₁)^i·m̄₀`. -/
def rpc9Mb (Λ₁ m0 : ℝ) (i : ℕ) : ℝ := (max 1 (2 * Λ₁)) ^ i * m0

theorem rpc9Mb_pos {Λ₁ m0 : ℝ} (hm0 : 0 < m0) (i : ℕ) : 0 < rpc9Mb Λ₁ m0 i :=
  mul_pos (pow_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) _) hm0

theorem rpc9Mb_mono {Λ₁ m0 : ℝ} (hm0 : 0 < m0) {i i' : ℕ} (h : i ≤ i') :
    rpc9Mb Λ₁ m0 i ≤ rpc9Mb Λ₁ m0 i' :=
  mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (le_max_left _ _) h) hm0.le

theorem rpc9Mb_ge {Λ₁ m0 : ℝ} (hm0 : 0 < m0) (i : ℕ) : m0 ≤ rpc9Mb Λ₁ m0 i := by
  have := rpc9Mb_mono (Λ₁ := Λ₁) hm0 (Nat.zero_le i)
  simpa [rpc9Mb] using this

theorem rpc9Mb_succ {Λ₁ m0 : ℝ} (hm0 : 0 < m0) (i : ℕ) :
    Λ₁ * rpc9Mb Λ₁ m0 i ≤ rpc9Mb Λ₁ m0 (i + 1) / 2 := by
  have hp := (rpc9Mb_pos (Λ₁ := Λ₁) hm0 i).le
  have e : rpc9Mb Λ₁ m0 (i + 1) = max 1 (2 * Λ₁) * rpc9Mb Λ₁ m0 i := by
    unfold rpc9Mb; ring
  rw [e]
  have := mul_le_mul_of_nonneg_right (le_max_right 1 (2 * Λ₁)) hp
  linarith

theorem rpc9_seed {C k₀ m0 x : ℝ} (hC : 0 ≤ C) (h : 8 * k₀ ≤ vck C * ((4 * C + 1) * m0))
    (hx : m0 ≤ x) : 8 * k₀ ≤ vck C * ((4 * C + 1) * x) :=
  h.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx (by linarith))
    (vck_pos hC).le)

set_option maxHeartbeats 8000000 in
/-- **The joint induction for the reduced chain of a general state** (domain form). -/
theorem rpc9_chainD {L : ℕ} [NeZero L] (M : MasterFacts L) :
    ∃ C₁v C₁m Λ₁ Λ₂ : ℝ, 0 ≤ C₁v ∧ 0 ≤ C₁m ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
    ∀ m ∈ mRange L N, ∀ b μ₀,
      (∀ jD ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ jD)) →
    ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∀ o : ObsSt .two L N, o.IsObs → ObsLocInv (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) o →
      ObsSymInv (Obs.coal L (0 : Lam 2 L N) x) o →
    ∀ Ma Mb : ℝ, 0 < Ma → 0 < Mb → ∀ k₀ : ℝ, 0 ≤ k₀ →
    (∀ X, IsConn (Obs.coal L (0 : Lam 2 L N) x) X →
      ENNReal.ofReal ((R.withMsq m).A ^ (nb (Obs.coal L (0 : Lam 2 L N) x) X - 2 ^ 2)) *
        oTo (wM Ma Mb) (Obs.coal L (0 : Lam 2 L N) x)
          (histS (R.withMsq m) (Obs.coal L (0 : Lam 2 L N) x)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          ((rpcRed R m b μ₀ x o).K X) ≤ ENNReal.ofReal k₀) →
    ∀ m0 : ℝ, 0 < m0 → 8 * k₀ ≤ vck C₁v * ((4 * C₁v + 1) * m0) →
      8 * k₀ ≤ vck C₁m * ((4 * C₁m + 1) * m0) →
    (∀ n, Obs.coal L (0 : Lam 2 L N) x ≤ n → n ≤ Nh → ∀ c ∈ blockIdx (L := L) (N := N) n,
      oTo (wM Ma Mb) n (histS (R.withMsq m) n (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((obsHistFrom (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x)
          (rpcRed R m b μ₀ x o) n (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).V c) ≤
        ENNReal.ofReal (rpc9Mb Λ₁ m0 (n - Obs.coal L (0 : Lam 2 L N) x))) ∧
    (∀ n, Obs.coal L (0 : Lam 2 L N) x < n → n ≤ Nh + 1 → ∀ c : Fin 2 → ℕ,
      ‖LocObs.mass2 ((obsHistFrom (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x)
        (rpcRed R m b μ₀ x o) n (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).V c :
          SA .two (Lam 2 L N)).ab‖ *
        (histS (R.withMsq m) n (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) *
          histS (R.withMsq m) n (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) ≤
        Ma * Mb * (Λ₁ * rpc9Mb Λ₁ m0 (n - 1 - Obs.coal L (0 : Lam 2 L N) x))) ∧
    (∀ k, Obs.coal L (0 : Lam 2 L N) x ≤ k → k ≤ Nh →
      ‖-pdefAB2 (ptsX x) k (histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)
          (hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (rpcRed R m b μ₀ x o)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k) +
        xAB2 (ptsX x) k (histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)
          (hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (rpcRed R m b μ₀ x o)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)
          (hWR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (rpcRed R m b μ₀ x o)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)
          (hKR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (rpcRed R m b μ₀ x o)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)‖ ≤
        Ma * Mb * (Λ₂ * rpc9Mb Λ₁ m0 (k - Obs.coal L (0 : Lam 2 L N) x))) := by
  obtain ⟨C₁v, hC₁v, hVS⟩ := M.core.vstepD
  obtain ⟨C₁m, Λ₁, Λ₂, hC₁m, hMS⟩ := M.core.rpc8_massD
  refine ⟨C₁v, C₁m, Λ₁, Λ₂, hC₁v, hC₁m, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD x hx h1 hj o ho hlo hso Ma Mb hMa hMb
    k₀ hk₀ hK0 m0 hm0 h8v h8m
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  set t : Hist.Seq (Xs (R.withMsq m)) := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  obtain ⟨hV, hVL, -, hRI⟩ := M.core.pairTrajD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD
  have hρ0 : 0 ≤ (R.withMsq m).ρ := (hRI 0 (Nat.zero_le _)).1.2.2.2.1
  have hρ8 : (R.withMsq m).ρ ≤ 1 / 8 := ((hRI 0 (Nat.zero_le _)).1).2.2.2.2.1
  -- the path from `0` to `x`
  obtain ⟨w, hwx, hwl⟩ := PtCorr2.exists_path_sum (n := L ^ N) (x : Lam 2 L N)
  have hpe : Obs2.pathEnd (ptsX x).a w = (ptsX x).b := by
    show Obs2.pathEnd (0 : Lam 2 L N) w = x
    rw [Obs2.pathEnd, zero_add, hwx]
  have hsn : supNorm ((ptsX x).a - (ptsX x).b) = supNorm x := by
    show supNorm ((0 : Lam 2 L N) - x) = supNorm x
    rw [zero_sub, supNorm_neg]
  have hwl' : (w.length : ℝ) ≤ 2 * ((supNorm ((ptsX x).a - (ptsX x).b) : ℕ) : ℝ) := by
    rw [hsn]; exact_mod_cast hwl
  have hsL : 2 * ((supNorm ((ptsX x).a - (ptsX x).b) : ℕ) : ℝ) ≤ (L : ℝ) ^ (j + 1) := by
    have h2 := two_supNorm_lt_coal (by have := M.core.hL49; omega : 2 ≤ L) x
    rw [sub_zero] at h2
    rw [hsn]; exact_mod_cast h2.le
  have hab : (ptsX x).a ≠ (ptsX x).b := fun h => hx (h.symm)
  -- the invariants of the reduced state
  set o' := rpcRed R m b μ₀ x o with ho'd
  have hobs : o'.IsObs := PtCorr2.rpcRedSt_isObs _ _ _ _ _ _
  have hloc0 : ObsLocInv (ptsX x) j o' := PtCorr2.rpcRedSt_loc hV hVL t hj hlo _
  have hsymj : ObsSymInv j o' :=
    PtCorr2.obsSymInv_redSt (hRI j hj).1 (hRI j hj).2 (rawD_mem (R.withMsq m) _ _)
      (rawK_mem (R.withMsq m) _ _) hso
  have hanc : ObsAnchInv (ptsX x) j o' :=
    PtCorr2.obsAnchInv_redSt (R.withMsq m) (ptsX x) _ _ (pairDCov_std Nh x hx h1 hj)
  have hVab : ObsVabInv (ptsX x) o' := PtCorr2.obsVabInv_redSt (R.withMsq m) (ptsX x)
  have hz : ∀ b', (o'.V b' : SA .two (Lam 2 L N)).ab = 0 := fun b' => by
    show ((0 : Obs2.OFam .two 2 L N) b' : SA .two (Lam 2 L N)).ab = 0
    simp
  have hWz : ∀ b', o'.W b' = 0 := fun b' => rfl
  have hW0 : ∀ (C mb : ℝ), ∀ b' ∈ blockIdx (L := L) (N := N) j,
      oTo (wM ((fun _ : ℕ => Ma) j) Mb) j (histS (R.withMsq m) j t) (o'.W b') ≤
        ENNReal.ofReal ((4 * C + 1) * (M.core.c * (t j).1) * mb) := fun C mb b' _ => by
    rw [hWz b', oTo_zero']; exact bot_le
  have hMa' : ∀ k, 0 < (fun _ : ℕ => Ma) k := fun _ => hMa
  have hdbl : ∀ n, ∀ k, j ≤ k → k < n → (fun _ : ℕ => Ma) k ≤ 2 * (fun _ : ℕ => Ma) (k + 1) :=
    fun _ _ _ _ => by dsimp only; linarith
  set mb := rpc9Mb Λ₁ m0 with hmbd
  -- the `V` bounds up to `N_h`
  have hVall : ∀ n, j ≤ n → n ≤ Nh → ∀ k, j ≤ k → k ≤ n → ∀ c ∈ blockIdx (L := L) (N := N) k,
      oTo (wM Ma Mb) k (histS (R.withMsq m) k t)
        ((obsHistFrom (R.withMsq m) (ptsX x) j o' k t).V c) ≤ ENNReal.ofReal (mb (n - j)) := by
    intro n hn hnN
    induction n, hn using Nat.le_induction with
    | base =>
      intro k hk1 hk2 c _
      obtain rfl : k = j := le_antisymm hk2 hk1
      rw [obsHistFrom_self]
      show oTo _ _ _ (0 : OE .two (Lam 2 L N)) ≤ _
      rw [oTo_zero']; exact bot_le
    | succ n hjn ih =>
      have ih' := ih (by omega)
      have hmono : mb (n - j) ≤ mb (n + 1 - j) := rpc9Mb_mono hm0 (by omega)
      intro k hk1 hk2 c hc
      rcases Nat.lt_or_ge k (n + 1) with hlt | hge
      · exact (ih' k hk1 (by omega) c hc).trans (ENNReal.ofReal_le_ofReal hmono)
      · obtain rfl : k = n + 1 := le_antisymm hk2 hge
        have hsp : 0 < histS (R.withMsq m) (n + 1) t := histS_pos' (R.withMsq m) hρ0 hρ8 t _
        have hss : 0 < histS (R.withMsq m) (n + 1) t * histS (R.withMsq m) (n + 1) t :=
          mul_pos hsp hsp
        have hmass := (hMS N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX x) Ma Mb hMa hMb
          j o' hobs hloc0 hsymj hanc hVab hWz k₀ hk₀ hK0 (mb (n - j)) (rpc9Mb_pos hm0 _)
          (rpc9_seed hC₁m h8m (rpc9Mb_ge hm0 _)) n hjn (by omega)
          (fun i hi1 hi2 c' hc' => ih' i hi1 hi2 c' hc')).1
        set ρ := Ma * Mb * (Λ₁ * mb (n - j)) /
          (histS (R.withMsq m) (n + 1) t * histS (R.withMsq m) (n + 1) t) with hρd
        have hρ : ∀ b' ∈ blockIdx (L := L) (N := N) (n + 1),
            ‖LocObs.mass2 ((obsHistFrom (R.withMsq m) (ptsX x) j o' (n + 1) t).V b' :
              SA .two (Lam 2 L N)).ab‖ ≤ ρ := fun b' _ => by
          rw [hρd, le_div_iff₀ hss]; exact hmass b'
        have hρm : ((fun _ : ℕ => Ma) (n + 1) * Mb)⁻¹ * (ρ *
            (histS (R.withMsq m) (n + 1) t * histS (R.withMsq m) (n + 1) t)) ≤
            mb (n + 1 - j) / 2 := by
          have e : ((fun _ : ℕ => Ma) (n + 1) * Mb)⁻¹ * (ρ *
              (histS (R.withMsq m) (n + 1) t * histS (R.withMsq m) (n + 1) t)) =
              Λ₁ * mb (n - j) := by
            rw [hρd]; dsimp only; field_simp
          rw [e, show n + 1 - j = n - j + 1 by omega]
          exact rpc9Mb_succ hm0 _
        exact hVS N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX x) hab w hpe hwl'
          (fun _ => Ma) Mb hMa' hMb j o' hobs hloc0 hsymj hanc hVab hz hsL (n + 1) (by omega)
          hnN (hdbl (n + 1)) (mb (n + 1 - j)) (rpc9Mb_pos hm0 _)
          (fun k' hk1' hk2' c' hc' => (ih' k' hk1' (by omega) c' hc').trans
            (ENNReal.ofReal_le_ofReal hmono)) (hW0 C₁v _) k₀ hk₀ hK0
          (rpc9_seed hC₁v h8v (rpc9Mb_ge hm0 _)) ρ hρ hρm c hc
  refine ⟨fun n hn1 hn2 c hc => hVall n hn1 hn2 n hn1 le_rfl c hc, fun n hn1 hn2 c => ?_,
    fun k hk1 hk2 => ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have h := (hMS N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX x) Ma Mb hMa hMb
      j o' hobs hloc0 hsymj hanc hVab hWz k₀ hk₀ hK0 (mb (k - j)) (rpc9Mb_pos hm0 _)
      (rpc9_seed hC₁m h8m (rpc9Mb_ge hm0 _)) k (by omega) (by omega)
      (fun i hi1 hi2 c' hc' => hVall k (by omega) (by omega) i hi1 hi2 c' hc')).1 c
    rwa [show k + 1 - 1 - j = k - j by omega]
  · exact (hMS N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX x) Ma Mb hMa hMb
      j o' hobs hloc0 hsymj hanc hVab hWz k₀ hk₀ hK0 (mb (k - j)) (rpc9Mb_pos hm0 _)
      (rpc9_seed hC₁m h8m (rpc9Mb_ge hm0 _)) k hk1 hk2
      (fun i hi1 hi2 c' hc' => hVall k hk1 hk2 i hi1 hi2 c' hc')).2

end

end Spin2
