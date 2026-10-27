import Spin2.Restart.RestartPairChain3
import Spin2.Pair.PairZeroAB4

/-!
# T5, item (5)(iii): the reduced chain of a general state from `j_x` to `N_h + 1` (crude chain)

Pair `(0, x)`, `1 ≤ j_x ≤ N_h`, a general observable state `o` at `j_x` (local, `U(1)`-invariant),
its reduced state `o' = rpcRed o` and the reduced chain `obsHistFrom … j_x o'`. In a **constant**
weight `wM(M_a, M_b)` (`M_a` the `a`-side size of `o`, e.g. `2s_{N_h}²σ`), the `V`-step of the
joint induction (`MasterCore.vstepD`) and its top version (`MasterCore.vstepTopD`) are
state-general; they are applied along the reduced chain with the seed `k₀` of `rpc_seed_gen`:

* **`rpc_chain_sizesD`** (domain form, from `MasterFacts`): there are `C₁w, C₁t ≥ 0` such that for
  every admissible trajectory, `x`, `o` as above, `M_a, M_b > 0`, a seed bound
  `A^{(|𝓑(X)|-4)_+}‖K'_{j_x}(X)‖_{wM} ≤ k₀`, a target `m̄ > 0` with
  `8k₀ ≤ vck(C)(4C + 1)m̄` (`C = C₁w, C₁t`), and **per-block masses**
  `|m₂(V_n(B)_{ab})| ≤ ρ_n` with `(M_aM_b)^{-1}ρ_ns_n² ≤ m̄/2` for `j_x < n ≤ N_h + 1`:
  `‖V_n(B)‖_{wM} ≤ m̄` (`j_x ≤ n ≤ N_h + 1`), `‖𝒲_{N_h+1}(B)‖_{wM} ≤ (4C₁t+1)cǧ_{N_h}m̄`,
  `A^{(…)}‖K_{N_h+1}(U)‖_{wM} ≤ (4C₁t+1)m̄`.

No smallness of `m̄` is needed (the reduced chain is linear in its seed), so every constant is
proportional to `m̄`, i.e. to `max(k₀, sup_n ρ_ns_n²/(M_aM_b))`; with `M_a = 2s_{N_h}²σ` these are
the inputs `c_V = m̄`, `c_W = (4C₁t+1)c·m̄`, `c_K = (4C₁t+1)m̄` of `rpc_zm_le`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs2

set_option maxHeartbeats 8000000 in
/-- **The reduced chain of a general state at `j_x ≤ N_h`, crude sizes up to `N_h + 1`**
(domain form). -/
theorem rpc_chain_sizesD {L : ℕ} [NeZero L] (M : MasterFacts L) :
    ∃ C₁w C₁t : ℝ, 0 ≤ C₁w ∧ 0 ≤ C₁t ∧
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
    ∀ mbar : ℝ, 0 < mbar → 8 * k₀ ≤ vck C₁w * ((4 * C₁w + 1) * mbar) →
      8 * k₀ ≤ vck C₁t * ((4 * C₁t + 1) * mbar) →
    ∀ ρ : ℕ → ℝ,
    (∀ n, Obs.coal L (0 : Lam 2 L N) x < n → n ≤ Nh + 1 → ∀ c ∈ blockIdx (L := L) (N := N) n,
      ‖LocObs.mass2 ((obsHistFrom (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x)
        (rpcRed R m b μ₀ x o) n (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).V c :
          SA .two (Lam 2 L N)).ab‖ ≤ ρ n) →
    (∀ n, Obs.coal L (0 : Lam 2 L N) x < n → n ≤ Nh + 1 →
      (Ma * Mb)⁻¹ * (ρ n * (histS (R.withMsq m) n (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) *
        histS (R.withMsq m) n (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))) ≤ mbar / 2) →
    (∀ n, Obs.coal L (0 : Lam 2 L N) x ≤ n → n ≤ Nh + 1 → ∀ c ∈ blockIdx (L := L) (N := N) n,
      oTo (wM Ma Mb) n (histS (R.withMsq m) n (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((obsHistFrom (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x)
          (rpcRed R m b μ₀ x o) n (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).V c) ≤
        ENNReal.ofReal mbar) ∧
    (∀ c ∈ blockIdx (L := L) (N := N) (Nh + 1),
      oTo (wM Ma Mb) (Nh + 1)
        (histS (R.withMsq m) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((rpcTail R Nh m b μ₀ x o).W c) ≤
        ENNReal.ofReal ((4 * C₁t + 1) * (M.core.c *
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) * mbar)) ∧
    (∀ U, IsConn (Nh + 1) U → ENNReal.ofReal ((R.withMsq m).A ^ (nb (Nh + 1) U - 2 ^ 2)) *
      oTo (wM Ma Mb) (Nh + 1)
        (histS (R.withMsq m) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((rpcTail R Nh m b μ₀ x o).K U) ≤ ENNReal.ofReal ((4 * C₁t + 1) * mbar)) := by
  obtain ⟨C₁w, hC₁w, hVS⟩ := M.core.vstepD
  obtain ⟨C₁t, hC₁t, hVT⟩ := M.core.vstepTopD
  refine ⟨C₁w, C₁t, hC₁w, hC₁t, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD x hx h1 hj o ho hlo hso Ma Mb hMa hMb
    k₀ hk₀ hK0 mbar hmbar h8 h8' ρ hρ hρm
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  set t : Hist.Seq (Xs (R.withMsq m)) := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  obtain ⟨hV, hVL, -, hRI⟩ := M.core.pairTrajD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD
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
  have hW0 : ∀ (C : ℝ), ∀ b' ∈ blockIdx (L := L) (N := N) j,
      oTo (wM ((fun _ : ℕ => Ma) j) Mb) j (histS (R.withMsq m) j t) (o'.W b') ≤
        ENNReal.ofReal ((4 * C + 1) * (M.core.c * (t j).1) * mbar) := fun C b' _ => by
    show oTo _ _ _ (0 : OE .two (Lam 2 L N)) ≤ _
    rw [oTo_zero']; exact bot_le
  have hMa' : ∀ k, 0 < (fun _ : ℕ => Ma) k := fun _ => hMa
  have hdbl : ∀ n, ∀ k, j ≤ k → k < n → (fun _ : ℕ => Ma) k ≤ 2 * (fun _ : ℕ => Ma) (k + 1) :=
    fun _ _ _ _ => by dsimp only; linarith
  -- the `V` bounds up to `N_h` by induction
  have hVall : ∀ n, j ≤ n → n ≤ Nh → ∀ k, j ≤ k → k ≤ n → ∀ c ∈ blockIdx (L := L) (N := N) k,
      oTo (wM Ma Mb) k (histS (R.withMsq m) k t)
        ((obsHistFrom (R.withMsq m) (ptsX x) j o' k t).V c) ≤ ENNReal.ofReal mbar := by
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
      intro k hk1 hk2 c hc
      rcases Nat.lt_or_ge k (n + 1) with hlt | hge
      · exact ih' k hk1 (by omega) c hc
      · obtain rfl : k = n + 1 := le_antisymm hk2 hge
        exact hVS N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX x) hab w hpe hwl'
          (fun _ => Ma) Mb hMa' hMb j o' hobs hloc0 hsymj hanc hVab hz hsL (n + 1) (by omega)
          hnN (hdbl (n + 1)) mbar hmbar
          (fun k' hk1' hk2' => ih' k' hk1' (by omega)) (hW0 C₁w) k₀ hk₀ hK0 h8 (ρ (n + 1))
          (hρ (n + 1) (by omega) (by omega)) (hρm (n + 1) (by omega) (by omega)) c hc
  -- the top step
  obtain ⟨hVt, hWt, hKt⟩ := hVT N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX x) hab w hpe
    hwl' (fun _ => Ma) Mb hMa' hMb j o' hobs hloc0 hsymj hanc hVab hz hsL (Nh + 1) hj rfl
    (hdbl (Nh + 1)) mbar hmbar
    (fun k hk1 hk2 => hVall Nh hj le_rfl k hk1 (by omega)) (hW0 C₁t) k₀ hk₀ hK0 h8'
    (ρ (Nh + 1)) (hρ (Nh + 1) (by omega) le_rfl) (hρm (Nh + 1) (by omega) le_rfl)
  refine ⟨fun n hn1 hn2 c hc => ?_, hWt, hKt⟩
  rcases Nat.lt_or_ge n (Nh + 1) with hlt | hge
  · exact hVall Nh hj le_rfl n hn1 (by omega) c hc
  · obtain rfl : n = Nh + 1 := le_antisymm hn2 hge
    exact hVt c hc

end

end Spin2
