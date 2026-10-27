import Obs.TranslCons

/-!
# `N`-independence of the observable flow at the pair `(ctr_N, ctr_N + x)`

For a fixed `x ∈ ℤ^d` and `N ≤ M` with `8 ((L^{N-1} - 1)/2 + |x|_∞) ≤ L^N`, the whole
observable coupling constants `V^obs_j` and the step data `nextObs` (in particular the `ab`
couplings `q`, `η`, `r_a`, `r_b`) of the flow on `Λ_N` at `(ctr_N, ctr_N + x)` and on `Λ_M` at
`(ctr_M, ctr_M + x)` agree for `j + 2 ≤ N` (`pair_consist`).

Proof: `flowO_consist` embeds the pair into `Λ_M` (`emb (ctr_N + x) = emb ctr_N + x`), and the
translation `t = ctr_M - emb ctr_N` (divisible by `L^{N-1}`, `L` odd) moves it to
`(ctr_M, ctr_M + x)` (`flowO_transl`).
-/

namespace Obs

noncomputable section

open Finset Grassmann SA Loc Step LocObs Gen FRD

variable {d L : ℕ} [NeZero L] {c : Case}

section Pair

variable (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {N M : ℕ} (hNM : N ≤ M) {msq ℓ₀ : ℝ}
  (hmsq : 0 ≤ msq) (V₀ : Vcoup)
  (hgoodM : ∀ j < M, GoodCov (d := d) (L := L) (N := M) j ℓ₀ (Flow.covAt d L M msq j))
  (hbulk : ∀ k, k + 3 ≤ N →
    uVnext k (Flow.covAt d L M msq k) (Flow.flowN d L M msq V₀ k).1 (Flow.flowN d L M msq V₀ k).2 =
      uVnext k (Flow.covAt d L N msq k) (Flow.flowN d L N msq V₀ k).1
        (Flow.flowN d L N msq V₀ k).2)
include hd hL hNM hmsq hgoodM hbulk

/-- **Pair consistency**: `(Λ_N, ctr_N, ctr_N + x) ≅ (Λ_M, ctr_M, ctr_M + x)` for `j + 2 ≤ N`. -/
theorem pair_consist (hLodd : Odd L) (Vo₀ : Coup c) (x : Zd d)
    (hx : 8 * ((L ^ (N - 1) - 1) / 2 + supNormZ x) ≤ L ^ N) {j : ℕ} (hj : j + 2 ≤ N) :
    (flowO d L c N msq V₀ Vo₀ (ctr d L N) (ctr d L N + prj x) j).1 =
        (flowO d L c M msq V₀ Vo₀ (ctr d L M) (ctr d L M + prj x) j).1 ∧
      nextObs (Flow.covAt d L N msq j) j
          (flowO d L c N msq V₀ Vo₀ (ctr d L N) (ctr d L N + prj x) j).1
          (flowO d L c N msq V₀ Vo₀ (ctr d L N) (ctr d L N + prj x) j).2
          (ctr d L N) (ctr d L N + prj x) =
        nextObs (Flow.covAt d L M msq j) j
          (flowO d L c M msq V₀ Vo₀ (ctr d L M) (ctr d L M + prj x) j).1
          (flowO d L c M msq V₀ Vo₀ (ctr d L M) (ctr d L M + prj x) j).2
          (ctr d L M) (ctr d L M + prj x) := by
  have h8 := eight_le hL
  have hN : 1 ≤ N := by omega
  have hLN : 0 < L ^ N := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
  have hc : supNorm (ctr d L N) ≤ (L ^ (N - 1) - 1) / 2 := by
    refine Finset.sup_le fun i _ => ?_
    have := ctr_val (d := d) (N := N) (by omega : 2 ≤ L) i
    exact (min_le_left _ _).trans (le_of_eq this)
  have hpx : supNorm (prj x : Lam d L N) ≤ supNormZ x := supNorm_prj_le x
  have hpx' : supNorm (prj x : Lam d L M) ≤ supNormZ x := supNorm_prj_le x
  have hsum : supNorm (ctr d L N + prj x) ≤ supNorm (ctr d L N) + supNorm (prj x : Lam d L N) :=
    supNorm_add_le _ _
  have ha : 8 * supNorm (ctr d L N) ≤ L ^ N := by omega
  have hb : 8 * supNorm (ctr d L N + prj x) ≤ L ^ N := by omega
  -- the embedding of the pair
  have hex : Flow.emb N M (prj x : Lam d L N) = (prj x : Lam d L M) := by
    have hr : rep (prj x : Lam d L N) = x := (eq_rep rfl (by omega)).symm
    rw [Flow.emb, hr]
  have heb : Flow.emb N M (ctr d L N + prj x) = Flow.emb N M (ctr d L N) + prj x := by
    rw [Flow.emb_add (by omega), hex]
  have ht : ∀ i, L ^ (N - 1) ∣ (co (ctr d L M - Flow.emb N M (ctr d L N)) i).val := fun i =>
    dvd_ctr_transl hLodd h8 hN hNM i
  have hea : Flow.emb N M (ctr d L N) + (ctr d L M - Flow.emb N M (ctr d L N)) = ctr d L M := by
    abel
  have heb' : Flow.emb N M (ctr d L N) + prj x + (ctr d L M - Flow.emb N M (ctr d L N)) =
      ctr d L M + prj x := by abel
  have h1 := (flowO_consist hd hL hNM hmsq V₀ Vo₀ ha hb hbulk j hj).1
  have h2 := nextObs_flowO_consist hd hL hNM hmsq V₀ Vo₀ ha hb hbulk hj
  rw [heb] at h1 h2
  have h3 := (flowO_transl V₀ Vo₀ hd hL hgoodM (k := N - 1) (by omega) _ ht
    (Flow.emb N M (ctr d L N)) (Flow.emb N M (ctr d L N) + prj x) j (by omega)).1
  have h4 := nextObs_flowO_transl V₀ Vo₀ hd hL hgoodM (k := N - 1) (by omega) _ ht
    (Flow.emb N M (ctr d L N)) (Flow.emb N M (ctr d L N) + prj x) (j := j) (by omega)
  rw [hea, heb'] at h3 h4
  exact ⟨h1.trans h3.symm, h2.trans h4.symm⟩

end Pair

end

end Obs
