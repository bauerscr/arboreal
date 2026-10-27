import Obs.ConsistStep
import Flow.FlowDefs

/-!
# Proposition `prop:consistency` for the observable flow

The observable flow on `Λ_N` (`flowO`), started at `(V^obs_0, K_0 = 0)` alongside the bulk flow
`Flow.flowN` (whose coupling constants `V^∅_j` are the bulk input of each step):
`V^obs_{j+1} = (nextObs …)^V` and `K_{j+1} = K_{j+1}(V_j, K_j)` restricted to connected
`(j+1)`-polymers, with the covariances `Flow.covAt` (the `C_{j+1}` of `sec:frd`).  Its bulk part
is the bulk flow (`bulkK_flowO`), and `K_j` satisfies the support hypotheses (`obsSupp_flowO`).

**Torus independence** (`flowO_consist`): for `N ≤ M`, observable points `a, b ∈ Λ_N` with
`8|a|_∞, 8|b|_∞ ≤ L^N`, embedded as `emb a, emb b ∈ Λ_M`, and bulk flows whose coupling
constants `(u, V)_{k+1}` agree for `k + 3 ≤ N` (this is the bulk part of `prop:consistency`,
provided by `Flow.thm_flow`, see `hbulk_of`), for `j + 2 ≤ N`:
* the observable coupling constants agree: `(V^obs_j)_N = (V^obs_j)_M`, and the next ones
  `(u + V)^obs_{j+1}` (`nextObs`) agree (`nextObs_flowO_consist`); hence `V^obs_j` agree for
  `j + 1 ≤ N` (`flowO_V_consist`);
* the activities are compatible on `{|x|_∞ ≤ L^N/4 - 2^{d+1} L^j}` up to diameter
  `L^N/8 - 2^{d+2} L^j`.

This is what `lem:Vobs-recursion` uses: for `j + 1 < N`, all coupling constants are independent
of `N`.
-/

namespace Obs

noncomputable section

open Finset Grassmann SA Loc Step LocObs Gen FRD

variable {d L : ℕ} [NeZero L] {c : Case}

open Classical in
/-- The restriction to connected `j`-polymers. -/
def restrO (j : ℕ) {N : ℕ} (K : Finset (Lam d L N) → OE c (Lam d L N)) :
    Finset (Lam d L N) → OE c (Lam d L N) :=
  fun X => if IsConn j X then K X else 0

theorem restrO_of_conn {j N : ℕ} (K : Finset (Lam d L N) → OE c (Lam d L N))
    {X : Finset (Lam d L N)} (hX : IsConn j X) : restrO j K X = K X := by
  simp [restrO, hX]

variable (d L) in
/-- **The observable flow** `(V^obs_j, K_j)` on `Λ_N`, started at `(V^obs_0, 0)`, along the bulk
flow `Flow.flowN N msq V₀`. -/
def flowO (c : Case) (N : ℕ) (msq : ℝ) (V₀ : Vcoup) (Vo₀ : Coup c) (a b : Lam d L N) :
    ℕ → Coup c × (Finset (Lam d L N) → OE c (Lam d L N))
  | 0 => (Vo₀, 0)
  | j + 1 => (Coup.toV c (nextObs (Flow.covAt d L N msq j) j (flowO c N msq V₀ Vo₀ a b j).1
        (flowO c N msq V₀ Vo₀ a b j).2 a b),
      restrO (j + 1) (KnextO j (Flow.covAt d L N msq j) (Flow.flowN d L N msq V₀ j).1
        (flowO c N msq V₀ Vo₀ a b j).1 (flowO c N msq V₀ Vo₀ a b j).2 a b))

section Flow

variable {N : ℕ} (msq : ℝ) (V₀ : Vcoup) (Vo₀ : Coup c) (a b : Lam d L N)

theorem flowO_succ (j : ℕ) : flowO d L c N msq V₀ Vo₀ a b (j + 1) =
    (Coup.toV c (nextObs (Flow.covAt d L N msq j) j (flowO d L c N msq V₀ Vo₀ a b j).1
        (flowO d L c N msq V₀ Vo₀ a b j).2 a b),
      restrO (j + 1) (KnextO j (Flow.covAt d L N msq j) (Flow.flowN d L N msq V₀ j).1
        (flowO d L c N msq V₀ Vo₀ a b j).1 (flowO d L c N msq V₀ Vo₀ a b j).2 a b)) := rfl

/-- The bulk part of the observable flow is the bulk flow. -/
theorem bulkK_flowO : ∀ j, bulkK (flowO d L c N msq V₀ Vo₀ a b j).2 = (Flow.flowN d L N msq V₀ j).2
  | 0 => funext fun _ => map_zero bulk
  | j + 1 => by
    funext X
    rw [Flow.flowN_succ]
    show bulk (restrO (j + 1) _ X) = Flow.restr (j + 1) _ X
    by_cases hX : IsConn (j + 1) X
    · rw [restrO_of_conn _ hX, Flow.restr_of_conn _ hX, bulk_KnextO _ _ _ _ _ _ _ (IsPolymer.of_succ hX.1),
        bulkK_flowO j]
    · rw [Flow.restr_of_not_conn _ hX]
      simp [restrO, hX]

/-- The activities of the observable flow satisfy the support hypotheses. -/
theorem obsSupp_flowO (hd : 1 ≤ d) : ∀ j, ObsSupp a b j (flowO d L c N msq V₀ Vo₀ a b j).2
  | 0 => fun _ _ => zero_mem _
  | j + 1 => fun X hX => by
    show restrO (j + 1) _ X ∈ _
    rw [restrO_of_conn _ hX]
    exact SL_mono a b (nbhd_subset_nbhd_succ X)
      (obsSupp_KnextO j _ _ _ _ a b hd (obsSupp_flowO hd j) hX.1)

end Flow

/-! ### Torus independence -/

theorem pow_facts (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {k N : ℕ} (hk : k + 2 ≤ N) :
    128 * (2 ^ d * L ^ k) ≤ L ^ N ∧ 16 * (2 ^ d * L ^ k) ≤ 2 ^ d * L ^ (k + 1) ∧
      1 ≤ 2 ^ d * L ^ k := by
  have hL0 : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have h16 : 16 ≤ L := by
    have : 2 ^ 4 ≤ 2 ^ (d + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hN : L ^ (k + 2) ≤ L ^ N := Nat.pow_le_pow_right hL0 hk
  have h7 : 128 * 2 ^ d ≤ 2 ^ (d + 3) * 2 ^ (d + 3) := by
    rw [← pow_add, show 128 = 2 ^ 7 by norm_num, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨?_, ?_, Nat.one_le_iff_ne_zero.2 (by positivity)⟩
  · calc 128 * (2 ^ d * L ^ k) = (128 * 2 ^ d) * L ^ k := by ring
      _ ≤ (2 ^ (d + 3) * 2 ^ (d + 3)) * L ^ k := Nat.mul_le_mul_right _ h7
      _ ≤ (L * L) * L ^ k := Nat.mul_le_mul_right _ (Nat.mul_le_mul hL hL)
      _ = L ^ (k + 2) := by ring
      _ ≤ L ^ N := hN
  · calc 16 * (2 ^ d * L ^ k) ≤ L * (2 ^ d * L ^ k) := Nat.mul_le_mul_right _ h16
      _ = 2 ^ d * L ^ (k + 1) := by ring

/-- The bulk hypothesis of `flowO_consist` from the torus independence of the bulk flow
(`Flow.thm_flow`: `V_j` agree for `j + 2 ≤ N`, `u_{j+1}` agree for `j + 3 ≤ N`). -/
theorem hbulk_of {N M : ℕ} {msq : ℝ} {V₀ : Vcoup}
    (hV : ∀ j, j + 2 ≤ N → (Flow.flowN d L N msq V₀ j).1 = (Flow.flowN d L M msq V₀ j).1)
    (hu : ∀ j, j + 3 ≤ N → Flow.uflow d L N msq V₀ j = Flow.uflow d L M msq V₀ j) :
    ∀ k, k + 3 ≤ N →
      uVnext k (Flow.covAt d L M msq k) (Flow.flowN d L M msq V₀ k).1 (Flow.flowN d L M msq V₀ k).2 =
        uVnext k (Flow.covAt d L N msq k) (Flow.flowN d L N msq V₀ k).1
          (Flow.flowN d L N msq V₀ k).2 := fun k hk =>
  Prod.ext (hu k hk).symm (hV (k + 1) (by omega)).symm

section Consist

variable (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {N M : ℕ} (hNM : N ≤ M) {msq : ℝ} (hmsq : 0 ≤ msq)
  (V₀ : Vcoup) (Vo₀ : Coup c) {a b : Lam d L N} (ha : 8 * supNorm a ≤ L ^ N)
  (hb : 8 * supNorm b ≤ L ^ N)
  (hbulk : ∀ k, k + 3 ≤ N →
    uVnext k (Flow.covAt d L M msq k) (Flow.flowN d L M msq V₀ k).1 (Flow.flowN d L M msq V₀ k).2 =
      uVnext k (Flow.covAt d L N msq k) (Flow.flowN d L N msq V₀ k).1
        (Flow.flowN d L N msq V₀ k).2)
include hd hL hNM hmsq ha hb hbulk

theorem flowN_V_eq : ∀ j, j + 2 ≤ N →
    (Flow.flowN d L M msq V₀ j).1 = (Flow.flowN d L N msq V₀ j).1
  | 0, _ => rfl
  | j + 1, hj => by
    rw [Flow.flowN_succ, Flow.flowN_succ]
    exact congrArg Prod.snd (hbulk j (by omega))

theorem covAt_emb {j : ℕ} (hj : j + 2 ≤ N) (x y : Lam d L N)
    (h : supNorm x + supNorm y + supNorm (x - y) < L ^ N) :
    Flow.covAt d L M msq j (Flow.emb N M x) (Flow.emb N M y) = Flow.covAt d L N msq j x y := by
  rw [Flow.covAt_lt (by omega), Flow.covAt_lt (by omega)]
  exact Flow.Cfrd_emb_of hNM (by omega) hmsq hd h

/-- **Proposition `prop:consistency` for the observable flow**: for `j + 2 ≤ N ≤ M`, the
observable coupling constants of the flows on `Λ_N` and `Λ_M` agree and the activities are
compatible near the origin. -/
theorem flowO_consist : ∀ j, j + 2 ≤ N →
    (flowO d L c N msq V₀ Vo₀ a b j).1 =
        (flowO d L c M msq V₀ Vo₀ (Flow.emb N M a) (Flow.emb N M b) j).1 ∧
      CompatO j (L ^ N / 4 - 2 * (2 ^ d * L ^ j)) (L ^ N / 8 - 4 * (2 ^ d * L ^ j))
        (flowO d L c N msq V₀ Vo₀ a b j).2
        (flowO d L c M msq V₀ Vo₀ (Flow.emb N M a) (Flow.emb N M b) j).2
  | 0, _ => ⟨rfl, fun X _ _ _ => map_zero (embO N M)⟩
  | j + 1, hj => by
    obtain ⟨ih1, ih2⟩ := flowO_consist j (by omega)
    obtain ⟨hPA, hAB, hA1⟩ := pow_facts hd hL (k := j) (N := N) (by omega)
    obtain ⟨hPB, -, -⟩ := pow_facts hd hL (k := j + 1) (N := N) (by omega)
    have hjN : j + 2 ≤ N := by omega
    have e1 : 2 ^ (d + 1) * L ^ j = 2 * (2 ^ d * L ^ j) := by ring
    have hC := covAt_emb hd hL hNM hmsq V₀ ha hb hbulk (j := j) hjN
    have hRa : supNorm a + 2 ^ d * L ^ j ≤ L ^ N / 4 - 2 * (2 ^ d * L ^ j) := by omega
    have hRb : supNorm b + 2 ^ d * L ^ j ≤ L ^ N / 4 - 2 * (2 ^ d * L ^ j) := by omega
    have hDab : 2 ^ (d + 1) * L ^ j ≤ L ^ N / 8 - 4 * (2 ^ d * L ^ j) := by omega
    have hnext := nextObs_consist hNM hd hL hjN hC ha hb (flowO d L c N msq V₀ Vo₀ a b j).1
      (compat_smallAt hNM hd hL hjN ih2 hRa hDab) (compat_smallAt hNM hd hL hjN ih2 hRb hDab)
    have hVb := flowN_V_eq hd hL hNM hmsq V₀ ha hb hbulk j hjN
    have huV : uVb j (Flow.covAt d L M msq j) (Flow.flowN d L N msq V₀ j).1
        (flowO d L c M msq V₀ Vo₀ (Flow.emb N M a) (Flow.emb N M b) j).2 =
        uVb j (Flow.covAt d L N msq j) (Flow.flowN d L N msq V₀ j).1
          (flowO d L c N msq V₀ Vo₀ a b j).2 := by
      have := hbulk j (by omega)
      rw [hVb] at this
      rw [uVb, uVb, bulkK_flowO, bulkK_flowO]
      exact this
    have H := KnextO_consist hNM hd hL hjN hC ha hb (Flow.flowN d L N msq V₀ j).1
      (flowO d L c N msq V₀ Vo₀ a b j).1 (obsSupp_flowO msq V₀ Vo₀ a b hd j) huV ih2
      (R' := L ^ N / 4 - 2 * (2 ^ d * L ^ (j + 1))) (D' := L ^ N / 8 - 4 * (2 ^ d * L ^ (j + 1)))
      (by omega) (by omega) (by omega) (by omega) hRa hRb hDab
    refine ⟨?_, ?_⟩
    · rw [flowO_succ, flowO_succ, ← ih1, hnext]
    · intro X hX hXR hXD
      obtain ⟨hQ, -, -, -⟩ := Flow.num_facts hd hL (j := j) (N := N) (by omega)
      have hX5 : ∀ x ∈ X, 16 * supNorm x ≤ 5 * L ^ N := fun x hx => by
        have := hXR x hx; omega
      have hXc : IsConn (j + 1) (X.image (Flow.emb N M)) :=
        (Flow.isConn_image_iff hNM (by omega) hQ hX5).2 hX
      show embO N M (restrO (j + 1) _ X) = restrO (j + 1) _ (X.image (Flow.emb N M))
      rw [restrO_of_conn _ hX, restrO_of_conn _ hXc, hVb, ← ih1]
      exact H X hX hXR hXD

/-- The observable coupling constants `(u + V)^obs_{j+1}` agree for `j + 2 ≤ N ≤ M`. -/
theorem nextObs_flowO_consist {j : ℕ} (hj : j + 2 ≤ N) :
    nextObs (Flow.covAt d L N msq j) j (flowO d L c N msq V₀ Vo₀ a b j).1
        (flowO d L c N msq V₀ Vo₀ a b j).2 a b =
      nextObs (Flow.covAt d L M msq j) j
        (flowO d L c M msq V₀ Vo₀ (Flow.emb N M a) (Flow.emb N M b) j).1
        (flowO d L c M msq V₀ Vo₀ (Flow.emb N M a) (Flow.emb N M b) j).2
        (Flow.emb N M a) (Flow.emb N M b) := by
  obtain ⟨ih1, ih2⟩ := flowO_consist hd hL hNM hmsq V₀ Vo₀ ha hb hbulk j hj
  obtain ⟨hPA, -, hA1⟩ := pow_facts hd hL (k := j) (N := N) hj
  have e1 : 2 ^ (d + 1) * L ^ j = 2 * (2 ^ d * L ^ j) := by ring
  have hC := covAt_emb hd hL hNM hmsq V₀ ha hb hbulk (j := j) hj
  have hRa : supNorm a + 2 ^ d * L ^ j ≤ L ^ N / 4 - 2 * (2 ^ d * L ^ j) := by omega
  have hRb : supNorm b + 2 ^ d * L ^ j ≤ L ^ N / 4 - 2 * (2 ^ d * L ^ j) := by omega
  have hDab : 2 ^ (d + 1) * L ^ j ≤ L ^ N / 8 - 4 * (2 ^ d * L ^ j) := by omega
  rw [← ih1]
  exact (nextObs_consist hNM hd hL hj hC ha hb _ (compat_smallAt hNM hd hL hj ih2 hRa hDab)
    (compat_smallAt hNM hd hL hj ih2 hRb hDab)).symm

end Consist

end

end Obs
