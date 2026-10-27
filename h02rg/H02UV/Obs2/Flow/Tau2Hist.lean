import Obs2.Flow.Tau2
import Obs2.Flow.MuHist2

/-!
# `𝔫^{(2)}` along the history, explicitly (Case (2))

Along the history (`ValidAt R i` for `i < n`, observable initial state):

* `c0H`, `dlH`: the lattice constants `C_k(0,0)`, `δ_k = C_k(e₁,0) - C_k(0,0)` of the step
  covariance `C_k = histCovO R t k`;
* `nuFH k = μ_kZ_{k+1}/L^{2k} - a_km²` and `gH k = ǧ_{r,k}Z_{k+1}²`: the `ν`- and `g`-coordinates
  of `V♭_k` (unshifted); `kapH k = κ♭_k.shift 2 c₀_k δ_k` the couplings of `V'_k(Λ)_∅`
  (`kapH_nu`: `ν'_k = ν♭_k + 4g_kδ_k`, `kapH_g`: `g'_k = g_k`);
* `histVprLO2_e`: `V'_k(Λ)_∅ = V_{κ'_k}(Λ) + r` (Case (2) copy of `histVprLO_e`);
* **`bulk2_hist`**: `Obs2.Bulk2` along the history (`k < n`);
* **`frakN2_hist`**: `𝔫^{(2)}_j = ν'_jS_{j+1} - ν♭_jS_j - g_j(𝔩_{w_{j+1}} - 𝔩_{w_j})
  - 4δ_j∑_{k<j}(g_j - g_k)rowS_{C_k} + ∑_{k<j}(g_j - g_k)𝔩_{C_k,C_j}` for `j < n`
  (`S_j = ∑_{k<j}rowS_{C_k}(a)`, `w_j = ∑_{k<j}C_k`).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 LocObs FRD Flow2

variable {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  (P : ObsPts 2 L N) (o₀ : ObsSt .two L N) (t : Hist.Seq (Xs R)) {n : ℕ}

/-- `C_k(0,0)`. -/
def c0H (k : ℕ) : ℂ := histCovO R t k 0 0

/-- `δ_k = C_k(e₁,0) - C_k(0,0)`. -/
def dlH (k : ℕ) : ℂ := histCovO R t k (dirVec (Sum.inl (0 : Fin 2))) 0 - histCovO R t k 0 0

/-- The (unshifted) `ν`-coordinate of `V♭_k`: `μ_kZ_{k+1}/L^{2k} - a_km²`. -/
def nuFH (k : ℕ) : ℂ := stNu R k (rawHist R k t) (t k).2.1 - stA R (rawHist R k t) * R.msq

/-- The `g`-coordinate of `V♭_k`: `ǧ_{r,k}Z_{k+1}²`. -/
def gH (k : ℕ) : ℂ := stGr R k (rawHist R k t) (t k).1 (t k).2.1 * stZ' R (rawHist R k t) ^ 2

/-- The couplings `κ'_k` of `V'_k(Λ)_∅`. -/
def kapH (k : ℕ) : Coup :=
  (Coup.ofVec ![(rawHist R k t).z + stYc R (rawHist R k t) - stA R (rawHist R k t),
    (rawHist R k t).y - stYc R (rawHist R k t), nuFH R t k, gH R t k]).shift 2 (c0H R t k) (dlH R t k)

theorem kapH_g (k : ℕ) : (kapH R t k).g = gH R t k := rfl

theorem kapH_nu (k : ℕ) : (kapH R t k).nu = nuFH R t k + 4 * gH R t k * dlH R t k := by
  simp only [kapH, Coup.shift, Coup.ofVec]
  simp only [Matrix.cons_val, Nat.cast_ofNat]
  ring

/-- **The bulk part of `V'_k(Λ)`** (Case (2)). -/
theorem histVprLO2_e {k : ℕ} (ho : (obsHist R P o₀ k t).IsObs) {c₀ δ : ℂ}
    (hc₀ : ∀ x, histCovO R t k x x = c₀) (hδ : ∀ x e, histCovO R t k (x + dirVec e) x = c₀ + δ)
    (hδ' : ∀ x e, histCovO R t k x (x + dirVec e) = c₀ + δ) :
    ∃ r : ℂ, (VprLO k (histCovO R t k) (histVO2 R P o₀ t k) : SA .two (Lam 2 L N)).e =
      Vcoup ((Coup.ofVec ![(rawHist R k t).z + stYc R (rawHist R k t) - stA R (rawHist R k t),
        (rawHist R k t).y - stYc R (rawHist R k t), nuFH R t k, gH R t k]).shift 2 c₀ δ)
        univ + r • (1 : Alg 2 L N) := by
  set v : Fin 4 → ℂ := ![(rawHist R k t).z + stYc R (rawHist R k t) - stA R (rawHist R k t),
        (rawHist R k t).y - stYc R (rawHist R k t), nuFH R t k, gH R t k] with hv
  choose r hr using fun b => EthE_VfamL (L := L) (N := N) hc₀ hδ hδ' k v b
  refine ⟨∑ b ∈ blockIdx (L := L) (N := N) k, r b, ?_⟩
  have hb : ∀ b, (VprO (histCovO R t k) (histVO2 R P o₀ t k) b : SA .two (Lam 2 L N)).e =
      Vcoup ((Coup.ofVec v).shift 2 c₀ δ) (blockSet (L := L) (N := N) k b) + r b • 1 := by
    intro b
    rw [VprO, (EthO_comp _ _).1, histVO2, fullV]
    show expLC _ ((stVf R k (rawHist R k t) (t k).1 (t k).2.1 b : Alg 2 L N) +
      ((obsHist R P o₀ k t).V b : SA .two (Lam 2 L N)).e) = _
    rw [e_eq_zero_of_bulk (ho.V b), add_zero]
    have h := congrArg Subtype.val (hr b)
    simp only [coe_EthE, Subalgebra.coe_add, Subalgebra.coe_smul, OneMemClass.coe_one] at h
    exact h
  rw [VprLO, AddSubmonoidClass.coe_finsetSum, sum_e, sum_congr rfl fun b _ => hb b,
    sum_add_distrib, ← sum_smul, sum_Vcoup_blocks]

/-- The lattice constants of the step covariances below `n`. -/
theorem histCov_consts (hV : ∀ i < n, ValidAt R i) {k : ℕ} (hk : k < n) :
    (∀ x, histCovO R t k x x = c0H R t k) ∧
      (∀ x e, histCovO R t k (x + dirVec e) x = c0H R t k + dlH R t k) ∧
      (∀ x e, histCovO R t k x (x + dirVec e) = c0H R t k + dlH R t k) := by
  have H := rawInv_hist R (hV k hk).2.2.2.1 k (fun i hi => hV i (by omega)) t
  obtain ⟨-, -, hCs, hCsym⟩ := H.cov (hV k hk)
  obtain ⟨c₀, δ, hc, hδ, hδ'⟩ := covProps (by norm_num) hCs hCsym
  have e0 : histCovO R t k 0 0 = c₀ := hc 0
  have e1 : histCovO R t k (dirVec (Sum.inl (0 : Fin 2))) 0 = c₀ + δ := by
    have := hδ 0 (Sum.inl 0)
    rw [zero_add] at this
    exact this
  have hc0 : c0H R t k = c₀ := e0
  have hd0 : dlH R t k = δ := by
    unfold dlH; rw [e1, e0]; ring
  rw [hc0, hd0]
  exact ⟨hc, hδ, hδ'⟩

/-- **`Bulk2` along the history** (Case (2)). -/
theorem bulk2_hist (hV : ∀ i < n, ValidAt R i) (h₀ : o₀.IsObs) :
    Bulk2 (histCovO R t) (histVO2 R P o₀ t) (kapH R t) (c0H R t) (dlH R t) n where
  he := fun k hk => by
    obtain ⟨hc, hδ, hδ'⟩ := histCov_consts R t hV hk
    exact histVprLO2_e R P o₀ t (obsHist_isObs R P o₀ h₀ k t) hc hδ hδ'
  hc := fun k hk => (histCov_consts R t hV hk).1
  hδ := fun k hk => (histCov_consts R t hV hk).2.1
  hδ' := fun k hk => (histCov_consts R t hV hk).2.2

/-- **`𝔫^{(2)}_j` along the history, explicitly.** -/
theorem frakN2_hist (hV : ∀ i < n, ValidAt R i) (h₀ : o₀.IsObs) {j : ℕ} (hj : j < n) :
    frakN2 P (histCovO R t) (histVO2 R P o₀ t) j =
      (nuFH R t j + 4 * gH R t j * dlH R t j) * (∑ k ∈ range (j + 1), rowS (histCovO R t k) P.a) -
        nuFH R t j * (∑ k ∈ range j, rowS (histCovO R t k) P.a) -
        gH R t j * (lfunC (∑ k ∈ range (j + 1), histCovO R t k) P.a -
          lfunC (∑ k ∈ range j, histCovO R t k) P.a) -
        4 * dlH R t j * ∑ k ∈ range j, (gH R t j - gH R t k) * rowS (histCovO R t k) P.a +
        ∑ k ∈ range j, (gH R t j - gH R t k) * lfunX (histCovO R t k) (histCovO R t j) P.a := by
  rw [(bulk2_hist R P o₀ t hV h₀).frakN2_split P hj]
  simp only [kapH_g, kapH_nu]
  push_cast
  ring

end

end Obs2
