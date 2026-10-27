import PtCorr2.Pair.PairReduce
import Obs2.Pair.PairRed

/-!
# The reduced pair chain along the history from coalescence (PR3 along `obsHistFrom`)

History started at scale `j` from a state `o'` without one-point parts (`ObsAbInv j o'`), Case (2).
Full inputs `V_k = hVR k`, `𝒲_k`, `K_k` (`fullV` etc. of `obsHistFrom`), covariance `C_k`
(`Obs2.histCovO`). Couplings: `q'_k = -ε(u'_{k,ab})` (`qR`), `r'_k = ∑_Bm₂(V_k(B)_{ab})` (`rR`).

* `hVR_a`, `hVR_b`, `uObsTotR_a`, `uObsTotR_b`: no one-point parts for `k ≥ j`; so `β_a = β_b = 0`.
* **`qR_succ`** (`Obs2.pair_step_red`): `q'_{k+1} - q'_k = -C_k(a,a)r'_k - 𝔡_k + X_k + ρ_aρ_b`
  (`incR`); no vertex term, no `γ`-cross terms. Needs `C_k(b,b) = C_k(a,a)` and no `σ_aσ_b`
  constants in `V_k` (automatic for `k > j`, `epsAB_histR_succ`; assumed at `k = j`).
* **`qR_eq_sum`**: `q'_n - q'_j = ∑_{j≤k<n} inc'_k`.
* **`rR_succ`** (`Obs2.rAB_next_red`): `r'_{k+1} = (1 - n_a)r'_k - d_r + 𝔡₂ - e_{ab} + f`.
* **`nAB_cstOF_eq`**: the reduced constants in couplings, `n_{ab}X' = q'_{N} - q'_k` with
  `q'_N = q'_{N_h+1} - ε(u'_N - u'_{N-1})_{ab}` (`qRN`), `k ≥ j`.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD Obs2 Flow2 Flow2.Hist

variable {L N : ℕ} [NeZero L]

section Chain

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N) (j : ℕ)
  (o' : ObsSt .two L N) (t : Hist.Seq (Xs R))

/-- The full `V♭_k + V'^{obs}_k` along the history from `j`. -/
def hVR (k : ℕ) : OFam .two 2 L N :=
  fullV R k (rawHist R k t) (t k).1 (t k).2.1 (obsHistFrom R P j o' k t)

/-- The full `𝒲_k + 𝒲'^{obs}_k`. -/
def hWR (k : ℕ) : OFam .two 2 L N :=
  fullW (rawHist R k t) (rawD R (rawHist R k t).u (t k).2.2) (obsHistFrom R P j o' k t)

/-- The full `K♭_k + K'^{obs,♭}_k`. -/
def hKR (k : ℕ) : OAct .two 2 L N :=
  fullK R k (rawHist R k t) (rawK R (rawHist R k t).u (t k).2.2) (obsHistFrom R P j o' k t)

/-- `q'_k = -ε(u'_{k,ab})`. -/
def qR (k : ℕ) : ℂ := -ε ((obsHistFrom R P j o' k t).u : SA .two (Lam 2 L N)).ab

/-- `r'_k = ∑_Bm₂(V_k(B)_{ab})`. -/
def rR (k : ℕ) : ℂ := rAB2 k (hVR R P j o' t k)

/-- The increment of step `k`: `-C_k(a,a)r'_k - 𝔡_k + X_k + ρ_aρ_b`. -/
def incR (k : ℕ) : ℂ :=
  -(histCovO R t k P.a P.a * rR R P j o' t k) - pdefAB2 P k (histCovO R t k) (hVR R P j o' t k) +
    (xAB2 P k (histCovO R t k) (hVR R P j o' t k) (hWR R P j o' t k) (hKR R P j o' t k) +
      rhoA2 P k (histCovO R t k) (hVR R P j o' t k) (hWR R P j o' t k) (hKR R P j o' t k) *
        rhoB2 P k (histCovO R t k) (hVR R P j o' t k) (hWR R P j o' t k) (hKR R P j o' t k))

/-- The `u^{obs}` increment `u'_N - u'_{N-1}` of the last step. -/
def lastUR (Nh : ℕ) : OE .two (Lam 2 L N) :=
  uXO P (Nh + 1) (LastN.stCovN R (Nh + 1) (histOut R Nh t).st)
    (fullV R (Nh + 1) (histOut R Nh t).st (histOut R Nh t).g.re (histOut R Nh t).nu.re
      (obsHistFrom R P j o' (Nh + 1) t))
    (fullW (histOut R Nh t).st (histOut R Nh t).D (obsHistFrom R P j o' (Nh + 1) t))
    (fullK R (Nh + 1) (histOut R Nh t).st (histOut R Nh t).K (obsHistFrom R P j o' (Nh + 1) t))
    univ

/-- `q'_N = q'_{N_h+1} - ε(u'_N - u'_{N-1})_{ab}`. -/
def qRN (Nh : ℕ) : ℂ := qR R P j o' t (Nh + 1) - ε (lastUR R P j o' t Nh : SA .two (Lam 2 L N)).ab

variable {R P j o' t}

theorem hab_at (h0 : ObsAbInv j o') {k : ℕ} (hk : j ≤ k) :
    ObsAbInv k (obsHistFrom R P j o' k t) := by
  have h := obsAbInv_histFrom R P h0 t (k - j)
  rwa [show j + (k - j) = k by omega] at h

theorem hVR_a (h0 : ObsAbInv j o') {k : ℕ} (hk : j ≤ k) (b : Fin 2 → ℕ) :
    (hVR R P j o' t k b : SA .two (Lam 2 L N)).a = 0 :=
  (add_mem (emb_mem_ab _) ((hab_at h0 hk).V b)).1

theorem hVR_b (h0 : ObsAbInv j o') {k : ℕ} (hk : j ≤ k) (b : Fin 2 → ℕ) :
    (hVR R P j o' t k b : SA .two (Lam 2 L N)).b = 0 :=
  (add_mem (emb_mem_ab _) ((hab_at h0 hk).V b)).2

theorem oabS_hR (h0 : ObsAbInv j o') {k : ℕ} (hk : j ≤ k) :
    OAbS k (hVR R P j o' t k) (hWR R P j o' t k) (hKR R P j o' t k) :=
  oabS_full R _ _ (hab_at h0 hk)

theorem uObsTotR_mem (h0 : ObsAbInv j o') {k : ℕ} (hk : j ≤ k) :
    uObsTot P k (histCovO R t k) (hVR R P j o' t k) (hWR R P j o' t k) (hKR R P j o' t k) ∈
      (abSub : Subalgebra ℂ (OE .two (Lam 2 L N))) :=
  Subalgebra.sum_mem _ fun b _ => (oabS_hR h0 hk).up_ab b

theorem obsHistFrom_u_succ {k : ℕ} (hk : j ≤ k) :
    (obsHistFrom R P j o' (k + 1) t).u = (obsHistFrom R P j o' k t).u +
      uObsTot P k (histCovO R t k) (hVR R P j o' t k) (hWR R P j o' t k) (hKR R P j o' t k) := by
  rw [obsHistFrom_succ hk]; rfl

theorem hVR_succ_ab {k : ℕ} (hk : j ≤ k) (c' : Fin 2 → ℕ) :
    (hVR R P j o' t (k + 1) c' : SA .two (Lam 2 L N)).ab =
      (Vnext2O P k (histCovO R t k) (hVR R P j o' t k) (hWR R P j o' t k) (hKR R P j o' t k) c' :
        SA .two (Lam 2 L N)).ab := by
  show (((emb _ : OE .two (Lam 2 L N)) + (obsHistFrom R P j o' (k + 1) t).V c' :
    OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).ab = _
  rw [obsHistFrom_succ hk]
  exact (zero_add _).trans (piobs_ab _)

theorem epsAB_histR_succ {k : ℕ} (hk : j ≤ k) :
    ∑ b ∈ blockIdx (L := L) (N := N) (k + 1),
      ε (hVR R P j o' t (k + 1) b : SA .two (Lam 2 L N)).ab = 0 := by
  refine sum_eq_zero fun c' _ => ?_
  rw [hVR_succ_ab hk, Vnext2O, AddSubmonoidClass.coe_finsetSum, sum_ab, map_sum]
  exact sum_eq_zero fun b _ => eps_VpO_ab _ _ _ _ _ _ _

theorem betaTot2_hR (h0 : ObsAbInv j o') {k : ℕ} (hk : j ≤ k) :
    betaTot2 k (hVR R P j o' t k) = 0 := by
  unfold betaTot2; exact sum_eq_zero fun b _ => by rw [hVR_a h0 hk, mass2_zero]

theorem betaB2_hR (h0 : ObsAbInv j o') {k : ℕ} (hk : j ≤ k) :
    betaB2 k (hVR R P j o' t k) = 0 := by
  unfold betaB2; exact sum_eq_zero fun b _ => by rw [hVR_b h0 hk, mass2_zero]

/-- **The reduced pair-constant step** (`k ≥ j`, `C_k(b,b) = C_k(a,a)`, no `σ_aσ_b` constants in
`V_k`): `q'_{k+1} - q'_k = -C_k(a,a)r'_k - 𝔡_k + X_k + ρ_aρ_b`. -/
theorem qR_succ (h0 : ObsAbInv j o') {k : ℕ} (hk : j ≤ k)
    (hC : histCovO R t k P.b P.b = histCovO R t k P.a P.a)
    (hab : ∑ b ∈ blockIdx (L := L) (N := N) k, ε (hVR R P j o' t k b : SA .two (Lam 2 L N)).ab = 0) :
    qR R P j o' t (k + 1) - qR R P j o' t k = incR R P j o' t k := by
  have hU := uObsTotR_mem h0 hk (R := R) (P := P) (t := t)
  have h := pair_step_red P k (histCovO R t k) (hVR R P j o' t k) (hWR R P j o' t k)
    (hKR R P j o' t k) (fun b => by rw [hVR_a h0 hk]; exact Loc2Form.zero _)
    (fun b => by rw [hVR_b h0 hk]; exact Loc2Form.zero _) hab
    (sum_eq_zero fun b _ => by rw [hVR_a h0 hk, map_zero])
    (sum_eq_zero fun b _ => by rw [hVR_b h0 hk, map_zero]) hC (betaTot2_hR h0 hk)
    (betaB2_hR h0 hk)
  rw [hU.1, hU.2, map_zero, neg_zero, zero_mul, add_zero] at h
  unfold qR incR rR
  rw [obsHistFrom_u_succ hk, Subalgebra.coe_add, add_ab, map_add]
  linear_combination h

/-- **`q'_n - q'_j = ∑_{j≤k<n} inc'_k`**. -/
theorem qR_eq_sum (h0 : ObsAbInv j o') (hC : ∀ k, histCovO R t k P.b P.b = histCovO R t k P.a P.a)
    (hab0 : ∑ b ∈ blockIdx (L := L) (N := N) j, ε (hVR R P j o' t j b : SA .two (Lam 2 L N)).ab = 0) :
    ∀ n, j ≤ n → qR R P j o' t n - qR R P j o' t j = ∑ k ∈ Ico j n, incR R P j o' t k
  | n, hn => by
    induction n with
    | zero => obtain rfl : j = 0 := by omega
              simp
    | succ n ih =>
      rcases Nat.eq_or_lt_of_le hn with h | h
      · rw [← h, Ico_self, sum_empty, sub_self]
      · have hab : ∑ b ∈ blockIdx (L := L) (N := N) n,
            ε (hVR R P j o' t n b : SA .two (Lam 2 L N)).ab = 0 := by
          rcases Nat.eq_or_lt_of_le (show j ≤ n by omega) with h' | h'
          · rw [← h']; exact hab0
          · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
            exact epsAB_histR_succ (by omega)
        rw [sum_Ico_succ_top (by omega), ← ih (by omega), ← qR_succ h0 (by omega) (hC n) hab]
        ring

/-- **The reduced `r` flow** (`k ≥ j`): `r'_{k+1} = (1 - n_a)r'_k - d_r + 𝔡₂ - e_{ab} + f`. -/
theorem rR_succ (h0 : ObsAbInv j o') {k : ℕ} (hk : j ≤ k) :
    rR R P j o' t (k + 1) =
      (1 - nA2 P k (histCovO R t k) (hVR R P j o' t k)) * rR R P j o' t k -
        dR2 P k (histCovO R t k) (hVR R P j o' t k) + pdefM2 k (histCovO R t k) (hVR R P j o' t k) -
        eAB2 P k (histCovO R t k) (hWR R P j o' t k) (hKR R P j o' t k) +
        farABm P k (histCovO R t k) (hVR R P j o' t k) (hWR R P j o' t k) := by
  have h := rAB_next_red P k (histCovO R t k) (hVR R P j o' t k) (hWR R P j o' t k)
    (hKR R P j o' t k) (fun b => by rw [hVR_a h0 hk]; exact Loc2Form.zero _)
    (fun b => by rw [hVR_b h0 hk]; exact Loc2Form.zero _) (betaTot2_hR h0 hk)
  have e : rR R P j o' t (k + 1) = rAB2 (k + 1) (Vnext2O P k (histCovO R t k) (hVR R P j o' t k)
      (hWR R P j o' t k) (hKR R P j o' t k)) := by
    unfold rR rAB2
    exact sum_congr rfl fun c' _ => by rw [hVR_succ_ab hk]
  rw [e, h]
  rfl

/-! ### The reduced constants in couplings -/

theorem sAB_smul_expU_neg {Λ : Type*} [DecidableEq Λ] [Fintype Λ] (r x : ℂ) {U : OE .two Λ}
    (hU : bulk U = 0) (hab : U ∈ (abSub : Subalgebra ℂ (OE .two Λ))) :
    sAB (r • expU x (-U)) = sE (r • expU x (-U)) * -ε (U : SA .two Λ).ab := by
  have hb : bulk (-U) = 0 := by rw [map_neg, hU, neg_zero]
  rw [sE_smul_expU r x hb]
  unfold sAB expU
  simp only [SetLike.val_smul, SA.smul_ab, map_smul, smul_eq_mul]
  rw [oexp_obs_ab hb, NegMemClass.coe_neg, SA.neg_a, SA.neg_b, SA.neg_ab, hab.1, hab.2]
  simp only [neg_zero, mul_zero, smul_zero, add_zero, map_neg]
  ring

theorem nAB_chOF (h0 : ObsAbInv j o') {i : ℕ} (hi : j ≤ i) (h0' : sE (chOF R P j o' i t) ≠ 0) :
    nAB (chOF R P j o' i t) = qR R P j o' t (i + 1) - qR R P j o' t i := by
  have hU := uObsTotR_mem h0 hi (R := R) (P := P) (t := t)
  have hs : sAB (chOF R P j o' i t) = sE (chOF R P j o' i t) *
      -ε (uObsTot P i (histCovO R t i) (hVR R P j o' t i) (hWR R P j o' t i) (hKR R P j o' t i) :
        SA .two (Lam 2 L N)).ab := sAB_smul_expU_neg _ _ (bulk_uObsTot P i _ _ _ _) hU
  unfold nAB
  rw [hs, mul_div_cancel_left₀ _ h0']
  unfold qR
  rw [obsHistFrom_u_succ hi, Subalgebra.coe_add, add_ab, map_add]
  ring

theorem nAB_lastCstOF (h0 : ObsAbInv j o') {Nh : ℕ} (hj : j ≤ Nh + 1)
    (h0' : sE (lastCstOF R P j o' Nh t) ≠ 0) :
    nAB (lastCstOF R P j o' Nh t) = -ε (lastUR R P j o' t Nh : SA .two (Lam 2 L N)).ab := by
  have hab := hab_at (R := R) (P := P) (t := t) h0 hj
  have H := oabS_full R (histOut R Nh t).g.re (histOut R Nh t).nu.re
    (st := (histOut R Nh t).st) (D := (histOut R Nh t).D) (K := (histOut R Nh t).K) hab
  have hU := H.uXO_ab (P := P) (C := LastN.stCovN R (Nh + 1) (histOut R Nh t).st) univ
  have h0'' := h0'
  unfold lastCstOF uOutNO at h0''
  unfold nAB lastCstOF uOutNO
  rw [sAB_smul_expU_neg _ _ (bulk_uXO_gen P (Nh + 1) _ _ _ _ _) hU, mul_div_cancel_left₀ _ h0'']
  rfl

/-- **The reduced constants in couplings**: `n_{ab}X' = q'_N - q'_k` (`k ≥ j`, `sE X' ≠ 0`). -/
theorem nAB_cstOF_eq (h0 : ObsAbInv j o') {Nh k : ℕ} (hk : j ≤ k) (hkN : k ≤ Nh + 1)
    (hX : sE (cstOF R P j o' Nh k t) ≠ 0) :
    nAB (cstOF R P j o' Nh k t) = qRN R P j o' t Nh - qR R P j o' t k := by
  have hX' := hX
  unfold cstOF at hX'
  rw [sE_mul, sE_prod] at hX'
  have hP0 := left_ne_zero_of_mul hX'
  have hL0 := right_ne_zero_of_mul hX'
  have hne' : ∀ i ∈ Ico k (Nh + 1), sE (chOF R P j o' i t) ≠ 0 := prod_ne_zero_iff.1 hP0
  -- extend to all `i ≥ k` by the closed form (`sE (chOF)` only depends on the bulk)
  have hne : ∀ i, k ≤ i → i < Nh + 1 → sE (chOF R P j o' i t) ≠ 0 := fun i h1 h2 =>
    hne' i (mem_Ico.2 ⟨h1, h2⟩)
  have hmain : ∀ n, k ≤ n → n ≤ Nh + 1 → sE (∏ i ∈ Ico k n, chOF R P j o' i t) ≠ 0 ∧
      nAB (∏ i ∈ Ico k n, chOF R P j o' i t) = qR R P j o' t n - qR R P j o' t k := by
    intro n hn hnN
    induction n with
    | zero =>
      obtain rfl : k = 0 := by omega
      simp [nAB, sAB, sE]
    | succ n ih =>
      rcases Nat.eq_or_lt_of_le hn with h | h
      · rw [← h, Ico_self, prod_empty]; simp [nAB, sAB, sE]
      · obtain ⟨h1, h2⟩ := ih (by omega) (by omega)
        rw [prod_Ico_succ_top (by omega)]
        have hmem : (∏ i ∈ Ico k n, chOF R P j o' i t) ∈
            (abSub : Subalgebra ℂ (OE .two (Lam 2 L N))) :=
          prod_mem fun i hi => chOF_mem_ab R P h0 t (hk.trans (mem_Ico.1 hi).1)
        have hn' := hne n (by omega) (by omega)
        refine ⟨by rw [sE_mul]; exact mul_ne_zero h1 hn', ?_⟩
        rw [nAB_mul_ab hmem h1 hn', h2, nAB_chOF h0 (by omega) hn']
        ring
  obtain ⟨hp1, hp2⟩ := hmain (Nh + 1) hkN le_rfl
  have hmem : (∏ i ∈ Ico k (Nh + 1), chOF R P j o' i t) ∈
      (abSub : Subalgebra ℂ (OE .two (Lam 2 L N))) :=
    prod_mem fun i hi => chOF_mem_ab R P h0 t (hk.trans (mem_Ico.1 hi).1)
  unfold cstOF
  rw [nAB_mul_ab hmem hp1 hL0, hp2, nAB_lastCstOF h0 (by omega) hL0]
  unfold qRN
  ring

end Chain


/-! ### The vertex factor only sees the bulk -/

section Vertex

variable (R : RGPar 2 L N) (P : ObsPts 2 L N) (k : ℕ) (st : RawSt 2 L N) (g μ : ℝ)
  (C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ)

theorem fullV_e_indep {o1 o2 : ObsSt .two L N} (h1 : o1.IsObs) (h2 : o2.IsObs) (b : Fin 2 → ℕ) :
    (fullV R k st g μ o1 b : SA .two (Lam 2 L N)).e = (fullV R k st g μ o2 b : SA .two (Lam 2 L N)).e := by
  show (((emb _ : OE .two (Lam 2 L N)) + o1.V b : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).e =
    (((emb _ : OE .two (Lam 2 L N)) + o2.V b : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).e
  rw [emb_add_e, emb_add_e, e_eq_zero_of_bulk (h1.V b), e_eq_zero_of_bulk (h2.V b)]

/-- **`n_a = m₂F_C(ψ̄_aψ_a, V'(Λ)_∅)` does not see the observables.** -/
theorem nA2_fullV_indep {o1 o2 : ObsSt .two L N} (h1 : o1.IsObs) (h2 : o2.IsObs) :
    nA2 P k C (fullV R k st g μ o1) = nA2 P k C (fullV R k st g μ o2) := by
  have he : (VprLO k C (fullV R k st g μ o1) : SA .two (Lam 2 L N)).e =
      (VprLO k C (fullV R k st g μ o2) : SA .two (Lam 2 L N)).e := by
    unfold VprLO
    rw [AddSubmonoidClass.coe_finsetSum, sum_e, AddSubmonoidClass.coe_finsetSum, sum_e]
    refine sum_congr rfl fun b _ => ?_
    unfold VprO EthO
    rw [coe_ECCO, ECCS_e, coe_ECCO, ECCS_e, coe_thetaO, thetaS_e, coe_thetaO, thetaS_e,
      fullV_e_indep R k st g μ h1 h2 b]
  unfold nA2; rw [he]

end Vertex

end

end PtCorr2
