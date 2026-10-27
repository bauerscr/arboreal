import Obs2.Flow.MuTad3
import Obs2.Pair.CoalHist
import Step2.Last.FlowLastF1a
import Step2.Coup.CoupQuad2
import Step2.Map.FullStep

/-!
# The `μ^{(1)}` flow along the observable history: `MuChain` instantiated

With the pointed `loc^a` of `Obs2.Loc.Loc`, `loc^a_{X,Y}F` is a multiple of `ψ̄_a` for **every**
polymer `X` (`locAp_one_form`), so in Case (1) the `σ_a` component of `V_{j+1}(B)` is a multiple
of `ψ̄_a` for every block `B` (not only `B ∋ a`): `VpO_a_one_span`, `Vnext2O_a_one_span`.

Along the history of `Obs2.Flow.Hist` (`C_k = stCov`, inputs `fullV`, `fullW`, `fullK` built from
`rawHist` and `obsHist`):

* `obsHist_hform`: `V_k(B)_a ∈ ℂψ̄_a` at every scale `k < N`, if this holds for the initial state;
* `histVprLO_e`: the bulk part of `V'_k(Λ) = 𝔼_{C_k}θV_k(Λ)` is the coupling polynomial of the
  shifted couplings `κ'_k = κ_k.shift 2 c₀ δ` plus a constant (`Step2.EthE_VfamL`), with
  `C_k(x,x) = c₀`, `C_k(x±e,x) = c₀ + δ` from `covProps` (`RawInv.covL` / `covU`);
* **`muChain_obsHist`**: the hypothesis bundle `MuChain` of `Obs2.Flow.MuTad3` holds along every
  history (hypotheses `ValidAt` below `n`, `ValidAtL` at `n`, `n < N`), for every observable
  initial state with `𝒲_0(B)_a = 0` and `V_0(B)_a ∈ ℂψ̄_a` (e.g. `obsInit .one V P`);
* **`mu_flow_exact_hist`**: hence the exact identity
  `β_{j+1} = β_j(1 - 𝔫_j) - ∑_{X ∈ 𝒮_j} m₁(K_j(X)_a) - R_j` along every history, with
  `𝔫_j = ν'_j w^{(1)}_{j+1} - ν♭_j w^{(1)}_j` (`frakN_TI`) and `ν♭_j` the `ν`-coordinate of `V♭_j`;
  **`mu_flow_bound_hist`**: the bound `|β_{j+1} - β_j(1 - 𝔫_j)| ≤ E_K + ABq/(1-q)² + E_P` under
  the error hypotheses `MuErr` (the open inputs: `K^{obs}`, drift, tadpole decay, product parts).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 LocObs FRD Flow2

/-! ### The form of `V_{j+1}(B)_a` for every block (Case (1)) -/

section Form

variable {d L N : ℕ} [NeZero L] (P : ObsPts d L N) (j : ℕ)
  (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V W : OFam .one d L N) (K : OAct .one d L N)

theorem expLC_mem_span_psibar {F : Alg d L N} (hF : F ∈ (ℂ ∙ psibar P.a)) :
    expLC C F ∈ (ℂ ∙ psibar P.a) := by
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hF
  rw [map_smul, expLC_psibar]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem locAp_one_mem_span (X Y : Finset (Lam d L N)) (F : Alg d L N) :
    locAp Obs.Case.one P.a X Y F ∈ (ℂ ∙ psibar P.a) := by
  obtain ⟨r, hr⟩ := locAp_one_form P.a X Y F
  rw [hr]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem Q2O_a_one_span (b : Fin d → ℕ) :
    (Q2O P j K b : SA .one (Lam d L N)).a ∈ (ℂ ∙ psibar P.a) := by
  classical
  unfold Q2O
  split_ifs
  · rw [AddSubmonoidClass.coe_finsetSum, sum_a]
    exact Submodule.sum_mem _ fun X _ => locAp_one_mem_span P X _ _
  · exact zero_mem _

/-- **`V_{j+1}(B)_a ∈ ℂψ̄_a` for every block `B`** (Case (1)), if `V_j(B)_a ∈ ℂψ̄_a`. -/
theorem VpO_a_one_span (b : Fin d → ℕ)
    (hV : (V b : SA .one (Lam d L N)).a ∈ (ℂ ∙ psibar P.a)) :
    (VpO P j C V W K b : SA .one (Lam d L N)).a ∈ (ℂ ∙ psibar P.a) := by
  have hu : ε (uVpO P j C V W K b : SA .one (Lam d L N)).a = 0 := ε_a_one _
  have e : (VpO P j C V W K b : SA .one (Lam d L N)).a =
      expLC C (V b : SA .one (Lam d L N)).a -
        expLC C (Q2O P j K b : SA .one (Lam d L N)).a -
        locAp Obs.Case.one P.a (Step2.Bp (L := L) (N := N) j b) (blockSet (L := L) (N := N) j b)
          (SXO j C V W (Step2.Bp (L := L) (N := N) j b) : SA .one (Lam d L N)).a -
        0 - algebraMap ℂ (Alg d L N)
          (ε (uVpO P j C V W K b : SA .one (Lam d L N)).a) := by
    have hup : (upO P j C V W K b : SA .one (Lam d L N)).a =
        algebraMap ℂ (Alg d L N) (ε (uVpO P j C V W K b : SA .one (Lam d L N)).a) := by
      show cmp true (πobs (epsO (uVpO P j C V W K b)) : SA .one (Lam d L N)) = _
      rw [cmp_πobs]; rfl
    have halg : ((algebraMap ℂ (OE .one (Lam d L N)) (upB P j C V W K b) : OE .one (Lam d L N)) :
        SA .one (Lam d L N)).a = 0 := by
      rw [Subalgebra.coe_algebraMap]; exact algebraMap_a _
    have h1 : (VpO P j C V W K b : SA .one (Lam d L N)).a =
        (uVpO P j C V W K b : SA .one (Lam d L N)).a -
          ((algebraMap ℂ (OE .one (Lam d L N)) (upB P j C V W K b) : OE .one (Lam d L N)) :
            SA .one (Lam d L N)).a - (upO P j C V W K b : SA .one (Lam d L N)).a := rfl
    have h2 : (uVpO P j C V W K b : SA .one (Lam d L N)).a =
        (VprO C V b : SA .one (Lam d L N)).a - (EthO C (Q2O P j K b) : SA .one (Lam d L N)).a -
          (LSO P j C V W b : SA .one (Lam d L N)).a := rfl
    rw [h1, halg, hup, h2, VprO, EthO_eq_expO, EthO_eq_expO]; rfl
  rw [e, hu, map_zero, sub_zero, sub_zero]
  exact sub_mem (sub_mem (expLC_mem_span_psibar P C hV)
    (expLC_mem_span_psibar P C (Q2O_a_one_span P j K b))) (locAp_one_mem_span P _ _ _)

theorem Vnext2O_a_one_span (c' : Fin d → ℕ)
    (hV : ∀ b, (V b : SA .one (Lam d L N)).a ∈ (ℂ ∙ psibar P.a)) :
    (Vnext2O P j C V W K c' : SA .one (Lam d L N)).a ∈ (ℂ ∙ psibar P.a) := by
  rw [Vnext2O, AddSubmonoidClass.coe_finsetSum, sum_a]
  exact Submodule.sum_mem _ fun b _ => VpO_a_one_span P j C V W K b (hV b)

theorem eq_mass1_smul_of_span {a : Lam d L N} {F : Alg d L N} (hF : F ∈ (ℂ ∙ psibar a)) :
    F = mass1 (-1) F • psibar a := by
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hF
  rw [mass1_smul, mass1_psibar, mul_one]

end Form

/-! ### Along the history -/

section Hist

variable {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  (P : ObsPts 2 L N) (o₀ : ObsSt .one L N) (t : Hist.Seq (Xs R)) {n k : ℕ}

/-- The covariance of step `k` of the history. -/
def histCovO (k : ℕ) : Matrix (Lam 2 L N) (Lam 2 L N) ℂ := stCov R k (rawHist R k t)

/-- The full `V♭_k + V^{obs}_k` along the history. -/
def histVO (k : ℕ) : OFam .one 2 L N :=
  fullV R k (rawHist R k t) (t k).1 (t k).2.1 (obsHist R P o₀ k t)

/-- The full `𝒲_k + 𝒲^{obs}_k` along the history. -/
def histWO (k : ℕ) : OFam .one 2 L N :=
  fullW (rawHist R k t) (rawD R (rawHist R k t).u (t k).2.2) (obsHist R P o₀ k t)

/-- The full `K♭_k + K^{obs,♭}_k` along the history. -/
def histKO (k : ℕ) : OAct .one 2 L N :=
  fullK R k (rawHist R k t) (rawK R (rawHist R k t).u (t k).2.2) (obsHist R P o₀ k t)

theorem histVO_a (k : ℕ) (b : Fin 2 → ℕ) :
    (histVO R P o₀ t k b : SA .one (Lam 2 L N)).a =
      ((obsHist R P o₀ k t).V b : SA .one (Lam 2 L N)).a :=
  emb_add_cmp true _ _

theorem histWO_a (k : ℕ) (b : Fin 2 → ℕ) :
    (histWO R P o₀ t k b : SA .one (Lam 2 L N)).a =
      ((obsHist R P o₀ k t).W b : SA .one (Lam 2 L N)).a :=
  emb_add_cmp true _ _

theorem histVO_succ_a (k : ℕ) (c' : Fin 2 → ℕ) :
    (histVO R P o₀ t (k + 1) c' : SA .one (Lam 2 L N)).a =
      (Vnext2O P k (histCovO R t k) (histVO R P o₀ t k) (histWO R P o₀ t k) (histKO R P o₀ t k) c' :
        SA .one (Lam 2 L N)).a := by
  rw [histVO_a, obsHist_succ]
  exact piobs_cmp true _

theorem histWO_succ_a (k : ℕ) (c' : Fin 2 → ℕ) :
    (histWO R P o₀ t (k + 1) c' : SA .one (Lam 2 L N)).a =
      (Wnext2O P k (histCovO R t k) (histVO R P o₀ t k) (histWO R P o₀ t k) c' :
        SA .one (Lam 2 L N)).a := by
  rw [histWO_a, obsHist_succ]
  exact piobs_cmp true _

/-- **`V_k(B)_a ∈ ℂψ̄_a` at every scale** of the history. -/
theorem obsHist_hform (h0 : ∀ b, (o₀.V b : SA .one (Lam 2 L N)).a ∈ (ℂ ∙ psibar P.a)) :
    ∀ k b, (histVO R P o₀ t k b : SA .one (Lam 2 L N)).a ∈ (ℂ ∙ psibar P.a)
  | 0, b => by rw [histVO_a]; exact h0 b
  | k + 1, b => by
    rw [histVO_succ_a]
    exact Vnext2O_a_one_span P k _ _ _ _ b (obsHist_hform h0 k)

/-- **The bulk part of `V'_k(Λ)`**: for a covariance with `C(x,x) = c₀`, `C(x±e,x) = c₀ + δ`,
`(𝔼θ V_k(Λ))_∅ = V_{κ'}(Λ) + r` with `κ' = κ♭.shift 2 c₀ δ`, `κ♭` the couplings of `V♭_k`. -/
theorem histVprLO_e (ho : (obsHist R P o₀ k t).IsObs) {c₀ δ : ℂ}
    (hc₀ : ∀ x, histCovO R t k x x = c₀) (hδ : ∀ x e, histCovO R t k (x + dirVec e) x = c₀ + δ)
    (hδ' : ∀ x e, histCovO R t k x (x + dirVec e) = c₀ + δ) :
    ∃ r : ℂ, (VprLO k (histCovO R t k) (histVO R P o₀ t k) : SA .one (Lam 2 L N)).e =
      Vcoup ((Coup.ofVec ![(rawHist R k t).z + stYc R (rawHist R k t) - stA R (rawHist R k t),
        (rawHist R k t).y - stYc R (rawHist R k t),
        stNu R k (rawHist R k t) (t k).2.1 - stA R (rawHist R k t) * R.msq,
        stGr R k (rawHist R k t) (t k).1 (t k).2.1 * stZ' R (rawHist R k t) ^ 2]).shift 2 c₀ δ)
        univ + r • (1 : Alg 2 L N) := by
  set v : Fin 4 → ℂ := ![(rawHist R k t).z + stYc R (rawHist R k t) - stA R (rawHist R k t),
        (rawHist R k t).y - stYc R (rawHist R k t),
        stNu R k (rawHist R k t) (t k).2.1 - stA R (rawHist R k t) * R.msq,
        stGr R k (rawHist R k t) (t k).1 (t k).2.1 * stZ' R (rawHist R k t) ^ 2] with hv
  choose r hr using fun b => EthE_VfamL (L := L) (N := N) hc₀ hδ hδ' k v b
  refine ⟨∑ b ∈ blockIdx (L := L) (N := N) k, r b, ?_⟩
  have hb : ∀ b, (VprO (histCovO R t k) (histVO R P o₀ t k) b : SA .one (Lam 2 L N)).e =
      Vcoup ((Coup.ofVec v).shift 2 c₀ δ) (blockSet (L := L) (N := N) k b) + r b • 1 := by
    intro b
    rw [VprO, (EthO_comp _ _).1, histVO, fullV]
    show expLC _ ((stVf R k (rawHist R k t) (t k).1 (t k).2.1 b : Alg 2 L N) +
      ((obsHist R P o₀ k t).V b : SA .one (Lam 2 L N)).e) = _
    rw [e_eq_zero_of_bulk (ho.V b), add_zero]
    have h := congrArg Subtype.val (hr b)
    simp only [coe_EthE, Subalgebra.coe_add, Subalgebra.coe_smul, OneMemClass.coe_one] at h
    exact h
  rw [VprLO, AddSubmonoidClass.coe_finsetSum, sum_e, sum_congr rfl fun b _ => hb b,
    sum_add_distrib, ← sum_smul, sum_Vcoup_blocks]

/-- The shifted couplings of step `k` (with the covariance constants of `covProps`). -/
theorem histVprLO_e_ex (hV : ∀ i < n, ValidAt R i) (hVL : ValidAtL R n) (h₀ : o₀.IsObs)
    (k : ℕ) : ∃ (κ : Step2.Coup) (r : ℂ), k ≤ n →
      (VprLO k (histCovO R t k) (histVO R P o₀ t k) : SA .one (Lam 2 L N)).e =
        Vcoup κ univ + r • (1 : Alg 2 L N) := by
  by_cases hk : k ≤ n
  · have H := rawInv_histU R hV hVL t k (by omega)
    obtain ⟨-, -, hCs, hCsym⟩ := covU R hV hVL hk H
    obtain ⟨c₀, δ, hc₀, hδ, hδ'⟩ := covProps (by norm_num : 1 ≤ 2) hCs hCsym
    obtain ⟨r, hr⟩ := histVprLO_e R P o₀ t (obsHist_isObs R P o₀ h₀ k t) hc₀ hδ hδ'
    exact ⟨_, r, fun _ => hr⟩
  · exact ⟨Coup.ofVec 0, 0, fun h => absurd h hk⟩

/-- **`MuChain` along the history** (Case (1)): for `n < N`, `ValidAt` below `n`, `ValidAtL` at
`n`, and an observable initial state with `𝒲_0(B)_a = 0` and `V_0(B)_a ∈ ℂψ̄_a`, the steps
`k < n` of the history form a `MuChain` (with suitable `κ`, `r`). -/
theorem muChain_obsHist (hN : n < N) (hV : ∀ i < n, ValidAt R i) (hVL : ValidAtL R n)
    (h₀ : o₀.IsObs) (hW0 : ∀ b, (o₀.W b : SA .one (Lam 2 L N)).a = 0)
    (hV0 : ∀ b, (o₀.V b : SA .one (Lam 2 L N)).a ∈ (ℂ ∙ psibar P.a)) :
    ∃ (κ : ℕ → Step2.Coup) (r : ℕ → ℂ),
      MuChain P (histCovO R t) (histVO R P o₀ t) (histWO R P o₀ t) (histKO R P o₀ t) κ r n := by
  choose κ r hκ using histVprLO_e_ex R P o₀ t hV hVL h₀
  exact ⟨κ, r,
    { hN := hN
      hW0 := fun b => by rw [histWO_a]; exact hW0 b
      hW := fun k _ c' => histWO_succ_a R P o₀ t k c'
      hV := fun k _ c' => histVO_succ_a R P o₀ t k c'
      hform := fun k _ b => eq_mass1_smul_of_span (obsHist_hform R P o₀ t hV0 k b)
      he := fun k hk => hκ k hk }⟩

/-- **The exact `μ^{(1)}` flow along the history**: for `j < n`,
`β_{j+1} = β_j(1 - 𝔫_j) - ∑_{X ∈ 𝒮_j} m₁(K_j(X)_a) - (drift_j + G_j(0) + prodInc_j)`, where
`β_k = ∑_B m₁(V_k(B)_a)` is the total coupling (`β = -μ^{(1)}`). -/
theorem mu_flow_exact_hist (hN : n < N) (hV : ∀ i < n, ValidAt R i) (hVL : ValidAtL R n)
    (h₀ : o₀.IsObs) (hW0 : ∀ b, (o₀.W b : SA .one (Lam 2 L N)).a = 0)
    (hV0 : ∀ b, (o₀.V b : SA .one (Lam 2 L N)).a ∈ (ℂ ∙ psibar P.a)) :
    ∃ (κ : ℕ → Step2.Coup) (r : ℕ → ℂ),
      MuChain P (histCovO R t) (histVO R P o₀ t) (histWO R P o₀ t) (histKO R P o₀ t) κ r n ∧
      ∀ j < n, betaTot (L := L) (N := N) (j + 1) (histVO R P o₀ t (j + 1)) =
        betaTot (L := L) (N := N) j (histVO R P o₀ t j) * (1 - frakN (histCovO R t) κ P.a j) -
          ∑ X ∈ smallSets (L := L) (N := N) j,
            mass1 (-1) (histKO R P o₀ t j X : SA .one (Lam 2 L N)).a -
          (muDrift P (histCovO R t) (histVO R P o₀ t) κ j +
            wTad j (mass1L (-1)) (histWO R P o₀ t j) 0 +
            muProdInc P (histCovO R t) (histVO R P o₀ t) (histWO R P o₀ t) j) := by
  obtain ⟨κ, r, H⟩ := muChain_obsHist R P o₀ t hN hV hVL h₀ hW0 hV0
  exact ⟨κ, r, H, fun j hj => H.mu_flow_exact hj⟩

/-- **The `μ^{(1)}` flow along the history with an explicit error bound**, conditional only on
the error hypotheses `MuErr` at step `j` (the activity term, the drift of `β g'`, the decay of
the tadpole between scales, and the product parts). -/
theorem mu_flow_bound_hist (hN : n < N) (hV : ∀ i < n, ValidAt R i) (hVL : ValidAtL R n)
    (h₀ : o₀.IsObs) (hW0 : ∀ b, (o₀.W b : SA .one (Lam 2 L N)).a = 0)
    (hV0 : ∀ b, (o₀.V b : SA .one (Lam 2 L N)).a ∈ (ℂ ∙ psibar P.a)) :
    ∃ (κ : ℕ → Step2.Coup) (r : ℕ → ℂ),
      MuChain P (histCovO R t) (histVO R P o₀ t) (histWO R P o₀ t) (histKO R P o₀ t) κ r n ∧
      ∀ j < n, ∀ {EK A B q EP : ℝ},
        MuErr P (histCovO R t) (histVO R P o₀ t) (histWO R P o₀ t) (histKO R P o₀ t) κ j
          EK A B q EP →
        ‖betaTot (L := L) (N := N) (j + 1) (histVO R P o₀ t (j + 1)) -
          betaTot (L := L) (N := N) j (histVO R P o₀ t j) * (1 - frakN (histCovO R t) κ P.a j)‖ ≤
          EK + A * B * (q / (1 - q) ^ 2) + EP := by
  obtain ⟨κ, r, H⟩ := muChain_obsHist R P o₀ t hN hV hVL h₀ hW0 hV0
  exact ⟨κ, r, H, fun j hj _ _ _ _ _ E => mu_flow_bound H hj E⟩

end Hist

end

end Obs2
