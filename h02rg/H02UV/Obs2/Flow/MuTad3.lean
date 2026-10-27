import Obs2.Flow.MuTad0
import Obs2.Flow.MuTad1
import Obs2.Flow.MuTad2

/-!
# The `μ^{(1)}` flow for the total coupling: `μ' = μ(1 - 𝔫_j) + R_j` with explicit `R_j`

Along a sequence of steps of the observable map (Case (1)) — covariances `C_k`, inputs
`V_k, 𝒲_k, K_k`, with `𝒲_{k+1}(B_+)_a = (∏(1 + 𝒲'_k) - 1)(B_+)_a` (`Wnext2O`) and `𝒲_0 = 0` in the
`a` component (the hypothesis bundle `MuChain`) — the total coupling `β_k = ∑_B m₁(V_k(B)_a)`
(`β = -μ^{(1)}`) satisfies the **exact identity** (`mu_flow_exact`)

  `β_{j+1} = β_j (1 - 𝔫_j) - ∑_{X ∈ 𝒮_j} m₁(K_j(X)_a) - R_j`,

* `𝔫_j = ν'_j ∑_x C_j(a,x) + g'_j τ(w_j, C_j)` (`frakN`), `w_j = ∑_{k<j} C_k`, `τ = tauC` the
  exact tadpole of the `𝒲^{obs}` cubic (`Obs2.Flow.MuTad2`), `(z', y', ν'_j, g'_j)` the couplings of
  `V'_j(Λ)_∅ = 𝔼θ V_j(Λ)_∅`;
* `R_j = ∑_{k<j} (β_k g'_k - β_j g'_j) τ(C_k, C_j)` (the drift: the cubic of step `k` carries the
  couplings of step `k`) `+ G_j(0) + ∑_{k<j} [P_{k+1}(C_j + S_{k,j}) - P_{k+1}(S_{k,j})]`
  (the product parts of `∏(1 + 𝒲') - 1`; `G_j(0) = P_j(0)` is the mass of `𝒲_j`).

For translation-invariant `C_j` (`C_j(x,x) = c₀`, `C_j(x±e,x) = c₀ + δ`) with
`ν'_j = ν♭_j + 2d g'_j δ` (the Wick shift, `Step2.Coup.shift`), `𝔫_j = ν'_j w^{(1)}_{j+1} -
ν♭_j w^{(1)}_j` (`frakN_TI`), the outline's `𝔫_j` (`lem:second`), for any `w`.

**Bounds** (`mu_flow_bound`, conditional on the hypothesis bundle `MuErr`): if
`|∑_X m₁(K_j(X)_a)| ≤ E_K`, `|β_k g'_k - β_j g'_j| ≤ A(j - k)`, `|τ(C_k, C_j)| ≤ B q^{j-k}` and the
product parts are `≤ E_P`, then
`|β_{j+1} - β_j(1 - 𝔫_j)| ≤ E_K + A B q/(1-q)² + E_P`. Each term is `O(ḡ²|μ|)` under the
expected inputs: `E_K` from the `K^{obs}` bound, `A = O(ḡ²|μ|)` from the one-step flow,
`E_P = O(ḡ²|μ|)` from `‖𝒲^{obs}‖ = O(ḡ|μ|)`, `‖𝒲^∅‖ = O(ḡ)`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 LocObs

variable {d L N : ℕ} [NeZero L]

/-- The total coupling `β_k = ∑_B m₁(V(B)_a)`. -/
def betaTot (k : ℕ) (V : OFam .one d L N) : ℂ :=
  ∑ b ∈ blockIdx (L := L) (N := N) k, mass1 (-1) (V b : SA .one (Lam d L N)).a

/-- The accumulated covariance `w_j = ∑_{k<j} C_k`. -/
def wCum (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ) (j : ℕ) : Matrix (Lam d L N) (Lam d L N) ℂ :=
  ∑ k ∈ range j, C k

/-- `𝔫_j = ν'_j ∑_x C_j(a,x) + g'_j τ(w_j, C_j)`. -/
def frakN (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ) (κ : ℕ → Step2.Coup) (a : Lam d L N)
    (j : ℕ) : ℂ :=
  (κ j).nu * ∑ x, C j a x + (κ j).g * tauC (wCum C j) (C j) a

/-- The step term `T_k(Γ) = β_k g'_k τ(C_k, Γ) + P_{k+1}(Γ)`. -/
def muTk (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ) (V W : ℕ → OFam .one d L N)
    (κ : ℕ → Step2.Coup) (k : ℕ) (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) : ℂ :=
  betaTot (L := L) (N := N) k (V k) * ((κ k).g * tauC (C k) Γ P.a) +
    wProd P k (C k) (V k) (W k) (mass1L (-1)) Γ

/-- The product-part increments `∑_{k<j} [P_{k+1}(C_j + S_{k,j}) - P_{k+1}(S_{k,j})]`. -/
def muProdInc (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : ℕ → OFam .one d L N) (j : ℕ) : ℂ :=
  ∑ k ∈ range j, (wProd P k (C k) (V k) (W k) (mass1L (-1)) (C j + cumBetween C k j) -
    wProd P k (C k) (V k) (W k) (mass1L (-1)) (cumBetween C k j))

/-- The drift `∑_{k<j} (β_k g'_k - β_j g'_j) τ(C_k, C_j)`. -/
def muDrift (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V : ℕ → OFam .one d L N) (κ : ℕ → Step2.Coup) (j : ℕ) : ℂ :=
  ∑ k ∈ range j, (betaTot (L := L) (N := N) k (V k) * (κ k).g -
    betaTot (L := L) (N := N) j (V j) * (κ j).g) * tauC (C k) (C j) P.a

/-- **`𝔫_j` for a translation-invariant covariance**: if `C_j(x,x) = c₀`,
`C_j(x+e,x) = C_j(x,x+e) = c₀ + δ` and `ν'_j = ν♭ + 2d g'_j δ`, then
`𝔫_j = ν'_j w^{(1)}_{j+1} - ν♭ w^{(1)}_j` with `w^{(1)}_k = ∑_x w_k(a,x)`. -/
theorem frakN_TI {C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ} {κ : ℕ → Step2.Coup}
    (a : Lam d L N) (j : ℕ) (c₀ δ nuF : ℂ) (hc : ∀ x, C j x x = c₀)
    (hδ : ∀ x e, C j (x + dirVec e) x = c₀ + δ) (hδ' : ∀ x e, C j x (x + dirVec e) = c₀ + δ)
    (hnu : (κ j).nu = nuF + 2 * d * (κ j).g * δ) :
    frakN C κ a j = (κ j).nu * ∑ x, wCum C (j + 1) a x - nuF * ∑ x, wCum C j a x := by
  rw [frakN, tauC_TI (wCum C j) (C j) a c₀ δ hc hδ hδ']
  have e : ∑ x, wCum C (j + 1) a x = ∑ x, wCum C j a x + ∑ x, C j a x := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun x _ => ?_
    rw [wCum, wCum, sum_range_succ, Matrix.add_apply]
  rw [e, hnu]
  ring

/-- **The hypothesis bundle of a sequence of observable steps** (Case (1)). -/
structure MuChain (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : ℕ → OFam .one d L N) (K : ℕ → OAct .one d L N) (κ : ℕ → Step2.Coup) (r : ℕ → ℂ)
    (n : ℕ) : Prop where
  /-- the steps `k < n` are regular (`k + 1 < N`) -/
  hN : n < N
  /-- the initial remainder has no `a` component -/
  hW0 : ∀ b, (W 0 b : SA .one (Lam d L N)).a = 0
  /-- `𝒲_{k+1} = ∏(1 + 𝒲'_k) - 1` in the `a` component -/
  hW : ∀ k < n, ∀ c', (W (k + 1) c' : SA .one (Lam d L N)).a =
    (Wnext2O P k (C k) (V k) (W k) c' : SA .one (Lam d L N)).a
  /-- `V_{k+1}(B_+) = ∑_{B ⊆ B_+} V'_{k}(B)` in the `a` component -/
  hV : ∀ k < n, ∀ c', (V (k + 1) c' : SA .one (Lam d L N)).a =
    (Vnext2O P k (C k) (V k) (W k) (K k) c' : SA .one (Lam d L N)).a
  /-- the `a` component of `V_k(B)` is a multiple of `ψ̄_a` -/
  hform : ∀ k ≤ n, ∀ b, (V k b : SA .one (Lam d L N)).a =
    mass1 (-1) (V k b : SA .one (Lam d L N)).a • psibar P.a
  /-- the bulk part of `V'_k(Λ) = 𝔼θ V_k(Λ)` is a coupling polynomial plus a constant -/
  he : ∀ k ≤ n, (VprLO k (C k) (V k) : SA .one (Lam d L N)).e =
    Step2.Vcoup (κ k) univ + r k • (1 : Alg d L N)

namespace MuChain

variable {P : ObsPts d L N} {C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ}
  {V W : ℕ → OFam .one d L N} {K : ℕ → OAct .one d L N} {κ : ℕ → Step2.Coup} {r : ℕ → ℂ}
  {n : ℕ} (H : MuChain P C V W K κ r n)
include H

theorem VprLO_a {k : ℕ} (hk : k ≤ n) :
    (VprLO k (C k) (V k) : SA .one (Lam d L N)).a = betaTot (L := L) (N := N) k (V k) •
      psibar P.a := by
  rw [VprLO, AddSubmonoidClass.coe_finset_sum, sum_a, betaTot, sum_smul]
  refine sum_congr rfl fun b _ => ?_
  conv_lhs => rw [VprO, EthO_a_eq, H.hform k hk b]
  rw [map_smul, expLC_psibar]

/-- The one-loop tadpole of step `k` is `β_k g'_k τ(C_k, Γ)`. -/
theorem oneTad_eq {k : ℕ} (hk : k ≤ n) (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) :
    oneTad k (C k) (V k) (mass1L (-1)) Γ =
      betaTot (L := L) (N := N) k (V k) * ((κ k).g * tauC (C k) Γ P.a) := by
  rw [oneTad, H.VprLO_a hk, H.he k hk]
  exact tad_FC_one (C k) Γ P.a (κ k) (r k) _

/-- The tadpole functional along the chain. -/
theorem wTad_succ {k : ℕ} (hk : k < n) (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) :
    wTad (k + 1) (mass1L (-1)) (W (k + 1)) Γ =
      betaTot (L := L) (N := N) k (V k) * ((κ k).g * tauC (C k) Γ P.a) +
        wProd P k (C k) (V k) (W k) (mass1L (-1)) Γ +
        (wTad k (mass1L (-1)) (W k) (Γ + C k) - wTad k (mass1L (-1)) (W k) (C k)) := by
  have e : wTad (k + 1) (mass1L (-1)) (W (k + 1)) Γ = wTad (k + 1) (mass1L (-1)) (Wnext2O P k (C k) (V k) (W k)) Γ := by
    unfold wTad
    exact sum_congr rfl fun c' _ => by rw [H.hW k hk c']
  rw [e, wTad_step k (C k) (V k) (W k) Γ (locMass_one P.a), H.oneTad_eq hk.le]
  ring

theorem wTad_zero (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) : wTad 0 (mass1L (-1)) (W 0) Γ = 0 := by
  unfold wTad
  exact sum_eq_zero fun b _ => by rw [H.hW0 b, map_zero, map_zero]

/-- **The unrolled tadpole functional**: for `j ≤ n`,
`G_j(Γ) = G_j(0) + ∑_{k<j} [β_k g'_k τ(C_k, Γ) + P_{k+1}(Γ + S_{k,j}) - P_{k+1}(S_{k,j})]`. -/
theorem wTad_unroll {j : ℕ} (hj : j ≤ n) (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) :
    wTad j (mass1L (-1)) (W j) Γ = wTad j (mass1L (-1)) (W j) 0 +
      ∑ k ∈ range j, (betaTot (L := L) (N := N) k (V k) * ((κ k).g * tauC (C k) Γ P.a) +
        (wProd P k (C k) (V k) (W k) (mass1L (-1)) (Γ + cumBetween C k j) -
          wProd P k (C k) (V k) (W k) (mass1L (-1)) (cumBetween C k j))) := by
  classical
  -- truncate the chain at `n` so that the recursion holds for all `k`
  let G : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ → ℂ := fun k Γ =>
    if k ≤ n then wTad k (mass1L (-1)) (W k) Γ else 0
  let T : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ → ℂ := fun k Γ =>
    if k < n then muTk P C V W κ k Γ else -(G k (Γ + C k) - G k (C k))
  have h0 : ∀ Γ, G 0 Γ = G 0 0 := fun Γ => by
    show (if 0 ≤ n then _ else _) = (if 0 ≤ n then _ else _)
    rw [if_pos (Nat.zero_le n), if_pos (Nat.zero_le n), H.wTad_zero, H.wTad_zero]
  have hs : ∀ k Γ, G (k + 1) Γ = T k Γ + (G k (Γ + C k) - G k (C k)) := by
    intro k Γ
    by_cases hk : k < n
    · simp only [G, T, if_pos hk, if_pos (show k + 1 ≤ n by omega), if_pos hk.le, muTk]
      rw [H.wTad_succ hk]
    · simp only [T, if_neg hk]
      simp only [G, if_neg (show ¬ k + 1 ≤ n by omega)]
      ring
  have hu := tad_unroll G T C h0 hs j Γ
  simp only [G, if_pos hj] at hu
  rw [hu]
  congr 1
  refine sum_congr rfl fun k hk => ?_
  have hk' : k < n := lt_of_lt_of_le (mem_range.1 hk) hj
  simp only [T, if_pos hk', muTk, tauC_add_right]
  ring

/-- **The exact `μ^{(1)}` flow for the total coupling**: for `j < n`,
`β_{j+1} = β_j(1 - 𝔫_j) - ∑_{X ∈ 𝒮_j} m₁(K_j(X)_a) - (drift_j + G_j(0) + prodInc_j)`. -/
theorem mu_flow_exact {j : ℕ} (hj : j < n) :
    betaTot (L := L) (N := N) (j + 1) (V (j + 1)) =
      betaTot (L := L) (N := N) j (V j) * (1 - frakN C κ P.a j) -
        ∑ X ∈ smallSets (L := L) (N := N) j, mass1 (-1) (K j X : SA .one (Lam d L N)).a -
        (muDrift P C V κ j + wTad j (mass1L (-1)) (W j) 0 + muProdInc P C V W j) := by
  have hjN : j + 1 < N := by have := H.hN; omega
  have h1 : betaTot (L := L) (N := N) (j + 1) (V (j + 1)) =
      ∑ b ∈ blockIdx (L := L) (N := N) j,
        mass1 (-1) (VpO P j (C j) (V j) (W j) (K j) b : SA .one (Lam d L N)).a := by
    unfold betaTot
    rw [← sum_blockIdx_succ j]
    refine sum_congr rfl fun c' _ => ?_
    rw [H.hV j hj c', Vnext2O, AddSubmonoidClass.coe_finset_sum, sum_a]
    show mass1L (-1) _ = _
    rw [map_sum]; rfl
  have hβ : ∀ b, (V j b : SA .one (Lam d L N)).a =
      (fun b => mass1 (-1) (V j b : SA .one (Lam d L N)).a) b • psibar P.a :=
    fun b => H.hform j hj.le b
  rw [h1, total_mu_one_tad P j (C j) (V j) (W j) (K j) hjN _ hβ (κ j) (r j) (H.he j hj.le),
    H.wTad_unroll hj.le (C j)]
  have hτ : ∑ k ∈ range j, betaTot (L := L) (N := N) k (V k) * ((κ k).g * tauC (C k) (C j) P.a) =
      betaTot (L := L) (N := N) j (V j) * (κ j).g * tauC (wCum C j) (C j) P.a +
        muDrift P C V κ j := by
    rw [muDrift, wCum, tauC_sum_left, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun k _ => by ring
  rw [sum_add_distrib, hτ, frakN, muProdInc]
  unfold betaTot
  ring

end MuChain

/-- **The error hypotheses** of the `μ^{(1)}` flow at step `j` (to be discharged by the `K^{obs}`,
`𝒲^{obs}` bounds and the one-step flow of `β g'`). -/
structure MuErr (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : ℕ → OFam .one d L N) (K : ℕ → OAct .one d L N) (κ : ℕ → Step2.Coup) (j : ℕ)
    (EK A B q EP : ℝ) : Prop where
  hA : 0 ≤ A
  hB : 0 ≤ B
  hq0 : 0 ≤ q
  hq : q < 1
  /-- the activity term -/
  hK : ‖∑ X ∈ smallSets (L := L) (N := N) j, mass1 (-1) (K j X : SA .one (Lam d L N)).a‖ ≤ EK
  /-- the drift of `β g'` -/
  hdrift : ∀ k < j, ‖betaTot (L := L) (N := N) k (V k) * (κ k).g -
    betaTot (L := L) (N := N) j (V j) * (κ j).g‖ ≤ A * (j - k : ℕ)
  /-- the decay of the tadpole between scales -/
  htau : ∀ k < j, ‖tauC (C k) (C j) P.a‖ ≤ B * q ^ (j - k)
  /-- the product parts -/
  hP : ‖wTad j (mass1L (-1)) (W j) 0 + muProdInc P C V W j‖ ≤ EP

/-- **The `μ^{(1)}` flow with an explicit error bound** (conditional on `MuChain` and `MuErr`):
`|β_{j+1} - β_j(1 - 𝔫_j)| ≤ E_K + A B q/(1-q)² + E_P`. -/
theorem mu_flow_bound {P : ObsPts d L N} {C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ}
    {V W : ℕ → OFam .one d L N} {K : ℕ → OAct .one d L N} {κ : ℕ → Step2.Coup} {r : ℕ → ℂ}
    {n j : ℕ} (H : MuChain P C V W K κ r n) (hj : j < n) {EK A B q EP : ℝ}
    (E : MuErr P C V W K κ j EK A B q EP) :
    ‖betaTot (L := L) (N := N) (j + 1) (V (j + 1)) -
        betaTot (L := L) (N := N) j (V j) * (1 - frakN C κ P.a j)‖ ≤
      EK + A * B * (q / (1 - q) ^ 2) + EP := by
  rw [H.mu_flow_exact hj]
  have hD : ‖muDrift P C V κ j‖ ≤ A * B * (q / (1 - q) ^ 2) :=
    drift_sum_le j E.hA E.hB E.hq0 E.hq E.hdrift E.htau
  have e : betaTot (L := L) (N := N) j (V j) * (1 - frakN C κ P.a j) -
      ∑ X ∈ smallSets (L := L) (N := N) j, mass1 (-1) (K j X : SA .one (Lam d L N)).a -
      (muDrift P C V κ j + wTad j (mass1L (-1)) (W j) 0 + muProdInc P C V W j) -
      betaTot (L := L) (N := N) j (V j) * (1 - frakN C κ P.a j) =
      -(∑ X ∈ smallSets (L := L) (N := N) j, mass1 (-1) (K j X : SA .one (Lam d L N)).a) -
        muDrift P C V κ j - (wTad j (mass1L (-1)) (W j) 0 + muProdInc P C V W j) := by ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  refine (add_le_add ((norm_sub_le _ _).trans (add_le_add (le_of_eq (norm_neg _)) le_rfl))
    le_rfl).trans ?_
  linarith [E.hK, E.hP, hD]

end

end Obs2
