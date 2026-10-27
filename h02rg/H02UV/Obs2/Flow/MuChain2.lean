import Obs2.Flow.BlockFlow
import Obs2.Flow.WickTotal

/-!
# The `μ^{(2)}` flow (Case (2), the vertex `σ_aψ̄_aψ_a`): per-block and total exact recursion

Case (2) analogue of `Obs2.Flow.MuTad3` / `Obs2.Flow.BlockFlow` (Case (1)). In Case (2) the `σ_a` component
of `V_k(B)` is `α_k(B) + c_k(B) ψ̄_aψ_a` for **every** block (`locAp_two_form`), with the share
`c_k(B) = m₂(V_k(B)_a)` (`m₂ = mass2`, `β = -μ^{(2)}_a`). With the sharp splitting `S^♯` of
`Obs2.Map.Map`:

* `tau2 C Γ a e = m₂(e^{ℒ_Γ}F_C(ψ̄_aψ_a, e)) - m₂(F_C(ψ̄_aψ_a, e))`: the tadpole (at a later
  covariance `Γ`) of the one-loop term of the unit vertex against the bulk `e = V'_k(Λ)_∅`
  (kept as a functional; for `e = V_κ(Λ) + r` only the quartic `g` part contributes);
* `nuBar2 = m₂F_C(ψ̄_aψ_a, V'_j(Λ)_∅)` (`= ν'(∑_xC(a,x) + ∑_xC(x,a)) - g'𝔩_C(a)` for
  `V'_j(Λ)_∅ = V_{κ'}(Λ) + r`, `total_FC_two`);
* `tadInc2 k j = τ₂(C_k, C_j + S_{k,j}) - τ₂(C_k, S_{k,j})` (bulk only), and
  **`frakN2 j = nuBar2_j + ∑_{k<j} tadInc2 k j`**, the one-loop coefficient `𝔫^{(2)}_j`;
* `MuChain2`: the hypothesis bundle (no condition on the bulk part is needed);
* **`MuChain2.share2_flow_exact`**: for every `(j+1)`-block `B_+`,
  `c_{j+1}(B_+) = β_j(B_+)(1 - 𝔫^{(2)}_j) - err_j(B_+)`, `err = muQX2 + muDriftX2 + G_j(B_+;0) +
  muProdIncX2` (activity, drift `∑_{k<j}(β_k(B_+) - β_j(B_+)) tadInc2 k j`, mass of `𝒲_j`,
  product increments) — the same structure as `MuChain.share_flow_exact`;
* **`MuChain2.betaTot2_succ_eq`**: the total flow `β_{j+1} = β_j(1 - 𝔫^{(2)}_j) - ∑_{B_+}err_j(B_+)`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 LocObs

variable {d L N : ℕ} [NeZero L]

/-- The coupling of the region `X` (Case (2)): `β_k(X) = ∑_{B ∈ 𝓑_k(X)} m₂(V(B)_a)`. -/
def betaX2 (k : ℕ) (V : OFam .two d L N) (X : Finset (Lam d L N)) : ℂ :=
  ∑ b ∈ blocks k X, mass2 (V b : SA .two (Lam d L N)).a

/-- The total coupling (Case (2)): `β_k = ∑_B m₂(V(B)_a)` (`= -μ^{(2)}_{a,k}`). -/
def betaTot2 (k : ℕ) (V : OFam .two d L N) : ℂ :=
  ∑ b ∈ blockIdx (L := L) (N := N) k, mass2 (V b : SA .two (Lam d L N)).a

/-- The tadpole of the unit Case-(2) vertex against a bulk element `e`. -/
def tau2 (C Γ : Matrix (Lam d L N) (Lam d L N) ℂ) (a : Lam d L N) (e : Alg d L N) : ℂ :=
  mass2 (expLC Γ (FC C (pbp a) e)) - mass2 (FC C (pbp a) e)

/-- The bulk part `V'_k(Λ)_∅` of step `k`. -/
def bulkE2 (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ) (V : ℕ → OFam .two d L N) (k : ℕ) :
    Alg d L N :=
  (VprLO k (C k) (V k) : SA .two (Lam d L N)).e

/-- The one-loop coefficient of step `j`: `ν̄^{(2)}_j = m₂F_{C_j}(ψ̄_aψ_a, V'_j(Λ)_∅)`. -/
def nuBar2 (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V : ℕ → OFam .two d L N) (j : ℕ) : ℂ :=
  mass2 (FC (C j) (pbp P.a) (bulkE2 C V j))

/-- The tadpole increment `τ₂(C_k, C_j + S_{k,j}) - τ₂(C_k, S_{k,j})` (bulk only). -/
def tadInc2 (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V : ℕ → OFam .two d L N) (k j : ℕ) : ℂ :=
  tau2 (C k) (C j + cumBetween C k j) P.a (bulkE2 C V k) -
    tau2 (C k) (cumBetween C k j) P.a (bulkE2 C V k)

/-- **`𝔫^{(2)}_j = ν̄^{(2)}_j + ∑_{k<j} tadInc2 k j`**. -/
def frakN2 (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V : ℕ → OFam .two d L N) (j : ℕ) : ℂ :=
  nuBar2 P C V j + ∑ k ∈ range j, tadInc2 P C V k j

/-- `F_C(α + βψ̄_aψ_a, e) = β F_C(ψ̄_aψ_a, e)`. -/
theorem FC_loc2 (C : Matrix (Lam d L N) (Lam d L N) ℂ) (α β : ℂ) (a : Lam d L N)
    (e : Alg d L N) : FC C (α • (1 : Alg d L N) + β • pbp a) e = β • FC C (pbp a) e := by
  rw [FC_add_left, Step2.FC_const_left, zero_add, FC_smul_left]

/-- `e^{ℒ_C}(α + βψ̄_aψ_a) = α' + βψ̄_aψ_a`. -/
theorem expLC_loc2 (C : Matrix (Lam d L N) (Lam d L N) ℂ) (α β : ℂ) (a : Lam d L N) :
    ∃ α' : ℂ, expLC C (α • (1 : Alg d L N) + β • pbp a) = α' • (1 : Alg d L N) + β • pbp a := by
  obtain ⟨r, hr⟩ := expLC_pbp C a
  refine ⟨α + β * r, ?_⟩
  rw [map_add, map_smul, map_smul, expLC_one', hr, smul_add, smul_smul, add_smul]
  abel

/-- **The hypothesis bundle of a sequence of observable steps** (Case (2)). -/
structure MuChain2 (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : ℕ → OFam .two d L N) (K : ℕ → OAct .two d L N) (n : ℕ) : Prop where
  hN : n < N
  hW0 : ∀ b, (W 0 b : SA .two (Lam d L N)).a = 0
  hW : ∀ k < n, ∀ c', (W (k + 1) c' : SA .two (Lam d L N)).a =
    (Wnext2O P k (C k) (V k) (W k) c' : SA .two (Lam d L N)).a
  hV : ∀ k < n, ∀ c', (V (k + 1) c' : SA .two (Lam d L N)).a =
    (Vnext2O P k (C k) (V k) (W k) (K k) c' : SA .two (Lam d L N)).a
  /-- the `a` component of `V_k(B)` is `α + m₂(V_k(B)_a) ψ̄_aψ_a` -/
  hform : ∀ k ≤ n, ∀ b, ∃ α : ℂ, (V k b : SA .two (Lam d L N)).a =
    α • (1 : Alg d L N) + mass2 (V k b : SA .two (Lam d L N)).a • pbp P.a

/-- The activity term of a `(j+1)`-block (Case (2)). -/
def muQX2 (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (K : ℕ → OAct .two d L N) (j : ℕ) (X : Finset (Lam d L N)) : ℂ :=
  ∑ b ∈ blocks j X, mass2 (EthO (C j) (Q2O P j (K j) b) : SA .two (Lam d L N)).a

/-- The drift of a region (Case (2)): `∑_{k<j} (β_k(X) - β_j(X)) tadInc2 k j`. -/
def muDriftX2 (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V : ℕ → OFam .two d L N) (j : ℕ) (X : Finset (Lam d L N)) : ℂ :=
  ∑ k ∈ range j, (betaX2 k (V k) X - betaX2 j (V j) X) * tadInc2 P C V k j

/-- The product increments of a region (Case (2)). -/
def muProdIncX2 (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : ℕ → OFam .two d L N) (j : ℕ) (X : Finset (Lam d L N)) : ℂ :=
  ∑ k ∈ range j, (wProdX P k (C k) (V k) (W k) mass2L X (C j + cumBetween C k j) -
    wProdX P k (C k) (V k) (W k) mass2L X (cumBetween C k j))

/-- The error of the per-block `μ^{(2)}` flow of the region `X`. -/
def shareErr2 (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : ℕ → OFam .two d L N) (K : ℕ → OAct .two d L N) (j : ℕ) (X : Finset (Lam d L N)) : ℂ :=
  muQX2 P C K j X + (muDriftX2 P C V j X + wTadX j mass2L (W j) X 0 + muProdIncX2 P C V W j X)

namespace MuChain2

variable {P : ObsPts d L N} {C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ}
  {V W : ℕ → OFam .two d L N} {K : ℕ → OAct .two d L N} {n : ℕ} (H : MuChain2 P C V W K n)
include H

theorem VprO_a {k : ℕ} (hk : k ≤ n) (b : Fin d → ℕ) :
    ∃ α' : ℂ, (VprO (C k) (V k) b : SA .two (Lam d L N)).a =
      α' • (1 : Alg d L N) + mass2 (V k b : SA .two (Lam d L N)).a • pbp P.a := by
  obtain ⟨α, hα⟩ := H.hform k hk b
  obtain ⟨α', h'⟩ := expLC_loc2 (C k) α (mass2 (V k b : SA .two (Lam d L N)).a) P.a
  refine ⟨α', ?_⟩
  rw [VprO, EthO_a_eq, ← h', ← hα]

theorem mass2_VprO_a {k : ℕ} (hk : k ≤ n) (b : Fin d → ℕ) :
    mass2 (VprO (C k) (V k) b : SA .two (Lam d L N)).a = mass2 (V k b : SA .two (Lam d L N)).a := by
  obtain ⟨α', h⟩ := H.VprO_a hk b
  rw [h, mass2_loc]

theorem SFO_a {k : ℕ} (hk : k ≤ n) (b : Fin d → ℕ) :
    (SFO k (C k) (V k) b : SA .two (Lam d L N)).a =
      mass2 (V k b : SA .two (Lam d L N)).a • FC (C k) (pbp P.a) (bulkE2 C V k) := by
  have h := SFO_cmp k (C k) (V k) true b
  simp only [cmp_true] at h
  obtain ⟨α', h'⟩ := H.VprO_a hk b
  rw [h, h', FC_loc2]
  rfl

/-- The one-loop tadpole of the block `B` (Case (2)). -/
theorem SFO_tad {k : ℕ} (hk : k ≤ n) (b : Fin d → ℕ) (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) :
    mass2L (expLC Γ (SFO k (C k) (V k) b : SA .two (Lam d L N)).a) -
        mass2L (SFO k (C k) (V k) b : SA .two (Lam d L N)).a =
      mass2 (V k b : SA .two (Lam d L N)).a * tau2 (C k) Γ P.a (bulkE2 C V k) := by
  rw [H.SFO_a hk b, map_smul]
  show mass2 _ - mass2 _ = _
  rw [mass2_smul, mass2_smul, tau2, mul_sub]

theorem mass2_SFO {k : ℕ} (hk : k ≤ n) (b : Fin d → ℕ) :
    mass2 (SFO k (C k) (V k) b : SA .two (Lam d L N)).a =
      mass2 (V k b : SA .two (Lam d L N)).a * nuBar2 P C V k := by
  rw [H.SFO_a hk b, mass2_smul, nuBar2]

theorem wTadX_succ {k : ℕ} (hk : k < n) {X : Finset (Lam d L N)} (hX : IsPolymer (k + 1) X)
    (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) :
    wTadX (k + 1) mass2L (W (k + 1)) X Γ =
      betaX2 k (V k) X * tau2 (C k) Γ P.a (bulkE2 C V k) +
        wProdX P k (C k) (V k) (W k) mass2L X Γ +
        (wTadX k mass2L (W k) X (Γ + C k) - wTadX k mass2L (W k) X (C k)) := by
  have e : wTadX (k + 1) mass2L (W (k + 1)) X Γ =
      wTadX (k + 1) mass2L (Wnext2O P k (C k) (V k) (W k)) X Γ := by
    unfold wTadX
    exact sum_congr rfl fun c' _ => by rw [H.hW k hk c']
  rw [e, wTadX_step k (C k) (V k) (W k) Γ (locMass_two P.a) hX]
  rw [sum_congr rfl fun b _ => H.SFO_tad hk.le b Γ, ← sum_mul, betaX2]
  ring

theorem wTadX_zero (X : Finset (Lam d L N)) (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) :
    wTadX 0 mass2L (W 0) X Γ = 0 := by
  unfold wTadX
  exact sum_eq_zero fun b _ => by rw [H.hW0 b, map_zero, map_zero]

/-- **The unrolled tadpole functional of a region** (Case (2)). -/
theorem wTadX_unroll {j : ℕ} (hj : j ≤ n) {X : Finset (Lam d L N)} (hX : IsPolymer j X)
    (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) :
    wTadX j mass2L (W j) X Γ = wTadX j mass2L (W j) X 0 +
      ∑ k ∈ range j, (betaX2 k (V k) X * (tau2 (C k) (Γ + cumBetween C k j) P.a (bulkE2 C V k) -
          tau2 (C k) (cumBetween C k j) P.a (bulkE2 C V k)) +
        (wProdX P k (C k) (V k) (W k) mass2L X (Γ + cumBetween C k j) -
          wProdX P k (C k) (V k) (W k) mass2L X (cumBetween C k j))) := by
  classical
  let G : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ → ℂ := fun k Γ =>
    if k ≤ j then wTadX k mass2L (W k) X Γ else 0
  let T : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ → ℂ := fun k Γ =>
    if k < j then betaX2 k (V k) X * tau2 (C k) Γ P.a (bulkE2 C V k) +
      wProdX P k (C k) (V k) (W k) mass2L X Γ
    else -(G k (Γ + C k) - G k (C k))
  have h0 : ∀ Γ, G 0 Γ = G 0 0 := fun Γ => by
    show (if 0 ≤ j then _ else _) = (if 0 ≤ j then _ else _)
    rw [if_pos (Nat.zero_le j), if_pos (Nat.zero_le j), H.wTadX_zero, H.wTadX_zero]
  have hs : ∀ k Γ, G (k + 1) Γ = T k Γ + (G k (Γ + C k) - G k (C k)) := by
    intro k Γ
    by_cases hk : k < j
    · simp only [G, T, if_pos hk, if_pos (show k + 1 ≤ j by omega), if_pos hk.le]
      rw [H.wTadX_succ (by omega) (Step2.isPolymer_of_le hX (k + 1) (by omega))]
    · simp only [T, if_neg hk]
      simp only [G, if_neg (show ¬ k + 1 ≤ j by omega)]
      ring
  have hu := tad_unroll G T C h0 hs j Γ
  simp only [G, if_pos le_rfl] at hu
  rw [hu]
  congr 1
  refine sum_congr rfl fun k hk => ?_
  have hk' : k < j := mem_range.1 hk
  simp only [T, if_pos hk']
  ring

/-- **The per-block `μ^{(2)}` flow** (sharp splitting): for `j < n` and every `(j+1)`-block
`B_+ = X`, `c_{j+1}(B_+) = β_j(B_+)(1 - 𝔫^{(2)}_j) - err_j(B_+)`. -/
theorem share2_flow_exact {j : ℕ} (hj : j < n) {c' : Fin d → ℕ}
    (hc' : c' ∈ blockIdx (L := L) (N := N) (j + 1)) :
    mass2 (V (j + 1) c' : SA .two (Lam d L N)).a =
      betaX2 j (V j) (blockSet (L := L) (N := N) (j + 1) c') * (1 - frakN2 P C V j) -
        shareErr2 P C V W K j (blockSet (L := L) (N := N) (j + 1) c') := by
  set X := blockSet (L := L) (N := N) (j + 1) c'
  have hX : IsPolymer j X := IsPolymer.of_succ (isPolymer_blockSet (j + 1) c')
  have h := share_step P j (C j) (V j) (W j) (K j) mass2L (fun r => mass2_algebraMap r)
    (locMass_two P.a) hc'
  have hS : ∀ b, mass2L (SbO j (C j) (V j) (W j) b : SA .two (Lam d L N)).a =
      mass2 (V j b : SA .two (Lam d L N)).a * nuBar2 P C V j +
        mass2 (EthO (C j) (W j b) : SA .two (Lam d L N)).a := by
    intro b
    show mass2 _ = _
    rw [SbO, Subalgebra.coe_add, add_a, mass2_add, H.mass2_SFO hj.le b]
  have hVp : ∀ b, mass2L (VprO (C j) (V j) b : SA .two (Lam d L N)).a =
      mass2 (V j b : SA .two (Lam d L N)).a := fun b => H.mass2_VprO_a hj.le b
  rw [H.hV j hj c']
  show mass2L _ = _
  rw [h]
  simp only [hS, hVp]
  have hW : ∑ b ∈ blocks j X, mass2 (EthO (C j) (W j b) : SA .two (Lam d L N)).a =
      wTadX j mass2L (W j) X (C j) := by
    unfold wTadX
    exact sum_congr rfl fun b _ => by rw [EthO_a_eq]; rfl
  have hQ : ∑ b ∈ blocks j X, mass2L (EthO (C j) (Q2O P j (K j) b) : SA .two (Lam d L N)).a =
      muQX2 P C K j X := rfl
  simp only [sum_sub_distrib, sum_add_distrib]
  rw [hQ, hW, H.wTadX_unroll hj.le hX (C j)]
  have hτ : ∑ k ∈ range j, betaX2 k (V k) X *
      (tau2 (C k) (C j + cumBetween C k j) P.a (bulkE2 C V k) -
        tau2 (C k) (cumBetween C k j) P.a (bulkE2 C V k)) =
      betaX2 j (V j) X * ∑ k ∈ range j, tadInc2 P C V k j + muDriftX2 P C V j X := by
    rw [muDriftX2, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun k _ => by rw [tadInc2]; ring
  rw [sum_add_distrib, hτ, frakN2, shareErr2, muProdIncX2, ← sum_mul, ← betaX2]
  ring

/-- **The total `μ^{(2)}` flow**: `β_{j+1} = β_j(1 - 𝔫^{(2)}_j) - ∑_{B_+} err_j(B_+)`. -/
theorem betaTot2_succ_eq {j : ℕ} (hj : j < n) :
    betaTot2 (L := L) (N := N) (j + 1) (V (j + 1)) =
      betaTot2 (L := L) (N := N) j (V j) * (1 - frakN2 P C V j) -
        ∑ c' ∈ blockIdx (L := L) (N := N) (j + 1),
          shareErr2 P C V W K j (blockSet (L := L) (N := N) (j + 1) c') := by
  unfold betaTot2
  rw [sum_congr rfl fun c' hc' => H.share2_flow_exact hj hc', sum_sub_distrib, ← sum_mul]
  congr 2
  unfold betaX2
  exact sum_blockIdx_succ j _

end MuChain2

end

end Obs2
