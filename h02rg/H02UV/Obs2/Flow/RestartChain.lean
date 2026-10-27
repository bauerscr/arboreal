import Obs2.Flow.MuChain2

/-!
# The `μ^{(2)}` chain started at scale `m` with a general datum (B3, T4)

Copy of `Obs2/Flow/MuChain2` for the observable flow started at an intermediate scale `m` from a
datum `(V_m, 𝒲_m, K_m)` with **`𝒲_m ≠ 0`** (the restart). The flow relations hold for
`m ≤ k < n`, the form `V_k(B)_a = α + c_k(B)ψ̄_aψ_a` for `m ≤ k ≤ n`.

* `cumFrom C m j = ∑_{m≤i<j} C_i`; **`tad_unroll_gen`**: the tadpole recursion unrolled from
  `j₀` with a nonzero initial functional:
  `G_j(Γ) = G_j(0) + ∑_{j₀≤k<j}(T_k(Γ + S_{k,j}) − T_k(S_{k,j})) + (G_{j₀}(Γ + S'_{j₀,j}) −
  G_{j₀}(S'_{j₀,j}))`, `S' = cumFrom`;
* `frakN2F m j = ν̄^{(2)}_j + ∑_{m≤k<j} tadInc2 k j` (the one-loop coefficient of the restarted
  flow; it differs from `𝔫^{(2)}_j` by the memory `∑_{k<m}` of the earlier scales);
* `wInitX2 m j X = G_m(X; C_j + S'_{m,j}) − G_m(X; S'_{m,j})`: the tadpole of the initial `𝒲_m`
  against the covariance `C_j` (the new source of the restart);
* `shareErr2F = muQX2 + muDriftX2F + G_j(X;0) + muProdIncX2F + wInitX2` (memory sums over
  `m ≤ k < j`);
* **`MuChain2F.share2_flow_exactF`**: `c_{j+1}(B_+) = β_j(B_+)(1 − 𝔫F_j) − errF_j(B_+)`;
  **`MuChain2F.betaTot2_succ_eqF`**: `β_{j+1} = β_j(1 − 𝔫F_j) − ∑_{B_+}errF_j(B_+)`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 LocObs

/-- `S'_{m,j} = ∑_{m ≤ i < j} C_i`. -/
def cumFrom {M : Type*} [AddCommMonoid M] (C : ℕ → M) (m j : ℕ) : M := ∑ i ∈ Ico m j, C i

theorem cumFrom_self {M : Type*} [AddCommMonoid M] (C : ℕ → M) (m : ℕ) : cumFrom C m m = 0 := by
  simp [cumFrom]

theorem cumFrom_succ {M : Type*} [AddCommMonoid M] (C : ℕ → M) {m j : ℕ} (h : m ≤ j) :
    cumFrom C m (j + 1) = cumFrom C m j + C j := by
  unfold cumFrom; rw [sum_Ico_succ_top h]

/-- **Unrolling the tadpole recursion from `j₀` with a nonzero initial functional.** -/
theorem tad_unroll_gen {M : Type*} [AddCommMonoid M] (G T : ℕ → M → ℂ) (C : ℕ → M) (j0 : ℕ)
    (hs : ∀ k, j0 ≤ k → ∀ Γ, G (k + 1) Γ = T k Γ + (G k (Γ + C k) - G k (C k))) :
    ∀ j, j0 ≤ j → ∀ Γ, G j Γ = G j 0 +
      ∑ k ∈ Ico j0 j, (T k (Γ + cumBetween C k j) - T k (cumBetween C k j)) +
      (G j0 (Γ + cumFrom C j0 j) - G j0 (cumFrom C j0 j)) := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => intro Γ; rw [Ico_self, sum_empty, cumFrom_self, add_zero, add_zero]; ring
  | succ j hj ih =>
    intro Γ
    have hG0 : G (j + 1) 0 = T j 0 := by rw [hs j hj 0, zero_add, sub_self, add_zero]
    rw [hs j hj Γ, hG0, ih (Γ + C j), ih (C j), sum_Ico_succ_top hj, cumBetween_self_succ,
      add_zero, cumFrom_succ C hj]
    have e : ∀ k ∈ Ico j0 j, T k (Γ + cumBetween C k (j + 1)) - T k (cumBetween C k (j + 1)) =
        T k (Γ + C j + cumBetween C k j) - T k (C j + cumBetween C k j) := by
      intro k hk
      rw [cumBetween_succ C (mem_Ico.1 hk).2, add_comm (cumBetween C k j) (C j), add_assoc]
    rw [sum_congr rfl e]
    have e2 : Γ + (cumFrom C j0 j + C j) = Γ + C j + cumFrom C j0 j := by
      rw [add_comm (cumFrom C j0 j) (C j), add_assoc]
    have e3 : cumFrom C j0 j + C j = C j + cumFrom C j0 j := add_comm _ _
    rw [e2, e3]
    have hsum : ∑ k ∈ Ico j0 j, (T k (Γ + C j + cumBetween C k j) - T k (cumBetween C k j)) -
        ∑ k ∈ Ico j0 j, (T k (C j + cumBetween C k j) - T k (cumBetween C k j)) =
        ∑ k ∈ Ico j0 j, (T k (Γ + C j + cumBetween C k j) - T k (C j + cumBetween C k j)) := by
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun k _ => by ring
    linear_combination hsum

variable {d L N : ℕ} [NeZero L]

/-- The one-loop coefficient of the flow restarted at `m`. -/
def frakN2F (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V : ℕ → OFam .two d L N) (m j : ℕ) : ℂ :=
  nuBar2 P C V j + ∑ k ∈ Ico m j, tadInc2 P C V k j

/-- The drift of a region, from `m`. -/
def muDriftX2F (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V : ℕ → OFam .two d L N) (m j : ℕ) (X : Finset (Lam d L N)) : ℂ :=
  ∑ k ∈ Ico m j, (betaX2 k (V k) X - betaX2 j (V j) X) * tadInc2 P C V k j

/-- The product increments of a region, from `m`. -/
def muProdIncX2F (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : ℕ → OFam .two d L N) (m j : ℕ) (X : Finset (Lam d L N)) : ℂ :=
  ∑ k ∈ Ico m j, (wProdX P k (C k) (V k) (W k) mass2L X (C j + cumBetween C k j) -
    wProdX P k (C k) (V k) (W k) mass2L X (cumBetween C k j))

/-- The tadpole of the initial `𝒲_m` against the covariance `C_j`. -/
def wInitX2 (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ) (W : ℕ → OFam .two d L N) (m j : ℕ)
    (X : Finset (Lam d L N)) : ℂ :=
  wTadX m mass2L (W m) X (C j + cumFrom C m j) - wTadX m mass2L (W m) X (cumFrom C m j)

/-- The error of the per-block flow of the region `X`, restarted at `m`. -/
def shareErr2F (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : ℕ → OFam .two d L N) (K : ℕ → OAct .two d L N) (m j : ℕ) (X : Finset (Lam d L N)) : ℂ :=
  muQX2 P C K j X + (muDriftX2F P C V m j X + wTadX j mass2L (W j) X 0 +
    muProdIncX2F P C V W m j X + wInitX2 C W m j X)

/-- **The `μ^{(2)}` chain from scale `m`** (hypothesis bundle). -/
structure MuChain2F (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : ℕ → OFam .two d L N) (K : ℕ → OAct .two d L N) (m n : ℕ) : Prop where
  hmn : m ≤ n
  hN : n < N
  hW : ∀ k, m ≤ k → k < n → ∀ c', (W (k + 1) c' : SA .two (Lam d L N)).a =
    (Wnext2O P k (C k) (V k) (W k) c' : SA .two (Lam d L N)).a
  hV : ∀ k, m ≤ k → k < n → ∀ c', (V (k + 1) c' : SA .two (Lam d L N)).a =
    (Vnext2O P k (C k) (V k) (W k) (K k) c' : SA .two (Lam d L N)).a
  hform : ∀ k, m ≤ k → k ≤ n → ∀ b, ∃ α : ℂ, (V k b : SA .two (Lam d L N)).a =
    α • (1 : Alg d L N) + mass2 (V k b : SA .two (Lam d L N)).a • pbp P.a

namespace MuChain2F

variable {P : ObsPts d L N} {C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ}
  {V W : ℕ → OFam .two d L N} {K : ℕ → OAct .two d L N} {m n : ℕ} (H : MuChain2F P C V W K m n)
include H

theorem VprO_a {k : ℕ} (hmk : m ≤ k) (hk : k ≤ n) (b : Fin d → ℕ) :
    ∃ α' : ℂ, (VprO (C k) (V k) b : SA .two (Lam d L N)).a =
      α' • (1 : Alg d L N) + mass2 (V k b : SA .two (Lam d L N)).a • pbp P.a := by
  obtain ⟨α, hα⟩ := H.hform k hmk hk b
  obtain ⟨α', h'⟩ := expLC_loc2 (C k) α (mass2 (V k b : SA .two (Lam d L N)).a) P.a
  refine ⟨α', ?_⟩
  rw [VprO, EthO_a_eq, ← h', ← hα]

theorem mass2_VprO_a {k : ℕ} (hmk : m ≤ k) (hk : k ≤ n) (b : Fin d → ℕ) :
    mass2 (VprO (C k) (V k) b : SA .two (Lam d L N)).a = mass2 (V k b : SA .two (Lam d L N)).a := by
  obtain ⟨α', h⟩ := H.VprO_a hmk hk b
  rw [h, mass2_loc]

theorem SFO_a {k : ℕ} (hmk : m ≤ k) (hk : k ≤ n) (b : Fin d → ℕ) :
    (SFO k (C k) (V k) b : SA .two (Lam d L N)).a =
      mass2 (V k b : SA .two (Lam d L N)).a • FC (C k) (pbp P.a) (bulkE2 C V k) := by
  have h := SFO_cmp k (C k) (V k) true b
  simp only [cmp_true] at h
  obtain ⟨α', h'⟩ := H.VprO_a hmk hk b
  rw [h, h', FC_loc2]
  rfl

theorem SFO_tad {k : ℕ} (hmk : m ≤ k) (hk : k ≤ n) (b : Fin d → ℕ)
    (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) :
    mass2L (expLC Γ (SFO k (C k) (V k) b : SA .two (Lam d L N)).a) -
        mass2L (SFO k (C k) (V k) b : SA .two (Lam d L N)).a =
      mass2 (V k b : SA .two (Lam d L N)).a * tau2 (C k) Γ P.a (bulkE2 C V k) := by
  rw [H.SFO_a hmk hk b, map_smul]
  show mass2 _ - mass2 _ = _
  rw [mass2_smul, mass2_smul, tau2, mul_sub]

theorem mass2_SFO {k : ℕ} (hmk : m ≤ k) (hk : k ≤ n) (b : Fin d → ℕ) :
    mass2 (SFO k (C k) (V k) b : SA .two (Lam d L N)).a =
      mass2 (V k b : SA .two (Lam d L N)).a * nuBar2 P C V k := by
  rw [H.SFO_a hmk hk b, mass2_smul, nuBar2]

theorem wTadX_succ {k : ℕ} (hmk : m ≤ k) (hk : k < n) {X : Finset (Lam d L N)}
    (hX : IsPolymer (k + 1) X) (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) :
    wTadX (k + 1) mass2L (W (k + 1)) X Γ =
      betaX2 k (V k) X * tau2 (C k) Γ P.a (bulkE2 C V k) +
        wProdX P k (C k) (V k) (W k) mass2L X Γ +
        (wTadX k mass2L (W k) X (Γ + C k) - wTadX k mass2L (W k) X (C k)) := by
  have e : wTadX (k + 1) mass2L (W (k + 1)) X Γ =
      wTadX (k + 1) mass2L (Wnext2O P k (C k) (V k) (W k)) X Γ := by
    unfold wTadX
    exact sum_congr rfl fun c' _ => by rw [H.hW k hmk hk c']
  rw [e, wTadX_step k (C k) (V k) (W k) Γ (locMass_two P.a) hX]
  rw [sum_congr rfl fun b _ => H.SFO_tad hmk hk.le b Γ, ← sum_mul, betaX2]
  ring

/-- **The unrolled tadpole functional of a region**, from `m` (with the initial `𝒲_m`). -/
theorem wTadX_unrollF {j : ℕ} (hmj : m ≤ j) (hj : j ≤ n) {X : Finset (Lam d L N)}
    (hX : IsPolymer j X) (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) :
    wTadX j mass2L (W j) X Γ = wTadX j mass2L (W j) X 0 +
      ∑ k ∈ Ico m j, (betaX2 k (V k) X * (tau2 (C k) (Γ + cumBetween C k j) P.a (bulkE2 C V k) -
          tau2 (C k) (cumBetween C k j) P.a (bulkE2 C V k)) +
        (wProdX P k (C k) (V k) (W k) mass2L X (Γ + cumBetween C k j) -
          wProdX P k (C k) (V k) (W k) mass2L X (cumBetween C k j))) +
      (wTadX m mass2L (W m) X (Γ + cumFrom C m j) - wTadX m mass2L (W m) X (cumFrom C m j)) := by
  classical
  let G : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ → ℂ := fun k Γ =>
    if k ≤ j then wTadX k mass2L (W k) X Γ else 0
  let T : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ → ℂ := fun k Γ =>
    if k < j then betaX2 k (V k) X * tau2 (C k) Γ P.a (bulkE2 C V k) +
      wProdX P k (C k) (V k) (W k) mass2L X Γ
    else -(G k (Γ + C k) - G k (C k))
  have hs : ∀ k, m ≤ k → ∀ Γ, G (k + 1) Γ = T k Γ + (G k (Γ + C k) - G k (C k)) := by
    intro k hmk Γ
    by_cases hk : k < j
    · simp only [G, T, if_pos hk, if_pos (show k + 1 ≤ j by omega), if_pos hk.le]
      rw [H.wTadX_succ hmk (by omega) (Step2.isPolymer_of_le hX (k + 1) (by omega))]
    · simp only [T, if_neg hk]
      simp only [G, if_neg (show ¬ k + 1 ≤ j by omega)]
      ring
  have hu := tad_unroll_gen G T C m hs j hmj Γ
  simp only [G, if_pos le_rfl, if_pos hmj] at hu
  rw [hu]
  congr 2
  refine sum_congr rfl fun k hk => ?_
  have hk' : k < j := (mem_Ico.1 hk).2
  simp only [T, if_pos hk']
  ring

/-- **The per-block `μ^{(2)}` flow, restarted at `m`**: for `m ≤ j < n` and every
`(j+1)`-block `B_+`, `c_{j+1}(B_+) = β_j(B_+)(1 − 𝔫F_j) − errF_j(B_+)`. -/
theorem share2_flow_exactF {j : ℕ} (hmj : m ≤ j) (hj : j < n) {c' : Fin d → ℕ}
    (hc' : c' ∈ blockIdx (L := L) (N := N) (j + 1)) :
    mass2 (V (j + 1) c' : SA .two (Lam d L N)).a =
      betaX2 j (V j) (blockSet (L := L) (N := N) (j + 1) c') * (1 - frakN2F P C V m j) -
        shareErr2F P C V W K m j (blockSet (L := L) (N := N) (j + 1) c') := by
  set X := blockSet (L := L) (N := N) (j + 1) c'
  have hX : IsPolymer j X := IsPolymer.of_succ (isPolymer_blockSet (j + 1) c')
  have h := share_step P j (C j) (V j) (W j) (K j) mass2L (fun r => mass2_algebraMap r)
    (locMass_two P.a) hc'
  have hS : ∀ b, mass2L (SbO j (C j) (V j) (W j) b : SA .two (Lam d L N)).a =
      mass2 (V j b : SA .two (Lam d L N)).a * nuBar2 P C V j +
        mass2 (EthO (C j) (W j b) : SA .two (Lam d L N)).a := by
    intro b
    show mass2 _ = _
    rw [SbO, Subalgebra.coe_add, add_a, mass2_add, H.mass2_SFO hmj hj.le b]
  have hVp : ∀ b, mass2L (VprO (C j) (V j) b : SA .two (Lam d L N)).a =
      mass2 (V j b : SA .two (Lam d L N)).a := fun b => H.mass2_VprO_a hmj hj.le b
  rw [H.hV j hmj hj c']
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
  rw [hQ, hW, H.wTadX_unrollF hmj hj.le hX (C j)]
  have hτ : ∑ k ∈ Ico m j, betaX2 k (V k) X *
      (tau2 (C k) (C j + cumBetween C k j) P.a (bulkE2 C V k) -
        tau2 (C k) (cumBetween C k j) P.a (bulkE2 C V k)) =
      betaX2 j (V j) X * ∑ k ∈ Ico m j, tadInc2 P C V k j + muDriftX2F P C V m j X := by
    rw [muDriftX2F, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun k _ => by rw [tadInc2]; ring
  rw [sum_add_distrib, hτ, frakN2F, shareErr2F, muProdIncX2F, wInitX2, ← sum_mul, ← betaX2]
  ring

/-- **The total `μ^{(2)}` flow, restarted at `m`**:
`β_{j+1} = β_j(1 − 𝔫F_j) − ∑_{B_+} errF_j(B_+)`. -/
theorem betaTot2_succ_eqF {j : ℕ} (hmj : m ≤ j) (hj : j < n) :
    betaTot2 (L := L) (N := N) (j + 1) (V (j + 1)) =
      betaTot2 (L := L) (N := N) j (V j) * (1 - frakN2F P C V m j) -
        ∑ c' ∈ blockIdx (L := L) (N := N) (j + 1),
          shareErr2F P C V W K m j (blockSet (L := L) (N := N) (j + 1) c') := by
  unfold betaTot2
  rw [sum_congr rfl fun c' hc' => H.share2_flow_exactF hmj hj hc', sum_sub_distrib, ← sum_mul]
  congr 2
  unfold betaX2
  exact sum_blockIdx_succ j _

end MuChain2F

end

end Obs2
