import Obs2.Flow.BlockMass
import Obs2.Flow.MuTad3
import Step2.Coup.CoupPast6

/-!
# The per-block `μ^{(1)}` flow (Case (1), sharp splitting)

With the sharp splitting `S^♯` of `Obs2.Map.Map` the one-loop term of `S(B)_a` stays with the block
carrying the share (`mass_SbO_a_one`), and `Loc_{B_+,·}`, `𝒲_{j+1}(B_+)` are hierarchical. So the
proof of `MuChain.mu_flow_exact` runs for every region `X` which is a union of blocks of the
coarsest scale, with the tadpole functional restricted to the blocks of `X`:

* `wTadX k m W X Γ = ∑_{B ∈ 𝓑_k(X)} m(e^{ℒ_Γ} 𝒲(B)_a)`, `wProdX` (the product parts in `X`),
  `betaX k V X = ∑_{B ∈ 𝓑_k(X)} m₁(V(B)_a)` (the coupling of the region);
* `wTadX_step`: `G_{j+1}(X; Γ) = ∑_{B ∈ 𝓑_j(X)} (m(e^{ℒ_Γ} S^{(2)}(B)_a) − m(S^{(2)}(B)_a))
  + (G_j(X; Γ + C) − G_j(X; C)) + P_{j+1}(X; Γ)` for a `(j+1)`-polymer `X`;
* along a `MuChain`: `MuChain.wTadX_succ`, `MuChain.wTadX_unroll` (the region version of
  `wTad_unroll`), and
* **`MuChain.share_flow_exact`**: for every `(j+1)`-block `B_+`,
  `c_{j+1}(B_+) = β_j(B_+)(1 − 𝔫_j) − ∑_{B ⊆ B_+} m₁((𝔼θQ(B))_a) − (drift_j(B_+) + G_j(B_+; 0)
  + prodInc_j(B_+))`, `β_j(B_+) = ∑_{B ⊆ B_+} c_j(B)`, with the same `𝔫_j` as the total flow.
  Only the activity term `Q` moves mass across `(j+1)`-blocks.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 LocObs

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

/-- `G_k(X; Γ) = ∑_{B ∈ 𝓑_k(X)} m(e^{ℒ_Γ} 𝒲(B)_a)`. -/
def wTadX (k : ℕ) (m : Alg d L N →ₗ[ℂ] ℂ) (W : OFam c d L N) (X : Finset (Lam d L N))
    (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) : ℂ :=
  ∑ b ∈ blocks k X, m (expLC Γ (W b : SA c (Lam d L N)).a)

/-- The product part in the region `X`:
`P_{j+1}(X; Γ) = ∑_{B_+ ∈ 𝓑_{j+1}(X)} m(e^{ℒ_Γ}(𝒲_{j+1}(B_+) − ∑_{B ⊆ B_+} 𝒲'(B))_a)`. -/
def wProdX (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V W : OFam c d L N)
    (m : Alg d L N →ₗ[ℂ] ℂ) (X : Finset (Lam d L N)) (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) : ℂ :=
  ∑ c' ∈ blocks (j + 1) X,
    m (expLC Γ ((Wnext2O P j C V W c' - ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
      WpO P j C V W b : OE c (Lam d L N)) : SA c (Lam d L N)).a)

/-- The coupling of the region `X` at scale `k`: `β_k(X) = ∑_{B ∈ 𝓑_k(X)} m₁(V(B)_a)`. -/
def betaX (k : ℕ) (V : OFam .one d L N) (X : Finset (Lam d L N)) : ℂ :=
  ∑ b ∈ blocks k X, mass1 (-1) (V b : SA .one (Lam d L N)).a

section Step

variable (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
  (V W : OFam c d L N) (m : Alg d L N →ₗ[ℂ] ℂ) (Γ : Matrix (Lam d L N) (Lam d L N) ℂ)

variable {P m}

/-- **The tadpole recursion in a region** `X` (a `(j+1)`-polymer). -/
theorem wTadX_step (hm : LocMass c P.a m) {X : Finset (Lam d L N)} (hX : IsPolymer (j + 1) X) :
    wTadX (j + 1) m (Wnext2O P j C V W) X Γ =
      ∑ b ∈ blocks j X, (m (expLC Γ (SFO j C V b : SA c (Lam d L N)).a) -
        m (SFO j C V b : SA c (Lam d L N)).a) +
      (wTadX j m W X (Γ + C) - wTadX j m W X C) + wProdX P j C V W m X Γ := by
  have h1 : ∀ c', m (expLC Γ (Wnext2O P j C V W c' : SA c (Lam d L N)).a) =
      m (expLC Γ ((Wnext2O P j C V W c' - ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
        WpO P j C V W b : OE c (Lam d L N)) : SA c (Lam d L N)).a) +
      ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
        m (expLC Γ (WpO P j C V W b : SA c (Lam d L N)).a) := by
    intro c'
    rw [AddSubgroupClass.coe_sub, sub_a, map_sub, map_sub, AddSubmonoidClass.coe_finsetSum,
      sum_a, map_sum, map_sum]
    ring
  have h2 : ∀ b, m (expLC Γ (WpO P j C V W b : SA c (Lam d L N)).a) =
      m (expLC Γ (SbO j C V W b : SA c (Lam d L N)).a) -
        m (LSO P j C V W b : SA c (Lam d L N)).a := by
    intro b
    have e : (WpO P j C V W b : SA c (Lam d L N)).a =
        (SbO j C V W b : SA c (Lam d L N)).a - (LSO P j C V W b : SA c (Lam d L N)).a := rfl
    have h3 : m (expLC Γ (LSO P j C V W b : SA c (Lam d L N)).a) =
        m (LSO P j C V W b : SA c (Lam d L N)).a :=
      hm.exp Γ (Step2.Bp (L := L) (N := N) j b) (blockSet j b) _
    rw [e, map_sub, map_sub, h3]
  have hS : ∀ b, (SbO j C V W b : SA c (Lam d L N)).a =
      (SFO j C V b : SA c (Lam d L N)).a + expLC C (W b : SA c (Lam d L N)).a := by
    intro b
    rw [SbO, Subalgebra.coe_add, add_a, EthO_a_eq]
  have hLS : ∀ c' ∈ blocks (j + 1) X,
      ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
        m (LSO P j C V W b : SA c (Lam d L N)).a =
      ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
        m (SbO j C V W b : SA c (Lam d L N)).a := fun c' hc' =>
    blk_LS P j C V W m hm (mem_blockIdx_of_mem_blocks hc')
  show ∑ c' ∈ blocks (j + 1) X, m (expLC Γ (Wnext2O P j C V W c' : SA c (Lam d L N)).a) = _
  rw [sum_congr rfl fun c' _ => h1 c', sum_add_distrib]
  simp only [h2, sum_sub_distrib]
  rw [sum_congr rfl hLS, Step2.sum_blocks_succ hX, Step2.sum_blocks_succ hX]
  simp only [hS, map_add, expLC_add, sum_add_distrib, wTadX, wProdX]
  ring

end Step

/-! ### Along a chain -/

namespace MuChain

variable {P : ObsPts d L N} {C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ}
  {V W : ℕ → OFam .one d L N} {K : ℕ → OAct .one d L N} {κ : ℕ → Step2.Coup} {r : ℕ → ℂ}
  {n : ℕ} (H : MuChain P C V W K κ r n)
include H

theorem VprO_a {k : ℕ} (hk : k ≤ n) (b : Fin d → ℕ) :
    (VprO (C k) (V k) b : SA .one (Lam d L N)).a =
      mass1 (-1) (V k b : SA .one (Lam d L N)).a • psibar P.a :=
  VprO_a_of_form (fun b => H.hform k hk b) b

/-- The one-loop tadpole of the block `B`: `m₁(e^{ℒ_Γ} S^{(2)}(B)_a) − m₁(S^{(2)}(B)_a) =
c_k(B) g'_k τ(C_k, Γ)`. -/
theorem SFO_tad {k : ℕ} (hk : k ≤ n) (b : Fin d → ℕ) (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) :
    mass1L (-1) (expLC Γ (SFO k (C k) (V k) b : SA .one (Lam d L N)).a) -
        mass1L (-1) (SFO k (C k) (V k) b : SA .one (Lam d L N)).a =
      mass1 (-1) (V k b : SA .one (Lam d L N)).a * ((κ k).g * tauC (C k) Γ P.a) := by
  have h := SFO_cmp k (C k) (V k) true b
  simp only [cmp_true] at h
  rw [h, H.VprO_a hk, H.he k hk]
  exact tad_FC_one (C k) Γ P.a (κ k) (r k) _

/-- The tadpole functional of a region along the chain. -/
theorem wTadX_succ {k : ℕ} (hk : k < n) {X : Finset (Lam d L N)} (hX : IsPolymer (k + 1) X)
    (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) :
    wTadX (k + 1) (mass1L (-1)) (W (k + 1)) X Γ =
      betaX k (V k) X * ((κ k).g * tauC (C k) Γ P.a) +
        wProdX P k (C k) (V k) (W k) (mass1L (-1)) X Γ +
        (wTadX k (mass1L (-1)) (W k) X (Γ + C k) - wTadX k (mass1L (-1)) (W k) X (C k)) := by
  have e : wTadX (k + 1) (mass1L (-1)) (W (k + 1)) X Γ =
      wTadX (k + 1) (mass1L (-1)) (Wnext2O P k (C k) (V k) (W k)) X Γ := by
    unfold wTadX
    exact sum_congr rfl fun c' _ => by rw [H.hW k hk c']
  rw [e, wTadX_step k (C k) (V k) (W k) Γ (locMass_one P.a) hX]
  rw [sum_congr rfl fun b _ => H.SFO_tad hk.le b Γ, ← sum_mul, betaX]
  ring

theorem wTadX_zero (X : Finset (Lam d L N)) (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) :
    wTadX 0 (mass1L (-1)) (W 0) X Γ = 0 := by
  unfold wTadX
  exact sum_eq_zero fun b _ => by rw [H.hW0 b, map_zero, map_zero]

/-- **The unrolled tadpole functional of a region** `X` (a `j`-polymer): for `j ≤ n`,
`G_j(X; Γ) = G_j(X; 0) + ∑_{k<j} [β_k(X) g'_k τ(C_k, Γ) + P_{k+1}(X; Γ + S_{k,j}) − P_{k+1}(X; S_{k,j})]`. -/
theorem wTadX_unroll {j : ℕ} (hj : j ≤ n) {X : Finset (Lam d L N)} (hX : IsPolymer j X)
    (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) :
    wTadX j (mass1L (-1)) (W j) X Γ = wTadX j (mass1L (-1)) (W j) X 0 +
      ∑ k ∈ range j, (betaX k (V k) X * ((κ k).g * tauC (C k) Γ P.a) +
        (wProdX P k (C k) (V k) (W k) (mass1L (-1)) X (Γ + cumBetween C k j) -
          wProdX P k (C k) (V k) (W k) (mass1L (-1)) X (cumBetween C k j))) := by
  classical
  let G : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ → ℂ := fun k Γ =>
    if k ≤ j then wTadX k (mass1L (-1)) (W k) X Γ else 0
  let T : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ → ℂ := fun k Γ =>
    if k < j then betaX k (V k) X * ((κ k).g * tauC (C k) Γ P.a) +
      wProdX P k (C k) (V k) (W k) (mass1L (-1)) X Γ
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
  simp only [T, if_pos hk', tauC_add_right]
  ring

end MuChain

/-- The drift of a region: `∑_{k<j} (β_k(X) g'_k − β_j(X) g'_j) τ(C_k, C_j)`. -/
def muDriftX (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V : ℕ → OFam .one d L N) (κ : ℕ → Step2.Coup) (j : ℕ) (X : Finset (Lam d L N)) : ℂ :=
  ∑ k ∈ range j, (betaX k (V k) X * (κ k).g - betaX j (V j) X * (κ j).g) *
    tauC (C k) (C j) P.a

/-- The product increments of a region. -/
def muProdIncX (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : ℕ → OFam .one d L N) (j : ℕ) (X : Finset (Lam d L N)) : ℂ :=
  ∑ k ∈ range j, (wProdX P k (C k) (V k) (W k) (mass1L (-1)) X (C j + cumBetween C k j) -
    wProdX P k (C k) (V k) (W k) (mass1L (-1)) X (cumBetween C k j))

/-- The activity term of a `(j+1)`-block: `∑_{B ⊆ B_+} m₁((𝔼θQ(B))_a)`. -/
def muQX (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (K : ℕ → OAct .one d L N) (j : ℕ) (X : Finset (Lam d L N)) : ℂ :=
  ∑ b ∈ blocks j X, mass1 (-1) (EthO (C j) (Q2O P j (K j) b) : SA .one (Lam d L N)).a

/-- The error of the per-block flow of the `(j+1)`-block `B_+ = X`. -/
def shareErr (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : ℕ → OFam .one d L N) (K : ℕ → OAct .one d L N) (κ : ℕ → Step2.Coup) (j : ℕ)
    (X : Finset (Lam d L N)) : ℂ :=
  muQX P C K j X + (muDriftX P C V κ j X + wTadX j (mass1L (-1)) (W j) X 0 +
    muProdIncX P C V W j X)

namespace MuChain

variable {P : ObsPts d L N} {C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ}
  {V W : ℕ → OFam .one d L N} {K : ℕ → OAct .one d L N} {κ : ℕ → Step2.Coup} {r : ℕ → ℂ}
  {n : ℕ} (H : MuChain P C V W K κ r n)
include H

/-- `ν̄_j = ν'_j ∑_x C_j(a,x)`. -/
theorem nuTot_eq {j : ℕ} (hj : j ≤ n) :
    nuTot P j (C j) (V j) = (κ j).nu * ∑ x, C j P.a x := by
  have h := total_FC_one (C j) P.a (κ j) (r j) 1
  rw [one_smul, one_mul] at h
  rw [nuTot, H.he j hj, h]

/-- **The per-block `μ^{(1)}` flow** (sharp splitting): for `j < n` and every `(j+1)`-block
`B_+ = X`, `c_{j+1}(B_+) = β_j(B_+)(1 − 𝔫_j) − err_j(B_+)` with
`err_j(B_+) = ∑_{B ⊆ B_+} m₁((𝔼θQ(B))_a) + drift_j(B_+) + G_j(B_+; 0) + prodInc_j(B_+)`. -/
theorem share_flow_exact {j : ℕ} (hj : j < n) {c' : Fin d → ℕ}
    (hc' : c' ∈ blockIdx (L := L) (N := N) (j + 1)) :
    mass1 (-1) (V (j + 1) c' : SA .one (Lam d L N)).a =
      betaX j (V j) (blockSet (L := L) (N := N) (j + 1) c') * (1 - frakN C κ P.a j) -
        shareErr P C V W K κ j (blockSet (L := L) (N := N) (j + 1) c') := by
  set X := blockSet (L := L) (N := N) (j + 1) c'
  have hX : IsPolymer j X := IsPolymer.of_succ (isPolymer_blockSet (j + 1) c')
  have hβ : ∀ b, (V j b : SA .one (Lam d L N)).a =
      (fun b => mass1 (-1) (V j b : SA .one (Lam d L N)).a) b • psibar P.a :=
    fun b => H.hform j hj.le b
  rw [H.hV j hj c', share_step_one (K := K j) j (W j) hβ hc', H.nuTot_eq hj.le]
  have hW : ∑ b ∈ blocks j X, mass1 (-1) (EthO (C j) (W j b) : SA .one (Lam d L N)).a =
      wTadX j (mass1L (-1)) (W j) X (C j) := by
    unfold wTadX
    exact sum_congr rfl fun b _ => by rw [EthO_a_eq]; rfl
  simp only [sum_sub_distrib]
  rw [hW, H.wTadX_unroll hj.le hX (C j)]
  have hτ : ∑ k ∈ range j, betaX k (V k) X * ((κ k).g * tauC (C k) (C j) P.a) =
      betaX j (V j) X * (κ j).g * tauC (wCum C j) (C j) P.a + muDriftX P C V κ j X := by
    rw [muDriftX, wCum, tauC_sum_left, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun k _ => by ring
  rw [sum_add_distrib, hτ, frakN, shareErr, muQX, muProdIncX, ← sum_mul, betaX]
  ring

end MuChain


/-! ### Concentration of the shares at the block of `a` -/

/-- The deviation of the shares from the block of `a`:
`D_k = ∑_B |c_k(B) − β_k 1_{a ∈ B}|`, `β_k = ∑_B c_k(B)`. -/
def shareDev (a : Lam d L N) (k : ℕ) (V : OFam .one d L N) : ℝ :=
  ∑ b ∈ blockIdx (L := L) (N := N) k,
    ‖mass1 (-1) (V b : SA .one (Lam d L N)).a -
      (if a ∈ blockSet (L := L) (N := N) k b then betaTot (L := L) (N := N) k V else 0)‖

/-- The `ℓ¹` error of the per-block flow at step `j`. -/
def shareErrL1 (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : ℕ → OFam .one d L N) (K : ℕ → OAct .one d L N) (κ : ℕ → Step2.Coup) (j : ℕ) : ℝ :=
  ∑ c' ∈ blockIdx (L := L) (N := N) (j + 1),
    ‖shareErr P C V W K κ j (blockSet (L := L) (N := N) (j + 1) c')‖

theorem sum_ite_mem_blockSet (a : Lam d L N) (j : ℕ) (c' : Fin d → ℕ) (x : ℂ) :
    ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
        (if a ∈ blockSet (L := L) (N := N) j b then x else 0) =
      if a ∈ blockSet (L := L) (N := N) (j + 1) c' then x else 0 := by
  classical
  simp only [mem_blockSet]
  rw [sum_ite_eq]
  congr 1
  apply propext
  constructor
  · intro h
    obtain ⟨y, hy, hya⟩ := mem_blocks.1 h
    rw [blk_succ, ← hya, ← blk_succ]
    exact mem_blockSet.1 hy
  · intro h
    exact mem_blocks.2 ⟨a, mem_blockSet.2 h, rfl⟩

theorem norm_sum_ite_mem_le (a : Lam d L N) (k : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    ∑ c' ∈ blockIdx (L := L) (N := N) k,
        (if a ∈ blockSet (L := L) (N := N) k c' then x else 0) ≤ x := by
  classical
  simp only [mem_blockSet]
  rw [sum_ite_eq]
  split_ifs <;> linarith

namespace MuChain

variable {P : ObsPts d L N} {C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ}
  {V W : ℕ → OFam .one d L N} {K : ℕ → OAct .one d L N} {κ : ℕ → Step2.Coup} {r : ℕ → ℂ}
  {n : ℕ} (H : MuChain P C V W K κ r n)
include H

/-- The total flow as the sum of the per-block flows:
`β_{j+1} = β_j(1 − 𝔫_j) − ∑_{B_+} err_j(B_+)`. -/
theorem betaTot_succ_eq {j : ℕ} (hj : j < n) :
    betaTot (L := L) (N := N) (j + 1) (V (j + 1)) =
      betaTot (L := L) (N := N) j (V j) * (1 - frakN C κ P.a j) -
        ∑ c' ∈ blockIdx (L := L) (N := N) (j + 1),
          shareErr P C V W K κ j (blockSet (L := L) (N := N) (j + 1) c') := by
  unfold betaTot
  rw [sum_congr rfl fun c' hc' => H.share_flow_exact hj hc', sum_sub_distrib, ← sum_mul]
  congr 2
  unfold betaX
  exact sum_blockIdx_succ j _

/-- **The `ℓ¹` step of the deviation**: `D_{j+1} ≤ |1 − 𝔫_j| D_j + 2 E_j`. -/
theorem shareDev_succ_le {j : ℕ} (hj : j < n) :
    shareDev P.a (j + 1) (V (j + 1)) ≤
      ‖1 - frakN C κ P.a j‖ * shareDev P.a j (V j) + 2 * shareErrL1 P C V W K κ j := by
  classical
  set β := betaTot (L := L) (N := N) j (V j)
  set a' := 1 - frakN C κ P.a j
  set e : (Fin d → ℕ) → ℂ := fun c' => shareErr P C V W K κ j (blockSet (L := L) (N := N) (j + 1) c')
  set δ : (Fin d → ℕ) → ℂ := fun b => mass1 (-1) (V j b : SA .one (Lam d L N)).a -
    (if P.a ∈ blockSet (L := L) (N := N) j b then β else 0)
  have hE0 : 0 ≤ shareErrL1 P C V W K κ j := sum_nonneg fun _ _ => norm_nonneg _
  have key : ∀ c' ∈ blockIdx (L := L) (N := N) (j + 1),
      mass1 (-1) (V (j + 1) c' : SA .one (Lam d L N)).a -
        (if P.a ∈ blockSet (L := L) (N := N) (j + 1) c' then
          betaTot (L := L) (N := N) (j + 1) (V (j + 1)) else 0) =
      a' * ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'), δ b - e c' +
        (if P.a ∈ blockSet (L := L) (N := N) (j + 1) c' then
          ∑ c'' ∈ blockIdx (L := L) (N := N) (j + 1), e c'' else 0) := by
    intro c' hc'
    rw [H.share_flow_exact hj hc', H.betaTot_succ_eq hj]
    have hX : betaX j (V j) (blockSet (L := L) (N := N) (j + 1) c') =
        ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'), δ b +
          (if P.a ∈ blockSet (L := L) (N := N) (j + 1) c' then β else 0) := by
      rw [betaX, ← sum_ite_mem_blockSet P.a j c' β, ← sum_add_distrib]
      exact sum_congr rfl fun b _ => by simp only [δ]; ring
    rw [hX]
    split_ifs <;> simp only [e, a'] <;> ring
  unfold shareDev
  rw [sum_congr rfl fun c' hc' => by rw [key c' hc']]
  have h1 : ∀ c' ∈ blockIdx (L := L) (N := N) (j + 1),
      ‖a' * ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'), δ b - e c' +
        (if P.a ∈ blockSet (L := L) (N := N) (j + 1) c' then
          ∑ c'' ∈ blockIdx (L := L) (N := N) (j + 1), e c'' else 0)‖ ≤
      ‖a'‖ * ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'), ‖δ b‖ + ‖e c'‖ +
        (if P.a ∈ blockSet (L := L) (N := N) (j + 1) c' then shareErrL1 P C V W K κ j else 0) := by
    intro c' _
    refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
      (add_le_add ?_ le_rfl)) ?_)
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    · split_ifs
      · exact norm_sum_le _ _
      · rw [norm_zero]
  refine (sum_le_sum h1).trans ?_
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum, sum_blockIdx_succ j (fun b => ‖δ b‖)]
  have h2 := norm_sum_ite_mem_le P.a (j + 1) (shareErrL1 P C V W K κ j) hE0
  have h3 : ∑ c' ∈ blockIdx (L := L) (N := N) (j + 1), ‖e c'‖ = shareErrL1 P C V W K κ j := rfl
  rw [h3]
  have h4 : ∑ b ∈ blockIdx (L := L) (N := N) j, ‖δ b‖ = shareDev P.a j (V j) := rfl
  rw [h4]
  linarith

end MuChain

/-! ### The concentration along the flow (real sequences) -/

/-- **Concentration of the shares**: if `D_0 = 0`, `D_{j+1} ≤ a_j D_j + 2E_j`,
`|β_{j+1}| ≥ a_j|β_j| − E_j`, `E_j ≤ δ_j a_j |β_j|` with `0 ≤ δ_j ≤ 1/2`, `a_j > 0`, and
`∑_{k<n} δ_k ≤ 1/6`, then `D_j ≤ 6 (∑_{k<j} δ_k) |β_j|` for `j ≤ n`. -/
theorem shareDev_seq_le {D A E δ a : ℕ → ℝ} {n : ℕ} (hD0 : D 0 = 0)
    (hD : ∀ j < n, D (j + 1) ≤ a j * D j + 2 * E j)
    (hA : ∀ j < n, a j * A j - E j ≤ A (j + 1))
    (hE : ∀ j < n, E j ≤ δ j * (a j * A j)) (hδ0 : ∀ j < n, 0 ≤ δ j) (hδ1 : ∀ j < n, δ j ≤ 1 / 2)
    (ha : ∀ j < n, 0 < a j) (hA0 : ∀ j ≤ n, 0 < A j)
    (hsum : ∑ k ∈ range n, δ k ≤ 1 / 6) :
    ∀ j ≤ n, D j ≤ 6 * (∑ k ∈ range j, δ k) * A j := by
  intro j
  induction j with
  | zero => intro _; simp [hD0]
  | succ j ih =>
    intro hj
    have hjn : j < n := by omega
    have ih' := ih hjn.le
    have hδj := hδ0 j hjn
    have hδj1 := hδ1 j hjn
    have haj := ha j hjn
    have hAj := hA0 j hjn.le
    have hAj1 := hA0 (j + 1) hj
    set S := ∑ k ∈ range j, δ k with hS
    have hS0 : 0 ≤ S := sum_nonneg fun k hk => hδ0 k (by have := mem_range.1 hk; omega)
    have hS1 : S + δ j ≤ 1 / 6 := by
      have : ∑ k ∈ range (j + 1), δ k ≤ ∑ k ∈ range n, δ k :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.2 hj) fun k hk _ =>
          hδ0 k (mem_range.1 hk)
      rw [sum_range_succ] at this; linarith
    have hEj := hE j hjn
    have hAs : a j * A j * (1 - δ j) ≤ A (j + 1) := by
      have := hA j hjn; nlinarith
    -- D_{j+1} ≤ a_j A_j (6 S + 2 δ_j)
    have hD1 : D (j + 1) ≤ a j * A j * (6 * S + 2 * δ j) := by
      have := hD j hjn
      have h2 : a j * D j ≤ a j * (6 * S * A j) := mul_le_mul_of_nonneg_left ih' haj.le
      nlinarith
    -- 6S + 2δ ≤ 6(S + δ)(1 - δ)
    have hkey : 6 * S + 2 * δ j ≤ 6 * (S + δ j) * (1 - δ j) := by nlinarith
    rw [sum_range_succ]
    have haA : 0 ≤ a j * A j := (mul_pos haj hAj).le
    calc D (j + 1) ≤ a j * A j * (6 * S + 2 * δ j) := hD1
      _ ≤ a j * A j * (6 * (S + δ j) * (1 - δ j)) := mul_le_mul_of_nonneg_left hkey haA
      _ = 6 * (S + δ j) * (a j * A j * (1 - δ j)) := by ring
      _ ≤ 6 * (S + δ j) * A (j + 1) :=
          mul_le_mul_of_nonneg_left hAs (by positivity)


/-- `|β_k| ≤ ∑_B |c_k(B)| ≤ |β_k| + D_k`. -/
theorem sum_norm_share_le (a : Lam d L N) (k : ℕ) (V : OFam .one d L N) :
    ∑ b ∈ blockIdx (L := L) (N := N) k, ‖mass1 (-1) (V b : SA .one (Lam d L N)).a‖ ≤
      ‖betaTot (L := L) (N := N) k V‖ + shareDev a k V := by
  classical
  have h : ∀ b ∈ blockIdx (L := L) (N := N) k, ‖mass1 (-1) (V b : SA .one (Lam d L N)).a‖ ≤
      ‖mass1 (-1) (V b : SA .one (Lam d L N)).a -
        (if a ∈ blockSet (L := L) (N := N) k b then betaTot (L := L) (N := N) k V else 0)‖ +
        (if a ∈ blockSet (L := L) (N := N) k b then ‖betaTot (L := L) (N := N) k V‖ else 0) := by
    intro b _
    refine (norm_le_norm_sub_add (mass1 (-1) (V b : SA .one (Lam d L N)).a)
      ((if a ∈ blockSet (L := L) (N := N) k b then
      betaTot (L := L) (N := N) k V else (0 : ℂ)))).trans (le_of_eq ?_)
    split_ifs <;> simp
  refine (sum_le_sum h).trans ?_
  rw [sum_add_distrib, add_comm]
  exact add_le_add (norm_sum_ite_mem_le a k _ (norm_nonneg (betaTot (L := L) (N := N) k V)))
    le_rfl

namespace MuChain

variable {P : ObsPts d L N} {C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ}
  {V W : ℕ → OFam .one d L N} {K : ℕ → OAct .one d L N} {κ : ℕ → Step2.Coup} {r : ℕ → ℂ}
  {n : ℕ} (H : MuChain P C V W K κ r n)
include H

theorem norm_betaTot_succ_ge {j : ℕ} (hj : j < n) :
    ‖1 - frakN C κ P.a j‖ * ‖betaTot (L := L) (N := N) j (V j)‖ - shareErrL1 P C V W K κ j ≤
      ‖betaTot (L := L) (N := N) (j + 1) (V (j + 1))‖ := by
  rw [H.betaTot_succ_eq hj]
  have h1 := norm_sub_norm_le (betaTot (L := L) (N := N) j (V j) * (1 - frakN C κ P.a j))
    (∑ c' ∈ blockIdx (L := L) (N := N) (j + 1),
      shareErr P C V W K κ j (blockSet (L := L) (N := N) (j + 1) c'))
  have h2 := norm_sum_le (blockIdx (L := L) (N := N) (j + 1))
    (fun c' => shareErr P C V W K κ j (blockSet (L := L) (N := N) (j + 1) c'))
  rw [norm_mul, mul_comm] at h1
  unfold shareErrL1
  linarith

/-- **Phase alignment of the shares** (sharp splitting, Case (1)): if initially all of the
coupling sits in the block of `a` (`D_0 = 0`), `|β_0| > 0`, and the `ℓ¹` error of the per-block
flow is relatively small, `E_j ≤ δ_j |1 − 𝔫_j| |β_j|` with `0 ≤ δ_j ≤ 1/2`, `|1 − 𝔫_j| > 0` and
`∑_{k<n} δ_k ≤ 1/6`, then for `j ≤ n`: `|β_j| > 0` and
`∑_B |c_j(B) − β_j 1_{a ∈ B}| ≤ 6 (∑_{k<j} δ_k) |β_j|`; hence
`∑_B |c_j(B)| ≤ (1 + 6 ∑_{k<j} δ_k) |β_j|` (`sum_norm_share_le`). -/
theorem phase_align (hD0 : shareDev P.a 0 (V 0) = 0) (δ : ℕ → ℝ)
    (hE : ∀ j < n, shareErrL1 P C V W K κ j ≤
      δ j * (‖1 - frakN C κ P.a j‖ * ‖betaTot (L := L) (N := N) j (V j)‖))
    (hδ0 : ∀ j < n, 0 ≤ δ j) (hδ1 : ∀ j < n, δ j ≤ 1 / 2)
    (ha : ∀ j < n, 0 < ‖1 - frakN C κ P.a j‖)
    (hβ0 : 0 < ‖betaTot (L := L) (N := N) 0 (V 0)‖) (hsum : ∑ k ∈ range n, δ k ≤ 1 / 6) :
    ∀ j ≤ n, 0 < ‖betaTot (L := L) (N := N) j (V j)‖ ∧
      shareDev P.a j (V j) ≤ 6 * (∑ k ∈ range j, δ k) * ‖betaTot (L := L) (N := N) j (V j)‖ := by
  have hpos : ∀ j ≤ n, 0 < ‖betaTot (L := L) (N := N) j (V j)‖ := by
    intro j
    induction j with
    | zero => intro _; exact hβ0
    | succ j ih =>
      intro hj
      have hjn : j < n := by omega
      have h1 := H.norm_betaTot_succ_ge hjn
      have h2 := hE j hjn
      have h3 := ih hjn.le
      have h4 := ha j hjn
      have h5 := hδ1 j hjn
      have h6 : 0 < ‖1 - frakN C κ P.a j‖ * ‖betaTot (L := L) (N := N) j (V j)‖ :=
        mul_pos h4 h3
      nlinarith
  intro j hj
  refine ⟨hpos j hj, ?_⟩
  exact shareDev_seq_le (D := fun k => shareDev P.a k (V k))
    (A := fun k => ‖betaTot (L := L) (N := N) k (V k)‖)
    (E := fun k => shareErrL1 P C V W K κ k) (a := fun k => ‖1 - frakN C κ P.a k‖) hD0
    (fun j hj => H.shareDev_succ_le hj) (fun j hj => H.norm_betaTot_succ_ge hj) hE hδ0 hδ1 ha
    hpos hsum j hj

end MuChain


/-! ### The pieces of the `ℓ¹` error -/

/-- **The activity term in `ℓ¹`**: `∑_B |m((𝔼θQ(B))_a)| ≤ ∑_{X ∈ 𝒮_j} |m(K(X)_a)|` (the pointed
`loc^a` distributes `m(K(X)_a)` over the blocks of `X` with weights `≥ 0` of sum `1`). -/
theorem sum_norm_EthQ_le (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
    (K : OAct c d L N) (hjN : j + 1 < N) (m : Alg d L N →ₗ[ℂ] ℂ) (hm : LocMass c P.a m) :
    ∑ b ∈ blockIdx (L := L) (N := N) j, ‖m (EthO C (Q2O P j K b) : SA c (Lam d L N)).a‖ ≤
      ∑ X ∈ smallSets (L := L) (N := N) j, ‖m (K X : SA c (Lam d L N)).a‖ := by
  classical
  have e1 : ∀ b, m (EthO C (Q2O P j K b) : SA c (Lam d L N)).a =
      ∑ X ∈ (smallSets (L := L) (N := N) j).filter (fun X => blockSet j b ⊆ X),
        m (locAp c P.a X (blockSet j b) (K X : SA c (Lam d L N)).a) := by
    intro b
    rw [EthO_a_eq]
    unfold Q2O
    rw [if_pos hjN, AddSubmonoidClass.coe_finsetSum, sum_a, map_sum, map_sum]
    exact sum_congr (by congr) fun X _ => hm.exp C X _ _
  have e2 : ∀ b, ‖m (EthO C (Q2O P j K b) : SA c (Lam d L N)).a‖ ≤
      ∑ X ∈ (smallSets (L := L) (N := N) j).filter (fun X => blockSet j b ⊆ X),
        ‖m (locAp c P.a X (blockSet j b) (K X : SA c (Lam d L N)).a)‖ := fun b => by
    rw [e1 b]; exact norm_sum_le _ _
  refine (sum_le_sum fun b _ => e2 b).trans (le_of_eq ?_)
  rw [sum_comm' (t' := smallSets (L := L) (N := N) j) (s' := fun X => blocks j X) ?_]
  · refine sum_congr rfl fun X hX => ?_
    have hs := mem_smallSets.1 hX
    exact sum_norm_locAp_blocks hm hs.1 hs.2.1.1 _
  · intro b X
    constructor
    · rintro ⟨hb, hX⟩
      obtain ⟨hXs, hbX⟩ := mem_filter.1 hX
      obtain ⟨x, hx⟩ := mem_blockIdx.1 hb
      exact ⟨mem_blocks.2 ⟨x, hbX hx, mem_blockSet.1 hx⟩, hXs⟩
    · rintro ⟨hb, hX⟩
      exact ⟨mem_blockIdx_of_mem_blocks hb,
        mem_filter.2 ⟨hX, blockSet_subset_of_mem_blocks (mem_smallSets.1 hX).1 hb⟩⟩

/-- **The `ℓ¹` error split into the activity, drift and product parts.** -/
theorem shareErrL1_le (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : ℕ → OFam .one d L N) (K : ℕ → OAct .one d L N) (κ : ℕ → Step2.Coup) (j : ℕ)
    (hjN : j + 1 < N) :
    shareErrL1 P C V W K κ j ≤
      ∑ X ∈ smallSets (L := L) (N := N) j, ‖mass1 (-1) (K j X : SA .one (Lam d L N)).a‖ +
      ∑ k ∈ range j, ‖tauC (C k) (C j) P.a‖ *
        ∑ c' ∈ blockIdx (L := L) (N := N) (j + 1),
          ‖betaX k (V k) (blockSet (L := L) (N := N) (j + 1) c') * (κ k).g -
            betaX j (V j) (blockSet (L := L) (N := N) (j + 1) c') * (κ j).g‖ +
      ∑ c' ∈ blockIdx (L := L) (N := N) (j + 1),
        ‖wTadX j (mass1L (-1)) (W j) (blockSet (L := L) (N := N) (j + 1) c') 0 +
          muProdIncX P C V W j (blockSet (L := L) (N := N) (j + 1) c')‖ := by
  unfold shareErrL1
  have h1 : ∀ c' ∈ blockIdx (L := L) (N := N) (j + 1),
      ‖shareErr P C V W K κ j (blockSet (L := L) (N := N) (j + 1) c')‖ ≤
        ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
          ‖mass1 (-1) (EthO (C j) (Q2O P j (K j) b) : SA .one (Lam d L N)).a‖ +
        ∑ k ∈ range j, ‖tauC (C k) (C j) P.a‖ *
          ‖betaX k (V k) (blockSet (L := L) (N := N) (j + 1) c') * (κ k).g -
            betaX j (V j) (blockSet (L := L) (N := N) (j + 1) c') * (κ j).g‖ +
        ‖wTadX j (mass1L (-1)) (W j) (blockSet (L := L) (N := N) (j + 1) c') 0 +
          muProdIncX P C V W j (blockSet (L := L) (N := N) (j + 1) c')‖ := by
    intro c' _
    rw [shareErr, add_assoc (muDriftX _ _ _ _ _ _)]
    refine (norm_add_le _ _).trans ?_
    rw [add_assoc]
    refine add_le_add (norm_sum_le _ _) ((norm_add_le _ _).trans (add_le_add ?_ le_rfl))
    refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun k _ => ?_))
    rw [norm_mul, mul_comm]
  refine (sum_le_sum h1).trans ?_
  rw [sum_add_distrib, sum_add_distrib, sum_blockIdx_succ j
    (fun b => ‖mass1 (-1) (EthO (C j) (Q2O P j (K j) b) : SA .one (Lam d L N)).a‖), sum_comm]
  refine add_le_add (add_le_add ?_ (le_of_eq (sum_congr rfl fun k _ => by rw [mul_sum]))) le_rfl
  exact sum_norm_EthQ_le P j (C j) (K j) hjN (mass1L (-1)) (locMass_one P.a)


/-- `‖f(k) − f(j)‖ ≤ ∑_{k ≤ i < j} ‖f(i+1) − f(i)‖`. -/
theorem norm_sub_le_sum_Ico {E : Type*} [SeminormedAddCommGroup E] (f : ℕ → E) {k j : ℕ}
    (hkj : k ≤ j) : ‖f k - f j‖ ≤ ∑ i ∈ Ico k j, ‖f (i + 1) - f i‖ := by
  induction j, hkj using Nat.le_induction with
  | base => simp
  | succ j hkj ih =>
    rw [sum_Ico_succ_top hkj]
    calc ‖f k - f (j + 1)‖ = ‖(f k - f j) - (f (j + 1) - f j)‖ := by congr 1; abel
      _ ≤ ‖f k - f j‖ + ‖f (j + 1) - f j‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add ih le_rfl

/-! ### Several scales at once, and the drift of a region -/

theorem blocks_blockSet_self {k : ℕ} {c' : Fin d → ℕ}
    (hne : (blockSet (L := L) (N := N) k c').Nonempty) :
    blocks k (blockSet (L := L) (N := N) k c') = {c'} := by
  ext b
  simp only [mem_singleton, mem_blocks, mem_blockSet]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact hx
  · rintro rfl
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, mem_blockSet.1 hx, mem_blockSet.1 hx⟩

/-- `∑_{B ∈ 𝓑_k(Y)} f(B) = ∑_{B' ∈ 𝓑_m(Y)} ∑_{B ∈ 𝓑_k(B')} f(B)` for an `m`-polymer `Y`, `k ≤ m`. -/
theorem sum_blocks_le {M : Type*} [AddCommMonoid M] (f : (Fin d → ℕ) → M) {k : ℕ} :
    ∀ m, k ≤ m → ∀ {Y : Finset (Lam d L N)}, IsPolymer m Y →
      ∑ b ∈ blocks k Y, f b =
        ∑ c' ∈ blocks m Y, ∑ b ∈ blocks k (blockSet (L := L) (N := N) m c'), f b := by
  intro m hkm
  induction m, hkm using Nat.le_induction with
  | base =>
    intro Y _
    refine sum_congr rfl fun c' hc' => ?_
    obtain ⟨x, hx, rfl⟩ := mem_blocks.1 hc'
    rw [blocks_blockSet_self ⟨x, mem_blockSet_blk k x⟩, sum_singleton]
  | succ m hkm ih =>
    intro Y hY
    rw [ih (IsPolymer.of_succ hY), ← Step2.sum_blocks_succ hY]
    refine sum_congr rfl fun c' _ => ?_
    exact (ih (IsPolymer.of_succ (isPolymer_blockSet (m + 1) c'))).symm

theorem sum_blockIdx_le {M : Type*} [AddCommMonoid M] (f : (Fin d → ℕ) → M) {k m : ℕ}
    (hkm : k ≤ m) :
    ∑ c' ∈ blockIdx (L := L) (N := N) m, ∑ b ∈ blocks k (blockSet (L := L) (N := N) m c'), f b =
      ∑ b ∈ blockIdx (L := L) (N := N) k, f b :=
  (sum_blocks_le f m hkm (isPolymer_univ m)).symm

/-- `∑_{B_+ ∈ 𝓑_m} |β_k(B_+)| ≤ ∑_{B ∈ 𝓑_k} |c_k(B)|` for `k ≤ m`. -/
theorem sum_norm_betaX_le {k m : ℕ} (hkm : k ≤ m) (V : OFam .one d L N) :
    ∑ c' ∈ blockIdx (L := L) (N := N) m, ‖betaX k V (blockSet (L := L) (N := N) m c')‖ ≤
      ∑ b ∈ blockIdx (L := L) (N := N) k, ‖mass1 (-1) (V b : SA .one (Lam d L N)).a‖ := by
  rw [← sum_blockIdx_le (fun b => ‖mass1 (-1) (V b : SA .one (Lam d L N)).a‖) hkm]
  exact sum_le_sum fun c' _ => norm_sum_le _ _

namespace MuChain

variable {P : ObsPts d L N} {C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ}
  {V W : ℕ → OFam .one d L N} {K : ℕ → OAct .one d L N} {κ : ℕ → Step2.Coup} {r : ℕ → ℂ}
  {n : ℕ} (H : MuChain P C V W K κ r n)
include H

/-- The flow of the coupling of a region `X` (an `(i+1)`-polymer). -/
theorem betaX_succ_eq {i : ℕ} (hi : i < n) {X : Finset (Lam d L N)} (hX : IsPolymer (i + 1) X) :
    betaX (i + 1) (V (i + 1)) X = betaX i (V i) X * (1 - frakN C κ P.a i) -
      ∑ c'' ∈ blocks (i + 1) X, shareErr P C V W K κ i (blockSet (L := L) (N := N) (i + 1) c'') := by
  unfold betaX
  rw [sum_congr rfl fun c'' hc'' =>
    H.share_flow_exact hi (mem_blockIdx_of_mem_blocks hc''), sum_sub_distrib, ← sum_mul]
  congr 2
  unfold betaX
  exact Step2.sum_blocks_succ hX _

/-- **The per-step drift of the regions in `ℓ¹`**: for `i < n`, `i + 1 ≤ m`,
`∑_{B_+ ∈ 𝓑_m} |β_{i+1}(B_+) g'_{i+1} − β_i(B_+) g'_i| ≤
|g'_{i+1} − g'_i| A_{i+1} + |g'_i| (|𝔫_i| A_i + E_i)`, `A_k = ∑_B |c_k(B)|`. -/
theorem drift_step_l1 {i m : ℕ} (hi : i < n) (him : i + 1 ≤ m) :
    ∑ c' ∈ blockIdx (L := L) (N := N) m,
        ‖betaX (i + 1) (V (i + 1)) (blockSet (L := L) (N := N) m c') * (κ (i + 1)).g -
          betaX i (V i) (blockSet (L := L) (N := N) m c') * (κ i).g‖ ≤
      ‖(κ (i + 1)).g - (κ i).g‖ *
          ∑ b ∈ blockIdx (L := L) (N := N) (i + 1), ‖mass1 (-1) (V (i + 1) b : SA .one (Lam d L N)).a‖ +
        ‖(κ i).g‖ * (‖frakN C κ P.a i‖ *
          ∑ b ∈ blockIdx (L := L) (N := N) i, ‖mass1 (-1) (V i b : SA .one (Lam d L N)).a‖ +
          shareErrL1 P C V W K κ i) := by
  have hpol : ∀ c' : Fin d → ℕ, IsPolymer (i + 1) (blockSet (L := L) (N := N) m c') := fun c' =>
    Step2.isPolymer_of_le (isPolymer_blockSet m c') (i + 1) him
  have h1 : ∀ c' ∈ blockIdx (L := L) (N := N) m,
      ‖betaX (i + 1) (V (i + 1)) (blockSet (L := L) (N := N) m c') * (κ (i + 1)).g -
          betaX i (V i) (blockSet (L := L) (N := N) m c') * (κ i).g‖ ≤
        ‖(κ (i + 1)).g - (κ i).g‖ * ‖betaX (i + 1) (V (i + 1)) (blockSet (L := L) (N := N) m c')‖ +
        ‖(κ i).g‖ * (‖frakN C κ P.a i‖ * ‖betaX i (V i) (blockSet (L := L) (N := N) m c')‖ +
          ∑ c'' ∈ blocks (i + 1) (blockSet (L := L) (N := N) m c'),
            ‖shareErr P C V W K κ i (blockSet (L := L) (N := N) (i + 1) c'')‖) := by
    intro c' _
    set X := blockSet (L := L) (N := N) m c'
    have e : betaX (i + 1) (V (i + 1)) X * (κ (i + 1)).g - betaX i (V i) X * (κ i).g =
        betaX (i + 1) (V (i + 1)) X * ((κ (i + 1)).g - (κ i).g) +
          (κ i).g * (-(betaX i (V i) X * frakN C κ P.a i) -
            ∑ c'' ∈ blocks (i + 1) X, shareErr P C V W K κ i (blockSet (L := L) (N := N) (i + 1) c'')) := by
      rw [H.betaX_succ_eq hi (hpol c')]; ring
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add (le_of_eq (by rw [norm_mul, mul_comm])) ?_)
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add ?_ (norm_sum_le _ _)))
      (norm_nonneg _)
    rw [norm_neg, norm_mul, mul_comm]
  refine (sum_le_sum h1).trans ?_
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_add_distrib, ← mul_sum]
  have h2 := sum_norm_betaX_le him (V (i + 1))
  have h3 := sum_norm_betaX_le (show i ≤ m by omega) (V i)
  have h4 : ∑ c' ∈ blockIdx (L := L) (N := N) m, ∑ c'' ∈ blocks (i + 1) (blockSet (L := L) (N := N) m c'),
      ‖shareErr P C V W K κ i (blockSet (L := L) (N := N) (i + 1) c'')‖ = shareErrL1 P C V W K κ i :=
    sum_blockIdx_le _ him
  rw [h4]
  have hg1 := norm_nonneg ((κ (i + 1)).g - (κ i).g)
  have hg2 := norm_nonneg (κ i).g
  have hn := norm_nonneg (frakN C κ P.a i)
  have := mul_le_mul_of_nonneg_left h2 hg1
  have := mul_le_mul_of_nonneg_left h3 hn
  have := mul_le_mul_of_nonneg_left (add_le_add_right this (shareErrL1 P C V W K κ i)) hg2
  nlinarith

/-- The drift of the regions between scales `k ≤ j` is bounded by the per-step drifts. -/
theorem drift_l1_le {k j m : ℕ} (hkj : k ≤ j) :
    ∑ c' ∈ blockIdx (L := L) (N := N) m,
        ‖betaX k (V k) (blockSet (L := L) (N := N) m c') * (κ k).g -
          betaX j (V j) (blockSet (L := L) (N := N) m c') * (κ j).g‖ ≤
      ∑ i ∈ Ico k j, ∑ c' ∈ blockIdx (L := L) (N := N) m,
        ‖betaX (i + 1) (V (i + 1)) (blockSet (L := L) (N := N) m c') * (κ (i + 1)).g -
          betaX i (V i) (blockSet (L := L) (N := N) m c') * (κ i).g‖ := by
  rw [sum_comm]
  exact sum_le_sum fun c' _ => norm_sub_le_sum_Ico
    (fun i => betaX i (V i) (blockSet (L := L) (N := N) m c') * (κ i).g) hkj

end MuChain

end

end Obs2
