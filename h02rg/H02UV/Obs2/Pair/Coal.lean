import Obs2.Map.Supp
import Obs.Norm

/-!
# Coalescence (Lemma `lem:coal`): the `ab` couplings vanish below `j_ab`

One step of the second-order map with sources (`Obs2.Map.Map`) at scale `j`, with covariance `C` of
range `L^{j+1}/2` (`C(x,y) = 0` for `|x - y|_∞ ≥ L^{j+1}/2`, property `D2` of the decomposition)
and `|a - b|_∞ ≥ L^{j+1}/2` (i.e. `j < j_ab`, `C(a,b) = 0`). The mechanism is the finite range:

* every observable `σ_a` component is supported near `a` (`σ_i`-freeness `noX`, `Obs2.Map.Supp`):
  `V(B)`, `𝒲(B)` and `K(X)` have no `σ_a` if `B`, `X` are at distance `≥ L^j` from `a`; the
  localised components are supported at the point (`V(B)_a ∈ 𝒩({a})`). With the pointed `loc^a`
  of `Obs2.Loc.Loc` (localisation at `a` also for `a ∉ X`), `V(B)_a` may be nonzero for blocks
  `B ∌ a` near `a`; the radius `L^j` is propagated through the step since every small set
  containing a block of a `(j+1)`-block at distance `≥ L^{j+1}` is at distance `≥ L^j`
  (`CoalHyp.clean_small`, `L ≥ 2^{d+3}`);
* the only new `σ_aσ_b` terms of the step are `F_C(V'_{B,a}, V'_{B',b})`, which vanish since
  `C(a,b) = 0`; products `(σ_a ⋯)(σ_b ⋯)` appear only in objects close to both points, and no
  block or small set is close to both points below the coalescence scale.

## Results
* `CoalHyp`: the hypotheses at scale `j`; `CoalHyp.Vnext_ab`, `Vnext_pt`, `Vnext_noX`,
  `Wnext_noX`, `Wnext_ab`, `Kplus_noX`, `Kplus_ab`, `uObsTot_ab`: the conclusions at scale `j+1`;
* `ObsCoalInv`, `obsStep_coalInv`: the invariant along the observable flow of `Obs2.Flow.Hist`;
* **`obsHist_coal`** (Lemma `lem:coal`): for `L ≥ 2^5` and `j ≤ j_ab = coal L a b`, the `ab`
  components of `V^{obs}_j(B)` and of the accumulated `u^{obs}_j` vanish, i.e.
  `q_j = η_j = r_j = χ_j = 0`, provided the step covariances have range `L^{k+1}/2`;
  `obsHist_coal_valid`: the range hypothesis from `ValidAt` (Step2's validity of the parameters).

The text states `j < j_ab`; the proof gives `j ≤ j_ab`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 LocObs FRD

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

/-- `X` is at sup-distance `≥ r` from `p`. -/
def FarS (r : ℕ) (p : Lam d L N) (X : Finset (Lam d L N)) : Prop := ∀ x ∈ X, r ≤ supNorm (x - p)

/-- The submodule of elements with vanishing `ab` component. -/
def abZ (c : Obs.Case) (Λ : Type*) [DecidableEq Λ] : Submodule ℂ (OE c Λ) where
  carrier := {F | (F : SA c Λ).ab = 0}
  zero_mem' := rfl
  add_mem' {F G} hF hG := by
    show (F : SA c Λ).ab + (G : SA c Λ).ab = 0
    rw [show (F : SA c Λ).ab = 0 from hF, show (G : SA c Λ).ab = 0 from hG, add_zero]
  smul_mem' r F hF := by
    show r • (F : SA c Λ).ab = 0
    rw [show (F : SA c Λ).ab = 0 from hF, smul_zero]

theorem abZ_of_noX {Λ : Type*} [DecidableEq Λ] {i : Bool} {F : OE c Λ} (h : F ∈ noX c Λ i) :
    F ∈ abZ c Λ := noX_ab h

theorem EthO_comp (C : Matrix (Lam d L N) (Lam d L N) ℂ) (F : OE c (Lam d L N)) :
    (EthO C F : SA c (Lam d L N)).e = expLC C (F : SA c (Lam d L N)).e ∧
      (∀ i, cmp i (EthO C F : SA c (Lam d L N)) = expLC C (cmp i (F : SA c (Lam d L N)))) ∧
      (EthO C F : SA c (Lam d L N)).ab = expLC C (F : SA c (Lam d L N)).ab := by
  rw [EthO_eq_expO]
  exact ⟨rfl, fun i => by cases i <;> rfl, rfl⟩

theorem cmp_mem_NX_sub {Λ : Type*} [DecidableEq Λ] {i : Bool} {S : Set Λ} {F G : SA c Λ}
    (hF : cmp i F ∈ NX S) (hG : cmp i G ∈ NX S) : cmp i (F - G) ∈ NX S := by
  rw [cmp_sub]; exact sub_mem hF hG

/-! ### Geometry -/

section Geom

theorem two_pow_le (hL : 2 ^ (d + 3) ≤ L) (j : ℕ) : 2 ^ (d + 1) * L ^ j ≤ L ^ (j + 1) := by
  have h : 2 ^ (d + 1) ≤ L := le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hL
  calc 2 ^ (d + 1) * L ^ j ≤ L * L ^ j := Nat.mul_le_mul_right _ h
    _ = L ^ (j + 1) := by ring

theorem not_mem_of_farS {r : ℕ} (hr : 0 < r) {p : Lam d L N} {X : Finset (Lam d L N)}
    (h : FarS r p X) : p ∉ X := fun hp => by
  have := h p hp; rw [sub_self, supNorm_zero] at this; omega

theorem farS_mono {r r' : ℕ} (hr : r' ≤ r) {p : Lam d L N} {X Y : Finset (Lam d L N)}
    (h : FarS r p X) (hYX : Y ⊆ X) : FarS r' p Y := fun y hy => hr.trans (h y (hYX hy))

/-- The small set neighbourhood of a block of a far polymer is at distance `≥ L^{j+1}/2`. -/
theorem nbhd_far (hL : 2 ^ (d + 3) ≤ L) {j : ℕ} {p : Lam d L N} {U : Finset (Lam d L N)}
    (hU : FarS (L ^ (j + 1)) p U) {b : Fin d → ℕ} (hbU : blockSet (L := L) (N := N) j b ⊆ U)
    {x : Lam d L N} (hx : x ∈ nbhd j (blockSet (L := L) (N := N) j b)) :
    (L : ℝ) ^ (j + 1) / 2 ≤ supNorm (x - p) := by
  obtain ⟨y, hy, hxy⟩ := exists_near_of_mem_nbhd hx
  have h1 := hU y (hbU hy)
  have e : y - p = (y - x) + (x - p) := by abel
  have h2 := supNorm_add_le (y - x) (x - p)
  rw [← e, supNorm_sub_comm y x] at h2
  have h3 := two_pow_le hL j
  have h4 : L ^ (j + 1) ≤ 2 * supNorm (x - p) := by
    have : 2 ^ (d + 1) * L ^ j = 2 * (2 ^ d * L ^ j) := by ring
    omega
  have h5 : ((L ^ (j + 1) : ℕ) : ℝ) ≤ ((2 * supNorm (x - p) : ℕ) : ℝ) := Nat.cast_le.2 h4
  push_cast at h5
  linarith

/-- A small set at scale `k` is far from one of the points if `|a - b|_∞ ≥ L^{k+1}/2`. -/
theorem small_far (hL : 2 ^ (d + 3) ≤ L) {k : ℕ} {a b : Lam d L N} {U : Finset (Lam d L N)}
    (hU : IsSmall k U) (hab : (L : ℝ) ^ (k + 1) / 2 ≤ supNorm (a - b)) :
    FarS (L ^ k) a U ∨ FarS (L ^ k) b U := by
  by_contra hc
  simp only [not_or, FarS, not_forall, not_le, exists_prop] at hc
  obtain ⟨⟨x, hx, hxa⟩, ⟨y, hy, hyb⟩⟩ := hc
  have hxy := supNorm_le_of_isSmall hU hx hy
  have e : a - b = (a - x) + ((x - y) + (y - b)) := by abel
  have h1 := supNorm_add_le (a - x) ((x - y) + (y - b))
  have h2 := supNorm_add_le (x - y) (y - b)
  rw [← e] at h1
  rw [supNorm_sub_comm a x] at h1
  have h3 : supNorm (a - b) < (2 + 2 ^ d) * L ^ k := by
    have : (2 + 2 ^ d) * L ^ k = L ^ k + 2 ^ d * L ^ k + L ^ k := by ring
    omega
  have h4 : L ^ (k + 1) ≤ 2 * supNorm (a - b) := by
    have h5 : ((L ^ (k + 1) : ℕ) : ℝ) ≤ ((2 * supNorm (a - b) : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast h5
  have h6 : 2 * ((2 + 2 ^ d) * L ^ k) ≤ L ^ (k + 1) := by
    have h : 2 * (2 + 2 ^ d) ≤ L := by
      refine le_trans ?_ hL
      have : 2 ^ (d + 3) = 8 * 2 ^ d := by ring
      have : 1 ≤ 2 ^ d := Nat.one_le_two_pow
      omega
    calc 2 * ((2 + 2 ^ d) * L ^ k) = (2 * (2 + 2 ^ d)) * L ^ k := by ring
      _ ≤ L * L ^ k := Nat.mul_le_mul_right _ h
      _ = L ^ (k + 1) := by ring
  omega

/-- A `k`-block is far from one of the points if `|a - b|_∞ ≥ L^{k+1}/2`. -/
theorem block_far (hL : 2 ^ (d + 3) ≤ L) {k : ℕ} {a b : Lam d L N} (c' : Fin d → ℕ)
    (hab : (L : ℝ) ^ (k + 1) / 2 ≤ supNorm (a - b)) :
    FarS (L ^ k) a (blockSet (L := L) (N := N) k c') ∨
      FarS (L ^ k) b (blockSet (L := L) (N := N) k c') := by
  by_cases hne : (blockSet (L := L) (N := N) k c').Nonempty
  · obtain ⟨x, hx⟩ := hne
    have hx' : blockSet (L := L) (N := N) k c' = blockSet k (blk k x) := by
      rw [(mem_blockSet.1 hx).symm]
    rw [hx']
    exact small_far hL (isSmall_blockSet k x) (by rwa [← hx'] at *)
  · left
    intro x hx; exact absurd ⟨x, hx⟩ hne

end Geom

/-! ### The hypotheses at scale `j` -/

variable (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
  (V W : OFam c d L N) (K : OAct c d L N)

/-- The hypotheses of one step below the coalescence scale. -/
structure CoalHyp : Prop where
  hL : 2 ^ (d + 3) ≤ L
  hC : ∀ x y, (L : ℝ) ^ (j + 1) / 2 ≤ supNorm (x - y) → C x y = 0
  hab : (L : ℝ) ^ (j + 1) / 2 ≤ supNorm (P.a - P.b)
  hVe : ∀ b, (V b : SA c (Lam d L N)).e ∈
    NX (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N))
  hVpt : ∀ i b, cmp i (V b : SA c (Lam d L N)) ∈ NX ({P.pt i} : Set (Lam d L N))
  hVab : ∀ b, (V b : SA c (Lam d L N)).ab = 0
  hVno : ∀ i b, FarS (L ^ j) (P.pt i) (blockSet (L := L) (N := N) j b) →
    V b ∈ noX c (Lam d L N) i
  hWab : ∀ b, (W b : SA c (Lam d L N)).ab = 0
  hWno : ∀ i b, FarS (L ^ j) (P.pt i) (blockSet (L := L) (N := N) j b) →
    W b ∈ noX c (Lam d L N) i
  hKab : ∀ X, IsSmall j X → (K X : SA c (Lam d L N)).ab = 0
  hKno : ∀ i X, IsConn j X → FarS (L ^ j) (P.pt i) X → K X ∈ noX c (Lam d L N) i

/-- The block `b` is clean for `σ_i`: it is nonempty and its `(j+1)`-block `B_+` is at distance
`≥ L^{j+1}` from `p_i`. Then `B` is far from `p_i`, `C` vanishes between `B^□` and `p_i`, the small
sets containing `B` are at distance `≥ L^j` (`clean_block`, `clean_nbhd`, `clean_small`), and so
are the blocks of `B_+` (`clean_sib`). -/
def Clean (i : Bool) (b : Fin d → ℕ) : Prop :=
  (blockSet (L := L) (N := N) j b).Nonempty ∧
    FarS (L ^ (j + 1)) (P.pt i) (Step2.Bp (L := L) (N := N) j b)

namespace CoalHyp

variable {P j C V W K} (H : CoalHyp P j C V W K)
include H

theorem C_far {x y : Lam d L N} (h : (L : ℝ) ^ (j + 1) / 2 ≤ supNorm (x - y)) :
    C x y = 0 ∧ C y x = 0 :=
  ⟨H.hC x y h, H.hC y x (by rwa [supNorm_sub_comm])⟩

theorem pt_ne (i : Bool) : P.pt (!i) ≠ P.pt i := by
  intro h
  have hL0 : (0 : ℝ) < (L : ℝ) ^ (j + 1) / 2 := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have := H.hab
  cases i
  · simp only [Bool.not_false, ObsPts.pt_true, ObsPts.pt_false] at h
    rw [h, sub_self, supNorm_zero] at this; push_cast at this; linarith
  · simp only [Bool.not_true, ObsPts.pt_true, ObsPts.pt_false] at h
    rw [h, sub_self, supNorm_zero] at this; push_cast at this; linarith

theorem pt_far (i : Bool) : (L : ℝ) ^ (j + 1) / 2 ≤ supNorm (P.pt (!i) - P.pt i) := by
  cases i
  · simp only [Bool.not_false, ObsPts.pt_true, ObsPts.pt_false]; exact H.hab
  · simp only [Bool.not_true, ObsPts.pt_true, ObsPts.pt_false]
    rw [supNorm_sub_comm]; exact H.hab

/-! #### `V'_B` -/

theorem Vpr_e (b : Fin d → ℕ) : (VprO C V b : SA c (Lam d L N)).e ∈
    NX (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N)) := by
  rw [VprO, (EthO_comp C (V b)).1]; exact expLC_mem_NX _ (H.hVe b)

theorem Vpr_pt (i : Bool) (b : Fin d → ℕ) :
    cmp i (VprO C V b : SA c (Lam d L N)) ∈ NX ({P.pt i} : Set (Lam d L N)) := by
  rw [VprO, (EthO_comp C (V b)).2.1]; exact expLC_mem_NX _ (H.hVpt i b)

theorem Vpr_ab (b : Fin d → ℕ) : (VprO C V b : SA c (Lam d L N)).ab = 0 := by
  rw [VprO, (EthO_comp C (V b)).2.2, H.hVab b, map_zero]

theorem Vpr_noX {i : Bool} {b : Fin d → ℕ}
    (hb : FarS (L ^ j) (P.pt i) (blockSet (L := L) (N := N) j b)) :
    VprO C V b ∈ noX c (Lam d L N) i :=
  EthO_mem_noX C (H.hVno i b hb)

/-! #### Clean blocks -/

omit H in
theorem farS_succ {i : Bool} {X : Finset (Lam d L N)} (h : FarS (L ^ (j + 1)) (P.pt i) X) :
    FarS (L ^ j) (P.pt i) X :=
  farS_mono (Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (Nat.le_succ j)) h subset_rfl

omit H in
theorem clean_block {i : Bool} {b : Fin d → ℕ} (hb : Clean P j i b) :
    FarS (L ^ (j + 1)) (P.pt i) (blockSet (L := L) (N := N) j b) :=
  farS_mono le_rfl hb.2 (subset_clo j _)

theorem clean_nbhd {i : Bool} {b : Fin d → ℕ} (hb : Clean P j i b) :
    ∀ x ∈ nbhd j (blockSet (L := L) (N := N) j b), (L : ℝ) ^ (j + 1) / 2 ≤ supNorm (x - P.pt i) :=
  fun _ hx => nbhd_far H.hL hb.2 (subset_clo j _) hx

theorem clean_V {i : Bool} {b : Fin d → ℕ} (hb : Clean P j i b) : V b ∈ noX c (Lam d L N) i :=
  H.hVno i b (farS_succ (clean_block hb))

theorem clean_W {i : Bool} {b : Fin d → ℕ} (hb : Clean P j i b) : W b ∈ noX c (Lam d L N) i :=
  H.hWno i b (farS_succ (clean_block hb))

/-- The small sets containing a clean block are at distance `≥ L^j`. -/
theorem clean_small {i : Bool} {b : Fin d → ℕ} (hb : Clean P j i b) {X : Finset (Lam d L N)}
    (hX : IsSmall j X) (hbX : blockSet (L := L) (N := N) j b ⊆ X) : FarS (L ^ j) (P.pt i) X := by
  intro x hx
  obtain ⟨y, hy⟩ := hb.1
  have h1 := clean_block hb y hy
  have h2 := supNorm_le_of_isSmall hX (hbX hy) hx
  have e : y - P.pt i = (y - x) + (x - P.pt i) := by abel
  have h3 := supNorm_add_le (y - x) (x - P.pt i)
  rw [← e] at h3
  have h4 := two_pow_le H.hL j
  have h5 : 2 ^ (d + 1) * L ^ j = 2 * (2 ^ d * L ^ j) := by ring
  have h6 : L ^ j ≤ 2 ^ d * L ^ j := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos d)
  omega

omit H in
/-- The blocks of the `(j+1)`-block of a clean block are clean. -/
theorem clean_sib {i : Bool} {b b'' : Fin d → ℕ} (hb : Clean P j i b)
    (h : b'' ∈ blocks j (Step2.Bp (L := L) (N := N) j b)) : Clean P j i b'' := by
  obtain ⟨x, -, hxb⟩ := mem_blocks.1 h
  exact ⟨⟨x, mem_blockSet.2 hxb⟩, farS_mono le_rfl hb.2 (Step2.BH.Bp_sub h)⟩

/-! #### Pairs `F_C(V'_B, V'_{B'})` -/

/-- **The new `σ_aσ_b` terms vanish** (`C(a,b) = 0`). -/
theorem FCpair_ab (b b' : Fin d → ℕ) :
    (FCO C (VprO C V b) (VprO C V b') : SA c (Lam d L N)).ab = 0 := by
  have hdis : Disjoint ({P.b} : Set (Lam d L N)) {P.a} := by
    rw [Set.disjoint_singleton]; exact H.pt_ne true
  have hCab : ∀ x ∈ ({P.b} : Set (Lam d L N)), ∀ y ∈ ({P.a} : Set (Lam d L N)),
      C x y = 0 ∧ C y x = 0 := by
    intro x hx y hy
    rw [Set.mem_singleton_iff.1 hx, Set.mem_singleton_iff.1 hy]
    exact H.C_far (by rw [supNorm_sub_comm]; exact H.hab)
  have hτa : c.tau (VprO C V b : SA c (Lam d L N)).a ∈ NX ({P.a} : Set (Lam d L N)) := by
    rw [Case.tau_of_par c (VprO C V b).par_a]
    exact Subalgebra.smul_mem _ (H.Vpr_pt true b) _
  have hτb : c.tau (VprO C V b : SA c (Lam d L N)).b ∈ NX ({P.b} : Set (Lam d L N)) := by
    rw [Case.tau_of_par c (VprO C V b).par_b]
    exact Subalgebra.smul_mem _ (H.Vpr_pt false b) _
  have hb' : (VprO C V b' : SA c (Lam d L N)).b ∈ NX ({P.b} : Set (Lam d L N)) :=
    H.Vpr_pt false b'
  have ha' : (VprO C V b' : SA c (Lam d L N)).a ∈ NX ({P.a} : Set (Lam d L N)) :=
    H.Vpr_pt true b'
  rw [FCO_ab, H.Vpr_ab b, H.Vpr_ab b', FC_zero_right, FC_zero_left, zero_add, add_zero,
    FC_eq_zero_of_disjoint C hdis.symm (fun x hx y hy => (hCab y hy x hx).symm) hτa hb',
    FC_eq_zero_of_disjoint C hdis hCab hτb ha', smul_zero, add_zero]

/-- The interaction of a clean block with any block has no `σ_i`. -/
theorem FCpair_noX {i : Bool} {b : Fin d → ℕ} (hb : Clean P j i b) (b' : Fin d → ℕ) :
    FCO C (VprO C V b) (VprO C V b') ∈ noX c (Lam d L N) i := by
  have h1 := farS_succ (clean_block hb)
  have h2 := H.clean_nbhd hb
  have hL0 : (0 : ℝ) < (L : ℝ) ^ (j + 1) / 2 := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  refine FCO_mem_noX_far C (H.Vpr_noX h1) (H.Vpr_ab b')
    (S := (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N)))
    (S' := {P.pt (!i)}) (T := {P.pt i}) ?_ ?_ ?_ ?_ (H.Vpr_e b) (H.Vpr_pt (!i) b)
    (H.Vpr_pt i b')
  · rw [Set.disjoint_singleton_right]
    intro hp
    have := h2 _ hp
    rw [sub_self, supNorm_zero] at this; push_cast at this; linarith
  · intro x hx y hy
    rw [Set.mem_singleton_iff.1 hy]
    exact H.C_far (h2 x hx)
  · rw [Set.disjoint_singleton]; exact H.pt_ne i
  · intro x hx y hy
    rw [Set.mem_singleton_iff.1 hx, Set.mem_singleton_iff.1 hy]
    exact H.C_far (H.pt_far i)

theorem FCL_ab (b : Fin d → ℕ) :
    FCO C (VprO C V b) (VprLO j C V) ∈ abZ c (Lam d L N) := by
  rw [VprLO, FCO_sum_right]
  exact Submodule.sum_mem _ fun b' _ => H.FCpair_ab b b'

/-! #### `S(B)` and `Loc S` -/

theorem VprL_ab : (VprLO j C V : SA c (Lam d L N)).ab = 0 := by
  rw [VprLO, AddSubmonoidClass.coe_finsetSum, sum_ab]
  exact sum_eq_zero fun b _ => H.Vpr_ab b

theorem SCor_ab (b : Fin d → ℕ) : SCorO j C V b ∈ abZ c (Lam d L N) := by
  show (SCorO j C V b : SA c (Lam d L N)).ab = 0
  rw [SCorO_ab, H.Vpr_ab, H.VprL_ab, FC_zero_left, FC_zero_right, sub_zero, smul_zero]

theorem SF_ab (b : Fin d → ℕ) : SFO j C V b ∈ abZ c (Lam d L N) :=
  add_mem (Submodule.smul_mem _ _ (H.FCL_ab b)) (H.SCor_ab b)

theorem SF_noX {i : Bool} {b : Fin d → ℕ} (hb : Clean P j i b) :
    SFO j C V b ∈ noX c (Lam d L N) i := by
  refine mem_noX.2 ⟨?_, H.SF_ab b⟩
  rw [SFO_cmp, noX_cmp (H.Vpr_noX (farS_succ (clean_block hb))), FC_zero_left]

theorem Sb_ab (b : Fin d → ℕ) : SbO j C V W b ∈ abZ c (Lam d L N) := by
  refine add_mem (H.SF_ab b) ?_
  show (EthO C (W b) : SA c (Lam d L N)).ab = 0
  rw [(EthO_comp C (W b)).2.2, H.hWab b, map_zero]

theorem Sb_noX {i : Bool} {b : Fin d → ℕ} (hb : Clean P j i b) :
    SbO j C V W b ∈ noX c (Lam d L N) i :=
  add_mem (H.SF_noX hb) (EthO_mem_noX C (H.clean_W hb))

theorem SX_ab (X : Finset (Lam d L N)) : SXO j C V W X ∈ abZ c (Lam d L N) :=
  Submodule.sum_mem _ fun b _ => H.Sb_ab b

theorem LS_ab (b : Fin d → ℕ) : LSO P j C V W b ∈ abZ c (Lam d L N) :=
  LocO2_ab_eq_zero P _ _ (H.SX_ab _)

theorem LS_noX {i : Bool} {b : Fin d → ℕ} (hb : Clean P j i b) :
    LSO P j C V W b ∈ noX c (Lam d L N) i :=
  LocO2_mem_noX P _ _ (Subalgebra.sum_mem _ fun _ hb'' => H.Sb_noX (clean_sib hb hb''))

theorem LS_pt (i : Bool) (b : Fin d → ℕ) :
    cmp i (LSO P j C V W b : SA c (Lam d L N)) ∈ NX ({P.pt i} : Set (Lam d L N)) :=
  cmp_LocO2_mem P _ _ i _

/-! #### `Q(B)` and `J(B, X)` -/

theorem Q_ab (b : Fin d → ℕ) : Q2O P j K b ∈ abZ c (Lam d L N) := by
  unfold Q2O; split_ifs
  · exact Submodule.sum_mem _ fun X hX =>
      LocO2_ab_eq_zero P _ _ (H.hKab X (mem_smallSets.1 (mem_filter.1 hX).1))
  · exact zero_mem _

theorem K_noX_of_clean {i : Bool} {b : Fin d → ℕ} (hb : Clean P j i b) {X : Finset (Lam d L N)}
    (hX : IsSmall j X) (hbX : blockSet (L := L) (N := N) j b ⊆ X) : K X ∈ noX c (Lam d L N) i :=
  H.hKno i X ⟨hX.1, hX.2.1⟩ (H.clean_small hb hX hbX)

theorem Q_noX {i : Bool} {b : Fin d → ℕ} (hb : Clean P j i b) :
    Q2O P j K b ∈ noX c (Lam d L N) i := by
  unfold Q2O; split_ifs
  · exact Subalgebra.sum_mem _ fun X hX => LocO2_mem_noX P _ _
      (H.K_noX_of_clean hb (mem_smallSets.1 (mem_filter.1 hX).1) (mem_filter.1 hX).2)
  · exact zero_mem _

theorem Q_pt (i : Bool) (b : Fin d → ℕ) :
    cmp i (Q2O P j K b : SA c (Lam d L N)) ∈ NX ({P.pt i} : Set (Lam d L N)) := by
  unfold Q2O; split_ifs
  · rw [AddSubmonoidClass.coe_finsetSum, cmp_sum]
    exact Subalgebra.sum_mem _ fun X _ => cmp_LocO2_mem P _ _ i _
  · rw [ZeroMemClass.coe_zero, cmp_zero]; exact zero_mem _

theorem J_noX {i : Bool} {b : Fin d → ℕ} (hb : Clean P j i b)
    (X : Finset (Lam d L N)) : J2O P j K b X ∈ noX c (Lam d L N) i := by
  unfold J2O; split_ifs with h1 h2
  · exact neg_mem (Subalgebra.sum_mem _ fun Y hY => LocO2_mem_noX P _ _
      (H.K_noX_of_clean hb (mem_smallSets.1 (mem_filter.1 hY).1) (mem_filter.1 hY).2.1))
  · exact LocO2_mem_noX P _ _ (H.K_noX_of_clean hb h1.2.1 h1.2.2)
  · exact zero_mem _

/-! #### `(u + V)_{j+1}(B)`, `V_{j+1}(B)`, `𝒲_{j+1}(B)` and the block factors -/

theorem uVp_ab (b : Fin d → ℕ) : uVpO P j C V W K b ∈ abZ c (Lam d L N) := by
  refine sub_mem (sub_mem (H.Vpr_ab b) ?_) (H.LS_ab b)
  show (EthO C (Q2O P j K b) : SA c (Lam d L N)).ab = 0
  rw [(EthO_comp C _).2.2, show (Q2O P j K b : SA c (Lam d L N)).ab = 0 from H.Q_ab b, map_zero]

theorem uVp_noX {i : Bool} {b : Fin d → ℕ} (hb : Clean P j i b) :
    uVpO P j C V W K b ∈ noX c (Lam d L N) i :=
  sub_mem (sub_mem (H.Vpr_noX (farS_succ (clean_block hb)))
    (EthO_mem_noX C (H.Q_noX hb))) (H.LS_noX hb)

theorem uVp_pt (i : Bool) (b : Fin d → ℕ) :
    cmp i (uVpO P j C V W K b : SA c (Lam d L N)) ∈ NX ({P.pt i} : Set (Lam d L N)) := by
  refine cmp_mem_NX_sub (cmp_mem_NX_sub (H.Vpr_pt i b) ?_) (H.LS_pt i b)
  rw [(EthO_comp C _).2.1]; exact expLC_mem_NX _ (H.Q_pt i b)

theorem upO_ab (b : Fin d → ℕ) : upO P j C V W K b ∈ abZ c (Lam d L N) := by
  show (πobs (epsO (uVpO P j C V W K b)) : SA c (Lam d L N)).ab = 0
  rw [ab_πobs, coe_epsO, epsS_ab,
    show (uVpO P j C V W K b : SA c (Lam d L N)).ab = 0 from H.uVp_ab b, map_zero, map_zero]

theorem upO_noX {i : Bool} {b : Fin d → ℕ} (hb : Clean P j i b) :
    upO P j C V W K b ∈ noX c (Lam d L N) i :=
  πobs_mem_noX (epsO_mem_noX (H.uVp_noX hb))

theorem upO_pt (i : Bool) (b : Fin d → ℕ) :
    cmp i (upO P j C V W K b : SA c (Lam d L N)) ∈ NX ({P.pt i} : Set (Lam d L N)) := by
  have : cmp i (upO P j C V W K b : SA c (Lam d L N)) =
      algebraMap ℂ _ (ε (cmp i (uVpO P j C V W K b : SA c (Lam d L N)))) := by
    show cmp i (πobs (epsO (uVpO P j C V W K b)) : SA c (Lam d L N)) = _
    rw [cmp_πobs, coe_epsO]; cases i <;> rfl
  rw [this]; exact Subalgebra.algebraMap_mem _ _

theorem Vp_ab (b : Fin d → ℕ) : VpO P j C V W K b ∈ abZ c (Lam d L N) := by
  refine sub_mem (sub_mem (H.uVp_ab b) ?_) (H.upO_ab b)
  show ((algebraMap ℂ (OE c (Lam d L N)) (upB P j C V W K b) : OE c (Lam d L N)) :
    SA c (Lam d L N)).ab = 0
  rw [Subalgebra.coe_algebraMap]; exact algebraMap_ab _

theorem Vp_noX {i : Bool} {b : Fin d → ℕ} (hb : Clean P j i b) :
    VpO P j C V W K b ∈ noX c (Lam d L N) i :=
  sub_mem (sub_mem (H.uVp_noX hb) (Subalgebra.algebraMap_mem _ _)) (H.upO_noX hb)

theorem Vp_pt (i : Bool) (b : Fin d → ℕ) :
    cmp i (VpO P j C V W K b : SA c (Lam d L N)) ∈ NX ({P.pt i} : Set (Lam d L N)) := by
  refine cmp_mem_NX_sub (cmp_mem_NX_sub (H.uVp_pt i b) ?_) (H.upO_pt i b)
  have : cmp i ((algebraMap ℂ (OE c (Lam d L N)) (upB P j C V W K b) : OE c (Lam d L N)) :
      SA c (Lam d L N)) = 0 := cmp_algebraMap i _
  rw [this]; exact zero_mem _

theorem Wp_noX {i : Bool} {b : Fin d → ℕ} (hb : Clean P j i b) :
    WpO P j C V W b ∈ noX c (Lam d L N) i :=
  sub_mem (H.Sb_noX hb) (H.LS_noX hb)

theorem Ib_noX {i : Bool} {b : Fin d → ℕ} (hb : Clean P j i b) :
    IbO V W b ∈ noX c (Lam d L N) i :=
  mul_mem (oexp_mem (neg_mem (H.clean_V hb))) (add_mem (one_mem _) (H.clean_W hb))

theorem Gp_noX {i : Bool} {b : Fin d → ℕ} (hb : Clean P j i b) :
    GpO P j C V W K b ∈ noX c (Lam d L N) i :=
  mul_mem (oexp_mem (neg_mem (H.Vp_noX hb))) (add_mem (one_mem _) (H.Wp_noX hb))

theorem Ip_noX {i : Bool} {b : Fin d → ℕ} (hb : Clean P j i b) :
    IpO P j C V W K b ∈ noX c (Lam d L N) i :=
  mul_mem (expU_mem _ (neg_mem (H.upO_noX hb))) (H.Gp_noX hb)

/-! #### The second-order part `k^{(2)}`, its split `J`, and `K_{j+1}` -/

theorem k2_noX {i : Bool} {X : Finset (Lam d L N)}
    (hX : ∀ b ∈ blocks j X, Clean P j i b) : k2O j C V X ∈ noX c (Lam d L N) i := by
  unfold k2O; split_ifs
  · refine Subalgebra.sum_mem _ fun b hb => ?_
    rw [k2one_eq]
    exact sub_mem (Subalgebra.smul_mem _ (H.FCpair_noX (hX b hb) b) _) (H.SF_noX (hX b hb))
  · exact Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun b hb =>
      Subalgebra.sum_mem _ fun b' _ => H.FCpair_noX (hX b hb) b') _
  · exact zero_mem _

theorem kap_noX {i : Bool} {X : Finset (Lam d L N)}
    (hX : ∀ b ∈ blocks j X, Clean P j i b) (c' : Fin d → ℕ) :
    kapO j C V X c' ∈ noX c (Lam d L N) i := by
  unfold kapO; split_ifs
  · refine Subalgebra.sum_mem _ fun b hb => ?_
    have hb' := (mem_filter.1 hb).1
    rw [k2one_eq]
    exact sub_mem (Subalgebra.smul_mem _ (H.FCpair_noX (hX b hb') b) _) (H.SF_noX (hX b hb'))
  · refine Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun b hb =>
      Subalgebra.sum_mem _ fun b' hb' => add_mem (H.FCpair_noX (hX b (mem_filter.1 hb).1) b') ?_) _
    have h1 := H.Vpr_noX (farS_succ (clean_block (hX b (mem_filter.1 hb).1)))
    have h2 := H.Vpr_noX (farS_succ (clean_block (hX b' (mem_of_mem_erase hb'))))
    exact sub_mem (FCO_mem_noX C (πobs_mem_noX h1) h2) (FCO_mem_noX C h1 (πobs_mem_noX h2))
  · exact zero_mem _

theorem blocks_of_clo {X U : Finset (Lam d L N)} (h : clo j X = U) :
    blocks j X ⊆ blocks j U := blocks_mono (h ▸ subset_clo j X)

theorem K2_noX {i : Bool} {U : Finset (Lam d L N)}
    (hU : ∀ b ∈ blocks j U, Clean P j i b) : K2O j C V U ∈ noX c (Lam d L N) i :=
  Subalgebra.sum_mem _ fun X hX => H.k2_noX fun b hb =>
    hU b (H.blocks_of_clo (mem_filter.1 hX).2 hb)

theorem Jh_noX {i : Bool} {U : Finset (Lam d L N)}
    (hU : ∀ b ∈ blocks j U, Clean P j i b) (c' : Fin d → ℕ) :
    JhO j C V c' U ∈ noX c (Lam d L N) i := by
  unfold JhO; split_ifs
  · exact Subalgebra.sum_mem _ fun X hX => H.kap_noX (fun b hb =>
      hU b (H.blocks_of_clo (mem_filter.1 hX).2 hb)) c'
  · exact zero_mem _

theorem Knext2_noX {i : Bool} {U : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U)
    (hcl : ∀ b ∈ blocks j U, Clean P j i b)
    (hK : ∀ Y, IsConn j Y → Y ⊆ U → K Y ∈ noX c (Lam d L N) i) :
    Knext2O P j C V W K U ∈ noX c (Lam d L N) i := by
  have hUj := IsPolymer.of_succ hU
  have hsub : ∀ b, blockSet (L := L) (N := N) j b ⊆ U → b ∈ blockIdx (L := L) (N := N) j →
      b ∈ blocks j U := fun b hbU hb => by
    obtain ⟨x, -, hx⟩ := mem_image.1 hb
    exact mem_image.2 ⟨x, hbU (mem_blockSet.2 hx), hx⟩
  have hG : OGMem j C (IbO V W) (IpO P j C V W K) K (J2O P j K) U (noX c (Lam d L N) i)
      (noX c (Lam d L N ⊕ Lam d L N) i) :=
    { hθ := fun F hF => thetaO_mem_noX hF
      hι := fun F hF => inclO_mem_noX hF
      hE := fun F hF => ECCO_mem_noX C hF
      hK := hK
      hJ := fun b X hb hbU => H.J_noX (hcl b (hsub b hbU hb)) X
      hIb := fun b hb hbU => H.Ib_noX (hcl b (hsub b hbU hb))
      hIp := fun b hb hbU => H.Ip_noX (hcl b (hsub b hbU hb)) }
  refine mul_mem (expU_mem _ (Subalgebra.sum_mem _ fun b hb => H.upO_noX (hcl b hb)))
    (hG.gKnextO_mem hU)

theorem Knew_noX {i : Bool} {U : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U)
    (hcl : ∀ b ∈ blocks j U, Clean P j i b)
    (hK : ∀ Y, IsConn j Y → Y ⊆ U → K Y ∈ noX c (Lam d L N) i) :
    KnewO P j C V W K U ∈ noX c (Lam d L N) i :=
  sub_mem (H.Knext2_noX hU hcl hK)
    (mul_mem (prod_mem fun b hb => H.Gp_noX (hcl b hb)) (H.K2_noX hcl))

theorem It_noX {i : Bool} {c' : Fin d → ℕ}
    (hcl : ∀ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'), Clean P j i b) :
    ItO P j C V W K c' ∈ noX c (Lam d L N) i :=
  prod_mem fun b hb => H.Gp_noX (hcl b hb)

/-- **`K_{j+1}(U)` has no `σ_i`** if all `j`-blocks of `U` are clean and `K(Y)` has no `σ_i`
for the connected `Y ⊆ U`. -/
theorem Kplus_noX_of {i : Bool} {U : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U)
    (hcl : ∀ b ∈ blocks j U, Clean P j i b)
    (hK : ∀ Y, IsConn j Y → Y ⊆ U → K Y ∈ noX c (Lam d L N) i) :
    KplusO P j C V W K U ∈ noX c (Lam d L N) i := by
  refine KoutO_mem (fun X hX hXU => ?_) (fun Y hY hYU => ?_) (fun p hp hpU => ?_)
  · refine prod_mem fun c' hc' => H.It_noX fun b hb => hcl b (blocks_mono ?_ hb)
    exact (blockSet_subset_of_mem_blocks hX hc').trans hXU
  · exact H.Knew_noX hY.1 (fun b hb => hcl b (blocks_mono hYU hb))
      (fun Y' hY' hY'Y => hK Y' hY' (hY'Y.trans hYU))
  · exact H.Jh_noX (fun b hb => hcl b (blocks_mono hpU hb)) p.1

/-! #### Clean blocks from distances -/

omit H in
theorem clean_of_far {i : Bool} {U : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U)
    (hfar : FarS (L ^ (j + 1)) (P.pt i) U) {b : Fin d → ℕ} (hb : b ∈ blocks j U) :
    Clean P j i b := by
  have hbU := blockSet_subset_of_mem_blocks (IsPolymer.of_succ hU) hb
  obtain ⟨x, -, hxb⟩ := mem_blocks.1 hb
  exact ⟨⟨x, mem_blockSet.2 hxb⟩, farS_mono le_rfl hfar (clo_subset hU hbU)⟩

/-! ### The conclusions at scale `j + 1` -/

/-- `V_{j+1}(B_+)` has no `ab` component. -/
theorem Vnext_ab (c' : Fin d → ℕ) : Vnext2O P j C V W K c' ∈ abZ c (Lam d L N) :=
  Submodule.sum_mem _ fun b _ => H.Vp_ab b

/-- `V_{j+1}(B_+)_i` is supported at `p_i`. -/
theorem Vnext_pt (i : Bool) (c' : Fin d → ℕ) :
    cmp i (Vnext2O P j C V W K c' : SA c (Lam d L N)) ∈ NX ({P.pt i} : Set (Lam d L N)) := by
  rw [Vnext2O, AddSubmonoidClass.coe_finsetSum, cmp_sum]
  exact Subalgebra.sum_mem _ fun b _ => H.Vp_pt i b

/-- `V_{j+1}(B_+)` has no `σ_i` if `B_+` is at distance `≥ L^{j+1}` from `p_i`. -/
theorem Vnext_noX {i : Bool} {c' : Fin d → ℕ}
    (h : FarS (L ^ (j + 1)) (P.pt i) (blockSet (L := L) (N := N) (j + 1) c')) :
    Vnext2O P j C V W K c' ∈ noX c (Lam d L N) i :=
  Subalgebra.sum_mem _ fun _ hb => H.Vp_noX (clean_of_far (isPolymer_blockSet (j + 1) c') h hb)

/-- `𝒲_{j+1}(B_+)` has no `σ_i` if `B_+` is at distance `≥ L^{j+1}` from `p_i`. -/
theorem Wnext_noX {i : Bool} {c' : Fin d → ℕ}
    (h : FarS (L ^ (j + 1)) (P.pt i) (blockSet (L := L) (N := N) (j + 1) c')) :
    Wnext2O P j C V W c' ∈ noX c (Lam d L N) i :=
  sub_mem (prod_mem fun _ hb => add_mem (one_mem _) (H.Wp_noX
    (clean_of_far (isPolymer_blockSet (j + 1) c') h hb))) (one_mem _)

/-- `𝒲_{j+1}(B_+)` has no `ab` component if `|a - b|_∞ ≥ L^{j+2}/2`. -/
theorem Wnext_ab (hab' : (L : ℝ) ^ (j + 1 + 1) / 2 ≤ supNorm (P.a - P.b)) (c' : Fin d → ℕ) :
    Wnext2O P j C V W c' ∈ abZ c (Lam d L N) := by
  rcases block_far H.hL c' hab' with h | h
  · exact abZ_of_noX (H.Wnext_noX (i := true) h)
  · exact abZ_of_noX (H.Wnext_noX (i := false) h)

/-- `K_{j+1}(U)` has no `σ_i` if `U` is at distance `≥ L^{j+1}` from `p_i`. -/
theorem Kplus_noX {i : Bool} {U : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U)
    (h : FarS (L ^ (j + 1)) (P.pt i) U) : KplusO P j C V W K U ∈ noX c (Lam d L N) i :=
  H.Kplus_noX_of hU (fun _ hb => clean_of_far hU h hb)
    (fun Y hY hYU => H.hKno i Y hY (farS_mono (Nat.pow_le_pow_right
      (Nat.pos_of_ne_zero (NeZero.ne L)) (Nat.le_succ j)) h hYU))

/-- `K_{j+1}(U)` has no `ab` component for small `U` if `|a - b|_∞ ≥ L^{j+2}/2`. -/
theorem Kplus_ab (hab' : (L : ℝ) ^ (j + 1 + 1) / 2 ≤ supNorm (P.a - P.b))
    {U : Finset (Lam d L N)} (hU : IsSmall (j + 1) U) :
    KplusO P j C V W K U ∈ abZ c (Lam d L N) := by
  rcases small_far H.hL hU hab' with h | h
  · exact abZ_of_noX (H.Kplus_noX (i := true) hU.1 h)
  · exact abZ_of_noX (H.Kplus_noX (i := false) hU.1 h)

/-- The observable constant of the step has no `ab` component. -/
theorem uObsTot_ab : uObsTot P j C V W K ∈ abZ c (Lam d L N) :=
  Submodule.sum_mem _ fun b _ => H.upO_ab b

end CoalHyp

end

end Obs2
