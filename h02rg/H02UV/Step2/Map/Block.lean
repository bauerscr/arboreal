import Step2.Map.Crude
import Step2.Map.LinBound

/-!
# Block bounds for the second-order map

Bounds, at a fixed field scale `ℓ` and for `j + 1 < N`, on the block quantities of the map of
`Step2.Map.Defs` in terms of a radius `r` with `‖V‖_j, ‖𝒲‖_j, ‖K‖_j ≤ r`:

* `V'_B = 𝔼θV(B)`: `≤ Q₁ r` (Lemma `lem:pauli`, `Q₁ = q^{(2^{d+1}+3)^d}`);
* `F(V'_B, V'_{B'}) = 0` unless `B'` is near `B` (finite range of `C`), so
  `‖S(B)‖ ≤ (n Q₁² + Q₁) r` with `n` the number of near blocks, and `S(B) ∈ 𝒩((B_+)^□)`;
* `Loc_{B_+,B} S(B_+)` and `𝔼θQ(B)` (Lemma `lem:loc2` with `prop:Loc`(i));
* `u_{j+1}(B)`, `V_{j+1}(B)`, `𝒲_{j+1}(B)`, `I_{j+1}(B) - 1`, `δI(B)`, `θK(X)`, `θJ(B, X)`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

/-! ### Generalities -/

theorem gexp_mem_NX {X : Set (Lam d L N)} {F : EvR (Lam d L N)} (hF0 : ε (F : Alg d L N) = 0)
    (hF : (F : Alg d L N) ∈ NX X) : (gexp F : Alg d L N) ∈ NX X := by
  rw [coe_gexp (pow_eq_zero_of_ε' hF0 (Nat.lt_succ_self _))]
  exact Subalgebra.sum_mem _ fun i _ => Subalgebra.smul_mem _ (Subalgebra.pow_mem _ hF _) _

theorem FCE_add_right {Λ : Type*} [DecidableEq Λ] [Fintype Λ] (C : Matrix Λ Λ ℂ)
    (A B B' : EvR Λ) : FCE C A (B + B') = FCE C A B + FCE C A B' :=
  Subtype.ext (by simp only [coe_FCE, Subalgebra.coe_add]; exact FC_add_right _ _ _ _)

theorem FCE_zero_right {Λ : Type*} [DecidableEq Λ] [Fintype Λ] (C : Matrix Λ Λ ℂ)
    (A : EvR Λ) : FCE C A 0 = 0 := by
  have := FCE_smul_right C (0 : ℂ) A 0
  simpa using this

theorem FCE_sum_right {Λ : Type*} [DecidableEq Λ] [Fintype Λ] (C : Matrix Λ Λ ℂ)
    {ι : Type*} (s : Finset ι) (A : EvR Λ) (B : ι → EvR Λ) :
    FCE C A (∑ i ∈ s, B i) = ∑ i ∈ s, FCE C A (B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [FCE_zero_right]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, FCE_add_right, ih]

/-- The Pauli constant for a block neighbourhood. -/
def Q1 (d : ℕ) : ℝ := pq d ^ ((2 ^ (d + 1) + 3) ^ d)

theorem one_le_Q1 (hd : 1 ≤ d) : 1 ≤ Q1 d := one_le_pow₀ (one_le_pq hd)

theorem nb_nbhd_block_le {j : ℕ} (hj : j ≤ N) (b : Fin d → ℕ) :
    nb j (nbhd j (blockSet (L := L) (N := N) j b)) ≤ (2 ^ (d + 1) + 3) ^ d := by
  have := nb_nbhd_le (L := L) hj (blockSet (L := L) (N := N) j b)
  have h1 := nb_blockSet_le (L := L) (N := N) j b
  exact this.trans ((Nat.mul_le_mul_left _ h1).trans (le_of_eq (mul_one _)))

theorem pq_pow_le_Q1 (hd : 1 ≤ d) {j : ℕ} (hj : j ≤ N) (b : Fin d → ℕ) :
    pq d ^ nb j (nbhd j (blockSet (L := L) (N := N) j b)) ≤ Q1 d :=
  pow_le_pow_right₀ (one_le_pq hd) (nb_nbhd_block_le hj b)

theorem pq_pow_nbhd_le (hd : 1 ≤ d) {j : ℕ} (hj : j ≤ N) (X : Finset (Lam d L N)) :
    pq d ^ nb j (nbhd j X) ≤ Q1 d ^ nb j X := by
  rw [Q1, ← pow_mul]
  exact pow_le_pow_right₀ (one_le_pq hd) (nb_nbhd_le hj X)

section Pauli

variable (hd : 1 ≤ d) (hL : pauliL0 d ≤ L) {j : ℕ} (hj : j < N) {ℓ : ℝ} (hℓ : 0 < ℓ)
include hd hL hj hℓ

theorem Tj2_block_le {b : Fin d → ℕ} {F : Alg d L N}
    (hF : F ∈ NX (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N))) :
    Tj d (L : ℝ) (j + 1) (2 * ℓ) F ≤ ENNReal.ofReal (Q1 d) * Tj d (L : ℝ) j ℓ F :=
  (Tj_succ_two_le hd hL hj hF hℓ).trans
    (mul_le_mul_right' (ENNReal.ofReal_le_ofReal (pq_pow_le_Q1 hd hj.le b)) _)

theorem EthE_block_le {C : Matrix (Lam d L N) (Lam d L N) ℂ} (hC : GoodCov2 j ℓ C)
    {b : Fin d → ℕ} {F : EvR (Lam d L N)}
    (hF : (F : Alg d L N) ∈ NX (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N))) :
    Tj d (L : ℝ) (j + 1) ℓ (EthE C F : Alg d L N) ≤
      ENNReal.ofReal (Q1 d) * Tj d (L : ℝ) j ℓ (F : Alg d L N) := by
  rw [coe_EthE, ← ECC_theta]
  exact (EthE_succ_le hd hL hj hℓ hC hF).trans
    (mul_le_mul_right' (ENNReal.ofReal_le_ofReal (pq_pow_le_Q1 hd hj.le b)) _)

end Pauli

section Pauli2

variable (hd : 1 ≤ d) (hL : pauliL0 d ≤ L) {j : ℕ} (hj : j < N) {ℓ ℓ' ℓC : ℝ} (hℓ' : 0 < ℓ')
  (hℓC : 0 < ℓC) (hsum : ℓ' + ℓC ≤ 2 * ℓ)
include hd hL hj hℓ' hℓC hsum

theorem theta_block_le2 {b : Fin d → ℕ} {F : Alg d L N}
    (hF : F ∈ NX (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N))) :
    T2 (Dir d) (pPhi d) ((L : ℝ) ^ (j + 1)) ℓ' ℓC (theta F) ≤
      ENNReal.ofReal (Q1 d) * Tj d (L : ℝ) j ℓ F :=
  (theta_succ_le2 hd hL hj hF hℓ' hℓC hsum).trans
    (mul_le_mul_right' (ENNReal.ofReal_le_ofReal (pq_pow_le_Q1 hd hj.le b)) _)

theorem EthE_block_le2 {C : Matrix (Lam d L N) (Lam d L N) ℂ} (hC : GoodCov2 j ℓC C)
    {b : Fin d → ℕ} {F : EvR (Lam d L N)}
    (hF : (F : Alg d L N) ∈ NX (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N))) :
    Tj d (L : ℝ) (j + 1) ℓ' (EthE C F : Alg d L N) ≤
      ENNReal.ofReal (Q1 d) * Tj d (L : ℝ) j ℓ (F : Alg d L N) := by
  rw [coe_EthE, ← ECC_theta]
  exact (EthE_succ_le2 hd hL hj hℓ' hℓC hsum hC hF).trans
    (mul_le_mul_right' (ENNReal.ofReal_le_ofReal (pq_pow_le_Q1 hd hj.le b)) _)

theorem theta_conn_le2 {X : Finset (Lam d L N)} {F : Alg d L N}
    (hF : F ∈ NX (nbhd j X : Set (Lam d L N))) :
    T2 (Dir d) (pPhi d) ((L : ℝ) ^ (j + 1)) ℓ' ℓC (theta F) ≤
      ENNReal.ofReal (Q1 d ^ nb j X) * Tj d (L : ℝ) j ℓ F :=
  (theta_succ_le2 hd hL hj hF hℓ' hℓC hsum).trans
    (mul_le_mul_right' (ENNReal.ofReal_le_ofReal (pq_pow_nbhd_le hd hj.le X)) _)

end Pauli2

theorem tj_of {x a : ENNReal} {c r : ℝ} (hc : 0 ≤ c)
    (h1 : x ≤ ENNReal.ofReal c * a) (h2 : a ≤ ENNReal.ofReal r) :
    x ≤ ENNReal.ofReal (c * r) := by
  rw [ENNReal.ofReal_mul hc]; exact h1.trans (mul_le_mul_left' h2 _)

/-! ### The near blocks -/

theorem mem_nearSet_self {j : ℕ} {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    b ∈ nearSet (L := L) (N := N) j b := by
  classical
  obtain ⟨x, -, hx⟩ := mem_image.1 hb
  have hxB : x ∈ blockSet (L := L) (N := N) j b := mem_blockSet.2 hx
  have hxn : x ∈ nbhd j (blockSet (L := L) (N := N) j b) :=
    subset_nbhd (isSmall_blockSet_of_mem hb).1 hxB
  refine mem_filter.2 ⟨hb, x, hxn, x, hxn, ?_⟩
  rw [sub_self]
  rw [supNorm_zero, mul_zero]
  exact pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _

theorem Vpr_mem {C : Matrix (Lam d L N) (Lam d L N) ℂ} {V : Fam d L N} {j : ℕ} (hV : InF j V)
    (b : Fin d → ℕ) :
    (Vpr C V b : Alg d L N) ∈ NX (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N)) := by
  rw [Vpr, coe_EthE]; exact expLC_mem_NX _ (hV.loc b)

/-- Far blocks do not interact. -/
theorem FCE_Vpr_far {j : ℕ} (hjN : j + 1 < N) {C : Matrix (Lam d L N) (Lam d L N) ℂ} {ℓ : ℝ}
    (hC : GoodCov2 j ℓ C) {V : Fam d L N} (hV : InF j V) {b b' : Fin d → ℕ}
    (hb' : b' ∈ blockIdx (L := L) (N := N) j) (h : b' ∉ nearSet (L := L) (N := N) j b) :
    FCE C (Vpr C V b) (Vpr C V b') = 0 := by
  refine Subtype.ext ?_
  show FC C (Vpr C V b : Alg d L N) (Vpr C V b' : Alg d L N) = 0
  set Y1 : Finset (Lam d L N) := nbhd j (blockSet (L := L) (N := N) j b) with hY1
  set Y2 : Finset (Lam d L N) := nbhd j (blockSet (L := L) (N := N) j b') with hY2
  have hfar : ∀ x ∈ Y1, ∀ y ∈ Y2, L ^ (j + 1) ≤ 2 * supNorm (x - y) :=
    fun x hx y hy => not_near_far hb' h hx hy
  have hpos : 0 < L ^ (j + 1) := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
  have hdis : Disjoint (Y1 : Set (Lam d L N)) (Y2 : Set (Lam d L N)) := by
    rw [Set.disjoint_left]
    intro z hz hz'
    have h3 := hfar z hz z hz'
    rw [sub_self, supNorm_zero, mul_zero] at h3
    omega
  have hCz : ∀ x ∈ (Y1 : Set (Lam d L N)), ∀ y ∈ (Y2 : Set (Lam d L N)),
      C x y = 0 ∧ C y x = 0 := by
    intro x hx y hy
    have h1 : L ^ (j + 1) ≤ 2 * supNorm (x - y) := hfar x hx y hy
    have h1' : ((L : ℝ) ^ (j + 1)) / 2 ≤ (supNorm (x - y) : ℝ) := by
      have h4 : ((L ^ (j + 1) : ℕ) : ℝ) ≤ ((2 * supNorm (x - y) : ℕ) : ℝ) := Nat.cast_le.2 h1
      rw [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] at h4
      linarith
    have h2 : supNorm (y - x) = supNorm (x - y) := by
      rw [← neg_sub, supNorm_neg]
    exact ⟨hC.range hjN x y h1', hC.range hjN y x (by rw [h2]; exact h1')⟩
  exact FC_eq_zero_of_disjoint C hdis hCz (Vpr_mem hV b) (Vpr_mem hV b')

theorem FCE_VprL_eq {j : ℕ} (hjN : j + 1 < N) {C : Matrix (Lam d L N) (Lam d L N) ℂ} {ℓ : ℝ}
    (hC : GoodCov2 j ℓ C) {V : Fam d L N} (hV : InF j V) (b : Fin d → ℕ) :
    FCE C (Vpr C V b) (VprL j C V) =
      ∑ b' ∈ nearSet (L := L) (N := N) j b, FCE C (Vpr C V b) (Vpr C V b') := by
  classical
  rw [VprL, FCE_sum_right, nearSet, ← sum_filter_add_sum_filter_not (blockIdx j)
    (fun b' => ∃ x ∈ nbhd j (blockSet (L := L) (N := N) j b),
      ∃ y ∈ nbhd j (blockSet (L := L) (N := N) j b'), 2 * supNorm (x - y) < L ^ (j + 1))]
  rw [sum_eq_zero (s := filter (fun b' => ¬ _) _) fun b' hb' => ?_, add_zero]
  obtain ⟨hb'1, hb'2⟩ := mem_filter.1 hb'
  exact FCE_Vpr_far hjN hC hV hb'1 (fun h => hb'2 (mem_filter.1 h).2)

theorem Loc2XY_mem' (hd : 1 ≤ d) {j : ℕ} {Y : Finset (Lam d L N)} (hY : IsPolymer j Y)
    (X : Finset (Lam d L N)) (F : Alg d L N) : Loc2sXY X Y F ∈ NX (nbhd j Y : Set (Lam d L N)) :=
  add_mem (LocXY_mem hd hY X F) (Loc4sXY_mem hd hY X F)

/-! ### The hypotheses -/

/-- The block constants. -/
def cNear (d L : ℕ) : ℝ := ((L + 2 ^ (d + 3) + 7) ^ d : ℕ)
def cSblk (d L : ℕ) : ℝ := cNear d L * Q1 d ^ 2 + Q1 d
def cUblk (d L : ℕ) (Cl cS : ℝ) : ℝ := Q1 d + Q1 d * (cS * Cl) + Cl * (L : ℝ) ^ d * cSblk d L
def cWblk (d L : ℕ) (Cl : ℝ) : ℝ := cSblk d L + Cl * (L : ℝ) ^ d * cSblk d L
def cIblk (d L : ℕ) (Cl cS : ℝ) : ℝ := 18 * cUblk d L Cl cS + 2 * cWblk d L Cl

/-- The hypotheses for the block bounds, with radius `r`. -/
structure BH (j : ℕ) (ℓ ℓ' ℓC : ℝ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V W : Fam d L N)
    (K : Act d L N) (A r Cl cS : ℝ) : Prop where
  hd : 1 ≤ d
  hLp : pauliL0 d ≤ L
  hL8 : 2 ^ (d + 3) + 8 * d < L
  hjN : j + 1 < N
  hℓ : 0 < ℓ
  hℓ' : 0 < ℓ'
  hℓC : 0 < ℓC
  hsum : ℓ' + ℓC ≤ 2 * ℓ
  hC : GoodCov2 j ℓC C
  hV : InF j V
  hW : InF j W
  hV0 : ∀ b, ε (V b : Alg d L N) = 0
  hK : InK2 j K
  hA : 1 ≤ A
  hr : 0 ≤ r
  hr1 : r ≤ 1
  hVr : ∀ b ∈ blockIdx (L := L) (N := N) j, Tj d (L : ℝ) j ℓ (V b : Alg d L N) ≤ ENNReal.ofReal r
  hWr : ∀ b ∈ blockIdx (L := L) (N := N) j, Tj d (L : ℝ) j ℓ (W b : Alg d L N) ≤ ENNReal.ofReal r
  hKr : Knorm j ℓ A K ≤ ENNReal.ofReal r
  hCl : 0 ≤ Cl
  hloc : ∀ k : ℕ, k < N → ∀ ℓ₀ : ℝ, 0 < ℓ₀ → ∀ X Y : Finset (Lam d L N), IsSmall k X → Y ⊆ X →
    ∀ F ∈ NX (nbhd k X : Set (Lam d L N)),
      Tj d (L : ℝ) k ℓ₀ (Loc2sXY X Y F) ≤ ENNReal.ofReal Cl * Tj d (L : ℝ) k ℓ₀ F
  hcS : 1 ≤ cS
  hcount : ∀ b ∈ blockIdx (d := d) (L := L) (N := N) j,
    (((smallSets (d := d) (L := L) (N := N) j).filter (fun X => blockSet j b ⊆ X)).card : ℝ) ≤ cS

namespace BH

variable {j : ℕ} {ℓ ℓ' ℓC : ℝ} {C : Matrix (Lam d L N) (Lam d L N) ℂ} {V W : Fam d L N}
  {K : Act d L N} {A r Cl cS : ℝ} (H : BH j ℓ ℓ' ℓC C V W K A r Cl cS)
include H

theorem hj : j < N := by have := H.hjN; omega

theorem hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)

theorem hh' : (0 : ℝ) < (L : ℝ) ^ (j + 1) := pow_pos H.hL0 _

theorem hQ1 : 1 ≤ Q1 d := one_le_Q1 H.hd

theorem hcNear : 0 ≤ cNear d L := Nat.cast_nonneg _

theorem hcS2 : 0 ≤ cSblk d L := by
  have := H.hQ1; have := H.hcNear; unfold cSblk; positivity

theorem hcS0 : 0 ≤ cS := by linarith [H.hcS]

theorem hcU : 0 ≤ cUblk d L Cl cS := by
  have := H.hQ1; have := H.hcS2; have := H.hCl; have := H.hcS0; have := H.hL0
  unfold cUblk; positivity

theorem hcW : 0 ≤ cWblk d L Cl := by
  have := H.hcS2; have := H.hCl; have := H.hL0; unfold cWblk; positivity

theorem Vpr_le {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    Tj d (L : ℝ) (j + 1) ℓ' (Vpr C V b : Alg d L N) ≤ ENNReal.ofReal (Q1 d * r) := by
  rw [Vpr]
  exact tj_of (by linarith [H.hQ1]) (EthE_block_le2 H.hd H.hLp H.hj H.hℓ' H.hℓC H.hsum H.hC (H.hV.loc b))
    (H.hVr b hb)

theorem V2_le {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    Tj d (L : ℝ) (j + 1) (2 * ℓ) (V b : Alg d L N) ≤ ENNReal.ofReal (Q1 d * r) := by
  rw [ENNReal.ofReal_mul (by linarith [H.hQ1])]
  exact (Tj2_block_le H.hd H.hLp H.hj H.hℓ (H.hV.loc b)).trans (mul_le_mul_left' (H.hVr b hb) _)

theorem FCE_pair_le {b b' : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j)
    (hb' : b' ∈ blockIdx (L := L) (N := N) j) :
    Tj d (L : ℝ) (j + 1) ℓ' (FCE C (Vpr C V b) (Vpr C V b') : Alg d L N) ≤
      ENNReal.ofReal (2 * (Q1 d * r) ^ 2) := by
  have e : ∀ b, (Vpr C V b : Alg d L N) = ECC C (theta (V b : Alg d L N)) := fun b => by
    rw [Vpr, coe_EthE, ECC_theta]
  rw [coe_FCE, e, e]
  refine (FC_succ_le2 H.hℓ' H.hℓC H.hsum H.hC _ _).trans ?_
  have hq : 0 ≤ Q1 d * r := mul_nonneg (by linarith [H.hQ1]) H.hr
  rw [sq, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul hq, ENNReal.ofReal_ofNat]
  gcongr
  · exact H.V2_le hb
  · exact H.V2_le hb'

theorem Sb_le {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    Tj d (L : ℝ) (j + 1) ℓ' (Sb j C V W b : Alg d L N) ≤ ENNReal.ofReal (cSblk d L * r) := by
  have hQ := H.hQ1
  have hr := H.hr
  rw [Sb, FCE_VprL_eq H.hjN H.hC H.hV b]
  have h1 := tn_sum_const (E := Dir d) (p := pPhi d) (h := (L : ℝ) ^ (j + 1)) (ℓ := ℓ')
    (nearSet (L := L) (N := N) j b) (fun b' => FCE C (Vpr C V b) (Vpr C V b'))
    (r := 2 * (Q1 d * r) ^ 2) (by positivity)
    (fun b' hb' => H.FCE_pair_le hb (mem_filter.1 hb').1)
  have hn : ((nearSet (L := L) (N := N) j b).card : ℝ) ≤ cNear d L := by
    unfold cNear; exact_mod_cast card_nearSet_le H.hj.le b hb
  have h2 : Tj d (L : ℝ) (j + 1) ℓ' (((1 / 2 : ℂ) • ∑ b' ∈ nearSet (L := L) (N := N) j b,
      FCE C (Vpr C V b) (Vpr C V b') : EvR (Lam d L N)) : Alg d L N) ≤
      ENNReal.ofReal (cNear d L * Q1 d ^ 2 * r) := by
    rw [Subalgebra.coe_smul, Tj_smul']
    refine (mul_le_mul_left' h1 _).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hr2 : r ^ 2 ≤ r := by nlinarith [H.hr1]
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [this]
    have h0 : 0 ≤ Q1 d ^ 2 := by positivity
    calc 1 / 2 * (((nearSet (L := L) (N := N) j b).card : ℝ) * (2 * (Q1 d * r) ^ 2))
        = ((nearSet (L := L) (N := N) j b).card : ℝ) * (Q1 d ^ 2 * r ^ 2) := by ring
      _ ≤ cNear d L * (Q1 d ^ 2 * r) := by have := H.hcNear; gcongr
      _ = _ := by ring
  have h3 : Tj d (L : ℝ) (j + 1) ℓ' (EthE C (W b) : Alg d L N) ≤ ENNReal.ofReal (Q1 d * r) :=
    tj_of (by linarith) (EthE_block_le2 H.hd H.hLp H.hj H.hℓ' H.hℓC H.hsum H.hC (H.hW.loc b)) (H.hWr b hb)
  refine (tn_addE (by have := H.hcNear; positivity) (by positivity) h2 h3).trans
    (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  unfold cSblk; ring

theorem hL8' : 2 ^ (d + 3) ≤ L := by have := H.hL8; omega

theorem nbhd_block_sub {b b' : Fin d → ℕ} (hb' : b' ∈ nearSet (L := L) (N := N) j b) :
    (nbhd j (blockSet (L := L) (N := N) j b') : Set (Lam d L N)) ⊆
      (nbhd (j + 1) (Bp (L := L) (N := N) j b) : Set (Lam d L N)) := fun _ hy =>
  mem_nbhd_succ_of_near H.hd H.hL8' H.hjN.le hb' hy

theorem Sb_mem {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    (Sb j C V W b : Alg d L N) ∈ NX (nbhd (j + 1) (Bp (L := L) (N := N) j b) : Set (Lam d L N)) := by
  rw [Sb, FCE_VprL_eq H.hjN H.hC H.hV b]
  have hs := H.nbhd_block_sub (mem_nearSet_self hb)
  refine add_mem (Subalgebra.smul_mem _ ?_ _) ?_
  · rw [AddSubmonoidClass.coe_finsetSum]
    refine Subalgebra.sum_mem _ fun b' hb' => ?_
    rw [coe_FCE]
    exact FC_mem_NX C (NX_mono hs (Vpr_mem H.hV b)) (NX_mono (H.nbhd_block_sub hb') (Vpr_mem H.hV b'))
  · rw [coe_EthE]; exact NX_mono hs (expLC_mem_NX _ (H.hW.loc b))

omit H in
theorem Bp_sub {b b'' : Fin d → ℕ} (h : b'' ∈ blocks j (Bp (L := L) (N := N) j b)) :
    Bp (L := L) (N := N) j b'' ⊆ Bp (L := L) (N := N) j b := by
  refine clo_subset (isPolymer_clo j _) fun z hz => ?_
  obtain ⟨x, hx, hxb⟩ := mem_blocks.1 h
  rw [Bp, mem_clo] at hx ⊢
  rw [blk_succ, mem_blockSet.1 hz, ← hxb, ← blk_succ]
  exact hx

theorem SX_mem {b : Fin d → ℕ} :
    (SX j C V W (Bp (L := L) (N := N) j b) : Alg d L N) ∈
      NX (nbhd (j + 1) (Bp (L := L) (N := N) j b) : Set (Lam d L N)) := by
  rw [SX, AddSubmonoidClass.coe_finsetSum]
  refine Subalgebra.sum_mem _ fun b'' hb'' => ?_
  exact NX_mono (nbhd_mono (Bp_sub hb'')) (H.Sb_mem (mem_blockIdx_of_mem_blocks hb''))

theorem nb_Bp_le (b : Fin d → ℕ) : nb j (Bp (L := L) (N := N) j b) ≤ L ^ d := by
  have h1 := nb_le_of_succ (isPolymer_clo (L := L) (N := N) j (blockSet j b))
  have h2 := (nb_clo_le (L := L) (N := N) j (blockSet j b)).trans (nb_blockSet_le j b)
  calc nb j (Bp (L := L) (N := N) j b) ≤ L ^ d * nb (j + 1) (clo j (blockSet j b)) := h1
    _ ≤ L ^ d * 1 := Nat.mul_le_mul_left _ h2
    _ = L ^ d := mul_one _

theorem SX_le (b : Fin d → ℕ) :
    Tj d (L : ℝ) (j + 1) ℓ' (SX j C V W (Bp (L := L) (N := N) j b) : Alg d L N) ≤
      ENNReal.ofReal ((L : ℝ) ^ d * (cSblk d L * r)) := by
  have := H.hcS2
  have hr := H.hr
  rw [SX]
  refine (tn_sum_const (E := Dir d) (p := pPhi d) _ _ (by positivity) fun b'' hb'' =>
    H.Sb_le (mem_blockIdx_of_mem_blocks hb'')).trans (ENNReal.ofReal_le_ofReal ?_)
  have : ((blocks j (Bp (L := L) (N := N) j b)).card : ℝ) ≤ (L : ℝ) ^ d := by
    exact_mod_cast H.nb_Bp_le b
  gcongr

theorem LS_le {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    Tj d (L : ℝ) (j + 1) ℓ' (LS j C V W b : Alg d L N) ≤
      ENNReal.ofReal (Cl * (L : ℝ) ^ d * cSblk d L * r) := by
  have := H.hcS2
  have hr := H.hr
  have hCl := H.hCl
  rw [LS, coe_Loc2E]
  refine (H.hloc (j + 1) H.hjN ℓ' H.hℓ' _ _ (isSmall_clo (isSmall_blockSet_of_mem hb))
    (subset_clo j _) _ H.SX_mem).trans ?_
  refine (mul_le_mul_left' (H.SX_le b) _).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul hCl]; congr 1; ring

theorem loc_term_le {b : Fin d → ℕ} {X : Finset (Lam d L N)} (hs : IsSmall j X)
    (hbX : blockSet (L := L) (N := N) j b ⊆ X) :
    Tj d (L : ℝ) j ℓ (Loc2E X (blockSet (L := L) (N := N) j b) (K X) : Alg d L N) ≤
      ENNReal.ofReal (Cl * r) := by
  have hc : IsConn j X := ⟨hs.1, hs.2.1⟩
  rw [coe_Loc2E]
  refine (H.hloc j H.hj ℓ H.hℓ X _ hs hbX _ (H.hK.loc X hc)).trans ?_
  rw [ENNReal.ofReal_mul H.hCl]
  exact mul_le_mul_left' ((Tj_le_Knorm H.hA hc).trans H.hKr) _

theorem Q2_le {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    Tj d (L : ℝ) (j + 1) ℓ' (EthE C (Q2 j K b) : Alg d L N) ≤
      ENNReal.ofReal (Q1 d * (cS * (Cl * r))) := by
  classical
  have hr := H.hr
  have hCl := H.hCl
  have hYp : IsPolymer j (blockSet (L := L) (N := N) j b) := (isSmall_blockSet_of_mem hb).1
  have hmem : (Q2 j K b : Alg d L N) ∈
      NX (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N)) := by
    rw [Q2, if_pos H.hjN, AddSubmonoidClass.coe_finsetSum]
    exact Subalgebra.sum_mem _ fun X _ => Loc2XY_mem' H.hd hYp _ _
  refine tj_of (by linarith [H.hQ1]) (EthE_block_le2 H.hd H.hLp H.hj H.hℓ' H.hℓC H.hsum H.hC hmem) ?_
  rw [Q2, if_pos H.hjN]
  refine (tn_sum_const (E := Dir d) (p := pPhi d) _ _ (r := Cl * r) (by positivity)
    fun X hX => ?_).trans (ENNReal.ofReal_le_ofReal ?_)
  · obtain ⟨hs, hbX⟩ := mem_smallSets_filter.1 hX
    exact H.loc_term_le hs hbX
  · exact mul_le_mul_of_nonneg_right (H.hcount b hb) (by positivity)

theorem uVp_le {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    Tj d (L : ℝ) (j + 1) ℓ' (uVp j C V W K b : Alg d L N) ≤ ENNReal.ofReal (cUblk d L Cl cS * r) := by
  have := H.hQ1; have := H.hcS2; have := H.hCl; have := H.hcS0; have := H.hL0; have := H.hr
  rw [uVp]
  refine (tn_subE (by positivity) (by positivity) (tn_subE (by positivity) (by positivity)
    (H.Vpr_le hb) (H.Q2_le hb)) (H.LS_le hb)).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  unfold cUblk; ring

theorem up_le {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    ‖up j C V W K b‖ ≤ cUblk d L Cl cS * r := by
  have h := (abs_ε_le (E := Dir d) (p := pPhi d) H.hh' H.hℓ' _).trans (H.uVp_le hb)
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg H.hcU H.hr)).1 h

theorem Vp_le {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    Tj d (L : ℝ) (j + 1) ℓ' (Vp j C V W K b : Alg d L N) ≤
      ENNReal.ofReal (2 * (cUblk d L Cl cS * r)) := by
  have h0 : 0 ≤ cUblk d L Cl cS * r := mul_nonneg H.hcU H.hr
  rw [Vp]
  refine (tn_subE h0 h0 (H.uVp_le hb) ?_).trans (ENNReal.ofReal_le_ofReal (by linarith))
  rw [Subalgebra.coe_algebraMap]
  exact (tNorm_algebraMap_le H.hh' H.hℓ' _).trans (ENNReal.ofReal_le_ofReal (H.up_le hb))

theorem Wp_le {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    Tj d (L : ℝ) (j + 1) ℓ' (Wp j C V W b : Alg d L N) ≤ ENNReal.ofReal (cWblk d L Cl * r) := by
  have := H.hcS2; have := H.hCl; have := H.hL0; have := H.hr
  rw [Wp]
  refine (tn_subE (by positivity) (by positivity) (H.Sb_le hb) (H.LS_le hb)).trans
    (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  unfold cWblk; ring

omit H in
theorem exp_quarter_le : Real.exp (1 / 4) ≤ 2 := by
  have := (abs_le.1 (Real.abs_exp_sub_one_le (x := 1 / 4) (by norm_num))).2
  linarith

theorem Ip_sub_one_le (hu : cUblk d L Cl cS * r ≤ 1 / 4) (hw : cWblk d L Cl * r ≤ 1)
    {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    Tj d (L : ℝ) (j + 1) ℓ' ((Ip j C V W K b - 1 : EvR (Lam d L N)) : Alg d L N) ≤
      ENNReal.ofReal (cIblk d L Cl cS * r) := by
  have hr := H.hr
  have hU0 : 0 ≤ cUblk d L Cl cS * r := mul_nonneg H.hcU hr
  have hW0 : 0 ≤ cWblk d L Cl * r := mul_nonneg H.hcW hr
  set c : ℂ := Complex.exp (-up j C V W K b)
  set G : EvR (Lam d L N) := (gexp (-Vp j C V W K b) - 1) * (1 + Wp j C V W b) + Wp j C V W b
  have e : Ip j C V W K b - 1 = c • G + (c - 1) • (1 : EvR (Lam d L N)) := by
    have : gexp (-Vp j C V W K b) * (1 + Wp j C V W b) = G + 1 := by simp only [G]; ring
    rw [Ip, this, smul_add, sub_smul, one_smul]; abel
  have hε : ε ((-Vp j C V W K b : EvR (Lam d L N)) : Alg d L N) = 0 := by
    rw [NegMemClass.coe_neg, map_neg, ε_Vp, neg_zero]
  have hg : Tj d (L : ℝ) (j + 1) ℓ' ((gexp (-Vp j C V W K b) - 1 : EvR (Lam d L N)) : Alg d L N) ≤
      ENNReal.ofReal (2 * (2 * (cUblk d L Cl cS * r))) := by
    refine (tNorm_gexp_sub_one_le H.hh' H.hℓ' hε (by positivity) ?_).trans
      (ENNReal.ofReal_le_ofReal (exp_sub_one_le (by positivity) (by linarith)))
    rw [NegMemClass.coe_neg, tNorm_neg]; exact H.Vp_le hb
  have h1W : Tj d (L : ℝ) (j + 1) ℓ' ((1 + Wp j C V W b : EvR (Lam d L N)) : Alg d L N) ≤
      ENNReal.ofReal (1 + cWblk d L Cl * r) :=
    tn_addE zero_le_one hW0 (by
      rw [OneMemClass.coe_one, ENNReal.ofReal_one]; exact tNorm_one_le H.hh' H.hℓ') (H.Wp_le hb)
  have hG : Tj d (L : ℝ) (j + 1) ℓ' (G : Alg d L N) ≤
      ENNReal.ofReal (2 * (2 * (cUblk d L Cl cS * r)) * (1 + cWblk d L Cl * r) + cWblk d L Cl * r) :=
    tn_addE (by positivity) hW0 (tn_mulE H.hh' H.hℓ' (by positivity) hg h1W) (H.Wp_le hb)
  have hupn : ‖up j C V W K b‖ ≤ 1 / 4 := (H.up_le hb).trans hu
  have hc : ‖c‖ ≤ 2 := by
    rw [Complex.norm_exp]
    refine (Real.exp_le_exp.2 ((Complex.re_le_norm _).trans ?_)).trans exp_quarter_le
    rw [norm_neg]; exact hupn
  have hc1 : ‖c - 1‖ ≤ 2 * (cUblk d L Cl cS * r) := by
    refine (Complex.norm_exp_sub_one_le (by rw [norm_neg]; linarith)).trans ?_
    rw [norm_neg]; linarith [H.up_le hb]
  rw [e]
  refine (tNorm_add_le _ _).trans ?_
  rw [Subalgebra.coe_smul, Subalgebra.coe_smul, tNorm_smul, tNorm_smul, OneMemClass.coe_one]
  have h1 := tNorm_one_le (E := Dir d) (p := pPhi d) (X := Lam d L N) H.hh' H.hℓ'
  calc ENNReal.ofReal ‖c‖ * Tj d (L : ℝ) (j + 1) ℓ' (G : Alg d L N) +
        ENNReal.ofReal ‖c - 1‖ * Tj d (L : ℝ) (j + 1) ℓ' (1 : Alg d L N)
      ≤ ENNReal.ofReal 2 * ENNReal.ofReal
          (2 * (2 * (cUblk d L Cl cS * r)) * (1 + cWblk d L Cl * r) + cWblk d L Cl * r) +
        ENNReal.ofReal (2 * (cUblk d L Cl cS * r)) * 1 := by
        gcongr
    _ = ENNReal.ofReal (2 * (2 * (2 * (cUblk d L Cl cS * r)) * (1 + cWblk d L Cl * r) +
          cWblk d L Cl * r) + 2 * (cUblk d L Cl cS * r)) := by
        rw [mul_one, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
    _ ≤ ENNReal.ofReal (cIblk d L Cl cS * r) := by
        refine ENNReal.ofReal_le_ofReal ?_
        unfold cIblk
        nlinarith

theorem Ib_sub_one_le {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    Tj d (L : ℝ) j ℓ ((Ib V W b - 1 : EvR (Lam d L N)) : Alg d L N) ≤ ENNReal.ofReal (5 * r) := by
  have hr := H.hr
  have hh : (0 : ℝ) < (L : ℝ) ^ j := pow_pos H.hL0 _
  have e : Ib V W b - 1 = (gexp (-V b) - 1) * (1 + W b) + W b := by rw [Ib]; ring
  have hε : ε ((-V b : EvR (Lam d L N)) : Alg d L N) = 0 := by
    rw [NegMemClass.coe_neg, map_neg, H.hV0 b, neg_zero]
  have hg : Tj d (L : ℝ) j ℓ ((gexp (-V b) - 1 : EvR (Lam d L N)) : Alg d L N) ≤
      ENNReal.ofReal (2 * r) := by
    refine (tNorm_gexp_sub_one_le hh H.hℓ hε hr ?_).trans
      (ENNReal.ofReal_le_ofReal (exp_sub_one_le hr H.hr1))
    rw [NegMemClass.coe_neg, tNorm_neg]; exact H.hVr b hb
  have h1W : Tj d (L : ℝ) j ℓ ((1 + W b : EvR (Lam d L N)) : Alg d L N) ≤
      ENNReal.ofReal (1 + r) :=
    tn_addE zero_le_one hr (by
      rw [OneMemClass.coe_one, ENNReal.ofReal_one]; exact tNorm_one_le hh H.hℓ) (H.hWr b hb)
  rw [e]
  refine (tn_addE (by positivity) hr (tn_mulE hh H.hℓ (by positivity) hg h1W)
    (H.hWr b hb)).trans (ENNReal.ofReal_le_ofReal ?_)
  nlinarith [H.hr1]

theorem Ib_sub_one_mem (b : Fin d → ℕ) :
    ((Ib V W b - 1 : EvR (Lam d L N)) : Alg d L N) ∈
      NX (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N)) := by
  have hε : ε ((-V b : EvR (Lam d L N)) : Alg d L N) = 0 := by
    rw [NegMemClass.coe_neg, map_neg, H.hV0 b, neg_zero]
  rw [Ib, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, AddMemClass.coe_add,
    OneMemClass.coe_one]
  refine sub_mem (mul_mem (gexp_mem_NX hε ?_) (add_mem (one_mem _) (H.hV.loc b |> fun _ =>
    H.hW.loc b))) (one_mem _)
  rw [NegMemClass.coe_neg]; exact neg_mem (H.hV.loc b)

theorem gdI_le (hu : cUblk d L Cl cS * r ≤ 1 / 4) (hw : cWblk d L Cl * r ≤ 1)
    {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    T2 (Dir d) (pPhi d) ((L : ℝ) ^ (j + 1)) ℓ' ℓC (gdI (Ib V W) (Ip j C V W K) b : Alg2 d L N) ≤
      ENNReal.ofReal ((5 * Q1 d + cIblk d L Cl cS) * r) := by
  have hr := H.hr
  have hQ := H.hQ1
  have hcI : 0 ≤ cIblk d L Cl cS := by have := H.hcU; have := H.hcW; unfold cIblk; positivity
  have e : gdI (Ib V W) (Ip j C V W K) b =
      thetaE (Ib V W b - 1) - inclE (Ip j C V W K b - 1) := by
    rw [gdI, map_sub, map_sub, map_one, map_one]; abel
  rw [e]
  refine (t2_subE (s := Q1 d * (5 * r)) (t := cIblk d L Cl cS * r) (by positivity)
    (by positivity) ?_ ?_).trans (ENNReal.ofReal_le_ofReal (le_of_eq (by ring)))
  · rw [coe_thetaE]
    exact tj_of (by linarith) (theta_block_le2 H.hd H.hLp H.hj H.hℓ' H.hℓC H.hsum (H.Ib_sub_one_mem b))
      (H.Ib_sub_one_le hb)
  · rw [coe_inclE]
    exact (T2_incl_le H.hh' H.hℓ' _).trans (H.Ip_sub_one_le hu hw hb)

theorem thetaK_le {X : Finset (Lam d L N)} (hX : IsConn j X) :
    T2 (Dir d) (pPhi d) ((L : ℝ) ^ (j + 1)) ℓ' ℓC (thetaE (K X) : Alg2 d L N) ≤
      ENNReal.ofReal (r * A ^ 2 ^ d * (Q1 d / A) ^ nb j X) := by
  have hA1 := H.hA
  have hA0 : 0 < A := by linarith
  have hr := H.hr
  have hQ := H.hQ1
  rw [coe_thetaE]
  refine (theta_conn_le2 H.hd H.hLp H.hj H.hℓ' H.hℓC H.hsum (H.hK.loc X hX)).trans ?_
  have hw := (wnorm_le_Knorm (ℓ := ℓ) (A := A) (K := K) hX).trans H.hKr
  rw [wnorm] at hw
  set n := nb j X
  have hAn : (1 : ℝ) ≤ A ^ 2 ^ d * A⁻¹ ^ n * A ^ (n - 2 ^ d) := by
    have h1 : A ^ n ≤ A ^ 2 ^ d * A ^ (n - 2 ^ d) := by
      rw [← pow_add]; exact pow_le_pow_right₀ hA1 (by omega)
    have hAn0 : 0 < A ^ n := by positivity
    rw [inv_pow]
    calc (1 : ℝ) = A ^ n * (A ^ n)⁻¹ := (mul_inv_cancel₀ hAn0.ne').symm
      _ ≤ (A ^ 2 ^ d * A ^ (n - 2 ^ d)) * (A ^ n)⁻¹ := by gcongr
      _ = _ := by ring
  have hT : Tj d (L : ℝ) j ℓ (K X : Alg d L N) ≤ ENNReal.ofReal (r * A ^ 2 ^ d * A⁻¹ ^ n) := by
    calc Tj d (L : ℝ) j ℓ (K X : Alg d L N)
        ≤ ENNReal.ofReal (A ^ 2 ^ d * A⁻¹ ^ n * A ^ (n - 2 ^ d)) *
            Tj d (L : ℝ) j ℓ (K X : Alg d L N) := by
          refine le_mul_of_one_le_left zero_le ?_
          rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hAn
      _ = ENNReal.ofReal (A ^ 2 ^ d * A⁻¹ ^ n) * (ENNReal.ofReal (A ^ (n - 2 ^ d)) *
            Tj d (L : ℝ) j ℓ (K X : Alg d L N)) := by
          rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
      _ ≤ ENNReal.ofReal (A ^ 2 ^ d * A⁻¹ ^ n) * ENNReal.ofReal r := by gcongr
      _ = ENNReal.ofReal (r * A ^ 2 ^ d * A⁻¹ ^ n) := by
          rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
  refine (mul_le_mul_left' hT _).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [div_eq_mul_inv, mul_pow]; ring

theorem thetaJ_le {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j)
    (X : Finset (Lam d L N)) :
    T2 (Dir d) (pPhi d) ((L : ℝ) ^ (j + 1)) ℓ' ℓC (thetaE (J2 j K b X) : Alg2 d L N) ≤
      ENNReal.ofReal (Q1 d * (cS * (Cl * r))) := by
  classical
  have hr := H.hr
  have hCl := H.hCl
  have hcS := H.hcS0
  have hYp : IsPolymer j (blockSet (L := L) (N := N) j b) := (isSmall_blockSet_of_mem hb).1
  have hmem : (J2 j K b X : Alg d L N) ∈
      NX (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N)) := by
    rw [J2]
    split_ifs
    · rw [NegMemClass.coe_neg, AddSubmonoidClass.coe_finsetSum]
      exact neg_mem (Subalgebra.sum_mem _ fun Y _ => Loc2XY_mem' H.hd hYp _ _)
    · exact Loc2XY_mem' H.hd hYp _ _
    · exact zero_mem _
  rw [coe_thetaE]
  refine tj_of (by linarith [H.hQ1])
    (theta_block_le2 H.hd H.hLp H.hj H.hℓ' H.hℓC H.hsum hmem) ?_
  rw [J2]
  split_ifs with h1 h2
  · rw [NegMemClass.coe_neg]
    refine (le_of_eq (tNorm_neg _)).trans ?_
    refine (tn_sum_const (E := Dir d) (p := pPhi d) _ _ (r := Cl * r) (by positivity)
      fun Y hY => ?_).trans (ENNReal.ofReal_le_ofReal ?_)
    · obtain ⟨hY1, hY2⟩ := mem_filter.1 hY
      exact H.loc_term_le (mem_smallSets.1 hY1) hY2.1
    · refine mul_le_mul_of_nonneg_right (le_trans ?_ (H.hcount b hb)) (by positivity)
      exact_mod_cast card_le_card fun Y hY => by
        obtain ⟨hY1, hY2⟩ := mem_filter.1 hY
        exact mem_filter.2 ⟨hY1, hY2.1⟩
  · refine (H.loc_term_le h1.2.1 h1.2.2).trans (ENNReal.ofReal_le_ofReal ?_)
    have := mul_le_mul_of_nonneg_right H.hcS (by positivity : (0 : ℝ) ≤ Cl * r)
    linarith
  · rw [ZeroMemClass.coe_zero, Step.Tj_zero (d := d) (L : ℝ) j ℓ]; exact zero_le

theorem Ip_le (hu : cUblk d L Cl cS * r ≤ 1 / 4) (hw : cWblk d L Cl * r ≤ 1)
    {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    Tj d (L : ℝ) (j + 1) ℓ' (Ip j C V W K b : Alg d L N) ≤
      ENNReal.ofReal (Real.exp (cIblk d L Cl cS * r)) := by
  have hcI : 0 ≤ cIblk d L Cl cS := by have := H.hcU; have := H.hcW; unfold cIblk; positivity
  have e : Ip j C V W K b = 1 + (Ip j C V W K b - 1) := by abel
  rw [e]
  refine (tn_addE zero_le_one (by have := H.hr; positivity)
    (by rw [OneMemClass.coe_one, ENNReal.ofReal_one]; exact tNorm_one_le H.hh' H.hℓ')
    (H.Ip_sub_one_le hu hw hb)).trans (ENNReal.ofReal_le_ofReal ?_)
  linarith [Real.add_one_le_exp (cIblk d L Cl cS * r)]

/-- The prefactors `e^{u(U)} I_{j+1}^{U ∖ Z}`. -/
theorem pref_le (hu : cUblk d L Cl cS * r ≤ 1 / 4) (hw : cWblk d L Cl * r ≤ 1)
    (U Z : Finset (Lam d L N)) :
    Tj d (L : ℝ) (j + 1) ℓ' ((Complex.exp (uX j C V W K U) • bpow j (Ip j C V W K) (U \ Z) :
      EvR (Lam d L N)) : Alg d L N) ≤
      ENNReal.ofReal (Real.exp ((cUblk d L Cl cS + cIblk d L Cl cS) * r * nb j U)) := by
  have hr := H.hr
  have hcI : 0 ≤ cIblk d L Cl cS := by have := H.hcU; have := H.hcW; unfold cIblk; positivity
  have hcU := H.hcU
  rw [Subalgebra.coe_smul, Tj_smul']
  have hb : Tj d (L : ℝ) (j + 1) ℓ' (bpow j (Ip j C V W K) (U \ Z) : Alg d L N) ≤
      ENNReal.ofReal (Real.exp (cIblk d L Cl cS * r) ^ nb j U) := by
    have := tn_prodE (E := Dir d) (p := pPhi d) H.hh' H.hℓ' (blocks j (U \ Z)) (Ip j C V W K)
      (fun _ => Real.exp (cIblk d L Cl cS * r)) (fun _ _ => (Real.exp_pos _).le)
      (fun b hb => H.Ip_le hu hw (mem_blockIdx_of_mem_blocks hb))
    rw [prod_const] at this
    refine this.trans (ENNReal.ofReal_le_ofReal ?_)
    exact pow_le_pow_right₀ (Real.one_le_exp (by positivity))
      (card_le_card (blocks_mono sdiff_subset))
  have hc : ‖Complex.exp (uX j C V W K U)‖ ≤ Real.exp (cUblk d L Cl cS * r * nb j U) := by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.2 ((Complex.re_le_norm _).trans ?_)
    rw [uX]
    refine (norm_sum_le _ _).trans ?_
    refine (sum_le_sum fun b hb => H.up_le (mem_blockIdx_of_mem_blocks hb)).trans (le_of_eq ?_)
    rw [sum_const, nsmul_eq_mul, nb]; ring
  refine (mul_le_mul' (ENNReal.ofReal_le_ofReal hc) hb).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 2; ring

end BH

end

end Step2

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

theorem le_one_of_le_div {x r D : ℝ} (hx : 0 ≤ x) (hD : 0 < D) (hr : r ≤ 1 / D) (hxD : x ≤ D) :
    x * r ≤ 1 := by
  rcases le_or_gt 0 r with h0 | h0
  · calc x * r ≤ D * (1 / D) := mul_le_mul hxD hr h0 hD.le
      _ = 1 := by field_simp
  · nlinarith

set_option maxHeartbeats 1000000 in
/-- **The crude bound** on `K_{j+1}` on a ball (for the Cauchy estimates), with input field
scale `ℓ`, output field scale `ℓ'` and covariance field scale `ℓ_C`, `ℓ' + ℓ_C ≤ 2ℓ`. -/
theorem Knext2_crude_ts (d : ℕ) (hd : 1 ≤ d) : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∃ r₀ : ℝ, 0 < r₀ ∧
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓC C →
    ∀ (V W : Fam d L N) (K : Act d L N), InF j V → InF j W → (∀ b, ε (V b : Alg d L N) = 0) →
      InK2 j K → Fnorm j ℓ V ≤ ENNReal.ofReal r₀ → Fnorm j ℓ W ≤ ENNReal.ofReal r₀ →
      Knorm j ℓ A K ≤ ENNReal.ofReal r₀ →
      ∀ U : Finset (Lam d L N), IsConn (j + 1) U →
        wnorm (j + 1) ℓ' A U (Knext2 j C V W K U) ≤ ENNReal.ofReal 1 := by
  classical
  obtain ⟨Cl, hCl0, hloc⟩ := exists_Loc2sXY_bound d hd
  obtain ⟨c, hc⟩ := card_small_containing d
  obtain ⟨η, hη0, -, hcomb⟩ := comb2 d
  refine ⟨max (2 ^ (d + 3) + 8 * d + 1) ⌈pauliL0 d⌉₊, ?_⟩
  intro L _ hL
  have hL8 : 2 ^ (d + 3) + 8 * d < L := lt_of_lt_of_le (Nat.lt_succ_self _) (le_trans (le_max_left _ _) hL)
  have hLp : pauliL0 d ≤ L := (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hL)
  have hd8 : 2 ^ (d + 3) = 2 ^ d * 8 := by ring
  have hd4 : 2 ^ (d + 2) = 2 ^ d * 4 := by ring
  have hL2 : 2 ^ (d + 2) ≤ L := by
    rw [hd8] at hL8; rw [hd4]; generalize 2 ^ d = t at hL8 ⊢; omega
  have hL1 : 2 ^ d + 1 ≤ L := by
    rw [hd8] at hL8; generalize 2 ^ d = t at hL8 ⊢; omega
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set Q := Q1 d with hQdef
  have hQ : 1 ≤ Q := one_le_Q1 hd
  have hQ0 : 0 < Q := by linarith
  set M : ℕ := 2 ^ ((1 + c) * L ^ d) with hMdef
  have hM1 : 1 ≤ M := Nat.one_le_two_pow
  have hM1' : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  set P : ℝ := Q * (2 * M) with hPdef
  have hP1 : 1 ≤ P := by rw [hPdef]; nlinarith
  have hη' : 0 < 2 * η / (1 + 2 * η) := by positivity
  set A₀ : ℝ := Q * max 1 ((4 * P) ^ ((1 + 2 * η) / (2 * η))) with hA₀
  have hA₀1 : 1 ≤ A₀ := by
    rw [hA₀]; nlinarith [le_max_left (1 : ℝ) ((4 * P) ^ ((1 + 2 * η) / (2 * η)))]
  refine ⟨A₀, hA₀1, ?_⟩
  intro A hA
  have hA1 : 1 ≤ A := hA₀1.trans hA
  have hA0 : 0 < A := by linarith
  set Ar : ℝ := A / Q with hArdef
  have hArQ : Ar * Q = A := by rw [hArdef]; field_simp
  have hAr : max 1 ((4 * P) ^ ((1 + 2 * η) / (2 * η))) ≤ Ar := by
    rw [hArdef, le_div_iff₀ hQ0, mul_comm]; exact hA
  have hAr1 : 1 ≤ Ar := (le_max_left _ _).trans hAr
  have hAP : 4 * P ≤ Ar ^ (2 * η / (1 + 2 * η)) := by
    calc 4 * P = ((4 * P) ^ ((1 + 2 * η) / (2 * η))) ^ (2 * η / (1 + 2 * η)) := by
          rw [← Real.rpow_mul (by positivity)]
          rw [show (1 + 2 * η) / (2 * η) * (2 * η / (1 + 2 * η)) = 1 by field_simp]
          rw [Real.rpow_one]
      _ ≤ Ar ^ (2 * η / (1 + 2 * η)) :=
          Real.rpow_le_rpow (by positivity) ((le_max_right _ _).trans hAr) hη'.le
  set cS : ℝ := c + 1 with hcSdef
  have hcS1 : 1 ≤ cS := by rw [hcSdef]; linarith [Nat.cast_nonneg (α := ℝ) c]
  set cJ : ℝ := Q * cS * Cl with hcJdef
  have hcJ : 0 ≤ cJ := by positivity
  set cu := cUblk d L Cl cS
  set cw := cWblk d L Cl
  set ci := cIblk d L Cl cS
  have hcu : 0 ≤ cu := by
    have := Nat.cast_nonneg (α := ℝ) ((L + 2 ^ (d + 3) + 7) ^ d)
    simp only [cu, cUblk, cSblk, cNear]; positivity
  have hcw : 0 ≤ cw := by
    have := Nat.cast_nonneg (α := ℝ) ((L + 2 ^ (d + 3) + 7) ^ d)
    simp only [cw, cWblk, cSblk, cNear]; positivity
  have hci : 0 ≤ ci := by simp only [ci, cIblk]; positivity
  set Bc : ℝ := (1 + 2 ^ d * cJ) * A ^ 2 ^ d + (5 * Q + ci) * Ar with hBc
  have hBc0 : 0 ≤ Bc := by positivity
  set D : ℝ := 1 + 4 * cu + cw + 2 * (cu + ci) * (L : ℝ) ^ d + A ^ 2 ^ d + (5 * Q + ci) * Ar +
    (Ar * P) ^ 2 ^ d * Bc with hD
  have hD0 : 0 < D := by positivity
  refine ⟨1 / D, by positivity, ?_⟩
  intro N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC V W K hV hW hV0 hK hVr hWr hKr U hU
  set r := 1 / D with hrdef
  have hr0 : 0 ≤ r := by positivity
  have hrle : r ≤ 1 / D := le_rfl
  have item : ∀ x : ℝ, 0 ≤ x → x ≤ D → x * r ≤ 1 := fun x hx hxD =>
    le_one_of_le_div hx hD0 hrle hxD
  have t1 : 0 ≤ 4 * cu := by positivity
  have t2 : 0 ≤ 2 * (cu + ci) * (L : ℝ) ^ d := by positivity
  have t3 : 0 ≤ A ^ 2 ^ d := by positivity
  have t4 : 0 ≤ (5 * Q + ci) * Ar := by positivity
  have t5 : 0 ≤ (Ar * P) ^ 2 ^ d * Bc := by positivity
  have hr1 : r ≤ 1 := by
    simpa using item 1 zero_le_one (by rw [hD]; linarith)
  have hj : j < N := by omega
  have H : BH j ℓ ℓ' ℓC C V W K A r Cl cS :=
    { hd := hd, hLp := hLp, hL8 := hL8, hjN := hjN, hℓ := hℓ, hℓ' := hℓ', hℓC := hℓC,
      hsum := hsum, hC := hC, hV := hV, hW := hW,
      hV0 := hV0, hK := hK, hA := hA1, hr := hr0, hr1 := hr1
      hVr := fun b hb => (le_iSup₂ (f := fun b (_ : b ∈ blockIdx (L := L) (N := N) j) =>
        Tj d (L : ℝ) j ℓ (V b : Alg d L N)) b hb).trans hVr
      hWr := fun b hb => (le_iSup₂ (f := fun b (_ : b ∈ blockIdx (L := L) (N := N) j) =>
        Tj d (L : ℝ) j ℓ (W b : Alg d L N)) b hb).trans hWr
      hKr := hKr, hCl := hCl0
      hloc := fun k hk ℓ₀ hℓ₀ X Y hX hYX F hF => hloc L hL8 N k hk X Y hX hYX F hF ℓ₀ hℓ₀
      hcS := hcS1
      hcount := fun b hb => by
        have h1 : ((smallSets (d := d) (L := L) (N := N) j).filter
            (fun X => blockSet j b ⊆ X)).card ≤ c := by convert hc L N j b hb
        have h2 := Nat.cast_le (α := ℝ) |>.2 h1
        linarith }
  have hu : cu * r ≤ 1 / 4 := by
    have := item (4 * cu) (by positivity) (by rw [hD]; linarith)
    linarith
  have hw : cw * r ≤ 1 := item cw hcw (by rw [hD]; linarith)
  have hpr : (cu + ci) * r * (L : ℝ) ^ d ≤ 1 / 2 := by
    have := item (2 * (cu + ci) * (L : ℝ) ^ d) (by positivity) (by rw [hD]; linarith)
    nlinarith
  have hκ1 : r * A ^ 2 ^ d ≤ 1 := by
    have := item (A ^ 2 ^ d) t3 (by rw [hD]; linarith)
    linarith [mul_comm r (A ^ 2 ^ d)]
  have hδ1 : (5 * Q + ci) * r * Ar ≤ 1 := by
    have := item ((5 * Q + ci) * Ar) t4 (by rw [hD]; linarith)
    have e : (5 * Q + ci) * r * Ar = (5 * Q + ci) * Ar * r := by ring
    linarith
  have hDβ : (Ar * P) ^ 2 ^ d * ((1 + 2 ^ d * cJ) * (r * A ^ 2 ^ d) + (5 * Q + ci) * r * Ar) ≤ 1 := by
    have e : (Ar * P) ^ 2 ^ d * ((1 + 2 ^ d * cJ) * (r * A ^ 2 ^ d) + (5 * Q + ci) * r * Ar) =
        ((Ar * P) ^ 2 ^ d * Bc) * r := by rw [hBc]; ring
    rw [e]; exact item _ (by positivity) (by rw [hD]; linarith)
  have hρ : Q / A = Ar⁻¹ := by rw [hArdef, inv_div]
  have G : GH j (Ib V W) (Ip j C V W K) K (J2 j K) ((L : ℝ) ^ (j + 1)) ℓ' ℓC (Q / A)
      (r * A ^ 2 ^ d) ((5 * Q + ci) * r * Ar) cJ :=
    { hh' := H.hh', hℓ' := hℓ', hρ := by positivity
      hρ1 := by rw [div_le_one hA0]; exact (le_mul_of_one_le_left hQ0.le hAr1).trans hArQ.le
      hκ₀ := by positivity, hκ₀1 := hκ1, hδ₁ := by positivity, hδ₁1 := hδ1, hcJ := hcJ
      hK := fun W hW => H.thetaK_le hW
      hdI := fun b hb => (H.gdI_le hu hw hb).trans (ENNReal.ofReal_le_ofReal (le_of_eq (by
        rw [hArdef]; field_simp; show _ = r * (5 * Q1 d + cIblk d L Cl cS); ring)))
      hJ := fun b hb X => (H.thetaJ_le hb X).trans (ENNReal.ofReal_le_ofReal (by
        have e : cJ * (r * A ^ 2 ^ d) * (Q / A) ^ 2 ^ d = Q * (cS * (Cl * r)) * Q ^ 2 ^ d := by
          rw [hcJdef, div_pow]; field_simp
        rw [e]
        have : 1 ≤ Q ^ 2 ^ d := one_le_pow₀ hQ
        have : 0 ≤ Q * (cS * (Cl * r)) := by positivity
        nlinarith))
      hJs := fun b X hX => J2_of_not_small j K b X hX }
  have hUj : IsPolymer j U := IsPolymer.of_succ hU.1
  have key := G.gKnext_le C (Complex.exp (uX j C V W K U)) hAr1 hρ hQ hη0.le
    (fun F => ECC_succ_le2 hℓ' hℓC hC F)
    (fun g _ => by
      refine (H.pref_le hu hw U _).trans (ENNReal.ofReal_le_ofReal ?_)
      have hnb : (nb j U : ℝ) ≤ (L : ℝ) ^ d * nb (j + 1) U := by
        exact_mod_cast nb_le_of_succ hU.1
      have hx : (cu + ci) * r * nb j U ≤ (nb (j + 1) U : ℝ) * (1 / 2) := by
        have : (cu + ci) * r * nb j U ≤ (cu + ci) * r * ((L : ℝ) ^ d * nb (j + 1) U) := by
          gcongr
        nlinarith [mul_le_mul_of_nonneg_right hpr (Nat.cast_nonneg (α := ℝ) (nb (j + 1) U))]
      have he : Real.exp (1 / 2) ≤ 2 := by
        have := (abs_le.1 (Real.abs_exp_sub_one_le (x := 1 / 2) (by norm_num))).2
        norm_num at this ⊢; linarith
      calc Real.exp ((cu + ci) * r * nb j U) ≤ Real.exp ((nb (j + 1) U : ℝ) * (1 / 2)) :=
            Real.exp_le_exp.2 hx
        _ = Real.exp (1 / 2) ^ nb (j + 1) U := Real.exp_nat_mul _ _
        _ ≤ 2 ^ nb (j + 1) U := pow_le_pow_left₀ (Real.exp_pos _).le he _)
    (by
      refine (card_Gset_le (fun b hb => hc L N j b hb) hUj).trans ?_
      rw [hMdef, ← pow_mul]
      exact Nat.pow_le_pow_right (by norm_num) (by
        rw [mul_assoc]; exact Nat.mul_le_mul_left _ (nb_le_of_succ hU.1)))
    (fun g hg => nU_bound (fun X hX => (hcomb L hL1 N j X hj hX).1)
      (fun b hb => (isSmall_clo_nbhd hd hL2 hj b hb).2.2) hη0.le hg)
    hPdef hM1 hAP hDβ
  rw [hArQ] at key
  refine le_trans ?_ key
  unfold wnorm
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (pow_le_pow_right₀ hA1 (Nat.sub_le _ _))) le_rfl


/-- **The crude bound** on `K_{j+1}` on a ball, at a single field scale. -/
theorem Knext2_crude (d : ℕ) (hd : 1 ≤ d) : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∃ r₀ : ℝ, 0 < r₀ ∧
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ : ℝ, 0 < ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓ C →
    ∀ (V W : Fam d L N) (K : Act d L N), InF j V → InF j W → (∀ b, ε (V b : Alg d L N) = 0) →
      InK2 j K → Fnorm j ℓ V ≤ ENNReal.ofReal r₀ → Fnorm j ℓ W ≤ ENNReal.ofReal r₀ →
      Knorm j ℓ A K ≤ ENNReal.ofReal r₀ →
      ∀ U : Finset (Lam d L N), IsConn (j + 1) U →
        wnorm (j + 1) ℓ A U (Knext2 j C V W K U) ≤ ENNReal.ofReal 1 := by
  obtain ⟨L₀, h⟩ := Knext2_crude_ts d hd
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨A₀, hA₀, h'⟩ := h L hL
  refine ⟨A₀, hA₀, fun A hA => ?_⟩
  obtain ⟨r₀, hr₀, h''⟩ := h' A hA
  exact ⟨r₀, hr₀, fun N j hj ℓ hℓ C hC => h'' N j hj ℓ ℓ ℓ hℓ hℓ hℓ (by linarith) C hC⟩

end

end Step2
