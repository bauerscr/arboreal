import Step2.Map.Defs
import Loc.Pauli
import Step.ExpNorm

/-!
# Norm estimates for the change of scale `j → j+1` at a fixed field scale

In `d = 2` the field scale is the same at scales `j` and `j+1`. The doubling map `θ` costs a
factor `2` in the field scale (`e:theta-bd`), which is compensated per `j`-block by
Lemma `lem:pauli`:

* `Tj_succ_two_le`: `‖F‖_{T_{j+1}(2ℓ)} ≤ q^{|𝓑_j(Y)|} ‖F‖_{T_j(ℓ)}` for `F ∈ 𝒩(Y)`, with
  `q = C_*^{(p+1)^d}` (`pq`);
* `theta_succ_le`, `EthE_succ_le`: the same for `θ F` and `𝔼_C θ F` in the `T_{j+1}(ℓ)` norm
  (on the doubled algebra, resp. for a Gram-admissible `C`);
* `FCE_succ_le`: `‖F_C(𝔼θA, 𝔼θB)‖_{T_{j+1}(ℓ)} ≤ 2 q^{|𝓑(Y)|+|𝓑(Y')|} ‖A‖_{T_j(ℓ)} ‖B‖_{T_j(ℓ)}`.

`GoodCov2` collects the hypotheses on the covariance `C = C'_{j+1}`: a Gram representation with
the Gram bound at scale `j+1` and field scale `ℓ`, and range `< L^{j+1}/2`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

/-- The per-block constant `q = C_*^{(p+1)^d}`. -/
def pq (d : ℕ) : ℝ := pauliC d ^ ((pPhi d + 1) ^ d)

theorem one_le_cChi {d : ℕ} (hd : 1 ≤ d) : 1 ≤ cChi d (pPhi d) := by
  unfold cChi
  have h1 : (1 : ℝ) ≤ 2 ^ pPhi d := one_le_pow₀ (by norm_num)
  have h2 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h3 : (1 : ℝ) ≤ 3 * (pPhi d : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) (pPhi d); linarith
  calc (1 : ℝ) = 1 * 1 * 1 := by ring
    _ ≤ 2 ^ pPhi d * d * (3 * (pPhi d : ℝ) + 1) := by gcongr

theorem one_le_pauliC {d : ℕ} (hd : 1 ≤ d) : 1 ≤ pauliC d := by
  unfold pauliC
  have h1 : (1 : ℝ) ≤ 2 ^ pPhi d := one_le_pow₀ (by norm_num)
  have h2 := one_le_cChi hd
  have : (1 : ℝ) ≤ 4 * (2 ^ pPhi d * cChi d (pPhi d)) := by nlinarith
  exact one_le_pow₀ this

theorem one_le_pq {d : ℕ} (hd : 1 ≤ d) : 1 ≤ pq d := one_le_pow₀ (one_le_pauliC hd)

theorem cells_eq_blocks (j : ℕ) (Y : Finset (Lam d L N)) :
    cells (L ^ j) (↑Y : Set (Lam d L N)) = blocks j Y := by
  ext c
  simp only [cells, blocks, mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ((@mem_filter _ (fun x => x ∈ (↑Y : Set (Lam d L N)))
      (fun _ => Classical.propDecidable _) _ _).1 ha).2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, (@mem_filter _ (fun x => x ∈ (↑Y : Set (Lam d L N)))
      (fun _ => Classical.propDecidable _) _ _).2 ⟨mem_univ _, ha⟩, rfl⟩

/-- `lem:pauli` with the count of `j`-blocks. -/
theorem Tj_succ_two_le (hd : 1 ≤ d) (hL : pauliL0 d ≤ L) {j : ℕ} (hj : j < N)
    {Y : Finset (Lam d L N)} {F : Alg d L N} (hF : F ∈ NX (↑Y : Set (Lam d L N))) {ℓ : ℝ}
    (hℓ : 0 < ℓ) :
    Tj d (L : ℝ) (j + 1) (2 * ℓ) F ≤ ENNReal.ofReal (pq d ^ nb j Y) * Tj d (L : ℝ) j ℓ F := by
  refine (pauli hd hL hj rfl hF hℓ).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
  have hR0 : 0 < L ^ j := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
  have hn : L ^ N = L ^ j * L ^ (N - j) := by rw [← pow_add, Nat.add_sub_cancel' hj.le]
  have hc := card_nearB_le (d := d) (n := L ^ N) (p := pPhi d) hR0 hn (↑Y : Set (Lam d L N))
  rw [cells_eq_blocks] at hc
  rw [pq, ← pow_mul]
  exact pow_le_pow_right₀ (one_le_pauliC hd) hc

/-- `‖θ F‖_{T_{j+1}(ℓ)} ≤ q^{|𝓑(Y)|} ‖F‖_{T_j(ℓ)}` on the doubled algebra. -/
theorem theta_succ_le (hd : 1 ≤ d) (hL : pauliL0 d ≤ L) {j : ℕ} (hj : j < N)
    {Y : Finset (Lam d L N)} {F : Alg d L N} (hF : F ∈ NX (↑Y : Set (Lam d L N))) {ℓ : ℝ}
    (hℓ : 0 < ℓ) :
    tNorm (Dir d) (pPhi d) ((L : ℝ) ^ (j + 1)) ℓ (theta F) ≤
      ENNReal.ofReal (pq d ^ nb j Y) * Tj d (L : ℝ) j ℓ F := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  exact (tNorm_theta_le (by positivity) hℓ F).trans (Tj_succ_two_le hd hL hj hF hℓ)

/-- The hypotheses on the covariance `C = C'_{j+1}`. -/
structure GoodCov2 (j : ℕ) (ℓ : ℝ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) : Prop where
  gram : ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (Fv Gv : Lam d L N → H), IsGram C Fv Gv ∧
      GramBound (Dir d) (pPhi d) ((L : ℝ) ^ (j + 1)) ℓ Fv Gv
  range : j + 1 < N → ∀ x y, (L : ℝ) ^ (j + 1) / 2 ≤ supNorm (x - y) → C x y = 0

/-- `e:E-contract2` at scale `j + 1`. -/
theorem ECC_succ_le {j : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {C : Matrix (Lam d L N) (Lam d L N) ℂ}
    (hC : GoodCov2 j ℓ C) (F : Grassmann.N (Lam d L N ⊕ Lam d L N)) :
    Tj d (L : ℝ) (j + 1) ℓ (ECC C F) ≤ tNorm (Dir d) (pPhi d) ((L : ℝ) ^ (j + 1)) ℓ F := by
  obtain ⟨H, _, _, Fv, Gv, hG, hB⟩ := hC.gram
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  exact tNorm_ECC_le (by positivity) hℓ hG hB F

/-- `‖𝔼_C θ F‖_{T_{j+1}(ℓ)} ≤ q^{|𝓑(Y)|} ‖F‖_{T_j(ℓ)}`. -/
theorem EthE_succ_le (hd : 1 ≤ d) (hL : pauliL0 d ≤ L) {j : ℕ} (hj : j < N) {ℓ : ℝ}
    (hℓ : 0 < ℓ) {C : Matrix (Lam d L N) (Lam d L N) ℂ} (hC : GoodCov2 j ℓ C)
    {Y : Finset (Lam d L N)} {F : Alg d L N} (hF : F ∈ NX (↑Y : Set (Lam d L N))) :
    Tj d (L : ℝ) (j + 1) ℓ (ECC C (theta F)) ≤
      ENNReal.ofReal (pq d ^ nb j Y) * Tj d (L : ℝ) j ℓ F :=
  (ECC_succ_le hℓ hC _).trans (theta_succ_le hd hL hj hF hℓ)

/-- `‖𝔼_C θ F‖_{T_{j+1}(ℓ)} ≤ ‖F‖_{T_{j+1}(2ℓ)}`. -/
theorem EthE_succ_le' {j : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {C : Matrix (Lam d L N) (Lam d L N) ℂ}
    (hC : GoodCov2 j ℓ C) (F : Alg d L N) :
    Tj d (L : ℝ) (j + 1) ℓ (ECC C (theta F)) ≤ Tj d (L : ℝ) (j + 1) (2 * ℓ) F := by
  obtain ⟨H, _, _, Fv, Gv, hG, hB⟩ := hC.gram
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  exact tNorm_ECC_theta_le (by positivity) hℓ hG hB F

/-- The truncated expectation: `‖F_C(𝔼θA, 𝔼θB)‖_{T_{j+1}(ℓ)} ≤ 2 ‖A‖_{T_{j+1}(2ℓ)}
‖B‖_{T_{j+1}(2ℓ)}`. -/
theorem FC_succ_le {j : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {C : Matrix (Lam d L N) (Lam d L N) ℂ}
    (hC : GoodCov2 j ℓ C) (A B : Alg d L N) :
    Tj d (L : ℝ) (j + 1) ℓ (FC C (ECC C (theta A)) (ECC C (theta B))) ≤
      2 * (Tj d (L : ℝ) (j + 1) (2 * ℓ) A * Tj d (L : ℝ) (j + 1) (2 * ℓ) B) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hh : (0 : ℝ) < (L : ℝ) ^ (j + 1) := by positivity
  rw [FC_ECC_theta]
  refine (tNorm_sub_le _ _).trans ?_
  have h1 := (EthE_succ_le' hℓ hC (A * B)).trans (tNorm_mul_le hh (by positivity) A B)
  have h2 := (tNorm_mul_le hh hℓ (ECC C (theta A)) (ECC C (theta B))).trans
    (mul_le_mul' (EthE_succ_le' hℓ hC A) (EthE_succ_le' hℓ hC B))
  calc _ ≤ Tj d (L : ℝ) (j + 1) (2 * ℓ) A * Tj d (L : ℝ) (j + 1) (2 * ℓ) B +
        Tj d (L : ℝ) (j + 1) (2 * ℓ) A * Tj d (L : ℝ) (j + 1) (2 * ℓ) B := add_le_add h1 h2
    _ = _ := by ring

end

end Step2
