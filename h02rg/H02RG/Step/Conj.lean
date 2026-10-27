import Step.Coupling
import Grassmann.Conj

/-!
# Complex conjugation and the renormalisation group map

For real covariances `C`, the renormalisation group map commutes with complex conjugation:
if `V̄` has the conjugate coupling constants and `K̄(X) = conj K(X)`, then
`(u_{j+1}, V_{j+1})(V̄, K̄) = conj (u_{j+1}, V_{j+1})(V, K)` (`uVnext_conj`) and
`K_{j+1}(V̄, K̄) = conj K_{j+1}(V, K)` (`Knext_conj`).  Conjugation preserves `𝒦^∅_j`
(`InK.conj`) and the norms `‖V‖_j`, `‖K‖_j` (`Vnorm_conj`, `Knorm_conjA`).

The proof is by direct computation through the definitions: all ingredients (`θ`, `𝔼_C`, the
localisation `Loc_{X,Y}`, whose matrix `A_X` has real entries, the exponential, the polymer
combinatorics) are real.
-/

namespace Step

noncomputable section

open Finset Grassmann Loc FRD

local notation "cj" => starRingEnd ℂ

@[simp] theorem cj_two : cj (2 : ℂ) = 2 := map_ofNat _ 2

/-! ### Coupling constants -/

/-- The conjugate coupling constants. -/
def _root_.Loc.Vcoup.conj (V : Vcoup) : Vcoup := ⟨cj V.z, cj V.y, cj V.a, cj V.b⟩

@[simp] theorem _root_.Loc.Vcoup.conj_z (V : Vcoup) : V.conj.z = cj V.z := rfl
@[simp] theorem _root_.Loc.Vcoup.conj_y (V : Vcoup) : V.conj.y = cj V.y := rfl
@[simp] theorem _root_.Loc.Vcoup.conj_a (V : Vcoup) : V.conj.a = cj V.a := rfl
@[simp] theorem _root_.Loc.Vcoup.conj_b (V : Vcoup) : V.conj.b = cj V.b := rfl

/-! ### The even subalgebra -/

section Even

variable {Λ : Type*} [DecidableEq Λ]

theorem conjN_mem_Ev {x : N Λ} (hx : x ∈ Ev Λ) : conjN x ∈ Ev Λ :=
  mem_Ev.2 (by rw [← conjN_inv', mem_Ev.1 hx])

/-- Complex conjugation on even elements. -/
def conjE : EvR Λ →+* EvR Λ :=
  (conjN.comp (Ev Λ).val.toRingHom).codRestrict (Ev Λ) fun x => conjN_mem_Ev x.2

@[simp] theorem coe_conjE (x : EvR Λ) : (conjE x : N Λ) = conjN (x : N Λ) := rfl

theorem conjE_conjE (x : EvR Λ) : conjE (conjE x) = x := Subtype.ext (by simp [conjN_conjN])

theorem conjE_smul (c : ℂ) (x : EvR Λ) : conjE (c • x) = cj c • conjE x :=
  Subtype.ext (by simp [conjN_smul])

theorem conjE_gexp (x : EvR Λ) : conjE (gexp x) = gexp (conjE x) := by
  have hc : nilpotencyClass (conjE x) = nilpotencyClass x := by
    unfold nilpotencyClass
    congr 1
    ext k
    simp only [Set.mem_setOf_eq, ← map_pow]
    constructor
    · intro h; simpa [conjE_conjE] using congrArg conjE h
    · intro h; rw [h, map_zero]
  simp only [gexp, IsNilpotent.exp, hc, map_sum, map_rat_smul, map_pow]

theorem conjE_mapE {Λ' : Type*} [DecidableEq Λ'] {f : V Λ →ₗ[ℂ] V Λ'} (hf : RealLin f)
    (x : EvR Λ) : conjE (mapE f x) = mapE f (conjE x) :=
  Subtype.ext (by simp [conjN_map hf])

theorem conjE_thetaE (x : EvR Λ) : conjE (thetaE x) = thetaE (conjE x) :=
  conjE_mapE realLin_thetaV x

theorem conjE_inclE (x : EvR Λ) : conjE (inclE x) = inclE (conjE x) :=
  conjE_mapE realLin_inlV x

theorem conjE_ECE [Fintype Λ] (C : Matrix Λ Λ ℝ) (x : EvR (Λ ⊕ Λ)) :
    conjE (ECE C x) = ECE C (conjE x) :=
  Subtype.ext (by simp [conjN_EC])

end Even

variable {d L N : ℕ} [NeZero L]

/-! ### Local polynomials -/

@[simp] theorem conjN_grad (e : Dir d) (x : Lam d L N) : conjN (grad e x) = grad e x := by
  simp [grad]

@[simp] theorem conjN_gradbar (e : Dir d) (x : Lam d L N) : conjN (gradbar e x) = gradbar e x := by
  simp [gradbar]

@[simp] theorem conjN_gradSq (x : Lam d L N) : conjN (gradSq x) = gradSq x := by
  simp [gradSq, conjN_smul, map_sum]

@[simp] theorem conjN_lapPsi (x : Lam d L N) : conjN (lapPsi x) = lapPsi x := by
  simp [lapPsi, conjN_smul, map_sum]

@[simp] theorem conjN_lapPsibar (x : Lam d L N) : conjN (lapPsibar x) = lapPsibar x := by
  simp [lapPsibar, conjN_smul, map_sum]

theorem conjN_eval (V : Vcoup) (X : Finset (Lam d L N)) :
    conjN (V.eval X) = V.conj.eval X := by
  simp [Vcoup.eval, conjN_smul, map_sum, map_div₀]

theorem conjE_VE (V : Vcoup) (X : Finset (Lam d L N)) : conjE (VE V X) = VE V.conj X :=
  Subtype.ext (conjN_eval V X)

@[simp] theorem conjN_monoAt (M : Mono d) (x : Lam d L N) : conjN (monoAt M x) = monoAt M x := by
  rw [monoAt, map_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun p _ => ?_
  simp only [Function.comp_apply]
  rw [conjN_ofReal_smul, map_mul, conjN_psi, conjN_psibar]

@[simp] theorem conjN_monoSet (M : Mono d) (X : Finset (Lam d L N)) :
    conjN (monoSet M X) = monoSet M X := by
  simp [monoSet, map_sum]

theorem mu_conjN (b : Lam d L N) (β : Mono d) (F : Alg d L N) :
    mu b β (conjN F) = cj (mu b β F) := by
  simp [mu, cf2, map_sum]

theorem Amat_conj (X : Finset (Lam d L N)) (M β : Mono d) : cj (Loc.Amat X M β) = Loc.Amat X M β := by
  rw [Loc.Amat, ← mu_conjN, conjN_monoSet]

theorem inv_conj_of_real {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    (hA : ∀ i j, cj (A i j) = A i j) (i j : n) : cj (A⁻¹ i j) = A⁻¹ i j := by
  have hH : A.conjTranspose = A.transpose := by
    ext a b; simp [Matrix.conjTranspose_apply, hA]
  have h := Matrix.conjTranspose_nonsing_inv A
  rw [hH, ← Matrix.transpose_nonsing_inv] at h
  have := congrFun (congrFun h j) i
  simpa [Matrix.conjTranspose_apply] using this

theorem locCoef_conjN (X : Finset (Lam d L N)) (F : Alg d L N) (M : Mono d) :
    locCoef X (conjN F) M = cj (locCoef X F M) := by
  simp only [locCoef, Matrix.vecMul, dotProduct, map_sum, map_mul, mu_conjN]
  refine sum_congr rfl fun β _ => ?_
  rw [inv_conj_of_real _ (Amat_conj X)]

theorem conjN_LocXY (X Y : Finset (Lam d L N)) (F : Alg d L N) :
    conjN (LocXY X Y F) = LocXY X Y (conjN F) := by
  simp [LocXY, conjN_smul, map_sum, locCoef_conjN, ε_conjN, map_div₀]

theorem conjE_LocE (X Y : Finset (Lam d L N)) (F : EvR (Lam d L N)) :
    conjE (LocE X Y F) = LocE X Y (conjE F) :=
  Subtype.ext (conjN_LocXY X Y F)

/-! ### Symmetries and the space `𝒦^∅_j` -/

theorem realLin_JV : RealLin (JV : V (Lam d L N) →ₗ[ℂ] V (Lam d L N)) := fun v => by
  ext a; by_cases h : a.2 = -1 <;> simp [JV, h]

theorem conjN_Jsym (F : Alg d L N) : conjN (Jsym F) = Jsym (conjN F) := conjN_map realLin_JV F

theorem realLin_autV (E : Lam d L N ≃ Lam d L N) :
    RealLin (autV E : V (Lam d L N) →ₗ[ℂ] V (Lam d L N)) := fun _ => rfl

theorem conjN_autAlg (E : Lam d L N ≃ Lam d L N) (F : Alg d L N) :
    conjN (autAlg E F) = autAlg E (conjN F) := conjN_map (realLin_autV E) F

theorem isSym_conjN {F : Alg d L N} (hF : IsSym F) : IsSym (conjN F) := by
  intro n z hz
  rw [coeff_conjN, hF n z hz, map_zero]

/-- The conjugate activity `K̄(X) = conj K(X)`. -/
def conjA (K : Act d L N) : Act d L N := fun X => conjE (K X)

@[simp] theorem conjA_apply (K : Act d L N) (X : Finset (Lam d L N)) :
    conjA K X = conjE (K X) := rfl

@[simp] theorem conjA_conjA (K : Act d L N) : conjA (conjA K) = K := by
  funext X; simp [conjE_conjE]

theorem conjA_add (K K' : Act d L N) : conjA (K + K') = conjA K + conjA K' := by
  funext X; simp

theorem conjA_smul (c : ℂ) (K : Act d L N) : conjA (c • K) = cj c • conjA K := by
  funext X; simp [conjE_smul]

@[simp] theorem conjA_zero : conjA (0 : Act d L N) = 0 := by funext X; simp

theorem InK.conj {j : ℕ} {K : Act d L N} (hK : InK j K) : InK j (conjA K) where
  loc X hX := conjN_mem_NX (hK.loc X hX)
  sym X hX := isSym_conjN (hK.sym X hX)
  jinv X hX := by
    simp only [conjA_apply, coe_conjE]
    rw [← conjN_Jsym, hK.jinv X hX]
  aut T hT hTb X hX := by
    simp only [conjA_apply, coe_conjE]
    rw [← conjN_autAlg, hK.aut T hT hTb X hX]

/-! ### Norms -/

theorem Knorm_conjA (j : ℕ) (ℓ A : ℝ) (K : Act d L N) :
    Knorm j ℓ A (conjA K) = Knorm j ℓ A K := by
  simp only [Knorm, conjA_apply, coe_conjE, Tj_conjN]

/-! ### The renormalisation group map -/

section Map

variable (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (V : Vcoup) (K : Act d L N)

theorem Kext_conjA (X : Finset (Lam d L N)) : Kext j (conjA K) X = conjE (Kext j K X) := by
  simp [Kext, map_prod]

theorem Qb_conjA (b : Fin d → ℕ) : Qb j (conjA K) b = conjE (Qb j K b) := by
  unfold Qb
  split_ifs
  · simp [map_sum, conjE_LocE]
  · simp

theorem Jb_conjA (b : Fin d → ℕ) (X : Finset (Lam d L N)) :
    Jb j (conjA K) b X = conjE (Jb j K b X) := by
  unfold Jb
  split_ifs
  · simp [map_sum, map_neg, conjE_LocE]
  · simp [conjE_LocE]
  · simp

/-- Complex conjugation of `(u, V)`. -/
def conjUV (p : ℂ × Vcoup) : ℂ × Vcoup := (cj p.1, p.2.conj)

theorem coupOf_conjN (hd : 1 ≤ d) (hLN : 3 ≤ L ^ N) {B : Finset (Lam d L N)} (hB : B.Nonempty)
    (hBp : Patch B) (F : Alg d L N) : coupOf (conjN F) B = conjUV (coupOf F B) := by
  by_cases h : F ∈ VXspace B
  · have h0 := coupOf_spec h
    have hc : conjN F = (cj (coupOf F B).1 * B.card) • (1 : Alg d L N) +
        (coupOf F B).2.conj.eval B := by
      conv_lhs => rw [h0]
      rw [map_add, conjN_smul, map_one, conjN_eval, map_mul, map_natCast]
    have h1 := coupOf_spec (⟨_, _, hc⟩ : conjN F ∈ VXspace B)
    obtain ⟨e1, e2⟩ := coup_injective hd hLN hB hBp (h1.symm.trans hc)
    exact Prod.ext e1 e2
  · have h' : conjN F ∉ VXspace B := fun hc => h <| by
      obtain ⟨u, W, hW⟩ := hc
      refine ⟨cj u, W.conj, ?_⟩
      have := congrArg conjN hW
      rw [conjN_conjN, map_add, conjN_smul, map_one, conjN_eval, map_mul, map_natCast] at this
      exact this
    have hn : ¬ ∃ (u : ℂ) (V' : Vcoup), F = (u * B.card) • (1 : Alg d L N) + V'.eval B := h
    have hn' : ¬ ∃ (u : ℂ) (V' : Vcoup),
        conjN F = (u * B.card) • (1 : Alg d L N) + V'.eval B := h'
    unfold coupOf
    rw [dif_neg hn, dif_neg hn']
    simp [conjUV, Vcoup.conj]

/-- **`(u_{j+1}, V_{j+1})` commutes with complex conjugation** (for real `C`). -/
theorem uVnext_conj (hd : 1 ≤ d) (hL : 3 ≤ L) (hj : j < N) :
    uVnext j C V.conj (conjA K) = conjUV (uVnext j C V K) := by
  have hLN : 3 ≤ L ^ N := hL.trans (Nat.le_self_pow (by omega) L)
  unfold uVnext
  rw [← coupOf_conjN hd hLN (mem_blockIdx.1 (zero_mem_blockIdx j)) (patch_blockSet hj hL 0),
    conjN_EC, conjN_theta]
  simp only [map_sub, conjN_eval, Qb_conjA, coe_conjE]

variable {j C V K}

section Hu

variable (hu : uVnext j C V.conj (conjA K) = conjUV (uVnext j C V K))
include hu

theorem Inext_conj (b : Fin d → ℕ) :
    Inext j C V.conj (conjA K) b = conjE (Inext j C V K b) := by
  simp only [Inext, hu, conjUV, conjE_smul, conjE_gexp, map_neg, conjE_VE, ← Complex.exp_conj,
    map_mul, map_natCast]

theorem InextPow_conj (X : Finset (Lam d L N)) :
    InextPow j C V.conj (conjA K) X = conjE (InextPow j C V K X) := by
  simp only [InextPow, map_prod, Inext_conj hu]

theorem dI_conj (b : Fin d → ℕ) : dI j C V.conj (conjA K) b = conjE (dI j C V K b) := by
  simp only [dI, map_sub, conjE_thetaE, conjE_inclE, conjE_gexp, map_neg, conjE_VE,
    Inext_conj hu]

theorem dIPow_conj (X : Finset (Lam d L N)) :
    dIPow j C V.conj (conjA K) X = conjE (dIPow j C V K X) := by
  simp only [dIPow, map_prod, dI_conj hu]

theorem Ktil_conj (W : Finset (Lam d L N)) :
    Ktil j C V.conj (conjA K) W = conjE (Ktil j C V K W) := by
  simp only [Ktil, map_sum, map_mul, conjE_thetaE, Kext_conjA, dIPow_conj hu]

theorem KchkC_conj (W : Finset (Lam d L N)) :
    KchkC j C V.conj (conjA K) W = conjE (KchkC j C V K W) := by
  simp only [KchkC, map_sub, map_sum, conjE_thetaE, Jb_conjA, Ktil_conj hu]

theorem Kchk_conj (X : Finset (Lam d L N)) :
    Kchk j C V.conj (conjA K) X = conjE (Kchk j C V K X) := by
  simp only [Kchk, map_prod, KchkC_conj hu]

theorem Knext_conj' (U : Finset (Lam d L N)) :
    Knext j C V.conj (conjA K) U = conjE (Knext j C V K U) := by
  simp only [Knext, hu, conjUV, conjE_smul, ← Complex.exp_conj, map_mul, map_natCast, map_sum,
    InextPow_conj hu, conjE_ECE, Kchk_conj hu, map_prod, conjE_thetaE, Jb_conjA]

end Hu

/-- **`K_{j+1}` commutes with complex conjugation** (for real `C`). -/
theorem Knext_conj (hd : 1 ≤ d) (hL : 3 ≤ L) (hj : j < N) (U : Finset (Lam d L N)) :
    Knext j C V.conj (conjA K) U = conjE (Knext j C V K U) :=
  Knext_conj' (uVnext_conj j C V K hd hL hj) U

theorem Knext_conjA (hd : 1 ≤ d) (hL : 3 ≤ L) (hj : j < N) :
    Knext j C V.conj (conjA K) = conjA (Knext j C V K) :=
  funext fun U => Knext_conj hd hL hj U

end Map

end

end Step
