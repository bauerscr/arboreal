import Step2.Coup.BubbleX
import Step.Conj

/-!
# Reality of the second-order step (`h02uv-outline.tex`, Section `sec:reduction`, (O2))

For a real covariance (`cj C(x,y) = C(x,y)`), the `Step2` map commutes with complex conjugation:
`K_{j+1}(V̄, 𝒲̄, K̄) = conj K_{j+1}(V, 𝒲, K)` (`Kplus_conj`), and likewise for `𝒲_{j+1}`
(`Wnext2_conj`) and `V_{j+1}` (`Vnext2_conj`). For real couplings the coupling polynomials are
real (`conjE_Vcoup`), and the coupling vector of a real polynomial is real (`cvec4_conjN`).
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

local notation "cj" => starRingEnd ℂ

section Gen

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ] {C : Matrix Λ Λ ℂ}
  (hC : ∀ x y, cj (C x y) = C x y)

include hC in
theorem conjN_LopC (F : N Λ) : conjN (LopC C F) = LopC C (conjN F) := by
  simp only [LopC_apply, map_sum, conjN_smul, hC, conjN_D]

include hC in
theorem conjN_LζC (F : N (Λ ⊕ Λ)) : conjN (LζC C F) = LζC C (conjN F) := by
  simp only [LζC_apply, map_sum, conjN_smul, hC, conjN_D]

include hC in
theorem conjN_expLC (F : N Λ) : conjN (expLC C F) = expLC C (conjN F) :=
  exp_apply_comm (LopC_isNilpotent C) (LopC_isNilpotent C) conjN.toAddMonoidHom
    (fun m => conjN_LopC hC m) F

include hC in
theorem conjN_ECC (F : N (Λ ⊕ Λ)) : conjN (ECC C F) = ECC C (conjN F) := by
  rw [ECC, LinearMap.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    AlgHom.toLinearMap_apply, conjN_proj]
  congr 1
  exact exp_apply_comm (LζC_isNilpotent C) (LζC_isNilpotent C) conjN.toAddMonoidHom
    (fun m => conjN_LζC hC m) F

include hC in
theorem conjE_ECCE (x : EvR (Λ ⊕ Λ)) : conjE (ECCE C x) = ECCE C (conjE x) :=
  Subtype.ext (conjN_ECC hC _)

include hC in
theorem conjE_EthE (x : EvR Λ) : conjE (EthE C x) = EthE C (conjE x) := by
  rw [EthE, conjE_ECCE hC, conjE_thetaE]; rfl

include hC in
theorem conjE_FCE (x y : EvR Λ) : conjE (FCE C x y) = FCE C (conjE x) (conjE y) := by
  have hC' : ∀ a b, cj ((-C) a b) = (-C) a b := fun a b => by simp [hC]
  refine Subtype.ext ?_
  simp only [coe_conjE, coe_FCE, FC, map_sub, map_mul, conjN_expLC hC, conjN_expLC hC']

end Gen

variable {d L N : ℕ} [NeZero L]

/-! ### Localisation -/

theorem cf4_conjN (F : Alg d L N) (x : Fin 4 → Lam d L N) : cf4 (conjN F) x = cj (cf4 F x) := by
  simp [cf4]

theorem mu4_conjN (b : Lam d L N) (i k : Fin d) (F : Alg d L N) :
    mu4 b i k (conjN F) = cj (mu4 b i k F) := by
  simp [mu4, cf4_conjN, map_sum]

@[simp] theorem conjN_gmono4 (e e' : Dir d) (x : Lam d L N) : conjN (gmono4 e e' x) = gmono4 e e' x := by
  simp [gmono4_eq]

@[simp] theorem conjN_mono4s (i k : Fin d) (x : Lam d L N) : conjN (mono4s i k x) = mono4s i k x := by
  unfold mono4s; split_ifs <;> simp [conjN_smul, map_ofNat]

@[simp] theorem conjN_mono4sSet (i k : Fin d) (Y : Finset (Lam d L N)) :
    conjN (mono4sSet i k Y) = mono4sSet i k Y := by
  simp [mono4sSet, map_sum]

theorem conjN_Loc2sXY (X Y : Finset (Lam d L N)) (F : Alg d L N) :
    conjN (Loc2sXY X Y F) = Loc2sXY X Y (conjN F) := by
  simp [Loc2sXY, Loc4sXY, conjN_LocXY, map_sum, conjN_smul, mu4_conjN, map_div₀]

theorem conjE_Loc2E (X Y : Finset (Lam d L N)) (F : EvR (Lam d L N)) :
    conjE (Loc2E X Y F) = Loc2E X Y (conjE F) :=
  Subtype.ext (conjN_Loc2sXY X Y F)

/-! ### The map -/

/-- The conjugate block family. -/
def conjF (V : Fam d L N) : Fam d L N := fun b => conjE (V b)

section Map

variable (j : ℕ) {C : Matrix (Lam d L N) (Lam d L N) ℂ} (hC : ∀ x y, cj (C x y) = C x y)
  (V W : Fam d L N) (K : Act d L N)

include hC

theorem Vpr_conj (b : Fin d → ℕ) : Vpr C (conjF V) b = conjE (Vpr C V b) :=
  (conjE_EthE hC _).symm

theorem VprL_conj : VprL j C (conjF V) = conjE (VprL j C V) := by
  simp [VprL, Vpr_conj hC, map_sum]

theorem Sb_conj (b : Fin d → ℕ) : Sb j C (conjF V) (conjF W) b = conjE (Sb j C V W b) := by
  simp only [Sb, map_add, conjE_smul, conjE_FCE hC, Vpr_conj hC, VprL_conj j hC, conjE_EthE hC]
  simp [conjF]

theorem SX_conj (X : Finset (Lam d L N)) :
    SX j C (conjF V) (conjF W) X = conjE (SX j C V W X) := by
  simp [SX, Sb_conj j hC, map_sum]

theorem LS_conj (b : Fin d → ℕ) : LS j C (conjF V) (conjF W) b = conjE (LS j C V W b) := by
  simp [LS, SX_conj j hC, conjE_Loc2E]

omit hC in
theorem Q2_conj (b : Fin d → ℕ) : Q2 j (conjA K) b = conjE (Q2 j K b) := by
  unfold Q2; split_ifs
  · simp [map_sum, conjE_Loc2E]
  · simp

omit hC in
theorem J2_conj (b : Fin d → ℕ) (X : Finset (Lam d L N)) :
    J2 j (conjA K) b X = conjE (J2 j K b X) := by
  unfold J2; split_ifs
  · simp [map_sum, map_neg, conjE_Loc2E]
  · simp [conjE_Loc2E]
  · simp

theorem uVp_conj (b : Fin d → ℕ) :
    uVp j C (conjF V) (conjF W) (conjA K) b = conjE (uVp j C V W K b) := by
  simp [uVp, Vpr_conj hC, LS_conj j hC, Q2_conj, conjE_EthE hC]

theorem up_conj (b : Fin d → ℕ) : up j C (conjF V) (conjF W) (conjA K) b = cj (up j C V W K b) := by
  simp [up, uVp_conj j hC, ε_conjN]

theorem Vp_conj (b : Fin d → ℕ) :
    Vp j C (conjF V) (conjF W) (conjA K) b = conjE (Vp j C V W K b) := by
  refine Subtype.ext ?_
  simp [Vp, uVp_conj j hC, up_conj j hC, Algebra.algebraMap_eq_smul_one, conjN_smul]

theorem Wp_conj (b : Fin d → ℕ) : Wp j C (conjF V) (conjF W) b = conjE (Wp j C V W b) := by
  simp [Wp, Sb_conj j hC, LS_conj j hC]

theorem Ib_conj (b : Fin d → ℕ) : Ib (conjF V) (conjF W) b = conjE (Ib V W b) := by
  simp [Ib, conjE_gexp, conjF]

theorem Ip_conj (b : Fin d → ℕ) :
    Ip j C (conjF V) (conjF W) (conjA K) b = conjE (Ip j C V W K b) := by
  simp only [Ip, up_conj j hC, Vp_conj j hC, Wp_conj j hC, conjE_smul, map_mul, map_add,
    map_one, map_neg, conjE_gexp, ← Complex.exp_conj]

theorem Gp_conj (b : Fin d → ℕ) :
    Gp j C (conjF V) (conjF W) (conjA K) b = conjE (Gp j C V W K b) := by
  simp only [Gp, Vp_conj j hC, Wp_conj j hC, map_mul, map_add, map_one, map_neg, conjE_gexp]

theorem uX_conj (X : Finset (Lam d L N)) :
    uX j C (conjF V) (conjF W) (conjA K) X = cj (uX j C V W K X) := by
  simp [uX, up_conj j hC, map_sum]

end Map

section Gen'

variable (k : ℕ) {C : Matrix (Lam d L N) (Lam d L N) ℂ} (hC : ∀ x y, cj (C x y) = C x y)
  (I Ib Ip : (Fin d → ℕ) → EvR (Lam d L N)) (K M : Act d L N)
  (J : (Fin d → ℕ) → Finset (Lam d L N) → EvR (Lam d L N))

omit [NeZero L] in
theorem bpow_conj (X : Finset (Lam d L N)) :
    bpow k (fun b => conjE (I b)) X = conjE (bpow k I X) := by
  simp [bpow, map_prod]

include hC in
theorem gKnext_conj (U : Finset (Lam d L N)) :
    gKnext k C (fun b => conjE (Ib b)) (fun b => conjE (Ip b)) (conjA K)
      (fun b X => conjE (J b X)) U = conjE (gKnext k C Ib Ip K J U) := by
  simp only [gKnext, gKchk, gKchkC, gKtil, gdIPow, gdI, map_sum, map_mul, map_prod, map_sub,
    conjE_thetaE, conjE_inclE, Kext_conjA, bpow_conj, conjE_ECCE hC]

theorem Kout_conj (W : Finset (Lam d L N)) :
    Kout k (fun b => conjE (I b)) (conjA M) (fun b X => conjE (J b X)) W =
      conjE (Kout k I M J W) := by
  simp only [Kout, Rterm, Jbar, map_sum, map_mul, map_prod, bpow_conj, Kext_conjA]

end Gen'

section Map2

variable (j : ℕ) {C : Matrix (Lam d L N) (Lam d L N) ℂ} (hC : ∀ x y, cj (C x y) = C x y)
  (V W : Fam d L N) (K : Act d L N)

include hC

theorem Knext2_conj (U : Finset (Lam d L N)) :
    Knext2 j C (conjF V) (conjF W) (conjA K) U = conjE (Knext2 j C V W K U) := by
  have hIb : Ib (conjF V) (conjF W) = fun b => conjE (Ib V W b) := funext (Ib_conj hC V W)
  have hIp : Ip j C (conjF V) (conjF W) (conjA K) = fun b => conjE (Ip j C V W K b) :=
    funext (Ip_conj j hC V W K)
  have hJ : J2 j (conjA K) = fun b X => conjE (J2 j K b X) := funext fun b => funext fun X =>
    J2_conj j K b X
  rw [Knext2, Knext2, hIb, hIp, hJ, gKnext_conj (k := j) hC, uX_conj j hC, conjE_smul,
    ← Complex.exp_conj]

theorem k2_conj (X : Finset (Lam d L N)) : k2 j C (conjF V) X = conjE (k2 j C V X) := by
  unfold k2; split_ifs
  · simp [map_sum, conjE_smul, conjE_FCE hC, Vpr_conj hC, VprL_conj j hC, map_ofNat]
  · simp [map_sum, conjE_smul, conjE_FCE hC, Vpr_conj hC, map_ofNat]
  · simp

theorem K2_conj (U : Finset (Lam d L N)) : K2 j C (conjF V) U = conjE (K2 j C V U) := by
  simp [K2, map_sum, k2_conj j hC]

theorem Knew_conj (U : Finset (Lam d L N)) :
    Knew j C (conjF V) (conjF W) (conjA K) U = conjE (Knew j C V W K U) := by
  have hG : Gp j C (conjF V) (conjF W) (conjA K) = fun b => conjE (Gp j C V W K b) :=
    funext (Gp_conj j hC V W K)
  rw [Knew, Knew, Knext2_conj j hC, K2_conj j hC, hG, bpow_conj, map_sub, map_mul]

theorem It_conj (c : Fin d → ℕ) :
    It j C (conjF V) (conjF W) (conjA K) c = conjE (It j C V W K c) := by
  have hG : Gp j C (conjF V) (conjF W) (conjA K) = fun b => conjE (Gp j C V W K b) :=
    funext (Gp_conj j hC V W K)
  rw [It, It, hG, bpow_conj]

theorem kap_conj (X : Finset (Lam d L N)) (c : Fin d → ℕ) :
    kap j C (conjF V) X c = conjE (kap j C V X c) := by
  unfold kap; split_ifs
  · simp [map_sum, conjE_smul, conjE_FCE hC, Vpr_conj hC, VprL_conj j hC, map_ofNat]
  · simp [map_sum, conjE_smul, conjE_FCE hC, Vpr_conj hC, map_ofNat]
  · simp

theorem Jh_conj (c : Fin d → ℕ) (U : Finset (Lam d L N)) :
    Jh j C (conjF V) c U = conjE (Jh j C V c U) := by
  unfold Jh; split_ifs
  · simp [map_sum, kap_conj j hC]
  · simp

/-- **`K_{j+1}` commutes with complex conjugation** (real covariance). -/
theorem Kplus_conj (U : Finset (Lam d L N)) :
    Kplus j C (conjF V) (conjF W) (conjA K) U = conjE (Kplus j C V W K U) := by
  have hI : It j C (conjF V) (conjF W) (conjA K) = fun c => conjE (It j C V W K c) :=
    funext (It_conj j hC V W K)
  have hM : Knew j C (conjF V) (conjF W) (conjA K) = conjA (Knew j C V W K) :=
    funext (Knew_conj j hC V W K)
  have hJ : Jh j C (conjF V) = fun c U => conjE (Jh j C V c U) :=
    funext fun c => funext fun U => Jh_conj j hC V c U
  rw [Kplus, Kplus, hI, hM, hJ, Kout_conj]

/-- **`𝒲_{j+1}` commutes with complex conjugation.** -/
theorem Wnext2_conj (c : Fin d → ℕ) :
    Wnext2 j C (conjF V) (conjF W) c = conjE (Wnext2 j C V W c) := by
  simp [Wnext2, map_prod, Wp_conj j hC]

/-- **`V_{j+1}` commutes with complex conjugation.** -/
theorem Vnext2_conj (c : Fin d → ℕ) :
    Vnext2 j C (conjF V) (conjF W) (conjA K) c = conjE (Vnext2 j C V W K c) := by
  simp [Vnext2, map_sum, Vp_conj j hC]

end Map2

/-! ### Real couplings -/

/-- The conjugate coupling constants. -/
def Coup.conj (κ : Coup) : Coup := ⟨cj κ.z, cj κ.y, cj κ.nu, cj κ.g⟩

theorem conjN_Vcoup (κ : Coup) (Y : Finset (Lam d L N)) :
    conjN (Vcoup κ Y) = Vcoup κ.conj Y := by
  have hC : ∀ M : Mono d, cj (coupC κ M) = coupC κ.conj M := by
    intro M; cases M <;> simp [coupC, Coup.conj] <;> split_ifs <;> simp [map_ofNat]
  have hE : ∀ i k : Fin d, cj (coupE κ i k) = coupE κ.conj i k := by
    intro i k; simp [coupE, Coup.conj]; split_ifs <;> simp
  simp [Vcoup, unif, map_sum, conjN_smul, hC, hE]

theorem cvec4_conjN (Y : Finset (Lam d L N)) (i₀ : Fin d) (F : Alg d L N) (a : Fin 4) :
    cvec4 Y i₀ (conjN F) a = cj (cvec4 Y i₀ F a) := by
  fin_cases a <;> simp [cvec4, locCoef_conjN, mu4_conjN, map_div₀, map_ofNat]

/-! ### Real dressed covariances -/

theorem kern_real {w : DressedFRD.Sym d (L ^ N)} (hw : w ∈ DressedFRD.realSub)
    (x : Lam d L N) : cj (DressedFRD.kern w x) = DressedFRD.kern w x := by
  unfold DressedFRD.kern
  rw [map_mul, map_inv₀, map_pow, map_natCast, map_sum]
  congr 1
  simp only [map_mul, (hw _).1, ← FRD.char_neg_left]
  rw [← Equiv.sum_comp (Equiv.neg (Lam d L N))]
  refine sum_congr rfl fun m _ => ?_
  simp [(hw m).2]

end

end Step2
