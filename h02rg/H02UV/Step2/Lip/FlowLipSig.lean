import Step2.Map.RGMap

/-!
# Equivariance of the step under field rescaling (Lipschitz bounds, part 1)

For `r ∈ ℂ` the field rescaling `σ_r` (`sig`, `sigE`, `sigF`, `sigK`) intertwines the
expectation with covariance `r² C` and the expectation with covariance `C`:
`𝔼_C σ_r = σ_r 𝔼_{r² C}` (`expLC_sig`). The localisation commutes with `σ_r` (it is homogeneous of
degree 0 in the fields), the coupling read-off scales as `(r², r², r², r⁴)`.

Consequently every map of the step is equivariant:
`Φ(C, σ_r V, σ_r 𝒲, σ_r K) = σ_r Φ(r² C, V, 𝒲, K)` for `Φ = K_{j+1}` (`Kplus_sig`),
`V_{j+1}` (`Vnext2_sig`), `𝒲^lin_{j+1}` (`WlinNext_sig`), `D_{j+1}` (`Dnext_sig`), and `K♭`,
`Kconn` commute with `σ_r`.
-/

namespace Step2

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD

/-! ### General Grassmann lemmas -/

section General

variable {Λ Λ' : Type*} [DecidableEq Λ] [DecidableEq Λ']

theorem map_sig_comm' (f : V Λ →ₗ[ℂ] V Λ') (r : ℂ) (F : Grassmann.N Λ) :
    ExteriorAlgebra.map f (sig r F) = sig r (ExteriorAlgebra.map f F) := by
  rw [sig, sig, ← AlgHom.comp_apply, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map,
    ExteriorAlgebra.map_comp_map]
  congr 2
  ext v; simp

theorem proj_sig (r : ℂ) (F : Grassmann.N (Λ ⊕ Λ)) : proj (sig r F) = sig r (proj F) :=
  map_sig_comm' _ r F

theorem mapE_sigE_comm (f : V Λ →ₗ[ℂ] V Λ') (r : ℂ) (F : EvR Λ) :
    mapE f (sigE r F) = sigE r (mapE f F) :=
  Subtype.ext (by simp only [coe_mapE, coe_sigE]; exact map_sig_comm' f r _)

theorem thetaE_sigE (r : ℂ) (F : EvR Λ) : thetaE (sigE r F) = sigE r (thetaE F) :=
  mapE_sigE_comm _ r F

theorem inclE_sigE (r : ℂ) (F : EvR Λ) : inclE (sigE r F) = sigE r (inclE F) :=
  mapE_sigE_comm _ r F

/-- A homogeneous element of degree `k` scales as `r^k`. -/
theorem sig_of_homog [Fintype Λ] {k : ℕ} {F : Grassmann.N Λ} (hF : ∀ n (z : Fin n → Sf Λ), n ≠ k → coeff F z = 0)
    (r : ℂ) : sig r F = r ^ k • F := by
  refine ext_coeff fun n z => ?_
  rw [coeff_sig, coeff_smul]
  by_cases h : n = k
  · subst h; rfl
  · rw [hF n z h, mul_zero, mul_zero]

end General

section Exp

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

theorem liftζC_smul (c : ℂ) (C : Matrix Λ Λ ℂ) : liftζC (c • C) = c • liftζC C := by
  rw [liftζC, liftζC, Matrix.fromBlocks_smul, smul_zero]

/-- **`𝔼_C σ_r = σ_r 𝔼_{r² C}`** on the doubled algebra. -/
theorem ECC_sig (C : Matrix Λ Λ ℂ) (r : ℂ) (F : Grassmann.N (Λ ⊕ Λ)) :
    ECC C (sig r F) = sig r (ECC ((r ^ 2) • C) F) := by
  rw [ECC_eq, ECC_eq, expLC_sig, proj_sig, liftζC_smul]

theorem FC_sig (C : Matrix Λ Λ ℂ) (r : ℂ) (A B : Grassmann.N Λ) :
    FC C (sig r A) (sig r B) = sig r (FC ((r ^ 2) • C) A B) := by
  simp only [FC, expLC_sig, ← map_mul, map_sub, smul_neg]

theorem ECCE_sigE (C : Matrix Λ Λ ℂ) (r : ℂ) (F : EvR (Λ ⊕ Λ)) :
    ECCE C (sigE r F) = sigE r (ECCE ((r ^ 2) • C) F) :=
  Subtype.ext (by simp only [coe_ECCE, coe_sigE]; exact ECC_sig C r _)

theorem EthE_sigE (C : Matrix Λ Λ ℂ) (r : ℂ) (F : EvR Λ) :
    EthE C (sigE r F) = sigE r (EthE ((r ^ 2) • C) F) := by
  rw [EthE, EthE, thetaE_sigE, ECCE_sigE]

theorem FCE_sigE (C : Matrix Λ Λ ℂ) (r : ℂ) (A B : EvR Λ) :
    FCE C (sigE r A) (sigE r B) = sigE r (FCE ((r ^ 2) • C) A B) :=
  Subtype.ext (by simp only [coe_FCE, coe_sigE]; exact FC_sig C r _ _)

theorem gexp_sigE (r : ℂ) (F : EvR Λ) (hF : ε (F : Grassmann.N Λ) = 0) :
    gexp (sigE r F) = sigE r (gexp F) := (sigE_gexp r F hF).symm

end Exp

/-! ### The localisation and the coupling read-off -/

section LocSig

variable {d L N : ℕ} [NeZero L]

theorem sig_monoSet (r : ℂ) (M : Mono d) (Y : Finset (Lam d L N)) :
    sig r (monoSet M Y) = r ^ 2 • monoSet M Y :=
  sig_of_homog (fun _ z hn => coeff_monoSet_of_ne M Y z hn) r

theorem sig_mono4sSet (r : ℂ) (i k : Fin d) (Y : Finset (Lam d L N)) :
    sig r (mono4sSet i k Y) = r ^ 4 • mono4sSet i k Y :=
  sig_of_homog (fun _ z hn => coeff_mono4Set_of_ne i k Y z hn) r

theorem mu_sig (b : Lam d L N) (β : Mono d) (r : ℂ) (F : Alg d L N) :
    mu b β (sig r F) = mu b β (r ^ 2 • F) := by
  simp only [mu, cf2, coeff_sig, coeff_smul]

theorem locCoef_sig (X : Finset (Lam d L N)) (r : ℂ) (F : Alg d L N) :
    locCoef X (sig r F) = r ^ 2 • locCoef X F := by
  rw [← locCoef_smul]
  unfold locCoef
  congr 1
  funext β
  exact mu_sig _ _ _ _

theorem LocXY_sig (X Y : Finset (Lam d L N)) (r : ℂ) (F : Alg d L N) :
    LocXY X Y (sig r F) = sig r (LocXY X Y F) := by
  simp only [LocXY, map_add, map_sum, map_smul, map_one, eps_sig, locCoef_sig, sig_monoSet,
    Pi.smul_apply, smul_eq_mul, smul_smul]
  congr 1
  refine sum_congr rfl fun M _ => ?_
  rw [mul_comm]

theorem Loc4sXY_sig (X Y : Finset (Lam d L N)) (r : ℂ) (F : Alg d L N) :
    Loc4sXY X Y (sig r F) = sig r (Loc4sXY X Y F) := by
  simp only [Loc4sXY, map_sum, map_smul, mu4_sig, sig_mono4sSet, smul_smul]
  refine sum_congr rfl fun i _ => sum_congr rfl fun k _ => ?_
  congr 1
  ring

theorem Loc2sXY_sig (X Y : Finset (Lam d L N)) (r : ℂ) (F : Alg d L N) :
    Loc2sXY X Y (sig r F) = sig r (Loc2sXY X Y F) := by
  rw [Loc2sXY, Loc2sXY, map_add, LocXY_sig, Loc4sXY_sig]

theorem Loc2E_sigE (X Y : Finset (Lam d L N)) (r : ℂ) (F : EvR (Lam d L N)) :
    Loc2E X Y (sigE r F) = sigE r (Loc2E X Y F) :=
  Subtype.ext (by simp only [coe_Loc2E, coe_sigE]; exact Loc2sXY_sig X Y r _)

/-- The scaling of a coupling vector: `(z, y, ν, g) ↦ (r²z, r²y, r²ν, r⁴g)`. -/
def vsc (r : ℂ) (v : Fin 4 → ℂ) : Fin 4 → ℂ := ![r ^ 2 * v 0, r ^ 2 * v 1, r ^ 2 * v 2, r ^ 4 * v 3]

theorem cvec4_sig (X : Finset (Lam d L N)) (i₀ : Fin d) (r : ℂ) (F : Alg d L N) :
    cvec4 X i₀ (sig r F) = vsc r (cvec4 X i₀ F) := by
  funext a
  fin_cases a <;> simp [cvec4, vsc, locCoef_sig, mu4_sig] <;> ring

theorem sig_unif (r κ : ℂ) (c : Mono d → ℂ) (e : Fin d → Fin d → ℂ) (Y : Finset (Lam d L N)) :
    sig r (unif κ c e Y) = unif κ (fun M => r ^ 2 * c M) (fun i k => r ^ 4 * e i k) Y := by
  simp only [unif, map_add, map_sum, map_smul, map_one, sig_monoSet, sig_mono4sSet, smul_smul]
  simp only [mul_comm _ (r ^ 2), mul_comm _ (r ^ 4)]

theorem sig_VcoupL (r : ℂ) (Y : Finset (Lam d L N)) (v : Fin 4 → ℂ) :
    sig r (VcoupL Y v) = VcoupL Y (vsc r v) := by
  show sig r (Vcoup _ Y) = Vcoup _ Y
  rw [Vcoup, Vcoup, sig_unif]
  congr 1
  · funext M
    cases M <;> simp [coupC, Coup.ofVec, vsc] <;> split_ifs <;> ring
  · funext i k
    simp only [coupE, Coup.ofVec, vsc]
    split_ifs <;> simp

theorem VfamL_vsc (k : ℕ) (r : ℂ) (v : Fin 4 → ℂ) :
    VfamL (d := d) (L := L) (N := N) k (vsc r v) = sigF r (VfamL k v) := by
  funext b
  exact Subtype.ext (sig_VcoupL r _ v).symm

end LocSig

/-! ### The maps of the step -/

section MapSig

variable {d L N : ℕ} [NeZero L]

theorem sigF_apply (r : ℂ) (F : Fam d L N) (b : Fin d → ℕ) : sigF r F b = sigE r (F b) := rfl

theorem sigK_apply (r : ℂ) (K : Act d L N) (X : Finset (Lam d L N)) :
    sigK r K X = sigE r (K X) := rfl

theorem bpow_sigE (j : ℕ) (r : ℂ) (I : (Fin d → ℕ) → EvR (Lam d L N)) (X : Finset (Lam d L N)) :
    bpow j (fun b => sigE r (I b)) X = sigE r (bpow j I X) := by
  rw [bpow, bpow, map_prod]

theorem Kext_sigK (j : ℕ) (r : ℂ) (K : Act d L N) (X : Finset (Lam d L N)) :
    Kext j (sigK r K) X = sigE r (Kext j K X) := by
  rw [Kext, Kext, map_prod]; rfl

theorem sigE_algebraMap {Λ : Type*} [DecidableEq Λ] (r c : ℂ) :
    sigE (Λ := Λ) r (algebraMap ℂ (EvR Λ) c) = algebraMap ℂ (EvR Λ) c := AlgHom.commutes _ _

variable (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V W : Fam d L N) (K : Act d L N) (r : ℂ)

theorem Vpr_sig (b : Fin d → ℕ) : Vpr C (sigF r V) b = sigE r (Vpr (r ^ 2 • C) V b) :=
  EthE_sigE C r (V b)

theorem VprL_sig : VprL j C (sigF r V) = sigE r (VprL j (r ^ 2 • C) V) := by
  simp only [VprL, Vpr_sig, map_sum]

theorem Sb_sig (b : Fin d → ℕ) :
    Sb j C (sigF r V) (sigF r W) b = sigE r (Sb j (r ^ 2 • C) V W b) := by
  rw [Sb, Sb, Vpr_sig, VprL_sig, FCE_sigE, sigF_apply, EthE_sigE, map_add, map_smul]

theorem SX_sig (X : Finset (Lam d L N)) :
    SX j C (sigF r V) (sigF r W) X = sigE r (SX j (r ^ 2 • C) V W X) := by
  simp only [SX, Sb_sig, map_sum]

theorem LS_sig (b : Fin d → ℕ) :
    LS j C (sigF r V) (sigF r W) b = sigE r (LS j (r ^ 2 • C) V W b) := by
  rw [LS, LS, SX_sig, Loc2E_sigE]

theorem Q2_sig (b : Fin d → ℕ) : Q2 j (sigK r K) b = sigE r (Q2 j K b) := by
  unfold Q2
  split_ifs
  · simp only [map_sum, sigK_apply, Loc2E_sigE]
  · rw [map_zero]

theorem J2_sig (b : Fin d → ℕ) (X : Finset (Lam d L N)) :
    J2 j (sigK r K) b X = sigE r (J2 j K b X) := by
  unfold J2
  split_ifs
  · simp only [map_neg, map_sum, sigK_apply, Loc2E_sigE]
  · simp only [sigK_apply, Loc2E_sigE]
  · rw [map_zero]

theorem uVp_sig (b : Fin d → ℕ) :
    uVp j C (sigF r V) (sigF r W) (sigK r K) b = sigE r (uVp j (r ^ 2 • C) V W K b) := by
  rw [uVp, uVp, Vpr_sig, Q2_sig, EthE_sigE, LS_sig, map_sub, map_sub]

theorem up_sig (b : Fin d → ℕ) :
    up j C (sigF r V) (sigF r W) (sigK r K) b = up j (r ^ 2 • C) V W K b := by
  rw [up, up, uVp_sig, eps_sigE]

theorem Vp_sig (b : Fin d → ℕ) :
    Vp j C (sigF r V) (sigF r W) (sigK r K) b = sigE r (Vp j (r ^ 2 • C) V W K b) := by
  rw [Vp, Vp, uVp_sig, up_sig, map_sub, sigE_algebraMap]

theorem Wp_sig (b : Fin d → ℕ) :
    Wp j C (sigF r V) (sigF r W) b = sigE r (Wp j (r ^ 2 • C) V W b) := by
  rw [Wp, Wp, Sb_sig, LS_sig, map_sub]

theorem Ib_sig (hV : ∀ b, ε (V b : Alg d L N) = 0) (b : Fin d → ℕ) :
    Ib (sigF r V) (sigF r W) b = sigE r (Ib V W b) := by
  rw [Ib, Ib, sigF_apply, sigF_apply, ← map_neg, gexp_sigE r _ (eps_neg_coe (hV b)), map_mul,
    map_add, map_one]

theorem Ip_sig (b : Fin d → ℕ) :
    Ip j C (sigF r V) (sigF r W) (sigK r K) b = sigE r (Ip j (r ^ 2 • C) V W K b) := by
  rw [Ip, Ip, up_sig, Vp_sig, Wp_sig, ← map_neg,
    gexp_sigE r _ (eps_neg_coe (ε_Vp j (r ^ 2 • C) V W K b)), map_smul, map_mul, map_add, map_one]

theorem Gp_sig (b : Fin d → ℕ) :
    Gp j C (sigF r V) (sigF r W) (sigK r K) b = sigE r (Gp j (r ^ 2 • C) V W K b) := by
  rw [Gp, Gp, Vp_sig, Wp_sig, ← map_neg,
    gexp_sigE r _ (eps_neg_coe (ε_Vp j (r ^ 2 • C) V W K b)), map_mul, map_add, map_one]

theorem uX_sig (X : Finset (Lam d L N)) :
    uX j C (sigF r V) (sigF r W) (sigK r K) X = uX j (r ^ 2 • C) V W K X := by
  simp only [uX, up_sig]

/-! #### The polymer formula with general block factors -/

section Gen

variable (Ib Ip : (Fin d → ℕ) → EvR (Lam d L N))
  (J : (Fin d → ℕ) → Finset (Lam d L N) → EvR (Lam d L N))

theorem gdI_sig (b : Fin d → ℕ) :
    gdI (fun b => sigE r (Ib b)) (fun b => sigE r (Ip b)) b = sigE r (gdI Ib Ip b) := by
  rw [gdI, gdI, thetaE_sigE, inclE_sigE, map_sub]

theorem gdIPow_sig (X : Finset (Lam d L N)) :
    gdIPow j (fun b => sigE r (Ib b)) (fun b => sigE r (Ip b)) X = sigE r (gdIPow j Ib Ip X) := by
  simp only [gdIPow, gdI_sig, map_prod]

theorem gKtil_sig (X : Finset (Lam d L N)) :
    gKtil j (fun b => sigE r (Ib b)) (fun b => sigE r (Ip b)) (sigK r K) X =
      sigE r (gKtil j Ib Ip K X) := by
  simp only [gKtil, gdIPow_sig, Kext_sigK, thetaE_sigE, map_sum, map_mul]

theorem gKchkC_sig (X : Finset (Lam d L N)) :
    gKchkC j (fun b => sigE r (Ib b)) (fun b => sigE r (Ip b)) (sigK r K)
      (fun b Y => sigE r (J b Y)) X = sigE r (gKchkC j Ib Ip K J X) := by
  simp only [gKchkC, gKtil_sig, thetaE_sigE, map_sum, map_sub]

theorem gKchk_sig (X : Finset (Lam d L N)) :
    gKchk j (fun b => sigE r (Ib b)) (fun b => sigE r (Ip b)) (sigK r K)
      (fun b Y => sigE r (J b Y)) X = sigE r (gKchk j Ib Ip K J X) := by
  simp only [gKchk, gKchkC_sig, map_prod]

theorem gKnext_sig (U : Finset (Lam d L N)) :
    gKnext j C (fun b => sigE r (Ib b)) (fun b => sigE r (Ip b)) (sigK r K)
      (fun b Y => sigE r (J b Y)) U = sigE r (gKnext j (r ^ 2 • C) Ib Ip K J U) := by
  simp only [gKnext, gKchk_sig, bpow_sigE, thetaE_sigE, ← map_prod, ← map_mul, ECCE_sigE,
    map_sum]

end Gen

theorem Knext2_sig (hV : ∀ b, ε (V b : Alg d L N) = 0) (U : Finset (Lam d L N)) :
    Knext2 j C (sigF r V) (sigF r W) (sigK r K) U = sigE r (Knext2 j (r ^ 2 • C) V W K U) := by
  have h1 : Ib (sigF r V) (sigF r W) = fun b => sigE r (Ib V W b) := funext (Ib_sig V W r hV)
  have h2 : Ip j C (sigF r V) (sigF r W) (sigK r K) = fun b => sigE r (Ip j (r ^ 2 • C) V W K b) :=
    funext (Ip_sig j C V W K r)
  have h3 : J2 j (sigK r K) = fun b Y => sigE r (J2 j K b Y) :=
    funext fun b => funext fun Y => J2_sig j K r b Y
  rw [Knext2, Knext2, uX_sig, h1, h2, h3, gKnext_sig, map_smul]

theorem k2_sig (X : Finset (Lam d L N)) : k2 j C (sigF r V) X = sigE r (k2 j (r ^ 2 • C) V X) := by
  unfold k2
  split_ifs
  · simp only [Vpr_sig, VprL_sig, ← map_sub, FCE_sigE, map_sum, map_smul]
  · simp only [Vpr_sig, FCE_sigE, map_sum, map_smul]
  · rw [map_zero]

theorem K2_sig (U : Finset (Lam d L N)) : K2 j C (sigF r V) U = sigE r (K2 j (r ^ 2 • C) V U) := by
  simp only [K2, k2_sig, map_sum]

theorem Knew_sig (hV : ∀ b, ε (V b : Alg d L N) = 0) (U : Finset (Lam d L N)) :
    Knew j C (sigF r V) (sigF r W) (sigK r K) U = sigE r (Knew j (r ^ 2 • C) V W K U) := by
  have h2 : Gp j C (sigF r V) (sigF r W) (sigK r K) = fun b => sigE r (Gp j (r ^ 2 • C) V W K b) :=
    funext (Gp_sig j C V W K r)
  rw [Knew, Knew, Knext2_sig j C V W K r hV, h2, bpow_sigE, K2_sig, map_sub, map_mul]

theorem It_sig (c : Fin d → ℕ) :
    It j C (sigF r V) (sigF r W) (sigK r K) c = sigE r (It j (r ^ 2 • C) V W K c) := by
  have h2 : Gp j C (sigF r V) (sigF r W) (sigK r K) = fun b => sigE r (Gp j (r ^ 2 • C) V W K b) :=
    funext (Gp_sig j C V W K r)
  rw [It, It, h2, bpow_sigE]

theorem kap_sig (X : Finset (Lam d L N)) (c : Fin d → ℕ) :
    kap j C (sigF r V) X c = sigE r (kap j (r ^ 2 • C) V X c) := by
  unfold kap
  split_ifs
  · simp only [Vpr_sig, VprL_sig, ← map_sub, FCE_sigE, map_sum, map_smul]
  · simp only [Vpr_sig, FCE_sigE, map_sum, map_smul]
  · rw [map_zero]

theorem Jh_sig (c : Fin d → ℕ) (U : Finset (Lam d L N)) :
    Jh j C (sigF r V) c U = sigE r (Jh j (r ^ 2 • C) V c U) := by
  unfold Jh
  split_ifs
  · simp only [kap_sig, map_sum]
  · rw [map_zero]

section Reblock

variable (k : ℕ) (I : (Fin d → ℕ) → EvR (Lam d L N)) (M : Act d L N)
  (J : (Fin d → ℕ) → Finset (Lam d L N) → EvR (Lam d L N))

theorem Kout_sig (U : Finset (Lam d L N)) :
    Kout k (fun b => sigE r (I b)) (sigK r M) (fun b Y => sigE r (J b Y)) U =
      sigE r (Kout k I M J U) := by
  simp only [Kout, Rterm, Jbar, bpow_sigE, Kext_sigK, ← map_mul, ← map_prod, map_sum]

end Reblock

/-- **Equivariance of `K_{j+1}`.** -/
theorem Kplus_sig (hV : ∀ b, ε (V b : Alg d L N) = 0) :
    Kplus j C (sigF r V) (sigF r W) (sigK r K) = sigK r (Kplus j (r ^ 2 • C) V W K) := by
  funext U
  have h1 : It j C (sigF r V) (sigF r W) (sigK r K) = fun c => sigE r (It j (r ^ 2 • C) V W K c) :=
    funext (It_sig j C V W K r)
  have h2 : Knew j C (sigF r V) (sigF r W) (sigK r K) = sigK r (Knew j (r ^ 2 • C) V W K) :=
    funext (Knew_sig j C V W K r hV)
  have h3 : Jh j C (sigF r V) = fun c Y => sigE r (Jh j (r ^ 2 • C) V c Y) :=
    funext fun c => funext fun Y => Jh_sig j C V r c Y
  rw [Kplus, Kplus, h1, h2, h3, Kout_sig]
  rfl

/-- **Equivariance of `V_{j+1}`.** -/
theorem Vnext2_sig (c : Fin d → ℕ) :
    Vnext2 j C (sigF r V) (sigF r W) (sigK r K) c = sigE r (Vnext2 j (r ^ 2 • C) V W K c) := by
  simp only [Vnext2, Vp_sig, map_sum]

theorem Wnext2_sig (c : Fin d → ℕ) :
    Wnext2 j C (sigF r V) (sigF r W) c = sigE r (Wnext2 j (r ^ 2 • C) V W c) := by
  simp only [Wnext2, Wp_sig, map_sub, map_prod, map_add, map_one]

theorem TrL_sig (s : ℂ) (F : Fam d L N) :
    TrL j C s (sigF r F) = sigF r (TrL j (r ^ 2 • C) s F) := by
  funext c
  have e : ∀ b, EthE C (sigE s (sigF r F b)) = sigE r (EthE (r ^ 2 • C) (sigE s (F b))) :=
    fun b => by
      rw [← EthE_sigE]
      congr 1
      exact Subtype.ext (by simp only [sigF_apply, coe_sigE, sig_sig, mul_comm])
  simp only [TrL, LinearMap.coe_mk, AddHom.coe_mk, e, ← map_sum, Loc2E_sigE, ← map_sub]
  rfl

theorem SrcFam_sig (A B : Fam d L N) :
    SrcFam j C (EthEL C) (sigF r A) (sigF r B) = sigF r (SrcFam j (r ^ 2 • C) (EthEL (r ^ 2 • C)) A B) := by
  funext c
  have e : ∀ b, SrcF j C (EthEL C) (sigF r A) (sigF r B) b =
      sigE r (SrcF j (r ^ 2 • C) (EthEL (r ^ 2 • C)) A B b) := fun b => by
    simp only [SrcF, EthEL_apply, sigF_apply, EthE_sigE, ← map_sum, FCE_sigE, map_smul]
  simp only [SrcFam, e, ← map_sum, Loc2E_sigE, ← map_sub]
  rfl

/-- **Equivariance of `𝒲^lin_{j+1}`.** -/
theorem WlinNext_sig (Wl : Fam d L N) :
    WlinNext j C (sigF r V) (sigF r Wl) = sigF r (WlinNext j (r ^ 2 • C) V Wl) := by
  rw [WlinNext, WlinNext, SrcL_apply, SrcL_apply, SrcFam_sig, TrL_sig, sigF_add]

/-- **Equivariance of `D_{j+1}`.** -/
theorem Dnext_sig (Wl D : Fam d L N) :
    Dnext j C (sigF r V) (sigF r Wl) (sigF r D) = sigF r (Dnext j (r ^ 2 • C) V Wl D) := by
  funext c
  show Wnext2 j C (sigF r V) (sigF r Wl + sigF r D) c - WlinNext j C (sigF r V) (sigF r Wl) c =
    sigE r (Wnext2 j (r ^ 2 • C) V (Wl + D) c - WlinNext j (r ^ 2 • C) V Wl c)
  rw [← sigF_add, Wnext2_sig, WlinNext_sig, sigF_apply, map_sub]

/-- `K♭` commutes with `σ_r`. -/
theorem Kflat_sig (Δ : Fam d L N) (hΔ : ∀ b, ε (Δ b : Alg d L N) = 0) :
    Kflat j (sigF r Δ) (sigK r K) = sigK r (Kflat j Δ K) := by
  funext Y
  have e : (fun b => gexp (sigF r Δ b)) = fun b => sigE r (gexp (Δ b)) :=
    funext fun b => gexp_sigE r _ (hΔ b)
  show bpow j (fun b => gexp (sigF r Δ b)) Y * sigK r K Y =
    sigE r (bpow j (fun b => gexp (Δ b)) Y * K Y)
  rw [e, bpow_sigE, sigK_apply, map_mul]

/-- `Kconn` commutes with `σ_r`. -/
theorem Kconn_sig (k : ℕ) : Kconn k (sigK r K) = sigK r (Kconn k K) := by
  funext X
  simp only [Kconn, sigK_apply]
  split_ifs <;> simp

end MapSig

end

end Step2
