import Obs2.Map.ExactStep
import PtCorr2.Zero.Chain
import PtCorr2.Zero.Final
import PtCorr2.Obs.ObsZero

/-!
# Gaussian integrals with sources along the raw flow (`sec:corr`, observables)

The analogue of `PtCorr2.Zero.Chain` on the algebra with sources `OE c Λ`.

* `omegaCO Γ F = ε(e^{ℒ_Γ} F)` componentwise (`omegaCO_e`, …): the Gaussian integral with sources;
* `cstO`: the constants (`ε F = F`); `omegaCO_cst_mul`: constants factor out;
* `omegaCO_absorb`: the absorption step (`lem:onestep`) with sources, componentwise from
  `Grassmann.omegaC_onestep`;
* `gZO_factor`: `Z(V♭ + Δ + V^{obs}, 𝒲, K) = e^{-Δ(Λ)} Z(V♭ + V^{obs}, 𝒲, K♭)`;
* **`rawStepO_omega`** (`j + 1 < N`): with the full input `ZinO` (bulk and observable parts of the
  observable flow of `Obs2.Flow.Hist`),
  `⟨Z_j⟩_{Γ_j} = det(1 + a_jAΓ_j) e^{-u_{j+1}(Λ)} ⟨Z_{j+1}⟩_{Γ_{j+1}}` with the extended constant
  `e^{-u_{j+1}(Λ)} = expU (-u^∅) (-u^{obs})`; hypotheses: those of `PtCorr2.rawStep_omega`, and the
  locality `OLocHyp` of the input with sources;
* **`lastStepO_omega`** (`j + 1 = N`, no locality hypothesis: at the last scale there is a single
  polymer): `⟨Z_{N-1}⟩_{Γ_{N-1}} = det(1 + aAΓ_{N-1}) e^{-u_N(Λ)} ⟨F_N⟩_{t_raw Q}` with the final
  object with sources `finO` (`∑_{U} Ĩ_N^{Λ∖U} K_N(U)`, nonzero modes integrated) and the zero mode
  `t_raw Q` (`zmRaw`) integrated by `omegaCO_cstC_e`, `omegaCO_cstC_ab`, `omegaCO_cstC_two`
  (`ε F_• - t_raw/|Λ| · F_•²`).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD Obs2 Step2.LastN Suscept

/-! ### Gaussian integrals with sources -/

section Gauss

variable {c : Obs.Case} {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

/-- **The Gaussian integral with sources**, componentwise `⟨F_•⟩_Γ = ε(e^{ℒ_Γ}F_•)`. -/
def omegaCO (Γ : Matrix Λ Λ ℂ) (F : OE c Λ) : OE c Λ := epsO (expO Γ F)

theorem omegaCO_e (Γ : Matrix Λ Λ ℂ) (F : OE c Λ) :
    ((omegaCO Γ F : OE c Λ) : SA c Λ).e = algebraMap ℂ (N Λ) (omegaC Γ (F : SA c Λ).e) := rfl
theorem omegaCO_a (Γ : Matrix Λ Λ ℂ) (F : OE c Λ) :
    ((omegaCO Γ F : OE c Λ) : SA c Λ).a = algebraMap ℂ (N Λ) (omegaC Γ (F : SA c Λ).a) := rfl
theorem omegaCO_b (Γ : Matrix Λ Λ ℂ) (F : OE c Λ) :
    ((omegaCO Γ F : OE c Λ) : SA c Λ).b = algebraMap ℂ (N Λ) (omegaC Γ (F : SA c Λ).b) := rfl
theorem omegaCO_ab (Γ : Matrix Λ Λ ℂ) (F : OE c Λ) :
    ((omegaCO Γ F : OE c Λ) : SA c Λ).ab = algebraMap ℂ (N Λ) (omegaC Γ (F : SA c Λ).ab) := rfl

theorem expO_zero (F : OE c Λ) : expO (0 : Matrix Λ Λ ℂ) F = F := by
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;> exact expLC_zero _

theorem expLC_comp (C₁ C₂ : Matrix Λ Λ ℂ) (x : N Λ) :
    expLC C₂ (expLC C₁ x) = expLC (C₁ + C₂) x := by
  rw [← ECC_theta, ← ECC_theta, ← ECC_theta, ECC_theta_comp]

theorem expO_comp (C₁ C₂ : Matrix Λ Λ ℂ) (F : OE c Λ) :
    expO C₂ (expO C₁ F) = expO (C₁ + C₂) F := by
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;> exact expLC_comp _ _ _

theorem ECCO_thetaO (C : Matrix Λ Λ ℂ) (F : OE c Λ) : ECCO C (thetaO F) = expO C F :=
  EthO_eq_expO C F

theorem omegaC_smulN (Γ : Matrix Λ Λ ℂ) (r : ℂ) (x : N Λ) :
    omegaC Γ (r • x) = r * omegaC Γ x := by
  rw [omegaC, omegaC, map_smul, map_smul, smul_eq_mul]

theorem omegaC_addN (Γ : Matrix Λ Λ ℂ) (x y : N Λ) :
    omegaC Γ (x + y) = omegaC Γ x + omegaC Γ y := by
  rw [omegaC, omegaC, omegaC, map_add, map_add]

/-- The constants: `ε F = F`. -/
def cstO (c : Obs.Case) (Λ : Type*) [DecidableEq Λ] [Fintype Λ] : Subalgebra ℂ (OE c Λ) :=
  AlgHom.equalizer epsO (AlgHom.id ℂ (OE c Λ))

theorem mem_cstO {G : OE c Λ} : G ∈ cstO c Λ ↔ epsO G = G := AlgHom.mem_equalizer _ _ _

theorem epsN_epsN (x : N Λ) : epsN (epsN x) = epsN x := by
  simp only [epsN, AlgHom.comp_apply, Algebra.ofId_apply, AlgHom.commutes]

theorem epsO_mem_cstO (F : OE c Λ) : epsO F ∈ cstO c Λ := by
  rw [mem_cstO]
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;> exact epsN_epsN _

theorem πobs_mem_cstO {G : OE c Λ} (hG : G ∈ cstO c Λ) : πobs G ∈ cstO c Λ := by
  rw [mem_cstO] at hG ⊢
  have ha : epsN (G : SA c Λ).a = (G : SA c Λ).a := congrArg (fun F : OE c Λ => (F : SA c Λ).a) hG
  have hb : epsN (G : SA c Λ).b = (G : SA c Λ).b := congrArg (fun F : OE c Λ => (F : SA c Λ).b) hG
  have hab : epsN (G : SA c Λ).ab = (G : SA c Λ).ab :=
    congrArg (fun F : OE c Λ => (F : SA c Λ).ab) hG
  refine Subtype.ext ?_
  show epsS (πobs G : SA c Λ) = (πobs G : SA c Λ)
  rw [coe_πobs']
  refine SA.ext ?_ ?_ ?_ ?_
  · show epsN 0 = 0; exact map_zero _
  · exact ha
  · exact hb
  · exact hab

theorem cst_e {G : OE c Λ} (hG : G ∈ cstO c Λ) :
    (G : SA c Λ).e = algebraMap ℂ (N Λ) (ε (G : SA c Λ).e) :=
  (congrArg (fun F : OE c Λ => (F : SA c Λ).e) (mem_cstO.1 hG)).symm
theorem cst_a {G : OE c Λ} (hG : G ∈ cstO c Λ) :
    (G : SA c Λ).a = algebraMap ℂ (N Λ) (ε (G : SA c Λ).a) :=
  (congrArg (fun F : OE c Λ => (F : SA c Λ).a) (mem_cstO.1 hG)).symm
theorem cst_b {G : OE c Λ} (hG : G ∈ cstO c Λ) :
    (G : SA c Λ).b = algebraMap ℂ (N Λ) (ε (G : SA c Λ).b) :=
  (congrArg (fun F : OE c Λ => (F : SA c Λ).b) (mem_cstO.1 hG)).symm
theorem cst_ab {G : OE c Λ} (hG : G ∈ cstO c Λ) :
    (G : SA c Λ).ab = algebraMap ℂ (N Λ) (ε (G : SA c Λ).ab) :=
  (congrArg (fun F : OE c Λ => (F : SA c Λ).ab) (mem_cstO.1 hG)).symm

/-- **Constants factor out of the Gaussian integral.** -/
theorem omegaCO_cst_mul (Γ : Matrix Λ Λ ℂ) {G : OE c Λ} (hG : G ∈ cstO c Λ) (F : OE c Λ) :
    omegaCO Γ (G * F) = G * omegaCO Γ F := by
  obtain ⟨re, he⟩ : ∃ r, (G : SA c Λ).e = algebraMap ℂ (N Λ) r := ⟨_, cst_e hG⟩
  obtain ⟨ra, ha⟩ : ∃ r, (G : SA c Λ).a = algebraMap ℂ (N Λ) r := ⟨_, cst_a hG⟩
  obtain ⟨rb, hb⟩ : ∃ r, (G : SA c Λ).b = algebraMap ℂ (N Λ) r := ⟨_, cst_b hG⟩
  obtain ⟨rab, hab⟩ : ∃ r, (G : SA c Λ).ab = algebraMap ℂ (N Λ) r := ⟨_, cst_ab hG⟩
  have k : ∀ (r : ℂ) (x : N Λ), algebraMap ℂ (N Λ) r * x = r • x :=
    fun r x => (Algebra.smul_def r x).symm
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;>
  simp only [omegaCO_e, omegaCO_a, omegaCO_b, omegaCO_ab, OE.mul_e, OE.mul_a, OE.mul_b, OE.mul_ab,
    he, ha, hb, hab, k, omegaC_addN, omegaC_smulN, map_add, map_mul, smul_mul_assoc, smul_smul]

theorem expU_mem_cstO (x : ℂ) {u : OE c Λ} (hu : u ∈ cstO c Λ) : expU x u ∈ cstO c Λ :=
  Subalgebra.smul_mem _ (oexp_mem hu) _

/-- **The absorption step with sources** (`lem:onestep`, componentwise). -/
theorem omegaCO_absorb (z : ℂ) (A Γ Γ₁ Γ₂ : Matrix Λ Λ ℂ) (hT : IsUnit (1 + z • (A * Γ)).det)
    (hΓ : Γ * (1 + z • (A * Γ))⁻¹ = Γ₁ + Γ₂) (E : EvR Λ)
    (hE : (E : N Λ) = IsNilpotent.exp (-(z • ∑ x, ∑ y, A x y • (psi x * psibar y))))
    (F : OE c Λ) :
    omegaCO Γ (emb E * F) = (1 + z • (A * Γ)).det • omegaCO Γ₂ (ECCO Γ₁ (thetaO F)) := by
  have h := fun G : N Λ => omegaC_onestep z A Γ Γ₁ Γ₂ hT hΓ G
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_)
  · show algebraMap ℂ (N Λ) (omegaC Γ ((emb E * F : OE c Λ) : SA c Λ).e) =
      (1 + z • (A * Γ)).det • algebraMap ℂ (N Λ) (omegaC Γ₂ (ECC Γ₁ (theta (F : SA c Λ).e)))
    rw [OE.mul_e, coe_emb, ofN_e, hE, h, map_mul, ← Algebra.smul_def]
  · show algebraMap ℂ (N Λ) (omegaC Γ ((emb E * F : OE c Λ) : SA c Λ).a) =
      (1 + z • (A * Γ)).det • algebraMap ℂ (N Λ) (omegaC Γ₂ (ECC Γ₁ (theta (F : SA c Λ).a)))
    rw [OE.mul_a, coe_emb, ofN_e, ofN_a, zero_mul, add_zero, hE, h, map_mul, ← Algebra.smul_def]
  · show algebraMap ℂ (N Λ) (omegaC Γ ((emb E * F : OE c Λ) : SA c Λ).b) =
      (1 + z • (A * Γ)).det • algebraMap ℂ (N Λ) (omegaC Γ₂ (ECC Γ₁ (theta (F : SA c Λ).b)))
    rw [OE.mul_b, coe_emb, ofN_e, ofN_b, zero_mul, add_zero, hE, h, map_mul, ← Algebra.smul_def]
  · show algebraMap ℂ (N Λ) (omegaC Γ ((emb E * F : OE c Λ) : SA c Λ).ab) =
      (1 + z • (A * Γ)).det • algebraMap ℂ (N Λ) (omegaC Γ₂ (ECC Γ₁ (theta (F : SA c Λ).ab)))
    rw [OE.mul_ab, coe_emb, ofN_e, ofN_a, ofN_b, ofN_ab, zero_mul, zero_mul, zero_mul, smul_zero,
      add_zero, add_zero, add_zero, hE, h, map_mul, ← Algebra.smul_def]

/-- `⟨F⟩_{cQ}` componentwise for the zero mode (`Q = 𝟙/|Λ|·…`, `cstC`): the bulk component. -/
theorem omegaCO_cstC_e [Nonempty Λ] (cc : ℂ) (F : OE c Λ) :
    ((omegaCO (cstC Λ cc) F : OE c Λ) : SA c Λ).e =
      algebraMap ℂ (N Λ) (ε (F : SA c Λ).e - cc * c2 (F : SA c Λ).e) := by
  rw [omegaCO_e, omegaC, ← ECC_theta, eps_ECC_cstC_even cc (Step.mem_Ev.1 (OE.e_mem F))]

/-- The `ab` component of the zero-mode integral. -/
theorem omegaCO_cstC_ab [Nonempty Λ] (cc : ℂ) (F : OE c Λ) :
    ((omegaCO (cstC Λ cc) F : OE c Λ) : SA c Λ).ab =
      algebraMap ℂ (N Λ) (ε (F : SA c Λ).ab - cc * c2 (F : SA c Λ).ab) := by
  rw [omegaCO_ab, omegaC, ← ECC_theta, eps_ECC_cstC_even cc (Step.mem_Ev.1 (OE.ab_mem F))]

/-- The `a` component of the zero-mode integral in Case (2) (even sources). -/
theorem omegaCO_cstC_two [Nonempty Λ] (cc : ℂ) (F : OE .two Λ) :
    ((omegaCO (cstC Λ cc) F : OE .two Λ) : SA .two Λ).a =
      algebraMap ℂ (N Λ) (ε (F : SA .two Λ).a - cc * c2 (F : SA .two Λ).a) := by
  rw [omegaCO_a, omegaC, ← ECC_theta, eps_ECC_cstC_even cc (Step.mem_Ev.1 (OE.a_mem F))]

end Gauss

/-! ### The input with the absorbed polynomial -/

section Factor

variable {c : Obs.Case} {d L N : ℕ} [NeZero L] (j : ℕ)

theorem isNilpotent_emb {x : EvR (Lam d L N)} (hx : ε (x : Alg d L N) = 0) :
    IsNilpotent (emb x : OE c (Lam d L N)) := ⟨_, emb_pow_eq_zero hx⟩

theorem emb_gexp (x : EvR (Lam d L N)) (hx : ε (x : Alg d L N) = 0) :
    (emb (gexp x) : OE c (Lam d L N)) = oexp (emb x) :=
  IsNilpotent.map_exp (⟨_, Step.pow_eq_zero_of_ε' hx (Nat.lt_succ_self _)⟩ : IsNilpotent x) emb

theorem bpow_comp_eq (E : (Fin d → ℕ) → EvR (Lam d L N)) {X : Finset (Lam d L N)}
    (hX : IsPolymer j X) : ∏ Y ∈ Comp j X, bpow j E Y = bpow j E X := by
  have h := Kext_bpow_mul j E (fun _ => 1) hX
  simp only [mul_one] at h
  rw [show Kext j (fun _ => (1 : EvR (Lam d L N))) X = 1 from prod_eq_one fun _ _ => rfl,
    mul_one] at h
  exact h

theorem KextO_KflatO (Δ : Fam d L N) (K : OAct c d L N) {X : Finset (Lam d L N)}
    (hX : IsPolymer j X) :
    KextO j (KflatO j Δ K) X = emb (bpow j (fun b => gexp (Δ b)) X) * KextO j K X := by
  rw [KextO, KextO, ← bpow_comp_eq j _ hX, map_prod, ← prod_mul_distrib]
  rfl

/-- **`Z(V♭ + Δ + V^{obs}, 𝒲, K) = e^{-Δ(Λ)} Z(V♭ + V^{obs}, 𝒲, K♭)`** with sources. -/
theorem gZO_factor (Vf Δ : Fam d L N) (Vo W : OFam c d L N) (K : OAct c d L N)
    (hVf : ∀ b, ε (Vf b : Alg d L N) = 0) (hΔ : ∀ b, ε (Δ b : Alg d L N) = 0)
    (hVo : ∀ b, bulk (Vo b) = 0) :
    gZO j (IbO (fun b => emb (Vf b + Δ b) + Vo b) W) K =
      emb (bpow j (fun b => gexp (-Δ b)) univ) *
        gZO j (IbO (fun b => emb (Vf b) + Vo b) W) (KflatO j Δ K) := by
  have hI : ∀ b, IbO (fun b => emb (Vf b + Δ b) + Vo b) W b =
      emb (gexp (-Δ b)) * IbO (fun b => emb (Vf b) + Vo b) W b := fun b => by
    have n1 : IsNilpotent (-(emb (Vf b) + Vo b) : OE c (Lam d L N)) := by
      refine isNilpotent_of_bulk ?_
      rw [map_neg, map_add, bulk_emb, hVo b, add_zero]
      exact ⟨_, Step.pow_eq_zero_of_ε' (eps_neg_coe (hVf b)) (Nat.lt_succ_self _)⟩
    have n2 : IsNilpotent (emb (-Δ b) : OE c (Lam d L N)) := isNilpotent_emb (eps_neg_coe (hΔ b))
    show oexp (-(emb (Vf b + Δ b) + Vo b)) * (1 + W b) =
      emb (gexp (-Δ b)) * (oexp (-(emb (Vf b) + Vo b)) * (1 + W b))
    rw [show -(emb (Vf b + Δ b) + Vo b) = -(emb (Vf b) + Vo b) + emb (-Δ b) by
      rw [map_add, map_neg]; abel, oexp, IsNilpotent.exp_add_of_commute (Commute.all _ _) n1 n2,
      ← oexp, ← oexp, emb_gexp _ (eps_neg_coe (hΔ b))]
    ring
  rw [gZO, gZO, mul_sum]
  refine sum_congr rfl fun X hX => ?_
  have hXp := (mem_Pj.1 hX).2
  have hc := IsPolymer.sdiff (isPolymer_univ j) hXp
  rw [KextO_KflatO j Δ K hXp]
  have hB : bpowO j (IbO (fun b => emb (Vf b + Δ b) + Vo b) W) (univ \ X) =
      emb (bpow j (fun b => gexp (-Δ b)) (univ \ X)) *
        bpowO j (IbO (fun b => emb (Vf b) + Vo b) W) (univ \ X) := by
    rw [bpowO, bpowO, bpow, map_prod, ← prod_mul_distrib]
    exact prod_congr rfl fun b _ => hI b
  have hU : bpow j (fun b => gexp (-Δ b)) univ =
      bpow j (fun b => gexp (-Δ b)) (univ \ X) * bpow j (fun b => gexp (-Δ b)) X := by
    rw [← bpow_union j _ hc hXp sdiff_disjoint, sdiff_union_of_subset (subset_univ _)]
  have hinv : bpow j (fun b => gexp (-Δ b)) X * bpow j (fun b => gexp (Δ b)) X = 1 := by
    rw [bpow, bpow, ← prod_mul_distrib]
    refine prod_eq_one fun b _ => ?_
    rw [← gexp_add (eps_neg_coe (hΔ b)) (hΔ b), neg_add_cancel, gexp_zero]
  have hinv' : (emb (bpow j (fun b => gexp (-Δ b)) X) : OE c (Lam d L N)) *
      emb (bpow j (fun b => gexp (Δ b)) X) = 1 := by rw [← map_mul, hinv, map_one]
  rw [hB, hU, map_mul]
  linear_combination (-(emb (bpow j (fun b => gexp (-Δ b)) (univ \ X)) *
    bpowO j (IbO (fun b => emb (Vf b) + Vo b) W) (univ \ X) * KextO j K X)) * hinv'

end Factor

/-! ### One raw step with sources -/

section Raw

variable {L N : ℕ} [NeZero L] {c : Obs.Case} (R : RGPar 2 L N) (P : ObsPts 2 L N) (j : ℕ)
  (st : RawSt 2 L N) (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N) (o : ObsSt c L N)

/-- **The input `Z_j` with sources**: `∑_X I^{Λ∖X}(K + K^{obs})^X`,
`I(B) = e^{-(V♭ + Δ + V^{obs})(B)}(1 + 𝒲(B) + 𝒲^{obs}(B))`. Its bulk part is `Zin`. -/
def ZinO : OE c (Lam 2 L N) :=
  gZO j (IbO (fun b => emb (stVf R j st g μ b + stDelta R j st b) + o.V b) (fullW st D o))
    (embF K + o.K)

/-- **The output `Z_{j+1}` with sources** (activity before `Kconn`). -/
def ZoutO : OE c (Lam 2 L N) :=
  gZO (j + 1) (ItO P j (stCov R j st) (fullV R j st g μ o) (fullW st D o) (fullK R j st K o))
    (KplusO P j (stCov R j st) (fullV R j st g μ o) (fullW st D o) (fullK R j st K o))

/-- The extended constant `e^{-u_{j+1}(Λ)}` of the step (bulk and observable parts). -/
def uOutO : OE c (Lam 2 L N) :=
  expU (-uOut R j st g μ D K)
    (-uObsTot P j (stCov R j st) (fullV R j st g μ o) (fullW st D o) (fullK R j st K o))

theorem uXO_mem_cstO (C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ) (V W : OFam c 2 L N)
    (K' : OAct c 2 L N) (X : Finset (Lam 2 L N)) : uXO P j C V W K' X ∈ cstO c (Lam 2 L N) :=
  Subalgebra.sum_mem _ fun _ _ => πobs_mem_cstO (epsO_mem_cstO _)

variable {R P j st g μ D K o}

theorem uXB_full (ho : o.IsObs) :
    uXB P j (stCov R j st) (fullV R j st g μ o) (fullW st D o) (fullK R j st K o) univ =
      uOut R j st g μ D K := by
  rw [uXB_eq, bulkF_fullV R j st g μ ho, bulkF_fullW st D ho, bulkF_fullK R j st K ho]
  rfl

/-- **One raw step with sources on Gaussian integrals** (`j + 1 < N`):
`⟨Z_j⟩_{Γ_j} = det(1 + a_jAΓ_j) e^{-u_{j+1}(Λ)} ⟨Z_{j+1}⟩_{Γ_{j+1}}`. -/
theorem rawStepO_omega (hV : ValidCore R j) (H : RawInv R j st) (hS : SplitOK R j st) (ho : o.IsObs)
    (hloc : OLocHyp P j (fullV R j st g μ o) (fullW st D o) (fullK R j st K o)) :
    omegaCO (DressedFRD.kmat ((stData R j st).Gam j)) (ZinO R j st g μ D K o) =
      detStep R j st • (uOutO R P j st g μ D K o *
        omegaCO (DressedFRD.kmat ((stData R j st).Gam (j + 1))) (ZoutO R P j st g μ D K o)) := by
  obtain ⟨hT, hΓ⟩ := split_kmat (L := L) (N := N) (stData R j st) j hS.1 hS.2
  rw [stData_ζZ H] at hT hΓ
  have e : stA R st - stYc R st + stYc R st = stA R st := sub_add_cancel _ _
  obtain ⟨hC, -, -, -⟩ := RawInv.covL hV H
  obtain ⟨hj2, hd, hL, -, -, -, -⟩ := hV
  have hL' : 2 ^ (2 + 3) ≤ L := by omega
  have hE := coe_bpow_gexp_grad (L := L) (N := N) j R.msq (stA R st - stYc R st) (stYc R st)
    (stDelta R j st) fun b => coe_stDelta b
  have hCR : CovRange j (stCov R j st) := fun x y h => hC.range hj2 x y h
  rw [ZinO, gZO_factor j (stVf R j st g μ) (stDelta R j st) o.V (fullW st D o) (embF K + o.K)
      (eps_VfamL j _) (eps_stDelta R j st) ho.V,
    omegaCO_absorb (stA R st - stYc R st + stYc R st) (Aop R.msq)
      (DressedFRD.kmat ((stData R j st).Gam j)) (stCov R j st)
      (DressedFRD.kmat ((stData R j st).Gam (j + 1)))
      (by rw [e]; exact hT) (by rw [e]; exact hΓ) _ hE, e]
  have hs := stepK_ZVKO (P := P) (C := stCov R j st) (V := fullV R j st g μ o)
    (W := fullW st D o) (K := fullK R j st K o) (by norm_num) hL' hj2 hCR hloc
  rw [show (IbO (fun b => emb (stVf R j st g μ b) + o.V b) (fullW st D o) : OFam c 2 L N) =
      IbO (fullV R j st g μ o) (fullW st D o) from rfl,
    show (KflatO j (stDelta R j st) (embF K + o.K) : OAct c 2 L N) = fullK R j st K o from rfl,
    hs, omegaCO_cst_mul _ (expU_mem_cstO _ (neg_mem (uXO_mem_cstO P j _ _ _ _ _))),
    uXB_full ho]
  rfl

end Raw

/-! ### The last step with sources -/

section Last

variable {L N : ℕ} [NeZero L] {c : Obs.Case} (R : RGPar 2 L N) (P : ObsPts 2 L N) (j : ℕ)
  (st : RawSt 2 L N) (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N) (o : ObsSt c L N)

/-- **The final object with sources** after the nonzero modes of the last step:
`F_N = ∑_{U ∈ 𝒫_N} Ĩ_N^{Λ∖U} K_N(U)` (`= Ĩ_N^Λ + K_N(Λ)`), covariance `C'^{≠0}_N`. -/
def finO : OE c (Lam 2 L N) :=
  ∑ U ∈ Pj (j + 1) (univ : Finset (Lam 2 L N)),
    bpowO j (GpO P j (stCovN R j st) (fullV R j st g μ o) (fullW st D o) (fullK R j st K o))
      (univ \ U) *
      Knext2O P j (stCovN R j st) (fullV R j st g μ o) (fullW st D o) (fullK R j st K o) U

/-- The extended constant `e^{-u_N(Λ)}` of the last step. -/
def uOutNO : OE c (Lam 2 L N) :=
  expU (-uXB P j (stCovN R j st) (fullV R j st g μ o) (fullW st D o) (fullK R j st K o) univ)
    (-uXO P j (stCovN R j st) (fullV R j st g μ o) (fullW st D o) (fullK R j st K o) univ)

variable {R P j st g μ D K o}

theorem omegaCO_zero_ECCO {Λ : Type*} [DecidableEq Λ] [Fintype Λ] (C₁ C₂ : Matrix Λ Λ ℂ)
    (F : OE c Λ) :
    omegaCO 0 (ECCO (C₁ + C₂) (thetaO F)) = omegaCO C₂ (ECCO C₁ (thetaO F)) := by
  rw [omegaCO, omegaCO, expO_zero, ECCO_thetaO, ECCO_thetaO, expO_comp]

set_option maxHeartbeats 1000000 in
/-- **The last step with sources** (`j + 1 = N`): `Γ_N = 0` and
`⟨Z_{N-1}⟩_{Γ_{N-1}} = det(1 + aAΓ_{N-1}) e^{-u_N(Λ)} ⟨F_N⟩_{t_raw Q}`, `t_raw = zmRaw`. No
locality hypothesis is needed. -/
theorem lastStepO_omega (hj : j + 1 = N) (H : RawInv R j st) (hS : SplitOK R j st)
    (ho : o.IsObs) :
    omegaCO (DressedFRD.kmat ((stData R j st).Gam j)) (ZinO R j st g μ D K o) =
      detStep R j st • (uOutNO R P j st g μ D K o *
        omegaCO (cstC (Lam 2 L N) (zmRaw R j (Function.update st.ζ j (stZeta R st)) /
          Fintype.card (Lam 2 L N))) (finO R P j st g μ D K o)) := by
  obtain ⟨hT, hΓ⟩ := split_kmat (L := L) (N := N) (stData R j st) j hS.1 hS.2
  rw [stData_ζZ H] at hT hΓ
  have e : stA R st - stYc R st + stYc R st = stA R st := sub_add_cancel _ _
  have hG0 : DressedFRD.kmat ((stData R j st).Gam (j + 1)) = 0 := by
    have : (stData R j st).Gam (j + 1) = 0 := by
      funext m
      simp only [DressedFRD.Data.Gam, Pi.add_apply, Pi.smul_apply, Finset.sum_apply]
      have h1 : DressedFRD.Cgt (stData R j st).C (stData R j st).N (j + 1) = 0 := by
        show DressedFRD.Cgt _ N (j + 1) = 0
        simp [DressedFRD.Cgt, ← hj]
      have h2 : Ioc (j + 1) (stData R j st).N = ∅ := by
        show Ioc (j + 1) N = ∅
        rw [← hj, Finset.Ioc_self]
      rw [h1, h2]; simp
    rw [this]
    ext x y
    simp [DressedFRD.kmat, DressedFRD.kern]
  have hΓ' : DressedFRD.kmat ((stData R j st).Gam j) * (1 + (stA R st - stYc R st + stYc R st) •
      (Aop R.msq * DressedFRD.kmat ((stData R j st).Gam j)))⁻¹ =
      (lastCov R j (Function.update st.ζ j (stZeta R st)) +
        cstC (Lam 2 L N) (zmRaw R j (Function.update st.ζ j (stZeta R st)) /
          Fintype.card (Lam 2 L N))) + DressedFRD.kmat ((stData R j st).Gam (j + 1)) := by
    rw [e]; refine hΓ.trans ?_; rw [← fullCovN_eq]; rfl
  have hE := coe_bpow_gexp_grad (L := L) (N := N) j R.msq (stA R st - stYc R st) (stYc R st)
    (stDelta R j st) fun b => coe_stDelta b
  unfold detStep
  rw [ZinO, gZO_factor j (stVf R j st g μ) (stDelta R j st) o.V (fullW st D o) (embF K + o.K)
      (eps_VfamL j _) (eps_stDelta R j st) ho.V,
    omegaCO_absorb (stA R st - stYc R st + stYc R st) (Aop R.msq) _ _ _
      (by rw [e]; exact hT) hΓ' _ hE, e, hG0]
  congr 1
  rw [omegaCO_zero_ECCO,
    show lastCov R j (Function.update st.ζ j (stZeta R st)) = stCovN R j st from rfl,
    show (IbO (fun b => emb (stVf R j st g μ b) + o.V b) (fullW st D o) : OFam c 2 L N) =
      IbO (fullV R j st g μ o) (fullW st D o) from rfl,
    show (KflatO j (stDelta R j st) (embF K + o.K) : OAct c 2 L N) = fullK R j st K o from rfl,
    stepO_ZVK P, omegaCO_cst_mul _ (expU_mem_cstO _ (neg_mem (uXO_mem_cstO P j _ _ _ _ _)))]
  rfl

end Last

/-! ### Telescoping -/

/-- **Telescoping of the step identities with sources.** -/
theorem chain_omegaO {c : Obs.Case} {Λ : Type*} [DecidableEq Λ] [Fintype Λ]
    {Γ : ℕ → Matrix Λ Λ ℂ} {Zs : ℕ → OE c Λ} {cs : ℕ → OE c Λ} (n : ℕ)
    (h : ∀ i < n, omegaCO (Γ i) (Zs i) = cs i * omegaCO (Γ (i + 1)) (Zs (i + 1))) :
    omegaCO (Γ 0) (Zs 0) = (∏ i ∈ range n, cs i) * omegaCO (Γ n) (Zs n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih fun i hi => h i (by omega), h n (by omega), prod_range_succ, mul_assoc]

end

end PtCorr2
