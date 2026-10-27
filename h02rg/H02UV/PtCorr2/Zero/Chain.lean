import PtCorr2.Zero.ZeroT
import Step2.Map.Raw

/-!
# The partition function along the raw flow (`sec:corr`, the analogue of `Suscept.ZNN_eq`)

The steps of the raw flow act on Gaussian integrals `⟨F⟩_Γ = omegaC Γ F` (`lem:onestep`):

* `stData R j st`: the dressed data of step `j` (history `ζ' = ζ` updated at `j` by the absorbed
  `ζ_j`); `Γ_j = kmat (Gam j)`, `Γ^int_{j+1} = kmat (Gint j) = stCov`;
* `Zin R j st g μ D K = ∑_X I^{Λ∖X} K(X)`, `I(B) = e^{-(V♭ + Δ)(B)}(1 + 𝒲(B))`, the input of
  `rawStep`; `Zout` = `∑_U I_{j+1}^{Λ∖U} K_{j+1}(U)` its output (blocks of scale `j + 1`, before
  the restriction `Kconn` to connected polymers); `uOut = u_{j+1}(Λ)`;
* **`rawStep_omega`** (one step, `j + 1 < N`, under `ValidCore`):
  `⟨Z_j⟩_{Γ_j} = det(1 + a_j A Γ_j) e^{-u_{j+1}(Λ)} ⟨Z_{j+1}⟩_{Γ_{j+1}}`, `a_j = Z_j ζ_j`;
* **`lastStep_omega`** (`j + 1 = N`): `⟨Z_{N-1}⟩_{Γ_{N-1}} = det(1 + a A Γ_{N-1}) e^{-u_N(Λ)}
  (1 + ũ_{N,N})` with the zero-mode integration of `PtCorr2.Final` (`Γ_N = 0`);
* `chain_omega`: telescoping.

The splitting hypotheses of the dressed decomposition (`hden`, `hsplit`; `Data.split`) are
explicit. The identification `Zout_j = Zin_{j+1}` along a history (`ExactStep`) is a hypothesis:
it needs the flow coordinates `(ǧ_{j+1}, μ_{j+1}, x_{j+1})` of the trajectory to reproduce the
complex raw output exactly (reality of the raw flow; see `Log.md`).
-/

namespace PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Step2 Step Step2.LastN

variable {L N : ℕ} [NeZero L]

/-! ### Output of a step as `e^{-u_{j+1}(Λ)} Z_{j+1}` -/

theorem sum_Ip_eq_gZ (j : ℕ) (C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ) (V W : Fam 2 L N)
    (K : Act 2 L N) :
    ∑ U ∈ Pj (j + 1) univ, bpow j (Ip j C V W K) (univ \ U) *
        (Complex.exp (-uX j C V W K U) • Kext (j + 1) (Kplus j C V W K) U) =
      Complex.exp (-uX j C V W K univ) • gZ (j + 1) (It j C V W K) (Kplus j C V W K) := by
  rw [gZ, smul_sum]
  refine sum_congr rfl fun U hU => ?_
  have hUp := (mem_Pj.1 hU).2
  have hc : IsPolymer (j + 1) (univ \ U) := IsPolymer.sdiff (isPolymer_univ _) hUp
  have h : bpow j (Ip j C V W K) (univ \ U) *
      (Complex.exp (-uX j C V W K U) • Kext (j + 1) (Kplus j C V W K) U) =
      Complex.exp (-uX j C V W K univ) •
        (bpow (j + 1) (It j C V W K) (univ \ U) * Kext (j + 1) (Kplus j C V W K) U) := by
    rw [bpow_It j C V W K hc, bpow_Ip, smul_mul_assoc, mul_smul_comm, smul_smul,
      ← Complex.exp_add, ← neg_add, ← uX_union' j C V W K (IsPolymer.of_succ hc)
        (IsPolymer.of_succ hUp) sdiff_disjoint, sdiff_union_of_subset (subset_univ _)]
  exact h

/-! ### Definitions -/

variable (R : RGPar 2 L N) (j : ℕ) (st : RawSt 2 L N) (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N)

/-- The dressed data of step `j`. -/
def stData : DressedFRD.Data 2 (L ^ N) :=
  ⟨L, N, R.msq, DressedFRD.frdC R.P R.msq L N, Function.update st.ζ j (stZeta R st)⟩

/-- The input `Z_j` of the raw step. -/
def Zin : EvR (Lam 2 L N) :=
  gZ j (Ib (fun b => stVf R j st g μ b + stDelta R j st b) (st.Wl + D)) K

/-- The output `Z_{j+1}` of the raw step (activity before `Kconn`). -/
def Zout : EvR (Lam 2 L N) :=
  gZ (j + 1) (It j (stCov R j st) (stVf R j st g μ) (st.Wl + D) (Kflat j (stDelta R j st) K))
    (Kplus j (stCov R j st) (stVf R j st g μ) (st.Wl + D) (Kflat j (stDelta R j st) K))

/-- `u_{j+1}(Λ)`. -/
def uOut : ℂ :=
  uX j (stCov R j st) (stVf R j st g μ) (st.Wl + D) (Kflat j (stDelta R j st) K) univ

/-- `det(1 + a_j A Γ_j)`, `a_j = Z_j ζ_j`. -/
def detStep : ℂ :=
  (1 + stA R st • (Aop (d := 2) (L := L) (N := N) R.msq *
    DressedFRD.kmat ((stData R j st).Gam j))).det

/-- The splitting hypotheses of the dressed decomposition at step `j` (`Data.split`). -/
def SplitOK : Prop :=
  (∀ m, 1 + (stData R j st).ζ j * (stData R j st).Z j * DressedFRD.Asym R.msq m *
      (stData R j st).Gam j m ≠ 0) ∧
    ∀ m, (stData R j st).absorbed j m = (stData R j st).Gint j m + (stData R j st).Gam (j + 1) m

variable {R j st g μ D K}

theorem stData_ζZ (H : RawInv R j st) :
    (stData R j st).ζ j * (stData R j st).Z j = stA R st := by
  show Function.update st.ζ j (stZeta R st) j * ∏ i ∈ range j,
    (1 + Function.update st.ζ j (stZeta R st) i) = st.Z * stZeta R st
  rw [Function.update_self, H.hZprod, mul_comm]
  congr 1
  refine prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (by have := mem_range.1 hi; omega)]

theorem omegaC_smul' (C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ) (c : ℂ) (F : EvR (Lam 2 L N)) :
    omegaC C ((c • F : EvR (Lam 2 L N)) : Alg 2 L N) = c * omegaC C (F : Alg 2 L N) := by
  rw [Subalgebra.coe_smul, omegaC, map_smul, map_smul, smul_eq_mul, omegaC]

theorem coe_stDelta (b : Fin 2 → ℕ) :
    (stDelta R j st b : Alg 2 L N) =
      Vcoup ⟨stA R st - stYc R st, stYc R st, (stA R st - stYc R st + stYc R st) * R.msq, 0⟩
        (blockSet (L := L) (N := N) j b) := by
  rw [sub_add_cancel]; rfl

/-! ### One step -/

/-- **One step of the raw flow on Gaussian integrals** (`j + 1 < N`, `ValidCore`; e.g. `ValidAt` or `ValidAtL`):
`⟨Z_j⟩_{Γ_j} = det(1 + a_j A Γ_j) e^{-u_{j+1}(Λ)} ⟨Z_{j+1}⟩_{Γ_{j+1}}`. -/
theorem rawStep_omega (hV : ValidCore R j) (H : RawInv R j st) (hD : D ∈ BSub (L := L) (N := N) j)
    (hK : K ∈ ASub (L := L) (N := N) j) (hS : SplitOK R j st) :
    omegaC (DressedFRD.kmat ((stData R j st).Gam j)) (Zin R j st g μ D K : Alg 2 L N) =
      detStep R j st * Complex.exp (-uOut R j st g μ D K) *
        omegaC (DressedFRD.kmat ((stData R j st).Gam (j + 1))) (Zout R j st g μ D K : Alg 2 L N) := by
  obtain ⟨hT, hΓ⟩ := split_kmat (L := L) (N := N) (stData R j st) j hS.1 hS.2
  rw [stData_ζZ H] at hT hΓ
  have e : stA R st - stYc R st + stYc R st = stA R st := sub_add_cancel _ _
  obtain ⟨hC, -, -, -⟩ := RawInv.covL hV H
  obtain ⟨hj2, hd, hL, hρ, -, -, -⟩ := hV
  have hjN : j < N := by omega
  have hL' : 2 ^ (2 + 2) ≤ L := by norm_num at hL ⊢; omega
  have hΔm := VfamL_mem (L := L) (N := N) hd hL hjN
    ![stA R st - stYc R st, stYc R st, stA R st * R.msq, 0]
  have hVm := VfamL_mem (L := L) (N := N) hd hL hjN ![st.z + stYc R st - stA R st,
    st.y - stYc R st, stNu R j st μ - stA R st * R.msq, stGr R j st g μ * stZ' R st ^ 2]
  have hKf := Kflat_mem hjN hΔm (eps_VfamL j _) hK
  have h := omegaC_full_step_raw j R.msq (stA R st - stYc R st) (stYc R st) (stVf R j st g μ)
    (stDelta R j st) (st.Wl + D) K (eps_VfamL j _) (fun b => coe_stDelta b)
    (DressedFRD.kmat ((stData R j st).Gam j)) (stCov R j st)
    (DressedFRD.kmat ((stData R j st).Gam (j + 1))) (by rw [e]; exact hT) (by rw [e]; exact hΓ)
    hd hL' (by omega) hC hVm.1 (add_mem H.hWl hD).1 hKf.1
  rw [e] at h
  rw [Zin, h, show (fun Y => bpow j (fun b => gexp (stDelta R j st b)) Y * K Y) =
    Kflat j (stDelta R j st) K from rfl, sum_Ip_eq_gZ, omegaC_smul', detStep, uOut, Zout, mul_assoc]

/-! ### The last step -/

/-- **The last step on Gaussian integrals** (`j + 1 = N`): `Γ_N = 0`, and
`⟨Z_{N-1}⟩_{Γ_{N-1}} = det(1 + a A Γ_{N-1}) e^{-u_N(Λ)} (1 + ũ_{N,N})`, with `ũ_{N,N}` of the
zero-mode integration of the final-scale object `out = rawStepN …` (`PtCorr2.Zero.Final`). -/
theorem lastStep_omega (hj : j + 1 = N) (H : RawInv R j st) (hS : SplitOK R j st)
    (hV : ∀ b ∈ blockIdx (L := L) (N := N) j,
      ((rawStepN R j st g μ D K).V b : Alg 2 L N) =
        Vcoup (rawStepN R j st g μ D K).κ (blockSet j b)) :
    omegaC (DressedFRD.kmat ((stData R j st).Gam j)) (Zin R j st g μ D K : Alg 2 L N) =
      detStep R j st * Complex.exp (-(rawStepN R j st g μ D K).u) *
        (1 + uFin j (rawStepN R j st g μ D K) (zmRaw R j (rawStepN R j st g μ D K).ζ)) := by
  obtain ⟨hT, hΓ⟩ := split_kmat (L := L) (N := N) (stData R j st) j hS.1 hS.2
  rw [stData_ζZ H] at hT hΓ
  have e : stA R st - stYc R st + stYc R st = stA R st := sub_add_cancel _ _
  -- `Γ_N = 0`
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
  have hstep := omegaC_gZ_step j R.msq (stA R st - stYc R st) (stYc R st) 1 1 (by norm_num)
    (stVf R j st g μ) (stDelta R j st) (st.Wl + D) K (eps_VfamL j _) (fun b => coe_stDelta b)
    (DressedFRD.kmat ((stData R j st).Gam j)) (fullCovN R j (Function.update st.ζ j (stZeta R st)))
    (DressedFRD.kmat ((stData R j st).Gam (j + 1))) (by rw [e]; exact hT) (by rw [e]; exact hΓ)
  rw [e, hG0] at hstep
  have hVs : (fun b => sigE 1 (stVf R j st g μ b)) = stVf R j st g μ := funext fun b => sigE_one' _
  have hWs : (fun b => sigE 1 ((st.Wl + D) b)) = st.Wl + D := funext fun b => sigE_one' _
  have hKs : (fun Y => sigE 1 (bpow j (fun b => gexp (stDelta R j st b)) Y * K Y)) =
      Kflat j (stDelta R j st) K := funext fun Y => sigE_one' _
  simp only [hVs, hWs, hKs, one_pow, one_smul] at hstep
  have hl := lastN_full_ZVK R hj st g μ D K
  rw [show fullCovN R j (rawStepN R j st g μ D K).ζ =
    fullCovN R j (Function.update st.ζ j (stZeta R st)) from rfl] at hl
  rw [Zin, hstep, hl, omegaC_smul', detStep, mul_assoc]
  congr 2
  have hz := congrArg ε (prop_ZNN2 (zmRaw R j (rawStepN R j st g μ D K).ζ) hV)
  rw [Suscept.ε_Rc] at hz
  rw [omegaC, expLC_zero, hz, map_sub, AlgHom.commutes, map_smul, ε_PP, smul_zero, sub_zero,
    Algebra.algebraMap_self, RingHom.id_apply]

/-! ### Telescoping -/

/-- **Telescoping of the step identities.** -/
theorem chain_omega {Γ : ℕ → Matrix (Lam 2 L N) (Lam 2 L N) ℂ} {Zs : ℕ → EvR (Lam 2 L N)}
    {c : ℕ → ℂ} (n : ℕ)
    (h : ∀ i < n, omegaC (Γ i) (Zs i : Alg 2 L N) = c i * omegaC (Γ (i + 1)) (Zs (i + 1) : Alg 2 L N)) :
    omegaC (Γ 0) (Zs 0 : Alg 2 L N) = (∏ i ∈ range n, c i) * omegaC (Γ n) (Zs n : Alg 2 L N) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih fun i hi => h i (by omega), h n (by omega), prod_range_succ, mul_assoc]

end

end PtCorr2
