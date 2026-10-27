import Step2.Lip.FlowLipSig
import Step2.FlowCont.FlowCont

/-!
# The normalised step map (Lipschitz bounds, part 2)

The raw step `rawStep` works with raw objects, normalised by the field strength `Z_j`. By the
equivariance of the step under field rescaling (`Step2.Lip.FlowLipSig`), the raw outputs, rescaled by
any `u ∈ ℂ` with `u² = Z_{j+1}`, are the outputs of a **normalised step**, which only depends on

* the normalised couplings `ẑ = z_j/Z_j`, `ŷ = y_j/Z_j`, the coordinates `g`, `μ`, and
  `ŵ = Z_{j+1} w^{(1)}_j / L^{2j}`;
* the normalised covariance `Ĉ = Z_{j+1} Γ^int_{j+1} = u² C` (`= Cdr`, `prop:C5`);
* the rescaled `Ŵ = σ_{u⁻¹} W^lin_j`, `D̂ = σ_{u⁻¹} D_j`, `K̂ = σ_{u⁻¹} K_j`.

This is `rawStep_norm`. In particular `Z_j` itself (which depends on the whole history) only
enters through `u`, i.e. through the rescaling of the inputs and outputs.
-/

namespace Step2

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

section NStep

variable (R : RGPar d L N) (j : ℕ)

/-- The absorbed coupling `ζ_j = clamp_ρ(ẑ + ŷ)`. -/
def nZeta (z y : ℂ) : ℂ := clampDisk R.ρ (z + y)

/-- The coupling vector of `V♭`, normalised by `Z_{j+1}`. -/
def nVec (z y : ℂ) (g μ : ℝ) (w : ℂ) : Fin 4 → ℂ :=
  ![(z + clampDisk R.ρ y - nZeta R z y) * (1 + nZeta R z y)⁻¹,
    (y - clampDisk R.ρ y) * (1 + nZeta R z y)⁻¹,
    (μ : ℂ) / (L : ℂ) ^ (2 * j) - nZeta R z y * (1 + nZeta R z y)⁻¹ * R.msq,
    (g : ℂ) / (1 + nCor (μ : ℂ) w)]

/-- The coupling vector of `Δ`, normalised by `Z_{j+1}`. -/
def nDel (z y : ℂ) : Fin 4 → ℂ :=
  ![(nZeta R z y - clampDisk R.ρ y) * (1 + nZeta R z y)⁻¹,
    clampDisk R.ρ y * (1 + nZeta R z y)⁻¹,
    nZeta R z y * (1 + nZeta R z y)⁻¹ * R.msq, 0]

variable (C : Matrix (Lam d L N) (Lam d L N) ℂ) (z y : ℂ) (g μ : ℝ) (w : ℂ) (W D : Fam d L N)
  (K : Act d L N)

/-- `K♭`, normalised. -/
def nKf : Act d L N := Kflat j (VfamL j (nDel R z y)) K

/-- The output couplings `(z, y, ν)_{j+1}/Z_{j+1}`, `g_{j+1}/Z_{j+1}²` (before the absorption of
`ζ_{j+1}`). -/
def nKap : Fin 4 → ℂ := cvec4 (blockSet (L := L) (N := N) (j + 1) 0) R.i₀
  (Vnext2 j C (VfamL j (nVec R j z y g μ w)) (W + D) (nKf R j z y K) 0)

/-- The normalised `𝒲^lin_{j+1}`. -/
def nWl : Fam d L N := WlinNext j C (VfamL j (nVec R j z y g μ w)) W

/-- The normalised `D_{j+1}`. -/
def nD : Fam d L N := Dnext j C (VfamL j (nVec R j z y g μ w)) W D

/-- The normalised `K_{j+1}`. -/
def nK : Act d L N :=
  Kconn (j + 1) (Kplus j C (VfamL j (nVec R j z y g μ w)) (W + D) (nKf R j z y K))

end NStep

/-! ### The raw step is the rescaled normalised step -/

section Equiv

variable {R : RGPar d L N} {j : ℕ} {st : RawSt d L N}

theorem absorbZeta_eq (R : RGPar d L N) (st : RawSt d L N) :
    absorbZeta R st.Z (st.z + st.y) = nZeta R (st.z / st.Z) (st.y / st.Z) := by
  rw [absorbZeta, nZeta, add_div]

/-- The data of the normalisation of step `j`: `u² = Z_{j+1}`, and the rescaled inputs. -/
structure NormData (R : RGPar d L N) (j : ℕ) (st : RawSt d L N) (u : ℂ) (D : Fam d L N)
    (K : Act d L N) (Wn Dn : Fam d L N) (Kn : Act d L N) : Prop where
  hZ : st.Z ≠ 0
  hζ : 1 + absorbZeta R st.Z (st.z + st.y) ≠ 0
  hu : u ^ 2 = st.Z * (1 + absorbZeta R st.Z (st.z + st.y))
  hW : st.Wl = sigF u Wn
  hD : D = sigF u Dn
  hK : K = sigK u Kn

variable {u : ℂ} {D : Fam d L N} {K : Act d L N} {Wn Dn : Fam d L N} {Kn : Act d L N}

namespace NormData

variable (H : NormData R j st u D K Wn Dn Kn)
include H

theorem vec_eq (g μ : ℝ) :
    cvV R j st g μ = vsc u (nVec R j (st.z / st.Z) (st.y / st.Z) g μ
        (st.Z * (1 + absorbZeta R st.Z (st.z + st.y)) * st.w1 / (L : ℂ) ^ (2 * j))) := by
  simp only [cvV, cYc, cA, cNu, cGr, cZ1, cζ]
  have hZ := H.hZ
  have hζ := H.hζ
  have hu := H.hu
  rw [absorbZeta_eq] at hζ hu ⊢
  have hn : nCor ((μ : ℂ) * (st.Z * (1 + nZeta R (st.z / st.Z) (st.y / st.Z))) /
      (L : ℂ) ^ (2 * j)) st.w1 = nCor (μ : ℂ)
        (st.Z * (1 + nZeta R (st.z / st.Z) (st.y / st.Z)) * st.w1 / (L : ℂ) ^ (2 * j)) := by
    unfold nCor; congr 1; ring
  have hu4 : u ^ 4 = (st.Z * (1 + nZeta R (st.z / st.Z) (st.y / st.Z))) ^ 2 := by
    rw [show u ^ 4 = (u ^ 2) ^ 2 by ring, hu]
  have hL : (L : ℂ) ^ (2 * j) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne L))
  funext a
  fin_cases a
  · simp only [vsc, nVec, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    rw [hu]; field_simp
  · simp only [vsc, nVec, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [hu]; field_simp
  · simp only [vsc, nVec, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
    rw [hu]; field_simp
  · simp only [vsc, nVec, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
    rw [hu4, hn]; ring

theorem del_eq : cvΔ R st = vsc u (nDel R (st.z / st.Z) (st.y / st.Z)) := by
  simp only [cvΔ, cYc, cA, cζ]
  have hZ := H.hZ
  have hζ := H.hζ
  have hu := H.hu
  rw [absorbZeta_eq] at hζ hu ⊢
  funext a
  fin_cases a
  · simp only [vsc, nDel, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    rw [hu]; field_simp
  · simp only [vsc, nDel, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [hu]; field_simp
  · simp only [vsc, nDel, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
    rw [hu]; field_simp
  · simp [vsc, nDel]

end NormData

/-- The normalised covariance `Ĉ = u² C = Z_{j+1} C`. -/
abbrev nCov (R : RGPar d L N) (j : ℕ) (st : RawSt d L N) (u : ℂ) :
    Matrix (Lam d L N) (Lam d L N) ℂ :=
  (u ^ 2) • rawCov R j (Function.update st.ζ j (absorbZeta R st.Z (st.z + st.y)))

/-- `ŵ = Z_{j+1} w^{(1)}_j / L^{2j}`. -/
abbrev nW1 (R : RGPar d L N) (j : ℕ) (st : RawSt d L N) : ℂ :=
  st.Z * (1 + absorbZeta R st.Z (st.z + st.y)) * st.w1 / (L : ℂ) ^ (2 * j)

/-- **The raw step is the rescaled normalised step.** With `u² = Z_{j+1}` and the inputs
`W^lin_j = σ_u Ŵ`, `D_j = σ_u D̂`, `K_j = σ_u K̂`, the outputs of `rawStep` are
`κ = (u² κ̂₀, u² κ̂₁, u² κ̂₂, u⁴ κ̂₃)`, `W^lin_{j+1} = σ_u Ŵ'`, `D_{j+1} = σ_u D̂'`,
`K_{j+1} = σ_u K̂'`, with the normalised step at `Ĉ = u² C`. -/
theorem rawStep_norm (H : NormData R j st u D K Wn Dn Kn) (g μ : ℝ) :
    let zh := st.z / st.Z
    let yh := st.y / st.Z
    let wh := nW1 R j st
    let Ch := nCov R j st u
    let out := rawStep R j st g μ D K
    cκ R j st g μ D K = vsc u (nKap R j Ch zh yh g μ wh Wn Dn Kn) ∧
      out.st.Wl = sigF u (nWl R j Ch zh yh g μ wh Wn) ∧
      out.D = sigF u (nD R j Ch zh yh g μ wh Wn Dn) ∧
      out.K = sigK u (nK R j Ch zh yh g μ wh Wn Dn Kn) := by
  intro zh yh wh Ch out
  have hVf : VfamL (d := d) (L := L) (N := N) j (cvV R j st g μ) =
      sigF u (VfamL j (nVec R j zh yh g μ wh)) := by
    rw [H.vec_eq g μ, VfamL_vsc]
  have hΔf : VfamL (d := d) (L := L) (N := N) j (cvΔ R st) = sigF u (VfamL j (nDel R zh yh)) := by
    rw [H.del_eq, VfamL_vsc]
  have hKf : Kflat j (sigF u (VfamL j (nDel R zh yh))) (sigK u Kn) =
      sigK u (nKf R j zh yh Kn) :=
    Kflat_sig j Kn u _ (eps_VfamL j _)
  have hWD : st.Wl + D = sigF u (Wn + Dn) := by rw [H.hW, H.hD, sigF_add]
  have hε := fun b => eps_VfamL (d := d) (L := L) (N := N) j (nVec R j zh yh g μ wh) b
  have hC : cC R j st = rawCov R j (Function.update st.ζ j (absorbZeta R st.Z (st.z + st.y))) :=
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [cκ]
    rw [hVf, hΔf, H.hK, hKf, hWD, hC, Vnext2_sig, coe_sigE, cvec4_sig]
    rfl
  · show WlinNext j (cC R j st) (VfamL j (cvV R j st g μ)) st.Wl = _
    rw [hVf, H.hW, WlinNext_sig]
    rfl
  · show Dnext j (cC R j st) (VfamL j (cvV R j st g μ)) st.Wl D = _
    rw [hVf, H.hW, H.hD, Dnext_sig]
    rfl
  · show Kconn (j + 1) (Kplus j (cC R j st) (VfamL j (cvV R j st g μ)) (st.Wl + D)
      (Kflat j (VfamL j (cvΔ R st)) K)) = _
    rw [hVf, hΔf, H.hK, hKf, hWD, Kplus_sig j _ _ _ _ u hε, Kconn_sig]
    rfl

end Equiv

end

end Step2
