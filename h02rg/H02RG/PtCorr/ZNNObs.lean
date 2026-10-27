import PtCorr.Fact
import PtCorr.Defs
import Obs.Corr

/-!
# Lemma `lem:ZNN-obs`, the identity part: `Z̃^obs_{N,N}` along the observable flow

The observable analogue of `Suscept.ZNN_eq`: iterating Proposition `prop:ZVK` with observables
(`Obs.ZVK_obs'`) along `Obs.flowO` started at `initObs c l₀` gives (`ZNNO_eq`)
`Z̃^obs_{N,N} = e^{-u^obs_N(Λ)} 𝔼_{t_N Q_N} θ (e^{-V_N(Λ)} + K_N(Λ))`,
with `V_N = V^∅_N + V^obs_N` (split evaluation) and `u^obs_N(Λ) = ∑_{j<N} u^obs_{j+1}(Λ)`
(`PtCorr.uObsN`), and the bulk part of `Z̃^obs_{N,N}` is `Z̃_{N,N}` (`bulk_ZtO`).

Ingredients:
* `ZjO j = ∑_{X ∈ 𝒫_j} e^{-V_j(Λ ∖ X)} K_j(X)` along the flow, `ZjO 0 = e^{-V_0(Λ)}`
  (`ZjO_zero`), `ZjO N = e^{-V_N(Λ)} + K_N(Λ)` (`ZjO_top`);
* one step (`ECO_ZjO`): `𝔼_{C_{j+1}} θ ZjO j = e^{-u_{j+1}|Λ|} e^{-u^obs_{j+1}(Λ)} ZjO (j+1)`,
  from `Obs.ZVK_obs'` and the factorisation `PtCorr.flowO_fact` of `K_{j+1}` over connected
  components (the flow stores `K_{j+1}` only on connected polymers, `Obs.restrO`);
* `u^obs_{j+1}(Λ)` is a scalar (its components are constants), so `θ` acts on it as the
  inclusion and `𝔼` pulls it out (`thetaO_uObsX`).

**Deviation.** The text's `Z_N` with observables is `e^{-V_N(Λ)} + K_N(Λ)` with the prefactor
`e^{-u_N}` including `u^obs`; since `Obs.flowO` does not store the `u` parts, `u^obs_N(Λ)` is
accumulated separately (`PtCorr.uObsN`), and the factorisation along the flow in Case (2) needs
the relaxed supports of `PtCorr.Fact` (the text does not address the nonlocal `η` term).
-/

namespace PtCorr

noncomputable section

open Finset Grassmann Loc Step Obs Obs.Gen

variable {d L : ℕ} [NeZero L] {c : Case}

/-! ### Scalar elements -/

section Scalar

variable {Λ : Type*} [DecidableEq Λ]

end Scalar

theorem thetaO_uObsX {N : ℕ} (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (Vo : Coup c)
    (K : Finset (Lam d L N) → OE c (Lam d L N)) (a b : Lam d L N) :
    thetaO (uObsX j C Vo K a b univ) = inclO (uObsX j C Vo K a b univ) := by
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;>
    simp only [coe_thetaO, coe_inclO, thetaS_e, thetaS_a, thetaS_b, thetaS_ab, inclS_e, inclS_a,
      inclS_b, inclS_ab, coe_uObsX_univ, AlgHom.commutes, map_zero]

theorem Coup.toV_toV (W : Coup c) : Coup.toV c (Coup.toV c W) = Coup.toV c W := by
  cases c <;> rfl

theorem VfullX_toV {N : ℕ} (V : Vcoup) (W : Coup c) (a b : Lam d L N) (X : Finset (Lam d L N)) :
    VfullX V (Coup.toV c W) a b X = VfullX V W a b X := by
  rw [VfullX, VfullX, Coup.toV_toV]

theorem VfullX_empty {N : ℕ} (V : Vcoup) (W : Coup c) (a b : Lam d L N) :
    VfullX V W a b (∅ : Finset (Lam d L N)) = 0 := by
  rw [VfullX, Suscept.VE_empty, map_zero, splitO_empty, add_zero]

/-! ### `Z_j` along the observable flow -/

variable (d L c) in
/-- `Z_j = ∑_{X ∈ 𝒫_j} e^{-V_j(Λ ∖ X)} K_j(X)` along the observable flow. -/
def ZjO (N : ℕ) (msq : ℝ) (V₀ : Vcoup) (Vo₀ : Coup c) (a b : Lam d L N) (j : ℕ) :
    OE c (Lam d L N) :=
  ∑ X ∈ Pj j univ, oexp (-VfullX (Flow.flowN d L N msq V₀ j).1
    (flowO d L c N msq V₀ Vo₀ a b j).1 a b (univ \ X)) * KextG j (flowO d L c N msq V₀ Vo₀ a b j).2 X

section Flow

variable {N : ℕ} {msq : ℝ} (V₀ : Vcoup) (Vo₀ : Coup c) (a b : Lam d L N)

theorem KextG_zero_of_nonempty {j : ℕ} {X : Finset (Lam d L N)} (hX : X.Nonempty) :
    KextG j (0 : Finset (Lam d L N) → OE c (Lam d L N)) X = 0 := by
  obtain ⟨x, hx⟩ := hX
  refine prod_eq_zero (i := compOf j X (blk j x)) ?_ rfl
  exact mem_image.2 ⟨blk j x, mem_blocks.2 ⟨x, hx, rfl⟩, rfl⟩

theorem KextG_empty' {j : ℕ} (K : Finset (Lam d L N) → OE c (Lam d L N)) :
    KextG j K ∅ = 1 := by
  simp [KextG, comp_empty]

/-- `Z_0 = e^{-V_0(Λ)}` (`K_0 = 0`). -/
theorem ZjO_zero : ZjO d L c N msq V₀ Vo₀ a b 0 = oexp (-VfullX V₀ Vo₀ a b univ) := by
  rw [ZjO, sum_eq_single ∅]
  · rw [sdiff_empty, KextG_empty', mul_one]; rfl
  · intro X _ hX
    rw [show (flowO d L c N msq V₀ Vo₀ a b 0).2 = 0 from rfl,
      KextG_zero_of_nonempty (nonempty_iff_ne_empty.2 hX), mul_zero]
  · intro h; exact absurd (mem_Pj.2 ⟨empty_subset _, isPolymer_empty 0⟩) h

/-- `Z_N = e^{-V_N(Λ)} + K_N(Λ)`, since `𝒫_N(Λ) = {∅, Λ}`. -/
theorem ZjO_top : ZjO d L c N msq V₀ Vo₀ a b N =
    oexp (-VfullX (Suscept.VN d L N msq V₀) (VoN d L c N msq V₀ Vo₀ a b) a b univ) +
      KNO d L c N msq V₀ Vo₀ a b := by
  have hne : (∅ : Finset (Lam d L N)) ≠ univ := (univ_nonempty.ne_empty).symm
  rw [ZjO, Suscept.Pj_top, sum_pair hne, sdiff_empty, sdiff_self, bot_eq_empty, VfullX_empty,
    neg_zero, oexp_zero, KextG_empty', mul_one, one_mul, KextG,
    comp_of_isConn (Suscept.isConn_top N), prod_singleton]

variable {V₀ a b}

/-- The factorised `K_{j+1}` agrees with the extension of its restriction to connected polymers. -/
theorem KnextO_eq_KextG_restrO {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℝ} {Vb : Vcoup}
    {Vo : Coup c} {K : Finset (Lam d L N) → OE c (Lam d L N)} {U : Finset (Lam d L N)}
    (hU : IsPolymer (j + 1) U)
    (hfac : KnextO j C Vb Vo K a b U = KextG (j + 1) (KnextO j C Vb Vo K a b) U) :
    KnextO j C Vb Vo K a b U = KextG (j + 1) (restrO (j + 1) (KnextO j C Vb Vo K a b)) U := by
  rw [hfac]
  exact prod_congr rfl fun Y hY => (restrO_of_conn _ (isConn_of_mem_comp hU hY)).symm

variable {ℓ₀ : ℝ} (l₀ : ℂ)

/-- **One step** along the observable flow (Proposition `prop:ZVK`):
`𝔼_{C_{j+1}} θ Z_j = e^{-u_{j+1}|Λ|} e^{-u^obs_{j+1}(Λ)} Z_{j+1}`. -/
theorem ECO_ZjO (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L)
    (hgood : ∀ k < N, GoodCov (d := d) (L := L) (N := N) k ℓ₀ (Flow.covAt d L N msq k))
    {j : ℕ} (hj : j < N) :
    ECO (Flow.covAt d L N msq j) (thetaO (ZjO d L c N msq V₀ (initObs c l₀) a b j)) =
      (algebraMap ℂ (OE c (Lam d L N))
          (Complex.exp (-(Flow.uflow d L N msq V₀ j * Fintype.card (Lam d L N)))) *
        oexp (-uObsX j (Flow.covAt d L N msq j) (flowO d L c N msq V₀ (initObs c l₀) a b j).1
          (flowO d L c N msq V₀ (initObs c l₀) a b j).2 a b univ)) *
      ZjO d L c N msq V₀ (initObs c l₀) a b (j + 1) := by
  rw [ZjO, ZVK_obs']
  have hu : (uVb j (Flow.covAt d L N msq j) (Flow.flowN d L N msq V₀ j).1
      (flowO d L c N msq V₀ (initObs c l₀) a b j).2) =
      (Flow.uflow d L N msq V₀ j, (Flow.flowN d L N msq V₀ (j + 1)).1) := by
    rw [uVb, bulkK_flowO]; rfl
  rw [hu, card_univ]
  congr 1
  rw [ZjO]
  refine sum_congr rfl fun U hU => ?_
  have hUp : IsPolymer (j + 1) U := (mem_Pj.1 hU).2
  rw [flowO_succ, KnextO_eq_KextG_restrO hUp (flowO_fact hd hL hgood hj hUp), VfullX_toV]

/-- **Iteration**: `𝔼_{C_1 + ⋯ + C_j} θ Z_0 = e^{-(u_1 + ⋯ + u_j)|Λ|} e^{-u^obs_{≤j}(Λ)} Z_j`. -/
theorem ECO_partial (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L)
    (hgood : ∀ k < N, GoodCov (d := d) (L := L) (N := N) k ℓ₀ (Flow.covAt d L N msq k)) :
    ∀ j ≤ N, ECO (∑ i ∈ range j, Flow.covAt d L N msq i)
        (thetaO (oexp (-VfullX V₀ (initObs c l₀) a b univ))) =
      Complex.exp (-((∑ i ∈ range j, Flow.uflow d L N msq V₀ i) * Fintype.card (Lam d L N))) •
        (oexp (-∑ i ∈ range j, uObsX i (Flow.covAt d L N msq i)
            (flowO d L c N msq V₀ (initObs c l₀) a b i).1
            (flowO d L c N msq V₀ (initObs c l₀) a b i).2 a b univ) *
          ZjO d L c N msq V₀ (initObs c l₀) a b j) := by
  intro j
  induction j with
  | zero =>
    intro _
    simp only [sum_range_zero, zero_mul, neg_zero, Complex.exp_zero, one_smul, oexp_zero,
      one_mul, ZjO_zero]
    exact ECO_zero_thetaO _
  | succ j ih =>
    intro hj
    set U := ∑ i ∈ range j, uObsX i (Flow.covAt d L N msq i)
      (flowO d L c N msq V₀ (initObs c l₀) a b i).1
      (flowO d L c N msq V₀ (initObs c l₀) a b i).2 a b univ with hUdef
    set u := uObsX j (Flow.covAt d L N msq j) (flowO d L c N msq V₀ (initObs c l₀) a b j).1
      (flowO d L c N msq V₀ (initObs c l₀) a b j).2 a b univ with hudef
    have hU0 : bulk U = 0 := by
      rw [hUdef, map_sum]; exact sum_eq_zero fun i _ => bulk_uObsX _ _ _ _ _ _ _
    have hu0 : bulk u = 0 := bulk_uObsX _ _ _ _ _ _ _
    have hθU : thetaO (oexp (-U)) = inclO (oexp (-U)) := by
      rw [thetaO_oexp (ε_bulk_eq_zero_of_obs (by rw [map_neg, hU0, neg_zero])),
        inclO_oexp (ε_bulk_eq_zero_of_obs (by rw [map_neg, hU0, neg_zero])), map_neg, map_neg,
        hUdef, map_sum, map_sum]
      simp only [thetaO_uObsX]
    rw [sum_range_succ, ← ECO_thetaO_comp, ih (by omega), map_smul, map_smul, map_mul, hθU,
      ECO_inclO_mul, ECO_ZjO l₀ hd hL hgood (by omega), sum_range_succ, sum_range_succ, ← hudef,
      neg_add, oexp_add (isNilpotent_of_obs (by rw [map_neg, hU0, neg_zero]))
        (isNilpotent_of_obs (by rw [map_neg, hu0, neg_zero])),
      add_mul, neg_add, Complex.exp_add, mul_smul, Algebra.algebraMap_eq_smul_one]
    simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_assoc]
    rfl

end Flow

/-! ### Lemma `lem:ZNN-obs`: the identity -/

section Main

variable {N : ℕ} {msq ℓ₀ : ℝ} (V₀ : Vcoup) (l₀ : ℂ) (a b : Lam d L N)

/-- **Lemma `lem:ZNN-obs`**, identity part (`e:ZNN-def` with observables):
`Z̃^obs_{N,N} = e^{-u^obs_N(Λ)} 𝔼_{t_N Q_N} θ (e^{-V_N(Λ)} + K_N(Λ))`, where
`Z̃^obs_{N,N} = e^{u_N |Λ|} 𝔼_C θ e^{-V_0(Λ)}`, `V_j = V^∅_j + V^obs_j`. -/
theorem ZNNO_eq (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hN : 1 ≤ N) (hmsq : 0 < msq)
    (hgood : ∀ j < N, GoodCov (d := d) (L := L) (N := N) j ℓ₀ (Flow.covAt d L N msq j)) :
    ZtO d L c N msq V₀ (initObs c l₀) a b =
      oexp (-uObsN d L c N msq V₀ (initObs c l₀) a b) *
        ECO (Suscept.tNN d L N msq • FRD.QN)
          (thetaO (oexp (-VfullX (Suscept.VN d L N msq V₀) (VoN d L c N msq V₀ (initObs c l₀) a b)
              a b univ) + KNO d L c N msq V₀ (initObs c l₀) a b)) := by
  have hU0 : bulk (uObsN d L c N msq V₀ (initObs c l₀) a b) = 0 := bulk_uObsN _ _ _ _ _
  have hθU : thetaO (oexp (-uObsN d L c N msq V₀ (initObs c l₀) a b)) =
      inclO (oexp (-uObsN d L c N msq V₀ (initObs c l₀) a b)) := by
    rw [thetaO_oexp (ε_bulk_eq_zero_of_obs (by rw [map_neg, hU0, neg_zero])),
      inclO_oexp (ε_bulk_eq_zero_of_obs (by rw [map_neg, hU0, neg_zero])), map_neg, map_neg,
      uObsN, map_sum, map_sum]
    simp only [thetaO_uObsX]
  rw [ZtO, Suscept.Cov_eq hmsq hN, ← ECO_thetaO_comp, ECO_partial (V₀ := V₀) (a := a) (b := b) l₀ hd hL hgood N le_rfl,
    map_smul, map_smul, map_mul, ← uObsN, hθU, ECO_inclO_mul, ZjO_top, smul_smul,
    ← Complex.exp_add, Suscept.uN, add_neg_cancel, Complex.exp_zero, one_smul]

/-- The bulk part of `Z̃^obs_{N,N}` is `Z̃_{N,N}` (for any observable initial condition). -/
theorem bulk_ZtO (Vo₀ : Coup c) :
    ((bulk (ZtO d L c N msq V₀ Vo₀ a b) : EvR (Lam d L N)) : Alg d L N) =
      Suscept.ZtNN d L N msq V₀ := by
  rw [ZtO, map_smul, bulk_ECO, bulk_thetaO, bulk_oexp (ε_neg_VfullX a b _ _ _), map_neg,
    bulk_VfullX, Subalgebra.coe_smul, coe_ECE, coe_thetaE, Suscept.ZtNN, Suscept.ZNN]
  rfl

/-- `ε(Z̃^obs_{N,N})_∅ = 1 + ũ_{N,N}`. -/
theorem ε_bulk_ZtO (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hN : 1 ≤ N) (hmsq : 0 < msq)
    (hgood : ∀ j < N, GoodCov (d := d) (L := L) (N := N) j ℓ₀ (Flow.covAt d L N msq j))
    (Vo₀ : Coup c) :
    ε ((ZtO d L c N msq V₀ Vo₀ a b : SA c (Lam d L N)).e) = 1 + Suscept.utN d L N msq V₀ := by
  rw [← coe_bulk, bulk_ZtO, Suscept.ε_ZtNN hd hL hN hmsq hgood V₀]

end Main

end

end PtCorr
