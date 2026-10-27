import PtCorr.ZNNObs
import PtCorr.ConstCalc

/-!
# Lemma `lem:ZNN-obs`: the constant-field components of `Z̃^obs_{N,N}`

From `PtCorr.ZNNO_eq`, `Z̃^obs_{N,N} = e^{-u^obs_N(Λ)} 𝔼_{t_N Q_N} θ (e^{-V_N(Λ)} + K_N(Λ))`, and
the constant-field calculus of `PtCorr.ConstCalc`, with `τ = t_N/|Λ|` and `ũ = ũ_{N,N}`
(`V_N`: `λ_{a}, λ_b, r_a, r_b, η` are the couplings of `V^obs_N = VoN`, `K = K_N(Λ) = KNO`):

**Case (1)** (`c1m_ZtO_a_one`, `c1p_ZtO_b_one`, `ε_ZtO_ab_one`):
* `c1m (Z̃^obs)_a = λ_{a,N} + k_a`, `k_a = c1m K_a` (the coefficient of `ψ̄` of `(Z̃^obs)_a`
  restricted to constant fields, i.e. `e:ZNN-lambda-a`);
* `c1p (Z̃^obs)_b = -λ_{b,N} + k_b`, `k_b = c1p K_b` (the sign: `V^obs ∋ -λ_b ψ_b σ̄_b`, i.e.
  `F_b = +λ_b ψ_b`);
* `ε (Z̃^obs)_ab = q_N (1 + ũ) + (λ_{a,N} λ_{b,N} - (r_{a,N} + r_{b,N})) τ + k_ab`,
  `k_ab = ε(K_ab) - c2(K_ab) τ`.

**Case (2)** (`ε_ZtO_a_two`, `ε_ZtO_b_two`, `ε_ZtO_ab_two`), with `λ̃_a = λ_{a,N} - c2(K_a)`,
`λ̃_b = λ_{b,N} - c2(K_b)`:
* `ε (Z̃^obs)_a = γ_{a,N} (1 + ũ) + λ̃_a τ + ε(K_a)`, and for `b`;
* `ε (Z̃^obs)_ab = (q_N + γ_{a,N} γ_{b,N}) (1 + ũ) + (η_N - (r_{a,N} + r_{b,N}) + λ̃_a γ_{b,N} +
  λ̃_b γ_{a,N}) τ + k_ab`, `k_ab = ε(K_ab) - c2(K_ab) τ + γ_{a,N} ε(K_b) + γ_{b,N} ε(K_a)`.

**Bounds** (`kOne_bounds`, `kTwo_bounds`), from `‖K^obs_N‖_N ≤ e` (`Obs.comp_le`, with
`ℓ = ℓ_N`, `ℓ' = ℓ_{N ∧ j_ab}`): Case (1) `|k_a|, |k_b| ≤ e`, `|k_ab| ≤ (ℓ² + |τ|) e`;
Case (2) `|c2(K_a)|, |c2(K_b)| ≤ e`, `|ε(K_a)|, |ε(K_b)| ≤ ℓ² e`,
`|k_ab| ≤ ((|γ_{a,N}| + |γ_{b,N}|) ℓ² + ℓ² ℓ'² + |τ| ℓ'²) e`.

**Deviations** (see `Log.md`):
* the signs: the paper's `+ r C(0,0)` in the `ab` component is `- (r_a + r_b) τ` here (the zero
  mode `t_N Q_N` of `𝔼θ(ψ̄ψ) = ψ̄ψ + t_N/|Λ|`, and `r ψ̄ψ` enters `e^{-V}` with a minus sign);
  `λ_a λ_b τ` enters with `+`; in Case (2), `η τ` with `+`;
* the constant term `ε(K^{ab}_N(Λ))` (omitted in the paper) is part of `k_ab`; its size is
  `ℓ_{ab,N}^{-1} ‖K_N‖ = ℓ_N² ‖K_N‖` (Case (1)), `ℓ_N² ℓ'² ‖K_N‖` (Case (2));
* in Case (2) the corrections `λ̃ - λ = -c2(K)` are explicit.
-/

namespace PtCorr

noncomputable section

open Finset Grassmann Loc Step Obs Obs.Gen

variable {d L : ℕ} [NeZero L]

local notation "c2" => Suscept.c2

/-! ### The `k`-constants -/

section Defs

variable (d L) (N : ℕ) (msq : ℝ) (V₀ : Vcoup)

/-- Case (1): `k_a = c1m (K_N(Λ))_a`. -/
def kaOne (Vo₀ : Coup .one) (a b : Lam d L N) : ℂ :=
  c1m ((KNO d L .one N msq V₀ Vo₀ a b : SA .one (Lam d L N)).a)

/-- Case (1): `k_b = c1p (K_N(Λ))_b`. -/
def kbOne (Vo₀ : Coup .one) (a b : Lam d L N) : ℂ :=
  c1p ((KNO d L .one N msq V₀ Vo₀ a b : SA .one (Lam d L N)).b)

/-- Case (1): `k_ab = ε(K_ab) - c2(K_ab) τ`. -/
def kabOne (Vo₀ : Coup .one) (a b : Lam d L N) : ℂ :=
  ε ((KNO d L .one N msq V₀ Vo₀ a b : SA .one (Lam d L N)).ab) -
    c2 ((KNO d L .one N msq V₀ Vo₀ a b : SA .one (Lam d L N)).ab) * tau d L N msq

/-- Case (2): `λ̃_a = λ_{a,N} - c2(K_a)`. -/
def lamtA (Vo₀ : Coup .two) (a b : Lam d L N) : ℂ :=
  laOf .two (VoN d L .two N msq V₀ Vo₀ a b) -
    c2 ((KNO d L .two N msq V₀ Vo₀ a b : SA .two (Lam d L N)).a)

/-- Case (2): `λ̃_b = λ_{b,N} - c2(K_b)`. -/
def lamtB (Vo₀ : Coup .two) (a b : Lam d L N) : ℂ :=
  lbOf .two (VoN d L .two N msq V₀ Vo₀ a b) -
    c2 ((KNO d L .two N msq V₀ Vo₀ a b : SA .two (Lam d L N)).b)

/-- Case (2): `k_ab = ε(K_ab) - c2(K_ab) τ + γ_a ε(K_b) + γ_b ε(K_a)`. -/
def kabTwo (Vo₀ : Coup .two) (a b : Lam d L N) : ℂ :=
  ε ((KNO d L .two N msq V₀ Vo₀ a b : SA .two (Lam d L N)).ab) -
    c2 ((KNO d L .two N msq V₀ Vo₀ a b : SA .two (Lam d L N)).ab) * tau d L N msq +
    gaN d L .two N msq V₀ Vo₀ a b * ε ((KNO d L .two N msq V₀ Vo₀ a b : SA .two (Lam d L N)).b) +
    gbN d L .two N msq V₀ Vo₀ a b * ε ((KNO d L .two N msq V₀ Vo₀ a b : SA .two (Lam d L N)).a)

end Defs

/-! ### Auxiliary identities -/

section Aux

variable {c : Case} {N : ℕ}

theorem VfullX_univ (V : Vcoup) (W : Coup c) (a b : Lam d L N) :
    VfullX V W a b univ = emb (VE V univ) + evalO c (Coup.toV c W) a b univ := by
  rw [VfullX, splitO_univ]

/-- The components of `e^{-u^obs_N(Λ)}`. -/
theorem coe_oexp_neg_uObsN (msq : ℝ) (V₀ : Vcoup) (Vo₀ : Coup c) (a b : Lam d L N) :
    (oexp (-uObsN d L c N msq V₀ Vo₀ a b) : SA c (Lam d L N)) =
      ⟨1, algebraMap ℂ (Alg d L N) (gaN d L c N msq V₀ Vo₀ a b),
        algebraMap ℂ (Alg d L N) (gbN d L c N msq V₀ Vo₀ a b),
        algebraMap ℂ (Alg d L N) (qN d L c N msq V₀ Vo₀ a b +
          (1 / 2 : ℂ) * ((c.s + 1) * (gaN d L c N msq V₀ Vo₀ a b * gbN d L c N msq V₀ Vo₀ a b)))⟩ := by
  have h0 : bulk (-uObsN d L c N msq V₀ Vo₀ a b) = 0 := by
    rw [map_neg, bulk_uObsN, neg_zero]
  have hU : ((-uObsN d L c N msq V₀ Vo₀ a b : OE c (Lam d L N)) : SA c (Lam d L N)) =
      ⟨0, algebraMap ℂ (Alg d L N) (gaN d L c N msq V₀ Vo₀ a b),
        algebraMap ℂ (Alg d L N) (gbN d L c N msq V₀ Vo₀ a b),
        algebraMap ℂ (Alg d L N) (qN d L c N msq V₀ Vo₀ a b)⟩ := by
    rw [NegMemClass.coe_neg, coe_uObsN]
    refine SA.ext ?_ ?_ ?_ ?_ <;> simp
  rw [oexp_of_obs h0, sq]
  refine SA.ext ?_ ?_ ?_ ?_
  · rw [Subalgebra.coe_add, Subalgebra.coe_add, Subalgebra.coe_smul, SA.add_e, SA.add_e, SA.smul_e,
      OE.mul_e, hU]; simp
  · rw [Subalgebra.coe_add, Subalgebra.coe_add, Subalgebra.coe_smul, SA.add_a, SA.add_a, SA.smul_a,
      OE.mul_a, hU]; simp
  · rw [Subalgebra.coe_add, Subalgebra.coe_add, Subalgebra.coe_smul, SA.add_b, SA.add_b, SA.smul_b,
      OE.mul_b, hU]; simp
  · rw [Subalgebra.coe_add, Subalgebra.coe_add, Subalgebra.coe_smul, SA.add_ab, SA.add_ab,
      SA.smul_ab, OE.mul_ab, hU]
    simp only [zero_mul, mul_zero, zero_add, add_zero, ← map_mul]
    rw [Algebra.smul_def (c.s), ← map_mul, ← map_add, Algebra.smul_def, ← map_mul,
      OneMemClass.coe_one, SA.one_ab, zero_add, ← map_add]
    congr 1
    ring

theorem ECO_coe_a (C : Matrix (Lam d L N) (Lam d L N) ℝ) (H : OE c (Lam d L N)) :
    ((ECO C (thetaO H) : OE c (Lam d L N)) : SA c (Lam d L N)).a =
      EC C (theta ((H : SA c (Lam d L N)).a)) := rfl
theorem ECO_coe_b (C : Matrix (Lam d L N) (Lam d L N) ℝ) (H : OE c (Lam d L N)) :
    ((ECO C (thetaO H) : OE c (Lam d L N)) : SA c (Lam d L N)).b =
      EC C (theta ((H : SA c (Lam d L N)).b)) := rfl
theorem ECO_coe_ab (C : Matrix (Lam d L N) (Lam d L N) ℝ) (H : OE c (Lam d L N)) :
    ((ECO C (thetaO H) : OE c (Lam d L N)) : SA c (Lam d L N)).ab =
      EC C (theta ((H : SA c (Lam d L N)).ab)) := rfl

end Aux

/-! ### Case (1) -/

section One

variable {N : ℕ} {msq ℓ₀ : ℝ} (V₀ : Vcoup) (l₀ : ℂ) (a b : Lam d L N)

/-- The integrand `e^{-V_N(Λ)} + K_N(Λ)` of Case (1): components. -/
theorem coe_top_one (Vo : Coup .one) (K : OE .one (Lam d L N)) (V : Vcoup) :
    ((oexp (-VfullX V Vo a b univ) + K : OE .one (Lam d L N)) : SA .one (Lam d L N)) =
      ⟨(gexp (-(VE V univ : EvR (Lam d L N))) : Alg d L N) + (K : SA .one _).e,
        (gexp (-(VE V univ : EvR (Lam d L N))) : Alg d L N) * (Coup1.la Vo • psibar a) +
          (K : SA .one _).a,
        (gexp (-(VE V univ : EvR (Lam d L N))) : Alg d L N) * (-(Coup1.lb Vo • psi b)) +
          (K : SA .one _).b,
        (gexp (-(VE V univ : EvR (Lam d L N))) : Alg d L N) *
          (-(nr (Coup1.ra Vo) (Coup1.rb Vo) a b) + (Coup1.la Vo * Coup1.lb Vo) •
            (psibar a * psi b)) + (K : SA .one _).ab⟩ := by
  rw [VfullX_univ, Subalgebra.coe_add, coe_oexp_neg_emb_add (ε_VE V univ)
    (bulk_evalO _ _ a b univ), coe_evalO]
  refine SA.ext ?_ ?_ ?_ ?_
  · rfl
  · simp [evalS, Coup1.evalS_a, Coup.toV, neg_smul]
  · simp [evalS, Coup1.evalS_b, Coup.toV]
  · simp only [SA.add_ab, evalS, Coup1.evalS_a, Coup1.evalS_b, Coup1.evalS_ab, Coup.toV,
      ind_pos (mem_univ _), ind_pos (And.intro (mem_univ a) (mem_univ b)), one_smul, add_zero,
      neg_zero, map_zero, zero_add, Case.s_one]
    congr 2
    have e : (1 / 2 : ℂ) • ((-1 : ℂ) • ((-Coup1.la Vo) • psibar a * Coup1.lb Vo • psi b) +
        Coup1.lb Vo • psi b * (-Coup1.la Vo) • psibar a) =
        (Coup1.la Vo * Coup1.lb Vo) • (psibar a * psi b) := by
      simp only [smul_mul_smul_comm, psi_mul_psibar]; module
    rw [e]

variable (d L N msq) in
/-- Shorthand for the observable coupling constants `V^obs_N` of Case (1). -/
abbrev Vo1 : Coup .one := VoN d L .one N msq V₀ (initObs .one l₀) a b

/-- **`e:ZNN-lambda-a`** (Case (1)): `c1m (Z̃^obs)_a = λ_{a,N} + k_a`. -/
theorem c1m_ZtO_a_one (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hN : 1 ≤ N) (hmsq : 0 < msq)
    (hgood : ∀ j < N, GoodCov (d := d) (L := L) (N := N) j ℓ₀ (Flow.covAt d L N msq j)) :
    c1m ((ZtO d L .one N msq V₀ (initObs .one l₀) a b : SA .one (Lam d L N)).a) =
      laOf .one (VoN d L .one N msq V₀ (initObs .one l₀) a b) +
        kaOne d L N msq V₀ (initObs .one l₀) a b := by
  rw [ZNNO_eq V₀ l₀ a b hd hL hN hmsq hgood, OE.mul_a, coe_oexp_neg_uObsN, ECO_coe_a,
    coe_top_one]
  have hga : gaN d L .one N msq V₀ (initObs .one l₀) a b = 0 := by simp [gaN, gaOf]
  simp only [hga, map_zero, zero_mul, add_zero, one_mul]
  have hodd := OE.isOdd_a (oexp (-VfullX (Suscept.VN d L N msq V₀)
    (VoN d L .one N msq V₀ (initObs .one l₀) a b) a b univ) +
      KNO d L .one N msq V₀ (initObs .one l₀) a b)
  rw [coe_top_one] at hodd
  have hgev : inv' ((gexp (-(VE (Suscept.VN d L N msq V₀) univ : EvR (Lam d L N))) :
      Alg d L N)) = (gexp (-(VE (Suscept.VN d L N msq V₀) univ : EvR (Lam d L N))) : Alg d L N) :=
    Suscept.Z0_mem N _
  rw [c1m_EC_tQ_theta_of_odd _ hodd, c1m_add, mul_smul_comm, c1m_smul,
    c1m_mul_psibar hgev, Step.ε_gexp (by rw [NegMemClass.coe_neg, map_neg,
      ε_VE, neg_zero]), mul_one]
  rfl

/-- Case (1): `c1p (Z̃^obs)_b = -λ_{b,N} + k_b`. -/
theorem c1p_ZtO_b_one (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hN : 1 ≤ N) (hmsq : 0 < msq)
    (hgood : ∀ j < N, GoodCov (d := d) (L := L) (N := N) j ℓ₀ (Flow.covAt d L N msq j)) :
    c1p ((ZtO d L .one N msq V₀ (initObs .one l₀) a b : SA .one (Lam d L N)).b) =
      -lbOf .one (VoN d L .one N msq V₀ (initObs .one l₀) a b) +
        kbOne d L N msq V₀ (initObs .one l₀) a b := by
  rw [ZNNO_eq V₀ l₀ a b hd hL hN hmsq hgood, OE.mul_b, coe_oexp_neg_uObsN, ECO_coe_b,
    coe_top_one]
  have hgb : gbN d L .one N msq V₀ (initObs .one l₀) a b = 0 := by simp [gbN, gbOf]
  simp only [hgb, map_zero, zero_mul, add_zero, one_mul]
  have hodd := OE.isOdd_b (oexp (-VfullX (Suscept.VN d L N msq V₀)
    (VoN d L .one N msq V₀ (initObs .one l₀) a b) a b univ) +
      KNO d L .one N msq V₀ (initObs .one l₀) a b)
  rw [coe_top_one] at hodd
  have hgev : inv' ((gexp (-(VE (Suscept.VN d L N msq V₀) univ : EvR (Lam d L N))) :
      Alg d L N)) = (gexp (-(VE (Suscept.VN d L N msq V₀) univ : EvR (Lam d L N))) : Alg d L N) :=
    Suscept.Z0_mem N _
  rw [c1p_EC_tQ_theta_of_odd _ hodd, c1p_add, mul_neg, c1p_neg, mul_smul_comm, c1p_smul,
    c1p_mul_psi hgev, Step.ε_gexp (by rw [NegMemClass.coe_neg, map_neg,
      ε_VE, neg_zero]), mul_one]
  rfl

/-- Case (1): `ε (Z̃^obs)_ab = q_N (1 + ũ) + (λ_a λ_b - (r_a + r_b)) τ + k_ab`. -/
theorem ε_ZtO_ab_one (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hN : 1 ≤ N) (hmsq : 0 < msq)
    (hgood : ∀ j < N, GoodCov (d := d) (L := L) (N := N) j ℓ₀ (Flow.covAt d L N msq j)) :
    ε ((ZtO d L .one N msq V₀ (initObs .one l₀) a b : SA .one (Lam d L N)).ab) =
      qN d L .one N msq V₀ (initObs .one l₀) a b * (1 + Suscept.utN d L N msq V₀) +
        (laOf .one (Vo1 d L N msq V₀ l₀ a b) * lbOf .one (Vo1 d L N msq V₀ l₀ a b) -
          (raOf .one (Vo1 d L N msq V₀ l₀ a b) + rbOf .one (Vo1 d L N msq V₀ l₀ a b))) *
          tau d L N msq +
        kabOne d L N msq V₀ (initObs .one l₀) a b := by
  have he := ε_bulk_ZtO V₀ a b hd hL hN hmsq hgood (initObs .one l₀)
  rw [ZNNO_eq V₀ l₀ a b hd hL hN hmsq hgood, OE.mul_e, coe_oexp_neg_uObsN, one_mul] at he
  rw [ZNNO_eq V₀ l₀ a b hd hL hN hmsq hgood, OE.mul_ab, coe_oexp_neg_uObsN]
  have hga : gaN d L .one N msq V₀ (initObs .one l₀) a b = 0 := by simp [gaN, gaOf]
  have hgb : gbN d L .one N msq V₀ (initObs .one l₀) a b = 0 := by simp [gbN, gbOf]
  simp only [hga, hgb, map_zero, zero_mul, mul_zero, smul_zero, add_zero, one_mul]
  rw [map_add, map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, he,
    ECO_coe_ab, coe_top_one]
  have hK := (KNO d L .one N msq V₀ (initObs .one l₀) a b).par_ab
  set g : Alg d L N := (gexp (-(VE (Suscept.VN d L N msq V₀) univ : EvR (Lam d L N))) :
    Alg d L N) with hg
  have hg1 : ε g = 1 := Step.ε_gexp (by rw [NegMemClass.coe_neg, map_neg, ε_VE, neg_zero])
  have hgev : inv' g = g := Suscept.Z0_mem N _
  set Vo := VoN d L .one N msq V₀ (initObs .one l₀) a b with hVo
  set X : Alg d L N := -(nr (Coup1.ra Vo) (Coup1.rb Vo) a b) +
    (Coup1.la Vo * Coup1.lb Vo) • (psibar a * psi b) with hX
  have hXev : inv' X = X := by
    simp [hX, map_add, map_neg, map_smul, inv'_nr, inv'_psibar_psi]
  have hεX : ε X = 0 := by simp [hX, ε_nr, ε_psibar_psi]
  have hc2X : c2 X = Coup1.ra Vo + Coup1.rb Vo - Coup1.la Vo * Coup1.lb Vo := by
    rw [hX, Suscept.c2_add, c2_neg, c2_nr, Suscept.c2_smul, c2_psibar_psi]; ring
  have hev : inv' (g * X + (KNO d L .one N msq V₀ (initObs .one l₀) a b : SA .one _).ab) =
      g * X + (KNO d L .one N msq V₀ (initObs .one l₀) a b : SA .one _).ab := by
    rw [map_add, map_mul, hgev, hXev, hK]
  rw [ε_EC_tQ_theta _ hev, map_add, map_mul, hg1, hεX, Suscept.c2_add,
    c2_mul_of_even hgev hXev, hg1, hεX, hc2X, kabOne]
  simp only [laOf, lbOf, raOf, rbOf, tau]
  ring

/-- The `RcO` form of `e:ZNN-lambda-a`. -/
theorem c1m_RcO_ZtO_a_one (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hN : 1 ≤ N) (hmsq : 0 < msq)
    (hgood : ∀ j < N, GoodCov (d := d) (L := L) (N := N) j ℓ₀ (Flow.covAt d L N msq j)) :
    c1m ((RcO .one _ (ZtO d L .one N msq V₀ (initObs .one l₀) a b) : SA .one (Lam d L N)).a) =
      laOf .one (VoN d L .one N msq V₀ (initObs .one l₀) a b) +
        kaOne d L N msq V₀ (initObs .one l₀) a b := by
  rw [coe_RcO_a, c1m_Rc, c1m_ZtO_a_one V₀ l₀ a b hd hL hN hmsq hgood]

end One

/-! ### Case (2) -/

section Two

variable {N : ℕ} {msq ℓ₀ : ℝ} (V₀ : Vcoup) (l₀ : ℂ) (a b : Lam d L N)

/-- The components of `V^obs(Λ)` in Case (2) for `V`-type couplings. -/
theorem coe_evalO_two (Vo : Coup .two) :
    (evalO .two (Coup.toV .two Vo) a b univ : SA .two (Lam d L N)) =
      ⟨0, -(Coup2.la Vo • (psibar a * psi a)), -(Coup2.lb Vo • (psibar b * psi b)),
        -((Coup2.eta Vo / 2) • nx a b) + nr (Coup2.ra Vo) (Coup2.rb Vo) a b⟩ := by
  rw [coe_evalO]
  refine SA.ext ?_ ?_ ?_ ?_ <;> simp [evalS, Coup.toV, sub_eq_add_neg]

theorem even_pbp (r : ℂ) (x : Lam d L N) :
    inv' (r • (psibar x * psi x)) = r • (psibar x * psi x) := by
  rw [map_smul, inv'_psibar_psi]

variable (d L N msq) in
/-- Shorthand for the observable coupling constants `V^obs_N` of Case (2). -/
abbrev Vo2 : Coup .two := VoN d L .two N msq V₀ (initObs .two l₀) a b

/-- `ε`, `c2` of the `a`-type components of the integrand. -/
theorem εc2_top_a_two (r : ℂ) (x : Lam d L N) (V : Vcoup) (F : Alg d L N) :
    ε ((gexp (-(VE V univ : EvR (Lam d L N))) : Alg d L N) * -(-(r • (psibar x * psi x))) + F) =
      ε F ∧
    c2 ((gexp (-(VE V univ : EvR (Lam d L N))) : Alg d L N) * -(-(r • (psibar x * psi x))) + F) =
      -r + c2 F := by
  have hg1 : ε ((gexp (-(VE V univ : EvR (Lam d L N))) : Alg d L N)) = 1 :=
    Step.ε_gexp (by rw [NegMemClass.coe_neg, map_neg, ε_VE, neg_zero])
  have hgev : inv' ((gexp (-(VE V univ : EvR (Lam d L N))) : Alg d L N)) =
      (gexp (-(VE V univ : EvR (Lam d L N))) : Alg d L N) := Suscept.Z0_mem N _
  rw [neg_neg]
  refine ⟨?_, ?_⟩
  · rw [map_add, map_mul, hg1, map_smul, ε_psibar_psi]; simp
  · rw [Suscept.c2_add, c2_mul_of_even hgev (even_pbp r x), hg1, map_smul, ε_psibar_psi,
      Suscept.c2_smul, c2_psibar_psi]
    simp

/-- Case (2): `ε (Z̃^obs)_a = γ_{a,N} (1 + ũ) + λ̃_a τ + ε(K_a)`. -/
theorem ε_ZtO_a_two (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hN : 1 ≤ N) (hmsq : 0 < msq)
    (hgood : ∀ j < N, GoodCov (d := d) (L := L) (N := N) j ℓ₀ (Flow.covAt d L N msq j)) :
    ε ((ZtO d L .two N msq V₀ (initObs .two l₀) a b : SA .two (Lam d L N)).a) =
      gaN d L .two N msq V₀ (initObs .two l₀) a b * (1 + Suscept.utN d L N msq V₀) +
        lamtA d L N msq V₀ (initObs .two l₀) a b * tau d L N msq +
        ε ((KNO d L .two N msq V₀ (initObs .two l₀) a b : SA .two (Lam d L N)).a) := by
  have he := ε_bulk_ZtO V₀ a b hd hL hN hmsq hgood (initObs .two l₀)
  rw [ZNNO_eq V₀ l₀ a b hd hL hN hmsq hgood, OE.mul_e, coe_oexp_neg_uObsN, one_mul] at he
  rw [ZNNO_eq V₀ l₀ a b hd hL hN hmsq hgood, OE.mul_a, coe_oexp_neg_uObsN, one_mul, map_add,
    map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, he, ECO_coe_a]
  set H := oexp (-VfullX (Suscept.VN d L N msq V₀) (VoN d L .two N msq V₀ (initObs .two l₀) a b)
      a b univ) + KNO d L .two N msq V₀ (initObs .two l₀) a b with hH
  have hHev : inv' (H : SA .two (Lam d L N)).a = (H : SA .two (Lam d L N)).a :=
    Step.mem_Ev.1 H.a_mem
  rw [ε_EC_tQ_theta _ hHev, hH, VfullX_univ, Subalgebra.coe_add, SA.add_a,
    coe_oexp_neg_emb_add (ε_VE _ univ) (bulk_evalO _ _ a b univ), coe_evalO_two]
  obtain ⟨h1, h2⟩ := εc2_top_a_two _ a (Suscept.VN d L N msq V₀) _
  simp only at h1 h2 ⊢
  rw [h1, h2, lamtA]
  simp only [laOf, tau]
  ring

/-- Case (2): `ε (Z̃^obs)_b = γ_{b,N} (1 + ũ) + λ̃_b τ + ε(K_b)`. -/
theorem ε_ZtO_b_two (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hN : 1 ≤ N) (hmsq : 0 < msq)
    (hgood : ∀ j < N, GoodCov (d := d) (L := L) (N := N) j ℓ₀ (Flow.covAt d L N msq j)) :
    ε ((ZtO d L .two N msq V₀ (initObs .two l₀) a b : SA .two (Lam d L N)).b) =
      gbN d L .two N msq V₀ (initObs .two l₀) a b * (1 + Suscept.utN d L N msq V₀) +
        lamtB d L N msq V₀ (initObs .two l₀) a b * tau d L N msq +
        ε ((KNO d L .two N msq V₀ (initObs .two l₀) a b : SA .two (Lam d L N)).b) := by
  have he := ε_bulk_ZtO V₀ a b hd hL hN hmsq hgood (initObs .two l₀)
  rw [ZNNO_eq V₀ l₀ a b hd hL hN hmsq hgood, OE.mul_e, coe_oexp_neg_uObsN, one_mul] at he
  rw [ZNNO_eq V₀ l₀ a b hd hL hN hmsq hgood, OE.mul_b, coe_oexp_neg_uObsN, one_mul, map_add,
    map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, he, ECO_coe_b]
  set H := oexp (-VfullX (Suscept.VN d L N msq V₀) (VoN d L .two N msq V₀ (initObs .two l₀) a b)
      a b univ) + KNO d L .two N msq V₀ (initObs .two l₀) a b with hH
  have hHev : inv' (H : SA .two (Lam d L N)).b = (H : SA .two (Lam d L N)).b :=
    Step.mem_Ev.1 H.b_mem
  rw [ε_EC_tQ_theta _ hHev, hH, VfullX_univ, Subalgebra.coe_add, SA.add_b,
    coe_oexp_neg_emb_add (ε_VE _ univ) (bulk_evalO _ _ a b univ), coe_evalO_two]
  obtain ⟨h1, h2⟩ := εc2_top_a_two _ b (Suscept.VN d L N msq V₀) _
  simp only at h1 h2 ⊢
  rw [h1, h2, lamtB]
  simp only [lbOf, tau]
  ring

/-- Case (2): `ε (Z̃^obs)_ab = (q_N + γ_{a,N} γ_{b,N}) (1 + ũ) +
(η_N - (r_{a,N} + r_{b,N}) + λ̃_a γ_{b,N} + λ̃_b γ_{a,N}) τ + k_ab`. -/
theorem ε_ZtO_ab_two (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hN : 1 ≤ N) (hmsq : 0 < msq)
    (hgood : ∀ j < N, GoodCov (d := d) (L := L) (N := N) j ℓ₀ (Flow.covAt d L N msq j)) :
    ε ((ZtO d L .two N msq V₀ (initObs .two l₀) a b : SA .two (Lam d L N)).ab) =
      (qN d L .two N msq V₀ (initObs .two l₀) a b +
          gaN d L .two N msq V₀ (initObs .two l₀) a b * gbN d L .two N msq V₀ (initObs .two l₀) a b) *
          (1 + Suscept.utN d L N msq V₀) +
        (etaOf .two (Vo2 d L N msq V₀ l₀ a b) -
            (raOf .two (Vo2 d L N msq V₀ l₀ a b) + rbOf .two (Vo2 d L N msq V₀ l₀ a b)) +
            lamtA d L N msq V₀ (initObs .two l₀) a b * gbN d L .two N msq V₀ (initObs .two l₀) a b +
            lamtB d L N msq V₀ (initObs .two l₀) a b * gaN d L .two N msq V₀ (initObs .two l₀) a b) *
          tau d L N msq +
        kabTwo d L N msq V₀ (initObs .two l₀) a b := by
  have hεa := ε_ZtO_a_two V₀ l₀ a b hd hL hN hmsq hgood
  have hεb := ε_ZtO_b_two V₀ l₀ a b hd hL hN hmsq hgood
  have he := ε_bulk_ZtO V₀ a b hd hL hN hmsq hgood (initObs .two l₀)
  rw [ZNNO_eq V₀ l₀ a b hd hL hN hmsq hgood, OE.mul_e, coe_oexp_neg_uObsN, one_mul] at he
  rw [ZNNO_eq V₀ l₀ a b hd hL hN hmsq hgood, OE.mul_a, coe_oexp_neg_uObsN, one_mul, map_add,
    map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, he] at hεa
  rw [ZNNO_eq V₀ l₀ a b hd hL hN hmsq hgood, OE.mul_b, coe_oexp_neg_uObsN, one_mul, map_add,
    map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, he] at hεb
  rw [ZNNO_eq V₀ l₀ a b hd hL hN hmsq hgood, OE.mul_ab, coe_oexp_neg_uObsN, one_mul, Case.s_two,
    one_smul, map_add, map_add, map_add, map_mul, map_mul, map_mul, AlgHom.commutes,
    AlgHom.commutes, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
    RingHom.id_apply, RingHom.id_apply, he]
  set G := ECO (Suscept.tNN d L N msq • FRD.QN)
    (thetaO (oexp (-VfullX (Suscept.VN d L N msq V₀) (VoN d L .two N msq V₀ (initObs .two l₀) a b)
      a b univ) + KNO d L .two N msq V₀ (initObs .two l₀) a b)) with hG
  have hGa : ε ((G : SA .two (Lam d L N)).a) =
      lamtA d L N msq V₀ (initObs .two l₀) a b * tau d L N msq +
        ε ((KNO d L .two N msq V₀ (initObs .two l₀) a b : SA .two (Lam d L N)).a) := by
    linear_combination hεa
  have hGb : ε ((G : SA .two (Lam d L N)).b) =
      lamtB d L N msq V₀ (initObs .two l₀) a b * tau d L N msq +
        ε ((KNO d L .two N msq V₀ (initObs .two l₀) a b : SA .two (Lam d L N)).b) := by
    linear_combination hεb
  rw [hGa, hGb, hG, ECO_coe_ab]
  have hK := (KNO d L .two N msq V₀ (initObs .two l₀) a b).par_ab
  set H := oexp (-VfullX (Suscept.VN d L N msq V₀) (VoN d L .two N msq V₀ (initObs .two l₀) a b)
      a b univ) + KNO d L .two N msq V₀ (initObs .two l₀) a b with hH
  have hHev : inv' (H : SA .two (Lam d L N)).ab = (H : SA .two (Lam d L N)).ab := H.par_ab
  rw [ε_EC_tQ_theta _ hHev, hH, VfullX_univ, Subalgebra.coe_add, SA.add_ab,
    coe_oexp_neg_emb_add (ε_VE _ univ) (bulk_evalO _ _ a b univ), coe_evalO_two]
  simp only [Case.s_two, one_smul]
  set Vo := VoN d L .two N msq V₀ (initObs .two l₀) a b with hVo
  set g : Alg d L N := (gexp (-(VE (Suscept.VN d L N msq V₀) univ : EvR (Lam d L N))) :
    Alg d L N) with hg
  have hg1 : ε g = 1 := Step.ε_gexp (by rw [NegMemClass.coe_neg, map_neg, ε_VE, neg_zero])
  have hgev : inv' g = g := Suscept.Z0_mem N _
  set Pa : Alg d L N := -(Coup2.la Vo • (psibar a * psi a)) with hPa
  set Pb : Alg d L N := -(Coup2.lb Vo • (psibar b * psi b)) with hPb
  have hPa_ev : inv' Pa = Pa := by rw [hPa, map_neg, even_pbp]
  have hPb_ev : inv' Pb = Pb := by rw [hPb, map_neg, even_pbp]
  have hεPa : ε Pa = 0 := by rw [hPa, map_neg, map_smul, ε_psibar_psi]; simp
  have hεPb : ε Pb = 0 := by rw [hPb, map_neg, map_smul, ε_psibar_psi]; simp
  set Y : Alg d L N := -(-((Coup2.eta Vo / 2) • nx a b) + nr (Coup2.ra Vo) (Coup2.rb Vo) a b) +
    (1 / 2 : ℂ) • (Pa * Pb + Pb * Pa) with hY
  have hYev : inv' Y = Y := by
    rw [hY, map_add, map_neg, map_add, map_neg, map_smul, inv'_nx, inv'_nr, map_smul, map_add,
      map_mul, map_mul, hPa_ev, hPb_ev]
  have hεY : ε Y = 0 := by
    rw [hY, map_add, map_neg, map_add, map_neg, map_smul, ε_nx, ε_nr, map_smul, map_add, map_mul,
      map_mul, hεPa, hεPb]; simp
  have hc2Y : c2 Y = Coup2.ra Vo + Coup2.rb Vo - Coup2.eta Vo := by
    rw [hY, Suscept.c2_add, c2_neg, Suscept.c2_add, c2_neg, Suscept.c2_smul, c2_nx, c2_nr,
      Suscept.c2_smul, Suscept.c2_add, c2_mul_of_even hPa_ev hPb_ev,
      c2_mul_of_even hPb_ev hPa_ev, hεPa, hεPb]
    ring
  rw [map_add, map_mul, hg1, hεY, Suscept.c2_add, c2_mul_of_even hgev hYev, hg1, hεY, hc2Y,
    kabTwo]
  simp only [etaOf, raOf, rbOf, tau]
  ring

end Two

/-! ### The bounds on the `k`-constants -/

section Bounds

variable {N : ℕ} {msq ℓ₀ : ℝ} {V₀ : Vcoup} {a b : Lam d L N}

theorem le_pow_mul_of_inv_pow_mul_le {ℓ T e : ℝ} (hℓ : 0 < ℓ) (k : ℕ) (h : ℓ⁻¹ ^ k * T ≤ e) :
    T ≤ ℓ ^ k * e := by
  have hk : 0 < ℓ ^ k := pow_pos hℓ k
  have : T = ℓ ^ k * (ℓ⁻¹ ^ k * T) := by
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hℓ.ne', one_pow, one_mul]
  rw [this]
  exact mul_le_mul_of_nonneg_left h hk.le

/-- **The `k`-bounds of Case (1)** (`e:ZNN-lambda-a` and the `ab` component), from
`‖K^obs_N‖_N ≤ e`: `|k_a|, |k_b| ≤ e` and `|k_ab| ≤ (ℓ_N² + |τ|) e`. -/
theorem kOne_bounds (hℓ₀ : 0 < ℓ₀) {A : ℝ} (hA : 1 ≤ A) {e : ℝ} (he0 : 0 ≤ e)
    (Vo₀ : Coup .one)
    (hK : KnormObs .one ℓ₀ a b N A (flowO d L .one N msq V₀ Vo₀ a b N).2 ≤ ENNReal.ofReal e) :
    ‖kaOne d L N msq V₀ Vo₀ a b‖ ≤ e ∧ ‖kbOne d L N msq V₀ Vo₀ a b‖ ≤ e ∧
      ‖kabOne d L N msq V₀ Vo₀ a b‖ ≤ (ellj d L ℓ₀ N ^ 2 + ‖tau d L N msq‖) * e := by
  have hℓ := ellj_pos (d := d) (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L) : (0 : ℝ) < L)
    hℓ₀ N
  obtain ⟨h1, h2, h3⟩ := comp_le hℓ₀ hA (Suscept.isConn_top N) he0 hK
  simp only [ella, ellab, Case.p, pow_one] at h1 h2 h3
  set K := (KNO d L .one N msq V₀ Vo₀ a b : SA .one (Lam d L N))
  set ℓ := ellj d (L : ℝ) ℓ₀ N
  refine ⟨?_, ?_, ?_⟩
  · have := norm_mass1_le hℓ N (-1) K.a
    calc ‖kaOne d L N msq V₀ Vo₀ a b‖ = ‖LocObs.mass1 (-1) K.a‖ := rfl
      _ ≤ _ := this
      _ = ℓ⁻¹ * (Tj d (L : ℝ) N ℓ K.a).toReal := mul_comm _ _
      _ ≤ e := h1
  · have := norm_mass1_le hℓ N 1 K.b
    calc ‖kbOne d L N msq V₀ Vo₀ a b‖ = ‖LocObs.mass1 1 K.b‖ := rfl
      _ ≤ _ := this
      _ = ℓ⁻¹ * (Tj d (L : ℝ) N ℓ K.b).toReal := mul_comm _ _
      _ ≤ e := h2
  · have hT := le_pow_mul_of_inv_pow_mul_le hℓ 2 h3
    have hε := norm_eps_le hℓ N K.ab
    have hc := Suscept.norm_c2_le (E := Dir d) (p := pPhi d) (Lpow_pos (L := L) N) hℓ K.ab
    have hc' : ‖c2 K.ab‖ ≤ e := by
      calc ‖c2 K.ab‖ ≤ _ := hc
        _ = ℓ⁻¹ ^ 2 * (Tj d (L : ℝ) N ℓ K.ab).toReal := mul_comm _ _
        _ ≤ e := h3
    calc ‖kabOne d L N msq V₀ Vo₀ a b‖ ≤ ‖ε K.ab‖ + ‖c2 K.ab‖ * ‖tau d L N msq‖ := by
          rw [kabOne, ← norm_mul]; exact norm_sub_le _ _
      _ ≤ ℓ ^ 2 * e + e * ‖tau d L N msq‖ := by gcongr; exact hε.trans hT
      _ = (ℓ ^ 2 + ‖tau d L N msq‖) * e := by ring

/-- **The `k`-bounds of Case (2)**, from `‖K^obs_N‖_N ≤ e`, with `ℓ = ℓ_N`,
`ℓ' = ℓ_{N ∧ j_ab}`: `|c2(K_a)|, |c2(K_b)| ≤ e` (so `|λ̃ - λ| ≤ e`), `|ε(K_a)|, |ε(K_b)| ≤ ℓ² e`,
`|k_ab| ≤ ((|γ_a| + |γ_b|) ℓ² + ℓ² ℓ'² + |τ| ℓ'²) e`. -/
theorem kTwo_bounds (hℓ₀ : 0 < ℓ₀) {A : ℝ} (hA : 1 ≤ A) {e : ℝ} (he0 : 0 ≤ e)
    (Vo₀ : Coup .two)
    (hK : KnormObs .two ℓ₀ a b N A (flowO d L .two N msq V₀ Vo₀ a b N).2 ≤ ENNReal.ofReal e) :
    ‖laOf .two (VoN d L .two N msq V₀ Vo₀ a b) - lamtA d L N msq V₀ Vo₀ a b‖ ≤ e ∧
      ‖lbOf .two (VoN d L .two N msq V₀ Vo₀ a b) - lamtB d L N msq V₀ Vo₀ a b‖ ≤ e ∧
      ‖ε ((KNO d L .two N msq V₀ Vo₀ a b : SA .two (Lam d L N)).a)‖ ≤ ellj d L ℓ₀ N ^ 2 * e ∧
      ‖ε ((KNO d L .two N msq V₀ Vo₀ a b : SA .two (Lam d L N)).b)‖ ≤ ellj d L ℓ₀ N ^ 2 * e ∧
      ‖kabTwo d L N msq V₀ Vo₀ a b‖ ≤
        ((‖gaN d L .two N msq V₀ Vo₀ a b‖ + ‖gbN d L .two N msq V₀ Vo₀ a b‖) * ellj d L ℓ₀ N ^ 2 +
          ellj d L ℓ₀ N ^ 2 * ellj d L ℓ₀ (min N (coal L a b)) ^ 2 +
          ‖tau d L N msq‖ * ellj d L ℓ₀ (min N (coal L a b)) ^ 2) * e := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hℓ := ellj_pos (d := d) hL0 hℓ₀ N
  have hℓ' := ellj_pos (d := d) hL0 hℓ₀ (min N (coal L a b))
  obtain ⟨h1, h2, h3⟩ := comp_le hℓ₀ hA (Suscept.isConn_top N) he0 hK
  rw [jwedge_coe] at h3
  simp only [ella, ellab, Case.p] at h1 h2 h3
  set K := (KNO d L .two N msq V₀ Vo₀ a b : SA .two (Lam d L N))
  set ℓ := ellj d (L : ℝ) ℓ₀ N
  set ℓ' := ellj d (L : ℝ) ℓ₀ (min N (coal L a b))
  have hc2 : ∀ F : Alg d L N, ℓ⁻¹ ^ 2 * (Tj d (L : ℝ) N ℓ F).toReal ≤ e → ‖c2 F‖ ≤ e :=
    fun F h => (Suscept.norm_c2_le (E := Dir d) (p := pPhi d) (Lpow_pos (L := L) N) hℓ F).trans ((mul_comm _ _).trans_le h)
  have hεK : ∀ F : Alg d L N, ℓ⁻¹ ^ 2 * (Tj d (L : ℝ) N ℓ F).toReal ≤ e → ‖ε F‖ ≤ ℓ ^ 2 * e :=
    fun F h => (norm_eps_le hℓ N F).trans (le_pow_mul_of_inv_pow_mul_le hℓ 2 h)
  have hla : laOf .two (VoN d L .two N msq V₀ Vo₀ a b) - lamtA d L N msq V₀ Vo₀ a b = c2 K.a := by
    rw [lamtA]; ring
  have hlb : lbOf .two (VoN d L .two N msq V₀ Vo₀ a b) - lamtB d L N msq V₀ Vo₀ a b = c2 K.b := by
    rw [lamtB]; ring
  have hεa := hεK K.a h1
  have hεb := hεK K.b h2
  have hTab : (Tj d (L : ℝ) N ℓ K.ab).toReal ≤ ℓ ^ 2 * ℓ' ^ 2 * e := by
    have hp : 0 < ℓ ^ 2 * ℓ' ^ 2 := by positivity
    have e1 : (Tj d (L : ℝ) N ℓ K.ab).toReal =
        (ℓ ^ 2 * ℓ' ^ 2) * (ℓ⁻¹ ^ 2 * ℓ'⁻¹ ^ 2 * (Tj d (L : ℝ) N ℓ K.ab).toReal) := by
      field_simp
    rw [e1]
    exact mul_le_mul_of_nonneg_left h3 hp.le
  have hcab : ‖c2 K.ab‖ ≤ ℓ' ^ 2 * e := by
    have := Suscept.norm_c2_le (E := Dir d) (p := pPhi d) (Lpow_pos (L := L) N) hℓ K.ab
    calc ‖c2 K.ab‖ ≤ (Tj d (L : ℝ) N ℓ K.ab).toReal * ℓ⁻¹ ^ 2 := this
      _ ≤ (ℓ ^ 2 * ℓ' ^ 2 * e) * ℓ⁻¹ ^ 2 := by gcongr
      _ = ℓ' ^ 2 * e := by field_simp
  refine ⟨by rw [hla]; exact hc2 _ h1, by rw [hlb]; exact hc2 _ h2, hεa, hεb, ?_⟩
  have hεab := (norm_eps_le hℓ N K.ab).trans hTab
  calc ‖kabTwo d L N msq V₀ Vo₀ a b‖ ≤ ‖ε K.ab‖ + ‖c2 K.ab‖ * ‖tau d L N msq‖ +
        ‖gaN d L .two N msq V₀ Vo₀ a b‖ * ‖ε K.b‖ + ‖gbN d L .two N msq V₀ Vo₀ a b‖ * ‖ε K.a‖ := by
        rw [kabTwo, ← norm_mul, ← norm_mul, ← norm_mul]
        exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)
    _ ≤ ℓ ^ 2 * ℓ' ^ 2 * e + ℓ' ^ 2 * e * ‖tau d L N msq‖ +
        ‖gaN d L .two N msq V₀ Vo₀ a b‖ * (ℓ ^ 2 * e) +
        ‖gbN d L .two N msq V₀ Vo₀ a b‖ * (ℓ ^ 2 * e) := by gcongr
    _ = _ := by ring

end Bounds

end

end PtCorr
