import Spin2.Pair.PairDef5c

/-!
# `PairDefSizesNS`: the gradient Pauli defect discharged

The gradient Pauli defect of `PairDefSizesNS` (`Spin2/Pair/PairDef5c`),
`𝔡_k − M₄_k·det_k = ∑_B∑_{u,v∈{a,b}}c_{uv}(V'_k(B)_{ab})(C_k(u,v) − C_k(a,a))` (`pdefAB2_hVR_sub`),
is of gradient type: with `g₁ = c_{ab} + c_{bb}`, `g₂ = c_{ba} + c_{bb}`, `g₃ = c_{bb}`,
`∑_{u,v}c_{uv}(C_{uv} − C_{aa}) = g₁(C_{ab} − C_{aa}) + g₂(C_{ba} − C_{aa}) + g₃(C_{aa} + C_{bb} − C_{ab} − C_{ba})`,
and with `|C_{ab} − C_{aa}| ≤ ns_k²/L^{k+1}`, `|C_{aa} + C_{bb} − C_{ab} − C_{ba}| ≤ (ns_k/L^{k+1})²` (`n = |w|`,
`n ≤ 2|a − b|_∞ ≤ 2|e|₁`) each block term is `≤ (2/L)·gradM4Sz` (**`pd5_gradDef_block_le`**), and the
block gradient sizes are bounded by `MasterCore.vhistG` and `pl6_grad`.

* **`PairDefSizesNF c_d`** (named): `PairDefSizesNS` without the gradient defect (the `ε`-tadpole
  `εF_{C_k}(V'_{k,ab}, V'_{k,∅})` and the last-step defect `lastDefR`).
* **`pairDefSizesNS_of_NF_at`**, **`pairDefSizesNS_of_NF_MFC`** (canonical constants):
  `PairDefSizesNF c_d ⇒ PairDefSizesNS (c_d + pd5Cp M C₁k C₁w m̄)`,
  `pd5Cp = (4/L)(21/16)c_u c_G(2k₀ + m̄(6c²G₂ + 2cε))` (`c_G = pl6cG`): `sp_k = (4/L)gradRHS_k`,
  `gradRHS_k ≤ s_k²|β_{k+1}|V c_G FO(k)` (`pl6_grad`), the weight bound
  `s_k²|β_{k+1}| ≤ (21/32)c_u‖M‖r_k`, `r_kFO(k) ≤ 2NF(k)` (`pl6_mul_FO`), `pairLoop2_sum_le`.
* **`pairDefSizesR3P_of_NF_MFC`**: `PairDefSizesNF c_d ⇒ PairDefSizesR3P (c_d + pd5Cp + pd5CS)`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs2

variable {L N : ℕ} [NeZero L]

/-- `|a − b|_∞ ≤ |e_{\{a\}}|₁`. -/
theorem pd5_supNorm_le_eN1 (a b : Lam 2 L N) :
    ((supNorm (a - b) : ℕ) : ℝ) ≤ eN1 ({a} : Finset (Lam 2 L N)) a b := by
  have hb : base ({a} : Finset (Lam 2 L N)) = a := by
    unfold base
    rw [dif_pos (Finset.singleton_nonempty a)]
    exact Finset.mem_singleton.1 (Finset.singleton_nonempty a).choose_spec
  have h0 : ∀ i, (rep (a - a) i : ℤ) = 0 := fun i => by
    have hp := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) N
    have hz : supNormZ (0 : Zd 2) = 0 := by simp [supNormZ]
    rw [sub_self, ← eq_rep prj_zero (by rw [hz]; omega)]
    rfl
  have hi : ∀ i, |eV ({a} : Finset (Lam 2 L N)) a b i| = (((rep (b - a) i).natAbs : ℕ) : ℝ) := by
    intro i
    unfold eV lift
    rw [hb, h0 i, Int.cast_zero, sub_zero, Nat.cast_natAbs, Int.cast_abs]
  rw [supNorm_sub_comm, ← supNormZ_rep_eq_supNorm]
  unfold supNormZ eN1
  obtain ⟨i, -, hi'⟩ := Finset.exists_mem_eq_sup (univ : Finset (Fin 2)) univ_nonempty
    (fun i => (rep (b - a) i).natAbs)
  rw [hi', ← hi i]
  exact single_le_sum (f := fun i => |eV ({a} : Finset (Lam 2 L N)) a b i|)
    (fun i _ => abs_nonneg _) (mem_univ i)

/-- **One block of the gradient Pauli defect** (pure): `|∑_{u,v}c_{uv}(C_{uv} − C_{aa})| ≤ (2/L)gradM4Sz`. -/
theorem pd5_gradDef_block_le {a b : Lam 2 L N} (hab : a ≠ b) (C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ)
    (F : Alg 2 L N) {h s D1 D2 : ℝ} (hs : 0 ≤ s) (hh : 0 ≤ h)
    (h1 : ‖C a b - C a a‖ ≤ D1) (h2 : ‖C b a - C a a‖ ≤ D1)
    (h3 : ‖C a a + C b b - C a b - C b a‖ ≤ D2)
    (hD1 : D1 ≤ 2 / L * (s * (eN1 ({a} : Finset (Lam 2 L N)) a b * s * h⁻¹)))
    (hD2 : D2 ≤ 2 / L * ((eN1 ({a} : Finset (Lam 2 L N)) a b * s * h⁻¹) *
      (eN1 ({a} : Finset (Lam 2 L N)) a b * s * h⁻¹))) :
    ‖∑ u ∈ ({a, b} : Finset (Lam 2 L N)), ∑ v ∈ ({a, b} : Finset (Lam 2 L N)),
        cfAB2 u v F * (C u v - C a a)‖ ≤ 2 / L * gradM4Sz {a} a b h s F := by
  rw [sum_pair hab, sum_pair hab, sum_pair hab]
  set g1 := cfAB2 a b F + cfAB2 b b F
  set g2 := cfAB2 b a F + cfAB2 b b F
  set g3 := cfAB2 b b F
  have e : cfAB2 a a F * (C a a - C a a) + cfAB2 a b F * (C a b - C a a) +
      (cfAB2 b a F * (C b a - C a a) + cfAB2 b b F * (C b b - C a a)) =
      g1 * (C a b - C a a) + g2 * (C b a - C a a) + g3 * (C a a + C b b - C a b - C b a) := by ring
  rw [e]
  have hE := eN1_nonneg ({a} : Finset (Lam 2 L N)) a b
  have hD10 : 0 ≤ D1 := (norm_nonneg _).trans h1
  have hD20 : 0 ≤ D2 := (norm_nonneg _).trans h3
  have k1 : ‖g1 * (C a b - C a a)‖ ≤ ‖g1‖ * D1 := by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
  have k2 : ‖g2 * (C b a - C a a)‖ ≤ ‖g2‖ * D1 := by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
  have k3 : ‖g3 * (C a a + C b b - C a b - C b a)‖ ≤ ‖g3‖ * D2 := by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
  have n3 := norm_add₃_le (a := g1 * (C a b - C a a)) (b := g2 * (C b a - C a a))
    (c := g3 * (C a a + C b b - C a b - C b a))
  set X := eN1 ({a} : Finset (Lam 2 L N)) a b * s * h⁻¹ with hX
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hM4 : 0 ≤ ‖cfAB4 a b F‖ * (s * s * (X * X)) := by positivity
  have l1 : (‖g1‖ + ‖g2‖) * D1 ≤ (‖g1‖ + ‖g2‖) * (2 / L * (s * X)) :=
    mul_le_mul_of_nonneg_left hD1 (by positivity)
  have l2 : ‖g3‖ * D2 ≤ ‖g3‖ * (2 / L * (X * X)) := mul_le_mul_of_nonneg_left hD2 (norm_nonneg _)
  have hL0 : (0 : ℝ) ≤ 2 / L := by positivity
  have hfin : 2 / L * gradM4Sz {a} a b h s F =
      (‖g1‖ + ‖g2‖) * (2 / L * (s * X)) + ‖g3‖ * (2 / L * (X * X)) +
        2 / L * (‖cfAB4 a b F‖ * (s * s * (X * X))) := by
    unfold gradM4Sz; rw [← hX]; ring
  rw [hfin]
  have := mul_nonneg hL0 hM4
  nlinarith

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- **Named input: `PairDefSizesNS` without the gradient Pauli defect**: the `ε`-tadpole and the
last-step defect, summed `≤ c_d‖M_{j_x}‖²ǧ_{j_x}`. -/
def PairDefSizesNF (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N)
    (cd : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∃ (sf : ℕ → ℝ) (sL : ℝ), (∀ k, 0 ≤ sf k) ∧
      (∀ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
        let t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀
        let C := Obs2.histCovO (R.withMsq m) t
        let V := PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x) t
        ‖ε (FC (C k) (Obs2.VprLO k (C k) (V k) : Obs.SA .two (Lam 2 L N)).ab
          (Obs2.VprLO k (C k) (V k) : Obs.SA .two (Lam 2 L N)).e)‖ ≤ sf k) ∧
      ‖lastDefR R Nh m b μ₀ oR x‖ ≤ sL ∧
      ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1), sf k + sL ≤
        cd * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ ^ 2 *
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1

end Traj

/-- **The constant of the gradient Pauli defect**:
`(4/L)(21/16)c_u c_G(2k₀ + m̄(6c²G₂ + 2cε))`. -/
def pd5Cp {L : ℕ} [NeZero L] (M : MasterFacts L) (C₁k C₁w mbar : ℝ) : ℝ :=
  4 / L * (21 / 16) * pairUnitC M *
    pl6cG L (KM4 2 Ccut2) (Obs2.KG 2 Ccut2 4) (2 * (cNb2 : ℝ) * (cSm2 : ℝ))
      (kB (kθ0 L M.core.A M.core.C₀a M.core.ηa) C₁k (8 * cx M.core.κ M.core.cT)) (4 * C₁w + 1) *
    (2 * pl6k0 M (pairUnitC M) + mbar *
      (6 * M.core.c ^ 2 * pl6G2 L M.core.ε + 2 * M.core.c * M.core.ε))

set_option maxHeartbeats 8000000 in
/-- **`PairDefSizesNS` from `PairDefSizesNF`, at given constants** (see the module docstring). -/
theorem pairDefSizesNS_of_NF_at {L : ℕ} [NeZero L] (M : MasterFacts L) {C₁k C₁w : ℝ}
    (hC₁k : 0 ≤ C₁k) (hC₁w : 0 ≤ C₁w) (hAH : M.core.AbwHistP C₁k C₁w)
    (hθ : C₁k * (2 + 2 * (8 * cx M.core.κ M.core.cT) + 1) * (M.core.c * M.core.ε) ≤ 1 / 72) :
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
    ∀ m ∈ mRange L N, ∀ b μ₀,
      Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μ₀ →
    ∀ (lam : ℕ → ℂ) (Kl : ℝ), 0 ≤ Kl → HLam R Nh m b μ₀ lam Kl →
      (∀ j ≤ Nh, max (spinMK L M.core.cg M.core.Ke M.core.KZ Kl M.core.KG 0) 0 *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤ 1 / 2) →
    ∀ mbar : ℝ, 0 < mbar →
      8 * (pairUnitC M * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) ≤ (4 * C₁w + 1) * mbar →
      (∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
        Obs.coal L (0 : Lam 2 L N) x ≤ Nh → PairVB R m b μ₀ lam x mbar (Nh + 1)) →
    ∀ cd : ℝ, PairDefSizesNF R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) cd →
      PairDefSizesNS R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) (cd + pd5Cp M C₁k C₁w mbar) := by
  have hKSW := pairKSWSizes_MFat M hC₁k hC₁w hAH
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam Kl hKl hl hsmall mbar hmbar
    h8 hVBtop cd hNF x hx h1 hj
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  set t : Flow2.Hist.Seq (Xs (R.withMsq m)) := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with ht
  have hb : 0 < b := by
    have := (hadm.1 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hL49 : 49 ≤ L := M.core.hL49
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hL8 : 2 ^ (2 + 3) + 8 * 2 < L := by omega
  obtain ⟨hVv, hVL, hG, hRI⟩ := M.core.pairTraj N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  have hρ0 : 0 ≤ (R.withMsq m).ρ := hVL.2.2.2.2.1
  have hρ8 : (R.withMsq m).ρ ≤ 1 / 8 := hVL.2.2.2.2.2.1
  have hs : ∀ k, 0 < histS (R.withMsq m) k t := fun k => histS_pos' (R.withMsq m) hρ0 hρ8 t k
  obtain ⟨hct, -, hcg⟩ := M.tad N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  obtain ⟨q, -, -, hlp⟩ :=
    (M.loop N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) (zV b)).2.2
  have htop := (M.top N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x)).1
  have hβne : ∀ k ≤ Nh, hBeta R m b μ₀ x k ≠ 0 ∧ hBeta R m b μ₀ x (k + 1) ≠ 0 := fun k hk => by
    obtain ⟨a1, a2, -, -⟩ := hBeta_rel_of R hNh hb x
      (M.relG N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) (zV b) (zV_mua_ne hb))
      (fun k hk => (hlp k hk).1) htop k hk
    exact ⟨a1, a2⟩
  have hβr := pairBetaRatio_MF M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm x
  have hβu := hBeta_up_MFD M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm.1 x
  obtain ⟨Hap, -, -⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm
  have hcR : cR (R.withMsq m) ((L : ℝ) ^ 2) M.core.cm M.core.C₂x = M.core.c := by
    obtain ⟨_, _, _, _, hAH⟩ := M.core.abwHist
    exact (hAH N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm).1
  have hc1 : 1 ≤ M.core.c := by
    rw [← hcR]
    have hcV : 0 ≤ cV (R.withMsq m) ((L : ℝ) ^ 2) M.core.cm := by
      unfold cV cZ; have := Hap.hcmu; positivity
    have hcW : 0 ≤ cW (R.withMsq m) ((L : ℝ) ^ 2) M.core.cm M.core.C₂x := by
      unfold cW; have := Hap.hC₂; positivity
    unfold cR; linarith
  have hc0 : 0 ≤ M.core.c := by linarith
  have hg : ∀ i ≤ Nh, 0 < (t i).1 ∧ (t i).1 ≤ M.core.ε := fun i hi =>
    ⟨(hadm.1 i hi).1, (hadm.1 i hi).2.1⟩
  have hε0 : 0 ≤ M.core.ε := ((hg 0 (Nat.zero_le _)).1.trans_le (hg 0 (Nat.zero_le _)).2).le
  have hcε : M.core.c * M.core.ε ≤ 1 := M.core.hcε
  -- the sequence `r`
  have hrE : ∀ i ≤ Nh, pl6r R m b μ₀ M.core.c i = M.core.c * (t i).1 := fun i hi => by
    show M.core.c * max (t i).1 0 = _; rw [max_eq_left (hg i hi).1.le]
  have hrε : ∀ i ≤ Nh, pl6r R m b μ₀ M.core.c i ≤ M.core.c * M.core.ε := fun i hi => by
    rw [hrE i hi]; exact mul_le_mul_of_nonneg_left (hg i hi).2 hc0
  have hr0 : ∀ i, 0 ≤ pl6r R m b μ₀ M.core.c i := fun i => mul_nonneg hc0 (le_max_right _ _)
  have hr1 : ∀ i ≤ Nh, pl6r R m b μ₀ M.core.c i ≤ 1 := fun i hi => (hrε i hi).trans hcε
  have hgr : ∀ i ≤ Nh, (t i).1 ≤ pl6r R m b μ₀ M.core.c i := fun i hi => by
    rw [hrE i hi]; exact le_mul_of_one_le_left (hg i hi).1.le hc1
  -- the ratio facts
  have H : PL6H j Nh (L : ℝ) (sXp x) (fun i => histS (R.withMsq m) i t)
      (fun i => ‖hBeta R m b μ₀ x i‖) (pl6r R m b μ₀ M.core.c) :=
    { hL := by exact_mod_cast hL49
      hs0 := hs
      hs1 := fun i => histS_succ_le_q (R.withMsq m) hρ0 hρ8 t i
      hs2 := fun i => histS_sq_ratio (R.withMsq m) hρ0 hρ8 t i
      hβ0 := fun i => norm_nonneg _
      hβp := fun i hi => by
        rcases Nat.lt_or_ge i (Nh + 1) with h | h
        · exact norm_pos_iff.2 (hβne i (by omega)).1
        · rw [show i = Nh + 1 by omega]; exact norm_pos_iff.2 (hβne Nh le_rfl).2
      hβr := hβr
      hr0 := hr0
      hr1 := hr1
      hsx := Nat.cast_nonneg _
      hsxL := by
        have h2 := two_supNorm_lt_coal (by omega : 2 ≤ L) x
        have hsn : supNorm ((ptsX x).a - (ptsX x).b) = supNorm (x - 0) := by
          show supNorm ((0 : Lam 2 L N) - x) = supNorm (x - 0)
          rw [supNorm_sub_comm]
        unfold sXp; rw [hsn]
        have : ((2 * supNorm (x - 0) : ℕ) : ℝ) ≤ ((L ^ (j + 1) : ℕ) : ℝ) := by
          exact_mod_cast h2.le
        push_cast at this; exact this }
  -- constants
  have hK4E : 0 ≤ KM4 2 CcutE := KM4_nonneg 2
  have hcNS : 0 ≤ 2 * (cNb2 : ℝ) * (cSm2 : ℝ) := by positivity
  have hQ1 : 1 ≤ Q1 2 := one_le_Q1 (d := 2) one_le_two
  have hθa0 : 0 ≤ kθ0 L M.core.A M.core.C₀a M.core.ηa := by
    unfold kθ0
    have := M.core.hA2
    exact mul_nonneg M.core.hC₀a (add_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _))
  have hθa : kθ0 L M.core.A M.core.C₀a M.core.ηa ≤ 1 / 72 := (M.core.hAa M.core.hLa).2
  set Bk := kB (kθ0 L M.core.A M.core.C₀a M.core.ηa) C₁k (8 * cx M.core.κ M.core.cT) with hBkd
  have hcx : 0 ≤ cx M.core.κ M.core.cT := Hap.hcx
  have hBk : 0 ≤ Bk := by rw [hBkd]; unfold kB; positivity
  have hcWc : 0 ≤ 4 * C₁w + 1 := by linarith
  have hAs : 0 ≤ pl6As L (4 * C₁w + 1) := pl6As_nonneg hcWc
  have haQ : 0 ≤ pl6aQ Bk (4 * C₁w + 1) := by unfold pl6aQ pl6ρ; positivity
  set V := vwB R m b μ₀ lam x with hVd
  have hV : 0 ≤ V := mul_nonneg (norm_nonneg _) (hg j hj).1.le
  set cu := pairUnitC M with hcud
  have hcu : 0 ≤ cu := pairUnitC_nonneg M
  set k₀ := pl6k0 M cu with hk₀d
  have hk₀ : 0 ≤ k₀ := by
    rw [hk₀d]; unfold pl6k0
    have := M.ιW_ge; have := M.core.hA2
    exact mul_nonneg hcu (pow_nonneg (by positivity) _)
  have hvwA : ∀ i ≤ Nh, vwA R m b μ₀ x i = 2 * histS (R.withMsq m) i t ^ 2 * ‖hBeta R m b μ₀ x i‖ :=
    fun i hi => by unfold vwA; rw [if_neg (hβne i hi).1]
  -- the small-set recursion in profile form (as in `pl6_item_le`)
  set θ := 8 * (kθ0 L M.core.A M.core.C₀a M.core.ηa + C₁k * (2 + 2 * (8 * cx M.core.κ M.core.cT) + 1) *
      (M.core.c * M.core.ε)) with hθd
  have hθ0 : 0 ≤ θ := by rw [hθd]; positivity
  have hθρ : θ * pl6ρ ≤ 1 / 2 := by
    have h29 : θ ≤ 2 / 9 := by rw [hθd]; linarith
    unfold pl6ρ; linarith only [h29]
  have hK : ∀ i, j ≤ i → i ≤ Nh →
      2 * histS (R.withMsq m) j t ^ 2 * ‖hBeta R m b μ₀ x j‖ *
        kszK R M C₁k C₁w mbar cu m b μ₀ lam x i ≤
      histS (R.withMsq m) i t ^ 2 * ‖hBeta R m b μ₀ x (i + 1)‖ *
        (128 / 49 * pl6P j k₀ i + 4 * pl6ρ * (64 / 49) * Bk * (4 * C₁w + 1) *
          (mbar * pl6Q j (pl6r R m b μ₀ M.core.c) i)) := fun i hji hi =>
    pl6_kseq H (r' := fun i => M.core.c * (t i).1)
      (m' := fun i => (4 * C₁w + 1) * (vwA R m b μ₀ x i * V / (vwA R m b μ₀ x j * V) * mbar))
      hθ0 hθρ hBk hcWc hk₀ hmbar.le (fun i hi => (hrE i hi).symm)
      (fun i hji hi => by
        show 2 * histS (R.withMsq m) j t ^ 2 * ‖hBeta R m b μ₀ x j‖ * ((4 * C₁w + 1) *
          (vwA R m b μ₀ x i * V / (vwA R m b μ₀ x j * V) * mbar)) ≤
          (4 * C₁w + 1) * (2 * histS (R.withMsq m) i t ^ 2 * ‖hBeta R m b μ₀ x i‖) * mbar
        rw [hvwA i hi, hvwA j hj]
        rcases hV.eq_or_lt with h0 | hpos
        · rw [← h0]; simp only [mul_zero, div_zero, zero_mul]
          have := hs i; positivity
        · rw [mul_div_mul_right _ _ hpos.ne']
          apply le_of_eq
          have := (hs j).ne'
          have := (H.hβp j (by omega)).ne'
          field_simp)
      hji hi
  have hkszQ : ∀ i, j ≤ i → i ≤ Nh → kszQ R M C₁k C₁w mbar cu m b μ₀ lam x i ≤
      V * (histS (R.withMsq m) i t ^ 2 * ‖hBeta R m b μ₀ x (i + 1)‖) *
        (pl6aQ Bk (4 * C₁w + 1) * pl6G0 j k₀ mbar (pl6r R m b μ₀ M.core.c) i) := by
    intro i hji hi
    have hA : 0 < 2 * histS (R.withMsq m) j t ^ 2 * ‖hBeta R m b μ₀ x j‖ := by
      have := hs j; have := H.hβp j (by omega); positivity
    have hKi := hK i hji hi
    set X := 128 / 49 * pl6P j k₀ i + 4 * pl6ρ * (64 / 49) * Bk * (4 * C₁w + 1) *
      (mbar * pl6Q j (pl6r R m b μ₀ M.core.c) i) with hXd
    have hP0 := pl6P_nonneg (j := j) hk₀ i
    have hQ0 := pl6Q_nonneg (j := j) (r := pl6r R m b μ₀ M.core.c) i
    have hc₁ : 0 ≤ 4 * pl6ρ * (64 / 49) * Bk * (4 * C₁w + 1) := by unfold pl6ρ; positivity
    have hX0 : 0 ≤ X := by rw [hXd]; have := hmbar.le; positivity
    have hT0 : 0 ≤ histS (R.withMsq m) i t ^ 2 * ‖hBeta R m b μ₀ x (i + 1)‖ := by positivity
    have hmax : 2 * histS (R.withMsq m) j t ^ 2 * ‖hBeta R m b μ₀ x j‖ *
        max (kszK R M C₁k C₁w mbar cu m b μ₀ lam x i) 0 ≤
        histS (R.withMsq m) i t ^ 2 * ‖hBeta R m b μ₀ x (i + 1)‖ * X := by
      rw [mul_max_of_nonneg _ _ hA.le, mul_zero]
      exact max_le hKi (mul_nonneg hT0 hX0)
    have h8' : 8 * X ≤ pl6aQ Bk (4 * C₁w + 1) * pl6G0 j k₀ mbar (pl6r R m b μ₀ M.core.c) i := by
      have e : pl6aQ Bk (4 * C₁w + 1) * pl6G0 j k₀ mbar (pl6r R m b μ₀ M.core.c) i =
          8 * X + 8 * (128 / 49 * (mbar * pl6Q j (pl6r R m b μ₀ M.core.c) i) +
            4 * pl6ρ * (64 / 49) * Bk * (4 * C₁w + 1) * pl6P j k₀ i) := by
        rw [hXd]; unfold pl6aQ pl6G0; ring
      rw [e]; have : 0 ≤ mbar * pl6Q j (pl6r R m b μ₀ M.core.c) i := mul_nonneg hmbar.le hQ0
      have : 0 ≤ 4 * pl6ρ * (64 / 49) * Bk * (4 * C₁w + 1) * pl6P j k₀ i := mul_nonneg hc₁ hP0
      linarith
    unfold kszQ
    rw [hvwA j hj]
    calc 2 * histS (R.withMsq m) j t ^ 2 * ‖hBeta R m b μ₀ x j‖ * V *
          (8 * max (kszK R M C₁k C₁w mbar cu m b μ₀ lam x i) 0) =
        8 * V * (2 * histS (R.withMsq m) j t ^ 2 * ‖hBeta R m b μ₀ x j‖ *
          max (kszK R M C₁k C₁w mbar cu m b μ₀ lam x i) 0) := by ring
      _ ≤ 8 * V * (histS (R.withMsq m) i t ^ 2 * ‖hBeta R m b μ₀ x (i + 1)‖ * X) := by gcongr
      _ = V * (histS (R.withMsq m) i t ^ 2 * ‖hBeta R m b μ₀ x (i + 1)‖) * (8 * X) := by ring
      _ ≤ _ := by gcongr
  have hkszS : ∀ i, j ≤ i → i ≤ Nh → kszS R M C₁w mbar m b μ₀ lam x i ≤
      V * (histS (R.withMsq m) i t ^ 2 * ‖hBeta R m b μ₀ x (i + 1)‖) *
        (128 / 49 * (L : ℝ) ^ 2 * pl6As L (4 * C₁w + 1) * (mbar * pl6r R m b μ₀ M.core.c i)) := by
    intro i hji hi
    have e : vwA R m b μ₀ x i * V * ((L : ℝ) ^ 2 * sO 2 L (M.core.c * (t i).1) mbar
        ((4 * C₁w + 1) * (M.core.c * (t i).1) * mbar)) =
        2 * (L : ℝ) ^ 2 * pl6As L (4 * C₁w + 1) * V * histS (R.withMsq m) i t ^ 2 *
          (mbar * pl6r R m b μ₀ M.core.c i) * ‖hBeta R m b μ₀ x i‖ := by
      rw [hvwA i hi, hrE i hi]; unfold sO pl6As; ring
    have hB := H.hβr i hi
    have hX0 : 0 ≤ 2 * (L : ℝ) ^ 2 * pl6As L (4 * C₁w + 1) * V * histS (R.withMsq m) i t ^ 2 *
        (mbar * pl6r R m b μ₀ M.core.c i) := by
      have := hr0 i; have := hmbar.le; positivity
    show max (vwA R m b μ₀ x i * V * ((L : ℝ) ^ 2 * sO 2 L (M.core.c * (t i).1) mbar
        ((4 * C₁w + 1) * (M.core.c * (t i).1) * mbar))) 0 ≤ _
    rw [e]
    have := hr0 i; have := hmbar.le
    refine max_le ?_ (by positivity)
    calc _ ≤ 2 * (L : ℝ) ^ 2 * pl6As L (4 * C₁w + 1) * V * histS (R.withMsq m) i t ^ 2 *
          (mbar * pl6r R m b μ₀ M.core.c i) * (64 / 49 * ‖hBeta R m b μ₀ x (i + 1)‖) :=
          mul_le_mul_of_nonneg_left hB hX0
      _ = _ := by ring
  -- the weight bound `s_i²|β_{i+1}| ≤ (21/32)c_u‖M_j‖r_i`
  set Mj := ‖Mmag R m b μ₀ lam j‖ with hMjd
  have hMj : 0 ≤ Mj := norm_nonneg _
  have hvwAle : ∀ i, j ≤ i → i ≤ Nh → vwA R m b μ₀ x i ≤ cu * Mj * pl6r R m b μ₀ M.core.c i :=
    fun i hji hi => by
      refine (vwA_le_mag_MF M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam Kl hKl hl
        hsmall x h1 hji hi (hβne i hi).1).trans ?_
      exact mul_le_mul_of_nonneg_left (hgr i hi) (mul_nonneg hcu hMj)
  have hwt : ∀ i, j ≤ i → i ≤ Nh → histS (R.withMsq m) i t ^ 2 * ‖hBeta R m b μ₀ x (i + 1)‖ ≤
      21 / 32 * cu * Mj * pl6r R m b μ₀ M.core.c i := fun i hji hi => by
    have h1' := hβu i hi
    have h2 := hvwAle i hji hi
    rw [hvwA i hi] at h2
    have h3 : histS (R.withMsq m) i t ^ 2 * ‖hBeta R m b μ₀ x (i + 1)‖ ≤
        histS (R.withMsq m) i t ^ 2 * (21 / 16 * ‖hBeta R m b μ₀ x i‖) :=
      mul_le_mul_of_nonneg_left h1' (sq_nonneg _)
    linarith only [h2, h3]
  -- the history sizes
  have hU := pairUnitSeed_MF M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam Kl hKl hl hsmall
  have hVB := hVBtop x hx h1 hj
  have hSz := fun i (hji : j ≤ i) (hi : i ≤ Nh) =>
    hKSW N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam cu mbar hU hmbar h8 x hx h1 hj
      (Nh + 1) le_rfl hVB i hji (by omega) hi
  -- the reduced state
  have hRd := pairSectRed_of R m hVv hVL b μ₀ (pairDCov_std (L := L) (N := N) Nh)
  obtain ⟨hobs, hloc0, -, -⟩ := hRd x hx h1 hj
  have hanc := pairAnchR_oRed R Nh m b μ₀ x hx h1 hj
  have hloc' : ∀ k, j ≤ k → k ≤ Nh → Obs2.OLocS (ptsX x) k
      (PtCorr2.hVR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t k)
      (PtCorr2.hWR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t k)
      (PtCorr2.hKR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t k) := fun k hk hkN =>
    PtCorr2.olocS_hR (R.withMsq m) (ptsX x) t hloc0 hk fun i' _ hi' => hRI i' (by omega)
  have hQK0 : ∀ i, 0 ≤ kszQ R M C₁k C₁w mbar cu m b μ₀ lam x i := fun i => by
    unfold kszQ
    exact mul_nonneg (mul_nonneg (vwA_nonneg R m b μ₀ x _) hV)
      (mul_nonneg (by norm_num) (le_max_right _ _))
  have hSK0 : ∀ i, 0 ≤ kszS R M C₁w mbar m b μ₀ lam x i := fun i => by
    unfold kszS; exact le_max_right _ _
  -- the path from `0` to `x`
  obtain ⟨w, hwx, hwl⟩ := PtCorr2.exists_path_sum (n := L ^ N) (x : Lam 2 L N)
  have hpe : Obs2.pathEnd (0 : Lam 2 L N) w = x := by rw [Obs2.pathEnd, zero_add, hwx]
  have hab : (ptsX x).a ≠ (ptsX x).b := fun h => hx h.symm
  have hpe' : Obs2.pathEnd (ptsX x).a w = (ptsX x).b := hpe
  have hwl' : (w.length : ℝ) ≤ 2 * ((supNorm ((ptsX x).a - (ptsX x).b) : ℕ) : ℝ) := by
    have hsn : supNorm ((ptsX x).a - (ptsX x).b) = supNorm x := by
      show supNorm ((0 : Lam 2 L N) - x) = supNorm x
      rw [zero_sub, supNorm_neg]
    rw [hsn]; exact_mod_cast hwl
  have hne : (w.length : ℝ) ≤ 2 * eN1 ({(ptsX x).a} : Finset (Lam 2 L N)) (ptsX x).a (ptsX x).b :=
    hwl'.trans (by linarith [pd5_supNorm_le_eN1 (ptsX x).a (ptsX x).b])
  -- the invariants of the reduced history
  have hVab : PtCorr2.ObsVabInv (ptsX x) (oRed R m b μ₀ dxStd x) :=
    PtCorr2.obsVabInv_redSt (R.withMsq m) (ptsX x)
  have hsymj : PtCorr2.ObsSymInv j (oRed R m b μ₀ dxStd x) :=
    PtCorr2.obsSymInv_redSt (hRI j hj).1 (hRI j hj).2 (rawD_mem (R.withMsq m) _ _)
      (rawK_mem (R.withMsq m) _ _)
      (PtCorr2.obsSymInv_hist (R.withMsq m) (ptsX x) _ (PtCorr2.obsSymInv_init .two (zV b) (ptsX x))
        t j fun i hi => (hRI i (by omega)))
  have hsym : ∀ k, j ≤ k → k ≤ Nh → PtCorr2.ObsSymInv k (PtCorr2.obsHistFrom (R.withMsq m)
      (ptsX x) j (oRed R m b μ₀ dxStd x) k t) := fun k hk hkN =>
    PtCorr2.obsSymInv_histFrom' (R.withMsq m) (ptsX x) hsymj t hk fun i _ hi => hRI i (by omega)
  have hz0 : ∀ b', ((oRed R m b μ₀ dxStd x).V b' : SA .two (Lam 2 L N)).ab = 0 :=
    fun b' => oRed_V_ab_zero R m b μ₀ dxStd x b'
  -- the abstract sizes `κ^Q`, `κ^S`
  have hK4 : 0 ≤ KM4 2 Ccut2 := KM4_nonneg 2
  have hKG : 0 ≤ Obs2.KG 2 Ccut2 4 := Obs2.KG_nonneg 2 (by norm_num)
  set κQ : ℕ → ℝ := fun i => 2 * (cNb2 : ℝ) * (cSm2 : ℝ) * kszQ R M C₁k C₁w mbar cu m b μ₀ lam x i
    with hκQd
  set κS : ℕ → ℝ := fun i => 2 * (L : ℝ) ^ 2 * kszS R M C₁w mbar m b μ₀ lam x i with hκSd
  have hκQ0 : ∀ i, 0 ≤ κQ i := fun i => mul_nonneg hcNS (hQK0 i)
  have hκS0 : ∀ i, 0 ≤ κS i := fun i => mul_nonneg (by positivity) (hSK0 i)
  have hcQ : 0 ≤ pl6cQ (2 * (cNb2 : ℝ) * (cSm2 : ℝ)) Bk (4 * C₁w + 1) := by
    unfold pl6cQ; exact mul_nonneg hcNS haQ
  have hcS : 0 ≤ pl6cS L (4 * C₁w + 1) := by unfold pl6cS; positivity
  have hκQ : ∀ i, j ≤ i → i ≤ Nh → κQ i ≤ V * (histS (R.withMsq m) i t ^ 2 *
      ‖hBeta R m b μ₀ x (i + 1)‖) * (pl6cQ (2 * (cNb2 : ℝ) * (cSm2 : ℝ)) Bk (4 * C₁w + 1) *
        pl6G0 j k₀ mbar (pl6r R m b μ₀ M.core.c) i) := fun i hji hi => by
    have := mul_le_mul_of_nonneg_left (hkszQ i hji hi) hcNS
    calc κQ i ≤ _ := this
      _ = _ := by unfold pl6cQ; ring
  have hκS : ∀ i, j ≤ i → i ≤ Nh → κS i ≤ V * (histS (R.withMsq m) i t ^ 2 *
      ‖hBeta R m b μ₀ x (i + 1)‖) * (pl6cS L (4 * C₁w + 1) *
        (mbar * pl6r R m b μ₀ M.core.c i)) := fun i hji hi => by
    have := mul_le_mul_of_nonneg_left (hkszS i hji hi) (by positivity : (0 : ℝ) ≤ 2 * (L : ℝ) ^ 2)
    calc κS i ≤ _ := this
      _ = _ := by unfold pl6cS; ring
  set cG := pl6cG L (KM4 2 Ccut2) (Obs2.KG 2 Ccut2 4) (2 * (cNb2 : ℝ) * (cSm2 : ℝ)) Bk
    (4 * C₁w + 1) with hcGd
  have hcG0 : 0 ≤ cG := by
    rw [hcGd]; unfold pl6cG pl6cM; positivity
  set gR := fun k => gradRHS (L : ℝ) (Obs2.KG 2 Ccut2 4) (KM4 2 Ccut2) (sXp x)
    (fun i => histS (R.withMsq m) i t) κQ κS j k with hgRd
  have hgR0 : ∀ k, 0 ≤ gR k := fun k =>
    gradRHS_nonneg hL0 hKG hK4 (Nat.cast_nonneg _) hs hκQ0 hκS0 _ _
  -- the per-block gradient sizes
  have hGr : ∀ k, j ≤ k → k ≤ Nh → ∀ c ∈ blockIdx (L := L) (N := N) k,
      gradM4Sz {(ptsX x).a} (ptsX x).a (ptsX x).b ((L : ℝ) ^ k) (histS (R.withMsq m) k t)
          (hVR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t k c :
            SA .two (Lam 2 L N)).ab ≤ gR k := fun k hjk hkN c hc =>
    (M.core.vhistG N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) hab w hpe' hwl'
      (oRed R m b μ₀ dxStd x) hloc0 hsymj hanc hVab hz0 hjk hkN _ _ hQK0 hSK0
      (fun i hi hik Y hY => (hSz i hi (by omega)).1 Y hY)
      (fun i hi hik b' hb' => ((hSz i hi (by omega)).2.1 b' hb').1) c hc).1
  have hγ : ∀ k, j ≤ k → k ≤ Nh → gR k ≤ histS (R.withMsq m) k t ^ 2 * ‖hBeta R m b μ₀ x (k + 1)‖ *
      V * (cG * pl6FO j k₀ mbar (pl6r R m b μ₀ M.core.c) k) := fun k hjk hk => by
    have hcGe : cG = (L : ℝ) * (3 / 4 * (L : ℝ) ^ 2 * (KM4 2 Ccut2 *
        (pl6cQ (2 * (cNb2 : ℝ) * (cSm2 : ℝ)) Bk (4 * C₁w + 1) / (L : ℝ) ^ 2 +
          6 / 5 * pl6cS L (4 * C₁w + 1))) +
        (2 * Obs2.KG 2 Ccut2 4 / (L : ℝ) + 243 / 64) * pl6cQ (2 * (cNb2 : ℝ) * (cSm2 : ℝ)) Bk
          (4 * C₁w + 1) + (2 * Obs2.KG 2 Ccut2 4 + 3) * pl6cS L (4 * C₁w + 1)) := by
      rw [hcGd]; rfl
    rw [hcGe]
    exact pl6_grad H hK4 hKG hV hk₀ hmbar.le hcQ hcS hκQ0 hκS0 hκQ hκS hk
  -- the non-gradient defects
  obtain ⟨sf, sL, hsf0, hNFk, hsL, hNFsum⟩ := hNF x hx h1 hj
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by omega)
  refine ⟨fun k => 4 / L * gR k, sf, sL, fun k => ⟨mul_nonneg (by positivity) (hgR0 k), hsf0 k⟩,
    fun k hk => ⟨?_, hNFk k hk⟩, hsL, ?_⟩
  · -- the gradient Pauli defect at `k`
    have hjk := (mem_Ico.1 hk).1
    have hkN : k ≤ Nh := by have := (mem_Ico.1 hk).2; omega
    have key := PtCorr2.pdefAB2_hVR_sub (R.withMsq m) (ptsX x) j _ t hVab (hsym k hjk hkN)
      (histCovO (R.withMsq m) t k)
    dsimp only
    change ‖pdefAB2 (ptsX x) k (histCovO (R.withMsq m) t k)
        (hVR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t k) -
      m4Tot (ptsX x) k (hVR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t k) *
        (histCovO (R.withMsq m) t k (ptsX x).a (ptsX x).a * histCovO (R.withMsq m) t k (ptsX x).b (ptsX x).b -
          histCovO (R.withMsq m) t k (ptsX x).a (ptsX x).b *
            histCovO (R.withMsq m) t k (ptsX x).b (ptsX x).a)‖ ≤ 4 / L * gR k
    rw [key]
    set Ck := histCovO (R.withMsq m) t k with hCkd
    set sk := histS (R.withMsq m) k t with hskd
    set e := eN1 ({(ptsX x).a} : Finset (Lam 2 L N)) (ptsX x).a (ptsX x).b with hed
    have he0 : 0 ≤ e := eN1_nonneg _ _ _
    have hsk0 : 0 ≤ sk := (hs k).le
    have hLk : (0 : ℝ) < (L : ℝ) ^ k := pow_pos hL0 k
    obtain ⟨-, hc2, hc3⟩ := covDiff_le_path (hG k hkN) (ptsX x).a w
    rw [hpe'] at hc2 hc3
    have hm2 := Obs2.norm_m2Def_le2 (hG k hkN) (ptsX x).a w
    rw [hpe'] at hm2
    have hn0 : (0 : ℝ) ≤ w.length := Nat.cast_nonneg _
    have hD1 : (w.length : ℝ) * (sk ^ 2 / (L : ℝ) ^ (k + 1)) ≤
        2 / L * (sk * (e * sk * ((L : ℝ) ^ k)⁻¹)) := by
      have h1' : (w.length : ℝ) * (sk ^ 2 / (L : ℝ) ^ (k + 1)) ≤ (2 * e) * (sk ^ 2 / (L : ℝ) ^ (k + 1)) :=
        mul_le_mul_of_nonneg_right hne (by positivity)
      refine h1'.trans (le_of_eq ?_)
      rw [pow_succ]; field_simp; ring
    have hD2 : ((w.length : ℝ) * (sk / (L : ℝ) ^ (k + 1))) ^ 2 ≤
        2 / L * ((e * sk * ((L : ℝ) ^ k)⁻¹) * (e * sk * ((L : ℝ) ^ k)⁻¹)) := by
      have h1' : (w.length : ℝ) * (sk / (L : ℝ) ^ (k + 1)) ≤ (2 * e) * (sk / (L : ℝ) ^ (k + 1)) :=
        mul_le_mul_of_nonneg_right hne (by positivity)
      have h2' := pow_le_pow_left₀ (by positivity) h1' 2
      refine h2'.trans ?_
      have e2 : ((2 * e) * (sk / (L : ℝ) ^ (k + 1))) ^ 2 =
          4 / (L : ℝ) ^ 2 * ((e * sk * ((L : ℝ) ^ k)⁻¹) * (e * sk * ((L : ℝ) ^ k)⁻¹)) := by
        rw [pow_succ]; field_simp; ring
      rw [e2]
      have hX : 0 ≤ (e * sk * ((L : ℝ) ^ k)⁻¹) * (e * sk * ((L : ℝ) ^ k)⁻¹) := by positivity
      have h42 : 4 / (L : ℝ) ^ 2 ≤ 2 / L := by
        have hL2' : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by omega)
        rw [div_le_div_iff₀ (by positivity) hL0]; nlinarith only [hL2', hL0]
      exact mul_le_mul_of_nonneg_right h42 hX
    have hblk : ∀ c ∈ blockIdx (L := L) (N := N) k,
        ‖∑ u ∈ ({(ptsX x).a, (ptsX x).b} : Finset (Lam 2 L N)),
          ∑ v ∈ ({(ptsX x).a, (ptsX x).b} : Finset (Lam 2 L N)),
            cfAB2 u v (hVR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t k c :
              SA .two (Lam 2 L N)).ab * (Ck u v - Ck (ptsX x).a (ptsX x).a)‖ ≤ 2 / L * gR k := by
      intro c hc
      refine (pd5_gradDef_block_le hab Ck _ hsk0 hLk.le
        (by rw [norm_sub_rev]; exact hc3) (by rw [norm_sub_rev]; exact hc2) hm2 hD1 hD2).trans ?_
      exact mul_le_mul_of_nonneg_left (hGr k hjk hkN c hc) (by positivity)
    have hz : ∀ c ∈ blockIdx (L := L) (N := N) k, c ≠ blk k (ptsX x).a → c ≠ blk k (ptsX x).b →
        ∑ u ∈ ({(ptsX x).a, (ptsX x).b} : Finset (Lam 2 L N)),
          ∑ v ∈ ({(ptsX x).a, (ptsX x).b} : Finset (Lam 2 L N)),
            cfAB2 u v (hVR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t k c :
              SA .two (Lam 2 L N)).ab * (Ck u v - Ck (ptsX x).a (ptsX x).a) = 0 := by
      intro c _ h1' h2'
      rw [hVR_ab_anch (R.withMsq m) (ptsX x) j _ t hanc hjk c h1' h2']
      simp [cfAB2, coeff_zero]
    have := norm_sum_two_le _ _ (blk k (ptsX x).a) (blk k (ptsX x).b)
      (mul_nonneg (by positivity) (hgR0 k)) hz hblk
    refine this.trans (le_of_eq ?_)
    ring
  · -- the sum
    set r := pl6r R m b μ₀ M.core.c with hrd
    set g' : ℕ → ℝ := fun i => max (min (t i).1 M.core.ε) 0 with hg'd
    have hrg : ∀ i ≤ Nh, r i = M.core.c * g' i := fun i hi => by
      show M.core.c * max (t i).1 0 = M.core.c * max (min (t i).1 M.core.ε) 0
      rw [min_eq_left (hg i hi).2]
    set Y := 21 / 32 * cu * Mj with hYd
    have hY : 0 ≤ Y := by positivity
    have hitem : ∀ k ∈ Finset.Ico j (Nh + 1),
        4 / L * gR k ≤ 4 / L * (2 * (V * Y * cG)) * pl6P j k₀ k + 4 / L * (2 * (V * Y * cG)) * mbar *
          ((M.core.c * g' k) ^ 2 + ∑ i ∈ Finset.Ico j k, (1 / 2 : ℝ) ^ (k - i) *
            ((M.core.c * g' i) ^ 2 + (M.core.c * g' i) * (M.core.c * g' k)) +
            (1 / 2 : ℝ) ^ (k - j) * (M.core.c * g' k)) := by
      intro k hk
      have hjk := (mem_Ico.1 hk).1
      have hkN : k ≤ Nh := by have := (mem_Ico.1 hk).2; omega
      have hFO := pl6FO_nonneg (j := j) (r := r) hk₀ hmbar.le hr0 k
      have h1' : gR k ≤ (21 / 32 * cu * Mj * r k) * V * (cG * pl6FO j k₀ mbar r k) := by
        refine (hγ k hjk hkN).trans ?_
        have := hwt k hjk hkN
        gcongr
      have h2' : r k * pl6FO j k₀ mbar r k ≤ 2 * pl6NF j k₀ mbar r k :=
        pl6_mul_FO hk₀ hmbar.le hr0 (hr1 k hkN)
      have h3 : gR k ≤ 2 * (V * Y * cG) * pl6NF j k₀ mbar r k := by
        refine h1'.trans ?_
        have e : (21 / 32 * cu * Mj * r k) * V * (cG * pl6FO j k₀ mbar r k) =
            V * Y * cG * (r k * pl6FO j k₀ mbar r k) := by rw [hYd]; ring
        rw [e]
        have := mul_le_mul_of_nonneg_left h2' (by positivity : (0 : ℝ) ≤ V * Y * cG)
        linarith
      have hQc : pl6Q j r k ≤ ∑ i ∈ Finset.Ico j k, (1 / 2 : ℝ) ^ (k - i) *
          ((M.core.c * g' i) ^ 2 + (M.core.c * g' i) * (M.core.c * g' k)) := by
        unfold pl6Q
        refine sum_le_sum fun i hi => ?_
        have hiN : i ≤ Nh := by have := (mem_Ico.1 hi).2; omega
        rw [hrg i hiN]
        have : 0 ≤ (M.core.c * g' i) * (M.core.c * g' k) := by
          rw [← hrg i hiN, ← hrg k hkN]; exact mul_nonneg (hr0 i) (hr0 k)
        have : 0 ≤ (1 / 2 : ℝ) ^ (k - i) := by positivity
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right ‹_›) this
      have hlast : 0 ≤ (1 / 2 : ℝ) ^ (k - j) * (M.core.c * g' k) := by
        rw [← hrg k hkN]; exact mul_nonneg (by positivity) (hr0 k)
      have hNF : pl6NF j k₀ mbar r k ≤ pl6P j k₀ k + mbar *
          ((M.core.c * g' k) ^ 2 + ∑ i ∈ Finset.Ico j k, (1 / 2 : ℝ) ^ (k - i) *
            ((M.core.c * g' i) ^ 2 + (M.core.c * g' i) * (M.core.c * g' k)) +
            (1 / 2 : ℝ) ^ (k - j) * (M.core.c * g' k)) := by
        unfold pl6NF pl6G0
        rw [hrg k hkN]
        have := mul_le_mul_of_nonneg_left hQc hmbar.le
        linarith only [this, mul_nonneg hmbar.le hlast]
      have hc4 : 0 ≤ 4 / L * (2 * (V * Y * cG)) := by positivity
      have := mul_le_mul_of_nonneg_left (h3.trans (mul_le_mul_of_nonneg_left hNF
        (by positivity : (0 : ℝ) ≤ 2 * (V * Y * cG)))) (by positivity : (0 : ℝ) ≤ 4 / L)
      refine this.trans (le_of_eq ?_)
      ring
    have hG2 : ∑ k ∈ Finset.Ico j (Nh + 1), g' k ^ 2 ≤ pl6G2 L M.core.ε := by
      have hβL : 0 < betaL L := lt_of_lt_of_le (by norm_num) (betaL_ge (by omega))
      have hinc := M.ginc N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
      have hS := sum_gsq_Ico_le (g := fun i => (t i).1) hβL hj (fun k hk hkn => hinc k hkn)
      have e : ∑ k ∈ Finset.Ico j Nh, g' k ^ 2 = ∑ k ∈ Finset.Ico j Nh, ((t k).1) ^ 2 :=
        sum_congr rfl fun k hk => by
          rw [hg'd]; dsimp only
          rw [min_eq_left (hg k (by have := (mem_Ico.1 hk).2; omega)).2,
            max_eq_left (hg k (by have := (mem_Ico.1 hk).2; omega)).1.le]
      rw [sum_Ico_succ_top hj, e]
      have h2 : g' Nh ^ 2 ≤ M.core.ε ^ 2 := by
        rw [hg'd]; dsimp only
        exact pow_le_pow_left₀ (le_max_right _ _) (max_le (min_le_right _ _) hε0) 2
      have h3 : 4 / betaL L * ((t Nh).1 - (t j).1) ≤ 4 * M.core.ε / betaL L := by
        rw [div_mul_eq_mul_div]
        apply div_le_div_of_nonneg_right _ hβL.le
        have h1 := (hg Nh le_rfl).2; have h2 := (hg j hj).1; linarith only [h1, h2]
      unfold pl6G2; linarith
    have hCE : 0 ≤ 4 / L * (2 * (V * Y * cG)) := by positivity
    have hsum := pairLoop2_sum_le (q := 1 / 2) (by norm_num) le_rfl hc0 hCE hmbar.le
      (g := g') (fun i => le_max_right _ _) (fun i => max_le (min_le_right _ _) hε0)
      (seed := fun k => 4 / L * (2 * (V * Y * cG)) * pl6P j k₀ k) hG2 hitem
    have hseedS : ∑ k ∈ Finset.Ico j (Nh + 1), 4 / L * (2 * (V * Y * cG)) * pl6P j k₀ k ≤
        2 * (4 / L * (2 * (V * Y * cG)) * k₀) := by
      have h := geom_decay_le (q := 1 / 2) (by norm_num) le_rfl (g := fun _ => (1 : ℝ))
        (fun _ => zero_le_one) (fun _ => le_rfl) j (Nh + 1)
      unfold pl6P
      have e : ∑ k ∈ Finset.Ico j (Nh + 1), 4 / L * (2 * (V * Y * cG)) * ((1 / 2 : ℝ) ^ (k - j) * k₀) =
          4 / L * (2 * (V * Y * cG)) * k₀ * ∑ k ∈ Finset.Ico j (Nh + 1), (1 / 2 : ℝ) ^ (k - j) * 1 := by
        rw [mul_sum]; exact sum_congr rfl fun k _ => by ring
      rw [e]
      have : 0 ≤ 4 / L * (2 * (V * Y * cG)) * k₀ := by positivity
      nlinarith only [h, this]
    have hcd : 2 * (4 / L * (2 * (V * Y * cG)) * k₀) + 4 / L * (2 * (V * Y * cG)) * mbar *
          (6 * M.core.c ^ 2 * pl6G2 L M.core.ε + 2 * M.core.c * M.core.ε) =
        pd5Cp M C₁k C₁w mbar * Mj ^ 2 * (t j).1 := by
      have hVe : V = Mj * (t j).1 := by rw [hVd, hMjd]; rfl
      rw [hYd, hVe, hk₀d, hcud, hcGd, hBkd]; unfold pd5Cp; ring
    show ∑ k ∈ Finset.Ico j (Nh + 1), (4 / L * gR k + sf k) + sL ≤
      (cd + pd5Cp M C₁k C₁w mbar) * Mj ^ 2 * (t j).1
    rw [sum_add_distrib]
    have hNF' : ∑ k ∈ Finset.Ico j (Nh + 1), sf k + sL ≤ cd * Mj ^ 2 * (t j).1 := hNFsum
    have hS1 : ∑ k ∈ Finset.Ico j (Nh + 1), 4 / L * gR k ≤ pd5Cp M C₁k C₁w mbar * Mj ^ 2 * (t j).1 := by
      rw [← hcd]; linarith
    have e : (cd + pd5Cp M C₁k C₁w mbar) * Mj ^ 2 * (t j).1 =
        pd5Cp M C₁k C₁w mbar * Mj ^ 2 * (t j).1 + cd * Mj ^ 2 * (t j).1 := by ring
    rw [e]; linarith

/-- **`pairDefSizesNS_of_NF_at` at the canonical constants** `C₁ka`, `C₁wa` (no requirement). -/
theorem pairDefSizesNS_of_NF_MFC {L : ℕ} [NeZero L] (M : MasterFacts L) :
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
    ∀ m ∈ mRange L N, ∀ b μ₀,
      Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μ₀ →
    ∀ (lam : ℕ → ℂ) (Kl : ℝ), 0 ≤ Kl → HLam R Nh m b μ₀ lam Kl →
      (∀ j ≤ Nh, max (spinMK L M.core.cg M.core.Ke M.core.KZ Kl M.core.KG 0) 0 *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤ 1 / 2) →
    ∀ mbar : ℝ, 0 < mbar →
      8 * (pairUnitC M * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) ≤
        (4 * M.core.C₁wa + 1) * mbar →
      (∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
        Obs.coal L (0 : Lam 2 L N) x ≤ Nh → PairVB R m b μ₀ lam x mbar (Nh + 1)) →
    ∀ cd : ℝ, PairDefSizesNF R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) cd →
      PairDefSizesNS R Nh m b μ₀ lam (oRed R m b μ₀ dxStd)
        (cd + pd5Cp M M.core.C₁ka M.core.C₁wa mbar) := by
  obtain ⟨-, hC₁k, -, hθ, -, -, -, hC₁w, -⟩ := M.core.hEaB
  exact pairDefSizesNS_of_NF_at M hC₁k hC₁w M.core.abwHistC hθ

/-- **`PairDefSizesR3P` from `PairDefSizesNF`** (canonical constants):
`PairDefSizesNF c_d ⇒ PairDefSizesR3P (c_d + pd5Cp + pd5CS)`. -/
theorem pairDefSizesR3P_of_NF_MFC {L : ℕ} [NeZero L] (M : MasterFacts L) :
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
    ∀ m ∈ mRange L N, ∀ b μ₀,
      Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μ₀ →
    ∀ (lam : ℕ → ℂ) (Kl : ℝ), 0 ≤ Kl → HLam R Nh m b μ₀ lam Kl →
      (∀ j ≤ Nh, max (spinMK L M.core.cg M.core.Ke M.core.KZ Kl M.core.KG 0) 0 *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤ 1 / 2) →
    ∀ mbar : ℝ, 0 < mbar →
      8 * (pairUnitC M * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) ≤
        (4 * M.core.C₁wa + 1) * mbar →
      (∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
        Obs.coal L (0 : Lam 2 L N) x ≤ Nh → PairVB R m b μ₀ lam x mbar (Nh + 1)) →
    ∀ cd : ℝ, PairDefSizesNF R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) cd →
      PairDefSizesR3P R Nh m b μ₀ lam (oRed R m b μ₀ dxStd)
        (cd + pd5Cp M M.core.C₁ka M.core.C₁wa mbar + pd5CS M M.core.C₁ka M.core.C₁wa mbar) := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam Kl hKl hl hsmall mbar hmbar h8
    hVB cd hNF
  exact pairDefSizesR3P_of_NS_MFC M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam Kl hKl hl
    hsmall mbar hmbar h8 hVB _ (pairDefSizesNS_of_NF_MFC M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b
      μ₀ hadm lam Kl hKl hl hsmall mbar hmbar h8 hVB cd hNF)

end

end Spin2
