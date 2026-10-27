import Obs2.Pair.PairLin1
import PtCorr2.Restart.RerepState
import PtCorr2.Pair.PairAbove

/-!
# Pair linearity, part 2: the integrand, the chain-invariant `W`, the pair output on triples

Case (2). Relative triples `Obs2.PlRel` (equal `∅`/`b` parts, `a`, `ab` parts `F − G = H`).

* `pl_rel_omegaCO`: `ω_Γ` (componentwise, linear) preserves triples.
* Scalars: `pl_sAB_sub`, `pl_nAB_sub`, `pl_nA_sub`, `pl_nB_eq`; **`pl_outW_sub`**: the connected
  output `outW W = n_{ab}W − n_aW·n_bW` is additive on triples, `outW F − outW G = outW H`.
* **`pl_out3`** (pure): for `W_i = e^{−u_i}Y_i` (`u_i` observable, common `σ_b` part) forming a
  triple, the `rpcOut`-type output `−ε(u_a)γ − n_{ab}Y` satisfies
  `out₁ − out₂ − out₃ = −D_a(γ + n_bW₁ + ε(u_b)·s/s) − D_{ab}·s/s`, `s = sE W₁`,
  `D_• = ε(u₁•) − ε(u₂•) − ε(u₃•)`.
* States: `PlRelSt` (componentwise triples), `plDiffSt o₁ o₂` (`a`, `ab` parts the difference,
  `∅`, `b` parts those of `o₂`), `pl_relSt_diff`, `pl_diff_prj` (`prjSt false` = that of `o₂`, the
  `rpb_b_eq` hypothesis), `pl_rrSt_prj` (relocation does not touch `∅`/`b` parts).
* **`pl_rel_ZinO`**: the scale-`j` integrand `ZinO` maps state triples to triples.
* `plW R P m o k t = e^{−u_k}·ω_{Γ_k}Z_k` along the history from `m`.
  **`pl_cst_chain`**: `e^{−u_m}∏_{m ≤ i < k} chOF_i = (∏ ch_i)·e^{−u_k}`;
  **`pl_W_chain`** (hypotheses of `hist_omegaOF_from`): `plW m = (∏_{m ≤ i < k} ch_i)·plW k`.
* **`pl_W_rel_m`**: `PlRelSt (rrStH o₁) o₂ o₃` ⟹ triple of `plW` at `m` (`rr_ZhOF`; `rrSt`
  keeps `u`);
  **`pl_W_rel`**: the same at every `m ≤ k ≤ N_h` (given `∏ ch ≠ 0`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2 Flow2.Hist

/-! ### Pure part -/

section Pure

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

theorem pl_omegaC_sub (C : Matrix Λ Λ ℂ) (F G : N Λ) :
    omegaC C (F - G) = omegaC C F - omegaC C G := by
  rw [sub_eq_add_neg, omegaC_add, ← neg_one_smul ℂ G, omegaC_smul]; ring

theorem pl_rel_omegaCO (Γ : Matrix Λ Λ ℂ) {F G H : OE .two Λ} (h : PlRel F G H) :
    PlRel (omegaCO Γ F) (omegaCO Γ G) (omegaCO Γ H) where
  e1 := by rw [omegaCO_e, omegaCO_e, h.e1]
  e2 := by rw [omegaCO_e, omegaCO_e, h.e2]
  b1 := by rw [omegaCO_b, omegaCO_b, h.b1]
  b2 := by rw [omegaCO_b, omegaCO_b, h.b2]
  a := by rw [omegaCO_a, omegaCO_a, omegaCO_a, ← h.a, pl_omegaC_sub, map_sub]
  ab := by rw [omegaCO_ab, omegaCO_ab, omegaCO_ab, ← h.ab, pl_omegaC_sub, map_sub]

theorem pl_sE_eq {F G H : OE .two Λ} (h : PlRel F G H) : sE G = sE F ∧ sE H = sE F := by
  unfold sE; rw [h.e1, h.e2]; exact ⟨rfl, rfl⟩

theorem pl_sB_eq {F G H : OE .two Λ} (h : PlRel F G H) : sB G = sB F ∧ sB H = sB F := by
  unfold sB; rw [h.b1, h.b2]; exact ⟨rfl, rfl⟩

theorem pl_sA_sub {F G H : OE .two Λ} (h : PlRel F G H) : sA F - sA G = sA H := by
  unfold sA; rw [← h.a, map_sub]

theorem pl_sAB_sub {F G H : OE .two Λ} (h : PlRel F G H) : sAB F - sAB G = sAB H := by
  unfold sAB; rw [← h.ab, map_sub]

theorem pl_nAB_sub {F G H : OE .two Λ} (h : PlRel F G H) : nAB F - nAB G = nAB H := by
  unfold nAB; rw [(pl_sE_eq h).1, (pl_sE_eq h).2, ← pl_sAB_sub h, sub_div]

theorem pl_nA_sub {F G H : OE .two Λ} (h : PlRel F G H) : nA F - nA G = nA H := by
  unfold nA; rw [(pl_sE_eq h).1, (pl_sE_eq h).2, ← pl_sA_sub h, sub_div]

theorem pl_nB_eq {F G H : OE .two Λ} (h : PlRel F G H) : nB G = nB F ∧ nB H = nB F := by
  unfold nB; rw [(pl_sE_eq h).1, (pl_sE_eq h).2, (pl_sB_eq h).1, (pl_sB_eq h).2]; exact ⟨rfl, rfl⟩

/-- The connected pair output of a generating element, `n_{ab}W − n_aW·n_bW`. -/
def outW (W : OE .two Λ) : ℂ := nAB W - nA W * nB W

/-- **The connected output is additive on relative triples.** -/
theorem pl_outW_sub {F G H : OE .two Λ} (h : PlRel F G H) : outW F - outW G = outW H := by
  unfold outW
  rw [← pl_nAB_sub h, ← pl_nA_sub h, (pl_nB_eq h).1, (pl_nB_eq h).2]; ring

theorem pl_sX_oexp_obs {u : OE .two Λ} (hu : bulk u = 0) :
    sE (oexp u) = 1 ∧ sA (oexp u) = ε (u : SA .two Λ).a ∧ sB (oexp u) = ε (u : SA .two Λ).b ∧
      sAB (oexp u) = ε (u : SA .two Λ).ab + ε (u : SA .two Λ).a * ε (u : SA .two Λ).b := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold sE; rw [oexp_obs_e hu, map_one]
  · unfold sA; rw [oexp_obs_a hu]
  · unfold sB; rw [oexp_obs_b' hu]
  · unfold sAB
    rw [oexp_obs_ab hu, Case.s_two, one_smul, map_add, map_smul, map_add, map_mul, map_mul,
      smul_eq_mul]
    ring

theorem pl_oexp_neg_mul {u : OE .two Λ} (hu : bulk u = 0) (Y : OE .two Λ) :
    oexp u * (oexp (-u) * Y) = Y := by
  rw [← mul_assoc, ← oexp_add_obs hu (by rw [map_neg, hu, neg_zero]), add_neg_cancel,
    show (0 : OE .two Λ) = 0 • (0 : OE .two Λ) by simp, oexp, IsNilpotent.exp_eq_sum (k := 1)
      (by simp)]
  simp

/-- The core scalar identity behind `pl_out3` (`Y_i = e^{u_i}W_i`). -/
theorem pl_out3_core {u₁ u₂ u₃ Y₁ Y₂ Y₃ W₁ W₂ W₃ : OE .two Λ} (hu₁ : bulk u₁ = 0)
    (hu₂ : bulk u₂ = 0) (hu₃ : bulk u₃ = 0) (hb₂ : (u₂ : SA .two Λ).b = (u₁ : SA .two Λ).b)
    (hb₃ : (u₃ : SA .two Λ).b = (u₁ : SA .two Λ).b) (hY₁ : Y₁ = oexp u₁ * W₁)
    (hY₂ : Y₂ = oexp u₂ * W₂) (hY₃ : Y₃ = oexp u₃ * W₃) (h : PlRel W₁ W₂ W₃) (γ : ℂ) :
    (-ε (u₁ : SA .two Λ).a * γ - nAB Y₁) - (-ε (u₂ : SA .two Λ).a * γ - nAB Y₂) -
        (-ε (u₃ : SA .two Λ).a * γ - nAB Y₃) =
      -(ε (u₁ : SA .two Λ).a - ε (u₂ : SA .two Λ).a - ε (u₃ : SA .two Λ).a) *
          (γ + nB W₁ + ε (u₁ : SA .two Λ).b * (sE W₁ / sE W₁)) -
        (ε (u₁ : SA .two Λ).ab - ε (u₂ : SA .two Λ).ab - ε (u₃ : SA .two Λ).ab) *
          (sE W₁ / sE W₁) := by
  obtain ⟨e1, a1, b1, ab1⟩ := pl_sX_oexp_obs hu₁
  obtain ⟨e2, a2, b2, ab2⟩ := pl_sX_oexp_obs hu₂
  obtain ⟨e3, a3, b3, ab3⟩ := pl_sX_oexp_obs hu₃
  obtain ⟨hE2, hE3⟩ := pl_sE_eq h
  obtain ⟨hB2, hB3⟩ := pl_sB_eq h
  have hA := pl_sA_sub h
  have hAB := pl_sAB_sub h
  have y1 : sAB Y₁ = sAB W₁ + ε (u₁ : SA .two Λ).a * sB W₁ + ε (u₁ : SA .two Λ).b * sA W₁ +
      (ε (u₁ : SA .two Λ).ab + ε (u₁ : SA .two Λ).a * ε (u₁ : SA .two Λ).b) * sE W₁ := by
    rw [hY₁, sAB_mul, e1, a1, b1, ab1]; ring
  have y2 : sAB Y₂ = sAB W₂ + ε (u₂ : SA .two Λ).a * sB W₂ + ε (u₂ : SA .two Λ).b * sA W₂ +
      (ε (u₂ : SA .two Λ).ab + ε (u₂ : SA .two Λ).a * ε (u₂ : SA .two Λ).b) * sE W₂ := by
    rw [hY₂, sAB_mul, e2, a2, b2, ab2]; ring
  have y3 : sAB Y₃ = sAB W₃ + ε (u₃ : SA .two Λ).a * sB W₃ + ε (u₃ : SA .two Λ).b * sA W₃ +
      (ε (u₃ : SA .two Λ).ab + ε (u₃ : SA .two Λ).a * ε (u₃ : SA .two Λ).b) * sE W₃ := by
    rw [hY₃, sAB_mul, e3, a3, b3, ab3]; ring
  have s1 : sE Y₁ = sE W₁ := by rw [hY₁, sE_mul, e1, one_mul]
  have s2 : sE Y₂ = sE W₁ := by rw [hY₂, sE_mul, e2, one_mul, hE2]
  have s3 : sE Y₃ = sE W₁ := by rw [hY₃, sE_mul, e3, one_mul, hE3]
  unfold nAB nB
  rw [y1, y2, y3, s1, s2, s3, hE2, hE3, hB2, hB3, hb₂, hb₃, ← hA, ← hAB]
  ring

/-- **The pair output on triples** (pure). `W_i = e^{−u_i}Y_i` form a triple, the `u_i` are
observable with a common `σ_b` part; `γ` arbitrary. Then for `o_i ↦ −ε(u_{i,a})γ − n_{ab}Y_i`:
`out₁ − out₂ − out₃ = −D_a(γ + n_bW₁ + ε(u_b)·s/s) − D_{ab}·s/s` (`s = sE W₁`). -/
theorem pl_out3 {u₁ u₂ u₃ Y₁ Y₂ Y₃ : OE .two Λ} (hu₁ : bulk u₁ = 0) (hu₂ : bulk u₂ = 0)
    (hu₃ : bulk u₃ = 0) (hb₂ : (u₂ : SA .two Λ).b = (u₁ : SA .two Λ).b)
    (hb₃ : (u₃ : SA .two Λ).b = (u₁ : SA .two Λ).b)
    (h : PlRel (oexp (-u₁) * Y₁) (oexp (-u₂) * Y₂) (oexp (-u₃) * Y₃)) (γ : ℂ) :
    (-ε (u₁ : SA .two Λ).a * γ - nAB Y₁) - (-ε (u₂ : SA .two Λ).a * γ - nAB Y₂) -
        (-ε (u₃ : SA .two Λ).a * γ - nAB Y₃) =
      -(ε (u₁ : SA .two Λ).a - ε (u₂ : SA .two Λ).a - ε (u₃ : SA .two Λ).a) *
          (γ + nB (oexp (-u₁) * Y₁) + ε (u₁ : SA .two Λ).b *
            (sE (oexp (-u₁) * Y₁) / sE (oexp (-u₁) * Y₁))) -
        (ε (u₁ : SA .two Λ).ab - ε (u₂ : SA .two Λ).ab - ε (u₃ : SA .two Λ).ab) *
          (sE (oexp (-u₁) * Y₁) / sE (oexp (-u₁) * Y₁)) :=
  pl_out3_core hu₁ hu₂ hu₃ hb₂ hb₃ (pl_oexp_neg_mul hu₁ Y₁).symm (pl_oexp_neg_mul hu₂ Y₂).symm
    (pl_oexp_neg_mul hu₃ Y₃).symm h γ

/-- The `rpcOut`/`rpTopOut`-type pair output `−ε(u_a)γ − n_{ab}Y`. -/
def plOut (γ : ℂ) (u Y : OE .two Λ) : ℂ := -ε (u : SA .two Λ).a * γ - nAB Y

/-- **The pair output on triples, reference form**: the correction terms in terms of the reference
(second) entry, `W₂ = e^{−u₂}Y₂`, `s = sE W₂`. -/
theorem pl_out_triple {u₁ u₂ u₃ Y₁ Y₂ Y₃ : OE .two Λ} (hu₁ : bulk u₁ = 0) (hu₂ : bulk u₂ = 0)
    (hu₃ : bulk u₃ = 0) (hb₁ : (u₁ : SA .two Λ).b = (u₂ : SA .two Λ).b)
    (hb₃ : (u₃ : SA .two Λ).b = (u₂ : SA .two Λ).b)
    (h : PlRel (oexp (-u₁) * Y₁) (oexp (-u₂) * Y₂) (oexp (-u₃) * Y₃)) (γ : ℂ) :
    plOut γ u₁ Y₁ - plOut γ u₂ Y₂ - plOut γ u₃ Y₃ =
      -(ε (u₁ : SA .two Λ).a - ε (u₂ : SA .two Λ).a - ε (u₃ : SA .two Λ).a) *
          (γ + nB (oexp (-u₂) * Y₂) + ε (u₂ : SA .two Λ).b *
            (sE (oexp (-u₂) * Y₂) / sE (oexp (-u₂) * Y₂))) -
        (ε (u₁ : SA .two Λ).ab - ε (u₂ : SA .two Λ).ab - ε (u₃ : SA .two Λ).ab) *
          (sE (oexp (-u₂) * Y₂) / sE (oexp (-u₂) * Y₂)) := by
  have H := pl_out3 hu₁ hu₂ hu₃ (hb₁.symm) (hb₃.trans hb₁.symm) h γ
  unfold plOut
  rw [H, ← (pl_nB_eq h).1, ← (pl_sE_eq h).1, hb₁]

/-- **Exact form**: with the reference `γ = −ε(u_{2,b})` and `sE W₂ ≠ 0`,
`out₁ − out₂ − out₃ = −D_a·n_bW₂ − D_{ab}`. -/
theorem pl_out_triple_exact {u₁ u₂ u₃ Y₁ Y₂ Y₃ : OE .two Λ} (hu₁ : bulk u₁ = 0)
    (hu₂ : bulk u₂ = 0) (hu₃ : bulk u₃ = 0) (hb₁ : (u₁ : SA .two Λ).b = (u₂ : SA .two Λ).b)
    (hb₃ : (u₃ : SA .two Λ).b = (u₂ : SA .two Λ).b)
    (h : PlRel (oexp (-u₁) * Y₁) (oexp (-u₂) * Y₂) (oexp (-u₃) * Y₃))
    (hs : sE (oexp (-u₂) * Y₂) ≠ 0) :
    plOut (-ε (u₂ : SA .two Λ).b) u₁ Y₁ - plOut (-ε (u₂ : SA .two Λ).b) u₂ Y₂ -
        plOut (-ε (u₂ : SA .two Λ).b) u₃ Y₃ =
      -(ε (u₁ : SA .two Λ).a - ε (u₂ : SA .two Λ).a - ε (u₃ : SA .two Λ).a) *
          nB (oexp (-u₂) * Y₂) -
        (ε (u₁ : SA .two Λ).ab - ε (u₂ : SA .two Λ).ab - ε (u₃ : SA .two Λ).ab) := by
  rw [pl_out_triple hu₁ hu₂ hu₃ hb₁ hb₃ h, div_self hs]; ring

end Pure

/-! ### States -/

section States

variable {L N : ℕ} [NeZero L]

/-- Componentwise relative triples of observable states. -/
structure PlRelSt (o₁ o₂ o₃ : ObsSt .two L N) : Prop where
  V : ∀ b, PlRel (o₁.V b) (o₂.V b) (o₃.V b)
  W : ∀ b, PlRel (o₁.W b) (o₂.W b) (o₃.W b)
  K : ∀ X, PlRel (o₁.K X) (o₂.K X) (o₃.K X)
  u : PlRel o₁.u o₂.u o₃.u

section Diff

variable {Λ : Type*} [DecidableEq Λ]

/-- `a`, `ab` parts `F − G`; `∅`, `b` parts those of `G`. -/
def plDiffS (F G : SA .two Λ) : SA .two Λ := ⟨G.e, F.a - G.a, G.b, F.ab - G.ab⟩

theorem plDiffS_mem (F G : OE .two Λ) :
    plDiffS (F : SA .two Λ) (G : SA .two Λ) ∈ OEv .two Λ := by
  obtain ⟨-, f2, -, f4⟩ := mem_OEv.1 F.2
  obtain ⟨g1, g2, g3, g4⟩ := mem_OEv.1 G.2
  refine mem_OEv.2 ⟨g1, ?_, g3, ?_⟩
  · show inv' ((F : SA .two Λ).a - (G : SA .two Λ).a) = _
    rw [map_sub, f2, g2, ← smul_sub]; rfl
  · show inv' ((F : SA .two Λ).ab - (G : SA .two Λ).ab) = _
    rw [map_sub, f4, g4]; rfl

/-- **The difference datum with the reference `∅`/`b` parts.** -/
def plDiffO (F G : OE .two Λ) : OE .two Λ := ⟨plDiffS (F : SA .two Λ) (G : SA .two Λ),
  plDiffS_mem F G⟩

theorem pl_rel_diffO {F G : OE .two Λ} (he : (G : SA .two Λ).e = (F : SA .two Λ).e)
    (hb : (G : SA .two Λ).b = (F : SA .two Λ).b) : PlRel F G (plDiffO F G) where
  e1 := he
  e2 := he
  b1 := hb
  b2 := hb
  a := rfl
  ab := rfl

theorem pl_prjO_false_eq {F G : OE .two Λ} (h : prjO false F = prjO false G) :
    (F : SA .two Λ).e = (G : SA .two Λ).e ∧ (F : SA .two Λ).b = (G : SA .two Λ).b := by
  have h' := congrArg (fun F : OE .two Λ => (F : SA .two Λ)) h
  simp only [coe_prjO] at h'
  have he := congrArg SA.e h'
  have ha := congrArg SA.a h'
  simp only [prjS_e, prjS_a, cmp_false] at he ha
  exact ⟨he, ha⟩

theorem pl_prjO_diffO (F G : OE .two Λ) : prjO false (plDiffO F G) = prjO false G :=
  Subtype.ext (SA.ext rfl rfl rfl rfl)

end Diff

/-- The difference state: `a`, `ab` parts `o₁ − o₂`, `∅`/`b` parts those of `o₂`. -/
def plDiffSt (o₁ o₂ : ObsSt .two L N) : ObsSt .two L N :=
  ⟨fun b => plDiffO (o₁.V b) (o₂.V b), fun b => plDiffO (o₁.W b) (o₂.W b),
    fun X => plDiffO (o₁.K X) (o₂.K X), plDiffO o₁.u o₂.u⟩

/-- **The difference state carries the `σ_b` (and `∅`) part of `o₂`** (`rpb_b_eq` setting). -/
theorem pl_diff_prj (o₁ o₂ : ObsSt .two L N) : prjSt false (plDiffSt o₁ o₂) = prjSt false o₂ := by
  simp only [prjSt, plDiffSt, ObsSt.mk.injEq]
  exact ⟨funext fun b => pl_prjO_diffO _ _, funext fun b => pl_prjO_diffO _ _,
    funext fun X => pl_prjO_diffO _ _, pl_prjO_diffO _ _⟩

theorem pl_diff_isObs (o₁ : ObsSt .two L N) {o₂ : ObsSt .two L N} (h : o₂.IsObs) :
    (plDiffSt o₁ o₂).IsObs where
  V b := (Subtype.ext rfl : bulk (plDiffO (o₁.V b) (o₂.V b)) = bulk (o₂.V b)).trans (h.V b)
  W b := (Subtype.ext rfl : bulk (plDiffO (o₁.W b) (o₂.W b)) = bulk (o₂.W b)).trans (h.W b)
  K X := (Subtype.ext rfl : bulk (plDiffO (o₁.K X) (o₂.K X)) = bulk (o₂.K X)).trans (h.K X)
  u := (Subtype.ext rfl : bulk (plDiffO o₁.u o₂.u) = bulk o₂.u).trans h.u

/-- **Triples from equal `σ_b` projections.** -/
theorem pl_relSt_diff {o₁ o₂ : ObsSt .two L N} (h : prjSt false o₁ = prjSt false o₂) :
    PlRelSt o₁ o₂ (plDiffSt o₁ o₂) := by
  simp only [prjSt, ObsSt.mk.injEq] at h
  obtain ⟨hV, hW, hK, hu⟩ := h
  have f := fun {F G : OE .two (Lam 2 L N)} (h : prjO false F = prjO false G) =>
    pl_rel_diffO (F := F) (G := G) (pl_prjO_false_eq h).1.symm (pl_prjO_false_eq h).2.symm
  exact ⟨fun b => f (congrFun hV b), fun b => f (congrFun hW b), fun X => f (congrFun hK X), f hu⟩

/-- **Relocation does not touch the `∅`/`b` parts.** -/
theorem pl_rrSt_prj (R : RGPar 2 L N) (j : ℕ) (st : RawSt 2 L N) (g μ : ℝ) (D : Fam 2 L N)
    (K : Act 2 L N) (a a' : Lam 2 L N) (β : (Fin 2 → ℕ) → ℂ) (o : ObsSt .two L N) :
    prjSt false (rrSt R j st g μ D K a a' β o) = prjSt false o := by
  simp only [prjSt, rrSt, ObsSt.mk.injEq, and_true, true_and]
  refine ⟨funext fun b => ?_, funext fun Y => ?_⟩
  · show prjO false (o.V b - rrD a a' β b) = prjO false (o.V b)
    refine Subtype.ext (SA.ext ?_ ?_ rfl rfl)
    · simp
    · simp [cmp_false]
  · show prjO false (o.K Y + _) = prjO false (o.K Y)
    rw [map_add, map_sum]
    conv_rhs => rw [← add_zero (prjO false (o.K Y))]
    congr 1
    refine sum_eq_zero fun b _ => ?_
    refine Subtype.ext (SA.ext ?_ ?_ rfl rfl)
    · simp [rrDel]
    · simp [rrDel, cmp_false]

end States

/-! ### The integrand and the chain-invariant `W` -/

section Chain

variable {L N : ℕ} [NeZero L]

/-- **The scale-`j` integrand maps state triples to triples.** -/
theorem pl_rel_ZinO (R : RGPar 2 L N) (j : ℕ) (st : RawSt 2 L N) (g μ : ℝ) (D : Fam 2 L N)
    (K : Act 2 L N) {o₁ o₂ o₃ : ObsSt .two L N} (h : PlRelSt o₁ o₂ o₃) :
    PlRel (ZinO R j st g μ D K o₁) (ZinO R j st g μ D K o₂) (ZinO R j st g μ D K o₃) :=
  pl_rel_gZO j (fun b => pl_rel_IbO (fun b => pl_rel_add (pl_rel_emb _) (h.V b))
    (fun b => pl_rel_add (pl_rel_emb _) (h.W b)) b) (fun X => pl_rel_add (pl_rel_emb _) (h.K X))

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N) (m : ℕ)

/-- **The chain-invariant generating element** `e^{−u_k}·ω_{Γ_k}Z_k` along the history from `m`. -/
def plW (o : ObsSt .two L N) (k : ℕ) (t : Hist.Seq (Xs R)) : OE .two (Lam 2 L N) :=
  oexp (-(obsHistFrom R P m o k t).u) * omegaCO (Γh R k t) (ZhOF R P m o k t)

theorem pl_chOF_eq (o : ObsSt .two L N) (i : ℕ) (t : Hist.Seq (Xs R)) :
    chOF R P m o i t = ch R i t • oexp (-uObsTot P i (stCov R i (rawHist R i t))
      (fullV R i (rawHist R i t) (t i).1 (t i).2.1 (obsHistFrom R P m o i t))
      (fullW (rawHist R i t) (rawD R (rawHist R i t).u (t i).2.2) (obsHistFrom R P m o i t))
      (fullK R i (rawHist R i t) (rawK R (rawHist R i t).u (t i).2.2)
        (obsHistFrom R P m o i t))) := by
  rw [chOF, uOutO, expU, smul_smul]; rfl

/-- **The accumulated constants**: `e^{−u_m}∏_{m ≤ i < k} chOF_i = (∏ ch_i)·e^{−u_k}`. -/
theorem pl_cst_chain {o : ObsSt .two L N} (ho : o.IsObs) (t : Hist.Seq (Xs R)) :
    ∀ d, oexp (-o.u) * ∏ i ∈ Ico m (m + d), chOF R P m o i t =
      (∏ i ∈ Ico m (m + d), ch R i t) • oexp (-(obsHistFrom R P m o (m + d) t).u)
  | 0 => by simp [obsHistFrom_self]
  | d + 1 => by
    rw [← Nat.add_assoc, prod_Ico_succ_top (by omega), prod_Ico_succ_top (by omega), ← mul_assoc,
      pl_cst_chain ho t d, pl_chOF_eq, smul_mul_smul_comm, obsHistFrom_succ (by omega)]
    have hO := obsHistFrom_isObs (R := R) (P := P) (j := m) ho t (m + d)
    have hO' := obsHistFrom_isObs (R := R) (P := P) (j := m) ho t (m + d + 1)
    rw [obsHistFrom_succ (by omega)] at hO'
    have hu : bulk (uObsTot P (m + d) (stCov R (m + d) (rawHist R (m + d) t))
        (fullV R (m + d) (rawHist R (m + d) t) (t (m + d)).1 (t (m + d)).2.1
          (obsHistFrom R P m o (m + d) t))
        (fullW (rawHist R (m + d) t) (rawD R (rawHist R (m + d) t).u (t (m + d)).2.2)
          (obsHistFrom R P m o (m + d) t))
        (fullK R (m + d) (rawHist R (m + d) t) (rawK R (rawHist R (m + d) t).u (t (m + d)).2.2)
          (obsHistFrom R P m o (m + d) t))) = 0 := by
      have h1 := hO'.u
      have h2 := hO.u
      change bulk ((obsHistFrom R P m o (m + d) t).u + _) = 0 at h1
      rw [map_add, h2, zero_add] at h1
      exact h1
    rw [← oexp_add_obs (by rw [map_neg, hO.u, neg_zero]) (by rw [map_neg, hu, neg_zero]),
      ← neg_add]
    rfl

/-- One step of `pl_cst_chain`: `e^{−u_i}chOF_i = ch_i·e^{−u_{i+1}}` (`m ≤ i`). -/
theorem pl_cst_step {o : ObsSt .two L N} (ho : o.IsObs) (t : Hist.Seq (Xs R)) {i : ℕ}
    (hi : m ≤ i) :
    oexp (-(obsHistFrom R P m o i t).u) * chOF R P m o i t =
      ch R i t • oexp (-(obsHistFrom R P m o (i + 1) t).u) := by
  rw [pl_chOF_eq, mul_smul_comm, obsHistFrom_succ hi]
  have hO := obsHistFrom_isObs (R := R) (P := P) (j := m) ho t i
  have hO' := obsHistFrom_isObs (R := R) (P := P) (j := m) ho t (i + 1)
  rw [obsHistFrom_succ hi] at hO'
  have hu : bulk (uObsTot P i (stCov R i (rawHist R i t))
      (fullV R i (rawHist R i t) (t i).1 (t i).2.1 (obsHistFrom R P m o i t))
      (fullW (rawHist R i t) (rawD R (rawHist R i t).u (t i).2.2) (obsHistFrom R P m o i t))
      (fullK R i (rawHist R i t) (rawK R (rawHist R i t).u (t i).2.2)
        (obsHistFrom R P m o i t))) = 0 := by
    have h1 := hO'.u
    change bulk ((obsHistFrom R P m o i t).u + _) = 0 at h1
    rw [map_add, hO.u, zero_add] at h1
    exact h1
  rw [← oexp_add_obs (by rw [map_neg, hO.u, neg_zero]) (by rw [map_neg, hu, neg_zero]),
    ← neg_add]
  rfl

/-- The generating element at the top: `e^{−u_{N_h+1}}·lastOF` (the last factor of `Π'`). -/
def plWTop (o : ObsSt .two L N) (Nh : ℕ) (t : Hist.Seq (Xs R)) : OE .two (Lam 2 L N) :=
  oexp (-(obsHistFrom R P m o (Nh + 1) t).u) * lastOF R P m o Nh t

set_option maxHeartbeats 400000 in
/-- **The top link**: `plW N_h = ch_{N_h}·plWTop`. -/
theorem pl_W_top {Nh : ℕ} (hN : Nh + 2 = N) (hρ1 : R.ρ < 1) (hspl : SplitSmall R.P L R.ρ)
    (hm0 : 0 < R.msq) (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))))
    (hV : ∀ j < Nh, ValidAt R j) (hVL : ValidAtL R Nh) (b μ₀ : ℝ) {o : ObsSt .two L N}
    (ho : o.IsObs) (h0 : ObsLocInv P m o) (hmN : m ≤ Nh) :
    plW R P m o Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) =
      ch R Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) •
        plWTop R P m o Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) := by
  have hk' := hist_omegaOF_from R P m o hN hρ1 hspl hm0 hm hV hVL b μ₀ ho h0 hmN le_rfl
  unfold plW plWTop
  rw [hk', prodHiF, Nat.Ico_succ_singleton, prod_singleton, ← mul_assoc,
    pl_cst_step R P m ho _ hmN, smul_mul_assoc]

set_option maxHeartbeats 400000 in
/-- **Chain invariance of `W`**: `plW m = (∏_{m ≤ i < k} ch_i)·plW k` (`m ≤ k ≤ N_h`). -/
theorem pl_W_chain {Nh : ℕ} (hN : Nh + 2 = N) (hρ1 : R.ρ < 1) (hspl : SplitSmall R.P L R.ρ)
    (hm0 : 0 < R.msq) (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))))
    (hV : ∀ j < Nh, ValidAt R j) (hVL : ValidAtL R Nh) (b μ₀ : ℝ) {o : ObsSt .two L N}
    (ho : o.IsObs) (h0 : ObsLocInv P m o) {k : ℕ} (hmk : m ≤ k) (hk : k ≤ Nh) :
    plW R P m o m (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) =
      (∏ i ∈ Ico m k, ch R i (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)) •
        plW R P m o k (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) := by
  set t := traj (rgData R) ((L : ℝ) ^ 2) b μ₀ with ht
  have hm' := hist_omegaOF_from R P m o hN hρ1 hspl hm0 hm hV hVL b μ₀ ho h0 le_rfl
    (hmk.trans hk)
  have hk' := hist_omegaOF_from R P m o hN hρ1 hspl hm0 hm hV hVL b μ₀ ho h0 hmk hk
  have hsplit : prodHiF R P m o Nh m t =
      (∏ i ∈ Ico m k, chOF R P m o i t) * prodHiF R P m o Nh k t := by
    rw [prodHiF, prodHiF, ← mul_assoc, prod_Ico_consecutive _ hmk (by omega)]
  have hc := pl_cst_chain R P m ho t (k - m)
  rw [show m + (k - m) = k by omega] at hc
  unfold plW
  rw [obsHistFrom_self, hm', hsplit, ← hk', ← mul_assoc, hc, smul_mul_assoc]

/-- **Triples at the relocation scale**: `plW` of `(P, o₁)`, `(P', o₂)`, `(P', o₃)` at `m` form a
triple when `(rrStH o₁, o₂, o₃)` does (`rr_ZhOF`: same `Z_m`; `rrSt` keeps `u`). -/
theorem pl_W_rel_m (P' : ObsPts 2 L N) (t : Hist.Seq (Xs R)) (a a' : Lam 2 L N)
    (β : (Fin 2 → ℕ) → ℂ) {o₁ o₂ o₃ : ObsSt .two L N}
    (h : PlRelSt (rrStH R m t a a' β o₁) o₂ o₃) :
    PlRel (plW R P m o₁ m t) (plW R P' m o₂ m t) (plW R P' m o₃ m t) := by
  unfold plW
  rw [rr_ZhOF R P P' m t a a' β o₁, obsHistFrom_self, obsHistFrom_self, obsHistFrom_self]
  refine pl_rel_mul (pl_rel_oexp (pl_rel_neg h.u)) (pl_rel_omegaCO _ ?_)
  unfold ZhOF
  rw [obsHistFrom_self, obsHistFrom_self, obsHistFrom_self]
  exact pl_rel_ZinO R m _ _ _ _ _ h

/-- **Triples at every scale `m ≤ k ≤ N_h`** (chain invariance; `∏ ch ≠ 0`). -/
theorem pl_W_rel {Nh : ℕ} (hN : Nh + 2 = N) (hρ1 : R.ρ < 1) (hspl : SplitSmall R.P L R.ρ)
    (hm0 : 0 < R.msq) (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))))
    (hV : ∀ j < Nh, ValidAt R j) (hVL : ValidAtL R Nh) (b μ₀ : ℝ) (P' : ObsPts 2 L N)
    (a a' : Lam 2 L N) (β : (Fin 2 → ℕ) → ℂ) {o₁ o₂ o₃ : ObsSt .two L N}
    (h₁ : o₁.IsObs) (h₂ : o₂.IsObs) (h₃ : o₃.IsObs) (hl₁ : ObsLocInv P m o₁)
    (hl₂ : ObsLocInv P' m o₂) (hl₃ : ObsLocInv P' m o₃)
    (h : PlRelSt (rrStH R m (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) a a' β o₁) o₂ o₃)
    {k : ℕ} (hmk : m ≤ k) (hk : k ≤ Nh)
    (hc : ∏ i ∈ Ico m k, ch R i (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) ≠ 0) :
    PlRel (plW R P m o₁ k (traj (rgData R) ((L : ℝ) ^ 2) b μ₀))
      (plW R P' m o₂ k (traj (rgData R) ((L : ℝ) ^ 2) b μ₀))
      (plW R P' m o₃ k (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)) := by
  have H := pl_rel_smul (∏ i ∈ Ico m k, ch R i (traj (rgData R) ((L : ℝ) ^ 2) b μ₀))⁻¹
    (pl_W_rel_m R P m P' _ a a' β h)
  rwa [pl_W_chain R P m hN hρ1 hspl hm0 hm hV hVL b μ₀ h₁ hl₁ hmk hk,
    pl_W_chain R P' m hN hρ1 hspl hm0 hm hV hVL b μ₀ h₂ hl₂ hmk hk,
    pl_W_chain R P' m hN hρ1 hspl hm0 hm hV hVL b μ₀ h₃ hl₃ hmk hk, smul_smul, smul_smul,
    smul_smul, inv_mul_cancel₀ hc, one_smul, one_smul, one_smul] at H

end Chain

end

end PtCorr2
