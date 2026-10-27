import Spin2.Pair.ZeroNormA
import Spin2.Gam.GamRemLast
import PtCorr2.Last.LastOneTI

/-!
# PR6, item (b) and the size of `εF_a`: `LastOneRem` reduced to the activity of the last step

Pair observable at `x`, last step `j = N_h + 1` (`C = C_N`, inputs `V, 𝒲, K` of scale `N - 1`).

* **`P₀ = 1` exactly** (`zP0_eq_one`): the bulk inputs of the last step are translation covariant
  and `C_N` is translation invariant, so `ε𝒲_N(B)_∅ = εS(B) - εS(Λ)|B|/|Λ| = 0`
  (`PtCorr2.finO_last_TI`). Item (a) needs no smallness.
* `c2(F_N)_a = β_N + c2K_N(Λ)_a`, `ε(F_N)_a = εK_N(Λ)_a` (the block remainders cancel), and
  `β_N = β - β ν̄ - e_𝒲` (`PtCorr2.betaN_last`) with
  - `ν̄ = m₂F_{C_N}(ψ̄_aψ_a, V'(Λ)_∅)`, `|ν̄| ≤ C_f(ℓ²/8 + ℓ⁴/128)ǧ_{N_h}` (**`mass2_bulk_last_le`**:
    `V'(Λ)_∅ = V_{κ_N}(Λ) + const`, `mass2_FC_pbp_Vcoup`, the final couplings of `GlueOut`);
  - `e_𝒲 = ∑_Bm₂(𝔼θ𝒲^{obs}_{N_h+1}(B))_a`, `|e_𝒲| ≤ c_BQ₁w/s²` (**`mass2_EthO_W_le`**, the `m₂`
    copy of `eps_EthO_W_le`).
* Named input **`LastKRem K`** (open: no bound of the activity `K_N(Λ) = Knext2O(Λ)` of the
  observable last step exists; it needs an observable copy of `LastN.lastK_ts`):
  `|c2K_N(Λ)_a| ≤ Kǧ_{N_h}|β_{a,N-1}|`, `|εK_N(Λ)_a| ≤ K|β_{a,N-1}|/|Z_N|`.
* **`lastOneRem_of`**: from the block bound `w = c_Wǧ_{N_h}s_{N_h}²|β_{N_h}|` of `𝒲^{obs}_{N_h+1}`,
  `Case2TopStep`, `GlueOut`, `LastKRem K` and
  `(C_f(ℓ²/8 + ℓ⁴/128) + (9/4)c_BQ₁c_W + K)ǧ_{N_h} ≤ ½`: `LastOneRem K`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs.SA Obs.LocObs

variable {L N : ℕ} [NeZero L]

/-! ### Two bounds of the last step -/

section Gen

/-- `|m₂(e^{ℒ_C}F)| ≤ Q₁‖F‖_{T_j(ℓ)}ℓ^{-2}` for `F ∈ 𝒩(B^□)`, `GoodCov2 j ℓ C` (copy of
`norm_eps_expLC_le`). -/
theorem norm_mass2_expLC_leS {d : ℕ} (hd : 1 ≤ d) (hL : pauliL0 d ≤ L) {j : ℕ} (hj : j < N)
    {ℓ : ℝ} (hℓ : 0 < ℓ) {C : Matrix (Lam d L N) (Lam d L N) ℂ} (hC : GoodCov2 j ℓ C)
    {b : Fin d → ℕ}
    {F : Alg d L N} (hF : F ∈ NX (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N))) :
    ‖mass2 (expLC C F)‖ ≤ Q1 d * (Tj d (L : ℝ) j ℓ F).toReal * ℓ⁻¹ ^ 2 := by
  have h1 := norm_mass2_le hℓ (j + 1) (expLC C F)
  have h2 := EthE_succ_le hd hL hj hℓ hC hF
  rw [ECC_theta] at h2
  have h3 : ENNReal.ofReal (pq d ^ nb j (nbhd j (blockSet (L := L) (N := N) j b))) *
      Tj d (L : ℝ) j ℓ F ≤ ENNReal.ofReal (Q1 d) * Tj d (L : ℝ) j ℓ F :=
    mul_le_mul_right' (ENNReal.ofReal_le_ofReal (pq_pow_le_Q1 hd hj.le b)) _
  have h4 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (tNorm_ne_top (Lpow_pos j) hℓ F)) (h2.trans h3)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by
    have := one_le_Q1 hd; linarith)] at h4
  exact h1.trans (mul_le_mul_of_nonneg_right h4 (sq_nonneg _))

/-- **The `𝒲` tadpole of a step** (`m₂` copy of `eps_EthO_W_le`):
`|∑_Bm₂(e^{ℒ_C}𝒲^{obs}(B)_a)| ≤ c_BQ₁w s^{-2}`. -/
theorem mass2_EthO_W_le (P : Obs2.ObsPts 2 L N) {j : ℕ} (hj : j < N) (hLp : pauliL0 2 ≤ L)
    {s : ℝ} (hs : 0 < s) {C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ} (hC : GoodCov2 j s C)
    (o : Obs2.ObsSt .two L N) (ho : ObsLocInv P j o) (st : RawSt 2 L N) (D : Fam 2 L N) {w : ℝ}
    (hw : 0 ≤ w)
    (hW : ∀ b ∈ blockIdx (L := L) (N := N) j, Obs2.oTo Obs2.wA j s (o.W b) ≤ ENNReal.ofReal w) :
    ‖∑ b ∈ blockIdx (L := L) (N := N) j,
        mass2 (Obs2.EthO C (Obs2.fullW st D o b) : SA .two (Lam 2 L N)).a‖ ≤
      cBn * (Q1 2 * w) * s⁻¹ ^ 2 := by
  classical
  have e : ∀ b, mass2 (Obs2.EthO C (Obs2.fullW st D o b) : SA .two (Lam 2 L N)).a =
      mass2 (expLC C (o.W b : SA .two (Lam 2 L N)).a) := by
    intro b
    rw [Obs2.EthO_a_eq]
    congr 2
    exact Obs2.emb_add_cmp true _ _
  simp only [e]
  refine (norm_sum_le _ _).trans ?_
  set S := blockIdx (L := L) (N := N) j
  set S' := S.filter (fun b => P.a ∈ nbhd j (blockSet (L := L) (N := N) j b))
  have hsplit : ∑ b ∈ S, ‖mass2 (expLC C (o.W b : SA .two (Lam 2 L N)).a)‖ =
      ∑ b ∈ S', ‖mass2 (expLC C (o.W b : SA .two (Lam 2 L N)).a)‖ := by
    refine (sum_subset (filter_subset _ _) fun b hb hb' => ?_).symm
    have hna : P.a ∉ nbhd j (blockSet (L := L) (N := N) j b) := fun h =>
      hb' (mem_filter.2 ⟨hb, h⟩)
    rw [((ho.W b).2.2.2.2.1 hna).1, map_zero]
    show ‖mass2 (0 : Alg 2 L N)‖ = 0
    rw [show mass2 (0 : Alg 2 L N) = 0 from map_zero Obs2.mass2L, norm_zero]
  rw [hsplit]
  have hQ : 0 ≤ Q1 2 := by have := one_le_Q1 (d := 2) (by norm_num); linarith
  have hterm : ∀ b ∈ S', ‖mass2 (expLC C (o.W b : SA .two (Lam 2 L N)).a)‖ ≤
      Q1 2 * w * s⁻¹ ^ 2 := by
    intro b hb
    have hbS := (mem_filter.1 hb).1
    refine (norm_mass2_expLC_leS (by norm_num) hLp hj hs hC (ho.W b).2.1).trans ?_
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hQ) (sq_nonneg _)
    have h := hW b hbS
    rw [Obs2.oTo_wA] at h
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    rwa [ENNReal.toReal_ofReal hw] at h2
  have hc : (S'.card : ℝ) ≤ cBn := by
    exact_mod_cast Classical.choose_spec (Obs2.card_blocks_near 2) L N j P.a S subset_rfl
  calc ∑ b ∈ S', ‖mass2 (expLC C (o.W b : SA .two (Lam 2 L N)).a)‖
      ≤ ∑ _b ∈ S', Q1 2 * w * s⁻¹ ^ 2 := sum_le_sum hterm
    _ = S'.card * (Q1 2 * w * s⁻¹ ^ 2) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ cBn * (Q1 2 * w * s⁻¹ ^ 2) :=
        mul_le_mul_of_nonneg_right hc (mul_nonneg (mul_nonneg hQ hw) (sq_nonneg _))
    _ = cBn * (Q1 2 * w) * s⁻¹ ^ 2 := by ring

/-- **The one-loop coefficient of the last step**:
`|m₂F_{C_N}(ψ̄_aψ_a, V_{κ_N}(Λ))| ≤ C_f(ℓ²/8 + ℓ⁴/128)ǧ_{N_h}` (final couplings from `GlueOut`). -/
theorem mass2_bulk_last_le (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {Nh : ℕ}
    (hNh : Nh + 2 = N) (hV : ∀ i < Nh, ValidAt R i) (hVL : ValidAtL R Nh)
    (hVN : LastN.ValidLast R (Nh + 1)) {Cf : ℝ} (t : Hist.Seq (Xs R)) (hG : GlueOut R Nh Cf t)
    (a : Lam 2 L N) :
    ‖mass2 (FC (LastN.stCovN R (Nh + 1) (histOut R Nh t).st) (LocObs.pbp a)
        (Vcoup (lastOut R Nh t).κ univ))‖ ≤
      Cf * (R.ℓ ^ 2 / 8 + R.ℓ ^ 4 / 128) * (t Nh).1 := by
  obtain ⟨-, ⟨-, -, hnu, hgg, -⟩⟩ := hG
  set st := (histOut R Nh t).st with hst
  set out := lastOut R Nh t with hout
  set g := (t Nh).1
  have H : RawInv R (Nh + 1) st := rawInv_histU R hV hVL t (Nh + 1) le_rfl
  have hC := (LastN.covN hVN H).1
  have hρ0 : 0 ≤ R.ρ := hVL.2.2.2.2.1
  have hρ8 : R.ρ ≤ 1 / 8 := hVL.2.2.2.2.2.1
  have hZ : st.Z ≠ 0 := H.Z_ne_zero (by linarith)
  have hZ1 : 0 < ‖st.Z‖ := norm_pos_iff.2 hZ
  have hZN : 7 / 8 * ‖st.Z‖ ≤ ‖stZ' R st‖ := norm_stZ'_ge R (j := 0) st hρ0 hρ8
  have hZp : 0 < ‖stZ' R st‖ := by linarith
  have hoZ : out.Z = stZ' R st := rfl
  rw [hoZ] at hnu hgg
  set Zn := ‖stZ' R st‖ with hZn
  set c := R.ℓ ^ 2 / (16 * Zn) with hc
  have hc0 : 0 ≤ c := by positivity
  have hc2 : (fscale (stZ' R st) * R.ℓ / 4) ^ 2 = c := by
    rw [fscale_sq, hc, ← hZn]; field_simp
  have hlf := norm_lfunC_leT hC (show Nh + 1 + 1 = N by omega) a
  rw [show (fscale (stZ' R st) * R.ℓ / 4) ^ 4 = ((fscale (stZ' R st) * R.ℓ / 4) ^ 2) ^ 2 by ring,
    hc2] at hlf
  set X := ((L : ℝ) ^ (Nh + 1 + 1)) ^ 2 with hX
  have hs1 : ‖∑ x, LastN.stCovN R (Nh + 1) st a x‖ ≤ X * c :=
    norm_sum_top_le (k := Nh + 1) (by omega) _ fun z => (Obs2.good_entry hC a z).trans (le_of_eq hc2)
  have hs2 : ‖∑ x, LastN.stCovN R (Nh + 1) st x a‖ ≤ X * c :=
    norm_sum_top_le (k := Nh + 1) (by omega) _ fun z => (Obs2.good_entry hC z a).trans (le_of_eq hc2)
  have hCg : 0 ≤ Cf * g := (norm_nonneg _).trans hnu
  have hnu' : X * ‖out.κ.nu‖ ≤ Cf * g * Zn := by
    have e : ‖(L : ℂ) ^ (2 * (Nh + 1 + 1)) * out.κ.nu / stZ' R st‖ = X * ‖out.κ.nu‖ / Zn := by
      rw [norm_div, norm_mul, norm_pow, Complex.norm_natCast, hX, ← pow_mul, mul_comm 2]
    rw [e, div_le_iff₀ hZp] at hnu
    exact hnu
  have hg' : ‖out.κ.g‖ ≤ Cf * g * Zn ^ 2 := by
    have e : ‖out.κ.g / stZ' R st ^ 2‖ = ‖out.κ.g‖ / Zn ^ 2 := by rw [norm_div, norm_pow]
    rw [e, div_le_iff₀ (by positivity)] at hgg
    exact hgg
  rw [Obs2.mass2_FC_pbp_Vcoup]
  have hX0 : 0 ≤ X := by positivity
  calc ‖out.κ.nu * (∑ x, LastN.stCovN R (Nh + 1) st a x + ∑ x, LastN.stCovN R (Nh + 1) st x a) -
        out.κ.g * Obs2.lfunC (LastN.stCovN R (Nh + 1) st) a‖
      ≤ ‖out.κ.nu‖ * (X * c + X * c) + ‖out.κ.g‖ * (2 * c ^ 2) := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul, norm_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add hs1 hs2))
          (norm_nonneg _)) (mul_le_mul_of_nonneg_left hlf (norm_nonneg _))
    _ = (X * ‖out.κ.nu‖) * (2 * c) + ‖out.κ.g‖ * (2 * c ^ 2) := by ring
    _ ≤ (Cf * g * Zn) * (2 * c) + (Cf * g * Zn ^ 2) * (2 * c ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_right hnu' (by positivity))
          (mul_le_mul_of_nonneg_right hg' (by positivity))
    _ = Cf * (R.ℓ ^ 2 / 8 + R.ℓ ^ 4 / 128) * g := by
        rw [hc]; field_simp; ring

end Gen

/-! ### Along the trajectory -/

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- The activity `K_N(Λ)` of the observable last step (pair history at `x`). -/
def zKN (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) : Obs.OE .two (Lam 2 L N) :=
  Obs2.Knext2O (ptsX x) (Nh + 1) (lC R Nh m b μ₀) (lV R Nh m b μ₀ x) (lW R Nh m b μ₀ x)
    (lK R Nh m b μ₀ x) univ

/-- **Named input (PR6, the activity of the observable last step).** The `σ_a` component of
`K_N(Λ)`: `|c2K_N(Λ)_a| ≤ Kǧ_{N_h}|β_{a,N-1}|`, `|εK_N(Λ)_a| ≤ K|β_{a,N-1}|/|Z_N|` (the natural
size of an observable activity `≲ r²s²|β|` at the last scale). Open: no estimate of the observable
`Knext2O` at `j + 1 = N` exists (bulk: `LastN.lastK_ts`). -/
def LastKRem (Nh : ℕ) (m b μ₀ : ℝ) (KK : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ‖Suscept.c2 (zKN R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a‖ ≤
        KK * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 *
          ‖Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖ ∧
    ‖ε (zKN R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a‖ ≤
      KK * ‖Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖ /
        ‖(lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z‖

set_option maxHeartbeats 4000000 in
/-- **The one-point part of the last step along one trajectory** (pair history at `x`):
`P₀ = 1`, `c2(F_N)_a - β_{a,N-1} = -β_{a,N-1}ν̄ - e_𝒲 + c2K_N(Λ)_a` with the bounds of `ν̄`, `e_𝒲`,
and `ε(F_N)_a = εK_N(Λ)_a`. -/
theorem lastOne_traj {Nh : ℕ} (hNh : Nh + 2 = N) {m b μ₀ Cf w : ℝ}
    (hV : ∀ i < Nh, ValidAt (R.withMsq m) i) (hVL : ValidAtL (R.withMsq m) Nh)
    (hVN : LastN.ValidLast (R.withMsq m) (Nh + 1)) (hLp : pauliL0 2 ≤ L)
    (hL8 : 2 ^ (2 + 3) + 8 * 2 < L)
    (hG : GlueOut (R.withMsq m) Nh Cf (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) (x : Lam 2 L N)
    (hw : 0 ≤ w)
    (hW : WbHc (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x))
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Nh + 1) w) :
    zP0 R Nh m b μ₀ x = 1 ∧
    ‖Suscept.c2 (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a -
        Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖ ≤
      ‖Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖ *
          (Cf * (R.ℓ ^ 2 / 8 + R.ℓ ^ 4 / 128) * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) +
        cBn * (Q1 2 * w) *
          (histS (R.withMsq m) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))⁻¹ ^ 2 +
        ‖Suscept.c2 (zKN R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a‖ ∧
    ε (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a =
      ε (zKN R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a := by
  have hℓ : 0 < R.ℓ := Fact.out
  set R' := R.withMsq m with hR'
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  set P := ptsX (L := L) (N := N) x with hPd
  set o₀ := Obs2.obsInit .two (zV b) P with ho₀
  set o := Obs2.obsHist R' P o₀ (Nh + 1) t with hod
  set st := (histOut R' Nh t).st with hst
  have ho : o.IsObs := Obs2.obsHist_isObs R' P o₀ (Obs2.obsInit_isObs .two (zV b) P) (Nh + 1) t
  have hρ0 : 0 ≤ R'.ρ := hVL.2.2.2.2.1
  have hρ8 : R'.ρ ≤ 1 / 8 := hVL.2.2.2.2.2.1
  -- the bulk inputs of the last step
  have H : RawInv R' (Nh + 1) st := rawInv_histU R' hV hVL t (Nh + 1) le_rfl
  obtain ⟨hC0, hCt, hCs, hCsym⟩ := LastN.covN hVN H
  have hjN : Nh + 1 < N := by omega
  have hVc : FamCovG (Nh + 1) (stVf R' (Nh + 1) st (histOut R' Nh t).g.re (histOut R' Nh t).nu.re) := by
    have h : stVf R' (Nh + 1) st (histOut R' Nh t).g.re (histOut R' Nh t).nu.re ∈
        BSub (L := L) (N := N) (Nh + 1) := by
      rw [stVf_eq_kap]
      exact VfamL_mem (L := L) (N := N) (d := 2) (by norm_num) hL8 hjN _
    exact h.2.1
  have hD : (histOut R' Nh t).D ∈ BSub (L := L) (N := N) (Nh + 1) :=
    (RawInv.stepL hVL (rawInv_hist R' hρ0 Nh hV t) (t Nh).1 (t Nh).2.1 (rawD_mem R' _ _)
      (rawK_mem R' _ _)).2.1
  have hWc : FamCovG (Nh + 1) (st.Wl + (histOut R' Nh t).D) := (add_mem H.hWl hD).2.1
  obtain ⟨hP0, hc2F, heF⟩ := finO_last_TI R' P (Nh + 1) st (histOut R' Nh t).g.re
    (histOut R' Nh t).nu.re (histOut R' Nh t).D (histOut R' Nh t).K o (by omega) ho hCt hVc hWc
  -- the coupling `β_N`
  have hform : ∀ b', Obs2.Loc2Form P.a (lV R Nh m b μ₀ x b' : SA .two (Lam 2 L N)).a := by
    intro b'
    have h := Obs2.obsHist_hform2 R' P o₀ t (fun b'' => Obs2.obsInit_two_form P (zV b) b'')
      (Nh + 1) b'
    rw [Obs2.histVO2_a] at h
    rw [show (lV R Nh m b μ₀ x b' : SA .two (Lam 2 L N)).a = (o.V b' : SA .two (Lam 2 L N)).a from
      Obs2.emb_add_cmp true _ _]
    exact h
  have hβN := betaN_last P (lC R Nh m b μ₀) (lV R Nh m b μ₀ x) (lW R Nh m b μ₀ x)
    (lK R Nh m b μ₀ x) (j := Nh + 1) (by omega) hform
  -- `ν̄`
  have hνe : (Obs2.VprLO (Nh + 1) (lC R Nh m b μ₀) (lV R Nh m b μ₀ x) : SA .two (Lam 2 L N)).e =
      (Vcoup (lastOut R' Nh t).κ univ : Alg 2 L N) +
        (∑ b' ∈ blockIdx (L := L) (N := N) (Nh + 1),
          LastN.upN (LastN.stCovN R' (Nh + 1) st)
            (stVf R' (Nh + 1) st (histOut R' Nh t).g.re (histOut R' Nh t).nu.re) b') •
          (1 : Alg 2 L N) := by
    rw [show lC R Nh m b μ₀ = LastN.stCovN R' (Nh + 1) st from rfl,
      show lV R Nh m b μ₀ x = Obs2.fullV R' (Nh + 1) st (histOut R' Nh t).g.re
        (histOut R' Nh t).nu.re o from rfl, VprLO_e_last R' (Nh + 1) st _ _ o ho]
    have hVNe : (LastN.VN (Nh + 1) (LastN.stCovN R' (Nh + 1) st)
        (stVf R' (Nh + 1) st (histOut R' Nh t).g.re (histOut R' Nh t).nu.re) : Alg 2 L N) =
        Vcoup (lastOut R' Nh t).κ univ :=
      LastN.rawStepN_VN R' (Nh + 1) st _ _ (histOut R' Nh t).D (histOut R' Nh t).K hCs hCsym
    rw [hVNe]
  have hν : ‖mass2 (FC (lC R Nh m b μ₀) (LocObs.pbp P.a)
      (Obs2.VprLO (Nh + 1) (lC R Nh m b μ₀) (lV R Nh m b μ₀ x) : SA .two (Lam 2 L N)).e)‖ ≤
      Cf * (R.ℓ ^ 2 / 8 + R.ℓ ^ 4 / 128) * (t Nh).1 := by
    rw [hνe, FC_add_right, FC_smul_right, Obs2.FC_one_right, smul_zero, add_zero]
    exact mass2_bulk_last_le R' hNh hV hVL hVN t hG P.a
  -- `e_𝒲`
  have hs : 0 < histS R' (Nh + 1) t := by
    have hZ : st.Z ≠ 0 := H.Z_ne_zero (by linarith)
    exact mul_pos (fscale_pos hZ) hℓ
  have heW : ‖∑ b' ∈ blockIdx (L := L) (N := N) (Nh + 1),
      mass2 (Obs2.EthO (lC R Nh m b μ₀) (lW R Nh m b μ₀ x b') : SA .two (Lam 2 L N)).a‖ ≤
      cBn * (Q1 2 * w) * (histS R' (Nh + 1) t)⁻¹ ^ 2 := by
    have hZ : st.Z ≠ 0 := H.Z_ne_zero (by linarith)
    have hζ8 : ‖stZeta R' st‖ ≤ 1 / 8 := (absorb_le R' hρ0 _ _).trans hρ8
    have hs' : 0 < fscale (stZ' R' st) * R'.ℓ :=
      mul_pos (fscale_pos (mul_ne_zero hZ (one_add_ne_zero (by linarith)))) hℓ
    have hmono : fscale (stZ' R' st) * R'.ℓ / 4 ≤ histS R' (Nh + 1) t := by
      have hsc := scale_ok hZ hζ8 hℓ
      have e : stZ' R' st = st.Z * (1 + stZeta R' st) := rfl
      have eℓ : R'.ℓ = R.ℓ := rfl
      rw [e] at hs' ⊢
      show _ ≤ fscale st.Z * R'.ℓ
      rw [eℓ] at hs' ⊢
      linarith
    have hC := hC0.mono hmono
    have hval := hist_validL R' hV hVL t
    have hloc := obsLocInv_hist R' P o₀ (obsLocInv_init .two (zV b) P) t (Nh + 1)
      fun i hi => hval i (by omega)
    exact mass2_EthO_W_le P (by omega) hLp hs hC o hloc st (histOut R' Nh t).D hw hW
  refine ⟨hP0, ?_, heF⟩
  rw [show zFin R Nh m b μ₀ x = PtCorr2.finO R' P (Nh + 1) st (histOut R' Nh t).g.re
    (histOut R' Nh t).nu.re (histOut R' Nh t).D (histOut R' Nh t).K o from rfl, hc2F]
  rw [show blocks (Nh + 1) (univ : Finset (Lam 2 L N)) = blockIdx (L := L) (N := N) (Nh + 1)
    from rfl]
  rw [show (∑ B ∈ blockIdx (L := L) (N := N) (Nh + 1), mass2 ((Obs2.VpO P (Nh + 1)
      (LastN.stCovN R' (Nh + 1) st) (Obs2.fullV R' (Nh + 1) st (histOut R' Nh t).g.re
        (histOut R' Nh t).nu.re o) (Obs2.fullW st (histOut R' Nh t).D o)
      (Obs2.fullK R' (Nh + 1) st (histOut R' Nh t).K o) B : SA .two (Lam 2 L N)).a)) =
    ∑ b' ∈ blockIdx (L := L) (N := N) (Nh + 1), mass2 (Obs2.VpO P (Nh + 1) (lC R Nh m b μ₀)
      (lV R Nh m b μ₀ x) (lW R Nh m b μ₀ x) (lK R Nh m b μ₀ x) b' : SA .two (Lam 2 L N)).a
    from rfl, hβN]
  set β := Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)
  set ν := mass2 (FC (lC R Nh m b μ₀) (LocObs.pbp P.a)
      (Obs2.VprLO (Nh + 1) (lC R Nh m b μ₀) (lV R Nh m b μ₀ x) : SA .two (Lam 2 L N)).e)
  set eW := ∑ b' ∈ blockIdx (L := L) (N := N) (Nh + 1),
      mass2 (Obs2.EthO (lC R Nh m b μ₀) (lW R Nh m b μ₀ x b') : SA .two (Lam 2 L N)).a
  set kc := Suscept.c2 (zKN R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a
  have e : β - β * ν - eW + kc - β = -(β * ν) - eW + kc := by ring
  rw [show Suscept.c2 ((Obs2.Knext2O P (Nh + 1) (LastN.stCovN R' (Nh + 1) st)
      (Obs2.fullV R' (Nh + 1) st (histOut R' Nh t).g.re (histOut R' Nh t).nu.re o)
      (Obs2.fullW st (histOut R' Nh t).D o) (Obs2.fullK R' (Nh + 1) st (histOut R' Nh t).K o)
        univ : SA .two (Lam 2 L N)).a) = kc from rfl, e]
  calc ‖-(β * ν) - eW + kc‖ ≤ ‖β * ν‖ + ‖eW‖ + ‖kc‖ := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans ?_) le_rfl)
        rw [norm_neg]
    _ ≤ ‖β‖ * (Cf * (R.ℓ ^ 2 / 8 + R.ℓ ^ 4 / 128) * (t Nh).1) +
          cBn * (Q1 2 * w) * (histS R' (Nh + 1) t)⁻¹ ^ 2 + ‖kc‖ := by
        rw [norm_mul]
        exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hν (norm_nonneg _)) heW) le_rfl

set_option maxHeartbeats 4000000 in
/-- **`LastOneRem K` from the activity of the last step**: the block bound
`w = c_Wǧ_{N_h}s_{N_h}²|β_{N_h}|` of `𝒲^{obs}_{N_h+1}` (pair vertex, every point configuration),
`Case2TopStep`, `GlueOut`, `LastKRem K` and the smallness
`(C_f(ℓ²/8 + ℓ⁴/128) + (9/4)c_BQ₁c_W + K)ǧ_{N_h} ≤ ½` give `LastOneRem K` (with `P₀ = 1`). -/
theorem lastOneRem_of {Nh : ℕ} (hNh : Nh + 2 = N) {m b μ₀ Cf cW KK : ℝ}
    (hV : ∀ i < Nh, ValidAt (R.withMsq m) i) (hVL : ValidAtL (R.withMsq m) Nh)
    (hVN : LastN.ValidLast (R.withMsq m) (Nh + 1)) (hLp : pauliL0 2 ≤ L)
    (hL8 : 2 ^ (2 + 3) + 8 * 2 < L)
    (hG : GlueOut (R.withMsq m) Nh Cf (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) (hcW : 0 ≤ cW)
    (hg0 : 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1)
    (hW : ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
      WbHc (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x))
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Nh + 1)
      (cW * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 *
        histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
        ‖bt2 R (ptsX x) (zV b) m b μ₀ Nh‖))
    (htop : ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh → Case2TopStep R (ptsX x) (zV b) Nh m b μ₀)
    (hsm : (Cf * (R.ℓ ^ 2 / 8 + R.ℓ ^ 4 / 128) + 9 / 4 * (cBn * Q1 2 * cW) + KK) *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 ≤ 1 / 2)
    (hK : LastKRem R Nh m b μ₀ KK) :
    LastOneRem R Nh m b μ₀ KK ∧ ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh → zP0 R Nh m b μ₀ x = 1 := by
  set R' := R.withMsq m with hR'
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  set g := (t Nh).1 with hgd
  have hρ0 : 0 ≤ R'.ρ := hVL.2.2.2.2.1
  have hρ8 : R'.ρ ≤ 1 / 8 := hVL.2.2.2.2.2.1
  have hwx : ∀ x : Lam 2 L N, 0 ≤ cW * g * histS R' Nh t ^ 2 * ‖bt2 R (ptsX x) (zV b) m b μ₀ Nh‖ :=
    fun x => mul_nonneg (mul_nonneg (mul_nonneg hcW hg0) (sq_nonneg _)) (norm_nonneg _)
  refine ⟨fun x hx h1 hj => ?_, fun x hx h1 hj => (lastOne_traj R hNh hV hVL hVN hLp hL8 hG x
    (hwx x) (hW x hx h1 hj)).1⟩
  set B0 := ‖bt2 R (ptsX x) (zV b) m b μ₀ Nh‖ with hB0
  set w := cW * g * histS R' Nh t ^ 2 * B0 with hwd
  obtain ⟨hP0, hb2, he⟩ := lastOne_traj R hNh hV hVL hVN hLp hL8 hG x (hwx x) (hW x hx h1 hj)
  obtain ⟨hk1, hk2⟩ := hK x hx h1 hj
  have hβeq : Obs2.betaTot2 (L := L) (N := N) (Nh + 1) (lV R Nh m b μ₀ x) =
      Obs2.betaTot2 (L := L) (N := N) (Nh + 1)
        (Obs2.histVO2 R' (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) t (Nh + 1)) := by
    unfold Obs2.betaTot2
    refine sum_congr rfl fun b' _ => ?_
    rw [Obs2.histVO2_a]
    congr 1
    exact Obs2.emb_add_cmp true _ _
  have eB : ‖Obs2.betaTot2 (L := L) (N := N) (Nh + 1)
      (Obs2.histVO2 R' (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) t (Nh + 1))‖ =
      ‖bt2 R (ptsX x) (zV b) m b μ₀ (Nh + 1)‖ := rfl
  set β := ‖Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖ with hβd
  have eβ : β = ‖bt2 R (ptsX x) (zV b) m b μ₀ (Nh + 1)‖ := by rw [hβd, hβeq, eB]
  have hflow := bt2_flow R (ptsX x) (zV b) (Nh := Nh + 1) (by omega) m b μ₀ (k := Nh) (by omega)
  have hBB : B0 ≤ 2 * β := by
    rw [hB0, eβ, hflow]; exact beta_step_ge (htop x hx h1 hj).1 (htop x hx h1 hj).2
  have hZp : 0 < zH R' t (Nh + 1) := zH_pos R' hρ0 hρ8 t (Nh + 1)
  have hS : histS R' Nh t ^ 2 ≤ 9 / 8 * R.ℓ ^ 2 * (zH R' t (Nh + 1))⁻¹ :=
    histS_sq_le_z R' t Nh hρ0 hρ8
  have hs1 : (histS R' (Nh + 1) t)⁻¹ ^ 2 = zH R' t (Nh + 1) / R.ℓ ^ 2 := by
    have hℓ : 0 < R.ℓ := Fact.out
    show (fscale (rawHist R' (Nh + 1) t).Z * R'.ℓ)⁻¹ ^ 2 = ‖(rawHist R' (Nh + 1) t).Z‖ / R.ℓ ^ 2
    rw [inv_pow, mul_pow, Step2.fscale_sq, show R'.ℓ = R.ℓ from rfl]
    have : 0 < ‖(rawHist R' (Nh + 1) t).Z‖ := hZp
    field_simp
  have hwS : cBn * (Q1 2 * w) * (histS R' (Nh + 1) t)⁻¹ ^ 2 ≤
      9 / 4 * (cBn * Q1 2 * cW) * g * β := by
    have hℓ : 0 < R.ℓ := Fact.out
    have hQ : 0 ≤ Q1 2 := by have := one_le_Q1 (d := 2) (by norm_num); linarith
    have hcB : (0 : ℝ) ≤ cBn := Nat.cast_nonneg _
    have hK0 : 0 ≤ cBn * Q1 2 * cW * g := mul_nonneg (mul_nonneg (mul_nonneg hcB hQ) hcW) hg0
    rw [hs1, hwd]
    have h1 : histS R' Nh t ^ 2 * zH R' t (Nh + 1) / R.ℓ ^ 2 ≤ 9 / 8 := by
      rw [div_le_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_right hS hZp.le
      rw [show 9 / 8 * R.ℓ ^ 2 * (zH R' t (Nh + 1))⁻¹ * zH R' t (Nh + 1) = 9 / 8 * R.ℓ ^ 2 by
        field_simp] at this
      linarith
    calc cBn * (Q1 2 * (cW * g * histS R' Nh t ^ 2 * B0)) * (zH R' t (Nh + 1) / R.ℓ ^ 2)
        = (cBn * Q1 2 * cW * g) * B0 * (histS R' Nh t ^ 2 * zH R' t (Nh + 1) / R.ℓ ^ 2) := by ring
      _ ≤ (cBn * Q1 2 * cW * g) * (2 * β) * (9 / 8) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hBB hK0) h1
            (div_nonneg (mul_nonneg (sq_nonneg _) hZp.le) (sq_nonneg _))
            (mul_nonneg hK0 (by linarith [norm_nonneg (Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x))]))
      _ = 9 / 4 * (cBn * Q1 2 * cW) * g * β := by ring
  simp only [hP0, mul_one, norm_one]
  refine ⟨?_, by rw [he]; exact hk2⟩
  have hb3 := hb2.trans (add_le_add (add_le_add le_rfl hwS) hk1)
  have hβ0 : 0 ≤ β := norm_nonneg _
  have := mul_le_mul_of_nonneg_right hsm hβ0
  calc _ ≤ _ := hb3
    _ = (Cf * (R.ℓ ^ 2 / 8 + R.ℓ ^ 4 / 128) + 9 / 4 * (cBn * Q1 2 * cW) + KK) * g * β := by ring
    _ ≤ 1 / 2 * β := this

/-- **`PairZeroRemW` with item (a) from `P₀ = 1`** (copy of `pairZeroRemW_of_A` without the
smallness of `P₀ - 1`). -/
theorem pairZeroRemW_of_A1 {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ} (hm0 : 0 < m) (b μ₀ : ℝ)
    (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) (hρ0 : 0 ≤ R.ρ) (hρ1 : R.ρ < 1)
    {Kt KA e1 e2 : ℝ}
    (hP1 : ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh → zP0 R Nh m b μ₀ x = 1)
    (hK : ‖(m : ℂ) * ((lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z *
        zmRaw (R.withMsq m) (Nh + 1)
          (lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).ζ) - 1‖ ≤
      Kt * m * (L : ℝ) ^ (2 * N))
    (hmT : Kt * m * (L : ℝ) ^ (2 * N) ≤ 1 / 2) (hmA : 8 * KA * m * (L : ℝ) ^ (2 * N) ≤ 1)
    (hA : LastOneRem R Nh m b μ₀ KA) (hAB : PairZeroRemAB R Nh m b μ₀ lam oR e1 e2) :
    PairZeroRemW R Nh m b μ₀ lam oR e1 e2 := by
  intro x hx h1 hj
  have hP : zP0 R Nh m b μ₀ x ≠ 0 := by rw [hP1 x hx h1 hj]; exact one_ne_zero
  obtain ⟨kb, ke⟩ := hA x hx h1 hj
  obtain ⟨kc, kd⟩ := hAB x hx h1 hj
  refine ⟨hP, kb, kc, kd, ?_⟩
  set Z := (lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z
  have hZ : Z ≠ 0 := lastOut_Z_ne (R.withMsq m) hρ0 hρ1 Nh _
  have hc := zCc_ge R hNh hm0 b μ₀ hK hmT hZ
  set β := ‖Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖
  set p := ‖zP0 R Nh m b μ₀ x‖
  set Λ := (L : ℝ) ^ (2 * N)
  have hZn : 0 < ‖Z‖ := norm_pos_iff.2 hZ
  have hΛ : 0 < Λ := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) _
  have hBP : 0 ≤ β * p := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hKA : KA * (β * p / ‖Z‖) ≤ 1 / 4 * (1 / (2 * m * ‖Z‖ * Λ)) * (β * p) := by
    have hq : 0 ≤ β * p / ‖Z‖ := div_nonneg hBP hZn.le
    have e : 1 / 4 * (1 / (2 * m * ‖Z‖ * Λ)) * (β * p) = 1 / (8 * m * Λ) * (β * p / ‖Z‖) := by
      field_simp; ring
    rw [e]
    refine mul_le_mul_of_nonneg_right ?_ hq
    rw [le_div_iff₀ (by positivity)]
    linarith
  calc ‖ε (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a‖ ≤ KA * β * p / ‖Z‖ := ke
    _ = KA * (β * p / ‖Z‖) := by ring
    _ ≤ 1 / 4 * (1 / (2 * m * ‖Z‖ * Λ)) * (β * p) := hKA
    _ ≤ 1 / 4 * ‖zCc R Nh m b μ₀‖ * (β * p) := by gcongr
    _ = 1 / 4 * (‖zCc R Nh m b μ₀‖ * β * p) := by ring

end Traj

end

end Spin2
