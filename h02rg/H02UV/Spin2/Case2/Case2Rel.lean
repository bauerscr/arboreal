import Spin2.Case2.Case2Thm
import PtCorr2.Obs.ProdBd2Hist

/-!
# `Case2Rel` under the master constants; `thm:multiscale` (Case 2) conditional only on `RGInput`

* `C2Ctx.tadInc2_le`: along a history with the bulk context `C2Ctx` (constant `c ≥ ℓ⁴`),
  `|tadInc2 k j| ≤ c(2/L)^{j−k}ǧ_k` (`tadInc2 = g_k(4δ_j rowS_{C_k} − 𝔩_{C_k,C_j})`,
  `|g_k| ≤ (8/7)ǧ_k|Z_{k+1}|²`, the Gram scales of `C_k`, `C_j`, `|Z_{k+1}|/|Z_{j+1}| ≤ (8/7)^{j−k}`);
* `c2RelReq`, `c2RelReq_ev`: the requirement on `ε` (that of `thm_multiscale_case2C`, those of the
  observable recursion, `c_Rε ≤ ε_P(L)`, and the smallness conditions for the constants
  `c_g = (B'+1)/c_R`, `c_δ = c2dF`);
* **`thm_multiscale_case2D`**: one set of constants with `FlowC2Concl`, `ε ≤ 1`, `BetaConcl`,
  `LamConcl`, `LoopConcl` and
  - `RelConcl2`: `Case2Rel R P V N_h m b μ₀ (c_δc_R²)` along every admissible trajectory
    (`N_h = N − 2`) for every Case-(2) vertex `V` with `γ_a = 0`;
  - `MultiConcl2D`: `thm:multiscale` for `λ̂ = μ_a/μ_{a,0}` (`γ_a = 0`, `μ_a ≠ 0`) conditional
    only on `RGInput`.
-/

set_option linter.unusedSectionVars false

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Filter Topology Step2.D2

variable {L N : ℕ} [NeZero L]

/-- Algebra of `tadInc2_le` (first term). -/
theorem tad_eAB (ℓ : ℝ) {zk zj Q : ℝ} (hzk : 0 < zk) (hzj : 0 < zj) (hQ : Q > 0) (P : ℝ) :
    4 * (ℓ ^ 2 / (16 * zj) / (2 * Q ^ 2)) * (18 * P ^ 2 * (ℓ ^ 2 / (16 * zk))) =
      9 / 64 * ℓ ^ 4 / (zk * zj) * (P ^ 2 / Q ^ 2) := by
  field_simp
  ring

/-- Algebra of `tadInc2_le` (second term). -/
theorem tad_eX (ℓ : ℝ) {zk zj : ℝ} (hzk : 0 < zk) (hzj : 0 < zj) (r : ℝ) :
    36 * (ℓ ^ 2 / (16 * zk)) * (ℓ ^ 2 / (16 * zj)) * r = 9 / 64 * ℓ ^ 4 / (zk * zj) * r := by
  field_simp
  ring

/-- The final real inequality of `tadInc2_le`. -/
theorem tad_real {g zk zj ℓ4 c u w q : ℝ} (hg : 0 ≤ g) (hzk : 0 < zk) (hzj : 0 < zj)
    (hℓ4 : 0 ≤ ℓ4) (hℓc : ℓ4 ≤ c) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hz : zk ≤ w * zj)
    (hwq : w * u ≤ q) (hw0 : 0 ≤ w) :
    8 / 7 * g * zk ^ 2 * (9 / 64 * ℓ4 / (zk * zj) * u ^ 2 + 9 / 64 * ℓ4 / (zk * zj) * u) ≤
      c * q * g := by
  have e : 8 / 7 * g * zk ^ 2 * (9 / 64 * ℓ4 / (zk * zj) * u ^ 2 + 9 / 64 * ℓ4 / (zk * zj) * u) =
      9 / 56 * g * ℓ4 * (zk / zj) * (u ^ 2 + u) := by
    field_simp
    ring
  have h1 : zk / zj ≤ w := by rw [div_le_iff₀ hzj]; linarith
  have h2 : u ^ 2 + u ≤ 2 * u := by nlinarith
  have hc0 : 0 ≤ c := hℓ4.trans hℓc
  have hq0 : 0 ≤ q := (mul_nonneg hw0 hu0).trans hwq
  rw [e]
  calc 9 / 56 * g * ℓ4 * (zk / zj) * (u ^ 2 + u) ≤ 9 / 56 * g * ℓ4 * w * (2 * u) := by
        gcongr
    _ = 9 / 28 * g * ℓ4 * (w * u) := by ring
    _ ≤ 9 / 28 * g * c * q := by gcongr
    _ ≤ c * q * g := by
        have : 0 ≤ c * q * g := by positivity
        nlinarith

namespace C2Ctx

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {Nh : ℕ} {t : Hist.Seq (Xs R)}
  {cmu' cz' cd c : ℝ} (X : C2Ctx R Nh t cmu' cz' cd c)
include X

/-- **The Case-(2) tadpole increments**: `|tadInc2 k j| ≤ c(2/L)^{j−k}ǧ_k` (`k < j < N_h`). -/
theorem tadInc2_le (P : Obs2.ObsPts 2 L N) (o₀ : Obs2.ObsSt .two L N) (h₀ : o₀.IsObs)
    {k j : ℕ} (hkj : k < j) (hj : j < Nh) :
    ‖Obs2.tadInc2 P (Obs2.histCovO R t) (Obs2.histVO2 R P o₀ t) k j‖ ≤
      c * (2 / (L : ℝ)) ^ (j - k) * (t k).1 := by
  have hL0 := X.L_pos
  have hL7 := X.L7
  have hℓ : 0 < R.ℓ := Fact.out
  have HB := Obs2.bulk2_hist R P o₀ t X.hV h₀
  rw [HB.tadInc2_eq P hkj hj, Obs2.kapH_g]
  have hg0 : 0 ≤ (t k).1 := (X.hg k (by omega)).1.le
  have hgk : ‖Obs2.gH R t k‖ ≤ 8 / 7 * (t k).1 * zH R t (k + 1) ^ 2 := by
    have h := hist_G_w R X.hρ0 X.hρ8 t k hg0
    have e : (PtCorr2.kapH R t k).g = Obs2.gH R t k := rfl
    rw [e, div_le_iff₀ (pow_pos (X.zpos (k + 1)) 2)] at h
    exact h
  have hzk := X.zpos (k + 1)
  have hzj := X.zpos (j + 1)
  have h1 := X.dl_le hj
  have h2 := X.rowS_le (hkj.trans hj) P.a
  have h3 := X.lfunX_le (hkj.trans hj) hj P.a
  have hz := zH_ratio_down R X.hρ0 X.hρ8 t (show k + 1 ≤ j + 1 by omega)
  rw [show j + 1 - (k + 1) = j - k by omega] at hz
  set u : ℝ := (L : ℝ)⁻¹ ^ (j - k) with hu
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by linarith))
  have hr := pow_ratio_L hL0 hkj.le
  have hr2 := pow_ratio_L2 hL0 hkj.le
  set A := R.ℓ ^ 2 / (16 * zH R t (j + 1)) / (2 * ((L : ℝ) ^ (j + 1)) ^ 2)
  set Bk := 18 * ((L : ℝ) ^ (k + 1)) ^ 2 * (R.ℓ ^ 2 / (16 * zH R t (k + 1)))
  set Xk := 36 * (R.ℓ ^ 2 / (16 * zH R t (k + 1))) * (R.ℓ ^ 2 / (16 * zH R t (j + 1))) *
    ((L : ℝ) ^ (k + 1) / (L : ℝ) ^ (j + 1))
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ Bk := by positivity
  have hX0 : 0 ≤ Xk := by positivity
  have hin : ‖2 * ((2 : ℕ) : ℂ) * Obs2.dlH R t j * Obs2.rowS (Obs2.histCovO R t k) P.a -
      Obs2.lfunX (Obs2.histCovO R t k) (Obs2.histCovO R t j) P.a‖ ≤ 4 * A * Bk + Xk := by
    refine (norm_sub_le _ _).trans (add_le_add ?_ h3)
    rw [norm_mul, norm_mul]
    have e4 : ‖(2 : ℂ) * ((2 : ℕ) : ℂ)‖ = 4 := by norm_num
    rw [e4]
    have h12 := mul_le_mul h1 h2 (norm_nonneg _) hA0
    nlinarith
  have hLn : (L : ℝ) ^ (j + 1) > 0 := by positivity
  have eAB : 4 * A * Bk = 9 / 64 * R.ℓ ^ 4 / (zH R t (k + 1) * zH R t (j + 1)) * u ^ 2 := by
    rw [tad_eAB R.ℓ hzk hzj hLn, ← div_pow, hr]
  have eX : Xk = 9 / 64 * R.ℓ ^ 4 / (zH R t (k + 1) * zH R t (j + 1)) * u := by
    simp only [Xk]
    rw [tad_eX R.ℓ hzk hzj, hr]
  have hq : (8 / 7 : ℝ) ^ (j - k) * u ≤ (2 / (L : ℝ)) ^ (j - k) := by
    rw [hu, ← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    rw [← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right (by norm_num) hL0.le
  have hfin : 8 / 7 * (t k).1 * zH R t (k + 1) ^ 2 * (4 * A * Bk + Xk) ≤
      c * (2 / (L : ℝ)) ^ (j - k) * (t k).1 := by
    rw [eAB, eX]
    exact tad_real hg0 hzk hzj (by positivity) X.hc4 hu0 hu1 hz hq (by positivity)
  calc ‖Obs2.gH R t k * (2 * ((2 : ℕ) : ℂ) * Obs2.dlH R t j * Obs2.rowS (Obs2.histCovO R t k) P.a -
        Obs2.lfunX (Obs2.histCovO R t k) (Obs2.histCovO R t j) P.a)‖
      ≤ 8 / 7 * (t k).1 * zH R t (k + 1) ^ 2 * (4 * A * Bk + Xk) := by
        rw [norm_mul]; exact mul_le_mul hgk hin (norm_nonneg _) (by positivity)
    _ ≤ _ := hfin

end C2Ctx

/-! ### The constants and the requirement on `ε` -/

/-- `B'` of `Case2Loop` under the master constants (`c = c_R`, `c' = c_x`). -/
def c2Bp (Cq Cl cS : ℝ) (L : ℕ) (K cS2 c c' : ℝ) : ℝ :=
  case2BK (betaL L) (bubB L (ceff L c) K cS2) (nuB L Cq Cl cS c' c (ceff L c))
    (9 / 64 * ceff L c ^ 2) (7 * ceff L c) 2

/-- The rescaled bulk constant `c_g = (B' + 1)/c_R` of the Case-(2) recursion (`B' ≥ 0`,
`c_R ≥ 2` along the trajectories). -/
def c2gF (B' c : ℝ) : ℝ := (max B' 0 + 1) / max c 2

/-- The relative error constant `c_δ` of the Case-(2) recursion. -/
def c2dF (L : ℕ) (Cp B' C₁w Bk c : ℝ) : ℝ :=
  3 * (16 * (8 * (csN 2 : ℝ)) * (3 * C₁w + 1) * Bk + 3 * prodCP2 L Cp * (3 * C₁w + 1) +
    4 * ceff L (max c 2) * c2gF B' c * (1 + c2gF B' c))

/-- The requirement on `ε` of `thm_multiscale_case2D` (`c = c_R`, `c' = c_x`). -/
def c2RelReq (Cq Cl cS C₀ η Kw : ℝ) (Lo : ℕ) (Cpf εpf : ℕ → ℝ) (L : ℕ) (A c c' ε : ℝ) : Prop :=
  ∀ [NeZero L], Lo ≤ L → obsAReq C₀ η Lo L A →
    ∃ ζbar K cS2 : ℝ, 0 < ζbar ∧ 0 ≤ K ∧ 0 ≤ cS2 ∧ LcProp L ζbar K cS2 ∧
      2 * ceff L c * ε ≤ ζbar ∧ c * ε ≤ 1 ∧ 8 * c' * ε ≤ 1 ∧ betaL L * ε ≤ 1 / 2 ∧
      c2Bp Cq Cl cS L K cS2 c c' * ε ≤ 1 / 8 ∧
      (max (c2Bp Cq Cl cS L K cS2 c c') 0 + 1) * ε ≤ 1 / 7 ∧
      4 * ceff L (max c 2) * (max (c2Bp Cq Cl cS L K cS2 c c') 0 + 1) * ε ≤ 1 / 2 ∧
      c * ε ≤ εpf L ∧
    ∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧ KObsBounds L A C₀ η ε₀ C₁ ∧
      C₁ * (2 + 2 * (8 * c') + 64 * kB (kθ0 L A C₀ η) C₁ (8 * c')) * (c * ε) ≤ 1 / 72 ∧
      c * ε ≤ ε₀ ∧ (8 * c' + 64 * kB (kθ0 L A C₀ η) C₁ (8 * c')) * (c * ε) ≤ ε₀ ∧
    ∃ C₁w ε₁ : ℝ, 0 ≤ C₁w ∧ 0 < ε₁ ∧ WObsBounds L Kw C₁w ε₁ ∧ C₁w * (c * ε) ≤ 1 / 12 ∧
      c * ε ≤ ε₁ ∧
      c2dF L (Cpf L) (c2Bp Cq Cl cS L K cS2 c c') C₁w (kB (kθ0 L A C₀ η) C₁ (8 * c')) c *
        c ^ 2 * (4 / betaL L) * ε ≤ 1 / 8

theorem c2RelReq_ev (Cq Cl cS : ℝ) {C₀ η Kw : ℝ} {L₀ Lo : ℕ} (Cpf εpf : ℕ → ℝ)
    (hw : ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ C₁ ε₁ : ℝ, 0 ≤ C₁ ∧ 0 < ε₁ ∧ WObsBounds L Kw C₁ ε₁)
    (hLo : L₀ ≤ Lo) (h7 : 7 ≤ Lo) (hεp : ∀ (L : ℕ) [NeZero L], Lo ≤ L → 0 < εpf L)
    (L : ℕ) (A c c' : ℝ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), c2RelReq Cq Cl cS C₀ η Kw Lo Cpf εpf L A c c' ε := by
  by_cases hL : L ≠ 0 ∧ Lo ≤ L
  · haveI : NeZero L := ⟨hL.1⟩
    by_cases hA : obsAReq C₀ η Lo L A
    · obtain ⟨⟨ε₀, C₁, hε₀, hC₁, hKB⟩, -⟩ := hA hL.2
      obtain ⟨C₁w, ε₁, hC₁w, hε₁, hWB⟩ := hw L (hLo.trans hL.2)
      obtain ⟨ζbar, hζ, K, cS2, hK, hcS2, hLc⟩ := lcProp_of (L := L) (h7.trans hL.2)
      set B' := c2Bp Cq Cl cS L K cS2 c c'
      set Bk := kB (kθ0 L A C₀ η) C₁ (8 * c')
      filter_upwards [ev_lin (2 * ceff L c) hζ, ev_lin c one_pos, ev_lin (8 * c') one_pos,
        ev_lin (betaL L) (by norm_num : (0 : ℝ) < 1 / 2), ev_lin B' (by norm_num : (0 : ℝ) < 1 / 8),
        ev_lin (max B' 0 + 1) (by norm_num : (0 : ℝ) < 1 / 7),
        ev_lin (4 * ceff L (max c 2) * (max B' 0 + 1)) (by norm_num : (0 : ℝ) < 1 / 2),
        ev_lin c (hεp L hL.2),
        ev_lin (C₁ * (2 + 2 * (8 * c') + 64 * Bk) * c) (by norm_num : (0 : ℝ) < 1 / 72),
        ev_lin c hε₀, ev_lin ((8 * c' + 64 * Bk) * c) hε₀,
        ev_lin (C₁w * c) (by norm_num : (0 : ℝ) < 1 / 12), ev_lin c hε₁,
        ev_lin (c2dF L (Cpf L) B' C₁w Bk c * c ^ 2 * (4 / betaL L))
          (by norm_num : (0 : ℝ) < 1 / 8)]
        with ε h1 h2 h3 h4 h5 h6 h7' h8 h9 h10 h11 h12 h13 h14
      intro _ _ _
      exact ⟨ζbar, K, cS2, hζ, hK, hcS2, hLc, h1, h2, h3, h4, h5, h6, h7', h8, ε₀, C₁, hε₀, hC₁,
        hKB, by rw [← mul_assoc]; exact h9, h10, by rw [← mul_assoc]; exact h11, C₁w, ε₁, hC₁w,
        hε₁, hWB, by rw [← mul_assoc]; exact h12, h13, h14⟩
    · exact Eventually.of_forall fun _ _ _ hA' => absurd (fun (_ : NeZero L) => hA') hA
  · exact Eventually.of_forall fun _ inst hLL _ => absurd ⟨inst.out, hLL⟩ hL

/-! ### The conclusions -/

/-- **`Case2Rel` along every admissible trajectory** (`N_h = N − 2`), for every point
configuration `P` and every Case-(2) vertex `V` with `γ_a = 0`, `μ_a ≠ 0`. -/
def RelConcl2 (L : ℕ) [NeZero L] (ℓ A ρ κ cm cT ε cδ : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
  ∀ m ∈ mRange L N, ∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
  ∀ (P : Obs2.ObsPts 2 L N) (V : Obs2.OCoup .two), Obs2.OCoup2.ga V = 0 →
    Obs2.OCoup2.mua V ≠ 0 → Case2Rel R P V Nh m b μ₀ cδ

/-- **`thm:multiscale` for `λ̂ = μ_a/μ_{a,0}`** (`γ_a = 0`), conditional on `RGInput` only. -/
def MultiConcl2D (L : ℕ) [NeZero L] (ℓ A ρ κ cg cm cT ε Ke KZ KG B B' cq cδ : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
  ∀ m ∈ mRange L N, ∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
  ∀ (P : Obs2.ObsPts 2 L N) (V : Obs2.OCoup .two) (KP : ℝ), 0 ≤ KP →
    Obs2.OCoup2.ga V = 0 → Obs2.OCoup2.mua V ≠ 0 →
    RGInput R Nh m b μ₀ (lamHat2 R P V m b μ₀) KP →
  ∀ x : Lam 2 L N, x ≠ 0 → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∃ jp : ℕ, (jp : ℤ) = jPhys L N (eucl x / (L : ℝ) ^ N) ∧
      jp ≤ Obs.coal L (0 : Lam 2 L N) x ∧ Obs.coal L (0 : Lam 2 L N) x ≤ jp + 1 ∧
      |Pconn L N (1 / b) x - thetaSq R m b μ₀ jp| ≤
        multK L cg Ke KZ KG (max (lamRelK (betaL L) cg B B' cq cδ (eRange (betaL L) Ke 1) 4) 0)
          KP * thetaSq R m b μ₀ jp / betaJ R m b μ₀ jp

set_option maxHeartbeats 8000000 in
/-- **Expected result `thm:multiscale` for `λ̂ = μ_a/μ_{a,0}`, `Case2Rel` discharged**: one set of
constants with `FlowC2Concl`, `ε ≤ 1`, `BetaConcl`, `LamConcl`, `LoopConcl`, `RelConcl2`
(`Case2Rel` along every admissible trajectory, `γ_a = 0`) and `MultiConcl2D` (conditional on
`RGInput` only). -/
theorem thm_multiscale_case2D : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ κ cg cm cT ε Ke Cf Cb KZ KG B₁ B₂ B₃ cq B' cδ : ℝ,
      FlowC2Concl L ℓ A ρ κ cg cm cT ε Ke Cf Cb ∧ ε ≤ 1 ∧
      BetaConcl L ℓ A ρ κ cg cm cT ε Ke Cb ∧ LamConcl L ℓ A ρ κ cg cm cT ε Ke ∧
      LoopConcl L ℓ A ρ κ cm cT ε B₁ B₂ B₃ cq B' ∧ 0 ≤ cδ ∧
      RelConcl2 L ℓ A ρ κ cm cT ε cδ ∧
      MultiConcl2D L ℓ A ρ κ cg cm cT ε Ke KZ KG (B₁ + B₂ + B₃) B' cq cδ := by
  obtain ⟨Cq, hCq, Cl, hCl, cS, hcS, hnu⟩ := nu_sharp
  obtain ⟨Cpf, εpf, L₀p, hCpf, hPf⟩ := prod_raw_step
  obtain ⟨C₀o, ηo, L₀k, hC₀o, hηo, hk⟩ := kobs_bounds
  obtain ⟨Kw, L₀w, hKw, hw⟩ := wobs_bounds
  obtain ⟨Lo, hLod⟩ : ∃ Lo : ℕ, Lo = max (max L₀k L₀w)
      (max (⌈144 * C₀o + 12 * Kw⌉₊ + 8) (max L₀p ⌈prodLb⌉₊)) := ⟨_, rfl⟩
  have hLk : L₀k ≤ Lo := hLod ▸ le_trans (le_max_left _ _) (le_max_left _ _)
  have hLw' : L₀w ≤ Lo := hLod ▸ le_trans (le_max_right _ _) (le_max_left _ _)
  have hLp : L₀p ≤ Lo := hLod ▸ le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))
  have hLb : prodLb ≤ (Lo : ℝ) := by
    have h1 : ⌈prodLb⌉₊ ≤ Lo := hLod ▸ le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))
    exact (Nat.le_ceil _).trans (by exact_mod_cast h1)
  have hLc8 : ⌈144 * C₀o + 12 * Kw⌉₊ + 8 ≤ Lo :=
    hLod ▸ le_trans (le_max_left _ _) (le_max_right _ _)
  have hLc : 144 * C₀o + 12 * Kw + 8 ≤ (Lo : ℝ) := by
    have h2 := Nat.le_ceil (144 * C₀o + 12 * Kw)
    have h3 : ((⌈144 * C₀o + 12 * Kw⌉₊ + 8 : ℕ) : ℝ) ≤ Lo := by exact_mod_cast hLc8
    push_cast at h3
    linarith
  have h7 : 7 ≤ Lo := by omega
  obtain ⟨L₀, hL₀⟩ := thm_flow_master_all (fun L A => 2 ≤ A ∧ obsAReq C₀o ηo Lo L A)
    (fun L => by
      obtain ⟨A₀, hA₀⟩ := obsAReq_ev hC₀o hηo hk hLk (by linarith) L
      exact ⟨max 2 A₀, fun A hA => ⟨le_trans (le_max_left _ _) hA,
        hA₀ A (le_trans (le_max_right _ _) hA)⟩⟩)
    (c2RelReq Cq Cl cS C₀o ηo Kw Lo Cpf εpf)
    (c2RelReq_ev Cq Cl cS Cpf εpf hw hLw' h7 fun L _ hL => (hPf L (hLp.trans hL)).1)
  refine ⟨max L₀ (max Lo (max 49 ⌈pauliL0 2⌉₊)), fun L _ hL => ?_⟩
  obtain ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, Cf, Cb, KZ, KG, hC2, hε1, -, -, hSp, hMag, hB,
    ⟨hA2, hAx⟩, -, C₀x, ηx, εsx, CKx, C₂x, CDx, Cqx, Clx, cSx, hSBx, hEx, hXm⟩ :=
    hL₀ L (le_trans (le_max_left _ _) hL)
  have hLo : Lo ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
  have hLr : (Lo : ℝ) ≤ L := by exact_mod_cast hLo
  have hL49 : 49 ≤ L := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))) hL
  have hLpl : pauliL0 2 ≤ L := (Nat.le_ceil _).trans (by
    exact_mod_cast le_trans (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))) hL)
  have hL8 : 2 ^ (2 + 3) + 8 * 2 < L := by norm_num; omega
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (by omega : 2 ≤ L)
  have hL0 : (0 : ℝ) < L := by linarith
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8, -, hCN⟩ := id hC2
  let R₀ : RGPar 2 L 1 := ⟨Pc, 0, ℓ, A, 0, ρ⟩
  obtain ⟨-, hθ⟩ := hAx hLo
  obtain ⟨ζbar, K, cS2, -, hK, hcS2, hLc', hζε, hcε, hc'ε, hβε, hsm, hgε7, hBτε, hεp,
    ε₀, C₁k, hε₀, hC₁k, hKB, hsmk, hεε, hεk, C₁w, ε₁, hC₁w, hε₁, hWB, hC₁ε, hε₁', hcδε⟩ :=
    hEx R₀ rfl hLo hAx
  obtain ⟨-, hPB⟩ := hPf L (hLp.trans hLo)
  set c := cR R₀ ((L : ℝ) ^ 2) cm C₂x with hc
  set ce := ceff L c with hce
  set B' := c2Bp Cq Cl cS L K cS2 c (cx κ cT) with hB'
  have hNu := hnu L hL8 hLpl
  have hβ2 := betaL_ge (by omega : 8 ≤ L)
  have hβ0 : 0 ≤ betaL L := by linarith
  have hθ0 : 0 ≤ kθ0 L A C₀o ηo := by
    unfold kθ0
    exact mul_nonneg hC₀o (add_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _))
  have hLwk : Kw / L ≤ 1 / 12 := by
    rw [div_le_iff₀ hL0]; linarith
  -- the loop conclusion (as in `thm_multiscale_case2C`)
  have hLoop : LoopConcl L ℓ A ρ κ cm cT ε (bubB L ce K cS2) (nuB L Cq Cl cS (cx κ cT) c ce)
      (9 / 64 * ce ^ 2) (7 * ce) B' := by
    intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm P V
    set R' := R.withMsq m with hR'
    obtain ⟨H, hm1, F1⟩ := hXm N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm
    obtain ⟨hV, hVL⟩ := (hCN N R hP hi0 hRℓ hRA hRρ hN Nh hNh).2.2.2.2.2.2.2.2.2 m hm
    have ht := admissible_InDh_rg R' F1 hadm Nh le_rfl
    have hRA' : R'.A = A := hRA
    have hρ0' : 0 ≤ R'.ρ := by rw [show R'.ρ = ρ from hRρ]; exact hρpos.le
    have hρ8' : R'.ρ ≤ 1 / 8 := by rw [show R'.ρ = ρ from hRρ]; exact hρ8
    have hcR : cR R' ((L : ℝ) ^ 2) cm C₂x = c := cR_congr (show R.ℓ = ℓ from hRℓ) _ _ _
    have hSB' : StepBounds L R'.A C₀x ηx εsx CKx C₂x CDx Cqx Clx cSx := by rw [hRA']; exact hSBx
    have hmsq : R'.msq ∈ mRange L N := hm
    have X := c2ctx_master R' hNh hL49 hSB' H hm1 hV hVL hρ0' hρ8' hmsq hβε ht
    rw [hcR] at X
    set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
    have hgε : ∀ j ≤ Nh, (t j).1 ≤ ε := fun j hj => (ht.1 j hj).2.1
    have hP' : R'.P = Pc := hP
    have hce0 : 0 ≤ ce := X.c_nonneg
    have hbulk : Case2Bulk R P Nh m b μ₀ (bubB L ce K cS2) (nuB L Cq Cl cS (cx κ cT) c ce)
        (9 / 64 * ce ^ 2) (7 * ce) := by
      refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
      · exact X.bubble_le hP' hLc' hK hcS2 hm.1 hm.2 hgε hζε hk P.a
      · have h := X.nuflow_le hCq hCl hcS hNu hSB' hm1 hβ0 (by norm_num) H ht
          (by rw [hRA']; exact hA2) (by rw [hcR]; exact hcε) hc'ε hk P.a
        rw [hcR] at h
        exact h
      · exact X.drift_le hk P.a
      · exact X.q_le hk P.a
    have hB1 : 0 ≤ bubB L ce K cS2 := by
      unfold bubB; have := bubE_nonneg; have := bubF_nonneg (L := L) hce0 hK hcS2
      have : 0 ≤ betaL L / 3 := by linarith
      positivity
    have hB2 : 0 ≤ nuB L Cq Cl cS (cx κ cT) c ce := by
      have hQ1 : 1 ≤ Q1 2 := one_le_Q1 (by norm_num)
      have hN0 : 0 ≤ cNear 2 L := Nat.cast_nonneg _
      have hcx : 0 ≤ cx κ cT := H.hcx
      have hQc : 0 ≤ cNear 2 L * Q1 2 ^ 2 + Q1 2 :=
        add_nonneg (mul_nonneg hN0 (sq_nonneg _)) (by linarith)
      unfold nuB
      have : 0 ≤ 16 * (L : ℝ) ^ 2 * Cq * cS * Cl * cx κ cT :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hCq) (by linarith)) hCl) hcx
      have : 0 ≤ 2 * Cq * Cl * (L : ℝ) ^ 2 * (cNear 2 L * Q1 2 ^ 2 + Q1 2) * c ^ 2 :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCq) hCl)
          (sq_nonneg _)) hQc) (sq_nonneg _)
      linarith
    have hB3 : 0 ≤ 9 / 64 * ce ^ 2 := by positivity
    refine ⟨by linarith, hbulk,
      case2Loop_of (fun i hi => hV i hi) hB1 hB2 hB3 ?_ hβ0 ?_ ?_ ?_ ?_ hbulk⟩
    · positivity
    · exact fun k hk => ⟨(X.hg k hk.le).1.le, (X.hg k hk.le).2⟩
    · exact fun k hk => ⟨zA_nonneg L hm.1.le k, zA_le_two (by linarith) (le_trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
          (pow_le_pow_right₀ (by linarith) (by omega)) 2) hm.1.le) X.hm)⟩
    · exact fun k hk => X.hg2 k hk
    · intro k hk
      have h1 := hgε k hk.le
      have h0 := (X.hg k hk.le).1.le
      have hB0 : 0 ≤ B' := by
        show 0 ≤ case2BK (betaL L) (bubB L ce K cS2) (nuB L Cq Cl cS (cx κ cT) c ce)
          (9 / 64 * ce ^ 2) (7 * ce) 2
        unfold case2BK
        have : 0 ≤ 7 * ce * (2 + 1) := by positivity
        have : 0 ≤ betaL L / 3 := by linarith
        linarith
      exact (mul_le_mul_of_nonneg_left h1 hB0).trans hsm
  -- nonnegativity of the constants
  have hcx : 0 ≤ cx κ cT := by
    obtain ⟨-, -, -, -, hκ0, hκ1, -, -, hcT, -⟩ := id hC2
    unfold cx; exact div_nonneg (by linarith) (by linarith)
  set Bk := kB (kθ0 L A C₀o ηo) C₁k (8 * cx κ cT) with hBk
  have hBk0 : 0 ≤ Bk := by
    have h1 := mul_nonneg hθ0 (by positivity : (0 : ℝ) ≤ 8 * cx κ cT)
    have h2 := mul_nonneg hC₁k
      (by positivity : (0 : ℝ) ≤ 8 + 2 * (8 * cx κ cT) + (8 * cx κ cT) ^ 2)
    show 0 ≤ kθ0 L A C₀o ηo * (8 * cx κ cT) + C₁k * (8 + 2 * (8 * cx κ cT) + (8 * cx κ cT) ^ 2)
    linarith
  set cgb := c2gF B' c with hcgb
  set cP := prodCP2 L (Cpf L) with hcP
  set cδ := c2dF L (Cpf L) B' C₁w Bk c with hcδd
  have hcm2 : (2 : ℝ) ≤ max c 2 := le_max_right _ _
  have hB0' : (0 : ℝ) ≤ max B' 0 := le_max_right _ _
  have hcgb0 : 0 ≤ cgb := div_nonneg (by linarith) (by linarith)
  have hce2 : 0 ≤ ceff L (max c 2) := by unfold ceff; linarith
  have hcP0 : 0 ≤ cP := by
    show 0 ≤ (cbnC : ℝ) * Cpf L * (6 / 5 * L + 3072 * Obs2.locK 2 ^ 2)
    have := hCpf L; positivity
  set Xc := 16 * (8 * (csN 2 : ℝ)) * (3 * C₁w + 1) * Bk + 3 * cP * (3 * C₁w + 1) +
    4 * ceff L (max c 2) * cgb * (1 + cgb) with hXc
  have hcδX : cδ = 3 * Xc := rfl
  have hX0 : 0 ≤ Xc := by positivity
  have hcδ0 : 0 ≤ cδ := by rw [hcδX]; positivity
  have hq4 : (2 : ℝ) / L ≤ 1 / 4 := by
    rw [div_le_div_iff₀ hL0 (by norm_num)]
    have : (49 : ℝ) ≤ L := by exact_mod_cast hL49
    linarith
  have hRel : RelConcl2 L ℓ A ρ κ cm cT ε (cδ * c ^ 2) := by
    intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm P V hga hmu
    rcases Nat.eq_zero_or_pos Nh with h0 | hNh0
    · intro k hk; omega
    set R' := R.withMsq m with hR'
    obtain ⟨H, hm1, F1⟩ := hXm N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm
    obtain ⟨hV, hVL⟩ := (hCN N R hP hi0 hRℓ hRA hRρ hN Nh hNh).2.2.2.2.2.2.2.2.2 m hm
    have ht := admissible_InDh_rg R' F1 hadm Nh le_rfl
    have hRA' : R'.A = A := hRA
    have hρ0' : 0 ≤ R'.ρ := by rw [show R'.ρ = ρ from hRρ]; exact hρpos.le
    have hρ8' : R'.ρ ≤ 1 / 8 := by rw [show R'.ρ = ρ from hRρ]; exact hρ8
    have hcR : cR R' ((L : ℝ) ^ 2) cm C₂x = c := cR_congr (show R.ℓ = ℓ from hRℓ) _ _ _
    have hSB' : StepBounds L R'.A C₀x ηx εsx CKx C₂x CDx Cqx Clx cSx := by rw [hRA']; exact hSBx
    have hmsq : R'.msq ∈ mRange L N := hm
    have X := c2ctx_master R' hNh hL49 hSB' H hm1 hV hVL hρ0' hρ8' hmsq hβε ht
    rw [hcR] at X
    have hc2 : 2 ≤ c := hcR ▸ two_le_cR R' H.hcmu H.hC₂
    have hmc : max c 2 = c := max_eq_left hc2
    have hce0 : 0 ≤ ce := X.c_nonneg
    obtain ⟨hB0, -, q, -, -, hl⟩ := hLoop N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm P V
    have hB'0 : 0 ≤ B' := by
      show 0 ≤ case2BK (betaL L) (bubB L ce K cS2) (nuB L Cq Cl cS (cx κ cT) c ce)
        (9 / 64 * ce ^ 2) (7 * ce) 2
      unfold case2BK
      have : 0 ≤ 7 * ce * (2 + 1) := by positivity
      have : 0 ≤ betaL L / 3 := by linarith
      linarith
    have hmB : max B' 0 = B' := max_eq_left hB'0
    have hcgc : cgb * c = B' + 1 := by
      rw [hcgb, c2gF, hmB, hmc]; field_simp
    set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
    have hPr := prodBd2_hist R' hPB (hCpf L) hSB' hV hm1 hβ0 (by norm_num : (1 / 2 : ℝ) ≤ 1) H
      hρ0' hρ8' P V hga t Nh le_rfl (by omega) hVL ht (by rw [hcR]; exact hεp) (hLb.trans hLr)
    rw [hcR] at hPr
    have hε0 : 0 ≤ ε := by have := H.hε; linarith
    have hcg1 : 1 ≤ cgb * cR R' ((L : ℝ) ^ 2) cm C₂x := by rw [hcR, hcgc]; linarith
    have hcgε' : cgb * (cR R' ((L : ℝ) ^ 2) cm C₂x * ε) ≤ 1 / 7 := by
      rw [hcR, ← mul_assoc, hcgc]; rw [hmB] at hgε7; exact hgε7
    have hcδ' : 16 * (8 * (csN 2 : ℝ)) * (3 * C₁w + 1) * kB (kθ0 L R'.A C₀o ηo) C₁k (8 * cx κ cT) +
        3 * cP * (3 * C₁w + 1) + 4 * ce * cgb * (1 + cgb) +
        4 * ce * cgb * cδ * (cR R' ((L : ℝ) ^ 2) cm C₂x * ε) ≤ 6 / 7 * cδ := by
      rw [hRA', hcR]
      have e1 : 4 * ce * cgb * cδ * (c * ε) = (4 * ceff L (max c 2) * (max B' 0 + 1) * ε) * cδ := by
        rw [hmc, hmB, hce, ← hcgc]; ring
      have e2 := mul_le_mul_of_nonneg_right hBτε hcδ0
      have e3 : 16 * (8 * (csN 2 : ℝ)) * (3 * C₁w + 1) * Bk + 3 * cP * (3 * C₁w + 1) +
          4 * ce * cgb * (1 + cgb) = cδ / 3 := by rw [hcδX, hXc, hmc]; ring
      rw [e1]
      linarith
    have hsumε : cδ * (cR R' ((L : ℝ) ^ 2) cm C₂x ^ 2 * (ε / (betaL L / 4))) ≤ 1 / 8 := by
      rw [hcR]
      have e : cδ * (c ^ 2 * (ε / (betaL L / 4))) = cδ * c ^ 2 * (4 / betaL L) * ε := by
        field_simp
      rw [e]; exact hcδε
    have hT : ∀ k j, k < j → j < Nh →
        ‖Obs2.tadInc2 P (Obs2.histCovO R' t) (Obs2.histVO2 R' P (Obs2.obsInit .two V P) t) k j‖ ≤
          ce * (2 / (L : ℝ)) ^ (j - k) * (t k).1 := fun k j hkj hj =>
      X.tadInc2_le P _ (Obs2.obsInit_isObs .two V P) hkj hj
    have hnn : ∀ i < Nh,
        ‖Obs2.frakN2 P (Obs2.histCovO R' t) (Obs2.histVO2 R' P (Obs2.obsInit .two V P) t) i‖ ≤
          cgb * (cR R' ((L : ℝ) ^ 2) cm C₂x * (t i).1) := by
      intro i hi
      rw [hcR, ← mul_assoc, hcgc]
      have h := (hl i hi).2.1
      have hg := (X.hg i hi.le).1.le
      have h' : B' * (t i).1 ≤ (B' + 1) * (t i).1 := by
        rw [add_mul, one_mul]; exact le_add_of_nonneg_right hg
      exact h.trans h'
    have key := obs_hist_rel2 R' (by rw [hRA']; exact hKB) hC₁k hWB hC₁w hSB' hV hm1 hβ0
      (by norm_num : (1 / 2 : ℝ) ≤ 1) H hρ0' hρ8' P V hga hmu t Nh le_rfl hNh0 (by omega) ht
      (by rw [hRA']; exact hθ0) (by rw [hRA']; exact hθ) (by rw [hRA', hcR]; exact hsmk)
      (by rw [hcR]; exact hcε) (by rw [hcR]; exact hεε) (by rw [hRA', hcR]; exact hεk) hLwk
      (by rw [hcR]; exact hC₁ε) (by rw [hcR]; exact hε₁') (by linarith) le_rfl
      (by have := H.h6; linarith) hcgb0 hcP0 hcδ0 hce0 (by positivity) hq4 hcg1 hcgε' hcδ'
      hsumε hT hnn (by rw [hcR]; exact hPr)
    rw [hcR] at key
    intro k hk
    obtain ⟨h1, h2⟩ := key k hk
    have e : cδ * c ^ 2 * (t k).1 ^ 2 = cδ * (c * (t k).1) ^ 2 := by ring
    rw [e]
    exact ⟨h1, h2⟩
  have hcδc : 0 ≤ cδ * c ^ 2 := by positivity
  refine ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, Cf, Cb, KZ, KG, bubB L ce K cS2,
    nuB L Cq Cl cS (cx κ cT) c ce, 9 / 64 * ce ^ 2, 7 * ce, B', cδ * c ^ 2, hC2, hε1, hB,
    lamConcl_of hL2 hε1 hSp, hLoop, hcδc, hRel, ?_⟩
  have hM2 := multiConcl2_of hL2 hε1 hSp (multiConcl_of (by omega) hε1 hSp hMag)
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm P V KP hKP hga hmu hrg x hx hj
  obtain ⟨hB0, -, hloop⟩ := hLoop N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm P V
  exact hM2 N R hP hi0 hRℓ hRA hRρ Nh hNh.le m hm b μ₀ hadm P V _ _ (7 * ce) (cδ * c ^ 2) KP
    hB0 hcδc hKP hmu (hRel N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm P V hga hmu) hloop hrg
    x hx hj

end

end Spin2
