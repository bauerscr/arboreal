import Spin2.Restart.Restart2Master
import Spin2.Master.MasterAllConst

/-!
# The restart with large transients, linear form (B3, T4′)

**`MasterCore.restartDT_lin`**: `MasterCore.restartDT` with the envelope chosen explicitly. For a
datum `o'` at scale `m_r` (as in `restartDT`) with `|β_{m_r}| + D_{m_r} ≤ M₀`,
`‖𝒲_{m_r}(B)‖ ≤ w`, `A^{(|𝓑(X)|−4)_+}‖K_{m_r}(X)‖ ≤ k`, the **scale condition**
`c_bn(1280K²·8/(7L)+1)·2c_W(cǧ_{m_r}) ≤ 1/1344` and
`1344(8c_Nk + Γ_w w) ≤ s_{m_r}²M₀` (`Γ_w = 960c_NB(cε) + c_bn(1280K²·8/(7L)+1) + 5c_P(cε)`):

  `|β_{m_r+j}| ≤ (4/3)M₀ ∏_{k<j}|1 − 𝔫F_{m_r+k}|`  for `j ≤ N_h − m_r`.

So the restarted coupling is bounded by a quantity **linear in the datum**:
`M₀ = max(|β_{m_r}| + D_{m_r}, 1344(8c_Nk + Γ_ww)/s_{m_r}²)`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

variable {L : ℕ} [NeZero L]

/-- The tadpole constant `c_bn(1280K²·8/(7L) + 1)` of the initial `𝒲`. -/
def MasterCore.rdtC (_D : MasterCore L) : ℝ :=
  cbnC * (1280 * Obs2.locK 2 ^ 2 * (8 / (7 * L)) + 1)

/-- The `𝒲` constant `Γ_w = 960c_NB(cε) + c_bn(1280K²·8/(7L)+1) + 5c_P(cε)`. -/
def MasterCore.rdtΓ (D : MasterCore L) : ℝ :=
  8 * (PtCorr2.csN 2 : ℝ) * (120 * D.Bk * (D.c * D.ε)) + D.rdtC + 5 * D.cP * (D.c * D.ε)

theorem MasterCore.rdt_L (D : MasterCore L) : 4 / 3 * (2 / (L : ℝ)) ≤ 1 / 56 := by
  have h1 : prodLb ≤ (D.Lo : ℝ) := D.hLb
  have h2 : (D.Lo : ℝ) ≤ L := by exact_mod_cast D.hLo
  have hpl : (1010 : ℝ) ≤ prodLb := by
    unfold prodLb; have := Obs2.one_le_locK 2; nlinarith
  have hL0 : (0 : ℝ) < L := by linarith
  rw [show 4 / 3 * (2 / (L : ℝ)) = 8 / (3 * L) by ring, div_le_div_iff₀ (by positivity)
    (by norm_num)]
  linarith

/-- The constant condition `c_t ≤ 1/48` of `restartDT` from the linear choice of `M₀`. -/
theorem rdt_ct_le {cN k w x M₀ C a g Bce cPce q : ℝ} (hx : 0 < x) (hX : 0 < x * M₀) (hM0 : 0 < M₀)
    (hq : q ≤ 1 / 56)
    (hM : 1344 * (8 * cN * k + (8 * cN * Bce + C + cPce) * w) ≤ x * M₀)
    (hg : C * (a * g * 2) ≤ 1 / 1344) :
    8 * cN * (k + Bce * w) / (x * M₀) + C * (a * g * (2 * x * M₀) + w) / (x * M₀) + q +
      cPce * w / (x * M₀) ≤ 1 / 48 := by
  have e : 8 * cN * (k + Bce * w) / (x * M₀) + C * (a * g * (2 * x * M₀) + w) / (x * M₀) + q +
      cPce * w / (x * M₀) =
      (8 * cN * k + (8 * cN * Bce + C + cPce) * w) / (x * M₀) + C * (a * g * 2) + q := by
    field_simp
    ring
  rw [e]
  have h1 : (8 * cN * k + (8 * cN * Bce + C + cPce) * w) / (x * M₀) ≤ 1 / 1344 := by
    rw [div_le_iff₀ hX]; linarith
  linarith

theorem rdt_final {β D M₀ ct P : ℝ} (hb : β + D ≤ M₀) (hD : 0 ≤ D) (hct : ct ≤ 1 / 48)
    (hM0 : 0 ≤ M₀) (hP : 0 ≤ P) : (β + (1 / 8 + 10 * ct) * M₀) * P ≤ 4 / 3 * M₀ * P := by
  refine mul_le_mul_of_nonneg_right ?_ hP
  have := mul_le_mul_of_nonneg_right hct hM0
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **The restart with large transients, linear form.** -/
theorem MasterCore.restartDT_lin (D : MasterCore L) (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)]
    [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = D.ℓ) (hRA : R.A = D.A)
    (hRρ : R.ρ = D.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ) (hm : m ∈ mRange L N)
    (b μ₀ : ℝ) (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) D.κ D.cm D.cT D.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    (P : Obs2.ObsPts 2 L N) (V : Obs2.OCoup .two) (mr : ℕ) (o' : Obs2.ObsSt .two L N)
    (hmr0 : 0 < mr) (hmrN : mr ≤ Nh) (h0 : o'.IsObs) (hl0 : ObsLocInv P mr o')
    (hs0 : ObsSymInv mr o')
    (hf0 : ∀ b, Obs2.Loc2Form P.a (o'.V b : Obs.SA .two (Lam 2 L N)).a)
    (hp0 : ∀ b, (o'.V b : Obs.SA .two (Lam 2 L N)).a =
      Obs.LocObs.mass2 (o'.V b : Obs.SA .two (Lam 2 L N)).a • Obs.LocObs.pbp P.a)
    {M₀ k w : ℝ} (hM0 : 0 < M₀) (hk : 0 ≤ k) (hw : 0 ≤ w)
    (hb : ‖Obs2.betaTot2 (L := L) (N := N) mr
          (histVF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) mr)‖ +
        Obs2.shareDev2 P.a mr
          (histVF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) mr) ≤ M₀)
    (hW : WbHF (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) mr w)
    (hK : KbHF (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) mr k)
    (hg : D.rdtC * (D.cWo * (D.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ mr).1) * 2) ≤ 1 / 1344)
    (hM : 1344 * (8 * (PtCorr2.csN 2 : ℝ) * k + D.rdtΓ * w) ≤
      histS (R.withMsq m) mr (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * M₀) :
    ∀ j ≤ Nh - mr,
      ‖Obs2.betaTot2 (L := L) (N := N) (mr + j)
          (histVF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (mr + j))‖ ≤
        4 / 3 * M₀ * ∏ k ∈ range j, ‖1 - Obs2.frakN2F P (Obs2.histCovO (R.withMsq m)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          (histVF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) mr (mr + k)‖ := by
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  set s := histS (R.withMsq m) mr t with hsd
  obtain ⟨H, -, -⟩ := D.hXm N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm
  have hcR : cR (R.withMsq m) ((L : ℝ) ^ 2) D.cm D.C₂x = D.c := by
    rw [D.hc]; exact cR_congr (show R.ℓ = D.ℓ from hRℓ) _ _ _
  have hc2 : 2 ≤ D.c := hcR ▸ two_le_cR (R.withMsq m) H.hcmu H.hC₂
  have hε0 : 0 ≤ D.ε := by have := H.hε; linarith
  have hcε : 0 ≤ D.c * D.ε := mul_nonneg (by linarith) hε0
  have hBk : 0 ≤ D.Bk := D.consts_nonneg.2.2.2.2.2.2.1
  have hcP : 0 ≤ D.cP := by
    show 0 ≤ (cbnC : ℝ) * D.Cpf L * (6 / 5 * L + 3072 * Obs2.locK 2 ^ 2)
    have := D.hCpf L; positivity
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8', -, -⟩ := id D.hC2
  have hρ0 : 0 ≤ (R.withMsq m).ρ := by rw [show (R.withMsq m).ρ = D.ρ from hRρ]; exact hρpos.le
  have hρ8 : (R.withMsq m).ρ ≤ 1 / 8 := by rw [show (R.withMsq m).ρ = D.ρ from hRρ]; exact hρ8'
  have hs : 0 < s := histS_pos' (R.withMsq m) hρ0 hρ8 t mr
  have hX : 0 < s ^ 2 * M₀ := by positivity
  have hkw0 : 0 ≤ 120 * D.Bk * (D.c * D.ε) * w := by positivity
  have hct0 := rdt_ct_le (cN := (PtCorr2.csN 2 : ℝ)) (k := k) (w := w) (x := s ^ 2)
    (C := D.rdtC) (a := D.cWo) (g := D.c * (t mr).1) (Bce := 120 * D.Bk * (D.c * D.ε))
    (cPce := 5 * D.cP * (D.c * D.ε)) (by positivity) hX hM0 D.rdt_L
    (by
      have e : D.rdtΓ * w = (8 * (PtCorr2.csN 2 : ℝ) * (120 * D.Bk * (D.c * D.ε)) + D.rdtC +
          5 * D.cP * (D.c * D.ε)) * w := by unfold MasterCore.rdtΓ; ring
      rw [← e]; exact hM) hg
  have hct : 8 * (PtCorr2.csN 2 : ℝ) * (k + 120 * D.Bk * (D.c * D.ε) * w) / (s ^ 2 * M₀) +
        cbnC * (1280 * Obs2.locK 2 ^ 2 * (8 / (7 * L)) + 1) *
          (D.cWo * (D.c * (t mr).1) * (2 * s ^ 2 * M₀) + w) / (s ^ 2 * M₀) +
        4 / 3 * (2 / (L : ℝ)) + 5 * D.cP * (D.c * D.ε) * w / (s ^ 2 * M₀) ≤ 1 / 48 := hct0
  have hW' : WbHF (R.withMsq m) P mr o' t mr
      (D.cWo * (D.c * (t mr).1) * (2 * s ^ 2 * M₀) + w) := by
    intro b' hb'
    refine (hW b' hb').trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : 1 ≤ D.cWo := D.consts_nonneg.2.2.2.2.2.1
    have hg0 : 0 ≤ (t mr).1 := by
      have := (inDh_rg_of_D (R.withMsq m) (D.hXm N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm).2.2 hD
        Nh le_rfl).1 mr hmrN
      exact this.1.le
    have : 0 ≤ D.cWo * (D.c * (t mr).1) * (2 * s ^ 2 * M₀) := by positivity
    linarith
  have key := D.restartDT N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hD P V mr o' hmr0 hmrN h0
    hl0 hs0 hf0 hp0 M₀ (k + 120 * D.Bk * (D.c * D.ε) * w) w hM0 (by linarith) hw (by linarith)
    hct hb hW'
    (fun X hX' => (hK X hX').trans (ENNReal.ofReal_le_ofReal (by linarith)))
  intro j hj
  have hP0 : 0 ≤ ∏ k ∈ range j, ‖1 - Obs2.frakN2F P (Obs2.histCovO (R.withMsq m) t)
      (histVF2 (R.withMsq m) P mr o' t) mr (mr + k)‖ := prod_nonneg fun _ _ => norm_nonneg _
  have hbD : 0 ≤ Obs2.shareDev2 P.a mr (histVF2 (R.withMsq m) P mr o' t mr) :=
    sum_nonneg fun _ _ => norm_nonneg _
  exact (key j hj).trans (rdt_final hb hbD hct hM0.le hP0)
end

end Spin2
