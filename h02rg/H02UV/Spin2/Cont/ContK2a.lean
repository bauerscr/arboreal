import Spin2.Cont.ContArt1
import Spin2.Cont.ContWire6
import PtCorr2.Cont.ContK2a

set_option autoImplicit false

/-!
# B3, T6: the backward ratio of the restart envelope (route (c) of `art_note`)

* `k2_ratio_pure`: `s_{m+i}²M_i ≤ (7/5)^d s_{m+i+d}²M_{i+d}` from `s_k ≤ (15/14)s_{k+1}` and
  `a_k ≥ 6/7` (`M_i = rkEnv M₀ a i`; `(15/14)²(7/6) ≤ 7/5`).
* **`MasterCore.k2_n7`**: `‖𝔫F_{m_r,i}‖ ≤ 1/7` for `m_r ≤ i < N_h` along the restarted history of
  any observable datum along `D_ε` (`frakN2F_mem_le` with the reference bounds `‖𝔫^{(2)}_i‖ ≤ 1/8`,
  `|tadInc2| ≤ c_eff(2/L)^{j−k}ǧ_k`; the setup of `cw2_restartDT`).
* **`MasterCore.k2_envRatio`**: `2s_{m_r+i}²M_i ≤ (7/5)^{i'−i}·2s_{m_r+i'}²M_{i'}` for
  `i ≤ i' ≤ N_h − m_r` (the envelope of `cw2_restartDT`), i.e. the `a`-sector envelope at an
  earlier scale against the fixed weight at a later one.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

variable {L : ℕ} [NeZero L]

theorem k2_rkEnv_succ (M₀ : ℝ) (a : ℕ → ℝ) (k : ℕ) :
    Obs2.rkEnv M₀ a (k + 1) = Obs2.rkEnv M₀ a k * a k := by
  unfold Obs2.rkEnv; rw [prod_range_succ]; ring

/-- **The backward ratio of the envelope** (pure). -/
theorem k2_ratio_pure (s a : ℕ → ℝ) (M₀ : ℝ) (hM0 : 0 ≤ M₀) (mr n : ℕ) (hs : ∀ j, 0 ≤ s j)
    (hss : ∀ j, s j ≤ 15 / 14 * s (j + 1)) (ha0 : ∀ k, 0 ≤ a k) (ha : ∀ k < n, 6 / 7 ≤ a k) :
    ∀ d i, i + d ≤ n → s (mr + i) ^ 2 * Obs2.rkEnv M₀ a i ≤
      (7 / 5) ^ d * (s (mr + i + d) ^ 2 * Obs2.rkEnv M₀ a (i + d)) := by
  intro d
  induction d with
  | zero => intro i _; simp
  | succ d ih =>
    intro i hid
    have h1 := ih i (by omega)
    set k := i + d with hk
    have hE0 : 0 ≤ Obs2.rkEnv M₀ a k :=
      mul_nonneg hM0 (prod_nonneg fun l _ => ha0 l)
    have hak := ha k (by omega)
    have hs1 := hss (mr + k)
    have hsk := hs (mr + k)
    have hsq : s (mr + k) ^ 2 ≤ (15 / 14) ^ 2 * s (mr + k + 1) ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hsk hs1 2
    have hE : Obs2.rkEnv M₀ a k ≤ 7 / 6 * Obs2.rkEnv M₀ a (k + 1) := by
      rw [k2_rkEnv_succ]; nlinarith
    have hstep : s (mr + k) ^ 2 * Obs2.rkEnv M₀ a k ≤
        7 / 5 * (s (mr + k + 1) ^ 2 * Obs2.rkEnv M₀ a (k + 1)) := by
      have hE1 : 0 ≤ Obs2.rkEnv M₀ a (k + 1) := by
        rw [k2_rkEnv_succ]; exact mul_nonneg hE0 (ha0 k)
      calc s (mr + k) ^ 2 * Obs2.rkEnv M₀ a k
          ≤ ((15 / 14) ^ 2 * s (mr + k + 1) ^ 2) * (7 / 6 * Obs2.rkEnv M₀ a (k + 1)) :=
            mul_le_mul hsq hE hE0 (by positivity)
        _ = (15 / 14) ^ 2 * (7 / 6) * (s (mr + k + 1) ^ 2 * Obs2.rkEnv M₀ a (k + 1)) := by ring
        _ ≤ 7 / 5 * (s (mr + k + 1) ^ 2 * Obs2.rkEnv M₀ a (k + 1)) :=
            mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    have e1 : mr + i + (d + 1) = mr + k + 1 := by omega
    have e2 : i + (d + 1) = k + 1 := by omega
    rw [e1, e2, pow_succ]
    have e3 : mr + i + d = mr + k := by omega
    rw [e3] at h1
    calc s (mr + i) ^ 2 * Obs2.rkEnv M₀ a i ≤ (7 / 5) ^ d * (s (mr + k) ^ 2 * Obs2.rkEnv M₀ a k) := h1
      _ ≤ (7 / 5) ^ d * (7 / 5 * (s (mr + k + 1) ^ 2 * Obs2.rkEnv M₀ a (k + 1))) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = _ := by ring

set_option maxHeartbeats 2000000 in
/-- **`‖𝔫F_{m_r,i}‖ ≤ 1/7`** along the restarted history of an observable datum (`D_ε`). -/
theorem MasterCore.k2_n7 (D : MasterCore L) (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)]
    [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = D.ℓ) (hRA : R.A = D.A)
    (hRρ : R.ρ = D.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ) (hm : m ∈ mRange L N)
    (b μ₀ : ℝ) (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) D.κ D.cm D.cT D.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    (P : Obs2.ObsPts 2 L N) (V : Obs2.OCoup .two) (mr : ℕ) (o' : Obs2.ObsSt .two L N)
    (h0 : o'.IsObs) {i : ℕ} (hmi : mr ≤ i) (hi : i < Nh) :
    ‖Obs2.frakN2F P (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
      (histVF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) mr i‖ ≤ 1 / 7 := by
  have hLoop := MasterCore.loopConclD D
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8, -, hCN⟩ := id D.hC2
  set R' := R.withMsq m with hR'
  obtain ⟨H, hm1, F1⟩ := D.hXm N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm
  obtain ⟨hV, hVL⟩ := (hCN N R hP hi0 hRℓ hRA hRρ hN Nh hNh).2.2.2.2.2.2.2.2.2 m hm
  have ht := inDh_rg_of_D R' F1 hD Nh le_rfl
  have hRA' : R'.A = D.A := hRA
  have hρ0' : 0 ≤ R'.ρ := by rw [show R'.ρ = D.ρ from hRρ]; exact hρpos.le
  have hρ8' : R'.ρ ≤ 1 / 8 := by rw [show R'.ρ = D.ρ from hRρ]; exact hρ8
  have hcR : cR R' ((L : ℝ) ^ 2) D.cm D.C₂x = D.c := by
    rw [D.hc]; exact cR_congr (show R.ℓ = D.ℓ from hRℓ) _ _ _
  have hSB' : StepBounds L R'.A D.C₀x D.ηx D.εsx D.CKx D.C₂x D.CDx D.Cqx D.Clx D.cSx := by
    rw [hRA']; exact D.hSBx
  have hmsq : R'.msq ∈ mRange L N := hm
  have X := c2ctx_master R' (by omega) D.hL49 hSB' H hm1 hV hVL hρ0' hρ8' hmsq D.hβε ht
  rw [hcR] at X
  have hc2 : 2 ≤ D.c := hcR ▸ two_le_cR R' H.hcmu H.hC₂
  have hmc : max D.c 2 = D.c := max_eq_left hc2
  have hce0 : 0 ≤ ceff L D.c := X.c_nonneg
  have hε0 : 0 ≤ D.ε := by have := H.hε; linarith
  obtain ⟨-, -, q, -, -, hl⟩ := hLoop N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hD P V
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  set o₀ := Obs2.obsInit .two V P with ho₀d
  have ho₀ : o₀.IsObs := Obs2.obsInit_isObs .two V P
  have hL0 : (0 : ℝ) < L := by
    have := D.hL49; exact_mod_cast (show 0 < L by omega)
  have hq4 : (2 : ℝ) / L ≤ 1 / 4 := by
    rw [div_le_div_iff₀ hL0 (by norm_num)]
    have : (49 : ℝ) ≤ L := by exact_mod_cast D.hL49
    linarith
  have hT : ∀ k j, k < j → j < Nh →
      ‖Obs2.tadInc2 P (Obs2.histCovO R' t) (Obs2.histVO2 R' P o₀ t) k j‖ ≤
        ceff L D.c * (2 / (L : ℝ)) ^ (j - k) * (t k).1 := fun k j hkj hj =>
    X.tadInc2_le P _ ho₀ hkj hj
  have hceε : ceff L D.c * D.ε ≤ 1 / 8 := by
    have hB0' : (0 : ℝ) ≤ max D.B' 0 := le_max_right _ _
    have h1 : ceff L D.c * D.ε ≤ ceff L D.c * D.ε * (max D.B' 0 + 1) :=
      le_mul_of_one_le_right (by positivity) (by linarith)
    have h2 : 4 * ceff L (max D.c 2) * (max D.B' 0 + 1) * D.ε =
        4 * (ceff L D.c * D.ε * (max D.B' 0 + 1)) := by rw [hmc]; ring
    have h3 : 4 * (ceff L D.c * D.ε * (max D.B' 0 + 1)) ≤ 1 / 2 := h2 ▸ D.hBτε
    linarith
  have hBg : ∀ k < Nh, ceff L D.c * (t k).1 ≤ 1 := fun k hk => by
    have hgk : (t k).1 ≤ D.ε := (ht.1 k hk.le).2.1
    have := mul_le_mul_of_nonneg_left hgk hce0
    linarith
  have hLr : (D.Lo : ℝ) ≤ L := by exact_mod_cast D.hLo
  have hq56 : 4 / 3 * (2 / (L : ℝ)) ≤ 1 / 56 := by
    have hpl : (1010 : ℝ) ≤ prodLb := by
      unfold prodLb; have := Obs2.one_le_locK 2; nlinarith
    have := D.hLb
    rw [show 4 / 3 * (2 / (L : ℝ)) = 8 / (3 * L) by ring, div_le_div_iff₀ (by positivity)
      (by norm_num)]
    linarith
  have h1 := frakN2F_mem_le R' P mr o' t h0 o₀ ho₀ (by positivity) hq4 hT hBg hmi hi
  have h2 : ‖Obs2.frakN2 P (Obs2.histCovO R' t) (Obs2.histVO2 R' P o₀ t) i‖ ≤ 1 / 8 :=
    (hl i hi).1
  have h3 : (1 / 2 : ℝ) ^ (i - mr) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h4 : 4 / 3 * (2 / (L : ℝ)) * (1 / 2) ^ (i - mr) ≤ 4 / 3 * (2 / (L : ℝ)) :=
    mul_le_of_le_one_right (by positivity) h3
  refine h1.trans ?_
  linarith

set_option maxHeartbeats 1000000 in
/-- **The backward ratio of the restart envelope** along `D_ε`. -/
theorem MasterCore.k2_envRatio (D : MasterCore L) (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)]
    [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = D.ℓ) (hRA : R.A = D.A)
    (hRρ : R.ρ = D.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ) (hm : m ∈ mRange L N)
    (b μ₀ : ℝ) (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) D.κ D.cm D.cT D.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    (P : Obs2.ObsPts 2 L N) (V : Obs2.OCoup .two) (mr : ℕ) (o' : Obs2.ObsSt .two L N)
    (h0 : o'.IsObs) {M₀ : ℝ} (hM0 : 0 ≤ M₀) {i i' : ℕ} (hii : i ≤ i') (hi' : i' ≤ Nh - mr) :
    2 * histS (R.withMsq m) (mr + i) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
        Obs2.rkEnv M₀ (fun i => ‖1 - Obs2.frakN2F P (Obs2.histCovO (R.withMsq m)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          (histVF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) mr (mr + i)‖) i ≤
      (7 / 5) ^ (i' - i) * (2 * histS (R.withMsq m) (mr + i') (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
        Obs2.rkEnv M₀ (fun i => ‖1 - Obs2.frakN2F P (Obs2.histCovO (R.withMsq m)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          (histVF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) mr (mr + i)‖) i') := by
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8, -, -⟩ := id D.hC2
  have hρ0' : 0 ≤ (R.withMsq m).ρ := by rw [show (R.withMsq m).ρ = D.ρ from hRρ]; exact hρpos.le
  have hρ8' : (R.withMsq m).ρ ≤ 1 / 8 := by rw [show (R.withMsq m).ρ = D.ρ from hRρ]; exact hρ8
  have ha : ∀ k < Nh - mr, 6 / 7 ≤ ‖1 - Obs2.frakN2F P (Obs2.histCovO (R.withMsq m)
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
      (histVF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) mr (mr + k)‖ := by
    intro k hk
    have h7 := D.k2_n7 N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hD P V mr o' h0
      (i := mr + k) (by omega) (by omega)
    have h2 := norm_sub_norm_le (1 : ℂ) (Obs2.frakN2F P (Obs2.histCovO (R.withMsq m)
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
      (histVF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) mr (mr + k))
    rw [norm_one] at h2
    linarith
  have key := k2_ratio_pure (fun j => histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
    _ M₀ hM0 mr (Nh - mr)
    (fun j => (histS_pos' (R.withMsq m) hρ0' hρ8' _ j).le)
    (fun j => MasterFacts.cw2_histS_le_succ (R.withMsq m) hρ0' hρ8' _ j) (fun _ => norm_nonneg _) ha
    (i' - i) i (by omega)
  have e1 : mr + i + (i' - i) = mr + i' := by omega
  have e2 : i + (i' - i) = i' := by omega
  simp only [e1, e2] at key
  nlinarith [key]

end

end Spin2
