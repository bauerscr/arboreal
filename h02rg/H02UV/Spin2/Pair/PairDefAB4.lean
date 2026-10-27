import Spin2.Pair.PairDefAB2
import Spin2.Pair.PairErrAB3
import PtCorr2.Pair.VObsStepAB1

/-!
# The quartic coefficient with second-order defects; the Pauli defects of the reduced history

The quartic coefficient `M₄` produced by the barycentric `loc^{ab}` grows like `(L^k/|x|)²` relative
to the norm (`norm_Mw_le`; `‖M₄ψ̄_aψ_aψ̄_bψ_b‖_{T_k} ≍ |M₄|ℓ_k⁴(|x|/L^k)²`, `tNorm_m4_le`). The
first-order defect bounds `hist_detDef_le`, `hist_m2Def_le` (`≍ |x|/L^k`) used in
`PairDefSizesR2` are then too weak; the defects are of second order (`Obs2.norm_detDef_le2`,
`Obs2.norm_m2Def_le2`, from the Gram representation), which matches `M₄` exactly.

* **`PairDefSizesR3 c_d`**: `PairDefSizesR2` with the second-order weight of the seed:
  `‖M_{4,k}‖·2ℓ_k²(L^{j_x+1}ℓ_k/L^{k+1})²`; **`pairDefSumR_of_sizes3`** (`⇒ PairDefSumR`);
  **`seed_geom2_le`**: if `‖M_{4,k}‖ℓ_k⁴ ≤ Dq^{k-j}` with `2q ≤ L²`, the seed sum is `≤ 4D`
  (room for a growth `q < L²/2` per scale, against `q < L/2` in `seed_geom_le`).
* Exact Pauli defects of the reduced history (`PtCorr2.pdefM2_hVR_eq`, `pdefAB2_hVR_sub`):
  **`pdefM2_hist_le`**: `|𝔡₂_k| ≤ |M₄_k|(nℓ_k/L^{k+1})²`; **`pdefAB2_hist_sub_le`**:
  `|𝔡_k − M₄_k det_k| ≤ ∑_B∑_{(u,v)≠(a,a)}|c_{uv}(V'_k(B))|·nℓ_k²/L^{k+1}`.
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

variable {L N : ℕ} [NeZero L]

/-- **The seed sum with second-order geometric weights**: `∑_{j≤k<n} 2(L^{j-k})²Dq^{k-j} ≤ 4D` for
`0 ≤ q`, `2q ≤ L²`. -/
theorem seed_geom2_le (hL : (2 : ℝ) ≤ L) {D q : ℝ} (hD : 0 ≤ D) (hq : 0 ≤ q)
    (hqL : 2 * q ≤ (L : ℝ) ^ 2) (j n : ℕ) (f : ℕ → ℝ)
    (hf : ∀ k ∈ Finset.Ico j n,
      f k ≤ 2 * ((L : ℝ) ^ (j + 1) / (L : ℝ) ^ (k + 1)) ^ 2 * (D * q ^ (k - j))) :
    ∑ k ∈ Finset.Ico j n, f k ≤ 4 * D := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hL2 : (0 : ℝ) < (L : ℝ) ^ 2 := by positivity
  set x : ℝ := q / (L : ℝ) ^ 2 with hx
  have hx0 : 0 ≤ x := div_nonneg hq hL2.le
  have hx1 : x ≤ 1 / 2 := by rw [hx, div_le_iff₀ hL2]; linarith
  have hterm : ∀ k ∈ Finset.Ico j n, f k ≤ 2 * D * x ^ (k - j) := by
    intro k hk
    have hjk : j ≤ k := (Finset.mem_Ico.1 hk).1
    refine (hf k hk).trans (le_of_eq ?_)
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hjk
    have hLi : (0 : ℝ) < (L : ℝ) ^ i := pow_pos hL0 i
    have e1 : (L : ℝ) ^ (j + 1) / (L : ℝ) ^ (j + i + 1) = ((L : ℝ) ^ i)⁻¹ := by
      rw [show j + i + 1 = (j + 1) + i by ring, pow_add]
      field_simp
      ring
    have e2 : (q / (L : ℝ) ^ 2) ^ i = q ^ i / ((L : ℝ) ^ i) ^ 2 := by
      rw [div_pow, ← pow_mul, ← pow_mul, mul_comm 2 i]
    rw [Nat.add_sub_cancel_left, hx, e1, e2]
    field_simp
  calc ∑ k ∈ Finset.Ico j n, f k ≤ ∑ k ∈ Finset.Ico j n, 2 * D * x ^ (k - j) := sum_le_sum hterm
    _ = 2 * D * ∑ i ∈ range (n - j), x ^ i := by
        rw [mul_sum, sum_Ico_eq_sum_range]; simp
    _ ≤ 2 * D * 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := n - j) hx0 (by linarith)
        rw [Finset.range_eq_Ico]
        refine h.trans ?_
        rw [pow_zero, div_le_iff₀ (by linarith)]; linarith
    _ = 4 * D := by ring

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- **Named input: the `ab` sizes of the reduced history, second-order seed weights.** As
`PairDefSizesR2`, with the seed entering per scale as `‖M_{4,k}‖·2ℓ_k²(L^{j_x+1}ℓ_k/L^{k+1})²`. -/
def PairDefSizesR3 (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N)
    (cd : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∃ (ℓs sq sw sp sf : ℕ → ℝ) (M4 : ℕ → ℂ) (sL : ℝ),
      (∀ k, 0 < ℓs k ∧ 0 ≤ sq k ∧ 0 ≤ sw k ∧ 0 ≤ sp k ∧ 0 ≤ sf k) ∧
      (∀ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
        let t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀
        let C := Obs2.histCovO (R.withMsq m) t
        let V := PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x) t
        let W := PtCorr2.hWR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x) t
        let K := PtCorr2.hKR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x) t
        GoodCov2 k (ℓs k) (C k) ∧
        (∀ B, (Obs2.Q2O (ptsX x) k (K k) B : Obs.SA .two (Lam 2 L N)).ab ∈
          NX (nbhd k (blockSet (L := L) (N := N) k B) : Set (Lam 2 L N))) ∧
        (∀ B, Tj 2 (L : ℝ) k (ℓs k) (Obs2.Q2O (ptsX x) k (K k) B : Obs.SA .two (Lam 2 L N)).ab ≤
          ENNReal.ofReal (sq k)) ∧
        (∀ B, (W k B : Obs.SA .two (Lam 2 L N)).ab ∈
          NX (nbhd k (blockSet (L := L) (N := N) k B) : Set (Lam 2 L N))) ∧
        (∀ B, Tj 2 (L : ℝ) k (ℓs k) (W k B : Obs.SA .two (Lam 2 L N)).ab ≤
          ENNReal.ofReal (sw k)) ∧
        ‖Obs2.pdefAB2 (ptsX x) k (C k) (V k) -
            M4 k * (C k 0 0 * C k x x - C k 0 x * C k x 0)‖ ≤ sp k ∧
        ‖ε (FC (C k) (Obs2.VprLO k (C k) (V k) : Obs.SA .two (Lam 2 L N)).ab
          (Obs2.VprLO k (C k) (V k) : Obs.SA .two (Lam 2 L N)).e)‖ ≤ sf k) ∧
      ‖lastDefR R Nh m b μ₀ oR x‖ ≤ sL ∧
      ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
          (2 * (Q1 2 * sq k) + 2 * (Q1 2 * sw k) + sp k + sf k +
            ‖M4 k‖ * (2 * ℓs k ^ 2 *
              ((L : ℝ) ^ (Obs.coal L (0 : Lam 2 L N) x + 1) * (ℓs k / (L : ℝ) ^ (k + 1))) ^ 2)) +
          sL ≤
        cd * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ ^ 2 *
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1

set_option maxHeartbeats 1000000 in
/-- **`PairDefSumR` from the `ab` sizes with second-order seed weights.** -/
theorem pairDefSumR_of_sizes3 {Nh : ℕ} (hN : Nh + 2 = N) (hL : pauliL0 2 ≤ L) (hL2 : 2 ≤ L)
    (m b μ₀ : ℝ) (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) {cd : ℝ}
    (hA : PairAnchR (L := L) (N := N) Nh oR) (hS : PairDefSizesR3 R Nh m b μ₀ lam oR cd) :
    PairDefSumR R Nh m b μ₀ lam oR cd := by
  intro x hx h1 hj
  obtain ⟨ℓs, sq, sw, sp, sf, M4, sL, h0, hk, hlast, hsum⟩ := hS x hx h1 hj
  have hanc := hA x hx h1 hj
  set jx := Obs.coal L (0 : Lam 2 L N) x with hjx
  set C := Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) with hCdef
  obtain ⟨w, hwx, hwl⟩ := PtCorr2.exists_path_sum (n := L ^ N) (x : Lam 2 L N)
  have hpe : Obs2.pathEnd (0 : Lam 2 L N) w = x := by rw [Obs2.pathEnd, zero_add, hwx]
  have hlen : (w.length : ℝ) ≤ (L : ℝ) ^ (jx + 1) := by
    have h2 := two_supNorm_lt_coal hL2 x
    rw [sub_zero] at h2
    have : w.length ≤ L ^ (jx + 1) := hwl.trans h2.le
    exact_mod_cast this
  have hstep : ∀ k ∈ Finset.Ico jx (Nh + 1), ‖hDefR R m b μ₀ oR x k‖ ≤
      2 * (Q1 2 * sq k) + 2 * (Q1 2 * sw k) + sp k + sf k +
        ‖M4 k‖ * (2 * ℓs k ^ 2 * ((L : ℝ) ^ (jx + 1) * (ℓs k / (L : ℝ) ^ (k + 1))) ^ 2) := by
    intro k hk'
    obtain ⟨hl, hq, hw, hp, hf⟩ := h0 k
    obtain ⟨hC, hlocQ, hQ, hlocW, hW, hP, hF⟩ := hk k hk'
    have hjk : jx ≤ k := (Finset.mem_Ico.1 hk').1
    have hkN : k < N := by have := (Finset.mem_Ico.1 hk').2; omega
    have H := PtCorr2.oanchS_hR (R.withMsq m) (ptsX x) hanc (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) hjk
    have hfar := Obs2.farAB_eq_zero_of_anch (C := C k) H
    have hwk := Obs2.norm_wkAB2_le one_le_two hL (ptsX x) hkN hl hq hw hC H hlocQ hQ hlocW hW
    rw [hDefR_eq R m b μ₀ oR x H.toAb]
    unfold Obs2.xAB2
    rw [hfar, sub_zero]
    have hdet := Obs2.norm_detDef_le2 hC 0 w
    rw [hpe] at hdet
    have hdet' : ‖C k 0 0 * C k x x - C k 0 x * C k x 0‖ ≤
        2 * ℓs k ^ 2 * ((L : ℝ) ^ (jx + 1) * (ℓs k / (L : ℝ) ^ (k + 1))) ^ 2 := by
      refine hdet.trans ?_
      have h3 : 0 ≤ ℓs k / (L : ℝ) ^ (k + 1) := by have := hl.le; positivity
      have h4 : (w.length : ℝ) * (ℓs k / (L : ℝ) ^ (k + 1)) ≤
          (L : ℝ) ^ (jx + 1) * (ℓs k / (L : ℝ) ^ (k + 1)) := mul_le_mul_of_nonneg_right hlen h3
      have h5 : 0 ≤ (w.length : ℝ) * (ℓs k / (L : ℝ) ^ (k + 1)) := by positivity
      have h6 := pow_le_pow_left₀ h5 h4 2
      have h7 : 0 ≤ 2 * ℓs k ^ 2 := by positivity
      exact mul_le_mul_of_nonneg_left h6 h7
    have hMd : ‖M4 k * (C k 0 0 * C k x x - C k 0 x * C k x 0)‖ ≤
        ‖M4 k‖ * (2 * ℓs k ^ 2 * ((L : ℝ) ^ (jx + 1) * (ℓs k / (L : ℝ) ^ (k + 1))) ^ 2) := by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left hdet' (norm_nonneg _)
    have key : ∀ A B Cw D : ℂ, ‖-A + (Cw + D)‖ ≤ ‖A - B‖ + ‖B‖ + ‖Cw‖ + ‖D‖ := by
      intro A B Cw D
      have e : -A + (Cw + D) = -(A - B) - B + Cw + D := by ring
      rw [e]
      have n1 := norm_add_le (-(A - B) - B + Cw) D
      have n2 := norm_add_le (-(A - B) - B) Cw
      have n3 := norm_sub_le (-(A - B)) B
      rw [norm_neg] at n3
      linarith
    refine (key _ (M4 k * (C k 0 0 * C k x x - C k 0 x * C k x 0)) _ _).trans ?_
    refine (add_le_add (add_le_add (add_le_add hP hMd) hwk) hF).trans (le_of_eq ?_)
    ring
  calc ∑ k ∈ Finset.Ico jx (Nh + 1), ‖hDefR R m b μ₀ oR x k‖ + ‖lastDefR R Nh m b μ₀ oR x‖
      ≤ ∑ k ∈ Finset.Ico jx (Nh + 1), (2 * (Q1 2 * sq k) + 2 * (Q1 2 * sw k) + sp k + sf k +
        ‖M4 k‖ * (2 * ℓs k ^ 2 * ((L : ℝ) ^ (jx + 1) * (ℓs k / (L : ℝ) ^ (k + 1))) ^ 2)) + sL :=
        add_le_add (Finset.sum_le_sum hstep) hlast
    _ ≤ _ := hsum

/-! ### The Pauli defects of the reduced history -/

end Traj

end

end Spin2
