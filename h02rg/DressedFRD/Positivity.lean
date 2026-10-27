import DressedFRD.Main
import DressedFRD.Range

/-!
# Positivity (`thm:main`(vii), `def:nondeg`)

`NonDeg cP`: `(λ + m²) Ĉ_{j+1} ≥ c_P ê_j (1 - ê_j)` for `j ≤ N - 2` (`e:S6`).

`Gplus_nonneg`: for real `ζ_j` with `|ζ_j| ≤ c_P/4`, the standard part
`Γ^+_{j+1} = C_{j+1} + w_{j+1}` of `Z_{j+1} Γ^int_{j+1}` has a real nonnegative symbol, so it is
positive semidefinite. The rest is `Γ^-_{j+1} = Z_j R_{j,j+1}`.
-/

namespace DressedFRD

noncomputable section

open Finset Grassmann FRD ComplexConjugate

variable {d n : ℕ} [NeZero n]

/-- The non-degeneracy condition `e:S6`. -/
def NonDeg (N : ℕ) (msq cP : ℝ) (C : ℕ → Torus d n → ℝ) : Prop :=
  ∀ j, j + 2 ≤ N → ∀ m, cP * ereal msq C j m * (1 - ereal msq C j m) ≤ (lam m + msq) * C (j + 1) m

namespace Data

variable {D : Data d n}

/-- The standard part `Γ^+_{j+1}`. -/
def Gplus (D : Data d n) (j : ℕ) : Sym d n := ofR (D.C (j + 1)) + D.wLow j (D.tails j) (j + 1)

/-- The rest `Γ^-_{j+1}`. -/
def Gminus (D : Data d n) (j : ℕ) : Sym d n := D.Z j • D.tails j (j + 1)

theorem zp_real {j : ℕ} (h : conj (D.ζ j) = D.ζ j) : D.zp j = ((D.zp j).re : ℂ) := by
  have : conj (D.zp j) = D.zp j := by simp [zp, map_div₀, h]
  exact (Complex.conj_eq_iff_re.1 this).symm

/-- `thm:main`(vii): the standard part is positive. -/
theorem Gplus_nonneg (h : StdHyp D.L D.N D.msq D.C) (hL : 5 ≤ D.L) {cP : ℝ} (hcP : 0 < cP)
    (hcP1 : cP ≤ 1) (hnd : NonDeg D.N D.msq cP D.C) {j : ℕ} (hjN : j + 1 < D.N)
    (hreal : conj (D.ζ j) = D.ζ j) (hζ : ‖D.ζ j‖ ≤ cP / 4) (m : Torus d n) :
    ∃ x : ℝ, 0 ≤ x ∧ D.Gplus j m = x := by
  have hL1 : 1 ≤ D.L := by omega
  have hζ2 : ‖D.ζ j‖ ≤ 1 / 2 := by linarith
  set a := (D.zp j).re
  have ha : D.zp j = (a : ℂ) := zp_real hreal
  have haz : |a| ≤ cP / 2 := by
    have := norm_zp_le (D := D) hζ2
    rw [ha, Complex.norm_real, Real.norm_eq_abs] at this; linarith
  obtain ⟨e, he⟩ : ∃ e, e = ereal D.msq D.C j m := ⟨_, rfl⟩
  have he0 : 0 ≤ e := he ▸ ereal_nonneg h j m
  have he1 : e ≤ 1 := he ▸ ereal_le_one h (by omega : j ≤ D.N) m
  have hp := lam_add_pos h m
  -- `u = C_{≤j}(1 - ê_j)` at `m`
  obtain ⟨S0, hS0⟩ : ∃ S0, S0 = ∑ k ∈ Icc 1 j, D.C k m := ⟨_, rfl⟩
  have hue : e = (lam m + D.msq) * S0 := by rw [he, hS0]; rfl
  have hu0 : 0 ≤ S0 * (1 - e) :=
    mul_nonneg (hS0 ▸ sum_nonneg fun k _ => h.nonneg k m) (by linarith)
  have hCu : cP * (S0 * (1 - e)) ≤ D.C (j + 1) m := by
    have := hnd j (by omega) m
    have : (lam m + D.msq) * (cP * (S0 * (1 - e))) ≤ (lam m + D.msq) * D.C (j + 1) m := by
      calc (lam m + D.msq) * (cP * (S0 * (1 - e))) = cP * ((lam m + D.msq) * S0) * (1 - e) := by
            ring
        _ = cP * e * (1 - e) := by rw [← hue]
        _ ≤ _ := by rw [he]; exact this
    exact le_of_mul_le_mul_left this hp
  set u := S0 * (1 - e) with hudef
  set T := (range (D.L ^ (j + 1))).filter fun k =>
    scale D.L j D.N (rbar (D.rbV j) (fun _ : Fin (k + 2) => (none : Option ℕ))) = j + 1
  set s : ℝ := ∑ k ∈ T, a ^ (k + 1) * u * e ^ k
  have hw : D.wLow j (D.tails j) (j + 1) m = (s : ℂ) := by
    simp only [wLow, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, s, T, Finset.sum_filter]
    push_cast
    refine sum_congr rfl fun k _ => ?_
    rw [wLen_succ_eq hL1 hjN (D.tails j) k]
    split_ifs
    · rw [wordVal_std, ha]
      simp only [Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, Pi.one_apply, Ehat_apply, Cle_apply]
      rw [← he, ← hS0, hudef]
      push_cast; ring
    · simp
  refine ⟨D.C (j + 1) m + s, ?_, ?_⟩
  · have hs : -(2 * |a| * u) ≤ s := by
      have h1 : ∀ k ∈ T, -(|a| ^ (k + 1) * u) ≤ a ^ (k + 1) * u * e ^ k := by
        intro k _
        have hek : e ^ k ≤ 1 := pow_le_one₀ he0 he1
        have hek0 : 0 ≤ e ^ k := pow_nonneg he0 k
        have habs : |a ^ (k + 1)| = |a| ^ (k + 1) := abs_pow a (k + 1)
        have := neg_abs_le (a ^ (k + 1))
        rw [habs] at this
        have hue0 := mul_nonneg hu0 hek0
        have h3 : -(|a| ^ (k + 1) * (u * e ^ k)) ≤ a ^ (k + 1) * (u * e ^ k) := by nlinarith
        have h4 : |a| ^ (k + 1) * (u * e ^ k) ≤ |a| ^ (k + 1) * u :=
          mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hu0 hek) (pow_nonneg (abs_nonneg a) _)
        have e5 : a ^ (k + 1) * u * e ^ k = a ^ (k + 1) * (u * e ^ k) := by ring
        rw [e5]; linarith
      have h2 : ∑ k ∈ T, |a| ^ (k + 1) * u ≤ 2 * |a| * u := by
        calc ∑ k ∈ T, |a| ^ (k + 1) * u ≤ ∑ k ∈ range (D.L ^ (j + 1)), |a| ^ (k + 1) * u :=
              sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun k _ _ => by positivity
          _ = |a| * u * ∑ k ∈ range (D.L ^ (j + 1)), |a| ^ k := by
              rw [mul_sum]; exact sum_congr rfl fun k _ => by ring
          _ ≤ |a| * u * 2 := mul_le_mul_of_nonneg_left
              (sum_range_geom_le (abs_nonneg a) (by linarith) _) (by positivity)
          _ = _ := by ring
      calc -(2 * |a| * u) ≤ -∑ k ∈ T, |a| ^ (k + 1) * u := neg_le_neg h2
        _ = ∑ k ∈ T, -(|a| ^ (k + 1) * u) := by rw [sum_neg_distrib]
        _ ≤ s := sum_le_sum h1
    have := mul_le_mul_of_nonneg_right haz hu0
    linarith
  · rw [Gplus, Pi.add_apply, hw]; simp [ofR]

/-! ### `thm:main`(vii): ranges and bounds of `Γ^±` -/

theorem Gplus_sub (j : ℕ) : D.Gplus j - ofR (D.C (j + 1)) = D.wLow j (D.tails j) (j + 1) := by
  simp [Gplus]

theorem two_rng_Gplus_lt (h : StdHyp D.L D.N D.msq D.C) (hL : 1 ≤ D.L) (hn : n = D.L ^ D.N)
    {j : ℕ} (hj : j + 1 < D.N) : 2 * rng (D.Gplus j) < D.L ^ (j + 1) := by
  have hR := tailRange h hL hn j (by omega)
  have h1 := h.range (j + 1) (by omega) hj
  have h3 := two_rng_wLow_lt h hL hn (by omega) (D.tails j) hR hj
  have h5 := rng_add_le (ofR (D.C (j + 1))) (D.wLow j (D.tails j) (j + 1))
  simp only [Gplus]
  rcases le_total (rng (ofR (D.C (j + 1)))) (rng (D.wLow j (D.tails j) (j + 1))) with h' | h' <;>
    simp only [max_eq_left, max_eq_right, h'] at h5 <;> omega

/-- `thm:main`(vii), bounds: `‖Γ^+_{j+1} - C_{j+1}‖_{(j)} ≤ K |ζ_j|` and
`‖Γ^-_{j+1}‖_{(j)} ≤ K ζ̄^{L/256} |ζ|_{<j}`. -/
theorem Gplus_Gminus_bound {q : ℕ} {ζbar K : ℝ} {j : ℕ} (hc : D.Concl q ζbar K j)
    (hj : j + 1 < D.N) :
    snorm D.L q j (D.Gplus j - ofR (D.C (j + 1))) ≤ K * ‖D.ζ j‖ ∧
      snorm D.L q j (D.Gminus j) ≤ K * ζbar ^ ((D.L : ℝ) / 256) * D.Mz j := by
  rw [Gplus_sub]; exact ⟨hc.plus hj, hc.minus hj⟩

end Data

end

end DressedFRD
